use std::alloc::{alloc_zeroed, dealloc, Layout};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{self, Read, Write};
use std::process::ExitCode;
use std::ptr::NonNull;
use std::time::Instant;

const _: () = assert!(usize::BITS == 64, "lrat_check_bytes requires a 64-bit target");

const DIMACS_BOUND: u64 = 1 << 28;
const MAX_WORK_BYTES: usize = (isize::MAX as usize) & !7;

extern "C" {
    fn lrat_check_bytes(
        cnf_ptr: *const u8,
        cnf_len: u64,
        prf_ptr: *const u8,
        prf_len: u64,
        work_ptr: *mut u8,
        work_len: u64,
    ) -> u64;
}

#[derive(Debug, PartialEq, Eq)]
struct Config {
    cnf_path: OsString,
    prf_path: OsString,
    quiet: bool,
    verbose: bool,
    work_bytes: Option<usize>,
}

enum ParseOutcome {
    Run(Config),
    Help,
}

fn usage_text() -> &'static str {
    "\
usage: lrat_check [options] <cnf> <lrat>

Verify unsatisfiability of an ASCII DIMACS CNF formula (<cnf>) against a
Binary LRAT proof (<lrat>) using the verified lean-qbe `lrat_check_bytes`
checker. Pass '-' for <cnf> or <lrat> (not both) to read from stdin.

options:
  -h, --help            show this help message and exit
  -q, --quiet           suppress stdout output (exit status only)
  -v, --verbose         print buffer sizes and timings ('c ...' lines)
  --work-bytes <bytes>  override scratch buffer size in bytes

exit status:
  0  verified (s VERIFIED)
  1  not verified or malformed input (s NOT VERIFIED)
  2  command-line or I/O error"
}

fn parse_work_bytes(s: &str) -> Result<usize, String> {
    let val: usize = s
        .parse()
        .map_err(|_| format!("invalid --work-bytes value '{s}'"))?;
    if val > MAX_WORK_BYTES {
        return Err(format!(
            "--work-bytes value '{s}' exceeds maximum {MAX_WORK_BYTES}"
        ));
    }
    Ok(val)
}

fn parse_args<I>(args: I) -> Result<ParseOutcome, String>
where
    I: IntoIterator<Item = OsString>,
{
    let mut it = args.into_iter();
    let _prog = it.next();

    let mut quiet = false;
    let mut verbose = false;
    let mut work_bytes = None;
    let mut positional: Vec<OsString> = Vec::new();
    let mut end_of_opts = false;

    while let Some(arg) = it.next() {
        if !end_of_opts && arg == OsStr::new("--") {
            end_of_opts = true;
            continue;
        }
        if !end_of_opts && arg != OsStr::new("-") {
            if let Some(s) = arg.to_str() {
                if s == "--help" {
                    return Ok(ParseOutcome::Help);
                } else if s == "--quiet" {
                    quiet = true;
                    continue;
                } else if s == "--verbose" {
                    verbose = true;
                    continue;
                } else if s == "--strict" || s == "--forward" {
                    return Err(format!(
                        "unsupported option '{s}' (lrat_check_bytes only checks non-strict Binary LRAT)"
                    ));
                } else if s == "--work-bytes" {
                    let next = it
                        .next()
                        .ok_or_else(|| "missing value after --work-bytes".to_string())?;
                    let next_str = next
                        .to_str()
                        .ok_or_else(|| "non-UTF-8 value for --work-bytes".to_string())?;
                    work_bytes = Some(parse_work_bytes(next_str)?);
                    continue;
                } else if let Some(val) = s.strip_prefix("--work-bytes=") {
                    work_bytes = Some(parse_work_bytes(val)?);
                    continue;
                } else if s.starts_with("--") {
                    return Err(format!("unknown option '{s}' (try --help)"));
                } else if s.starts_with('-') {
                    for ch in s.chars().skip(1) {
                        match ch {
                            'h' => return Ok(ParseOutcome::Help),
                            'q' => quiet = true,
                            'v' => verbose = true,
                            'S' | 'f' => {
                                return Err(format!(
                                    "unsupported option '-{ch}' (lrat_check_bytes only checks non-strict Binary LRAT)"
                                ));
                            }
                            _ => return Err(format!("unknown option '-{ch}' (try --help)")),
                        }
                    }
                    continue;
                }
            } else if arg.as_encoded_bytes().starts_with(b"-") {
                return Err("unknown non-UTF-8 option (try --help)".to_string());
            }
        }
        positional.push(arg);
    }

    match positional.len() {
        0 | 1 => Err("expected <cnf> <lrat> (try --help)".to_string()),
        2 => {
            let mut pos = positional.into_iter();
            let cnf_path = pos.next().unwrap();
            let prf_path = pos.next().unwrap();
            if cnf_path == OsStr::new("-") && prf_path == OsStr::new("-") {
                return Err("<cnf> and <lrat> cannot both be '-' (stdin)".to_string());
            }
            Ok(ParseOutcome::Run(Config {
                cnf_path,
                prf_path,
                quiet,
                verbose,
                work_bytes,
            }))
        }
        _ => Err(
            "unexpected extra positional argument (trimming / output proof is not supported)"
                .to_string(),
        ),
    }
}

#[inline]
fn is_dimacs_ws(b: u8) -> bool {
    b == b' ' || (9..=13).contains(&b)
}

fn skip_ws_comments(mut s: &[u8]) -> &[u8] {
    loop {
        match s {
            [b, rest @ ..] if is_dimacs_ws(*b) => s = rest,
            [b'c', rest @ ..] => {
                s = match rest.iter().position(|&x| x == b'\n') {
                    Some(idx) => &rest[idx + 1..],
                    None => &[],
                };
            }
            _ => return s,
        }
    }
}

fn skip_ws1(s: &[u8]) -> Option<&[u8]> {
    let (first, mut rest) = s.split_first()?;
    if !is_dimacs_ws(*first) {
        return None;
    }
    while let Some((b, tail)) = rest.split_first() {
        if is_dimacs_ws(*b) {
            rest = tail;
        } else {
            break;
        }
    }
    Some(rest)
}

fn parse_dimacs_nat(s: &[u8]) -> Option<(u32, &[u8])> {
    let (&first, mut rest) = s.split_first()?;
    if !first.is_ascii_digit() {
        return None;
    }
    let mut acc = u64::from(first - b'0');
    while let Some((&b, tail)) = rest.split_first() {
        if b.is_ascii_digit() {
            acc = acc * 10 + u64::from(b - b'0');
            if acc >= DIMACS_BOUND {
                return None;
            }
            rest = tail;
        } else if is_dimacs_ws(b) {
            return Some((acc as u32, rest));
        } else {
            return None;
        }
    }
    Some((acc as u32, rest))
}

/// Mirror of `LeanQbe.LratBytes.parseHeader` used only to size the scratch buffer.
/// `lrat_check_bytes` itself re-parses and validates everything from scratch.
fn peek_dimacs_header_with_rest(cnf: &[u8]) -> Option<(u32, u32, usize)> {
    let s = skip_ws_comments(cnf);
    let s = s.strip_prefix(b"p")?;
    let s = skip_ws1(s)?;
    let s = s.strip_prefix(b"cnf")?;
    let s = skip_ws1(s)?;
    let (mv, s) = parse_dimacs_nat(s)?;
    let s = skip_ws1(s)?;
    let (nc, rest) = parse_dimacs_nat(s)?;
    Some((mv, nc, rest.len()))
}

fn peek_dimacs_header(cnf: &[u8]) -> Option<(u32, u32)> {
    peek_dimacs_header_with_rest(cnf).map(|(mv, nc, _)| (mv, nc))
}

fn compute_work_len(cnf: &[u8], prf_len: usize) -> usize {
    let Some((mv, nc, rest_len)) = peek_dimacs_header_with_rest(cnf) else {
        return 4096;
    };
    // Each clause consumes at least 1 whitespace separator byte plus '0'.
    if (rest_len as u64) < u64::from(nc).saturating_mul(2) {
        return 4096;
    }
    let mv = u64::from(mv);
    let nc = u64::from(nc);
    let cnf_len = cnf.len() as u64;
    let prf_len_u64 = prf_len as u64;

    // Matches `lrat_check_bytes` in `LeanQbe/Examples/LratBytes.lean`:
    //   v_bytes = (mv + 8) & -8
    //   t_bytes = ((mv + 1) * 4 + 7) & -8
    //   fixed   = 80 + v_bytes + t_bytes
    //   want    = nc + (prf_len & 0xfffffff) + 32
    //   cap     = min(rem >> 4, want)
    let v_bytes = (mv + 8) & !7;
    let t_bytes = ((mv + 1) * 4 + 7) & !7;
    let fixed = 80 + v_bytes + t_bytes;

    let p_cap = prf_len_u64 & 0x0fff_ffff;
    let want = nc + p_cap + 32;
    let pool_needed = cnf_len
        .saturating_add(prf_len_u64)
        .saturating_mul(4)
        .saturating_add(64);
    let rem = (16 * want).max((8 * want).saturating_add(pool_needed));
    let total = fixed.saturating_add(rem).max(128);
    total.min(MAX_WORK_BYTES as u64) as usize
}

/// 8-byte-aligned, fallibly-allocated zeroed scratch buffer (uses OS lazy zero-pages via `calloc`).
struct WorkBuf {
    ptr: Option<(NonNull<u8>, Layout)>,
    len: usize,
}

impl WorkBuf {
    fn new_zeroed(len: usize) -> Result<Self, String> {
        if len == 0 {
            return Ok(Self { ptr: None, len: 0 });
        }
        let layout = Layout::from_size_align(len, 8)
            .map_err(|_| format!("work buffer size {len} bytes exceeds allocator limit"))?;
        // SAFETY: `layout.size() > 0` and `layout.align() == 8`.
        let raw = unsafe { alloc_zeroed(layout) };
        let Some(ptr) = NonNull::new(raw) else {
            return Err(format!("failed to allocate {len} bytes for work buffer"));
        };
        Ok(Self {
            ptr: Some((ptr, layout)),
            len,
        })
    }

    fn as_mut_slice(&mut self) -> &mut [u8] {
        match self.ptr {
            Some((ptr, _)) => {
                // SAFETY: `ptr` points to `self.len` initialized bytes live until `Drop`.
                unsafe { std::slice::from_raw_parts_mut(ptr.as_ptr(), self.len) }
            }
            None => &mut [],
        }
    }
}

impl Drop for WorkBuf {
    fn drop(&mut self) {
        if let Some((ptr, layout)) = self.ptr {
            // SAFETY: `ptr` was allocated with `alloc_zeroed(layout)` and `layout.size() > 0`.
            unsafe { dealloc(ptr.as_ptr(), layout) };
        }
    }
}

fn read_input(path: &OsStr) -> io::Result<Vec<u8>> {
    if path == OsStr::new("-") {
        let mut buf = Vec::new();
        io::stdin().read_to_end(&mut buf)?;
        Ok(buf)
    } else {
        fs::read(path)
    }
}

fn check_bytes(cnf: &[u8], prf: &[u8], work: &mut [u8]) -> u64 {
    // SAFETY: `cnf`, `prf`, and `work` are valid live slices whose byte lengths
    // fit in `u64` (checked via `usize::BITS == 64`), and `lrat_check_bytes` is
    // proved to read only `[cnf_ptr, cnf_ptr + cnf_len)` and `[prf_ptr, prf_ptr + prf_len)`
    // and only read/write `[work_ptr, work_ptr + work_len)`.
    unsafe {
        lrat_check_bytes(
            cnf.as_ptr(),
            cnf.len() as u64,
            prf.as_ptr(),
            prf.len() as u64,
            work.as_mut_ptr(),
            work.len() as u64,
        )
    }
}

fn run(cfg: Config) -> ExitCode {
    let t_start = Instant::now();

    let cnf = match read_input(&cfg.cnf_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!(
                "lrat_check: failed to read '{}': {e}",
                cfg.cnf_path.to_string_lossy()
            );
            return ExitCode::from(2);
        }
    };
    let prf = match read_input(&cfg.prf_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!(
                "lrat_check: failed to read '{}': {e}",
                cfg.prf_path.to_string_lossy()
            );
            return ExitCode::from(2);
        }
    };
    let read_dur = t_start.elapsed();

    let work_len = cfg
        .work_bytes
        .unwrap_or_else(|| compute_work_len(&cnf, prf.len()));
    let mut work = match WorkBuf::new_zeroed(work_len) {
        Ok(b) => b,
        Err(msg) => {
            eprintln!("lrat_check: {msg}");
            return ExitCode::from(2);
        }
    };

    let t_check = Instant::now();
    let ok = check_bytes(&cnf, &prf, work.as_mut_slice());
    let check_dur = t_check.elapsed();
    let total_dur = t_start.elapsed();

    if !cfg.quiet {
        let mut out = io::stdout().lock();
        if cfg.verbose {
            let hdr = match peek_dimacs_header(&cnf) {
                Some((mv, nc)) => format!("max_var={mv} clauses={nc}"),
                None => "header=invalid".to_string(),
            };
            let _ = writeln!(
                out,
                "c cnf '{}' ({} bytes, {hdr})",
                cfg.cnf_path.to_string_lossy(),
                cnf.len()
            );
            let _ = writeln!(
                out,
                "c prf '{}' ({} bytes)",
                cfg.prf_path.to_string_lossy(),
                prf.len()
            );
            if prf.len() >= DIMACS_BOUND as usize {
                let _ = writeln!(
                    out,
                    "c note: prf_len >= 256 MiB wraps internal clause capacity (prf_len & 0xfffffff) in lrat_check_bytes"
                );
            }
            let _ = writeln!(out, "c work {work_len} bytes");
            let _ = writeln!(
                out,
                "c time read={:.3} ms check={:.3} ms total={:.3} ms",
                read_dur.as_secs_f64() * 1e3,
                check_dur.as_secs_f64() * 1e3,
                total_dur.as_secs_f64() * 1e3
            );
        }
        match ok {
            1 => {
                let _ = writeln!(out, "s VERIFIED");
            }
            0 => {
                let _ = writeln!(out, "s NOT VERIFIED");
            }
            other => {
                eprintln!("lrat_check: unexpected return code {other} from lrat_check_bytes");
                return ExitCode::from(1);
            }
        }
    }

    match ok {
        1 => ExitCode::SUCCESS,
        0 => ExitCode::from(1),
        other => {
            if cfg.quiet {
                eprintln!("lrat_check: unexpected return code {other} from lrat_check_bytes");
            }
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    match parse_args(std::env::args_os()) {
        Ok(ParseOutcome::Help) => {
            let _ = writeln!(io::stdout(), "{}", usage_text());
            ExitCode::SUCCESS
        }
        Ok(ParseOutcome::Run(cfg)) => run(cfg),
        Err(msg) => {
            eprintln!("lrat_check: {msg}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn os(xs: &[&str]) -> Vec<OsString> {
        xs.iter().map(OsString::from).collect()
    }

    #[test]
    fn cli_basic_and_flags() {
        let Ok(ParseOutcome::Run(cfg)) = parse_args(os(&["lrat_check", "a.cnf", "b.lrat"])) else {
            panic!("expected Run");
        };
        assert_eq!(cfg.cnf_path, OsStr::new("a.cnf"));
        assert_eq!(cfg.prf_path, OsStr::new("b.lrat"));
        assert!(!cfg.quiet);
        assert!(!cfg.verbose);
        assert_eq!(cfg.work_bytes, None);

        let Ok(ParseOutcome::Run(cfg)) =
            parse_args(os(&["lrat_check", "-qv", "--work-bytes", "2048", "-", "b.lrat"]))
        else {
            panic!("expected Run");
        };
        assert!(cfg.quiet);
        assert!(cfg.verbose);
        assert_eq!(cfg.work_bytes, Some(2048));
        assert_eq!(cfg.cnf_path, OsStr::new("-"));

        let Ok(ParseOutcome::Run(cfg)) =
            parse_args(os(&["lrat_check", "--work-bytes=512", "--", "-weird.cnf", "-weird.lrat"]))
        else {
            panic!("expected Run");
        };
        assert_eq!(cfg.work_bytes, Some(512));
        assert_eq!(cfg.cnf_path, OsStr::new("-weird.cnf"));
        assert_eq!(cfg.prf_path, OsStr::new("-weird.lrat"));
    }

    #[test]
    fn cli_errors() {
        assert!(matches!(parse_args(os(&["lrat_check", "-h"])), Ok(ParseOutcome::Help)));
        assert!(parse_args(os(&["lrat_check"])).is_err());
        assert!(parse_args(os(&["lrat_check", "a.cnf"])).is_err());
        assert!(parse_args(os(&["lrat_check", "a.cnf", "b.lrat", "trimmed.lrat"])).is_err());
        assert!(parse_args(os(&["lrat_check", "-", "-"])).is_err());
        assert!(parse_args(os(&["lrat_check", "-S", "a.cnf", "b.lrat"])).is_err());
        assert!(parse_args(os(&["lrat_check", "--strict", "a.cnf", "b.lrat"])).is_err());
        assert!(parse_args(os(&["lrat_check", "-f", "a.cnf", "b.lrat"])).is_err());
        assert!(parse_args(os(&["lrat_check", "--unknown", "a.cnf", "b.lrat"])).is_err());
        assert!(parse_args(os(&["lrat_check", "--work-bytes", "abc", "a.cnf", "b.lrat"])).is_err());
    }

    #[test]
    fn dimacs_header_peek_cases() {
        assert_eq!(peek_dimacs_header(b"p cnf 1 2\n1 0\n-1 0\n"), Some((1, 2)));
        assert_eq!(
            peek_dimacs_header(b"c hello\r\nc world\n  p \t cnf  12   34 \r\n"),
            Some((12, 34))
        );
        assert_eq!(peek_dimacs_header(b"p cnf 0 0"), Some((0, 0)));
        assert_eq!(peek_dimacs_header(b"p cnf 268435455 1\n0\n"), Some((268435455, 1)));
        assert_eq!(peek_dimacs_header(b"p cnf 268435456 1\n0\n"), None);
        assert_eq!(peek_dimacs_header(b"p cnf 1\n"), None);
        assert_eq!(peek_dimacs_header(b""), None);
        assert_eq!(peek_dimacs_header(b"p cnf 1 2x\n"), None);
    }

    #[test]
    fn work_len_bounds() {
        assert_eq!(compute_work_len(b"bad", 10), 4096);
        assert_eq!(compute_work_len(b"p cnf 268435455 268435455\n", 10), 4096);
        assert_eq!(compute_work_len(b"p cnf 268435455 1\n", 10), 4096);
        let w = compute_work_len(b"p cnf 1 2\n1 0\n-1 0\n", 15);
        assert!(w >= 128);
        assert_eq!(compute_work_len(b"p cnf 1 1\n0\n", usize::MAX), MAX_WORK_BYTES);
    }

    #[test]
    fn work_buf_alloc_and_oom() {
        let mut empty = WorkBuf::new_zeroed(0).expect("zero-len WorkBuf should succeed");
        assert_eq!(empty.as_mut_slice().len(), 0);

        let mut small = WorkBuf::new_zeroed(4097).expect("4097-byte WorkBuf should succeed");
        assert_eq!(small.as_mut_slice().len(), 4097);
        assert_eq!(small.as_mut_slice().as_ptr() as usize % 8, 0);
        assert!(small.as_mut_slice().iter().all(|&b| b == 0));

        assert!(WorkBuf::new_zeroed(1 << 62).is_err());
        assert!(parse_work_bytes(&((isize::MAX as usize).to_string())).is_err());
    }

    #[test]
    fn ffi_accept_and_reject() {
        let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
        // 'a' id=3 lits=[1] hints=[1]; 'd' ids=[1]; 'a' id=4 lits=[] hints=[3, 2]
        let accept_prf = [b'a', 6, 2, 0, 2, 0, b'd', 2, 0, b'a', 8, 0, 6, 4, 0];
        let mut work = vec![0u8; compute_work_len(cnf, accept_prf.len())];
        assert_eq!(check_bytes(cnf, &accept_prf, &mut work), 1);

        let reject_prf = [b'a', 6, 0, 2, 0];
        let mut work2 = vec![0u8; compute_work_len(cnf, reject_prf.len())];
        assert_eq!(check_bytes(cnf, &reject_prf, &mut work2), 0);

        // Tiny work buffer and empty slices must cleanly return 0 without UB.
        let mut tiny = [0u8; 64];
        assert_eq!(check_bytes(cnf, &accept_prf, &mut tiny), 0);
        assert_eq!(check_bytes(&[], &[], &mut []), 0);
    }
}
