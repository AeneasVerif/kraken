use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{self, Read, Write};
use std::process::ExitCode;
use std::time::Instant;

const _: () = assert!(usize::BITS == 64, "lrat_check_bytes requires a 64-bit target");

const DIMACS_BOUND: u64 = 1 << 28;
/// Largest byte count that still fits in `isize::MAX` bytes (the limit on any Rust
/// buffer) once rounded up to whole `u64` words.
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

    // Matches verified C0 LRAT kernel in `LeanQbe/T/Examples/LratBytesProg.lean:673`:
    //   v_bytes = (mv + 8) & -8
    //   t_bytes = ((mv + 1) * 4 + 7) & -8
    //   fixed   = 80 + v_bytes + t_bytes
    //   want    = nc + (prf_len & 0x0fff_ffff) + 32
    //   cap     = min(rem >> 4, want)
    // where 0x0fff_ffff = DIMACS_BOUND - 1 (28 bits = 256 MiB - 1).
    let v_bytes = (mv + 8) & !7;
    let t_bytes = ((mv + 1) * 4 + 7) & !7;
    let fixed = 80 + v_bytes + t_bytes;

    let p_cap = prf_len_u64 & (DIMACS_BOUND - 1);
    let want = nc + p_cap + 32;
    let pool_needed = cnf_len
        .saturating_add(prf_len_u64)
        .saturating_mul(4)
        .saturating_add(64);
    let rem = (16 * want).max((8 * want).saturating_add(pool_needed));
    let total = fixed.saturating_add(rem).max(128);
    total.min(MAX_WORK_BYTES as u64) as usize
}

/// Zeroed scratch buffer of `ceil(len / 8)` words, so it holds at least `len` bytes and
/// is 8-byte aligned. `vec!` of zeros asks for zeroed memory rather than writing it, so
/// a large buffer is lazily zeroed pages from the OS. Running out of memory aborts.
fn zeroed_work(len: usize) -> Vec<u64> {
    vec![0u64; len.div_ceil(8)]
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

/// Runs the checker with the first `work_len` bytes of `work` as its scratch space.
/// Panics if `work_len` exceeds the buffer or if `cnf` and `prf` overlap.
fn check_bytes(cnf: &[u8], prf: &[u8], work: &mut [u64], work_len: usize) -> u64 {
    let work_cap = std::mem::size_of_val(work); // 8 * work.len() bytes
    assert!(
        work_len <= work_cap,
        "work_len {work_len} exceeds the {work_cap}-byte work buffer"
    );
    // Two shared slices may overlap, which the contract of `lrat_check_bytes` rules out.
    // (This also refuses an empty slice that points strictly inside the other one.)
    let (c, p) = (cnf.as_ptr_range(), prf.as_ptr_range());
    assert!(c.end <= p.start || p.end <= c.start, "cnf and prf overlap");
    // SAFETY: `cnf` and `prf` are valid live byte slices. `work` is a valid live
    // exclusive `u64` slice, so its `work_cap` bytes are initialized and writable, and
    // they stay valid `u64`s whatever bytes are stored in them; `work_len <= work_cap`
    // is asserted above. All three lengths fit in `u64` (checked via
    // `usize::BITS == 64`). None of the three ranges wraps around the end of the
    // address space (`ptr + len < 2^64`): a slice is empty or within one allocation,
    // which has `base + size <= usize::MAX`. The three ranges are pairwise disjoint, as
    // the proved contract of `lrat_check_bytes` requires: `cnf` and `prf` because one
    // ends at or before the other starts (asserted above), and `work` from both because
    // an exclusive slice shares no byte with any other live slice. Given all that,
    // `lrat_check_bytes` is proved to read only `[cnf_ptr, cnf_ptr + cnf_len)` and
    // `[prf_ptr, prf_ptr + prf_len)` and only read/write
    // `[work_ptr, work_ptr + work_len)`.
    unsafe {
        lrat_check_bytes(
            cnf.as_ptr(),
            cnf.len() as u64,
            prf.as_ptr(),
            prf.len() as u64,
            work.as_mut_ptr().cast::<u8>(),
            work_len as u64,
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
    let mut work = zeroed_work(work_len);

    let t_check = Instant::now();
    let ok = check_bytes(&cnf, &prf, &mut work, work_len);
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
    fn work_buf_words_and_limit() {
        for (len, words) in [(0, 0), (1, 1), (8, 1), (9, 2), (127, 16), (1024, 128), (4097, 513)] {
            let work = zeroed_work(len);
            assert_eq!(work.len(), words, "{len} bytes");
            assert!(work.iter().all(|&w| w == 0));
        }

        // Up to `MAX_WORK_BYTES` the word count cannot overflow; anything larger is
        // rejected as a usage error.
        assert_eq!(MAX_WORK_BYTES.div_ceil(8) * 8, MAX_WORK_BYTES);
        assert_eq!(parse_work_bytes(&MAX_WORK_BYTES.to_string()), Ok(MAX_WORK_BYTES));
        assert!(parse_work_bytes(&(MAX_WORK_BYTES + 1).to_string()).is_err());
        assert!(parse_work_bytes(&((isize::MAX as usize).to_string())).is_err());
    }

    #[test]
    fn ffi_accept_and_reject() {
        let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
        // 'a' id=3 lits=[1] hints=[1]; 'd' ids=[1]; 'a' id=4 lits=[] hints=[3, 2]
        let accept_prf = [b'a', 6, 2, 0, 2, 0, b'd', 2, 0, b'a', 8, 0, 6, 4, 0];
        let len = compute_work_len(cnf, accept_prf.len());
        assert_eq!(check_bytes(cnf, &accept_prf, &mut zeroed_work(len), len), 1);

        let reject_prf = [b'a', 6, 0, 2, 0];
        let len2 = compute_work_len(cnf, reject_prf.len());
        assert_eq!(check_bytes(cnf, &reject_prf, &mut zeroed_work(len2), len2), 0);

        // Tiny work buffer and empty slices must cleanly return 0 without UB.
        assert_eq!(check_bytes(cnf, &accept_prf, &mut [0u64; 8], 64), 0);
        assert_eq!(check_bytes(&[], &[], &mut [], 0), 0);

        // The checker is given `work_len`, not the size of the buffer behind it: a
        // buffer that suffices in full is too small when only 64 bytes of it are offered.
        assert_eq!(check_bytes(cnf, &accept_prf, &mut zeroed_work(len), 64), 0);
    }

    #[test]
    #[should_panic(expected = "work_len 9 exceeds the 8-byte work buffer")]
    fn ffi_work_len_beyond_buffer_panics() {
        check_bytes(&[], &[], &mut [0u64; 1], 9);
    }

    #[test]
    fn ffi_overlapping_inputs_panic() {
        let buf = [0u8; 16];
        // Partial overlap, overlap in a single byte, one slice inside the other (each
        // of those both ways round), and the same slice twice.
        let cases: [(&[u8], &[u8]); 7] = [
            (&buf[..10], &buf[6..]),
            (&buf[6..], &buf[..10]),
            (&buf[..9], &buf[8..]),
            (&buf[8..], &buf[..9]),
            (&buf, &buf[4..8]),
            (&buf[4..8], &buf),
            (&buf, &buf),
        ];
        for (i, (cnf, prf)) in cases.into_iter().enumerate() {
            let caught = std::panic::catch_unwind(|| check_bytes(cnf, prf, &mut [0u64; 8], 64));
            let payload = caught.expect_err(&format!("case {i}: overlapping inputs accepted"));
            let msg = payload
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| payload.downcast_ref::<String>().cloned());
            assert_eq!(msg.as_deref(), Some("cnf and prf overlap"), "case {i}");
        }
    }

    #[test]
    fn ffi_adjacent_inputs_accepted() {
        let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
        let prf = [b'a', 6, 2, 0, 2, 0, b'd', 2, 0, b'a', 8, 0, 6, 4, 0];
        let len = compute_work_len(cnf, prf.len());

        // One buffer holding `cnf` then `prf` with nothing between them: the two
        // ranges touch but share no byte.
        let mut buf = cnf.to_vec();
        buf.extend_from_slice(&prf);
        let (c, p) = buf.split_at(cnf.len());
        assert_eq!(c.as_ptr_range().end, p.as_ptr_range().start);
        assert_eq!(check_bytes(c, p, &mut zeroed_work(len), len), 1);

        // The same with `prf` first.
        let mut buf = prf.to_vec();
        buf.extend_from_slice(cnf);
        let (p, c) = buf.split_at(prf.len());
        assert_eq!(p.as_ptr_range().end, c.as_ptr_range().start);
        assert_eq!(check_bytes(c, p, &mut zeroed_work(len), len), 1);

        // An empty slice at either end of the other one, or dangling, is accepted too
        // (and the instance is then simply not verified).
        for empty in [&c[..0], &c[c.len()..], &[]] {
            assert_eq!(check_bytes(empty, c, &mut zeroed_work(len), len), 0);
            assert_eq!(check_bytes(c, empty, &mut zeroed_work(len), len), 0);
        }
    }
}
