module

-- Ported from bedrock2/src/bedrock2/ToCString.v at mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13

public import Kraken.Bedrock2.Syntax

@[expose] public section

namespace Kraken.Bedrock2

def cPrelude (testHooks : Bool := false) : String :=
  r#"// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <limits.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), "signed size");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, "pointer fits in int");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, "two's complement");
static_assert(sizeof(br_word_t) <= 8, "word fits in 64 bits");
static_assert(UINTPTR_MAX >= UINT_MAX, "no promotion to int");
static_assert(UINT_MAX >= 0xffffffff, "int has at least 32 bits");
static_assert(BR_WORD_MAX == UINT32_MAX ? sizeof(br_word_t) == 4 :
              BR_WORD_MAX == UINT64_MAX && sizeof(br_word_t) == 8, "word is 32 or 64 bits");
static_assert(_Generic((uint8_t)0, unsigned char: 1, default: 0), "uint8_t is unsigned char");
static_assert((br_signed_t)BR_WORD_MAX == -1, "modular conversion to signed");
static_assert(((br_signed_t)-1 >> 1) == -1, "arithmetic right shift");

#if defined(linux) || defined(unix)
  #error "compile with -std=c11 or later (not gnu*)"
#endif

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, "little-endian");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error "failed to confirm that target is little-endian"
#endif

// "An object shall have its stored value accessed only ... a character type."
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load8(br_word_t a) {
  uint64_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return (br_word_t)r;
}

static inline void _br_store1(br_word_t a, br_word_t v) {
  *((uint8_t *)a) = (uint8_t)v;
}

static inline void _br_store2(br_word_t a, br_word_t v) {
  uint16_t r = (uint16_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

static inline void _br_store4(br_word_t a, br_word_t v) {
  uint32_t r = (uint32_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

static inline void _br_store8(br_word_t a, br_word_t v) {
  uint64_t r = (uint64_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

#if defined(_MSC_VER)
  #include <intrin.h>
#endif

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
"# ++ "\t" ++ r#"  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}
"# ++
  (if testHooks then "\nvoid _br_test_stackalloc(br_word_t addr, br_word_t n);\n" else "")

def cHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def cLit (v : Int) : String :=
  let n := (v % 2 ^ 64).toNat
  let s := if n < 0xff then toString n else cHex n
  if s.endsWith "e" then s ++ " " else s

def cOp1 : Op1 → String → String
  | .not, e => "~" ++ e
  | .opp, e => "0u-" ++ e

def cBop (e1 : String) : BinOp → String → String
  | .add, e2 => e1 ++ "+" ++ e2
  | .sub, e2 => e1 ++ "-" ++ e2
  | .mul, e2 => e1 ++ "*" ++ e2
  | .mulhuu, e2 => "_br_mulhuu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | .divu, e2 => "_br_divu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | .remu, e2 => "_br_remu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | .and, e2 => e1 ++ "&" ++ e2
  | .or, e2 => e1 ++ "|" ++ e2
  | .xor, e2 => e1 ++ "^" ++ e2
  | .sru, e2 => e1 ++ ">>" ++ e2
  | .slu, e2 => e1 ++ "<<" ++ e2
  | .srs, e2 => "(br_word_t)((br_signed_t)" ++ e1 ++ ">>" ++ e2 ++ ")"
  | .lts, e2 => "(br_word_t)((br_signed_t)" ++ e1 ++ "<" ++ "(br_signed_t)" ++ e2 ++ ")"
  | .ltu, e2 => "(br_word_t)(" ++ e1 ++ "<" ++ e2 ++ ")"
  | .eq, e2 => "(br_word_t)(" ++ e1 ++ "==" ++ e2 ++ ")"

def AccessSize.cSuffix : AccessSize → String
  | .one => "1" | .two => "2" | .four => "4" | .eight => "8"

def cInlinetable (t : List UInt8) : String :=
  "static const uint8_t _inlinetable[" ++ cLit t.length ++ "] = {" ++
    ", ".intercalate (t.map (cHex ·.toNat)) ++ "};"

def cLoadtable (s : AccessSize) (i : String) : String :=
  "_br_load" ++ s.cSuffix ++ "((br_word_t)&_inlinetable[" ++ i ++ "])"

def cParen (e : Expr) (s : String) : String :=
  match e with
  | .literal _ | .var _ => s
  | _ => "(" ++ s ++ ")"

def cOperand2 (e : Expr) (s : String) : String :=
  match e with
  | .literal v => if v % 2 ^ 64 < 2 ^ 32 then cLit v else s
  | _ => cParen e s

def cShamt (e : Expr) (s : String) : String :=
  match e with
  | .literal v => if v % 2 ^ 64 < 32 then cLit v else "(" ++ s ++ "&(sizeof(br_word_t)*8-1))"
  | _ => "(" ++ cParen e s ++ "&(sizeof(br_word_t)*8-1))"

def cExpr : Expr → String
  | .literal v => "(br_word_t)" ++ cLit v
  | .var x => x
  | .load s ea => "_br_load" ++ s.cSuffix ++ "(" ++ cExpr ea ++ ")"
  | .inlinetable s t i => "({ " ++ cInlinetable t ++ cLoadtable s (cExpr i) ++ "; })"
  | .op1 op e => cOp1 op (cParen e (cExpr e))
  | .op op e1 e2 =>
    let a := cParen e1 (cExpr e1)
    match op with
    | .slu | .sru | .srs => cBop a op (cShamt e2 (cExpr e2))
    | .add | .sub | .mul | .and | .or | .xor => cBop a op (cOperand2 e2 (cExpr e2))
    | _ => cBop a op (cParen e2 (cExpr e2))
  | .ite c e1 e2 => cParen c (cExpr c) ++ " ? " ++ cParen e1 (cExpr e1) ++ " : " ++ cParen e2 (cExpr e2)

def Expr.vars : Expr → List String
  | .literal _ => []
  | .var x => [x]
  | .load _ ea => ea.vars
  | .inlinetable _ _ i => i.vars
  | .op1 _ e => e.vars
  | .op _ e1 e2 => e1.vars ++ e2.vars
  | .ite c e1 e2 => c.vars ++ (e1.vars ++ e2.vars)

def Cmd.vars : Cmd → List String
  | .skip => []
  | .set x e => x :: e.vars
  | .unset x => [x]
  | .store _ ea ev => ea.vars ++ ev.vars
  | .stackalloc x _ b => x :: b.vars
  | .cond e t f => e.vars ++ (t.vars ++ f.vars)
  | .seq c1 c2 => c1.vars ++ c2.vars
  | .while e c => e.vars ++ c.vars
  | .call binds _ args | .interact binds _ args => binds ++ args.flatMap Expr.vars

def cCall (binds : List String) (f : String) (es : List String) : String :=
  match binds.getLast? with
  | none => f ++ "(" ++ ", ".intercalate es ++ ");\n"
  | some r => r ++ " = " ++ f ++ "(" ++ ", ".intercalate (es ++ binds.dropLast.map ("&" ++ ·)) ++ ");\n"

def cCmd (c : Cmd) (indent : String := "  ") (testHooks : Bool := false) : String :=
  match c with
  | .store s ea ev => indent ++ "_br_store" ++ s.cSuffix ++ "(" ++ cExpr ea ++ ", " ++ cExpr ev ++ ");\n"
  | .stackalloc x n body =>
    let tmp := "_br_stackalloc_" ++ x
    indent ++ "uint8_t " ++ tmp ++ "[" ++ toString (max n 1) ++ "] = {0}; " ++ x ++ " = (br_word_t)&" ++ tmp ++ ";\n" ++
    (if testHooks then indent ++ "_br_test_stackalloc(" ++ x ++ ", " ++ cLit n ++ ");\n" else "") ++
    cCmd body indent testHooks
  | .set x (.inlinetable s t ei) =>
    indent ++ "{ " ++ cInlinetable t ++ " " ++ x ++ " = " ++ cLoadtable s (cExpr ei) ++ "; }\n"
  | .set x ev => indent ++ x ++ " = " ++ cExpr ev ++ ";\n"
  | .unset x => indent ++ "// unset " ++ x ++ "\n"
  | .cond eb t f =>
    indent ++ "if (" ++ cExpr eb ++ ") {\n" ++
      cCmd t ("  " ++ indent) testHooks ++
    indent ++ "} else {\n" ++
      cCmd f ("  " ++ indent) testHooks ++
    indent ++ "}\n"
  | .while eb b =>
    indent ++ "while (" ++ cExpr eb ++ ") {\n" ++
      cCmd b ("  " ++ indent) testHooks ++
    indent ++ "}\n"
  | .seq c1 c2 => cCmd c1 indent testHooks ++ cCmd c2 indent testHooks
  | .skip => indent ++ "/*skip*/\n"
  | .call binds f es => indent ++ cCall binds f (es.map cExpr)
  | .interact binds a es => indent ++ cCall binds a (es.map cExpr)

def cKeywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum",
   "extern", "float", "for", "goto", "if", "inline", "int", "long", "register", "restrict", "return",
   "short", "signed", "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
   "volatile", "while", "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic",
   "_Imaginary", "_Noreturn", "_Static_assert", "_Thread_local", "alignas", "alignof", "bool",
   "constexpr", "false", "nullptr", "static_assert", "thread_local", "true", "typeof",
   "typeof_unqual", "_BitInt", "_Decimal32", "_Decimal64", "_Decimal128", "asm"]

def cReservedNames : List String :=
  ["BR_WORD_MAX", "_inlinetable", "memcpy", "assert", "NULL", "NDEBUG", "CHAR_BIT", "BITINT_MAXWIDTH"]

def cPreludeHeaderFunctions : List String :=
  ["memcpy", "memccpy", "memchr", "memcmp", "memset", "memset_explicit", "memmove", "memalignment",
   "strcat", "strncat", "strchr", "strcmp", "strncmp", "strcoll", "strcpy", "strncpy", "strcspn",
   "strdup", "strndup", "strerror", "strlen", "strpbrk", "strrchr", "strspn", "strstr", "strtok",
   "strxfrm", "memcpy_s", "memmove_s", "memset_s", "strcpy_s", "strncpy_s", "strcat_s",
   "strncat_s", "strtok_s", "strerror_s", "strerrorlen_s", "strnlen_s"]

def cMathFunctionBases : List String :=
  ["acos", "asin", "atan", "atan2", "cos", "sin", "tan", "acospi", "asinpi", "atanpi", "atan2pi",
   "cospi", "sinpi", "tanpi", "acosh", "asinh", "atanh", "cosh", "sinh", "tanh", "exp", "exp10",
   "exp10m1", "exp2", "exp2m1", "expm1", "frexp", "ilogb", "ldexp", "llogb", "log", "log10",
   "log10p1", "log1p", "logp1", "log2", "log2p1", "logb", "modf", "scalbn", "scalbln", "cbrt",
   "compoundn", "fabs", "hypot", "pow", "pown", "powr", "rootn", "rsqrt", "sqrt", "erf", "erfc",
   "lgamma", "tgamma", "ceil", "floor", "nearbyint", "rint", "lrint", "llrint", "round", "lround",
   "llround", "roundeven", "trunc", "fromfp", "ufromfp", "fromfpx", "ufromfpx", "fmod",
   "remainder", "remquo", "copysign", "nan", "nextafter", "nexttoward", "nextup", "nextdown",
   "canonicalize", "fdim", "fmax", "fmin", "fmaximum", "fminimum", "fmaximum_mag", "fminimum_mag",
   "fmaximum_num", "fminimum_num", "fmaximum_mag_num", "fminimum_mag_num", "fma", "fadd", "dadd",
   "fsub", "dsub", "fmul", "dmul", "fdiv", "ddiv", "ffma", "dfma", "fsqrt", "dsqrt", "getpayload",
   "setpayload", "setpayloadsig", "totalorder", "totalordermag", "quantize", "samequantum",
   "quantum", "llquantexp", "encodedec", "decodedec", "encodebin", "decodebin"]

def cComplexFunctionBases : List String :=
  ["cacos", "casin", "catan", "ccos", "csin", "ctan", "cacosh", "casinh", "catanh", "ccosh",
   "csinh", "ctanh", "cexp", "clog", "cabs", "cpow", "csqrt", "carg", "cimag", "conj", "cproj",
   "creal", "cerf", "cerfc", "cexp2", "cexpm1", "clog10", "clog1p", "clog2", "clgamma", "ctgamma",
   "csinpi", "ccospi", "ctanpi", "casinpi", "cacospi", "catanpi", "ccompoundn", "cpown", "cpowr",
   "crootn", "crsqrt", "cexp10", "cexp10m1", "cexp2m1", "clog10p1", "clog2p1", "clogp1"]

def cStdlibExternalNames : List String :=
  cPreludeHeaderFunctions ++
  cMathFunctionBases.flatMap (fun b => [b, b ++ "f", b ++ "l", b ++ "d32", b ++ "d64", b ++ "d128"]) ++
  cComplexFunctionBases.flatMap (fun b => [b, b ++ "f", b ++ "l"]) ++
  (["add", "sub", "mul", "div", "fma", "sqrt"].flatMap fun o =>
    ["d32" ++ o ++ "d64", "d32" ++ o ++ "d128", "d64" ++ o ++ "d128"]) ++
  ["errno", "setjmp", "longjmp", "va_copy", "va_end", "signal", "raise", "setlocale", "localeconv",
   "imaxabs", "imaxdiv", "call_once", "kill_dependency",
   "remove", "rename", "tmpfile", "tmpnam", "fclose", "fflush", "fopen", "freopen", "setbuf",
   "setvbuf", "fprintf", "fscanf", "printf", "scanf", "snprintf", "sprintf", "sscanf", "vfprintf",
   "vfscanf", "vprintf", "vscanf", "vsnprintf", "vsprintf", "vsscanf", "fgetc", "fgets", "fputc",
   "fputs", "getc", "getchar", "gets", "putc", "putchar", "puts", "ungetc", "fread", "fwrite",
   "fgetpos", "fseek", "fsetpos", "ftell", "rewind", "clearerr", "feof", "ferror", "perror",
   "atof", "atoi", "atol", "atoll", "rand", "srand", "aligned_alloc", "calloc", "free",
   "free_sized", "free_aligned_sized", "malloc", "realloc", "abort", "atexit", "at_quick_exit",
   "exit", "_Exit", "getenv", "quick_exit", "system", "bsearch", "qsort", "abs", "labs", "llabs",
   "div", "ldiv", "lldiv", "mblen", "mbtowc", "wctomb", "mbstowcs", "wcstombs",
   "clock", "difftime", "mktime", "time", "timespec_get", "timespec_getres", "timegm", "asctime",
   "ctime", "gmtime", "gmtime_r", "localtime", "localtime_r",
   "mbrtoc8", "c8rtomb", "mbrtoc16", "c16rtomb", "mbrtoc32", "c32rtomb",
   "fwprintf", "fwscanf", "swprintf", "swscanf", "vfwprintf", "vfwscanf", "vswprintf", "vswscanf",
   "vwprintf", "vwscanf", "wprintf", "wscanf", "fgetwc", "fgetws", "fputwc", "fputws", "fwide",
   "getwc", "getwchar", "putwc", "putwchar", "ungetwc", "wmemcpy", "wmemmove", "wmemcmp",
   "wmemchr", "wmemset", "btowc", "wctob", "mbsinit", "mbrlen", "mbrtowc", "wcrtomb", "mbsrtowcs",
   "wcsrtombs", "wctype", "wctrans",
   "tmpfile_s", "tmpnam_s", "fopen_s", "freopen_s", "fprintf_s", "fscanf_s", "printf_s", "scanf_s",
   "snprintf_s", "sprintf_s", "sscanf_s", "vfprintf_s", "vfscanf_s", "vprintf_s", "vscanf_s",
   "vsnprintf_s", "vsprintf_s", "vsscanf_s", "gets_s", "set_constraint_handler_s",
   "abort_handler_s", "ignore_handler_s", "getenv_s", "bsearch_s", "qsort_s", "wctomb_s",
   "mbstowcs_s", "wcstombs_s", "asctime_s", "ctime_s", "gmtime_s", "localtime_s", "fwprintf_s",
   "fwscanf_s", "snwprintf_s", "swprintf_s", "swscanf_s", "vfwprintf_s", "vfwscanf_s",
   "vsnwprintf_s", "vswprintf_s", "vswscanf_s", "vwprintf_s", "vwscanf_s", "wprintf_s",
   "wscanf_s", "wcrtomb_s", "mbsrtowcs_s", "wmemcpy_s", "wmemmove_s"]

def cStdlibExternalPrefixes : List String := ["cr_", "stdc_"]

def cStdlibExternalLowerPrefixes : List String :=
  ["is", "to", "str", "mem", "wcs", "fe", "atomic_", "cnd_", "mtx_", "thrd_", "tss_"]

def cExternalNameError? (x : String) : Option String :=
  if cStdlibExternalNames.contains x || cStdlibExternalPrefixes.any (x.startsWith ·) ||
      cStdlibExternalLowerPrefixes.any (fun p =>
        x.startsWith p && ((x.toList.drop p.length).head?.map Char.isLower).getD false) then
    some s!"reserved external identifier '{x}'"
  else none

def cIdentError? (isFun : Bool) (x : String) : Option String :=
  match x.toList with
  | c :: cs =>
    if !((c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')) then
      some s!"invalid identifier '{x}'"
    else if cKeywords.contains x || cReservedNames.contains x || x.startsWith "_br_" ||
        x.startsWith "__" || (c == '_' && (cs.head?.map Char.isUpper).getD false) ||
        x.endsWith "_t" ||
        (x.all (fun c => c.isUpper || c.isDigit || c == '_') &&
          ["_MAX", "_MIN", "_WIDTH", "_C"].any (x.endsWith ·)) ||
        (isFun && (c == '_' || x == "main" || x.startsWith "stdc_" ||
          cPreludeHeaderFunctions.contains x ||
          (["str", "mem", "wcs"].any (x.startsWith ·) && ((cs.drop 2).head?.map Char.isLower).getD false))) then
      some s!"reserved identifier '{x}'"
    else none
  | [] => some s!"invalid identifier '{x}'"

def cCheckIdent (isFun : Bool) (x : String) : Except String Unit :=
  match cIdentError? isFun x with
  | some msg => throw msg
  | none => pure ()

def Cmd.calls : Cmd → List (Bool × List String × String × List Expr)
  | .stackalloc _ _ b | .while _ b => b.calls
  | .cond _ t f | .seq t f => t.calls ++ f.calls
  | .call binds f args => [(true, binds, f, args)]
  | .interact binds a args => [(false, binds, a, args)]
  | _ => []

def Cmd.stackallocDup : Cmd → List String × Option String
  | .stackalloc x _ b =>
    let (xs, e) := b.stackallocDup
    (x :: xs, e <|> if xs.contains x then some x else none)
  | .seq c1 c2 =>
    let (xs, e1) := c1.stackallocDup
    let (ys, e2) := c2.stackallocDup
    (xs ++ ys, e1 <|> e2 <|> xs.find? ys.contains)
  | .cond _ t f => ([], t.stackallocDup.2 <|> f.stackallocDup.2)
  | .while _ b => ([], b.stackallocDup.2)
  | _ => ([], none)

def listUniqLast : List String → List String
  | [] => []
  | a :: l => if l.contains a then listUniqLast l else a :: listUniqLast l

def listFindDup : List String → Option String
  | [] => none
  | a :: l => if l.contains a then some a else listFindDup l

def Expr.tableLengths : Expr → List Nat
  | .literal _ | .var _ => []
  | .load _ ea => ea.tableLengths
  | .inlinetable _ t i => t.length :: i.tableLengths
  | .op1 _ e => e.tableLengths
  | .op _ e1 e2 => e1.tableLengths ++ e2.tableLengths
  | .ite c e1 e2 => c.tableLengths ++ (e1.tableLengths ++ e2.tableLengths)

def Cmd.exprs : Cmd → List Expr
  | .skip | .unset _ => []
  | .set _ e => [e]
  | .store _ ea ev => [ea, ev]
  | .stackalloc _ _ b => b.exprs
  | .cond e t f => e :: (t.exprs ++ f.exprs)
  | .seq c1 c2 => c1.exprs ++ c2.exprs
  | .while e c => e :: c.exprs
  | .call _ _ args | .interact _ _ args => args

def Cmd.stackallocSizes : Cmd → List Nat
  | .stackalloc _ n b => n :: b.stackallocSizes
  | .cond _ t f | .seq t f => t.stackallocSizes ++ f.stackallocSizes
  | .while _ b => b.stackallocSizes
  | _ => []

def cCheckFunc (name : String) (f : Func) : Except String Unit := do
  cCheckIdent true name
  let vars := f.params ++ f.rets ++ f.body.vars
  for x in vars do cCheckIdent false x
  for (isCall, _, g, _) in f.body.calls do
    cCheckIdent true g
    if !isCall && vars.contains g then throw s!"variable '{g}' in '{name}' shadows an interact action"
  for e in f.body.exprs do
    for n in e.tableLengths do
      if n == 0 || n >= 2 ^ 31 then throw s!"inlinetable of length {n} in '{name}'"
  for n in f.body.stackallocSizes do
    if n >= 2 ^ 64 then throw s!"stackalloc of {n} bytes in '{name}'"
  if let some x := listFindDup f.params then throw s!"duplicate parameter '{x}' in '{name}'"
  if let some x := f.body.stackallocDup.2 then
    throw s!"duplicate stackalloc of '{x}' in one block of '{name}'"

def renameOuts : List String → List String → Except String (List (String × String) × List String)
  | [], used => pure ([], used)
  | o :: outs, used => do
    let (rs, used) ← renameOuts outs used
    let o' := "_" ++ o
    if used.contains o' then throw s!"rename_away_from '{o}' = '{o'}' collides"
    if let some msg := cIdentError? false o' then throw s!"rename_away_from '{o}': {msg}"
    pure ((o, o') :: rs, o :: o' :: used)

def fmtCDecl (rett : String) (args : List String) (name : String) (retptrs : List String) : String :=
  let argstring := match args, retptrs with
    | [], [] => "void"
    | _, _ => ", ".intercalate (args.map ("br_word_t " ++ ·) ++ retptrs.map ("br_word_t* " ++ ·))
  rett ++ " " ++ name ++ "(" ++ argstring ++ ")"

def cHeader (name : String) (f : Func) : Except String (String × List (String × String)) := do
  match f.rets with
  | [] => pure (fmtCDecl "void" f.params name [], [])
  | _ :: _ =>
    let (rs, _) ← renameOuts f.rets.dropLast (f.params ++ f.rets ++ f.body.vars)
    pure (fmtCDecl "br_word_t" f.params name (rs.map (·.2)), rs)

def cFuncUnchecked (name : String) (f : Func) (testHooks : Bool) : Except String String := do
  let (decl, rs) ← cHeader name f
  let retvar := f.rets.getLast?
  let allvars := retvar.toList ++ f.body.vars
  let allvars := allvars ++ f.rets.filter (fun r => !allvars.contains r)
  let locals := listUniqLast (allvars.filter (!f.params.contains ·))
  return decl ++ " {\n" ++
    (if locals.isEmpty then "" else "  br_word_t " ++ ", ".intercalate locals ++ ";\n") ++
    cCmd f.body "  " testHooks ++
    String.join (rs.map fun (o, o') => "  *" ++ o' ++ " = " ++ o ++ ";\n") ++
    (match retvar with | none => "" | some r => "  return " ++ r ++ ";\n") ++
    "}\n"

def cFunc (name : String) (f : Func) (testHooks : Bool := false) : Except String String := do
  cCheckFunc name f
  cFuncUnchecked name f testHooks

def cModule (entry internal : List (String × Func)) (testHooks : Bool := false) :
    Except String String := do
  let fs := entry ++ internal
  let names := fs.map (·.1)
  if let some g := listFindDup names then throw s!"duplicate function '{g}'"
  for (name, _) in entry do
    if let some msg := cExternalNameError? name then throw msg
  for (name, f) in fs do
    cCheckFunc name f
    for x in f.params ++ f.rets ++ f.body.vars do
      if names.contains x then throw s!"variable '{x}' in '{name}' shadows a function"
    for (isCall, binds, g, args) in f.body.calls do
      if !isCall then
        if names.contains g then throw s!"interact action '{g}' in '{name}' names a function"
      else
        match fs.lookup g with
        | none => throw s!"call to undefined function '{g}' in '{name}'"
        | some gf =>
          if gf.params.length != args.length || gf.rets.length != binds.length then
            throw s!"call to '{g}' in '{name}' has wrong arity"
  let eDecls ← entry.mapM fun (n, f) => return (← cHeader n f).1 ++ ";"
  let iDecls ← internal.mapM fun (n, f) => return "static " ++ (← cHeader n f).1 ++ ";"
  let eDefs ← entry.mapM fun (n, f) => cFuncUnchecked n f testHooks
  let iDefs ← internal.mapM fun (n, f) => return "static " ++ (← cFuncUnchecked n f testHooks)
  return "\n".intercalate (cPrelude testHooks :: (eDecls ++ iDecls)) ++ "\n\n" ++
    "\n".intercalate (eDefs ++ iDefs)

def cWidthGuard (w : Nat) : Except String String := do
  let max ← match w with
    | 32 => pure "0xFFFFFFFFu"
    | 64 => pure "0xFFFFFFFFFFFFFFFFu"
    | _ => throw s!"unsupported word width {w}"
  return "#include <stdint.h>\n#if UINTPTR_MAX != " ++ max ++ "\n" ++
    s!"#error \"this module requires {w}-bit words\"\n#endif\n"

def cModuleForWidth (w : Nat) (entry internal : List (String × Func)) (testHooks : Bool := false) :
    Except String String :=
  return (← cWidthGuard w) ++ (← cModule entry internal testHooks)

end Kraken.Bedrock2
