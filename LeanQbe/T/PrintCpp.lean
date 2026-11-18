module

public import LeanQbe.T.IL
public import LeanQbe.T.Module

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.PrintCpp

open LeanQbe.T

/-- PHOAS variable representation: C++ variable/parameter identifier string. -/
abbrev SV : Ty → Type := fun _ => String

/-- PHOAS label representation: monotonic block ID, label name, and block parameter names. -/
abbrev SL : List Ty → Type := fun ts => Nat × String × Tup SV ts

/-- A rendered basic block to be emitted after the entry body of a C++ function. -/
structure Block where
  /-- Monotonic label allocation index used to sort blocks deterministically. -/
  id : Nat
  /-- C++ label identifier (e.g. `L_0`). -/
  label : String
  /-- Indented statements inside the block. -/
  body : String
  /-- Target block IDs jumped to directly from this block body. -/
  outJumps : Array Nat := #[]
  deriving Repr

/-- Mutable emitter state for emitting a single C++ function. -/
structure EmitState where
  /-- Next fresh local variable index. -/
  nv : Nat := 0
  /-- Next fresh basic block label index. -/
  nl : Nat := 0
  /-- Top-level local variable and block-parameter declarations. -/
  decls : Array String := #[]
  /-- Accumulated non-entry blocks. -/
  blocks : Array Block := #[]
  /-- Block IDs jumped to during the expression currently being emitted. -/
  curJumps : Array Nat := #[]

/-- Emitter monad threading `EmitState`. -/
abbrev EmitM := StateM EmitState

/-- Mapping from QBE function symbols to collision-free C++ identifiers. -/
abbrev SymMap := Sym → String

/-- C++20 keywords, alternative operator tokens, reserved runtime names, and C macros. -/
def cppKeywords : List String :=
  [ "alignas", "alignof", "and", "and_eq", "asm", "atomic_cancel", "atomic_commit"
  , "atomic_noexcept", "auto", "bitand", "bitor", "bool", "break", "case", "catch"
  , "char", "char8_t", "char16_t", "char32_t", "class", "compl", "concept", "const"
  , "consteval", "constexpr", "constinit", "const_cast", "continue", "co_await"
  , "co_return", "co_yield", "decltype", "default", "delete", "do", "double"
  , "dynamic_cast", "else", "enum", "explicit", "export", "extern", "false"
  , "float", "for", "friend", "goto", "if", "inline", "int", "long", "mutable"
  , "namespace", "new", "noexcept", "not", "not_eq", "nullptr", "operator", "or"
  , "or_eq", "private", "protected", "public", "reflexpr", "register"
  , "reinterpret_cast", "requires", "return", "short", "signed", "sizeof"
  , "static", "static_assert", "static_cast", "struct", "switch", "synchronized"
  , "template", "this", "thread_local", "throw", "true", "try", "typedef"
  , "typeid", "typename", "union", "unsigned", "using", "virtual", "void"
  , "volatile", "wchar_t", "while", "xor", "xor_eq"
  , "main", "tqbe", "std", "mem", "Mem"
  , "NULL", "EOF", "NAN", "INFINITY", "HUGE_VAL", "stdin", "stdout", "stderr"
  , "errno", "abort", "exit"
  ]

/-- Return `true` if `cs` is a non-empty list of decimal digit characters. -/
def allDigits (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all Char.isDigit

/-- Return `true` when `s` matches an emitter-reserved local identifier (`v0`, `p0`, `b0_p0`, `L_0`). -/
def isLocalPattern (s : String) : Bool :=
  match s.toList with
  | 'v' :: rest => allDigits rest
  | 'p' :: rest => allDigits rest
  | 'L' :: '_' :: rest => allDigits rest
  | 'b' :: rest =>
    let lhs := rest.takeWhile Char.isDigit
    let after := rest.dropWhile Char.isDigit
    !lhs.isEmpty && match after with
      | '_' :: 'p' :: rhs => allDigits rhs
      | _ => false
  | _ => false

/-- Deterministically mangle a QBE symbol into a safe C++ identifier base. -/
def baseMangle (s : Sym) : String :=
  let cleaned := String.ofList <| s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  match cleaned.toList with
  | [] => "fn_empty"
  | c :: _ =>
    if c.isDigit || c == '_' || cppKeywords.contains cleaned || isLocalPattern cleaned then
      "fn_" ++ cleaned
    else
      cleaned

/-- Build an injective `Sym → String` map across a list of symbols, rejecting duplicate exact symbols. -/
def buildSymMapNames (syms : List Sym) : Except String SymMap := do
  let mut seen : List Sym := []
  let mut used : List String := []
  let mut pairs : List (Sym × String) := []
  for name in syms do
    if seen.contains name then
      throw s!"duplicate function symbol: {name}"
    seen := name :: seen
    let base := baseMangle name
    let mut cand := base
    let mut k : Nat := 2
    while used.contains cand do
      cand := s!"{base}_{k}"
      k := k + 1
    used := cand :: used
    pairs := (name, cand) :: pairs
  pure fun s =>
    match pairs.find? (fun p => p.1 == s) with
    | some (_, id) => id
    | none => baseMangle s

/-- Build an injective `Sym → String` map across a list of `Fn`s, rejecting duplicate exact symbols. -/
def buildSymMap (fns : List Fn) : Except String SymMap :=
  buildSymMapNames (fns.map Fn.name)

/-- Escape UTF-8 bytes of a string into a valid C++ string literal body (using 3-digit octal escapes). -/
def escapeCString (s : String) : String :=
  let octDigit (n : Nat) : Char := Char.ofNat ('0'.toNat + n)
  String.ofList <| s.toUTF8.toList.foldr (fun b acc =>
    let n := b.toNat
    if n == '\\'.toNat then '\\' :: '\\' :: acc
    else if n == '"'.toNat then '\\' :: '"' :: acc
    else if n == '\n'.toNat then '\\' :: 'n' :: acc
    else if n == '\r'.toNat then '\\' :: 'r' :: acc
    else if n == '\t'.toNat then '\\' :: 't' :: acc
    else if n < 32 || n >= 127 then
      '\\' :: octDigit (n / 64) :: octDigit ((n / 8) % 8) :: octDigit (n % 8) :: acc
    else
      Char.ofNat n :: acc
  ) []

/-- Render a floating-point format tag to its `::tqbe::Fmt` enumerator name. -/
def ppFmt : Fmt → String
  | .h => "h"
  | .s => "s"
  | .d => "d"
  | .q => "q"

/-- Render a `LeanQbe.T.Ty` to its C++ value type in `tqbe_rt.hpp`. -/
def ppTy : Ty → String
  | .bool => "bool"
  | .bits n => s!"::tqbe::bits<{n}>"
  | .float f => s!"::tqbe::fval<::tqbe::Fmt::{ppFmt f}>"
  | .pair a b => s!"::tqbe::pair<{ppTy a}, {ppTy b}>"

/-- Render a list of return types to a C++ function return type. -/
def ppRetTy : List Ty → String
  | [] => "::std::tuple<>"
  | [t] => ppTy t
  | ts => "::std::tuple<" ++ String.intercalate ", " (ts.map ppTy) ++ ">"

/-- Render a natural number in base-16 without a prefix. -/
def natToHex (n : Nat) : String :=
  if n == 0 then "0"
  else String.ofList (Nat.toDigits 16 n)

/-- Render a `w`-bit unsigned natural value as a `::tqbe::bits<w>` C++ expression. -/
def ppBitsNat (w n : Nat) : String :=
  if w == 0 then
    "::tqbe::bits<0>{}"
  else if w <= 64 then
    s!"::tqbe::bits<{w}>(0x{natToHex n}ULL)"
  else
    let nw := (w + 63) / 64
    let mask64 := 1 <<< 64
    let words := (List.range nw).map fun i =>
      let limb := (n >>> (64 * i)) % mask64
      s!"0x{natToHex limb}ULL"
    s!"::tqbe::bits<{w}>::from_words(" ++ "{" ++ String.intercalate ", " words ++ "})"

/-- Render a `LeanQbe.T.Val t` constant to a C++ expression. -/
def ppVal : (t : Ty) → Val t → String
  | .bool, b => if b then "true" else "false"
  | .bits n, v => ppBitsNat n v.toNat
  | .float f, v => s!"::tqbe::fval<::tqbe::Fmt::{ppFmt f}>::from_bits({ppBitsNat f.width v.toNat})"
  | .pair a b, (va, vb) =>
    s!"::tqbe::pair<{ppTy a}, {ppTy b}>" ++ "{" ++ ppVal a va ++ ", " ++ ppVal b vb ++ "}"

/-- Render an `Arg SV t` operand (variable name or constant literal). -/
def ppArg : {t : Ty} → Arg SV t → String
  | _, .var s => s
  | t, .imm v => ppVal t v

/-- Flatten a `Tup (Arg SV) ts` into a list of rendered C++ argument expressions. -/
def ppArgsList : {ts : List Ty} → Tup (Arg SV) ts → List String
  | [], _ => []
  | _ :: _, (a, as) => ppArg a :: ppArgsList as

/-- Flatten a `Tup SV ts` into a list of C++ variable names. -/
def ppTupVars : {ts : List Ty} → Tup SV ts → List String
  | [], _ => []
  | _ :: _, (v, vs) => v :: ppTupVars vs

/-- Allocate a fresh local variable `v<idx>` and record its zero-initialized declaration. -/
def freshVar (t : Ty) (pfx : String := "v") : EmitM String := do
  let st ← get
  let name := s!"{pfx}{st.nv}"
  let decl := s!"  [[maybe_unused]] {ppTy t} {name}" ++ "{};"
  set { st with nv := st.nv + 1, decls := st.decls.push decl }
  pure name

/-- Allocate fresh local variables for a tuple of output types. -/
def freshTup : (ts : List Ty) → EmitM (Tup SV ts)
  | [] => pure PUnit.unit
  | t :: ts => do
    let v ← freshVar t
    let vs ← freshTup ts
    pure (v, vs)

/-- Allocate hoisted block-parameter variables `b<lid>_p<idx>` for a basic block label. -/
def allocBlockParams : (lid : Nat) → (idx : Nat) → (ts : List Ty) → EmitM (Tup SV ts)
  | _, _, [] => pure PUnit.unit
  | lid, idx, t :: ts => do
    let name := s!"b{lid}_p{idx}"
    let st ← get
    let decl := s!"  [[maybe_unused]] {ppTy t} {name}" ++ "{};"
    set { st with decls := st.decls.push decl }
    let rest ← allocBlockParams lid (idx + 1) ts
    pure (name, rest)

/-- Allocate a fresh monotonic label ID `L_<lid>` and its block parameters. -/
def freshLabel (ts : List Ty) : EmitM (SL ts) := do
  let st ← get
  let lid := st.nl
  set { st with nl := lid + 1 }
  let params ← allocBlockParams lid 0 ts
  pure (lid, s!"L_{lid}", params)

/-- Allocate labels for a block group signature `sig`. -/
def allocLabels : (sig : List (List Ty)) → EmitM (Tup SL sig)
  | [] => pure PUnit.unit
  | ts :: sig => do
    let l ← freshLabel ts
    let ls ← allocLabels sig
    pure (l, ls)

/-- Render a `CmpOp` to its `::tqbe::CmpOp` enumerator name. -/
def ppCmpOp : CmpOp → String
  | .eq  => "eq"
  | .ne  => "ne"
  | .ult => "ult"
  | .ule => "ule"
  | .ugt => "ugt"
  | .uge => "uge"
  | .slt => "slt"
  | .sle => "sle"
  | .sgt => "sgt"
  | .sge => "sge"

/-- Render an `FCmpOp` to its `::tqbe::FCmpOp` enumerator name. -/
def ppFCmpOp : FCmpOp → String
  | .eq  => "eq"
  | .ne  => "ne"
  | .lt  => "lt"
  | .le  => "le"
  | .gt  => "gt"
  | .ge  => "ge"
  | .ord => "ord"
  | .uno => "uno"

/-- Totally render any `OpCode sig rs` statement binding `outs` from `args`. -/
def ppOpCode : {sig rs : List Ty} → OpCode sig rs → Tup SV rs → Tup (Arg SV) sig → String
  | _, _, .copy _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_copy({ppArg a});\n"
  | _, _, .add _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_add({ppArg a}, {ppArg b});\n"
  | _, _, .sub _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_sub({ppArg a}, {ppArg b});\n"
  | _, _, .mul _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_mul({ppArg a}, {ppArg b});\n"
  | _, _, .neg _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_neg({ppArg a});\n"
  | _, _, .and _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_and({ppArg a}, {ppArg b});\n"
  | _, _, .or _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_or({ppArg a}, {ppArg b});\n"
  | _, _, .xor _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_xor({ppArg a}, {ppArg b});\n"
  | _, _, .not _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_not({ppArg a});\n"
  | _, _, .ternlog _ imm, (v, _), (a, b, c, _) =>
    s!"  {v} = ::tqbe::op_ternlog({ppArg a}, {ppArg b}, {ppArg c}, {imm.toNat}U);\n"
  | _, _, .shl _, (v, _), (a, s, _) => s!"  {v} = ::tqbe::op_shl({ppArg a}, {ppArg s});\n"
  | _, _, .lshr _, (v, _), (a, s, _) => s!"  {v} = ::tqbe::op_lshr({ppArg a}, {ppArg s});\n"
  | _, _, .ashr _, (v, _), (a, s, _) => s!"  {v} = ::tqbe::op_ashr({ppArg a}, {ppArg s});\n"
  | _, _, .rotl _, (v, _), (a, s, _) => s!"  {v} = ::tqbe::op_rotl({ppArg a}, {ppArg s});\n"
  | _, _, .rotr _, (v, _), (a, s, _) => s!"  {v} = ::tqbe::op_rotr({ppArg a}, {ppArg s});\n"
  | _, _, .fshl n, (v, _), (a, b, c, _) =>
    s!"  {v} = ::tqbe::op_fshl<{n}>({ppArg a}, {ppArg b}, {ppArg c});\n"
  | _, _, .fshr n, (v, _), (a, b, c, _) =>
    s!"  {v} = ::tqbe::op_fshr<{n}>({ppArg a}, {ppArg b}, {ppArg c});\n"
  | _, _, .bswap _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_bswap({ppArg a});\n"
  | _, _, .clz n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_clz<{n}>({ppArg a});\n"
  | _, _, .cls n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_cls<{n}>({ppArg a});\n"
  | _, _, .rbit n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_rbit<{n}>({ppArg a});\n"
  | _, _, .ctz n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_ctz<{n}>({ppArg a});\n"
  | _, _, .popcnt n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_popcnt<{n}>({ppArg a});\n"
  | _, _, .cmp op _ _ _, (v, _), (a, b, _) =>
    s!"  {v} = ::tqbe::op_cmp<::tqbe::CmpOp::{ppCmpOp op}>({ppArg a}, {ppArg b});\n"
  | _, _, .select _, (v, _), (c, a, b, _) =>
    s!"  {v} = ::tqbe::op_select({ppArg c}, {ppArg a}, {ppArg b});\n"
  | _, _, .blend _ _ _, (v, _), (m, a, b, _) =>
    s!"  {v} = ::tqbe::op_blend({ppArg m}, {ppArg a}, {ppArg b});\n"
  | _, _, .zext m n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_zext<{m}, {n}>({ppArg a});\n"
  | _, _, .sext m n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_sext<{m}, {n}>({ppArg a});\n"
  | _, _, .trunc m n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_trunc<{m}, {n}>({ppArg a});\n"
  | _, _, .ofBool n, (v, _), (a, _) =>
    s!"  {v} = ({ppArg a} ? ::tqbe::bits<{n}>(1ULL) : ::tqbe::bits<{n}>(0ULL));\n"
  | _, _, .addc n, (s, c, _), (a, b, cin, _) =>
    s!"  do " ++ "{ " ++ s!"auto _r = ::tqbe::op_addc<{n}>({ppArg a}, {ppArg b}, {ppArg cin}); {s} = _r.first; {c} = _r.second;" ++ " }" ++ " while (0);\n"
  | _, _, .subb n, (d, b, _), (x, y, bin, _) =>
    s!"  do " ++ "{ " ++ s!"auto _r = ::tqbe::op_subb<{n}>({ppArg x}, {ppArg y}, {ppArg bin}); {d} = _r.first; {b} = _r.second;" ++ " }" ++ " while (0);\n"
  | _, _, .umulw n, (lo, hi, _), (a, b, _) =>
    s!"  do " ++ "{ " ++ s!"auto _r = ::tqbe::op_umulw<{n}>({ppArg a}, {ppArg b}); {lo} = _r.first; {hi} = _r.second;" ++ " }" ++ " while (0);\n"
  | _, _, .smulw n, (lo, hi, _), (a, b, _) =>
    s!"  do " ++ "{ " ++ s!"auto _r = ::tqbe::op_smulw<{n}>({ppArg a}, {ppArg b}); {lo} = _r.first; {hi} = _r.second;" ++ " }" ++ " while (0);\n"
  | _, _, .udiv n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_udiv<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .sdiv n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_sdiv<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .urem n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_urem<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .srem n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_srem<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .udiv0 n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_udiv0<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .sdiv0 n, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_sdiv0<{n}>({ppArg a}, {ppArg b});\n"
  | _, _, .mkpair _ _, (v, _), (a, b, _) => s!"  {v} = " ++ "{" ++ s!"{ppArg a}, {ppArg b}" ++ "};\n"
  | _, _, .unpair _ _, (x, y, _), (p, _) =>
    s!"  do " ++ "{ " ++ s!"auto _p = {ppArg p}; {x} = _p.first; {y} = _p.second;" ++ " }" ++ " while (0);\n"
  | _, _, .bitcast _ u _, (v, _), (a, _) =>
    s!"  {v} = ::tqbe::op_bitcast<{ppTy u}>({ppArg a});\n"
  | _, _, .shufd _ imm, (v, _), (a, _) => s!"  {v} = ::tqbe::op_shufd({ppArg a}, {imm.toNat}U);\n"
  | _, _, .shufb _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_shufb({ppArg a}, {ppArg b});\n"
  | _, _, .alignr _ imm, (v, _), (hi, lo, _) => s!"  {v} = ::tqbe::op_alignr({ppArg hi}, {ppArg lo}, {imm.toNat}U);\n"
  | _, _, .blendw _ imm, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_blendw({ppArg a}, {ppArg b}, {imm.toNat}U);\n"
  | _, _, .sha256rnds2, (v, _), (cdgh, abef, wk, _) =>
    s!"  {v} = ::tqbe::op_sha256rnds2({ppArg cdgh}, {ppArg abef}, {ppArg wk});\n"
  | _, _, .sha256msg1, (v, _), (w0123, w4, _) =>
    s!"  {v} = ::tqbe::op_sha256msg1({ppArg w0123}, {ppArg w4});\n"
  | _, _, .sha256msg2, (v, _), (sums, w, _) =>
    s!"  {v} = ::tqbe::op_sha256msg2({ppArg sums}, {ppArg w});\n"
  | _, _, .fadd _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_fadd({ppArg a}, {ppArg b});\n"
  | _, _, .fsub _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_fsub({ppArg a}, {ppArg b});\n"
  | _, _, .fmul _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_fmul({ppArg a}, {ppArg b});\n"
  | _, _, .fdiv _, (v, _), (a, b, _) => s!"  {v} = ::tqbe::op_fdiv({ppArg a}, {ppArg b});\n"
  | _, _, .ffma _, (v, _), (a, b, c, _) => s!"  {v} = ::tqbe::op_ffma({ppArg a}, {ppArg b}, {ppArg c});\n"
  | _, _, .fsqrt _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_fsqrt({ppArg a});\n"
  | _, _, .fneg _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_fneg({ppArg a});\n"
  | _, _, .fabs _, (v, _), (a, _) => s!"  {v} = ::tqbe::op_fabs({ppArg a});\n"
  | _, _, .fcmp op _ _ _, (v, _), (a, b, _) =>
    s!"  {v} = ::tqbe::op_fcmp<::tqbe::FCmpOp::{ppFCmpOp op}>({ppArg a}, {ppArg b});\n"
  | _, _, .fptoui f n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_fptoui<::tqbe::Fmt::{ppFmt f}, {n}>({ppArg a});\n"
  | _, _, .fptosi f n, (v, _), (a, _) => s!"  {v} = ::tqbe::op_fptosi<::tqbe::Fmt::{ppFmt f}, {n}>({ppArg a});\n"
  | _, _, .uitofp n f, (v, _), (a, _) => s!"  {v} = ::tqbe::op_uitofp<{n}, ::tqbe::Fmt::{ppFmt f}>({ppArg a});\n"
  | _, _, .sitofp n f, (v, _), (a, _) => s!"  {v} = ::tqbe::op_sitofp<{n}, ::tqbe::Fmt::{ppFmt f}>({ppArg a});\n"
  | _, _, .fcvt src dst, (v, _), (a, _) =>
    s!"  {v} = ::tqbe::op_fcvt<::tqbe::Fmt::{ppFmt src}, ::tqbe::Fmt::{ppFmt dst}>({ppArg a});\n"

/-- Render a call statement binding result tuple `outs`. -/
def ppAssignCall : {bs : List Ty} → Tup SV bs → String → List String → String
  | [], _, callee, args =>
    let argStr := String.intercalate ", " ("mem" :: args)
    s!"  (void){callee}({argStr});\n"
  | [_], (v, _), callee, args =>
    let argStr := String.intercalate ", " ("mem" :: args)
    s!"  {v} = {callee}({argStr});\n"
  | _ :: _ :: _, outs, callee, args =>
    let argStr := String.intercalate ", " ("mem" :: args)
    let vs := String.intercalate ", " (ppTupVars outs)
    s!"  ::std::tie({vs}) = {callee}({argStr});\n"

/-- Render a return statement from a tuple of result arguments. -/
def ppRetStmt : {rs : List Ty} → Tup (Arg SV) rs → String
  | [], _ => "  return {};\n"
  | [_], (a, _) => s!"  return {ppArg a};\n"
  | _ :: _ :: _, vs =>
    "  return ::std::make_tuple(" ++ String.intercalate ", " (ppArgsList vs) ++ ");\n"

/-- Record a jump target ID in the active expression's jump set. -/
def recordJump (lid : Nat) : EmitM Unit :=
  modify fun st =>
    if st.curJumps.contains lid then st else { st with curJumps := st.curJumps.push lid }

/-- Pair block parameter variable names with their rendered jump argument expressions. -/
def collectJumpPairs : {ts : List Ty} → Tup SV ts → Tup (Arg SV) ts → List (String × String)
  | [], _, _ => []
  | _ :: _, (p, ps), (a, as) => (p, ppArg a) :: collectJumpPairs ps as

/-- Render simultaneous assignments to block parameters before a `goto` (eliding `p = p` self-copies). -/
def ppJumpArgs {ts : List Ty} (ps : Tup SV ts) (as : Tup (Arg SV) ts) : String :=
  let pairs := (collectJumpPairs ps as).filter fun (p, a) => p != a
  match pairs with
  | [] => ""
  | [(p, a)] => s!"  {p} = {a};\n"
  | _ =>
    let tmps := pairs.zipIdx.map fun ((_, a), i) => s!"    auto _j{i} = {a};"
    let assigns := pairs.zipIdx.map fun ((p, _), i) => s!"    {p} = _j{i};"
    "  do {\n" ++ String.intercalate "\n" tmps ++ "\n"
      ++ String.intercalate "\n" assigns ++ "\n  } while (0);\n"

mutual
  /-- Directly emit C++ statements from a PHOAS `Expr SV SL rs`. -/
  def ppE (symMap : SymMap) {rs : List Ty} : Expr SV SL rs → EmitM String
    | .let_ (ts := ts) op k => do
      let outs ← freshTup ts
      let s := ppOpCode op.code outs op.args
      let rest ← ppE symMap (k outs)
      pure (s ++ rest)
    | .load t a k => do
      let out ← freshVar t
      let s := s!"  {out} = ::tqbe::load<{ppTy t}>(mem, {ppArg a});\n"
      let rest ← ppE symMap (k out)
      pure (s ++ rest)
    | .store (t := t) v a k => do
      let s := s!"  ::tqbe::store<{ppTy t}>(mem, {ppArg a}, {ppArg v});\n"
      let rest ← ppE symMap k
      pure (s ++ rest)
    | .call f (bs := bs) args k => do
      let outs ← freshTup bs
      let s := ppAssignCall outs (symMap f) (ppArgsList args)
      let rest ← ppE symMap (k outs)
      pure (s ++ rest)
    | .jnz c t e => do
      let st ← ppE symMap t
      let se ← ppE symMap e
      pure (s!"  if ({ppArg c}) " ++ "{\n" ++ st ++ "  } else {\n" ++ se ++ "  }\n")
    | .jump j args => do
      recordJump j.1
      pure (ppJumpArgs j.2.2 args ++ s!"  goto {j.2.1};\n")
    | .ret vs =>
      pure (ppRetStmt vs)
    | .exit f args =>
      let argStr := String.intercalate ", " (s!"\"{escapeCString f}\"" :: ppArgsList args)
      pure s!"  ::tqbe::exit_call({argStr});\n"
    | .hlt =>
      pure "  TQBE_HLT();\n"
    | .group (sig := sig) bodies k => do
      let ls ← allocLabels sig
      ppB symMap ls (bodies ls)
      ppE symMap (k ls)

  /-- Emit all blocks of a mutually recursive PHOAS `Blocks SV SL rs sig`. -/
  def ppB (symMap : SymMap) {rs : List Ty} : {sig : List (List Ty)} → Tup SL sig → Blocks SV SL rs sig → EmitM Unit
    | [], _, .nil => pure ()
    | _ :: _, (l, ls), .cons b bs => do
      let savedJumps := (← get).curJumps
      modify fun st => { st with curJumps := #[] }
      let bodyStr ← ppE symMap (b l.2.2)
      let blkJumps := (← get).curJumps
      modify fun st =>
        { st with
          curJumps := savedJumps
          blocks := st.blocks.push { id := l.1, label := l.2.1, body := bodyStr, outJumps := blkJumps } }
      ppB symMap ls bs
end

/-- Compute block IDs reachable from entry jumps to avoid `-Wunused-label` on dead blocks. -/
def reachableBlockIds (blocks : Array Block) (seeds : Array Nat) : Array Nat :=
  Id.run do
    let isKnown (id : Nat) : Bool := blocks.any fun b => b.id == id
    let mut enqueued : Array Nat := #[]
    let mut queue : List Nat := []
    for s in seeds do
      if isKnown s && !enqueued.contains s then
        enqueued := enqueued.push s
        queue := s :: queue
    for _ in List.range (blocks.size + 1) do
      match queue with
      | [] => break
      | id :: rest =>
        queue := rest
        if let some blk := blocks.find? (fun b => b.id == id) then
          for dst in blk.outJumps do
            if isKnown dst && !enqueued.contains dst then
              enqueued := enqueued.push dst
              queue := dst :: queue
    pure enqueued

/-- Format C++ function parameter declarations and `(void)`-suppression lines. -/
def ppFnSigParams (as : List Ty) : String × List String :=
  let (decls, voids) := as.zipIdx.foldr (fun (t, i) (ds, vs) =>
    let p := s!"p{i}"
    (s!"{ppTy t} {p}" :: ds, s!"  (void){p};\n" :: vs)
  ) ([], [])
  let paramList := String.intercalate ", " ("::tqbe::Mem& mem" :: decls)
  (paramList, voids)

/-- Construct initial parameter names `p0, p1, ...` for a function entry. -/
def allocEntryParams : (idx : Nat) → (ts : List Ty) → Tup SV ts
  | _, [] => PUnit.unit
  | idx, _ :: ts => (s!"p{idx}", allocEntryParams (idx + 1) ts)

/-- Render a forward declaration for a single `Fn`. -/
def ppFnDecl (symMap : SymMap := baseMangle) (fn : Fn) : String :=
  let (paramStr, _) := ppFnSigParams fn.as
  s!"{ppRetTy fn.rs} {symMap fn.name}({paramStr});\n"

/-- Render a forward declaration for an external function `Extern`. -/
def ppExternDecl (symMap : SymMap := baseMangle) (ex : Extern) : String :=
  let (paramStr, _) := ppFnSigParams ex.as
  s!"{ppRetTy ex.rs} {symMap ex.name}({paramStr});\n"

/-- Render a full C++ function definition directly from a PHOAS `Fn`. -/
def ppFn (symMap : SymMap := baseMangle) (fn : Fn) : String :=
  let (paramStr, paramVoids) := ppFnSigParams fn.as
  let initParams := allocEntryParams 0 fn.as
  let (entryBody, st) := (ppE symMap (fn.body SV SL initParams)).run {}
  let declsStr := String.intercalate "\n" st.decls.toList
  let declBlock := if st.decls.isEmpty then "" else declsStr ++ "\n"
  let liveIds := reachableBlockIds st.blocks st.curJumps
  let sortedBlocks := (st.blocks.toList.filter fun b => liveIds.contains b.id).mergeSort (fun a b => a.id ≤ b.id)
  let blocksStr := String.join <| sortedBlocks.map fun blk =>
    s!"{blk.label}:\n{blk.body}"
  let voidStr := "  (void)mem;\n" ++ String.join paramVoids
  s!"{ppRetTy fn.rs} {symMap fn.name}({paramStr}) " ++ "{\n"
    ++ voidStr ++ declBlock ++ entryBody ++ blocksStr ++ "  TQBE_UB(\"fallthrough\");\n}\n"

/-- Render a complete standalone C++20 translation unit for a list of `Fn`s. -/
def ppModule (fns : List Fn) : Except String String := do
  let symMap ← buildSymMap fns
  let hdr := "#include \"tqbe_rt.hpp\"\n\n"
  let decls := String.join (fns.map (ppFnDecl symMap))
  let sep := if fns.isEmpty then "" else "\n"
  let defs := String.intercalate "\n" (fns.map (ppFn symMap))
  pure (hdr ++ decls ++ sep ++ defs)

/-- Render a complete standalone C++20 translation unit for a `LeanQbe.T.Module`
(checking symbol uniqueness across both `M.fns` and `M.externs`). -/
def ppTModule (M : Module) : Except String String := do
  let symMap ← buildSymMapNames M.names
  let hdr := "#include \"tqbe_rt.hpp\"\n\n"
  let extDecls := String.join (M.externs.map (ppExternDecl symMap))
  let fnDecls := String.join (M.fns.map (ppFnDecl symMap))
  let decls := extDecls ++ fnDecls
  let sep := if decls.isEmpty || M.fns.isEmpty then "" else "\n"
  let defs := String.intercalate "\n" (M.fns.map (ppFn symMap))
  pure (hdr ++ decls ++ sep ++ defs)

end LeanQbe.T.PrintCpp

end
