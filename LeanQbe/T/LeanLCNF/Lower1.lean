module

public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.LeanLRC.ToT

/-!
# Impure `LCNF` → `LeanQbe.T`: code, declarations, closures and modules

* `lowerCode`: `let` → inline op / call, non-recursive `jp`/`jmp` → one-block `.group`/`.jump`,
  `cases` → tag dispatch (`jnz` chain), self tail calls `let r := f ys; return r` → `.jump` to a
  `loop1` header (O(1) stack, loop-carried registers), `unreach` → `exit lcnf_panic`.
  It is structurally recursive on `LcCode` (mutually with `lowerAlts`), and the static
  environments (`LEnv`, `LCtx`) are association lists, so `lowerModule` is total and reduces in
  the kernel (no `partial`, no `Std.HashMap`/`String.hash`); `splice_lcnf_tflat!` relies on this
  to emit a kernel-checked `<tfs>_lower : lowerModule lc = .ok <tfs>_raw`.
* `lowerDecl`: `rt` + 5 register parameters, the rest reloaded from `rt->extra_args`; closed
  constants (0 parameters) are read through `rt->globals` once-cells and marked persistent.
* `genApply k`: defunctionalized `lcnf_apply_k` (exact application dispatches on `fun_id` through
  a balanced `jnz` tree; under-application extends the closure; over-application chains
  `lcnf_apply_r` and `lcnf_apply_(k-r)`).
* `lowerModule`: every function is scope-checked by `lExprToTFlat` + `TFlat.wfCheck`;
  `LeanLRC.tflatFnsToFns_wf` gives `Func.Wf` for every reified function.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0 (LExpr LVar LArg LOp LFlatCtx lExprToTFlat TFlatFn)

instance : Inhabited LExpr := ⟨.hlt⟩

/-- Static lowering environment of one module. Every map is an association list (newest binding
first, looked up with `List.lookup`), so that lookups reduce in the kernel. -/
structure LEnv where
  decls : List (String × LcDecl)
  funIds : List (String × Nat)
  globals : List (String × Nat)
  strLits : List (String × Nat)
  bigNatLits : List (Nat × Nat)

/-- Per-function lowering context. -/
structure LCtx where
  fn : String
  rt : LArg
  retTy : LcTy
  params : List LcTy
  vars : List (Nat × LArg × LcTy) := []
  jps : List (Nat × Nat × List LcTy) := []
  loop? : Option Nat := none

/-- Look up a variable. -/
def LCtx.var (c : LCtx) (x : Nat) : LM (LArg × LcTy) :=
  match c.vars.lookup x with
  | some r => pure r
  | none => lfail s!"LeanLCNF ({c.fn}): unbound variable x.{x}"

/-- Bind a variable. -/
def LCtx.bind (c : LCtx) (x : Nat) (a : LArg) (t : LcTy) : LCtx :=
  { c with vars := (x, a, t) :: c.vars }

/-- Bind parameters to operands. -/
def LCtx.bindAll (c : LCtx) (ps : List LcParam) (as : List LArg) : LCtx :=
  (ps.zip as).foldl (fun cc (p, a) => cc.bind p.id a p.ty) c

/-- An argument at expected type `t`. -/
def argAt (c : LCtx) (a : LcArg) (t : LcTy) : LM LArg :=
  match a with
  | .erased => pure (imm t.width (if t.isScalar then 0 else 1))
  | .var x => do
    let (v, vt) ← c.var x
    if vt.width == t.width then pure v
    else lfail s!"LeanLCNF ({c.fn}): x.{x} has width {vt.width}, expected {t.width}"

/-- An argument at its own type (erased → `box(0)`). -/
def argOwn (c : LCtx) (a : LcArg) : LM LArg :=
  match a with
  | .erased => pure (imm64 1)
  | .var x => do pure (← c.var x).1

/-! ## Calls with `extra_args` spilling -/

/-- Store arguments `5..` into `rt->extra_args`. -/
def spillExtras (rt : LArg) : Nat → List (LArg × Ty) → LM LExpr → LM LExpr
  | _, [], k => k
  | i, (a, t) :: rest, k => storeAt t a rt (rtExtraOff + 8 * i) (spillExtras rt (i + 1) rest k)

/-- Reload parameters `5..` from `rt->extra_args`. -/
def loadExtras (rt : LArg) : Nat → List Ty → (List LArg → LM LExpr) → LM LExpr
  | _, [], k => k []
  | i, t :: ts, k => loadAt t rt (rtExtraOff + 8 * i) fun v =>
    loadExtras rt (i + 1) ts fun vs => k (v :: vs)

/-- Call a lowered function `sym(rt, args...)`. -/
def callFn (rt : LArg) (sym : Sym) (args : List (LArg × Ty)) (ret : Ty)
    (k : LArg → LM LExpr) : LM LExpr := do
  if args.length > regArgs + rtExtraSlots then lfail s!"LeanLCNF: too many arguments to {sym}"
  let regs := args.take regArgs
  spillExtras rt 0 (args.drop regArgs) <|
    call1 sym (i64 :: regs.map (·.2)) ret (rt :: regs.map (·.1)) k

/-! ## Values -/

/-- Pack a UTF-8 `ByteArray` into 64-bit little-endian words (zero-padded). -/
def packBytesLE (bs : ByteArray) : List Nat :=
  let nw := (bs.size + 7) / 8
  (List.range nw).map fun k =>
    (List.range 8).foldl (fun acc b =>
      let idx := 8 * k + b
      let byte := if h : idx < bs.size then (bs[idx]'h).toNat else 0
      acc + byte * 2 ^ (8 * b)) 0

/-- Split a non-negative `Nat` into 64-bit little-endian limbs (`[]` for `0`). -/
def natToLimbs (n : Nat) : List Nat :=
  if h : n == 0 then []
  else (n % 2 ^ 64) :: natToLimbs (n / 2 ^ 64)
termination_by n
decreasing_by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by simpa using h)
  exact Nat.div_lt_self hpos (by decide)

/-- Initialize and read a `rt->globals` once-cell, marking the built object persistent. -/
def readOnceCell (rt : LArg) (slot : Nat) (build : (LArg → LM LExpr) → LM LExpr)
    (k : LArg → LM LExpr) : LM LExpr :=
  let off := rtGlobalsOff + 8 * slot
  loadAt i64 rt off fun g => withJoin1 i64 k fun j => do
    let init ← build fun r =>
      call0 "lcnf_mark_persistent" [i64, i64] [rt, r] (storeAt i64 r rt off (pure (j r)))
    cmpOp .eq 64 g (imm64 0) fun z => pure (.jnz z init (j g))

/-- Read a closed constant through its `rt->globals` once-cell. -/
def readConst (rt : LArg) (sym : Sym) (slot : Nat) (k : LArg → LM LExpr) : LM LExpr :=
  readOnceCell rt slot (call1 sym [i64] i64 [rt]) k

/-- Materialize a string literal into its `rt->globals` once-cell. -/
def readStrLit (rt : LArg) (slot : Nat) (s : String) (k : LArg → LM LExpr) : LM LExpr :=
  let bs := s.toUTF8
  let words := (packBytesLE bs).map imm64
  readOnceCell rt slot (fun done =>
    call1 "lcnf_str_alloc" [i64, i64, i64] i64 [rt, imm64 bs.size, imm64 s.length] fun p =>
      storeFields p 32 words (done p)) k

/-- Materialize a big `Nat` literal (`≥ 2^63`) into its `rt->globals` once-cell. -/
def readBigNatLit (rt : LArg) (slot n : Nat) (k : LArg → LM LExpr) : LM LExpr :=
  let limbs := (natToLimbs n).map imm64
  readOnceCell rt slot (fun done =>
    call1 "lcnf_nat_alloc" [i64, i64] i64 [rt, imm64 limbs.length] fun p =>
      storeFields p 16 limbs (done p)) k

/-- `fap f as`. -/
def lowerFap (env : LEnv) (c : LCtx) (f : String) (as : List LcArg) (ty : LcTy)
    (k : LArg → LM LExpr) : LM LExpr := do
  match env.decls.lookup f with
  | some d =>
    if d.params.isEmpty && !d.retTy.isScalar then
      match env.globals.lookup f with
      | some slot => readConst c.rt (mangleLc f) slot k
      | none => lfail s!"LeanLCNF: constant {f} has no global slot"
    else
      if as.length != d.params.length then lfail s!"LeanLCNF ({c.fn}): fap {f} arity"
      let args ← (as.zip d.params).mapM fun (a, p) => do
        pure (← argAt c a p.ty, p.ty.toTTy)
      callFn c.rt (mangleLc f) args d.retTy.toTTy fun r => convW d.retTy.width ty.width r k
  | none =>
    let args ← as.mapM (argOwn c)
    externPrim c.rt f args k

/-- `pap f as`: allocate a defunctionalized closure. -/
def lowerPap (env : LEnv) (c : LCtx) (f : String) (as : List LcArg) (k : LArg → LM LExpr) :
    LM LExpr := do
  let some fid := env.funIds.lookup f | lfail s!"LeanLCNF: pap target {f} not in closure table"
  let some d := env.decls.lookup f | lfail s!"LeanLCNF: pap target {f} has no code"
  let nfix := as.length
  let sz := 24 + 8 * nfix
  let vs ← as.mapM (argOwn c)
  allocObj c.rt sz (1 + sz * 2 ^ 32 + closureTag * 2 ^ 56) fun p =>
    storeAt i64 (imm64 fid) p 8 <|
    storeAt i32 (imm 32 (d.params.length + nfix * 65536)) p 16 <|
    storeAt i32 (imm 32 0) p 20 <|
    storeFields p 24 vs (k p)

/-- `reset n x` (only reached if `ExpandResetReuse` left one): exclusive → release the `n`
fields (`lean_ctor_release`: `dec` each and overwrite it with `box(0)`, so a token that is later
`dec`'d instead of reused frees nothing twice) and reuse `x`; shared → `dec x`, `box(0)`. -/
def lowerReset (c : LCtx) (n : Nat) (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  withJoin1 i64 k fun j => do
    let rec decFields : Nat → LM LExpr
      | 0 => pure (j x)
      | i + 1 =>
        let off := 8 + 8 * (n - 1 - i)
        loadAt i64 x off fun y =>
        emitDec1 c.rt y .tobject true (storeAt i64 (imm64 1) x off (decFields i))
    let ex ← decFields n
    let sh ← emitDec1 c.rt x .object false (pure (j (imm64 1)))
    loadAt i32 x 0 fun rc => cmpOp .eq 32 rc (imm 32 1) fun e => pure (.jnz e ex sh)

/-- `reuse x in ctor_i ys`: reuse the cell unless `reset` produced `box(0)` (the scalar test is
emitted before the join is opened, see `emitInc`). -/
def lowerReuse (c : LCtx) (x : LArg) (ci : LcCtor) (upd : Bool) (vs : List LArg)
    (k : LArg → LM LExpr) : LM LExpr :=
  isScalarObj x fun s => withJoin1 i64 (fun p => storeFields p 8 vs (k p)) fun j => do
    let fresh ← allocObj c.rt ci.byteSize ci.header fun p => pure (j p)
    let keep ← if upd then storeAt i8 (imm 8 ci.cidx) x 7 (pure (j x)) else pure (j x)
    pure (.jnz s fresh keep)

/-- Kernel-reducible `s!"lcnf_apply_{k}"` (`Nat.repr` is unexposed in `module` mode). -/
def applySym (k : Nat) : Sym :=
  "lcnf_apply_" ++ String.ofList (natDigits 10 k)

/-- Lower a `LetValue` bound at type `ty`. -/
def lowerVal (env : LEnv) (c : LCtx) (ty : LcTy) (v : LcVal) (k : LArg → LM LExpr) :
    LM LExpr := do
  let w := ty.width
  match v with
  | .lit (.nat n) =>
    if n < 2 ^ 63 then k (imm64 (2 * n + 1))
    else match env.bigNatLits.lookup n with
      | some slot => readBigNatLit c.rt slot n k
      | none => lfail s!"LeanLCNF ({c.fn}): big Nat literal {n} has no global slot"
  | .lit (.scalar n) => k (imm w n)
  | .lit (.str s) =>
    match env.strLits.lookup s with
    | some slot => readStrLit c.rt slot s k
    | none => lfail s!"LeanLCNF ({c.fn}): string literal has no global slot"
  | .erased => k (imm w (if ty.isScalar then 0 else 1))
  | .ap f as =>
    let (fa, _) ← c.var f
    let vs ← as.mapM (argOwn c)
    callFn c.rt (applySym as.length) ((fa :: vs).map (·, i64)) i64 k
  | .ctor ci as =>
    if ci.isScalar then k (imm w (if ty.isScalar then ci.cidx else 2 * ci.cidx + 1))
    else
      let vs ← as.mapM fun a => argAt c a .tobject
      allocObj c.rt ci.byteSize ci.header fun p => storeFields p 8 vs (k p)
  | .oproj i x | .uproj i x => do loadAt i64 (← c.var x).1 (8 + 8 * i) k
  | .sproj n off x => do loadAt ty.toTTy (← c.var x).1 (8 + 8 * n + off) k
  | .fap f as => lowerFap env c f as ty k
  | .pap f as => lowerPap env c f as k
  | .reset n x => do lowerReset c n (← c.var x).1 k
  | .reuse x ci upd as => do
    let vs ← as.mapM fun a => argAt c a .tobject
    lowerReuse c (← c.var x).1 ci upd vs k
  | .box t x =>
    let (xa, _) ← c.var x
    match t with
    | .uint64 | .usize | .float => boxU64 c.rt xa k
    | .uint8 | .uint16 | .uint32 => convW t.width 64 xa fun x64 => boxSmall x64 k
    | _ => k xa
  | .unbox x =>
    let (xa, _) ← c.var x
    match ty with
    | .uint64 | .usize | .float => loadAt i64 xa 8 k
    | _ => lshr64 xa (imm64 1) fun u => convW 64 w u k
  | .isShared x => do
    loadAt i32 (← c.var x).1 0 fun rc => cmpOp .ne 32 rc (imm 32 1) fun b => boolToU8 b k

/-! ## Code -/

/-- Is `let x := f ys; return x` (with `f` the current function) the shape of `code`? -/
def isSelfTail (fn : String) (arity : Nat) : LcCode → Bool
  | .let_ x _ (.fap f as) (.ret (.var y)) => x == y && f == fn && as.length == arity
  | _ => false

mutual
/-- Does `code` contain a self tail call? -/
def hasSelfTail (fn : String) (arity : Nat) : LcCode → Bool
  | c@(.let_ _ _ _ k) => isSelfTail fn arity c || hasSelfTail fn arity k
  | .jp _ _ b k => hasSelfTail fn arity b || hasSelfTail fn arity k
  | .cases _ alts => altsHaveSelfTail fn arity alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => hasSelfTail fn arity k
  | .jmp _ _ | .ret _ | .unreach => false

/-- `hasSelfTail` over alternatives. -/
def altsHaveSelfTail (fn : String) (arity : Nat) : List (LcPat × LcCode) → Bool
  | [] => false
  | (_, b) :: rest => hasSelfTail fn arity b || altsHaveSelfTail fn arity rest
end

/-- The loop-back `.jump` of a self tail call, when `code` is `let x := f ys; return x` with `f`
the current function and a loop header is open. -/
def selfTailJump? (c : LCtx) (code : LcCode) : Option (LM LExpr) :=
  match code, c.loop? with
  | .let_ _ _ (.fap _ as) _, some lbl =>
    if isSelfTail c.fn c.params.length code then
      some do
        let args ← (as.zip c.params).mapM fun (a, t) => argAt c a t
        pure (.jump lbl (c.params.map LcTy.toTTy) args)
    else none
  | _, _ => none

/-- Dispatch on a computed tag of width `w` over already lowered alternatives. -/
def dispatchAlts (tag : LArg) (w : Nat) : List (LcPat × LM LExpr) → LM LExpr
  | [] => pure .hlt
  | [(_, b)] => b
  | (.dflt, b) :: _ => b
  | (.ctor ci _, b) :: rest => cmpOp .eq w tag (imm w ci) fun e => do
    pure (.jnz e (← b) (← dispatchAlts tag w rest))

/-- Lower `cases` over already lowered alternatives (unrun builder actions, so the fresh-id
order is the dispatch order): compute the tag once, then a `jnz` chain over the alternatives.
For a `tobject` scrutinee the scalar test is emitted before the tag join is opened (see
`emitInc`). -/
def lowerCases (c : LCtx) (x : Nat) (alts : List (LcPat × LM LExpr)) : LM LExpr := do
  let (xa, xt) ← c.var x
  let ctors := alts.filter fun | (.ctor .., _) => true | _ => false
  let dflts := alts.filter fun | (.dflt, _) => true | _ => false
  match ctors ++ dflts with
  | [] => pure .hlt
  | [(_, b)] => b
  | sorted =>
    if xt.isScalar then dispatchAlts xa xt.width sorted
    else if xt == .object then loadAt i8 xa 7 fun t => dispatchAlts t 8 sorted
    else if xt == .tagged then lshr64 xa (imm64 1) fun t => dispatchAlts t 64 sorted
    else isScalarObj xa fun s =>
      withJoin1 i64 (fun t => dispatchAlts t 64 sorted) fun j => do
        let ptr ← loadAt i8 xa 7 fun t8 => convW 8 64 t8 fun t => pure (j t)
        let sc ← lshr64 xa (imm64 1) fun t => pure (j t)
        pure (.jnz s sc ptr)

mutual
/-- Lower `Code .impure` (structural recursion on the code tree; a self tail call becomes a
`.jump` to the loop header, see `selfTailJump?`). -/
def lowerCode (env : LEnv) (c : LCtx) : LcCode → LM LExpr
  | .let_ x ty v k =>
    match selfTailJump? c (.let_ x ty v k) with
    | some jump => jump
    | none => lowerVal env c ty v fun r => lowerCode env (c.bind x r ty) k
  | .jp j ps body k => do
    let lbl ← fresh
    let pvs ← ps.mapM fun p => freshVar p.ty.toTTy
    let c' := { c with jps := (j, lbl, ps.map (·.ty)) :: c.jps }
    let b ← lowerCode env (c'.bindAll ps (pvs.map vArg)) body
    let kk ← lowerCode env c' k
    pure (.group [(lbl, pvs, b)] kk)
  | .jmp j as => do
    let some (lbl, ts) := c.jps.lookup j | lfail s!"LeanLCNF ({c.fn}): unbound join point {j}"
    if as.length != ts.length then lfail s!"LeanLCNF ({c.fn}): jmp arity"
    let args ← (as.zip ts).mapM fun (a, t) => argAt c a t
    pure (.jump lbl (ts.map LcTy.toTTy) args)
  | .cases x alts => lowerCases c x (lowerAlts env c alts)
  | .ret a => do pure (.ret [c.retTy.toTTy] [← argAt c a c.retTy])
  | .unreach => pure (.exit "lcnf_panic" [i64, i64] [c.rt, imm64 panicUnreachable])
  | .oset x i y k => do
    let (xa, _) ← c.var x
    storeAt i64 (← argAt c y .tobject) xa (8 + 8 * i) (lowerCode env c k)
  | .uset x i y k => do
    storeAt i64 (← c.var y).1 (← c.var x).1 (8 + 8 * i) (lowerCode env c k)
  | .sset x n off y ty k => do
    storeAt ty.toTTy (← argAt c (.var y) ty) (← c.var x).1 (8 + 8 * n + off) (lowerCode env c k)
  | .setTag x cidx k => do storeAt i8 (imm 8 cidx) (← c.var x).1 7 (lowerCode env c k)
  | .inc x n chk k => do
    let (xa, xt) ← c.var x
    emitInc xa xt n chk (lowerCode env c k)
  | .dec x n chk k => do
    let (xa, xt) ← c.var x
    emitDec c.rt xa xt n chk (lowerCode env c k)
  | .del x k => do call0 "lcnf_free_obj" [i64, i64] [c.rt, (← c.var x).1] (lowerCode env c k)

/-- The (unrun) builder action of every `cases` alternative. -/
def lowerAlts (env : LEnv) (c : LCtx) : List (LcPat × LcCode) → List (LcPat × LM LExpr)
  | [] => []
  | (p, b) :: rest => (p, lowerCode env c b) :: lowerAlts env c rest
end

/-! ## Declarations -/

/-- Scope-check a generated body into a `Frontend.C0.TFlatFn`. -/
def finishFn (name : Sym) (ps : List LVar) (ret : Ty) (body : LExpr) :
    Except String Frontend.C0.TFlatFn := do
  let tf ← lExprToTFlat (({} : LFlatCtx).pushVars ps) [ret] body
  let as := ps.map (·.ty)
  if tf.wfCheck (pushTypes as []) [] then pure { name, as, rs := [ret], flat := tf }
  else throw s!"LeanLCNF: TFlat.wfCheck failed on {name}"

/-- Generate `rt`, register parameters and the `extra_args` prologue for parameter types `tys`. -/
def withParams (tys : List Ty) (k : LArg → List LArg → LM LExpr) : LM (List LVar × LExpr) := do
  let rtV ← freshVar i64
  let regVs ← (tys.take regArgs).mapM freshVar
  let body ← loadExtras (vArg rtV) 0 (tys.drop regArgs) fun extras =>
    k (vArg rtV) (regVs.map vArg ++ extras)
  pure (rtV :: regVs, body)

/-- Lower one declaration. -/
def lowerDecl (env : LEnv) (d : LcDecl) : Except String Frontend.C0.TFlatFn := do
  let tys := d.params.map (·.ty.toTTy)
  let act := withParams tys fun rt pargs => do
    let c0 : LCtx := { fn := d.name, rt, retTy := d.retTy, params := d.params.map (·.ty) }
    if hasSelfTail d.name d.params.length d.body then
      let lbl ← fresh
      let lvs ← tys.mapM freshVar
      let b ← lowerCode env ({ c0 with loop? := some lbl }.bindAll d.params (lvs.map vArg)) d.body
      pure (.group [(lbl, lvs, b)] (.jump lbl tys pargs))
    else lowerCode env (c0.bindAll d.params pargs) d.body
  let ((ps, body), _) ← act.run 1
  finishFn (mangleLc d.name) ps d.retTy.toTTy body

/-! ## Defunctionalized closure application -/

/-- A closure-table entry: `(fun_id, symbol, arity)`. -/
abbrev CloTarget := Nat × Sym × Nat

/-- `lcnf_apply_k`. -/
def genApply (k : Nat) (targets : List CloTarget) :
    Except String Frontend.C0.TFlatFn := do
  let panic (rt : LArg) : LExpr := .exit "lcnf_panic" [i64, i64] [rt, imm64 panicBadClosure]
  let act := withParams (List.replicate (k + 1) i64) fun rt pargs => do
    let f := pargs.headD (imm64 1)
    let as := pargs.drop 1
    let leaf (t : CloTarget) : LM LExpr := do
      let (_, sym, arity) := t
      let nfix := arity - k
      let rec caps : Nat → (List LArg → LM LExpr) → LM LExpr
        | 0, kk => kk []
        | i + 1, kk => caps i fun cs => loadAt i64 f (24 + 8 * i) fun v => kk (cs ++ [v])
      let incAll (cs : List LArg) (kk : LM LExpr) : LM LExpr :=
        cs.foldr (fun c acc => emitInc c .tobject 1 true acc) kk
      -- Release the consumed closure inline (`lean_apply`): an exclusive closure gives its
      -- captured objects away (cell freed); a shared one keeps them (inc each, `m_rc -= 1`);
      -- a persistent one (`m_rc = 0`) is left alone.
      caps nfix fun cs =>
      loadAt i32 f 0 fun rc =>
      cmpOp .eq 32 rc (imm 32 1) fun is1 =>
      withJoin [] (fun _ =>
        callFn rt sym ((cs ++ as).map (·, i64)) i64 fun r => pure (.ret [i64] [r])) fun j => do
        let excl ← call0 "lcnf_free_obj" [i64, i64] [rt, f] (pure (j []))
        let shared ← cmpOp .sgt 32 rc (imm 32 1) fun gt => do
          let dec ← incAll cs <| op1 i32 (.sub i32) [rc, imm 32 1] fun rc' =>
            storeAt i32 rc' f 0 (pure (j []))
          pure (.jnz gt dec (j []))
        pure (.jnz is1 excl shared)
    let rec tree (fid : LArg) : Nat → List CloTarget → LM LExpr
      | _, [] => pure (panic rt)
      | _, [t] => cmpOp .eq 64 fid (imm64 t.1) fun e => do pure (.jnz e (← leaf t) (panic rt))
      | 0, _ => pure (panic rt)
      | fuel + 1, ts =>
        let l := ts.take (ts.length / 2)
        let r := ts.drop (ts.length / 2)
        cmpOp .ult 64 fid (imm64 ((r.headD (0, "", 0)).1)) fun lt => do
          pure (.jnz lt (← tree fid fuel l) (← tree fid fuel r))
    let exactTs := targets.filter fun t => t.2.2 ≥ k
    let rec over (rem : LArg) : Nat → LM LExpr
      | 0 => pure (panic rt)
      | n + 1 =>
        let r := k - (n + 1)
        if r == 0 then pure (panic rt)
        else cmpOp .eq 32 rem (imm 32 r) fun e => do
          let hit ← callFn rt (applySym r) ((f :: as.take r).map (·, i64)) i64 fun t =>
            callFn rt (applySym (k - r)) ((t :: as.drop r).map (·, i64)) i64 fun res =>
              pure (.ret [i64] [res])
          pure (.jnz e hit (← over rem n))
    loadAt i32 f 16 fun hw =>
    op1 i32 (.and i32) [hw, imm 32 0xffff] fun arity =>
    op1 i32 (.lshr i32) [hw, imm 32 16] fun nfix =>
    op1 i32 (.sub i32) [arity, nfix] fun rem =>
    cmpOp .eq 32 rem (imm 32 k) fun isEq =>
    cmpOp .ugt 32 rem (imm 32 k) fun isUnder => do
      let exact ← loadAt i64 f 8 fun fid => tree fid (exactTs.length + 1) exactTs
      let under ← call1 "lcnf_clo_under" [i64, i64, i64] i64 [rt, f, imm64 k] fun c2 =>
        convW 32 64 nfix fun n64 => shl64 n64 (imm64 3) fun off => add64 c2 off fun base =>
        storeFields base 24 as (pure (.ret [i64] [c2]))
      let ov ← over rem (k - 1)
      pure (.jnz isEq exact (.jnz isUnder under ov))
  let ((ps, body), _) ← act.run 1
  finishFn (applySym k) ps i64 body

/-! ## Modules -/

/-- Kernel-reducible `Nodup` on symbols. -/
def symsNodup : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && symsNodup xs

/-- The closure table of a module. -/
def LcModule.cloTargets (m : LcModule) : Except String (List CloTarget) :=
  (m.papTargets.zip (List.range m.papTargets.length)).mapM fun (f, i) =>
    match m.decls.find? (·.name == f) with
    | some d =>
      if d.retTy.width == 64 && d.params.all (·.ty.width == 64) then
        pure (i, mangleLc f, d.params.length)
      else throw s!"LeanLCNF: closure target {f} is not boxed"
    | none => throw s!"LeanLCNF: closure target {f} has no code"

mutual
/-- Collect `(string literals, big Nat literals ≥ 2^63)` in a code tree. -/
def LcCode.lits : LcCode → List String × List Nat
  | .let_ _ _ v k =>
    let (ss, ns) := k.lits
    match v with
    | .lit (.str s) => (s :: ss, ns)
    | .lit (.nat n) => if n < 2 ^ 63 then (ss, ns) else (ss, n :: ns)
    | _ => (ss, ns)
  | .jp _ _ b k =>
    let (s1, n1) := b.lits
    let (s2, n2) := k.lits
    (s1 ++ s2, n1 ++ n2)
  | .cases _ alts => LcCode.altsLits alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => k.lits
  | .jmp _ _ | .ret _ | .unreach => ([], [])

/-- `LcCode.lits` over `cases` alternatives. -/
def LcCode.altsLits : List (LcPat × LcCode) → List String × List Nat
  | [] => ([], [])
  | (_, b) :: rest =>
    let (s1, n1) := b.lits
    let (s2, n2) := LcCode.altsLits rest
    (s1 ++ s2, n1 ++ n2)
end

/-- Deduplicate `Nat` preserving first occurrences. -/
def dedupNat (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Lower a whole impure LCNF module (functions + `lcnf_apply_1..k`). -/
def lowerModule (m : LcModule) : Except String (List Frontend.C0.TFlatFn) := do
  let targets ← m.cloTargets
  let consts := m.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := m.decls.map (·.body.lits)
  let strs := dedupStr (allLits.flatMap (·.1))
  let bigNats := dedupNat (allLits.flatMap (·.2))
  let totalGlobals := consts.length + strs.length + bigNats.length
  if totalGlobals > rtGlobalSlots then throw "LeanLCNF: too many closed constants/literals"
  let strBase := consts.length
  let natBase := strBase + strs.length
  let env : LEnv :=
    { decls := m.decls.foldl (fun s d => (d.name, d) :: s) []
      funIds := m.papTargets.zip (List.range m.papTargets.length) |>.foldl
        (fun s (f, i) => (f, i) :: s) []
      globals := consts.zip (List.range consts.length) |>.foldl
        (fun s (d, i) => (d.name, i) :: s) []
      strLits := strs.zip (List.range strs.length) |>.foldl
        (fun s (x, i) => (x, strBase + i) :: s) []
      bigNatLits := bigNats.zip (List.range bigNats.length) |>.foldl
        (fun s (x, i) => (x, natBase + i) :: s) [] }
  let fns ← m.decls.mapM (lowerDecl env)
  let maxK := if targets.isEmpty then m.maxAp else Nat.max 1 m.maxAp
  let applies ← (List.range maxK).mapM fun i => genApply (i + 1) targets
  let all := fns ++ applies
  if !symsNodup (all.map (·.name)) then throw "LeanLCNF: mangled symbol collision"
  pure all

/-- Runtime externs as `LeanQbe.T.Extern`s. -/
def rtExterns : List Extern := rtCalls.map fun (n, as, bs) => { name := n, as, rs := bs }

/-- The `LeanQbe.T.Module` of a lowered program (runtime calls are externs); every function is
`Func.Wf` by `LeanLRC.tflatFnsToFns_wf`. -/
def lcnfTModule (tfs : List Frontend.C0.TFlatFn) : Module :=
  { fns := LeanLRC.tflatFnsToFns tfs, externs := rtExterns, exits := rtExitSyms }

end LeanQbe.T.LeanLCNF
