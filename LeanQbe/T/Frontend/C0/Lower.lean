module

public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.IL
public import LeanQbe.T.Module
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Shape-Stable PHOAS-First Lowering (`X0-core`)

Lowers `C0.TranslationUnit` into explicit typed SSA/join-point representation (`LFn` / `LExpr`)
together with `#c0_shape` metadata (`FnShape` / `GroupShape`), enforcing the fixed lowering scheme
(`kissat_c_frontend_design.md` §6.5):
1. Locals live purely in a compile-time map (zero `alloca`, zero `&local`; `&ptr->f` is pure
   pointer arithmetic `ptr + off`).
2. `if` with live-out mutated locals `M` (in deterministic declaration order) → 1-block join `group`.
3. `while` / `for` / `do-while` → `loop1` (or `brk` + `lp` nested `group` if `break` occurs)
   carrying mutated live-head locals `L` in declaration order.
4. Forward `goto L` → enclosing 1-block `group` carrying live locals mutated before `L`.
5. Short-circuit `&&`, `||`, `!` ALWAYS lower to `jnz` branches, NEVER `select`.
6. `static inline` functions inline at call sites (supporting multi-return & early `return`).
7. Memory `bool`s are stored as `i8` (`0`/`1`) and compared `!= 0` on load.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open LeanQbe.T

/-! ## Lowered IR (`LExpr` / `LFn`) & `#c0_shape` Metadata -/

structure LVar : Type where
  id : Nat
  name : String
  ty : Ty
  deriving Repr, BEq, Inhabited

inductive LArg : Type
  | var (id : Nat) (ty : Ty)
  | imm (t : Ty) (v : Val t)
  deriving Repr, Inhabited

def LArg.ty : LArg → Ty
  | .var _ t => t
  | .imm t _ => t

structure LOp : Type where
  rs : List Ty
  sig : List Ty
  code : OpCode sig rs
  args : List LArg

inductive LExpr : Type
  | let_ (op : LOp) (binders : List LVar) (k : LExpr)
  | load (t : Ty) (addr : LArg) (binder : LVar) (k : LExpr)
  | store (t : Ty) (val addr : LArg) (k : LExpr)
  | call (f : Sym) (as bs : List Ty) (args : List LArg) (binders : List LVar) (k : LExpr)
  | jnz (c : LArg) (t e : LExpr)
  | jump (lblId : Nat) (ts : List Ty) (args : List LArg)
  | ret (rs : List Ty) (args : List LArg)
  | exit (f : Sym) (as : List Ty) (args : List LArg)
  | hlt
  | group (blocks : List (Nat × List LVar × LExpr)) (k : LExpr)

structure GroupShape : Type where
  kind : String
  label : String
  params : List (String × Ty)
  deriving Repr, BEq, Inhabited

structure FnShape : Type where
  name : String
  params : List (String × Ty)
  rets : List Ty
  groups : List GroupShape
  deriving Repr, BEq, Inhabited

def FnShape.format (s : FnShape) : String :=
  let ps := String.intercalate ", " (s.params.map fun (nm, t) => s!"{nm} : {repr t}")
  let rs := String.intercalate ", " (s.rets.map fun t => s!"{repr t}")
  let gs := s.groups.map fun g =>
    let gps := String.intercalate ", " (g.params.map fun (nm, t) => s!"{nm} : {repr t}")
    s!"  {g.kind} @{g.label} ({gps})"
  s!"fn {s.name}({ps}) -> [{rs}]" ++ (if gs.isEmpty then "" else "\n" ++ String.intercalate "\n" gs)

structure LFn : Type where
  name : Sym
  params : List LVar
  rs : List Ty
  body : LExpr
  shape : FnShape

structure LModule : Type where
  fns : List LFn
  externs : List Extern
  exits : List Sym

/-! ## Lowering Monad & Environment -/

private inductive VarVal : Type
  | scalar (c0ty : C0Type) (arg : LArg)
  | tup (elems : List (C0Type × LArg))
  deriving Repr

private structure EnvEntry : Type where
  declId : Nat
  name : String
  val : VarVal
  deriving Repr

private abbrev LocalEnv := List EnvEntry

private structure JumpTarget : Type where
  lblId : Nat
  vars : List (Nat × String × C0Type × Ty)

private structure LowerCtx : Type where
  layout : LayoutEnv
  fns : Std.HashMap String FnDef
  externs : Std.HashMap String FnSig
  enums : Std.HashMap String Int := {}
  inlineStack : List String := []
  assertAsCheck : Bool := false
  breakTarget : Option JumpTarget := none
  contTarget : Option JumpTarget := none
  contInlineStep : Option Stmt := none
  gotoTargets : Std.HashMap String JumpTarget := {}
  retCont : Option (List (C0Type × LArg) → Except String LExpr) := none
  retTy : C0Type := .void

private structure LowerState : Type where
  nextVar : Nat := 0
  nextLbl : Nat := 0
  nextDecl : Nat := 0
  groups : List GroupShape := []

private abbrev LowerM := StateT LowerState (Except String)

private def freshDeclId : LowerM Nat := do
  let st ← get
  set { st with nextDecl := st.nextDecl + 1 }
  pure st.nextDecl

private def freshLVar (name : String) (t : Ty) : LowerM LVar := do
  let st ← get
  set { st with nextVar := st.nextVar + 1 }
  pure { id := st.nextVar, name, ty := t }

private def freshLblId : LowerM Nat := do
  let st ← get
  set { st with nextLbl := st.nextLbl + 1 }
  pure st.nextLbl

private def recordGroup (kind label : String) (ps : List LVar) : LowerM Unit :=
  modify fun st =>
    { st with groups := st.groups ++ [{ kind, label, params := ps.map fun v => (v.name, v.ty) }] }

private def lookupEnv? (env : LocalEnv) (nm : String) : Option EnvEntry :=
  env.reverse.find? fun e => e.name == nm

private def lookupEnvById? (env : LocalEnv) (id : Nat) : Option EnvEntry :=
  env.find? fun e => e.declId == id

private def updateEnvById (env : LocalEnv) (id : Nat) (v : VarVal) : LocalEnv :=
  env.map fun e => if e.declId == id then { e with val := v } else e

private def updateEnv (env : LocalEnv) (nm : String) (v : VarVal) : LocalEnv :=
  match lookupEnv? env nm with
  | some e => updateEnvById env e.declId v
  | none => env

private def snapshotArgs (env : LocalEnv) (vars : List (Nat × String × C0Type × Ty)) :
    Except String (List LArg) :=
  vars.mapM fun (id, nm, _, t) =>
    match lookupEnvById? env id with
    | some { val := .scalar _ a, .. } =>
      if a.ty == t then pure a else throw s!"internal type mismatch on join var '{nm}'"
    | _ => throw s!"local '{nm}' not in scope at jump"

private def allocJoinVars (vars : List (Nat × String × C0Type × Ty)) : LowerM (List LVar) :=
  vars.mapM fun (_, nm, _, t) => freshLVar nm t

private def rebindJoinVars (env : LocalEnv) (vars : List (Nat × String × C0Type × Ty))
    (lvs : List LVar) : LocalEnv :=
  (vars.zip lvs).foldl (fun e ((id, _, c0t, _), lv) =>
    updateEnvById e id (.scalar c0t (.var lv.id lv.ty))) env

private def selectJoinVars (env : LocalEnv) (mutated : Std.HashSet String) :
    Except String (List (Nat × String × C0Type × Ty)) := do
  let mut res : List (Nat × String × C0Type × Ty) := []
  for e in env do
    if mutated.contains e.name then
      if (lookupEnv? env e.name).map (·.declId) == some e.declId then
        match e.val with
        | .scalar c0ty a => res := res ++ [(e.declId, e.name, c0ty, a.ty)]
        | .tup _ => throw s!"tuple variable '{e.name}' cannot be carried across join/loop"
  pure res

/-! ## C0 Type System, Promotions, and Conversions -/

private def isSignedInt : C0Type → Bool
  | .int s _ => s
  | _ => false

private def intBitWidth : C0Type → Nat
  | .bool => 1
  | .int _ n => n
  | _ => 0

private def lowerScalarTy (env : LayoutEnv) (ty : C0Type) : Except String Ty := do
  match ← resolveType env ty with
  | .bool => pure .bool
  | .int _ n => pure (.bits n)
  | .f64 => pure f64
  | .ptr _ => pure i64
  | .structRef _ | .unionRef _ | .anonAggregate _ _ =>
    let lay ← getAggregateLayout env ty
    if lay.size == 1 || lay.size == 2 || lay.size == 4 || lay.size == 8 then
      pure (.bits (8 * lay.size))
    else throw s!"aggregate of size {lay.size} cannot be passed by value in C0"
  | t => throw s!"type {repr t} has no scalar T lowering"

private def lowerRetTys (env : LayoutEnv) (ty : C0Type) : Except String (List Ty) := do
  match ← resolveType env ty with
  | .void => pure []
  | .tuple ts => ts.mapM (lowerScalarTy env)
  | t => pure [← lowerScalarTy env t]

private def emitOp (rs sig : List Ty) (code : OpCode sig rs) (args : List LArg) (nm : String)
    (k : List LArg → LowerM LExpr) : LowerM LExpr := do
  let binders ← rs.mapM (freshLVar nm)
  let body ← k (binders.map fun v => LArg.var v.id v.ty)
  pure (.let_ ⟨rs, sig, code, args⟩ binders body)

private def emitOp1 (r : Ty) (sig : List Ty) (code : OpCode sig [r]) (args : List LArg)
    (nm : String := "t") (k : LArg → LowerM LExpr) : LowerM LExpr :=
  emitOp [r] sig code args nm fun | [o] => k o | _ => pure .hlt

private def emitLoad (t : Ty) (addr : LArg) (nm : String := "ld")
    (k : LArg → LowerM LExpr) : LowerM LExpr := do
  let b ← freshLVar nm t
  let rest ← k (.var b.id t)
  pure (.load t addr b rest)

private def emitStore (t : Ty) (val addr : LArg) (k : LowerM LExpr) : LowerM LExpr := do
  let rest ← k
  pure (.store t val addr rest)

private def emitF64ToU64Sat (d : LArg) (k : LArg → LowerM LExpr) : LowerM LExpr := do
  let joinLbl ← freshLblId
  let resVar ← freshLVar "sat" i64
  recordGroup "sat_join" s!"sat_{joinLbl}" [resVar]
  let joinBody ← k (.var resVar.id i64)
  emitOp1 .bool [f64, f64] (.fcmp .ge f64) [d, .imm f64 0#64] "ge0" fun c0 => do
    let two64Bits : BitVec 64 := BitVec.ofNat 64 0x43f0000000000000
    let maxU64 : BitVec 64 := BitVec.allOnes 64
    let inRangeBody ← emitOp1 .bool [f64, f64] (.fcmp .lt f64) [d, .imm f64 two64Bits] "lt2p64" fun c1 => do
      let convBody ← emitOp1 i64 [f64] (.fptoui .d 64) [d] "f2u" fun u =>
        pure (.jump joinLbl [i64] [u])
      pure (.jnz c1 convBody (.jump joinLbl [i64] [.imm i64 maxU64]))
    pure (.group [(joinLbl, [resVar], joinBody)] (.jnz c0 inRangeBody (.jump joinLbl [i64] [.imm i64 0#64])))

private def convertVal (env : LayoutEnv) (srcTy dstTy : C0Type) (a : LArg)
    (k : LArg → LowerM LExpr) : LowerM LExpr := do
  let src ← MonadExcept.ofExcept (resolveType env srcTy)
  let dst ← MonadExcept.ofExcept (resolveType env dstTy)
  if src == dst then return ← k a
  match src, dst with
  | .ptr _, .ptr _ | .ptr _, .int _ 64 | .int _ 64, .ptr _ => k a
  | .ptr _, .bool => emitOp1 .bool [i64, i64] (.cmp .ne i64) [a, .imm i64 0#64] "ptr_b" k
  | .ptr _, .int _ n =>
    if n < 64 then emitOp1 (.bits n) [i64] (.trunc 64 n) [a] "ptr_tr" k else k a
  | .int s m, .ptr _ =>
    if m == 64 then k a
    else if s then emitOp1 i64 [.bits m] (.sext m 64) [a] "sx_p" k
    else emitOp1 i64 [.bits m] (.zext m 64) [a] "zx_p" k
  | .bool, .ptr _ => emitOp1 i64 [.bool] (.ofBool 64) [a] "b_p" k
  | .bool, .int _ n => emitOp1 (.bits n) [.bool] (.ofBool n) [a] "b_i" k
  | .int _ m, .bool => emitOp1 .bool [.bits m, .bits m] (.cmp .ne (.bits m)) [a, .imm (.bits m) (0#m)] "i_b" k
  | .f64, .bool => emitOp1 .bool [f64, f64] (.fcmp .ne f64) [a, .imm f64 0#64] "f_b" k
  | .bool, .f64 =>
    emitOp1 i32 [.bool] (.ofBool 32) [a] "b_i32" fun ai =>
      emitOp1 f64 [i32] (.uitofp 32 .d) [ai] "i_f" k
  | .int s m, .int _ n =>
    if m == n then k a
    else if m < n then
      if s then emitOp1 (.bits n) [.bits m] (.sext m n) [a] "sx" k
      else emitOp1 (.bits n) [.bits m] (.zext m n) [a] "zx" k
    else emitOp1 (.bits n) [.bits m] (.trunc m n) [a] "tr" k
  | .int s m, .f64 =>
    if s then emitOp1 f64 [.bits m] (.sitofp m .d) [a] "si2f" k
    else emitOp1 f64 [.bits m] (.uitofp m .d) [a] "ui2f" k
  | .f64, .int s n =>
    if !s && n == 64 then emitF64ToU64Sat a k
    else if s then emitOp1 (.bits n) [f64] (.fptosi .d n) [a] "f2si" k
    else emitOp1 (.bits n) [f64] (.fptoui .d n) [a] "f2ui" k
  | _, _ =>
    let ts ← MonadExcept.ofExcept (lowerScalarTy env src)
    let td ← MonadExcept.ofExcept (lowerScalarTy env dst)
    if ts == td then k a
    else throw s!"unsupported conversion from {repr src} to {repr dst}"

private def coerceIntLit (v : Int) (suf : IntSuffix) (isDec : Bool := true) : C0Type × LArg :=
  let ty := intLitType v suf isDec
  let w := intBitWidth ty
  (ty, .imm (.bits w) (BitVec.ofInt w v))

/-! ## Memory & Bitfield Read/Write Helpers -/

private def addOffset (base : LArg) (off : Nat) (k : LArg → LowerM LExpr) : LowerM LExpr := do
  if off == 0 then k base
  else emitOp1 i64 [i64, i64] (.add i64) [base, .imm i64 (BitVec.ofNat 64 off)] "off" k

private def loadMemScalar (env : LayoutEnv) (ty : C0Type) (addr : LArg)
    (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
  let rt ← MonadExcept.ofExcept (resolveType env ty)
  match rt with
  | .bool =>
    emitLoad i8 addr "ldb" fun b =>
      emitOp1 .bool [i8, i8] (.cmp .ne i8) [b, .imm i8 0#8] "b" (k .bool)
  | .array inner _ => k (.ptr inner) addr
  | _ =>
    let lt ← MonadExcept.ofExcept (lowerScalarTy env rt)
    emitLoad lt addr "ld" (k rt)

private def storeMemScalar (env : LayoutEnv) (dstTy srcTy : C0Type) (addr rhs : LArg)
    (k : LowerM LExpr) : LowerM LExpr := do
  let rd ← MonadExcept.ofExcept (resolveType env dstTy)
  convertVal env srcTy rd rhs fun cv =>
    match rd with
    | .bool => emitOp1 i8 [.bool] (.ofBool 8) [cv] "stb" fun b8 => emitStore i8 b8 addr k
    | _ => do
      let lt ← MonadExcept.ofExcept (lowerScalarTy env rd)
      emitStore lt cv addr k

private def extractBitsFromWord (env : LayoutEnv) (wordVal : LArg) (wordBits bitOff width : Nat)
    (declTy : C0Type) (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
  let unitTy := Ty.bits wordBits
  let afterShift := fun shifted => do
    let afterMask := fun masked => do
      let rdecl ← MonadExcept.ofExcept (resolveType env declTy)
      if rdecl == .bool then
        emitOp1 .bool [unitTy, unitTy] (.cmp .ne unitTy) [masked, .imm unitTy (0#wordBits)] "bfb" (k .bool)
      else
        let outTy ← MonadExcept.ofExcept (bitfieldValueType env rdecl width)
        if isSignedInt rdecl && width < wordBits then
          let sh := wordBits - width
          emitOp1 unitTy [unitTy, unitTy] (.shl unitTy) [masked, .imm unitTy (BitVec.ofNat wordBits sh)] "bfs1" fun s1 =>
            emitOp1 unitTy [unitTy, unitTy] (.ashr unitTy) [s1, .imm unitTy (BitVec.ofNat wordBits sh)] "bfs2" fun sx =>
              convertVal env (.int true wordBits) outTy sx (k outTy)
        else convertVal env (.int false wordBits) outTy masked (k outTy)
    if width == wordBits then afterMask shifted
    else
      let mask : BitVec wordBits := BitVec.ofNat wordBits ((1 <<< width) - 1)
      emitOp1 unitTy [unitTy, unitTy] (.and unitTy) [shifted, .imm unitTy mask] "bfm" afterMask
  if bitOff == 0 then afterShift wordVal
  else emitOp1 unitTy [unitTy, unitTy] (.lshr unitTy) [wordVal, .imm unitTy (BitVec.ofNat wordBits bitOff)] "bfs" afterShift

private def inferTy (ctx : LowerCtx) (env : LocalEnv) (e : Expr)
    (decayArray : Bool := true) (forSizeof : Bool := false) : Except String C0Type :=
  let lookupVar (nm : String) : Except String C0Type :=
    match lookupEnv? env nm with
    | some { val := .scalar t _, .. } => pure t
    | some { val := .tup _, .. } => throw s!"tuple variable '{nm}' cannot be used as scalar"
    | none =>
      match ctx.enums.get? nm with
      | some v => pure (intLitType v .none true)
      | none => throw s!"unbound local '{nm}'"
  let lookupFnRet (fn : String) : Except String C0Type :=
    if let some fd := ctx.fns.get? fn then pure fd.retTy
    else if let some sg := ctx.externs.get? fn then pure sg.retTy
    else throw s!"unknown function '{fn}'"
  inferExprType ctx.layout lookupVar lookupFnRet e decayArray forSizeof

private def loadFieldFromAddr (env : LayoutEnv) (baseAddr : LArg) (byteOff : Nat)
    (loc : FieldLoc) (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
  match loc with
  | .regular fOff fty _ =>
    addOffset baseAddr (byteOff + fOff) fun addr => loadMemScalar env fty addr k
  | .bitfield unitOff unitBytes localBitOff width declTy =>
    let unitBits := unitBytes * 8
    addOffset baseAddr (byteOff + unitOff) fun addr =>
      emitLoad (.bits unitBits) addr "ldbf" fun raw =>
        extractBitsFromWord env raw unitBits localBitOff width declTy k

private def storeFieldToAddr (env : LayoutEnv) (baseAddr : LArg) (byteOff : Nat)
    (loc : FieldLoc) (rhsTy : C0Type) (rhs : LArg) (k : LowerM LExpr) : LowerM LExpr := do
  match loc with
  | .regular fOff fty _ =>
    addOffset baseAddr (byteOff + fOff) fun addr => storeMemScalar env fty rhsTy addr rhs k
  | .bitfield unitOff unitBytes localBitOff width declTy =>
    let unitBits := unitBytes * 8
    let unitTy := Ty.bits unitBits
    let rdecl ← MonadExcept.ofExcept (resolveType env declTy)
    convertVal env rhsTy rdecl rhs fun cv =>
      convertVal env rdecl (.int false unitBits) cv fun uval => do
        let valMask : BitVec unitBits := BitVec.ofNat unitBits ((1 <<< width) - 1)
        let maskedStep := fun mv => do
          let shiftedStep := fun sv => do
            addOffset baseAddr (byteOff + unitOff) fun addr =>
              if width == unitBits && localBitOff == 0 then emitStore unitTy sv addr k
              else emitLoad unitTy addr "ldold" fun old => do
                let clearMask : BitVec unitBits := ~~~(BitVec.ofNat unitBits (((1 <<< width) - 1) <<< localBitOff))
                emitOp1 unitTy [unitTy, unitTy] (.and unitTy) [old, .imm unitTy clearMask] "clr" fun cleared =>
                  emitOp1 unitTy [unitTy, unitTy] (.or unitTy) [cleared, sv] "upd" fun updated =>
                    emitStore unitTy updated addr k
          if localBitOff == 0 then shiftedStep mv
          else emitOp1 unitTy [unitTy, unitTy] (.shl unitTy) [mv, .imm unitTy (BitVec.ofNat unitBits localBitOff)] "bfshl" shiftedStep
        if width == unitBits then maskedStep uval
        else emitOp1 unitTy [unitTy, unitTy] (.and unitTy) [uval, .imm unitTy valMask] "bfvm" maskedStep

private def resolveFieldChain (env : LayoutEnv) (ty : C0Type) :
    List String → Except String (Nat × FieldLoc)
  | [] => throw "empty field chain"
  | [fld] => do pure (0, ← lookupField env ty fld)
  | fld :: rest => do
    match ← lookupField env ty fld with
    | .regular off subTy _ =>
      let (off', loc) ← resolveFieldChain env subTy rest
      pure (off + off', loc)
    | .bitfield _ _ _ _ _ => throw s!"cannot access field inside bitfield '{fld}'"

private def collectFieldChain : Expr → List String → Expr × List String
  | .field base fld, acc => collectFieldChain base (fld :: acc)
  | root, acc => (root, acc)

private def cmpOpOf (op : BinOp) (signed : Bool) : Except String CmpOp :=
  match op with
  | .eq => pure .eq | .ne => pure .ne
  | .lt => pure (if signed then .slt else .ult)
  | .le => pure (if signed then .sle else .ule)
  | .gt => pure (if signed then .sgt else .ugt)
  | .ge => pure (if signed then .sge else .uge)
  | _ => throw s!"not a comparison op: {repr op}"

/-! ## Mutually Recursive Expression, Condition, Call, and Statement Lowering -/

mutual
  private partial def lowerIndexAddr (ctx : LowerCtx) (env : LocalEnv) (arrE idxE : Expr)
      (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
    lowerExpr ctx env arrE fun pty pa => do
      let elemTy ← match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr elem | .array elem _ => pure elem
        | t => throw s!"indexing requires pointer or array, got {repr t}"
      let (elemSz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout elemTy)
      lowerExpr ctx env idxE fun ity ia =>
        convertVal ctx.layout ity .i64 ia fun idx64 =>
          if elemSz == 1 then emitOp1 i64 [i64, i64] (.add i64) [pa, idx64] "elt" (k elemTy)
          else emitOp1 i64 [i64, i64] (.mul i64) [idx64, .imm i64 (BitVec.ofNat 64 elemSz)] "mul" fun off =>
            emitOp1 i64 [i64, i64] (.add i64) [pa, off] "elt" (k elemTy)

  private partial def lowerMemRoot (ctx : LowerCtx) (env : LocalEnv) (root : Expr)
      (chain : List String) (k : C0Type → LArg → Nat → FieldLoc → LowerM LExpr) : LowerM LExpr := do
    let finish (aggTy : C0Type) (addr : LArg) (baseOff : Nat) : LowerM LExpr := do
      let (off, loc) ← MonadExcept.ofExcept (resolveFieldChain ctx.layout aggTy chain)
      k aggTy addr (baseOff + off) loc
    match root with
    | .unary .deref ptrE =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr aggTy => finish aggTy pa 0
        | t => throw s!"'*' requires pointer, got {repr t}"
    | .arrow ptrE fld0 =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr aggTy =>
          let (off, loc) ← MonadExcept.ofExcept (resolveFieldChain ctx.layout aggTy (fld0 :: chain))
          k aggTy pa off loc
        | t => throw s!"'->' requires pointer, got {repr t}"
    | .index arrE idxE =>
      lowerIndexAddr ctx env arrE idxE fun elemTy pa => finish elemTy pa 0
    | _ => throw "field access base must be an aggregate pointer/index or register local"

  private partial def lowerAddrOfExpr (ctx : LowerCtx) (env : LocalEnv) (e : Expr)
      (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
    let finishRegular (pa : LArg) (off : Nat) (loc : FieldLoc) (fld : String) :=
      match loc with
      | .regular fOff fty _ =>
        let addrTy := match fty with | .array elem _ => C0Type.ptr elem | t => C0Type.ptr t
        addOffset pa (off + fOff) (k addrTy)
      | .bitfield _ _ _ _ _ => throw s!"cannot take address of bitfield '{fld}'"
    match e with
    | .arrow ptrE fld =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr aggTy =>
          let loc ← MonadExcept.ofExcept (lookupField ctx.layout aggTy fld)
          finishRegular pa 0 loc fld
        | t => throw s!"'->' requires pointer, got {repr t}"
    | .field base fld =>
      let (root, chain) := collectFieldChain base [fld]
      match root with
      | .var nm => throw s!"cannot take address of local variable '&{nm}' in C0"
      | _ => lowerMemRoot ctx env root chain fun _ pa off loc => finishRegular pa off loc fld
    | .index arrE idxE => lowerIndexAddr ctx env arrE idxE fun elemTy pa => k (.ptr elemTy) pa
    | .unary .deref ptrE => lowerExpr ctx env ptrE k
    | .var nm => throw s!"cannot take address of local variable '&{nm}' in C0"
    | _ => throw "address-of '&' is only supported on memory lvalues (e->f, p[i], *p)"

  private partial def lowerExpr (ctx : LowerCtx) (env : LocalEnv) (e : Expr)
      (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
    match e with
    | .intLit v suf isDec => let (ty, arg) := coerceIntLit v suf isDec; k ty arg
    | .floatLit bits => k .f64 (.imm f64 (BitVec.ofNat 64 bits.toNat))
    | .boolLit b => k .bool (.imm .bool b)
    | .null => k (.ptr .void) (.imm i64 0#64)
    | .var nm =>
      match lookupEnv? env nm with
      | some { val := .scalar ty a, .. } => k ty a
      | some { val := .tup _, .. } => throw s!"tuple variable '{nm}' cannot be used as a scalar"
      | none =>
        match ctx.enums.get? nm with
        | some v => let (ty, arg) := coerceIntLit v .none true; k ty arg
        | none => throw s!"unbound local variable '{nm}'"
    | .cast dstTy sub =>
      lowerExpr ctx env sub fun srcTy a =>
        convertVal ctx.layout srcTy dstTy a fun ca => do
          k (← MonadExcept.ofExcept (resolveType ctx.layout dstTy)) ca
    | .sizeofTy ty =>
      let (sz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout ty)
      k .u64 (.imm i64 (BitVec.ofNat 64 sz))
    | .sizeofExpr sub =>
      let ty ← MonadExcept.ofExcept (inferTy ctx env sub false true)
      let (sz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout ty)
      k .u64 (.imm i64 (BitVec.ofNat 64 sz))
    | .unary .pos sub =>
      lowerExpr ctx env sub fun ty a =>
        let pty := intPromote ty
        convertVal ctx.layout ty pty a (k pty)
    | .unary .neg sub =>
      lowerExpr ctx env sub fun ty a => do
        let rty ← MonadExcept.ofExcept (resolveType ctx.layout ty)
        if rty == .f64 then emitOp1 f64 [f64] (.fneg f64) [a] "fneg" (k .f64)
        else
          let pty := intPromote rty
          convertVal ctx.layout rty pty a fun pa => do
            let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout pty)
            emitOp1 lt [lt] (.neg lt) [pa] "neg" (k pty)
    | .unary .bitnot sub =>
      lowerExpr ctx env sub fun ty a =>
        let pty := intPromote ty
        convertVal ctx.layout ty pty a fun pa => do
          let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout pty)
          emitOp1 lt [lt] (.not lt) [pa] "bnot" (k pty)
    | .unary .lognot sub =>
      lowerExpr ctx env sub fun ty a =>
        convertVal ctx.layout ty .bool a fun ba =>
          emitOp1 .bool [.bool] (.not .bool) [ba] "lnot" (k .bool)
    | .unary .deref ptrE =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr elem => loadMemScalar ctx.layout elem pa k
        | t => throw s!"cannot dereference non-pointer type {repr t}"
    | .unary .addrOf sub => lowerAddrOfExpr ctx env sub k
    | .field base fld =>
      let (root, chain) := collectFieldChain base [fld]
      match root with
      | .var nm =>
        match lookupEnv? env nm with
        | some { val := .scalar aggTy regVal, .. } =>
          let (byteOff, loc) ← MonadExcept.ofExcept (resolveFieldChain ctx.layout aggTy chain)
          let (aggSz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout aggTy)
          match loc with
          | .regular fOff fty fsz =>
            let rf ← MonadExcept.ofExcept (resolveType ctx.layout fty)
            let bitOff := (byteOff + fOff) * 8
            if bitOff == 0 && fsz == aggSz then
              let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout rf)
              if lt == regVal.ty then k rf regVal
              else extractBitsFromWord ctx.layout regVal (aggSz * 8) 0 (fsz * 8) rf k
            else extractBitsFromWord ctx.layout regVal (aggSz * 8) bitOff (fsz * 8) rf k
          | .bitfield uOff _ lBit w dty =>
            extractBitsFromWord ctx.layout regVal (aggSz * 8) ((byteOff + uOff) * 8 + lBit) w dty k
        | _ => throw s!"cannot take field '{fld}' of non-aggregate local"
      | _ => lowerMemRoot ctx env root chain fun _ pa off loc =>
        loadFieldFromAddr ctx.layout pa off loc k
    | .arrow ptrE fld =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr aggTy =>
          let loc ← MonadExcept.ofExcept (lookupField ctx.layout aggTy fld)
          loadFieldFromAddr ctx.layout pa 0 loc k
        | t => throw s!"'->' requires pointer to struct/union, got {repr t}"
    | .index arrE idxE =>
      lowerIndexAddr ctx env arrE idxE fun elemTy pa =>
        loadMemScalar ctx.layout elemTy pa k
    | .binary .logand _ _ | .binary .logor _ _ =>
      let jLbl ← freshLblId
      let jVar ← freshLVar "cond_v" .bool
      recordGroup "cond_join" s!"cj_{jLbl}" [jVar]
      let joinBody ← k .bool (.var jVar.id .bool)
      let entry ← lowerCond ctx env e
        (pure (.jump jLbl [.bool] [.imm .bool true]))
        (pure (.jump jLbl [.bool] [.imm .bool false]))
      pure (.group [(jLbl, [jVar], joinBody)] entry)
    | .binary op lhs rhs => lowerBinOp ctx env op lhs rhs k
    | .ternary cond thn els =>
      let resTy ← MonadExcept.ofExcept (inferTy ctx env e)
      let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout resTy)
      let jLbl ← freshLblId
      let jVar ← freshLVar "tern" lt
      recordGroup "ternary_join" s!"tern_{jLbl}" [jVar]
      let joinBody ← k resTy (.var jVar.id lt)
      let thnCode ← lowerExpr ctx env thn fun t1 a1 =>
        convertVal ctx.layout t1 resTy a1 fun ca => pure (.jump jLbl [lt] [ca])
      let elsCode ← lowerExpr ctx env els fun t2 a2 =>
        convertVal ctx.layout t2 resTy a2 fun ca => pure (.jump jLbl [lt] [ca])
      let entry ← lowerCond ctx env cond (pure thnCode) (pure elsCode)
      pure (.group [(jLbl, [jVar], joinBody)] entry)
    | .call fn args =>
      lowerCallExpr ctx env fn args fun
        | [(ty, arg)] => k ty arg
        | _ => throw s!"call to '{fn}' in expression position must return 1 value"

  private partial def lowerBinOp (ctx : LowerCtx) (env : LocalEnv) (op : BinOp)
      (lhs rhs : Expr) (k : C0Type → LArg → LowerM LExpr) : LowerM LExpr := do
    lowerExpr ctx env lhs fun t1 a1 =>
      lowerExpr ctx env rhs fun t2 a2 => do
        let rt1 ← MonadExcept.ofExcept (resolveType ctx.layout t1)
        let rt2 ← MonadExcept.ofExcept (resolveType ctx.layout t2)
        let ptrArith (elem : C0Type) (ptrVal : LArg) (idxTy : C0Type) (idxVal : LArg)
            (isAdd : Bool) (outTy : C0Type) : LowerM LExpr := do
          let (sz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout elem)
          convertVal ctx.layout idxTy .i64 idxVal fun idx64 =>
            let go := fun off =>
              let code := if isAdd then OpCode.add i64 else OpCode.sub i64
              emitOp1 i64 [i64, i64] code [ptrVal, off] "pstep" (k outTy)
            if sz == 1 then go idx64
            else emitOp1 i64 [i64, i64] (.mul i64) [idx64, .imm i64 (BitVec.ofNat 64 sz)] "pmul" go
        match op, rt1, rt2 with
        | .add, .ptr elem, _ => ptrArith elem a1 rt2 a2 true rt1
        | .add, _, .ptr elem => ptrArith elem a2 rt1 a1 true rt2
        | .sub, .ptr elem, .ptr _ =>
          let (sz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout elem)
          if sz == 0 then throw "cannot subtract pointers to zero-sized type"
          emitOp1 i64 [i64, i64] (.sub i64) [a1, a2] "pdiff" fun diff =>
            if sz == 1 then k .i64 diff
            else emitOp1 i64 [i64, i64] (.sdiv 64) [diff, .imm i64 (BitVec.ofNat 64 sz)] "pdiv" (k .i64)
        | .sub, .ptr elem, _ => ptrArith elem a1 rt2 a2 false rt1
        | _, .ptr _, .ptr _ =>
          let cmpOp ← MonadExcept.ofExcept (cmpOpOf op false)
          emitOp1 .bool [i64, i64] (.cmp cmpOp i64) [a1, a2] "pcmp" (k .bool)
        | _, .ptr _, _ =>
          convertVal ctx.layout rt2 (.ptr .void) a2 fun a2p => do
            let cmpOp ← MonadExcept.ofExcept (cmpOpOf op false)
            emitOp1 .bool [i64, i64] (.cmp cmpOp i64) [a1, a2p] "pcmp" (k .bool)
        | _, _, .ptr _ =>
          convertVal ctx.layout rt1 (.ptr .void) a1 fun a1p => do
            let cmpOp ← MonadExcept.ofExcept (cmpOpOf op false)
            emitOp1 .bool [i64, i64] (.cmp cmpOp i64) [a1p, a2] "pcmp" (k .bool)
        | .shl, _, _ | .shr, _, _ =>
          let p1 := intPromote rt1; let p2 := intPromote rt2
          convertVal ctx.layout rt1 p1 a1 fun ca1 =>
            convertVal ctx.layout rt2 p2 a2 fun ca2 =>
              convertVal ctx.layout p2 p1 ca2 fun shiftAmt => do
                let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout p1)
                let code := if op == .shl then OpCode.shl lt
                            else if isSignedInt p1 then OpCode.ashr lt else OpCode.lshr lt
                emitOp1 lt [lt, lt] code [ca1, shiftAmt] "sh" (k p1)
        | _, _, _ =>
          let cty ← MonadExcept.ofExcept (usualArithType rt1 rt2)
          convertVal ctx.layout rt1 cty a1 fun ca1 =>
            convertVal ctx.layout rt2 cty a2 fun ca2 => do
              if cty == .f64 then
                match op with
                | .add => emitOp1 f64 [f64, f64] (.fadd f64) [ca1, ca2] "fadd" (k .f64)
                | .sub => emitOp1 f64 [f64, f64] (.fsub f64) [ca1, ca2] "fsub" (k .f64)
                | .mul => emitOp1 f64 [f64, f64] (.fmul f64) [ca1, ca2] "fmul" (k .f64)
                | .div => emitOp1 f64 [f64, f64] (.fdiv f64) [ca1, ca2] "fdiv" (k .f64)
                | .eq => emitOp1 .bool [f64, f64] (.fcmp .eq f64) [ca1, ca2] "feq" (k .bool)
                | .ne => emitOp1 .bool [f64, f64] (.fcmp .ne f64) [ca1, ca2] "fne" (k .bool)
                | .lt => emitOp1 .bool [f64, f64] (.fcmp .lt f64) [ca1, ca2] "flt" (k .bool)
                | .le => emitOp1 .bool [f64, f64] (.fcmp .le f64) [ca1, ca2] "fle" (k .bool)
                | .gt => emitOp1 .bool [f64, f64] (.fcmp .gt f64) [ca1, ca2] "fgt" (k .bool)
                | .ge => emitOp1 .bool [f64, f64] (.fcmp .ge f64) [ca1, ca2] "fge" (k .bool)
                | _ => throw s!"invalid operator {repr op} on f64"
              else
                let signed := isSignedInt cty
                let n := intBitWidth cty
                let lt := Ty.bits n
                match op with
                | .add => emitOp1 lt [lt, lt] (.add lt) [ca1, ca2] "add" (k cty)
                | .sub => emitOp1 lt [lt, lt] (.sub lt) [ca1, ca2] "sub" (k cty)
                | .mul => emitOp1 lt [lt, lt] (.mul lt) [ca1, ca2] "mul" (k cty)
                | .bitand => emitOp1 lt [lt, lt] (.and lt) [ca1, ca2] "and" (k cty)
                | .bitor => emitOp1 lt [lt, lt] (.or lt) [ca1, ca2] "or" (k cty)
                | .bitxor => emitOp1 lt [lt, lt] (.xor lt) [ca1, ca2] "xor" (k cty)
                | .div => emitOp1 lt [lt, lt] (if signed then .sdiv n else .udiv n) [ca1, ca2] "div" (k cty)
                | .mod => emitOp1 lt [lt, lt] (if signed then .srem n else .urem n) [ca1, ca2] "rem" (k cty)
                | _ =>
                  let cmpOp ← MonadExcept.ofExcept (cmpOpOf op signed)
                  emitOp1 .bool [lt, lt] (.cmp cmpOp lt) [ca1, ca2] "cmp" (k .bool)

  private partial def lowerCond (ctx : LowerCtx) (env : LocalEnv) (c : Expr)
      (onTrue onFalse : LowerM LExpr) : LowerM LExpr := do
    match c with
    | .unary .lognot sub => lowerCond ctx env sub onFalse onTrue
    | .binary .logand lhs rhs =>
      let fCode ← onFalse
      match fCode with
      | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .hlt =>
        lowerCond ctx env lhs (lowerCond ctx env rhs onTrue (pure fCode)) (pure fCode)
      | _ =>
        let jLbl ← freshLblId
        recordGroup "sc_false" s!"scf_{jLbl}" []
        let right ← lowerCond ctx env rhs onTrue (pure (.jump jLbl [] []))
        let entry ← lowerCond ctx env lhs (pure right) (pure (.jump jLbl [] []))
        pure (.group [(jLbl, [], fCode)] entry)
    | .binary .logor lhs rhs =>
      let tCode ← onTrue
      match tCode with
      | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .hlt =>
        lowerCond ctx env lhs (pure tCode) (lowerCond ctx env rhs (pure tCode) onFalse)
      | _ =>
        let jLbl ← freshLblId
        recordGroup "sc_true" s!"sct_{jLbl}" []
        let right ← lowerCond ctx env rhs (pure (.jump jLbl [] [])) onFalse
        let entry ← lowerCond ctx env lhs (pure (.jump jLbl [] [])) (pure right)
        pure (.group [(jLbl, [], tCode)] entry)
    | _ =>
      lowerExpr ctx env c fun ty a =>
        convertVal ctx.layout ty .bool a fun ba => do
          pure (.jnz ba (← onTrue) (← onFalse))

  private partial def lowerCallArgs (ctx : LowerCtx) (env : LocalEnv)
      (paramTys : List C0Type) (args : List Expr)
      (k : List (C0Type × LArg) → LowerM LExpr) : LowerM LExpr := do
    unless paramTys.length == args.length do
      throw s!"call argument count mismatch: expected {paramTys.length}, got {args.length}"
    let rec go (pts : List C0Type) (es : List Expr) (acc : List (C0Type × LArg)) : LowerM LExpr := do
      match pts, es with
      | [], [] => k acc
      | pt :: pts', e :: es' =>
        lowerExpr ctx env e fun et a =>
          convertVal ctx.layout et pt a fun ca => do
            let rpt ← MonadExcept.ofExcept (resolveType ctx.layout pt)
            go pts' es' (acc ++ [(rpt, ca)])
      | _, _ => throw "arity mismatch"
    go paramTys args []

  private partial def lowerCallExpr (ctx : LowerCtx) (env : LocalEnv)
      (fn : String) (args : List Expr)
      (k : List (C0Type × LArg) → LowerM LExpr) : LowerM LExpr := do
    let unaryBit (w : Nat) (mkOp : OpCode [.bits w] [.bits w]) (nm : String) (x : Expr) :=
      let cty := C0Type.int false w
      let ty := Ty.bits w
      lowerCallArgs ctx env [cty] [x] fun
        | [(_, vx)] => emitOp1 ty [ty] mkOp [vx] nm fun r => k [(cty, r)]
        | _ => pure .hlt
    let binBit (w : Nat) (mkOp : OpCode [.bits w, .bits w] [.bits w]) (nm : String) (x y : Expr) :=
      let cty := C0Type.int false w
      let ty := Ty.bits w
      lowerCallArgs ctx env [cty, cty] [x, y] fun
        | [(_, vx), (_, vy)] => emitOp1 ty [ty, ty] mkOp [vx, vy] nm fun r => k [(cty, r)]
        | _ => pure .hlt
    match fn, args with
    | "c0_rotl32", [x, s] => binBit 32 (.rotl i32) "rotl" x s
    | "c0_rotr32", [x, s] => binBit 32 (.rotr i32) "rotr" x s
    | "c0_rotl64", [x, s] => binBit 64 (.rotl i64) "rotl" x s
    | "c0_rotr64", [x, s] => binBit 64 (.rotr i64) "rotr" x s
    | "c0_clz32", [x] => unaryBit 32 (.clz 32) "clz" x
    | "c0_clz64", [x] => unaryBit 64 (.clz 64) "clz" x
    | "c0_ctz32", [x] => unaryBit 32 (.ctz 32) "ctz" x
    | "c0_ctz64", [x] => unaryBit 64 (.ctz 64) "ctz" x
    | "c0_popcnt32", [x] => unaryBit 32 (.popcnt 32) "pop" x
    | "c0_popcnt64", [x] => unaryBit 64 (.popcnt 64) "pop" x
    | "c0_addc64", [a, b, cin] =>
      lowerCallArgs ctx env [.u64, .u64, .bool] [a, b, cin] fun
        | [(_, va), (_, vb), (_, vc)] =>
          emitOp [i64, .bool] [i64, i64, .bool] (.addc 64) [va, vb, vc] "addc" fun
            | [s, c] => k [(.u64, s), (.bool, c)] | _ => pure .hlt
        | _ => pure .hlt
    | "c0_subb64", [a, b, bin] =>
      lowerCallArgs ctx env [.u64, .u64, .bool] [a, b, bin] fun
        | [(_, va), (_, vb), (_, vb0)] =>
          emitOp [i64, .bool] [i64, i64, .bool] (.subb 64) [va, vb, vb0] "subb" fun
            | [d, bOut] => k [(.u64, d), (.bool, bOut)] | _ => pure .hlt
        | _ => pure .hlt
    | "c0_umul128", [a, b] =>
      lowerCallArgs ctx env [.u64, .u64] [a, b] fun
        | [(_, va), (_, vb)] =>
          emitOp [i64, i64] [i64, i64] (.umulw 64) [va, vb] "umul" fun
            | [lo, hi] => k [(.u64, lo), (.u64, hi)] | _ => pure .hlt
        | _ => pure .hlt
    | "c0_f64_to_bits", [d] =>
      lowerCallArgs ctx env [.f64] [d] fun
        | [(_, vd)] => emitOp1 i64 [f64] (.bitcast f64 i64 rfl) [vd] "f2b" fun r => k [(.u64, r)]
        | _ => pure .hlt
    | "c0_bits_to_f64", [u] =>
      lowerCallArgs ctx env [.u64] [u] fun
        | [(_, vu)] => emitOp1 f64 [i64] (.bitcast i64 f64 rfl) [vu] "b2f" fun r => k [(.f64, r)]
        | _ => pure .hlt
    | "c0_f64_to_u64_sat", [d] =>
      lowerCallArgs ctx env [.f64] [d] fun
        | [(_, vd)] => emitF64ToU64Sat vd fun r => k [(.u64, r)] | _ => pure .hlt
    | _, _ =>
      if let some fd := ctx.fns.get? fn then
        if fd.isStatic && fd.isInline then
          if ctx.inlineStack.contains fn then
            throw s!"recursive static inline function '{fn}' is not supported in C0"
          lowerCallArgs ctx env (fd.params.map (·.1)) args fun argVals =>
            inlineFunction { ctx with inlineStack := fn :: ctx.inlineStack } fd argVals k
        else
          emitExternalOrDirectCall ctx env fd.name (fd.params.map (·.1)) fd.retTy args k
      else if let some sg := ctx.externs.get? fn then
        emitExternalOrDirectCall ctx env sg.name (sg.params.map (·.1)) sg.retTy args k
      else throw s!"unknown function '{fn}'"

  private partial def emitExternalOrDirectCall (ctx : LowerCtx) (env : LocalEnv)
      (fn : Sym) (paramTys : List C0Type) (retTy : C0Type) (args : List Expr)
      (k : List (C0Type × LArg) → LowerM LExpr) : LowerM LExpr := do
    lowerCallArgs ctx env paramTys args fun argVals => do
      let asTys := argVals.map fun (_, a) => a.ty
      let callArgs := argVals.map (·.2)
      let rRet ← MonadExcept.ofExcept (resolveType ctx.layout retTy)
      let retC0Tys : List C0Type := match rRet with | .void => [] | .tuple ts => ts | t => [t]
      let bsTys ← MonadExcept.ofExcept (lowerRetTys ctx.layout retTy)
      let binders ← bsTys.mapM (freshLVar "call")
      let outs := (retC0Tys.zip binders).map fun (ct, lv) => (ct, LArg.var lv.id lv.ty)
      pure (.call fn asTys bsTys callArgs binders (← k outs))

  private partial def inlineFunction (ctx : LowerCtx) (fd : FnDef)
      (argVals : List (C0Type × LArg)) (k : List (C0Type × LArg) → LowerM LExpr) : LowerM LExpr := do
    let innerEnv ← (fd.params.zip argVals).mapM fun ((_, nm), (ct, a)) => do
      pure { declId := ← freshDeclId, name := nm, val := .scalar ct a : EnvEntry }
    let rRet ← MonadExcept.ofExcept (resolveType ctx.layout fd.retTy)
    let retC0Tys : List C0Type := match rRet with | .void => [] | .tuple ts => ts | t => [t]
    let bsTys ← MonadExcept.ofExcept (lowerRetTys ctx.layout fd.retTy)
    let retCount := countReturns fd.body
    let endsWithRet := match fd.body.getLast? with | some (.retStmt _) => true | _ => false
    if retCount == 1 && endsWithRet then
      let jLbl ← freshLblId
      let jVars ← bsTys.mapM (freshLVar "ret_v")
      -- Fast inline path when single tail return has no extra jump if possible;
      -- note: `retCont` runs in `Except String`, so if `k` uses `LowerM` we bind a 1-block join
      -- UNLESS we only jump? Actually let's compute `joinBody` via `k` or store `retCont` in `LowerM`!
      -- Using a 1-block inline_ret join when `retCount > 1` and evaluating `k` directly on tail ret:
      let _ := (jLbl, jVars)
      -- Since `retCont` returns `Except String`, convert tail-ret directly by lowering `fd.body.dropLast` then `retStmt`!
      let initStmts := fd.body.dropLast
      let lastRet ← match fd.body.getLast! with | .retStmt es => pure es | _ => throw "internal"
      let ctxBody := { ctx with breakTarget := none, contTarget := none, contInlineStep := none, gotoTargets := {}, retTy := rRet, retCont := none }
      lowerStmtList ctxBody innerEnv initStmts fun env' =>
        evalAndPassRets ctxBody env' retC0Tys lastRet k
    else
      let jLbl ← freshLblId
      let jVars ← bsTys.mapM (freshLVar "ret_v")
      recordGroup "inline_ret" s!"iret_{fd.name}_{jLbl}" jVars
      let joinOuts := (retC0Tys.zip jVars).map fun (ct, lv) => (ct, LArg.var lv.id lv.ty)
      let joinBody ← k joinOuts
      let ctx' : LowerCtx := {
        ctx with
        breakTarget := none, contTarget := none, contInlineStep := none, gotoTargets := {}
        retTy := rRet
        retCont := some fun vals => pure (.jump jLbl bsTys (vals.map (·.2)))
      }
      let entry ← lowerStmtList ctx' innerEnv fd.body fun _ =>
        if bsTys.isEmpty then pure (.jump jLbl [] [])
        else throw s!"non-void inline function '{fd.name}' reaches end without return"
      pure (.group [(jLbl, jVars, joinBody)] entry)

  private partial def evalAndPassRets (ctx : LowerCtx) (env : LocalEnv)
      (cts : List C0Type) (es : List Expr) (k : List (C0Type × LArg) → LowerM LExpr) : LowerM LExpr := do
    unless cts.length == es.length do
      throw s!"return value count mismatch: expected {cts.length}, got {es.length}"
    let rec go (cs : List C0Type) (xs : List Expr) (acc : List (C0Type × LArg)) : LowerM LExpr :=
      match cs, xs with
      | [], [] => k acc
      | ct :: cs', e :: xs' =>
        lowerExpr ctx env e fun et ea =>
          convertVal ctx.layout et ct ea fun ca => go cs' xs' (acc ++ [(ct, ca)])
      | _, _ => throw "return arity mismatch"
    go cts es []

  private partial def countReturns (ss : List Stmt) : Nat :=
    ss.foldl (fun acc s => acc + countStmt s) 0
  where
    countStmt : Stmt → Nat
      | .retStmt _ => 1
      | .block bs => countReturns bs
      | .ifStmt _ t e? => countStmt t + (e?.map countStmt |>.getD 0)
      | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b => countStmt b
      | .switchStmt _ arms =>
        arms.foldl (fun a arm => a + countReturns arm.body) 0
      | .labelStmt _ st => countStmt st
      | _ => 0

  private partial def lowerLValWrite (ctx : LowerCtx) (env : LocalEnv) (lv : LVal)
      (op? : Option BinOp) (rhsExpr : Expr) (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    let evalCompOp (bop : BinOp) (curTy : C0Type) (curA : LArg) (kw : C0Type → LArg → LowerM LExpr) := do
      let tid ← freshDeclId
      let dummyEnv : LocalEnv := env ++ [{ declId := tid, name := "__lval_tmp", val := .scalar curTy curA }]
      lowerBinOp ctx dummyEnv bop (.var "__lval_tmp") rhsExpr kw
    let writeAtPtr (elemTy : C0Type) (pa : LArg) : LowerM LExpr := do
      let re ← MonadExcept.ofExcept (resolveType ctx.layout elemTy)
      match op? with
      | none =>
        lowerExpr ctx env rhsExpr fun rty ra =>
          storeMemScalar ctx.layout re rty pa ra (k env)
      | some bop =>
        loadMemScalar ctx.layout re pa fun curTy curA =>
          evalCompOp bop curTy curA fun rty ra =>
            storeMemScalar ctx.layout re rty pa ra (k env)
    match lv with
    | .var nm =>
      match lookupEnv? env nm with
      | some { val := .scalar c0ty _, .. } =>
        let evalRhs := fun kVal =>
          match op? with
          | none => lowerExpr ctx env rhsExpr kVal
          | some bop => lowerBinOp ctx env bop (.var nm) rhsExpr kVal
        evalRhs fun rhsTy rhsArg =>
          convertVal ctx.layout rhsTy c0ty rhsArg fun cv =>
            k (updateEnv env nm (.scalar c0ty cv))
      | _ => throw s!"unbound local variable '{nm}' in assignment"
    | .deref ptrE =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr elem => writeAtPtr elem pa
        | t => throw s!"cannot store through non-pointer {repr t}"
    | .arrow ptrE fld =>
      lowerExpr ctx env ptrE fun pty pa => do
        match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
        | .ptr aggTy =>
          let loc ← MonadExcept.ofExcept (lookupField ctx.layout aggTy fld)
          let writeF := fun rty ra => storeFieldToAddr ctx.layout pa 0 loc rty ra (k env)
          match op? with
          | none => lowerExpr ctx env rhsExpr writeF
          | some bop =>
            loadFieldFromAddr ctx.layout pa 0 loc fun curTy curA =>
              evalCompOp bop curTy curA writeF
        | t => throw s!"'->' requires pointer, got {repr t}"
    | .index arrE idxE =>
      lowerIndexAddr ctx env arrE idxE fun elemTy pa => writeAtPtr elemTy pa
    | .dot baseLv fld =>
      let rec splitDot : LVal → List String → LVal × List String
        | .dot b f, acc => splitDot b (f :: acc)
        | root, acc => (root, acc)
      let (rootLv, chain) := splitDot baseLv [fld]
      let doMemField (aggTy : C0Type) (baseAddr : LArg) (baseOff : Nat) : LowerM LExpr := do
        let (off', loc) ← MonadExcept.ofExcept (resolveFieldChain ctx.layout aggTy chain)
        let writeF := fun rty ra => storeFieldToAddr ctx.layout baseAddr (baseOff + off') loc rty ra (k env)
        match op? with
        | none => lowerExpr ctx env rhsExpr writeF
        | some bop =>
          loadFieldFromAddr ctx.layout baseAddr (baseOff + off') loc fun curTy curA =>
            evalCompOp bop curTy curA writeF
      match rootLv with
      | .deref ptrE =>
        lowerExpr ctx env ptrE fun pty pa => do
          match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
          | .ptr aggTy => doMemField aggTy pa 0
          | t => throw s!"cannot access field on non-pointer {repr t}"
      | .arrow ptrE fld0 =>
        lowerExpr ctx env ptrE fun pty pa => do
          match ← MonadExcept.ofExcept (resolveType ctx.layout pty) with
          | .ptr aggTy =>
            match ← MonadExcept.ofExcept (lookupField ctx.layout aggTy fld0) with
            | .regular off subTy _ => doMemField subTy pa off
            | .bitfield _ _ _ _ _ => throw s!"cannot access field inside bitfield '{fld0}'"
          | t => throw s!"'->' requires pointer, got {repr t}"
      | .index arrE idxE => lowerIndexAddr ctx env arrE idxE fun elemTy pa => doMemField elemTy pa 0
      | .var nm =>
        match lookupEnv? env nm with
        | some { val := .scalar aggTy regVal, .. } =>
          let (off', loc) ← MonadExcept.ofExcept (resolveFieldChain ctx.layout aggTy chain)
          let (aggSz, _) ← MonadExcept.ofExcept (typeSizeAlign ctx.layout aggTy)
          let regBits := aggSz * 8
          let regTy := Ty.bits regBits
          let (bitOff, width, dty) := match loc with
            | .regular fOff fty fsz => ((off' + fOff) * 8, fsz * 8, fty)
            | .bitfield uOff _ lBit w fty => ((off' + uOff) * 8 + lBit, w, fty)
          if op?.isSome then
            let fldPath := String.intercalate "." chain
            throw ("compound assignment on register bitfield / value field " ++
              s!"'{nm}.{fldPath}' is not supported")
          lowerExpr ctx env rhsExpr fun rty ra => do
            let rd ← MonadExcept.ofExcept (resolveType ctx.layout dty)
            convertVal ctx.layout rty rd ra fun cv =>
              convertVal ctx.layout rd (.int false regBits) cv fun uval => do
                let valMask : BitVec regBits := BitVec.ofNat regBits ((1 <<< width) - 1)
                let maskStep := fun mv => do
                  let shiftStep := fun sv => do
                    if width == regBits && bitOff == 0 then k (updateEnv env nm (.scalar aggTy sv))
                    else
                      let clearMask : BitVec regBits := ~~~(BitVec.ofNat regBits (((1 <<< width) - 1) <<< bitOff))
                      emitOp1 regTy [regTy, regTy] (.and regTy) [regVal, .imm regTy clearMask] "rclr" fun cleared =>
                        emitOp1 regTy [regTy, regTy] (.or regTy) [cleared, sv] "rupd" fun updated =>
                          k (updateEnv env nm (.scalar aggTy updated))
                  if bitOff == 0 then shiftStep mv
                  else emitOp1 regTy [regTy, regTy] (.shl regTy) [mv, .imm regTy (BitVec.ofNat regBits bitOff)] "rshl" shiftStep
                if width == regBits then maskStep uval
                else emitOp1 regTy [regTy, regTy] (.and regTy) [uval, .imm regTy valMask] "rmsk" maskStep
        | _ => throw s!"unbound local '{nm}' in field assignment"
      | .dot _ _ => throw "unreachable"

  private partial def lowerStmtList (ctx : LowerCtx) (env : LocalEnv) (stmts : List Stmt)
      (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    let lastLabelIdx? := Id.run do
      let mut idx : Option Nat := none
      for i in [:stmts.length] do
        if stmts[i]! matches .labelStmt _ _ then idx := some i
      return idx
    match lastLabelIdx? with
    | some idx =>
      let prefixStmts := stmts.take idx
      let suffixStmts := stmts.drop idx
      let (lblName, firstLabeledStmt) ← match suffixStmts.head! with
        | .labelStmt l s => pure (l, s)
        | _ => throw "internal error"
      let afterStmts := firstLabeledStmt :: suffixStmts.tail!
      -- Lower leading statements before the first `goto` to any label in this block so declarations enter `env`
      let allLbls := stmts.filterMap fun | .labelStmt l _ => some l | _ => none
      let firstUseIdx := (prefixStmts.findIdx? fun st => allLbls.any (stmtHasGoto · st)).getD prefixStmts.length
      if firstUseIdx == prefixStmts.length then
        lowerStmtList ctx env (prefixStmts ++ afterStmts) k
      else
        let leadStmts := prefixStmts.take firstUseIdx
        let regionStmts := prefixStmts.drop firstUseIdx
        lowerStmtList ctx env leadStmts fun envMid => do
          let mutSet := regionStmts.foldl (fun acc s => setUnion acc (stmtMutatedLocals false false s)) {}
          let envMutVars ← MonadExcept.ofExcept (selectJoinVars envMid mutSet)
          let lblId ← freshLblId
          let lvs ← allocJoinVars envMutVars
          recordGroup "goto_join" s!"lbl_{lblName}" lvs
          let target : JumpTarget := { lblId, vars := envMutVars }
          let envAfter := rebindJoinVars envMid envMutVars lvs
          let suffixBody ← lowerStmtList ctx envAfter afterStmts k
          let ctxPrefix := { ctx with gotoTargets := ctx.gotoTargets.insert lblName target }
          let prefixBody ← lowerStmtList ctxPrefix envMid regionStmts fun env' => do
            let args ← MonadExcept.ofExcept (snapshotArgs env' envMutVars)
            pure (.jump lblId (lvs.map (·.ty)) args)
          pure (.group [(lblId, lvs, suffixBody)] prefixBody)
    | none =>
      lowerPlainStmts ctx env stmts k

  private partial def lowerPlainStmts (ctx : LowerCtx) (env : LocalEnv) (stmts : List Stmt)
      (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    match stmts with
    | [] => k env
    | s :: rest =>
      match s with
      | .ifStmt cond thn els? =>
        let els := els?.getD .empty
        let thnFalls := stmtMayFallThrough thn
        let elsFalls := stmtMayFallThrough els
        if !thnFalls && !elsFalls then
          let tBody ← lowerStmt ctx env thn fun _ => pure .hlt
          let eBody ← lowerStmt ctx env els fun _ => pure .hlt
          lowerCond ctx env cond (pure tBody) (pure eBody)
        else if thnFalls && !elsFalls then
          let eBody ← lowerStmt ctx env els fun _ => pure .hlt
          let tBody ← lowerStmt ctx env thn fun env' => lowerPlainStmts ctx env' rest k
          lowerCond ctx env cond (pure tBody) (pure eBody)
        else if !thnFalls && elsFalls then
          let tBody ← lowerStmt ctx env thn fun _ => pure .hlt
          let eBody ← lowerStmt ctx env els fun env' => lowerPlainStmts ctx env' rest k
          lowerCond ctx env cond (pure tBody) (pure eBody)
        else
          let mutSet := setUnion (stmtMutatedLocals false false thn) (stmtMutatedLocals false false els)
          let mVars ← MonadExcept.ofExcept (selectJoinVars env mutSet)
          let jLbl ← freshLblId
          let jLvs ← allocJoinVars mVars
          recordGroup "if_join" s!"if_{jLbl}" jLvs
          let envAfter := rebindJoinVars env mVars jLvs
          let joinBody ← lowerPlainStmts ctx envAfter rest k
          let mkJump := fun envBranch => do
            let args ← MonadExcept.ofExcept (snapshotArgs envBranch mVars)
            pure (.jump jLbl (jLvs.map (·.ty)) args)
          let tBody ← lowerStmt ctx env thn mkJump
          let eBody ← lowerStmt ctx env els mkJump
          let entry ← lowerCond ctx env cond (pure tBody) (pure eBody)
          pure (.group [(jLbl, jLvs, joinBody)] entry)
      | .whileStmt cond body => lowerLoop ctx env none (some cond) none body false rest k
      | .doWhileStmt body cond => lowerLoop ctx env none (some cond) none body true rest k
      | .forStmt init? cond? step? body =>
        match init? with
        | some initS =>
          lowerStmt ctx env initS fun env' =>
            lowerLoop ctx env' (some env) cond? step? body false rest k
        | none => lowerLoop ctx env none cond? step? body false rest k
      | _ =>
        if stmtMayFallThrough s then
          lowerStmt ctx env s fun env' => lowerPlainStmts ctx env' rest k
        else
          lowerStmt ctx env s fun _ => pure .hlt

  private partial def lowerLoop (ctx : LowerCtx) (env : LocalEnv)
      (outerEnvBeforeInit? : Option LocalEnv)
      (cond? : Option Expr) (step? : Option Stmt) (body : Stmt) (isDoWhile : Bool)
      (rest : List Stmt) (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    let hasBrk := stmtHasBreak body
    let bodyMutBack := stmtMutatedLocals true false body
    let stepMutBack := step?.map (stmtMutatedLocals true false) |>.getD {}
    let lVars ← MonadExcept.ofExcept (selectJoinVars env (setUnion bodyMutBack stepMutBack))
    let lpLbl ← freshLblId
    let lpLvs ← allocJoinVars lVars
    recordGroup "loop" s!"lp_{lpLbl}" lpLvs
    let lpTarget : JumpTarget := { lblId := lpLbl, vars := lVars }
    let envLoop := rebindJoinVars env lVars lpLvs
    let initArgs ← MonadExcept.ofExcept (snapshotArgs env lVars)
    let reconcile (envExit : LocalEnv) : LocalEnv :=
      match outerEnvBeforeInit? with
      | none => envExit
      | some orig => envExit.take orig.length
    let jumpLp := fun envCur => do
      let args ← MonadExcept.ofExcept (snapshotArgs envCur lVars)
      pure (.jump lpLbl (lpLvs.map (·.ty)) args)
    let mkDoWhileBody (ctxB : LowerCtx) (exitJump : LocalEnv → LowerM LExpr) : LowerM LExpr := do
      if stmtHasContinue body then
        let contVars ← MonadExcept.ofExcept (selectJoinVars env (stmtMutatedLocals false false body))
        let contLbl ← freshLblId
        let contLvs ← allocJoinVars contVars
        recordGroup "do_cont" s!"dc_{contLbl}" contLvs
        let envCont := rebindJoinVars env contVars contLvs
        let contCond ← lowerCond ctx envCont (cond?.getD (.boolLit true)) (jumpLp envCont) (exitJump envCont)
        let contTgt : JumpTarget := { lblId := contLbl, vars := contVars }
        let jumpCont := fun envCur => do
          let args ← MonadExcept.ofExcept (snapshotArgs envCur contVars)
          pure (.jump contLbl (contLvs.map (·.ty)) args)
        let doBody ← lowerStmt { ctxB with contTarget := some contTgt } envLoop body jumpCont
        pure (.group [(contLbl, contLvs, contCond)] doBody)
      else
        lowerStmt ctxB envLoop body fun envAfterBody =>
          lowerCond ctx envAfterBody (cond?.getD (.boolLit true)) (jumpLp envAfterBody) (exitJump envAfterBody)

    if hasBrk then
      let mutAny := setUnion (stmtMutatedLocals false false body) stepMutBack
      let brkEnvBase := reconcile env
      let brkVars ← MonadExcept.ofExcept (selectJoinVars brkEnvBase mutAny)
      let brkLbl ← freshLblId
      let brkLvs ← allocJoinVars brkVars
      recordGroup "loop_break" s!"brk_{brkLbl}" brkLvs
      let brkTarget : JumpTarget := { lblId := brkLbl, vars := brkVars }
      let envAfter := rebindJoinVars brkEnvBase brkVars brkLvs
      let afterBody ← lowerPlainStmts ctx envAfter rest k
      let jumpBrk := fun envCur => do
        let args ← MonadExcept.ofExcept (snapshotArgs envCur brkVars)
        pure (.jump brkLbl (brkLvs.map (·.ty)) args)
      let ctxBody : LowerCtx := { ctx with
        breakTarget := some brkTarget
        contTarget := some lpTarget
        contInlineStep := if isDoWhile then none else step? }
      let lpBody ←
        if isDoWhile then
          mkDoWhileBody ctxBody jumpBrk
        else
          let bodyPlusStep ← lowerStmt ctxBody envLoop body fun envAfterBody =>
            match step? with
            | some st => lowerStmt ctxBody envAfterBody st jumpLp
            | none => jumpLp envAfterBody
          match cond? with
          | some c => lowerCond ctx envLoop c (pure bodyPlusStep) (jumpBrk envLoop)
          | none => pure bodyPlusStep
      let innerGroup := LExpr.group [(lpLbl, lpLvs, lpBody)] (.jump lpLbl (lpLvs.map (·.ty)) initArgs)
      pure (.group [(brkLbl, brkLvs, afterBody)] innerGroup)
    else
      let ctxBody : LowerCtx := { ctx with
        breakTarget := none
        contTarget := some lpTarget
        contInlineStep := if isDoWhile then none else step? }
      let infLoop := match cond? with
        | none => true
        | some (.boolLit true) => true
        | some (.intLit v _ _) => v != 0
        | _ => false
      let exitCont :=
        if infLoop then fun _ => pure .hlt
        else fun envExit => lowerPlainStmts ctx (reconcile envExit) rest k
      let lpBody ←
        if isDoWhile then
          mkDoWhileBody ctxBody exitCont
        else
          let bodyPlusStep ← lowerStmt ctxBody envLoop body fun envAfterBody =>
            match step? with
            | some st => lowerStmt ctxBody envAfterBody st jumpLp
            | none => jumpLp envAfterBody
          match cond? with
          | some c => lowerCond ctx envLoop c (pure bodyPlusStep) (exitCont envLoop)
          | none => pure bodyPlusStep
      pure (.group [(lpLbl, lpLvs, lpBody)] (.jump lpLbl (lpLvs.map (·.ty)) initArgs))

  private partial def lowerStmt (ctx : LowerCtx) (env : LocalEnv) (s : Stmt)
      (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    match s with
    | .empty => k env
    | .block ss =>
      lowerStmtList ctx env ss fun envAfter =>
        k (envAfter.take env.length)
    | .decl ty nm init =>
      let rty ← MonadExcept.ofExcept (resolveType ctx.layout ty)
      let did ← freshDeclId
      match init with
      | .zeroInit =>
        let lt ← MonadExcept.ofExcept (lowerScalarTy ctx.layout rty)
        let imm0 : LArg := match lt with
          | .bool => .imm .bool false
          | .bits n => .imm (.bits n) (0#n)
          | .float .d => .imm f64 0#64
          | _ => .imm i64 0#64
        k (env ++ [{ declId := did, name := nm, val := .scalar rty imm0 }])
      | .expr e =>
        lowerExpr ctx env e fun ety a =>
          convertVal ctx.layout ety rty a fun ca =>
            k (env ++ [{ declId := did, name := nm, val := .scalar rty ca }])
    | .assign lv op? rhs => lowerLValWrite ctx env lv op? rhs k
    | .incDec lv isInc =>
      lowerLValWrite ctx env lv (some (if isInc then .add else .sub)) (.intLit 1 .none) k
    | .callStmt lhs fn args =>
      lowerCallExpr ctx env fn args fun outs => do
        if lhs.isEmpty then k env
        else
          unless lhs.length == outs.length do
            throw s!"call to '{fn}' returned {outs.length} value(s), assigned to {lhs.length}"
          let rec bindAll (rem : List (String × C0Type × LArg)) (eCur : LocalEnv) : LowerM LExpr :=
            match rem with
            | [] => k eCur
            | (nm, rty, ra) :: more =>
              match lookupEnv? eCur nm with
              | some { val := .scalar c0ty _, .. } =>
                convertVal ctx.layout rty c0ty ra fun ca =>
                  bindAll more (updateEnv eCur nm (.scalar c0ty ca))
              | _ => throw s!"unbound local '{nm}' in multi-return assignment"
          bindAll (lhs.zip (outs.map fun (t, a) => (t, a))) env
    | .breakStmt =>
      match ctx.breakTarget with
      | some tgt =>
        let args ← MonadExcept.ofExcept (snapshotArgs env tgt.vars)
        pure (.jump tgt.lblId (tgt.vars.map (·.2.2.2)) args)
      | none => throw "`break` outside loop or switch"
    | .continueStmt =>
      match ctx.contTarget with
      | some tgt =>
        match ctx.contInlineStep with
        | some step =>
          lowerStmt { ctx with contInlineStep := none } env step fun env' => do
            let args ← MonadExcept.ofExcept (snapshotArgs env' tgt.vars)
            pure (.jump tgt.lblId (tgt.vars.map (·.2.2.2)) args)
        | none =>
          let args ← MonadExcept.ofExcept (snapshotArgs env tgt.vars)
          pure (.jump tgt.lblId (tgt.vars.map (·.2.2.2)) args)
      | none => throw "`continue` outside loop"
    | .gotoStmt lbl =>
      match ctx.gotoTargets.get? lbl with
      | some tgt =>
        let args ← MonadExcept.ofExcept (snapshotArgs env tgt.vars)
        pure (.jump tgt.lblId (tgt.vars.map (·.2.2.2)) args)
      | none => throw s!"goto target '{lbl}' is not a forward label in an enclosing block"
    | .labelStmt _ inner => lowerStmt ctx env inner k
    | .retStmt es =>
      let retC0Tys : List C0Type := match ctx.retTy with
        | .void => [] | .tuple ts => ts | t => [t]
      evalAndPassRets ctx env retC0Tys es fun acc => do
        match ctx.retCont with
        | some rk => MonadExcept.ofExcept (rk acc)
        | none =>
          let rsTys ← MonadExcept.ofExcept (lowerRetTys ctx.layout ctx.retTy)
          pure (.ret rsTys (acc.map (·.2)))
    | .assumeStmt cond =>
      let body ← k env
      lowerCond ctx env cond (pure body) (pure .hlt)
    | .checkStmt cond line =>
      let body ← k env
      lowerCond ctx env cond (pure body)
        (pure (.exit "c0_abort" [i32] [.imm i32 (BitVec.ofInt 32 line)]))
    | .assertStmt cond line =>
      if ctx.assertAsCheck then
        let body ← k env
        lowerCond ctx env cond (pure body)
          (pure (.exit "c0_abort" [i32] [.imm i32 (BitVec.ofInt 32 line)]))
      else k env
    | .switchStmt scrut arms => lowerSwitch ctx env scrut arms k
    | .ifStmt _ _ _ | .whileStmt _ _ | .doWhileStmt _ _ | .forStmt _ _ _ _ =>
      lowerPlainStmts ctx env [s] k

  private partial def lowerSwitch (ctx : LowerCtx) (env : LocalEnv) (scrut : Expr)
      (arms : List SwitchArm) (k : LocalEnv → LowerM LExpr) : LowerM LExpr := do
    let mutSet := arms.foldl (fun acc a => setUnion acc (stmtMutatedLocals false false (.block a.body))) {}
    let jVars ← MonadExcept.ofExcept (selectJoinVars env mutSet)
    let brkLbl ← freshLblId
    let brkLvs ← allocJoinVars jVars
    recordGroup "switch_join" s!"sw_{brkLbl}" brkLvs
    let brkTarget : JumpTarget := { lblId := brkLbl, vars := jVars }
    let envAfter := rebindJoinVars env jVars brkLvs
    let afterBody ← k envAfter
    let ctxSw := { ctx with breakTarget := some brkTarget }
    let jumpBrk := fun envCur => do
      let args ← MonadExcept.ofExcept (snapshotArgs envCur jVars)
      pure (.jump brkLbl (brkLvs.map (·.ty)) args)
    let entry ← lowerExpr ctx env scrut fun sty sa => do
      let pty := intPromote sty
      convertVal ctx.layout sty pty sa fun scrA => do
        let n := intBitWidth pty
        let lt := Ty.bits n
        let rec runFrom (envCur : LocalEnv) : List SwitchArm → LowerM LExpr
          | [] => jumpBrk envCur
          | arm :: rest =>
            lowerStmtList ctxSw envCur arm.body fun envNext => runFrom envNext rest
        let defBody ← match arms.findIdx? (·.hasDefault) with
          | some idx => runFrom env (arms.drop idx)
          | none => jumpBrk env
        let rec buildCases : List SwitchArm → LowerM LExpr
          | [] => pure defBody
          | arm :: rest => do
            let elseChain ← buildCases rest
            if arm.vals.isEmpty then pure elseChain
            else
              let armBody ← runFrom env (arm :: rest)
              let rec testVals : List Int → LowerM LExpr
                | [] => pure elseChain
                | v :: vs => do
                  let restTest ← testVals vs
                  emitOp1 .bool [lt, lt] (.cmp .eq lt) [scrA, .imm lt (BitVec.ofInt n v)] "sw_eq" fun eqB =>
                    pure (.jnz eqB armBody restTest)
              testVals arm.vals
        buildCases arms
    pure (.group [(brkLbl, brkLvs, afterBody)] entry)
end

/-! ## Function & Translation-Unit Lowering -/

private def lowerFnDef (ctx : LowerCtx) (fd : FnDef) : Except String LFn := do
  let mut env : LocalEnv := []
  let mut paramLVs : List LVar := []
  let mut st : LowerState := {}
  for (pt, nm) in fd.params do
    let rpt ← resolveType ctx.layout pt
    let lt ← lowerScalarTy ctx.layout rpt
    let lv : LVar := { id := st.nextVar, name := nm, ty := lt }
    let did := st.nextDecl
    st := { st with nextVar := st.nextVar + 1, nextDecl := did + 1 }
    paramLVs := paramLVs ++ [lv]
    env := env ++ [{ declId := did, name := nm, val := .scalar rpt (.var lv.id lt) }]
  let rRet ← resolveType ctx.layout fd.retTy
  let rs ← lowerRetTys ctx.layout rRet
  let ctxFn : LowerCtx := { ctx with retTy := rRet, retCont := none }
  let (body, st') ← (lowerStmtList ctxFn env fd.body fun _ =>
    if rs.isEmpty then pure (.ret [] [])
    else throw s!"non-void function '{fd.name}' reaches end without return").run st
  let shape : FnShape := {
    name := fd.name, params := paramLVs.map fun v => (v.name, v.ty), rets := rs, groups := st'.groups
  }
  pure { name := fd.name, params := paramLVs, rs, body, shape }

/-- Lower all declarations in a C0 `TranslationUnit` into an `LModule`. -/
def lowerTranslationUnit (tu : TranslationUnit) (assertAsCheck : Bool := false) :
    Except String LModule := do
  let layout ← buildLayoutEnv tu
  let mut fnDefs : Std.HashMap String FnDef := {}
  let mut fnOrder : List FnDef := []
  let mut externMap : Std.HashMap String FnSig := {}
  let mut externList : List Extern := []
  let mut enumMap : Std.HashMap String Int := {}
  for d in tu.decls do
    match d with
    | .fnDef fd => fnDefs := fnDefs.insert fd.name fd; fnOrder := fnOrder ++ [fd]
    | .fnDecl sg =>
      if !fnDefs.contains sg.name && !externMap.contains sg.name then
        externMap := externMap.insert sg.name sg
    | .enumConsts items =>
      for (nm, v) in items do enumMap := enumMap.insert nm v
    | _ => pure ()
  for (_, sg) in externMap.toList do
    if !fnDefs.contains sg.name && sg.name != "c0_abort" then
      let as ← sg.params.mapM fun (t, _) => lowerScalarTy layout t
      let rs ← lowerRetTys layout sg.retTy
      externList := externList ++ [{ name := sg.name, as, rs }]
  let ctx : LowerCtx := { layout, fns := fnDefs, externs := externMap, enums := enumMap, assertAsCheck }
  let lfns ← fnOrder.mapM (lowerFnDef ctx)
  pure { fns := lfns, externs := externList, exits := ["c0_abort"] }

end LeanQbe.T.Frontend.C0
