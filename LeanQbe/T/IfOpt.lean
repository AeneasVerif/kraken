module

public import LeanQbe.T.OptUtil

/-!
# Diamond `jnz` → `select` If-Conversion (`Func.ifOpt`)

Pure 100%-PHOAS if-conversion pass (`ifOpt` / `Func.ifOpt`) using local label tagging
`JLabel L ts` (no `reify`/`TFlat`):

* Recognizes 1-block join groups `.group (sig := [ts]) (.cons joinBlk .nil) k` whose entry `k`
  reaches `.jnz c thenArm elseArm` (at root or after straight-line entry prefixes) where:
  - `thenArm` and `elseArm` each contain at most `4` pure, total, non-UB `.let_` instructions
    from the whitelisted safe opcode set (`isSafeOp`, guarding `!t.hasFloat` on arithmetic/shifts/
    comparisons and `m ≤ n`/`n ≤ m` on `zext`/`sext`/`trunc`; excluding `udiv`/`sdiv`/`urem`/`srem`,
    all float ops, `bswap`, `.load`, `.store`, `.call`),
  - both arms terminate at `.jump J argsT` and `.jump J argsE` on the current `.group`'s binder `J`,
  - `ts` consists solely of `select`-compatible non-float types (`!t.hasFloat`).
* Hoists the pure prefixes of both arms, emits nested `.select`s across `.pair`s / elementwise
  tuple `.select`s onto `.bits`/`bool` (keeping identical operands un-selected via symbolic keys),
  and jumps to `J` with the selected arguments while preserving the `.group` structure for
  `SimplifyGroupPlan`. Never turns `.select` into `.jnz` (preserving constant-time selects).

Correctness (`LeanQbe/T/IfOptLemmas.lean`): `ifOpt_wp`, `ifOpt_wf`, `Func.ifOpt_wf`,
`Func.ifOpt_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace IfOptImpl

/-! ## Local PHOAS label tagging and symbolic value keys -/

/-- Label representation for `IfOpt`: `outer` preserves enclosing labels, `loc` tags the current
1-block `.group` binder for `checkDiamondWith`, and `tag` tags every `.group` binder with a unique
binder `id` alongside its PHOAS label `lbl` for arbitrary-position diamond conversion. -/
inductive JLabel (L : List Ty → Type) : List Ty → Type
  | outer {ts : List Ty} : L ts → JLabel L ts
  | loc {ts : List Ty} (id : Nat) : JLabel L ts
  | tag {ts : List Ty} (id : Nat) (lbl : L ts) : JLabel L ts

/-- Tag every binder in a `.group` label tuple `Js` with consecutive IDs starting at `depth`. -/
def tagLabels {L : List Ty → Type} (depth : Nat) :
    {sig : List (List Ty)} → Tup L sig → Tup (JLabel L) sig
  | [], () => ()
  | _ :: _, (j, Js) => (.tag depth j, tagLabels (depth + 1) Js)

/-- Extract the underlying PHOAS label from `JLabel` (`loc` has no underlying label). -/
def unwrapJLabel {L : List Ty → Type} {ts : List Ty} : JLabel L ts → Option (L ts)
  | .outer l => some l
  | .tag _ l => some l
  | .loc _ => none

/-- Input variable representation in `ifOpt`: output operand paired with symbolic `FKey`. -/
abbrev IVal (V : Ty → Type) (t : Ty) : Type := Arg V t × FKey t

/-- Output operand of an `Arg (IVal V) t`. -/
def iout {V : Ty → Type} {t : Ty} : Arg (IVal V) t → Arg V t
  | .var p => p.1
  | .imm c => .imm c

/-- Symbolic key of an `Arg (IVal V) t`. -/
def ikey {V : Ty → Type} {t : Ty} : Arg (IVal V) t → FKey t
  | .var p => p.2
  | .imm c => .imm c

/-- Map `iout` across an operand tuple. -/
abbrev tupIOut {V : Ty → Type} :
    {ts : List Ty} → Tup (Arg (IVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => iout

/-- Wrap bound output variables `xs : Tup V ts` into fresh `IVal V`s starting at `next`. -/
abbrev freshIVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (IVal V) ts :=
  tupFreshWith fun x next => (.var x, .var next)

/-- Inhabited dummy `IVal V` tuple for speculative diamond inspection (never emitted). -/
def dummyIVals {V : Ty → Type} : (ts : List Ty) → Nat → Tup (IVal V) ts
  | [], _ => ()
  | _ :: ts, next => ((.imm default, .var next), dummyIVals ts (next + 1))

/-! ## Safe speculative opcode whitelist and diamond pattern checker -/

/-- Whitelist of pure, total, non-UB opcodes eligible for speculative hoisting in `IfOpt`. -/
def isSafeOp {sig rs : List Ty} : OpCode sig rs → Bool
  | .copy _ => true
  | .add t | .sub t | .mul t | .neg t => !t.hasFloat
  | .and _ | .or _ | .xor _ | .not _ | .ternlog _ _ => true
  | .shl t | .lshr t | .ashr t | .rotl t | .rotr t => !t.hasFloat
  | .fshl _ | .fshr _ => true
  | .clz _ | .cls _ | .rbit _ | .ctz _ | .popcnt _ => true
  | .bswap t => t.bswapOk
  | .cmp _ t _ _ => !t.hasFloat
  | .select _ | .blend _ _ _ => true
  | .ofBool _ => true
  | .addc _ | .subb _ | .umulw _ | .smulw _ => true
  | .udiv0 _ | .sdiv0 _ => true
  | .mkpair _ _ | .unpair _ _ => true
  | .zext m n | .sext m n => Nat.ble m n
  | .trunc m n => Nat.ble n m
  | .bitcast _ _ _ => true
  | .shufd t _ | .shufb t | .alignr t _ | .blendw t _ => t.size != 0 && t.size % 128 == 0
  | .sha256rnds2 | .sha256msg1 | .sha256msg2 => true
  | _ => false

/-- Type eligible for `select` conversion (leaves are `.bool` and `.bits`, no floats). -/
def isSelectTy (t : Ty) : Bool := !t.hasFloat

/-- Signature eligible for `select` conversion. -/
def isSelectSig (ts : List Ty) : Bool := ts.all isSelectTy

/-- Variant of `isSelectTy` optionally restricting to machine `.bits` (`8`/`16`/`32`/`64`) so
post-`Legal` targets never see `.select .bool` or `.select (.pair ..)`. -/
def isSelectTyWith (bitsOnly : Bool) (t : Ty) : Bool :=
  if bitsOnly then match t with | .bits n => [8, 16, 32, 64].contains n | _ => false
  else isSelectTy t

/-- Signature filter parameterized by `bitsOnly`. -/
def isSelectSigWith (bitsOnly : Bool) (ts : List Ty) : Bool :=
  ts.all (isSelectTyWith bitsOnly)

/-- Target recognized by `checkArm`: a local `.group` binder `loc`, an arbitrary-position tagged
binder `tag`, or function return `ret`. -/
inductive ArmTarget : Type
  | loc (jId : Nat) (jTs : List Ty)
  | tag (jId : Nat) (jTs : List Ty)
  | ret

/-- Plan for one arm of a matched diamond, permitting pure `.let_`s and bounded nested `.jnz`
sub-diamonds up to `.jump` or `.ret`. -/
inductive ArmPlan : Type
  | jump
  | ret
  | let_ (rest : ArmPlan)
  | jnz (pT pE : ArmPlan)

/-- Post-store pure tail plan up to `.jump` or `.ret`. -/
inductive StoreTail : Type
  | jump
  | ret
  | let_ (rest : StoreTail)

/-- Per-instruction action for hoisting a store-diamond arm prefix up to `.store`. -/
inductive StoreStep : Type
  | let_ (rest : StoreStep)
  | loadEmit (rest : StoreStep)
  | loadReuse (slot : Nat) (rest : StoreStep)
  | store (tail : StoreTail)

/-- Matched two-arm common-address store-sinking diamond plan at `.jnz c t e`. -/
structure StoreDiamondPlan : Type where
  armT : StoreStep
  armE : StoreStep
  storeTy : Ty
  numLoads : Nat

/-- Structural plan for a matched diamond inside a 1-block `.group` continuation. -/
inductive DiamondPlan : Type
  | jnz (pT pE : ArmPlan)
  | jnzStore (sp : StoreDiamondPlan)
  | let_ (rest : DiamondPlan)
  | load (rest : DiamondPlan)
  | store (rest : DiamondPlan)
  | call (rest : DiamondPlan)

/-- Tagged jump target discovered in a `jnz` arm during arbitrary-position conversion. -/
structure TaggedTarget (L : List Ty → Type) where
  jTs : List Ty
  jId : Nat
  lbl : L jTs

/-- Find the leftmost `.jump (.tag id lbl)` in an arm along `.let_` and `then` branches. -/
def findFirstJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → Expr (IVal V) (JLabel L) rs → Option (TaggedTarget L)
  | 0, _ => none
  | _ + 1, .jump (ts := ts) (.tag id lbl) _ => some ⟨ts, id, lbl⟩
  | fuel + 1, .let_ _ k => findFirstJump fuel (k (dummyIVals _ 0))
  | fuel + 1, .jnz _ t _ => findFirstJump fuel t
  | _ + 1, _ => none

/-- Check that `e` consists of at most `letFuel` total safe `.let_` bindings and at most
`jnzFuel` nested `.jnz` levels terminating at `tgt`. -/
def checkArm {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (tgt : ArmTarget) :
    Nat → Nat → Nat → Expr (IVal V) (JLabel L) rs → Option (ArmPlan × Nat)
  | jnzFuel, letFuel, next, .let_ (ts := ts) op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 =>
        (checkArm tgt jnzFuel letFuel' (next + ts.length) (k (dummyIVals ts next))).map
          fun (p, rem) => (.let_ p, rem)
    else none
  | _, letFuel, _, .jump (ts := ts) j _ =>
    match tgt, j with
    | .loc jId jTs, .loc id
    | .tag jId jTs, .tag id _ =>
      if id == jId && Ty.listBeq ts jTs then some (.jump, letFuel) else none
    | _, _ => none
  | _, letFuel, _, .ret _ =>
    match tgt with
    | .ret => some (.ret, letFuel)
    | _ => none
  | jnzFuel + 1, letFuel, next, .jnz _ t e => do
    let (pT, rem1) ← checkArm tgt jnzFuel letFuel next t
    let (pE, rem2) ← checkArm tgt jnzFuel rem1 next e
    pure (.jnz pT pE, rem2)
  | _, _, _, _ => none

/-- Pointwise `fKeyBeq` on a tuple of `FKey`s. -/
def fKeysBeq : {ts : List Ty} → Tup FKey ts → Tup FKey ts → Bool
  | [], (), () => true
  | _ :: _, (a, as), (b, bs) => fKeyBeq a b && fKeysBeq as bs

/-- Fresh variable `FKey` tuple starting at `next`. -/
def freshFKeys : (ts : List Ty) → Nat → Tup FKey ts
  | [], _ => ()
  | _ :: ts, next => (.var next, freshFKeys ts (next + 1))

/-- Inhabited dummy `IVal V` tuple carrying explicit symbolic `FKey`s. -/
def dummyKeyIVals {V : Ty → Type} : (ts : List Ty) → Tup FKey ts → Tup (IVal V) ts
  | [], () => ()
  | _ :: ts, (k, ks) => ((.imm default, k), dummyKeyIVals ts ks)

/-- Map `ikey` across an operand tuple. -/
abbrev tupIKeys {V : Ty → Type} : {ts : List Ty} → Tup (Arg (IVal V)) ts → Tup FKey ts :=
  tupMapArg fun _ => ikey

/-- Symbolic safe operation entry mapping `(sig, ts, code, args)` to canonical `FKey` outputs. -/
structure SymOpEntry : Type where
  sig : List Ty
  ts : List Ty
  code : OpCode sig ts
  args : Tup FKey sig
  res : Tup FKey ts

/-- Symbolic pre-store load entry mapping `(lt, addr)` to canonical load slot & `FKey`. -/
structure SymLoadEntry : Type where
  slot : Nat
  lt : Ty
  addr : FKey i64
  vn : Nat

/-- Value-numbering table used during store-diamond checking across `T` and `E`. -/
structure SymTbl : Type where
  vnNext : Nat
  ops : List SymOpEntry
  loads : List SymLoadEntry

/-- Look up a matching safe op `(sig, ts, code, args)` in `ops`. -/
def findSymOp : List SymOpEntry → (sig ts : List Ty) → OpCode sig ts → Tup FKey sig →
    Option (Tup FKey ts)
  | [], _, _, _, _ => none
  | e :: es, sig, ts, code, args =>
    match listTyDecEq e.sig sig, listTyDecEq e.ts ts with
    | isTrue hs, isTrue hr =>
      let eArgs : Tup FKey sig := hs ▸ e.args
      let eCode : OpCode sig ts := hs ▸ hr ▸ e.code
      if fKeysBeq eArgs args then
        match decEq eCode code with
        | isTrue _ => some (hr ▸ e.res)
        | isFalse _ => findSymOp es sig ts code args
      else findSymOp es sig ts code args
    | _, _ => findSymOp es sig ts code args

/-- Intern a safe op into `tbl`, treating `.copy` transparently as an alias to its input key. -/
def SymTbl.internOp (tbl : SymTbl) : {sig ts : List Ty} →
    OpCode sig ts → Tup FKey sig → Tup FKey ts × SymTbl
  | _, _, .copy _, (k, ()) => ((k, ()), tbl)
  | sig, ts, code, args =>
    match findSymOp tbl.ops sig ts code args with
    | some res => (res, tbl)
    | none =>
      let res := freshFKeys ts tbl.vnNext
      let entry : SymOpEntry := ⟨sig, ts, code, args, res⟩
      (res, { tbl with vnNext := tbl.vnNext + ts.length, ops := entry :: tbl.ops })

/-- Look up a matching pre-store load `(lt, addr)` in `loads`. -/
def findSymLoad : List SymLoadEntry → (lt : Ty) → FKey i64 → Option SymLoadEntry
  | [], _, _ => none
  | e :: es, lt, addr =>
    match tyDecEq e.lt lt with
    | isTrue _ => if fKeyBeq e.addr addr then some e else findSymLoad es lt addr
    | isFalse _ => findSymLoad es lt addr

/-- Result of checking one arm of a store-sinking diamond. -/
structure StoreArmPlan : Type where
  step : StoreStep
  storeTy : Ty
  storeAddr : FKey i64
  hitSlots : List Nat

/-- Find the leftmost `.jump (.tag id lbl)` in a store-diamond arm along
`.let_`, `.load`, `.store`. -/
def findFirstJumpStore {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → Expr (IVal V) (JLabel L) rs → Option (TaggedTarget L)
  | 0, _ => none
  | _ + 1, .jump (ts := ts) (.tag id lbl) _ => some ⟨ts, id, lbl⟩
  | fuel + 1, .let_ _ k => findFirstJumpStore fuel (k (dummyIVals _ 0))
  | fuel + 1, .load _ _ k => findFirstJumpStore fuel (k (.imm default, .var 0))
  | fuel + 1, .store _ _ k => findFirstJumpStore fuel k
  | _ + 1, _ => none

/-- Check that a post-`.store` tail consists of at most `letFuel` safe `.let_`s up to `tgt`. -/
def checkStoreTail {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (tgt : ArmTarget) : Nat → Expr (IVal V) (JLabel L) rs → Option StoreTail
  | letFuel, .let_ op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 =>
        (checkStoreTail tgt letFuel' (k (dummyIVals _ 0))).map .let_
    else none
  | _, .jump (ts := ts) j _ =>
    match tgt, j with
    | .loc jId jTs, .loc id
    | .tag jId jTs, .tag id _ =>
      if id == jId && Ty.listBeq ts jTs then some .jump else none
    | _, _ => none
  | _, .ret _ =>
    match tgt with
    | .ret => some .ret
    | _ => none
  | _, _ => none

/-- Check that an arm computes pure `isSafeOp` `.let_`s and matched pre-store `.load`s leading to a
single terminal `.store` followed by `checkStoreTail`. -/
def checkStoreArm {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (tgt : ArmTarget) (allowNewLoads : Bool) :
    Nat → Nat → SymTbl → List Nat → Expr (IVal V) (JLabel L) rs →
    Option (StoreArmPlan × SymTbl)
  | letFuel, loadFuel, tbl, hits, .let_ (ts := ts) op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 =>
        let (resKeys, tbl') := tbl.internOp op.code (tupIKeys op.args)
        (checkStoreArm tgt allowNewLoads letFuel' loadFuel tbl' hits
          (k (dummyKeyIVals ts resKeys))).map fun (ap, tbl'') =>
          ({ ap with step := .let_ ap.step }, tbl'')
    else none
  | letFuel, loadFuel, tbl, hits, .load t a k =>
    let aKey := ikey a
    match findSymLoad tbl.loads t aKey with
    | some entry =>
      let hits' := if hits.contains entry.slot then hits else entry.slot :: hits
      let lv : IVal V t := (.imm default, .var entry.vn)
      (checkStoreArm tgt allowNewLoads letFuel loadFuel tbl hits' (k lv)).map
        fun (ap, tbl') => ({ ap with step := .loadReuse entry.slot ap.step }, tbl')
    | none =>
      if allowNewLoads then
        match loadFuel with
        | 0 => none
        | loadFuel' + 1 =>
          let slot := tbl.loads.length
          let vn := tbl.vnNext
          let entry : SymLoadEntry := ⟨slot, t, aKey, vn⟩
          let tbl' : SymTbl := { tbl with vnNext := vn + 1, loads := tbl.loads ++ [entry] }
          let hits' := slot :: hits
          let lv : IVal V t := (.imm default, .var vn)
          (checkStoreArm tgt allowNewLoads letFuel loadFuel' tbl' hits' (k lv)).map
            fun (ap, tbl'') => ({ ap with step := .loadEmit ap.step }, tbl'')
      else none
  | letFuel, _, tbl, hits, .store (t := st) _ a tail =>
    (checkStoreTail tgt letFuel tail).map fun tailPlan =>
      ({ step := .store tailPlan, storeTy := st, storeAddr := ikey a, hitSlots := hits }, tbl)
  | _, _, _, _, _ => none

/-- Match a common-address store-sinking diamond (RMW or pure store) across both arms of `.jnz`. -/
def checkStoreArms {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (tgt : ArmTarget) (next : Nat)
    (t e : Expr (IVal V) (JLabel L) rs) : Option StoreDiamondPlan := do
  let tbl0 : SymTbl := ⟨next, [], []⟩
  let (apT, tbl1) ← checkStoreArm tgt true 12 2 tbl0 [] t
  guard (isSelectTyWith bitsOnly apT.storeTy)
  let (apE, _) ← checkStoreArm tgt false 12 0 tbl1 [] e
  match tyDecEq apT.storeTy apE.storeTy with
  | isFalse _ => none
  | isTrue _ =>
    guard (fKeyBeq apT.storeAddr apE.storeAddr)
    let numLoads := tbl1.loads.length
    guard ((List.range numLoads).all fun s => apE.hitSlots.contains s)
    pure ⟨apT.step, apE.step, apT.storeTy, numLoads⟩

/-- Check whether `e` is a straight-line entry prefix ending in a diamond `.jnz` whose arms each
have `≤ 4` total safe `.let_`s and `≤ 2` nested `.jnz` levels jumping to `(.loc jId)` with
`select`-compatible signature `jTs`, or a common-address store-sinking diamond. -/
def checkDiamondWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (jId : Nat) (jTs : List Ty) (next : Nat) :
    Expr (IVal V) (JLabel L) rs → Option DiamondPlan
  | .let_ (ts := ts) _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + ts.length) (k (dummyIVals ts next))).map .let_
  | .load _ _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + 1) (k (.imm default, .var next))).map .load
  | .store _ _ k =>
    (checkDiamondWith bitsOnly jId jTs next k).map .store
  | .call _ (bs := bs) _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + bs.length) (k (dummyIVals bs next))).map .call
  | .jnz _ t e =>
    if isSelectSigWith bitsOnly jTs then
      match checkArm (.loc jId jTs) 2 4 next t, checkArm (.loc jId jTs) 2 4 next e with
      | some (pT, _), some (pE, _) =>
        some (.jnz pT pE)
      | _, _ => (checkStoreArms bitsOnly (.loc jId jTs) next t e).map .jnzStore
    else none
  | _ => none

/-- Default (`bitsOnly = false`) alias for `checkDiamondWith`. -/
abbrev checkDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @checkDiamondWith V L rs false

/-! ## Hoisting pure arm prefixes and emitting scalar/pair `select`s -/

/-- Recombine pair components without emitting `mkpair` when both components are immediates. -/
def mkPairIValArg {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {a b : Ty}
    (next : Nat) (x : Arg (IVal V) a) (y : Arg (IVal V) b)
    (cont : Nat → Arg (IVal V) (.pair a b) → Expr V L rs) : Expr V L rs :=
  match iout x, iout y with
  | .imm cx, .imm cy => cont next (.imm (cx, cy))
  | vx, vy =>
    .let_ (op2 (.mkpair a b) vx vy) fun (p, ()) =>
      cont (next + 1) (.var (.var p, .var next))

/-- Decompose a pair `Arg (IVal V) (.pair a b)` into component `Arg (IVal V)`s. -/
def splitPairIVal {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {a b : Ty}
    (next : Nat) (p : Arg (IVal V) (.pair a b))
    (cont : Nat → Arg (IVal V) a → Arg (IVal V) b → Expr V L rs) : Expr V L rs :=
  match iout p with
  | .imm (c₁, c₂) => cont next (Arg.imm c₁) (Arg.imm c₂)
  | .var v =>
    .let_ (op1 (.unpair a b) (.var v)) fun (v₁, v₂, ()) =>
      cont (next + 2) (Arg.var (.var v₁, .var next)) (Arg.var (.var v₂, .var (next + 1)))

/-- Emit nested `.select`s across a single non-float type `t`, producing a fresh `Arg (IVal V) t`
with key deduplication when `fKeyBeq (ikey aT) (ikey aE)`. -/
def emitSelectTyIVal {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (t : Ty) → Nat → Arg (IVal V) t → Arg (IVal V) t →
    (Nat → Arg (IVal V) t → Expr V L rs) → Expr V L rs
  | .bool, next, aT, aE, cont
  | .bits _, next, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont next aT
    else
      .let_ (op3 (.select _) c (iout aT) (iout aE)) fun (r, ()) =>
        cont (next + 1) (.var (.var r, .var next))
  | .float _, next, aT, _, cont => cont next aT
  | .pair a b, next, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont next aT
    else
      splitPairIVal next aT fun next₁ aT₁ aT₂ =>
      splitPairIVal next₁ aE fun next₂ aE₁ aE₂ =>
      emitSelectTyIVal c a next₂ aT₁ aE₁ fun next₃ r₁ =>
      emitSelectTyIVal c b next₃ aT₂ aE₂ fun next₄ r₂ =>
      mkPairIValArg next₄ r₁ r₂ cont

/-- Emit elementwise `.select`s over a tuple returning `Arg (IVal V)`s for composable nesting. -/
def emitSelectTupIVal {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (ts : List Ty) → Nat →
    Tup (Arg (IVal V)) ts → Tup (Arg (IVal V)) ts →
    (Nat → Tup (Arg (IVal V)) ts → Expr V L rs) → Expr V L rs
  | [], next, (), (), cont => cont next ()
  | t :: ts, next, (aT, asT), (aE, asE), cont =>
    emitSelectTyIVal c t next aT aE fun next' r =>
    emitSelectTupIVal c ts next' asT asE fun next'' rs' =>
    cont next'' (r, rs')

/-- Emit nested `.select`s across a single non-float type `t`, returning an `Arg V t`. -/
def emitSelectTy {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) (t : Ty) (next : Nat) (aT aE : Arg (IVal V) t)
    (cont : Nat → Arg V t → Expr V L rs) : Expr V L rs :=
  emitSelectTyIVal c t next aT aE fun next' r => cont next' (iout r)

/-- Emit elementwise `.select`s over a tuple of arguments `(argsT, argsE)`. -/
def emitSelectTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) (ts : List Ty) (next : Nat)
    (asT asE : Tup (Arg (IVal V)) ts)
    (cont : Tup (Arg V) ts → Expr V L rs) : Expr V L rs :=
  emitSelectTupIVal c ts next asT asE fun _ sel => cont (tupIOut sel)

/-- Hoist safe `.let_` instructions and bounded nested `.jnz` selects from a validated arm and
pass its final argument tuple to `cont`. -/
def hoistArm {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    ArmPlan → Nat → Expr (IVal V) (JLabel L) rs →
    (Nat → Tup (Arg (IVal V)) jTs → Expr V L rs) → Expr V L rs
  | .jump, next, .jump (ts := ts) _ args, cont =>
    match listTyDecEq ts jTs with
    | isTrue h => cont next (h ▸ args)
    | isFalse _ => .hlt
  | .ret, next, .ret vs, cont =>
    match listTyDecEq rs jTs with
    | isTrue h => cont next (h ▸ vs)
    | isFalse _ => .hlt
  | .let_ rest, next, .let_ (ts := ts) op k, cont =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistArm jTs rest (next + ts.length) (k (freshIVals ts xs next)) cont
  | .jnz pT pE, next, .jnz c t e, cont =>
    hoistArm jTs pT next t fun next₁ argsT =>
    hoistArm jTs pE next₁ e fun next₂ argsE =>
    emitSelectTupIVal (iout c) jTs next₂ argsT argsE cont
  | _, _, _, _ => .hlt

/-- Hoist two planned `.jnz` arms, emit elementwise `.select`s, and pass selected args to `fin`. -/
def hoistJnzArms {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty)
    (pT pE : ArmPlan) (next : Nat) (c : Arg (IVal V) .bool)
    (t e : Expr (IVal V) (JLabel L) rs) (fin : Tup (Arg V) jTs → Expr V L rs) : Expr V L rs :=
  hoistArm jTs pT next t fun next₁ argsT =>
  hoistArm jTs pE next₁ e fun next₂ argsE =>
  emitSelectTup (iout c) jTs next₂ argsT argsE fin

/-- Hoist a planned post-store pure tail up to `.jump` or `.ret`. -/
def hoistStoreTail {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    StoreTail → Nat → Expr (IVal V) (JLabel L) rs →
    (Nat → Tup (Arg (IVal V)) jTs → Expr V L rs) → Expr V L rs
  | .jump, next, .jump (ts := ts) _ args, cont =>
    match listTyDecEq ts jTs with
    | isTrue h => cont next (h ▸ args)
    | isFalse _ => .hlt
  | .ret, next, .ret vs, cont =>
    match listTyDecEq rs jTs with
    | isTrue h => cont next (h ▸ vs)
    | isFalse _ => .hlt
  | .let_ rest, next, .let_ (ts := ts) op k, cont =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistStoreTail jTs rest (next + ts.length) (k (freshIVals ts xs next)) cont
  | _, _, _, _ => .hlt

/-- Hoist a planned store-diamond arm prefix, emitting/reusing matched pre-store `.load`s and
extracting the final `.store` value/address plus exit arguments. -/
def hoistStoreStep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (jTs : List Ty) (st : Ty) :
    StoreStep → Nat → List ((t : Ty) × IVal V t) → Expr (IVal V) (JLabel L) rs →
    (Nat → List ((t : Ty) × IVal V t) → Arg (IVal V) st → Arg (IVal V) i64 →
      Tup (Arg (IVal V)) jTs → Expr V L rs) → Expr V L rs
  | .let_ rest, next, loads, .let_ (ts := ts) op k, cont =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistStoreStep jTs st rest (next + ts.length) loads (k (freshIVals ts xs next)) cont
  | .loadEmit rest, next, loads, .load t a k, cont =>
    .load t (iout a) fun v =>
      let iv : IVal V t := (.var v, .var next)
      hoistStoreStep jTs st rest (next + 1) (loads ++ [⟨t, iv⟩]) (k iv) cont
  | .loadReuse slot rest, next, loads, .load t _ k, cont =>
    match loads[slot]? with
    | some ⟨t', iv⟩ =>
      match tyDecEq t' t with
      | isTrue h => hoistStoreStep jTs st rest next loads (k (h ▸ iv)) cont
      | isFalse _ => .hlt
    | none => .hlt
  | .store tail, next, loads, .store (t := st') v a k, cont =>
    match tyDecEq st' st with
    | isTrue h =>
      hoistStoreTail jTs tail next k fun next' exitArgs =>
        cont next' loads (h ▸ v) a exitArgs
    | isFalse _ => .hlt
  | _, _, _, _, _ => .hlt

/-- Hoist two planned store-diamond arms, select the stored value, emit a single sunk `.store`,
and pass selected exit args to `fin`. -/
def hoistStoreArms {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty)
    (sp : StoreDiamondPlan) (next : Nat) (c : Arg (IVal V) .bool)
    (t e : Expr (IVal V) (JLabel L) rs) (fin : Tup (Arg V) jTs → Expr V L rs) : Expr V L rs :=
  hoistStoreStep jTs sp.storeTy sp.armT next [] t fun next₁ loads₁ vT aT argsT =>
  hoistStoreStep jTs sp.storeTy sp.armE next₁ loads₁ e fun next₂ _ vE _ argsE =>
  emitSelectTy (iout c) sp.storeTy next₂ vT vE fun next₃ selVal =>
  .store selVal (iout aT) (emitSelectTup (iout c) jTs next₃ argsT argsE fin)

/-- Rewrite a planned diamond entry into hoisted `.let_`s + `.select`s + `.jump jLbl`. -/
def hoistDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {jTs : List Ty}
    (jLbl : L jTs) : DiamondPlan → Nat → Expr (IVal V) (JLabel L) rs → Expr V L rs
  | .jnz pT pE, next, .jnz c t e =>
    hoistJnzArms jTs pT pE next c t e fun selArgs => .jump jLbl selArgs
  | .jnzStore sp, next, .jnz c t e =>
    hoistStoreArms jTs sp next c t e fun selArgs => .jump jLbl selArgs
  | .let_ rest, next, .let_ (ts := ts) op k =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistDiamond jLbl rest (next + ts.length) (k (freshIVals ts xs next))
  | .load rest, next, .load t a k =>
    .load t (iout a) fun v =>
      hoistDiamond jLbl rest (next + 1) (k (.var v, .var next))
  | .store rest, next, .store v a k =>
    .store (iout v) (iout a) (hoistDiamond jLbl rest next k)
  | .call rest, next, .call f (bs := bs) args k =>
    .call f (tupIOut args) fun xs =>
      hoistDiamond jLbl rest (next + bs.length) (k (freshIVals bs xs next))
  | _, _, _ => .hlt

/-- Attempt pure arbitrary-position `.jnz` diamond if-conversion. -/
def tryPureJnzDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (next : Nat) (c : Arg (IVal V) .bool)
    (t e : Expr (IVal V) (JLabel L) rs) : Option (Expr V L rs) :=
  match findFirstJump 8 t with
  | some ⟨jTs, jId, jLbl⟩ =>
    if isSelectSigWith bitsOnly jTs then
      match checkArm (.tag jId jTs) 2 4 next t, checkArm (.tag jId jTs) 2 4 next e with
      | some (pT, _), some (pE, _) =>
        some (hoistJnzArms jTs pT pE next c t e fun selArgs => .jump jLbl selArgs)
      | _, _ => none
    else none
  | none =>
    if isSelectSigWith bitsOnly rs then
      match checkArm .ret 2 4 next t, checkArm .ret 2 4 next e with
      | some (pT, _), some (pE, _) =>
        some (hoistJnzArms rs pT pE next c t e fun selArgs => .ret selArgs)
      | _, _ => none
    else none

/-- Attempt common-address store-sinking `.jnz` diamond if-conversion. -/
def tryStoreJnzDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (next : Nat) (c : Arg (IVal V) .bool)
    (t e : Expr (IVal V) (JLabel L) rs) : Option (Expr V L rs) :=
  match findFirstJumpStore 16 t with
  | some ⟨jTs, jId, jLbl⟩ =>
    if isSelectSigWith bitsOnly jTs then
      (checkStoreArms bitsOnly (.tag jId jTs) next t e).map fun sp =>
        hoistStoreArms jTs sp next c t e fun selArgs => .jump jLbl selArgs
    else none
  | none =>
    if isSelectSigWith bitsOnly rs then
      (checkStoreArms bitsOnly .ret next t e).map fun sp =>
        hoistStoreArms rs sp next c t e fun selArgs => .ret selArgs
    else none

/-- Attempt arbitrary-position `.jnz` diamond if-conversion at `.jnz c t e` targeting either a
tagged `.group` label or `.ret` (pure arms or common-address store-sinking diamond). -/
def tryJnzDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (next : Nat) (c : Arg (IVal V) .bool)
    (t e : Expr (IVal V) (JLabel L) rs) : Option (Expr V L rs) :=
  match tryPureJnzDiamond bitsOnly next c t e with
  | some r => some r
  | none => tryStoreJnzDiamond bitsOnly next c t e

/-! ## Pure integer compare sinking (`cmpSink`) next to `.select` consumers -/

/-- Deferred pure integer `.bits` comparison awaiting materialization right before its
`.select` consumer. -/
structure DeferCmp (V : Ty → Type) where
  id : Nat
  n : Nat
  co : CmpOp
  lhs : Arg V (.bits n)
  rhs : Arg V (.bits n)

/-- Variable representation in `cmpSink`: either a regular bound operand tagged with a unique
binder `id`, or a deferred `.bits` comparison (of type `.bool`). -/
inductive SVal (V : Ty → Type) : Ty → Type
  | val {t : Ty} (a : Arg V t) (id : Nat) : SVal V t
  | defer (d : DeferCmp V) : SVal V .bool

/-- Unique binder identifier of an `SVal`. -/
def svalId {V : Ty → Type} {t : Ty} : SVal V t → Nat
  | .val _ id => id
  | .defer d => d.id

/-- True iff `a` is a variable with binder identifier `cid`. -/
def sargIsId {V : Ty → Type} {t : Ty} (cid : Nat) : Arg (SVal V) t → Bool
  | .var sv => svalId sv == cid
  | .imm _ => false

/-- True iff any argument in `args` is a variable with binder identifier `cid`. -/
def sargsHasId {V : Ty → Type} (cid : Nat) : {ts : List Ty} → Tup (Arg (SVal V)) ts → Bool
  | [], () => false
  | _ :: _, (a, as) => sargIsId cid a || sargsHasId cid as

/-- Wrap bound output variables `xs` into fresh `SVal V`s starting at `next`. -/
def freshSVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (SVal V) ts
  | [], (), _ => ()
  | _ :: ts, (x, xs), next => (.val (.var x) next, freshSVals ts xs (next + 1))

/-- Inhabited dummy `SVal V` tuple for straight-line lookahead (never emitted). -/
def dummySVals {V : Ty → Type} : (ts : List Ty) → Nat → Tup (SVal V) ts
  | [], _ => ()
  | _ :: ts, next => (.val (.imm default) next, dummySVals ts (next + 1))

/-- Extract the underlying `Arg V (.bits n)` from `Arg (SVal V) (.bits n)`. -/
def soutBits {V : Ty → Type} {n : Nat} : Arg (SVal V) (.bits n) → Arg V (.bits n)
  | .imm c => .imm c
  | .var (.val a _) => a

/-- True iff `code` clobbers CPU condition flags on both x86-64 and Arm64 (another compare,
carry arithmetic, or an intervening `.select`). -/
def isCmpClobberOp {sig rs : List Ty} : OpCode sig rs → Bool
  | .cmp _ _ _ _ | .addc _ | .subb _ | .select _ => true
  | _ => false

/-- Non-recursive `.let_` step for `shouldDeferCmp`. -/
def shouldDeferCmpStep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (cid : Nat) (sawClobber : Bool) (next : Nat)
    (rec : Bool → Nat → Expr (SVal V) L rs → Bool) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg (SVal V)) sig →
    (Tup (SVal V) ts → Expr (SVal V) L rs) → Bool
  | _, _, .select u, (cond, aT, aE, ()), k =>
    if sargIsId cid cond && !sargIsId cid aT && !sargIsId cid aE then
      sawClobber
    else if sargIsId cid cond || sargIsId cid aT || sargIsId cid aE then
      false
    else
      rec true (next + 1) (k (dummySVals [u] next))
  | _, ts, code, args, k =>
    if sargsHasId cid args then false
    else
      rec (sawClobber || isCmpClobberOp code) (next + ts.length) (k (dummySVals ts next))

/-- Straight-line `.let_` lookahead: true iff `.bool` binder `cid` is first consumed as the
condition of a `.select` (not as its value operands) after at least one flag-clobbering op
within `fuel` `.let_` bindings. -/
def shouldDeferCmp {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (cid : Nat) : Nat → Bool → Nat → Expr (SVal V) L rs → Bool
  | 0, _, _, _ => false
  | fuel + 1, sawClobber, next, .let_ ⟨code, args⟩ k =>
    shouldDeferCmpStep cid sawClobber next (shouldDeferCmp cid fuel) code args k
  | _ + 1, _, _, _ => false

/-- Look up an already-materialized deferred comparison by binder `id`. -/
def lookupMat {V : Ty → Type} (id : Nat) : List (Nat × V .bool) → Option (V .bool)
  | [] => none
  | (k, v) :: rest => if k == id then some v else lookupMat id rest

/-- Materialize `a : Arg (SVal V) t`, emitting a deferred `.cmp` once on first use. -/
def matArg {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mat : List (Nat × V .bool)) : {t : Ty} → Arg (SVal V) t →
    (List (Nat × V .bool) → Arg V t → Expr V L rs) → Expr V L rs
  | _, .imm c, cont => cont mat (.imm c)
  | _, .var (.val a _), cont => cont mat a
  | .bool, .var (.defer d), cont =>
    match lookupMat d.id mat with
    | some v => cont mat (.var v)
    | none =>
      .let_ (op2 (.cmp d.co (.bits d.n) .bool rfl) d.lhs d.rhs) fun (v, ()) =>
        cont ((d.id, v) :: mat) (.var v)

/-- Materialize a tuple of `Arg (SVal V)` operands left-to-right. -/
def matArgs {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mat : List (Nat × V .bool)) : {ts : List Ty} → Tup (Arg (SVal V)) ts →
    (List (Nat × V .bool) → Tup (Arg V) ts → Expr V L rs) → Expr V L rs
  | [], (), cont => cont mat ()
  | _ :: _, (a, as), cont =>
    matArg mat a fun mat' a' =>
    matArgs mat' as fun mat'' as' =>
    cont mat'' (a', as')

end IfOptImpl

open IfOptImpl

mutual
/-- PHOAS straight-line pure `.bits` compare sinking: defers `.cmp` ops whose first use is a
`.select` condition past intervening flag-clobbering ops, materializing them directly before
that `.select`. -/
def cmpSink {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (mat : List (Nat × V .bool)) : Expr (SVal V) L rs → Expr V L rs
  | .let_ (ts := ts) ⟨code, args⟩ k =>
    match code, args, k with
    | .cmp co t m h, args, k =>
      match t, m, h, args, k with
      | .bits n, .bool, _, (a, b, ()), k =>
        if shouldDeferCmp next 16 false (next + 1) (k (.val (.imm default) next, ())) then
          let d : DeferCmp V := ⟨next, n, co, soutBits a, soutBits b⟩
          cmpSink (next + 1) mat (k (.defer d, ()))
        else
          .let_ (op2 (.cmp co (.bits n) .bool rfl) (soutBits a) (soutBits b)) fun (v, ()) =>
            cmpSink (next + 1) mat (k (.val (.var v) next, ()))
      | .bool, m, h, args, k =>
        matArgs mat args fun mat' args' =>
          .let_ ⟨.cmp co .bool m h, args'⟩ fun xs =>
            cmpSink (next + 1) mat' (k (freshSVals [m] xs next))
      | .float f, m, h, args, k =>
        matArgs mat args fun mat' args' =>
          .let_ ⟨.cmp co (.float f) m h, args'⟩ fun xs =>
            cmpSink (next + 1) mat' (k (freshSVals [m] xs next))
      | .pair x y, m, h, args, k =>
        matArgs mat args fun mat' args' =>
          .let_ ⟨.cmp co (.pair x y) m h, args'⟩ fun xs =>
            cmpSink (next + 1) mat' (k (freshSVals [m] xs next))
    | code, args, k =>
      matArgs mat args fun mat' args' =>
        .let_ ⟨code, args'⟩ fun xs =>
          cmpSink (next + ts.length) mat' (k (freshSVals ts xs next))
  | .load t a k =>
    matArg mat a fun mat' a' =>
      .load t a' fun v => cmpSink (next + 1) mat' (k (.val (.var v) next))
  | .store v a k =>
    matArg mat v fun mat₁ v' =>
    matArg mat₁ a fun mat₂ a' =>
      .store v' a' (cmpSink next mat₂ k)
  | .call f (bs := bs) args k =>
    matArgs mat args fun mat' args' =>
      .call f args' fun xs => cmpSink (next + bs.length) mat' (k (freshSVals bs xs next))
  | .jnz c t e =>
    matArg mat c fun mat' c' =>
      .jnz c' (cmpSink next mat' t) (cmpSink next mat' e)
  | .jump j args =>
    matArgs mat args fun _ args' => .jump j args'
  | .ret vs =>
    matArgs mat vs fun _ vs' => .ret vs'
  | .exit f args =>
    matArgs mat args fun _ args' => .exit f args'
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => cmpSinkB next mat (bodies Js))
           (fun Js => cmpSink next mat (k Js))

/-- Block-list companion of `cmpSink`. -/
def cmpSinkB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (mat : List (Nat × V .bool)) :
    {sig : List (List Ty)} → Blocks (SVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => cmpSink (next + ts.length) mat (b (freshSVals ts xs next)))
      (cmpSinkB next mat bs)
end

/-- Closed-function pure `.bits` compare sinking next to `.select` consumers. -/
def Func.cmpSink {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => _root_.LeanQbe.T.cmpSink as.length [] (f (SVal V) L (freshSVals as xs 0))

mutual
/-- PHOAS-to-PHOAS if-conversion pass (diamond `jnz` → `select`), preserving `.group`
block structure. When `bitsOnly = true`, only `.bits` (`8/16/32/64`) join values are converted,
and diamonds at arbitrary AST positions (`.group` targets and `.ret`) are converted. -/
def ifOptWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) : Expr (IVal V) (JLabel L) rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      ifOptWith bitsOnly depth (next + ts.length) (k (freshIVals ts xs next))
  | .load t a k =>
    .load t (iout a) fun v => ifOptWith bitsOnly depth (next + 1) (k (.var v, .var next))
  | .store v a k =>
    .store (iout v) (iout a) (ifOptWith bitsOnly depth next k)
  | .call f (bs := bs) args k =>
    .call f (tupIOut args) fun xs =>
      ifOptWith bitsOnly depth (next + bs.length) (k (freshIVals bs xs next))
  | .jnz c t e =>
    let fallback :=
      .jnz (iout c) (ifOptWith bitsOnly depth next t) (ifOptWith bitsOnly depth next e)
    if bitsOnly then (tryJnzDiamond bitsOnly next c t e).getD fallback else fallback
  | .jump j args =>
    match unwrapJLabel j with
    | some l => .jump l (tupIOut args)
    | none => .hlt
  | .ret vs => .ret (tupIOut vs)
  | .exit f args => .exit f (tupIOut args)
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    if bitsOnly then
      .group
        (fun Js => ifOptBWith true (depth + sig.length) next (bodies (tagLabels depth Js)))
        (fun Js => ifOptWith true (depth + sig.length) next (k (tagLabels depth Js)))
    else
      match sig with
      | [] =>
        .group
          (fun Js => ifOptBWith false depth next (bodies (Js.map fun _ l => .outer l)))
          (fun Js => ifOptWith false depth next (k (Js.map fun _ l => .outer l)))
      | [ts] =>
        let plan? := checkDiamondWith false depth ts next (k (.loc depth, ()))
        .group (sig := [ts])
          (fun Js => ifOptBWith false (depth + 1) next (bodies (Js.map fun _ l => .outer l)))
          (fun Js =>
            match plan? with
            | some plan => hoistDiamond Js.1 plan next (k (.outer Js.1, ()))
            | none => ifOptWith false (depth + 1) next (k (.outer Js.1, ())))
      | _ :: _ :: rest =>
        .group
          (fun Js =>
            ifOptBWith false (depth + rest.length + 2) next
              (bodies (Js.map fun _ l => .outer l)))
          (fun Js =>
            ifOptWith false (depth + rest.length + 2) next (k (Js.map fun _ l => .outer l)))

/-- Block-list companion of `ifOptWith`. -/
def ifOptBWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) : {sig : List (List Ty)} →
    Blocks (IVal V) (JLabel L) rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => ifOptWith bitsOnly depth (next + ts.length) (b (freshIVals ts xs next)))
      (ifOptBWith bitsOnly depth next bs)
end

/-- Default (`bitsOnly = false`) alias for `ifOptWith`. -/
abbrev ifOpt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @ifOptWith V L rs false

/-- Default (`bitsOnly = false`) alias for `ifOptBWith`. -/
abbrev ifOptB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @ifOptBWith V L rs false

/-- Core if-conversion pass without post-conversion compare sinking. -/
def Func.ifOptCore (bitsOnly : Bool) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs =>
    _root_.LeanQbe.T.ifOptWith bitsOnly 0 as.length (f (IVal V) (JLabel L) (freshIVals as xs 0))

/-- Convert eligible diamond `jnz` patterns into `.select`s on a closed typed function `Func`
(followed by pure `.bits` compare sinking `Func.cmpSink` when `bitsOnly = true`). -/
def Func.ifOptWith (bitsOnly : Bool) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  if bitsOnly then Func.cmpSink (Func.ifOptCore true f)
  else Func.ifOptCore false f

/-- Pre-`Legal` if-conversion allowing `.bool`/`.bits`/`.pair` select values. -/
abbrev Func.ifOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.ifOptWith false f

/-- Post-`Legal` if-conversion restricted to machine `.bits` (`8/16/32/64`) select values. -/
def Func.ifOptBits {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.ifOptWith true f

end LeanQbe.T
