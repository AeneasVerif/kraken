module

public import LeanQbe.T.Flat
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.Trie
public import LeanQbe.T.MemLoad
public import LeanQbe.T.AssumeBits
public import LeanQbe.T.DivConst

/-!
# First-Order `Trie`-Env Memory & Known-Bits Passes (`OptFlatMem`)

Native `Trie`-env `TFlat → TFlat` implementations matching `Func.memLoad`, `Func.assumeBits`,
and full `Func.divConst` (`memLoadFlat`, `assumeBitsFlat`, `divConstFlat`) without intermediate
PHOAS closures or de Bruijn index shifting:

* `OptFlatMem.memLoadFlat`: two-pass `TFlat` lexical load CSE and store-to-load forwarding
  (`analyzeMemFlat` + `memLoadSweepFlat`).
* `OptFlatMem.assumeBitsFlat`: `TFlat` known-bits and branch-implied simplification reusing
  `Op.abLet` / `ABVal`.
* `OptFlatMem.divConstFlat`: `O(N)` `hasDivRem` fast-path + full `TFlat` constant
  division/remainder lowering (`emit{U,S}{Div,Rem}ConstPlan`) supporting `d = 1`, power-of-two
  shifts, and Granlund-Montgomery certificates.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatMem

open OptFlatPlanKit

/-- Resolve a `TFlat` operand `Arg K t` directly into a lowered `Arg K t` output level. -/
def resolveFlatArg (inDepth : Nat) (env : Trie ((t : Ty) × Arg K t)) {t : Ty} :
    Arg K t → Arg K t
  | .imm c => .imm c
  | .var idx =>
    match lookupEnv inDepth env t idx with
    | some a => a
    | none => .var 0

/-- Resolve a tuple of `TFlat` operands directly into `Tup (Arg K) ts`. -/
def resolveFlatArgs (inDepth : Nat) (env : Trie ((t : Ty) × Arg K t)) :
    {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (resolveFlatArg inDepth env a, resolveFlatArgs inDepth env as)

/-! ## 1. Native `TFlat` `memLoadFlat` (Phase 1 `analyzeMemFlat` + Phase 2 `memLoadSweepFlat`) -/

/-- Convert a de Bruijn index operand at depth `next` into its `FKey` level. -/
abbrev lvlArg (next : Nat) {t : Ty} : Arg K t → FKey t := levelArg next

/-- Convert a tuple of de Bruijn index operands at depth `next` into `FKey` levels. -/
abbrev lvlArgs (next : Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup FKey ts := levelArgs next

mutual
/-- Phase 1 of `memLoadFlat`: compute conservative `MemSumTree` directly over `TFlat`. -/
def analyzeMemFlat {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap) :
    TFlat rs → MemSummary × Trie Unit × MemSumTree
  | .let_ (ts := ts) op k =>
    let baseOff' := stepBaseOff next baseOff op.code (lvlArgs next op.args)
    let (s, l, kt) := analyzeMemFlat (next + ts.length) nl baseOff' k
    (s, l, .node1 kt)
  | .load _ _ k =>
    let (s, l, kt) := analyzeMemFlat (next + 1) nl baseOff k
    (s, l, .node1 kt)
  | .store (t := t) _ a k =>
    let ak := resolveKey baseOff (lvlArg next a)
    let (s, l, kt) := analyzeMemFlat next nl baseOff k
    (MemSummary.addWrite ⟨ak, t.bytes⟩ s, l, .node1 kt)
  | .call _ bs _ k =>
    let (_, l, kt) := analyzeMemFlat (next + bs.length) nl baseOff k
    (.unknown, l, .node1 kt)
  | .jnz _ t e =>
    let (st, lt, ktt) := analyzeMemFlat next nl baseOff t
    let (se, le, kte) := analyzeMemFlat next nl baseOff e
    (st.join se, trieUnion lt le, .node2 ktt kte)
  | .jump j _ => (.empty, (Trie.empty).insert (nl - 1 - j) (), .leaf)
  | .ret _ | .exit _ _ | .hlt => (.empty, .empty, .leaf)
  | .group (sig := sig) bodies k =>
    let nl' := nl + sig.length
    let (sb, lb, bs) := analyzeMemBFlat next nl' baseOff bodies
    let (sk, lk, kt) := analyzeMemFlat next nl' baseOff k
    let sum := sb.join sk
    let sumB := if anyLive nl sig.length lb then sum else sk
    (sum, trieUnion lb lk, .groupNode sumB bs kt)

/-- Block-list companion of `analyzeMemFlat`. -/
def analyzeMemBFlat {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap) :
    {sig : List (List Ty)} → TBlocks rs sig → MemSummary × Trie Unit × MemSumBlocks
  | _, .nil => (.empty, .empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, lh, kh) := analyzeMemFlat (next + ts.length) nl baseOff hd
    let (st, lt, kt) := analyzeMemBFlat next nl baseOff tl
    (sh.join st, trieUnion lh lt, .cons kh kt)
end

/-- Resolve a `TFlat` operand to its `(out, key)` pair in `MVal K`. -/
def resolveMVal (inDepth : Nat) (env : Trie ((t : Ty) × MVal K t)) {t : Ty} :
    Arg K t → MVal K t
  | .imm c => ⟨.imm c, .imm c⟩
  | .var idx =>
    match lookupEnv inDepth env t idx with
    | some m => m
    | none => ⟨.var 0, .var 0⟩

/-- Resolve and re-index `TFlat` output operands directly at `outDepth`. -/
def resolveMOuts (inDepth outDepth : Nat) (env : Trie ((t : Ty) × MVal K t)) :
    {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) =>
    (idxArg outDepth (resolveMVal inDepth env a).out, resolveMOuts inDepth outDepth env as)

/-- Extract symbolic `FKey`s across a tuple of `TFlat` operands. -/
def resolveMKeys (inDepth : Nat) (env : Trie ((t : Ty) × MVal K t)) :
    {ts : List Ty} → Tup (Arg K) ts → Tup FKey ts
  | [], () => ()
  | _ :: _, (a, as) =>
    ((resolveMVal inDepth env a).key, resolveMKeys inDepth env as)

mutual
/-- Phase 2 of `memLoadFlat`: direct `TFlat` load-CSE and store-to-load forwarding sweep. -/
def memLoadSweepFlat {rs : List Ty} (inDepth outDepth : Nat) (baseOff : BaseOffMap)
    (cache : List (CacheEntry K)) (mst : MemSumTree) :
    TFlat rs → Trie ((t : Ty) × MVal K t) → TFlat rs
  | .let_ (ts := ts) op k, inEnv =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let baseOff' := stepBaseOff inDepth baseOff op.code (resolveMKeys inDepth inEnv op.args)
    let outs := resolveMOuts inDepth outDepth inEnv op.args
    let inEnv' := insertFreshWith (fun _ inD outD => MVal.fresh outD inD)
      inDepth outDepth ts inEnv
    .let_ ⟨op.code, outs⟩
      (memLoadSweepFlat (inDepth + ts.length) (outDepth + ts.length) baseOff' cache kt k inEnv')
  | .load t a k, inEnv =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let ma := resolveMVal inDepth inEnv a
    let ak := resolveKey baseOff ma.key
    match lookupCache ak t cache with
    | some cached =>
      let inEnv' := inEnv.insert inDepth ⟨t, cached⟩
      memLoadSweepFlat (inDepth + 1) outDepth baseOff cache kt k inEnv'
    | none =>
      let cache' := ⟨ak, t, .var outDepth, .var inDepth⟩ :: cache
      let inEnv' := inEnv.insert inDepth ⟨t, MVal.fresh outDepth inDepth⟩
      .load t (idxArg outDepth ma.out)
        (memLoadSweepFlat (inDepth + 1) (outDepth + 1) baseOff cache' kt k inEnv')
  | .store (t := t) v a k, inEnv =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let mv := resolveMVal inDepth inEnv v
    let ma := resolveMVal inDepth inEnv a
    let ak := resolveKey baseOff ma.key
    let cache' := filterCacheWrite ak t.bytes cache
    let cache'' :=
      if t.bytes ≤ 2 ^ 64 then ⟨ak, t, mv.out, mv.key⟩ :: cache'
      else cache'
    .store (idxArg outDepth mv.out) (idxArg outDepth ma.out)
      (memLoadSweepFlat inDepth outDepth baseOff cache'' kt k inEnv)
  | .call f bs args k, inEnv =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let outs := resolveMOuts inDepth outDepth inEnv args
    let inEnv' := insertFreshWith (fun _ inD outD => MVal.fresh outD inD)
      inDepth outDepth bs inEnv
    .call f bs outs
      (memLoadSweepFlat (inDepth + bs.length) (outDepth + bs.length) baseOff [] kt k inEnv')
  | .jnz c t e, inEnv =>
    let (ktt, kte) := match mst with | .node2 ktt kte => (ktt, kte) | _ => (.leaf, .leaf)
    let mc := resolveMVal inDepth inEnv c
    .jnz (idxArg outDepth mc.out)
      (memLoadSweepFlat inDepth outDepth baseOff cache ktt t inEnv)
      (memLoadSweepFlat inDepth outDepth baseOff cache kte e inEnv)
  | .jump j args, inEnv => .jump j (resolveMOuts inDepth outDepth inEnv args)
  | .ret vs, inEnv => .ret (resolveMOuts inDepth outDepth inEnv vs)
  | .exit f args, inEnv => .exit f (resolveMOuts inDepth outDepth inEnv args)
  | .hlt, _ => .hlt
  | .group bodies k, inEnv =>
    let (sum, bsMST, kMST) := match mst with
      | .groupNode sum bsMST kMST => (sum, bsMST, kMST)
      | _ => (.unknown, .nil, .leaf)
    let cacheB := filterCacheSummary sum cache
    .group
      (memLoadSweepBFlat inDepth outDepth baseOff cacheB bsMST bodies inEnv)
      (memLoadSweepFlat inDepth outDepth baseOff cache kMST k inEnv)

/-- Block-list companion of `memLoadSweepFlat`. -/
def memLoadSweepBFlat {rs : List Ty} (inDepth outDepth : Nat) (baseOff : BaseOffMap)
    (cache : List (CacheEntry K)) (bsMST : MemSumBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig → Trie ((t : Ty) × MVal K t) → TBlocks rs sig
  | _, .nil, _ => .nil
  | _, .cons (ts := ts) b bs, inEnv =>
    let (kh, kt) := match bsMST with | .cons kh kt => (kh, kt) | _ => (.leaf, .nil)
    let inEnv' := insertFreshWith (fun _ inD outD => MVal.fresh outD inD)
      inDepth outDepth ts inEnv
    .cons
      (memLoadSweepFlat (inDepth + ts.length) (outDepth + ts.length) baseOff cache kh b inEnv')
      (memLoadSweepBFlat inDepth outDepth baseOff cache kt bs inEnv)
end

/-- Native `TFlat` lexical load CSE and store-to-load forwarding pass. -/
def memLoadFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let mst := (analyzeMemFlat as.length 0 .empty tf).2.2
  let initEnv := insertFreshWith (fun _ inD outD => MVal.fresh outD inD) 0 0 as .empty
  memLoadSweepFlat as.length as.length .empty [] mst tf initEnv

/-! ## 2. Native `TFlat` `assumeBitsFlat` -/

/-- Resolve a `TFlat` operand into `Arg (ABVal K) t`. -/
def resolveABArg (inDepth : Nat) (env : Trie ((t : Ty) × ABVal K t)) {t : Ty}
    (a : Arg K t) : Arg (ABVal K) t :=
  resolveEnvArg inDepth env a (fun _ => .var ⟨.var 0, {}⟩)

/-- Resolve a tuple of `TFlat` operands into `Tup (Arg (ABVal K)) ts`. -/
def resolveABArgs (inDepth : Nat) (env : Trie ((t : Ty) × ABVal K t)) {ts : List Ty}
    (args : Tup (Arg K) ts) : Tup (Arg (ABVal K)) ts :=
  resolveEnvArgs inDepth env args (fun _ => .var ⟨.var 0, {}⟩)

/-- Resolve and re-index `assumeBits` output operands directly at `outDepth`. -/
def resolveAOuts (inDepth outDepth : Nat) (env : Trie ((t : Ty) × ABVal K t)) :
    {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) =>
    (idxArg outDepth (resolveABArg inDepth env a).abOut, resolveAOuts inDepth outDepth env as)

mutual
/-- Direct `TFlat` known-bits and branch-implied simplification sweep. -/
def assumeBitsGo {rs : List Ty} (inDepth outDepth : Nat) (F : List BitFact) :
    TFlat rs → Trie ((t : Ty) × ABVal K t) → TFlat rs
  | .let_ (ts := ts) op k, inEnv =>
    let abArgs := resolveABArgs inDepth inEnv op.args
    match ({ code := op.code, args := abArgs } : Op (ABVal K) ts).abLet F outDepth with
    | .elim res =>
      assumeBitsGo (inDepth + ts.length) outDepth F k (insertTupEnv inDepth inEnv res)
    | .emit op' wrap =>
      let res := wrap (Tup.levels ts outDepth)
      .let_ ⟨op'.code, idxArgs outDepth op'.args⟩
        (assumeBitsGo (inDepth + ts.length) (outDepth + ts.length) F k
          (insertTupEnv inDepth inEnv res))
  | .load t a k, inEnv =>
    let a' := resolveABArg inDepth inEnv a
    let inEnv' := inEnv.insert inDepth ⟨t, ABVal.fresh outDepth outDepth⟩
    .load t (idxArg outDepth a'.abOut)
      (assumeBitsGo (inDepth + 1) (outDepth + 1) F k inEnv')
  | .store v a k, inEnv =>
    let v' := resolveABArg inDepth inEnv v
    let a' := resolveABArg inDepth inEnv a
    .store (idxArg outDepth v'.abOut) (idxArg outDepth a'.abOut)
      (assumeBitsGo inDepth outDepth F k inEnv)
  | .call f bs args k, inEnv =>
    let outs := resolveAOuts inDepth outDepth inEnv args
    let inEnv' := insertFreshWith (fun _ _ outD => ABVal.fresh outD outD)
      inDepth outDepth bs inEnv
    .call f bs outs (assumeBitsGo (inDepth + bs.length) (outDepth + bs.length) F k inEnv')
  | .jnz c t e, inEnv =>
    let c' := resolveABArg inDepth inEnv c
    .jnz (idxArg outDepth c'.abOut)
      (assumeBitsGo inDepth outDepth (c'.abInfo.nf ++ F) t inEnv)
      (assumeBitsGo inDepth outDepth (c'.abInfo.zf ++ F) e inEnv)
  | .jump j args, inEnv => .jump j (resolveAOuts inDepth outDepth inEnv args)
  | .ret vs, inEnv => .ret (resolveAOuts inDepth outDepth inEnv vs)
  | .exit f args, inEnv => .exit f (resolveAOuts inDepth outDepth inEnv args)
  | .hlt, _ => .hlt
  | .group bodies k, inEnv =>
    .group (assumeBitsBGo inDepth outDepth F bodies inEnv)
      (assumeBitsGo inDepth outDepth F k inEnv)

/-- Block-list companion of `assumeBitsGo`. -/
def assumeBitsBGo {rs : List Ty} (inDepth outDepth : Nat) (F : List BitFact) :
    {sig : List (List Ty)} → TBlocks rs sig → Trie ((t : Ty) × ABVal K t) → TBlocks rs sig
  | _, .nil, _ => .nil
  | _, .cons (ts := ts) b bs, inEnv =>
    let inEnv' := insertFreshWith (fun _ _ outD => ABVal.fresh outD outD)
      inDepth outDepth ts inEnv
    .cons (assumeBitsGo (inDepth + ts.length) (outDepth + ts.length) F b inEnv')
      (assumeBitsBGo inDepth outDepth F bs inEnv)
end

/-- Native `TFlat` known-bits and branch-implied simplification pass. -/
def assumeBitsFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let initEnv := insertFreshWith (fun _ _ outD => ABVal.fresh outD outD) 0 0 as .empty
  assumeBitsGo as.length as.length [] tf initEnv

/-! ## 3. Native `TFlat` `divConstFlat` (Fast-Path + Full `divConstGo`) -/

/-- True iff `c` is a UB division/remainder opcode (`udiv`/`urem`/`sdiv`/`srem`). -/
def opCodeIsDivRem : {as ts : List Ty} → OpCode as ts → Bool
  | _, _, .udiv _ | _, _, .urem _ | _, _, .sdiv _ | _, _, .srem _ => true
  | _, _, _ => false

mutual
/-- True iff `tf` contains any `udiv`/`urem`/`sdiv`/`srem` operation. -/
def hasDivRem {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => opCodeIsDivRem op.code || hasDivRem k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => hasDivRem k
  | .jnz _ t e => hasDivRem t || hasDivRem e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => false
  | .group bodies k => hasDivRemB bodies || hasDivRem k

/-- Block-list companion of `hasDivRem`. -/
def hasDivRemB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasDivRem b || hasDivRemB bs
end

/-- Emitted `TFlat` instruction sequence producing a single `.bits n` result. -/
structure DivEmit (n : Nat) : Type where
  outDepth : Nat
  res : Arg K (.bits n)
  wrap : {rs : List Ty} → TFlat rs → TFlat rs

/-- Emitted `TFlat` instruction sequence producing an arbitrary result tuple. -/
structure DivPlan (ts : List Ty) : Type where
  outDepth : Nat
  res : Tup (Arg K) ts
  wrap : {rs : List Ty} → TFlat rs → TFlat rs

/-- Sequence one `DivEmit n` with a continuation producing the next `DivEmit n`. -/
def DivEmit.seq {n : Nat} (p : DivEmit n) (f : Nat → Arg K (.bits n) → DivEmit n) : DivEmit n :=
  let q := f p.outDepth p.res
  ⟨q.outDepth, q.res, fun tail => p.wrap (q.wrap tail)⟩

/-- Emit a 2-operand `OpCode [.bits n, .bits n] [.bits n]` instruction at `outD`. -/
def emitOp2E (outD : Nat) {n : Nat} (code : OpCode [.bits n, .bits n] [.bits n])
    (x y : Arg K (.bits n)) : DivEmit n :=
  ⟨outD + 1, .var outD, fun tail => .let_ (op2 code (idxArg outD x) (idxArg outD y)) tail⟩

/-- Emit a widening multiply instruction returning its upper half at `outD + 1`. -/
def emitMulwE (outD : Nat) (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n, .bits n])
    (x y : Arg K (.bits n)) : DivEmit n :=
  ⟨outD + 2, .var (outD + 1),
    fun tail => .let_ (op2 code (idxArg outD x) (idxArg outD y)) tail⟩

/-- Plan certified constant unsigned division directly as `TFlat` wrappers. -/
def emitUDivConstPlan (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD : Nat) :
    Option (DivEmit n) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n then none
  else if d == 1#n then some ⟨outD, x, fun tail => tail⟩
  else
    match findPow2Shift n d with
    | some m =>
      if pow2ShiftCert n d m then
        some (emitOp2E outD (.lshr (.bits n)) x (.imm (BitVec.ofNat n m)))
      else none
    | none =>
      match findUMagic n d with
      | some (M, s, false) =>
        if uNoAddCert n d M s then
          some <|
            (emitMulwE outD n (.umulw n) x (.imm (BitVec.ofNat n M))).seq fun d1 hi =>
            emitOp2E d1 (.lshr (.bits n)) hi (.imm (BitVec.ofNat n s))
        else none
      | some (M, s, true) =>
        if uAddShiftCert n d M s then
          some <|
            (emitMulwE outD n (.umulw n) x (.imm (BitVec.ofNat n (M - 2 ^ n)))).seq fun d1 hi =>
            (emitOp2E d1 (.sub (.bits n)) x hi).seq fun d2 t1 =>
            (emitOp2E d2 (.lshr (.bits n)) t1 (.imm 1#n)).seq fun d3 t2 =>
            (emitOp2E d3 (.add (.bits n)) hi t2).seq fun d4 t3 =>
            emitOp2E d4 (.lshr (.bits n)) t3 (.imm (BitVec.ofNat n (s - 1)))
        else none
      | none => none

/-- Plan certified constant unsigned remainder directly as `TFlat` wrappers. -/
def emitURemConstPlan (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD : Nat) :
    Option (DivEmit n) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n then none
  else if d == 1#n then some ⟨outD, .imm 0#n, fun tail => tail⟩
  else
    match findPow2Shift n d with
    | some m =>
      if pow2ShiftCert n d m then
        some (emitOp2E outD (.and (.bits n)) x (.imm (BitVec.twoPow n m - 1#n)))
      else none
    | none =>
      (emitUDivConstPlan n x d outD).map fun p =>
        p.seq fun d1 q =>
        (emitOp2E d1 (.mul (.bits n)) q (.imm d)).seq fun d2 prod =>
        emitOp2E d2 (.sub (.bits n)) x prod

/-- Plan certified constant signed division directly as `TFlat` wrappers. -/
def emitSDivConstPlan (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD : Nat) :
    Option (DivEmit n) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n || d == BitVec.allOnes n then none
  else if d == 1#n then some ⟨outD, x, fun tail => tail⟩
  else
    match findSPow2Shift n d with
    | some m =>
      if sPow2Cert n d m then
        if m == 1 then
          some <|
            (emitOp2E outD (.lshr (.bits n)) x (.imm (BitVec.ofNat n (n - 1)))).seq fun d1 t1 =>
            (emitOp2E d1 (.add (.bits n)) x t1).seq fun d2 t2 =>
            emitOp2E d2 (.ashr (.bits n)) t2 (.imm 1#n)
        else
          some <|
            (emitOp2E outD (.ashr (.bits n)) x (.imm (BitVec.ofNat n (n - 1)))).seq fun d1 t1 =>
            (emitOp2E d1 (.lshr (.bits n)) t1 (.imm (BitVec.ofNat n (n - m)))).seq fun d2 t2 =>
            (emitOp2E d2 (.add (.bits n)) x t2).seq fun d3 t3 =>
            emitOp2E d3 (.ashr (.bits n)) t3 (.imm (BitVec.ofNat n m))
      else none
    | none =>
      match findSMagic n d with
      | some (A, s) =>
        if sDivCert n d A s then
          let mInt : Int := if 0 < d.toInt then (A : Int) else -(A : Int)
          let m : BitVec n := BitVec.ofInt n mInt
          let finish (p : DivEmit n) : DivEmit n :=
            p.seq fun d1 q0 =>
            (emitOp2E d1 (.lshr (.bits n)) q0 (.imm (BitVec.ofNat n (n - 1)))).seq fun d2 sgn =>
            emitOp2E d2 (.add (.bits n)) q0 sgn
          let afterShift (p : DivEmit n) : DivEmit n :=
            if s == 0 then finish p
            else finish (p.seq fun d1 t =>
              emitOp2E d1 (.ashr (.bits n)) t (.imm (BitVec.ofNat n s)))
          some <| afterShift <|
            let p0 := emitMulwE outD n (.smulw n) x (.imm m)
            if 0 < d.toInt && m.toInt < 0 then
              p0.seq fun d1 hi => emitOp2E d1 (.add (.bits n)) hi x
            else if d.toInt < 0 && 0 < m.toInt then
              p0.seq fun d1 hi => emitOp2E d1 (.sub (.bits n)) hi x
            else p0
        else none
      | none => none

/-- Plan certified constant signed remainder directly as `TFlat` wrappers. -/
def emitSRemConstPlan (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD : Nat) :
    Option (DivEmit n) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n || d == BitVec.allOnes n then none
  else if d == 1#n then some ⟨outD, .imm 0#n, fun tail => tail⟩
  else
    (emitSDivConstPlan n x d outD).map fun p =>
      p.seq fun d1 q =>
      (emitOp2E d1 (.mul (.bits n)) q (.imm d)).seq fun d2 prod =>
      emitOp2E d2 (.sub (.bits n)) x prod

/-- Dispatch constant division/remainder replacement for one `let_` operation. -/
def divConstEmit {sig ts : List Ty} :
    OpCode sig ts → Tup (Arg K) sig → Nat → Option (DivPlan ts)
  | .udiv n, (x, .imm d, ()), outD =>
    (emitUDivConstPlan n x d outD).map fun p => ⟨p.outDepth, (p.res, ()), p.wrap⟩
  | .urem n, (x, .imm d, ()), outD =>
    (emitURemConstPlan n x d outD).map fun p => ⟨p.outDepth, (p.res, ()), p.wrap⟩
  | .sdiv n, (x, .imm d, ()), outD =>
    (emitSDivConstPlan n x d outD).map fun p => ⟨p.outDepth, (p.res, ()), p.wrap⟩
  | .srem n, (x, .imm d, ()), outD =>
    (emitSRemConstPlan n x d outD).map fun p => ⟨p.outDepth, (p.res, ()), p.wrap⟩
  | _, _, _ => none

mutual
/-- Direct `TFlat` constant division/remainder lowering sweep. -/
def divConstGo {rs : List Ty} (inDepth outDepth : Nat) :
    TFlat rs → Trie ((t : Ty) × Arg K t) → TFlat rs
  | .let_ (ts := ts) op k, inEnv =>
    let args' := resolveFlatArgs inDepth inEnv op.args
    match divConstEmit op.code args' outDepth with
    | some p =>
      let inEnv' := insertTupEnv inDepth inEnv p.res
      p.wrap (divConstGo (inDepth + ts.length) p.outDepth k inEnv')
    | none =>
      let inEnv' := insertFreshWith (fun _ _ outD => .var outD) inDepth outDepth ts inEnv
      .let_ ⟨op.code, idxArgs outDepth args'⟩
        (divConstGo (inDepth + ts.length) (outDepth + ts.length) k inEnv')
  | .load t a k, inEnv =>
    let a' := resolveFlatArg inDepth inEnv a
    .load t (idxArg outDepth a')
      (divConstGo (inDepth + 1) (outDepth + 1) k (inEnv.insert inDepth ⟨t, .var outDepth⟩))
  | .store v a k, inEnv =>
    let v' := resolveFlatArg inDepth inEnv v
    let a' := resolveFlatArg inDepth inEnv a
    .store (idxArg outDepth v') (idxArg outDepth a') (divConstGo inDepth outDepth k inEnv)
  | .call f bs args k, inEnv =>
    let args' := resolveFlatArgs inDepth inEnv args
    let inEnv' := insertFreshWith (fun _ _ outD => .var outD) inDepth outDepth bs inEnv
    .call f bs (idxArgs outDepth args')
      (divConstGo (inDepth + bs.length) (outDepth + bs.length) k inEnv')
  | .jnz c t e, inEnv =>
    let c' := resolveFlatArg inDepth inEnv c
    .jnz (idxArg outDepth c')
      (divConstGo inDepth outDepth t inEnv) (divConstGo inDepth outDepth e inEnv)
  | .jump j args, inEnv => .jump j (idxArgs outDepth (resolveFlatArgs inDepth inEnv args))
  | .ret vs, inEnv => .ret (idxArgs outDepth (resolveFlatArgs inDepth inEnv vs))
  | .exit f args, inEnv => .exit f (idxArgs outDepth (resolveFlatArgs inDepth inEnv args))
  | .hlt, _ => .hlt
  | .group bodies k, inEnv =>
    .group (divConstBGo inDepth outDepth bodies inEnv) (divConstGo inDepth outDepth k inEnv)

/-- Block-list companion of `divConstGo`. -/
def divConstBGo {rs : List Ty} (inDepth outDepth : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Trie ((t : Ty) × Arg K t) → TBlocks rs sig
  | _, .nil, _ => .nil
  | _, .cons (ts := ts) b bs, inEnv =>
    let inEnv' := insertFreshWith (fun _ _ outD => .var outD) inDepth outDepth ts inEnv
    .cons (divConstGo (inDepth + ts.length) (outDepth + ts.length) b inEnv')
      (divConstBGo inDepth outDepth bs inEnv)
end

/-- Native `TFlat` constant division/remainder pass with `O(N)` `hasDivRem` fast-path. -/
def divConstFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  if hasDivRem tf then
    let initEnv := insertFreshWith (fun _ _ outD => .var outD) 0 0 as .empty
    divConstGo as.length as.length tf initEnv
  else tf

end OptFlatMem
end LeanQbe.T
