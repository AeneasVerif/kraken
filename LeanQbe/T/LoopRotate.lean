module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Flat

/-!
# CFG Loop Rotation Pass (`LeanQbe.T.LoopRotate`)

Transforms single-block `while`-style header-tested loops `.group (sig := [ts]) (.cons b .nil) k`
whose block body `b` begins with a short straight-line header `H` (`let_` / `load` chain) ending in
`.jnz c armT armE` where one arm (`exitArm`) has `0` jumps back to the loop and the other arm
(`contArm`) has `≥ 1` back-edges:

1. **`buildRotPlan`** (Phase 1, untrusted `O(N)` `TFlat` planner): scans `reifyFunc f` bottom-up
   tracking jump counts, subtree sizes, and referenced variable levels, selecting loops that fit
   within header, back-edge, and code-growth caps (`defaultRotConfig`). Projects minimal masks so
   dead header booleans/temporaries add zero extra block parameters on `loop_rot` (and wraps large
   or structured `exitArm`s into an outer 1-block join `.group` `exit_lbl` with minimal live
   parameters).
2. **`validateRotPlan` / `rewriteRot`** (Phase 2, verified PHOAS validator & single-pass rewriter):
   confirms header structure, `exitArm` absence of back-edges (`BoolL`), and liveness masks for
   dropped parameters, then rewrites entries and back-edges to evaluate `H` at each jump target so
   loops become bottom-tested (`jcc loop_rot`).
3. **`Func.loopRotate` / `Fn.loopRotate`**: skips `rewriteRot` immediately if `!plan.hasRot`,
   falling back cleanly if validation ever rejects.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace LoopRotate

attribute [local instance] Val.inhabited

/-- Type-erased label predicate marking outer labels (`true`) vs forbidden loop target (`false`). -/
abbrev BoolL : List Ty → Type := fun _ => Bool

/-- Build an all-`true` tuple of `BoolL` predicates matching `sig`. -/
def trueLabels : (sig : List (List Ty)) → Tup BoolL sig
  | [] => ()
  | _ :: sig => (true, trueLabels sig)

/-- Kernel-friendly decidable equality on `List Ty` built on `tyDecEq`. -/
def tysDecEq : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match tyDecEq a b, tysDecEq as bs with
    | isTrue ha, isTrue hbs => isTrue (ha ▸ hbs ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)

/-! ## Loop rotation plan and heuristic configuration -/

/-- One straight-line operation in a duplicated loop header. -/
inductive HdrStep : Type
  | let_ (dts : List Ty)
  | load (t : Ty)
  deriving Repr, DecidableEq

/-- Parameter types bound by one header step. -/
@[reducible] def HdrStep.tys : HdrStep → List Ty
  | .let_ dts => dts
  | .load t => [t]

/-- Straight-line loop header prefix prior to `.jnz`. -/
abbrev HdrPlan : Type := List HdrStep

/-- How the non-looping exit arm of a rotated loop is emitted. -/
inductive ExitMode : Type
  | inline
  | wrap (xsMask : List Bool) (hMasks : List (List Bool))
  deriving Repr, DecidableEq

/-- Structural plan guiding verified loop rotation. -/
inductive RotPlan : Type
  | leaf
  | letP (k : RotPlan)
  | loadP (k : RotPlan)
  | storeP (k : RotPlan)
  | callP (k : RotPlan)
  | jnzP (t e : RotPlan)
  | groupKeep (bs : List RotPlan) (k : RotPlan)
  | groupRot (dir : Bool) (hdr : HdrPlan) (contMasks : List (List Bool))
      (exitMode : ExitMode) (contP exitP entryP : RotPlan)
  deriving Repr

mutual
/-- True iff `p` performs at least one loop rotation. -/
def RotPlan.hasRot : RotPlan → Bool
  | .leaf => false
  | .letP k | .loadP k | .storeP k | .callP k => k.hasRot
  | .jnzP t e => t.hasRot || e.hasRot
  | .groupKeep bs k => RotPlan.listHasRot bs || k.hasRot
  | .groupRot .. => true

/-- True iff any plan in `bs` performs a loop rotation. -/
def RotPlan.listHasRot : List RotPlan → Bool
  | [] => false
  | p :: ps => p.hasRot || RotPlan.listHasRot ps
end

/-- Size and duplication limits for loop rotation (`buildRotPlan`). -/
structure RotConfig where
  maxHdrOps : Nat := 6
  maxBackJumps : Nat := 16
  maxEntryJumps : Nat := 4
  inlineExitMax : Nat := 3
  dupBudget : Nat := 40
  maxContLiveVars : Nat := 4
  allowLoadHdr : Bool := false
  requireTailMajority : Bool := true
  deriving Repr, DecidableEq

/-- Default loop-rotation configuration. -/
def defaultRotConfig : RotConfig := {}

/-! ## Masked signature and tuple plumbing -/

/-- Retain parameter types whose mask entry is `true` (missing entries default to `true`). -/
@[reducible] def filterTys : (ts : List Ty) → List Bool → List Ty
  | [], _ => []
  | t :: ts, bs => if bs.headD true then t :: filterTys ts bs.tail else filterTys ts bs.tail

/-- Concatenated masked signature over a header step list plus a tail signature. -/
@[reducible] def stepMasksSig : HdrPlan → List (List Bool) → List Ty → List Ty
  | [], _, tail => tail
  | s :: ss, ms, tail =>
    filterTys s.tys (ms.headD []) ++ stepMasksSig ss ms.tail tail

/-- Rotated loop-block signature (`contMasks` over header variables, keeping all loop `ts`). -/
@[reducible] def rotSig (hdr : HdrPlan) (contMasks : List (List Bool)) (ts : List Ty) :
    List Ty :=
  stepMasksSig hdr contMasks ts

/-- Factored exit-block signature (`hMasks` over header variables, `xsMask` over loop `ts`). -/
@[reducible] def exitSig (hdr : HdrPlan) (hMasks : List (List Bool))
    (xsMask : List Bool) (ts : List Ty) : List Ty :=
  stepMasksSig hdr hMasks (filterTys ts xsMask)

/-- Concatenate two heterogeneous tuples. -/
def tupAppend {f : Ty → Type} : {as bs : List Ty} → Tup f as → Tup f bs → Tup f (as ++ bs)
  | [], _, (), ys => ys
  | _ :: _, _, (x, xs), ys => (x, tupAppend xs ys)

/-- Split a concatenated heterogeneous tuple at prefix `as`. -/
def tupSplit {f : Ty → Type} :
    (as : List Ty) → {bs : List Ty} → Tup f (as ++ bs) → Tup f as × Tup f bs
  | [], _, ys => ((), ys)
  | _ :: as, _, (x, rest) =>
    let (xs, ys) := tupSplit as rest
    ((x, xs), ys)

/-- Optional operand binder enabling dead header/exit variables to be bound as `none`. -/
abbrev OptArg (V : Ty → Type) (t : Ty) : Type := Option (Arg V t)

/-- Flatten `Arg (OptArg V) t` into `Arg V t`, substituting `default` for dead `none` slots. -/
def flatOptArg {V : Ty → Type} {t : Ty} : Arg (OptArg V) t → Arg V t
  | .var (some a) => a
  | .var none => .imm default
  | .imm c => .imm c

/-- Map `flatOptArg` across an operand tuple. -/
abbrev flatOptArgs {V : Ty → Type} {ts : List Ty} :
    Tup (Arg (OptArg V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => flatOptArg

/-- Flatten operands of an `Op (OptArg V) rs` into `Op V rs`. -/
def flatOptOp {V : Ty → Type} {rs : List Ty} (op : Op (OptArg V) rs) : Op V rs :=
  ⟨op.code, flatOptArgs op.args⟩

/-- Lift concrete operands `Tup (Arg V) ts` into all-`some` `OptArg` binders. -/
def someArgsToOpt {V : Ty → Type} : {ts : List Ty} → Tup (Arg V) ts → Tup (OptArg V) ts
  | [], () => ()
  | _ :: _, (a, as) => (some a, someArgsToOpt as)

/-- Lift concrete variables `Tup V ts` into all-`some` `OptArg` binders. -/
def someVarsToOpt {V : Ty → Type} : {ts : List Ty} → Tup V ts → Tup (OptArg V) ts
  | [], () => ()
  | _ :: _, (v, vs) => (some (.var v), someVarsToOpt vs)

/-- Select masked operands from `Tup (Arg V) ts`. -/
def tupSelectArgs {V : Ty → Type} :
    (ts : List Ty) → (bs : List Bool) → Tup (Arg V) ts → Tup (Arg V) (filterTys ts bs)
  | [], _, () => ()
  | _ :: ts, bs, (a, as) =>
    if h : bs.headD true = true then by
      simpa only [filterTys, h, ↓reduceIte] using (a, tupSelectArgs ts bs.tail as)
    else by
      simpa only [filterTys, h, Bool.false_eq_true, ↓reduceIte] using tupSelectArgs ts bs.tail as

/-- Widen masked live variables `Tup V (filterTys ts bs)` into `Tup (OptArg V) ts`. -/
def tupWiden {V : Ty → Type} :
    (ts : List Ty) → (bs : List Bool) → Tup V (filterTys ts bs) → Tup (OptArg V) ts
  | [], _, _ => ()
  | _ :: ts, bs, ys =>
    if h : bs.headD true = true then
      let ys' : V _ × Tup V (filterTys ts bs.tail) := by
        simpa only [filterTys, h, ↓reduceIte] using ys
      (some (.var ys'.1), tupWiden ts bs.tail ys'.2)
    else
      let ys' : Tup V (filterTys ts bs.tail) := by
        simpa only [filterTys, h, Bool.false_eq_true, ↓reduceIte] using ys
      (none, tupWiden ts bs.tail ys')

/-! ## Rewriter label representation -/

/-- Sweep label mapping outer labels (`keep`), rotated loop entries (`expand`), and partial
loop-body targets that may either expand the header (`expand`) or jump back to the shared
header block `lHdr` (`expandOrKeep`). -/
inductive RotL (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List Ty → Type
  | keep {ts : List Ty} (l : L ts) : RotL V L rs ts
  | expand {ts : List Ty} (f : Tup (Arg V) ts → Expr V L rs) : RotL V L rs ts
  | expandOrKeep {ts : List Ty} (f : Tup (Arg V) ts → Expr V L rs) (lHdr : L ts) :
      RotL V L rs ts
  | dead {ts : List Ty} : RotL V L rs ts

/-- Wrap outer target labels into `RotL.keep`. -/
def wrapKeepLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Tup L sig → Tup (RotL V L rs) sig
  | [], () => ()
  | _ :: _, (l, ls) => (.keep l, wrapKeepLabels ls)

/-- Build `exitArm`-side labels matching `sig` (`.dead` is unreachable in validated `exitArm`s). -/
def exitLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (ts : List Ty) :
    Tup (RotL V L rs) [ts] :=
  (.dead, ())

/-! ## Phase 2: Verified PHOAS validator (`validateRotPlan`) -/

/-- Add variable keys in a `Tup (Arg K) ts` into a `Trie Unit` set. -/
def addArgsSet {ts : List Ty} (as : Tup (Arg K) ts) (s : Trie Unit) : Trie Unit :=
  addArgKeys as s

/-- Check that every masked-out variable position `[lvl .. lvl + ts.length)` is absent from `s`. -/
def checkDeadMask (lvl : Nat) (s : Trie Unit) : (ts : List Ty) → List Bool → Bool
  | [], _ => true
  | _ :: ts, bs =>
    (bs.headD true || !(s.find? lvl).isSome) && checkDeadMask (lvl + 1) s ts bs.tail

/-- Check dead masks across every step of `hdr : HdrPlan` starting at level `lvl`. -/
def checkDeadStepMasks (lvl : Nat) (s : Trie Unit) : HdrPlan → List (List Bool) → Bool
  | [], _ => true
  | st :: ss, ms =>
    checkDeadMask lvl s st.tys (ms.headD []) &&
      checkDeadStepMasks (lvl + st.tys.length) s ss ms.tail

/-- Validate a `.leaf` subtree (collecting referenced variable levels and rejecting any `false`
jump target). -/
def validateLeaf {rs : List Ty} : Expr K BoolL rs → Nat → Option (Trie Unit)
  | .let_ (ts := ts) op k, nv => do
    let s ← validateLeaf (k (Tup.levels ts nv)) (nv + ts.length)
    pure (addArgsSet op.args s)
  | .load _ a k, nv => do
    let s ← validateLeaf (k nv) (nv + 1)
    pure (addArgKey a s)
  | .store v a k, nv => do
    let s ← validateLeaf k nv
    pure (addArgKey v (addArgKey a s))
  | .call _ (bs := bs) args k, nv => do
    let s ← validateLeaf (k (Tup.levels bs nv)) (nv + bs.length)
    pure (addArgsSet args s)
  | .jnz c t e, nv => do
    let st ← validateLeaf t nv
    let se ← validateLeaf e nv
    pure (addArgKey c (trieUnion st se))
  | .jump lb args, _ => if lb then pure (addArgsSet args .empty) else none
  | .ret vs, _ => pure (addArgsSet vs .empty)
  | .exit _ args, _ => pure (addArgsSet args .empty)
  | .hlt, _ => pure .empty
  | .group (sig := sig) bs k, nv => do
    let ls := trueLabels sig
    let sb ← validateLeafB (bs ls) nv
    let sk ← validateLeaf (k ls) nv
    pure (trieUnion sb sk)
where
  /-- Block-list companion for `validateLeaf`. -/
  validateLeafB {rs : List Ty} :
      {sig : List (List Ty)} → Blocks K BoolL rs sig → Nat → Option (Trie Unit)
    | _, .nil, _ => pure .empty
    | _, .cons (ts := ts) b bs, nv => do
      let s ← validateLeaf (b (Tup.levels ts nv)) (nv + ts.length)
      let ss ← validateLeafB bs nv
      pure (trieUnion s ss)

/-- Validate a header prefix `hdr` ending in `.jnz`, returning `(hdrVars, armT, armE, nvAfter)`
along with an updated variable-level cursor. -/
def validateHdr {rs : List Ty} :
    HdrPlan → Expr K BoolL rs → Nat →
    Option (Trie Unit × Expr K BoolL rs × Expr K BoolL rs × Nat)
  | [], .jnz c t e, nv => pure (addArgKey c .empty, t, e, nv)
  | .let_ dts :: ss, .let_ (ts := dts') op k, nv =>
    match tysDecEq dts dts' with
    | isTrue h => do
      let (s, t, e, nv') ← validateHdr ss (k (h ▸ Tup.levels dts nv)) (nv + dts.length)
      pure (addArgsSet op.args s, t, e, nv')
    | isFalse _ => none
  | .load t :: ss, .load t' a k, nv =>
    match tyDecEq t t' with
    | isTrue h => do
      let (s, te, ee, nv') ← validateHdr ss (k (h ▸ nv)) (nv + 1)
      pure (addArgKey a s, te, ee, nv')
    | isFalse _ => none
  | _, _, _ => none

/-- Total parameter count bound by a header plan. -/
def hdrStepCount : HdrPlan → Nat
  | [] => 0
  | s :: ss => s.tys.length + hdrStepCount ss

/-- Sentinel plan in a validated `contP` arm preserving a cold back-jump to the shared loop
header block (`lHdr`) instead of duplicating the loop header along that edge. -/
abbrev keepJumpPlan : RotPlan := .jnzP .leaf .leaf

/-- True when `.groupRot` uses partial tail-edge mode (`contMasks.length > hdr.length`), emitting
a 2-block loop `[rotSig, ts]` with shared cold header block `ts`. -/
def isPartialMasks (hdr : HdrPlan) (contMasks : List (List Bool)) : Bool :=
  hdr.length < contMasks.length

/-- Parameterized `validateRotPlan` allowing `keepJumpPlan` on `.jump true` edges when
`allowHdr = true` (inside partial-rotation loop bodies). -/
def validateRotPlanWith {rs : List Ty} (allowHdr : Bool) :
    RotPlan → Expr K BoolL rs → Nat → Option (Trie Unit)
  | .leaf, ek, nv => validateLeaf ek nv
  | .letP p, .let_ (ts := ts) op k, nv => do
    let s ← validateRotPlanWith allowHdr p (k (Tup.levels ts nv)) (nv + ts.length)
    pure (addArgsSet op.args s)
  | .loadP p, .load _ a k, nv => do
    let s ← validateRotPlanWith allowHdr p (k nv) (nv + 1)
    pure (addArgKey a s)
  | .storeP p, .store v a k, nv => do
    let s ← validateRotPlanWith allowHdr p k nv
    pure (addArgKey v (addArgKey a s))
  | .callP p, .call _ (bs := bs) args k, nv => do
    let s ← validateRotPlanWith allowHdr p (k (Tup.levels bs nv)) (nv + bs.length)
    pure (addArgsSet args s)
  | .jnzP tp ep, .jnz c t e, nv => do
    let st ← validateRotPlanWith allowHdr tp t nv
    let se ← validateRotPlanWith allowHdr ep e nv
    pure (addArgKey c (trieUnion st se))
  | .jnzP .leaf .leaf, .jump lb args, _ =>
    if allowHdr && lb then pure (addArgsSet args .empty) else none
  | .groupKeep bsP kP, .group (sig := sig) bs k, nv => do
    let ls := trueLabels sig
    let sb ← validateKeepB allowHdr bsP (bs ls) nv
    let sk ← validateRotPlanWith allowHdr kP (k ls) nv
    pure (trieUnion sb sk)
  | .groupRot dir hdr contMasks exitMode contP exitP entryP,
    .group (sig := [ts]) bs k, nv => do
    let xsLvls := Tup.levels ts nv
    let nv0 := nv + ts.length
    let (sh, armT, armE, _) ← validateHdr hdr ((bs (true, ())).get .here xsLvls) nv0
    let (shF, armTF, armEF, _) ← validateHdr hdr ((bs (false, ())).get .here xsLvls) nv0
    let _ := shF
    let armCont := if dir then armT else armE
    let armExit := if dir then armEF else armTF
    let isPart := isPartialMasks hdr contMasks
    let sc ← validateRotPlanWith (allowHdr || isPart) contP armCont (nv0 + hdrStepCount hdr)
    let sx ← validateRotPlanWith allowHdr exitP armExit (nv0 + hdrStepCount hdr)
    let se ← validateRotPlanWith allowHdr entryP (k (true, ())) nv
    if !checkDeadStepMasks nv0 sc hdr contMasks then none
    else match exitMode with
    | .inline => pure (trieUnion sh (trieUnion sc (trieUnion sx se)))
    | .wrap xsMask hMasks =>
      if checkDeadMask nv sx ts xsMask && checkDeadStepMasks nv0 sx hdr hMasks then
        pure (trieUnion sh (trieUnion sc (trieUnion sx se)))
      else none
  | _, _, _ => none
where
  /-- Block-list companion matching `.groupKeep` plans against block bodies. -/
  validateKeepB {rs : List Ty} (allowHdr : Bool) :
      List RotPlan → {sig : List (List Ty)} → Blocks K BoolL rs sig → Nat → Option (Trie Unit)
    | [], _, .nil, _ => pure .empty
    | p :: ps, _, .cons (ts := ts) b bs, nv => do
      let s ← validateRotPlanWith allowHdr p (b (Tup.levels ts nv)) (nv + ts.length)
      let ss ← validateKeepB allowHdr ps bs nv
      pure (trieUnion s ss)
    | _, _, _, _ => none

/-- Check `validateRotPlan` structurally over `p : RotPlan`, returning `some liveVars` on
success or `none` if structure, label permissions, or dead-variable masks fail. -/
def validateRotPlan {rs : List Ty} (plan : RotPlan) (ek : Expr K BoolL rs) (nv : Nat) :
    Option (Trie Unit) :=
  validateRotPlanWith false plan ek nv

/-! ## Phase 2: Verified single-pass PHOAS rewriter (`rewriteRot`) -/

/-- Identity flattening rewriter for `.leaf` subtrees (replacing `OptArg` and `RotL.keep`). -/
def flatExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptArg V) (RotL V L rs) rs → Expr V L rs
  | .let_ op k => .let_ (flatOptOp op) fun xs => flatExpr (k (someVarsToOpt xs))
  | .load t a k => .load t (flatOptArg a) fun v => flatExpr (k (some (.var v)))
  | .store v a k => .store (flatOptArg v) (flatOptArg a) (flatExpr k)
  | .call f args k => .call f (flatOptArgs args) fun xs => flatExpr (k (someVarsToOpt xs))
  | .jnz c t e => .jnz (flatOptArg c) (flatExpr t) (flatExpr e)
  | .jump (.keep l) args => .jump l (flatOptArgs args)
  | .jump (.expand f) args | .jump (.expandOrKeep f _) args => f (flatOptArgs args)
  | .jump .dead _ => .hlt
  | .ret vs => .ret (flatOptArgs vs)
  | .exit f args => .exit f (flatOptArgs args)
  | .hlt => .hlt
  | .group bs k =>
    .group (fun ls => flatBlocks (bs (wrapKeepLabels ls))) fun ls =>
      flatExpr (k (wrapKeepLabels ls))
where
  /-- Block-list companion for `flatExpr`. -/
  flatBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
      {sig : List (List Ty)} → Blocks (OptArg V) (RotL V L rs) rs sig → Blocks V L rs sig
    | _, .nil => .nil
    | _, .cons b bs => .cons (fun xs => flatExpr (b (someVarsToOpt xs))) (flatBlocks bs)

/-- Emit header `hdr` along `e`, collecting masked continuation and exit tuples via CPS and
terminating with `.jnz` invoking `onCont` and `onExit`. -/
def hdrEmit {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {tailC tailX : List Ty}
    (dir : Bool) (tailCArgs : Tup (Arg V) tailC) (tailXArgs : Tup (Arg V) tailX) :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    Expr (OptArg V) (RotL V L rs) rs →
    (Tup (Arg V) (stepMasksSig hdr cMs tailC) → Expr V L rs) →
    (Expr (OptArg V) (RotL V L rs) rs → Tup (Arg V) (stepMasksSig hdr xMs tailX) → Expr V L rs) →
    Expr V L rs
  | [], _, _, .jnz c armT armE, kC, kX =>
    if dir then .jnz (flatOptArg c) (kC tailCArgs) (kX armE tailXArgs)
    else .jnz (flatOptArg c) (kX armT tailXArgs) (kC tailCArgs)
  | .let_ dts :: ss, cMs, xMs, .let_ (ts := dts') op k, kC, kX =>
    match tysDecEq dts dts' with
    | isTrue rfl =>
      .let_ (flatOptOp op) fun ys =>
        hdrEmit dir tailCArgs tailXArgs ss cMs.tail xMs.tail (k (someVarsToOpt ys))
          (fun rest => kC (tupAppend (tupSelectArgs dts (cMs.headD []) (toArgTup ys)) rest))
          (fun ex rest => kX ex (tupAppend (tupSelectArgs dts (xMs.headD []) (toArgTup ys)) rest))
    | isFalse _ => .hlt
  | .load t :: ss, cMs, xMs, .load t' a k, kC, kX =>
    match tyDecEq t t' with
    | isTrue rfl =>
      .load t (flatOptArg a) fun v =>
        let as1 : Tup (Arg V) [t] := (.var v, ())
        hdrEmit dir tailCArgs tailXArgs ss cMs.tail xMs.tail (k (some (.var v)))
          (fun rest => kC (tupAppend (tupSelectArgs [t] (cMs.headD []) as1) rest))
          (fun ex rest => kX ex (tupAppend (tupSelectArgs [t] (xMs.headD []) as1) rest))
    | isFalse _ => .hlt
  | _, _, _, _, _, _ => .hlt

/-- Peel header steps `hdr` from `e`, passing live block parameters from `params` (`none` for
masked-out slots) to reach either `contArm` (`wantCont = true`) or `exitArm` (`wantCont =
false`). -/
def hdrPeel {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {tail : List Ty}
    (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    Tup V (stepMasksSig hdr ms tail) →
    Expr (OptArg V) (RotL V L rs) rs →
    Expr (OptArg V) (RotL V L rs) rs
  | [], _, _, .jnz _ armT armE => if wantCont == dir then armT else armE
  | .let_ dts :: ss, ms, params, .let_ (ts := dts') _ k =>
    match tysDecEq dts dts' with
    | isTrue rfl =>
      let (stepLive, rest) := tupSplit (filterTys dts (ms.headD [])) params
      let ys : Tup (OptArg V) dts := tupWiden dts (ms.headD []) stepLive
      hdrPeel dir wantCont ss ms.tail rest (k ys)
    | isFalse _ => .hlt
  | .load t :: ss, ms, params, .load t' _ k =>
    match tyDecEq t t' with
    | isTrue rfl =>
      let (stepLive, rest) := tupSplit (filterTys [t] (ms.headD [])) params
      let y1 : OptArg V t := (tupWiden [t] (ms.headD []) stepLive).1
      hdrPeel dir wantCont ss ms.tail rest (k y1)
    | isFalse _ => .hlt
  | _, _, _, _ => .hlt

/-- Split trailing `tail` variables from `stepMasksSig hdr ms tail`. -/
def splitTail {V : Ty → Type} {tail : List Ty} :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    Tup V (stepMasksSig hdr ms tail) → Tup V tail
  | [], _, xs => xs
  | st :: ss, ms, params =>
    let (_, rest) := tupSplit (filterTys st.tys (ms.headD [])) params
    splitTail ss ms.tail rest

/-- Extract the peeled continuation arm inside a rotated loop body block. -/
@[reducible] def rotBodyExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (dir : Bool) (hdr : HdrPlan) (contMasks : List (List Bool))
    (bs : Tup (RotL V L rs) [ts] → Blocks (OptArg V) (RotL V L rs) rs [ts])
    (jLbl : RotL V L rs ts) (rotParams : Tup V (rotSig hdr contMasks ts)) :
    Expr (OptArg V) (RotL V L rs) rs :=
  let xs := splitTail hdr contMasks rotParams
  hdrPeel dir true hdr contMasks rotParams ((bs (jLbl, ())).get .here (someVarsToOpt xs))

/-- Rewrite a validated PHOAS expression structurally following `p : RotPlan`, optionally allowing
`keepJumpPlan` jumps to `lHdr` when `allowHdr = true`. -/
def rewriteRotWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Bool → RotPlan → Expr (OptArg V) (RotL V L rs) rs → Expr V L rs
  | _, .leaf, e => flatExpr e
  | allowHdr, .letP p, .let_ op k =>
    .let_ (flatOptOp op) fun xs => rewriteRotWith allowHdr p (k (someVarsToOpt xs))
  | allowHdr, .loadP p, .load t a k =>
    .load t (flatOptArg a) fun v => rewriteRotWith allowHdr p (k (some (.var v)))
  | allowHdr, .storeP p, .store v a k =>
    .store (flatOptArg v) (flatOptArg a) (rewriteRotWith allowHdr p k)
  | allowHdr, .callP p, .call f args k =>
    .call f (flatOptArgs args) fun xs => rewriteRotWith allowHdr p (k (someVarsToOpt xs))
  | allowHdr, .jnzP tp ep, .jnz c t e =>
    .jnz (flatOptArg c) (rewriteRotWith allowHdr tp t) (rewriteRotWith allowHdr ep e)
  | true, .jnzP .leaf .leaf, .jump j args =>
    match j with
    | .expandOrKeep _ lHdr => .jump lHdr (flatOptArgs args)
    | .expand f => f (flatOptArgs args)
    | .keep l => .jump l (flatOptArgs args)
    | .dead => .hlt
  | allowHdr, .groupKeep bsP kP, .group bs k =>
    .group (fun ls => rewriteKeepB allowHdr bsP (bs (wrapKeepLabels ls)))
      fun ls => rewriteRotWith allowHdr kP (k (wrapKeepLabels ls))
  | allowHdr, .groupRot dir hdr contMasks exitMode contP exitP entryP,
    .group (sig := [ts]) bs k =>
    let bFun := fun xs => (bs (exitLabels ts)).get .here xs
    let emitLoop (mkHdrCont : L (rotSig hdr contMasks ts) → Tup (Arg V) ts → Expr V L rs) :
        Expr V L rs :=
      if isPartialMasks hdr contMasks then
        .group (sig := [rotSig hdr contMasks ts, ts])
          (fun (J_rot, J_hdr, ()) =>
            .cons (fun rotParams =>
              rewriteRotWith true contP
                (rotBodyExpr dir hdr contMasks bs (.expandOrKeep (mkHdrCont J_rot) J_hdr)
                  rotParams))
              (.cons (fun hdrParams => mkHdrCont J_rot (toArgTup hdrParams)) .nil))
          (fun (J_rot, _, ()) =>
            rewriteRotWith allowHdr entryP (k (.expand (mkHdrCont J_rot), ())))
      else
        .group (sig := [rotSig hdr contMasks ts])
          (fun (J_rot, ()) =>
            .cons (fun rotParams =>
              rewriteRotWith allowHdr contP
                (rotBodyExpr dir hdr contMasks bs (.expand (mkHdrCont J_rot)) rotParams))
              .nil)
          (fun (J_rot, ()) =>
            rewriteRotWith allowHdr entryP (k (.expand (mkHdrCont J_rot), ())))
    match exitMode with
    | .inline =>
      let onExit := fun exitExpr (_ : Tup (Arg V) (stepMasksSig hdr [] ts)) =>
        rewriteRotWith allowHdr exitP exitExpr
      emitLoop fun J_rot args =>
        hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
          (bFun (someArgsToOpt args)) (fun rotArgs => .jump J_rot rotArgs) onExit
    | .wrap xsMask hMasks =>
      let exitBlock := fun (exitParams : Tup V (exitSig hdr hMasks xsMask ts)) =>
        let xsTail := splitTail hdr hMasks exitParams
        let xsOpt := tupWiden ts xsMask xsTail
        let arm := hdrPeel dir false hdr hMasks exitParams (bFun xsOpt)
        rewriteRotWith allowHdr exitP arm
      .group (sig := [exitSig hdr hMasks xsMask ts])
        (fun _ => .cons exitBlock .nil)
        (fun (J_exit, ()) =>
          emitLoop fun J_rot args =>
            hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
              dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
              (bFun (someArgsToOpt args)) (fun rotArgs => .jump J_rot rotArgs)
              (fun _ exitArgs => .jump J_exit exitArgs))
  | _, _, _ => .hlt
where
  /-- Block-list companion for `.groupKeep`. -/
  rewriteKeepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (allowHdr : Bool) :
      List RotPlan → {sig : List (List Ty)} → Blocks (OptArg V) (RotL V L rs) rs sig →
      Blocks V L rs sig
    | [], _, bs => flatExpr.flatBlocks bs
    | p :: ps, _, .cons b bs =>
      .cons (fun xs => rewriteRotWith allowHdr p (b (someVarsToOpt xs)))
        (rewriteKeepB allowHdr ps bs)
    | _ :: _, _, .nil => .nil

/-- Rewrite a validated PHOAS expression structurally following `p : RotPlan`. -/
def rewriteRot {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (plan : RotPlan) (e : Expr (OptArg V) (RotL V L rs) rs) : Expr V L rs :=
  rewriteRotWith false plan e

/-! ## Phase 1: Untrusted linear-time `TFlat` planner (`buildRotPlan`) -/

/-- Sorted sparse map `(depth, count)` tracking jump counts to enclosing labels. -/
abbrev JumpCounts := List (Nat × Nat)

/-- Insert `(d₁, c₁)` merged with `cont` (the recursive merge on the left tail) into sorted
`JumpCounts` by structural recursion. -/
def mergeJumpsInsert (d₁ c₁ : Nat) (cont : JumpCounts → JumpCounts) :
    JumpCounts → JumpCounts
  | [] => (d₁, c₁) :: cont []
  | (d₂, c₂) :: ys =>
    if d₁ < d₂ then (d₁, c₁) :: cont ((d₂, c₂) :: ys)
    else if d₂ < d₁ then (d₂, c₂) :: mergeJumpsInsert d₁ c₁ cont ys
    else (d₁, c₁ + c₂) :: cont ys

/-- Sum two `JumpCounts` maps in `O(#entries)` via pure structural recursion. -/
def mergeJumps : JumpCounts → JumpCounts → JumpCounts
  | [], ys => ys
  | (d₁, c₁) :: xs, ys => mergeJumpsInsert d₁ c₁ (mergeJumps xs) ys

/-- Shift jump counts outward across a `sig.length`-label `.group` binder. -/
def shiftJumps (n : Nat) (jc : JumpCounts) : JumpCounts :=
  jc.filterMap fun (d, c) => if d < n then none else some (d - n, c)

/-- Query jump count to relative label index `d`. -/
def getJumpCount (d : Nat) : JumpCounts → Nat
  | [] => 0
  | (d', c) :: rest => if d' == d then c else if d' < d then getJumpCount d rest else 0

/-- Pre-jnz arm snapshot captured during bottom-up `TFlat` analysis. -/
structure ArmSnap where
  plan : RotPlan
  size : Nat
  noGroup : Bool
  live : Trie Unit
  jumps : JumpCounts
  condJumps : JumpCounts

/-- Straight-line header candidate captured bottom-up before reaching `.group`. -/
structure HdrCand where
  hdr : HdrPlan
  sHdr : Trie Unit
  armT : ArmSnap
  armE : ArmSnap

/-- Bottom-up analysis summary per `TFlat` subtree. -/
structure PlanInfo where
  plan : RotPlan
  size : Nat
  noGroup : Bool
  live : Trie Unit
  jumps : JumpCounts
  condJumps : JumpCounts
  cand? : Option HdrCand

/-- Record `TFlat` index operands (converted via `nv` into de Bruijn levels) into `s`. -/
def addIdxArgs (nv : Nat) : {ts : List Ty} → Tup (Arg K) ts → Trie Unit → Trie Unit
  | [], (), s => s
  | _ :: _, (.var idx, rest), s =>
    let s' := addIdxArgs nv rest s
    if idx < nv then s'.insert (nv - 1 - idx) () else s'
  | _ :: _, (.imm _, rest), s => addIdxArgs nv rest s

/-- Compress a `PlanInfo`'s plan to `.leaf` when zero rotations appear below it. -/
def compressInfo (i : PlanInfo) : PlanInfo :=
  if i.plan.hasRot then i else { i with plan := .leaf }

/-- Snapshot a `PlanInfo` for inclusion inside `HdrCand` with conditional jump counts. -/
def toArmSnap (i : PlanInfo) (cj : JumpCounts) : ArmSnap :=
  ⟨i.plan, i.size, i.noGroup, i.live, i.jumps, cj⟩

/-- Compute per-parameter liveness mask for `[lvl .. lvl + len)` against `s`. -/
def liveMaskOf (lvl len : Nat) (s : Trie Unit) : List Bool :=
  match len with
  | 0 => []
  | n + 1 => (s.find? lvl).isSome :: liveMaskOf (lvl + 1) n s

/-- Compute liveness masks per header step starting at `lvl`. -/
def hdrMasksOf (lvl : Nat) (s : Trie Unit) : HdrPlan → List (List Bool)
  | [] => []
  | st :: ss => liveMaskOf lvl st.tys.length s :: hdrMasksOf (lvl + st.tys.length) s ss

/-- Count `true` bits across a list of boolean masks. -/
def countTrues (ms : List (List Bool)) : Nat :=
  ms.foldl (fun acc m => m.foldl (fun a b => if b then a + 1 else a) acc) 0

mutual
/-- Whether `tf` contains at least one `.jump` targeting label index `tgt`. -/
def hasBackJump (tgt : Nat) : {rs : List Ty} → TFlat rs → Bool
  | _, .let_ _ k | _, .load _ _ k | _, .store _ _ k | _, .call _ _ _ k => hasBackJump tgt k
  | _, .jnz _ t e => hasBackJump tgt t || hasBackJump tgt e
  | _, .jump j _ => j == tgt
  | _, .ret _ | _, .exit _ _ | _, .hlt => false
  | _, .group (sig := sig) bs k =>
    hasBackJumpB (tgt + sig.length) bs || hasBackJump (tgt + sig.length) k

/-- Block-list companion for `hasBackJump`. -/
def hasBackJumpB (tgt : Nat) : {rs : List Ty} → {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, _, .nil => false
  | _, _, .cons b bs => hasBackJump tgt b || hasBackJumpB tgt bs
end

mutual
/-- Count `.jump` occurrences targeting label `tgt` inside `tf`. -/
def countBackJumps (tgt : Nat) : {rs : List Ty} → TFlat rs → Nat
  | _, .let_ _ k | _, .load _ _ k | _, .store _ _ k | _, .call _ _ _ k => countBackJumps tgt k
  | _, .jnz _ t e => countBackJumps tgt t + countBackJumps tgt e
  | _, .jump j _ => if j == tgt then 1 else 0
  | _, .ret _ | _, .exit _ _ | _, .hlt => 0
  | _, .group (sig := sig) bs k =>
    countBackJumpsB (tgt + sig.length) bs + countBackJumps (tgt + sig.length) k

/-- Block-list companion for `countBackJumps`. -/
def countBackJumpsB (tgt : Nat) : {rs : List Ty} → {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, _, .nil => 0
  | _, _, .cons b bs => countBackJumps tgt b + countBackJumpsB tgt bs
end

/-- Peel `hdr` down a `TFlat` loop body and extract the `contArm` subtree (`dir = true` -> `t`,
`dir = false` -> `e`). -/
def peelTFlatHdr {rs : List Ty} : HdrPlan → Bool → TFlat rs → Option (TFlat rs)
  | [], dir, .jnz _ t e => some (if dir then t else e)
  | .let_ _ :: ss, dir, .let_ _ k => peelTFlatHdr ss dir k
  | .load _ :: ss, dir, .load _ _ k => peelTFlatHdr ss dir k
  | _, _, _ => none

/-- Wrap `child` in `ctor` if any keep-mark or rotation lies below it; else collapse to `.leaf`. -/
def wrapStepPlan (ctor : RotPlan → RotPlan) (child : RotPlan) (kp : Nat) : RotPlan :=
  if kp > 0 || child.hasRot then ctor child else .leaf

mutual
/-- Rewrite `plan` over `tf` (`contArm`), replacing direct `.jnz` cold early-`continue` back-edges
(whose sibling arm still jumps to `tgt`) with `keepJumpPlan`, returning
`(plan', expCount, keepCount)`. -/
def markColdContJumps {rs : List Ty} (tgt : Nat) :
    TFlat rs → RotPlan → RotPlan × Nat × Nat
  | .let_ _ k, p =>
    let pk := match p with | .letP q => q | _ => .leaf
    let (k', e, kp) := markColdContJumps tgt k pk
    (wrapStepPlan .letP k' kp, e, kp)
  | .load _ _ k, p =>
    let pk := match p with | .loadP q => q | _ => .leaf
    let (k', e, kp) := markColdContJumps tgt k pk
    (wrapStepPlan .loadP k' kp, e, kp)
  | .store _ _ k, p =>
    let pk := match p with | .storeP q => q | _ => .leaf
    let (k', e, kp) := markColdContJumps tgt k pk
    (wrapStepPlan .storeP k' kp, e, kp)
  | .call _ _ _ k, p =>
    let pk := match p with | .callP q => q | _ => .leaf
    let (k', e, kp) := markColdContJumps tgt k pk
    (wrapStepPlan .callP k' kp, e, kp)
  | .jnz _ t e, p =>
    let (pt, pe) := match p with | .jnzP t1 e1 => (t1, e1) | _ => (.leaf, .leaf)
    let isJT := match t with | .jump j _ => j == tgt | _ => false
    let isJE := match e with | .jump j _ => j == tgt | _ => false
    let (t', et, kt) :=
      if isJT && hasBackJump tgt e then (keepJumpPlan, 0, 1)
      else markColdContJumps tgt t pt
    let (e', ee, ke) :=
      if isJE && hasBackJump tgt t then (keepJumpPlan, 0, 1)
      else markColdContJumps tgt e pe
    let kp := kt + ke
    let p' := if kp > 0 || t'.hasRot || e'.hasRot then .jnzP t' e' else .leaf
    (p', et + ee, kp)
  | .jump j _, _ => (.leaf, if j == tgt then 1 else 0, 0)
  | .ret _, _ | .exit _ _, _ | .hlt, _ => (.leaf, 0, 0)
  | .group (sig := [_]) (.cons b' .nil) k,
    .groupRot dir' hdr' cm' xm' contP' exitP' entryP' =>
    let (k', ek, kk) := markColdContJumps (tgt + 1) k entryP'
    let expB := countBackJumps (tgt + 1) b'
    (.groupRot dir' hdr' cm' xm' contP' exitP' k', expB + ek, kk)
  | .group (sig := sig) bs k, p =>
    let (bsP0, kP0) := match p with | .groupKeep b kp => (b, kp) | _ => ([], .leaf)
    let (bsP', eb, kb) := markColdContJumpsB (tgt + sig.length) bs bsP0
    let (k', ek, kk) := markColdContJumps (tgt + sig.length) k kP0
    let kp := kb + kk
    let p' :=
      if kp > 0 || RotPlan.listHasRot bsP' || k'.hasRot then .groupKeep bsP' k' else .leaf
    (p', eb + ek, kp)

/-- Block-list companion for `markColdContJumps`. -/
def markColdContJumpsB {rs : List Ty} (tgt : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → List RotPlan → List RotPlan × Nat × Nat
  | _, .nil, _ => ([], 0, 0)
  | _, .cons b bs, ps =>
    let p0 := ps.headD .leaf
    let (b', eb, kb) := markColdContJumps tgt b p0
    let (bs', ebs, kbs) := markColdContJumpsB tgt bs ps.tail
    (b' :: bs', eb + ebs, kb + kbs)
end

/-- Choose full or partial tail-edge rotation for a single-block `.group (sig := [ts])` given
body `b`, `cand : HdrCand`, and continuation `infoK`. -/
def decideRot {rs : List Ty} (cfg : RotConfig) (ts : List Ty) (nv : Nat) (b : TFlat rs)
    (cand : HdrCand) (infoK : PlanInfo) : Option RotPlan :=
  let hasLd := cand.hdr.any fun | .load _ => true | _ => false
  if !cfg.allowLoadHdr && hasLd then none
  else
  let ti := cand.armT
  let ei := cand.armE
  let jT := getJumpCount 0 ti.jumps
  let jE := getJumpCount 0 ei.jumps
  let dir? : Option Bool :=
    if jT > 0 && jE == 0 then some true
    else if jE > 0 && jT == 0 then some false
    else none
  match dir? with
  | none => none
  | some dir =>
    let backJumps := if dir then jT else jE
    let contInfo := if dir then ti else ei
    let exitInfo := if dir then ei else ti
    let entryJumps := getJumpCount 0 infoK.jumps
    let condBack := getJumpCount 0 contInfo.condJumps
    if entryJumps == 0 || entryJumps > cfg.maxEntryJumps then none
    else if backJumps == 0 || contInfo.size ≤ 1 then none
    else
      let nv0 := nv + ts.length
      let contMasks := hdrMasksOf nv0 contInfo.live cand.hdr
      if countTrues contMasks > cfg.maxContLiveVars then none
      else
        let useWrap := exitInfo.size > cfg.inlineExitMax || !exitInfo.noGroup ||
          !(shiftJumps 1 exitInfo.jumps).isEmpty
        let exitMode :=
          if useWrap then
            .wrap (liveMaskOf nv ts.length exitInfo.live)
              (hdrMasksOf nv0 exitInfo.live cand.hdr)
          else .inline
        let dupPerEdge := cand.hdr.length + 1 + (if useWrap then 1 else exitInfo.size)
        let extraFull := entryJumps + backJumps - 1
        let growthFull := extraFull * dupPerEdge + (if useWrap then 2 else 0)
        let fullOk := backJumps ≤ cfg.maxBackJumps &&
          !(cfg.requireTailMajority && 2 * condBack ≥ backJumps) &&
          growthFull ≤ cfg.dupBudget
        if fullOk then
          some (.groupRot dir cand.hdr contMasks exitMode contInfo.plan exitInfo.plan infoK.plan)
        else if condBack < backJumps then
          match peelTFlatHdr cand.hdr dir b with
          | none => none
          | some contArm =>
            let (contP', expCount, keepCount) := markColdContJumps 0 contArm contInfo.plan
            let partialGrowth :=
              (entryJumps + expCount) * dupPerEdge + (if useWrap then 2 else 0)
            if keepCount > 0 && expCount > 0 && expCount ≤ cfg.maxBackJumps &&
                partialGrowth ≤ cfg.dupBudget then
              some (.groupRot dir cand.hdr (contMasks ++ [[]]) exitMode
                contP' exitInfo.plan infoK.plan)
            else none
        else none

mutual
/-- Structural single-pass bottom-up analyzer on `TFlat rs`. -/
def analyzeTFlat (cfg : RotConfig) {rs : List Ty} (nv : Nat) : TFlat rs → PlanInfo
  | .let_ (ts := ts) op k =>
    let ki := analyzeTFlat cfg (nv + ts.length) k
    let cand? := match ki.cand? with
      | some c =>
        if c.hdr.length < cfg.maxHdrOps then
          some { c with hdr := .let_ ts :: c.hdr, sHdr := addIdxArgs nv op.args c.sHdr }
        else none
      | none => none
    compressInfo ⟨.letP ki.plan, 1 + ki.size, ki.noGroup,
      addIdxArgs nv op.args ki.live, ki.jumps, ki.condJumps, cand?⟩
  | .load t a k =>
    let ki := analyzeTFlat cfg (nv + 1) k
    let cand? := match ki.cand? with
      | some c =>
        if c.hdr.length < cfg.maxHdrOps then
          let sHdr := addIdxArgs nv (ts := [i64]) (a, ()) c.sHdr
          some ⟨.load t :: c.hdr, sHdr, c.armT, c.armE⟩
        else none
      | none => none
    compressInfo ⟨.loadP ki.plan, 1 + ki.size, ki.noGroup,
      addIdxArgs nv (ts := [i64]) (a, ()) ki.live, ki.jumps, ki.condJumps, cand?⟩
  | .store v a k =>
    let ki := analyzeTFlat cfg nv k
    let l := addIdxArgs nv (ts := [_, i64]) (v, a, ()) ki.live
    compressInfo ⟨.storeP ki.plan, 1 + ki.size, ki.noGroup, l, ki.jumps, ki.condJumps, none⟩
  | .call _ (bs := bs) args k =>
    let ki := analyzeTFlat cfg (nv + bs.length) k
    compressInfo ⟨.callP ki.plan, 1 + ki.size, ki.noGroup,
      addIdxArgs nv args ki.live, ki.jumps, ki.condJumps, none⟩
  | .jnz c t e =>
    let ti := analyzeTFlat cfg nv t
    let ei := analyzeTFlat cfg nv e
    let ct := match t with | .jump j _ => [(j, 1)] | _ => ti.condJumps
    let ce := match e with | .jump j _ => [(j, 1)] | _ => ei.condJumps
    let sC := addIdxArgs nv (ts := [.bool]) (c, ()) .empty
    let l := trieUnion sC (trieUnion ti.live ei.live)
    let cand : HdrCand := ⟨[], sC, toArmSnap ti ct, toArmSnap ei ce⟩
    compressInfo ⟨.jnzP ti.plan ei.plan, 1 + ti.size + ei.size, ti.noGroup && ei.noGroup,
      l, mergeJumps ti.jumps ei.jumps, mergeJumps ct ce, some cand⟩
  | .jump j args =>
    ⟨.leaf, 1, true, addIdxArgs nv args .empty, [(j, 1)], [], none⟩
  | .ret vs =>
    ⟨.leaf, 1, true, addIdxArgs nv vs .empty, [], [], none⟩
  | .exit _ args =>
    ⟨.leaf, 1, true, addIdxArgs nv args .empty, [], [], none⟩
  | .hlt => ⟨.leaf, 1, true, .empty, [], [], none⟩
  | .group (sig := [ts]) (.cons b .nil) k =>
    let bi := analyzeTFlat cfg (nv + ts.length) b
    let ki := analyzeTFlat cfg nv k
    let totLive := trieUnion bi.live ki.live
    let outJumps := shiftJumps 1 (mergeJumps bi.jumps ki.jumps)
    let outCond := shiftJumps 1 (mergeJumps bi.condJumps ki.condJumps)
    let totSize := 1 + bi.size + ki.size
    match bi.cand? with
    | some cand =>
      match decideRot cfg ts nv b cand ki with
      | some rp => ⟨rp, totSize, false, totLive, outJumps, outCond, none⟩
      | none =>
        compressInfo ⟨.groupKeep [bi.plan] ki.plan, totSize, false, totLive, outJumps, outCond,
          none⟩
    | none =>
      compressInfo ⟨.groupKeep [bi.plan] ki.plan, totSize, false, totLive, outJumps, outCond, none⟩
  | .group (sig := sig) bs k =>
    let (bsP, bSz, bLive, bJumps, bCond) := analyzeTBlocks cfg nv bs
    let ki := analyzeTFlat cfg nv k
    compressInfo ⟨.groupKeep bsP ki.plan, 1 + bSz + ki.size, false,
      trieUnion bLive ki.live, shiftJumps sig.length (mergeJumps bJumps ki.jumps),
      shiftJumps sig.length (mergeJumps bCond ki.condJumps), none⟩

/-- Block-list companion for `analyzeTFlat`. -/
def analyzeTBlocks (cfg : RotConfig) {rs : List Ty} (nv : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig →
    List RotPlan × Nat × Trie Unit × JumpCounts × JumpCounts
  | _, .nil => ([], 0, .empty, [], [])
  | _, .cons (ts := ts) b bs =>
    let bi := analyzeTFlat cfg (nv + ts.length) b
    let (ps, sz, l, jc, cj) := analyzeTBlocks cfg nv bs
    (bi.plan :: ps, bi.size + sz, trieUnion bi.live l,
      mergeJumps bi.jumps jc, mergeJumps bi.condJumps cj)
end

/-- Construct a `RotPlan` directly from a reified `TFlat` body in a single linear pass. -/
def buildRotPlan (cfg : RotConfig := defaultRotConfig) {as rs : List Ty}
    (tf : TFlat rs) : RotPlan :=
  (analyzeTFlat cfg as.length tf).plan

end LoopRotate

/-! ## Top-level `Func.loopRotate` and `Fn.loopRotate` entry points -/

open LoopRotate in
/-- Apply verified loop rotation guided by `plan : RotPlan` to a closed function `f`. Returns
`f` unchanged if validation fails. -/
def Func.loopRotateWithPlan {as rs : List Ty} (plan : RotPlan) (f : Func as rs) : Func as rs :=
  match validateRotPlan plan (f K BoolL (Tup.levels as 0)) as.length with
  | some _ => fun V L xs => rewriteRot plan (f (OptArg V) (RotL V L rs) (someVarsToOpt xs))
  | none => f

open LoopRotate in
/-- Perform single-pass `TFlat`-planned, PHOAS-verified CFG loop rotation on a closed function. -/
def Func.loopRotate {as rs : List Ty} (f : Func as rs) (cfg : RotConfig := defaultRotConfig) :
    Func as rs :=
  let tf := reifyFunc f
  let plan := buildRotPlan (as := as) cfg tf
  if plan.hasRot then Func.loopRotateWithPlan plan (denoteFunc tf) else denoteFunc tf

/-- Apply `Func.loopRotate` to a named function, preserving metadata. -/
def Fn.loopRotate (fn : Fn) (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.loopRotate fn.body cfg⟩

end LeanQbe.T
