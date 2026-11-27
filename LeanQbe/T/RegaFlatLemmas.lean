module

public import LeanQbe.T.RegaFlat
public import LeanQbe.T.FlatDirectLemmas

/-!
# Equivalence of `Rega.lowerFlatFn` and `Rega.lowerFn` (`RegaFlatLemmas`)

Proves `Rega.lowerFlatExpr_eq` and `Rega.lowerFlatFn_eq_lowerFn` by structural induction over
`TFlat` / `TBlocks`, maintaining `CtxTypes Γ vs`, `CtxTypes Δ ls`,
`TrieProjMatch (fun _ x => x) vDepth vEnv vs`, `ListLblMatch lEnv ls`, and `wfCheck = true`.
All proofs live cleanly inside `std3` axioms with zero edits to `RegaLemmas*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

/-! ## 1. Variable & Label Environment Lookup Simulation -/

/-- Projecting `insertVLevels` across `pushTup (Tup.levels ts nv) vs` preserves `TrieProjMatch`. -/
private theorem trieProjMatch_insertVLevels :
    {ts : List Ty} → {vs : List ((t : Ty) × VNat t)} →
    {depth nv : Nat} → {env : Trie Nat} →
    TrieProjMatch (fun _ x => x) depth env vs →
    TrieProjMatch (fun _ x => x) (depth + ts.length)
      (insertVLevels ts.length depth nv env) (pushTup (Tup.levels ts nv) vs)
  | [], _, _, _, _, h => h
  | t :: ts, vs, depth, nv, env, h => by
    dsimp only [List.length_cons, insertVLevels, Tup.levels, pushTup]
    have h1 := h.cons t (nv : VNat t)
    have h2 := trieProjMatch_insertVLevels (ts := ts) (nv := nv + 1) h1
    have hadd : depth + (ts.length + 1) = depth + 1 + ts.length := by omega
    rwa [hadd]

/-- De Bruijn label level environment correspondence against `ls`. -/
@[expose] def ListLblMatch (lEnv : List Nat) (ls : List ((ts : List Ty) × LNat ts)) : Prop :=
  ∀ idx, listGet? lEnv idx = (listGet? ls idx).map (·.2)

private theorem listLblMatch_empty : ListLblMatch [] [] := by
  intro idx; cases idx <;> rfl

private theorem listLblMatch_cons {lEnv : List Nat} {ls : List ((ts : List Ty) × LNat ts)}
    (h : ListLblMatch lEnv ls) (ts : List Ty) (nl : Nat) :
    ListLblMatch (nl :: lEnv) (⟨ts, nl⟩ :: ls) := by
  intro idx
  cases idx with
  | zero => rfl
  | succ i => exact h i

private theorem listLblMatch_pushLLevels :
    {sig : List (List Ty)} → {ls : List ((ts : List Ty) × LNat ts)} →
    {lEnv : List Nat} → {nl : Nat} →
    ListLblMatch lEnv ls →
    ListLblMatch (pushLLevels sig nl lEnv) (pushTup (Tup.levels sig nl) ls)
  | [], _, _, _, h => h
  | ts :: sig, ls, lEnv, nl, h => by
    dsimp only [pushLLevels, Tup.levels, pushTup]
    exact listLblMatch_pushLLevels (nl := nl + 1) (listLblMatch_cons h ts nl)

private theorem flatLabel_lookupL_eq {Δ : List (List Ty)}
    {ls : List ((ts : List Ty) × LNat ts)} {lEnv : List Nat}
    (hΔ : CtxTypes Δ ls) (hlm : ListLblMatch lEnv ls) {ts : List Ty} {j : Nat}
    (hj : listGet? Δ j = some ts) :
    lookupL ls ts j = some (flatLabel lEnv j) := by
  obtain ⟨lvl, hgetls, _⟩ := ctxTypes_listGet? hΔ hj
  have hle := hlm j
  rw [hgetls] at hle
  have hfl : flatLabel lEnv j = lvl := by
    dsimp only [flatLabel]; rw [hle]; rfl
  rw [hfl]
  dsimp only [lookupL]; rw [hgetls]; dsimp only
  rw [PassFlatKit.castListTy_self]

private theorem denoteArg_eq_flatArg {Γ : List Ty} {vs : List ((t : Ty) × VNat t)}
    {vDepth : Nat} {vEnv : Trie Nat}
    (hΓ : CtxTypes Γ vs) (hm : TrieProjMatch (fun _ x => x) vDepth vEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    denoteArg vs a = some (flatArg vDepth vEnv a) := by
  cases a with
  | imm c => rfl
  | var idx =>
    have hget := checkArg_eq_true_iff.mp hc
    obtain ⟨x, hgetvs, hfind⟩ := TrieProjMatch.find?_var_eq hΓ hm hget
    have hvar : flatVar vDepth vEnv idx = x := by
      dsimp only [flatVar, Trie.getD]; rw [hfind]; rfl
    dsimp only [flatArg]; rw [hvar]
    dsimp only [denoteArg, lookupV]; rw [hgetvs]; dsimp only
    rw [PassFlatKit.castTy_self]

private theorem denoteArgs_eq_flatArgs {Γ : List Ty} {vs : List ((t : Ty) × VNat t)}
    {vDepth : Nat} {vEnv : Trie Nat}
    (hΓ : CtxTypes Γ vs) (hm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (flatArgs vDepth vEnv as)
  | [], (), _ => rfl
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    dsimp only [denoteArgs, flatArgs]
    rw [denoteArg_eq_flatArg hΓ hm a hc.1, denoteArgs_eq_flatArgs hΓ hm as hc.2]

/-! ## 2. Instruction-Pointer Count & Lookahead Simulation -/

mutual
private theorem exprIpCountFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × VNat t)} → {ls : List ((ts : List Ty) × LNat ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    ∀ nv nl,
      exprIpCountFlat tf nv nl = exprIpCount (denote VNat LNat tf vs ls) nv nl
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [exprIpCountFlat, denote]; rw [ha]; dsimp only [exprIpCount]
    have hk := exprIpCountFlat_eq k (CtxTypes.push (Tup.levels ts nv) hΓ) hΔ hwf.2
      (nv + ts.length) nl
    rw [hk]
  | .load t a k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [exprIpCountFlat, denote]; rw [ha]; dsimp only [exprIpCount]
    have hk := exprIpCountFlat_eq k (CtxTypes.cons (a := t) (v := (nv : VNat t)) hΓ) hΔ hwf.2
      (nv + 1) nl
    rw [hk]
  | .store v a k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [exprIpCountFlat, denote]; rw [hv, ha]; dsimp only [exprIpCount]
    rw [exprIpCountFlat_eq k hΓ hΔ hwf.2 nv nl]
  | .call f bs args k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [exprIpCountFlat, denote]; rw [ha]; dsimp only [exprIpCount]
    have hk := exprIpCountFlat_eq k (CtxTypes.push (Tup.levels bs nv) hΓ) hΔ hwf.2
      (nv + bs.length) nl
    rw [hk]
  | .jnz c t e, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases c with
    | imm b =>
      dsimp only [exprIpCountFlat, denote, denoteArg, exprIpCount]
      cases b with
      | true => simp only [↓reduceIte]; rw [exprIpCountFlat_eq t hΓ hΔ hwf.1.2 nv nl]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; rw [exprIpCountFlat_eq e hΓ hΔ hwf.2 nv nl]
    | var idx =>
      obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
      dsimp only [denoteArg] at hv
      cases hlk : lookupV vs .bool idx with
      | none => rw [hlk] at hv; cases hv
      | some cx =>
        rw [hlk] at hv; cases hv
        dsimp only [exprIpCountFlat, denote, denoteArg]; rw [hlk]; dsimp only [exprIpCount]
        rw [exprIpCountFlat_eq e hΓ hΔ hwf.2 nv (nl + 1),
          exprIpCountFlat_eq t hΓ hΔ hwf.1.2 _ _]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [exprIpCountFlat, denote]; rw [hj, ha]; rfl
  | .ret vs', Γ, _, vs, _, hΓ, _, hwf, _, _ => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [exprIpCountFlat, denote]; rw [hv]; rfl
  | .exit f args, Γ, _, vs, _, hΓ, _, hwf, _, _ => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [exprIpCountFlat, denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [exprIpCountFlat, denote, exprIpCount]
    have hk := exprIpCountFlat_eq k hΓ (CtxTypes.push (Tup.levels sig nl) hΔ) hwf.2 nv
      (nl + sig.length)
    have hb := blocksIpCountFlat_eq bodies hΓ (CtxTypes.push (Tup.levels sig nl) hΔ) hwf.1
      (exprIpCountFlat k nv (nl + sig.length)).1 (exprIpCountFlat k nv (nl + sig.length)).2.1
    rw [hk] at hb
    rw [hk, hb]

private theorem blocksIpCountFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × VNat t)} → {ls : List ((ts : List Ty) × LNat ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    ∀ nv nl,
      blocksIpCountFlat tb nv nl = blocksIpCount (denoteB VNat LNat tb vs ls) nv nl
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, hΓ, hΔ, hwf, nv, nl => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [blocksIpCountFlat, denoteB, blocksIpCount]
    have hb := exprIpCountFlat_eq b (CtxTypes.push (Tup.levels ts nv) hΓ) hΔ hwf.1
      (nv + ts.length) nl
    rw [hb, blocksIpCountFlat_eq bs hΓ hΔ hwf.2 _ _]
end

private theorem jnzIpTFlat_eq {rs : List Ty} {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (nv nl ip : Nat) (t e : TFlat rs)
    (hwt : t.wfCheck Γ Δ = true) (hwe : e.wfCheck Γ Δ = true) :
    jnzIpTFlat nv nl ip t e =
      jnzIpT nv nl ip (denote VNat LNat t vs ls) (denote VNat LNat e vs ls) := by
  dsimp only [jnzIpTFlat]
  cases t with
  | jump j args =>
    dsimp only [TFlat.wfCheck] at hwt; simp only [Bool.and_eq_true] at hwt
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwt.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwt.2)
    dsimp only [denote]; rw [hj, ha]; dsimp only [jnzIpT]
    rw [exprIpCountFlat_eq e hΓ hΔ hwe nv (nl + 1)]
  | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
  | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
  | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
  | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
  | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
  | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | hlt | group _ _ => rfl

private theorem firstNonFwdFlat_eq {rs : List Ty} (fwd : Trie Nat) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    (vs : List ((t : Ty) × VNat t)) → (ls : List ((ts : List Ty) × LNat ts)) →
    (lid : Nat) → (ft : Option Nat) →
    firstNonFwdFlat fwd tb lid ft = firstNonFwd fwd (denoteB VNat LNat tb vs ls) lid ft
  | _, .nil, _, _, _, _ => rfl
  | _, .cons b bs, vs, ls, lid, ft => by
    dsimp only [firstNonFwdFlat, denoteB, firstNonFwd]
    cases fwd.find? lid with
    | some _ => exact firstNonFwdFlat_eq fwd bs vs ls (lid + 1) ft
    | none => rfl

private theorem zeroMoveJump?Flat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (ip : Nat)
    (st : SymState I) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (tf : TFlat rs) (hwf : tf.wfCheck Γ Δ = true) :
    zeroMoveJump?Flat I h ip st vDepth vEnv lEnv tf =
      zeroMoveJump? I h ip st (denote VNat LNat tf vs ls) := by
  cases tf with
  | jump j args =>
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hj := checkJump_eq_true_iff.mp hwf.1
    dsimp only [zeroMoveJump?Flat, denote]
    rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2]
    rfl
  | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
  | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
  | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
  | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
  | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
  | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | hlt | group _ _ => rfl

private theorem jnzModeFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (ipT ipE : Nat)
    (st : SymState I) (canInv : Bool) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (t e : TFlat rs) (hwt : t.wfCheck Γ Δ = true) (hwe : e.wfCheck Γ Δ = true)
    (ft : Option Nat) (fwd : Trie Nat) :
    jnzModeFlat I h ipT ipE st canInv vDepth vEnv lEnv t e ft fwd =
      jnzMode I h ipT ipE st canInv (denote VNat LNat t vs ls)
        (denote VNat LNat e vs ls) ft fwd := by
  dsimp only [jnzModeFlat, jnzMode]
  rw [zeroMoveJump?Flat_eq I h ipT st hΓ hΔ hvm hlm t hwt,
    zeroMoveJump?Flat_eq I h ipE st hΓ hΔ hvm hlm e hwe]
  rfl

private theorem gprThread?Flat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipT : Nat)
    (st1 : SymState I) (r : I.Reg) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (arm : TFlat rs) (hwf : arm.wfCheck Γ Δ = true) (fwd : Trie Nat) :
    gprThread?Flat I h fn ipT st1 r vDepth vEnv lEnv arm fwd =
      gprThread? I h fn ipT st1 r (denote VNat LNat arm vs ls) fwd := by
  cases arm with
  | jump j args =>
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hj := checkJump_eq_true_iff.mp hwf.1
    dsimp only [gprThread?Flat, denote]
    rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2]
    dsimp only [gprThread?]
    have hz : ∀ stB,
        zeroMoveJump?Flat (rs := rs) I h ipT stB vDepth vEnv lEnv (.jump j args) =
        zeroMoveJump? (rs := rs) I h ipT stB
          (.jump (flatLabel lEnv j) (flatArgs vDepth vEnv args)) := by
      intro stB
      have h0 := zeroMoveJump?Flat_eq (rs := rs) I h ipT stB hΓ hΔ hvm hlm (.jump j args)
        (by dsimp only [TFlat.wfCheck]; simp [hwf.1, hwf.2])
      dsimp only [denote] at h0
      rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2] at h0
      exact h0
    exact hz _
  | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
  | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
  | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
  | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
  | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
  | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | hlt | group _ _ => rfl

private theorem threadFusedArmFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipA : Nat)
    (st1 : SymState I) (emit : Sym → Option (List I.Directive × FlagMask))
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (arm : TFlat rs) (hwf : arm.wfCheck Γ Δ = true) (fwd : Trie Nat) :
    threadFusedArmFlat I h fn ipA st1 emit vDepth vEnv lEnv arm fwd =
      threadFusedArm I h fn ipA st1 emit (denote VNat LNat arm vs ls) fwd := by
  cases arm with
  | jump j args =>
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hj := checkJump_eq_true_iff.mp hwf.1
    have hzm : ∀ stB,
        zeroMoveJump?Flat (rs := rs) I h ipA stB vDepth vEnv lEnv (.jump j args) =
        zeroMoveJump? (rs := rs) I h ipA stB
          (.jump (flatLabel lEnv j) (flatArgs vDepth vEnv args)) := by
      intro stB
      have hz := zeroMoveJump?Flat_eq (rs := rs) I h ipA stB hΓ hΔ hvm hlm (.jump j args)
        (by dsimp only [TFlat.wfCheck]; simp [hwf.1, hwf.2])
      dsimp only [denote] at hz
      rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2] at hz
      exact hz
    dsimp only [threadFusedArmFlat, denote]
    rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2]
    dsimp only [threadFusedArm]
    cases emit (lname fn (tgtLab fwd (flatLabel lEnv j))) with
    | none => rfl
    | some p => dsimp only [Option.bind]; rw [hzm _]
  | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
  | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
  | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
  | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
  | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
  | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | hlt | group _ _ => rfl

private theorem fuseJnzChoiceFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym)
    (nl ipT ipE : Nat) (st1 : SymState I) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (t e : TFlat rs) (hwt : t.wfCheck Γ Δ = true) (hwe : e.wfCheck Γ Δ = true)
    (ft : Option Nat) (emit : Bool → Sym → Option (List I.Directive × FlagMask))
    (fwd : Trie Nat) :
    fuseJnzChoiceFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft emit fwd =
      fuseJnzChoice I h fn nl ipT ipE st1 (denote VNat LNat t vs ls) (denote VNat LNat e vs ls)
        ft emit fwd := by
  dsimp only [fuseJnzChoiceFlat, fuseJnzChoice]
  rw [threadFusedArmFlat_eq I h fn ipT st1 (emit false) hΓ hΔ hvm hlm t hwt fwd,
    threadFusedArmFlat_eq I h fn ipE st1 (emit true) hΓ hΔ hvm hlm e hwe fwd]
  rfl

private theorem finishCmpJnzFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym)
    (nl ipT ipE : Nat) (st1 : SymState I) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (t e : TFlat rs) (hwt : t.wfCheck Γ Δ = true) (hwe : e.wfCheck Γ Δ = true)
    (ft : Option Nat) (fwd : Trie Nat) (cc : I.Cond) (cmpCode : List I.Directive)
    (cl : FlagMask) (fl : Option FlagFact) :
    finishCmpJnzFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft fwd cc cmpCode cl fl =
      finishCmpJnz I h fn nl ipT ipE st1 (denote VNat LNat t vs ls) (denote VNat LNat e vs ls)
        ft fwd cc cmpCode cl fl := by
  dsimp only [finishCmpJnzFlat, finishCmpJnz]
  rw [jnzModeFlat_eq I h ipT ipE _ true hΓ hΔ hvm hlm t e hwt hwe ft fwd]
  rfl

private theorem jnzSetupFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym)
    (nl ipT ipE : Nat) (st1 : SymState I) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (t e : TFlat rs) (hwt : t.wfCheck Γ Δ = true) (hwe : e.wfCheck Γ Δ = true)
    (ft : Option Nat) (cond : JnzCond I) (fwd : Trie Nat) :
    jnzSetupFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft cond fwd =
      jnzSetup I h fn nl ipT ipE st1 (denote VNat LNat t vs ls) (denote VNat LNat e vs ls)
        ft cond fwd := by
  cases cond with
  | flag cc =>
    dsimp only [jnzSetupFlat, jnzSetup]
    rw [jnzModeFlat_eq I h ipT ipE _ true hΓ hΔ hvm hlm t e hwt hwe ft fwd]
    rfl
  | gpr r =>
    dsimp only [jnzSetupFlat, jnzSetup]
    cases I.gpr.jnzGprInv? with
    | some jnzFn =>
      exact fuseJnzChoiceFlat_eq I h fn nl ipT ipE st1 hΓ hΔ hvm hlm t e hwt hwe ft _ fwd
    | none =>
      dsimp only
      rw [gprThread?Flat_eq I h fn ipT st1 r hΓ hΔ hvm hlm t hwt fwd]
      rfl
  | slot idx =>
    dsimp only [jnzSetupFlat, jnzSetup]
    rw [jnzModeFlat_eq I h ipT ipE _ true hΓ hΔ hvm hlm t e hwt hwe ft fwd]
    rfl
  | cmpZero co w r =>
    dsimp only [jnzSetupFlat, jnzSetup]
    exact fuseJnzChoiceFlat_eq I h fn nl ipT ipE st1 hΓ hΔ hvm hlm t e hwt hwe ft _ fwd
  | cmpZeroMem co w x aa cc =>
    dsimp only [jnzSetupFlat, jnzSetup]
    cases I.gpr.cmpMem co w aa (.imm 0#w) (.flag cc) with
    | none => rfl
    | some p =>
      dsimp only [Option.map]
      rw [finishCmpJnzFlat_eq I h fn nl ipT ipE st1 hΓ hΔ hvm hlm t e hwt hwe ft fwd cc p.1]
  | cmpZeroFlag co w x r cc =>
    dsimp only [jnzSetupFlat, jnzSetup]
    cases I.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cc, ()) .default with
    | none => rfl
    | some p =>
      dsimp only [Option.map]
      rw [finishCmpJnzFlat_eq I h fn nl ipT ipE st1 hΓ hΔ hvm hlm t e hwt hwe ft fwd cc p.1]
      rfl
  | testImm neg w r mask =>
    dsimp only [jnzSetupFlat, jnzSetup]
    exact fuseJnzChoiceFlat_eq I h fn nl ipT ipE st1 hΓ hΔ hvm hlm t e hwt hwe ft _ fwd

private theorem finishJnzBranchFlat_eq {rs : List Ty} (I : Isa) (fn : Sym)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (nl : Nat) (tgt? : Option Nat) (b_taken : TFlat rs) (hwf : b_taken.wfCheck Γ Δ = true)
    (br c_ft c_taken : List I.Directive) (nv2 nl2 ip2 : Nat) :
    finishJnzBranchFlat I fn lEnv nl tgt? b_taken br c_ft c_taken nv2 nl2 ip2 =
      finishJnzBranch I fn nl tgt? (denote VNat LNat b_taken vs ls)
        br c_ft c_taken nv2 nl2 ip2 := by
  cases tgt? with
  | none => rfl
  | some j =>
    cases b_taken with
    | jump j' args' =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have hj := checkJump_eq_true_iff.mp hwf.1
      dsimp only [finishJnzBranchFlat, denote]
      rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args' hwf.2]
      rfl
    | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
    | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
    | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
    | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
    | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
    | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
    | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
    | hlt | group _ _ => rfl

private theorem jumpAvoidsFlat_eq {rs : List Ty} {I : Isa} (h : I.Hints) (x : Nat)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (tf : TFlat rs) (hwf : tf.wfCheck Γ Δ = true) :
    jumpAvoidsFlat (I := I) h x vDepth vEnv lEnv tf =
      jumpAvoids (I := I) h x (denote VNat LNat tf vs ls) := by
  cases tf with
  | jump j args =>
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hj := checkJump_eq_true_iff.mp hwf.1
    dsimp only [jumpAvoidsFlat, denote]
    rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2]
    rfl
  | let_ op _ => dsimp only [denote]; cases denoteArgs vs op.args <;> rfl
  | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
  | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
  | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
  | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
  | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
  | hlt | group _ _ => rfl

private theorem loadSextNextFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (nv ip : Nat) (st : SymState I) (t : Ty) (a : Arg VNat i64)
    (k : TFlat rs) (hwf : k.wfCheck (t :: Γ) Δ = true) :
    loadSextNextFlat I h (vDepth + 1) (vEnv.insert vDepth nv) lEnv nv ip st t a k =
      loadSextNext I h nv ip st t a (denote VNat LNat k (⟨t, nv⟩ :: vs) ls) := by
  let vs1 : List ((u : Ty) × VNat u) := ⟨t, nv⟩ :: vs
  have hΓ1 : CtxTypes (t :: Γ) vs1 := CtxTypes.cons (a := t) (v := (nv : VNat t)) hΓ
  have hvm1 : TrieProjMatch (fun _ x => x) (vDepth + 1) (vEnv.insert vDepth nv) vs1 :=
    hvm.cons t (nv : VNat t)
  dsimp only [loadSextNextFlat, loadSextNext]
  cases k with
  | let_ op k2 =>
    rename_i ts
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_flatArgs hΓ1 hvm1 op.args hwf.1]
    dsimp only [flatOp]
    have hΓ2 := CtxTypes.push (Tup.levels ts (nv + 1)) hΓ1
    have hvm2 := trieProjMatch_insertVLevels (ts := ts) (nv := nv + 1) hvm1
    cases k2 with
    | jnz c tt ee =>
      have hwf2 := hwf.2
      dsimp only [TFlat.wfCheck] at hwf2; simp only [Bool.and_eq_true] at hwf2
      cases c with
      | imm _ => dsimp only [denote, denoteArg]; rfl
      | var cx =>
        dsimp only [denote]
        rw [denoteArg_eq_flatArg hΓ2 hvm2 (.var cx) hwf2.1.1]
        dsimp only [flatArg]
        apply congrArg (isGprTy I t && ·)
        apply congrArg (_ || ·)
        apply congrArg (_ && ·)
        apply congrArg (_ && ·)
        refine congr (congrArg (· || ·) ?_) ?_
        · rw [jumpAvoidsFlat_eq h nv hΓ2 hΔ hvm2 hlm tt hwf2.1.2]
          apply congrArg (_ && ·)
          have hwe := hwf2.2
          cases ee with
          | let_ op3 _ =>
            dsimp only [TFlat.wfCheck] at hwe; simp only [Bool.and_eq_true] at hwe
            dsimp only [denote]
            rw [denoteArgs_eq_flatArgs hΓ2 hvm2 op3.args hwe.1]
            rfl
          | load _ a3 _ => dsimp only [denote]; cases denoteArg _ a3 <;> rfl
          | store v3 a3 _ =>
            dsimp only [denote]; cases denoteArg _ v3 <;> cases denoteArg _ a3 <;> rfl
          | call _ _ args3 _ => dsimp only [denote]; cases denoteArgs _ args3 <;> rfl
          | jnz c3 _ _ => dsimp only [denote]; cases denoteArg _ c3 <;> rfl
          | jump j3 args3 =>
            rename_i ts3
            dsimp only [denote]; cases lookupL ls ts3 j3 <;> cases denoteArgs _ args3 <;> rfl
          | ret vs3 => dsimp only [denote]; cases denoteArgs _ vs3 <;> rfl
          | exit _ args3 => dsimp only [denote]; cases denoteArgs _ args3 <;> rfl
          | hlt | group _ _ => rfl
        · rw [jumpAvoidsFlat_eq h nv hΓ2 hΔ hvm2 hlm ee hwf2.2]
          apply congrArg (_ && ·)
          have hwt := hwf2.1.2
          cases tt with
          | let_ op3 _ =>
            dsimp only [TFlat.wfCheck] at hwt; simp only [Bool.and_eq_true] at hwt
            dsimp only [denote]
            rw [denoteArgs_eq_flatArgs hΓ2 hvm2 op3.args hwt.1]
            rfl
          | load _ a3 _ => dsimp only [denote]; cases denoteArg _ a3 <;> rfl
          | store v3 a3 _ =>
            dsimp only [denote]; cases denoteArg _ v3 <;> cases denoteArg _ a3 <;> rfl
          | call _ _ args3 _ => dsimp only [denote]; cases denoteArgs _ args3 <;> rfl
          | jnz c3 _ _ => dsimp only [denote]; cases denoteArg _ c3 <;> rfl
          | jump j3 args3 =>
            rename_i ts3
            dsimp only [denote]; cases lookupL ls ts3 j3 <;> cases denoteArgs _ args3 <;> rfl
          | ret vs3 => dsimp only [denote]; cases denoteArgs _ vs3 <;> rfl
          | exit _ args3 => dsimp only [denote]; cases denoteArgs _ args3 <;> rfl
          | hlt | group _ _ => rfl
    | let_ op2 _ => dsimp only [denote]; cases denoteArgs _ op2.args <;> rfl
    | load _ a2 _ => dsimp only [denote]; cases denoteArg _ a2 <;> rfl
    | store v2 a2 _ => dsimp only [denote]; cases denoteArg _ v2 <;> cases denoteArg _ a2 <;> rfl
    | call _ _ args2 _ => dsimp only [denote]; cases denoteArgs _ args2 <;> rfl
    | jump j2 args2 =>
      rename_i ts2; dsimp only [denote]
      cases lookupL ls ts2 j2 <;> cases denoteArgs _ args2 <;> rfl
    | ret vs2 => dsimp only [denote]; cases denoteArgs _ vs2 <;> rfl
    | exit _ args2 => dsimp only [denote]; cases denoteArgs _ args2 <;> rfl
    | hlt | group _ _ => rfl
  | load _ a2 _ => dsimp only [denote]; cases denoteArg vs1 a2 <;> rfl
  | store v2 a2 _ => dsimp only [denote]; cases denoteArg vs1 v2 <;> cases denoteArg vs1 a2 <;> rfl
  | call _ _ args2 _ => dsimp only [denote]; cases denoteArgs vs1 args2 <;> rfl
  | jnz c2 _ _ => dsimp only [denote]; cases denoteArg vs1 c2 <;> rfl
  | jump j2 args2 =>
    rename_i ts2; dsimp only [denote]
    cases lookupL ls ts2 j2 <;> cases denoteArgs vs1 args2 <;> rfl
  | ret vs2 => dsimp only [denote]; cases denoteArgs vs1 vs2 <;> rfl
  | exit _ args2 => dsimp only [denote]; cases denoteArgs vs1 args2 <;> rfl
  | hlt | group _ _ => rfl

private theorem deferJnzNextFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vd' : Nat} {ve' : Trie Nat}
    (hΓ : CtxTypes Γ vs) (hvm : TrieProjMatch (fun _ x => x) vd' ve' vs)
    (nv nl ip : Nat) (st1 : SymState I) {ts : List Ty} (op : Op VNat ts)
    (k : TFlat rs) (hwf : k.wfCheck Γ Δ = true) :
    deferJnzNextFlat I h fn vd' ve' nv nl ip st1 op k =
      deferJnzNext I h fn nv nl ip st1 op (denote VNat LNat k vs ls) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    cases t <;> cases ts'
    case bool.nil =>
      cases k with
      | jnz c t e =>
        cases c with
        | imm _ => dsimp only [deferJnzNextFlat, denote, denoteArg]; rfl
        | var cx =>
          dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
          dsimp only [deferJnzNextFlat, denote]
          rw [denoteArg_eq_flatArg hΓ hvm (.var cx) hwf.1.1]
          rfl
      | let_ op2 _ => dsimp only [deferJnzNextFlat, denote]; cases denoteArgs vs op2.args <;> rfl
      | load _ a _ => dsimp only [deferJnzNextFlat, denote]; cases denoteArg vs a <;> rfl
      | store v a _ =>
        dsimp only [deferJnzNextFlat, denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
      | call _ _ args _ => dsimp only [deferJnzNextFlat, denote]; cases denoteArgs vs args <;> rfl
      | jump j args =>
        rename_i tsj
        dsimp only [deferJnzNextFlat, denote]
        cases lookupL ls tsj j <;> cases denoteArgs vs args <;> rfl
      | ret vs' => dsimp only [deferJnzNextFlat, denote]; cases denoteArgs vs vs' <;> rfl
      | exit _ args => dsimp only [deferJnzNextFlat, denote]; cases denoteArgs vs args <;> rfl
      | hlt | group _ _ => rfl
    all_goals rfl

private theorem deferLeaNextFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vd' : Nat} {ve' : Trie Nat}
    (hΓ : CtxTypes Γ vs) (hvm : TrieProjMatch (fun _ x => x) vd' ve' vs)
    (nv ip : Nat) (st1 : SymState I) {ts : List Ty} (op : Op VNat ts)
    (k : TFlat rs) (hwf : k.wfCheck Γ Δ = true) :
    deferLeaNextFlat I h vd' ve' nv ip st1 op k =
      deferLeaNext I h nv ip st1 op (denote VNat LNat k vs ls) := by
  by_cases hcand : isLeaDeferCand I.gpr.deferShiftAlu op.code = true
  · dsimp only [deferLeaNextFlat, deferLeaNext]
    simp only [hcand, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases ts with
    | nil => rfl
    | cons _ ts' =>
      cases ts' with
      | cons _ _ => rfl
      | nil =>
        cases k with
        | let_ op2 k2 =>
          dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
          dsimp only [denote]
          rw [denoteArgs_eq_flatArgs hΓ hvm op2.args hwf.1]
          rfl
        | load _ a _ => dsimp only [denote]; cases denoteArg vs a <;> rfl
        | store v a _ => dsimp only [denote]; cases denoteArg vs v <;> cases denoteArg vs a <;> rfl
        | call _ _ args _ => dsimp only [denote]; cases denoteArgs vs args <;> rfl
        | jnz c _ _ => dsimp only [denote]; cases denoteArg vs c <;> rfl
        | jump j args =>
          rename_i tsj; dsimp only [denote]
          cases lookupL ls tsj j <;> cases denoteArgs vs args <;> rfl
        | ret vs' => dsimp only [denote]; cases denoteArgs vs vs' <;> rfl
        | exit _ args => dsimp only [denote]; cases denoteArgs vs args <;> rfl
        | hlt | group _ _ => rfl
  · simp [deferLeaNextFlat, deferLeaNext, hcand]

private theorem blockTrampoline?Flat_eq {rs : List Ty} (I : Isa) (h : I.Hints)
    (defs : Trie DefFact) (vw : Trie SlotWidth) (lid nv ip : Nat)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    (ts : List Ty) (b : TFlat rs) (hwf : b.wfCheck (pushTypes ts Γ) Δ = true) :
    blockTrampoline?Flat I h defs vw lid vDepth vEnv lEnv nv ip ts b =
      blockTrampoline? I h defs vw lid nv ip (ts := ts)
        (fun xs => denote VNat LNat b (pushTup xs vs) ls) := by
  dsimp only [blockTrampoline?Flat, blockTrampoline?]
  cases h.entry.find? lid with
  | none => rfl
  | some en =>
    dsimp only
    split
    · rfl
    · cases buildEntryBaseZ I h.nslots vw en.live en.liveZ
          { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
      | none => rfl
      | some baseSt =>
        dsimp only
        cases bindBlockParamsZ I h.nslots ts en.ploc en.plocZ nv baseSt with
        | none => rfl
        | some initSt =>
          dsimp only
          have hΓ' := CtxTypes.push (Tup.levels ts nv) hΓ
          have hvm' := trieProjMatch_insertVLevels (ts := ts) (nv := nv) hvm
          cases b with
          | jump j' args' =>
            dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
            have hj := checkJump_eq_true_iff.mp hwf.1
            dsimp only [denote]
            rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ' hvm' args' hwf.2]
            rfl
          | let_ op _ => dsimp only [denote]; cases denoteArgs _ op.args <;> rfl
          | load _ a _ => dsimp only [denote]; cases denoteArg _ a <;> rfl
          | store v a _ => dsimp only [denote]; cases denoteArg _ v <;> cases denoteArg _ a <;> rfl
          | call _ _ args _ => dsimp only [denote]; cases denoteArgs _ args <;> rfl
          | jnz c _ _ => dsimp only [denote]; cases denoteArg _ c <;> rfl
          | ret vs' => dsimp only [denote]; cases denoteArgs _ vs' <;> rfl
          | exit _ args => dsimp only [denote]; cases denoteArgs _ args <;> rfl
          | hlt | group _ _ => rfl

private theorem collectRawFwdsFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints)
    (defs : Trie DefFact) (vw : Trie SlotWidth) (fwd : Trie Nat) (fwdTgts : Trie Bool)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls) :
    {sig : List (List Ty)} → (bodies : TBlocks rs sig) → bodies.wfCheck Γ Δ = true →
    ∀ lid nv nl ip raw lids,
      collectRawFwdsFlat I h defs vw fwd fwdTgts vDepth vEnv lEnv bodies
          lid nv nl ip raw lids =
        collectRawFwds I h defs vw fwd fwdTgts (denoteB VNat LNat bodies vs ls)
          lid nv nl ip raw lids
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, hwf, lid, nv, nl, ip, raw, lids => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [collectRawFwdsFlat, denoteB, collectRawFwds]
    rw [blockTrampoline?Flat_eq I h defs vw lid nv ip hΓ hΔ hvm hlm ts b hwf.1,
      exprIpCountFlat_eq b (CtxTypes.push (Tup.levels ts nv) hΓ) hΔ hwf.1 (nv + ts.length) nl]
    exact collectRawFwdsFlat_eq I h defs vw fwd fwdTgts hΓ hΔ hvm hlm bs hwf.2
      (lid + 1) _ _ _ _ _

private theorem findGroupFwdsFlat_eq {rs : List Ty} (I : Isa) (h : I.Hints) (st : SymState I)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × VNat t)} {ls : List ((ts : List Ty) × LNat ts)}
    {vDepth : Nat} {vEnv : Trie Nat} {lEnv : List Nat}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hvm : TrieProjMatch (fun _ x => x) vDepth vEnv vs) (hlm : ListLblMatch lEnv ls)
    {sig : List (List Ty)} (bodies : TBlocks rs sig) (k : TFlat rs)
    (hwb : bodies.wfCheck Γ (pushTypes sig Δ) = true)
    (hwk : k.wfCheck Γ (pushTypes sig Δ) = true)
    (nv nl ip : Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    findGroupFwdsFlat I h st vDepth vEnv (pushLLevels sig nl lEnv) bodies k nv nl ip fwd fwdTgts =
      findGroupFwds I h st (denoteB VNat LNat bodies vs (pushTup (Tup.levels sig nl) ls))
        (denote VNat LNat k vs (pushTup (Tup.levels sig nl) ls)) nv nl ip fwd fwdTgts := by
  have hΔ' := CtxTypes.push (Tup.levels sig nl) hΔ
  have hlm' := listLblMatch_pushLLevels (sig := sig) (nl := nl) hlm
  dsimp only [findGroupFwdsFlat, findGroupFwds]
  have hk := exprIpCountFlat_eq k hΓ hΔ' hwk nv (nl + sig.length)
  have hc := collectRawFwdsFlat_eq I h st.defs st.vecWidths fwd fwdTgts hΓ hΔ' hvm hlm' bodies hwb
    nl (exprIpCountFlat k nv (nl + sig.length)).1 (exprIpCountFlat k nv (nl + sig.length)).2.1
    (ip + (exprIpCountFlat k nv (nl + sig.length)).2.2) .empty []
  rw [hk] at hc
  rw [hk, hc]
  rfl

/-! ## 3. Core Mutual Simulation & `Rega.lowerFlatFn_eq_lowerFn` -/

mutual
/-- Structural simulation equating `Rega.lowerFlatExpr` on `tf` with `Rega.lowerExpr` on
`denote VNat LNat tf vs ls` under well-formedness and environment correspondence. -/
theorem lowerFlatExpr_eq (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × VNat t)} → {ls : List ((ts : List Ty) × LNat ts)} →
    {vDepth : Nat} → {vEnv : Trie Nat} → {lEnv : List Nat} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieProjMatch (fun _ x => x) vDepth vEnv vs → ListLblMatch lEnv ls →
    tf.wfCheck Γ Δ = true →
    ∀ nv nl ip st ft fwd fwdTgts,
      lowerFlatExpr I h E fn tf vDepth vEnv lEnv nv nl ip st ft fwd fwdTgts =
        lowerExpr I h E fn (denote VNat LNat tf vs ls) nv nl ip st ft fwd fwdTgts
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArgs_eq_flatArgs hΓ hvm op.args hwf.1]
    dsimp only [flatOp]
    unfold lowerExpr
    cases stepPre I h ip st with
    | none => rfl
    | some p =>
      dsimp only
      have hΓ' := CtxTypes.push (Tup.levels ts nv) hΓ
      have hvm' := trieProjMatch_insertVLevels (ts := ts) (nv := nv) hvm
      rw [deferJnzNextFlat_eq I h fn (ls := ls) hΓ' hvm' nv nl ip p.2 _ k hwf.2,
        deferLeaNextFlat_eq I h (ls := ls) hΓ' hvm' nv ip p.2 _ k hwf.2]
      cases lowerOp I h nv ip p.2 ⟨op.code, flatArgs vDepth vEnv op.args⟩ _
          (h.mulHiIps.getD ip false) with
      | none => rfl
      | some q =>
        dsimp only
        rw [lowerFlatExpr_eq I h E fn k hΓ' hΔ hvm' hlm hwf.2 (nv + ts.length) nl (ip + 1)
          q.2 ft fwd fwdTgts]
  | .load t a k, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArg_eq_flatArg hΓ hvm a hwf.1]
    dsimp only [lowerExpr]
    cases stepPre I h ip st with
    | none => rfl
    | some p =>
      dsimp only
      have hΓ' := CtxTypes.cons (a := t) (v := (nv : VNat t)) hΓ
      have hvm' := hvm.cons t (nv : VNat t)
      rw [loadSextNextFlat_eq I h hΓ hΔ hvm hlm nv ip p.2 t _ k hwf.2]
      cases lowerLoad I h nv ip p.2 t (flatArg vDepth vEnv a) _ with
      | none => rfl
      | some q =>
        dsimp only
        rw [lowerFlatExpr_eq I h E fn k hΓ' hΔ hvm' hlm hwf.2 (nv + 1) nl (ip + 1)
          q.2 ft fwd fwdTgts]
  | .store (t := t) v a k, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArg_eq_flatArg hΓ hvm v hwf.1.1, denoteArg_eq_flatArg hΓ hvm a hwf.1.2]
    dsimp only [lowerExpr]
    cases stepPre I h ip st with
    | none => rfl
    | some p =>
      dsimp only
      cases lowerStore I p.2 (h.variant.getD ip .default) t
          (flatArg vDepth vEnv v) (flatArg vDepth vEnv a) with
      | none => rfl
      | some q =>
        dsimp only
        rw [lowerFlatExpr_eq I h E fn k hΓ hΔ hvm hlm hwf.2 nv nl (ip + 1) q.2 ft fwd fwdTgts]
  | .call f (as := as) bs args k, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArgs_eq_flatArgs hΓ hvm args hwf.1]
    dsimp only [lowerExpr]
    cases stepPre I h ip st with
    | none => rfl
    | some p =>
      dsimp only
      split
      · rfl
      · cases I.assignArgs as <;> cases I.assignRets bs <;> try rfl
        rename_i argLocs retLocs
        dsimp only
        cases abiTargets I (flatArgs vDepth vEnv args) argLocs with
        | none => rfl
        | some tgts =>
          dsimp only
          cases shuffle I h.nslots h.saved p.2 tgts (h.deadFlags.getD ip false) with
          | none => rfl
          | some q =>
            dsimp only
            cases bindAbiParams I retLocs nv (afterCallState I h.saved q.2) with
            | none => rfl
            | some st4 =>
              dsimp only
              have hΓ' := CtxTypes.push (Tup.levels bs nv) hΓ
              have hvm' := trieProjMatch_insertVLevels (ts := bs) (nv := nv) hvm
              rw [lowerFlatExpr_eq I h E fn k hΓ' hΔ hvm' hlm hwf.2 (nv + bs.length) nl (ip + 1)
                st4 ft fwd fwdTgts]
  | .jnz c t e, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases c with
    | imm b =>
      dsimp only [lowerFlatExpr, denote, denoteArg, lowerExpr]
      cases stepPre I h ip st with
      | none => rfl
      | some p =>
        dsimp only
        cases b with
        | true =>
          simp only [↓reduceIte]
          rw [lowerFlatExpr_eq I h E fn t hΓ hΔ hvm hlm hwf.1.2 nv nl (ip + 1) p.2 ft fwd fwdTgts]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [lowerFlatExpr_eq I h E fn e hΓ hΔ hvm hlm hwf.2 nv nl (ip + 1) p.2 ft fwd fwdTgts]
    | var cx =>
      dsimp only [lowerFlatExpr, denote]
      rw [denoteArg_eq_flatArg hΓ hvm (.var cx) hwf.1.1]
      dsimp only [flatArg, lowerExpr]
      cases stepPre I h ip st with
      | none => rfl
      | some p =>
        dsimp only
        cases findJnzCond I h.nslots p.2 (flatVar vDepth vEnv cx) with
        | none => rfl
        | some cond =>
          dsimp only
          rw [jnzIpTFlat_eq hΓ hΔ nv nl ip t e hwf.1.2 hwf.2,
            jnzSetupFlat_eq I h fn nl (jnzIpT nv nl ip (denote VNat LNat t vs ls)
              (denote VNat LNat e vs ls)) (ip + 1) p.2 hΓ hΔ hvm hlm t e hwf.1.2 hwf.2
              ft cond fwd]
          cases jnzSetup I h fn nl _ (ip + 1) p.2 _ _ ft cond fwd with
          | none => rfl
          | some s =>
            rcases s with ⟨inv, tgt?, br, stBr⟩
            dsimp only
            rw [lowerFlatExpr_eq I h E fn e hΓ hΔ hvm hlm hwf.2 nv (nl + 1) (ip + 1) stBr _
              fwd fwdTgts]
            cases lowerExpr I h E fn (denote VNat LNat e vs ls) nv (nl + 1) (ip + 1) stBr _
                fwd fwdTgts with
            | error err => rfl
            | ok pe =>
              rcases pe with ⟨ce, nv1, nl1, ip1⟩
              dsimp only
              rw [lowerFlatExpr_eq I h E fn t hΓ hΔ hvm hlm hwf.1.2 nv1 nl1 ip1 stBr _
                fwd fwdTgts]
              cases lowerExpr I h E fn (denote VNat LNat t vs ls) nv1 nl1 ip1 stBr _
                  fwd fwdTgts with
              | error err => rfl
              | ok pt =>
                rcases pt with ⟨ct, nv2, nl2, ip2⟩
                dsimp only
                cases inv with
                | true =>
                  simp only [↓reduceIte]
                  rw [finishJnzBranchFlat_eq I fn hΓ hΔ hvm hlm nl tgt? e hwf.2 br ct ce
                    nv2 nl2 ip2]
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [finishJnzBranchFlat_eq I fn hΓ hΔ hvm hlm nl tgt? t hwf.1.2 br ce ct
                    nv2 nl2 ip2]
  | .jump j args, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hj := checkJump_eq_true_iff.mp hwf.1
    dsimp only [lowerFlatExpr, denote]
    rw [flatLabel_lookupL_eq hΔ hlm hj, denoteArgs_eq_flatArgs hΓ hvm args hwf.2]
    rfl
  | .ret vs', Γ, _, vs, _, vDepth, vEnv, lEnv, hΓ, _, hvm, _, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArgs_eq_flatArgs hΓ hvm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, _, vDepth, vEnv, lEnv, hΓ, _, hvm, _, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf
    dsimp only [lowerFlatExpr, denote]
    rw [denoteArgs_eq_flatArgs hΓ hvm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hΔ' := CtxTypes.push (Tup.levels sig nl) hΔ
    have hlm' := listLblMatch_pushLLevels (sig := sig) (nl := nl) hlm
    dsimp only [lowerFlatExpr, denote, lowerExpr]
    rw [findGroupFwdsFlat_eq I h st hΓ hΔ hvm hlm bodies k hwf.1 hwf.2 nv nl ip fwd fwdTgts]
    rw [firstNonFwdFlat_eq _ bodies vs (pushTup (Tup.levels sig nl) ls) nl ft]
    rw [lowerFlatExpr_eq I h E fn k hΓ hΔ' hvm hlm' hwf.2 nv (nl + sig.length) ip st _ _ _]
    cases lowerExpr I h E fn (denote VNat LNat k vs (pushTup (Tup.levels sig nl) ls))
        nv (nl + sig.length) ip st _ _ _ with
    | error err => rfl
    | ok pk =>
      rcases pk with ⟨ck, nv1, nl1, ip1⟩
      dsimp only
      rw [lowerFlatBlocks_eq I h E fn bodies hΓ hΔ' hvm hlm' hwf.1 nl nv1 nl1 ip1
        st.defs st.vecWidths ft _ _]

/-- Mutual companion to `lowerFlatExpr_eq` over `TBlocks rs sig`. -/
theorem lowerFlatBlocks_eq (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × VNat t)} → {ls : List ((ts : List Ty) × LNat ts)} →
    {vDepth : Nat} → {vEnv : Trie Nat} → {lEnv : List Nat} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieProjMatch (fun _ x => x) vDepth vEnv vs → ListLblMatch lEnv ls →
    tb.wfCheck Γ Δ = true →
    ∀ lid nv nl ip defs vw ft fwd fwdTgts,
      lowerFlatBlocks I h E fn tb lid vDepth vEnv lEnv nv nl ip defs vw ft fwd fwdTgts =
        lowerBlocks I h E fn (denoteB VNat LNat tb vs ls) lid nv nl ip defs vw ft fwd fwdTgts
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, vDepth, vEnv, lEnv, hΓ, hΔ, hvm, hlm, hwf,
      lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [lowerFlatBlocks, denoteB, lowerBlocks]
    cases fwd.find? lid with
    | some fwdTgt =>
      dsimp only
      rw [blockTrampoline?Flat_eq I h defs vw lid nv ip hΓ hΔ hvm hlm ts b hwf.1]
      cases blockTrampoline? I h defs vw lid nv ip (ts := ts)
          (fun xs => denote VNat LNat b (pushTup xs vs) ls) with
      | none => rfl
      | some j' =>
        dsimp only
        split
        · rfl
        · exact lowerFlatBlocks_eq I h E fn bs hΓ hΔ hvm hlm hwf.2
            (lid + 1) (nv + ts.length) nl (ip + 1) defs vw ft fwd fwdTgts
    | none =>
      dsimp only
      cases h.entry.find? lid with
      | none => rfl
      | some en =>
        dsimp only
        split
        · rfl
        · cases buildEntryBaseZ I h.nslots vw en.live en.liveZ
              { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
          | none => rfl
          | some baseSt =>
            dsimp only
            cases bindBlockParamsZ I h.nslots ts en.ploc en.plocZ nv baseSt with
            | none => rfl
            | some initSt =>
              dsimp only
              have hΓ' := CtxTypes.push (Tup.levels ts nv) hΓ
              have hvm' := trieProjMatch_insertVLevels (ts := ts) (nv := nv) hvm
              rw [firstNonFwdFlat_eq fwd bs vs ls (lid + 1) ft]
              rw [lowerFlatExpr_eq I h E fn b hΓ' hΔ hvm' hlm hwf.1 (nv + ts.length) nl ip
                initSt (firstNonFwd fwd (denoteB VNat LNat bs vs ls) (lid + 1) ft) fwd fwdTgts]
              cases lowerExpr I h E fn (denote VNat LNat b (pushTup (Tup.levels ts nv) vs) ls)
                  (nv + ts.length) nl ip initSt _ fwd fwdTgts with
              | error err => rfl
              | ok pb =>
                rcases pb with ⟨cb, nv1, nl1, ip1⟩
                dsimp only
                rw [lowerFlatBlocks_eq I h E fn bs hΓ hΔ hvm hlm hwf.2
                  (lid + 1) nv1 nl1 ip1 defs vw ft fwd fwdTgts]
end

/-- `Rega.lowerFlatFn` produces the exact same machine code (or error) as `Rega.lowerFn f.toFn`
for every closed `TFlatFn` satisfying `f.wfCheck = true`. -/
theorem lowerFlatFn_eq_lowerFn (I : Isa) (h : I.Hints) (E : Ext) (f : TFlatFn)
    (hwf : f.wfCheck = true) :
    lowerFlatFn I h E f = lowerFn I h E f.toFn := by
  dsimp only [lowerFlatFn, lowerFn, TFlatFn.toFn, denoteFunc]
  split
  · rfl
  · cases I.assignArgs f.as <;> cases I.assignRets f.rs <;> try rfl
    rename_i argLocs _
    dsimp only
    cases bindAbiParams I argLocs 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
    | none => rfl
    | some st0 =>
      dsimp only
      have hΓ := CtxTypes.push (Tup.levels f.as 0) (.nil (α := Ty) (f := VNat))
      have hvm := trieProjMatch_insertVLevels (ts := f.as) (nv := 0)
        (TrieProjMatch.empty (α := Ty) (f := VNat) (β := Nat) (fun _ x => x))
      rw [Nat.zero_add] at hvm
      rw [lowerFlatExpr_eq I h E f.name f.body hΓ .nil hvm listLblMatch_empty hwf
        f.as.length 0 0 st0 none .empty .empty]
      rfl

end Rega
end LeanQbe.T
