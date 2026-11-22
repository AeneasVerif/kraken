module

public import LeanQbe.T.RegaLemmas1
public import LeanQbe.T.WPLemmas

/-!
# `T7b` Part 3: Operands, Ops/Loads/Stores, and Structural `LabelsUnique` (Guardrail 5)

* `tryArg_ok`, `pickPArgs_ok`, `tryAddr_ok`, `lowerOp_ok`, `lowerLoad_ok`, `lowerStore_ok`.
* Structural label bounds (`LabelClean`, `lname_inj`, `lowerExpr_labels`/`lowerBlocks_labels`): every
  label emitted by `lowerExpr` is `lname fn j` with `j ∈ [nl, nl')`, pairwise distinct, via monotone
  `nl` (no `O(L^2)` `decide`); `lowerFn_labelsUnique`, `lowerFn_label_mem`, `lowerExpr_nv_le`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## Pure helpers -/

theorem orElse_eq_some {α : Type} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem slotWidthEq_eq {a b : SlotWidth} (h : slotWidthEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [slotWidthEq]

theorem symArgEq_eq {a b : SymArg} (h : symArgEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [symArgEq]
  · rename_i x y; revert h; cases x <;> cases y <;> decide
  · exact slotWidthEq_eq h.1

theorem regLocEq_eq {I : Isa} {a b : RegLoc I.Reg I.VReg I.Cond} (h : regLocEq a b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [regLocEq]

theorem gprSym_match {G : VCtx} {w : BitVec 64} {sa' sa : SymArg} (h : GprSym G w sa')
    (hm : symArgMatchesGpr sa' sa = true) : GprSym G w sa := by
  unfold symArgMatchesGpr at hm
  split at hm
  · next he => rwa [← symArgEq_eq he]
  · split at hm
    · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq] at hm
      obtain ⟨⟨rfl, hle⟩, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      exact ⟨hle, by rw [h.2]⟩
    · simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      rw [h.2]; cases ‹Bool› <;> rfl
    · simp at hm

theorem mem_cons_top {G : VCtx} {nv : Nat} (hlt : ∀ p ∈ G, p.2.2 < nv) {t t' : Ty} {v : Val t}
    {v' : Val t'} (h : (⟨t', v', nv⟩ : (a : Ty) × Val a × VNat a) ∈ ⟨t, v, nv⟩ :: G) :
    (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := by
  rcases List.mem_cons.mp h with h | h
  · cases h; rfl
  · exact absurd (hlt _ h) (Nat.lt_irrefl _)

private theorem bv_add_shiftLeft {w : Nat} (a b : BitVec w) (k : Nat) :
    (a + b) <<< k = (a <<< k) + (b <<< k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem bv_shiftLeft_shiftLeft {w : Nat} (a : BitVec w) (k1 k2 : Nat) :
    (a <<< k1) <<< k2 = a <<< (k1 + k2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.pow_add, Nat.mul_assoc]

private theorem defOk_addVarImm {G : VCtx} {nv x : Nat} {vx c : BitVec 64}
    {defs : Trie DefFact} (hdefs : ∀ y d, defs.find? y = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hm : ⟨i64, vx, x⟩ ∈ G) :
    DefOk (⟨i64, vx + c, nv⟩ :: G) nv (recordAddVarImm defs x c) := by
  unfold recordAddVarImm
  cases hd : defs.find? x with
  | none =>
    intro v hv; cases mem_cons_top hlt hv
    exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩
  | some d =>
    have hdx := hdefs x d hd
    cases d with
    | imm64 c0 =>
      intro v hv; cases mem_cons_top hlt hv
      have hx := hdx vx hm; rw [hx]
    | addImm64 b disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hdx vx hm
      exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx, BitVec.add_assoc]⟩
    | scaleOff idx sh disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vi, hi, hvx⟩ := hdx vx hm
      exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, BitVec.add_assoc]⟩
    | addrSum b idx sh disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, vi, hb, hi, hvx⟩ := hdx vx hm
      exact ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi,
        by simp [hvx, BitVec.add_assoc]⟩
    | andVarVar _ _ _ | andVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ =>
      intro v hv; cases mem_cons_top hlt hv
      exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩

private theorem defOk_addScale {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {dfx : DefFact} {dfy? : Option DefFact} {df : DefFact}
    (hx : DefOk G x dfx) (hy : ∀ d, dfy? = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    (h : recordAddScale dfx dfy? y = some df) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
  unfold recordAddScale at h
  cases dfx with
  | scaleOff idx sh d1 =>
    dsimp only at h
    split at h
    · cases dfy? with
      | some dy =>
        cases dy with
        | addImm64 b d2 =>
          cases h; intro v hv; cases mem_cons_top hlt hv
          obtain ⟨vi, hi, hvx⟩ := hx vx hmx
          obtain ⟨vb, hb, hvy⟩ := hy (.addImm64 b d2) rfl vy hmy
          refine ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi, ?_⟩
          rw [hvx, hvy]; ac_rfl
        | _ =>
          cases h; intro v hv; cases mem_cons_top hlt hv
          obtain ⟨vi, hi, hvx⟩ := hx vx hmx
          refine ⟨vy, vi, List.mem_cons_of_mem _ hmy, List.mem_cons_of_mem _ hi, ?_⟩
          rw [hvx]; ac_rfl
      | none =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vi, hi, hvx⟩ := hx vx hmx
        refine ⟨vy, vi, List.mem_cons_of_mem _ hmy, List.mem_cons_of_mem _ hi, ?_⟩
        rw [hvx]; ac_rfl
    · simp at h
  | _ => simp at h

private theorem defOk_addBase {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {dfx : DefFact} {dfy? : Option DefFact} {df : DefFact}
    (hx : DefOk G x dfx) (hy : ∀ d, dfy? = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    (h : recordAddBase dfx y dfy? = some df) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
  unfold recordAddBase at h
  cases dfx with
  | addImm64 b d1 =>
    cases dfy? with
    | some dy =>
      cases dy with
      | addImm64 b2 d2 =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, hb, hvx⟩ := hx vx hmx
        obtain ⟨vb2, hb2, hvy⟩ := hy (.addImm64 b2 d2) rfl vy hmy
        refine ⟨vb, vb2, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hb2, ?_⟩
        rw [hvx, hvy]; simp only [BitVec.shiftLeft_zero]; ac_rfl
      | _ =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, hb, hvx⟩ := hx vx hmx
        refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
        rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
    | none =>
      cases h; intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hx vx hmx
      refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
      rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
  | _ => simp at h

private theorem defOk_addVarVar {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {defs : Trie DefFact} (hdefs : ∀ z d, defs.find? z = some d → DefOk G z d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (recordAddVarVar defs x y) := by
  let s1 := (defs.find? x).bind (recordAddScale · (defs.find? y) y)
  let s2 := (defs.find? y).bind (recordAddScale · (defs.find? x) x)
  let b1 := (defs.find? x).bind (recordAddBase · y (defs.find? y))
  let b2 := (defs.find? y).bind (recordAddBase · x (defs.find? x))
  have fall : DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (.addrSum x y 0 0) := by
    intro v hv; cases mem_cons_top hlt hv
    exact ⟨vx, vy, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, by simp⟩
  have hs1 : ∀ df, s1 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hs; obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp hs
    exact defOk_addScale (hdefs x dx hdx) (fun d hd => hdefs y d hd) hlt hmx hmy hk
  have hs2 : ∀ df, s2 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hs; obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp hs
    simpa [BitVec.add_comm] using
      defOk_addScale (hdefs y dy hdy) (fun d hd => hdefs x d hd) hlt hmy hmx hk
  have hb1 : ∀ df, b1 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hb; obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp hb
    exact defOk_addBase (hdefs x dx hdx) (fun d hd => hdefs y d hd) hlt hmx hmy hk
  have hb2 : ∀ df, b2 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hb; obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp hb
    simpa [BitVec.add_comm] using
      defOk_addBase (hdefs y dy hdy) (fun d hd => hdefs x d hd) hlt hmy hmx hk
  have hmid : DefOk (⟨i64, vx + vy, nv⟩ :: G) nv
      ((s1 <|> s2 <|> b1 <|> b2).getD (.addrSum x y 0 0)) := by
    cases ho : (s1 <|> s2 <|> b1 <|> b2) with
    | none => exact fall
    | some df =>
      rcases orElse_eq_some ho with h | h
      · exact hs1 df h
      rcases orElse_eq_some h with h | h
      · exact hs2 df h
      rcases orElse_eq_some h with h | h
      · exact hb1 df h
      · exact hb2 df h
  unfold recordAddVarVar; dsimp only
  cases hx : defs.find? x with
  | none =>
    cases hy : defs.find? y with
    | none => simpa [s1, s2, b1, b2, hx, hy] using hmid
    | some dy =>
      cases dy with
      | imm64 c =>
        have hc : vy = c := hdefs y (.imm64 c) hy vy hmy
        subst hc; simpa using defOk_addVarImm hdefs hlt hmx (c := vy)
      | _ => simpa [s1, s2, b1, b2, hx, hy] using hmid
  | some dx =>
    cases dx with
    | imm64 c =>
      have hc : vx = c := hdefs x (.imm64 c) hx vx hmx
      subst hc; simpa [BitVec.add_comm] using defOk_addVarImm hdefs hlt hmy (c := vx)
    | _ =>
      cases hy : defs.find? y with
      | none => simpa [s1, s2, b1, b2, hx, hy] using hmid
      | some dy =>
        cases dy with
        | imm64 c =>
          have hc : vy = c := hdefs y (.imm64 c) hy vy hmy
          subst hc; simpa using defOk_addVarImm hdefs hlt hmx (c := vy)
        | _ => simpa [s1, s2, b1, b2, hx, hy] using hmid

private theorem recordDef_rs {defs : Trie DefFact} {sig rs : List Ty} {code : OpCode sig rs}
    {args : Tup (Arg VNat) sig} {df : DefFact} (hd : recordDef defs code args = some df) :
    ∃ w, rs = [.bits w] := by
  cases code with
  | add t | sub t | shl t | copy t | and t =>
    cases t with
    | bits n => exact ⟨n, rfl⟩
    | _ => simp [recordDef] at hd
  | sext _ n | zext _ n => exact ⟨n, rfl⟩
  | _ => simp [recordDef] at hd

theorem wp_recordDef {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef defs code args = some df) :
    code.wp (vals args₁) (fun rvs => P rvs ∧
      0 < rs.length ∧ DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df) := by
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      have hn : n = 64 := Decidable.byContradiction fun hne => by
        cases a <;> cases b <;> simp [recordDef, hne] at hd
      subst hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | var x =>
        cases b with
        | var y =>
          simp only [recordDef] at hd
          cases hd; cases h1 with | var hmx => cases h2 with | var hmy =>
          simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
            ite_false, Tup.zip, Tup.levels] at hwp ⊢
          exact ⟨hwp, by simp, defOk_addVarVar hdefs hlt hmx hmy⟩
        | imm c =>
          simp only [recordDef] at hd
          cases hd; cases h1 with | var hm => cases h2 with | imm =>
          simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
            ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
          exact ⟨hwp, by simp, defOk_addVarImm hdefs hlt hm⟩
      | imm c =>
        cases b with
        | var y =>
          simp only [recordDef] at hd
          cases hd; cases h1 with | imm => cases h2 with | var hm =>
          simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
            ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, ?_⟩
          rw [BitVec.add_comm]; exact defOk_addVarImm hdefs hlt hm
        | imm _ => simp [recordDef] at hd
    | _ => simp [recordDef] at hd
  | sub t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      have hn : n = 64 := Decidable.byContradiction fun hne => by
        cases a <;> cases b <;> simp [recordDef, hne] at hd
      subst hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | imm _ => simp [recordDef] at hd
      | var x =>
        cases b with
        | var _ => simp [recordDef] at hd
        | imm c =>
          simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
          cases hd; cases h1 with | var hm => cases h2 with | imm =>
          simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
            ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, ?_⟩
          rw [BitVec.sub_eq_add_neg]; exact defOk_addVarImm hdefs hlt hm
    | _ => simp [recordDef] at hd
  | shl t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      cases a with
      | imm _ => simp [recordDef] at hd
      | var x =>
        cases b with
        | var _ => simp [recordDef] at hd
        | imm k =>
          have hn : n = 64 := Decidable.byContradiction fun hne => by
            simp [recordDef, hne] at hd
          subst hn
          have hk : k.toNat < 64 := Decidable.byContradiction fun hke => by
            simp [recordDef, Nat.blt_eq, hke] at hd
          simp only [recordDef] at hd
          split at hd
          · cases hd
          rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
          cases h1 with | var hm => cases h2 with | imm =>
          dsimp only [vals, Arg.val] at hwp ⊢
          simp only [OpCode.wp_shl, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp ⊢
          rw [Nat.mod_eq_of_lt hk] at hwp ⊢
          refine ⟨hwp, by simp, ?_⟩
          cases hdx : defs.find? x with
          | none =>
            rw [hdx] at hd; cases hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
          | some d =>
            rw [hdx] at hd
            have hxok := hdefs x d hdx
            cases d with
            | imm64 c0 =>
              cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
              cases mem_cons_top hlt hv; simp only [DefOk] at hxok; rw [hxok _ hm]
            | addImm64 b d =>
              cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
              cases mem_cons_top hlt hv
              obtain ⟨vb, hb, hvx⟩ := hxok _ hm
              exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx]⟩
            | scaleOff idx sh d =>
              dsimp only at hd; split at hd
              · cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                cases mem_cons_top hlt hv
                obtain ⟨vi, hi, hvx⟩ := hxok _ hm
                exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, bv_shiftLeft_shiftLeft]⟩
              · cases hd
            | addrSum _ _ _ _ | andVarVar _ _ _ | andVarImm _ _ _
            | sextVar _ _ _ | zextVar _ _ _ =>
              cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
              cases mem_cons_top hlt hv
              exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
    | _ => simp [recordDef] at hd
  | copy t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, ⟨⟩⟩
      have hn : n = 64 := Decidable.byContradiction fun hne => by
        cases a <;> simp [recordDef, hne] at hd
      subst hn
      rcases hrel with _ | ⟨h1, -⟩
      cases a with
      | imm c =>
        simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
        cases hd; cases h1 with | imm =>
        simp only [OpCode.wp_copy, vals, Arg.val, BitVec.setWidth_eq] at hwp ⊢
        refine ⟨hwp, by simp, fun v' hm' => ?_⟩
        simp only [Tup.zip, Tup.levels] at hm'; cases mem_cons_top hlt hm'; simp
      | var x =>
        simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
        cases h1 with | var hm =>
        dsimp only [vals, Arg.val] at hwp ⊢
        simp only [OpCode.wp_copy] at hwp ⊢
        refine ⟨hwp, by simp, ?_⟩
        cases hdx : defs.find? x with
        | none =>
          rw [hdx] at hd; cases hd
          intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
        | some d =>
          rw [hdx] at hd
          have h' := hdefs x d hdx
          cases d with
          | imm64 c0 =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            simpa using h' _ hm
          | addImm64 b disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vb, hb, hvx⟩ := h' _ hm
            exact ⟨vb, List.mem_cons_of_mem _ hb, hvx⟩
          | scaleOff idx sh disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vi, hi, hvx⟩ := h' _ hm
            exact ⟨vi, List.mem_cons_of_mem _ hi, hvx⟩
          | addrSum b idx sh disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vb, vi, hb, hi, hvx⟩ := h' _ hm
            exact ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi, hvx⟩
          | andVarVar _ _ _ | andVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ =>
            simp only [DefFact.isAddr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd
            subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
    | _ => simp [recordDef] at hd
  | and t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      have hn : n ≤ 64 := Decidable.byContradiction fun hne => by
        have hbf : Nat.ble n 64 = false := Bool.eq_false_iff.mpr (by simpa [Nat.ble_eq] using hne)
        cases a <;> cases b <;> simp [recordDef, hbf] at hd
      have hbt : Nat.ble n 64 = true := Nat.ble_eq.mpr hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | var x =>
        cases b with
        | var y =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | var hmx => cases h2 with | var hmy =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, _, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, rfl⟩
        | imm c =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | var hmx => cases h2 with | imm =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hmx, by
            rw [BitVec.setWidth_setWidth_of_le c hn, BitVec.setWidth_eq]⟩
      | imm c =>
        cases b with
        | var y =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | imm => cases h2 with | var hmy =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hmy, by
            rw [BitVec.setWidth_setWidth_of_le c hn, BitVec.setWidth_eq, BitVec.and_comm]⟩
        | imm _ => simp [recordDef, hbt] at hd
    | _ => simp [recordDef] at hd
  | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    cases a with
    | imm _ => simp [recordDef] at hd
    | var x =>
      simp only [recordDef] at hd
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
        cases hd
        rcases hrel with _ | ⟨h1, -⟩
        cases h1 with | var hmx =>
        simp only [OpCode.wp_sext, vals, Arg.val, Tup.zip, Tup.levels] at hwp ⊢
        refine ⟨hwp.1, hwp.2, by simp, hc.1.1, hc.1.2, hc.2, fun v hv => ?_⟩
        cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmx, rfl⟩
      · cases hd
  | zext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    cases a with
    | imm _ => simp [recordDef] at hd
    | var x =>
      simp only [recordDef] at hd
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
        cases hd
        rcases hrel with _ | ⟨h1, -⟩
        cases h1 with | var hmx =>
        simp only [OpCode.wp_zext, vals, Arg.val, Tup.zip, Tup.levels] at hwp ⊢
        refine ⟨hwp.1, hwp.2, by simp, hc.1.1, hc.1.2, hc.2, fun v hv => ?_⟩
        cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmx, rfl⟩
      · cases hd
  | _ => simp [recordDef] at hd

theorem recordDef_elide_ok {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef defs code args = some df) :
    ∃ (w : Nat) (_h : rs = [.bits w]) (rvs : Tup Val rs), P rvs ∧
      DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df := by
  obtain ⟨w, hrs⟩ := recordDef_rs hd
  subst hrs
  have hwp' := wp_recordDef hdefs hrel hlt hwp hd
  cases code with
  | add _ =>
    simp only [OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | sub _ =>
    simp only [OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | shl _ =>
    simp only [OpCode.wp_shl, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | copy _ =>
    simp only [OpCode.wp_copy] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | and _ =>
    simp only [OpCode.wp_and] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | sext _ _ =>
    simp only [OpCode.wp_sext] at hwp'
    exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | zext _ _ =>
    simp only [OpCode.wp_zext] at hwp'
    exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | _ => simp [recordDef] at hd

theorem zip_levels_mem {G : VCtx} : ∀ {ts : List Ty} {rvs : Tup Val ts} {nv : Nat} {p},
    p ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx) ++ G → p ∈ G ∨ (nv ≤ p.2.2 ∧ p.2.2 < nv + ts.length)
  | [], _, _, _, h => Or.inl (by simpa [Tup.zip] using h)
  | _ :: _, _, nv, p, h => by
    simp only [Tup.zip, Tup.levels, List.cons_append, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr ⟨Nat.le_refl _, by simp⟩
    · rcases zip_levels_mem h with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Nat.le_of_succ_le h.1, ?_⟩
        rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact h.2

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

/-! ## Operand lookups -/

theorem tryGpr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {sa : SymArg}
    {k : T.Reg → Option α} {res : α} (h : tryGpr T.toIsa st.regs sa k = some res) :
    ∃ r, k r = some res ∧ r ∉ T.frame.scratch ∧ GprSym G (T.mach.getGpr s r) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | gpr r =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨r, hk, by simpa using hc.1, gprSym_match (hA.regs _ hmem) hc.2⟩
    · simp at hk
  | gprZ r =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨r, hk, by simpa using hc.1, gprSym_match (hA.regs _ hmem).1 hc.2⟩
    · simp at hk
  | vec _ | flag _ => simp at hk

theorem findGprFor_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {sa : SymArg} {r : T.Reg}
    (h : findGprFor T.toIsa true st.regs sa = some r) :
    r ∉ T.frame.scratch ∧ GprSym G (T.mach.getGpr s r) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | gpr r' =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Option.some.injEq] at hk; subst hk
      simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hc
      exact ⟨by simpa using hc.1, gprSym_match (hA.regs _ hmem) hc.2⟩
    · simp at hk
  | gprZ r' =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Option.some.injEq] at hk; subst hk
      simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hc
      exact ⟨by simpa using hc.1, gprSym_match (hA.regs _ hmem).1 hc.2⟩
    · simp at hk
  | vec _ | flag _ => simp at hk

theorem tryVec_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {sa : SymArg}
    {k : T.VReg → Option α} {res : α} (h : tryVec T.toIsa st.regs sa k = some res) :
    ∃ v, k v = some res ∧ v ∉ T.vec.vecScratch ∧ VecSym G .w512 (T.mach.getVec s v) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | vec v =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have := hA.regs _ hmem
      rw [symArgEq_eq hc.2] at this
      exact ⟨v, hk, by simpa using hc.1, this⟩
    · simp at hk
  | gpr _ | gprZ _ | flag _ => simp at hk

theorem tryFlag_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond}
    {sa : SymArg} {k : T.Cond → Option α} {res : α}
    (h : tryFlag T.toIsa st.regs pref sa k = some res) :
    ∃ c, k c = some res ∧ FlagSym G (T.mach.evalCond s c) sa := by
  rcases orElse_eq_some h with h | h
  · obtain ⟨c, -, hk⟩ := List.exists_of_findSome?_eq_some h
    split at hk
    · next hc =>
      obtain ⟨⟨sa', rl⟩, hmem, hp⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true] at hp
      have := hA.regs _ hmem
      rw [regLocEq_eq hp.2, symArgEq_eq hp.1] at this
      exact ⟨c, hk, this⟩
    · simp at hk
  · obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
    cases rl with
    | flag c =>
      simp only at hk; split at hk
      · next hc =>
        have := hA.regs _ hmem
        rw [symArgEq_eq hc] at this
        exact ⟨c, hk, this⟩
      · simp at hk
    | gpr _ | gprZ _ | vec _ => simp at hk

theorem tryArg_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond} {t : Ty}
    {a₁ : Arg Val t} {a : Arg VNat t} {k : PArg T.Reg T.VReg T.Cond t → Option α} {res : α}
    (hrel : ArgRel G t a₁ a) (h : tryArg T.toIsa st pref t a k = some res) :
    ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
      (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧ T.mach.PArgHolds s t pa a₁.val := by
  cases hrel with
  | var hm =>
    cases t with
    | bool =>
      rcases orElse_eq_some h with h | h
      · obtain ⟨c, hk, hf⟩ := tryFlag_ok hA h
        exact ⟨.flag c, hk, by simp [PArg.gprs], by simp, (hf _ _ hm).symm⟩
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg _ _ hm⟩
    | bits _ =>
      obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
      exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg _ _ hm⟩
    | pair _ _ =>
      obtain ⟨v, hk, hv, hg⟩ := tryVec_ok hA h
      exact ⟨.vec v, hk, by simp [PArg.gprs], by rintro _ ⟨⟩; exact hv, (hg _ _ hm).2⟩
    | float _ => simp [tryArg] at h
  | imm c =>
    have imm : k (.imm c) = some res → ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
        (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧ T.mach.PArgHolds s t pa (Arg.imm c).val :=
      fun hk => ⟨.imm _, hk, by simp [PArg.gprs], by simp, by cases t <;> rfl⟩
    cases t with
    | bool =>
      rcases orElse_eq_some h with h | h
      · obtain ⟨c', hk, hf⟩ := tryFlag_ok hA h
        exact ⟨.flag c', hk, by simp [PArg.gprs], by simp, hf⟩
      rcases orElse_eq_some h with h | h
      · exact imm h
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg⟩
    | bits w =>
      rcases orElse_eq_some h with h | h
      · exact imm h
      split at h
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        refine ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg.1, ?_⟩
        rw [hg.2]; exact (BitVec.setWidth_setWidth_of_le c (Nat.le_of_ble_eq_true ‹_›)).trans
          (BitVec.setWidth_eq c)
      · simp at h
    | pair a b =>
      rcases orElse_eq_some h with h | h
      · exact imm h
      split at h
      · simp at h
      · obtain ⟨v, hk, hv, hg⟩ := tryVec_ok hA h
        exact ⟨.vec v, hk, by simp [PArg.gprs], by rintro _ ⟨⟩; exact hv,
          immVec_vecHolds (vecWidth?_spec ‹_›).1 hg.2⟩
    | float _ => simp [tryArg] at h

theorem pickPArgs_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond} :
    ∀ {sig : List Ty} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg T.Reg T.VReg T.Cond) sig → Option α} {res : α},
    TRel (ArgRel G) args₁ args → pickPArgs T.toIsa st pref args k = some res →
    ∃ pas, k pas = some res ∧ (∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch) ∧
      (∀ v ∈ tupArgVecs pas, v ∉ T.vec.vecScratch) ∧ TRel (T.mach.PArgHolds s) pas (vals args₁) := by
  intro sig args₁ args k res hrel h
  induction hrel generalizing res with
  | nil => exact ⟨(), h, by simp [tupArgGprs], by simp [tupArgVecs], .nil⟩
  | cons ha _ ih =>
    simp only [pickPArgs] at h
    obtain ⟨pa, hk, hg, hv, hp⟩ := tryArg_ok hA ha h
    obtain ⟨pas, hk', hg', hv', hp'⟩ := ih (k := fun pas => k (pa, pas)) hk
    refine ⟨(pa, pas), hk', ?_, ?_, .cons hp hp'⟩
    · cases pa <;> simp_all [tupArgGprs, PArg.gprs]
    · cases pa <;> simp_all [tupArgVecs]

theorem tryAddr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {vh : VariantHint} {α : Type}
    {a₁ : Arg Val i64} {a : Arg VNat i64} {k : AddrArg T.Reg → Option α} {res : α}
    (hrel : ArgRel G i64 a₁ a) (h : tryAddr T.toIsa st vh a k = some res) :
    ∃ aa, k aa = some res ∧ (∀ r ∈ aa.regs, r ∉ T.frame.scratch) ∧
      aa.eval (T.mach.getGpr s) = a₁.val := by
  have reg : ∀ {r : T.Reg} {d : Int64} {x : BitVec 64}, k (.baseDisp r d) = some res →
      findGprFor T.toIsa true st.regs (.immBits 64 x) = some r ∨
        (∃ y v, findGprFor T.toIsa true st.regs (.var y) = some r ∧ ⟨i64, v, y⟩ ∈ G ∧ x = v) →
      x + d.toBitVec = a₁.val →
      ∃ aa, k aa = some res ∧ (∀ r ∈ aa.regs, r ∉ T.frame.scratch) ∧
        aa.eval (T.mach.getGpr s) = a₁.val := by
    intro r d x hk hr hx
    rcases hr with hr | ⟨y, v, hr, hm, rfl⟩ <;> obtain ⟨hs, hg⟩ := findGprFor_ok hA hr <;>
      refine ⟨.baseDisp r d, hk, by simpa [AddrArg.regs] using hs, ?_⟩
    · simp only [GprSym, BitVec.setWidth_eq] at hg; simp [AddrArg.eval, hg.2, ← hx]
    · have := (hg _ _ hm).2; simp only [BitVec.setWidth_eq] at this; simp [AddrArg.eval, this, ← hx]
  cases hrel with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨.imm c, h, by simp [AddrArg.regs], rfl⟩
    · obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
      exact reg hk (Or.inl hr) (by simp [Arg.val])
  | var hm =>
    rename_i v x
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h
      · rename_i off base d hdef _
        split at h
        · next hd =>
          obtain ⟨rb, hr, hk⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨vb, hmb, hv⟩ := hA.defs _ _ hdef v hm
          exact reg hk (Or.inr ⟨_, _, hr, hmb, rfl⟩) (by simp_all [Arg.val])
        · simp at h
      · simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
      exact reg hk (Or.inr ⟨_, _, hr, hm, rfl⟩) (by simp [Arg.val])
    · split at h
      · next base d hdef =>
        obtain ⟨rb, hr, hk⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vb, hmb, hv⟩ := hA.defs _ _ hdef v hm
        exact reg hk (Or.inr ⟨_, _, hr, hmb, rfl⟩)
          (by simp [Arg.val, hv, Int64.toBitVec_ofBitVec])
      · next base idx sh d hdef =>
        obtain ⟨sc, hsc, r1⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨rb, hrb, r2⟩ := Option.bind_eq_some_iff.mp r1
        obtain ⟨ri, hri, hk⟩ := Option.bind_eq_some_iff.mp r2
        obtain ⟨vb, vi, hmb, hmi, hv⟩ := hA.defs _ _ hdef v hm
        obtain ⟨hsb, hgb⟩ := findGprFor_ok hA hrb
        obtain ⟨hsi, hgi⟩ := findGprFor_ok hA hri
        have hb := (hgb _ _ hmb).2
        have hi := (hgi _ _ hmi).2
        simp only [BitVec.setWidth_eq] at hb hi
        have hsh : sc.shift = sh := by
          rcases sh with _ | _ | _ | _ | _ <;> simp [AddrScale.ofShift?] at hsc <;>
            subst hsc <;> rfl
        refine ⟨.baseIdxDisp rb ri sc (Int64.ofBitVec d), hk, fun r hr => ?_, ?_⟩
        · simp only [AddrArg.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption
        · simp [Arg.val, AddrArg.eval, hb, hi, hv, hsh, Int64.toBitVec_ofBitVec]
      · next c hdef => exact ⟨.imm c, h, by simp [AddrArg.regs], (hA.defs _ _ hdef v hm).symm⟩
      · simp at h

/-! ## `Agree`/`Inv` plumbing -/

theorem Agree.consReg {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (hA : Agree T G nv st s σ) (h : RegLocOk T.mach G s sa rl) (hlt : symArgScopeOk nv sa = true) :
    Agree T G nv { st with regs := (sa, rl) :: st.regs } s σ :=
  { hA with
    regs := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp <;> first | exact h | exact hA.regs p hp
    regs_lt := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp <;> first | exact hlt | exact hA.regs_lt p hp }

theorem isGprTy_ne_pair {I : Isa} {t : Ty} (h : isGprTy I t = true) : ∀ a b, t ≠ .pair a b := by
  rintro a b rfl; simp [isGprTy] at h

/-- One new binder `⟨t, v, nv⟩`, with the vector-width trie possibly gaining an entry at `nv`. -/
theorem Agree.push {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (t : Ty) (v : Val t) (vw' : Trie SlotWidth)
    (hvw0 : ∀ x < nv, vw'.find? x = st.vecWidths.find? x)
    (hvw : ∀ w, vw'.find? nv = some w → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)
    (hvw1 : ∀ x, nv < x → vw'.find? x = none)
    (hty : vw'.find? nv = none → ∀ a b, t ≠ .pair a b) :
    Agree T (⟨t, v, nv⟩ :: G) (nv + 1) { st with vecWidths := vw' } s σ := by
  have top : ∀ {t' : Ty} {v' : Val t'} {x}, ⟨t', v', x⟩ ∈ (⟨t, v, nv⟩ :: G : VCtx) → nv ≤ x →
      x = nv ∧ (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := fun hm hx => by
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact ⟨rfl, rfl⟩
    · exact absurd (hA.ctx_lt _ hm) (Nat.not_lt.mpr hx)
  refine hA.extend (Nat.le_succ nv) (fun p hp => ?_) (fun p hp => ?_) (fun _ hp => List.mem_cons_of_mem _ hp)
    hvw0 (fun x w hx hle => ?_) (fun p hp hle hn => ?_)
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr (Nat.le_refl _)
    · exact Or.inl hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hA.ctx_lt p hp)
  · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact ⟨Nat.lt_succ_self _, fun t' v' hm => by
        obtain ⟨-, he⟩ := top hm (Nat.le_refl _); cases he; exact hvw w hx⟩
    · simp [hvw1 x hlt] at hx
  · obtain ⟨h1, he⟩ := top (x := p.2.2) hp hle
    rw [show p.1 = t from congrArg Sigma.fst he]; exact hty (h1 ▸ hn)

theorem keep_of_frame {s s' : T.mach.MData} {gs : List T.Reg}
    (hk : T.mach.KeepsGpr s s' (gs ++ T.frame.scratch))
    (hgs : ∀ r ∈ gs, isAllocGpr T.toIsa hints.saved r = true) :
    ∀ r, isMoveGpr T.toIsa hints.saved r = false → T.mach.getGpr s' r = T.mach.getGpr s r := by
  intro r hr
  simp only [isMoveGpr, Bool.or_eq_false_iff] at hr
  refine hk r fun hm => ?_
  rcases List.mem_append.mp hm with hm | hm
  · simp [hgs r hm] at hr
  · simp [hm] at hr

theorem Inv.store {zl : Bool} {m : Mem 64} {s s' : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {a : BitVec 64} {v : Val t} (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hk : T.mach.KeepsGpr s s' T.frame.scratch) (hok : storeOk m t a)
    (hm : T.mach.mem s' = storeMem (T.mach.mem s) t a v) :
    Inv T hints s₀ ra n Rf (storeMem m t a v) s' σ zl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  refine ⟨h1, ?_, fun r hr hns => ?_, ?_, h5, h6, h7⟩
  · rw [hk _ T.frameSpec.sp_disj.1]; exact h2
  · rw [hk r (fun h => (T.frameSpec.scratch_disj r h).2.1 hr)]; exact h3 r hr hns
  · rw [hm]; exact storeMem_frame h4 hok v

/-! ## Loads and stores -/

theorem lowerLoad_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {a₁ : Arg Val i64} {a : Arg VNat i64}
    (hrel : ArgRel G i64 a₁ a) (hl : lowerLoad T.toIsa hints nv ip st t a = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    {v : Val t} (hv : loadVal m t a₁.val = some v)
    (kont : ∀ s', Agree T (⟨t, v, nv⟩ :: G) (nv + 1) st' s' σ →
      MemDefsOk (⟨t, v, nv⟩ :: G) m (nv + 1) st'.memDefs → Inv T hints s₀ ra n Rf m s' σ zl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hload : ∀ (aa : AddrArg T.Reg), aa.eval (T.mach.getGpr s) = a₁.val →
      loadVal (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) = some v :=
    fun aa hev => by rw [hev]; exact loadVal_frame hI.2.2.2.1 hv
  have hMgrow : MemDefsOk (⟨t, v, nv⟩ :: G) m (nv + 1) st.memDefs :=
    hM.grow (Nat.le_succ _)
      (fun p hp => (List.mem_cons.mp hp).elim (fun h => Or.inr (h ▸ Nat.le_refl _)) Or.inl)
      (fun _ h => List.mem_cons_of_mem _ h)
  unfold lowerLoad at hl
  split at hl
  · split at hl
    · rename_i hgt
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      have hpush := hA.push t v st.vecWidths (fun _ _ => rfl)
        (fun w h => absurd (hA.vw_lt _ _ h) (Nat.lt_irrefl _))
        (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
          absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
        (fun _ => isGprTy_ne_pair hgt)
      simpa using kont s { hpush with } (hM.insert hA.ctx_lt hrel hv) hI
    · simp at hl
  split at hl
  · next d _ =>
    split at hl
    · simp at hl
    · next hcond =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hcond
      obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      by_cases hzu : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) = true
      · simp only [Bool.and_eq_true] at hzu
        have ht32 : t = .bits 32 := by
          cases t <;> simp [tyEq] at hzu; exact congrArg Ty.bits hzu.2
        subst ht32
        have hzu1 : T.toIsa.gpr.zeroUpper32Load = true := hzu.1
        refine T.gprSpec.load_zero32 hzu1 hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg
          (hload aa hev) hc fun s' ⟨hg, hm⟩ hfr => kont s' ?_ hMgrow ?_
        · have hk := hA.kill hfr
          refine (hk.push (.bits 32) v _ (fun _ _ => rfl)
            (fun w h => absurd (hk.vw_lt _ _ h) (Nat.lt_irrefl _))
            (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
              absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
            (fun _ a b h => by cases h)).consReg (sa := .var nv)
            (rl := if T.toIsa.gpr.zeroUpper32Load && tyEq (.bits 32) (.bits 32)
              then RegLoc.gprZ d else .gpr d) ?_ (by simp [symArgScopeOk])
          simp only [hzu1, tyEq]
          refine ⟨fun t' v' hm' => ?_, fun v' hm' => ?_⟩
          · cases mem_cons_top hA.ctx_lt hm'
            exact ⟨by decide, by rw [hg, BitVec.setWidth_setWidth_of_le _ (by decide),
              BitVec.setWidth_eq]⟩
          · cases mem_cons_top hA.ctx_lt hm'; exact hg
        · exact hI.keep hm (keep_of_frame (gs := [d]) hfr.1 (by simpa using hcond.1))
      · have hzuf : (T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32)) = false := by
          cases hb : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) <;> simp_all
        refine T.gprSpec.load_spec hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg
          (hload aa hev) hc fun s' ⟨hg, hm⟩ hfr => kont s' ?_ hMgrow ?_
        · have hk := hA.kill hfr
          have hpush := hk.push t v _ (fun _ _ => rfl)
            (fun w h => absurd (hk.vw_lt _ _ h) (Nat.lt_irrefl _))
            (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
              absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
            (fun _ => isGprTy_ne_pair hcond.2)
          have hr1 := hpush.consReg (sa := .var nv) (rl := .gpr d)
            (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hg)
            (by simp [symArgScopeOk])
          simpa [hzuf] using hr1
        · exact hI.keep hm (keep_of_frame (gs := [d]) hfr.1 (by simpa using hcond.1))
  · next vd _ =>
    obtain ⟨w, hw, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl
    · simp at hl
    · next hcond =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcond
      obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      refine T.vecSpec.vload_spec hk (not_vecScratch_of_isAllocVec hcond) hreg (hload aa hev) hc
        fun s' ⟨hg, hm⟩ hfr => kont s' ?_ hMgrow ?_
      · have hk := hA.kill hfr
        refine (hk.push t v _ (fun x hx => Trie.find?_insert_ne _ _ (Nat.ne_of_lt hx))
          (fun w' h => ?_) (fun x hx => ?_) (fun h => by simp [Trie.find?_insert_self] at h)).consReg (sa := .var nv)
          (rl := .vec vd) (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hg.1, hg⟩)
          (by simp [symArgScopeOk])
        · simp only [Trie.find?_insert_self, Option.some.injEq] at h; subst h; exact vecWidth?_spec hw
        · rw [Trie.find?_insert_ne _ _ (Nat.ne_of_gt hx)]
          exact Option.eq_none_iff_forall_ne_some.mpr fun w h =>
            absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx))
      · exact hI.keep hm (keep_of_frame (gs := []) hfr.1 (by simp))
  · simp at hl

theorem lowerStore_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {vh : VariantHint}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {v₁ : Arg Val t} {v : Arg VNat t}
    {a₁ : Arg Val i64} {a : Arg VNat i64} (hv : ArgRel G t v₁ v) (ha : ArgRel G i64 a₁ a)
    (hl : lowerStore T.toIsa st vh t v a = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl) (hok : storeOk m t a₁.val)
    (kont : ∀ s', Agree T G nv st' s' σ →
      MemDefsOk G (storeMem m t a₁.val v₁.val) nv st'.memDefs →
      Inv T hints s₀ ra n Rf (storeMem m t a₁.val v₁.val) s' σ zl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hsok : ∀ (aa : AddrArg T.Reg), aa.eval (T.mach.getGpr s) = a₁.val →
      storeOk (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) :=
    fun aa hev => by rw [hev]; exact storeOk_frame hI.2.2.2.1 hok
  cases t with
  | pair x y =>
    simp only [lowerStore] at hl
    obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
    cases heq
    obtain ⟨pa, hk, -, hpv, hp⟩ := tryArg_ok hA hv hta
    cases pa with
    | vec vs =>
      obtain ⟨aa, hk', hreg, hev⟩ := tryAddr_ok hA ha hk
      refine T.vecSpec.vstore_spec hk' hreg (hpv vs rfl) hp (hsok aa hev) hc
        fun s' hm hfr => kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) ?_
      rw [hev] at hm
      exact hI.store hfr.1 hok hm
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl
    split at hl
    · simp at hl
    · obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨pa, hk, hpg, -, hp⟩ := tryArg_ok hA hv hta
      obtain ⟨aa, hk', hreg, hev⟩ := tryAddr_ok hA ha hk
      refine T.gprSpec.store_spec hk' (fun r hr => ?_) hp (hsok aa hev) hc
        fun s' hm hfr => kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) ?_
      · exact (List.mem_append.mp hr).elim (hpg r) (hreg r)
      · rw [hev] at hm
        exact hI.store hfr.1 hok hm

/-! ## Operations -/

/-- Per-destination typing facts checked by `resolveDsts`. -/
def DstsOk (I : Isa) : {ts : List Ty} → Tup (PDst I.Reg I.VReg I.Cond) ts → Prop
  | [], () => True
  | t :: _, (.gpr _, ds) => isGprTy I t = true ∧ DstsOk I ds
  | t :: _, (.vec _, ds) => (vecWidth? I t).isSome = true ∧ DstsOk I ds
  | _ :: _, (.flag _, ds) => DstsOk I ds

theorem resolveDsts_spec {I : Isa} {h : I.Hints} :
    ∀ {ts : List Ty} {nv : Nat} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts},
    resolveDsts I h ts nv = some dsts →
    (∀ r ∈ tupDstGprs dsts, isAllocGpr I h.saved r = true) ∧
      (∀ v ∈ tupDstVecs dsts, isAllocVec I v = true) ∧ DstsOk I dsts
  | [], _, _, _ => by simp [tupDstGprs, tupDstVecs, DstsOk]
  | t :: ts, nv, dsts, hr => by
    simp only [resolveDsts] at hr
    split at hr <;> (try split at hr) <;> (try (simp at hr; done))
    all_goals
      cases hr; have := resolveDsts_spec ‹resolveDsts _ _ _ _ = _›
      simp_all [tupDstGprs, tupDstVecs, DstsOk]

/-- Conclusion of `bindDsts_ok` for new binders `[nv, nv + len)`, old state `(regs, vw)`, result `r`. -/
def BindOk (T : Target) (G' : VCtx) (s' : T.mach.MData) (nv len : Nat)
    (regs : List (SymArg × RegLoc T.Reg T.VReg T.Cond)) (vw : Trie SlotWidth)
    (r : List (SymArg × RegLoc T.Reg T.VReg T.Cond) × Trie SlotWidth) : Prop :=
  (∀ p ∈ r.1, p ∈ regs ∨ (RegLocOk T.mach G' s' p.1 p.2 ∧ symArgScopeOk (nv + len) p.1 = true)) ∧
  (∀ x < nv, r.2.find? x = vw.find? x) ∧
  (∀ x w, r.2.find? x = some w → nv ≤ x → vw.find? x = some w ∨
    (x < nv + len ∧ ∀ t v, ⟨t, v, x⟩ ∈ G' → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)) ∧
  (∀ t v x, ⟨t, v, x⟩ ∈ G' → nv ≤ x → r.2.find? x = none → ∀ a b, t ≠ .pair a b)

theorem bindDsts_ok {G' : VCtx} {s' : T.mach.MData} :
    ∀ {ts : List Ty} (dsts : Tup (PDst T.Reg T.VReg T.Cond) ts) (rvs : Tup Val ts) (nv : Nat)
      (regs : List (SymArg × RegLoc T.Reg T.VReg T.Cond)) (vw : Trie SlotWidth),
    TRel (T.mach.PDstHolds s') dsts rvs → DstsOk T.toIsa dsts →
    (∀ t v x, ⟨t, v, x⟩ ∈ G' → nv ≤ x → ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx)) →
    BindOk T G' s' nv ts.length regs vw (bindDsts T.toIsa dsts nv (regs, vw))
  | [], _, _, _, _, _, _, _, hG =>
    ⟨fun _ hp => Or.inl hp, fun _ _ => rfl, fun _ _ hx _ => Or.inl hx, fun t v x hm hx _ =>
      absurd (hG t v x hm hx) (by simp [Tup.zip])⟩
  | t :: ts, (d, ds), (rv, rvs), nv, regs, vw, .cons hd hds, hdo, hG => by
    have hG' : ∀ t v x, ⟨t, v, x⟩ ∈ G' → nv + 1 ≤ x →
        ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts (nv + 1)) : VCtx) := fun t' v' x hm hx => by
      rcases List.mem_cons.mp (hG t' v' x hm (Nat.le_of_succ_le hx)) with he | he
      · cases he; exact absurd hx (Nat.lt_irrefl _)
      · exact he
    have top : ∀ t' v', ⟨t', v', nv⟩ ∈ G' → (⟨t', v'⟩ : Sigma Val) = ⟨t, rv⟩ := fun t' v' hm => by
      rcases List.mem_cons.mp (hG t' v' nv hm (Nat.le_refl _)) with he | he
      · cases he; rfl
      · have := (zip_levels_mem (G := []) (List.mem_append_left [] he)).resolve_left (by simp)
        exact absurd this.1 (Nat.not_succ_le_self _)
    have hsc : symArgScopeOk (nv + (ts.length + 1)) (.var nv) = true := by simp [symArgScopeOk]
    have hlen : nv + 1 + ts.length = nv + (ts.length + 1) := by omega
    have step : ∀ (rl : RegLoc T.Reg T.VReg T.Cond) (vw' : Trie SlotWidth), DstsOk T.toIsa ds →
        RegLocOk T.mach G' s' (.var nv) rl → (∀ x < nv, vw'.find? x = vw.find? x) →
        (∀ x w, vw'.find? x = some w → nv ≤ x → vw.find? x = some w ∨ (x < nv + (ts.length + 1) ∧
          ∀ t v, ⟨t, v, x⟩ ∈ G' → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)) →
        (vw'.find? nv = none → ∀ a b, t ≠ .pair a b) →
        BindOk T G' s' nv (ts.length + 1) regs vw
          (bindDsts T.toIsa ds (nv + 1) ((.var nv, rl) :: regs, vw')) := by
      intro rl vw' hdo' hrl h0 h1 h2
      obtain ⟨ih1, ih2, ih3, ih4⟩ := bindDsts_ok ds rvs (nv + 1) ((.var nv, rl) :: regs) vw' hds hdo' hG'
      refine ⟨fun p hp => ?_, fun x hx => ?_, fun x w hx hle => ?_, fun t' v' x hm hle hn => ?_⟩
      · rcases ih1 p hp with hp | hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr ⟨hrl, hsc⟩
          · exact Or.inl hp
        · exact Or.inr ⟨hp.1, hlen ▸ hp.2⟩
      · rw [ih2 x (Nat.lt_succ_of_lt hx), h0 x hx]
      · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · rw [ih2 _ (Nat.lt_succ_self _)] at hx; exact h1 _ _ hx (Nat.le_refl _)
        · rcases ih3 x w hx hlt with hx | hx
          · exact h1 x w hx (Nat.le_of_lt hlt)
          · exact Or.inr ⟨hlen ▸ hx.1, hx.2⟩
      · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · rw [ih2 _ (Nat.lt_succ_self _)] at hn
          cases top t' v' hm; exact h2 hn
        · exact ih4 t' v' x hm hlt hn
    cases d with
    | gpr r =>
      exact step (.gpr r) vw hdo.2 (fun t' v' hm => by cases top t' v' hm; exact hd)
        (fun _ _ => rfl) (fun _ _ h _ => Or.inl h) (fun _ => isGprTy_ne_pair hdo.1)
    | vec vr =>
      obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp hdo.1
      have e : (bindDsts T.toIsa (ts := t :: ts) (PDst.vec vr, ds) nv (regs, vw)) =
          bindDsts T.toIsa ds (nv + 1) ((.var nv, .vec vr) :: regs, vw.insert nv w0) := by
        simp [bindDsts, hw0]
      rw [e]
      refine step (.vec vr) _ hdo.2 (fun t' v' hm => by cases top t' v' hm; exact ⟨hd.1, hd⟩)
        (fun x hx => Trie.find?_insert_ne _ _ (Nat.ne_of_lt hx)) (fun x w hx hle => ?_)
        (fun h => by simp [Trie.find?_insert_self] at h)
      rw [Trie.find?_insert] at hx; split at hx
      · cases hx; subst_vars
        exact Or.inr ⟨by omega, fun t' v' hm => by cases top t' v' hm; exact vecWidth?_spec hw0⟩
      · exact Or.inl hx
    | flag c =>
      exact step (.flag c) vw hdo (fun t' v' hm => by cases top t' v' hm; exact hd.symm)
        (fun _ _ => rfl) (fun _ _ h _ => Or.inl h) (fun _ => by simp)

private theorem cmpOp_evalBits_signExtend {m n : Nat} (_hm : 0 < m) (hmn : m < n)
    {co : CmpOp} (hco : cmpIsSignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hc : (c.truncate m).signExtend n = c) :
    co.evalBits (a.signExtend n) c = co.evalBits a (c.truncate m) := by
  have hle : m ≤ n := Nat.le_of_lt hmn
  have ha : (a.signExtend n).toInt = a.toInt := BitVec.toInt_signExtend_of_le hle
  have hci : c.toInt = (c.truncate m).toInt :=
    calc c.toInt = ((c.truncate m).signExtend n).toInt := congrArg BitVec.toInt hc.symm
      _ = (c.truncate m).toInt := BitVec.toInt_signExtend_of_le hle
  have heq : (a.signExtend n = c) ↔ (a = c.truncate m) :=
    ⟨fun h => BitVec.eq_of_toInt_eq (by rw [← ha, h, hci]), fun h => by rw [h, hc]⟩
  cases co <;> simp only [cmpIsSignedOrEq] at hco <;> try (cases hco; done)
  all_goals simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, Ne, ha, hci, heq]

private theorem cmpOp_evalBits_zeroExtend {m n : Nat} (hmn : m < n)
    {co : CmpOp} (hco : cmpIsUnsignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hc : (c.truncate m).zeroExtend n = c) :
    co.evalBits (a.zeroExtend n) c = co.evalBits a (c.truncate m) := by
  have hle : m ≤ n := Nat.le_of_lt hmn
  have ha : (a.zeroExtend n).toNat = a.toNat := by
    change (a.setWidth n).toNat = a.toNat
    rw [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hle))]
  have hcn : c.toNat = (c.truncate m).toNat := by
    calc c.toNat = ((c.truncate m).setWidth n).toNat := congrArg BitVec.toNat hc.symm
      _ = (c.truncate m).toNat := by
        rw [BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (c.truncate m).isLt
            (Nat.pow_le_pow_right (by decide) hle))]
  have heq : (a.zeroExtend n = c) ↔ (a = c.truncate m) :=
    ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← ha, h, hcn]), fun h => by rw [h, hc]⟩
  cases co <;> simp only [cmpIsUnsignedOrEq] at hco <;> try (cases hco; done)
  all_goals simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, Ne, ha, hcn, heq]

private theorem tryTestMemVar_ok {zl : Bool} {G : VCtx} {nv w x k : Nat} {neg : Bool}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vx : BitVec w} {other₁ : Arg Val (.bits w)} {other : Arg VNat (.bits w)}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmx : ⟨.bits w, vx, x⟩ ∈ G)
    (hrel : ArgRel G (.bits w) other₁ other) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryTestMemVar T.toIsa st neg w x other pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (vx &&& other₁.val) 0#w) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryTestMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at h
      split at h
      · rename_i heq
        have hw : w' = w := Nat.beq_eq.mp heq
        subst hw
        obtain ⟨-, hlv0⟩ := hM x (.bits w') addr hmd
        obtain ⟨a₁, ha₁, hlv⟩ := hlv0 vx hmx
        obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA ha₁ h
        obtain ⟨pb, hk2, hpb, -, hphp⟩ := tryArg_ok hA hrel hk1
        have hlm : loadVal (T.mach.mem s) (.bits w') (aa.eval (T.mach.getGpr s)) = some vx := by
          rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
        exact T.gprSpec.testMem_spec hk2
          (fun r hr => (List.mem_append.mp hr).elim (hreg r) (hpb r)) hdg hlm hphp
      · simp at h
    | _ => simp [hmd] at h

private theorem tryTestFuse_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {neg : Bool}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vt : BitVec w} {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmt : ⟨.bits w, vt, t⟩ ∈ G)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryTestFuse T.toIsa st neg w t pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits vt 0#w) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryTestFuse at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm w' x ci =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hne
        have hw : w' = w := Nat.beq_eq.mp (by simpa using hne)
        subst hw
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, hmx, rfl⟩ := hfun vt hmt
        rcases orElse_eq_some h with h1 | h2
        · exact tryTestMemVar_ok hA hI hM hmx (.imm (ci.setWidth w')) hdg h1
        · obtain ⟨pa, hk, hpa, -, hphp⟩ := tryArg_ok hA (.var hmx) h2
          exact T.gprSpec.testOp_spec hk (by simpa [PArg.gprs] using hpa) hdg hphp rfl
    | andVarVar w' x y =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hne
        have hw : w' = w := Nat.beq_eq.mp (by simpa using hne)
        subst hw
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, vy, hmx, hmy, rfl⟩ := hfun vt hmt
        rcases orElse_eq_some h with h1 | h
        · exact tryTestMemVar_ok hA hI hM hmx (.var hmy) hdg h1
        rcases orElse_eq_some h with h2 | h3
        · simpa [BitVec.and_comm] using tryTestMemVar_ok hA hI hM hmy (.var hmx) hdg h2
        · obtain ⟨pa, hk1, hpa, -, hpaH⟩ := tryArg_ok hA (.var hmx) h3
          obtain ⟨pb, hk2, hpb, -, hpbH⟩ := tryArg_ok hA (.var hmy) hk1
          exact T.gprSpec.testOp_spec hk2
            (fun r hr => (List.mem_append.mp hr).elim (hpa r) (hpb r)) hdg hpaH hpbH
    | _ => simp [hdef] at h

private theorem tryExtCmp_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {vh : VariantHint}
    {co : CmpOp} {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vt ci : BitVec w} {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive}
    {clob : FlagMask} (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmt : ⟨.bits w, vt, t⟩ ∈ G)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryExtCmp T.toIsa st vh co w t ci pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd (co.evalBits vt ci) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryExtCmp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hgd
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
          beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨rfl, hm0⟩, hmn⟩, hco⟩, hci⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        have hev := cmpOp_evalBits_signExtend hm0 hmn hco va ci hci
        rcases orElse_eq_some h with h1 | h2
        · cases hmd : st.memDefs.find? x with
          | none => simp [hmd] at h1
          | some p =>
            rcases p with ⟨tm, addr⟩
            cases tm with
            | bits m' =>
              simp only [hmd] at h1
              split at h1
              · rename_i hmeq
                have hm' : m' = mw := Nat.beq_eq.mp hmeq
                subst hm'
                obtain ⟨-, hlv0⟩ := hM x (.bits m') addr hmd
                obtain ⟨a₁, ha₁, hlv⟩ := hlv0 va hmx
                obtain ⟨aa, hk, hreg, haev⟩ := tryAddr_ok hA ha₁ h1
                have hlm : loadVal (T.mach.mem s) (.bits m') (aa.eval (T.mach.getGpr s)) =
                    some va := by
                  rw [haev]; exact loadVal_frame hI.2.2.2.1 hlv
                rw [hev]
                exact T.gprSpec.cmpMem_spec hk (by simpa [PArg.gprs] using hreg) hdg hlm rfl
              · simp at h1
            | _ => simp [hmd] at h1
        · split at h2
          · obtain ⟨rx, hk, hrx, hgx⟩ := tryGpr_ok hA h2
            intro hc hkont
            refine T.gprSpec.op_spec (P := fun r => r = (co.evalBits va (ci.truncate mw), ()))
              hk (by simpa [tupArgGprs, PArg.gprs] using hrx)
              (by simpa [tupDstGprs] using hdg)
              (.cons (hgx _ _ hmx) (.cons rfl .nil)) (by simp [OpCode.wp_cmp, liftCmp]) hc
              fun s' ⟨⟨⟨b, ⟨⟩⟩, hb, hpd⟩, hm⟩ hfr => ?_
            cases hb
            cases hpd with | cons hd _ =>
            exact hkont s' ⟨hev ▸ hd, hm⟩ (by simpa [tupDstGprs] using hfr)
          · simp at h2
    | zextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hgd
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
          beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨rfl, _hm0⟩, hmn⟩, hco⟩, hci⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        have hev := cmpOp_evalBits_zeroExtend hmn hco va ci hci
        rcases orElse_eq_some h with h1 | h2
        · cases hmd : st.memDefs.find? x with
          | none => simp [hmd] at h1
          | some p =>
            rcases p with ⟨tm, addr⟩
            cases tm with
            | bits m' =>
              simp only [hmd] at h1
              split at h1
              · rename_i hmeq
                have hm' : m' = mw := Nat.beq_eq.mp hmeq
                subst hm'
                obtain ⟨-, hlv0⟩ := hM x (.bits m') addr hmd
                obtain ⟨a₁, ha₁, hlv⟩ := hlv0 va hmx
                obtain ⟨aa, hk, hreg, haev⟩ := tryAddr_ok hA ha₁ h1
                have hlm : loadVal (T.mach.mem s) (.bits m') (aa.eval (T.mach.getGpr s)) =
                    some va := by
                  rw [haev]; exact loadVal_frame hI.2.2.2.1 hlv
                rw [hev]
                exact T.gprSpec.cmpMem_spec hk (by simpa [PArg.gprs] using hreg) hdg hlm rfl
              · simp at h1
            | _ => simp [hmd] at h1
        · split at h2
          · obtain ⟨rx, hk, hrx, hgx⟩ := tryGpr_ok hA h2
            intro hc hkont
            refine T.gprSpec.op_spec (P := fun r => r = (co.evalBits va (ci.truncate mw), ()))
              hk (by simpa [tupArgGprs, PArg.gprs] using hrx)
              (by simpa [tupDstGprs] using hdg)
              (.cons (hgx _ _ hmx) (.cons rfl .nil)) (by simp [OpCode.wp_cmp, liftCmp]) hc
              fun s' ⟨⟨⟨b, ⟨⟩⟩, hb, hpd⟩, hm⟩ hfr => ?_
            cases hb
            cases hpd with | cons hd _ =>
            exact hkont s' ⟨hev ▸ hd, hm⟩ (by simpa [tupDstGprs] using hfr)
          · simp at h2
    | _ => simp [hdef] at h

private theorem tryCmpMemVar_ok {zl : Bool} {G : VCtx} {nv w x k : Nat} {co : CmpOp}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vx : BitVec w} {other₁ : Arg Val (.bits w)} {other : Arg VNat (.bits w)}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmx : ⟨.bits w, vx, x⟩ ∈ G)
    (hrel : ArgRel G (.bits w) other₁ other) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryCmpMemVar T.toIsa st co w x other pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd (co.evalBits vx other₁.val) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryCmpMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at h
      split at h
      · rename_i heq
        have hw : w' = w := Nat.beq_eq.mp heq
        subst hw
        obtain ⟨-, hlv0⟩ := hM x (.bits w') addr hmd
        obtain ⟨a₁, ha₁, hlv⟩ := hlv0 vx hmx
        obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA ha₁ h
        obtain ⟨pb, hk2, hpb, -, hphp⟩ := tryArg_ok hA hrel hk1
        have hlm : loadVal (T.mach.mem s) (.bits w') (aa.eval (T.mach.getGpr s)) = some vx := by
          rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
        exact T.gprSpec.cmpMem_spec hk2
          (fun r hr => (List.mem_append.mp hr).elim (hreg r) (hpb r)) hdg hlm hphp
      · simp at h
    | _ => simp [hmd] at h

private theorem tryFuseCmp_ok {zl : Bool} {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P : Tup Val ts → Prop} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch) (hwp : code.wp (vals args₁) P)
    (h : tryFuseCmp T.toIsa st vh code args dsts = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  cases code with
  | cmp co ty mty hm =>
    cases ty with
    | bits w =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩
        rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
        have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch := fun r hr =>
          hdg r (by simpa [tupDstGprs] using hr)
        have hP : P (co.evalBits a₁.val b₁.val, ()) := by
          simpa [OpCode.wp_cmp, vals, liftCmp] using hwp
        have wrap : ∀ {bval : Bool}, bval = co.evalBits a₁.val b₁.val →
            T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
              (fun s' => T.mach.PDstHolds s' .bool pd bval ∧ T.mach.mem s' = T.mach.mem s) post →
            T.mach.FallsTo T.gpr.condReads host k c
              (tupDstGprs (ts := [.bool]) (pd, ()) ++ T.frame.scratch) [] clob s
              (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') (as := [.bool]) (pd, ()) rvs) ∧
                T.mach.mem s' = T.mach.mem s) post := by
          intro bval heq hft hc hkont
          refine hft hc fun s' ⟨hd, hms⟩ hfr =>
            hkont s' ⟨⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons (heq ▸ hd) .nil⟩, hms⟩
              (by simpa [tupDstGprs] using hfr)
        unfold tryFuseCmp at h
        dsimp only at h
        split at h
        · simp at h
        rcases orElse_eq_some h with ht | h
        · split at ht
          · rename_i hco
            have hcoEq : (if co == .ne then CmpOp.ne else CmpOp.eq) = co := by
              cases co <;> simp at hco ⊢
            cases a with
            | var t =>
              cases b with
              | imm c0 =>
                dsimp only at ht
                split at ht
                · rename_i hc0
                  have hc0' : c0 = 0#w := beq_iff_eq.mp hc0
                  cases ha with | var hmt => cases hb with | imm =>
                  refine wrap (by rw [hcoEq, hc0']; rfl)
                    (tryTestFuse_ok hA hI hM hmt hdg1 ht)
                · simp at ht
              | var _ => simp at ht
            | imm c0 =>
              cases b with
              | var t =>
                dsimp only at ht
                split at ht
                · rename_i hc0
                  have hc0' : c0 = 0#w := beq_iff_eq.mp hc0
                  cases ha with | imm => cases hb with | var hmt =>
                  refine wrap ?_ (tryTestFuse_ok hA hI hM hmt hdg1 ht)
                  rw [hcoEq, ← CmpOp.swap_evalBits]
                  cases co <;> simp [CmpOp.swap, hc0'] at hco ⊢
                · simp at ht
              | imm _ => simp at ht
          · simp at ht
        rcases orElse_eq_some h with he | hm'
        · cases a with
          | var t =>
            cases b with
            | imm ci =>
              cases ha with | var hmt => cases hb with | imm =>
              exact wrap rfl (tryExtCmp_ok hA hI hM hmt hdg1 he)
            | var _ => simp at he
          | imm ci =>
            cases b with
            | var t =>
              cases ha with | imm => cases hb with | var hmt =>
              exact wrap (CmpOp.swap_evalBits co _ _) (tryExtCmp_ok hA hI hM hmt hdg1 he)
            | imm _ => simp at he
        · rcases orElse_eq_some hm' with hm1 | hm2
          · cases a with
            | var x =>
              cases ha with | var hmx =>
              exact wrap rfl (tryCmpMemVar_ok hA hI hM hmx hb hdg1 hm1)
            | imm _ => simp at hm1
          · cases b with
            | var y =>
              cases hb with | var hmy =>
              exact wrap (CmpOp.swap_evalBits co _ _)
                (tryCmpMemVar_ok hA hI hM hmy ha hdg1 hm2)
            | imm _ => simp at hm2
      | _ => simp [tryFuseCmp] at h
    | _ => simp [tryFuseCmp] at h
  | _ => simp [tryFuseCmp] at h

theorem lowerOp_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {ts : List Ty} {op₁ : Op Val ts} {op : Op VNat ts}
    (hop : OpRel G op₁ op) (hl : lowerOp T.toIsa hints nv ip st op = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    {P : Tup Val ts → Prop} (hwp : op₁.wp P)
    (kont : ∀ (rvs : Tup Val ts) s', P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st'.memDefs →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  cases hop with
  | mk code hargs =>
  rename_i sig args₁ args
  have hMgrow : ∀ rvs : Tup Val ts,
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs := fun rvs =>
    hM.grow (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun _ h => List.mem_append_right _ h)
  unfold lowerOp at hl
  split at hl
  · cases hd : recordDef st.defs code args with
    | none => simp [hd] at hl
    | some df =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      obtain ⟨w, hrs, rvs, hP, hdef⟩ := recordDef_elide_ok hA.defs hargs hA.ctx_lt hwp hd
      subst hrs
      rcases rvs with ⟨rv, ⟨⟩⟩
      have hvw0 : ∀ x < nv, st.vecWidths.find? x = st.vecWidths.find? x := fun _ _ => rfl
      have hvw : ∀ sw, st.vecWidths.find? nv = some sw →
          (Ty.bits w).size ≤ sw.bits ∧ ∃ a b, Ty.bits w = .pair a b := fun sw hw =>
        absurd (hA.vw_lt _ _ hw) (Nat.lt_irrefl _)
      have hvw1 : ∀ x, nv < x → st.vecWidths.find? x = none := fun x hx =>
        Option.eq_none_iff_forall_ne_some.mpr fun sw hw =>
          absurd (hA.vw_lt _ _ hw) (Nat.not_lt.mpr (Nat.le_of_lt hx))
      have hA1 := hA.push (.bits w) rv st.vecWidths hvw0 hvw hvw1 (by intro _ a b h; cases h)
      refine kont (rv, ()) s hP
        { hA1 with
          defs := fun x d hx => by
            rw [Trie.find?_insert] at hx; split at hx
            · cases hx; subst_vars; exact hdef
            · exact hA1.defs x d hx
          defs_lt := fun x d hx => by
            rw [Trie.find?_insert] at hx; split at hx
            · subst_vars; exact Nat.lt_succ_self _
            · exact hA1.defs_lt x d hx }
        (hMgrow (rv, ())) hI
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨dsts, hdst, hl⟩ := hl
  obtain ⟨⟨c', clob, isVec, z32⟩, hpick, heq⟩ := Option.map_eq_some_iff.mp hl
  cases heq
  obtain ⟨hdg, hdv, hdo⟩ := resolveDsts_spec hdst
  have hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch :=
    fun r hr => not_scratch_of_isAllocGpr hsv (hdg r hr)
  have hdv' : ∀ v ∈ tupDstVecs dsts, v ∉ T.vec.vecScratch :=
    fun v hv => not_vecScratch_of_isAllocVec (hdv v hv)
  let G' : Tup Val ts → VCtx := fun rvs => Tup.zip rvs (Tup.levels ts nv) ++ G
  have hwp' : code.wp (vals args₁) (fun rvs => P rvs ∧ ∀ df, recordDef st.defs code args = some df →
      0 < ts.length ∧ DefOk (G' rvs) nv df) := by
    cases hd : recordDef st.defs code args with
    | none => exact OpCode.wp_mono code _ (fun r hp => ⟨hp, by simp⟩) hwp
    | some df =>
      exact OpCode.wp_mono code _ (fun r hp => ⟨hp.1, fun df' he => by cases he; exact hp.2⟩)
        (wp_recordDef hA.defs hargs hA.ctx_lt hwp hd)
  have hGtop : ∀ {rvs : Tup Val ts} t v x, ⟨t, v, x⟩ ∈ G' rvs → nv ≤ x →
      ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx) := fun {rvs} t v x hm hx => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hm
    · exact absurd hx (Nat.not_le_of_lt (hA.ctx_lt _ hm))
  have fin : z32 = false → ∀ s' (vC : List T.VReg),
      (∃ rvs, (P rvs ∧ ∀ df, recordDef st.defs code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) ∧ TRel (T.mach.PDstHolds s') dsts rvs) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) vC clob →
      vC = (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) →
      T.mach.Run host (k + c'.length) s' post := by
    rintro rfl s' vC ⟨rvs, ⟨hP, hdef⟩, hdh⟩ hm hfr rfl
    have hK := hA.kill hfr
    obtain ⟨hb1, hb2, hb3, hb4⟩ := bindDsts_ok dsts rvs nv
      (killRegs T.toIsa (tupDstGprs dsts ++ T.frame.scratch)
        (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) clob st.regs)
      st.vecWidths hdh hdo (hGtop (rvs := rvs))
    have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
      Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
    have hA1 := hK.extend (G' := G' rvs) (nv' := nv + ts.length) (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun p hp => (zip_levels_mem hp).elim (fun h => Nat.lt_of_lt_of_le (hA.ctx_lt p h)
        (Nat.le_add_right _ _)) (·.2))
      (fun p hp => List.mem_append_right _ hp) hb2
      (fun x w hx hle => (hb3 x w hx hle).resolve_left (by simp [hnone x hle]))
      (fun p hp hle hn => hb4 p.1 p.2.1 p.2.2 hp hle hn)
    have hr1 := fun p hp => (hb1 p hp).elim (fun hp => ⟨hA1.regs p hp, hA1.regs_lt p hp⟩) id
    have hd1 : ∀ x d, Trie.find? (match recordDef st.defs code args with
        | some df => st.defs.insert nv df | none => st.defs) x = some d →
        DefOk (G' rvs) x d ∧ x < nv + ts.length := by
      intro x d hx; split at hx
      · rw [Trie.find?_insert] at hx; split at hx
        · cases hx; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_add_of_pos_right (hdef _ ‹_›).1⟩
        · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
      · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
    exact kont rvs s' hP ⟨hA1.ctx_lt, fun p hp => (hr1 p hp).1, hA1.slots, fun x d hx => (hd1 x d hx).1,
      hA1.vw, fun p hp => (hr1 p hp).2, hA1.slots_lt, fun x d hx => (hd1 x d hx).2, hA1.vw_lt, hA1.vt⟩
      (hMgrow rvs) (hI.keep hm (keep_of_frame hfr.1 hdg))
  by_cases hel : elideZext32? T.toIsa st.regs code args dsts = true
  · simp only [hel, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpick
    rcases hpick with ⟨rfl, rfl, rfl, rfl⟩
    cases code <;> try (simp [elideZext32?] at hel; done)
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
    cases a with
    | imm _ => simp [elideZext32?] at hel
    | var x =>
      cases d0 with
      | vec _ => simp [elideZext32?] at hel
      | gpr rd =>
        simp only [elideZext32?, Bool.and_eq_true, Nat.beq_eq,
          hasVarGprZ, List.any_eq_true] at hel
        obtain ⟨⟨⟨rfl, rfl⟩, _⟩, ⟨sa', rl'⟩, hmem, hsa⟩ := hel
        have heq1 := symArgEq_eq hsa.1; have heq2 := regLocEq_eq hsa.2
        subst heq1; subst heq2
        rcases args₁ with ⟨a₁, ⟨⟩⟩
        cases hargs with
        | cons ha₁ _ =>
          cases ha₁ with
          | var hmG =>
            rename_i vx
            have hgr := (hA.regs _ hmem).2 vx hmG
            simpa [OpCode.wp] using
              fin rfl s [] ⟨(vx.setWidth 64, ()), hwp'.2,
                TRel.cons ⟨by decide, by rw [hgr, BitVec.setWidth_eq]⟩ .nil⟩
                rfl ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ rfl
  · simp only [hel, Bool.false_eq_true, ↓reduceIte] at hpick
    rcases orElse_eq_some hpick with hfuse | hpick
    · obtain ⟨⟨c'', cl⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse
      cases he
      refine tryFuseCmp_ok hA hI hM hargs hdg' hwp' hfc hc fun s' ⟨hQ, hm⟩ hfr =>
        fin rfl s' [] hQ hm hfr rfl
    · obtain ⟨pas, hk, hpg, hpv, hph⟩ := pickPArgs_ok hA hargs hpick
      split at hk <;> (try rcases orElse_eq_some hk with hk | hk) <;>
        obtain ⟨⟨c'', cl⟩, hop', he⟩ := Option.map_eq_some_iff.mp hk <;> cases he
      · by_cases hz : opProducesZ32 T.toIsa code pas dsts = true
        · have hz_eq := hz
          cases ts with
          | nil => simp [opProducesZ32] at hz
          | cons t0 ts0 =>
            cases ts0 with
            | cons _ _ => simp [opProducesZ32] at hz
            | nil =>
              cases t0 with
              | bool | float _ | pair _ _ => simp [opProducesZ32] at hz
              | bits n0 =>
                rcases dsts with ⟨d0, ⟨⟩⟩
                cases d0 with
                | vec _ => simp [opProducesZ32] at hz
                | gpr rd =>
                  simp only [opProducesZ32, Bool.and_eq_true, Nat.beq_eq] at hz
                  obtain ⟨rfl, hzop⟩ := hz
                  have hrd : rd ∉ T.frame.scratch := hdg' rd (by simp [tupDstGprs])
                  refine T.gprSpec.op_zero32 hzop hop' rfl hpg hrd hph hwp' hc
                    fun s' ⟨⟨rv, ⟨hP, hdef⟩, hrd_eq⟩, hm⟩ hfr => ?_
                  have hK := hA.kill hfr
                  have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
                    Option.eq_none_iff_forall_ne_some.mpr fun w h =>
                      absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
                  have hA1 := hK.push (.bits 32) rv st.vecWidths (fun _ _ => rfl)
                    (fun w h => absurd (hnone nv (Nat.le_refl _)) (by simp [h]))
                    (fun x hx => hnone x (Nat.le_of_lt hx)) (fun _ a b h => by cases h)
                  have hA2 := hA1.consReg (sa := .var nv) (rl := .gprZ rd)
                    ⟨fun t' v' hm' => by
                      cases mem_cons_top hA.ctx_lt hm'
                      exact ⟨by decide, by rw [hrd_eq,
                        BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]⟩,
                      fun v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hrd_eq⟩
                    (by simp [symArgScopeOk])
                  have hd1 : ∀ x d, Trie.find? (match recordDef st.defs code args with
                      | some df => st.defs.insert nv df | none => st.defs) x = some d →
                      DefOk (G' (rv, ())) x d ∧ x < nv + 1 := by
                    intro x d hx; split at hx
                    · rw [Trie.find?_insert] at hx; split at hx
                      · cases hx; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_succ_self _⟩
                      · exact ⟨hA2.defs x d hx, hA2.defs_lt x d hx⟩
                    · exact ⟨hA2.defs x d hx, hA2.defs_lt x d hx⟩
                  have hA3 : Agree T (G' (rv, ())) (nv + [Ty.bits 32].length)
                      { st with
                        regs := (.var nv, RegLoc.gprZ rd) ::
                          killRegs T.toIsa (rd :: T.frame.scratch) [] cl st.regs
                        defs := match recordDef st.defs code args with
                          | some df => st.defs.insert nv df | none => st.defs } s' σ :=
                    { hA2 with
                      defs := fun x d hx => (hd1 x d hx).1
                      defs_lt := fun x d hx => (hd1 x d hx).2 }
                  have hI' := hI.keep hm (keep_of_frame (gs := [rd]) hfr.1
                    (fun r hr => hdg r (by simpa [tupDstGprs] using hr)))
                  refine kont (rv, ()) s' hP ?_ (hMgrow (rv, ())) hI'
                  dsimp only; rw [hz_eq]
                  dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
                  exact hA3
        · refine T.gprSpec.op_spec hop' hpg hdg' hph hwp' hc fun s' ⟨hQ, hm⟩ hfr =>
            fin (Bool.eq_false_iff.mpr hz) s' [] hQ hm hfr rfl
      all_goals exact T.vecSpec.vop_spec hop' hpg hpv hdg' hdv' hph hwp' hc
                  fun s' ⟨hQ, hm⟩ hfr => fin rfl s' _ hQ hm hfr rfl

end Lemmas

/-! ## Part B: structural `LabelsUnique` (Guardrail 5) -/

section Labels
variable {I : Isa}

theorem NoLab.nil : NoLab I [] := fun _ h => nomatch h

theorem NoLab.append {a b : List I.Directive} (ha : NoLab I a) (hb : NoLab I b) :
    NoLab I (a ++ b) := fun l h => (List.mem_append.mp h).elim (ha l) (hb l)

/-! ### Label names -/

private def digF (a : Nat) (c : Char) : Nat := a * 10 + (c.toNat - 48)

private theorem natDigits_fold : ∀ (fuel n : Nat) (acc : List Char), n < fuel →
    (natDigits fuel n acc).foldl digF 0 = acc.foldl digF n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, acc, h => by
    have hc : ∀ d < 10, (Char.ofNat (48 + d)).toNat - 48 = d := by decide
    simp only [natDigits]
    split
    · next h10 =>
      rw [natDigits_fold fuel (n / 10) _ (by have := Nat.le_of_ble_eq_true h10; omega)]
      simp only [List.foldl, digF, hc _ (Nat.mod_lt _ (by decide))]
      rw [Nat.div_add_mod' n 10]
    · next h10 =>
      have : n < 10 := by simpa [Nat.ble_eq] using h10
      simp only [List.foldl, digF, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt this, hc n this]

theorem lname_inj {fn : Sym} {a b : Nat} (h : lname fn a = lname fn b) : a = b := by
  have h' := congrArg String.toList h
  simp only [lname, String.toList_append, String.toList_ofList, List.append_assoc] at h'
  have := congrArg (List.foldl digF 0) (List.append_cancel_left (List.append_cancel_left h'))
  rwa [natDigits_fold _ _ _ (Nat.lt_succ_self a), natDigits_fold _ _ _ (Nat.lt_succ_self b)] at this

theorem lname_ne {fn : Sym} {a : Nat} : lname fn a ≠ fn := fun h => by
  have := congrArg String.length h
  simp only [lname, String.length_append] at this
  have : ".L".length = 2 := rfl
  omega

/-- Labels `lname fn j` with `a ≤ j < b`. -/
def lrange (fn : Sym) (a b : Nat) (l : Sym) : Prop := ∃ j, a ≤ j ∧ j < b ∧ l = lname fn j

theorem lrange_disj {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l)
    (h' : lrange fn a' b' l) (hd : b ≤ a' ∨ b' ≤ a) : False := by
  obtain ⟨j, h1, h2, rfl⟩ := h; obtain ⟨j', h1', h2', he⟩ := h'
  have := lname_inj he; omega

theorem lrange_mono {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l) (ha : a' ≤ a)
    (hb : b ≤ b') : lrange fn a' b' l := by
  obtain ⟨j, h1, h2, rfl⟩ := h; exact ⟨j, by omega, by omega, rfl⟩

/-! ### Label-range invariant -/

/-- Equal labels of `c` sit at equal positions, and all labels satisfy `S`. -/
def LabOk (I : Isa) (S : Sym → Prop) (c : List I.Directive) : Prop :=
  (∀ (i j : Nat) l, c[i]? = some (I.frame.label l) → c[j]? = some (I.frame.label l) → i = j) ∧
  ∀ l, I.frame.label l ∈ c → S l

theorem LabOk.clean {S : Sym → Prop} {c : List I.Directive} (h : NoLab I c) : LabOk I S c :=
  ⟨fun _ _ l hi _ => absurd (List.mem_of_getElem? hi) (h l), fun l hl => absurd hl (h l)⟩

theorem LabOk.mono {S S' : Sym → Prop} {c : List I.Directive} (h : LabOk I S c)
    (hs : ∀ l, S l → S' l) : LabOk I S' c := ⟨h.1, fun l hl => hs l (h.2 l hl)⟩

theorem LabOk.single (hcl : LabelClean I) (l : Sym) : LabOk I (· = l) [I.frame.label l] := by
  refine ⟨fun i j l' hi hj => ?_, fun l' hl => hcl.label_inj _ _ (List.mem_singleton.mp hl)⟩
  cases i <;> cases j <;> simp_all

theorem LabOk.append {S₁ S₂ S : Sym → Prop} {c₁ c₂ : List I.Directive} (h₁ : LabOk I S₁ c₁)
    (h₂ : LabOk I S₂ c₂) (hd : ∀ l, S₁ l → S₂ l → False) (hs : ∀ l, S₁ l ∨ S₂ l → S l) :
    LabOk I S (c₁ ++ c₂) := by
  refine ⟨fun i j l hi hj => ?_, fun l hl => hs l ((List.mem_append.mp hl).imp (h₁.2 l) (h₂.2 l))⟩
  rw [List.getElem?_append] at hi hj
  split at hi <;> split at hj
  · exact h₁.1 i j l hi hj
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hi)) (h₂.2 l (List.mem_of_getElem? hj))).elim
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hj)) (h₂.2 l (List.mem_of_getElem? hi))).elim
  · have := h₂.1 _ _ l hi hj; omega

theorem LabOk.pre {S : Sym → Prop} {a c : List I.Directive} (ha : NoLab I a) (h : LabOk I S c) :
    LabOk I S (a ++ c) :=
  (LabOk.clean (S := fun _ => False) ha).append h (fun _ h _ => h) (fun _ h => h.elim False.elim id)

/-! ### Snippet code is label-free -/

theorem tryArg_some {st : SymState I} {pref : List I.Cond} {α : Type} {t : Ty} {a : Arg VNat t}
    {k : PArg I.Reg I.VReg I.Cond t → Option α} {res : α} (h : tryArg I st pref t a k = some res) :
    ∃ pa, k pa = some res := by
  have fs : ∀ {β γ : Type} {l : List β} {g : β → Option α} {f : γ → PArg I.Reg I.VReg I.Cond t},
      (∀ b, g b = some res → ∃ x, k (f x) = some res) → l.findSome? g = some res →
      ∃ pa, k pa = some res := fun hg h => by
    obtain ⟨b, -, hb⟩ := List.exists_of_findSome?_eq_some h; obtain ⟨x, hx⟩ := hg b hb; exact ⟨_, hx⟩
  have gpr : ∀ {sa}, tryGpr I st.regs sa (k ∘ .gpr) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.gpr) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  have vec : ∀ {sa}, tryVec I st.regs sa (k ∘ .vec) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.vec) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  cases t with
  | bool =>
    have flag : ∀ {sa}, tryFlag I st.regs pref sa (k ∘ .flag) = some res → ∃ pa, k pa = some res := by
        intro sa h; rcases orElse_eq_some h with h | h
        · obtain ⟨c, -, hb⟩ := List.exists_of_findSome?_eq_some h
          split at hb <;> first | exact ⟨_, hb⟩ | simp at hb
        · exact fs (f := PArg.flag) (fun ⟨_, rl⟩ hb => by
            cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb) h
    cases a with
    | var x => rcases orElse_eq_some h with h | h <;> first | exact flag h | exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact flag h
      rcases orElse_eq_some h with h | h <;> first | exact ⟨_, h⟩ | exact gpr h
  | bits w =>
    cases a with
    | var x => exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact gpr h | simp at h
  | pair x y =>
    cases a with
    | var x => exact vec h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact vec h | simp at h
  | float _ => simp [tryArg] at h

theorem pickPArgs_some {st : SymState I} {pref : List I.Cond} {α : Type} :
    ∀ {sig : List Ty} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α} {res : α},
    pickPArgs I st pref args k = some res → ∃ pas, k pas = some res
  | [], (), _, _, h => ⟨(), h⟩
  | _ :: _, (_, _), _, _, h => by
    obtain ⟨pa, h⟩ := tryArg_some h
    obtain ⟨pas, h⟩ := pickPArgs_some h
    exact ⟨_, h⟩

theorem tryAddr_some {st : SymState I} {vh : VariantHint} {α : Type} {a : Arg VNat i64}
    {k : AddrArg I.Reg → Option α} {res : α} (h : tryAddr I st vh a k = some res) :
    ∃ aa, k aa = some res := by
  cases a with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨_, h⟩
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
  | var x =>
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h <;> (try split at h) <;>
        first | (obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩) | simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · simp at h

variable (hcl : LabelClean I)
include hcl

theorem execMove_clean {nslots : Nat} {saved : List I.Reg} {mv : I.Move} {st st' : SymState I}
    {c : List I.Directive} (h : execMove I nslots saved mv st = some (c, st')) : NoLab I c := by
  cases mv <;> simp only [execMove] at h <;> (repeat' split at h) <;>
    first | (simp at h; done) | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)
  all_goals first
    | exact hcl.mov _ _
    | exact hcl.movi _ _
    | exact hcl.slotLd _ _
    | exact hcl.slotSt _ _
    | exact hcl.setcc _ _
    | exact hcl.vmov _ _ _
    | exact hcl.vslotLd _ _ _
    | exact hcl.vslotSt _ _ _
    | exact hcl.vmovi _ _ _ _ ‹_›

theorem execMoves_clean {nslots : Nat} {saved : List I.Reg} :
    ∀ {mvs : List I.Move} {st st' : SymState I} {c : List I.Directive},
    execMoves I nslots saved mvs st = some (c, st') → NoLab I c
  | [], _, _, _, h => by simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact NoLab.nil
  | _ :: _, _, _, _, h => by
    simp only [execMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    exact (execMove_clean hcl h1).append (execMoves_clean h2)

theorem stepPre_clean {h : I.Hints} {ip : Nat} {st st' : SymState I} {c : List I.Directive}
    (hs : stepPre I h ip st = some (c, st')) : NoLab I c := by
  simp only [stepPre] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · obtain ⟨⟨mc, st1⟩, h1, he⟩ := Option.map_eq_some_iff.mp hs
    split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1]
    · exact (execMoves_clean hcl h1).append hcl.clearFlags
    · exact execMoves_clean hcl h1

theorem shuffle_clean {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts = some (c, st')) : NoLab I c := by
  simp only [shuffle] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · split at hs
    · simp at hs
    · split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact execMoves_clean hcl ‹_›
      · simp at hs

theorem canonAbiCode_clean : ∀ {ts : List Ty} (locs : Tup (AbiReg I.Reg I.VReg) ts),
    NoLab I (canonAbiCode I locs)
  | [], () => NoLab.nil
  | _ :: _, (.gpr _, locs) => (hcl.canonAbi _ _).append (canonAbiCode_clean locs)
  | _ :: _, (.vec _, locs) => canonAbiCode_clean locs

theorem restoreCs_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (restoreCs I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotLd _ _).append (restoreCs_clean _ rs)

theorem saveCs_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (saveCs I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotSt _ _).append (saveCs_clean _ rs)

omit hcl in
private theorem tryGpr_some {st : SymState I} {α : Type} {sa : SymArg}
    {k : I.Reg → Option α} {res : α} (h : tryGpr I st.regs sa k = some res) :
    ∃ r, k r = some res := by
  obtain ⟨⟨_, rl⟩, -, hb⟩ := List.exists_of_findSome?_eq_some h
  cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb

private theorem tryTestMemVar_clean {st : SymState I} {neg : Bool} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryTestMemVar I st neg w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryTestMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at h
      split at h
      · obtain ⟨_, h1⟩ := tryAddr_some h
        obtain ⟨_, h2⟩ := tryArg_some h1
        exact hcl.testMem _ _ _ _ _ _ _ h2
      · simp at h
    | _ => simp [hmd] at h

private theorem tryCmpMemVar_clean {st : SymState I} {co : CmpOp} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryCmpMemVar I st co w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryCmpMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at h
      split at h
      · obtain ⟨_, h1⟩ := tryAddr_some h
        obtain ⟨_, h2⟩ := tryArg_some h1
        exact hcl.cmpMem _ _ _ _ _ _ _ h2
      · simp at h
    | _ => simp [hmd] at h

private theorem tryTestFuse_clean {st : SymState I} {neg : Bool} {w t : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryTestFuse I st neg w t pd = some (c, cl)) : NoLab I c := by
  unfold tryTestFuse at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · exact tryTestMemVar_clean hcl h1
      · obtain ⟨_, hk⟩ := tryArg_some h2; exact hcl.testOp _ _ _ _ _ _ _ hk
    | andVarVar _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h
      · exact tryTestMemVar_clean hcl h1
      rcases orElse_eq_some h with h2 | h3
      · exact tryTestMemVar_clean hcl h2
      · obtain ⟨_, hk1⟩ := tryArg_some h3
        obtain ⟨_, hk2⟩ := tryArg_some hk1
        exact hcl.testOp _ _ _ _ _ _ _ hk2
    | _ => simp [hdef] at h

private theorem tryExtCmp_clean {st : SymState I} {vh : VariantHint} {co : CmpOp} {w t : Nat}
    {ci : BitVec w} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryExtCmp I st vh co w t ci pd = some (c, cl)) : NoLab I c := by
  unfold tryExtCmp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw _ x | zextVar mw _ x =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · cases hmd : st.memDefs.find? x with
        | none => simp [hmd] at h1
        | some p =>
          rcases p with ⟨tm, addr⟩
          cases tm with
          | bits _ =>
            simp only [hmd] at h1; split at h1
            · obtain ⟨_, hk⟩ := tryAddr_some h1; exact hcl.cmpMem _ _ _ _ _ _ _ hk
            · simp at h1
          | _ => simp [hmd] at h1
      · split at h2
        · obtain ⟨_, hk⟩ := tryGpr_some h2; exact hcl.op _ _ _ _ _ _ hk
        · simp at h2
    | _ => simp [hdef] at h

private theorem tryFuseCmp_clean {st : SymState I} {vh : VariantHint} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask}
    (h : tryFuseCmp I st vh code args dsts = some (c, cl)) : NoLab I c := by
  cases code with
  | cmp _ ty mty _ =>
    cases ty with
    | bits _ =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
        unfold tryFuseCmp at h; dsimp only at h
        split at h; · simp at h
        rcases orElse_eq_some h with ht | h
        · split at ht
          · cases a with
            | var _ =>
              cases b with
              | imm _ =>
                dsimp only at ht
                split at ht <;> first | exact tryTestFuse_clean hcl ht | simp at ht
              | var _ => simp at ht
            | imm _ =>
              cases b with
              | var _ =>
                dsimp only at ht
                split at ht <;> first | exact tryTestFuse_clean hcl ht | simp at ht
              | imm _ => simp at ht
          · simp at ht
        rcases orElse_eq_some h with he | hm
        · cases a <;> cases b <;> first | exact tryExtCmp_clean hcl he | simp at he
        · rcases orElse_eq_some hm with hm1 | hm2
          · cases a <;> first | exact tryCmpMemVar_clean hcl hm1 | simp at hm1
          · cases b <;> first | exact tryCmpMemVar_clean hcl hm2 | simp at hm2
      | _ => simp [tryFuseCmp] at h
    | _ => simp [tryFuseCmp] at h
  | _ => simp [tryFuseCmp] at h

theorem lowerOp_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {c : List I.Directive} (hl : lowerOp I h nv ip st op = some (c, st')) :
    NoLab I c := by
  unfold lowerOp at hl
  split at hl
  · cases hd : recordDef st.defs op.code op.args <;> simp [hd] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨dsts, -, hl⟩ := hl
  obtain ⟨⟨c', cl, iv, _z⟩, hp, he⟩ := Option.map_eq_some_iff.mp hl
  cases he
  split at hp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩; exact NoLab.nil
  rcases orElse_eq_some hp with hfuse | hp
  · obtain ⟨⟨_, _⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse; cases he
    exact tryFuseCmp_clean hcl hfc
  obtain ⟨pas, hk⟩ := pickPArgs_some hp
  have hv : (I.vec.vop op.code pas dsts (h.variant.getD ip .default)).map
      (fun x => (x.1, x.2, true, false)) = some (c', cl, iv, _z) → NoLab I c' := fun hk => by
    obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he; exact hcl.vop _ _ _ _ _ _ hop
  split at hk
  · rcases orElse_eq_some hk with hk | hk
    · obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he; exact hcl.op _ _ _ _ _ _ hop
    · exact hv hk
  · exact hv hk

theorem lowerLoad_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {t : Ty}
    {a : Arg VNat i64} {c : List I.Directive} (hl : lowerLoad I h nv ip st t a = some (c, st')) :
    NoLab I c := by
  unfold lowerLoad at hl
  split at hl
  · split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl; rcases hl with ⟨rfl, -⟩; exact NoLab.nil
    · simp at hl
  split at hl
  · split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.load _ _ _ _ _ hk
  · obtain ⟨_, -, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.vload _ _ _ _ _ hk
  · simp at hl

theorem lowerStore_clean {st st' : SymState I} {vh : VariantHint} {t : Ty} {v : Arg VNat t}
    {a : Arg VNat i64} {c : List I.Directive} (hl : lowerStore I st vh t v a = some (c, st')) :
    NoLab I c := by
  cases t with
  | pair x y =>
    simp only [lowerStore] at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨pa, hk⟩ := tryArg_some hta
    cases pa with
    | vec vs => obtain ⟨_, hk⟩ := tryAddr_some hk; exact hcl.vstore _ _ _ _ _ hk
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl; split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryArg_some hta; obtain ⟨_, hk⟩ := tryAddr_some hk; exact hcl.store _ _ _ _ _ hk

theorem fnPrologue_clean (h : I.Hints) (E : Ext) : NoLab I (fnPrologue I h E) := by
  unfold fnPrologue; split
  · exact NoLab.nil
  · exact hcl.prologue _

theorem fnEpilogue_clean (h : I.Hints) (E : Ext) : NoLab I (fnEpilogue I h E) := by
  unfold fnEpilogue; split
  · exact NoLab.nil
  · exact hcl.epilogue _

omit hcl in
theorem lowerTail_spec {h : I.Hints} {E : Ext} {st : SymState I} {mc tail : List I.Directive}
    {ts : List Ty} {args : Tup (Arg VNat) ts} {locs : Tup (AbiReg I.Reg I.VReg) ts} {nv nl ip : Nat}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (hl : lowerTail I h E st mc tail args locs nv nl ip = .ok (c, nv', nl', ip')) :
    nv' = nv ∧ nl' = nl ∧ (LabelClean I → NoLab I mc → NoLab I tail → NoLab I c) := by
  unfold lowerTail at hl; repeat' (split at hl <;> try (simp at hl; done))
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl, rfl, -⟩ := hl
  exact ⟨rfl, rfl, fun hcl hm ht => ((((hm.append (shuffle_clean hcl ‹_›)).append
    (canonAbiCode_clean hcl _)).append (restoreCs_clean hcl _ _)).append
      (fnEpilogue_clean hcl h E)).append ht⟩

end Labels

section Labels2
variable {I : Isa}

/-! ### Structural label bounds for `lowerExpr`/`lowerBlocks` -/

theorem prepend_ok {pre : List I.Directive} {r : Res I} {c : List I.Directive} {nv nl ip : Nat}
    (h : prepend pre r = .ok (c, nv, nl, ip)) : ∃ c0, r = .ok (c0, nv, nl, ip) ∧ c = pre ++ c0 := by
  cases r with
  | error e => simp [prepend] at h
  | ok q =>
    obtain ⟨c0, a, b, d⟩ := q; simp only [prepend, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨c0, rfl, rfl⟩

theorem ite_cases {α : Type} {p : Prop} [Decidable p] {a b r : α} (h : (if p then a else b) = r) :
    a = r ∨ b = r := by
  by_cases hp : p <;> simp_all

theorem finishJnz_ok {rs : List Ty} {fn : Sym} {nl : Nat} {tgt : Option Nat}
    {b : Expr VNat LNat rs} {br c₁ c₂ : List I.Directive} {nv₂ nl₂ ip₂ : Nat} {c : List I.Directive}
    {nv' nl' ip' : Nat} (h : finishJnzBranch I fn nl tgt b br c₁ c₂ nv₂ nl₂ ip₂ = .ok (c, nv', nl', ip')) :
    nv' = nv₂ ∧ nl' = nl₂ ∧ (c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂) := by
  unfold finishJnzBranch at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, -⟩ := h; simp)

/-- `jnz` code: `br ++ c₁ ++ [label nl] ++ c₂` with `c₁`, `c₂` in disjoint ranges above `nl`. -/
theorem LabOk.jnz (hcl : LabelClean I) {fn : Sym} {nl a b d : Nat} {br c₁ c₂ : List I.Directive}
    (hbr : NoLab I br) (hab : nl < a ∧ a ≤ b ∧ b ≤ d) (h₁ : LabOk I (lrange fn (nl + 1) b) c₁)
    (h₂ : LabOk I (lrange fn b d) c₂) {c : List I.Directive}
    (hc : c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂ ∨
      c = br ++ c₂ ∨ c = br ++ c₂ ++ [I.frame.label (lname fn nl)] ++ c₁) :
    LabOk I (lrange fn nl d) c := by
  have hl : LabOk I (lrange fn nl (nl + 1)) [I.frame.label (lname fn nl)] :=
    (LabOk.single hcl _).mono fun l hl => ⟨nl, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
  have m : ∀ {x y l}, lrange fn x y l → nl ≤ x → y ≤ d → lrange fn nl d l :=
    fun h hx hy => lrange_mono h hx hy
  have three : ∀ {x y : List I.Directive} {S T : Sym → Prop}, LabOk I S x → LabOk I T y →
      (∀ l, S l → lrange fn (nl + 1) d l) → (∀ l, T l → lrange fn (nl + 1) d l) →
      (∀ l, S l → T l → False) → LabOk I (lrange fn nl d) (br ++ x ++ [I.frame.label (lname fn nl)] ++ y) := by
      intro x y S T hx hy hS hT hST
      refine (((hx.pre hbr).append (S := fun l => S l ∨ lrange fn nl (nl + 1) l) hl
        (fun l h1 h2 => lrange_disj (hS l h1) h2 (by omega)) (fun l h => h)).append hy
        (fun l h1 h2 => ?_) (fun l h => ?_))
      · exact h1.elim (fun h1 => hST l h1 h2) (fun h1 => lrange_disj h1 (hT l h2) (by omega))
      · rcases h with (h | h) | h
        · exact m (hS l h) (by omega) (Nat.le_refl _)
        · exact m h (Nat.le_refl _) (by omega)
        · exact m (hT l h) (by omega) (Nat.le_refl _)
  rcases hc with rfl | rfl | rfl | rfl
  · exact (h₁.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₁ h₂ (fun l h => lrange_mono h (Nat.le_refl _) (by omega))
      (fun l h => lrange_mono h (by omega) (Nat.le_refl _)) (fun l h1 h2 => lrange_disj h1 h2 (by omega))
  · exact (h₂.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₂ h₁ (fun l h => lrange_mono h (by omega) (Nat.le_refl _))
      (fun l h => lrange_mono h (Nat.le_refl _) (by omega)) (fun l h1 h2 => lrange_disj h1 h2 (by omega))

mutual
/-- `lowerExpr` is monotone in `nv`/`nl`, and (for a `LabelClean` ISA) its labels are distinct
`lname fn j` with `nl ≤ j < nl'`. -/
theorem lowerExpr_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ (e : Expr VNat LNat rs) (nv nl ip : Nat) (st : SymState I) (ft : Option Nat)
      (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerExpr I h E fn e nv nl ip st ft = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → LabOk I (lrange fn nl nl') c)
  | .let_ op k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerOp_clean hcl ‹_›))⟩
  | .load t a k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerLoad_clean hcl ‹_›))⟩
  | .store v a k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨h1, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerStore_clean hcl ‹_›))⟩
  | .call f args k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((((stepPre_clean hcl ‹_›).append
      (shuffle_clean hcl ‹_›)).append (canonAbiCode_clean hcl _)).append (hcl.call _))⟩
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    rcases ite_cases hr with hr | hr <;> obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr <;>
      exact ⟨h1, h2, fun hcl => (h3 hcl).pre (stepPre_clean hcl ‹_›)⟩
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    rename_i _ ce nv₁ nl₁ ip₁ he₁
    split at he <;> try (simp at he; done)
    rename_i _ ct nv₂ nl₂ ip₂ he₂
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₂
    rcases ite_cases hr with hr | hr <;> obtain ⟨rfl, rfl, hc⟩ := finishJnz_ok hr
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl ?_ ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl)
        (b3 hcl) (hc.elim (fun h => Or.inr (Or.inr (Or.inl h))) fun h => Or.inr (Or.inr (Or.inr h)))).pre
        (stepPre_clean hcl ‹_›)⟩
      first | (cases ‹Sum I.Cond I.Reg› <;> simp only [jnzSetup] <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _) | (split <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _)
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl ?_ ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl)
        (b3 hcl) (hc.elim Or.inl fun h => Or.inr (Or.inl h))).pre (stepPre_clean hcl ‹_›)⟩
      first | (cases ‹Sum I.Cond I.Reg› <;> simp only [jnzSetup] <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _) | (split <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _)
  | .jump j args, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    repeat' (split at he <;> try (simp at he; done))
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      refine ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean ((((stepPre_clean hcl ‹_›).append
        (shuffle_clean hcl ‹_›))).append ?_)⟩
      first | exact NoLab.nil | exact hcl.jmp _
  | .ret vs, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) hcl.ret)⟩
  | .exit f args, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl =>
      LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) (hcl.exitJmp _))⟩
  | .hlt, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => LabOk.clean NoLab.nil⟩
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    rename_i ck nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl => (a3 hcl).append (b3 hcl a2) (fun l h1 h2 => ?_) (fun l h => ?_)⟩
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h <;> exact lrange_mono h (by omega) (by omega)

/-- `lowerBlocks` analogue: block labels `lname fn j` for `lid ≤ j < lid + sig.length`, plus body
labels in `[nl, nl')`. -/
theorem lowerBlocks_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat)
      (defs : Trie DefFact) (vw : Trie SlotWidth) (ft : Option Nat) (c : List I.Directive)
      (nv' nl' ip' : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → lid + sig.length ≤ nl →
      LabOk I (fun l => lrange fn lid (lid + sig.length) l ∨ lrange fn nl nl' l) c)
  | _, .nil, lid, nv, nl, ip, defs, vw, ft, c, nv', nl', ip', he => by
    simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => LabOk.clean NoLab.nil⟩
  | _, .cons (sig := sig) b bs, lid, nv, nl, ip, defs, vw, ft, c, nv', nl', ip', he => by
    simp only [lowerBlocks] at he
    repeat' (split at he <;> try (simp at he; done))
    rename_i cb nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl hlid => ?_⟩
    simp only [List.length_cons] at hlid ⊢
    have hl : LabOk I (lrange fn lid (lid + 1)) [I.frame.label (lname fn lid)] :=
      (LabOk.single hcl _).mono fun l hl => ⟨lid, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
    refine (hl.append ((a3 hcl).append (b3 hcl (by omega)) (fun l h1 h2 => ?_) (fun l h => h))
      (fun l h1 h2 => ?_) (fun l h => ?_))
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h2 with h2 | h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h | h <;> first
        | exact Or.inl (lrange_mono h (by omega) (by omega)) | exact Or.inr (lrange_mono h (by omega) (by omega))
end

theorem lowerExpr_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {e : Expr VNat LNat rs}
    {nv nl ip : Nat} {st : SymState I} {ft : Option Nat} {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerExpr I h E fn e nv nl ip st ft = .ok (c, nv', nl', ip')) : nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerExpr_labels e nv nl ip st ft c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerBlocks_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {sig : List (List Ty)}
    {bs : Blocks VNat LNat rs sig} {lid nv nl ip : Nat} {defs : Trie DefFact} {vw : Trie SlotWidth}
    {ft : Option Nat} {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerBlocks I h E fn bs lid nv nl ip defs vw ft = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerBlocks_labels bs lid nv nl ip defs vw ft c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerFn_labOk {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (hf : lowerFn I hints E f = .ok code) :
    LabOk I (fun l => l = f.name ∨ ∃ j, l = lname f.name j) code := by
  unfold lowerFn at hf
  repeat' (split at hf <;> try (simp at hf; done))
  rename_i c _ _ _ he
  simp only [Except.ok.injEq] at hf; subst hf
  have h3 := (lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he).2.2 hcl
  refine (LabOk.single hcl f.name).append
    (h3.pre ((fnPrologue_clean hcl hints E).append (saveCs_clean hcl _ _)))
    (fun l h1 h2 => ?_) (fun l h => ?_)
  · obtain ⟨j, -, -, rfl⟩ := h2; exact lname_ne h1
  · exact h.imp id fun ⟨j, _, _, e⟩ => ⟨j, e⟩

/-- Guardrail 5: labels of a lowered function are pairwise distinct (structurally, no `decide`). -/
theorem lowerFn_labelsUnique {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) :
    ∀ (i j : Nat) l, code[i]? = some (I.frame.label l) → code[j]? = some (I.frame.label l) → i = j :=
  (lowerFn_labOk hcl h).1

theorem lowerFn_label_mem {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) {i : Nat} {l : Sym}
    (hi : code[i]? = some (I.frame.label l)) : l = f.name ∨ ∃ j, l = lname f.name j :=
  (lowerFn_labOk hcl h).2 l (List.mem_of_getElem? hi)

end Labels2

end Rega
end LeanQbe.T
