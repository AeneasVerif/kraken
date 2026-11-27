module

public import LeanQbe.T.Rega
public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas

/-!
# `RegaLemmas` Part 0: Slot Splices and `execMovi_spec`

Extracted from `RegaLemmas1.lean` to keep every file well under `2,500` LOC:
* `slice`, `unpack_ofFn`, `packW`, `extract_packW`, `unpack_packW`, `unpack_inj`,
  `splice`, `Splice`.
* `execMovi_spec`: machine `FallsTo` specification for flag-liveness-gated `execMovi`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

/-- The `w.slots` words of `σ` starting at slot `i`. -/
@[expose]
def slice (σ : List (BitVec 64)) (i k : Nat) : List (BitVec 64) := (σ.drop i).take k

/-! ## Slot words and splices -/

theorem unpack_ofFn (w : SlotWidth) (bv : BitVec 512) :
    unpackSlotWords w bv = List.ofFn (n := w.slots) fun n => bv.extractLsb' (64 * n) 64 := by
  cases w <;> simp [unpackSlotWords, List.ofFn_succ]

@[expose]
def packW : List (BitVec 64) → BitVec 512
  | [] => 0
  | x :: xs => x.setWidth 512 ||| (packW xs <<< 64)

theorem extract_packW : ∀ (xs : List (BitVec 64)) (n : Nat) (h : n < xs.length), n < 8 →
    (packW xs).extractLsb' (64 * n) 64 = xs[n]
  | [], _, h, _ => by simp at h
  | x :: xs, 0, _, _ => by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [packW, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj]
    omega
  | x :: xs, n + 1, h, h8 => by
    have hn : n < xs.length := by simp at h; omega
    have ih := extract_packW xs n hn (by omega)
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    show _ = (xs[n]'hn).getLsbD j
    rw [← ih]
    simp [packW, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj]
    simp [show 64 * (n + 1) + j < 512 by omega, show ¬ 64 * (n + 1) + j < 64 by omega,
      show 64 * (n + 1) + j - 64 = 64 * n + j by omega,
      BitVec.getLsbD_of_ge x _ (by omega : 64 ≤ 64 * (n + 1) + j)]

theorem unpack_packW {w : SlotWidth} {ws : List (BitVec 64)} (h : ws.length = w.slots) :
    unpackSlotWords w (packW ws) = ws := by
  rw [unpack_ofFn]; apply List.ext_getElem (by simp [h])
  intro n h1 h2; simp only [List.getElem_ofFn]
  exact extract_packW ws n h2 (by simp at h1; have := SlotWidth.slots_le_eight w; omega)

theorem unpack_inj {w : SlotWidth} {bv bv' : BitVec 512}
    (h : unpackSlotWords w bv = unpackSlotWords w bv') :
    bv.setWidth w.bits = bv'.setWidth w.bits := by
  rw [unpack_ofFn, unpack_ofFn] at h; apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hb := SlotWidth.bits_eq_64_mul_slots w
  have hn : j / 64 < w.slots := by omega
  have e := congrArg (fun l => l[j / 64]?) h
  simp [hn] at e
  have e2 := congrArg (fun x => BitVec.getLsbD x (j % 64)) e
  have hj' : j < 64 * w.slots := by omega
  simp [hj', Nat.mod_lt] at e2 ⊢; have : 64 * (j / 64) + j % 64 = j := by omega
  rw [this] at e2; exact e2

@[expose]
def splice (σ : List (BitVec 64)) (i k : Nat) (ws : List (BitVec 64)) : List (BitVec 64) :=
  σ.take i ++ ws ++ σ.drop (i + k)

section Splice
variable {σ ws : List (BitVec 64)} {i k : Nat}

theorem length_splice (h : i + k ≤ σ.length) (hw : ws.length = k) :
    (splice σ i k ws).length = σ.length := by
  simp [splice, hw]; omega

theorem getElem?_splice (h : i + k ≤ σ.length) (hw : ws.length = k) (j : Nat) :
    (splice σ i k ws)[j]? =
      if j < i then σ[j]? else if j < i + k then ws[j - i]? else σ[j]? := by
  unfold splice; have hi : (σ.take i).length = i := by simp; omega
  split
  · rw [List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt (by omega)]
  · rw [List.append_assoc, List.getElem?_append_right (by omega), hi]
    split
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop, hw]; congr 1; omega

theorem getElem?_slice (n : Nat) : (slice σ i k)[n]? = if n < k then σ[i + n]? else none := by
  simp only [slice, List.getElem?_take, List.getElem?_drop]

theorem slice_splice_self (h : i + k ≤ σ.length) (hw : ws.length = k) :
    slice (splice σ i k ws) i k = ws := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice, getElem?_splice h hw]; split
  · simp only [show ¬ (i + n < i) by omega, show i + n < i + k by omega, ↓reduceIte]
    congr 1; omega
  · rw [List.getElem?_eq_none (by omega)]

theorem slice_splice_disj (h : i + k ≤ σ.length) (hw : ws.length = k) {j kj : Nat}
    (hd : j + kj ≤ i ∨ i + k ≤ j) : slice (splice σ i k ws) j kj = slice σ j kj := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice, getElem?_slice, getElem?_splice h hw]
  split; split; rfl; simp only [show ¬ (j + n < i + k) by omega, ↓reduceIte]; rfl

theorem getElem?_splice_disj (h : i + k ≤ σ.length) (hw : ws.length = k) {j : Nat}
    (hd : j < i ∨ i + k ≤ j) : (splice σ i k ws)[j]? = σ[j]? := by
  rw [getElem?_splice h hw]; split; rfl; simp only [show ¬ (j < i + k) by omega, ↓reduceIte]

theorem slice_length (h : i + k ≤ σ.length) : (slice σ i k).length = k := by
  simp [slice]; omega

theorem splice_slice : splice σ i k (slice σ i k) = σ := by
  simp only [splice, slice, List.append_assoc]
  rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem slice_one (h : i < σ.length) : slice σ i 1 = [σ[i]] := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice]
  rcases n with _ | n <;> simp [List.getElem?_eq_getElem h]
end Splice

theorem execMovi_spec {T : Target} {h : T.mach.Host} {k : Nat}
    {st : SymState T.toIsa} {deadHint : Bool} {d : T.Reg} {c : BitVec 64}
    {s : T.mach.MData} {post : T.mach.State → Prop} :
    T.mach.FallsTo T.gpr.condReads h k (execMovi T.toIsa st deadHint d c).1
      (d :: T.frame.scratch) [] (execMovi T.toIsa st deadHint d c).2 s
      (fun s' => T.mach.getGpr s' d = c ∧ T.mach.mem s' = T.mach.mem s) post := by
  unfold execMovi
  cases hmd : T.gpr.moviDeadFlags? with
  | none => exact T.gprSpec.movi_spec
  | some fn =>
    by_cases hcond : ((st.flags.isNone && !stHasFlagReg st.regs) || deadHint) = true
    · simp only [hcond, ↓reduceIte]; exact T.gprSpec.moviDeadFlags?_spec hmd
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact T.gprSpec.movi_spec

@[expose]
def SymValAt (G : Ctx Val VNat) (w : Nat) (bv : BitVec w) : SymArg → Prop
  | .var x => ⟨.bits w, bv, x⟩ ∈ G
  | .immBits w' c => w' = w ∧ c.setWidth w = bv
  | _ => False

theorem SymValAt.mono {G G' : Ctx Val VNat} (hsub : ∀ p ∈ G, p ∈ G') {w : Nat}
    {bv : BitVec w} {sa : SymArg} (h : SymValAt G w bv sa) : SymValAt G' w bv sa := by
  cases sa with
  | var _ => exact hsub _ h
  | immBits _ _ => exact h
  | _ => exact h

theorem ctx_uniq_cons {G : Ctx Val VNat} {nv : Nat}
    (hlt : ∀ p ∈ G, p.2.2 < nv)
    (hu : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G → ⟨t, v₂, x⟩ ∈ G → v₁ = v₂)
    {t0 : Ty} {v0 : Val t0} {t : Ty} {x : Nat} {v₁ v₂ : Val t}
    (h1 : ⟨t, v₁, x⟩ ∈ (⟨t0, v0, nv⟩ :: G : Ctx Val VNat))
    (h2 : ⟨t, v₂, x⟩ ∈ (⟨t0, v0, nv⟩ :: G : Ctx Val VNat)) : v₁ = v₂ := by
  rcases List.mem_cons.mp h1 with e1 | m1 <;> rcases List.mem_cons.mp h2 with e2 | m2
  · cases e1; cases e2; rfl
  · cases e1; exact absurd (hlt _ m2) (Nat.lt_irrefl _)
  · cases e2; exact absurd (hlt _ m1) (Nat.lt_irrefl _)
  · exact hu m1 m2

theorem mem_zip_levels_ge :
    ∀ {ts : List Ty} {rvs : Tup Val ts} {nv0 : Nat} {p : (t : Ty) × Val t × VNat t},
      p ∈ Tup.zip rvs (Tup.levels ts nv0) → nv0 ≤ p.2.2
  | [], _, _, _, h => by simp [Tup.zip] at h
  | _ :: ts, (v, rvs), nv0, _, h => by
    simp only [Tup.zip, Tup.levels, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (mem_zip_levels_ge h))

theorem ctx_uniq_zip {G : Ctx Val VNat} {nv : Nat}
    (hlt : ∀ p ∈ G, p.2.2 < nv)
    (hu : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G → ⟨t, v₂, x⟩ ∈ G → v₁ = v₂) :
    ∀ (ts : List Ty) (rvs : Tup Val ts) (nv0 : Nat), nv ≤ nv0 →
    ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t},
      ⟨t, v₁, x⟩ ∈ Tup.zip rvs (Tup.levels ts nv0) ++ G →
      ⟨t, v₂, x⟩ ∈ Tup.zip rvs (Tup.levels ts nv0) ++ G → v₁ = v₂
  | [], (), _, _, _, _, _, _, h1, h2 =>
    hu (by simpa [Tup.zip] using h1) (by simpa [Tup.zip] using h2)
  | _ :: ts, (v, rvs), nv0, hle, _, _, _, _, h1, h2 => by
    simp only [Tup.zip, Tup.levels, List.cons_append] at h1 h2
    have hge : ∀ p ∈ Tup.zip rvs (Tup.levels ts (nv0 + 1)) ++ G, p.2.2 ≠ nv0 := by
      intro p hp
      rcases List.mem_append.mp hp with hm | hm
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (mem_zip_levels_ge hm))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hlt p hm) hle)
    rcases List.mem_cons.mp h1 with e1 | m1 <;> rcases List.mem_cons.mp h2 with e2 | m2
    · cases e1; cases e2; rfl
    · cases e1; exact absurd rfl (hge _ m2)
    · cases e2; exact absurd rfl (hge _ m1)
    · exact ctx_uniq_zip hlt hu ts rvs (nv0 + 1) (by omega) m1 m2

abbrev VCtx : Type := Ctx Val VNat

theorem scrOk_nil {R V C D : Type} (M : Machine R V C D) (scratch : List R) (s : M.MData) :
    ScrOk M scratch [] s := fun _ h => False.elim (List.not_mem_nil h)

theorem scrOk_killScr {R V C D : Type} [DecidableEq R] {M : Machine R V C D}
    {scratch gClob : List R} {scr : List (R × BitVec 64)} {s s' : M.MData}
    (hk : M.KeepsGpr s s' gClob) (h : ScrOk M scratch scr s) :
    ScrOk M scratch (Rega.killScr gClob scr) s' := by
  intro p hp
  simp only [Rega.killScr, List.mem_filter, Bool.not_eq_true'] at hp
  refine ⟨(h p hp.1).1, ?_⟩
  rw [hk p.1 (by simpa [List.contains_iff_mem] using hp.2), (h p hp.1).2]

theorem scrOk_moveKeepsScr {T : Target} {d r : T.Reg} {scr : List (T.Reg × BitVec 64)}
    {s s' : T.mach.MData} (hk : T.mach.KeepsGpr s s' [d])
    (h : ScrOk T.mach T.frame.scratch scr s) :
    ScrOk T.mach T.frame.scratch (Rega.moveKeepsScr T.toIsa (.mov d r) scr) s' := by
  simp only [Rega.moveKeepsScr]
  split
  · exact scrOk_nil _ _ _
  · exact scrOk_killScr hk h

theorem scrOk_frame {R V C D : Type} {M : Machine R V C D} {scratch gClob : List R}
    {scr : List (R × BitVec 64)} {s s' : M.MData}
    (hdisj : ∀ r ∈ scratch, r ∉ gClob) (hk : M.KeepsGpr s s' gClob)
    (h : ScrOk M scratch scr s) : ScrOk M scratch scr s' := fun p hp =>
  ⟨(h p hp).1, (hk p.1 (hdisj p.1 (h p hp).1)).trans (h p hp).2⟩

@[expose]
def RmwOp.eval {w : Nat} : RmwOp → BitVec w → BitVec w → BitVec w
  | .add => (· + ·)
  | .sub => (· - ·)
  | .and => (· &&& ·)
  | .or  => (· ||| ·)
  | .xor => (· ^^^ ·)

theorem RmwOp.eval_comm {w : Nat} {op : RmwOp} (h : op.isComm = true) (a b : BitVec w) :
    op.eval a b = op.eval b a := by
  cases op with
  | add => exact BitVec.add_comm a b
  | sub => simp [RmwOp.isComm] at h
  | and => exact BitVec.and_comm a b
  | or  => exact BitVec.or_comm a b
  | xor => exact BitVec.xor_comm a b

theorem RmwOp.wp_eval {w : Nat} (op : RmwOp) (a b : BitVec w) (P : Tup Val [.bits w] → Prop) :
    (op.toOpCode w).wp (a, b, ()) P ↔ P (op.eval a b, ()) := by
  cases op <;> simp [RmwOp.toOpCode, RmwOp.eval, OpCode.wp, lift2, Ty.hasFloat]

@[expose]
def DefOk (G : VCtx) (x : Nat) : DefFact → Prop
  | .addImm64 b d => (∀ t v, ⟨t, v, x⟩ ∈ G → t = i64) ∧
      ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vb : BitVec 64, ⟨i64, vb, b⟩ ∈ G ∧ v = vb + d
  | .scaleOff i sh d =>
    ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vi : BitVec 64, ⟨i64, vi, i⟩ ∈ G ∧ v = (vi <<< sh) + d
  | .addrSum b i sh d =>
    ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vb vi : BitVec 64, ⟨i64, vb, b⟩ ∈ G ∧ ⟨i64, vi, i⟩ ∈ G ∧
      v = vb + (vi <<< sh) + d
  | .imm64 c => ∀ v, ⟨i64, v, x⟩ ∈ G → v = c
  | .andVarVar w a b => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va vb : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ ⟨.bits w, vb, b⟩ ∈ G ∧ v = va &&& vb
  | .andVarImm w a c => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = va &&& c.setWidth w
  | .binVarVar w op a b => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va vb : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ ⟨.bits w, vb, b⟩ ∈ G ∧ v = op.eval va vb
  | .binVarImm w op a c => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = op.eval va (c.setWidth w)
  | .shlVarImm w a sh => w ≤ 64 ∧ sh < w ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = va <<< sh
  | .shiftVarImm w sk a k => w ≤ 64 ∧ k < w ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = sk.eval va k
  | .sextVar m n a => 0 < m ∧ m < n ∧ n ≤ 64 ∧ ∀ v : BitVec n, ⟨.bits n, v, x⟩ ∈ G →
    ∃ va : BitVec m, ⟨.bits m, va, a⟩ ∈ G ∧ v = va.signExtend n
  | .zextVar m n a => 0 < m ∧ m < n ∧ n ≤ 64 ∧ ∀ v : BitVec n, ⟨.bits n, v, x⟩ ∈ G →
    ∃ va : BitVec m, ⟨.bits m, va, a⟩ ∈ G ∧ v = va.zeroExtend n
  | .cmpZeroVar co w a => w ≤ 64 ∧ ∀ cv : Bool, ⟨.bool, cv, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ cv = co.evalBits va 0#w
  | .testBitVar neg w a c => w ≤ 64 ∧ ∀ cv : Bool, ⟨.bool, cv, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧
      cv = (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& c.setWidth w) 0#w

theorem scope_lt {nv x : Nat} (h : symArgScopeOk nv (.var x) = true) : x < nv := by
  simp only [symArgScopeOk, Nat.ble_eq] at h; omega

theorem mem_grow {G G' : VCtx} {nv : Nat} (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2) {sa : SymArg}
    (hs : symArgScopeOk nv sa = true) :
    ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G' → ⟨t, v, x⟩ ∈ G := by
  rintro x rfl t v hm; exact (hG _ hm).resolve_right (Nat.not_le.mpr (scope_lt hs))

theorem DefOk.grow {G G' : VCtx} {nv x : Nat} {d : DefFact} (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2)
    (hsub : ∀ p ∈ G, p ∈ G') (hx : x < nv) (h : DefOk G x d) : DefOk G' x d := by
  have hm := mem_grow hG (sa := .var x) (by simp [symArgScopeOk, Nat.ble_eq]; omega) x rfl
  cases d with
  | addImm64 b c =>
    refine ⟨fun t v hv => h.1 t v (hm _ _ hv), fun v hv => ?_⟩
    obtain ⟨vb, h1, h2⟩ := h.2 v (hm _ _ hv); exact ⟨vb, hsub _ h1, h2⟩
  | scaleOff i sh d =>
    intro v hv; obtain ⟨vi, h1, h2⟩ := h v (hm _ _ hv); exact ⟨vi, hsub _ h1, h2⟩
  | addrSum b i sh d =>
    intro v hv; obtain ⟨vb, vi, h1, h2, h3⟩ := h v (hm _ _ hv)
    exact ⟨vb, vi, hsub _ h1, hsub _ h2, h3⟩
  | imm64 c => intro v hv; exact h v (hm _ _ hv)
  | andVarVar w a b =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, vb, h1, h2, h3⟩ := h.2 v (hm _ _ hv); exact ⟨va, vb, hsub _ h1, hsub _ h2, h3⟩
  | andVarImm w a c =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 v (hm _ _ hv); exact ⟨va, hsub _ h1, h2⟩
  | binVarVar w op a b =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, vb, h1, h2, h3⟩ := h.2 v (hm _ _ hv); exact ⟨va, vb, hsub _ h1, hsub _ h2, h3⟩
  | binVarImm w op a c =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 v (hm _ _ hv); exact ⟨va, hsub _ h1, h2⟩
  | shlVarImm _ _ _ | shiftVarImm _ _ _ _ =>
    refine ⟨h.1, h.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2 v (hm _ _ hv); exact ⟨va, hsub _ h1, h2⟩
  | sextVar m n a =>
    refine ⟨h.1, h.2.1, h.2.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2.2 v (hm _ _ hv); exact ⟨va, hsub _ h1, h2⟩
  | zextVar m n a =>
    refine ⟨h.1, h.2.1, h.2.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2.2 v (hm _ _ hv); exact ⟨va, hsub _ h1, h2⟩
  | cmpZeroVar co w a =>
    refine ⟨h.1, fun cv hcv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 cv (hm _ _ hcv); exact ⟨va, hsub _ h1, h2⟩
  | testBitVar neg w a c =>
    refine ⟨h.1, fun cv hcv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 cv (hm _ _ hcv); exact ⟨va, hsub _ h1, h2⟩

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

theorem mem_cons_top {G : VCtx} {nv : Nat} (hlt : ∀ p ∈ G, p.2.2 < nv) {t t' : Ty} {v : Val t}
    {v' : Val t'} (h : (⟨t', v', nv⟩ : (a : Ty) × Val a × VNat a) ∈ ⟨t, v, nv⟩ :: G) :
    (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := by
  rcases List.mem_cons.mp h with h | h
  · cases h; rfl
  · exact absurd (hlt _ h) (Nat.lt_irrefl _)

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
    refine ⟨fun t v hv => by cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
    cases mem_cons_top hlt hv
    exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩
  | some d =>
    have hdx := hdefs x d hd
    cases d with
    | imm64 c0 =>
      intro v hv; cases mem_cons_top hlt hv
      have hx := hdx vx hm; rw [hx]
    | addImm64 b disp =>
      refine ⟨fun t v hv => by cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
      cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hdx.2 vx hm
      exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx, BitVec.add_assoc]⟩
    | scaleOff idx sh disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vi, hi, hvx⟩ := hdx vx hm
      exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, BitVec.add_assoc]⟩
    | addrSum b idx sh disp =>
      dsimp only
      split
      · refine ⟨fun t v hv => by cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
        cases mem_cons_top hlt hv
        exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩
      · intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, vi, hb, hi, hvx⟩ := hdx vx hm
        exact ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi,
          by simp [hvx, BitVec.add_assoc]⟩
    | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _ | binVarImm _ _ _ _
    | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ | cmpZeroVar _ _ _
    | testBitVar _ _ _ _ | shiftVarImm _ _ _ _ =>
      refine ⟨fun t v hv => by cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
      cases mem_cons_top hlt hv
      exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩

private theorem defOk_addScale {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {defs : Trie DefFact} {dfx : DefFact} {dfy? : Option DefFact} {df : DefFact}
    (hx : DefOk G x dfx) (hy : ∀ d, dfy? = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    (h : recordAddScale defs dfx dfy? y = some df) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
  unfold recordAddScale at h
  cases dfx with
  | scaleOff idx sh d1 =>
    dsimp only at h
    split at h
    · have hfall : DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (.addrSum y idx sh d1) := by
        intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vi, hi, hvx⟩ := hx vx hmx
        refine ⟨vy, vi, List.mem_cons_of_mem _ hmy, List.mem_cons_of_mem _ hi, ?_⟩
        rw [hvx]; ac_rfl
      cases dfy? with
      | some dy =>
        cases dy with
        | addImm64 b d2 =>
          by_cases hc : isScaledAddrSum defs b = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at h; subst h; exact hfall
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
            intro v hv; cases mem_cons_top hlt hv
            obtain ⟨vi, hi, hvx⟩ := hx vx hmx
            obtain ⟨vb, hb, hvy⟩ := (hy (.addImm64 b d2) rfl).2 vy hmy
            refine ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi, ?_⟩
            rw [hvx, hvy]; ac_rfl
        | _ => cases h; exact hfall
      | none => cases h; exact hfall
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
        obtain ⟨vb, hb, hvx⟩ := hx.2 vx hmx
        obtain ⟨vb2, hb2, hvy⟩ := (hy (.addImm64 b2 d2) rfl).2 vy hmy
        refine ⟨vb, vb2, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hb2, ?_⟩
        rw [hvx, hvy]; simp only [BitVec.shiftLeft_zero]; ac_rfl
      | _ =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, hb, hvx⟩ := hx.2 vx hmx
        refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
        rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
    | none =>
      cases h; intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hx.2 vx hmx
      refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
      rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
  | _ => simp at h

private theorem defOk_addVarVar {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {defs : Trie DefFact} (hdefs : ∀ z d, defs.find? z = some d → DefOk G z d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (recordAddVarVar defs x y) := by
  let s1 := (defs.find? x).bind (recordAddScale defs · (defs.find? y) y)
  let s2 := (defs.find? y).bind (recordAddScale defs · (defs.find? x) x)
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

private theorem defOk_rmwBin {G : VCtx} {nv w : Nat} {op : RmwOp}
    {a₁ b₁ : Arg Val (.bits w)} {a b : Arg VNat (.bits w)} {df : DefFact}
    (ha : ArgRel G (.bits w) a₁ a) (hb : ArgRel G (.bits w) b₁ b)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (h : recordRmwBin w op a b = some df) :
    DefOk (Tup.zip (op.eval a₁.val b₁.val, ()) (Tup.levels [.bits w] nv) ++ G) nv df := by
  cases a with
  | var x =>
    cases b with
    | var y =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      simp only [Option.some.injEq] at h; subst h
      cases ha with | var hmx => cases hb with | var hmy =>
      refine ⟨hw, fun v hv => ?_⟩
      simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
      exact ⟨_, _, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, rfl⟩
    | imm c =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      simp only [Option.some.injEq] at h; subst h
      cases ha with | var hmx => cases hb with | imm =>
      refine ⟨hw, fun v hv => ?_⟩
      simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
      exact ⟨_, List.mem_cons_of_mem _ hmx, by
        rw [BitVec.setWidth_setWidth_of_le c hw, BitVec.setWidth_eq]; rfl⟩
  | imm c =>
    cases b with
    | var y =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      dsimp only at h; split at h
      · rename_i hcomm; simp only [Option.some.injEq] at h; subst h
        cases ha with | imm => cases hb with | var hmy =>
        refine ⟨hw, fun v hv => ?_⟩
        simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmy, by
          simp only [Arg.val]
          rw [BitVec.setWidth_setWidth_of_le c hw, BitVec.setWidth_eq, RmwOp.eval_comm hcomm]⟩
      · simp at h
    | imm _ => simp [recordRmwBin] at h

private theorem recordDef_rs {defs : Trie DefFact} {sig rs : List Ty} {code : OpCode sig rs}
    {args : Tup (Arg VNat) sig} {df : DefFact} (hd : recordDef defs code args = some df) :
    ∃ w, rs = [.bits w] := by
  cases code with
  | add t | sub t | shl t | copy t | and t | or t | xor t | lshr t | ashr t =>
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
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      by_cases hn64 : n = 64
      · subst hn64
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
      · have hnf : Nat.beq n 64 = false :=
          Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn64)
        simp only [recordDef, hnf, Bool.not_false, ↓reduceIte] at hd
        simp only [OpCode.wp_add, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
          at hwp ⊢
        exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
    | _ => simp [recordDef] at hd
  | sub t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | var x =>
        cases b with
        | imm c =>
          by_cases hn64 : n = 64
          · subst hn64
            simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
            cases hd; cases h1 with | var hm => cases h2 with | imm =>
            simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
            refine ⟨hwp, by simp, ?_⟩
            rw [BitVec.sub_eq_add_neg]; exact defOk_addVarImm hdefs hlt hm
          · have hnf : Nat.beq n 64 = false :=
              Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn64)
            simp only [recordDef, hnf, Bool.false_eq_true, ↓reduceIte] at hd
            simp only [OpCode.wp_sub, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
              at hwp ⊢
            exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
        | var y =>
          simp only [recordDef] at hd
          simp only [OpCode.wp_sub, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
            at hwp ⊢
          exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
      | imm _ =>
        simp only [recordDef] at hd
        cases b <;> simp [recordRmwBin, RmwOp.isComm] at hd
    | _ => simp [recordDef] at hd
  | or t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      simp only [recordDef] at hd
      simp only [OpCode.wp_or, vals, lift2] at hwp ⊢
      exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
    | _ => simp [recordDef] at hd
  | xor t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      simp only [recordDef] at hd
      simp only [OpCode.wp_xor, vals, lift2] at hwp ⊢
      exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
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
          by_cases hn : n = 64
          · subst hn
            have hb64 : Nat.beq 64 64 = true := rfl
            have hk : k.toNat < 64 := Decidable.byContradiction fun hke => by
              simp [recordDef, Nat.blt_eq, hke] at hd
            simp only [recordDef, hb64, ↓reduceIte] at hd
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
                obtain ⟨vb, hb, hvx⟩ := hxok.2 _ hm
                exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx]⟩
              | scaleOff idx sh d =>
                dsimp only at hd; split at hd
                · cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                  cases mem_cons_top hlt hv
                  obtain ⟨vi, hi, hvx⟩ := hxok _ hm
                  exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, bv_shiftLeft_shiftLeft]⟩
                · cases hd
              | addrSum _ _ _ _ | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _
              | binVarImm _ _ _ _ | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _
              | cmpZeroVar _ _ _ | testBitVar _ _ _ _ | shiftVarImm _ _ _ _ =>
                cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                cases mem_cons_top hlt hv
                exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
          · have hnf : Nat.beq n 64 = false :=
              Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn)
            simp only [recordDef, hnf, Bool.false_eq_true, ↓reduceIte] at hd
            split at hd
            · rename_i hc
              simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
              obtain ⟨⟨hnle, _⟩, hklt⟩ := hc
              cases hd
              rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
              cases h1 with | var hm => cases h2 with | imm =>
              dsimp only [vals, Arg.val] at hwp ⊢
              simp only [OpCode.wp_shl, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
                at hwp ⊢
              rw [Nat.mod_eq_of_lt hklt] at hwp ⊢
              refine ⟨hwp, by simp, hnle, hklt, fun v hv => ?_⟩
              simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
              exact ⟨_, List.mem_cons_of_mem _ hm, rfl⟩
            · cases hd
    | _ => simp [recordDef] at hd
  | lshr t | ashr t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | imm _ => simp [recordDef] at hd
      | var x =>
        cases b with
        | var _ => simp [recordDef] at hd
        | imm k =>
          simp only [recordDef, recordShiftImm] at hd
          split at hd
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
            cases hd; cases h1 with | var hm => cases h2 with | imm =>
            dsimp only [vals, Arg.val] at hwp ⊢
            simp only [OpCode.wp_lshr, OpCode.wp_ashr, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false] at hwp ⊢
            rw [Nat.mod_eq_of_lt hc.2] at hwp ⊢
            refine ⟨hwp, by simp, hc.1, hc.2, fun v hv => ?_⟩
            simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            exact ⟨_, List.mem_cons_of_mem _ hm, rfl⟩
          · cases hd
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
          refine ⟨fun t v hv => by
            simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
          simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
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
            refine ⟨fun t v hv => by
              simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
            simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vb, hb, hvx⟩ := h'.2 _ hm
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
          | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _ | binVarImm _ _ _ _
          | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ | cmpZeroVar _ _ _
          | testBitVar _ _ _ _ | shiftVarImm _ _ _ _ =>
            simp only [DefFact.isAddr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd
            subst hd
            refine ⟨fun t v hv => by
              simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv; rfl, fun v hv => ?_⟩
            simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
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
  | or _ => simp only [OpCode.wp_or] at hwp'; exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | xor _ => simp only [OpCode.wp_xor] at hwp'; exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | shl _ =>
    simp only [OpCode.wp_shl, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | lshr _ | ashr _ =>
    simp only [OpCode.wp_lshr, OpCode.wp_ashr, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | copy _ => simp only [OpCode.wp_copy] at hwp'; exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | and _ => simp only [OpCode.wp_and] at hwp'; exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | sext _ _ => simp only [OpCode.wp_sext] at hwp'; exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | zext _ _ => simp only [OpCode.wp_zext] at hwp'; exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | _ => simp [recordDef] at hd

/-- `addrDefOf` (the `GprIsa.addrCse` address view) preserves `DefOk`. -/
theorem addrDefOf_ok {G : VCtx} {cse : Bool} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x : Nat} {df : DefFact}
    (h : addrDefOf cse defs x = some df) : DefOk G x df := by
  unfold addrDefOf at h
  split at h
  · rename_i p c hx
    have hdx := hdefs x _ hx
    split at h
    · split at h
      · rename_i b i sh d hp
        cases h
        intro v hv
        obtain ⟨vp, hmp, hvp⟩ := hdx.2 v hv
        obtain ⟨vb, vi, hb, hi, hvb⟩ := hdefs p _ hp vp hmp
        exact ⟨vb, vi, hb, hi, by rw [hvp, hvb, BitVec.add_assoc]⟩
      · cases h; exact hdx
    · cases h; exact hdx
  · rename_i hx; exact hdefs x df (by rw [← h])

private theorem recordDefC_ok_app {G : VCtx} {cse : Bool} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {sig rs : List Ty}
    {code : OpCode sig rs} {args : Tup (Arg VNat) sig} {df : DefFact}
    (hd : recordDefC cse defs code args = some df) :
    ∃ defs' : Trie DefFact, (∀ x d, defs'.find? x = some d → DefOk G x d) ∧
      recordDef defs' code args = some df := by
  unfold recordDefC at hd
  split at hd
  · exact ⟨_, fun _ _ hx => by simp at hx, hd⟩
  · exact ⟨_, hdefs, hd⟩

theorem wp_recordDefC {G : VCtx} {nv : Nat} {cse : Bool} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {sig rs : List Ty}
    {code : OpCode sig rs} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact}
    (hd : recordDefC cse defs code args = some df) :
    code.wp (vals args₁) (fun rvs => P rvs ∧
      0 < rs.length ∧ DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df) :=
  let ⟨_, hok, hd'⟩ := recordDefC_ok_app hdefs hd
  wp_recordDef hok hrel hlt hwp hd'

theorem recordDefC_elide_ok {G : VCtx} {nv : Nat} {cse : Bool} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {sig rs : List Ty}
    {code : OpCode sig rs} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact}
    (hd : recordDefC cse defs code args = some df) :
    ∃ (w : Nat) (_h : rs = [.bits w]) (rvs : Tup Val rs), P rvs ∧
      DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df :=
  let ⟨_, hok, hd'⟩ := recordDefC_ok_app hdefs hd
  recordDef_elide_ok hok hrel hlt hwp hd'

end Rega
end LeanQbe.T
