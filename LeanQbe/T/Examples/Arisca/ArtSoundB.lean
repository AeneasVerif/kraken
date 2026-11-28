module

public import LeanQbe.T.Examples.Arisca.ArtSound
public import LeanQbe.T.Examples.Arisca.ArtCoreB

/-!
# Soundness of the geobucket checker `checkArtB`

Same statement as `checkArt_sound`. The MAIN invariant is `evalT σ buckets = evalP σ P₀`,
where `evalT` sums all buckets. `setNE` never evicts, `lead`/`nz` are arbitrary hints.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanQbe.T.Examples.Arisca

@[expose] public section

/-- sum of all buckets -/
noncomputable def evalT (w : Nat) (σ : Nat → Bool) : Tree Poly → BitVec w
  | .empty => 0
  | .tip _ v => evalP w σ v
  | .br l r => evalT w σ l + evalT w σ r

end

public section

variable {w : Nat} {σ : Nat → Bool}

theorem Tree.setNEP_eval (k : Nat) (v : Poly) (d : Nat) :
    ∀ (p : Nat) (t t' : Tree Poly), Tree.setNEP k v d p t = some t' →
      evalT w σ t' + evalP w σ (Option.rec Poly.nil (fun q => q) (Tree.getP k d p t)) =
        evalT w σ t + evalP w σ v := by
  induction d with
  | zero =>
    intro p t t' h
    cases t with
    | empty =>
      cases h
      show evalP w σ v + evalP w σ Poly.nil = 0 + evalP w σ v
      rw [evalP_nil]; grind
    | tip k' v' =>
      change (Bool.rec none (some (Tree.tip k v)) (Nat.beq k k') : Option (Tree Poly)) =
        some t' at h
      cases hb : Nat.beq k k' <;> rw [hb] at h <;> simp only [brec_false, brec_true] at h
      · cases h
      · cases h
        change evalP w σ v + evalP w σ (Option.rec Poly.nil (fun q => q)
          (Bool.rec none (some v') (Nat.beq k k') : Option Poly)) = evalP w σ v' + evalP w σ v
        rw [hb]; simp only [brec_true, orec_some]; exact BitVec.add_comm _ _
    | br l r => cases h
  | succ d ih =>
    intro p t t' h
    have side : ∀ (l r : Tree Poly),
        Tree.setNEP k v (d+1) p (Tree.br l r) = some t' →
        evalT w σ t' + evalP w σ
          (Option.rec Poly.nil (fun q => q) (Tree.getP k (d+1) p (Tree.br l r))) =
          evalT w σ (Tree.br l r) + evalP w σ v := by
      intro l r h
      change (Bool.rec
          (Option.rec none (fun c => some (Tree.br l c))
            (Tree.setNEP k v d (Nat.shiftRight p 1) r))
          (Option.rec none (fun c => some (Tree.br c r))
            (Tree.setNEP k v d (Nat.shiftRight p 1) l))
          (Nat.beq (Nat.land p 1) 0) : Option (Tree Poly)) = some t' at h
      change evalT w σ t' + evalP w σ (Option.rec Poly.nil (fun q => q)
        (Bool.rec (Tree.getP k d (Nat.shiftRight p 1) r) (Tree.getP k d (Nat.shiftRight p 1) l)
          (Nat.beq (Nat.land p 1) 0) : Option Poly)) = evalT w σ l + evalT w σ r + evalP w σ v
      cases hp : Nat.beq (Nat.land p 1) 0 <;> rw [hp] at h <;>
        simp only [brec_false, brec_true] at h ⊢
      · cases hc : Tree.setNEP k v d (Nat.shiftRight p 1) r with
        | none => rw [hc] at h; cases h
        | some c =>
          rw [hc] at h; simp only [orec_some] at h; cases h
          have := ih _ r c hc
          simp only [evalT]; grind
      · cases hc : Tree.setNEP k v d (Nat.shiftRight p 1) l with
        | none => rw [hc] at h; cases h
        | some c =>
          rw [hc] at h; simp only [orec_some] at h; cases h
          have := ih _ l c hc
          simp only [evalT]; grind
    cases t with
    | empty =>
      have h' : Tree.setNEP k v (d+1) p (Tree.br Tree.empty Tree.empty) = some t' := by
        change (Bool.rec
          (Option.rec none (fun c => some (Tree.br Tree.empty c))
            (Tree.setNEP k v d (Nat.shiftRight p 1) Tree.empty))
          (Option.rec none (fun c => some (Tree.br c Tree.empty))
            (Tree.setNEP k v d (Nat.shiftRight p 1) Tree.empty))
          (Nat.beq (Nat.land p 1) 0) : Option (Tree Poly)) = some t' at h
        exact h
      have := side _ _ h'
      have e1 : Tree.getP k (d+1) p (Tree.br (Tree.empty : Tree Poly) Tree.empty) = none := by
        change (Bool.rec (Tree.getP k d (Nat.shiftRight p 1) Tree.empty)
          (Tree.getP k d (Nat.shiftRight p 1) Tree.empty)
          (Nat.beq (Nat.land p 1) 0) : Option Poly) = none
        rw [Tree.getP_empty]; cases Nat.beq (Nat.land p 1) 0 <;> rfl
      rw [e1] at this; rw [Tree.getP_empty]
      simpa [evalT] using this
    | tip a b => cases h
    | br l r => exact side l r h

theorem setNE_eval {d k : Nat} {v : Poly} {t t' : Tree Poly} (h : t.setNE d k v = some t') :
    evalT w σ t' + evalP w σ (bget d k t) = evalT w σ t + evalP w σ v :=
  Tree.setNEP_eval k v d k t t' h

theorem allNil_eval (t : Tree Poly) (h : allNil t = true) : evalT w σ t = 0 := by
  induction t with
  | empty => rfl
  | tip k v => exact isNil_eval v h
  | br l r ihl ihr =>
    change (Bool.rec false (allNil r) (allNil l) : Bool) = true at h
    obtain ⟨hl, hr⟩ := band_true h
    simp only [evalT, ihl hl, ihr hr]; exact BitVec.add_zero _

theorem appendP_eval (p q : Poly) : evalP w σ (appendP p q) = evalP w σ p + evalP w σ q := by
  induction p with
  | nil => show evalP w σ q = 0 + evalP w σ q; exact (BitVec.zero_add _).symm
  | cons c m p ih =>
    show BitVec.ofNat w c * monoVal w σ m + evalP w σ (appendP p q) = _
    rw [ih, evalP_cons]; grind

theorem run_eval (b : Nat) (q : Poly) :
    evalP w σ (takeRun b q) + evalP w σ (dropRun b q) = evalP w σ q := by
  induction q with
  | nil => show (0 : BitVec w) + 0 = 0; exact BitVec.add_zero _
  | cons c m q ih =>
    change evalP w σ (Bool.rec Poly.nil (Poly.cons c m (takeRun b q)) (Nat.ble b m)) +
      evalP w σ (Bool.rec (Poly.cons c m q) (dropRun b q) (Nat.ble b m)) = _
    cases Nat.ble b m <;> simp only [brec_false, brec_true]
    · show (0 : BitVec w) + _ = _; exact BitVec.zero_add _
    · rw [evalP_cons, evalP_cons, ← ih]; grind

theorem addBucket_ok (M : Nat) (hM : M = 2 ^ w) (bd k : Nat) (B : Poly) (t : Tree Poly) (nz : Nat)
    (kont : Tree Poly → Nat → Bool) (h : addBucket M bd k B t nz kont = true) :
    ∃ t' nz', evalT w σ t' = evalT w σ t + evalP w σ B ∧ kont t' nz' = true := by
  unfold addBucket at h
  obtain ⟨t', ht, h⟩ := orec_true h
  refine ⟨t', _, ?_, h⟩
  have := setNE_eval (w := w) (σ := σ) ht
  rw [merge_eval M hM] at this
  grind

theorem insRuns_ok (M : Nat) (hM : M = 2 ^ w) (bd : Nat) (lead : Nat → Nat) (fuel : Nat) :
    ∀ (Q : Poly) (t : Tree Poly) (nz : Nat) (kont : Tree Poly → Nat → Bool),
      insRuns M bd lead fuel Q t nz kont = true →
      ∃ t' nz', evalT w σ t' = evalT w σ t + evalP w σ Q ∧ kont t' nz' = true := by
  induction fuel with
  | zero => intro Q t nz kont h; cases h
  | succ f ih =>
    intro Q t nz kont h
    cases Q with
    | nil => exact ⟨t, nz, by rw [evalP_nil]; exact (BitVec.add_zero _).symm, h⟩
    | cons c m q =>
      change addBucket M bd (lead m) (Poly.cons c m (takeRun (Nat.pow 2 (lead m)) q)) t nz
        (fun t' nz' => insRuns M bd lead f (dropRun (Nat.pow 2 (lead m)) q) t' nz' kont) =
        true at h
      obtain ⟨t1, nz1, h1, h⟩ := addBucket_ok (σ := σ) M hM bd _ _ t nz _ h
      obtain ⟨t2, nz2, h2, h⟩ := ih _ t1 nz1 kont h
      refine ⟨t2, nz2, ?_, h⟩
      rw [h2, h1, evalP_cons, evalP_cons, ← run_eval (Nat.pow 2 (lead m)) q]
      grind

theorem collB_ok (bd s : Nat) (lead : Nat → Nat) (fuel : Nat) :
    ∀ (H : Nat) (t : Tree Poly) (nz : Nat) (W : Poly) (kont : Tree Poly → Nat → Poly → Bool),
      collB bd s lead fuel H t nz W kont = true →
      ∃ t' nz' W',
        evalT w σ t' + bv w (σ s) * evalP w σ W' = evalT w σ t + bv w (σ s) * evalP w σ W ∧
        kont t' nz' W' = true := by
  induction fuel with
  | zero => intro H t nz W kont h; cases h
  | succ f ih =>
    intro H t nz W kont h
    change (Bool.rec
        (Option.rec false
          (fun t' => collB bd s lead f (Nat.xor H (Nat.land H (Nat.xor H (Nat.sub H 1)))) t'
            (nzUpd nz (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1)))))
              (filterS (Nat.pow 2 s)
                (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t)))
            (appendP (collectS (Nat.pow 2 s)
              (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t)) W) kont)
          (t.setNE bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1)))))
            (filterS (Nat.pow 2 s)
              (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t))))
        (kont t nz W)
        (Nat.beq H 0) : Bool) = true at h
    generalize Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1)))) = kk at h
    cases hH : Nat.beq H 0 <;> rw [hH] at h <;> simp only [brec_false, brec_true] at h
    · obtain ⟨t1, ht1, h⟩ := orec_true h
      obtain ⟨t2, nz2, W2, h2, h⟩ := ih _ t1 _ _ kont h
      refine ⟨t2, nz2, W2, ?_, h⟩
      have e1 := setNE_eval (w := w) (σ := σ) ht1
      have e2 := split_eval (w := w) (σ := σ) s (bget bd kk t)
      rw [h2, appendP_eval]
      grind
    · exact ⟨t, nz, W, rfl, h⟩

theorem substB_ok (M : Nat) (hM : M = 2 ^ w) (bd : Nat) (lead : Nat → Nat) (van : Nat → Bool)
    (hv : VanOk w σ van) (s : Nat) (R : Poly) (hR : bv w (σ s) = evalP w σ R)
    (t : Tree Poly) (nz : Nat) (kont : Tree Poly → Nat → Bool)
    (h : substB M bd lead van s R t nz kont = true) :
    ∃ t' nz', evalT w σ t' = evalT w σ t ∧ kont t' nz' = true := by
  unfold substB at h
  obtain ⟨t1, nz1, W, h1, h⟩ := collB_ok (w := w) (σ := σ) bd s lead _ _ t nz Poly.nil _ h
  obtain ⟨t2, nz2, h2, h⟩ := insRuns_ok (σ := σ) M hM bd lead _ _ t1 nz1 kont h
  refine ⟨t2, nz2, ?_, h⟩
  rw [h2, sumB_eval M hM, mulTerms_eval M hM van hv, ← hR]
  rw [evalP_nil] at h1
  grind

section mainB
variable (e : Env) (hM : e.M = 2 ^ w) (hflip : ∀ x, σ (2 * x + 1) = !σ (2 * x))

include hM hflip in
theorem mainLoopB_ok (pr : Pairs) (hpr : PairsOk σ pr) (rules : Tree Poly)
    (hr : RulesOk w σ e rules) (nNets bd : Nat) (lead : Nat → Nat) (X : BitVec w) (n : Nat) :
    ∀ t nz fl ws, evalT w σ t = X → mainLoopB e pr rules nNets bd lead n t nz fl ws = true →
      X = 0 := by
  induction n with
  | zero =>
    intro t nz fl ws hX h
    change (Bool.rec false (allNil t) (List.rec true (fun _ _ _ => false) ws) : Bool) = true at h
    obtain ⟨-, h⟩ := band_true h
    rw [← hX, allNil_eval t h]
  | succ n ih =>
    intro t nz fl ws hX h
    change rd ws false (fun op ws =>
        Bool.rec
          (Option.rec false
            (fun R0 =>
              Bool.rec
                (substB e.M bd lead (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                  (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) t nz
                  (fun t nz => mainLoopB e pr rules nNets bd lead n t nz fl ws))
                (substB e.M bd lead (van pr) (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)
                  (oneSub e.M (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0)) t nz
                  (fun t nz => mainLoopB e pr rules nNets bd lead n t nz fl ws))
                (tb fl (Nat.mul 2 (Nat.shiftRight op 1))))
            (rules.get e.nd (Nat.shiftRight op 1)))
          (Bool.rec
            (substB e.M bd lead (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
              (oneSub e.M
                (single e.M 1 (Nat.pow 2 (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)))) t nz
              (fun t nz => mainLoopB e pr rules nNets bd lead n t nz
                (Nat.lor fl (Nat.pow 2 (Nat.mul 2 (Nat.shiftRight op 1)))) ws))
            false
            (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
              (Nat.ble nNets (Nat.shiftRight op 1))))
          (Nat.beq (Nat.land op 1) 1)) = true at h
    obtain ⟨op, ws', -, h⟩ := rd_true h
    have hv := van_ok (w := w) pr hpr
    cases hf : Nat.beq (Nat.land op 1) 1
    · rw [hf] at h; simp only [brec_false] at h
      obtain ⟨R0, hR0, h⟩ := orec_true h
      have hR1 : bv w (σ (Nat.mul 2 (Nat.shiftRight op 1))) =
          evalP w σ (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) := by
        rw [flipR_eval e.M hM hflip]; exact hr _ R0 hR0
      cases hfl : tb fl (Nat.mul 2 (Nat.shiftRight op 1))
      · rw [hfl] at h; simp only [brec_false] at h
        obtain ⟨t', nz', ht', h⟩ := substB_ok e.M hM bd lead _ hv _ _ hR1 t nz _ h
        exact ih t' nz' fl ws' (by rw [ht']; exact hX) h
      · rw [hfl] at h; simp only [brec_true] at h
        have hR2 : bv w (σ (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)) =
            evalP w σ (oneSub e.M (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0)) := by
          show bv w (σ (2 * Nat.shiftRight op 1 + 1)) = _
          rw [hflip, bv_not, oneSub_eval e.M hM, ← hR1]; rfl
        obtain ⟨t', nz', ht', h⟩ := substB_ok e.M hM bd lead _ hv _ _ hR2 t nz _ h
        exact ih t' nz' fl ws' (by rw [ht']; exact hX) h
    · rw [hf] at h; simp only [brec_true] at h
      cases hc : (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
          (Nat.ble nNets (Nat.shiftRight op 1)) : Bool)
      · rw [hc] at h; simp only [brec_false] at h
        obtain ⟨t', nz', ht', h⟩ :=
          substB_ok e.M hM bd lead _ hv _ _ (flipPoly_eval e.M hM hflip _).symm t nz _ h
        exact ih t' nz' _ ws' (by rw [ht']; exact hX) h
      · rw [hc] at h; cases h

end mainB

theorem checkWordsB_sound (signed : Bool) (g : Aig) (ws0 : List Nat)
    (h : checkWordsB signed g ws0 = true) : ∀ ρ : Nat → Bool,
      BitVec.ofNat g.outs.length (outWord g ρ) =
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2)) := by
  intro ρ
  unfold checkWordsB at h
  obtain ⟨hd, ws1, hhl, h⟩ := rdN_true h
  obtain ⟨hhdr, h⟩ := band_true h
  obtain ⟨bindW, ws2, -, h⟩ := rdN_true h
  obtain ⟨bt, -, h⟩ := orec_true h
  unfold afterBindB at h
  obtain ⟨inNet, ws3, hinl, h⟩ := rdN_true h
  obtain ⟨outRef, ws4, houtl, h⟩ := rdN_true h
  obtain ⟨hio, h⟩ := band_true h
  obtain ⟨hin, hout⟩ := band_true hio
  unfold headerOk at hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨hI, hhdr⟩ := band_true hhdr
  obtain ⟨hI, hev⟩ := band_true hI
  obtain ⟨hO, -⟩ := band_true hhdr
  rw [beq_true] at hI hO hev
  rw [len_eq] at hO
  generalize hw : g.outs.length = w at hO
  let e : Env := ⟨Nat.pow 2 (nthN hd 4), g.M, g.I, bitLen g.M, andTree (bitLen g.M) g.I g.ands,
    bitLen (nthN hd 5), bt⟩
  have hM : e.M = 2 ^ w := by show Nat.pow 2 (nthN hd 4) = 2 ^ w; rw [hO]; rfl
  have hT : e.andT = andTree e.ad g.I g.ands := rfl
  unfold runPhasesB at h
  have hinit : GInv w (sig g ρ e) e ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ :=
    ⟨fun v Q hv => by simp [Tree.get_empty] at hv, fun c s hcs => by simp [Tree.get_empty] at hcs⟩
  obtain ⟨st, ws5, hst, h⟩ := gates_ok g ρ e hM hT _ _ _ ws4 hinit h
  obtain ⟨st', ws6, hst', h⟩ := cones_ok e hM _ _ st ws5 hst h
  obtain ⟨t0, nz0, ht0, h⟩ := insRuns_ok (σ := sig g ρ e) e.M hM _ _ _ _ Tree.empty 0 _ h
  have hP := mainLoopB_ok e hM (sig_flip g ρ e) st'.pr hst'.2 st'.rules hst'.1 _ _ _
    (evalP w (sig g ρ e)
      (initP e.M st'.pr signed (Nat.shiftRight (nthN hd 3) 1) inNet outRef))
    _ t0 nz0 0 ws6 (by rw [ht0]; exact BitVec.zero_add _) h
  rw [initP_eval e.M hM st'.pr (van_ok st'.pr hst'.2)] at hP
  have hn : Nat.shiftRight (nthN hd 3) 1 = g.I / 2 := by rw [shiftRight_one, hI]
  rw [hn] at hP
  have hinl' : inNet.length = g.I := by rw [hinl, hI]
  have hev' : g.I % 2 = 0 := by rw [← hI, ← land_one]; exact hev
  have hinb := inOk_spec e (nthN hd 5) inNet 0 hin
  obtain ⟨htl, htn⟩ := takeN_spec (g.I / 2) inNet (by omega)
  obtain ⟨hdl, hdn⟩ := dropN_spec (g.I / 2) inNet
  have hA : inSum w (sig g ρ e) signed (g.I / 2) (takeN (g.I / 2) inNet) 0 =
      BitVec.ofInt w (inWord signed (g.I / 2) ρ 0) := by
    rw [inSum_eq signed (g.I / 2) ρ 0 _ 0 (fun k hk => ?_), htl]
    · unfold inWord; rw [List.range_eq_range']
    · rw [htl] at hk
      rw [htn k hk, sig_bound g ρ e (hinb k (by omega)), Nat.zero_add, Nat.zero_add,
        litVal_pi g ρ k (by omega)]
  have hB : inSum w (sig g ρ e) signed (g.I / 2) (dropN (g.I / 2) inNet) 0 =
      BitVec.ofInt w (inWord signed (g.I / 2) ρ (g.I / 2)) := by
    rw [inSum_eq signed (g.I / 2) ρ (g.I / 2) _ 0 (fun k hk => ?_), hdl,
      show inNet.length - g.I / 2 = g.I / 2 by omega]
    · unfold inWord; rw [List.range_eq_range']
    · rw [hdl] at hk
      rw [hdn k, sig_bound g ρ e (hinb (g.I / 2 + k) (by omega)), Nat.zero_add, Nat.zero_add,
        litVal_pi g ρ _ (by omega)]
  have hob := outOkAll_spec e (nthN hd 5) outRef g.outs hout
  have hC : outSum w (sig g ρ e) outRef 0 = BitVec.ofNat w (outWord g ρ) := by
    rw [outSum_eq g ρ outRef 0 (fun k hk => ?_)]
    · unfold outWord; rw [hw, houtl, hO, List.range_eq_range']
    · obtain ⟨-, b, hb1, hb2⟩ := hob k hk
      have hb1' : e.bind.get e.nd (nthN outRef k / 2) = some b := by
        rw [← shiftRight_one]; exact hb1
      rw [sig_bound g ρ e hb1', Nat.zero_add, ← litVal_xor, hb2, nthN_eq_getD]
  rw [hA, hB, hC] at hP
  have := congrArg (· + BitVec.ofInt w (inWord signed (g.I / 2) ρ 0) *
    BitVec.ofInt w (inWord signed (g.I / 2) ρ (g.I / 2))) hP
  simp only [BitVec.sub_add_cancel] at this
  rw [this]; exact BitVec.zero_add _

theorem checkArtB_sound (signed : Bool) (aigN aigLen artN artLen : Nat)
    (h : checkArtB signed aigN aigLen artN artLen = true) :
    ∃ g, parseAig (toBytes aigN aigLen) = some g ∧ ∀ ρ : Nat → Bool,
      BitVec.ofNat g.outs.length (outWord g ρ) =
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2)) := by
  unfold checkArtB at h
  obtain ⟨g, hg, h⟩ := orec_true h
  obtain ⟨-, h⟩ := band_true h
  exact ⟨g, hg, checkWordsB_sound signed g _ h⟩

/-! ## Geobucket ART v1.5 Miter Soundness (`SPEC_MITER`, `spec = 2`) -/

theorem checkWordsBMiter_sound (g : Aig) (ws0 : List Nat) (h : checkWordsBMiter g ws0 = true) :
    g.outs.length % 2 = 0 ∧ 2 ≤ g.outs.length ∧ g.outs.length ≤ 256 ∧
      ∀ ρ : Nat → Bool,
        BitVec.ofNat (g.outs.length / 2) (outSlice g ρ 0 (g.outs.length / 2)) =
          BitVec.ofNat (g.outs.length / 2)
            (outSlice g ρ (g.outs.length / 2) (g.outs.length / 2)) := by
  unfold checkWordsBMiter at h
  obtain ⟨hd, ws1, -, h⟩ := rdN_true h
  obtain ⟨hhdr, h⟩ := band_true h
  obtain ⟨bindW, ws2, -, h⟩ := rdN_true h
  obtain ⟨bt, -, h⟩ := orec_true h
  unfold afterBindBMiter at h
  obtain ⟨inNet, ws3, -, h⟩ := rdN_true h
  obtain ⟨outRef, ws4, houtl, h⟩ := rdN_true h
  obtain ⟨hio, h⟩ := band_true h
  obtain ⟨-, hout⟩ := band_true hio
  unfold headerMiterOk at hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨hO, hhdr⟩ := band_true hhdr
  obtain ⟨hge2, hhdr⟩ := band_true hhdr
  obtain ⟨hevO, hhdr⟩ := band_true hhdr
  obtain ⟨hle128, -⟩ := band_true hhdr
  rw [beq_true] at hO hevO
  rw [ble_true] at hge2 hle128
  rw [len_eq] at hO
  have hO_even : g.outs.length % 2 = 0 := by
    rw [← hO, ← land_one]; exact hevO
  have hO_ge2 : 2 ≤ g.outs.length := by rw [← hO]; exact hge2
  have hO_le256 : g.outs.length ≤ 256 := by
    have hshr : Nat.shiftRight (nthN hd 4) 1 = nthN hd 4 / 2 := shiftRight_one _
    rw [hshr] at hle128; rw [← hO]; omega
  refine ⟨hO_even, hO_ge2, hO_le256, fun ρ => ?_⟩
  generalize hmw : g.outs.length / 2 = w
  let e : Env := ⟨Nat.pow 2 (Nat.shiftRight (nthN hd 4) 1), g.M, g.I, bitLen g.M,
    andTree (bitLen g.M) g.I g.ands, bitLen (nthN hd 5), bt⟩
  have hmw' : Nat.shiftRight (nthN hd 4) 1 = w := by rw [shiftRight_one, hO, hmw]
  have hM : e.M = 2 ^ w := by show Nat.pow 2 (Nat.shiftRight (nthN hd 4) 1) = 2 ^ w; rw [hmw']; rfl
  have hT : e.andT = andTree e.ad g.I g.ands := rfl
  unfold runPhasesBMiter at h
  have hinit : GInv w (sig g ρ e) e ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ :=
    ⟨fun v Q hv => by simp [Tree.get_empty] at hv, fun c s hcs => by simp [Tree.get_empty] at hcs⟩
  obtain ⟨st, ws5, hst, h⟩ := gates_ok g ρ e hM hT _ _ _ ws4 hinit h
  obtain ⟨st', ws6, hst', h⟩ := cones_ok e hM _ _ st ws5 hst h
  obtain ⟨t0, nz0, ht0, h⟩ := insRuns_ok (σ := sig g ρ e) e.M hM _ _ _ _ Tree.empty 0 _ h
  have hP := mainLoopB_ok e hM (sig_flip g ρ e) st'.pr hst'.2 st'.rules hst'.1 _ _ _
    (evalP w (sig g ρ e)
      (initPMiter e.M st'.pr st'.rules e.nd (Nat.shiftRight (nthN hd 4) 1) outRef g.outs))
    _ t0 nz0 0 ws6 (by rw [ht0]; exact BitVec.zero_add _) h
  have hP' : evalP w (sig g ρ e) (initPMiter e.M st'.pr st'.rules e.nd w outRef g.outs) = 0 := by
    simpa only [e, hmw'] using hP
  rw [initPMiter_eval (nNets := nthN hd 5) g ρ e hM st'.pr (van_ok st'.pr hst'.2) st'.rules w
    outRef (by rw [houtl, hO]; omega) (by omega) hout] at hP'
  have := congrArg (· + BitVec.ofNat w (outSlice g ρ w w)) hP'
  simp only [BitVec.sub_add_cancel] at this
  rw [this]; exact BitVec.zero_add _

theorem checkArtBMiter_sound (aigN aigLen artN artLen : Nat)
    (h : checkArtBMiter aigN aigLen artN artLen = true) :
    ∃ g, parseAig (toBytes aigN aigLen) = some g ∧
      g.outs.length % 2 = 0 ∧ 2 ≤ g.outs.length ∧ g.outs.length ≤ 256 ∧
      ∀ ρ : Nat → Bool,
        BitVec.ofNat (g.outs.length / 2) (outSlice g ρ 0 (g.outs.length / 2)) =
          BitVec.ofNat (g.outs.length / 2)
            (outSlice g ρ (g.outs.length / 2) (g.outs.length / 2)) := by
  unfold checkArtBMiter at h
  obtain ⟨g, hg, h⟩ := orec_true h
  obtain ⟨-, h⟩ := band_true h
  exact ⟨g, hg, checkWordsBMiter_sound g _ h⟩

end

end LeanQbe.T.Examples.Arisca
