module

public import LeanQbe.T.Examples.Kissat.FullM4SweepKitten1

/-!
# Kissat `D-Full` M4b — 512-Var `kitten` 2WL Watch Cursor, `flip`, & `propagate` (`Part 2`)

1. Shared 2WL watch-chain cursor (`K5WChainCursor`), keep/relocate preservation
   (`k5WatchKeep_preserves`, `k5WatchReloc_preserves`), and literal-flip preservation
   (`k5FlipFinish_preserves`).
2. Parametric `(Γ : Env)` `Func.wp` proofs for `2/24` functions (`9/24` cumulative):
   - `full_k512_flip_wp`
   - `full_k512_propagate_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped K512MemATactics

/-! ## 1. 2WL Watch-Chain Cursor & Keep/Relocate/Flip Preservation -/

private theorem k5_list_flatten_set_sub_perm {α : Type} (xs : List (List α)) {l : Nat}
    (hi : l < xs.length) (done todo' : List α) (w0 : α)
    (heq : xs[l]'hi = done ++ w0 :: todo') :
    xs.flatten.Perm (w0 :: (xs.set l (done ++ todo')).flatten) := by
  induction xs generalizing l with
  | nil => simp at hi
  | cons x tl ih =>
    cases l with
    | zero =>
      simp only [List.getElem_cons_zero] at heq
      simp only [List.set_cons_zero, List.flatten_cons, heq, List.append_assoc]
      exact List.perm_middle
    | succ l' =>
      simp only [List.getElem_cons_succ] at heq
      simp only [List.set_cons_succ, List.flatten_cons]
      exact ((ih (by simp at hi; omega) heq).append_left x).trans List.perm_middle

private theorem k5_list_flatten_nodup_getElem {α : Type} :
    ∀ {xs : List (List α)}, xs.flatten.Nodup → ∀ {i : Nat} (hi : i < xs.length),
      (xs[i]'hi).Nodup ∧ ∀ j, j ≠ i → (hj : j < xs.length) → ∀ a ∈ xs[i]'hi, a ∉ xs[j]'hj
  | [], _, _, hi => absurd hi (by simp)
  | x :: tl, hnd, 0, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    refine ⟨ha.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero => exact hne rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      simp only [List.getElem_cons_zero] at hai; simp only [List.getElem_cons_succ] at haj
      exact ha.2.2 a hai a (List.mem_flatten.mpr ⟨tl[j'], List.getElem_mem hj', haj⟩) rfl
  | x :: tl, hnd, i + 1, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    have hi' : i < tl.length := by simp at hi; exact hi
    have ihr := k5_list_flatten_nodup_getElem ha.2.1 hi'
    refine ⟨ihr.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem_cons_succ] at hai; simp only [List.getElem_cons_zero] at haj
      exact ha.2.2 a haj a (List.mem_flatten.mpr ⟨tl[i], List.getElem_mem hi', hai⟩) rfl
    | succ j' =>
      exact ihr.2 j' (fun h => hne (congrArg Nat.succ h)) (by simp at hj; exact hj) a hai haj

theorem k5_wchain_bypass {wn : List (BitVec 32)} {hd nxt : BitVec 32}
    {pfx : List Nat} {u w0 : Nat} {todo' : List Nat}
    (hc : K5WChain wn hd (pfx ++ u :: w0 :: todo'))
    (hnd : (pfx ++ u :: w0 :: todo').Nodup)
    (hu : u < wn.length) (hw0 : w0 < wn.length) (hnxt : wn[w0]'hw0 = nxt) :
    K5WChain (wn.set u nxt) hd (pfx ++ [u] ++ todo') := by
  induction pfx generalizing hd with
  | nil =>
    simp only [List.nil_append, List.singleton_append] at hc hnd ⊢
    rcases K5WChain_cases hc with ⟨_, hc_nil⟩ | ⟨u', ws1, hu', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hu_eq, hws1⟩ := List.cons.inj hcons; subst hhd hu_eq hws1
      rcases K5WChain_cases htail with ⟨_, hnil⟩ | ⟨w', ws2, hw', hw_eq, hcons2, htail2⟩
      · cases hnil
      · obtain ⟨hw0_eq, hws2⟩ := List.cons.inj hcons2; subst hw0_eq hws2
        have hnd_u : u ∉ w0 :: todo' := (List.nodup_cons.mp hnd).1
        have hu_nt : u ∉ todo' := fun h => hnd_u (List.mem_cons_of_mem _ h)
        have htail_c : K5WChain (wn.set u nxt) nxt todo' := by
          rw [← hnxt]
          exact htail2.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
        have hus : u < (wn.set u nxt).length := by simp [hu]
        exact K5WChain.cons hus (by rw [List.getElem_set_self]; exact htail_c)
  | cons x xs ih =>
    simp only [List.cons_append] at hc hnd ⊢
    rcases K5WChain_cases hc with ⟨_, hc_nil⟩ | ⟨x', ws1, hx', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hx_eq, hws1⟩ := List.cons.inj hcons; subst hhd hx_eq hws1
      have hnd_x := List.nodup_cons.mp hnd
      have hxu : x ≠ u := fun h => hnd_x.1 (h ▸ List.mem_append_right xs List.mem_cons_self)
      have hxs_s : x < (wn.set u nxt).length := by simp [hx']
      have hset_x : (wn.set u nxt)[x]'hxs_s = wn[x]'hx' := List.getElem_set_ne hxu.symm hxs_s
      have ih' := ih htail hnd_x.2
      rw [← hset_x] at ih'; exact K5WChain.cons hxs_s ih'

structure K5WChainCursor (ks : K512State) (l : Nat) (chains : List (List Nat))
    (done todo : List Nat) (prev w : BitVec 32) : Prop where
  len_eq : chains.length = 2 * ks.nv.toNat
  nodup : chains.flatten.Nodup
  chain_l : chains[l]?.getD [] = done ++ todo
  chains_wc : ∀ x < 2 * ks.nv.toNat,
    K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])
  chains_bnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
    u < 2 * ks.nc.toNat ∧ 2 ≤ k5ClauseSize ks (u / 2) ∧
    (ks.arena[k5ClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
    (ks.wblit[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
  tail_wc : K5WChain ks.wnext w todo
  prev_rel : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks.whead[l]?.getD 0xFFFFFFFF#32 = w) ∨
    (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
      u < ks.wnext.length ∧ ks.wnext[u]?.getD 0xFFFFFFFF#32 = w)

theorem K5WChainCursor.watchesOk {ks : K512State} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K5WChainCursor ks l chains done todo prev w) : K512WatchesOk ks :=
  ⟨chains, wc.len_eq, wc.nodup, wc.chains_wc, wc.chains_bnd⟩

theorem K5WChainCursor.init {acap : Nat} {ks : K512State} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ k5MaxV) (hw : K512WatchesOk ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) :
    ∃ chains, K5WChainCursor ks l chains [] (chains[l]?.getD []) 0xFFFFFFFF#32
      (ks.whead[l]?.getD 0#32) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold k5MaxV at hnv; omega
  have hwh_eq : ks.whead[l]?.getD 0#32 = ks.whead[l]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwh_len]; rfl
  rw [hwh_eq]
  exact ⟨chains, hlen, hnd, rfl, hwc, hbnd, hwc l hl, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem K5WChainCursor.step_unfold {ks : K512State} (hnc : ks.nc.toNat ≤ k5MaxCl)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K5WChainCursor ks l chains done todo prev w) (hne : w ≠ 0xFFFFFFFF#32) :
    ∃ w0 todo', w0 < ks.wnext.length ∧
      todo = w0 :: todo' ∧ w = BitVec.ofNat 32 w0 ∧ w0 < 2 * ks.nc.toNat ∧ w0 < 4096 ∧
      w.toNat = w0 ∧ (w >>> (1 : Nat)).toNat = w0 / 2 ∧ (w &&& 1#32).toNat = w0 % 2 ∧
      2 ≤ k5ClauseSize ks (w0 / 2) ∧
      (ks.arena[k5ClauseOff ks (w0 / 2) + (w0 % 2)]?.getD 0#32).toNat = l ∧
      (ks.wblit[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat ∧
      K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo' := by
  obtain ⟨w0, todo', hw0, htd, hw_eq, htail⟩ := K5WChain_getElem_of_eq wc.tail_wc hne
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l, htd]; exact List.mem_append_right _ List.mem_cons_self
  have hb := wc.chains_bnd l hl w0 hm_l
  have hw0_4096 : w0 < 4096 := by unfold k5MaxCl at hnc; omega
  have hw_tn : w.toNat = w0 := by rw [hw_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw_div2 : (w >>> (1 : Nat)).toNat = w0 / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hw_tn]
  have hw_mod2 : (w &&& 1#32).toNat = w0 % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 1, hw_tn]
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0 := by
    rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  refine ⟨w0, todo', hw0, htd, hw_eq, hb.1, hw0_4096, hw_tn, hw_div2, hw_mod2,
    hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  rw [hnxt_eq]; exact htail

theorem k5WatchSkip_cursor {acap : Nat} {ks : K512State} (hsh : ks.ShapesOk acap)
    (_hnc : ks.nc.toNat ≤ k5MaxCl)
    {l : Nat} {chains : List (List Nat)} {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K5WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    (hw0_len : w0 < ks.wnext.length) :
    K5WChainCursor ks l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hw0_len]; rfl
  rcases K5WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by rw [hsh.wnext_len] at hw0_len; omega
      have h2 : w0' < 2 ^ 32 := by rw [hsh.wnext_len] at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, wc.chains_bnd, ?_,
      Or.inr ⟨done, w0, rfl, rfl, hw0_len, hnxt_eq.symm⟩⟩
    rwa [List.getElem?_eq_getElem hw0', Option.getD_some]

private theorem k5ClausesOk_cast {acap : Nat} {P : (Nat → Bool) → Prop} {ks ks' : K512State}
    (h : K512ClausesOk acap P ks)
    (h1 : ks'.acap = ks.acap) (h2 : ks'.nv = ks.nv) (h3 : ks'.nc = ks.nc)
    (h4 : ks'.alen = ks.alen) (h5 : ks'.nassump = ks.nassump) (h6 : ks'.nkl = ks.nkl)
    (h7 : ks'.nana = ks.nana) (h8 : ks'.incons = ks.incons) (h9 : ks'.assump = ks.assump)
    (h10 : ks'.flags = ks.flags) (h11 : ks'.clOff = ks.clOff) (h12 : ks'.clSz = ks.clSz)
    (h13 : ks'.arena = ks.arena) : K512ClausesOk acap P ks' := by
  rcases h with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
  refine ⟨c1, c2, h1.trans c3, h2 ▸ c4, h3 ▸ c5, h4 ▸ c6, h5 ▸ c7, h6 ▸ c8, h7 ▸ c9,
    ?_, ?_, h8 ▸ c12, ?_, ?_⟩
  · intro cid hc; rw [h3] at hc
    have := c10 cid hc
    simp only [k5ClauseSize, k5ClauseOff, k5ClauseLits, h11, h12, h13, h4, h2]; exact this
  · intro c1' c2' hlt hc; rw [h3] at hc
    simp only [k5ClauseSize, k5ClauseOff, h11, h12]; exact c11 c1' c2' hlt hc
  · intro i hi; rw [h5] at hi; rw [h9, h2]; exact c13 i hi
  · intro v hv; rw [h2] at hv; rw [h10]; exact c14 v hv

private theorem k5BaseAssignOk_cast {P : (Nat → Bool) → Prop} {ks ks' : K512State}
    (h : K512BaseAssignOk P ks)
    (h1 : ks'.nv = ks.nv) (h2 : ks'.lvl = ks.lvl) (h3 : ks'.prop = ks.prop)
    (h4 : ks'.trl_end = ks.trl_end) (h5 : ks'.unass = ks.unass)
    (h6 : ks'.lvlArr = ks.lvlArr) (h7 : ks'.rsn = ks.rsn)
    (h8 : ks'.trl = ks.trl) (h9 : ks'.vals = ks.vals) : K512BaseAssignOk P ks' := by
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  refine ⟨by rw [h4, h1]; exact a1, by rw [h3, h4]; exact a2, by rw [h5, h4, h1]; exact a3,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a4 l hl,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a5 l hl,
    fun l hl => by rw [h1] at hl; rw [h9, h4, h8]; exact a6 l hl,
    by unfold k5TrailLits; rw [h8, h4]; exact a7,
    fun l hl => by unfold k5TrailLits at hl; rw [h8, h4] at hl; rw [h1]; exact a8 l hl,
    fun v hv => by rw [h1] at hv; rw [h6, h2]; exact a9 v hv,
    fun v hv hv0 => by rw [h1] at hv; rw [h9] at hv0; rw [h6, h7]; exact a10 v hv hv0,
    fun i j hij hj => by rw [h4] at hj; rw [h6, h8]; exact a11 i j hij hj,
    fun i j hij hi hp heq => by
      rw [h4] at hi; rw [h6, h8] at hp heq; rw [h7, h8]; exact a12 i j hij hi hp heq,
    fun i hi => by rw [h4] at hi; dsimp only; rw [h8, h6, h9]; exact a13 i hi⟩

theorem k5WatchKeep_preserves {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K5WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {other : BitVec 32} (hoth : other.toNat < 2 * ks.nv.toNat) :
    let ks' := ks.putArr .wblit w0 other
    K512Inv acap P ks' ∧
    K5WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  intro ks'
  have hsh := hinv.shapes; have hnc := hinv.clauses.nc_le
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hwb_len : w0 < ks.wblit.length := by rw [hsh.wblit_len]; unfold k5MaxCl at hnc; omega
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold k5MaxCl at hnc; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases K5WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold k5MaxCl at hnc; omega
      have h2 : w0' < 2 ^ 32 := by rw [hsh.wnext_len] at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    have wc' : K5WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
        (ks.wnext[w0]?.getD 0#32) := by
      refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, ?_, ?_,
        Or.inr ⟨done, w0, rfl, rfl, hwn_len, hnxt_eq.symm⟩⟩
      · intro x hx u hu; have hbu := wc.chains_bnd x hx u hu
        by_cases hu0 : u = w0
        · rw [hu0] at hbu ⊢
          exact ⟨hbu.1, hbu.2.1, hbu.2.2.1, by
            change ((ks.wblit.set w0 other)[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_self hwb_len, Option.getD_some]; exact hoth⟩
        · exact ⟨hbu.1, hbu.2.1, hbu.2.2.1, by
            change ((ks.wblit.set w0 other)[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_ne (Ne.symm hu0)]; exact hbu.2.2.2⟩
      · change K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo'
        rwa [List.getElem?_eq_getElem hw0', Option.getD_some]
    exact ⟨⟨hsh.putArr .wblit w0 other,
      k5ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      wc'.watchesOk,
      k5BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      by dsimp only [ks', K512State.putArr]; exact hinv.reasons⟩, wc'⟩

theorem k5WatchReloc_preserves {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K5WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {ri : Nat} (hri_ge : 2 ≤ ri) (hri_lt : ri < k5ClauseSize ks (w0 / 2))
    {repl other : BitVec 32} (hrepl_ne : repl.toNat ≠ l)
    (hother_eq : other = ks.arena[k5ClauseOff ks (w0 / 2) + ((w0 % 2) ^^^ 1)]?.getD 0#32)
    (hrepl_eq : repl = ks.arena[k5ClauseOff ks (w0 / 2) + ri]?.getD 0#32) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let cid := w0 / 2
    let slot := w0 % 2
    let off := k5ClauseOff ks cid
    let ar' := (ks.arena.set (off + slot) repl).set (off + ri) (BitVec.ofNat 32 l)
    let wh1 := if prev = 0xFFFFFFFF#32 then ks.whead.set l nxt else ks.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ks.wnext else ks.wnext.set prev.toNat nxt
    let ks1 : K512State := { ks with arena := ar', whead := wh1, wnext := wn1 }
    let ks' := k5WatchStep0 ks1 w repl other
    K512Inv acap P ks' ∧ (∃ chains', K5WChainCursor ks' l chains' done todo' prev nxt) := by
  intro w nxt cid slot off ar' wh1 wn1 ks1 ks'
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le; have hnc := hinv.clauses.nc_le
  have hch_l : l < chains.length := by rw [wc.len_eq]; exact hl
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hcid_lt : cid < ks.nc.toNat := by dsimp only [cid]; omega
  have hwf_c := hinv.clauses.cl_wf cid hcid_lt
  have hsz_ge : 2 ≤ k5ClauseSize ks cid := hb0.2.1
  have hslot_lt : slot < 2 := Nat.mod_lt w0 (by decide)
  have hother_slot_lt : slot ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [slot, h]
  have hoff_le : off + k5ClauseSize ks cid ≤ ks.alen.toNat := hwf_c.2.1
  have har_len : ks.arena.length = acap := hsh.arena_len
  have hal_le : ks.alen.toNat ≤ acap := hinv.clauses.alen_le
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold k5MaxCl at hnc; omega
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold k5MaxV at hnv; omega
  have hnxt_eq : nxt = ks.wnext[w0]'hwn_len := by
    dsimp only [nxt]; rw [List.getElem?_eq_getElem hwn_len, Option.getD_some]
  have hoff_le' : k5ClauseOff ks (w0 / 2) + k5ClauseSize ks (w0 / 2) ≤ ks.alen.toNat := hoff_le
  have har_slot :
      ks.arena[off + slot]'(by dsimp only [off, cid, slot]; omega) = BitVec.ofNat 32 l := by
    have ha := hb0.2.2.1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at ha
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat]
      exact ha.trans (Nat.mod_eq_of_lt (by unfold k5MaxV at hnv; omega)).symm)
  have hrepl_lt_ar : off + ri < ks.arena.length := by dsimp only [off, cid]; omega
  have hrepl_mem : repl.toNat ∈ k5ClauseLits ks cid := by
    rw [hrepl_eq, k5_mem_clauseLits_iff (by omega)]; exact ⟨ri, hri_lt, rfl⟩
  have hrepl_nv : repl.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hrepl_mem
  have hother_mem : other.toNat ∈ k5ClauseLits ks cid := by
    rw [hother_eq, k5_mem_clauseLits_iff (by omega)]; exact ⟨slot ^^^ 1, by omega, rfl⟩
  have hother_nv : other.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hother_mem
  have har'_eq : ar' = (ks.arena.set (off + slot) (ks.arena[off + ri]'hrepl_lt_ar)).set
      (off + ri) (ks.arena[off + slot]'(by dsimp only [off]; omega)) := by
    dsimp only [ar']; rw [har_slot, hrepl_eq]
    change (ks.arena.set (off + slot) (ks.arena[off + ri]?.getD 0#32)).set (off + ri) _ = _
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
  have hsh1 : ks1.ShapesOk acap :=
    { hsh with
      whead_len := by dsimp only [ks1, wh1]; split <;> simp [hsh.whead_len]
      wnext_len := by dsimp only [ks1, wn1]; split <;> simp [hsh.wnext_len]
      arena_len := by simp [ks1, ar', hsh.arena_len] }
  have hsh' := k5WatchStep0_preserves_shapes hsh1 w repl other
  have hlits_perm_all : ∀ c < ks.nc.toNat, (k5ClauseLits ks' c).Perm (k5ClauseLits ks c) := by
    intro c hc
    by_cases hcc : c = cid
    · subst hcc; change (((ar'.drop off).take (k5ClauseSize ks cid)).map BitVec.toNat).Perm
        (((ks.arena.drop off).take (k5ClauseSize ks cid)).map BitVec.toNat)
      rw [har'_eq]
      exact (k5_drop_take_set_swap ks.arena (off := off) (sz := k5ClauseSize ks cid)
        (p := slot) (q := ri) (by omega) hri_lt (by dsimp only [off]; omega)).map _
    · have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
          idx < k5ClauseOff ks c ∨ k5ClauseOff ks c + k5ClauseSize ks c ≤ idx := by
        intro idx hidx; by_cases hlt : c < cid
        · right; have hm := hinv.clauses.cl_mono c cid hlt hcid_lt
          change k5ClauseOff ks c + k5ClauseSize ks c ≤ off at hm
          rcases hidx with rfl | rfl <;> omega
        · left; have hm := hinv.clauses.cl_mono cid c (by omega) hc
          change off + k5ClauseSize ks cid ≤ k5ClauseOff ks c at hm
          dsimp only [cid] at hm; rcases hidx with rfl | rfl <;> omega
      change (((ar'.drop (k5ClauseOff ks c)).take (k5ClauseSize ks c)).map BitVec.toNat).Perm _
      dsimp only [ar']
      rw [k5_drop_take_set_out _ _ (hout _ (Or.inr rfl)),
        k5_drop_take_set_out _ _ (hout _ (Or.inl rfl))]
      exact List.Perm.refl _
  have hcl' : K512ClausesOk acap P ks' :=
    { hinv.clauses with
      cl_wf := fun c hc => by
        have hw := hinv.clauses.cl_wf c hc; have hp := hlits_perm_all c hc
        exact ⟨hw.1, hw.2.1, fun x hx => hw.2.2.1 x (hp.mem_iff.mp hx),
          hw.2.2.2.perm hp.symm⟩ }
  have hrsn' : K512ReasonOk ks' := fun i hi => by
    rcases hinv.reasons i hi with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right; have hp := hlits_perm_all _ hr_lt
      exact ⟨hr_lt, hp.mem_iff.mpr hmem, fun x hx => hall x (hp.mem_iff.mp hx)⟩
  let chains1 := chains.set l (done ++ todo')
  have hch1_len : chains1.length = 2 * ks1.nv.toNat := by rw [List.length_set]; exact wc.len_eq
  have hch_l_eq : chains[l]'hch_l = done ++ w0 :: todo' := by
    have := wc.chain_l; rwa [List.getElem?_eq_getElem hch_l, Option.getD_some] at this
  have hperm1 := k5_list_flatten_set_sub_perm chains hch_l done todo' w0 hch_l_eq
  have hnd_cons := hperm1.nodup_iff.mp wc.nodup
  have hw0_not_in : w0 ∉ chains1.flatten := (List.nodup_cons.mp hnd_cons).1
  have hch1_nd : chains1.flatten.Nodup := (List.nodup_cons.mp hnd_cons).2
  have hch1_sub : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains1[x]?.getD [], u ∈ chains[x]?.getD [] := by
    intro x hx u hu
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    rw [List.getElem?_eq_getElem hx1, Option.getD_some] at hu
    rw [List.getElem?_eq_getElem hx0, Option.getD_some]
    by_cases hxl : x = l
    · subst hxl; simp only [chains1, List.getElem_set_self] at hu; rw [hch_l_eq]
      exact (List.mem_append.mp hu).elim (List.mem_append_left _)
        (fun ht => List.mem_append_right _ (List.mem_cons_of_mem _ ht))
    · simpa only [chains1, List.getElem_set_ne (Ne.symm hxl)] using hu
  have hdone_elim : prev = 0xFFFFFFFF#32 → done = [] := fun hprev => by
    rcases wc.prev_rel with ⟨hd, _, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
    · exact hd
    · exfalso; have h2 : u < 4096 := by rw [hsh.wnext_len] at hu_len; exact hu_len
      have h3 := congrArg BitVec.toNat (hp_eq.symm.trans hprev)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h3; omega
  have htail_ks : K5WChain ks.wnext nxt todo' := by
    rcases K5WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
    · cases hn
    · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
      have hw0_eq : w0 = w0' := by
        have ht := congrArg BitVec.toNat hw_eq'
        have h1 : w0 < 2 ^ 32 := by unfold k5MaxCl at hnc; omega
        have h2 : w0' < 2 ^ 32 := by rw [hsh.wnext_len] at hw0'; omega
        simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
      subst hw0_eq
      have hg : nxt = ks.wnext[w0]'hw0' := by
        dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
      rwa [hg]
  have hwc1 : ∀ x < 2 * ks1.nv.toNat,
      K5WChain ks1.wnext (ks1.whead[x]?.getD 0xFFFFFFFF#32) (chains1[x]?.getD []) := by
    intro x hx
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    by_cases hprev : prev = 0xFFFFFFFF#32
    · have hdone_nil := hdone_elim hprev
      have hwh1 : wh1 = ks.whead.set l nxt := by simp [wh1, hprev]
      have hwn1 : wn1 = ks.wnext := by simp [wn1, hprev]
      by_cases hxl : l = x
      · subst hxl; rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        simp only [chains1, List.getElem_set_self, hdone_nil, List.nil_append, ks1, hwh1, hwn1]
        rw [List.getElem?_set_self hwh_len, Option.getD_some]; exact htail_ks
      · have hwc0 := wc.chains_wc x hx
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
        simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1] at hwc0 ⊢
        rwa [List.getElem?_set_ne hxl]
    · rcases wc.prev_rel with ⟨_, hp_fff, _⟩ | ⟨pfx, u, hdone_eq, hp_eq, hu_len, _⟩
      · exact absurd hp_fff hprev
      · have hu_tn : prev.toNat = u := by
          rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hsh.wnext_len] at hu_len; omega)]
        have hwh1 : wh1 = ks.whead := by simp [wh1, hprev]
        have hwn1 : wn1 = ks.wnext.set u nxt := by simp [wn1, hprev, hu_tn]
        have hnd_get := k5_list_flatten_nodup_getElem wc.nodup hch_l
        by_cases hxl : l = x
        · subst hxl; rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          simp only [chains1, List.getElem_set_self, hdone_eq, List.append_assoc, ks1, hwh1, hwn1]
          have hwc0 := wc.chains_wc l hx
          rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_l_eq, hdone_eq,
            List.append_assoc] at hwc0
          have hnd_l := hnd_get.1; rw [hch_l_eq, hdone_eq, List.append_assoc] at hnd_l
          simpa [List.append_assoc] using k5_wchain_bypass hwc0 hnd_l hu_len hwn_len hnxt_eq.symm
        · have hu_not_x : u ∉ chains[x]'hx0 :=
            hnd_get.2 x (Ne.symm hxl) hx0 u (by rw [hch_l_eq, hdone_eq]; simp)
          have hwc0 := wc.chains_wc x hx
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
          simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1]
          exact hwc0.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_not_x (h ▸ hy))).symm
  have hbnd1 : ∀ x < 2 * ks1.nv.toNat, ∀ u ∈ chains1[x]?.getD [],
      u < 2 * ks1.nc.toNat ∧ 2 ≤ k5ClauseSize ks1 (u / 2) ∧
      (ks1.arena[k5ClauseOff ks1 (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks1.wblit[u]?.getD 0#32).toNat < 2 * ks1.nv.toNat := by
    intro x hx u hu
    have hbu := wc.chains_bnd x hx u (hch1_sub x hx u hu)
    have hu_ne : u ≠ w0 := fun h => hw0_not_in (by
      rw [← h, List.mem_flatten]; have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
      exact ⟨chains1[x], List.getElem_mem hx1, by simpa [List.getElem?_eq_getElem hx1] using hu⟩)
    have har_u : ks1.arena[k5ClauseOff ks (u / 2) + u % 2]? =
        ks.arena[k5ClauseOff ks (u / 2) + u % 2]? := by
      dsimp only [ks1, ar']
      by_cases huc : u / 2 = cid
      · have hm1 : u % 2 ≠ slot := fun hm => hu_ne (by omega)
        have hm2 : u % 2 ≠ ri := by have := Nat.mod_lt u (by decide : 0 < 2); omega
        rw [huc, List.getElem?_set_ne (by dsimp only [off]; omega),
          List.getElem?_set_ne (by dsimp only [off]; omega)]
      · have hu_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
        have hu_m : u % 2 < 2 := Nat.mod_lt u (by decide)
        have hdisj : ∀ idx, idx = off + slot ∨ idx = off + ri →
            idx ≠ k5ClauseOff ks (u / 2) + u % 2 := fun idx hidx => by
          by_cases hlu : u / 2 < cid
          · have hm := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have := hbu.2.1; change k5ClauseOff ks (u / 2) + k5ClauseSize ks (u / 2) ≤ off at hm
            rcases hidx with rfl | rfl <;> omega
          · have hm := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change off + k5ClauseSize ks cid ≤ k5ClauseOff ks (u / 2) at hm
            dsimp only [cid] at hm; rcases hidx with rfl | rfl <;> omega
        rw [List.getElem?_set_ne (hdisj _ (Or.inr rfl)),
          List.getElem?_set_ne (hdisj _ (Or.inl rfl))]
    refine ⟨hbu.1, hbu.2.1, ?_, hbu.2.2.2⟩
    change (ks1.arena[k5ClauseOff ks (u / 2) + u % 2]?.getD 0#32).toNat = x
    rw [har_u]; exact hbu.2.2.1
  have hw_tn : w.toNat = w0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold k5MaxCl at hnc; omega)]
  have hw_step0 := k5WatchStep0_preserves_watches_with hsh1 hch1_len hch1_nd hwc1 hbnd1
    (w := w) (l := repl) (vo := other)
    (by change w.toNat < 2 * ks.nc.toNat; rw [hw_tn]; exact hb0.1)
    hnc hnv hrepl_nv hother_nv
    (by change 2 ≤ k5ClauseSize ks (w.toNat / 2); rw [hw_tn]; exact hsz_ge)
    (by change (ar'[k5ClauseOff ks (w.toNat / 2) + w.toNat % 2]?.getD 0#32).toNat = repl.toNat
        rw [hw_tn]; change (ar'[off + slot]?.getD 0#32).toNat = repl.toNat
        simp [ar', List.getElem?_set_ne (by omega : off + ri ≠ off + slot),
          List.getElem?_set_self (by dsimp only [off]; omega : off + slot < ks.arena.length)])
    (by rw [hw_tn]; exact hw0_not_in)
  have hrepl_ch1 : repl.toNat < chains1.length := by rw [hch1_len]; exact hrepl_nv
  let chains' := chains1.set repl.toNat (w.toNat :: chains1[repl.toNat]'hrepl_ch1)
  have hwc_cur' : K5WChainCursor ks' l chains' done todo' prev nxt := by
    have hch'_l : l < chains'.length := by
      simp only [chains', List.length_set]; rw [hch1_len]; exact hl
    have hcl'_eq : chains'[l]?.getD [] = done ++ todo' := by
      rw [List.getElem?_eq_getElem hch'_l, Option.getD_some]
      simp only [chains', List.getElem_set_ne hrepl_ne, chains1, List.getElem_set_self]
    have hnd_l := (k5_list_flatten_nodup_getElem wc.nodup hch_l).1
    have hw0_nt : w0 ∉ todo' := by
      rw [hch_l_eq] at hnd_l; exact (List.nodup_cons.mp (List.nodup_append.mp hnd_l).2.1).1
    have htail1 : K5WChain ks1.wnext nxt todo' := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · simp [ks1, wn1, hprev, htail_ks]
      · rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by rw [hsh.wnext_len] at hu_len; omega)]
          have hu_nt : u ∉ todo' := by
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact fun h => hd u (List.mem_cons_of_mem _ h) rfl
          simp only [ks1, wn1, hprev, ↓reduceIte, hu_tn]
          exact htail_ks.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
    have htail' : K5WChain ks'.wnext nxt todo' := by
      change K5WChain (ks1.wnext.set w.toNat _) nxt todo'; rw [hw_tn]
      exact htail1.congr fun y hy => (List.getElem?_set_ne (fun h : w0 = y => hw0_nt (h ▸ hy))).symm
    have hprev' : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks'.whead[l]?.getD 0xFFFFFFFF#32 = nxt) ∨
        (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
          u < ks'.wnext.length ∧ ks'.wnext[u]?.getD 0xFFFFFFFF#32 = nxt) := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · left; refine ⟨hdone_elim hprev, hprev, ?_⟩
        change (ks1.whead.set repl.toNat w)[l]?.getD 0xFFFFFFFF#32 = nxt
        rw [List.getElem?_set_ne hrepl_ne]; change wh1[l]?.getD 0xFFFFFFFF#32 = nxt
        simp only [wh1, hprev, ↓reduceIte, List.getElem?_set_self hwh_len, Option.getD_some]
      · right
        rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by rw [hsh.wnext_len] at hu_len; omega)]
          have hune : w0 ≠ u := fun heq => by
            rw [hch_l_eq, hde] at hnd_l
            exact (List.nodup_append.mp hnd_l).2.2 u (by simp) w0 List.mem_cons_self heq.symm
          refine ⟨pfx, u, hde, hp_eq, by simpa [ks', k5WatchStep0, ks1, wn1, hprev] using hu_len,
            ?_⟩
          change (ks1.wnext.set w.toNat _)[u]?.getD 0xFFFFFFFF#32 = nxt
          rw [hw_tn, List.getElem?_set_ne hune]; change wn1[u]?.getD 0xFFFFFFFF#32 = nxt
          simp only [wn1, hprev, ↓reduceIte, hu_tn, List.getElem?_set_self hu_len, Option.getD_some]
    exact ⟨hw_step0.1, hw_step0.2.1, hcl'_eq, hw_step0.2.2.1, hw_step0.2.2.2.1, htail', hprev'⟩
  exact ⟨⟨hsh', hcl', hwc_cur'.watchesOk,
    k5BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hrsn'⟩, chains', hwc_cur'⟩

theorem k5FlipFinish_preserves {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hval1 : ks.vals[lit.toNat]? = some 1#32)
    (hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32) :
    K512Inv acap P ((ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32) := by
  let ks' := (ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  obtain ⟨hv_eq, _⟩ := k5_bv32_div2_lt hlit
  obtain ⟨hn_eq, _⟩ := k5_bv32_xor1_lt hlit
  have hl_ne : lit.toNat ≠ (lit ^^^ 1#32).toNat := by
    rw [hn_eq, ← k5_litNeg_eq_xor1]
    rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hlen_v : lit.toNat < ks.vals.length := by rw [hsh.vals_len]; unfold k5MaxV at hnv; omega
  have hlen_nl : (lit ^^^ 1#32).toNat < ks.vals.length := by
    rw [hsh.vals_len]; unfold k5MaxV at hnv; rw [hn_eq, ← k5_litNeg_eq_xor1]
    rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hval_lit : ks'.vals[lit.toNat]? = some 2#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[lit.toNat]? = some 2#32
    rw [List.getElem?_set_ne hl_ne.symm, List.getElem?_set_self hlen_v]
  have hval_nl : ks'.vals[(lit ^^^ 1#32).toNat]? = some 1#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[(lit ^^^ 1#32).toNat]? =
      some 1#32
    rw [List.getElem?_set_self (by simp; exact hlen_nl)]
  have hval_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hx => by
    have h1 : x ≠ lit.toNat := fun h => hx (h ▸ rfl)
    have h2 : x ≠ (lit ^^^ 1#32).toNat := fun h => by
      have : x / 2 = (lit.toNat ^^^ 1) / 2 := by rw [h, hn_eq, ← k5_litNeg_eq_xor1]
      rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[x]? = ks.vals[x]?
    rw [List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm]
  have hba' : K512BaseAssignOk P ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, ?_, ?_, ?_, h0.trl_nodup, h0.trl_lt,
      h0.trl_lvl_le, ?_, h0.trl_lvl_mono, h0.dec_earliest, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, ← k5_litNeg_eq_xor1]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit]; exact Or.inr (Or.inr rfl)
        · rw [hval_nl]; exact Or.inr (Or.inl rfl)
      · rw [hval_other l hv]; exact h0.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, ← k5_litNeg_eq_xor1]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit,
            show lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat by rw [hn_eq, ← k5_litNeg_eq_xor1],
            hval_nl]; simp
        · rw [hval_nl,
          show (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat by rw [hn_eq]; exact litNeg_litNeg _,
            hval_lit]; simp
      · have hnv' : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hval_other l hv, hval_other (l ^^^ 1) hnv']; exact h0.vals_neg_iff l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have hex := (h0.vals_nz_iff_trl lit.toNat hlit).mp (by simp [hval1])
        have hnz_new : ks'.vals[l]?.getD 0#32 ≠ 0#32 := by
          have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
            rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
              rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
                (rw [hn_eq, ← k5_litNeg_eq_xor1]; omega)
          rcases he with rfl | rfl
          · rw [hval_lit]; decide
          · rw [hval_nl]; decide
        exact ⟨fun _ => by
          dsimp only [ks', K512State.putArr]; simpa [hv] using hex, fun _ => hnz_new⟩
      · rw [hval_other l hv]; exact h0.vals_nz_iff_trl l hl
    · intro v hv hv0; by_cases hvq : v = lit.toNat / 2
      · exfalso; subst hvq; rcases k5_nat_xor1_cases lit.toNat with ⟨ha, _⟩ | ⟨_, hb⟩
        · rw [← ha, hval_lit] at hv0; cases hv0
        · rw [show 2 * (lit.toNat / 2) = (lit ^^^ 1#32).toNat by
            rw [hn_eq, ← k5_litNeg_eq_xor1]; omega, hval_nl] at hv0; cases hv0
      · rw [hval_other (2 * v) (by omega)] at hv0; exact h0.unass_lvl_zero v hv hv0
    · intro i hi; dsimp only [ks', K512State.putArr]; intro hlv
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq => by
        rw [heq, ← hv_eq] at hlv; exact hlvl_nz hlv
      have hne_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k5_nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      have h0l := h0.lvl0_ok i hi hlv
      change ks'.vals[(ks.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32 ∧ _
      rw [hval_other _ hne_v, hval_other _ hne_x]; exact h0l
  exact ⟨(hsh.putArr .vals _ _).putArr .vals _ _,
    k5ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by dsimp only [K512State.putArr]; exact hinv.watches,
    hba', by dsimp only [K512State.putArr]; exact hinv.reasons⟩

/-! ## 2. `8/24`: `full_k512_flip_wp` -/

theorem full_k512_flip_wp (Γ : Env) :
    ∀ args m Q X, k5FlipSpec args m Q X → Func.wp Γ full_k512_flip_body args m Q X := by
  rintro ⟨hPtr, lit, ⟨⟩⟩ m Q X ⟨c, s, P, R, rfl, hlen, hinv_s, hlit_lt, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let scr := s.scratch.scratch_buf
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_21792 : 21792 ≤ scr.length := by
    dsimp only [scr]; unfold k5MinScr at hscr_ge; omega
  let acap := scr.length - (k5Base + k5SlabFixed)
  let ks := k5StateOfScratch scr
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hmA0 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks ⋆
      (FullK512Frame c s ⋆ R)) m := by
    rw [fullMem_eq_k5Frame hscr_21792] at hm
    exact k5Mem_to_amem hsh (by rw [k5Ptr_base_eq]; exact sep_ac hm)
  clear hm
  obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK512Frame c s ⋆ R) := ⟨_, rfl⟩
  have hfinish : ∀ (ok : Bool) (ks' : K512State) (m' : Mem 64),
      K512Inv acap P ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump → ks'.assump = ks.assump →
      (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks' ⋆ Rfr) m' → Q (ok, ()) m' := by
    intro ok ks' m' hinv' hnv' hna' hass' hm'
    rw [hRfr] at hm'
    obtain ⟨_, hm0⟩ := k5MemA_to_mem hm'
    have h2304 : 2304 ≤ s.scratch.scratch_buf.length := by
      change 2304 ≤ scr.length; omega
    have hmJ := fullMem_join_k5 (c := c) (s := s) (acap := acap) (ks' := ks') (R := R)
      h2304 hinv'.shapes (by rw [k5Ptr_base_eq] at hm0; exact sep_ac hm0)
    let scr' := s.scratch.scratch_buf.take 2304 ++ ks'.toSlab
    have htk_len : (s.scratch.scratch_buf.take 2304).length = 2304 := List.length_take_of_le h2304
    have hscr'_len : scr'.length = c.scratch_cap := by
      dsimp only [scr']
      rw [List.length_append, htk_len, K512State.toSlab_length hinv'.shapes]
      dsimp only [acap]; unfold k5Base k5SlabFixed; omega
    have hpre : ∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
      rw [List.getElem?_append_left (by rw [htk_len]; unfold k5Base at hi; omega),
        List.getElem?_take_of_lt (by unfold k5Base at hi; omega)]
    have hof : k5StateOfScratch scr' = ks' := by
      unfold k5StateOfScratch k5Base
      rw [k5_slab_drop_exact _ ks'.toSlab htk_len]
      exact K512State.ofSlab_toSlab hinv'.shapes
    refine hQ ok scr' m' (k5_fullState_lengthsOk_scratch hlen hscr'_len) hpre
      ⟨by rw [hscr'_len, ← hscr_len]; exact hscr_ge, by rw [hscr'_len]; exact c.hscr, ?_⟩
      (by rw [hof]; exact hnv') (by rw [hof]; exact hna')
      (by unfold k5AssumpLitsS k5AssumpLits; rw [hof, hna', hass']) hmJ
    rw [hof, show scr'.length - (k5Base + k5SlabFixed) = acap by
      dsimp only [acap]; rw [hscr'_len, ← hscr_len]]
    exact hinv'
  obtain ⟨hv_eq, hv_lt⟩ := k5_bv32_div2_lt hlit_lt
  have hlit_1024 : lit.toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hv_512 : (lit >>> (1 : Nat)).toNat < 512 := by unfold k5MaxV at hnv; omega
  c0_hsplit
  · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl (by rw [hRfr]; exact hmA0)
  · have hmA : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks ⋆ Rfr) m := by
      rw [hRfr]; exact hmA0
    clear hmA0
    c0_hsplit
    · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl hmA
    · c0_hsplit
      · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl hmA
      · have hval1 : ks.vals[lit.toNat]? = some 1#32 := by
          have hc : ks.vals[lit.toNat]?.getD 0#32 = 1#32 := ‹_›
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_1024),
            Option.getD_some] at hc
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_1024), hc]
        have hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := ‹_›
        obtain ⟨ch0, hwc0⟩ := K5WChainCursor.init hsh hnv hinv.watches hlit_lt
        c0_hsteps_nogrp
        refine wp_while_state
          (α := BitVec 32 × BitVec 32 × List Nat × List Nat × K512State × List (List Nat))
          (fun st => (st.2.1, st.1, ())) (fun st => st.2.2.2.1.length)
          (fun st m' =>
            K5WChainCursor st.2.2.2.2.1 lit.toNat st.2.2.2.2.2 st.2.2.1 st.2.2.2.1 st.1 st.2.1 ∧
            K512Inv acap P st.2.2.2.2.1 ∧
            st.2.2.2.2.1.nv = ks.nv ∧ st.2.2.2.2.1.nassump = ks.nassump ∧
            st.2.2.2.2.1.assump = ks.assump ∧ st.2.2.2.2.1.vals = ks.vals ∧
            st.2.2.2.2.1.lvlArr = ks.lvlArr ∧
            (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap st.2.2.2.2.1 ⋆ Rfr) m') ?_ ?_
        · intro J hJ
          exact wp_jump_state
            (proj :=
              fun st : BitVec 32 × BitVec 32 × List Nat × List Nat × K512State × List (List Nat)
              => (st.2.1, st.1, ()))
            (0xFFFFFFFF#32, ks.whead[lit.toNat]?.getD 0#32, [], ch0[lit.toNat]?.getD [], ks, ch0)
            rfl (hJ _ m ⟨hwc0, hinv, rfl, rfl, rfl, rfl, rfl, hmA⟩)
        · rintro J ⟨prev, w, done, todo, ksW, chW⟩ m'
            ⟨hwc, hinvW, w_nv, w_na, w_as, w_va, w_la, hmW⟩ ih
          dsimp only at hwc hinvW w_nv w_na w_as w_va w_la hmW ⊢
          have hshW := hinvW.shapes; have hclW := hinvW.clauses
          have hnvW := hclW.nv_le; have hncW := hclW.nc_le
          have hlit_ltW : lit.toNat < 2 * ksW.nv.toNat := w_nv ▸ hlit_lt
          c0_hsplit
          · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
            obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_4096, hw_tn, hw_div2, hw_mod2,
                hsz_ge, har_slot, _, _⟩ := hwc.step_unfold hncW hlit_ltW hw_ne
            have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
            have hcid_2048 : w0 / 2 < 2048 := by unfold k5MaxCl at hncW; omega
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
            have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have har_ok : ∀ idx < k5ClauseSize ksW (w0 / 2),
                k5ClauseOff ksW (w0 / 2) + idx < acap ∧
                k5ClauseOff ksW (w0 / 2) + idx < 2 ^ 28 ∧
                (ksW.arena[k5ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat < 2 * ksW.nv.toNat :=
                  by
              intro idx hidx
              have hcap : k5ClauseOff ksW (w0 / 2) + idx < acap := by have := hclW.alen_le; omega
              have hwrp : k5ClauseOff ksW (w0 / 2) + idx < 2 ^ 28 := by
                have := hclW.acap_lt; unfold dimacsBound at this; omega
              have hmem : (ksW.arena[k5ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat ∈
                  k5ClauseLits ksW (w0 / 2) := by
                rw [k5_mem_clauseLits_iff (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                exact ⟨idx, hidx, rfl⟩
              exact ⟨hcap, hwrp, hwf_c.2.2.1 _ hmem⟩
            let other := ksW.arena[k5ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_nv : other.toNat < 2 * ksW.nv.toNat := (har_ok _ (by omega)).2.2
            have hother_1024 : other.toNat < 1024 := by unfold k5MaxV at hnvW; omega
            have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
            have hslot_other_eq : (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat = w0 % 2 ^^^ 1 := by
              rw [BitVec.toNat_xor, hw_mod2]; rfl
            have hcl_off_wrap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < 2 ^ 28 := by
              rw [hw_sh1, hslot_other_eq]; exact (har_ok _ (by omega)).2.1
            have hcl_off_cap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < acap := by
              rw [hw_sh1, hslot_other_eq]; exact (har_ok _ (by omega)).1
            have hother_bv_1024 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat]?.getD 0#32).toNat < 1024 := by
              rw [hw_sh1, hslot_other_eq]; exact hother_1024
            have hw_sh_2048 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < 2048 := by
              rw [hw_sh1]; exact hcid_2048
            iterate 23 c0_hstep
            refine head_wp_load rfl
              (K512MemATactics.load_k5_arena_off hcl_off_wrap hcl_off_cap hmW) ?_
            c0_hsplit
            · -- vals[other] == 1 => keep watch
              obtain ⟨hkp_inv, hkp_wc⟩ := k5WatchKeep_preserves hinvW hlit_ltW hwc hother_nv
              c0_hsteps!
              rw [hw_tn]
              refine ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo',
                  ksW.putArr .wblit w0 other, chW) _ (by simp)
                ⟨hkp_wc, hkp_inv, by k5_field; exact w_nv, by k5_field; exact w_na,
                  by k5_field; exact w_as, by k5_field; exact w_va, by k5_field; exact w_la, ?_⟩
              refine Eq.mp (congrArg (fun x =>
                (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap x ⋆ _) _) ?_) hm
              k5_ext <;> (first | rfl | simp only [other, k5ClauseOff, hw_tn, hw_sh1,
                show (BitVec.ofNat 32 w0 &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 from hslot_other_eq])
            · -- search for replacement literal r = 2..sz-1
              c0_hsteps_nogrp
              let sz := ksW.clSz[w0 / 2]?.getD 0#32
              let off := ksW.clOff[w0 / 2]?.getD 0#32
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                (fun b mb => mb = m' ∧
                  (b.2.1 = 0xFFFFFFFF#32 ∨
                    (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      b.2.2 ≠ lit ∧ ksW.vals[b.2.2.toNat]? = some 1#32)))
                (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                (fun st m'' => m'' = m' ∧ st.toNat ≤ sz.toNat ∧ 2 ≤ st.toNat) ?_ ?_ ?_
              · rintro B ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · c0_hsteps!; exact hfinish false ksW mb hinvW w_nv w_na w_as hmW
                · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                  obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne, _⟩ := hbrk.resolve_left hri_ne
                  have hrepl_ne' : repl.toNat ≠ lit.toNat :=
                    fun h => hrepl_ne (BitVec.eq_of_toNat_eq h)
                  obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                    k5WatchReloc_preserves hinvW hlit_ltW hwc hri_ge hri_lt hrepl_ne' rfl hrepl_eq
                  obtain ⟨hri_cap, hri_wrap, hri_lit⟩ := har_ok ri.toNat hri_lt
                  obtain ⟨hslot_cap, hslot_wrap, _⟩ :=
                    har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                  have hslot_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32).toNat < 2 ^ 28 := by
                        rw [hw_sh1, hw_mod2]; exact hslot_wrap
                  have hslot_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32).toNat < acap := by
                        rw [hw_sh1, hw_mod2]; exact hslot_cap
                  have hri_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      ri.toNat < 2 ^ 28 := by rw [hw_sh1]; exact hri_wrap
                  have hri_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      ri.toNat < acap := by rw [hw_sh1]; exact hri_cap
                  have hrepl_1024 : repl.toNat < 1024 := by
                    change repl = ksW.arena[k5ClauseOff ksW (w0 / 2) +
                      ri.toNat]?.getD 0#32 at hrepl_eq
                    rw [hrepl_eq]; unfold k5MaxV at hnvW; omega
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < 4096 := fun hp => by
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hshW.wnext_len] at hu_len
                      rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hu_len
                  iterate 5 c0_hstep
                  refine wp_store_sep
                    (K512MemATactics.store_k5_arena_off repl hslot_bv_wrap hslot_bv_cap hmW)
                    fun m_s1 hm_s1 => ?_
                  iterate 5 c0_hstep
                  refine wp_store_sep
                    (K512MemATactics.store_k5_arena_off lit hri_bv_wrap hri_bv_cap hm_s1)
                    fun m_s2 hm_s2 => ?_
                  clear hm_s1
                  c0_hsteps_nogrp
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                    c0_hsteps!; rw [hw_tn]
                    refine ih (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chW') _ (by simp)
                      ⟨hwc', hrl_inv, w_nv, w_na, w_as, w_va, w_la, ?_⟩
                    refine Eq.mp (congrArg (fun x =>
                      (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap x ⋆ _) _) ?_) hm
                    dsimp only [k5WatchStep0, k5ClauseOff]; simp only [hpeq, ↓reduceIte]
                    k5_ext <;> (first | rfl | (simp [hw_tn, hw_sh1, hw_mod2,
                      hslot_other_eq, BitVec.ofNat_toNat]; try rfl))
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                    have hprv_4096 := hprv_lt hpne
                    c0_hsteps!; rw [hw_tn]
                    refine ih (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chW') _ (by simp)
                      ⟨hwc', hrl_inv, w_nv, w_na, w_as, w_va, w_la, ?_⟩
                    refine Eq.mp (congrArg (fun x =>
                      (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap x ⋆ _) _) ?_) hm
                    dsimp only [k5WatchStep0, k5ClauseOff]; simp only [hpne, ↓reduceIte]
                    k5_ext <;> (first | rfl | (simp [hw_tn, hw_sh1, hw_mod2,
                      hslot_other_eq, BitVec.ofNat_toNat]; try rfl))
              · intro B L1 r m1 hB ih1 ⟨rfl, hr_le, hr2⟩
                dsimp only at hr_le hr2 ⊢
                have hw_md : w0 % 2 ^ 32 / 2 = w0 / 2 := by rw [Nat.mod_eq_of_lt (by omega)]
                c0_hsplit
                · have hr_lt : r.toNat < sz.toNat := by
                    have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := by bv_omega
                    rwa [hw_md] at hc0
                  obtain ⟨hr_cap, hr_wrap, hr_lit⟩ := har_ok r.toNat hr_lt
                  have hr_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      r.toNat < 2 ^ 28 := by rw [hw_sh1]; exact hr_wrap
                  have hr_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      r.toNat < acap := by rw [hw_sh1]; exact hr_cap
                  have hcand_1024 :
                      (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                      0#32).toNat + r.toNat]?.getD 0#32).toNat < 1024 := by
                    rw [hw_sh1]
                    change (ksW.arena[k5ClauseOff ksW (w0 / 2) + r.toNat]?.getD 0#32).toNat < 1024
                    unfold k5MaxV at hnvW; omega
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                    have hsz_bd : sz.toNat < 2 ^ 28 := by
                      have := hclW.alen_le; have := hclW.acap_lt; unfold dimacsBound at this
                      change k5ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                    bv_omega
                  iterate 5 c0_hstep
                  refine head_wp_load rfl
                    (K512MemATactics.load_k5_arena_off hr_bv_wrap hr_bv_cap hmW) ?_
                  refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hne_cand : ksW.arena[off.toNat + r.toNat]?.getD 0#32 ≠ lit := by
                      have hc0 : ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                          r.toNat]?.getD 0#32 ≠ lit := by bv_omega
                      rwa [hw_md] at hc0
                    c0_hsplit
                    · have hc_val1 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? =
                          some 1#32 := by
                        have hvl :
                            (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < ksW.vals.length :=
                              by
                          rw [hshW.vals_len]
                          change (ksW.arena[k5ClauseOff ksW (w0 / 2) +
                            r.toNat]?.getD 0#32).toNat < 1024
                          unfold k5MaxV at hnvW; omega
                        have hc0 :
                            ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                            r.toNat]?.getD 0#32).toNat]?.getD 0#32 = 1#32 := by bv_omega
                        rw [hw_md] at hc0
                        rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                        rw [List.getElem?_eq_getElem hvl, hc0]
                      c0_hsteps!
                      rw [hw_sh1]
                      exact hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) _
                        ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hne_cand, hc_val1⟩⟩
                    · c0_hsteps!
                      exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                        ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                  · c0_hsteps!
                    exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                      ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                · c0_hsteps!; exact hB (r, 0xFFFFFFFF#32, 0#32) _ ⟨rfl, Or.inl rfl⟩
              · intro B L1 _ hL1; c0_hsteps!; exact hL1 2#32 m' ⟨rfl, hsz_ge, le_refl _⟩
          · -- w == 0xFFFFFFFF => flip vals[lit] := 2, vals[lit^1] := 1
            obtain ⟨_, hn_lt⟩ := k5_bv32_xor1_lt hlit_lt
            have hnl_1024 : (lit ^^^ 1#32).toNat < 1024 := by unfold k5MaxV at hnv; omega
            have hfin :=
              k5FlipFinish_preserves hinvW hlit_ltW (w_va.symm ▸ hval1) (w_la.symm ▸ hlvl_nz)
            c0_hsteps!
            exact hfinish true _ _ hfin (by k5_field; exact w_nv) (by k5_field; exact w_na)
              (by k5_field; exact w_as) hm

/-! ## 3. `9/24`: `full_k512_propagate_wp` -/

private structure K5PropFrame (ks0 ks : K512State) : Prop where
  pres : K5PropPreserved ks0 ks
  te_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  old_trl : ∀ i < ks0.trl_end.toNat,
    ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? = ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? ∧
    ks.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]? = ks0.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]?
  new_trl : ∀ i, ks0.trl_end.toNat ≤ i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks0.lvl ∧
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32

private theorem K5PropFrame.refl (ks : K512State) : K5PropFrame ks ks :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩,
   fun _ h1 h2 => by omega⟩

private theorem K5PropFrame.cast {ks0 ks ks' : K512State} (h : K5PropFrame ks0 ks)
    (h1 : ks'.nv = ks.nv) (h2 : ks'.nc = ks.nc) (h3 : ks'.lvl = ks.lvl)
    (h4 : ks'.incons = ks.incons) (h5 : ks'.alen = ks.alen) (h6 : ks'.acap = ks.acap)
    (h7 : ks'.nassump = ks.nassump) (h8 : ks'.assump = ks.assump)
    (h9 : ks'.trl_end = ks.trl_end) (h10 : ks'.trl = ks.trl)
    (h11 : ks'.lvlArr = ks.lvlArr) (h12 : ks'.rsn = ks.rsn) : K5PropFrame ks0 ks' :=
  ⟨⟨h1.trans h.pres.nv, h2.trans h.pres.nc, h3.trans h.pres.lvl, h4.trans h.pres.incons,
    h5.trans h.pres.alen, h6.trans h.pres.acap, h7.trans h.pres.nassump, h8.trans h.pres.assump⟩,
   h9 ▸ h.te_ge,
   fun i hi => by rw [h10, h11, h12]; exact h.old_trl i hi,
   fun i hlo hhi => by rw [h9] at hhi; rw [h10, h11, h12]; exact h.new_trl i hlo hhi⟩

private theorem K5PropFrame.trans {ks0 ks1 ks2 : K512State}
    (h12 : K5PropFrame ks0 ks1) (h23 : K5PropFrame ks1 ks2) : K5PropFrame ks0 ks2 :=
  ⟨⟨h23.pres.nv.trans h12.pres.nv, h23.pres.nc.trans h12.pres.nc, h23.pres.lvl.trans h12.pres.lvl,
    h23.pres.incons.trans h12.pres.incons, h23.pres.alen.trans h12.pres.alen,
    h23.pres.acap.trans h12.pres.acap, h23.pres.nassump.trans h12.pres.nassump,
    h23.pres.assump.trans h12.pres.assump⟩,
   Nat.le_trans h12.te_ge h23.te_ge,
   fun i hi => by
     have h1 := h12.old_trl i hi
     have h2 := h23.old_trl i (Nat.lt_of_lt_of_le hi h12.te_ge)
     rw [h1.1] at h2
     exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩,
   fun i hlo hhi => by
     by_cases h1 : i < ks1.trl_end.toNat
     · have hn := h12.new_trl i hlo h1
       have ho := h23.old_trl i h1
       rw [ho.1, ho.2.1, ho.2.2]; exact hn
     · have hn := h23.new_trl i (by omega) hhi; rw [h12.pres.lvl] at hn; exact hn⟩

private theorem k5PropAssign_frame {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32) (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) :
    K5PropFrame ks (k5AssignStep ks lit rsn) := by
  have hnv := hinv.clauses.nv_le
  have hte_lt := k5_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hv_eq := (k5_bv32_div2_lt hlit).1
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by unfold k5MaxV at hnv; bv_omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    by change ks.trl_end.toNat ≤ (ks.trl_end + 1#32).toNat; omega,
    fun i hi => by
      have hne := hnot_trl i hi
      exact ⟨List.getElem?_set_ne (by omega),
        by dsimp only [k5AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne),
        by dsimp only [k5AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)⟩,
    fun i hlo hhi => by
      change i < (ks.trl_end + 1#32).toNat at hhi; rw [hte1] at hhi
      have hie : i = ks.trl_end.toNat := by omega
      subst hie; dsimp only [k5AssignStep]
      rw [List.getElem?_set_self (by rw [hinv.shapes.trl_len]; unfold k5MaxV at hnv; omega),
        Option.getD_some, hv_eq,
        List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; unfold k5MaxV at hnv; omega),
        List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; unfold k5MaxV at hnv; omega),
        Option.getD_some, Option.getD_some]
      exact ⟨rfl, hrsn_ne⟩⟩

private theorem k5_unlinked_clause_falsified {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks : K512State} (hinv : K512Inv acap P ks) {cid slot : Nat} (hcid : cid < ks.nc.toNat)
    (hslot : slot < 2) {nl other : BitVec 32}
    (hnl_f : ks.vals[nl.toNat]? = some 2#32)
    (hslot_eq : (ks.arena[k5ClauseOff ks cid + slot]?.getD 0#32).toNat = nl.toNat)
    (hoth_eq : other = ks.arena[k5ClauseOff ks cid + (slot ^^^ 1)]?.getD 0#32)
    (hrest : ∀ q, 2 ≤ q → q < k5ClauseSize ks cid →
      ks.vals[(ks.arena[k5ClauseOff ks cid + q]?.getD 0#32).toNat]? = some 2#32) :
    ∀ x ∈ k5ClauseLits ks cid, x ≠ other.toNat → ks.vals[x]? = some 2#32 := by
  intro x hx hne
  have hbd : k5ClauseOff ks cid + k5ClauseSize ks cid ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := (hinv.clauses.cl_wf cid hcid).2.1
    have := hinv.clauses.alen_le; omega
  obtain ⟨q, hq, rfl⟩ := (k5_mem_clauseLits_iff hbd).mp hx
  by_cases hq2 : q < 2
  · by_cases hqs : q = slot
    · subst hqs; rw [hslot_eq]; exact hnl_f
    · have hqo : q = slot ^^^ 1 := by
        rcases (show slot = 0 ∨ slot = 1 by omega) with rfl | rfl
        · change q = 1; omega
        · change q = 0; omega
      subst hqo; exact absurd (by rw [hoth_eq]) hne
  · exact hrest q (by omega) hq

theorem full_k512_propagate_wp (Γ : Env)
    (hAssign : ∀ args m Q X, k5AssignSpec args m Q X →
      Γ "full_k512_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, k5PropagateSpec args m Q X → Func.wp Γ full_k512_propagate_body args m Q X := by
  rintro ⟨kPtr, ⟨⟩⟩ m Q X ⟨acap, P, ks0, R, hinv0, hsync0, hm0, hQ⟩
  have hmA0 := k5Mem_to_amem hinv0.shapes hm0; clear hm0
  have hret : ∀ (confl : BitVec 32) (ksF : K512State) (mF : Mem 64),
      K512Inv acap P ksF → K512TrailSynced ksF → K5PropFrame ks0 ksF →
      (confl = 0xFFFFFFFF#32 → ksF.prop = ksF.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl.toNat < ksF.nc.toNat ∧
        ∀ l ∈ k5ClauseLits ksF confl.toNat, ksF.vals[l]? = some 2#32) →
      (K512MemA kPtr acap ksF ⋆ R) mF → Q (confl, ()) mF := fun confl ksF mF hi hs hf h1 h2 hmF =>
    hQ confl ksF mF hi hs hf.pres hf.te_ge hf.old_trl hf.new_trl h1 h2 (k5MemA_to_mem hmF).2
  refine wp_while_state (α := K512State) (fun _ => ())
    (fun ksO => ks0.nv.toNat - ksO.prop.toNat)
    (fun ksO mO => K512Inv acap P ksO ∧ K512TrailSynced ksO ∧ K5PropFrame ks0 ksO ∧
      (K512MemA kPtr acap ksO ⋆ R) mO) ?_ ?_
  · intro J hJ
    exact wp_jump_state (proj := fun _ : K512State => ()) ks0 rfl
      (hJ ks0 m ⟨hinv0, hsync0, K5PropFrame.refl ks0, hmA0⟩)
  · rintro J ksO mO ⟨hinvO, hsyncO, hfrO, hmO⟩ ihO
    have hnvO := hinvO.clauses.nv_le
    c0_hsplit
    · -- ksO.prop < ksO.trl_end
      have hp_lt : ksO.prop.toNat < ksO.trl_end.toNat := by bv_omega
      have hp_512 : ksO.prop.toNat < 512 := by
        have := hinvO.assign.trl_end_le; unfold k5MaxV at hnvO; omega
      let pO := ksO.prop
      let lit := ksO.trl[pO.toNat]?.getD 0#32
      have hlit_lt : lit.toNat < 2 * ksO.nv.toNat :=
        hinvO.assign.trl_lt lit.toNat (k5_mem_trailLits_of_lt hp_lt
          (by rw [hinvO.shapes.trl_len]; have := hinvO.assign.trl_end_le
              unfold k5MaxV at hnvO; omega))
      obtain ⟨hnl_eq, hnl_lt⟩ := k5_bv32_xor1_lt hlit_lt
      have hnl_1024 : (lit ^^^ 1#32).toNat < 1024 := by unfold k5MaxV at hnvO; omega
      have hnl_val2O : ksO.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
        rw [hnl_eq, ← k5_litNeg_eq_xor1]; exact (hsyncO pO.toNat hp_lt).2
      have hp1_eq : (pO + 1#32).toNat = pO.toNat + 1 := by dsimp only [pO]; bv_omega
      obtain ⟨hinv1, hsync1⟩ := k5BumpPropTicks_preserves_inv hinvO hsyncO (tk' := ksO.ticks + 1#32)
        (by rw [hp1_eq]; exact hp_lt)
      let ks1 := (ksO.putHdr .prop (pO + 1#32)).putHdr .ticks (ksO.ticks + 1#32)
      have hfr1 : K5PropFrame ks0 ks1 :=
        hfrO.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨ch1, hwc1⟩ :=
        K5WChainCursor.init hinv1.shapes hinv1.clauses.nv_le hinv1.watches hnl_lt
      c0_hsteps_nogrp
      refine wp_while_state
        (α := BitVec 32 × BitVec 32 × List Nat × List Nat × K512State × List (List Nat))
        (fun st => (st.1, st.2.1, ())) (fun st => st.2.2.2.1.length)
        (fun st mW =>
          K5WChainCursor st.2.2.2.2.1 (lit ^^^ 1#32).toNat st.2.2.2.2.2 st.2.2.1 st.2.2.2.1
            st.1 st.2.1 ∧
          K512Inv acap P st.2.2.2.2.1 ∧ K512TrailSynced st.2.2.2.2.1 ∧
          K5PropFrame ks0 st.2.2.2.2.1 ∧ st.2.2.2.2.1.prop.toNat = pO.toNat + 1 ∧
          pO.toNat < st.2.2.2.2.1.trl_end.toNat ∧ st.2.2.2.2.1.trl[pO.toNat]? = some lit ∧
          (K512MemA kPtr acap st.2.2.2.2.1 ⋆ R) mW) ?_ ?_
      · intro Jw hJw
        have htr_lit : ks1.trl[pO.toNat]? = some lit := by
          change ksO.trl[pO.toNat]? = some (ksO.trl[pO.toNat]?.getD 0#32)
          rw [List.getElem?_eq_getElem (by rw [hinvO.shapes.trl_len]; exact hp_512),
            Option.getD_some]
        exact wp_jump_state
          (proj :=
            fun st : BitVec 32 × BitVec 32 × List Nat × List Nat × K512State × List (List Nat)
            => (st.1, st.2.1, ()))
          (0xFFFFFFFF#32, ks1.whead[(lit ^^^ 1#32).toNat]?.getD 0#32, [],
            ch1[(lit ^^^ 1#32).toNat]?.getD [], ks1, ch1)
          rfl (hJw _ _ ⟨hwc1, hinv1, hsync1, hfr1, by change (pO + 1#32).toNat = _; exact hp1_eq,
            hp_lt, htr_lit, hm⟩)
      · rintro Jw ⟨prev, w, done, todo, ksW, chW⟩ mW
          ⟨hwc, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hmW⟩ ihW
        dsimp only at hwc hinvW hsyncW hfrW hw_pr hw_te hw_lit hmW ⊢
        have hshW := hinvW.shapes; have hclW := hinvW.clauses
        have hnvW := hclW.nv_le; have hncW := hclW.nc_le
        have hw_nl_lt : (lit ^^^ 1#32).toNat < 2 * ksW.nv.toNat := by
          rw [hfrW.pres.nv, ← hfrO.pres.nv]; exact hnl_lt
        have hnl_val2W : ksW.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
          have hs := hsyncW pO.toNat hw_te
          rw [hw_lit, Option.getD_some] at hs; rw [hnl_eq, ← k5_litNeg_eq_xor1]; exact hs.2
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
          obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_4096, hw_tn, hw_div2, hw_mod2,
              hsz_ge, har_slot_l, hwb_lt, _⟩ := hwc.step_unfold hncW hw_nl_lt hw_ne
          have hwb_1024 : (ksW.wblit[w0]?.getD 0#32).toNat < 1024 := by unfold k5MaxV at hnvW; omega
          have hwb_1024' : (ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32).toNat < 1024 := by
            rw [hw_tn]; exact hwb_1024
          c0_hsplit
          · -- wblit satisfied => keep watch
            have hwc_next := k5WatchSkip_cursor hshW hncW hwc hw0_len
            c0_hsteps!; rw [hw_tn]
            exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo', ksW, chW)
              mW (by simp) ⟨hwc_next, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hmW⟩
          · -- inspect clause cid = w0 / 2
            have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
            have hcid_2048 : w0 / 2 < 2048 := by unfold k5MaxCl at hncW; omega
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
            have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have har_ok : ∀ idx < k5ClauseSize ksW (w0 / 2),
                k5ClauseOff ksW (w0 / 2) + idx < acap ∧ k5ClauseOff ksW (w0 / 2) + idx < 2 ^ 28 ∧
                (ksW.arena[k5ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat < 2 * ksW.nv.toNat :=
                  by
              intro idx hidx
              have hcap : k5ClauseOff ksW (w0 / 2) + idx < acap := by have := hclW.alen_le; omega
              have hwrp : k5ClauseOff ksW (w0 / 2) + idx < 2 ^ 28 := by
                have := hclW.acap_lt; unfold dimacsBound at this; omega
              have hmem : (ksW.arena[k5ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat ∈
                  k5ClauseLits ksW (w0 / 2) := by
                rw [k5_mem_clauseLits_iff (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                exact ⟨idx, hidx, rfl⟩
              exact ⟨hcap, hwrp, hwf_c.2.2.1 _ hmem⟩
            let other := ksW.arena[k5ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_nv : other.toNat < 2 * ksW.nv.toNat := (har_ok _ (by omega)).2.2
            have hother_1024 : other.toNat < 1024 := by unfold k5MaxV at hnvW; omega
            have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
            have hw_sh_2048 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < 2048 := by
              rw [hw_sh1]; exact hcid_2048
            have hslot_other_eq : (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat = w0 % 2 ^^^ 1 := by
              rw [BitVec.toNat_xor, hw_mod2]; rfl
            have hcl_off_wrap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < 2 ^ 28 := by
              rw [hw_sh1, hslot_other_eq]; exact (har_ok _ (by omega)).2.1
            have hcl_off_cap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < acap := by
              rw [hw_sh1, hslot_other_eq]; exact (har_ok _ (by omega)).1
            have hother_bv_1024 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat]?.getD 0#32).toNat < 1024 := by
              rw [hw_sh1, hslot_other_eq]; exact hother_1024
            have hother_bv_eq : ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                0#32).toNat + (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat]?.getD 0#32 = other := by
              dsimp only [other, k5ClauseOff]; rw [hw_sh1, hslot_other_eq]
            iterate 18 c0_hstep
            refine head_wp_load rfl
              (K512MemATactics.load_k5_arena_off hcl_off_wrap hcl_off_cap hmW) ?_
            c0_hsplit
            · -- vals[other] == 1 => update wblit and continue
              obtain ⟨hkp_inv, hkp_wc⟩ := k5WatchKeep_preserves hinvW hw_nl_lt hwc hother_nv
              c0_hsteps!; rw [hw_tn]
              refine ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo',
                  ksW.putArr .wblit w0 other, chW) _ (by simp)
                ⟨hkp_wc, hkp_inv, hsyncW,
                  hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
                  hw_pr, hw_te, hw_lit, ?_⟩
              refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm
              k5_ext <;> (first | rfl | simp only [other, k5ClauseOff, hw_tn, hw_sh1,
                show (BitVec.ofNat 32 w0 &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 from hslot_other_eq])
            · -- bump ticks and scan r = 2..sz-1
              let ksT := ksW.putHdr .ticks (ksW.ticks + 1#32)
              have hinvT : K512Inv acap P ksT :=
                ⟨hinvW.shapes.putHdr .ticks _,
                 k5ClausesOk_cast hinvW.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
                 by dsimp only [ksT, K512State.putHdr]; exact hinvW.watches,
                 k5BaseAssignOk_cast hinvW.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
                 by dsimp only [ksT, K512State.putHdr]; exact hinvW.reasons⟩
              have hfrT : K5PropFrame ks0 ksT :=
                hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              have hwcT : K5WChainCursor ksT (lit ^^^ 1#32).toNat chW done (w0 :: todo')
                  prev (BitVec.ofNat 32 w0) :=
                ⟨hwc.len_eq, hwc.nodup, hwc.chain_l, hwc.chains_wc, hwc.chains_bnd,
                 hwc.tail_wc, hwc.prev_rel⟩
              c0_hsteps_nogrp
              let sz := ksW.clSz[w0 / 2]?.getD 0#32
              let off := ksW.clOff[w0 / 2]?.getD 0#32
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                (fun b mb => (K512MemA kPtr acap ksT ⋆ R) mb ∧
                  ((b.2.1 = 0xFFFFFFFF#32 ∧ ∀ q, 2 ≤ q → q < sz.toNat →
                    ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32) ∨
                   (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                    b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                    ksW.vals[b.2.2.toNat]? ≠ some 2#32)))
                (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                (fun r m'' => (K512MemA kPtr acap ksT ⋆ R) m'' ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                  ∀ q, 2 ≤ q → q < r.toNat →
                    ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32) ?_ ?_ ?_
              · rintro B ⟨_, ri, repl⟩ mb ⟨hmb, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · -- ri != 0xFFFFFFFF => relocate watch
                  have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                  obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne2⟩ :=
                    hbrk.resolve_left (fun h => hri_ne h.1)
                  have hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat := fun h =>
                    hrepl_ne2 (by rw [h]; exact hnl_val2W)
                  obtain ⟨hrl_inv, ⟨chR, hwcR⟩⟩ :=
                    k5WatchReloc_preserves hinvT hw_nl_lt hwcT hri_ge hri_lt hrepl_ne rfl hrepl_eq
                  obtain ⟨hri_cap, hri_wrap, hri_lit⟩ := har_ok ri.toNat hri_lt
                  obtain ⟨hslot_cap, hslot_wrap, _⟩ :=
                    har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                  have hslot_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32).toNat < 2 ^ 28 := by
                        rw [hw_sh1, hw_mod2]; exact hslot_wrap
                  have hslot_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32).toNat < acap := by
                        rw [hw_sh1, hw_mod2]; exact hslot_cap
                  have hri_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      ri.toNat < 2 ^ 28 := by rw [hw_sh1]; exact hri_wrap
                  have hri_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      ri.toNat < acap := by rw [hw_sh1]; exact hri_cap
                  have hrepl_1024 : repl.toNat < 1024 := by
                    change repl = ksW.arena[k5ClauseOff ksW (w0 / 2) +
                      ri.toNat]?.getD 0#32 at hrepl_eq
                    rw [hrepl_eq]; unfold k5MaxV at hnvW; omega
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < 4096 := fun hp => by
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hshW.wnext_len] at hu_len
                      rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hu_len
                  iterate 5 c0_hstep
                  refine wp_store_sep
                    (K512MemATactics.store_k5_arena_off repl hslot_bv_wrap hslot_bv_cap hmb)
                    fun m_s1 hm_s1 => ?_
                  iterate 5 c0_hstep
                  refine wp_store_sep
                    (K512MemATactics.store_k5_arena_off (lit ^^^ 1#32) hri_bv_wrap hri_bv_cap hm_s1)
                    fun m_s2 hm_s2 => ?_
                  clear hm_s1
                  c0_hsteps_nogrp
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                    c0_hsteps!; rw [hw_tn]
                    exact ihW (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chR) _ (by simp)
                      ⟨hwcR, hrl_inv, hsyncW,
                        hfrT.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
                        hw_pr, hw_te, hw_lit, by
                        refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm
                        dsimp only [k5WatchStep0, k5ClauseOff, ksT]; simp only [hpeq, ↓reduceIte]
                        k5_ext <;> (first | rfl | (simp [hw_tn, hw_sh1, hw_mod2,
                          hslot_other_eq, BitVec.ofNat_toNat]; try rfl))⟩
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                    have hprv_4096 := hprv_lt hpne
                    c0_hsteps!; rw [hw_tn]
                    exact ihW (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chR) _ (by simp)
                      ⟨hwcR, hrl_inv, hsyncW,
                        hfrT.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
                        hw_pr, hw_te, hw_lit, by
                        refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm
                        dsimp only [k5WatchStep0, k5ClauseOff, ksT]; simp only [hpne, ↓reduceIte]
                        k5_ext <;> (first | rfl | (simp [hw_tn, hw_sh1, hw_mod2,
                          hslot_other_eq, BitVec.ofNat_toNat]; try rfl))⟩
                · -- ri == 0xFFFFFFFF => conflict or unit propagation
                  have hri_eq : ri = 0xFFFFFFFF#32 := by bv_omega
                  have h_all2 : ∀ q, 2 ≤ q → q < sz.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32 :=
                    (hbrk.resolve_right fun h => by
                      have hlt := h.2.1
                      have hsz_bd : sz.toNat < 2 ^ 28 := by
                        have := hclW.alen_le; have := hclW.acap_lt; unfold dimacsBound at this
                        change k5ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                      rw [hri_eq,
                        show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at hlt
                      omega).2
                  obtain ⟨hinvK, hwcK⟩ := k5WatchKeep_preserves hinvT hw_nl_lt hwcT hother_nv
                  let ksK := ksT.putArr .wblit w0 other
                  have hfrK : K5PropFrame ks0 ksK :=
                    hfrT.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hcl_fals := k5_unlinked_clause_falsified hinvK hcid_lt
                    (Nat.mod_lt w0 (by decide)) hnl_val2W har_slot_l rfl h_all2
                  have hother_bv_eq' : ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                      (w0 % 2 ^ 32 % 2 ^^^ 1)]?.getD 0#32 = other := by
                    dsimp only [other, k5ClauseOff]; rw [Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
                  c0_hsplit
                  · -- ov == 2 => conflict return cid
                    have hov2 : ksK.vals[other.toNat]? = some 2#32 := by
                      have hc0 : ksW.vals[other.toNat]?.getD 0#32 = 2#32 := by
                        rw [hother_bv_eq'] at ‹_›; exact ‹_›
                      rw [List.getElem?_eq_getElem (by rw [hshW.vals_len]; exact hother_1024),
                        Option.getD_some] at hc0
                      rw [List.getElem?_eq_getElem
                        (by rw [hinvK.shapes.vals_len]; exact hother_1024)]
                      exact congrArg some hc0
                    c0_hsteps!
                    have hmK : (K512MemA kPtr acap ksK ⋆ R) m := by
                      refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) m) ?_) hm
                      dsimp only [ksK]; k5_ext <;>
                        (first | rfl | simp only [other, k5ClauseOff, hw_tn, hw_sh1,
                          show (BitVec.ofNat 32 w0 &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 from
                            hslot_other_eq])
                    refine hret (BitVec.ofNat 32 w0 >>> (1 : Nat)) ksK _ hinvK hsyncW hfrK
                      (fun h => by
                        have := congrArg BitVec.toNat h; rw [hw_sh1] at this
                        change w0 / 2 = 4294967295 at this; omega)
                      (fun _ => ⟨by rw [hw_sh1]; exact hcid_lt, fun x hx => ?_⟩) hmK
                    rw [hw_sh1] at hx
                    by_cases hxo : x = other.toNat
                    · rw [hxo]; exact hov2
                    · exact hcl_fals x hx hxo
                  · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    c0_hsplit
                    · -- ov == 0 => full_k512_assign(k, other, cid)
                      have hov0 : ksK.vals[other.toNat]? = some 0#32 := by
                        have hc0 : ksW.vals[other.toNat]?.getD 0#32 = 0#32 := by
                          rw [hother_bv_eq'] at ‹_›; exact ‹_›
                        rw [List.getElem?_eq_getElem (by rw [hshW.vals_len]; exact hother_1024),
                          Option.getD_some] at hc0
                        rw [List.getElem?_eq_getElem
                          (by rw [hinvK.shapes.vals_len]; exact hother_1024)]
                        exact congrArg some hc0
                      have hmK : (K512MemA kPtr acap ksK ⋆ R) m := by
                        refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) m) ?_) hm
                        dsimp only [ksK]; k5_ext <;>
                          (first | rfl | simp only [other, k5ClauseOff, hw_tn, hw_sh1,
                            show (BitVec.ofNat 32 w0 &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 from
                              hslot_other_eq])
                      let cid := BitVec.ofNat 32 w0 >>> (1 : Nat)
                      have hcid_ne_ff : cid ≠ 0xFFFFFFFF#32 := fun h => by
                        have := congrArg BitVec.toNat h; rw [hw_sh1] at this
                        change w0 / 2 = 4294967295 at this; omega
                      have hoth_mem : other.toNat ∈ k5ClauseLits ksK cid.toNat := by
                        rw [hw_sh1, k5_mem_clauseLits_iff
                          (by rw [hinvK.shapes.arena_len]; have := hclW.alen_le
                              dsimp only [ksK, ksT, K512State.putArr, K512State.putHdr,
                                k5ClauseOff, k5ClauseSize] at *; omega)]
                        exact ⟨w0 % 2 ^^^ 1, by
                          dsimp only [ksK, ksT, K512State.putArr, K512State.putHdr,
                            k5ClauseSize] at *; omega, rfl⟩
                      have hte_ltK := k5_trl_end_lt_of_unassigned hinvK.shapes hnvW hinvK.assign
                        hother_nv (by dsimp only [ksK] at hov0; simp [hov0])
                      obtain ⟨hinvF, hsyncF⟩ :=
                        k5AssignStep_preserves_inv hinvK hsyncW hother_nv hov0
                        (fun hl0 => SemEntails.unit_of_falsified (hclW.cl_wf (w0 / 2) hcid_lt).2.2.2
                          fun x hx hne => (k5_falsified_lvl0_entails hinvK hl0
                            ((hclW.cl_wf (w0 / 2) hcid_lt).2.2.1 x hx) (hcl_fals x hx hne)).2)
                        (fun _ hrs => absurd hrs hcid_ne_ff)
                        (Or.inr ⟨by rw [hw_sh1]; exact hcid_lt, hoth_mem, fun x hx hne => by
                          rw [hw_sh1] at hx
                          exact k5_falsified_to_trail hinvK.shapes hnvW hinvK.assign hsyncW
                            ((hclW.cl_wf (w0 / 2) hcid_lt).2.2.1 x hx) (hcl_fals x hx hne)⟩)
                      have hfr_kf := k5PropAssign_frame hinvK hother_nv hov0 hcid_ne_ff
                      c0_hsteps_nogrp
                      c0_call hAssign
                      refine ⟨acap, ksK, R, hinvK.shapes, hclW.acap_lt,
                        hnvW, by
                          change (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> 1).toNat]?.getD
                            0#32).toNat + (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat]?.getD
                            0#32).toNat < 2 * ksK.nv.toNat
                          rw [hother_bv_eq]; exact hother_nv,
                        hte_ltK, (k5MemA_to_mem hmK).2, fun mF hmF => ?_⟩
                      change (K512Mem kPtr (k5AssignStep ksK
                        (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> 1).toNat]?.getD 0#32).toNat +
                          (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat]?.getD 0#32)
                        cid) ⋆ R) mF at hmF
                      rw [hother_bv_eq] at hmF
                      c0_hsteps!; rw [hw_tn]
                      exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0],
                          todo', k5AssignStep ksK other cid, chW) mF (by simp)
                        ⟨⟨hwcK.len_eq, hwcK.nodup, hwcK.chain_l, hwcK.chains_wc,
                            hwcK.chains_bnd, hwcK.tail_wc, hwcK.prev_rel⟩,
                          hinvF, hsyncF, hfrK.trans hfr_kf, hw_pr,
                          Nat.lt_of_lt_of_le hw_te hfr_kf.te_ge,
                          (hfr_kf.old_trl pO.toNat hw_te).1.trans hw_lit,
                          k5Mem_to_amem hinvF.shapes hmF⟩
                    · -- ov == 1 => continue
                      c0_hsteps!
                      have hmK : (K512MemA kPtr acap ksK ⋆ R) m := by
                        refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) m) ?_) hm
                        dsimp only [ksK]; k5_ext <;>
                          (first | rfl | simp only [other, k5ClauseOff, hw_tn, hw_sh1,
                            show (BitVec.ofNat 32 w0 &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 from
                              hslot_other_eq])
                      rw [hw_tn]
                      exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0],
                          todo', ksK, chW) _ (by simp)
                        ⟨hwcK, hinvK, hsyncW, hfrK, hw_pr, hw_te, hw_lit, hmK⟩
              · intro B L2 r m2 hB ih2 ⟨hm2, hr_le, hr2, hr_fals⟩
                dsimp only at hr_le hr2 hr_fals ⊢
                have hw_md : w0 % 2 ^ 32 / 2 = w0 / 2 := by rw [Nat.mod_eq_of_lt (by omega)]
                c0_hsplit
                · have hr_lt : r.toNat < sz.toNat := by
                    have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := by bv_omega
                    rwa [hw_md] at hc0
                  obtain ⟨hr_cap, hr_wrap, hr_lit⟩ := har_ok r.toNat hr_lt
                  have hr_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      r.toNat < 2 ^ 28 := by rw [hw_sh1]; exact hr_wrap
                  have hr_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                      r.toNat < acap := by rw [hw_sh1]; exact hr_cap
                  have hcand_1024 :
                      (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                      0#32).toNat + r.toNat]?.getD 0#32).toNat < 1024 := by
                    rw [hw_sh1]
                    change (ksW.arena[k5ClauseOff ksW (w0 / 2) + r.toNat]?.getD 0#32).toNat < 1024
                    unfold k5MaxV at hnvW; omega
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                    have hsz_bd : sz.toNat < 2 ^ 28 := by
                      have := hclW.alen_le; have := hclW.acap_lt; unfold dimacsBound at this
                      change k5ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                    bv_omega
                  iterate 5 c0_hstep
                  refine head_wp_load rfl
                    (K512MemATactics.load_k5_arena_off hr_bv_wrap hr_bv_cap hm2) ?_
                  c0_hsplit
                  · have hc_ne2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? ≠
                        some 2#32 := fun heq => by
                      have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                          r.toNat]?.getD 0#32).toNat]?.getD 0#32 ≠ 2#32 := by
                        dsimp only [ksT, K512State.putHdr] at *; bv_omega
                      rw [hw_md] at hc0; rw [heq, Option.getD_some] at hc0; exact hc0 rfl
                    c0_hsteps!
                    rw [hw_sh1]
                    exact hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) m2
                      ⟨hm2, Or.inr ⟨hr2, hr_lt, rfl, hc_ne2⟩⟩
                  · have hc_eq2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? =
                        some 2#32 := by
                      have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                          r.toNat]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := by
                        dsimp only [ksT, K512State.putHdr] at *; bv_omega
                      rw [hw_md] at hc0
                      have hvl :
                          (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < ksW.vals.length := by
                        rw [hshW.vals_len]
                        change (ksW.arena[k5ClauseOff ksW (w0 / 2) +
                          r.toNat]?.getD 0#32).toNat < 1024
                        unfold k5MaxV at hnvW; omega
                      rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                      rw [List.getElem?_eq_getElem hvl, hc0]
                    c0_hsteps!
                    refine ih2 (r + 1#32) m2 (by rw [hr1_wrap]; omega)
                      ⟨hm2, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega, fun q hq2 hqr => ?_⟩
                    rw [hr1_wrap] at hqr
                    by_cases hqe : q = r.toNat
                    · subst hqe; exact hc_eq2
                    · exact hr_fals q hq2 (by omega)
                · have hr_eq : r.toNat = sz.toNat := by
                    have hge : ¬ r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := by
                      bv_omega
                    rw [hw_md] at hge; dsimp only [sz] at hr_le ⊢; omega
                  c0_hsteps!
                  exact hB (r, 0xFFFFFFFF#32, 0#32) m2
                    ⟨hm2, Or.inl ⟨rfl, fun q hq2 hqsz => hr_fals q hq2 (by omega)⟩⟩
              · intro B L2 _ hL2
                exact hL2 2#32 _ ⟨by simpa [ksT] using hm, hsz_ge, le_refl _, fun _ _ hq => by
                  rw [show (2#32 : BitVec 32).toNat = 2 from rfl] at hq; omega⟩
        · -- inner loop done => next outer iteration
          c0_hsteps!
          exact ihO ksW mW (by
            have h1 := hinvO.assign.trl_end_le
            have h2 : ksO.nv.toNat = ks0.nv.toNat := congrArg BitVec.toNat hfrO.pres.nv
            dsimp only [pO] at hw_pr; omega) ⟨hinvW, hsyncW, hfrW, hmW⟩
    · -- outer loop done => return 0xFFFFFFFF
      have hpr_eq : ksO.prop = ksO.trl_end :=
        BitVec.eq_of_toNat_eq (by have := hinvO.assign.prop_le; bv_omega)
      c0_hsteps!
      exact hret 0xFFFFFFFF#32 ksO mO hinvO hsyncO hfrO (fun _ => hpr_eq)
        (fun h => absurd rfl h) hmO

end LeanQbe.T.Examples.Kissat.FullM4Sweep
