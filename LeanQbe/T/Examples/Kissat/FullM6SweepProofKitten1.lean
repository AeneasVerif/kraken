module

import LeanQbe.T.Examples.Kissat.FullM4SweepKitten1
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKittenLemmas

/-!
# Kissat `D-Full` M6 — Scaled `K6` Sub-Solver Proofs (`Part 1`, `10/39` cumulative)

1. Header focus/unfocus (`k6Focus_hdr`, `k6Unfocus_hdr`), `K6Inv` cast/status/ticks helpers, and
   `K6WChainCursor` (2WL watch-chain cursor with inline binary `K6_BIN_FLAG` invariant, shared by
   `full_k6_flip` and `full_k6_propagate`).
2. Parametric `(Γ : Env)` `Func.wp` proofs for `5/39` owned functions (`10/39` cumulative):
   - `full_k6_backtrack_wp`
   - `full_k6_init_wp`
   - `full_k6_add_clause_wp`
   - `full_k6_flip_wp`
   - `full_k512_add_live_m6_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Header Focus, `K6Inv` Field-Cast Helpers, & `K6WChainCursor` -/

theorem k6Focus_hdr {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6Mem L kPtr ks ⋆ R) m) :
    (array (t := i32) kPtr (k6HdrWords ks) ⋆ ((K6Tree L kPtr ks).rest (k6Path 0) ⋆ R)) m :=
  SepTree.focus (t := K6Tree L kPtr ks) (k6Path 0) hm

theorem k6Unfocus_hdr {L : K6Layout} {kPtr : BitVec 64} {ks ks' : K6State}
    {hdr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (heq : ((K6Tree L kPtr ks).set (k6Path 0) (array (t := i32) kPtr hdr')).eval =
      K6Mem L kPtr ks')
    (hm : (array (t := i32) kPtr hdr' ⋆ ((K6Tree L kPtr ks).rest (k6Path 0) ⋆ R)) m) :
    (K6Mem L kPtr ks' ⋆ R) m :=
  SepTree.unfocus_eq (t := K6Tree L kPtr ks) (k6Path 0) heq hm

namespace K6DynExtraMem
@[scoped c0_load] theorem load_k6arr32_z1 {a : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array (t := i32) a xs ⋆ R) m)
    (hi : 1 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 1 * 4) = some (xs[1]'hi) := by
  rw [k6_ptr_nat_mul4 a 1 (by decide)]; exact loadVal_array (t := i32) (by decide) hi h
end K6DynExtraMem

theorem k6_bv32_zero : (0 : BitVec 32) = 0#32 := rfl
theorem k6_bv32_one : (1 : BitVec 32) = 1#32 := rfl

theorem k6_vals_cons {t : Ty} {ts : List Ty} (a : Arg Val t) (as : Tup (Arg Val) ts) :
    @vals (t :: ts) (a, as) = (a.val, vals as) := rfl
theorem k6_vals_nil : vals (ts := []) () = () := rfl
theorem k6_val_var {t : Ty} (v : Val t) : (@Arg.var Val t v).val = v := rfl
theorem k6_val_imm {t : Ty} (v : Val t) : (@Arg.imm Val t v).val = v := rfl
theorem k6_fst {α β : Sort _} (a : α) (b : β) : (a, b).1 = a := rfl
theorem k6_snd {α β : Sort _} (a : α) (b : β) : (a, b).2 = b := rfl

scoped macro "k6_call " h:ident : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_); dsimp only [vals, Arg.val]))

theorem k6_maxV_call_step {Γ : Env} {rs : List Ty}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {n : Nat} (hn : n < 2 ^ 64) {Q : Post rs} {X : XPost}
    {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV n), ())) m) :
    wp Γ Q X (@Expr.call Val Cont rs "full_m6_max_v" [i64] [i64]
      (@Arg.var Val i64 (BitVec.ofNat 64 n), ()) k) m := by
  refine LeanQbe.T.wp_call_of_spec _ _ (hMaxV _ _ _ _ ?_)
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  change wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 n).toNat), ())) m
  rw [h1]; exact hk

open scoped K6DynExtraMem

theorem k6ClausesOk_cast {L : K6Layout} {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (h : K6ClausesOk L P ks)
    (h1 : ks'.acap = ks.acap) (h2 : ks'.max_v = ks.max_v) (h3 : ks'.max_orig = ks.max_orig)
    (h4 : ks'.max_cl = ks.max_cl) (h5 : ks'.nv = ks.nv) (h6 : ks'.nc = ks.nc)
    (h7 : ks'.alen = ks.alen) (h8 : ks'.nassump = ks.nassump) (h9 : ks'.nkl = ks.nkl)
    (h10 : ks'.nana = ks.nana) (h11 : ks'.incons = ks.incons) (h12 : ks'.assump = ks.assump)
    (h13 : ks'.flags = ks.flags) (h14 : ks'.clOff = ks.clOff) (h15 : ks'.clSz = ks.clSz)
    (h16 : ks'.arena = ks.arena) : K6ClausesOk L P ks' := by
  rcases h with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩
  refine ⟨h1.trans c1, h2.trans c2, h3.trans c3, h4.trans c4, h5 ▸ c5, h6 ▸ c6, h7 ▸ c7,
    h8 ▸ c8, h9 ▸ c9, h10 ▸ c10, ?_, ?_, h11 ▸ c13, ?_, ?_⟩
  · intro cid hc; rw [h6] at hc
    have := c11 cid hc
    simp only [k6ClauseSize, k6ClauseOff, k6ClauseLits, h14, h15, h16, h7, h5]; exact this
  · intro c1' c2' hlt hc; rw [h6] at hc
    simp only [k6ClauseSize, k6ClauseOff, h14, h15]; exact c12 c1' c2' hlt hc
  · intro i hi; rw [h8] at hi; rw [h12, h5]; exact c14 i hi
  · intro v hv; rw [h5] at hv; rw [h13]; exact c15 v hv

theorem k6BaseAssignOk_cast {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (h : K6BaseAssignOk P ks)
    (h1 : ks'.nv = ks.nv) (h2 : ks'.lvl = ks.lvl) (h3 : ks'.prop = ks.prop)
    (h4 : ks'.trl_end = ks.trl_end) (h5 : ks'.unass = ks.unass)
    (h6 : ks'.lvlArr = ks.lvlArr) (h7 : ks'.rsn = ks.rsn)
    (h8 : ks'.trl = ks.trl) (h9 : ks'.vals = ks.vals) : K6BaseAssignOk P ks' := by
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  refine ⟨by rw [h4, h1]; exact a1, by rw [h3, h4]; exact a2, by rw [h5, h4, h1]; exact a3,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a4 l hl,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a5 l hl,
    fun l hl => by rw [h1] at hl; rw [h9, h4, h8]; exact a6 l hl,
    by unfold k6TrailLits; rw [h8, h4]; exact a7,
    fun l hl => by unfold k6TrailLits at hl; rw [h8, h4] at hl; rw [h1]; exact a8 l hl,
    fun v hv => by rw [h1] at hv; rw [h6, h2]; exact a9 v hv,
    fun v hv hv0 => by rw [h1] at hv; rw [h9] at hv0; rw [h6, h7]; exact a10 v hv hv0,
    fun i j hij hj => by rw [h4] at hj; rw [h6, h8]; exact a11 i j hij hj,
    fun i j hij hi hp heq => by
      rw [h4] at hi; rw [h6, h8] at hp heq; rw [h7, h8]; exact a12 i j hij hi hp heq,
    fun i hi => by rw [h4] at hi; dsimp only; rw [h8, h6, h9]; exact a13 i hi⟩

theorem k6AddTicks_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (tk' : BitVec 32) : K6Inv L P (ks.putHdr .ticks tk') :=
  ⟨hinv.shapes.putHdr .ticks tk',
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6SetStatus_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (st' : BitVec 32) : K6Inv L P (ks.putHdr .status st') :=
  ⟨hinv.shapes.putHdr .status st',
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6_trailSynced_of_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hl0 : ks.lvl = 0#32) : K6TrailSynced ks := fun i hi => by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  have hl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi htrl_len)
  have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
  rw [hl0] at hle
  have h0 : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 :=
    BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have ok := hinv.assign.lvl0_ok i hi h0
  exact ⟨ok.1, ok.2.1⟩

private theorem k6_list_flatten_set_sub_perm {α : Type} (xs : List (List α)) {l : Nat}
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

private theorem k6_list_flatten_nodup_getElem {α : Type} :
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
    have ihr := k6_list_flatten_nodup_getElem ha.2.1 hi'
    refine ⟨ihr.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem_cons_succ] at hai; simp only [List.getElem_cons_zero] at haj
      exact ha.2.2 a haj a (List.mem_flatten.mpr ⟨tl[i], List.getElem_mem hi', hai⟩) rfl
    | succ j' =>
      exact ihr.2 j' (fun h => hne (congrArg Nat.succ h)) (by simp at hj; exact hj) a hai haj

theorem k6_wchain_bypass {wn : List (BitVec 32)} {hd nxt : BitVec 32}
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

structure K6WChainCursor (ks : K6State) (l : Nat) (chains : List (List Nat))
    (done todo : List Nat) (prev w : BitVec 32) : Prop where
  len_eq : chains.length = 2 * ks.nv.toNat
  nodup : chains.flatten.Nodup
  chain_l : chains[l]?.getD [] = done ++ todo
  chains_wc : ∀ x < 2 * ks.nv.toNat,
    K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])
  chains_bnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
    u < 2 * ks.nc.toNat ∧ 2 ≤ k6ClauseSize ks (u / 2) ∧
    (ks.arena[k6ClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
    let wb := ks.wblit[u]?.getD 0#32
    let bv := (wb &&& 0x7FFFFFFF#32).toNat
    bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (u / 2) ∧
    ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (u / 2) = 2) ∧
    (k6ClauseSize ks (u / 2) = 2 →
      bv = (ks.arena[k6ClauseOff ks (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat)
  tail_wc : K5WChain ks.wnext w todo
  prev_rel : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks.whead[l]?.getD 0xFFFFFFFF#32 = w) ∨
    (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
      u < ks.wnext.length ∧ ks.wnext[u]?.getD 0xFFFFFFFF#32 = w)

theorem K6WChainCursor.watchesOk {ks : K6State} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K6WChainCursor ks l chains done todo prev w) : K6WatchesOk ks :=
  ⟨chains, wc.len_eq, wc.nodup, wc.chains_wc, wc.chains_bnd⟩

theorem K6WChainCursor.init {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    (hnv : ks.nv.toNat ≤ L.maxV) (hw : K6WatchesOk ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) :
    ∃ chains, K6WChainCursor ks l chains [] (chains[l]?.getD []) 0xFFFFFFFF#32
      (ks.whead[l]?.getD 0#32) := by
  have hm := L.hmaxV
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; omega
  have hwh_eq : ks.whead[l]?.getD 0#32 = ks.whead[l]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwh_len]; rfl
  rw [hwh_eq]
  exact ⟨chains, hlen, hnd, rfl, hwc, hbnd, hwc l hl, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem K6WChainCursor.step_unfold {L : K6Layout} {ks : K6State} (hnc : ks.nc.toNat ≤ L.maxCl)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K6WChainCursor ks l chains done todo prev w) (hne : w ≠ 0xFFFFFFFF#32) :
    ∃ w0 todo', w0 < ks.wnext.length ∧
      todo = w0 :: todo' ∧ w = BitVec.ofNat 32 w0 ∧ w0 < 2 * ks.nc.toNat ∧ w0 < 2 * L.maxCl ∧
      w.toNat = w0 ∧ (w >>> (1 : Nat)).toNat = w0 / 2 ∧ (w &&& 1#32).toNat = w0 % 2 ∧
      2 ≤ k6ClauseSize ks (w0 / 2) ∧
      (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2)]?.getD 0#32).toNat = l ∧
      let wb := ks.wblit[w0]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w0 / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w0 / 2) = 2) ∧
      (k6ClauseSize ks (w0 / 2) = 2 →
        bv = (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32).toNat) ∧
      K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo' := by
  have hm := L.hmaxV
  obtain ⟨w0, todo', hw0, htd, hw_eq, htail⟩ := K5WChain_getElem_of_eq wc.tail_wc hne
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l, htd]; exact List.mem_append_right _ List.mem_cons_self
  have hb := wc.chains_bnd l hl w0 hm_l
  have hlt_mc : w0 < 2 * L.maxCl := by omega
  have hlt32 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hlt_mc; omega
  have hw_tn : w.toNat = w0 := by rw [hw_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
  have hw_div2 : (w >>> (1 : Nat)).toNat = w0 / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hw_tn]
  have hw_mod2 : (w &&& 1#32).toNat = w0 % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 1, hw_tn]
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0 := by
    rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  refine ⟨w0, todo', hw0, htd, hw_eq, hb.1, hlt_mc, hw_tn, hw_div2, hw_mod2,
    hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2, ?_⟩
  rw [hnxt_eq]; exact htail

theorem k6WatchSkip_cursor {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    {l : Nat} {chains : List (List Nat)} {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    (hw0_len : w0 < ks.wnext.length) :
    K6WChainCursor ks l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  have hm := L.hmaxV
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hw0_len]; rfl
  rcases K5WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0_len; unfold K6Layout.maxCl at hw0_len; omega
      have h2 : w0' < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, wc.chains_bnd, ?_,
      Or.inr ⟨done, w0, rfl, rfl, hw0_len, hnxt_eq.symm⟩⟩
    rwa [List.getElem?_eq_getElem hw0', Option.getD_some]

theorem k6WatchKeep_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {other : BitVec 32} (hoth : other.toNat < 2 * ks.nv.toNat)
    (hot_mem : other.toNat ∈ k6ClauseLits ks (w0 / 2))
    (hsz3 : k6ClauseSize ks (w0 / 2) ≠ 2) :
    let ks' := ks.putArr .wblit w0 other
    K6Inv L P ks' ∧
    K6WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  intro ks'
  have hm := L.hmaxV
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le; have hnc := hinv.clauses.nc_le
  have hoth31 : other.toNat < 2 ^ 31 := by omega
  have hmk := k6_bv32_lt31_and_mask hoth31
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hwb_len : w0 < ks.wblit.length := by rw [hsh.wblit_len]; have := hb0.1; omega
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; have := hb0.1; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases K5WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hnc; omega
      have h2 : w0' < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    have wc' : K6WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
        (ks.wnext[w0]?.getD 0#32) := by
      refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, ?_, ?_,
        Or.inr ⟨done, w0, rfl, rfl, hwn_len, hnxt_eq.symm⟩⟩
      · intro x hx u hu; have hbu := wc.chains_bnd x hx u hu
        by_cases hu0 : u = w0
        · rw [hu0] at hbu ⊢
          refine ⟨hbu.1, hbu.2.1, hbu.2.2.1, ?_⟩
          change let wb := (ks.wblit.set w0 other)[w0]?.getD 0#32
                 let bv := (wb &&& 0x7FFFFFFF#32).toNat
                 bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w0 / 2) ∧
                 ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w0 / 2) = 2) ∧
                 (k6ClauseSize ks (w0 / 2) = 2 →
                   bv = (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32).toNat)
          dsimp only
          rw [List.getElem?_set_self hwb_len, Option.getD_some, hmk.1, hmk.2]
          exact ⟨hoth, hot_mem, ⟨fun h => absurd rfl h, fun h => absurd h hsz3⟩,
            fun h => absurd h hsz3⟩
        · refine ⟨hbu.1, hbu.2.1, hbu.2.2.1, ?_⟩
          have hwb : (ks.wblit.set w0 other)[u]? = ks.wblit[u]? :=
            List.getElem?_set_ne (Ne.symm hu0)
          dsimp only [ks', K6State.putArr]; rw [hwb]
          exact ⟨hbu.2.2.2.1, hbu.2.2.2.2.1, hbu.2.2.2.2.2.1, hbu.2.2.2.2.2.2⟩
      · change K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo'
        rwa [List.getElem?_eq_getElem hw0', Option.getD_some]
    exact ⟨⟨hsh.putArr .wblit w0 other,
      k6ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      wc'.watchesOk,
      k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      by dsimp only [ks', K6State.putArr]; exact hinv.reasons⟩, wc'⟩

theorem k6WatchReloc_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {ri : Nat} (hri_ge : 2 ≤ ri) (hri_lt : ri < k6ClauseSize ks (w0 / 2))
    {repl other : BitVec 32} (hrepl_ne : repl.toNat ≠ l)
    (hother_eq : other = ks.arena[k6ClauseOff ks (w0 / 2) + ((w0 % 2) ^^^ 1)]?.getD 0#32)
    (hrepl_eq : repl = ks.arena[k6ClauseOff ks (w0 / 2) + ri]?.getD 0#32) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let cid := w0 / 2
    let slot := w0 % 2
    let off := k6ClauseOff ks cid
    let ar' := (ks.arena.set (off + slot) repl).set (off + ri) (BitVec.ofNat 32 l)
    let wh1 := if prev = 0xFFFFFFFF#32 then ks.whead.set l nxt else ks.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ks.wnext else ks.wnext.set prev.toNat nxt
    let ks1 : K6State := { ks with arena := ar', whead := wh1, wnext := wn1 }
    let ks' := k6WatchStep0 ks1 w repl other
    K6Inv L P ks' ∧ (∃ chains', K6WChainCursor ks' l chains' done todo' prev nxt) := by
  intro w nxt cid slot off ar' wh1 wn1 ks1 ks'
  have hm := L.hmaxV
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le; have hnc := hinv.clauses.nc_le
  have hch_l : l < chains.length := by rw [wc.len_eq]; exact hl
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hcid_lt : cid < ks.nc.toNat := by dsimp only [cid]; omega
  have hwf_c := hinv.clauses.cl_wf cid hcid_lt
  have hsz_ge : 2 ≤ k6ClauseSize ks cid := hb0.2.1
  have hsz_ne2 : k6ClauseSize ks cid ≠ 2 := by dsimp only [cid]; omega
  have hslot_lt : slot < 2 := Nat.mod_lt w0 (by decide)
  have hother_slot_lt : slot ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [slot, h]
  have hoff_le : off + k6ClauseSize ks cid ≤ ks.alen.toNat := hwf_c.2.1
  have har_len : ks.arena.length = L.acap := hsh.arena_len
  have hal_le : ks.alen.toNat ≤ L.acap := hinv.clauses.alen_le
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; have := hb0.1; omega
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; omega
  have hnxt_eq : nxt = ks.wnext[w0]'hwn_len := by
    dsimp only [nxt]; rw [List.getElem?_eq_getElem hwn_len, Option.getD_some]
  have hoff_le' : k6ClauseOff ks (w0 / 2) + k6ClauseSize ks (w0 / 2) ≤ ks.alen.toNat := hoff_le
  have har_slot :
      ks.arena[off + slot]'(by dsimp only [off, cid, slot]; omega) = BitVec.ofNat 32 l := by
    have ha := hb0.2.2.1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at ha
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat]
      exact ha.trans (Nat.mod_eq_of_lt (by omega)).symm)
  have hrepl_lt_ar : off + ri < ks.arena.length := by dsimp only [off, cid]; omega
  have hrepl_mem : repl.toNat ∈ k6ClauseLits ks cid := by
    rw [hrepl_eq, k6_mem_clauseLits_iff (by omega)]; exact ⟨ri, hri_lt, rfl⟩
  have hrepl_nv : repl.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hrepl_mem
  have hother_mem : other.toNat ∈ k6ClauseLits ks cid := by
    rw [hother_eq, k6_mem_clauseLits_iff (by omega)]; exact ⟨slot ^^^ 1, by omega, rfl⟩
  have hother_nv : other.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hother_mem
  have har'_eq : ar' = (ks.arena.set (off + slot) (ks.arena[off + ri]'hrepl_lt_ar)).set
      (off + ri) (ks.arena[off + slot]'(by dsimp only [off]; omega)) := by
    dsimp only [ar']; rw [har_slot, hrepl_eq]
    change (ks.arena.set (off + slot) (ks.arena[off + ri]?.getD 0#32)).set (off + ri) _ = _
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
  have hsh1 : ks1.ShapesOk L :=
    { hsh with
      whead_len := by dsimp only [ks1, wh1]; split <;> simp [hsh.whead_len]
      wnext_len := by dsimp only [ks1, wn1]; split <;> simp [hsh.wnext_len]
      arena_len := by simp [ks1, ar', hsh.arena_len] }
  have hsh' := k6WatchStep0_preserves_shapes hsh1 w repl other
  have hlits_perm_all : ∀ c < ks.nc.toNat, (k6ClauseLits ks' c).Perm (k6ClauseLits ks c) := by
    intro c hc
    by_cases hcc : c = cid
    · subst hcc; change (((ar'.drop off).take (k6ClauseSize ks cid)).map BitVec.toNat).Perm
        (((ks.arena.drop off).take (k6ClauseSize ks cid)).map BitVec.toNat)
      rw [har'_eq]
      exact (k6_drop_take_set_swap ks.arena (off := off) (sz := k6ClauseSize ks cid)
        (p := slot) (q := ri) (by omega) hri_lt (by dsimp only [off]; omega)).map _
    · have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
          idx < k6ClauseOff ks c ∨ k6ClauseOff ks c + k6ClauseSize ks c ≤ idx := by
        intro idx hidx; by_cases hlt : c < cid
        · right; have hm := hinv.clauses.cl_mono c cid hlt hcid_lt
          change k6ClauseOff ks c + k6ClauseSize ks c ≤ off at hm
          rcases hidx with rfl | rfl <;> omega
        · left; have hm := hinv.clauses.cl_mono cid c (by omega) hc
          change off + k6ClauseSize ks cid ≤ k6ClauseOff ks c at hm
          dsimp only [cid] at hm; rcases hidx with rfl | rfl <;> omega
      change (((ar'.drop (k6ClauseOff ks c)).take (k6ClauseSize ks c)).map BitVec.toNat).Perm _
      dsimp only [ar']
      rw [k6_drop_take_set_out _ _ (hout _ (Or.inr rfl)),
        k6_drop_take_set_out _ _ (hout _ (Or.inl rfl))]
      exact List.Perm.refl _
  have hcl' : K6ClausesOk L P ks' :=
    { hinv.clauses with
      cl_wf := fun c hc => by
        have hw := hinv.clauses.cl_wf c hc; have hp := hlits_perm_all c hc
        exact ⟨hw.1, hw.2.1, fun x hx => hw.2.2.1 x (hp.mem_iff.mp hx),
          SemEntails.perm hp.symm hw.2.2.2⟩ }
  have hrsn' : K6ReasonOk ks' := fun i hi => by
    rcases hinv.reasons i hi with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right; have hp := hlits_perm_all _ hr_lt
      exact ⟨hr_lt, hp.mem_iff.mpr hmem, fun x hx => hall x (hp.mem_iff.mp hx)⟩
  let chains1 := chains.set l (done ++ todo')
  have hch1_len : chains1.length = 2 * ks1.nv.toNat := by rw [List.length_set]; exact wc.len_eq
  have hch_l_eq : chains[l]'hch_l = done ++ w0 :: todo' := by
    have := wc.chain_l; rwa [List.getElem?_eq_getElem hch_l, Option.getD_some] at this
  have hperm1 := k6_list_flatten_set_sub_perm chains hch_l done todo' w0 hch_l_eq
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
    · exfalso
      have h2 : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
      have h3 := congrArg BitVec.toNat (hp_eq.symm.trans hprev)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at h2; omega),
        show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h3
      unfold K6Layout.maxCl at h2; omega
  have htail_ks : K5WChain ks.wnext nxt todo' := by
    rcases K5WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
    · cases hn
    · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
      have hw0_eq : w0 = w0' := by
        have ht := congrArg BitVec.toNat hw_eq'
        have h1 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hnc; omega
        have h2 : w0' < 2 ^ 32 := by
          rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
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
      · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
        have hu_tn : prev.toNat = u := by
          rw [hp_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
        have hwh1 : wh1 = ks.whead := by simp [wh1, hprev]
        have hwn1 : wn1 = ks.wnext.set u nxt := by simp [wn1, hprev, hu_tn]
        have hnd_get := k6_list_flatten_nodup_getElem wc.nodup hch_l
        by_cases hxl : l = x
        · subst hxl; rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          simp only [chains1, List.getElem_set_self, hdone_eq, List.append_assoc, ks1, hwh1, hwn1]
          have hwc0 := wc.chains_wc l hx
          rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_l_eq, hdone_eq,
            List.append_assoc] at hwc0
          have hnd_l := hnd_get.1; rw [hch_l_eq, hdone_eq, List.append_assoc] at hnd_l
          simpa [List.append_assoc] using k6_wchain_bypass hwc0 hnd_l hu_len hwn_len hnxt_eq.symm
        · have hu_not_x : u ∉ chains[x]'hx0 :=
            hnd_get.2 x (Ne.symm hxl) hx0 u (by rw [hch_l_eq, hdone_eq]; simp)
          have hwc0 := wc.chains_wc x hx
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
          simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1]
          exact hwc0.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_not_x (h ▸ hy))).symm
  have hbnd1 : ∀ x < 2 * ks1.nv.toNat, ∀ u ∈ chains1[x]?.getD [],
      u < 2 * ks1.nc.toNat ∧ 2 ≤ k6ClauseSize ks1 (u / 2) ∧
      (ks1.arena[k6ClauseOff ks1 (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      let wb := ks1.wblit[u]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks1.nv.toNat ∧ bv ∈ k6ClauseLits ks1 (u / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks1 (u / 2) = 2) ∧
      (k6ClauseSize ks1 (u / 2) = 2 →
        bv = (ks1.arena[k6ClauseOff ks1 (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat) := by
    intro x hx u hu
    have hbu := wc.chains_bnd x hx u (hch1_sub x hx u hu)
    have hu_ne : u ≠ w0 := fun h => hw0_not_in (by
      rw [← h, List.mem_flatten]; have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
      exact ⟨chains1[x], List.getElem_mem hx1, by simpa [List.getElem?_eq_getElem hx1] using hu⟩)
    have hdisj : ∀ (huc : u / 2 ≠ cid) (koff : Nat), koff < 2 →
        ks1.arena[k6ClauseOff ks (u / 2) + koff]? = ks.arena[k6ClauseOff ks (u / 2) + koff]? :=
      fun huc koff hkoff => by
        dsimp only [ks1, ar']
        have hu_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
        have hne_i : ∀ idx, idx = off + slot ∨ idx = off + ri →
            idx ≠ k6ClauseOff ks (u / 2) + koff := fun idx hidx => by
          by_cases hlu : u / 2 < cid
          · have hmn := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have := hbu.2.1; change k6ClauseOff ks (u / 2) + k6ClauseSize ks (u / 2) ≤ off at hmn
            rcases hidx with rfl | rfl <;> omega
          · have hmn := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change off + k6ClauseSize ks cid ≤ k6ClauseOff ks (u / 2) at hmn
            dsimp only [cid] at hmn; rcases hidx with rfl | rfl <;> omega
        rw [List.getElem?_set_ne (hne_i _ (Or.inr rfl)),
          List.getElem?_set_ne (hne_i _ (Or.inl rfl))]
    have har_u : ks1.arena[k6ClauseOff ks (u / 2) + u % 2]? =
        ks.arena[k6ClauseOff ks (u / 2) + u % 2]? := by
      by_cases huc : u / 2 = cid
      · dsimp only [ks1, ar']
        have hm1 : u % 2 ≠ slot := fun hm => hu_ne (by omega)
        have hm2 : u % 2 ≠ ri := by have := Nat.mod_lt u (by decide : 0 < 2); omega
        rw [huc, List.getElem?_set_ne (by dsimp only [off]; omega),
          List.getElem?_set_ne (by dsimp only [off]; omega)]
      · exact hdisj huc (u % 2) (Nat.mod_lt u (by decide))
    have hp_u : (k6ClauseLits ks1 (u / 2)).Perm (k6ClauseLits ks (u / 2)) :=
      hlits_perm_all (u / 2) (Nat.div_lt_of_lt_mul hbu.1)
    refine ⟨hbu.1, hbu.2.1, ?_, hbu.2.2.2.1, hp_u.mem_iff.mpr hbu.2.2.2.2.1,
      hbu.2.2.2.2.2.1, fun h2 => ?_⟩
    · change (ks1.arena[k6ClauseOff ks (u / 2) + u % 2]?.getD 0#32).toNat = x
      rw [har_u]; exact hbu.2.2.1
    · have huc_ne : u / 2 ≠ cid := fun heq => by rw [heq] at h2; exact hsz_ne2 h2
      have hk1 := hdisj huc_ne (u % 2 ^^^ 1) (by
        rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h])
      change ((ks1.wblit[u]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat =
        (ks1.arena[k6ClauseOff ks (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat
      rw [hk1]; exact hbu.2.2.2.2.2.2 h2
  have hw_tn : w.toNat = w0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hnc; omega)]
  have har_slot_repl :
      (ar'[k6ClauseOff ks (w.toNat / 2) + w.toNat % 2]?.getD 0#32).toNat = repl.toNat := by
    rw [hw_tn]; change (ar'[off + slot]?.getD 0#32).toNat = repl.toNat
    simp [ar', List.getElem?_set_ne (by omega : off + ri ≠ off + slot),
      List.getElem?_set_self (by dsimp only [off]; omega : off + slot < ks.arena.length)]
  have hot_mem1 : other.toNat ∈ k6ClauseLits ks1 (w.toNat / 2) := by
    have hp := hlits_perm_all cid hcid_lt
    rw [hw_tn]; exact hp.mem_iff.mpr hother_mem
  have hw_step0 := k6WatchStep0_preserves_watches_with hsh1 hch1_len hch1_nd hwc1 hbnd1
    (w := w) (l := repl) (ot := other)
    (by change w.toNat < 2 * ks.nc.toNat; rw [hw_tn]; exact hb0.1)
    hnc hnv hrepl_nv hother_nv hot_mem1
    (fun h2 => absurd h2 (by change k6ClauseSize ks (w.toNat / 2) ≠ 2; rw [hw_tn]; exact hsz_ne2))
    (by change 2 ≤ k6ClauseSize ks (w.toNat / 2); rw [hw_tn]; exact hsz_ge)
    har_slot_repl (by rw [hw_tn]; exact hw0_not_in)
  have hbf0 : (if k6ClauseSize ks1 (w.toNat / 2) = 2 then 0x80000000#32 else 0#32) = 0#32 := by
    have hne : k6ClauseSize ks1 (w.toNat / 2) ≠ 2 := by
      change k6ClauseSize ks (w.toNat / 2) ≠ 2; rw [hw_tn]; exact hsz_ne2
    simp only [hne, ite_false]
  dsimp only at hw_step0; rw [hbf0, BitVec.or_zero] at hw_step0
  have hrepl_ch1 : repl.toNat < chains1.length := by rw [hch1_len]; exact hrepl_nv
  let chains' := chains1.set repl.toNat (w.toNat :: chains1[repl.toNat]'hrepl_ch1)
  have hwc_cur' : K6WChainCursor ks' l chains' done todo' prev nxt := by
    have hch'_l : l < chains'.length := by
      simp only [chains', List.length_set]; rw [hch1_len]; exact hl
    have hcl'_eq : chains'[l]?.getD [] = done ++ todo' := by
      rw [List.getElem?_eq_getElem hch'_l, Option.getD_some]
      simp only [chains', List.getElem_set_ne hrepl_ne, chains1, List.getElem_set_self]
    have hnd_l := (k6_list_flatten_nodup_getElem wc.nodup hch_l).1
    have hw0_nt : w0 ∉ todo' := by
      rw [hch_l_eq] at hnd_l; exact (List.nodup_cons.mp (List.nodup_append.mp hnd_l).2.1).1
    have htail1 : K5WChain ks1.wnext nxt todo' := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · simp [ks1, wn1, hprev, htail_ks]
      · rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
          have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
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
        · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
          have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
          have hune : w0 ≠ u := fun heq => by
            rw [hch_l_eq, hde] at hnd_l
            exact (List.nodup_append.mp hnd_l).2.2 u (by simp) w0 List.mem_cons_self heq.symm
          refine ⟨pfx, u, hde, hp_eq, by simpa [ks', k6WatchStep0, ks1, wn1, hprev] using hu_len,
            ?_⟩
          change (ks1.wnext.set w.toNat _)[u]?.getD 0xFFFFFFFF#32 = nxt
          rw [hw_tn, List.getElem?_set_ne hune]; change wn1[u]?.getD 0xFFFFFFFF#32 = nxt
          simp only [wn1, hprev, ↓reduceIte, hu_tn, List.getElem?_set_self hu_len, Option.getD_some]
    exact ⟨hw_step0.1, hw_step0.2.1, hcl'_eq, hw_step0.2.2.1, hw_step0.2.2.2.1, htail', hprev'⟩
  exact ⟨⟨hsh', hcl', hwc_cur'.watchesOk,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hrsn'⟩, chains', hwc_cur'⟩

theorem k6FlipFinish_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hval1 : ks.vals[lit.toNat]? = some 1#32)
    (hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32) :
    K6Inv L P ((ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32) := by
  let ks' := (ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32
  have hm := L.hmaxV; have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hlit
  obtain ⟨hn_eq, _⟩ := k6_bv32_xor1_lt hlit
  have hl_ne : lit.toNat ≠ (lit ^^^ 1#32).toNat := by
    rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hlen_v : lit.toNat < ks.vals.length := by rw [hsh.vals_len]; omega
  have hlen_nl : (lit ^^^ 1#32).toNat < ks.vals.length := by
    rw [hsh.vals_len, hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
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
      have : x / 2 = (lit.toNat ^^^ 1) / 2 := by
        rw [h, hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
      rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[x]? = ks.vals[x]?
    rw [List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm]
  have hba' : K6BaseAssignOk P ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, ?_, ?_, ?_, h0.trl_nodup, h0.trl_lt,
      h0.trl_lvl_le, ?_, h0.trl_lvl_mono, h0.dec_earliest, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit]; exact Or.inr (Or.inr rfl)
        · rw [hval_nl]; exact Or.inr (Or.inl rfl)
      · rw [hval_other l hv]; exact h0.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit,
            show lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat by
              rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl],
            hval_nl]; simp
        · rw [hval_nl,
            show (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat by
              rw [hn_eq]; exact litNeg_litNeg _,
            hval_lit]; simp
      · have hnv' : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hval_other l hv, hval_other (l ^^^ 1) hnv']; exact h0.vals_neg_iff l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have hex := (h0.vals_nz_iff_trl lit.toNat hlit).mp (by simp [hval1])
        have hnz_new : ks'.vals[l]?.getD 0#32 ≠ 0#32 := by
          have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
            rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
              rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
                (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
          rcases he with rfl | rfl
          · rw [hval_lit]; decide
          · rw [hval_nl]; decide
        exact ⟨fun _ => by
          dsimp only [ks', K6State.putArr]; simpa [hv] using hex, fun _ => hnz_new⟩
      · rw [hval_other l hv]; exact h0.vals_nz_iff_trl l hl
    · intro v hv hv0; by_cases hvq : v = lit.toNat / 2
      · exfalso; subst hvq; rcases k6_nat_xor1_cases lit.toNat with ⟨ha, _⟩ | ⟨_, hb⟩
        · rw [← ha, hval_lit] at hv0; cases hv0
        · rw [show 2 * (lit.toNat / 2) = (lit ^^^ 1#32).toNat by
            rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega, hval_nl] at hv0
          cases hv0
      · rw [hval_other (2 * v) (by omega)] at hv0; exact h0.unass_lvl_zero v hv hv0
    · intro i hi; dsimp only [ks', K6State.putArr]; intro hlv
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq => by
        rw [heq, ← hv_eq] at hlv; exact hlvl_nz hlv
      have hne_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k6_nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      have h0l := h0.lvl0_ok i hi hlv
      change ks'.vals[(ks.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32 ∧ _
      rw [hval_other _ hne_v, hval_other _ hne_x]; exact h0l
  exact ⟨(hsh.putArr .vals _ _).putArr .vals _ _,
    k6ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by dsimp only [K6State.putArr]; exact hinv.watches,
    hba', by dsimp only [K6State.putArr]; exact hinv.reasons⟩

/-! ## 2. `6/39`: `full_k6_backtrack_wp` -/

theorem full_k6_backtrack_wp (Γ : Env) :
    ∀ args m Q X, k6BacktrackSpec args m Q X → Func.wp Γ full_k6_backtrack_body args m Q X := by
  rintro ⟨kPtr, target_lvl, ⟨⟩⟩ m Q X ⟨L, P, ks, R, hinv, hsync_below, hm, hQ⟩
  have hm_b := L.hmaxV; have hnv := hinv.clauses.nv_le; have hsh := hinv.shapes
  have hmv : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  refine wp_join_state1 (fun st : BitVec 32 => st)
    (fun _ m' => (K6MemA L kPtr ks ⋆ R) m') ?_ ?_
  · intro J0 best_st m0 hm0
    refine wp_while_break_state (β := BitVec 32 × BitVec 32 × K6State)
      (fun bst => (bst.1, bst.2.1, ()))
      (fun bst m' => K6BtLoopInv L ks target_lvl bst.1 bst.2.2 ∧
        (bst.1 = 0#32 ∨ ∃ i < bst.1.toNat, i = bst.1.toNat - 1 ∧
          (bst.2.2.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) ∧
        (K6MemA L kPtr bst.2.2 ⋆ R) m')
      (α := BitVec 32 × BitVec 32 × K6State)
      (fun st => (st.1, st.2.1, ())) (fun st => st.1.toNat)
      (fun st m' => K6BtLoopInv L ks target_lvl st.1 st.2.2 ∧ (K6MemA L kPtr st.2.2 ⋆ R) m')
      ?_ ?_ ?_
    · rintro B ⟨te, _best_st, st⟩ m' ⟨hbt, hexit, hm'⟩
      dsimp only at hbt hexit hm'
      c0_hsteps_nogrp
      let stProp := if te.toNat < st.prop.toNat then (st.putHdr .trl_end te).putHdr .prop te
        else st.putHdr .trl_end te
      refine wp_join0 (fun m'' => (K6MemA L kPtr stProp ⋆ R) m'') ?_ ?_
      · intro Jf m'' hm''
        c0_hsteps!
        obtain ⟨_, hmFin⟩ := k6MemA_to_mem hm
        have hfin := k6BtLoopInv_finish hinv hbt hsync_below hexit
        have heq_st : stProp.putHdr .lvl target_lvl =
            ((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl := by
          dsimp only [stProp]
          by_cases hp : te.toNat < st.prop.toNat <;> simp only [hp, ite_true, ite_false] <;> k6_ext
        rw [heq_st] at hmFin
        rcases hfin with ⟨h1, h2, h3, h4, h5, h6⟩
        have h7 : ∀ i < ks.trl_end.toNat,
            (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
            i < (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat <
                st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl).trl_end.toNat := by
          intro i hi hle
          have hte_eq : (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl).trl_end =
                te := by
            k6_field
          rw [hte_eq]
          rcases Nat.lt_or_ge i te.toNat with hlt | hge
          · exact hlt
          · exfalso; have := hbt.popped_gt i hge hi; omega
        exact hQ _ _ h1 h2 h3 h4 h5 h6 h7 hmFin
      · intro Jf hJf
        have hpr_eq : (st.putHdr .trl_end te).prop = st.prop := by k6_field
        c0_hsteps!
        · apply hJf _; have hp : te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
        · apply hJf _; have hp : ¬ te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
    · rintro B L1 ⟨te, bst, st⟩ m' hB hL ⟨hbt, hm'⟩
      dsimp only at hbt hm'
      c0_hsplit
      · have hpos : 0 < te.toNat := by bv_omega
        have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
        have hte1_mv : (te - 1#32).toNat < szV L := by
          have := hinv.assign.trl_end_le; have := hbt.te_le; unfold szV; bv_omega
        have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
          rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
        let lit := ks.trl[te.toNat - 1]'(by omega)
        have hte_sub1 : (te - (1 : BitVec 32)).toNat = te.toNat - 1 := by bv_omega
        have hlit_get : st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 = lit := by
          rw [hte_sub1, hbt.trl_eq,
            List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
        have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
          have hm1 := k6_mem_trailLits_of_lt hte1_lt htrl_len
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some] at hm1
          exact hinv.assign.trl_lt lit.toNat hm1
        obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hlit_lt
        obtain ⟨hn_eq, _⟩ := k6_bv32_xor1_lt hlit_lt
        have hv_st_mv : ((st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32) >>> (1 : Nat)).toNat <
            szV L := by
          rw [hlit_get, hv_eq]; unfold szV; omega
        have hl_mv2 : lit.toNat < sz2V L := by unfold sz2V; omega
        have hnl_st_mv2 :
            (st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 ^^^ (1 : BitVec 32)).toNat <
            sz2V L := by
          rw [hlit_get, k6_bv32_one, hn_eq]; unfold sz2V litNeg
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        c0_hsplit
        · refine hB (te, bst, st) m' ⟨hbt, Or.inr ⟨te.toNat - 1, Nat.sub_lt hpos Nat.one_pos, rfl,
          ?_⟩, hm'⟩
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
          have hle_raw :
              (st.lvlArr[(st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ target_lvl.toNat := by c0_bound
          rwa [hlit_get] at hle_raw
        · have hstep := k6BtLoopInv_step hinv hbt hpos (by
            have hle_raw :
                ¬ (st.lvlArr[(st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat ≤ target_lvl.toNat := by c0_bound
            rw [hte_sub1, hbt.trl_eq] at hle_raw; exact Nat.lt_of_not_le hle_raw)
          c0_hsteps!
          · have hs2 := hstep.2 (st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 >>> (1 : Nat))
            have hex1 : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
            refine hL (te - 1#32, _, _) _ (by dsimp only; rw [hex1]; omega) ⟨hs2, ?_⟩
            refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
            k6_ext <;> (first | rfl | (simp only [hbt.trl_eq,
              k6_bv32_zero, k6_bv32_one, hex1]; try rfl))
          · have hex1 : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
            refine hL (te - 1#32, bst, _) _ (by dsimp only; rw [hex1]; omega) ⟨hstep.1, ?_⟩
            refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
            k6_ext <;> (first | rfl | (simp only [hbt.trl_eq,
              k6_bv32_zero, k6_bv32_one, hex1]; try rfl))
      · exact hB (te, bst, st) m' ⟨hbt, Or.inl (by bv_omega), hm'⟩
    · intro B L1 hB hL
      exact wp_jump_state (proj := fun st : BitVec 32 × BitVec 32 × K6State => (st.1, st.2.1, ()))
        (ks.trl_end, best_st, ks) rfl (hL (ks.trl_end, best_st, ks) m0 ⟨k6BtLoopInv_init hinv, hm0⟩)
  · intro J0 hJ0
    c0_hsplit
    · have hqs_mv : ks.qsearch.toNat < szV L := by
        have : ks.qsearch.toNat < ks.nv.toNat := by bv_omega
        unfold szV; omega
      c0_hsteps!; exact hJ0 _ m hmA
    · c0_hsteps!; exact hJ0 _ m hmA

/-! ## 3. `7/39`: `full_k6_init_wp` -/

private structure K6InitScalar (L : K6Layout) (nv0 ac0 : BitVec 32) (st : K6State) : Prop where
  nv : st.nv = nv0
  nc : st.nc = 0#32
  lvl : st.lvl = 0#32
  prop : st.prop = 0#32
  trl_end : st.trl_end = 0#32
  unass : st.unass = nv0
  incons : st.incons = 0#32
  alen : st.alen = 0#32
  acap : st.acap = ac0
  nassump : st.nassump = 0#32
  nkl : st.nkl = 0#32
  nana : st.nana = 0#32
  status : st.status = 0#32
  openCnt : st.openCnt = 0#32
  max_v : st.max_v = L.mv32
  max_orig : st.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl : st.max_cl = BitVec.ofNat 32 L.maxCl
  neq : st.neq = 0#32

private theorem K6InitScalar.putArr {L : K6Layout} {nv ac : BitVec 32} {st : K6State}
    (h : K6InitScalar L nv ac st) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    K6InitScalar L nv ac (st.putArr f i v) := by
  cases f <;> exact ⟨h.nv, h.nc, h.lvl, h.prop, h.trl_end, h.unass, h.incons, h.alen, h.acap,
    h.nassump, h.nkl, h.nana, h.status, h.openCnt, h.max_v, h.max_orig, h.max_cl, h.neq⟩

theorem full_k6_init_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, k6InitSpec args m Q X → Func.wp Γ full_k6_init_body args m Q X := by
  rintro ⟨hPtr, nv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_toNat :
      ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat = k6MaxV c.scratch_cap := by
    have hbd : k6MaxV c.scratch_cap ≤ 8192 := by
      by_cases hc : c.scratch_cap < k6MinScr
      · rw [k6MaxV_eq_zero hc]; decide
      · exact (k6MaxV_bounds (Nat.le_of_not_lt hc)).2.1
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · have hcap_lt : c.scratch_cap < k6MinScr := by
      by_cases hc : c.scratch_cap < k6MinScr
      · exact hc
      · exfalso
        have hb := (k6MaxV_bounds (Nat.le_of_not_lt hc)).1
        have h0 : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat = 0 := by bv_omega
        omega
    have hif : c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat := Or.inl hcap_lt
    simp only [hif, ite_true] at hQ
    c0_hsteps!; exact hQ
  · have hcap_ge : k6MinScr ≤ c.scratch_cap := by
      by_cases hc : k6MinScr ≤ c.scratch_cap
      · exact hc
      · exfalso
        have hz := k6MaxV_eq_zero (Nat.lt_of_not_le hc)
        have hne : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat ≠ 0 := by bv_omega
        omega
    c0_hsplit
    · have hlt_nv : k6MaxV c.scratch_cap < nv.toNat := by bv_omega
      have hif : c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat := Or.inr hlt_nv
      simp only [hif, ite_true] at hQ
      c0_hsteps!; exact hQ
    · have hnv_le : nv.toNat ≤ k6MaxV c.scratch_cap := by bv_omega
      have hnot : ¬ (c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat) := by omega
      simp only [hnot, ite_false] at hQ
      let L := k6LayoutOfCap c.scratch_cap hcap_ge c.hscr
      have hL_len : L.scrLen = c.scratch_cap := k6LayoutOfCap_scrLen hcap_ge c.hscr
      have hL_mv : L.maxV = k6MaxV c.scratch_cap := rfl
      have hmv_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
        unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
        rw [hmv32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hmaxV; omega), ← hL_mv]
      let scr := s.scratch.scratch_buf
      have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
      let ks0 := K6State.ofSlab L (scr.drop L.k6Base)
      have hsh0 : ks0.ShapesOk L := K6State.shapesOk_ofSlab_eq (by
        rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega)
      have hmF : (FullK6Frame c L s ⋆ K6Mem L (L.kPtr c.pScratchBuf) ks0 ⋆ R) m := by
        rw [fullMem_eq_k6Frame hscr_len] at hm; exact sep_ac hm
      clear hm
      c0_hsteps_nogrp
      rw [hmv_eq, k6_ptr_base L c.pScratchBuf]
      have hmHdr : (array (t := i32) (L.kPtr c.pScratchBuf) (k6HdrWords ks0) ⋆
          ((K6Tree L (L.kPtr c.pScratchBuf) ks0).rest (k6Path 0) ⋆
            (FullK6Frame c L s ⋆ R))) m :=
        k6Focus_hdr (sep_ac hmF)
      clear hmF
      refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
        (fun p => 32 - p.1.toNat)
        (fun p m' => p.1.toNat ≤ 32 ∧ p.2.length = 32 ∧
          (∀ j < p.1.toNat, p.2[j]? = some 0#32) ∧
          (array (t := i32) (L.kPtr c.pScratchBuf) p.2 ⋆
            ((K6Tree L (L.kPtr c.pScratchBuf) ks0).rest (k6Path 0) ⋆
              (FullK6Frame c L s ⋆ R))) m')
        ?_ ?_
      · intro J hJ
        exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
          (0#32, k6HdrWords ks0) rfl
          (hJ _ m ⟨by simp, k6HdrWords_length hsh0, fun _ hj => by simp at hj, hmHdr⟩)
      · rintro J ⟨i, hdrWs⟩ m' ⟨hi_le, hlen_w, hzeros, hm'⟩ ih
        dsimp only at hi_le hlen_w hzeros hm'
        c0_hsplit
        · have hi_lt : i.toNat < 32 := by bv_omega
          have hi_w : i.toNat < hdrWs.length := by rw [hlen_w]; exact hi_lt
          c0_hsteps!
          have hsw : (BitVec.setWidth 64 i).toNat = i.toNat := by have := i.isLt; simp; omega
          rw [hsw] at hm
          refine ih (i + 1#32, hdrWs.set i.toNat 0#32) _ (by bv_omega)
            ⟨by bv_omega, by simp [hlen_w], ?_, hm⟩
          intro j hj
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          rw [hi1] at hj
          by_cases hji : j = i.toNat
          · subst hji; exact List.getElem?_set_self hi_w
          · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hzeros j (by omega)
        · have hi_eq : i.toNat = 32 := by bv_omega
          have hrep : hdrWs = List.replicate 32 0#32 := by
            apply List.ext_getElem (by simp [hlen_w]); intro j hj _
            have hj32 : j < 32 := by simp [hlen_w] at hj; exact hj
            have hz := hzeros j (by omega)
            rw [List.getElem?_eq_getElem (by omega : j < hdrWs.length)] at hz
            rw [List.getElem_replicate]; exact Option.some.inj hz
          rw [hrep] at hm'
          let ks1 : K6State :=
            { ks0 with nv := 0#32, nc := 0#32, lvl := 0#32, prop := 0#32, trl_end := 0#32,
                       unass := 0#32, incons := 0#32, qfirst := 0#32, qlast := 0#32,
                       qsearch := 0#32, qstamp := 0#32, ticks := 0#32, tick_lim := 0#32,
                       alen := 0#32, acap := 0#32, nassump := 0#32, nkl := 0#32, nana := 0#32,
                       status := 0#32, phase := 0#32, openCnt := 0#32, max_v := 0#32,
                       max_orig := 0#32, max_cl := 0#32, neq := 0#32,
                       hdrTail := List.replicate 7 0#32 }
          have hsh1 : ks1.ShapesOk L := { hsh0 with hdrTail_len := by simp [ks1] }
          let kPtr := L.kPtr c.pScratchBuf
          have hunf : (K6Mem L kPtr ks1 ⋆ (FullK6Frame c L s ⋆ R)) m' := by
            refine k6Unfocus_hdr (ks := ks0) (ks' := ks1) (hdr' := List.replicate 32 0#32) ?_ hm'
            rw [show k6Path 0 = [false, false, false, false] from rfl]
            simp only [K6Mem, K6Tree, SepTree.set, SepTree.eval, k6HdrWords, ks1,
              List.replicate]; congr 1
          have hmA1 : (K6MemA L kPtr ks1 ⋆ (FullK6Frame c L s ⋆ R)) m' :=
            k6Mem_to_amem hsh1 hunf
          clear hm' hunf
          c0_hsteps_nogrp
          let acVal :=
            ((BitVec.ofNat 64 c.scratch_cap -
              ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).setWidth 64)).setWidth
                32
          have e_acap : acVal = BitVec.ofNat 32 L.acap := by
            have hm_bd := L.hmaxV; have hac := L.hacap; unfold dimacsBound at hac
            have hscr_bd : c.scratch_cap < dimacsBound := c.hscr
            unfold dimacsBound at hscr_bd
            have hshl : (L.mv32 <<< (1 : Nat)).toNat = 2 * L.maxV := by
              rw [k6_shl1_toNat]; unfold K6Layout.mv32
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hb_expr : ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).toNat =
                1312 + 40 * L.maxV := by
              have h32 : (32#32 : BitVec 32).toNat = 32 := by decide
              have h38 : (38#32 : BitVec 32).toNat = 38 := by decide
              have hmv : L.mv32.toNat = L.maxV := by
                unfold K6Layout.mv32; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have h1 : (1280#32 + (L.mv32 <<< (1 : Nat))).toNat = 1280 + 2 * L.maxV := by
                rw [BitVec.toNat_add, hshl]
                change (1280 + 2 * L.maxV) % 2 ^ 32 = _
                exact Nat.mod_eq_of_lt (by omega)
              have h2 : (1280#32 + (L.mv32 <<< (1 : Nat)) + 32#32).toNat = 1312 + 2 * L.maxV := by
                rw [BitVec.toNat_add, h1, h32, Nat.mod_eq_of_lt (by omega)]; omega
              have h3 : (38#32 * L.mv32).toNat = 38 * L.maxV := by
                rw [BitVec.toNat_mul, h38, hmv, Nat.mod_eq_of_lt (by omega)]
              rw [BitVec.toNat_add, h2, h3, Nat.mod_eq_of_lt (by omega)]; omega
            have hscr_val : c.scratch_cap = L.k6Base + L.k6Fixed + L.acap := hL_len.symm
            have hbase_fix : L.k6Base + L.k6Fixed = 1312 + 40 * L.maxV := by
              unfold K6Layout.k6Base K6Layout.k6Fixed; omega
            have hsub64 :
                BitVec.ofNat 64 c.scratch_cap -
                  ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).setWidth 64 =
                BitVec.ofNat 64 L.acap := by
              apply BitVec.eq_of_toNat_eq
              have hm_b2 : (1312 + 40 * L.maxV) % 2 ^ 64 = 1312 + 40 * L.maxV :=
                Nat.mod_eq_of_lt (by omega)
              have hm_sc : c.scratch_cap % 2 ^ 64 = c.scratch_cap := Nat.mod_eq_of_lt (by omega)
              have hm_ac : L.acap % 2 ^ 64 = L.acap := Nat.mod_eq_of_lt (by omega)
              rw [BitVec.toNat_sub, BitVec.toNat_setWidth, hb_expr, BitVec.toNat_ofNat,
                BitVec.toNat_ofNat, hm_b2, hm_sc, hm_ac]
              have hsplit : 2 ^ 64 - (1312 + 40 * L.maxV) + c.scratch_cap = 2 ^ 64 + L.acap := by
                omega
              rw [hsplit]; omega
            dsimp only [acVal]; rw [hsub64]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have e_max_orig : L.mv32 * 3#32 = BitVec.ofNat 32 L.maxOrig := by
            have hm_bd := L.hmaxV; unfold K6Layout.mv32 K6Layout.maxOrig
            apply BitVec.eq_of_toNat_eq; bv_omega
          have e_max_cl : L.mv32 * 4#32 = BitVec.ofNat 32 L.maxCl := by
            have hm_bd := L.hmaxV; unfold K6Layout.mv32 K6Layout.maxCl
            apply BitVec.eq_of_toNat_eq; bv_omega
          let ksH0 := ((((((ks1.putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim 16384#32).putHdr
            .max_v L.mv32).putHdr .max_orig (BitVec.ofNat 32 L.maxOrig)).putHdr .max_cl
              (BitVec.ofNat 32 L.maxCl)).putHdr .acap acVal
          let ksH := if nv == 0#32 then
              ((ksH0.putHdr .qfirst 0xFFFFFFFF#32).putHdr .qlast 0xFFFFFFFF#32).putHdr .qsearch
                0xFFFFFFFF#32
            else
              (((ksH0.putHdr .qfirst 0#32).putHdr .qlast (nv - 1#32)).putHdr
                .qsearch (nv - 1#32)).putHdr .qstamp nv
          have hshH : ksH.ShapesOk L := by
            have hh0 := ((((((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim
              16384#32).putHdr .max_v L.mv32).putHdr .max_orig
                (BitVec.ofNat 32 L.maxOrig)).putHdr .max_cl (BitVec.ofNat 32 L.maxCl)).putHdr
                  .acap acVal
            dsimp only [ksH]; split
            · exact ((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _
            · exact (((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _).putHdr .qstamp _
          have e_acapH : ksH.acap = BitVec.ofNat 32 L.acap := by
            have hh : ksH.acap = acVal := by
              dsimp only [ksH]; split <;> dsimp only [ksH0] <;> k6_field
            exact hh.trans e_acap
          refine wp_join0 (fun m2 => (K6MemA L kPtr ksH ⋆ (FullK6Frame c L s ⋆ R)) m2) ?_ ?_
          · intro J2 m2 hm2
            c0_hsteps_nogrp
            have hInitH : K6InitScalar L nv ksH.acap ksH := by
              dsimp only [ksH]; split <;> dsimp only [ksH0, ks1] <;>
                exact ⟨by k6_field, by k6_field, by k6_field, by k6_field, by k6_field,
                  by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field,
                  by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field,
                  by k6_field⟩
            refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
              (fun p => nv.toNat - p.1.toNat)
              (fun p m3 => p.1.toNat ≤ nv.toNat ∧ p.2.ShapesOk L ∧
                K6InitScalar L nv ksH.acap p.2 ∧
                (∀ v < p.1.toNat, p.2.lvlArr[v]? = some 0#32 ∧ p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧
                  p.2.flags[v]? = some 0#32) ∧
                (K6MemA L kPtr p.2 ⋆ (FullK6Frame c L s ⋆ R)) m3)
              ?_ ?_
            · intro J3 hJ3
              exact wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                (0#32, ksH) rfl (hJ3 _ m2 ⟨by simp, hshH, hInitH, fun _ h => by simp at h, hm2⟩)
            · rintro J3 ⟨j, st⟩ m3 ⟨hj_le, hsh_st, hsc_st, hvars_st, hm3⟩ ih3
              dsimp only at hj_le hsh_st hsc_st hvars_st hm3
              c0_hsplit
              · have hj_lt : j.toNat < nv.toNat := by bv_omega
                have hj_mv : j.toNat < szV L := by unfold szV; omega
                c0_hsteps!
                all_goals
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  refine ih3 (j + 1#32, _) _ (by dsimp only; rw [hj1]; omega)
                    ⟨by dsimp only; rw [hj1]; omega, ?_, ?_, ?_, hm⟩
                  · exact (((((hsh_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _
                      _).putArr .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                  · exact (((((hsc_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _
                      _).putArr .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                  · intro v hv; rw [hj1] at hv
                    by_cases hvj : v = j.toNat
                    · subst hvj
                      exact ⟨by
                          k6_field
                          rw [List.getElem?_set_self (by rw [hsh_st.lvlArr_len]; exact hj_mv)]; rfl,
                        by
                          k6_field
                          rw [List.getElem?_set_self (by rw [hsh_st.rsn_len]; exact hj_mv)]; rfl,
                        by
                          k6_field
                          rw [List.getElem?_set_self (by rw [hsh_st.flags_len]; exact hj_mv)]; rfl⟩
                    · have hvv := hvars_st v (by omega)
                      exact ⟨by k6_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.1,
                        by k6_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.1,
                        by k6_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.2⟩
              · have hj_eq : j.toNat = nv.toNat := by bv_omega
                rw [hj_eq] at hvars_st
                c0_hsteps_nogrp
                have hnl_eq : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := by
                  rw [k6_shl1_toNat]; have := L.hmaxV; omega
                refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                  (fun p => 2 * nv.toNat - p.1.toNat)
                  (fun p m4 => p.1.toNat ≤ 2 * nv.toNat ∧ p.2.ShapesOk L ∧
                    K6InitScalar L nv ksH.acap p.2 ∧
                    (∀ v < nv.toNat, p.2.lvlArr[v]? = some 0#32 ∧
                      p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧ p.2.flags[v]? = some 0#32) ∧
                    (∀ l < p.1.toNat, p.2.vals[l]? = some 0#32 ∧
                      p.2.whead[l]? = some 0xFFFFFFFF#32) ∧
                    (K6MemA L kPtr p.2 ⋆ (FullK6Frame c L s ⋆ R)) m4)
                  ?_ ?_
                · intro J4 hJ4
                  exact wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                    (0#32, st) rfl (hJ4 _ m3 ⟨by simp, hsh_st, hsc_st, hvars_st, fun _ h => by
                      simp at h, hm3⟩)
                · rintro J4 ⟨k, st4⟩ m4 ⟨hk_le, hsh4, hsc4, hvars4, hlits4, hm4⟩ ih4
                  dsimp only at hk_le hsh4 hsc4 hvars4 hlits4 hm4
                  c0_hsplit
                  · have hk_lt : k.toNat < 2 * nv.toNat := by rw [← hnl_eq]; bv_omega
                    have hk_mv2 : k.toNat < sz2V L := by unfold sz2V; omega
                    c0_hsteps!
                    let st4' := (st4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32
                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                    refine ih4 (k + 1#32, st4') _ (by dsimp only; rw [hk1]; omega)
                      ⟨by dsimp only; rw [hk1]; omega,
                       (hsh4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32,
                       (hsc4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32,
                       fun v hv => let hvv := hvars4 v hv
                       ⟨by k6_field; exact hvv.1, by k6_field; exact hvv.2.1,
                         by k6_field; exact hvv.2.2⟩,
                       ?_, hm⟩
                    intro l hl; rw [hk1] at hl
                    by_cases hlk : l = k.toNat
                    · subst hlk
                      exact ⟨by
                          dsimp only [st4']; k6_field
                          rw [List.getElem?_set_self (by rw [hsh4.vals_len]; exact hk_mv2)],
                        by
                          dsimp only [st4']; k6_field
                          rw [List.getElem?_set_self (by rw [hsh4.whead_len]; exact hk_mv2)]⟩
                    · have hll := hlits4 l (by omega)
                      exact ⟨by
                          dsimp only [st4']; k6_field
                          rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.1,
                        by
                          dsimp only [st4']; k6_field
                          rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.2⟩
                  · have hk_eq : k.toNat = 2 * nv.toNat := by
                      have hnl : ¬ k.toNat < (nv <<< (1 : Nat)).toNat := ‹_›; rw [hnl_eq] at hnl
                      omega
                    rw [hk_eq] at hlits4
                    c0_hsteps!
                    have hfin := k6Init_finish_inv hsh4 hnv_le hsc4.nv hsc4.nc
                      hsc4.lvl hsc4.prop hsc4.trl_end hsc4.unass (hsc4.acap.trans e_acapH)
                      hsc4.max_v hsc4.max_orig hsc4.max_cl hsc4.alen hsc4.incons hsc4.nassump
                      hsc4.nkl hsc4.nana hvars4 hlits4
                    obtain ⟨_, hm4'⟩ := k6MemA_to_mem hm4
                    have hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length := by
                      change L.k6Base ≤ scr.length; rw [hscr_len]; unfold K6Layout.scrLen; omega
                    have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := st4)
                      (R := R) hkb_le hsh4 (sep_ac hm4')
                    let scr' := s.scratch.scratch_buf.take L.k6Base ++ st4.toSlab
                    have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
                      List.length_take_of_le hkb_le
                    have hscr'_len : scr'.length = c.scratch_cap := by
                      simp only [scr', List.length_append, htk_len, K6State.toSlab_length hsh4]
                      rw [← hL_len]; unfold K6Layout.scrLen; omega
                    have hpre : ∀ x < L.k6Base, scr'[x]? = s.scratch.scratch_buf[x]? :=
                      fun x hx => by
                        rw [List.getElem?_append_left (by rw [htk_len]; exact hx),
                          List.getElem?_take_of_lt hx]
                    have hof : k6StateOfScratch L scr' = st4 := by
                      unfold k6StateOfScratch
                      rw [k6_slab_drop_exact _ st4.toSlab htk_len]
                      exact K6State.ofSlab_toSlab hsh4
                    exact hQ L scr' m4 hL_len rfl
                      (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
                      (fun P => by rw [hof]; exact hfin.1 P)
                      (by rw [hof]; exact hfin.2)
                      (by rw [hof]; exact hsc4.nv) (by rw [hof]; exact hsc4.nc)
                      (by rw [hof]; exact hsc4.lvl) (by rw [hof]; exact hsc4.prop)
                      (by rw [hof]; exact hsc4.trl_end) (by rw [hof]; exact hsc4.unass)
                      (by rw [hof]; exact hsc4.incons) (by rw [hof]; exact hsc4.nassump)
                      (by rw [hof]; exact hsc4.status) (by rw [hof]; exact hsc4.openCnt)
                      (by rw [hof]; exact hsc4.neq) hmJ
          · intro J2 hJ2
            c0_hsteps!
            · refine hJ2 _ (Eq.mp (congrArg (fun x =>
                (K6MemA L kPtr x ⋆ (FullK6Frame c L s ⋆ R)) _) ?_) hm)
              dsimp only [ksH, ksH0]
              simp only [show nv = 0#32 from by bv_omega, beq_self_eq_true, ite_true]
              k6_ext <;> first | exact e_max_orig | exact e_max_cl
            · refine hJ2 _ (Eq.mp (congrArg (fun x =>
                (K6MemA L kPtr x ⋆ (FullK6Frame c L s ⋆ R)) _) ?_) hm)
              dsimp only [ksH, ksH0]
              simp only [show (nv == 0#32) = false from by
                apply Bool.eq_false_iff.mpr; intro h; exact absurd (beq_iff_eq.mp h) (by bv_omega),
                Bool.false_eq_true, ite_false]
              k6_ext <;> first | exact e_max_orig | exact e_max_cl

/-! ## 4. `8/39`: `full_k6_add_clause_wp` -/

theorem full_k6_add_clause_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec) :
    ∀ args m Q X, k6AddClauseSpec args m Q X →
      Func.wp Γ full_k6_add_clause_body args m Q X := by
  rintro ⟨hPtr, litsPtr, sz, ⟨⟩⟩ m Q X ⟨c, s, P, L, scr, xs, R, rfl, hlen, hscr_buf, hL_len,
    hL_mv, hinv, hsync, hlvl0, hsz_xs, hsz_max, hxlits, hent, hm, hQ⟩
  let ks := k6StateOfScratch L scr
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hsh : ks.ShapesOk L := hinv.shapes
  have hnv : ks.nv.toNat ≤ L.maxV := hinv.clauses.nv_le
  have hmv_eq_ks : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hal : ks.alen.toNat ≤ L.acap := hinv.clauses.alen_le
  have hca_eq : ks.acap.toNat = L.acap := by
    have := L.hacap; unfold dimacsBound at this
    rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmc_eq : ks.max_cl.toNat = L.maxCl := by
    have := L.hmaxV
    rw [hinv.clauses.max_cl_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold K6Layout.maxCl; omega)]
  have hscr_len : scr.length = L.scrLen :=
    (hscr_buf ▸ hlen.scratch_ok.scratch_buf_len).trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  let kPtr := L.kPtr c.pScratchBuf
  have hmA : (K6MemA L kPtr ks ⋆ (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (array (t := i32) litsPtr xs ⋆ (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R))))
        m :=
    fullAddClause6_mem_to_ka hscr_len hsh rfl hm
  clear hm
  have hreorg : ∀ {ks' : K6State} {m' : Mem 64} (hsh' : ks'.ShapesOk L),
      (K6MemA L kPtr ks' ⋆ (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m' →
      let scr' := scr.take L.k6Base ++ ks'.toSlab
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap ∧ (∀ i < L.k6Base, scr'[i]? = scr[i]?) ∧
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) litsPtr xs ⋆ R) m' := by
    intro ks' m' hsh' hm' scr' s'
    have htk : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkb_le
    have hlen' : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk, K6State.toSlab_length hsh', ← hL_len]
      unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
    have hpre : ∀ i < L.k6Base, scr'[i]? = scr[i]? := fun i hi => by
      rw [List.getElem?_append_left (by rw [htk]; exact hi), List.getElem?_take_of_lt hi]
    exact ⟨hlen', hpre, fullAddClause6_ka_to_mem hkb_le hsh' hm'⟩
  have hscr_orig : scr.take L.k6Base ++ ks.toSlab = scr := by
    have hle : L.k6Fixed ≤ (scr.drop L.k6Base).length := by
      rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega
    dsimp only [ks, k6StateOfScratch]
    rw [K6State.toSlab_ofSlab hle, List.take_append_drop]
  have hof_slab : ∀ {ks' : K6State} (hsh' : ks'.ShapesOk L),
      k6StateOfScratch L (scr.take L.k6Base ++ ks'.toSlab) = ks' := fun {ks'} hsh' => by
    have htk : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkb_le
    unfold k6StateOfScratch
    rw [k6_slab_drop_exact _ ks'.toSlab htk]; exact K6State.ofSlab_toSlab hsh'
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · exfalso
    have hmv0 : L.mv32 = 0#32 := by
      rw [← hmv32_eq]
      exact (‹(BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32›)
    have h0 := congrArg BitVec.toNat hmv0
    change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    iterate 7 c0_hstep
    rw [k6_ptr_base L c.pScratchBuf]
    c0_hsplit
    · -- sz == 0
      have hsz0 : sz = 0#32 := ‹_›
      have hunsat : ∀ β, ¬ P β := by
        rw [hsz0] at hent; simp at hent; exact SemEntails.unsat_of_nil hent
      c0_hsteps!
      have hinv' := k6SetIncons_preserves_inv hinv hunsat
      have hmF := hreorg hinv'.shapes hm
      exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
        (by rw [hof_slab hinv'.shapes]; exact hsync)
        (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
        (by rw [hof_slab hinv'.shapes]; k6_field)
        (by rw [hof_slab hinv'.shapes]; k6_field)
        (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; k6_field)
        (fun h => by cases h)
        (fun h2 => by rw [hsz0] at h2; simp at h2)
        (fun M _ hM htr => by
          rw [hof_slab hinv'.shapes]
          exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
    · c0_hsplit
      · -- sz == 1
        have hsz1 : sz = 1#32 := ‹_›
        have h0_xs : 0 < xs.length := by rw [hsz1] at hsz_xs; simp at hsz_xs; omega
        have hu_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
          have h := hxlits 0 (by rw [hsz1]; decide)
          rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
        have hu_mv2 : (xs[0]'h0_xs).toNat < sz2V L := by unfold sz2V; omega
        have hent1 : SemEntails P [(xs[0]'h0_xs).toNat] := by
          have htk : (xs.take sz.toNat).map BitVec.toNat = [(xs[0]'h0_xs).toNat] := by
            rw [hsz1]; cases xs with | nil => simp at h0_xs | cons x _ => rfl
          rwa [htk] at hent
        c0_hsteps_nogrp
        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · -- uv == 2u => incons = 1u
          have hfals : ks.vals[(xs[0]'h0_xs).toNat]? = some 2#32 := by
            have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 2#32 := by simpa using ‹_›
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
              Option.getD_some] at hv_eq
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
          have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent1 fun x hx => by
            simp at hx; subst hx; exact (k6_falsified_lvl0_entails hinv hlvl0 hu_lt hfals).2
          c0_hsteps!
          have hinv' := k6SetIncons_preserves_inv hinv hunsat
          have hmF := hreorg hinv'.shapes hm
          exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
            (by rw [hof_slab hinv'.shapes]; exact hsync)
            (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
            (by rw [hof_slab hinv'.shapes]; k6_field)
            (by rw [hof_slab hinv'.shapes]; k6_field)
            (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; k6_field)
            (fun h => by cases h)
            (fun h2 => by rw [hsz1] at h2; simp at h2)
            (fun M _ hM htr => by
              rw [hof_slab hinv'.shapes]
              exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
        · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · -- uv == 0u => assign(k, ul, 0xFFFFFFFFu)
            have hun0 : ks.vals[(xs[0]'h0_xs).toNat]? = some 0#32 := by
              have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 0#32 := by simpa using ‹_›
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
                Option.getD_some] at hv_eq
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
            have hte_lt := k6_trl_end_lt_of_unassigned hsh hnv hinv.assign hu_lt (by simp [hun0])
            obtain ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hinv hsync hu_lt hun0
              (fun _ => hent1) (fun hpos => by rw [hlvl0] at hpos; simp at hpos) (Or.inl rfl)
            k6_call hAssign
            refine ⟨L, ks, _, hsh, hmv_eq_ks,
              (by change (xs[0]'h0_xs).toNat < 2 * L.maxV; omega),
              (by omega), (k6MemA_to_mem hmA).2, fun m' hm' => ?_⟩
            c0_hsteps!
            have hmF := hreorg hinv'.shapes (k6Mem_to_amem hinv'.shapes hm')
            exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
              (by rw [hof_slab hinv'.shapes]; exact hsync')
              (by rw [hof_slab hinv'.shapes]; exact hlvl0)
              (by rw [hof_slab hinv'.shapes]; rfl) (by rw [hof_slab hinv'.shapes]; rfl)
              (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
              (fun h => by cases h)
              (fun h2 => by rw [hsz1] at h2; simp at h2)
              (fun M hxsM hM htr => by
                rw [hof_slab hinv'.shapes]
                refine ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, fun l hl => ?_⟩
                unfold k6TrailLits k6AssignStep at hl
                dsimp only [K6State.putHdr, K6State.putArr] at hl
                have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by
                  have := L.hmaxV; bv_omega
                rw [hte1] at hl
                rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
                obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
                simp only [List.length_take, List.length_set] at hj
                have hj_lt : j < ks.trl_end.toNat + 1 := by omega
                simp only [List.getElem_take]
                by_cases hj_old : j < ks.trl_end.toNat
                · rw [List.getElem_set_ne (Nat.ne_of_gt hj_old)]
                  refine htr _ (List.mem_map.mpr ⟨(ks.trl.take ks.trl_end.toNat)[j]'(by
                    rw [List.length_take, hsh.trl_len, Nat.min_eq_left (by omega)]
                    exact hj_old), List.getElem_mem _, by simp only [List.getElem_take]; rfl⟩)
                · have hj_eq : j = ks.trl_end.toNat := by omega
                  subst hj_eq
                  rw [List.getElem_set_self]
                  have hx0 := hxsM 0 (by rw [hsz1]; decide)
                  rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hx0) hmF.2.2
          · -- uv == 1u => noop
            c0_hsteps!
            have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
            exact hQ true scr m (hscr_len.trans hL_len) (fun _ _ => rfl) hinv hsync hlvl0
              rfl rfl rfl (fun _ => rfl) (fun h2 => by rw [hsz1] at h2; simp at h2)
              (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
      · -- sz >= 2
        have hsz2 : 2 ≤ sz.toNat := by
          have hne0 : sz ≠ 0#32 := ‹_›; have hne1 : sz ≠ 1#32 := ‹_›
          have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
          have h1 : sz.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h); omega
        c0_hsplit
        · -- nc >= max_cl => false
          c0_hsteps!
          have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
          exact hQ false scr m (hscr_len.trans hL_len) (fun _ _ => rfl) hinv hsync hlvl0
            rfl rfl rfl (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
            (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
        · c0_hsplit
          · -- off + sz > acap => false
            c0_hsteps!
            have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
            exact hQ false scr m (hscr_len.trans hL_len) (fun _ _ => rfl) hinv hsync hlvl0
              rfl rfl rfl (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
              (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
          · have hnc_lt : ks.nc.toNat < L.maxCl := by rw [← hmc_eq]; bv_omega
            have hoff_fit : ks.alen.toNat + sz.toNat ≤ L.acap := by
              have hcap_lt : ks.acap.toNat < 2 ^ 28 := by
                rw [hca_eq]; unfold dimacsBound at hac_b; omega
              have hal_ks : ks.alen.toNat ≤ ks.acap.toNat := by rw [hca_eq]; exact hal
              rw [← hca_eq]; bv_omega
            obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop,
                Rfr = (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                  (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)) := ⟨_, rfl⟩
            have hmA_r : (K6MemA L kPtr ks ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) m := by
              rw [hRfr]; exact sep_ac hmA
            c0_hsteps_nogrp
            refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
              (fun p => sz.toNat - p.1.toNat)
              (fun p m' => p.1.toNat ≤ sz.toNat ∧ p.2.length = L.acap ∧
                (∀ j < ks.alen.toNat, p.2[j]? = ks.arena[j]?) ∧
                (∀ j < p.1.toNat, p.2[ks.alen.toNat + j]? = xs[j]?) ∧
                (K6MemA L kPtr { ks with arena := p.2 } ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) m')
              ?_ ?_
            · intro J hJ
              exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                (0#32, ks.arena) rfl
                (hJ _ m ⟨by simp, hsh.arena_len, fun _ _ => rfl, fun _ hj => by simp at hj, hmA_r⟩)
            · rintro J ⟨i, ar⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ ih
              dsimp only at hi_le har_len har_old har_new hm' ⊢
              obtain ⟨st, hst⟩ : ∃ x : K6State, x = { ks with arena := ar } := ⟨_, rfl⟩
              rw [← hst] at hm'
              c0_hsplit
              · have hi_lt : i.toNat < sz.toNat := by bv_omega
                have hi_xs : i.toNat < xs.length := by omega
                have hoff_i_ar : (ks.alen + i).toNat < szAr L := by
                  unfold szAr dimacsBound at *; bv_omega
                c0_hsteps!
                have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                have hoi : (ks.alen + i).toNat = ks.alen.toNat + i.toNat := by
                  unfold szAr dimacsBound at *; bv_omega
                rw [hoi] at hm
                refine ih (i + 1#32, ar.set (ks.alen.toNat + i.toNat) (xs[i.toNat]'hi_xs)) _
                  (by dsimp only; rw [hi1]; omega)
                  ⟨by dsimp only; rw [hi1]; omega, by simp [har_len],
                   fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact har_old j hj, ?_, ?_⟩
                · intro j hj; rw [hi1] at hj
                  by_cases hji : j = i.toNat
                  · subst hji; rw [List.getElem?_set_self (by rw [har_len]; omega),
                      List.getElem?_eq_getElem hi_xs]
                  · rw [List.getElem?_set_ne (by omega)]; exact har_new j (by omega)
                · refine Eq.mp (congrArg (fun x =>
                    (K6MemA L kPtr x ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) _) ?_) hm
                  rw [hst]; k6_ext
              · have hi_eq : i.toNat = sz.toNat := by bv_omega
                rw [hi_eq] at har_new
                have h0_xs : 0 < xs.length := by omega
                have h1_xs : 1 < xs.length := by omega
                have hl0_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
                  have h := hxlits 0 (by omega)
                  rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
                have hl1_lt : (xs[1]'h1_xs).toNat < 2 * ks.nv.toNat := by
                  have h := hxlits 1 (by omega)
                  rwa [List.getElem?_eq_getElem h1_xs, Option.getD_some] at h
                have hpres := k6AddClause_ge2_preserves hinv hsync hnc_lt hsz2 hsz_max hsz_xs
                  hoff_fit har_len har_old har_new hxlits hent
                c0_hsteps_nogrp
                obtain ⟨hshM, hmM⟩ := k6MemA_to_mem hm
                k6_call hWatch
                refine ⟨L, _, _, hshM, (by rw [hst]; k6_field; exact hmv_eq_ks), hnc_lt,
                  (by change (xs[0]'h0_xs).toNat < 2 * L.maxV; omega),
                  (by change (xs[1]'h1_xs).toNat < 2 * L.maxV; omega),
                  hmM, fun m2 hm2 => ?_⟩
                c0_hsteps!
                have hsh' := hpres.1.shapes
                have hm2_eq : (K6Mem L kPtr
                    (k6WatchStep ((((({ ks with arena := ar } : K6State).putHdr .alen
                      (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat
                      sz).putHdr .nc (ks.nc + 1#32)) ks.nc (xs[0]'h0_xs) (xs[1]'h1_xs)) ⋆
                    (array (t := i32) litsPtr xs ⋆ Rfr)) m2 := by
                  rw [hst] at hm2; exact hm2
                have hmF := hreorg hsh' (by
                  have hA := k6Mem_to_amem hsh' hm2_eq; rw [hRfr] at hA; exact sep_ac hA)
                exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hsh']; exact hpres.1)
                  (by rw [hof_slab hsh']; exact hpres.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.1.trans hlvl0)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                  (by unfold k6AssumpLitsS k6AssumpLits
                      rw [hof_slab hsh', hpres.2.2.2.2.1, hpres.2.2.2.2.2.1])
                  (fun h => by cases h)
                  (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; dsimp only [k6WatchStep, k6WatchStep0]; k6_field,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1⟩)
                  (fun M hxsM hM htr => by
                    rw [hof_slab hsh']
                    refine ⟨hpres.2.2.2.2.2.2.2.2.2 M hxsM hM, ?_⟩
                    unfold k6TrailLits; dsimp only [k6WatchStep, k6WatchStep0]; k6_field
                    exact htr) hmF.2.2

/-! ## 5. `9/39`: `full_k6_flip_wp` -/

theorem full_k6_flip_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec) :
    ∀ args m Q X, k6FlipSpec args m Q X → Func.wp Γ full_k6_flip_body args m Q X := by
  rintro ⟨hPtr, lit, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hinv, hlit_lt, hm, hQ⟩
  let scr := s.scratch.scratch_buf
  let ks := k6StateOfScratch L scr
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hmv_eq_ks : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  let kPtr := L.kPtr c.pScratchBuf
  have hmA0 : (K6MemA L kPtr ks ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_len] at hm
    exact k6Mem_to_amem hsh (sep_ac hm)
  clear hm
  obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
  have hfinish : ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump → ks'.assump = ks.assump →
      ks'.neq = ks.neq → (K6MemA L kPtr ks' ⋆ Rfr) m' → Q (ok, ()) m' := by
    intro ok ks' m' hinv' hnv' hna' hass' hneq' hm'
    rw [hRfr] at hm'
    obtain ⟨_, hm0⟩ := k6MemA_to_mem hm'
    have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := ks') (R := R)
      hkb_le hinv'.shapes (sep_ac hm0)
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
      List.length_take_of_le hkb_le
    have hscr'_len : scr'.length = c.scratch_cap := by
      dsimp only [scr']
      rw [List.length_append, htk_len, K6State.toSlab_length hinv'.shapes, ← hL_len]
      unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
    have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
      rw [List.getElem?_append_left (by rw [htk_len]; exact hi), List.getElem?_take_of_lt hi]
    have hof : k6StateOfScratch L scr' = ks' := by
      unfold k6StateOfScratch
      rw [k6_slab_drop_exact _ ks'.toSlab htk_len]
      exact K6State.ofSlab_toSlab hinv'.shapes
    exact hQ ok scr' m' (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
      (by rw [hof]; exact hinv') (by rw [hof]; exact hnv') (by rw [hof]; exact hna')
      (by unfold k6AssumpLitsS k6AssumpLits; rw [hof, hna', hass'])
      (by rw [hof]; exact hneq') hmJ
  obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hlit_lt
  have hlit_mv2 : lit.toNat < sz2V L := by unfold sz2V; omega
  have hv_mv : (lit >>> (1 : Nat)).toNat < szV L := by unfold szV; omega
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · exfalso
    have hmv0 : L.mv32 = 0#32 := by
      rw [← hmv32_eq]
      exact (‹(BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32›)
    have h0 := congrArg BitVec.toNat hmv0
    change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    iterate 7 c0_hstep
    rw [k6_ptr_base L c.pScratchBuf]
    have hmA : (K6MemA L kPtr ks ⋆ Rfr) m := by rw [hRfr]; exact hmA0
    clear hmA0
    c0_hsplit
    · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl rfl hmA
    · c0_hsplit
      · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl rfl hmA
      · c0_hsplit
        · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl rfl hmA
        · c0_hsplit
          · c0_hsteps!; exact hfinish false ks m hinv rfl rfl rfl rfl hmA
          · have hval1 : ks.vals[lit.toNat]? = some 1#32 := by
              have hc : ks.vals[lit.toNat]?.getD 0#32 = 1#32 := ‹_›
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_mv2),
                Option.getD_some] at hc
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_mv2), hc]
            have hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := ‹_›
            obtain ⟨ch0, hwc0⟩ := K6WChainCursor.init hsh hnv hinv.watches hlit_lt
            c0_hsteps_nogrp
            refine wp_while_break_state
              (projBrk :=
                fun bst : BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × Bool × K6State =>
                (bst.2.1, bst.1, bst.2.2.1, bst.2.2.2.1, bst.2.2.2.2.1, ()))
              (fun bst m' => K6Inv L P bst.2.2.2.2.2 ∧
                bst.2.2.2.2.2.nv = ks.nv ∧ bst.2.2.2.2.2.nassump = ks.nassump ∧
                bst.2.2.2.2.2.assump = ks.assump ∧ bst.2.2.2.2.2.vals = ks.vals ∧
                bst.2.2.2.2.2.lvlArr = ks.lvlArr ∧ bst.2.2.2.2.2.neq = ks.neq ∧
                bst.2.2.2.2.2.max_v = L.mv32 ∧
                (K6MemA L kPtr bst.2.2.2.2.2 ⋆ Rfr) m')
              (α :=
                BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × List Nat × List Nat ×
                  K6State × List (List Nat))
              (fun st => (st.2.1, st.1, st.2.2.1, st.2.2.2.1, ()))
              (fun st => st.2.2.2.2.2.1.length)
              (fun st m' =>
                K6WChainCursor st.2.2.2.2.2.2.1 lit.toNat st.2.2.2.2.2.2.2
                  st.2.2.2.2.1 st.2.2.2.2.2.1 st.1 st.2.1 ∧
                K6Inv L P st.2.2.2.2.2.2.1 ∧
                st.2.2.2.2.2.2.1.nv = ks.nv ∧ st.2.2.2.2.2.2.1.nassump = ks.nassump ∧
                st.2.2.2.2.2.2.1.assump = ks.assump ∧ st.2.2.2.2.2.2.1.vals = ks.vals ∧
                st.2.2.2.2.2.2.1.lvlArr = ks.lvlArr ∧ st.2.2.2.2.2.2.1.neq = ks.neq ∧
                st.2.2.2.2.2.2.1.max_v = L.mv32 ∧
                (K6MemA L kPtr st.2.2.2.2.2.2.1 ⋆ Rfr) m') ?_ ?_ ?_
            · rintro B ⟨_, _, visits, ticks, ok, ksB⟩ m'
                ⟨hinvB, b_nv, b_na, b_as, b_va, b_la, b_nq, _b_mv, hmB⟩
              dsimp only at hinvB b_nv b_na b_as b_va b_la b_nq hmB
              c0_hsteps_nogrp
              k6_call hAddTicks
              refine ⟨L, ksB, Rfr, hinvB.shapes, (k6MemA_to_mem hmB).2, fun tk' m2 hm2 => ?_⟩
              have hinvT := k6AddTicks_preserves_inv hinvB tk'
              have hmAT := k6Mem_to_amem hinvT.shapes hm2
              c0_hsplit
              · obtain ⟨_, hn_lt⟩ := k6_bv32_xor1_lt hlit_lt
                have hnl_mv2 : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; omega
                have hlit_ltT : lit.toNat < 2 * (ksB.putHdr .ticks tk').nv.toNat := by
                  k6_field; rw [b_nv]; exact hlit_lt
                have hvalT : (ksB.putHdr .ticks tk').vals[lit.toNat]? = some 1#32 := by
                  k6_field; rw [b_va]; exact hval1
                have hlvlT : (ksB.putHdr .ticks tk').lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠
                    0#32 := by
                  k6_field; rw [b_la]; exact hlvl_nz
                have hfin := k6FlipFinish_preserves hinvT hlit_ltT hvalT hlvlT
                c0_hsteps!
                exact hfinish true _ _ hfin (by k6_field; exact b_nv)
                  (by k6_field; exact b_na) (by k6_field; exact b_as) (by k6_field; exact b_nq)
                  ‹_›
              · c0_hsteps!
                exact hfinish false _ m2 hinvT (by k6_field; exact b_nv)
                  (by k6_field; exact b_na) (by k6_field; exact b_as) (by k6_field; exact b_nq)
                  hmAT
            · rintro B L1 ⟨prev, w, visits, ticks, done, todo, ksW, chW⟩ m'
                hB ih ⟨hwc, hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
              dsimp only at hwc hinvW w_nv w_na w_as w_va w_la w_nq w_mv hmW ⊢
              have hshW := hinvW.shapes; have hclW := hinvW.clauses
              have hnvW := hclW.nv_le; have hncW := hclW.nc_le
              have hlit_ltW : lit.toNat < 2 * ksW.nv.toNat := w_nv ▸ hlit_lt
              c0_hsplit
              · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
                obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_mc2, hw_tn, hw_div2, hw_mod2,
                    hsz_ge, har_slot, hbv_nv, hbv_mem, hbin_iff, hbin_eq, _⟩ :=
                  hwc.step_unfold hncW hlit_ltW hw_ne
                have hw0_2cl : w0 < sz2Cl L := by unfold sz2Cl; exact hw0_mc2
                have hw0_bv2 : (BitVec.ofNat 32 w0).toNat < sz2Cl L := by rw [hw_tn]; exact hw0_2cl
                have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
                have hcid_cl : w0 / 2 < szCl L := by
                  unfold szCl K6Layout.maxCl at *; omega
                have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
                have hbv_mv2 : ((ksW.wblit[w0]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < sz2V L := by
                  unfold sz2V; omega
                have hbv_mv2' :
                    ((ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat <
                      sz2V L := by
                  rw [hw_tn]; exact hbv_mv2
                c0_hsplit
                · -- Binary fast-path `(wb & K6_BIN_FLAG) != 0`
                  c0_hsplit
                  · c0_hsteps!
                    exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks, false, ksW) m'
                      ⟨hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                  · c0_hsplit
                    · c0_hsteps!
                      exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks, false, ksW) m'
                        ⟨hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                    · -- keep binary watch
                      have hskip := k6WatchSkip_cursor hshW hwc hw0_len
                      c0_hsteps!; rw [hw_tn]
                      exact ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                          ticks, done ++ [w0], todo', ksW, chW) _ (by simp)
                        ⟨hskip, hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                · -- Non-binary `(wb & K6_BIN_FLAG) == 0`
                  have hnonbin : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
                    rw [← hw_tn]; bv_omega
                  have hsz_ne2 : k6ClauseSize ksW (w0 / 2) ≠ 2 := fun h2 =>
                    absurd (hbin_iff.mpr h2) (by rw [hnonbin]; simp)
                  refine LeanQbe.T.wp_unroll_group fun Jnk hJnk => ?_
                  have hnk : Jnk () m' := by
                    refine hJnk () m' ?_
                    have har_ok : ∀ idx < k6ClauseSize ksW (w0 / 2),
                        k6ClauseOff ksW (w0 / 2) + idx < L.acap ∧
                        (ksW.arena[k6ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat <
                          2 * ksW.nv.toNat := by
                      intro idx hidx
                      have hcap : k6ClauseOff ksW (w0 / 2) + idx < L.acap := by
                        have := hclW.alen_le; omega
                      have hmem : (ksW.arena[k6ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat ∈
                          k6ClauseLits ksW (w0 / 2) := by
                        rw [k6_mem_clauseLits_iff
                          (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                        exact ⟨idx, hidx, rfl⟩
                      exact ⟨hcap, hwf_c.2.2.1 _ hmem⟩
                    have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
                      rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
                    let other := ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
                    have hother_nv : other.toNat < 2 * ksW.nv.toNat := (har_ok _ (by omega)).2
                    have hot_mem : other.toNat ∈ k6ClauseLits ksW (w0 / 2) := by
                      rw [k6_mem_clauseLits_iff
                        (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                      exact ⟨w0 % 2 ^^^ 1, by omega, rfl⟩
                    have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
                    have hw_m2_lt : w0 % 2 < 2 ^ 32 :=
                      Nat.lt_trans (Nat.mod_lt w0 (by decide)) (by decide)
                    have hm2_xor_lt : w0 % 2 ^^^ 1 < 2 ^ 32 := by
                      rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
                    have hslot_bv :
                        (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)) =
                          BitVec.ofNat 32 (w0 % 2) := by
                      apply BitVec.eq_of_toNat_eq
                      change (BitVec.ofNat 32 w0 &&& 1#32).toNat = (BitVec.ofNat 32 (w0 % 2)).toNat
                      rw [hw_mod2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
                    have hslot_other_bv :
                        (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)) =
                          BitVec.ofNat 32 (w0 % 2 ^^^ 1) := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_xor,
                        show (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat =
                          (BitVec.ofNat 32 w0 &&& 1#32).toNat from rfl,
                        hw_mod2, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt hm2_xor_lt]
                    have hcl_off_add :
                        (ksW.clOff[w0 / 2]?.getD 0#32 +
                          (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat =
                        k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) := by
                      have hcap' : k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) < L.acap :=
                        (har_ok (w0 % 2 ^^^ 1) (by omega)).1
                      unfold k6ClauseOff at hcap' ⊢; unfold dimacsBound at hac_b
                      rw [hslot_other_bv]; have := hm2_xor_lt; bv_omega
                    have hcl_off_ar :
                        ((ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32) +
                          (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat <
                          szAr L := by
                      unfold szAr; rw [hw_sh1, hcl_off_add]
                      exact (har_ok (w0 % 2 ^^^ 1) (by omega)).1
                    have hother_mv2 : other.toNat < sz2V L := by unfold sz2V; omega
                    have hoth_arr_lt :
                        (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                          (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD
                            0#32).toNat < sz2V L := by
                      rw [hw_sh1, hcl_off_add]; exact hother_mv2
                    c0_hsteps_nogrp
                    refine LeanQbe.T.wp_unroll_group fun Jsc hJsc => ?_
                    have hsc : Jsc () m' := by
                      refine hJsc () m' ?_
                      let sz := ksW.clSz[w0 / 2]?.getD 0#32
                      let off := ksW.clOff[w0 / 2]?.getD 0#32
                      refine wp_while_break_state
                        (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 =>
                          (b.1, b.2.1, b.2.2, ()))
                        (fun b mb => mb = m' ∧
                          (b.2.1 = 0xFFFFFFFF#32 ∨
                            (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                              b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                              b.2.2 ≠ lit ∧ ksW.vals[b.2.2.toNat]? = some 1#32)))
                        (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                        (fun st m'' => m'' = m' ∧ st.toNat ≤ sz.toNat ∧ 2 ≤ st.toNat) ?_ ?_ ?_
                      · rintro B2 ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
                        dsimp only at hbrk ⊢
                        c0_hsplit
                        · c0_hsteps!
                          exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks + 1#64,
                            false, ksW) mb ⟨hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                        · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                          obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne, _⟩ :=
                            hbrk.resolve_left hri_ne
                          have hrepl_ne' : repl.toNat ≠ lit.toNat :=
                            fun h => hrepl_ne (BitVec.eq_of_toNat_eq h)
                          obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                            k6WatchReloc_preserves hinvW hlit_ltW hwc hri_ge hri_lt hrepl_ne'
                              rfl hrepl_eq
                          obtain ⟨hri_cap, hri_lit⟩ := har_ok ri.toNat hri_lt
                          obtain ⟨hslot_cap, _⟩ :=
                            har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                          have hslot_off_eq :
                              (ksW.clOff[w0 / 2]?.getD 0#32 +
                                (BitVec.ofNat 32 w0 &&& (1 : BitVec 32))).toNat =
                              (ksW.clOff[w0 / 2]?.getD 0#32).toNat + w0 % 2 := by
                            rw [hslot_bv]; unfold dimacsBound at hac_b
                            change (ksW.clOff[w0 / 2]?.getD 0#32 +
                              BitVec.ofNat 32 (w0 % 2)).toNat = _
                            change k6ClauseOff ksW (w0 / 2) + w0 % 2 < L.acap at hslot_cap
                            unfold k6ClauseOff at hslot_cap; bv_omega
                          have hslot_ar :
                              (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                                (BitVec.ofNat 32 w0 &&& (1 : BitVec 32))).toNat < szAr L := by
                            unfold szAr; rw [hw_sh1, hslot_off_eq]; exact hslot_cap
                          have hri_off_eq :
                              (ksW.clOff[w0 / 2]?.getD 0#32 + ri).toNat =
                              (ksW.clOff[w0 / 2]?.getD 0#32).toNat + ri.toNat := by
                            unfold dimacsBound at hac_b
                            change k6ClauseOff ksW (w0 / 2) + ri.toNat < L.acap at hri_cap
                            unfold k6ClauseOff at hri_cap; bv_omega
                          have hri_ar :
                              (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                                ri).toNat < szAr L := by
                            unfold szAr; rw [hw_sh1, hri_off_eq]; exact hri_cap
                          have hsw_lit : BitVec.setWidth 32 lit = lit := by
                            apply BitVec.eq_of_toNat_eq; simp
                          have hlit_bn : BitVec.ofNat 32 lit.toNat = lit := by simp
                          have hrepl_mv2 : repl.toNat < sz2V L := by
                            change repl = ksW.arena[k6ClauseOff ksW (w0 / 2) +
                              ri.toNat]?.getD 0#32 at hrepl_eq
                            rw [hrepl_eq]; unfold sz2V; omega
                          have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < sz2Cl L :=
                            fun hp => by
                              rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                              · exact absurd hpf hp
                              · rw [hshW.wnext_len] at hu_len
                                have hu32 : u < 2 ^ 32 := by
                                  unfold K6Layout.maxCl at hu_len; omega
                                rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]
                                unfold sz2Cl; exact hu_len
                          c0_hsteps_nogrp
                          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                          c0_hsplit
                          · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                            c0_hsteps!; rw [hw_tn]
                            refine ih (prev, ksW.wnext[w0]?.getD 0#32, visits + 1#64, ticks + 1#64,
                                done, todo', _, chW') _ (by simp)
                              ⟨hwc', hrl_inv, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, ?_⟩
                            refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ Rfr) _) ?_) ‹_›
                            dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpeq, ↓reduceIte]
                            k6_ext <;> (first | rfl | {
                              try rw [hw_tn]
                              try rw [hw_sh1]
                              try rw [hcl_off_add]
                              try rw [hslot_off_eq]
                              try rw [hri_off_eq]
                              try rw [hlit_bn]
                              try dsimp only [k6ClauseOff]
                              try rfl })
                          · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                            have hprv_bd := hprv_lt hpne
                            c0_hsteps!; rw [hw_tn]
                            refine ih (prev, ksW.wnext[w0]?.getD 0#32, visits + 1#64, ticks + 1#64,
                                done, todo', _, chW') _ (by simp)
                              ⟨hwc', hrl_inv, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, ?_⟩
                            refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ Rfr) _) ?_) ‹_›
                            dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpne, ↓reduceIte]
                            k6_ext <;> (first | rfl | {
                              try rw [hw_tn]
                              try rw [hw_sh1]
                              try rw [hcl_off_add]
                              try rw [hslot_off_eq]
                              try rw [hri_off_eq]
                              try rw [hlit_bn]
                              try dsimp only [k6ClauseOff]
                              try rfl })
                      · intro B2 L2 r m1 hB2 ih1 ⟨rfl, hr_le, hr2⟩
                        dsimp only at hr_le hr2 ⊢
                        have hw_md : w0 % 2 ^ 32 / 2 = w0 / 2 := by
                          rw [Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hw0_mc2; omega)]
                        c0_hsplit
                        · have hr_lt : r.toNat < sz.toNat := by
                            have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := by
                              bv_omega
                            rwa [hw_md] at hc0
                          obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                          have hr_ar :
                              (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                                r).toNat < szAr L := by
                            rw [hw_sh1]; unfold szAr dimacsBound at *
                            change k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap at hr_cap
                            unfold k6ClauseOff at hr_cap; bv_omega
                          have hcand_mv2 :
                              (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                                0#32 + r).toNat]?.getD 0#32).toNat < sz2V L := by
                            rw [hw_sh1]
                            have hco :
                                (ksW.clOff[w0 / 2]?.getD 0#32 + r).toNat =
                                k6ClauseOff ksW (w0 / 2) + r.toNat := by
                              unfold k6ClauseOff at hr_cap ⊢; unfold dimacsBound at hac_b; bv_omega
                            rw [hco]; unfold sz2V; omega
                          have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                            have hsz_bd : sz.toNat < 2 ^ 28 := by
                              have := hclW.alen_le; unfold dimacsBound at hac_b
                              change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                            bv_omega
                          c0_hsteps_nogrp
                          refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                          c0_hsplit
                          · have hne_cand : ksW.arena[off.toNat + r.toNat]?.getD 0#32 ≠ lit := by
                              have hco : (ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 + r).toNat =
                                  off.toNat + r.toNat := by
                                rw [hw_md]; change (off + r).toNat = off.toNat + r.toNat
                                unfold off
                                have hcap' : k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap := hr_cap
                                unfold k6ClauseOff at hcap'; unfold dimacsBound at hac_b; bv_omega
                              have hc0 : ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 +
                                  r).toNat]?.getD 0#32 ≠ lit := by bv_omega
                              rwa [hco] at hc0
                            c0_hsplit
                            · have hc_val1 :
                                  ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? =
                                  some 1#32 := by
                                have hvl :
                                    (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat <
                                    ksW.vals.length := by
                                  rw [hshW.vals_len]
                                  change (ksW.arena[k6ClauseOff ksW (w0 / 2) +
                                    r.toNat]?.getD 0#32).toNat < 2 * L.maxV
                                  omega
                                have hco : (ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 + r).toNat =
                                    off.toNat + r.toNat := by
                                  rw [hw_md]; change (off + r).toNat = off.toNat + r.toNat
                                  unfold off
                                  change k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap at hr_cap
                                  unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b
                                  bv_omega
                                have hc0 :
                                    ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 +
                                      r).toNat]?.getD 0#32).toNat]?.getD 0#32 = 1#32 := by
                                  bv_omega
                                rw [hco] at hc0
                                rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                                rw [List.getElem?_eq_getElem hvl, hc0]
                              c0_hsteps!
                              have hco : (ksW.clOff[w0 / 2]?.getD 0#32 + r).toNat =
                                  off.toNat + r.toNat := by
                                change (off + r).toNat = off.toNat + r.toNat; unfold off
                                change k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap at hr_cap
                                unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b; bv_omega
                              rw [hw_sh1, hco]
                              exact hB2 (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) _
                                ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hne_cand, hc_val1⟩⟩
                            · c0_hsteps!
                              exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                                ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                          · c0_hsteps!
                            exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                              ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                        · c0_hsteps!; exact hB2 (r, 0xFFFFFFFF#32, 0#32) _ ⟨rfl, Or.inl rfl⟩
                      · intro B2 L2 _ hL2; c0_hsteps!; exact hL2 2#32 m' ⟨rfl, hsz_ge, le_refl _⟩
                    c0_hsplit
                    · -- other != lit ∧ vals[other] == 1 => wblit[w] = other, keep
                      c0_hsplit
                      · obtain ⟨hkp_inv, hkp_wc⟩ :=
                          k6WatchKeep_preserves hinvW hlit_ltW hwc hother_nv hot_mem hsz_ne2
                        c0_hsteps!; rw [hw_tn]
                        refine ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                            ticks + 1#64, done ++ [w0], todo', ksW.putArr .wblit w0 other, chW)
                          _ (by simp)
                          ⟨hkp_wc, hkp_inv, by k6_field; exact w_nv, by k6_field; exact w_na,
                            by k6_field; exact w_as, by k6_field; exact w_va,
                            by k6_field; exact w_la, by k6_field; exact w_nq,
                            by k6_field; exact w_mv, ?_⟩
                        refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ Rfr) _) ?_) ‹_›
                        k6_ext <;> (first | rfl | {
                          dsimp only [other]
                          try rw [hw_tn]
                          try rw [hw_sh1]
                          try rw [hcl_off_add]
                          try dsimp only [k6ClauseOff]
                          try rfl })
                      · refine head_wp_jump rfl rfl hsc
                    · refine head_wp_jump rfl rfl hsc
                  c0_hsplit
                  · -- bv != lit ∧ vals[bv] == 1 => keep
                    c0_hsplit
                    · have hskip := k6WatchSkip_cursor hshW hwc hw0_len
                      c0_hsteps!; rw [hw_tn]
                      exact ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                          ticks, done ++ [w0], todo', ksW, chW) _ (by simp)
                        ⟨hskip, hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                    · refine head_wp_jump rfl rfl hnk
                  · refine head_wp_jump rfl rfl hnk
              · have hw_fff : w = 0xFFFFFFFF#32 := by bv_omega
                c0_hsteps!
                exact hB (prev, w, visits, ticks, true, ksW) m'
                  ⟨hinvW, w_nv, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
            · intro B L1 hB hL
              exact wp_jump_state (proj :=
                  fun st : BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × List Nat ×
                    List Nat × K6State × List (List Nat) =>
                  (st.2.1, st.1, st.2.2.1, st.2.2.2.1, ()))
                (0xFFFFFFFF#32, ks.whead[lit.toNat]?.getD 0#32, 0#64, 1#64,
                  [], ch0[lit.toNat]?.getD [], ks, ch0) rfl
                (hL _ m ⟨hwc0, hinv, rfl, rfl, rfl, rfl, rfl, rfl, hmv_eq_ks, hmA⟩)

/-! ## 6. `10/39`: `full_k512_add_live_m6_wp` -/

theorem k6_arena_take2 {ar : List (BitVec 32)} {off acap : Nat} {a b : BitVec 32}
    (hlen : ar.length = acap) (h1 : off + 1 < acap) :
    ((((ar.set off a).set (off + 1) b).drop off).take 2).map BitVec.toNat =
      [a.toNat, b.toNat] := by
  have hlen0 : (ar.set off a).length = acap := by rw [List.length_set, hlen]
  have hlen1 : ((ar.set off a).set (off + 1) b).length = acap := by rw [List.length_set, hlen0]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, hlen1,
      List.length_cons, List.length_nil]
    omega
  · intro k hk1 _
    have hk2 : k < 2 := by simp at hk1; omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [List.getElem_set_ne (by omega : off + 1 ≠ off), List.getElem_set_self]
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [List.getElem_set_self]

theorem full_k512_add_live_m6_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hBt : M6EnvSpec Γ "full_k6_backtrack" k6BacktrackSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec)
    (hProp : M6EnvSpec Γ "full_k6_propagate" k6PropagateSpec) :
    ∀ args m Q X, k6AddLiveSpec args m Q X →
      Func.wp Γ full_k512_add_live_m6_body args m Q X := by
  rintro ⟨hPtr, a, b, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hinv0, ha_lt,
    hb_unit, hb_bin, hm, hQ⟩
  let scr := s.scratch.scratch_buf
  have hm_b := L.hmaxV; have hac_b := L.hacap
  let ks0 := k6StateOfScratch L scr
  have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  let kPtr := L.kPtr c.pScratchBuf
  have hmF0 : (K6Mem L kPtr ks0 ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_len] at hm; exact sep_ac hm
  clear hm
  have finish : ∀ {ks' : K6State} {m' : Mem 64},
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv →
      ks'.nassump = ks0.nassump → ks'.assump = ks0.assump → ks'.neq = ks0.neq →
      (K6Mem L kPtr ks' ⋆ (FullK6Frame c L s ⋆ R)) m' → Q () m' := by
    intro ks' m' hinv' hsync' hnv' hna' hass' hneq' hm'
    have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := ks') (R := R) (m := m')
      hkb_le hinv'.shapes (sep_ac hm')
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
      List.length_take_of_le hkb_le
    have hscr'_len : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk_len, K6State.toSlab_length hinv'.shapes, ← hL_len]
      unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
    have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
      rw [List.getElem?_append_left (by rw [htk_len]; exact hi), List.getElem?_take_of_lt hi]
    have hof : k6StateOfScratch L scr' = ks' := by
      unfold k6StateOfScratch
      rw [k6_slab_drop_exact _ ks'.toSlab htk_len]
      exact K6State.ofSlab_toSlab hinv'.shapes
    exact hQ scr' m' (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
      (by rw [hof]; exact hinv') (by rw [hof]; exact hsync') (by rw [hof]; exact hnv')
      (by rw [hof]; exact hna') (by unfold k6AssumpLitsS k6AssumpLits; rw [hof, hna', hass'])
      (by rw [hof]; exact hneq') hmJ
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · exfalso
    have hmv0 : L.mv32 = 0#32 := by
      rw [← hmv32_eq]
      exact (‹(BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32›)
    have h0 := congrArg BitVec.toNat hmv0
    change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    iterate 7 c0_hstep
    rw [k6_ptr_base L c.pScratchBuf]
    obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
    have hmA0 : (K6MemA L kPtr ks0 ⋆ Rfr) m := by
      rw [hRfr]; exact k6Mem_to_amem hinv0.shapes hmF0
    have finishR : ∀ {ks' : K6State} {m' : Mem 64},
        K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv →
        ks'.nassump = ks0.nassump → ks'.assump = ks0.assump → ks'.neq = ks0.neq →
        (K6Mem L kPtr ks' ⋆ Rfr) m' → Q () m' :=
      fun hi hs h1 h2 h3 h4 hm' => finish hi hs h1 h2 h3 h4 (by rw [hRfr] at hm'; exact hm')
    clear hmF0
    refine wp_join_state0 (α := K6State)
      (fun ks1 m1 => K6Inv L P ks1 ∧ K6TrailSynced ks1 ∧ ks1.lvl = 0#32 ∧
        ks1.nv = ks0.nv ∧ ks1.nassump = ks0.nassump ∧ ks1.assump = ks0.assump ∧
        ks1.neq = ks0.neq ∧ (K6MemA L kPtr ks1 ⋆ Rfr) m1) ?_ ?_
    · intro J0 ks1 m1 ⟨hinv1, hsync1, hlvl1, hnv1_0, hna1_0, hass1_0, hneq1_0, hmA1⟩
      let runLiveProp :
          ∀ {ksW : K6State} {mW : Mem 64} {k : Tup Val [i32] → Expr Val Cont []},
          K6Inv L P ksW → K6TrailSynced ksW → ksW.lvl = 0#32 →
          ksW.nv = ks0.nv → ksW.nassump = ks0.nassump → ksW.assump = ks0.assump →
          ksW.neq = ks0.neq → (K6MemA L kPtr ksW ⋆ Rfr) mW →
          (∀ confl ksP mP, K6Inv L P ksP → K6TrailSynced ksP → K6PropPreserved ksW ksP →
            confl ≠ 0xFFFFFFFF#32 →
            (confl.toNat < ksP.nc.toNat ∧ ∀ l ∈ k6ClauseLits ksP confl.toNat,
              ksP.vals[l]? = some 2#32) →
            (K6Mem L (L.kPtr c.pScratchBuf) ksP ⋆ Rfr) mP → wp Γ Q X (k (confl, ())) mP) →
          (∀ ksP mP, K6Inv L P ksP → K6TrailSynced ksP → K6PropPreserved ksW ksP →
            (K6Mem L (L.kPtr c.pScratchBuf) ksP ⋆ Rfr) mP →
            wp Γ Q X (k (0xFFFFFFFF#32, ())) mP) →
          k6PropagateSpec (L.kPtr c.pScratchBuf, ()) mW
            (fun r mP => wp Γ Q X (k r) mP) X :=
        fun hinvW hsyncW _ _ _ _ _ hmAW hC hN =>
          ⟨L, P, _, Rfr, hinvW, hsyncW, (k6MemA_to_mem hmAW).2,
            fun confl ksP mP hiP hsP hpp _ _ _ _ hconfl hmP => by
              by_cases hcf : confl = 0xFFFFFFFF#32
              · subst hcf; exact hN ksP mP hiP hsP hpp hmP
              · exact hC confl ksP mP hiP hsP hpp hcf (hconfl hcf) hmP⟩
      have hnv1 := hinv1.clauses.nv_le
      have hmv1 : ks1.max_v = L.mv32 := hinv1.clauses.max_v_eq
      have ha_lt1 : a.toNat < 2 * ks1.nv.toNat := by rw [hnv1_0]; exact ha_lt
      have ha_mv2 : a.toNat < sz2V L := by unfold sz2V; omega
      c0_hsplit
      · -- incons != 0
        c0_hsteps!
        have hinvS := k6SetStatus_preserves_inv hinv1 20#32
        exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsync1)
          (by k6_field; exact hnv1_0) (by k6_field; exact hna1_0)
          (by k6_field; exact hass1_0) (by k6_field; exact hneq1_0) (k6MemA_to_mem hm).2
      · c0_hsplit
        · -- b == 0xFFFFFFFF (unit live clause [a])
          have hent_a := hb_unit ‹_›
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · -- va == 2 => incons = 1, status = 20
            have hfals : ks1.vals[a.toNat]? = some 2#32 := by
              have hv_eq : ks1.vals[a.toNat]?.getD 0#32 = 2#32 := ‹_›
              rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_mv2),
                Option.getD_some] at hv_eq
              rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_mv2), hv_eq]
            have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_a fun x hx => by
              simp at hx; subst hx; exact (k6_falsified_lvl0_entails hinv1 hlvl1 ha_lt1 hfals).2
            c0_hsteps!
            have hinv2 := k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinv1 hunsat) 20#32
            exact finishR hinv2 (by unfold K6TrailSynced at *; k6_field; exact hsync1)
              (by k6_field; exact hnv1_0) (by k6_field; exact hna1_0)
              (by k6_field; exact hass1_0) (by k6_field; exact hneq1_0) (k6MemA_to_mem hm).2
          · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · -- va == 0 => assign(k, a, 0xFFFFFFFF) then propagate
              have hun0 : ks1.vals[a.toNat]? = some 0#32 := by
                have hv_eq : ks1.vals[a.toNat]?.getD 0#32 = 0#32 := ‹_›
                rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_mv2),
                  Option.getD_some] at hv_eq
                rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_mv2), hv_eq]
              have hte_lt := k6_trl_end_lt_of_unassigned hinv1.shapes hnv1 hinv1.assign ha_lt1
                (by simp [hun0])
              obtain ⟨hinv2, hsync2⟩ := k6AssignStep_preserves_inv hinv1 hsync1 ha_lt1 hun0
                (fun _ => hent_a) (fun hpos => by rw [hlvl1] at hpos; simp at hpos) (Or.inl rfl)
              k6_call hAssign
              refine ⟨L, ks1, Rfr, hinv1.shapes, hmv1, (by have := hinv1.clauses.nv_le; omega),
                Nat.lt_of_lt_of_le hte_lt hnv1, (k6MemA_to_mem hmA1).2, fun m2 hm2 => ?_⟩
              c0_hsteps_nogrp
              have hmA2 := k6Mem_to_amem hinv2.shapes hm2
              have hlvl2 : (k6AssignStep ks1 a 0xFFFFFFFF#32).lvl = 0#32 := hlvl1
              refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              k6_call hProp
              refine runLiveProp hinv2 hsync2 hlvl2 hnv1_0 hna1_0 hass1_0 hneq1_0 hmA2 ?_ ?_
              · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                have hunsat := k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                have hmAP := k6Mem_to_amem hinvP.shapes hmP
                c0_hsteps!
                have hinvS :=
                  k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                  (by k6_field; exact hpp.nv.trans hnv1_0)
                  (by k6_field; exact hpp.nassump.trans hna1_0)
                  (by k6_field; exact hpp.assump.trans hass1_0)
                  (by k6_field; exact hpp.neq.trans hneq1_0) (k6MemA_to_mem hm).2
              · intro ksP mP hinvP hsyncP hpp hmP
                c0_hsteps!
                exact finishR hinvP hsyncP (hpp.nv.trans hnv1_0) (hpp.nassump.trans hna1_0)
                  (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0) hmP
            · -- va == 1 => propagate
              c0_hsteps_nogrp
              refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              k6_call hProp
              refine runLiveProp hinv1 hsync1 hlvl1 hnv1_0 hna1_0 hass1_0 hneq1_0 hmA1 ?_ ?_
              · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                have hunsat := k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl1) hconfl_lt hfals
                have hmAP := k6Mem_to_amem hinvP.shapes hmP
                c0_hsteps!
                have hinvS :=
                  k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                  (by k6_field; exact hpp.nv.trans hnv1_0)
                  (by k6_field; exact hpp.nassump.trans hna1_0)
                  (by k6_field; exact hpp.assump.trans hass1_0)
                  (by k6_field; exact hpp.neq.trans hneq1_0) (k6MemA_to_mem hm).2
              · intro ksP mP hinvP hsyncP hpp hmP
                c0_hsteps!
                exact finishR hinvP hsyncP (hpp.nv.trans hnv1_0) (hpp.nassump.trans hna1_0)
                  (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0) hmP
        · -- b != 0xFFFFFFFF (binary live clause [a, b])
          obtain ⟨hb_lt0, hent_ab⟩ := hb_bin ‹_›
          have hb_lt1 : b.toNat < 2 * ks1.nv.toNat := by rw [hnv1_0]; exact hb_lt0
          have hb_mv2 : b.toNat < sz2V L := by unfold sz2V; omega
          have hca1 : ks1.acap.toNat = L.acap := by
            unfold dimacsBound at hac_b
            rw [hinv1.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hmc1 : ks1.max_cl.toNat = L.maxCl := by
            rw [hinv1.clauses.max_cl_eq]; unfold K6Layout.maxCl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hsplit
          · c0_hsteps!
            exact finishR hinv1 hsync1 hnv1_0 hna1_0 hass1_0 hneq1_0 (k6MemA_to_mem hmA1).2
          · c0_hsplit
            · c0_hsteps!
              exact finishR hinv1 hsync1 hnv1_0 hna1_0 hass1_0 hneq1_0 (k6MemA_to_mem hmA1).2
            · have hnc_lt : ks1.nc.toNat < L.maxCl := by rw [← hmc1]; bv_omega
              have hal_ks : ks1.alen.toNat ≤ ks1.acap.toNat := by
                rw [hca1]; exact hinv1.clauses.alen_le
              have hcap_lt : ks1.acap.toNat < 2 ^ 28 := by
                rw [hca1]; unfold dimacsBound at hac_b; omega
              have hoff_fit : ks1.alen.toNat + 2 ≤ L.acap := by rw [← hca1]; bv_omega
              have hoff0_ar : ks1.alen.toNat < szAr L := by unfold szAr; omega
              have hoff1_ar : (ks1.alen + 1#32).toNat < szAr L := by
                unfold szAr dimacsBound at *; bv_omega
              have h1_eq : (ks1.alen + (1 : BitVec 32)).toNat = ks1.alen.toNat + 1 := by
                unfold dimacsBound at hac_b; bv_omega
              have har_len :
                  ((ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b).length = L.acap :=
                by simp [hinv1.shapes.arena_len]
              have hpres := k6AddClause_ge2_preserves (xs := [a, b]) (sz := 2#32)
                (ar := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b) hinv1 hsync1
                hnc_lt (by decide) (by decide) (by simp) hoff_fit har_len
                (fun j hj => by
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                (fun j hj => by
                  have hj2 : j < 2 := by
                    change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
                  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
                  · rw [List.getElem?_set_ne (by omega), Nat.add_zero,
                      List.getElem?_set_self (by rw [hinv1.shapes.arena_len]; omega)]; rfl
                  · rw [List.getElem?_set_self (by simp [hinv1.shapes.arena_len]; omega)]; rfl)
                (fun j hj => by
                  have hj2 : j < 2 := by
                    change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
                  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simpa)
                (by simpa using hent_ab)
              c0_hsteps_nogrp
              obtain ⟨hshM, hmM⟩ := k6MemA_to_mem hm
              let stM := (((({ ks1 with
                  arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
                K6State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
                .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32)
              have hsh_stM : stM.ShapesOk L := by
                have h1 : ({ ks1 with
                    arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
                  K6State).ShapesOk L := { hinv1.shapes with arena_len := har_len }
                exact (((h1.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
              have hmM_eq : (K6Mem L kPtr stM ⋆ Rfr) m := by
                refine Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ Rfr) _) ?_) hmM
                dsimp only [stM]; k6_ext <;> (try rfl) <;> rw [h1_eq]
              k6_call hWatch
              refine ⟨L, stM, Rfr, hsh_stM, (by dsimp only [stM]; k6_field; exact hmv1),
                hnc_lt, (by omega), (by omega), hmM_eq, fun m2 hm2 => ?_⟩
              let ks2_0 := k6WatchStep stM ks1.nc a b
              have hinv2 : K6Inv L P ks2_0 := hpres.1
              have hsync2 : K6TrailSynced ks2_0 := hpres.2.1
              have hlvl2 : ks2_0.lvl = 0#32 := hpres.2.2.1.trans hlvl1
              have hnv2_eq : ks2_0.nv = ks0.nv := hpres.2.2.2.1.trans hnv1_0
              have hna2_eq : ks2_0.nassump = ks0.nassump := hpres.2.2.2.2.1.trans hna1_0
              have hass2_eq : ks2_0.assump = ks0.assump := hpres.2.2.2.2.2.1.trans hass1_0
              have hneq2_eq : ks2_0.neq = ks0.neq := by
                have : ks2_0.neq = ks1.neq := by
                  dsimp only [ks2_0, k6WatchStep, k6WatchStep0, stM]; k6_field
                exact this.trans hneq1_0
              have hnv2 : ks2_0.nv.toNat ≤ L.maxV := hinv2.clauses.nv_le
              have hmv2 : ks2_0.max_v = L.mv32 := hinv2.clauses.max_v_eq
              have hnv21 : ks2_0.nv = ks1.nv := hpres.2.2.2.1
              have ha_lt2 : a.toNat < 2 * ks2_0.nv.toNat := by rw [hnv21]; exact ha_lt1
              have hb_lt2 : b.toNat < 2 * ks2_0.nv.toNat := by rw [hnv21]; exact hb_lt1
              have hcl_nc : k6ClauseLits ks2_0 ks1.nc.toNat = [a.toNat, b.toNat] := by
                have hoff : k6ClauseOff ks2_0 ks1.nc.toNat = ks1.alen.toNat := by
                  unfold k6ClauseOff; dsimp only [ks2_0, k6WatchStep, k6WatchStep0, stM]; k6_field
                  rw [List.getElem?_set_self (by rw [hinv1.shapes.clOff_len]; exact hnc_lt),
                    Option.getD_some]
                have hsz : k6ClauseSize ks2_0 ks1.nc.toNat = 2 := by
                  unfold k6ClauseSize; dsimp only [ks2_0, k6WatchStep, k6WatchStep0, stM]; k6_field
                  rw [List.getElem?_set_self (by rw [hinv1.shapes.clSz_len]; exact hnc_lt),
                    Option.getD_some]; rfl
                unfold k6ClauseLits; rw [hoff, hsz]
                have har_eq : ks2_0.arena =
                    (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b := by
                  dsimp only [ks2_0, k6WatchStep, k6WatchStep0, stM]; k6_field
                rw [har_eq]
                exact k6_arena_take2 hinv1.shapes.arena_len (by omega)
              have hnc_lt2 : ks1.nc.toNat < ks2_0.nc.toNat := by
                have : ks2_0.nc = ks1.nc + 1#32 := by
                  dsimp only [ks2_0, k6WatchStep, k6WatchStep0, stM]; k6_field
                rw [this]; unfold K6Layout.maxCl at hnc_lt; bv_omega
              have hmA2 : (K6MemA L kPtr ks2_0 ⋆ Rfr) m2 := k6Mem_to_amem hinv2.shapes hm2
              clear hm2 hpres hnv21
              obtain ⟨ks2, hks2_def⟩ : ∃ x : K6State, x = ks2_0 := ⟨ks2_0, rfl⟩
              rw [← hks2_def] at hinv2 hsync2 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq
              rw [← hks2_def] at hnv2 hmv2 ha_lt2 hb_lt2 hcl_nc hnc_lt2 hmA2
              clear hks2_def ks2_0 hmM_eq hsh_stM stM
              c0_hsteps_nogrp
              refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · -- va == 2
                have hfals_a : ks2.vals[a.toNat]? = some 2#32 := by
                  have hv_eq : ks2.vals[a.toNat]?.getD 0#32 = 2#32 := ‹_›
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_mv2),
                    Option.getD_some] at hv_eq
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_mv2), hv_eq]
                obtain ⟨⟨ja, hja, hja_eq⟩, hent_na⟩ :=
                  k6_falsified_lvl0_entails hinv2 hlvl2 ha_lt2 hfals_a
                c0_hsplit
                · -- vb == 2 => incons = 1, status = 20
                  have hfals_b : ks2.vals[b.toNat]? = some 2#32 := by
                    have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 2#32 := ‹_›
                    rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                      Option.getD_some] at hv_eq
                    rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                      hv_eq]
                  have hent_nb := (k6_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b).2
                  have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_ab fun x hx => by
                    simp at hx; rcases hx with rfl | rfl
                    · exact hent_na
                    · exact hent_nb
                  c0_hsteps!
                  have hinv3 :=
                    k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinv2 hunsat) 20#32
                  exact finishR hinv3 (by unfold K6TrailSynced at *; k6_field; exact hsync2)
                    (by k6_field; exact hnv2_eq) (by k6_field; exact hna2_eq)
                    (by k6_field; exact hass2_eq) (by k6_field; exact hneq2_eq) (k6MemA_to_mem hm).2
                · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · -- vb == 0 => assign(k, b, nc) then propagate
                    have hun_b : ks2.vals[b.toNat]? = some 0#32 := by
                      have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 0#32 := ‹_›
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                        Option.getD_some] at hv_eq
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                        hv_eq]
                    have hte_lt := k6_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign hb_lt2
                      (by simp [hun_b])
                    have hent_b : SemEntails P [b.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact hent_na
                        · exact absurd rfl hne
                    obtain ⟨hinv3, hsync3⟩ := k6AssignStep_preserves_inv hinv2 hsync2 hb_lt2 hun_b
                      (fun _ => hent_b) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact ⟨ja, hja, hja_eq⟩
                        · exact absurd rfl hne⟩)
                    k6_call hAssign
                    refine ⟨L, ks2, Rfr, hinv2.shapes, hmv2,
                      (by have := hinv2.clauses.nv_le; omega),
                      Nat.lt_of_lt_of_le hte_lt hnv2, (k6MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                    c0_hsteps_nogrp
                    have hmA3 := k6Mem_to_amem hinv3.shapes hm3
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    k6_call hProp
                    refine runLiveProp hinv3 hsync3 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq hmA3
                      ?_ ?_
                    · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                      have hunsat :=
                        k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                      have hmAP := k6Mem_to_amem hinvP.shapes hmP
                      c0_hsteps!
                      have hinvS :=
                        k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                      exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                        (by k6_field; exact hpp.nv.trans hnv2_eq)
                        (by k6_field; exact hpp.nassump.trans hna2_eq)
                        (by k6_field; exact hpp.assump.trans hass2_eq)
                        (by k6_field; exact hpp.neq.trans hneq2_eq) (k6MemA_to_mem ‹_›).2
                    · intro ksP mP hinvP hsyncP hpp hmP
                      c0_hsteps!
                      exact finishR hinvP hsyncP (hpp.nv.trans hnv2_eq)
                        (hpp.nassump.trans hna2_eq) (hpp.assump.trans hass2_eq)
                        (hpp.neq.trans hneq2_eq) hmP
                  · c0_hsteps_nogrp
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    k6_call hProp
                    refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq hmA2
                      ?_ ?_
                    · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                      have hunsat :=
                        k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                      have hmAP := k6Mem_to_amem hinvP.shapes hmP
                      c0_hsteps!
                      have hinvS :=
                        k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                      exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                        (by k6_field; exact hpp.nv.trans hnv2_eq)
                        (by k6_field; exact hpp.nassump.trans hna2_eq)
                        (by k6_field; exact hpp.assump.trans hass2_eq)
                        (by k6_field; exact hpp.neq.trans hneq2_eq) (k6MemA_to_mem hm).2
                    · intro ksP mP hinvP hsyncP hpp hmP
                      c0_hsteps!
                      exact finishR hinvP hsyncP (hpp.nv.trans hnv2_eq)
                        (hpp.nassump.trans hna2_eq) (hpp.assump.trans hass2_eq)
                        (hpp.neq.trans hneq2_eq) hmP
              · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · c0_hsplit
                  · -- va != 2, vb == 2, va == 0 => assign(k, a, nc) then propagate
                    have hfals_b : ks2.vals[b.toNat]? = some 2#32 := by
                      have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 2#32 := ‹_›
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                        Option.getD_some] at hv_eq
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_mv2),
                        hv_eq]
                    have hun_a : ks2.vals[a.toNat]? = some 0#32 := by
                      have hv_eq : ks2.vals[a.toNat]?.getD 0#32 = 0#32 := ‹_›
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_mv2),
                        Option.getD_some] at hv_eq
                      rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_mv2),
                        hv_eq]
                    obtain ⟨⟨jb, hjb, hjb_eq⟩, hent_nb⟩ :=
                      k6_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b
                    have hte_lt := k6_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign ha_lt2
                      (by simp [hun_a])
                    have hent_a : SemEntails P [a.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact hent_nb
                    obtain ⟨hinv3, hsync3⟩ := k6AssignStep_preserves_inv hinv2 hsync2 ha_lt2 hun_a
                      (fun _ => hent_a) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact ⟨jb, hjb, hjb_eq⟩⟩)
                    k6_call hAssign
                    refine ⟨L, ks2, Rfr, hinv2.shapes, hmv2,
                      (by have := hinv2.clauses.nv_le; omega),
                      Nat.lt_of_lt_of_le hte_lt hnv2, (k6MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                    c0_hsteps_nogrp
                    have hmA3 := k6Mem_to_amem hinv3.shapes hm3
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    k6_call hProp
                    refine runLiveProp hinv3 hsync3 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq hmA3
                      ?_ ?_
                    · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                      have hunsat :=
                        k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                      have hmAP := k6Mem_to_amem hinvP.shapes hmP
                      c0_hsteps!
                      have hinvS :=
                        k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                      exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                        (by k6_field; exact hpp.nv.trans hnv2_eq)
                        (by k6_field; exact hpp.nassump.trans hna2_eq)
                        (by k6_field; exact hpp.assump.trans hass2_eq)
                        (by k6_field; exact hpp.neq.trans hneq2_eq) (k6MemA_to_mem hm).2
                    · intro ksP mP hinvP hsyncP hpp hmP
                      c0_hsteps!
                      exact finishR hinvP hsyncP (hpp.nv.trans hnv2_eq)
                        (hpp.nassump.trans hna2_eq) (hpp.assump.trans hass2_eq)
                        (hpp.neq.trans hneq2_eq) hmP
                  · c0_hsteps_nogrp
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    k6_call hProp
                    refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq hmA2
                      ?_ ?_
                    · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                      have hunsat :=
                        k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                      have hmAP := k6Mem_to_amem hinvP.shapes hmP
                      c0_hsteps!
                      have hinvS :=
                        k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                      exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                        (by k6_field; exact hpp.nv.trans hnv2_eq)
                        (by k6_field; exact hpp.nassump.trans hna2_eq)
                        (by k6_field; exact hpp.assump.trans hass2_eq)
                        (by k6_field; exact hpp.neq.trans hneq2_eq) (k6MemA_to_mem hm).2
                    · intro ksP mP hinvP hsyncP hpp hmP
                      c0_hsteps!
                      exact finishR hinvP hsyncP (hpp.nv.trans hnv2_eq)
                        (hpp.nassump.trans hna2_eq) (hpp.assump.trans hass2_eq)
                        (hpp.neq.trans hneq2_eq) hmP
                · c0_hsteps_nogrp
                  refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  k6_call hProp
                  refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq hna2_eq hass2_eq hneq2_eq hmA2 ?_ ?_
                  · intro confl ksP mP hinvP hsyncP hpp hc_ne ⟨hconfl_lt, hfals⟩ hmP
                    have hunsat :=
                      k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                    have hmAP := k6Mem_to_amem hinvP.shapes hmP
                    c0_hsteps!
                    have hinvS :=
                      k6SetStatus_preserves_inv (k6SetIncons_preserves_inv hinvP hunsat) 20#32
                    exact finishR hinvS (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                      (by k6_field; exact hpp.nv.trans hnv2_eq)
                      (by k6_field; exact hpp.nassump.trans hna2_eq)
                      (by k6_field; exact hpp.assump.trans hass2_eq)
                      (by k6_field; exact hpp.neq.trans hneq2_eq) (k6MemA_to_mem hm).2
                  · intro ksP mP hinvP hsyncP hpp hmP
                    c0_hsteps!
                    exact finishR hinvP hsyncP (hpp.nv.trans hnv2_eq)
                      (hpp.nassump.trans hna2_eq) (hpp.assump.trans hass2_eq)
                      (hpp.neq.trans hneq2_eq) hmP
    · intro J0 hJ0
      refine LeanQbe.T.wp_unroll_group fun J1 hJ1 => ?_
      have hBt_ok : J1 () m := by
        refine hJ1 () m ?_
        k6_call hBt
        refine ⟨L, P, ks0, Rfr, hinv0, Or.inl rfl, (k6MemA_to_mem hmA0).2,
          fun ks1 m1 hinv1 hsync1 hlvl1 _ hbtp _ _ hm1 => ?_⟩
        have hmA1 := k6Mem_to_amem hinv1.shapes hm1
        c0_hsteps!
        have hinv1' := k6SetStatus_preserves_inv hinv1 0#32
        exact hJ0 _ _ ⟨hinv1', by unfold K6TrailSynced at *; k6_field; exact hsync1,
          by k6_field; exact hlvl1, by k6_field; exact hbtp.nv,
          by k6_field; exact hbtp.nassump, by k6_field; exact hbtp.assump,
          by k6_field; exact hbtp.neq, ‹_›⟩
      c0_hsplit
      · refine head_wp_jump rfl rfl hBt_ok
      · c0_hsplit
        · refine head_wp_jump rfl rfl hBt_ok
        · have hlvl0 : ks0.lvl = 0#32 := by bv_omega
          c0_hsteps!
          exact hJ0 _ m ⟨hinv0, k6_trailSynced_of_lvl0 hinv0 hlvl0, hlvl0, rfl, rfl, rfl, rfl,
            hmA0⟩

end LeanQbe.T.Examples.Kissat.FullM6Sweep
