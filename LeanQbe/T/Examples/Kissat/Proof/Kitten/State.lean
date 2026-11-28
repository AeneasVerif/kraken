/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Mem
public import LeanQbe.T.Examples.Kissat.Ref.Base

/-!
# Semantic Model-Set Invariants & Step-13 `K6TailEq` State Predicates (`Kissat.Proof.Kitten.State`)

Self-contained semantic entailment, 2-watched-literal chains, structural invariants (`K6Inv`,
`K6AnaInv`, `K6ScratchInv`), preservation relations (`K6BtPreserved`, `K6AnaPreserved`,
`K6PropPreserved`), Step-13 `K6HwmClean` / `K6TailEq`, and pure preservation lemmas.

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Semantic Entailment & Resolution Lemmas -/

/-- Model-set semantic entailment: every local assignment `β` in `P` satisfies clause `cl`. -/
@[expose] def SemEntails (P : (Nat → Bool) → Prop) (cl : List Nat) : Prop :=
  ∀ β, P β → (cnfClause cl).Sat β

theorem SemEntails.mono {P P' : (Nat → Bool) → Prop} {cl : List Nat}
    (himp : ∀ β, P' β → P β) (h : SemEntails P cl) : SemEntails P' cl :=
  fun β hβ => h β (himp β hβ)

theorem SemEntails.subset {P : (Nat → Bool) → Prop} {c1 c2 : List Nat}
    (hsub : ∀ l ∈ c1, l ∈ c2) (h : SemEntails P c1) : SemEntails P c2 := fun β hβ => by
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β c1).mp (h β hβ)
  exact (clause_sat_cnfClause_iff β c2).mpr ⟨l, hsub l hl, hs⟩

theorem SemEntails.perm {P : (Nat → Bool) → Prop} {c1 c2 : List Nat}
    (hp : c1.Perm c2) (h : SemEntails P c1) : SemEntails P c2 :=
  h.subset fun _ hl => hp.mem_iff.mp hl

theorem SemEntails.unsat_of_nil {P : (Nat → Bool) → Prop} (h : SemEntails P []) :
    ∀ β, ¬ P β := fun β hβ => by
  obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff β []).mp (h β hβ); cases hm

theorem SemEntails.unit_of_falsified {P : (Nat → Bool) → Prop} {c : List Nat} {u : Nat}
    (hc : SemEntails P c)
    (hoth : ∀ x ∈ c, x ≠ u → SemEntails P [x ^^^ 1]) : SemEntails P [u] := fun β hβ => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β c).mp (hc β hβ)
  by_cases hxu : x = u
  · rw [hxu] at hxs; exact (sat_cnfClause_singleton β u).mpr hxs
  · have hneg := hoth x hx hxu β hβ
    exact absurd ((sat_cnfClause_singleton β x).mpr hxs)
      ((sat_cnfClause_litNeg_iff β x).mp hneg)

theorem SemEntails.unsat_of_falsified {P : (Nat → Bool) → Prop} {c : List Nat}
    (hc : SemEntails P c) (hfals : ∀ x ∈ c, SemEntails P [x ^^^ 1]) :
    ∀ β, ¬ P β := fun β hβ => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β c).mp (hc β hβ)
  exact (sat_cnfClause_litNeg_iff β x).mp (hfals x hx β hβ) ((sat_cnfClause_singleton β x).mpr hxs)

theorem SemEntails.resolve {P : (Nat → Bool) → Prop} {p : Nat} {c1 c2 res : List Nat}
    (h1 : SemEntails P c1) (h2 : SemEntails P c2)
    (hr1 : ∀ l ∈ c1, l ≠ p → l ∈ res) (hr2 : ∀ l ∈ c2, l ≠ p ^^^ 1 → l ∈ res) :
    SemEntails P res := fun β hβ => by
  obtain ⟨l1, hm1, hs1⟩ := (clause_sat_cnfClause_iff β c1).mp (h1 β hβ)
  by_cases h1p : l1 = p
  · subst h1p
    obtain ⟨l2, hm2, hs2⟩ := (clause_sat_cnfClause_iff β c2).mp (h2 β hβ)
    by_cases h2p : l2 = l1 ^^^ 1
    · rw [h2p] at hs2
      exact absurd ((sat_cnfClause_singleton β l1).mpr hs1)
        ((sat_cnfClause_litNeg_iff β l1).mp ((sat_cnfClause_singleton β (litNeg l1)).mpr hs2))
    · exact (clause_sat_cnfClause_iff β res).mpr ⟨l2, hr2 l2 hm2 h2p, hs2⟩
  · exact (clause_sat_cnfClause_iff β res).mpr ⟨l1, hr1 l1 hm1 h1p, hs1⟩

/-! ## 2. Watch Chains, State Steps, & Invariants -/

/-- Intrusive singly-linked watch chain starting at head `0xFFFFFFFF#32`-terminated. -/
inductive K5WChain (wnext : List (BitVec 32)) : BitVec 32 → List Nat → Prop where
  | nil : K5WChain wnext 0xFFFFFFFF#32 []
  | cons {w : Nat} {ws : List Nat} (hw : w < wnext.length) :
      K5WChain wnext (wnext[w]'hw) ws → K5WChain wnext (BitVec.ofNat 32 w) (w :: ws)

@[expose] def k6WatchStep0 (ks : K6State) (w l valOther : BitVec 32) : K6State :=
  let wi := w.toNat; let li := l.toNat
  { ks with
    wblit := ks.wblit.set wi valOther
    wnext := ks.wnext.set wi (ks.whead[li]?.getD 0#32)
    whead := ks.whead.set li w }

@[expose] def k6WatchStep (ks : K6State) (cid l0 l1 : BitVec 32) : K6State :=
  let w0 := cid <<< 1; let w1 := w0 ||| 1#32
  let sz := (ks.clSz[cid.toNat]?.getD 0#32).toNat
  let bf := if sz = 2 then 0x80000000#32 else 0#32
  k6WatchStep0 (k6WatchStep0 ks w0 l0 (l1 ||| bf)) w1 l1 (l0 ||| bf)

@[expose] def k6AssignStep (ks : K6State) (lit rsn : BitVec 32) : K6State :=
  let v := (lit >>> 1).toNat; let li := lit.toNat; let nli := (lit ^^^ 1#32).toNat
  let te := ks.trl_end.toNat
  let unass' := if ks.unass.toNat > 0 then ks.unass - 1#32 else ks.unass
  let fl := ks.flags[v]?.getD 0#32
  let fl' := if (lit &&& 1#32) ≠ 0#32 then fl ||| 1#32 else fl &&& ~~~1#32
  { ks with
    vals := (ks.vals.set li 1#32).set nli 2#32
    lvlArr := ks.lvlArr.set v ks.lvl
    rsn := ks.rsn.set v rsn
    trl := ks.trl.set te lit
    trl_end := ks.trl_end + 1#32
    unass := unass'
    flags := ks.flags.set v fl' }

@[expose] def k6ClauseOff (ks : K6State) (cid : Nat) : Nat := (ks.clOff[cid]?.getD 0#32).toNat
@[expose] def k6ClauseSize (ks : K6State) (cid : Nat) : Nat := (ks.clSz[cid]?.getD 0#32).toNat

@[expose] def k6ClauseLits (ks : K6State) (cid : Nat) : List Nat :=
  ((ks.arena.drop (k6ClauseOff ks cid)).take (k6ClauseSize ks cid)).map BitVec.toNat

@[expose] def k6AssumpLits (ks : K6State) : List Nat :=
  (ks.assump.take ks.nassump.toNat).map BitVec.toNat

@[expose] def k6TrailLits (ks : K6State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).map BitVec.toNat

@[expose] def k6TrailDecisions (ks : K6State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).filterMap fun l =>
    if 0 < (ks.lvlArr[l.toNat / 2]?.getD 0#32).toNat ∧
       ks.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32
    then some l.toNat else none

/-- `K6` 2WL invariant with exact inline binary `K6_BIN_FLAG` (`0x80000000#32`) tracking. -/
@[expose] def K6WatchesOk (ks : K6State) : Prop :=
  ∃ chains : List (List Nat),
    chains.length = 2 * ks.nv.toNat ∧ chains.flatten.Nodup ∧
    (∀ l < 2 * ks.nv.toNat,
      K5WChain ks.wnext (ks.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
    (∀ l < 2 * ks.nv.toNat, ∀ w ∈ chains[l]?.getD [],
      w < 2 * ks.nc.toNat ∧ 2 ≤ k6ClauseSize ks (w / 2) ∧
      (ks.arena[k6ClauseOff ks (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
      let wb := ks.wblit[w]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w / 2) = 2) ∧
      (k6ClauseSize ks (w / 2) = 2 →
        bv = (ks.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]?.getD 0#32).toNat))

structure K6ClausesOk (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  acap_eq : ks.acap = BitVec.ofNat 32 L.acap
  max_v_eq : ks.max_v = BitVec.ofNat 32 L.maxV
  max_orig_eq : ks.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl
  nv_le : ks.nv.toNat ≤ L.maxV
  nc_le : ks.nc.toNat ≤ L.maxCl
  alen_le : ks.alen.toNat ≤ L.acap
  nassump_le : ks.nassump.toNat ≤ L.maxV
  nkl_le : ks.nkl.toNat ≤ L.maxV
  nana_le : ks.nana.toNat ≤ L.maxV
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k6ClauseSize ks cid ∧
    k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k6ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧
    SemEntails P (k6ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k6ClauseOff ks c1 + k6ClauseSize ks c1 ≤ k6ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  flags_clean : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32

structure K6BaseAssignOk (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  trl_end_le : ks.trl_end.toNat ≤ ks.nv.toNat
  prop_le : ks.prop.toNat ≤ ks.trl_end.toNat
  unass_eq : ks.unass.toNat + ks.trl_end.toNat = ks.nv.toNat
  vals_dom : ∀ l < 2 * ks.nv.toNat,
    let v := ks.vals[l]?.getD 0#32; v = 0#32 ∨ v = 1#32 ∨ v = 2#32
  vals_neg_iff : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 = 1#32 ↔ ks.vals[l ^^^ 1]?.getD 0#32 = 2#32
  vals_nz_iff_trl : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 ≠ 0#32 ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
  trl_nodup : (k6TrailLits ks |>.map (· / 2)).Nodup
  trl_lt : ∀ l ∈ k6TrailLits ks, l < 2 * ks.nv.toNat
  trl_lvl_le : ∀ v < ks.nv.toNat, (ks.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
  unass_lvl_zero : ∀ v < ks.nv.toNat, ks.vals[2 * v]?.getD 0#32 = 0#32 →
    ks.lvlArr[v]?.getD 0#32 = 0#32 ∧ ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32
  trl_lvl_mono : ∀ i j, i ≤ j → j < ks.trl_end.toNat →
    (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  dec_earliest : ∀ i j, j < i → i < ks.trl_end.toNat →
    0 < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 =
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 →
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32
  lvl0_ok : ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]

@[expose] def K6TrailSynced (ks : K6State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32

@[expose] def K6ReasonOk (ks : K6State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    let r := ks.rsn[l / 2]?.getD 0xFFFFFFFF#32
    r = 0xFFFFFFFF#32 ∨
    (r.toNat < ks.nc.toNat ∧ l ∈ k6ClauseLits ks r.toNat ∧
     ∀ x ∈ k6ClauseLits ks r.toNat, x ≠ l → ∃ j < i, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)

structure K6Inv (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  shapes : ks.ShapesOk L
  clauses : K6ClausesOk L P ks
  watches : K6WatchesOk ks
  assign : K6BaseAssignOk P ks
  reasons : K6ReasonOk ks

@[expose] def k6StateOfScratch (L : K6Layout) (scr : List (BitVec 32)) : K6State :=
  K6State.ofSlab L (scr.drop L.k6Base)

@[expose] def k6AssumpLitsS (L : K6Layout) (scr : List (BitVec 32)) : List Nat :=
  k6AssumpLits (k6StateOfScratch L scr)

@[expose] def K6ScratchInv (P : (Nat → Bool) → Prop) (scr : List (BitVec 32)) : Prop :=
  ∃ (hge : k6MinScr ≤ scr.length) (hlt : scr.length < dimacsBound),
    K6Inv (k6LayoutOfCap scr.length hge hlt) P
      (k6StateOfScratch (k6LayoutOfCap scr.length hge hlt) scr)

@[expose] def K6LitsBounded (M : Nat) (ks : K6State) : Prop :=
  (∀ cid < ks.nc.toNat, ∀ l ∈ k6ClauseLits ks cid, l < 2 * M) ∧
  (∀ w < 2 * ks.nc.toNat, (ks.wblit[w]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < 2 * M)

@[expose] def k6ResolventLits (ks : K6State) (idx : Nat) : List Nat :=
  let seenTop := ((List.range idx).filterMap fun j =>
    let l := (ks.trl[j]?.getD 0#32).toNat
    if ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
    then some (l ^^^ 1) else none)
  let klLits := ((ks.kl.take ks.nkl.toNat).drop 1).map BitVec.toNat
  seenTop ++ klLits

structure K6AnaInv (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (idx : Nat) :
    Prop where
  shapes : ks.ShapesOk L
  acap_eq : ks.acap = BitVec.ofNat 32 L.acap
  max_v_eq : ks.max_v = BitVec.ofNat 32 L.maxV
  max_orig_eq : ks.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl
  nv_le : ks.nv.toNat ≤ L.maxV
  nc_le : ks.nc.toNat ≤ L.maxCl
  alen_le : ks.alen.toNat ≤ L.acap
  nassump_le : ks.nassump.toNat ≤ L.maxV
  lvl_pos : 0 < ks.lvl.toNat
  idx_le : idx ≤ ks.trl_end.toNat
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k6ClauseSize ks cid ∧ k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k6ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧ SemEntails P (k6ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k6ClauseOff ks c1 + k6ClauseSize ks c1 ≤ k6ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  watches : K6WatchesOk ks
  assign : K6BaseAssignOk P ks
  synced : K6TrailSynced ks
  reasons : K6ReasonOk ks
  nkl_pos : 1 ≤ ks.nkl.toNat
  nkl_le : ks.nkl.toNat ≤ ks.nv.toNat
  nana_le : ks.nana.toNat ≤ ks.nv.toNat
  ana_nodup : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup
  ana_lt : ∀ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat < ks.nv.toNat
  flags_seen : ∀ v < ks.nv.toNat,
    ((ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat = v
  kl_nonTop : ∀ i, 1 ≤ i → i < ks.nkl.toNat →
    let l := (ks.kl[i]?.getD 0#32).toNat
    l < 2 * ks.nv.toNat ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
    0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat ∧ (ks.lvlArr[l / 2]?.getD 0#32).toNat < ks.lvl.toNat ∧
    ks.vals[l]? = some 2#32
  kl_injective : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat →
    ∃ i, 1 ≤ i ∧ i < ks.nkl.toNat ∧ (ks.kl[i]?.getD 0#32).toNat / 2 = v
  nkl_count : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    0 < (ks.lvlArr[v]?.getD 0#32).toNat
  kl_nodup : (((ks.kl.take ks.nkl.toNat).drop 1).map (fun l => l.toNat / 2)).Nodup
  open_eq : ks.openCnt.toNat =
    ((List.range idx).filter fun j =>
      let v := (ks.trl[j]?.getD 0#32).toNat / 2
      decide (ks.lvlArr[v]?.getD 0#32 = ks.lvl ∧ (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
  seen_in_trl : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    ks.lvlArr[v]?.getD 0#32 = ks.lvl →
    ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = v

structure K6BtPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  nkl : ks'.nkl = ks.nkl
  nana : ks'.nana = ks.nana
  status : ks'.status = ks.status
  phase : ks'.phase = ks.phase
  openCnt : ks'.openCnt = ks.openCnt
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  hdrTail : ks'.hdrTail = ks.hdrTail
  assump : ks'.assump = ks.assump
  ana : ks'.ana = ks.ana
  kl : ks'.kl = ks.kl
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena
  flags2_eq : ∀ v < ks.nv.toNat,
    (ks'.flags[v]?.getD 0#32 &&& 2#32) = (ks.flags[v]?.getD 0#32 &&& 2#32)
  lvlArr_kept : ∀ i < ks'.trl_end.toNat,
    ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
      ks.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?

structure K6AnaPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  status : ks'.status = ks.status
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  lvlArr : ks'.lvlArr = ks.lvlArr
  rsn : ks'.rsn = ks.rsn
  trl : ks'.trl = ks.trl
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena

structure K6PropPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  status : ks'.status = ks.status
  openCnt : ks'.openCnt = ks.openCnt
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  assump : ks'.assump = ks.assump

theorem k6ScratchInv_to_inv {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} {L : K6Layout}
    (hlen : L.scrLen = scr.length) (hmv : L.maxV = k6MaxV scr.length)
    (h : K6ScratchInv P scr) : K6Inv L P (k6StateOfScratch L scr) := by
  rcases h with ⟨hge, hlt, hinv⟩
  rwa [k6LayoutOfCap_eq hlen hmv hge hlt] at hinv

theorem K6Inv.to_scratchInv {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} {L : K6Layout}
    (hlen : scr.length = L.scrLen) (hmv : L.maxV = k6MaxV scr.length)
    (hge : k6MinScr ≤ scr.length) (hlt : scr.length < dimacsBound)
    (h : K6Inv L P (k6StateOfScratch L scr)) : K6ScratchInv P scr := by
  refine ⟨hge, hlt, ?_⟩
  rwa [k6LayoutOfCap_eq hlen.symm hmv hge hlt]

/-! ## 3. Step-13 `K6HwmClean`, `K6TailEq`, & Pure Tail Preservation Lemmas -/

/-- Step-13 `glue_used[33]` high-water mark clean invariant:
either `hw = 0xFFFFFFFF#32` (cold start, full zeroing required) or all entries in `[hw ..< mv)`
already satisfy the initial `K6` defaults (`lvl=0, rsn=0xFFFFFFFF, flags=0, vals=0, whead=-1`). -/
@[expose] def K6HwmClean (L : K6Layout) (hw : BitVec 32) (ks : K6State) : Prop :=
  hw = 0xFFFFFFFF#32 ∨
  (hw.toNat ≤ L.maxV ∧
    ∀ v, hw.toNat ≤ v → v < L.maxV →
      ks.lvlArr[v]?.getD 0#32 = 0#32 ∧
      ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
      ks.flags[v]?.getD 0#32 = 0#32 ∧
      ks.vals[2 * v]?.getD 0#32 = 0#32 ∧
      ks.vals[2 * v + 1]?.getD 0#32 = 0#32 ∧
      ks.whead[2 * v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
      ks.whead[2 * v + 1]?.getD 0#32 = 0xFFFFFFFF#32)

/-- Equality of `nv` and all `7` `K6HwmClean` arrays (`lvlArr, rsn, flags, vals, whead`)
across the unused variable tail `[ks.nv.toNat ..< L.maxV)`. -/
@[expose] def K6TailEq (L : K6Layout) (ks ks' : K6State) : Prop :=
  ks'.nv = ks.nv ∧
  ∀ v, ks.nv.toNat ≤ v → v < L.maxV →
    ks'.lvlArr[v]? = ks.lvlArr[v]? ∧
    ks'.rsn[v]? = ks.rsn[v]? ∧
    ks'.flags[v]? = ks.flags[v]? ∧
    ks'.vals[2 * v]? = ks.vals[2 * v]? ∧
    ks'.vals[2 * v + 1]? = ks.vals[2 * v + 1]? ∧
    ks'.whead[2 * v]? = ks.whead[2 * v]? ∧
    ks'.whead[2 * v + 1]? = ks.whead[2 * v + 1]?

theorem k6TailEq_refl (L : K6Layout) (ks : K6State) : K6TailEq L ks ks :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem k6TailEq_trans {L : K6Layout} {ks1 ks2 ks3 : K6State}
    (h12 : K6TailEq L ks1 ks2) (h23 : K6TailEq L ks2 ks3) : K6TailEq L ks1 ks3 := by
  refine ⟨h23.1.trans h12.1, fun v hv1 hv2 => ?_⟩
  have a := h12.2 v hv1 hv2
  have b := h23.2 v (h12.1 ▸ hv1) hv2
  exact ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1,
    b.2.2.2.1.trans a.2.2.2.1, b.2.2.2.2.1.trans a.2.2.2.2.1,
    b.2.2.2.2.2.1.trans a.2.2.2.2.2.1, b.2.2.2.2.2.2.trans a.2.2.2.2.2.2⟩

theorem k6TailEq_of_putHdr_ne_nv {L : K6Layout} {ks : K6State} {f : K6HdrField}
    (hf : f ≠ .nv) (val : BitVec 32) : K6TailEq L ks (ks.putHdr f val) := by
  have hnv : (ks.putHdr f val).nv = ks.nv := by cases f <;> simp_all [K6State.putHdr]
  refine ⟨hnv, fun v _ _ => ?_⟩
  cases f <;> simp [K6State.putHdr]

theorem k6TailEq_of_k6AssignStep {L : K6Layout} {ks : K6State} (lit rsn : BitVec 32)
    (hlit : lit.toNat < 2 * ks.nv.toNat) : K6TailEq L ks (k6AssignStep ks lit rsn) := by
  have hdiv : (lit >>> 1).toNat = lit.toNat / 2 := by
    rw [show (lit >>> 1) = lit >>> (1 : Nat) from rfl, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hxor : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp [BitVec.toNat_xor]
  refine ⟨rfl, fun v hv1 _ => ?_⟩
  have hdiv_x : (lit.toNat ^^^ 1) / 2 = lit.toNat / 2 := by
    rw [← Nat.pow_one 2, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_xor_distrib]
    simp
  have hne_v : lit.toNat / 2 ≠ v := by omega
  have hne_l0 : lit.toNat ≠ 2 * v := by omega
  have hne_l1 : lit.toNat ≠ 2 * v + 1 := by omega
  have hne_x0 : lit.toNat ^^^ 1 ≠ 2 * v := by omega
  have hne_x1 : lit.toNat ^^^ 1 ≠ 2 * v + 1 := by omega
  dsimp only [k6AssignStep]
  rw [hdiv, hxor]
  refine ⟨List.getElem?_set_ne hne_v, List.getElem?_set_ne hne_v, List.getElem?_set_ne hne_v, ?_,
    ?_, rfl, rfl⟩
  · rw [List.getElem?_set_ne hne_x0, List.getElem?_set_ne hne_l0]
  · rw [List.getElem?_set_ne hne_x1, List.getElem?_set_ne hne_l1]

theorem k6TailEq_of_k6WatchStep {L : K6Layout} {ks : K6State} (cid l0 l1 : BitVec 32)
    (hl0 : l0.toNat < 2 * ks.nv.toNat) (hl1 : l1.toNat < 2 * ks.nv.toNat) :
    K6TailEq L ks (k6WatchStep ks cid l0 l1) := by
  refine ⟨rfl, fun v hv1 _ => ?_⟩
  have hne00 : l0.toNat ≠ 2 * v := by omega
  have hne01 : l0.toNat ≠ 2 * v + 1 := by omega
  have hne10 : l1.toNat ≠ 2 * v := by omega
  have hne11 : l1.toNat ≠ 2 * v + 1 := by omega
  dsimp only [k6WatchStep, k6WatchStep0]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [List.getElem?_set_ne hne10, List.getElem?_set_ne hne00]
  · rw [List.getElem?_set_ne hne11, List.getElem?_set_ne hne01]

theorem k6HwmClean_of_tailEq {L : K6Layout} {gu_pre : Option (BitVec 32)} {hw : BitVec 32}
    {ks ks' : K6State} (hgu : gu_pre = some 0xFFFFFFFF#32 ∨ ks.nv.toNat ≤ hw.toNat)
    (hd : hw = gu_pre.getD 0#32) (hhwm : K6HwmClean L hw ks) (ht : K6TailEq L ks ks') :
    K6HwmClean L hw ks' := by
  rcases hhwm with rfl | ⟨hle, hclean⟩
  · exact Or.inl rfl
  · rcases hgu with hff | hle_nv
    · have : hw = 0xFFFFFFFF#32 := by rw [hd, hff]; rfl
      exact Or.inl this
    · refine Or.inr ⟨hle, fun v hvw hvm => ?_⟩
      have heq := ht.2 v (Nat.le_trans hle_nv hvw) hvm
      have hc := hclean v hvw hvm
      rw [heq.1, heq.2.1, heq.2.2.1, heq.2.2.2.1, heq.2.2.2.2.1, heq.2.2.2.2.2.1,
        heq.2.2.2.2.2.2]
      exact hc

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
