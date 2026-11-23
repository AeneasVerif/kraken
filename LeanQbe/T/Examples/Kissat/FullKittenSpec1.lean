module

public import LeanQbe.T.Examples.Kissat.FullKittenSpec

/-!
# Kissat `D-Full` Scratch `kitten` Invariants & UNSAT-Only `Spec`s (`Part 2`)

Defines the semantic invariants and `15`-function `Spec` contract table for `FullKitten`:
1. Pure functional step specifications (`kittenWatchStep`, `kittenAssignStep`) and acyclic
   2-watched-literal chain predicate `WChain`.
2. Clause-table, antecedent-DAG soundness (`kittenClauseAnts`, `incons_ok`, `failing_ok`),
   base trail/assignment (`lvl0_ok`), and 1UIP conflict-analysis invariants (`KittenAnaInv`,
   `kittenResolventLits`).
3. Compact unchanged-field frame structures eliminating tuple/equality bloat.
4. All `15` UNSAT-only `Spec`s (`9` internal `u32 *k` + `6` public `FullHdr *h`),
   `fullKittenSpecTable`, and `fullKittenEnv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 5. Clause, Watch, Trail & UNSAT Soundness Invariants -/

/-- Exact functional update of one 2WL slot (`wblit[w] := valOther`, prepend `w` to `whead[l]`). -/
def kittenWatchStep0 (ks : KittenState) (w l valOther : BitVec 32) : KittenState :=
  let wi := w.toNat
  let li := l.toNat
  let oldHead := ks.whead[li]?.getD 0#32
  { ks with
    wblit := ks.wblit.set wi valOther
    wnext := ks.wnext.set wi oldHead
    whead := ks.whead.set li w }

/-- Exact functional update of `full_kitten_watch(k, cid, l0, l1)`. -/
def kittenWatchStep (ks : KittenState) (cid l0 l1 : BitVec 32) : KittenState :=
  let w0 := cid <<< 1
  let w1 := w0 ||| 1#32
  kittenWatchStep0 (kittenWatchStep0 ks w0 l0 l1) w1 l1 l0

/-- Exact functional update of `full_kitten_assign(k, lit, rsn)`. -/
def kittenAssignStep (ks : KittenState) (lit rsn : BitVec 32) : KittenState :=
  let v := (lit >>> 1).toNat
  let li := lit.toNat
  let nli := (lit ^^^ 1#32).toNat
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

/-- Acyclic finite linked-list chain encoded in `wnext` starting at `head` (`0xFFFFFFFF` = nil). -/
inductive WChain (wnext : List (BitVec 32)) : BitVec 32 → List Nat → Prop where
  | nil : WChain wnext 0xFFFFFFFF#32 []
  | cons {w : Nat} {ws : List Nat} (hw : w < wnext.length) :
      WChain wnext (wnext[w]'hw) ws →
      WChain wnext (BitVec.ofNat 32 w) (w :: ws)

def kittenClauseOff (ks : KittenState) (cid : Nat) : Nat := (ks.clOff[cid]?.getD 0#32).toNat
def kittenClauseMeta (ks : KittenState) (cid : Nat) : BitVec 32 := ks.clMeta[cid]?.getD 0#32
def kittenClauseSize (ks : KittenState) (cid : Nat) : Nat :=
  (kittenClauseMeta ks cid &&& 0xFFFF#32).toNat
def kittenClauseIsLrn (ks : KittenState) (cid : Nat) : Bool :=
  (kittenClauseMeta ks cid &&& kmLrn) != 0#32
def kittenClauseAux (ks : KittenState) (cid : Nat) : Nat := (ks.clAux[cid]?.getD 0#32).toNat
def kittenClauseSpan (ks : KittenState) (cid : Nat) : Nat :=
  kittenClauseSize ks cid + if kittenClauseIsLrn ks cid then kittenClauseAux ks cid else 0

def kittenClauseLits (ks : KittenState) (cid : Nat) : List Nat :=
  ((ks.arena.drop (kittenClauseOff ks cid)).take (kittenClauseSize ks cid)).map BitVec.toNat

/-- Recorded antecedent clause IDs (`clAux` trailing slice for learned, `[cid]` for orig). -/
def kittenClauseAnts (ks : KittenState) (cid : Nat) : List Nat :=
  if kittenClauseIsLrn ks cid then
    ((ks.arena.drop (kittenClauseOff ks cid + kittenClauseSize ks cid)).take
      (kittenClauseAux ks cid)).map BitVec.toNat
  else [cid]

def kittenOrigClauses (ks : KittenState) : List (List Nat) :=
  (List.range ks.orig_nc.toNat).map (kittenClauseLits ks)

def kittenAssumpLits (ks : KittenState) : List Nat :=
  (ks.assump.take ks.nassump.toNat).map BitVec.toNat

def kittenCoreClauses (ks : KittenState) : List (List Nat) :=
  ((List.range ks.orig_nc.toNat).filter fun ci =>
    (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)

/-- Disjointness, boundedness, and watch soundness over `whead[0..2*nv)` / `wnext`. -/
def KittenWatchesOk (ks : KittenState) : Prop :=
  ∃ chains : List (List Nat),
    chains.length = 2 * ks.nv.toNat ∧
    chains.flatten.Nodup ∧
    (∀ l < 2 * ks.nv.toNat,
      WChain ks.wnext (ks.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
    (∀ l < 2 * ks.nv.toNat, ∀ w ∈ chains[l]?.getD [],
      w < 2 * ks.nc.toNat ∧ 2 ≤ kittenClauseSize ks (w / 2) ∧
      (ks.arena[kittenClauseOff ks (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
      (ks.wblit[w]?.getD 0#32).toNat < 2 * ks.nv.toNat)

/-- Clause-table well-formedness, DAG antecedent soundness, & UNSAT entailment. -/
structure KittenClausesOk (acap : Nat) (ks : KittenState) : Prop where
  acap_ge : kMinScratchCap - kBase - kSlabFixed ≤ acap
  acap_lt : acap < dimacsBound
  acap_eq : ks.acap = BitVec.ofNat 32 acap
  nv_le : ks.nv.toNat ≤ kMaxV
  nc_le : ks.nc.toNat ≤ kMaxCl
  orig_nc_le : ks.orig_nc.toNat ≤ ks.nc.toNat
  orig_nc_max : ks.orig_nc.toNat ≤ kMaxOrig
  alen_le : ks.alen.toNat ≤ acap
  nassump_le : ks.nassump.toNat ≤ kMaxV
  nunits_le : ks.nunits.toNat ≤ kMaxL
  nres_le : ks.nres.toNat ≤ kMaxL + 1
  nkl_le : ks.nkl.toNat ≤ kMaxV
  nana_le : ks.nana.toNat ≤ kMaxV
  cl_wf : ∀ cid < ks.nc.toNat,
    kittenClauseIsLrn ks cid = decide (ks.orig_nc.toNat ≤ cid) ∧
    (ks.orig_nc.toNat ≤ cid → 1 ≤ kittenClauseSize ks cid) ∧
    kittenClauseOff ks cid + kittenClauseSpan ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ kittenClauseLits ks cid, l < 2 * ks.nv.toNat) ∧
    (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause (kittenClauseLits ks cid)) ∧
    (ks.ante ≠ 0#32 → ks.orig_nc.toNat ≤ cid →
      (∀ a ∈ kittenClauseAnts ks cid, a < cid) ∧
      (cnfOfClauses ((kittenClauseAnts ks cid).map (kittenClauseLits ks))).EntailsClause
        (cnfClause (kittenClauseLits ks cid)))
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    kittenClauseOff ks c1 + kittenClauseSpan ks c1 ≤ kittenClauseOff ks c2
  units_ok : ∀ ui < ks.nunits.toNat,
    let ucid := (ks.units[ui]?.getD 0#32).toNat
    ucid < ks.nc.toNat ∧ kittenClauseSize ks ucid = 1
  incons_ok : ks.incons ≠ 0xFFFFFFFF#32 →
    ks.incons.toNat < ks.nc.toNat ∧
    (cnfOfClauses (kittenOrigClauses ks)).Unsat ∧
    (∀ l ∈ kittenClauseLits ks ks.incons.toNat,
      ks.vals[l]? = some 2#32 ∧ ks.lvlArr[l / 2]?.getD 0#32 = 0#32 ∧
      (ks.ante ≠ 0#32 →
        let r := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
        r < ks.nc.toNat ∧ kittenClauseLits ks r = [l ^^^ 1]))
  failing_ok : ks.ante ≠ 0#32 → ks.failing ≠ 0xFFFFFFFF#32 →
    (cnfOfClauses
      (((List.range ks.nc.toNat).filter fun ci =>
        (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
      unitsCnf (kittenAssumpLits ks)).Unsat
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  flags_clean : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32

def kittenTrailLits (ks : KittenState) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).map BitVec.toNat

/-- Base trail & assignment invariant (preserved by `full_kitten_flip`). -/
structure KittenBaseAssignOk (ks : KittenState) : Prop where
  trl_end_le : ks.trl_end.toNat ≤ ks.nv.toNat
  prop_le : ks.prop.toNat ≤ ks.trl_end.toNat
  unass_eq : ks.unass.toNat + ks.trl_end.toNat = ks.nv.toNat
  vals_dom : ∀ l < 2 * ks.nv.toNat,
    let v := ks.vals[l]?.getD 0#32
    v = 0#32 ∨ v = 1#32 ∨ v = 2#32
  vals_neg_iff : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 = 1#32 ↔ ks.vals[l ^^^ 1]?.getD 0#32 = 2#32
  vals_nz_iff_trl : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 ≠ 0#32 ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
  trl_nodup : (kittenTrailLits ks |>.map (· / 2)).Nodup
  trl_lt : ∀ l ∈ kittenTrailLits ks, l < 2 * ks.nv.toNat
  trl_lvl_le : ∀ v < ks.nv.toNat, (ks.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
  unass_lvl_zero : ∀ v < ks.nv.toNat, ks.vals[2 * v]?.getD 0#32 = 0#32 →
    ks.lvlArr[v]?.getD 0#32 = 0#32 ∧ ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32
  trl_lvl_mono : ∀ i j, i ≤ j → j < ks.trl_end.toNat →
    (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  dec_earliest : ∀ i j, j < i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 =
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 →
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32
  lvl0_ok : ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
    ks.rsn[l / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32 ∧
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 ∧
    (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [l]) ∧
    (ks.ante ≠ 0#32 →
      let r := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
      r < ks.nc.toNat ∧ kittenClauseLits ks r = [l])

/-- Trail entries match `vals` at all levels (`true` before `flip`, restored by `backtrack 0`). -/
def KittenTrailSynced (ks : KittenState) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32

/-- Well-founded propagation reason DAG invariant on `trl[0..trl_end)`. -/
def ReasonOk (ks : KittenState) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    let r := ks.rsn[l / 2]?.getD 0#32
    r = 0xFFFFFFFF#32 ∨
    (r.toNat < ks.nc.toNat ∧
     l ∈ kittenClauseLits ks r.toNat ∧
     ∀ x ∈ kittenClauseLits ks r.toNat, x ≠ l →
       ∃ j < i, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)

/-- Every watched clause's blocker literal `wblit[w]` belongs to that clause's literals. -/
def KittenWblitInClause (ks : KittenState) : Prop :=
  ∀ w < 2 * ks.nc.toNat, 2 ≤ kittenClauseSize ks (w / 2) →
    (ks.wblit[w]?.getD 0#32).toNat ∈ kittenClauseLits ks (w / 2)

/-- Combined internal `KittenState` invariant (excluding `TrailSynced`, so `flip` preserves it). -/
structure KittenInv (acap : Nat) (ks : KittenState) : Prop where
  shapes : ks.ShapesOk acap
  clauses : KittenClausesOk acap ks
  watches : KittenWatchesOk ks
  assign : KittenBaseAssignOk ks
  reasons : ReasonOk ks

abbrev KittenState.Inv (ks : KittenState) (acap : Nat) : Prop :=
  KittenInv acap ks

/-- Public view of `KittenState` from `h->scratch_buf`. -/
def kittenStateOfScratch (scr : List (BitVec 32)) : KittenState :=
  KittenState.ofSlab (scr.drop 256)

/-- Public original clauses from `h->scratch_buf`. -/
def kittenOrigClausesS (scr : List (BitVec 32)) : List (List Nat) :=
  kittenOrigClauses (kittenStateOfScratch scr)

/-- Public active assumption literals from `h->scratch_buf`. -/
def kittenAssumpLitsS (scr : List (BitVec 32)) : List Nat :=
  kittenAssumpLits (kittenStateOfScratch scr)

/-- Public core-marked original clauses (`KM_CORE != 0`) from `h->scratch_buf`. -/
def kittenCoreClausesS (scr : List (BitVec 32)) : List (List Nat) :=
  kittenCoreClauses (kittenStateOfScratch scr)

/-- Headline scratch invariant over `h->scratch_buf : List (BitVec 32)`. -/
def KittenScratchInv (scr : List (BitVec 32)) : Prop :=
  kMinScratchCap ≤ scr.length ∧ scr.length < dimacsBound ∧
  (kittenStateOfScratch scr).Inv (scr.length - 8864)

/-- Clause-by-clause permutation equivalence preserving `sat`, `unsat`, and entailment. -/
def KittenCnfPermEquiv (F1 F2 : List (List Nat)) : Prop :=
  F1.length = F2.length ∧ ∀ i < F1.length, (F1[i]!).Perm (F2[i]!)

/-- Trail decisions (`rsn[l/2] = 0xFFFFFFFF`). -/
def kittenTrailDecisions (ks : KittenState) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).filterMap fun l =>
    if ks.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 then some l.toNat else none

/-- Every active assumption is assigned true (`vals[a] = 1`) on `ks`. -/
def KittenAllAssumpsAssigned (ks : KittenState) : Prop :=
  ∀ i < ks.nassump.toNat, ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 1#32

/-- Every decision on the current trail belongs to `assump[0..nassump)`. -/
def KittenAllDecisionsInAssumps (ks : KittenState) : Prop :=
  ∀ d ∈ kittenTrailDecisions ks, d ∈ kittenAssumpLits ks

/-- Active resolvent literals at analysis cursor `idx` (marked current-level negs + `kl[1..)`). -/
def kittenResolventLits (ks : KittenState) (idx : Nat) : List Nat :=
  let seenTop := ((List.range idx).filterMap fun j =>
    let l := (ks.trl[j]?.getD 0#32).toNat
    if ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
    then some (l ^^^ 1) else none)
  let klLits := ((ks.kl.take ks.nkl.toNat).drop 1).map BitVec.toNat
  seenTop ++ klLits

/-- Structural loop invariant for 1UIP conflict analysis (`ana_clause` + `analyze`). -/
structure KittenAnaInv (acap : Nat) (ks : KittenState) (F0 : List (List Nat))
    (idx : Nat) : Prop where
  shapes : ks.ShapesOk acap
  nv_le : ks.nv.toNat ≤ kMaxV
  nc_le : ks.nc.toNat ≤ kMaxCl
  orig_nc_le : ks.orig_nc.toNat ≤ ks.nc.toNat
  orig_nc_max : ks.orig_nc.toNat ≤ kMaxOrig
  alen_le : ks.alen.toNat ≤ acap
  acap_lt : acap < dimacsBound
  acap_eq : ks.acap = BitVec.ofNat 32 acap
  lvl_pos : 0 < ks.lvl.toNat
  idx_le : idx ≤ ks.trl_end.toNat
  cl_wf : ∀ cid < ks.nc.toNat,
    kittenClauseIsLrn ks cid = decide (ks.orig_nc.toNat ≤ cid) ∧
    (ks.orig_nc.toNat ≤ cid → 1 ≤ kittenClauseSize ks cid) ∧
    kittenClauseOff ks cid + kittenClauseSpan ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ kittenClauseLits ks cid, l < 2 * ks.nv.toNat) ∧
    (cnfOfClauses F0).EntailsClause (cnfClause (kittenClauseLits ks cid)) ∧
    (ks.ante ≠ 0#32 → ks.orig_nc.toNat ≤ cid →
      (∀ a ∈ kittenClauseAnts ks cid, a < cid) ∧
      (cnfOfClauses ((kittenClauseAnts ks cid).map (kittenClauseLits ks))).EntailsClause
        (cnfClause (kittenClauseLits ks cid)))
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    kittenClauseOff ks c1 + kittenClauseSpan ks c1 ≤ kittenClauseOff ks c2
  orig_eq : kittenOrigClauses ks = F0
  watches : KittenWatchesOk ks
  assign : KittenBaseAssignOk ks
  synced : KittenTrailSynced ks
  reasons : ReasonOk ks
  nres_le : ks.nres.toNat ≤ kMaxL + 1
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
    l < 2 * ks.nv.toNat ∧
    (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
    0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat ∧
    (ks.lvlArr[l / 2]?.getD 0#32).toNat < ks.lvl.toNat ∧
    ks.vals[l]? = some 2#32
  kl_injective : ∀ v < ks.nv.toNat,
    (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat →
    ∃ i, 1 ≤ i ∧ i < ks.nkl.toNat ∧ (ks.kl[i]?.getD 0#32).toNat / 2 = v
  nkl_count : ∀ v < ks.nv.toNat,
    (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    0 < (ks.lvlArr[v]?.getD 0#32).toNat
  kl_nodup : (((ks.kl.take ks.nkl.toNat).drop 1).map (fun l => l.toNat / 2)).Nodup
  status_eq : ks.status.toNat =
    ((List.range idx).filter fun j =>
      let v := (ks.trl[j]?.getD 0#32).toNat / 2
      decide (ks.lvlArr[v]?.getD 0#32 = ks.lvl ∧ (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
  seen_in_trl : ∀ v < ks.nv.toNat,
    (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    ks.lvlArr[v]?.getD 0#32 = ks.lvl →
    ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = v

/-! ### Compact Frame Preservation Helpers -/

/-- Unchanged `KittenState` frame fields across `full_kitten_backtrack`. -/
structure KittenBtPreserved (ks ks' : KittenState) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  orig_nc : ks'.orig_nc = ks.orig_nc
  incons : ks'.incons = ks.incons
  failing : ks'.failing = ks.failing
  ante : ks'.ante = ks.ante
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  nunits : ks'.nunits = ks.nunits
  nres : ks'.nres = ks.nres
  nkl : ks'.nkl = ks.nkl
  nana : ks'.nana = ks.nana
  status : ks'.status = ks.status
  phase : ks'.phase = ks.phase
  hdrTail : ks'.hdrTail = ks.hdrTail
  assump : ks'.assump = ks.assump
  ana : ks'.ana = ks.ana
  kl : ks'.kl = ks.kl
  units : ks'.units = ks.units
  res : ks'.res = ks.res
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clMeta : ks'.clMeta = ks.clMeta
  clAux : ks'.clAux = ks.clAux
  arena : ks'.arena = ks.arena
  flags2_eq : ∀ v < ks.nv.toNat,
    (ks'.flags[v]?.getD 0#32 &&& 2#32) = (ks.flags[v]?.getD 0#32 &&& 2#32)
  lvlArr_kept : ∀ i < ks'.trl_end.toNat,
    ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
      ks.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?

/-- Unchanged `KittenState` frame fields across `full_kitten_learn_unit0` on success. -/
structure KittenUnit0Preserved (ks ks' : KittenState) : Prop where
  orig_nc : ks'.orig_nc = ks.orig_nc
  nv : ks'.nv = ks.nv
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  failing : ks'.failing = ks.failing
  ante : ks'.ante = ks.ante
  nassump : ks'.nassump = ks.nassump
  nres : ks'.nres = ks.nres
  nkl : ks'.nkl = ks.nkl
  nana : ks'.nana = ks.nana
  status : ks'.status = ks.status
  lvlArr : ks'.lvlArr = ks.lvlArr
  rsn : ks'.rsn = ks.rsn
  trl : ks'.trl = ks.trl
  flags : ks'.flags = ks.flags
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  old_clauses : ∀ cid < ks.nc.toNat,
    kittenClauseOff ks' cid = kittenClauseOff ks cid ∧
    kittenClauseMeta ks' cid = kittenClauseMeta ks cid ∧
    kittenClauseAux ks' cid = kittenClauseAux ks cid ∧
    kittenClauseLits ks' cid = kittenClauseLits ks cid
  arena_old : ∀ i < ks.alen.toNat, ks'.arena[i]? = ks.arena[i]?

/-- Unchanged `KittenState` frame fields across `full_kitten_ana_clause`. -/
structure KittenAnaClausePreserved (ks ks' : KittenState) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  orig_nc : ks'.orig_nc = ks.orig_nc
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  failing : ks'.failing = ks.failing
  ante : ks'.ante = ks.ante
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  nunits : ks'.nunits = ks.nunits
  lvlArr : ks'.lvlArr = ks.lvlArr
  rsn : ks'.rsn = ks.rsn
  trl : ks'.trl = ks.trl
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  units : ks'.units = ks.units
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clMeta : ks'.clMeta = ks.clMeta
  clAux : ks'.clAux = ks.clAux
  arena : ks'.arena = ks.arena
  flags2_mono : ∀ v < ks.nv.toNat,
    (ks'.flags[v]?.getD 0#32 &&& 2#32) = 0#32 → (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32

/-- Unchanged `KittenState` frame fields across `full_kitten_build_failing`. -/
structure KittenBuildFailingPreserved (ks ks' : KittenState) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  orig_nc : ks'.orig_nc = ks.orig_nc
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  ante : ks'.ante = ks.ante
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  orig_eq : kittenOrigClauses ks' = kittenOrigClauses ks
  clAux_eq : ∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?

/-! ## 6. UNSAT-Only `Spec` Contracts (`9` internal + `6` public) & `fullKittenSpecTable` -/

/-! ### Internal `u32 *k` Helper Contracts (`9` fns) -/

def fullKittenWatchSpec : Spec [i64, i32, i32, i32] [] := fun (kPtr, cid, l0, l1, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ kMaxV ∧ cid.toNat < kMaxCl ∧
    l0.toNat < 2 * ks.nv.toNat ∧ l1.toNat < 2 * ks.nv.toNat ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ m', (KittenMem kPtr (kittenWatchStep ks cid l0 l1) ⋆ R) m' → Q () m'

def fullKittenAssignSpec : Spec [i64, i32, i32] [] := fun (kPtr, lit, rsn, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ kMaxV ∧
    lit.toNat < 2 * ks.nv.toNat ∧ ks.trl_end.toNat < ks.nv.toNat ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ m', (KittenMem kPtr (kittenAssignStep ks lit rsn) ⋆ R) m' → Q () m'

def fullKittenMtfSpec : Spec [i64, i32] [] := fun (kPtr, _v, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ kMaxV ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : KittenState :=
        { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                  qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk acap → (KittenMem kPtr ks' ⋆ R) m' → Q () m'

def fullKittenBacktrackSpec : Spec [i64, i32] [] := fun (kPtr, target_lvl, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.Inv acap ∧
    (∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
      let l := (ks.trl[i]?.getD 0#32).toNat
      ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32) ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ ks' m',
      ks'.Inv acap → KittenTrailSynced ks' → ks'.lvl = target_lvl →
      ks'.trl_end.toNat ≤ ks.trl_end.toNat →
      ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks'.trl_end.toNat →
      KittenBtPreserved ks ks' →
      (∀ d ∈ kittenTrailDecisions ks', ∃ i < ks'.trl_end.toNat,
        (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions ks) →
      (∀ i < ks.trl_end.toNat,
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < ks'.trl_end.toNat) →
      (KittenMem kPtr ks' ⋆ R) m' → Q () m'

def fullKittenLearnUnit0Spec : Spec [i64, i32, i32, .bool] [i32] :=
  fun (kPtr, lit, src_cid, from_res, ()) m Q _ =>
    ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
      ks.ShapesOk acap ∧ KittenClausesOk acap ks ∧
      lit.toNat < 2 * ks.nv.toNat ∧
      (from_res = false → src_cid.toNat < ks.nc.toNat) ∧
      (ks.ante ≠ 0#32 → from_res = false →
        ∀ l ∈ kittenClauseLits ks src_cid.toNat, l ≠ lit.toNat →
          let r := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
          r < ks.nc.toNat ∧ kittenClauseLits ks r = [l ^^^ 1]) ∧
      (ks.ante ≠ 0#32 → from_res = true → ks.nres.toNat ≤ kMaxL ∧
        (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) ∧
        (cnfOfClauses ((ks.res.take ks.nres.toNat).map fun c =>
          kittenClauseLits ks c.toNat)).EntailsClause (cnfClause [lit.toNat])) ∧
      (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [lit.toNat]) ∧
      (KittenMem kPtr ks ⋆ R) m ∧
      ∀ (ucid : BitVec 32) (ks' : KittenState) (m' : Mem 64),
        ks'.ShapesOk acap → KittenClausesOk acap ks' →
        (ucid = 0xFFFFFFFF#32 → ks' = ks) →
        (ucid ≠ 0xFFFFFFFF#32 →
          ucid = ks.nc ∧ ks'.nc = ks.nc + 1#32 ∧ KittenUnit0Preserved ks ks' ∧
          kittenClauseSize ks' ucid.toNat = 1 ∧ kittenClauseLits ks' ucid.toNat = [lit.toNat]) →
        (KittenMem kPtr ks' ⋆ R) m' → Q (ucid, ()) m'

def fullKittenPropagateSpec : Spec [i64] [i32] := fun (kPtr, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.Inv acap ∧ KittenTrailSynced ks ∧ (KittenMem kPtr ks ⋆ R) m ∧
    ∀ (confl : BitVec 32) (ks' : KittenState) (m' : Mem 64),
      ks'.Inv acap → KittenTrailSynced ks' →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.lvl = ks.lvl →
      ks'.incons = ks.incons → ks'.failing = ks.failing → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump →
      KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      ks.trl_end.toNat ≤ ks'.trl_end.toNat →
      kittenTrailDecisions ks' = kittenTrailDecisions ks →
      (∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
        ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) →
      (confl = 0xFFFFFFFF#32 → ks'.prop = ks'.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl ≠ 0xFFFFFFFE#32 →
        confl.toNat < ks'.nc.toNat ∧
        ∀ l ∈ kittenClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) →
      (KittenMem kPtr ks' ⋆ R) m' → Q (confl, ()) m'

def fullKittenAnaClauseSpec : Spec [i64, i32, i32] [] :=
  fun (kPtr, cid, skip_v, ()) m Q _ =>
    ∃ (acap : Nat) (ks : KittenState) (F0 : List (List Nat)) (idx : Nat)
      (R : Mem 64 → Prop),
      KittenAnaInv acap ks F0 idx ∧ cid.toNat < ks.nc.toNat ∧
      (skip_v = 0xFFFFFFFF#32 ∨ skip_v.toNat < ks.nv.toNat) ∧
      (∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl) ∧
      (∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip_v.toNat →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1) ∧
      ((skip_v = 0xFFFFFFFF#32 ∧ ks.status = 0#32 ∧ ks.nkl = 1#32 ∧
        ks.nana = 0#32 ∧ ks.nres = 0#32) ∨
       (∃ p, p / 2 = skip_v.toNat ∧ p ∈ kittenClauseLits ks cid.toNat ∧
        (∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 = skip_v.toNat → l = p) ∧
        (cnfOfClauses F0).EntailsClause (cnfClause ((p ^^^ 1) :: kittenResolventLits ks idx)) ∧
        (ks.ante ≠ 0#32 → ks.nres.toNat ≤ kMaxL →
          (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) ∧
          (cnfOfClauses ((ks.res.take ks.nres.toNat).map fun c =>
            kittenClauseLits ks c.toNat)).EntailsClause
              (cnfClause ((p ^^^ 1) :: kittenResolventLits ks idx))))) ∧
      (KittenMem kPtr ks ⋆ R) m ∧
      ∀ (ks' : KittenState) (m' : Mem 64),
        KittenAnaInv acap ks' F0 idx →
        KittenAnaClausePreserved ks ks' →
        (cnfOfClauses F0).EntailsClause (cnfClause (kittenResolventLits ks' idx)) →
        (ks'.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
          (∀ i < ks'.nres.toNat, (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks'.nc.toNat) ∧
          (cnfOfClauses ((ks'.res.take ks'.nres.toNat).map fun c =>
            kittenClauseLits ks' c.toNat)).EntailsClause
              (cnfClause (kittenResolventLits ks' idx))) →
        (KittenMem kPtr ks' ⋆ R) m' → Q () m'

def fullKittenAnalyzeSpec : Spec [i64, i32] [.bool] := fun (kPtr, confl_cid, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.Inv acap ∧ KittenTrailSynced ks ∧ 0 < ks.lvl.toNat ∧
    (∃ i < ks.trl_end.toNat, ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl) ∧
    confl_cid.toNat < ks.nc.toNat ∧
    (∀ l ∈ kittenClauseLits ks confl_cid.toNat, ks.vals[l]? = some 2#32) ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ (ok : Bool) (ks' : KittenState) (m' : Mem 64),
      ks'.Inv acap →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump →
      ks'.incons = ks.incons → ks'.failing = ks.failing →
      kittenOrigClauses ks' = kittenOrigClauses ks →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      (ok = true →
        KittenTrailSynced ks' ∧ ks'.lvl.toNat < ks.lvl.toNat ∧
        (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
          ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
        (∀ d ∈ kittenTrailDecisions ks', ∃ i < ks.trl_end.toNat,
          (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions ks ∧
          (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat) ∧
        (∀ i < ks.trl_end.toNat,
          (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
          i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
          ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)) →
      (KittenMem kPtr ks' ⋆ R) m' → Q (ok, ()) m'

def fullKittenBuildFailingSpec : Spec [i64, i32] [] := fun (kPtr, alit, ()) m Q _ =>
  ∃ (acap : Nat) (ks : KittenState) (R : Mem 64 → Prop),
    ks.Inv acap ∧ KittenTrailSynced ks ∧ alit.toNat < 2 * ks.nv.toNat ∧
    alit.toNat ∈ kittenAssumpLits ks ∧
    ks.vals[alit.toNat]? = some 2#32 ∧ KittenAllDecisionsInAssumps ks ∧
    (KittenMem kPtr ks ⋆ R) m ∧
    ∀ (ks' : KittenState) (m' : Mem 64),
      ks'.Inv acap → KittenTrailSynced ks' → ks'.failing = 1#32 →
      KittenBuildFailingPreserved ks ks' →
      (KittenMem kPtr ks' ⋆ R) m' → Q () m'

/-! ### Public `FullHdr *h` Entry Contracts (`6` fns, matching `FullDefSweep`) -/

def fullKittenInitSpec : Spec [i64, i32, i32] [] := fun (h, nv, track_ante, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat then
      Q () m
    else
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        let ks' := kittenStateOfScratch scr'
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        s'.LengthsOk c →
        (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
        KittenScratchInv scr' → KittenTrailSynced ks' →
        ks'.nv = nv → ks'.nc = 0#32 → ks'.orig_nc = 0#32 → ks'.lvl = 0#32 →
        ks'.prop = 0#32 → ks'.trl_end = 0#32 → ks'.unass = nv →
        ks'.incons = 0xFFFFFFFF#32 → ks'.failing = 0xFFFFFFFF#32 → ks'.ante = track_ante →
        ks'.nassump = 0#32 → ks'.nunits = 0#32 →
        kittenOrigClausesS scr' = [] → kittenAssumpLitsS scr' = [] →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullKittenAddClauseSpec : Spec [i64, i32, i64, i32] [.bool] :=
  fun (h, cid, lits_ptr, sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (scr xs : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.scratch.scratch_buf = scr ∧
      KittenScratchInv scr ∧ KittenTrailSynced (kittenStateOfScratch scr) ∧
      (kittenStateOfScratch scr).lvl = 0#32 ∧ (kittenStateOfScratch scr).trl_end = 0#32 ∧
      (kittenStateOfScratch scr).nc = (kittenStateOfScratch scr).orig_nc ∧
      sz.toNat ≤ xs.length ∧ sz.toNat < 2 ^ 16 ∧
      (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * (kittenStateOfScratch scr).nv.toNat) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) lits_ptr xs ⋆ R) m ∧
      ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
        let ks := kittenStateOfScratch scr
        let ks' := kittenStateOfScratch scr'
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < kBase, scr'[i]? = scr[i]?) →
        KittenScratchInv scr' → KittenTrailSynced ks' →
        ks'.lvl = 0#32 → ks'.trl_end = 0#32 → ks'.nv = ks.nv →
        ks'.nc = ks'.orig_nc → ks'.ante = ks.ante →
        ks'.nassump = ks.nassump → kittenAssumpLitsS scr' = kittenAssumpLitsS scr →
        (ok = false → scr' = scr) →
        (ok = true →
          ks'.orig_nc = ks.orig_nc + 1#32 ∧
          ks'.clAux[ks.orig_nc.toNat]? = some cid ∧
          (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) ∧
          (ks'.clMeta[ks.orig_nc.toNat]?.getD 0#32 &&& 0xFFFF#32) = sz ∧
          kittenOrigClausesS scr' =
            kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] ∧
          (∀ w < 2 * ks.nc.toNat, ks'.wblit[w]? = ks.wblit[w]?) ∧
          (2 ≤ sz.toNat →
            ks'.wblit[2 * ks.nc.toNat]? = xs[1]? ∧
            ks'.wblit[2 * ks.nc.toNat + 1]? = xs[0]?)) →
        (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
          array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) lits_ptr xs ⋆ R) m' →
        Q (ok, ()) m'

def fullKittenSolveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ KittenScratchInv s.scratch.scratch_buf ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr' } }
      let ks := kittenStateOfScratch s.scratch.scratch_buf
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
      KittenScratchInv scr' →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      KittenCnfPermEquiv (kittenOrigClausesS scr') (kittenOrigClausesS s.scratch.scratch_buf) →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (r ≠ 20#64 → ∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 →
        (ks'.incons ≠ 0xFFFFFFFF#32 ∨ ks'.failing ≠ 0xFFFFFFFF#32) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullKittenCoreSpec : Spec [i64] [i32] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    let ks0 := kittenStateOfScratch s.scratch.scratch_buf
    h = c.hdr ∧ s.LengthsOk c ∧ KittenScratchInv s.scratch.scratch_buf ∧
    ks0.ante ≠ 0#32 ∧ (ks0.incons ≠ 0xFFFFFFFF#32 ∨ ks0.failing ≠ 0xFFFFFFFF#32) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (csz : BitVec 32) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
      KittenScratchInv scr' →
      csz.toNat ≤ ks'.orig_nc.toNat →
      ks'.nv = ks0.nv → ks'.orig_nc = ks0.orig_nc → ks'.ante = ks0.ante →
      ks'.nassump = ks0.nassump →
      ks'.incons = ks0.incons → ks'.failing = ks0.failing →
      kittenOrigClausesS scr' = kittenOrigClausesS s.scratch.scratch_buf →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      (∀ ci < ks0.orig_nc.toNat, ks'.clAux[ci]? = ks0.clAux[ci]?) →
      (∀ cl ∈ kittenCoreClausesS scr', cl ∈ kittenOrigClausesS scr') →
      (cnfOfClauses (kittenCoreClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat →
      (FullMem c s' ⋆ R) m' → Q (csz, ()) m'

def fullKittenShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ KittenScratchInv s.scratch.scratch_buf ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := kittenStateOfScratch s.scratch.scratch_buf
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
      KittenScratchInv scr' → KittenTrailSynced ks' →
      ks'.nv = ks.nv → ks'.lvl = 0#32 → ks'.trl_end = 0#32 → ks'.nc = ks'.orig_nc →
      ks'.ante = ks.ante → ks'.nassump = ks.nassump →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      kittenOrigClausesS scr' = kittenCoreClausesS s.scratch.scratch_buf →
      (kittenOrigClausesS scr').Sublist (kittenOrigClausesS s.scratch.scratch_buf) →
      (∀ cl ∈ kittenOrigClausesS scr', cl ∈ kittenOrigClausesS s.scratch.scratch_buf) →
      ((List.range ks'.orig_nc.toNat).map (kittenClauseAux ks') =
        ((List.range ks.orig_nc.toNat).filter fun ci =>
          (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseAux ks)) →
      (∀ ci < ks'.orig_nc.toNat, (kittenClauseMeta ks' ci &&& kmCore) = 0#32) →
      KittenWblitInClause ks' →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullKittenFlipSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ KittenScratchInv s.scratch.scratch_buf ∧
    lit.toNat < 2 * (kittenStateOfScratch s.scratch.scratch_buf).nv.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := kittenStateOfScratch s.scratch.scratch_buf
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
      KittenScratchInv scr' →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      KittenCnfPermEquiv (kittenOrigClausesS scr') (kittenOrigClausesS s.scratch.scratch_buf) →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ### `15`-Row Specification Table & Environment -/

def fullKittenSpecTable : List SpecEntry :=
  [ ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  , ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  , ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  , ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  , ⟨"full_kitten_mtf", [i64, i32], [], fullKittenMtfSpec, true⟩
  , ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  , ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], fullKittenLearnUnit0Spec, true⟩
  , ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  , ⟨"full_kitten_ana_clause", [i64, i32, i32], [], fullKittenAnaClauseSpec, true⟩
  , ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  , ⟨"full_kitten_build_failing", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  , ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  , ⟨"full_kitten_core", [i64], [i32], fullKittenCoreSpec, true⟩
  , ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  , ⟨"full_kitten_flip", [i64, i32], [.bool], fullKittenFlipSpec, true⟩
  ]

def fullKittenEnv : Env :=
  Env.ofTable fullKittenSpecTable

theorem fullKittenSpecTable_noExit :
    ∀ e ∈ fullKittenSpecTable, e.noExit = true := by
  intro e he
  have hall : fullKittenSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fullKittenSpecTable_sigs :
    fullKittenSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fullKitten_fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full
