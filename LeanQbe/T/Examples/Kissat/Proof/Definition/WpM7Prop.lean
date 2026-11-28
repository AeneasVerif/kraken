/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Definition.SpecHelpers
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat M7 K6 Unit Propagation Preservation Proof (`Proof.Definition.WpM7Prop`)

Certifies `fullK6PropM7Spec` for `full_k6_prop_m7` on flat `CanonicalEnv`, split across
`k6_prop_search_repl_wp`, `k6_prop_reloc_watch_wp`, `k6_prop_nonbin_wp`,
`k6_prop_watch_loop_wp`, and `full_k6_prop_m7_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics K6Tactics

@[local bv_c0]
private theorem k6_ofnat_one :
    @OfNat.ofNat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (instOfNatNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) = 1 := rfl

public section

/-- Invariant maintained across `full_k6_prop_m7` and subcalls: `K6BufOk` holds, length is
unchanged, header scalars `[0..2]` and `[14..15]` are preserved, and clause descriptor tables
`[1888, 2656)` are preserved. -/
@[expose] def PropKeep (kbuf kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧
  kb[0]? = kbuf[0]? ∧ kb[1]? = kbuf[1]? ∧ kb[2]? = kbuf[2]? ∧
  kb[14]? = kbuf[14]? ∧ kb[15]? = kbuf[15]? ∧
  (∀ cid < 256,
    kb[1888 + cid]? = kbuf[1888 + cid]? ∧
    kb[2144 + cid]? = kbuf[2144 + cid]? ∧
    kb[2400 + cid]? = kbuf[2400 + cid]?)

/-- Reflexivity of `PropKeep` when `K6BufOk kbuf` holds. -/
theorem propKeep_refl {kbuf : List (BitVec 32)} (hok : K6BufOk kbuf) :
    PropKeep kbuf kbuf :=
  ⟨hok, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

/-- Frame preservation for `PropKeep` when header scalars `{0, 1, 2, 14, 15}` and clause
descriptor tables `[1888, 2656)` are preserved. -/
theorem propKeep_of_frame {kbuf kb kb' : List (BitVec 32)}
    (hpk : PropKeep kbuf kb) (hlen : kb'.length = kb.length)
    (hpres : ∀ idx < kb.length,
      (idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 14 ∨ idx = 15 ∨ (1888 ≤ idx ∧ idx < 2656)) →
      kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hge := hpk.1.base_ge
  refine ⟨k6BufOk_of_frame hpk.1 hlen (fun idx hi hor => ?_), hlen.trans hpk.2.1,
    ?_, ?_, ?_, ?_, ?_, fun cid hcid => ⟨?_, ?_, ?_⟩⟩
  · exact hpres idx hi (by rcases hor with rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)
  · rw [hpres 0 (by omega) (by omega)]; exact hpk.2.2.1
  · rw [hpres 1 (by omega) (by omega)]; exact hpk.2.2.2.1
  · rw [hpres 2 (by omega) (by omega)]; exact hpk.2.2.2.2.1
  · rw [hpres 14 (by omega) (by omega)]; exact hpk.2.2.2.2.2.1
  · rw [hpres 15 (by omega) (by omega)]; exact hpk.2.2.2.2.2.2.1
  · rw [hpres (1888 + cid) (by omega) (by omega)]; exact (hpk.2.2.2.2.2.2.2 cid hcid).1
  · rw [hpres (2144 + cid) (by omega) (by omega)]; exact (hpk.2.2.2.2.2.2.2 cid hcid).2.1
  · rw [hpres (2400 + cid) (by omega) (by omega)]; exact (hpk.2.2.2.2.2.2.2 cid hcid).2.2

/-- Updating any buffer slot outside `{0, 1, 2, 14, 15}` and `[1888, 2656)` preserves
`PropKeep`. -/
theorem propKeep_set {kbuf kb : List (BitVec 32)} (hpk : PropKeep kbuf kb) {idx : Nat}
    (hidx : idx ≠ 0 ∧ idx ≠ 1 ∧ idx ≠ 2 ∧ idx ≠ 14 ∧ idx ≠ 15 ∧ ¬(1888 ≤ idx ∧ idx < 2656))
    (val : BitVec 32) :
    PropKeep kbuf (kb.set idx val) :=
  propKeep_of_frame hpk (by simp) fun j _ hj => by
    rw [List.getElem?_set_ne (by rcases hj with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)]

/-- Postcondition of `full_k6_assign_m7` preserves `PropKeep`. -/
theorem propKeep_of_assign {kbuf kb kb' : List (BitVec 32)}
    (hpk : PropKeep kbuf kb) (hlen : kb'.length = kb.length)
    (hpres : ∀ idx < kb.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
      (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' :=
  propKeep_of_frame hpk hlen fun idx hi hor =>
    hpres idx hi (by rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)
      (by rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;> omega)

end

private def pDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (pDflt a, pDflt b)

private def pDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (pDflt t, pDfltT r)

private def pSL2 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (pDfltT t1) with
    | .let_ (ts := t2) _ k2 => k2 (pDfltT t2) | _ => .hlt
  | _ => .hlt

private def pSL3 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (pDfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (pDfltT t2) with
      | .let_ (ts := t3) _ k3 => k3 (pDfltT t3) | _ => .hlt
    | _ => .hlt
  | _ => .hlt

private def pSL4 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (pDfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (pDfltT t2) with
      | .let_ (ts := t3) _ k3 => match k3 (pDfltT t3) with
        | .let_ (ts := t4) _ k4 => k4 (pDfltT t4) | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt

private def pSLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (pDfltT ts) | _ => .hlt

private def pSLetI {L rs} (v : BitVec 32) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt

private def pSLetI64 {L rs} (v : BitVec 64) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ()) | _ => .hlt

private def pSLd {L rs} (v : BitVec 32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt

private def pSLd3 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs := pSLd v (pSL3 e)

private def pSLd4 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs := pSLd v (pSL4 e)

private def pSSt {L rs} : Expr Val L rs → Expr Val L rs
  | .store _ _ e => e | _ => .hlt

private def pSJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt

private def pSJT {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ e _ => e | _ => .hlt

private def pSGrpB64 {rs} (Jout : Cont [.bits 64]) (x : BitVec 64) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bs _ =>
      match bs (Jout, ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def pSGrpKN {rs} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ k => k (J, ()) | _ => .hlt

private def pSGrpK3 {rs} (J : Cont [.bits 32, .bits 32, .bits 32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) _ k => k (J, ()) | _ => .hlt

private def pSGrpB3 {rs} (a b c : BitVec 32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons fn _ => fn (a, b, c, ())
  | _ => .hlt

private def pOuter (pk : BitVec 64) (nc nv acap : BitVec 32)
    (Jout : Cont [.bits 64]) (ticks : BitVec 64) : Expr Val Cont [i32] :=
  let e := pSLd3 nc (full_k6_prop_m7_body Val Cont (pk, ()))
  let e := pSJF (pSLet (pSJF (pSLet (pSLd3 acap (pSLd3 nv e)))))
  pSGrpB64 Jout ticks e

private def pWatchLoopGrpE (pk : BitVec 64) (nc nv acap lit hd : BitVec 32)
    (Jout : Cont [.bits 64]) (ticks : BitVec 64) (Jcfl : Cont []) : Expr Val Cont [i32] :=
  let e := pSGrpKN Jcfl (pOuter pk nc nv acap Jout ticks)
  let e := pSJT (pSLet (pSLd3 0#32 (pSLd3 0#32 e)))
  let e := pSJT (pSLet (pSLd3 0#32 e))
  let e := pSLd lit (pSL4 (pSLd3 0#32 e))
  let e := pSJF (pSLet (pSLet (pSSt (pSLet (pSLd3 0#32 (pSL3 e))))))
  pSLd4 hd (pSLetI (lit ^^^ 1#32) e)

private def pNonBinE (pk : BitVec 64) (nc nv acap lit prev wi steps w nxt : BitVec 32)
    (Jout : Cont [.bits 64]) (ticks cnt : BitVec 64) (Jcfl : Cont [])
    (Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32])
    (Jexit : Cont []) : Expr Val Cont [i32] :=
  let e := pSGrpKN Jexit (match pWatchLoopGrpE pk nc nv acap lit 0#32 Jout ticks Jcfl with
    | .group (sig := [[.bits 64, .bits 64, .bits 32, .bits 32, .bits 32]]) bs _ =>
        match bs (Lw, ()) with | .cons b _ => b (ticks, cnt, prev, wi, steps, ())
    | _ => .hlt)
  let e := pSJT (pSLet (pSJT (pSL2 e)))
  let e := pSLd4 w (pSLetI64 (cnt + 1#64) (pSLd4 nxt (pSLetI (steps + 1#32) e)))
  let e := pSJF (pSL3 e)
  let e := pSJF (pSLet (pSLd4 0#32 e))
  pSJF (pSL2 (pSLetI (wi >>> (1 : Nat)) e))

private def pRelocGrpE (pk : BitVec 64) (nc nv acap lit prev wi steps w nxt off cm other :
    BitVec 32) (Jout : Cont [.bits 64]) (ticks cnt : BitVec 64) (Jcfl : Cont [])
    (Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32])
    (Jexit : Cont []) : Expr Val Cont [i32] :=
  let e := pNonBinE pk nc nv acap lit prev wi steps w nxt Jout ticks cnt Jcfl Lw Jexit
  let e := pSJF (pSLet (pSLetI (cm &&& 0xFFFF#32)
    (pSLd4 cm (pSLd4 off (pSLetI (wi &&& 1#32) e)))))
  let e := pSJF (pSL2 (pSLd other (pSL2 (pSL4 (pSJF (pSL2 e))))))
  pSLetI64 (ticks + 1#64) (pSJF (pSLet (pSLd4 0#32 e)))

private def pRelocE (pk : BitVec 64) (nc nv acap lit prev wi steps w nxt off cm other u ri rl :
    BitVec 32) (Jout : Cont [.bits 64]) (ticks cnt : BitVec 64) (Jcfl : Cont [])
    (Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32])
    (Jexit : Cont []) : Expr Val Cont [i32] :=
  pSGrpB3 u ri rl (pRelocGrpE pk nc nv acap lit prev wi steps w nxt off cm other
    Jout ticks cnt Jcfl Lw Jexit)

private def pSearchReplGrpE (pk : BitVec 64) (nc nv acap lit prev wi steps w nxt off cm other :
    BitVec 32) (Jout : Cont [.bits 64]) (ticks cnt : BitVec 64) (Jcfl : Cont [])
    (Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32])
    (Jexit : Cont []) (Jreloc : Cont [.bits 32, .bits 32, .bits 32]) : Expr Val Cont [i32] :=
  pSGrpK3 Jreloc (pRelocGrpE pk nc nv acap lit prev wi steps w nxt off cm other
    Jout ticks cnt Jcfl Lw Jexit)

private theorem propKeep_to_Q {pk : BitVec 64} {kbuf kb' : List (BitVec 32)}
    {R : Mem 64 → Prop} {Q : Post [i32]} {m' : Mem 64}
    (hQ : ∀ (r : Val i32) (kb' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kb' → kb'.length = kbuf.length →
      kb'[0]? = kbuf[0]? → kb'[1]? = kbuf[1]? → kb'[2]? = kbuf[2]? → kb'[15]? = kbuf[15]? →
      (∀ cid < 256, kb'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kb'[2144 + cid]? = kbuf[2144 + cid]? ∧ kb'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kb' ⋆ R) m' → Q (r, ()) m')
    (hpk : PropKeep kbuf kb') (hm' : (array (t := i32) pk kb' ⋆ R) m') (r : Val i32) :
    Q (r, ()) m' :=
  hQ r kb' m' hpk.1 hpk.2.1 hpk.2.2.1 hpk.2.2.2.1 hpk.2.2.2.2.1 hpk.2.2.2.2.2.2.1
    hpk.2.2.2.2.2.2.2 hm'

private theorem propKeep_store_ex {kbuf kb : List (BitVec 32)} {pk : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : Nat} {val : BitVec 32} {qh1 : BitVec 32}
    (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hm : (array (t := i32) pk (kb.set idx val) ⋆ R) m)
    (hidx : idx ≠ 0 ∧ idx ≠ 1 ∧ idx ≠ 2 ∧ idx ≠ 4 ∧ idx ≠ 14 ∧ idx ≠ 15 ∧
      ¬(1888 ≤ idx ∧ idx < 2656)) :
    ∃ kb', PropKeep kbuf kb' ∧ kb'[4]? = some qh1 ∧ (array (t := i32) pk kb' ⋆ R) m :=
  ⟨kb.set idx val,
    propKeep_set hpk ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.2.1, hidx.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2⟩ val,
    by rw [List.getElem?_set_ne hidx.2.2.2.1]; exact hqh, hm⟩

private theorem propKeep_store_ge2656 {kbuf kb : List (BitVec 32)} {pk : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : Nat} {val qh1 : BitVec 32}
    (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hm : (array (t := i32) pk (kb.set idx val) ⋆ R) m) (hge : 2656 ≤ idx) :
    ∃ kb', PropKeep kbuf kb' ∧ kb'[4]? = some qh1 ∧ (array (t := i32) pk kb' ⋆ R) m :=
  propKeep_store_ex hpk hqh hm ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

private theorem propKeep_store_safe {kbuf kb : List (BitVec 32)} {pk : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : Nat} {val qh1 : BitVec 32}
    (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hm : (array (t := i32) pk (kb.set idx val) ⋆ R) m)
    (hsafe : 16 ≤ idx ∧ (idx < 1888 ∨ 2656 ≤ idx)) :
    ∃ kb', PropKeep kbuf kb' ∧ kb'[4]? = some qh1 ∧ (array (t := i32) pk kb' ⋆ R) m :=
  propKeep_store_ex hpk hqh hm ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

private theorem k6_prop_assign_call_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {kbuf kb : List (BitVec 32)} {lit cid qh1 : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [i32]} {X : XPost} {k : Tup Val [] → Expr Val Cont [i32]}
    {m : Mem 64} (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hm : (array (t := i32) pk kb ⋆ R) m)
    (hk : ∀ kb' m', PropKeep kbuf kb' → kb'[4]? = some qh1 →
      (array (t := i32) pk kb' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_m7"
      (Arg.var pk, Arg.var lit, Arg.var cid, ()) k) m := by
  refine wp_call_of_spec _ _ (Spec.has_full_k6_assign_m7 hΓ _ _ _ _ ?_)
  have hge := hpk.1.base_ge
  refine fullK6AssignM7Spec_intro (kbuf := kb) (R := R) (by omega) hm ?_
  intro kb' m' hlen' hpres' hm'
  exact hk kb' m' (propKeep_of_assign hpk hlen' hpres')
    (by rw [hpres' 4 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide)),
      hqh]) hm'

private theorem k6_prop_search_repl_wp {Γ : Env} {pk : BitVec 64} {kbuf kb : List (BitVec 32)}
    {nc nv acap lit prev wi steps w nxt off cm other : BitVec 32}
    {Jout : Cont [.bits 64]} {ticks cnt : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i32]}
    {X : XPost} {Jcfl : Cont []}
    {Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32]}
    {Jexit : Cont []} {Jreloc : Cont [.bits 32, .bits 32, .bits 32]} {m : Mem 64}
    (hnv_le : nv.toNat ≤ 64) (hpk : PropKeep kbuf kb)
    (_hkb0 : kb[0]? = some nv) (hkb15 : kb[15]? = some acap)
    (hosz_le : off.toNat + (cm &&& 0xFFFF#32).toNat ≤ acap.toNat)
    (hsz2 : 2 ≤ (cm &&& 0xFFFF#32).toNat)
    (hJreloc : ∀ u ri rl : BitVec 32,
      (ri = 0xFFFFFFFF#32 ∨ (ri.toNat < (cm &&& 0xFFFF#32).toNat ∧ rl.toNat < 2 * nv.toNat)) →
      Jreloc (u, ri, rl, ()) m)
    (hm : (array (t := i32) pk kb ⋆ R) m) :
    wp Γ Q X (pSearchReplGrpE pk nc nv acap lit prev wi steps w nxt off cm other
      Jout ticks cnt Jcfl Lw Jexit Jreloc) m := by
  dsimp only [pSearchReplGrpE, pRelocGrpE, pNonBinE, pWatchLoopGrpE, pOuter, pSGrpK3, pSGrpKN,
    pSGrpB64, pSLd4, pSLd3, pSL4, pSL3, pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet,
    pDfltT, pDflt, Prod.fst]
  let sz := cm &&& 0xFFFF#32
  have hsz_mod : sz.toNat = cm.toNat % 65536 := by
    dsimp only [sz]; rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod cm.toNat 16
  have hsz_lt : sz.toNat < 65536 := by rw [hsz_mod]; exact Nat.mod_lt _ (by decide)
  have hge := hpk.1.base_ge; have hlt28 := hpk.1.length_lt; have hbuf_sz := hpk.1.1
  have h15 : (kb[15]?.getD 0#32).toNat = acap.toNat := by rw [hkb15]; rfl
  refine wp_loop_group (ts := [i32])
    (fun rem (k, ()) m' => m' = m ∧ k.toNat ≤ sz.toNat ∧ rem = sz.toNat - k.toNat) ?_ ?_
  · rintro Lk remk ⟨k, ⟨⟩⟩ m' hLk ⟨hm_eq, hk_le, rfl⟩
    subst hm_eq
    c0_hsplit
    · have hk_lt' : k.toNat < cm.toNat % 65536 := hc
      have hk_lt : k.toNat < sz.toNat := hsz_mod ▸ hc
      have hosz_le' : off.toNat + cm.toNat % 65536 ≤ acap.toNat := hsz_mod ▸ hosz_le
      clear hc
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by have := hsz_lt; have := hk_lt; c0_bound
      have hidx_eq : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + k)).toNat =
          2912 + off.toNat + k.toNat := by
        have := hosz_le'; have := hk_lt'; c0_bound
      have hidx_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + k)).toNat < kb.length := by
        rw [hidx_eq]; have := hk_lt'; omega
      c0_hsteps_nogrp
      refine wp_join0 (fun m1 => m1 = m') ?_ ?_
      · intro _ m1 hm1; subst hm1; c0_hsteps!
        exact hLk (sz.toNat - (k + 1#32).toNat) (k + 1#32, ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
      · intro Jnext hJnext
        let lk := kb[(BitVec.setWidth 64 ((2912 : BitVec 32) + off + k)).toNat]'hidx_c0
        c0_hsplit
        · have hlk_c0 :
              kb[(BitVec.toNat (2912 : BitVec 32) + off.toNat + BitVec.toNat k) % 2 ^ 32]'(by
                refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
                have h2912n : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
                have := hbuf_sz; have := h15; have := hosz_le'; have := hk_lt'; omega) = lk :=
            m8_k6_get_congr (by
              have h2912n : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
              have hlt32 : 2912 + off.toNat + BitVec.toNat k < 2 ^ 32 := by
                have := hbuf_sz; have := h15; have := hosz_le'; have := hk_lt'; omega
              rw [h2912n, hidx_eq, Nat.mod_eq_of_lt hlt32]) _ _
          have hlk_lt : lk.toNat < 2 * nv.toNat := by
            rw [hlk_c0] at hc; have := hnv_le; omega
          clear hc
          have h608_c0 : (BitVec.setWidth 64 ((608 : BitVec 32) + lk)).toNat < kb.length := by
            have := hnv_le; have := hlk_lt; c0_bound
          c0_hsplit
          · c0_hsteps!; exact hJreloc k k lk (Or.inr ⟨hk_lt, hlk_lt⟩)
          · c0_hsteps!; exact hJnext m' rfl
        · c0_hsteps!; exact hJnext m' rfl
    · c0_hsteps!; exact hJreloc k 0xFFFFFFFF#32 0#32 (Or.inl rfl)
  · intro L0 hL0; c0_hsteps!; exact hL0 (sz.toNat - 2) (2#32, ()) m ⟨rfl, hsz2, rfl⟩

private theorem k6_prop_cfl_close {pk : BitVec 64} {kbuf kb : List (BitVec 32)}
    {R : Mem 64 → Prop} {Q : Post [i32]} {m : Mem 64} {idx : Nat} {val ret : BitVec 32}
    (hQ : ∀ (r : Val i32) (kb' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kb' → kb'.length = kbuf.length →
      kb'[0]? = kbuf[0]? → kb'[1]? = kbuf[1]? → kb'[2]? = kbuf[2]? → kb'[15]? = kbuf[15]? →
      (∀ cid < 256, kb'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kb'[2144 + cid]? = kbuf[2144 + cid]? ∧ kb'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kb' ⋆ R) m' → Q (r, ()) m')
    (hpk : PropKeep kbuf kb)
    (hm : (array (t := i32) pk (kb.set idx val) ⋆ R) m) (hidx : idx = 12) :
    Q (ret, ()) m := by
  subst hidx
  exact propKeep_to_Q hQ (propKeep_set hpk ⟨by omega, by omega, by omega, by omega, by omega,
    by omega⟩ val) hm ret

private theorem k6_prop_reloc_watch_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs) {pk : BitVec 64}
    {kbuf kb : List (BitVec 32)}
    {nc nv acap lit prev wi steps w nxt off cm other u ri rl qh1 : BitVec 32}
    {Jout : Cont [.bits 64]} {ticks cnt : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i32]}
    {X : XPost} {Jcfl : Cont []}
    {Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32]}
    {Jexit : Cont []} {m : Mem 64}
    (hnv_le : nv.toNat ≤ 64) (hnc_le : nc.toNat ≤ 256)
    (hQ : ∀ (r : Val i32) (kb' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kb' → kb'.length = kbuf.length →
      kb'[0]? = kbuf[0]? → kb'[1]? = kbuf[1]? → kb'[2]? = kbuf[2]? → kb'[15]? = kbuf[15]? →
      (∀ cid < 256, kb'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kb'[2144 + cid]? = kbuf[2144 + cid]? ∧ kb'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kb' ⋆ R) m' → Q (r, ()) m')
    (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hkb1 : kb[1]? = some nc) (hkb15 : kb[15]? = some acap)
    (hwi : wi.toNat < 2 * nc.toNat) (hsteps1 : (steps + 1#32).toNat ≤ 512)
    (hlit : lit.toNat < 2 * nv.toNat) (hoth : other.toNat < 2 * nv.toNat)
    (hosz_le : off.toNat + (cm &&& 0xFFFF#32).toNat ≤ acap.toNat)
    (hsz2 : 2 ≤ (cm &&& 0xFFFF#32).toNat)
    (hri : ri = 0xFFFFFFFF#32 ∨ (ri.toNat < (cm &&& 0xFFFF#32).toNat ∧ rl.toNat < 2 * nv.toNat))
    (hLw : ∀ kb' m' (ticks' cnt' : BitVec 64) (prev' wi' steps' : BitVec 32),
      PropKeep kbuf kb' → kb'[4]? = some qh1 →
      (steps + 1#32).toNat ≤ steps'.toNat → steps'.toNat ≤ 512 →
      (array (t := i32) pk kb' ⋆ R) m' → Lw (ticks', cnt', prev', wi', steps', ()) m')
    (hm : (array (t := i32) pk kb ⋆ R) m) :
    wp Γ Q X (pRelocE pk nc nv acap lit prev wi steps w nxt off cm other u ri rl
      Jout ticks cnt Jcfl Lw Jexit) m := by
  dsimp only [pRelocE, pRelocGrpE, pNonBinE, pWatchLoopGrpE, pOuter, pSGrpB3, pSGrpKN,
    pSGrpB64, pSLd4, pSLd3, pSL4, pSL3, pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet,
    pDfltT, pDflt, Prod.fst]
  have hge := hpk.1.base_ge; have hlt28 := hpk.1.length_lt; have hbuf_sz := hpk.1.1
  have h15 : (kb[15]?.getD 0#32).toNat = acap.toNat := by rw [hkb15]; rfl
  have h1 : (kb[1]?.getD 0#32).toNat = nc.toNat := by rw [hkb1]; rfl
  have hslot_le : (wi &&& 1#32).toNat ≤ 1 := by
    rw [BitVec.toNat_and]; exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
  have hnl : (lit ^^^ 1#32).toNat < 2 * nv.toNat := (m8_bv32_xor1_lt lit hlit).2
  have hnc_shl : (nc <<< (1 : Nat)).toNat = 2 * nc.toNat := by
    rw [K6Tactics.k6_bv32_shl1]; exact Nat.mod_eq_of_lt (by omega)
  c0_hsplit
  · have hri' : ri.toNat < (cm &&& 0xFFFF#32).toNat ∧ rl.toNat < 2 * nv.toNat := by
      rcases hri with hri_eq | h
      · exact absurd hri_eq hc
      · exact h
    have h2912_s_eq : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + (wi &&& 1#32))).toNat =
        2912 + off.toNat + (wi &&& 1#32).toNat := by
      have := hosz_le; have := hslot_le; have := hsz2; have := hbuf_sz; c0_bound
    have h2912_s_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + (wi &&& 1#32))).toNat <
        kb.length := by
      rw [h2912_s_eq]; omega
    iterate 5 c0_hstep; try dsimp only [Prod.fst]
    c0_hstep; rw [m8_k6_set_congr h2912_s_eq rfl] at hm
    obtain ⟨kb1, hk1, hqh1, hm1⟩ := propKeep_store_ge2656 hpk hqh hm (by omega)
    clear hm
    have hge1 := hk1.1.base_ge; have hlt28_1 := hk1.1.length_lt; have hbuf_sz1 := hk1.1.1
    have h15_1 : (kb1[15]?.getD 0#32).toNat = acap.toNat := by
      rw [hk1.2.2.2.2.2.2.1, ← hpk.2.2.2.2.2.2.1, hkb15]; rfl
    have h2912_r_eq : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + ri)).toNat =
        2912 + off.toNat + ri.toNat := by
      have := hosz_le; have := hri'.1; have := hbuf_sz1; c0_bound
    have h2912_r_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off + ri)).toNat <
        kb1.length := by
      rw [h2912_r_eq]; omega
    iterate 5 c0_hstep; try dsimp only [Prod.fst]
    c0_hstep; rw [m8_k6_set_congr h2912_r_eq rfl] at hm
    obtain ⟨kb2, hk2, hqh2, hm2⟩ := propKeep_store_ge2656 hk1 hqh1 hm (by omega)
    clear hm
    refine wp_join0 (fun mj => ∃ kbj, PropKeep kbuf kbj ∧ kbj[4]? = some qh1 ∧
        (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
    · intro _ mj ⟨kbj, hkj, hj4, hmj⟩
      have hgej := hkj.1.base_ge
      have h1376_eq : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat = 1376 + wi.toNat := by
        have := hwi; have := hnc_le; c0_bound
      have h1376_c0 : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat < kbj.length := by
        rw [h1376_eq]; have := hwi; have := hnc_le; omega
      iterate 4 c0_hstep; try dsimp only [Prod.fst]
      c0_hstep; rw [m8_k6_set_congr h1376_eq rfl] at hm
      obtain ⟨kbj1, hkj1, hqh1j, hm1j⟩ := propKeep_store_safe hkj hj4 hm (by omega)
      clear hm
      have hge1j := hkj1.1.base_ge
      have h864_eq : (BitVec.setWidth 64 ((864 : BitVec 32) + wi)).toNat = 864 + wi.toNat := by
        have := hwi; have := hnc_le; c0_bound
      have h736_eq : (BitVec.setWidth 64 ((736 : BitVec 32) + rl)).toNat =
          736 + rl.toNat := by
        have := hri'.2; have := hnv_le; c0_bound
      have h864_c0 : (BitVec.setWidth 64 ((864 : BitVec 32) + wi)).toNat < kbj1.length := by
        rw [h864_eq]; have := hwi; have := hnc_le; omega
      have h736_c0 : (BitVec.setWidth 64 ((736 : BitVec 32) + rl)).toNat < kbj1.length := by
        rw [h736_eq]; have := hri'.2; have := hnv_le; omega
      iterate 9 c0_hstep; try dsimp only [Prod.fst]
      c0_hstep; rw [m8_k6_set_congr h864_eq rfl] at hm
      obtain ⟨kbj2, hkj2, hqh2j, hm2j⟩ := propKeep_store_safe hkj1 hqh1j hm (by omega)
      clear hm
      have hge2j := hkj2.1.base_ge
      have h736_c02 : (BitVec.setWidth 64 ((736 : BitVec 32) + rl)).toNat < kbj2.length := by
        rw [h736_eq]; have := hri'.2; have := hnv_le; omega
      c0_hsteps!; rw [m8_k6_set_congr h736_eq rfl] at hm
      obtain ⟨kbj3, hkj3, hqh3j, hm3j⟩ := propKeep_store_safe hkj2 hqh2j hm (by omega)
      exact hLw kbj3 _ _ _ _ _ _ hkj3 hqh3j (by omega) hsteps1 hm3j
    · intro J136 hJ136
      have hge2 := hk2.1.base_ge
      c0_hsplit
      · clear hc
        have h736_eq : (BitVec.setWidth 64 ((736 : BitVec 32) + (lit ^^^ 1#32))).toNat =
            736 + (lit ^^^ 1#32).toNat := by
          have := hnl; have := hnv_le; c0_bound
        have h736_c0 : (BitVec.setWidth 64 ((736 : BitVec 32) + (lit ^^^ 1#32))).toNat <
            kb2.length := by
          rw [h736_eq]; have := hnl; have := hnv_le; omega
        c0_hsteps!; rw [m8_k6_set_congr h736_eq rfl] at hm
        obtain ⟨kb3, hk3, hqh3, hm3⟩ := propKeep_store_ex hk2 hqh2 hm
          ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
        exact hJ136 _ ⟨kb3, hk3, hqh3, hm3⟩
      · have hprev : prev.toNat < 2 * nc.toNat :=
          Nat.lt_of_not_le fun h => hc (by have := hnc_le; omega)
        clear hc
        have h864_eq : (BitVec.setWidth 64 ((864 : BitVec 32) + prev)).toNat =
            864 + prev.toNat := by
          have := hprev; have := hnc_le; c0_bound
        have h864_c0 : (BitVec.setWidth 64 ((864 : BitVec 32) + prev)).toNat < kb2.length := by
          rw [h864_eq]; have := hprev; have := hnc_le; omega
        c0_hsteps!; rw [m8_k6_set_congr h864_eq rfl] at hm
        obtain ⟨kb3, hk3, hqh3, hm3⟩ := propKeep_store_ex hk2 hqh2 hm
          ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
        exact hJ136 _ ⟨kb3, hk3, hqh3, hm3⟩
  · clear hc
    have h1376_eq : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat = 1376 + wi.toNat := by
      have := hwi; have := hnc_le; c0_bound
    have h1376_c0 : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat < kb.length := by
      rw [h1376_eq]; have := hwi; have := hnc_le; omega
    iterate 4 c0_hstep; try dsimp only [Prod.fst]
    c0_hstep; rw [m8_k6_set_congr h1376_eq rfl] at hm
    obtain ⟨kb1, hk1, hqh1, hm1⟩ := propKeep_store_safe hpk hqh hm (by omega)
    clear hm
    have hge1 := hk1.1.base_ge
    have h608_c0 : (BitVec.setWidth 64 ((608 : BitVec 32) + other)).toNat < kb1.length := by
      have := hoth; have := hnv_le; c0_bound
    c0_hsplit
    · clear hc; c0_hsteps!
      exact k6_prop_cfl_close hQ hk1 (by assumption) (by decide)
    · clear hc
      refine wp_join0 (fun mj => ∃ kbj, PropKeep kbuf kbj ∧ kbj[4]? = some qh1 ∧
          (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
      · intro _ mj ⟨kbj, hkj, hj4, hmj⟩; c0_hsteps!
        exact hLw kbj _ _ _ _ _ _ hkj hj4 (by omega) hsteps1 hmj
      · intro J136 hJ136
        c0_hsplit
        · clear hc
          exact k6_prop_assign_call_wp hΓ hk1 hqh1 hm1 fun kb2 m2 hk2 hqh2 hm2 => by
            c0_hsteps!; exact hJ136 _ ⟨kb2, hk2, hqh2, hm2⟩
        · clear hc; c0_hsteps!; exact hJ136 _ ⟨kb1, hk1, hqh1, hm1⟩

private theorem k6_prop_nonbin_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs) {pk : BitVec 64}
    {kbuf kb : List (BitVec 32)} {nc nv acap lit prev wi steps w nxt qh1 : BitVec 32}
    {Jout : Cont [.bits 64]} {ticks cnt : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i32]}
    {X : XPost} {Jcfl : Cont []}
    {Lw : Cont [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32]}
    {Jexit : Cont []} {m : Mem 64}
    (hnv_le : nv.toNat ≤ 64) (hnc_le : nc.toNat ≤ 256)
    (hQ : ∀ (r : Val i32) (kb' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kb' → kb'.length = kbuf.length →
      kb'[0]? = kbuf[0]? → kb'[1]? = kbuf[1]? → kb'[2]? = kbuf[2]? → kb'[15]? = kbuf[15]? →
      (∀ cid < 256, kb'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kb'[2144 + cid]? = kbuf[2144 + cid]? ∧ kb'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kb' ⋆ R) m' → Q (r, ()) m')
    (hpk : PropKeep kbuf kb) (hqh : kb[4]? = some qh1)
    (hkb0 : kb[0]? = some nv) (hkb1 : kb[1]? = some nc) (hkb15 : kb[15]? = some acap)
    (hwi : wi.toNat < 2 * nc.toNat) (hsteps1 : (steps + 1#32).toNat ≤ 512)
    (hlit : lit.toNat < 2 * nv.toNat)
    (hLw : ∀ kb' m' (ticks' cnt' : BitVec 64) (prev' wi' steps' : BitVec 32),
      PropKeep kbuf kb' → kb'[4]? = some qh1 →
      (steps + 1#32).toNat ≤ steps'.toNat → steps'.toNat ≤ 512 →
      (array (t := i32) pk kb' ⋆ R) m' → Lw (ticks', cnt', prev', wi', steps', ()) m')
    (hm : (array (t := i32) pk kb ⋆ R) m) :
    wp Γ Q X (pNonBinE pk nc nv acap lit prev wi steps w nxt
      Jout ticks cnt Jcfl Lw Jexit) m := by
  dsimp only [pNonBinE, pWatchLoopGrpE, pOuter, pSGrpKN, pSGrpB64, pSLd4, pSLd3, pSL4, pSL3,
    pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet, pDfltT, pDflt, Prod.fst]
  have hge := hpk.1.base_ge; have hlt28 := hpk.1.length_lt; have hbuf_sz := hpk.1.1
  have h15 : (kb[15]?.getD 0#32).toNat = acap.toNat := by rw [hkb15]; rfl
  have hcid := (m7_p6_shr1_lt (n := nc.toNat) (l := wi) hwi).2
  have h1888_c0 : (BitVec.setWidth 64 ((1888 : BitVec 32) + (wi >>> (1 : Nat)))).toNat <
      kb.length := by
    have := hcid; have := hnc_le; c0_bound
  have h2144_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) + (wi >>> (1 : Nat)))).toNat <
      kb.length := by
    have := hcid; have := hnc_le; c0_bound
  let off := kb[(BitVec.setWidth 64 ((1888 : BitVec 32) + (wi >>> (1 : Nat)))).toNat]'h1888_c0
  let cm := kb[(BitVec.setWidth 64 ((2144 : BitVec 32) + (wi >>> (1 : Nat)))).toNat]'h2144_c0
  let sz := cm &&& 0xFFFF#32
  have hsz_mod : sz.toNat = cm.toNat % 65536 := by
    dsimp only [sz]; rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod cm.toNat 16
  c0_hsplit
  · c0_hsteps!
    exact hLw kb m ticks (cnt + 1#64) wi nxt (steps + 1#32) hpk hqh (by omega) hsteps1 hm
  · have hsz2 : 2 ≤ sz.toNat := by rw [hsz_mod]; exact Nat.le_of_not_lt hc
    clear hc
    have hsz_lt : sz.toNat < 65536 := by
      dsimp only [sz]; rw [BitVec.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hcl_ok := hpk.1.clause_ok (by rw [hkb1]; exact hcid)
    have hoff_eq : off = kb[1888 + (wi >>> (1 : Nat)).toNat]'
        (by have := hcid; have := hnc_le; omega) :=
      m8_k6_get_congr (by have := hcid; have := hnc_le; c0_bound) _ _
    have hcm_eq : cm = kb[2144 + (wi >>> (1 : Nat)).toNat]'
        (by have := hcid; have := hnc_le; omega) :=
      m8_k6_get_congr (by have := hcid; have := hnc_le; c0_bound) _ _
    have hosz_le : off.toNat + sz.toNat ≤ acap.toNat := by
      rw [hoff_eq]; dsimp only [sz]; rw [hcm_eq]
      rw [m8_k6_get_eq (by have := hcid; have := hnc_le; omega),
        m8_k6_get_eq (by have := hcid; have := hnc_le; omega), h15] at hcl_ok
      exact hcl_ok.1
    c0_hsplit
    · c0_hsteps!
      exact hLw kb m ticks (cnt + 1#64) wi nxt (steps + 1#32) hpk hqh (by omega) hsteps1 hm
    · clear hc
      have hslot_le : (wi &&& 1#32).toNat ≤ 1 := by
        rw [BitVec.toNat_and]
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
      have hslot_x_le : ((wi &&& 1#32) ^^^ 1#32).toNat ≤ 1 := by
        rcases (by omega : (wi &&& 1#32).toNat = 0 ∨ (wi &&& 1#32).toNat = 1) with hw | hw
        · have hw' : wi &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq hw; rw [hw']; decide
        · have hw' : wi &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq hw; rw [hw']; decide
      have hslot_x_nat : (wi &&& 1#32).toNat ^^^ 1 ≤ 1 := by
        simpa [BitVec.toNat_xor] using hslot_x_le
      have hoth_idx_eq : (BitVec.setWidth 64
          ((2912 : BitVec 32) + off + ((wi &&& 1#32) ^^^ 1#32))).toNat =
          2912 + off.toNat + ((wi &&& 1#32) ^^^ 1#32).toNat := by
        rcases (by omega : (wi &&& 1#32).toNat = 0 ∨ (wi &&& 1#32).toNat = 1) with hw | hw
        · have hw' : wi &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq hw
          have h0x : (0#32 ^^^ 1#32) = 1#32 := by decide
          have h32 : 2912 + off.toNat + 1 < 2 ^ 32 := by
            have := hosz_le; have := hsz2; have := hbuf_sz; have := hlt28; have := h15; omega
          have h64 : 2912 + off.toNat + 1 < 2 ^ 64 := by omega
          rw [hw', h0x]
          simp [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h32,
            Nat.mod_eq_of_lt h64]
        · have hw' : wi &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq hw
          have h1x : (1#32 ^^^ 1#32) = 0#32 := by decide
          have h32 : 2912 + off.toNat < 2 ^ 32 := by
            have := hosz_le; have := hsz2; have := hbuf_sz; have := hlt28; have := h15; omega
          have h64 : 2912 + off.toNat < 2 ^ 64 := by omega
          rw [hw', h1x]
          simp [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h32,
            Nat.mod_eq_of_lt h64]
      have hoth_c0 : (BitVec.setWidth 64
          ((2912 : BitVec 32) + off + ((wi &&& 1#32) ^^^ 1#32))).toNat < kb.length := by
        rw [hoth_idx_eq]; have := hbuf_sz; have := hslot_x_nat; omega
      let other := kb[(BitVec.setWidth 64
        ((2912 : BitVec 32) + off + ((wi &&& 1#32) ^^^ 1#32))).toNat]'hoth_c0
      c0_hsplit
      · c0_hsteps!
        exact hLw kb m ticks (cnt + 1#64) wi nxt (steps + 1#32) hpk hqh (by omega) hsteps1 hm
      · have hoff_bd : (BitVec.toNat (1888 : BitVec 32) + wi.toNat / 2) % 2 ^ 32 < kb.length := by
          refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
          have h1888n : BitVec.toNat (1888 : BitVec 32) = 1888 := rfl
          have := hcid; have := hnc_le; omega
        have hoff_c0 : kb[(BitVec.toNat (1888 : BitVec 32) + wi.toNat / 2) % 2 ^ 32]'hoff_bd =
            off := by
          dsimp only [off]
          exact m8_k6_get_congr (by
            have h1888_lt : 1888 + wi.toNat / 2 < 2 ^ 32 := by have := hcid; have := hnc_le; omega
            have h1888_lt64 : 1888 + wi.toNat / 2 < 2 ^ 64 := by omega
            have h1888n : BitVec.toNat (1888 : BitVec 32) = 1888 := rfl
            rw [h1888n]
            simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
              Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h1888_lt, Nat.mod_eq_of_lt h1888_lt64])
            _ _
        have hoth_c0_val : kb[(BitVec.toNat (2912 : BitVec 32) +
            BitVec.toNat kb[(BitVec.toNat (1888 : BitVec 32) + wi.toNat / 2) % 2 ^ 32] +
            (wi.toNat % 2 + 1 - 2 * (wi.toNat % 2 % 2))) % 2 ^ 32]'(by
              rw [hoff_c0]
              refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
              have h2912n : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
              have := hosz_le; have := hsz2; have := hbuf_sz
              have hwm : wi.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
              omega) = other := by
          dsimp only [other]
          refine m8_k6_get_congr ?_ _ _
          rw [hoff_c0, hoth_idx_eq]
          rcases Nat.mod_two_eq_zero_or_one wi.toNat with hw0 | hw1
          · have hwa : wi &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq (by
              rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.and_one_is_mod, hw0]; rfl)
            have hlt32 : 2912 + off.toNat + 1 < 2 ^ 32 := by
              have := hosz_le; have := hbuf_sz; have := hlt28; have := h15; omega
            rw [hwa, hw0]
            simp [Nat.mod_eq_of_lt hlt32]
          · have hwa : wi &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq (by
              rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.and_one_is_mod, hw1])
            have hlt32 : 2912 + off.toNat < 2 ^ 32 := by
              have := hosz_le; have := hbuf_sz; have := hlt28; have := h15; omega
            rw [hwa, hw1]
            simp [Nat.mod_eq_of_lt hlt32]
        have hoth : other.toNat < 2 * nv.toNat := by
          rw [hoth_c0_val] at hc
          exact Nat.lt_of_not_le fun h => hc (by have := hnv_le; omega)
        clear hc
        have h608_c0 : (BitVec.setWidth 64 ((608 : BitVec 32) + other)).toNat < kb.length := by
          have := hoth; have := hnv_le; c0_bound
        c0_hsplit
        · clear hc
          have h1376_eq : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat =
              1376 + wi.toNat := by
            have := hwi; have := hnc_le; c0_bound
          have h1376_c0 : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat < kb.length := by
            rw [h1376_eq]; have := hwi; have := hnc_le; omega
          c0_hsteps!; rw [m8_k6_set_congr h1376_eq rfl] at hm
          obtain ⟨kb1, hk1, hqh1, hm1⟩ := propKeep_store_safe hpk hqh hm (by omega)
          exact hLw kb1 m ticks (cnt + 1#64) wi nxt (steps + 1#32) hk1 hqh1 (by omega) hsteps1 hm1
        · clear hc; c0_hsteps_nogrp
          refine wp_join_state (ts := [.bits 32, .bits 32, .bits 32])
            (α := BitVec 32 × BitVec 32 × BitVec 32)
            (fun x => (x.1, x.2.1, x.2.2, ()))
            (fun x m' => m' = m ∧ (x.2.1 = 0xFFFFFFFF#32 ∨
              (x.2.1.toNat < sz.toNat ∧ x.2.2.toNat < 2 * nv.toNat))) ?_ ?_
          · rintro Jreloc ⟨u, ri, rl⟩ m' ⟨rfl, hri⟩
            dsimp only [Prod.fst]
            have h_rel := k6_prop_reloc_watch_wp hΓ (pk := pk) (kbuf := kbuf) (kb := kb)
              (nc := nc) (nv := nv) (acap := acap) (lit := lit) (prev := prev) (wi := wi)
              (steps := steps) (w := w) (nxt := nxt) (off := off) (cm := cm) (other := other)
              (u := u) (ri := ri) (rl := rl) (qh1 := qh1) (Jout := Jout)
              (ticks := ticks) (cnt := cnt) (R := R) (Q := Q) (X := X) (Jcfl := Jcfl)
              (Lw := Lw) (Jexit := Jexit)
              hnv_le hnc_le hQ hpk hqh hkb1 hkb15 hwi hsteps1 hlit hoth hosz_le hsz2 hri hLw hm
            dsimp only [pRelocE, pRelocGrpE, pNonBinE, pWatchLoopGrpE, pOuter, pSGrpB3, pSGrpKN,
              pSGrpB64, pSLd4, pSLd3, pSL4, pSL3, pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI,
              pSLet, pDfltT, pDflt] at h_rel
            exact h_rel
          · intro Jreloc hJreloc
            have h_sr := k6_prop_search_repl_wp (Γ := Γ) (pk := pk) (kbuf := kbuf) (kb := kb)
              (nc := nc) (nv := nv) (acap := acap) (lit := lit) (prev := prev) (wi := wi)
              (steps := steps) (w := w) (nxt := nxt) (off := off) (cm := cm) (other := other)
              (Jout := Jout) (ticks := ticks) (cnt := cnt) (R := R) (Q := Q) (X := X)
              (Jcfl := Jcfl) (Lw := Lw) (Jexit := Jexit) (Jreloc := Jreloc)
              hnv_le hpk hkb0 hkb15 hosz_le hsz2
              (fun u ri rl h => hJreloc (u, ri, rl) m ⟨rfl, h⟩) hm
            dsimp only [pSearchReplGrpE, pRelocGrpE, pNonBinE, pWatchLoopGrpE, pOuter, pSGrpK3,
              pSGrpKN, pSGrpB64, pSLd4, pSLd3, pSL4, pSL3, pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64,
              pSLetI, pSLet, pDfltT, pDflt] at h_sr
            exact h_sr

private theorem k6_prop_watch_loop_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs) {pk : BitVec 64}
    {kbuf kb0 : List (BitVec 32)} {nc nv acap lit hd qh1 : BitVec 32} {ticks0 : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i32]} {X : XPost} {Jcfl : Cont []}
    {Jout : Cont [.bits 64]} {m0 : Mem 64}
    (hnv_le : nv.toNat ≤ 64) (hnc_le : nc.toNat ≤ 256)
    (hQ : ∀ (r : Val i32) (kb' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kb' → kb'.length = kbuf.length →
      kb'[0]? = kbuf[0]? → kb'[1]? = kbuf[1]? → kb'[2]? = kbuf[2]? → kb'[15]? = kbuf[15]? →
      (∀ cid < 256, kb'[1888 + cid]? = kbuf[1888 + cid]? ∧
        kb'[2144 + cid]? = kbuf[2144 + cid]? ∧ kb'[2400 + cid]? = kbuf[2400 + cid]?) →
      (array (t := i32) pk kb' ⋆ R) m' → Q (r, ()) m')
    (hpk0 : PropKeep kbuf kb0) (hqh0 : kb0[4]? = some qh1)
    (hkb0 : kb0[0]? = some nv) (hkb1 : kb0[1]? = some nc) (hkb15 : kb0[15]? = some acap)
    (hlit : lit.toNat < 2 * nv.toNat)
    (hJout : ∀ ticks' m' kb', PropKeep kbuf kb' → kb'[4]? = some qh1 →
      (array (t := i32) pk kb' ⋆ R) m' → Jout (ticks', ()) m')
    (hm0 : (array (t := i32) pk kb0 ⋆ R) m0) :
    wp Γ Q X (pWatchLoopGrpE pk nc nv acap lit hd Jout ticks0 Jcfl) m0 := by
  dsimp only [pWatchLoopGrpE, pOuter, pSGrpKN, pSGrpB64, pSLd4, pSLd3, pSL4, pSL3,
    pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet, pDfltT, pDflt, Prod.fst]
  refine wp_loop_group (ts := [.bits 64, .bits 64, .bits 32, .bits 32, .bits 32])
    (fun rem (ticks, cnt, prev, wi, steps, ()) m => ∃ kb, PropKeep kbuf kb ∧
      kb[4]? = some qh1 ∧ steps.toNat ≤ 512 ∧ rem = 512 - steps.toNat ∧
      (array (t := i32) pk kb ⋆ R) m) ?_ ?_
  · rintro Lw remw ⟨ticks, cnt, prev, wi, steps, ⟨⟩⟩ m hLw ⟨kb, hpk, hqh, hsteps, rfl, hm⟩
    have hge := hpk.1.base_ge; have hlt28 := hpk.1.length_lt
    have hkb0' : kb[0]? = some nv := by rw [hpk.2.2.1, ← hpk0.2.2.1, hkb0]
    have hkb1' : kb[1]? = some nc := by rw [hpk.2.2.2.1, ← hpk0.2.2.2.1, hkb1]
    have hkb15' : kb[15]? = some acap := by rw [hpk.2.2.2.2.2.2.1, ← hpk0.2.2.2.2.2.2.1, hkb15]
    refine wp_join0 (fun m' => ∃ kb', PropKeep kbuf kb' ∧ kb'[4]? = some qh1 ∧
        (array (t := i32) pk kb' ⋆ R) m') ?_ ?_
    · intro _ m' ⟨kb', hpk', hqh', hm'⟩; c0_hsteps!
      exact hJout _ m' kb' hpk' hqh' hm'
    · intro Jexit hJexit
      c0_hsplit
      · have hwi : wi.toNat < 2 * nc.toNat := by have := hnc_le; omega
        clear hc
        c0_hsplit
        · have hsteps_lt : steps.toNat < 512 := hc
          clear hc
          have hsteps1 : (steps + 1#32).toNat = steps.toNat + 1 := by
            have := hsteps_lt; c0_bound
          have h864_c0 : (BitVec.setWidth 64 ((864 : BitVec 32) + wi)).toNat < kb.length := by
            have := hwi; have := hnc_le; c0_bound
          have h1376_c0 : (BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat < kb.length := by
            have := hwi; have := hnc_le; c0_bound
          let nxt := kb[(BitVec.setWidth 64 ((864 : BitVec 32) + wi)).toNat]'h864_c0
          let w := kb[(BitVec.setWidth 64 ((1376 : BitVec 32) + wi)).toNat]'h1376_c0
          c0_hsplit
          · c0_hsteps!
            exact hLw (512 - (steps + 1#32).toNat) (ticks, cnt + 1#64, wi, nxt, steps + 1#32, ())
              m (by omega) ⟨kb, hpk, hqh, by omega, rfl, hm⟩
          · have hw_c0 : kb[(BitVec.toNat (1376 : BitVec 32) + BitVec.toNat wi) % 2 ^ 32]'(by
                refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
                have h1376n : BitVec.toNat (1376 : BitVec 32) = 1376 := rfl
                have := hwi; have := hnc_le; omega) = w :=
              m8_k6_get_congr (by
                have hlt32 : 1376 + BitVec.toNat wi < 2 ^ 32 := by
                  have := hwi; have := hnc_le; omega
                have hlt64 : 1376 + BitVec.toNat wi < 2 ^ 64 := by omega
                have h1376n : BitVec.toNat (1376 : BitVec 32) = 1376 := rfl
                rw [h1376n]
                simp [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt hlt32,
                  Nat.mod_eq_of_lt hlt64]) _ _
            have hblit : (w &&& 0x7FFFFFFF#32).toNat < 2 * nv.toNat := by
              rw [hw_c0] at hc
              exact Nat.lt_of_not_le fun h => hc (by
                rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
                  Nat.and_two_pow_sub_one_eq_mod w.toNat 31] at h
                have := hnv_le; omega)
            clear hc
            have h608_c0 : (BitVec.setWidth 64
                ((608 : BitVec 32) + (w &&& 0x7FFFFFFF#32))).toNat < kb.length := by
              have := hblit; have := hnv_le; c0_bound
            c0_hsplit
            · c0_hsteps!
              exact hLw (512 - (steps + 1#32).toNat)
                (ticks, cnt + 1#64, wi, nxt, steps + 1#32, ()) m (by omega)
                ⟨kb, hpk, hqh, by omega, rfl, hm⟩
            · clear hc
              c0_hsplit
              · clear hc
                c0_hsplit
                · clear hc; c0_hsteps!
                  exact k6_prop_cfl_close hQ hpk (by assumption) (by decide)
                · clear hc
                  refine wp_join0 (fun mj => ∃ kbj, PropKeep kbuf kbj ∧ kbj[4]? = some qh1 ∧
                      (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
                  · intro _ mj ⟨kbj, hkj, hj4, hmj⟩; c0_hsteps!
                    exact hLw (512 - (steps + 1#32).toNat)
                      (ticks, cnt + 1#64, wi, nxt, steps + 1#32, ()) mj (by omega)
                      ⟨kbj, hkj, hj4, by omega, rfl, hmj⟩
                  · intro Jbin hJbin
                    c0_hsplit
                    · clear hc
                      exact k6_prop_assign_call_wp hΓ hpk hqh hm fun kb' m' hk' hqh' hm' => by
                        c0_hsteps!; exact hJbin _ ⟨kb', hk', hqh', hm'⟩
                    · clear hc; c0_hsteps!; exact hJbin _ ⟨kb, hpk, hqh, hm⟩
              · clear hc
                have h_nb := k6_prop_nonbin_wp hΓ (pk := pk) (kbuf := kbuf) (kb := kb)
                  (nc := nc) (nv := nv) (acap := acap) (lit := lit) (prev := prev) (wi := wi)
                  (steps := steps) (w := w) (nxt := nxt) (qh1 := qh1) (Jout := Jout)
                  (ticks := ticks) (cnt := cnt) (R := R) (Q := Q) (X := X)
                  (Jcfl := Jcfl) (Lw := Lw) (Jexit := Jexit)
                  hnv_le hnc_le hQ hpk hqh hkb0' hkb1' hkb15' hwi (by omega) hlit
                  (fun kb' m' ticks' cnt' prev' wi' steps' hpk' hqh' hst_lo hst_hi hm' =>
                    hLw (512 - steps'.toNat) (ticks', cnt', prev', wi', steps', ()) m'
                      (by omega) ⟨kb', hpk', hqh', hst_hi, rfl, hm'⟩) hm
                dsimp only [pNonBinE, pWatchLoopGrpE, pOuter, pSGrpKN, pSGrpB64, pSLd4, pSLd3,
                  pSL4, pSL3, pSL2, pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet, pDfltT,
                  pDflt] at h_nb
                exact h_nb
        · c0_hsteps!; exact hJexit m ⟨kb, hpk, hqh, hm⟩
      · c0_hsteps!; exact hJexit m ⟨kb, hpk, hqh, hm⟩
  · intro L0 hL0; c0_hsteps!
    exact hL0 512 (ticks0, 0#64, 0xFFFFFFFF#32, hd, 0#32, ()) m0
      ⟨kb0, hpk0, hqh0, by decide, by decide, hm0⟩

public section

/-- Certifies `fullK6PropM7Spec` for `full_k6_prop_m7` on flat `CanonicalEnv`. -/
theorem full_k6_prop_m7_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, fullK6PropM7Spec a m Q X → Func.wp Γ full_k6_prop_m7_body a m Q X := by
  rintro ⟨pk, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6PropM7Spec_elim hSpec
  have hge0 := hok0.base_ge
  let nc := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'(by
    change 1 % 2 ^ 64 < _; omega)
  let nv := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'(by
    change 0 % 2 ^ 64 < _; omega)
  let acap := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 15)).toNat]'(by
    change 15 % 2 ^ 64 < _; omega)
  unfold Func.wp full_k6_prop_m7_body
  c0_hsplit
  · c0_hsteps!; exact propKeep_to_Q hQ (propKeep_refl hok0) hm0 0xFFFFFFFF#32
  · have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (by simpa [nc] using hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact propKeep_to_Q hQ (propKeep_refl hok0) hm0 0xFFFFFFFF#32
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [nv] using hc)
      clear hc
      refine wp_loop_group (ts := [.bits 64])
        (fun rem (ticks, ()) m => ∃ kb qh, PropKeep kbuf kb ∧ kb[4]? = some qh ∧
          rem = 64 - qh.toNat ∧ (array (t := i32) pk kb ⋆ R) m) ?_ ?_
      · rintro Jout rem ⟨ticks, ⟨⟩⟩ m hJout ⟨kb, qh, hpk, hqh, rfl, hm⟩
        have hge := hpk.1.base_ge; have hlt28 := hpk.1.length_lt
        have hkb0 : kb[0]? = some nv := by
          rw [hpk.2.2.1, List.getElem?_eq_getElem (by omega)]; rfl
        have hkb1 : kb[1]? = some nc := by
          rw [hpk.2.2.2.1, List.getElem?_eq_getElem (by omega)]; rfl
        have hkb15 : kb[15]? = some acap := by
          rw [hpk.2.2.2.2.2.2.1, List.getElem?_eq_getElem (by omega)]; rfl
        refine wp_join0 (fun m' => ∃ kb', PropKeep kbuf kb' ∧
            (array (t := i32) pk kb' ⋆ R) m') ?_ ?_
        · intro _ m' ⟨kb', hpk', hm'⟩
          have hge' := hpk'.1.base_ge
          c0_hsteps!
          exact k6_prop_cfl_close hQ hpk' (by assumption) (by decide)
        · intro Jcfl hJcfl
          c0_hsplit
          · clear hc
            have hk4_bd : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat < kb.length := by
              change 4 % 2 ^ 64 < _; omega
            have h4eq : kb[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat]'hk4_bd = qh := by
              rw [← m8_k6_get_eq hk4_bd,
                show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat = 4 from rfl, hqh]; rfl
            have h4eq_nat : kb[OfNat.ofNat 4 % 18446744073709551616]'(by
                change 4 % 18446744073709551616 < _; omega) = qh := by
              simpa [BitVec.ofNat] using h4eq
            c0_hsplit
            · have hqh_lt : qh.toNat < 64 := by rw [← h4eq_nat]; exact hc
              clear hc
              have h4_toNat : (kb[(BitVec.ofNat (OfNat.ofNat 64)
                  (OfNat.ofNat 4)).toNat]'hk4_bd).toNat = qh.toNat := congrArg BitVec.toNat h4eq
              have h352_c0 : (BitVec.setWidth 64 ((352 : BitVec 32) +
                  kb[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'hk4_bd)).toNat < kb.length := by
                have := hqh_lt; have := h4_toNat; c0_bound
              have h352_qh_c0 : (BitVec.setWidth 64 ((352 : BitVec 32) + qh)).toNat <
                  kb.length := by
                have := hqh_lt; c0_bound
              have hqh1 : (qh + 1#32).toNat = qh.toNat + 1 := by
                have := hqh_lt; c0_bound
              let lit := kb[(BitVec.setWidth 64 ((352 : BitVec 32) + qh)).toNat]'h352_qh_c0
              have hget_lit : ∀ hbd, kb[(BitVec.setWidth 64 ((352 : BitVec 32) +
                  kb[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'hk4_bd)).toNat]'hbd = lit := by
                intro hbd; simp only [lit, h4eq]
              c0_hstraight
              have hm4_eq : kb.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat
                  (kb[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'hk4_bd + (1 : BitVec 32)) =
                  kb.set 4 (qh + 1#32) := m8_k6_set_congr (by decide) (by rw [h4eq]; rfl)
              rw [hm4_eq] at hm
              obtain ⟨kb1, hk1, hm1⟩ : ∃ kb1, PropKeep kbuf kb1 ∧ kb1[4]? = some (qh + 1#32) ∧
                  (array (t := i32) pk kb1 ⋆ R) m :=
                ⟨kb.set 4 (qh + 1#32), propKeep_set hpk ⟨by omega, by omega, by omega, by omega,
                  by omega, by omega⟩ (qh + 1#32),
                  List.getElem?_set_self (by omega), hm⟩
              clear hm
              have hge1 := hk1.1.base_ge
              have hkb1_0 : kb1[0]? = some nv := by rw [hk1.2.2.1, ← hpk.2.2.1, hkb0]
              have hkb1_1 : kb1[1]? = some nc := by rw [hk1.2.2.2.1, ← hpk.2.2.2.1, hkb1]
              have hkb1_15 : kb1[15]? = some acap := by
                rw [hk1.2.2.2.2.2.2.1, ← hpk.2.2.2.2.2.2.1, hkb15]
              c0_hsplit
              · c0_hsteps!; exact hJout (64 - (qh + 1#32).toNat) (ticks, ()) m (by omega)
                  ⟨kb1, qh + 1#32, hk1, hm1.1, rfl, hm1.2⟩
              · have hlit_lt : lit.toNat < 2 * nv.toNat := by
                  have h0_eq : kbuf[OfNat.ofNat 0 % 2 ^ 64]'(by change 0 < _; omega) = nv := rfl
                  have hlit_hc : kb[(BitVec.toNat (352 : BitVec 32) +
                      BitVec.toNat kb[OfNat.ofNat 4 % 2 ^ 64]) % 2 ^ 32]'(by
                      rw [show kb[OfNat.ofNat 4 % 2 ^ 64] =
                        kb[OfNat.ofNat 4 % 18446744073709551616] from rfl, h4eq_nat]
                      refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
                      have h352n : BitVec.toNat (352 : BitVec 32) = 352 := rfl
                      have := hqh_lt; omega) = lit := by
                    dsimp only [lit]
                    exact m8_k6_get_congr (by
                      have hlt32 : 352 + qh.toNat < 2 ^ 32 := by have := hqh_lt; omega
                      have hlt64 : 352 + qh.toNat < 2 ^ 64 := by omega
                      have h352n : BitVec.toNat (352 : BitVec 32) = 352 := rfl
                      rw [show kb[OfNat.ofNat 4 % 2 ^ 64] =
                        kb[OfNat.ofNat 4 % 18446744073709551616] from rfl, h4eq_nat, h352n]
                      simp [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt hlt32,
                        Nat.mod_eq_of_lt hlt64]) _ _
                  rw [h0_eq, hlit_hc] at hc
                  have := hnv_le; omega
                clear hc
                have hnl : (lit ^^^ 1#32).toNat < 2 * nv.toNat := (m8_bv32_xor1_lt lit hlit_lt).2
                have h736_c0 : (BitVec.setWidth 64
                    ((736 : BitVec 32) + (lit ^^^ 1#32))).toNat < kb1.length := by
                  have := hnl; have := hnv_le; c0_bound
                let hd := kb1[(BitVec.setWidth 64
                    ((736 : BitVec 32) + (lit ^^^ 1#32))).toNat]'h736_c0
                rw [hget_lit h352_c0]
                have hm := hm1.2
                c0_hsteps_nogrp
                have h_wl := k6_prop_watch_loop_wp hΓ (pk := pk) (kbuf := kbuf) (kb0 := kb1)
                  (nc := nc) (nv := nv) (acap := acap) (lit := lit) (hd := hd) (qh1 := qh + 1#32)
                  (ticks0 := ticks) (R := R) (Q := Q) (X := X) (Jcfl := Jcfl) (Jout := Jout)
                  hnv_le hnc_le hQ hk1 hm1.1 hkb1_0 hkb1_1 hkb1_15 hlit_lt
                  (fun ticks' m' kb' hpk' hqh' hm' =>
                    hJout (64 - (qh + 1#32).toNat) (ticks', ()) m' (by omega)
                      ⟨kb', qh + 1#32, hpk', hqh', rfl, hm'⟩)
                  hm1.2
                dsimp only [pWatchLoopGrpE, pOuter, pSGrpKN, pSGrpB64, pSLd4, pSLd3, pSL4, pSL3,
                  pSLd, pSSt, pSJF, pSJT, pSLetI64, pSLetI, pSLet, pDfltT, pDflt] at h_wl
                exact h_wl
            · c0_hsteps!; exact hJcfl m ⟨kb, hpk, hm⟩
          · c0_hsteps!; exact hJcfl m ⟨kb, hpk, hm⟩
      · intro L0 hL0; c0_hsteps!
        have h4 : kbuf[4]? = some (kbuf[(BitVec.ofNat (OfNat.ofNat 64)
            (OfNat.ofNat 4)).toNat]'(by change 4 % 2 ^ 64 < _; omega)) := by
          rw [List.getElem?_eq_getElem (by omega)]; rfl
        exact hL0 _ (0#64, ()) m0 ⟨kbuf, _, propKeep_refl hok0, h4, rfl, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
