module

public import LeanQbe.T.Examples.Kissat.FullM7BcpNoBoundsProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Audit & Verification for Kissat M7 No-Bounds BCP (`FullM7BcpNoBounds*`)

1. Executable `#guard` checks on `m7BcpNoBounds_fns` (`3` fns), signatures, `checkAcyclic`,
   `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` checks (`.aarch64`, `.scalar64`, `.x64AVX2`,
   `.x64AVX512`).
2. Concrete `Mem 64` binary-watch UNSAT non-vacuity check (`nv_m7_bcp_nobounds_ok`,
   `XPost := False`, `FullWatchBoundsInv` preservation, zero model-finding proofs) plus
   composability sanity checks for `FullWatchBoundsInv` preservation across `full_watch_push`,
   `full_wstack_defrag`, `full_add_clause`, and `full_bcp_nobounds_m7`.
3. Single-line `#print axioms` audit via short root aliases across all exported
   `FullM7BcpNoBounds*` theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BcpNoBoundsTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds
  LeanQbe.T.Examples.Kissat.FastCore

/-! ## 1. Executable `#guard` sanity & 4-ISA codegen checks -/

#guard m7BcpNoBounds_fns.length == 3
#guard m7BcpNoBounds_fns.map Fn.name ==
  ["full_prop_lit_nobounds_m7", "full_propagate_ignore_nobounds_m7", "full_bcp_nobounds_m7"]
#guard full_prop_lit_nobounds_m7.as == [i64, i32, i64]
#guard full_prop_lit_nobounds_m7.rs == [Ty.bool]
#guard full_propagate_ignore_nobounds_m7.as == [i64, i64]
#guard full_propagate_ignore_nobounds_m7.rs == [i64]
#guard full_bcp_nobounds_m7.as == [i64]
#guard full_bcp_nobounds_m7.rs == [i64]
#guard m7BcpNoBoundsModule.checkAcyclic == true
#guard m7BcpNoBoundsModule.exits.isEmpty == true
#guard (ppTModule m7BcpNoBoundsModule).isOk
#guard (PrintQbe.module m7BcpNoBoundsModule).isOk
#guard (ppModule (m7BcpNoBounds_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BcpNoBounds_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BcpNoBounds_fns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (m7BcpNoBounds_fns.map (Fn.legal .x64AVX512))).isOk

/-! ## 2. Concrete `Mem 64` UNSAT NV & Composable `FullWatchBoundsInv` Preservation Checks -/

theorem nv_m7_bcp_nobounds_ok :
    Func.wp m7BcpNoBoundsEnv full_bcp_nobounds_m7_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', FullWatchBoundsInv s' ∧ (Full.FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m7_bcp_nobounds

theorem test_bcp_sparse_wb {Γ : Env}
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreNoBoundsSpec args m Q X →
      Γ "full_propagate_ignore_nobounds_m7" [i64, i64] [i64] args m Q X)
    {c : Full.FullCfg} {F0 : CNF Nat} {s : Full.FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : Full.FullPropDecSpecs.FullSparseInv c F0 s) (hwb : FullWatchBoundsInv s)
    (hm : (Full.FullMem c s ⋆ R) m) (Q : Post [i64]) (X : XPost)
    (hpost : ∀ r s' m',
      Full.FullPropDecSpecs.FullSparseInv c F0 s' → FullWatchBoundsInv s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) →
      (Full.FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bcp_nobounds_m7_body (c.hdr, ()) m Q X :=
  full_bcp_nobounds_m7_preserves_sparse_watchBounds hPropIgn hsp hwb hm Q X hpost

theorem test_wpush_wb {Γ : Env}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : Full.FullCfg} {F_cur : List (List Nat)} {s : Full.FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {lit w0 w1 cnt : BitVec 32}
    (hlen : s.LengthsOk c) (hwb : FullWatchBoundsInv s)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ Full.fullArenaClauseRefsCore s.core)
    (ha : Full.FullArenaClausesInv c F_cur (Full.withEmptyWatchesCore c s.core))
    (hcnt : cnt.toNat = 2) (hm : (Full.FullMem c s ⋆ R) m)
    (Q : Post [.bool]) (X : XPost)
    (hpost : ∀ pok s' m', s'.LengthsOk c → FullWatchBoundsInv s' →
      (Full.FullMem c s' ⋆ R) m' → Q (pok, ()) m') :
    wp Γ Q X (.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      (.imm c.hdr, (.imm lit, (.imm w0, (.imm w1, (.imm cnt, ())))))
      fun p => .ret (.var p.1, ())) m :=
  full_watch_push_preserves_watchBoundsInv_wp hPush hlen hwb
    (fun h => absurd (hcnt ▸ h) (by decide))
    (fun _ => ⟨fun hw0 => by rw [hw0] at hflag; exact absurd hflag (by decide),
      fun hw1 => by rw [hw1] at hlt; exact absurd hlt (by decide)⟩)
    (fun _ h => absurd (hcnt ▸ h) (by decide))
    (fun _ _ =>
      let hwf := ha.refs_wf w1.toNat href
      ⟨hflag, hblk, hlt, Nat.le_trans (by decide : 2 ≤ 3) hwf.2.1,
        Nat.le_trans hwf.2.2.1 hwf.2.2.2.1,
        fullArenaLiveLitsLt_of_arenaInv ha
          (Nat.le_trans hlen.core_ok.arena_len_le (Nat.le_of_eq hlen.core_ok.arena_len_arr.symm))
          href⟩)
    hm Q X hpost

end LeanQbeTest.T.KissatM7BcpNoBoundsTest

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev nb_plit_wf := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_prop_lit_nobounds_m7_wf
abbrev nb_ign_wf :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_propagate_ignore_nobounds_m7_wf
abbrev nb_bcp_wf := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_bcp_nobounds_m7_wf
abbrev nb_fns_wf := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBounds_fns_wf
abbrev nb_acyc := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBounds_acyclic
abbrev nb_def_wb :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.fullWstackDefrag_preserves_watchBoundsInv
abbrev nb_def_wp :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_wstack_defrag_preserves_watchBoundsInv_wp
abbrev nb_psh_wb :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.fullWatchPush_preserves_watchBoundsInv
abbrev nb_psh_wp :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_watch_push_preserves_watchBoundsInv_wp
abbrev nb_add_wp :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_add_clause_preserves_watchBoundsInv_wp
abbrev nb_plit_wp := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_prop_lit_nobounds_m7_wp
abbrev nb_ign_wp :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_propagate_ignore_nobounds_m7_wp
abbrev nb_bcp_wp := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_bcp_nobounds_m7_wp
abbrev nb_sp_wb :=
  @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.full_bcp_nobounds_m7_preserves_sparse_watchBounds
abbrev nb_noEx_t := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBoundsSpecTable_noExit
abbrev nb_noEx := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBoundsEnv_noExit
abbrev nb_tbl := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBounds_tableImpl
abbrev nb_modOk := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.m7BcpNoBounds_moduleOk
abbrev nb_nv_st := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.nvFastProp_watchBounds
abbrev nb_nv_bcp := @LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds.nv_m7_bcp_nobounds
abbrev nb_nv_tst := @LeanQbeTest.T.KissatM7BcpNoBoundsTest.nv_m7_bcp_nobounds_ok
abbrev nb_t_sp := @LeanQbeTest.T.KissatM7BcpNoBoundsTest.test_bcp_sparse_wb
abbrev nb_t_psh := @LeanQbeTest.T.KissatM7BcpNoBoundsTest.test_wpush_wb

#print axioms nb_plit_wf
#print axioms nb_ign_wf
#print axioms nb_bcp_wf
#print axioms nb_fns_wf
#print axioms nb_acyc
#print axioms nb_def_wb
#print axioms nb_def_wp
#print axioms nb_psh_wb
#print axioms nb_psh_wp
#print axioms nb_add_wp
#print axioms nb_plit_wp
#print axioms nb_ign_wp
#print axioms nb_bcp_wp
#print axioms nb_sp_wb
#print axioms nb_noEx_t
#print axioms nb_noEx
#print axioms nb_tbl
#print axioms nb_modOk
#print axioms nb_nv_st
#print axioms nb_nv_bcp
#print axioms nb_nv_tst
#print axioms nb_t_sp
#print axioms nb_t_psh
