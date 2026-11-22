module

public import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Forward Subsumption — Part 4 (`Stage 4`): Strengthening & Compaction

`full_fwd_check_cl` C0 expression fragments (`fwdLd32`, `fwdSt32`, `fwdCompactionExpr`, ...),
strengthening-by-shrinking (`PH_SHRK` + `0xFFFFFFFF#32` sentinel) and garbage-marking invariant
lemmas, and the factored compaction `wp` lemmas (`fwd_compaction_exit`, `fwd_compaction_wp`).
-/

set_option autoImplicit false
public section
namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaFwdTactics

namespace FullBvaFwdHelpers

theorem fullDenseInv_of_shrink {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hng_cref : fullArenaClauseGarbCore s.core cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore s.core cref)
    {arena' : List (BitVec 32)} {drop : Nat} (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (if (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore s.core cref ||| 0x00800000#32 else fullArenaHdrCore s.core cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_new : (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore s.core cref - 1]? = some 0xFFFFFFFF#32 ∧
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore s.core cref - 1 →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpad_old : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 →
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore s.core cref →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_cref : fullArenaClauseLitsCore { s.core with arena := arena' } cref =
      (fullArenaClauseLitsCore s.core cref).filter (· != drop))
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLitsCore s.core cref).filter (· != drop)))) :
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    FullWitnessInv c F0 F_cur s'.core ∧ FullDenseInv c F0 s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hnew_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := arena' } cref,
      l < 2 * s.core.cur_vars := fun l hl => by
    rw [hlits_cref] at hl; exact hw.arena.lits_lt cref href hng_cref l (List.mem_filter.mp hl).1
  have ⟨hclen', hrefs', hw', hother⟩ := fullWitnessInv_shrink_at_root
    hinv.1.lengths.core_ok hw hinv.2.2.2.2.1 href hnsz3 hnsz_lt hal hhdr' hsz'
    hpad_new hpad_old hout hnew_lt (by rw [hlits_cref]; exact hnew_ent)
  refine ⟨hw', ⟨⟨⟨hclen', hinv.1.lengths.scratch_ok⟩, F_cur, hw'⟩, hinv.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by dsimp only [s']; unfold fullArenaClauseRefs; rw [hrefs']
                    exact hinv.2.2.2.1.1 i hi, hinv.2.2.2.1.2⟩,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩, hrefs'⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
  by_cases hrc : r = cref
  · subst r; change ((fullArenaClauseLitsCore s'.core cref).map (· / 2)).Nodup; rw [hlits_cref]
    exact List.Nodup.sublist (List.Sublist.map (· / 2) List.filter_sublist)
      (hinv.2.2.1 cref href hng_cref)
  · have ⟨hg, hl⟩ := hother r hr hrc
    have hng0 : fullArenaClauseGarb s r = false := by
      change fullArenaClauseGarbCore s'.core r = false at hng; rwa [hg] at hng
    rw [show fullArenaClauseLits s' r = fullArenaClauseLits s r from hl]
    exact hinv.2.2.1 r hr hng0

theorem fwd_shrink_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_c st_u st_k : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {m : Mem 64}
    {cref sz nsz drop : BitVec 32} {C : List Nat}
    (hdu : FullDenseInv c F0 st_u) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (har_u : st_u.core.arena = s.core.arena) (hstu_cv : st_u.core.cur_vars = s.core.cur_vars)
    (hstu_al : st_u.core.arena_len = s.core.arena_len) (hstu_fl : st_u.core.fuel = s.core.fuel)
    (hstk_eq : st_k = { st_u with core := { st_u.core with arena := st_k.core.arena } })
    (href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng_cref : fullArenaClauseGarbCore s.core cref.toNat = false)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt_sz : nsz.toNat < sz.toNat)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cref.toNat)
    (hCu : fullArenaClauseLitsCore s.core cref.toNat = C)
    (hfilt_len : (C.filter (· != drop.toNat)).length = nsz.toNat)
    (hfilt_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop.toNat))))
    (hrefs_u : fullArenaClauseRefs st_u = fullArenaClauseRefs st_c)
    (hrefs_c : fullArenaClauseRefs st_c = fullArenaClauseRefs s)
    {arena' : List (BitVec 32)} (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref.toNat]? = some (if (fullArenaHdrCore st_u.core cref.toNat &&&
        0x00800000#32) = 0#32 then fullArenaHdrCore st_u.core cref.toNat ||| 0x00800000#32
      else fullArenaHdrCore st_u.core cref.toNat))
    (hsz' : arena'[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz.toNat))
    (hpad_new : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) = 0#32 →
      arena'[cref.toNat + 3 + fullArenaClauseSizeCore st_u.core cref.toNat - 1]? =
        some 0xFFFFFFFF#32 ∧
      ∀ i, cref.toNat + 3 + nsz.toNat ≤ i →
        i < cref.toNat + 3 + fullArenaClauseSizeCore st_u.core cref.toNat - 1 →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpad_old : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) ≠ 0#32 →
      ∀ i, cref.toNat + 3 + nsz.toNat ≤ i →
        i < cref.toNat + 3 + fullArenaClauseSizeCore st_u.core cref.toNat →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i,
        i < cref.toNat ∨ cref.toNat + 3 + fullArenaClauseSizeCore st_u.core cref.toNat ≤ i →
      arena'[i]? = st_u.core.arena[i]?)
    (hlits_elem : ∀ t < nsz.toNat, arena'[cref.toNat + 3 + t]?.map BitVec.toNat =
      (C.filter (· != drop.toNat))[t]?)
    (hm : (FullMem c { st_k with core := { st_k.core with arena := arena' } } ⋆ R) m)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q (true, ()) m := by
  have hCu' : fullArenaClauseLitsCore st_u.core cref.toNat = C := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har_u]; exact hCu
  have hsz_u : fullArenaClauseSizeCore st_u.core cref.toNat = sz.toNat := by
    unfold fullArenaClauseSizeCore; rw [har_u]; exact hsz_eq.symm
  have href_u := (by unfold fullArenaClauseRefsCore; rw [har_u, hstu_al]; exact href_c :
    cref.toNat ∈ fullArenaClauseRefsCore st_u.core)
  have hcr_wf := hw_u.arena.refs_wf cref.toNat href_u
  have hlen_a := hdu.1.lengths.core_ok.arena_len_le
  have ⟨hw_sh, hd_sh, hrefs_sh⟩ := fullDenseInv_of_shrink hdu hw_u href_u
    (by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har_u]; exact hng_cref)
    hnsz3 (by rw [hsz_u]; exact hnsz_lt_sz) hal hhdr' hsz' hpad_new hpad_old hout
    (fwd_shrink_litsCore_eq hsz' nsz.isLt hfilt_len hCu' hlits_elem (by omega))
    (by rw [hCu']; exact hfilt_ent)
  have hst_eq : ({ st_k with core := { st_k.core with arena := arena' } } : FullState) =
      { st_u with core := { st_u.core with arena := arena' } } := by rw [hstk_eq]
  refine hQ true _ m (by rw [hst_eq]; exact ⟨hd_sh.1.lengths, hw_sh, hd_sh.2⟩)
    (by dsimp only; rw [hstk_eq, hstu_cv]) (by dsimp only; rw [hstk_eq, hstu_al])
    (by dsimp only; rw [hstk_eq, hstu_fl])
    ((by rw [hst_eq]; exact hrefs_sh : fullArenaClauseRefs _ = fullArenaClauseRefs st_u).trans
      (hrefs_u.trans hrefs_c))
    (by simp) hm

@[expose] def fwdZext64 (a : Arg Val i32) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (a, ()) } fun p => k p.fst

@[expose] def fwdOp64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i64, i64], code := c, args := (a, b, ()) } fun p => k p.fst

@[expose] def fwdCmp32 (op : CmpOp) (a b : Arg Val i32) (k : Val .bool → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p => k p.fst

@[expose] def fwdCmp64 (op : CmpOp) (a b : Arg Val i64) (k : Val .bool → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp op i64, args := (a, b, ()) } fun p => k p.fst

@[expose] def fwdLd32 (base idx : Val i64) (k : Val i32 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  fwdOp64 (.mul i64) (Arg.var idx) (Arg.imm 4) fun p1 =>
  fwdOp64 (.add i64) (Arg.var base) (Arg.var p1) fun p2 => Expr.load i32 (Arg.var p2) k

@[expose] def fwdSt32 (base idx : Val i64) (v : Arg Val i32) (k : Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  fwdOp64 (.mul i64) (Arg.var idx) (Arg.imm 4) fun p1 =>
  fwdOp64 (.add i64) (Arg.var base) (Arg.var p1) fun p2 => Expr.store v (Arg.var p2) k

@[expose] def fwdArOff (cr : Val i32) (off : BitVec 64) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  fwdZext64 (Arg.var cr) fun p1 => fwdOp64 (.add i64) (Arg.var p1) (Arg.imm off) k

@[expose] def fwdArIdx3 (cr idx : Val i32) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  fwdArOff cr 3 fun p1 => fwdZext64 (Arg.var idx) fun p2 =>
  fwdOp64 (.add i64) (Arg.var p1) (Arg.var p2) k

@[expose] def fwdCompExitExpr (h pAr : Val i64) (sz cref hdr ik nsz : Val i32)
    (JsOuter : Cont [i32]) : Expr Val Cont [.bool] :=
  fwdCmp32 .ule (Arg.var nsz) (Arg.imm 2) fun cu => Expr.jnz (Arg.var cu)
    (fwdZext64 (Arg.var cref) fun p43 => fwdOp64 (.mul i64) (Arg.var p43) (Arg.imm 4) fun p44 =>
     fwdOp64 (.add i64) (Arg.var pAr) (Arg.var p44) fun p45 =>
     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                 args := (Arg.var hdr, Arg.imm 524288, ()) } fun p46 =>
     Expr.store (Arg.var p46.fst) (Arg.var p45)
       (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun p47 =>
        Expr.load i64 (Arg.var p47) fun ld10 =>
        fwdOp64 (.add i64) (Arg.var ld10) (Arg.imm 3) fun p48 =>
        fwdZext64 (Arg.var sz) fun p49 =>
        fwdOp64 (.add i64) (Arg.var p48) (Arg.var p49) fun p50 =>
        fwdOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun p51 =>
        Expr.store (Arg.var p50) (Arg.var p51)
          (fwdCmp32 .eq (Arg.var nsz) (Arg.imm 0) fun c0 => Expr.jnz (Arg.var c0)
             (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1024) fun p =>
              Expr.store (Arg.imm (t := i64) 1#64) (Arg.var p) (Expr.ret (Arg.imm false, ())))
             (fwdCmp32 .eq (Arg.var nsz) (Arg.imm 1) fun c1 => Expr.jnz (Arg.var c1)
                (fwdArOff cref 3 fun p => fwdLd32 pAr p fun ld =>
                 Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
                   (Arg.var h, Arg.var ld, ()) fun ok => Expr.ret (Arg.var ok.fst, ()))
                (fwdArOff cref 3 fun p => fwdLd32 pAr p fun ld11 =>
                 fwdArOff cref 4 fun p => fwdLd32 pAr p fun ld =>
                 Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
                   (Arg.var h, Arg.var ld11, Arg.var ld, ()) fun r =>
                 fwdCmp64 .ne (Arg.var r.fst) (Arg.imm 20) fun c =>
                 Expr.ret (Arg.var c, ()))))))
    (fwdArOff cref 2 fun p => fwdSt32 pAr p (Arg.var nsz)
     (fwdArOff cref 1 fun p => fwdSt32 pAr p (Arg.imm 2)
      (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.jump JsOuter (Arg.var ik, ())) Blocks.nil) fun Js =>
       Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                   args := (Arg.var hdr, Arg.imm 8388608, ()) } fun p =>
       fwdCmp32 .eq (Arg.var p.fst) (Arg.imm 0) fun cq => Expr.jnz (Arg.var cq)
         (fwdZext64 (Arg.var cref) fun p1 => fwdOp64 (.mul i64) (Arg.var p1) (Arg.imm 4) fun p2 =>
          fwdOp64 (.add i64) (Arg.var pAr) (Arg.var p2) fun p3 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var hdr, Arg.imm 8388608, ()) } fun p4 =>
          Expr.store (Arg.var p4.fst) (Arg.var p3)
            (fwdArOff cref 3 fun p5 => fwdZext64 (Arg.var sz) fun p6 =>
             fwdOp64 (.add i64) (Arg.var p5) (Arg.var p6) fun p7 =>
             fwdOp64 (.sub i64) (Arg.var p7) (Arg.imm 1) fun p8 =>
             fwdSt32 pAr p8 (Arg.imm 4294967295) (Expr.jump Js.fst ())))
         (Expr.jump Js.fst ()))))

@[expose] def fwdCompactionExpr (h pAr : Val i64) (sz cref drop hdr : Val i32)
    (JsOuter : Cont [i32]) : Expr Val Cont [.bool] :=
  Expr.group (fun Js_1 => Blocks.cons (fun (p40 : Tup Val [i32, i32]) =>
    fwdCmp32 .ult (Arg.var p40.fst) (Arg.var sz) fun c =>
    Expr.jnz (Arg.var c)
      (fwdArIdx3 cref p40.fst fun p45 => fwdLd32 pAr p45 fun ld_10 =>
       Expr.group (fun _ => Blocks.cons (fun (pn : Tup Val [i32]) =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p40.fst, Arg.imm 1, ()) } fun p48 =>
         Expr.jump Js_1.fst (Arg.var p48.fst, Arg.var pn.fst, ())) Blocks.nil)
       fun Js =>
       fwdCmp32 .ne (Arg.var ld_10) (Arg.var drop) fun cn => Expr.jnz (Arg.var cn)
         (fwdArIdx3 cref p40.snd.fst fun p => fwdSt32 pAr p (Arg.var ld_10)
            (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                         args := (Arg.var p40.snd.fst, Arg.imm 1, ()) } fun pn =>
             Expr.jump Js.fst (Arg.var pn.fst, ())))
         (Expr.jump Js.fst (Arg.var p40.snd.fst, ())))
      (fwdCompExitExpr h pAr sz cref hdr p40.fst p40.snd.fst JsOuter)) Blocks.nil)
  fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, Arg.imm 0, ())

theorem fwdDenseW_set_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨{ h.1 with core_ok := { h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le } },
   fullWitnessInv_set_inconsistent h.2.1 hu, h.2.2⟩

theorem fwd_markGarb_comp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_u st_k : FullState} {cref sz hdr : BitVec 32} (ag' : BitVec 64)
    (hdu : FullDenseInv c F0 st_u) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (har_u : st_u.core.arena = s.core.arena) (hstu_al : st_u.core.arena_len = s.core.arena_len)
    (hstk_eq : st_k = { st_u with core := { st_u.core with arena := st_k.core.arena } })
    (href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (har_k_len : st_k.core.arena.length = c.arena_cap) (hcr_lt : cref.toNat < s.core.arena.length)
    (hhdr_v : s.core.arena[cref.toNat]'hcr_lt = hdr)
    (hout_k : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
      st_k.core.arena[idx]? = s.core.arena[idx]?)
    (hsz : fullArenaClauseSizeCore s.core cref.toNat = sz.toNat) :
    FullWitnessInv c F0 F_cur { st_k.core with
      arena := st_k.core.arena.set cref.toNat (hdr ||| 0x00080000#32), arena_garbage := ag' } ∧
    FullDenseInvW c F0 F_cur { st_k with core := { st_k.core with
      arena := st_k.core.arena.set cref.toNat (hdr ||| 0x00080000#32), arena_garbage := ag' } } ∧
    fullArenaClauseRefs { st_k with core := { st_k.core with
      arena := st_k.core.arena.set cref.toNat (hdr ||| 0x00080000#32), arena_garbage := ag' } } =
      fullArenaClauseRefs st_u := by
  have hal_u : st_u.core.arena.length = c.arena_cap := hdu.1.lengths.core_ok.arena_len_arr
  have hal_s : s.core.arena.length = c.arena_cap := by rw [← har_u]; exact hal_u
  have href_u : cref.toNat ∈ fullArenaClauseRefsCore st_u.core := by
    unfold fullArenaClauseRefsCore; rw [har_u, hstu_al]; exact href_c
  have hsz_u : fullArenaClauseSizeCore st_u.core cref.toNat = sz.toNat := by
    unfold fullArenaClauseSizeCore; rw [har_u]; exact hsz
  have hhdr_u : fullArenaHdrCore st_u.core cref.toNat = hdr := by
    unfold fullArenaHdrCore; rw [har_u, List.getElem?_eq_getElem hcr_lt, Option.getD_some, hhdr_v]
  have h := fullDenseInv_of_markGarb (ag' := ag') (cnt' := st_u.scratch.fwd_sub_cnt) hdu hw_u href_u
    (arena' := st_k.core.arena.set cref.toNat (hdr ||| 0x00080000#32)) (by simp [har_k_len])
    (by rw [List.getElem?_set_self (by omega), hhdr_u])
    (fun i hne hi => by
      rw [List.getElem?_set_ne (Ne.symm hne), har_u]; exact hout_k i (by rw [hsz_u] at hi; omega))
  rw [hstk_eq]
  exact ⟨h.1, ⟨h.2.1.1.lengths, h.1, h.2.1.2⟩, h.2.2⟩

theorem fwd_compaction_exit {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_c st_u st_k : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cref sz drop hdr ik nsz : BitVec 32} {mlk : Mem 64} {JsOuter : Cont [i32]}
    (hdu : FullDenseInv c F0 st_u) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (har_u : st_u.core.arena = s.core.arena) (hstu_cv : st_u.core.cur_vars = s.core.cur_vars)
    (hstu_al : st_u.core.arena_len = s.core.arena_len) (hstu_fl : st_u.core.fuel = s.core.fuel)
    (href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng_cref : fullArenaClauseGarbCore s.core cref.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cref.toNat)
    (hsz_ar_len : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hhdr_v : s.core.arena[cref.toNat]'(by omega) = hdr)
    (hCu : C = fullArenaClauseLitsCore s.core cref.toNat) (hC_lt : ∀ l ∈ C, l < 2 * s.core.cur_vars)
    (hfilt_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop.toNat))))
    (hrefs_u : fullArenaClauseRefs st_u = fullArenaClauseRefs st_c)
    (hrefs_c : fullArenaClauseRefs st_c = fullArenaClauseRefs s)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJsOuter : ∀ (iv : Val i32) ms, Q (true, ()) ms → JsOuter (iv, ()) ms)
    (hstk_eq : st_k = { st_u with core := { st_u.core with arena := st_k.core.arena } })
    (har_k_len : st_k.core.arena.length = c.arena_cap)
    (hnsz_eq : nsz.toNat = (C.filter (· != drop.toNat)).length) (hnsz_lt_sz : nsz.toNat < sz.toNat)
    (hpref_k : ∀ t < nsz.toNat, st_k.core.arena[cref.toNat + 3 + t]?.map BitVec.toNat =
      (C.filter (· != drop.toNat))[t]?)
    (hnesent_k : ∀ t < sz.toNat,
      st_k.core.arena[cref.toNat + 3 + t]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout_k : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
      st_k.core.arena[idx]? = s.core.arena[idx]?) (hmlk : (FullMem c st_k ⋆ R) mlk) :
    wp Γ Q X (fwdCompExitExpr c.hdr c.pArena sz cref hdr ik nsz JsOuter) mlk := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcv_le := hdu.1.lengths.core_ok.cur_vars_le
  have hal_le := hdu.1.lengths.core_ok.arena_len_le
  have har_u_len : st_u.core.arena.length = c.arena_cap := hdu.1.lengths.core_ok.arena_len_arr
  have har_s_len : s.core.arena.length = c.arena_cap := by rw [← har_u, har_u_len]
  have hcref64 : (BitVec.setWidth 64 cref).toNat = cref.toNat := by c0_bound
  have hcref1_n : (BitVec.setWidth 64 cref + 1).toNat = cref.toNat + 1 := by c0_bound
  have hcref2_n : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by c0_bound
  have hcref3_n : (BitVec.setWidth 64 cref + 3).toNat = cref.toNat + 3 := by c0_bound
  have hcref4_n : (BitVec.setWidth 64 cref + 4).toNat = cref.toNat + 4 := by c0_bound
  let C_filt := C.filter (· != drop.toNat)
  unfold fwdCompExitExpr fwdArOff fwdLd32 fwdSt32 fwdZext64 fwdOp64 fwdCmp32 fwdCmp64
  dsimp only
  bf_fast_nogrp
  all_goals
    have hlen_k : cref.toNat + 3 + sz.toNat ≤ st_k.core.arena.length := by
      rw [har_k_len, ← har_s_len]; exact hsz_ar_len
    have hfilt_elem : ∀ (t : Nat) (ht : t < nsz.toNat),
        (st_k.core.arena[cref.toNat + 3 + t]'(by omega)).toNat =
          (C.filter (· != drop.toNat))[t]'(by omega) :=
      fun t ht => Option.some.inj (by
        have h1 := hpref_k t ht
        rw [List.getElem?_eq_getElem (by omega), Option.map_some,
          List.getElem?_eq_getElem (by omega)] at h1; exact h1)
    try simp only [hcref64, hcref1_n, hcref2_n] at hm
    have hk_cv : st_k.core.cur_vars = s.core.cur_vars := by rw [hstk_eq]; exact hstu_cv
    have hk_al : st_k.core.arena_len = s.core.arena_len := by rw [hstk_eq]; exact hstu_al
    have hk_fl : st_k.core.fuel = s.core.fuel := by rw [hstk_eq]; exact hstu_fl
    have hhdr_u : fullArenaHdrCore st_u.core cref.toNat = hdr := by
      unfold fullArenaHdrCore; rw [har_u, List.getElem?_eq_getElem (by omega), Option.getD_some,
        hhdr_v]
    have hCf : C_filt.length = nsz.toNat := hnsz_eq.symm
  · have hnsz0 : nsz.toNat = 0 := by c0_bound
    have ⟨hu_cur, hu_f0⟩ := fwd_unsat_of_empty_entails hw_u.ext_sound
      (List.eq_nil_of_length_eq_zero (l := C.filter (· != drop.toNat)) (by omega) ▸ hfilt_ent)
    have ⟨_, hdg, hrefs_g⟩ := fwd_markGarb_comp (st_k.core.arena_garbage + 3 +
      BitVec.setWidth 64 sz) hdu hw_u har_u hstu_al hstk_eq href_c har_k_len (by omega) hhdr_v
      hout_k hsz_eq.symm
    exact hQ false _ m (fwdDenseW_set_inc hdg hu_cur) hk_cv hk_al hk_fl
      (hrefs_g.trans (hrefs_u.trans hrefs_c)) (fun _ => hu_f0) hm
  · have hnsz1 : nsz.toNat = 1 := by c0_bound
    have hlt3 : (st_k.core.arena[cref.toNat + 3]'(by omega)).toNat < 2 * st_k.core.cur_vars := by
      have h0 := hfilt_elem 0 (by omega); simp only [Nat.add_zero] at h0
      rw [hk_cv, h0]; exact hC_lt _ (List.mem_filter.mp (List.getElem_mem _)).1
    have hC1 : C_filt = [(st_k.core.arena[cref.toNat + 3]'(by omega)).toNat] :=
      List.ext_getElem (by rw [hCf]; simp [hnsz1]) fun i hi _ => by
        cases i with
        | zero => exact (hfilt_elem 0 (by omega)).symm
        | succ => omega
    have ⟨hwg, hdg, hrefs_g⟩ := fwd_markGarb_comp (st_k.core.arena_garbage + 3 +
      BitVec.setWidth 64 sz) hdu hw_u har_u hstu_al hstk_eq href_c har_k_len (by omega) hhdr_v
      hout_k hsz_eq.symm
    c0_call hAddUnit; refine ⟨c, F0, F_cur, _, R, rfl, hdg.1, hwg, fun _ => by
        simp only [hcref64, hcref3_n,
          List.getElem_set_ne (show cref.toNat ≠ cref.toNat + 3 by omega)]
        rw [← hC1]; exact hfilt_ent, hm,
      fun ok1 _ _ _ _ _ _ _ _ cl1 _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1 hw1 hcl1 _ hfalse1 hm1 => ?_⟩
    have ⟨hd1, hrefs1⟩ := fullDenseInv_of_fwd_call hdg.toDense hlen1 hw1 hcl1
      rfl rfl rfl rfl rfl rfl rfl
    exact hQ ok1 _ m1 ⟨hd1.1.lengths, hw1, hd1.2⟩ hk_cv hk_al hk_fl
      (hrefs1.trans (hrefs_g.trans (hrefs_u.trans hrefs_c)))
      (fun hok => ((hfalse1 hok).resolve_left (by
        simp only [hcref64, hcref3_n,
          List.getElem_set_ne (show cref.toNat ≠ cref.toNat + 3 by omega)]
        exact Nat.not_le.mpr hlt3)).1) hm1
  · have hnsz2 : nsz.toNat = 2 := by c0_bound
    have : (BitVec.setWidth 64 cref + 4).toNat < st_k.core.arena.length := by
      rw [hcref4_n]; omega
    have : (BitVec.setWidth 64 cref + 4).toNat <
        (st_k.core.arena.set cref.toNat (hdr ||| 524288)).length := by
      simp only [List.length_set]; omega
    bf_fast_nogrp
    have hC2 : C_filt = [(st_k.core.arena[cref.toNat + 3]'(by omega)).toNat,
        (st_k.core.arena[cref.toNat + 4]'(by omega)).toNat] :=
      List.ext_getElem (by rw [hCf]; simp [hnsz2]) fun i hi _ => by
        rcases i with _ | _ | i
        · exact (hfilt_elem 0 (by omega)).symm
        · exact (hfilt_elem 1 (by omega)).symm
        · omega
    have ⟨hwg, hdg, hrefs_g⟩ := fwd_markGarb_comp (st_k.core.arena_garbage + 3 +
      BitVec.setWidth 64 sz) hdu hw_u har_u hstu_al hstk_eq href_c har_k_len (by omega) hhdr_v
      hout_k hsz_eq.symm
    c0_call hAddBin; refine ⟨c, F0, F_cur, _, R, rfl, hdg.1, hwg, hdg.2.2.2.2.2.1, fun _ _ => by
        simp only [hcref64, hcref3_n, hcref4_n,
          List.getElem_set_ne (show cref.toNat ≠ cref.toNat + 3 by omega),
          List.getElem_set_ne (show cref.toNat ≠ cref.toNat + 4 by omega)]
        rw [← hC2]; exact hfilt_ent, hm,
      fun rb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 hlen2 hw2 _ h20 _ hm2 => ?_⟩
    have ⟨hd2, hrefs2⟩ := fullDenseInv_of_fwd_call hdg.toDense hlen2 hw2 hdg.2.2.2.2.2.1
      rfl rfl rfl rfl rfl rfl rfl
    bf_fast; exact hQ (rb != 20#64) _ m2 ⟨hd2.1.lengths, hw2, hd2.2⟩ hk_cv hk_al hk_fl
      (hrefs2.trans (hrefs_g.trans (hrefs_u.trans hrefs_c)))
      (fun hne => (h20 (by simp only [bne_eq_false_iff_eq] at hne; exact hne)).1) hm2
  · have hnsz3 : 3 ≤ nsz.toNat := by c0_bound
    have hnsz_ofNat : nsz = BitVec.ofNat 32 nsz.toNat :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nsz.isLt])
    have hszeq_u : fullArenaClauseSizeCore st_u.core cref.toNat = sz.toNat := by
      unfold fullArenaClauseSizeCore; rw [har_u]; exact hsz_eq.symm
    have hsent_n : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 sz - 1).toNat =
        cref.toNat + 3 + sz.toNat - 1 := by c0_bound
    bf_fast
    · have hsh0 : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) = 0#32 := by
        rw [hhdr_u]; exact hc
      simp only [hcref64, hsent_n] at hm
      exact hJsOuter _ _ (fwd_shrink_done hdu hw_u har_u hstu_cv hstu_al hstu_fl hstk_eq href_c
        hng_cref hnsz3 hnsz_lt_sz hsz_eq hCu.symm hnsz_eq.symm hfilt_ent hrefs_u hrefs_c
        (by simp [har_k_len])
        (by rw [List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [har_k_len]; omega),
              ite_eq_left hsh0, hhdr_u]; try rfl)
        (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [har_k_len]; omega)]
            exact congrArg some hnsz_ofNat)
        (fun _ => ⟨by rw [hszeq_u, List.getElem?_set_self (by simp [har_k_len]; omega)]; try rfl,
          fun idx hi1 hi2 => by
            rw [hszeq_u] at hi2
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            have hsub := hnesent_k (idx - (cref.toNat + 3)) (by omega)
            rwa [show cref.toNat + 3 + (idx - (cref.toNat + 3)) = idx by omega] at hsub⟩)
        (fun hne => absurd hsh0 hne)
        (fun idx hidx => by
          rw [hszeq_u] at hidx
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), har_u]
          exact hout_k idx (by omega))
        (fun t ht => by
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_eq_getElem (by omega), Option.map_some, hfilt_elem t ht,
            List.getElem?_eq_getElem (by omega)]) hm hQ)
    · have hsh1 : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) ≠ 0#32 := by
        rw [hhdr_u]; exact hc
      exact hJsOuter _ _ (fwd_shrink_done hdu hw_u har_u hstu_cv hstu_al hstu_fl hstk_eq href_c
        hng_cref hnsz3 hnsz_lt_sz hsz_eq hCu.symm hnsz_eq.symm hfilt_ent hrefs_u hrefs_c
        (by simp [har_k_len])
        (by rw [ite_eq_right hsh1, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              hout_k cref.toNat (by omega), hhdr_u, List.getElem?_eq_getElem (by omega), hhdr_v])
        (by rw [List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [har_k_len]; omega)]
            exact congrArg some hnsz_ofNat)
        (fun h0 => absurd h0 hsh1)
        (fun _ idx hi1 hi2 => by
          rw [hszeq_u] at hi2
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          have hsub := hnesent_k (idx - (cref.toNat + 3)) (by omega)
          rwa [show cref.toNat + 3 + (idx - (cref.toNat + 3)) = idx by omega] at hsub)
        (fun idx hidx => by
          rw [hszeq_u] at hidx
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), har_u]
          exact hout_k idx (by omega))
        (fun t ht => by
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_eq_getElem (by omega), Option.map_some, hfilt_elem t ht,
            List.getElem?_eq_getElem (by omega)]) hm hQ)


theorem fwd_compaction_wp {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_c st_u : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cref sz drop hdr : BitVec 32} {mu : Mem 64}
    (hdu : FullDenseInv c F0 st_u) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (har_u : st_u.core.arena = s.core.arena) (hstu_cv : st_u.core.cur_vars = s.core.cur_vars)
    (hstu_al : st_u.core.arena_len = s.core.arena_len) (hstu_fl : st_u.core.fuel = s.core.fuel)
    (href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng_cref : fullArenaClauseGarbCore s.core cref.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cref.toNat)
    (hsz_ge3 : 3 ≤ sz.toNat) (hsz_ar_len : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hhdr_v : s.core.arena[cref.toNat]'(by omega) = hdr)
    (hCu : C = fullArenaClauseLitsCore s.core cref.toNat)
    (hC_len : C.length = fullArenaClauseSizeCore s.core cref.toNat)
    (hC_lit : ∀ (t : Nat) (ht : t < sz.toNat),
      let lit := s.core.arena[cref.toNat + 3 + t]'(by omega)
      C[t]? = some lit.toNat ∧ lit.toNat ∈ C ∧ lit.toNat < 2 * s.core.cur_vars)
    (hC_lt : ∀ l ∈ C, l < 2 * s.core.cur_vars)
    (hfilt_lt_sz : (C.filter (· != drop.toNat)).length < sz.toNat)
    (hfilt_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop.toNat))))
    (hrefs_u : fullArenaClauseRefs st_u = fullArenaClauseRefs st_c)
    (hrefs_c : fullArenaClauseRefs st_c = fullArenaClauseRefs s)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hmu : (FullMem c st_u ⋆ R) mu)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (JsOuter : Cont [i32])
    (hJsOuter : ∀ (iv : Val i32) ms, Q (true, ()) ms → JsOuter (iv, ()) ms) :
    wp Γ Q X (fwdCompactionExpr c.hdr c.pArena sz cref drop hdr JsOuter) mu := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcv_le := hdu.1.lengths.core_ok.cur_vars_le
  have hal_le := hdu.1.lengths.core_ok.arena_len_le
  have har_u_len : st_u.core.arena.length = c.arena_cap := hdu.1.lengths.core_ok.arena_len_arr
  have har_s_len : s.core.arena.length = c.arena_cap := by rw [← har_u, har_u_len]
  have hcref64 : (BitVec.setWidth 64 cref).toNat = cref.toNat := by c0_bound
  have hcref1_n : (BitVec.setWidth 64 cref + 1).toNat = cref.toNat + 1 := by c0_bound
  have hcref2_n : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by c0_bound
  have hcref3_n : (BitVec.setWidth 64 cref + 3).toNat = cref.toNat + 3 := by c0_bound
  have hcref4_n : (BitVec.setWidth 64 cref + 4).toNat = cref.toNat + 4 := by c0_bound
  let C_filt := C.filter (· != drop.toNat)
  unfold fwdCompactionExpr fwdArIdx3 fwdArOff fwdLd32 fwdSt32 fwdZext64 fwdOp64 fwdCmp32
  dsimp only
  refine wp_loop_inv (fun (ik, nsz, ()) mlk => ∃ st_k : FullState,
      AgreesExcept fwdArenaMask st_u st_k ∧ st_k.core.arena.length = c.arena_cap ∧
      ik.toNat ≤ sz.toNat ∧ nsz.toNat = ((C.take ik.toNat).filter (· != drop.toNat)).length ∧
      (∀ t < nsz.toNat, st_k.core.arena[cref.toNat + 3 + t]?.map BitVec.toNat =
        ((C.take ik.toNat).filter (· != drop.toNat))[t]?) ∧
      (∀ t, ik.toNat ≤ t → t < sz.toNat →
        st_k.core.arena[cref.toNat + 3 + t]? = s.core.arena[cref.toNat + 3 + t]?) ∧
      (∀ t < sz.toNat, st_k.core.arena[cref.toNat + 3 + t]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
      (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
        st_k.core.arena[idx]? = s.core.arena[idx]?) ∧ (FullMem c st_k ⋆ R) mlk)
    (fun (ik, _, _) _ => sz.toNat - ik.toNat) (fun Jk hJk => by
      bf_fast; refine hJk (0#32, 0#32, ()) mu ⟨st_u, .refl _ _, har_u_len,
        by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, by simp,
        fun _ ht => by simp at ht, fun _ _ _ => by rw [har_u], fun t ht => by
          rw [har_u, List.getElem?_eq_getElem (by omega), Option.getD_some]
          intro heq; have hlt := (hC_lit t ht).2.2
          have : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [heq] at hlt; omega,
        fun _ _ => by rw [har_u], hmu⟩)
    (fun Jk (ik, nsz, ()) mlk ⟨st_k, hag_k, har_k_len, hik_le, hnsz_eq, hpref_k,
      htail_k, hnesent_k, hout_k, hmlk⟩ ihk => ?_)
  have hstk_eq := fwd_arena_reconstruct hag_k
  have hnsz_le_ik : nsz.toNat ≤ ik.toNat := by
    rw [hnsz_eq]; exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
  bf_fast_nogrp
  · have hik_lt : ik.toNat < sz.toNat := by c0_bound
    have hidx_nsz : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 nsz).toNat =
        cref.toNat + 3 + nsz.toNat := by c0_bound
    have hik1 : (ik + 1#32).toNat = ik.toNat + 1 := by c0_bound
    have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by c0_bound
    have hl_eq : st_k.core.arena[cref.toNat + 3 + ik.toNat]'(by omega) =
        s.core.arena[cref.toNat + 3 + ik.toNat]'(by omega) := Option.some.inj
      (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
          exact htail_k ik.toNat (Nat.le_refl _) hik_lt)
    have hC_ik : C[ik.toNat]'(by omega) =
        (s.core.arena[cref.toNat + 3 + ik.toNat]'(by omega)).toNat := Option.some.inj
      (by rw [← List.getElem?_eq_getElem (by omega)]; exact (hC_lit ik.toNat hik_lt).1)
    have hstep_filt := take_succ_filter_eq (l := C) (i := ik.toNat) (x := drop.toNat) (by omega)
    refine wp_join_group
      (fun (x : Tup Val [i32]) mls => ∃ st_s : FullState,
        AgreesExcept fwdArenaMask st_u st_s ∧ st_s.core.arena.length = c.arena_cap ∧
        x.1.toNat = ((C.take (ik.toNat + 1)).filter (· != drop.toNat)).length ∧
        (∀ t < x.1.toNat, st_s.core.arena[cref.toNat + 3 + t]?.map BitVec.toNat =
          ((C.take (ik.toNat + 1)).filter (· != drop.toNat))[t]?) ∧
        (∀ t, ik.toNat + 1 ≤ t → t < sz.toNat →
          st_s.core.arena[cref.toNat + 3 + t]? = s.core.arena[cref.toNat + 3 + t]?) ∧
        (∀ t < sz.toNat, st_s.core.arena[cref.toNat + 3 + t]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
        (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
          st_s.core.arena[idx]? = s.core.arena[idx]?) ∧ (FullMem c st_s ⋆ R) mls)
      (fun _ x mls ⟨st_s, hags, hars, hnszs, hps, hts, hnes, hos, hms⟩ =>
        by bf_fast; exact ihk (ik + 1#32, x.1, ()) mls (by dsimp only; rw [hik1]; omega)
             ⟨st_s, hags, hars, by rw [hik1]; omega, by rw [hik1]; exact hnszs,
              fun t ht => by rw [hik1]; exact hps t ht,
              fun t ht1 ht2 => hts t (by rw [hik1] at ht1; omega) ht2, hnes, hos, hms⟩)
      (fun Js hJs => ?_)
    bf_fast
    · have hidx_k' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ik.toNat) % 2 ^ 64 =
          cref.toNat + 3 + ik.toNat := by c0_bound
      have hidx_kk : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 ik).toNat =
          cref.toNat + 3 + ik.toNat := by c0_bound
      simp only [hidx_k', hl_eq] at hc
      simp only [hidx_nsz, hidx_kk, hl_eq] at hm
      have hne_nat : (C[ik.toNat]'(by omega) != drop.toNat) = true := by
        rw [hC_ik, bne_iff_ne]; intro heq; exact hc (BitVec.eq_of_toNat_eq heq)
      simp only [hne_nat, ↓reduceIte] at hstep_filt
      have hset_lt : cref.toNat + 3 + nsz.toNat < st_k.core.arena.length := by
        rw [har_k_len]; omega
      refine hJs (nsz + 1#32, ()) m ⟨_, by exact hag_k.trans rfl, by simp [har_k_len],
        by dsimp only; rw [hnsz1, hstep_filt, List.length_append]; simp [hnsz_eq],
        fun t ht => by
          dsimp only at ht ⊢; rw [hnsz1] at ht; rw [hstep_filt]
          by_cases htn : t = nsz.toNat
          · subst htn
            rw [List.getElem?_set_self hset_lt, Option.map_some,
              List.getElem?_append_right (by omega)]
            simp [hnsz_eq, hC_ik]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
            exact hpref_k t (by omega),
        fun t ht1 ht2 => by
          dsimp only; rw [List.getElem?_set_ne (by omega)]; exact htail_k t (by omega) ht2,
        fun t ht => by
          dsimp only; by_cases htn : t = nsz.toNat
          · subst htn; rw [List.getElem?_set_self hset_lt, Option.getD_some]
            intro heq; have hlt := (hC_lit ik.toNat hik_lt).2.2
            have : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [heq] at hlt; omega
          · rw [List.getElem?_set_ne (by omega)]; exact hnesent_k t ht,
        fun idx hidx => by
          dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hout_k idx hidx,
        hm⟩
    · have hidx_k' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ik.toNat) % 2 ^ 64 =
          cref.toNat + 3 + ik.toNat := by c0_bound
      simp only [hidx_k', hl_eq] at hc
      have heq_nat : (C[ik.toNat]'(by omega) != drop.toNat) = false := by
        rw [hC_ik, bne_eq_false_iff_eq, hc]
      simp only [heq_nat, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep_filt
      exact hJs (nsz, ()) mlk ⟨st_k, hag_k, har_k_len, by rw [hstep_filt]; exact hnsz_eq,
        fun t ht => by rw [hstep_filt]; exact hpref_k t ht,
        fun t ht1 ht2 => htail_k t (by omega) ht2, hnesent_k, hout_k, hmlk⟩
  have hik_eq : ik.toNat = sz.toNat := by c0_bound
  have htake_all : C.take ik.toNat = C := List.take_of_length_le (by omega)
  rw [htake_all] at hnsz_eq hpref_k
  exact fwd_compaction_exit hdu hw_u har_u hstu_cv hstu_al hstu_fl href_c hng_cref hsz_eq
    hsz_ar_len hhdr_v hCu hC_lt hfilt_ent hrefs_u hrefs_c hAddUnit hAddBin hQ hJsOuter hstk_eq
    har_k_len hnsz_eq (by rw [hnsz_eq]; exact hfilt_lt_sz) hpref_k hnesent_k hout_k hmlk

end FullBvaFwdHelpers

end LeanQbe.T.Examples.Kissat.Full
