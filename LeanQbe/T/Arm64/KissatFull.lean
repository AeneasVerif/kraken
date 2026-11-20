module
public import LeanQbe.T.Arm64.KissatFullCert
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Arm64.TargLemmas
import all Std.Sat.CNF.Basic
import all Kraken.Mem
import all Kraken.Separation
set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T.Arm64.KissatFull
open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.LratBytes LeanQbe.T.Arm64 Kraken
@[reducible] def kissatFull_compiled_arm64 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean fullModule :=
  KissatFullCert.fullCert
private theorem solve_in_fullModule : Full.kissat_solve_bytes ∈ fullModule.fns := by
  change Full.kissat_solve_bytes ∈ fullFns; dsimp only [fullFns]; repeat apply List.mem_append_right
  exact List.mem_of_getElem? (rfl : full4_fns[37]? = some Full.kissat_solve_bytes)
private theorem fullEnv_names_eq (spec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fullSpecTable spec).map SpecEntry.name = fullFns.map Fn.name := by
  have h := congrArg (List.map Prod.fst) (fullSpecTable_sigs spec)
  simp only [List.map_map] at h; exact h
theorem full_module_fnspec [hh : Host] (hmok : ModuleOk fullEnv fullModule) (k₀ : Nat)
    (hc : kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fullModule.fns) : armTarget.Defined hh f.name ∧ armTarget.FnSpec hh
    f.name (fullEnv f.name f.as f.rs) (kissatFull_compiled_arm64.bound f.name) 0 := by
  refine KissatFullCert.mk_module_fnspec fullEnv (fun g hg args m Q X hs => ?_) (fun g _ args m Q
    X X' => Env.ofTable_noExit (fullSpecTable_noExit fullSolveBytesSpec) g.name g.as g.rs args m Q
    X X') k₀ hc hu hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
  exact (hmok.fnsOk pre g post hsp).2.2 args m Q X hs
section Unsat
variable [hh : Host] (hmok : ModuleOk fullEnv fullModule) (k₀ : Nat) (hc :
  kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) (cnf_ptr work_ptr
  fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat) (hcfit : cnf_ptr.toNat + cnfBytes.length
  < 2 ^ 64) (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (s : MachineData) (ra : Int64) (R : Mem 64 →
  Prop) (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr) (hx1 : (s.regs.getXReg .X1).toBitVec =
  BitVec.ofNat 64 cnfBytes.length) (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr) (hx3 :
  (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen) (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
  (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0) (hmem : (bytes cnf_ptr
  cnfBytes ⋆ region work_ptr wlen ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64
  (kissatFull_compiled_arm64.bound "kissat_solve_bytes")) (kissatFull_compiled_arm64.bound
  "kissat_solve_bytes") ⋆ R) s.dmem)
include hh hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4
  hra hsp hmem
theorem full_solve_bytes_unsat_arm64 :
    Eventually (step1 Host.exe) (fun st => st.pc = ra ∧ ((st.data.regs.getXReg .X0).toBitVec = 0#64
      ∨ (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨ (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
      ((st.data.regs.getXReg .X0).toBitVec = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      cnf.Unsat) ∧ (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st.data.regs.getXReg r = s.regs.getXReg r) ∧ st.data.regs.SP = s.regs.SP ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64
        (kissatFull_compiled_arm64.bound "kissat_solve_bytes")) (kissatFull_compiled_arm64.bound
        "kissat_solve_bytes") ⋆ R) st.data.dmem) ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (full_module_fnspec hmok k₀ hc hu solve_in_fullModule).2
  rcases hmem with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, hm_r⟩
  have hspec : fullEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] (cnf_ptr, BitVec.ofNat
      64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m (fun r m' => (r.fst = 0#64 ∨
      r.fst = 10#64 ∨ r.fst = 20#64) ∧ (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      cnf.Unsat) ∧ (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m') (fun _ _ _ _ => False) :=
    Env.ofTable_of_mem (List.mem_of_getElem? (rfl : (fullSpecTable _)[165]? = some _))
      (fullEnv_names_eq fullSolveBytesSpec ▸ hmok.nodup) ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit,
        hwfit, by rw [sep_emp]; exact hm_in,
        fun _ _ h u' m' => by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (KissatFullCert.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _
    fuel hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩)
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩, ⟨ma, mr2, u3, d3, ⟨_, ms2, u4, d4, rfl, hs⟩,
    hr⟩⟩; exact ⟨hpc, hdom, hu', hcal, hsp', ⟨ma, mr2, u3, d3, ⟨m', ms2, u4, d4, hm', hs⟩, hr⟩⟩
theorem full_solve_bytes_unsat_sound_arm64 :
    Eventually (step1 Host.exe) (fun st => st.pc = ra ∧ ((st.data.regs.getXReg .X0).toBitVec = 0#64
      ∨ (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨ (st.data.regs.getXReg .X0).toBitVec = 20#64)
      ∧ ((st.data.regs.getXReg .X0).toBitVec = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      cnf.Unsat)) ⟨s, Labels.label "kissat_solve_bytes"⟩ := eventually_weaken _ _ _ _ (fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1⟩) (full_solve_bytes_unsat_arm64 hmok k₀ hc hu cnf_ptr work_ptr fuel
    cnfBytes wlen hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)
end Unsat
private abbrev nvBytes : List UInt8 :=
  [99,32,97,97,97,10,112,32,99,110,102,32,49,32,50,10,49,32,48,10,45,49,32,48]
private theorem nv_cnf : ∃ cnf, parseDimacs nvBytes = some cnf ∧ cnf.Unsat := by
  refine ⟨(CNF.empty.add (CNF.Clause.empty.add 1 true)).add (CNF.Clause.empty.add 1 false), rfl, ?_⟩
  intro a; cases ha1 : a 1 <;> simp [CNF.eval_add, CNF.eval_empty, CNF.Clause.eval_add, ha1]
private def nvEntry : SpecEntry :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fun (cp, cl, wp, wl, fl, ()) m Q _ =>
    cp = 0x1000#64 ∧ cl = BitVec.ofNat 64 nvBytes.length ∧ wp = 0x1018#64 ∧ wl = 2048#64 ∧
    fl = 1#64 ∧ (bytes cp nvBytes ⋆ region wp 2048) m ∧
    ∀ m', (bytes cp nvBytes ⋆ region wp 2048) m' → Q (20#64, ()) m', true⟩
private abbrev nvEnv : Env := Env.ofTable (nvEntry :: fullSpecTable fullSolveBytesSpec)
private theorem wp_cmp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64} {b : Bool}
    {o : CmpOp} {args : Tup (Arg Val) [i64, i64]} {t e : Expr Val Cont rs}
    (hb : o.evalBits args.fst.val args.snd.fst.val = b) (hk : wp Γ Q X (cond b t e) m) :
    wp Γ Q X (Expr.let_ { sig := [i64, i64], code := OpCode.cmp o i64 Ty.bool rfl, args := args }
      fun p => Expr.jnz (Arg.var p.fst) t e) m := by
  rw [wp_let_cmp_eq, wp.eq_5]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]; cases b
  · exact ⟨fun h => (by change o.evalBits _ _ = true at h; rw [hb] at h; cases h), fun _ => hk⟩
  · exact ⟨fun _ => hk, fun h => (by change o.evalBits _ _ = false at h; rw [hb] at h; cases h)⟩
private theorem nv_witness_wp (hnd_fns : (fullFns.map Fn.name).Nodup)
    (args : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hn : nvEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] args m Q X) :
    Func.wp nvEnv Full.kissat_solve_bytes.body args m Q X := by
  rcases args with ⟨_, _, _, _, _, ⟨⟩⟩; dsimp only [nvEnv, nvEntry] at hn
  rw [Env.ofTable_cons_self] at hn; rcases hn with ⟨rfl, rfl, rfl, rfl, rfl, hm, hQ⟩
  dsimp only at hm hQ; dsimp only [Func.wp, Full.kissat_solve_bytes, Full.kissat_solve_bytes_body]
  iterate 3 (apply wp_cmp (b := false) (by decide); dsimp only [cond])
  iterate 2 (rw [wp_let_not_eq, wp_let_sub_eq]; simp only [Ty.hasFloat, Bool.false_eq_true,
    ↓reduceIte]; apply wp_cmp (b := false) (by decide); dsimp only [cond])
  rw [wp_let_and_eq, wp_let_sub_eq, wp_let_and_eq, wp_let_add_eq]; simp only [Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]; apply wp_cmp (b := false) (by decide); dsimp only [cond]
  rw [wp_let_add_eq, wp_let_sub_eq, wp_let_add_eq]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  have hnd : ((fullSpecTable fullSolveBytesSpec).map SpecEntry.name).Nodup :=
    fullEnv_names_eq fullSolveBytesSpec ▸ hnd_fns
  have h_hdr : parseHeader nvBytes = some (1, 2, nvBytes.drop 15) := by decide
  rw [wp.eq_4]; refine ⟨_, fun _ _ _ _ => False, ?_, fun _ _ h => h, fun _ _ _ _ h => h.elim⟩
  dsimp only [nvEnv, nvEntry]; rw [Env.ofTable_cons_ne (by decide)]
  refine Env.ofTable_of_mem (List.mem_of_getElem? (rfl : (fullSpecTable _)[41]? = some _)) hnd
    ⟨nvBytes, emp, rfl, by decide, by decide, by decide, by rw [sep_emp]; exact hm,
      ⟨fun _ _ hb => absurd (hb 1 2 (nvBytes.drop 15) h_hdr) (by decide),
      fun c s j rest _ hhdr hav hph _ hd hinv hcv hdcur hal _ hte hpr hcl _ _ hprob _ _ hoom hinc
        hvals hwvec _ _ _ hm' => ?_⟩⟩
  have hpeq : c.mv = 1 ∧ c.nc = 2 ∧ rest = nvBytes.drop 15 := by
    have h := Option.some.inj (hph.symm.trans h_hdr); rwa [Prod.mk.injEq, Prod.mk.injEq] at h
  have hj15 : j = 15 := by have := congrArg List.length (hd.trans hpeq.2.2); simp at this; omega
  subst hj15; dsimp only; rw [wp.eq_5]; refine ⟨fun _ => ?_, fun h => by cases h⟩
  rw [wp.eq_4]; refine ⟨_, fun _ _ _ _ => False, ?_, fun _ _ h => h, fun _ _ _ _ h => h.elim⟩
  rw [Env.ofTable_cons_ne (by decide)]
  refine Env.ofTable_of_mem (List.mem_of_getElem? (rfl : (fullSpecTable _)[44]? = some _)) hnd
    ⟨c, s, 0x1000#64, nvBytes, 15, emp, hhdr.symm, rfl, by decide, by decide,
      by rw [hpeq.1, hpeq.2.1]; exact h_hdr, hcv, hdcur, hcl, hte, hpr, hal, hoom, hprob, hinc,
      hvals, hwvec, hinv, hm', fun r s' m'' hlen _ _ _ _ _ _ htr hm'' => ?_⟩
  have htake : List.take (2 * c.mv) s.core.vals = List.replicate 2 0#8 := by
    rw [hvals, List.take_replicate, hpeq.1]; have := c.hbva
    simp [Nat.min_eq_left (by omega : 2 ≤ 2 * c.max_vars)]
  obtain rfl : r = 20#64 := htr (by
    rw [htake, hpeq.1, hpeq.2.1]
    exact UnitUnsatTrace.step (l := 0) (by decide) rfl (by decide)
      (UnitUnsatTrace.conflict (l := 1) (by decide) rfl (by decide) ⟨_, rfl⟩))
  dsimp only; apply wp_cmp (b := true) (by decide); dsimp only [cond]; rw [wp.eq_7]; apply hQ
  rw [sep_emp] at hm''; rcases hm'' with ⟨m1, m2, hm12, hm12d, hm_b, hm_fm⟩
  have hreg := fullMem_anyDimacs_to_region hlen hm_fm; rw [hhdr, hav] at hreg
  exact ⟨m1, m2, hm12, hm12d, hm_b, hreg⟩
private theorem eq_of_map_nodup : ∀ {l : List Fn} (_ : (l.map Fn.name).Nodup) {a b : Fn},
    a ∈ l → b ∈ l → a.name = b.name → a = b
  | _ :: _, _, _, _, .head _, .head _, _ => rfl
  | _ :: _, h, _, _, .head _, .tail _ hb, e =>
    absurd (e.symm ▸ List.mem_map.mpr ⟨_, hb, rfl⟩) (List.nodup_cons.mp h).1
  | _ :: _, h, _, _, .tail _ ha, .head _, e =>
    absurd (e ▸ List.mem_map.mpr ⟨_, ha, rfl⟩) (List.nodup_cons.mp h).1
  | _ :: _, h, _, _, .tail _ ha, .tail _ hb, e => eq_of_map_nodup (List.nodup_cons.mp h).2 ha hb e
private theorem pre_ne_solve {pre post : List Fn} {fn : Fn} (hsp : fullModule.fns = pre ++ fn ::
    post) (hnd : (fullFns.map Fn.name).Nodup) {g : Fn} (hg : g ∈ pre) :
    g.name ≠ "kissat_solve_bytes" := by
  intro hgn; have hm : (pre.map Fn.name ++ (fn :: post).map Fn.name).getLast? =
      some "kissat_solve_bytes" := by rw [← List.map_append, ← hsp]; rfl
  rw [List.getLast?_append] at hm; cases he : ((fn :: post).map Fn.name).getLast?
  · simp at he
  · rw [he] at hm; cases hm
    have hnd' := List.nodup_append.mp (by rw [← List.map_append, ← hsp]; exact hnd)
    exact hnd'.2.2 _ (List.mem_map.mpr ⟨g, hg, hgn⟩) _ (List.mem_of_getLast? he) rfl

theorem full_unsat_nonvacuous_arm64 [hh : Host] (hmok : ModuleOk fullEnv fullModule) (k₀ : Nat)
    (hc : kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat) (s : MachineData)
      (ra : Int64) (R : Mem 64 → Prop), cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧ (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧ (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64
      wlen ∧ (s.regs.getXReg .X4).toBitVec = fuel ∧ s.regs.X30 = ra.toUInt64 ∧ s.regs.SP.toNat % 16
      = 0 ∧ (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ region (s.regs.SP.toBitVec -
      BitVec.ofNat 64 (kissatFull_compiled_arm64.bound "kissat_solve_bytes"))
      (kissatFull_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧ Eventually (step1
      Host.exe) (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧ ∃ cnf,
      parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hnd : (fullFns.map Fn.name).Nodup := hmok.nodup
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes" (nvEnv "kissat_solve_bytes" [i64, i64, i64,
      i64, i64] [i64]) (kissatFull_compiled_arm64.bound "kissat_solve_bytes") 0 := by
    refine (KissatFullCert.mk_module_fnspec nvEnv (fun g hg args m Q X hs => ?_) (fun g _ args m Q
      X X' => Env.ofTable_noExit (fun e he => List.mem_cons.mp he |>.elim (fun h => h ▸ rfl)
        (fullSpecTable_noExit fullSolveBytesSpec e)) g.name g.as g.rs args m Q X X') k₀ hc hu
      solve_in_fullModule).2
    by_cases hnm : g.name = "kissat_solve_bytes"
    · have heq := eq_of_map_nodup hnd hg solve_in_fullModule hnm; subst heq
      exact nv_witness_wp hnd args m Q X hs
    · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
      obtain ⟨hwf, hca, hbd⟩ := hmok.fnsOk pre g post hsp
      dsimp only [nvEnv, nvEntry] at hs; rw [Env.ofTable_cons_ne (Ne.symm hnm)] at hs
      refine wp_env_agree_of_callsOk (hwf _ (fun _ => Unit) _ (fun _ => Unit) args (Tup.units g.as))
        hca (fun fnm _ _ hc' _ _ _ _ hf => ?_) m (hbd args m Q X hs)
      have hne : fnm ≠ "kissat_solve_bytes" := by
        rcases List.mem_append.mp hc' with h | h
        · obtain ⟨z, hz, hs'⟩ := List.mem_map.mp h; cases hs'; exact pre_ne_solve hsp hnd hz
        · simp [fullModule] at h
      dsimp only [nvEnv, nvEntry]; rw [Env.ofTable_cons_ne (Ne.symm hne)]; exact hf
  let b := kissatFull_compiled_arm64.bound "kissat_solve_bytes"
  let bs := nvBytes ++ List.replicate 2048 0
  let s := armInitState b bs (as := [i64, i64, i64, i64, i64])
    (0x1000#64, BitVec.ofNat 64 nvBytes.length, 0x1018#64, 2048#64, 1#64, ())
  have h1 := armInitMem_entry b bs (by decide) (by rw [show bs = nvBytes ++
    List.replicate 2048 0 from rfl, List.length_append, List.length_replicate]; decide)
  change (Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp) s.dmem at h1
  rw [show bs = nvBytes ++ List.replicate 2048 0 from rfl, Mem.At_append_sep nvBytes
    (List.replicate 2048 0) 0x1000#64 (by rw [List.length_replicate]; decide), sep_assoc] at h1
  have hdm : (bytes 0x1000#64 nvBytes ⋆ region 0x1018#64 2048 ⋆ region (s.regs.SP.toBitVec -
      BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by
    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]
    have h3 := sep_mono_mid (fun _ h => show region 0x1018#64 2048 _ from
      ⟨List.replicate 2048 0, List.length_replicate, h.symm⟩) h1
    dsimp only [Target.Entry, armTarget, armFrameSpec] at h3
    simp only [region_zero, sep_emp] at h3 ⊢; exact h3
  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide
  refine ⟨0x1000#64, 0x1018#64, 1#64, nvBytes, 2048, s, 0x1234, emp, by decide, by decide, rfl,
    rfl, rfl, rfl, rfl, rfl, hhsp, hdm, ?_⟩
  rcases hdm with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, hm_r⟩
  have hspec : nvEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] (0x1000#64,
      BitVec.ofNat 64 nvBytes.length, 0x1018#64, 2048#64, 1#64, ()) m (fun r _ => r.fst = 20#64)
      (fun _ _ _ _ => False) := by dsimp only [nvEnv, nvEntry]; rw [Env.ofTable_cons_self]
                                   exact ⟨rfl, rfl, rfl, rfl, rfl, hm_in, fun _ _ => rfl⟩
  have hev := KissatFullCert.solve_arm64_of_fnspec hfn 0x1000#64 _ 0x1018#64 _ 1#64 hspec s 0x1234
    emp rfl rfl rfl rfl rfl rfl hhsp ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩
  exact eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, _, _, h20, _⟩ => ⟨hpc, h20, nv_cnf⟩) hev
end LeanQbe.T.Arm64.KissatFull
