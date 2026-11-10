module

public import spike.frames.Frames
public import LeanQbe.Amd64.FrameLemmas

/-!
# Spike A1: `f` meets `FnSpec1`, with the stack bounds adding up
-/

@[expose] public section

namespace LeanQbe

namespace Frames

open Amd64 Std

/-! ## Addresses -/

theorem a1 (sp : BitVec 64) : sp - 8#64 - (16 : Int64).toBitVec = sp - 24#64 := by
  have : (16 : Int64).toBitVec = 16#64 := rfl
  rw [this]; bv_omega
theorem a2 (sp : BitVec 64) : sp - 24#64 + (0 : Int64).toBitVec = sp - 24#64 := by
  have : (0 : Int64).toBitVec = 0#64 := rfl
  rw [this]; bv_omega
theorem a3 (sp : BitVec 64) : sp - 24#64 - 8#64 = sp - 32#64 := by bv_omega
theorem a4 (sp : BitVec 64) : sp - 32#64 + BitVec.ofNat 64 8 = sp - 24#64 := by bv_omega
theorem a5 (sp : BitVec 64) : sp - 24#64 + (16 : Int64).toBitVec = sp - 8#64 := by
  have : (16 : Int64).toBitVec = 16#64 := rfl
  rw [this]; bv_omega
theorem a6 (sp : BitVec 64) : sp - 8#64 + 8#64 = sp := by bv_omega
theorem a7 (sp : BitVec 64) (n : Nat) : sp - 32#64 - BitVec.ofNat 64 n = sp - BitVec.ofNat 64 (32 + n) := by
  rw [BitVec.ofNat_add, BitVec.sub_sub]
theorem a8 (sp : BitVec 64) (n : Nat) : sp - BitVec.ofNat 64 (32 + n) + BitVec.ofNat 64 (n + 8) = sp - 24#64 := by
  bv_omega
theorem a9 (sp : BitVec 64) (n : Nat) :
    sp - BitVec.ofNat 64 (32 + n) + BitVec.ofNat 64 (n + 8 + 8) = sp - 16#64 := by
  bv_omega
theorem a10 (sp : BitVec 64) (n : Nat) :
    sp - BitVec.ofNat 64 (32 + n) + BitVec.ofNat 64 (n + 8 + 8 + 8) = sp - 8#64 := by
  bv_omega
theorem a11 (sp : BitVec 64) (n : Nat) :
    sp - BitVec.ofNat 64 (32 + n) + BitVec.ofNat 64 (n + 8 + 8 + 8 + 8) = sp := by
  bv_omega
theorem a12 (sp : BitVec 64) (n : Nat) :
    sp - BitVec.ofNat 64 (32 + n) + BitVec.ofNat 64 n = sp - 32#64 := by
  bv_omega

theorem a13 (sp : BitVec 64) (h : (sp + 8#64).toNat % 16 = 0) : (sp - 32#64 + 8#64).toNat % 16 = 0 := by
  bv_omega

/-! ## Memory shapes -/

theorem sep_ac {P Q : Mem 64 → Prop} {M : Mem 64} (e : P = Q) (h : P M) : Q M := e ▸ h

/-- f's stack bound split into g's region, g's return address slot, the spill slot, padding and
the rbx save slot. -/
theorem regions_entry (sp : BitVec 64) (n : Nat) (hn : n + 40 ≤ 2 ^ 64) :
    region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) =
      region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 32#64) 8 ⋆
        (region (sp - 24#64) 8 ⋆ (region (sp - 16#64) 8 ⋆ region (sp - 8#64) 8))) := by
  have b1 := a12 sp n
  have b2 := a8 sp n
  have b3 := a9 sp n
  have b4 := a10 sp n
  generalize sp - BitVec.ofNat 64 (32 + n) = X at b1 b2 b3 b4 ⊢
  rw [show 32 + n = n + 8 + 8 + 8 + 8 by omega,
    region_split (n1 := n + 8 + 8 + 8) (n2 := 8) (by omega),
    region_split (n1 := n + 8 + 8) (n2 := 8) (by omega),
    region_split (n1 := n + 8) (n2 := 8) (by omega),
    region_split (n1 := n) (n2 := 8) (by omega), b1, b2, b3, b4]
  simp only [ExtHashMap.sep_assoc]

theorem regions_exit (sp : BitVec 64) (n : Nat) (hn : n + 40 ≤ 2 ^ 64) :
    region (sp - BitVec.ofNat 64 (32 + n)) (n + 8) ⋆ (region (sp - 24#64) 8 ⋆
        (region (sp - 16#64) 8 ⋆ region (sp - 8#64) 8)) =
      region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) := by
  have b2 := a8 sp n
  have b3 := a9 sp n
  have b4 := a10 sp n
  generalize sp - BitVec.ofNat 64 (32 + n) = X at b2 b3 b4 ⊢
  rw [show 32 + n = n + 8 + 8 + 8 + 8 by omega,
    region_split (n1 := n + 8 + 8 + 8) (n2 := 8) (by omega),
    region_split (n1 := n + 8 + 8) (n2 := 8) (by omega),
    region_split (n1 := n + 8) (n2 := 8) (by omega), b2, b3, b4]
  simp only [ExtHashMap.sep_assoc]

theorem regions_ra (sp : BitVec 64) (n : Nat) (hn : n + 40 ≤ 2 ^ 64) :
    region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) ⋆ region sp 8 =
      region (sp - BitVec.ofNat 64 (32 + n)) (32 + n + 8) := by
  rw [region_split (n1 := 32 + n) (n2 := 8) (by omega)]
  congr 2
  bv_omega

theorem mem_entry {m M : Mem 64} {sp : BitVec 64} {ra : Int64} {n : Nat} {R : Mem 64 → Prop}
    (hn : n + 40 ≤ 2 ^ 64) (h : (Eq m ⋆ target.Entry sp ra (32 + n) ⋆ R) M) :
    (region (sp - 8#64) 8 ⋆ (region (sp - 24#64) 8 ⋆ (region (sp - 32#64) 8 ⋆
      (region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 16#64) 8 ⋆
      (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))))))) M := by
  have h' : (Eq m ⋆ (region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) ⋆
      Eq (ra.toUInt64.At sp)) ⋆ R) M := h
  rw [regions_entry sp n hn] at h'
  exact sep_ac (by ac_rfl) h'

theorem mem_exit {m M : Mem 64} {sp : BitVec 64} {ra : Int64} {n : Nat} {R : Mem 64 → Prop}
    {b w : Val} (hn : n + 40 ≤ 2 ^ 64)
    (h : (Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆ (region (sp - 16#64) 8 ⋆
      (word (sp - 8#64) w ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))) M) :
    (Eq m ⋆ target.Entry sp ra (32 + n) ⋆ R) M ∧ (Eq m ⋆ target.Exit sp (32 + n) ⋆ R) M := by
  have h' : (Eq m ⋆ region (sp - 32#64 - BitVec.ofNat 64 n) (n + 8) ⋆
      (word (sp - 24#64) b ⋆ (region (sp - 16#64) 8 ⋆
      (word (sp - 8#64) w ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))) M := h
  rw [a7] at h'
  have h2 : ((region (sp - BitVec.ofNat 64 (32 + n)) (n + 8) ⋆ (word (sp - 24#64) b ⋆
      (region (sp - 16#64) 8 ⋆ word (sp - 8#64) w))) ⋆ (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))) M :=
    sep_ac (by ac_rfl) h'
  have h3 : ((region (sp - BitVec.ofNat 64 (32 + n)) (n + 8) ⋆ (region (sp - 24#64) 8 ⋆
      (region (sp - 16#64) 8 ⋆ region (sp - 8#64) 8))) ⋆ (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))) M :=
    sep_mono (fun _ hx => sep_mono_r (fun _ hy => sep_mono_r
      (fun _ hz => sep_mono_r (fun _ => word_region) hz) (sep_mono (fun _ => word_region) hy)) hx) h2
  rw [regions_exit sp n hn] at h3
  refine ⟨?_, ?_⟩
  · show (Eq m ⋆ (region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) ⋆ Eq (ra.toUInt64.At sp)) ⋆ R) M
    exact sep_ac (by ac_rfl) h3
  have h4 : (region (sp - BitVec.ofNat 64 (32 + n)) (32 + n) ⋆ (region sp 8 ⋆ (Eq m ⋆ R))) M :=
    sep_mono_r (fun _ => sep_mono fun _ hx => target.retAddr_region _ ra _ hx) h3
  rw [← ExtHashMap.sep_assoc, regions_ra sp n hn] at h4
  show (Eq m ⋆ region (sp - BitVec.ofNat 64 (32 + n)) (32 + n + 8) ⋆ R) M
  exact sep_ac (by ac_rfl) h4

/-! ## Registers -/

/-- Register-file simp set: `get64` through `set64` on concrete or distinct registers. -/
theorem get64_set64_ne' {regs : Reg64s} {r r' : Reg64} {v : BitVec 64} (h : r' ≠ r) :
    (regs.set64 r v).get64 r' = regs.get64 r' := Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h)

/-! ## `f` meets its contract -/

theorem f_spec (h : Host) (k : Nat) (hc : fCode.IsInfixAt (@Host.prog h) k)
    (hu : @Host.LabelsUnique h) (hab : target.Defined h "abort") (n nX : Nat)
    (hX : nX ≤ 32 + n) (hn : n + 40 ≤ 2 ^ 64) (hg : target.FnSpec h "g" gSpec n nX) :
    target.FnSpec h "f" fSpec (32 + n) nX := by
  letI := h
  intro args m Q X hspec s ra R hargs _ hspE hmem
  obtain ⟨a, b, rfl, hXa, hTa⟩ := hspec
  have hab' : s.regs.get64 .rdi = a ∧ s.regs.get64 .rsi = b := by
    simpa [Target.ArgsIn, Target.ValsIn] using hargs
  obtain ⟨ha, hb⟩ := hab'
  -- the code
  have hgi := List.isInfixAt_iff_getElem?.mp hc
  have h0 : Host.prog[k]? = some (.label "f") := hgi 0 (by decide)
  have h1 : Host.prog[k + 1]? = some (pushD .rbx) := hgi 1 (by decide)
  have h2 : Host.prog[k + 2]? = some (subSpD 16) := hgi 2 (by decide)
  have h3 : Host.prog[k + 3]? = some (movD .rbx .rdi) := hgi 3 (by decide)
  have h4 : Host.prog[k + 4]? = some (stSpD .rsi 0) := hgi 4 (by decide)
  have h5 : Host.prog[k + 5]? = some (callD "g") := hgi 5 (by decide)
  have h6 : Host.prog[k + 6]? = some (ldSpD .rsi 0) := hgi 6 (by decide)
  have h7 : Host.prog[k + 7]? = some (ins (.add (.reg (q .rax)) (.reg (q .rbx)))) :=
    hgi 7 (by decide)
  have h8 : Host.prog[k + 8]? = some (ins (.add (.reg (q .rax)) (.reg (q .rsi)))) :=
    hgi 8 (by decide)
  have hjnz : (jnz .rax "f.ret").IsInfixAt Host.prog (k + 9) :=
    List.isInfixAt_iff_getElem?.mpr fun i hi => by
      rcases i with _ | _ | i
      · exact hgi 9 (by decide)
      · exact hgi 10 (by decide)
      · exfalso; simp [jnz] at hi; omega
  have h11 : Host.prog[k + 11]? = some (movD .rdi .rbx) := hgi 11 (by decide)
  have h12 : Host.prog[k + 12]? = some (addSpD 16) := hgi 12 (by decide)
  have h13 : Host.prog[k + 13]? = some (popD .rbx) := hgi 13 (by decide)
  have h14 : Host.prog[k + 14]? = some (jmpD "abort") := hgi 14 (by decide)
  have h15 : Host.prog[k + 15]? = some (.label "f.ret") := hgi 15 (by decide)
  have h16 : Host.prog[k + 16]? = some (addSpD 16) := hgi 16 (by decide)
  have h17 : Host.prog[k + 17]? = some (popD .rbx) := hgi 17 (by decide)
  have hret : ret.IsInfixAt Host.prog (k + 18) := List.isInfixAt_singleton.mpr (hgi 18 (by decide))
  have hlf : Labels.label "f" = Host.addrOf k := Host.label_eq_addrOf_of_unique hu h0
  have hlr : Labels.label "f.ret" = Host.addrOf (k + 15) := Host.label_eq_addrOf_of_unique hu h15
  show Eventually (step1 Host.exe) _ ⟨s, Labels.label "f"⟩
  rw [hlf]
  refine Host.eventually_label h0 ?_
  -- names for the entry stack pointer and rbx
  obtain ⟨sp, hsp⟩ : ∃ sp : BitVec 64, s.regs.get64 .rsp = sp := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : BitVec 64, s.regs.get64 .rbx = w := ⟨_, rfl⟩
  have hmem' : (Eq m ⋆ target.Entry sp ra (32 + n) ⋆ R) s.dmem := by rw [← hsp]; exact hmem
  have hspE' : (sp + 8#64).toNat % 16 = 0 := by rw [← hsp]; exact hspE
  have hM0 := mem_entry hn hmem'
  -- push %rbx
  refine eventually_pushD h1 (by rw [hsp]; exact hM0) fun s1 hs1 hm1 => ?_
  have hm1' : (word (sp - 8#64) w ⋆ (region (sp - 24#64) 8 ⋆ (region (sp - 32#64) 8 ⋆
      (region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 16#64) 8 ⋆
      (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))))))) s1.dmem := by
    rw [hsp, hw] at hm1; exact hm1
  -- sub $16, %rsp
  refine eventually_subSpD h2 fun s2 hs2 hm2 => ?_
  -- mov %rdi, %rbx
  refine eventually_movD h3 fun s3 hs3 hm3 => ?_
  have hsp3 : s3.regs.get64 .rsp = (sp - 24#64 : BitVec 64) := by
    rw [hs3, get64_set64_ne' (by decide), hs2, Reg64s.get64_set64_same, hs1,
      Reg64s.get64_set64_same, hsp, a1]
  have hrsi3 : s3.regs.get64 .rsi = b := by
    rw [hs3, get64_set64_ne' (by decide), hs2, get64_set64_ne' (by decide), hs1,
      get64_set64_ne' (by decide), hb]
  -- movq %rsi, (%rsp)
  refine eventually_stSpD h4
    (F := word (sp - 8#64) w ⋆ (region (sp - 32#64) 8 ⋆
      (region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 16#64) 8 ⋆
      (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))))))
    (by rw [hsp3, a2, hm3, hm2]; exact sep_ac (by ac_rfl) hm1') fun s4 hs4 hm4 => ?_
  rw [hsp3, a2, hrsi3] at hm4
  have hsp4 : s4.regs.get64 .rsp = (sp - 24#64 : BitVec 64) := by rw [hs4, hsp3]
  -- call g
  refine eventually_callD_any h5
    (F := word (sp - 24#64) b ⋆ (word (sp - 8#64) w ⋆
      (region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 16#64) 8 ⋆
      (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))))))
    (by rw [hsp4, a3]; exact sep_ac (by ac_rfl) hm4) fun s5 hs5 hm5 => ?_
  rw [hsp4, a3] at hm5
  have hm5' : (Eq ((Host.addrOf (k + 6)).toUInt64.At (sp - 32#64)) ⋆ (word (sp - 24#64) b ⋆
      (word (sp - 8#64) w ⋆ (region (sp - BitVec.ofNat 64 (32 + n)) n ⋆ (region (sp - 16#64) 8 ⋆
      (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ R))))))) s5.dmem := hm5
  have hsp5 : s5.regs.get64 .rsp = (sp - 32#64 : BitVec 64) := by rw [hs5, Reg64s.get64_set64_same, hsp4, a3]
  have hrdi5 : s5.regs.get64 .rdi = a := by
    rw [hs5, get64_set64_ne' (by decide), hs4, hs3, get64_set64_ne' (by decide), hs2,
      get64_set64_ne' (by decide), hs1, get64_set64_ne' (by decide), ha]
  have hrbx5 : s5.regs.get64 .rbx = a := by
    rw [hs5, get64_set64_ne' (by decide), hs4, hs3, Reg64s.get64_set64_same, hs2,
      get64_set64_ne' (by decide), hs1, get64_set64_ne' (by decide), ha]
  have hkeep5 : ∀ r, r ≠ .rsp → r ≠ .rbx → s5.regs.get64 r = s.regs.get64 r := by
    intro r hr1 hr2
    rw [hs5, get64_set64_ne' hr1, hs4, hs3, get64_set64_ne' hr2, hs2, get64_set64_ne' hr1, hs1,
      get64_set64_ne' hr1]
  -- g's contract
  have hg' := hg [a] m (fun rets m' => Truthy a ∧ rets = [a + a] ∧ m' = m) X
    ⟨a, rfl, fun ht => ⟨ht, rfl, rfl⟩, hXa⟩ s5 (Host.addrOf (k + 6))
    (word (sp - 24#64) b ⋆ (region (sp - 16#64) 8 ⋆ (word (sp - 8#64) w ⋆
      (Eq (ra.toUInt64.At sp) ⋆ R))))
    (by show [s5.regs.get64 .rdi] = [a]; rw [hrdi5]) trivial
    (by show (s5.regs.get64 .rsp + 8#64).toNat % 16 = 0; rw [hsp5]; exact a13 sp hspE')
    (by
      have e : target.get s5 target.sp = sp - 32#64 := hsp5
      rw [e]
      show (Eq m ⋆ (region (sp - 32#64 - BitVec.ofNat 64 n) n ⋆
        Eq ((Host.addrOf (k + 6)).toUInt64.At (sp - 32#64))) ⋆ _) s5.dmem
      rw [a7]
      exact sep_ac (by ac_rfl) hm5')
  refine eventually_trans _ _ _ _ hg' ?_
  rintro ⟨s6, pc⟩ (hst | hst)
  rotate_left
  · -- g exits: propagate, with f's frame folded into the exit frame
    obtain ⟨sym', as, m', hX', hdef, hpc, hargs', hspE'', ra', n', F, hnX, hra', hm'⟩ := hst
    refine .done _ (Or.inr ⟨sym', as, m', hX', hdef, hpc, hargs', hspE'', ra', n',
      F ⋆ (word (sp - 24#64) b ⋆ (region (sp - 16#64) 8 ⋆ (word (sp - 8#64) w ⋆
        Eq (ra.toUInt64.At sp)))), hnX, hra', sep_ac (by ac_rfl) hm'⟩)
  obtain ⟨hpc, rets, m', ⟨hta, rfl, hmm⟩, hrets, ⟨hcs6, hsp6⟩, hm6⟩ := hst
  subst m'
  obtain ⟨hT, hNT⟩ := hTa hta
  change pc = _ at hpc
  subst hpc
  have hrax6 : s6.regs.get64 .rax = a + a := by
    simpa [Target.RetsIn, Target.ValsIn] using hrets
  have hsp6' : s6.regs.get64 .rsp = (sp - 24#64 : BitVec 64) := by
    have : s6.regs.get64 .rsp = s5.regs.get64 .rsp + BitVec.ofNat 64 8 := hsp6
    rw [this, hsp5, a4]
  have hcs6' : ∀ r, r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] →
      s6.regs.get64 r = s5.regs.get64 r := hcs6
  have hm6' : (Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆
      (region (sp - 16#64) 8 ⋆ (word (sp - 8#64) w ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))) s6.dmem := by
    rw [← hsp5]; exact hm6
  obtain ⟨hmEntry, hmExit⟩ := mem_exit hn hm6'
  -- movq (%rsp), %rsi
  refine eventually_ldSpD h6 (v := b)
    (F := Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (region (sp - 16#64) 8 ⋆
      (word (sp - 8#64) w ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))
    (by rw [hsp6', a2]; exact sep_ac (by ac_rfl) hm6') fun s7 hs7 hm7 => ?_
  -- add %rbx, %rax; add %rsi, %rax
  refine eventually_addRR h7 fun s8 hs8 hm8 => ?_
  refine eventually_addRR h8 fun s9 hs9 hm9 => ?_
  have hrax9 : s9.regs.get64 .rax = fVal a b := by
    simp only [hs9, hs8, hs7, Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hrax6, hcs6' _ (by simp), hrbx5]
    rfl
  have hkeep9 : ∀ r, r ≠ .rsi → r ≠ .rax → s9.regs.get64 r = s6.regs.get64 r := by
    intro r hr1 hr2
    rw [hs9, get64_set64_ne' hr2, hs8, get64_set64_ne' hr2, hs7, get64_set64_ne' hr1]
  have hm9 : s9.dmem = s6.dmem := by rw [hm9, hm8, hm7]
  have hsp9 : s9.regs.get64 .rsp = (sp - 24#64 : BitVec 64) := by rw [hkeep9 _ (by decide) (by decide), hsp6']
  -- callee-saved registers other than rbx, at s9
  have hcs9 : ∀ r, r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15] → s9.regs.get64 r = s.regs.get64 r := by
    intro r hr
    have hr' : r ≠ .rsi ∧ r ≠ .rax ∧ r ≠ .rsp ∧ r ≠ .rbx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    have hr'' : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hkeep9 r hr'.1 hr'.2.1, hcs6' r hr'', hkeep5 r hr'.2.2.1 hr'.2.2.2]
  -- test %eax, %eax; jnz f.ret
  refine eventually_jnz hjnz hlr fun s10 hs10 hm10 => ⟨fun htr => ?_, fun hntr => ?_⟩
  · -- return path
    rw [hrax9] at htr
    refine Host.eventually_label h15 ?_
    refine eventually_addSpD h16 fun s11 hs11 hm11 => ?_
    have hsp11 : s11.regs.get64 .rsp = (sp - 8#64 : BitVec 64) := by
      rw [hs11, Reg64s.get64_set64_same, hs10, hsp9, a5]
    refine eventually_popD h17 (v := w)
      (F := Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆
        (region (sp - 16#64) 8 ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))
      (by rw [hsp11, hm11, hm10, hm9]; exact sep_ac (by ac_rfl) hm6') fun s12 hs12 hm12 => ?_
    have hsp12 : s12.regs.get64 .rsp = sp := by
      rw [hs12, get64_set64_ne' (by decide), Reg64s.get64_set64_same, hsp11, a6]
    have hm12' : s12.dmem = s6.dmem := by rw [hm12, hm11, hm10, hm9]
    refine eventually_ret hret (ra := ra)
      (R := Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆
        (region (sp - 16#64) 8 ⋆ (word (sp - 8#64) w ⋆ R))))
      (by
        rw [hsp12, hm12']
        show (Eq (ra.toUInt64.At sp) ⋆ (Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆
          (region (sp - 16#64) 8 ⋆ (word (sp - 8#64) w ⋆ R))))) s6.dmem
        exact sep_ac (by ac_rfl) hm6') (.done _ (Or.inl ?_))
    refine ⟨rfl, [fVal a b], m, hT htr, ?_, ⟨?_, ?_⟩, ?_⟩
    · show [(s12.regs.set64 .rsp _).get64 .rax] = [fVal a b]
      rw [get64_set64_ne' (by decide), hs12, get64_set64_ne' (by decide),
        get64_set64_ne' (by decide), hs11, get64_set64_ne' (by decide), hs10, hrax9]
    · intro r hr
      show (s12.regs.set64 .rsp _).get64 r = s.regs.get64 r
      have hr1 : r ≠ .rsp := by
        intro he; subst he; simp at hr
      rw [get64_set64_ne' hr1, hs12]
      by_cases hr2 : r = .rbx
      · subst hr2; rw [Reg64s.get64_set64_same, hw]
      · rw [get64_set64_ne' hr2, get64_set64_ne' hr1, hs11, get64_set64_ne' hr1, hs10]
        apply hcs9
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h
        · exact absurd h hr2
        all_goals simp [h]
    · show (s12.regs.set64 .rsp (s12.regs.get64 .rsp + 8#64)).get64 .rsp =
        s.regs.get64 .rsp + BitVec.ofNat 64 8
      rw [Reg64s.get64_set64_same, hsp12, hsp]
    · show (Eq m ⋆ target.Exit (s.regs.get64 .rsp) (32 + n) ⋆ R) s12.dmem
      rw [hm12', hsp]
      exact hmExit
  · -- exit path
    rw [hrax9] at hntr
    refine eventually_movD h11 fun s11 hs11 hm11 => ?_
    refine eventually_addSpD h12 fun s12 hs12 hm12 => ?_
    have hsp12 : s12.regs.get64 .rsp = (sp - 8#64 : BitVec 64) := by
      rw [hs12, Reg64s.get64_set64_same, hs11, get64_set64_ne' (by decide), hs10, hsp9, a5]
    refine eventually_popD h13 (v := w)
      (F := Eq m ⋆ target.Exit (sp - 32#64) n ⋆ (word (sp - 24#64) b ⋆
        (region (sp - 16#64) 8 ⋆ (Eq (ra.toUInt64.At sp) ⋆ R))))
      (by rw [hsp12, hm12, hm11, hm10, hm9]; exact sep_ac (by ac_rfl) hm6')
      fun s13 hs13 hm13 => ?_
    have hm13' : s13.dmem = s6.dmem := by rw [hm13, hm12, hm11, hm10, hm9]
    have hsp13 : s13.regs.get64 .rsp = sp := by
      rw [hs13, get64_set64_ne' (by decide), Reg64s.get64_set64_same, hsp12, a6]
    refine eventually_jmpD_any h14 (.done _ (Or.inr ⟨"abort", [a], m, hNT hntr, hab, rfl, ?_,
      ?_, ra, 32 + n, ExtHashMap.emp, hX, trivial, ?_⟩))
    · show [s13.regs.get64 .rdi] = [a]
      rw [hs13, get64_set64_ne' (by decide), get64_set64_ne' (by decide), hs12,
        get64_set64_ne' (by decide), hs11, Reg64s.get64_set64_same, hs10,
        hkeep9 _ (by decide) (by decide), hcs6' _ (by simp), hrbx5]
    · show (s13.regs.get64 .rsp + 8#64).toNat % 16 = 0
      rw [hsp13]; exact hspE'
    · show (Eq m ⋆ target.Entry (s13.regs.get64 .rsp) ra (32 + n) ⋆ ExtHashMap.emp ⋆ R) s13.dmem
      rw [hm13', hsp13, ExtHashMap.sep_emp]
      exact hmEntry

end Frames

end LeanQbe
