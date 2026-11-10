module

public import spike.frames.Frames
public import LeanQbe.Amd64.FrameLemmas

/-!
# Spike A1: `f` meets `FnSpec` v1, and non-vacuity

* `f_spec`: from `g`'s `FnSpec … n nX`, `f` meets `FnSpec … (32 + n) nX` (frame 24 bytes, + 8 for
  g's return address). The entry region is split into g's region, g's return-address slot, the
  spill slot, padding and the rbx save slot (`regions_entry`); `g`'s exit is propagated with f's
  frame folded into the exit frame; f's own exit is call-ready with f's entry stack.
* Non-vacuity in a concrete host `fCode ++ gCode ++ abortCode`, with `g_spec`, `f_spec`,
  `abort_spec` linked (`n = 8`, `nX = 8`): `f_returns` (`f(1, 2) = 5`), `f_exits_in_g` (`f(0, 2)`:
  `g` exits to `abort(0)`), `f_exits_itself` (`f(1, -3)`: `f` exits to `abort(1)`); each exit state
  is fed into `abort`'s `FnSpec` (`AbortsWith`). Statements are Kraken-level (`step1 Host.exe`).
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

/-! ## Non-vacuity: a concrete host with `f`, `g` and `abort` -/

/-- An entry stack of `n` bytes with return address `ra` keeps only the return address as the
callee's entry footprint (`n = 0`), the `n` bytes go to the frame. Used to feed an exit state to
the exit target's `FnSpec` without knowing a bound on the exit stack. -/
theorem entry_zero {m M : Mem 64} {sp : BitVec 64} {ra : Int64} {n : Nat} {F R : Mem 64 → Prop}
    (h : (Eq m ⋆ target.Entry sp ra n ⋆ F ⋆ R) M) :
    (Eq m ⋆ target.Entry sp ra 0 ⋆ (region (sp - BitVec.ofNat 64 n) n ⋆ F ⋆ R)) M := by
  have h' : (Eq m ⋆ (region (sp - BitVec.ofNat 64 n) n ⋆ Eq (ra.toUInt64.At sp)) ⋆ F ⋆ R) M := h
  show (Eq m ⋆ (region (sp - BitVec.ofNat 64 0) 0 ⋆ Eq (ra.toUInt64.At sp)) ⋆
    (region (sp - BitVec.ofNat 64 n) n ⋆ F ⋆ R)) M
  rw [region_zero, ExtHashMap.emp_sep]
  exact sep_ac (by ac_rfl) h'

/-- The host program: `f`, `g`, `abort`. Labels at 0 (`f`), 15 (`f.ret`), 19 (`g`), 23 (`g.ok`),
29 (`abort`). -/
def prog : Program := fCode ++ gCode ++ abortCode

/-- Labels take no space, every instruction 4 bytes (any positive sizes would do). -/
@[instance_reducible] def layout : Layout :=
  { start := 0x1000, size := fun i => if i = 0 ∨ i = 15 ∨ i = 19 ∨ i = 23 ∨ i = 29 then 0 else 4 }

abbrev host : Host :=
  .ofLayout prog layout
    (fun i d hd hz => by
      have hz' : (if i = 0 ∨ i = 15 ∨ i = 19 ∨ i = 23 ∨ i = 29 then 0 else 4) = 0 := hz
      have hi : i = 0 ∨ i = 15 ∨ i = 19 ∨ i = 23 ∨ i = 29 := by
        by_cases h : i = 0 ∨ i = 15 ∨ i = 19 ∨ i = 23 ∨ i = 29
        · exact h
        · simp [h] at hz'
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact ⟨"f", (Option.some.inj (hd.symm.trans (rfl : prog[0]? = some (.label "f"))))⟩
      · exact ⟨"f.ret",
          (Option.some.inj (hd.symm.trans (rfl : prog[15]? = some (.label "f.ret"))))⟩
      · exact ⟨"g", (Option.some.inj (hd.symm.trans (rfl : prog[19]? = some (.label "g"))))⟩
      · exact ⟨"g.ok",
          (Option.some.inj (hd.symm.trans (rfl : prog[23]? = some (.label "g.ok"))))⟩
      · exact ⟨"abort",
          (Option.some.inj (hd.symm.trans (rfl : prog[29]? = some (.label "abort"))))⟩)
    (by decide)

section Concrete

attribute [local instance] host

theorem host_unique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

theorem host_prog : ((fCode ++ gCode) ++ abortCode).IsInfixAt Host.prog 0 := List.prefix_refl _

theorem host_f : fCode.IsInfixAt Host.prog 0 := host_prog.append.1.append.1

theorem host_g : gCode.IsInfixAt Host.prog 19 := host_prog.append.1.append.2

theorem host_abort : abortCode.IsInfixAt Host.prog 29 := host_prog.append.2

theorem host_defined : target.Defined host "abort" := ⟨29, rfl⟩

/-- `g` within 8 bytes, leaving 8 to its exit target. -/
theorem host_g_spec : target.FnSpec host "g" gSpec 8 8 :=
  g_spec host 19 host_g host_unique host_defined 8 8 (Nat.le_refl _) (by decide)

/-- `f` within `32 + 8` bytes, leaving 8 to its exit target. -/
theorem host_f_spec : target.FnSpec host "f" fSpec 40 8 :=
  f_spec host 0 host_f host_unique host_defined 8 8 (by decide) (by decide) host_g_spec

theorem host_abort_spec : target.FnSpec host "abort" abortSpec 0 0 :=
  abort_spec host 29 host_abort host_unique 0 0 (by decide)

/-- The caller's return address. -/
def raF : Int64 := 0x1234
def z40 : List UInt8 := List.replicate 40 0
def z8 : List UInt8 := List.replicate 8 0
/-- The source memory: 8 zero bytes at `0x8000`. -/
def m0 : Mem 64 := z8.At 0x8000#64
/-- 40 free bytes below `rsp = 0x7ff8`, the return address at `rsp`, then the source memory. -/
def dmem0 : Mem 64 := (z40 ++ (raF.toUInt64.toBytes ++ z8)).At 0x7fd0#64

/-- A start state with `rdi`, `rsi` as given. -/
def st0 (a b : UInt64) : MachineData := { regs := { rdi := a, rsi := b, rsp := 0x7ff8 }, dmem := dmem0 }

theorem dmem0_split :
    (Eq m0 ⋆ target.Entry 0x7ff8#64 raF 40 ⋆ ExtHashMap.emp) dmem0 := by
  have hl : raF.toUInt64.toBytes.length = 8 := UInt64.toBytes_length _
  have e1 := Mem.At_append_sep z40 (raF.toUInt64.toBytes ++ z8) 0x7fd0#64
    (by simp [z40, z8, hl])
  have e2 := Mem.At_append_sep raF.toUInt64.toBytes z8 0x7ff8#64 (by simp [z8, hl])
  have l40 : z40.length = 40 := by simp [z40]
  rw [l40, show (0x7fd0#64 + BitVec.ofNat 64 40) = 0x7ff8#64 from rfl, e2, hl,
    show (0x7ff8#64 + BitVec.ofNat 64 8) = 0x8000#64 from rfl] at e1
  have h : (Eq (z40.At 0x7fd0#64) ⋆ (Eq (raF.toUInt64.toBytes.At 0x7ff8#64) ⋆
      Eq (z8.At 0x8000#64))) dmem0 := (congrFun e1 dmem0).mp rfl
  have h2 : (region 0x7fd0#64 40 ⋆ (Eq (raF.toUInt64.toBytes.At 0x7ff8#64) ⋆
      Eq (z8.At 0x8000#64))) dmem0 := sep_mono (fun _ hx => ⟨z40, l40, hx.symm⟩) h
  show (Eq (z8.At 0x8000#64) ⋆ (region (0x7ff8#64 - BitVec.ofNat 64 40) 40 ⋆
    Eq (raF.toUInt64.toBytes.At 0x7ff8#64)) ⋆ ExtHashMap.emp) dmem0
  rw [ExtHashMap.sep_emp, show 0x7ff8#64 - BitVec.ofNat 64 40 = 0x7fd0#64 from rfl]
  exact sep_ac (by ac_rfl) h2

/-- Running `f` from its label in the concrete host, for arguments `a`, `b`. -/
theorem run_f (a b : UInt64) (Q : Post) (X : XPost) (hs : fSpec [a.toBitVec, b.toBitVec] m0 Q X) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = raF ∧ ∃ rets m', Q rets m' ∧ target.RetsIn rets st.data ∧
          target.Restored (st0 a b) st.data ∧
          (st.data.dmem =⋆ Eq m' ⋆ target.Exit 0x7ff8#64 40 ⋆ ExtHashMap.emp)) ∨
        (∃ sym' as m', X sym' as m' ∧ target.Defined host sym' ∧ st.pc = Labels.label sym' ∧
          target.ArgsIn as st.data ∧ target.spEntry (st.data.regs.get64 .rsp) ∧
          ∃ (ra' : Int64) (n' : Nat) (F : Mem 64 → Prop), 8 ≤ n' ∧ True ∧
            (st.data.dmem =⋆ Eq m' ⋆ target.Entry (st.data.regs.get64 .rsp) ra' n' ⋆ F ⋆
              ExtHashMap.emp)))
      ⟨st0 a b, Host.addrOf 0⟩ := by
  have h := host_f_spec [a.toBitVec, b.toBitVec] m0 Q X hs (st0 a b) raF ExtHashMap.emp rfl
    trivial (show ((0x7ff8 : UInt64).toBitVec + 8#64).toNat % 16 = 0 by decide) dmem0_split
  rw [show Host.addrOf 0 = Labels.label "f" from
    (Host.label_eq_addrOf_of_unique host_unique (k := 0) rfl).symm]
  exact h

/-- Return branch: `f(1, 2)` returns `5` to `raF`, with `rsp` popped, the source memory intact and
the 48-byte stack footprint (contents arbitrary) handed back. -/
theorem f_returns :
    Eventually (step1 Host.exe)
      (fun st => st.pc = raF ∧ st.data.regs.get64 .rax = 5 ∧
        st.data.regs.get64 .rsp = 0x8000#64 ∧
        (st.data.dmem =⋆ Eq m0 ⋆ (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At 0x7fd0#64) ⋆
          ExtHashMap.emp))
      ⟨st0 1 2, Host.addrOf 0⟩ := by
  have hs : fSpec [(1 : UInt64).toBitVec, (2 : UInt64).toBitVec] m0
      (fun rets m' => rets = [5] ∧ m' = m0) (fun _ _ _ => False) :=
    ⟨1, 2, rfl, fun h => absurd (by decide) h, fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd (by decide) h⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (run_f 1 2 _ _ hs)
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨-, hsp⟩, hm⟩ | ⟨_, _, _, hF, _⟩)
  · refine ⟨hpc, ?_, ?_, hm⟩
    · simpa [Target.RetsIn, Target.ValsIn] using hrets
    · exact hsp
  · exact hF.elim

/-- What an exit to `abort(a)` yields, fed to `abort`'s `FnSpec`: the machine is at `abort` with `a`
in `rdi` and a return address `ra'` on the stack, and `abort` returns to `ra'` with the source
memory intact. -/
def AbortsWith (a : Val) (st : MachineState) : Prop :=
  st.pc = Labels.label "abort" ∧ st.data.regs.get64 .rdi = a ∧
  ∃ ra' : Int64, (st.data.dmem =⋆ Eq (ra'.toUInt64.At (st.data.regs.get64 .rsp)) ⋆ fun _ => True) ∧
    Eventually (step1 Host.exe) (fun st' => st'.pc = ra' ∧ (st'.data.dmem =⋆ Eq m0 ⋆ fun _ => True))
      st

theorem abortsWith_of_exit {a : Val} {st : MachineState} {sym' : String} {as : List Val}
    {m' : Mem 64} (hX : sym' = "abort" ∧ as = [a] ∧ m' = m0) (hpc : st.pc = Labels.label sym')
    (hargs : target.ArgsIn as st.data) (hspE : target.spEntry (st.data.regs.get64 .rsp))
    {ra' : Int64} {n' : Nat} {F : Mem 64 → Prop}
    (hm : st.data.dmem =⋆ Eq m' ⋆ target.Entry (st.data.regs.get64 .rsp) ra' n' ⋆ F ⋆
      ExtHashMap.emp) :
    AbortsWith a st := by
  obtain ⟨rfl, rfl, rfl⟩ := hX
  obtain ⟨d, pc⟩ := st
  change pc = _ at hpc
  subst hpc
  refine ⟨rfl, by simpa [Target.ArgsIn, Target.ValsIn] using hargs, ra', ?_, ?_⟩
  · have h' : (Eq m0 ⋆ (region (d.regs.get64 .rsp - BitVec.ofNat 64 n') n' ⋆
        Eq (ra'.toUInt64.At (d.regs.get64 .rsp))) ⋆ F ⋆ ExtHashMap.emp) d.dmem := hm
    have h'' : (Eq (ra'.toUInt64.At (d.regs.get64 .rsp)) ⋆ (Eq m0 ⋆
        region (d.regs.get64 .rsp - BitVec.ofNat 64 n') n' ⋆ F ⋆ ExtHashMap.emp)) d.dmem :=
      sep_ac (by ac_rfl) h'
    exact sep_mono_r (fun _ _ => trivial) h''
  · have h := host_abort_spec [a] m0 (fun rets m'' => rets = [] ∧ m'' = m0) (fun _ _ _ => False)
      ⟨a, rfl, rfl, rfl⟩ d ra' _ hargs trivial hspE (entry_zero hm)
    refine eventually_weaken _ _ _ _ ?_ h
    rintro st' (⟨hpc', rets, m'', ⟨-, rfl⟩, -, -, hm'⟩ | ⟨_, _, _, hF, _⟩)
    · refine ⟨hpc', ?_⟩
      rw [ExtHashMap.sep_assoc] at hm'
      exact sep_mono_r (fun _ _ => trivial) hm'
    · exact hF.elim

/-- Exit propagated through the callee: `f(0, 2)` calls `g(0)`, which exits to `abort(0)`. -/
theorem f_exits_in_g :
    Eventually (step1 Host.exe) (AbortsWith 0) ⟨st0 0 2, Host.addrOf 0⟩ := by
  have hs : fSpec [(0 : UInt64).toBitVec, (2 : UInt64).toBitVec] m0 (fun _ _ => False)
      (fun sym as m' => sym = "abort" ∧ as = [0] ∧ m' = m0) :=
    ⟨0, 2, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  refine eventually_weaken _ _ _ _ ?_ (run_f 0 2 _ _ hs)
  rintro st (⟨_, _, _, hF, _⟩ | ⟨sym', as, m', hX, -, hpc, hargs, hspE, ra', n', F, -, -, hm⟩)
  · exact hF.elim
  · exact abortsWith_of_exit hX hpc hargs hspE hm

/-- `f`'s own exit: `f(1, -3)` computes `fVal 1 (-3) = 0` and exits to `abort(1)`. -/
theorem f_exits_itself :
    Eventually (step1 Host.exe) (AbortsWith 1) ⟨st0 1 0xFFFFFFFFFFFFFFFD, Host.addrOf 0⟩ := by
  have hs : fSpec [(1 : UInt64).toBitVec, (0xFFFFFFFFFFFFFFFD : UInt64).toBitVec] m0
      (fun _ _ => False) (fun sym as m' => sym = "abort" ∧ as = [1] ∧ m' = m0) :=
    ⟨1, 0xFFFFFFFFFFFFFFFD#64, rfl, fun h => absurd (by decide) h,
      fun _ => ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (run_f 1 0xFFFFFFFFFFFFFFFD _ _ hs)
  rintro st (⟨_, _, _, hF, _⟩ | ⟨sym', as, m', hX, -, hpc, hargs, hspE, ra', n', F, -, -, hm⟩)
  · exact hF.elim
  · exact abortsWith_of_exit hX hpc hargs hspE hm

end Concrete

end Frames

end LeanQbe
