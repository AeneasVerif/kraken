module

public import LeanQbe.T.Arm64.IselLemmas3
public import LeanQbe.T.Arm64.IselNarrowLemmas

/-!
# AArch64 Wave 6.2-A Scratch-Constant, Memory & `mulHi` Proofs — Part 1

Verifies `ScrOk` preservation and `FallsTo` specifications for:
* `armMovImmScr`, `armArgInScr`, `armSetupAddrScr`, `armStoreValInScr`
* `armMulHi` (`armMulHi_spec`, `armMulHi_noLab`)
* `armLoadScr` / `armLoadZextIdxScr` (`armLoadScr_spec`, `armLoadZextIdxScr_spec`, `_noLab`)
* `armStoreScr` / `armStoreZextIdxScr` (`armStoreScr_spec`, `armStoreZextIdxScr_spec`, `_noLab`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `ScrOk` Framing and Scratch-Cache Materializers -/

private theorem reg_beq_self (a : Reg) : (a == a) = true := by
  cases a with
  | SP => rfl
  | reg x => cases x <;> rfl

private theorem reg_beq_eq {a b : Reg} (h : (a == b) = true) : a = b := by
  cases a with
  | SP => cases b <;> first | rfl | cases h
  | reg x => cases b with
    | SP => cases h
    | reg y => cases x <;> cases y <;> first | rfl | cases h

private theorem reg_not_contains_of_mem {r : Reg} {l : List Reg}
    (hm : r ∈ l) (hc : l.contains r = false) : False := by
  induction l with
  | nil => cases hm
  | cons x xs ih =>
    dsimp only [List.contains, List.elem_cons] at hc
    rcases List.mem_cons.mp hm with rfl | hmem
    · rw [reg_beq_self] at hc; cases hc
    · cases hrx : (r == x)
      · rw [hrx] at hc; exact ih hmem (by simpa using hc)
      · rw [hrx] at hc; simp at hc

theorem armHasScr_eq {scr : List (Reg × BitVec 64)} {tmp : XReg} {c64 : BitVec 64}
    {s : MachineData} (hscr : ScrOk armMach armScratch scr s)
    (hhas : armHasScr scr tmp c64 = true) :
    (s.regs.getXReg tmp).toBitVec = c64 := by
  dsimp only [armHasScr] at hhas
  rw [List.any_eq_true] at hhas
  rcases hhas with ⟨⟨r, v⟩, hmem, hp⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rcases hp with ⟨hr, rfl⟩
  have hrt := reg_beq_eq hr
  subst hrt
  exact (hscr (.reg tmp, v) hmem).2

theorem scrOk_killScr {scr : List (Reg × BitVec 64)} (gClob : List Reg) {s : MachineData}
    (hscr : ScrOk armMach armScratch scr s) :
    ScrOk armMach armScratch (armKillScr gClob scr) s := by
  intro p hp
  dsimp only [armKillScr] at hp
  rw [List.mem_filter] at hp
  exact hscr p hp.1

theorem scrOk_of_keeps {scr : List (Reg × BitVec 64)} {s s' : MachineData}
    (hscr : ScrOk armMach armScratch scr s)
    (hk : ∀ r ∈ armScratch, armMach.getGpr s' r = armMach.getGpr s r) :
    ScrOk armMach armScratch scr s' := by
  intro p hp
  have ⟨hs, hv⟩ := hscr p hp
  exact ⟨hs, (hk p.1 hs).trans hv⟩

theorem scrOk_kill_of_keeps {scr : List (Reg × BitVec 64)} {gClob : List Reg} {s s' : MachineData}
    (hscr : ScrOk armMach armScratch scr s)
    (hk : ∀ r ∈ armScratch, r ∉ gClob → armMach.getGpr s' r = armMach.getGpr s r) :
    ScrOk armMach armScratch (armKillScr gClob scr) s' := by
  intro p hp
  dsimp only [armKillScr] at hp
  rw [List.mem_filter] at hp
  have hnc : p.1 ∉ gClob := fun hm =>
    reg_not_contains_of_mem hm (Bool.eq_false_iff.mpr fun h => by simp [h] at hp)
  have ⟨hs, hv⟩ := hscr p hp.1
  exact ⟨hs, (hk p.1 hs hnc).trans hv⟩

theorem scrOk_wr {scr : List (Reg × BitVec 64)} {tmp : XReg} {c64 : BitVec 64} {s : MachineData}
    (hscr : ScrOk armMach armScratch scr s) (htmp : XRegOrSp.reg tmp ∈ armScratch) :
    ScrOk armMach armScratch (armSetScr scr tmp c64) (wr s tmp c64) := by
  intro p hp
  dsimp only [armSetScr] at hp
  rw [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ⟨htmp, get_wr_same s tmp c64⟩
  · exact scrOk_kill_of_keeps hscr
      (fun r _ hr => get_wr_of_ne s tmp c64 r fun e => hr (e ▸ by simp)) p hp

theorem scrOk_wr_kill {scr : List (Reg × BitVec 64)} {tmp : XReg} {v : BitVec 64}
    {s : MachineData} (hscr : ScrOk armMach armScratch scr s) :
    ScrOk armMach armScratch (armKillScr [.reg tmp] scr) (wr s tmp v) :=
  scrOk_kill_of_keeps hscr fun r _ hr => get_wr_of_ne s tmp v r fun e => hr (e ▸ by simp)

theorem scrOk_wr_nonScr {scr : List (Reg × BitVec 64)} {d : XReg} {v : BitVec 64}
    {s : MachineData} (hscr : ScrOk armMach armScratch scr s)
    (hd : XRegOrSp.reg d ∉ armScratch) :
    ScrOk armMach armScratch scr (wr s d v) :=
  scrOk_of_keeps hscr fun r hr => get_wr_of_ne s d v r fun e => hd (e ▸ hr)

theorem armMovImmScr_wp [Host] {scr : List (Reg × BitVec 64)} {tmp : XReg}
    (htmp : XRegOrSp.reg tmp ∈ armScratch) (c64 : BitVec 64) {s : MachineData}
    (hscr : ScrOk armMach armScratch scr s) :
    let (ci, scr') := armMovImmScr scr tmp c64
    _root_.Program.wp (emitClean ci) (fun s' =>
      (s'.regs.getXReg tmp).toBitVec = c64 ∧
      (∀ x, x ≠ tmp → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone ∧
      ScrOk armMach armScratch scr' s') (fun _ _ => False) s := by
  dsimp only [armMovImmScr]
  by_cases hhas : armHasScr scr tmp c64 = true
  · simp only [hhas, ↓reduceIte, emitClean_nil]
    exact armWp_nil ⟨armHasScr_eq hscr hhas, fun _ _ => rfl, rfl, rfl, rfl,
      Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone, hscr⟩
  · simp only [hhas, Bool.false_eq_true, ↓reduceIte]
    refine armWp_mono (armMovImm_wp tmp c64 s) ?_
    rintro s' rfl
    refine ⟨by simp, fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
      by simp, rfl, rfl, frame_wr tmp c64 List.mem_cons_self maskNone, scrOk_wr hscr htmp⟩

theorem armArgInScr_wp [Host] {n : Nat} (hn : n ≤ 64) {scr : List (Reg × BitVec 64)} {tmp : XReg}
    (htmp : XRegOrSp.reg tmp ∈ armScratch) {pa : PArg Reg Empty ArmCond (.bits n)}
    {v : BitVec n} {s : MachineData} {ca : List Instr} {ra : XReg} {scr' : List (Reg × BitVec 64)}
    (ha : armArgInScr scr tmp pa = some (ca, ra, scr'))
    (hp : armMach.PArgHolds s (.bits n) pa v)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean ca) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth n = v ∧
      (∀ x, x ≠ tmp → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone ∧
      ScrOk armMach armScratch scr' s') (fun _ _ => False) s := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr r =>
    cases r with
    | SP => simp [armArgInScr] at ha
    | reg x =>
      simp only [armArgInScr, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl, rfl⟩
      refine armWp_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl,
        Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone, hscr⟩
      simpa [Machine.PArgHolds, GprHolds, armMach, get_reg] using hp.2
  | imm c =>
    simp only [armArgInScr, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp; subst hp
    refine armWp_mono (armMovImmScr_wp htmp (c.setWidth 64) hscr) ?_
    rintro s' ⟨hr, hx, hsp, hdm, hst, hfr, hscr'⟩
    refine ⟨?_, hx, hsp, hdm, hst, hfr, hscr'⟩
    rw [hr, BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]

theorem armArgs2Scr_wp [Host] {n₁ n₂ : Nat} (hn₁ : n₁ ≤ 64) (hn₂ : n₂ ≤ 64)
    {scr : List (Reg × BitVec 64)}
    {pa : PArg Reg Empty ArmCond (.bits n₁)} {pb : PArg Reg Empty ArmCond (.bits n₂)}
    {va : BitVec n₁} {vb : BitVec n₂} {s : MachineData}
    {ca cb : List Instr} {ra rb : XReg} {scr₁ scr₂ : List (Reg × BitVec 64)}
    (ha : armArgInScr scr .X16 pa = some (ca, ra, scr₁))
    (hb : armArgInScr scr₁ .X17 pb = some (cb, rb, scr₂))
    (hpa : armMach.PArgHolds s (.bits n₁) pa va) (hpb : armMach.PArgHolds s (.bits n₂) pb vb)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean (ca ++ cb)) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth n₁ = va ∧
      (s'.regs.getXReg rb).toBitVec.setWidth n₂ = vb ∧
      ra ≠ .X17 ∧ rb ≠ .X16 ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' armScratch [] maskNone ∧
      ScrOk armMach armScratch scr₂ s') (fun _ _ => False) s := by
  have hneA : ra ≠ .X17 := by
    cases pa with
    | vec vr => exact vr.elim
    | imm _ => simp [armArgInScr] at ha; rcases ha with ⟨rfl, rfl, rfl⟩; decide
    | gpr r => cases r with
      | SP => simp [armArgInScr] at ha
      | reg x =>
        simp [armArgInScr] at ha; rcases ha with ⟨rfl, rfl, rfl⟩
        exact (xreg_ne_scratch_of_not_mem (hga (.reg x) (by simp [PArg.gprs]))).2
  have hneB : rb ≠ .X16 := by
    cases pb with
    | vec vr => exact vr.elim
    | imm _ => simp [armArgInScr] at hb; rcases hb with ⟨rfl, rfl, rfl⟩; decide
    | gpr r => cases r with
      | SP => simp [armArgInScr] at hb
      | reg x =>
        simp [armArgInScr] at hb; rcases hb with ⟨rfl, rfl, rfl⟩
        exact (xreg_ne_scratch_of_not_mem (hgb (.reg x) (by simp [PArg.gprs]))).1
  rw [emitClean_append]
  refine armWp_append (armArgInScr_wp hn₁ x16_mem_scratch ha hpa hscr) ?_
  rintro s₁ ⟨hra₁, _, _, hdmem₁, hst₁, hfr₁, hscr₁⟩
  have hpb₁ : armMach.PArgHolds s₁ (.bits n₂) pb vb :=
    Machine.PArgHolds.frame hfr₁ hpb (fun r hr => by
      subst hr; have hg := hgb r (by simp [PArg.gprs])
      cases r with | SP => intro h; simp at h | reg x => simp [armScratch] at hg ⊢; exact hg.1)
      (fun v => v.elim) (fun _ ht => nomatch ht)
  refine armWp_mono (armArgInScr_wp hn₂ x17_mem_scratch hb hpb₁ hscr₁) ?_
  rintro s₂ ⟨hrb₂, hx₂, _, hdmem₂, hst₂, hfr₂, hscr₂⟩
  have hra₂ : (s₂.regs.getXReg ra).toBitVec.setWidth n₁ = va := by
    have hx := hx₂ ra hneA
    simpa [hx] using hra₁
  exact ⟨hra₂, hrb₂, hneA, hneB, hdmem₂.trans hdmem₁, hst₂.trans hst₁,
    armFrame_scratch2 hfr₁ hfr₂, hscr₂⟩

private theorem armSetupAddrScr_wp [Host] (scr : List (Reg × BitVec 64)) (scale : Nat)
    (a : AddrArg Reg) (s : MachineData) (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hva : armAddrValid scale a = true) (hscr : ScrOk armMach armScratch scr s) :
    let (setup, addr, scr') := armSetupAddrScr scr scale a
    (∃ rx, addr.base = .low (.reg rx) .W64) ∧
    _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (a.eval (get s), s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone ∧
      ScrOk armMach armScratch scr' s') (fun _ _ => False) s := by
  have armAtReg_ev : ∀ [Labels] (sx : MachineData) (rb : XReg) (p : Std.Rco Int64),
      (atReg rb).eval sx p = ((sx.regs.getXReg rb).toBitVec, sx) := fun sx rb p => by
    simp [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp_reg64, BitVec.signed,
      BitVec.ofInt_toInt]
  have armAtIdx_ev : ∀ [Labels] (sx : MachineData) (rb idx : XReg) (p : Std.Rco Int64),
      (armAtIdx rb idx).eval sx p =
        ((sx.regs.getXReg rb).toBitVec + (sx.regs.getXReg idx).toBitVec, sx) :=
    fun sx rb idx p => by
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.signed, BitVec.unsigned]
    congr 1
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have armAtDisp_ev : ∀ [Labels] (sx : MachineData) (rb : XReg) (disp : Int64) (p : Std.Rco Int64),
      (armAtDisp rb disp).eval sx p = ((sx.regs.getXReg rb).toBitVec + disp.toBitVec, sx) :=
    fun sx rb disp p => by
      simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp_reg64, BitVec.signed,
        BitVec.ofInt_add]
      rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  cases a with
  | imm addr =>
    dsimp only [armSetupAddrScr]
    refine ⟨⟨.X16, rfl⟩, armWp_mono (armMovImmScr_wp x16_mem_scratch addr hscr) ?_⟩
    rintro s' ⟨h16, hx, hsp, hdm, hst, hfr, hscr'⟩
    exact ⟨by intro _ p; rw [armAtReg_ev, h16, AddrArg.eval], hx, hsp, hdm, hst, hfr, hscr'⟩
  | baseDisp base disp =>
    cases base with
    | reg rb =>
      have hrb16 : rb ≠ .X16 :=
        fun h => haregs (.reg rb) (by simp [AddrArg.regs]) (by simp [h, armScratch])
      dsimp only [armSetupAddrScr]
      split
      · rename_i h0
        have hd : disp.toBitVec = 0#64 := by have := beq_iff_eq.mp h0; subst this; rfl
        refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
          intro _ p; rw [armAtReg_ev, AddrArg.eval, hd, BitVec.add_zero, get_reg],
          fun _ _ => rfl, rfl, rfl, rfl,
          Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone, hscr⟩⟩
      · split
        · refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
            intro _ p; rw [armAtDisp_ev, AddrArg.eval, get_reg],
            fun _ _ => rfl, rfl, rfl, rfl,
            Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone, hscr⟩⟩
        · refine ⟨⟨rb, rfl⟩, armWp_mono (armMovImmScr_wp x16_mem_scratch disp.toBitVec hscr) ?_⟩
          rintro s' ⟨h16, hx, hsp, hdm, hst, hfr, hscr'⟩
          exact ⟨by intro _ p; rw [armAtIdx_ev, AddrArg.eval, get_reg, hx rb hrb16, h16],
            hx, hsp, hdm, hst, hfr, hscr'⟩
    | SP =>
      dsimp only [armSetupAddrScr]
      have hne : (armSetupAddrIns scale (.baseDisp .SP disp)).1.isEmpty = false := by
        dsimp only [armSetupAddrIns]
        split
        · rfl
        · split
          · rfl
          · simp
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hbase := armSetupAddr_wp scale (.baseDisp .SP disp) s haregs hva
      dsimp only at hbase
      refine ⟨hbase.1, armWp_mono hbase.2 ?_⟩
      rintro s' ⟨hev, hx, hsp, hdm, hst, hfr⟩
      refine ⟨hev, hx, hsp, hdm, hst, hfr, scrOk_kill_of_keeps hscr fun r _ hr => ?_⟩
      cases r with
      | SP => simp [get_sp, hsp]
      | reg x =>
        have hx16 : x ≠ .X16 := fun h => hr (h ▸ by simp)
        simpa [get_reg] using congrArg UInt64.toBitVec (hx x hx16)
  | baseIdxDisp base idx sc disp =>
    cases base with
    | SP => simp [armAddrValid] at hva
    | reg rb =>
      cases idx with
      | SP => simp [armAddrValid] at hva
      | reg ri =>
        have hri16 : ri ≠ .X16 :=
          fun h => haregs (.reg ri) (by simp [AddrArg.regs]) (by simp [h, armScratch])
        dsimp only [armAddrValid] at hva
        dsimp only [armSetupAddrScr, armSetupAddrIns]
        by_cases hdisp0 : disp == 0
        · cases hamt : armMemExtendAmount scale sc with
          | none =>
            dsimp only [armAddrIdxValid] at hva
            rw [beq_iff_eq] at hdisp0; subst hdisp0; simp [hamt] at hva
          | some amt =>
            have heq : armSetupIdxDispIns false scale rb ri sc disp =
                ([], armAtIdxExtScale false rb ri amt) := by
              simp [armSetupIdxDispIns, hdisp0, hamt]
            simp only [heq, List.isEmpty_nil, ↓reduceIte]
            have hd0 : disp.toBitVec = 0#64 := by have := beq_iff_eq.mp hdisp0; subst this; rfl
            refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
                intro _ p; rw [armAtIdxExtScale_eval false s rb ri hamt p]
                simp [AddrArg.eval, hd0, get_reg],
              fun _ _ => rfl, rfl, rfl, rfl,
              Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone, hscr⟩⟩
        · have hsub := armSetupIdxDisp_wp false scale rb ri sc disp s hri16 hva
          rcases hsub with ⟨hnoSp, hwp⟩
          have hne : (armSetupIdxDispIns false scale rb ri sc disp).1.isEmpty = false := by
            dsimp only [armSetupIdxDispIns]
            simp only [hdisp0, Bool.false_eq_true, ↓reduceIte]
            split
            · rfl
            · dsimp only [armAddrIdxValid] at hva
              simp only [hdisp0, Bool.false_or] at hva
              have hboth : (armMemExtendAmount scale sc).isSome = true ∧
                  ((armImm12? disp.toBitVec).isSome = true ∨
                    (armImm12? (-disp.toBitVec)).isSome = true) := by
                rename_i hfit
                simpa [bne, hdisp0, hfit, Bool.and_eq_true, Bool.or_eq_true] using hva
              obtain ⟨amt, hamt⟩ := Option.isSome_iff_exists.mp hboth.1
              have hadd : ∃ addIns,
                  armAddSubImmI? false .W64 .X16 rb disp.toBitVec = some addIns := by
                dsimp only [armAddSubImmI?]
                rcases hboth.2 with h1 | h2
                · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h1; simp [hei]
                · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h2
                  cases h1 : armImm12? disp.toBitVec <;> simp [hei]
              obtain ⟨addIns, hadd⟩ := hadd
              simp [hamt, hadd]
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          refine ⟨hnoSp, armWp_mono hwp ?_⟩
          rintro s' ⟨hev, hx, hsp, hdm, hst, hfr⟩
          refine ⟨by
              intro _ p; dsimp only [armSetupIdxDispIns]; rw [hev p]; simp [AddrArg.eval, get_reg],
            hx, hsp, hdm, hst, hfr, scrOk_kill_of_keeps hscr fun r _ hr => ?_⟩
          cases r with
          | SP => simp [get_sp, hsp]
          | reg x =>
            have hx16 : x ≠ .X16 := fun h => hr (h ▸ by simp)
            simpa [get_reg] using congrArg UInt64.toBitVec (hx x hx16)

private theorem armStoreValInScr_wp [Host] {scr : List (Reg × BitVec 64)} {t : Ty}
    {pa : PArg Reg Empty ArmCond t} {v : Val t} {s : MachineData}
    {valSetup : List Instr} {rx : XRegOrXzr} {scr' : List (Reg × BitVec 64)}
    (hpa : armStoreValInScr scr t pa = some (valSetup, rx, scr'))
    (hp : armMach.PArgHolds s t pa v)
    (hregs : ∀ r ∈ pa.gprs, r ∉ armScratch)
    (ht : t = .bool ∨ t = .bits 8 ∨ t = .bits 16 ∨ t = .bits 32 ∨ t = .bits 64)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean valSetup) (fun s' =>
      rx ≠ .reg .X16 ∧
      (∃ w64 : BitVec 64, s'.regs.getRegOrZr (.low rx .W64) = w64 ∧ GprHolds w64 t v) ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      (∀ x, x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.regs.SP = s.regs.SP ∧
      ScrOk armMach armScratch scr' s')
      (fun _ _ => False) s := by
  have ht' : t = .bool ∨ ∃ n, n ≤ 64 ∧ t = .bits n := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    all_goals exact Or.inr ⟨_, by decide, rfl⟩
  cases pa with
  | vec vr => exact vr.elim
  | flag cond =>
    simp only [armStoreValInScr, Option.some.injEq, Prod.mk.injEq] at hpa
    rcases hpa with ⟨rfl, rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armCset64_wp .X17 cond s) ?_
    rintro s' rfl
    refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
      fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, scrOk_wr_kill hscr⟩
    rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, hp]
    cases v <;> rfl
  | gpr r =>
    have hcases : (∃ x, r = .reg x ∧ valSetup = [] ∧ rx = .reg x ∧ scr' = scr) ∨
        (r = .SP ∧ valSetup = [armIselMovToXI .X17 .SP] ∧ rx = .reg .X17 ∧
          scr' = armKillScr [.reg .X17] scr) := by
      cases r with
      | reg x =>
        rcases ht' with rfl | ⟨n, _, rfl⟩ <;>
          · simp only [armStoreValInScr, Option.some.injEq, Prod.mk.injEq] at hpa
            exact Or.inl ⟨x, rfl, hpa.1.symm, hpa.2.1.symm, hpa.2.2.symm⟩
      | SP =>
        rcases ht' with rfl | ⟨n, _, rfl⟩ <;>
          · simp only [armStoreValInScr, Option.some.injEq, Prod.mk.injEq] at hpa
            exact Or.inr ⟨rfl, hpa.1.symm, hpa.2.1.symm, hpa.2.2.symm⟩
    rcases hcases with ⟨x, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hx16 : XRegOrXzr.reg x ≠ .reg .X16 := fun h =>
        (xreg_ne_scratch_of_not_mem (hregs (.reg x) (by simp [PArg.gprs]))).1
          (by cases h; rfl)
      refine armWp_nil ⟨hx16, ⟨_, rfl, ?_⟩, rfl, rfl, fun _ _ => rfl, rfl, hscr⟩
      rw [getRegOrZr_low64_reg]; exact hp
    · simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armMovToX_wp .X17 .SP s) ?_
      rintro s' rfl
      refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
        fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, scrOk_wr_kill hscr⟩
      rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]
      simpa [Machine.PArgHolds, armMach, get_sp] using hp
  | imm c =>
    rcases ht' with rfl | ⟨n, hn64, rfl⟩
    · cases c
      · simp only [armStoreValInScr, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_nil ⟨by decide, ⟨0#64, by rfl, by rfl⟩, rfl, rfl, fun _ _ => rfl, rfl, hscr⟩
      · simp only [armStoreValInScr, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_mono (armMovImmScr_wp x17_mem_scratch 1#64 hscr) ?_
        rintro s' ⟨h17, hx, hsp, hdm, hst, _, hscr'⟩
        refine ⟨by decide, ⟨_, rfl, ?_⟩, hdm, hst, hx, hsp, hscr'⟩
        rw [getRegOrZr_low64_reg, h17]; rfl
    · simp only [armStoreValInScr] at hpa
      split at hpa
      · rename_i hc0
        simp only [Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        have hc0' : c = 0#n := beq_iff_eq.mp hc0
        refine armWp_nil ⟨by decide, ⟨0#64, by rfl, hn64, ?_⟩, rfl, rfl,
          fun _ _ => rfl, rfl, hscr⟩
        rw [BitVec.setWidth_zero, hc0']
      · simp only [Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_mono (armMovImmScr_wp x17_mem_scratch (c.setWidth 64) hscr) ?_
        rintro s' ⟨h17, hx, hsp, hdm, hst, _, hscr'⟩
        refine ⟨by decide, ⟨_, rfl, hn64, ?_⟩, hdm, hst, hx, hsp, hscr'⟩
        rw [getRegOrZr_low64_reg, h17, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]

/-! ## 2. `armMulHi_spec`, `armLoadScr_spec`, `armLoadZextIdxScr_spec`, `armStoreScr_spec`,
`armStoreZextIdxScr_spec` -/

private theorem mul_lt_pow64' (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 := by
  have ha := a.isLt; have hb := b.isLt
  calc a.toNat * b.toNat ≤ 2 ^ 32 * b.toNat := Nat.mul_le_mul_right _ (Nat.le_of_lt ha)
    _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_left (by decide) |>.mpr hb
    _ = 2 ^ 64 := by decide

private theorem umulw32_hi' (a b : BitVec 32) :
    ((BitVec.ofInt 64 (a.unsigned * b.unsigned + (0#64).signed)) >>> 32).setWidth 32 =
      BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := mul_lt_pow64' a b
  have hdiv : a.toNat * b.toNat / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul hlt
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero, BitVec.unsigned, BitVec.unsigned, ← Int.natCast_mul,
    BitVec.ofInt_natCast]
  simp [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv]

private theorem smulw32_hi' (a b : BitVec 32) :
    ((BitVec.ofInt 64 (a.signed * b.signed + (0#64).signed)) >>> 32).setWidth 32 =
      (BitVec.ofInt (32 + 32) (a.toInt * b.toInt)).extractLsb' 32 32 := by
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, BitVec.signed, Nat.add_comm 32 i]

private theorem umulw64_hi' (a b : BitVec 64) :
    (BitVec.ofInt 128 (a.unsigned * b.unsigned)).extractLsb' 64 64 =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.unsigned, BitVec.unsigned, ← Int.natCast_mul, BitVec.ofInt_natCast]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, hi, show 64 + i < 128 by omega,
    decide_true, Bool.true_and]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem armMulHi_spec {h : Host} {k : Nat} {isSigned : Bool} {n : Nat}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {rd : Reg} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armMulHi isSigned n pa pb rd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch) (hrd : rd ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' =>
        let hi : BitVec n :=
          if isSigned then (BitVec.ofInt (n + n) (va.toInt * vb.toInt)).extractLsb' n n
          else BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n)
        GprHolds (armMach.getGpr s' rd) (.bits n) hi ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armMulHiIns] at hc
  split at hc
  · cases hc
  · rename_i hok
    have hn' : n = 32 ∨ n = 64 := by cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> simp_all
    have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
    cases rd with
    | SP => simp at hc
    | reg dhi =>
      simp only [Option.bind_some, bind, Option.bind_eq_some_iff] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, hc2⟩
      dsimp only at hc2
      rcases hc2 with ⟨⟨cb, rb⟩, hb, htail⟩
      dsimp only at htail
      have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_left _ hr)
      have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_right _ hr)
      rcases hn' with rfl | rfl
      · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at htail
        rcases htail with ⟨rfl, rfl⟩
        simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
        refine armFallsTo_of_wp (armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_)
        rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
        simp only [emitClean_cons, emitClean_nil]
        have hmul64 : _root_.Program.wp [Kraken.Directive.instr (if isSigned then
              armIselInsI (.SMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
              else armIselInsI (.UMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))]
            (fun s' => s' = wr s₂ .X16 (BitVec.ofInt 64
              (if isSigned then va.signed * vb.signed + (0#64).signed
               else va.unsigned * vb.unsigned + (0#64).signed)))
            (fun _ _ => False) s₂ := by
          cases isSigned
          · exact armDirFallsTo_wp
              (d := ins (.UMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))
              fun {_} p next jmp Q hk => by
                simp only [t_step_simp, hra, hrb, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
          · exact armDirFallsTo_wp
              (d := ins (.SMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))
              fun {_} p next jmp Q hk => by
                simp only [t_step_simp, hra, hrb, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
        refine armWp_cons hmul64 fun s₃ hs₃ => ?_
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' =>
            s' = wr s₃ dhi (((s₃.regs.getXReg .X16).toBitVec >>> 32).setWidth 64))
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp]; rw [evalUBFM_32_63]
            simp only [BitVec.setWidth_eq]; exact hk _ rfl)
          fun s₄ hs₄ => ?_
        subst hs₄ hs₃
        refine ⟨⟨⟨hn64, ?_⟩, hd₂⟩, armFrame_status_eq (fun r hr => ?_) hst₂⟩
        · simp only [get_wr_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
          cases isSigned <;> (first | exact umulw32_hi' va vb | exact smulw32_hi' va vb)
        · have hr' : r ≠ .reg dhi ∧ r ≠ .reg .X16 ∧ r ∉ armScratch := by
            have := ne_of_not_mem_armScratch (fun h => hr (List.mem_cons_of_mem _ h))
            exact ⟨fun e => hr (e ▸ List.mem_cons_self), this.1,
              fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          rw [get_wr_of_ne _ dhi _ r hr'.1, get_wr_of_ne s₂ .X16 _ r hr'.2.1]
          exact hfr₂.1 r hr'.2.2
      · simp only [show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at htail
        rcases htail with ⟨rfl, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armFallsTo_of_wp (armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_)
        rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
        simp only [BitVec.setWidth_eq] at hra hrb
        have hmulH : _root_.Program.wp [Kraken.Directive.instr (if isSigned then
              armIselInsI (.SMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64))
              else armIselInsI (.UMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64)))]
            (fun s' => s' = wr s₂ dhi
              (if isSigned then (BitVec.ofInt 128 (va.signed * vb.signed)).extractLsb' 64 64
               else BitVec.ofNat 64 (va.toNat * vb.toNat / 2 ^ 64)))
            (fun _ _ => False) s₂ := by
          cases isSigned
          · exact armDirFallsTo_wp (d := ins (.UMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64)))
              fun {_} p next jmp Q hk => by
                simp only [t_step_simp, BitVec.setWidth_eq, RegWidth.bits, MemWidth.bits, hra, hrb]
                rw [show (64 + 64 : Nat) = 128 from rfl, umulw64_hi']; exact hk _ rfl
          · exact armDirFallsTo_wp (d := ins (.SMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64)))
              fun {_} p next jmp Q hk => by
                simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hra, hrb]; exact hk _ rfl
        refine armWp_mono hmulH fun s₃ hs₃ => ?_
        subst hs₃
        refine ⟨⟨⟨hn64, ?_⟩, hd₂⟩, armFrame_status_eq (fun r hr => ?_) hst₂⟩
        · cases isSigned <;> simp [get_wr_same, BitVec.signed]
        · have hr' : r ≠ .reg dhi ∧ r ∉ armScratch :=
            ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          rw [get_wr_of_ne s₂ dhi _ r hr'.1]; exact hfr₂.1 r hr'.2

theorem armMulHi_noLab {isSigned : Bool} {n : Nat} {pa pb : PArg Reg Empty ArmCond (.bits n)}
    {rd : Reg} {c : List Directive} {clob : FlagMask}
    (hc : armMulHi isSigned n pa pb rd = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

private theorem armLoadTailScr_wp {h : Host} {k : Nat} {scr1 scrOut : List (Reg × BitVec 64)}
    {t : Ty} {rd : Reg} {setup : List Instr} {addr : AddrExpr} {effAddr : BitVec 64}
    {ci : List Instr} {clob : FlagMask} {v : Val t} {s : MachineData} {post : MachineState → Prop}
    (hc : armLoadTailIns t rd setup addr = some (ci, clob))
    (hscrOut : scrOut = match rd with | .reg _ => scr1 | .SP => armKillScr [.reg .X16] scr1)
    (hrd : rd ∉ armScratch)
    (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (hwpSetup : _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (effAddr, s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone ∧
      ScrOk armMach armScratch scr1 s') (fun _ _ => False) s)
    (hv : loadVal (armMach.mem s) t effAddr = some v) :
    armMach.FallsTo armCondReads h k (emitClean ci) (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) t v ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  subst hscrOut
  cases rd with
  | reg d =>
    simp only [armLoadTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_)
    rintro s₁ ⟨heval, _, _, hdmem₁, hst₁, hfr₁, hscr₁⟩
    refine armWp_mono (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    have hdScr : XRegOrSp.reg d ∉ armScratch := hrd
    refine ⟨⟨by simpa [armMach, get_wr_same] using hw64, hdmem₁,
      scrOk_wr_nonScr hscr₁ hdScr⟩, armFrame_status_eq ?_ hst₁⟩
    intro r hr
    have hnd : r ≠ .reg d := fun e => hr (e ▸ List.mem_cons_self)
    rw [get_wr_of_ne s₁ d w64 r hnd]
    exact hfr₁.1 r fun h16 => hr (by simp at h16; subst h16; simp [armScratch])
  | SP =>
    simp only [armLoadTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_)
    rintro s₁ ⟨heval, hx₁, _, hdmem₁, hst₁, _, hscr₁⟩
    refine armWp_cons (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    refine armWp_mono (armMovToSp_wp .X16 (wr s₁ .X16 w64)) ?_
    rintro s₃ rfl
    have hkill : ScrOk armMach armScratch (armKillScr [.reg .X16] scr1)
        { regs := { (wr s₁ .X16 w64).regs with
            SP := UInt64.ofBitVec (get (wr s₁ .X16 w64) (.reg .X16)) },
          status := (wr s₁ .X16 w64).status,
          dmem := (wr s₁ .X16 w64).dmem } := by
      refine scrOk_kill_of_keeps hscr₁ fun r hr hne16 => ?_
      cases r with
      | SP => exact absurd (show XRegOrSp.SP ∈ armScratch from hr) (by simp [armScratch])
      | reg xr =>
        have hx16 : xr ≠ .X16 := fun e => hne16 (e ▸ by simp)
        change (({ (wr s₁ .X16 w64).regs with SP := _ } : Reg64s).getXReg xr).toBitVec =
          (s₁.regs.getXReg xr).toBitVec
        have hgetSp : ∀ (regs : Reg64s) (v : UInt64) (x : XReg),
            ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
          intro regs v x; cases x <;> rfl
        rw [hgetSp, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
    refine ⟨⟨by simpa [armMach, get_sp, get_wr_same] using hw64, hdmem₁, hkill⟩,
      armFrame_status_eq ?_ hst₁⟩
    intro r hr
    simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx16 : xr ≠ .X16 := fun e => hr.2.1 (congrArg XRegOrSp.reg e)
      have : ∀ (regs : Reg64s) (v : UInt64) (x : XReg),
          ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
        intro regs v x; cases x <;> rfl
      simp only [get_reg, this, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
      exact congrArg UInt64.toBitVec (hx₁ xr hx16)

theorem armLoadScr_spec {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {t : Ty} {rd : Reg} {a : AddrArg Reg} {c : List Directive} {clob : FlagMask}
    {scrOut : List (Reg × BitVec 64)} {v : Val t} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoadScr scr t rd a = some (c, clob, scrOut))
    (hrd : rd ∉ armScratch) (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hv : loadVal (armMach.mem s) t (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) t v ∧
        (armGpr.zeroUpper32Load = true → ∀ (ht : t = .bits 32),
          armMach.getGpr s' rd = (ht ▸ v).setWidth 64) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  dsimp only [armLoadScr] at hc_in
  rw [Option.map_eq_some_iff] at hc_in
  rcases hc_in with ⟨⟨ci, clob', scrOut'⟩, hc, hceq⟩
  cases hceq
  dsimp only [armLoadScrIns] at hc
  match hsc : armMemScale t with
  | none => simp [hsc] at hc
  | some scale =>
    simp only [hsc, bind, Option.bind_some] at hc
    have hva : armAddrValid scale a = true := by
      cases h' : armAddrValid scale a
      · simp [h'] at hc
      · rfl
    rw [show (!armAddrValid scale a) = false by simp [hva]] at hc
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    have hsetup := armSetupAddrScr_wp scr scale a s haregs hva hscr
    generalize armSetupAddrScr scr scale a = sa at hc hsetup
    rcases sa with ⟨setup, addr, scr1⟩
    rcases hsetup with ⟨hnoSp, hwpSetup⟩
    cases rd <;> dsimp only at hc <;>
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc <;>
      rcases hc with ⟨⟨ci', cl'⟩, htail, rfl, rfl, rfl⟩ <;>
      · letI := h
        refine (armLoadTailScr_wp htail rfl hrd hnoSp hwpSetup hv).conseq ?_
        intro s' ⟨habi, hdm, hscr'⟩ _
        exact ⟨habi, fun _ ht => by subst ht; exact habi.2, hdm, hscr'⟩

theorem armLoadZextIdxScr_spec {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {t : Ty} {rd base idx : Reg} {sc : AddrScale} {disp : Int64}
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {v : Val t} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoadZextIdxScr scr t rd base idx sc disp = some (c, clob, scrOut))
    (hrd : rd ∉ armScratch) (_ : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) =
      some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) t v ∧
        (armGpr.zeroUpper32Load = true → ∀ (ht : t = .bits 32),
          armMach.getGpr s' rd = (ht ▸ v).setWidth 64) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  dsimp only [armLoadZextIdxScr] at hc_in
  rw [Option.map_eq_some_iff] at hc_in
  rcases hc_in with ⟨⟨ci, clob', scrOut'⟩, hc, hceq⟩
  cases hceq
  cases hsc : armMemScale t with
  | none => simp [armLoadZextIdxScrIns, hsc] at hc
  | some scale =>
    simp only [armLoadZextIdxScrIns, hsc, Option.bind_some, bind, Option.bind_eq_some_iff] at hc
    rcases hc with ⟨⟨setup, addr⟩, hsa, hc2⟩
    dsimp only at hc2
    rcases hc2 with ⟨⟨ci', cl'⟩, htail, hsome⟩
    dsimp only at hsome
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    rcases hsome with ⟨rfl, rfl, hscr_eq⟩
    letI := h
    have hwpScr : ∃ (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64),
        _root_.Program.wp (emitClean setup) (fun s' =>
          (∀ [Labels] p, addr.eval s' p =
            (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec, s')) ∧
          (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
          s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
          armMach.Frame armCondReads s s' [.reg .X16] [] maskNone ∧
          ScrOk armMach armScratch
            (if setup.isEmpty then scr else armKillScr [.reg .X16] scr) s')
          (fun _ _ => False) s := by
      by_cases hem : setup.isEmpty
      · have hsetup0 : setup = [] := by cases setup with | nil => rfl | cons _ _ => simp at hem
        subst hsetup0
        cases base with
        | SP => simp [armSetupAddrZextIns] at hsa
        | reg rb => cases idx with
          | SP => simp [armSetupAddrZextIns] at hsa
          | reg ri =>
            dsimp only [armSetupAddrZextIns] at hsa
            split at hsa
            · rename_i hva
              simp only [Option.some.injEq] at hsa
              by_cases hdisp0 : disp == 0
              · cases hamt : armMemExtendAmount scale sc with
                | none =>
                  dsimp only [armAddrIdxValid] at hva
                  rw [beq_iff_eq] at hdisp0; subst hdisp0; simp [hamt] at hva
                | some amt =>
                  have heq : armSetupIdxDispIns true scale rb ri sc disp =
                      ([], armAtIdxExtScale true rb ri amt) := by
                    simp [armSetupIdxDispIns, hdisp0, hamt]
                  rw [heq] at hsa
                  injection hsa with _ ha_eq; subst ha_eq
                  have hd0 : disp.toBitVec = 0#64 := by
                    have := beq_iff_eq.mp hdisp0; subst this; rfl
                  have hrb : (s.regs.getXReg rb).toBitVec = vb := by
                    simpa [GprHolds, armMach, get_reg] using hvb.2
                  have hri : (s.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
                    simpa [GprHolds, armMach, get_reg] using hvi.2
                  refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
                      intro _ p; rw [armAtIdxExtScale_eval true s rb ri hamt p]
                      simp [hrb, hri, hd0],
                    fun _ _ => rfl, rfl, rfl, rfl,
                    Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone,
                    by simpa using hscr⟩⟩
              · exfalso
                dsimp only [armSetupIdxDispIns] at hsa
                simp only [hdisp0, Bool.false_eq_true, ↓reduceIte] at hsa
                split at hsa
                · simp at hsa
                · dsimp only [armAddrIdxValid] at hva
                  simp only [hdisp0, Bool.false_or] at hva
                  have hboth : (armMemExtendAmount scale sc).isSome = true ∧
                      ((armImm12? disp.toBitVec).isSome = true ∨
                        (armImm12? (-disp.toBitVec)).isSome = true) := by
                    rename_i hfit
                    simpa [bne, hdisp0, hfit, Bool.and_eq_true, Bool.or_eq_true] using hva
                  obtain ⟨amt, hamt⟩ := Option.isSome_iff_exists.mp hboth.1
                  have hadd : ∃ addIns,
                      armAddSubImmI? false .W64 .X16 rb disp.toBitVec = some addIns := by
                    dsimp only [armAddSubImmI?]
                    rcases hboth.2 with h1 | h2
                    · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h1; simp [hei]
                    · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h2
                      cases h1 : armImm12? disp.toBitVec <;> simp [hei]
                  obtain ⟨addIns, hadd⟩ := hadd
                  simp [hamt, hadd] at hsa
            · simp at hsa
      · obtain ⟨rb, ri, rfl, rfl, hnoSp, hwpSetup⟩ :=
          armSetupAddrZext_wp scale base idx sc disp s hidx hsa
        have hrb : (s.regs.getXReg rb).toBitVec = vb := by
          simpa [GprHolds, armMach, get_reg] using hvb.2
        have hri : (s.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
          simpa [GprHolds, armMach, get_reg] using hvi.2
        rw [hrb, hri] at hwpSetup
        refine ⟨hnoSp, ?_⟩
        simp only [hem, Bool.false_eq_true, ↓reduceIte]
        refine armWp_mono hwpSetup ?_
        rintro s' ⟨hev, hx, hsp, hdm, hst, hfr⟩
        refine ⟨hev, hx, hsp, hdm, hst, hfr, scrOk_kill_of_keeps hscr fun r _ hr => ?_⟩
        cases r with
        | SP => simp [get_sp, hsp]
        | reg x =>
          have hx16 : x ≠ .X16 := fun h => hr (h ▸ by simp)
          simpa [get_reg] using congrArg UInt64.toBitVec (hx x hx16)
    rcases hwpScr with ⟨hnoSp, hwpScr⟩
    cases rd <;> dsimp only at hscr_eq <;> cases hscr_eq <;>
      · refine (armLoadTailScr_wp htail rfl hrd hnoSp hwpScr hv).conseq ?_
        intro s' ⟨habi, hdm, hscr'⟩ _
        exact ⟨habi, fun _ ht => by subst ht; exact habi.2, hdm, hscr'⟩

theorem armStoreScr_spec {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {t : Ty} {pa : PArg Reg Empty ArmCond t} {a : AddrArg Reg} {c : List Directive}
    {clob : FlagMask} {scrOut : List (Reg × BitVec 64)} {v : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armStoreScr scr t pa a = some (c, clob, scrOut))
    (hregs : ∀ r ∈ pa.gprs ++ a.regs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hp : armMach.PArgHolds s t pa v) (hok : storeOk (armMach.mem s) t (a.eval (get s))) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' = storeMem (armMach.mem s) t (a.eval (get s)) v ∧
        ScrOk armMach armScratch scrOut s') post := by
  letI := h
  dsimp only [armStoreScr] at hc_in
  rw [Option.map_eq_some_iff] at hc_in
  rcases hc_in with ⟨⟨ci, clob', scrOut'⟩, hc, hceq⟩
  cases hceq
  dsimp only [armStoreScrIns] at hc
  rcases Option.bind_eq_some_iff.mp hc with ⟨scale, hsc, hc'⟩
  have hvaValid : armAddrValid scale a = true := by
    cases h' : armAddrValid scale a
    · simp [h'] at hc'
    · rfl
  rw [show (!armAddrValid scale a) = false by simp [hvaValid]] at hc'
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at hc'
  rcases hc' with ⟨⟨valSetup, rx, scr1⟩, hva, dir, hdir, rfl, rfl, rfl⟩
  have ht := armTy_of_armMemScale hsc
  have hpaRegs : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_left _ hr)
  have haRegs : ∀ r ∈ a.regs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_right _ hr)
  rw [List.append_assoc]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armFallsTo_of_wp (armWp_append (armStoreValInScr_wp hva hp hpaRegs ht hscr) ?_)
  rintro s₁ ⟨hrx16, ⟨w64, hrx₁, hw64⟩, hdmem₁, hst₁, hx₁, hsp₁, hscr₁⟩
  have hsetup := armSetupAddrScr_wp scr1 scale a s₁ haRegs hvaValid hscr₁
  generalize armSetupAddrScr scr1 scale a = sa at hdir hsetup
  rcases sa with ⟨addrSetup, addr, scr2⟩
  rcases hsetup with ⟨hnoSp, hwpAddr⟩
  have heqAddr : a.eval (get s₁) = a.eval (get s) := by
    cases a with
    | imm _ => rfl
    | baseDisp b disp =>
      simp only [AddrArg.eval]
      have hrb : b ∉ armScratch := haRegs b (by simp [AddrArg.regs])
      cases b with
      | SP => simp [get_sp, hsp₁]
      | reg rb =>
        have h17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hrb).2
        simp [get_reg, hx₁ rb h17]
    | baseIdxDisp b i sc disp =>
      cases b with
      | SP => simp [armAddrValid] at hvaValid
      | reg rb =>
        cases i with
        | SP => simp [armAddrValid] at hvaValid
        | reg ri =>
          have hrb : (.reg rb) ∉ armScratch := haRegs (.reg rb) (by simp [AddrArg.regs])
          have hri : (.reg ri) ∉ armScratch := haRegs (.reg ri) (by simp [AddrArg.regs])
          have hrb17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hrb).2
          have hri17 : ri ≠ .X17 := (xreg_ne_scratch_of_not_mem hri).2
          simp only [AddrArg.eval, get_reg, hx₁ rb hrb17, hx₁ ri hri17]
  refine armWp_append hwpAddr ?_
  rintro s₂ ⟨heval₂, hx₂, hsp₂, hdmem₂, hst₂, _, hscr₂⟩
  rw [heqAddr] at heval₂
  have hval₂ : GprHolds (s₂.regs.getRegOrZr (.low rx .W64)) t v := by
    cases rx with
    | XZR =>
      rw [getRegOrZr_low64_xzr]; rw [getRegOrZr_low64_xzr] at hrx₁
      rw [hrx₁]; exact hw64
    | reg rx' =>
      have hne16 : rx' ≠ .X16 := fun h => hrx16 (congrArg XRegOrXzr.reg h)
      rw [getRegOrZr_low64_reg, hx₂ rx' hne16]
      rw [getRegOrZr_low64_reg] at hrx₁
      rw [hrx₁]; exact hw64
  have hok₂ : storeOk s₂.dmem t (a.eval (get s)) := by rw [hdmem₂, hdmem₁]; exact hok
  refine armWp_mono (armStoreDir_wp hdir hnoSp heval₂ hval₂ hok₂) ?_
  rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
  refine ⟨⟨by simpa [armMach, hdmem₂, hdmem₁] using hdmem₃,
      scrOk_of_keeps hscr₂ fun r hr => by
        cases r with
        | SP => exact absurd (show XRegOrSp.SP ∈ armScratch from hr) (by simp [armScratch])
        | reg x => simp [get_reg, hregs₃]⟩,
    armFrame_status_eq ?_ (by rw [hst₃, hst₂, hst₁])⟩
  intro r hr
  cases r with
  | SP => simp [get_sp, hregs₃, hsp₂, hsp₁]
  | reg x =>
    have hx16' : x ≠ .X16 := fun e => hr (by simp [e, armScratch])
    have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
    simp [get_reg, hregs₃, hx₂ x hx16', hx₁ x hx17']

theorem armStoreZextIdxScr_spec {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {t : Ty} {pa : PArg Reg Empty ArmCond t} {base idx : Reg} {sc : AddrScale} {disp : Int64}
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {v : Val t} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armStoreZextIdxScr scr t pa base idx sc disp = some (c, clob, scrOut))
    (hpaRegs : ∀ r ∈ pa.gprs, r ∉ armScratch)
    (hbase : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) (hp : armMach.PArgHolds s t pa v)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hok : storeOk (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec)) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' =
          storeMem (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) v ∧
        ScrOk armMach armScratch scrOut s') post := by
  letI := h
  dsimp only [armStoreZextIdxScr] at hc_in
  rw [Option.map_eq_some_iff] at hc_in
  rcases hc_in with ⟨⟨ci, clob', scrOut'⟩, hc, hceq⟩
  cases hceq
  have ⟨scale, hsc⟩ : ∃ scale, armMemScale t = some scale := by
    cases hsc : armMemScale t with
    | none => simp [armStoreZextIdxScrIns, hsc] at hc
    | some s => exact ⟨s, rfl⟩
  simp only [armStoreZextIdxScrIns, hsc, Option.bind_some, bind, Option.bind_eq_some_iff] at hc
  rcases hc with ⟨⟨addrSetup, addr⟩, hsa, hc2⟩
  dsimp only at hc2
  rcases hc2 with ⟨⟨valSetup, rx, scr2⟩, hva, hc3⟩
  dsimp only at hc3
  simp only [Option.some.injEq, Prod.mk.injEq] at hc3
  rcases hc3 with ⟨dir, hdir, rfl, rfl, rfl⟩
  have ht := armTy_of_armMemScale hsc
  have hscr1 : ScrOk armMach armScratch
      (if addrSetup.isEmpty then scr else armKillScr [.reg .X16] scr) s := by
    by_cases hem : addrSetup.isEmpty
    · simp [hem, hscr]
    · simp [hem, scrOk_killScr _ hscr]
  have hscr1_noX16 : ¬addrSetup.isEmpty →
      ∀ p ∈ (if addrSetup.isEmpty then scr else armKillScr [.reg .X16] scr), p.1 ≠ .reg .X16 := by
    intro hne p hp
    simp only [hne, Bool.false_eq_true, ↓reduceIte, armKillScr, List.mem_filter] at hp
    intro h; have h16 : (p.1 == .reg .X16) = true := by rw [h]; exact reg_beq_self (.reg .X16)
    simp [h16] at hp
  have hval_noX16 : ∀ {scrA scrB vs rx},
      armStoreValInScr scrA t pa = some (vs, rx, scrB) →
      (∀ p ∈ scrA, p.1 ≠ .reg .X16) → ∀ p ∈ scrB, p.1 ≠ .reg .X16 := by
    intro scrA scrB vs rx hv ha p hp
    cases pa with
    | vec vr => exact vr.elim
    | flag c =>
      simp [armStoreValInScr] at hv; rcases hv with ⟨_, _, rfl⟩
      exact ha p (List.mem_filter.mp hp).1
    | gpr r => cases r with
      | reg _ =>
        rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [armStoreValInScr] at hv <;>
          rcases hv with ⟨_, _, rfl⟩ <;> exact ha p hp
      | SP =>
        rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [armStoreValInScr] at hv <;>
          rcases hv with ⟨_, _, rfl⟩ <;> exact ha p (List.mem_filter.mp hp).1
    | imm c =>
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · cases c <;> simp [armStoreValInScr] at hv <;> rcases hv with ⟨_, _, rfl⟩
        · exact ha p hp
        · dsimp only [armMovImmScr] at hp
          split at hp
          · exact ha p hp
          · dsimp only [armSetScr] at hp; rcases List.mem_cons.mp hp with rfl | hp'
            · intro e; cases e
            · exact ha p (List.mem_filter.mp hp').1
      all_goals
        simp only [armStoreValInScr] at hv
        split at hv
        · rcases hv with ⟨_, _, rfl⟩; exact ha p hp
        · rcases hv with ⟨_, _, rfl⟩
          dsimp only [armMovImmScr] at hp; split at hp
          · exact ha p hp
          · dsimp only [armSetScr] at hp; rcases List.mem_cons.mp hp with rfl | hp'
            · intro e; cases e
            · exact ha p (List.mem_filter.mp hp').1
  rw [List.append_assoc]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armFallsTo_of_wp (armWp_append (armStoreValInScr_wp hva hp hpaRegs ht hscr1) ?_)
  rintro s₁ ⟨hrx16, ⟨w64, hrx₁, hw64⟩, hdmem₁, hst₁, hx₁, hsp₁, hscr₂⟩
  by_cases hem : addrSetup.isEmpty
  · have haddr0 : addrSetup = [] := by
      cases addrSetup with | nil => rfl | cons _ _ => simp at hem
    subst haddr0
    cases base with
    | SP => simp [armSetupAddrZextIns] at hsa
    | reg rb => cases idx with
      | SP => simp [armSetupAddrZextIns] at hsa
      | reg ri =>
        dsimp only [armSetupAddrZextIns] at hsa
        split at hsa
        · rename_i hva'
          simp only [Option.some.injEq] at hsa
          by_cases hdisp0 : disp == 0
          · cases hamt : armMemExtendAmount scale sc with
            | none =>
              dsimp only [armAddrIdxValid] at hva'
              rw [beq_iff_eq] at hdisp0; subst hdisp0; simp [hamt] at hva'
            | some amt =>
              have heq : armSetupIdxDispIns true scale rb ri sc disp =
                  ([], armAtIdxExtScale true rb ri amt) := by
                simp [armSetupIdxDispIns, hdisp0, hamt]
              rw [heq] at hsa; injection hsa with _ ha_eq; subst ha_eq
              have hd0 : disp.toBitVec = 0#64 := by
                have := beq_iff_eq.mp hdisp0; subst this; rfl
              have hrb17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hbase).2
              have hri17 : ri ≠ .X17 := (xreg_ne_scratch_of_not_mem hidx).2
              have heval₁ : ∀ [Labels] p, (armAtIdxExtScale true rb ri amt).eval s₁ p =
                  (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec, s₁) := fun p => by
                rw [armAtIdxExtScale_eval true s₁ rb ri hamt p, hx₁ rb hrb17, hx₁ ri hri17]
                have hrb' : (s.regs.getXReg rb).toBitVec = vb := by
                  simpa [GprHolds, armMach, get_reg] using hvb.2
                have hri' : (s.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
                  simpa [GprHolds, armMach, get_reg] using hvi.2
                simp [hrb', hri', hd0]
              have hval₁ : GprHolds (s₁.regs.getRegOrZr (.low rx .W64)) t v := by
                rw [hrx₁]; exact hw64
              have hok₁ :
                  storeOk s₁.dmem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) := by
                rw [hdmem₁]; exact hok
              simp only [emitClean_nil, List.nil_append]
              refine armWp_mono (armStoreDir_wp hdir ⟨rb, rfl⟩ heval₁ hval₁ hok₁) ?_
              rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
              refine ⟨⟨by simpa [armMach, hdmem₁] using hdmem₃,
                  scrOk_of_keeps hscr₂ fun r hr => by
                    cases r with
                    | SP =>
                      exact absurd (show XRegOrSp.SP ∈ armScratch from hr) (by simp [armScratch])
                    | reg x => simp [get_reg, hregs₃]⟩,
                armFrame_status_eq (fun r hr => by
                  cases r with
                  | SP => simp [get_sp, hregs₃, hsp₁]
                  | reg x =>
                    have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
                    simp [get_reg, hregs₃, hx₁ x hx17']) (by rw [hst₃, hst₁])⟩
          · exfalso
            dsimp only [armSetupIdxDispIns] at hsa
            simp only [hdisp0, Bool.false_eq_true, ↓reduceIte] at hsa
            split at hsa
            · simp at hsa
            · dsimp only [armAddrIdxValid] at hva'
              simp only [hdisp0, Bool.false_or] at hva'
              have hboth : (armMemExtendAmount scale sc).isSome = true ∧
                  ((armImm12? disp.toBitVec).isSome = true ∨
                    (armImm12? (-disp.toBitVec)).isSome = true) := by
                rename_i hfit
                simpa [bne, hdisp0, hfit, Bool.and_eq_true, Bool.or_eq_true] using hva'
              obtain ⟨amt, hamt⟩ := Option.isSome_iff_exists.mp hboth.1
              have hadd : ∃ addIns,
                  armAddSubImmI? false .W64 .X16 rb disp.toBitVec = some addIns := by
                dsimp only [armAddSubImmI?]
                rcases hboth.2 with h1 | h2
                · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h1; simp [hei]
                · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h2
                  cases h1 : armImm12? disp.toBitVec <;> simp [hei]
              obtain ⟨addIns, hadd⟩ := hadd
              simp [hamt, hadd] at hsa
        · simp at hsa
  · obtain ⟨rb, ri, rfl, rfl, hnoSp, hwpAddr⟩ :=
      armSetupAddrZext_wp scale base idx sc disp s₁ hidx hsa
    have hrb17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hbase).2
    have hri17 : ri ≠ .X17 := (xreg_ne_scratch_of_not_mem hidx).2
    have hrb : (s₁.regs.getXReg rb).toBitVec = vb := by
      rw [hx₁ rb hrb17]; simpa [GprHolds, armMach, get_reg] using hvb.2
    have hri : (s₁.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
      rw [hx₁ ri hri17]; simpa [GprHolds, armMach, get_reg] using hvi.2
    rw [hrb, hri] at hwpAddr
    refine armWp_append hwpAddr ?_
    rintro s₂ ⟨heval₂, hx₂, hsp₂, hdmem₂, hst₂, _⟩
    have hval₂ : GprHolds (s₂.regs.getRegOrZr (.low rx .W64)) t v := by
      cases rx with
      | XZR =>
        rw [getRegOrZr_low64_xzr]; rw [getRegOrZr_low64_xzr] at hrx₁
        rw [hrx₁]; exact hw64
      | reg rx' =>
        have hne16 : rx' ≠ .X16 := fun h => hrx16 (congrArg XRegOrXzr.reg h)
        rw [getRegOrZr_low64_reg, hx₂ rx' hne16]
        rw [getRegOrZr_low64_reg] at hrx₁
        rw [hrx₁]; exact hw64
    have hno16 := hval_noX16 hva (hscr1_noX16 hem)
    have hscr₂' : ScrOk armMach armScratch scr2 s₂ := by
      intro p hp
      have hp16 := hno16 p hp
      have ⟨hs, hv⟩ := hscr₂ p hp
      refine ⟨hs, ?_⟩
      cases hpr : p.1 with
      | SP => exact absurd (hpr ▸ hs) (by simp [armScratch])
      | reg x =>
        have hx16 : x ≠ .X16 := fun e => hp16 (hpr ▸ congrArg XRegOrSp.reg e)
        rw [hpr] at hv
        simpa [armMach, get_reg, hx₂ x hx16] using hv
    have hok₂ : storeOk s₂.dmem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) := by
      rw [hdmem₂, hdmem₁]; exact hok
    refine armWp_mono (armStoreDir_wp hdir hnoSp heval₂ hval₂ hok₂) ?_
    rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
    refine ⟨⟨by simpa [armMach, hdmem₂, hdmem₁] using hdmem₃,
        scrOk_of_keeps hscr₂' fun r hr => by
          cases r with
          | SP => exact absurd (show XRegOrSp.SP ∈ armScratch from hr) (by simp [armScratch])
          | reg x => simp [get_reg, hregs₃]⟩,
      armFrame_status_eq ?_ (by rw [hst₃, hst₂, hst₁])⟩
    intro r hr
    cases r with
    | SP => simp [get_sp, hregs₃, hsp₂, hsp₁]
    | reg x =>
      have hx16' : x ≠ .X16 := fun e => hr (by simp [e, armScratch])
      have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
      simp [get_reg, hregs₃, hx₂ x hx16', hx₁ x hx17']

theorem armLoadScr_noLab {scr : List (Reg × BitVec 64)} {t : Ty} {rd : Reg} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    (hc : armLoadScr scr t rd a = some (c, clob, scrOut)) (l : Sym) :
    Kraken.Directive.label l ∉ c := by
  dsimp only [armLoadScr] at hc
  rw [Option.map_eq_some_iff] at hc
  rcases hc with ⟨⟨ci, cl, sc⟩, _, h⟩; cases h; exact emitClean_noLab ci l

theorem armLoadZextIdxScr_noLab {scr : List (Reg × BitVec 64)} {t : Ty} {rd base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask}
    {scrOut : List (Reg × BitVec 64)}
    (hc : armLoadZextIdxScr scr t rd base idx sc disp = some (c, clob, scrOut)) (l : Sym) :
    Kraken.Directive.label l ∉ c := by
  dsimp only [armLoadZextIdxScr] at hc
  rw [Option.map_eq_some_iff] at hc
  rcases hc with ⟨⟨ci, cl, sc'⟩, _, h⟩; cases h; exact emitClean_noLab ci l

theorem armStoreScr_noLab {scr : List (Reg × BitVec 64)} {t : Ty}
    {pa : PArg Reg Empty ArmCond t} {a : AddrArg Reg} {c : List Directive} {clob : FlagMask}
    {scrOut : List (Reg × BitVec 64)}
    (hc : armStoreScr scr t pa a = some (c, clob, scrOut)) (l : Sym) :
    Kraken.Directive.label l ∉ c := by
  dsimp only [armStoreScr] at hc
  rw [Option.map_eq_some_iff] at hc
  rcases hc with ⟨⟨ci, cl, sc⟩, _, h⟩; cases h; exact emitClean_noLab ci l

theorem armStoreZextIdxScr_noLab {scr : List (Reg × BitVec 64)} {t : Ty}
    {pa : PArg Reg Empty ArmCond t} {base idx : Reg} {sc : AddrScale} {disp : Int64}
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    (hc : armStoreZextIdxScr scr t pa base idx sc disp = some (c, clob, scrOut)) (l : Sym) :
    Kraken.Directive.label l ∉ c := by
  dsimp only [armStoreZextIdxScr] at hc
  rw [Option.map_eq_some_iff] at hc
  rcases hc with ⟨⟨ci, cl, sc'⟩, _, h⟩; cases h; exact emitClean_noLab ci l

end LeanQbe.T.Arm64
