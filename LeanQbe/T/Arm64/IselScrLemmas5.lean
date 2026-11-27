module

public import LeanQbe.T.Arm64.IselScrLemmas4

/-!
# AArch64 Wave 6.2-A Scratch-Aware Lowering Spec & Label Freedom — Part 5

Verifies top-level `armOpScr_spec_aux` and `armOpScr_noLab` for `armOpScr`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

private theorem armOpScr_fallback {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {sig rs : List Ty} {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Reg Empty ArmCond) rs} {vh : VariantHint} {c : List Directive}
    {clob : FlagMask} {scrOut : List (Reg × BitVec 64)} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hopSpec : ∀ {c' cl'}, armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (tupDstGprs dsts ++ armScratch) [] cl' s
        (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
            (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
                {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
              pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
              armGpr.cmpFlagsOut? co w pa pb pd = some lf →
              FlagCmpOk armMach armGpr s'
                (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
                (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
          armMach.mem s' = armMach.mem s) post)
    (hopZext : ∀ {t0} {ht : rs = [t0]} {rd c' cl'},
      dsts = ht ▸ (.gpr rd, ()) → armGpr.zeroExtOp code pas dsts = true →
      armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (rd :: armScratch) [] cl' s
        (fun s' => (∃ rv : Val t0, P (ht ▸ (rv, ())) ∧ AbiGprHolds (armMach.getGpr s' rd) t0 rv) ∧
          armMach.mem s' = armMach.mem s) post)
    (_hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hdsts : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) (hrel : TRel (armMach.PArgHolds s) pas vs)
    (hwp : code.wp vs P) (hop : armOp code pas dsts vh = some (c, clob))
    (hnotCmp : ∀ {co w} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]},
      code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) → False)
    (hso : (armKeepScr code pas = true ∧ scrOut = scr) ∨ scrOut = []) :
    armMach.FallsTo armCondReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t0} {ht : rs = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armGpr.zeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
          (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
              {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
            pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
            armGpr.cmpFlagsOut? co w pa pb pd = some lf →
            FlagCmpOk armMach armGpr s'
              (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
              (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  rcases hso with ⟨hk, rfl⟩ | rfl
  · exact (armOpScr_keep_fallsTo hk hop hdsts hscr hrel hwp).conseq
      fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ => ⟨⟨rvs, hp, htr, hz, fun {co w pa pb pd lf}
        {h1 h2 _he} => absurd _he (hnotCmp (co := co) (w := w) (h1 := h1) (h2 := h2))⟩, hm, hs⟩
  · by_cases hz : ∃ t0, ∃ ht : rs = [t0], ∃ rd, dsts = ht ▸ (.gpr rd, ()) ∧
        armGpr.zeroExtOp code pas dsts = true
    · rcases hz with ⟨t0, ht, rd, rfl, hz0⟩; subst ht
      exact (@hopZext t0 rfl rd _ _ rfl hz0 hop).conseq fun s' ⟨⟨rv, hp, hab⟩, hm⟩ _ => by
        have htr : TRel (as := [t0]) (armMach.PDstHolds s') (.gpr rd, ()) (rv, ()) :=
          .cons hab.toGprHolds .nil
        refine ⟨⟨(rv, ()), hp, htr, fun {t0' ht' rd'} hrd' _ => ?_,
          fun {co w pa pb pd lf} {h1 h2 _he} =>
            absurd _he (hnotCmp (co := co) (w := w) (h1 := h1) (h2 := h2))⟩, hm, scrOk_nil s'⟩
        obtain rfl : t0 = t0' := (List.cons.inj ht').1; cases hrd'; exact hab
    · exact (hopSpec hop).conseq
        fun s' ⟨⟨rvs, hp, htr, hfc⟩, hm⟩ _ => ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz0 =>
          absurd ⟨t0, ht, rd, hdr, hz0⟩ hz, fun {co w pa pb pd lf} {h1 h2 _he} hp' hd' hl' =>
            @hfc co w pa pb pd lf h1 h2 _he hp' hd' hl'⟩, hm, scrOk_nil s'⟩

private theorem armOpScr_inr {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {sig rs : List Ty} {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Reg Empty ArmCond) rs} {vh : VariantHint} {c : List Directive}
    {clob : FlagMask} {scrOut : List (Reg × BitVec 64)} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hopSpec : ∀ {c' cl'}, armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (tupDstGprs dsts ++ armScratch) [] cl' s
        (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
            (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
                {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
              pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
              armGpr.cmpFlagsOut? co w pa pb pd = some lf →
              FlagCmpOk armMach armGpr s'
                (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
                (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
          armMach.mem s' = armMach.mem s) post)
    (hopZext : ∀ {t0} {ht : rs = [t0]} {rd c' cl'},
      dsts = ht ▸ (.gpr rd, ()) → armGpr.zeroExtOp code pas dsts = true →
      armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (rd :: armScratch) [] cl' s
        (fun s' => (∃ rv : Val t0, P (ht ▸ (rv, ())) ∧ AbiGprHolds (armMach.getGpr s' rd) t0 rv) ∧
          armMach.mem s' = armMach.mem s) post)
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hdsts : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) (hrel : TRel (armMach.PArgHolds s) pas vs)
    (hwp : code.wp vs P)
    (hnotCmp : ∀ {co w} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]},
      code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) → False)
    (hc : (armOp code pas dsts vh).map (fun (c, cl) => (c, cl, ([] : List (Reg × BitVec 64)))) =
      some (c, clob, scrOut)) :
    armMach.FallsTo armCondReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t0} {ht : rs = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armGpr.zeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
          (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
              {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
            pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
            armGpr.cmpFlagsOut? co w pa pb pd = some lf →
            FlagCmpOk armMach armGpr s'
              (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
              (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  obtain ⟨⟨_, _⟩, hop, hq⟩ := Option.map_eq_some_iff.mp hc; rcases hq with ⟨rfl, rfl, rfl⟩
  exact armOpScr_fallback hopSpec (fun {t0} {ht} {rd c' cl'} => @hopZext t0 ht rd c' cl')
    hargs hdsts hscr hrel hwp hop (fun {co w h1 h2} => @hnotCmp co w h1 h2) (.inr rfl)

theorem armOpScr_spec_aux {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)} {sig rs : List Ty}
    {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Reg Empty ArmCond) rs} {vh : VariantHint} {c : List Directive}
    {clob : FlagMask} {scrOut : List (Reg × BitVec 64)} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hopSpec : ∀ {c' cl'}, armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (tupDstGprs dsts ++ armScratch) [] cl' s
        (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
            (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
                {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
              pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
              armGpr.cmpFlagsOut? co w pa pb pd = some lf →
              FlagCmpOk armMach armGpr s'
                (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
                (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
          armMach.mem s' = armMach.mem s) post)
    (hopZext : ∀ {t0} {ht : rs = [t0]} {rd c' cl'},
      dsts = ht ▸ (.gpr rd, ()) → armGpr.zeroExtOp code pas dsts = true →
      armOp code pas dsts vh = some (c', cl') →
      armMach.FallsTo armCondReads h k c' (rd :: armScratch) [] cl' s
        (fun s' => (∃ rv : Val t0, P (ht ▸ (rv, ())) ∧ AbiGprHolds (armMach.getGpr s' rd) t0 rv) ∧
          armMach.mem s' = armMach.mem s) post)
    (hc : armOpScr scr code pas dsts vh = some (c, clob, scrOut))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hdsts : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) (hrel : TRel (armMach.PArgHolds s) pas vs)
    (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t0} {ht : rs = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armGpr.zeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
          (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
              {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
            pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
            armGpr.cmpFlagsOut? co w pa pb pd = some lf →
            FlagCmpOk armMach armGpr s'
              (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
              (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  have fb {c' cl' s'} (hop : armOp code pas dsts vh = some (c', cl'))
      (hnc : ∀ {co w} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]},
        code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) → False)
      (hso : (armKeepScr code pas = true ∧ s' = scr) ∨ s' = []) :=
    armOpScr_fallback (c := c') (clob := cl') (scrOut := s')
      hopSpec (fun {t0} {ht} {rd c'' cl''} => @hopZext t0 ht rd c'' cl'')
      hargs hdsts hscr hrel hwp hop (fun {co w h1 h2} => @hnc co w h1 h2) hso
  have inr'
      (hnc : ∀ {co w} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]},
        code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) → False)
      (hmap : (armOp code pas dsts vh).map
        (fun (c, cl) => (c, cl, ([] : List (Reg × BitVec 64)))) = some (c, clob, scrOut)) :=
    armOpScr_inr hopSpec (fun {t0} {ht} {rd c'' cl''} => @hopZext t0 ht rd c'' cl'')
      hargs hdsts hscr hrel hwp (fun {co w h1 h2} => @hnc co w h1 h2) hmap
  cases code
  case add t | sub t | mul t | «and» t | «or» t | xor t =>
    cases t <;> dsimp only [armOpScr] at hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · rename_i n
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩
      · have hd := hdsts (.reg d) (by simp [tupDstGprs])
        have ⟨hpa, hpb⟩ := trel2_inv hrel
        first
        | exact (armOpScr_bin_spec .add (code := .add (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
        | exact (armOpScr_bin_spec .sub (code := .sub (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
        | exact (armOpScr_bin_spec .mul (code := .mul (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
        | exact (armOpScr_bin_spec .and (code := .and (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
        | exact (armOpScr_bin_spec .or  (code := .or  (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
        | exact (armOpScr_bin_spec .xor (code := .xor (.bits n)) d hc hargs hd hscr hpa hpb
            hwp).conseq fun _ ⟨⟨rvs, hp, htr, hz⟩, hm, hs⟩ _ =>
              ⟨⟨rvs, hp, htr, fun {t0 ht rd} hdr hz' => by
                rcases rvs with ⟨rv0, ⟨⟩⟩; cases ht; cases hdr; rcases htr with _ | ⟨hgh, _⟩
                have hza := hz hz'; rw [← hgh.2, hza.toGprHolds.2]; exact hza,
                fun {_ _ _ _ _ _ _ h2} => by cases h2⟩, hm, hs⟩
      · exact inr' (fun {_ _ _ h2} _ => by cases h2) hc
      · exact vr.elim
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
  case cmp o t m hm =>
    subst hm
    cases t <;> dsimp only [armOpScr] at hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; rcases dsts with ⟨dst, ⟨⟩⟩
      exact (armOpScr_cmp_spec o dst hc hargs hdsts hscr (trel2_inv hrel).1 (trel2_inv hrel).2
        hwp).conseq fun _ ⟨hp, htr, hab, hfc, hm, hs⟩ _ =>
          ⟨⟨((o.evalBits va vb, ()) : Tup Val [.bool]), hp, htr, fun {t0 ht rd} hdr _ => by
            cases ht; cases hdr; exact hab rd rfl,
            fun {co w pa' pb' pd lf} {h1 h2 _he} hpa hpb hl => by
              have hn : _ = w := Ty.bits.inj (List.cons.inj h1).1
              subst hn; cases _he; cases hpa; cases hpb; exact hfc hl⟩, hm, hs⟩
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
  case select t =>
    cases t <;> dsimp only [armOpScr] at hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩
      rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩
      · have hd := hdsts (.reg d) (by simp [tupDstGprs])
        have ⟨hpc, hpa, hpb⟩ := trel3_inv hrel
        exact (armOpScr_sel_spec d hc hargs hd hscr hpc hpa hpb hwp).conseq
          fun _ ⟨hp, htr, hz, hm, hs⟩ _ =>
            ⟨⟨((if vc then va else vb, ()) : Tup Val [.bits _]), hp, htr,
              fun {t0 ht rd} hdr hz' => by cases ht; cases hdr; exact hz hz',
              fun {_ _ _ _ _ _} _ {h2} => by cases h2⟩, hm, hs⟩
      · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
      · exact vr.elim
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
    · exact inr' (fun {_ _ h1 _} _ => by cases h1) hc
  case shl t | lshr t | ashr t =>
    dsimp only [armOpScr] at hc
    obtain ⟨⟨_, _⟩, hop, hq⟩ := Option.map_eq_some_iff.mp hc; rcases hq with ⟨rfl, rfl, rfl⟩
    refine fb hop (fun {_ _ h1 h2} _ => by cases t with | bits _ => cases h2 | _ => cases h1) ?_
    cases t with
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩
      cases pa with
      | gpr r =>
        cases r with
        | reg _ =>
          cases pb with
          | imm _ =>
            exact if hn : (n == 32 || n == 64) = true then .inl ⟨hn, by simp [hn]⟩
            else .inr (by simp [hn])
          | _ => exact .inr rfl
        | SP => exact .inr rfl
      | _ => exact .inr rfl
    | _ => exact .inr rfl
  all_goals
    dsimp only [armOpScr] at hc
    obtain ⟨⟨_, _⟩, hop, hq⟩ := Option.map_eq_some_iff.mp hc; rcases hq with ⟨rfl, rfl, rfl⟩
    refine fb hop (fun {_ _ h1 h2} he => by cases h1 <;> cases h2 <;> cases he) ?_
    first | exact .inl ⟨rfl, rfl⟩ | exact .inr rfl

theorem armOpScr_noLab {scr : List (Reg × BitVec 64)} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg Empty ArmCond) sig} {dsts : Tup (PDst Reg Empty ArmCond) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    (hc : armOpScr scr code pas dsts vh = some (c, clob, scrOut)) (l : Sym) :
    Kraken.Directive.label l ∉ c := by
  have hfb {scr' : List (Reg × BitVec 64)}
      (h : (armOp code pas dsts vh).map (fun (c, cl) => (c, cl, scr')) = some (c, clob, scrOut)) :
      Kraken.Directive.label l ∉ c := by
    obtain ⟨⟨ci, cl⟩, hop, rfl, _, _⟩ := Option.map_eq_some_iff.mp h
    exact emitCleanPair_noLab hop l
  have hmap {x : Option (List Instr × FlagMask × List (Reg × BitVec 64))}
      (h : x.map (fun (c, cl, s') => (emitClean c, cl, s')) = some (c, clob, scrOut)) :
      Kraken.Directive.label l ∉ c := by
    obtain ⟨⟨ci, cl, sc⟩, _, rfl, _, _⟩ := Option.map_eq_some_iff.mp h
    exact emitClean_noLab ci l
  dsimp only [armOpScr] at hc
  cases code with
  | add t | sub t | mul t | «and» t | «or» t | xor t =>
    cases t <;> try exact hfb hc
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact vr.elim
    · exact hmap hc
    · exact hfb hc
  | cmp o t m hm =>
    subst hm; cases t <;> try exact hfb hc
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨dst, ⟨⟩⟩; exact hmap hc
  | select t =>
    cases t <;> try exact hfb hc
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;>
      try exact vr.elim
    · exact hmap hc
    · exact hfb hc
  | _ =>
    obtain ⟨⟨ci, cl⟩, hop, rfl, _, _⟩ := Option.map_eq_some_iff.mp hc
    exact emitCleanPair_noLab hop l

end LeanQbe.T.Arm64
