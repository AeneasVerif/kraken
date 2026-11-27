module

public import LeanQbe.T.RegaW62Lemmas

/-!
# Wave 6.2-A Checked Lowering Proofs Part 2 (`T.RegaW62Lemmas2`)

* Cross-block `.gprZ` entry/parameter checking (`LiveZOk.mono`, `LiveZOk.frame`, `holdsZLoc_ok`,
  `paramZVal_of_locZOk`, `entryZOk_ok`, `buildEntryBaseZ_ok`, `bindBlockParamsZ_ok`).
* Label-cleanliness helpers (`*_some`, `*_clean`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

/-! ## Cross-Block `.gprZ` / `.gprZ`-Slot Soundness (`OPT-10a`) -/

theorem LocZOk.mono {G G' : VCtx} (hsub : ∀ p ∈ G, p ∈ G') {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {loc : T.toIsa.Loc}
    (h : LocZOk T.mach G' s σ sa loc) : LocZOk T.mach G s σ sa loc := by
  have hT : ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ⟨t, v, x⟩ ∈ G' :=
    fun _ _ _ _ hm => hsub _ hm
  cases loc with
  | gpr r => cases sa <;> first | exact h | exact SymZ.tr hT h
  | slot i w =>
    refine ⟨h.1, ?_⟩
    cases sa with
    | var x =>
      obtain ⟨w64, h1, h2⟩ := h.2
      exact ⟨w64, h1, SymZ.tr hT h2⟩
    | _ => exact h.2
  | vec _ | flag _ => exact h

theorem LiveZOk.mono {G G' : VCtx} (hsub : ∀ p ∈ G, p ∈ G') {s : T.mach.MData}
    {σ : List (BitVec 64)} :
    ∀ {live : List (SymArg × T.toIsa.Loc)} {liveZ : List Bool},
    LiveZOk T.mach G' s σ live liveZ → LiveZOk T.mach G s σ live liveZ
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨fun hz => (h1 hz).mono hsub, LiveZOk.mono hsub h2⟩

theorem LocZOk.frame {G : VCtx} {s s' : T.mach.MData} {σ : List (BitVec 64)} {sa : SymArg}
    {loc : T.toIsa.Loc} {g : List T.Reg} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' g v f) (hok : LocZOk T.mach G s σ sa loc)
    (hg : ∀ r, loc = .gpr r → r ∉ g) : LocZOk T.mach G s' σ sa loc := by
  cases loc with
  | gpr r => cases sa <;> simp only [LocZOk] at hok ⊢ <;> rwa [hfr.1 r (hg r rfl)]
  | slot _ _ | vec _ | flag _ => exact hok

theorem LiveZOk.frame {G : VCtx} {s s' : T.mach.MData} {σ : List (BitVec 64)}
    {g : List T.Reg} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' g v f)
    (hg : ∀ (r : T.Reg), r ∉ g ∨ True) :
    ∀ {live : List (SymArg × T.toIsa.Loc)} {liveZ : List Bool},
    (∀ p ∈ live, ∀ r, p.2 = .gpr r → r ∉ g) →
    LiveZOk T.mach G s σ live liveZ → LiveZOk T.mach G s' σ live liveZ
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | (_, _loc) :: _, _ :: _, hloc, ⟨h1, h2⟩ =>
    ⟨fun hz => (h1 hz).frame hfr (hloc _ (List.mem_cons_self ..)),
     LiveZOk.frame hfr hg (fun p hp => hloc p (List.mem_cons_of_mem _ hp)) h2⟩

theorem holdsZLoc_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {loc : T.toIsa.Loc}
    (hA : Agree T G nv st s σ) (hh : holdsZLoc T.toIsa st sa loc = true) :
    LocZOk T.mach G s σ sa loc := by
  cases loc with
  | gpr r =>
    cases sa with
    | var x => exact (holdsVarGprZ_ok hA hh).2
    | immBits w c =>
      simp only [holdsZLoc, List.any_eq_true, Bool.and_eq_true] at hh
      obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := hh
      obtain rfl := symArgEq_eq he1
      have h0 := hA.regs _ hmem
      have hgs : GprSym G (T.mach.getGpr s r) (.immBits 64 c) := by
        cases rl' with
        | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0
        | gprZ r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0.1
        | _ => simp [regLocMatchesGpr] at he2
      exact hgs.2
    | immBool b =>
      simp only [holdsZLoc, List.any_eq_true, Bool.and_eq_true] at hh
      obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := hh
      obtain rfl := symArgEq_eq he1
      have h0 := hA.regs _ hmem
      have hgs : GprSym G (T.mach.getGpr s r) (.immBits 64 (if b then 1#64 else 0#64)) := by
        cases rl' with
        | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0
        | gprZ r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0.1
        | _ => simp [regLocMatchesGpr] at he2
      exact hgs.2
    | immVec _ _ => simp [holdsZLoc] at hh
  | slot i w =>
    simp only [holdsZLoc] at hh; split at hh; · simp at hh
    rename_i hwn
    have hw : w = .w64 := by cases w <;> simp_all [slotWidthEq]
    cases sa with
    | immBits _ _ | immBool _ | immVec _ _ => simp at hh
    | var x =>
      cases hf : st.slots.find? i with
      | none => simp [hf] at hh
      | some se =>
        cases se with
        | gpr _ | vec _ _ => simp [hf] at hh
        | gprZ sas =>
          rw [hf] at hh
          simp only [List.any_eq_true, Bool.and_eq_true] at hh
          obtain ⟨⟨sa', z'⟩, hmem, rfl, heq⟩ := hh
          obtain rfl := symArgEq_eq heq
          obtain ⟨w64, hσ, hall⟩ := hA.slots i _ hf
          exact ⟨hw, w64, hσ, (hall _ hmem).2 rfl⟩
  | vec _ | flag _ => simp [holdsZLoc] at hh

theorem paramZVal_of_locZOk {G : VCtx} {s : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {a₁ : Arg Val t} {a₂ : Arg VNat t} {sa : SymArg} {loc : T.toIsa.Loc}
    (hrel : ArgRel G t a₁ a₂) (hsa : toSymArg T.toIsa t a₂ = some sa)
    (hok : LocZOk T.mach G s σ sa loc) : ParamZVal T.mach s σ t a₁.val loc := by
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    cases loc with
    | gpr r => exact hok _ _ hm
    | slot i w =>
      obtain ⟨hw, w64, hσ, hsz⟩ := hok
      exact ⟨hw, w64, hσ, hsz _ _ hm⟩
    | vec _ | flag _ => exact hok
  | imm c =>
    cases t with
    | bool =>
      simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
      cases loc with
      | gpr r => cases c <;> exact hok
      | slot i w => exact hok.2.elim
      | vec _ | flag _ => exact hok
    | bits k =>
      simp only [toSymArg] at hsa; split at hsa
      · rename_i hk; simp only [Option.some.injEq] at hsa; subst hsa
        have hk : k ≤ 64 := by simpa using hk
        cases loc with
        | gpr r => exact ⟨hk, hok⟩
        | slot i w => exact hok.2.elim
        | vec _ | flag _ => exact hok
      · simp at hsa
    | pair _ _ =>
      simp only [toSymArg, Option.map_eq_some_iff] at hsa
      obtain ⟨_, _, rfl⟩ := hsa
      cases loc with
      | gpr _ | vec _ | flag _ => exact hok
      | slot _ _ => exact hok.2.elim
    | float _ => simp [toSymArg] at hsa

theorem entryZOk_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {en : Entry T.Reg T.VReg T.Cond}
    {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts}
    {argTgts : List (SymArg × T.toIsa.Loc)}
    (hA : Agree T G nv st s σ) (hrel : TRel (ArgRel G) args₁ args)
    (hj : jumpTargets T.toIsa args en.ploc = some argTgts)
    (hz : entryZOk T.toIsa st en argTgts = true) :
    LiveZOk T.mach G s σ en.live en.liveZ ∧
    ParamsZOk T.mach s σ ts (vals args₁) en.ploc en.plocZ := by
  simp only [entryZOk, Bool.and_eq_true] at hz
  have hLive : ∀ live liveZ, entryZOk.goLive T.toIsa st live liveZ = true →
      LiveZOk T.mach G s σ live liveZ := by
    intro live
    induction live with
    | nil => intro liveZ _; cases liveZ <;> trivial
    | cons p rest ih =>
      intro liveZ hg
      cases liveZ with
      | nil => trivial
      | cons z zs =>
        simp only [entryZOk.goLive, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hg
        refine ⟨fun hz => holdsZLoc_ok hA ((hg.1).resolve_left (by simp [hz])), ih zs hg.2⟩
  have hArg : ∀ {ts'} {a₁ : Tup (Arg Val) ts'} {a : Tup (Arg VNat) ts'}
      {ploc : List T.toIsa.Loc} {plocZ : List Bool} {tgts : List (SymArg × T.toIsa.Loc)},
      TRel (ArgRel G) a₁ a → jumpTargets T.toIsa a ploc = some tgts →
      entryZOk.goArg T.toIsa st tgts plocZ = true →
      ParamsZOk T.mach s σ ts' (vals a₁) ploc plocZ := by
    intro ts' a₁ a ploc plocZ tgts hr
    induction hr generalizing ploc plocZ tgts with
    | nil =>
      intro hj' _
      cases ploc <;> cases plocZ <;> simp_all [jumpTargets, ParamsZOk]
    | cons hr0 _ ih =>
      intro hj' hg
      cases ploc with
      | nil => simp [jumpTargets] at hj'
      | cons loc locs =>
        dsimp only [jumpTargets] at hj'
        split at hj'
        · rename_i sa rest hsa hrest
          simp only [Option.some.injEq] at hj'; subst hj'
          cases plocZ with
          | nil => cases rest <;> trivial
          | cons z zs =>
            simp only [entryZOk.goArg, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hg
            exact ⟨fun hz => paramZVal_of_locZOk hr0 hsa
              (holdsZLoc_ok hA ((hg.1).resolve_left (by simp [hz]))), ih hrest hg.2⟩
        · simp at hj'
  exact ⟨hLive _ _ hz.1, hArg hrel hj hz.2⟩

private theorem addSlotZEntry_ok {G : VCtx} {nv : Nat} {σ : List (BitVec 64)}
    {vw : Trie SlotWidth} {sa : SymArg} {z : Bool} {i : Nat} {w : SlotWidth}
    {sl sl' : Trie SlotEntry} (ha : addSlotZEntry vw sa z i w sl = some sl')
    (hsl : SlotsOk G nv σ sl)
    (hloc : w = .w64 ∧ SlotOk G σ i (.gpr [sa]))
    (hlz : z = true → SymZ G (σ[i]?.getD 0#64) sa)
    (hsc : symArgScopeOk nv sa = true)
    (hi : i + w.slots ≤ σ.length) : SlotsOk G nv σ sl' := by
  have hm1 : sa ∈ [sa] := List.mem_singleton_self _
  unfold addSlotZEntry at ha
  split at ha; · skip; · simp at ha
  split at ha; · simp at ha
  rename_i hw64
  have hw64' : w = .w64 := by simpa [slotWidthEq_iff] using hw64
  subst hw64'
  have hi' : i < σ.length := by simp [SlotWidth.slots] at hi; omega
  obtain ⟨_, w0, hσ, hgpr⟩ := hloc
  have hsz : z = true → SymZ G w0 sa := by
    intro hz; have h := hlz hz; rw [hσ] at h; exact h
  have hpair : GprSym G w0 sa ∧ (z = true → SymZ G w0 sa) := ⟨hgpr sa hm1, hsz⟩
  have hfresh : SlotOk G σ i (.gprZ [(sa, z)]) ∧
      ∀ sa' ∈ (SlotEntry.gprZ [(sa, z)]).sas, symArgScopeOk nv sa' = true :=
    ⟨⟨w0, hσ, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hpair⟩,
     by simpa [SlotEntry.sas] using hsc⟩
  split at ha
  · rename_i sas hf
    simp only [Option.some.injEq] at ha; subst ha
    obtain ⟨⟨w1, hσ1, hall⟩, hsc1⟩ := hsl i _ hf
    rw [hσ] at hσ1; cases hσ1
    refine hsl.insert ⟨⟨w0, hσ, fun p hp => ?_⟩, fun sa' hsa' => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp'
      · exact hpair
      · exact hall p hp'
    · simp only [SlotEntry.sas, List.map_cons, List.mem_cons] at hsa'
      rcases hsa' with rfl | hsa''
      · exact hsc
      · exact hsc1 sa' hsa''
  · rename_i sas hf
    simp only [Option.some.injEq] at ha; subst ha
    obtain ⟨⟨w1, hσ1, hall⟩, hsc1⟩ := hsl i _ hf
    rw [hσ] at hσ1; cases hσ1
    refine hsl.insert ⟨⟨w0, hσ, fun p hp => ?_⟩, fun sa' hsa' => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp'
      · exact hpair
      · obtain ⟨sa', hsa', rfl⟩ := List.mem_map.mp hp'
        exact ⟨hall sa' hsa', fun h => by cases h⟩
    · simp only [SlotEntry.sas, List.map_cons, List.map_map, Function.comp_def, List.mem_cons]
        at hsa'
      rcases hsa' with rfl | hsa''
      · exact hsc
      · obtain ⟨sa0, hsa0, rfl⟩ := List.mem_map.mp hsa''
        exact hsc1 sa0 hsa0
  · simp only [Option.some.injEq] at ha; subst ha
    exact (hsl.clear _ _).insert hfresh

private theorem buildEntryBaseZ_aux {G : VCtx} {nv : Nat} {vw : Trie SlotWidth} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hσ : σ.length = hints.nslots) :
    ∀ (live : List (SymArg × T.toIsa.Loc)) (liveZ : List Bool) (st st' : SymState T.toIsa),
    st.vecWidths = vw →
    buildEntryBaseZ T.toIsa hints.nslots vw live liveZ st = some st' →
    (∀ p ∈ live, LocOk T.mach G s σ p.1 p.2) →
    LiveZOk T.mach G s σ live liveZ →
    (∀ p ∈ live, symArgScopeOk nv p.1 = true) →
    Agree T G nv st s σ → Agree T G nv st' s σ
  | [], _, st, st', _, hb, _, _, _, hA => by
    simp only [buildEntryBaseZ, Option.some.injEq] at hb; subst hb; exact hA
  | (sa, loc) :: rest, zs, st, st', hvw, hb, hl, hlz, hs, hA => by
    have hl0 := hl _ (List.mem_cons_self ..)
    have hs0 : symArgScopeOk nv sa = true := hs _ (List.mem_cons_self ..)
    have hlz0 : zs.headD false = true → LocZOk T.mach G s σ sa loc := by
      cases zs with
      | nil => intro h; simp at h
      | cons z zs' => exact hlz.1
    have hlz' : LiveZOk T.mach G s σ rest zs.tail := by
      cases zs with
      | nil => cases rest <;> trivial
      | cons _ _ => exact hlz.2
    have IH := fun st1 (h1 : st1.vecWidths = vw) hb1 =>
      buildEntryBaseZ_aux hσ rest zs.tail st1 st' h1 hb1
        (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hlz'
        (fun p hp => hs p (List.mem_cons_of_mem _ hp))
    cases loc with
    | gpr r =>
      dsimp only [buildEntryBaseZ] at hb
      split at hb
      · cases sa with
        | immBits _ _ | immBool _ | immVec _ _ =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hb
          exact IH { st with regs := (_, .gpr r) :: st.regs } hvw hb
            (hA.pushReg (rl := .gpr r) hl0 hs0)
        | var x =>
          dsimp only at hb
          split at hb
          · rename_i hisZ
            simp only [Bool.and_true] at hisZ
            have hsymZ : SymZ G (T.mach.getGpr s r) (.var x) := hlz0 hisZ
            exact IH { st with regs := (.var x, .gprZ r) :: st.regs } hvw hb
              (hA.pushReg (rl := .gprZ r) ⟨hl0, hsymZ⟩ hs0)
          · exact IH { st with regs := (.var x, .gpr r) :: st.regs } hvw hb
              (hA.pushReg (rl := .gpr r) hl0 hs0)
      · simp at hb
    | vec v =>
      dsimp only [buildEntryBaseZ] at hb; split at hb
      · exact IH { st with regs := (sa, .vec v) :: st.regs } hvw hb
          (hA.pushReg (rl := .vec v) hl0 hs0)
      · simp at hb
    | flag c =>
      dsimp only [buildEntryBaseZ] at hb
      exact IH { st with regs := (sa, .flag c) :: st.regs } hvw hb
        (hA.pushReg (rl := .flag c) hl0 hs0)
    | slot i w =>
      dsimp only [buildEntryBaseZ] at hb; split at hb; · simp at hb
      rename_i hi
      simp only [Option.bind_eq_some_iff] at hb
      obtain ⟨sl', ha, hb⟩ := hb
      have hislot : i + w.slots ≤ σ.length := by rw [hσ]; simpa using hi
      have finishPlain : addSlotEntry vw sa i w st.slots = some sl' → Agree T G nv st' s σ :=
        fun ha' => IH { st with slots := sl' } hvw hb (hA.setSlots (addSlotEntry_ok ha'
          (fun j se hj => ⟨hA.slots j se hj, hA.slots_lt j se hj⟩) hl0 hs0
          (fun x wx hx t v hm => (hA.vw x wx (hvw ▸ hx) t v hm).2)
          (fun x hx t v hm => hA.vt x t v hm (hvw ▸ hx)) hislot))
      cases sa with
      | immBits _ _ | immBool _ | immVec _ _ =>
        simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at ha
        exact finishPlain ha
      | var x =>
        dsimp only at ha
        split at ha
        · rename_i hz
          simp only [Bool.and_eq_true, Bool.and_true] at hz
          obtain ⟨hw64, w0, hσw, hsymZ⟩ := hlz0 hz.1.1
          subst hw64
          have hslotGpr : SlotOk G σ i (.gpr [.var x]) := by
            rcases hl0 with ⟨_, hty⟩ | ⟨_, x0, h1, h2⟩
            · refine ⟨w0, hσw, fun sa' hsa' => ?_⟩
              rw [List.mem_singleton] at hsa'; subst hsa'
              intro t' v' hm'
              obtain ⟨a, b, rfl⟩ := hty t' v' hm'
              exact (hsymZ (.pair a b) v' hm').elim
            · exact ⟨x0, h1, h2⟩
          have hsz : true = true → SymZ G (σ[i]?.getD 0#64) (.var x) := fun _ => by
            rw [hσw]; exact hsymZ
          exact IH { st with slots := sl' } hvw hb (hA.setSlots (addSlotZEntry_ok ha
            (fun j se hj => ⟨hA.slots j se hj, hA.slots_lt j se hj⟩)
            ⟨rfl, hslotGpr⟩ hsz hs0 hislot))
        · exact finishPlain ha

theorem buildEntryBaseZ_ok {G : VCtx} {nv : Nat} {vw : Trie SlotWidth} {defs : Trie DefFact}
    {live : List (SymArg × T.toIsa.Loc)} {liveZ : List Bool} {st' : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)}
    (hb : buildEntryBaseZ T.toIsa hints.nslots vw live liveZ
      { regs := [], slots := .empty, defs := defs, vecWidths := vw } = some st')
    (hlive : ∀ p ∈ live, LocOk T.mach G s σ p.1 p.2)
    (hliveZ : LiveZOk T.mach G s σ live liveZ)
    (hlt : ∀ p ∈ live, symArgScopeOk nv p.1 = true) (hσ : σ.length = hints.nslots)
    (hA : Agree T G nv { regs := [], slots := .empty, defs := defs, vecWidths := vw } s σ) :
    Agree T G nv st' s σ :=
  buildEntryBaseZ_aux hσ live liveZ _ _ rfl hb hlive hliveZ hlt hA

private theorem bindBlockParamsZ_aux {s : T.mach.MData} {σ : List (BitVec 64)}
    (hσ : σ.length = hints.nslots) :
    ∀ (ts : List Ty) (xs : Tup Val ts) (ploc : List T.toIsa.Loc) (plocZ : List Bool)
      (G : VCtx) (nv : Nat) (st st' : SymState T.toIsa),
    bindBlockParamsZ T.toIsa hints.nslots ts ploc plocZ nv st = some st' →
    ParamsOk T.mach s σ ts xs ploc → ParamsZOk T.mach s σ ts xs ploc plocZ →
    Agree T G nv st s σ →
    Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ
  | [], _, [], _, G, nv, st, st', hb, _, _, hA => by
    simp only [bindBlockParamsZ, Option.some.injEq] at hb; subst hb; exact hA
  | [], _, _ :: _, _, _, _, _, _, hb, _, _, _
  | _ :: _, _, [], _, _, _, _, _, hb, _, _, _ => by
    simp [bindBlockParamsZ] at hb
  | t :: ts, (x, xs), loc :: locs, zs, G, nv, st, st', hb, ⟨hp0, hp'⟩, hpz, hA => by
    have hpz0 : zs.headD false = true → ParamZVal T.mach s σ t x loc := by
      cases zs with
      | nil => intro h; simp at h
      | cons z zs' => exact hpz.1
    have hpz' : ParamsZOk T.mach s σ ts xs locs zs.tail := by
      cases zs with
      | nil => cases ts <;> cases locs <;> trivial
      | cons _ _ => exact hpz.2
    have fin := fun st1 hb1 hA1 =>
      (bindBlockParamsZ_aux hσ ts xs locs zs.tail (⟨t, x, nv⟩ :: G) _ st1 st'
        hb1 hp' hpz' hA1).congrG
        (G' := Tup.zip (x, xs) (Tup.levels (t :: ts) nv) ++ G) (fun p => List.perm_middle.mem_iff)
        (show nv + 1 + ts.length = nv + (ts.length + 1) by omega)
    have hlt := hA.ctx_lt
    cases loc with
    | gpr r =>
      dsimp only [bindBlockParamsZ] at hb
      split at hb
      · rename_i hg
        have hg : r ∉ T.frame.scratch ∧ isGprTy T.toIsa t = true := by
          simpa [Bool.and_eq_true] using hg
        let zExt := if zs.headD false && tyEq t (.bits 32) then r :: killZeroExt [r] st.zeroExt32
                    else killZeroExt [r] st.zeroExt32
        have hfrK : T.mach.Frame T.gpr.condReads s s [r] [] FlagMask.none :=
          Machine.Frame.refl _ _ _ _ _
        have hzExt : ∀ q ∈ zExt,
            T.mach.getGpr s q = ((T.mach.getGpr s q).setWidth 32).setWidth 64 := by
          intro q hq; dsimp only [zExt] at hq
          split at hq
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            rcases List.mem_cons.mp hq with rfl | hq'
            · obtain rfl : t = .bits 32 := tyEq_iff.mp hcond.2
              have hab := hpz0 hcond.1
              rw [hab.2, setWidth_32_64_val]
            · exact zeroExt32_frame hA hfrK q hq'
          · exact zeroExt32_frame hA hfrK q hq
        have hreg : RegLocOk T.mach (⟨t, x, nv⟩ :: G) s (.var nv)
            (if zs.headD false then .gprZ r else .gpr r) := by
          by_cases hzh : zs.headD false = true
          · simp only [hzh, ↓reduceIte]
            exact ⟨fun t' v' hm => mem_head_cases hlt hm (fun t v => GprHolds (T.mach.getGpr s
              r) t v)
                hp0,
              fun t' v' hm => mem_head_cases hlt hm (fun t v => AbiGprHolds (T.mach.getGpr s r) t v)
                (hpz0 hzh)⟩
          · have hzf : zs.headD false = false := Bool.eq_false_iff.mpr hzh
            simp only [hzf, Bool.false_eq_true, ↓reduceIte]
            exact fun t' v' hm => mem_head_cases hlt hm (fun t v => GprHolds (T.mach.getGpr s
              r) t v)
              hp0
        exact fin _ hb ((hA.bindSame x (not_pair_of_isGprTy hg.2)).pushRegZ hreg
          (scope_nv nv) zExt hzExt)
      · simp at hb
    | vec v =>
      simp only [bindBlockParamsZ, Option.bind_eq_some_iff] at hb; obtain ⟨w, hw, hb⟩ := hb
      split at hb
      · exact fin _ hb ((hA.bindIns x hw).pushReg (rl := .vec v)
          (fun t' v' hm => mem_head_cases hlt hm
            (fun t0 v0 => t0.size ≤ SlotWidth.w512.bits ∧ VecHolds (T.mach.getVec s v) t0 v0)
            ⟨hp0.1, hp0⟩) (scope_nv nv))
      · simp at hb
    | flag c =>
      simp only [bindBlockParamsZ] at hb; split at hb
      · exact fin _ hb ((hA.bindSame x (by simp)).pushReg (rl := .flag c) (fun t' v' hm =>
          mem_head_cases hlt hm (fun t v => FlagHolds (T.mach.evalCond s c) t v) hp0) (scope_nv nv))
      · simp at hb
    | slot i w =>
      simp only [bindBlockParamsZ] at hb; split at hb; · simp at hb
      rename_i hg
      have hg : i + w.slots ≤ hints.nslots ∧
          (isGprTy T.toIsa t = false → ¬vecWidth? T.toIsa t = none) := by
        simpa using hg
      simp only [Option.bind_eq_some_iff] at hb; obtain ⟨sl', ha, hb⟩ := hb
      have hA1 : Agree T (⟨t, x, nv⟩ :: G) (nv + 1)
          { st with vecWidths := match vecWidth? T.toIsa t with
            | some wt => st.vecWidths.insert nv wt | none => st.vecWidths } s σ := by
        split
        · rename_i wt hwt; exact hA.bindIns x hwt
        · rename_i hwt; refine hA.bindSame x ?_
          cases hgt : isGprTy T.toIsa t
          · exact (hg.2 hgt hwt).elim
          · exact not_pair_of_isGprTy hgt
      have hislot : i + w.slots ≤ σ.length := by rw [hσ]; exact hg.1
      by_cases hz : (zs.headD false && (vecWidth? T.toIsa t).isNone && slotWidthEq w .w64) = true
      · simp only [hz, ↓reduceIte] at ha
        simp only [Bool.and_eq_true] at hz
        have hlocZ : ParamZVal T.mach s σ t x (.slot i w) := hpz0 hz.1.1
        obtain ⟨hw64, w0, hσw, hab⟩ := hlocZ
        subst hw64
        have hslotGpr : SlotOk (⟨t, x, nv⟩ :: G) σ i (.gpr [.var nv]) := by
          refine ⟨w0, hσw, fun sa hm => ?_⟩
          rw [List.mem_singleton] at hm; subst hm
          intro t' v' hm'
          exact mem_head_cases hlt hm' (fun t v => GprHolds w0 t v) hab.toGprHolds
        have hsz : true = true → SymZ (⟨t, x, nv⟩ :: G) (σ[i]?.getD 0#64) (.var nv) :=
          fun _ => by
            rw [hσw]; exact fun t' v' hm' =>
              mem_head_cases hlt hm' (fun t v => AbiGprHolds w0 t v) hab
        exact fin _ hb (hA1.setSlots (addSlotZEntry_ok ha
          (fun j se hj => ⟨hA1.slots j se hj, hA1.slots_lt j se hj⟩) ⟨rfl, hslotGpr⟩ hsz
          (scope_nv nv) hislot))
      · have hzf : (zs.headD false && (vecWidth? T.toIsa t).isNone && slotWidthEq w .w64) = false :=
          Bool.eq_false_iff.mpr hz
        simp only [hzf, Bool.false_eq_true, ↓reduceIte] at ha
        refine fin _ hb (hA1.setSlots (addSlotEntry_ok ha
          (fun j se hj => ⟨hA1.slots j se hj, hA1.slots_lt j se hj⟩) ?_ (scope_nv nv)
          (fun y wy hy t' v' hm => (hA1.vw y wy hy t' v' hm).2)
          (fun y hy t' v' hm => hA1.vt y t' v' hm hy) hislot))
        rcases hp0 with ⟨⟨bv, h1, h2, h3⟩, hpair⟩ | ⟨rfl, y, h1, h2⟩
        · refine Or.inl ⟨⟨bv, h1, fun sa hm => ?_⟩,
            fun t' v' hm => mem_head_cases hlt hm (fun t _ => ∃ a b, t = .pair a b) hpair⟩
          rw [List.mem_singleton] at hm; subst hm
          exact fun t' v' hm =>
            mem_head_cases hlt hm (fun t v => t.size ≤ w.bits ∧ VecHolds bv t v) ⟨h2, h3⟩
        · refine Or.inr ⟨rfl, y, h1, fun sa hm => ?_⟩
          rw [List.mem_singleton] at hm; subst hm
          exact fun t' v' hm => mem_head_cases hlt hm (fun t v => GprHolds y t v) h2

theorem bindBlockParamsZ_ok {G : VCtx} {nv : Nat} :
    ∀ {ts : List Ty} {xs : Tup Val ts} {ploc : List T.toIsa.Loc} {plocZ : List Bool}
      {st st' : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)},
    bindBlockParamsZ T.toIsa hints.nslots ts ploc plocZ nv st = some st' →
    ParamsOk T.mach s σ ts xs ploc → ParamsZOk T.mach s σ ts xs ploc plocZ →
    σ.length = hints.nslots → Agree T G nv st s σ →
    Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ :=
  fun hb hp hpz hσ hA => bindBlockParamsZ_aux hσ _ _ _ _ _ _ _ _ hb hp hpz hA

end Lemmas

/-! ## Structural Label-Cleanliness Helpers (`*_some`, `*_clean`) -/

section Clean
variable {I : Isa}

theorem tryArgPref_some {st : SymState I} {pref : List I.Cond} {preferReg : Bool} {α : Type}
    {t : Ty} {a : Arg VNat t} {k : PArg I.Reg I.VReg I.Cond t → Option α} {res : α}
    (h : tryArgPref I st pref preferReg t a k = some res) : ∃ pa, k pa = some res := by
  have fs : ∀ {β γ : Type} {l : List β} {g : β → Option α} {f : γ → PArg I.Reg I.VReg I.Cond t},
      (∀ b, g b = some res → ∃ x, k (f x) = some res) → l.findSome? g = some res →
      ∃ pa, k pa = some res := fun hg h => by
    obtain ⟨b, -, hb⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨x, hx⟩ := hg b hb; exact ⟨_, hx⟩
  have gpr : ∀ {sa}, tryGpr I st.regs sa (fun r => k (.gpr r)) = some res →
      ∃ pa, k pa = some res :=
    fs (f := PArg.gpr) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  have vec : ∀ {sa}, tryVec I st.regs sa (fun v => k (.vec v)) = some res →
      ∃ pa, k pa = some res :=
    fs (f := PArg.vec) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  cases t with
  | bool =>
    have flag : ∀ {sa}, tryFlag I st.regs pref sa (fun c => k (.flag c)) = some res →
        ∃ pa, k pa = some res := by
      intro sa h; rcases orElse_eq_some h with h | h
      · obtain ⟨c, -, hb⟩ := List.exists_of_findSome?_eq_some h
        split at hb <;> first | exact ⟨_, hb⟩ | simp at hb
      · exact fs (f := PArg.flag) (fun ⟨_, rl⟩ hb => by
          cases rl <;> simp only at hb <;> (try split at hb) <;>
            first | exact ⟨_, hb⟩ | simp at hb) h
    cases a with
    | var x => rcases orElse_eq_some h with h | h <;> first | exact flag h | exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact flag h
      rcases orElse_eq_some h with h | h <;> first | exact ⟨_, h⟩ | exact gpr h
  | bits w =>
    cases a with
    | var x => exact gpr h
    | imm b =>
      dsimp only [tryArgPref] at h
      split at h
      · rcases orElse_eq_some h with h | h <;> first | exact gpr h | exact ⟨_, h⟩
      · rcases orElse_eq_some h with h | h
        · exact ⟨_, h⟩
        · split at h <;> first | exact gpr h | simp at h
  | pair x y =>
    cases a with
    | var x => exact vec h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact vec h | simp at h
  | float _ => simp [tryArgPref] at h

theorem tryArg_some {st : SymState I} {pref : List I.Cond} {α : Type} {t : Ty} {a : Arg VNat t}
    {k : PArg I.Reg I.VReg I.Cond t → Option α} {res : α}
    (h : tryArg I st pref t a k = some res) : ∃ pa, k pa = some res :=
  tryArgPref_some h

theorem pickPArgsCode_some {st : SymState I} {pref : List I.Cond} {sig₀ rs₀ : List Ty}
    {code : OpCode sig₀ rs₀} {α : Type} :
    ∀ {sig : List Ty} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α} {res : α},
    pickPArgsCode I st pref code args k = some res → ∃ pas, k pas = some res
  | [], (), _, _, h => ⟨(), h⟩
  | _ :: _, (_, _), _, _, h => by
    obtain ⟨pa, h⟩ := tryArgPref_some h
    obtain ⟨pas, h⟩ := pickPArgsCode_some h
    exact ⟨_, h⟩

theorem pickPArgs_some {st : SymState I} {pref : List I.Cond} {α : Type} :
    ∀ {sig : List Ty} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α} {res : α},
    pickPArgs I st pref args k = some res → ∃ pas, k pas = some res
  | [], (), _, _, h => ⟨(), h⟩
  | _ :: _, (_, _), _, _, h => by
    obtain ⟨pa, h⟩ := tryArg_some h
    obtain ⟨pas, h⟩ := pickPArgs_some h
    exact ⟨_, h⟩

theorem tryAddr_some {st : SymState I} {vh : VariantHint} {α : Type} {a : Arg VNat i64}
    {k : AddrArg I.Reg → Option α} {res : α} (h : tryAddr I st vh a k = some res) :
    ∃ aa, k aa = some res := by
  cases a with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨_, h⟩
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
  | var x =>
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h <;> (try split at h) <;>
        first | (obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩) | simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
    rcases orElse_eq_some h with h | h
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · simp at h
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, h⟩
      · simp at h

theorem tryAddrZext_some {st : SymState I} {α : Type} {a : Arg VNat i64}
    {k : I.Reg → I.Reg → AddrScale → Int64 → Option α} {res : α}
    (h : tryAddrZext I st a k = some res) :
    ∃ rb ri sc disp, k rb ri sc disp = some res := by
  cases a with
  | imm _ => simp [tryAddrZext] at h
  | var x =>
    simp only [tryAddrZext] at h
    cases hdef : addrDefOf I.gpr.addrCse st.defs x with
    | none => simp [hdef] at h
    | some df =>
      cases df with
      | addrSum base idx sh d =>
        rw [hdef] at h; dsimp only at h
        cases hz : zextAddrSumVar? st.defs base idx sh with
        | none => simp [hz] at h
        | some _ =>
          rw [hz] at h; dsimp only at h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          exact ⟨_, _, _, _, h⟩
      | _ => simp [hdef] at h

theorem lowerLoadScr_clean (hcl : LabelClean I) {st : SymState I} {vh : VariantHint}
    {t : Ty} {d : I.Reg} {a : Arg VNat i64} {c : List I.Directive} {cl : FlagMask}
    {scrOut : List (I.Reg × BitVec 64)}
    (h : lowerLoadScr I st vh t d a = some (c, cl, scrOut)) : NoLab I c := by
  unfold lowerLoadScr at h
  rcases orElse_eq_some h with h1 | h
  · obtain ⟨fn, hfn, hta⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨aa, hk⟩ := tryAddr_some hta
    exact hcl.loadScr fn _ t d aa c cl scrOut hfn hk
  rcases orElse_eq_some h with h2 | h3
  · obtain ⟨fn, hfn, htz⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨rb, ri, sc, disp, hk⟩ := tryAddrZext_some htz
    exact hcl.loadZextIdxScr fn _ t d rb ri sc disp c cl scrOut hfn hk
  · obtain ⟨⟨c', cl'⟩, hta, heq⟩ := Option.map_eq_some_iff.mp h3
    cases heq
    rcases orElse_eq_some hta with hta | htz
    · obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.load _ _ _ _ _ hk
    · obtain ⟨_, _, _, _, hk⟩ := tryAddrZext_some htz; exact hcl.loadZextIdx _ _ _ _ _ _ _ _ hk

theorem lowerStoreScr_clean (hcl : LabelClean I) {st : SymState I} {vh : VariantHint}
    {t : Ty} {pa : PArg I.Reg I.VReg I.Cond t} {a : Arg VNat i64}
    {c : List I.Directive} {cl : FlagMask} {scrOut : List (I.Reg × BitVec 64)}
    (h : lowerStoreScr I st vh t pa a = some (c, cl, scrOut)) : NoLab I c := by
  unfold lowerStoreScr at h
  rcases orElse_eq_some h with h1 | h
  · obtain ⟨fn, hfn, hta⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨aa, hk⟩ := tryAddr_some hta
    exact hcl.storeScr fn _ t pa aa c cl scrOut hfn hk
  rcases orElse_eq_some h with h2 | h3
  · obtain ⟨fn, hfn, htz⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨rb, ri, sc, disp, hk⟩ := tryAddrZext_some htz
    exact hcl.storeZextIdxScr fn _ t pa rb ri sc disp c cl scrOut hfn hk
  · obtain ⟨⟨c', cl'⟩, hta, heq⟩ := Option.map_eq_some_iff.mp h3
    cases heq
    rcases orElse_eq_some hta with hta | htz
    · obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.store _ _ _ _ _ hk
    · obtain ⟨_, _, _, _, hk⟩ := tryAddrZext_some htz; exact hcl.storeZextIdx _ _ _ _ _ _ _ _ hk

theorem lowerOpScr_clean (hcl : LabelClean I) {st : SymState I} {vh : VariantHint}
    {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg I.Reg I.VReg I.Cond) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) rs}
    {c : List I.Directive} {cl : FlagMask} {scrOut : List (I.Reg × BitVec 64)}
    (h : lowerOpScr I st vh code pas dsts = some (c, cl, scrOut)) : NoLab I c := by
  unfold lowerOpScr at h
  split at h
  · obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
    cases he; exact hcl.op _ _ _ _ _ _ hop
  · cases hfn : I.gpr.opScr? with
    | some fn =>
      rw [hfn] at h; dsimp only at h; exact hcl.opScr fn _ code pas dsts vh c cl scrOut hfn h
    | none =>
      rw [hfn] at h; dsimp only at h
      obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
      cases he; exact hcl.op _ _ _ _ _ _ hop

theorem tryLoadTrunc_clean (hcl : LabelClean I) {st : SymState I} {vh : VariantHint}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    {isZ z32 : Bool} {scrOut : List (I.Reg × BitVec 64)}
    (h : tryLoadTrunc I st vh code args dsts = some (c, cl, isZ, z32, scrOut)) : NoLab I c := by
  cases code <;> try (simp [tryLoadTrunc] at h; done)
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
  cases a with
  | imm _ => simp [tryLoadTrunc] at h
  | var x =>
    cases d0 with
    | vec _ => simp [tryLoadTrunc] at h
    | gpr rd =>
      dsimp only [tryLoadTrunc] at h; split at h; · simp at h
      cases hmd : st.memDefs.find? x with
      | none => simp [hmd] at h
      | some p =>
        rcases p with ⟨tm, addr⟩
        cases tm with
        | bool | float _ | pair _ _ => simp [hmd] at h
        | bits _ =>
          simp only [hmd] at h
          split at h
          · obtain ⟨⟨c0, cl0, scr0⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
            exact lowerLoadScr_clean hcl hl
          · simp at h

theorem tryMulHi_clean (hcl : LabelClean I) {h : I.Hints} {st : SymState I} {nv : Nat}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {c : List I.Directive} {cl : FlagMask} {dhi : I.Reg}
    (hm : tryMulHi I h st nv code args = some (c, cl, dhi)) : NoLab I c := by
  cases hmh : I.gpr.mulHi? with
  | none => simp [tryMulHi, hmh] at hm
  | some fn =>
    cases code <;> try (simp [tryMulHi, hmh] at hm; done)
    all_goals
      rcases args with ⟨a, b, ⟨⟩⟩
      dsimp only [tryMulHi] at hm; rw [hmh] at hm; dsimp only at hm
      cases hd : h.dest.find? (nv + 1) <;> simp [hd] at hm
      rename_i loc; cases loc <;> simp at hm
      obtain ⟨_, hm⟩ := hm
      obtain ⟨pa, hka⟩ := tryArg_some hm
      obtain ⟨pb, hkb⟩ := tryArg_some hka
      obtain ⟨⟨c0, cl0⟩, hml, he⟩ := Option.map_eq_some_iff.mp hkb
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, he⟩; subst he
      exact hcl.mulHi fn _ _ pa pb _ c0 cl0 hmh hml

end Clean

end Rega
end LeanQbe.T
