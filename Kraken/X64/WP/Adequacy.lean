module

public import Kraken.X64.WP.Basic

section
variable [Host] [Layout] [hv : Layout.Valid]

public theorem Host.step1_of_step {st : MachineState} {P : MachineState → Prop}
    (h : Host.exe.step' st P) : step1 Host.exe st P := by
  obtain ⟨s, a⟩ := st
  unfold Kraken.Executable.step' at h
  split at h
  · exact h.elim
  rename_i d z hinstr
  have hmem := List.mem_of_find?_eq_some hinstr
  have hz : 0 < z := by simpa using List.find?_some hinstr
  obtain ⟨x, hx, hxdz⟩ := List.mem_map.mp hmem
  have hxa : x.1 = a := by simpa using List.all_eq_true.mp List.all_takeWhile x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    ((List.dropWhile_sublist _).subset (List.takeWhile_sublist _ |>.subset hx))
  rw [Kraken.Executable.getElem?_withAddresses_eq] at hk
  obtain ⟨dz, hdz, rfl⟩ := Option.map_eq_some_iff.mp hk
  dsimp only at hxa hxdz
  subst hxa hxdz
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hdz hz
  unfold step1 Executable.step
  change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _).All P
  rw [hat, Directives.interp_inert_append hpre]
  exact h

public theorem Host.eventually_step1 {st : MachineState} {P : MachineState → Prop}
    (h : Eventually Host.exe.step' P st) : Eventually (step1 Host.exe) P st := by
  induction h with
  | done st hp => exact Eventually.done _ hp
  | step st Q hstep _ ih => exact Eventually.step _ Q (Host.step1_of_step hstep) ih

end

public theorem Program.step1_of_wp [Host] [Layout] [Layout.Valid] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : MachineState → Prop} (h : p.IsInfix Host.prog) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post (s', endAddr h)) (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (step1 Host.exe) post (s, startAddr h) := by
  refine eventually_weaken _ _ _ _ ?_ (Host.eventually_step1 (hwp _ (List.isInfixAt_infixIdx h)))
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha
    rw [ha]
    exact hQ s' hq
  · exact hE a s' he
