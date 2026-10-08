module

public import Kraken.X64.WP.Basic

section
variable [Host] [Layout] [hv : Layout.Valid]

public theorem Host.step1_of_step {st : MachineState} {post : @Post MachineState}
    (h : Host.exe.step' st post) : step1 Host.exe st post := by
  obtain ⟨s, a⟩ := st
  unfold Kraken.Executable.step' at h
  split at h
  · exact h.elim
  rename_i d z hinstr
  have hz : 0 < z := by simpa using List.find?_some hinstr
  obtain ⟨k, hdz, rfl⟩ : ∃ k, Host.exe.2[k]? = some (d, z) ∧ a = Host.exe.addrOf k := by
    obtain ⟨x, hx, hxdz⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hinstr)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      ((List.dropWhile_sublist _).subset (List.takeWhile_sublist _ |>.subset hx))
    have := List.all_eq_true.mp List.all_takeWhile x hx
    grind [Kraken.Executable.getElem?_withAddresses_eq]
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hdz hz
  unfold step1 Executable.step
  change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _).All post
  rw [hat, Directives.interp_inert_append hpre]
  exact h

public theorem Host.eventually_step1 {st : MachineState} {post : @Post MachineState}
    (h : Eventually Host.exe.step' post st) : Eventually (step1 Host.exe) post st := by
  induction h with
  | done st hp => exact Eventually.done _ hp
  | step st Q hstep _ ih => exact Eventually.step _ Q (Host.step1_of_step hstep) ih

end

public theorem Program.step1_of_wp_at [Host] [Layout] [Layout.Valid] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} {k : Nat} (hk : p.IsInfixAt Host.prog k) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post (s', Host.addrOf (k + p.length))) (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (step1 Host.exe) post (s, Host.addrOf k) := by
  refine eventually_weaken _ _ _ _ ?_ (Host.eventually_step1 (hwp k hk))
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha
    rw [ha]
    exact hQ s' hq
  · exact hE a s' he

public theorem Program.step1_of_wp [Host] [Layout] [Layout.Valid] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} (h : p.IsInfix Host.prog) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post (s', endAddr h)) (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (step1 Host.exe) post (s, startAddr h) :=
  Program.step1_of_wp_at (List.isInfixAt_infixIdx h) hwp hQ hE
