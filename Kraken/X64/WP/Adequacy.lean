module

public import Kraken.X64.WP.Basic

namespace Kraken.Executable

private theorem getElem?_withAddresses_pair :
    ∀ (ds : List (Directive × Nat)) (a : Int64) (k : Nat),
      (Kraken.Executable.withAddresses (a, ds))[k]?
        = ds[k]?.map (fun dz => (a + .ofNat ((ds.take k).map (·.2)).sum, dz.1, dz.2))
  | [], a, k => by rw [Kraken.Executable.withAddresses]; simp
  | (d, z) :: ds, a, 0 => by
    rw [Kraken.Executable.withAddresses]
    simp
  | (d, z) :: ds, a, k + 1 => by
    rw [Kraken.Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_pair ds _ k,
      List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

private theorem getElem?_withAddresses (e : Kraken.Executable Directive) (k : Nat) (hk : k < e.2.length) :
    e.withAddresses[k]?.map (·.1) = some (e.addrOf k) := by
  show (Kraken.Executable.withAddresses (e.1, e.2))[k]?.map (·.1) = some (e.addrOf k)
  rw [getElem?_withAddresses_pair]
  obtain ⟨dz, hdz⟩ : ∃ dz, e.2[k]? = some dz :=
    ⟨_, List.getElem?_eq_getElem hk⟩
  rw [hdz]
  simp [addrOf, sizeBefore]

private theorem dropWhile_eq_drop_of {α} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  induction l generalizing j with
  | nil => simp
  | cons x xs ih =>
    cases j with
    | zero =>
      have hx := hhead x rfl
      rw [List.dropWhile_cons, ite_eq_right (by simp [hx]), List.drop_zero]
    | succ m =>
      have hx := hprior 0 (Nat.succ_pos m) x rfl
      rw [List.dropWhile_cons, ite_eq_left (by simp [hx]), List.drop_succ_cons]
      exact ih (fun k hk c hc => hprior (k+1) (by omega) c (by simpa using hc))
        (fun c hc => hhead c (by simpa using hc))

private theorem getElem?_withAddresses_eq (e : Kraken.Executable Directive) (k : Nat) :
    (Kraken.Executable.withAddresses (e.1, e.2))[k]? = e.2[k]?.map (fun dz => (e.addrOf k, dz)) := by
  rw [getElem?_withAddresses_pair]
  rfl

private theorem takeWhile_eq_take_of {α} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp [hhead x rfl]
    | succ m =>
      rw [List.takeWhile_cons_of_pos (hprior 0 (Nat.succ_pos m) x rfl), List.take_succ_cons,
        ih (n := m) (fun k hk c hc => hprior (k+1) (by omega) c (by simpa using hc))
          (fun c hc => hhead c (by simpa using hc))]

private theorem withAddresses_dropWhile_addrOf (e : Kraken.Executable Directive) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ e.addrOf n)
      = (Kraken.Executable.withAddresses (e.1, e.2)).drop j := by
  have hlen : (Kraken.Executable.withAddresses (e.1, e.2)).length = e.2.length := by
    conv => lhs; rw [show (Kraken.Executable.withAddresses (e.1, e.2)).length
      = ((Kraken.Executable.withAddresses (e.1, e.2)).map (·.2)).length by simp]
    rw [withAddresses_map_snd e.2 e.1]
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    have hklt : k < e.2.length := by
      have hbound : k < (Kraken.Executable.withAddresses (e.1, e.2)).length := by
        by_cases h : k < (Kraken.Executable.withAddresses (e.1, e.2)).length
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hc; cases hc
      omega
    have := getElem?_withAddresses e k hklt
    rw [hc] at this
    simp only [Option.map_some, Option.some.injEq] at this
    have hne : c.1 ≠ e.addrOf n := this ▸ hfresh k hk
    simpa using hne
  · intro c hc
    have hjlt : j < e.2.length := by
      have hbound : j < (Kraken.Executable.withAddresses (e.1, e.2)).length := by
        by_cases h : j < (Kraken.Executable.withAddresses (e.1, e.2)).length
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hc; cases hc
      omega
    have := getElem?_withAddresses e j hjlt
    rw [hc] at this
    simp only [Option.map_some, Option.some.injEq] at this
    have heq : c.1 = e.addrOf n := this ▸ hj
    simpa using heq

private theorem findSome?_eq_of {α β} {f : α → Option β} {l : List α} :
    ∀ {n : Nat} {b : β}, l[n]?.bind f = some b →
      (∀ k, k < n → l[k]?.bind f = none) → l.findSome? f = some b := by
  induction l with
  | nil => intro n b hn _; simp at hn
  | cons x xs ih =>
    intro n b hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.bind_some] at hn
      simp [hn]
    | succ m =>
      have h0 : f x = none := by simpa using hlt 0 (Nat.succ_pos m)
      rw [List.findSome?_cons, h0,
        ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]

public theorem label_addrOf (e : Kraken.Executable Directive) (l : Label) (n : Nat)
    (hn : e.2[n]? = some (.label l, 0))
    (hfirst : ∀ dz ∈ e.2.take n, dz.1 ≠ Directive.label l) :
    (_root_.Executable.labels e).label l = e.addrOf n := by
  replace hfirst : ∀ k, k < n → e.2[k]?.map (·.1) ≠ some (Directive.label l) := by
    intro k hk hcontra
    obtain ⟨dz, hdz⟩ : ∃ dz, e.2[k]? = some dz := by
      rcases h : e.2[k]? with _ | dz
      · rw [h] at hcontra; simp at hcontra
      · exact ⟨dz, rfl⟩
    rw [hdz] at hcontra
    refine hfirst dz (List.mem_iff_getElem?.mpr ⟨k, ?_⟩) (by simpa using hcontra)
    rw [List.getElem?_take_of_lt hk, hdz]
  have hstep : e.1 + .ofNat ((e.2.take (n + 1)).map (·.2)).sum = e.addrOf n := by
    unfold addrOf sizeBefore
    rw [List.take_add_one, hn]
    simp
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n) ?hit ?miss]
  · exact rfl
  case hit =>
    show ((Kraken.Executable.withAddresses (e.1, e.2))[n]?.bind _) = some (e.addrOf n)
    rw [getElem?_withAddresses_pair, hn]
    show some (e.addrOf n, Directive.label l, 0) >>= _ = some (e.addrOf n)
    simp
  case miss =>
    intro k hk
    show ((Kraken.Executable.withAddresses (e.1, e.2))[k]?.bind _) = none
    rw [getElem?_withAddresses_pair]
    rcases hm : e.2[k]? with _ | ⟨d, z⟩
    · simp
    · have hd : d ≠ .label l := by
        have := hfirst k hk
        rw [hm] at this
        simpa using this
      simp [hd]

public theorem _root_.Nat.exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hb
      obtain ⟨j, hj, hPj, hmin⟩ := ih m hm hPm
      exact ⟨j, by omega, hPj, hmin⟩
    · exact ⟨n, Nat.le_refl n, h, fun k hk hPk => hb ⟨k, hk, hPk⟩⟩

end Kraken.Executable

public theorem Directives.interp_inert_append [Labels] {pre rest : List (Directive × Nat)}
    (hpre : ∀ c ∈ pre, c.2 = 0 ∧ c.1.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc))

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Layout.length_apply [layout : Layout] (p : Program) : (layout p).2.length = p.length := by
  simp [Kraken.Layout.apply]

section
variable [Host] [layout : Layout] [hv : Layout.Valid]

private theorem Host.inert_of_cell {m : Nat} {d : Directive}
    (h : (layout Host.prog).2[m]? = some (d, 0)) : d.Inert := by
  rw [Layout.apply_getElem?] at h
  obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hz⟩ := heq
  exact hv.zero_inert m d' hd' hz

private theorem Host.zero_between {j m n : Nat} (hjm : j ≤ m) (hmn : m < n) (hn : n ≤ Host.prog.length)
    (heq : (layout Host.prog).addrOf j = (layout Host.prog).addrOf n) :
    ∃ d, (layout Host.prog).2[m]? = some (d, 0) := by
  refine ⟨Host.prog[m], ?_⟩
  rw [Layout.apply_getElem?, List.getElem?_eq_getElem (by omega), hv.fits j n m hjm hmn hn heq]
  rfl

private theorem Host.inert_between {j j' : Nat}
    (hzero : ∀ m, j ≤ m → m < j' → ∃ d, (layout Host.prog).2[m]? = some (d, 0)) :
    ∀ c ∈ ((layout Host.prog).2.drop j).take (j' - j), c.2 = 0 ∧ c.1.Inert := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have := hzero (j + m) (by grind) (by grind)
  grind [Host.inert_of_cell]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {d : Directive} {z : Nat}
    (hd : (layout Host.prog).2[k]? = some (d, z)) (hz : 0 < z) :
    ∃ pre, (layout Host.prog).directivesAtAddress ((layout Host.prog).addrOf k) = pre ++ [(d, z)] ∧
      ∀ c ∈ pre, c.2 = 0 ∧ c.1.Inert := by
  have hk : k < Host.prog.length := by
    rw [← Layout.length_apply]; exact (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨j, hjk, hj, hmin⟩ :=
    Nat.exists_least_le (P := fun i => (layout Host.prog).addrOf i = (layout Host.prog).addrOf k) rfl
  have hzero : ∀ m, j ≤ m → m < k → ∃ d, (layout Host.prog).2[m]? = some (d, 0) :=
    fun m hjm hmk => Host.zero_between hjm hmk (Nat.le_of_lt hk) hj
  have haddr' : ∀ i, j + i ≤ k → (layout Host.prog).addrOf (j + i) = (layout Host.prog).addrOf k := by
    intro i
    induction i with
    | zero => exact fun _ => hj
    | succ i ih =>
      intro hik
      obtain ⟨d', hd'⟩ := hzero (j + i) (by omega) (by omega)
      rw [← Nat.add_assoc, Kraken.Executable.addrOf_succ _ hd', ih (by omega)]
      simp
  have haddr : ∀ m, j ≤ m → m ≤ k → (layout Host.prog).addrOf m = (layout Host.prog).addrOf k :=
    fun m hjm hmk => by simpa [Nat.add_sub_cancel' hjm] using haddr' (m - j) (by omega)
  have hnext : (layout Host.prog).addrOf (k + 1) ≠ (layout Host.prog).addrOf k := by
    intro h
    have hsz := hv.fits k (k + 1) k (Nat.le_refl _) (Nat.lt_succ_self _) (by omega) h.symm
    have hd' := hd
    rw [Layout.apply_getElem?] at hd'
    obtain ⟨d', -, heq⟩ := Option.map_eq_some_iff.mp hd'
    simp only [Prod.mk.injEq] at heq
    omega
  refine ⟨((layout Host.prog).2.drop j).take (k - j), ?_, Host.inert_between hzero⟩
  show (((Kraken.Executable.withAddresses ((layout Host.prog).1, (layout Host.prog).2)).dropWhile
    (·.1 ≠ (layout Host.prog).addrOf k)).takeWhile (·.1 = (layout Host.prog).addrOf k)).map (·.2) = _
  rw [Kraken.Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    Kraken.Executable.takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Kraken.Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hd]
    rfl
  · intro m hm c hc
    rw [List.getElem?_drop, Kraken.Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using haddr (j + m) (by omega) (by omega)
  · intro c hc
    rw [List.getElem?_drop, Kraken.Executable.getElem?_withAddresses_eq,
      show j + (k - j + 1) = k + 1 by omega] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hnext

public theorem Host.fetch?_addrOf {k : Nat} {d : Directive} {z : Nat}
    (hd : (layout Host.prog).2[k]? = some (d, z)) (hz : 0 < z) :
    (layout Host.prog).fetch? ((layout Host.prog).addrOf k) = some (d, z) := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
  unfold Kraken.Executable.fetch?
  rw [hat, List.find?_append, List.find?_eq_none.mpr fun c hc => by simp [(hpre c hc).1]]
  simp [hz]

public theorem Host.eventually_directive {k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt Host.prog k) {B : MachineState → Prop} {s : MachineData}
    (h : (d.interp s ⟨(layout Host.prog).addrOf k, (layout Host.prog).addrOf (k + 1)⟩
      (fun s' => .done (s', (layout Host.prog).addrOf (k + 1))) (fun a s' => .done (s', a))).All B) :
    Eventually Host.step B (s, (layout Host.prog).addrOf k) := by
  have hd : (layout Host.prog).2[k]? = some (d, Kraken.Layout.size Directive k) := by
    rw [Layout.apply_getElem?, hdp.cons.1]
    rfl
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive k) with h0 | hz
  · rw [h0] at hd
    rw [Host.inert_of_cell hd, Kraken.Executable.addrOf_succ _ hd] at h
    have h0' : (layout Host.prog).addrOf k + Int64.ofNat 0 = (layout Host.prog).addrOf k := by simp
    simp only [Effects.All, h0'] at h
    exact Eventually.done _ h
  · refine Eventually.step _ B ?_ fun _ hb => Eventually.done _ hb
    unfold Host.step
    rw [Host.fetch?_addrOf hd hz]
    dsimp only
    rw [← Kraken.Executable.addrOf_succ _ hd]
    exact h

public theorem Host.step1_of_step {st : MachineState} {P : MachineState → Prop}
    (h : Host.step st P) : step1 (layout Host.prog) st P := by
  obtain ⟨s, a⟩ := st
  unfold Host.step at h
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
  dsimp only
  rw [hat, Directives.interp_inert_append hpre]
  exact h

public theorem Host.eventually_step1 {st : MachineState} {P : MachineState → Prop}
    (h : Eventually Host.step P st) : Eventually (step1 (layout Host.prog)) P st := by
  induction h with
  | done st hp => exact Eventually.done _ hp
  | step st Q hstep _ ih => exact Eventually.step _ Q (Host.step1_of_step hstep) ih

public theorem Host.label_eq {p : Program} {k i : Nat} {l : Label}
    (hp : p.IsInfixAt Host.prog k) (hi : p[i]? = some (.label l)) :
    label l = (layout Host.prog).addrOf (k + i) := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  have hP : Host.prog[k + i]? = some (.label l) := by
    rw [List.isInfixAt_iff_getElem?.mp hp i hlt, hpi]
  have hcell : (layout Host.prog).2[k + i]? = some (.label l, 0) := by
    rw [Layout.apply_getElem?, hP, hv.label_size _ l hP]
    rfl
  refine Kraken.Executable.label_addrOf (layout Host.prog) l (k + i) hcell ?_
  intro dz hdz heq
  obtain ⟨m, hm, hmdz⟩ := List.getElem_of_mem hdz
  rw [List.length_take] at hm
  have h1 : (layout Host.prog).2[m]? = some dz := by
    rw [List.getElem?_eq_getElem (by omega), ← hmdz, List.getElem_take]
  rw [Layout.apply_getElem?] at h1
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h1
  dsimp only at heq
  subst heq
  exact absurd (Program.eq_of_getElem?_label Host.labels_nodup hd' hP) (by omega)

end

public def Host.startAddr [Host] [layout : Layout] {p : Program} (h : p <:+: Host.prog) : Int64 :=
  (layout Host.prog).addrOf (p.infixIdx Host.prog h)

export Host (startAddr)

public theorem Program.step1_of_wp [Host] [layout : Layout] [Layout.Valid] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : MachineState → Prop} (h : p <:+: Host.prog) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → ∀ pc, post (s', pc)) (hE : ∀ a s', E a s' → post (s', a)) :
    Eventually (step1 (layout Host.prog)) post (s, startAddr h) := by
  refine eventually_weaken _ _ _ _ ?_ (Host.eventually_step1 (hwp _ (List.isInfixAt_infixIdx h)))
  rintro ⟨s', a⟩ (⟨-, hq⟩ | he)
  · exact hQ s' hq a
  · exact hE a s' he
