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

public theorem directivesFromAddress_addrOf_first (e : Kraken.Executable Directive) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop j := by
  show ((Kraken.Executable.withAddresses (e.1, e.2)).dropWhile
      (·.1 ≠ e.addrOf n)).map (·.2) = e.2.drop j
  have hlen : (Kraken.Executable.withAddresses (e.1, e.2)).length = e.2.length := by
    conv => lhs; rw [show (Kraken.Executable.withAddresses (e.1, e.2)).length
      = ((Kraken.Executable.withAddresses (e.1, e.2)).map (·.2)).length by simp]
    rw [withAddresses_map_snd e.2 e.1]
  have hdw : (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ e.addrOf n)
      = (Kraken.Executable.withAddresses (e.1, e.2)).drop j := by
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
  rw [hdw, List.map_drop, withAddresses_map_snd e.2 e.1]

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

public def _root_.Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s p (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
    d.interp s p next jmp = next s

public class Assembled (e : Kraken.Executable Directive) : Prop where
  label_size : ∀ (i : Nat) l z, e.2[i]? = some (Directive.label l, z) → z = 0
  zero_inert : ∀ (i : Nat) d, e.2[i]? = some (d, 0) → d.Inert
  no_wrap : (e.2.map (·.2)).sum < 2 ^ 64
  labels_unique : ∀ (i j : Nat) l z z', e.2[i]? = some (Directive.label l, z) →
    e.2[j]? = some (Directive.label l, z') → i = j

private theorem sum_map_take_mono {α} (f : α → Nat) (l : List α) {k n : Nat} (h : k ≤ n) :
    ((l.take k).map f).sum ≤ ((l.take n).map f).sum := by
  grind [List.take_append_drop]
grind_pattern sum_map_take_mono => ((l.take k).map f).sum, ((l.take n).map f).sum

public theorem sizeBefore_eq_of_addrOf_eq (e : Kraken.Executable Directive) [hv : Assembled e] {k n : Nat}
    (heq : e.addrOf k = e.addrOf n) : e.sizeBefore k = e.sizeBefore n := by
  have : e.sizeBefore k ≤ (e.2.map (·.2)).sum := by grind [sizeBefore, List.take_append_drop]
  have : e.sizeBefore n ≤ (e.2.map (·.2)).sum := by grind [sizeBefore, List.take_append_drop]
  have := hv.no_wrap
  grind [addrOf]

public theorem _root_.Nat.exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hb
      obtain ⟨j, hj, hPj, hmin⟩ := ih m hm hPm
      exact ⟨j, by omega, hPj, hmin⟩
    · exact ⟨n, Nat.le_refl n, h, fun k hk hPk => hb ⟨k, hk, hPk⟩⟩

public theorem zero_between_of_addrOf_eq (e : Kraken.Executable Directive) [hv : Assembled e]
    {j k n : Nat} (hjk : j ≤ k) (hkn : k < n) (hn : n ≤ e.2.length)
    (heq : e.addrOf j = e.addrOf n) :
    ∃ d, e.2[k]? = some (d, 0) := by
  obtain ⟨⟨d, z⟩, hdz⟩ : ∃ dz, e.2[k]? = some dz := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have := sizeBefore_eq_of_addrOf_eq e heq
  have : e.sizeBefore (k + 1) ≤ e.sizeBefore n := by grind [sizeBefore]
  exact ⟨d, by grind [sizeBefore, List.take_add_one]⟩

public theorem exists_cut (e : Kraken.Executable Directive) [Assembled e] {n : Nat} (hn : n ≤ e.2.length) :
    ∃ j, j ≤ n ∧ e.directivesFromAddress (e.addrOf n) = e.2.drop j
      ∧ ∀ m, j ≤ m → m < n → ∃ d, e.2[m]? = some (d, 0) := by
  obtain ⟨j, hjn, hj, hmin⟩ :=
    Nat.exists_least_le (P := fun k => e.addrOf k = e.addrOf n) rfl
  exact ⟨j, hjn, directivesFromAddress_addrOf_first e j n hj hmin,
    fun m hjm hmn => zero_between_of_addrOf_eq e hjm hmn hn hj⟩

end Kraken.Executable

public theorem straightlineStep_eq_interp [Layout] (e : Executable) (st : MachineState)
    (post : MachineState → Prop) :
    straightlineStep e st post
      = (@Directives.interp (Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2
          fun pc s => .done (s, pc)).All post := by
  unfold straightlineStep Executable.straightline
  rfl

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

public theorem Executable.inert_between (e : Executable) [hv : Kraken.Executable.Assembled e]
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' ≤ e.2.length)
    (hzero : ∀ m, j ≤ m → m < j' → ∃ d, e.2[m]? = some (d, 0)) :
    ∀ c ∈ (e.2.drop j).take (j' - j), c.2 = 0 ∧ c.1.Inert := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have := hzero (j + m) (by grind) (by grind)
  grind [hv.zero_inert]

public theorem Executable.drop_split (e : Executable) {j j' : Nat} (hjj : j ≤ j') :
    e.2.drop j = (e.2.drop j).take (j' - j) ++ e.2.drop j' := by
  conv => lhs; rw [← List.take_append_drop (j' - j) (e.2.drop j)]
  rw [List.drop_drop, show j + (j' - j) = j' by omega]

public theorem LinkedProgram.eventually_straightlineStep [Layout] {e : Executable}
    [hv : Kraken.Executable.Assembled e] {B post : MachineState → Prop}
    (hB : ∀ st, B st → st.2 = e.addrOf e.2.length ∧ ∀ pc, post (st.1, pc))
    {st : MachineState} (h : @Eventually _ (@LinkedProgram.step ⟨e⟩) B st) :
    Eventually (straightlineStep e) post st := by
  letI : Labels := Executable.labels e
  let G := Eventually (straightlineStep e) post
  let Burst := fun (j : Nat) (s : MachineData) =>
    (Directives.interp (e.2.drop j) s (e.addrOf j) fun pc s => .done (s, pc)).All G
  have hsame : ∀ j j' s, j ≤ j' → j' ≤ e.2.length → e.addrOf j = e.addrOf j' →
      Burst j s = Burst j' s := by
    intro j j' s hjj hj' heq
    show (Directives.interp _ _ _ _).All G = (Directives.interp _ _ _ _).All G
    rw [Executable.drop_split e hjj, Directives.interp_inert_append
      (Executable.inert_between e hjj hj' fun m hjm hmj' =>
        Kraken.Executable.zero_between_of_addrOf_eq e hjm hmj' hj' heq), heq]
  have hplaced : ∀ j s, j ≤ e.2.length → Burst j s → G (s, e.addrOf j) := by
    intro j s hj hb
    refine Eventually.step _ _ ?_ fun _ h => h
    obtain ⟨j₀, hj₀, hdir, hzero⟩ := Kraken.Executable.exists_cut e hj
    rw [straightlineStep_eq_interp]
    dsimp only
    rw [hdir, Executable.drop_split e hj₀,
      Directives.interp_inert_append (Executable.inert_between e hj₀ hj hzero)]
    exact hb
  have key : ∀ st, @Eventually _ (@LinkedProgram.step ⟨e⟩) B st →
      G st ∧ ∀ j, j ≤ e.2.length → st.2 = e.addrOf j → Burst j st.1 := by
    intro st h
    induction h with
    | done st hb =>
      obtain ⟨s, a⟩ := st
      obtain ⟨hend, hpost⟩ := hB _ hb
      dsimp only at hend hpost
      refine ⟨Eventually.done _ (hpost a), fun j hj hja => ?_⟩
      dsimp only at hja
      show Burst j s
      rw [hsame j e.2.length s hj (Nat.le_refl _) (hja.symm.trans hend)]
      show (Directives.interp (e.2.drop e.2.length) _ _ _).All G
      rw [List.drop_length]
      exact Eventually.done _ (hpost _)
    | step st P hstep _ ih =>
      obtain ⟨j₀, d, z, hcell, hst, hall⟩ := hstep
      obtain ⟨s, a⟩ := st
      dsimp only at hst hall ⊢
      subst hst
      replace hcell : e.2[j₀]? = some (d, z) := hcell
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hcell
      have hb0 : Burst j₀ s := by
        show (Directives.interp (e.2.drop j₀) s (e.addrOf j₀) _).All G
        rw [List.drop_eq_getElem_cons hlt, hget]
        simp only [Directives.interp]
        rw [← Kraken.Executable.addrOf_succ _ hcell]
        exact hall G _ _ (fun s' hp => (ih _ hp).2 (j₀ + 1) hlt rfl)
          (fun a' s' hp => (ih _ hp).1)
      refine ⟨hplaced j₀ s (Nat.le_of_lt hlt) hb0, fun j hj hja => ?_⟩
      rcases Nat.le_total j j₀ with hle | hle
      · rw [hsame j j₀ s hle (Nat.le_of_lt hlt) hja.symm]
        exact hb0
      · rw [← hsame j₀ j s hle hj hja]
        exact hb0
  exact (key st h).1

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Layout.text {layout : Layout} {p : Program} : (layout p).2.map (·.1) = p :=
  List.ext_getElem (by simp [Kraken.Layout.apply]) (by simp [Kraken.Layout.apply])

public theorem Program.linkedAt_layout [layout : Layout] {p : Program}
    [hv : Kraken.Executable.Assembled (layout p)] :
    @Program.LinkedAt ⟨layout p⟩ p 0 := by
  refine ⟨?_, fun i l hi => ?_⟩
  · show p <+: ((layout p).2.map (·.1)).drop 0
    rw [Layout.text, List.drop_zero]
    exact List.prefix_refl _
  · show (Executable.labels (layout p)).label l = (layout p).addrOf (0 + i)
    rw [Nat.zero_add]
    have hlay : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
      rw [Layout.apply_getElem?, hi]; rfl
    refine Kraken.Executable.label_addrOf (layout p) l i ?_ ?_
    · rw [hlay, hv.label_size i l _ hlay]
    · intro dz hdz heq
      obtain ⟨k, hk, hkdz⟩ := List.getElem_of_mem hdz
      rw [List.length_take] at hk
      have hcell : (layout p).2[k]? = some (Directive.label l, dz.2) := by
        rw [← heq, List.getElem?_eq_getElem (by omega), ← hkdz, List.getElem_take]
      exact absurd (hv.labels_unique k i l _ _ hcell hlay) (by omega)

public theorem Program.straightline_of_wp [layout : Layout] {p : Program}
    [Kraken.Executable.Assembled (layout p)] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : MachineState → Prop} (h : @Program.wp ⟨layout p⟩ p Q E s)
    (hQ : ∀ s', Q s' → ∀ pc, post (s', pc)) (hE : ∀ a s', ¬ E a s') :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  have := LinkedProgram.eventually_straightlineStep (e := layout p) (post := post) ?_
    (h 0 Program.linkedAt_layout)
  · change Eventually _ _ (s, (layout p).addrOf 0) at this
    rwa [Kraken.Executable.addrOf_zero] at this
  · rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
    · refine ⟨?_, hQ s' hq⟩
      rw [ha, Nat.zero_add]
      congr 1
      simp [Kraken.Layout.apply]
    · exact absurd he (hE _ _)
