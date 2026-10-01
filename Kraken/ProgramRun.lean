module

/- The run of a program fragment in the baseline interpreter. -/
public import Kraken.X64.OmniSemantics

@[expose] public section

def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- In every burst that runs `q` from `s` and continues with `rest`, `q` falls through
with `Q` or exits with `E` at the address it jumps to. -/
def Program.run [Labels] (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    (∀ s', Q s' →
      (Directives.interp rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (Directives.interp (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

theorem Program.run_straightlineStep [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {post : MachineState → Prop}
    (h : @Program.run (Executable.labels (layout p)) p Q E s)
    (hQ : ∀ st', Q st'.1 → post st') (hE : ∀ a s', E a s' → post (s', a)) :
    straightlineStep (layout p) (s, layout.start) post := by
  show (@Directives.interp (Executable.labels (layout p)) ((layout p).directivesFromAddress
    layout.start) s layout.start fun pc s => .done (s, pc)).All _
  rw [Kraken.Executable.directivesFromStart, ← List.append_nil (p.mapIdx _)]
  exact h _ [] layout.start _ (List.ext_getElem (by simp) (by simp))
    (fun s' hq => hQ (s', _) hq) hE

/- With a `Directives.interp` that returns its final state as
`Effects MachineState` instead of passing it to `ret`, the run would be the
burst's `.All` of the post, without the continuation `rest` and the post `Φ`:
`(Directives.interp ds s pc).All fun st => (st.2 = endPc pc sizes ∧ Q st.1) ∨ E st.2 st.1`.
`Program.run_cons` would then be the bind law of `Effects.All`, and the lemma
above the instance `ds := (layout p).2`. -/

theorem Program.run_mono [Labels] {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun ds rest pc Φ hds hQ₂ hE₂ =>
    h ds rest pc Φ hds (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

theorem Program.run_cons [Labels] {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro ds rest pc Φ hds hQ hE
  match ds, hds with
  | (d', z) :: ds', hds =>
    obtain ⟨rfl, hq⟩ := List.cons.inj hds
    exact h [(d', z)] (ds' ++ rest) pc Φ rfl
      (fun s' hrun => hrun ds' rest (pc + Int64.ofNat z) Φ hq hQ hE) hE
