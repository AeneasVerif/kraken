module

public import LeanQbe.T.LinkRec
public import LeanQbe.T.Scc

/-!
# Well-Founded Index-Parameterized SCC Module Linking (`R-B`)

Generalizes `LinkRec` from `Nat` fuel to an arbitrary well-founded index `(ι, lt, wf, depth)`
(`RecIdx ι`):
* `RecIdx`, `natRecIdx`, `lexNatRecIdx`: well-founded termination index paired with stack depth.
* `Env.stepIdx`: index-stepped recursive environment with `strict : Bool` (`strict = (step ≠ 0)`),
  requiring `idx.lt i' i` and (`strict = false ∨ idx.depth i' < idx.depth i`).
  Includes the marked comment hook for `F-A`'s call/tail-slot split (`link_scc_compiled_split`).
* `Env.ofModuleScc`, `Env.ofModuleSccAt`, `Env.exportScc`, `envOfIdxSpec`, and `ModuleSccOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LinkScc

open LeanQbe.T

/-- Well-founded termination index `ι` paired with a stack-depth projection `depth : ι → Nat`. -/
structure RecIdx (ι : Type) where
  lt : ι → ι → Prop
  wf : WellFounded lt
  depth : ι → Nat

/-- Canonical `Nat` recursion index recovering `LinkRec` (`lt := (· < ·)`, `depth := id`). -/
def natRecIdx : RecIdx Nat where
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  depth := id

/-- Lexicographic `Nat × Nat` recursion index with a caller-supplied stack-depth projection. -/
def lexNatRecIdx (depth : Nat × Nat → Nat) : RecIdx (Nat × Nat) where
  lt := Prod.Lex (· < ·) (· < ·)
  wf := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  depth := depth

-- HOOK (F-A): Stage F-A will split `Env.stepIdx` into a call-slot (`idx.depth i' < idx.depth i`)
-- and a tail-slot (`idx.lt i' i ∧ idx.depth i' ≤ idx.depth i`) for `link_scc_compiled_split`.
/-- Index-stepped environment available to the body of a recursive function at index `i : ι`:
* cyclic callees in `recSigs` may only be invoked at `i'` with `idx.lt i' i` and
  `(strict = false ∨ idx.depth i' < idx.depth i)`;
* external / earlier-SCC callees in `extSigs` are invoked at fixed `Γext`. -/
def Env.stepIdx {ι : Type} (idx : RecIdx ι) (recSigs extSigs : List SigEntry)
    (Γrec : ι → Env) (Γext : Env) (strict : Bool) (i : ι) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ recSigs ∧
      ∃ i', idx.lt i' i ∧ (strict = false ∨ idx.depth i' < idx.depth i) ∧
        Γrec i' f as bs xs m Q X) ∨
    ((f, as, bs) ∈ extSigs ∧ Γext f as bs xs m Q X)

/-- Closed cyclic SCC environment pairing `Γrec : ι → Env` over `M.fns` with fixed external
contracts `Γext` over `M.externs`. -/
def Env.ofModuleScc {ι : Type} (M : Module) (Γrec : ι → Env) (Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ i, Γrec i f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X)

/-- Index-`i` slice of `Env.ofModuleScc` matching stack bound `base + idx.depth i * step`. -/
def Env.ofModuleSccAt {ι : Type} (M : Module) (Γrec : ι → Env) (Γext : Env) (i : ι) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fns.map Fn.sig ∧ Γrec i f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X)

/-- Fuel-bounded export environment packaging all indices `i : ι` with `idx.depth i ≤ fuel` for
downstream callers at uniform static stack bound `base + fuel * step`. -/
def Env.exportScc {ι : Type} (idx : RecIdx ι) (Γrec : ι → Env) (fuel : Nat) : Env :=
  fun f as bs xs m Q X =>
    ∃ i, idx.depth i ≤ fuel ∧ Γrec i f as bs xs m Q X

/-- Lift a single-signature index-parameterized contract family `P : Sym → ι → Spec as bs` into
`ι → Env`. -/
def envOfIdxSpec {ι : Type} {as bs : List Ty} (P : Sym → ι → Spec as bs) : ι → Env :=
  fun i f as' bs' xs m Q X =>
    ∃ (ha : as' = as) (hb : bs' = bs), P f i (ha ▸ xs) m (hb ▸ Q) X

-- HOOK (F-A): `link_scc_compiled_split` will generalize `ModuleSccOk` to separate call-slot
-- (`idx.depth i' < idx.depth i`) and tail-slot (`idx.depth i' ≤ idx.depth i`) obligations.
/-- Well-founded SCC correctness obligation: `M.namesNodup`, per-function `Wf` and `callsOk`,
and every `fn ∈ M.fns` at index `i` satisfies `Func.wp` under `Env.stepIdx ... strict i`. -/
structure ModuleSccOk {ι : Type} (idx : RecIdx ι) (Γrec : ι → Env) (Γext : Env)
    (strict : Bool) (M : Module) : Prop where
  nodup : M.namesNodup
  fnsOk : ∀ fn ∈ M.fns,
    fn.Wf ∧ fn.callsOk M.sigs M.exits ∧
    ∀ i xs m Q X, Γrec i fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.stepIdx idx (M.fns.map Fn.sig) (M.externs.map Extern.sig)
        Γrec Γext strict i) fn.body xs m Q X

end LeanQbe.T.LinkScc
