module

public import Kraken.Bedrock2.SemanticsLemmas
import all Kraken.Mem

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2

variable {w : Nat}

abbrev Handler (w : Nat) :=
  Trace w → Mem w → String → List (BitVec w) → Option (Mem w × Mem w × List (BitVec w))

def Handler.Ok (ext : ExtSpec w) (handler : Handler w) : Prop :=
  ∀ t m mKeep mGive a args mid mGive' mReceive rets,
    split m mKeep mGive → ext t mGive a args mid →
    handler t m a args = some (mGive', mReceive, rets) → mGive' = mGive ∧ mid mReceive rets

theorem Handler.ok_none (ext : ExtSpec w) : Handler.Ok ext fun _ _ _ _ => none :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => nomatch h

--GEN: Stackalloc addresses are taken from the oracle list `o` in allocation order. The
--GEN: differential tests replay the addresses logged by the compiled C program.
abbrev RunResult (w : Nat) := Trace w × Mem w × Locals w × List (BitVec w)

def run (e : Env) (fill : UInt8) (fuel : Nat) (c : Cmd) (t : Trace w) (m : Mem w) (l : Locals w)
    (o : List (BitVec w)) (handler : Handler w := fun _ _ _ _ => none) : Option (RunResult w) :=
  match fuel, c with
  | _, .skip => some (t, m, l, o)
  | _, .set x ex => do
    let v ← ex.eval m l
    some (t, m, l.insert x v, o)
  | _, .unset x => some (t, m, l.erase x, o)
  | _, .store sz ea ev => do
    let a ← ea.eval m l
    let v ← ev.eval m l
    let m' ← store? sz m a v
    some (t, m', l, o)
  | fuel, .stackalloc x n body =>
    match o with
    | [] => none
    | a :: o =>
      if n ≤ 2 ^ w ∧ (List.range n).all (fun i => !m.contains (a + .ofNat w i)) then do
        let region : Mem w := (List.replicate n fill).At a
        let r ← run e fill fuel body t (m.union region) (l.insert x a) o handler
        if (List.range n).all (fun i => r.2.1.contains (a + .ofNat w i)) then
          some (r.1, r.2.1.filter (fun k _ => !region.contains k), r.2.2.1, r.2.2.2)
        else none
      else none
  | fuel, .cond ec c1 c2 => do
    let v ← ec.eval m l
    if v ≠ 0 then run e fill fuel c1 t m l o handler else run e fill fuel c2 t m l o handler
  | fuel, .seq c1 c2 => do
    let r ← run e fill fuel c1 t m l o handler
    run e fill fuel c2 r.1 r.2.1 r.2.2.1 r.2.2.2 handler
  | 0, .while _ _ => none
  | fuel + 1, .while ec c => do
    let v ← ec.eval m l
    if v ≠ 0 then
      let r ← run e fill fuel c t m l o handler
      run e fill fuel (.while ec c) r.1 r.2.1 r.2.2.1 r.2.2.2 handler
    else some (t, m, l, o)
  | 0, .call _ _ _ => none
  | fuel + 1, .call binds fname arges => do
    let f ← e.lookup fname
    let args ← evalArgs m l arges
    let lf ← putManyZip f.params args ∅
    let r ← run e fill fuel f.body t m lf o handler
    let rets ← getMany r.2.2.1 f.rets
    let l' ← putManyZip binds rets l
    some (r.1, r.2.1, l', r.2.2.2)
  | _, .interact binds action arges => do
    let args ← evalArgs m l arges
    let h ← handler t m action args
    let mKeep := m.filter fun k _ => !h.1.contains k
    if (mKeep.inter h.2.1).isEmpty then
      let l' ← putManyZip binds h.2.2 l
      some (((h.1, action, args), (h.2.1, h.2.2)) :: t, mKeep.union h.2.1, l', o)
    else none
termination_by (fuel, c)

private theorem filter_of_split {m mKeep mGive : Mem w} (h : split m mKeep mGive) :
    m.filter (fun k _ => !mGive.contains k) = mKeep := by
  obtain ⟨rfl, hi⟩ := h
  have hi := eq_empty_iff_forall_not_mem.mp hi
  simp only [inter_eq, mem_inter_iff] at hi
  apply ext_getElem?
  intro k
  have hk := hi k
  simp only [mem_iff_isSome_getElem?] at hk
  simp only [union_eq, getElem?_filter', getElem?_union, contains_eq_isSome_getElem?]
  revert hk
  cases mKeep[k]? <;> cases mGive[k]? <;> simp

theorem run_of_exec {ext : ExtSpec w} {handler : Handler w} (hh : Handler.Ok ext handler)
    {e : Env} {c : Cmd} {t : Trace w} {m : Mem w} {l : Locals w}
    {post : Trace w → Mem w → Locals w → Prop} (h : Exec ext e c t m l post)
    {fill : UInt8} {fuel : Nat} {o : List (BitVec w)} {t' : Trace w} {m' : Mem w} {l' : Locals w}
    {o' : List (BitVec w)} (hr : run e fill fuel c t m l o handler = some (t', m', l', o')) :
    post t' m' l' := by
  induction h generalizing fuel o t' m' l' o' with
  | skip _ _ _ _ hp => simp_all [run]
  | set _ _ _ _ _ _ _ hv hp => simp_all [run]
  | unset _ _ _ _ _ hp => simp_all [run]
  | store _ _ _ _ _ _ _ _ _ _ ha hv hs hp => simp_all [run]
  | stackalloc x n body t mSmall l post _ ih =>
    cases o with
    | nil => simp [run] at hr
    | cons a o =>
      simp only [run, Option.bind_eq_bind, Option.ite_none_right_eq_some, Option.bind_eq_some_iff] at hr
      obtain ⟨⟨hn, hfresh⟩, ⟨t1, m1, l1, o1⟩, hrun, -, hr⟩ := hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
      simp only [List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at hfresh
      have hdisj : mSmall.inter ((List.replicate n fill).At a) = ∅ := by
        refine eq_empty_iff_forall_not_mem.mpr fun k hk => ?_
        simp only [inter_eq, mem_inter_iff, mem_At_iff, List.length_replicate] at hk
        obtain ⟨hk, i, hi, rfl⟩ := hk
        exact absurd (contains_iff_mem.mpr hk) (by simp [hfresh i hi])
      obtain ⟨s', st', ⟨bs, rfl, hbl, -⟩, hsplit, hp⟩ :=
        ih a _ _ ⟨_, rfl, List.length_replicate, hn⟩ ⟨rfl, hdisj⟩ hrun
      have hkey : (fun k (_ : UInt8) => !((List.replicate n fill).At a).contains k) =
          fun k _ => !(bs.At a).contains k := by
        funext k _
        congr 1
        rw [Bool.eq_iff_iff, contains_iff_mem, contains_iff_mem, mem_At_iff, mem_At_iff,
          List.length_replicate, hbl]
      simpa only [hkey, filter_of_split hsplit] using hp
  | if_true _ _ _ _ _ _ _ _ hv hnz _ ih => simp_all [run]; exact ih hr
  | if_false _ _ _ _ _ _ _ _ hv hz _ ih => simp_all [run]; exact ih hr
  | seq _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨t1, m1, l1, o1⟩, h1, h2⟩ := hr
    exact ih2 _ _ _ (ih1 h1) h2
  | while_false _ _ _ _ _ _ _ hv hz hp =>
    cases fuel <;> simp_all [run]
  | while_true _ _ _ _ _ _ _ _ hv hnz _ _ ih1 ih2 =>
    cases fuel with
    | zero => simp [run] at hr
    | succ fuel =>
      simp only [run, hv, hnz, Option.bind_eq_bind, Option.bind_some, ne_eq, not_false_eq_true, ite_true,
        Option.bind_eq_some_iff] at hr
      obtain ⟨⟨t1, m1, l1, o1⟩, h1, h2⟩ := hr
      exact ih2 _ _ _ (ih1 h1) h2
  | call _ _ _ _ _ _ _ _ _ _ _ hf ha hl _ hk ih =>
    cases fuel with
    | zero => simp [run] at hr
    | succ fuel =>
      simp only [run, hf, ha, hl, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hr
      obtain ⟨⟨t1, m1, l1, o1⟩, h1, rets, hrets, l2, hl2, hr⟩ := hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
      obtain ⟨rv, hrv, l3, hl3, hp⟩ := hk _ _ _ (ih h1)
      cases hrv.symm.trans hrets; cases hl3.symm.trans hl2
      exact hp
  | interact _ _ _ _ _ _ _ _ mKeep _ _ hs ha hx hk =>
    simp only [run, ha, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨g, r, rets⟩, hhd, hr⟩ := hr
    obtain ⟨rfl, hmid⟩ := hh _ _ _ _ _ _ _ _ _ _ hs hx hhd
    simp only [filter_of_split hs, Option.ite_none_right_eq_some, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨hemp, l2, hl2, rfl, rfl, rfl, rfl⟩ := hr
    obtain ⟨l3, hl3, hp⟩ := hk _ _ hmid
    cases hl3.symm.trans hl2
    exact hp _ ⟨rfl, isEmpty_iff.mp hemp⟩

theorem run_body_of_call {ext : ExtSpec w} {handler : Handler w} (hh : Handler.Ok ext handler)
    {e : Env} {fname : String} {t : Trace w} {m : Mem w} {args : List (BitVec w)}
    {post : Trace w → Mem w → List (BitVec w) → Prop} (h : call ext e fname t m args post)
    {f : Func} (hf : e.lookup fname = some f) {lf : Locals w}
    (hl : putManyZip f.params args ∅ = some lf)
    {fill : UInt8} {fuel : Nat} {o : List (BitVec w)} {t' : Trace w} {m' : Mem w} {l' : Locals w}
    {o' : List (BitVec w)} (hr : run e fill fuel f.body t m lf o handler = some (t', m', l', o')) :
    ∃ rets, getMany l' f.rets = some rets ∧ post t' m' rets := by
  obtain ⟨f', hf', lf', hl', hb⟩ := h
  cases hf.symm.trans hf'; cases hl.symm.trans hl'
  exact run_of_exec hh hb hr

theorem run_of_call {ext : ExtSpec w} {handler : Handler w} (hh : Handler.Ok ext handler)
    {e : Env} {fname : String} {t : Trace w} {m : Mem w} {args : List (BitVec w)}
    {post : Trace w → Mem w → List (BitVec w) → Prop} (h : call ext e fname t m args post)
    {binds : List String} {arges : List Expr} {l : Locals w} (ha : evalArgs m l arges = some args)
    {fill : UInt8} {fuel : Nat} {o : List (BitVec w)} {t' : Trace w} {m' : Mem w} {l' : Locals w}
    {o' : List (BitVec w)}
    (hr : run e fill fuel (.call binds fname arges) t m l o handler = some (t', m', l', o')) :
    ∃ rets, putManyZip binds rets l = some l' ∧ post t' m' rets := by
  cases fuel with
  | zero => simp [run] at hr
  | succ fuel =>
    obtain ⟨f, hf, -⟩ := id h
    simp only [run, hf, ha, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hr
    obtain ⟨lf, hl, ⟨t1, m1, l1, o1⟩, h1, rets, hrets, l2, hl2, hr⟩ := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    obtain ⟨rets', hrets', hp⟩ := run_body_of_call hh h hf hl h1
    cases hrets'.symm.trans hrets
    exact ⟨rets, hl2, hp⟩

end Kraken.Bedrock2
