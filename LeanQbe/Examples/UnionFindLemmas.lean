module

public import LeanQbe.Examples.UnionFind
public import LeanQbe.Logic.MemLemmas
public import LeanQbe.Logic.Rules
public import LeanQbe.Wf
public import LeanQbe.MainLemmas

/-!
# Union-find: correctness

* Model lemmas: `Forest.halve` (path halving keeps the forest and the partition) and `Forest.link`
  (linking two roots merges their classes), each one `grind` call.
* `findK_spec`: the macro, by the loop rule with the ghost `rank` as measure.
* `find_correct`, `union_correct` (calls `$find` through its contract), `unionInline_correct`.
* Non-vacuity: `uf_init` (a fresh structure of singletons exists in memory) and `union_nonvacuous`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.UnionFind

open Std Std.ExtHashMap

/-! ## Model -/

theorem pa_set {parent : List Val} {j v : Val} (hj : j.toNat < parent.length) (i : Val) :
    pa (parent.set j.toNat v) i = if i = j then v else pa parent i := by
  simp only [pa, List.getD_eq_getElem?_getD, List.getElem?_set]
  grind

theorem pa_eq_getElem {parent : List Val} {i : Val} (hi : i.toNat < parent.length) :
    parent[i.toNat] = pa parent i := by
  simp [pa, List.getD_eq_getElem?_getD, hi]

attribute [local grind →] Forest.len Forest.closed Forest.rep_lt Forest.rep_root Forest.root_rep
  Forest.rep_pa Forest.rank_lt

/-- Path halving keeps the forest, the partition, and the ranks. -/
theorem Forest.halve {n : Nat} {parent : List Val} {rep : Val → Val} {rank : Val → Nat} {y : Val}
    (hf : Forest n parent rep rank) (hy : y.toNat < n) (hnr : pa parent y ≠ y) :
    Forest n (parent.set y.toNat (pa parent (pa parent y))) rep rank := by
  have hl : y.toNat < parent.length := hf.len ▸ hy
  constructor <;> intros <;> (try simp only [pa_set hl, List.length_set] at *) <;> grind

/-- Linking the root of `x` under the root of `y` merges their classes. -/
theorem Forest.link {n : Nat} {parent : List Val} {rep : Val → Val} {rank : Val → Nat} {x y : Val}
    (hf : Forest n parent rep rank) (hx : x.toNat < n) (hy : y.toNat < n) (hne : rep x ≠ rep y) :
    Forest n (parent.set (rep x).toNat (rep y)) (merge rep x y)
      (fun i => if rep i = rep x then rank i + rank (rep y) + 1 else rank i) := by
  have hl : (rep x).toNat < parent.length := hf.len ▸ hf.rep_lt x hx
  unfold merge
  constructor <;> intros <;> (try simp only [pa_set hl, List.length_set] at *) <;> grind

theorem merge_self {rep : Val → Val} {x y : Val} (h : rep x = rep y) : merge rep x y = rep := by
  funext i; unfold merge; split <;> simp_all

/-- Unpack (or repack) `uf` inside a frame. -/
theorem uf_sep {p : Val} {n : Nat} {rep : Val → Val} {R : Mem 64 → Prop} {m : Mem 64} :
    (uf p n rep ⋆ R) m ↔ ∃ parent rank, Forest n parent rep rank ∧ (array64 p parent ⋆ R) m := by
  unfold uf; simp only [sep_ex_l, sep_pure_l]

/-! ## Programs -/

theorem findK_spec {Γ : Env} {Q : Post} {X : XPost} {p x : Val} {n : Nat} {rep : Val → Val}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Val → Expr Val Cont}
    (hm : (uf p n rep ⋆ R) m) (hx : x.toNat < n)
    (hk : ∀ m', (uf p n rep ⋆ R) m' → wp Γ Q X (k (rep x)) [] [] m') :
    wp Γ Q X (findK p x k) [] [] m := by
  obtain ⟨parent, rank, hf, hm⟩ := uf_sep.1 hm
  apply wp_loop (fun r as m => ∃ y parent, as = [y] ∧ y.toNat < n ∧ rep y = rep x ∧ rank y = r ∧
    Forest n parent rep rank ∧ (array64 p parent ⋆ R) m)
  · rintro J r as m ⟨y, parent, rfl, hy, hrep, rfl, hf, hm⟩ ih
    wp_unfold
    have hyl : y.toNat < parent.length := hf.len ▸ hy
    refine ⟨_, loadVal_array64 hyl hm, fun hroot => ?_, fun hnr => ?_⟩
    · rw [pa_eq_getElem hyl] at hroot
      rw [show y = rep x from hrep ▸ (hf.root_rep y hy hroot).symm]
      exact hk m (uf_sep.2 ⟨parent, rank, hf, hm⟩)
    · rw [pa_eq_getElem hyl] at hnr ⊢
      have hpy := hf.closed y hy
      have hpl : (pa parent y).toNat < parent.length := hf.len ▸ hpy
      obtain ⟨hok, hm'⟩ := store_array64 (pa parent (pa parent y)) hyl hm
      refine ⟨_, loadVal_array64 hpl hm, ?_⟩
      rw [pa_eq_getElem hpl]
      refine ⟨hok, ih _ _ _ (by grind) ⟨_, _, rfl, hf.closed _ hpy, by grind, rfl, hf.halve hy hnr, hm'⟩⟩
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨x, parent, rfl, hx, rfl, rfl, hf, hm⟩

theorem find_correct (Γ : Env) : ∀ args m Q X, findSpec args m Q X → Func.spec Γ find args m Q X := by
  rintro _ m Q X ⟨p, x, n, rep, R, rfl, hm, hx, hQ⟩
  exact findK_spec hm hx fun m' hm' => by wp_unfold; exact hQ m' hm'

/-- The tail of `union` after both representatives are known. -/
theorem link_spec {Γ : Env} {Q : Post} {X : XPost} {p x y : Val} {n : Nat} {rep : Val → Val}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (uf p n rep ⋆ R) m) (hx : x.toNat < n) (hy : y.toNat < n)
    (hQ : ∀ m', (uf p n (merge rep x y) ⋆ R) m' → Q [] m') :
    wp Γ Q X (qbe {
      %c =w ceql ⟨.var (rep x)⟩, ⟨.var (rep y)⟩
      jnz %c, { ret }, {
        %o =l shl ⟨.var (rep x)⟩, 3
        %a =l add ⟨.var p⟩, %o
        storel ⟨.var (rep y)⟩, %a
        ret
      }
    }) [] [] m := by
  wp_unfold
  refine ⟨fun heq => hQ m (by rwa [merge_self heq]), fun hne => ?_⟩
  obtain ⟨parent, rank, hf, hm⟩ := uf_sep.1 hm
  have hl : (rep x).toNat < parent.length := hf.len ▸ hf.rep_lt x hx
  obtain ⟨hok, hm'⟩ := store_array64 (rep y) hl hm
  exact ⟨hok, hQ _ (uf_sep.2 ⟨_, _, hf.link hx hy hne, hm'⟩)⟩

theorem union_correct (Γ : Env) (hfind : ∀ args m Q X, findSpec args m Q X → Γ "find" args m Q X) :
    ∀ args m Q X, unionSpec args m Q X → Func.spec Γ union args m Q X := by
  rintro _ m Q X ⟨p, x, y, n, rep, R, rfl, hm, hx, hy, hQ⟩
  simp only [Func.spec, union, wp_param_cons]
  refine wp_call_of_spec (hfind _ _ _ _ ⟨p, x, n, rep, R, rfl, hm, hx, fun m1 hm1 => ?_⟩)
  simp only [wp_param_cons]
  refine wp_call_of_spec (hfind _ _ _ _ ⟨p, y, n, rep, R, rfl, hm1, hy, fun m2 hm2 => ?_⟩)
  simp only [wp_param_cons]
  exact link_spec hm2 hx hy hQ

theorem unionInline_correct (Γ : Env) :
    ∀ args m Q X, unionSpec args m Q X → Func.spec Γ unionInline args m Q X := by
  rintro _ m Q X ⟨p, x, y, n, rep, R, rfl, hm, hx, hy, hQ⟩
  exact findK_spec hm hx fun m1 hm1 => findK_spec hm1 hy fun m2 hm2 => link_spec hm2 hx hy hQ

/-! ## Well-formedness (what the compiler needs) -/

theorem find_wf : Func.Wf find := by wf_tac
theorem union_wf : Func.Wf union := by wf_tac
theorem unionInline_wf : Func.Wf unionInline := by wf_tac

/-! ## Non-vacuity -/

/-- `n` singletons: every element is its own parent. -/
def init (n : Nat) : List Val := (List.range n).map (BitVec.ofNat 64)

theorem forest_init {n : Nat} (_hn : n ≤ 2 ^ 64) : Forest n (init n) id (fun _ => 0) := by
  have hpa : ∀ i : Val, i.toNat < n → pa (init n) i = i := fun i hi => by
    simp [pa, init, List.getD_eq_getElem?_getD, hi]
  constructor <;> intros <;> simp_all [init]

/-- A fresh union-find structure exists in memory: the bytes of `init n` at `p`. -/
theorem uf_init (p : Val) {n : Nat} (hn : 8 * n ≤ 2 ^ 64) :
    uf p n id ((bytes64 (init n)).At p) :=
  ⟨_, _, forest_init (by omega), array64_bytes p _ (by simpa [init] using hn)⟩

/-- `unionSpec` is satisfiable, with a postcondition that pins the new partition down. -/
theorem union_nonvacuous :
    unionSpec [0x1000, 1, 2] ((bytes64 (init 4)).At 0x1000)
      (fun rs m' => rs = [] ∧ (uf 0x1000 4 (merge id 1 2) ⋆ emp) m') (fun _ _ _ => False) :=
  ⟨0x1000, 1, 2, 4, id, emp, rfl, by rw [sep_emp]; exact uf_init 0x1000 (by decide),
    by decide, by decide, fun _ h => ⟨rfl, h⟩⟩

/-- `findSpec` is satisfiable, and on fresh singletons `find` returns its argument. -/
theorem find_nonvacuous :
    findSpec [0x1000, 3] ((bytes64 (init 4)).At 0x1000)
      (fun rs m' => rs = [3] ∧ (uf 0x1000 4 id ⋆ emp) m') (fun _ _ _ => False) :=
  ⟨0x1000, 3, 4, id, emp, rfl, by rw [sep_emp]; exact uf_init 0x1000 (by decide),
    by decide, fun _ h => ⟨rfl, h⟩⟩

/-- After `union 1 2` on singletons, 1 and 2 share a class and 0 does not join it. -/
theorem merge_init_1_2 : merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1 := by
  decide

theorem ufFns_wf : ∀ f ∈ ufFns, Func.Wf f.body := by
  intro f hf
  simp only [ufFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact find_wf
  · exact union_wf
  · exact unionInline_wf

theorem ufEnv_sound :
    ∀ f ∈ ufFns, ∀ args m Q X, ufEnv f.name args m Q X → Func.spec ufEnv f.body args m Q X := by
  intro f hf
  simp only [ufFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact find_correct _
  · exact union_correct _ (fun _ _ _ _ h => h)
  · exact unionInline_correct _

/-- Target-generic `FnSpec` for all three functions in `ufFns`. -/
theorem uf_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 ufFns maxBound)
    (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    {nm : String} (hnm : nm ∈ ufFns.map Fn.name) :
    T.Defined h nm ∧ T.FnSpec h nm (ufEnv nm) (M.bound nm) 0 :=
  M.fnSpec h ufEnv k₀ hc hu ufFns_wf ufEnv_sound
    (fun _ hp => nomatch hp) (fun _ hg => nomatch hg) hnm

def ufInitBytes : List UInt8 := bytes64 (init 4)

theorem find_witness {T : Target} (I : TargetInit T)
    (M : Compiled T [] [] 0 ufFns 2048) :
    Eventually (T.step M.host)
      (fun st => T.pc st = I.ra0 ∧ T.get (T.data st) I.ret0 = 3 ∧
        (T.mem (T.data st) =⋆ uf 0x1000#64 4 id ⋆
          T.Exit I.sp0 (M.bound "find") ⋆ Std.ExtHashMap.emp))
      (T.mkState (I.initState (M.bound "find") ufInitBytes [0x1000, 3])
        (T.labelAddr M.host "find")) :=
  I.run_ret1_sep M (M.fnSpec_host ufEnv ufFns_wf ufEnv_sound (nm := "find") (by decide)).2
    ufInitBytes [0x1000, 3] 3 (uf 0x1000#64 4 id) (by decide) (by decide)
    (Q := fun rs m' => rs = [3] ∧ (uf 0x1000 4 id ⋆ emp) m') find_nonvacuous
    fun _ _ ⟨hr, hm⟩ => ⟨hr, by rwa [sep_emp] at hm⟩

theorem union_witness {T : Target} (I : TargetInit T)
    (M : Compiled T [] [] 0 ufFns 2048) {nm : String}
    (hnm : nm ∈ ufFns.map Fn.name) (heq : ufEnv nm = unionSpec) :
    Eventually (T.step M.host)
      (fun st => T.pc st = I.ra0 ∧
        (T.mem (T.data st) =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      (T.mkState (I.initState (M.bound nm) ufInitBytes [0x1000, 1, 2])
        (T.labelAddr M.host nm)) := by
  refine I.run_fnSpec M (heq ▸ (M.fnSpec_host ufEnv ufFns_wf ufEnv_sound hnm).2)
    ufInitBytes [0x1000, 1, 2] (by decide) (by decide) union_nonvacuous ?_
  rintro st (⟨hpc, _, m', ⟨_, huf⟩, _, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · rw [sep_emp] at huf
    exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf)) hm', merge_init_1_2⟩
  · exact hx.elim

end LeanQbe.UnionFind
