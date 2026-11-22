module

public import LeanQbe.T.Examples.UnionFind
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.WfLemmas

/-!
# Verification of Union-Find in `LeanQbe.T` (`T4`)

Typed-IR proof of path-halving `find`, call-based `union`, and inlined `unionInline`
using `LeanQbe.T.Logic` (`wp_loop_group`, `wp_unfold`, `wp_load_array64`, `wp_store_array64`,
`wp_call_of_spec`) and `t_wf_tac`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.UnionFind

open Std.ExtHashMap

/-! ## Parent array and forest invariants -/

theorem pa_set {parent : List (BitVec 64)} {j v : BitVec 64} (hj : j.toNat < parent.length) :
    ∀ i, pa (parent.set j.toNat v) i = if i = j then v else pa parent i := by
  intro i
  by_cases he : i = j
  · subst he; simp [pa, List.getD_eq_getElem?_getD, hj]
  · have hne : j.toNat ≠ i.toNat := fun h => he (BitVec.eq_of_toNat_eq h.symm)
    simp [pa, List.getD_eq_getElem?_getD, hne, he]

theorem pa_eq_getElem {parent : List (BitVec 64)} {i : BitVec 64} (hi : i.toNat < parent.length) :
    parent[i.toNat] = pa parent i := by
  simp [pa, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

attribute [local grind →] Forest.len Forest.closed Forest.rep_lt Forest.rep_root Forest.root_rep
  Forest.rep_pa Forest.rank_lt

/-- Path halving (`parent[y] := parent[parent[y]]`) preserves `Forest n parent rep rank`. -/
theorem Forest.halve {n : Nat} {parent : List (BitVec 64)} {rep : BitVec 64 → BitVec 64}
    {rank : BitVec 64 → Nat} {y : BitVec 64}
    (F : Forest n parent rep rank) (hy : y.toNat < n) (hne : pa parent y ≠ y) :
    Forest n (parent.set y.toNat (pa parent (pa parent y))) rep rank := by
  have hl : y.toNat < parent.length := F.len ▸ hy
  constructor <;> intros <;> (try simp only [pa_set hl, List.length_set] at *) <;> grind

/-- Linking `rep x`'s parent pointer to `rep y` updates `rep` to `merge rep x y`. -/
theorem Forest.link {n : Nat} {parent : List (BitVec 64)} {rep : BitVec 64 → BitVec 64}
    {rank : BitVec 64 → Nat} {x y : BitVec 64}
    (F : Forest n parent rep rank) (hx : x.toNat < n) (hy : y.toNat < n)
    (hne : rep x ≠ rep y) :
    Forest n (parent.set (rep x).toNat (rep y)) (merge rep x y)
      (fun i => if rep i = rep x then rank i + rank (rep y) + 1 else rank i) := by
  have hl : (rep x).toNat < parent.length := F.len ▸ F.rep_lt x hx
  unfold merge
  constructor <;> intros <;> (try simp only [pa_set hl, List.length_set] at *) <;> grind

theorem merge_self {rep : BitVec 64 → BitVec 64} {x y : BitVec 64} (h : rep x = rep y) :
    merge rep x y = rep := by
  funext i; simp only [merge, h]; split <;> simp_all

theorem uf_sep {p : BitVec 64} {n : Nat} {rep : BitVec 64 → BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} :
    (uf p n rep ⋆ R) m ↔ ∃ parent rank, Forest n parent rep rank ∧ (array64 p parent ⋆ R) m := by
  unfold uf
  simp only [sep_ex_l, sep_pure_l]

/-! ## `findK`, `find`, `union`, `unionInline` correctness -/

theorem findK_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {p x : BitVec 64} {n : Nat} {rep : BitVec 64 → BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : BitVec 64 → Expr Val Cont rs}
    (hm : (uf p n rep ⋆ R) m) (hx : x.toNat < n)
    (hk : ∀ m', (uf p n rep ⋆ R) m' → wp Γ Q X (k (rep x)) m') :
    wp Γ Q X (findK p x k) m := by
  refine wp_loop_group
    (fun r (y, ()) m' => ∃ parent rank,
      Forest n parent rep rank ∧ (array64 p parent ⋆ R) m' ∧
        y.toNat < n ∧ rep y = rep x ∧ rank y = r)
    ?_ (fun J hJ => ?_)
  · intro J r ⟨y, ⟨⟩⟩ m' hlt ⟨parent, rank, F, hm', hy, hry, hr⟩
    dsimp only [Blocks.get_here]
    wp_unfold
    have hy' : y.toNat < parent.length := F.len ▸ hy
    refine load_array64_step p y.toNat hy' hm' (hk := ?_)
    rw [pa_eq_getElem hy']
    refine ⟨fun hdone => ?_, fun hne => ?_⟩
    · rw [← F.root_rep y hy hdone, hry]
      exact hk m' (uf_sep.mpr ⟨parent, rank, F, hm'⟩)
    · have hpy : (pa parent y).toNat < n := F.closed y hy
      have hpy' : (pa parent y).toNat < parent.length := F.len ▸ hpy
      refine load_array64_step p (pa parent y).toNat hpy' hm' (hk := ?_)
      rw [pa_eq_getElem hpy']
      refine store_array64_step p y.toNat (pa parent (pa parent y)) hy' hm' (hk := fun _ hm'' => ?_)
      have hdec : rank (pa parent (pa parent y)) < r := by
        rw [← hr]
        by_cases h2 : pa parent (pa parent y) = pa parent y
        · rw [h2]; exact F.rank_lt y hy hne
        · exact Nat.lt_trans (F.rank_lt _ hpy h2) (F.rank_lt y hy hne)
      exact hlt (rank (pa parent (pa parent y))) (pa parent (pa parent y), ()) _ hdec
        ⟨parent.set y.toNat (pa parent (pa parent y)), rank,
          F.halve hy hne, hm'', F.closed _ hpy, by rw [F.rep_pa _ hpy, F.rep_pa y hy, hry], rfl⟩
  · wp_unfold
    obtain ⟨parent, rank, F, hm'⟩ := uf_sep.mp hm
    exact hJ (rank x) (x, ()) m ⟨parent, rank, F, hm', hx, rfl, rfl⟩

theorem find_correct :
    ∀ (Γ : Env) (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      findSpec args m Q X → Func.spec Γ find args m Q X := by
  rintro Γ ⟨p, x, ⟨⟩⟩ m Q X ⟨n, rep, R, hm, hx, hQ⟩
  dsimp only [Func.spec, Func.wp, find]
  refine findK_spec hm hx fun m' hm' => ?_
  wp_unfold
  exact hQ m' hm'

/-- Shared post-`find` link step used by both `union` and `unionInline`. -/
theorem link_spec {Γ : Env} {Q : Post []} {X : XPost} {p x y : BitVec 64} {n : Nat}
    {rep : BitVec 64 → BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (uf p n rep ⋆ R) m) (hx : x.toNat < n) (hy : y.toNat < n)
    (hQ : ∀ m', (uf p n (merge rep x y) ⋆ R) m' → Q () m') :
    wp Γ Q X (tqbe {
      %same:b = ceql ⟨.var (rep x)⟩, ⟨.var (rep y)⟩
      jnz %same, {
        ret
      }, {
        %off:l = shl ⟨.var (rep x)⟩, 3
        %a:l = add ⟨.var p⟩, %off
        store ⟨.var (rep y)⟩ : l, %a
        ret
      }
    }) m := by
  wp_unfold
  refine ⟨fun hsame => ?_, fun hne => ?_⟩
  · exact hQ m (by rwa [merge_self hsame])
  · obtain ⟨parent, rank, F, hm'⟩ := uf_sep.mp hm
    have hrx' : (rep x).toNat < parent.length := F.len ▸ F.rep_lt x hx
    exact store_array64_step p (rep x).toNat (rep y) hrx' hm'
      (hk := fun _ hm'' => hQ _ (uf_sep.mpr ⟨_, _, F.link hx hy hne, hm''⟩))

theorem union_correct (Γ : Env)
    (hfind : ∀ args m Q X, findSpec args m Q X → Γ "find" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, unionSpec args m Q X → Func.spec Γ union args m Q X := by
  rintro ⟨p, x, y, ⟨⟩⟩ m Q X ⟨n, rep, R, hm, hx, hy, hQ⟩
  dsimp only [Func.spec, Func.wp, union]
  apply wp_call_of_spec
  apply hfind
  refine ⟨n, rep, R, hm, hx, fun m₁ hm₁ => ?_⟩
  dsimp only
  apply wp_call_of_spec
  apply hfind
  refine ⟨n, rep, R, hm₁, hy, fun m₂ hm₂ => ?_⟩
  exact link_spec hm₂ hx hy hQ

theorem unionInline_correct :
    ∀ (Γ : Env) (args : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      unionSpec args m Q X → Func.spec Γ unionInline args m Q X := by
  rintro Γ ⟨p, x, y, ⟨⟩⟩ m Q X ⟨n, rep, R, hm, hx, hy, hQ⟩
  dsimp only [Func.spec, Func.wp, unionInline]
  refine findK_spec hm hx fun m₁ hm₁ => ?_
  refine findK_spec hm₁ hy fun m₂ hm₂ => ?_
  exact link_spec hm₂ hx hy hQ

/-! ## Well-formedness and module soundness -/

theorem find_wf : Func.Wf find := by t_wf_tac
theorem union_wf : Func.Wf union := by t_wf_tac
theorem unionInline_wf : Func.Wf unionInline := by t_wf_tac

/-- Non-vacuous concrete `n`-element initialization: every element points to itself. -/
@[expose] def init (n : Nat) : List (BitVec 64) :=
  (List.range n).map (BitVec.ofNat 64)

theorem forest_init {n : Nat} (_hn : n ≤ 2 ^ 64) :
    Forest n (init n) id (fun _ => 0) := by
  have hlen : (init n).length = n := by simp [init]
  have hpa : ∀ i : BitVec 64, i.toNat < n → pa (init n) i = i := by
    intro i hi
    simp only [pa, init, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    simp [BitVec.ofNat_toNat]
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hpa i hi]; exact hi
  · intro i hi; exact hi
  · intro i hi; exact hpa i hi
  · intro _ _ _; rfl
  · intro i hi; rw [hpa i hi]
  · intro i hi hne; exact absurd (hpa i hi) hne

theorem uf_init (p : BitVec 64) {n : Nat} (hn : 8 * n ≤ 2 ^ 64) :
    uf p n id ((bytes64 (init n)).At p) :=
  ⟨init n, fun _ => 0, forest_init (by omega),
    array64_bytes p (init n) (by simp only [init, List.length_map, List.length_range]; exact hn)⟩

theorem union_nonvacuous :
    unionSpec (4096, 1, 2, ()) ((bytes64 (init 4)).At 4096)
      (fun r m' => r = () ∧ (uf 4096 4 (merge id 1 2) ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  ⟨4, id, emp, by rw [sep_emp]; exact uf_init 4096 (by decide), by decide, by decide,
    fun _ h => ⟨rfl, h⟩⟩

theorem find_nonvacuous :
    findSpec (4096, 3, ()) ((bytes64 (init 4)).At 4096)
      (fun r m' => r = (3, ()) ∧ (uf 4096 4 id ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  ⟨4, id, emp, by rw [sep_emp]; exact uf_init 4096 (by decide), by decide, fun _ h => ⟨rfl, h⟩⟩

theorem merge_init_1_2 :
    merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1 := by
  decide

theorem ufFns_wf : ∀ f ∈ ufFns, Fn.Wf f := by
  intro f hf
  simp only [ufFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact find_wf
  · exact union_wf
  · exact unionInline_wf

theorem ufEnv_sound : ∀ f ∈ ufFns,
    ∀ args m Q X, ufEnv f.name f.as f.rs args m Q X → Func.spec ufEnv f.body args m Q X := by
  intro f hf
  simp only [ufFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact find_correct ufEnv
  · exact union_correct ufEnv (fun args m Q X h => h)
  · exact unionInline_correct ufEnv

theorem ufModule_checkAcyclic : ufModule.checkAcyclic = true := by rfl

theorem ufEnv_moduleOk : ModuleOk ufEnv ufModule :=
  Module.moduleOk_of_checkAcyclic ufModule_checkAcyclic ufFns_wf ufEnv_sound

end LeanQbe.T.Examples.UnionFind
