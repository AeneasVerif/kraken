module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Frontend.C0

/-!
# End-to-end test of the C0 proof-scaling toolkit (`c0_layout_lemmas!`, `c0_steps`, `Env.ofTable`)

A small "solver state" module: an 8-field `Solver` struct, a `u64` trail array, an array scan
(`sv_find`, calling `sv_get` in its loop condition) and a backtrack-style loop (`sv_backtrack`)
that pops the trail, clears popped slots, and counts steps. The three functions are linked through
one `Env.ofTable` specification table, proved `ModuleOk` with `Env.ofTable_moduleOk`, and shown to
ignore exit continuations with `Env.ofTable_noExit`.

* `c0_decl_and_layout!` generates `structure Solver`, `Solver.At`, the `@[c0_load]` /
  `@[c0_store]` field lemmas, and the lowered C0 module from one single C0 source string;
  `c0_steps` finds them through the `Solver.At` footprint.
* The six fields the code never touches (`cap`, `level`, `flags`, `aux0`, `aux1`, and `found` in
  `sv_backtrack`) are never mentioned: stores produce record updates `{ s with f := v }`, and the
  `sv_backtrack` contract and invariant frame them with `AgreesExcept btMask s s'`.
* Sections `v2.1`–`v2.4` exercise recursive embedded-struct flattening (`#025-B2`), combined
  single-source `c0_layout_lemmas!`, `.sdiv`/`.srem`/`.addc`/`.subb`/`.umulw` (`#679`),
  `D-Plain` 32-bit `ward` dynamic-offset array access & slice framing, and crisp diagnostic
  error reporting on untagged/non-matching `loadVal` / `storeMem` goals.

## Proof-to-C0 LOC ratio

Counted as non-blank lines of this file:
* C0 code of the three functions (`u64 sv_get` .. the closing `}` of `sv_backtrack`): 22.
* The three `*_wp` theorems, statements and proofs (`sv_get_wp` .. `sv_backtrack_wp`): 39,
  i.e. **1.8 : 1** (target `≤ 4 : 1`).
* Also counting the three `Spec` definitions and `btMask` (16 lines): 55, i.e. **2.5 : 1**.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.C0StepTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.C0Step

c0_decl_and_layout! sv "
typedef struct {
  u64 len; u64 cap; u64 level; u64 found; u64 steps; u64 flags; u64 aux0; u64 aux1;
} Solver;
u64 sv_get(u64 arr, u64 i) { return ((u64 *)arr)[i]; }
u64 sv_find(u64 sp, u64 arr, u64 key) {
  Solver *s = (Solver *)sp;
  u64 i = 0ULL;
  while (i < s->len) {
    if (sv_get(arr, i) == key) {
      s->found = i;
      return 1ULL;
    }
    i = i + 1ULL;
  }
  s->found = s->len;
  return 0ULL;
}
void sv_backtrack(u64 sp, u64 arr, u64 target) {
  Solver *s = (Solver *)sp;
  while (target < s->len) {
    s->len = s->len - 1ULL;
    ((u64 *)arr)[s->len] = 0ULL;
    s->steps = s->steps + 1ULL;
  }
}
"

/-! ## Generated layout -/

example : Solver.sizeof = 64 := rfl
example (s : Solver) (v : BitVec 64) : ({ s with found := v } : Solver).cap = s.cap := rfl

/-- `AgreesExcept` frames every field outside the mask by `rfl`. -/
example (s s' : Solver) (h : AgreesExcept (fun t => { t with len := 0, steps := 0 }) s s') :
    s'.cap = s.cap ∧ s'.aux1 = s.aux1 :=
  ⟨h.get Solver.cap, h.get Solver.aux1⟩

/-! ## Contracts -/

def svGetSpec : Spec [i64, i64] [i64] := fun (arr, i, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop) (hi : i.toNat < xs.length),
    (array (t := i64) arr xs ⋆ R) m ∧ Q (xs[i.toNat], ()) m

def svFindSpec : Spec [i64, i64, i64] [i64] := fun (sp, arr, key, ()) m Q _ =>
  ∃ (s : Solver) (xs : List (BitVec 64)) (R : Mem 64 → Prop), s.len.toNat ≤ xs.length ∧
    (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m ∧
    ∀ r k m', (Solver.At sp { s with found := k } ⋆ array (t := i64) arr xs ⋆ R) m' →
      (r = 1 → k.toNat < s.len.toNat ∧ xs[k.toNat]? = some key) →
      (r = 0 → ∀ j < s.len.toNat, xs[j]? ≠ some key) → Q (r, ()) m'

/-- The fields `sv_backtrack` may change. -/
abbrev btMask (t : Solver) : Solver := { t with len := 0, steps := 0 }

def svBacktrackSpec : Spec [i64, i64, i64] [] := fun (sp, arr, tgt, ()) m Q _ =>
  ∃ (s : Solver) (xs : List (BitVec 64)) (R : Mem 64 → Prop), s.len.toNat ≤ xs.length ∧
    (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m ∧
    ∀ s' ys m', AgreesExcept btMask s s' → s'.len.toNat = min s.len.toNat tgt.toNat →
      ys.length = xs.length → (∀ j < s'.len.toNat, ys[j]? = xs[j]?) →
      (Solver.At sp s' ⋆ array (t := i64) arr ys ⋆ R) m' → Q () m'

/-! ## `Func.wp` proofs -/

theorem sv_get_wp (Γ : Env) : ∀ a m Q X, svGetSpec a m Q X → Func.wp Γ sv_get_body a m Q X := by
  rintro ⟨arr, i, ⟨⟩⟩ m Q X ⟨xs, R, hi, hm, hQ⟩; c0_steps; exact hQ

theorem sv_find_wp (Γ : Env)
    (hGet : ∀ a m Q X, svGetSpec a m Q X → Γ "sv_get" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, svFindSpec a m Q X → Func.wp Γ sv_find_body a m Q X := by
  rintro ⟨sp, arr, key, ⟨⟩⟩ m Q X ⟨s, xs, R, hlen, hm, hQ⟩
  c0_steps
  refine wp_loop_inv (fun v m => v.1.toNat ≤ s.len.toNat ∧ (∀ j < v.1.toNat, xs[j]? ≠ some key) ∧
      (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m) (fun v _ => s.len.toNat - v.1.toNat)
    (fun J hJ => ?_) (fun J v m ⟨hle, hne, hm⟩ hJ => ?_)
  · c0_steps; exact hJ _ _ ⟨by simp, by simp, hm⟩
  · c0_steps
    · c0_call hGet
      refine ⟨xs, _, by omega, by c0_frame, ?_⟩
      c0_steps
      · exact hQ _ _ _ (by c0_frame) (fun _ => ⟨by omega, List.getElem?_eq_some_iff.2 ⟨_, hc⟩⟩)
          (by simp)
      · refine hJ _ _ (by c0_bound) ⟨by c0_bound, fun j hj => ?_, hm⟩
        rcases Nat.lt_or_ge j v.1.toNat with h | h
        · exact hne j h
        obtain rfl : j = v.1.toNat := by simp only at hj; bv_omega
        simpa [List.getElem?_eq_getElem (show v.1.toNat < xs.length by omega)] using hc
    · exact hQ _ _ _ (by c0_frame) (by simp) fun _ j hj => hne j (by omega)

theorem sv_backtrack_wp (Γ : Env) :
    ∀ a m Q X, svBacktrackSpec a m Q X → Func.wp Γ sv_backtrack_body a m Q X := by
  rintro ⟨sp, arr, tgt, ⟨⟩⟩ m Q X ⟨s, xs, R, hlen, hm, hQ⟩
  c0_steps
  refine wp_loop_group (fun n _ m => ∃ s' ys, n = s'.len.toNat ∧ AgreesExcept btMask s s' ∧
      s'.len.toNat ≤ s.len.toNat ∧ (s'.len.toNat < s.len.toNat → tgt.toNat ≤ s'.len.toNat) ∧
      ys.length = xs.length ∧ (∀ j < s'.len.toNat, ys[j]? = xs[j]?) ∧
      (Solver.At sp s' ⋆ array (t := i64) arr ys ⋆ R) m)
    (fun J n _ m hJ ⟨s', ys, hn, hag, hle, hlt, hyl, hys, hm⟩ => ?_) (fun J hJ => ?_)
  · c0_steps
    · refine hJ _ () m ?_ ⟨_, _, rfl, ?_, ?_, ?_, ?_, fun j hj => ?_, by c0_frame⟩
      all_goals first | exact hag.update _ | c0_bound | simpa using hyl | skip
      rw [List.getElem?_set_ne (by c0_bound)]; exact hys j (by c0_bound)
    · exact hQ s' ys m hag (by c0_bound) hyl hys (by c0_frame)
  · c0_steps
    exact hJ _ () m ⟨s, xs, rfl, .refl _ _, Nat.le_refl _, by omega, rfl, fun _ _ => rfl, hm⟩

/-! ## Linking: one specification table for the whole module -/

def svTable : List SpecEntry :=
  [⟨"sv_get", [i64, i64], [i64], svGetSpec, true⟩,
    ⟨"sv_find", [i64, i64, i64], [i64], svFindSpec, true⟩,
    ⟨"sv_backtrack", [i64, i64, i64], [], svBacktrackSpec, true⟩]

abbrev svEnv : Env := Env.ofTable svTable

theorem svEnv_get : ∀ a m Q X, svGetSpec a m Q X → svEnv "sv_get" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := ⟨"sv_get", [i64, i64], [i64], svGetSpec, true⟩)
    (by simp [svTable]) (by decide) h

theorem sv_module_checkAcyclic : sv_module.checkAcyclic = true := by t_kernel_rfl

theorem sv_get_wf : Func.Wf sv_get_body := by t_wf_reify
theorem sv_find_wf : Func.Wf sv_find_body := by t_wf_reify
theorem sv_backtrack_wf : Func.Wf sv_backtrack_body := by t_wf_reify

/-- Headline: the whole module meets its specification table. -/
theorem svEnv_moduleOk : ModuleOk svEnv sv_module :=
  Env.ofTable_moduleOk sv_module_checkAcyclic ⟨sv_get_wf, sv_find_wf, sv_backtrack_wf, trivial⟩
    ⟨.of (sv_get_wp _), .of (sv_find_wp _ svEnv_get), .of (sv_backtrack_wp _), trivial⟩

/-- Every row is `noExit`, as `Compiled.fnSpec_noExit_id` requires. -/
theorem svEnv_noExit : ∀ f as bs xs m Q X X', svEnv f as bs xs m Q X → svEnv f as bs xs m Q X' :=
  Env.ofTable_noExit (by simp [svTable])

#print axioms sv_find_wp
#print axioms sv_backtrack_wp
#print axioms svEnv_moduleOk
#print axioms svEnv_noExit

/-! ## v2.1: Embedded-struct flattening (`#025-B2`) & single-source `c0_layout_lemmas!` -/

c0_decl_and_layout! nested "
typedef struct {
  u64 mv;
  u64 nc;
  u64 cur;
  u64 val;
} KissatDimacs;

struct TagBox {
  u32 id;
  u32 flags;
};

typedef union {
  u64 raw;
  u32 half;
} SkipUnion;

typedef struct {
  KissatDimacs d;
  u8 kind;
  struct TagBox tb;
  struct { u32 lo; u32 hi; } pair;
  SkipUnion u;
  u64 tail;
} NestedHdr;

typedef struct {
  u32 hdr;
  struct TagBox inner;
} MidBox;

typedef struct {
  u8 tag;
  MidBox m;
} DeepBox;

typedef struct {
  u64 only;
} SingleBox;

u64 nested_step(NestedHdr *h, u32 delta) {
  h->d.cur = h->d.cur + 1ULL;
  h->tb.flags = h->tb.flags + delta;
  h->pair.hi = h->pair.lo + delta;
  return h->d.mv + h->d.nc + (u64)h->tb.id + h->tail;
}

u32 deep_read_bump(DeepBox *b) {
  u32 x = b->m.inner.id;
  b->m.inner.flags = x + 1u;
  return x;
}

u64 single_swap(SingleBox *b, u64 v) {
  u64 old = b->only;
  b->only = v;
  return old;
}
"

/-! Verify exact SysV LP64 sizes and flattened offsets/types (`#025-B2`). -/

example : KissatDimacs.sizeof = 32 := rfl
example : TagBox.sizeof = 8 := rfl
example : NestedHdr.sizeof = 72 := rfl
example : DeepBox.sizeof = 16 := rfl
example : SingleBox.sizeof = 8 := rfl

example (h : NestedHdr) :
    (h.d_mv, h.d_nc, h.d_cur, h.d_val, h.kind, h.tb_id, h.tb_flags, h.pair_lo, h.pair_hi,
      h.tail) =
    (h.d_mv, h.d_nc, h.d_cur, h.d_val, h.kind, h.tb_id, h.tb_flags, h.pair_lo, h.pair_hi,
      h.tail) := rfl

example (p : BitVec 64) (h : NestedHdr) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (NestedHdr.At p h ⋆ R) m) :
    loadVal m i64 p = some h.d_mv ∧
    loadVal m i64 (p + 8) = some h.d_nc ∧
    loadVal m i64 (p + 16) = some h.d_cur ∧
    loadVal m i64 (p + 24) = some h.d_val ∧
    loadVal m i8 (p + 32) = some h.kind ∧
    loadVal m i32 (p + 36) = some h.tb_id ∧
    loadVal m i32 (p + 40) = some h.tb_flags ∧
    loadVal m i32 (p + 44) = some h.pair_lo ∧
    loadVal m i32 (p + 48) = some h.pair_hi ∧
    loadVal m i64 (p + 64) = some h.tail :=
  ⟨NestedHdr.load_d_mv hm, NestedHdr.load_d_nc hm, NestedHdr.load_d_cur hm,
    NestedHdr.load_d_val hm, NestedHdr.load_kind hm, NestedHdr.load_tb_id hm,
    NestedHdr.load_tb_flags hm, NestedHdr.load_pair_lo hm, NestedHdr.load_pair_hi hm,
    NestedHdr.load_tail hm⟩

theorem nested_step_wp (Γ : Env) (p : BitVec 64) (delta : BitVec 32) (h : NestedHdr)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (NestedHdr.At p h ⋆ R) m)
    (hQ : ∀ m',
      (NestedHdr.At p
        { h with d_cur := h.d_cur + 1, tb_flags := h.tb_flags + delta,
                 pair_hi := h.pair_lo + delta } ⋆ R) m' →
      Q (h.d_mv + h.d_nc + h.tb_id.setWidth 64 + h.tail, ()) m') :
    Func.wp Γ nested_step_body (p, delta, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem deep_read_bump_wp (Γ : Env) (p : BitVec 64) (b : DeepBox)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hm : (DeepBox.At p b ⋆ R) m)
    (hQ : ∀ m', (DeepBox.At p { b with m_inner_flags := b.m_inner_id + 1 } ⋆ R) m' →
      Q (b.m_inner_id, ()) m') :
    Func.wp Γ deep_read_bump_body (p, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem single_swap_wp (Γ : Env) (p v : BitVec 64) (b : SingleBox)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (SingleBox.At p b ⋆ R) m)
    (hQ : ∀ m', (SingleBox.At p { only := v } ⋆ R) m' → Q (b.only, ()) m') :
    Func.wp Γ single_swap_body (p, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

/-! Combined C0 string (structs + functions) works directly with `c0_layout_lemmas!` too. -/

namespace CombinedSolo
c0_layout_lemmas! "
typedef struct { u32 x; u32 y; } Pt;
u32 pt_sum(Pt *p) { return p->x + p->y; }
"
example : Pt.sizeof = 8 := rfl
end CombinedSolo

/-! ## v2.2: `.sdiv`, `.srem`, pointer subtraction, `.addc`, `.subb`, `.umulw` (`#679`) -/

c0_decl! arith "
i64 sdiv_srem_pos(i64 a, i64 b) {
  if (b <= 0LL) { return 0LL; }
  return (a / b) + (a % b);
}
i64 ptr_diff_u32(u32 *p, u32 *q) {
  return p - q;
}
i64 sdiv_unguarded(i64 a, i64 b) {
  return a / b;
}
u64 udiv_const(u64 x) {
  return (x * 20ULL) / 19ULL;
}
u64 arith_ext(u64 a, u64 b, bool cin) {
  u64 s = 0ULL; bool co = false;
  C0_TIE2(s, co, c0_addc64(a, b, cin));
  u64 d = 0ULL; bool bo = false;
  C0_TIE2(d, bo, c0_subb64(s, b, co));
  u64 lo = 0ULL; u64 hi = 0ULL;
  C0_TIE2(lo, hi, c0_umul128(d, a));
  return lo ^ hi ^ (u64)bo;
}
"

theorem sdiv_srem_pos_wp (Γ : Env) (a b : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (h0 : b.sle 0#64 = true → Q (0#64, ()) m)
    (hpos : b.sle 0#64 = false → Q (a.sdiv b + a.srem b, ()) m) :
    Func.wp Γ sdiv_srem_pos_body (a, b, ()) m Q X := by
  c0_steps!
  · exact h0 hc
  · exact hpos hc

theorem ptr_diff_u32_wp (Γ : Env) (p q : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hQ : Q ((p - q).sdiv 4#64, ()) m) :
    Func.wp Γ ptr_diff_u32_body (p, q, ()) m Q X := by
  c0_steps!
  exact hQ

theorem sdiv_unguarded_wp (Γ : Env) (a b : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hd : sdivDefined a b = true) (hQ : Q (a.sdiv b, ()) m) :
    Func.wp Γ sdiv_unguarded_body (a, b, ()) m Q X := by
  c0_steps!
  exact hQ

theorem sdiv_unguarded_split_test (Γ : Env) (a b : BitVec 64) (m : Mem 64) (Q : Post [i64])
    (X : XPost) (hb : b ≠ 0) (hno : ¬ (a = BitVec.intMin 64 ∧ b = -1))
    (hQ : Q (a.sdiv b, ()) m) :
    Func.wp Γ sdiv_unguarded_body (a, b, ()) m Q X := by
  c0_steps!
  exact hQ

/-- When `sdivDefined` is not auto-provable, `c0_steps` leaves the side condition as a subgoal
while continuing to symbolically execute the body. -/
example (Γ : Env) (a b : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hQ : Q (a.sdiv b, ()) m) (hdef : True → sdivDefined a b = true) :
    Func.wp Γ sdiv_unguarded_body (a, b, ()) m Q X := by
  c0_steps!
  · exact hdef trivial
  · exact hQ

theorem udiv_const_wp (Γ : Env) (x : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hQ : Q ((x * 20#64) / 19#64, ()) m) :
    Func.wp Γ udiv_const_body (x, ()) m Q X := by
  c0_steps!
  exact hQ

theorem arith_ext_wp (Γ : Env) (a b : BitVec 64) (cin : Bool) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hQ :
      let s := a + b + BitVec.ofNat 64 cin.toNat
      let co := decide (2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat)
      let d := s - b - BitVec.ofNat 64 co.toNat
      let bo := decide (s.toNat < b.toNat + co.toNat)
      let lo := d * a
      let hi := BitVec.ofNat 64 (d.toNat * a.toNat / 2 ^ 64)
      Q (lo ^^^ hi ^^^ BitVec.ofNat 64 bo.toNat, ()) m) :
    Func.wp Γ arith_ext_body (a, b, cin, ()) m Q X := by
  c0_steps!
  exact hQ

/-! ## v2.3: `D-Plain` 32-bit `ward` dynamic indexing & slice framing -/

c0_decl! ward "
u32 ward_shl2_rw(u64 arena, u64 off, u64 k, u32 v) {
  u32 *p = (u32 *)(arena + ((off + k) << 2ULL));
  u32 old = *p;
  *p = v;
  return old;
}
u32 ward_clause_swap(u64 arena, u32 cref, u32 k) {
  u32 *cl = (u32 *)arena + cref;
  u32 sz = cl[1];
  u32 lit = cl[k];
  cl[k] = sz;
  return lit;
}
u32 ward_u32_shl2_read(u64 arena, u32 off, u32 k) {
  return *(u32 *)(arena + (((u64)off + (u64)k) << 2ULL));
}
u64 word64_off_shl3_rw(u64 base, u64 off, u64 k, u64 v) {
  u64 *p = (u64 *)(base + ((off + k) << 3ULL));
  u64 old = *p;
  *p = v;
  return old;
}
"

theorem ward_shl2_rw_wp (Γ : Env) (arena off k : BitVec 64) (v : BitVec 32)
    (ws : List (BitVec 32)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hi : off.toNat + k.toNat < ws.length) (hm : (array (t := i32) arena ws ⋆ R) m)
    (hQ : ∀ m', (array (t := i32) arena (ws.set (off.toNat + k.toNat) v) ⋆ R) m' →
      Q (ws[off.toNat + k.toNat]'hi, ()) m') :
    Func.wp Γ ward_shl2_rw_body (arena, off, k, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem ward_clause_swap_wp (Γ : Env) (arena : BitVec 64) (ref k : BitVec 32)
    (ws : List (BitVec 32)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (h1 : ref.toNat + 1 < ws.length) (hk : ref.toNat + k.toNat < ws.length)
    (hm : (array (t := i32) arena ws ⋆ R) m)
    (hQ : ∀ m',
      (array (t := i32) arena (ws.set (ref.toNat + k.toNat) (ws[ref.toNat + 1]'h1)) ⋆ R) m' →
      Q (ws[ref.toNat + k.toNat]'hk, ()) m') :
    Func.wp Γ ward_clause_swap_body (arena, ref, k, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem ward_u32_shl2_read_wp (Γ : Env) (arena : BitVec 64) (off k : BitVec 32)
    (ws : List (BitVec 32)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hi : off.toNat + k.toNat < ws.length) (hm : (array (t := i32) arena ws ⋆ R) m)
    (hQ : Q (ws[off.toNat + k.toNat]'hi, ()) m) :
    Func.wp Γ ward_u32_shl2_read_body (arena, off, k, ()) m Q X := by
  c0_steps!
  exact hQ

theorem word64_off_shl3_rw_wp (Γ : Env) (base off k v : BitVec 64)
    (ws : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hi : off.toNat + k.toNat < ws.length) (hm : (array64 base ws ⋆ R) m)
    (hQ : ∀ m', (array64 base (ws.set (off.toNat + k.toNat) v) ⋆ R) m' →
      Q (ws[off.toNat + k.toNat]'hi, ()) m') :
    Func.wp Γ word64_off_shl3_rw_body (base, off, k, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

/-- Slice framing round-trip on a 32-bit `ward` arena: focus `[off, off + len)` at
`arena + (off <<< 2)`, read/update inside the slice, and merge back. -/
theorem ward_slice_roundtrip (arena off : BitVec 64) (ws ys : List (BitVec 32))
    (len : Nat) (R : Mem 64 → Prop) (m : Mem 64)
    (hlen : off.toNat + len ≤ ws.length) (hy : ys.length = len)
    (hm : (array (t := i32) arena ws ⋆ R) m) :
    ∃ F : Mem 64 → Prop,
      (array (t := i32) (arena + (off <<< 2)) ((ws.drop off.toNat).take len) ⋆ F) m ∧
      ∀ m', (array (t := i32) (arena + (off <<< 2)) ys ⋆ F) m' →
        (array (t := i32) arena
          (ws.take off.toNat ++ ys ++ ws.drop (off.toNat + len)) ⋆ R) m' := by
  rw [ward_slice_focus arena ws hlen] at hm
  refine ⟨_, by c0_frame, fun m' hm' => ?_⟩
  rw [ward_slice_replace arena ws ys hlen hy]
  c0_frame

/-! ## v2.3b: Plain-array backwards compatibility (`a[i + 1]` priority and `a[0]` without
global `BitVec.add_zero` rewriting) -/

c0_decl! compat "
u32 arr32_get_i1(u64 a, u64 i) { return ((u32 *)a)[i + 1]; }
void arr32_set_i1(u64 a, u64 i, u32 v) { ((u32 *)a)[i + 1] = v; }
u64 arr64_get_i1(u64 a, u64 i) { return ((u64 *)a)[i + 1]; }
u32 arr32_rw_zero(u64 a, u32 v) {
  u32 old = ((u32 *)a)[0];
  ((u32 *)a)[0] = v;
  return old;
}
u64 arr64_rw_zero(u64 a, u64 v) {
  u64 old = ((u64 *)a)[0];
  ((u64 *)a)[0] = v;
  return old;
}
u8 arr8_get_zero(u64 a) { return ((u8 *)a)[0]; }
u32 arr32_deref_zero(u64 a) { return *(u32 *)a + *(u32 *)(a + 0ULL); }
"

theorem arr32_get_i1_wp (Γ : Env) (a i : BitVec 64) (ws : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hi : i.toNat + 1 < ws.length) (hm : (array (t := i32) a ws ⋆ R) m)
    (hQ : Q (ws[(i + 1#64).toNat]'(by simp [bv_c0]; omega), ()) m) :
    Func.wp Γ arr32_get_i1_body (a, i, ()) m Q X := by
  c0_steps!
  exact hQ

theorem arr32_set_i1_wp (Γ : Env) (a i : BitVec 64) (v : BitVec 32) (ws : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post []) (X : XPost)
    (hi : i.toNat + 1 < ws.length) (hm : (array (t := i32) a ws ⋆ R) m)
    (hQ : ∀ m', (array (t := i32) a (ws.set (i + 1#64).toNat v) ⋆ R) m' → Q () m') :
    Func.wp Γ arr32_set_i1_body (a, i, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem arr64_get_i1_wp (Γ : Env) (a i : BitVec 64) (ws : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hi : i.toNat + 1 < ws.length) (hm : (array64 a ws ⋆ R) m)
    (hQ : Q (ws[(i + 1#64).toNat]'(by simp [bv_c0]; omega), ()) m) :
    Func.wp Γ arr64_get_i1_body (a, i, ()) m Q X := by
  c0_steps!
  exact hQ

theorem arr32_rw_zero_wp (Γ : Env) (a : BitVec 64) (v : BitVec 32) (ws : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (h0 : 0 < ws.length) (hm : (array (t := i32) a ws ⋆ R) m)
    (hQ : ∀ m', (array (t := i32) a (ws.set 0 v) ⋆ R) m' → Q (ws[0]'h0, ()) m') :
    Func.wp Γ arr32_rw_zero_body (a, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem arr64_rw_zero_wp (Γ : Env) (a v : BitVec 64) (ws : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (h0 : 0 < ws.length) (hm : (array64 a ws ⋆ R) m)
    (hQ : ∀ m', (array64 a (ws.set 0 v) ⋆ R) m' → Q (ws[0]'h0, ()) m') :
    Func.wp Γ arr64_rw_zero_body (a, v, ()) m Q X := by
  c0_steps!
  exact hQ _ (by c0_frame)

theorem arr8_get_zero_wp (Γ : Env) (a : BitVec 64) (bs : List (BitVec 8))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i8]) (X : XPost)
    (h0 : 0 < bs.length) (hm : (array (t := i8) a bs ⋆ R) m)
    (hQ : Q (bs[0]'h0, ()) m) :
    Func.wp Γ arr8_get_zero_body (a, ()) m Q X := by
  c0_steps!
  exact hQ

theorem arr32_deref_zero_wp (Γ : Env) (a : BitVec 64) (ws : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (h0 : 0 < ws.length) (hm : (array (t := i32) a ws ⋆ R) m)
    (hQ : Q (ws[0]'h0 + ws[0]'h0, ()) m) :
    Func.wp Γ arr32_deref_zero_body (a, ()) m Q X := by
  c0_steps!
  exact hQ

/-! ## v2.4: Crisp diagnostic reporting on untagged / non-matching `load` / `store` goals -/

/-- Intentionally untagged footprint predicate for testing diagnostic error messages. -/
def RawBox (p v : BitVec 64) : Mem 64 → Prop := cell (t := i64) p v

c0_decl! diag "
u64 diag_load(u64 p) { return *(u64 *)p; }
void diag_store(u64 p, u64 v) { *(u64 *)p = v; }
"

private meta def expectTacticErrContains (needles : List String) (tac : Lean.TSyntax `tactic) :
    Lean.Elab.Tactic.TacticM Unit := do
  let s ← Lean.Elab.Tactic.saveState
  try
    Lean.Elab.Tactic.evalTactic tac
    s.restore
    throwError "expected tactic failure, but tactic succeeded"
  catch e =>
    let msg ← e.toMessageData.toString
    s.restore
    for needle in needles do
      unless (msg.splitOn needle).length > 1 do
        throwError "diagnostic missing expected substring '{needle}':\n{msg}"

example (Γ : Env) (p v : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hm : (RawBox p v ⋆ R) m) (hQ : Q (v, ()) m) :
    Func.wp Γ diag_load_body (p, ()) m Q X := by
  run_tac do
    expectTacticErrContains ["c0_load", "untagged footprints", "RawBox"] (← `(tactic| c0_steps!))
  -- Plain `c0_steps` unfolds `Func.wp`, stops cleanly at `.load`, and errors on retry:
  c0_steps
  run_tac do
    expectTacticErrContains ["c0_load", "untagged footprints", "RawBox"] (← `(tactic| c0_steps))
  unfold RawBox at hm
  c0_steps!
  exact hQ

example (Γ : Env) (p v0 v : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post []) (X : XPost) (hm : (RawBox p v0 ⋆ R) m)
    (hQ : ∀ m', (RawBox p v ⋆ R) m' → Q () m') :
    Func.wp Γ diag_store_body (p, v, ()) m Q X := by
  run_tac do
    expectTacticErrContains ["c0_store", "untagged footprints", "RawBox"] (← `(tactic| c0_steps!))
  unfold RawBox at hm
  c0_steps!
  exact hQ _ (by unfold RawBox; c0_frame)

example (Γ : Env) (arena : BitVec 64) (off k : BitVec 32) (ws : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hm : (array (t := i32) arena ws ⋆ R) m)
    (hQ : ∀ hi : off.toNat + k.toNat < ws.length, Q (ws[off.toNat + k.toNat]'hi, ()) m)
    (hi : off.toNat + k.toNat < ws.length) :
    Func.wp Γ ward_u32_shl2_read_body (arena, off, k, ()) m Q X := by
  revert hi
  run_tac do
    expectTacticErrContains ["c0_load", "side goal failed"]
      (← `(tactic| (intro h; clear h; c0_steps!)))
  intro hi
  c0_steps!
  exact hQ hi

section O1MemAndMData

local elab "wrap_hyp_mdata" h:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError "unknown hypothesis {h.getId}"
    let ty ← Lean.instantiateMVars decl.type
    let g ← Lean.Elab.Tactic.getMainGoal
    let g' ← g.changeLocalDecl decl.fvarId (Lean.mkMData {} ty) (checkDefEq := false)
    Lean.Elab.Tactic.replaceMainGoal [g']

local elab "wrap_goal_mdata" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let g' ← g.change (Lean.mkMData {} ty) (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [g']

local elab "solve_load_with_c0step" : tactic => do
  LeanQbe.T.C0Step.memSolve true (← Lean.Elab.Tactic.getMainGoal)

local elab "solve_store_with_c0step" : tactic => do
  LeanQbe.T.C0Step.memSolve false (← Lean.Elab.Tactic.getMainGoal)

def O1FP (p : BitVec 64) (a : List (Val i32)) : Mem 64 → Prop :=
  array (t := i32) p a

@[scoped c0_load] theorem o1fp_bad_any {p addr : BitVec 64} {a : List (Val i32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hbad : False) (_hm : (O1FP p a ⋆ R) m) :
    loadVal m i32 addr = some 0#32 :=
  False.elim hbad

@[scoped c0_load] theorem o1fp_good_off0 {p : BitVec 64} {a : List (Val i32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < a.length) (hm : (O1FP p a ⋆ R) m) :
    loadVal m i32 (p + 0#64) = some (a[0]'h0) := by
  dsimp only [O1FP] at hm
  solve_load_with_c0step

@[scoped c0_store] theorem o1fp_store_any {p addr : BitVec 64} {a : List (Val i32)}
    {v : Val i32} {R : Mem 64 → Prop} {m : Mem 64} (hbad : False)
    (_hm : (O1FP p a ⋆ R) m) :
    storeOk m i32 addr ∧ (O1FP p a ⋆ R) (storeMem m i32 addr v) :=
  False.elim hbad

@[scoped c0_store] theorem o1fp_store_off0 {p : BitVec 64} {a : List (Val i32)}
    {v : Val i32} {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < a.length)
    (hm : (O1FP p a ⋆ R) m) :
    storeOk m i32 (p + 0#64) ∧
      (O1FP p (a.set 0 v) ⋆ R) (storeMem m i32 (p + 0#64) v) := by
  dsimp only [O1FP] at hm
  change storeOk m i32 (p + 0#64) ∧
    (array (t := i32) p (a.set 0 v) ⋆ R) (storeMem m i32 (p + 0#64) v)
  solve_store_with_c0step

def O1FallbackFP (p : BitVec 64) (a : List (Val i32)) : Mem 64 → Prop :=
  array (t := i32) p a

@[reducible] def opaqueZeroPtr (p : BitVec 64) : BitVec 64 := p + 0#64

@[scoped c0_load] theorem o1fb_load_opaque {p : BitVec 64} {a : List (Val i32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < a.length)
    (hm : (O1FallbackFP p a ⋆ R) m) :
    loadVal m i32 (opaqueZeroPtr p) = some (a[0]'h0) := by
  dsimp only [O1FallbackFP, opaqueZeroPtr] at hm ⊢
  solve_load_with_c0step

theorem o1_mem_addr_dispatch_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {p : BitVec 64} {a : List (Val i32)} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : 0 < a.length) (hm : (O1FP p a ⋆ R) m)
    (hQ : ∀ m', (O1FP p (a.set 0 (a[0]'h0 + 1#32)) ⋆ R) m' →
      Q ((a[0]'h0 + 1#32), ()) m') :
    wp Γ Q X
      (.load i32 (Arg.imm (p + 0#64)) fun x =>
        .let_ (op2 (.add i32) (Arg.var x) (Arg.imm 1#32)) fun (y, _) =>
          .store (Arg.var y) (Arg.imm (p + 0#64)) (.ret (Arg.var y, ()))) m := by
  c0_steps!
  exact hQ _ hm

theorem o1_mem_pass2_fallback_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {p : BitVec 64} {a : List (Val i32)} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : 0 < a.length) (hm : (O1FallbackFP p a ⋆ R) m)
    (hQ : Q (a[0]'h0, ()) m) :
    wp Γ Q X (.load i32 (Arg.imm (p + 0#64)) fun x => .ret (Arg.var x, ())) m := by
  c0_steps!
  exact hQ

theorem mem_solve_mdata_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {p : BitVec 64} {a : List (Val i32)} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : 0 < a.length) (hm : (array (t := i32) p a ⋆ R) m)
    (hQ : ∀ m', (array (t := i32) p (a.set 0 (a[0]'h0)) ⋆ R) m' → Q (a[0]'h0, ()) m') :
    wp Γ Q X
      (.load i32 (Arg.imm (p + 0#64)) fun x =>
        .store (Arg.var x) (Arg.imm (p + 0#64)) (.ret (Arg.var x, ()))) m := by
  wrap_hyp_mdata hm
  refine wp_load_of (v := a[0]'h0) ?_ ?_
  · wrap_goal_mdata
    solve_load_with_c0step
  · refine wp_store_sep (P := array (t := i32) p (a.set 0 (a[0]'h0))) (R := R) ?_ ?_
    · wrap_goal_mdata
      solve_store_with_c0step
    · intro m' hm'
      c0_steps!
      exact hQ m' hm'

end O1MemAndMData

#print axioms nested_step_wp
#print axioms deep_read_bump_wp
#print axioms single_swap_wp
#print axioms sdiv_srem_pos_wp
#print axioms ptr_diff_u32_wp
#print axioms arith_ext_wp
#print axioms ward_shl2_rw_wp
#print axioms ward_clause_swap_wp
#print axioms word64_off_shl3_rw_wp
#print axioms ward_slice_roundtrip
#print axioms arr32_get_i1_wp
#print axioms arr32_set_i1_wp
#print axioms arr64_get_i1_wp
#print axioms arr32_rw_zero_wp
#print axioms arr64_rw_zero_wp
#print axioms arr8_get_zero_wp
#print axioms arr32_deref_zero_wp
#print axioms o1_mem_addr_dispatch_wp
#print axioms o1_mem_pass2_fallback_wp
#print axioms mem_solve_mdata_wp

end LeanQbeTest.T.C0StepTest
