module

public import LeanQbe.T.Logic.Ops
public import LeanQbe.T.Logic.Vec
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.BitVec

/-!
# Proof rules and `wp_unfold` tactics for `LeanQbe.T` (`T4`)

* Block-projection helpers (`Blocks.get_here`, `Blocks.get_there`).
* Group-matched loop/join/unroll rules (`wp_loop_group`, `wp_join_group`, `wp_loop_break_group`,
  `wp_unroll_group`) that unify directly with `tqbe`-elaborated `Expr.group` terms.
* Memory-backed `wp` load/store helpers (`wp_load_cell`, `wp_store_cell`, `wp_load_cell64`,
  `wp_store_cell64`, `wp_load_array64`, `wp_store_array64`).
* `t_wp_unfold` (plus `scoped` alias `wp_unfold` inside `LeanQbe.T`): unfolds straight-line `wp`,
  reduces `vals` / `Prod.fst` / `Prod.snd` / `Arg.val`, and stops at `group`, `call`, and
  multi-result/UB arithmetic (`addc`, `subb`, `umulw`, `smulw`, `udiv`, `sdiv`, `urem`, `srem`).
* `t_wp_unfold_all` (`wp_unfold_all`): also unfolds `addc`/`subb`/`umulw`/`smulw`/`udiv`/`sdiv`/`urem`/`srem`.
* `t_wp_step`, `t_branch_t`, `t_branch_f` (with `scoped` `wp_step`, `branch_t`, `branch_f`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `Blocks.get` simplification -/

@[simp] theorem Blocks.get_here {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    {sig : List (List Ty)} (b : Tup V ts → Expr V L rs) (bs : Blocks V L rs sig)
    (xs : Tup V ts) : (Blocks.cons b bs).get .here xs = b xs := rfl

@[simp] theorem Blocks.get_there {V : Ty → Type} {L : List Ty → Type} {rs ts hd : List Ty}
    {sig : List (List Ty)} (b : Tup V hd → Expr V L rs) (bs : Blocks V L rs sig)
    (i : Member ts sig) (xs : Tup V ts) :
    (Blocks.cons b bs).get (.there i) xs = bs.get i xs := rfl

/-! ## Group-matched loop, join, and unroll rules -/

/-- One-block loop rule matching `Expr.group (sig := [ts]) bodies entry` directly
(no higher-order unification required on `tqbe`-elaborated `loop` terms). -/
theorem wp_loop_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : Nat → Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) n xs m,
      (∀ n' ys m', n' < n → Inv n' ys m' → J ys m') →
      Inv n xs m →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts),
      (∀ n xs m, Inv n xs m → J xs m) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m := by
  simp only [wp]
  intro Js hc
  rcases Js with ⟨J, ⟨⟩⟩
  cases hcons : bodies (J, ()) with
  | cons b bs =>
    have hc' : ∀ xs m, wp Γ Q X (b xs) m → J xs m := by
      rw [hcons] at hc
      exact hc.1
    apply hentry J
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro xs m hinv
      refine hc' xs m ?_
      have hb := hbody J n xs m (fun n' ys m' h => ih n' h ys m') hinv
      simpa [hcons] using hb

/-- Forward join-point rule matching `Expr.group (sig := [ts]) bodies entry` directly. -/
theorem wp_join_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) xs m, P xs m → wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts), (∀ xs m, P xs m → J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group (fun _ => P) (fun J _ xs m _ h => hbody J xs m h) fun J hJ => hentry J (hJ 0)

/-- Combined loop-with-break rule matching `tqbe`'s `loop ... -> @brk ... { ... }` sugar. -/
theorem wp_loop_break_group {Γ : Env} {rs brkTs lpTs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    (BrkPost : Tup Val brkTs → Mem 64 → Prop)
    (Inv : Nat → Tup Val lpTs → Mem 64 → Prop)
    (hafter : ∀ (B : Cont brkTs) xs m, BrkPost xs m →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here xs) m)
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) n xs m,
      (∀ r m', BrkPost r m' → B r m') →
      (∀ n' ys m', n' < n → Inv n' ys m' → L ys m') →
      Inv n xs m →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here xs) m)
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ r m', BrkPost r m' → B r m') →
      (∀ n xs m, Inv n xs m → L xs m) →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_join_group BrkPost hafter fun B hB =>
    wp_loop_group Inv (fun L n xs m hL hinv => hbody B L n xs m hB hL hinv)
      fun L hL => hentry B L hB hL

/-- Unrolling rule for a 1-block group (for concrete/bounded step-by-step execution). -/
theorem wp_unroll_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (h : ∀ (J : Cont ts),
      (∀ xs m', wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m' → J xs m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m := by
  simp only [wp]
  intro Js hc
  rcases Js with ⟨J, ⟨⟩⟩
  cases hcons : bodies (J, ()) with
  | cons b bs =>
    rw [hcons] at hc
    refine h J fun xs m' hb => hc.1 xs m' ?_
    simpa [hcons] using hb

/-! ## Memory-backed `wp` load and store helpers -/

section
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}

theorem wp_load_cell {t : Ty} {a : Arg Val i64} {v : Val t} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val t → Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64) (hm : (cell a.val v ⋆ R) m)
    (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load t a k) m :=
  ⟨v, loadVal_cell hb hm, hk⟩

theorem wp_store_cell {t : Ty} {v0 : Val t} {v : Arg Val t} {a : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64) (hm : (cell a.val v0 ⋆ R) m)
    (hk : ∀ m', (cell a.val v.val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  let ⟨hok, hm'⟩ := store_cell v.val hb hm
  ⟨hok, hk _ hm'⟩

theorem wp_load_cell64 {a : Arg Val i64} {v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : BitVec 64 → Expr Val Cont rs}
    (hm : (cell64 a.val v ⋆ R) m) (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load i64 a k) m :=
  ⟨v, loadVal_cell64 hm, hk⟩

theorem wp_store_cell64 {v0 : BitVec 64} {v a : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Expr Val Cont rs}
    (hm : (cell64 a.val v0 ⋆ R) m)
    (hk : ∀ m', (cell64 a.val v.val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  let ⟨hok, hm'⟩ := store_cell64 v.val hm
  ⟨hok, hk _ hm'⟩

theorem wp_load_array {t : Ty} {base : BitVec 64} {xs : List (Val t)} {i : Nat}
    {a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val t → Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64)
    (heq : a.val = base + BitVec.ofNat 64 (t.bytes * i)) (hi : i < xs.length)
    (hm : (array base xs ⋆ R) m) (hk : wp Γ Q X (k xs[i]) m) :
    wp Γ Q X (.load t a k) m :=
  ⟨xs[i], heq ▸ loadVal_array hb hi hm, hk⟩

theorem wp_store_array {t : Ty} {base : BitVec 64} {xs : List (Val t)} {i : Nat}
    {v : Arg Val t} {a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64)
    (heq : a.val = base + BitVec.ofNat 64 (t.bytes * i)) (hi : i < xs.length)
    (hm : (array base xs ⋆ R) m)
    (hk : ∀ m', (array base (xs.set i v.val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  let ⟨hok, hm'⟩ := store_array v.val hb hi hm
  ⟨heq ▸ hok, hk _ (heq ▸ hm')⟩

theorem wp_load_array64 {base : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : BitVec 64 → Expr Val Cont rs}
    (heq : a.val = base + BitVec.ofNat 64 (8 * i)) (hi : i < xs.length)
    (hm : (array64 base xs ⋆ R) m) (hk : wp Γ Q X (k xs[i]) m) :
    wp Γ Q X (.load i64 a k) m :=
  ⟨xs[i], heq ▸ loadVal_array64 hi hm, hk⟩

theorem wp_store_array64 {base : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {v a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Expr Val Cont rs}
    (heq : a.val = base + BitVec.ofNat 64 (8 * i)) (hi : i < xs.length)
    (hm : (array64 base xs ⋆ R) m)
    (hk : ∀ m', (array64 base (xs.set i v.val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  let ⟨hok, hm'⟩ := store_array64 v.val hi hm
  ⟨heq ▸ hok, hk _ (heq ▸ hm')⟩

end

/-! ## `wp_unfold`, `wp_unfold_all`, `wp_step`, `branch_t`, `branch_f` -/

/-- Shared base simp list for `t_wp_unfold` and `t_wp_unfold_all` (`B6`). -/
macro "t_wp_unfold_with" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk,
    LeanQbe.T.wp_let_copy_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq,
    LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_neg_eq, LeanQbe.T.wp_let_and_eq,
    LeanQbe.T.wp_let_or_eq, LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq,
    LeanQbe.T.wp_let_ternlog_eq, LeanQbe.T.wp_let_shl_eq, LeanQbe.T.wp_let_lshr_eq,
    LeanQbe.T.wp_let_ashr_eq, LeanQbe.T.wp_let_rotl_eq, LeanQbe.T.wp_let_rotr_eq,
    LeanQbe.T.wp_let_fshl_eq, LeanQbe.T.wp_let_fshr_eq, LeanQbe.T.wp_let_bswap_eq,
    LeanQbe.T.wp_let_clz_eq, LeanQbe.T.wp_let_cls_eq, LeanQbe.T.wp_let_rbit_eq,
    LeanQbe.T.wp_let_ctz_eq, LeanQbe.T.wp_let_popcnt_eq, LeanQbe.T.wp_let_cmp_eq,
    LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_blend_eq, LeanQbe.T.wp_let_zext_eq,
    LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq,
    LeanQbe.T.wp_let_udiv0_eq, LeanQbe.T.wp_let_sdiv0_eq, LeanQbe.T.wp_let_mkpair_eq,
    LeanQbe.T.wp_let_unpair_eq, LeanQbe.T.wp_let_bitcast_eq,
    LeanQbe.T.wp_let_shufd_eq, LeanQbe.T.wp_let_shufb_eq, LeanQbe.T.wp_let_alignr_eq,
    LeanQbe.T.wp_let_blendw_eq, LeanQbe.T.wp_let_sha256rnds2_eq,
    LeanQbe.T.wp_let_sha256msg1_eq, LeanQbe.T.wp_let_sha256msg2_eq,
    LeanQbe.T.wp_let_fneg_eq, LeanQbe.T.wp_let_fabs_eq, LeanQbe.T.wp_let_fcmp_eq,
    LeanQbe.T.wp_let_uitofp_eq, LeanQbe.T.wp_let_sitofp_eq,
    LeanQbe.T.wp_load, LeanQbe.T.wp_store, LeanQbe.T.wp_jnz, LeanQbe.T.wp_jump,
    LeanQbe.T.wp_ret, LeanQbe.T.wp_exit,
    LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
    LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge, LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle,
    LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there,
    LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
    LeanQbe.T.Ty.bswapOk_vec, LeanQbe.T.Ty.bswapOk,
    LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
    LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq,
    LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_slt_eq, LeanQbe.T.evalBits_sle_eq,
    LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
    LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
    LeanQbe.T.evalBool_ult_eq, LeanQbe.T.evalBool_ule_eq, LeanQbe.T.evalBool_ugt_eq,
    LeanQbe.T.evalBool_uge_eq, LeanQbe.T.evalBool_slt_eq, LeanQbe.T.evalBool_sle_eq,
    LeanQbe.T.evalBool_sgt_eq, LeanQbe.T.evalBool_sge_eq,
    LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3, LeanQbe.T.liftCmp, LeanQbe.T.blendV,
    LeanQbe.T.liftFCmp, LeanQbe.T.shl_three,
    cast_eq, ite_self, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
    true_and, and_true, false_implies, true_implies, Option.some.injEq, exists_eq_left',
    decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne, bne_eq_false_iff_eq, beq_self_eq_true,
    BitVec.reduceToNat, Nat.reduceMod, Nat.reduceLeDiff,
    $extra,*])

/-- Unfold `wp` over straight-line `LeanQbe.T` code (both `tqbe` `Op.mk` and manual `op1`/`2`/`3`),
reducing `vals`, `Prod.fst`/`Prod.snd`, `Arg.val`, and pure 1-result/pair ops while stopping at
`group`, `call`, and `addc`/`subb`/`umulw`/`smulw`/`udiv`/`sdiv`/`urem`/`srem`. -/
macro "t_wp_unfold" : tactic =>
  `(tactic| t_wp_unfold_with [])

/-- Like `t_wp_unfold`, but also unfolds `addc`, `subb`, `umulw`, `smulw`, `udiv`, `sdiv`,
`urem`, `srem`, and relational/converting float ops. -/
macro "t_wp_unfold_all" : tactic =>
  `(tactic| t_wp_unfold_with [
    LeanQbe.T.wp_let_addc_eq, LeanQbe.T.wp_let_subb_eq, LeanQbe.T.wp_let_umulw_eq,
    LeanQbe.T.wp_let_smulw_eq, LeanQbe.T.wp_let_udiv_eq, LeanQbe.T.wp_let_sdiv_eq,
    LeanQbe.T.wp_let_urem_eq, LeanQbe.T.wp_let_srem_eq,
    LeanQbe.T.wp_let_fadd_eq, LeanQbe.T.wp_let_fsub_eq, LeanQbe.T.wp_let_fmul_eq,
    LeanQbe.T.wp_let_fdiv_eq, LeanQbe.T.wp_let_ffma_eq, LeanQbe.T.wp_let_fsqrt_eq,
    LeanQbe.T.wp_let_fptoui_eq, LeanQbe.T.wp_let_fptosi_eq, LeanQbe.T.wp_let_fcvt_eq])

macro "t_wp_step" h:term : tactic =>
  `(tactic| ((first | refine $h _ ?_ | refine $h _ _ ?_ | refine $h _ _ _ ?_ | refine $h _ _ _ _ ?_ | refine $h _ _ _ _ _ ?_); t_wp_unfold))

macro "t_branch_t" t:tacticSeq : tactic =>
  `(tactic| refine ⟨fun _ => by $t, fun hc => by first | contradiction | exact absurd hc (by decide) | exact absurd (by decide) hc | exact absurd rfl hc | exact absurd rfl hc.symm⟩)

macro "t_branch_f" t:tacticSeq : tactic =>
  `(tactic| refine ⟨fun hc => by first | contradiction | exact absurd hc (by decide) | exact absurd (by decide) hc | exact absurd rfl hc | exact absurd rfl hc.symm, fun _ => by $t⟩)

scoped macro "wp_unfold" : tactic => `(tactic| t_wp_unfold)
scoped macro "wp_unfold_all" : tactic => `(tactic| t_wp_unfold_all)
scoped macro "wp_step" h:term : tactic => `(tactic| t_wp_step $h)
scoped macro "branch_t" t:tacticSeq : tactic => `(tactic| t_branch_t $t)
scoped macro "branch_f" t:tacticSeq : tactic => `(tactic| t_branch_f $t)

end LeanQbe.T
