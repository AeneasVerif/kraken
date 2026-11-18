module

public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Logic.Arith

/-!
# Operation-spec lemmas and `vals`/`Op.mk` normalization (`T4`)

* `Op.mk`-based `wp_let_mk1`/`2`/`3`, `op1`/`op2`/`op3` normalization (`op1_eq_mk`, ...),
  `vals_nil`/`vals_cons`, and category wrappers (`wp_let_unary`, `wp_let_binary`, `wp_let_ternary`,
  `wp_let_cmp`, `wp_let_select`, `wp_let_cast`).
* `wp_<op>` lemmas in the `wp_addc` style (named result variables, one crisp fact per result)
  for every scalar opcode in `OpCode`, including `wp_smulw` (via `smulw_toInt`), `wp_addc_mk`,
  `wp_subb_mk`, `wp_umulw_mk`, and scalar float opcodes.
* Per-opcode `wp_let_<op>_eq` rewrite equations for `wp_unfold` / `wp_unfold_all`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `vals`, `Op.mk`, and `wp_let_op*` normalization -/

@[simp] theorem vals_nil (as : Tup (Arg Val) []) : vals (ts := []) as = () := rfl
@[simp] theorem vals_cons {t : Ty} {ts : List Ty} (as : Tup (Arg Val) (t :: ts)) :
    vals (ts := t :: ts) as = (as.1.val, vals as.2) := rfl

theorem op1_eq_mk {V : Ty → Type} {t : Ty} {rs : List Ty} (c : OpCode [t] rs) (a : Arg V t) :
    op1 c a = Op.mk c (a, ()) := rfl

theorem op2_eq_mk {V : Ty → Type} {t u : Ty} {rs : List Ty} (c : OpCode [t, u] rs)
    (a : Arg V t) (b : Arg V u) :
    op2 c a b = Op.mk c (a, b, ()) := rfl

theorem op3_eq_mk {V : Ty → Type} {t u w : Ty} {rs : List Ty} (c : OpCode [t, u, w] rs)
    (a : Arg V t) (b : Arg V u) (d : Arg V w) :
    op3 c a b d = Op.mk c (a, b, d, ()) := rfl

section
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}

theorem wp_let_op {sig ts} (c : OpCode sig ts) (args : Tup (Arg Val) sig)
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk c args) k) m = c.wp (vals args) (fun r => wp Γ Q X (k r) m) := rfl

theorem wp_let_mk1 {t ts} (c : OpCode [t] ts) (args : Tup (Arg Val) [t])
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk c args) k) m = c.wp (args.1.val, ()) (fun r => wp Γ Q X (k r) m) := by
  rcases args with ⟨a, ⟨⟩⟩; rfl

theorem wp_let_mk2 {t u ts} (c : OpCode [t, u] ts) (args : Tup (Arg Val) [t, u])
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk c args) k) m =
      c.wp (args.1.val, args.2.1.val, ()) (fun r => wp Γ Q X (k r) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; rfl

theorem wp_let_mk3 {t u w ts} (c : OpCode [t, u, w] ts) (args : Tup (Arg Val) [t, u, w])
    (k : Tup Val ts → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk c args) k) m =
      c.wp (args.1.val, args.2.1.val, args.2.2.1.val, ()) (fun r => wp Γ Q X (k r) m) := by
  rcases args with ⟨a, b, d, ⟨⟩⟩; rfl

theorem wp_let_unary {t ts} (c : OpCode [t] ts) (a : Arg Val t)
    (k : Tup Val ts → Expr Val Cont rs)
    (h : c.wp (a.val, ()) (fun r => wp Γ Q X (k r) m)) :
    wp Γ Q X (.let_ (Op.mk c (a, ())) k) m := by
  rw [wp_let_mk1]; exact h

theorem wp_let_binary {t u ts} (c : OpCode [t, u] ts) (a : Arg Val t) (b : Arg Val u)
    (k : Tup Val ts → Expr Val Cont rs)
    (h : c.wp (a.val, b.val, ()) (fun r => wp Γ Q X (k r) m)) :
    wp Γ Q X (.let_ (Op.mk c (a, b, ())) k) m := by
  rw [wp_let_mk2]; exact h

theorem wp_let_ternary {t u w ts} (c : OpCode [t, u, w] ts) (a : Arg Val t) (b : Arg Val u)
    (d : Arg Val w) (k : Tup Val ts → Expr Val Cont rs)
    (h : c.wp (a.val, b.val, d.val, ()) (fun r => wp Γ Q X (k r) m)) :
    wp Γ Q X (.let_ (Op.mk c (a, b, d, ())) k) m := by
  rw [wp_let_mk3]; exact h

theorem wp_let_cmp (o : CmpOp) (t : Ty) {mt : Ty} (hm : mt = t.mask) (a b : Arg Val t)
    (k : Tup Val [mt] → Expr Val Cont rs) (ht : t.hasFloat = false)
    (h : wp Γ Q X
      (k (cast (congrArg (fun u => Tup Val [u]) hm.symm)
        (liftCmp o.evalBits o.evalBool t a.val b.val, ()))) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o t mt hm) (a, b, ())) k) m := by
  subst hm
  simpa [wp_let_mk2, OpCode.wp_cmp, ht] using h

theorem wp_let_select (t : Ty) (c : Arg Val .bool) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : wp Γ Q X (k (if c.val then a.val else b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.select t) (c, a, b, ())) k) m := by
  simpa [wp_let_mk3, OpCode.wp_select] using h

theorem wp_let_cast {mW nW : Nat} (c : OpCode [.bits mW] [.bits nW]) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : c.wp (a.val, ()) (fun r => wp Γ Q X (k r) m)) :
    wp Γ Q X (.let_ (Op.mk c (a, ())) k) m := by
  rw [wp_let_mk1]; exact h

/-! ## Per-opcode `wp_let_*_eq` equations (for `wp_unfold` / `wp_unfold_all`) -/

theorem wp_let_copy_eq (t : Ty) (args : Tup (Arg Val) [t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.copy t) args) k) m = wp Γ Q X (k (args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_add_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.add t) args) k) m =
      if t.hasFloat then False else wp Γ Q X (k (lift2 (· + ·) (· ^^ ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_sub_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sub t) args) k) m =
      if t.hasFloat then False else wp Γ Q X (k (lift2 (· - ·) (· ^^ ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_mul_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.mul t) args) k) m =
      if t.hasFloat then False else wp Γ Q X (k (lift2 (· * ·) (· && ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_neg_eq (t : Ty) (args : Tup (Arg Val) [t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.neg t) args) k) m =
      if t.hasFloat then False else wp Γ Q X (k (lift1 (- ·) id t args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_and_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.and t) args) k) m =
      wp Γ Q X (k (lift2 (· &&& ·) (· && ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_or_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.or t) args) k) m =
      wp Γ Q X (k (lift2 (· ||| ·) (· || ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_xor_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.xor t) args) k) m =
      wp Γ Q X (k (lift2 (· ^^^ ·) (· ^^ ·) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_not_eq (t : Ty) (args : Tup (Arg Val) [t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.not t) args) k) m =
      wp Γ Q X (k (lift1 (~~~ ·) (! ·) t args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_ternlog_eq (t : Ty) (imm : BitVec 8) (args : Tup (Arg Val) [t, t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.ternlog t imm) args) k) m =
      wp Γ Q X (k (lift3 (fun x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t args.1.val args.2.1.val args.2.2.1.val, ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_shl_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.shl t) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X (k (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_lshr_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.lshr t) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X (k (lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_ashr_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.ashr t) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X (k (lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_rotl_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.rotl t) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X (k (lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_rotr_eq (t : Ty) (args : Tup (Arg Val) [t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.rotr t) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X (k (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t args.1.val args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fshl_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fshl n) args) k) m =
      wp Γ Q X (k ((((args.1.val ++ args.2.1.val) <<< (args.2.2.1.val.toNat % n)).extractLsb' n n), ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_fshr_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fshr n) args) k) m =
      wp Γ Q X (k ((((args.1.val ++ args.2.1.val) >>> (args.2.2.1.val.toNat % n)).extractLsb' 0 n), ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_bswap_eq (t : Ty) (args : Tup (Arg Val) [t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.bswap t) args) k) m =
      if !t.bswapOk then False else wp Γ Q X (k (lift1 bswapBits id t args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_clz_eq (n : Nat) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.clz n) args) k) m = wp Γ Q X (k (args.1.val.clz, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_cls_eq (n : Nat) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cls n) args) k) m =
      wp Γ Q X (k ((if args.1.val.msb then (~~~args.1.val).clz else args.1.val.clz) - 1#n, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_rbit_eq (n : Nat) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.rbit n) args) k) m = wp Γ Q X (k (args.1.val.reverse, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_ctz_eq (n : Nat) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.ctz n) args) k) m = wp Γ Q X (k (args.1.val.reverse.clz, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_popcnt_eq (n : Nat) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.popcnt n) args) k) m = wp Γ Q X (k (args.1.val.cpop, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_cmp_eq (o : CmpOp) (t : Ty) {mt : Ty} (hm : mt = t.mask)
    (args : Tup (Arg Val) [t, t]) (k : Tup Val [mt] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp o t mt hm) args) k) m =
      if t.hasFloat then False
      else wp Γ Q X
        (k (cast (congrArg (fun u => Tup Val [u]) hm.symm)
          (liftCmp o.evalBits o.evalBool t args.1.val args.2.1.val, ()))) m := by
  subst hm; rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_select_eq (t : Ty) (args : Tup (Arg Val) [.bool, t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.select t) args) k) m =
      wp Γ Q X (k (if args.1.val then args.2.1.val else args.2.2.1.val, ())) m := by
  rcases args with ⟨c, a, b, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_blend_eq (t : Ty) {mt : Ty} (hm : mt = t.mask)
    (args : Tup (Arg Val) [mt, t, t]) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.blend t mt hm) args) k) m =
      wp Γ Q X (k (blendV t (cast (congrArg Val hm) args.1.val) args.2.1.val args.2.2.1.val, ())) m := by
  subst hm; rcases args with ⟨c, a, b, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_zext_eq (mW nW : Nat) (args : Tup (Arg Val) [.bits mW])
    (k : Tup Val [.bits nW] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.zext mW nW) args) k) m =
      (mW ≤ nW ∧ wp Γ Q X (k (args.1.val.setWidth nW, ())) m) := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_sext_eq (mW nW : Nat) (args : Tup (Arg Val) [.bits mW])
    (k : Tup Val [.bits nW] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) args) k) m =
      (mW ≤ nW ∧ wp Γ Q X (k (args.1.val.signExtend nW, ())) m) := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_trunc_eq (mW nW : Nat) (args : Tup (Arg Val) [.bits mW])
    (k : Tup Val [.bits nW] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.trunc mW nW) args) k) m =
      (nW ≤ mW ∧ wp Γ Q X (k (args.1.val.setWidth nW, ())) m) := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_ofBool_eq (n : Nat) (args : Tup (Arg Val) [.bool])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.ofBool n) args) k) m =
      wp Γ Q X (k (BitVec.ofNat n args.1.val.toNat, ())) m := by
  rcases args with ⟨c, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_udiv0_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.udiv0 n) args) k) m =
      wp Γ Q X (k (if args.2.1.val = 0 then 0 else args.1.val / args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_sdiv0_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sdiv0 n) args) k) m =
      wp Γ Q X (k (if args.2.1.val = 0 then 0 else args.1.val.sdiv args.2.1.val, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_mkpair_eq (a b : Ty) (args : Tup (Arg Val) [a, b])
    (k : Tup Val [.pair a b] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.mkpair a b) args) k) m =
      wp Γ Q X (k ((args.1.val, args.2.1.val), ())) m := by
  rcases args with ⟨x, y, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_unpair_eq (a b : Ty) (args : Tup (Arg Val) [.pair a b])
    (k : Tup Val [a, b] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.unpair a b) args) k) m =
      wp Γ Q X (k (args.1.val.1, args.1.val.2, ())) m := by
  rcases args with ⟨p, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_bitcast_eq (t u : Ty) (h : t.size = u.size) (args : Tup (Arg Val) [t])
    (k : Tup Val [u] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.bitcast t u h) args) k) m =
      wp Γ Q X (k (ofBits u ((toBits t args.1.val).cast h), ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_shufd_eq (t : Ty) (imm : BitVec 8) (args : Tup (Arg Val) [t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.shufd t imm) args) k) m =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        wp Γ Q X (k (ofBits t (shuffleDwords (toBits t args.1.val) imm), ())) m) := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_shufb_eq (t : Ty) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.shufb t) args) k) m =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        wp Γ Q X (k (ofBits t (shuffleBytes (toBits t args.1.val) (toBits t args.2.1.val)), ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_alignr_eq (t : Ty) (imm : BitVec 8) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.alignr t imm) args) k) m =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        wp Γ Q X
          (k (ofBits t (alignBytes (toBits t args.1.val) (toBits t args.2.1.val) imm), ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_blendw_eq (t : Ty) (imm : BitVec 8) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.blendw t imm) args) k) m =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        wp Γ Q X
          (k (ofBits t (blendWords (toBits t args.1.val) (toBits t args.2.1.val) imm), ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_sha256rnds2_eq (args : Tup (Arg Val) [v4i32, v4i32, v4i32])
    (k : Tup Val [v4i32] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk .sha256rnds2 args) k) m =
      wp Γ Q X (k (ofBits v4i32
        (Sha256.rounds2 (toBits v4i32 args.1.val) (toBits v4i32 args.2.1.val)
          (toBits v4i32 args.2.2.1.val)), ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_sha256msg1_eq (args : Tup (Arg Val) [v4i32, v4i32])
    (k : Tup Val [v4i32] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk .sha256msg1 args) k) m =
      wp Γ Q X (k (ofBits v4i32
        (Sha256.msg1 (toBits v4i32 args.1.val) (toBits v4i32 args.2.1.val)), ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_sha256msg2_eq (args : Tup (Arg Val) [v4i32, v4i32])
    (k : Tup Val [v4i32] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk .sha256msg2 args) k) m =
      wp Γ Q X (k (ofBits v4i32
        (Sha256.msg2 (toBits v4i32 args.1.val) (toBits v4i32 args.2.1.val)), ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fneg_eq (t : Ty) (args : Tup (Arg Val) [t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fneg t) args) k) m =
      if !t.isFloatTree then False
      else wp Γ Q X
        (k (lift1 (fun {n} x => x ^^^ (1#n <<< (n - 1))) id t args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_fabs_eq (t : Ty) (args : Tup (Arg Val) [t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fabs t) args) k) m =
      if !t.isFloatTree then False
      else wp Γ Q X
        (k (lift1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) id t args.1.val, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_fcmp_eq (o : FCmpOp) (t : Ty) {mt : Ty} (hm : mt = t.mask)
    (args : Tup (Arg Val) [t, t]) (k : Tup Val [mt] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fcmp o t mt hm) args) k) m =
      if !t.isFloatTree then False
      else wp Γ Q X
        (k (cast (congrArg (fun u => Tup Val [u]) hm.symm)
          (liftFCmp o t args.1.val args.2.1.val, ()))) m := by
  subst hm; rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_uitofp_eq (n : Nat) (f : Fmt) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.float f] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.uitofp n f) args) k) m =
      wp Γ Q X (k (packFloat f (Float.Model.UnpackedFloat.ofInt f.format args.1.val.toNat), ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_sitofp_eq (n : Nat) (f : Fmt) (args : Tup (Arg Val) [.bits n])
    (k : Tup Val [.float f] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sitofp n f) args) k) m =
      wp Γ Q X (k (packFloat f (Float.Model.UnpackedFloat.ofInt f.format args.1.val.toInt), ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

/-! Additional equations for `wp_unfold_all` (carry/mul/div/rem) -/

theorem wp_let_addc_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n, .bool])
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.addc n) args) k) m =
      wp Γ Q X (k (args.1.val + args.2.1.val + BitVec.ofNat n args.2.2.1.val.toNat,
        decide (2 ^ n ≤ args.1.val.toNat + args.2.1.val.toNat + args.2.2.1.val.toNat), ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_subb_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n, .bool])
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.subb n) args) k) m =
      wp Γ Q X (k (args.1.val - args.2.1.val - BitVec.ofNat n args.2.2.1.val.toNat,
        decide (args.1.val.toNat < args.2.1.val.toNat + args.2.2.1.val.toNat), ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_umulw_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.umulw n) args) k) m =
      wp Γ Q X (k (args.1.val * args.2.1.val,
        BitVec.ofNat n (args.1.val.toNat * args.2.1.val.toNat / 2 ^ n), ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_smulw_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.smulw n) args) k) m =
      wp Γ Q X (k (args.1.val * args.2.1.val,
        (BitVec.ofInt (n + n) (args.1.val.toInt * args.2.1.val.toInt)).extractLsb' n n, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_udiv_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.udiv n) args) k) m =
      (args.2.1.val ≠ 0 ∧ wp Γ Q X (k (args.1.val / args.2.1.val, ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_sdiv_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sdiv n) args) k) m =
      (sdivDefined args.1.val args.2.1.val = true ∧
        wp Γ Q X (k (args.1.val.sdiv args.2.1.val, ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_urem_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.urem n) args) k) m =
      (args.2.1.val ≠ 0 ∧ wp Γ Q X (k (args.1.val % args.2.1.val, ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_srem_eq (n : Nat) (args : Tup (Arg Val) [.bits n, .bits n])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.srem n) args) k) m =
      (sdivDefined args.1.val args.2.1.val = true ∧
        wp Γ Q X (k (args.1.val.srem args.2.1.val, ())) m) := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fadd_eq (t : Ty) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fadd t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.add t args.1.val args.2.1.val
        fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fsub_eq (t : Ty) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fsub t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.sub t args.1.val args.2.1.val
        fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fmul_eq (t : Ty) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fmul t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.mul t args.1.val args.2.1.val
        fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_fdiv_eq (t : Ty) (args : Tup (Arg Val) [t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fdiv t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.div t args.1.val args.2.1.val
        fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, b, ⟨⟩⟩; simp [wp_let_mk2]

theorem wp_let_ffma_eq (t : Ty) (args : Tup (Arg Val) [t, t, t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.ffma t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel3 Float.Model.UnpackedFloat.fma t
        args.1.val args.2.1.val args.2.2.1.val fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, b, c, ⟨⟩⟩; simp [wp_let_mk3]

theorem wp_let_fsqrt_eq (t : Ty) (args : Tup (Arg Val) [t])
    (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fsqrt t) args) k) m =
      if !t.isFloatTree then False
      else liftFloatRel1 Float.Model.UnpackedFloat.sqrt t args.1.val
        fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

theorem wp_let_fptoui_eq (f : Fmt) (n : Nat) (args : Tup (Arg Val) [.float f])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fptoui f n) args) k) m =
      (match truncToInt (unpackFloat f args.1.val) with
       | some z => 0 ≤ z ∧ z < 2 ^ n ∧ wp Γ Q X (k (BitVec.ofInt n z, ())) m
       | none => False) := by
  rcases args with ⟨a, ⟨⟩⟩; simp only [wp_let_mk1, OpCode.wp_fptoui]; rfl

theorem wp_let_fptosi_eq (f : Fmt) (n : Nat) (args : Tup (Arg Val) [.float f])
    (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fptosi f n) args) k) m =
      (n ≠ 0 ∧ match truncToInt (unpackFloat f args.1.val) with
       | some z => -(2 ^ (n - 1) : Int) ≤ z ∧ z < (2 ^ (n - 1) : Int) ∧
           wp Γ Q X (k (BitVec.ofInt n z, ())) m
       | none => False) := by
  rcases args with ⟨a, ⟨⟩⟩; simp only [wp_let_mk1, OpCode.wp_fptosi]; rfl

theorem wp_let_fcvt_eq (f g : Fmt) (args : Tup (Arg Val) [.float f])
    (k : Tup Val [.float g] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.fcvt f g) args) k) m =
      convertFloat f g args.1.val fun r => wp Γ Q X (k (r, ())) m := by
  rcases args with ⟨a, ⟨⟩⟩; simp [wp_let_mk1]

/-! ## Named-result scalar operation specs (`wp_addc` style) for every scalar opcode -/

theorem wp_copy {t : Ty} (a : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m := by
  rw [wp_let_copy_eq]; exact h _ rfl

theorem wp_add {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val + b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_add_eq]; exact h _ rfl

theorem wp_add_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val != b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add .bool) (a, b, ())) k) m := by
  rw [wp_let_add_eq]; exact h _ (by cases a.val <;> cases b.val <;> rfl)

theorem wp_add_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· + ·) (· ^^ ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add t) (a, b, ())) k) m := by
  rw [wp_let_add_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_sub {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val - b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_sub_eq]; exact h _ rfl

theorem wp_sub_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val != b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub .bool) (a, b, ())) k) m := by
  rw [wp_let_sub_eq]; exact h _ (by cases a.val <;> cases b.val <;> rfl)

theorem wp_sub_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· - ·) (· ^^ ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub t) (a, b, ())) k) m := by
  rw [wp_let_sub_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_mul {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val * b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_mul_eq]; exact h _ rfl

theorem wp_mul_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val && b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul .bool) (a, b, ())) k) m := by
  rw [wp_let_mul_eq]; exact h _ rfl

theorem wp_mul_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· * ·) (· && ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul t) (a, b, ())) k) m := by
  rw [wp_let_mul_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_neg {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = -a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.neg (.bits n)) (a, ())) k) m := by
  rw [wp_let_neg_eq]; exact h _ rfl

theorem wp_neg_bool (a : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.neg .bool) (a, ())) k) m := by
  rw [wp_let_neg_eq]; exact h _ rfl

theorem wp_neg_ty {t : Ty} (ht : t.hasFloat = false) (a : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift1 (- ·) id t a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.neg t) (a, ())) k) m := by
  rw [wp_let_neg_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_and {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val &&& b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_and_eq]; exact h _ rfl

theorem wp_and_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val && b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and .bool) (a, b, ())) k) m := by
  rw [wp_let_and_eq]; exact h _ rfl

theorem wp_and_ty {t : Ty} (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· &&& ·) (· && ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and t) (a, b, ())) k) m := by
  rw [wp_let_and_eq]; exact h _ rfl

theorem wp_or {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val ||| b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_or_eq]; exact h _ rfl

theorem wp_or_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val || b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or .bool) (a, b, ())) k) m := by
  rw [wp_let_or_eq]; exact h _ rfl

theorem wp_or_ty {t : Ty} (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· ||| ·) (· || ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or t) (a, b, ())) k) m := by
  rw [wp_let_or_eq]; exact h _ rfl

theorem wp_xor {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val ^^^ b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_xor_eq]; exact h _ rfl

theorem wp_xor_bool (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = (a.val != b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor .bool) (a, b, ())) k) m := by
  rw [wp_let_xor_eq]; exact h _ (by cases a.val <;> cases b.val <;> rfl)

theorem wp_xor_ty {t : Ty} (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift2 (· ^^^ ·) (· ^^ ·) t a.val b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor t) (a, b, ())) k) m := by
  rw [wp_let_xor_eq]; exact h _ rfl

theorem wp_not {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = ~~~a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.not (.bits n)) (a, ())) k) m := by
  rw [wp_let_not_eq]; exact h _ rfl

theorem wp_not_bool (a : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = !a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.not .bool) (a, ())) k) m := by
  rw [wp_let_not_eq]; exact h _ rfl

theorem wp_not_ty {t : Ty} (a : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift1 (~~~ ·) (! ·) t a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.not t) (a, ())) k) m := by
  rw [wp_let_not_eq]; exact h _ rfl

theorem wp_ternlog {n : Nat} (imm : BitVec 8) (a b c : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = ternaryLogic a.val b.val c.val imm → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ternlog (.bits n) imm) (a, b, c, ())) k) m := by
  rw [wp_let_ternlog_eq]; exact h _ rfl

theorem wp_ternlog_bool (imm : BitVec 8) (a b c : Arg Val .bool)
    (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ r : Bool, r = ternaryLogicBool a.val b.val c.val imm → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ternlog .bool imm) (a, b, c, ())) k) m := by
  rw [wp_let_ternlog_eq]; exact h _ rfl

theorem wp_ternlog_ty {t : Ty} (imm : BitVec 8) (a b c : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift3 (fun x y z => ternaryLogic x y z imm) (fun x y z => ternaryLogicBool x y z imm)
        t a.val b.val c.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ternlog t imm) (a, b, c, ())) k) m := by
  rw [wp_let_ternlog_eq]; exact h _ rfl

theorem wp_shl {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val <<< (b.val.toNat % n) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_shl_eq]; exact h _ rfl

theorem wp_shl_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl t) (a, b, ())) k) m := by
  rw [wp_let_shl_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_lshr {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val >>> (b.val.toNat % n) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_lshr_eq]; exact h _ rfl

theorem wp_lshr_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr t) (a, b, ())) k) m := by
  rw [wp_let_lshr_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_ashr {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.sshiftRight (b.val.toNat % n) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ashr (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_ashr_eq]; exact h _ rfl

theorem wp_ashr_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ashr t) (a, b, ())) k) m := by
  rw [wp_let_ashr_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_rotl {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.rotateLeft (b.val.toNat % n) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotl (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_rotl_eq]; exact h _ rfl

theorem wp_rotl_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotl t) (a, b, ())) k) m := by
  rw [wp_let_rotl_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_rotr {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.rotateRight (b.val.toNat % n) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotr (.bits n)) (a, b, ())) k) m := by
  rw [wp_let_rotr_eq]; exact h _ rfl

theorem wp_rotr_ty {t : Ty} (ht : t.hasFloat = false) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t,
      r = lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotr t) (a, b, ())) k) m := by
  rw [wp_let_rotr_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_fshl {n : Nat} (a b c : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = ((a.val ++ b.val) <<< (c.val.toNat % n)).extractLsb' n n →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fshl n) (a, b, c, ())) k) m := by
  rw [wp_let_fshl_eq]; exact h _ rfl

theorem wp_fshr {n : Nat} (a b c : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = ((a.val ++ b.val) >>> (c.val.toNat % n)).extractLsb' 0 n →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fshr n) (a, b, c, ())) k) m := by
  rw [wp_let_fshr_eq]; exact h _ rfl

theorem wp_bswap {n : Nat} (hn : n % 8 = 0) (a : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = bswapBits a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.bswap (.bits n)) (a, ())) k) m := by
  rw [wp_let_bswap_eq]; simp only [Ty.bswapOk, hn, beq_self_eq_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  exact h _ rfl

theorem wp_bswap_ty {t : Ty} (ht : t.bswapOk = true) (a : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = lift1 bswapBits id t a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.bswap t) (a, ())) k) m := by
  rw [wp_let_bswap_eq]; simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact h _ rfl

theorem wp_clz {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.clz → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.clz n) (a, ())) k) m := by
  rw [wp_let_clz_eq]; exact h _ rfl

theorem wp_cls {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = (if a.val.msb then (~~~a.val).clz else a.val.clz) - 1#n →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cls n) (a, ())) k) m := by
  rw [wp_let_cls_eq]; exact h _ rfl

theorem wp_rbit {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.reverse → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rbit n) (a, ())) k) m := by
  rw [wp_let_rbit_eq]; exact h _ rfl

theorem wp_ctz {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.reverse.clz → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ctz n) (a, ())) k) m := by
  rw [wp_let_ctz_eq]; exact h _ rfl

theorem wp_popcnt {n : Nat} (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = a.val.cpop → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.popcnt n) (a, ())) k) m := by
  rw [wp_let_popcnt_eq]; exact h _ rfl

theorem wp_cmp {n : Nat} (o : CmpOp)
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = o.evalBits a.val b.val → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) m := by
  rw [wp_let_cmp_eq]; exact h _ rfl

theorem wp_cmp_bool (o : CmpOp)
    (a b : Arg Val .bool) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = o.evalBool a.val b.val → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o .bool .bool rfl) (a, b, ())) k) m := by
  rw [wp_let_cmp_eq]; exact h _ rfl

theorem wp_cmp_ty (o : CmpOp) {t : Ty} (ht : t.hasFloat = false) {mt : Ty} (hm : mt = t.mask)
    (a b : Arg Val t) (k : Tup Val [mt] → Expr Val Cont rs)
    (h : ∀ c : Val t.mask, c = liftCmp o.evalBits o.evalBool t a.val b.val →
      wp Γ Q X (k (cast (congrArg (fun u => Tup Val [u]) hm.symm) (c, ()))) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o t mt hm) (a, b, ())) k) m := by
  subst hm; rw [wp_let_cmp_eq]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h _ rfl

theorem wp_eq {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val = b.val) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .eq a b k h

theorem wp_ne {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val ≠ b.val) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .ne a b k h

theorem wp_ult {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val.toNat < b.val.toNat) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .ult a b k fun c hc => h c (by simpa [evalBits_ult_eq_decide] using hc)

theorem wp_ule {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val.toNat ≤ b.val.toNat) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .ule a b k fun c hc => h c (by simpa [evalBits_ule_eq_decide] using hc)

theorem wp_ugt {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (b.val.toNat < a.val.toNat) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .ugt a b k fun c hc => h c (by simpa [evalBits_ugt_eq_decide] using hc)

theorem wp_uge {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (b.val.toNat ≤ a.val.toNat) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .uge a b k fun c hc => h c (by simpa [evalBits_uge_eq_decide] using hc)

theorem wp_slt {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val.toInt < b.val.toInt) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .slt a b k fun c hc => h c (by simpa [evalBits_slt_eq_decide] using hc)

theorem wp_sle {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (a.val.toInt ≤ b.val.toInt) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sle (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .sle a b k fun c hc => h c (by simpa [evalBits_sle_eq_decide] using hc)

theorem wp_sgt {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (b.val.toInt < a.val.toInt) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sgt (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .sgt a b k fun c hc => h c (by simpa [evalBits_sgt_eq_decide] using hc)

theorem wp_sge {n : Nat}
    (a b : Arg Val (.bits n)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = decide (b.val.toInt ≤ a.val.toInt) → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sge (.bits n) .bool rfl) (a, b, ())) k) m :=
  wp_cmp .sge a b k fun c hc => h c (by simpa [evalBits_sge_eq_decide] using hc)

theorem wp_select {t : Ty} (c : Arg Val .bool) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = (if c.val then a.val else b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.select t) (c, a, b, ())) k) m := by
  rw [wp_let_select_eq]; exact h _ rfl

theorem wp_select_ite {t : Ty} (c : Arg Val .bool) (a b : Arg Val t)
    (k : Tup Val [t] → Expr Val Cont rs)
    (ht : c.val = true → wp Γ Q X (k (a.val, ())) m)
    (hf : c.val = false → wp Γ Q X (k (b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.select t) (c, a, b, ())) k) m := by
  rw [wp_let_select_eq]
  cases hc : c.val
  · simpa using hf hc
  · simpa using ht hc

theorem wp_blend {t : Ty} {mt : Ty} (hm : mt = t.mask)
    (c : Arg Val mt) (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = blendV t (cast (congrArg Val hm) c.val) a.val b.val →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.blend t mt hm) (c, a, b, ())) k) m := by
  subst hm; rw [wp_let_blend_eq]; exact h _ rfl

theorem wp_zext {mW nW : Nat} (hmn : mW ≤ nW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r = a.val.setWidth nW → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext mW nW) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨hmn, h _ rfl⟩

theorem wp_zext_toNat {mW nW : Nat} (hmn : mW ≤ nW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r.toNat = a.val.toNat → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext mW nW) (a, ())) k) m :=
  wp_zext hmn a k fun r hr => h r (by rw [hr, zext_toNat a.val hmn])

theorem wp_sext {mW nW : Nat} (hmn : mW ≤ nW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r = a.val.signExtend nW → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) (a, ())) k) m := by
  rw [wp_let_sext_eq]; exact ⟨hmn, h _ rfl⟩

theorem wp_sext_toInt {mW nW : Nat} (hm : 0 < mW) (hmn : mW ≤ nW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r.toInt = a.val.toInt → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) (a, ())) k) m :=
  wp_sext hmn a k fun r hr => h r (by rw [hr, sext_toInt a.val hm hmn])

theorem wp_trunc {mW nW : Nat} (hnm : nW ≤ mW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r = a.val.setWidth nW → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc mW nW) (a, ())) k) m := by
  rw [wp_let_trunc_eq]; exact ⟨hnm, h _ rfl⟩

theorem wp_trunc_toNat {mW nW : Nat} (hnm : nW ≤ mW) (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs)
    (h : ∀ r : BitVec nW, r.toNat = a.val.toNat % 2 ^ nW → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc mW nW) (a, ())) k) m :=
  wp_trunc hnm a k fun r hr => h r (by rw [hr, trunc_toNat])

theorem wp_ofBool {n : Nat} (c : Arg Val .bool) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = BitVec.ofNat n c.val.toNat → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ofBool n) (c, ())) k) m := by
  rw [wp_let_ofBool_eq]; exact h _ rfl

theorem wp_ofBool_toNat {n : Nat} (hn : 0 < n) (c : Arg Val .bool)
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r.toNat = c.val.toNat → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ofBool n) (c, ())) k) m :=
  wp_ofBool c k fun r hr => h r (by rw [hr, ofBool_toNat hn c.val])

theorem wp_addc_mk {n : Nat} (a b : Arg Val (.bits n)) (c : Arg Val .bool)
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs)
    (h : ∀ (s : BitVec n) (co : Bool),
      co.toNat * 2 ^ n + s.toNat = a.val.toNat + b.val.toNat + c.val.toNat →
      wp Γ Q X (k (s, co, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.addc n) (a, b, c, ())) k) m := by
  rw [wp_let_addc_eq]; exact h _ _ (addc_toNat _ _ _)

theorem wp_subb_mk {n : Nat} (a b : Arg Val (.bits n)) (c : Arg Val .bool)
    (k : Tup Val [.bits n, .bool] → Expr Val Cont rs)
    (h : ∀ (d : BitVec n) (bo : Bool),
      d.toNat + b.val.toNat + c.val.toNat = a.val.toNat + bo.toNat * 2 ^ n →
      wp Γ Q X (k (d, bo, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.subb n) (a, b, c, ())) k) m := by
  rw [wp_let_subb_eq]; exact h _ _ (subb_toNat _ _ _)

theorem wp_umulw_mk {n : Nat} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : ∀ lo hi : BitVec n, hi.toNat * 2 ^ n + lo.toNat = a.val.toNat * b.val.toNat →
      wp Γ Q X (k (lo, hi, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.umulw n) (a, b, ())) k) m := by
  rw [wp_let_umulw_eq]
  refine h _ _ ?_
  dsimp only
  have := (umulw_toNat a.val b.val).1
  rw [Nat.mul_comm] at this
  omega

/-- Signed widening multiplication spec in `wp_addc` style (`#18` #7). -/
theorem wp_smulw {n : Nat} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : ∀ lo hi : BitVec n,
      hi.toInt * (2 ^ n : Int) + (lo.toNat : Int) = a.val.toInt * b.val.toInt →
      wp Γ Q X (k (lo, hi, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.smulw n) (a, b, ())) k) m := by
  rw [wp_let_smulw_eq]
  exact h _ _ (smulw_toInt a.val b.val)

theorem wp_smulw_div_mod {n : Nat} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : ∀ lo hi : BitVec n,
      (lo.toNat : Int) = (a.val.toInt * b.val.toInt) % (2 ^ n : Int) →
      hi.toInt = (a.val.toInt * b.val.toInt) / (2 ^ n : Int) →
      wp Γ Q X (k (lo, hi, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.smulw n) (a, b, ())) k) m := by
  rw [wp_let_smulw_eq]
  exact h _ _ (smulw_lo_toNat a.val b.val) (smulw_hi_toInt a.val b.val)

theorem wp_udiv {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hb : b.val ≠ 0) (h : ∀ r : BitVec n, r = a.val / b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.udiv n) (a, b, ())) k) m := by
  rw [wp_let_udiv_eq]; exact ⟨hb, h _ rfl⟩

theorem wp_sdiv {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hdef : sdivDefined a.val b.val = true)
    (h : ∀ r : BitVec n, r = a.val.sdiv b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sdiv n) (a, b, ())) k) m := by
  rw [wp_let_sdiv_eq]; exact ⟨hdef, h _ rfl⟩

theorem wp_urem {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hb : b.val ≠ 0) (h : ∀ r : BitVec n, r = a.val % b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.urem n) (a, b, ())) k) m := by
  rw [wp_let_urem_eq]; exact ⟨hb, h _ rfl⟩

theorem wp_srem {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hdef : sdivDefined a.val b.val = true)
    (h : ∀ r : BitVec n, r = a.val.srem b.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.srem n) (a, b, ())) k) m := by
  rw [wp_let_srem_eq]; exact ⟨hdef, h _ rfl⟩

theorem wp_udiv0 {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = (if b.val = 0 then 0 else a.val / b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.udiv0 n) (a, b, ())) k) m := by
  rw [wp_let_udiv0_eq]; exact h _ rfl

theorem wp_sdiv0 {n : Nat} (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∀ r : BitVec n, r = (if b.val = 0 then 0 else a.val.sdiv b.val) → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sdiv0 n) (a, b, ())) k) m := by
  rw [wp_let_sdiv0_eq]; exact h _ rfl

theorem wp_mkpair {a b : Ty} (x : Arg Val a) (y : Arg Val b)
    (k : Tup Val [.pair a b] → Expr Val Cont rs)
    (h : ∀ p : Val a × Val b, p = (x.val, y.val) → wp Γ Q X (k (p, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mkpair a b) (x, y, ())) k) m := by
  rw [wp_let_mkpair_eq]; exact h _ rfl

theorem wp_unpair {a b : Ty} (p : Arg Val (.pair a b)) (k : Tup Val [a, b] → Expr Val Cont rs)
    (h : ∀ (x : Val a) (y : Val b), x = p.val.1 → y = p.val.2 → wp Γ Q X (k (x, y, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.unpair a b) (p, ())) k) m := by
  rw [wp_let_unpair_eq]; exact h _ _ rfl rfl

theorem wp_bitcast {t u : Ty} (ht : t.size = u.size) (a : Arg Val t)
    (k : Tup Val [u] → Expr Val Cont rs)
    (h : ∀ r : Val u, r = bitcastVal t u ht a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.bitcast t u ht) (a, ())) k) m := by
  rw [wp_let_bitcast_eq]; exact h _ rfl

theorem wp_bitcast_bits {t u : Ty} (ht : t.size = u.size) (a : Arg Val t)
    (k : Tup Val [u] → Expr Val Cont rs)
    (h : ∀ r : Val u, toBits u r = (toBits t a.val).cast ht → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.bitcast t u ht) (a, ())) k) m :=
  wp_bitcast ht a k fun r hr => h r (by simp [hr, bitcastVal, toBits_ofBits])

/-! ## Shuffle and SHA operation specs -/

theorem wp_shufd {t : Ty} (ht0 : t.size ≠ 0) (ht128 : t.size % 128 = 0) (imm : BitVec 8)
    (a : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = ofBits t (shuffleDwords (toBits t a.val) imm) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shufd t imm) (a, ())) k) m := by
  rw [wp_let_shufd_eq]; exact ⟨ht0, ht128, h _ rfl⟩

theorem wp_shufb {t : Ty} (ht0 : t.size ≠ 0) (ht128 : t.size % 128 = 0)
    (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = ofBits t (shuffleBytes (toBits t a.val) (toBits t b.val)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shufb t) (a, b, ())) k) m := by
  rw [wp_let_shufb_eq]; exact ⟨ht0, ht128, h _ rfl⟩

theorem wp_alignr {t : Ty} (ht0 : t.size ≠ 0) (ht128 : t.size % 128 = 0) (imm : BitVec 8)
    (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = ofBits t (alignBytes (toBits t a.val) (toBits t b.val) imm) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.alignr t imm) (a, b, ())) k) m := by
  rw [wp_let_alignr_eq]; exact ⟨ht0, ht128, h _ rfl⟩

theorem wp_blendw {t : Ty} (ht0 : t.size ≠ 0) (ht128 : t.size % 128 = 0) (imm : BitVec 8)
    (a b : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs)
    (h : ∀ r : Val t, r = ofBits t (blendWords (toBits t a.val) (toBits t b.val) imm) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.blendw t imm) (a, b, ())) k) m := by
  rw [wp_let_blendw_eq]; exact ⟨ht0, ht128, h _ rfl⟩

theorem wp_sha256rnds2 (cdgh abef wk : Arg Val v4i32)
    (k : Tup Val [v4i32] → Expr Val Cont rs)
    (h : ∀ r : Val v4i32, r = ofBits v4i32
      (Sha256.rounds2 (toBits v4i32 cdgh.val) (toBits v4i32 abef.val) (toBits v4i32 wk.val)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk .sha256rnds2 (cdgh, abef, wk, ())) k) m := by
  rw [wp_let_sha256rnds2_eq]; exact h _ rfl

theorem wp_sha256msg1 (w0123 w4 : Arg Val v4i32)
    (k : Tup Val [v4i32] → Expr Val Cont rs)
    (h : ∀ r : Val v4i32, r = ofBits v4i32
      (Sha256.msg1 (toBits v4i32 w0123.val) (toBits v4i32 w4.val)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk .sha256msg1 (w0123, w4, ())) k) m := by
  rw [wp_let_sha256msg1_eq]; exact h _ rfl

theorem wp_sha256msg2 (sums w : Arg Val v4i32)
    (k : Tup Val [v4i32] → Expr Val Cont rs)
    (h : ∀ r : Val v4i32, r = ofBits v4i32
      (Sha256.msg2 (toBits v4i32 sums.val) (toBits v4i32 w.val)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk .sha256msg2 (sums, w, ())) k) m := by
  rw [wp_let_sha256msg2_eq]; exact h _ rfl

/-! ## Scalar floating-point operation specs -/

theorem wp_fadd (f : Fmt) (a b : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f (Float.Model.UnpackedFloat.add f.format (unpackFloat f a.val) (unpackFloat f b.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fadd (.float f)) (a, b, ())) k) m := by
  rw [wp_let_mk2]; simpa [OpCode.wp_fadd, liftFloatRel2] using h

theorem wp_fsub (f : Fmt) (a b : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f (Float.Model.UnpackedFloat.sub f.format (unpackFloat f a.val) (unpackFloat f b.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fsub (.float f)) (a, b, ())) k) m := by
  rw [wp_let_mk2]; simpa [OpCode.wp_fsub, liftFloatRel2] using h

theorem wp_fmul (f : Fmt) (a b : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f (Float.Model.UnpackedFloat.mul f.format (unpackFloat f a.val) (unpackFloat f b.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fmul (.float f)) (a, b, ())) k) m := by
  rw [wp_let_mk2]; simpa [OpCode.wp_fmul, liftFloatRel2] using h

theorem wp_fdiv (f : Fmt) (a b : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f (Float.Model.UnpackedFloat.div f.format (unpackFloat f a.val) (unpackFloat f b.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fdiv (.float f)) (a, b, ())) k) m := by
  rw [wp_let_mk2]; simpa [OpCode.wp_fdiv, liftFloatRel2] using h

theorem wp_ffma (f : Fmt) (a b c : Arg Val (.float f))
    (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f
      (Float.Model.UnpackedFloat.fma f.format (unpackFloat f a.val) (unpackFloat f b.val) (unpackFloat f c.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ffma (.float f)) (a, b, c, ())) k) m := by
  rw [wp_let_mk3]; simpa [OpCode.wp_ffma, liftFloatRel3] using h

theorem wp_fsqrt (f : Fmt) (a : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : floatResultWp f (Float.Model.UnpackedFloat.sqrt f.format (unpackFloat f a.val))
      fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fsqrt (.float f)) (a, ())) k) m := by
  rw [wp_let_mk1]; simpa [OpCode.wp_fsqrt, liftFloatRel1] using h

theorem wp_fneg (f : Fmt) (a : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : ∀ r : BitVec f.width, r = a.val ^^^ (1#f.width <<< (f.width - 1)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fneg (.float f)) (a, ())) k) m := by
  rw [wp_let_mk1]
  simp only [OpCode.wp_fneg, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lift1]
  exact h _ rfl

theorem wp_fabs (f : Fmt) (a : Arg Val (.float f)) (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : ∀ r : BitVec f.width, r = a.val &&& ~~~(1#f.width <<< (f.width - 1)) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fabs (.float f)) (a, ())) k) m := by
  rw [wp_let_mk1]
  simp only [OpCode.wp_fabs, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lift1]
  exact h _ rfl

theorem wp_fcmp (o : FCmpOp) (f : Fmt)
    (a b : Arg Val (.float f)) (k : Tup Val [.bool] → Expr Val Cont rs)
    (h : ∀ c : Bool, c = fcmpLeaf o f a.val b.val → wp Γ Q X (k (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fcmp o (.float f) .bool rfl) (a, b, ())) k) m := by
  rw [wp_let_fcmp_eq]
  simpa [liftFCmp] using h _ rfl

theorem wp_fptoui (f : Fmt) (n : Nat) (a : Arg Val (.float f))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    {z : Int} (hz : truncToInt (unpackFloat f a.val) = some z)
    (h0 : 0 ≤ z) (hlt : z < 2 ^ n)
    (h : ∀ r : BitVec n, r = BitVec.ofInt n z → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fptoui f n) (a, ())) k) m := by
  rw [wp_let_fptoui_eq]; simp only [hz]; exact ⟨h0, hlt, h _ rfl⟩

theorem wp_fptoui_ex (f : Fmt) (n : Nat) (a : Arg Val (.float f))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : ∃ z : Int, truncToInt (unpackFloat f a.val) = some z ∧ 0 ≤ z ∧ z < 2 ^ n ∧
      wp Γ Q X (k (BitVec.ofInt n z, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fptoui f n) (a, ())) k) m := by
  rcases h with ⟨z, hz, h0, hlt, hk⟩
  exact wp_fptoui f n a k hz h0 hlt fun r hr => hr ▸ hk

theorem wp_fptosi (f : Fmt) (n : Nat) (a : Arg Val (.float f))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hn : n ≠ 0) {z : Int} (hz : truncToInt (unpackFloat f a.val) = some z)
    (hlo : -(2 ^ (n - 1) : Int) ≤ z) (hhi : z < (2 ^ (n - 1) : Int))
    (h : ∀ r : BitVec n, r = BitVec.ofInt n z → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fptosi f n) (a, ())) k) m := by
  rw [wp_let_fptosi_eq]; simp only [hz]; exact ⟨hn, hlo, hhi, h _ rfl⟩

theorem wp_fptosi_ex (f : Fmt) (n : Nat) (a : Arg Val (.float f))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hn : n ≠ 0)
    (h : ∃ z : Int, truncToInt (unpackFloat f a.val) = some z ∧
      -(2 ^ (n - 1) : Int) ≤ z ∧ z < (2 ^ (n - 1) : Int) ∧
      wp Γ Q X (k (BitVec.ofInt n z, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fptosi f n) (a, ())) k) m := by
  rcases h with ⟨z, hz, hlo, hhi, hk⟩
  exact wp_fptosi f n a k hn hz hlo hhi fun r hr => hr ▸ hk

theorem wp_uitofp (n : Nat) (f : Fmt) (a : Arg Val (.bits n))
    (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : ∀ r : BitVec f.width,
      r = packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.val.toNat) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.uitofp n f) (a, ())) k) m := by
  rw [wp_let_mk1]; simpa [OpCode.wp_uitofp] using h _ rfl

theorem wp_sitofp (n : Nat) (f : Fmt) (a : Arg Val (.bits n))
    (k : Tup Val [.float f] → Expr Val Cont rs)
    (h : ∀ r : BitVec f.width,
      r = packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.val.toInt) →
      wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sitofp n f) (a, ())) k) m := by
  rw [wp_let_mk1]; simpa [OpCode.wp_sitofp] using h _ rfl

theorem wp_fcvt (f g : Fmt) (a : Arg Val (.float f)) (k : Tup Val [.float g] → Expr Val Cont rs)
    (h : convertFloat f g a.val fun r => wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.fcvt f g) (a, ())) k) m := by
  rw [wp_let_mk1]; simpa [OpCode.wp_fcvt] using h

end

end LeanQbe.T
