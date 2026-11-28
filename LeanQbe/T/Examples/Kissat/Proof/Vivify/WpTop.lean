module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify

import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem wp_udiv_c {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} (a : Arg Val (Ty.bits n)) {b : BitVec n} (hb : b ≠ 0 := by decide)
    (k : Tup Val [Ty.bits n] → Expr Val Cont rs)
    (hk : ∀ r : BitVec n, r = a.val / b → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (Expr.let_ (op2 (OpCode.udiv n) a (Arg.imm b)) k) m :=
  wp_udiv a (Arg.imm b) k hb hk

private theorem wp_zext_c {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {mW nW : Nat} (h : mW ≤ nW := by decide) (a : Arg Val (Ty.bits mW))
    (k : Tup Val [Ty.bits nW] → Expr Val Cont rs)
    (hk : ∀ r : BitVec nW, r = BitVec.setWidth nW a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (Expr.let_ (op1 (OpCode.zext mW nW) a) k) m :=
  wp_zext h a k hk

private theorem wp_sext_c {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {mW nW : Nat} (h : mW ≤ nW := by decide) (a : Arg Val (Ty.bits mW))
    (k : Tup Val [Ty.bits nW] → Expr Val Cont rs)
    (hk : ∀ r : BitVec nW, r = BitVec.signExtend nW a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (Expr.let_ (op1 (OpCode.sext mW nW) a) k) m :=
  wp_sext h a k hk

private theorem wp_trunc_c {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {mW nW : Nat} (h : nW ≤ mW := by decide) (a : Arg Val (Ty.bits mW))
    (k : Tup Val [Ty.bits nW] → Expr Val Cont rs)
    (hk : ∀ r : BitVec nW, r = BitVec.setWidth nW a.val → wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (Expr.let_ (op1 (OpCode.trunc mW nW) a) k) m :=
  wp_trunc h a k hk

local syntax "step_let1" : tactic
local macro_rules
  | `(tactic| step_let1) => `(tactic|
    first
    | (apply wp_copy; rintro _ h_; subst h_)
    | (apply wp_not; rintro _ h_; subst h_)
    | (apply wp_add; rintro _ h_; subst h_)
    | (apply wp_sub; rintro _ h_; subst h_)
    | (apply wp_mul; rintro _ h_; subst h_)
    | (apply wp_udiv_c; decide; rintro _ h_; subst h_)
    | (apply wp_shl; rintro _ h_; subst h_)
    | (apply wp_and; rintro _ h_; subst h_)
    | (apply wp_or; rintro _ h_; subst h_)
    | (apply wp_cmp; rintro _ h_; subst h_)
    | (apply wp_zext_c; decide; rintro _ h_; subst h_)
    | (apply wp_sext_c; decide; rintro _ h_; subst h_)
    | (apply wp_trunc_c; decide; rintro _ h_; subst h_))

local syntax "step_lets" : tactic
local macro_rules
  | `(tactic| step_lets) => `(tactic|
    ((repeat step_let1); try dsimp only))

local syntax "step_jnz" : tactic
local macro_rules
  | `(tactic| step_jnz) => `(tactic|
    (step_lets
     rw [wp_jnz]
     try dsimp only [Arg.val, CmpOp.evalBits]
     refine ⟨fun _ => ?_, fun _ => ?_⟩))

local syntax "step_jump" : tactic
local macro_rules
  | `(tactic| step_jump) => `(tactic|
    (step_lets; rw [wp_jump]; try dsimp only [vals, Arg.val]))

local syntax "step_ret" : tactic
local macro_rules
  | `(tactic| step_ret) => `(tactic|
    (step_lets; rw [wp_ret]; try dsimp only [vals, Arg.val]))

private theorem wp_store_of {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {t : Ty} {v : Arg Val t} {a : Arg Val i64}
    {k : Expr Val Cont rs} {P : Prop} (h : storeOk m t a.val ∧ P)
    (hk : P → wp Γ Q X k (storeMem m t a.val v.val)) :
    wp Γ Q X (Expr.store v a k) m := by
  rw [wp_store]
  exact ⟨h.1, hk h.2⟩

private abbrev withTr (s : FullState) (tr : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with tarjan_reach := tr } }

private abbrev withTier1 (s : FullState) (t1 : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with tier1 := t1 } }

private abbrev withTier2 (s : FullState) (t2 : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with tier2 := t2 } }

private abbrev withResSz (s : FullState) (rsz : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with res_sz := rsz } }

private abbrev withProbing (s : FullState) (pr : BitVec 64) : FullState :=
  { s with core := { s.core with probing := pr } }

private abbrev VivHdrInv (c : FullCfg) (F0 : Std.Sat.CNF Nat)
    (ext : List (BitVec 64)) (s0 : FullState)
    (ext' : List (BitVec 64)) (s' : FullState) : Prop :=
  M6HdrExtOk ext' ∧
    (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
    FullSparseInv c F0 s' ∧
    s'.core.cur_level = 0 ∧
    s'.core.probing = s0.core.probing ∧
    s'.core.fuel.toNat ≤ s0.core.fuel.toNat

private abbrev VivTierLoopInv (c : FullCfg) (F0 : Std.Sat.CNF Nat)
    (ext : List (BitVec 64)) (s5 : FullState) (fuel0 : Nat)
    (ext' : List (BitVec 64)) (s' : FullState) : Prop :=
  M6HdrExtOk ext' ∧
    (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
    FullSparseInv c F0 s' ∧
    s'.core.fuel.toNat ≤ fuel0 ∧
    s'.core.arena_len = s5.core.arena_len ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s5 ∧
    s'.scratch.red_refs = s5.scratch.red_refs

private theorem full_cur_level_lt64 {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) : s.core.cur_level < 2 ^ 64 := by
  rcases hsp.1.witness with ⟨_, hw⟩
  have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le
  have := hsp.1.lengths.core_ok.cur_vars_le; have := c.hmaxv
  have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl; omega

private theorem bv64_eq_zero_of_ne_false {n : Nat} (hn : n < 2 ^ 64)
    (h : decide (BitVec.ofNat 64 n ≠ 0#64) = false) : n = 0 := by
  have h1 := congrArg BitVec.toNat (Classical.byContradiction (fun hne => of_decide_eq_false h hne))
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt hn] at h1; exact h1

private theorem bv64_eq_zero_of_eq_true {n : Nat} (hn : n < 2 ^ 64)
    (h : decide (BitVec.ofNat 64 n = 0#64) = true) : n = 0 := by
  have h1 := congrArg BitVec.toNat (of_decide_eq_true h)
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt hn] at h1; exact h1

private abbrev bt0GuardExpr {rs : List Ty} (hdr : Val i64) (J : Cont []) :
    Expr Val Cont rs :=
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 160#64)) fun p =>
  Expr.load i64 (Arg.var p.1) fun ld =>
  Expr.let_ (op2 (OpCode.cmp CmpOp.ne i64 Ty.bool) (Arg.var ld) (Arg.imm 0#64)) fun cnd =>
  Expr.jnz (Arg.var cnd.1)
    (@Expr.call Val Cont rs "full_backtrack" [i64, i64] []
      (Arg.var hdr, Arg.imm 0#64, ()) fun _ => Expr.jump J ())
    (Expr.jump J ())

private abbrev zeroTrExpr {rs : List Ty} (pTr lim : Val i64) (exitE : Expr Val Cont rs) :
    Expr Val Cont rs :=
  Expr.group (sig := [[i64]])
    (fun J =>
      Blocks.cons
        (fun i =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var i.1) (Arg.var lim))
            fun cnd =>
          Expr.jnz (Arg.var cnd.1)
            (Expr.let_ (op2 (OpCode.mul i64) (Arg.var i.1) (Arg.imm 4#64)) fun o =>
             Expr.let_ (op2 (OpCode.add i64) (Arg.var pTr) (Arg.var o.1)) fun p =>
             @Expr.store Val Cont rs i32 (Arg.imm 0#32) (Arg.var p.1)
               (Expr.let_ (op2 (OpCode.add i64) (Arg.var i.1) (Arg.imm 1#64)) fun ni =>
                Expr.jump J.1 (Arg.var ni.1, ())))
            exitE)
        Blocks.nil)
    (fun J => Expr.jump J.1 (Arg.imm 0#64, ()))

private abbrev scanClauseBodyExpr {rs : List Ty} (pAr pTr : Val i64) (cr lim : Val i64)
    (Ju : Cont [i32]) (u : Val i32) : Expr Val Cont rs :=
  Expr.let_ (op2 (OpCode.add i64) (Arg.var cr) (Arg.imm 3#64)) fun a1 =>
  Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var u)) fun u64 =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var a1.1) (Arg.var u64.1)) fun idx =>
  Expr.let_ (op2 (OpCode.mul i64) (Arg.var idx.1) (Arg.imm 4#64)) fun off =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var pAr) (Arg.var off.1)) fun ptr =>
  Expr.load i32 (Arg.var ptr.1) fun lit =>
  Expr.group (sig := [[]])
    (fun Jn0 =>
      Blocks.cons
        (fun _ =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var u) (Arg.imm 1#32)) fun nu =>
          Expr.jump Ju (Arg.var nu.1, ()))
        Blocks.nil)
    (fun Jn0 =>
      Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var lit)) fun l64 =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var l64.1) (Arg.var lim))
        fun clt =>
      Expr.jnz (Arg.var clt.1)
        (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var lit)) fun l64b =>
         Expr.let_ (op2 (OpCode.mul i64) (Arg.var l64b.1) (Arg.imm 4#64)) fun o1 =>
         Expr.let_ (op2 (OpCode.add i64) (Arg.var pTr) (Arg.var o1.1)) fun p1 =>
         Expr.load i32 (Arg.var p1.1) fun cnt =>
         Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool) (Arg.var cnt) (Arg.imm 4294967295#32))
           fun cmax =>
         Expr.jnz (Arg.var cmax.1)
           (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var lit)) fun l64c =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var l64c.1) (Arg.imm 4#64)) fun o2 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var pTr) (Arg.var o2.1)) fun p2 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var lit)) fun l64d =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var l64d.1) (Arg.imm 4#64)) fun o3 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var pTr) (Arg.var o3.1)) fun p3 =>
            Expr.load i32 (Arg.var p3.1) fun cur =>
            Expr.let_ (op2 (OpCode.add i32) (Arg.var cur) (Arg.imm 1#32)) fun nxt =>
            Expr.store (Arg.var nxt.1) (Arg.var p2.1) (Expr.jump Jn0.1 ()))
           (Expr.jump Jn0.1 ()))
        (Expr.jump Jn0.1 ()))

private abbrev scanClauseExpr {rs : List Ty} (pAr pTr : Val i64) (cr lim : Val i64)
    (sz : Val i32) (Jret : Cont []) : Expr Val Cont rs :=
  Expr.group (sig := [[i32]])
    (fun Ju =>
      Blocks.cons
        (fun u =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool) (Arg.var u.1) (Arg.var sz))
            fun cnd =>
          Expr.jnz (Arg.var cnd.1)
            (scanClauseBodyExpr pAr pTr cr lim Ju.1 u.1)
            (Expr.jump Jret ()))
        Blocks.nil)
    (fun Ju => Expr.jump Ju.1 (Arg.imm 0#32, ()))

private abbrev scanArenaStepExpr {rs : List Ty} (hdr pAr pTr lim cr : Val i64)
    (J2 : Cont [i64]) : Expr Val Cont rs :=
  Expr.let_ (op2 (OpCode.mul i64) (Arg.var cr) (Arg.imm 4#64)) fun o1 =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var pAr) (Arg.var o1.1)) fun pa1 =>
  Expr.load i32 (Arg.var pa1.1) fun chdr =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var cr) (Arg.imm 2#64)) fun cr2 =>
  Expr.let_ (op2 (OpCode.mul i64) (Arg.var cr2.1) (Arg.imm 4#64)) fun o2 =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var pAr) (Arg.var o2.1)) fun pa2 =>
  Expr.load i32 (Arg.var pa2.1) fun sz =>
  Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var cr)) fun cr32 =>
  @Expr.call Val Cont rs "full_arena_next" [i64, i32] [i32]
    (Arg.var hdr, Arg.var cr32.1, ()) fun nxt32 =>
  Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var nxt32.1)) fun nxt =>
  Expr.group (sig := [[]])
    (fun J3 => Blocks.cons (fun _ => Expr.jump J2 (Arg.var nxt.1, ())) Blocks.nil)
    (fun J3 =>
      Expr.let_ (op2 (OpCode.and i32) (Arg.var chdr) (Arg.imm 524288#32)) fun g =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.eq i32 Ty.bool) (Arg.var g.1) (Arg.imm 0#32)) fun cg =>
      Expr.jnz (Arg.var cg.1)
        (Expr.let_ (op2 (OpCode.cmp CmpOp.uge i32 Ty.bool) (Arg.var sz) (Arg.imm 3#32))
           fun csz =>
         Expr.jnz (Arg.var csz.1) (scanClauseExpr pAr pTr cr lim sz J3.1) (Expr.jump J3.1 ()))
        (Expr.jump J3.1 ()))

private abbrev scanArenaExpr {rs : List Ty} (hdr pAr pTr lim : Val i64)
    (after : Expr Val Cont rs) : Expr Val Cont rs :=
  Expr.group (sig := [[i64]])
    (fun J2 =>
      Blocks.cons
        (fun cr =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 48#64)) fun p =>
          Expr.load i64 (Arg.var p.1) fun alen =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var cr.1) (Arg.var alen))
            fun clt =>
          Expr.jnz (Arg.var clt.1) (scanArenaStepExpr hdr pAr pTr lim cr.1 J2.1) after)
        Blocks.nil)
    (fun J2 => Expr.jump J2.1 (Arg.imm 0#64, ()))

private abbrev clauseStepExpr {rs : List Ty} (hdr pRR bn tick_lim : Val i64)
    (J5 : Cont [i64, i64, i64]) (J6 : Cont [i64, i64]) (rem j_idx : Val i64) :
    Expr Val Cont rs :=
  Expr.call (as := [i64, i64]) (bs := [i64]) "m6_hdr_get_watermark"
    (Arg.var hdr, Arg.imm 5#64, ()) fun wm =>
  Expr.let_ (op2 (OpCode.cmp CmpOp.ule i64 Ty.bool) (Arg.var wm.1) (Arg.var tick_lim))
    fun c5 =>
  Expr.jnz (Arg.var c5.1)
    (Expr.let_ (op2 (OpCode.sub i64) (Arg.var bn) (Arg.imm 1#64)) fun b1 =>
     Expr.let_ (op2 (OpCode.sub i64) (Arg.var b1.1) (Arg.var j_idx)) fun idx =>
     Expr.let_ (op2 (OpCode.mul i64) (Arg.var idx.1) (Arg.imm 4#64)) fun off =>
     Expr.let_ (op2 (OpCode.add i64) (Arg.var pRR) (Arg.var off.1)) fun ptr =>
     Expr.load i32 (Arg.var ptr.1) fun cref =>
     Expr.let_ (op2 (OpCode.sub i64) (Arg.var rem) (Arg.imm 1#64)) fun rem1 =>
     Expr.call (as := [i64, i32]) (bs := [i64]) "full_viv_clause_m6"
       (Arg.var hdr, Arg.var cref, ()) fun rc =>
     Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var rc.1) (Arg.imm 20#64))
       fun cr20 =>
     Expr.jnz (Arg.var cr20.1)
       (Expr.jump J5 (Arg.var rem1.1, Arg.imm 20#64, Arg.var j_idx, ()))
       (Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var rc.1) (Arg.imm 2#64))
          fun cr2 =>
        Expr.jnz (Arg.var cr2.1)
          (Expr.jump J5 (Arg.var rem1.1, Arg.imm 1#64, Arg.var j_idx, ()))
          (Expr.group (sig := [[]])
             (fun J7 =>
               Blocks.cons
                 (fun _ =>
                   Expr.let_ (op2 (OpCode.add i64) (Arg.var j_idx) (Arg.imm 1#64)) fun nj =>
                   Expr.jump J6 (Arg.var rem1.1, Arg.var nj.1, ()))
                 Blocks.nil)
             (fun J7 =>
               Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 160#64)) fun pcl =>
               Expr.load i64 (Arg.var pcl.1) fun cl =>
               Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var cl) (Arg.imm 0#64))
                 fun ccl =>
               Expr.jnz (Arg.var ccl.1)
                 (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                    (Arg.var hdr, ()) fun pr =>
                  Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var pr.1) (Arg.imm 1#64))
                    fun cpr =>
                  Expr.jnz (Arg.var cpr.1)
                    (Expr.jump J5 (Arg.var rem1.1, Arg.imm 20#64, Arg.var j_idx, ()))
                    (Expr.jump J7.1 ()))
                 (Expr.jump J7.1 ())))))
    (Expr.jump J5 (Arg.var rem, Arg.imm 1#64, Arg.var j_idx, ()))

private abbrev clauseLoopExpr {rs : List Ty} (hdr pRR bn budget tick_lim : Val i64)
    (J5 : Cont [i64, i64, i64]) : Expr Val Cont rs :=
  Expr.group (sig := [[i64, i64]])
    (fun J6 =>
      Blocks.cons
        (fun p =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var p.2.1) (Arg.var bn))
            fun c1 =>
          Expr.jnz (Arg.var c1.1)
            (Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p.1) (Arg.imm 0#64))
               fun c2 =>
             Expr.jnz (Arg.var c2.1)
               (Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 760#64)) fun poom =>
                Expr.load i64 (Arg.var poom.1) fun oom =>
                Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var oom) (Arg.imm 0#64))
                  fun c3 =>
                Expr.jnz (Arg.var c3.1)
                  (Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 168#64)) fun pf =>
                   Expr.load i64 (Arg.var pf.1) fun fuel =>
                   Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var fuel) (Arg.imm 0#64))
                     fun c4 =>
                   Expr.jnz (Arg.var c4.1)
                     (clauseStepExpr hdr pRR bn tick_lim J5 J6.1 p.1 p.2.1)
                     (Expr.jump J5 (Arg.var p.1, Arg.imm 1#64, Arg.var p.2.1, ())))
                  (Expr.jump J5 (Arg.var p.1, Arg.imm 1#64, Arg.var p.2.1, ())))
               (Expr.jump J5 (Arg.var p.1, Arg.imm 1#64, Arg.var p.2.1, ())))
            (Expr.jump J5 (Arg.var p.1, Arg.imm 1#64, Arg.var p.2.1, ())))
        Blocks.nil)
    (fun J6 => Expr.jump J6.1 (Arg.var budget, Arg.imm 0#64, ()))

private abbrev tierFinishExpr (hdr mode bn old_p rc _rem rc_out j_idx : Val i64) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[]])
    (fun J6 =>
      Blocks.cons
        (fun _ =>
          Expr.group (sig := [[]])
            (fun J7 =>
              Blocks.cons
                (fun _ =>
                  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 1144#64)) fun p1 =>
                  Expr.store (Arg.var j_idx) (Arg.var p1.1)
                    (Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 520#64)) fun p2 =>
                     Expr.store (Arg.var old_p) (Arg.var p2.1) (Expr.ret (Arg.var rc_out, ()))))
                Blocks.nil)
            (fun J7 =>
              Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var rc_out) (Arg.imm 1#64))
                fun c1 =>
              Expr.jnz (Arg.var c1.1)
                (Expr.let_ (op2 (OpCode.cmp CmpOp.uge i64 Ty.bool) (Arg.var j_idx) (Arg.var bn))
                   fun c2 =>
                 Expr.jnz (Arg.var c2.1)
                   (Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var bn) (Arg.var rc))
                      fun c3 =>
                    Expr.jnz (Arg.var c3.1)
                      (@Expr.call Val Cont [i64] "full_viv_clear_tier_m6" [i64, i64] []
                        (Arg.var hdr, Arg.var mode, ()) fun _ => Expr.jump J7.1 ())
                      (Expr.jump J7.1 ()))
                   (Expr.jump J7.1 ()))
                (Expr.jump J7.1 ())))
        Blocks.nil)
    (fun J6 => bt0GuardExpr hdr J6.1)

private abbrev condTierExpr {rs : List Ty} (hdr : Val i64) (mode : BitVec 64)
    (rc_prev wm_prev lim_arg tot_slice tot : Val i64) (Jnext : Cont [i64, i64]) :
    Expr Val Cont rs :=
  Expr.let_ (op2 (OpCode.cmp CmpOp.ne i64 Ty.bool) (Arg.var rc_prev) (Arg.imm 20#64)) fun cr =>
  Expr.jnz (Arg.var cr.1)
    (Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var lim_arg) (Arg.imm 0#64))
       fun cb =>
     Expr.jnz (Arg.var cb.1)
       (Expr.let_ (op2 (OpCode.mul i64) (Arg.var tot_slice) (Arg.var lim_arg)) fun m1 =>
        Expr.let_ (op2 (OpCode.udiv 64) (Arg.var m1.1) (Arg.var tot)) fun q1 =>
        Expr.group (sig := [[i64]])
          (fun Jt =>
            Blocks.cons
              (fun lim =>
                Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "full_vivify_tier_m6_hdr"
                  (Arg.var hdr, Arg.imm mode, Arg.imm 4294967295#64, Arg.var lim.1, ())
                  fun r => Expr.jump Jnext (Arg.var r.1, Arg.var lim.1, ()))
              Blocks.nil)
          (fun Jt =>
            Expr.let_ (op1 (OpCode.not i64) (Arg.imm 0#64)) fun z0 =>
            Expr.let_ (op2 (OpCode.sub i64) (Arg.var z0.1) (Arg.var q1.1)) fun nq =>
            Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var wm_prev) (Arg.var nq.1))
              fun cov =>
            Expr.jnz (Arg.var cov.1)
              (Expr.let_ (op1 (OpCode.not i64) (Arg.imm 0#64)) fun z1 =>
               Expr.jump Jt.1 (Arg.var z1.1, ()))
              (Expr.let_ (op2 (OpCode.add i64) (Arg.var wm_prev) (Arg.var q1.1)) fun s1 =>
               Expr.jump Jt.1 (Arg.var s1.1, ()))))
       (Expr.jump Jnext (Arg.var rc_prev, Arg.var wm_prev, ())))
    (Expr.jump Jnext (Arg.var rc_prev, Arg.var wm_prev, ()))

private abbrev delayAdjustExpr {rs : List Ty} (hdr r4 lim4 ld_vc ld_unass ld_rsz : Val i64)
    (J11 : Cont [i64, i64]) : Expr Val Cont rs :=
  Expr.group (sig := [[]])
    (fun J22 => Blocks.cons (fun _ => Expr.jump J11 (Arg.var r4, Arg.var lim4, ())) Blocks.nil)
    (fun J22 =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.ne i64 Ty.bool) (Arg.var r4) (Arg.imm 20#64)) fun c1 =>
      Expr.jnz (Arg.var c1.1)
        (Expr.group (sig := [[i64]])
           (fun J32 =>
             Blocks.cons
               (fun du =>
                 Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 1056#64)) fun pv =>
                 Expr.load i64 (Arg.var pv.1) fun vc2 =>
                 Expr.let_ (op2 (OpCode.sub i64) (Arg.var vc2) (Arg.var ld_vc)) fun dv =>
                 Expr.let_ (op2 (OpCode.add i64) (Arg.var dv.1) (Arg.var du.1)) fun w =>
                 Expr.group (sig := [[]])
                   (fun J33 => Blocks.cons (fun _ => Expr.jump J22.1 ()) Blocks.nil)
                   (fun J33 =>
                     Expr.group (sig := [[]])
                       (fun J43 =>
                         Blocks.cons
                           (fun _ =>
                             @Expr.call Val Cont rs "m6_hdr_bump_delay" [i64, i64] []
                               (Arg.var hdr, Arg.imm 3#64, ()) fun _ => Expr.jump J33.1 ())
                           Blocks.nil)
                       (fun J43 =>
                         Expr.let_ (op2 (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var ld_rsz)
                             (Arg.imm 0#64)) fun cz =>
                         Expr.jnz (Arg.var cz.1) (Expr.jump J43.1 ())
                           (Expr.let_ (op2 (OpCode.mul i64) (Arg.var w.1) (Arg.imm 100#64))
                              fun w100 =>
                            Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var w100.1)
                                (Arg.var ld_rsz)) fun cw =>
                            Expr.jnz (Arg.var cw.1) (Expr.jump J43.1 ())
                              (@Expr.call Val Cont rs "m6_hdr_reduce_delay" [i64, i64] []
                                (Arg.var hdr, Arg.imm 3#64, ()) fun _ => Expr.jump J33.1 ())))))
               Blocks.nil)
           (fun J32 =>
             Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 792#64)) fun pu1 =>
             Expr.load i64 (Arg.var pu1.1) fun u1 =>
             Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var ld_unass) (Arg.var u1))
               fun cu =>
             Expr.jnz (Arg.var cu.1)
               (Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 792#64)) fun pu2 =>
                Expr.load i64 (Arg.var pu2.1) fun u2 =>
                Expr.let_ (op2 (OpCode.sub i64) (Arg.var ld_unass) (Arg.var u2)) fun diff =>
                Expr.jump J32.1 (Arg.var diff.1, ()))
               (Expr.jump J32.1 (Arg.imm 0#64, ()))))
        (Expr.jump J22.1 ()))

private theorem viv_backtrack0_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    {k : Tup Val [] → Expr Val Cont rs}
    (hk : ∀ s' m', FullSparseInv c F0 s' →
      s'.core.cur_level = 0 → s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.cur_vars = s.core.cur_vars → s'.scratch.red_refs = s.scratch.red_refs →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (@Expr.call Val Cont rs "full_backtrack" [i64, i64] []
      (Arg.var c.hdr, Arg.imm 0#64, ()) k) m := by
  apply wp_call_of_spec
  refine hBt _ _ _ _ ?_
  have hmF := fullM6HdrMem_focus_full hm
  rcases hsp.1.witness with ⟨_, hw⟩
  have hcl_lt := full_cur_level_lt64 hsp
  have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp.1.lengths, hcl_lt,
    fun _ => by
      have := hsp.1.lengths.core_ok.cur_vars_ge
      have := hsp.1.lengths.core_ok.cur_vars_le
      have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le; omega,
    hw.trail_lits_lt, hmF, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s'
    hlen' _ _ hcl_eq hps hsc_eq _ _ hfb _ hmF'
  have hm' := fullM6HdrMem_unfocus_full hmF'
  have hsp' := viv_sparse_of_backtrack hsp (target_lvl := 0) (Nat.zero_le _) hlen' hps
    (fun F1 h1 _ => hfb F0 F1 h1 (Nat.zero_le _))
  have hcl0 : cl' = 0 := by rw [hcl_eq]; exact Nat.min_zero _
  rcases hsc_eq with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  exact hk _ m' hsp' hcl0 rfl rfl rfl rfl rfl rfl hm'

private theorem viv_backtrack0_guard_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m) {J : Cont []}
    (hJ : ∀ s' m', FullSparseInv c F0 s' →
      s'.core.cur_level = 0 → s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.cur_vars = s.core.cur_vars → s'.scratch.red_refs = s.scratch.red_refs →
      (FullM6HdrMem c ext s' ⋆ R) m' → J () m') :
    wp Γ Q X (bt0GuardExpr c.hdr J) m := by
  step_lets
  have hmF := fullM6HdrMem_focus_full hm
  apply wp_load_of (a := Arg.var _) (load_full_cur_level hmF)
  step_jnz
  · apply viv_backtrack0_step hBt hsp hm
    intro s' m' hsp' hcl' hpr' hfl' har' hal' hcv' hrr' hm'
    step_jump
    exact hJ s' m' hsp' hcl' hpr' hfl' har' hal' hcv' hrr' hm'
  · rename_i hc
    step_jump
    exact hJ s m hsp (bv64_eq_zero_of_ne_false (full_cur_level_lt64 hsp) hc)
      rfl rfl rfl rfl rfl rfl hm

private theorem viv_w2a_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fn : Sym} {ea res : List Ty} (hFn : Γ.Has fn (m6HdrW2aSpec ea res))
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hpres : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext ∧ M6ExtW2bPres ext0 ext)
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (args : Tup (Arg Val) ea) {k : Tup Val res → Expr Val Cont rs}
    (hk : ∀ r ext' s' m', M6HdrExtOk ext' →
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      FullSparseInv c F0 s' → s'.core = s.core → M6HdrScratchPres s s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (@Expr.call Val Cont rs fn (i64 :: ea) res (Arg.var c.hdr, args) k) m := by
  apply wp_call_of_spec
  refine hFn _ _ _ _ (m6HdrW2aSpec_of rfl hcfg hext hsp.1.lengths hm ?_)
  intro r ext' s' m' hcore' hlen' hsc' hext' hpres' hm'
  exact hk r ext' s' m' hext' (viv_ext_pres_trans hpres hpres')
    (viv_sparse_of_core_eq hsp hlen' hcore' hsc') hcore' hsc' hm'

private theorem viv_watermark_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hpres : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext ∧ M6ExtW2bPres ext0 ext)
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (kind : BitVec 64) {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : ∀ r ext' s' m', M6HdrExtOk ext' →
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      FullSparseInv c F0 s' → s'.core = s.core → M6HdrScratchPres s s' →
      s'.scratch.red_refs = s.scratch.red_refs → (FullM6HdrMem c ext' s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (@Expr.call Val Cont rs "m6_hdr_get_watermark" [i64, i64] [i64]
      (Arg.var c.hdr, Arg.imm kind, ()) k) m := by
  apply wp_call_of_spec
  refine hGetWm _ _ _ _ ⟨c, ext, s, R, rfl, hcfg, hext, hsp.1.lengths, hm, ?_⟩
  intro r ext' s' m' hcore' hlen' hsc' hrr' hext' hpres' hm'
  exact hk r ext' s' m' hext' (viv_ext_pres_trans hpres hpres')
    (viv_sparse_of_core_eq hsp hlen' hcore' hsc') hcore' hsc' hrr' hm'

private theorem viv_tier_zero_tr_loop_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)}
    (s : FullState) {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (lim : BitVec 64) (hlim : lim.toNat = 2 * s.core.cur_vars)
    {exitExpr : Expr Val Cont rs}
    (hexit : ∀ tr m', tr.length = 2 * c.max_vars → FullSparseInv c F0 (withTr s tr) →
      (FullM6HdrMem c ext (withTr s tr) ⋆ R) m' → wp Γ Q X exitExpr m') :
    wp Γ Q X (zeroTrExpr c.pTarjanReach lim exitExpr) m := by
  refine wp_while_state1 (t := i64)
    (fun (st : BitVec 64 × List (BitVec 32)) => st.1)
    (fun st => 2 * s.core.cur_vars - st.1.toNat)
    (fun (i, tr) m' => i.toNat ≤ 2 * s.core.cur_vars ∧ tr.length = 2 * c.max_vars ∧
      FullSparseInv c F0 (withTr s tr) ∧ (FullM6HdrMem c ext (withTr s tr) ⋆ R) m')
    ?_ ?_
  · intro J hJ; step_jump
    exact hJ (0#64, s.scratch.tarjan_reach) m
      ⟨Nat.zero_le _, hsp.1.lengths.scratch_ok.tarjan_reach_len, hsp, hm⟩
  · intro J ⟨i, tr⟩ m' ⟨hi_le, htr_len, hsp_tr, hm_tr⟩ ih
    try simp only [Blocks.get]
    step_jnz
    · rename_i hc
      rw [BitVec.ult] at hc
      have hi_lt : i.toNat < 2 * s.core.cur_vars := by rw [← hlim]; exact of_decide_eq_true hc
      have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
      have hi_tr : i.toNat < tr.length := by omega
      have hmv := c.hmaxv; have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
      step_lets
      have hmF := fullM6HdrMem_focus_full hm_tr
      apply wp_store_of (a := Arg.var _) (c0_store_full_tarjan_reach 0#32 hi_tr hmF)
      intro hmF1
      have htr1_len : (tr.set i.toNat 0#32).length = 2 * c.max_vars := by
        rw [List.length_set]; exact htr_len
      step_jump
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ih (i + 1#64, tr.set i.toNat 0#32) _ (by dsimp only; rw [hi1]; omega)
        ⟨by rw [hi1]; omega, htr1_len, viv_sparse_with_tr hsp_tr htr1_len,
         fullM6HdrMem_unfocus_full hmF1⟩
    · exact hexit tr m' htr_len hsp_tr hm_tr

private theorem viv_tier_scan_clause_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)}
    (s4 : FullState) {R : Mem 64 → Prop} {m : Mem 64}
    (cr : BitVec 64) (sz : BitVec 32) (lim : BitVec 64) (tr : List (BitVec 32))
    (htr_len : tr.length = 2 * c.max_vars) (hlim : lim.toNat = 2 * s4.core.cur_vars)
    (hsp4 : FullSparseInv c F0 (withTr s4 tr)) (hm4 : (FullM6HdrMem c ext (withTr s4 tr) ⋆ R) m)
    (hbounds : cr.toNat + 3 + sz.toNat ≤ s4.core.arena_len) {Jret : Cont []}
    (hJret : ∀ tr' m', tr'.length = 2 * c.max_vars → FullSparseInv c F0 (withTr s4 tr') →
      (FullM6HdrMem c ext (withTr s4 tr') ⋆ R) m' → Jret () m') :
    wp Γ Q X (scanClauseExpr c.pArena c.pTarjanReach cr lim sz Jret) m := by
  refine wp_while_state1 (t := i32) (fun (st : BitVec 32 × List (BitVec 32)) => st.1)
    (fun st => sz.toNat - st.1.toNat)
    (fun (u, tr') m' => u.toNat ≤ sz.toNat ∧ tr'.length = 2 * c.max_vars ∧
      FullSparseInv c F0 (withTr s4 tr') ∧ (FullM6HdrMem c ext (withTr s4 tr') ⋆ R) m')
    ?_ ?_
  · intro Ju hJu; step_jump; exact hJu (0#32, tr) m ⟨Nat.zero_le _, htr_len, hsp4, hm4⟩
  · intro Ju ⟨u, tr'⟩ m' ⟨hu_le, htr'_len, hsp_tr', hm_tr'⟩ ih
    try simp only [Blocks.get]
    step_jnz
    · rename_i hc
      rw [BitVec.ult] at hc
      have hu_lt : u.toNat < sz.toNat := of_decide_eq_true hc
      have hal_le : s4.core.arena_len ≤ c.arena_cap := hsp4.1.lengths.core_ok.arena_len_le
      have har_len : s4.core.arena.length = c.arena_cap := hsp4.1.lengths.core_ok.arena_len_arr
      have hha := c.harena; have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
      have har_lt : ((cr + 3#64) + BitVec.setWidth 64 u).toNat <
          (withTr s4 tr').core.arena.length := by
        have h1 : (BitVec.setWidth 64 u).toNat = u.toNat := by
          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
        have h2 : (cr + 3#64).toNat = cr.toNat + 3 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [BitVec.toNat_add, h1, h2]; change _ < s4.core.arena.length; omega
      step_lets
      have hmF := fullM6HdrMem_focus_full hm_tr'
      apply wp_load_of (a := Arg.var _) (c0_load_full_arena har_lt hmF)
      refine wp_join_state0 (α := List (BitVec 32))
        (fun tr'' m'' => tr''.length = 2 * c.max_vars ∧ FullSparseInv c F0 (withTr s4 tr'') ∧
          (FullM6HdrMem c ext (withTr s4 tr'') ⋆ R) m'')
        ?_ ?_
      · intro Jn tr'' m'' ⟨htr''_len, hsp_tr'', hm_tr''⟩
        try simp only [Blocks.get]
        step_jump
        have hu1 : (u + 1#32).toNat = u.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        exact ih (u + 1#32, tr'') m'' (by dsimp only; rw [hu1]; omega)
          ⟨by rw [hu1]; omega, htr''_len, hsp_tr'', hm_tr''⟩
      · intro Jn hJn
        step_jnz
        · rename_i hc
          rw [BitVec.ult] at hc
          have hl64 : (BitVec.setWidth 64
              ((withTr s4 tr').core.arena[((cr + 3#64) + BitVec.setWidth 64 u).toNat])).toNat <
              lim.toNat := of_decide_eq_true hc
          have hcv_le : s4.core.cur_vars ≤ c.max_vars := hsp4.1.lengths.core_ok.cur_vars_le
          have hl_tr : (BitVec.setWidth 64
              ((withTr s4 tr').core.arena[((cr + 3#64) + BitVec.setWidth 64 u).toNat])).toNat <
              (withTr s4 tr').scratch.tarjan_reach.length := by
            change _ < tr'.length; omega
          step_lets
          apply wp_load_of (a := Arg.var _) (c0_load_full_tarjan_reach hl_tr hmF)
          step_jnz
          · step_lets
            apply wp_load_of (a := Arg.var _) (c0_load_full_tarjan_reach hl_tr hmF)
            step_lets
            apply wp_store_of (a := Arg.var _) (c0_store_full_tarjan_reach _ hl_tr hmF)
            intro hmF1
            step_jump
            exact hJn _ _ ⟨by rw [List.length_set]; exact htr'_len,
              viv_sparse_with_tr hsp_tr' (by rw [List.length_set]; exact htr'_len),
              fullM6HdrMem_unfocus_full hmF1⟩
          · step_jump; exact hJn tr' m' ⟨htr'_len, hsp_tr', hm_tr'⟩
        · step_jump; exact hJn tr' m' ⟨htr'_len, hsp_tr', hm_tr'⟩
    · step_jump; exact hJret tr' m' htr'_len hsp_tr' hm_tr'

private theorem viv_tier_scan_arena_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)}
    (s4 : FullState) {R : Mem 64 → Prop} {m : Mem 64}
    (lim : BitVec 64) (tr0 : List (BitVec 32)) (htr0 : tr0.length = 2 * c.max_vars)
    (hlim : lim.toNat = 2 * s4.core.cur_vars) (hsp4 : FullSparseInv c F0 (withTr s4 tr0))
    (hm4 : (FullM6HdrMem c ext (withTr s4 tr0) ⋆ R) m) {after : Expr Val Cont rs}
    (hafter : ∀ tr' m', tr'.length = 2 * c.max_vars → FullSparseInv c F0 (withTr s4 tr') →
      (FullM6HdrMem c ext (withTr s4 tr') ⋆ R) m' → wp Γ Q X after m') :
    wp Γ Q X (scanArenaExpr c.hdr c.pArena c.pTarjanReach lim after) m := by
  refine wp_while_state1 (t := i64) (fun (st : BitVec 64 × List (BitVec 32)) => st.1)
    (fun st => s4.core.arena_len - st.1.toNat)
    (fun (cr, tr') m' =>
      (cr.toNat = s4.core.arena_len ∨ cr.toNat ∈ fullArenaClauseRefs s4) ∧
      cr.toNat ≤ s4.core.arena_len ∧ tr'.length = 2 * c.max_vars ∧
      FullSparseInv c F0 (withTr s4 tr') ∧ (FullM6HdrMem c ext (withTr s4 tr') ⋆ R) m')
    ?_ ?_
  · intro J2 hJ2; step_jump
    have h0 : (0#64).toNat = s4.core.arena_len ∨ (0#64).toNat ∈ fullArenaClauseRefs s4 := by
      rcases Nat.eq_zero_or_pos s4.core.arena_len with hal0 | hal_pos
      · exact Or.inl (by simp [hal0])
      · rcases hsp4.1.witness with ⟨_, hw4⟩
        exact Or.inr (fullArenaClauseRefs_zero_mem hw4.arena hal_pos)
    exact hJ2 (0#64, tr0) m ⟨h0, Nat.zero_le _, htr0, hsp4, hm4⟩
  · intro J2 ⟨cr, tr'⟩ m' ⟨hcr_mem_or, hcr_le, htr'_len, hsp_tr', hm_tr'⟩ ih
    try simp only [Blocks.get]
    step_lets
    have hmF := fullM6HdrMem_focus_full hm_tr'
    apply wp_load_of (a := Arg.var _) (load_full_arena_len hmF)
    step_jnz
    · rename_i hc
      rw [BitVec.ult] at hc
      have hal_le : s4.core.arena_len ≤ c.arena_cap := hsp4.1.lengths.core_ok.arena_len_le
      have har_len : s4.core.arena.length = c.arena_cap := hsp4.1.lengths.core_ok.arena_len_arr
      have hha := c.harena; have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
      have hcr_lt : cr.toNat < s4.core.arena_len := by
        have := of_decide_eq_true hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
      have hcr_mem : cr.toNat ∈ fullArenaClauseRefs s4 :=
        hcr_mem_or.elim (fun h => absurd h (Nat.ne_of_lt hcr_lt)) id
      rcases hsp4.1.witness with ⟨_, hw4⟩
      have hwf := hw4.arena.refs_wf cr.toNat hcr_mem
      have hcr3 : cr.toNat + 3 ≤ s4.core.arena_len := hwf.1
      have hnxt_ge : cr.toNat + 3 + fullArenaClauseSizeCore s4.core cr.toNat ≤
          fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat := hwf.2.2.1
      have hnxt_le : fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat ≤
          s4.core.arena_len := hwf.2.2.2.1
      have hnext_or : fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat =
          s4.core.arena_len ∨
          fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat ∈
            fullArenaClauseRefs s4 :=
        fullArenaClauseRefs_next_mem_or_end hw4.arena hcr_mem
      have hcr_ar : cr.toNat < (withTr s4 tr').core.arena.length := by
        change _ < s4.core.arena.length; omega
      have hcr2_ar : (cr + 2#64).toNat < (withTr s4 tr').core.arena.length := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; change _ < s4.core.arena.length
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      step_lets
      apply wp_load_of (a := Arg.var _) (c0_load_full_arena hcr_ar hmF)
      step_lets
      apply wp_load_of (a := Arg.var _) (c0_load_full_arena hcr2_ar hmF)
      step_lets
      apply wp_call_of_spec
      refine hNext _ _ _ _ ⟨c, withTr s4 tr', m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
        hsp_tr'.1.lengths, hmF, ?_⟩
      dsimp only
      have hcr32 : (BitVec.setWidth 32 cr).toNat = cr.toNat := by
        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      have hnxt_eq : (BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len
          (BitVec.setWidth 32 cr).toNat)).toNat =
          fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat := by
        rw [BitVec.toNat_ofNat, hcr32]; exact Nat.mod_eq_of_lt (by omega)
      step_lets
      refine wp_join_state0 (α := List (BitVec 32))
        (fun tr'' m'' => tr''.length = 2 * c.max_vars ∧ FullSparseInv c F0 (withTr s4 tr'') ∧
          (FullM6HdrMem c ext (withTr s4 tr'') ⋆ R) m'')
        ?_ ?_
      · intro J3 tr'' m'' ⟨htr''_len, hsp_tr'', hm_tr''⟩
        try simp only [Blocks.get]
        step_jump
        refine ih (_, tr'') m'' ?_ ⟨?_, ?_, htr''_len, hsp_tr'', hm_tr''⟩
        · change s4.core.arena_len - (BitVec.ofNat 32 (fullArenaNextOff s4.core.arena
              s4.core.arena_len (BitVec.setWidth 32 cr).toNat)).toNat < _
          rw [hnxt_eq]; dsimp only; have := hwf.2.1; omega
        · change (BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len
              (BitVec.setWidth 32 cr).toNat)).toNat = s4.core.arena_len ∨
            (BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len
              (BitVec.setWidth 32 cr).toNat)).toNat ∈ fullArenaClauseRefs s4
          rw [hnxt_eq]; exact hnext_or
        · change (BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len
              (BitVec.setWidth 32 cr).toNat)).toNat ≤ _
          rw [hnxt_eq]; exact hnxt_le
      · intro J3 hJ3
        step_jnz
        · step_jnz
          · have hidx : (cr + 2#64).toNat = cr.toNat + 2 := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hbounds : cr.toNat + 3 + (s4.core.arena[(cr + 2#64).toNat]).toNat ≤
                s4.core.arena_len := by
              have hget : (s4.core.arena[(cr + 2#64).toNat]).toNat =
                  (s4.core.arena[cr.toNat + 2]).toNat :=
                congrArg BitVec.toNat (Option.some.inj (by
                  rw [← List.getElem?_eq_getElem hcr2_ar,
                    ← List.getElem?_eq_getElem (by omega), hidx]))
              have hszg : (s4.core.arena[cr.toNat + 2]?.getD 0#32).toNat =
                  (s4.core.arena[cr.toNat + 2]).toNat := by
                rw [List.getElem?_eq_getElem (by omega)]; rfl
              change cr.toNat + 3 + fullArenaClauseSizeCore s4.core cr.toNat ≤
                fullArenaNextOff s4.core.arena s4.core.arena_len cr.toNat at hnxt_ge
              have hcs : fullArenaClauseSizeCore s4.core cr.toNat =
                  (s4.core.arena[cr.toNat + 2]).toNat := hszg
              omega
            apply viv_tier_scan_clause_wp s4 cr _ lim tr' htr'_len hlim hsp_tr' hm_tr' hbounds
            intro tr'' m'' htr'' hsp'' hm''
            exact hJ3 tr'' m'' ⟨htr'', hsp'', hm''⟩
          · step_jump; exact hJ3 tr' m' ⟨htr'_len, hsp_tr', hm_tr'⟩
        · step_jump; exact hJ3 tr' m' ⟨htr'_len, hsp_tr', hm_tr'⟩
    · exact hafter tr' m' htr'_len hsp_tr' hm_tr'

private theorem viv_tier_clause_loop_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hClause : Γ.Has "full_viv_clause_m6" Spec.vivClauseM6Spec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 : List (BitVec 64)}
    (s5 : FullState) (fuel0 : Nat) (bn budget tick_lim : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (hext0 : M6HdrExtOk ext0)
    (hbn_le : bn.toNat ≤ c.red_cap) (hfuel0 : s5.core.fuel.toNat ≤ fuel0)
    (hrr_mem : ∀ k, k < bn.toNat →
      (s5.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s5)
    (hsp5 : FullSparseInv c F0 s5) (hm5 : (FullM6HdrMem c ext0 s5 ⋆ R) m)
    {J5 : Cont [i64, i64, i64]}
    (hJ5 : ∀ rem rc_out j_idx ext' s' m', M6HdrExtOk ext' →
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      FullSparseInv c F0 s' → s'.core.fuel.toNat ≤ fuel0 → (rc_out = 1#64 ∨ rc_out = 20#64) →
      (rc_out = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' →
      J5 (rem, rc_out, j_idx, ()) m') :
    wp Γ Q X (clauseLoopExpr c.hdr c.pRedRefs bn budget tick_lim J5) m := by
  refine wp_while_state (ts := [i64, i64])
    (fun (st : BitVec 64 × BitVec 64 × List (BitVec 64) × FullState) => (st.1, st.2.1, ()))
    (fun st => bn.toNat - st.2.1.toNat)
    (fun (rem, j_idx, ext', s') m' => j_idx.toNat ≤ bn.toNat ∧
      VivTierLoopInv c F0 ext0 s5 fuel0 ext' s' ∧ (FullM6HdrMem c ext' s' ⋆ R) m')
    ?_ ?_
  · intro J6 hJ6; step_jump
    exact hJ6 (budget, 0#64, ext0, s5) m
      ⟨Nat.zero_le _, ⟨hext0, viv_ext_pres_refl ext0, hsp5, hfuel0, rfl, rfl, rfl⟩, hm5⟩
  · intro J6 ⟨rem, j_idx, ext', s'⟩ m'
      ⟨hj_le, ⟨hext', hpres', hsp', hfuel', hal', hrefs', hrr'⟩, hm'⟩ ih
    try simp only [Blocks.get]
    step_jnz
    · rename_i hc; rw [BitVec.ult] at hc
      have hj_lt : j_idx.toNat < bn.toNat := of_decide_eq_true hc
      step_jnz
      · step_lets; have hmF := fullM6HdrMem_focus_full hm'
        apply wp_load_of (a := Arg.var _) (load_full_oom hmF)
        step_jnz
        · step_lets; apply wp_load_of (a := Arg.var _) (load_full_fuel hmF)
          step_jnz
          · apply viv_watermark_step hGetWm hcfg hext' hpres' hsp' hm' 5#64
            intro wm ext1 s1 m1 hext1 hpres1 hsp1 hcore1 _ hrr1 hm1
            have hfuel1 : s1.core.fuel.toNat ≤ fuel0 := by rw [hcore1]; exact hfuel'
            have hal1 : s1.core.arena_len = s5.core.arena_len := by rw [hcore1]; exact hal'
            have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s5 := by
              change fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s5.core
              rw [hcore1]; exact hrefs'
            have hrr1' : s1.scratch.red_refs = s5.scratch.red_refs := hrr1.trans hrr'
            step_jnz
            · have hred := c.hred; have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
              have hidx_lt : (bn - 1#64 - j_idx).toNat < bn.toNat := by
                have hb1 : (bn - 1#64).toNat = bn.toNat - 1 := by
                  rw [BitVec.toNat_sub_of_le
                    (BitVec.le_def.mpr (by rw [BitVec.toNat_ofNat]; omega)), BitVec.toNat_ofNat]
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hb1]; omega
              have hidx_rr : (bn - 1#64 - j_idx).toNat < s1.scratch.red_refs.length := by
                rw [hsp1.1.lengths.scratch_ok.red_refs_len]; omega
              have hcref_mem : (s1.scratch.red_refs[(bn - 1#64 - j_idx).toNat]).toNat ∈
                  fullArenaClauseRefs s1 := by
                have hk := hrr_mem _ hidx_lt
                have hidx_rr5 : (bn - 1#64 - j_idx).toNat < s5.scratch.red_refs.length := by
                  rw [hsp5.1.lengths.scratch_ok.red_refs_len]; omega
                rw [List.getElem?_eq_getElem hidx_rr5] at hk
                have hget : s1.scratch.red_refs[(bn - 1#64 - j_idx).toNat] =
                    s5.scratch.red_refs[(bn - 1#64 - j_idx).toNat] :=
                  Option.some.inj (by
                    rw [← List.getElem?_eq_getElem hidx_rr,
                      ← List.getElem?_eq_getElem hidx_rr5, hrr1'])
                rw [hrefs1, hget]; exact hk
              step_lets; have hm1F := fullM6HdrMem_focus_full hm1
              apply wp_load_of (a := Arg.var _) (c0_load_full_red_refs hidx_rr hm1F)
              step_lets; apply wp_call_of_spec
              rcases hsp1.1.witness with ⟨F_cur, hw1⟩
              have hspW1 : FullSparseInvW c F0 F_cur s1 :=
                ⟨hsp1.1.lengths, hw1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
              refine hClause _ _ _ _ ⟨c, F0, F_cur, ext1, s1, R, rfl, hcfg, hext1, hspW1,
                hcref_mem, hm1, ?_⟩
              intro rc ext2 s2 m2 hext2 hpres2 hspW2 _ _ hfuel2 hal2 hrefs2 hrr2 _ hunsat2 hm2
              have hpres02 := viv_ext_pres_trans hpres1 hpres2
              have hfuel02 : s2.core.fuel.toNat ≤ fuel0 := Nat.le_trans hfuel2 hfuel1
              have hal02 : s2.core.arena_len = s5.core.arena_len := hal2.trans hal1
              have hrefs02 : fullArenaClauseRefs s2 = fullArenaClauseRefs s5 := hrefs2.trans hrefs1
              have hrr02 : s2.scratch.red_refs = s5.scratch.red_refs := hrr2.trans hrr1'
              step_jnz
              · rename_i hc
                have h20 : rc = 20#64 := of_decide_eq_true hc
                step_jump
                exact hJ5 (rem - 1#64) 20#64 j_idx ext2 s2 m2 hext2 hpres02
                  (viv_sparseW_to_sparse hspW2) hfuel02 (Or.inr rfl) (fun _ => hunsat2 h20) hm2
              · step_jnz
                · step_jump
                  exact hJ5 (rem - 1#64) 1#64 j_idx ext2 s2 m2 hext2 hpres02
                    (viv_sparseW_to_sparse hspW2) hfuel02 (Or.inl rfl) (fun h => by cases h) hm2
                · refine wp_join_state0 (α := List (BitVec 64) × FullState)
                    (fun (ext3, s3) m3 => VivTierLoopInv c F0 ext0 s5 fuel0 ext3 s3 ∧
                      (FullM6HdrMem c ext3 s3 ⋆ R) m3)
                    ?_ ?_
                  · intro J7 ⟨ext3, s3⟩ m3 ⟨hinv3, hm3⟩
                    try simp only [Blocks.get]
                    step_jump
                    have hj1 : (j_idx + 1#64).toNat = j_idx.toNat + 1 := by
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                    exact ih (rem - 1#64, j_idx + 1#64, ext3, s3) m3
                      (by dsimp only; rw [hj1]; omega)
                      ⟨by rw [hj1]; omega, hinv3, hm3⟩
                  · intro J7 hJ7
                    step_lets; have hm2F := fullM6HdrMem_focus_full hm2
                    apply wp_load_of (a := Arg.var _) (load_full_cur_level hm2F)
                    step_jnz
                    · rename_i hc
                      have hcl2_eq : s2.core.cur_level = 0 :=
                        bv64_eq_zero_of_eq_true
                          (full_cur_level_lt64 (viv_sparseW_to_sparse hspW2)) hc
                      apply wp_call_of_spec
                      refine hProp _ _ _ _ ⟨c, F0, F_cur, ext2, s2, R, rfl, hcfg, hext2,
                        hspW2.1, hspW2.2.1, hspW2.2.2.2.2.2, hm2, ?_⟩
                      intro pr ext3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 unass3 unfl3
                        wvec3 arena3 wstk3 wlen3 wu3 fuel3 ctype3 cref3 c0_3 c1_3 oom3 sc3 m3 s3
                        hext3 hpres3 hlen3 hw3 _ _ har3 hps3 hrr3 _ _ _ hfuel3 _ _ hconfl3 _ _ hm3
                      have hspW3 := viv_sparseInvW_of_prop_canon hspW2 hlen3 hw3 har3 hps3
                      have hpres03 := viv_ext_pres_trans hpres02 hpres3
                      have hfuel03 : fuel3.toNat ≤ fuel0 := Nat.le_trans hfuel3 hfuel02
                      have hrefs03 : fullArenaClauseRefs s3 = fullArenaClauseRefs s5 := by
                        change fullArenaClauseRefsCore _ = _; rw [har3.2.1]; exact hrefs02
                      have hrr03 : sc3.red_refs = s5.scratch.red_refs := hrr3.trans hrr02
                      step_jnz
                      · rename_i hc; have hpr1 : pr = 1#64 := of_decide_eq_true hc
                        have hunsat3 := Spec.level0_unsat_of_conflict_okW hspW3.2.1 hcl2_eq
                          (hconfl3 hpr1).2.2
                        step_jump
                        exact hJ5 (rem - 1#64) 20#64 j_idx ext3 s3 m3 hext3 hpres03
                          (viv_sparseW_to_sparse hspW3) hfuel03 (Or.inr rfl)
                          (fun _ => hunsat3) hm3
                      · step_jump
                        exact hJ7 (ext3, s3) m3
                          ⟨⟨hext3, hpres03, viv_sparseW_to_sparse hspW3, hfuel03, hal02,
                            hrefs03, hrr03⟩, hm3⟩
                    · step_jump
                      exact hJ7 (ext2, s2) m2
                        ⟨⟨hext2, hpres02, viv_sparseW_to_sparse hspW2, hfuel02, hal02,
                          hrefs02, hrr02⟩, hm2⟩
            · step_jump; exact hJ5 rem 1#64 j_idx ext1 s1 m1 hext1 hpres1 hsp1 hfuel1
                (Or.inl rfl) (fun h => by cases h) hm1
          · step_jump; exact hJ5 rem 1#64 j_idx ext' s' m' hext' hpres' hsp' hfuel'
              (Or.inl rfl) (fun h => by cases h) hm'
        · step_jump; exact hJ5 rem 1#64 j_idx ext' s' m' hext' hpres' hsp' hfuel'
            (Or.inl rfl) (fun h => by cases h) hm'
      · step_jump; exact hJ5 rem 1#64 j_idx ext' s' m' hext' hpres' hsp' hfuel'
          (Or.inl rfl) (fun h => by cases h) hm'
    · step_jump; exact hJ5 rem 1#64 j_idx ext' s' m' hext' hpres' hsp' hfuel'
        (Or.inl rfl) (fun h => by cases h) hm'

private theorem viv_tier_finish_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hClear : Γ.Has "full_viv_clear_tier_m6" Spec.fullVivClearTierM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 ext : List (BitVec 64)}
    (s0 : FullState) {s : FullState} (mode bn old_p rc rem rc_out j_idx : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hQ : ∀ r ext' s' m', VivHdrInv c F0 ext0 (withProbing s0 old_p) ext' s' →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (hext : M6HdrExtOk ext)
    (hpres : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext ∧ M6ExtW2bPres ext0 ext)
    (hsp : FullSparseInv c F0 s) (hfuel : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hrc_eq : rc_out = 1#64 ∨ rc_out = 20#64) (hunsat : rc_out = 20#64 → F0.Unsat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    wp Γ Q X (tierFinishExpr c.hdr mode bn old_p rc rem rc_out j_idx) m := by
  refine wp_join_state0 (α := FullState)
    (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.cur_level = 0 ∧
      s6.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext s6 ⋆ R) m6)
    ?_ ?_
  · intro J6 s6 m6 ⟨hsp6, hcl6, hfuel6, hm6⟩
    try simp only [Blocks.get]
    refine wp_join_state0 (α := FullState)
      (fun s7 m7 => FullSparseInv c F0 s7 ∧ s7.core.cur_level = 0 ∧
        s7.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext s7 ⋆ R) m7)
      ?_ ?_
    · intro J7 s7 m7 ⟨hsp7, hcl7, hfuel7, hm7⟩
      try simp only [Blocks.get]
      step_lets; have hm7F := fullM6HdrMem_focus_full hm7
      apply wp_store_of (a := Arg.var _) (store_full_res_sz j_idx hm7F)
      intro hm8F; have hsp8 := viv_sparse_with_res_sz hsp7 j_idx
      step_lets; apply wp_store_of (a := Arg.var _) (store_full_probing old_p hm8F)
      intro hm9F; have hsp9 := viv_with_probing hsp8 old_p
      have hm9 := fullM6HdrMem_unfocus_full hm9F
      step_ret
      exact hQ rc_out ext _ _ ⟨hext, hpres, hsp9, hcl7, rfl, hfuel7⟩ hrc_eq hunsat hm9
    · intro J7 hJ7
      step_jnz
      · step_jnz
        · step_jnz
          · apply wp_call_of_spec; have hm6F := fullM6HdrMem_focus_full hm6
            refine hClear _ _ _ _ ⟨c, F0, s6, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp6,
              hcl6, hm6F, ?_⟩
            intro s7 m7 hsp7 hcl7 hfl7 hm7F
            step_jump
            exact hJ7 s7 m7 ⟨hsp7, hcl7, by rw [hfl7]; exact hfuel6, fullM6HdrMem_unfocus_full hm7F⟩
          · step_jump; exact hJ7 s6 m6 ⟨hsp6, hcl6, hfuel6, hm6⟩
        · step_jump; exact hJ7 s6 m6 ⟨hsp6, hcl6, hfuel6, hm6⟩
      · step_jump; exact hJ7 s6 m6 ⟨hsp6, hcl6, hfuel6, hm6⟩
  · intro J6 hJ6
    apply viv_backtrack0_guard_wp hBt hsp hm
    intro s6 m6 hsp6 hcl6 _ hfl6 _ _ _ _ hm6
    exact hJ6 s6 m6 ⟨hsp6, hcl6, by rw [hfl6]; exact hfuel, hm6⟩

private theorem full_vivify_tier_m6_hdr_wp_aux (Γ : Env)
    (hCollect : Γ.Has "full_viv_collect_fid" Spec.vivCollectFidSpec)
    (hSort : Γ.Has "full_viv_sort_fid" Spec.fullVivSortFidSpec)
    (hClear : Γ.Has "full_viv_clear_tier_m6" Spec.fullVivClearTierM6Spec)
    (hClause : Γ.Has "full_viv_clause_m6" Spec.vivClauseM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (c : FullCfg) (F0 : Std.Sat.CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (mode budget tick_lim : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (R : Mem 64 → Prop) (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      s'.core.probing = s.core.probing → (budget ≠ 0#64 → s'.core.cur_level = 0) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (full_vivify_tier_m6_hdr_body Val Cont (c.hdr, mode, budget, tick_lim, ())) m := by
  dsimp only [full_vivify_tier_m6_hdr_body]
  step_jnz
  · rename_i hc; step_ret
    exact hQ 1#64 ext s m ⟨hext, viv_ext_pres_refl ext⟩ hsp id rfl
      (fun hne => absurd (of_decide_eq_true hc) hne) (Nat.le_refl _) (Or.inl rfl)
      (fun h => by cases h) hm
  · refine wp_join_state0 (α := FullState)
      (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.probing = s.core.probing ∧ s1.core.fuel = s.core.fuel ∧
        (FullM6HdrMem c ext s1 ⋆ R) m1)
      ?_ ?_
    · intro J0 s1 m1 ⟨hsp1, hcl1, hpr1, hfl1, hm1⟩
      try simp only [Blocks.get]
      step_lets; have hm1F := fullM6HdrMem_focus_full hm1
      apply wp_load_of (a := Arg.var _) (load_full_probing hm1F)
      step_lets; apply wp_store_of (a := Arg.var _) (store_full_probing 1#64 hm1F)
      intro hm2F; have hsp2 := viv_with_probing hsp1 1#64
      step_lets; apply wp_load_of (a := Arg.var _) (load_full_red_refs_ptr hm2F)
      step_lets; apply wp_load_of (a := Arg.var _) (load_full_red_cap hm2F)
      step_lets; apply wp_call_of_spec
      refine hCollect _ _ _ _ ⟨c, F0, withProbing s1 1#64,
        m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp2, hm2F, ?_⟩
      intro bn arena3 rr3 m3F s3 hbn_le hrr3_len hsp3 hrefs3 hrr3_mem hm3F
      have hm3 := fullM6HdrMem_unfocus_full hm3F
      step_lets; apply wp_load_of (a := Arg.var _) (load_full_cur_vars hm3F)
      step_lets; apply wp_load_of (a := Arg.var _) (load_full_tarjan_reach_ptr hm3F)
      step_lets; apply wp_load_of (a := Arg.var _) (load_full_arena_ptr hm3F)
      have hcv_le := hsp3.1.lengths.core_ok.cur_vars_le
      have hmv := c.hmaxv; have hdb : Examples.Kissat.Ref.dimacsBound = 2 ^ 28 := rfl
      have hlim_nat : (BitVec.ofNat 64 s3.core.cur_vars <<< BitVec.signExtend 64 1#32).toNat =
          2 * s3.core.cur_vars := by
        have hs1 : BitVec.signExtend 64 1#32 = 1#64 := by decide
        have hlt : s3.core.cur_vars < 2 ^ 29 := by
          change s3.core.cur_vars ≤ c.max_vars at hcv_le; omega
        rw [hs1]
        change (BitVec.ofNat 64 s3.core.cur_vars <<< (1#64).toNat).toNat = _
        have h1 : (1 : Nat) % 2 ^ 64 = 1 := by decide
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (by omega)]
        omega
      apply viv_tier_zero_tr_loop_wp _ hsp3 hm3 _ hlim_nat
      intro tr4 m4 htr4_len hsp4 hm4
      apply viv_tier_scan_arena_wp hNext s3 _ tr4 htr4_len hlim_nat hsp4 hm4
      intro tr5 m5 htr5_len hsp5 hm5
      refine wp_join_state_pure (ts := [Ty.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
        ?_ ?_
      · intro Jdo do_sort _
        try simp only [Blocks.get]
        refine wp_join_state0 (α := FullState)
          (fun s5 m5' => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
            s5.core.fuel = s.core.fuel ∧ s5.scratch.red_refs.length = c.red_cap ∧
            (∀ k, k < bn.toNat →
              (s5.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s5) ∧
            (FullM6HdrMem c ext s5 ⋆ R) m5')
          ?_ ?_
        · intro J4 s5 m5' ⟨hsp5', hcl5', hfl5', hrr5_len, hrr5_mem, hm5'⟩
          try simp only [Blocks.get]
          refine wp_join_state (ts := [i64, i64, i64])
            (α := BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64) × FullState)
            (fun st => (st.1, st.2.1, st.2.2.1, ()))
            (fun (rem, rc_out, j_idx, ext', s') m' => M6HdrExtOk ext' ∧
              (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
              FullSparseInv c F0 s' ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (rc_out = 1#64 ∨ rc_out = 20#64) ∧ (rc_out = 20#64 → F0.Unsat) ∧
              (FullM6HdrMem c ext' s' ⋆ R) m')
            ?_ ?_
          · intro J5 ⟨rem, rc_out, j_idx, ext', s'⟩ m'
              ⟨hext', hpres', hsp', hfuel', hrc_eq, hunsat, hm'⟩
            try simp only [Blocks.get]
            apply viv_tier_finish_wp hClear hBt s mode bn s1.core.probing
              (BitVec.ofNat 64 c.red_cap) rem rc_out j_idx
              (fun r extf sf mf hinv hr hu hmf =>
                hQ r extf sf mf ⟨hinv.1, hinv.2.1⟩ hinv.2.2.1
                  (fun _ => hinv.2.2.2.1) (by rw [hinv.2.2.2.2.1, hpr1])
                  (fun _ => hinv.2.2.2.1) hinv.2.2.2.2.2 hr hu hmf)
              hext' hpres' hsp' hfuel' hrc_eq hunsat hm'
          · intro J5 hJ5
            apply viv_tier_clause_loop_wp hClause hProp hGetWm s5 s.core.fuel.toNat bn budget
              tick_lim hcfg hext hbn_le (by rw [hfl5']; exact Nat.le_refl _) hrr5_mem hsp5' hm5'
              (fun rem rc_out j_idx ext' s' m' a b d e f g h =>
                hJ5 (rem, rc_out, j_idx, ext', s') m' ⟨a, b, d, e, f, g, h⟩)
        · intro J4 hJ4
          step_jnz
          · apply wp_call_of_spec; have hm5F := fullM6HdrMem_focus_full hm5
            refine hSort _ _ _ _ ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp5,
              hbn_le, hrr3_mem, hm5F, ?_⟩
            intro rr' scr' m5' hrr'_len hscr'_len hrr'_mem hm5F'
            step_jump
            exact hJ4 _ _ ⟨viv_sparse_with_rr_scr hsp5 hrr'_len hscr'_len, hcl1, hfl1, hrr'_len,
              hrr'_mem, fullM6HdrMem_unfocus_full hm5F'⟩
          · step_jump; exact hJ4 _ m5 ⟨hsp5, hcl1, hfl1, hrr3_len, hrr3_mem, hm5⟩
      · intro Jdo hJdo
        step_jnz
        · step_jump; exact hJdo true trivial
        · step_lets; have hm5F := fullM6HdrMem_focus_full hm5
          apply wp_load_of (a := Arg.var _) (load_full_num_irred hm5F)
          step_lets; apply wp_load_of (a := Arg.var _) (load_full_num_redundant hm5F)
          step_jnz
          · step_jump; exact hJdo true trivial
          · step_jump; exact hJdo false trivial
    · intro J0 hJ0
      apply viv_backtrack0_guard_wp hBt hsp hm
      intro s1 m1 hsp1 hcl1 hpr1 hfl1 _ _ _ _ hm1
      exact hJ0 s1 m1 ⟨hsp1, hcl1, hpr1, hfl1, hm1⟩

private theorem viv_sat_add_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (wm q : BitVec 64) {J : Cont [i64]} (hJ : ∀ r, J (r, ()) m) :
    wp Γ Q X
      (Expr.let_ (op1 (OpCode.not i64) (Arg.imm 0#64)) fun z0 =>
       Expr.let_ (op2 (OpCode.sub i64) (Arg.var z0.1) (Arg.var q)) fun nq =>
       Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var wm) (Arg.var nq.1)) fun cov =>
       Expr.jnz (Arg.var cov.1)
         (Expr.let_ (op1 (OpCode.not i64) (Arg.imm 0#64)) fun z1 =>
          Expr.jump J (Arg.var z1.1, ()))
         (Expr.let_ (op2 (OpCode.add i64) (Arg.var wm) (Arg.var q)) fun s1 =>
          Expr.jump J (Arg.var s1.1, ()))) m := by
  step_jnz <;> (step_jump; exact hJ _)

private theorem viv_tier_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hTier : Γ.Has "full_vivify_tier_m6_hdr" Spec.vivifyTierM6HdrSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hcfg : FullM6HdrCfgOk c)
    (hinv : VivHdrInv c F0 ext0 s0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (mode tick_lim : BitVec 64) {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : ∀ r ext' s' m', VivHdrInv c F0 ext0 s0 ext' s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (@Expr.call Val Cont rs "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
      (Arg.var c.hdr, Arg.imm mode, Arg.imm 4294967295#64, Arg.var tick_lim, ()) k) m := by
  apply wp_call_of_spec
  refine hTier _ _ _ _ ⟨c, F0, ext, s, R, rfl, hcfg, hinv.1, hinv.2.2.1, hm, ?_⟩
  intro r ext' s' m' ⟨hext', hpres'⟩ hsp' _ hpr' hcl' hfl' hr' hu' hm'
  exact hk r ext' s' m' ⟨hext', viv_ext_pres_trans hinv.2.1 hpres', hsp', hcl' (by decide),
    hpr'.trans hinv.2.2.2.2.1, Nat.le_trans hfl' hinv.2.2.2.2.2⟩ hr' hu' hm'

private theorem viv_top_cond_tier_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hTier : Γ.Has "full_vivify_tier_m6_hdr" Spec.vivifyTierM6HdrSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 : List (BitVec 64)} {s0 : FullState}
    (mode : BitVec 64) (rc_prev wm_prev lim_arg tot_slice tot : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (htot : tot ≠ 0#64)
    {ext_in : List (BitVec 64)} {s_in : FullState}
    (hinv_in : VivHdrInv c F0 ext0 s0 ext_in s_in)
    (hrc_ok : rc_prev = 1#64 ∨ rc_prev = 20#64) (hunsat_in : rc_prev = 20#64 → F0.Unsat)
    (hm_in : (FullM6HdrMem c ext_in s_in ⋆ R) m) {Jnext : Cont [i64, i64]}
    (hJnext : ∀ rc_out wm_out ext' s' m', VivHdrInv c F0 ext0 s0 ext' s' →
      (rc_out = 1#64 ∨ rc_out = 20#64) → (rc_out = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Jnext (rc_out, wm_out, ()) m') :
    wp Γ Q X (condTierExpr c.hdr mode rc_prev wm_prev lim_arg tot_slice tot Jnext) m := by
  step_jnz
  · step_jnz
    · step_let1; apply wp_udiv; · exact htot
      rintro _ h_; subst h_
      refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
        ?_ ?_
      · intro Jt lim _
        try simp only [Blocks.get]
        apply viv_tier_step hTier hcfg hinv_in hm_in mode lim
        intro r ext' s' m' hinv' hr' hu' hm'
        step_jump; exact hJnext r lim ext' s' m' hinv' hr' hu' hm'
      · intro Jt hJt
        exact viv_sat_add_wp wm_prev _ (fun r => hJt r trivial)
    · step_jump; exact hJnext rc_prev wm_prev ext_in s_in m hinv_in hrc_ok hunsat_in hm_in
  · step_jump; exact hJnext rc_prev wm_prev ext_in s_in m hinv_in hrc_ok hunsat_in hm_in

private theorem viv_top_delay_adjust_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hBump : Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hReduce : Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext0 : List (BitVec 64)} {s0 : FullState}
    (r4 lim4 ld_vc ld_unass ld_rsz : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hcfg : FullM6HdrCfgOk c) {ext4 : List (BitVec 64)} {s4 : FullState}
    (hinv4 : VivHdrInv c F0 ext0 s0 ext4 s4) (_hr4_ok : r4 = 1#64 ∨ r4 = 20#64)
    (_hunsat4 : r4 = 20#64 → F0.Unsat) (hm4 : (FullM6HdrMem c ext4 s4 ⋆ R) m)
    {J11 : Cont [i64, i64]}
    (hJ11 : ∀ ext' s' m', VivHdrInv c F0 ext0 s0 ext' s' → (FullM6HdrMem c ext' s' ⋆ R) m' →
      J11 (r4, lim4, ()) m') :
    wp Γ Q X (delayAdjustExpr c.hdr r4 lim4 ld_vc ld_unass ld_rsz J11) m := by
  refine wp_join_state0 (α := List (BitVec 64) × FullState)
    (fun (ext', s') m' => VivHdrInv c F0 ext0 s0 ext' s' ∧ (FullM6HdrMem c ext' s' ⋆ R) m')
    ?_ ?_
  · intro J22 ⟨ext', s'⟩ m' ⟨hinv', hm'⟩
    try simp only [Blocks.get]; step_jump; exact hJ11 ext' s' m' hinv' hm'
  · intro J22 hJ22
    step_jnz
    · refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
        ?_ ?_
      · intro J32 du _
        try simp only [Blocks.get]; step_lets
        have hm4F := fullM6HdrMem_focus_full hm4
        apply wp_load_of (a := Arg.var _) (load_full_viv_cnt hm4F)
        step_lets
        refine wp_join_state0 (α := List (BitVec 64) × FullState)
          (fun (ext5, s5) m5 => VivHdrInv c F0 ext0 s0 ext5 s5 ∧ (FullM6HdrMem c ext5 s5 ⋆ R) m5)
          ?_ ?_
        · intro J33 ⟨ext5, s5⟩ m5 ⟨hinv5, hm5⟩
          try simp only [Blocks.get]; step_jump; exact hJ22 (ext5, s5) m5 ⟨hinv5, hm5⟩
        · intro J33 hJ33
          refine wp_join_state0 (α := Unit) (fun _ m' => m' = m ∧ m = m) ?_ ?_
          · intro J43 _ _ ⟨rfl, _⟩
            try simp only [Blocks.get]
            apply viv_w2a_step hBump hcfg hinv4.1 hinv4.2.1 hinv4.2.2.1 hm4 (Arg.imm 3#64, ())
            intro _ ext5 s5 m5 hext5 hpres5 hsp5 hcore5 _ hm5
            step_jump
            exact hJ33 (ext5, s5) m5
              ⟨⟨hext5, hpres5, hsp5, by rw [hcore5]; exact hinv4.2.2.2.1,
                by rw [hcore5]; exact hinv4.2.2.2.2.1,
                by rw [hcore5]; exact hinv4.2.2.2.2.2⟩, hm5⟩
          · intro J43 hJ43
            step_jnz
            · step_jump; exact hJ43 () m ⟨rfl, rfl⟩
            · step_jnz
              · step_jump; exact hJ43 () m ⟨rfl, rfl⟩
              · apply viv_w2a_step hReduce hcfg hinv4.1 hinv4.2.1 hinv4.2.2.1 hm4
                  (Arg.imm 3#64, ())
                intro _ ext5 s5 m5 hext5 hpres5 hsp5 hcore5 _ hm5
                step_jump
                exact hJ33 (ext5, s5) m5
                  ⟨⟨hext5, hpres5, hsp5, by rw [hcore5]; exact hinv4.2.2.2.1,
                    by rw [hcore5]; exact hinv4.2.2.2.2.1,
                    by rw [hcore5]; exact hinv4.2.2.2.2.2⟩, hm5⟩
      · intro J32 hJ32; step_lets
        have hm4F := fullM6HdrMem_focus_full hm4
        apply wp_load_of (a := Arg.var _) (load_full_unassigned hm4F)
        step_jnz
        · step_lets; apply wp_load_of (a := Arg.var _) (load_full_unassigned hm4F)
          step_jump; exact hJ32 _ trivial
        · step_jump; exact hJ32 _ trivial
    · step_jump; exact hJ22 (ext4, s4) m ⟨hinv4, hm4⟩

private abbrev TopPost (c : FullCfg) (F0 : Std.Sat.CNF Nat) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop)
    (st : BitVec 64 × BitVec 64 × List (BitVec 64) × FullState) (m : Mem 64) : Prop :=
  VivHdrInv c F0 ext s st.2.2.1 st.2.2.2 ∧ (st.1 = 1#64 ∨ st.1 = 20#64) ∧
    (st.1 = 20#64 → F0.Unsat) ∧ (FullM6HdrMem c st.2.2.1 st.2.2.2 ⋆ R) m

private theorem viv_top_bt0_tier12_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hGetTier1 : Γ.Has "m6_hdr_get_tier1" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hGetTier2 : Γ.Has "m6_hdr_get_tier2" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hsp : FullSparseInv c F0 s) (hm : (FullM6HdrMem c ext s ⋆ R) m) {k : Expr Val Cont rs}
    (hk : ∀ ext2 s2 m2, VivHdrInv c F0 ext s ext2 s2 →
      (FullM6HdrMem c ext2 s2 ⋆ R) m2 → wp Γ Q X k m2) :
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _J0 =>
          Blocks.cons
            (fun _ =>
              @Expr.call Val Cont rs "m6_hdr_get_tier1" [i64, Ty.bool] [i64]
                (Arg.var c.hdr, Arg.imm true, ()) fun r_t1 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var c.hdr) (Arg.imm 696#64)) fun p1 =>
              Expr.store (Arg.var r_t1.1) (Arg.var p1.1)
                (@Expr.call Val Cont rs "m6_hdr_get_tier2" [i64, Ty.bool] [i64]
                   (Arg.var c.hdr, Arg.imm true, ()) fun r_t2 =>
                 Expr.let_ (op2 (OpCode.add i64) (Arg.var c.hdr) (Arg.imm 704#64)) fun p2 =>
                 Expr.store (Arg.var r_t2.1) (Arg.var p2.1) k))
            Blocks.nil)
        (fun J0 => bt0GuardExpr c.hdr J0.1)) m := by
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => VivHdrInv c F0 ext s ext s1 ∧ (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
  · intro _J0 s1 m1 ⟨hinv1, hm1⟩; try simp only [Blocks.get]
    apply viv_w2a_step hGetTier1 hcfg hinv1.1 hinv1.2.1 hinv1.2.2.1 hm1 (Arg.imm true, ())
    intro r_t1 ext1 s1a m1a hext1 hpres1 hsp1a hcore1a _ hm1a
    step_lets; have hm1aF := fullM6HdrMem_focus_full hm1a
    apply wp_store_of (a := Arg.var _) (store_full_tier1 r_t1.1 hm1aF)
    intro hm1bF; have hsp1b := viv_sparse_with_tier1 hsp1a r_t1.1
    apply viv_w2a_step hGetTier2 hcfg hext1 hpres1 hsp1b
      (fullM6HdrMem_unfocus_full hm1bF) (Arg.imm true, ())
    intro r_t2 ext2 s2a m2a hext2 hpres2 hsp2a hcore2a _ hm2a
    step_lets; have hm2aF := fullM6HdrMem_focus_full hm2a
    apply wp_store_of (a := Arg.var _) (store_full_tier2 r_t2.1 hm2aF)
    intro hm2bF; have hsp2b := viv_sparse_with_tier2 hsp2a r_t2.1
    exact hk ext2 _ _ ⟨hext2, hpres2, hsp2b,
      by change s2a.core.cur_level = 0; rw [hcore2a]; change s1a.core.cur_level = 0
         rw [hcore1a]; exact hinv1.2.2.2.1,
      by change s2a.core.probing = s.core.probing; rw [hcore2a]; change s1a.core.probing = _
         rw [hcore1a]; exact hinv1.2.2.2.2.1,
      by change s2a.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcore2a]
         change s1a.core.fuel.toNat ≤ _; rw [hcore1a]; exact hinv1.2.2.2.2.2⟩
      (fullM6HdrMem_unfocus_full hm2bF)
  · intro J0 hJ0; apply viv_backtrack0_guard_wp hBt hsp hm
    intro s1 m1 hsp1 hcl1 hpr1 hfl1 _ _ _ _ hm1
    exact hJ0 s1 m1
      ⟨⟨hext, viv_ext_pres_refl ext, hsp1, hcl1, hpr1, by rw [hfl1]; exact Nat.le_refl _⟩, hm1⟩

private theorem full_vivify_m6_hdr_wp_aux (Γ : Env)
    (hTier : Γ.Has "full_vivify_tier_m6_hdr" Spec.vivifyTierM6HdrSpec)
    (hGetTier1 : Γ.Has "m6_hdr_get_tier1" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hGetTier2 : Γ.Has "m6_hdr_get_tier2" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    (hSync : Γ.Has "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] []))
    (hBump : Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hReduce : Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hDelaying : Γ.Has "m6_hdr_delaying" (m6HdrW2aSpec [i64] [Ty.bool]))
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (c : FullCfg) (F0 : Std.Sat.CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (m : Mem 64) (Q : Post [i64]) (X : XPost) (R : Mem 64 → Prop)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (full_vivify_m6_hdr_body Val Cont (c.hdr, ())) m := by
  dsimp only [full_vivify_m6_hdr_body]
  apply viv_top_bt0_tier12_wp hGetTier1 hGetTier2 hBt hcfg hext hsp hm
  intro ext2 s2 m2b hinv2 hm2b
  refine wp_join_state (ts := [i64]) (α := BitVec 64 × List (BitVec 64) × FullState)
    (fun st => (st.1, ()))
    (fun (b4, ext3, s3) m3 => VivHdrInv c F0 ext s ext3 s3 ∧ (FullM6HdrMem c ext3 s3 ⋆ R) m3)
    ?_ ?_
  · intro J105 ⟨b4, ext3, s3⟩ m3 ⟨hinv3, hm3⟩; try simp only [Blocks.get]
    refine wp_join_state_pure (ts := [i64]) (fun x => (x, ())) (fun _ => True) ?_ ?_
    · intro J206 b5 _; try simp only [Blocks.get]
      refine wp_join_state_pure (ts := [i64]) (fun x => (x, ())) (fun _ => True) ?_ ?_
      · intro J307 b6 _; try simp only [Blocks.get]
        refine wp_join_state_pure (ts := [i64]) (fun x => (x, ())) (fun _ => True) ?_ ?_
        · intro J408 b7 _; try simp only [Blocks.get]; step_jnz
          · step_ret
            exact hQ 1#64 ext3 s3 m3 ⟨hinv3.1, hinv3.2.1⟩ hinv3.2.2.1
              ⟨hinv3.2.2.2.1, hinv3.2.2.2.2.1⟩ hinv3.2.2.2.2.2 (Or.inl rfl)
              (fun h => by cases h) hm3
          · rename_i hc; have htot_ne : b4 + b5 + b6 + b7 ≠ 0#64 := of_decide_eq_false hc
            step_lets; have hm3F := fullM6HdrMem_focus_full hm3
            apply wp_load_of (a := Arg.var _) (load_full_search_ticks hm3F)
            apply viv_watermark_step hGetWm hcfg hinv3.1 hinv3.2.1 hinv3.2.2.1 hm3 0#64
            intro wm0 ext4 s4 m4 hext4 hpres4 hsp4 hcore4 _ _ hm4
            have hinv4 : VivHdrInv c F0 ext s ext4 s4 :=
              ⟨hext4, hpres4, hsp4, by rw [hcore4]; exact hinv3.2.2.2.1,
               by rw [hcore4]; exact hinv3.2.2.2.2.1, by rw [hcore4]; exact hinv3.2.2.2.2.2⟩
            refine wp_join_state_pure (ts := [i64]) (fun x => (x, ())) (fun _ => True) ?_ ?_
            · intro J516 _ _; try simp only [Blocks.get]
              refine wp_join_state_pure (ts := [i64]) (fun x => (x, ())) (fun _ => True) ?_ ?_
              · intro J617 ticks_lim _; try simp only [Blocks.get]; step_lets
                refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
                  (fun p => (p.1, p.2, ())) (fun _ => True) ?_ ?_
                · intro J719 ⟨w1, w2⟩ _; try simp only [Blocks.get]
                  apply viv_watermark_step hGetWm hcfg hinv4.1 hinv4.2.1 hinv4.2.2.1 hm4 5#64
                  intro wm5 ext5 s5 m5 hext5 hpres5 hsp5 hcore5 _ _ hm5
                  have hinv5 : VivHdrInv c F0 ext s ext5 s5 :=
                    ⟨hext5, hpres5, hsp5, by rw [hcore5]; exact hinv4.2.2.2.1,
                     by rw [hcore5]; exact hinv4.2.2.2.2.1, by rw [hcore5]; exact hinv4.2.2.2.2.2⟩
                  refine wp_join_state (ts := [i64, i64])
                    (fun st => (st.1, st.2.1, ())) (TopPost c F0 ext s R) ?_ ?_
                  · intro J822 ⟨r1, wm1, ext6, s6⟩ m6 ⟨hinv6, hr1_ok, hu1, hm6⟩
                    try simp only [Blocks.get]
                    refine wp_join_state (ts := [i64, i64])
                      (fun st => (st.1, st.2.1, ())) (TopPost c F0 ext s R) ?_ ?_
                    · intro J924 ⟨r2, wm2, ext7, s7⟩ m7 ⟨hinv7, hr2_ok, hu2, hm7⟩
                      try simp only [Blocks.get]
                      refine wp_join_state (ts := [i64, i64])
                        (fun st => (st.1, st.2.1, ())) (TopPost c F0 ext s R) ?_ ?_
                      · intro J1026 ⟨r3, wm3, ext8, s8⟩ m8 ⟨hinv8, hr3_ok, hu3, hm8⟩
                        try simp only [Blocks.get]
                        refine wp_join_state (ts := [i64, i64])
                          (fun st => (st.1, st.2.1, ())) (TopPost c F0 ext s R) ?_ ?_
                        · intro J1128 ⟨r4, _, ext9, s9⟩ m9 ⟨hinv9, hr4_ok, hu4, hm9⟩
                          try simp only [Blocks.get]
                          apply viv_w2a_step hSync hcfg hinv9.1 hinv9.2.1 hinv9.2.2.1 hm9 ()
                          intro _ ext10 s10 m10 hext10 hpres10 hsp10 hcore10 _ hm10; step_ret
                          exact hQ r4 ext10 s10 m10 ⟨hext10, hpres10⟩ hsp10
                            ⟨by rw [hcore10]; exact hinv9.2.2.2.1,
                             by rw [hcore10]; exact hinv9.2.2.2.2.1⟩
                            (by rw [hcore10]; exact hinv9.2.2.2.2.2) hr4_ok hu4 hm10
                        · intro J1128 hJ1128; step_jnz
                          · step_jnz
                            · step_let1; apply wp_udiv; · exact htot_ne
                              rintro _ h_; subst h_
                              refine wp_join_state_pure (ts := [i64]) (fun x => (x, ()))
                                (fun _ => True) ?_ ?_
                              · intro J2132 lim4 _; try simp only [Blocks.get]; step_lets
                                have hm8F := fullM6HdrMem_focus_full hm8
                                apply wp_load_of (a := Arg.var _) (load_full_viv_cnt hm8F)
                                step_lets; apply wp_load_of (a := Arg.var _)
                                  (load_full_unassigned hm8F)
                                step_lets; apply viv_tier_step hTier hcfg hinv8 hm8 0#64 lim4
                                intro r4 ext8b s8b m8b hinv8b hr4_ok hu4 hm8b; step_lets
                                have hm8bF := fullM6HdrMem_focus_full hm8b
                                apply wp_load_of (a := Arg.var _) (load_full_res_sz hm8bF)
                                apply viv_top_delay_adjust_wp hBump hReduce r4 lim4 _ _ _ hcfg
                                  hinv8b hr4_ok hu4 hm8b
                                intro ext9 s9 m9 hinv9 hm9
                                exact hJ1128 (r4, lim4, ext9, s9) m9 ⟨hinv9, hr4_ok, hu4, hm9⟩
                              · intro J2132 hJ2132
                                exact viv_sat_add_wp wm3 _ (fun r => hJ2132 r trivial)
                            · step_jump
                              exact hJ1128 (r3, wm3, ext8, s8) m8 ⟨hinv8, hr3_ok, hu3, hm8⟩
                          · step_jump
                            exact hJ1128 (r3, wm3, ext8, s8) m8 ⟨hinv8, hr3_ok, hu3, hm8⟩
                      · intro J1026 hJ1026
                        apply viv_top_cond_tier_wp hTier 3#64 r2 wm2 b7 (ticks_lim / 10#64)
                          (b4 + b5 + b6 + b7) hcfg htot_ne hinv7 hr2_ok hu2 hm7
                        intro rc3 wm3 ext8 s8 m8 a b d hm8
                        exact hJ1026 (rc3, wm3, ext8, s8) m8 ⟨a, b, d, hm8⟩
                    · intro J924 hJ924
                      apply viv_top_cond_tier_wp hTier 2#64 r1 wm1 w2 (ticks_lim / 10#64)
                        (b4 + b5 + b6 + b7) hcfg htot_ne hinv6 hr1_ok hu1 hm6
                      intro rc2 wm2 ext7 s7 m7 a b d hm7
                      exact hJ924 (rc2, wm2, ext7, s7) m7 ⟨a, b, d, hm7⟩
                  · intro J822 hJ822; step_jnz
                    · step_let1; apply wp_udiv; · exact htot_ne
                      rintro _ h_; subst h_
                      refine wp_join_state_pure (ts := [i64]) (fun x => (x, ()))
                        (fun _ => True) ?_ ?_
                      · intro J1825 lim1 _; try simp only [Blocks.get]
                        apply viv_tier_step hTier hcfg hinv5 hm5 1#64 lim1
                        intro r1 ext6 s6 m6 hinv6 hr1_ok hu1 hm6
                        step_jump; exact hJ822 (r1, lim1, ext6, s6) m6 ⟨hinv6, hr1_ok, hu1, hm6⟩
                      · intro J1825 hJ1825; exact viv_sat_add_wp wm5 _ (fun r => hJ1825 r trivial)
                    · step_jump; exact hJ822 (1#64, wm5, ext5, s5) m5
                        ⟨hinv5, Or.inl rfl, (fun h => by cases h), hm5⟩
                · intro J719 hJ719; step_jnz
                  · step_jnz
                    · step_lets; have hm4F := fullM6HdrMem_focus_full hm4
                      apply wp_load_of (a := Arg.var _) (load_full_tier1 hm4F); step_lets
                      apply wp_load_of (a := Arg.var _) (load_full_tier2 hm4F)
                      step_jnz <;> (step_jump; exact hJ719 (_, _) trivial)
                    · step_jump; exact hJ719 (b5, b6) trivial
                  · step_jump; exact hJ719 (b5, b6) trivial
              · intro J617 hJ617; step_jnz <;> (step_jump; exact hJ617 _ trivial)
            · intro J516 hJ516; step_jnz <;> (step_jump; exact hJ516 _ trivial)
        · intro J408 hJ408; step_lets; have hm3F := fullM6HdrMem_focus_full hm3
          apply wp_load_of (a := Arg.var _) (load_full_num_redundant hm3F)
          step_jnz <;> (step_jump; exact hJ408 _ trivial)
      · intro J307 hJ307; step_lets; have hm3F := fullM6HdrMem_focus_full hm3
        apply wp_load_of (a := Arg.var _) (load_full_num_redundant hm3F)
        step_jnz <;> (step_jump; exact hJ307 _ trivial)
    · intro J206 hJ206; step_lets; have hm3F := fullM6HdrMem_focus_full hm3
      apply wp_load_of (a := Arg.var _) (load_full_num_redundant hm3F)
      step_jnz <;> (step_jump; exact hJ206 _ trivial)
  · intro J105 hJ105
    apply viv_w2a_step hDelaying hcfg hinv2.1 hinv2.2.1 hinv2.2.2.1 hm2b (Arg.imm 3#64, ())
    intro rd ext3 s3 m3 hext3 hpres3 hsp3 hcore3 _ hm3
    have hinv3 : VivHdrInv c F0 ext s ext3 s3 :=
      ⟨hext3, hpres3, hsp3, by rw [hcore3]; exact hinv2.2.2.2.1,
       by rw [hcore3]; exact hinv2.2.2.2.2.1, by rw [hcore3]; exact hinv2.2.2.2.2.2⟩
    step_jnz
    · step_jump; exact hJ105 (0#64, ext3, s3) m3 ⟨hinv3, hm3⟩
    · step_jump; exact hJ105 (3#64, ext3, s3) m3 ⟨hinv3, hm3⟩

public section

theorem full_vivify_tier_m6_hdr_wp (Γ : Env)
    (hCollect : Γ.Has "full_viv_collect_fid" Spec.vivCollectFidSpec)
    (hSort : Γ.Has "full_viv_sort_fid" Spec.fullVivSortFidSpec)
    (hClear : Γ.Has "full_viv_clear_tier_m6" Spec.fullVivClearTierM6Spec)
    (hClause : Γ.Has "full_viv_clause_m6" Spec.vivClauseM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, Spec.vivifyTierM6HdrSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_body a m Q X := by
  intro ⟨h, mode, budget, tick_lim, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩
  exact full_vivify_tier_m6_hdr_wp_aux Γ hCollect hSort hClear hClause hBt hProp hGetWm hNext
    c F0 ext s mode budget tick_lim m Q X R hcfg hext hsp hm hQ

theorem full_vivify_m6_hdr_wp (Γ : Env)
    (hTier : Γ.Has "full_vivify_tier_m6_hdr" Spec.vivifyTierM6HdrSpec)
    (hGetTier1 : Γ.Has "m6_hdr_get_tier1" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hGetTier2 : Γ.Has "m6_hdr_get_tier2" (m6HdrW2aSpec [Ty.bool] [i64]))
    (hGetWm : Γ.Has "m6_hdr_get_watermark" Tiers.Spec.m6HdrGetWatermarkSpec)
    (hSync : Γ.Has "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] []))
    (hBump : Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hReduce : Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hDelaying : Γ.Has "m6_hdr_delaying" (m6HdrW2aSpec [i64] [Ty.bool]))
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec) :
    ∀ a m Q X, Spec.vivifyM6HdrSpec a m Q X →
      Func.wp Γ full_vivify_m6_hdr_body a m Q X := by
  intro ⟨h, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩
  exact full_vivify_m6_hdr_wp_aux Γ hTier hGetTier1 hGetTier2 hGetWm hSync hBump hReduce hDelaying
    hBt c F0 ext s m Q X R hcfg hext hsp hm hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
