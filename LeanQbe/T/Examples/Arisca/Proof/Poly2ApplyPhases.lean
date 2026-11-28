/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplyBase
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_apply` Loop 1 & Loop 3 WP Phases (`Arisca.Proof.Poly2ApplyPhases`)

Sharded WP phase proofs for `ar_apply`:
- `apply_bx_loop_wp` (Loop 1: `i < n` Bloom-filtered scan populating `bx`, `nb`, `slB`)
- `apply_vq_loop_wp` (Loop 3: `r < nR` partner-conflict table populating `vq_off`, `vq_skip`, `vq`)
plus pure word-budget invariants supporting Loop 4 (`Poly2`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

@[expose] public section

/-! ## 1. Loop 3 Vanishing-Partner Invariant & AST Extractors -/

/-- Per-row vanishing / partner-literal invariant built by Loop 3 of `ar_apply`. -/
def VqRowOk (nNets sym : Nat) (partnerArr curRp curRm : List (BitVec 32))
    (vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (Valid : (Nat → Bool) → Prop) (r q : Nat) : Prop :=
  (vqSkip.getD r 0#8 ≠ 0#8 →
    ∀ σ, Valid σ → monoValL σ (symListAt curRp (curRm.getD r 0#32).toNat) = false) ∧
  (vqSkip.getD r 0#8 = 0#8 →
    (vqOff.getD r 0#32).toNat ≤ (vqOff.getD (r + 1) 0#32).toNat ∧
    (vqOff.getD (r + 1) 0#32).toNat ≤ q ∧
    ∀ idx, (vqOff.getD r 0#32).toNat ≤ idx → idx < (vqOff.getD (r + 1) 0#32).toNat →
      ∃ w ∈ symListAt curRp (curRm.getD r 0#32).toNat,
        w % 2 = 0 ∧ w / 2 < nNets ∧
        partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
        (vq.getD idx 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
        (vq.getD idx 0#32).toNat ≠ sym)

noncomputable def applyLoop1Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bit : Val i64)
    (tm0 pool0 ts0 bx : Val i64) : Expr Val Cont [.bool] :=
  match ar_apply_body Val Cont (cx, sym, ()) with
  | @Expr.let_ _ _ _ [.bits 64] _ e0 => match e0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ e1 => match e1 curRm with
      | @Expr.let_ _ _ _ [.bits 64] _ e2 => match e2 (0#64, ()) with
        | @Expr.load _ _ _ (.bits 64) _ e3 => match e3 curRl with
          | @Expr.let_ _ _ _ [.bits 64] _ e4 => match e4 (0#64, ()) with
            | @Expr.load _ _ _ (.bits 64) _ e5 => match e5 curRh with
              | @Expr.let_ _ _ _ [.bits 64] _ e6 => match e6 (0#64, ()) with
                | @Expr.load _ _ _ (.bits 64) _ e7 => match e7 curRp with
                  | @Expr.let_ _ _ _ [.bits 64] _ e8 => match e8 (0#64, ()) with
                    | @Expr.load _ _ _ (.bits 32) _ e9 => match e9 nR with
                      | @Expr.let_ _ _ _ [.bits 64] _ e10 => match e10 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 32) _ e11 => match e11 n with
                          | @Expr.call _ _ _ _ _ [.bits 64] _ e12 => match e12 (bit, ()) with
                            | @Expr.let_ _ _ _ [.bits 64] _ e13 => match e13 (0#64, ()) with
                              | @Expr.let_ _ _ _ [.bits 64] _ e14 => match e14 (0#64, ()) with
                                | @Expr.load _ _ _ (.bits 32) _ e15 => match e15 0#32 with
                                  | @Expr.let_ _ _ _ [.bits 64] _ e16 => match e16 (0#64, ()) with
                                    | @Expr.let_ _ _ _ [.bits 64] _ e17 => match e17 (0#64, ()) with
                                      | @Expr.let_ _ _ _ [.bits 64] _ e18 =>
                                        (match e18 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ e19 => match e19 tm0 with
      | @Expr.let_ _ _ _ [.bits 64] _ e20 => match e20 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ e21 => match e21 (0#64, ()) with
          | @Expr.load _ _ _ (.bits 32) _ e22 => match e22 0#32 with
            | @Expr.let_ _ _ _ [.bits 64] _ e23 => match e23 (0#64, ()) with
              | @Expr.let_ _ _ _ [.bits 64] _ e24 => match e24 (0#64, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ e25 => match e25 (0#64, ()) with
                  | @Expr.load _ _ _ (.bits 64) _ e26 => match e26 pool0 with
                    | @Expr.let_ _ _ _ [.bits 64] _ e27 => match e27 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ e28 => match e28 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 32) _ e29 => match e29 0#32 with
                          | @Expr.let_ _ _ _ [.bits 64] _ e30 => match e30 (0#64, ()) with
                            | @Expr.let_ _ _ _ [.bits 64] _ e31 => match e31 (0#64, ()) with
                              | @Expr.let_ _ _ _ [.bits 64] _ e32 => match e32 (0#64, ()) with
                                | @Expr.load _ _ _ (.bits 64) _ e33 => match e33 ts0 with
                                  | @Expr.let_ _ _ _ [.bits 64] _ e34 => match e34 (0#64, ()) with
                                    | @Expr.load _ _ _ (.bits 64) _ e35 => e35 bx
                                    | _ => .ret (Arg.imm false, ())
                                  | _ => .ret (Arg.imm false, ())
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ()))
                                      | _ => .ret (Arg.imm false, ())
                                    | _ => .ret (Arg.imm false, ())
                                  | _ => .ret (Arg.imm false, ())
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyLoop1ExitExpr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB : Val i64) : Expr Val Cont [.bool] :=
  match applyLoop1Expr cx sym curRm curRl curRh curRp nR n 0#64 0#64 0#64 0#64 bx with
  | @Expr.group _ _ _ [[.bits 32, .bits 64, .bits 32]] bs _ =>
    match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (nb, slB, 0#32, ()) with
      | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
        | .jnz _ _ f => f
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyLoop2Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB : Val i64) : Expr Val Cont [.bool] :=
  match applyLoop1ExitExpr cx sym curRm curRl curRh curRp nR n bx nb slB with
  | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
    | .jnz _ _ f => f
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyAfterLoop2Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR : Val i64) : Expr Val Cont [.bool] :=
  match applyLoop2Expr cx sym curRm curRl curRh curRp nR n bx nb slB with
  | @Expr.group _ _ _ [[.bits 64, .bits 32]] bs _ =>
    match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (slR, 0#32, ()) with
      | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
        | .jnz _ _ f => f
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyLoop3Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR : Val i64) : Expr Val Cont [.bool] :=
  match applyAfterLoop2Expr cx sym curRm curRl curRh curRp nR n bx nb slB slR with
  | @Expr.let_ _ _ _ [.bits 64] _ l0 => match l0 (0#64, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ l1 => match l1 (0#64, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ l2 => match l2 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ l3 => match l3 (0#64, ()) with
          | @Expr.load _ _ _ (.bits 32) _ l4 => match l4 0#32 with
            | @Expr.let_ _ _ _ [.bits 64] _ l5 => match l5 (0#64, ()) with
              | @Expr.let_ _ _ _ [.bool] _ l6 => match l6 (false, ()) with
                | .jnz _ _ f1 => match f1 with
                  | @Expr.let_ _ _ _ [.bits 64] _ l7 => match l7 (0#64, ()) with
                    | @Expr.let_ _ _ _ [.bits 64] _ l8 => match l8 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ l9 => match l9 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ l10 => match l10 (0#64, ()) with
                          | @Expr.let_ _ _ _ [.bits 64] _ l11 => match l11 (0#64, ()) with
                            | @Expr.load _ _ _ (.bits 32) _ l12 => match l12 0#32 with
                              | @Expr.let_ _ _ _ [.bits 64] _ l13 => match l13 (0#64, ()) with
                                | @Expr.let_ _ _ _ [.bool] _ l14 => match l14 (false, ()) with
                                  | .jnz _ _ f2 => match f2 with
                                    | @Expr.let_ _ _ _ [.bits 64] _ l15 => match l15 (0#64, ()) with
                                      | @Expr.let_ _ _ _ [.bits 64] _ l16 =>
                                        (match l16 (0#64, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ l17 => match l17 (0#64, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ l18 => match l18 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ l19 => match l19 (0#64, ()) with
          | @Expr.let_ _ _ _ [.bits 64] _ l20 => match l20 (0#64, ()) with
            | @Expr.load _ _ _ (.bits 64) _ l21 => match l21 0#64 with
              | @Expr.let_ _ _ _ [.bool] _ l22 => match l22 (false, ()) with
                | .jnz _ _ f3 => match f3 with
                  | @Expr.group _ _ _ [[]] bs _ =>
                    match bs (fun _ _ => False, ()) with
                    | .cons b _ => match b () with
                      | @Expr.let_ _ _ _ [.bits 64] _ c0 => match c0 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ c1 => match c1 (0#64, ()) with
                          | @Expr.load _ _ _ (.bits 32) _ c2 => match c2 0#32 with
                            | @Expr.let_ _ _ _ [.bits 64] _ c3 => match c3 (0#64, ()) with
                              | @Expr.let_ _ _ _ [.bool] _ c4 => match c4 (false, ()) with
                                | .jnz _ _ f4 => f4
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ()))
                                      | _ => .ret (Arg.imm false, ())
                                    | _ => .ret (Arg.imm false, ())
                                  | _ => .ret (Arg.imm false, ())
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyAfterLoop3Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR : Val i64) : Expr Val Cont [.bool] :=
  match applyLoop3Expr cx sym curRm curRl curRh curRp nR n bx nb slB slR with
  | @Expr.group _ _ _ [[.bits 32, .bits 64]] bs _ =>
    match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (nR, 0#64, ()) with
      | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
        | .jnz _ _ f => match f with
          | @Expr.let_ _ _ _ [.bits 64] _ s0 => match s0 (0#64, ()) with
            | @Expr.load _ _ _ (.bits 64) _ s1 => match s1 0#64 with
              | @Expr.let_ _ _ _ [.bits 64] _ s2 => match s2 (0#64, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ s3 => match s3 (0#64, ()) with
                  | @Expr.let_ _ _ _ [.bits 64] _ s4 => match s4 (0#64, ()) with
                    | @Expr.let_ _ _ _ [.bits 32] _ s5 => match s5 (0#32, ()) with
                      | .store _ _ k => k
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

noncomputable def applyLoop4Expr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR pool0 tm0 tl0 th0 ptop : Val i64) : Expr Val Cont [.bool] :=
  match applyAfterLoop3Expr cx sym curRm curRl curRh curRp nR n bx nb slB slR with
  | @Expr.let_ _ _ _ [.bits 64] _ l0 => match l0 (0#64, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ l1 => match l1 (0#64, ()) with
      | @Expr.load _ _ _ (.bits 32) _ l2 => match l2 0#32 with
        | @Expr.let_ _ _ _ [.bits 64] _ l3 => match l3 (0#64, ()) with
          | @Expr.let_ _ _ _ [.bits 64] _ l4 => match l4 (0#64, ()) with
            | @Expr.let_ _ _ _ [.bits 64] _ l5 => match l5 (0#64, ()) with
              | @Expr.load _ _ _ (.bits 64) _ l6 => match l6 pool0 with
                | @Expr.let_ _ _ _ [.bits 64] _ l7 => match l7 (0#64, ()) with
                  | @Expr.let_ _ _ _ [.bits 64] _ l8 => match l8 (0#64, ()) with
                    | @Expr.load _ _ _ (.bits 32) _ l9 => match l9 0#32 with
                      | @Expr.let_ _ _ _ [.bits 64] _ l10 => match l10 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ l11 => match l11 (0#64, ()) with
                          | @Expr.let_ _ _ _ [.bits 64] _ l12 => match l12 (0#64, ()) with
                            | @Expr.load _ _ _ (.bits 64) _ l13 => match l13 tm0 with
                              | @Expr.let_ _ _ _ [.bits 64] _ l14 => match l14 (0#64, ()) with
                                | @Expr.let_ _ _ _ [.bits 64] _ l15 => match l15 (0#64, ()) with
                                  | @Expr.load _ _ _ (.bits 32) _ l16 => match l16 0#32 with
                                    | @Expr.let_ _ _ _ [.bits 64] _ l17 => match l17 (0#64, ()) with
                                      | @Expr.let_ _ _ _ [.bits 64] _ l18 =>
                                        (match l18 (0#64, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ l19 => match l19 (0#64, ()) with
      | @Expr.load _ _ _ (.bits 64) _ l20 => match l20 tl0 with
        | @Expr.let_ _ _ _ [.bits 64] _ l21 => match l21 (0#64, ()) with
          | @Expr.let_ _ _ _ [.bits 64] _ l22 => match l22 (0#64, ()) with
            | @Expr.load _ _ _ (.bits 32) _ l23 => match l23 0#32 with
              | @Expr.let_ _ _ _ [.bits 64] _ l24 => match l24 (0#64, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ l25 => match l25 (0#64, ()) with
                  | @Expr.let_ _ _ _ [.bits 64] _ l26 => match l26 (0#64, ()) with
                    | @Expr.load _ _ _ (.bits 64) _ l27 => match l27 th0 with
                      | @Expr.let_ _ _ _ [.bits 64] _ l28 => match l28 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 64) _ l29 => l29 ptop
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ()))
                                      | _ => .ret (Arg.imm false, ())
                                    | _ => .ret (Arg.imm false, ())
                                  | _ => .ret (Arg.imm false, ())
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

/-- Pre-finalization Loop 3 invariant for row `idx < rMax` using `q` for `idx + 1 = rMax`. -/
def VqRowPreOk (nNets sym : Nat) (partnerArr curRp curRm vqOff vq : List (BitVec 32))
    (vqSkip : List (BitVec 8)) (Valid : (Nat → Bool) → Prop) (rMax idx q : Nat) : Prop :=
  (vqSkip.getD idx 0#8 ≠ 0#8 →
    ∀ σ, Valid σ → monoValL σ (symListAt curRp (curRm.getD idx 0#32).toNat) = false) ∧
  (vqSkip.getD idx 0#8 = 0#8 →
    let hi := if idx + 1 = rMax then q else (vqOff.getD (idx + 1) 0#32).toNat
    (vqOff.getD idx 0#32).toNat ≤ hi ∧ hi ≤ q ∧
    ∀ p, (vqOff.getD idx 0#32).toNat ≤ p → p < hi →
      ∃ w ∈ symListAt curRp (curRm.getD idx 0#32).toNat,
        w % 2 = 0 ∧ w / 2 < nNets ∧
        partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
        (vq.getD p 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
        (vq.getD p 0#32).toNat ≠ sym)

end

public section

/-! ## 2. Pure Helpers for `bx` / `vq` / `need` Bounds -/

theorem bx_strictInc_snoc {bx : List (BitVec 32)} {nb i : Nat} {i32v : BitVec 32}
    (hinc : strictIncBelow bx nb i) (hnblt : nb < bx.length) (hi : i32v.toNat = i) :
    strictIncBelow (bx.set nb i32v) (nb + 1) (i + 1) := by
  constructor
  · intro p hp
    rw [getD_set_eq bx 0#32 i32v hnblt]
    by_cases hpn : p = nb
    · subst hpn; simp [hi]
    · have := hinc.1 p (by omega); simp only [hpn, ↓reduceIte]; omega
  · intro p hp
    rw [getD_set_eq bx 0#32 i32v hnblt, getD_set_eq bx 0#32 i32v hnblt]
    by_cases hp1 : p + 1 = nb
    · have hpn : p ≠ nb := by omega
      simp only [hpn, hp1, ↓reduceIte, hi]
      exact hinc.1 p (by omega)
    · have hpn : p ≠ nb := by omega
      simp only [hpn, hp1, ↓reduceIte]
      exact hinc.2 p (by omega)

theorem bxSymLenSum_set_nb {pool tm bx : List (BitVec 32)} {nb : Nat} {v : BitVec 32}
    (hnb : nb < bx.length) :
    bxSymLenSum pool tm (bx.set nb v) nb = bxSymLenSum pool tm bx nb := by
  apply bxSymLenSum_congr
  · intro b hb
    rw [getD_set_eq bx 0#32 v hnb, ite_eq_right (by omega)]
  · intro b hb
    rw [getD_set_eq bx 0#32 v hnb, ite_eq_right (by omega)]
  · intro b hb
    rw [getD_set_eq bx 0#32 v hnb, ite_eq_right (by omega)]

theorem apply_need_lt_u32_mul {nb nR qcap : Nat}
    (hnb_pos : 0 < nb) (_hnb_lt : nb < 2 ^ 30) (hnprod : nb * nR ≤ qcap)
    (hqcap32 : qcap + 16 < 2 ^ 32) :
    nR ≤ qcap ∧ nR < 2 ^ 32 := by
  have h1 : nR ≤ nb * nR := Nat.le_mul_of_pos_left nR hnb_pos
  exact ⟨le_trans h1 hnprod, by omega⟩

theorem apply_step_budget_le {pool tm rp rm bx : List (BitVec 32)} {nR b r : Nat} :
    let mOff := (tm.getD (bx.getD b 0#32).toNat 0#32).toNat
    let mLen := (pool.getD mOff 0#32).toNat
    let mrLen := (rp.getD (rm.getD r 0#32).toNat 0#32).toNat
    (b * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx b +
      r * mLen + rSymLenSum rp rm r) + (mLen + mrLen) ≤
      b * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx b +
        (r + 1) * mLen + rSymLenSum rp rm (r + 1) := by
  dsimp only
  rw [rSymLenSum_succ, Nat.add_mul, Nat.one_mul]
  omega

theorem apply_row_budget_le {pool tm rp rm bx : List (BitVec 32)} {nR b : Nat} :
    let mOff := (tm.getD (bx.getD b 0#32).toNat 0#32).toNat
    let mLen := (pool.getD mOff 0#32).toNat
    b * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx b +
      nR * mLen + rSymLenSum rp rm nR =
      (b + 1) * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx (b + 1) := by
  rw [bxSymLenSum_succ, Nat.mul_add, Nat.succ_mul]
  omega

theorem apply_outer_budget_le {pool tm rp rm bx : List (BitVec 32)} {nb nR b : Nat}
    (hb : b ≤ nb) :
    b * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx b ≤
      nR * bxSymLenSum pool tm bx nb + nb * rSymLenSum rp rm nR := by
  have h1 : bxSymLenSum pool tm bx b ≤ bxSymLenSum pool tm bx nb := by
    have hdiff : ∀ d, bxSymLenSum pool tm bx b ≤ bxSymLenSum pool tm bx (b + d) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← Nat.add_assoc, bxSymLenSum_succ]; exact le_trans ih (Nat.le_add_right _ _)
    have he := hdiff (nb - b)
    rwa [show b + (nb - b) = nb by omega] at he
  have h2 : b * rSymLenSum rp rm nR ≤ nb * rSymLenSum rp rm nR := Nat.mul_le_mul_right _ hb
  have h3 : nR * bxSymLenSum pool tm bx b ≤ nR * bxSymLenSum pool tm bx nb :=
    Nat.mul_le_mul_left _ h1
  omega

theorem vqRowPreOk_to_ok {nNets sym : Nat} {partnerArr curRp curRm vqOff vq : List (BitVec 32)}
    {vqSkip : List (BitVec 8)} {Valid : (Nat → Bool) → Prop} {nR q idx : Nat}
    (hpre : VqRowPreOk nNets sym partnerArr curRp curRm vqOff vq vqSkip Valid nR idx q)
    (hidx : idx < nR) (hnr : nR < vqOff.length) (hq32 : q < 2 ^ 32) :
    VqRowOk nNets sym partnerArr curRp curRm (vqOff.set nR (BitVec.ofNat 32 q)) vq vqSkip
      Valid idx q := by
  refine ⟨hpre.1, fun hsk => ?_⟩
  have h := hpre.2 hsk
  rw [getD_set_eq vqOff 0#32 (BitVec.ofNat 32 q) hnr,
    getD_set_eq vqOff 0#32 (BitVec.ofNat 32 q) hnr,
    ite_eq_right (by omega)]
  by_cases hlast : idx + 1 = nR
  · simp only [hlast, ↓reduceIte] at h ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
    exact ⟨h.1, le_refl _, h.2.2⟩
  · simp only [hlast, ↓reduceIte] at h ⊢
    exact h

theorem wp_store_arr8_abs {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i8} {a : Arg Val i64} {val : BitVec 8} {k : Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 8)} {idx : BitVec 32} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + BitVec.setWidth 64 idx)
    (hi : idx.toNat < xs.length) (hm : (array (t := i8) base xs ⋆ R) m)
    (hk : ∀ m', (array (t := i8) base (xs.set idx.toNat val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 ((i8 : Ty).bytes * idx.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Ty.bytes, Ty.size]
  exact head_wp_store hv ha' (store_array (t := i8) val (by decide) hi hm) hk

/-! ## 3. Loop 1: `apply_bx_loop_wp` (`i < n`) -/

theorem apply_bx_loop_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 _tl0 _th0 ts1 _tl1 _th1 : List (BitVec 64)}
    {pool0 pool1 : List (BitVec 32)} {bx : List (BitVec 32)}
    {restBx R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (_hpc : s.pc.toNat < 2) (_htc : s.tc.toNat < 2)
    (htn : s.tn.toNat ≤ s.tcap.toNat) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hptop : s.ptop.toNat ≤ s.pcap.toNat) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (htm_len : s.tcap.toNat ≤ (if s.tc.toNat = 0 then tm0 else tm1).length)
    (hts_len : s.tcap.toNat ≤ (if s.tc.toNat = 0 then ts0 else ts1).length)
    (hp_len : s.pcap.toNat ≤ (if s.pc.toNat = 0 then pool0 else pool1).length)
    (hbx_t : s.tcap.toNat ≤ bx.length)
    (hSlices : ∀ i < s.tn.toNat,
      MonoSliceOk (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat s.ptop.toNat ∧
      ((if s.pc.toNat = 0 then pool0 else pool1).getD
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (_hSorted : ∀ i < s.tn.toNat,
      MonoSorted (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat)
    (hTot : monoTotalWords (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) s.tn.toNat ≤ s.ptop.toNat)
    (hm0 : (arCtxMem cx s ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
      array (t := i32) s.bx bx ⋆ restBx ⋆ R) m0)
    (hZero : ∀ (bxL : List (BitVec 32)) (mL : Mem 64),
      bxL.length = bx.length →
      (arCtxMem cx s ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        array (t := i32) s.bx bxL ⋆ restBx ⋆ R) mL →
      Q (true, ⟨⟩) mL)
    (hDone : ∀ (nb : BitVec 32) (slB : BitVec 64) (bxL : List (BitVec 32)) (mL : Mem 64),
      bxL.length = bx.length → 0 < nb.toNat → nb.toNat ≤ s.tn.toNat →
      strictIncBelow bxL nb.toNat s.tn.toNat →
      slB.toNat = bxSymLenSum (if s.pc.toNat = 0 then pool0 else pool1)
        (if s.tc.toNat = 0 then tm0 else tm1) bxL nb.toNat →
      (∀ b < nb.toNat, sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD (bxL.getD b 0#32).toNat 0#32).toNat) →
      (arCtxMem cx s ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        array (t := i32) s.bx bxL ⋆ restBx ⋆ R) mL →
      wp Γ Q X (applyLoop2Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
        s.bx nb slB) mL) :
    wp Γ Q X (applyLoop1Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
      (sigBit sym) (s.tm.getD s.tc.toNat 0#64) (s.pool.getD s.pc.toNat 0#64)
      (s.ts.getD s.tc.toNat 0#64) s.bx) m0 := by
  dsimp only [applyLoop1Expr]
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let R1 := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ restBx ⋆ R
  refine wp_loop_group (fun rem ⟨nb, slB, i, ⟨⟩⟩ mL =>
      ∃ bxL : List (BitVec 32),
        bxL.length = bx.length ∧ nb.toNat ≤ i.toNat ∧ i.toNat ≤ s.tn.toNat ∧
        rem = s.tn.toNat - i.toNat ∧ strictIncBelow bxL nb.toNat i.toNat ∧
        slB.toNat = bxSymLenSum srcPool srcTm bxL nb.toNat ∧
        (∀ b < nb.toNat,
          sym.toNat ∈ symListAt srcPool (srcTm.getD (bxL.getD b 0#32).toNat 0#32).toNat) ∧
        (array (t := i32) s.bx bxL ⋆ R1) mL)
    ?_ ?_
  · rintro J rem ⟨nb, slB, i, ⟨⟩⟩ mL hrec ⟨bxL, hbx_len, hnb_i, hi_tn, hrem, hinc, hslB, hmem, hmL⟩
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < s.tn.toNat := hc; clear hc
      have hi_ts : i.toNat < srcTs.length := by dsimp only [srcTs]; omega
      have hi_tm : i.toNat < srcTm.length := by dsimp only [srcTm]; omega
      have hm_ts : (array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          (array (t := i32) s.bx bxL ⋆ arCtxMem cx s ⋆
           array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆ restBx ⋆ R)) mL :=
        sep_cast hmL (by dsimp only [R1]; ac_rfl)
      refine wp_join_group (fun (v : Tup Val [i32, i64]) mK =>
          ∃ bxK : List (BitVec 32),
            bxK.length = bx.length ∧ v.1.toNat ≤ i.toNat + 1 ∧
            strictIncBelow bxK v.1.toNat (i.toNat + 1) ∧
            v.2.1.toNat = bxSymLenSum srcPool srcTm bxK v.1.toNat ∧
            (∀ b < v.1.toNat,
              sym.toNat ∈ symListAt srcPool (srcTm.getD (bxK.getD b 0#32).toNat 0#32).toNat) ∧
            (array (t := i32) s.bx bxK ⋆ R1) mK)
        ?_ ?_
      · rintro Jk ⟨nb1, slB1, ⟨⟩⟩ mK ⟨bxK, hbxK_len, hnb1_le, hincK, hslBK, hmemK, hmK⟩
        c0_hsteps_nogrp
        have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
        exact hrec (s.tn.toNat - (i + 1#32).toNat) (nb1, slB1, i + 1#32, ⟨⟩) mK (by omega)
          ⟨bxK, hbxK_len, by rw [hip1]; exact hnb1_le, by rw [hip1]; omega, rfl,
            by rw [hip1]; exact hincK, hslBK, hmemK, hmK⟩
      · intro JK hJK
        c0_hsteps_nogrp
        · have hts_nz : (srcTs[i.toNat] &&& sigBit sym) ≠ 0#64 := by simpa using hc
          clear hc
          let mOffBv := srcTm[(BitVec.setWidth 64 i).toNat]'(by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide))]
            exact hi_tm)
          have hmOff_eq : mOffBv.toNat = (srcTm.getD i.toNat 0#32).toNat := by
            dsimp only [mOffBv]
            have hisw : (BitVec.setWidth 64 i).toNat = i.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide))]
            simp only [hisw]
            rw [getD_eq_getElem srcTm 0#32 hi_tm]
          have hmSl := (hSlices i.toNat hi_lt).1
          have hm32 := (hSlices i.toNat hi_lt).2
          rw [← hmOff_eq] at hmSl hm32
          have hmSl_len : MonoSliceOk srcPool mOffBv.toNat srcPool.length :=
            ⟨Nat.lt_of_lt_of_le hmSl.1 (by dsimp only [srcPool]; omega),
             le_trans hmSl.2 (by dsimp only [srcPool]; omega)⟩
          refine wp_join_group (fun (v : Tup Val [i32, i64]) mK =>
              ∃ bxK : List (BitVec 32),
                bxK.length = bx.length ∧ v.1.toNat ≤ i.toNat + 1 ∧
                strictIncBelow bxK v.1.toNat (i.toNat + 1) ∧
                v.2.1.toNat = bxSymLenSum srcPool srcTm bxK v.1.toNat ∧
                (∀ b < v.1.toNat,
                  sym.toNat ∈ symListAt srcPool (srcTm.getD (bxK.getD b 0#32).toNat 0#32).toNat) ∧
                (array (t := i32) s.bx bxK ⋆ R1) mK)
            ?_ ?_
          · rintro Jk2 ⟨nb2, slB2, ⟨⟩⟩ mK2 hK2
            c0_hsteps_nogrp
            exact hJK (nb2, slB2, ⟨⟩) mK2 hK2
          · intro JK2 hJK2
            let Rhas := array (t := i32) s.bx bxL ⋆ arCtxMem cx s ⋆
              array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
              array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ restBx ⋆ R
            have hm_has : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆ Rhas) mL := by
              dsimp only [Rhas]; exact sep_cast hmL (by dsimp only [R1]; ac_rfl)
            refine wp_call_of_spec _ _ (hMhas
              ⟨s.pool.getD s.pc.toNat 0#64 + BitVec.setWidth 64 mOffBv * 4#64, 1#32, sym, ⟨⟩⟩ mL _ X
              ⟨s.pool.getD s.pc.toNat 0#64, srcPool, mOffBv.toNat, Rhas,
                (by congr 1; apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                      Nat.mul_comm 4 mOffBv.toNat]),
                hmSl_len, hm32, (by decide),
                (by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega),
                hm_has, fun ok hok _ => ?_⟩)
            dsimp only
            c0_hsplit_nobound
            · have hok_t : ok = true := hc; clear hc
              obtain ⟨idx, hidx1, hidx_le, hidx_eq⟩ := hok hok_t
              have hsym_mem : sym.toNat ∈ symListAt srcPool mOffBv.toNat := by
                rw [mem_symListAt_iff]
                exact ⟨idx, hidx1, hidx_le, congrArg BitVec.toNat hidx_eq⟩
              have hnb_bx : nb.toNat < bxL.length := by omega
              c0_hsteps_nogrp
              have hnb_sw : (BitVec.setWidth 64 nb : BitVec 64).toNat = nb.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans nb.isLt (by decide))]
              let bxL' := bxL.set nb.toNat i
              have hmS : (array (t := i32) s.bx bxL' ⋆ R1) m := by
                dsimp only [bxL']; rw [← hnb_sw]; exact hm
              have hmS_pool : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                  (array (t := i32) s.bx bxL' ⋆ arCtxMem cx s ⋆
                   array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
                   array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ restBx ⋆ R)) m :=
                sep_cast hmS (by dsimp only [R1]; ac_rfl)
              have hsrc_lt : mOffBv.toNat < srcPool.length := hmSl_len.1
              refine wp_load_arr32_0 (base := s.pool.getD s.pc.toNat 0#64) (xs := srcPool)
                (off := mOffBv.toNat) ?_ hsrc_lt hmS_pool ?_
              · simp only [Arg.val, mOffBv]; congr 1
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  Nat.mul_comm 4]
              c0_hsteps_nogrp
              have hinc' : strictIncBelow bxL' (nb.toNat + 1) (i.toNat + 1) :=
                bx_strictInc_snoc hinc hnb_bx rfl
              have hnbp1 : (nb + 1#32).toNat = nb.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : nb.toNat + 1 < 2 ^ 32)]
              have hsl_eq : bxSymLenSum srcPool srcTm bxL' (nb.toNat + 1) =
                  slB.toNat + (srcPool[mOffBv.toNat]'hsrc_lt).toNat := by
                rw [bxSymLenSum_succ, bxSymLenSum_set_nb hnb_bx, ← hslB]
                congr 1
                rw [getD_set_eq bxL 0#32 i hnb_bx, ite_eq_left rfl, ← hmOff_eq,
                  getD_eq_getElem srcPool 0#32 hsrc_lt]
              have hbd_sum : bxSymLenSum srcPool srcTm bxL' (nb.toNat + 1) + (nb.toNat + 1) ≤
                  monoTotalWords srcPool srcTm s.tn.toNat :=
                bxSymLenSum_add_nb_le_monoTotalWords srcPool srcTm bxL'
                  ⟨fun p hp => Nat.lt_of_lt_of_le (hinc'.1 p hp) (by omega), hinc'.2⟩
              have hslB' : (slB + BitVec.setWidth 64 (srcPool[mOffBv.toNat]'hsrc_lt)).toNat =
                  bxSymLenSum srcPool srcTm bxL' (nb.toNat + 1) := by
                have hlt64 : slB.toNat + (srcPool[mOffBv.toNat]'hsrc_lt).toNat < 2 ^ 64 := by
                  dsimp only [srcPool, srcTm] at hbd_sum hsl_eq; omega
                rw [BitVec.toNat_add, BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (by omega : (srcPool[mOffBv.toNat]'hsrc_lt).toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt hlt64, hsl_eq]
              refine hJK2 (nb + 1#32, _, ⟨⟩) m ⟨bxL', by simp [bxL', hbx_len],
                by dsimp only; rw [hnbp1]; omega, by dsimp only; rw [hnbp1]; exact hinc',
                by dsimp only; rw [hnbp1]; exact hslB', ?_, hmS⟩
              intro b hb
              dsimp only at hb
              rw [hnbp1] at hb
              by_cases hbn : b = nb.toNat
              · subst hbn
                rw [getD_set_eq bxL 0#32 i hnb_bx, ite_eq_left rfl, ← hmOff_eq]
                exact hsym_mem
              · rw [getD_set_eq bxL 0#32 i hnb_bx, ite_eq_right hbn]
                exact hmem b (by omega)
            · c0_hsteps_nogrp
              exact hJK2 (nb, slB, ⟨⟩) mL ⟨bxL, hbx_len, by dsimp only; omega,
                ⟨fun p hp => Nat.lt_of_lt_of_le (hinc.1 p (by dsimp only at hp; exact hp))
                  (by omega), hinc.2⟩,
                hslB, fun b hb => hmem b (by dsimp only at hb; exact hb), hmL⟩
        · exact hJK (nb, slB, ⟨⟩) mL ⟨bxL, hbx_len, by dsimp only; omega,
            ⟨fun p hp => Nat.lt_of_lt_of_le (hinc.1 p (by dsimp only at hp; exact hp))
              (by omega), hinc.2⟩,
            hslB, fun b hb => hmem b (by dsimp only at hb; exact hb), hmL⟩
    · exact hZero bxL mL hbx_len
        (sep_cast hmL (by dsimp only [R1, srcPool, srcTm, srcTs]; ac_rfl))
    · have hi_eq : i.toNat = s.tn.toNat := by
        have hnot : ¬ i.toNat < s.tn.toNat := by c0_bv_omega
        omega
      have hnb_pos : 0 < nb.toNat := by
        have hne : nb ≠ 0#32 := hc
        have : nb.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
        omega
      exact hDone nb slB bxL mL hbx_len hnb_pos (by omega) (hi_eq ▸ hinc) hslB hmem
        (sep_cast hmL (by dsimp only [R1, srcPool, srcTm, srcTs]; ac_rfl))
  · intro J hJ
    c0_hsteps_nogrp
    exact hJ s.tn.toNat (0#32, 0#64, 0#32, ⟨⟩) m0
      ⟨bx, rfl, Nat.zero_le _, Nat.zero_le _, by simp,
        ⟨fun _ hp => by simp at hp, fun _ hp => by simp at hp⟩,
        rfl, fun _ hb => by simp at hb, sep_cast hm0 (by dsimp only [R1]; ac_rfl)⟩

/-! ## 4. Loop 2, Compact & Bounds: `apply_slR_loop_wp` -/

theorem apply_slR_loop_wp (Γ : T.Env)
    (hComp : ∀ xs m Q X, arCompactSpec xs m Q X → Γ "ar_compact" [i64] [] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)} {curRp : List (BitVec 32)}
    {partnerArr : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop}
    {nb : BitVec 32} {slB : BitVec 64} {m0 : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (htn : s.tn.toNat ≤ s.tcap.toNat) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hptop : s.ptop.toNat ≤ s.pcap.toNat)
    (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (htm0 : s.tcap.toNat ≤ tm0.length) (htm1 : s.tcap.toNat ≤ tm1.length)
    (hp0 : s.pcap.toNat ≤ pool0.length) (hp1 : s.pcap.toNat ≤ pool1.length)
    (hnb_pos : 0 < nb.toNat) (hnb_tn : nb.toNat ≤ s.tn.toNat)
    (hinc : strictIncBelow bx nb.toNat s.tn.toNat)
    (hslB : slB.toNat = bxSymLenSum (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) bx nb.toNat)
    (hNonEmpty : ∃ σ₀, Valid σ₀)
    (hcurNr_rm : s.cur_nr.toNat ≤ curRm.length)
    (hcurSl : ∀ r < s.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length)
    (hcurTot : monoTotalWords curRp curRm s.cur_nr.toNat ≤ 4000000000)
    (hSlices : ∀ i < s.tn.toNat,
      MonoSliceOk (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat s.ptop.toNat ∧
      ((if s.pc.toNat = 0 then pool0 else pool1).getD
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ i < s.tn.toNat,
      MonoSorted (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat)
    (hSig : SigOk (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat)
    (hTot : monoTotalWords (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) s.tn.toNat ≤ s.ptop.toNat)
    (hbxMem : ∀ b < nb.toNat, sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0 else pool1)
      ((if s.tc.toNat = 0 then tm0 else tm1).getD (bx.getD b 0#32).toNat 0#32).toNat)
    (hm0 : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆
      tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m0)
    (hFail : ∀ (s' : ArCtxState) (tm0' tm1' pool0' pool1' : List (BitVec 32)) (m' : Mem 64),
      s'.pc.toNat < 2 → s'.ptop.toNat ≤ s.pcap.toNat →
      s' = { s with pc := s'.pc, ptop := s'.ptop } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
        qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m' →
      Q (false, ⟨⟩) m')
    (hDone : ∀ (s' : ArCtxState) (tm0' tm1' pool0' pool1' : List (BitVec 32)) (slR : BitVec 64)
        (m' : Mem 64),
      let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
      let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
      s'.pc.toNat < 2 → s'.ptop.toNat ≤ s.pcap.toNat →
      s' = { s with pc := s'.pc, ptop := s'.ptop } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      s.cur_nr.toNat ≤ s.qcap.toNat →
      nb.toNat * s.cur_nr.toNat ≤ s.qcap.toNat →
      (s.tn.toNat - nb.toNat) + nb.toNat * s.cur_nr.toNat ≤ s.tcap.toNat →
      slR.toNat = rSymLenSum curRp curRm s.cur_nr.toNat →
      s'.ptop.toNat + (s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤ s.pcap.toNat →
      slB.toNat = bxSymLenSum dstPool dstTm bx nb.toNat →
      (∀ i < s.tn.toNat,
        MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
        (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ i < s.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) →
      SigOk dstPool dstTm (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat →
      monoTotalWords dstPool dstTm s.tn.toNat ≤ s'.ptop.toNat →
      (∀ b < nb.toNat, sym.toNat ∈ symListAt dstPool
        (dstTm.getD (bx.getD b 0#32).toNat 0#32).toNat) →
      (∀ i < s.tn.toNat,
        symListAt dstPool (dstTm.getD i 0#32).toNat =
          symListAt (if s.pc.toNat = 0 then pool0 else pool1)
            ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
        qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m' →
      wp Γ Q X (applyLoop3Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
        s.bx nb slB slR) m') :
    wp Γ Q X (applyLoop2Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
      s.bx nb slB) m0 := by
  dsimp only [applyLoop2Expr, applyLoop1ExitExpr, applyLoop1Expr]
  refine wp_loop_group (fun rem ⟨slR, r, ⟨⟩⟩ mL =>
      mL = m0 ∧ r.toNat ≤ s.cur_nr.toNat ∧ rem = s.cur_nr.toNat - r.toNat ∧
      slR.toNat = rSymLenSum curRp curRm r.toNat)
    ?_ ?_
  · rintro J rem ⟨slR, r, ⟨⟩⟩ mL hrec ⟨rfl, hr_le, hrem, hslR⟩
    c0_hsteps_nogrp
    · have hr_lt : r.toNat < s.cur_nr.toNat := hc
      have hrm_lt : r.toNat < curRm.length := by omega
      let mrOff := curRm[r.toNat]'hrm_lt
      have hmr_eq : mrOff.toNat = (curRm.getD r.toNat 0#32).toNat := by
        dsimp only [mrOff]; rw [getD_eq_getElem curRm 0#32 hrm_lt]
      have hmr_sl := hcurSl r.toNat hr_lt
      rw [← hmr_eq] at hmr_sl
      have hm_rp : (array (t := i32) s.cur_rp curRp ⋆
          (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
           array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
           array64 s.cur_rh curRh ⋆
           tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
           qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R)) mL :=
        sep_cast hm0 (by ac_rfl)
      refine wp_load_arr32_idx (base := s.cur_rp) (off := 0) (xs := curRp) (i := mrOff)
        (by simp [BitVec.add_zero]; rfl) (by have := hmr_sl.1; omega) hm_rp ?_
      c0_hsteps_nogrp
      have hmono_le : rSymLenSum curRp curRm (r.toNat + 1) ≤
          monoTotalWords curRp curRm s.cur_nr.toNat := by
        have hstep : rSymLenSum curRp curRm (r.toNat + 1) + (r.toNat + 1) ≤
            rSymLenSum curRp curRm s.cur_nr.toNat + s.cur_nr.toNat := by
          have hdiff : ∀ d, rSymLenSum curRp curRm (r.toNat + 1) ≤
              rSymLenSum curRp curRm (r.toNat + 1 + d) := by
            intro d; induction d with
            | zero => simp
            | succ d ih =>
              rw [show r.toNat + 1 + (d + 1) = (r.toNat + 1 + d) + 1 by omega,
                rSymLenSum_succ curRp curRm (r.toNat + 1 + d)]
              exact le_trans ih (Nat.le_add_right _ _)
          have hd := hdiff (s.cur_nr.toNat - (r.toNat + 1))
          rw [show r.toNat + 1 + (s.cur_nr.toNat - (r.toNat + 1)) = s.cur_nr.toNat by omega] at hd
          omega
        rw [rSymLenSum_add_nr curRp curRm s.cur_nr.toNat] at hstep; omega
      have hsl_sum : (slR + BitVec.setWidth 64 (curRp[0 + mrOff.toNat]'(by
            have := hmr_sl.1; omega))).toNat =
          rSymLenSum curRp curRm (r.toNat + 1) := by
        simp only [Nat.zero_add]
        have hlt64 : slR.toNat + (curRp[mrOff.toNat]'hmr_sl.1).toNat < 2 ^ 64 := by
          rw [hslR, ← getD_eq_getElem curRp 0#32 hmr_sl.1, hmr_eq]
          rw [← rSymLenSum_succ]; omega
        rw [BitVec.toNat_add, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega : (curRp[mrOff.toNat]'hmr_sl.1).toNat < 2 ^ 64),
          Nat.mod_eq_of_lt hlt64, hslR, rSymLenSum_succ,
          ← getD_eq_getElem curRp 0#32 hmr_sl.1, hmr_eq]
      have hrp1 : (r + 1#32).toNat = r.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : r.toNat + 1 < 2 ^ 32)]
      exact hrec (s.cur_nr.toNat - (r + 1#32).toNat) (_, r + 1#32, ⟨⟩) mL (by omega)
        ⟨rfl, by rw [hrp1]; omega, rfl, by rw [hrp1]; exact hsl_sum⟩
    · exact hFail s tm0 tm1 pool0 pool1 mL hpc hptop rfl rfl rfl rfl rfl hm0
    · exact hFail s tm0 tm1 pool0 pool1 mL hpc hptop rfl rfl rfl rfl rfl hm0
    · exact hFail s tm0 tm1 pool0 pool1 mL hpc hptop rfl rfl rfl rfl rfl hm0
    ·
            have hr_eq : r.toNat = s.cur_nr.toNat := by
              have hnot : ¬ r.toNat < s.cur_nr.toNat := by c0_bv_omega
              omega
            have hslR_fin : slR.toNat = rSymLenSum curRp curRm s.cur_nr.toNat := by
              rw [← hr_eq]; exact hslR
            have hnprod_lt64 : nb.toNat * s.cur_nr.toNat < 2 ^ 64 := by
              have hnb32 : nb.toNat ≤ 2 ^ 32 - 1 := by have := nb.isLt; omega
              have hnr32 : s.cur_nr.toNat ≤ 2 ^ 32 - 1 := by have := s.cur_nr.isLt; omega
              have hm := Nat.mul_le_mul hnb32 hnr32
              omega
            have hnprod64 : ((BitVec.setWidth 64 nb : BitVec 64) *
                BitVec.setWidth 64 s.cur_nr).toNat = nb.toNat * s.cur_nr.toNat := by
              rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by omega : nb.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.cur_nr.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt hnprod_lt64]
            have hnprod_le : nb.toNat * s.cur_nr.toNat ≤ s.qcap.toNat := by
              have hnot : ¬ s.qcap.toNat < nb.toNat * s.cur_nr.toNat % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt hnprod_lt64] at hnot
              omega
            have hnr_qcap := apply_need_lt_u32_mul hnb_pos (by omega) hnprod_le hqcap32
            have hsub64 : ((BitVec.setWidth 64 s.tn - BitVec.setWidth 64 nb : BitVec 64) +
                BitVec.setWidth 64 nb * BitVec.setWidth 64 s.cur_nr).toNat =
                (s.tn.toNat - nb.toNat) + nb.toNat * s.cur_nr.toNat := by
              have hs1 : (BitVec.setWidth 64 s.tn - BitVec.setWidth 64 nb : BitVec 64).toNat =
                  s.tn.toNat - nb.toNat := by
                rw [BitVec.toNat_sub_of_le (by
                    rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                      Nat.mod_eq_of_lt (by omega : nb.toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : s.tn.toNat < 2 ^ 64)]
                    exact hnb_tn),
                  BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (by omega : nb.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : s.tn.toNat < 2 ^ 64)]
              rw [BitVec.toNat_add, hs1, hnprod64, Nat.mod_eq_of_lt (by omega)]
            have htcap_le : (s.tn.toNat - nb.toNat) + nb.toNat * s.cur_nr.toNat ≤ s.tcap.toNat := by
              have hnot : ¬ (BitVec.setWidth 64 s.tcap).ult
                  ((BitVec.setWidth 64 s.tn - BitVec.setWidth 64 nb) +
                    BitVec.setWidth 64 nb * BitVec.setWidth 64 s.cur_nr) := by c0_bv_omega
              rw [BitVec.ult, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by omega : s.tcap.toNat < 2 ^ 64), hsub64] at hnot
              simpa using hnot
            have hslB_lt32 : slB.toNat < 2 ^ 32 := by
              have := bxSymLenSum_add_nb_le_monoTotalWords
                (if s.pc.toNat = 0 then pool0 else pool1)
                (if s.tc.toNat = 0 then tm0 else tm1) bx hinc
              rw [← hslB] at this; omega
            have hR_tot : slR.toNat + s.cur_nr.toNat ≤ 4000000000 := by
              rw [hslR_fin, rSymLenSum_add_nr]; exact hcurTot
            have hneed64 : ((BitVec.setWidth 64 s.cur_nr : BitVec 64) * slB +
                BitVec.setWidth 64 nb * slR).toNat =
                s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat := by
              have hlt := apply_need_lt_u64 (by omega : nb.toNat < 2 ^ 30) hslB_lt32 hR_tot
              have h1 : (BitVec.setWidth 64 s.cur_nr * slB : BitVec 64).toNat =
                  s.cur_nr.toNat * slB.toNat := by
                rw [BitVec.toNat_mul, BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (by omega : s.cur_nr.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt)]
              have h2 : (BitVec.setWidth 64 nb * slR : BitVec 64).toNat =
                  nb.toNat * slR.toNat := by
                rw [BitVec.toNat_mul, BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (by omega : nb.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt)]
              rw [BitVec.toNat_add, h1, h2, Nat.mod_eq_of_lt hlt]
            have hneed_le : s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat ≤ s.pcap.toNat := by
              have hnot : ¬ s.pcap.ult (BitVec.setWidth 64 s.cur_nr * slB +
                  BitVec.setWidth 64 nb * slR) := by c0_bv_omega
              rw [BitVec.ult, hneed64] at hnot
              simpa using hnot
            clear hc
            let Rcmpt := array (t := i32) s.partner partnerArr ⋆
              array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
              array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
              qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R
            refine wp_join_group (fun _ mC =>
                ∃ (sC : ArCtxState) (tm0C tm1C pool0C pool1C : List (BitVec 32)),
                  let dstPool := if sC.pc.toNat = 0 then pool0C else pool1C
                  let dstTm := if sC.tc.toNat = 0 then tm0C else tm1C
                  sC.pc.toNat < 2 ∧ sC.ptop.toNat ≤ s.pcap.toNat ∧
                  sC = { s with pc := sC.pc, ptop := sC.ptop } ∧
                  tm0C.length = tm0.length ∧ tm1C.length = tm1.length ∧
                  pool0C.length = pool0.length ∧ pool1C.length = pool1.length ∧
                  sC.ptop.toNat + (s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤
                    s.pcap.toNat ∧
                  slB.toNat = bxSymLenSum dstPool dstTm bx nb.toNat ∧
                  (∀ i < s.tn.toNat,
                    MonoSliceOk dstPool (dstTm.getD i 0#32).toNat sC.ptop.toNat ∧
                    (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
                  (∀ i < s.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) ∧
                  SigOk dstPool dstTm (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat ∧
                  monoTotalWords dstPool dstTm s.tn.toNat ≤ sC.ptop.toNat ∧
                  (∀ b < nb.toNat, sym.toNat ∈ symListAt dstPool
                    (dstTm.getD (bx.getD b 0#32).toNat 0#32).toNat) ∧
                  (∀ i < s.tn.toNat,
                    symListAt dstPool (dstTm.getD i 0#32).toNat =
                      symListAt (if s.pc.toNat = 0 then pool0 else pool1)
                        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat) ∧
                  (arCtxMem cx sC ⋆ array (t := i32) sC.partner partnerArr ⋆
                    array (t := i32) sC.cur_rm curRm ⋆ array64 sC.cur_rl curRl ⋆
                    array64 sC.cur_rh curRh ⋆ array (t := i32) sC.cur_rp curRp ⋆
                    tMem sC tm0C tm1C ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
                    qMem sC qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) mC)
              ?_ ?_
            · rintro Jc ⟨⟩ mC ⟨sC, tm0C, tm1C, pool0C, pool1C, hpcC, hptC, hsC, htm0C, htm1C,
                  hp0C, hp1C, hroomC, hslBC, hSlC, hSortC, hSigC, hTotC, hbxMC, hSyEqC, hmC⟩
              c0_hsteps_nogrp
              c0_hsplit_nobound
              · c0_hsteps_nogrp
                exact hFail sC tm0C tm1C pool0C pool1C mC hpcC hptC hsC htm0C htm1C hp0C hp1C hmC
              · clear hc
                change wp Γ Q X (applyLoop3Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp
                  s.cur_nr s.tn s.bx nb slB slR) mC
                exact hDone sC tm0C tm1C pool0C pool1C slR mC hpcC hptC hsC htm0C htm1C hp0C hp1C
                  hnr_qcap.1 hnprod_le htcap_le hslR_fin hroomC hslBC hSlC hSortC hSigC hTotC
                  hbxMC hSyEqC hmC
            · intro Jc hJc
              c0_hsteps_nogrp
              c0_hsplit_nobound
              · obtain ⟨σ₀, _⟩ := hNonEmpty
                have hm_cmp : (arCtxMem cx s ⋆
                    tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ Rcmpt) mL := by
                  dsimp only [Rcmpt]; exact sep_cast hm0 (by ac_rfl)
                have hsrc_len :
                    s.ptop.toNat ≤ (if s.pc.toNat = 0 then pool0 else pool1).length := by
                  by_cases hpc0 : s.pc.toNat = 0 <;> simp [hpc0] <;> omega
                refine wp_call_of_spec _ _ (hComp _ mL _ X
                  ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, σ₀, Rcmpt,
                    hpc, htc, htn, htm0, htm1, hptop, hpcap32, hp0, hp1,
                    (fun i hi => ⟨Nat.lt_of_lt_of_le (hSlices i hi).1.1 hsrc_len,
                      le_trans (hSlices i hi).1.2 hsrc_len⟩),
                    le_trans hTot hptop, hm_cmp,
                    fun s1 tm0_1 tm1_1 pool0_1 pool1_1 m1 hpc1 hs1 hpt1_tot hpt1_cap
                      htm0_1 htm1_1 hp0_1 hp1_1 hp_eq htm_eq hsy1 hm_tot1 _ hm1 => ?_⟩)
                have hpc1_lt : s1.pc.toNat < 2 := by omega
                have hs1_norm : (arCtxMem cx s1 ⋆ array (t := i32) s1.partner partnerArr ⋆
                    array (t := i32) s1.cur_rm curRm ⋆ array64 s1.cur_rl curRl ⋆
                    array64 s1.cur_rh curRh ⋆ array (t := i32) s1.cur_rp curRp ⋆
                    tMem s1 tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
                    qMem s1 qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m1 := by
                  have hq1 : qMem s1 qm qs ql qh ix ix2 bx vqOff vq vqSkip =
                      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip := by
                    rw [hs1]; rfl
                  rw [show s1.partner = s.partner by rw [hs1],
                    show s1.cur_rm = s.cur_rm by rw [hs1], show s1.cur_rl = s.cur_rl by rw [hs1],
                    show s1.cur_rh = s.cur_rh by rw [hs1], show s1.cur_rp = s.cur_rp by rw [hs1],
                    hq1]
                  dsimp only [Rcmpt] at hm1; exact sep_cast hm1 (by ac_rfl)
                c0_hsteps_nogrp
                · exact hFail s1 tm0_1 tm1_1 pool0_1 pool1_1 m1 hpc1_lt hpt1_cap hs1
                    htm0_1 htm1_1 hp0_1 hp1_1 hs1_norm
                · exact hFail s1 tm0_1 tm1_1 pool0_1 pool1_1 m1 hpc1_lt hpt1_cap hs1
                    htm0_1 htm1_1 hp0_1 hp1_1 hs1_norm
                ·
                    have hroom1 : s1.ptop.toNat +
                        (s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤ s.pcap.toNat := by
                      have hpcap1 : s1.pcap.toNat = s.pcap.toNat := by rw [hs1]
                      have hnot := hc
                      rw [hpcap1] at hnot
                      have hlt := apply_need_lt_u64 (by omega : nb.toNat < 2 ^ 30) hslB_lt32 hR_tot
                      have hsub : (2 ^ 64 - s1.ptop.toNat + s.pcap.toNat) % 2 ^ 64 =
                          s.pcap.toNat - s1.ptop.toNat := by omega
                      rw [Nat.mod_eq_of_lt hlt, hsub] at hnot
                      omega
                    clear hc
                    let dPool := if s1.pc.toNat = 0 then pool0_1 else pool1_1
                    let dTm := if s1.tc.toNat = 0 then tm0_1 else tm1_1
                    have htc1 : s1.tc = s.tc := by rw [hs1]
                    have hd_eq : dPool = (if s.pc.toNat = 0 then pool1_1 else pool0_1) ∧
                        dTm = (if s.tc.toNat = 0 then tm0_1 else tm1_1) := by
                      dsimp only [dPool, dTm]
                      rw [hpc1, htc1]
                      constructor
                      · have h01 : s.pc.toNat = 0 ∨ s.pc.toNat = 1 := by omega
                        rcases h01 with h0 | h1
                        · simp [h0]
                        · simp [h1]
                      · rfl
                    have hsy1' : ∀ i < s.tn.toNat,
                        symListAt dPool (dTm.getD i 0#32).toNat =
                          symListAt (if s.pc.toNat = 0 then pool0 else pool1)
                            ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat ∧
                        MonoSliceOk dPool (dTm.getD i 0#32).toNat s1.ptop.toNat := by
                      rw [hd_eq.1, hd_eq.2]; exact hsy1
                    have hslB1 : slB.toNat =
                        bxSymLenSum dPool dTm bx nb.toNat := by
                      rw [hslB]
                      suffices h : ∀ m ≤ nb.toNat,
                          bxSymLenSum (if s.pc.toNat = 0 then pool0 else pool1)
                            (if s.tc.toNat = 0 then tm0 else tm1) bx m =
                            bxSymLenSum dPool dTm bx m from h nb.toNat (le_refl _)
                      intro m hm
                      induction m with
                      | zero => rfl
                      | succ b ih =>
                        rw [bxSymLenSum_succ, bxSymLenSum_succ, ih (by omega)]
                        congr 1
                        have hbn := hinc.1 b (by omega)
                        have he := (hsy1' (bx.getD b 0#32).toNat hbn).1
                        simpa only [symListAt, List.length_map, List.length_range] using
                          congrArg List.length he.symm
                    have hSl1 : ∀ i < s.tn.toNat,
                        MonoSliceOk dPool (dTm.getD i 0#32).toNat s1.ptop.toNat ∧
                        (dPool.getD (dTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := by
                      intro i hi
                      refine ⟨(hsy1' i hi).2, ?_⟩
                      have he := (hsy1' i hi).1
                      have hl : (dPool.getD (dTm.getD i 0#32).toNat 0#32).toNat =
                          ((if s.pc.toNat = 0 then pool0 else pool1).getD
                            ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat 0#32).toNat :=
                            by
                        simpa only [symListAt, List.length_map, List.length_range] using
                          congrArg List.length he
                      rw [hl]; exact (hSlices i hi).2
                    have hSort1 : ∀ i < s.tn.toNat, MonoSorted dPool (dTm.getD i 0#32).toNat := by
                      intro i hi
                      rw [MonoSorted, (hsy1' i hi).1]
                      exact hSorted i hi
                    have hSig1 : SigOk dPool dTm
                        (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat := by
                      intro i hi x hx
                      rw [(hsy1' i hi).1] at hx
                      exact hSig i hi x hx
                    have hm_tot1' : monoTotalWords dPool dTm s.tn.toNat ≤ s1.ptop.toNat := by
                      rw [hd_eq.1, hd_eq.2]; exact le_of_eq hm_tot1
                    have hbxM1 : ∀ b < nb.toNat, sym.toNat ∈ symListAt dPool
                        (dTm.getD (bx.getD b 0#32).toNat 0#32).toNat := by
                      intro b hb
                      rw [(hsy1' (bx.getD b 0#32).toNat (hinc.1 b hb)).1]
                      exact hbxMem b hb
                    refine hJc () m1 ⟨s1, tm0_1, tm1_1, pool0_1, pool1_1, hpc1_lt, hpt1_cap, hs1,
                      htm0_1, htm1_1, hp0_1, hp1_1, hroom1, hslB1, hSl1, hSort1, hSig1,
                      hm_tot1', hbxM1, fun i hi => (hsy1' i hi).1, hs1_norm⟩
              · have hroom0 : s.ptop.toNat +
                    (s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤ s.pcap.toNat := by
                  have hnot : ¬ (s.pcap - s.ptop).ult
                      (BitVec.setWidth 64 s.cur_nr * slB + BitVec.setWidth 64 nb * slR) := by
                    c0_bv_omega
                  rw [BitVec.ult, hneed64,
                    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hptop)] at hnot
                  omega
                clear hc
                c0_hsteps_nogrp
                exact hJc () mL ⟨s, tm0, tm1, pool0, pool1, hpc, hptop, rfl, rfl, rfl, rfl, rfl,
                  hroom0, hslB, hSlices, hSorted, hSig, hTot, hbxMem, fun _ _ => rfl, hm0⟩
  · intro J hJ
    c0_hsteps_nogrp
    exact hJ s.cur_nr.toNat (0#64, 0#32, ⟨⟩) m0 ⟨rfl, Nat.zero_le _, by simp, rfl⟩

end

end LeanQbe.T.Examples.Arisca.Proof
