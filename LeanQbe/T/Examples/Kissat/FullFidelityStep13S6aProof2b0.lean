/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `full_bve_var_m7` Helpers (`Proof2b0`)

Supporting invariant lemmas, AST sub-expression extractors, and factored resolution-loop
WP theorems for `FullFidelityStep12B.full_bve_var_m7_body` (`0` cross-shard `S0..S5` imports,
`0` `@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols, `<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics

@[expose] public section

section BvePipeHelpers
variable {V : Ty → Type} {L : List Ty → Type}

def sL64 (x : V i64) : Expr V L [i64] → Expr V L [i64]
  | .let_ (ts := [.bits 64]) _ k => k (x, ()) | _ => .hlt
def sL32 (x : V i32) : Expr V L [i64] → Expr V L [i64]
  | .let_ (ts := [.bits 32]) _ k => k (x, ()) | _ => .hlt
def sL8 (x : V (.bits 8)) : Expr V L [i64] → Expr V L [i64]
  | .let_ (ts := [.bits 8]) _ k => k (x, ()) | _ => .hlt
def sLb (x : V .bool) : Expr V L [i64] → Expr V L [i64]
  | .let_ (ts := [.bool]) _ k => k (x, ()) | _ => .hlt
def sD64 (x : V i64) : Expr V L [i64] → Expr V L [i64]
  | .load (.bits 64) _ k => k x | _ => .hlt
def sD32 (x : V i32) : Expr V L [i64] → Expr V L [i64]
  | .load (.bits 32) _ k => k x | _ => .hlt
def sD8 (x : V (.bits 8)) : Expr V L [i64] → Expr V L [i64]
  | .load (.bits 8) _ k => k x | _ => .hlt
def sC32 (x : V i32) : Expr V L [i64] → Expr V L [i64]
  | .call (bs := [.bits 32]) _ _ k => k (x, ()) | _ => .hlt
def sCb (x : V .bool) : Expr V L [i64] → Expr V L [i64]
  | .call (bs := [.bool]) _ _ k => k (x, ()) | _ => .hlt
def sT : Expr V L [i64] → Expr V L [i64]
  | .jnz _ t _ => t | _ => .hlt
def sE : Expr V L [i64] → Expr V L [i64]
  | .jnz _ _ f => f | _ => .hlt
def sB0 (j : L []) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[]]) bs _ => match bs (j, ()) with | .cons b _ => b ()
  | _ => .hlt
def sB64 (j : L [i64]) (x : V i64) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64]]) bs _ => match bs (j, ()) with | .cons b _ => b (x, ())
  | _ => .hlt
def sB32 (j : L [i32]) (x : V i32) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 32]]) bs _ => match bs (j, ()) with | .cons b _ => b (x, ())
  | _ => .hlt
def sBb (j : L [.bool]) (x : V .bool) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bool]]) bs _ => match bs (j, ()) with | .cons b _ => b (x, ())
  | _ => .hlt
def sB4 (j : L [i64, i64, i64, .bool])
    (x : Tup V [i64, i64, i64, .bool]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bool]]) bs _ =>
    match bs (j, ()) with | .cons b _ => b x
  | _ => .hlt
def sB6 (j : L [i64, i64, i64, .bool, i64, i32])
    (x : Tup V [i64, i64, i64, .bool, i64, i32]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bool, .bits 64, .bits 32]]) bs _ =>
    match bs (j, ()) with | .cons b _ => b x
  | _ => .hlt
def sB5 (j : L [i64, i64, i64, i64, i32])
    (x : Tup V [i64, i64, i64, i64, i32]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bits 64, .bits 32]]) bs _ =>
    match bs (j, ()) with | .cons b _ => b x
  | _ => .hlt
def sK0 (j : L []) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[]]) _ k => k (j, ()) | _ => .hlt
def sKb (j : L [.bool]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bool]]) _ k => k (j, ()) | _ => .hlt
def sK4 (j : L [i64, i64, i64, .bool]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bool]]) _ k => k (j, ()) | _ => .hlt
def sK5 (j : L [i64, i64, i64, .bool, i32]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bool, .bits 32]]) _ k => k (j, ())
  | _ => .hlt
def sK6 (j : L [i64, i64, i64, .bool, i64, i32]) : Expr V L [i64] → Expr V L [i64]
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bool, .bits 64, .bits 32]]) _ k =>
    k (j, ())
  | _ => .hlt

end BvePipeHelpers

def bveAt45 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool)
    (d64 : V i64) (_d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  FullFidelityStep12B.full_bve_var_m7_body V L (h, v, ())
    |> sL64 d64 |> sD64 scap |> sLb db |> sE
    |> sLb use_m8
    |> sB32 dJ32 occ_lim |> sB32 dJ32 neg_off |> sB32 dJ32 pos_mask |> sB32 dJ32 neg_mask
    |> sB32 dJ32 gf_idx |> sB32 dJ32 rg_idx |> sB64 dJ64 r_off
    |> sL64 d64 |> sD64 scr
    |> sL64 d64 |> sD64 vals
    |> sL64 d64 |> sD64 tmp
    |> sL64 d64 |> sD64 wvec
    |> sL64 d64 |> sD64 d64 |> sL64 d64 |> sL64 cv2
    |> sL64 d64 |> sD64 acap
    |> sL64 d64 |> sD64 wcap
    |> sL32 pl |> sL32 nl
    |> sC32 np
    |> sL64 d64 |> sL64 d64 |> sL64 d64
    |> sC32 nn
    |> sLb db |> sE |> sLb db |> sE
    |> sB0 dJ0
    |> sB64 dJ64 d64 |> sB64 dJ64 d64
    |> sLb push_pos
    |> sB64 dJ64 d64
    |> sBb dJb ext_ok

def bveFastAt45 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (J25 : L [])
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  bveAt45 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok
    d64 d32 db dJ0 dJ64 dJ32 dJb |> sK0 J25

def bvePhaseAt45 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool)
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  bveAt45 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok
    d64 d32 db dJ0 dJ64 dJ32 dJb |> sB0 dJ0

def bveAt52 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (lim_cls : V i64)
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  bvePhaseAt45 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok
    d64 d32 db dJ0 dJ64 dJ32 dJb
    |> sL64 d64 |> sL64 d64 |> sL64 d64 |> sL64 d64 |> sD64 d64 |> sL64 lim_cls

def bveFitAt52 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (lim_cls : V i64)
    (b52 : Tup V [i64, i64, i64, .bool]) (fit_f : V .bool)
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool])
    (dJ4 : L [i64, i64, i64, .bool]) : Expr V L [i64] :=
  bveAt52 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok lim_cls
    d64 d32 db dJ0 dJ64 dJ32 dJb |> sB4 dJ4 b52 |> sBb dJb fit_f |> sT

def bveDefragAt52 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (lim_cls : V i64)
    (b52 : Tup V [i64, i64, i64, .bool]) (Jpre : L [.bool])
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool])
    (dJ4 : L [i64, i64, i64, .bool]) : Expr V L [i64] :=
  bveAt52 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok lim_cls
    d64 d32 db dJ0 dJ64 dJ32 dJb |> sB4 dJ4 b52 |> sKb Jpre

def bveGatesAt52 (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (lim_cls : V i64) (J52 : L [i64, i64, i64, .bool])
    (d64 : V i64) (d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  bveAt52 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok lim_cls
    d64 d32 db dJ0 dJ64 dJ32 dJb |> sK4 J52 |> sT

def bveILoopAt54B (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (push_pos ext_ok : V .bool) (lim_cls : V i64) (J52 : L [i64, i64, i64, .bool])
    (gf rg : V .bool) (res_sz0 : V i64)
    (d64 : V i64) (d32 : V i32) (d8 : V (.bits 8)) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) (dJb : L [.bool]) :
    Expr V L [i64] :=
  bveGatesAt52 V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
    scr vals tmp wvec cv2 acap wcap pl nl np nn push_pos ext_ok lim_cls J52
    d64 d32 db dJ0 dJ64 dJ32 dJb
    |> sB0 dJ0
    |> sL64 d64 |> sD64 d64 |> sLb db |> sE
    |> sL64 d64 |> sL64 d64 |> sD8 d8 |> sL8 d8 |> sL32 d32 |> sL32 d32 |> sLb db |> sE
    |> sL64 d64 |> sL64 d64 |> sL64 d64 |> sD32 d32 |> sLb gf
    |> sL64 d64 |> sL64 d64 |> sL64 d64 |> sD32 d32 |> sLb rg
    |> sL64 d64 |> sD64 res_sz0

end

private def bveRlen1Expr (hdr pTmp pVals cv2 rp_j rcnt_j west_j rsz1 : Val i64)
    (j : Val i32) (Lj : Cont [i64, i64, i64, i64, i32]) : Expr Val Cont [i64] :=
  Expr.let_ (op1 (.sext 32 64) (.imm 0)) fun p =>
  Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
  Expr.let_ (op2 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
  Expr.load i32 (.var p.fst) fun ld =>
  Expr.group (sig := [[]])
    (fun _ => Blocks.cons
      (fun _ =>
        Expr.let_ (op2 (.add i32) (.var j) (.imm 1)) fun p =>
        Expr.jump Lj (.var rp_j, .var rcnt_j, .var west_j, .var rsz1, .var p.fst, ()))
      Blocks.nil)
    fun Js =>
  Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
  Expr.let_ (op2 (.cmp .ult i64) (.var p.fst) (.var cv2)) fun p =>
  Expr.jnz (.var p.fst)
    (Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
     Expr.let_ (op2 (.add i64) (.var pVals) (.var p.fst)) fun p =>
     Expr.load i8 (.var p.fst) fun ld_1 =>
     Expr.let_ (op1 (.trunc 32 8) (.imm 0)) fun p =>
     Expr.let_ (op1 (.sext 8 32) (.var ld_1)) fun p_1 =>
     Expr.let_ (op1 (.sext 8 32) (.var p.fst)) fun p =>
     Expr.let_ (op2 (.cmp .slt i32) (.var p_1.fst) (.var p.fst)) fun p =>
     Expr.jnz (.var p.fst)
       (Expr.let_ (op2 (.add i64) (.var hdr) (.imm 1144)) fun p =>
        Expr.store (t := i64) (.var rsz1) (.var p.fst)
          (Expr.let_ (op2 (.add i64) (.var hdr) (.imm 1024)) fun p =>
           Expr.store (t := i64) (.imm (1 : Val i64)) (.var p.fst)
             (.ret (.imm (20 : Val i64), ()))))
       (Expr.group (sig := [[]])
          (fun _ => Blocks.cons (fun _ => .jump Js.fst ()) Blocks.nil) fun Js2 =>
        Expr.let_ (op1 (.trunc 32 8) (.imm 0)) fun p =>
        Expr.let_ (op1 (.sext 8 32) (.var ld_1)) fun p_2 =>
        Expr.let_ (op1 (.sext 8 32) (.var p.fst)) fun p =>
        Expr.let_ (op2 (.cmp .eq i32) (.var p_2.fst) (.var p.fst)) fun p =>
        Expr.jnz (.var p.fst)
          (.call "full_assign_lvl" (as := [i64, i32, i32, i32]) (bs := [])
            (.var hdr, .var ld, .imm 4294967295, .imm 0, ())
            fun _ => .jump Js2.fst ())
          (.jump Js2.fst ())))
    (.jump Js.fst ())

private def bveRlen2Expr (pTmp pScratchBuf pWvec cv2 scap rlen lim_cls : Val i64)
    (rp_j rcnt_j west_j rsz1 : Val i64) (fit : Bool) (j : Val i32)
    (Bj : Cont [i64, i64, i64, .bool, i64, i32])
    (J81 : Cont [i64, i64, i64, .bool, i32]) : Expr Val Cont [i64] :=
  Expr.let_ (op2 (.add i64) (.var rcnt_j) (.imm 1)) fun p =>
  Expr.let_ (op2 (.cmp .ugt i64) (.var rlen) (.imm 100)) fun p_1 =>
  Expr.jnz (.var p_1.fst)
    (.jump Bj (.var rp_j, .var p.fst, .var west_j, .imm false, .var rsz1, .var j, ()))
    (Expr.let_ (op2 (.cmp .ugt i64) (.var p.fst) (.var lim_cls)) fun p_2 =>
     Expr.jnz (.var p_2.fst)
       (.jump Bj (.var rp_j, .var p.fst, .var west_j, .imm false, .var rsz1, .var j, ()))
       (Expr.let_ (op2 (.add i64) (.var rp_j) (.imm 1)) fun p_3 =>
        Expr.let_ (op2 (.add i64) (.var p_3.fst) (.var rlen)) fun p_4 =>
        Expr.let_ (op2 (.cmp .ugt i64) (.var p_4.fst) (.var scap)) fun p_5 =>
        Expr.jnz (.var p_5.fst)
          (.jump Bj (.var rp_j, .var p.fst, .var west_j, .imm false, .var rsz1, .var j, ()))
          (Expr.let_ (op2 (.mul i64) (.var rp_j) (.imm 4)) fun p_6 =>
           Expr.let_ (op2 (.add i64) (.var pScratchBuf) (.var p_6.fst)) fun p_7 =>
           Expr.let_ (op1 (.trunc 64 32) (.var rlen)) fun p_8 =>
           Expr.store (.var p_8.fst) (.var p_7.fst)
             (Expr.group (sig := [[i64, i32]]) (fun Js => Blocks.cons (fun p_9 =>
                Expr.let_ (op1 (.zext 32 64) (.var p_9.snd.fst)) fun p_10 =>
                Expr.let_ (op2 (.cmp .ult i64) (.var p_10.fst) (.var rlen)) fun p_11 =>
                Expr.jnz (.var p_11.fst)
                  (Expr.let_ (op1 (.zext 32 64) (.var p_9.snd.fst)) fun p =>
                   Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                   Expr.let_ (op2 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
                   Expr.load i32 (.var p.fst) fun ld =>
                   Expr.let_ (op2 (.add i64) (.var rp_j) (.imm 1)) fun p =>
                   Expr.let_ (op1 (.zext 32 64) (.var p_9.snd.fst)) fun p_12 =>
                   Expr.let_ (op2 (.add i64) (.var p.fst) (.var p_12.fst)) fun p =>
                   Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                   Expr.let_ (op2 (.add i64) (.var pScratchBuf) (.var p.fst)) fun p =>
                   Expr.store (.var ld) (.var p.fst)
                     (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                        Expr.let_ (op2 (.add i32) (.var p_9.snd.fst) (.imm 1)) fun p_13 =>
                        Expr.jump Js.fst (.var p.fst, .var p_13.fst, ())) Blocks.nil)
                       fun Js2 =>
                      Expr.let_ (op2 (.cmp .uge i64) (.var rlen) (.imm 2)) fun p =>
                      Expr.jnz (.var p.fst)
                        (Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                         Expr.let_ (op2 (.cmp .ult i64) (.var p.fst) (.var cv2)) fun p =>
                         Expr.jnz (.var p.fst)
                           (Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                            Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun p_13 =>
                            Expr.let_ (op2 (.shl i64) (.var p.fst) (.var p_13.fst)) fun p =>
                            Expr.let_ (op2 (.add i64) (.var p.fst) (.imm 1)) fun p =>
                            Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                            Expr.let_ (op2 (.add i64) (.var pWvec) (.var p.fst)) fun p =>
                            Expr.load i32 (.var p.fst) fun ld =>
                            Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                            Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun p_14 =>
                            Expr.let_ (op2 (.shl i64) (.var p.fst) (.var p_14.fst)) fun p =>
                            Expr.let_ (op2 (.add i64) (.var p_9.fst) (.var p.fst)) fun p =>
                            Expr.let_ (op2 (.add i64) (.var p.fst) (.imm 4)) fun p =>
                            Expr.jump Js2.fst (.var p.fst, ()))
                           (.jump Js2.fst (.var p_9.fst, ())))
                        (.jump Js2.fst (.var p_9.fst, ()))))
                  (Expr.let_ (op2 (.add i64) (.var rp_j) (.imm 1)) fun p_12 =>
                   Expr.let_ (op2 (.add i64) (.var p_12.fst) (.var rlen)) fun p_13 =>
                   Expr.jump J81
                     (.var p_13.fst, .var p.fst, .var p_9.fst, .var fit, .var j, ())))
                Blocks.nil) fun Js => Expr.jump (ts := [i64, i32]) Js.fst
                  (.var west_j, Arg.imm (t := i32) 0, ())))))

public section

/-! ## 1. Pure, Invariant & Separation Helpers -/

theorem s6a_var_resBuf_mono {F_cur : List (List Nat)} {s s' : FullState}
    {r_end p : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (heq : ∀ idx, p ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s' r_end p := by
  induction h with
  | nil => exact .nil
  | @cons p sz hle hsz hlt hnd hent _ ih =>
    have h0 := heq p (Nat.le_refl _) (by omega)
    have hk : ∀ k < sz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => heq (p + 1 + k) (by omega) (by omega)
    refine .cons hle (by rw [h0]; exact hsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hlt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => heq idx (by omega) hi2)
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hnd
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hent

theorem s6a_var_resBuf_append {F_cur : List (List Nat)} {s s' : FullState}
    {r_off rp sz : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hpref : ∀ idx, r_off ≤ idx → idx < rp →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s rp r_off)
    (hsz : (s'.scratch.scratch_buf[rp]?.getD 0#32).toNat = sz)
    (hlt : ∀ k < sz, (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat < 2 * s'.core.cur_vars)
    (hnd : ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat))) :
    FullResBufOkW F_cur s' (rp + 1 + sz) r_off := by
  induction h with
  | nil => exact .cons (Nat.le_refl _) hsz hlt hnd hent .nil
  | @cons p psz hle hpsz hplt hpnd hpent _ ih =>
    have h0 := hpref p (Nat.le_refl _) (by omega)
    have hk : ∀ k < psz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => hpref (p + 1 + k) (by omega) (by omega)
    refine .cons (by omega) (by rw [h0]; exact hpsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hplt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => hpref idx (by omega) hi2)
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpnd
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpent

theorem s6a_var_bveEntry_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk; split at h <;> simp_all

theorem s6a_var_bveEntry_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  unfold FullBveEntryOkW at h
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; rw [ite_eq_right hb] at h
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    have hal := hdw.1.core_ok.arena_len_le; omega

theorem s6a_var_fullDenseInvW_setInact13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} {unass' : BitVec 64}
    {qp' qn' qs' : List (BitVec 32)} {qsi' qss' qf' ql' : BitVec 64}
    {hp' ps' : List (BitVec 32)} {hl' : Nat}
    (hlen : ({ s with
      core := { s.core with flags := fl', unassigned := unass' }
      scratch := { s.scratch with
        q_prev := qp', q_next := qn', q_stamp := qs',
        q_search_idx := qsi', q_search_stamp := qss',
        q_first := qf', q_last := ql',
        heap := hp', pos := ps', heap_len := hl' } } : FullState).LengthsOk c) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with flags := fl', unassigned := unass' }
        scratch := { s.scratch with
          q_prev := qp', q_next := qn', q_stamp := qs',
          q_search_idx := qsi', q_search_stamp := qss',
          q_first := qf', q_last := ql',
          heap := hp', pos := ps', heap_len := hl' } } := by
  have h1 : FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := unass' } } :=
    ⟨⟨{ h.1.core_ok with flags_len := hlen.core_ok.flags_len }, h.1.scratch_ok⟩,
     { h.2.1 with
       arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
       watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
     h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  exact m6_fullDenseInvW_with_scratch h1 hlen.scratch_ok rfl rfl

theorem s6a_var_take_map {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length) :
    (xs.take n).map BitVec.toNat =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem s6a_var_take_div2 {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length) :
    (xs.take n).map (fun x => x.toNat / 2) =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat / 2) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem s6a_var_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * v.toNat + 1 := by
  have h := m8_pl_nl_eq v hv
  exact ⟨h.1, by simpa [show ((1 : BitVec 32)) = 1#32 from rfl] using h.2⟩

theorem s6a_var_layout_ok {scap : Nat}
    {occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : BitVec 32} {r_off : BitVec 64}
    (hsc2048 : 2048 ≤ scap)
    (hocc : (16384 ≤ scap ∧ occ_lim = 2001#32) ∨ (scap < 16384 ∧ occ_lim = 512#32))
    (hneg : neg_off = occ_lim)
    (hpm : (occ_lim = 2001#32 ∧ pos_mask = 4002#32) ∨ (occ_lim = 512#32 ∧ pos_mask = 1024#32))
    (hnm : (occ_lim = 2001#32 ∧ neg_mask = 4066#32) ∨ (occ_lim = 512#32 ∧ neg_mask = 1040#32))
    (hgf : (occ_lim = 2001#32 ∧ gf_idx = 4130#32) ∨ (occ_lim = 512#32 ∧ gf_idx = 1056#32))
    (hrg : (occ_lim = 2001#32 ∧ rg_idx = 4131#32) ∨ (occ_lim = 512#32 ∧ rg_idx = 1057#32))
    (hroff : (occ_lim = 2001#32 ∧ r_off = 4192#64) ∨ (occ_lim = 512#32 ∧ r_off = 1088#64)) :
    occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat ∧
    r_off.toNat ≤ scap ∧
    gf_idx.toNat < r_off.toNat ∧
    rg_idx.toNat < r_off.toNat ∧
    (∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat) ∧
    (∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat) ∧
    (16384 ≤ scap → occ_lim = 2001#32 ∧ neg_off.toNat = 2001) ∧
    (scap < 16384 → occ_lim = 512#32 ∧ neg_off.toNat = 512) := by
  subst hneg
  have hne : (2001#32 : BitVec 32) ≠ 512#32 := by decide
  rcases hocc with ⟨hsc16, rfl⟩ | ⟨hsc16, rfl⟩
  · rcases hpm.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hnm.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hgf.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hrg.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hroff.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    refine ⟨by decide, by simp; omega, by decide, by decide, ?_, ?_,
      fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
    · intro i hi
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hi ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro j hj
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hj ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rcases hpm.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hnm.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hgf.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hrg.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hroff.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    refine ⟨by decide, by simp; omega, by decide, by decide, ?_, ?_,
      fun hge => by omega, fun _ => ⟨rfl, rfl⟩⟩
    · intro i hi
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hi ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro j hj
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hj ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem s6a_bv8_dom_neg {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).slt (((0 : BitVec 32).setWidth 8).signExtend 32) = true) :
    v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem s6a_bv8_dom_zero {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : v.signExtend 32 = ((0 : BitVec 32).setWidth 8).signExtend 32) :
    v = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem s6a_lvl0_unit_contra_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false hent fun x hx => ?_)
  simp only [List.mem_singleton] at hx; rw [hx]; right
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hl0; rwa [htrl] at hs

/-! ## 2. Factored `rlen == 1` & `rlen >= 2` Branches -/

private theorem s6a_bve_var_rlen1_wp (Γ : Env)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s3 sj : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {nn : BitVec 32} {r_off : BitVec 64}
    {rp_j rcnt_j west_j rsz_j : BitVec 64} {j : BitVec 32}
    {lm_r : List (BitVec 8)} {tmp_r : List (BitVec 32)} {tl_r : Nat}
    {m_r : Mem 64}
    {Lj : Cont [i64, i64, i64, i64, i32]}
    (hcv_0 : s0.core.cur_vars ≤ c.max_vars)
    (hmx : c.max_vars < 2 * 2 ^ 28)
    (hj_lt : j.toNat < nn.toNat)
    (hj1 : (j + 1#32).toNat = j.toNat + 1)
    (hcvj : sj.core.cur_vars = s0.core.cur_vars)
    (harj : sj.core.arena = s3.core.arena)
    (halj : sj.core.arena_len = s3.core.arena_len)
    (hflj : sj.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hrpj_lo : r_off.toNat ≤ rp_j.toNat)
    (hrpj_hi : rp_j.toNat ≤ c.scratch_cap)
    (hkeepj : ∀ k < r_off.toNat, sj.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?)
    (hdwr : FullDenseInvW c F0 F_cur
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } })
    (htmkr : TmkZero
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } })
    (hres_sr : FullResBufOkW F_cur
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
      rp_j.toNat r_off.toNat)
    (hm_r : (FullMem c
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } } ⋆ R) m_r)
    (htl_cv : tl_r ≤ c.max_vars)
    (htl1 : tl_r = 1)
    (hr_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp_r.take tl_r).map BitVec.toNat)))
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hLj : ∀ rem_j' (args : Tup Val [i64, i64, i64, i64, i32]) mj',
      rem_j' < nn.toNat - j.toNat →
      (∃ sk : FullState,
        args.2.2.2.2.1.toNat ≤ nn.toNat ∧ rem_j' = nn.toNat - args.2.2.2.2.1.toNat ∧
        FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
        sk.core.cur_vars = s0.core.cur_vars ∧ sk.core.arena = s3.core.arena ∧
        sk.core.arena_len = s3.core.arena_len ∧ sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        r_off.toNat ≤ args.1.toNat ∧ args.1.toNat ≤ c.scratch_cap ∧
        FullResBufOkW F_cur sk args.1.toNat r_off.toNat ∧
        (∀ k < r_off.toNat, sk.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
        (FullMem c sk ⋆ R) mj') →
      Lj args mj') :
    wp Γ Q X (bveRlen1Expr c.hdr c.pTmp c.pVals
      (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat))
      rp_j rcnt_j west_j (rsz_j + 1#64) j Lj) m_r := by
  let sr : FullState :=
    { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
  have htmp0 : 0 < tmp_r.length := by rw [hdwr.1.core_ok.tmp_len_arr]; omega
  let ul := tmp_r[0]'htmp0
  have htake1 : (tmp_r.take tl_r).map BitVec.toNat = [ul.toNat] := by
    rw [htl1]; cases htr : tmp_r with
    | nil => simp [htr] at htmp0
    | cons a _ => simp [ul, htr]
  have hul_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
    simpa only [htake1] using hr_ent
  unfold bveRlen1Expr
  c0_hsteps_nogrp
  let InvU (su : FullState) (mu : Mem 64) : Prop :=
    FullDenseInvW c F0 F_cur su ∧ TmkZero su ∧
    su.core.cur_vars = s0.core.cur_vars ∧ su.core.arena = s3.core.arena ∧
    su.core.arena_len = s3.core.arena_len ∧ su.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
    FullResBufOkW F_cur su rp_j.toNat r_off.toNat ∧
    (∀ k < r_off.toNat, su.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
    (FullMem c su ⋆ R) mu
  refine wp_join_state0 (α := FullState) InvU ?_ ?_
  · rintro _ su mu ⟨hdwu, htmku, hcvu, haru, halu, hflu, hresu, hkeepu, hmu⟩
    c0_hsteps!
    exact hLj (nn.toNat - (j + 1#32).toNat)
      (rp_j, rcnt_j, west_j, rsz_j + 1#64, j + 1#32, ()) mu (by rw [hj1]; omega)
      ⟨su, by rw [hj1]; omega, rfl, hdwu, htmku, hcvu, haru, halu, hflu,
       hrpj_lo, hrpj_hi, hresu, hkeepu, hmu⟩
  · intro Jul hJul
    c0_hsplit
    · have hul_lt : ul.toNat < 2 * sr.core.cur_vars := by
        have hcv_max : sr.core.cur_vars ≤ c.max_vars := hdwr.1.core_ok.cur_vars_le
        have hc' : tmp_r[0].toNat < 2 * s0.core.cur_vars := by
          simpa [Nat.zero_mod,
            Nat.mod_eq_of_lt (by rw [← hcvj]; omega : s0.core.cur_vars < 2 ^ 64),
            Nat.mod_eq_of_lt (by rw [← hcvj]; omega : 2 * s0.core.cur_vars < 2 ^ 64)] using hc
        dsimp only [sr]; rw [hcvj]; exact hc'
      have hul_vl : (ul.setWidth 64).toNat < sr.core.vals.length := by
        rw [hdwr.1.core_ok.vals_len, m6_zext32_toNat]
        have hcv_r : sr.core.cur_vars ≤ c.max_vars := hdwr.1.core_ok.cur_vars_le
        omega
      have hul_dom := hdwr.2.1.vals_domain ul.toNat hul_lt
      have hul_vget :
          sr.core.vals[ul.toNat]?.getD 0#8 = sr.core.vals[(ul.setWidth 64).toNat]'hul_vl := by
        rw [List.getElem?_eq_getElem (by rw [m6_zext32_toNat] at hul_vl; exact hul_vl),
          Option.getD_some]
        exact m6_getElem_congr (m6_zext32_toNat ul).symm _ _
      c0_hsplit
      · have huv_neg : sr.core.vals[ul.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hul_vget] at hul_dom ⊢; exact s6a_bv8_dom_neg hul_dom hc
        have huns := s6a_lvl0_unit_contra_unsat hdwr.2.1 hdwr.2.2.2.2.2.1 hul_lt huv_neg hul_ent
        c0_hsteps!
        let sr1 : FullState := { sr with scratch := { sr.scratch with res_sz := rsz_j + 1#64 } }
        have hdw_sr1 := m6_fullDenseInvW_with_scratch hdwr (sc' := sr1.scratch)
          { hdwr.1.scratch_ok with } rfl rfl
        let sr2 : FullState := { sr1 with core := { sr1.core with inconsistent := 1#64 } }
        have hdw_sr2 := m6_fullDenseInvW_set_inc hdw_sr1 huns
        exact hQ 20#64 sr2 _ hdw_sr2.toDense htmkr (by dsimp only [sr2, sr1, sr]; omega)
          hflj (Or.inr (Or.inr rfl)) (fun _ => hdw_sr2.2.1.ext_sound.2 huns) hm
      · clear hc
        refine wp_join_state0 (α := FullState) InvU ?_ ?_
        · rintro _ su mu hsu; c0_hsteps!; exact hJul su mu hsu
        · intro Jul2 hJul2
          c0_hsplit
          · have huv_zero : sr.core.vals[ul.toNat]?.getD 0#8 = 0#8 := by
              rw [hul_vget] at hul_dom ⊢; exact s6a_bv8_dom_zero hul_dom hc
            have hte_lt : sr.core.trail_end < sr.core.cur_vars :=
              hdwr.2.1.trail_end_lt_of_unassigned hul_lt huv_zero
            have hnot_skip : ¬ (sr.core.cur_vars ≤ ul.toNat / 2 ∨
                c.max_vars ≤ sr.core.trail_end ∨ sr.core.vals[ul.toNat]?.getD 0#8 ≠ 0#8) := by
              have hcv_r : sr.core.cur_vars ≤ c.max_vars := hdwr.1.core_ok.cur_vars_le
              simp only [huv_zero, ne_eq, not_true_eq_false, or_false]; omega
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
            refine ⟨c, sr, R, rfl, hdwr.1, hm_r, ?_⟩
            simp only [Arg.val, show (BitVec.ofNat 64 0).toNat = 0 from rfl]
            rw [ite_eq_right (by simpa [ul] using hnot_skip)]
            intro fl_a un_a ph_a m_a hfl_a hph_a hm_a
            simp only [show ((0 : BitVec 32) = 0#32) = True from eq_true rfl, ↓reduceIte] at hm_a
            obtain ⟨hdw_a, _⟩ := FullM6Sweep.assignLvl0_preserves_denseInvW
              hdwr (lit := ul) (unassigned' := un_a) (unflushed' := sr.core.unflushed + 1#64)
              hfl_a hph_a hul_lt huv_zero hul_ent
            let sA : FullState :=
              { sr with
                core := { sr.core with
                  vals := (sr.core.vals.set ul.toNat 1#8).set (ul.toNat ^^^ 1) 0xFF#8
                  flags := fl_a, lvl := sr.core.lvl.set (ul.toNat / 2) 0#32
                  rsns := sr.core.rsns.set (ul.toNat / 2) 0xFFFFFFFF#32
                  trl := sr.core.trl.set sr.core.trail_end ul
                  trail_pos :=
                    sr.core.trail_pos.set (ul.toNat / 2) (BitVec.ofNat 32 sr.core.trail_end)
                  trail_end := sr.core.trail_end + 1
                  unassigned := un_a, unflushed := sr.core.unflushed + 1#64 }
                scratch := { sr.scratch with phases := ph_a } }
            have hres_a : FullResBufOkW F_cur sA rp_j.toNat r_off.toNat :=
              s6a_var_resBuf_mono (s := sr) (s' := sA) rfl (fun _ _ _ => rfl) hres_sr
            c0_hsteps!
            exact hJul2 sA m_a ⟨hdw_a, htmkr, hcvj, harj, halj, hflj, hres_a, hkeepj, hm_a⟩
          · c0_hsteps!
            exact hJul2 sr m_r ⟨hdwr, htmkr, hcvj, harj, halj, hflj, hres_sr, hkeepj, hm_r⟩
    · c0_hsteps!
      exact hJul sr m_r ⟨hdwr, htmkr, hcvj, harj, halj, hflj, hres_sr, hkeepj, hm_r⟩

private theorem s6a_bve_var_rlen2_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s3 sj : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {r_off lim_cls : BitVec 64} {fit : Bool}
    {rp_j rcnt_j west_j rsz_j : BitVec 64} {j : BitVec 32}
    {lm_r : List (BitVec 8)} {tmp_r : List (BitVec 32)} {tl_r : Nat}
    {m_r : Mem 64}
    {Bj : Cont [i64, i64, i64, .bool, i64, i32]}
    {J81 : Cont [i64, i64, i64, .bool, i32]}
    (hmx : c.max_vars < 2 * 2 ^ 28)
    (hsc : c.scratch_cap ≤ 2 ^ 29)
    (hcvj : sj.core.cur_vars = s0.core.cur_vars)
    (harj : sj.core.arena = s3.core.arena)
    (halj : sj.core.arena_len = s3.core.arena_len)
    (hflj : sj.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hrpj_lo : r_off.toNat ≤ rp_j.toNat)
    (hrpj_hi : rp_j.toNat ≤ c.scratch_cap)
    (hkeepj : ∀ k < r_off.toNat, sj.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?)
    (hdwr : FullDenseInvW c F0 F_cur
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } })
    (htmkr : TmkZero
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } })
    (hres_sr : FullResBufOkW F_cur
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
      rp_j.toNat r_off.toNat)
    (hm_r : (FullMem c
      { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } } ⋆ R) m_r)
    (htl_cv : tl_r ≤ c.max_vars)
    (hr_lt : ∀ k < tl_r, (tmp_r[k]?.getD 0#32).toNat < 2 * sj.core.cur_vars)
    (hr_nd : ((tmp_r.take tl_r).map fun x => x.toNat / 2).Nodup)
    (hr_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp_r.take tl_r).map BitVec.toNat)))
    (hBj : ∀ (args : Tup Val [i64, i64, i64, .bool, i64, i32]) mb,
      (∃ sb : FullState,
        FullDenseInvW c F0 F_cur sb ∧ TmkZero sb ∧
        sb.core.cur_vars = s0.core.cur_vars ∧ sb.core.arena = s3.core.arena ∧
        sb.core.arena_len = s3.core.arena_len ∧ sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        r_off.toNat ≤ args.1.toNat ∧ args.1.toNat ≤ c.scratch_cap ∧
        FullResBufOkW F_cur sb args.1.toNat r_off.toNat ∧
        (∀ k < r_off.toNat, sb.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
        (FullMem c sb ⋆ R) mb) →
      Bj args mb)
    (hJ81 : ∀ (args : Tup Val [i64, i64, i64, .bool, i32]) mk,
      (args.2.2.2.2.1 = j ∧
      ∃ sk : FullState,
        FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
        sk.core.cur_vars = s0.core.cur_vars ∧ sk.core.arena = s3.core.arena ∧
        sk.core.arena_len = s3.core.arena_len ∧ sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        r_off.toNat ≤ args.1.toNat ∧ args.1.toNat ≤ c.scratch_cap ∧
        FullResBufOkW F_cur sk args.1.toNat r_off.toNat ∧
        (∀ k < r_off.toNat, sk.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
        (FullMem c sk ⋆ R) mk) →
      J81 args mk) :
    wp Γ Q X (bveRlen2Expr c.pTmp c.pScratchBuf c.pWvec
      (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat))
      (BitVec.ofNat 64 c.scratch_cap) (BitVec.ofNat 64 tl_r) lim_cls
      rp_j rcnt_j west_j (rsz_j + 1#64) fit j Bj J81) m_r := by
  let sr : FullState :=
    { sj with core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
  unfold bveRlen2Expr
  c0_hsplit
  · c0_hsteps!
    exact hBj (rp_j, rcnt_j + 1#64, west_j, false, rsz_j + 1#64, j, ()) m_r
      ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
  · have htl100 : tl_r ≤ 100 := by
      rw [Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64),
        show (100 : BitVec 64).toNat = 100 from rfl] at hc
      omega
    c0_hsplit
    · c0_hsteps!
      exact hBj (rp_j, rcnt_j + 1#64, west_j, false, rsz_j + 1#64, j, ()) m_r
        ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
    · c0_hsplit
      · c0_hsteps!
        exact hBj (rp_j, rcnt_j + 1#64, west_j, false, rsz_j + 1#64, j, ()) m_r
          ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
      · have hrp_sum : (rp_j + 1 + BitVec.ofNat 64 tl_r).toNat = rp_j.toNat + 1 + tl_r := by
          c0_bound
        have hrp_fit : rp_j.toNat + 1 + tl_r ≤ c.scratch_cap := by
          rw [show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : rp_j.toNat + 1 + tl_r < 2 ^ 64)] at hc
          omega
        have hrp_sc : rp_j.toNat < sr.scratch.scratch_buf.length := by
          rw [hdwr.1.scratch_ok.scratch_buf_len]; omega
        c0_hsteps_nogrp
        let scr_w0 := sr.scratch.scratch_buf.set rp_j.toNat ((BitVec.ofNat 64 tl_r).setWidth 32)
        have hlen_w0 : (BitVec.ofNat 64 tl_r).setWidth 32 = BitVec.ofNat 32 tl_r := by
          apply BitVec.eq_of_toNat_eq; simp
        refine wp_loop_group (ts := [i64, i32])
          (fun rem_k (wk, k, ()) mk =>
            ∃ scr_k : List (BitVec 32),
              let sk : FullState := { sr with scratch := { sr.scratch with scratch_buf := scr_k } }
              scr_k.length = c.scratch_cap ∧ k.toNat ≤ tl_r ∧ rem_k = tl_r - k.toNat ∧
              (∀ idx < rp_j.toNat, scr_k[idx]? = sr.scratch.scratch_buf[idx]?) ∧
              scr_k[rp_j.toNat]? = some (BitVec.ofNat 32 tl_r) ∧
              (∀ t < k.toNat, scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]?) ∧
              (FullMem c sk ⋆ R) mk)
          ?_ ?_
        · rintro Lk rem_k ⟨wk, k, ⟨⟩⟩ mk hLk ⟨scr_k, hsck, hk_le, rfl, hpre_k, hsz_k, hcp_k, hmk⟩
          c0_hsplit
          · have hk_lt : k.toNat < tl_r := by
              rw [Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64)] at hc; exact hc
            have hk_tmp : (k.setWidth 64).toNat < tmp_r.length := by
              rw [hdwr.1.core_ok.tmp_len_arr, m6_zext32_toNat]; omega
            have hk_sc : (rp_j + 1#64 + k.setWidth 64).toNat < scr_k.length := by
              rw [hsck]; c0_bound
            have hk_sc_eq : (rp_j + 1#64 + k.setWidth 64).toNat = rp_j.toNat + 1 + k.toNat := by
              c0_bound
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            let lk := tmp_r[(k.setWidth 64).toNat]'hk_tmp
            let scr_k' := scr_k.set (rp_j + 1#64 + k.setWidth 64).toNat lk
            have hstep_k : ∀ (wk' : BitVec 64) m_step,
                (FullMem c { sr with scratch := { sr.scratch with scratch_buf := scr_k' } } ⋆ R)
                  m_step → Lk (wk', k + 1#32, ()) m_step := fun wk' m_step hm_s =>
              hLk (tl_r - (k + 1#32).toNat) (wk', k + 1#32, ()) m_step (by omega)
                ⟨scr_k', by simp [scr_k', hsck], by omega, rfl,
                 fun idx hidx => by
                   dsimp only [scr_k']; rw [List.getElem?_set_ne (by omega)]; exact hpre_k idx hidx,
                 by dsimp only [scr_k']; rw [List.getElem?_set_ne (by omega)]; exact hsz_k,
                 fun t ht => by
                   dsimp only [scr_k']
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ ht)) with h | h
                   · rw [List.getElem?_set_ne (by omega)]; exact hcp_k t h
                   · subst h
                     have hkt : k.toNat < tmp_r.length := by
                       rw [m6_zext32_toNat] at hk_tmp; exact hk_tmp
                     rw [← hk_sc_eq, List.getElem?_set_self hk_sc, List.getElem?_eq_getElem hkt]
                     exact congrArg some (m6_getElem_congr (m6_zext32_toNat k) _ _),
                 hm_s⟩
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True) (fun _ wk' _ => by c0_hsteps!; exact hstep_k wk' _ hm)
              (fun Jw hJw => by
                c0_hsplit
                · c0_hsplit
                  · have hlk_lt : lk.toNat < 2 * sr.core.cur_vars := by
                      have hlt_k : k.toNat < tmp_r.length := by
                        rw [m6_zext32_toNat] at hk_tmp; exact hk_tmp
                      have h0 := hr_lt k.toNat hk_lt
                      rw [List.getElem?_eq_getElem hlt_k, Option.getD_some] at h0
                      dsimp only [lk]
                      rw [m6_getElem_congr (m6_zext32_toNat k) hk_tmp hlt_k]; exact h0
                    have hlk_wv :
                        (lk.setWidth 64 <<< (1 : Nat) + 1#64).toNat < sr.core.wvec.length := by
                      rw [hdwr.1.core_ok.wvec_len]
                      have hcv_r : sr.core.cur_vars ≤ c.max_vars := hdwr.1.core_ok.cur_vars_le
                      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                        BitVec.toNat_setWidth]
                      simp only [BitVec.toNat_ofNat, Nat.reducePow]
                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                        Nat.mod_eq_of_lt (by omega)]
                      omega
                    c0_hsteps!; exact hJw _ trivial
                  · c0_hsteps!; exact hJw wk trivial
                · c0_hsteps!; exact hJw wk trivial)
          · have hk_eq : k.toNat = tl_r := by
              rw [Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64)] at hc
              change ¬ k.toNat < tl_r at hc; omega
            have h_tl := hdwr.1.core_ok.tmp_len_arr
            let s_ap : FullState := { sr with scratch := { sr.scratch with scratch_buf := scr_k } }
            let sb_ap := s_ap.scratch.scratch_buf
            have hdw_ap : FullDenseInvW c F0 F_cur s_ap := m8_fullDenseInvW_scr hdwr hsck
            have hrp_next : (rp_j + 1 + BitVec.ofNat 64 tl_r).toNat = rp_j.toNat + 1 + tl_r := by
              c0_bound
            have hcp_full : ∀ t < tl_r, scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]? := fun t ht =>
              hcp_k t (by omega)
            have hres_ap : FullResBufOkW F_cur s_ap
                (rp_j + 1 + BitVec.ofNat 64 tl_r).toNat r_off.toNat := by
              rw [hrp_next]
              refine s6a_var_resBuf_append (s := sr) (s' := s_ap) rfl
                (fun idx _ hi2 => hpre_k idx hi2) hres_sr
                (by dsimp only [s_ap]
                    rw [hsz_k, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
                (fun t ht => by dsimp only [s_ap]; rw [hcp_full t ht]; exact hr_lt t ht) ?_ ?_
              · have hmap : ((List.range tl_r).map fun t =>
                    (sb_ap[rp_j.toNat + 1 + t]?.getD 0#32).toNat / 2) =
                    (tmp_r.take tl_r).map (fun x => x.toNat / 2) := by
                  rw [s6a_var_take_div2 (by rw [h_tl]; omega)]
                  exact List.map_congr_left fun t htm => by
                    dsimp only [sb_ap, s_ap]; rw [hcp_full t (List.mem_range.mp htm)]
                rw [hmap]; exact hr_nd
              · have hmap : ((List.range tl_r).map fun t =>
                    (sb_ap[rp_j.toNat + 1 + t]?.getD 0#32).toNat) =
                    (tmp_r.take tl_r).map BitVec.toNat := by
                  rw [s6a_var_take_map (by rw [h_tl]; omega)]
                  exact List.map_congr_left fun t htm => by
                    dsimp only [sb_ap, s_ap]; rw [hcp_full t (List.mem_range.mp htm)]
                rw [hmap]; exact hr_ent
            c0_hsteps!
            exact hJ81
              (rp_j + 1 + BitVec.ofNat 64 tl_r, rcnt_j + 1, wk, fit, j, ()) mk
              ⟨rfl, s_ap, hdw_ap, htmkr, hcvj, harj, halj, hflj,
               by rw [hrp_next]; omega, by rw [hrp_next]; omega, hres_ap,
               fun idx hidx => (hpre_k idx (by omega)).trans (hkeepj idx hidx), hmk⟩
        · intro Lk hLk; c0_hsteps!
          have h_sbl := hdwr.1.scratch_ok.scratch_buf_len
          exact hLk tl_r (west_j, 0#32, ()) _
            ⟨scr_w0, by dsimp only [scr_w0, sr]; rw [List.length_set]; exact h_sbl,
             Nat.zero_le _, by simp,
             fun idx hidx => by dsimp only [scr_w0]; exact List.getElem?_set_ne (by omega),
             by dsimp only [scr_w0]; rw [hlen_w0]; exact List.getElem?_set_self hrp_sc,
             fun _ h => by rw [show (0#32).toNat = 0 from rfl] at h; omega, hm⟩

/-! ## 3. Factored Nested Resolution Loop (`s6a_bve_var_resolve_loop_wp`) -/

theorem s6a_bve_var_resolve_loop_wp (Γ : Env)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 s3 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask : BitVec 32} {r_off lim_cls : BitVec 64}
    {gf rg ext_ok : Bool} {np nn : BitVec 32} {m3 : Mem 64}
    {J52 : Cont [i64, i64, i64, .bool]}
    {e79 : Expr Val Cont [i64]}
    (he79 : e79 = bveILoopAt54B Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask 0#32 0#32 r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn
      false ext_ok lim_cls J52 gf rg s3.scratch.res_sz
      0#64 0#32 0#8 false (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True))
    (hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap ≤ 2 ^ 29)
    (hv_lt : v.toNat < s0.core.cur_vars) (hcv_0 : s0.core.cur_vars ≤ c.max_vars)
    (hneg : neg_off = occ_lim)
    (hocc_le_roff : occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat)
    (hroff_le_sc : r_off.toNat ≤ c.scratch_cap)
    (hpm_lt_roff : ∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hnm_lt_roff : ∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hnp_le : np.toNat ≤ occ_lim.toNat) (hnn_le : nn.toNat ≤ occ_lim.toNat)
    (hdw3 : FullDenseInvW c F0 F_cur s3) (htmk3 : TmkZero s3)
    (hcv3 : s3.core.cur_vars = s0.core.cur_vars)
    (har3 : s3.core.arena = s2.core.arena) (hal3 : s3.core.arena_len = s2.core.arena_len)
    (hfl3 : s3.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hp3 : ∀ i < np.toNat, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?)
    (hn3 : ∀ j < nn.toNat,
      s3.scratch.scratch_buf[neg_off.toNat + j]? = s2.scratch.scratch_buf[neg_off.toNat + j]?)
    (hent_p3 : ∀ i < np.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat)
      (s3.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n3 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat + 1)
      (s3.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32))
    (hm3 : (FullMem c s3 ⋆ R) m3)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJ32 : ∀ (args : Tup Val [i64, i64, i64, .bool]) mf,
      (∃ sf : FullState,
        FullDenseInvW c F0 F_cur sf ∧ TmkZero sf ∧
        sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.arena = s2.core.arena ∧
        sf.core.arena_len = s2.core.arena_len ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        r_off.toNat ≤ args.1.toNat ∧ args.1.toNat ≤ c.scratch_cap ∧
        FullResBufOkW F_cur sf args.1.toNat r_off.toNat ∧
        (∀ k < np.toNat, sf.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
        (∀ k < nn.toNat,
          sf.scratch.scratch_buf[neg_off.toNat + k]? = s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
        (FullMem c sf ⋆ R) mf) →
      J52 args mf) :
    wp Γ Q X e79 m3 := by
  subst he79
  dsimp only [bveILoopAt54B, bveGatesAt52, bveAt52, bvePhaseAt45, bveAt45,
    sL64, sL32, sL8, sLb, sD64, sD32, sD8, sC32, sCb, sT, sE, sB0, sB64, sB32, sBb,
    sB4, sB6, sB5, sK0, sKb, sK4, sK5, sK6]
  have hnp_lt : np.toNat < 2 ^ 32 := np.isLt
  have hnn_lt : nn.toNat < 2 ^ 32 := nn.isLt
  refine wp_loop_group (ts := [i64, i64, i64, .bool, i64, i32])
    (fun rem_i (rp, r_cnt, w_est, fit, res_sz, i, ()) mi =>
      ∃ si : FullState,
        i.toNat ≤ np.toNat ∧ rem_i = np.toNat - i.toNat ∧
        FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
        si.core.cur_vars = s0.core.cur_vars ∧ si.core.arena = s3.core.arena ∧
        si.core.arena_len = s3.core.arena_len ∧ si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        r_off.toNat ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
        FullResBufOkW F_cur si rp.toNat r_off.toNat ∧
        (∀ k < r_off.toNat, si.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
        (FullMem c si ⋆ R) mi)
    ?_ ?_
  · rintro Li rem_i ⟨rp, r_cnt, w_est, fit, res_sz, i, ⟨⟩⟩ mi hLi
      ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi, hres_i, hkeep_i, hmi⟩
    refine wp_join_state (ts := []) (α := Unit) (fun _ => ()) (fun _ mj => mj = mi)
      (fun _ _ mj hmj => by
        rcases hmj with rfl; c0_hsteps!
        let sf1 : FullState := { si with scratch := { si.scratch with res_sz := res_sz } }
        have hdw_sf1 := m6_fullDenseInvW_with_scratch hdwi (sc' := sf1.scratch)
          { hdwi.1.scratch_ok with } rfl rfl
        have hres_sf1 : FullResBufOkW F_cur sf1 rp.toNat r_off.toNat :=
          s6a_var_resBuf_mono (s := si) (s' := sf1) rfl (fun _ _ _ => rfl) hres_i
        exact hJ32 (rp, r_cnt, w_est, fit, ()) _
          ⟨sf1, hdw_sf1, htmki, hcvi, hari.trans har3, hali.trans hal3, hfli, hrp_lo, hrp_hi,
           hres_sf1, fun k hk => (hkeep_i k (by omega)).trans (hp3 k hk),
           fun k hk => (hkeep_i (neg_off.toNat + k) (by rw [hneg]; omega)).trans (hn3 k hk), hm⟩)
      ?_
    intro Jexit hJexit
    c0_hsplit
    · have hi_lt : i.toNat < np.toNat := hc
      c0_hsplit
      · have hi_mask_sc : ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat <
            si.scratch.scratch_buf.length := by
          rw [hdwi.1.scratch_ok.scratch_buf_len]
          exact Nat.lt_of_lt_of_le (hpm_lt_roff i (by omega)) hroff_le_sc
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i64, i64, i64, .bool, i64, i32])
          (lpTs := [i64, i64, i64, i64, i32])
          (fun (rp_b, rcnt_b, west_b, fit_b, rsz_b, _ib, ()) mb =>
            ∃ sb : FullState,
              FullDenseInvW c F0 F_cur sb ∧ TmkZero sb ∧ sb.core.cur_vars = s0.core.cur_vars ∧
              sb.core.arena = s3.core.arena ∧ sb.core.arena_len = s3.core.arena_len ∧
              sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
              r_off.toNat ≤ rp_b.toNat ∧ rp_b.toNat ≤ c.scratch_cap ∧
              FullResBufOkW F_cur sb rp_b.toNat r_off.toNat ∧
              (∀ k < r_off.toNat, sb.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
              (FullMem c sb ⋆ R) mb)
          (fun rem_j (rp_j, rcnt_j, west_j, rsz_j, j, ()) mj =>
            ∃ sj : FullState,
              j.toNat ≤ nn.toNat ∧ rem_j = nn.toNat - j.toNat ∧
              FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
              sj.core.arena = s3.core.arena ∧ sj.core.arena_len = s3.core.arena_len ∧
              sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
              r_off.toNat ≤ rp_j.toNat ∧ rp_j.toNat ≤ c.scratch_cap ∧
              FullResBufOkW F_cur sj rp_j.toNat r_off.toNat ∧
              (∀ k < r_off.toNat, sj.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
              (FullMem c sj ⋆ R) mj)
          ?_ ?_ ?_
        · rintro _ ⟨rp_b, rcnt_b, west_b, fit_b, rsz_b, _ib, ⟨⟩⟩ mb
            ⟨sb, hdwb, htmkb, hcvb, harb, halb, hflb, hrpb_lo, hrpb_hi, hresb, hkeepb, hmb⟩
          c0_hsteps!
          exact hLi (np.toNat - (i + 1#32).toNat) (rp_b, rcnt_b, west_b, fit_b, rsz_b, i + 1#32, ())
            mb (by omega) ⟨sb, by omega, rfl, hdwb, htmkb, hcvb, harb, halb, hflb,
              hrpb_lo, hrpb_hi, hresb, hkeepb, hmb⟩
        · rintro Bj Lj rem_j ⟨rp_j, rcnt_j, west_j, rsz_j, j, ⟨⟩⟩ mj hBj hLj
            ⟨sj, hj_le, rfl, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
              hresj, hkeepj, hmj⟩
          c0_hsplit
          · have hj_lt : j.toNat < nn.toNat := hc
            c0_hsplit
            · have hj_mask_sc : ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat <
                  sj.scratch.scratch_buf.length := by
                rw [hdwj.1.scratch_ok.scratch_buf_len]
                exact Nat.lt_of_lt_of_le (hnm_lt_roff j (by omega)) hroff_le_sc
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun np_b => (np_b, ()))
                (fun _ => True) ?_ ?_
              · rintro _ np_b _; c0_hsteps_nogrp
                refine wp_join_state (ts := [i64, i64, i64, .bool, i64, i32])
                  (α :=
                    BitVec 64 × BitVec 64 × BitVec 64 × Bool × BitVec 64 × BitVec 32 × FullState)
                  (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ()))
                  (fun x mk =>
                    let sk := x.2.2.2.2.2.2
                    x.2.2.2.2.2.1 = j ∧ FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
                    sk.core.cur_vars = s0.core.cur_vars ∧ sk.core.arena = s3.core.arena ∧
                    sk.core.arena_len = s3.core.arena_len ∧
                    sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    r_off.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ c.scratch_cap ∧
                    FullResBufOkW F_cur sk x.1.toNat r_off.toNat ∧
                    (∀ k < r_off.toNat, sk.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
                    (FullMem c sk ⋆ R) mk) ?_ ?_
                · rintro _ ⟨rp_k, rcnt_k, west_k, fit_k, rsz_k, jk, sk⟩ mk
                    ⟨hjk, hdwk, htmkk, hcvk, hark, halk, hflk, hrpk_lo, hrpk_hi, hresk, hkeepk, hmk⟩
                  dsimp only at hjk; c0_hsteps!
                  exact hLj (nn.toNat - (jk + 1#32).toNat)
                    (rp_k, rcnt_k, west_k, rsz_k, jk + 1#32, ()) mk (by rw [hjk, hj1]; omega)
                    ⟨sk, by rw [hjk, hj1]; omega, rfl, hdwk, htmkk, hcvk, hark, halk, hflk,
                     hrpk_lo, hrpk_hi, hresk, hkeepk, hmk⟩
                · intro Jj hJj
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64, i64, i64, .bool, i32])
                      (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × BitVec 32 × FullState)
                      (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ()))
                      (fun x mk =>
                        let sk := x.2.2.2.2.2
                        x.2.2.2.2.1 = j ∧ FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
                        sk.core.cur_vars = s0.core.cur_vars ∧ sk.core.arena = s3.core.arena ∧
                        sk.core.arena_len = s3.core.arena_len ∧
                        sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                        r_off.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ c.scratch_cap ∧
                        FullResBufOkW F_cur sk x.1.toNat r_off.toNat ∧
                        (∀ k < r_off.toNat,
                          sk.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
                        (FullMem c sk ⋆ R) mk) ?_ ?_
                    · rintro _ ⟨rp_k, rcnt_k, west_k, fit_k, jk, sk⟩ mk
                        ⟨hjk, hdwk, htmkk, hcvk, hark, halk, hflk, hrpk_lo, hrpk_hi, hresk,
                          hkeepk, hmk⟩
                      c0_hsteps!
                      exact hJj (rp_k, rcnt_k, west_k, fit_k, rsz_j + 1#64, jk, sk) mk
                        ⟨hjk, hdwk, htmkk, hcvk, hark, halk, hflk, hrpk_lo, hrpk_hi,
                         hresk, hkeepk, hmk⟩
                    · intro J81 hJ81
                      have hi_scj : (i.setWidth 64).toNat < sj.scratch.scratch_buf.length := by
                        rw [hdwj.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                      have hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ r_off.toNat := by
                        rw [hneg]; exact hocc_le_roff
                      have hneg_j_eq : ((neg_off + j).setWidth 64).toNat =
                          neg_off.toNat + j.toNat := by
                        rw [m6_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                      have hj_scj : ((neg_off + j).setWidth 64).toNat <
                          sj.scratch.scratch_buf.length := by
                        rw [hdwj.1.scratch_ok.scratch_buf_len, hneg_j_eq]; omega
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hResPair _ _ _ _ ?_)
                      dsimp only [vals, Arg.val]
                      refine ⟨c, F0, F_cur, sj, R, rfl, hdwj, by omega, ?_, ?_, hmj, ?_⟩
                      · have hget : sj.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_scj =
                            s3.scratch.scratch_buf[i.toNat]?.getD 0#32 := by
                          have h0 := hkeepj i.toNat (by omega)
                          rw [← h0, List.getElem?_eq_getElem
                            (by rw [m6_zext32_toNat] at hi_scj; exact hi_scj), Option.getD_some]
                          exact m6_getElem_congr (m6_zext32_toNat i) _ _
                        rw [hget]
                        exact m8_bveEntry_congr_core (hent_p3 i.toNat hi_lt)
                          (hcvj.trans hcv3.symm) harj halj
                      · have hget : sj.scratch.scratch_buf[((neg_off + j).setWidth 64).toNat]'
                            hj_scj =
                            s3.scratch.scratch_buf[neg_off.toNat + j.toNat]?.getD 0#32 := by
                          have h0 := hkeepj (neg_off.toNat + j.toNat) (by rw [hneg]; omega)
                          rw [← h0, List.getElem?_eq_getElem (by rw [← hneg_j_eq]; exact hj_scj),
                            Option.getD_some]
                          exact m6_getElem_congr hneg_j_eq _ _
                        rw [hget]
                        exact m8_bveEntry_congr_core (hent_n3 j.toNat hj_lt)
                          (hcvj.trans hcv3.symm) harj halj
                      · intro ok_r lm_r tmp_r tl_r m_r; dsimp only
                        intro hdwr htl_le hres_ok hm_r
                        let sr : FullState := { sj with core := { sj.core with
                          lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
                        have hres_sr : FullResBufOkW F_cur sr rp_j.toNat r_off.toNat :=
                          s6a_var_resBuf_mono (s := sj) (s' := sr) rfl (fun _ _ _ => rfl) hresj
                        c0_hsplit
                        · obtain ⟨hr_lt, hr_nd, hr_ent⟩ := hres_ok (by simpa using hc)
                          have htl_cv : tl_r ≤ c.max_vars := by
                            have := hdwr.1.core_ok.cur_vars_le; omega
                          c0_hsplit
                          · have htl0 : tl_r = 0 := by
                              have h := congrArg BitVec.toNat hc
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
                              simpa using h
                            have htake0 : (tmp_r.take tl_r).map BitVec.toNat = [] := by simp [htl0]
                            rw [htake0] at hr_ent
                            have huns : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hr_ent
                            c0_hsteps!
                            let sr1 : FullState :=
                              { sr with scratch := { sr.scratch with res_sz := rsz_j + 1#64 } }
                            have hdw_sr1 := m6_fullDenseInvW_with_scratch hdwr (sc' := sr1.scratch)
                              { hdwr.1.scratch_ok with } rfl rfl
                            let sr2 : FullState :=
                              { sr1 with core := { sr1.core with inconsistent := 1#64 } }
                            have hdw_sr2 := m6_fullDenseInvW_set_inc hdw_sr1 huns
                            exact hQ 20#64 sr2 _ hdw_sr2.toDense htmkj
                              (by dsimp only [sr2, sr1, sr]; omega) hflj (Or.inr (Or.inr rfl))
                              (fun _ => hdw_sr2.2.1.ext_sound.2 huns) hm
                          · clear hc
                            c0_hsplit
                            · have htl1 : tl_r = 1 := by
                                have h := congrArg BitVec.toNat hc
                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
                                simpa using h
                              exact s6a_bve_var_rlen1_wp Γ hAssign hcv_0 hmx hj_lt
                                hj1 hcvj harj halj hflj hrpj_lo hrpj_hi hkeepj hdwr htmkj
                                hres_sr hm_r htl_cv htl1 hr_ent hQ
                                (fun r' args' mj' hr' hex => hLj r' args' mj' hr' hex)
                            · refine s6a_bve_var_rlen2_wp Γ (c := c) (F0 := F0) (F_cur := F_cur)
                                (s0 := s0) (s3 := s3) (sj := sj) (R := R) (fit := fit) hmx hsc
                                hcvj harj halj hflj hrpj_lo hrpj_hi hkeepj hdwr htmkj
                                hres_sr hm_r htl_cv hr_lt hr_nd hr_ent ?_ ?_
                              · intro args mb ⟨sb, hsb⟩
                                exact hBj args mb ⟨sb, hsb⟩
                              · intro args mk ⟨hjk, sk, hsk⟩
                                exact hJ81 (args.1, args.2.1, args.2.2.1, args.2.2.2.1,
                                  args.2.2.2.2.1, sk) mk ⟨hjk, hsk⟩
                        · c0_hsteps!
                          exact hJ81 (rp_j, rcnt_j, west_j, fit, j, sr) m_r
                            ⟨rfl, hdwr, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                             hres_sr, hkeepj, hm_r⟩
                  · c0_hsteps!
                    exact hJj (rp_j, rcnt_j, west_j, fit, rsz_j, j, sj) mj
                      ⟨rfl, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                       hresj, hkeepj, hmj⟩
              · intro Jn hJn
                c0_hsplit
                · refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                    (fun _ => True)
                    (fun _ _ _ => by c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial))
                    (fun J80 hJ80 => by
                      c0_hsplit
                      · refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                          (fun _ => True) (fun _ _ _ => by c0_hsteps!; exact hJ80 _ trivial)
                          (fun J81p hJ81p => by
                            c0_hsplit
                            · c0_hsteps!; exact hJ81p true trivial
                            · c0_hsplit
                              · c0_hsteps!; exact hJ81p true trivial
                              · c0_hsteps!; exact hJ81p false trivial)
                      · c0_hsteps!; exact hJ80 _ trivial)
                · c0_hsteps!; exact hJn true trivial
            · c0_hsteps!
              exact hBj (rp_j, rcnt_j, west_j, fit, rsz_j, j, ()) mj
                ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi, hresj, hkeepj, hmj⟩
          · c0_hsteps!
            exact hBj (rp_j, rcnt_j, west_j, fit, rsz_j, j, ()) mj
              ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi, hresj, hkeepj, hmj⟩
        · intro _ Lj _ hLj; c0_hsteps!
          exact hLj nn.toNat (rp, r_cnt, w_est, res_sz, 0#32, ()) mi
            ⟨si, Nat.zero_le _, by simp, hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi,
             hres_i, hkeep_i, hmi⟩
      · c0_hsteps!; exact hJexit () mi rfl
    · c0_hsteps!; exact hJexit () mi rfl
  · intro Li hLi; c0_hsteps!
    exact hLi np.toNat (r_off, 0#64, 0#64, _, s3.scratch.res_sz, 0#32, ()) m3
      ⟨s3, Nat.zero_le _, by simp, hdw3, htmk3, hcv3, rfl, rfl, hfl3,
       Nat.le_refl _, hroff_le_sc, .nil, fun _ _ => rfl, hm3⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
