/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Parse
public import LeanQbe.T.Examples.Arisca.Proof.Arena
public import LeanQbe.T.Examples.Arisca.Proof.Arith
public import LeanQbe.T.Examples.Arisca.Proof.Sem
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import LeanQbe.T.Logic.Arith

/-!
# ARiSCA Parser WP Specifications & Proofs (`Arisca.Proof.ParseBase`)

`XPost`-polymorphic (`noExit = true`) WP specifications and proofs for all `5` functions of
`LeanQbe.T.Examples.Arisca.Src.Parse`:
- `ar_pnum` (`arPnumSpec` / `ar_pnum_wp`)
- `ar_pch` (`arPchSpec` / `ar_pch_wp`)
- `ar_pvarint` (`arPvarintSpec` / `ar_pvarint_wp`)
- `ar_parse_aig` (`arParseAigSpec` / `ar_parse_aig_wp`)
- `ar_parse_art_header_and_tables` (`arParseArtHeaderAndTablesSpec` /
  `ar_parse_art_header_and_tables_wp`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open LeanQbe.T.Examples.Arisca.Src.Parse

/-! ## 1. Specs & Geometry Definitions (`@[expose]`) -/

@[expose] public section

/-- Total byte offset at the end of the `18` static/AIG/table/scratch slabs (`776 + ...`). -/
def tablesEndTop (A O nNets nIn nOut : Nat) : Nat :=
  let t0 := 776 + align8 (4 * A) + align8 (4 * A) + align8 (4 * O)
  let t1 := t0 + align8 (4 * nNets)
  let t2 := t1 + align8 (4 * nNets)
  let t3 := t2 + align8 (4 * nNets)
  let t4 := t3 + align8 (4 * nNets)
  let t5 := t4 + align8 nNets
  let t6 := t5 + align8 (4 * nIn)
  let t7 := t6 + align8 (4 * nOut)
  t7 + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd +
    8 * 128 + align8 (4 * 85) + 8 * 16 + 8 * 16

/-- Exact contiguous pointer geometry for `aigArraysMem`, `netTablesMem`, and `gateScratchMem`. -/
structure TablesGeom (s : ArCtxState) (A O nNets nIn nOut top0 : Nat) : Prop where
  top_eq : top0 = tablesEndTop A O nNets nIn nOut
  rhs0_eq : s.rhs0 = s.w + 776#64
  rhs1_eq : s.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * A))
  olit_eq : s.olit = s.w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A))
  bind_eq :
    s.bind = s.w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A) + align8 (4 * O))
  rule_off_eq : s.rule_off = s.bind + BitVec.ofNat 64 (align8 (4 * nNets))
  rule_n_eq : s.rule_n = s.rule_off + BitVec.ofNat 64 (align8 (4 * nNets))
  partner_eq : s.partner = s.rule_n + BitVec.ofNat 64 (align8 (4 * nNets))
  flipped_eq : s.flipped = s.partner + BitVec.ofNat 64 (align8 (4 * nNets))
  in_net_eq : s.in_net = s.flipped + BitVec.ofNat 64 (align8 nNets)
  out_ref_eq : s.out_ref = s.in_net + BitVec.ofNat 64 (align8 (4 * nIn))
  stk_n_eq : s.stk_n = s.out_ref + BitVec.ofNat 64 (align8 (4 * nOut))
  stk_p_eq : s.stk_p = s.stk_n + BitVec.ofNat 64 (4 * arTTStk)
  memo_n_eq : s.memo_n = s.stk_p + BitVec.ofNat 64 (4 * arTTStk)
  memo_v_eq : s.memo_v = s.memo_n + BitVec.ofNat 64 (4 * arTTMaxAnd)
  dense_eq : s.dense = s.memo_v + BitVec.ofNat 64 (8 * arTTMaxAnd)
  gsy_eq : s.gsy = s.dense + BitVec.ofNat 64 (8 * 128)
  gcl_eq : s.gcl = s.gsy + BitVec.ofNat 64 (align8 (4 * 85))
  gch_eq : s.gch = s.gcl + BitVec.ofNat 64 (8 * 16)

/-- WP specification for `ar_pnum(b, n, pos)`. -/
def arPnumSpec : Spec [i64, i64, i64] [.bool, i64, i32] :=
  fun ⟨b, n, pos, ⟨⟩⟩ m Q _ =>
    ∃ (bs : List UInt8) (R : Mem 64 → Prop),
      n.toNat ≤ bs.length ∧
      bs.length ≤ 2 ^ 64 ∧
      (bytes b bs ⋆ R) m ∧
      (∀ (ok : Bool) (p' : BitVec 64) (v : BitVec 32),
        (ok = true →
          pos.toNat < p'.toNat ∧ p'.toNat ≤ n.toNat ∧
          (p'.toNat < n.toNat → isDigit (bs.getD p'.toNat 0).toNat = false) ∧
          (∀ (term : Nat) {β : Type} (fail : β) (k : Nat → List Nat → β),
            p'.toNat < n.toNat → (bs.getD p'.toNat 0).toNat = term →
            pnum term fail ((toNatBytes bs).drop pos.toNat) k =
              k v.toNat ((toNatBytes bs).drop (p'.toNat + 1)))) →
        Q (ok, p', v, ⟨⟩) m)

/-- WP specification for `ar_pch(b, n, pos, c)`. -/
def arPchSpec : Spec [i64, i64, i64, i8] [.bool, i64] :=
  fun ⟨b, n, pos, c, ⟨⟩⟩ m Q _ =>
    ∃ (bs : List UInt8) (R : Mem 64 → Prop),
      n.toNat ≤ bs.length ∧
      bs.length ≤ 2 ^ 64 ∧
      (bytes b bs ⋆ R) m ∧
      (∀ (ok : Bool) (p' : BitVec 64),
        ((pos.toNat < n.toNat ∧ (bs.getD pos.toNat 0).toNat = c.toNat →
          ok = true ∧ p' = pos + 1 ∧ p'.toNat = pos.toNat + 1 ∧ pos.toNat + 1 ≤ n.toNat) ∧
         (¬ (pos.toNat < n.toNat ∧ (bs.getD pos.toNat 0).toNat = c.toNat) →
          ok = false ∧ p' = pos)) →
        Q (ok, p', ⟨⟩) m)

/-- WP specification for `ar_pvarint(b, n, pos)`. -/
def arPvarintSpec : Spec [i64, i64, i64] [.bool, i64, i32] :=
  fun ⟨b, n, pos, ⟨⟩⟩ m Q _ =>
    ∃ (bs : List UInt8) (R : Mem 64 → Prop),
      n.toNat ≤ bs.length ∧
      bs.length ≤ 2 ^ 64 ∧
      (bytes b bs ⋆ R) m ∧
      (∀ (ok : Bool) (p' : BitVec 64) (v : BitVec 32),
        (ok = true →
          pos.toNat < p'.toNat ∧ p'.toNat ≤ n.toNat ∧
          (∀ {β : Type} (fail : β) (k : Nat → List Nat → β),
            pvar fail ((toNatBytes bs).drop pos.toNat) k =
              k v.toNat ((toNatBytes bs).drop p'.toNat))) →
        Q (ok, p', v, ⟨⟩) m)

/-- WP specification for `ar_parse_aig(cx, b, n)`. -/
def arParseAigSpec : Spec [i64, i64, i64] [.bool] :=
  fun ⟨cx, b, n, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (aigBytes : List UInt8) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧
      s.top = 776#64 ∧
      776 ≤ s.wlen.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      n.toNat = aigBytes.length ∧
      (arCtxMem cx s ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
        bytes b aigBytes ⋆ R) m ∧
      (∀ (ok : Bool) (m' : Mem 64),
        ((ok = false ∧ ∃ s' : ArCtxState,
            s'.w = s.w ∧ s'.wlen = s.wlen ∧
            s'.art = s.art ∧ s'.nw = s.nw ∧ s'.pos = s.pos ∧
            s'.rs_n = s.rs_n ∧ s'.rs_ptop = s.rs_ptop ∧
            s'.rs_cap = s.rs_cap ∧ s'.rs_pcap = s.rs_pcap ∧
            (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
              bytes b aigBytes ⋆ R) m') ∨
         (ok = true ∧ ∃ (g : Aig) (rhs0 rhs1 olit : List (BitVec 32)) (s' : ArCtxState),
            parseAig (toNatBytes aigBytes) = some g ∧
            AigRep g rhs0 rhs1 olit ∧
            g.M ≤ 0x3FFFFFF0 ∧
            s'.w = s.w ∧ s'.wlen = s.wlen ∧
            s'.art = s.art ∧ s'.nw = s.nw ∧ s'.pos = s.pos ∧
            s'.rs_n = s.rs_n ∧ s'.rs_ptop = s.rs_ptop ∧
            s'.rs_cap = s.rs_cap ∧ s'.rs_pcap = s.rs_pcap ∧
            s'.ptop = s.ptop ∧ s'.tn = s.tn ∧ s'.qn = s.qn ∧
            s'.pc = s.pc ∧ s'.tc = s.tc ∧ s'.cur_nr = s.cur_nr ∧
            s'.M.toNat = g.M ∧ s'.I.toNat = g.I ∧
            s'.A.toNat = g.ands.length ∧ s'.O.toNat = g.outs.length ∧
            s'.rhs0 = s.w + 776#64 ∧
            s'.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * g.ands.length)) ∧
            s'.olit = s.w + BitVec.ofNat 64
              (776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length)) ∧
            s'.top.toNat = 776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length) +
              4 * g.outs.length ∧
            s'.top.toNat ≤ s'.wlen.toNat ∧
            (arCtxMem cx s' ⋆
              arrayPad i32 s'.rhs0 rhs0 ⋆
              arrayPad i32 s'.rhs1 rhs1 ⋆
              array (t := i32) s'.olit olit ⋆
              region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆
              bytes b aigBytes ⋆ R) m')) →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_parse_art_header_and_tables(cx, art, art_len)`. -/
def arParseArtHeaderAndTablesSpec : Spec [i64, i64, i64] [.bool] :=
  fun ⟨cx, art, art_len, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (g : Aig) (rhs0 rhs1 olit : List (BitVec 32))
      (artBytes : List UInt8) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      s.top.toNat = 776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length) +
        4 * g.outs.length ∧
      s.top.toNat ≤ s.wlen.toNat ∧
      s.rhs0 = s.w + 776#64 ∧
      s.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * g.ands.length)) ∧
      s.olit = s.w + BitVec.ofNat 64
        (776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length)) ∧
      AigRep g rhs0 rhs1 olit ∧
      g.M ≤ 0x3FFFFFF0 ∧
      s.M.toNat = g.M ∧ s.I.toNat = g.I ∧
      s.A.toNat = g.ands.length ∧ s.O.toNat = g.outs.length ∧
      s.rs_n = 0#32 ∧ s.rs_ptop = 0#64 ∧ s.rs_cap = 0#32 ∧ s.rs_pcap = 0#64 ∧
      art_len.toNat = artBytes.length ∧
      art.toNat + artBytes.length < 2 ^ 64 ∧
      (arCtxMem cx s ⋆
        arrayPad i32 s.rhs0 rhs0 ⋆
        arrayPad i32 s.rhs1 rhs1 ⋆
        array (t := i32) s.olit olit ⋆
        region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆
        bytes art artBytes ⋆ R) m ∧
      (∀ (ok : Bool) (m' : Mem 64),
        ((ok = false ∧ ∃ s' : ArCtxState,
            s'.w = s.w ∧ s'.wlen = s.wlen ∧
            (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
              bytes art artBytes ⋆ R) m') ∨
         (ok = true ∧ ∃ (s' : ArCtxState)
            (bindArr ruleOff ruleN partnerArr : List (BitVec 32))
            (flippedArr : List (BitVec 8))
            (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
            (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32))
            (gcl gch : List (BitVec 64)),
            s'.w = s.w ∧ s'.wlen = s.wlen ∧
            s'.art = art ∧ 4 * s'.nw.toNat = artBytes.length ∧
            s'.pos.toNat = 10 + s'.n_nets.toNat + s'.n_in.toNat + s'.n_out.toNat ∧
            s'.pos.toNat ≤ s'.nw.toNat ∧
            s'.M = s.M ∧ s'.I = s.I ∧ s'.A = s.A ∧ s'.O = s.O ∧
            s'.n_nets.toNat ≤ 0x3FFFFFFF ∧
            s'.spec = BitVec.ofNat 32 (wordAt artBytes 2) ∧
            (s'.spec = 0#32 ∨ s'.spec = 1#32 ∨ s'.spec = 2#32) ∧
            s'.rs_n = 0#32 ∧ s'.rs_ptop = 0#64 ∧ s'.rs_cap = 0#32 ∧ s'.rs_pcap = 0#64 ∧
            s'.ptop = s.ptop ∧ s'.tn = s.tn ∧ s'.qn = s.qn ∧
            s'.pc = s.pc ∧ s'.tc = s.tc ∧ s'.cur_nr = s.cur_nr ∧
            s'.top.toNat = tablesEndTop g.ands.length g.outs.length
              s'.n_nets.toNat s'.n_in.toNat s'.n_out.toNat ∧
            s'.top.toNat ≤ s'.wlen.toNat ∧
            TablesGeom s' g.ands.length g.outs.length
              s'.n_nets.toNat s'.n_in.toNat s'.n_out.toNat s'.top.toNat ∧
            MasksOk s'.modW s'.mlo s'.mhi ∧
            BindRep s' g bindArr inNetArr outRefArr ∧
            bindArr.length = s'.n_nets.toNat ∧
            ruleOff.length = s'.n_nets.toNat ∧
            ruleN.length = s'.n_nets.toNat ∧
            partnerArr.length = s'.n_nets.toNat ∧
            flippedArr.length = s'.n_nets.toNat ∧
            inNetArr.length = s'.n_in.toNat ∧
            outRefArr.length = s'.n_out.toNat ∧
            stkN.length = arTTStk ∧ stkP.length = arTTStk ∧
            memoN.length = arTTMaxAnd ∧ memoV.length = arTTMaxAnd ∧
            dense.length = 128 ∧ gsy.length = 85 ∧ gcl.length = 16 ∧ gch.length = 16 ∧
            (∀ i < s'.n_nets.toNat, flippedArr.getD i 0#8 = 0#8) ∧
            (∀ σ : Nat → Bool, PartnerRep σ s'.n_nets.toNat partnerArr ∧
              RulesRep s'.modW σ s' ruleOff ruleN [] [] [] []) ∧
            (arCtxMem cx s' ⋆
              aigArraysMem s' rhs0 rhs1 olit ⋆
              netTablesMem s' bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
              gateScratchMem s' stkN stkP memoN memoV dense gsy gcl gch ⋆
              region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆
              bytes art artBytes ⋆ R) m')) →
        Q (ok, ⟨⟩) m')

end

/-! ## 2. Pure Parser & Memory Collapse Helpers -/

public section

private theorem toNatBytes_length (bs : List UInt8) : (toNatBytes bs).length = bs.length := by
  simp [toNatBytes]

theorem drop_toNatBytes_cons {bs : List UInt8} {i : Nat} (hi : i < bs.length) :
    (toNatBytes bs).drop i = bs[i].toNat :: (toNatBytes bs).drop (i + 1) := by
  simp only [toNatBytes, ← List.map_drop, List.drop_eq_getElem_cons hi, List.map_cons]

private theorem isDigit_iff (b : Nat) : isDigit b = true ↔ 48 ≤ b ∧ b ≤ 57 := by
  unfold isDigit
  cases h1 : Nat.ble 48 b <;> cases h2 : Nat.ble b 57
  · have hn1 : ¬ 48 ≤ b := fun h => by rw [Nat.ble_eq.mpr h] at h1; cases h1
    simp [hn1]
  · have hn1 : ¬ 48 ≤ b := fun h => by rw [Nat.ble_eq.mpr h] at h1; cases h1
    simp [hn1]
  · have hn2 : ¬ b ≤ 57 := fun h => by rw [Nat.ble_eq.mpr h] at h2; cases h2
    simp [hn2]
  · simp [Nat.ble_eq.mp h1, Nat.ble_eq.mp h2]

private theorem isDigit_false_iff (b : Nat) : isDigit b = false ↔ b < 48 ∨ 57 < b := by
  have h := isDigit_iff b
  cases hd : isDigit b <;> simp [hd] at h ⊢ <;> omega

private theorem pnum_eq_pnumGo {term : Nat} {β : Type} {fail : β} {k : Nat → List Nat → β}
    {bs : List UInt8} {pos : Nat} (hpos : pos < bs.length)
    (hdig : isDigit bs[pos].toNat = true) :
    pnum term fail ((toNatBytes bs).drop pos) k =
      pnumGo term fail k ((toNatBytes bs).drop pos) 0 := by
  rw [drop_toNatBytes_cons hpos]
  unfold pnum rd
  simp only [hdig, ← drop_toNatBytes_cons hpos]

private theorem pnumGo_step_digit {term : Nat} {β : Type} {fail : β} {k : Nat → List Nat → β}
    {bs : List UInt8} {p : Nat} (hp : p < bs.length) (hdig : isDigit bs[p].toNat = true)
    (acc : Nat) :
    pnumGo term fail k ((toNatBytes bs).drop p) acc =
      pnumGo term fail k ((toNatBytes bs).drop (p + 1)) (acc * 10 + (bs[p].toNat - 48)) := by
  rw [drop_toNatBytes_cons hp]
  unfold pnumGo
  simp only [hdig]
  rfl

private theorem pnumGo_stop_term {term : Nat} {β : Type} {fail : β} {k : Nat → List Nat → β}
    {bs : List UInt8} {p : Nat} (hp : p < bs.length) (hnd : isDigit bs[p].toNat = false)
    (hterm : bs[p].toNat = term) (acc : Nat) :
    pnumGo term fail k ((toNatBytes bs).drop p) acc = k acc ((toNatBytes bs).drop (p + 1)) := by
  rw [drop_toNatBytes_cons hp]
  unfold pnumGo
  have hbeq : Nat.beq bs[p].toNat term = true := Nat.beq_eq.mpr hterm
  simp only [hnd, hbeq]

private theorem pvar_eq_pvarGo {β : Type} {fail : β} {k : Nat → List Nat → β} (bs : List Nat) :
    pvar fail bs k = pvarGo fail k bs 0 0 := rfl

private theorem pvarGo_step_cont {β : Type} {fail : β} {k : Nat → List Nat → β}
    {bs : List UInt8} {p : Nat} (hp : p < bs.length) (hc : 128 ≤ bs[p].toNat) (acc sh : Nat) :
    pvarGo fail k ((toNatBytes bs).drop p) acc sh =
      pvarGo fail k ((toNatBytes bs).drop (p + 1))
        (Nat.lor acc (Nat.shiftLeft (Nat.land bs[p].toNat 127) sh)) (sh + 7) := by
  rw [drop_toNatBytes_cons hp]
  unfold pvarGo
  have hble : Nat.ble 128 bs[p].toNat = true := Nat.ble_eq.mpr hc
  simp only [hble]

private theorem pvarGo_step_done {β : Type} {fail : β} {k : Nat → List Nat → β}
    {bs : List UInt8} {p : Nat} (hp : p < bs.length) (hc : bs[p].toNat < 128) (acc sh : Nat) :
    pvarGo fail k ((toNatBytes bs).drop p) acc sh =
      k (Nat.lor acc (Nat.shiftLeft (Nat.land bs[p].toNat 127) sh))
        ((toNatBytes bs).drop (p + 1)) := by
  rw [drop_toNatBytes_cons hp]
  unfold pvarGo
  have hble : Nat.ble 128 bs[p].toNat = false := by
    cases hb : Nat.ble 128 bs[p].toNat
    · rfl
    · have := Nat.ble_eq.mp hb; omega
  simp only [hble]

private theorem nat_lor_shl_disj (acc v sh : Nat) (hacc : acc < 2 ^ sh) :
    Nat.lor acc (Nat.shiftLeft v sh) = acc + v * 2 ^ sh := by
  show acc ||| (v <<< sh) = acc + v * 2 ^ sh
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  by_cases hi : i < sh
  · have hpow : 2 ^ sh = (2 * 2 ^ (sh - i - 1)) * 2 ^ i := by
      have h1 : 2 * 2 ^ (sh - i - 1) = 2 ^ (sh - i) := by
        rw [← Nat.pow_succ', Nat.succ_eq_add_one, show sh - i - 1 + 1 = sh - i by omega]
      rw [h1, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hmul : v * 2 ^ sh = (2 * (v * 2 ^ (sh - i - 1))) * 2 ^ i := by
      rw [hpow]; simp only [Nat.mul_assoc, Nat.mul_left_comm]
    have hpowPos : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have h0 : (v * 2 ^ sh).testBit i = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hmul, Nat.mul_div_left _ hpowPos,
        Nat.and_comm 1, Nat.and_one_is_mod, Nat.mul_mod_right]; decide
    have ha1 : (acc + v * 2 ^ sh) / 2 ^ i % 2 = acc / 2 ^ i % 2 := by
      rw [hmul, Nat.add_mul_div_right _ _ hpowPos, Nat.mul_comm 2, Nat.add_mul_mod_self_right]
    rw [h0, Bool.or_false]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, ha1]
  · have hge : sh ≤ i := by omega
    have hpow : 2 ^ i = 2 ^ sh * 2 ^ (i - sh) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    have ha0 : acc.testBit i = false := by
      have hlti : acc < 2 ^ i := Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) hge)
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlti]; decide
    have hv1 : (acc + v * 2 ^ sh) / 2 ^ i = v / 2 ^ (i - sh) := by
      rw [hpow, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hacc, Nat.zero_add]
    have hv2 : (v * 2 ^ sh) / 2 ^ i = v / 2 ^ (i - sh) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_left v (Nat.pow_pos (by decide))]
    rw [ha0, Bool.false_or]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [hv1, hv2]

theorem poutsGo_succ {β : Type} (fail : β) (k : List Nat → List Nat → β)
    (rem : Nat) (acc bs : List Nat) :
    poutsGo fail k (rem + 1) acc bs =
      pnum 10 fail bs (fun o bs => poutsGo fail k rem (o :: acc) bs) := rfl

theorem pandsGo_succ {β : Type} (fail : β) (k : List (Nat × Nat) → β)
    (rem lhs : Nat) (acc : List (Nat × Nat)) (bs : List Nat) :
    pandsGo fail k (rem + 1) lhs acc bs =
      pvar fail bs fun d0 bs => pvar fail bs fun d1 bs =>
        Bool.rec fail
          (Bool.rec fail
            (pandsGo fail k rem (lhs + 2) ((lhs - d0, (lhs - d0) - d1) :: acc) bs)
            (Nat.ble d1 (lhs - d0)))
          (Bool.rec (Nat.ble d0 lhs) false (Nat.beq d0 0)) := rfl

theorem getD_reverse_append {α : Type} (d : α) (acc : List α) (x : α) (idx : Nat) :
    ((x :: acc).reverse.getD idx d) =
      if idx < acc.length then acc.reverse.getD idx d else if idx = acc.length then x else d := by
  rw [List.reverse_cons]
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : idx < acc.length
  · have hr : idx < acc.reverse.length := by simpa using hlt
    simp [hlt, List.getElem?_append_left hr]
  · by_cases heq : idx = acc.length
    · subst heq; simp
    · have hge : (acc.reverse ++ [x]).length ≤ idx := by simp; omega
      simp [hlt, heq, List.getElem?_eq_none hge]

theorem getD_set_nat {α : Type} (d : α) (xs : List α) (j : Nat) (v : α) (hj : j < xs.length)
    (idx : Nat) :
    (xs.set j v).getD idx d = if idx = j then v else xs.getD idx d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases heq : idx = j
  · subst heq; simp [hj]
  · have hne : j ≠ idx := Ne.symm heq
    simp [heq, List.getElem?_set_ne hne]

private theorem pvar_bv_step (x : BitVec 64) (c : BitVec 8) (i : BitVec 32)
    (hi : i.toNat < 5) (hx : x.toNat < 2 ^ (7 * i.toNat)) :
    let x' := x ||| (BitVec.signExtend 64 (c.setWidth 32 &&& 0x7F#32) <<<
      ((BitVec.setWidth 64 (7#32 * i)).toNat % 64))
    x'.toNat = Nat.lor x.toNat (Nat.shiftLeft (Nat.land c.toNat 127) (7 * i.toNat)) ∧
    x'.toNat < 2 ^ (7 * (i.toNat + 1)) := by
  have hi7 : (7#32 * i).toNat = 7 * i.toNat := by c0_bv_omega [hi]
  have hc7 : (c.setWidth 32 &&& 0x7F#32).toNat = Nat.land c.toNat 127 := by
    have hlt256 := c.isLt
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 32)]
    rfl
  have hc_lt : Nat.land c.toNat 127 < 128 := by
    rw [← hc7, BitVec.toNat_and, show (0x7F#32 : BitVec 32).toNat = 127 from rfl]
    exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hmsb : (c.setWidth 32 &&& 0x7F#32).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hc7]; omega
  have hsext : (BitVec.signExtend 64 (c.setWidth 32 &&& 0x7F#32)).toNat = Nat.land c.toNat 127 := by
    rw [BitVec.toNat_signExtend, hmsb]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [bv_c0_toNat_setWidth_of_le (c.setWidth 32 &&& 0x7F#32) (by decide), hc7]
  have hsh_lt : Nat.land c.toNat 127 * 2 ^ (7 * i.toNat) < 2 ^ (7 * (i.toNat + 1)) := by
    have hpow : 2 ^ (7 * (i.toNat + 1)) = 128 * 2 ^ (7 * i.toNat) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    rw [hpow]; exact Nat.mul_lt_mul_of_pos_right hc_lt (Nat.pow_pos (by decide))
  have hsh_lt64 : Nat.land c.toNat 127 * 2 ^ (7 * i.toNat) < 2 ^ 64 := by
    have hpow : 2 ^ (7 * (i.toNat + 1)) ≤ 2 ^ 35 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hsh_lt64' : Nat.shiftLeft (Nat.land c.toNat 127) (7 * i.toNat) < 2 ^ 64 := by
    show (Nat.land c.toNat 127) <<< (7 * i.toNat) < 2 ^ 64
    rw [Nat.shiftLeft_eq]; exact hsh_lt64
  have himod : (BitVec.setWidth 64 (7#32 * i)).toNat % 64 = 7 * i.toNat := by
    rw [bv_c0_toNat_setWidth_of_le _ (by decide), hi7, Nat.mod_eq_of_lt (by omega)]
  have hsh : (BitVec.signExtend 64 (c.setWidth 32 &&& 0x7F#32) <<<
      ((BitVec.setWidth 64 (7#32 * i)).toNat % 64)).toNat =
      Nat.shiftLeft (Nat.land c.toNat 127) (7 * i.toNat) := by
    rw [bv_c0_toNat_shiftLeft_nat, hsext, himod,
      show Nat.land c.toNat 127 * 2 ^ (7 * i.toNat) =
        Nat.shiftLeft (Nat.land c.toNat 127) (7 * i.toNat) from
        (Nat.shiftLeft_eq (Nat.land c.toNat 127) (7 * i.toNat)).symm,
      Nat.mod_eq_of_lt hsh_lt64']
  have hlor : (x ||| (BitVec.signExtend 64 (c.setWidth 32 &&& 0x7F#32) <<<
      ((BitVec.setWidth 64 (7#32 * i)).toNat % 64))).toNat =
      Nat.lor x.toNat (Nat.shiftLeft (Nat.land c.toNat 127) (7 * i.toNat)) := by
    rw [BitVec.toNat_or, hsh]; rfl
  refine ⟨hlor, ?_⟩
  change (x ||| BitVec.signExtend 64 (c.setWidth 32 &&& 0x7F#32) <<<
      ((BitVec.setWidth 64 (7#32 * i)).toNat % 64)).toNat < 2 ^ (7 * (i.toNat + 1))
  rw [hlor, nat_lor_shl_disj _ _ _ hx]
  have hpow : 2 ^ (7 * (i.toNat + 1)) = 2 ^ (7 * i.toNat) + 127 * 2 ^ (7 * i.toNat) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, show 2 ^ 7 = 1 + 127 by decide, Nat.mul_add,
      Nat.mul_one]
    omega
  have hle : Nat.land c.toNat 127 * 2 ^ (7 * i.toNat) ≤ 127 * 2 ^ (7 * i.toNat) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## 3. `bytes` Load Rules & WP Proofs for `ar_pch`, `ar_pnum`, `ar_pvarint` -/

@[c0_load] theorem c0_load_bytes_bv64 {base i : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bytes base bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (base + i) = some (BitVec.ofNat 8 (bs[i.toNat]'hi).toNat) := by
  have heq : i = BitVec.ofNat 64 i.toNat := by apply BitVec.eq_of_toNat_eq; simp
  conv => lhs; rw [heq]
  exact load_bytes_at hi hlen hm

@[c0_load] theorem c0_load_bytes_ofNat {base : BitVec 64} {k : Nat} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bytes base bs ⋆ R) m)
    (hk : k < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (base + BitVec.ofNat 64 k) = some (BitVec.ofNat 8 (bs[k]'hk).toNat) :=
  load_bytes_at hk hlen hm

@[c0_load] theorem c0_load_bytes_zero {base : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bytes base bs ⋆ R) m)
    (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 base = some (BitVec.ofNat 8 (bs[0]'hi).toNat) := by
  simpa using load_bytes_at (i := 0) hi hlen hm

private theorem u8_and_128_eq_zero (b : UInt8) (h : b.toNat &&& 128 = 0) : b.toNat < 128 := by
  have hb := b.toNat_lt
  have htb : b.toNat.testBit 7 = false := by
    have ht := Nat.testBit_and b.toNat 128 7
    rw [h, Nat.zero_testBit] at ht
    simpa [show (128 : Nat).testBit 7 = true by decide] using ht
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, show (2 ^ 7 : Nat) = 128 from rfl] at htb
  have hdiv : b.toNat / 128 = 0 ∨ b.toNat / 128 = 1 := by omega
  rcases hdiv with h0 | h1
  · omega
  · rw [h1] at htb; cases htb

private theorem u8_and_128_ne_zero (b : UInt8) (h : b.toNat &&& 128 ≠ 0) : 128 ≤ b.toNat := by
  by_cases hlt : b.toNat < 128
  · exfalso; apply h
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j = 7
    · subst hj
      have hdiv : b.toNat / 128 = 0 := Nat.div_eq_of_lt hlt
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
    · have h128 : (128 : Nat).testBit j = false := by
        have : j < 7 ∨ 7 < j := by omega
        rcases this with hjlt | hjgt
        · rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
          have hpow : 128 = 2 ^ j * (2 * 2 ^ (6 - j)) := by
            rw [← Nat.pow_succ', ← Nat.pow_add, show j + (6 - j + 1) = 7 by omega]
          rw [hpow, Nat.mul_div_right _ (Nat.pow_pos (by decide)), Nat.and_comm 1,
            Nat.and_one_is_mod, Nat.mul_mod_right]; decide
        · have hdiv : 128 / 2 ^ j = 0 :=
            Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 128 < 2 ^ 8)
              (Nat.pow_le_pow_right (by decide) (by omega)))
          rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; decide
      rw [h128, Bool.and_false]
  · omega

private theorem bv32_toInt_of_lt (x : Nat) (hx : x < 2 ^ 31) :
    (BitVec.ofNat 32 x).toInt = (x : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 32)]
  have h : 2 * x < 2 ^ 32 := by omega
  simp only [h, ↓reduceIte]

private theorem bv32_setWidth_u8_toInt (b : UInt8) :
    ((BitVec.ofNat 8 b.toNat).setWidth 32).toInt = (b.toNat : Int) := by
  have hb := b.toNat_lt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)]
  have h : 2 * b.toNat < 2 ^ 32 := by omega
  simp only [h, ↓reduceIte]

private theorem u8_sle_lo (k : Nat) (hk : k < 2 ^ 31) (b : UInt8)
    (h : (BitVec.ofNat 32 k).sle ((BitVec.ofNat 8 b.toNat).setWidth 32) = true) : k ≤ b.toNat := by
  rw [BitVec.sle_eq_decide, decide_eq_true_eq, bv32_toInt_of_lt k hk, bv32_setWidth_u8_toInt] at h
  omega

private theorem u8_sle_lo_false (k : Nat) (hk : k < 2 ^ 31) (b : UInt8)
    (h : (BitVec.ofNat 32 k).sle ((BitVec.ofNat 8 b.toNat).setWidth 32) = false) :
    b.toNat < k := by
  rw [BitVec.sle_eq_decide, decide_eq_false_iff_not, bv32_toInt_of_lt k hk,
    bv32_setWidth_u8_toInt] at h; omega

private theorem u8_sle_hi (k : Nat) (hk : k < 2 ^ 31) (b : UInt8)
    (h : ((BitVec.ofNat 8 b.toNat).setWidth 32).sle (BitVec.ofNat 32 k) = true) : b.toNat ≤ k := by
  rw [BitVec.sle_eq_decide, decide_eq_true_eq, bv32_toInt_of_lt k hk, bv32_setWidth_u8_toInt] at h
  omega

private theorem u8_sle_hi_false (k : Nat) (hk : k < 2 ^ 31) (b : UInt8)
    (h : ((BitVec.ofNat 8 b.toNat).setWidth 32).sle (BitVec.ofNat 32 k) = false) :
    k < b.toNat := by
  rw [BitVec.sle_eq_decide, decide_eq_false_iff_not, bv32_toInt_of_lt k hk,
    bv32_setWidth_u8_toInt] at h; omega

theorem ar_pch_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arPchSpec xs m Q X → Func.wp Γ ar_pch_body xs m Q X := by
  rintro ⟨b, n, pos, c, ⟨⟩⟩ m Q X ⟨bs, R, hn, hlen, hm, hQ⟩
  c0_hsteps
  · refine hQ false pos ⟨fun h => ?_, fun _ => ⟨rfl, rfl⟩⟩
    have hge : ¬ pos.toNat < n.toNat := by c0_bv_omega [hc]
    exact absurd h.1 hge
  · refine hQ false pos ⟨fun h => ?_, fun _ => ⟨rfl, rfl⟩⟩
    have hlt : pos.toNat < n.toNat := by c0_bv_omega [hc]
    have hlt_b : (bs[pos.toNat]'(by omega)).toNat < 256 := (bs[pos.toNat]'(by omega)).toNat_lt
    have hne : (bs.getD pos.toNat 0).toNat ≠ c.toNat := by
      intro heq; apply hc
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_b,
        Nat.mod_eq_of_lt (by omega : (bs[pos.toNat]'(by omega)).toNat < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 32)]
      simpa [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : pos.toNat < bs.length)] using heq
    exact absurd h.2 hne
  · have hlt : pos.toNat < n.toNat := by c0_bv_omega [hc]
    have hlt_b : (bs[pos.toNat]'(by omega)).toNat < 256 := (bs[pos.toNat]'(by omega)).toNat_lt
    have heq : (bs.getD pos.toNat 0).toNat = c.toNat := by
      have ht : (bs[pos.toNat]'(by omega)).toNat = c.toNat := by c0_bv_omega [hc, hlt_b]
      simpa [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : pos.toNat < bs.length)] using ht
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := by c0_bv_omega [hlt]
    exact hQ true (pos + 1) ⟨fun _ => ⟨rfl, rfl, hp1, by omega⟩, fun h => absurd ⟨hlt, heq⟩ h⟩

private structure PnumSt where
  p : BitVec 64
  v : BitVec 64
  nd : BitVec 32

theorem ar_pnum_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arPnumSpec xs m Q X → Func.wp Γ ar_pnum_body xs m Q X := by
  rintro ⟨b, n, pos, ⟨⟩⟩ m Q X ⟨bs, R, hn, hlen, hm, hQ⟩
  c0_hsteps
  refine c0_while_state (α := PnumSt)
    (fun st => (st.p, st.v, st.nd, ()))
    (fun st => 11 - st.nd.toNat)
    (fun st m' => m' = m ∧ st.nd.toNat ≤ 10 ∧ st.v.toNat ≤ 0xFFFFFFFF ∧
      st.p.toNat = pos.toNat + st.nd.toNat ∧
      (st.nd.toNat = 0 → st.v = 0#64) ∧
      (st.nd.toNat > 0 →
        pos.toNat < n.toNat ∧ st.p.toNat ≤ n.toNat ∧
        isDigit (bs.getD pos.toNat 0).toNat = true ∧
        ∀ (term : Nat) {β : Type} (fail : β) (k : Nat → List Nat → β),
          pnum term fail ((toNatBytes bs).drop pos.toNat) k =
            pnumGo term fail k ((toNatBytes bs).drop st.p.toNat) st.v.toNat))
    (fun J hJ => by
      c0_hsteps
      exact hJ ⟨pos, 0#64, 0#32⟩ m ⟨rfl, by simp, by simp, by simp, fun _ => rfl,
        fun h => by simp at h⟩)
    (fun J_lp st m' ⟨hm', hnd, hv, hp, hv0, hinv⟩ hJ_lp => by
      subst hm'
      refine LeanQbe.T.wp_unroll_group fun K hK => ?_
      c0_hsplit
      · -- p < n
        have hlt_pn : st.p.toNat < n.toNat := hc
        clear hc
        c0_hsplit
        · -- b[p] >= 48
          have hge48 : 48 ≤ (bs[st.p.toNat]'(by omega)).toNat :=
            u8_sle_lo 48 (by decide) _ hc
          clear hc
          c0_hsplit
          · -- b[p] <= 57
            have hle57 : (bs[st.p.toNat]'(by omega)).toNat ≤ 57 :=
              u8_sle_hi 57 (by decide) _ hc
            clear hc
            c0_hsplit
            · -- nd' > 10 -> return false
              c0_hsteps
              exact hQ false (st.p + 1) 0#32 (fun h => absurd h (by decide))
            · -- nd' <= 10
              have hnd' : (st.nd + 1#32).toNat ≤ 10 := by c0_bv_omega [hc, hnd]
              clear hc
              c0_hsplit
              · -- v' > 0xFFFFFFFF -> return false
                c0_hsteps
                exact hQ false (st.p + 1) 0#32 (fun h => absurd h (by decide))
              · -- v' <= 0xFFFFFFFF -> continue
                have hdig_p : isDigit (bs[st.p.toNat]'(by omega)).toNat = true :=
                  (isDigit_iff _).mpr ⟨hge48, hle57⟩
                have hb_lt256 := (bs[st.p.toNat]'(by omega)).toNat_lt
                have hsext_eq :
                    (BitVec.signExtend 64
                      (BitVec.setWidth 32 (BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat) -
                        48#32)).toNat =
                      (bs[st.p.toNat]'(by omega)).toNat - 48 := by
                  let d32 := BitVec.setWidth 32
                    (BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat) - 48#32
                  have hsub32 : d32.toNat = (bs[st.p.toNat]'(by omega)).toNat - 48 := by
                    dsimp only [d32]; c0_bv_omega [hge48, hb_lt256]
                  have hmsb : d32.msb = false := by
                    rw [BitVec.msb_eq_false_iff_two_mul_lt, hsub32]; omega
                  rw [BitVec.toNat_signExtend, hmsb]
                  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
                  rw [bv_c0_toNat_setWidth_of_le _ (by decide), hsub32]
                have hv_lt : st.v.toNat * 10 + ((bs[st.p.toNat]'(by omega)).toNat - 48) <
                    2 ^ 64 := by
                  omega
                let v' := st.v * 10#64 +
                  BitVec.signExtend 64
                    (BitVec.setWidth 32 (BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat) - 48#32)
                have hv'_eq : v'.toNat =
                    st.v.toNat * 10 + ((bs[st.p.toNat]'(by omega)).toNat - 48) := by
                  dsimp only [v']
                  rw [BitVec.toNat_add, BitVec.toNat_mul,
                    show (10#64 : BitVec 64).toNat = 10 from rfl, hsext_eq,
                    Nat.mod_eq_of_lt (by omega : st.v.toNat * 10 < 2 ^ 64),
                    Nat.mod_eq_of_lt hv_lt]
                have hv'_le : v'.toNat ≤ 0xFFFFFFFF := by
                  have hsub : ((BitVec.setWidth 32
                      (BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat)) - 48#32).toNat =
                      (bs[st.p.toNat]'(by omega)).toNat - 48 := by c0_bv_omega [hge48, hb_lt256]
                  have hc' : ¬ 0xFFFFFFFF <
                      (st.v.toNat * 10 + ((BitVec.signExtend 64 (BitVec.setWidth 32
                        (BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat) - 48#32)).toNat)) %
                        2 ^ 64 := by
                    simpa using hc
                  rw [hsext_eq, Nat.mod_eq_of_lt hv_lt] at hc'
                  omega
                have hp'_eq : (st.p + 1#64).toNat = st.p.toNat + 1 := by c0_bv_omega [hlt_pn]
                have hnd'_eq : (st.nd + 1#32).toNat = st.nd.toNat + 1 := by c0_bv_omega [hnd]
                clear hc
                c0_hsteps
                refine hJ_lp ⟨st.p + 1#64, v', st.nd + 1#32⟩ m' (by dsimp only; rw [hnd'_eq]; omega)
                  ⟨rfl, by dsimp only; rw [hnd'_eq]; omega,
                    by dsimp only; exact hv'_le,
                    by dsimp only; rw [hp'_eq, hnd'_eq]; omega,
                    fun h => by dsimp only at h; rw [hnd'_eq] at h; omega,
                    fun _ => ?_⟩
                dsimp only
                by_cases hnd0 : st.nd.toNat = 0
                · have hp0 : st.p.toNat = pos.toNat := by omega
                  have hpos_lt : pos.toNat < n.toNat := by omega
                  have hdig_pos : isDigit (bs.getD pos.toNat 0).toNat = true := by
                    simp only [List.getD_eq_getElem?_getD,
                      List.getElem?_eq_getElem (by omega : pos.toNat < bs.length), Option.getD_some]
                    simpa [hp0] using hdig_p
                  have hst_v : st.v.toNat = 0 := by rw [hv0 hnd0]; rfl
                  refine ⟨hpos_lt, by rw [hp'_eq]; omega, hdig_pos, fun term β fail k => ?_⟩
                  rw [pnum_eq_pnumGo (by omega) (by simpa [hp0] using hdig_p), ← hp0,
                    pnumGo_step_digit (by omega) hdig_p 0, hp'_eq, hv'_eq, hst_v]
                · obtain ⟨hpos_lt, _, hdig_pos, hfn⟩ := hinv (by omega)
                  refine ⟨hpos_lt, by rw [hp'_eq]; omega, hdig_pos, fun term β fail k => ?_⟩
                  rw [hfn term fail k, pnumGo_step_digit (by omega) hdig_p st.v.toNat,
                    hp'_eq, hv'_eq]
          · -- b[p] > 57 -> exit loop
            have hgt57 : 57 < (bs[st.p.toNat]'(by omega)).toNat :=
              u8_sle_hi_false 57 (by decide) _ (by simpa using hc)
            have hnd_p : isDigit (bs.getD st.p.toNat 0).toNat = false := by
              simp [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length),
                isDigit_false_iff, hgt57]
            clear hc
            c0_hsteps
            · exact hQ false st.p 0#32 (fun h => absurd h (by decide))
            · have hnd_pos : 0 < st.nd.toNat :=
                Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
              obtain ⟨_, hp_le, _, hfn⟩ := hinv hnd_pos
              refine hQ true st.p (st.v.setWidth 32) (fun _ => ?_)
              have hv32 : (st.v.setWidth 32).toNat = st.v.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              refine ⟨by omega, hp_le, fun _ => hnd_p, fun term β fail k hpn hterm => ?_⟩
              rw [hfn term fail k, hv32]
              have hterm' : (bs[st.p.toNat]'(by omega)).toNat = term := by
                simpa [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length)] using hterm
              have hnd_p' : isDigit (bs[st.p.toNat]'(by omega)).toNat = false := by
                simpa [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length)] using hnd_p
              exact pnumGo_stop_term (by omega) hnd_p' hterm' st.v.toNat
        · -- b[p] < 48 -> exit loop
          have hlt48 : (bs[st.p.toNat]'(by omega)).toNat < 48 :=
            u8_sle_lo_false 48 (by decide) _ (by simpa using hc)
          have hnd_p : isDigit (bs.getD st.p.toNat 0).toNat = false := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length),
              isDigit_false_iff, hlt48]
          clear hc
          c0_hsteps
          · exact hQ false st.p 0#32 (fun h => absurd h (by decide))
          · have hnd_pos : 0 < st.nd.toNat :=
              Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
            obtain ⟨_, hp_le, _, hfn⟩ := hinv hnd_pos
            refine hQ true st.p (st.v.setWidth 32) (fun _ => ?_)
            have hv32 : (st.v.setWidth 32).toNat = st.v.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            refine ⟨by omega, hp_le, fun _ => hnd_p, fun term β fail k hpn hterm => ?_⟩
            rw [hfn term fail k, hv32]
            have hterm' : (bs[st.p.toNat]'(by omega)).toNat = term := by
              simpa [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length)] using hterm
            have hnd_p' : isDigit (bs[st.p.toNat]'(by omega)).toNat = false := by
              simpa [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : st.p.toNat < bs.length)] using hnd_p
            exact pnumGo_stop_term (by omega) hnd_p' hterm' st.v.toNat
      · -- p >= n -> exit loop
        have hp_ge : n.toNat ≤ st.p.toNat := by c0_bv_omega [hc]
        clear hc
        c0_hsteps
        · exact hQ false st.p 0#32 (fun h => absurd h (by decide))
        · have hnd_pos : 0 < st.nd.toNat :=
            Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
          obtain ⟨_, hp_le, _, hfn⟩ := hinv hnd_pos
          refine hQ true st.p (st.v.setWidth 32) (fun _ => ?_)
          refine ⟨by omega, hp_le, fun h => by omega, fun term β fail k hpn _ => by omega⟩)

private structure PvarSt where
  p : BitVec 64
  x : BitVec 64
  i : BitVec 32

theorem ar_pvarint_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arPvarintSpec xs m Q X → Func.wp Γ ar_pvarint_body xs m Q X := by
  rintro ⟨b, n, pos, ⟨⟩⟩ m Q X ⟨bs, R, hn, hlen, hm, hQ⟩
  c0_hsteps
  refine c0_while_state (α := PvarSt)
    (fun st => (st.p, st.x, st.i, ()))
    (fun st => 5 - st.i.toNat)
    (fun st m' => m' = m ∧ st.i.toNat ≤ 5 ∧
      st.p.toNat = pos.toNat + st.i.toNat ∧
      (st.i.toNat > 0 → st.p.toNat ≤ n.toNat) ∧
      st.x.toNat < 2 ^ (7 * st.i.toNat) ∧
      ∀ {β : Type} (fail : β) (k : Nat → List Nat → β),
        pvar fail ((toNatBytes bs).drop pos.toNat) k =
          pvarGo fail k ((toNatBytes bs).drop st.p.toNat) st.x.toNat (7 * st.i.toNat))
    (fun J hJ => by
      c0_hsteps
      exact hJ ⟨pos, 0#64, 0#32⟩ m ⟨rfl, by simp, by simp, fun h => by simp at h,
        by simp, fun fail k => rfl⟩)
    (fun J st m' ⟨hm', hi, hp, hp_le, hx, hfn⟩ hJ => by
      subst hm'
      c0_hsplit
      · -- i < 5
        have hi5 : st.i.toNat < 5 := hc
        clear hc
        c0_hsplit
        · -- p >= n -> return false
          c0_hsteps
          exact hQ false st.p 0#32 (fun h => absurd h (by decide))
        · -- p < n
          have hlt_pn : st.p.toNat < n.toNat := by c0_bv_omega [hc]
          clear hc
          let c8 := BitVec.ofNat 8 (bs[st.p.toNat]'(by omega)).toNat
          let x' := st.x ||| (BitVec.signExtend 64 (c8.setWidth 32 &&& 0x7F#32) <<<
            ((BitVec.setWidth 64 (7#32 * st.i)).toNat % 64))
          obtain ⟨hx'_eq, hx'_lt⟩ := pvar_bv_step st.x c8 st.i hi5 hx
          have hc8_toNat : c8.toNat = (bs[st.p.toNat]'(by omega)).toNat := by
            dsimp only [c8]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bs[st.p.toNat]'(by omega)).toNat_lt]
          have hp'_eq : (st.p + 1#64).toNat = st.p.toNat + 1 := by c0_bv_omega [hlt_pn]
          c0_hsplit
          · -- (c & 0x80) == 0
            have hc_lt128 : (bs[st.p.toNat]'(by omega)).toNat < 128 := by
              have hc8_and : (c8.setWidth 32 &&& 0x80#32).toNat = 0 := by
                dsimp only [c8]; rw [hc, BitVec.toNat_zero]
              have hlt256 := (bs[st.p.toNat]'(by omega)).toNat_lt
              rw [BitVec.toNat_and, BitVec.toNat_setWidth, hc8_toNat,
                Nat.mod_eq_of_lt (by omega : (bs[st.p.toNat]'(by omega)).toNat < 2 ^ 32),
                show (0x80#32 : BitVec 32).toNat = 128 from rfl] at hc8_and
              exact u8_and_128_eq_zero _ hc8_and
            clear hc
            c0_hsplit
            · -- x' > 0xFFFFFFFF -> return false
              c0_hsteps
              exact hQ false (st.p + 1) 0#32 (fun h => absurd h (by decide))
            · -- x' <= 0xFFFFFFFF -> return true
              have hx'_le : x'.toNat ≤ 0xFFFFFFFF := by
                have : ¬ 0xFFFFFFFF < x'.toNat := by c0_bv_omega [hc]
                omega
              clear hc
              c0_hsteps
              refine hQ true (st.p + 1) (x'.setWidth 32) (fun _ => ?_)
              have hv32 : (x'.setWidth 32).toNat = x'.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              have hp1' : (st.p + 1).toNat = st.p.toNat + 1 := hp'_eq
              refine ⟨by omega, by omega, fun {β} fail k => ?_⟩
              rw [hfn fail k, pvarGo_step_done (by omega) hc_lt128 st.x.toNat (7 * st.i.toNat),
                hv32, hx'_eq, hc8_toNat, hp1']
          · -- (c & 0x80) != 0 -> continue
            have hc_ge128 : 128 ≤ (bs[st.p.toNat]'(by omega)).toNat := by
              have hc8_ne : (c8.setWidth 32 &&& 0x80#32).toNat ≠ 0 := by
                intro h0; apply hc; apply BitVec.eq_of_toNat_eq
                dsimp only [c8] at h0; rw [h0, BitVec.toNat_zero]
              have hlt256 := (bs[st.p.toNat]'(by omega)).toNat_lt
              rw [BitVec.toNat_and, BitVec.toNat_setWidth, hc8_toNat,
                Nat.mod_eq_of_lt (by omega : (bs[st.p.toNat]'(by omega)).toNat < 2 ^ 32),
                show (0x80#32 : BitVec 32).toNat = 128 from rfl] at hc8_ne
              exact u8_and_128_ne_zero _ hc8_ne
            have hi'_eq : (st.i + 1#32).toNat = st.i.toNat + 1 := by c0_bv_omega [hi5]
            clear hc
            c0_hsteps
            refine hJ ⟨st.p + 1#64, x', st.i + 1#32⟩ m' (by rw [hi'_eq]; omega)
              ⟨rfl, by rw [hi'_eq]; omega, by rw [hp'_eq, hi'_eq]; omega,
                fun _ => by rw [hp'_eq]; omega, by rw [hi'_eq]; exact hx'_lt,
                fun fail k => ?_⟩
            rw [hfn fail k, pvarGo_step_cont (by omega) hc_ge128 st.x.toNat (7 * st.i.toNat),
              hx'_eq, hc8_toNat, hp'_eq, hi'_eq, Nat.mul_add, Nat.mul_one]
      · -- i >= 5 -> return false
        c0_hsteps
        exact hQ false st.p 0#32 (fun h => absurd h (by decide)))

/-! ## 4. Slab Collapse, Allocator & Table-Pop Helpers -/

theorem addr_add_ofNat (w : BitVec 64) (a b : Nat) :
    w + BitVec.ofNat 64 a + BitVec.ofNat 64 b = w + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem addr_add_toNat (w top : BitVec 64) : w + BitVec.ofNat 64 top.toNat = w + top :=
  congrArg (w + ·) (BitVec.eq_of_toNat_eq (by simp))

private theorem pred_ofArrayAlign8_eq (ty : Ty) (p : BitVec 64) (xs : List (Val ty))
    (a : Nat) (ha : ty.bytes * xs.length = a) :
    (SlabSeg.ofArrayAlign8 ty xs a ha).pred p = arrayPad ty p xs := by
  subst ha; rfl

/-- Collapse the post-`ar_parse_aig` arrays and trailing arena slack back to `region (w + 776)`. -/
theorem aigArraysPre_collapse {w top rhs0Ptr rhs1Ptr olitPtr : BitVec 64}
    {rhs0 rhs1 olit : List (BitVec 32)} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hfit : w.toNat + wlen < 2 ^ 64)
    (htop : top.toNat = 776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) +
      4 * olit.length)
    (hle : top.toNat ≤ wlen)
    (hr0 : rhs0Ptr = w + 776#64)
    (hr1 : rhs1Ptr = w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length)))
    (hol : olitPtr = w + BitVec.ofNat 64
      (776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length)))
    (hm : (arrayPad i32 rhs0Ptr rhs0 ⋆ arrayPad i32 rhs1Ptr rhs1 ⋆
      array (t := i32) olitPtr olit ⋆ region (w + top) (wlen - top.toNat) ⋆ R) m) :
    (region (w + 776#64) (wlen - 776) ⋆ R) m := by
  have hbytes0 : Ty.bytes i32 * rhs0.length = 4 * rhs0.length := by simp [Ty.bytes, Ty.size]
  have hbytes1 : Ty.bytes i32 * rhs1.length = 4 * rhs1.length := by simp [Ty.bytes, Ty.size]
  have hbytes2 : Ty.bytes i32 * olit.length = 4 * olit.length := by simp [Ty.bytes, Ty.size]
  let segs : List SlabSeg :=
    [SlabSeg.ofArrayAlign8 i32 rhs0 (4 * rhs0.length) hbytes0,
     SlabSeg.ofArrayAlign8 i32 rhs1 (4 * rhs1.length) hbytes1,
     SlabSeg.ofArrayExact i32 olit (4 * olit.length) hbytes2,
     SlabSeg.ofRegion (wlen - top.toNat)]
  have htot : SlabChain.totalBytes segs = wlen - 776 := by
    simp only [segs, SlabChain.totalBytes, SlabSeg.ofArrayAlign8, SlabSeg.ofArray,
      SlabSeg.ofArrayExact, SlabSeg.ofRegion]; omega
  refine SlabChain.to_region_frame htot (by omega) ?_
  simp only [segs, SlabChain.eval, SlabSeg.ofArrayExact, SlabSeg.ofRegion, sep_emp, sep_assoc]
  rw [pred_ofArrayAlign8_eq, pred_ofArrayAlign8_eq]
  simp only [SlabSeg.ofArrayAlign8, SlabSeg.ofArray, addr_add_ofNat, Nat.add_assoc]
  rw [show 776 + (align8 (4 * rhs0.length) + (align8 (4 * rhs1.length) + 4 * olit.length)) =
      top.toNat by rw [htop]; omega,
    show 776 + (align8 (4 * rhs0.length) + align8 (4 * rhs1.length)) =
      776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) by omega,
    addr_add_toNat, ← hr0, ← hr1, ← hol]
  simpa only [sep_assoc] using hm

/-- Collapse `aigArraysMem ⋆ netTablesMem ⋆ gateScratchMem` back to `region (s.w + 776)`. -/
theorem tables_collapse {s : ArCtxState} {A O nNets nIn nOut top0 : Nat}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hg : TablesGeom s A O nNets nIn nOut top0)
    (hle : top0 ≤ s.wlen.toNat) (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64)
    (hr0 : rhs0.length = A) (hr1 : rhs1.length = A) (hol : olit.length = O)
    (hb : bindArr.length = nNets) (hro : ruleOff.length = nNets) (hrn : ruleN.length = nNets)
    (hp : partnerArr.length = nNets) (hf : flippedArr.length = nNets)
    (hin : inNetArr.length = nIn) (hout : outRefArr.length = nOut)
    (hsn : stkN.length = arTTStk) (hsp : stkP.length = arTTStk)
    (hmn : memoN.length = arTTMaxAnd) (hmv : memoV.length = arTTMaxAnd)
    (hd : dense.length = 128) (hgy : gsy.length = 85)
    (hcl : gcl.length = 16) (hch : gch.length = 16)
    (hm : (aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ R) m) :
    (region (s.w + 776#64) (top0 - 776) ⋆ R) m := by
  have h4A0 : Ty.bytes i32 * rhs0.length = 4 * A := by simp [Ty.bytes, Ty.size, hr0]
  have h4A1 : Ty.bytes i32 * rhs1.length = 4 * A := by simp [Ty.bytes, Ty.size, hr1]
  have h4O : Ty.bytes i32 * olit.length = 4 * O := by simp [Ty.bytes, Ty.size, hol]
  have h4N0 : Ty.bytes i32 * bindArr.length = 4 * nNets := by simp [Ty.bytes, Ty.size, hb]
  have h4N1 : Ty.bytes i32 * ruleOff.length = 4 * nNets := by simp [Ty.bytes, Ty.size, hro]
  have h4N2 : Ty.bytes i32 * ruleN.length = 4 * nNets := by simp [Ty.bytes, Ty.size, hrn]
  have h4N3 : Ty.bytes i32 * partnerArr.length = 4 * nNets := by simp [Ty.bytes, Ty.size, hp]
  have h1N : Ty.bytes i8 * flippedArr.length = nNets := by simp [Ty.bytes, Ty.size, hf]
  have h4I : Ty.bytes i32 * inNetArr.length = 4 * nIn := by simp [Ty.bytes, Ty.size, hin]
  have h4Ou : Ty.bytes i32 * outRefArr.length = 4 * nOut := by simp [Ty.bytes, Ty.size, hout]
  have hS0 : Ty.bytes i32 * stkN.length = 4 * arTTStk := by simp [Ty.bytes, Ty.size, hsn]
  have hS1 : Ty.bytes i32 * stkP.length = 4 * arTTStk := by simp [Ty.bytes, Ty.size, hsp]
  have hMn : Ty.bytes i32 * memoN.length = 4 * arTTMaxAnd := by simp [Ty.bytes, Ty.size, hmn]
  have hGy : Ty.bytes i32 * gsy.length = 4 * 85 := by simp [Ty.bytes, Ty.size, hgy]
  let segs : List SlabSeg :=
    [SlabSeg.ofArrayAlign8 i32 rhs0 (4 * A) h4A0,
     SlabSeg.ofArrayAlign8 i32 rhs1 (4 * A) h4A1,
     SlabSeg.ofArrayAlign8 i32 olit (4 * O) h4O,
     SlabSeg.ofArrayAlign8 i32 bindArr (4 * nNets) h4N0,
     SlabSeg.ofArrayAlign8 i32 ruleOff (4 * nNets) h4N1,
     SlabSeg.ofArrayAlign8 i32 ruleN (4 * nNets) h4N2,
     SlabSeg.ofArrayAlign8 i32 partnerArr (4 * nNets) h4N3,
     SlabSeg.ofArrayAlign8 i8 flippedArr nNets h1N,
     SlabSeg.ofArrayAlign8 i32 inNetArr (4 * nIn) h4I,
     SlabSeg.ofArrayAlign8 i32 outRefArr (4 * nOut) h4Ou,
     SlabSeg.ofArrayAlign8 i32 stkN (4 * arTTStk) hS0,
     SlabSeg.ofArrayAlign8 i32 stkP (4 * arTTStk) hS1,
     SlabSeg.ofArrayAlign8 i32 memoN (4 * arTTMaxAnd) hMn,
     SlabSeg.ofArray64 memoV arTTMaxAnd hmv,
     SlabSeg.ofArray64 dense 128 hd,
     SlabSeg.ofArrayAlign8 i32 gsy (4 * 85) hGy,
     SlabSeg.ofArray64 gcl 16 hcl,
     SlabSeg.ofArray64 gch 16 hch]
  have haS0 : align8 (4 * arTTStk) = 4 * arTTStk := by
    simp only [arTTStk]; decide
  have haMn : align8 (4 * arTTMaxAnd) = 4 * arTTMaxAnd := by
    simp only [arTTMaxAnd]; decide
  have htot : SlabChain.totalBytes segs = top0 - 776 := by
    rw [hg.top_eq, tablesEndTop]
    simp only [segs, SlabChain.totalBytes, SlabSeg.ofArrayAlign8, SlabSeg.ofArray,
      SlabSeg.ofArray64, haS0, haMn, Nat.add_zero, Nat.add_assoc]
    exact (Nat.add_sub_cancel_left 776 _).symm
  refine SlabChain.to_region_frame htot (by omega) ?_
  simp only [segs, SlabChain.eval, SlabSeg.ofArray64, pred_ofArrayAlign8_eq]
  simp only [SlabSeg.ofArrayAlign8, SlabSeg.ofArray, haS0, haMn, sep_emp, sep_assoc]
  rw [← hg.rhs0_eq]
  have ha1 : s.rhs0 + BitVec.ofNat 64 (align8 (4 * A)) = s.rhs1 := by
    rw [hg.rhs0_eq, hg.rhs1_eq, addr_add_ofNat]
  have ha2 : s.rhs1 + BitVec.ofNat 64 (align8 (4 * A)) = s.olit := by
    rw [hg.rhs1_eq, hg.olit_eq, addr_add_ofNat]
  have ha3 : s.olit + BitVec.ofNat 64 (align8 (4 * O)) = s.bind := by
    rw [hg.olit_eq, hg.bind_eq, addr_add_ofNat]
  rw [ha1, ha2, ha3, ← hg.rule_off_eq, ← hg.rule_n_eq, ← hg.partner_eq, ← hg.flipped_eq,
    ← hg.in_net_eq, ← hg.out_ref_eq, ← hg.stk_n_eq, ← hg.stk_p_eq, ← hg.memo_n_eq,
    ← hg.memo_v_eq, ← hg.dense_eq, ← hg.gsy_eq, ← hg.gcl_eq, ← hg.gch_eq]
  simpa only [aigArraysMem, netTablesMem, gateScratchMem, sep_assoc] using hm

theorem region_merge_offset (w : BitVec 64) {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hfit : w.toNat + c < 2 ^ 64) :
    (region (w + BitVec.ofNat 64 a) (b - a) ⋆ region (w + BitVec.ofNat 64 b) (c - b)) =
      region (w + BitVec.ofNat 64 a) (c - a) := by
  have heq : w + BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) = w + BitVec.ofNat 64 b := by
    rw [addr_add_ofNat]; congr 2; omega
  rw [← heq]
  exact region_merge_eq (by omega) (by omega)

theorem sep_mono_r {A P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ P) m) : (A ⋆ Q) m := by
  rw [sep_comm] at hm ⊢
  exact sep_mono h hm

theorem sep_swap2r {P Q R : Mem 64 → Prop} {m : Mem 64} (h : (P ⋆ (Q ⋆ R)) m) :
    (Q ⋆ (P ⋆ R)) m := by
  rw [← sep_assoc, sep_comm P Q, sep_assoc] at h; exact h

theorem sep_pull3r {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ D))) m) : (C ⋆ (A ⋆ (B ⋆ D))) m :=
  sep_swap2r (sep_mono_r (fun _ => sep_swap2r) h)

theorem sep_pull4r {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m) : (D ⋆ (A ⋆ (B ⋆ (C ⋆ E)))) m :=
  sep_swap2r (sep_mono_r (fun _ => sep_pull3r) h)

/-- Collapse `aigArraysMem ⋆ netTablesMem ⋆ gateScratchMem ⋆ region (w + top0)` to
`region (s.w + 776)`. -/
theorem tables_collapse_avail {s : ArCtxState} {A O nNets nIn nOut top0 : Nat}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hg : TablesGeom s A O nNets nIn nOut top0)
    (h776 : 776 ≤ top0) (hle : top0 ≤ s.wlen.toNat) (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64)
    (hr0 : rhs0.length = A) (hr1 : rhs1.length = A) (hol : olit.length = O)
    (hb : bindArr.length = nNets) (hro : ruleOff.length = nNets) (hrn : ruleN.length = nNets)
    (hp : partnerArr.length = nNets) (hf : flippedArr.length = nNets)
    (hin : inNetArr.length = nIn) (hout : outRefArr.length = nOut)
    (hsn : stkN.length = arTTStk) (hsp : stkP.length = arTTStk)
    (hmn : memoN.length = arTTMaxAnd) (hmv : memoV.length = arTTMaxAnd)
    (hd : dense.length = 128) (hgy : gsy.length = 85)
    (hcl : gcl.length = 16) (hch : gch.length = 16)
    (hm : (aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
      region (s.w + BitVec.ofNat 64 top0) (s.wlen.toNat - top0) ⋆ R) m) :
    (region (s.w + 776#64) (s.wlen.toNat - 776) ⋆ R) m := by
  have hm0 : (aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
      (region (s.w + BitVec.ofNat 64 top0) (s.wlen.toNat - top0) ⋆ R)) m := by
    simpa only [sep_assoc] using hm
  have hm1 := tables_collapse hg hle hfit hr0 hr1 hol hb hro hrn hp hf hin hout hsn hsp hmn hmv
    hd hgy hcl hch hm0
  rw [← sep_assoc, show (776#64 : BitVec 64) = BitVec.ofNat 64 776 from rfl,
    region_merge_offset s.w h776 hle hfit] at hm1
  exact hm1

theorem ar_aalloc_seq_step (Γ : LeanQbe.T.Env)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X)
    {cx nbytes : BitVec 64} {s : ArCtxState} {baseTop : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hwpos : 0 < s.w.toNat) (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64)
    (hbase : baseTop ≤ s.top.toNat) (htop : s.top.toNat ≤ s.wlen.toNat)
    (hm : (arCtxMem cx s ⋆ (region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
      (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R))) m)
    (hk : ∀ (ret newTop : BitVec 64) (m' : Mem 64),
      baseTop ≤ newTop.toNat → newTop.toNat ≤ s.wlen.toNat →
      ((ret = 0#64 ∧ newTop = s.top) ∨
       (ret ≠ 0#64 ∧ ret = s.w + BitVec.ofNat 64 (align8 s.top.toNat) ∧
        newTop.toNat = align8 s.top.toNat + nbytes.toNat)) →
      (arCtxMem cx { s with top := newTop } ⋆
        (region (s.w + BitVec.ofNat 64 baseTop) (newTop.toNat - baseTop) ⋆
         (region (s.w + newTop) (s.wlen.toNat - newTop.toNat) ⋆ R))) m' →
      Q (ret, ⟨⟩) m') :
    Γ "ar_aalloc" [i64, i64] [i64] (cx, nbytes, ⟨⟩) m Q X := by
  have hm0 : (arCtxMem cx s ⋆ region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆
      (region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆ R)) m := by
    rw [sep_assoc]
    exact sep_mono_r (fun _ => sep_swap2r) hm
  refine hAlloc (cx, nbytes, ⟨⟩) m Q X ⟨s,
    region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆ R,
    hwpos, htop, hfit, hm0, ?_⟩
  intro ret s' m'; dsimp only; intro h
  rcases h with ⟨rfl, rfl, hm'⟩ | ⟨hne, hle, rfl, rfl, hm'⟩
  · have hctx : { s' with top := s'.top } = s' := by cases s'; rfl
    simp only [sep_assoc] at hm'
    have hm1 := sep_mono_r (fun _ => sep_swap2r) hm'
    rw [← hctx] at hm1
    exact hk 0#64 s'.top m' hbase htop (Or.inl ⟨rfl, rfl⟩) hm1
  · have hpad : s.top.toNat + (8 - s.top.toNat % 8) % 8 = align8 s.top.toNat := by
      unfold align8; omega
    let newTop := BitVec.ofNat 64 (align8 s.top.toNat + nbytes.toNat)
    have hnew : newTop.toNat = align8 s.top.toNat + nbytes.toNat := by
      dsimp only [newTop]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hm1 : (arCtxMem cx { s with top := newTop } ⋆
        (region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
         (region (s.w + BitVec.ofNat 64 s.top.toNat) ((8 - s.top.toNat % 8) % 8) ⋆
          (region (s.w + BitVec.ofNat 64 (align8 s.top.toNat)) nbytes.toNat ⋆
           (region (s.w + newTop) (s.wlen.toNat - newTop.toNat) ⋆ R))))) m' := by
      dsimp only [newTop]
      rw [show (BitVec.ofNat 64 (align8 s.top.toNat + nbytes.toNat)).toNat =
        align8 s.top.toNat + nbytes.toNat from hnew]
      simp only [sep_assoc] at hm'
      rw [hpad, ← addr_add_toNat s.w s.top] at hm'
      exact sep_mono_r (fun _ h => sep_pull4r h) hm'
    have h1' : (region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
        region (s.w + BitVec.ofNat 64 s.top.toNat) ((8 - s.top.toNat % 8) % 8)) =
        region (s.w + BitVec.ofNat 64 baseTop) (align8 s.top.toNat - baseTop) := by
      simpa [← hpad] using
        region_merge_offset s.w hbase (by omega : s.top.toNat ≤ align8 s.top.toNat)
        (by omega)
    have h2' := region_merge_offset s.w (by omega : baseTop ≤ align8 s.top.toNat)
      (by rw [hnew]; omega : align8 s.top.toNat ≤ newTop.toNat) (by omega)
    rw [show nbytes.toNat = newTop.toNat - align8 s.top.toNat by omega] at hm1
    rw [← sep_assoc (region (s.w + BitVec.ofNat 64 baseTop) _), h1',
      ← sep_assoc (region (s.w + BitVec.ofNat 64 baseTop) _), h2'] at hm1
    exact hk _ newTop m' (by omega) (by omega) (Or.inr ⟨hne, by rw [hpad], hnew⟩) hm1

private theorem pop_arrayPad_u32 {w : BitVec 64} {off : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : align8 (4 * n) ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) (align8 (4 * n)) ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (arrayPad i32 (w + BitVec.ofNat 64 off) xs ⋆ R) m := by
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u32 n
    (by rw [ha, Nat.sub_self, Nat.zero_add]; exact align8_ge (4 * n)) hle hm
  rw [ha, Nat.sub_self, region_zero, emp_sep, ← hlen, ← addr_add_ofNat,
    show align8 (4 * xs.length) - (0 + 4 * xs.length) =
      align8 (4 * xs.length) - 4 * xs.length by omega] at hm1
  exact ⟨xs, hlen, region_merge_pad_u32 hm1⟩

private theorem pop_arrayPad_u8 {w : BitVec 64} {off : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : align8 n ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) (align8 n) ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (arrayPad i8 (w + BitVec.ofNat 64 off) xs ⋆ R) m := by
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u8 n
    (by rw [ha, Nat.sub_self, Nat.zero_add]; exact align8_ge n) hle hm
  rw [ha, Nat.sub_self, region_zero, emp_sep, ← hlen, ← addr_add_ofNat,
    show align8 xs.length - (0 + xs.length) = align8 xs.length - xs.length by omega] at hm1
  exact ⟨xs, hlen, region_merge_pad_u8 hm1⟩

private theorem pop_array64 {w : BitVec 64} {off : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : 8 * n ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) (8 * n) ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (array64 (w + BitVec.ofNat 64 off) xs ⋆ R) m := by
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u64 n (by rw [ha]; omega) hle hm
  rw [ha, Nat.sub_self, region_zero, emp_sep, show 8 * n - (0 + 8 * n) = 0 by omega,
    region_zero] at hm1
  exact ⟨xs, hlen, by simpa [sep_emp] using hm1⟩

private theorem pop_step_u32 {w ptr : BitVec 64} {off rem : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : align8 (4 * n) ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (hptr : ptr = w + BitVec.ofNat 64 off) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (arrayPad i32 ptr xs ⋆
       (region (w + BitVec.ofNat 64 (off + align8 (4 * n))) (rem - align8 (4 * n)) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = align8 (4 * n) + (rem - align8 (4 * n)) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  simpa [hptr] using pop_arrayPad_u32 n h8 (by omega) hm0

private theorem pop_step_u8 {w ptr : BitVec 64} {off rem : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : align8 n ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (hptr : ptr = w + BitVec.ofNat 64 off) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (arrayPad i8 ptr xs ⋆
       (region (w + BitVec.ofNat 64 (off + align8 n)) (rem - align8 n) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = align8 n + (rem - align8 n) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  simpa [hptr] using pop_arrayPad_u8 n h8 (by omega) hm0

private theorem pop_step_64 {w ptr : BitVec 64} {off rem : Nat} (n : Nat)
    (h8 : off % 8 = 0) (hle : 8 * n ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (hptr : ptr = w + BitVec.ofNat 64 off) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (array64 ptr xs ⋆
       (region (w + BitVec.ofNat 64 (off + 8 * n)) (rem - 8 * n) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = 8 * n + (rem - 8 * n) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  simpa [hptr] using pop_array64 n h8 (by omega) hm0

theorem aig_pop_alloc {w top : BitVec 64} {A O wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (htop : top.toNat = 776 + align8 (4 * A) + align8 (4 * A) + 4 * O)
    (hm : (region (w + 776#64) (top.toNat - 776) ⋆ region (w + top) (wlen - top.toNat) ⋆ R) m) :
    ∃ rhs0 rhs1 olit : List (BitVec 32),
      rhs0.length = A ∧ rhs1.length = A ∧ olit.length = O ∧
      (arrayPad i32 (w + 776#64) rhs0 ⋆
       arrayPad i32 (w + BitVec.ofNat 64 (776 + align8 (4 * A))) rhs1 ⋆
       array (t := i32) (w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A))) olit ⋆
       region (w + top) (wlen - top.toNat) ⋆ R) m := by
  have h80 : 776 % 8 = 0 := by decide
  have h81 : (776 + align8 (4 * A)) % 8 = 0 := by have := align8_mod (4 * A); omega
  have ha2 : align8 (776 + align8 (4 * A) + align8 (4 * A)) =
      776 + align8 (4 * A) + align8 (4 * A) := by
    have := align8_mod (4 * A); unfold align8; omega
  have hm0 : (region (w + BitVec.ofNat 64 776)
      (align8 (4 * A) + (align8 (4 * A) + 4 * O)) ⋆
      (region (w + top) (wlen - top.toNat) ⋆ R)) m := by
    rw [show top.toNat - 776 = align8 (4 * A) + (align8 (4 * A) + 4 * O) by omega] at hm
    simpa [sep_assoc] using hm
  rw [region_split (n1 := align8 (4 * A)) (n2 := align8 (4 * A) + 4 * O) (by omega),
    sep_assoc, addr_add_ofNat] at hm0
  obtain ⟨rhs0, hr0, hm1⟩ := pop_arrayPad_u32 A h80 (by omega) hm0
  have hm1' := sep_swap2r hm1
  rw [region_split (n1 := align8 (4 * A)) (n2 := 4 * O) (by omega),
    sep_assoc, addr_add_ofNat] at hm1'
  obtain ⟨rhs1, hr1, hm2⟩ := pop_arrayPad_u32 A h81 (by omega) hm1'
  have hm2' := sep_swap2r hm2
  obtain ⟨olit, hol, hm3⟩ :=
    region_pop_alloc_u32 O (by rw [ha2]; omega) (by omega) hm2'
  rw [ha2, Nat.sub_self, region_zero, emp_sep,
    show 4 * O - (0 + 4 * O) = 0 by omega, region_zero,
    show BitVec.ofNat 64 776 = 776#64 from rfl] at hm3
  simp only [sep_emp] at hm3
  have hm3' := sep_pull3r hm3
  have hm3'' := sep_mono_r (fun _ => sep_swap2r) hm3'
  exact ⟨rhs0, rhs1, olit, hr0, hr1, hol, by simpa [sep_assoc] using hm3''⟩

theorem art_tables_pop_alloc {s0 s : ArCtxState} {A O nNets nIn nOut top0 : Nat}
    {rhs0 rhs1 olit : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hg : TablesGeom s A O nNets nIn nOut top0) (htop_fit : top0 ≤ 2 ^ 64)
    (hs0_top : s0.top.toNat = 776 + align8 (4 * A) + align8 (4 * A) + 4 * O)
    (hs_w : s.w = s0.w) (hs_rhs0 : s.rhs0 = s0.rhs0) (hs_rhs1 : s.rhs1 = s0.rhs1)
    (hs_olit : s.olit = s0.olit)
    (hol_ptr : s0.olit = s0.w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A)))
    (hol_len : olit.length = O)
    (hm : (arrayPad i32 s0.rhs0 rhs0 ⋆ (arrayPad i32 s0.rhs1 rhs1 ⋆
      (array (t := i32) s0.olit olit ⋆
       (region (s0.w + s0.top) (top0 - s0.top.toNat) ⋆ R)))) m) :
    ∃ (bindArr ruleOff ruleN partnerArr : List (BitVec 32))
      (flippedArr : List (BitVec 8))
      (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
      (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32))
      (gcl gch : List (BitVec 64)),
      bindArr.length = nNets ∧ ruleOff.length = nNets ∧ ruleN.length = nNets ∧
      partnerArr.length = nNets ∧ flippedArr.length = nNets ∧
      inNetArr.length = nIn ∧ outRefArr.length = nOut ∧
      stkN.length = arTTStk ∧ stkP.length = arTTStk ∧
      memoN.length = arTTMaxAnd ∧ memoV.length = arTTMaxAnd ∧
      dense.length = 128 ∧ gsy.length = 85 ∧ gcl.length = 16 ∧ gch.length = 16 ∧
      (aigArraysMem s rhs0 rhs1 olit ⋆
       netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
       gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ R) m := by
  have haO := align8_ge (4 * O)
  let t0 := 776 + align8 (4 * A) + align8 (4 * A) + align8 (4 * O)
  have hpadO : align8 (4 * O) - 4 * O ≤ top0 - s0.top.toNat := by
    rw [hg.top_eq, tablesEndTop, hs0_top]; dsimp only; omega
  have ht0_mod : t0 % 8 = 0 := by
    have := align8_mod (4 * A); have := align8_mod (4 * O); dsimp only [t0]; omega
  have hm_top0 : top0 = t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) + align8 (4 * nOut) +
      4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd +
      8 * 128 + align8 (4 * 85) + 8 * 16 + 8 * 16 := by
    rw [hg.top_eq, tablesEndTop]
  have haS : align8 (4 * arTTStk) = 4 * arTTStk := by simp only [arTTStk]; decide
  have haM : align8 (4 * arTTMaxAnd) = 4 * arTTMaxAnd := by simp only [arTTMaxAnd]; decide
  have ha85 : align8 (4 * 85) = 344 := by decide
  have hm1 : (arrayPad i32 s0.rhs0 rhs0 ⋆ (arrayPad i32 s0.rhs1 rhs1 ⋆
      ((array (t := i32) s0.olit olit ⋆
        region (s0.olit + BitVec.ofNat 64 (4 * olit.length))
          (align8 (4 * olit.length) - 4 * olit.length)) ⋆
       (region (s0.w + BitVec.ofNat 64 t0) (top0 - t0) ⋆ R)))) m := by
    have hm' := hm
    rw [← addr_add_toNat, hs0_top,
      show top0 - (776 + align8 (4 * A) + align8 (4 * A) + 4 * O) =
        (align8 (4 * O) - 4 * O) + (top0 - t0) by omega,
      region_split (by omega), addr_add_ofNat] at hm'
    have hadd1 : s0.w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A) + 4 * O) =
        s0.olit + BitVec.ofNat 64 (4 * olit.length) := by
      rw [hol_ptr, hol_len, addr_add_ofNat]
    have hadd2 : s0.w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A) + 4 * O +
        (align8 (4 * O) - 4 * O)) = s0.w + BitVec.ofNat 64 t0 := by
      congr 2; omega
    rw [hadd1, hadd2] at hm'
    rw [← hol_len] at hm'
    exact sep_mono_r (fun _ => sep_mono_r (fun _ h => by simpa [sep_assoc] using h)) hm'
  have hm2 : (region (s.w + BitVec.ofNat 64 t0) (top0 - t0) ⋆
      (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
       (arrayPad i32 s.olit olit ⋆ R)))) m := by
    have h0 := sep_mono_r (fun _ => sep_mono_r (fun _ => region_merge_pad_u32)) hm1
    rw [← hs_w, ← hs_rhs0, ← hs_rhs1, ← hs_olit] at h0
    exact sep_pull4r h0
  have hfit_rem : top0 - t0 ≤ 2 ^ 64 := by omega
  have h8n : ∀ k, (k + align8 (4 * nNets)) % 8 = k % 8 := fun k => by
    have := align8_mod (4 * nNets); omega
  have pb := hg.bind_eq
  have pro : s.rule_off = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets)) := by
    rw [hg.rule_off_eq, pb, addr_add_ofNat]
  have prn : s.rule_n = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets)) := by
    rw [hg.rule_n_eq, pro, addr_add_ofNat, Nat.add_assoc]
  have pp : s.partner = s.w + BitVec.ofNat 64
      (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets)) := by
    rw [hg.partner_eq, prn, addr_add_ofNat, Nat.add_assoc]
  have pf : s.flipped = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets)) := by
    rw [hg.flipped_eq, pp, addr_add_ofNat, Nat.add_assoc]
  have pin : s.in_net = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets) := by
    rw [hg.in_net_eq, pf, addr_add_ofNat, Nat.add_assoc]
  have pou : s.out_ref = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn)) := by
    rw [hg.out_ref_eq, pin, addr_add_ofNat, Nat.add_assoc]
  have psn : s.stk_n = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut)) := by
    rw [hg.stk_n_eq, pou, addr_add_ofNat, Nat.add_assoc]
  have psp : s.stk_p = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk) := by
    rw [hg.stk_p_eq, psn, addr_add_ofNat, Nat.add_assoc]
  have pmn : s.memo_n = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk) := by
    rw [hg.memo_n_eq, psp, addr_add_ofNat, Nat.add_assoc]
  have pmv : s.memo_v = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd) := by
    rw [hg.memo_v_eq, pmn, addr_add_ofNat, Nat.add_assoc]
  have pd : s.dense = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd) := by
    rw [hg.dense_eq, pmv, addr_add_ofNat, Nat.add_assoc]
  have pgy : s.gsy = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd +
      8 * 128) := by
    rw [hg.gsy_eq, pd, addr_add_ofNat, Nat.add_assoc]
  have pcl : s.gcl = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd +
      8 * 128 + align8 (4 * 85)) := by
    rw [hg.gcl_eq, pgy, addr_add_ofNat, Nat.add_assoc]
  have pch : s.gch = s.w + BitVec.ofNat 64 (t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) + 4 * arTTStk + 4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd +
      8 * 128 + align8 (4 * 85) + 8 * 16) := by
    rw [hg.gch_eq, pcl, addr_add_ofNat, Nat.add_assoc]
  obtain ⟨bindArr, hb, hm⟩ := pop_step_u32 nNets ht0_mod (by omega) (by omega) pb hm2
  obtain ⟨ruleOff, hro, hm⟩ :=
    pop_step_u32 nNets (by rw [h8n, ht0_mod]) (by omega) (by omega) pro (sep_swap2r hm)
  obtain ⟨ruleN, hrn, hm⟩ :=
    pop_step_u32 nNets (by rw [h8n, h8n, ht0_mod]) (by omega) (by omega) prn (sep_swap2r hm)
  obtain ⟨partnerArr, hp, hm⟩ :=
    pop_step_u32 nNets (by rw [h8n, h8n, h8n, ht0_mod]) (by omega) (by omega) pp (sep_swap2r hm)
  obtain ⟨flippedArr, hf, hm⟩ :=
    pop_step_u8 nNets (by rw [h8n, h8n, h8n, h8n, ht0_mod]) (by omega) (by omega) pf (sep_swap2r hm)
  have hm8_5 : (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets) % 8 = 0 := by
    have := align8_mod (4 * nNets); have := align8_mod nNets; dsimp only [t0] at *; omega
  have hm8_6 : (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets + align8 (4 * nIn)) % 8 = 0 := by
    have := align8_mod (4 * nNets); have := align8_mod nNets; have := align8_mod (4 * nIn)
    dsimp only [t0] at *; omega
  have hm8_7 : (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) + align8 (4 * nOut)) % 8 = 0 := by
    have := align8_mod (4 * nNets); have := align8_mod nNets
    have := align8_mod (4 * nIn); have := align8_mod (4 * nOut)
    dsimp only [t0] at *; omega
  obtain ⟨inNetArr, hin, hm⟩ := pop_step_u32 nIn hm8_5 (by omega) (by omega) pin (sep_swap2r hm)
  obtain ⟨outRefArr, hout, hm⟩ := pop_step_u32 nOut hm8_6 (by omega) (by omega) pou (sep_swap2r hm)
  obtain ⟨stkN, hsn, hm⟩ := pop_step_u32 arTTStk hm8_7 (by rw [haS]; omega)
    (by omega) psn (sep_swap2r hm)
  rw [haS] at hm
  obtain ⟨stkP, hsp, hm⟩ := pop_step_u32 arTTStk (by simp only [arTTStk] at *; omega)
    (by rw [haS]; omega) (by omega) psp (sep_swap2r hm)
  rw [haS] at hm
  obtain ⟨memoN, hmn, hm⟩ := pop_step_u32 arTTMaxAnd (by simp only [arTTStk] at *; omega)
    (by rw [haM]; omega) (by omega) pmn (sep_swap2r hm)
  rw [haM] at hm
  obtain ⟨memoV, hmv, hm⟩ := pop_step_64 arTTMaxAnd
    (by simp only [arTTStk, arTTMaxAnd] at *; omega) (by omega) (by omega) pmv (sep_swap2r hm)
  obtain ⟨dense, hd, hm⟩ := pop_step_64 128
    (by simp only [arTTStk, arTTMaxAnd] at *; omega) (by omega) (by omega) pd (sep_swap2r hm)
  obtain ⟨gsy, hgy, hm⟩ := pop_step_u32 85
    (by simp only [arTTStk, arTTMaxAnd] at *; omega) (by rw [ha85]; omega) (by omega)
    pgy (sep_swap2r hm)
  have hm8_13 : (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) + align8 (4 * nOut) + 4 * arTTStk +
      4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd + 8 * 128 + align8 (4 * 85)) % 8 = 0 := by
    have := align8_mod (4 * nNets); have := align8_mod nNets
    have := align8_mod (4 * nIn); have := align8_mod (4 * nOut)
    simp only [arTTStk, arTTMaxAnd] at *; rw [ha85]; dsimp only [t0] at *; omega
  have hm8_14 : (t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) + align8 (4 * nOut) + 4 * arTTStk +
      4 * arTTStk + 4 * arTTMaxAnd + 8 * arTTMaxAnd + 8 * 128 + align8 (4 * 85) + 8 * 16) % 8 =
      0 := by rw [Nat.add_mod, hm8_13]
  obtain ⟨gcl, hcl, hm⟩ := pop_step_64 16 hm8_13 (by omega) (by omega) pcl (sep_swap2r hm)
  obtain ⟨gch, hch, hm⟩ := pop_step_64 16 hm8_14 (by omega) (by omega) pch (sep_swap2r hm)
  have hm' := sep_swap2r hm
  rw [show top0 - t0 - align8 (4 * nNets) - align8 (4 * nNets) - align8 (4 * nNets) -
      align8 (4 * nNets) - align8 nNets - align8 (4 * nIn) - align8 (4 * nOut) - 4 * arTTStk -
      4 * arTTStk - 4 * arTTMaxAnd - 8 * arTTMaxAnd - 8 * 128 - align8 (4 * 85) - 8 * 16 -
      8 * 16 = 0 by omega, region_zero, emp_sep] at hm'
  refine ⟨bindArr, ruleOff, ruleN, partnerArr, flippedArr, inNetArr, outRefArr,
    stkN, stkP, memoN, memoV, dense, gsy, gcl, gch,
    hb, hro, hrn, hp, hf, hin, hout, hsn, hsp, hmn, hmv, hd, hgy, hcl, hch, ?_⟩
  simp only [aigArraysMem, netTablesMem, gateScratchMem]
  exact sep_cast hm' (by ac_rfl)

end

end LeanQbe.T.Examples.Arisca.Proof
