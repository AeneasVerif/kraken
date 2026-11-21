module

public import LeanQbe.T.Logic.SlabLayoutElab
meta import LeanQbe.T.Logic.SlabLayoutElab

/-!
# End-to-End Tests for `SepTree`, `SlabChain`, `c0_slab_layout!`, and `c0_lens!`

Exercises all Wave-2 slab-layout proof-tooling components:
1. **`MiniLayout` (Mode A — existing sliced `MiniCfg` / `MiniState`, 13-word header + 8 arrays):**
   - `c0_slab_layout!` generating `MiniHdrWords`, `MiniTree`, `MiniMem`, `O(log K)`
     `focus_Mini_*` / `unfocus_Mini_*`, `@[scoped c0_load]` / `@[scoped c0_store]` (including
     `Nat`-backed scalar stores without extra proof obligations and `i8` byte loads/stores),
     and `Mini_to_region` (`SlabChain.to_region`).
   - `c0_lens!` generating `MiniLens_*` + `MiniState.LengthsOk.{upd,set}_*` one-liners.
   - Live `c0_steps` execution (`miniStepProg_wp`: loads/updates both `BitVec 64` `fuel` AND
     `Nat`-backed `arenaLen`, reads `arena[i]`, stores to `lvl[j]`, reads `vals[k]` byte).
   - `O(log K)` focus/unfocus roundtrip (zero `ecancel`), constant-offset sub-buffer load &
     store (`load_Mini_scratch_off` / `store_Mini_scratch_off`), and `regions_to_avail`.
2. **`AutoMiniLayout` (Mode B — `c0_slab_layout! def`, full sliced synthesis):**
   - Generates `AutoMiniCfg`, `AutoMiniState`, `AutoMiniState.LengthsOk`, `AutoMiniLens_*`,
     `AutoMiniMem`, `focus_*`/`unfocus_*`, `@[scoped c0_load/store]`, and **zero-`ecancel`**
     `AutoMini_to_region` via `SlabChain.balancedTree_to_region_eq`.
   - Live `c0_steps` execution + `focus`/`unfocus` on an `align8`-padded `i8` array +
     `hlen.set_arena` one-liner.
3. **Nested sliced state (`SlicedLayout`, `core`/`scratch` split):**
   - Tests `c0_lens!` on 2-level nested `SlicedState.LengthsOk` (`core_ok`/`scratch_ok`) and
     `C0Lens.comp` + `AgreesExcept` framing.
4. **Scoped attribute isolation & `#print axioms` audit:**
   - Confirms all `@[scoped c0_load/store]` lemmas stay confined to their namespace and every
     exported theorem uses only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.SlabLayoutTest

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step

/-! ## 1. Realistic Kissat-Style 13-Word Header + 8-Array Contiguous Slab (`MiniLayout`) -/

structure MiniCfg where
  hdr : BitVec 64
  avail : Nat
  mv : Nat
  maxVars : Nat
  arenaCap : Nat
  scratchCap : Nat
  hmax : maxVars < 2 ^ 28
  harena : arenaCap < 2 ^ 28
  hscr : scratchCap < 2 ^ 28
  hsize : 104 + align8 (2 * maxVars) + align8 maxVars + 12 * maxVars +
    4 * arenaCap + 8 * maxVars + 4 * scratchCap ≤ avail
  hfit : avail ≤ 2 ^ 64

namespace MiniCfg
def pVals (c : MiniCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 104
def pMark (c : MiniCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (align8 (2 * c.maxVars))
def pLvl (c : MiniCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (align8 c.maxVars)
def pRsns (c : MiniCfg) : BitVec 64 := c.pLvl + BitVec.ofNat 64 (4 * c.maxVars)
def pTrl (c : MiniCfg) : BitVec 64 := c.pRsns + BitVec.ofNat 64 (4 * c.maxVars)
def pArena (c : MiniCfg) : BitVec 64 := c.pTrl + BitVec.ofNat 64 (4 * c.maxVars)
def pScore (c : MiniCfg) : BitVec 64 := c.pArena + BitVec.ofNat 64 (4 * c.arenaCap)
def pScratch (c : MiniCfg) : BitVec 64 := c.pScore + BitVec.ofNat 64 (8 * c.maxVars)
def pSlack (c : MiniCfg) : BitVec 64 := c.pScratch + BitVec.ofNat 64 (4 * c.scratchCap)
def slack (c : MiniCfg) : Nat :=
  c.avail - (104 + align8 (2 * c.maxVars) + align8 c.maxVars + 12 * c.maxVars +
    4 * c.arenaCap + 8 * c.maxVars + 4 * c.scratchCap)

def padMem (c : MiniCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.maxVars)) (align8 (2 * c.maxVars) - 2 * c.maxVars) ⋆
  region (c.pMark + BitVec.ofNat 64 c.maxVars) (align8 c.maxVars - c.maxVars) ⋆
  region c.pSlack c.slack
end MiniCfg

structure MiniState where
  arenaLen : Nat
  trailEnd : Nat
  fuel : BitVec 64
  vals : List (BitVec 8)
  mark : List (BitVec 8)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  trl : List (BitVec 32)
  arena : List (BitVec 32)
  score : List (BitVec 64)
  scratch : List (BitVec 32)

structure MiniState.LengthsOk (c : MiniCfg) (s : MiniState) : Prop where
  vals_len : s.vals.length = 2 * c.maxVars
  mark_len : s.mark.length = c.maxVars
  lvl_len : s.lvl.length = c.maxVars
  rsns_len : s.rsns.length = c.maxVars
  trl_len : s.trl.length = c.maxVars
  arena_len : s.arena.length = c.arenaCap
  score_len : s.score.length = c.maxVars
  scratch_len : s.scratch.length = c.scratchCap

namespace MiniLayout

c0_lens! Mini (s : MiniState) lengths (c : MiniCfg) MiniState.LengthsOk {
  scalar arenaLen : Nat       := s.arenaLen | fun n  => { s with arenaLen := n },
  scalar trailEnd : Nat       := s.trailEnd | fun n  => { s with trailEnd := n },
  scalar fuel     : BitVec 64 := s.fuel     | fun v  => { s with fuel := v },
  arr    vals     : BitVec 8  := s.vals     | fun xs => { s with vals := xs },
  arr    mark     : BitVec 8  := s.mark     | fun xs => { s with mark := xs },
  arr    lvl      : BitVec 32 := s.lvl      | fun xs => { s with lvl := xs },
  arr    rsns     : BitVec 32 := s.rsns     | fun xs => { s with rsns := xs },
  arr    trl      : BitVec 32 := s.trl      | fun xs => { s with trl := xs },
  arr    arena    : BitVec 32 := s.arena    | fun xs => { s with arena := xs },
  arr    score    : BitVec 64 := s.score    | fun xs => { s with score := xs },
  arr    scratch  : BitVec 32 := s.scratch  | fun xs => { s with scratch := xs }
}

c0_slab_layout! Mini (c : MiniCfg) (s : MiniState)
  (hdrBase := c.hdr)
  (withPad := c.padMem)
  header {
    hconst_nat mv       := c.mv,
    hconst_nat maxVars  := c.maxVars,
    hmut_nat   arenaLen := s.arenaLen | fun n => { s with arenaLen := n },
    hmut_nat   trailEnd := s.trailEnd | fun n => { s with trailEnd := n },
    hmut       fuel     := s.fuel     | fun v => { s with fuel := v },
    hconst     pVals    := c.pVals,
    hconst     pMark    := c.pMark,
    hconst     pLvl     := c.pLvl,
    hconst     pRsns    := c.pRsns,
    hconst     pTrl     := c.pTrl,
    hconst     pArena   := c.pArena,
    hconst     pScore   := c.pScore,
    hconst     pScratch := c.pScratch
  }
  arrays {
    vals    : i8  | pVals    := s.vals    | (fun xs => { s with vals := xs })
      ; len (2 * c.maxVars) | align8,
    mark    : i8  | pMark    := s.mark    | (fun xs => { s with mark := xs })
      ; len c.maxVars | align8,
    lvl     : i32 | pLvl     := s.lvl     | (fun xs => { s with lvl := xs })
      ; len c.maxVars,
    rsns    : i32 | pRsns    := s.rsns    | (fun xs => { s with rsns := xs })
      ; len c.maxVars,
    trl     : i32 | pTrl     := s.trl     | (fun xs => { s with trl := xs })
      ; len c.maxVars,
    arena   : i32 | pArena   := s.arena   | (fun xs => { s with arena := xs })
      ; len c.arenaCap,
    score   : i64 | pScore   := s.score   | (fun xs => { s with score := xs })
      ; len c.maxVars,
    scratch : i32 | pScratch := s.scratch | (fun xs => { s with scratch := xs })
      ; len c.scratchCap
  }
  to_region (hlen : s.LengthsOk c) {
    total  := c.avail,
    slack  := c.slack,
    fit    := c.hfit,
    bounds := [c.hsize],
    unfold := [MiniCfg.slack, MiniCfg.padMem, MiniCfg.pSlack]
  }

/-- End-to-end `c0_steps` execution using generated `MiniLayout` `@[scoped c0_load/store]`:
loads/decrements `fuel` (`hdr + 32`), loads/increments `Nat`-backed `arenaLen` (`hdr + 16`),
loads `arena[i]`, stores it into `lvl[j]`, reads byte `vals[k]`, and returns `arena[i]`. -/
def miniStepProg (h : BitVec 64) (i j k : BitVec 32) : Expr Val Cont [i32] :=
  .load i64 (.imm (h + 32)) fun fuel =>
  .let_ (op2 (.sub i64) (.var fuel) (.imm 1#64)) fun (fuel', ()) =>
  .store (.var fuel') (.imm (h + 32)) <|
  .load i64 (.imm (h + 16)) fun alen =>
  .let_ (op2 (.add i64) (.var alen) (.imm 1#64)) fun (alen', ()) =>
  .store (.var alen') (.imm (h + 16)) <|
  .load i64 (.imm (h + 80)) fun pArena =>
  .let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
  .let_ (op2 (.mul i64) (.var i64v) (.imm 4#64)) fun (ioff, ()) =>
  .let_ (op2 (.add i64) (.var pArena) (.var ioff)) fun (pa, ()) =>
  .load i32 (.var pa) fun aval =>
  .load i64 (.imm (h + 56)) fun pLvl =>
  .let_ (op1 (.zext 32 64) (.var j)) fun (j64v, ()) =>
  .let_ (op2 (.mul i64) (.var j64v) (.imm 4#64)) fun (joff, ()) =>
  .let_ (op2 (.add i64) (.var pLvl) (.var joff)) fun (pl, ()) =>
  .store (.var aval) (.var pl) <|
  .load i64 (.imm (h + 40)) fun pVals =>
  .let_ (op1 (.zext 32 64) (.var k)) fun (k64v, ()) =>
  .let_ (op2 (.add i64) (.var pVals) (.var k64v)) fun (pv, ()) =>
  .load i8 (.var pv) fun _vbyte =>
  .ret (.var aval, ())

theorem miniStepProg_wp (Γ : Env) (Q : Post [i32]) (X : XPost)
    (c : MiniCfg) (s : MiniState) (R : Mem 64 → Prop) (m : Mem 64)
    (i j k : BitVec 32)
    (hi : i.toNat < s.arena.length) (hj : j.toNat < s.lvl.length) (hk : k.toNat < s.vals.length)
    (hm : (MiniMem c s ⋆ R) m)
    (hQ : ∀ m', (MiniMem c { s with
        fuel := s.fuel - 1#64,
        arenaLen := (BitVec.ofNat 64 s.arenaLen + 1#64).toNat,
        lvl := s.lvl.set j.toNat (s.arena[i.toNat]'hi) } ⋆ R) m' →
      Q (s.arena[i.toNat]'hi, ()) m') :
    wp Γ Q X (miniStepProg c.hdr i j k) m := by
  unfold miniStepProg
  c0_steps
  exact hQ _ (by assumption)

/-- `O(log K)` focus → direct `array` store → unfocus with zero `ecancel`. -/
theorem mini_focus_unfocus_roundtrip (c : MiniCfg) (s : MiniState) (R : Mem 64 → Prop)
    (m : Mem 64) (i : BitVec 32) (v : BitVec 32) (hi : i.toNat < s.scratch.length)
    (hm : (MiniMem c s ⋆ R) m) :
    ∃ m', (MiniMem c { s with scratch := s.scratch.set i.toNat v } ⋆ R) m' := by
  have hf := focus_Mini_scratch hm
  obtain ⟨_, hst⟩ := c0_store_array32_u32 v hf hi
  exact ⟨_, unfocus_Mini_scratch hst⟩

/-- Parameterized sub-buffer offset load (`c.pScratch + 4096#64 + i * 4#64`). -/
theorem mini_scratch_subbuf_load (c : MiniCfg) (s : MiniState) (R : Mem 64 → Prop) (m : Mem 64)
    (i : BitVec 64) (hi : 1024 + i.toNat < s.scratch.length) (hm : (MiniMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratch + 4096#64 + i * 4#64) = some (s.scratch[1024 + i.toNat]'hi) :=
  load_Mini_scratch_off 1024 rfl hi hm

/-- Parameterized sub-buffer offset store (`c.pScratch + 4096#64 + i * 4#64`). -/
theorem mini_scratch_subbuf_store (c : MiniCfg) (s : MiniState) (R : Mem 64 → Prop) (m : Mem 64)
    (v : BitVec 32) (i : BitVec 64) (hi : 1024 + i.toNat < s.scratch.length)
    (hm : (MiniMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratch + 4096#64 + i * 4#64) ∧
      (MiniMem c { s with scratch := s.scratch.set (1024 + i.toNat) v } ⋆ R)
        (storeMem m i32 (c.pScratch + 4096#64 + i * 4#64) v) :=
  store_Mini_scratch_off 1024 rfl v hi hm

/-- `regions_to_avail` generated by `c0_slab_layout!` via `SlabChain.to_region_eq`. -/
theorem mini_regions_to_avail (c : MiniCfg) (s : MiniState) (hlen : s.LengthsOk c) {m : Mem 64}
    (hm : MiniMem c s m) : region c.hdr c.avail m :=
  Mini_to_region c s hlen hm

/-- `c0_lens!` `LengthsOk` preservation one-liners (`hlen.set_*`). -/
theorem mini_lengths_preserved (c : MiniCfg) (s : MiniState) (hlen : s.LengthsOk c)
    (i : Nat) (v : BitVec 32) (f : BitVec 64) :
    ({ s with arena := s.arena.set i v, fuel := f } : MiniState).LengthsOk c :=
  (hlen.set_arena i v).set_fuel f

end MiniLayout

/-! ## 2. Mode B (`c0_slab_layout! def`): Full Sliced Synthesis + Zero-`ecancel` `to_region` -/

namespace AutoMiniLayout

c0_slab_layout! def AutoMini (c)
  params {
    mv         : Nat,
    maxVars    : Nat,
    arenaCap   : Nat,
    scratchCap : Nat
  }
  scalars {
    nat  arenaLen,
    nat  trailEnd,
    bv64 fuel
  }
  arrays {
    vals    : i8  | len (2 * c.maxVars) | align8,
    mark    : i8  | len c.maxVars       | align8,
    lvl     : i32 | len c.maxVars,
    arena   : i32 | len c.arenaCap,
    score   : i64 | len c.maxVars,
    scratch : i32 | len c.scratchCap
  }

/-- Zero-`ecancel` `regions_to_avail` from `SlabChain.balancedTree_to_region_eq`. -/
theorem autoMini_regions_to_avail (c : AutoMiniCfg) (s : AutoMiniState)
    (hsize : c.SizeOk) (hlen : s.LengthsOk c) {m : Mem 64} (hm : AutoMiniMem c s m) :
    region c.hdr c.avail m :=
  AutoMini_to_region c s hsize hlen hm

/-- `O(log K)` focus/unfocus on an `align8`-padded `i8` array leaf (zero `ecancel`). -/
theorem autoMini_focus_unfocus_vals (c : AutoMiniCfg) (s : AutoMiniState) (R : Mem 64 → Prop)
    (m : Mem 64) (i : BitVec 32) (b : BitVec 8) (hi : i.toNat < s.vals.length)
    (hm : (AutoMiniMem c s ⋆ R) m) :
    ∃ m', (AutoMiniMem c { s with vals := s.vals.set i.toNat b } ⋆ R) m' := by
  have hf := focus_AutoMini_vals hm
  obtain ⟨_, hst⟩ := c0_store_array8_u32 b hf hi
  exact ⟨_, unfocus_AutoMini_vals hst⟩

/-- Live `c0_steps` on Mode-B generated `AutoMini`: reads `mv` (offset 0!), updates `fuel`
(offset 48), loads `vals[k]` (padded `i8` leaf!), stores `arena[i]` → `lvl[j]`. -/
def autoProg (h : BitVec 64) (i j k : BitVec 32) : Expr Val Cont [i64] :=
  .load i64 (.imm h) fun mv =>
  .load i64 (.imm (h + 48)) fun fuel =>
  .let_ (op2 (.sub i64) (.var fuel) (.imm 1#64)) fun (fuel', ()) =>
  .store (.var fuel') (.imm (h + 48)) <|
  .load i64 (.imm (h + 56)) fun pVals =>
  .let_ (op1 (.zext 32 64) (.var k)) fun (k64, ()) =>
  .let_ (op2 (.add i64) (.var pVals) (.var k64)) fun (pv, ()) =>
  .load i8 (.var pv) fun b =>
  .store (.var b) (.var pv) <|
  .load i64 (.imm (h + 80)) fun pArena =>
  .let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
  .let_ (op2 (.mul i64) (.var i64v) (.imm 4#64)) fun (ioff, ()) =>
  .let_ (op2 (.add i64) (.var pArena) (.var ioff)) fun (pa, ()) =>
  .load i32 (.var pa) fun aval =>
  .load i64 (.imm (h + 72)) fun pLvl =>
  .let_ (op1 (.zext 32 64) (.var j)) fun (j64v, ()) =>
  .let_ (op2 (.mul i64) (.var j64v) (.imm 4#64)) fun (joff, ()) =>
  .let_ (op2 (.add i64) (.var pLvl) (.var joff)) fun (pl, ()) =>
  .store (.var aval) (.var pl) <|
  .ret (.var mv, ())

theorem autoProg_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (c : AutoMiniCfg) (s : AutoMiniState) (R : Mem 64 → Prop) (m : Mem 64)
    (i j k : BitVec 32)
    (hi : i.toNat < s.arena.length) (hj : j.toNat < s.lvl.length) (hk : k.toNat < s.vals.length)
    (hm : (AutoMiniMem c s ⋆ R) m)
    (hQ : ∀ m', (AutoMiniMem c { s with
        fuel := s.fuel - 1#64,
        vals := s.vals.set k.toNat (s.vals[k.toNat]'hk),
        lvl := s.lvl.set j.toNat (s.arena[i.toNat]'hi) } ⋆ R) m' →
      Q (BitVec.ofNat 64 c.mv, ()) m') :
    wp Γ Q X (autoProg c.hdr i j k) m := by
  unfold autoProg
  c0_steps
  exact hQ _ (by assumption)

theorem autoMini_lengths_one_liner (c : AutoMiniCfg) (s : AutoMiniState) (hlen : s.LengthsOk c)
    (i : Nat) (v : BitVec 32) (n : Nat) :
    ({ s with arena := s.arena.set i v, arenaLen := n } : AutoMiniState).LengthsOk c :=
  (hlen.set_arena i v).set_arenaLen n

end AutoMiniLayout

/-! ## 3. Nested 2-Level Sliced State (`core` / `scratch`) with `c0_lens!` & `C0Lens.comp` -/

structure SlicedCfg where
  maxVars : Nat
  arenaCap : Nat

structure SlicedCore where
  arenaLen : Nat
  arena : List (BitVec 32)

structure SlicedScratch where
  ticks : BitVec 64
  heap : List (BitVec 32)

structure SlicedState where
  core : SlicedCore
  scratch : SlicedScratch

structure SlicedCore.LengthsOk (c : SlicedCfg) (k : SlicedCore) : Prop where
  arena_len : k.arena.length = c.arenaCap
  arena_le : k.arenaLen ≤ c.arenaCap

structure SlicedScratch.LengthsOk (c : SlicedCfg) (sc : SlicedScratch) : Prop where
  heap_len : sc.heap.length = c.maxVars

structure SlicedState.LengthsOk (c : SlicedCfg) (s : SlicedState) : Prop where
  core_ok : s.core.LengthsOk c
  scratch_ok : s.scratch.LengthsOk c

namespace SlicedLayout

c0_lens! Core (k : SlicedCore) {
  bscalar arenaLen : Nat       := k.arenaLen | fun n  => { k with arenaLen := n },
  arr     arena    : BitVec 32 := k.arena    | fun xs => { k with arena := xs }
}

c0_lens! Sliced (s : SlicedState) lengths (c : SlicedCfg) SlicedState.LengthsOk {
  bscalar core     : SlicedCore    := s.core          | fun k  => { s with core := k },
  scalar  ticks    : BitVec 64     := s.scratch.ticks | fun t  =>
    { s with scratch := { s.scratch with ticks := t } },
  arr     arena    : BitVec 32     := s.core.arena    | fun xs =>
    { s with core := { s.core with arena := xs } },
  arr     heap     : BitVec 32     := s.scratch.heap  | fun xs =>
    { s with scratch := { s.scratch with heap := xs } }
}

/-- Composed lens `SlicedLens_core.comp CoreLens_arena` agrees with direct `SlicedLens_arena`. -/
theorem sliced_lens_comp_eq (s : SlicedState) (xs : List (BitVec 32)) :
    (SlicedLens_core.comp CoreLens_arena).set s xs = SlicedLens_arena.set s xs := rfl

/-- Nested 2-level `LengthsOk` preservation in one line. -/
theorem sliced_nested_lengths (c : SlicedCfg) (s : SlicedState) (hlen : s.LengthsOk c)
    (i j : Nat) (v w : BitVec 32) (t : BitVec 64) :
    ({ s with
        core := { s.core with arena := s.core.arena.set i v },
        scratch := { s.scratch with heap := s.scratch.heap.set j w, ticks := t } } :
      SlicedState).LengthsOk c :=
  ((hlen.set_arena i v).set_heap j w).set_ticks t

/-- Lens + `AgreesExcept` framing for scratch-only mutations. -/
theorem sliced_scratch_agrees (s : SlicedState) (i : Nat) (v : BitVec 32) :
    AgreesExcept (fun t : SlicedState => { t with scratch := s.scratch })
      s (SlicedLens_heap.set_list s i v) :=
  SlicedLens_heap.agreesExcept_set (fun t => { t with scratch := s.scratch }) s _

end SlicedLayout

/-! ## 4. Axioms Verification (Strictly Standard Axioms Only) -/

#print axioms SepTree.eval_eq_focus
#print axioms SepTree.focus
#print axioms SepTree.unfocus_eq
#print axioms SlabChain.to_region
#print axioms SlabChain.balancedTree_to_region
#print axioms MiniLayout.mini_regions_to_avail
#print axioms MiniLayout.miniStepProg_wp
#print axioms MiniLayout.mini_focus_unfocus_roundtrip
#print axioms MiniLayout.mini_scratch_subbuf_load
#print axioms MiniLayout.mini_scratch_subbuf_store
#print axioms MiniLayout.mini_lengths_preserved
#print axioms AutoMiniLayout.autoMini_regions_to_avail
#print axioms AutoMiniLayout.autoMini_focus_unfocus_vals
#print axioms AutoMiniLayout.autoProg_wp
#print axioms AutoMiniLayout.autoMini_lengths_one_liner
#print axioms SlicedLayout.sliced_nested_lengths
#print axioms SlicedLayout.sliced_scratch_agrees

end LeanQbeTest.T.SlabLayoutTest
