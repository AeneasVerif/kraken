module

public import LeanQbeTest.T.RegaLitmusProgs
public import LeanQbe.T.RegaLemmas
import all Kraken.Mem

/-!
# `T7b` Litmus Witnesses (`*_nonvacuous`) and `lowerFn_correct` Hooks

* §1 Kernel-reducible function memory `FMem` and the simulation `runG_rel`: a run of the generic
  machine over `FMem` (evaluated by the kernel) is a run of `mach` over `Mem 64`.
* §2 `eventually_of_runG`: any fuel-bounded run is an `Eventually (mach.step host)` derivation.
* §3 Concrete hosts (lowered code, plus callee code for `carryCall`), concrete initial states, and
  `*_nonvacuous` theorems: execution returns to the return address with the expected results.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.RegaLitmus
open LeanQbe.T

/-! ## 1. Function Memory and the Memory Simulation -/

abbrev FMem : Type := BitVec 64 → Option UInt8

def fmemOps : MemOps FMem :=
  ⟨fun f k => f k, fun f a bs k => if (k - a).toNat < bs.length then bs[(k - a).toNat]? else f k⟩

def MemRel (m : Mem 64) (f : FMem) : Prop := ∀ k, m.get? k = f k

def SRel (s : MData) (t : MDataG FMem) : Prop :=
  s.gpr = t.gpr ∧ s.vec = t.vec ∧ s.cf = t.cf ∧ s.zf = t.zf ∧ s.of = t.of ∧ MemRel s.mem t.mem

theorem loadValG_rel {m : Mem 64} {f : FMem} (hm : MemRel m f) (t : Ty) (a : BitVec 64) :
    loadValG memOps m t a = loadValG fmemOps f t a := by
  have hm' : ∀ k, m.get? k = f k := hm
  simp only [loadValG, memOps, fmemOps, hm']

theorem put_rel {m : Mem 64} {f : FMem} (hm : MemRel m f) (a : BitVec 64) (bs : List UInt8)
    (hl : bs.length ≤ 2 ^ 64) : MemRel (memOps.put m a bs) (fmemOps.put f a bs) := by
  intro k
  have hk := hm k
  rw [Std.ExtHashMap.get?_eq_getElem?] at hk
  simp only [memOps, fmemOps, Mem.storeBytes]
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union,
    get?_At bs a k hl, hk]
  generalize (k - a).toNat = j
  by_cases h : j < bs.length
  · simp only [h, ↓reduceIte, List.getElem?_eq_getElem h, Option.some_or]
  · simp only [h, ↓reduceIte, List.getElem?_eq_none (Nat.le_of_not_lt h), Option.none_or]

theorem i64_bytes_le : (i64).bytes ≤ 2 ^ 64 := by simp [Ty.bytes, Ty.size]

/-- Stores of types wider than the address space are excluded from the simulation. -/
def instrOk : Instr → Bool
  | .st t _ _ => Nat.ble t.bytes (2 ^ 64)
  | _ => true

theorem storeMemG_rel {m : Mem 64} {f : FMem} (hm : MemRel m f) {t : Ty} (a : BitVec 64)
    (v : Val t) (ht : t.bytes ≤ 2 ^ 64) :
    MemRel (storeMemG memOps m t a v) (storeMemG fmemOps f t a v) :=
  put_rel hm a _ (by rw [Int.toBytes_length]; exact ht)

theorem storeWords_rel {m : Mem 64} {f : FMem} (hm : MemRel m f) (a : BitVec 64)
    (ws : List (BitVec 64)) : MemRel (storeWords memOps m a ws) (storeWords fmemOps f a ws) := by
  induction ws generalizing m f a with
  | nil => exact hm
  | cons w ws ih =>
    simp only [storeWords]
    exact ih (storeMemG_rel (t := i64) hm a w i64_bytes_le) _

theorem loadWords_rel {m : Mem 64} {f : FMem} (hm : MemRel m f) (a : BitVec 64) (k : Nat) :
    loadWords memOps m a k = loadWords fmemOps f a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [loadWords, loadValG_rel hm, ih]

def ORel : Option (MData × Nat) → Option (MDataG FMem × Nat) → Prop
  | none, none => True
  | some (s, p), some (t, q) => SRel s t ∧ p = q
  | _, _ => False

theorem execI_rel {h : LHost} {s : MData} {t : MDataG FMem} {pc : Nat} {i : Instr}
    (hs : SRel s t) (hi : instrOk i = true) :
    ORel (execI memOps h s pc i) (execI fmemOps h t pc i) := by
  obtain ⟨g, v, c, z, o, m⟩ := s
  obtain ⟨g', v', c', z', o', f⟩ := t
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hm⟩ := hs
  change MemRel m f at hm
  cases i with
  | ld ty d a =>
    have ha : (⟨g, v, c, z, o, m⟩ : MData).addr a = (⟨g, v, c, z, o, f⟩ : MDataG FMem).addr a := by
      cases a <;> rfl
    simp only [execI, loadValG_rel hm, ha]
    cases loadValG fmemOps f ty _ with
    | none => trivial
    | some x => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hm⟩, rfl⟩
  | ret =>
    simp only [execI, loadValG_rel hm]
    cases loadValG fmemOps f i64 _ with
    | none => trivial
    | some x => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hm⟩, rfl⟩
  | vld w d k =>
    simp only [execI, loadWords_rel hm]
    cases loadWords fmemOps f _ _ with
    | none => trivial
    | some x => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hm⟩, rfl⟩
  | st ty x a =>
    simp only [instrOk, Nat.ble_eq] at hi
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, storeMemG_rel hm _ _ hi⟩, rfl⟩
  | call l => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, storeMemG_rel (t := i64) hm _ _ i64_bytes_le⟩, rfl⟩
  | vst w k x => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, storeWords_rel hm _ _⟩, rfl⟩
  | _ => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hm⟩, rfl⟩

/-! ## 2. Fuel-Bounded Runs -/

/-- Run until stuck (e.g. after returning outside the program) or out of fuel. -/
def runG {M : Type} (ops : MemOps M) (h : LHost) : Nat → MDataG M × Nat → MDataG M × Nat
  | 0, st => st
  | n + 1, st => match execG ops h st with
    | some st' => runG ops h n st'
    | none => st

theorem eventually_of_runG {h : LHost} {P : mach.State → Prop} :
    ∀ (n : Nat) (st : MData × Nat), P (runG memOps h n st) → Eventually (mach.step h) P st
  | 0, _, hp => .done _ hp
  | n + 1, st, hp => by
    simp only [runG] at hp
    split at hp
    · rename_i st' he
      exact step_cps _ _ _ ⟨st', he, eventually_of_runG n st' hp⟩
    · exact .done _ hp

def progOk (h : LHost) : Bool := h.prog.all instrOk

theorem runG_rel {h : LHost} (hok : progOk h = true) :
    ∀ (n : Nat) {s : MData} {t : MDataG FMem} {pc : Nat}, SRel s t →
      SRel (runG memOps h n (s, pc)).1 (runG fmemOps h n (t, pc)).1 ∧
        (runG memOps h n (s, pc)).2 = (runG fmemOps h n (t, pc)).2
  | 0, _, _, _, hs => ⟨hs, rfl⟩
  | n + 1, s, t, pc, hs => by
    simp only [runG, execG]
    cases hp : h.prog[pc]? with
    | none => exact ⟨hs, rfl⟩
    | some i =>
      have hi : instrOk i = true :=
        List.all_eq_true.mp hok i (List.mem_of_getElem? hp)
      have hr := execI_rel (h := h) (pc := pc) hs hi
      dsimp only
      generalize execI memOps h s pc i = A at hr ⊢
      generalize execI fmemOps h t pc i = B at hr ⊢
      rcases A with _ | ⟨s', p⟩ <;> rcases B with _ | ⟨t', q⟩
      · exact ⟨hs, rfl⟩
      · exact hr.elim
      · exact hr.elim
      · obtain ⟨hs', rfl⟩ := hr
        exact runG_rel hok n hs'

/-- Transfer a kernel-evaluated `FMem` run to an `Eventually` derivation of `mach`. -/
theorem eventually_of_runG_rel {h : LHost} (hok : progOk h = true) {P : mach.State → Prop}
    (n : Nat) {s : MData} {t : MDataG FMem} {pc : Nat} (hs : SRel s t)
    (hp : ∀ st : MData × Nat, SRel st.1 (runG fmemOps h n (t, pc)).1 →
      st.2 = (runG fmemOps h n (t, pc)).2 → P st) :
    Eventually (mach.step h) P (s, pc) :=
  eventually_of_runG n _ (hp _ (runG_rel hok n hs).1 (runG_rel hok n hs).2)

/-! ## 3. Concrete Initial States and the Return Check -/

def initMem (ws : List (BitVec 64 × List UInt8)) : Mem 64 :=
  ws.foldl (fun m p => memOps.put m p.1 p.2) ∅

def initFMem (ws : List (BitVec 64 × List UInt8)) : FMem :=
  ws.foldl (fun f p => fmemOps.put f p.1 p.2) (fun _ => none)

theorem initMem_rel (ws : List (BitVec 64 × List UInt8)) (hws : ws.all (Nat.ble ·.2.length 64) = true) :
    MemRel (initMem ws) (initFMem ws) := by
  suffices ∀ (ws : List (BitVec 64 × List UInt8)) (m : Mem 64) (f : FMem), MemRel m f →
      ws.all (Nat.ble ·.2.length 64) = true →
      MemRel (ws.foldl (fun m p => memOps.put m p.1 p.2) m)
        (ws.foldl (fun f p => fmemOps.put f p.1 p.2) f) from
    this ws _ _ (fun k => by simp) hws
  intro ws
  induction ws with
  | nil => intro m f hm _; exact hm
  | cons p ws ih =>
    intro m f hm hall
    simp only [List.all_cons, Bool.and_eq_true, Nat.ble_eq] at hall
    exact ih _ _ (put_rel hm p.1 p.2 (Nat.le_trans hall.1 (by decide))) hall.2

/-- Register file from an association list (unlisted registers are `0`). -/
def regFile (rs : List (Nat × BitVec 64)) : Nat → BitVec 64 := fun r => (rs.lookup r).getD 0

def mkSt {M : Type} (rs : List (Nat × BitVec 64)) (m : M) : MDataG M :=
  ⟨regFile rs, fun _ => 0, false, false, false, m⟩

theorem mkSt_rel {rs : List (Nat × BitVec 64)} {m : Mem 64} {f : FMem} (hm : MemRel m f) :
    SRel (mkSt rs m) (mkSt rs f) := ⟨rfl, rfl, rfl, rfl, rfl, hm⟩

/-- The 8 little-endian bytes of a return address. -/
def raBytes (ra : Nat) : List UInt8 := Int.toBytes 8 (BitVec.ofNat 64 ra).toInt

/-- Returned to `ra` with `rsp = sp + 8`, GPR results `rets`, and vector results `vrets`
(low 64 bits). -/
def Returns (ra : Nat) (sp : BitVec 64) (rets vrets : List (Nat × BitVec 64))
    (st : mach.State) : Prop :=
  st.2 = ra ∧ st.1.gpr 4 = sp + 8 ∧ (∀ p ∈ rets, st.1.gpr p.1 = p.2) ∧
    ∀ p ∈ vrets, (st.1.vec p.1).setWidth 64 = p.2

def checkRet (r : MDataG FMem × Nat) (ra : Nat) (sp : BitVec 64)
    (rets vrets : List (Nat × BitVec 64)) : Bool :=
  r.2 == ra && r.1.gpr 4 == sp + 8 && rets.all (fun p => r.1.gpr p.1 == p.2) &&
    vrets.all (fun p => (r.1.vec p.1).setWidth 64 == p.2)

theorem returns_of_check {h : LHost} (hok : progOk h = true) (n : Nat) {s : MData}
    {t : MDataG FMem} {pc : Nat} (hs : SRel s t) {ra : Nat} {sp : BitVec 64}
    {rets vrets : List (Nat × BitVec 64)}
    (hc : checkRet (runG fmemOps h n (t, pc)) ra sp rets vrets = true) :
    Eventually (mach.step h) (Returns ra sp rets vrets) (s, pc) := by
  refine eventually_of_runG_rel hok n hs fun st hst hpc => ?_
  obtain ⟨hg, hv, -⟩ := hst
  simp only [checkRet, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨hpc.trans h1, ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hg]; exact h2
  · rw [hg]; exact h3 p hp
  · rw [hv]; exact h4 p hp

/-! ## 4. `*_nonvacuous` Witnesses (concrete hosts = lowered code) -/

/-- Initial stack pointer and return address of every witness (`ra` lies outside the program,
so execution stops right after the final `ret`). -/
abbrev sp0 : BitVec 64 := 0x1000#64
abbrev ra0 : Nat := 0x1234
abbrev stackInit : List (BitVec 64 × List UInt8) := [(sp0, raBytes ra0)]

def mkHost (c : List Instr) (h : Nat.ble (c.length + 1) (2 ^ 64) = true) : LHost :=
  ⟨c, Nat.le_of_ble_eq_true h⟩

def hostBranches : LHost := mkHost codeBranches (by t_kernel_rfl)
def hostLoop : LHost := mkHost codeLoop (by t_kernel_rfl)
def hostEvenOdd : LHost := mkHost codeEvenOdd (by t_kernel_rfl)
def hostNested : LHost := mkHost codeNested (by t_kernel_rfl)
def hostPairLoop : LHost := mkHost codePairLoop (by t_kernel_rfl)
def hostVecLoop : LHost := mkHost codeVecLoop (by t_kernel_rfl)
/-- Callee code followed by the caller's code. -/
def hostCarryCall : LHost := mkHost (codeInc ++ codeCarryCall) (by t_kernel_rfl)
def hostBits8 : LHost := mkHost codeBits8 (by t_kernel_rfl)
def hostCmpJcc : LHost := mkHost codeCmpJcc (by t_kernel_rfl)
def hostAdcChain : LHost := mkHost codeAdcChain (by t_kernel_rfl)
def hostAdcxAdox : LHost := mkHost codeAdcxAdox (by t_kernel_rfl)
def hostCfLoop : LHost := mkHost codeCfLoop (by t_kernel_rfl)
def hostAddrDisp : LHost := mkHost codeAddrDisp (by t_kernel_rfl)
def hostAddrCall : LHost := mkHost (codeInc ++ codeAddrCall) (by t_kernel_rfl)
def hostAddrSib : LHost := mkHost codeAddrSib (by t_kernel_rfl)

abbrev ones64 : BitVec 64 := 0xFFFFFFFFFFFFFFFF#64

/-! ### `G12a` -/

/-- `branches 3 10 = |3 - 10| + 1 = 8` (taken `jcc` on `CF`, join block). -/
theorem branches_nonvacuous :
    Eventually (mach.step hostBranches) (Returns ra0 sp0 [(0, 8#64)] [])
      (mkSt [(4, sp0), (7, 3#64), (6, 10#64)] (initMem stackInit),
        labelAddr hostBranches "branches") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `loop 5 = 5 + 4 + 3 + 2 + 1 = 15`. -/
theorem loop_nonvacuous :
    Eventually (mach.step hostLoop) (Returns ra0 sp0 [(0, 15#64)] [])
      (mkSt [(4, sp0), (7, 5#64)] (initMem stackInit), labelAddr hostLoop "loop") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `evenOdd 7 1`: enters the irreducible cycle at `odd`, `odd 7 = 1`. -/
theorem evenOdd_nonvacuous :
    Eventually (mach.step hostEvenOdd) (Returns ra0 sp0 [(0, 1#64)] [])
      (mkSt [(4, sp0), (7, 7#64), (6, 1#64)] (initMem stackInit),
        labelAddr hostEvenOdd "evenOdd") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `nested 3 4 = 12`. -/
theorem nested_nonvacuous :
    Eventually (mach.step hostNested) (Returns ra0 sp0 [(0, 12#64)] [])
      (mkSt [(4, sp0), (7, 3#64), (6, 4#64)] (initMem stackInit), labelAddr hostNested "nested") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `pairLoop 5 = (15, true)` (`bool` result `1` in `rdx`). -/
theorem pairLoop_nonvacuous :
    Eventually (mach.step hostPairLoop) (Returns ra0 sp0 [(0, 15#64), (2, 1#64)] [])
      (mkSt [(4, sp0), (7, 5#64)] (initMem stackInit), labelAddr hostPairLoop "pairLoop") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `vecLoop 3 = (8, 16)` from the `vmovi`-materialised `(1, 2)`: lanes `8` (low) and `16` (high)
of `zmm0`. -/
theorem vecLoop_nonvacuous :
    Eventually (mach.step hostVecLoop) (Returns ra0 sp0 [] [(0, 0x0000001000000008#64)])
      (mkSt [(4, sp0), (7, 3#64)] (initMem stackInit), labelAddr hostVecLoop "vecLoop") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `carryCall (2^64-1) 1 5`: `s0 = 0`, carry `1` spilled across `call inc` (`inc 0 = 1`), then
`1 + 5 + 1 = 7` with carry-out `false`. -/
theorem carryCall_nonvacuous :
    Eventually (mach.step hostCarryCall) (Returns ra0 sp0 [(0, 7#64), (2, 0#64)] [])
      (mkSt [(4, sp0), (7, ones64), (6, 1#64), (2, 5#64)] (initMem stackInit),
        labelAddr hostCarryCall "carryCall") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `bits8 p 30` with `*p = 48`: `x = 48 >> 1 = 24 <u 30`, so it returns `24`. -/
theorem bits8_nonvacuous :
    Eventually (mach.step hostBits8) (Returns ra0 sp0 [(0, 24#64)] [])
      (mkSt [(4, sp0), (7, 0x2000#64), (6, 30#64)] (initMem (stackInit ++ [(0x2000#64, [48])])),
        labelAddr hostBits8 "bits8") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-! ### `G12d` -/

/-- `cmpJcc 7 3 = 3` (`cmp; jcc` on `CF`). -/
theorem cmpJcc_nonvacuous :
    Eventually (mach.step hostCmpJcc) (Returns ra0 sp0 [(0, 3#64)] [])
      (mkSt [(4, sp0), (7, 7#64), (6, 3#64)] (initMem stackInit), labelAddr hostCmpJcc "cmpJcc") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `(5 : 2^64-1) + (2^64-1 : 1)`: carries ripple through `CF` (`adc; adc; adc`), giving high limb
`5` and carry-out limb `1`. -/
theorem adcChain_nonvacuous :
    Eventually (mach.step hostAdcChain) (Returns ra0 sp0 [(0, 5#64), (2, 1#64)] [])
      (mkSt [(4, sp0), (7, ones64), (6, 5#64), (2, 1#64), (1, ones64)] (initMem stackInit),
        labelAddr hostAdcChain "adcChain") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- Interleaved chains: `(7 : 2^64-1) + 1` on `CF` (`adcx`) gives `8`, `(9 : 2^64-2) + 3` on `OF`
(`adox`) gives `10`. -/
theorem adcxAdox_nonvacuous :
    Eventually (mach.step hostAdcxAdox) (Returns ra0 sp0 [(0, 8#64), (2, 10#64)] [])
      (mkSt [(4, sp0), (7, ones64), (6, 7#64), (2, 1#64), (1, 0xFFFFFFFFFFFFFFFE#64), (8, 9#64),
          (9, 3#64)] (initMem stackInit), labelAddr hostAdcxAdox "adcxAdox") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `cfLoop 3 2^63`: the carry out of trip 2 (`2^63 + (2^63 + 8)`) is carried in `CF` across
`lea`/`dec`/`tstz` and the back-edge into trip 3: `8 + (2^63 + 16) + 1 = 2^63 + 25`, final carry
`false`. -/
theorem cfLoop_nonvacuous :
    Eventually (mach.step hostCfLoop) (Returns ra0 sp0 [(0, 0x8000000000000019#64), (2, 0#64)] [])
      (mkSt [(4, sp0), (7, 3#64), (6, 0x8000000000000000#64)] (initMem stackInit),
        labelAddr hostCfLoop "cfLoop") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `addrDisp 0x2000 0x2A`: stores `0x2A` at `0x2010`, loads `0x99` from `0x2008` (`p - (-8)`). -/
theorem addrDisp_nonvacuous :
    Eventually (mach.step hostAddrDisp) (Returns ra0 sp0 [(0, 0x99#64)] [])
      (mkSt [(4, sp0), (7, 0x2000#64), (6, 0x2A#64)]
        (initMem (stackInit ++ [(0x2008#64, [0x99, 0, 0, 0, 0, 0, 0, 0]),
          (0x2010#64, [0, 0, 0, 0, 0, 0, 0, 0])])),
        labelAddr hostAddrDisp "addrDisp") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `addrCall 0x2000`: elides `p + 8` before `call inc(41)`, loads `100` from `0x2008`, returns
`42 + 100 = 142`. -/
theorem addrCall_nonvacuous :
    Eventually (mach.step hostAddrCall) (Returns ra0 sp0 [(0, 142#64)] [])
      (mkSt [(4, sp0), (7, 0x2000#64)]
        (initMem (stackInit ++ [(0x2008#64, [100, 0, 0, 0, 0, 0, 0, 0])])),
        labelAddr hostAddrCall "addrCall") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

/-- `addrSib 0x2000 10 0x2A`: stores `0x2A` at `0x2000 + 10*4 + 8 = 0x2030`, loads `0x99` from
`0x2000 + 10*8 - 8 = 0x2048`. -/
theorem addrSib_nonvacuous :
    Eventually (mach.step hostAddrSib) (Returns ra0 sp0 [(0, 0x99#64)] [])
      (mkSt [(4, sp0), (7, 0x2000#64), (6, 10#64), (2, 0x2A#64)]
        (initMem (stackInit ++ [(0x2030#64, [0, 0, 0, 0, 0, 0, 0, 0]),
          (0x2048#64, [0x99, 0, 0, 0, 0, 0, 0, 0])])),
        labelAddr hostAddrSib "addrSib") :=
  returns_of_check (by t_kernel_rfl) 1000 (mkSt_rel (initMem_rel _ (by t_kernel_rfl)))
    (by t_kernel_rfl)

#print axioms branches_nonvacuous
#print axioms loop_nonvacuous
#print axioms evenOdd_nonvacuous
#print axioms nested_nonvacuous
#print axioms pairLoop_nonvacuous
#print axioms vecLoop_nonvacuous
#print axioms carryCall_nonvacuous
#print axioms bits8_nonvacuous
#print axioms cmpJcc_nonvacuous
#print axioms adcChain_nonvacuous
#print axioms adcxAdox_nonvacuous
#print axioms cfLoop_nonvacuous
#print axioms addrDisp_nonvacuous
#print axioms addrCall_nonvacuous
#print axioms addrSib_nonvacuous

/-! ## 5. Host Facts for the `lowerFn_correct` Hooks (`IsInfixAt`, `LabelsUnique`, `Defined`) -/

/-- Every label occurrence is the first one (`labelAddr`): a kernel-checkable uniqueness test. -/
def labelsOk (h : LHost) : Bool :=
  (List.range h.prog.length).all fun i =>
    match h.prog[i]? with
    | some (.label l) => labelAddr h l == i
    | _ => true

theorem labelAddr_of_labelsOk {h : LHost} (hok : labelsOk h = true) {i : Nat} {l : String}
    (hi : h.prog[i]? = some (.label l)) : labelAddr h l = i := by
  have hlt : i < h.prog.length := by
    rcases Nat.lt_or_ge i h.prog.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hi; cases hi
  have := List.all_eq_true.mp hok i (List.mem_range.mpr hlt)
  rw [hi] at this
  exact beq_iff_eq.mp this

/-- `Target.LabelsUnique` for a host, stated on `mach`/`Instr.label` (definitionally the same for
the litmus target). -/
theorem labelsUnique_of_ok {h : LHost} (hok : labelsOk h = true) :
    ∀ (i j : Nat) (l : String), h.prog[i]? = some (.label l) → h.prog[j]? = some (.label l) →
      i = j := fun _ _ _ hi hj =>
  (labelAddr_of_labelsOk hok hi).symm.trans (labelAddr_of_labelsOk hok hj)

theorem labels_ok_addr :
    labelsOk hostAddrDisp = true ∧ labelsOk hostAddrCall = true ∧ labelsOk hostAddrSib = true :=
  ⟨by t_kernel_rfl, by t_kernel_rfl, by t_kernel_rfl⟩

theorem addrCall_layout :
    codeInc.IsInfixAt hostAddrCall.prog 0 ∧
    codeAddrCall.IsInfixAt hostAddrCall.prog codeInc.length := by
  refine ⟨⟨codeAddrCall, by simp [hostAddrCall, mkHost]⟩, ⟨[], ?_⟩⟩
  simp [hostAddrCall, mkHost]

theorem labels_ok_all :
    labelsOk hostBranches = true ∧ labelsOk hostLoop = true ∧ labelsOk hostEvenOdd = true ∧
    labelsOk hostNested = true ∧ labelsOk hostPairLoop = true ∧ labelsOk hostVecLoop = true ∧
    labelsOk hostCarryCall = true ∧ labelsOk hostBits8 = true ∧ labelsOk hostCmpJcc = true ∧
    labelsOk hostAdcChain = true ∧ labelsOk hostAdcxAdox = true ∧ labelsOk hostCfLoop = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> t_kernel_rfl

/-- The lowered code sits at offset `0` of its witness host (callee `inc` at `0`, `carryCall` right
after it), and `inc` is `Defined` in the `carryCall` host. -/
theorem carryCall_layout :
    codeInc.IsInfixAt hostCarryCall.prog 0 ∧
    codeCarryCall.IsInfixAt hostCarryCall.prog codeInc.length ∧
    hostCarryCall.prog[0]? = some (.label "inc") := by
  refine ⟨⟨codeCarryCall, by simp [hostCarryCall, mkHost]⟩, ⟨[], ?_⟩, by t_kernel_rfl⟩
  simp [hostCarryCall, mkHost]

theorem code_infix_self (c : List Instr) (hc : Nat.ble (c.length + 1) (2 ^ 64) = true) :
    c.IsInfixAt (mkHost c hc).prog 0 := ⟨[], by simp [mkHost]⟩

/-! ## 6. Hooks for End-to-End `*_correct` (`t7-rega`'s `lowerFn_correct`)

`HookHyps` bundles exactly the non-callee hypotheses of `Rega.lowerFn_correct` (#226) for the
litmus `Target`; every `*_hook` below discharges them for a concrete host. Once
`LeanQbe/T/RegaLemmas4.lean` is importable, each end-to-end theorem is a one-liner, e.g.

```
theorem loop_correct (Γ : Env) :
    litmusTarget.FnSpec hostLoop fnLoop.name (Func.spec Γ fnLoop.body) 0 0 :=
  let H := loop_hook
  Rega.lowerFn_correct litmusTarget hostLoop hintsLoop {} fnLoop Γ 0 0 (fun _ => 0)
    H.wf H.lower H.infixAt H.unique H.frame_le H.stack (by simp) (by simp)
```

(`hcal`/`hex` are vacuous for the empty `Ext`). For `carryCall`, `inc_hook` (offset `0`,
`n = 0`) gives `inc_correct`, which discharges `hcal` of `carryCall_hook` (offset
`codeInc.length`, `n = 24 = 16 + 8 + 0`) for its single callee `("inc", [i64], [i64])`.
-/

structure HookHyps (host : LHost) (hints : isa.Hints) (E : Rega.Ext) (f : Fn) (code : List Instr)
    (k₀ n : Nat) : Prop where
  wf : f.Wf
  lower : Rega.lowerFn litmusTarget.toIsa hints E f = .ok code
  infixAt : code.IsInfixAt (litmusTarget.mach.prog host) k₀
  unique : litmusTarget.LabelsUnique host
  frame_le : litmusTarget.frame.frameSize hints.totalSlots ≤ n
  stack : n + litmusTarget.frame.raBytes ≤ 2 ^ 64

theorem branches_hook : HookHyps hostBranches hintsBranches {} fnBranches codeBranches 0 0 :=
  ⟨branches_wf, branches_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem loop_hook : HookHyps hostLoop hintsLoop {} fnLoop codeLoop 0 0 :=
  ⟨loop_wf, loop_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem evenOdd_hook : HookHyps hostEvenOdd hintsEvenOdd {} fnEvenOdd codeEvenOdd 0 0 :=
  ⟨evenOdd_wf, evenOdd_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem nested_hook : HookHyps hostNested hintsNested {} fnNested codeNested 0 0 :=
  ⟨nested_wf, nested_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem pairLoop_hook : HookHyps hostPairLoop hintsPairLoop {} fnPairLoop codePairLoop 0 0 :=
  ⟨pairLoop_wf, pairLoop_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem vecLoop_hook : HookHyps hostVecLoop hintsVecLoop {} fnVecLoop codeVecLoop 0 0 :=
  ⟨vecLoop_wf, vecLoop_lower, ⟨[], List.append_nil _⟩,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem inc_hook : HookHyps hostCarryCall hintsInc {} fnInc codeInc 0 0 :=
  ⟨inc_wf, inc_lower, carryCall_layout.1, labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem carryCall_hook :
    HookHyps hostCarryCall hintsCarryCall extCarryCall fnCarryCall codeCarryCall codeInc.length 24 :=
  ⟨carryCall_wf, carryCall_lower, carryCall_layout.2.1,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem bits8_hook : HookHyps hostBits8 hintsBits8 {} fnBits8 codeBits8 0 0 :=
  ⟨bits8_wf, bits8_lower, ⟨[], List.append_nil _⟩, labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem cmpJcc_hook : HookHyps hostCmpJcc hintsCmpJcc {} fnCmpJcc codeCmpJcc 0 0 :=
  ⟨cmpJcc_wf, cmpJcc_lower, ⟨[], List.append_nil _⟩,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem adcChain_hook : HookHyps hostAdcChain hintsAdcChain {} fnAdcChain codeAdcChain 0 0 :=
  ⟨adcChain_wf, adcChain_lower, ⟨[], List.append_nil _⟩,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem adcxAdox_hook : HookHyps hostAdcxAdox hintsAdcxAdox {} fnAdcxAdox codeAdcxAdox 0 0 :=
  ⟨adcxAdox_wf, adcxAdox_lower, ⟨[], List.append_nil _⟩,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.2.2.2.2.1,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
theorem cfLoop_hook : HookHyps hostCfLoop hintsCfLoop {} fnCfLoop codeCfLoop 0 0 :=
  ⟨cfLoop_wf, cfLoop_lower, ⟨[], List.append_nil _⟩,
    labelsUnique_of_ok labels_ok_all.2.2.2.2.2.2.2.2.2.2.2,
    Nat.le_of_ble_eq_true (by t_kernel_rfl), Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩

/-- `inc` is `Defined` in the `carryCall` host (needed by `FnSpec`'s callee hypotheses). -/
theorem inc_defined : litmusTarget.Defined hostCarryCall "inc" := ⟨0, carryCall_layout.2.2⟩

#print axioms cfLoop_hook
#print axioms carryCall_hook
#print axioms inc_defined

/-! ## 7. End-to-End `G12a`/`G12d` Correctness (`Rega.lowerFn_correct` → `Target.FnSpec`) -/

section Correct
variable (Γ : Env)

theorem HookHyps.correct {host : LHost} {hints : isa.Hints} {f : Fn} {code : List Instr} {k₀ n : Nat}
    (H : HookHyps host hints {} f code k₀ n) :
    litmusTarget.FnSpec host f.name (Func.spec Γ f.body) n 0 :=
  Rega.lowerFn_correct litmusTarget host hints {} f Γ n 0 (fun _ => 0) H.wf H.lower H.infixAt H.unique
    H.frame_le H.stack (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem branches_correct :
    litmusTarget.FnSpec hostBranches fnBranches.name (Func.spec Γ fnBranches.body) 0 0 :=
  branches_hook.correct Γ
theorem loop_correct :
    litmusTarget.FnSpec hostLoop fnLoop.name (Func.spec Γ fnLoop.body) 0 0 :=
  loop_hook.correct Γ
theorem evenOdd_correct :
    litmusTarget.FnSpec hostEvenOdd fnEvenOdd.name (Func.spec Γ fnEvenOdd.body) 0 0 :=
  evenOdd_hook.correct Γ
theorem nested_correct :
    litmusTarget.FnSpec hostNested fnNested.name (Func.spec Γ fnNested.body) 0 0 :=
  nested_hook.correct Γ
theorem pairLoop_correct :
    litmusTarget.FnSpec hostPairLoop fnPairLoop.name (Func.spec Γ fnPairLoop.body) 0 0 :=
  pairLoop_hook.correct Γ
theorem vecLoop_correct :
    litmusTarget.FnSpec hostVecLoop fnVecLoop.name (Func.spec Γ fnVecLoop.body) 0 0 :=
  vecLoop_hook.correct Γ
theorem inc_correct :
    litmusTarget.FnSpec hostCarryCall fnInc.name (Func.spec Γ fnInc.body) 0 0 :=
  inc_hook.correct Γ
theorem bits8_correct :
    litmusTarget.FnSpec hostBits8 fnBits8.name (Func.spec Γ fnBits8.body) 0 0 :=
  bits8_hook.correct Γ
theorem cmpJcc_correct :
    litmusTarget.FnSpec hostCmpJcc fnCmpJcc.name (Func.spec Γ fnCmpJcc.body) 0 0 :=
  cmpJcc_hook.correct Γ
theorem adcChain_correct :
    litmusTarget.FnSpec hostAdcChain fnAdcChain.name (Func.spec Γ fnAdcChain.body) 0 0 :=
  adcChain_hook.correct Γ
theorem adcxAdox_correct :
    litmusTarget.FnSpec hostAdcxAdox fnAdcxAdox.name (Func.spec Γ fnAdcxAdox.body) 0 0 :=
  adcxAdox_hook.correct Γ
theorem cfLoop_correct :
    litmusTarget.FnSpec hostCfLoop fnCfLoop.name (Func.spec Γ fnCfLoop.body) 0 0 :=
  cfLoop_hook.correct Γ

theorem addrDisp_correct :
    litmusAddrTarget.FnSpec hostAddrDisp fnAddrDisp.name (Func.spec Γ fnAddrDisp.body) 0 0 :=
  Rega.lowerFn_correct litmusAddrTarget hostAddrDisp hintsAddrDisp {} fnAddrDisp Γ 0 0
    (fun _ => 0) addrDisp_wf addrDisp_lower (code_infix_self codeAddrDisp (by t_kernel_rfl))
    (labelsUnique_of_ok labels_ok_addr.1) (Nat.le_of_ble_eq_true (by t_kernel_rfl))
    (Nat.le_of_ble_eq_true (by t_kernel_rfl)) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem addrSib_correct :
    litmusAddrTarget.FnSpec hostAddrSib fnAddrSib.name (Func.spec Γ fnAddrSib.body) 0 0 :=
  Rega.lowerFn_correct litmusAddrTarget hostAddrSib hintsAddrSib {} fnAddrSib Γ 0 0
    (fun _ => 0) addrSib_wf addrSib_lower (code_infix_self codeAddrSib (by t_kernel_rfl))
    (labelsUnique_of_ok labels_ok_addr.2.2) (Nat.le_of_ble_eq_true (by t_kernel_rfl))
    (Nat.le_of_ble_eq_true (by t_kernel_rfl)) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem inc_correct_addr :
    litmusAddrTarget.FnSpec hostAddrCall fnInc.name (Func.spec Γ fnInc.body) 0 0 :=
  Rega.lowerFn_correct litmusAddrTarget hostAddrCall hintsInc {} fnInc Γ 0 0 (fun _ => 0)
    inc_wf inc_lower addrCall_layout.1 (labelsUnique_of_ok labels_ok_addr.2.1)
    (Nat.le_of_ble_eq_true (by t_kernel_rfl)) (Nat.le_of_ble_eq_true (by t_kernel_rfl))
    (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem addrCall_correct (hΓ : Γ "inc" [i64] [i64] = Func.spec Γ fnInc.body) :
    litmusAddrTarget.FnSpec hostAddrCall fnAddrCall.name (Func.spec Γ fnAddrCall.body) 24 0 := by
  refine Rega.lowerFn_correct litmusAddrTarget hostAddrCall hintsAddrCall extCarryCall fnAddrCall
    Γ 24 0 (fun _ => 0) addrCall_wf addrCall_lower addrCall_layout.2
    (labelsUnique_of_ok labels_ok_addr.2.1) (Nat.le_of_ble_eq_true (by t_kernel_rfl))
    (Nat.le_of_ble_eq_true (by t_kernel_rfl)) ?_ (fun _ h => nomatch h)
  intro g as bs hg
  simp only [extCarryCall, List.mem_singleton, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl, rfl⟩ := hg
  refine ⟨?_, Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
  rw [hΓ]; exact inc_correct_addr Γ

/-- Carry chain across a `call`: the callee `inc` is discharged by `inc_correct`. -/
theorem carryCall_correct (hΓ : Γ "inc" [i64] [i64] = Func.spec Γ fnInc.body) :
    litmusTarget.FnSpec hostCarryCall fnCarryCall.name (Func.spec Γ fnCarryCall.body) 24 0 := by
  have H := carryCall_hook
  refine Rega.lowerFn_correct litmusTarget hostCarryCall hintsCarryCall extCarryCall fnCarryCall Γ 24 0
    (fun _ => 0) H.wf H.lower H.infixAt H.unique H.frame_le H.stack ?_ (fun _ h => nomatch h)
  intro g as bs hg
  simp only [extCarryCall, List.mem_singleton, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl, rfl⟩ := hg
  refine ⟨?_, Nat.le_of_ble_eq_true (by t_kernel_rfl)⟩
  rw [hΓ]; exact inc_correct Γ

end Correct

#print axioms Rega.lowerFn_correct
#print axioms Rega.lowerExpr_correct
#print axioms Rega.lowerFn_labelsUnique
#print axioms cfLoop_correct
#print axioms adcxAdox_correct
#print axioms carryCall_correct
#print axioms vecLoop_correct
#print axioms evenOdd_correct
#print axioms addrDisp_correct
#print axioms addrCall_correct
#print axioms addrSib_correct

end LeanQbe.T.RegaLitmus
