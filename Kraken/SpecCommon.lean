import Kraken.Semantics
import Kraken.Theorems

/-- Asserts that a contiguous region of n 64-bit words starting at addr exists in the heap. -/
def heapRegionValid (s : MachineState) (addr : UInt64) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → (s.1.dmem[addr + i.toUInt64 * 8]?).isSome

/-- Stack is valid: rsp is 8-byte aligned and has at least `minBytes` of space. -/
def stackValid (s : MachineState) (minBytes : Nat) : Prop :=
  s.1.regs.rsp.toNat % 8 = 0 ∧ s.1.regs.rsp.toNat ≥ minBytes


-- ============================================================================
-- heapRegionValid Theorems
-- ============================================================================
theorem heap_valid_base (s : MachineState) (addr : UInt64) (n : Nat)
    (h_mem : heapRegionValid s addr n) (h_nz : 0 < n) :
    (s.1.dmem[addr]?).isSome := by
  have h_0 := h_mem 0 h_nz
  have hy : addr + Nat.toUInt64 0 * 8 = addr := by
    change addr + 0 = addr
    simp
  rw [hy] at h_0
  exact h_0

theorem dmem_get_of_heapRegionValid_base (s_data : MachineData) (pc : Int64) (base : UInt64) (N : Nat)
    (h_mem : heapRegionValid (s_data, pc) base N) (h_bound : 0 < N := by decide) :
    s_data.dmem[base]? = some ((s_data.dmem[base]?).get (by
      have h_val := heap_valid_base (s_data, pc) base N h_mem h_bound
      simp [h_val])) := by
  have h_val := heap_valid_base (s_data, pc) base N h_mem h_bound
  exact option_eq_some _ h_val

theorem dmem_get_of_heapRegionValid (s_data : MachineData) (pc : Int64) (base : UInt64) (N : Nat)
    (h_mem : heapRegionValid (s_data, pc) base N) (offset_bytes : UInt64) (offset_idx : Nat)
    (h_eq : offset_bytes = offset_idx.toUInt64 * 8 := by decide)
    (h_bound : offset_idx < N := by decide) :
    s_data.dmem[base + offset_bytes]? = some ((s_data.dmem[base + offset_idx.toUInt64 * 8]?).get (by
      have h_val := h_mem offset_idx h_bound
      simp [h_val])) := by
  have h_val := h_mem offset_idx h_bound
  rw [h_eq]
  exact option_eq_some _ h_val

theorem heapRegionValid_get (s_data : MachineData) (pc : Int64) (base : UInt64) (N : Nat)
    (h_mem : heapRegionValid (s_data, pc) base N) (offset : Nat) (h_bound : offset < N) :
    (s_data.dmem[base + offset.toUInt64 * 8]?).isSome = true := by
  have h := h_mem offset h_bound
  exact h

macro "resolve_mem_option" : tactic => `(tactic|
  (
    try rw [option_eq_some _ (heapRegionValid_get _ _ _ _ (by assumption) _ (by decide))]
  )
)
