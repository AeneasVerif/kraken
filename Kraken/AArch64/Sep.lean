import Kraken.AArch64.Semantics
import Kraken.Attribute
import Kraken.SeparationMem

open Std
open Std.ExtHashMap
open List

@[kspec]
theorem store_sep (s : MachineData) (addr : BitVec 64) (w : MemWidth) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeBV s.dmem addr w.bytes v
    MachineData.store s addr v ret =
      require_write_access addr w (fun _ =>
        ret { s with dmem := mem' }) := by
  have h_load : Mem.loadBytes s.dmem addr w.bytes = some bs :=
    Mem.loadBytes_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.store, h_load]

@[kspec]
theorem load_sep (s : MachineData) (addr : BitVec 64) (w : MemWidth) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_read_access addr w (fun _ => ret (BitVec.ofBytes w.bits bs) s) := by
  simp only [MachineData.load,
    Mem.loadBV_sep bs addr w.bits w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]
