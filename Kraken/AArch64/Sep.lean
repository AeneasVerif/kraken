import Kraken.AArch64.Semantics
import Kraken.SeparationMem

open Std
open Std.ExtHashMap
open List

theorem store_sep (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.store s addr v ret =
      require_write_access addr w (fun _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.store, h_load]

theorem load_sep (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_read_access addr w (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.load, h_load]
