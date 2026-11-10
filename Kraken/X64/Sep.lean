module

import Kraken.Attribute
public import Kraken.SeparationMem
public import Kraken.X64.Semantics
public import Kraken.X64.OmniSemantics

public section

open Std
open Std.ExtHashMap
open List

@[kspec]
theorem store_sep (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeInt s.dmem addr w.bytes v.toInt
    MachineData.store s addr v ret =
      require_access require_write_access addr (UInt64.ofNat w.bytes) (fun _ =>
        ret { s with dmem := mem' }) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.store, h_load]

@[kspec]
theorem load_sep (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_access require_read_access addr (UInt64.ofNat w.bytes) (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.load,
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]

/-- `store_sep` at the level of `Effects.All`, with the write-access effect discharged. -/
theorem store_All_of_sep (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type)
    (ret : MachineData → Effects) (post : MachineState → Prop) (bs : List UInt8)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R) (h_len : bs.length = w.bytes) :
    (MachineData.store s addr v ret).All post ↔
      (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post := by
  have h := store_sep s addr w v ret bs R h_mem h_len
  simp only at h
  rw [h, Effects.All_require_write_access]

/-- `load_sep` at the level of `Effects.All`, with the read-access effect discharged. -/
theorem load_All_of_sep (s : MachineData) (addr : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (post : MachineState → Prop) (bs : List UInt8)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R) (h_len : bs.length = w.bytes) :
    (MachineData.load s addr w ret).All post ↔
      (ret (.ofInt w.bits (Int.ofBytes bs)) s).All post := by
  rw [load_sep s addr w ret bs R h_mem h_len, Effects.All_require_read_access]
