module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound1
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.LeanLCNF.LcnfC0RtProofCommon

/-!
# Heap Object & Allocation Simulation Proofs (`LowerSound1b`)

Companion to `LowerSound1.lean` providing separation-logic and `LExpr.wp` proofs for:
1. Runtime state, bytes/cells/`readBitsLE`, and `LcnfObj` memory helpers (`m_rc`, `m_tag`, fields,
   scalar data, disjointness, well-formedness)
2. `allocObj`, `storeFields`, constructor initialization, `boxU64`, and their `LMMono` lemmas
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.RtProof
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. Runtime State, Bytes, and `LcnfObj` Memory Helpers -/

theorem hinv_of_preservesMeta {rt : BitVec 64} {σ : HState} {st' : RtC0State}
    {objs' : List LcnfObj} (hinv : HInv rt σ) (hpm : st'.PreservesMeta σ.st) :
    HInv rt { st := st', objs := objs', scr := σ.scr, scrLimbs := σ.scrLimbs } := by
  refine ⟨?_, hinv.2⟩
  simpa [RtC0State.Bounded48, hpm.2.2.2.1] using hinv.1

theorem hstate_mem_unfold (rt : BitVec 64) (σ : HState) :
    σ.mem rt =
      (rtC0Inv rt σ.st ⋆
        cell64 (rt + 33672#64) σ.scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
        array64 σ.scr σ.scrLimbs ⋆
        lcnfHeap σ.objs) := by
  simp only [HState.mem.eq_1, fullRtInv.eq_1, sep_assoc]

theorem writeNatLE_eq_toBytes : ∀ (k n : Nat), writeNatLE n k = Int.toBytes k (n : Int)
  | 0, _ => by rw [writeNatLE.eq_1, Int.toBytes.eq_1]
  | k + 1, n => by
    rw [writeNatLE.eq_2, Int.toBytes.eq_2, writeNatLE_eq_toBytes k (n / 256)]
    have htake : ((n : Int).take 8).toNat.toUInt8 = UInt8.ofNat (n % 256) := by
      simp only [Int.take, show (2 ^ 8 : Int) = 256 by decide]
      have hm : (n : Int) % 256 = ((n % 256 : Nat) : Int) := by omega
      rw [hm, Int.toNat_natCast]
    have hdiv : ((n : Int) / 256) = ((n / 256 : Nat) : Int) := by omega
    rw [htake, hdiv]

theorem bytes_writeNatLE8_eq_cell64 (a v : BitVec 64) :
    bytes a (writeNatLE v.toNat 8) = cell64 a v := by
  rw [bytes.eq_1, writeNatLE_eq_toBytes, cell64_eq_word8]
  rfl

private theorem toBytes_readNatLE :
    ∀ (k : Nat) (bs : List UInt8) (off : Nat),
      off + k ≤ bs.length →
      Int.toBytes k (readNatLE bs off k : Int) = (bs.drop off).take k
  | 0, bs, off, _ => by rw [readNatLE.eq_1, Int.toBytes.eq_1]; rfl
  | k + 1, bs, off, hk => by
    have hlt : off < bs.length := by omega
    have hget : bs.getD off 0 = bs[off] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [readNatLE.eq_2, hget, Int.toBytes.eq_2]
    have hb : (bs[off]'hlt).toNat < 256 := (bs[off]'hlt).toNat_lt
    have htake :
        ((((bs[off]'hlt).toNat + 256 * readNatLE bs (off + 1) k : Nat) : Int).take
          8).toNat.toUInt8 = bs[off]'hlt := by
      simp only [Int.take, show (2 ^ 8 : Int) = 256 by decide]
      have hm :
          (((bs[off]'hlt).toNat + 256 * readNatLE bs (off + 1) k : Nat) : Int) % 256 =
            ((bs[off]'hlt).toNat : Int) := by omega
      rw [hm, Int.toNat_natCast]
      exact UInt8.ofNat_toNat
    have hdiv :
        (((bs[off]'hlt).toNat + 256 * readNatLE bs (off + 1) k : Nat) : Int) / 256 =
          (readNatLE bs (off + 1) k : Int) := by omega
    rw [htake, hdiv, toBytes_readNatLE k bs (off + 1) (by omega),
      List.drop_eq_getElem_cons hlt, List.take_succ_cons]

theorem readBitsLE_bytes_loadVal {base : BitVec 64} {bs : List UInt8} {off w : Nat}
    {F : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + (w + 7) / 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ F) m) :
    loadVal m (.bits w) (base + BitVec.ofNat 64 off) = some (readBitsLE w bs off) := by
  let nbytes := (w + 7) / 8
  have hsplit : bs = bs.take off ++ ((bs.drop off).take nbytes ++ bs.drop (off + nbytes)) := by
    have h2 : (bs.drop off).take nbytes ++ (bs.drop off).drop nbytes = bs.drop off :=
      List.take_append_drop nbytes (bs.drop off)
    rw [List.drop_drop] at h2
    rw [h2, List.take_append_drop]
  have hlen1 : (bs.take off).length = off := List.length_take_of_le (by omega)
  have hlen2 : ((bs.drop off).take nbytes).length = nbytes := by
    simp [List.length_take, List.length_drop]; omega
  have heq : bytes base bs =
      (Eq ((Int.toBytes nbytes (readNatLE bs off nbytes : Int)).At
          (base + BitVec.ofNat 64 off)) ⋆
        (Eq ((bs.take off).At base) ⋆
          Eq ((bs.drop (off + nbytes)).At
            (base + BitVec.ofNat 64 off + BitVec.ofNat 64 nbytes)))) := by
    rw [bytes.eq_1]
    conv => lhs; rw [hsplit]
    rw [eq_append_At base (bs.take off) ((bs.drop off).take nbytes ++ bs.drop (off + nbytes))
        (by simp [List.length_take, List.length_drop]; omega),
      hlen1,
      eq_append_At (base + BitVec.ofNat 64 off) ((bs.drop off).take nbytes)
        (bs.drop (off + nbytes)) (by simp [List.length_take, List.length_drop]; omega),
      hlen2, toBytes_readNatLE nbytes bs off hoff]
    ac_rfl
  have hm' :
      (Eq ((Int.toBytes (Ty.bits w).bytes (readNatLE bs off nbytes : Int)).At
          (base + BitVec.ofNat 64 off)) ⋆
        ((Eq ((bs.take off).At base) ⋆
          Eq ((bs.drop (off + nbytes)).At
            (base + BitVec.ofNat 64 off + BitVec.ofNat 64 nbytes))) ⋆ F)) m := by
    rw [heq] at hm
    exact sep_cast hm (by ac_rfl)
  have hbytesLe : (Ty.bits w).bytes ≤ 2 ^ 64 := by
    change (w + 7) / 8 ≤ 2 ^ 64
    omega
  have hld := loadVal_toBytes_bits (n := w) hbytesLe hm'
  simpa [readBitsLE, BitVec.ofInt_natCast] using hld

private theorem getLsbD_ge_width {w : Nat} (x : BitVec w) {i : Nat} (hi : w ≤ i) :
    x.getLsbD i = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hi))

theorem lcnfObj_header_setWidth32 (o : LcnfObj) :
    BitVec.setWidth 32 o.header = o.rc := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · simp only [LcnfObj.header, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
    have h48 : ¬ (48 ≤ i) := by omega
    have h56 : ¬ (56 ≤ i) := by omega
    have hi64 : i < 64 := by omega
    have hlt48 : i < 48 := by omega
    have hlt56 : i < 56 := by omega
    simp [hi, hi64, hlt48, hlt56]
  · have hrcFalse : o.rc.getLsbD i = false := getLsbD_ge_width o.rc (by omega : 32 ≤ i)
    simp [hi, hrcFalse]

theorem lcnfObjMem_load_i32_rc {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i32 o.addr = some o.rc := by
  rw [lcnfObjMem_eq_header_body, sep_assoc, cell64_eq_word8, word8_eq_int4_sep, sep_assoc] at hm
  have h := load_int4 hm
  rwa [lcnfObj_header_setWidth32] at h

theorem lcnfObjMem_store_i32_rc {o : LcnfObj} (rc' : BitVec 32) {F : Mem 64 → Prop} {m : Mem 64}
    (hwf : o.Wf) (hm : (lcnfObjMem o ⋆ F) m) :
    storeOk m i32 o.addr ∧
      (lcnfObjMem (o.withRc rc') ⋆ F) (storeMem m i32 o.addr rc') := by
  have hdrop :
      List.drop 4 (Int.toBytes 8 (o.withRc rc').header.toNat) =
        List.drop 4 (Int.toBytes 8 o.header.toNat) := by
    have hhi : (o.withRc rc').header >>> 32 = o.header >>> 32 := by
      have hclear := LcnfObj.header_clear_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
      have hclear' := LcnfObj.header_clear_rc (o.withRc rc') hwf.2.2.2.1 hwf.2.2.2.2.1
        hwf.2.2.2.2.2.1
      have hwith : (o.withRc rc').withRc 0#32 = o.withRc 0#32 := rfl
      rw [hwith] at hclear'
      have heq := hclear'.trans hclear.symm
      apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 32
      · have hcon := congrArg (fun x : BitVec 64 => x.getLsbD (32 + i)) heq
        have hmask : (0xffffffff00000000#64).getLsbD (32 + i) = true := by
          have : 32 + i < 64 := by omega
          simp only [BitVec.getLsbD_ofNat, this, decide_true, Bool.true_and]
          rw [show (0xffffffff00000000 : Nat) = (2 ^ 32 - 1) <<< 32 by decide,
            Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
          simp [hi]
        have hi64 : i < 64 := by omega
        simp only [BitVec.getLsbD_ushiftRight, hi64]
        simpa [BitVec.getLsbD_and, hmask] using hcon
      · have h0 : ∀ v : BitVec 64, (v >>> 32).getLsbD i = false := fun v => by
          rw [BitVec.getLsbD_ushiftRight]
          exact getLsbD_ge_width v (by omega : 64 ≤ 32 + i)
        simp [h0]
    have hhiNat : (o.withRc rc').header.toNat / 2 ^ 32 = o.header.toNat / 2 ^ 32 := by
      have := congrArg BitVec.toNat hhi
      simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
    have h256 : ∀ v : Nat,
        List.drop 4 (Int.toBytes 8 (v : Int)) = Int.toBytes 4 ((v / 2 ^ 32 : Nat) : Int) := by
      intro v
      rw [show (8 : Nat) = 7 + 1 from rfl, Int.toBytes.eq_2]
      rw [show (7 : Nat) = 6 + 1 from rfl, Int.toBytes.eq_2]
      rw [show (6 : Nat) = 5 + 1 from rfl, Int.toBytes.eq_2]
      rw [show (5 : Nat) = 4 + 1 from rfl, Int.toBytes.eq_2]
      simp only [List.drop_succ_cons, List.drop_zero]
      congr 1
      omega
    rw [h256, h256, hhiNat]
  rw [lcnfObjMem_eq_header_body, sep_assoc, cell64_eq_word8, word8_eq_int4_sep, sep_assoc] at hm
  obtain ⟨hok, hm'⟩ := store_int4 rc' hm
  refine ⟨hok, ?_⟩
  have hrcEq : rc'.setWidth 64 = BitVec.setWidth 64 (BitVec.setWidth 32 (o.withRc rc').header) := by
    rw [lcnfObj_header_setWidth32 (o.withRc rc')]; rfl
  have hint :
      Kraken.Bedrock2.Test.int4 o.addr (rc'.setWidth 64) =
        Kraken.Bedrock2.Test.int4 o.addr (o.withRc rc').header := by
    rw [hrcEq, int4_setWidth32]
  rw [hint] at hm'
  have haddr' : (o.withRc rc').addr = o.addr := rfl
  rw [lcnfObjMem_eq_header_body, lcnfObjBody_withRc, sep_assoc, cell64_eq_word8,
    word8_eq_int4_sep, hdrop, haddr', sep_assoc]
  exact hm'

private theorem toBytes_8_byte7 (v : BitVec 64) :
    ((Int.toBytes 8 (v.toNat : Int))[7]'(by
      rw [Int.toBytes_length]; decide)).toNat = (v >>> 56).toNat := by
  have hget : (Int.toBytes 8 (v.toNat : Int))[7]? =
      some (UInt8.ofNat (v >>> 56).toNat) := by
    rw [show (8 : Nat) = 7 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (7 : Nat) = 6 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (6 : Nat) = 5 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (5 : Nat) = 4 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (4 : Nat) = 3 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (3 : Nat) = 2 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (2 : Nat) = 1 + 1 from rfl, Int.toBytes.eq_2]
    rw [show (1 : Nat) = 0 + 1 from rfl, Int.toBytes.eq_2]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    have hlt : v.toNat < 2 ^ 64 := v.isLt
    have hdiv : v.toNat / 2 ^ 56 < 256 := by omega
    have htake : (((v.toNat : Int) / 256 / 256 / 256 / 256 / 256 / 256 / 256).take 8).toNat =
        v.toNat / 2 ^ 56 := by
      simp only [Int.take, show (2 ^ 8 : Int) = 256 by decide]
      omega
    rw [htake, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [List.getElem?_eq_getElem (by rw [Int.toBytes_length]; decide)] at hget
  have h7 := Option.some.inj hget
  have hmod : (v >>> 56).toNat < 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt := v.isLt
    omega
  rw [h7]
  dsimp only [UInt8.ofNat, UInt8.toNat]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmod]

theorem lcnfObjMem_load_i8_tag {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hwf : o.Wf) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i8 (o.addr + 7#64) = some (BitVec.ofNat 8 o.tag) := by
  rw [lcnfObjMem_eq_header_body, sep_assoc] at hm
  have hbytes : bytes o.addr (Int.toBytes 8 (o.header.toNat : Int)) = cell64 o.addr o.header := by
    rw [bytes.eq_1, cell64_eq_word8]; rfl
  rw [← hbytes] at hm
  have hlen : (Int.toBytes 8 (o.header.toNat : Int)).length = 8 := Int.toBytes_length 8 _
  have hld := load_bytes_at (i := 7) (by omega) (by omega) hm
  have htagLt : o.tag < 256 := hwf.2.2.2.2.2.1
  have htag := LcnfObj.header_tag o hwf.2.2.2.1 hwf.2.2.2.2.1 htagLt
  have h7 := toBytes_8_byte7 o.header
  have hbyte7 :
      BitVec.ofNat 8 ((Int.toBytes 8 (o.header.toNat : Int))[7]'(by omega)).toNat =
        BitVec.ofNat 8 o.tag := by
    rw [h7, htag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa [hbyte7] using hld

private theorem tag_ne_special {t : Nat} (ht : t ≤ 244) :
    t ≠ closureTag ∧ t ≠ arrayTag ∧ t ≠ sarrayTag ∧ t ≠ stringTag ∧ t ≠ mpzTag := by
  unfold closureTag arrayTag sarrayTag stringTag mpzTag
  omega

theorem lcnfObjMem_load_field {o : LcnfObj} {i : Nat} {F : Mem 64 → Prop} {m : Mem 64}
    (htag : o.tag ≤ 244) (hi : i < o.fields.length) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + BitVec.ofNat 64 (8 + 8 * i)) = some (o.fields[i]'hi) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tag_ne_special htag
  have hm' :
      (array64 (o.addr + 8#64) o.fields ⋆
        (cell64 o.addr o.header ⋆
         bytes (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length)) o.scalarData ⋆
         region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length))
           (o.csSz - (8 + 8 * o.fields.length + o.scalarData.length)) ⋆ F)) m := by
    simp only [lcnfObjMem, h1, h2, h3, h4, h5, ↓reduceIte] at hm
    exact sep_cast hm (by ac_rfl)
  have haddr : o.addr + 8#64 + BitVec.ofNat 64 (8 * i) = o.addr + BitVec.ofNat 64 (8 + 8 * i) :=
    ptr_add_nat_p _ _ _
  rw [← haddr]
  exact loadVal_array64 hi hm'

theorem lcnfObjMem_load_scalar {o : LcnfObj} {bOff w : Nat} {F : Mem 64 → Prop} {m : Mem 64}
    (hwf : o.Wf) (htag : o.tag ≤ 244)
    (hoff : bOff + (w + 7) / 8 ≤ o.scalarData.length) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m (.bits w) (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + bOff)) =
      some (readBitsLE w o.scalarData bOff) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tag_ne_special htag
  have hm' :
      (bytes (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length)) o.scalarData ⋆
        (cell64 o.addr o.header ⋆ array64 (o.addr + 8#64) o.fields ⋆
         region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length))
           (o.csSz - (8 + 8 * o.fields.length + o.scalarData.length)) ⋆ F)) m := by
    simp only [lcnfObjMem, h1, h2, h3, h4, h5, ↓reduceIte] at hm
    exact sep_cast hm (by ac_rfl)
  have hspec := hwf.2.2.2.2.2.2.2.2.2
  simp only [h1, h2, h3, h4, h5, ↓reduceIte] at hspec
  have hlen : o.scalarData.length ≤ 2 ^ 64 := by
    have hcs := hwf.2.2.2.1
    omega
  have haddr :
      o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length) + BitVec.ofNat 64 bOff =
        o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + bOff) :=
    ptr_add_nat_p _ _ _
  rw [← haddr]
  exact readBitsLE_bytes_loadVal hoff hlen hm'

theorem lcnfObj_withRc_self (o : LcnfObj) : o.withRc o.rc = o := rfl

theorem lcnfHeap_disj_of_cell64 {p v : BitVec 64} {objs : List LcnfObj} {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (cell64 p v ⋆ lcnfHeap objs ⋆ F) m) :
    ∀ o ∈ objs, o.addr ≠ p := by
  intro o ho heq
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp ho
  rw [lcnfHeap_focus objs hidx, lcnfObjMem_eq_header_body, sep_assoc] at hm
  have hm' :
      ((cell64 p v ⋆ emp) ⋆
        (cell64 p objs[idx].header ⋆
          (lcnfObjBody objs[idx] ⋆
            (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ F))) m := by
    rw [sep_emp]
    rw [heq] at hm
    exact sep_cast hm (by ac_rfl)
  exact cell64_conflict p v objs[idx].header _ _ m hm'

theorem lcnfObj_ctor_wf {p : BitVec 64} {ci : LcCtor} {vs : List (BitVec 64)}
    {scal : List UInt8}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0)
    (hcidx : ci.cidx ≤ 244) (hsz : ci.size < 256)
    (hmin : rtMinObjBytes ≤ ci.byteSize) (hmax : ci.byteSize < 65536)
    (hvs : vs.length = ci.size) (hscal : scal.length = 8 * ci.usize + ci.ssize) :
    LcnfObj.Wf
      { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
        fields := vs, scalarData := scal } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tag_ne_special hcidx
  let obj : LcnfObj :=
    { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
      fields := vs, scalarData := scal }
  have hmod : ci.byteSize % 8 = 0 := by unfold LcCtor.byteSize; omega
  have htb : obj.totalBytes = ci.byteSize := by
    simp only [obj, LcnfObj.totalBytes, h2, h3, h4, h5, ↓reduceIte]
  have hbound : 8 + 8 * vs.length + scal.length ≤ ci.byteSize := by
    unfold LcCtor.byteSize at *
    omega
  have hrc0 : (0 : Int) ≤ (1#32 : BitVec 32).toInt := by decide
  have htagLt : ci.cidx < 256 := by omega
  have hmin' : rtMinObjBytes ≤ obj.totalBytes := by rw [htb]; exact hmin
  have hmax' : obj.totalBytes < rtMaxObjBytes := by
    rw [htb]; unfold rtMaxObjBytes; omega
  have hmod' : obj.totalBytes % 8 = 0 := by rw [htb]; exact hmod
  refine ⟨hp0, hp8, hrc0, hmax, hsz, htagLt, hmin', hmax', hmod', ?_⟩
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  exact ⟨hcidx, hvs, hbound, hmod⟩

theorem lcnfObj_boxU64_wf {p v : BitVec 64} (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) :
    LcnfObj.Wf
      { addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
        scalarData := writeNatLE v.toNat 8 } := by
  have hlen : (writeNatLE v.toNat 8).length = 8 := by
    rw [writeNatLE_eq_toBytes, Int.toBytes_length]
  obtain ⟨h1, h2, h3, h4, h5⟩ := tag_ne_special (by decide : 0 ≤ 244)
  let obj : LcnfObj :=
    { addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
      scalarData := writeNatLE v.toNat 8 }
  have htb : obj.totalBytes = 16 := by
    simp only [obj, LcnfObj.totalBytes, h2, h3, h4, h5, ↓reduceIte]
  have hmin' : rtMinObjBytes ≤ obj.totalBytes := by
    rw [htb]; unfold rtMinObjBytes; decide
  have hmax' : obj.totalBytes < rtMaxObjBytes := by
    rw [htb]; unfold rtMaxObjBytes; decide
  have hmod' : obj.totalBytes % 8 = 0 := by rw [htb]
  refine ⟨hp0, hp8, by dsimp [obj]; decide, by dsimp [obj]; decide,
    by dsimp [obj]; decide, by dsimp [obj]; decide, hmin', hmax', hmod', ?_⟩
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  exact ⟨by decide, by decide, by simp [hlen], by decide⟩

/-! ## 2. Allocation, Field Initialization, and `LMMono` Combinators -/

theorem allocObj_mono {rt : LArg} {sz hdr : Nat} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (allocObj rt sz hdr k) :=
  call1_mono fun p => storeAt_mono (hk p)

theorem storeFields_mono {p : LArg} :
    ∀ off vs (k : LM LExpr), LMMono k → LMMono (storeFields p off vs k)
  | _, [], _, hk => hk
  | off, _ :: vs, k, hk => storeAt_mono (storeFields_mono (off + 8) vs k hk)

theorem boxU64_mono {rt x : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (boxU64 rt x k) :=
  allocObj_mono fun p => storeAt_mono (hk p)

theorem allocObj_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {rtArg : LArg} {sz hdr : Nat} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (allocObj rtArg sz hdr k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt)
    (hszLo : rtMinObjBytes ≤ sz) (hszHi : sz < 65536) (hsz8 : sz % 8 = 0)
    (hcan : canAllocBytesR0 σ.st sz)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hk : ∀ (p : BitVec 64) (st' : RtC0State) (rp : LArg) (ek : LExpr)
        (ρ' : Frontend.C0.VEnv) (nr : Nat) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 →
      (∀ o ∈ σ.objs, o.addr ≠ p) →
      st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - sz ≤ st'.rem →
      n + 1 ≤ nr →
      HInv rt { st := st', objs := σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs } →
      (cell64 p (BitVec.ofNat 64 hdr) ⋆ region (p + 8#64) (sz - 8) ⋆
        ({ st := st', objs := σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs } : HState).mem rt ⋆
        R) m' →
      (k rp).run nr = .ok (ek, n') →
      argIdsBelow rp nr → VEnvAgreeBelow n ρ' ρ → LArg.eval ρ' i64 rp = some p →
      LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold allocObj at hrun
  have hsig : ("lcnf_alloc", [i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  have hszNat : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have halign : align8 sz = sz := by unfold align8; omega
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆
    lcnfHeap σ.objs ⋆ R
  have hmRt : (rtC0Inv rt σ.st ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm
    exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (p, ()) m1 =>
    ∃ st' : RtC0State,
      p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ st'.PreservesMeta σ.st ∧ st'.rem ≤ σ.st.rem ∧
      σ.st.rem - sz ≤ st'.rem ∧ (rtC0Inv rt st' ⋆ region p sz ⋆ scrFrame) m1
  let E : XPost := fun _ _ _ _ => False
  have hspec : lcnfAllocRemSpec (rt, BitVec.ofNat 64 sz, ()) mem P E := by
    refine ⟨σ.st, scrFrame, by rw [hszNat]; omega,
      by rw [hszNat, halign]; exact hszLo,
      by rw [hszNat, halign]; unfold rtMaxObjBytes; omega,
      by rw [hszNat, halign]; exact hcan, hmRt, ?_⟩
    intro p st' m1 hp0 hp8 hpm hremLe hremLo hm1
    rw [hszNat, halign] at hremLo hm1
    exact ⟨st', hp0, hp8, hpm, hremLe, hremLo, hm1⟩
  refine call1_wp hrun
    (evalArgs_cons hrt (evalArgs_cons (LArg.eval_imm_self ρ i64 (BitVec.ofNat 64 sz))
      (evalArgs_nil ρ)))
    (hΓ.rt hsig (rtC0CoreEnv_lcnf_alloc hspec))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro rp ek1 hek1 hrp p m1 ⟨st', hp0, hp8, hpm, hremLe, hremLo, hm1⟩ hagr1 hevp1
  have hmin16 : 16 ≤ sz := by simpa [rtMinObjBytes] using hszLo
  have hsp : region p sz = (region p 8 ⋆ region (p + 8#64) (sz - 8)) := by
    have hs := region_split (a := p) (n1 := 8) (n2 := sz - 8) (by omega)
    simpa [show 8 + (sz - 8) = sz by omega] using hs
  rw [hsp] at hm1
  have hmCell : (region p 8 ⋆ (rtC0Inv rt st' ⋆ region (p + 8#64) (sz - 8) ⋆ scrFrame)) m1 :=
    sep_cast hm1 (by ac_rfl)
  obtain ⟨v0, hmCell'⟩ := sep_ex_l.mp (sep_mono (fun _ => region_to_cell64) hmCell)
  have hdisj : ∀ o ∈ σ.objs, o.addr ≠ p := by
    let restFrame : Mem 64 → Prop :=
      cell64 (rt + 33672#64) σ.scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
      array64 σ.scr σ.scrLimbs ⋆ R
    have hscr : scrFrame = (lcnfHeap σ.objs ⋆ restFrame) := by
      dsimp only [scrFrame, restFrame]; ac_rfl
    have hmHeap : (cell64 p v0 ⋆ lcnfHeap σ.objs ⋆
        (rtC0Inv rt st' ⋆ region (p + 8#64) (sz - 8) ⋆ restFrame)) m1 := by
      have hmCell2 :
          (cell64 p v0 ⋆ (rtC0Inv rt st' ⋆ region (p + 8#64) (sz - 8) ⋆ scrFrame)) m1 :=
        hmCell'
      rw [hscr] at hmCell2
      exact sep_cast hmCell2 (by ac_rfl)
    exact lcnfHeap_disj_of_cell64 hmHeap
  have hst := store_cell64 (BitVec.ofNat 64 hdr) hmCell'
  have hpadd : p + BitVec.ofNat 64 0 = p := by simp
  rw [← hpadd] at hst
  refine storeAt_wp hek1 (LArg.eval_imm_self _ i64 (BitVec.ofNat 64 hdr)) trivial hevp1 hrp
    hst.1 ?_
  intro ek2 ρ2 nk hnk hek2 hagr2
  let σ' : HState := { st := st', objs := σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
  have hmPost : (cell64 p (BitVec.ofNat 64 hdr) ⋆ region (p + 8#64) (sz - 8) ⋆ σ'.mem rt ⋆ R)
      (storeMem m1 i64 (p + BitVec.ofNat 64 0) (BitVec.ofNat 64 hdr)) := by
    rw [hstate_mem_unfold]
    exact sep_cast hst.2 (by dsimp only [scrFrame, σ']; ac_rfl)
  exact hk p st' rp ek2 ρ2 nk _ hp0 hp8 hdisj hpm hremLe hremLo (by omega)
    (hinv_of_preservesMeta hinv hpm) hmPost hek2
    (argIdsBelow_mono (by omega) hrp) ((hagr2.mono (Nat.le_succ n)).trans hagr1)
    ((hagr2.eval hrp).trans hevp1)

theorem storeFields_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {pArg : LArg} {p : BitVec 64}
    {n' : Nat} {J : JEnv} {k : LM LExpr} :
    ∀ (off : Nat) (vsArgs : List LArg) (vs : List (BitVec 64))
      (F : Mem 64 → Prop) (n : Nat) (e : LExpr) (ρ : Frontend.C0.VEnv) (mem : Mem 64),
      vsArgs.length = vs.length →
      8 * vs.length ≤ 2 ^ 64 →
      (storeFields pArg off vsArgs k).run n = .ok (e, n') →
      LArg.eval ρ i64 pArg = some p → argIdsBelow pArg n →
      (∀ a ∈ vsArgs, argIdsBelow a n) →
      (∀ pr ∈ vsArgs.zip vs, LArg.eval ρ i64 pr.1 = some pr.2) →
      (region (p + BitVec.ofNat 64 off) (8 * vs.length) ⋆ F) mem →
      (∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nk : Nat) (m' : Mem 64),
        n ≤ nk → k.run nk = .ok (ek, n') → VEnvAgreeBelow n ρ' ρ →
        (array64 (p + BitVec.ofNat 64 off) vs ⋆ F) m' →
        LExpr.wp Γ QT XT ek ρ' J m') →
      LExpr.wp Γ QT XT e ρ J mem := by
  intro off vsArgs
  induction vsArgs generalizing off with
  | nil =>
    intro vs F n e ρ mem hlen _ hrun _ _ _ _ hm hk
    rcases vs with _ | ⟨_, _⟩
    · simp only [storeFields] at hrun
      simp only [List.length_nil, Nat.mul_zero, region_zero, emp_sep] at hm
      exact hk e ρ n mem (Nat.le_refl n) hrun (VEnvAgreeBelow.refl n ρ)
        (by simpa [array64_nil, emp_sep] using hm)
    · simp at hlen
  | cons va vsArgs' ih =>
    intro vs F n e ρ mem hlen hfit hrun hp hnp hids hevs hm hk
    rcases vs with _ | ⟨v, vs'⟩
    · simp at hlen
    have hva : LArg.eval ρ i64 va = some v := hevs (va, v) List.mem_cons_self
    have hvaId : argIdsBelow va n := hids va List.mem_cons_self
    have hvsIds : ∀ a ∈ vsArgs', argIdsBelow a n := fun a ha => hids a (List.mem_cons_of_mem _ ha)
    have hvsEvs : ∀ pr ∈ vsArgs'.zip vs', LArg.eval ρ i64 pr.1 = some pr.2 :=
      fun pr hpr => hevs pr (List.mem_cons_of_mem _ hpr)
    have hmul : 8 * (v :: vs').length = 8 + 8 * vs'.length := by simp; omega
    have hfit' : 8 + 8 * vs'.length ≤ 2 ^ 64 := hmul ▸ hfit
    rw [hmul, region_split hfit', ptr_add_nat_p p off 8] at hm
    have hm' : (region (p + BitVec.ofNat 64 off) 8 ⋆
        (region (p + BitVec.ofNat 64 (off + 8)) (8 * vs'.length) ⋆ F)) mem :=
      sep_cast hm (by ac_rfl)
    obtain ⟨v0, hmCell⟩ := sep_ex_l.mp (sep_mono (fun _ => region_to_cell64) hm')
    have hst := store_cell64 v hmCell
    unfold storeFields at hrun
    refine storeAt_wp hrun hva hvaId hp hnp hst.1 ?_
    intro ek1 ρ1 nk1 hn1 hek1 hagr1
    have hids1 : ∀ a ∈ vsArgs', argIdsBelow a nk1 := fun a ha => argIdsBelow_mono hn1 (hvsIds a ha)
    have hevs1 : ∀ pr ∈ vsArgs'.zip vs', LArg.eval ρ1 i64 pr.1 = some pr.2 := fun pr hpr =>
      (hagr1.eval (hvsIds pr.1 (List.of_mem_zip hpr).1)).trans (hvsEvs pr hpr)
    have hm1 :
        (region (p + BitVec.ofNat 64 (off + 8)) (8 * vs'.length) ⋆
          (cell64 (p + BitVec.ofNat 64 off) v ⋆ F))
          (storeMem mem i64 (p + BitVec.ofNat 64 off) v) :=
      sep_cast hst.2 (by ac_rfl)
    refine ih (off + 8) vs' (cell64 (p + BitVec.ofNat 64 off) v ⋆ F) nk1 ek1 ρ1 _
      (Nat.succ.inj hlen) (by omega) hek1 ((hagr1.eval hnp).trans hp)
      (argIdsBelow_mono hn1 hnp) hids1 hevs1 hm1 ?_
    intro ek2 ρ2 nk2 m' hn2 hek2 hagr2 hmArr
    refine hk ek2 ρ2 nk2 m' (Nat.le_trans hn1 hn2) hek2 ((hagr2.mono hn1).trans hagr1) ?_
    have hmOut : ((cell64 (p + BitVec.ofNat 64 off) v ⋆
        array64 ((p + BitVec.ofNat 64 off) + 8#64) vs') ⋆ F) m' := by
      rw [ptr_add_nat_p p off 8]
      exact sep_cast hmArr (by ac_rfl)
    simpa [array64_cons] using hmOut

private theorem testBit_add_mul_pow (a b k i : Nat) (ha : a < 2 ^ k) :
    (a + b * 2 ^ k).testBit i = if i < k then a.testBit i else b.testBit (i - k) := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hsplit : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hi)]
    have hmul : b * 2 ^ k = (b * 2 ^ (k - i)) * 2 ^ i := by
      rw [hsplit, Nat.mul_comm (2 ^ i), Nat.mul_assoc]
    have h1 : (a + b * 2 ^ k) / 2 ^ i = a / 2 ^ i + b * 2 ^ (k - i) := by
      rw [hmul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    have hpow2 : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
      have hk1 : k - i = (k - i - 1) + 1 := by omega
      rw [congrArg (fun x => 2 ^ x) hk1, Nat.pow_succ, Nat.mul_comm]
    have heven : (b * 2 ^ (k - i)) % 2 = 0 := by
      rw [hpow2, Nat.mul_left_comm, Nat.mul_mod_right]
    have h2 : (a / 2 ^ i + b * 2 ^ (k - i)) % 2 = (a / 2 ^ i) % 2 := by omega
    simp [h1, h2]
  · simp only [hi, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_not_lt hi)]
    have hdiv : (a + b * 2 ^ k) / 2 ^ k = b := by
      rw [Nat.add_mul_div_right _ _ hkpos, Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv]

theorem lcnfObj_ctor_header_eq (ci : LcCtor) (vs : List (BitVec 64)) (scal : List UInt8)
    (_hcidx : ci.cidx ≤ 244) (hsz : ci.size < 256) (hmax : ci.byteSize < 65536) :
    BitVec.ofNat 64 ci.header =
      ({ addr := 0#64, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
          fields := vs, scalarData := scal } : LcnfObj).header := by
  unfold LcCtor.header LcnfObj.header
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 64
  · simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi,
      decide_true, Bool.true_and]
    have h48 : 1 + ci.byteSize * 2 ^ 32 < 2 ^ 48 := by omega
    have h56 : 1 + ci.byteSize * 2 ^ 32 + ci.size * 2 ^ 48 < 2 ^ 56 := by omega
    have h32 : 1 < 2 ^ 32 := by decide
    have hsum : 1 + ci.byteSize * 2 ^ 32 + ci.size * 2 ^ 48 + ci.cidx * 2 ^ 56 =
        (1 + ci.byteSize * 2 ^ 32 + ci.size * 2 ^ 48) + ci.cidx * 2 ^ 56 := by omega
    rw [hsum, testBit_add_mul_pow _ _ 56 i h56]
    by_cases hi56 : i < 56
    · have hsum2 : 1 + ci.byteSize * 2 ^ 32 + ci.size * 2 ^ 48 =
          (1 + ci.byteSize * 2 ^ 32) + ci.size * 2 ^ 48 := rfl
      rw [ite_eq_left hi56, hsum2, testBit_add_mul_pow _ _ 48 i h48]
      by_cases hi48 : i < 48
      · rw [ite_eq_left hi48, testBit_add_mul_pow 1 ci.byteSize 32 i h32]
        by_cases hi32 : i < 32
        · simp [hi32, hi48, hi56]
        · have hbi : (1 : Nat).testBit i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2 ^ 32)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
          have hrc : (1#32 : BitVec 32).toNat.testBit i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
              (by decide : (1#32 : BitVec 32).toNat < 2 ^ 32)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
          simp [hi32, hi48, hi56, show i - 32 < 64 by omega, hbi]
      · have hbi : (1 : Nat).testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2 ^ 48)
            (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
        have hcs : ci.byteSize.testBit (i - 32) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : ci.byteSize < 2 ^ 16)
            (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
        simp [hi48, hi56, show ¬(i < 32) by omega, show i - 32 < 64 by omega,
          show i - 48 < 64 by omega, hbi, hcs]
    · have hbi : (1 : Nat).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2 ^ 56)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
      have hcs : ci.byteSize.testBit (i - 32) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : ci.byteSize < 2 ^ 16)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
      have hszb : ci.size.testBit (i - 48) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : ci.size < 2 ^ 8)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
      simp [hi56, show ¬(i < 32) by omega, show ¬(i < 48) by omega,
        show i - 32 < 64 by omega, show i - 48 < 64 by omega, show i - 56 < 64 by omega,
        hbi, hcs, hszb]
  · simp [getLsbD_ge_width _ (by omega : 64 ≤ i)]

theorem ctor_alloc_store_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {ci : LcCtor}
    {vsArgs : List LArg} {vs : List (BitVec 64)}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (allocObj rtArg ci.byteSize ci.header fun p =>
      storeFields p 8 vsArgs (k p)).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt)
    (hvsLen : vsArgs.length = vs.length) (hciSz : vs.length = ci.size)
    (hcidx : ci.cidx ≤ 244) (hsz : ci.size < 256)
    (hmin : rtMinObjBytes ≤ ci.byteSize) (hmax : ci.byteSize < 65536)
    (hcan : canAllocBytesR0 σ.st ci.byteSize)
    (hvsIds : ∀ a ∈ vsArgs, argIdsBelow a n)
    (hvsEvs : ∀ pr ∈ vsArgs.zip vs, LArg.eval ρ i64 pr.1 = some pr.2)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hk : ∀ (p : BitVec 64) (st' : RtC0State) (scal : List UInt8) (rp : LArg) (ek : LExpr)
        (ρ' : Frontend.C0.VEnv) (nr : Nat) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 →
      (∀ o ∈ σ.objs, o.addr ≠ p) →
      st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - ci.byteSize ≤ st'.rem →
      scal.length = 8 * ci.usize + ci.ssize →
      n + 1 ≤ nr →
      let newObj : LcnfObj :=
        { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
          fields := vs, scalarData := scal }
      let σ' : HState :=
        { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
      HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      (k rp).run nr = .ok (ek, n') →
      argIdsBelow rp nr → VEnvAgreeBelow n ρ' ρ → LArg.eval ρ' i64 rp = some p →
      LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  have hmod : ci.byteSize % 8 = 0 := by unfold LcCtor.byteSize; omega
  refine allocObj_wp hΓ hrun hrt hmin hmax hmod hcan hinv hm ?_
  intro p st' rp ek1 ρ1 nr1 m1 hp0 hp8 hdisj hpm hremLe hremLo hnr1 hinv1 hm1 hek1 hrp1 hagr1 hrpEv1
  have hbound : 8 + 8 * vs.length + (8 * ci.usize + ci.ssize) ≤ ci.byteSize := by
    unfold LcCtor.byteSize at *; rw [hciSz]; omega
  have hsp1 : region (p + 8#64) (ci.byteSize - 8) =
      (region (p + 8#64) (8 * vs.length) ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length)) (ci.byteSize - (8 + 8 * vs.length))) := by
    have h1 := region_split (a := p + 8#64) (n1 := 8 * vs.length)
      (n2 := ci.byteSize - (8 + 8 * vs.length)) (by omega)
    rw [show 8 * vs.length + (ci.byteSize - (8 + 8 * vs.length)) = ci.byteSize - 8 by omega,
      ptr_add_nat_p] at h1
    exact h1
  have hsp2 : region (p + BitVec.ofNat 64 (8 + 8 * vs.length))
        (ci.byteSize - (8 + 8 * vs.length)) =
      (region (p + BitVec.ofNat 64 (8 + 8 * vs.length)) (8 * ci.usize + ci.ssize) ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length + (8 * ci.usize + ci.ssize)))
          (ci.byteSize - (8 + 8 * vs.length + (8 * ci.usize + ci.ssize)))) := by
    have h2 := region_split (a := p + BitVec.ofNat 64 (8 + 8 * vs.length))
      (n1 := 8 * ci.usize + ci.ssize)
      (n2 := ci.byteSize - (8 + 8 * vs.length + (8 * ci.usize + ci.ssize))) (by omega)
    rw [show (8 * ci.usize + ci.ssize) + (ci.byteSize - (8 + 8 * vs.length +
        (8 * ci.usize + ci.ssize))) = ci.byteSize - (8 + 8 * vs.length) by omega,
      ptr_add_nat_p] at h2
    exact h2
  rw [hsp1, hsp2] at hm1
  have hvsIds1 : ∀ a ∈ vsArgs, argIdsBelow a nr1 :=
    fun a ha => argIdsBelow_mono (by omega) (hvsIds a ha)
  have hvsEvs1 : ∀ pr ∈ vsArgs.zip vs, LArg.eval ρ1 i64 pr.1 = some pr.2 := fun pr hpr =>
    (hagr1.eval (hvsIds pr.1 (List.of_mem_zip hpr).1)).trans (hvsEvs pr hpr)
  let σMid : HState := { st := st', objs := σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
  have hm1' : (region (p + BitVec.ofNat 64 8) (8 * vs.length) ⋆
      (cell64 p (BitVec.ofNat 64 ci.header) ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length)) (8 * ci.usize + ci.ssize) ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length + (8 * ci.usize + ci.ssize)))
          (ci.byteSize - (8 + 8 * vs.length + (8 * ci.usize + ci.ssize))) ⋆
        σMid.mem rt ⋆ R)) m1 :=
    sep_cast hm1 (by dsimp only [σMid]; ac_rfl)
  refine storeFields_wp 8 vsArgs vs _ nr1 _ ρ1 m1 hvsLen (by omega) hek1 hrpEv1 hrp1
    hvsIds1 hvsEvs1 hm1' ?_
  intro ek2 ρ2 nr2 m2 hnr2 hek2 hagr2 hm2
  have hmReg : (region (p + BitVec.ofNat 64 (8 + 8 * vs.length)) (8 * ci.usize + ci.ssize) ⋆
      (cell64 p (BitVec.ofNat 64 ci.header) ⋆
        array64 (p + 8#64) vs ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length + (8 * ci.usize + ci.ssize)))
          (ci.byteSize - (8 + 8 * vs.length + (8 * ci.usize + ci.ssize))) ⋆
        σMid.mem rt ⋆ R)) m2 :=
    sep_cast hm2 (by ac_rfl)
  have hmReg' : ((fun m => ∃ scal : List UInt8, scal.length = 8 * ci.usize + ci.ssize ∧
      bytes (p + BitVec.ofNat 64 (8 + 8 * vs.length)) scal m) ⋆ _) m2 :=
    sep_mono (fun _ h => by
      rw [region.eq_1] at h
      rcases h with ⟨scal, hlen, hat⟩
      exact ⟨scal, hlen, by rw [bytes.eq_1]; exact hat.symm⟩) hmReg
  obtain ⟨scal, hmScal⟩ := sep_ex_l.mp hmReg'
  obtain ⟨hscal, hmBytes⟩ := sep_pure_l.mp hmScal
  let newObj : LcnfObj :=
    { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
      fields := vs, scalarData := scal }
  let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
  have hhdr := lcnfObj_ctor_header_eq ci vs scal hcidx hsz hmax
  obtain ⟨t1, t2, t3, t4, t5⟩ := tag_ne_special hcidx
  have hobjMem : lcnfObjMem newObj =
      (cell64 p (BitVec.ofNat 64 ci.header) ⋆ array64 (p + 8#64) vs ⋆
        bytes (p + BitVec.ofNat 64 (8 + 8 * vs.length)) scal ⋆
        region (p + BitVec.ofNat 64 (8 + 8 * vs.length + scal.length))
          (ci.byteSize - (8 + 8 * vs.length + scal.length))) := by
    simp only [lcnfObjMem, newObj, t1, t2, t3, t4, t5, ↓reduceIte]
    rw [hhdr]
    rfl
  have hmObj : (σ'.mem rt ⋆ R) m2 := by
    rw [hscal] at hobjMem
    have hmSplit : (lcnfObjMem newObj ⋆ σMid.mem rt ⋆ R) m2 := by
      rw [hobjMem]
      exact sep_cast hmBytes (by ac_rfl)
    simp only [σ', hstate_mem_unfold, lcnfHeap]
    simp only [σMid, hstate_mem_unfold] at hmSplit
    exact sep_cast hmSplit (by ac_rfl)
  exact hk p st' scal rp ek2 ρ2 nr2 m2 hp0 hp8 hdisj hpm hremLe hremLo hscal
    (by omega) hinv1 hmObj hek2 (argIdsBelow_mono hnr2 hrp1) ((hagr2.mono (by omega)).trans hagr1)
    ((hagr2.eval hrp1).trans hrpEv1)

theorem boxU64_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg xArg : LArg} {vx : BitVec 64}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (boxU64 rtArg xArg k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt)
    (hx : LArg.eval ρ i64 xArg = some vx) (hnx : argIdsBelow xArg n)
    (hcan : canAllocBytesR0 σ.st 16)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hk : ∀ (p : BitVec 64) (st' : RtC0State) (rp : LArg) (ek : LExpr)
        (ρ' : Frontend.C0.VEnv) (nr : Nat) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 →
      (∀ o ∈ σ.objs, o.addr ≠ p) →
      st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - 16 ≤ st'.rem →
      n + 1 ≤ nr →
      let newObj : LcnfObj :=
        { addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
          scalarData := writeNatLE vx.toNat 8 }
      let σ' : HState :=
        { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
      HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      (k rp).run nr = .ok (ek, n') →
      argIdsBelow rp nr → VEnvAgreeBelow n ρ' ρ → LArg.eval ρ' i64 rp = some p →
      LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold boxU64 at hrun
  refine allocObj_wp hΓ hrun hrt (by unfold rtMinObjBytes; decide) (by decide) (by decide)
    hcan hinv hm ?_
  intro p st' rp ek1 ρ1 nr1 m1 hp0 hp8 hdisj hpm hremLe hremLo hnr1 hinv1 hm1 hek1 hrp1 hagr1 hrpEv1
  let σMid : HState := { st := st', objs := σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
  have hreg : (region (p + 8#64) 8 ⋆
      (cell64 p (BitVec.ofNat 64 (1 + 16 * 2 ^ 32)) ⋆ σMid.mem rt ⋆ R)) m1 := by
    simpa using sep_cast hm1 (by dsimp only [σMid]; ac_rfl)
  obtain ⟨v0, hm8⟩ := sep_ex_l.mp (sep_mono (fun _ => region_to_cell64) hreg)
  have hst := store_cell64 vx hm8
  have hnx1 : argIdsBelow xArg nr1 := argIdsBelow_mono (by omega) hnx
  have hx1 : LArg.eval ρ1 i64 xArg = some vx := (hagr1.eval hnx).trans hx
  refine storeAt_wp hek1 hx1 hnx1 hrpEv1 hrp1 hst.1 ?_
  intro ek2 ρ2 nr2 hnr2 hek2 hagr2
  let newObj : LcnfObj :=
    { addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
      scalarData := writeNatLE vx.toNat 8 }
  let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
  have hhdr : BitVec.ofNat 64 (1 + 16 * 2 ^ 32) = newObj.header := by
    have hval : BitVec.ofNat 64 (1 + 16 * 2 ^ 32) =
        (BitVec.setWidth 64 (1#32) ||| (BitVec.ofNat 64 16 <<< 32) |||
          (BitVec.ofNat 64 0 <<< 48) ||| (BitVec.ofNat 64 0 <<< 56)) := by decide
    rw [hval]
    rfl
  have hlen : (writeNatLE vx.toNat 8).length = 8 := by
    rw [writeNatLE_eq_toBytes, Int.toBytes_length]
  obtain ⟨t1, t2, t3, t4, t5⟩ := tag_ne_special (by decide : 0 ≤ 244)
  have hobjMem : lcnfObjMem newObj =
      (cell64 p (BitVec.ofNat 64 (1 + 16 * 2 ^ 32)) ⋆ cell64 (p + 8#64) vx) := by
    simp only [lcnfObjMem, newObj, t1, t2, t3, t4, t5, ↓reduceIte, array64_nil, sep_emp, hlen,
      List.length_nil, Nat.mul_zero, Nat.add_zero]
    rw [show 16 - (8 + 8) = 0 by decide, region_zero, sep_emp, ← hhdr,
      show p + BitVec.ofNat 64 8 = p + 8#64 from rfl, bytes_writeNatLE8_eq_cell64]
  have hmPost : (σ'.mem rt ⋆ R) (storeMem m1 i64 (p + BitVec.ofNat 64 8) vx) := by
    have hm1' := hst.2
    rw [show (p + BitVec.ofNat 64 8) = p + 8#64 from rfl] at hm1'
    have hm2' : (lcnfObjMem newObj ⋆ σMid.mem rt ⋆ R)
        (storeMem m1 i64 (p + 8#64) vx) := by
      rw [hobjMem]
      exact sep_cast hm1' (by ac_rfl)
    simp only [σ', hstate_mem_unfold, lcnfHeap]
    simp only [σMid, hstate_mem_unfold] at hm2'
    exact sep_cast hm2' (by ac_rfl)
  exact hk p st' rp ek2 ρ2 nr2 _ hp0 hp8 hdisj hpm hremLe hremLo (by omega) hinv1 hmPost
    hek2 (argIdsBelow_mono hnr2 hrp1) ((hagr2.mono (by omega)).trans hagr1)
    ((hagr2.eval hrp1).trans hrpEv1)

end LeanQbe.T.LeanLCNF.Sem
