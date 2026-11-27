module

public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof2b
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof3b
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof4
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof
public import LeanQbe.T.LeanLCNF.LcnfC0RtProof

/-!
# Soundness & Concrete Non-Vacuity Proofs for `LcnfC0Strings` (R2b + `lcnf_clo_under`)

* `rtR2bMod_tableImpl`, `rtR2bMod_allFns_wf`, `rtR2bMod_moduleOk`, `rtR2bMod_fn_sound`
* Public soundness wrappers (`lcnf_*_sound`) for all 13 R2b runtime functions
* Concrete `Mem 64` non-vacuity theorems (`nv_*`, `X := fun _ _ _ _ => False`) covering
  strings, UTF-8 chars/positions, lists/arrays/`lcnf_ba_data`, `lcnf_nat_to_str` (boxed
  zero, boxed nonzero, and mpz), and `lcnf_clo_under` via `rtC0Env_clo_under_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

/-! ## Module Well-Formedness & `TableImpl` / `ModuleOk` -/

private theorem allFns_of_mem {P : Fn → Prop} {fs : List Fn}
    (h : ∀ f ∈ fs, P f) : AllFns P fs := by
  induction fs with
  | nil => trivial
  | cons f fs ih => exact ⟨h f (by simp), ih (fun g hg => h g (by simp [hg]))⟩

theorem rtR2bMod_allFns_wf : AllFns Fn.Wf rtR2bMod.fns :=
  allFns_of_mem rtR2b_fns_wf

theorem rtR2bMod_tableImpl : TableImpl rtR2bEnv rtR2bMod.fns rtR2bSpecEntries :=
  ⟨⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_alloc_mpz_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_str_alloc_cap_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_utf8_len_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_utf8_write_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_utf8_decode_step_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, r2b_utf8_decode_cp_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_str_alloc_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_char_op_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_push_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_append_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_cmp_op_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_pos_op_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_to_list_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_string_mk_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_ba_data_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_array_mk_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_array_to_list_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_array_replicate_wp⟩,
   ⟨⟨rfl, ⟨rfl, rfl⟩⟩, lcnf_nat_to_str_wp⟩,
   trivial⟩

theorem rtR2bMod_moduleOk : ModuleOk rtR2bEnv rtR2bMod :=
  Env.ofTable_moduleOk rtR2b_checkAcyclic rtR2bMod_allFns_wf rtR2bMod_tableImpl

theorem rtR2bMod_fn_sound :
    ∀ {fn : Fn}, fn ∈ rtR2bMod.fns →
      ∀ {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost},
        rtR2bEnv fn.name fn.as fn.rs xs m Q X → Func.wp rtR2bEnv fn.body xs m Q X :=
  fun {fn} hfn {xs} {m} {Q} {X} hpre =>
    Env.ofTable_sound (List.nodup_append.mp rtR2bMod_moduleOk.nodup).1
      rtR2bMod_tableImpl fn hfn xs m Q X hpre

/-! ## Exported R2b Runtime Soundness Theorems -/

theorem lcnf_str_alloc_sound :
    ∀ xs m Q X, lcnfStrAllocSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_str_alloc_body xs m Q X :=
  lcnf_str_alloc_wp

theorem lcnf_char_op_sound :
    ∀ xs m Q X, lcnfCharOpSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_char_op_body xs m Q X :=
  lcnf_char_op_wp

theorem lcnf_string_push_sound :
    ∀ xs m Q X, lcnfStringPushSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_push_body xs m Q X :=
  lcnf_string_push_wp

theorem lcnf_string_append_sound :
    ∀ xs m Q X, lcnfStringAppendSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_append_body xs m Q X :=
  lcnf_string_append_wp

theorem lcnf_string_cmp_op_sound :
    ∀ xs m Q X, lcnfStringCmpOpSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_cmp_op_body xs m Q X :=
  lcnf_string_cmp_op_wp

theorem lcnf_string_pos_op_sound :
    ∀ xs m Q X, lcnfStringPosOpSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_pos_op_body xs m Q X :=
  lcnf_string_pos_op_wp

theorem lcnf_string_to_list_sound :
    ∀ xs m Q X, lcnfStringToListSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_to_list_body xs m Q X :=
  lcnf_string_to_list_wp

theorem lcnf_string_mk_sound :
    ∀ xs m Q X, lcnfStringMkSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_mk_body xs m Q X :=
  lcnf_string_mk_wp

theorem lcnf_ba_data_sound :
    ∀ xs m Q X, lcnfBaDataSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_ba_data_body xs m Q X :=
  lcnf_ba_data_wp

theorem lcnf_array_mk_sound :
    ∀ xs m Q X, lcnfArrayMkSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_array_mk_body xs m Q X :=
  lcnf_array_mk_wp

theorem lcnf_array_to_list_sound :
    ∀ xs m Q X, lcnfArrayToListSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_array_to_list_body xs m Q X :=
  lcnf_array_to_list_wp

theorem lcnf_array_replicate_sound :
    ∀ xs m Q X, lcnfArrayReplicateSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_array_replicate_body xs m Q X :=
  lcnf_array_replicate_wp

theorem lcnf_nat_to_str_sound :
    ∀ xs m Q X, lcnfNatToStrSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_nat_to_str_body xs m Q X :=
  lcnf_nat_to_str_wp

/-! ## Concrete `Mem 64` Non-Vacuity Helpers -/

private theorem u64ListBytes_cons (v : BitVec 64) (vs : List (BitVec 64)) :
    u64ListBytes (v :: vs) = Int.toBytes 8 v.toInt ++ u64ListBytes vs :=
  u64ListBytes.eq_2 v vs

private theorem u64_bytes_len (v : BitVec 64) : (Int.toBytes 8 v.toInt).length = 8 := by
  simp [Int.toBytes]

private theorem u64ListBytes_len (xs : List (BitVec 64)) :
    (u64ListBytes xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [u64ListBytes_cons, List.length_append, u64_bytes_len, ih, List.length_cons]
    omega

private theorem nvR2RtBytes_len : nvR2RtBytes.length = 34216 := by
  simp only [nvR2RtBytes, List.length_append, List.length_replicate, u64ListBytes_len,
    nvR2HdrWords, List.length_cons, List.length_nil]
  have hcap : nvArenaCap = 512 := rfl
  rw [hcap]

private theorem sml {P P' Q : Mem 64 → Prop} (h : ∀ m, P m → P' m) :
    ∀ m, (P ⋆ Q) m → (P' ⋆ Q) m := fun _ hm => sep_mono h hm

private theorem smr {P Q Q' : Mem 64 → Prop} (h : ∀ m, Q m → Q' m) :
    ∀ m, (P ⋆ Q) m → (P ⋆ Q') m := fun _ hm => sep_mono_r h hm

private theorem sm2 {P1 P1' P2 P2' : Mem 64 → Prop}
    (h1 : ∀ m, P1 m → P1' m) (h2 : ∀ m, P2 m → P2' m) :
    ∀ m, (P1 ⋆ P2) m → (P1' ⋆ P2') m := fun m hm => sep_mono2 h1 h2 m hm

private theorem bytes_u64_to_cell64 (a v : BitVec 64) :
    ∀ (m : Mem 64), bytes a (Int.toBytes 8 v.toInt) m → cell64 a v m := by
  intro m h; rcases h with rfl; exact cell64_bytes a v

private theorem bytes_at_self (a : BitVec 64) (bs : List UInt8) :
    bytes a bs (bs.At a) := rfl

private theorem sep_bytes_split {a : BitVec 64} {xs ys : List UInt8} (R : Mem 64 → Prop)
    (hlen : xs.length + ys.length ≤ 2 ^ 64) :
    ∀ (m : Mem 64), (bytes a (xs ++ ys) ⋆ R) m →
      (bytes a xs ⋆ (bytes (a + BitVec.ofNat 64 xs.length) ys ⋆ R)) m := by
  intro m h
  rw [bytes_append a xs ys hlen] at h
  exact sep_cast h (Std.ExtHashMap.sep_assoc _ _ _)

private theorem hdr4_bytes_to_cells (a w0 w1 w2 w3 : BitVec 64) (R : Mem 64 → Prop) :
    ∀ (m : Mem 64), (bytes a (u64ListBytes [w0, w1, w2, w3]) ⋆ R) m →
      (cell64 a w0 ⋆ (cell64 (a + 8#64) w1 ⋆
        (cell64 (a + 16#64) w2 ⋆ (cell64 (a + 24#64) w3 ⋆ R)))) m := by
  intro m h
  simp only [u64ListBytes_cons] at h
  have hlen3 : (Int.toBytes 8 w3.toInt).length + ([] : List UInt8).length ≤ 2 ^ 64 := by
    rw [u64_bytes_len]; decide
  have hlen2 :
      (Int.toBytes 8 w2.toInt).length +
        (Int.toBytes 8 w3.toInt ++ u64ListBytes []).length ≤ 2 ^ 64 := by
    simp only [u64ListBytes, List.length_append, List.length_nil, u64_bytes_len]; decide
  have hlen1 :
      (Int.toBytes 8 w1.toInt).length +
        (Int.toBytes 8 w2.toInt ++ (Int.toBytes 8 w3.toInt ++ u64ListBytes [])).length ≤
        2 ^ 64 := by
    simp only [u64ListBytes, List.length_append, List.length_nil, u64_bytes_len]; decide
  have hlen0 :
      (Int.toBytes 8 w0.toInt).length +
        (Int.toBytes 8 w1.toInt ++
          (Int.toBytes 8 w2.toInt ++ (Int.toBytes 8 w3.toInt ++ u64ListBytes []))).length ≤
        2 ^ 64 := by
    simp only [u64ListBytes, List.length_append, List.length_nil, u64_bytes_len]; decide
  have h0 := sep_bytes_split R hlen0 m h
  rw [u64_bytes_len] at h0
  have h1 := smr (sep_bytes_split R hlen1) m h0
  rw [u64_bytes_len] at h1
  have h2 := smr (smr (sep_bytes_split R hlen2)) m h1
  rw [u64_bytes_len] at h2
  have hnil : u64ListBytes [] = [] := rfl
  rw [hnil, List.append_nil] at h2
  have hc := sm2 (bytes_u64_to_cell64 a w0)
    (sm2 (bytes_u64_to_cell64 (a + 8#64) w1)
      (sm2 (bytes_u64_to_cell64 (a + 8#64 + 8#64) w2)
        (sml (bytes_u64_to_cell64 (a + 8#64 + 8#64 + 8#64) w3)))) m h2
  have h16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by
    rw [BitVec.add_assoc]; exact congrArg (a + ·) (by decide)
  have h24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (a + ·) (by decide)
  rw [show BitVec.ofNat 64 8 = 8#64 from rfl] at h16 h24 ⊢
  rw [h24, h16] at hc
  exact hc

private theorem hdr3_bytes_to_cells (a w0 w1 w2 : BitVec 64) (R : Mem 64 → Prop) :
    ∀ (m : Mem 64), (bytes a (u64ListBytes [w0, w1, w2]) ⋆ R) m →
      (cell64 a w0 ⋆ (cell64 (a + 8#64) w1 ⋆ (cell64 (a + 16#64) w2 ⋆ R))) m := by
  intro m h
  have hnil : u64ListBytes [] = [] := rfl
  simp only [u64ListBytes_cons, hnil, List.append_nil] at h
  have hlen1 :
      (Int.toBytes 8 w1.toInt).length + (Int.toBytes 8 w2.toInt).length ≤ 2 ^ 64 := by
    simp only [u64_bytes_len]; decide
  have hlen0 :
      (Int.toBytes 8 w0.toInt).length +
        (Int.toBytes 8 w1.toInt ++ Int.toBytes 8 w2.toInt).length ≤ 2 ^ 64 := by
    simp only [List.length_append, u64_bytes_len]; decide
  have h0 := sep_bytes_split R hlen0 m h
  rw [u64_bytes_len] at h0
  have h1 := smr (sep_bytes_split R hlen1) m h0
  rw [u64_bytes_len] at h1
  have hc := sm2 (bytes_u64_to_cell64 a w0)
    (sm2 (bytes_u64_to_cell64 (a + 8#64) w1)
      (sml (bytes_u64_to_cell64 (a + 8#64 + 8#64) w2))) m h1
  have h16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by
    rw [BitVec.add_assoc]; exact congrArg (a + ·) (by decide)
  rw [show BitVec.ofNat 64 8 = 8#64 from rfl] at h16 ⊢
  rw [h16] at hc
  exact hc

def mkStrBytes (cap : Nat) (payload : List UInt8) (len : Nat) : List UInt8 :=
  u64ListBytes [strHeaderWord, BitVec.ofNat 64 (payload.length + 1),
    BitVec.ofNat 64 cap, BitVec.ofNat 64 len] ++
  payload ++ [0] ++ List.replicate (strAllocBytes cap - (32 + payload.length + 1)) 0

private theorem strObjMem_of_bytes (p : BitVec 64) (cap len : Nat) (payload : List UInt8)
    (R : Mem 64 → Prop) (hcap : cap ≤ strMaxCap) (hlen : payload.length + 1 ≤ cap) :
    ∀ (m : Mem 64), (bytes p (mkStrBytes cap payload len) ⋆ R) m →
      (lcnfObjMem (mkStrObj p 1#32 cap payload len) ⋆ R) m := by
  intro m h
  have h32 :
      (u64ListBytes [strHeaderWord, BitVec.ofNat 64 (payload.length + 1),
        BitVec.ofNat 64 cap, BitVec.ofNat 64 len]).length = 32 := by
    simp only [u64ListBytes_len, List.length_cons, List.length_nil]
  have hfit :
      (u64ListBytes [strHeaderWord, BitVec.ofNat 64 (payload.length + 1),
        BitVec.ofNat 64 cap, BitVec.ofNat 64 len]).length +
        (payload ++ ([0] ++
          List.replicate (strAllocBytes cap - (32 + payload.length + 1)) 0)).length ≤ 2 ^ 64 := by
    rw [h32]
    simp only [List.length_append, List.length_singleton, List.length_replicate]
    unfold strAllocBytes align8 strMaxCap at *; omega
  unfold mkStrBytes at h
  rw [List.append_assoc, List.append_assoc] at h
  have h0 := sep_bytes_split R hfit m h
  rw [h32] at h0
  have h1 := hdr4_bytes_to_cells p strHeaderWord (BitVec.ofNat 64 (payload.length + 1))
    (BitVec.ofNat 64 cap) (BitVec.ofNat 64 len) _ m h0
  have ha1 :
      payload.length +
        ([(0 : UInt8)] ++
          List.replicate (strAllocBytes cap - (32 + payload.length + 1)) 0).length ≤ 2 ^ 64 := by
    simp only [List.length_append, List.length_singleton, List.length_replicate]
    unfold strAllocBytes align8 strMaxCap at *; omega
  have ha2 :
      ([(0 : UInt8)] : List UInt8).length +
        (List.replicate (strAllocBytes cap - (32 + payload.length + 1)) (0 : UInt8)).length ≤
        2 ^ 64 := by
    simp only [List.length_singleton, List.length_replicate]
    unfold strAllocBytes align8 strMaxCap at *; omega
  have htailStep :
      ∀ (mx : Mem 64),
        (bytes (p + 32#64)
            (payload ++ ([(0 : UInt8)] ++
              List.replicate (strAllocBytes cap - (32 + payload.length + 1)) (0 : UInt8))) ⋆
          R) mx →
        (bytes (p + 32#64) payload ⋆
          bytes (p + 32#64 + BitVec.ofNat 64 payload.length) [0] ⋆
          region (p + 32#64 + BitVec.ofNat 64 payload.length + 1#64)
            (strAllocBytes cap - (32 + payload.length + 1)) ⋆ R) mx := by
    intro mx hx
    have hs1 := sep_bytes_split R ha1 mx hx
    have hs2 := smr (sep_bytes_split R ha2) mx hs1
    simp only [List.length_singleton] at hs2
    have hreg : ∀ (mz : Mem 64),
        bytes (p + 32#64 + BitVec.ofNat 64 payload.length + BitVec.ofNat 64 1)
          (List.replicate (strAllocBytes cap - (32 + payload.length + 1)) 0) mz →
        region (p + 32#64 + BitVec.ofNat 64 payload.length + 1#64)
          (strAllocBytes cap - (32 + payload.length + 1)) mz := by
      intro mz hz
      have hz' := _root_.LeanQbe.T.LeanLCNF.bytes_to_region hz
      rw [List.length_replicate] at hz'; exact hz'
    have hs3 := smr (smr (sml hreg)) mx hs2
    exact sep_cast hs3 (by simp only [Std.ExtHashMap.sep_assoc])
  have h2 := smr (smr (smr (smr htailStep))) m h1
  exact mkStrObj_mem_of_parts hcap hlen (sep_cast h2 (by simp only [Std.ExtHashMap.sep_assoc]))

private theorem baObjMem_of_bytes (p : BitVec 64) (cap : Nat) (data : List UInt8)
    (R : Mem 64 → Prop) (hcap : cap ≤ baMaxCap) (hlen : data.length ≤ cap) :
    ∀ (m : Mem 64),
      (bytes p (u64ListBytes [baHeaderWord, BitVec.ofNat 64 data.length, BitVec.ofNat 64 cap] ++
        data ++ List.replicate (baAllocBytes cap - (24 + data.length)) 0) ⋆ R) m →
      (lcnfObjMem (mkBaObj p 1#32 cap data) ⋆ R) m := by
  intro m h
  have h24 :
      (u64ListBytes [baHeaderWord, BitVec.ofNat 64 data.length, BitVec.ofNat 64 cap]).length =
        24 := by
    simp only [u64ListBytes_len, List.length_cons, List.length_nil]
  rw [List.append_assoc] at h
  have h0 := sep_bytes_split R (by
    rw [h24]; simp only [List.length_append, List.length_replicate]
    unfold baAllocBytes align8 baMaxCap at *; omega) m h
  rw [h24] at h0
  have h1 := hdr3_bytes_to_cells p baHeaderWord (BitVec.ofNat 64 data.length)
    (BitVec.ofNat 64 cap) _ m h0
  have ha : data.length +
      (List.replicate (baAllocBytes cap - (24 + data.length)) (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [List.length_replicate]; unfold baAllocBytes align8 baMaxCap at *; omega
  have htailStep :
      ∀ (mx : Mem 64),
        (bytes (p + 24#64)
            (data ++ List.replicate (baAllocBytes cap - (24 + data.length)) (0 : UInt8)) ⋆
          R) mx →
        (bytes (p + 24#64) data ⋆
          region (p + 24#64 + BitVec.ofNat 64 data.length) (baAllocBytes cap - 24 - data.length) ⋆
          R) mx := by
    intro mx hx
    have hs1 := sep_bytes_split R ha mx hx
    have hreg : ∀ (mz : Mem 64),
        bytes (p + 24#64 + BitVec.ofNat 64 data.length)
          (List.replicate (baAllocBytes cap - (24 + data.length)) 0) mz →
        region (p + 24#64 + BitVec.ofNat 64 data.length) (baAllocBytes cap - 24 - data.length)
          mz := by
      intro mz hz
      have hz' := _root_.LeanQbe.T.LeanLCNF.bytes_to_region hz
      rw [List.length_replicate, show baAllocBytes cap - (24 + data.length) =
        baAllocBytes cap - 24 - data.length by omega] at hz'
      exact hz'
    have hs2 := smr (sml hreg) mx hs1
    exact sep_cast hs2 (by simp only [Std.ExtHashMap.sep_assoc])
  have h2 := smr (smr (smr htailStep)) m h1
  exact mkBaObj_mem_of_parts (sep_cast h2 (by simp only [Std.ExtHashMap.sep_assoc]))

private theorem arrObjMem2_of_bytes (p v0 v1 : BitVec 64) (R : Mem 64 → Prop) :
    ∀ (m : Mem 64),
      (bytes p (u64ListBytes ([arrHeaderWord, 2#64, 4#64] ++ [v0, v1]) ++
        List.replicate 16 0) ⋆ R) m →
      (lcnfObjMem (mkArrObj p 1#32 4 [v0, v1]) ⋆ R) m := by
  intro m h
  have h24 : (u64ListBytes [arrHeaderWord, 2#64, 4#64]).length = 24 := by
    simp only [u64ListBytes_len, List.length_cons, List.length_nil]
  have h16 : (u64ListBytes [v0, v1]).length = 16 := by
    simp only [u64ListBytes_len, List.length_cons, List.length_nil]
  have hnil : u64ListBytes [] = [] := rfl
  have hu : u64ListBytes ([arrHeaderWord, 2#64, 4#64] ++ [v0, v1]) =
      u64ListBytes [arrHeaderWord, 2#64, 4#64] ++ u64ListBytes [v0, v1] := by
    simp only [List.cons_append, List.nil_append, u64ListBytes_cons, hnil,
      List.append_assoc, List.append_nil]
  rw [hu, List.append_assoc] at h
  have h0 := sep_bytes_split R
    (by rw [h24, List.length_append, h16, List.length_replicate]; decide) m h
  rw [h24] at h0
  have h1 := hdr3_bytes_to_cells p arrHeaderWord 2#64 4#64 _ m h0
  have ha16 : (u64ListBytes [v0, v1]).length + (List.replicate 16 (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [h16, List.length_replicate]; decide
  have hmA : ∀ (mx : Mem 64), bytes (p + 24#64) (u64ListBytes [v0, v1]) mx →
      array64 (p + 24#64) [v0, v1] mx := by
    intro mx hx
    simp only [u64ListBytes_cons, hnil, List.append_nil] at hx
    rw [bytes_append _ _ _ (by simp)] at hx
    simp only [u64_bytes_len] at hx
    have hx' := sm2 (bytes_u64_to_cell64 (p + 24#64) v0)
      (bytes_u64_to_cell64 (p + 24#64 + BitVec.ofNat 64 8) v1) mx hx
    rw [show (BitVec.ofNat 64 8 : BitVec 64) = 8#64 from rfl] at hx'
    rw [array64_cons, array64_cons, array64_nil, Std.ExtHashMap.sep_emp]
    exact hx'
  have hmReg : ∀ (mx : Mem 64), bytes (p + 24#64 + 16#64) (List.replicate 16 0) mx →
      region (p + BitVec.ofNat 64 (24 + 8 * 2)) (8 * (4 - 2)) mx := by
    intro mx hx
    have hx' := _root_.LeanQbe.T.LeanLCNF.bytes_to_region hx
    have hpe : p + 24#64 + 16#64 = p + BitVec.ofNat 64 (24 + 8 * 2) := by
      rw [BitVec.add_assoc]; exact congrArg (p + ·) (by decide)
    rw [List.length_replicate, hpe] at hx'
    exact hx'
  have htail : ∀ (mx : Mem 64),
      (bytes (p + 24#64) (u64ListBytes [v0, v1] ++ List.replicate 16 0) ⋆ R) mx →
      (array64 (p + 24#64) [v0, v1] ⋆
        (region (p + BitVec.ofNat 64 (24 + 8 * 2)) (8 * (4 - 2)) ⋆ R)) mx := by
    intro mx hx
    have hs1 := sep_bytes_split R ha16 mx hx
    rw [h16, show BitVec.ofNat 64 16 = 16#64 from rfl] at hs1
    exact sm2 hmA (sml hmReg) mx hs1
  have hfin := smr (smr (smr htail)) m h1
  have htag : (mkArrObj p 1#32 4 [v0, v1]).tag = arrayTag := rfl
  unfold lcnfObjMem
  rw [htag, ite_eq_right (by decide), ite_eq_left rfl, mkArrObj_header]
  simp only [mkArrObj, List.length_cons, List.length_nil]
  exact sep_cast hfin (by simp only [Std.ExtHashMap.sep_assoc])

/-! ## Concrete `Mem 64` Non-Vacuity Witnesses -/

def nvStr1Addr : BitVec 64 := 0x185a8#64
def nvStr2Addr : BitVec 64 := nvStr1Addr + 40#64
def nvStr1 : LcnfObj := mkStrObj nvStr1Addr 1#32 8 [65, 66] 2
def nvStr2 : LcnfObj := mkStrObj nvStr2Addr 1#32 8 [65, 67] 2
def nvStr1Bytes : List UInt8 := mkStrBytes 8 [65, 66] 2
def nvStr2Bytes : List UInt8 := mkStrBytes 8 [65, 67] 2
def nvStrSlabMem : Mem 64 := (nvR2RtBytes ++ nvStr1Bytes ++ nvStr2Bytes).At nvRtAddr

def nvNode2Addr : BitVec 64 := nvStr1Addr
def nvNode1Addr : BitVec 64 := nvNode2Addr + 24#64
def nvNode2 : LcnfObj := mkListConsObj nvNode2Addr 1#32 (boxNat 66) 1#64
def nvNode1 : LcnfObj := mkListConsObj nvNode1Addr 1#32 (boxNat 65) nvNode2Addr
def nvConsListBytes : List UInt8 :=
  u64ListBytes [listConsHeaderWord, boxNat 66, 1#64] ++
  u64ListBytes [listConsHeaderWord, boxNat 65, nvNode2Addr]
def nvConsListSlabMem : Mem 64 := (nvR2RtBytes ++ nvConsListBytes).At nvRtAddr

def nvMpz1 : LcnfObj :=
  { addr := nvStr1Addr, rc := 1#32, csSz := 0, other := 0, tag := mpzTag,
    cap := 1, arrSize := 1, limbs := [7#64] }
def nvMpz1Bytes : List UInt8 :=
  u64ListBytes [mpzHeaderWord, 1#64 ||| (1#64 <<< 32), 7#64]
def nvMpzSlabMem : Mem 64 := (nvR2RtBytes ++ nvMpz1Bytes).At nvRtAddr

def nvClo0 : LcnfObj :=
  { addr := nvStr1Addr, rc := 1#32, csSz := 32, other := 0, tag := closureTag,
    funId := 1024#64, arity := 2, fields := [1#64] }
def nvClo0Bytes : List UInt8 :=
  u64ListBytes [nvClo0.header, nvClo0.funId, nvClo0.cloMeta, 1#64]
def nvCloSlabMem : Mem 64 := (nvR2RtBytes ++ nvClo0Bytes).At nvRtAddr

private theorem nvStr1Addr_eq : nvRtAddr + BitVec.ofNat 64 nvR2RtBytes.length = nvStr1Addr := by
  rw [nvR2RtBytes_len]; decide

private theorem nvRtMem_inv : (rtC0Inv nvRtAddr nvRtSt) (nvR2RtBytes.At nvRtAddr) := by
  have h := nvRtSt_inv (R := Std.ExtHashMap.emp) (by
    rw [Std.ExtHashMap.sep_emp]; exact bytes_at_self nvRtAddr nvR2RtBytes)
  rw [Std.ExtHashMap.sep_emp] at h
  exact h

private theorem nvStrSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvStr1 ⋆ lcnfObjMem nvStr2) nvStrSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ (nvStr1Bytes ++ nvStr2Bytes)) ⋆
      Std.ExtHashMap.emp) nvStrSlabMem := by
    rw [Std.ExtHashMap.sep_emp, ← List.append_assoc]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + (nvStr1Bytes ++ nvStr2Bytes).length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len, List.length_append]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvStrSlabMem h0
  rw [nvStr1Addr_eq] at h1
  have h2 := nvRtSt_inv h1
  have h3 := sep_mono_r (sep_bytes_split Std.ExtHashMap.emp (by decide)) h2
  have h4 := sep_mono_r (strObjMem_of_bytes nvStr1Addr 8 2 [65, 66] _
    (by decide) (by decide)) h3
  have hs2 : nvStr1Addr + BitVec.ofNat 64 nvStr1Bytes.length = nvStr2Addr := by decide
  rw [hs2] at h4
  have h5 := sep_mono_r (smr (strObjMem_of_bytes nvStr2Addr 8 2 [65, 67] _
    (by decide) (by decide))) h4
  rw [Std.ExtHashMap.sep_emp] at h5
  exact sep_cast h5 (by rw [← Std.ExtHashMap.sep_assoc]; rfl)

private theorem nvConsListSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvNode1, nvNode2]) nvConsListSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ nvConsListBytes) ⋆ Std.ExtHashMap.emp)
      nvConsListSlabMem := by
    rw [Std.ExtHashMap.sep_emp]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + nvConsListBytes.length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvConsListSlabMem h0
  rw [nvStr1Addr_eq] at h1
  have h2 := nvRtSt_inv h1
  have h3 : (rtC0Inv nvRtAddr nvRtSt ⋆
      (bytes nvNode2Addr (u64ListBytes [listConsHeaderWord, boxNat 66, 1#64]) ⋆
        (bytes nvNode1Addr (u64ListBytes [listConsHeaderWord, boxNat 65, nvNode2Addr]) ⋆
          Std.ExtHashMap.emp))) nvConsListSlabMem := by
    have hsplit := sep_mono_r (sep_bytes_split Std.ExtHashMap.emp (by decide)) h2
    have h24 : (u64ListBytes [listConsHeaderWord, boxNat 66, 1#64]).length = 24 := by
      simp only [u64ListBytes_len, List.length_cons, List.length_nil]
    rw [h24] at hsplit
    exact hsplit
  have hn2 : ∀ mx, bytes nvNode2Addr (u64ListBytes [listConsHeaderWord, boxNat 66, 1#64]) mx →
      lcnfObjMem nvNode2 mx := by
    intro mx hx
    rw [← Std.ExtHashMap.sep_emp (bytes nvNode2Addr _)] at hx
    have hc := hdr3_bytes_to_cells nvNode2Addr listConsHeaderWord (boxNat 66) 1#64 _ mx hx
    have hm := mkListConsObj_mem (R := Std.ExtHashMap.emp)
      (p := nvNode2Addr) (hd := boxNat 66) (tl := 1#64) (by decide) (by decide)
      (sep_cast hc (by rw [← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc]))
    rw [Std.ExtHashMap.sep_emp] at hm; exact hm
  have hn1 : ∀ mx,
      (bytes nvNode1Addr (u64ListBytes [listConsHeaderWord, boxNat 65, nvNode2Addr]) ⋆
        Std.ExtHashMap.emp) mx → lcnfObjMem nvNode1 mx := by
    intro mx hx
    have hc := hdr3_bytes_to_cells nvNode1Addr listConsHeaderWord (boxNat 65) nvNode2Addr _ mx hx
    have hm := mkListConsObj_mem (R := Std.ExtHashMap.emp)
      (p := nvNode1Addr) (hd := boxNat 65) (tl := nvNode2Addr) (by decide) (by decide)
      (sep_cast hc (by rw [← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc]))
    rw [Std.ExtHashMap.sep_emp] at hm; exact hm
  have h4 := sep_mono_r (sep_mono2 hn2 hn1) h3
  change (rtC0Inv nvRtAddr nvRtSt ⋆ (lcnfObjMem nvNode2 ⋆ lcnfObjMem nvNode1))
    nvConsListSlabMem at h4
  rw [Std.ExtHashMap.sep_comm (lcnfObjMem nvNode2) (lcnfObjMem nvNode1)] at h4
  simpa [lcnfHeap, Std.ExtHashMap.sep_emp] using h4

private theorem nvMpzSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvMpz1]) nvMpzSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ nvMpz1Bytes) ⋆ Std.ExtHashMap.emp)
      nvMpzSlabMem := by
    rw [Std.ExtHashMap.sep_emp]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + nvMpz1Bytes.length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvMpzSlabMem h0
  rw [nvStr1Addr_eq] at h1
  have h2 := nvRtSt_inv h1
  have h3 := sep_mono_r (hdr3_bytes_to_cells nvStr1Addr mpzHeaderWord
    (1#64 ||| (1#64 <<< 32)) 7#64 Std.ExtHashMap.emp) h2
  have hm : ∀ mx, (cell64 nvStr1Addr mpzHeaderWord ⋆
      (cell64 (nvStr1Addr + 8#64) (1#64 ||| (1#64 <<< 32)) ⋆
        (cell64 (nvStr1Addr + 16#64) 7#64 ⋆ Std.ExtHashMap.emp))) mx →
      lcnfObjMem nvMpz1 mx := by
    intro mx hx
    have htag : nvMpz1.tag = mpzTag := rfl
    rw [r2b_lcnfObjMem_mpz_eq htag]
    have hmeta : nvMpz1.mpzMeta = (1#64 ||| (1#64 <<< 32)) := by decide
    have hhdr : nvMpz1.header = mpzHeaderWord := by decide
    rw [hhdr, hmeta, show nvMpz1.addr = nvStr1Addr from rfl,
      show nvMpz1.limbs = [7#64] from rfl, array64_cons, array64_nil, Std.ExtHashMap.sep_emp]
    rw [Std.ExtHashMap.sep_emp] at hx
    exact sep_cast hx (by simp only [Std.ExtHashMap.sep_assoc])
  have h4 := sep_mono_r hm h3
  simpa [lcnfHeap, Std.ExtHashMap.sep_emp] using h4

private theorem nvCloSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvClo0) nvCloSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ nvClo0Bytes) ⋆ Std.ExtHashMap.emp)
      nvCloSlabMem := by
    rw [Std.ExtHashMap.sep_emp]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + nvClo0Bytes.length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvCloSlabMem h0
  rw [nvStr1Addr_eq] at h1
  have h2 := nvRtSt_inv h1
  have h3 := sep_mono_r (hdr4_bytes_to_cells nvStr1Addr nvClo0.header nvClo0.funId
    nvClo0.cloMeta 1#64 Std.ExtHashMap.emp) h2
  refine sep_mono_r (fun mx hx => ?_) h3
  have hobj : lcnfObjMem nvClo0 =
      cell64 nvStr1Addr nvClo0.header ⋆ cell64 (nvStr1Addr + 8#64) nvClo0.funId ⋆
        cell64 (nvStr1Addr + 16#64) nvClo0.cloMeta ⋆ array64 (nvStr1Addr + 24#64) [1#64] ⋆
        region (nvStr1Addr + 32#64) 0 := rfl
  rw [hobj, array64_cons, array64_nil, region_zero, Std.ExtHashMap.sep_emp,
    Std.ExtHashMap.sep_emp]
  rw [Std.ExtHashMap.sep_emp] at hx
  exact sep_cast hx (by simp only [Std.ExtHashMap.sep_assoc])

private theorem nvBaSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvBa1] ⋆ bytes nvBa2Addr nvBa2Bytes)
      nvBaSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ (nvBa1Bytes ++ nvBa2Bytes)) ⋆
      Std.ExtHashMap.emp) nvBaSlabMem := by
    rw [Std.ExtHashMap.sep_emp, ← List.append_assoc]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + (nvBa1Bytes ++ nvBa2Bytes).length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len, List.length_append]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvBaSlabMem h0
  have hba1 : nvRtAddr + BitVec.ofNat 64 nvR2RtBytes.length = nvBa1Addr := by
    rw [nvR2RtBytes_len]; decide
  rw [hba1] at h1
  have h2 := nvRtSt_inv h1
  have h3 := sep_mono_r (sep_bytes_split Std.ExtHashMap.emp (by decide)) h2
  have h4 := sep_mono_r (baObjMem_of_bytes nvBa1Addr 8 [65, 66] _ (by decide) (by decide)) h3
  rw [Std.ExtHashMap.sep_emp] at h4
  have hba2 : nvBa1Addr + BitVec.ofNat 64 nvBa1Bytes.length = nvBa2Addr := by decide
  rw [hba2] at h4
  change (rtC0Inv nvRtAddr nvRtSt ⋆ (lcnfObjMem nvBa1 ⋆ bytes nvBa2Addr nvBa2Bytes))
    nvBaSlabMem at h4
  simpa [lcnfHeap, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using h4

private theorem nvArrSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvArr1] ⋆ bytes nvArr2Addr nvArr2Bytes)
      nvArrSlabMem := by
  have h0 : (bytes nvRtAddr (nvR2RtBytes ++ (nvArr1Bytes ++ nvArr2Bytes)) ⋆
      Std.ExtHashMap.emp) nvArrSlabMem := by
    rw [Std.ExtHashMap.sep_emp, ← List.append_assoc]; exact bytes_at_self nvRtAddr _
  have hfit0 : nvR2RtBytes.length + (nvArr1Bytes ++ nvArr2Bytes).length ≤ 2 ^ 64 := by
    rw [nvR2RtBytes_len, List.length_append]; decide
  have h1 := sep_bytes_split Std.ExtHashMap.emp hfit0 nvArrSlabMem h0
  have harr1 : nvRtAddr + BitVec.ofNat 64 nvR2RtBytes.length = nvArr1Addr := by
    rw [nvR2RtBytes_len]; decide
  rw [harr1] at h1
  have h2 := nvRtSt_inv h1
  have h3 := sep_mono_r (sep_bytes_split Std.ExtHashMap.emp (by decide)) h2
  have h4 := sep_mono_r (arrObjMem2_of_bytes nvArr1Addr 3#64 5#64 _) h3
  rw [Std.ExtHashMap.sep_emp] at h4
  have harr2 : nvArr1Addr + BitVec.ofNat 64 nvArr1Bytes.length = nvArr2Addr := by decide
  rw [harr2] at h4
  change (rtC0Inv nvRtAddr nvRtSt ⋆ (lcnfObjMem nvArr1 ⋆ bytes nvArr2Addr nvArr2Bytes))
    nvArrSlabMem at h4
  simpa [lcnfHeap, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using h4

private theorem nvStr1_canon : StrCanon nvStr1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

private theorem nvStr2_canon : StrCanon nvStr2 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

private theorem nvStr1_wf : nvStr1.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvStr1, mkStrObj, closureTag, arrayTag, sarrayTag, stringTag]

private theorem nvStr2_wf : nvStr2.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvStr2, mkStrObj, closureTag, arrayTag, sarrayTag, stringTag]

private theorem nvNode2_canon : ListConsCanon nvNode2 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, rfl⟩

private theorem nvNode1_canon : ListConsCanon nvNode1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, rfl⟩

private theorem nvNode2_wf : nvNode2.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvNode2, mkListConsObj, closureTag, arrayTag, sarrayTag, stringTag, mpzTag, listConsTag]

private theorem nvNode1_wf : nvNode1.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvNode1, mkListConsObj, closureTag, arrayTag, sarrayTag, stringTag, mpzTag, listConsTag]

private theorem nvBa1_canon : BaCanon nvBa1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvBa1_wf : nvBa1.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvBa1, mkBaObj, closureTag, arrayTag, sarrayTag]

private theorem nvArr1_canon : ArrCanon nvArr1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvArr1_wf : nvArr1.Wf := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  simp [nvArr1, mkArrObj, closureTag, arrayTag]

private theorem nvMpz1_canon : MpzCanon nvMpz1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide⟩

private theorem natToDecimalBytes_0 : natToDecimalBytes 0 = [48] := by
  simp [natToDecimalBytes]

private theorem natToDecimalBytes_7 : natToDecimalBytes 7 = [55] := by
  rw [natToDecimalBytes, ite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_left (by decide)]
  decide

private theorem natToDecimalBytes_42 : natToDecimalBytes 42 = [52, 50] := by
  rw [natToDecimalBytes, ite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_left (by decide)]
  decide

private theorem utf8DecodeFrom_65_66 : utf8DecodeFrom [65, 66] 0 = [boxNat 65, boxNat 66] := by
  rw [utf8DecodeFrom.eq_1, dite_eq_left (by decide),
    show 0 + utf8DecodeStepAt [65, 66] 0 = 1 from by decide,
    utf8DecodeFrom.eq_1, dite_eq_left (by decide),
    show 1 + utf8DecodeStepAt [65, 66] 1 = 2 from by decide,
    utf8DecodeFrom.eq_1, dite_eq_right (by decide)]
  decide

theorem nv_lcnf_char_op :
    Func.wp rtR2bEnv lcnf_char_op_body (nvRtAddr, 0#64, boxNat 0x03b1, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (r, _) m' => r = 0x03b1#64 ∧ m' = nvR2RtBytes.At nvRtAddr)
      (fun _ _ _ _ => False) ∧
    Func.wp rtR2bEnv lcnf_char_op_body (nvRtAddr, 1#64, 0x1f600#64, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (r, _) m' => r = boxNat 4 ∧ m' = nvR2RtBytes.At nvRtAddr)
      (fun _ _ _ _ => False) := by
  constructor
  · apply lcnf_char_op_sound
    rw [lcnfCharOpSpec, ite_eq_left (Or.inl rfl)]
    exact ⟨by decide, rfl⟩
  · apply lcnf_char_op_sound
    rw [lcnfCharOpSpec, ite_eq_left (Or.inr rfl)]
    exact ⟨by decide, rfl⟩

theorem nv_lcnf_str_alloc :
    Func.wp rtR2bEnv lcnf_str_alloc_body (nvRtAddr, 4#64, 3#64, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (p, _) m' => p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
        ∃ st', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          (rtC0Inv nvRtAddr st' ⋆ cell64 p strHeaderWord ⋆ cell64 (p + 8#64) 5#64 ⋆
            cell64 (p + 16#64) 5#64 ⋆ cell64 (p + 24#64) 3#64 ⋆
            region (p + 32#64) 4 ⋆ bytes (p + 36#64) [0] ⋆
            region (p + 37#64) (strAllocBytes 5 - 37)) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_str_alloc_sound
  rw [lcnfStrAllocSpec, ite_eq_right (by decide)]
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ Std.ExtHashMap.emp) (nvR2RtBytes.At nvRtAddr) := by
    rw [Std.ExtHashMap.sep_emp]; exact nvRtMem_inv
  refine ⟨nvRtSt, Std.ExtHashMap.emp, Or.inr (by decide), hm0,
    fun p st' m' hp0 hp8 hpr hrem _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hp0, hp8, st', hpr, hrem, by simpa [BitVec.add_assoc] using hm'⟩

theorem nv_lcnf_string_push :
    Func.wp rtR2bEnv lcnf_string_push_body (nvRtAddr, nvStr1Addr, 67#64, ())
      nvStrSlabMem
      (fun (r, _) m' => r = nvStr1Addr ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆
          lcnfObjMem (mkStrObj nvStr1Addr 1#32 8 [65, 66, 67] 3) ⋆
          lcnfObjMem nvStr2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_string_push_sound
  refine ⟨nvRtSt, nvStr1, lcnfObjMem nvStr2, rfl, nvStr1_canon,
    sep_cast nvStrSlabMem_split (by simp only [Std.ExtHashMap.sep_assoc]), ?_⟩
  have hcp : BitVec.toNat (67#64 &&& 4294967295#64) = 67 := by decide
  have hbs : strPayload nvStr1 ++ utf8EncodeBytes (BitVec.toNat (67#64 &&& 4294967295#64)) =
      [65, 66, 67] := by decide
  have hnMax :
      ¬ strMaxCap ≤
        (strPayload nvStr1 ++ utf8EncodeBytes (67#64 &&& 4294967295#64).toNat).length := by
    decide
  rw [ite_eq_right hnMax]
  have hin : nvStr1.rc = 1#32 ∧
      (strPayload nvStr1 ++ utf8EncodeBytes (67#64 &&& 4294967295#64).toNat).length + 1 ≤
        nvStr1.cap := by
    decide
  refine ⟨fun h => absurd hin h, fun r st' m' _ _ _ _ hin' hcan hm' => ?_⟩
  rcases hin' hin with ⟨rfl, rfl⟩
  rw [hbs] at hm'
  have hlen : (nvStr1.strLen + 1) % 2 ^ 64 = 3 := by decide
  have hkeep :
      (if nvStr1.rc = 1#32 then Std.ExtHashMap.emp
       else lcnfObjMem (nvStr1.withRc (decNonExclRc nvStr1.rc))) = Std.ExtHashMap.emp :=
    ite_eq_left (by decide)
  rw [ite_eq_left (show nvStr1.rc = 1#32 ∧
      ([65, 66, 67] : List UInt8).length + 1 ≤ nvStr1.cap from by decide),
    show nvStr1.cap = 8 from rfl, hlen, hkeep, Std.ExtHashMap.sep_emp] at hm'
  exact ⟨rfl, sep_cast hm' (by simp only [Std.ExtHashMap.sep_assoc])⟩

theorem nv_lcnf_string_append :
    Func.wp rtR2bEnv lcnf_string_append_body (nvRtAddr, nvStr1Addr, nvStr2Addr, ())
      nvStrSlabMem
      (fun (r, _) m' => r = nvStr1Addr ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆
          lcnfHeap [mkStrObj nvStr1Addr 1#32 8 [65, 66, 65, 67] 4, nvStr2]) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_string_append_sound
  refine ⟨nvRtSt, nvStr1, nvStr2, [nvStr1, nvStr2], Std.ExtHashMap.emp,
    by simp, rfl, nvStr1_canon, by simp, rfl, nvStr2_canon,
    fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> first | exact nvStr1_wf | exact nvStr2_wf,
    by
      rw [Std.ExtHashMap.sep_emp]
      simpa [lcnfHeap, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using nvStrSlabMem_split,
    ?_⟩
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  have hin :
      nvStr1.rc = 1#32 ∧ (strPayload nvStr1 ++ strPayload nvStr2).length + 1 ≤ nvStr1.cap := by
    decide
  refine ⟨fun h => absurd hin h, fun r st' objs' m' _ _ _ _ hin' _ hm' => ?_⟩
  rcases hin' hin with ⟨rfl, rfl, rfl⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  have hmmap : List.map (fun o => if o.addr = nvStr1Addr then
      mkStrObj nvStr1Addr 1#32 nvStr1.cap (strPayload nvStr1 ++ strPayload nvStr2)
        ((nvStr1.strLen + nvStr2.strLen) % 2 ^ 64) else o) [nvStr1, nvStr2] =
      [mkStrObj nvStr1Addr 1#32 8 [65, 66, 65, 67] 4, nvStr2] := by
    rw [List.map_cons, List.map_cons, List.map_nil, ite_eq_left (by decide),
      ite_eq_right (by decide)]
    have hp : strPayload nvStr1 ++ strPayload nvStr2 = [65, 66, 65, 67] := by decide
    have hl : (nvStr1.strLen + nvStr2.strLen) % 2 ^ 64 = 4 := by decide
    have hc : nvStr1.cap = 8 := rfl
    rw [hp, hl, hc]
  rw [hmmap] at hm'
  exact ⟨rfl, hm'⟩

theorem nv_lcnf_string_cmp_op :
    Func.wp rtR2bEnv lcnf_string_cmp_op_body (nvRtAddr, 1#64, nvStr1Addr, nvStr2Addr, ())
      nvStrSlabMem
      (fun (r, _) m' => r = 1#64 ∧ m' = nvStrSlabMem)
      (fun _ _ _ _ => False) := by
  apply lcnf_string_cmp_op_sound
  rw [lcnfStringCmpOpSpec, ite_eq_left (Or.inr (Or.inl rfl)), ite_eq_right (by decide)]
  refine ⟨nvStr1, nvStr2, rtC0Inv nvRtAddr nvRtSt, rfl, nvStr1_canon, rfl, nvStr2_canon,
    sep_cast nvStrSlabMem_split (by
      rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm (rtC0Inv nvRtAddr nvRtSt)]),
    ⟨by decide, rfl⟩⟩

theorem nv_lcnf_string_pos_op :
    Func.wp rtR2bEnv lcnf_string_pos_op_body
      (nvRtAddr, 0#64, nvStr1Addr, boxNat 1, 0#64, ()) nvStrSlabMem
      (fun (r, _) m' => r = 66#64 ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvStr1 ⋆ lcnfObjMem nvStr2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_string_pos_op_sound
  refine ⟨nvRtSt, nvStr1, [], lcnfObjMem nvStr2, rfl, nvStr1_canon,
    fun h => by exact absurd h.1 (by decide), fun o ho => by contradiction,
    by
      simpa [lcnfHeap, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using nvStrSlabMem_split,
    ?_⟩
  rw [ite_eq_left (Or.inl rfl)]
  intro objs' m' hm'
  dsimp only [objs'] at hm'
  rw [ite_eq_right (by decide)] at hm'
  simp only [lcnfHeap, Std.ExtHashMap.sep_emp] at hm'
  exact ⟨by decide, sep_cast hm' (by simp only [Std.ExtHashMap.sep_assoc])⟩

theorem nv_lcnf_string_to_list :
    Func.wp rtR2bEnv lcnf_string_to_list_body (nvRtAddr, nvStr1Addr, ())
      nvStrSlabMem
      (fun (res, _) m' => ∃ st' resObjs objs',
        st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
        ExclListMem res [boxNat 65, boxNat 66] resObjs ∧ DecObjRel nvStr1Addr [nvStr1] objs' ∧
        (rtC0Inv nvRtAddr st' ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs' ⋆ lcnfObjMem nvStr2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_string_to_list_sound
  have hcps : utf8DecodeFrom (strPayload nvStr1) 0 = [boxNat 65, boxNat 66] := by
    have hp : strPayload nvStr1 = [65, 66] := by decide
    rw [hp, utf8DecodeFrom_65_66]
  refine ⟨nvRtSt, nvStr1, [nvStr1], lcnfObjMem nvStr2, by simp, rfl, nvStr1_canon,
    fun o ho => by simp at ho; subst ho; exact nvStr1_wf,
    fun _ => ⟨by decide,
      fun o ho f hf => by
        simp at ho; subst ho; simp [LcnfObj.childFields, nvStr1, mkStrObj, stringTag] at hf,
      ⟨fun p hp hp0 => by simp at hp; subst hp; exact absurd hp0 (by decide),
       fun y hy _ => by
        simp at hy; subst hy
        simp [nonPersistRefs, LcnfObj.childFields, nvStr1, mkStrObj, stringTag, nvStr1Addr]⟩⟩,
    by rw [hcps]; decide,
    by simpa [lcnfHeap, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using nvStrSlabMem_split,
    fun res st' resObjs objs' m' hpr hrem hex hdec hm' => ?_⟩
  rw [hcps] at hex
  exact ⟨st', resObjs, objs', hpr, hrem, hex, hdec, hm'⟩

theorem nv_lcnf_string_mk :
    Func.wp rtR2bEnv lcnf_string_mk_body (nvRtAddr, nvNode1Addr, ())
      nvConsListSlabMem
      (fun (r, _) m' => r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
        ∃ st' objs', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          DecObjRel nvNode1Addr [nvNode1, nvNode2] objs' ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkStrObj r 1#32 3 [65, 66] 2) ⋆
            lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  apply lcnf_string_mk_sound
  have his : IsListInHeap [nvNode1, nvNode2] nvNode1Addr [boxNat 65, boxNat 66] :=
    IsListInHeap.cons (by simp) rfl nvNode1_canon rfl (by decide)
      (IsListInHeap.cons (by simp) rfl nvNode2_canon rfl (by decide) IsListInHeap.nil)
  have hwf : ∀ o ∈ [nvNode1, nvNode2], o.Wf := fun o ho => by
    simp at ho; rcases ho with rfl | rfl <;> first | exact nvNode1_wf | exact nvNode2_wf
  have hne : nvNode1Addr ≠ 1#64 → ∃ o ∈ [nvNode1, nvNode2], o.addr = nvNode1Addr ∧
      (o.rc = 1#32 → [nvNode1, nvNode2].length ≤ nvRtSt.workCap ∧
        lcnfHeapClosed [nvNode1, nvNode2] ∧ RcSound nvNode1Addr [nvNode1, nvNode2]) := by
    intro _
    refine ⟨nvNode1, by simp, rfl, fun _ => ⟨by decide, ?_, ?_⟩⟩
    · intro o ho f hf hf0
      simp at ho; rcases ho with rfl | rfl
      · simp [LcnfObj.childFields, nvNode1, mkListConsObj, listConsTag] at hf
        rcases hf with rfl | rfl
        · exact absurd hf0 (by decide)
        · exact ⟨nvNode2, by simp, rfl⟩
      · simp [LcnfObj.childFields, nvNode2, mkListConsObj, listConsTag] at hf
        rcases hf with rfl | rfl <;> exact absurd hf0 (by decide)
    · refine ⟨fun p hp hp0 => by
        simp at hp; rcases hp with rfl | rfl <;> exact absurd hp0 (by decide),
        fun y hy _ => by
          simp at hy; rcases hy with rfl | rfl
          · rw [show nonPersistRefs [nvNode1, nvNode2] nvNode1.addr = 0 from by decide]; decide
          · rw [show nonPersistRefs [nvNode1, nvNode2] nvNode2.addr = 1 from by decide]; decide⟩
  refine ⟨nvRtSt, [boxNat 65, boxNat 66], [nvNode1, nvNode2], Std.ExtHashMap.emp,
    his, hwf, hne, by rw [Std.ExtHashMap.sep_emp]; exact nvConsListSlabMem_split, ?_⟩
  rw [ite_eq_right (by decide)]
  refine ⟨Or.inr (by decide), fun r st' objs' m' hr0 hr8 hpr hrem hcan hdec hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  have hbs : utf8EncodeList [boxNat 65, boxNat 66] = [65, 66] := by decide
  rw [hbs] at hm'
  exact ⟨hr0, hr8, st', objs', hpr, hrem, hdec, hm'⟩

theorem nv_lcnf_ba_data :
    Func.wp rtR2bEnv lcnf_ba_data_body (nvRtAddr, nvBa1Addr, ())
      nvBaSlabMem
      (fun (arr, _) m' => arr ≠ 0#64 ∧ arr.toNat % 8 = 0 ∧
        ∃ st' objs', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          DecObjRel nvBa1Addr [nvBa1] objs' ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkArrObj arr 1#32 2 [boxNat 65, boxNat 66]) ⋆
            lcnfHeap objs' ⋆ bytes nvBa2Addr nvBa2Bytes) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_ba_data_sound
  refine ⟨nvRtSt, nvBa1, [nvBa1], bytes nvBa2Addr nvBa2Bytes, by simp, rfl, nvBa1_canon,
    fun o ho => by simp at ho; subst ho; exact nvBa1_wf,
    fun _ => ⟨by decide,
      fun o ho f hf => by
        simp at ho; subst ho; simp [LcnfObj.childFields, nvBa1, mkBaObj, sarrayTag] at hf,
      ⟨fun p hp hp0 => by simp at hp; subst hp; exact absurd hp0 (by decide),
       fun y hy _ => by
         simp at hy; subst hy
         simp [nonPersistRefs, LcnfObj.childFields, nvBa1, mkBaObj, sarrayTag]⟩⟩,
    nvBaSlabMem_split, ?_⟩
  rw [ite_eq_right (by decide)]
  refine ⟨Or.inr (by decide), fun arr st' objs' m' ha0 ha8 hpr hrem hcan hdec hm' => ?_⟩
  exact ⟨ha0, ha8, st', objs', hpr, hrem, hdec, by
    simpa [nvBa1, mkBaObj] using hm'⟩

theorem nv_lcnf_array_mk :
    Func.wp rtR2bEnv lcnf_array_mk_body (nvRtAddr, nvNode1Addr, ())
      nvConsListSlabMem
      (fun (arr, _) m' => arr ≠ 0#64 ∧ arr.toNat % 8 = 0 ∧
        ∃ st' objs', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          DecObjRel nvNode1Addr [nvNode1, nvNode2] objs' ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkArrObj arr 1#32 2 [boxNat 65, boxNat 66]) ⋆
            lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  apply lcnf_array_mk_sound
  have his : IsListInHeap [nvNode1, nvNode2] nvNode1Addr [boxNat 65, boxNat 66] :=
    IsListInHeap.cons (by simp) rfl nvNode1_canon rfl (by decide)
      (IsListInHeap.cons (by simp) rfl nvNode2_canon rfl (by decide) IsListInHeap.nil)
  have hwf : ∀ o ∈ [nvNode1, nvNode2], o.Wf := fun o ho => by
    simp at ho; rcases ho with rfl | rfl <;> first | exact nvNode1_wf | exact nvNode2_wf
  have hsc : ∀ v ∈ [boxNat 65, boxNat 66],
      v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ [nvNode1, nvNode2], o.addr = v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact Or.inr (Or.inl (by decide))
  refine ⟨nvRtSt, [boxNat 65, boxNat 66], [nvNode1, nvNode2], Std.ExtHashMap.emp,
    his, hwf, hsc, by rw [Std.ExtHashMap.sep_emp]; exact nvConsListSlabMem_split, ?_⟩
  rw [ite_eq_right (by decide)]
  have hinc : incElemsList [boxNat 65, boxNat 66] [nvNode1, nvNode2] = [nvNode1, nvNode2] := by
    simp [incElemsList.eq_2, incElemsList.eq_1, incObjList, boxNat]
  rw [hinc]
  refine ⟨fun _ => ⟨nvNode1, by simp, rfl, fun _ => ⟨by decide,
    fun o ho f hf hf0 => by
      simp at ho; rcases ho with rfl | rfl
      · simp [LcnfObj.childFields, nvNode1, mkListConsObj, listConsTag] at hf
        rcases hf with rfl | rfl
        · exact absurd hf0 (by decide)
        · exact ⟨nvNode2, by simp, rfl⟩
      · simp [LcnfObj.childFields, nvNode2, mkListConsObj, listConsTag] at hf
        rcases hf with rfl | rfl <;> exact absurd hf0 (by decide),
    ⟨fun p hp hp0 => by
       simp at hp; rcases hp with rfl | rfl <;> exact absurd hp0 (by decide),
     fun y hy _ => by
       simp at hy; rcases hy with rfl | rfl
       · rw [show nonPersistRefs [nvNode1, nvNode2] nvNode1.addr = 0 from by decide]; decide
       · rw [show nonPersistRefs [nvNode1, nvNode2] nvNode2.addr = 1 from by decide]; decide⟩⟩⟩,
    Or.inr (by decide), fun arr st' objs' m' ha0 ha8 hpr hrem hcan hdec hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨ha0, ha8, st', objs', hpr, hrem, hdec, hm'⟩

theorem nv_lcnf_array_to_list :
    Func.wp rtR2bEnv lcnf_array_to_list_body (nvRtAddr, nvArr1Addr, ())
      nvArrSlabMem
      (fun (res, _) m' => ∃ st' resObjs objs',
        st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
        ExclListMem res [3#64, 5#64] resObjs ∧ DecObjRel nvArr1Addr [nvArr1] objs' ∧
        (rtC0Inv nvRtAddr st' ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs' ⋆
          bytes nvArr2Addr nvArr2Bytes) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_array_to_list_sound
  have hinc : incElemsList nvArr1.fields.reverse [nvArr1] = [nvArr1] := by
    simp [incElemsList.eq_2, incElemsList.eq_1, incObjList, nvArr1, mkArrObj]
  refine ⟨nvRtSt, nvArr1, [nvArr1], bytes nvArr2Addr nvArr2Bytes, by simp, rfl, nvArr1_canon,
    fun o ho => by simp at ho; subst ho; exact nvArr1_wf,
    fun v hv => by
      simp [nvArr1, mkArrObj] at hv; rcases hv with rfl | rfl <;> exact Or.inr (Or.inl (by decide)),
    ?_, by decide, nvArrSlabMem_split, fun res st' resObjs objs' m' hpr hrem hex hdec hm' => ?_⟩
  · rw [hinc]
    refine ⟨nvArr1, by simp, rfl, fun _ => ⟨by decide,
      fun o ho f hf hf0 => by
        simp at ho; subst ho; simp [LcnfObj.childFields, nvArr1, mkArrObj] at hf
        rcases hf with rfl | rfl <;> exact absurd hf0 (by decide),
      ⟨fun p hp hp0 => by simp at hp; subst hp; exact absurd hp0 (by decide),
       fun y hy _ => by
         simp at hy; subst hy
         rw [show nonPersistRefs [nvArr1] nvArr1.addr = 0 from by decide]; decide⟩⟩⟩
  · rw [hinc] at hdec
    exact ⟨st', resObjs, objs', hpr, hrem, hex, hdec, hm'⟩

theorem nv_lcnf_array_replicate :
    Func.wp rtR2bEnv lcnf_array_replicate_body (nvRtAddr, boxNat 2, 7#64, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (arr, _) m' => arr ≠ 0#64 ∧ arr.toNat % 8 = 0 ∧
        ∃ st', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkArrObj arr 1#32 2 [7#64, 7#64])) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_array_replicate_sound
  rw [lcnfArrayReplicateSpec, ite_eq_right (by decide)]
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [] ⋆ Std.ExtHashMap.emp)
      (nvR2RtBytes.At nvRtAddr) := by
    simp only [lcnfHeap, Std.ExtHashMap.sep_emp]; exact nvRtMem_inv
  refine ⟨nvRtSt, [], Std.ExtHashMap.emp, Or.inr (by decide),
    fun o ho => by contradiction, fun h => by simp at h, fun h => by simp at h, hm0,
    fun arr st' objs' m' ha0 ha8 hpr hrem hcan _ _ hgt hm' => ?_⟩
  have h1gt : 1 < (boxNat 2 >>> 1).toNat := by decide
  have hobj := hgt h1gt
  rw [ite_eq_left (by decide)] at hobj
  subst hobj
  simp only [lcnfHeap, Std.ExtHashMap.sep_emp, show (boxNat 2 >>> 1).toNat = 2 from by decide,
    List.replicate] at hm'
  exact ⟨ha0, ha8, st', hpr, hrem, hm'⟩

theorem nv_lcnf_nat_to_str_zero :
    Func.wp rtR2bEnv lcnf_nat_to_str_body (nvRtAddr, 1#64, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (s, _) m' => s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
        ∃ st', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkStrObj s 1#32 2 [48] 1)) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_nat_to_str_sound
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [] ⋆ Std.ExtHashMap.emp)
      (nvR2RtBytes.At nvRtAddr) := by
    simp only [lcnfHeap, Std.ExtHashMap.sep_emp]; exact nvRtMem_inv
  refine ⟨nvRtSt, 0, [], Std.ExtHashMap.emp, by simp [NatInHeap],
    fun _ h => by contradiction, hm0, ?_⟩
  rw [ite_eq_left (by decide), natToDecimalBytes_0]
  refine ⟨Or.inr (by decide), fun s st' m' hs0 hs8 hpr hrem hcan hm' => ?_⟩
  simp only [lcnfHeap, Std.ExtHashMap.sep_emp, List.length_singleton] at hm'
  exact ⟨hs0, hs8, st', hpr, hrem, hm'⟩

theorem nv_lcnf_nat_to_str_boxed :
    Func.wp rtR2bEnv lcnf_nat_to_str_body (nvRtAddr, boxNat 42, ())
      (nvR2RtBytes.At nvRtAddr)
      (fun (s, _) m' => s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
        ∃ st', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2)) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_nat_to_str_sound
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [] ⋆ Std.ExtHashMap.emp)
      (nvR2RtBytes.At nvRtAddr) := by
    simp only [lcnfHeap, Std.ExtHashMap.sep_emp]; exact nvRtMem_inv
  refine ⟨nvRtSt, 42, [], Std.ExtHashMap.emp, by simp [NatInHeap]; decide,
    fun _ h => by contradiction, hm0, ?_⟩
  rw [ite_eq_left (by decide), natToDecimalBytes_42]
  refine ⟨Or.inr (by decide), fun s st' m' hs0 hs8 hpr hrem hcan hm' => ?_⟩
  simp only [lcnfHeap, Std.ExtHashMap.sep_emp, List.length_cons, List.length_nil] at hm'
  exact ⟨hs0, hs8, st', hpr, hrem, hm'⟩

theorem nv_lcnf_nat_to_str_mpz :
    Func.wp rtR2bEnv lcnf_nat_to_str_body (nvRtAddr, nvStr1Addr, ())
      nvMpzSlabMem
      (fun (s, _) m' => s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
        ∃ st' objs', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          DecObjRel nvStr1Addr [nvMpz1] objs' ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkStrObj s 1#32 2 [55] 1) ⋆
            lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  apply lcnf_nat_to_str_sound
  have hwf : nvMpz1.Wf := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, ?_⟩
    simp [nvMpz1, closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvMpz1] ⋆ Std.ExtHashMap.emp) nvMpzSlabMem := by
    rw [Std.ExtHashMap.sep_emp]; exact nvMpzSlabMem_split
  refine ⟨nvRtSt, 7, [nvMpz1], Std.ExtHashMap.emp,
    by rw [NatInHeap, ite_eq_right (by decide)]
       exact ⟨nvMpz1, by simp, rfl, nvMpz1_canon, by decide⟩,
    fun o ho => by simp at ho; subst ho; exact hwf, hm0, ?_⟩
  rw [ite_eq_right (by decide)]
  refine ⟨nvMpz1, by simp, rfl, nvMpz1_canon,
    fun _ => ⟨by decide,
      fun o ho f hf => by simp at ho; subst ho; simp [LcnfObj.childFields, nvMpz1, mpzTag] at hf,
      ⟨fun p hp hp0 => by simp at hp; subst hp; exact absurd hp0 (by decide),
       fun y hy _ => by
         simp at hy; subst hy
         rw [show nonPersistRefs [nvMpz1] nvMpz1.addr = 0 from by decide]; decide⟩⟩,
    ?_⟩
  rw [ite_eq_right (by decide), ite_eq_right (by decide), natToDecimalBytes_7]
  refine ⟨by decide, fun s st' objs' m' hs0 hs8 hpr hrem hcan hdec hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  simp only [List.length_singleton] at hm'
  exact ⟨hs0, hs8, st', objs', hpr, hrem, hdec, hm'⟩

theorem nv_lcnf_clo_under :
    Func.wp rtC0Env lcnf_clo_under.body (nvRtAddr, nvStr1Addr, 1#64, ())
      nvCloSlabMem
      (fun (c, _) m' => c ≠ 0#64 ∧ c.toNat % 8 = 0 ∧
        ∃ st', st'.PreservesMeta nvRtSt ∧ st'.rem ≤ nvRtSt.rem ∧
          (rtC0Inv nvRtAddr st' ⋆
            cell64 c (1#64 ||| BitVec.ofNat 64 40 <<< 32 |||
              BitVec.ofNat 64 closureTag <<< 56) ⋆
            cell64 (c + 8#64) 1024#64 ⋆
            cell64 (c + 16#64) (cloMetaWord 2 2) ⋆
            array64 (c + 24#64) [1#64] ⋆
            region (c + 32#64) 8) m')
      (fun _ _ _ _ => False) := by
  apply rtC0Env_clo_under_wp
  have hwf : nvClo0.Wf := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, ?_⟩
    simp [nvClo0, closureTag]
  have hm0 : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvClo0 ⋆ lcnfHeap [] ⋆ Std.ExtHashMap.emp)
      nvCloSlabMem := by
    simp only [lcnfHeap, Std.ExtHashMap.sep_emp]; exact nvCloSlabMem_split
  refine ⟨nvRtSt, nvClo0, [], Std.ExtHashMap.emp, rfl, rfl, hwf,
    fun o ho => by contradiction, fun o ho => by contradiction,
    fun p hp hp0 => by simp [nvClo0] at hp; subst hp; exact absurd hp0 (by decide),
    fun o ho => by contradiction,
    by decide, by decide, by decide, by decide, by decide, Or.inr (by decide), hm0,
    fun c st' objs' m' hc0 hc8 hpr hrem hrel hm' => ?_⟩
  rw [ite_eq_left (by decide)] at hrel
  subst hrel
  simp only [lcnfHeap, Std.ExtHashMap.sep_emp, show nvClo0.rc = 1#32 from rfl, ↓reduceIte,
    Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hc0, hc8, st', hpr, hrem, by simpa [nvClo0, cloMetaWord] using hm'⟩

end LeanQbe.T.LeanLCNF
