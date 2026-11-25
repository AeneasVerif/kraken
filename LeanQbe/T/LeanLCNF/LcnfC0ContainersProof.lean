module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof3

/-!
# Top-Level `ModuleOk` & Non-Vacuity Proofs for `LeanLCNF` C0 Containers (`Milestone R2 Part 1`)

Composes the decomposed `Func.wp` proofs from:
- `LcnfC0ContainersProof1`: RC/bounds/slice helpers + `r2_inc_obj`, `r2_dec_obj`,
  `r2_mem_copy_bytes`, `r2_cmp_byte_slices`, `lcnf_oob`
- `LcnfC0ContainersProof2`: `ByteArray` (`tag = 248`, `m_other = 1`) primitives + COW proofs
- `LcnfC0ContainersProof3`: `Array` (`tag = 246`) primitives + COW/recursive-RC proofs

Delivers:
1. `rtR2Mod_tableImpl : TableImpl rtR2Env rtR2Mod.fns rtR2SpecEntries`
2. `rtR2Mod_moduleOk : ModuleOk rtR2Env rtR2Mod` (pure `std3` axioms, acyclic C0)
3. Public `*_sound` theorems for all 14 R2 primitives (`lcnf_ba_*`, `lcnf_array_*`, `lcnf_oob`)
4. Concrete `Mem 64` non-vacuity (`XPost := (fun _ _ _ _ => False)`) proofs over a concrete
   `RtC0State` slab (`nvRtSt`) exercising `lcnf_ba_empty`, exclusive vs shared `ByteArray`
   (`push`/`set`/`get`/`cmp_op`), and exclusive vs shared `Array`
   (`push`/`set`/`pop`/`swap`/`get`/`lcnf_oob`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

/-! ## 1. Whole-Module `TableImpl` and `ModuleOk` -/

private theorem allFns_of_mem {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
      ⟨h _ List.mem_cons_self, allFns_of_mem (fun _ hm => h _ (List.mem_cons_of_mem _ hm))⟩

/-- All 22 functions in `rtR2Mod` conform to `rtR2SpecEntries` under `rtR2Env`. -/
theorem rtR2Mod_tableImpl : TableImpl rtR2Env rtR2Mod.fns rtR2SpecEntries := by
  dsimp only [rtR2Mod, rtR2_fns, rtR2SpecEntries]
  refine ⟨⟨⟨rfl, rfl, rfl⟩, r2_inc_obj_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_dec_obj_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_mem_copy_bytes_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_cmp_byte_slices_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_oob_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_alloc_sarray_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_ensure_excl_ba_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_empty_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_mk_empty_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_mk_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_get_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_set_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_push_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_ba_cmp_op_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_alloc_array_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, r2_ensure_excl_array_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_mk_empty_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_get_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_set_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_push_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_pop_wp⟩,
    ⟨⟨⟨rfl, rfl, rfl⟩, lcnf_array_swap_wp⟩, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- All 22 functions in `rtR2Mod` satisfy `Fn.Wf`. -/
theorem rtR2Mod_allFns_wf : AllFns Fn.Wf rtR2Mod.fns :=
  allFns_of_mem rtR2_fns_wf

/-- Top-level acyclic C0 module correctness proof for `rtR2Mod` under `rtR2Env`. -/
theorem rtR2Mod_moduleOk : ModuleOk rtR2Env rtR2Mod :=
  Env.ofTable_moduleOk rtR2_checkAcyclic rtR2Mod_allFns_wf rtR2Mod_tableImpl

/-- Lookup-indexed `ModuleOk` WP corollary for every function in `rtR2Mod`. -/
theorem rtR2Mod_fn_sound {fn : Fn} (hfn : fn ∈ rtR2Mod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : rtR2Env fn.name fn.as fn.rs xs m Q X) :
    Func.wp rtR2Env fn.body xs m Q X :=
  Env.ofTable_sound (List.nodup_append.mp rtR2Mod_moduleOk.nodup).1
    rtR2Mod_tableImpl fn hfn xs m Q X hpre

/-! ## 2. Public R2 Target Soundness Theorems -/

theorem lcnf_oob_sound :
    ∀ xs m Q X, lcnfOobSpec xs m Q X → Func.wp rtR2Env lcnf_oob_body xs m Q X :=
  lcnf_oob_wp

theorem lcnf_ba_empty_sound :
    ∀ xs m Q X, lcnfBaEmptySpec xs m Q X → Func.wp rtR2Env lcnf_ba_empty_body xs m Q X :=
  lcnf_ba_empty_wp

theorem lcnf_ba_mk_empty_sound :
    ∀ xs m Q X, lcnfBaMkEmptySpec xs m Q X → Func.wp rtR2Env lcnf_ba_mk_empty_body xs m Q X :=
  lcnf_ba_mk_empty_wp

theorem lcnf_ba_mk_sound :
    ∀ xs m Q X, lcnfBaMkSpec xs m Q X → Func.wp rtR2Env lcnf_ba_mk_body xs m Q X :=
  lcnf_ba_mk_wp

theorem lcnf_ba_get_sound :
    ∀ xs m Q X, lcnfBaGetSpec xs m Q X → Func.wp rtR2Env lcnf_ba_get_body xs m Q X :=
  lcnf_ba_get_wp

theorem lcnf_ba_set_sound :
    ∀ xs m Q X, lcnfBaSetSpec xs m Q X → Func.wp rtR2Env lcnf_ba_set_body xs m Q X :=
  lcnf_ba_set_wp

theorem lcnf_ba_push_sound :
    ∀ xs m Q X, lcnfBaPushSpec xs m Q X → Func.wp rtR2Env lcnf_ba_push_body xs m Q X :=
  lcnf_ba_push_wp

theorem lcnf_ba_cmp_op_sound :
    ∀ xs m Q X, lcnfBaCmpOpSpec xs m Q X → Func.wp rtR2Env lcnf_ba_cmp_op_body xs m Q X :=
  lcnf_ba_cmp_op_wp

theorem lcnf_array_mk_empty_sound :
    ∀ xs m Q X, lcnfArrayMkEmptySpec xs m Q X →
      Func.wp rtR2Env lcnf_array_mk_empty_body xs m Q X :=
  lcnf_array_mk_empty_wp

theorem lcnf_array_get_sound :
    ∀ xs m Q X, lcnfArrayGetSpec xs m Q X → Func.wp rtR2Env lcnf_array_get_body xs m Q X :=
  lcnf_array_get_wp

theorem lcnf_array_set_sound :
    ∀ xs m Q X, lcnfArraySetSpec xs m Q X → Func.wp rtR2Env lcnf_array_set_body xs m Q X :=
  lcnf_array_set_wp

theorem lcnf_array_push_sound :
    ∀ xs m Q X, lcnfArrayPushSpec xs m Q X → Func.wp rtR2Env lcnf_array_push_body xs m Q X :=
  lcnf_array_push_wp

theorem lcnf_array_pop_sound :
    ∀ xs m Q X, lcnfArrayPopSpec xs m Q X → Func.wp rtR2Env lcnf_array_pop_body xs m Q X :=
  lcnf_array_pop_wp

theorem lcnf_array_swap_sound :
    ∀ xs m Q X, lcnfArraySwapSpec xs m Q X → Func.wp rtR2Env lcnf_array_swap_body xs m Q X :=
  lcnf_array_swap_wp

/-! ## 3. Symbolic Slab & Byte-Serialization Builders for Concrete `Mem 64` Non-Vacuity -/

/-- Serialize a list of 64-bit words in little-endian byte order matching `cell64`. -/
def u64ListBytes : List (BitVec 64) → List UInt8
  | [] => []
  | v :: vs => Int.toBytes 8 v.toInt ++ u64ListBytes vs

private theorem u64ListBytes_length (vs : List (BitVec 64)) :
    (u64ListBytes vs).length = 8 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [u64ListBytes, List.length_append, Int.toBytes_length, ih, List.length_cons]
    omega

private theorem replicate_append_eq {α : Type} (x : α) (a b : Nat) :
    List.replicate a x ++ List.replicate b x = List.replicate (a + b) x := by
  induction a with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, ih, Nat.succ_add, List.replicate_succ]

private theorem array64_eq_bytes (a : BitVec 64) :
    ∀ (vs : List (BitVec 64)), 8 * vs.length ≤ 2 ^ 64 →
      array64 a vs = bytes a (u64ListBytes vs)
  | [], _ => by
    rw [array64_nil, u64ListBytes]
    exact eq_nil_At a
  | v :: vs, hle => by
    rw [array64_cons, u64ListBytes, bytes_append]
    · have ih := array64_eq_bytes (a + 8) vs (by simp only [List.length_cons] at hle; omega)
      rw [ih]; simp [Int.toBytes_length]; rfl
    · simp only [Int.toBytes_length, u64ListBytes_length]
      simp only [List.length_cons] at hle; omega

private theorem zero_u64ListBytes (n : Nat) :
    u64ListBytes (List.replicate n 0#64) = List.replicate (8 * n) 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hz : Int.toBytes 8 (0#64 : BitVec 64).toInt = List.replicate 8 0 := by decide
    rw [List.replicate_succ, u64ListBytes, ih, hz, replicate_append_eq,
      Nat.mul_succ, Nat.add_comm 8 (8 * k)]

private theorem array64_replicate_zero (a : BitVec 64) {n : Nat} (hle : 8 * n ≤ 2 ^ 64) :
    array64 a (List.replicate n 0#64) = bytes a (List.replicate (8 * n) 0) := by
  rw [array64_eq_bytes a (List.replicate n 0#64) (by simpa using hle), zero_u64ListBytes]

private theorem sep_bytes_split {a : BitVec 64} {xs ys : List UInt8} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : xs.length + ys.length ≤ 2 ^ 64)
    (h : (bytes a (xs ++ ys) ⋆ R) m) :
    (bytes a xs ⋆ (bytes (a + BitVec.ofNat 64 xs.length) ys ⋆ R)) m := by
  rw [bytes_append a xs ys hlen] at h
  exact sep_cast h (by ac_rfl)

private theorem sep_bytes_to_region {a : BitVec 64} {n : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes a (List.replicate n 0) ⋆ R) m) :
    (region a n ⋆ R) m := by
  have hr := sep_mono (fun _ hf => LeanQbe.T.bytes_to_region hf) hm
  simpa only [List.length_replicate] using hr

private theorem nvSmallPools_emp :
    smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) rtNumClasses =
      Std.ExtHashMap.emp := by
  suffices h : ∀ k, k ≤ rtNumClasses →
      smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) k = Std.ExtHashMap.emp from
    h _ (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => rfl
  | succ n ih =>
    change smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) n ⋆
        smallPoolSlot n ((List.replicate rtNumClasses 0#64).getD n 0#64) [] =
      Std.ExtHashMap.emp
    have hhd : (List.replicate rtNumClasses 0#64).getD n 0#64 = 0#64 := by
      simp only [List.getD, List.getElem?_replicate]
      split <;> rfl
    have hslot : smallPoolSlot n ((List.replicate rtNumClasses 0#64).getD n 0#64) [] =
        Std.ExtHashMap.emp := by
      rw [hhd]; funext m; simp only [smallPoolSlot]
      split
      · simp [smallFreeList]
      · simp
    rw [ih (Nat.le_of_lt hk), hslot, Std.ExtHashMap.sep_emp]

private theorem nvLargeFree_emp : largeFreeList 0#64 [] = Std.ExtHashMap.emp := by
  funext m; simp [largeFreeList, largeSeg]

/-- Concrete base address of the `RtC0State` header struct (`65536`, 8-byte aligned). -/
def nvRtAddr : BitVec 64 := 0x10000#64

/-- Concrete 512-byte bump arena capacity for non-vacuity proofs. -/
def nvArenaCap : Nat := 512

/-- Concrete `LcnfC0Rt` header: zeroed pools/stats, `512B` bump arena, `4`-slot worklist. -/
def nvHdr : LcnfC0Rt :=
  { s_large_free := 0#64
    s_ba_empty := 0#64
    s_cur := nvRtAddr + 33672#64
    s_end := nvRtAddr + 33672#64 + 512#64
    s_work := nvRtAddr + 33672#64 + 512#64
    s_work_cap := 4#64
    s_chunks := 0#64
    s_nchunks := 0#64
    s_chunks_cap := 0#64
    s_st_allocs := 0#64
    s_st_frees := 0#64
    s_st_live := 0#64
    s_st_peak_live := 0#64
    s_st_persistent := 0#64
    s_st_reused := 0#64
    s_st_cold_decs := 0#64
    s_st_bytes := 0#64 }

/-- Concrete initial `RtC0State` used across non-vacuity theorems. -/
def nvRtSt : RtC0State :=
  { extraArgs := List.replicate rtExtraSlots 0#64
    globals := List.replicate rtGlobalSlots 0#64
    freeList := List.replicate rtNumClasses 0#64
    hdr := nvHdr
    workBuf := List.replicate 4 0#64
    smallPools := fun _ => []
    largeNodes := []
    extraLen := List.length_replicate
    globalsLen := List.length_replicate
    freeListLen := List.length_replicate
    workLen := by decide
    curLeEnd := by decide
    arenaAlign := by decide
    curNz := by decide }

/-- Serialized 17 header words (`136` bytes) of `nvHdr`. -/
def nvHdrWords : List (BitVec 64) :=
  [nvHdr.s_large_free, nvHdr.s_ba_empty, nvHdr.s_cur, nvHdr.s_end, nvHdr.s_work,
   nvHdr.s_work_cap, nvHdr.s_chunks, nvHdr.s_nchunks, nvHdr.s_chunks_cap,
   nvHdr.s_st_allocs, nvHdr.s_st_frees, nvHdr.s_st_live, nvHdr.s_st_peak_live,
   nvHdr.s_st_persistent, nvHdr.s_st_reused, nvHdr.s_st_cold_decs, nvHdr.s_st_bytes]

/-- Concrete byte image (`34216` bytes) of `nvRtSt` starting at `nvRtAddr`. -/
def nvRtBytes : List UInt8 :=
  List.replicate 256 0 ++ List.replicate 32768 0 ++ List.replicate 512 0 ++
    u64ListBytes nvHdrWords ++ List.replicate nvArenaCap 0 ++ List.replicate 32 0

private theorem nvHdrWords_len : (u64ListBytes nvHdrWords).length = 136 := by
  rw [u64ListBytes_length]; decide

private theorem nvRtBytes_length : nvRtBytes.length = 34216 := by
  dsimp only [nvRtBytes]
  simp only [List.length_append, List.length_replicate, nvHdrWords_len, nvArenaCap]

private theorem nvHdr_eq_bytes :
    bytes (nvRtAddr + 33536#64) (u64ListBytes nvHdrWords) = LcnfC0Rt.At nvRtAddr nvHdr := by
  rw [← array64_eq_bytes (nvRtAddr + 33536#64) nvHdrWords (by decide)]
  simp only [nvHdrWords, LcnfC0Rt.At, array64_cons, array64_nil, Std.ExtHashMap.sep_emp]
  have h0 : nvRtAddr + 33536#64 = nvRtAddr + 33536 := rfl
  simp only [h0,
    show (nvRtAddr + 33536) + 8 = nvRtAddr + 33544 by decide,
    show (nvRtAddr + 33544) + 8 = nvRtAddr + 33552 by decide,
    show (nvRtAddr + 33552) + 8 = nvRtAddr + 33560 by decide,
    show (nvRtAddr + 33560) + 8 = nvRtAddr + 33568 by decide,
    show (nvRtAddr + 33568) + 8 = nvRtAddr + 33576 by decide,
    show (nvRtAddr + 33576) + 8 = nvRtAddr + 33584 by decide,
    show (nvRtAddr + 33584) + 8 = nvRtAddr + 33592 by decide,
    show (nvRtAddr + 33592) + 8 = nvRtAddr + 33600 by decide,
    show (nvRtAddr + 33600) + 8 = nvRtAddr + 33608 by decide,
    show (nvRtAddr + 33608) + 8 = nvRtAddr + 33616 by decide,
    show (nvRtAddr + 33616) + 8 = nvRtAddr + 33624 by decide,
    show (nvRtAddr + 33624) + 8 = nvRtAddr + 33632 by decide,
    show (nvRtAddr + 33632) + 8 = nvRtAddr + 33640 by decide,
    show (nvRtAddr + 33640) + 8 = nvRtAddr + 33648 by decide,
    show (nvRtAddr + 33648) + 8 = nvRtAddr + 33656 by decide,
    show (nvRtAddr + 33656) + 8 = nvRtAddr + 33664 by decide]
  have hc : ∀ (a : BitVec 64) (v : BitVec 64), cell64 a v = cell (t := i64) a v :=
    fun _ _ => rfl
  simp only [hc]
  ac_rfl

/-- Splitting `nvRtBytes` establishes `rtC0Inv nvRtAddr nvRtSt` symbolically. -/
theorem nvRtSt_inv {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes nvRtAddr nvRtBytes ⋆ R) m) :
    (rtC0Inv nvRtAddr nvRtSt ⋆ R) m := by
  have hm0 : (bytes nvRtAddr (List.replicate 256 0 ++
      (List.replicate 32768 0 ++ (List.replicate 512 0 ++
      (u64ListBytes nvHdrWords ++ (List.replicate nvArenaCap 0 ++
        List.replicate 32 0))))) ⋆ R) m := by
    simpa only [nvRtBytes, List.append_assoc] using hm
  have h1 := sep_bytes_split (by
    simp only [List.length_append, List.length_replicate, nvHdrWords_len, nvArenaCap]; omega) hm0
  simp only [List.length_replicate] at h1
  rw [show nvRtAddr + 256#64 = nvRtAddr + BitVec.ofNat 64 rtGlobalsOff from rfl] at h1
  have h1' : (bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff)
        (List.replicate 32768 0 ++ (List.replicate 512 0 ++
          (u64ListBytes nvHdrWords ++ (List.replicate nvArenaCap 0 ++ List.replicate 32 0)))) ⋆
      (bytes nvRtAddr (List.replicate 256 0) ⋆ R)) m := sep_cast h1 (by ac_rfl)
  have h2 := sep_bytes_split (by
    simp only [List.length_append, List.length_replicate, nvHdrWords_len, nvArenaCap]; omega) h1'
  simp only [List.length_replicate,
    show (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) + 32768#64 = nvRtAddr + 33024#64 by decide]
    at h2
  have h2' : (bytes (nvRtAddr + 33024#64)
        (List.replicate 512 0 ++ (u64ListBytes nvHdrWords ++
          (List.replicate nvArenaCap 0 ++ List.replicate 32 0))) ⋆
      (bytes nvRtAddr (List.replicate 256 0) ⋆
        bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate 32768 0) ⋆ R)) m :=
    sep_cast h2 (by ac_rfl)
  have h3 := sep_bytes_split (by
    simp only [List.length_append, List.length_replicate, nvHdrWords_len, nvArenaCap]; omega) h2'
  simp only [List.length_replicate,
    show (nvRtAddr + 33024#64) + 512#64 = nvRtAddr + 33536#64 by decide] at h3
  have h3' : (bytes (nvRtAddr + 33536#64)
        (u64ListBytes nvHdrWords ++ (List.replicate nvArenaCap 0 ++ List.replicate 32 0)) ⋆
      (bytes nvRtAddr (List.replicate 256 0) ⋆
        bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate 32768 0) ⋆
        bytes (nvRtAddr + 33024#64) (List.replicate 512 0) ⋆ R)) m :=
    sep_cast h3 (by ac_rfl)
  have h4 := sep_bytes_split (by
    simp only [List.length_append, List.length_replicate, nvHdrWords_len, nvArenaCap]; omega) h3'
  rw [nvHdrWords_len, show (nvRtAddr + 33536#64) + 136#64 = nvRtAddr + 33672#64 by decide] at h4
  have h4' : (bytes (nvRtAddr + 33672#64) (List.replicate nvArenaCap 0 ++ List.replicate 32 0) ⋆
      (bytes nvRtAddr (List.replicate 256 0) ⋆
        bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate 32768 0) ⋆
        bytes (nvRtAddr + 33024#64) (List.replicate 512 0) ⋆
        bytes (nvRtAddr + 33536#64) (u64ListBytes nvHdrWords) ⋆ R)) m :=
    sep_cast h4 (by ac_rfl)
  have h5 := sep_bytes_split (by
    simp only [List.length_replicate, nvArenaCap]; omega) h4'
  simp only [List.length_replicate, nvArenaCap,
    show (nvRtAddr + 33672#64) + 512#64 = nvHdr.s_work by rfl] at h5
  rw [show nvRtAddr + 33672#64 = nvHdr.s_cur from rfl] at h5
  have h5' : (bytes nvHdr.s_cur (List.replicate 512 0) ⋆
      (bytes nvRtAddr (List.replicate 256 0) ⋆
        bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate 32768 0) ⋆
        bytes (nvRtAddr + 33024#64) (List.replicate 512 0) ⋆
        bytes (nvRtAddr + 33536#64) (u64ListBytes nvHdrWords) ⋆
        bytes nvHdr.s_work (List.replicate 32 0) ⋆ R)) m := sep_cast h5 (by ac_rfl)
  have hmReg := sep_bytes_to_region h5'
  have hremEq : nvRtSt.rem = 512 := by decide
  rw [← hremEq] at hmReg
  have hmReassoc : (bytes nvRtAddr (List.replicate 256 0) ⋆
      bytes (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate 32768 0) ⋆
      bytes (nvRtAddr + 33024#64) (List.replicate 512 0) ⋆
      bytes (nvRtAddr + 33536#64) (u64ListBytes nvHdrWords) ⋆
      bytes nvHdr.s_work (List.replicate 32 0) ⋆
      region nvHdr.s_cur nvRtSt.rem ⋆ R) m :=
    sep_cast hmReg (by ac_rfl)
  rw [← show 8 * rtExtraSlots = 256 by decide,
    ← show 8 * rtGlobalSlots = 32768 by decide,
    ← show 8 * rtNumClasses = 512 by decide,
    ← show 8 * 4 = 32 by rfl,
    ← array64_replicate_zero nvRtAddr (by decide),
    ← array64_replicate_zero (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (by decide),
    ← array64_replicate_zero (nvRtAddr + 33024#64) (by decide),
    ← array64_replicate_zero nvHdr.s_work (by decide),
    nvHdr_eq_bytes] at hmReassoc
  dsimp only [rtC0Inv, nvRtSt, nvHdr]
  change (array64 nvRtAddr (List.replicate rtExtraSlots 0#64) ⋆
      array64 (nvRtAddr + BitVec.ofNat 64 rtGlobalsOff) (List.replicate rtGlobalSlots 0#64) ⋆
      array64 (nvRtAddr + 33024#64) (List.replicate rtNumClasses 0#64) ⋆
      LcnfC0Rt.At nvRtAddr nvHdr ⋆
      array64 nvHdr.s_work (List.replicate 4 0#64) ⋆
      smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) rtNumClasses ⋆
      largeFreeList 0#64 [] ⋆
      region nvHdr.s_cur nvRtSt.rem ⋆ R) m
  rw [nvSmallPools_emp, nvLargeFree_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_emp]
  exact sep_cast hmReassoc (by ac_rfl)

private theorem baObjMem_of_bytes {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon o)
    (hc : (bytes o.addr (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap]
        ++ o.scalarData ++ List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0) ⋆ R)
      m) :
    (lcnfObjMem o ⋆ R) m := by
  have hlen1 : (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize,
      BitVec.ofNat 64 o.cap]).length = 24 := by
    rw [u64ListBytes_length]; rfl
  have htag := hcanon.2.2.2.2.2.1
  have hlenS := hcanon.2.2.2.2.2.2.1
  have hars := hcanon.2.2.2.2.2.2.2.1
  have hmaxC : o.cap ≤ baMaxCap := hcanon.2.2.2.2.2.2.2.2
  have hoth := hcanon.2.2.2.2.1
  have htot : o.totalBytes = align8 (24 + o.cap) := by
    dsimp only [LcnfObj.totalBytes]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [htag]; decide)),
      ite_eq_left_of_eq_true _ _ (eq_true htag), hoth]
    have h1m : (1 : Nat) % 128 = 1 := rfl
    rw [h1m, Nat.one_mul]
  have hge : 24 + o.scalarData.length ≤ o.totalBytes := by
    rw [htot, ← hlenS]; unfold align8; omega
  have hlenT : 24 + (o.scalarData.length + (o.totalBytes - (24 + o.scalarData.length))) ≤ 2 ^ 64 :=
    by rw [htot]; unfold align8 baMaxCap at *; omega
  have hc' : (bytes o.addr (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize,
      BitVec.ofNat 64 o.cap] ++ (o.scalarData ++
        List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0)) ⋆ R) m := by
    simpa only [List.append_assoc] using hc
  have h1 := sep_bytes_split (by
    rw [hlen1, List.length_append, List.length_replicate]; exact hlenT) hc'
  rw [hlen1] at h1
  have h1' : (bytes (o.addr + 24#64)
        (o.scalarData ++ List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0) ⋆
      (bytes o.addr (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize,
        BitVec.ofNat 64 o.cap]) ⋆ R)) m := sep_cast h1 (by ac_rfl)
  have h2 := sep_bytes_split (by
    rw [List.length_replicate]; omega) h1'
  have h2' : (bytes ((o.addr + 24#64) + BitVec.ofNat 64 o.scalarData.length)
        (List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0) ⋆
      (bytes o.addr (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap]) ⋆
        bytes (o.addr + 24#64) o.scalarData ⋆ R)) m := sep_cast h2 (by ac_rfl)
  have hreg := sep_bytes_to_region h2'
  have hadd : (o.addr + 24#64) + BitVec.ofNat 64 o.scalarData.length =
      o.addr + BitVec.ofNat 64 (24 + o.scalarData.length) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    have hltS : o.scalarData.length < 2 ^ 64 := by unfold baMaxCap at *; omega
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hltS]
  rw [hadd] at hreg
  have hhdrEq : bytes o.addr
      (u64ListBytes [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap]) =
      cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) := by
    have hle3 : 8 * [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap].length ≤ 2 ^ 64 :=
      by simp only [List.length_cons, List.length_nil]; decide
    rw [← array64_eq_bytes o.addr _ hle3]
    simp only [array64_cons, array64_nil, Std.ExtHashMap.sep_emp, BitVec.add_assoc]
    have h88 : (8 : BitVec 64) + 8 = 16#64 := by decide
    have ha1 : o.addr + (8 : BitVec 64) = o.addr + 8#64 := rfl
    rw [h88, ha1]
    ac_rfl
  rw [hhdrEq] at hreg
  dsimp only [lcnfObjMem]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcanon.2.2.2.2.2.1]; decide)),
    ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcanon.2.2.2.2.2.1]; decide)),
    ite_eq_left_of_eq_true _ _ (eq_true hcanon.2.2.2.2.2.1)]
  exact sep_cast hreg (by ac_rfl)

private theorem arrObjMem_of_bytes {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : ArrCanon o)
    (hc : (bytes o.addr (u64ListBytes ([o.header, BitVec.ofNat 64 o.fields.length,
          BitVec.ofNat 64 o.cap] ++ o.fields) ++
        List.replicate (8 * (o.cap - o.fields.length)) 0) ⋆ R) m) :
    (lcnfObjMem o ⋆ R) m := by
  have hlen1 : (u64ListBytes ([o.header, BitVec.ofNat 64 o.fields.length,
      BitVec.ofNat 64 o.cap] ++ o.fields)).length = 24 + 8 * o.fields.length := by
    rw [u64ListBytes_length]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlenT : 24 + 8 * o.fields.length + 8 * (o.cap - o.fields.length) ≤ 2 ^ 64 := by
    have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega
  have h1 := sep_bytes_split (by
    rw [hlen1, List.length_replicate]; exact hlenT) hc
  rw [hlen1] at h1
  have h1' : (bytes (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
        (List.replicate (8 * (o.cap - o.fields.length)) 0) ⋆
      (bytes o.addr (u64ListBytes ([o.header, BitVec.ofNat 64 o.fields.length,
        BitVec.ofNat 64 o.cap] ++ o.fields)) ⋆ R)) m := sep_cast h1 (by ac_rfl)
  have hreg := sep_bytes_to_region h1'
  have hhdrEq : bytes o.addr (u64ListBytes
      ([o.header, BitVec.ofNat 64 o.fields.length, BitVec.ofNat 64 o.cap] ++ o.fields)) =
      cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆ array64 (o.addr + 24#64) o.fields := by
    have hle64 : 8 * ([o.header, BitVec.ofNat 64 o.fields.length,
        BitVec.ofNat 64 o.cap] ++ o.fields).length ≤ 2 ^ 64 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega
    rw [← array64_eq_bytes o.addr _ hle64]
    rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      array64_cons, array64_cons, array64_cons, BitVec.add_assoc, BitVec.add_assoc]
    have h888 : (8 : BitVec 64) + 8 + 8 = 24#64 := by decide
    have h88 : (8 : BitVec 64) + 8 = 16#64 := by decide
    have ha0 : o.addr + (8 : BitVec 64) = o.addr + 8#64 := rfl
    rw [h888, h88, ha0]
    ac_rfl
  rw [hhdrEq] at hreg
  dsimp only [lcnfObjMem]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcanon.2.2.2.2.2.1]; decide)),
    ite_eq_left_of_eq_true _ _ (eq_true hcanon.2.2.2.2.2.1)]
  exact sep_cast hreg (by ac_rfl)

/-! ## 4. Non-Vacuity (`XPost := False`) Concrete `Mem 64` Theorems -/

/-- Non-vacuity (`XPost := False`) for `lcnf_ba_empty` on the concrete `nvRtBytes` memory. -/
theorem nv_lcnf_ba_empty :
    Func.wp rtR2Env lcnf_ba_empty_body (nvRtAddr, ()) (nvRtBytes.At nvRtAddr)
      (fun (p, _) m' => p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
        ∃ st' : RtC0State, st'.hdr.s_ba_empty = p ∧
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkBaObj p 0#32 0 [])) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_ba_empty_sound
  have hmRt : (rtC0Inv nvRtAddr nvRtSt ⋆ Std.ExtHashMap.emp) (nvRtBytes.At nvRtAddr) :=
    nvRtSt_inv (by rw [Std.ExtHashMap.sep_emp]; rfl)
  rw [Std.ExtHashMap.sep_emp] at hmRt
  refine ⟨nvRtSt, Std.ExtHashMap.emp, ?_, ?_⟩
  · rwa [Std.ExtHashMap.sep_emp]
  · have h0 : ¬ (nvRtSt.hdr.s_ba_empty ≠ 0#64) := fun h => h rfl
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    dsimp only [nvRtSt, nvHdr]
    refine ⟨by decide, Or.inr (by decide), fun p st' m' hp0 hp8 _ _ hba hm' => ?_⟩
    rw [Std.ExtHashMap.sep_emp] at hm'
    exact ⟨hp0, hp8, st', hba, hm'⟩

/-- Concrete exclusive `ByteArray` (`rc = 1`, `cap = 8`, `[65, 66]`) at `nvBa1Addr`. -/
def nvBa1Addr : BitVec 64 := nvRtAddr + 34216#64

def nvBa1 : LcnfObj := mkBaObj nvBa1Addr 1#32 8 [65, 66]

def nvBa1Bytes : List UInt8 :=
  u64ListBytes [nvBa1.header, BitVec.ofNat 64 nvBa1.arrSize, BitVec.ofNat 64 nvBa1.cap] ++
    nvBa1.scalarData ++ List.replicate (nvBa1.totalBytes - (24 + nvBa1.scalarData.length)) 0

/-- Concrete shared `ByteArray` (`rc = 2`, `cap = 8`, `[65, 66]`) at `nvBa2Addr`. -/
def nvBa2Addr : BitVec 64 := nvBa1Addr + 32#64

def nvBa2 : LcnfObj := mkBaObj nvBa2Addr 2#32 8 [65, 66]

def nvBa2Bytes : List UInt8 :=
  u64ListBytes [nvBa2.header, BitVec.ofNat 64 nvBa2.arrSize, BitVec.ofNat 64 nvBa2.cap] ++
    nvBa2.scalarData ++ List.replicate (nvBa2.totalBytes - (24 + nvBa2.scalarData.length)) 0

/-- Combined concrete `Mem 64` slab with `nvRtSt`, exclusive `nvBa1`, and shared `nvBa2`. -/
def nvBaSlabMem : Mem 64 :=
  (nvRtBytes ++ nvBa1Bytes ++ nvBa2Bytes).At nvRtAddr

private theorem nvBa1Bytes_len : nvBa1Bytes.length = 32 := by
  dsimp only [nvBa1Bytes, nvBa1, mkBaObj, LcnfObj.totalBytes, sarrayTag, baAllocBytes, align8]
  rw [List.length_append, List.length_append, u64ListBytes_length, List.length_replicate]
  decide

private theorem nvBa2Bytes_len : nvBa2Bytes.length = 32 := by
  dsimp only [nvBa2Bytes, nvBa2, mkBaObj, LcnfObj.totalBytes, sarrayTag, baAllocBytes, align8]
  rw [List.length_append, List.length_append, u64ListBytes_length, List.length_replicate]
  decide

private theorem nvBa1_canon : BaCanon nvBa1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvBa2_canon : BaCanon nvBa2 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvBaSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvBa1 ⋆ lcnfObjMem nvBa2) nvBaSlabMem := by
  have hm0 : bytes nvRtAddr (nvRtBytes ++ (nvBa1Bytes ++ nvBa2Bytes)) nvBaSlabMem := by
    simp [nvBaSlabMem, bytes, List.append_assoc]
  have h0 : (bytes nvRtAddr (nvRtBytes ++ (nvBa1Bytes ++ nvBa2Bytes)) ⋆ Std.ExtHashMap.emp)
      nvBaSlabMem := by
    rwa [Std.ExtHashMap.sep_emp]
  have h1 := sep_bytes_split (by
    rw [nvRtBytes_length, List.length_append, nvBa1Bytes_len, nvBa2Bytes_len]; omega) h0
  rw [nvRtBytes_length] at h1
  change (bytes nvRtAddr nvRtBytes ⋆ (bytes nvBa1Addr (nvBa1Bytes ++ nvBa2Bytes) ⋆
    Std.ExtHashMap.emp)) nvBaSlabMem at h1
  have hRt := nvRtSt_inv h1
  have hRt' : (bytes nvBa1Addr (nvBa1Bytes ++ nvBa2Bytes) ⋆ rtC0Inv nvRtAddr nvRtSt)
      nvBaSlabMem := sep_cast hRt (by ac_rfl)
  have h2 := sep_bytes_split (by rw [nvBa1Bytes_len, nvBa2Bytes_len]; omega) hRt'
  rw [nvBa1Bytes_len] at h2
  change (bytes nvBa1Addr nvBa1Bytes ⋆ (bytes nvBa2Addr nvBa2Bytes ⋆
    rtC0Inv nvRtAddr nvRtSt)) nvBaSlabMem at h2
  have hO1 := baObjMem_of_bytes nvBa1_canon h2
  have hO1' : (bytes nvBa2Addr nvBa2Bytes ⋆ (lcnfObjMem nvBa1 ⋆ rtC0Inv nvRtAddr nvRtSt))
      nvBaSlabMem := sep_cast hO1 (by ac_rfl)
  have hO2 := baObjMem_of_bytes nvBa2_canon hO1'
  exact sep_cast hO2 (by ac_rfl)

/-- Concrete `Mem 64` (`XPost := False`): exclusive `lcnf_ba_push` mutates in-place. -/
theorem nv_lcnf_ba_push_excl :
    Func.wp rtR2Env lcnf_ba_push_body (nvRtAddr, nvBa1Addr, 67#64, ()) nvBaSlabMem
      (fun (r, _) m' => r = nvBa1Addr ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆
          lcnfObjMem (mkBaObj nvBa1Addr 1#32 8 [65, 66, 67]) ⋆ lcnfObjMem nvBa2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_ba_push_sound
  refine ⟨nvRtSt, nvBa1, lcnfObjMem nvBa2, rfl, nvBa1_canon,
    sep_cast nvBaSlabMem_split (by ac_rfl), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  refine ⟨fun hneed => by simp [nvBa1, mkBaObj] at hneed,
    fun r st' m' _ _ _ _ hin _ hm' => ?_⟩
  rcases hin rfl (by decide) with ⟨rfl, rfl⟩
  exact ⟨rfl, sep_cast hm' (by ac_rfl)⟩

/-- Concrete `Mem 64` (`XPost := False`): shared `lcnf_ba_push` copies + decrements `rc`. -/
theorem nv_lcnf_ba_push_shared :
    Func.wp rtR2Env lcnf_ba_push_body (nvRtAddr, nvBa2Addr, 67#64, ()) nvBaSlabMem
      (fun (r, _) m' => r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
        (∃ st' : RtC0State,
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkBaObj r 1#32 8 [65, 66, 67]) ⋆
            lcnfObjMem (nvBa2.withRc 1#32) ⋆ lcnfObjMem nvBa1) m'))
      (fun _ _ _ _ => False) := by
  apply lcnf_ba_push_sound
  refine ⟨nvRtSt, nvBa2, lcnfObjMem nvBa1, rfl, nvBa2_canon,
    sep_cast nvBaSlabMem_split (by ac_rfl), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  refine ⟨fun _ => Or.inr (by decide), fun r st' m' hr0 hr8 _ _ _ _ hm' => ?_⟩
  have hdec : decNonExclRc nvBa2.rc = 1#32 := by decide
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), hdec] at hm'
  exact ⟨hr0, hr8, st', sep_cast hm' (by ac_rfl)⟩

/-- Concrete `Mem 64` (`XPost := False`): exclusive `lcnf_ba_set` mutates in-place. -/
theorem nv_lcnf_ba_set_excl :
    Func.wp rtR2Env lcnf_ba_set_body (nvRtAddr, nvBa1Addr, 1#64, 90#64, 1#64, ()) nvBaSlabMem
      (fun (r, _) m' => r = nvBa1Addr ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆
          lcnfObjMem (mkBaObj nvBa1Addr 1#32 8 [65, 90]) ⋆ lcnfObjMem nvBa2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_ba_set_sound
  refine ⟨nvRtSt, nvBa1, lcnfObjMem nvBa2, rfl, nvBa1_canon,
    sep_cast nvBaSlabMem_split (by ac_rfl), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  refine ⟨fun h => absurd rfl h, fun r st' m' _ _ _ _ hin _ hm' => ?_⟩
  rcases hin rfl with ⟨rfl, rfl⟩
  exact ⟨rfl, sep_cast hm' (by ac_rfl)⟩

/-- Concrete `Mem 64` (`XPost := False`): `lcnf_ba_get` & `lcnf_ba_cmp_op` on `nvBaSlabMem`. -/
theorem nv_lcnf_ba_get_and_cmp :
    Func.wp rtR2Env lcnf_ba_get_body (nvRtAddr, nvBa1Addr, 1#64, 1#64, ()) nvBaSlabMem
      (fun (v, _) _ => v = 66#64) (fun _ _ _ _ => False) ∧
    Func.wp rtR2Env lcnf_ba_cmp_op_body (nvRtAddr, 0#64, nvBa1Addr, nvBa2Addr, ()) nvBaSlabMem
      (fun (v, _) _ => v = 1#64) (fun _ _ _ _ => False) := by
  constructor
  · apply lcnf_ba_get_sound
    exact ⟨nvBa1, lcnfObjMem nvBa2 ⋆ rtC0Inv nvRtAddr nvRtSt, rfl, nvBa1_canon,
      sep_cast nvBaSlabMem_split (by ac_rfl), rfl⟩
  · apply lcnf_ba_cmp_op_sound
    refine ⟨nvBa1, nvBa2, rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvBa2,
      rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvBa1, rfl, rfl, nvBa1_canon, nvBa2_canon,
      sep_cast nvBaSlabMem_split (by ac_rfl), sep_cast nvBaSlabMem_split (by ac_rfl), ?_⟩
    decide

/-- Concrete exclusive `Array` (`rc = 1`, `cap = 4`, tagged scalars `[3, 5]`) at `nvArr1Addr`. -/
def nvArr1Addr : BitVec 64 := nvRtAddr + 34216#64

def nvArr1 : LcnfObj := mkArrObj nvArr1Addr 1#32 4 [3#64, 5#64]

def nvArr1Bytes : List UInt8 :=
  u64ListBytes ([nvArr1.header, 2#64, 4#64] ++ nvArr1.fields) ++ List.replicate 16 0

/-- Concrete shared `Array` (`rc = 2`, `cap = 4`, tagged scalars `[3, 5]`) at `nvArr2Addr`. -/
def nvArr2Addr : BitVec 64 := nvArr1Addr + 56#64

def nvArr2 : LcnfObj := mkArrObj nvArr2Addr 2#32 4 [3#64, 5#64]

def nvArr2Bytes : List UInt8 :=
  u64ListBytes ([nvArr2.header, 2#64, 4#64] ++ nvArr2.fields) ++ List.replicate 16 0

/-- Combined concrete `Mem 64` slab with `nvRtSt`, exclusive `nvArr1`, and shared `nvArr2`. -/
def nvArrSlabMem : Mem 64 :=
  (nvRtBytes ++ nvArr1Bytes ++ nvArr2Bytes).At nvRtAddr

private theorem nvArr1Bytes_len : nvArr1Bytes.length = 56 := by
  dsimp only [nvArr1Bytes, nvArr1, mkArrObj]
  rw [List.length_append, u64ListBytes_length, List.length_replicate]
  decide

private theorem nvArr2Bytes_len : nvArr2Bytes.length = 56 := by
  dsimp only [nvArr2Bytes, nvArr2, mkArrObj]
  rw [List.length_append, u64ListBytes_length, List.length_replicate]
  decide

private theorem nvArr1_canon : ArrCanon nvArr1 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvArr2_canon : ArrCanon nvArr2 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide, by decide⟩

private theorem nvArrSlabMem_split :
    (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfObjMem nvArr1 ⋆ lcnfObjMem nvArr2) nvArrSlabMem := by
  have hm0 : bytes nvRtAddr (nvRtBytes ++ (nvArr1Bytes ++ nvArr2Bytes)) nvArrSlabMem := by
    simp [nvArrSlabMem, bytes, List.append_assoc]
  have h0 : (bytes nvRtAddr (nvRtBytes ++ (nvArr1Bytes ++ nvArr2Bytes)) ⋆ Std.ExtHashMap.emp)
      nvArrSlabMem := by
    rwa [Std.ExtHashMap.sep_emp]
  have h1 := sep_bytes_split (by
    rw [nvRtBytes_length, List.length_append, nvArr1Bytes_len, nvArr2Bytes_len]; omega) h0
  rw [nvRtBytes_length] at h1
  change (bytes nvRtAddr nvRtBytes ⋆ (bytes nvArr1Addr (nvArr1Bytes ++ nvArr2Bytes) ⋆
    Std.ExtHashMap.emp)) nvArrSlabMem at h1
  have hRt := nvRtSt_inv h1
  have hRt' : (bytes nvArr1Addr (nvArr1Bytes ++ nvArr2Bytes) ⋆ rtC0Inv nvRtAddr nvRtSt)
      nvArrSlabMem := sep_cast hRt (by ac_rfl)
  have h2 := sep_bytes_split (by rw [nvArr1Bytes_len, nvArr2Bytes_len]; omega) hRt'
  rw [nvArr1Bytes_len] at h2
  change (bytes nvArr1Addr nvArr1Bytes ⋆ (bytes nvArr2Addr nvArr2Bytes ⋆
    rtC0Inv nvRtAddr nvRtSt)) nvArrSlabMem at h2
  have hO1 := arrObjMem_of_bytes nvArr1_canon h2
  have hO1' : (bytes nvArr2Addr nvArr2Bytes ⋆ (lcnfObjMem nvArr1 ⋆ rtC0Inv nvRtAddr nvRtSt))
      nvArrSlabMem := sep_cast hO1 (by ac_rfl)
  have hO2 := arrObjMem_of_bytes nvArr2_canon hO1'
  exact sep_cast hO2 (by ac_rfl)

/-- Concrete `Mem 64` (`XPost := False`): exclusive `lcnf_array_push` mutates in-place. -/
theorem nv_lcnf_array_push_excl :
    Func.wp rtR2Env lcnf_array_push_body (nvRtAddr, nvArr1Addr, 7#64, ()) nvArrSlabMem
      (fun (r, _) m' => r = nvArr1Addr ∧
        (rtC0Inv nvRtAddr nvRtSt ⋆
          lcnfObjMem (mkArrObj nvArr1Addr 1#32 4 [3#64, 5#64, 7#64]) ⋆ lcnfObjMem nvArr2) m')
      (fun _ _ _ _ => False) := by
  apply lcnf_array_push_sound
  refine ⟨nvRtSt, nvArr1, [], lcnfObjMem nvArr2, rfl, nvArr1_canon,
    (fun _ h => nomatch h), sep_cast nvArrSlabMem_split (by ac_rfl),
    (fun h => absurd rfl h), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  refine ⟨fun h => by simp [nvArr1, mkArrObj] at h,
    fun r st' ch' m' _ _ _ _ hin _ hch1 _ hm' => ?_⟩
  rcases hin rfl (by decide) with ⟨rfl, rfl⟩
  have hcap4 : arrEnsureCap nvArr1.fields.length nvArr1.cap 1#64 = 4 := by decide
  have hrc1 : nvArr1.rc = 1#32 := rfl
  have hf : nvArr1.fields ++ [7#64] = [3#64, 5#64, 7#64] := rfl
  simp only [hcap4, hrc1, ↓reduceIte, hch1 hrc1, hf] at hm'
  dsimp only [lcnfHeap, lcnfHeap._f] at hm'
  rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_emp] at hm'
  exact ⟨rfl, sep_cast hm' (by ac_rfl)⟩

/-- Concrete `Mem 64` (`XPost := False`): shared `lcnf_array_push` copies + decrements `rc`. -/
theorem nv_lcnf_array_push_shared :
    Func.wp rtR2Env lcnf_array_push_body (nvRtAddr, nvArr2Addr, 7#64, ()) nvArrSlabMem
      (fun (r, _) m' => r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
        (∃ st' : RtC0State,
          (rtC0Inv nvRtAddr st' ⋆ lcnfObjMem (mkArrObj r 1#32 4 [3#64, 5#64, 7#64]) ⋆
            lcnfObjMem (nvArr2.withRc 1#32) ⋆ lcnfObjMem nvArr1) m'))
      (fun _ _ _ _ => False) := by
  apply lcnf_array_push_sound
  refine ⟨nvRtSt, nvArr2, [], lcnfObjMem nvArr1, rfl, nvArr2_canon,
    (fun _ h => nomatch h), sep_cast nvArrSlabMem_split (by ac_rfl),
    (fun _ => ⟨fun f hf1 hf2 => by
      simp only [nvArr2, mkArrObj, List.mem_cons, List.not_mem_nil, or_false] at hf1
      rcases hf1 with rfl | rfl <;> exact absurd hf2 (by decide),
      fun _ h => nomatch h⟩), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  refine ⟨fun _ => Or.inr (by decide), fun r st' ch' m' hr0 hr8 _ _ _ _ _ hchN hm' => ?_⟩
  have hcap4 : arrEnsureCap nvArr2.fields.length nvArr2.cap 1#64 = 4 := by decide
  have hdec : decNonExclRc nvArr2.rc = 1#32 := by decide
  have hne1 : nvArr2.rc ≠ 1#32 := by decide
  have hinc : incChildrenObjs nvArr2.fields [] = [] := rfl
  have hf : nvArr2.fields ++ [7#64] = [3#64, 5#64, 7#64] := rfl
  simp only [hcap4, hne1, ↓reduceIte, hdec, hchN hne1, hinc, hf] at hm'
  dsimp only [lcnfHeap, lcnfHeap._f] at hm'
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr0, hr8, st', sep_cast hm' (by ac_rfl)⟩

/-- Concrete `Mem 64` (`XPost := False`): exclusive `set`, `pop`, `swap`, `get`, and `oob`. -/
theorem nv_lcnf_array_ops_and_oob :
    Func.wp rtR2Env lcnf_array_set_body
      (nvRtAddr, nvArr1Addr, 1#64, 9#64, 1#64, ()) nvArrSlabMem
      (fun (r, _) _ => r = nvArr1Addr) (fun _ _ _ _ => False) ∧
    Func.wp rtR2Env lcnf_array_pop_body (nvRtAddr, nvArr1Addr, ()) nvArrSlabMem
      (fun (r, _) _ => r = nvArr1Addr) (fun _ _ _ _ => False) ∧
    Func.wp rtR2Env lcnf_array_swap_body
      (nvRtAddr, nvArr1Addr, 1#64, 3#64, 1#64, ()) nvArrSlabMem
      (fun (r, _) _ => r = nvArr1Addr) (fun _ _ _ _ => False) ∧
    Func.wp rtR2Env lcnf_array_get_body
      (nvRtAddr, 1#64, nvArr1Addr, 1#64, 3#64, ()) nvArrSlabMem
      (fun (v, _) _ => v = 5#64) (fun _ _ _ _ => False) ∧
    Func.wp rtR2Env lcnf_oob_body (nvRtAddr, 1#64, ()) nvArrSlabMem
      (fun (v, _) _ => v = 1#64) (fun _ _ _ _ => False) := by
  have hwfObjs : ∀ o ∈ [nvArr1, nvArr2], o.Wf := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact nvArr1_canon.wf
    · exact nvArr2_canon.wf
  have hch1 : nvArr1.childFields = [3#64, 5#64] := by decide
  have hch2 : nvArr2.childFields = [3#64, 5#64] := by decide
  have hclosed : lcnfHeapClosed [nvArr1, nvArr2] := by
    intro o ho f hf hfe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · rw [hch1] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> exact absurd hfe (by decide)
    · rw [hch2] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> exact absurd hfe (by decide)
  have hheap : (rtC0Inv nvRtAddr nvRtSt ⋆ lcnfHeap [nvArr1, nvArr2]) nvArrSlabMem := by
    dsimp only [lcnfHeap, lcnfHeap._f]
    rw [Std.ExtHashMap.sep_emp]
    exact sep_cast nvArrSlabMem_split (by ac_rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply lcnf_array_set_sound
    refine ⟨nvRtSt, [nvArr1, nvArr2], 0, by decide, Std.ExtHashMap.emp,
      rfl, nvArr1_canon, by decide, hwfObjs, hclosed,
      by rw [Std.ExtHashMap.sep_emp]; exact sep_cast hheap (by ac_rfl), ?_⟩
    rw [dite_eq_left (by decide)]
    exact ⟨fun h => absurd rfl h, fun _ _ h5 => by simp [nvArr1, mkArrObj] at h5,
      fun _ _ hfe => absurd hfe (by decide),
      fun r _ _ _ _ _ _ _ hr _ _ _ _ _ _ _ _ _ => hr rfl⟩
  · apply lcnf_array_pop_sound
    refine ⟨nvRtSt, [nvArr1, nvArr2], 0, by decide, Std.ExtHashMap.emp,
      rfl, nvArr1_canon, by decide, hwfObjs, hclosed,
      by rw [Std.ExtHashMap.sep_emp]; exact sep_cast hheap (by ac_rfl),
      fun h => absurd rfl h, fun _ _ _ h5 => by simp [nvArr1, mkArrObj] at h5,
      fun r _ _ _ _ _ _ _ hr _ _ _ _ _ _ _ _ _ => hr rfl⟩
  · apply lcnf_array_swap_sound
    refine ⟨nvRtSt, nvArr1, [], lcnfObjMem nvArr2, rfl, nvArr1_canon,
      (fun _ h => nomatch h), sep_cast nvArrSlabMem_split (by ac_rfl), ?_⟩
    rw [dite_eq_left (by decide)]
    exact ⟨fun h => absurd rfl h, fun r _ _ _ _ _ _ _ hin _ _ _ _ => (hin rfl).1⟩
  · apply lcnf_array_get_sound
    refine ⟨nvArr1, [nvArr1, nvArr2], rtC0Inv nvRtAddr nvRtSt, List.mem_cons_self, rfl,
      nvArr1_canon, hwfObjs, sep_cast hheap (by ac_rfl), ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    exact ⟨fun ⟨hb, _⟩ => absurd hb (by decide), fun _ _ _ => rfl⟩
  · apply lcnf_oob_sound
    dsimp only [lcnfOobSpec]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (by decide)))]

end LeanQbe.T.LeanLCNF
