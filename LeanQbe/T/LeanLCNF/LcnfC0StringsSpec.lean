module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersSpec
import Kraken.Separation

/-!
# Specifications for `LcnfC0Strings` (`rtR2bMod`)

Defines canonical object predicates (`StrCanon`, `ListConsCanon`, `ExclListMem`, `IsListInHeap`,
`MpzCanon`), pure UTF-8 / Char / decimal formatting semantics, `Spec` contracts (using R0's
progress-aware `lcnfAllocRemSpec` for multi-allocation routines) for the 6 `r2b_*` helpers,
the 6 R2 `r2_*` externs, and 13 exported `lcnf_*` runtime functions, and the closed specification
table `rtR2bSpecEntries` / `rtR2bEnv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open Std.ExtHashMap

/-! ## 1. Constants, Object Layouts, and Canonical Predicates -/

def strMaxCap : Nat := 268435415
def mpzMaxLimbsNat : Nat := 13421770
def listConsTag : Nat := 1

def strHeaderWord : BitVec 64 := 0xf901000000000001#64
def listConsHeaderWord : BitVec 64 := 0x0102001800000001#64
def mpzHeaderWord : BitVec 64 := 0xfa00000000000001#64

def strAllocBytes (cap : Nat) : Nat := align8 (32 + cap)
def sarrayAllocBytes (cap : Nat) : Nat := align8 (24 + cap)
def mpzAllocBytes (cap : Nat) : Nat := 16 + 8 * cap

def boxNat (n : Nat) : BitVec 64 := BitVec.ofNat 64 (2 * n + 1)

def strPayload (o : LcnfObj) : List UInt8 := o.scalarData.dropLast

def mkStrObj (addr : BitVec 64) (rc : BitVec 32) (cap : Nat)
    (payload : List UInt8) (strLen : Nat) : LcnfObj :=
  { addr := addr
    rc := rc
    csSz := 0
    other := 1
    tag := stringTag
    cap := cap
    arrSize := payload.length + 1
    strLen := strLen
    scalarData := payload ++ [0] }

def StrCanon (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧
    o.addr.toNat % 8 = 0 ∧
      0 ≤ o.rc.toInt ∧
        o.csSz = 0 ∧
          o.other = 1 ∧
            o.tag = stringTag ∧
              1 ≤ o.arrSize ∧
                o.arrSize ≤ o.cap ∧
                  o.cap ≤ strMaxCap ∧
                    o.scalarData.length = o.arrSize ∧
                      o.scalarData.getLast? = some 0 ∧
                        o.strLen < 2 ^ 64

def strGrowCap (rc : BitVec 32) (oldCap need : Nat) : Nat :=
  if rc = 1#32 then min strMaxCap (max (oldCap * 2) need) else need

def mkListConsObj (addr : BitVec 64) (rc : BitVec 32) (hd tl : BitVec 64) : LcnfObj :=
  { addr := addr
    rc := rc
    csSz := 24
    other := 2
    tag := listConsTag
    fields := [hd, tl] }

def ListConsCanon (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧
    o.addr.toNat % 8 = 0 ∧
      0 ≤ o.rc.toInt ∧
        o.csSz = 24 ∧
          o.other = 2 ∧
            o.tag = listConsTag ∧
              o.fields.length = 2 ∧
                o.scalarData = []

inductive ExclListMem : BitVec 64 → List (BitVec 64) → List LcnfObj → Prop
  | nil : ExclListMem 1#64 [] []
  | cons {p hd tl : BitVec 64} {rest : List (BitVec 64)} {o : LcnfObj} {os : List LcnfObj} :
      o = mkListConsObj p 1#32 hd tl →
      p ≠ 0#64 →
      p.toNat % 8 = 0 →
      ExclListMem tl rest os →
      ExclListMem p (hd :: rest) (o :: os)

inductive IsListInHeap (objs : List LcnfObj) : BitVec 64 → List (BitVec 64) → Prop
  | nil : IsListInHeap objs 1#64 []
  | cons {p hd tl : BitVec 64} {rest : List (BitVec 64)} {node : LcnfObj} :
      node ∈ objs →
      node.addr = p →
      ListConsCanon node →
      node.fields = [hd, tl] →
      (p &&& 1#64) = 0#64 →
      IsListInHeap objs tl rest →
      IsListInHeap objs p (hd :: rest)

def MpzCanon (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧
    o.addr.toNat % 8 = 0 ∧
      0 ≤ o.rc.toInt ∧
        o.csSz = 0 ∧
          o.other = 0 ∧
            o.tag = mpzTag ∧
              o.limbs.length = o.cap ∧
                o.arrSize ≤ o.cap ∧
                  o.cap ≤ 33554429

def mpzLimbsVal (xs : List (BitVec 64)) : Nat :=
  xs.foldr (fun w acc => w.toNat + 2 ^ 64 * acc) 0

def trimZeroLimbsLen : List (BitVec 64) → Nat → Nat
  | _, 0 => 0
  | xs, k + 1 => if xs.getD k 0#64 = 0#64 then trimZeroLimbsLen xs k else k + 1

def NatInHeap (n : BitVec 64) (val : Nat) (objs : List LcnfObj) : Prop :=
  if (n &&& 1#64) ≠ 0#64 then val = (n >>> 1).toNat
  else
    ∃ nObj, nObj ∈ objs ∧ nObj.addr = n ∧ MpzCanon nObj ∧
      val = mpzLimbsVal (nObj.limbs.take nObj.arrSize)

theorem StrCanon.wf {o : LcnfObj} (h : StrCanon o) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, htag, ha1, hac, hcap, hsl, _, hlen⟩
  have htb : o.totalBytes = align8 (32 + o.cap) := by
    unfold LcnfObj.totalBytes; simp [htag, stringTag, arrayTag, sarrayTag]
  have hmin : rtMinObjBytes ≤ o.totalBytes := by
    rw [htb]; unfold rtMinObjBytes align8; omega
  have hmax : o.totalBytes < rtMaxObjBytes := by
    rw [htb]; unfold rtMaxObjBytes align8 strMaxCap at *; omega
  have hmod : o.totalBytes % 8 = 0 := by
    rw [htb]; unfold align8; omega
  refine ⟨h0, h8, hrc, by omega, by omega, by rw [htag]; decide, hmin, hmax, hmod, ?_⟩
  simp only [htag, stringTag, closureTag, arrayTag, sarrayTag,
    show (249 : Nat) ≠ 246 by decide, show (249 : Nat) ≠ 248 by decide, ↓reduceIte]
  unfold strMaxCap at hcap
  exact ⟨hcap, by omega, hlen, by omega⟩

theorem ListConsCanon.wf {o : LcnfObj} (h : ListConsCanon o) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, htag, hf, hs⟩
  have htb : o.totalBytes = o.csSz := by
    unfold LcnfObj.totalBytes; simp [htag, listConsTag, arrayTag, sarrayTag, stringTag, mpzTag]
  refine ⟨h0, h8, hrc, by omega, by omega, by rw [htag]; decide, ?_, ?_, ?_, ?_⟩
  · rw [htb, hcs]; unfold rtMinObjBytes; omega
  · rw [htb, hcs]; unfold rtMaxObjBytes; omega
  · rw [htb, hcs]
  · simp [htag, listConsTag, closureTag, arrayTag, sarrayTag, stringTag, mpzTag,
      hf, ho, hs, hcs]

theorem MpzCanon.wf {o : LcnfObj} (h : MpzCanon o) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, htag, hl, hac, hcap⟩
  have htb : o.totalBytes = 16 + 8 * o.cap := by
    unfold LcnfObj.totalBytes; simp [htag, arrayTag, sarrayTag, stringTag, mpzTag]
  refine ⟨h0, h8, hrc, by omega, by omega, by rw [htag]; decide, ?_, ?_, ?_, ?_⟩
  · rw [htb]; unfold rtMinObjBytes; omega
  · rw [htb]; unfold rtMaxObjBytes; omega
  · rw [htb]; omega
  · simp [htag, closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
    exact ⟨hl, hcap, by omega⟩

theorem mkStrObj_canon {p : BitVec 64} {rc : BitVec 32} {cap len : Nat}
    {payload : List UInt8} (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0)
    (hrc : 0 ≤ rc.toInt) (hlen : payload.length + 1 ≤ cap) (hcap : cap ≤ strMaxCap)
    (hslen : len < 2 ^ 64) : StrCanon (mkStrObj p rc cap payload len) := by
  refine ⟨hp0, hp8, hrc, rfl, rfl, rfl, Nat.succ_pos _, hlen, hcap, ?_, ?_, hslen⟩
  · simp [mkStrObj]
  · simp [mkStrObj]

theorem mkListConsObj_canon {p : BitVec 64} {rc : BitVec 32} {hd tl : BitVec 64}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) (hrc : 0 ≤ rc.toInt) :
    ListConsCanon (mkListConsObj p rc hd tl) :=
  ⟨hp0, hp8, hrc, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Pure Char, UTF-8, Comparison, Heap-Update, and Decimal Helpers -/

def isValidCharNat (v : Nat) : Bool :=
  v < 0xd800 || (0xe000 ≤ v && v < 0x110000)

def charOfNatVal (arg : BitVec 64) : BitVec 64 :=
  if (arg &&& 1#64) = 0#64 then 0#64
  else
    let v := (arg >>> 1).toNat
    if isValidCharNat v then BitVec.ofNat 64 v else 0#64

def utf8LenNat (cp : Nat) : Nat :=
  if cp ≤ 0x7f then 1
  else if cp ≤ 0x7ff then 2
  else if cp ≤ 0xffff then 3
  else 4

def utf8EncodeBytes (cp : Nat) : List UInt8 :=
  if cp ≤ 0x7f then
    [UInt8.ofNat cp]
  else if cp ≤ 0x7ff then
    [UInt8.ofNat (0xc0 ||| (cp >>> 6)), UInt8.ofNat (0x80 ||| (cp &&& 0x3f))]
  else if cp ≤ 0xffff then
    [ UInt8.ofNat (0xe0 ||| (cp >>> 12))
    , UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3f))
    , UInt8.ofNat (0x80 ||| (cp &&& 0x3f)) ]
  else
    [ UInt8.ofNat (0xf0 ||| ((cp >>> 18) &&& 0x07))
    , UInt8.ofNat (0x80 ||| ((cp >>> 12) &&& 0x3f))
    , UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3f))
    , UInt8.ofNat (0x80 ||| (cp &&& 0x3f)) ]

theorem utf8EncodeBytes_length (cp : Nat) : (utf8EncodeBytes cp).length = utf8LenNat cp := by
  unfold utf8EncodeBytes utf8LenNat
  by_cases h1 : cp ≤ 0x7f
  · simp [h1]
  · by_cases h2 : cp ≤ 0x7ff
    · simp [h1, h2]
    · by_cases h3 : cp ≤ 0xffff <;> simp [h1, h2, h3]

def charOpVal (op arg : BitVec 64) : BitVec 64 :=
  if op = 0#64 then charOfNatVal arg
  else boxNat (utf8LenNat (arg &&& 0xffffffff#64).toNat)

def utf8DecodeStepAt (bs : List UInt8) (idx : Nat) : Nat :=
  if idx ≥ bs.length then 0
  else
    let b0 := bs[idx]!.toNat
    if (b0 &&& 0x80) = 0 then 1
    else if (b0 &&& 0xe0) = 0xc0 then if idx + 1 < bs.length then 2 else 1
    else if (b0 &&& 0xf0) = 0xe0 then if idx + 2 < bs.length then 3 else 1
    else if (b0 &&& 0xf8) = 0xf0 then if idx + 3 < bs.length then 4 else 1
    else 1

def utf8DecodeCpAt (bs : List UInt8) (idx : Nat) : BitVec 64 :=
  if idx ≥ bs.length then 0#64
  else
    let b0 := bs[idx]!.toNat
    if (b0 &&& 0x80) = 0 then BitVec.ofNat 64 b0
    else if (b0 &&& 0xe0) = 0xc0 then
      if idx + 1 < bs.length then
        let b1 := bs[idx + 1]!.toNat
        BitVec.ofNat 64 (((b0 &&& 0x1f) <<< 6) ||| (b1 &&& 0x3f))
      else 0#64
    else if (b0 &&& 0xf0) = 0xe0 then
      if idx + 2 < bs.length then
        let b1 := bs[idx + 1]!.toNat
        let b2 := bs[idx + 2]!.toNat
        BitVec.ofNat 64 (((b0 &&& 0x0f) <<< 12) ||| ((b1 &&& 0x3f) <<< 6) ||| (b2 &&& 0x3f))
      else 0#64
    else if (b0 &&& 0xf8) = 0xf0 then
      if idx + 3 < bs.length then
        let b1 := bs[idx + 1]!.toNat
        let b2 := bs[idx + 2]!.toNat
        let b3 := bs[idx + 3]!.toNat
        BitVec.ofNat 64
          (((b0 &&& 0x07) <<< 18) ||| ((b1 &&& 0x3f) <<< 12) |||
            ((b2 &&& 0x3f) <<< 6) ||| (b3 &&& 0x3f))
      else 0#64
    else 0#64

theorem utf8DecodeStepAt_pos {bs : List UInt8} {idx : Nat} (h : idx < bs.length) :
    1 ≤ utf8DecodeStepAt bs idx ∧ idx + utf8DecodeStepAt bs idx ≤ bs.length := by
  unfold utf8DecodeStepAt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  dsimp only
  split
  · omega
  · split
    · split <;> omega
    · split
      · split <;> omega
      · split
        · split <;> omega
        · omega

def utf8DecodeFrom (bs : List UInt8) (idx : Nat) : List (BitVec 64) :=
  if h : idx < bs.length then
    let _ := h
    ((utf8DecodeCpAt bs idx <<< 1) ||| 1#64) ::
      utf8DecodeFrom bs (idx + utf8DecodeStepAt bs idx)
  else []
termination_by bs.length - idx
decreasing_by
  have := (utf8DecodeStepAt_pos h).1
  omega

def utf8CountFrom (bs : List UInt8) (idx : Nat) : Nat :=
  (utf8DecodeFrom bs idx).length

def utf8EncodeList : List (BitVec 64) → List UInt8
  | [] => []
  | hd :: tl => utf8EncodeBytes ((hd >>> 1) &&& 0xffffffff#64).toNat ++ utf8EncodeList tl

def strCmpOpVal (op : BitVec 64) (bs1 bs2 : List UInt8) : BitVec 64 :=
  if op = 0#64 then if cmpByteSlices bs1 bs2 = 1#64 then 1#64 else 0#64
  else if op = 1#64 then if cmpByteSlices bs1 bs2 = 0#64 then 1#64 else 0#64
  else cmpByteSlices bs1 bs2

def strPosClamp (v : BitVec 64) (sz : Nat) : Nat :=
  if (v &&& 1#64) ≠ 0#64 then min (v >>> 1).toNat sz else sz

def strPosOpVal (op : BitVec 64) (bs : List UInt8) (idxV _endV : BitVec 64) : BitVec 64 :=
  let sz := bs.length
  if op = 0#64 then
    if (idxV &&& 1#64) = 0#64 then 0#64
    else let idx := (idxV >>> 1).toNat; if idx < sz then utf8DecodeCpAt bs idx else 0#64
  else if op = 1#64 then
    if (idxV &&& 1#64) = 0#64 then idxV
    else
      let idx := (idxV >>> 1).toNat
      if idx < sz then ((BitVec.ofNat 64 (idx + utf8DecodeStepAt bs idx)) <<< 1) ||| 1#64
      else idxV
  else if op = 2#64 then
    if (idxV &&& 1#64) = 0#64 then 1#64
    else if (idxV >>> 1).toNat < sz then 0#64 else 1#64
  else if op = 4#64 then
    if (idxV &&& 1#64) = 0#64 then 0#64
    else let idx := (idxV >>> 1).toNat
      if h : idx < sz then BitVec.setWidth 64 bs[idx].toBitVec else 0#64
  else
    if (idxV &&& 1#64) = 0#64 then 0#64
    else let idx := (idxV >>> 1).toNat
      if idx > sz then 0#64
      else if h : idx < sz then
        if (bs[idx].toNat &&& 0xc0) ≠ 0x80 then 1#64 else 0#64
      else 1#64

def natDigitsRev (n : Nat) : List UInt8 :=
  if _h : n = 0 then []
  else UInt8.ofNat (48 + n % 10) :: natDigitsRev (n / 10)
termination_by n
decreasing_by omega

def natToDecimalBytes (n : Nat) : List UInt8 :=
  if n = 0 then [UInt8.ofNat 48] else (natDigitsRev n).reverse

def incObjList (v : BitVec 64) (objs : List LcnfObj) : List LcnfObj :=
  if v = 0#64 ∨ (v &&& 1#64) ≠ 0#64 then objs
  else objs.map (fun o => if o.addr = v then o.withRc (incRcVal o.rc) else o)

def incElemsList : List (BitVec 64) → List LcnfObj → List LcnfObj
  | [], objs => objs
  | v :: vs, objs => incElemsList vs (incObjList v objs)

def addRcObjList (v : BitVec 64) (delta : Nat) (objs : List LcnfObj) : List LcnfObj :=
  objs.map (fun o =>
    if o.addr = v ∧ o.rc ≠ 0#32 then o.withRc (o.rc + BitVec.ofNat 32 delta) else o)

theorem natToDecimalBytes_pos (n : Nat) : 1 ≤ (natToDecimalBytes n).length := by
  unfold natToDecimalBytes
  split
  · simp
  · next h =>
    have h1 : natDigitsRev n =
        UInt8.ofNat (48 + n % 10) :: natDigitsRev (n / 10) := by
      conv => lhs; unfold natDigitsRev
      simp [h]
    rw [h1]; simp

/-! ## 3. Allocator Progress Contract (`lcnfAllocRemSpec`) & Helper `Spec`s -/

def r2bAllocMpzSpec : Spec [i64, i64, i64] [i64] := fun (rt, cap, sz, ()) m Q X =>
  if sz.toNat ≤ cap.toNat ∧ cap.toNat ≤ 33554429 then
    let bytes := mpzAllocBytes cap.toNat
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
        st'.rem ≤ st.rem → st.rem - bytes ≤ st'.rem →
        (rtC0Inv rt st' ⋆ cell64 p mpzHeaderWord ⋆
          cell64 (p + 8#64) (cap ||| (sz <<< 32)) ⋆
          region (p + 16#64) (8 * cap.toNat) ⋆ R) m' →
        Q (p, ()) m'
  else
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

def r2bStrAllocCapSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, cap, sz, len, ()) m Q X =>
    if sz.toNat < strMaxCap ∧ sz.toNat < cap.toNat ∧ cap.toNat ≤ strMaxCap then
      let reqBytes := strAllocBytes cap.toNat
      ∃ (st : RtC0State) (R : Mem 64 → Prop),
        (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
        (rtC0Inv rt st ⋆ R) m ∧
        ∀ p st' m',
          p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
          st'.rem ≤ st.rem → st.rem - reqBytes ≤ st'.rem →
          (rtC0Inv rt st' ⋆ cell64 p strHeaderWord ⋆
            cell64 (p + 8#64) (sz + 1#64) ⋆ cell64 (p + 16#64) cap ⋆
            cell64 (p + 24#64) len ⋆ region (p + 32#64) sz.toNat ⋆
            bytes (p + 32#64 + sz) [(0 : UInt8)] ⋆
            region (p + 32#64 + sz + 1#64) (reqBytes - (32 + sz.toNat + 1)) ⋆ R) m' →
          Q (p, ()) m'
    else
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

def r2bUtf8LenSpec : Spec [i64] [i64] := fun (cp, ()) m Q _ =>
  Q (BitVec.ofNat 64 (utf8LenNat cp.toNat), ()) m

def r2bUtf8WriteSpec : Spec [i64, i64] [i64] := fun (dst, cp, ()) m Q _ =>
  let bs := utf8EncodeBytes cp.toNat
  ∃ (remCap : Nat) (R : Mem 64 → Prop),
    bs.length ≤ remCap ∧ remCap ≤ 2 ^ 64 ∧
    (region dst remCap ⋆ R) m ∧
    ∀ m', (bytes dst bs ⋆ region (dst + BitVec.ofNat 64 bs.length) (remCap - bs.length) ⋆ R) m' →
      Q (BitVec.ofNat 64 bs.length, ()) m'

def r2bUtf8DecodeStepSpec : Spec [i64, i64, i64] [i64] := fun (data, sz, idx, ()) m Q _ =>
  ∃ (bs : List UInt8) (R : Mem 64 → Prop),
    bs.length = sz.toNat ∧ (bytes data bs ⋆ R) m ∧
    Q (BitVec.ofNat 64 (utf8DecodeStepAt bs idx.toNat), ()) m

def r2bUtf8DecodeCpSpec : Spec [i64, i64, i64] [i64] := fun (data, sz, idx, ()) m Q _ =>
  ∃ (bs : List UInt8) (R : Mem 64 → Prop),
    bs.length = sz.toNat ∧ (bytes data bs ⋆ R) m ∧
    Q (utf8DecodeCpAt bs idx.toNat, ()) m

/-! ## 4. Specifications for All 13 Exported R2b Runtime Functions -/

def lcnfStrAllocSpec : Spec [i64, i64, i64] [i64] := fun (rt, sz, len, ()) m Q X =>
  if strMaxCap ≤ sz.toNat then
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
  else
    let reqBytes := strAllocBytes (sz.toNat + 1)
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
        st'.rem ≤ st.rem → st.rem - reqBytes ≤ st'.rem →
        (rtC0Inv rt st' ⋆ cell64 p strHeaderWord ⋆
          cell64 (p + 8#64) (sz + 1#64) ⋆ cell64 (p + 16#64) (sz + 1#64) ⋆
          cell64 (p + 24#64) len ⋆ region (p + 32#64) sz.toNat ⋆
          bytes (p + 32#64 + sz) [(0 : UInt8)] ⋆
          region (p + 32#64 + sz + 1#64) (reqBytes - (32 + sz.toNat + 1)) ⋆ R) m' →
        Q (p, ()) m'

def lcnfCharOpSpec : Spec [i64, i64, i64] [i64] := fun (rt, op, arg, ()) m Q X =>
  if op = 0#64 ∨ op = 1#64 then Q (charOpVal op arg, ()) m
  else X "lcnf_panic" [i64, i64] (rt, 1#64, ()) m

def lcnfStringPushSpec : Spec [i64, i64, i64] [i64] := fun (rt, s, c, ()) m Q X =>
  ∃ (st : RtC0State) (sObj : LcnfObj) (R : Mem 64 → Prop),
    sObj.addr = s ∧ StrCanon sObj ∧
    (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ R) m ∧
    let cp := (c &&& 0xffffffff#64).toNat
    let bs := strPayload sObj ++ utf8EncodeBytes cp
    let newSz := bs.length
    if strMaxCap ≤ newSz then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let inPlace := sObj.rc = 1#32 ∧ newSz + 1 ≤ sObj.cap
      let newCap := if inPlace then sObj.cap else strGrowCap sObj.rc sObj.cap (newSz + 1)
      let reqBytes := strAllocBytes newCap
      (¬ inPlace → (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
        (sObj.rc = 1#32 → 1 ≤ st.workCap)) ∧
      ∀ r st' m',
        r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        (inPlace → r = s ∧ st' = st) →
        let rObj := mkStrObj r 1#32 newCap bs ((sObj.strLen + 1) % 2 ^ 64)
        let oldKeep :=
          if sObj.rc = 1#32 then emp else lcnfObjMem (sObj.withRc (decNonExclRc sObj.rc))
        StrCanon rObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m' → Q (r, ()) m'

def lcnfStringAppendSpec : Spec [i64, i64, i64] [i64] := fun (rt, s1, s2, ()) m Q X =>
  ∃ (st : RtC0State) (s1Obj s2Obj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    s1Obj ∈ objs ∧ s1Obj.addr = s1 ∧ StrCanon s1Obj ∧
    s2Obj ∈ objs ∧ s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
    (∀ o ∈ objs, o.Wf) ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    let p1 := strPayload s1Obj
    let p2 := strPayload s2Obj
    if p2.length = 0 then
      Q (s1, ()) m
    else if strMaxCap ≤ p1.length + p2.length then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let newPayload := p1 ++ p2
      let newLen := (s1Obj.strLen + s2Obj.strLen) % 2 ^ 64
      let inPlace := s1Obj.rc = 1#32 ∧ newPayload.length + 1 ≤ s1Obj.cap
      let newCap :=
        if inPlace then s1Obj.cap else strGrowCap s1Obj.rc s1Obj.cap (newPayload.length + 1)
      let reqBytes := strAllocBytes newCap
      (¬ inPlace → (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
        (s1Obj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound s1 objs)) ∧
      ∀ r st' objs' m',
        r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        (inPlace →
          r = s1 ∧ st' = st ∧
          objs' = objs.map (fun o =>
            if o.addr = s1 then mkStrObj s1 1#32 s1Obj.cap newPayload newLen else o)) →
        (¬ inPlace → ∃ objs1, DecObjRel s1 objs objs1 ∧
          objs' = mkStrObj r 1#32 newCap newPayload newLen :: objs1) →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q (r, ()) m'

def lcnfStringCmpOpSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, op, s1, s2, ()) m Q X =>
    if op = 0#64 ∨ op = 1#64 ∨ op = 2#64 then
      if s1 = s2 then Q (strCmpOpVal op [] [], ()) m
      else
        ∃ (s1Obj s2Obj : LcnfObj) (R : Mem 64 → Prop),
          s1Obj.addr = s1 ∧ StrCanon s1Obj ∧ s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
          (lcnfObjMem s1Obj ⋆ lcnfObjMem s2Obj ⋆ R) m ∧
          Q (strCmpOpVal op (strPayload s1Obj) (strPayload s2Obj), ()) m
    else X "lcnf_panic" [i64, i64] (rt, 1#64, ()) m

def lcnfStringPosOpSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, op, s, idxV, endV, ()) m Q X =>
    ∃ (st : RtC0State) (sObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
      sObj.addr = s ∧ StrCanon sObj ∧
      (op = 1#64 ∧ (idxV &&& 1#64) = 0#64 ∧ idxV ≠ 0#64 →
        ∃ iObj ∈ objs, iObj.addr = idxV ∧ iObj.Wf) ∧
      (∀ o ∈ objs, o.Wf) ∧
      (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m ∧
      let bs := strPayload sObj
      if op = 0#64 ∨ op = 1#64 ∨ op = 2#64 ∨ op = 4#64 ∨ op = 5#64 then
        let objs' := if op = 1#64 then incObjList idxV objs else objs
        ∀ m', (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' →
          Q (strPosOpVal op bs idxV endV, ()) m'
      else if op = 3#64 then
        let b := strPosClamp idxV bs.length
        let e := strPosClamp endV bs.length
        let sub := if b < e then (bs.take e).drop b else []
        let subLen := if b < e then utf8CountFrom (bs.take e) b else 0
        let reqBytes := strAllocBytes (sub.length + 1)
        (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
        ∀ r st' m',
          r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
          let rObj := mkStrObj r 1#32 (sub.length + 1) sub subLen
          StrCanon rObj →
          (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
          Q (r, ()) m'
      else
        X "lcnf_panic" [i64, i64] (rt, 1#64, ()) m

def lcnfStringToListSpec : Spec [i64, i64] [i64] := fun (rt, s, ()) m Q _ =>
  ∃ (st : RtC0State) (sObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    sObj ∈ objs ∧ sObj.addr = s ∧ StrCanon sObj ∧
    (∀ o ∈ objs, o.Wf) ∧
    (sObj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound s objs) ∧
    let bs := strPayload sObj
    let cps := utf8DecodeFrom bs 0
    24 * cps.length ≤ st.rem ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' resObjs objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      ExclListMem res cps resObjs →
      DecObjRel s objs objs' →
      (rtC0Inv rt st' ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'

def lcnfStringMkSpec : Spec [i64, i64] [i64] := fun (rt, cs, ()) m Q X =>
  ∃ (st : RtC0State) (cps : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop),
    IsListInHeap objs cs cps ∧
    (∀ o ∈ objs, o.Wf) ∧
    (cs ≠ 1#64 →
      ∃ o ∈ objs, o.addr = cs ∧
        (o.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound cs objs)) ∧
    let bs := utf8EncodeList cps
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    if strMaxCap ≤ bs.length then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let bytes := strAllocBytes (bs.length + 1)
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      ∀ r st' objs' m',
        r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        let rObj := mkStrObj r 1#32 (bs.length + 1) bs (cps.length % 2 ^ 64)
        StrCanon rObj →
        DecObjRel cs objs objs' →
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (r, ()) m'

def lcnfBaDataSpec : Spec [i64, i64] [i64] := fun (rt, ba, ()) m Q X =>
  ∃ (st : RtC0State) (baObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    baObj ∈ objs ∧ baObj.addr = ba ∧ BaCanon baObj ∧
    (∀ o ∈ objs, o.Wf) ∧
    (baObj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound ba objs) ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    let n := baObj.scalarData.length
    if arrMaxCap < n then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let bytes := arrAllocBytes n
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      ∀ arr st' objs' m',
        arr ≠ 0#64 → arr.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        let elems := baObj.scalarData.map (fun b => boxNat b.toNat)
        let arrObj := mkArrObj arr 1#32 n elems
        ArrCanon arrObj →
        DecObjRel ba objs objs' →
        (rtC0Inv rt st' ⋆ lcnfObjMem arrObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (arr, ()) m'

def lcnfArrayMkSpec : Spec [i64, i64] [i64] := fun (rt, list, ()) m Q X =>
  ∃ (st : RtC0State) (elems : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop),
    IsListInHeap objs list elems ∧
    (∀ o ∈ objs, o.Wf) ∧
    (∀ v ∈ elems, v = 0#64 ∨ (v &&& 1#64) ≠ 0#64 ∨ ∃ o ∈ objs, o.addr = v) ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    if arrMaxCap < elems.length then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let objs1 := incElemsList elems objs
      (list ≠ 1#64 →
        ∃ o ∈ objs1, o.addr = list ∧
          (o.rc = 1#32 → objs1.length ≤ st.workCap ∧ lcnfHeapClosed objs1 ∧ RcSound list objs1)) ∧
      let bytes := arrAllocBytes elems.length
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      ∀ arr st' objs' m',
        arr ≠ 0#64 → arr.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        let arrObj := mkArrObj arr 1#32 elems.length elems
        ArrCanon arrObj →
        DecObjRel list objs1 objs' →
        (rtC0Inv rt st' ⋆ lcnfObjMem arrObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (arr, ()) m'

def lcnfArrayToListSpec : Spec [i64, i64] [i64] := fun (rt, arr, ()) m Q _ =>
  ∃ (st : RtC0State) (arrObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    arrObj ∈ objs ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
    (∀ o ∈ objs, o.Wf) ∧
    (∀ v ∈ arrObj.fields, v = 0#64 ∨ (v &&& 1#64) ≠ 0#64 ∨ ∃ o ∈ objs, o.addr = v) ∧
    let objs1 := incElemsList arrObj.fields.reverse objs
    (∃ o ∈ objs1, o.addr = arr ∧
      (o.rc = 1#32 → objs1.length ≤ st.workCap ∧ lcnfHeapClosed objs1 ∧ RcSound arr objs1)) ∧
    24 * arrObj.fields.length ≤ st.rem ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' resObjs objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      ExclListMem res arrObj.fields resObjs →
      DecObjRel arr objs1 objs' →
      (rtC0Inv rt st' ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'

def lcnfArrayReplicateSpec : Spec [i64, i64, i64] [i64] := fun (rt, n, v, ()) m Q X =>
  if (n &&& 1#64) = 0#64 ∨ arrMaxCap < (n >>> 1).toNat then
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
  else
    let cnt := (n >>> 1).toNat
    let bytes := arrAllocBytes cnt
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (∀ o ∈ objs, o.Wf) ∧
      (cnt = 0 ∧ v ≠ 0#64 ∧ (v &&& 1#64) = 0#64 →
        ∃ o ∈ objs, o.addr = v ∧
          (o.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound v objs)) ∧
      (1 < cnt ∧ v ≠ 0#64 ∧ (v &&& 1#64) = 0#64 →
        ∃ o ∈ objs, o.addr = v ∧
          (o.rc ≠ 0#32 ∧ 2147483647 - o.rc.toNat < cnt - 1 →
            objs.length ≤ st.workCap ∧ lcnfHeapClosed objs)) ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      ∀ arr st' objs' m',
        arr ≠ 0#64 → arr.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        let arrObj := mkArrObj arr 1#32 cnt (List.replicate cnt v)
        ArrCanon arrObj →
        (cnt = 0 → DecObjRel v objs objs') →
        (cnt = 1 → objs' = objs) →
        (1 < cnt →
          if v = 0#64 ∨ (v &&& 1#64) ≠ 0#64 then objs' = objs
          else ∃ o ∈ objs, o.addr = v ∧
            if o.rc = 0#32 ∨ o.rc.toNat + (cnt - 1) ≤ 2147483647 then
              objs' = addRcObjList v (cnt - 1) objs
            else MarkPersistRel v objs objs') →
        (rtC0Inv rt st' ⋆ lcnfObjMem arrObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (arr, ()) m'

def lcnfNatToStrSpec : Spec [i64, i64] [i64] := fun (rt, n, ()) m Q X =>
  ∃ (st : RtC0State) (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
    NatInHeap n val objs ∧
    (∀ o ∈ objs, o.Wf) ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    let dec := natToDecimalBytes val
    if (n &&& 1#64) ≠ 0#64 then
      let bytes := strAllocBytes (dec.length + 1)
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      ∀ s st' m',
        s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
        StrCanon sObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' → Q (s, ()) m'
    else
      ∃ nObj, nObj ∈ objs ∧ nObj.addr = n ∧ MpzCanon nObj ∧
        let cn := trimZeroLimbsLen nObj.limbs nObj.arrSize
        (nObj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound n objs) ∧
        if cn = 0 then
          let bytes := strAllocBytes 2
          (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
          ∀ s st' objs' m',
            s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
            let sObj := mkStrObj s 1#32 2 [UInt8.ofNat 48] 1
            StrCanon sObj → DecObjRel n objs objs' →
            (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m'
        else if mpzMaxLimbsNat < cn then
          X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
        else
          let needRem := mpzAllocBytes cn + sarrayAllocBytes (20 * cn) + strAllocBytes (20 * cn + 1)
          needRem ≤ st.rem ∧
          ∀ s st' objs' m',
            s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
            let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
            StrCanon sObj → DecObjRel n objs objs' →
            (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m'

/-! ## 5. Closed Specification Table (`rtR2bEnv`) -/

def rtR2bSpecEntries : List SpecEntry :=
  [ { name := "r2b_alloc_mpz", as := [i64, i64, i64], rs := [i64], spec := r2bAllocMpzSpec }
  , { name := "r2b_str_alloc_cap", as := [i64, i64, i64, i64], rs := [i64],
      spec := r2bStrAllocCapSpec }
  , { name := "r2b_utf8_len", as := [i64], rs := [i64], spec := r2bUtf8LenSpec }
  , { name := "r2b_utf8_write", as := [i64, i64], rs := [i64], spec := r2bUtf8WriteSpec }
  , { name := "r2b_utf8_decode_step", as := [i64, i64, i64], rs := [i64],
      spec := r2bUtf8DecodeStepSpec }
  , { name := "r2b_utf8_decode_cp", as := [i64, i64, i64], rs := [i64],
      spec := r2bUtf8DecodeCpSpec }
  , { name := "lcnf_str_alloc", as := [i64, i64, i64], rs := [i64], spec := lcnfStrAllocSpec }
  , { name := "lcnf_char_op", as := [i64, i64, i64], rs := [i64], spec := lcnfCharOpSpec }
  , { name := "lcnf_string_push", as := [i64, i64, i64], rs := [i64], spec := lcnfStringPushSpec }
  , { name := "lcnf_string_append", as := [i64, i64, i64], rs := [i64],
      spec := lcnfStringAppendSpec }
  , { name := "lcnf_string_cmp_op", as := [i64, i64, i64, i64], rs := [i64],
      spec := lcnfStringCmpOpSpec }
  , { name := "lcnf_string_pos_op", as := [i64, i64, i64, i64, i64], rs := [i64],
      spec := lcnfStringPosOpSpec }
  , { name := "lcnf_string_to_list", as := [i64, i64], rs := [i64], spec := lcnfStringToListSpec }
  , { name := "lcnf_string_mk", as := [i64, i64], rs := [i64], spec := lcnfStringMkSpec }
  , { name := "lcnf_ba_data", as := [i64, i64], rs := [i64], spec := lcnfBaDataSpec }
  , { name := "lcnf_array_mk", as := [i64, i64], rs := [i64], spec := lcnfArrayMkSpec }
  , { name := "lcnf_array_to_list", as := [i64, i64], rs := [i64], spec := lcnfArrayToListSpec }
  , { name := "lcnf_array_replicate", as := [i64, i64, i64], rs := [i64],
      spec := lcnfArrayReplicateSpec }
  , { name := "lcnf_nat_to_str", as := [i64, i64], rs := [i64], spec := lcnfNatToStrSpec }
  , { name := "lcnf_alloc", as := [i64, i64], rs := [i64], spec := lcnfAllocRemSpec }
  , { name := "lcnf_free_obj", as := [i64, i64], rs := [], spec := lcnfFreeObjSpec }
  , { name := "lcnf_dec_ref_cold", as := [i64, i64], rs := [], spec := lcnfDecRefColdSpec }
  , { name := "lcnf_mark_persistent", as := [i64, i64], rs := [], spec := lcnfMarkPersistentSpec }
  , { name := "r2_inc_obj", as := [i64], rs := [], spec := r2IncObjSpec }
  , { name := "r2_dec_obj", as := [i64, i64], rs := [], spec := r2DecObjSpec }
  , { name := "r2_mem_copy_bytes", as := [i64, i64, i64], rs := [], spec := r2MemCopyBytesSpec }
  , { name := "r2_cmp_byte_slices", as := [i64, i64, i64, i64], rs := [i64],
      spec := r2CmpByteSlicesSpec }
  , { name := "r2_alloc_sarray", as := [i64, i64, i64], rs := [i64], spec := r2AllocSarraySpec }
  , { name := "r2_alloc_array", as := [i64, i64, i64], rs := [i64], spec := r2AllocArraySpec }
  ]

def rtR2bEnv : Env := Env.ofTable rtR2bSpecEntries

theorem rtR2bSpecEntries_nodup : (rtR2bSpecEntries.map SpecEntry.name).Nodup := by
  decide

section EnvLookups

theorem rtR2bEnv_r2_inc_obj {xs m Q X} :
    r2IncObjSpec xs m Q X → rtR2bEnv "r2_inc_obj" [i64] [] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2_inc_obj", [i64], [], r2IncObjSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2_dec_obj {xs m Q X} :
    r2DecObjSpec xs m Q X → rtR2bEnv "r2_dec_obj" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2_dec_obj", [i64, i64], [], r2DecObjSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2_mem_copy_bytes {xs m Q X} :
    r2MemCopyBytesSpec xs m Q X → rtR2bEnv "r2_mem_copy_bytes" [i64, i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2_cmp_byte_slices {xs m Q X} :
    r2CmpByteSlicesSpec xs m Q X →
      rtR2bEnv "r2_cmp_byte_slices" [i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"r2_cmp_byte_slices", [i64, i64, i64, i64], [i64], r2CmpByteSlicesSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2_alloc_sarray {xs m Q X} :
    r2AllocSarraySpec xs m Q X → rtR2bEnv "r2_alloc_sarray" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2_alloc_sarray", [i64, i64, i64], [i64], r2AllocSarraySpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2_alloc_array {xs m Q X} :
    r2AllocArraySpec xs m Q X → rtR2bEnv "r2_alloc_array" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2_alloc_array", [i64, i64, i64], [i64], r2AllocArraySpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_alloc_mpz {xs m Q X} :
    r2bAllocMpzSpec xs m Q X → rtR2bEnv "r2b_alloc_mpz" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2b_alloc_mpz", [i64, i64, i64], [i64], r2bAllocMpzSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_str_alloc_cap {xs m Q X} :
    r2bStrAllocCapSpec xs m Q X →
      rtR2bEnv "r2b_str_alloc_cap" [i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"r2b_str_alloc_cap", [i64, i64, i64, i64], [i64], r2bStrAllocCapSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_utf8_len {xs m Q X} :
    r2bUtf8LenSpec xs m Q X → rtR2bEnv "r2b_utf8_len" [i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2b_utf8_len", [i64], [i64], r2bUtf8LenSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_utf8_write {xs m Q X} :
    r2bUtf8WriteSpec xs m Q X → rtR2bEnv "r2b_utf8_write" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"r2b_utf8_write", [i64, i64], [i64], r2bUtf8WriteSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_utf8_decode_step {xs m Q X} :
    r2bUtf8DecodeStepSpec xs m Q X →
      rtR2bEnv "r2b_utf8_decode_step" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"r2b_utf8_decode_step", [i64, i64, i64], [i64], r2bUtf8DecodeStepSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_r2b_utf8_decode_cp {xs m Q X} :
    r2bUtf8DecodeCpSpec xs m Q X →
      rtR2bEnv "r2b_utf8_decode_cp" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"r2b_utf8_decode_cp", [i64, i64, i64], [i64], r2bUtf8DecodeCpSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_str_alloc {xs m Q X} :
    lcnfStrAllocSpec xs m Q X → rtR2bEnv "lcnf_str_alloc" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_str_alloc", [i64, i64, i64], [i64], lcnfStrAllocSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_char_op {xs m Q X} :
    lcnfCharOpSpec xs m Q X → rtR2bEnv "lcnf_char_op" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_char_op", [i64, i64, i64], [i64], lcnfCharOpSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_push {xs m Q X} :
    lcnfStringPushSpec xs m Q X → rtR2bEnv "lcnf_string_push" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_string_push", [i64, i64, i64], [i64], lcnfStringPushSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_append {xs m Q X} :
    lcnfStringAppendSpec xs m Q X →
      rtR2bEnv "lcnf_string_append" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_string_append", [i64, i64, i64], [i64], lcnfStringAppendSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_cmp_op {xs m Q X} :
    lcnfStringCmpOpSpec xs m Q X →
      rtR2bEnv "lcnf_string_cmp_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_string_cmp_op", [i64, i64, i64, i64], [i64], lcnfStringCmpOpSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_pos_op {xs m Q X} :
    lcnfStringPosOpSpec xs m Q X →
      rtR2bEnv "lcnf_string_pos_op" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_string_pos_op", [i64, i64, i64, i64, i64], [i64], lcnfStringPosOpSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_to_list {xs m Q X} :
    lcnfStringToListSpec xs m Q X → rtR2bEnv "lcnf_string_to_list" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_string_to_list", [i64, i64], [i64], lcnfStringToListSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_string_mk {xs m Q X} :
    lcnfStringMkSpec xs m Q X → rtR2bEnv "lcnf_string_mk" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_string_mk", [i64, i64], [i64], lcnfStringMkSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_ba_data {xs m Q X} :
    lcnfBaDataSpec xs m Q X → rtR2bEnv "lcnf_ba_data" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_ba_data", [i64, i64], [i64], lcnfBaDataSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_array_mk {xs m Q X} :
    lcnfArrayMkSpec xs m Q X → rtR2bEnv "lcnf_array_mk" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_array_mk", [i64, i64], [i64], lcnfArrayMkSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_array_to_list {xs m Q X} :
    lcnfArrayToListSpec xs m Q X → rtR2bEnv "lcnf_array_to_list" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_array_to_list", [i64, i64], [i64], lcnfArrayToListSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_array_replicate {xs m Q X} :
    lcnfArrayReplicateSpec xs m Q X →
      rtR2bEnv "lcnf_array_replicate" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_array_replicate", [i64, i64, i64], [i64], lcnfArrayReplicateSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_nat_to_str {xs m Q X} :
    lcnfNatToStrSpec xs m Q X → rtR2bEnv "lcnf_nat_to_str" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_nat_to_str", [i64, i64], [i64], lcnfNatToStrSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_alloc {xs m Q X} :
    lcnfAllocRemSpec xs m Q X → rtR2bEnv "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_free_obj {xs m Q X} :
    lcnfFreeObjSpec xs m Q X → rtR2bEnv "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_dec_ref_cold {xs m Q X} :
    lcnfDecRefColdSpec xs m Q X → rtR2bEnv "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (e := ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

theorem rtR2bEnv_lcnf_mark_persistent {xs m Q X} :
    lcnfMarkPersistentSpec xs m Q X → rtR2bEnv "lcnf_mark_persistent" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩)
    (by simp [rtR2bSpecEntries]) rtR2bSpecEntries_nodup

end EnvLookups

end LeanQbe.T.LeanLCNF
