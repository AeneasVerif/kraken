module

public import LeanQbe.T.Bedrock2.Phoas
public import LeanQbe.T.Bedrock2.Flat
public import LeanQbe.T.Bedrock2.ToT
public import Kraken.Bedrock2.Semantics
import Kraken.Mem
import LeanQbe.T.ZeroPeelLemmas1

/-!
# `Kraken.Bedrock2` Frontend Translator and Exact `Exec ↔ Cmd.wp` Agreement

Translates first-order `Kraken.Bedrock2` ASTs (`String` locals, `Int` literals,
all `Op1`/`BinOp`, all `AccessSize`s, `inlinetable`, short-circuiting `ite`,
`stackalloc`, `cond`, `seq`, `while`, `call`, `interact`) into verified
`BFlat`/`FuncB` (`LeanQbe.T.Bedrock2`), and proves:

1. `loadVal_sz_eq_load?` and `store?_iff_storeOk_storeMem`: exact 64-bit byte-memory
   agreement between `Kraken.Bedrock2.Memory` and `LeanQbe.T.Logic.Mem`.
2. `Func.fromKraken_wf` / `Func.fromKraken_toFunc_wf`: unconditional `FuncB.Wf` and
   `LeanQbe.T.Func.Wf` via `FuncB.wf_of_denote` and `FuncB.toFunc_wf`.
3. `trCmd_wp_iff_exec` & `Func.fromKraken_wp_iff_exec`: exact bidirectional equivalence
   `FuncB.wp (extToB ext) (EnvB.ofKraken ext e) ↔ Kraken.Bedrock2.Exec ext e`
   over all 10 `Cmd` constructors and all 7 `Expr` constructors.
4. `Func.fromKraken_toFunc_wp_iff` & `Func.fromKraken_toFunc_wp_sound`: full pipeline
   agreement from `Kraken.Bedrock2.Exec` down to `LeanQbe.T.Func.wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bedrock2

open LeanQbe.T
open Kraken.Bedrock2 (AccessSize anybytes split)

/-! ## 1. Register-List / Tuple / Trace / Env Conversions -/

/-- Convert a homogeneous tuple of `n` 64-bit register values to a `List (BitVec 64)`. -/
def tupToList : {n : Nat} → Tup Val (List.replicate n i64) → List (BitVec 64)
  | 0, () => []
  | _ + 1, (v, vs) => v :: tupToList vs

@[simp]
theorem tupToList_length : {n : Nat} → (xs : Tup Val (List.replicate n i64)) →
    (tupToList xs).length = n
  | 0, () => rfl
  | _ + 1, (_, vs) => congrArg Nat.succ (tupToList_length vs)

/-- Convert a `List (BitVec 64)` of length `n` into `Tup Val (List.replicate n i64)`. -/
def listToTup? : (n : Nat) → List (BitVec 64) → Option (Tup Val (List.replicate n i64))
  | 0, [] => some ()
  | n + 1, v :: vs => (listToTup? n vs).map (v, ·)
  | _, _ => none

theorem listToTup?_tupToList : {n : Nat} → (xs : Tup Val (List.replicate n i64)) →
    listToTup? n (tupToList xs) = some xs
  | 0, () => rfl
  | _ + 1, (v, vs) => by simp [tupToList, listToTup?, listToTup?_tupToList vs]

theorem tupToList_listToTup? : {n : Nat} → {vs : List (BitVec 64)} →
    {xs : Tup Val (List.replicate n i64)} →
    listToTup? n vs = some xs → tupToList xs = vs
  | 0, [], (), _ => rfl
  | 0, _ :: _, _, h => by simp [listToTup?] at h
  | n + 1, [], _, h => by simp [listToTup?] at h
  | n + 1, v :: vs, (x, xs), h => by
      simp only [listToTup?, Option.map_eq_some_iff] at h
      rcases h with ⟨xs', hxs', hpair⟩
      have hv : v = x := by cases hpair; rfl
      have hxs : xs' = xs := by cases hpair; rfl
      subst hv; subst hxs
      exact congrArg (v :: ·) (tupToList_listToTup? hxs')

theorem exists_listToTup?_of_length : {n : Nat} → {vs : List (BitVec 64)} →
    vs.length = n → ∃ xs : Tup Val (List.replicate n i64), listToTup? n vs = some xs
  | 0, [], _ => ⟨(), rfl⟩
  | n + 1, v :: vs, h => by
      have ⟨xs, hxs⟩ := exists_listToTup?_of_length (Nat.succ.inj h)
      exact ⟨(v, xs), by simp [listToTup?, hxs]⟩

/-- Convert a `List (BitVec 64)` into `Tup Val (List.replicate vs.length i64)`. -/
def listToTup : (vs : List (BitVec 64)) → Tup Val (List.replicate vs.length i64)
  | [] => ()
  | v :: vs => (v, listToTup vs)

@[simp]
theorem tupToList_listToTup (vs : List (BitVec 64)) : tupToList (listToTup vs) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [listToTup, tupToList, ih]

theorem tupToList_inj : {n : Nat} → {xs ys : Tup Val (List.replicate n i64)} →
    tupToList xs = tupToList ys → xs = ys
  | 0, (), (), _ => rfl
  | _ + 1, (x, xs), (y, ys), h => by
      simp only [tupToList, List.cons.injEq] at h
      obtain ⟨rfl, hr⟩ := h
      exact congrArg (x, ·) (tupToList_inj hr)

/-- Extract a `List (BitVec 64)` from `Tup Val ts` when all types equal `i64`. -/
def extTupToList? : {ts : List Ty} → Tup Val ts → Option (List (BitVec 64))
  | [], () => some []
  | .bits w :: _, (v, vs) =>
      if h : w = 64 then (extTupToList? vs).map ((h ▸ v) :: ·) else none
  | _ :: _, _ => none

@[simp]
theorem extTupToList?_replicate : {n : Nat} → (xs : Tup Val (List.replicate n i64)) →
    extTupToList? xs = some (tupToList xs)
  | 0, () => rfl
  | _ + 1, (v, vs) => by
      simp only [List.replicate_succ, i64, extTupToList?, ↓reduceDIte,
        extTupToList?_replicate vs, Option.map_some, tupToList]

/-- Inject a `List (BitVec 64)` into `Tup Val ts` when `ts` consists solely of `i64`. -/
def extListToTup? : (ts : List Ty) → List (BitVec 64) → Option (Tup Val ts)
  | [], [] => some ()
  | .bits 64 :: ts, v :: vs => (extListToTup? ts vs).map (v, ·)
  | _, _ => none

@[simp]
theorem extListToTup?_replicate (n : Nat) (vs : List (BitVec 64)) :
    extListToTup? (List.replicate n i64) vs = listToTup? n vs := by
  induction n generalizing vs with
  | zero => cases vs <;> rfl
  | succ n ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
          simp only [List.replicate_succ, i64, extListToTup?, ih, listToTup?]

theorem extTupToList?_some_replicate {ts : List Ty} {args : Tup Val ts}
    {vs : List (BitVec 64)} (h : extTupToList? args = some vs) :
    ts = List.replicate vs.length i64 := by
  induction ts generalizing vs with
  | nil =>
      cases args
      simp only [extTupToList?, Option.some.injEq] at h
      subst h; rfl
  | cons t ts ih =>
      cases t with
      | bits w =>
          rcases args with ⟨a, as⟩
          by_cases hw : w = 64
          · subst hw
            simp only [extTupToList?, ↓reduceDIte, Option.map_eq_some_iff] at h
            rcases h with ⟨rest, hr, rfl⟩
            exact congrArg (i64 :: ·) (ih hr)
          · simp [extTupToList?, hw] at h
      | bool | float _ | pair _ _ => simp [extTupToList?] at h

/-- Convert a `Kraken.Bedrock2.LogItem 64` into a typed `LogItemB`. -/
def logItemToB (li : Kraken.Bedrock2.LogItem 64) : LogItemB :=
  let ((mGive, action, args), mReceive, rets) := li
  ⟨List.replicate args.length i64, List.replicate rets.length i64, mGive, action,
    listToTup args, mReceive, listToTup rets⟩

/-- Convert a typed `LogItemB` back into `Kraken.Bedrock2.LogItem 64` when `i64`-homogeneous. -/
def logItemFromB? (li : LogItemB) : Option (Kraken.Bedrock2.LogItem 64) := do
  let args ← extTupToList? li.args
  let rets ← extTupToList? li.rets
  pure ((li.mGive, li.action, args), li.mReceive, rets)

/-- Convert a `Kraken.Bedrock2.Trace 64` into a `TraceB`. -/
def traceToB : Kraken.Bedrock2.Trace 64 → TraceB :=
  List.map logItemToB

/-- Convert a `TraceB` back into a `Kraken.Bedrock2.Trace 64`. -/
def traceFromB? : TraceB → Option (Kraken.Bedrock2.Trace 64) :=
  List.mapM logItemFromB?

@[simp]
theorem traceFromB?_nil : traceFromB? [] = some [] := rfl

@[simp]
theorem traceFromB?_cons (li : LogItemB) (tb : TraceB) :
    traceFromB? (li :: tb) =
      (do let li' ← logItemFromB? li; let t' ← traceFromB? tb; pure (li' :: t')) := by
  simp [traceFromB?, List.mapM_cons]

theorem logItemFromB?_logItemToB (li : Kraken.Bedrock2.LogItem 64) :
    logItemFromB? (logItemToB li) = some li := by
  rcases li with ⟨⟨mGive, action, args⟩, mReceive, rets⟩
  simp [logItemFromB?, logItemToB, extTupToList?_replicate]

@[simp]
theorem traceFromB?_traceToB (t : Kraken.Bedrock2.Trace 64) :
    traceFromB? (traceToB t) = some t := by
  induction t with
  | nil => rfl
  | cons li t ih =>
      simp only [traceToB, List.map_cons, traceFromB?_cons, logItemFromB?_logItemToB,
        Option.pure_def]
      rw [show traceFromB? (List.map logItemToB t) = some t from ih]
      rfl

theorem logItemFromB?_mk (mGive : Mem 64) (action : String) (nArgs nRets : Nat)
    (argTup : Tup Val (List.replicate nArgs i64)) (mRec : Mem 64)
    (resTup : Tup Val (List.replicate nRets i64)) :
    logItemFromB? ⟨List.replicate nArgs i64, List.replicate nRets i64, mGive, action,
      argTup, mRec, resTup⟩ =
      some ((mGive, action, tupToList argTup), mRec, tupToList resTup) := by
  simp [logItemFromB?]

/-- Lift a `Kraken.Bedrock2.ExtSpec 64` to an `ExtSpecB` agreeing on all `i64` interactions. -/
def extToB (ext : Kraken.Bedrock2.ExtSpec 64) : ExtSpecB :=
  fun tb mGive action _as bs args midB =>
    ∃ (t : Kraken.Bedrock2.Trace 64) (argList : List (BitVec 64))
      (mid : Mem 64 → List (BitVec 64) → Prop),
      traceFromB? tb = some t ∧
      extTupToList? args = some argList ∧
      ext t mGive action argList mid ∧
      (∀ mRec resvals, mid mRec resvals →
        ∃ (resTup : Tup Val bs), extTupToList? resTup = some resvals ∧ midB mRec resTup)

/-- Lift a `Kraken.Bedrock2.Env` directly into an `EnvB` using `Kraken.Bedrock2.Exec`. -/
def EnvB.ofKraken (ext : Kraken.Bedrock2.ExtSpec 64) (e : Kraken.Bedrock2.Env) : EnvB :=
  fun fname _as bs B args tb m P =>
    ∃ (f : Kraken.Bedrock2.Func) (t : Kraken.Bedrock2.Trace 64)
      (argList : List (BitVec 64)) (lf : Kraken.Bedrock2.Locals 64)
      (mid : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop),
      List.lookup fname e = some f ∧
      traceFromB? tb = some t ∧
      extTupToList? args = some argList ∧
      Kraken.Bedrock2.putManyZip f.params argList ∅ = some lf ∧
      Kraken.Bedrock2.Exec ext e B f.body t m lf mid ∧
      (∀ t' m' st1, mid t' m' st1 →
        ∃ (retvs : List (BitVec 64)) (resTup : Tup Val bs),
          Kraken.Bedrock2.getMany st1 f.rets = some retvs ∧
          extTupToList? resTup = some retvs ∧
          P resTup (traceToB t') m')

/-! ## 2. Exact 64-Bit Byte-Memory & BitVec Arithmetic Equivalence -/

/-- `Ty` corresponding to a Bedrock2 `AccessSize`. -/
def accessTy (sz : AccessSize) : Ty := .bits (8 * sz.bytes)

theorem accessTy_bytes (sz : AccessSize) : (accessTy sz).bytes = sz.bytes := by
  cases sz <;> rfl

theorem accessSize_pos (sz : AccessSize) : 0 < sz.bytes := by
  cases sz <;> decide

theorem accessSize_le8 (sz : AccessSize) : sz.bytes ≤ 8 := by
  cases sz <;> decide

private theorem pow256_eq_pow2 (n : Nat) : (256 : Int) ^ n = (2 : Int) ^ (8 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        (256 : Int) ^ (n + 1) = (256 : Int) ^ n * 256 := Int.pow_succ ..
        _ = (2 : Int) ^ (8 * n) * (2 : Int) ^ 8 := by rw [ih]; rfl
        _ = (2 : Int) ^ (8 * n + 8) := (Int.pow_add 2 (8 * n) 8).symm
        _ = (2 : Int) ^ (8 * (n + 1)) := by rw [Nat.mul_succ]

theorem loadVal_sz_eq_load? (sz : AccessSize) (m : Mem 64) (a : BitVec 64) :
    (loadVal m (accessTy sz) a).map (fun v => BitVec.setWidth 64 v) =
      Kraken.Bedrock2.load? sz m a := by
  dsimp only [loadVal, ofBits, Kraken.Bedrock2.load?]
  rw [accessTy_bytes]
  dsimp only [accessTy]
  cases hli : m.loadInt a sz.bytes with
  | none => rfl
  | some z =>
      have hok : storeOk m (accessTy sz) a := ⟨z, by rw [accessTy_bytes]; exact hli⟩
      have hall := (ZeroPeel.storeOk_iff_forall_mem m (accessTy sz) a).1 hok
      rw [accessTy_bytes] at hall
      have hsz : sz.bytes ≤ 2 ^ 64 := by cases sz <;> decide
      obtain ⟨bs, mRest, hlen, _, hsp⟩ := mem_split_At m a sz.bytes hsz fun i hi => by
        simpa [Std.ExtHashMap.get?_eq_getElem?] using hall i hi
      have hli2 := Mem.loadInt_sep bs a sz.bytes (Eq mRest) m (split_iff_sep.1 hsp) hlen hsz
      have hz : z = Int.ofBytes bs := Option.some.inj (hli.symm.trans hli2)
      subst hz
      simp only [Option.map_some, Option.bind_some]
      congr 1
      have hge0 : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
      have hlt : Int.ofBytes bs < (2 : Int) ^ (8 * sz.bytes) := by
        have h1 := Int.ofBytes_lt bs
        rw [hlen, pow256_eq_pow2] at h1
        exact h1
      have hlt64 : Int.ofBytes bs < (2 : Int) ^ 64 := by
        have hp : (2 : Int) ^ (8 * sz.bytes) ≤ (2 : Int) ^ 64 := by
          cases sz <;> decide
        exact Int.lt_of_lt_of_le hlt hp
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
      have hm1 : Int.ofBytes bs % ↑((2 : Nat) ^ (8 * sz.bytes)) = Int.ofBytes bs :=
        Int.emod_eq_of_lt hge0 (by simpa [Int.natCast_pow] using hlt)
      have hm2 : Int.ofBytes bs % ↑((2 : Nat) ^ 64) = Int.ofBytes bs :=
        Int.emod_eq_of_lt hge0 (by simpa [Int.natCast_pow] using hlt64)
      rw [hm1, hm2]
      have hmod : (Int.ofBytes bs).toNat < 2 ^ 64 := by
        have hlt' : Int.ofBytes bs < (2 ^ 64 : Nat) := by simpa using hlt64
        omega
      exact Nat.mod_eq_of_lt hmod

theorem loadVal_eight_eq_load? (m : Mem 64) (a : BitVec 64) :
    loadVal m i64 a = Kraken.Bedrock2.load? .eight m a := by
  have h := loadVal_sz_eq_load? .eight m a
  dsimp only [accessTy, AccessSize.bytes] at h
  have hset : (fun v : BitVec 64 => BitVec.setWidth 64 v) = id :=
    funext fun v => BitVec.eq_of_toNat_eq (by simp)
  rw [hset] at h
  simpa [i64] using h

theorem store?_iff_storeOk_storeMem (sz : AccessSize) (m : Mem 64) (a v : BitVec 64)
    (m' : Mem 64) :
    Kraken.Bedrock2.store? sz m a v = some m' ↔
      storeOk m (accessTy sz) a ∧
        m' = storeMem m (accessTy sz) a (BitVec.setWidth (8 * sz.bytes) v) := by
  have hsz : sz.bytes ≤ 2 ^ 64 := by cases sz <;> decide
  have hbytes : Int.toBytes sz.bytes (v.toNat : Int) =
      Int.toBytes sz.bytes
        (BitVec.setWidth (8 * sz.bytes)
          (toBits (Ty.bits (8 * sz.bytes)) (BitVec.setWidth (8 * sz.bytes) v))).toInt := by
    have htb : toBits (Ty.bits (8 * sz.bytes)) (BitVec.setWidth (8 * sz.bytes) v) =
        BitVec.setWidth (8 * sz.bytes) v := rfl
    have hsw : BitVec.setWidth (8 * sz.bytes) (BitVec.setWidth (8 * sz.bytes) v) =
        BitVec.setWidth (8 * sz.bytes) v := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [htb, hsw, ← Int.toBytes_emod sz.bytes (v.toNat : Int),
      ← Int.toBytes_emod sz.bytes (BitVec.setWidth (8 * sz.bytes) v).toInt]
    congr 1
    simp only [Int.take, BitVec.toInt_setWidth]
    exact (Int.bmod_emod).symm
  have hstoreEq : ∀ (bs : List UInt8) (mRest : Mem 64), bs.length = sz.bytes →
      split m (bs.At a) mRest →
      m.storeInt a sz.bytes (v.toNat : Int) =
        storeMem m (accessTy sz) a (BitVec.setWidth (8 * sz.bytes) v) := by
    intro bs mRest hlen hsp
    have hsep := split_iff_sep.1 hsp
    have h1 := Mem.storeInt_sep a sz.bytes bs (Eq mRest) m ⟨hsep, hlen⟩ (v.toNat : Int)
    have h2 : (Eq ((Int.toBytes sz.bytes (v.toNat : Int)).At a) ⋆ Eq mRest)
        (storeMem m (accessTy sz) a (BitVec.setWidth (8 * sz.bytes) v)) := by
      dsimp only [storeMem]; rw [accessTy_bytes]; dsimp only [accessTy]
      rw [hbytes]
      exact Mem.storeInt_sep a sz.bytes bs (Eq mRest) m ⟨hsep, hlen⟩ _
    exact (split_iff_sep.2 h1).1.symm.trans (split_iff_sep.2 h2).1
  dsimp only [Kraken.Bedrock2.store?]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨bs, hlb, rfl⟩
    obtain ⟨bs', mRest, hlen, _, hsp⟩ := mem_split_At m a sz.bytes hsz fun i hi => by
      rw [Std.ExtHashMap.mem_iff_isSome_getElem?.mp (Mem.mem_of_loadBytes hlb hi)]
    refine ⟨⟨Int.ofBytes bs', ?_⟩, hstoreEq bs' mRest hlen hsp⟩
    rw [accessTy_bytes]
    exact Mem.loadInt_sep bs' a sz.bytes (Eq mRest) m (split_iff_sep.1 hsp) hlen hsz
  · rintro ⟨hok, rfl⟩
    have hall := (ZeroPeel.storeOk_iff_forall_mem m (accessTy sz) a).1 hok
    rw [accessTy_bytes] at hall
    obtain ⟨bs', mRest, hlen, _, hsp⟩ := mem_split_At m a sz.bytes hsz fun i hi => by
      simpa [Std.ExtHashMap.get?_eq_getElem?] using hall i hi
    exact ⟨bs', Mem.loadBytes_sep bs' a sz.bytes (Eq mRest) m (split_iff_sep.1 hsp) hlen hsz,
      hstoreEq bs' mRest hlen hsp⟩

theorem exists_lt_of_load?_listAt {sz : AccessSize} {t : List UInt8} {idx v : BitVec 64}
    (h : Kraken.Bedrock2.load? sz (t.At 0) idx = some v) :
    ∃ j < t.length, idx = BitVec.ofNat 64 j := by
  simp only [Kraken.Bedrock2.load?, Option.map_eq_some_iff] at h
  rcases h with ⟨i, hi, _⟩
  have hok : storeOk (t.At 0) (accessTy sz) idx := ⟨i, by rw [accessTy_bytes]; exact hi⟩
  have hall := (ZeroPeel.storeOk_iff_forall_mem (t.At 0) (accessTy sz) idx).1 hok
  have h0 := hall 0 (by rw [accessTy_bytes]; exact accessSize_pos sz)
  rw [BitVec.add_zero, Std.ExtHashMap.get?_eq_getElem?,
    ← Std.ExtHashMap.mem_iff_isSome_getElem?] at h0
  rcases (mem_At_iff t 0 idx).1 h0 with ⟨j, hj, heq⟩
  exact ⟨j, hj, by simpa using heq⟩

theorem shamt64_eq (b : BitVec 64) : Kraken.Bedrock2.shamt b = b.toNat % 64 := rfl

/-! ## 3. Translator from `Kraken.Bedrock2` into `BFlat` & `FuncB` -/

/-- Active variable stack tracking Bedrock2 locals aligned 1-to-1 with `BFlat` stack slots.
Index `0` is the top of the `BFlat` stack; `none` denotes an anonymous/dead/shadowed slot. -/
abbrev B2Ctx := List (Option String)

/-- Replace all active occurrences of `x` in `ctx` with `none`, preserving length. -/
def B2Ctx.shadow (x : String) : B2Ctx → B2Ctx
  | [] => []
  | some y :: rest => (if y == x then none else some y) :: shadow x rest
  | none :: rest => none :: shadow x rest

@[simp]
theorem B2Ctx.shadow_length (x : String) (ctx : B2Ctx) :
    (ctx.shadow x).length = ctx.length := by
  induction ctx with
  | nil => rfl
  | cons o rest ih => cases o <;> simp [B2Ctx.shadow, ih]

/-- Push a new binding of `x` onto `ctx`, shadowing any older slot for `x`. -/
def B2Ctx.bind1 (x : String) (ctx : B2Ctx) : B2Ctx :=
  some x :: ctx.shadow x

@[simp]
theorem B2Ctx.bind1_length (x : String) (ctx : B2Ctx) :
    (ctx.bind1 x).length = ctx.length + 1 := by
  simp [B2Ctx.bind1]

/-- Push a list of bindings left-to-right onto `ctx` (matching `pushTup` and `insertMany`). -/
def B2Ctx.bindMany (xs : List String) (ctx : B2Ctx) : B2Ctx :=
  xs.foldl (fun c x => c.bind1 x) ctx

@[simp]
theorem B2Ctx.bindMany_nil (ctx : B2Ctx) : B2Ctx.bindMany [] ctx = ctx := rfl

@[simp]
theorem B2Ctx.bindMany_cons (x : String) (xs : List String) (ctx : B2Ctx) :
    B2Ctx.bindMany (x :: xs) ctx = B2Ctx.bindMany xs (ctx.bind1 x) := rfl

@[simp]
theorem B2Ctx.bindMany_length (xs : List String) (ctx : B2Ctx) :
    (B2Ctx.bindMany xs ctx).length = ctx.length + xs.length := by
  induction xs generalizing ctx with
  | nil => simp
  | cons x xs ih =>
      simp only [B2Ctx.bindMany_cons, ih, B2Ctx.bind1_length, List.length_cons]
      omega

/-- Anonymous dead stack prefix of length `n`. -/
def deadCtx (n : Nat) : B2Ctx := List.replicate n none

@[simp]
theorem deadCtx_length (n : Nat) : (deadCtx n).length = n := List.length_replicate

/-- Find the de Bruijn index of `some x` in `ctx`, if present. -/
def lookupCtx (ctx : B2Ctx) (x : String) : Option Nat :=
  match ctx with
  | [] => none
  | some y :: rest => if y == x then some 0 else (lookupCtx rest x).map (· + 1)
  | none :: rest => (lookupCtx rest x).map (· + 1)

/-- Ordered list of currently live variable names in `ctx` (oldest first, duplicate-free when
constructed via `bind1`/`shadow`). -/
def B2Ctx.liveVars (ctx : B2Ctx) : List String :=
  (ctx.filterMap id).reverse

/-- Gather `BFlat` operands `.var idx` for a list of Bedrock2 variable names. -/
def gatherVars (ctx : B2Ctx) : (vs : List String) →
    Option (Tup (Arg K) (List.replicate vs.length i64))
  | [] => some ()
  | x :: xs => do
      let idx ← lookupCtx ctx x
      let rest ← gatherVars ctx xs
      pure (.var idx, rest)

/-- Build `(.var (m - 1), ..., .var 0, ())` reading the top `m` stack slots in push order. -/
def revVars : (m : Nat) → Tup (Arg K) (List.replicate m i64)
  | 0 => ()
  | m + 1 => (.var m, revVars m)

/-- Finite decision tree lowering `inlinetable sz t` against index variable `idxVar`. -/
def inlineTableChain (sz : AccessSize) (t : List UInt8) : Nat → Nat → BFlat [i64]
  | _, 0 => .hlt
  | idxVar, n + 1 =>
      match Kraken.Bedrock2.load? sz (t.At 0) (BitVec.ofNat 64 n) with
      | none => inlineTableChain sz t idxVar n
      | some v =>
          .let_ ⟨.cmp .eq i64, (.var idxVar, .imm (BitVec.ofNat 64 n), ())⟩
            (.cond (.var 0) (.ret (.imm v, ())) (inlineTableChain sz t (idxVar + 1) n))

/-- Helper translating a unary `Op1` on top-of-stack operand `.var 0` to `BFlat [i64]`. -/
def trOp1 : Kraken.Bedrock2.Op1 → BFlat [i64]
  | .not => .let_ ⟨.not i64, (.var 0, ())⟩ (.ret (.var 0, ()))
  | .opp => .let_ ⟨.neg i64, (.var 0, ())⟩ (.ret (.var 0, ()))

/-- Helper translating a binary `BinOp` on `.var 1` (lhs) and `.var 0` (rhs) to `BFlat [i64]`. -/
def trBinop : Kraken.Bedrock2.BinOp → BFlat [i64]
  | .add => .let_ ⟨.add i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .sub => .let_ ⟨.sub i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .mul => .let_ ⟨.mul i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .mulhuu => .let_ ⟨.umulw 64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .divu =>
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩
        (.cond (.var 0)
          (.ret (.imm (BitVec.allOnes 64), ()))
          (.let_ ⟨.udiv 64, (.var 2, .var 1, ())⟩ (.ret (.var 0, ()))))
  | .remu =>
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩
        (.cond (.var 0)
          (.ret (.var 2, ()))
          (.let_ ⟨.urem 64, (.var 2, .var 1, ())⟩ (.ret (.var 0, ()))))
  | .and => .let_ ⟨.and i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .or => .let_ ⟨.or i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .xor => .let_ ⟨.xor i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .sru => .let_ ⟨.lshr i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .slu => .let_ ⟨.shl i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .srs => .let_ ⟨.ashr i64, (.var 1, .var 0, ())⟩ (.ret (.var 0, ()))
  | .lts =>
      .let_ ⟨.cmp .slt i64, (.var 1, .var 0, ())⟩
        (.let_ ⟨.ofBool 64, (.var 0, ())⟩ (.ret (.var 0, ())))
  | .ltu =>
      .let_ ⟨.cmp .ult i64, (.var 1, .var 0, ())⟩
        (.let_ ⟨.ofBool 64, (.var 0, ())⟩ (.ret (.var 0, ())))
  | .eq =>
      .let_ ⟨.cmp .eq i64, (.var 1, .var 0, ())⟩
        (.let_ ⟨.ofBool 64, (.var 0, ())⟩ (.ret (.var 0, ())))

/-- Translate a `Kraken.Bedrock2.Expr` under `ctx` into `BFlat [i64]`. -/
def trExpr (ctx : B2Ctx) : Kraken.Bedrock2.Expr → Option (BFlat [i64])
  | .literal v => some (.ret (.imm (BitVec.ofInt 64 v), ()))
  | .var x => do
      let idx ← lookupCtx ctx x
      pure (.ret (.var idx, ()))
  | .load sz addr => do
      let bfAddr ← trExpr ctx addr
      match sz with
      | .eight =>
          pure (.seq [i64] bfAddr (.load i64 (.var 0) (.ret (.var 0, ()))))
      | _ =>
          let bits := 8 * sz.bytes
          pure (.seq [i64] bfAddr
            (.load (.bits bits) (.var 0)
              (.let_ ⟨.zext bits 64, (.var 0, ())⟩ (.ret (.var 0, ())))))
  | .inlinetable sz tbl index => do
      let bfIdx ← trExpr ctx index
      pure (.seq [i64] bfIdx (inlineTableChain sz tbl 0 tbl.length))
  | .op1 o e => do
      let bf ← trExpr ctx e
      pure (.seq [i64] bf (trOp1 o))
  | .op o e1 e2 => do
      let bf1 ← trExpr ctx e1
      let bf2 ← trExpr (none :: ctx) e2
      pure (.seq [i64] bf1 (.seq [i64] bf2 (trBinop o)))
  | .ite c e1 e2 => do
      let bfC ← trExpr ctx c
      let bf1 ← trExpr (none :: none :: ctx) e1
      let bf2 ← trExpr (none :: none :: ctx) e2
      pure (.seq [i64] bfC
        (.let_ ⟨.cmp .ne i64, (.var 0, .imm 0#64, ())⟩
          (.cond (.var 0) bf1 bf2)))

/-- Translate a list of argument expressions sequentially into `BFlat (replicate es.length i64)`. -/
def trArgs (ctx : B2Ctx) : (es : List Kraken.Bedrock2.Expr) →
    Option (BFlat (List.replicate es.length i64))
  | [] => some (.ret ())
  | e :: es => do
      let bfE ← trExpr ctx e
      let bfRest ← trArgs (none :: ctx) es
      pure (.seq [i64] bfE
        (.seq (List.replicate es.length i64) bfRest
          (.ret (revVars (es.length + 1)))))

/-- Output signature and lowered `BFlat` body produced by `trCmd`. -/
abbrev CmdLowerRes := (varsOut : List String) × BFlat (List.replicate varsOut.length i64)

theorem filter_length_eq_imp_forall {α : Type} (p : α → Bool) :
    (xs : List α) → (xs.filter p).length = xs.length → ∀ x ∈ xs, p x = true
  | [], _, _, h => nomatch h
  | y :: xs, hlen, x, hx => by
      by_cases hy : p y = true
      · simp only [List.filter_cons, hy, ↓reduceIte, List.length_cons, Nat.succ.injEq] at hlen
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hy
        · exact filter_length_eq_imp_forall p xs hlen x hx'
      · have hbf : p y = false := Bool.eq_false_iff.mpr hy
        simp only [List.filter_cons, hbf, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
        have hle := List.length_filter_le p xs
        omega

/-- Bounded-fuel structural helper computing the greatest-fixed-point loop invariant. -/
def whileLoopInvAux (trBody : B2Ctx → Option CmdLowerRes) (deadLen : Nat) :
    Nat → (inv : List String) →
    Option ((varsInv : List String) ×
      (res : CmdLowerRes) ×
      PLift (∀ x, x ∈ varsInv → x ∈ res.1))
  | fuel, inv =>
      match trBody (B2Ctx.bindMany inv (deadCtx deadLen)) with
      | none => none
      | some res =>
          if h : (inv.filter (· ∈ res.1)).length < inv.length then
            match fuel with
            | 0 => none
            | fuel' + 1 => whileLoopInvAux trBody deadLen fuel' (inv.filter (· ∈ res.1))
          else
            have hlen : (inv.filter (· ∈ res.1)).length = inv.length :=
              Nat.le_antisymm (List.length_filter_le _ _) (Nat.not_lt.mp h)
            have hsub : ∀ x, x ∈ inv → x ∈ res.1 := fun x hx =>
              of_decide_eq_true (filter_length_eq_imp_forall _ inv hlen x hx)
            pure ⟨inv, res, ⟨hsub⟩⟩

/-- Compute the greatest-fixed-point loop-invariant variable list `inv ⊆ varsBody` by
shrinking `inv` monotonically until every variable in `inv` stays initialized after `body`. -/
def whileLoopInv (trBody : B2Ctx → Option CmdLowerRes) (deadLen : Nat)
    (inv : List String) :
    Option ((varsInv : List String) ×
      (res : CmdLowerRes) ×
      PLift (∀ x, x ∈ varsInv → x ∈ res.1)) :=
  whileLoopInvAux trBody deadLen inv.length inv

/-- Translate a `Kraken.Bedrock2.Cmd` under `ctx`, returning live output vars + `BFlat`. -/
def trCmd (ctx : B2Ctx) : Kraken.Bedrock2.Cmd → Option CmdLowerRes
  | .skip => do
      let out := ctx.liveVars
      let g ← gatherVars ctx out
      pure ⟨out, .ret g⟩
  | .set x rhs => do
      let bfRhs ← trExpr ctx rhs
      let ctx' := ctx.bind1 x
      let out := ctx'.liveVars
      let g ← gatherVars ctx' out
      pure ⟨out, .seq [i64] bfRhs (.ret g)⟩
  | .unset x => do
      let ctx' := ctx.shadow x
      let out := ctx'.liveVars
      let g ← gatherVars ctx' out
      pure ⟨out, .ret g⟩
  | .store sz ea ev => do
      let bfA ← trExpr ctx ea
      let bfV ← trExpr (none :: ctx) ev
      let out := ctx.liveVars
      match sz with
      | .eight => do
          let g ← gatherVars (none :: none :: ctx) out
          pure ⟨out, .seq [i64] bfA (.seq [i64] bfV
            (.store (t := i64) (.var 0) (.var 1) (.ret g)))⟩
      | _ => do
          let bits := 8 * sz.bytes
          let g ← gatherVars (none :: none :: none :: ctx) out
          pure ⟨out, .seq [i64] bfA (.seq [i64] bfV
            (.let_ ⟨.trunc 64 bits, (.var 0, ())⟩
              (.store (t := .bits bits) (.var 0) (.var 2) (.ret g))))⟩
  | .stackalloc x nbytes body => do
      let ⟨out, bfBody⟩ ← trCmd (ctx.bind1 x) body
      pure ⟨out, .stackalloc nbytes bfBody⟩
  | .seq c1 c2 => do
      let ⟨vars1, bf1⟩ ← trCmd ctx c1
      let ctx2 := B2Ctx.bindMany vars1 (deadCtx ctx.length)
      let ⟨vars2, bf2⟩ ← trCmd ctx2 c2
      pure ⟨vars2, .seq (List.replicate vars1.length i64) bf1 bf2⟩
  | .cond ec c1 c2 => do
      let bfC ← trExpr ctx ec
      let ctxBr := none :: none :: ctx
      let ⟨vars1, bf1⟩ ← trCmd ctxBr c1
      let ⟨vars2, bf2⟩ ← trCmd ctxBr c2
      let out := vars1.filter (· ∈ vars2)
      let g1 ← gatherVars (B2Ctx.bindMany vars1 (deadCtx ctxBr.length)) out
      let g2 ← gatherVars (B2Ctx.bindMany vars2 (deadCtx ctxBr.length)) out
      let bf1' := BFlat.seq (List.replicate vars1.length i64) bf1 (.ret g1)
      let bf2' := BFlat.seq (List.replicate vars2.length i64) bf2 (.ret g2)
      pure ⟨out, .seq [i64] bfC
        (.let_ ⟨.cmp .ne i64, (.var 0, .imm 0#64, ())⟩
          (.cond (.var 0) bf1' bf2'))⟩
  | .while ec body => do
      let ⟨inv, ⟨varsBody, bfBodyRaw⟩, _⟩ ←
        whileLoopInv (fun c => trCmd c body) ctx.length ctx.liveVars
      let ctxLoop := B2Ctx.bindMany inv (deadCtx ctx.length)
      let init ← gatherVars ctx inv
      let bfEc ← trExpr ctxLoop ec
      let bfTest : BFlat [.bool] :=
        .seq [i64] bfEc (.let_ ⟨.cmp .ne i64, (.var 0, .imm 0#64, ())⟩ (.ret (.var 0, ())))
      let gBody ← gatherVars (B2Ctx.bindMany varsBody (deadCtx ctxLoop.length)) inv
      let bfBody := BFlat.seq (List.replicate varsBody.length i64) bfBodyRaw (.ret gBody)
      let gExit ← gatherVars ctxLoop inv
      pure ⟨inv, .while_ (List.replicate inv.length i64) init bfTest bfBody (.ret gExit)⟩
  | .call binds fname arges => do
      let bfArgs ← trArgs ctx arges
      let deadBase := deadCtx (ctx.length + arges.length)
      let ctxAfter := B2Ctx.bindMany binds deadBase
      let out := ctxAfter.liveVars
      let g ← gatherVars ctxAfter out
      pure ⟨out, .seq (List.replicate arges.length i64) bfArgs
        (.call fname (List.replicate binds.length i64) (revVars arges.length) (.ret g))⟩
  | .interact binds action arges => do
      let bfArgs ← trArgs ctx arges
      let deadBase := deadCtx (ctx.length + arges.length)
      let ctxAfter := B2Ctx.bindMany binds deadBase
      let out := ctxAfter.liveVars
      let g ← gatherVars ctxAfter out
      pure ⟨out, .seq (List.replicate arges.length i64) bfArgs
        (.interact action (List.replicate binds.length i64) (revVars arges.length) (.ret g))⟩

/-- Translate a closed `Kraken.Bedrock2.Func` into `BFlat (List.replicate f.rets.length i64)`. -/
def Func.toBFlat? (f : Kraken.Bedrock2.Func) :
    Option (BFlat (List.replicate f.rets.length i64)) := do
  let ctx0 := B2Ctx.bindMany f.params []
  let ⟨outVars, bfBody⟩ ← trCmd ctx0 f.body
  let gRet ← gatherVars (B2Ctx.bindMany outVars (deadCtx ctx0.length)) f.rets
  pure (.seq (List.replicate outVars.length i64) bfBody (.ret gRet))

/-- Translate a closed `Kraken.Bedrock2.Func` into typed PHOAS `FuncB`. -/
def Func.fromKraken (f : Kraken.Bedrock2.Func) :
    Option (FuncB (List.replicate f.params.length i64) (List.replicate f.rets.length i64)) :=
  (Func.toBFlat? f).map denoteFuncB

/-- Computable check that a `BFlat rs` contains no `stackalloc`, `interact`, or `hlt`. -/
def BFlat.noStackNoIO : {rs : List Ty} → BFlat rs → Bool
  | _, .ret _ => true
  | _, .let_ _ k => k.noStackNoIO
  | _, .load _ _ k => k.noStackNoIO
  | _, .store _ _ k => k.noStackNoIO
  | _, .call _ _ _ k => k.noStackNoIO
  | _, .interact _ _ _ _ => false
  | _, .stackalloc _ _ => false
  | _, .seq _ c1 c2 => c1.noStackNoIO && c2.noStackNoIO
  | _, .cond _ t e => t.noStackNoIO && e.noStackNoIO
  | _, .while_ _ _ test body k => test.noStackNoIO && body.noStackNoIO && k.noStackNoIO
  | _, .hlt => false

theorem BFlat.noStackNoIO_denote :
    {rs : List Ty} → (bf : BFlat rs) → bf.noStackNoIO = true →
    ∀ vs : List ((t : Ty) × Val t), (bf.denote Val vs).NoStackNoIO
  | _, .ret vs', _, vs => by
      dsimp only [BFlat.denote]
      cases denoteArgs vs vs' with
      | none => exact .hlt
      | some _ => exact .ret
  | _, .let_ op k, hk, vs => by
      dsimp only [BFlat.denote]
      cases denoteArgs vs op.args with
      | none => exact .hlt
      | some _ => exact .let_ fun xs => BFlat.noStackNoIO_denote k hk (pushTup xs vs)
  | _, .load _ a k, hk, vs => by
      dsimp only [BFlat.denote]
      cases denoteArg vs a with
      | none => exact .hlt
      | some _ => exact .load fun v => BFlat.noStackNoIO_denote k hk (_ :: vs)
  | _, .store v a k, hk, vs => by
      dsimp only [BFlat.denote]
      cases denoteArg vs v <;> cases denoteArg vs a <;>
        first | exact .hlt | exact .store (BFlat.noStackNoIO_denote k hk vs)
  | _, .call _ _ args k, hk, vs => by
      dsimp only [BFlat.denote]
      cases denoteArgs vs args with
      | none => exact .hlt
      | some _ => exact .call fun xs => BFlat.noStackNoIO_denote k hk (pushTup xs vs)
  | _, .interact _ _ _ _, hk, _ => by simp [BFlat.noStackNoIO] at hk
  | _, .stackalloc _ _, hk, _ => by simp [BFlat.noStackNoIO] at hk
  | _, .seq _ c1 c2, hk, vs => by
      simp only [BFlat.noStackNoIO, Bool.and_eq_true] at hk
      exact .seq (BFlat.noStackNoIO_denote c1 hk.1 vs)
        fun xs => BFlat.noStackNoIO_denote c2 hk.2 (pushTup xs vs)
  | _, .cond c t e, hk, vs => by
      simp only [BFlat.noStackNoIO, Bool.and_eq_true] at hk
      dsimp only [BFlat.denote]
      cases denoteArg vs c with
      | none => exact .hlt
      | some _ => exact (.cond (BFlat.noStackNoIO_denote t hk.1 vs)
          (BFlat.noStackNoIO_denote e hk.2 vs))
  | _, .while_ _ init test body k, hk, vs => by
      simp only [BFlat.noStackNoIO, Bool.and_eq_true] at hk
      dsimp only [BFlat.denote]
      cases denoteArgs vs init with
      | none => exact .hlt
      | some _ =>
          exact .while_
            (fun xs => BFlat.noStackNoIO_denote test hk.1.1 (pushTup xs vs))
            (fun xs => BFlat.noStackNoIO_denote body hk.1.2 (pushTup xs vs))
            (fun xs => BFlat.noStackNoIO_denote k hk.2 (pushTup xs vs))
  | _, .hlt, hk, _ => by simp [BFlat.noStackNoIO] at hk

/-! ## 4. `LocalsAgree` & `TupAgree` Invariant Machinery -/

/-- `vs` aligns with `ctx` and every active binding in `ctx` has the same value in `l`. -/
def LocalsAgree (ctx : B2Ctx) (vs : List ((t : Ty) × Val t))
    (l : Kraken.Bedrock2.Locals 64) : Prop :=
  vs.length = ctx.length ∧
  ∀ (idx : Nat) (x : String), listGet? ctx idx = some (some x) →
    ∃ v : BitVec 64, listGet? vs idx = some ⟨i64, v⟩ ∧ l.get? x = some v

/-- Every `(name, val)` pair in `names.zip (tupToList xs)` matches `l.get? name = some val`. -/
def TupAgree (names : List String) (xs : Tup Val (List.replicate names.length i64))
    (l : Kraken.Bedrock2.Locals 64) : Prop :=
  ∀ k v, (k, v) ∈ names.zip (tupToList xs) → l.get? k = some v

private theorem listGet?_cons_succ {α : Type} (a : α) (xs : List α) (i : Nat) :
    listGet? (a :: xs) (i + 1) = listGet? xs i := rfl

private theorem listGet?_cons_zero {α : Type} (a : α) (xs : List α) :
    listGet? (a :: xs) 0 = some a := rfl

private theorem listGet?_shadow {x : String} :
    (ctx : B2Ctx) → ∀ idx y, listGet? (B2Ctx.shadow x ctx) idx = some (some y) →
    listGet? ctx idx = some (some y) ∧ y ≠ x
  | [], idx, _, h => by cases idx <;> simp [B2Ctx.shadow, listGet?] at h
  | o :: rest, 0, y, h => by
      cases o with
      | none => simp [B2Ctx.shadow, listGet?] at h
      | some z =>
          simp only [B2Ctx.shadow, listGet?] at h
          by_cases hzx : z = x
          · simp [hzx] at h
          · simp [beq_false_of_ne hzx] at h
            subst h
            exact ⟨rfl, hzx⟩
  | o :: rest, idx + 1, y, h => by
      cases o with
      | none => exact listGet?_shadow rest idx y h
      | some _ => exact listGet?_shadow rest idx y h

private theorem listGet?_deadCtx (n idx : Nat) (x : String) :
    listGet? (deadCtx n) idx = some (some x) → False := by
  induction n generalizing idx with
  | zero => cases idx <;> simp [deadCtx, listGet?]
  | succ n ih =>
      cases idx with
      | zero => simp [deadCtx, List.replicate_succ, listGet?]
      | succ idx => exact ih idx

theorem LocalsAgree_dead {vs : List ((t : Ty) × Val t)} (l : Kraken.Bedrock2.Locals 64) :
    LocalsAgree (deadCtx vs.length) vs l :=
  ⟨by simp, fun idx x hx => absurd hx (listGet?_deadCtx vs.length idx x)⟩

theorem LocalsAgree_none {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) (ty : Ty) (v : Val ty) :
    LocalsAgree (none :: ctx) (⟨ty, v⟩ :: vs) l := by
  refine ⟨by simp [h.1], fun idx x hx => ?_⟩
  cases idx with
  | zero => simp [listGet?] at hx
  | succ idx => exact h.2 idx x hx

theorem LocalsAgree_shadow {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) (x : String) :
    LocalsAgree (ctx.shadow x) vs (l.erase x) := by
  refine ⟨by simp [h.1], fun idx y hy => ?_⟩
  obtain ⟨hyc, hne⟩ := listGet?_shadow ctx idx y hy
  obtain ⟨v, hvs, hl⟩ := h.2 idx y hyc
  refine ⟨v, hvs, ?_⟩
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_erase,
      beq_false_of_ne hne.symm]
  simpa [Std.ExtHashMap.get?_eq_getElem?] using hl

theorem LocalsAgree_bind1 {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) (x : String) (v : BitVec 64) :
    LocalsAgree (ctx.bind1 x) (⟨i64, v⟩ :: vs) (l.insert x v) := by
  refine ⟨by simp [h.1], fun idx y hy => ?_⟩
  cases idx with
  | zero =>
      simp only [B2Ctx.bind1, listGet?_cons_zero, Option.some.injEq] at hy
      cases hy
      refine ⟨v, rfl, ?_⟩
      rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      simp
  | succ idx =>
      obtain ⟨hyc, hne⟩ := listGet?_shadow ctx idx y hy
      obtain ⟨w, hvs, hl⟩ := h.2 idx y hyc
      refine ⟨w, hvs, ?_⟩
      rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
          beq_false_of_ne hne.symm]
      simpa [Std.ExtHashMap.get?_eq_getElem?] using hl

theorem LocalsAgree_bind1_of_get? {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) {x : String} {v : BitVec 64}
    (hx : l.get? x = some v) :
    LocalsAgree (ctx.bind1 x) (⟨i64, v⟩ :: vs) l := by
  refine ⟨by simp [h.1], fun idx y hy => ?_⟩
  cases idx with
  | zero =>
      simp only [B2Ctx.bind1, listGet?_cons_zero, Option.some.injEq] at hy
      cases hy
      exact ⟨v, rfl, hx⟩
  | succ idx =>
      obtain ⟨hyc, _⟩ := listGet?_shadow ctx idx y hy
      exact h.2 idx y hyc

@[simp]
theorem tupToList_cons {n : Nat} (v : Val i64) (xs : Tup Val (List.replicate n i64)) :
    tupToList (n := n + 1) (v, xs) = v :: tupToList xs := rfl

@[simp]
theorem pushTup_cons {a : Ty} {as : List Ty} (x : Val a) (xs : Tup Val as)
    (vs : List ((t : Ty) × Val t)) :
    pushTup (as := a :: as) (x, xs) vs = pushTup xs (⟨a, x⟩ :: vs) := rfl

@[simp]
theorem pushTup_nil (vs : List ((t : Ty) × Val t)) :
    pushTup (as := []) () vs = vs := rfl

private theorem revVars_succ (m : Nat) :
    revVars (m + 1) = (Arg.var m, revVars m) := rfl

theorem LocalsAgree_bindMany_insertMany :
    {names : List String} → {ctx : B2Ctx} → {vs : List ((t : Ty) × Val t)} →
    {l : Kraken.Bedrock2.Locals 64} →
    LocalsAgree ctx vs l →
    (xs : Tup Val (List.replicate names.length i64)) →
    LocalsAgree (B2Ctx.bindMany names ctx) (pushTup xs vs)
      (l.insertMany (names.zip (tupToList xs)))
  | [], _, _, _, h, () => by
      simpa [B2Ctx.bindMany, tupToList, Std.ExtHashMap.insertMany_nil] using h
  | x :: names, ctx, vs, l, h, (v, xs) => by
      dsimp only [B2Ctx.bindMany, List.foldl, List.length_cons, List.replicate_succ,
        tupToList, pushTup]
      rw [List.zip_cons_cons, Std.ExtHashMap.insertMany_cons]
      exact LocalsAgree_bindMany_insertMany (LocalsAgree_bind1 h x v) xs

theorem LocalsAgree_bindMany_of_TupAgree :
    {names : List String} → {ctx : B2Ctx} → {vs : List ((t : Ty) × Val t)} →
    {l : Kraken.Bedrock2.Locals 64} →
    LocalsAgree ctx vs l →
    (xs : Tup Val (List.replicate names.length i64)) →
    TupAgree names xs l →
    LocalsAgree (B2Ctx.bindMany names ctx) (pushTup xs vs) l
  | [], _, _, _, h, (), _ => h
  | x :: names, ctx, vs, l, h, (v, xs), hta => by
      have hx : l.get? x = some v := hta x v (List.mem_cons_self)
      have hrest : TupAgree names xs l := fun k w hkw =>
        hta k w (List.mem_cons_of_mem _ hkw)
      exact LocalsAgree_bindMany_of_TupAgree (LocalsAgree_bind1_of_get? h hx) xs hrest

theorem lookupCtx_spec : (ctx : B2Ctx) → ∀ x idx,
    lookupCtx ctx x = some idx → listGet? ctx idx = some (some x)
  | [], _, _, h => by simp [lookupCtx] at h
  | none :: rest, x, idx, h => by
      dsimp only [lookupCtx] at h
      cases hm : lookupCtx rest x with
      | none => simp [hm] at h
      | some i =>
          simp only [hm, Option.map_some, Option.some.injEq] at h
          subst h
          exact lookupCtx_spec rest x i hm
  | some y :: rest, x, idx, h => by
      dsimp only [lookupCtx] at h
      by_cases hyx : y = x
      · simp only [beq_iff_eq.mpr hyx, ↓reduceIte, Option.some.injEq] at h
        subst h; subst hyx; rfl
      · simp only [beq_false_of_ne hyx, Bool.false_eq_true, ↓reduceIte] at h
        cases hm : lookupCtx rest x with
        | none => simp [hm] at h
        | some i =>
            simp only [hm, Option.map_some, Option.some.injEq] at h
            subst h
            exact lookupCtx_spec rest x i hm

theorem lookupV_of_LocalsAgree {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) {x : String} {idx : Nat}
    (hlk : lookupCtx ctx x = some idx) :
    ∃ v : BitVec 64, lookupV vs i64 idx = some v ∧ l.get? x = some v := by
  obtain ⟨v, hvs, hl⟩ := h.2 idx x (lookupCtx_spec ctx x idx hlk)
  refine ⟨v, ?_, hl⟩
  simp [lookupV, hvs, castTy]

theorem gatherVars_denote {ctx : B2Ctx} {vs : List ((t : Ty) × Val t)}
    {l : Kraken.Bedrock2.Locals 64} (h : LocalsAgree ctx vs l) :
    {names : List String} →
    {args : Tup (Arg K) (List.replicate names.length i64)} →
    gatherVars ctx names = some args →
    ∃ valArgs : Tup (Arg Val) (List.replicate names.length i64),
      denoteArgs vs args = some valArgs ∧ TupAgree names (vals valArgs) l
  | [], (), _ => ⟨(), rfl, fun _ _ hmem => nomatch hmem⟩
  | x :: names, (a, args), hg => by
      simp only [gatherVars, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hg
      rcases hg with ⟨idx, hidx, rest, hrest, hpair⟩
      have ha : a = .var idx := by cases hpair; rfl
      have hargs : args = rest := by cases hpair; rfl
      subst ha; subst hargs
      obtain ⟨v, hv, hl⟩ := lookupV_of_LocalsAgree h hidx
      obtain ⟨valRest, hdv, hta⟩ := gatherVars_denote h hrest
      refine ⟨(.var v, valRest), ?_, ?_⟩
      · simp [denoteArgs, denoteArg, hv, hdv]
      · intro k w hmem
        have hv0 : vals (ts := List.replicate (x :: names).length i64)
            (Arg.var v, valRest) = (v, vals valRest) := rfl
        rw [hv0, tupToList_cons, List.zip_cons_cons, List.mem_cons] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | hmem'
        · exact hl
        · exact hta k w hmem'

theorem getMany_of_TupAgree {l : Kraken.Bedrock2.Locals 64} :
    {names : List String} → (xs : Tup Val (List.replicate names.length i64)) →
    TupAgree names xs l →
    Kraken.Bedrock2.getMany l names = some (tupToList xs)
  | [], (), _ => rfl
  | x :: names, (v, xs), hta => by
      have hx : l.get? x = some v := hta x v List.mem_cons_self
      have hrest := getMany_of_TupAgree xs (fun k w hkw => hta k w (List.mem_cons_of_mem _ hkw))
      dsimp only [Kraken.Bedrock2.getMany] at hrest ⊢
      rw [List.mapM_cons, hx]
      simp only [Option.bind_eq_bind, Option.bind_some, hrest, Option.pure_def]
      rfl

private theorem listGet?_prefix_len {α : Type} :
    (pref : List α) → (x : α) → (tail : List α) →
    listGet? (pref ++ x :: tail) pref.length = some x
  | [], _, _ => rfl
  | _ :: pref, x, tail => listGet?_prefix_len pref x tail

private theorem lookupV_pushTup_top : ∀ (n : Nat) (x : BitVec 64)
    (xs : Tup Val (List.replicate n i64)) (acc : List ((t : Ty) × Val t)),
    lookupV (pushTup xs (⟨i64, x⟩ :: acc)) i64 n = some x := by
  intro n x xs acc
  suffices hg : ∀ (k : Nat) (ys : Tup Val (List.replicate k i64))
      (pref tail : List ((t : Ty) × Val t)),
      listGet? (pushTup ys (pref ++ ⟨i64, x⟩ :: tail)) (k + pref.length) =
        some ⟨i64, x⟩ by
    have h0 := hg n xs [] acc
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at h0
    simp [lookupV, h0, castTy]
  intro k ys pref tail
  induction k generalizing pref with
  | zero =>
      cases ys
      simpa using listGet?_prefix_len pref ⟨i64, x⟩ tail
  | succ k ihk =>
      rcases ys with ⟨y, ys⟩
      have h1 := ihk ys (⟨i64, y⟩ :: pref)
      have hlen : k + (⟨i64, y⟩ :: pref).length = k + 1 + pref.length := by
        simp [List.length_cons]; omega
      dsimp only [List.replicate_succ, pushTup]
      rwa [← hlen]

private theorem revVars_denote_nat : ∀ (n : Nat) (acc : List ((t : Ty) × Val t))
    (xs : Tup Val (List.replicate n i64)),
    ∃ valArgs : Tup (Arg Val) (List.replicate n i64),
      denoteArgs (pushTup xs acc) (revVars n) = some valArgs ∧ vals valArgs = xs
  | 0, _, xs => by
      cases xs
      exact ⟨(), rfl, rfl⟩
  | n + 1, acc, xs => by
      rcases xs with ⟨x, xs⟩
      obtain ⟨valRest, hdRest, hvRest⟩ := revVars_denote_nat n (⟨i64, x⟩ :: acc) xs
      have htop := lookupV_pushTup_top n x xs acc
      refine ⟨(.var x, valRest), ?_, ?_⟩
      · dsimp only [revVars, List.replicate_succ, pushTup]
        simp [denoteArgs, denoteArg, htop, hdRest]
      · simp [vals, hvRest]

theorem revVars_denote :
    {es : List Kraken.Bedrock2.Expr} →
    ∀ (vs : List ((t : Ty) × Val t)) (ts : Tup Val (List.replicate es.length i64)),
    ∃ valArgs : Tup (Arg Val) (List.replicate es.length i64),
      denoteArgs (pushTup ts vs) (revVars es.length) = some valArgs ∧
      vals valArgs = ts :=
  fun vs ts => revVars_denote_nat _ vs ts

theorem revVars_denote_cons {n : Nat} (vs : List ((t : Ty) × Val t))
    (v : BitVec 64) (ts : Tup Val (List.replicate n i64)) :
    ∃ valArgs : Tup (Arg Val) (List.replicate (n + 1) i64),
      denoteArgs (pushTup ts (⟨i64, v⟩ :: vs)) (revVars (n + 1)) = some valArgs ∧
      vals valArgs = (v, ts) := by
  obtain ⟨valRest, hdRest, hvRest⟩ := revVars_denote_nat n (⟨i64, v⟩ :: vs) ts
  have htop := lookupV_pushTup_top n v ts vs
  refine ⟨(.var v, valRest), ?_, ?_⟩
  · dsimp only [revVars, List.replicate_succ]
    simp [denoteArgs, denoteArg, htop, hdRest]
  · simp [vals, hvRest]

theorem putManyZip_of_length_eq {ks : List String} {vs : List (BitVec 64)}
    {l : Kraken.Bedrock2.Locals 64} (h : ks.length = vs.length) :
    Kraken.Bedrock2.putManyZip ks vs l = some (l.insertMany (ks.zip vs)) := by
  simp [Kraken.Bedrock2.putManyZip, h]

/-! ## 5. Expression Translation Correctness (`trExpr` / `trArgs`) -/

theorem lookupV_head_i64 (v : Val i64) (vs : List ((t' : Ty) × Val t')) :
    lookupV (⟨i64, v⟩ :: vs) i64 0 = some v := rfl

theorem lookupV_head_bool (v : Val .bool) (vs : List ((t' : Ty) × Val t')) :
    lookupV (⟨.bool, v⟩ :: vs) .bool 0 = some v := rfl

theorem lookupV_head_bits {n : Nat} (v : Val (.bits n))
    (vs : List ((t' : Ty) × Val t')) :
    lookupV (⟨.bits n, v⟩ :: vs) (.bits n) 0 = some v := by
  simp [lookupV, listGet?, castTy]

theorem denoteArg_var {vs : List ((t : Ty) × Val t)} {t1 : Ty} {i1 : Nat}
    {v1 : Val t1} (h1 : lookupV vs t1 i1 = some v1) :
    denoteArg vs (Arg.var i1 : Arg K t1) = some (Arg.var v1) := by
  simp [denoteArg, h1]

theorem denoteArgs_var1 {vs : List ((t : Ty) × Val t)} {t1 : Ty} {i1 : Nat}
    {v1 : Val t1} (h1 : lookupV vs t1 i1 = some v1) :
    denoteArgs (ts := [t1]) vs (.var i1, ()) = some (.var v1, ()) := by
  simp [denoteArgs, denoteArg, h1]

theorem denoteArgs_var2 {vs : List ((t : Ty) × Val t)} {t1 t2 : Ty}
    {i1 i2 : Nat} {v1 : Val t1} {v2 : Val t2}
    (h1 : lookupV vs t1 i1 = some v1) (h2 : lookupV vs t2 i2 = some v2) :
    denoteArgs (ts := [t1, t2]) vs (.var i1, .var i2, ()) = some (.var v1, .var v2, ()) := by
  simp [denoteArgs, denoteArg, h1, h2]

theorem denoteArgs_var_imm {vs : List ((t : Ty) × Val t)} {t1 : Ty} (t2 : Ty)
    {i1 : Nat} {v1 : Val t1} (c : Val t2) (h1 : lookupV vs t1 i1 = some v1) :
    denoteArgs (ts := [t1, t2]) vs (.var i1, .imm c, ()) = some (.var v1, .imm c, ()) := by
  simp [denoteArgs, denoteArg, h1]

private theorem inlineTableChain_wp_iff (sz : AccessSize) (t : List UInt8)
    {ext : ExtSpecB} {Γ : EnvB} (B : Nat) (Q : PostB [i64]) (tb : TraceB) (m : Mem 64) :
    ∀ (n idxVar : Nat) (vs : List ((t : Ty) × Val t)) (idxVal : BitVec 64),
    lookupV vs i64 idxVar = some idxVal →
    ((inlineTableChain sz t idxVar n).wp ext Γ B Q vs tb m ↔
      ∃ j < n, idxVal = BitVec.ofNat 64 j ∧
        ∃ v, Kraken.Bedrock2.load? sz (t.At 0) (BitVec.ofNat 64 j) = some v ∧
          Q (v, ()) tb m) := by
  intro n
  induction n with
  | zero =>
      intro idxVar vs idxVal _
      simp [inlineTableChain, BFlat.wp]
  | succ n ih =>
      intro idxVar vs idxVal hlk
      dsimp only [inlineTableChain]
      cases hload : Kraken.Bedrock2.load? sz (t.At 0) (BitVec.ofNat 64 n) with
      | none =>
          rw [ih idxVar vs idxVal hlk]
          constructor
          · rintro ⟨j, hj, heq, v, hv, hq⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, heq, v, hv, hq⟩
          · rintro ⟨j, hj, heq, v, hv, hq⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
            · exact ⟨j, hlt, heq, v, hv, hq⟩
            · rw [hload] at hv; contradiction
      | some v0 =>
          dsimp only [BFlat.wp]
          rw [denoteArgs_var_imm i64 (BitVec.ofNat 64 n) hlk]
          dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
            liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
          rw [denoteArg_var (lookupV_head_bool _ _)]
          simp only [denoteArgs, denoteArg, Bool.false_eq_true, ↓reduceIte]
          have hlk' : lookupV (⟨Ty.bool, decide (idxVal = BitVec.ofNat 64 n)⟩ :: vs) i64
              (idxVar + 1) = some idxVal := hlk
          rw [ih (idxVar + 1) _ idxVal hlk']
          constructor
          · rintro ⟨ht, hf⟩
            by_cases heq : idxVal = BitVec.ofNat 64 n
            · exact ⟨n, Nat.lt_succ_self n, heq, v0, hload, ht (decide_eq_true heq)⟩
            · obtain ⟨j, hj, hjEq, v, hv, hq⟩ := hf (decide_eq_false heq)
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq, v, hv, hq⟩
          · rintro ⟨j, hj, hjEq, v, hv, hq⟩
            constructor
            · intro hdec
              have heq : idxVal = BitVec.ofNat 64 n := of_decide_eq_true hdec
              rw [heq] at hjEq
              rw [← hjEq, hload] at hv
              cases hv; exact hq
            · intro hdec
              have hne : idxVal ≠ BitVec.ofNat 64 n := of_decide_eq_false hdec
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
              · exact ⟨j, hlt, hjEq, v, hv, hq⟩
              · exact absurd hjEq hne

private theorem trOp1_wp_iff (o : Kraken.Bedrock2.Op1) {ext : ExtSpecB} {Γ : EnvB}
    (B : Nat) (Q : PostB [i64]) (vs : List ((t : Ty) × Val t)) (tb : TraceB) (m : Mem 64)
    (v : BitVec 64) (h0 : lookupV vs i64 0 = some v) :
    (trOp1 o).wp ext Γ B Q vs tb m ↔ Q (Kraken.Bedrock2.interpOp1 o v, ()) tb m := by
  cases o <;>
    · dsimp only [trOp1, BFlat.wp]
      rw [denoteArgs_var1 h0]
      dsimp only [Op.wp, OpCode.wp, vals, lift1, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        pushTup]
      rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
      rfl

private theorem trBinop_wp_iff (o : Kraken.Bedrock2.BinOp) {ext : ExtSpecB} {Γ : EnvB}
    (B : Nat) (Q : PostB [i64]) (vs : List ((t : Ty) × Val t)) (tb : TraceB) (m : Mem 64)
    (v1 v2 : BitVec 64) (h1 : lookupV vs i64 1 = some v1) (h0 : lookupV vs i64 0 = some v2) :
    (trBinop o).wp ext Γ B Q vs tb m ↔ Q (Kraken.Bedrock2.interpBinop o v1 v2, ()) tb m := by
  cases o
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var_imm i64 0#64 h0]
    dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
    rw [denoteArg_var (lookupV_head_bool _ _)]
    have h1'' : lookupV (⟨Ty.bool, false⟩ :: vs) i64 2 = some v1 := h1
    have h0'' : lookupV (⟨Ty.bool, false⟩ :: vs) i64 1 = some v2 := h0
    by_cases hv2 : v2 = 0#64
    · simp [hv2, denoteArgs, denoteArg, Kraken.Bedrock2.interpBinop]
    · simp only [hv2, ↓reduceIte, decide_false, Bool.false_eq_true, false_implies, true_implies,
        true_and]
      rw [denoteArgs_var2 h1'' h0'']
      dsimp only [Op.wp, OpCode.wp, vals, pushTup]
      rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
      simp [hv2, Kraken.Bedrock2.interpBinop]
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var_imm i64 0#64 h0]
    dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
    rw [denoteArg_var (lookupV_head_bool _ _)]
    have h1' : lookupV (⟨Ty.bool, true⟩ :: vs) i64 2 = some v1 := h1
    have h1'' : lookupV (⟨Ty.bool, false⟩ :: vs) i64 2 = some v1 := h1
    have h0'' : lookupV (⟨Ty.bool, false⟩ :: vs) i64 1 = some v2 := h0
    by_cases hv2 : v2 = 0#64
    · simp only [hv2, decide_true, true_implies, Bool.true_eq_false, false_implies, and_true]
      rw [denoteArgs_var1 h1']
      simp [Kraken.Bedrock2.interpBinop]
    · simp only [hv2, ↓reduceIte, decide_false, Bool.false_eq_true, false_implies, true_implies,
        true_and]
      rw [denoteArgs_var2 h1'' h0'']
      dsimp only [Op.wp, OpCode.wp, vals, pushTup]
      rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
      simp [hv2, Kraken.Bedrock2.interpBinop]
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]; rfl
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
    rw [denoteArgs_var1 (lookupV_head_bool _ _)]
    dsimp only [Op.wp, OpCode.wp, vals, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
    cases hslt : v1.slt v2 <;> simp [Kraken.Bedrock2.interpBinop, hslt]
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
    rw [denoteArgs_var1 (lookupV_head_bool _ _)]
    dsimp only [Op.wp, OpCode.wp, vals, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
    cases hult : v1.ult v2 <;> simp [Kraken.Bedrock2.interpBinop, hult]
  · dsimp only [trBinop, BFlat.wp]; rw [denoteArgs_var2 h1 h0]
    dsimp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
    rw [denoteArgs_var1 (lookupV_head_bool _ _)]
    dsimp only [Op.wp, OpCode.wp, vals, pushTup]
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
    by_cases heq : v1 = v2 <;> simp [Kraken.Bedrock2.interpBinop, heq]

theorem BFlat.wp_mono {ext : ExtSpecB} {Γ : EnvB} :
    {rs : List Ty} → (bf : BFlat rs) → ∀ {B : Nat} {P Q : PostB rs},
    (∀ r t' m', P r t' m' → Q r t' m') →
    ∀ vs t m, bf.wp ext Γ B P vs t m → bf.wp ext Γ B Q vs t m := by
  intro rs bf B P Q hPQ vs t m hp
  rw [BFlat.wp_iff_denote_wp] at hp ⊢
  exact Cmd.wp_mono hPQ _ t m hp

private theorem load_sub64_wp_iff {ext : ExtSpecB} {Γ : EnvB}
    (sz : AccessSize) (hle : 8 * sz.bytes ≤ 64)
    {addr : Kraken.Bedrock2.Expr} {bfAddr bf : BFlat [i64]}
    (hbf : bf = BFlat.seq [i64] bfAddr
      (BFlat.load (Ty.bits (8 * sz.bytes)) (Arg.var 0)
        (BFlat.let_ ⟨OpCode.zext (8 * sz.bytes) 64, (Arg.var 0, ())⟩
          (BFlat.ret (Arg.var 0, ())))))
    {B : Nat} {vs : List ((t : Ty) × Val t)} {tb : TraceB} {m : Mem 64}
    {l : Kraken.Bedrock2.Locals 64}
    (ihA : ∀ (Q : PostB [i64]),
      (bfAddr.wp ext Γ B Q vs tb m ↔
        ∃ v : BitVec 64, addr.eval m l = some v ∧ Q (v, ()) tb m))
    (Q : PostB [i64]) :
    bf.wp ext Γ B Q vs tb m ↔
      ∃ v : BitVec 64, (Kraken.Bedrock2.Expr.load sz addr).eval m l = some v ∧ Q (v, ()) tb m := by
  subst hbf
  dsimp only [BFlat.wp]
  rw [ihA]
  have hl64 := fun a => loadVal_sz_eq_load? sz m a
  dsimp only [accessTy] at hl64
  constructor
  · rintro ⟨a, ha, hld⟩
    dsimp only [BFlat.wp, pushTup] at hld
    rw [denoteArg_var (lookupV_head_i64 a vs)] at hld
    rcases hld with ⟨v, hv, hlet⟩
    rw [denoteArgs_var1 (lookupV_head_bits v _)] at hlet
    dsimp only [Op.wp, OpCode.wp, vals, pushTup] at hlet
    rcases hlet with ⟨_, hret⟩
    rw [denoteArgs_var1 (lookupV_head_i64 _ _)] at hret
    dsimp only [Arg.val] at hv
    have hv64 : Kraken.Bedrock2.load? sz m a = some (BitVec.setWidth 64 v) := by
      rw [← hl64 a, hv]; rfl
    exact ⟨BitVec.setWidth 64 v, by simp [Kraken.Bedrock2.Expr.eval, ha, hv64], hret⟩
  · rintro ⟨v64, hev, hq⟩
    simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hev
    rcases hev with ⟨a, ha, hv64⟩
    have hl := hl64 a
    rw [hv64] at hl
    cases hlv : loadVal m (Ty.bits (8 * sz.bytes)) a with
    | none => simp only [hlv] at hl; cases hl
    | some v =>
        simp only [hlv, Option.map_some, Option.some.injEq] at hl
        refine ⟨a, ha, ?_⟩
        dsimp only [BFlat.wp, pushTup]
        rw [denoteArg_var (lookupV_head_i64 a vs)]
        refine ⟨v, hlv, ?_⟩
        rw [denoteArgs_var1 (lookupV_head_bits v _)]
        refine ⟨hle, ?_⟩
        dsimp only [vals, pushTup]
        rw [denoteArgs_var1 (lookupV_head_i64 _ _)]
        exact hl ▸ hq

theorem trExpr_wp_iff_eval {ext : ExtSpecB} {Γ : EnvB} :
    (e : Kraken.Bedrock2.Expr) → ∀ {ctx : B2Ctx} {bf : BFlat [i64]},
    trExpr ctx e = some bf →
    ∀ {B : Nat} {vs : List ((t : Ty) × Val t)} {tb : TraceB} {m : Mem 64}
      {l : Kraken.Bedrock2.Locals 64},
    LocalsAgree ctx vs l →
    ∀ (Q : PostB [i64]),
    (bf.wp ext Γ B Q vs tb m ↔
      ∃ v : BitVec 64, e.eval m l = some v ∧ Q (v, ()) tb m)
  | .literal n, ctx, bf, htr, B, vs, tb, m, l, _, Q => by
      simp only [trExpr, Option.some.injEq] at htr
      subst htr
      simp [BFlat.wp, denoteArgs, denoteArg, vals, Kraken.Bedrock2.Expr.eval]
  | .var x, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨idx, hidx, rfl⟩
      obtain ⟨v, hlk, hl⟩ := lookupV_of_LocalsAgree hag hidx
      dsimp only [BFlat.wp]
      rw [denoteArgs_var1 hlk]
      dsimp only [Kraken.Bedrock2.Expr.eval, vals]
      rw [hl]
      simp
  | .load sz addr, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff] at htr
      rcases htr with ⟨bfAddr, htrA, hmatch⟩
      have ihA := trExpr_wp_iff_eval addr htrA (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      cases sz with
      | eight =>
          simp only [Option.pure_def, Option.some.injEq] at hmatch
          subst hmatch
          dsimp only [BFlat.wp]
          rw [ihA]
          simp only [pushTup]
          constructor
          · rintro ⟨a, ha, hld⟩
            rw [denoteArg_var (lookupV_head_i64 a vs)] at hld
            rcases hld with ⟨v, hv, hret⟩
            rw [denoteArgs_var1 (lookupV_head_i64 v _)] at hret
            dsimp only [Arg.val] at hv
            rw [loadVal_eight_eq_load?] at hv
            exact ⟨v, by simp [Kraken.Bedrock2.Expr.eval, ha, hv], hret⟩
          · rintro ⟨v, hev, hq⟩
            simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind,
              Option.bind_eq_some_iff] at hev
            rcases hev with ⟨a, ha, hv⟩
            refine ⟨a, ha, ?_⟩
            rw [denoteArg_var (lookupV_head_i64 a vs)]
            rw [← loadVal_eight_eq_load?] at hv
            refine ⟨v, hv, ?_⟩
            rw [denoteArgs_var1 (lookupV_head_i64 v _)]
            exact hq
      | one =>
          simp only [Option.pure_def, Option.some.injEq] at hmatch
          exact load_sub64_wp_iff .one (by decide) hmatch.symm ihA Q
      | two =>
          simp only [Option.pure_def, Option.some.injEq] at hmatch
          exact load_sub64_wp_iff .two (by decide) hmatch.symm ihA Q
      | four =>
          simp only [Option.pure_def, Option.some.injEq] at hmatch
          exact load_sub64_wp_iff .four (by decide) hmatch.symm ihA Q
  | .inlinetable sz tbl index, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfIdx, htrIdx, rfl⟩
      have ihI := trExpr_wp_iff_eval index htrIdx (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      dsimp only [BFlat.wp]
      rw [ihI]
      simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨idxVal, hidx, hchain⟩
        dsimp only [pushTup] at hchain
        rw [inlineTableChain_wp_iff sz tbl B Q tb m tbl.length 0
          (⟨i64, idxVal⟩ :: vs) idxVal (lookupV_head_i64 idxVal vs)] at hchain
        rcases hchain with ⟨j, _, hjEq, v, hv, hq⟩
        rw [← hjEq] at hv
        exact ⟨v, ⟨idxVal, hidx, hv⟩, hq⟩
      · rintro ⟨v, ⟨idxVal, hidx, hv⟩, hq⟩
        refine ⟨idxVal, hidx, ?_⟩
        dsimp only [pushTup]
        rw [inlineTableChain_wp_iff sz tbl B Q tb m tbl.length 0
          (⟨i64, idxVal⟩ :: vs) idxVal (lookupV_head_i64 idxVal vs)]
        obtain ⟨j, hj, hjEq⟩ := exists_lt_of_load?_listAt hv
        refine ⟨j, hj, hjEq, v, ?_, hq⟩
        rw [← hjEq]; exact hv
  | .op1 o e, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bf1, htr1, rfl⟩
      have ih := trExpr_wp_iff_eval e htr1 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      dsimp only [BFlat.wp]
      rw [ih]
      simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq]
      constructor
      · rintro ⟨v, hv, hOp⟩
        dsimp only [pushTup] at hOp
        rw [trOp1_wp_iff o B Q (⟨i64, v⟩ :: vs) tb m v (lookupV_head_i64 v vs)] at hOp
        exact ⟨Kraken.Bedrock2.interpOp1 o v, ⟨v, hv, rfl⟩, hOp⟩
      · rintro ⟨res, ⟨v, hv, rfl⟩, hq⟩
        refine ⟨v, hv, ?_⟩
        dsimp only [pushTup]
        rw [trOp1_wp_iff o B Q (⟨i64, v⟩ :: vs) tb m v (lookupV_head_i64 v vs)]
        exact hq
  | .op o e1 e2, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bf1, htr1, bf2, htr2, rfl⟩
      have ih1 := trExpr_wp_iff_eval e1 htr1 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      dsimp only [BFlat.wp]
      rw [ih1]
      simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq]
      constructor
      · rintro ⟨v1, hv1, hseq2⟩
        have ih2 := trExpr_wp_iff_eval e2 htr2 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
          (m := m) (l := l) (LocalsAgree_none hag i64 v1)
        dsimp only [pushTup] at hseq2
        rw [ih2] at hseq2
        rcases hseq2 with ⟨v2, hv2, hbin⟩
        dsimp only [pushTup] at hbin
        have hl1 : lookupV (⟨i64, v2⟩ :: ⟨i64, v1⟩ :: vs) i64 1 = some v1 :=
          lookupV_head_i64 v1 vs
        have hl0 : lookupV (⟨i64, v2⟩ :: ⟨i64, v1⟩ :: vs) i64 0 = some v2 :=
          lookupV_head_i64 v2 _
        rw [trBinop_wp_iff o B Q _ tb m v1 v2 hl1 hl0] at hbin
        exact ⟨Kraken.Bedrock2.interpBinop o v1 v2, ⟨v1, hv1, v2, hv2, rfl⟩, hbin⟩
      · rintro ⟨res, ⟨v1, hv1, v2, hv2, rfl⟩, hq⟩
        refine ⟨v1, hv1, ?_⟩
        have ih2 := trExpr_wp_iff_eval e2 htr2 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
          (m := m) (l := l) (LocalsAgree_none hag i64 v1)
        dsimp only [pushTup]
        rw [ih2]
        refine ⟨v2, hv2, ?_⟩
        dsimp only [pushTup]
        have hl1 : lookupV (⟨i64, v2⟩ :: ⟨i64, v1⟩ :: vs) i64 1 = some v1 :=
          lookupV_head_i64 v1 vs
        have hl0 : lookupV (⟨i64, v2⟩ :: ⟨i64, v1⟩ :: vs) i64 0 = some v2 :=
          lookupV_head_i64 v2 _
        rw [trBinop_wp_iff o B Q _ tb m v1 v2 hl1 hl0]
        exact hq
  | .ite c e1 e2, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfC, htrC, bf1, htr1, bf2, htr2, rfl⟩
      have ihC := trExpr_wp_iff_eval c htrC (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      dsimp only [BFlat.wp]
      rw [ihC]
      simp only [Kraken.Bedrock2.Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨vc, hvc, hlet⟩
        dsimp only [BFlat.wp, pushTup] at hlet
        rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc vs)] at hlet
        dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, CmpOp.evalBits, Ty.mask, pushTup] at hlet
        rw [denoteArg_var (lookupV_head_bool _ _)] at hlet
        rcases hlet with ⟨ht, hf⟩
        by_cases hcz : vc = 0#64
        · have ih2 := trExpr_wp_iff_eval e2 htr2 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
            (m := m) (l := l)
            (LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64)))
          have hf' := (ih2 Q).1 (hf (by simp [hcz]))
          rcases hf' with ⟨v, hv, hq⟩
          exact ⟨v, ⟨vc, hvc, by simp [hcz, hv]⟩, hq⟩
        · have ih1 := trExpr_wp_iff_eval e1 htr1 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
            (m := m) (l := l)
            (LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64)))
          have ht' := (ih1 Q).1 (ht (decide_eq_true hcz))
          rcases ht' with ⟨v, hv, hq⟩
          exact ⟨v, ⟨vc, hvc, by simp [hcz, hv]⟩, hq⟩
      · rintro ⟨v, ⟨vc, hvc, hbr⟩, hq⟩
        refine ⟨vc, hvc, ?_⟩
        dsimp only [BFlat.wp, pushTup]
        rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc vs)]
        dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
        rw [denoteArg_var (lookupV_head_bool _ _)]
        constructor
        · intro hdec
          have hcz : vc ≠ 0#64 := of_decide_eq_true hdec
          simp [hcz] at hbr
          have ih1 := trExpr_wp_iff_eval e1 htr1 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
            (m := m) (l := l)
            (LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64)))
          exact (ih1 Q).2 ⟨v, hbr, hq⟩
        · intro hdec
          have hcz : vc = 0#64 := Classical.not_not.mp (of_decide_eq_false hdec)
          simp [hcz] at hbr
          have ih2 := trExpr_wp_iff_eval e2 htr2 (ext := ext) (Γ := Γ) (B := B) (tb := tb)
            (m := m) (l := l)
            (LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64)))
          exact (ih2 Q).2 ⟨v, hbr, hq⟩

theorem trArgs_wp_iff_evalArgs {ext : ExtSpecB} {Γ : EnvB} :
    (es : List Kraken.Bedrock2.Expr) → ∀ {ctx : B2Ctx}
    {bf : BFlat (List.replicate es.length i64)},
    trArgs ctx es = some bf →
    ∀ {B : Nat} {vs : List ((t : Ty) × Val t)} {tb : TraceB} {m : Mem 64}
      {l : Kraken.Bedrock2.Locals 64},
    LocalsAgree ctx vs l →
    ∀ (Q : PostB (List.replicate es.length i64)),
    (bf.wp ext Γ B Q vs tb m ↔
      ∃ argVals : List (BitVec 64),
        Kraken.Bedrock2.evalArgs m l es = some argVals ∧
        ∃ argTup : Tup Val (List.replicate es.length i64),
          tupToList argTup = argVals ∧ Q argTup tb m)
  | [], ctx, bf, htr, B, vs, tb, m, l, _, Q => by
      simp only [trArgs, Option.some.injEq] at htr
      subst htr
      simp only [List.length_nil, BFlat.wp, denoteArgs, vals, Kraken.Bedrock2.evalArgs,
        List.mapM_nil, Option.pure_def, Option.some.injEq]
      constructor
      · intro hq; exact ⟨[], rfl, (), rfl, hq⟩
      · rintro ⟨_, rfl, ⟨⟩, _, hq⟩; exact hq
  | e :: es, ctx, bf, htr, B, vs, tb, m, l, hag, Q => by
      simp only [trArgs, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfE, htrE, bfRest, htrRest, rfl⟩
      have ihE := trExpr_wp_iff_eval e htrE (ext := ext) (Γ := Γ) (B := B) (tb := tb)
        (m := m) (l := l) hag
      dsimp only [BFlat.wp]
      rw [ihE]
      constructor
      · rintro ⟨v, hv, hseq⟩
        have ihR := trArgs_wp_iff_evalArgs es htrRest (ext := ext) (Γ := Γ) (B := B) (tb := tb)
          (m := m) (l := l) (LocalsAgree_none hag i64 v)
        dsimp only [pushTup] at hseq
        rw [ihR] at hseq
        rcases hseq with ⟨restVals, hrest, restTup, hrt, hret⟩
        obtain ⟨valArgs, hd, hvEq⟩ := revVars_denote_cons vs v restTup
        rw [hd] at hret
        dsimp only at hret
        rw [hvEq] at hret
        refine ⟨v :: restVals, ?_, (v, restTup), congrArg (v :: ·) hrt, hret⟩
        dsimp only [Kraken.Bedrock2.evalArgs]
        rw [List.mapM_cons, hv]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        change Option.bind (Kraken.Bedrock2.evalArgs m l es) (fun r => some (v :: r)) =
          some (v :: restVals)
        rw [hrest]; rfl
      · rintro ⟨argVals, hargs, ⟨v, restTup⟩, htv, hq⟩
        simp only [Kraken.Bedrock2.evalArgs, List.mapM_cons, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hargs
        rcases hargs with ⟨v', hv', restVals, hrest, rfl⟩
        dsimp only [List.length_cons, tupToList] at htv
        obtain ⟨rfl, hrt⟩ := List.cons.inj htv
        refine ⟨v, hv', ?_⟩
        have ihR := trArgs_wp_iff_evalArgs es htrRest (ext := ext) (Γ := Γ) (B := B) (tb := tb)
          (m := m) (l := l) (LocalsAgree_none hag i64 v)
        dsimp only [pushTup]
        rw [ihR]
        refine ⟨restVals, hrest, restTup, hrt, ?_⟩
        obtain ⟨valArgs, hd, hvEq⟩ := revVars_denote_cons vs v restTup
        rw [hd]
        dsimp only
        rw [hvEq]
        exact hq

end LeanQbe.T.Bedrock2
