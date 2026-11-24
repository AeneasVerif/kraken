module

public import LeanQbe.T.Wasm.Lower
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.Arith
public import LeanQbe.T.LinkLfp
public import LeanQbe.T.Module
public import LeanQbe.T.InlineLemmas

/-!
# Bulk-Memory & VM-Context Separation Invariants & WP Proofs (`LeanQbe.T.Wasm.BulkSafety`)

Defines the VM-context SFI separation invariant (`WasmMemInv`), monotone growth postcondition
(`WasmPost`), control/callee invariants (`LabsSafe`, `WasmCalleeEnvOk`, `WasmSandboxEnv`), and
weakest-precondition (`wp`) + `callsOk` proofs for every VM-context and bulk-memory emitter in
`LeanQbe.T.Wasm.BulkLower`:
* `emitLoadVmCtx_wp`
* `emitMemBounds_wp`
* `emitMemSize_wp`
* `emitMemZeroPage_wp`
* `emitMemGrowLoop_wp` & `emitMemGrow_wp`
* `emitMemFillLoop_wp` & `emitMemFill_wp`
* `emitMemCopyLoop_wp` & `emitMemCopy_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Wasm

open LeanQbe.T LeanQbe.T.LinkScc

/-! ## Equational `wp` & `Closed` Helpers -/

theorem wp_let_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.let_ op k) m = op.wp (fun r => wp Γ Q X (k r) m) := by
  simp only [wp]

theorem wp_load_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (a : Arg Val T.i64) (k : Val t → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.load t a k) m = ∃ v, loadVal m t a.val = some v ∧ wp Γ Q X (k v) m := by
  simp only [wp]

theorem wp_store_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} (v : Arg Val t) (a : Arg Val T.i64) (k : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.store v a k) m = (storeOk m t a.val ∧ wp Γ Q X k (storeMem m t a.val v.val)) := by
  simp only [wp]

theorem wp_call_ {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    (f : Sym) (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.call f (as := as) (bs := bs) args k) m =
      ∃ (P : Post bs) (E : XPost), Γ f as bs (vals args) m P E ∧
        (∀ r m', P r m' → wp Γ Q X (k r) m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m') := by
  simp only [wp]

theorem wp_jnz_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (c : Arg Val Ty.bool) (t e : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.jnz c t e) m =
      ((c.val = true → wp Γ Q X t m) ∧ (c.val = false → wp Γ Q X e m)) := by
  simp only [wp]

theorem wp_jump_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    (j : Cont ts) (args : Tup (Arg Val) ts) (m : Mem 64) :
    wp Γ Q X (.jump j args) m = j (vals args) m := by
  simp only [wp]

theorem wp_ret_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (vs : Tup (Arg Val) rs) (m : Mem 64) :
    wp Γ Q X (.ret vs) m = Q (vals vs) m := by
  simp only [wp]

theorem wp_group_ {Γ : Env} {rs : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} (bodies : Tup Cont sig → Blocks Val Cont rs sig)
    (k : Tup Cont sig → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.group bodies k) m = ∀ Js, Closed Γ Q X (bodies Js) Js → wp Γ Q X (k Js) m := by
  simp only [wp]

theorem closed_cons_ {Γ : Env} {rs : List Ty} {ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} (b : Tup Val ts → Expr Val Cont rs) (bs : Blocks Val Cont rs sig)
    (Js : Tup Cont (ts :: sig)) :
    Closed Γ Q X (.cons b bs) Js =
      ((∀ xs m, wp Γ Q X (b xs) m → Js.1 xs m) ∧ Closed Γ Q X bs Js.2) := by
  simp only [Closed]

/-! ## Sandbox Invariant, Postcondition & Control/Callee Contracts -/

/-- Host-guest VM-context separation invariant: when linear memory is enabled (`hasMem = true`),
`vmCtx` holds `[memBase, memLen, memCap]` (`cell64` at `+0`, `+8`, `+16`), `memLen ≤ memCap`,
and the pre-allocated guest backing region `region memBase memCap.toNat` is separated (`⋆`)
from the arbitrary host frame `R`. When `hasMem = false`, all memory belongs to `R`. -/
@[expose] def WasmMemInv (hasMem : Bool) (vmCtx memBase memLen memCap : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) : Prop :=
  if hasMem then
    memLen.toNat ≤ memCap.toNat ∧
      (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
       cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R) mem
  else R mem

/-- Universal WebAssembly sandbox return postcondition: status is in `{0#32, 1#32, 2#32}`,
remaining fuel never exceeds entry `fuel`, live memory length never shrinks (`memLen ≤ memLen'`),
and `WasmMemInv` (including host frame `R`) is preserved. -/
@[expose] def WasmPost (hasMem : Bool) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (retTys : List WValTy) (R : Mem 64 → Prop) : Post (wasmRetSig retTys) :=
  fun ys mem' =>
    (ys.1 = 0#32 ∨ ys.1 = 1#32 ∨ ys.1 = 2#32) ∧
    ys.2.1.toNat ≤ fuel.toNat ∧
    ∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
      WasmMemInv hasMem vmCtx memBase memLen' memCap R mem'

theorem WasmPost.mono {hasMem : Bool} {vmCtx memBase l₁ l₂ memCap f₁ f₂ : BitVec 64}
    (hleLen : l₁.toNat ≤ l₂.toNat) (hleFuel : f₁.toNat ≤ f₂.toNat)
    {retTys : List WValTy} {R : Mem 64 → Prop} {ys mem'}
    (h : WasmPost hasMem vmCtx memBase l₂ memCap f₁ retTys R ys mem') :
    WasmPost hasMem vmCtx memBase l₁ memCap f₂ retTys R ys mem' :=
  ⟨h.1, Nat.le_trans h.2.1 hleFuel,
    let ⟨l', hl', hm'⟩ := h.2.2
    ⟨l', Nat.le_trans hleLen hl', hm'⟩⟩

/-- Function-level sandbox specification at recursion bound `i` (fuel cap). -/
@[expose] def WasmFnSpec (hasMem : Bool) (ft : WFuncTy) (i : Nat) :
    Spec (wasmAbiParams ft) (wasmAbiResults ft) :=
  fun xs mem Q _ =>
    xs.2.1.toNat ≤ i ∧
    ∃ (memBase memLen memCap : BitVec 64) (R : Mem 64 → Prop),
      WasmMemInv hasMem xs.1 memBase memLen memCap R mem ∧
      ∀ ys mem', WasmPost hasMem xs.1 memBase memLen memCap xs.2.1 ft.results R ys mem' → Q ys mem'

/-- Parameterized sandbox environment mapping each lowered Wasm function at fuel bound `i` to
`WasmFnSpec`. -/
@[expose] def WasmSandboxEnv (m : WModule) (i : Nat) : Env :=
  fun f as bs xs mem Q X =>
    ∃ fn ∈ m.funcs,
      ∃ (ha : as = wasmAbiParams ((m.types[fn.typeIdx]?).getD {}))
        (hb : bs = wasmAbiResults ((m.types[fn.typeIdx]?).getD {})),
        f = fn.name ∧
        WasmFnSpec m.memory.isSome ((m.types[fn.typeIdx]?).getD {}) i
          (ha ▸ xs) mem (hb ▸ Q) X

/-- Existential fuel-quantified sandbox environment for acyclic `ModuleOk` modules. -/
@[expose] def WasmSandboxEnvAny (m : WModule) : Env :=
  fun f as bs xs mem Q X => ∃ i, WasmSandboxEnv m i f as bs xs mem Q X

/-- Control-label safety invariant: every label `l ∈ labs` accepts any monotone live length
`curLen ≥ minLen`, fuel bound `≤ fuel`, and valid `WasmMemInv`. -/
@[expose] def LabsSafe (locTys : List WValTy) (hasMem : Bool)
    (vmCtx memBase minLen memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (labs : List (WLabel Val Cont locTys)) : Prop :=
  ∀ l ∈ labs, ∀ curLen (xs : Tup Val (labelSig locTys l.argTys)) mem',
    minLen.toNat ≤ curLen.toNat → xs.1.toNat ≤ fuel.toNat →
    WasmMemInv hasMem vmCtx memBase curLen memCap R mem' → l.lbl xs mem'

theorem LabsSafe.mono {locTys : List WValTy} {hasMem : Bool}
    {vmCtx memBase l₁ l₂ memCap f₁ f₂ : BitVec 64}
    (hleLen : l₁.toNat ≤ l₂.toNat) (hleFuel : f₁.toNat ≤ f₂.toNat)
    {R : Mem 64 → Prop} {labs : List (WLabel Val Cont locTys)}
    (hl : LabsSafe locTys hasMem vmCtx memBase l₁ memCap f₂ R labs) :
    LabsSafe locTys hasMem vmCtx memBase l₂ memCap f₁ R labs :=
  fun l hlmem curLen xs m' hcur hf hm =>
    hl l hlmem curLen xs m' (Nat.le_trans hleLen hcur) (Nat.le_trans hf hleFuel) hm

/-- Callee environment invariant: any valid intra-module call at strictly smaller fuel
`f' < fuelBound` and arbitrary live `curLen` satisfies `WasmPost` while preserving `R`. -/
@[expose] def WasmCalleeEnvOk (Γ : Env) (funcs : List WFunc) (types : List WFuncTy)
    (hasMem : Bool) (vmCtx memBase memCap fuelBound : BitVec 64) (R : Mem 64 → Prop) : Prop :=
  ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
    funcs[fnIdx]? = some callee → types[callee.typeIdx]? = some ft →
    ∀ (curLen f' : BitVec 64) args mem', f'.toNat < fuelBound.toNat →
      WasmMemInv hasMem vmCtx memBase curLen memCap R mem' →
      Γ callee.name (wasmAbiParams ft) (wasmAbiResults ft) (vmCtx, f', args) mem'
        (WasmPost hasMem vmCtx memBase curLen memCap f' ft.results R) (fun _ _ _ _ => False)

theorem WasmCalleeEnvOk.mono_fuel {Γ : Env} {funcs : List WFunc} {types : List WFuncTy}
    {hasMem : Bool} {vmCtx memBase memCap f₁ f₂ : BitVec 64} (hle : f₁.toNat ≤ f₂.toNat)
    {R : Mem 64 → Prop}
    (h : WasmCalleeEnvOk Γ funcs types hasMem vmCtx memBase memCap f₂ R) :
    WasmCalleeEnvOk Γ funcs types hasMem vmCtx memBase memCap f₁ R :=
  fun idx c ft hc hft curLen f' args m' hlt hm =>
    h idx c ft hc hft curLen f' args m' (Nat.lt_of_lt_of_le hlt hle) hm

/-! ## Region Separation & BitVec Arithmetic Helpers -/

theorem region_focus_eq (base : BitVec 64) (len ea k : Nat)
    (hlen : len ≤ 2 ^ 64) (hbnd : ea + k ≤ len) :
    region base len =
      (region (base + BitVec.ofNat 64 ea) k ⋆
        (region base ea ⋆
          region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 k) (len - ea - k))) := by
  have h1 := region_split (a := base) (n1 := ea) (n2 := len - ea) (by omega)
  rw [show ea + (len - ea) = len by omega] at h1
  have h2 := region_split (a := base + BitVec.ofNat 64 ea) (n1 := k) (n2 := len - ea - k)
    (by omega)
  rw [show k + (len - ea - k) = len - ea by omega] at h2
  rw [h1, h2]
  ac_rfl

private theorem toBytes_ofBytes_w (w : WMemWidth) {bs : List UInt8} (hl : bs.length = w.bytes) :
    Int.toBytes w.memTy.bytes (Int.ofBytes bs) = bs := by
  cases w <;> simp only [WMemWidth.bytes, WMemWidth.memTy, Ty.bytes] at hl ⊢ <;> grind

theorem region_load_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat}
    (hlen : len ≤ 2 ^ 64) (hbnd : ea + w.bytes ≤ len)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : (region base len ⋆ R) mem) :
    ∃ v : Val w.memTy, loadVal mem w.memTy (base + BitVec.ofNat 64 ea) = some v := by
  rw [region_focus_eq base len ea w.bytes hlen hbnd] at hm
  have hm1 : (region (base + BitVec.ofNat 64 ea) w.bytes ⋆
      (region base ea ⋆
        region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 w.bytes) (len - ea - w.bytes) ⋆
        R)) mem :=
    sep_cast hm (by ac_rfl)
  rcases region_sep_elim hm1 with ⟨bs, hbsLen, hbs⟩
  have hbytes : bs = Int.toBytes w.memTy.bytes (Int.ofBytes bs) := (toBytes_ofBytes_w w hbsLen).symm
  rw [hbytes] at hbs
  cases w with
  | w8 => exact ⟨_, loadVal_toBytes_bits (n := 8) (by decide) hbs⟩
  | w16 => exact ⟨_, loadVal_toBytes_bits (n := 16) (by decide) hbs⟩
  | w32 => exact ⟨_, loadVal_toBytes_bits (n := 32) (by decide) hbs⟩
  | w64 => exact ⟨_, loadVal_toBytes_bits (n := 64) (by decide) hbs⟩

theorem region_store_bits {n : Nat} (hn : n = 8 * (Ty.bits n).bytes)
    (hb64 : (Ty.bits n).bytes ≤ 2 ^ 64) {base : BitVec 64} {len ea : Nat}
    (hlen : len ≤ 2 ^ 64) (hbnd : ea + (Ty.bits n).bytes ≤ len) (v : BitVec n)
    (hbytes : ∀ bs : List UInt8, bs.length = (Ty.bits n).bytes →
      Int.toBytes (Ty.bits n).bytes (Int.ofBytes bs) = bs)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : (region base len ⋆ R) mem) :
    storeOk mem (.bits n) (base + BitVec.ofNat 64 ea) ∧
      (region base len ⋆ R)
        (storeMem mem (.bits n) (base + BitVec.ofNat 64 ea) v) := by
  rw [region_focus_eq base len ea (Ty.bits n).bytes hlen hbnd] at hm
  have hm1 : (region (base + BitVec.ofNat 64 ea) (Ty.bits n).bytes ⋆
      (region base ea ⋆
        region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 (Ty.bits n).bytes)
          (len - ea - (Ty.bits n).bytes) ⋆
        R)) mem :=
    sep_cast hm (by ac_rfl)
  rcases region_sep_elim hm1 with ⟨bs, hbsLen, hbs⟩
  rw [(hbytes bs hbsLen).symm] at hbs
  have hst := store_toBytes_bits (n := n) v hn hb64 hbs
  refine ⟨hst.1, ?_⟩
  have hreg : (region (base + BitVec.ofNat 64 ea) (Ty.bits n).bytes ⋆
      (region base ea ⋆
        region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 (Ty.bits n).bytes)
          (len - ea - (Ty.bits n).bytes) ⋆
        R)) (storeMem mem (.bits n) (base + BitVec.ofNat 64 ea) v) :=
    sep_mono (fun _ h => ⟨_, Int.toBytes_length _ _, h.symm⟩) hst.2
  rw [region_focus_eq base len ea (Ty.bits n).bytes hlen hbnd]
  exact sep_cast hreg (by ac_rfl)

theorem region_store_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat}
    (hlen : len ≤ 2 ^ 64) (hbnd : ea + w.bytes ≤ len)
    (v : Val w.memTy) {R : Mem 64 → Prop} {mem : Mem 64} (hm : (region base len ⋆ R) mem) :
    storeOk mem w.memTy (base + BitVec.ofNat 64 ea) ∧
      (region base len ⋆ R) (storeMem mem w.memTy (base + BitVec.ofNat 64 ea) v) := by
  cases w with
  | w8 =>
    exact region_store_bits (n := 8) rfl (by decide) hlen hbnd v
      (fun _ hl => toBytes_ofBytes_w .w8 hl) hm
  | w16 =>
    exact region_store_bits (n := 16) rfl (by decide) hlen hbnd v
      (fun _ hl => toBytes_ofBytes_w .w16 hl) hm
  | w32 =>
    exact region_store_bits (n := 32) rfl (by decide) hlen hbnd v
      (fun _ hl => toBytes_ofBytes_w .w32 hl) hm
  | w64 =>
    exact region_store_bits (n := 64) rfl (by decide) hlen hbnd v
      (fun _ hl => toBytes_ofBytes_w .w64 hl) hm

/-! ### `WasmMemFocus`: Separation Focusing on `WasmMemInv` Components -/

theorem WasmMemInv.focus_base {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) curLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
  sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_len {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
  sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_cap {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 (vmCtx + 16#64) memCap ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) curLen ⋆ region memBase memCap.toNat ⋆ R)) mem :=
  sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_region {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) mem :=
  sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.load_w {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat) :
    ∃ v : Val w.memTy, loadVal mem w.memTy (memBase + BitVec.ofNat 64 ea) = some v :=
  region_load_w w (Nat.le_of_lt memCap.isLt) hbnd hm.focus_region

theorem WasmMemInv.store_w {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat) (v : Val w.memTy) :
    storeOk mem w.memTy (memBase + BitVec.ofNat 64 ea) ∧
      WasmMemInv true vmCtx memBase curLen memCap R
        (storeMem mem w.memTy (memBase + BitVec.ofNat 64 ea) v) := by
  rcases region_store_w w (Nat.le_of_lt memCap.isLt) hbnd v hm.focus_region with ⟨hsok, hreg⟩
  exact ⟨hsok, hm.1, sep_cast hreg (by ac_rfl)⟩

theorem WasmMemInv.store_len {vmCtx memBase curLen memCap : BitVec 64}
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (newLen : BitVec 64) (hle : newLen.toNat ≤ memCap.toNat) :
    storeOk mem T.i64 (vmCtx + 8#64) ∧
      WasmMemInv true vmCtx memBase newLen memCap R
        (storeMem mem T.i64 (vmCtx + 8#64) newLen) := by
  rcases store_cell64 newLen hm.focus_len with ⟨hsok, h8⟩
  exact ⟨hsok, hle, sep_cast h8 (by ac_rfl)⟩

theorem memBounds_toNat {idx32 off32 : BitVec 32} {bytes : Nat} {memLen : BitVec 64}
    (hb : bytes ≤ 8)
    (hule : (((idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat) +
      BitVec.ofNat 64 bytes).ule memLen) = true) :
    (idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat).toNat + bytes ≤ memLen.toNat := by
  have h1 : idx32.toNat < 2 ^ 32 := idx32.isLt
  have h2 : off32.toNat < 2 ^ 32 := off32.isLt
  have hidx : (idx32.setWidth 64).toNat = idx32.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : idx32.toNat < 2 ^ 64)]
  have hoff : (BitVec.ofNat 64 off32.toNat).toNat = off32.toNat := by
    simp [Nat.mod_eq_of_lt (by omega : off32.toNat < 2 ^ 64)]
  have hea : (idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat).toNat =
      idx32.toNat + off32.toNat := by
    rw [BitVec.toNat_add, hidx, hoff, Nat.mod_eq_of_lt (by omega)]
  have hend : ((idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat) +
      BitVec.ofNat 64 bytes).toNat =
      (idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat).toNat + bytes := by
    rw [BitVec.toNat_add, hea, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have hle : ((idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat) +
      BitVec.ofNat 64 bytes).toNat ≤ memLen.toNat := by
    simpa [BitVec.ule_eq_decide, decide_eq_true_eq] using hule
  omega

theorem u32Add_toNat {a b : BitVec 32} {memLen : BitVec 64}
    (hule : (a.setWidth 64 + b.setWidth 64).ule memLen = true) :
    a.toNat + b.toNat ≤ memLen.toNat := by
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have ha64 : (a.setWidth 64).toNat = a.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64)]
  have hb64 : (b.setWidth 64).toNat = b.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  have hsum : (a.setWidth 64 + b.setWidth 64).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, ha64, hb64, Nat.mod_eq_of_lt (by omega)]
  have hle : (a.setWidth 64 + b.setWidth 64).toNat ≤ memLen.toNat := by
    simpa [BitVec.ule_eq_decide, decide_eq_true_eq] using hule
  omega

private theorem bv64_sub_one_eq {x : BitVec 64} (hne : x ≠ 0#64) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx0 : 0 < x.toNat := Nat.pos_of_ne_zero fun hz =>
    hne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub]
  have hlt := x.isLt
  simp only [h1]
  omega

theorem bv64_sub_one_lt {x : BitVec 64} (hne : x ≠ 0#64) :
    (x - 1#64).toNat < x.toNat := by
  have hx0 : 0 < x.toNat := Nat.pos_of_ne_zero fun hz =>
    hne (BitVec.eq_of_toNat_eq (by simpa using hz))
  rw [bv64_sub_one_eq hne]
  omega

theorem vals_wasmAbi (ft : WFuncTy) (vc f : Arg Val T.i64)
    (ca : Tup (Arg Val) (ft.params.map WValTy.toTy)) :
    vals (ts := wasmAbiParams ft) (vc, f, ca) = (vc.val, f.val, vals ca) := rfl

private theorem arg_imm_val {t : Ty} (c : Val t) : (Arg.imm c).val = c := rfl
private theorem arg_var_val {t : Ty} (v : Val t) : (Arg.var v).val = v := rfl

private theorem bv64_ofNat_add_eq {a b : Nat} :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

private theorem bv64_add_sub_cancel (x y : BitVec 64) : (x + y) - y = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  have hx := x.isLt
  have hy := y.isLt
  by_cases hsum : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hsum]; omega
  · have hlt : x.toNat + y.toNat < 2 ^ 64 + 2 ^ 64 := by omega
    have hmod : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]; omega

/-! ## Trap, VM-Context & Bulk-Memory WP Lemmas -/

theorem wp_mkTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} (retTys : List WValTy)
    (code : BitVec 32) (hc : code = 0#32 ∨ code = 1#32 ∨ code = 2#32)
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (mkTrapExpr retTys code fuel) mem := by
  simp only [mkTrapExpr]
  rw [wp_ret_]
  exact ⟨hc, hf, curLen, hlen, hm⟩

theorem wp_mkStatusTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} (retTys : List WValTy)
    {status : Arg Val T.i32} (hs : status.val = 0#32 ∨ status.val = 1#32 ∨ status.val = 2#32)
    {remFuel : Arg Val T.i64} (hf : remFuel.val.toNat ≤ fuel0.toNat)
    (hlen : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (mkStatusTrapExpr retTys status remFuel) mem := by
  simp only [mkStatusTrapExpr]
  rw [wp_ret_]
  exact ⟨hs, hf, curLen, hlen, hm⟩

macro "wasm_wp_let" : tactic =>
  `(tactic| (
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    try refine ⟨by decide, ?_⟩))

theorem wp_wasm_load_w {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat)
    {k : Val w.memTy → Expr Val Cont rs}
    (hk : ∀ raw : Val w.memTy, wp Γ Q X (k raw) mem) :
    wp Γ Q X (.load w.memTy (.var (memBase + BitVec.ofNat 64 ea)) k) mem := by
  rcases hm.load_w w hbnd with ⟨raw, hraw⟩
  rw [wp_load_]
  exact ⟨raw, hraw, hk raw⟩

theorem wp_wasm_store_w {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat)
    (v : Arg Val w.memTy) {k : Expr Val Cont rs}
    (hk : ∀ m', WasmMemInv true vmCtx memBase curLen memCap R m' → wp Γ Q X k m') :
    wp Γ Q X (.store (t := w.memTy) v (.var (memBase + BitVec.ofNat 64 ea)) k) mem := by
  rcases hm.store_w w hbnd v.val with ⟨hsok, hm'⟩
  rw [wp_store_]
  exact ⟨hsok, hk _ hm'⟩

theorem emitLoadVmCtx_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc : Arg Val T.i64) (hvc : vc.val = vmCtx)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Arg Val T.i64 → Expr Val Cont rs)
    (hk : wp Γ Q X (k (.var memBase) (.var curLen)) mem) :
    wp Γ Q X (emitLoadVmCtx vc k) mem := by
  rcases hm with ⟨_, hsep⟩
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) curLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  simp only [emitLoadVmCtx]
  rw [wp_load_]
  refine ⟨memBase, hvc ▸ loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, hvc, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  refine ⟨curLen, loadVal_cell64 h8, ?_⟩
  exact hk

theorem emitMemBounds_wp {Γ : Env} {X : XPost}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    (vc f : Arg Val T.i64) (hvc : vc.val = vmCtx)
    (hf : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (idx : Arg Val T.i32) (arg : WMemArg) (w : WMemWidth)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (ea : Nat), ea + w.bytes ≤ memCap.toNat →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
        (k (.var (memBase + BitVec.ofNat 64 ea))) mem) :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemBounds retTys vc f idx arg w.bytes k) mem := by
  have hcap : curLen.toNat ≤ memCap.toNat := hm.1
  simp only [emitMemBounds]
  refine emitLoadVmCtx_wp vc hvc hm _ ?_
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals]
  refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ =>
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  have hwb : w.bytes ≤ 8 := by cases w <;> decide
  have hin' : (((idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat) +
      BitVec.ofNat 64 w.bytes).ule curLen) = true := by
    rw [arg_var_val] at hin; exact hin
  have hnat := memBounds_toNat hwb hin'
  have hptr : memBase + (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat) =
      memBase + BitVec.ofNat 64
        (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hptr]
  exact hk _ (Nat.le_trans hnat hcap)

theorem emitMemSize_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc : Arg Val T.i64) (hvc : vc.val = vmCtx)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : wp Γ Q X (k (.var ((curLen >>> 16).setWidth 32))) mem) :
    wp Γ Q X (emitMemSize vc k) mem := by
  rcases hm with ⟨_, hsep⟩
  have h8 : (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  simp only [emitMemSize]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, hvc, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  refine ⟨curLen, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val]
  exact ⟨by decide, by simpa using hk⟩

theorem emitMemZeroPage_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (off : Nat) (hbnd : off + 65536 ≤ memCap.toNat)
    (pagePtr : Arg Val T.i64) (hptr : pagePtr.val = memBase + BitVec.ofNat 64 off)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (kDone : Expr Val Cont rs)
    (hk : ∀ m', WasmMemInv true vmCtx memBase curLen memCap R m' → wp Γ Q X kDone m') :
    wp Γ Q X (emitMemZeroPage pagePtr kDone) mem := by
  simp only [emitMemZeroPage]
  refine wp_join_group (fun _ m' => WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun _ _ m' hm' => hk m' hm') (fun jDone hjDone => ?_)
  let Inv : Nat → Tup Val [T.i64, T.i64] → Mem 64 → Prop := fun n zxs m' =>
    zxs.1.toNat ≤ 65536 ∧ zxs.1.toNat % 8 = 0 ∧ zxs.1.toNat / 8 = n ∧
      zxs.2.1 = memBase + BitVec.ofNat 64 (off + (65536 - zxs.1.toNat)) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_loop_group Inv (fun lZero n zxs m' hlZero hinv => ?_)
    (fun lZero hlZero => ?_)
  · rcases zxs with ⟨zRem, zPtr, ⟨⟩⟩
    rcases hinv with ⟨hRemLe, hMod8, hDiv8, hzPtr, hm'⟩
    dsimp only at hRemLe hMod8 hDiv8 hzPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · rw [wp_jump_]; exact hjDone () m' hm'
    · have hne : zRem ≠ 0#64 := decide_eq_false_iff_not.mp hnz
      have hRemPos : 0 < zRem.toNat := Nat.pos_of_ne_zero fun h0 =>
        hne (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hRemGe8 : 8 ≤ zRem.toNat := by omega
      let ea : Nat := off + (65536 - zRem.toNat)
      have heaBnd : ea + 8 ≤ memCap.toNat := by omega
      have hreg : (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆
          cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) m' :=
        sep_cast hm'.2 (by ac_rfl)
      rcases region_store_w .w64 (Nat.le_of_lt memCap.isLt) heaBnd 0#64 hreg with
        ⟨hsok, hreg'⟩
      rw [wp_store_]
      refine ⟨by simpa [hzPtr, ea] using hsok, ?_⟩
      have hm'' : WasmMemInv true vmCtx memBase curLen memCap R
          (storeMem m' T.i64 zPtr 0#64) :=
        ⟨hm'.1, sep_cast (by simpa [hzPtr, ea] using hreg') (by ac_rfl)⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      have hSubNat : (zRem - 8#64).toNat = zRem.toNat - 8 := by
        rw [BitVec.toNat_sub]
        have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
        have hlt : zRem.toNat < 2 ^ 64 := zRem.isLt
        omega
      have hPtrNext : zPtr + 8#64 =
          memBase + BitVec.ofNat 64 (off + (65536 - (zRem - 8#64).toNat)) := by
        rw [hzPtr, hSubNat, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
          BitVec.add_assoc, bv64_ofNat_add_eq]
        congr 2
        omega
      refine hlZero (n - 1) (zRem - 8#64, zPtr + 8#64, ()) _ (by omega) ?_
      dsimp only [Inv]
      exact ⟨by omega, by omega, by omega, hPtrNext, hm''⟩
  · rw [wp_jump_]
    refine hlZero 8192 (65536#64, pagePtr.val, ()) mem ?_
    dsimp only [Inv]
    exact ⟨by decide, by decide, by decide,
      by rw [hptr, show (65536#64 : BitVec 64).toNat = 65536 from rfl, Nat.sub_self, Nat.add_zero],
      hm⟩

theorem emitMemGrowLoop_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (jDone : Cont [T.i64, T.i32])
    (pLen newLen f delta64 startPtr : Arg Val T.i64) (oldPages32 : Arg Val T.i32)
    (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hpLen : pLen.val = vmCtx + 8#64) (hNoWrap : curLen.toNat ≤ newLen.val.toNat)
    (hLeCap : newLen.val.toNat ≤ memCap.toNat)
    (hNewEq : newLen.val.toNat = curLen.toNat + delta64.val.toNat * 65536)
    (hStart : startPtr.val =
      memBase + BitVec.ofNat 64 (newLen.val.toNat - delta64.val.toNat * 65536))
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (hjDone : ∀ f' res len' m', f'.toNat ≤ f.val.toNat → curLen.toNat ≤ len'.toNat →
      WasmMemInv true vmCtx memBase len' memCap R m' → jDone (f', res, ()) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemGrowLoop retTys jDone pLen newLen oldPages32 f delta64 startPtr) mem := by
  simp only [emitMemGrowLoop]
  let Inv : Nat → Tup Val [T.i64, T.i64, T.i64] → Mem 64 → Prop := fun n pxs m' =>
    pxs.1.toNat ≤ f.val.toNat ∧ pxs.2.1.toNat ≤ delta64.val.toNat ∧ pxs.2.1.toNat = n ∧
      pxs.2.2.1 = memBase + BitVec.ofNat 64 (newLen.val.toNat - pxs.2.1.toNat * 65536) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_loop_group Inv (fun lPage n pxs m' hlPage hinv => ?_)
    (fun lPage hlPage => ?_)
  · rcases pxs with ⟨fHdr, pRem, pPtr, ⟨⟩⟩
    rcases hinv with ⟨hfHdr, hpRemLe, hpRemN, hpPtr, hm'⟩
    dsimp only at hfHdr hpRemLe hpRemN hpPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hd => ?_, fun hnd => ?_⟩
    · have h8 : (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆
          cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) m' :=
        sep_cast hm'.2 (by ac_rfl)
      rcases store_cell64 newLen.val h8 with ⟨hsok, h8'⟩
      rw [wp_store_]
      refine ⟨by simpa [hpLen] using hsok, ?_⟩
      have hm'' : WasmMemInv true vmCtx memBase newLen.val memCap R
          (storeMem m' T.i64 pLen.val newLen.val) :=
        ⟨hLeCap, sep_cast (by simpa [hpLen] using h8') (by ac_rfl)⟩
      rw [wp_jump_]
      exact hjDone fHdr oldPages32.val newLen.val _ hfHdr hNoWrap hm''
    · rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun _ => wp_mkTrapExpr retTys 2#32 (Or.inr (Or.inr rfl))
        (Nat.le_trans hfHdr hf0) hlen0 hm', fun hnz => ?_⟩
      have hneF : fHdr ≠ 0#64 := decide_eq_false_iff_not.mp hnz
      have hneR : pRem ≠ 0#64 := decide_eq_false_iff_not.mp hnd
      have hRemPos : 0 < pRem.toNat := Nat.pos_of_ne_zero fun h0 =>
        hneR (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hFlt : (fHdr - 1#64).toNat < fHdr.toNat := bv64_sub_one_lt hneF
      let off : Nat := newLen.val.toNat - pRem.toNat * 65536
      have hoffBnd : off + 65536 ≤ memCap.toNat := by
        have hmul : 65536 ≤ pRem.toNat * 65536 := Nat.le_mul_of_pos_left 65536 hRemPos
        have hmul2 : pRem.toNat * 65536 ≤ delta64.val.toNat * 65536 :=
          Nat.mul_le_mul_right 65536 hpRemLe
        omega
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      refine emitMemZeroPage_wp off hoffBnd (.var pPtr) hpPtr hm' _ fun m'' hm'' => ?_
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      have hRemSub : (pRem - 1#64).toNat = pRem.toNat - 1 := bv64_sub_one_eq hneR
      have hPtrNext : pPtr + 65536#64 =
          memBase + BitVec.ofNat 64 (newLen.val.toNat - (pRem - 1#64).toNat * 65536) := by
        rw [hpPtr, hRemSub, show (65536#64 : BitVec 64) = BitVec.ofNat 64 65536 from rfl,
          BitVec.add_assoc, bv64_ofNat_add_eq]
        congr 2
        have hmul : 65536 ≤ pRem.toNat * 65536 := Nat.le_mul_of_pos_left 65536 hRemPos
        have hmul2 : pRem.toNat * 65536 ≤ delta64.val.toNat * 65536 :=
          Nat.mul_le_mul_right 65536 hpRemLe
        have hsubMul : (pRem.toNat - 1) * 65536 = pRem.toNat * 65536 - 65536 := by
          rw [Nat.sub_mul, Nat.one_mul]
        omega
      refine hlPage (pRem.toNat - 1) (fHdr - 1#64, pRem - 1#64, pPtr + 65536#64, ()) m''
        (by omega) ?_
      dsimp only [Inv]
      exact ⟨by omega, by omega, hRemSub, hPtrNext, hm''⟩
  · rw [wp_jump_]
    refine hlPage delta64.val.toNat (f.val, delta64.val, startPtr.val, ()) mem ?_
    dsimp only [Inv]
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, hStart, hm⟩

theorem emitMemGrow_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (memMaxBytes : BitVec 64) (vc f : Arg Val T.i64) (delta32 : Arg Val T.i32)
    (hvc : vc.val = vmCtx) (hf : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Arg Val T.i32 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (f' : Arg Val T.i64) (res : Arg Val T.i32) (len' : BitVec 64) (m' : Mem 64),
      f'.val.toNat ≤ f.val.toNat → curLen.toNat ≤ len'.toNat →
      WasmMemInv true vmCtx memBase len' memCap R m' →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X (k f' res) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemGrow retTys memMaxBytes vc f delta32 k) mem := by
  simp only [emitMemGrow]
  let P : Tup Val [T.i64, T.i32] → Mem 64 → Prop := fun xs m' =>
    xs.1.toNat ≤ f.val.toNat ∧ ∃ len', curLen.toNat ≤ len'.toNat ∧
      WasmMemInv true vmCtx memBase len' memCap R m'
  refine wp_join_group P (fun _ xs m' ⟨hf', len', hle, hm'⟩ =>
    hk (.var xs.1) (.var xs.2.1) len' m' hf' hle hm') (fun jDone hjDone => ?_)
  rcases hm with ⟨hLenCap, hsep⟩
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) curLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, hvc ▸ loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, hvc, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  refine ⟨curLen, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, hvc, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h16 : (cell64 (vmCtx + 16#64) memCap ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) curLen ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  refine ⟨memCap, loadVal_cell64 h16, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val]
  refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [wp_jump_]
    exact hjDone _ mem ⟨Nat.le_refl _, curLen, Nat.le_refl _, ⟨hLenCap, hsep⟩⟩
  · rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    have hsh16 : ((16#64 : BitVec 64).toNat % 64) = 16 := rfl
    simp only [hsh16]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2]
    rw [wp_jnz_]
    refine ⟨fun hok => ?_, fun _ => ?_⟩
    · rw [arg_var_val] at hok
      simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at hok
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      have hNoWrap : curLen.toNat ≤ (curLen + (delta32.val.setWidth 64 <<< 16)).toNat :=
        hok.1.1
      have hLeCap : (curLen + (delta32.val.setWidth 64 <<< 16)).toNat ≤ memCap.toNat :=
        hok.1.2
      have hDelta : (delta32.val.setWidth 64).toNat = delta32.val.toNat := by
        simp [BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_trans delta32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
      have hGrowEq :
          (delta32.val.setWidth 64 <<< 16).toNat = (delta32.val.setWidth 64).toNat * 65536 := by
        rw [BitVec.toNat_shiftLeft, hDelta, Nat.shiftLeft_eq, show 2 ^ 16 = 65536 by decide]
        have hd32 : delta32.val.toNat < 2 ^ 32 := delta32.val.isLt
        exact Nat.mod_eq_of_lt (by omega)
      have hNewEq :
          (curLen + (delta32.val.setWidth 64 <<< 16)).toNat =
            curLen.toNat + (delta32.val.setWidth 64).toNat * 65536 := by
        rw [BitVec.toNat_add, hGrowEq] at hNoWrap ⊢
        have hd32 : delta32.val.toNat < 2 ^ 32 := delta32.val.isLt
        have hcl : curLen.toNat < 2 ^ 64 := curLen.isLt
        have hgb : (delta32.val.setWidth 64).toNat * 65536 < 2 ^ 64 := by omega
        by_cases hsum : curLen.toNat + (delta32.val.setWidth 64).toNat * 65536 < 2 ^ 64
        · exact Nat.mod_eq_of_lt hsum
        · have hmod : (curLen.toNat + (delta32.val.setWidth 64).toNat * 65536) % 2 ^ 64 =
              curLen.toNat + (delta32.val.setWidth 64).toNat * 65536 - 2 ^ 64 := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
      have hStart : memBase + curLen = memBase + BitVec.ofNat 64
          ((curLen + (delta32.val.setWidth 64 <<< 16)).toNat -
            (delta32.val.setWidth 64).toNat * 65536) := by
        rw [hNewEq, Nat.add_sub_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact emitMemGrowLoop_wp jDone (.var (vmCtx + 8#64)) _ f _ _ _ hf hlen0 rfl hNoWrap hLeCap
        hNewEq hStart ⟨hLenCap, hsep⟩
        fun f' res len' m' hf' hle hm' => hjDone _ _ ⟨hf', len', hle, hm'⟩
    · rw [wp_jump_]
      exact hjDone _ _ ⟨Nat.le_refl _, curLen, Nat.le_refl _, ⟨hLenCap, hsep⟩⟩

theorem emitMemFillLoop_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [T.i64]) (byteVal : Arg Val T.i8) (f n64 dstPtr0 : Arg Val T.i64)
    (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (dstOff : Nat) (hBnd : dstOff + n64.val.toNat ≤ memCap.toNat)
    (hPtr0 : dstPtr0.val = memBase + BitVec.ofNat 64 dstOff)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (hjAfter : ∀ f' m', f'.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' → jAfter (f', ()) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemFillLoop retTys jAfter byteVal f n64 dstPtr0) mem := by
  simp only [emitMemFillLoop]
  let Inv : Nat → Tup Val [T.i64, T.i64, T.i64] → Mem 64 → Prop := fun n lxs m' =>
    lxs.1.toNat ≤ f.val.toNat ∧ lxs.2.1.toNat ≤ n64.val.toNat ∧ lxs.2.1.toNat = n ∧
      lxs.2.2.1 = memBase + BitVec.ofNat 64 (dstOff + (n64.val.toNat - lxs.2.1.toNat)) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_loop_group Inv (fun lLoop n lxs m' hlLoop hinv => ?_)
    (fun lLoop hlLoop => ?_)
  · rcases lxs with ⟨fHdr, rem, ptr, ⟨⟩⟩
    rcases hinv with ⟨hfHdr, hRemLe, hRemN, hPtr, hm'⟩
    dsimp only at hfHdr hRemLe hRemN hPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun hnzRem => ?_⟩
    · rw [wp_jump_]; exact hjAfter fHdr m' hfHdr hm'
    · rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun _ => wp_mkTrapExpr retTys 2#32 (Or.inr (Or.inr rfl))
        (Nat.le_trans hfHdr hf0) hlen0 hm', fun hnzF => ?_⟩
      have hneF : fHdr ≠ 0#64 := decide_eq_false_iff_not.mp hnzF
      have hneR : rem ≠ 0#64 := decide_eq_false_iff_not.mp hnzRem
      have hRemPos : 0 < rem.toNat := Nat.pos_of_ne_zero fun h0 =>
        hneR (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hFlt : (fHdr - 1#64).toNat < fHdr.toNat := bv64_sub_one_lt hneF
      have hRemSub : (rem - 1#64).toNat = rem.toNat - 1 := bv64_sub_one_eq hneR
      let ea : Nat := dstOff + (n64.val.toNat - rem.toNat)
      have heaBnd : ea + 1 ≤ memCap.toNat := by omega
      have hreg : (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆
          cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) m' :=
        sep_cast hm'.2 (by ac_rfl)
      rcases region_store_w .w8 (Nat.le_of_lt memCap.isLt) heaBnd byteVal.val hreg with
        ⟨hsok, hreg'⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_store_]
      refine ⟨by simpa [hPtr, ea] using hsok, ?_⟩
      have hm'' : WasmMemInv true vmCtx memBase curLen memCap R
          (storeMem m' T.i8 ptr byteVal.val) :=
        ⟨hm'.1, sep_cast (by simpa [hPtr, ea] using hreg') (by ac_rfl)⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      have hPtrNext : ptr + 1#64 =
          memBase + BitVec.ofNat 64 (dstOff + (n64.val.toNat - (rem - 1#64).toNat)) := by
        rw [hPtr, hRemSub, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
          BitVec.add_assoc, bv64_ofNat_add_eq]
        congr 2
        omega
      refine hlLoop (rem.toNat - 1) (fHdr - 1#64, rem - 1#64, ptr + 1#64, ()) _ (by omega) ?_
      dsimp only [Inv]
      exact ⟨by omega, by omega, hRemSub, hPtrNext, hm''⟩
  · rw [wp_jump_]
    refine hlLoop n64.val.toNat (f.val, n64.val, dstPtr0.val, ()) mem ?_
    dsimp only [Inv]
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, by rw [hPtr0, Nat.sub_self, Nat.add_zero], hm⟩

theorem emitMemFill_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc f : Arg Val T.i64) (dst32 val32 n32 : Arg Val T.i32)
    (hvc : vc.val = vmCtx) (hf : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (f' : Arg Val T.i64) (m' : Mem 64), f'.val.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X (k f') m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemFill retTys vc f dst32 val32 n32 k) mem := by
  have hcap : curLen.toNat ≤ memCap.toNat := hm.1
  simp only [emitMemFill]
  refine emitLoadVmCtx_wp vc hvc hm _ ?_
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ =>
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  have hBnd : dst32.val.toNat + n32.val.toNat ≤ memCap.toNat :=
    Nat.le_trans (u32Add_toNat hin) hcap
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  let P : Tup Val [T.i64] → Mem 64 → Prop := fun xs m' =>
    xs.1.toNat ≤ f.val.toNat ∧ WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_join_group P (fun _ xs m' ⟨hf', hm'⟩ => hk (.var xs.1) m' hf' hm')
    (fun jAfter hjAfter => ?_)
  have hn64 : (n32.val.setWidth 64).toNat = n32.val.toNat := by
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans n32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  have hdst64 : dst32.val.setWidth 64 = BitVec.ofNat 64 dst32.val.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans dst32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  refine emitMemFillLoop_wp jAfter _ f _ _ hf hlen0 dst32.val.toNat ?_ ?_ hm
    fun f' m' hf' hm' => hjAfter _ m' ⟨hf', hm'⟩
  · simpa [hn64] using hBnd
  · simp only [arg_var_val, hdst64]

theorem emitMemCopyLoop_wp {Γ : Env} {X : XPost} (fwd : Bool) (retTys : List WValTy)
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [T.i64]) (f n64 dPtr0 sPtr0 : Arg Val T.i64)
    (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (dOff sOff : Nat)
    (hdBnd : dOff + n64.val.toNat ≤ memCap.toNat)
    (hsBnd : sOff + n64.val.toNat ≤ memCap.toNat)
    (hdPtr : dPtr0.val = memBase + BitVec.ofNat 64 (if fwd then dOff else dOff + n64.val.toNat))
    (hsPtr : sPtr0.val = memBase + BitVec.ofNat 64 (if fwd then sOff else sOff + n64.val.toNat))
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (hjAfter : ∀ f' m', f'.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' → jAfter (f', ()) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemCopyLoop fwd retTys jAfter f n64 dPtr0 sPtr0) mem := by
  simp only [emitMemCopyLoop]
  let Inv : Nat → Tup Val [T.i64, T.i64, T.i64, T.i64] → Mem 64 → Prop := fun n lxs m' =>
    lxs.1.toNat ≤ f.val.toNat ∧ lxs.2.1.toNat ≤ n64.val.toNat ∧ lxs.2.1.toNat = n ∧
      lxs.2.2.1 = memBase + BitVec.ofNat 64
        (if fwd then dOff + (n64.val.toNat - lxs.2.1.toNat) else dOff + lxs.2.1.toNat) ∧
      lxs.2.2.2.1 = memBase + BitVec.ofNat 64
        (if fwd then sOff + (n64.val.toNat - lxs.2.1.toNat) else sOff + lxs.2.1.toNat) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_loop_group Inv (fun lLoop n lxs m' hlLoop hinv => ?_)
    (fun lLoop hlLoop => ?_)
  · rcases lxs with ⟨fHdr, rem, dPtr, sPtr, ⟨⟩⟩
    rcases hinv with ⟨hfHdr, hRemLe, hRemN, hdP, hsP, hm'⟩
    dsimp only at hfHdr hRemLe hRemN hdP hsP
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun hnzRem => ?_⟩
    · rw [wp_jump_]; exact hjAfter fHdr m' hfHdr hm'
    · rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun _ => wp_mkTrapExpr retTys 2#32 (Or.inr (Or.inr rfl))
        (Nat.le_trans hfHdr hf0) hlen0 hm', fun hnzF => ?_⟩
      have hneF : fHdr ≠ 0#64 := decide_eq_false_iff_not.mp hnzF
      have hneR : rem ≠ 0#64 := decide_eq_false_iff_not.mp hnzRem
      have hRemPos : 0 < rem.toNat := Nat.pos_of_ne_zero fun h0 =>
        hneR (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hFlt : (fHdr - 1#64).toNat < fHdr.toNat := bv64_sub_one_lt hneF
      have hRemSub : (rem - 1#64).toNat = rem.toNat - 1 := bv64_sub_one_eq hneR
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte] at hdP hsP ⊢
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
          Bool.false_eq_true, ↓reduceIte]
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
          Bool.false_eq_true, ↓reduceIte]
        let eaD := dOff + (rem.toNat - 1)
        let eaS := sOff + (rem.toNat - 1)
        have heaD : eaD + 1 ≤ memCap.toNat := by omega
        have heaS : eaS + 1 ≤ memCap.toNat := by omega
        have hDP : dPtr - 1#64 = memBase + BitVec.ofNat 64 eaD := by
          have h : dPtr = (memBase + BitVec.ofNat 64 eaD) + 1#64 := by
            rw [hdP, show dOff + rem.toNat = eaD + 1 from by omega, ← bv64_ofNat_add_eq,
              ← BitVec.add_assoc, show BitVec.ofNat 64 1 = 1#64 from rfl]
          rw [h]; exact bv64_add_sub_cancel _ _
        have hSP : sPtr - 1#64 = memBase + BitVec.ofNat 64 eaS := by
          have h : sPtr = (memBase + BitVec.ofNat 64 eaS) + 1#64 := by
            rw [hsP, show sOff + rem.toNat = eaS + 1 from by omega, ← bv64_ofNat_add_eq,
              ← BitVec.add_assoc, show BitVec.ofNat 64 1 = 1#64 from rfl]
          rw [h]; exact bv64_add_sub_cancel _ _
        have hreg : (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆
            cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) m' :=
          sep_cast hm'.2 (by ac_rfl)
        rcases region_load_w .w8 (Nat.le_of_lt memCap.isLt) heaS hreg with ⟨b, hb⟩
        rw [wp_load_]
        refine ⟨b, by simpa [hSP, eaS] using hb, ?_⟩
        rcases region_store_w .w8 (Nat.le_of_lt memCap.isLt) heaD b hreg with ⟨hsok, hreg'⟩
        rw [wp_store_]
        refine ⟨by simpa [hDP, eaD] using hsok, ?_⟩
        have hm'' : WasmMemInv true vmCtx memBase curLen memCap R
            (storeMem m' T.i8 (dPtr - 1#64) b) :=
          ⟨hm'.1, sep_cast (by simpa [hDP, eaD] using hreg') (by ac_rfl)⟩
        rw [wp_jump_]
        refine hlLoop (rem.toNat - 1)
          (fHdr - 1#64, rem - 1#64, dPtr - 1#64, sPtr - 1#64, ()) _ (by omega) ?_
        dsimp only [Inv]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, by omega, hRemSub, hRemSub ▸ hDP, hRemSub ▸ hSP, hm''⟩
      · simp only [↓reduceIte] at hdP hsP ⊢
        let eaD := dOff + (n64.val.toNat - rem.toNat)
        let eaS := sOff + (n64.val.toNat - rem.toNat)
        have heaD : eaD + 1 ≤ memCap.toNat := by omega
        have heaS : eaS + 1 ≤ memCap.toNat := by omega
        have hreg : (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆
            cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) m' :=
          sep_cast hm'.2 (by ac_rfl)
        rcases region_load_w .w8 (Nat.le_of_lt memCap.isLt) heaS hreg with ⟨b, hb⟩
        rw [wp_load_]
        refine ⟨b, by simpa [hsP, eaS] using hb, ?_⟩
        rcases region_store_w .w8 (Nat.le_of_lt memCap.isLt) heaD b hreg with ⟨hsok, hreg'⟩
        rw [wp_store_]
        refine ⟨by simpa [hdP, eaD] using hsok, ?_⟩
        have hm'' : WasmMemInv true vmCtx memBase curLen memCap R
            (storeMem m' T.i8 dPtr b) :=
          ⟨hm'.1, sep_cast (by simpa [hdP, eaD] using hreg') (by ac_rfl)⟩
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
          Bool.false_eq_true, ↓reduceIte]
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
          Bool.false_eq_true, ↓reduceIte]
        rw [wp_jump_]
        have hdNext : dPtr + 1#64 =
            memBase + BitVec.ofNat 64 (dOff + (n64.val.toNat - (rem - 1#64).toNat)) := by
          rw [hdP, hRemSub, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
            BitVec.add_assoc, bv64_ofNat_add_eq]
          congr 2; omega
        have hsNext : sPtr + 1#64 =
            memBase + BitVec.ofNat 64 (sOff + (n64.val.toNat - (rem - 1#64).toNat)) := by
          rw [hsP, hRemSub, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
            BitVec.add_assoc, bv64_ofNat_add_eq]
          congr 2; omega
        refine hlLoop (rem.toNat - 1)
          (fHdr - 1#64, rem - 1#64, dPtr + 1#64, sPtr + 1#64, ()) _ (by omega) ?_
        dsimp only [Inv]
        simp only [↓reduceIte]
        exact ⟨by omega, by omega, hRemSub, hdNext, hsNext, hm''⟩
  · rw [wp_jump_]
    refine hlLoop n64.val.toNat (f.val, n64.val, dPtr0.val, sPtr0.val, ()) mem ?_
    dsimp only [Inv]
    refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, ?_, ?_, hm⟩
    · cases fwd
      · simpa [Nat.sub_self, Nat.add_zero] using hdPtr
      · rw [hdPtr]; simp only [↓reduceIte, Nat.sub_self, Nat.add_zero]
    · cases fwd
      · simpa [Nat.sub_self, Nat.add_zero] using hsPtr
      · rw [hsPtr]; simp only [↓reduceIte, Nat.sub_self, Nat.add_zero]

theorem emitMemCopy_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc f : Arg Val T.i64) (dst32 src32 n32 : Arg Val T.i32)
    (hvc : vc.val = vmCtx) (hf : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (f' : Arg Val T.i64) (m' : Mem 64), f'.val.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X (k f') m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemCopy retTys vc f dst32 src32 n32 k) mem := by
  have hcap : curLen.toNat ≤ memCap.toNat := hm.1
  simp only [emitMemCopy]
  refine emitLoadVmCtx_wp vc hvc hm _ ?_
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2]
  rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ =>
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  simp only [arg_var_val, Bool.and_eq_true] at hin
  have hdBnd : dst32.val.toNat + n32.val.toNat ≤ memCap.toNat :=
    Nat.le_trans (u32Add_toNat hin.1) hcap
  have hsBnd : src32.val.toNat + n32.val.toNat ≤ memCap.toNat :=
    Nat.le_trans (u32Add_toNat hin.2) hcap
  let P : Tup Val [T.i64] → Mem 64 → Prop := fun xs m' =>
    xs.1.toNat ≤ f.val.toNat ∧ WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_join_group P (fun _ xs m' ⟨hf', hm'⟩ => hk (.var xs.1) m' hf' hm')
    (fun jAfter hjAfter => ?_)
  have hn64 : (n32.val.setWidth 64).toNat = n32.val.toNat := by
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans n32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  have hdst64 : dst32.val.setWidth 64 = BitVec.ofNat 64 dst32.val.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans dst32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  have hsrc64 : src32.val.setWidth 64 = BitVec.ofNat 64 src32.val.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans src32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  have hn64bv : n32.val.setWidth 64 = BitVec.ofNat 64 n32.val.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans n32.val.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    refine emitMemCopyLoop_wp true retTys jAfter f _ _ _ hf hlen0
      dst32.val.toNat src32.val.toNat (by simpa [hn64] using hdBnd) (by simpa [hn64] using hsBnd)
      (by simp only [ite_true, arg_var_val, hdst64])
      (by simp only [ite_true, arg_var_val, hsrc64]) hm
      fun f' m' hf' hm' => hjAfter _ m' ⟨hf', hm'⟩
  · rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    refine emitMemCopyLoop_wp false retTys jAfter f _ _ _ hf hlen0
      dst32.val.toNat src32.val.toNat (by simpa [hn64] using hdBnd) (by simpa [hn64] using hsBnd) ?_
      ?_ hm fun f' m' hf' hm' => hjAfter _ m' ⟨hf', hm'⟩
    · simp only [arg_var_val]; rw [hn64]
      simp only [Bool.false_eq_true, ↓reduceIte, hdst64, hn64bv, bv64_ofNat_add_eq]
    · simp only [arg_var_val]; rw [hn64]
      simp only [Bool.false_eq_true, ↓reduceIte, hsrc64, hn64bv, bv64_ofNat_add_eq]

/-! ## `callsOk` Preservation for Bulk-Memory Emitters -/

theorem emitLoadVmCtx_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (vc : Arg (fun _ => Unit) T.i64)
    (k : Arg (fun _ => Unit) T.i64 → Arg (fun _ => Unit) T.i64 →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ mb ml, (k mb ml).callsOk allowed exits) :
    (emitLoadVmCtx vc k).callsOk allowed exits := by
  simp only [emitLoadVmCtx, Expr.callsOk]
  exact hk _ _

theorem emitMemBounds_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (vc f : Arg (fun _ => Unit) T.i64)
    (idx : Arg (fun _ => Unit) T.i32) (arg : WMemArg) (bytes : Nat)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ p, (k p).callsOk allowed exits) :
    (emitMemBounds retTys vc f idx arg bytes k).callsOk allowed exits :=
  emitLoadVmCtx_callsOk allowed exits vc _ fun _ _ => ⟨hk _, trivial⟩

theorem emitMemSize_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (vc : Arg (fun _ => Unit) T.i64)
    (k : Arg (fun _ => Unit) T.i32 → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ p, (k p).callsOk allowed exits) :
    (emitMemSize vc k).callsOk allowed exits := by
  simp only [emitMemSize, Expr.callsOk]
  exact hk _

theorem emitMemZeroPage_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (pPtr : Arg (fun _ => Unit) T.i64) (kDone : Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : kDone.callsOk allowed exits) :
    (emitMemZeroPage pPtr kDone).callsOk allowed exits := by
  simp only [emitMemZeroPage, Expr.callsOk, Blocks.callsOk]
  exact ⟨⟨hk, trivial⟩, ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩⟩

theorem emitMemGrowLoop_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (jDone : Unit) (pLen newLen : Arg (fun _ => Unit) T.i64)
    (op32 : Arg (fun _ => Unit) T.i32) (f d64 sp : Arg (fun _ => Unit) T.i64) :
    (emitMemGrowLoop retTys jDone pLen newLen op32 f d64 sp).callsOk allowed exits := by
  simp only [emitMemGrowLoop, Expr.callsOk, Blocks.callsOk]
  refine ⟨⟨⟨trivial, ⟨trivial, emitMemZeroPage_callsOk allowed exits _ _ trivial⟩⟩, trivial⟩,
    trivial⟩

theorem emitMemGrow_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (memMaxBytes : BitVec 64)
    (vc f : Arg (fun _ => Unit) T.i64) (d32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Arg (fun _ => Unit) T.i32 →
      Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f' r, (k f' r).callsOk allowed exits) :
    (emitMemGrow retTys memMaxBytes vc f d32 k).callsOk allowed exits := by
  simp only [emitMemGrow, Expr.callsOk, Blocks.callsOk]
  exact ⟨⟨hk _ _, trivial⟩, ⟨trivial, ⟨emitMemGrowLoop_callsOk allowed exits _ _ _ _ _ _ _ _,
    trivial⟩⟩⟩

theorem emitMemFillLoop_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (jAfter : Unit) (bv : Arg (fun _ => Unit) T.i8)
    (f n64 dp0 : Arg (fun _ => Unit) T.i64) :
    (emitMemFillLoop retTys jAfter bv f n64 dp0).callsOk allowed exits := by
  simp only [emitMemFillLoop, Expr.callsOk, Blocks.callsOk]
  exact ⟨⟨⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩, trivial⟩

theorem emitMemFill_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (vc f : Arg (fun _ => Unit) T.i64)
    (d32 v32 n32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f', (k f').callsOk allowed exits) :
    (emitMemFill retTys vc f d32 v32 n32 k).callsOk allowed exits := by
  refine emitLoadVmCtx_callsOk allowed exits vc _ fun _ _ => ?_
  simp only [Expr.callsOk, Blocks.callsOk]
  exact ⟨⟨⟨hk _, trivial⟩, emitMemFillLoop_callsOk allowed exits _ _ _ _ _ _⟩, trivial⟩

theorem emitMemCopyLoop_callsOk (allowed : List SigEntry) (exits : List Sym) (fwd : Bool)
    (retTys : List WValTy) (jAfter : Unit) (f n64 dp0 sp0 : Arg (fun _ => Unit) T.i64) :
    (emitMemCopyLoop fwd retTys jAfter f n64 dp0 sp0).callsOk allowed exits := by
  cases fwd <;> simp only [emitMemCopyLoop, Expr.callsOk, Blocks.callsOk] <;>
  exact ⟨⟨⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩, trivial⟩

theorem emitMemCopy_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (vc f : Arg (fun _ => Unit) T.i64)
    (d32 s32 n32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f', (k f').callsOk allowed exits) :
    (emitMemCopy retTys vc f d32 s32 n32 k).callsOk allowed exits := by
  refine emitLoadVmCtx_callsOk allowed exits vc _ fun _ _ => ?_
  simp only [Expr.callsOk, Blocks.callsOk]
  exact ⟨⟨⟨hk _, trivial⟩,
    ⟨emitMemCopyLoop_callsOk allowed exits true _ _ _ _ _ _,
     emitMemCopyLoop_callsOk allowed exits false _ _ _ _ _ _⟩⟩, trivial⟩

end LeanQbe.T.Wasm
