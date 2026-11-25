module

public import LeanQbe.T.Wasm.Lower
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.Arith
public import LeanQbe.T.LinkLfp
public import LeanQbe.T.Module
public import LeanQbe.T.InlineLemmas
import LeanQbe.T.Logic.ProofKit

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

open LeanQbe.T LeanQbe.T.LinkScc LeanQbe.T.ProofKit

/-! ## Equational `wp` & `Closed` Helpers -/

theorem wp_let_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} (op : Op Val ts)
    (k : Tup Val ts → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.let_ op k) m = op.wp (fun r => wp Γ Q X (k r) m) := by simp only [wp]

theorem wp_load_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (t : Ty) (a : Arg Val T.i64)
    (k : Val t → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.load t a k) m = ∃ v, loadVal m t a.val = some v ∧ wp Γ Q X (k v) m := by
  simp only [wp]

theorem wp_store_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {t : Ty} (v : Arg Val t)
    (a : Arg Val T.i64) (k : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.store v a k) m = (storeOk m t a.val ∧ wp Γ Q X k (storeMem m t a.val v.val)) := by
  simp only [wp]

theorem wp_call_ {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost} (f : Sym)
    (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.call f (as := as) (bs := bs) args k) m =
      ∃ (P : Post bs) (E : XPost), Γ f as bs (vals args) m P E ∧
        (∀ r m', P r m' → wp Γ Q X (k r) m') ∧ (∀ g cs xs m', E g cs xs m' → X g cs xs m') := by
  simp only [wp]

theorem wp_jnz_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (c : Arg Val Ty.bool)
    (t e : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.jnz c t e) m = ((c.val = true → wp Γ Q X t m) ∧ (c.val = false → wp Γ Q X e m)) := by
  simp only [wp]

theorem wp_jump_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} (j : Cont ts)
    (args : Tup (Arg Val) ts) (m : Mem 64) :
    wp Γ Q X (.jump j args) m = j (vals args) m := by simp only [wp]

theorem wp_ret_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (vs : Tup (Arg Val) rs)
    (m : Mem 64) : wp Γ Q X (.ret vs) m = Q (vals vs) m := by simp only [wp]

theorem wp_group_ {Γ : Env} {rs : List Ty} {sig : List (List Ty)} {Q : Post rs} {X : XPost}
    (bodies : Tup Cont sig → Blocks Val Cont rs sig) (k : Tup Cont sig → Expr Val Cont rs)
    (m : Mem 64) :
    wp Γ Q X (.group bodies k) m = ∀ Js, Closed Γ Q X (bodies Js) Js → wp Γ Q X (k Js) m := by
  simp only [wp]

theorem closed_cons_ {Γ : Env} {rs : List Ty} {ts : List Ty} {sig : List (List Ty)} {Q : Post rs}
    {X : XPost} (b : Tup Val ts → Expr Val Cont rs) (bs : Blocks Val Cont rs sig)
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
    (ys.1 = 0#32 ∨ ys.1 = 1#32 ∨ ys.1 = 2#32) ∧ ys.2.1.toNat ≤ fuel.toNat ∧
    ∃ memLen', memLen.toNat ≤ memLen'.toNat ∧ WasmMemInv hasMem vmCtx memBase memLen' memCap R mem'

theorem WasmPost.mono {hasMem : Bool} {vmCtx memBase l₁ l₂ memCap f₁ f₂ : BitVec 64}
    (hleLen : l₁.toNat ≤ l₂.toNat) (hleFuel : f₁.toNat ≤ f₂.toNat)
    {retTys : List WValTy} {R : Mem 64 → Prop} {ys mem'}
    (h : WasmPost hasMem vmCtx memBase l₂ memCap f₁ retTys R ys mem') :
    WasmPost hasMem vmCtx memBase l₁ memCap f₂ retTys R ys mem' :=
  let ⟨m', hm', hinv⟩ := h.2.2
  ⟨h.1, Nat.le_trans h.2.1 hleFuel, m', Nat.le_trans hleLen hm', hinv⟩

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

theorem region_focus_eq (base : BitVec 64) (len ea k : Nat) (hlen : len ≤ 2 ^ 64)
    (hbnd : ea + k ≤ len) :
    region base len = (region (base + BitVec.ofNat 64 ea) k ⋆ (region base ea ⋆
      region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 k) (len - ea - k))) := by
  have h1 := region_split (a := base) (n1 := ea) (n2 := len - ea) (by omega)
  rw [show ea + (len - ea) = len by omega] at h1
  have h2 := region_split (a := base + BitVec.ofNat 64 ea) (n1 := k) (n2 := len - ea - k) (by omega)
  rw [show k + (len - ea - k) = len - ea by omega] at h2; rw [h1, h2]; ac_rfl

private theorem toBytes_ofBytes_w (w : WMemWidth) {bs : List UInt8} (hl : bs.length = w.bytes) :
    Int.toBytes w.memTy.bytes (Int.ofBytes bs) = bs := by
  cases w <;> simp only [WMemWidth.bytes, WMemWidth.memTy, Ty.bytes] at hl ⊢ <;> grind

private theorem region_focus_bytes {base : BitVec 64} {len ea k : Nat} (hlen : len ≤ 2 ^ 64)
    (hbnd : ea + k ≤ len) {R : Mem 64 → Prop} {mem : Mem 64} (hm : (region base len ⋆ R) mem) :
    (region (base + BitVec.ofNat 64 ea) k ⋆ (region base ea ⋆
      region (base + BitVec.ofNat 64 ea + BitVec.ofNat 64 k) (len - ea - k) ⋆ R)) mem := by
  rw [region_focus_eq base len ea k hlen hbnd] at hm; exact sep_cast hm (by ac_rfl)

theorem region_load_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat} (hlen : len ≤ 2 ^ 64)
    (hbnd : ea + w.bytes ≤ len) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : (region base len ⋆ R) mem) :
    ∃ v : Val w.memTy, loadVal mem w.memTy (base + BitVec.ofNat 64 ea) = some v := by
  rcases region_sep_elim (region_focus_bytes hlen hbnd hm) with ⟨bs, hbsLen, hbs⟩
  rw [← toBytes_ofBytes_w w hbsLen] at hbs
  cases w <;> exact ⟨_, loadVal_toBytes_bits (by decide) hbs⟩

theorem region_store_bits {n : Nat} (hn : n = 8 * (Ty.bits n).bytes)
    (hb64 : (Ty.bits n).bytes ≤ 2 ^ 64) {base : BitVec 64} {len ea : Nat} (hlen : len ≤ 2 ^ 64)
    (hbnd : ea + (Ty.bits n).bytes ≤ len) (v : BitVec n)
    (hbytes : ∀ bs : List UInt8, bs.length = (Ty.bits n).bytes →
      Int.toBytes (Ty.bits n).bytes (Int.ofBytes bs) = bs)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : (region base len ⋆ R) mem) :
    storeOk mem (.bits n) (base + BitVec.ofNat 64 ea) ∧
      (region base len ⋆ R) (storeMem mem (.bits n) (base + BitVec.ofNat 64 ea) v) := by
  rcases region_sep_elim (region_focus_bytes hlen hbnd hm) with ⟨bs, hbsLen, hbs⟩
  rw [← hbytes bs hbsLen] at hbs
  have hst := store_toBytes_bits (n := n) v hn hb64 hbs
  refine ⟨hst.1, ?_⟩; rw [region_focus_eq base len ea (Ty.bits n).bytes hlen hbnd]
  exact sep_cast (sep_mono (P' := region (base + BitVec.ofNat 64 ea) (Ty.bits n).bytes)
    (fun _ h => ⟨_, Int.toBytes_length _ _, h.symm⟩) hst.2) (by ac_rfl)

theorem region_store_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat} (hlen : len ≤ 2 ^ 64)
    (hbnd : ea + w.bytes ≤ len) (v : Val w.memTy) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : (region base len ⋆ R) mem) :
    storeOk mem w.memTy (base + BitVec.ofNat 64 ea) ∧
      (region base len ⋆ R) (storeMem mem w.memTy (base + BitVec.ofNat 64 ea) v) :=
  let hb : ∀ bs : List UInt8, bs.length = w.bytes →
      Int.toBytes w.memTy.bytes (Int.ofBytes bs) = bs := fun _ hl => toBytes_ofBytes_w w hl
  by cases w <;> exact region_store_bits rfl (by decide) hlen hbnd v hb hm

/-! ### `WasmMemFocus`: Separation Focusing on `WasmMemInv` Components -/

theorem WasmMemInv.focus_base {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) curLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆
      region memBase memCap.toNat ⋆ R)) mem := sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_len {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 (vmCtx + 8#64) curLen ⋆ (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 16#64) memCap ⋆
      region memBase memCap.toNat ⋆ R)) mem := sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_cap {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (cell64 (vmCtx + 16#64) memCap ⋆ (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) curLen ⋆
      region memBase memCap.toNat ⋆ R)) mem := sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.focus_region {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    (region memBase memCap.toNat ⋆ (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) curLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ R)) mem := sep_cast hm.2 (by ac_rfl)

theorem WasmMemInv.load_w {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat) :
    ∃ v : Val w.memTy, loadVal mem w.memTy (memBase + BitVec.ofNat 64 ea) = some v :=
  region_load_w w (Nat.le_of_lt memCap.isLt) hbnd hm.focus_region

theorem WasmMemInv.store_w {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (w : WMemWidth) {ea : Nat} (hbnd : ea + w.bytes ≤ memCap.toNat) (v : Val w.memTy) :
    storeOk mem w.memTy (memBase + BitVec.ofNat 64 ea) ∧
      WasmMemInv true vmCtx memBase curLen memCap R
        (storeMem mem w.memTy (memBase + BitVec.ofNat 64 ea) v) := by
  rcases region_store_w w (Nat.le_of_lt memCap.isLt) hbnd v hm.focus_region with ⟨hsok, hreg⟩
  exact ⟨hsok, hm.1, sep_cast hreg (by ac_rfl)⟩

theorem WasmMemInv.store_len {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop}
    {mem : Mem 64} (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (newLen : BitVec 64) (hle : newLen.toNat ≤ memCap.toNat) :
    storeOk mem T.i64 (vmCtx + 8#64) ∧
      WasmMemInv true vmCtx memBase newLen memCap R (storeMem mem T.i64 (vmCtx + 8#64) newLen) := by
  rcases store_cell64 newLen hm.focus_len with ⟨hsok, h8⟩
  exact ⟨hsok, hle, sep_cast h8 (by ac_rfl)⟩

theorem bv32_toNat_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by c0_bv_omega
theorem bv32_setWidth64_eq_ofNat (x : BitVec 32) :
    x.setWidth 64 = BitVec.ofNat 64 x.toNat := by c0_bv_omega
theorem bv64_add_noWrap_toNat {a b : BitVec 64} (hle : a.toNat ≤ (a + b).toNat) :
    (a + b).toNat = a.toNat + b.toNat := by c0_bv_omega

theorem memBounds_toNat {idx32 off32 : BitVec 32} {bytes : Nat} {memLen : BitVec 64}
    (hb : bytes ≤ 8)
    (hule : (((idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat) +
      BitVec.ofNat 64 bytes).ule memLen) = true) :
    (idx32.setWidth 64 + BitVec.ofNat 64 off32.toNat).toNat + bytes ≤ memLen.toNat := by c0_bv_omega

theorem u32Add_toNat {a b : BitVec 32} {memLen : BitVec 64}
    (hule : (a.setWidth 64 + b.setWidth 64).ule memLen = true) :
    a.toNat + b.toNat ≤ memLen.toNat := by c0_bv_omega

theorem bv64_sub_ofNat_eq {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) (hlt : k < 2 ^ 64) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by c0_bv_omega

theorem bv64_sub_one_eq {x : BitVec 64} (hne : x ≠ 0#64) : (x - 1#64).toNat = x.toNat - 1 := by
  c0_bv_omega
theorem bv64_sub_one_lt {x : BitVec 64} (hne : x ≠ 0#64) : (x - 1#64).toNat < x.toNat := by
  c0_bv_omega
theorem bv64_sub_ne_zero {d n : Nat} (hd : d < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - d) ≠ 0#64 := by c0_bv_omega
theorem vals_wasmAbi (ft : WFuncTy) (vc f : Arg Val T.i64)
    (ca : Tup (Arg Val) (ft.params.map WValTy.toTy)) :
    vals (ts := wasmAbiParams ft) (vc, f, ca) = (vc.val, f.val, vals ca) := rfl
theorem arg_imm_val {t : Ty} (c : Val t) : (Arg.imm c).val = c := rfl
theorem arg_var_val {t : Ty} (v : Val t) : (Arg.var v).val = v := rfl
theorem bv64_ofNat_add_eq {a b : Nat} :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by c0_bv_omega
theorem bv64_add_sub_cancel (x y : BitVec 64) : (x + y) - y = x := by c0_bv_omega

theorem bv64_ptr_add {base : BitVec 64} {a k : Nat} :
    (base + BitVec.ofNat 64 a) + BitVec.ofNat 64 k = base + BitVec.ofNat 64 (a + k) := by
  rw [BitVec.add_assoc, bv64_ofNat_add_eq]

theorem bv64_ptr_sub_one {base : BitVec 64} {a : Nat} (ha : 0 < a) :
    (base + BitVec.ofNat 64 a) - 1#64 = base + BitVec.ofNat 64 (a - 1) := by
  rw [← show BitVec.ofNat 64 (a - 1) + 1#64 = BitVec.ofNat 64 a by c0_bv_omega,
    ← BitVec.add_assoc, bv64_add_sub_cancel]

private theorem ptr_add_nat {base : BitVec 64} {a k b : Nat} (h : a + k = b) :
    (base + BitVec.ofNat 64 a) + BitVec.ofNat 64 k = base + BitVec.ofNat 64 b := by
  rw [bv64_ptr_add, h]

/-! ## Trap, VM-Context & Bulk-Memory WP Lemmas -/

theorem wp_mkTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} (retTys : List WValTy)
    (code : BitVec 32) (hc : code = 0#32 ∨ code = 1#32 ∨ code = 2#32)
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat) (hlen : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (mkTrapExpr retTys code fuel) mem := by
  simp only [mkTrapExpr]; rw [wp_ret_]; exact ⟨hc, hf, curLen, hlen, hm⟩

theorem wp_mkStatusTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} (retTys : List WValTy)
    {status : Arg Val T.i32} (hs : status.val = 0#32 ∨ status.val = 1#32 ∨ status.val = 2#32)
    {remFuel : Arg Val T.i64} (hf : remFuel.val.toNat ≤ fuel0.toNat)
    (hlen : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (mkStatusTrapExpr retTys status remFuel) mem := by
  simp only [mkStatusTrapExpr]; rw [wp_ret_]; exact ⟨hs, hf, curLen, hlen, hm⟩

theorem bv32_ofNat64_toNat (x : BitVec 32) : (BitVec.ofNat 64 x.toNat).toNat = x.toNat := by
  c0_bv_omega

macro "wasm_wp_let" : tactic => `(tactic| (
  rw [wp_let_]; try dsimp only [Op.wp, vals]
  simp only [Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  try (with_reducible apply And.intro; · decide)
  try dsimp only []))

macro "wasm_wp_lets" : tactic => `(tactic| repeat wasm_wp_let)

theorem wp_wasm_load_w {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) (w : WMemWidth) {ea : Nat}
    (hbnd : ea + w.bytes ≤ memCap.toNat) {k : Val w.memTy → Expr Val Cont rs}
    (hk : ∀ raw : Val w.memTy, wp Γ Q X (k raw) mem) :
    wp Γ Q X (.load w.memTy (.var (memBase + BitVec.ofNat 64 ea)) k) mem := by
  rcases hm.load_w w hbnd with ⟨raw, hraw⟩; rw [wp_load_]; exact ⟨raw, hraw, hk raw⟩

theorem wp_wasm_store_w {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) (w : WMemWidth) {ea : Nat}
    (hbnd : ea + w.bytes ≤ memCap.toNat) (v : Arg Val w.memTy) {k : Expr Val Cont rs}
    (hk : ∀ m', WasmMemInv true vmCtx memBase curLen memCap R m' → wp Γ Q X k m') :
    wp Γ Q X (.store (t := w.memTy) v (.var (memBase + BitVec.ofNat 64 ea)) k) mem := by
  rcases hm.store_w w hbnd v.val with ⟨hsok, hm'⟩; rw [wp_store_]; exact ⟨hsok, hk _ hm'⟩

/-! ### `WasmLoopFrame`: Fuel-Metered Countdown Loop Combinators -/

theorem wp_fuel_loop_group {Γ : Env} {retTys : List WValTy} {Q : Post (wasmRetSig retTys)}
    {X : XPost} {ts : List Ty} (Inv : BitVec 64 → BitVec 64 → Tup Val ts → Mem 64 → Prop)
    (args0 : Tup (Arg Val) (T.i64 :: T.i64 :: ts)) (m0 : Mem 64)
    (exitExpr : Val T.i64 → Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (stepExpr : Cont (T.i64 :: T.i64 :: ts) → Val T.i64 → Val T.i64 →
      Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (hInit : Inv (vals args0).1 (vals args0).2.1 (vals args0).2.2 m0)
    (hExit : ∀ fHdr st m', Inv fHdr 0#64 st m' → wp Γ Q X (exitExpr fHdr st) m')
    (hTrap : ∀ fHdr rem st m', rem ≠ 0#64 → fHdr = 0#64 → Inv fHdr rem st m' →
      wp Γ Q X (mkTrapExpr retTys 2#32 (.var fHdr)) m')
    (hStep : ∀ lLoop (fHdr rem : Val T.i64) st m', rem ≠ 0#64 → fHdr ≠ 0#64 →
      (fHdr - 1#64).toNat < fHdr.toNat → (∀ f' rem' st' m'', rem'.toNat < rem.toNat →
        Inv f' rem' st' m'' → lLoop (f', rem', st') m'') →
      Inv fHdr rem st m' → wp Γ Q X (stepExpr lLoop (fHdr - 1#64) rem st) m') :
    wp Γ Q X (.group (sig := [T.i64 :: T.i64 :: ts]) (fun (lLoop, ()) => .cons (fun xs =>
      .let_ (.mk (.cmp .eq T.i64) (.var xs.2.1, .imm 0#64, ())) fun isDone =>
      .jnz (.var isDone.1) (exitExpr xs.1 xs.2.2)
        (.let_ (.mk (.cmp .eq T.i64) (.var xs.1, .imm 0#64, ())) fun outFuel =>
         .jnz (.var outFuel.1) (mkTrapExpr retTys 2#32 (.var xs.1))
           (.let_ (.mk (.sub T.i64) (.var xs.1, .imm 1#64, ())) fun fNext =>
             stepExpr lLoop fNext.1 xs.2.1 xs.2.2))) .nil)
      (fun (lLoop, ()) => .jump lLoop args0)) m0 := by
  refine wp_loop_group (fun n xs m' => xs.2.1.toNat = n ∧ Inv xs.1 xs.2.1 xs.2.2 m')
    (fun lLoop n xs m' hlLoop ⟨hn, hinv⟩ => ?_) (fun lLoop hlLoop => ?_)
  · rcases xs with ⟨fHdr, rem, st⟩; dsimp only at hn hinv; dsimp only [Blocks.get_here]
    wasm_wp_let; rw [wp_jnz_]; refine ⟨fun hd => ?_, fun hnd => ?_⟩
    · have hrem0 : rem = 0#64 := decide_eq_true_eq.mp hd
      subst hrem0; exact hExit fHdr st m' hinv
    · have hneR : rem ≠ 0#64 := decide_eq_false_iff_not.mp hnd; wasm_wp_let; rw [wp_jnz_]
      refine ⟨fun hf0 => hTrap fHdr rem st m' hneR (decide_eq_true_eq.mp hf0) hinv, fun hnzF => ?_⟩
      have hneF : fHdr ≠ 0#64 := decide_eq_false_iff_not.mp hnzF; wasm_wp_let
      exact hStep lLoop fHdr rem st m' hneR hneF (bv64_sub_one_lt hneF)
        (fun _ _ _ _ hlt hinv' => hlLoop _ (_, _, _) _ (hn ▸ hlt) ⟨rfl, hinv'⟩) hinv
  · rw [wp_jump_]; rcases args0 with ⟨a0, a1, ast⟩
    exact hlLoop (vals (ts := T.i64 :: T.i64 :: ts) (a0, a1, ast)).2.1.toNat _ m0 ⟨rfl, hInit⟩

theorem wp_wasm_fuel_loop {Γ : Env} {retTys : List WValTy} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {X : XPost}
    {ts : List Ty} (Inv : BitVec 64 → BitVec 64 → Tup Val ts → Mem 64 → Prop)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hSafe : ∀ f' r' st' m', Inv f' r' st' m' →
      f'.toNat ≤ fuel0.toNat ∧ WasmMemInv hasMem vmCtx memBase curLen memCap R m')
    (args0 : Tup (Arg Val) (T.i64 :: T.i64 :: ts)) (m0 : Mem 64)
    (exitExpr : Val T.i64 → Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (stepExpr : Cont (T.i64 :: T.i64 :: ts) → Val T.i64 → Val T.i64 →
      Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (hInit : Inv (vals args0).1 (vals args0).2.1 (vals args0).2.2 m0)
    (hExit : ∀ fHdr st m', Inv fHdr 0#64 st m' →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (exitExpr fHdr st) m')
    (hStep : ∀ lLoop (fHdr rem : Val T.i64) st m', rem ≠ 0#64 → fHdr ≠ 0#64 →
      (fHdr - 1#64).toNat < fHdr.toNat → (∀ f' rem' st' m'', rem'.toNat < rem.toNat →
        Inv f' rem' st' m'' → lLoop (f', rem', st') m'') →
      Inv fHdr rem st m' → wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
        (stepExpr lLoop (fHdr - 1#64) rem st) m') :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (.group (sig := [T.i64 :: T.i64 :: ts]) (fun (lLoop, ()) => .cons (fun xs =>
        .let_ (.mk (.cmp .eq T.i64) (.var xs.2.1, .imm 0#64, ())) fun isDone =>
        .jnz (.var isDone.1) (exitExpr xs.1 xs.2.2)
          (.let_ (.mk (.cmp .eq T.i64) (.var xs.1, .imm 0#64, ())) fun outFuel =>
           .jnz (.var outFuel.1) (mkTrapExpr retTys 2#32 (.var xs.1))
             (.let_ (.mk (.sub T.i64) (.var xs.1, .imm 1#64, ())) fun fNext =>
               stepExpr lLoop fNext.1 xs.2.1 xs.2.2))) .nil)
        (fun (lLoop, ()) => .jump lLoop args0)) m0 :=
  wp_fuel_loop_group Inv args0 m0 exitExpr stepExpr hInit hExit
    (fun fHdr _ _ _ _ _ hinv =>
      let ⟨hf, hm⟩ := hSafe _ _ _ _ hinv
      wp_mkTrapExpr retTys 2#32 (Or.inr (Or.inr rfl)) (fuel := .var fHdr) hf hlen0 hm) hStep

theorem wp_exact_fuel_loop {Γ : Env} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {X : XPost} {ts : List Ty}
    (Inv : BitVec 64 → BitVec 64 → Tup Val ts → Mem 64 → Prop)
    (hFuelLe : ∀ f' r' st' m', Inv f' r' st' m' → r'.toNat ≤ f'.toNat)
    (args0 : Tup (Arg Val) (T.i64 :: T.i64 :: ts)) (m0 : Mem 64)
    (exitExpr : Val T.i64 → Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (stepExpr : Cont (T.i64 :: T.i64 :: ts) → Val T.i64 → Val T.i64 →
      Tup Val ts → Expr Val Cont (wasmRetSig retTys))
    (hInit : Inv (vals args0).1 (vals args0).2.1 (vals args0).2.2 m0)
    (hExit : ∀ fHdr st m', Inv fHdr 0#64 st m' → wp Γ Q X (exitExpr fHdr st) m')
    (hStep : ∀ lLoop (fHdr rem : Val T.i64) st m', rem ≠ 0#64 → fHdr ≠ 0#64 →
      (fHdr - 1#64).toNat < fHdr.toNat → (∀ f' rem' st' m'', rem'.toNat < rem.toNat →
        Inv f' rem' st' m'' → lLoop (f', rem', st') m'') →
      Inv fHdr rem st m' → wp Γ Q X (stepExpr lLoop (fHdr - 1#64) rem st) m') :
    wp Γ Q X (.group (sig := [T.i64 :: T.i64 :: ts]) (fun (lLoop, ()) => .cons (fun xs =>
      .let_ (.mk (.cmp .eq T.i64) (.var xs.2.1, .imm 0#64, ())) fun isDone =>
      .jnz (.var isDone.1) (exitExpr xs.1 xs.2.2)
        (.let_ (.mk (.cmp .eq T.i64) (.var xs.1, .imm 0#64, ())) fun outFuel =>
         .jnz (.var outFuel.1) (mkTrapExpr retTys 2#32 (.var xs.1))
           (.let_ (.mk (.sub T.i64) (.var xs.1, .imm 1#64, ())) fun fNext =>
             stepExpr lLoop fNext.1 xs.2.1 xs.2.2))) .nil)
      (fun (lLoop, ()) => .jump lLoop args0)) m0 :=
  wp_fuel_loop_group Inv args0 m0 exitExpr stepExpr hInit hExit
    (fun _ _ _ _ hneR hf0 hinv => False.elim <| hneR <| BitVec.eq_of_toNat_eq <| by
      have hle := hFuelLe _ _ _ _ hinv; rw [hf0] at hle; exact Nat.eq_zero_of_le_zero hle) hStep

theorem emitLoadVmCtx_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc : Arg Val T.i64) (hvc : vc.val = vmCtx)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Arg Val T.i64 → Expr Val Cont rs)
    (hk : wp Γ Q X (k (.var memBase) (.var curLen)) mem) :
    wp Γ Q X (emitLoadVmCtx vc k) mem := by
  simp only [emitLoadVmCtx]; rw [wp_load_]; refine ⟨memBase, hvc ▸ loadVal_cell64 hm.focus_base, ?_⟩
  wasm_wp_let; rw [wp_load_]; exact ⟨curLen, hvc ▸ loadVal_cell64 hm.focus_len, hk⟩

theorem emitMemBounds_wp {Γ : Env} {X : XPost}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    (vc f : Arg Val T.i64) (hvc : vc.val = vmCtx) (hf : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) (idx : Arg Val T.i32)
    (arg : WMemArg) (w : WMemWidth) (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (ea : Nat), ea + w.bytes ≤ memCap.toNat →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
        (k (.var (memBase + BitVec.ofNat 64 ea))) mem) :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemBounds retTys vc f idx arg w.bytes k) mem := by
  have hcap : curLen.toNat ≤ memCap.toNat := hm.1
  simp only [emitMemBounds]; refine emitLoadVmCtx_wp vc hvc hm _ ?_; wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ => wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  wasm_wp_lets; have hnat := memBounds_toNat (by cases w <;> decide : w.bytes ≤ 8) hin
  rw [show memBase + (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat) =
      memBase + BitVec.ofNat 64 (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat).toNat by
    c0_bv_omega]
  exact hk _ (Nat.le_trans hnat hcap)

theorem emitMemSize_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc : Arg Val T.i64) (hvc : vc.val = vmCtx)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : wp Γ Q X (k (.var ((curLen >>> 16).setWidth 32))) mem) :
    wp Γ Q X (emitMemSize vc k) mem := by
  simp only [emitMemSize]; wasm_wp_let; rw [wp_load_]
  refine ⟨curLen, hvc ▸ loadVal_cell64 hm.focus_len, ?_⟩
  wasm_wp_lets; simp only [show ((16#64 : BitVec 64).toNat % 64) = 16 from rfl] at hk ⊢; exact hk

private theorem bv64_pos_of_ne {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by c0_bv_omega

theorem emitMemZeroPage_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase curLen memCap : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (off : Nat) (hbnd : off + 65536 ≤ memCap.toNat) (pagePtr : Arg Val T.i64)
    (hptr : pagePtr.val = memBase + BitVec.ofNat 64 off)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) (kDone : Expr Val Cont rs)
    (hk : ∀ m', WasmMemInv true vmCtx memBase curLen memCap R m' → wp Γ Q X kDone m') :
    wp Γ Q X (emitMemZeroPage pagePtr kDone) mem := by
  simp only [emitMemZeroPage]
  refine wp_join_group (fun _ m' => WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun _ _ m' hm' => hk m' hm') (fun jDone hjDone => ?_)
  let Inv : Nat → Tup Val [T.i64, T.i64] → Mem 64 → Prop := fun n zxs m' =>
    zxs.1.toNat ≤ 65536 ∧ zxs.1.toNat % 8 = 0 ∧ zxs.1.toNat / 8 = n ∧
      zxs.2.1 = memBase + BitVec.ofNat 64 (off + (65536 - zxs.1.toNat)) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_loop_group Inv (fun lZero n (zRem, zPtr, ()) m' hlZero
      ⟨hRemLe, hMod8, hDiv8, hzPtr, hm'⟩ => by
    dsimp only at hRemLe hMod8 hDiv8 hzPtr; dsimp only [Blocks.get_here]; wasm_wp_let; rw [wp_jnz_]
    refine ⟨fun _ => by rw [wp_jump_]; exact hjDone () m' hm', fun hnz => ?_⟩
    have hRemPos := bv64_pos_of_ne (decide_eq_false_iff_not.mp hnz)
    have hSub : (zRem - 8#64).toNat = zRem.toNat - 8 := bv64_sub_ofNat_eq (by omega) (by decide)
    rw [hzPtr]
    refine wp_wasm_store_w hm' .w64 (ea := off + (65536 - zRem.toNat))
      (by dsimp [WMemWidth.bytes]; omega) (.imm 0#64) fun m'' hm'' => ?_
    wasm_wp_lets; rw [wp_jump_]
    refine hlZero (n - 1) (zRem - 8#64, _, ()) m'' (by omega)
      ⟨by dsimp only; rw [hSub]; omega, by dsimp only; rw [hSub]; omega,
        by dsimp only; rw [hSub]; omega, ptr_add_nat (k := 8) (by dsimp only; rw [hSub]; omega),
        hm''⟩)
    fun lZero hlZero => by
      rw [wp_jump_]; refine hlZero 8192 (65536#64, pagePtr.val, ()) mem
        ⟨by dsimp only; decide, by dsimp only; decide, by dsimp only; decide, ?_, hm⟩
      dsimp only
      rw [hptr, show (65536#64 : BitVec 64).toNat = 65536 from rfl, Nat.sub_self, Nat.add_zero]

theorem emitMemGrowLoop_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (jDone : Cont [T.i64, T.i32]) (pLen newLen f delta64 startPtr : Arg Val T.i64)
    (oldPages32 : Arg Val T.i32) (hf0 : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) (hpLen : pLen.val = vmCtx + 8#64)
    (hNoWrap : curLen.toNat ≤ newLen.val.toNat) (hLeCap : newLen.val.toNat ≤ memCap.toNat)
    (hNewEq : newLen.val.toNat = curLen.toNat + delta64.val.toNat * 65536) (hStart :
      startPtr.val = memBase + BitVec.ofNat 64 (newLen.val.toNat - delta64.val.toNat * 65536))
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (hjDone : ∀ f' res len' m', f'.toNat ≤ f.val.toNat → curLen.toNat ≤ len'.toNat →
      WasmMemInv true vmCtx memBase len' memCap R m' → jDone (f', res, ()) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemGrowLoop retTys jDone pLen newLen oldPages32 f delta64 startPtr) mem := by
  simp only [emitMemGrowLoop]
  let Inv : BitVec 64 → BitVec 64 → Tup Val [T.i64] → Mem 64 → Prop := fun fHdr pRem st m' =>
    fHdr.toNat ≤ f.val.toNat ∧ pRem.toNat ≤ delta64.val.toNat ∧
      st.1 = memBase + BitVec.ofNat 64 (newLen.val.toNat - pRem.toNat * 65536) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_wasm_fuel_loop Inv hlen0 (fun _ _ _ _ h => ⟨Nat.le_trans h.1 hf0, h.2.2.2⟩)
    (f, delta64, startPtr, ()) mem
    (fun fHdr _ => .store (t := T.i64) newLen pLen (.jump jDone (.var fHdr, oldPages32, ())))
    (fun lPage fNext pRem st => emitMemZeroPage (.var st.1)
      (.let_ (.mk (.sub T.i64) (.var pRem, .imm 1#64, ())) fun pRemN =>
       .let_ (.mk (.add T.i64) (.var st.1, .imm 65536#64, ())) fun pPtrN =>
         .jump lPage (.var fNext, .var pRemN.1, .var pPtrN.1, ())))
    ⟨Nat.le_refl _, Nat.le_refl _, hStart, hm⟩
    (fun fHdr _ m' ⟨hfHdr, _, _, hm'⟩ => by
      rcases hm'.store_len newLen.val hLeCap with ⟨hsok, hm''⟩; rw [wp_store_]
      refine ⟨by simpa [hpLen] using hsok, ?_⟩; rw [wp_jump_]
      exact hjDone fHdr oldPages32.val newLen.val _ hfHdr hNoWrap (by simpa [hpLen] using hm''))
    fun lPage fHdr pRem (pPtr, ()) m' hneR _ _ hRec ⟨hfHdr, hpRemLe, hpPtr, hm'⟩ => by
      dsimp only at hpPtr; have hRemPos := bv64_pos_of_ne hneR
      have hmul : 65536 ≤ pRem.toNat * 65536 := Nat.le_mul_of_pos_left 65536 hRemPos
      have hmul2 := Nat.mul_le_mul_right 65536 hpRemLe
      refine emitMemZeroPage_wp (newLen.val.toNat - pRem.toNat * 65536) (by omega) (.var pPtr)
        hpPtr hm' _ fun m'' hm'' => ?_; wasm_wp_lets; rw [wp_jump_]
      have hSub : (pRem - 1#64).toNat = pRem.toNat - 1 := bv64_sub_one_eq hneR
      refine hRec (fHdr - 1#64) (pRem - 1#64) (pPtr + 65536#64, ()) m'' (bv64_sub_one_lt hneR)
        ⟨by omega, by omega, ?_, hm''⟩
      rw [hpPtr]; exact ptr_add_nat (k := 65536) (by rw [hSub, Nat.sub_mul, Nat.one_mul]; omega)

theorem emitMemGrow_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (memMaxBytes : BitVec 64) (vc f : Arg Val T.i64) (delta32 : Arg Val T.i32)
    (hvc : vc.val = vmCtx) (hf : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
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
  rw [wp_load_]; refine ⟨memBase, hvc ▸ loadVal_cell64 hm.focus_base, ?_⟩
  wasm_wp_let; rw [wp_load_]; refine ⟨curLen, hvc ▸ loadVal_cell64 hm.focus_len, ?_⟩
  wasm_wp_let; rw [wp_load_]; refine ⟨memCap, hvc ▸ loadVal_cell64 hm.focus_cap, ?_⟩
  wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun _ => by rw [wp_jump_]; exact hjDone _ mem ⟨Nat.le_refl _, curLen, Nat.le_refl _, hm⟩,
    fun _ => ?_⟩
  wasm_wp_lets; simp only [show ((16#64 : BitVec 64).toNat % 64) = 16 from rfl]; wasm_wp_lets
  rw [wp_jnz_]
  refine ⟨fun hok => ?_, fun _ => by
    rw [wp_jump_]; exact hjDone _ mem ⟨Nat.le_refl _, curLen, Nat.le_refl _, hm⟩⟩
  simp only [arg_var_val, Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at hok
  wasm_wp_lets
  have hNoWrap : curLen.toNat ≤ (curLen + (delta32.val.setWidth 64 <<< 16)).toNat := hok.1.1
  have hGrowEq :
      (delta32.val.setWidth 64 <<< 16).toNat = (delta32.val.setWidth 64).toNat * 65536 := by
    rw [BitVec.toNat_shiftLeft, bv32_toNat_setWidth64, Nat.shiftLeft_eq,
      show 2 ^ 16 = 65536 by decide]
    have := delta32.val.isLt; exact Nat.mod_eq_of_lt (by omega)
  have hNewEq : (curLen + (delta32.val.setWidth 64 <<< 16)).toNat =
      curLen.toNat + (delta32.val.setWidth 64).toNat * 65536 := by
    rw [bv64_add_noWrap_toNat hNoWrap, hGrowEq]
  have hStart : memBase + curLen = memBase + BitVec.ofNat 64
      ((curLen + (delta32.val.setWidth 64 <<< 16)).toNat -
        (delta32.val.setWidth 64).toNat * 65536) := by
    rw [hNewEq, Nat.add_sub_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact emitMemGrowLoop_wp jDone (.var (vc.val + 8#64)) _ f _ _ _ hf hlen0 (by simp [hvc])
    hNoWrap hok.1.2 hNewEq hStart hm fun f' res len' m' hf' hle hm' =>
      hjDone _ _ ⟨hf', len', hle, hm'⟩

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
  let Inv : BitVec 64 → BitVec 64 → Tup Val [T.i64] → Mem 64 → Prop := fun fHdr rem st m' =>
    fHdr.toNat ≤ f.val.toNat ∧ rem.toNat ≤ n64.val.toNat ∧
      st.1 = memBase + BitVec.ofNat 64 (dstOff + (n64.val.toNat - rem.toNat)) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_wasm_fuel_loop Inv hlen0 (fun _ _ _ _ h => ⟨Nat.le_trans h.1 hf0, h.2.2.2⟩)
    (f, n64, dstPtr0, ()) mem (fun fHdr _ => .jump jAfter (.var fHdr, ()))
    (fun lLoop fNext rem st => .store (t := T.i8) byteVal (.var st.1)
      (.let_ (.mk (.sub T.i64) (.var rem, .imm 1#64, ())) fun remN =>
       .let_ (.mk (.add T.i64) (.var st.1, .imm 1#64, ())) fun ptrN =>
         .jump lLoop (.var fNext, .var remN.1, .var ptrN.1, ())))
    ⟨Nat.le_refl _, Nat.le_refl _, by simp [vals, hPtr0, Nat.sub_self, Nat.add_zero], hm⟩
    (fun fHdr _ m' ⟨hfHdr, _, _, hm'⟩ => by rw [wp_jump_]; exact hjAfter fHdr m' hfHdr hm')
    (fun lLoop fHdr rem (ptr, ()) m' hneR _ _ hRec ⟨hfHdr, hRemLe, hPtr, hm'⟩ => by
      dsimp only at hPtr; have hRemPos := bv64_pos_of_ne hneR
      have hRemSub : (rem - 1#64).toNat = rem.toNat - 1 := bv64_sub_one_eq hneR; rw [hPtr]
      refine wp_wasm_store_w hm' .w8 (ea := dstOff + (n64.val.toNat - rem.toNat))
        (by dsimp [WMemWidth.bytes]; omega) byteVal fun m'' hm'' => ?_
      wasm_wp_lets; rw [wp_jump_]
      refine hRec (fHdr - 1#64) (rem - 1#64) _ m'' (bv64_sub_one_lt hneR)
        ⟨by omega, by omega, ptr_add_nat (k := 1) (by omega), hm''⟩)

theorem emitMemFill_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc f : Arg Val T.i64) (dst32 val32 n32 : Arg Val T.i32) (hvc : vc.val = vmCtx)
    (hf : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (f' : Arg Val T.i64) (m' : Mem 64), f'.val.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X (k f') m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemFill retTys vc f dst32 val32 n32 k) mem := by
  simp only [emitMemFill]; refine emitLoadVmCtx_wp vc hvc hm _ ?_; wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ => wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  wasm_wp_lets
  refine wp_join_group (fun xs m' =>
      xs.1.toNat ≤ f.val.toNat ∧ WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun _ xs m' ⟨hf', hm'⟩ => hk (.var xs.1) m' hf' hm') (fun jAfter hjAfter => ?_)
  exact emitMemFillLoop_wp jAfter _ f _ _ hf hlen0 dst32.val.toNat
    (by simp only [bv32_toNat_setWidth64, arg_var_val]
        exact Nat.le_trans (u32Add_toNat (by simpa using hin)) hm.1)
    (by simp only [arg_var_val, bv32_setWidth64_eq_ofNat]) hm
    fun f' m' hf' hm' => hjAfter _ m' ⟨hf', hm'⟩

theorem emitMemCopyLoop_wp {Γ : Env} {X : XPost} (fwd : Bool) (retTys : List WValTy)
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [T.i64]) (f n64 dPtr0 sPtr0 : Arg Val T.i64)
    (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat) (dOff sOff : Nat)
    (hdBnd : dOff + n64.val.toNat ≤ memCap.toNat) (hsBnd : sOff + n64.val.toNat ≤ memCap.toNat)
    (hdPtr : dPtr0.val = memBase + BitVec.ofNat 64 (if fwd then dOff else dOff + n64.val.toNat))
    (hsPtr : sPtr0.val = memBase + BitVec.ofNat 64 (if fwd then sOff else sOff + n64.val.toNat))
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (hjAfter : ∀ f' m', f'.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' → jAfter (f', ()) m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemCopyLoop fwd retTys jAfter f n64 dPtr0 sPtr0) mem := by
  simp only [emitMemCopyLoop]
  let Inv : BitVec 64 → BitVec 64 → Tup Val [T.i64, T.i64] → Mem 64 → Prop := fun fHdr rem st m' =>
    fHdr.toNat ≤ f.val.toNat ∧ rem.toNat ≤ n64.val.toNat ∧
      st.1 = memBase +
        BitVec.ofNat 64 (if fwd then dOff + (n64.val.toNat - rem.toNat) else dOff + rem.toNat) ∧
      st.2.1 = memBase +
        BitVec.ofNat 64 (if fwd then sOff + (n64.val.toNat - rem.toNat) else sOff + rem.toNat) ∧
      WasmMemInv true vmCtx memBase curLen memCap R m'
  refine wp_wasm_fuel_loop Inv hlen0 (fun _ _ _ _ h => ⟨Nat.le_trans h.1 hf0, h.2.2.2.2⟩)
    (f, n64, dPtr0, sPtr0, ()) mem (fun fHdr _ => .jump jAfter (.var fHdr, ()))
    (fun lLoop fNext rem st => .let_ (.mk (.sub T.i64) (.var rem, .imm 1#64, ())) fun remN =>
      if fwd then .load T.i8 (.var st.2.1) fun b => .store (t := T.i8) (.var b) (.var st.1)
        (.let_ (.mk (.add T.i64) (.var st.1, .imm 1#64, ())) fun dPtrN =>
         .let_ (.mk (.add T.i64) (.var st.2.1, .imm 1#64, ())) fun sPtrN =>
           .jump lLoop (.var fNext, .var remN.1, .var dPtrN.1, .var sPtrN.1, ()))
      else .let_ (.mk (.sub T.i64) (.var st.1, .imm 1#64, ())) fun dPtrP =>
        .let_ (.mk (.sub T.i64) (.var st.2.1, .imm 1#64, ())) fun sPtrP =>
        .load T.i8 (.var sPtrP.1) fun b => .store (t := T.i8) (.var b) (.var dPtrP.1)
          (.jump lLoop (.var fNext, .var remN.1, .var dPtrP.1, .var sPtrP.1, ())))
    ⟨Nat.le_refl _, Nat.le_refl _,
      by cases fwd <;> simp [vals, hdPtr, Nat.sub_self, Nat.add_zero],
      by cases fwd <;> simp [vals, hsPtr, Nat.sub_self, Nat.add_zero], hm⟩
    (fun fHdr _ m' ⟨hfHdr, _, _, _, hm'⟩ => by rw [wp_jump_]; exact hjAfter fHdr m' hfHdr hm')
    (fun lLoop fHdr rem (dPtr, sPtr, ()) m' hneR _ _ hRec ⟨hfHdr, hRemLe, hdP, hsP, hm'⟩ => by
      dsimp only at hdP hsP; have hRemPos := bv64_pos_of_ne hneR
      have hRemSub : (rem - 1#64).toNat = rem.toNat - 1 := bv64_sub_one_eq hneR; wasm_wp_lets
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte] at hdP hsP ⊢; wasm_wp_lets
        rw [hsP, hdP, bv64_ptr_sub_one (by omega), bv64_ptr_sub_one (by omega)]
        refine wp_wasm_load_w hm' .w8 (ea := sOff + rem.toNat - 1)
          (by dsimp [WMemWidth.bytes]; omega) fun b => wp_wasm_store_w hm' .w8
            (ea := dOff + rem.toNat - 1) (by dsimp [WMemWidth.bytes]; omega) (.var b)
            fun m'' hm'' => by
              rw [wp_jump_]
              exact hRec (fHdr - 1#64) (rem - 1#64) _ m'' (bv64_sub_one_lt hneR)
                ⟨by omega, by omega, by simp; congr 2; omega,
                  by simp; congr 2; omega, hm''⟩
      · simp only [↓reduceIte] at hdP hsP ⊢; rw [hsP, hdP]
        refine wp_wasm_load_w hm' .w8 (ea := sOff + (n64.val.toNat - rem.toNat))
          (by dsimp [WMemWidth.bytes]; omega) fun b => wp_wasm_store_w hm' .w8
            (ea := dOff + (n64.val.toNat - rem.toNat)) (by dsimp [WMemWidth.bytes]; omega) (.var b)
            fun m'' hm'' => by
              wasm_wp_lets; rw [wp_jump_]
              exact hRec (fHdr - 1#64) (rem - 1#64) _ m'' (bv64_sub_one_lt hneR)
                ⟨by omega, by omega,
                  ptr_add_nat (k := 1) (by simp only [↓reduceIte, hRemSub]; omega),
                  ptr_add_nat (k := 1) (by simp only [↓reduceIte, hRemSub]; omega), hm''⟩)

theorem emitMemCopy_wp {Γ : Env} {X : XPost} {retTys : List WValTy}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop} {mem : Mem 64}
    (vc f : Arg Val T.i64) (dst32 src32 n32 : Arg Val T.i32) (hvc : vc.val = vmCtx)
    (hf : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (f' : Arg Val T.i64) (m' : Mem 64), f'.val.toNat ≤ f.val.toNat →
      WasmMemInv true vmCtx memBase curLen memCap R m' →
      wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X (k f') m') :
    wp Γ (WasmPost true vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitMemCopy retTys vc f dst32 src32 n32 k) mem := by
  simp only [emitMemCopy]; refine emitLoadVmCtx_wp vc hvc hm _ ?_; wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hin => ?_, fun _ => wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm⟩
  simp only [arg_var_val, Bool.and_eq_true] at hin
  refine wp_join_group (fun xs m' =>
      xs.1.toNat ≤ f.val.toNat ∧ WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun _ xs m' ⟨hf', hm'⟩ => hk (.var xs.1) m' hf' hm') (fun jAfter hjAfter => ?_)
  wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> (
    wasm_wp_lets
    refine emitMemCopyLoop_wp _ retTys jAfter f _ _ _ hf hlen0 dst32.val.toNat src32.val.toNat
      (by simp only [bv32_toNat_setWidth64, arg_var_val]
          exact Nat.le_trans (u32Add_toNat hin.1) hm.1)
      (by simp only [bv32_toNat_setWidth64, arg_var_val]
          exact Nat.le_trans (u32Add_toNat hin.2) hm.1)
      (by simp only [arg_var_val, Bool.false_eq_true, ↓reduceIte, bv32_setWidth64_eq_ofNat,
        bv32_ofNat64_toNat, bv64_ofNat_add_eq])
      (by simp only [arg_var_val, Bool.false_eq_true, ↓reduceIte, bv32_setWidth64_eq_ofNat,
        bv32_ofNat64_toNat, bv64_ofNat_add_eq])
      hm fun f' m' hf' hm' => hjAfter _ m' ⟨hf', hm'⟩)

/-! ## `callsOk` Preservation for Bulk-Memory Emitters -/

theorem emitLoadVmCtx_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (vc : Arg (fun _ => Unit) T.i64)
    (k : Arg (fun _ => Unit) T.i64 → Arg (fun _ => Unit) T.i64 →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ mb ml, (k mb ml).callsOk allowed exits) :
    (emitLoadVmCtx vc k).callsOk allowed exits := hk _ _

theorem emitMemBounds_callsOk (allowed : List SigEntry) (exits : List Sym) (retTys : List WValTy)
    (vc f : Arg (fun _ => Unit) T.i64) (idx : Arg (fun _ => Unit) T.i32) (arg : WMemArg)
    (bytes : Nat) (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit)
      (wasmRetSig retTys)) (hk : ∀ p, (k p).callsOk allowed exits) :
    (emitMemBounds retTys vc f idx arg bytes k).callsOk allowed exits := ⟨hk _, trivial⟩

theorem emitMemSize_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (vc : Arg (fun _ => Unit) T.i64)
    (k : Arg (fun _ => Unit) T.i32 → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ p, (k p).callsOk allowed exits) :
    (emitMemSize vc k).callsOk allowed exits := hk _

theorem emitMemZeroPage_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (pPtr : Arg (fun _ => Unit) T.i64) (kDone : Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : kDone.callsOk allowed exits) :
    (emitMemZeroPage pPtr kDone).callsOk allowed exits := by
  simp only [emitMemZeroPage, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | exact hk | apply And.intro)

theorem emitMemGrowLoop_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (jDone : Unit) (pLen newLen : Arg (fun _ => Unit) T.i64)
    (op32 : Arg (fun _ => Unit) T.i32) (f d64 sp : Arg (fun _ => Unit) T.i64) :
    (emitMemGrowLoop retTys jDone pLen newLen op32 f d64 sp).callsOk allowed exits := by
  simp only [emitMemGrowLoop, emitMemZeroPage, mkTrapExpr, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | apply And.intro)

theorem emitMemGrow_callsOk (allowed : List SigEntry) (exits : List Sym) (retTys : List WValTy)
    (memMaxBytes : BitVec 64) (vc f : Arg (fun _ => Unit) T.i64) (d32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Arg (fun _ => Unit) T.i32 →
      Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f' r, (k f' r).callsOk allowed exits) :
    (emitMemGrow retTys memMaxBytes vc f d32 k).callsOk allowed exits := by
  simp only [emitMemGrow, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | exact hk _ _ |
    exact emitMemGrowLoop_callsOk allowed exits _ _ _ _ _ _ _ _ | apply And.intro)

theorem emitMemFillLoop_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (jAfter : Unit) (bv : Arg (fun _ => Unit) T.i8)
    (f n64 dp0 : Arg (fun _ => Unit) T.i64) :
    (emitMemFillLoop retTys jAfter bv f n64 dp0).callsOk allowed exits := by
  simp only [emitMemFillLoop, mkTrapExpr, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | apply And.intro)

theorem emitMemFill_callsOk (allowed : List SigEntry) (exits : List Sym) (retTys : List WValTy)
    (vc f : Arg (fun _ => Unit) T.i64) (d32 v32 n32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f', (k f').callsOk allowed exits) :
    (emitMemFill retTys vc f d32 v32 n32 k).callsOk allowed exits := by
  simp only [emitMemFill, emitLoadVmCtx, mkTrapExpr, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | exact hk _ |
    exact emitMemFillLoop_callsOk allowed exits _ _ _ _ _ _ | apply And.intro)

theorem emitMemCopyLoop_callsOk (allowed : List SigEntry) (exits : List Sym) (fwd : Bool)
    (retTys : List WValTy) (jAfter : Unit) (f n64 dp0 sp0 : Arg (fun _ => Unit) T.i64) :
    (emitMemCopyLoop fwd retTys jAfter f n64 dp0 sp0).callsOk allowed exits := by
  cases fwd <;> simp only [emitMemCopyLoop, mkTrapExpr, Expr.callsOk, Blocks.callsOk,
    Bool.false_eq_true, ↓reduceIte] <;> repeat (first | exact trivial | apply And.intro)

theorem emitMemCopy_callsOk (allowed : List SigEntry) (exits : List Sym) (retTys : List WValTy)
    (vc f : Arg (fun _ => Unit) T.i64) (d32 s32 n32 : Arg (fun _ => Unit) T.i32)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ f', (k f').callsOk allowed exits) :
    (emitMemCopy retTys vc f d32 s32 n32 k).callsOk allowed exits := by
  simp only [emitMemCopy, emitLoadVmCtx, mkTrapExpr, Expr.callsOk, Blocks.callsOk]
  repeat (first | exact trivial | exact hk _ |
    exact emitMemCopyLoop_callsOk allowed exits _ _ _ _ _ _ _ | apply And.intro)

end LeanQbe.T.Wasm
