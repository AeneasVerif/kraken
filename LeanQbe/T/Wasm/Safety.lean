module

public import LeanQbe.T.Wasm.Lower
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.Arith
public import LeanQbe.T.LinkLfp
public import LeanQbe.T.Module
public import LeanQbe.T.InlineLemmas

/-!
# Universal WebAssembly Sandbox Memory Safety (`WasmSandboxInv`)

Proves universal total-correctness memory safety and host-frame preservation for ANY WebAssembly
module lowered via `LeanQbe.T.Wasm.lowerModule`:

* `WasmMemInv`: separates guest linear memory `[memBase, memBase + memLen)` (`region memBase
  memLen.toNat`) from an arbitrary host memory frame `R : Mem 64 → Prop`.
* `WasmPost`: guarantees clean return status (`0#32` OK, `1#32` trap, or `2#32` out-of-fuel),
  monotone fuel (`remFuel ≤ fuel`), and `WasmMemInv` preservation.
* `lowerFuncBody_wp`: universal `Func.wp` theorem covering every instruction (SFI bounds-checked
  8/16/32/64-bit loads/stores, division/remainder trap guards, SWAR popcnt, structured
  `block`/`loop`/`if`/`br`/`br_if`/`br_table`/`return`, and fuel-bounded `call`).
* `lowerModule_moduleSccOk` & `lowerModule_semScc`: universal `ModuleSccOk` and `Env.semScc`
  soundness for arbitrary validated Wasm modules (`validateModule m = true`), including recursive
  and mutually recursive Wasm guests.
* `lowerModule_moduleOk` & `wasm_preserves_host_mem`: acyclic `ModuleOk` wrapper (for modules with
  `(lowerModule m).checkAcyclic = true`) and user-facing host-memory preservation corollary.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Wasm

open LeanQbe.T LeanQbe.T.LinkScc

/-! ## Equational `wp` & `Closed` Helpers -/

private theorem wp_let_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.let_ op k) m = op.wp (fun r => wp Γ Q X (k r) m) := by
  simp only [wp]

private theorem wp_load_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (a : Arg Val T.i64) (k : Val t → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.load t a k) m = ∃ v, loadVal m t a.val = some v ∧ wp Γ Q X (k v) m := by
  simp only [wp]

private theorem wp_store_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} (v : Arg Val t) (a : Arg Val T.i64) (k : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.store v a k) m = (storeOk m t a.val ∧ wp Γ Q X k (storeMem m t a.val v.val)) := by
  simp only [wp]

private theorem wp_call_ {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    (f : Sym) (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.call f (as := as) (bs := bs) args k) m =
      ∃ (P : Post bs) (E : XPost), Γ f as bs (vals args) m P E ∧
        (∀ r m', P r m' → wp Γ Q X (k r) m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m') := by
  simp only [wp]

private theorem wp_jnz_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (c : Arg Val Ty.bool) (t e : Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.jnz c t e) m = ((c.val = true → wp Γ Q X t m) ∧ (c.val = false → wp Γ Q X e m)) := by
  simp only [wp]

private theorem wp_jump_ {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    (j : Cont ts) (args : Tup (Arg Val) ts) (m : Mem 64) :
    wp Γ Q X (.jump j args) m = j (vals args) m := by
  simp only [wp]

private theorem wp_ret_ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (vs : Tup (Arg Val) rs) (m : Mem 64) :
    wp Γ Q X (.ret vs) m = Q (vals vs) m := by
  simp only [wp]

private theorem wp_group_ {Γ : Env} {rs : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} (bodies : Tup Cont sig → Blocks Val Cont rs sig)
    (k : Tup Cont sig → Expr Val Cont rs) (m : Mem 64) :
    wp Γ Q X (.group bodies k) m = ∀ Js, Closed Γ Q X (bodies Js) Js → wp Γ Q X (k Js) m := by
  simp only [wp]

private theorem closed_cons_ {Γ : Env} {rs : List Ty} {ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} (b : Tup Val ts → Expr Val Cont rs) (bs : Blocks Val Cont rs sig)
    (Js : Tup Cont (ts :: sig)) :
    Closed Γ Q X (.cons b bs) Js =
      ((∀ xs m, wp Γ Q X (b xs) m → Js.1 xs m) ∧ Closed Γ Q X bs Js.2) := by
  simp only [Closed]

/-! ## Sandbox Invariant, Postcondition & Region Framing -/

/-- Host-guest memory separation invariant: when linear memory is present (`hasMem = true`), the
guest's `memLen` bytes at `memBase` are separated (`⋆`) from arbitrary host frame `R`. When
`hasMem = false`, all memory belongs to `R` and any guest `load`/`store` traps safely. -/
@[reducible] def WasmMemInv (hasMem : Bool) (memBase memLen : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) : Prop :=
  if hasMem then (region memBase memLen.toNat ⋆ R) mem else R mem

/-- Universal WebAssembly sandbox return postcondition: status is in `{0#32, 1#32, 2#32}`, remaining
fuel never exceeds entry `fuel`, and the host frame `R` outside linear memory is preserved. -/
def WasmPost (hasMem : Bool) (memBase memLen fuel : BitVec 64)
    (retTys : List WValTy) (R : Mem 64 → Prop) : Post (wasmRetSig retTys) :=
  fun ys mem' =>
    (ys.1 = 0#32 ∨ ys.1 = 1#32 ∨ ys.1 = 2#32) ∧
    ys.2.1.toNat ≤ fuel.toNat ∧
    WasmMemInv hasMem memBase memLen R mem'

theorem WasmPost.mono_fuel {hasMem : Bool} {memBase memLen f₁ f₂ : BitVec 64}
    (hle : f₁.toNat ≤ f₂.toNat) {retTys : List WValTy} {R : Mem 64 → Prop} {ys mem'}
    (h : WasmPost hasMem memBase memLen f₁ retTys R ys mem') :
    WasmPost hasMem memBase memLen f₂ retTys R ys mem' :=
  ⟨h.1, Nat.le_trans h.2.1 hle, h.2.2⟩

/-- Function-level sandbox specification at recursion bound `i` (fuel cap). -/
def WasmFnSpec (hasMem : Bool) (ft : WFuncTy) (i : Nat) :
    Spec (wasmAbiParams ft) (wasmAbiResults ft) :=
  fun xs mem Q _ =>
    xs.2.2.1.toNat ≤ i ∧
    ∃ R : Mem 64 → Prop,
      WasmMemInv hasMem xs.1 xs.2.1 R mem ∧
      ∀ ys mem', WasmPost hasMem xs.1 xs.2.1 xs.2.2.1 ft.results R ys mem' → Q ys mem'

/-- Parameterized sandbox environment mapping each lowered Wasm function at fuel bound `i` to
`WasmFnSpec`. -/
def WasmSandboxEnv (m : WModule) (i : Nat) : Env :=
  fun f as bs xs mem Q X =>
    ∃ fn ∈ m.funcs,
      ∃ (ha : as = wasmAbiParams ((m.types[fn.typeIdx]?).getD {}))
        (hb : bs = wasmAbiResults ((m.types[fn.typeIdx]?).getD {})),
        f = fn.name ∧
        WasmFnSpec m.memory.isSome ((m.types[fn.typeIdx]?).getD {}) i
          (ha ▸ xs) mem (hb ▸ Q) X

private theorem region_focus_eq (base : BitVec 64) (len ea k : Nat)
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

private theorem region_load_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat}
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

private theorem region_store_bits {n : Nat} (hn : n = 8 * (Ty.bits n).bytes)
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

private theorem region_store_w (w : WMemWidth) {base : BitVec 64} {len ea : Nat}
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

private theorem memBounds_toNat {idx32 off32 : BitVec 32} {bytes : Nat} {memLen : BitVec 64}
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

/-! ## Instruction & Structured Control WP Lemmas -/

private theorem wp_mkTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} (retTys : List WValTy) (code : BitVec 32)
    (hc : code = 0#32 ∨ code = 1#32 ∨ code = 2#32) {fuel : Arg Val T.i64}
    (hf : fuel.val.toNat ≤ fuel0.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem memBase memLen R mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (mkTrapExpr retTys code fuel) mem := by
  simp only [mkTrapExpr]
  rw [wp_ret_]
  exact ⟨hc, hf, hm⟩

private theorem wp_mkStatusTrapExpr {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} (retTys : List WValTy)
    {status : Arg Val T.i32} (hs : status.val = 0#32 ∨ status.val = 1#32 ∨ status.val = 2#32)
    {remFuel : Arg Val T.i64} (hf : remFuel.val.toNat ≤ fuel0.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (mkStatusTrapExpr retTys status remFuel) mem := by
  simp only [mkStatusTrapExpr]
  rw [wp_ret_]
  exact ⟨hs, hf, hm⟩

private theorem wp_pure_bin {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {n : Nat} (code : OpCode [.bits n, .bits n] [.bits n])
    (hc : code = .lshr (.bits n) ∨ code = .and (.bits n) ∨ code = .sub (.bits n) ∨
          code = .add (.bits n) ∨ code = .mul (.bits n))
    (x y : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs)
    (hk : ∀ r, wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.let_ (.mk code (x, y, ())) k) m := by
  rw [wp_let_]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
    exact hk _

private theorem emitPopcnt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (w : WValTy) (x : Arg Val w.toTy) (k : Arg Val w.toTy → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitPopcnt w x k) m := by
  cases w <;> simp only [emitPopcnt] <;>
  repeat first
    | exact hk _
    | refine wp_pure_bin _ (by simp) _ _ _ fun _ => ?_

private theorem emitUnOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem)
    (w : WValTy) (op : WUnOp) (x : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (emitUnOp retTys fuel w op x k) mem := by
  cases w <;> cases op <;> simp only [emitUnOp]
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact hk _
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact hk _
  · exact emitPopcnt_wp .i32 x k hk
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]; simp only [Op.wp, OpCode.wp]; refine ⟨by decide, hk _⟩
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]; simp only [Op.wp, OpCode.wp]; refine ⟨by decide, hk _⟩
  · exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hm
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact hk _
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact hk _
  · exact emitPopcnt_wp .i64 x k hk
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]; simp only [Op.wp, OpCode.wp]; refine ⟨by decide, hk _⟩
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]; simp only [Op.wp, OpCode.wp]; refine ⟨by decide, hk _⟩
  · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]; simp only [Op.wp, OpCode.wp]; refine ⟨by decide, hk _⟩

private theorem sdivDefined_of_guards {n : Nat} {a b minConst neg1Const : BitVec n}
    (hiMin : BitVec.intMin n = minConst) (hiAll : BitVec.allOnes n = neg1Const)
    (hz : decide (b = 0#n) = false)
    (hov : (decide (a = minConst) && decide (b = neg1Const)) = false) :
    sdivDefined a b = true := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  simp only [decide_eq_false_iff_not, Bool.and_eq_false_iff] at hz hov
  refine ⟨by simpa using hz, ?_⟩
  rw [hiMin, hiAll]
  exact hov

private theorem arg_imm_val {t : Ty} (c : Val t) : (Arg.imm c).val = c := rfl
private theorem arg_var_val {t : Ty} (v : Val t) : (Arg.var v).val = v := rfl

private theorem emitBinOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem)
    (w : WValTy) (op : WBinOp) (a b : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (emitBinOp retTys fuel w op a b k) mem := by
  have htrap : wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (mkTrapExpr retTys 1#32 fuel) mem :=
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hm
  cases op <;> cases w <;> simp only [emitBinOp] <;>
  first
  | (rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals, arg_imm_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
     exact hk _)
  | (rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals, arg_imm_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
       liftCmp, CmpOp.evalBits]
     rw [wp_jnz_]
     refine ⟨fun _ => htrap, fun hz => ?_⟩
     rw [arg_var_val] at hz
     simp only [wp_let_, Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
       Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
     rw [wp_jnz_]
     refine ⟨fun _ => htrap, fun hov => ?_⟩
     rw [arg_var_val] at hov
     rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals]
     refine ⟨sdivDefined_of_guards rfl rfl hz hov, hk _⟩)
  | (rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals, arg_imm_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
       liftCmp, CmpOp.evalBits]
     rw [wp_jnz_]
     refine ⟨fun _ => htrap, fun hz => ?_⟩
     rw [arg_var_val] at hz
     simp only [wp_let_, Op.wp, OpCode.wp, vals, arg_imm_val, arg_var_val, Ty.hasFloat,
       Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
     rw [wp_jnz_]
     refine ⟨fun _ => hk _, fun hov => ?_⟩
     rw [arg_var_val] at hov
     rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals]
     refine ⟨sdivDefined_of_guards rfl rfl hz hov, hk _⟩)
  | (rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals, arg_imm_val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
       liftCmp, CmpOp.evalBits]
     rw [wp_jnz_]
     refine ⟨fun _ => htrap, fun hz => ?_⟩
     rw [arg_var_val] at hz
     have hz' := of_decide_eq_false hz
     rw [wp_let_]
     simp only [Op.wp, OpCode.wp, vals]
     exact ⟨by simpa [BitVec.toNat_eq] using hz', hk _⟩)

private theorem emitLoadCast_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem)
    (resTy : WValTy) (width : WMemWidth) (signed : Bool) (raw : Val width.memTy)
    (k : Arg Val resTy.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (emitLoadCast (mkTrapExpr retTys 1#32 fuel) resTy width signed raw k) mem := by
  have htrap : wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (mkTrapExpr retTys 1#32 fuel) mem :=
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hm
  cases resTy <;> cases width <;> cases signed <;> simp only [emitLoadCast] <;>
  first
  | exact htrap
  | exact hk _
  | (rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact ⟨by decide, hk _⟩)

private theorem emitStoreCast_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem)
    (srcTy : WValTy) (width : WMemWidth) (v : Arg Val srcTy.toTy)
    (k : Arg Val width.memTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (emitStoreCast (mkTrapExpr retTys 1#32 fuel) srcTy width v k) mem := by
  have htrap : wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (mkTrapExpr retTys 1#32 fuel) mem :=
    wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hm
  cases srcTy <;> cases width <;> simp only [emitStoreCast] <;>
  first
  | exact htrap
  | exact hk _
  | (rw [wp_let_]; simp only [Op.wp, OpCode.wp]; exact ⟨by decide, hk _⟩)

private theorem emitMemBounds_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {memBase memLen fuel0 : BitVec 64} {retTys : List WValTy}
    (mb ml f : Arg Val T.i64) (hmb : mb.val = memBase) (hml : ml.val = memLen)
    (hf : f.val.toNat ≤ fuel0.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem memBase memLen R mem)
    (idx : Arg Val T.i32) (arg : WMemArg) (w : WMemWidth)
    (k : Arg Val T.i64 → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ (ea : Nat), ea + w.bytes ≤ memLen.toNat →
      wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
        (k (.var (memBase + BitVec.ofNat 64 ea))) mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
      (emitMemBounds retTys mb ml f idx arg w.bytes k) mem := by
  simp only [emitMemBounds]
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
  refine ⟨fun hin => ?_, fun _ => wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hm⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, arg_var_val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  have hwb : w.bytes ≤ 8 := by cases w <;> decide
  have hin' : (((idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat) +
      BitVec.ofNat 64 w.bytes).ule memLen) = true := by
    rw [arg_var_val] at hin
    rw [← hml]; exact hin
  have hnat := memBounds_toNat hwb hin'
  have hptr : mb.val + (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat) =
      memBase + BitVec.ofNat 64
        (idx.val.setWidth 64 + BitVec.ofNat 64 arg.offset.toNat).toNat := by
    rw [hmb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hptr]
  exact hk _ hnat

/-- Predicate asserting that every control label `l ∈ labs` enforces fuel bound `≤ fuel` and
preserves `WasmMemInv`. -/
def LabsSafe (locTys : List WValTy) (hasMem : Bool) (memBase memLen fuel : BitVec 64)
    (R : Mem 64 → Prop) (labs : List (WLabel Val Cont locTys)) : Prop :=
  ∀ l ∈ labs, ∀ (xs : Tup Val (labelSig locTys l.argTys)) mem',
    xs.1.toNat ≤ fuel.toNat → WasmMemInv hasMem memBase memLen R mem' → l.lbl xs mem'

private theorem LabsSafe.mono_fuel {locTys : List WValTy} {hasMem : Bool}
    {memBase memLen f₁ f₂ : BitVec 64} (hle : f₁.toNat ≤ f₂.toNat)
    {R : Mem 64 → Prop} {labs : List (WLabel Val Cont locTys)}
    (hl : LabsSafe locTys hasMem memBase memLen f₂ R labs) :
    LabsSafe locTys hasMem memBase memLen f₁ R labs :=
  fun l hlmem xs m' hf hm => hl l hlmem xs m' (Nat.le_trans hf hle) hm

private theorem eqRec_cont_wp {locTys : List WValTy} {ts₁ ts₂ : List WValTy}
    {hasMem : Bool} {memBase memLen fuel : BitVec 64} {R : Mem 64 → Prop}
    (h : ts₁ = ts₂) (J : Cont (labelSig locTys ts₁))
    (args : Tup Val (labelSig locTys ts₂)) (m : Mem 64)
    (hJ : ∀ xs m', xs.1.toNat ≤ fuel.toNat → WasmMemInv hasMem memBase memLen R m' → J xs m')
    (hf : args.1.toNat ≤ fuel.toNat) (hm : WasmMemInv hasMem memBase memLen R m) :
    (h ▸ J) args m := by
  subst h
  exact hJ args m hf hm

private theorem emitBrTable_wp {Γ : Env} {X : XPost} {locTys retTys : List WValTy}
    {hasMem : Bool} {memBase memLen fuel0 curFuel : BitVec 64} {R : Mem 64 → Prop}
    (labs : List (WLabel Val Cont locTys))
    (hlabs : LabsSafe locTys hasMem memBase memLen curFuel R labs)
    (locs : Tup (Arg Val) (locTys.map WValTy.toTy))
    (f : Arg Val T.i64) (hf0 : f.val.toNat ≤ fuel0.toNat) (hf : f.val.toNat ≤ curFuel.toNat)
    (idx : Arg Val T.i32) (defLbl : WLabel Val Cont locTys) (hdef : defLbl ∈ labs)
    (ba : Tup (Arg Val) (defLbl.argTys.map WValTy.toTy))
    {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem) :
    ∀ (i : Nat) (ts : List Nat),
      wp Γ (WasmPost hasMem memBase memLen fuel0 retTys R) X
        (emitBrTable locTys retTys labs locs f idx defLbl ba i ts) mem := by
  intro i ts
  induction ts generalizing i with
  | nil =>
    simp only [emitBrTable]
    rw [wp_jump_]
    exact hlabs defLbl hdef _ mem hf hm
  | cons t rest ih =>
    simp only [emitBrTable]
    cases hget : labs[t]? with
    | none => exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hm
    | some lbl =>
      have hlblMem : lbl ∈ labs := List.mem_of_getElem? hget
      by_cases hty : lbl.argTys = defLbl.argTys
      · simp only [hty, ↓reduceDIte]
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, CmpOp.evalBits]
        rw [wp_jnz_]
        refine ⟨fun _ => ?_, fun _ => ih (i + 1)⟩
        rw [wp_jump_]
        exact eqRec_cont_wp hty lbl.lbl (vals (f, tupAppend locs ba)) mem
          (hlabs lbl hlblMem) hf hm
      · simp only [hty, ↓reduceDIte]
        exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hm

/-- Callee environment invariant: any valid function call at strictly smaller fuel `f' < fuelBound`
satisfies `WasmPost` while preserving arbitrary host memory `R`. -/
def WasmCalleeEnvOk (Γ : Env) (funcs : List WFunc) (types : List WFuncTy)
    (hasMem : Bool) (memBase memLen fuelBound : BitVec 64) (R : Mem 64 → Prop) : Prop :=
  ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
    funcs[fnIdx]? = some callee → types[callee.typeIdx]? = some ft →
    ∀ (f' : BitVec 64) args mem', f'.toNat < fuelBound.toNat →
      WasmMemInv hasMem memBase memLen R mem' →
      Γ callee.name (wasmAbiParams ft) (wasmAbiResults ft) (memBase, memLen, f', args) mem'
        (WasmPost hasMem memBase memLen f' ft.results R) (fun _ _ _ _ => False)

private theorem vals_wasmAbi (ft : WFuncTy) (mb ml f : Arg Val T.i64)
    (ca : Tup (Arg Val) (ft.params.map WValTy.toTy)) :
    vals (ts := wasmAbiParams ft) (mb, ml, f, ca) = (mb.val, ml.val, f.val, vals ca) := rfl

private theorem WasmCalleeEnvOk.mono_fuel {Γ : Env} {funcs : List WFunc} {types : List WFuncTy}
    {hasMem : Bool} {memBase memLen f₁ f₂ : BitVec 64} (hle : f₁.toNat ≤ f₂.toNat)
    {R : Mem 64 → Prop}
    (h : WasmCalleeEnvOk Γ funcs types hasMem memBase memLen f₂ R) :
    WasmCalleeEnvOk Γ funcs types hasMem memBase memLen f₁ R :=
  fun idx c ft hc hft f' args m' hlt hm =>
    h idx c ft hc hft f' args m' (Nat.lt_of_lt_of_le hlt hle) hm

private theorem bv64_sub_one_lt {x : BitVec 64} (hne : x ≠ 0#64) :
    (x - 1#64).toNat < x.toNat := by
  have hx0 : 0 < x.toNat := Nat.pos_of_ne_zero fun hz =>
    hne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsub : (x - 1#64).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub]
    have hlt := x.isLt
    simp only [h1]
    omega
  omega

private theorem lowerSimpleInstr_wp {Γ : Env} {X : XPost} (ctx : WLowerCtx)
    {hasMem : Bool} (hmem : ctx.hasMem = hasMem) {memBase memLen fuel0 : BitVec 64}
    {R : Mem 64 → Prop} (mb ml f : Arg Val T.i64)
    (hmb : mb.val = memBase) (hml : ml.val = memLen) (hf0 : f.val.toNat ≤ fuel0.toNat)
    (hcal : WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem memBase memLen f.val R)
    (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
    (labs : List (WLabel Val Cont ctx.locTys))
    (hlabs : LabsSafe ctx.locTys hasMem memBase memLen f.val R labs)
    (instr : WInstr) (k : WCont Val Cont ctx.locTys ctx.retTys)
    (hk : ∀ f' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
      WasmMemInv hasMem memBase memLen R mem' →
      LabsSafe ctx.locTys hasMem memBase memLen f'.val R labs →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem memBase memLen f'.val R →
      wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X (k f' locs' stk') mem')
    {mem : Mem 64} (hm : WasmMemInv hasMem memBase memLen R mem) :
    wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X
      (lowerSimpleInstr ctx mb ml f locs stk labs instr k) mem := by
  have htrap : wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X
      (mkTrapExpr ctx.retTys 1#32 f) mem :=
    wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hm
  have hk0 : ∀ (locs' : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) stk',
      wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X (k f locs' stk') mem :=
    fun locs' stk' => hk f locs' stk' mem (Nat.le_refl _) hm hlabs hcal
  cases instr with
  | nop => exact hk0 locs stk
  | br_if depth =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨c, r⟩
      cases hget : labs[depth]? with
      | none => exact htrap
      | some lbl =>
        have hlblMem : lbl ∈ labs := List.mem_of_getElem? hget
        dsimp only
        cases popArgsAux lbl.argTys r with
        | none => exact htrap
        | some p' =>
          rcases p' with ⟨ba, _⟩
          dsimp only
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
            liftCmp, CmpOp.evalBits]
          rw [wp_jnz_]
          refine ⟨fun _ => ?_, fun _ => hk0 locs r⟩
          rw [wp_jump_]
          exact hlabs lbl hlblMem _ mem (Nat.le_refl _) hm
  | call fnIdx =>
    simp only [lowerSimpleInstr]
    cases hc : ctx.funcs[fnIdx]? with
    | none => exact htrap
    | some callee =>
      dsimp only
      cases hft : ctx.types[callee.typeIdx]? with
      | none => exact htrap
      | some ft =>
        dsimp only
        cases popArgsAux ft.params stk with
        | none => exact htrap
        | some p =>
          rcases p with ⟨ca, s1⟩
          dsimp only
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
            liftCmp, CmpOp.evalBits]
          rw [wp_jnz_]
          refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl)) hf0 hm, fun hz => ?_⟩
          have hne : f.val ≠ 0#64 := decide_eq_false_iff_not.mp hz
          have hlt : (f.val - 1#64).toNat < f.val.toNat := bv64_sub_one_lt hne
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
            Bool.false_eq_true, ↓reduceIte]
          rw [wp_call_]
          refine ⟨WasmPost hasMem memBase memLen (f.val - 1#64) ft.results R,
            fun _ _ _ _ => False, ?_, ?_, fun _ _ _ _ h => False.elim h⟩
          · rw [vals_wasmAbi, hmb, hml]
            exact hcal fnIdx callee ft hc hft (f.val - 1#64) (vals ca) mem hlt hm
          · intro r m' ⟨hst, hrf, hm'⟩
            rw [wp_let_]
            simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
              ↓reduceIte, liftCmp, CmpOp.evalBits]
            rw [wp_jnz_]
            have hle : r.2.1.toNat ≤ f.val.toNat := Nat.le_trans hrf (Nat.le_of_lt hlt)
            refine ⟨fun _ => hk (.var r.2.1) locs (pushArgsAux ft.results (varsTup r.2.2) s1) m'
              hle hm' (LabsSafe.mono_fuel hle hlabs) (WasmCalleeEnvOk.mono_fuel hle hcal),
              fun _ => wp_mkStatusTrapExpr ctx.retTys (status := .var r.1) hst
                (Nat.le_trans hle hf0) hm'⟩
  | drop =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap
    | cons _ r => exact hk0 locs r
  | select =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨c, r⟩
      cases r with
      | nil => exact htrap
      | cons v₂ r2 =>
        cases r2 with
        | nil => cases v₂ <;> exact htrap
        | cons v₁ r3 =>
          cases v₂ <;> cases v₁ <;> dsimp only
          · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
            rw [wp_let_]; simp only [Op.wp, OpCode.wp]
            exact hk0 locs _
          · exact htrap
          · exact htrap
          · rw [wp_let_]; simp only [Op.wp, OpCode.wp]
            rw [wp_let_]; simp only [Op.wp, OpCode.wp]
            exact hk0 locs _
  | local_get idx =>
    simp only [lowerSimpleInstr]
    cases getLocal ctx.locTys locs idx with
    | none => exact htrap
    | some v => exact hk0 locs (v :: stk)
  | local_set idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap
    | cons v r =>
      dsimp only
      cases setLocal ctx.locTys locs idx v with
      | none => exact htrap
      | some locs' => exact hk0 locs' r
  | local_tee idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap
    | cons v r =>
      dsimp only
      cases setLocal ctx.locTys locs idx v with
      | none => exact htrap
      | some locs' => exact hk0 locs' (v :: r)
  | global_get idx =>
    simp only [lowerSimpleInstr]
    cases ctx.globals[idx]? with
    | none => exact htrap
    | some g => exact hk0 locs _
  | load resTy width signed arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]
      have hhm : hasMem = true := by
        simp only [Bool.and_eq_true] at hok; rw [← hmem, hok.1]
      cases pop32 stk with
      | none => exact htrap
      | some p =>
        rcases p with ⟨idx32, s1⟩
        dsimp only
        refine emitMemBounds_wp mb ml f hmb hml hf0 hm idx32 arg width _ fun ea hba => ?_
        have hreg : (region memBase memLen.toNat ⋆ R) mem := by
          simpa [WasmMemInv, hhm] using hm
        have hlen : memLen.toNat ≤ 2 ^ 64 := Nat.le_of_lt memLen.isLt
        rcases region_load_w width hlen hba hreg with ⟨raw, hraw⟩
        rw [wp_load_]
        refine ⟨raw, hraw, ?_⟩
        exact emitLoadCast_wp hf0 hm resTy width signed raw _ fun v =>
          hk0 locs (SVal.ofArg resTy v :: s1)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | store srcTy width arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]
      have hhm : hasMem = true := by
        simp only [Bool.and_eq_true] at hok; rw [← hmem, hok.1]
      cases popExpectS srcTy stk with
      | none => exact htrap
      | some p =>
        rcases p with ⟨sv, s1⟩
        dsimp only
        cases pop32 s1 with
        | none => exact htrap
        | some p2 =>
          rcases p2 with ⟨idx32, s2⟩
          dsimp only
          refine emitMemBounds_wp mb ml f hmb hml hf0 hm idx32 arg width _ fun ea hba => ?_
          refine emitStoreCast_wp hf0 hm srcTy width sv _ fun memVal => ?_
          have hreg : (region memBase memLen.toNat ⋆ R) mem := by
            simpa [WasmMemInv, hhm] using hm
          have hlen : memLen.toNat ≤ 2 ^ 64 := Nat.le_of_lt memLen.isLt
          rcases region_store_w width hlen hba memVal.val hreg with ⟨hsok, hmem'⟩
          rw [wp_store_]
          refine ⟨hsok, ?_⟩
          have hm' : WasmMemInv hasMem memBase memLen R
              (storeMem mem width.memTy (memBase + BitVec.ofNat 64 ea) memVal.val) := by
            simpa [WasmMemInv, hhm] using hmem'
          exact hk f locs s2 _ (Nat.le_refl _) hm' hlabs hcal
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | memory_size =>
    simp only [lowerSimpleInstr]
    by_cases hmFlag : ctx.hasMem = true
    · simp only [hmFlag, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp]
      exact ⟨by decide, hk0 locs _⟩
    · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | memory_grow =>
    simp only [lowerSimpleInstr]
    by_cases hmFlag : ctx.hasMem = true
    · simp only [hmFlag, ↓reduceIte]
      cases pop32 stk with
      | none => exact htrap
      | some p =>
        rcases p with ⟨_, s1⟩
        dsimp only
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp]
        refine ⟨by decide, ?_⟩
        rw [wp_let_]
        simp only [Op.wp, OpCode.wp]
        exact hk0 locs _
    · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | i32_const _ => exact hk0 locs _
  | i64_const _ => exact hk0 locs _
  | eqz w =>
    simp only [lowerSimpleInstr]
    cases w with
    | i32 =>
      cases stk with
      | nil => exact htrap
      | cons x _ =>
        cases x with
        | i32 _ =>
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
          rw [wp_let_]; simp only [Op.wp, OpCode.wp]
          exact hk0 locs _
        | i64 _ => exact htrap
    | i64 =>
      cases stk with
      | nil => exact htrap
      | cons x _ =>
        cases x with
        | i32 _ => exact htrap
        | i64 _ =>
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
          rw [wp_let_]; simp only [Op.wp, OpCode.wp]
          exact hk0 locs _
  | unop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨x, s1⟩
      dsimp only
      exact emitUnOp_wp hf0 hm w op x _ fun y => hk0 locs (SVal.ofArg w y :: s1)
  | binop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨b, s1⟩
      dsimp only
      cases popExpectS w s1 with
      | none => exact htrap
      | some p2 =>
        rcases p2 with ⟨a, s2⟩
        dsimp only
        exact emitBinOp_wp hf0 hm w op a b _ fun y => hk0 locs (SVal.ofArg w y :: s2)
  | relop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨b, s1⟩
      dsimp only
      cases popExpectS w s1 with
      | none => exact htrap
      | some p2 =>
        rcases p2 with ⟨a, s2⟩
        dsimp only
        cases w <;>
        · rw [wp_let_]
          simp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
          rw [wp_let_]
          simp only [Op.wp, OpCode.wp]
          exact hk0 locs _
  | wrap_i64 =>
    simp only [lowerSimpleInstr]
    cases pop64 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨_, s1⟩
      dsimp only
      rw [wp_let_]; simp only [Op.wp, OpCode.wp]
      exact ⟨by decide, hk0 locs _⟩
  | extend_i32_s =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨_, s1⟩
      dsimp only
      rw [wp_let_]; simp only [Op.wp, OpCode.wp]
      exact ⟨by decide, hk0 locs _⟩
  | extend_i32_u =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨_, s1⟩
      dsimp only
      rw [wp_let_]; simp only [Op.wp, OpCode.wp]
      exact ⟨by decide, hk0 locs _⟩
  | unreachable => exact htrap
  | block _ _ => exact htrap
  | loop _ _ => exact htrap
  | if_ _ _ _ => exact htrap
  | br _ => exact htrap
  | br_table _ _ => exact htrap
  | return_ => exact htrap

/-- Universal WP theorem for `lowerSeq`: arbitrary instruction sequences preserve host frame `R`,
respect fuel bounds, and never trap outside `{1#32, 2#32}`. -/
theorem lowerSeq_wp_aux {Γ : Env} {X : XPost} (ctx : WLowerCtx)
    {hasMem : Bool} (hmem : ctx.hasMem = hasMem) {memBase memLen fuel0 : BitVec 64}
    {R : Mem 64 → Prop} (mb ml : Arg Val T.i64) (hmb : mb.val = memBase) (hml : ml.val = memLen) :
    ∀ (sz : Nat) (f : Arg Val T.i64),
      f.val.toNat ≤ fuel0.toNat →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem memBase memLen f.val R →
      ∀ (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
        (labs : List (WLabel Val Cont ctx.locTys)),
        LabsSafe ctx.locTys hasMem memBase memLen f.val R labs →
        ∀ (instrs : List WInstr), sizeOf instrs ≤ sz →
          ∀ (k : WCont Val Cont ctx.locTys ctx.retTys),
            (∀ f' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
              WasmMemInv hasMem memBase memLen R mem' →
              LabsSafe ctx.locTys hasMem memBase memLen f'.val R labs →
              WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem memBase memLen f'.val R →
              wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X (k f' locs' stk') mem') →
            ∀ {mem : Mem 64}, WasmMemInv hasMem memBase memLen R mem →
              wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X
                (lowerSeq ctx mb ml f locs stk labs instrs k) mem := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro f hf0 hcal locs stk labs hlabs instrs hsz k hk mem hm
    have htrap : wp Γ (WasmPost hasMem memBase memLen fuel0 ctx.retTys R) X
        (mkTrapExpr ctx.retTys 1#32 f) mem :=
      wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hm
    cases instrs with
    | nil =>
      simp only [lowerSeq]
      exact hk f locs stk mem (Nat.le_refl _) hm hlabs hcal
    | cons i rest =>
      have hszRest : sizeOf rest < sizeOf (i :: rest) := by simp +arith
      cases i with
      | unreachable => simp only [lowerSeq]; exact htrap
      | br depth =>
        simp only [lowerSeq]
        cases hget : labs[depth]? with
        | none => exact htrap
        | some lbl =>
          have hlblMem : lbl ∈ labs := List.mem_of_getElem? hget
          dsimp only
          cases popArgsAux lbl.argTys stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨ba, _⟩
            dsimp only
            rw [wp_jump_]
            exact hlabs lbl hlblMem _ mem (Nat.le_refl _) hm
      | br_table targets defTarget =>
        simp only [lowerSeq]
        cases pop32 stk with
        | none => exact htrap
        | some p =>
          rcases p with ⟨idx32, s1⟩
          cases hget : labs[defTarget]? with
          | none => exact htrap
          | some defLbl =>
            have hdefMem : defLbl ∈ labs := List.mem_of_getElem? hget
            dsimp only
            cases popArgsAux defLbl.argTys s1 with
            | none => exact htrap
            | some p' =>
              rcases p' with ⟨ba, _⟩
              dsimp only
              exact emitBrTable_wp labs hlabs locs f hf0 (Nat.le_refl _) idx32 defLbl hdefMem ba
                hm 0 targets
      | return_ =>
        simp only [lowerSeq]
        cases popArgsAux ctx.retTys stk with
        | none => exact htrap
        | some p =>
          rcases p with ⟨ra, _⟩
          dsimp only
          rw [wp_ret_]
          exact ⟨Or.inl rfl, hf0, hm⟩
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨ia, sa⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            rw [wp_group_]
            intro Js hcl
            rw [closed_cons_] at hcl
            have hJoin : ∀ xs m', xs.1.toNat ≤ f.val.toNat →
                WasmMemInv hasMem memBase memLen R m' → Js.1 xs m' := by
              intro xs m' hxs hm'
              apply hcl.1 xs m'
              exact ih _ hszRest' (.var xs.1) (Nat.le_trans hxs hf0)
                (WasmCalleeEnvOk.mono_fuel hxs hcal) _ _ labs
                (LabsSafe.mono_fuel hxs hlabs) rest (Nat.le_refl _) k
                (fun f' locs' stk' m'' hf' hm'' hl' hc' =>
                  hk f' locs' stk' m'' (Nat.le_trans hf' hxs) hm'' hl' hc') hm'
            let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.results, Js.1⟩
            have hlabs' : LabsSafe ctx.locTys hasMem memBase memLen f.val R (lbl' :: labs) := by
              intro l hl xs m' hxs hm'
              rcases List.mem_cons.mp hl with rfl | hl
              · exact hJoin xs m' hxs hm'
              · exact hlabs l hl xs m' hxs hm'
            refine ih _ hszBody f hf0 hcal locs _ (lbl' :: labs) hlabs' body (Nat.le_refl _) _
              (fun f' locs' stk' m' hf' hm' _ _ => ?_) hm
            cases popArgsAux ft.results stk' with
            | none =>
              exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl))
                (Nat.le_trans hf' hf0) hm'
            | some p' =>
              rcases p' with ⟨ra, _⟩
              dsimp only
              rw [wp_jump_]
              exact hJoin _ m' hf' hm'
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨ia, sa⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            rw [wp_group_]
            intro JsAfter hclAfter
            rw [closed_cons_] at hclAfter
            have hAfter : ∀ xs m', xs.1.toNat ≤ f.val.toNat →
                WasmMemInv hasMem memBase memLen R m' → JsAfter.1 xs m' := by
              intro xs m' hxs hm'
              apply hclAfter.1 xs m'
              exact ih _ hszRest' (.var xs.1) (Nat.le_trans hxs hf0)
                (WasmCalleeEnvOk.mono_fuel hxs hcal) _ _ labs
                (LabsSafe.mono_fuel hxs hlabs) rest (Nat.le_refl _) k
                (fun f' locs' stk' m'' hf' hm'' hl' hc' =>
                  hk f' locs' stk' m'' (Nat.le_trans hf' hxs) hm'' hl' hc') hm'
            rw [wp_group_]
            intro JsHdr hclHdr
            rw [closed_cons_] at hclHdr
            have hHdr : ∀ (n : Nat) (xs : Tup Val (labelSig ctx.locTys ft.params)) m',
                xs.1.toNat = n → n ≤ f.val.toNat →
                WasmMemInv hasMem memBase memLen R m' → JsHdr.1 xs m' := by
              intro n
              induction n using Nat.strongRecOn with
              | _ n ihn =>
                intro xs m' hxn hnf hm'
                apply hclHdr.1 xs m'
                rw [wp_let_]
                simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat,
                  Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
                rw [wp_jnz_]
                refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl))
                  (Nat.le_trans (hxn.symm ▸ hnf) hf0) hm', fun hz => ?_⟩
                have hne : xs.1 ≠ 0#64 := decide_eq_false_iff_not.mp hz
                have hlt : (xs.1 - 1#64).toNat < xs.1.toNat := bv64_sub_one_lt hne
                have hnextLe : (xs.1 - 1#64).toNat ≤ f.val.toNat := by omega
                rw [wp_let_]
                simp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
                let fNext : Arg Val T.i64 := .var (xs.1 - 1#64)
                let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.params, JsHdr.1⟩
                have hlabs' : LabsSafe ctx.locTys hasMem memBase memLen fNext.val R
                    (lbl' :: labs) := by
                  intro l hl ys m'' hys hm''
                  rcases List.mem_cons.mp hl with rfl | hl
                  · have hlt' : ys.1.toNat < n := Nat.lt_of_le_of_lt hys (hxn ▸ hlt)
                    exact ihn ys.1.toNat hlt' ys m'' rfl (Nat.le_trans (Nat.le_of_lt hlt') hnf) hm''
                  · exact hlabs l hl ys m'' (Nat.le_trans hys hnextLe) hm''
                refine ih _ hszBody fNext (Nat.le_trans hnextLe hf0)
                  (WasmCalleeEnvOk.mono_fuel hnextLe hcal) _ _ (lbl' :: labs) hlabs'
                  body (Nat.le_refl _) _ (fun f' locs' stk' m'' hf' hm'' _ _ => ?_) hm'
                have hf'Le : f'.val.toNat ≤ f.val.toNat := Nat.le_trans hf' hnextLe
                cases popArgsAux ft.results stk' with
                | none =>
                  exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl))
                    (Nat.le_trans hf'Le hf0) hm''
                | some p' =>
                  rcases p' with ⟨ra, _⟩
                  dsimp only
                  rw [wp_jump_]
                  exact hAfter _ m'' hf'Le hm''
            rw [wp_jump_]
            exact hHdr f.val.toNat _ mem rfl (Nat.le_refl _) hm
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases pop32 stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨cond, stk1⟩
            dsimp only
            cases popArgsAux ft.params stk1 with
            | none => exact htrap
            | some p' =>
              rcases p' with ⟨ia, sa⟩
              dsimp only
              have hszT : sizeOf thenBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              rw [wp_group_]
              intro Js hcl
              rw [closed_cons_] at hcl
              have hJoin : ∀ xs m', xs.1.toNat ≤ f.val.toNat →
                  WasmMemInv hasMem memBase memLen R m' → Js.1 xs m' := by
                intro xs m' hxs hm'
                apply hcl.1 xs m'
                exact ih _ hszRest' (.var xs.1) (Nat.le_trans hxs hf0)
                  (WasmCalleeEnvOk.mono_fuel hxs hcal) _ _ labs
                  (LabsSafe.mono_fuel hxs hlabs) rest (Nat.le_refl _) k
                  (fun f' locs' stk' m'' hf' hm'' hl' hc' =>
                    hk f' locs' stk' m'' (Nat.le_trans hf' hxs) hm'' hl' hc') hm'
              let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.results, Js.1⟩
              have hlabs' : LabsSafe ctx.locTys hasMem memBase memLen f.val R
                  (lbl' :: labs) := by
                intro l hl xs m' hxs hm'
                rcases List.mem_cons.mp hl with rfl | hl
                · exact hJoin xs m' hxs hm'
                · exact hlabs l hl xs m' hxs hm'
              rw [wp_let_]
              simp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
                liftCmp, CmpOp.evalBits]
              rw [wp_jnz_]
              refine ⟨fun _ => ?_, fun _ => ?_⟩
              · refine ih _ hszT f hf0 hcal locs _ (lbl' :: labs) hlabs' thenBody
                  (Nat.le_refl _) _ (fun f' locs' stk' m' hf' hm' _ _ => ?_) hm
                cases popArgsAux ft.results stk' with
                | none =>
                  exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl))
                    (Nat.le_trans hf' hf0) hm'
                | some p'' =>
                  rcases p'' with ⟨ra, _⟩
                  dsimp only
                  rw [wp_jump_]
                  exact hJoin _ m' hf' hm'
              · refine ih _ hszE f hf0 hcal locs _ (lbl' :: labs) hlabs' elseBody
                  (Nat.le_refl _) _ (fun f' locs' stk' m' hf' hm' _ _ => ?_) hm
                cases popArgsAux ft.results stk' with
                | none =>
                  exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl))
                    (Nat.le_trans hf' hf0) hm'
                | some p'' =>
                  rcases p'' with ⟨ra, _⟩
                  dsimp only
                  rw [wp_jump_]
                  exact hJoin _ m' hf' hm'
      | _ =>
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        exact lowerSimpleInstr_wp ctx hmem mb ml f hmb hml hf0 hcal locs stk labs hlabs _ _
          (fun f' locs' stk' m' hf' hm' hl' hc' =>
            ih _ hszRest' f' (Nat.le_trans hf' hf0) hc' locs' stk' labs hl' rest (Nat.le_refl _)
              k (fun f'' l'' s'' m'' hf'' hm'' hl'' hc'' =>
                hk f'' l'' s'' m'' (Nat.le_trans hf'' hf') hm'' hl'' hc'') hm')
          hm

/-! ## Function & Module Soundness (`Func.wp`, `ModuleSccOk`, `Env.semScc`, `ModuleOk`) -/

/-- Universal function-level safety theorem: ANY lowered Wasm function body satisfies
`WasmPost` and preserves arbitrary host memory `R` under `WasmCalleeEnvOk`. -/
theorem lowerFuncBody_wp {Γ : Env} {X : XPost} (m : WModule) (f : WFunc) (ft : WFuncTy)
    {xs : Tup Val (wasmAbiParams ft)} {mem : Mem 64} {R : Mem 64 → Prop}
    (hm : WasmMemInv m.memory.isSome xs.1 xs.2.1 R mem)
    (hcal : WasmCalleeEnvOk Γ m.funcs m.types m.memory.isSome xs.1 xs.2.1 xs.2.2.1 R) :
    Func.wp Γ (lowerFuncBody m f ft) xs mem
      (WasmPost m.memory.isSome xs.1 xs.2.1 xs.2.2.1 ft.results R) X := by
  simp only [Func.wp, lowerFuncBody]
  rw [wp_group_]
  intro Js hcl
  rw [closed_cons_] at hcl
  have hRet : ∀ rxs m', rxs.1.toNat ≤ xs.2.2.1.toNat →
      WasmMemInv m.memory.isSome xs.1 xs.2.1 R m' → Js.1 rxs m' := by
    intro rxs m' hr hm'
    apply hcl.1 rxs m'
    rw [wp_ret_]
    exact ⟨Or.inl rfl, hr, hm'⟩
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  let retLbl : WLabel Val Cont ctx.locTys := ⟨ft.results, Js.1⟩
  have hlabs : LabsSafe ctx.locTys m.memory.isSome xs.1 xs.2.1 xs.2.2.1 R [retLbl] := by
    intro l hl rxs m' hr hm'
    rcases List.mem_singleton.mp hl with rfl
    exact hRet rxs m' hr hm'
  refine lowerSeq_wp_aux ctx rfl (.var xs.1) (.var xs.2.1) rfl rfl (sizeOf f.body)
    (.var xs.2.2.1) (Nat.le_refl _) hcal _ [] [retLbl] hlabs f.body (Nat.le_refl _) _
    (fun f' _ stk' m' hf' hm' _ _ => ?_) hm
  cases popArgsAux ft.results stk' with
  | none => exact wp_mkTrapExpr ft.results 1#32 (Or.inr (Or.inl rfl)) hf' hm'
  | some p =>
    rcases p with ⟨ra, _⟩
    dsimp only
    rw [wp_ret_]
    exact ⟨Or.inl rfl, hf', hm'⟩

/-- `callsOk` preservation for lowered Wasm instruction helpers and sequences. -/
private theorem emitPopcnt_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (w : WValTy) (x : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) w.toTy → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitPopcnt w x k).callsOk allowed exits := by
  cases w <;> simp only [emitPopcnt, Expr.callsOk] <;> exact hk _

private theorem emitUnOp_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (f : Arg (fun _ => Unit) T.i64) (w : WValTy) (op : WUnOp)
    (x : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) w.toTy → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitUnOp retTys f w op x k).callsOk allowed exits := by
  cases w <;> cases op <;> simp only [emitUnOp, Expr.callsOk] <;>
  first | exact hk _ | exact emitPopcnt_callsOk allowed exits _ x k hk | trivial

private theorem emitBinOp_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (f : Arg (fun _ => Unit) T.i64) (w : WValTy) (op : WBinOp)
    (a b : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) w.toTy → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitBinOp retTys f w op a b k).callsOk allowed exits := by
  cases op <;> cases w <;> simp only [emitBinOp, Expr.callsOk] <;>
  first
  | exact hk _
  | exact ⟨trivial, hk _⟩
  | exact ⟨trivial, trivial, hk _⟩
  | exact ⟨trivial, hk _, hk _⟩

private theorem emitLoadCast_callsOk (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} {trap : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (htrap : trap.callsOk allowed exits) (resTy : WValTy) (width : WMemWidth) (signed : Bool)
    (raw : Unit) (k : Arg (fun _ => Unit) resTy.toTy → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitLoadCast trap resTy width signed raw k).callsOk allowed exits := by
  cases resTy <;> cases width <;> cases signed <;> simp only [emitLoadCast, Expr.callsOk] <;>
  first | exact htrap | exact hk _

private theorem emitStoreCast_callsOk (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} {trap : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (htrap : trap.callsOk allowed exits) (srcTy : WValTy) (width : WMemWidth)
    (v : Arg (fun _ => Unit) srcTy.toTy)
    (k : Arg (fun _ => Unit) width.memTy → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitStoreCast trap srcTy width v k).callsOk allowed exits := by
  cases srcTy <;> cases width <;> simp only [emitStoreCast, Expr.callsOk] <;>
  first | exact htrap | exact hk _

private theorem emitMemBounds_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (mb ml f : Arg (fun _ => Unit) T.i64)
    (idx : Arg (fun _ => Unit) T.i32) (arg : WMemArg) (bytes : Nat)
    (k : Arg (fun _ => Unit) T.i64 → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ p, (k p).callsOk allowed exits) :
    (emitMemBounds retTys mb ml f idx arg bytes k).callsOk allowed exits := by
  simp only [emitMemBounds, Expr.callsOk]
  exact ⟨hk _, trivial⟩

private theorem emitBrTable_callsOk (allowed : List SigEntry) (exits : List Sym)
    (locTys retTys : List WValTy)
    (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) locTys))
    (locs : Tup (Arg (fun _ => Unit)) (locTys.map WValTy.toTy))
    (f : Arg (fun _ => Unit) T.i64) (idx : Arg (fun _ => Unit) T.i32)
    (defLbl : WLabel (fun _ => Unit) (fun _ => Unit) locTys)
    (ba : Tup (Arg (fun _ => Unit)) (defLbl.argTys.map WValTy.toTy)) :
    ∀ (i : Nat) (ts : List Nat),
      (emitBrTable locTys retTys labs locs f idx defLbl ba i ts).callsOk allowed exits := by
  intro i ts
  induction ts generalizing i with
  | nil => simp [emitBrTable, Expr.callsOk]
  | cons t rest ih =>
    simp only [emitBrTable]
    cases labs[t]? with
    | none => exact trivial
    | some l =>
      by_cases hlt : l.argTys = defLbl.argTys
      · simp only [hlt, ↓reduceDIte, Expr.callsOk]
        exact ⟨trivial, ih (i + 1)⟩
      · simp only [hlt, ↓reduceDIte]; exact trivial

private theorem lowerSimpleInstr_callsOk (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym)
    (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed)
    (mb ml f : Arg (fun _ => Unit) T.i64)
    (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal (fun _ => Unit)))
    (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys))
    (instr : WInstr) (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys)
    (hk : ∀ f' l' s', (k f' l' s').callsOk allowed exits) :
    (lowerSimpleInstr ctx mb ml f locs stk labs instr k).callsOk allowed exits := by
  cases instr with
  | nop => exact hk f locs stk
  | br_if depth =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨c, r⟩
      cases labs[depth]? with
      | none => exact trivial
      | some l =>
        dsimp only
        cases popArgsAux l.argTys r with
        | none => exact trivial
        | some p' => rcases p' with ⟨_, _⟩; simp only [Expr.callsOk]; exact ⟨trivial, hk f locs r⟩
  | call fnIdx =>
    simp only [lowerSimpleInstr]
    cases hc : ctx.funcs[fnIdx]? with
    | none => exact trivial
    | some callee =>
      dsimp only
      cases hft : ctx.types[callee.typeIdx]? with
      | none => exact trivial
      | some ft =>
        dsimp only
        cases popArgsAux ft.params stk with
        | none => exact trivial
        | some p =>
          rcases p with ⟨_, _⟩
          simp only [Expr.callsOk]
          exact ⟨trivial, hcal fnIdx callee ft hc hft, hk _ locs _, trivial⟩
  | drop =>
    simp only [lowerSimpleInstr]
    cases stk with | nil => exact trivial | cons _ r => exact hk f locs r
  | select =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨_, r⟩
      cases r with
      | nil => exact trivial
      | cons v₂ r2 =>
        cases r2 with
        | nil => cases v₂ <;> exact trivial
        | cons v₁ r3 =>
          cases v₂ <;> cases v₁ <;> dsimp only <;> first | exact trivial | exact hk f locs _
  | local_get idx =>
    simp only [lowerSimpleInstr]
    cases getLocal ctx.locTys locs idx with | none => exact trivial | some v => exact hk f locs _
  | local_set idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact trivial
    | cons v r => dsimp only; cases setLocal ctx.locTys locs idx v with
      | none => exact trivial | some l' => exact hk f l' r
  | local_tee idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact trivial
    | cons v r => dsimp only; cases setLocal ctx.locTys locs idx v with
      | none => exact trivial | some l' => exact hk f l' (v :: r)
  | global_get idx =>
    simp only [lowerSimpleInstr]
    cases ctx.globals[idx]? with | none => exact trivial | some g => exact hk f locs _
  | load resTy width signed arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]
      cases pop32 stk with
      | none => exact trivial
      | some p =>
        rcases p with ⟨idx32, _⟩
        dsimp only
        exact emitMemBounds_callsOk allowed exits ctx.retTys mb ml f idx32 arg width.bytes _
          fun _ => emitLoadCast_callsOk allowed exits (by simp [Expr.callsOk])
            resTy width signed () _ fun _ => hk f locs _
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | store srcTy width arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]
      cases popExpectS srcTy stk with
      | none => exact trivial
      | some p =>
        rcases p with ⟨sv, s1⟩
        dsimp only
        cases pop32 s1 with
        | none => exact trivial
        | some p2 =>
          rcases p2 with ⟨idx32, s2⟩
          dsimp only
          exact emitMemBounds_callsOk allowed exits ctx.retTys mb ml f idx32 arg width.bytes _
            fun _ => emitStoreCast_callsOk allowed exits (by simp [Expr.callsOk])
              srcTy width sv _ fun _ => hk f locs s2
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | memory_size =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]; exact hk f locs _
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | memory_grow =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      cases pop32 stk with
      | none => exact trivial
      | some p => rcases p with ⟨_, _⟩; exact hk f locs _
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | i32_const _ => exact hk f locs _
  | i64_const _ => exact hk f locs _
  | eqz w =>
    simp only [lowerSimpleInstr]
    cases w <;> cases stk with
    | nil => exact trivial
    | cons x _ => cases x <;> dsimp only <;> first | exact trivial | exact hk f locs _
  | unop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨x, _⟩
      dsimp only
      exact emitUnOp_callsOk allowed exits ctx.retTys f w op x _ fun _ => hk f locs _
  | binop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨b, s1⟩
      dsimp only
      cases popExpectS w s1 with
      | none => exact trivial
      | some p2 =>
        rcases p2 with ⟨a, _⟩
        dsimp only
        exact emitBinOp_callsOk allowed exits ctx.retTys f w op a b _ fun _ => hk f locs _
  | relop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨b, s1⟩
      dsimp only
      cases popExpectS w s1 with
      | none => exact trivial
      | some p2 => rcases p2 with ⟨a, _⟩; dsimp only; cases w <;> exact hk f locs _
  | wrap_i64 =>
    simp only [lowerSimpleInstr]
    cases pop64 stk with | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _
  | extend_i32_s =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _
  | extend_i32_u =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _
  | unreachable => exact trivial
  | block _ _ => exact trivial
  | loop _ _ => exact trivial
  | if_ _ _ _ => exact trivial
  | br _ => exact trivial
  | br_table _ _ => exact trivial
  | return_ => exact trivial

private theorem lowerSeq_callsOk_aux (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym)
    (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed) :
    ∀ (sz : Nat) (mb ml f : Arg (fun _ => Unit) T.i64)
      (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal (fun _ => Unit)))
      (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys))
      (instrs : List WInstr) (_hsz : sizeOf instrs ≤ sz)
      (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys),
      (∀ f' l' s', (k f' l' s').callsOk allowed exits) →
      (lowerSeq ctx mb ml f locs stk labs instrs k).callsOk allowed exits := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro mb ml f locs stk labs instrs hsz k hk
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk
    | cons i rest =>
      have hszRest : sizeOf rest < sizeOf (i :: rest) := by simp +arith
      cases i with
      | unreachable => simp only [lowerSeq]; exact trivial
      | br depth =>
        simp only [lowerSeq]
        cases labs[depth]? with
        | none => exact trivial
        | some lbl =>
          dsimp only
          cases popArgsAux lbl.argTys stk with
          | none => exact trivial
          | some p => rcases p with ⟨_, _⟩; exact trivial
      | br_table targets defTarget =>
        simp only [lowerSeq]
        cases pop32 stk with
        | none => exact trivial
        | some p =>
          rcases p with ⟨idx32, s1⟩
          cases labs[defTarget]? with
          | none => exact trivial
          | some defLbl =>
            dsimp only
            cases popArgsAux defLbl.argTys s1 with
            | none => exact trivial
            | some p' =>
              rcases p' with ⟨ba, _⟩
              dsimp only
              exact emitBrTable_callsOk allowed exits ctx.locTys ctx.retTys labs locs f idx32 defLbl
                ba 0 targets
      | return_ =>
        simp only [lowerSeq]
        cases popArgsAux ctx.retTys stk with
        | none => exact trivial
        | some p => rcases p with ⟨_, _⟩; exact trivial
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact trivial
          | some p =>
            rcases p with ⟨_, _⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            simp only [Expr.callsOk, Blocks.callsOk]
            refine ⟨⟨ih _ hszRest' mb ml _ _ _ labs rest (Nat.le_refl _) k hk, trivial⟩, ?_⟩
            refine ih _ hszBody mb ml f locs _ _ body (Nat.le_refl _) _ fun _ _ s' => ?_
            cases popArgsAux ft.results s' with
            | none => exact trivial
            | some p' => rcases p' with ⟨_, _⟩; exact trivial
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact trivial
          | some p =>
            rcases p with ⟨_, _⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            simp only [Expr.callsOk, Blocks.callsOk]
            refine ⟨⟨ih _ hszRest' mb ml _ _ _ labs rest (Nat.le_refl _) k hk, trivial⟩,
              ⟨⟨⟨trivial, ?_⟩, trivial⟩, trivial⟩⟩
            refine ih _ hszBody mb ml _ _ _ _ body (Nat.le_refl _) _ fun _ _ s' => ?_
            cases popArgsAux ft.results s' with
            | none => exact trivial
            | some p' => rcases p' with ⟨_, _⟩; exact trivial
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft =>
          dsimp only
          cases pop32 stk with
          | none => exact trivial
          | some p =>
            rcases p with ⟨_, s1⟩
            dsimp only
            cases popArgsAux ft.params s1 with
            | none => exact trivial
            | some p' =>
              rcases p' with ⟨_, _⟩
              dsimp only
              have hszT : sizeOf thenBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              simp only [Expr.callsOk, Blocks.callsOk]
              refine ⟨⟨ih _ hszRest' mb ml _ _ _ labs rest (Nat.le_refl _) k hk, trivial⟩,
                ?_, ?_⟩
              · refine ih _ hszT mb ml f locs _ _ thenBody (Nat.le_refl _) _ fun _ _ s' => ?_
                cases popArgsAux ft.results s' with
                | none => exact trivial
                | some p'' => rcases p'' with ⟨_, _⟩; exact trivial
              · refine ih _ hszE mb ml f locs _ _ elseBody (Nat.le_refl _) _ fun _ _ s' => ?_
                cases popArgsAux ft.results s' with
                | none => exact trivial
                | some p'' => rcases p'' with ⟨_, _⟩; exact trivial
      | _ =>
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        exact lowerSimpleInstr_callsOk ctx allowed exits hcal mb ml f locs stk labs _ _
          fun f' l' s' => ih _ hszRest' mb ml f' l' s' labs rest (Nat.le_refl _) k hk

/-- Every lowered function only invokes intra-module functions at their lowered ABI signatures. -/
theorem lowerFn_callsOk (m : WModule) (f : WFunc) :
    (lowerFn m f).callsOk (lowerModule m).sigs (lowerModule m).exits := by
  simp only [Fn.callsOk, lowerFn, lowerFuncBody, Expr.callsOk, Blocks.callsOk]
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  let ft := (m.types[f.typeIdx]?).getD {}
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  have hcal : ∀ (fnIdx : Nat) (callee : WFunc) (cft : WFuncTy), m.funcs[fnIdx]? = some callee →
      m.types[callee.typeIdx]? = some cft →
      (callee.name, wasmAbiParams cft, wasmAbiResults cft) ∈ (lowerModule m).sigs := by
    intro fnIdx callee cft hc hft
    have hmem : callee ∈ m.funcs := List.mem_of_getElem? hc
    have hsig : (lowerFn m callee).sig ∈ (lowerModule m).fns.map Fn.sig :=
      List.mem_map.mpr ⟨lowerFn m callee, List.mem_map.mpr ⟨callee, hmem, rfl⟩, rfl⟩
    have hftEq : (m.types[callee.typeIdx]?).getD {} = cft := by simp [hft]
    refine List.mem_append_left _ ?_
    simpa [Fn.sig, lowerFn, hftEq] using hsig
  refine lowerSeq_callsOk_aux ctx (lowerModule m).sigs (lowerModule m).exits hcal
    (sizeOf f.body) _ _ _ _ [] _ f.body (Nat.le_refl _) _ fun _ _ s' => ?_
  cases popArgsAux ft.results s' with
  | none => simp [Expr.callsOk]
  | some p => rcases p with ⟨_, _⟩; exact trivial

/-- Helper: when `m.funcs.map WFunc.name` is `Nodup`, any two functions with the same name are
identical. -/
private theorem func_eq_of_namesNodup {fs : List WFunc} (hnd : (fs.map WFunc.name).Nodup)
    {f₁ f₂ : WFunc} (h1 : f₁ ∈ fs) (h2 : f₂ ∈ fs) (heq : f₁.name = f₂.name) : f₁ = f₂ := by
  induction fs with
  | nil => cases h1
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd heq.symm (hnd.1 f₂ h2')
    · exact absurd heq (hnd.1 f₁ h1')
    · exact ih hnd.2 h1' h2'

private theorem wasmSandboxEnv_callee (m : WModule) (callee : WFunc)
    (hmem : callee ∈ m.funcs) (ft : WFuncTy) (hft : m.types[callee.typeIdx]? = some ft)
    {memBase memLen f' : BitVec 64}
    {args : Tup Val (ft.params.map WValTy.toTy)}
    {mem' : Mem 64} {R : Mem 64 → Prop}
    (hm' : WasmMemInv m.memory.isSome memBase memLen R mem') :
    WasmSandboxEnv m f'.toNat callee.name (wasmAbiParams ft) (wasmAbiResults ft)
      (memBase, memLen, f', args) mem'
      (WasmPost m.memory.isSome memBase memLen f' ft.results R)
      (fun _ _ _ _ => False) := by
  have hftEq : ft = (m.types[callee.typeIdx]?).getD {} := by simp [hft]
  subst hftEq
  exact ⟨callee, hmem, rfl, rfl, rfl, Nat.le_refl _, R, hm', fun _ _ h => h⟩

/-- Universal `ModuleSccOk` theorem: EVERY validated Wasm module lowered via `lowerModule`
satisfies `ModuleSccOk` under fuel-indexed `WasmSandboxEnv` (for arbitrary external contracts
`Γext` and arbitrary host memory frame `R`). -/
theorem lowerModule_moduleSccOk {m : WModule} (hv : validateModule m = true) (Γext : Env) :
    ModuleSccOk natRecIdx (WasmSandboxEnv m) Γext false (lowerModule m) := by
  have hnd : (lowerModule m).namesNodup := lowerModule_namesNodup hv
  have hfnd : (m.funcs.map WFunc.name).Nodup := by
    simpa [Module.namesNodup, Module.names, lowerModule, Function.comp_def, lowerFn] using hnd
  refine ⟨hnd, fun fn hfn => ?_⟩
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfn
  refine ⟨lowerFuncBody_wf m f _, lowerFn_callsOk m f, fun i xs mem Q X hspec => ?_⟩
  rcases hspec with ⟨f', hf', ha, hb, heq, hfuel, R, hm, hpost⟩
  have heqf : f = f' := func_eq_of_namesNodup hfnd hf hf' heq
  subst heqf
  have hba : ha = rfl := Subsingleton.elim _ _
  have hbb : hb = rfl := Subsingleton.elim _ _
  subst hba; subst hbb
  dsimp only at hfuel hm hpost
  have hstep : WasmCalleeEnvOk
      (Env.stepIdx natRecIdx ((lowerModule m).fns.map Fn.sig)
        ((lowerModule m).externs.map Extern.sig) (WasmSandboxEnv m) Γext false i)
      m.funcs m.types m.memory.isSome xs.1 xs.2.1 xs.2.2.1 R := by
    intro fnIdx callee ft hc hft f' args m' hlt hm'
    have hcmem : callee ∈ m.funcs := List.mem_of_getElem? hc
    have hftEq : (m.types[callee.typeIdx]?).getD {} = ft := by simp [hft]
    have hsig : (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈
        (lowerModule m).fns.map Fn.sig := by
      have hm1 : lowerFn m callee ∈ (lowerModule m).fns :=
        List.mem_map.mpr ⟨callee, hcmem, rfl⟩
      have hm2 : (lowerFn m callee).sig ∈ (lowerModule m).fns.map Fn.sig :=
        List.mem_map.mpr ⟨lowerFn m callee, hm1, rfl⟩
      simpa [Fn.sig, lowerFn, hftEq] using hm2
    left
    exact ⟨hsig, f'.toNat, Nat.lt_of_lt_of_le hlt hfuel, Or.inl rfl,
      wasmSandboxEnv_callee m callee hcmem ft hft hm'⟩
  have hwp := lowerFuncBody_wp m f _ hm hstep (X := X)
  exact wp_mono hpost (fun _ _ _ _ h => h) _ mem hwp

/-- Universal `Env.semScc` soundness theorem: ANY validated Wasm module `m` lowered via
`lowerModule` embeds `WasmSandboxEnv m` into `Env.semScc (lowerModule m) Γext`. -/
theorem lowerModule_semScc {m : WModule} (hv : validateModule m = true) (Γext : Env) :
    ∀ i, Env.le (Env.restrict (WasmSandboxEnv m i) ((lowerModule m).fns.map Fn.sig))
      (Env.semScc (lowerModule m) Γext) :=
  moduleSccOk_le_semScc (lowerModule_moduleSccOk hv Γext)

/-- Existential fuel-quantified sandbox environment for acyclic `ModuleOk` modules. -/
def WasmSandboxEnvAny (m : WModule) : Env :=
  fun f as bs xs mem Q X => ∃ i, WasmSandboxEnv m i f as bs xs mem Q X

/-- Acyclic `ModuleOk` theorem: whenever `validateModule m = true` and
`(lowerModule m).checkAcyclic = true`, `(lowerModule m)` satisfies `ModuleOk (WasmSandboxEnvAny m)`.
-/
theorem lowerModule_moduleOk {m : WModule} (hv : validateModule m = true)
    (hacyc : (lowerModule m).checkAcyclic = true) :
    ModuleOk (WasmSandboxEnvAny m) (lowerModule m) := by
  have hnd := (validateModule_elim hv).1
  have hfnd : (m.funcs.map WFunc.name).Nodup := hnd
  refine Module.moduleOk_of_checkAcyclic hacyc (lowerModule_wf m) fun fn hfn xs mem Q X hspec => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfn
  rcases hspec with ⟨i, hi⟩
  rcases hi with ⟨f', hf', ha, hb, heq, hfuel, R, hm, hpost⟩
  have heqf : f = f' := func_eq_of_namesNodup hfnd hf hf' heq
  subst heqf
  have hba : ha = rfl := Subsingleton.elim _ _
  have hbb : hb = rfl := Subsingleton.elim _ _
  subst hba; subst hbb
  dsimp only at hfuel hm hpost
  have hcal : WasmCalleeEnvOk (WasmSandboxEnvAny m) m.funcs m.types m.memory.isSome
      xs.1 xs.2.1 xs.2.2.1 R := by
    intro fnIdx callee ft hc hft f' args m' _ hm'
    exact ⟨f'.toNat, wasmSandboxEnv_callee m callee (List.mem_of_getElem? hc) ft hft hm'⟩
  have hwp := lowerFuncBody_wp m f _ hm hcal (X := X)
  exact wp_mono hpost (fun _ _ _ _ h => h) _ mem hwp

/-- Primary user-facing theorem: ANY validated Wasm module lowered via `lowerModule` preserves
arbitrary host memory `R` outside linear memory `[memBase, memBase + memLen)`, never performs OOB
loads/stores, never divides by zero or overflows `INT_MIN / -1`, and terminates cleanly with
status `0#32` (OK), `1#32` (trap), or `2#32` (out of fuel). -/
theorem wasm_preserves_host_mem {m : WModule} (hv : validateModule m = true)
    (Γext : Env) {f : WFunc} (hf : f ∈ m.funcs)
    (memBase memLen fuel : BitVec 64)
    (args : Tup Val (((m.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv m.memory.isSome memBase memLen R mem)
    (Q : Post (wasmAbiResults ((m.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost m.memory.isSome memBase memLen fuel
      ((m.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc (lowerModule m) Γext f.name
      (wasmAbiParams ((m.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((m.types[f.typeIdx]?).getD {}))
      (memBase, memLen, fuel, args) mem Q X := by
  have hfn : lowerFn m f ∈ (lowerModule m).fns :=
    List.mem_map.mpr ⟨f, hf, rfl⟩
  have hsig : (f.name, wasmAbiParams ((m.types[f.typeIdx]?).getD {}),
      wasmAbiResults ((m.types[f.typeIdx]?).getD {})) ∈ (lowerModule m).fns.map Fn.sig :=
    List.mem_map.mpr ⟨lowerFn m f, hfn, rfl⟩
  refine lowerModule_semScc hv Γext fuel.toNat _ _ _ _ _ _ _ ⟨hsig, ?_⟩
  exact ⟨f, hf, rfl, rfl, rfl, Nat.le_refl _, R, hmem, hpost⟩

mutual
/-- Check that all `.call` targets inside `i` have function index `< bound`. -/
def wasmInstrCallsBelow (bound : Nat) : WInstr → Bool
  | .block _ body => wasmSeqCallsBelow bound body
  | .loop _ body => wasmSeqCallsBelow bound body
  | .if_ _ t e => wasmSeqCallsBelow bound t && wasmSeqCallsBelow bound e
  | .call fnIdx => decide (fnIdx < bound)
  | _ => true

/-- Check that all `.call` targets in an instruction sequence have function index `< bound`. -/
def wasmSeqCallsBelow (bound : Nat) : List WInstr → Bool
  | [] => true
  | i :: rest => wasmInstrCallsBelow bound i && wasmSeqCallsBelow bound rest
end

/-- Check that every function in `fs` (starting at index `idx`) only calls earlier functions. -/
def wasmAcyclicAux (idx : Nat) : List WFunc → Bool
  | [] => true
  | f :: fs => wasmSeqCallsBelow idx f.body && wasmAcyclicAux (idx + 1) fs

/-- Decidable syntactic callee-first acyclicity check on a `WModule`. -/
def wasmAcyclic (m : WModule) : Bool :=
  wasmAcyclicAux 0 m.funcs

private theorem lowerSimpleInstr_take_eq {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs)
    (mb ml f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instr : WInstr)
    (hb : wasmInstrCallsBelow bound instr = true)
    (k : WCont V L ctx.locTys ctx.retTys) :
    lowerSimpleInstr { ctx with funcs := fs.take bound } mb ml f locs stk labs instr k =
      lowerSimpleInstr ctx mb ml f locs stk labs instr k := by
  subst hfs
  cases instr with
  | call fnIdx =>
    simp only [wasmInstrCallsBelow, decide_eq_true_eq] at hb
    simp only [lowerSimpleInstr, List.getElem?_take_of_lt hb]
  | br_if depth =>
    simp only [lowerSimpleInstr]
    cases pop32 stk <;> cases labs[depth]? <;>
    first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
  | local_set idx =>
    simp only [lowerSimpleInstr]
    cases stk <;> first | rfl | (dsimp only; cases setLocal ctx.locTys locs idx _ <;> rfl)
  | local_tee idx =>
    simp only [lowerSimpleInstr]
    cases stk <;> first | rfl | (dsimp only; cases setLocal ctx.locTys locs idx _ <;> rfl)
  | _ => simp only [lowerSimpleInstr] <;> try rfl

private theorem lowerSeq_take_eq_aux {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs)
    (sz : Nat) :
    ∀ (mb ml f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instrs : List WInstr),
      sizeOf instrs ≤ sz → wasmSeqCallsBelow bound instrs = true →
      ∀ (k₁ k₂ : WCont V L ctx.locTys ctx.retTys),
        (∀ f' l' s', k₁ f' l' s' = k₂ f' l' s') →
        lowerSeq { ctx with funcs := fs.take bound } mb ml f locs stk labs instrs k₁ =
          lowerSeq ctx mb ml f locs stk labs instrs k₂ := by
  induction sz with
  | zero =>
    intro mb ml f locs stk labs instrs hsz _ k₁ k₂ hk
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk
    | cons _ _ => simp +arith at hsz
  | succ sz ih =>
    intro mb ml f locs stk labs instrs hsz hb k₁ k₂ hk
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk
    | cons instr rest =>
      simp only [wasmSeqCallsBelow, Bool.and_eq_true] at hb
      rcases hb with ⟨hi, hrest⟩
      have hszRest : sizeOf rest < sizeOf (instr :: rest) := by simp +arith
      have hszRest' : sizeOf rest ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hszRest hsz)
      cases instr with
      | block bt body =>
        simp only [wasmInstrCallsBelow] at hi
        have hszBody : sizeOf body < sizeOf (WInstr.block bt body :: rest) := by simp +arith
        have hszBody' : sizeOf body ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hszBody hsz)
        simp only [lowerSeq]
        split
        · rfl
        · split
          · rfl
          · exact congr
              (congrArg Expr.group (funext fun _ => congrArg (fun b => Blocks.cons b Blocks.nil)
                (funext fun _ => ih _ _ _ _ _ _ rest hszRest' hrest _ _ hk)))
              (funext fun _ => ih _ _ _ _ _ _ body hszBody' hi _ _ (fun _ _ _ => rfl))
      | loop bt body =>
        simp only [wasmInstrCallsBelow] at hi
        have hszBody : sizeOf body < sizeOf (WInstr.loop bt body :: rest) := by simp +arith
        have hszBody' : sizeOf body ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hszBody hsz)
        simp only [lowerSeq]
        split
        · rfl
        · split
          · rfl
          · refine congr
              (congrArg Expr.group (funext fun _ => congrArg (fun b => Blocks.cons b Blocks.nil)
                (funext fun _ => ih _ _ _ _ _ _ rest hszRest' hrest _ _ hk)))
              (funext fun _ => congrArg (fun b => Expr.group b _) (funext fun _ =>
                congrArg (fun b => Blocks.cons b Blocks.nil) (funext fun _ =>
                  congrArg (Expr.let_ _) (funext fun _ => congrArg (Expr.jnz _ _)
                    (congrArg (Expr.let_ _) (funext fun _ =>
                      ih _ _ _ _ _ _ body hszBody' hi _ _ (fun _ _ _ => rfl)))))))
      | if_ bt thenBody elseBody =>
        simp only [wasmInstrCallsBelow, Bool.and_eq_true] at hi
        rcases hi with ⟨hT, hE⟩
        have hszT : sizeOf thenBody < sizeOf (WInstr.if_ bt thenBody elseBody :: rest) := by
          simp +arith
        have hszE : sizeOf elseBody < sizeOf (WInstr.if_ bt thenBody elseBody :: rest) := by
          simp +arith
        have hszT' : sizeOf thenBody ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hszT hsz)
        have hszE' : sizeOf elseBody ≤ sz := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hszE hsz)
        simp only [lowerSeq]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · exact congr
                (congrArg Expr.group (funext fun _ => congrArg (fun b => Blocks.cons b Blocks.nil)
                  (funext fun _ => ih _ _ _ _ _ _ rest hszRest' hrest _ _ hk)))
                (funext fun _ => congrArg (Expr.let_ _) (funext fun _ =>
                  congr (congrArg (Expr.jnz _)
                    (ih _ _ _ _ _ _ thenBody hszT' hT _ _ (fun _ _ _ => rfl)))
                    (ih _ _ _ _ _ _ elseBody hszE' hE _ _ (fun _ _ _ => rfl))))
      | unreachable => simp only [lowerSeq]
      | br depth =>
        simp only [lowerSeq]
        cases labs[depth]? <;> first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
      | br_table _ defT =>
        simp only [lowerSeq]
        cases pop32 stk <;> cases labs[defT]? <;>
        first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
      | return_ =>
        simp only [lowerSeq]
        cases popArgsAux ctx.retTys stk <;> rfl
      | _ =>
        simp only [lowerSeq]
        first
        | rfl
        | (rw [lowerSimpleInstr_take_eq ctx fs bound hfs mb ml f locs stk labs _ hi]
           exact congrArg (lowerSimpleInstr ctx mb ml f locs stk labs _)
             (funext fun f' => funext fun l' => funext fun s' =>
               ih mb ml f' l' s' labs rest hszRest' hrest k₁ k₂ hk))

private theorem lowerFn_callsOk_take (m : WModule) (bound : Nat) (f : WFunc)
    (hb : wasmSeqCallsBelow bound f.body = true) :
    (lowerFn m f).callsOk ((m.funcs.take bound).map (fun c => (lowerFn m c).sig)) [] := by
  have h1 := lowerFn_callsOk { m with funcs := m.funcs.take bound } f
  have hsigEq : ∀ c : WFunc,
      (lowerFn { m with funcs := m.funcs.take bound } c).sig = (lowerFn m c).sig :=
    fun _ => rfl
  have hmodEq : (lowerModule { m with funcs := m.funcs.take bound }).sigs =
      (m.funcs.take bound).map (fun c => (lowerFn m c).sig) := by
    simp [lowerModule, Module.sigs, Function.comp_def, hsigEq]
  have hbodyEq :
      ((lowerFn { m with funcs := m.funcs.take bound } f).body
        (fun _ => Unit) (fun _ => Unit)
        (Tup.units (lowerFn { m with funcs := m.funcs.take bound } f).as)) =
      ((lowerFn m f).body (fun _ => Unit) (fun _ => Unit) (Tup.units (lowerFn m f).as)) := by
    simp only [lowerFn, lowerFuncBody]
    refine congrArg (Expr.group _) (funext fun _ => ?_)
    let ctx : WLowerCtx :=
      { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
        globals := m.globals,
        locTys := ((m.types[f.typeIdx]?).getD {}).params ++ f.locals,
        retTys := ((m.types[f.typeIdx]?).getD {}).results }
    exact lowerSeq_take_eq_aux ctx m.funcs bound rfl (sizeOf f.body)
      _ _ _ _ [] _ f.body (Nat.le_refl _) hb _ _ (fun _ _ _ => rfl)
  rw [hmodEq] at h1
  change Expr.callsOk ((m.funcs.take bound).map (fun c => (lowerFn m c).sig)) []
      ((lowerFn { m with funcs := m.funcs.take bound } f).body
        (fun _ => Unit) (fun _ => Unit)
        (Tup.units (lowerFn { m with funcs := m.funcs.take bound } f).as)) at h1
  rw [hbodyEq] at h1
  exact h1

private theorem wasmAcyclicAux_drop :
    ∀ (fs : List WFunc) (idx : Nat),
      wasmAcyclicAux idx fs = true →
      ∀ (k : Nat) (f : WFunc), fs[k]? = some f →
        wasmSeqCallsBelow (idx + k) f.body = true
  | [], _, _, _, _, hk => by cases hk
  | a :: rest, idx, ha, 0, f, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [wasmAcyclicAux, Bool.and_eq_true] at ha
    simpa using ha.1
  | a :: rest, idx, ha, k + 1, f, hk => by
    simp only [wasmAcyclicAux, Bool.and_eq_true] at ha
    simp only [List.getElem?_cons_succ] at hk
    have ih := wasmAcyclicAux_drop rest (idx + 1) ha.2 k f hk
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih

/-- Universal acyclicity theorem: ANY validated callee-first Wasm module (`validateModule m = true`
and `wasmAcyclic m = true`) lowers to a QBE module satisfying `(lowerModule m).checkAcyclic = true`
without requiring kernel reduction of `lowerSeq`. -/
theorem lowerModule_checkAcyclic {m : WModule} (hv : validateModule m = true)
    (hacyc : wasmAcyclic m = true) :
    (lowerModule m).checkAcyclic = true := by
  have hnd : (lowerModule m).checkNamesNodup = true := by
    rw [Module.checkNamesNodup, listNodup_iff]
    exact lowerModule_namesNodup hv
  have hcalls : Module.checkFnsCallsOk [] [] [] (m.funcs.map (lowerFn m)) = true := by
    refine checkFnsCallsOk_of_forall [] [] [] (m.funcs.map (lowerFn m)) fun pre fn post hsp => ?_
    have hfnEq : (m.funcs.map (lowerFn m))[pre.length]? = some fn := by
      rw [hsp, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hk : ∃ f : WFunc, m.funcs[pre.length]? = some f ∧ lowerFn m f = fn := by
      have hg :
          (m.funcs.map (lowerFn m))[pre.length]? = (m.funcs[pre.length]?).map (lowerFn m) :=
        List.getElem?_map
      rw [hg] at hfnEq
      cases hw : m.funcs[pre.length]? with
      | none => simp [hw] at hfnEq
      | some f =>
        simp only [hw, Option.map_some, Option.some.injEq] at hfnEq
        exact ⟨f, rfl, hfnEq⟩
    rcases hk with ⟨f, hfGet, rfl⟩
    have hbelow : wasmSeqCallsBelow pre.length f.body = true := by
      simpa using wasmAcyclicAux_drop m.funcs 0 hacyc pre.length f hfGet
    have htake : pre = (m.funcs.take pre.length).map (lowerFn m) := by
      have h1 : (m.funcs.map (lowerFn m)).take pre.length = pre := by
        rw [hsp, List.take_left]
      rw [← List.map_take] at h1
      exact h1.symm
    have hsig :
        pre.map Fn.sig = (m.funcs.take pre.length).map (fun c => (lowerFn m c).sig) := by
      conv => lhs; rw [htake]
      rw [List.map_map]
      rfl
    simpa [List.append_nil, hsig] using lowerFn_callsOk_take m pre.length f hbelow
  simp only [Module.checkAcyclic, Bool.and_eq_true, lowerModule] at hnd ⊢
  exact ⟨hnd, hcalls⟩

end LeanQbe.T.Wasm
