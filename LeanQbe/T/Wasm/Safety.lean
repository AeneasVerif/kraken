module

public import LeanQbe.T.Wasm.BulkSafety

/-!
# Universal WebAssembly Sandbox Memory Safety (`WasmSandboxInv`)

Proves universal total-correctness memory safety and host-frame preservation for ANY WebAssembly
module lowered via `LeanQbe.T.Wasm.lowerModule`:

* `WasmMemInv` & `WasmPost` (exported from `LeanQbe.T.Wasm.BulkSafety`): separates guest VM context
  `vmCtx ↦ [memBase, memLen, memCap]` and pre-allocated guest backing `region memBase memCap.toNat`
  from arbitrary host memory frame `R : Mem 64 → Prop`, while guaranteeing monotone growth
  (`memLen ≤ memLen'`), monotone fuel (`remFuel ≤ fuel`), and status `{0#32, 1#32, 2#32}`.
* `lowerFuncBody_wp`: universal `Func.wp` theorem covering every instruction (SFI bounds-checked
  8/16/32/64-bit loads/stores, `memory.size`, `memory.grow`, `memory.fill`, `memory.copy`,
  division/remainder trap guards, SWAR popcnt, structured control, and fuel-bounded `call`).
* `lowerModule_moduleSccOk` & `lowerModule_semScc`: universal `ModuleSccOk` and `Env.semScc`
  soundness for arbitrary validated Wasm modules (`validateModule m = true`), including recursive
  and mutually recursive Wasm guests.
* `lowerModule_moduleOk` & `wasm_preserves_host_mem`: acyclic `ModuleOk` wrapper and host-memory
  preservation corollary.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Wasm

open LeanQbe.T LeanQbe.T.LinkScc

/-! ## Instruction & Structured Control WP Lemmas -/


local macro "w_pop" e:Lean.Parser.Tactic.elimTarget ","
    x:Lean.binderIdent r:Lean.binderIdent : tactic => `(tactic| (
  cases $e; · first | assumption | exact trivial
  rename_i _p; cases _p; rename_i $x $r; try dsimp only))

local macro "wp_mem" b:term "," hmem:term : tactic => `(tactic| (
  by_cases _hmf : $b; rotate_left; · simp only [_hmf, Bool.false_eq_true, ↓reduceIte]; assumption
  simp only [_hmf, ↓reduceIte]; first
  | (have _hhm := (Eq.symm $hmem).trans _hmf; subst _hhm)
  | (simp only [Bool.and_eq_true] at _hmf
     have _hhm := (Eq.symm $hmem).trans _hmf.1; subst _hhm)))

local macro "c_mem" b:term : tactic => `(tactic| (
  by_cases _hmc : $b; rotate_left; · simp only [_hmc, Bool.false_eq_true, ↓reduceIte]; exact trivial
  simp only [_hmc, ↓reduceIte]))

private theorem emitPopcntCore_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (n : Nat) (m1 m2 m4 mul sh : BitVec n) (x : Arg Val (.bits n))
    (k : Arg Val (.bits n) → Expr Val Cont rs) (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitPopcntCore n m1 m2 m4 mul sh x k) m := by
  simp only [emitPopcntCore]
  repeat' (rw [wp_let_]; simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte])
  exact hk _

private theorem emitPopcnt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (w : WValTy) (x : Arg Val w.toTy) (k : Arg Val w.toTy → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) : wp Γ Q X (emitPopcnt w x k) m := by
  cases w <;> exact emitPopcntCore_wp _ _ _ _ _ _ x k hk

private theorem emitUnOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (w : WValTy) (op : WUnOp) (x : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitUnOp retTys fuel w op x k) mem := by
  cases w <;> cases op <;> simp only [emitUnOp] <;> first
  | exact emitPopcnt_wp _ x k hk
  | exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  | ((repeat' wasm_wp_let); exact hk _)

private theorem sdivDefined_of_guards {n : Nat} {a b minConst neg1Const : BitVec n}
    (hiMin : BitVec.intMin n = minConst) (hiAll : BitVec.allOnes n = neg1Const)
    (hz : decide (b = 0#n) = false)
    (hov : (decide (a = minConst) && decide (b = neg1Const)) = false) :
    sdivDefined a b = true := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  simp only [decide_eq_false_iff_not, Bool.and_eq_false_iff] at hz hov
  rw [hiMin, hiAll]; exact ⟨by simpa using hz, hov⟩

private theorem emitDivRemCore_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (n : Nat) (minC neg1C : BitVec n) (signed trapOvf : Bool)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (hcode : ∀ (x y : BitVec n) (Q' : Tup Val [.bits n] → Prop), decide (y = 0#n) = false →
      (signed = true → (decide (x = minC) && decide (y = neg1C)) = false) →
      (∀ r, Q' (r, ())) → OpCode.wp code (x, y, ()) Q')
    (a b : Arg Val (.bits n)) (k : Arg Val (.bits n) → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitDivRemCore retTys fuel n minC neg1C signed trapOvf code a b k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  simp only [emitDivRemCore]; wasm_wp_let; rw [wp_jnz_]
  refine ⟨fun _ => htrap, fun hz => ?_⟩; rw [arg_var_val] at hz
  cases signed <;> simp only [↓reduceIte, Bool.false_eq_true]
  · rw [wp_let_]; exact hcode a.val b.val _ hz (fun h => by cases h) (fun r => hk (.var r))
  · repeat' wasm_wp_let; rw [wp_jnz_]
    refine ⟨fun _ => by cases trapOvf <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
        first | exact htrap | exact hk _,
      fun hov => by
        rw [arg_var_val] at hov; rw [wp_let_]
        exact hcode a.val b.val _ hz (fun _ => hov) (fun r => hk (.var r))⟩

private theorem emitBinOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (w : WValTy) (op : WBinOp) (a b : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitBinOp retTys fuel w op a b k) mem := by
  cases op <;> cases w <;> simp only [emitBinOp] <;> first
  | (wasm_wp_let; exact hk _)
  | exact emitDivRemCore_wp hf hlen0 hm _ _ _ false false _ (fun x y _ hz _ hQ => by
      simp only [OpCode.wp]; exact ⟨by simpa [BitVec.toNat_eq] using of_decide_eq_false hz, hQ _⟩)
      a b k hk
  | exact emitDivRemCore_wp hf hlen0 hm _ _ _ true _ _ (fun x y _ hz hs hQ => by
      simp only [OpCode.wp]; exact ⟨sdivDefined_of_guards rfl rfl hz (hs rfl), hQ _⟩) a b k hk

private theorem emitLoadCast_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (resTy : WValTy) (width : WMemWidth) (signed : Bool) (raw : Val width.memTy)
    (k : Arg Val resTy.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitLoadCast (mkTrapExpr retTys 1#32 fuel) resTy width signed raw k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  cases resTy <;> cases width <;> cases signed <;> simp only [emitLoadCast] <;>
    first | exact htrap | exact hk _ | (wasm_wp_let; exact hk _)

private theorem emitStoreCast_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {R : Mem 64 → Prop} {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (srcTy : WValTy) (width : WMemWidth) (v : Arg Val srcTy.toTy)
    (k : Arg Val width.memTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitStoreCast (mkTrapExpr retTys 1#32 fuel) srcTy width v k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  cases srcTy <;> cases width <;> simp only [emitStoreCast] <;>
    first | exact htrap | exact hk _ | (wasm_wp_let; exact hk _)

private theorem emitSelect_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {trap : Expr Val Cont rs} (htrap : wp Γ Q X trap m) (c : Arg Val T.i32) (v1 v2 : SVal Val)
    (k : SVal Val → Expr Val Cont rs) (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitSelect trap c v1 v2 k) m := by
  cases v1 <;> cases v2 <;> simp only [emitSelect] <;>
    first | exact htrap | ((repeat' wasm_wp_let); exact hk _)

private theorem emitEqz_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (w : WValTy) (x : Arg Val w.toTy) (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) : wp Γ Q X (emitEqz w x k) m := by
  cases w <;> simp only [emitEqz] <;> (repeat' wasm_wp_let) <;> exact hk _

private theorem emitRelOp_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (w : WValTy) (op : WRelOp) (a b : Arg Val w.toTy) (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) : wp Γ Q X (emitRelOp w op a b k) m := by
  cases w <;> simp only [emitRelOp] <;> (repeat' wasm_wp_let) <;> exact hk _

private theorem eqRec_cont_wp {locTys : List WValTy} {ts₁ ts₂ : List WValTy}
    {hasMem : Bool} {vmCtx memBase curLen memCap fuel : BitVec 64} {R : Mem 64 → Prop}
    (h : ts₁ = ts₂) (J : Cont (labelSig locTys ts₁)) (args : Tup Val (labelSig locTys ts₂))
    (m : Mem 64) (hJ : ∀ curLen' (xs : Tup Val (labelSig locTys ts₁)) m',
      curLen.toNat ≤ curLen'.toNat → xs.1.toNat ≤ fuel.toNat →
      WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → J xs m')
    (hf : args.1.toNat ≤ fuel.toNat) (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R m) :
    (h ▸ J) args m := by subst h; exact hJ curLen args m (Nat.le_refl _) hf hm

private theorem emitBrTable_wp {Γ : Env} {X : XPost} {locTys retTys : List WValTy}
    {hasMem : Bool} {vmCtx memBase memLen0 curLen memCap fuel0 curFuel : BitVec 64}
    {R : Mem 64 → Prop} (labs : List (WLabel Val Cont locTys))
    (hlabs : LabsSafe locTys hasMem vmCtx memBase curLen memCap curFuel R labs)
    (locs : Tup (Arg Val) (locTys.map WValTy.toTy)) (f : Arg Val T.i64)
    (hf0 : f.val.toNat ≤ fuel0.toNat) (hf : f.val.toNat ≤ curFuel.toNat) (idx : Arg Val T.i32)
    (defLbl : WLabel Val Cont locTys) (hdef : defLbl ∈ labs)
    (ba : Tup (Arg Val) (defLbl.argTys.map WValTy.toTy))
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) (i : Nat) (ts : List Nat) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitBrTable locTys retTys labs locs f idx defLbl ba i ts) mem := by
  induction ts generalizing i with
  | nil =>
    simp only [emitBrTable]; rw [wp_jump_]
    exact hlabs defLbl hdef curLen _ mem (Nat.le_refl _) hf hm
  | cons t rest ih =>
    simp only [emitBrTable]
    cases hget : labs[t]? with
    | none => exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hlen0 hm
    | some lbl =>
      by_cases hty : lbl.argTys = defLbl.argTys
      · simp only [hty, ↓reduceDIte]; wasm_wp_let; rw [wp_jnz_]
        refine ⟨fun _ => ?_, fun _ => ih (i + 1)⟩; rw [wp_jump_]
        exact eqRec_cont_wp hty lbl.lbl (vals (f, tupAppend locs ba)) mem
          (hlabs lbl (List.mem_of_getElem? hget)) hf hm
      · simp only [hty, ↓reduceDIte]
        exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hlen0 hm

private theorem lowerSimpleInstr_wp {Γ : Env} {X : XPost} (ctx : WLowerCtx)
    {hasMem : Bool} (hmem : ctx.hasMem = hasMem)
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop}
    (vc f : Arg Val T.i64) (hvc : vc.val = vmCtx) (hf0 : f.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hcal : WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R)
    (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
    (labs : List (WLabel Val Cont ctx.locTys))
    (hlabs : LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs)
    (instr : WInstr) (k : WCont Val Cont ctx.locTys ctx.retTys)
    (hk : ∀ f' curLen' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
      curLen.toNat ≤ curLen'.toNat → WasmMemInv hasMem vmCtx memBase curLen' memCap R mem' →
      LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap f'.val R labs →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f'.val R →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (k f' locs' stk') mem')
    {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
      (lowerSimpleInstr ctx vc f locs stk labs instr k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) (vmCtx := vmCtx) (memBase := memBase)
    (memLen0 := memLen0) (memCap := memCap) (fuel0 := fuel0) ctx.retTys 1#32
    (Or.inr (Or.inl rfl)) hf0 hlen0 hm
  have hks : ∀ {f' curLen' locs' stk' m'}, f'.val.toNat ≤ f.val.toNat →
      curLen.toNat ≤ curLen'.toNat → WasmMemInv hasMem vmCtx memBase curLen' memCap R m' →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (k f' locs' stk') m' :=
    fun hf' hcur' hm' => hk _ _ _ _ _ hf' hcur' hm' (LabsSafe.mono hcur' hf' hlabs)
      (WasmCalleeEnvOk.mono_fuel hf' hcal)
  have hk0 : ∀ (locs' : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) stk',
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (k f locs' stk') mem := fun _ _ => hks (Nat.le_refl _) (Nat.le_refl _) hm
  cases instr with
  | load resTy width signed _ =>
    simp only [lowerSimpleInstr]
    wp_mem (ctx.hasMem && validateLoad resTy width signed) = true, hmem
    w_pop (pop32 stk), idx32 s1
    refine emitMemBounds_wp vc f hvc hf0 hlen0 hm idx32 _ _ _ fun _ hba =>
      wp_wasm_load_w hm _ hba fun raw =>
        emitLoadCast_wp hf0 hlen0 hm _ _ _ raw _ fun v => hk0 locs (SVal.ofArg _ v :: s1)
  | store srcTy width _ =>
    simp only [lowerSimpleInstr]; wp_mem (ctx.hasMem && validateStore srcTy width) = true, hmem
    w_pop (popExpectS _ stk), sv s1; w_pop (pop32 s1), idx32 s2
    refine emitMemBounds_wp vc f hvc hf0 hlen0 hm idx32 _ _ _ fun _ hba =>
      emitStoreCast_wp hf0 hlen0 hm _ _ sv _ fun memVal =>
        wp_wasm_store_w hm _ hba memVal fun _ hm' => hks (Nat.le_refl _) (Nat.le_refl _) hm'
  | br_if depth =>
    simp only [lowerSimpleInstr]; w_pop (pop32 stk), c r
    cases hget : labs[depth]? with | none => dsimp only; exact htrap | some lbl =>
    dsimp only; w_pop (popArgsAux lbl.argTys r), ba s_; wasm_wp_let; rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun _ => hk0 locs r⟩; rw [wp_jump_]
    exact hlabs lbl (List.mem_of_getElem? hget) curLen _ mem (Nat.le_refl _) (Nat.le_refl _) hm
  | _ =>
  simp only [lowerSimpleInstr] <;> first
  | exact htrap | exact hk0 locs _
  | (cases hc : ctx.funcs[‹Nat›]? with | none => exact htrap | some callee =>
     dsimp only; cases hft : ctx.types[callee.typeIdx]? with | none => exact htrap | some ft =>
     dsimp only; w_pop (popArgsAux ft.params stk), ca s1; wasm_wp_let; rw [wp_jnz_]
     refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl)) hf0 hlen0 hm,
       fun hz => ?_⟩
     have hlt := bv64_sub_one_lt (decide_eq_false_iff_not.mp hz); wasm_wp_let; rw [wp_call_]
     refine ⟨WasmPost hasMem vmCtx memBase curLen memCap (f.val - 1#64) ft.results R,
       fun _ _ _ _ => False, ?_, ?_, fun _ _ _ _ h => False.elim h⟩
     · rw [vals_wasmAbi, hvc]; exact hcal _ callee ft hc hft curLen _ (vals ca) mem hlt hm
     · intro r m' ⟨hst, hrf, curLen', hcurLe, hm'⟩; wasm_wp_let; rw [wp_jnz_]
       have hle := Nat.le_trans hrf (Nat.le_of_lt hlt)
       exact ⟨fun _ => hks hle hcurLe hm', fun _ => wp_mkStatusTrapExpr ctx.retTys
         (status := .var r.1) hst (Nat.le_trans hle hf0) (Nat.le_trans hlen0 hcurLe) hm'⟩)
  | (cases stk with | nil => exact htrap | cons _ r => exact hk0 locs r)
  | (w_pop (pop32 stk), c r; cases r with | nil => exact htrap | cons v₂ r2 =>
     cases r2 with | nil => exact htrap | cons v₁ r3 =>
     exact emitSelect_wp htrap c v₁ v₂ _ fun y => hk0 locs (y :: r3))
  | (cases getLocal ctx.locTys locs ‹Nat› with | none => exact htrap | some v => exact hk0 locs _)
  | (cases stk with | nil => exact htrap | cons v r =>
     dsimp only; cases setLocal ctx.locTys locs ‹Nat› v with
     | none => exact htrap | some locs' => exact hk0 locs' _)
  | (cases ctx.globals[‹Nat›]? with | none => exact htrap | some _ => exact hk0 locs _)
  | (wp_mem ctx.hasMem = true, hmem; exact emitMemSize_wp vc hvc hm _ (hk0 locs _))
  | (wp_mem ctx.hasMem = true, hmem; w_pop (pop32 stk), delta s1
     exact emitMemGrow_wp ctx.memMaxBytes vc f delta hvc hf0 hlen0 hm _
       fun _ _ _ _ hf' hle hm' => hks hf' hle hm')
  | (wp_mem ctx.hasMem = true, hmem
     w_pop (pop32 stk), n32 s1; w_pop (pop32 s1), v32 s2; w_pop (pop32 s2), d32 s3
     exact emitMemFill_wp vc f d32 v32 n32 hvc hf0 hlen0 hm _
       fun _ _ hf' hm' => hks hf' (Nat.le_refl _) hm')
  | (wp_mem ctx.hasMem = true, hmem
     w_pop (pop32 stk), n32 s1; w_pop (pop32 s1), sr32 s2; w_pop (pop32 s2), d32 s3
     exact emitMemCopy_wp vc f d32 sr32 n32 hvc hf0 hlen0 hm _
       fun _ _ hf' hm' => hks hf' (Nat.le_refl _) hm')
  | (cases ‹WValTy› <;> cases stk with | nil => exact htrap | cons x r =>
     cases x <;> first | exact htrap | exact emitEqz_wp _ _ _ fun y => hk0 locs (.i32 y :: r))
  | (w_pop (popExpectS _ stk), x s1; exact emitUnOp_wp hf0 hlen0 hm _ _ x _ fun _ => hk0 locs _)
  | (w_pop (popExpectS _ stk), b s1; w_pop (popExpectS _ s1), a s2
     exact emitBinOp_wp hf0 hlen0 hm _ _ a b _ fun _ => hk0 locs _)
  | (w_pop (popExpectS _ stk), b s1; w_pop (popExpectS _ s1), a s2
     exact emitRelOp_wp _ _ a b _ fun _ => hk0 locs _)
  | (w_pop (pop64 stk), x_ s1; wasm_wp_let; exact hk0 locs _)
  | (w_pop (pop32 stk), x_ s1; wasm_wp_let; exact hk0 locs _)

private theorem lowerGroupJoin_wp {Γ : Env} {X : XPost} (ctx : WLowerCtx) (ft : WFuncTy)
    {hasMem : Bool} {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop}
    {f : Arg Val T.i64} (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (labs : List (WLabel Val Cont ctx.locTys)) (sa : List (SVal Val))
    (hlabs : LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs)
    (hcal : WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R)
    (body : WLabel Val Cont ctx.locTys → WCont Val Cont ctx.locTys ctx.retTys →
      Expr Val Cont (wasmRetSig ctx.retTys))
    (after : WCont Val Cont ctx.locTys ctx.retTys) {mem : Mem 64}
    (hafter : ∀ curLen' (f' : Arg Val T.i64) locs' stk' m', curLen.toNat ≤ curLen'.toNat →
      f'.val.toNat ≤ f.val.toNat → WasmMemInv hasMem vmCtx memBase curLen' memCap R m' →
      LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap f'.val R labs →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f'.val R →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (after f' locs' stk') m')
    (hbody : ∀ lbl' fall,
      LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R (lbl' :: labs) →
      (∀ f' curLen' locs' stk' m', f'.val.toNat ≤ f.val.toNat → curLen.toNat ≤ curLen'.toNat →
        WasmMemInv hasMem vmCtx memBase curLen' memCap R m' →
        wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
          (fall f' locs' stk') m') →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (body lbl' fall) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
      (lowerGroupJoin ctx ft sa body after) mem := by
  simp only [lowerGroupJoin]; rw [wp_group_]; intro Js hcl; rw [closed_cons_] at hcl
  have hJoin : ∀ curLen' (xs : Tup Val (labelSig ctx.locTys ft.results)) m',
      curLen.toNat ≤ curLen'.toNat → xs.1.toNat ≤ f.val.toNat →
      WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → Js.1 xs m' :=
    fun _ _ _ hcur hxs hm' => hcl.1 _ _ (hafter _ (.var _) _ _ _ hcur hxs hm'
      (LabsSafe.mono hcur hxs hlabs) (WasmCalleeEnvOk.mono_fuel hxs hcal))
  refine hbody ⟨ft.results, Js.1⟩ _ (fun _ hl _ _ _ hcur hxs hm' => by
    rcases List.mem_cons.mp hl with rfl | hl
    · exact hJoin _ _ _ hcur hxs hm'
    · exact hlabs _ hl _ _ _ hcur hxs hm') ?_
  intro _ _ _ _ _ hf' hcur' hm'
  cases popArgsAux ft.results _ with
  | none =>
    dsimp only; exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl)) (Nat.le_trans hf' hf0)
      (Nat.le_trans hlen0 hcur') hm'
  | some p' => rcases p' with ⟨ra, _⟩; dsimp only; rw [wp_jump_]; exact hJoin _ _ _ hcur' hf' hm'

/-- Universal WP theorem for `lowerSeq`: arbitrary instruction sequences preserve host frame `R`,
respect fuel bounds, grow memory monotonically (`curLen ≤ curLen'`), and never trap outside
`{1#32, 2#32}`. -/
theorem lowerSeq_wp_aux {Γ : Env} {X : XPost} (ctx : WLowerCtx) {hasMem : Bool}
    (hmem : ctx.hasMem = hasMem) {vmCtx memBase memLen0 memCap fuel0 : BitVec 64}
    {R : Mem 64 → Prop} (vc : Arg Val T.i64) (hvc : vc.val = vmCtx) :
    ∀ (sz : Nat) (curLen : BitVec 64) (f : Arg Val T.i64),
      f.val.toNat ≤ fuel0.toNat → memLen0.toNat ≤ curLen.toNat →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R →
      ∀ (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
        (labs : List (WLabel Val Cont ctx.locTys)),
        LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs →
        ∀ (instrs : List WInstr), sizeOf instrs ≤ sz →
          ∀ (k : WCont Val Cont ctx.locTys ctx.retTys),
            (∀ f' curLen' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
              curLen.toNat ≤ curLen'.toNat → WasmMemInv hasMem vmCtx memBase curLen' memCap R mem' →
              LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap f'.val R labs →
              WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f'.val R →
              wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
                (k f' locs' stk') mem') →
            ∀ {mem : Mem 64}, WasmMemInv hasMem vmCtx memBase curLen memCap R mem →
              wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
                (lowerSeq ctx vc f locs stk labs instrs k) mem := by
  intro sz; induction sz using Nat.strongRecOn with | _ sz ih =>
  intro curLen f hf0 hlen0 hcal locs stk labs hlabs instrs hsz k hk mem hm
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) (vmCtx := vmCtx) (memBase := memBase)
    (memLen0 := memLen0) (memCap := memCap) (fuel0 := fuel0) ctx.retTys 1#32
    (Or.inr (Or.inl rfl)) hf0 hlen0 hm
  cases instrs with
  | nil =>
    simp only [lowerSeq]
    exact hk f curLen locs stk mem (Nat.le_refl _) (Nat.le_refl _) hm hlabs hcal
  | cons i rest =>
    have hlt {b : List WInstr} (h : sizeOf b < sizeOf (i :: rest)) : sizeOf b < sz :=
      Nat.lt_of_lt_of_le h hsz
    let hafter := fun curLen' (f' : Arg Val T.i64) l' s' (m' : Mem 64) hcur hf'
        (hm' : WasmMemInv hasMem vmCtx memBase curLen' memCap R m') hl' hc' =>
      ih _ (hlt (by simp +arith)) curLen' f' (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur) hc'
        l' s' labs hl' rest (Nat.le_refl _) k (fun _ _ _ _ _ hf'' hcur'' hm'' hl'' hc'' =>
          hk _ _ _ _ _ (Nat.le_trans hf'' hf') (Nat.le_trans hcur hcur'') hm'' hl'' hc'')
        (mem := m') hm'
    cases i with
    | unreachable => simp only [lowerSeq]; exact htrap
    | br depth =>
      simp only [lowerSeq]; cases hget : labs[depth]? with | none => exact htrap | some lbl =>
      dsimp only; w_pop (popArgsAux lbl.argTys stk), ba s_; rw [wp_jump_]
      exact hlabs lbl (List.mem_of_getElem? hget) curLen _ mem (Nat.le_refl _) (Nat.le_refl _) hm
    | br_table targets defTarget =>
      simp only [lowerSeq]; w_pop (pop32 stk), idx32 s1
      cases hget : labs[defTarget]? with | none => exact htrap | some defLbl =>
      dsimp only; w_pop (popArgsAux defLbl.argTys s1), ba s_
      exact emitBrTable_wp labs hlabs locs f hf0 (Nat.le_refl _) idx32 defLbl
        (List.mem_of_getElem? hget) ba hlen0 hm 0 targets
    | return_ =>
      simp only [lowerSeq]; w_pop (popArgsAux ctx.retTys stk), ra s_
      rw [wp_ret_]; exact ⟨Or.inl rfl, hf0, curLen, hlen0, hm⟩
    | block bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; w_pop (popArgsAux ft.params stk), ia sa
      exact lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _ hafter
        fun lbl' fall hlabs' hfall => ih _ (hlt (by simp +arith)) curLen f hf0 hlen0 hcal locs _
          (lbl' :: labs) hlabs' body (Nat.le_refl _) fall
          (fun _ _ _ _ _ hf' hcur' hm' _ _ => hfall _ _ _ _ _ hf' hcur' hm') hm
    | loop bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; w_pop (popArgsAux ft.params stk), ia sa
      refine lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _ hafter
        fun _ fall _ hfall => ?_
      rw [wp_group_]; intro JsHdr hclHdr; rw [closed_cons_] at hclHdr
      have hHdr : ∀ (n : Nat) curLen' (xs : Tup Val (labelSig ctx.locTys ft.params)) m',
          curLen.toNat ≤ curLen'.toNat → xs.1.toNat = n → n ≤ f.val.toNat →
          WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → JsHdr.1 xs m' := by
        intro n; induction n using Nat.strongRecOn with | _ n ihn =>
        intro curLen' xs m' hcur' hxn hnf hm'
        apply hclHdr.1 xs m'; wasm_wp_let; rw [wp_jnz_]
        refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl))
          (Nat.le_trans (hxn.symm ▸ hnf) hf0) (Nat.le_trans hlen0 hcur') hm', fun hz => ?_⟩
        have hSubLt := bv64_sub_one_lt (decide_eq_false_iff_not.mp hz)
        have hnextLe : (xs.1 - 1#64).toNat ≤ f.val.toNat := by omega
        wasm_wp_let; let fNext : Arg Val T.i64 := .var (xs.1 - 1#64)
        let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.params, JsHdr.1⟩
        have hlabs' : LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap fNext.val R
            (lbl' :: labs) := fun _ hl _ _ _ hcur'' hys hm'' => by
          rcases List.mem_cons.mp hl with rfl | hl
          · have hlt' : _ < n := Nat.lt_of_le_of_lt hys (hxn ▸ hSubLt)
            exact ihn _ hlt' _ _ _ (Nat.le_trans hcur' hcur'') rfl
              (Nat.le_trans (Nat.le_of_lt hlt') hnf) hm''
          · exact hlabs _ hl _ _ _ (Nat.le_trans hcur' hcur'') (Nat.le_trans hys hnextLe) hm''
        exact ih _ (hlt (by simp +arith)) curLen' fNext (Nat.le_trans hnextLe hf0)
          (Nat.le_trans hlen0 hcur') (WasmCalleeEnvOk.mono_fuel hnextLe hcal) _ _
          (lbl' :: labs) hlabs' body (Nat.le_refl _) fall
          (fun _ _ _ _ _ hf' hcur'' hm'' _ _ =>
            hfall _ _ _ _ _ (Nat.le_trans hf' hnextLe) (Nat.le_trans hcur' hcur'') hm'') hm'
      rw [wp_jump_]
      exact hHdr f.val.toNat curLen (vals (f, tupAppend locs ia)) mem (Nat.le_refl _) rfl
        (Nat.le_refl _) hm
    | if_ bt thenBody elseBody =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; w_pop (pop32 stk), cond stk1; w_pop (popArgsAux ft.params stk1), ia sa
      refine lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _ hafter
        fun lbl' fall hlabs' hfall => by
          wasm_wp_let; rw [wp_jnz_]
          refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> exact ih _ (hlt (by simp +arith)) curLen f hf0
            hlen0 hcal locs _ (lbl' :: labs) hlabs' _ (Nat.le_refl _) fall
            (fun _ _ _ _ _ hf' hcur' hm' _ _ => hfall _ _ _ _ _ hf' hcur' hm') hm
    | _ =>
      simp only [lowerSeq]
      exact lowerSimpleInstr_wp ctx hmem vc f hvc hf0 hlen0 hcal locs stk labs hlabs _ _
        (fun f' curLen' locs' stk' m' hf' hcur' hm' hl' hc' =>
          hafter curLen' f' locs' stk' m' hcur' hf' hm' hl' hc') hm

/-! ## Function & Module Soundness (`Func.wp`, `ModuleSccOk`, `Env.semScc`, `ModuleOk`) -/

/-- Universal function-level safety theorem: ANY lowered Wasm function body satisfies
`WasmPost` and preserves arbitrary host memory `R` under `WasmCalleeEnvOk`. -/
theorem lowerFuncBody_wp {Γ : Env} {X : XPost} (m : WModule) (f : WFunc) (ft : WFuncTy)
    {xs : Tup Val (wasmAbiParams ft)} {memBase memLen memCap : BitVec 64}
    {mem : Mem 64} {R : Mem 64 → Prop}
    (hm : WasmMemInv m.memory.isSome xs.1 memBase memLen memCap R mem)
    (hcal : WasmCalleeEnvOk Γ m.funcs m.types m.memory.isSome xs.1 memBase memCap xs.2.1 R) :
    Func.wp Γ (lowerFuncBody m f ft) xs mem
      (WasmPost m.memory.isSome xs.1 memBase memLen memCap xs.2.1 ft.results R) X := by
  simp only [Func.wp, lowerFuncBody]; rw [wp_group_]; intro Js hcl; rw [closed_cons_] at hcl
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  refine lowerSeq_wp_aux ctx rfl (.var xs.1) rfl (sizeOf f.body) memLen (.var xs.2.1)
    (Nat.le_refl _) (Nat.le_refl _) hcal _ [] [⟨ft.results, Js.1⟩]
    (fun _ hl _ _ _ hlen' hr hm' => by
      rcases List.mem_singleton.mp hl with rfl
      exact hcl.1 _ _ (by rw [wp_ret_]; exact ⟨Or.inl rfl, hr, _, hlen', hm'⟩))
    f.body (Nat.le_refl _) _ (fun _ _ _ stk' m' hf' hcur' hm' _ _ => by
      cases popArgsAux ft.results stk' with
      | none => exact wp_mkTrapExpr ft.results 1#32 (Or.inr (Or.inl rfl)) hf' hcur' hm'
      | some p =>
        rcases p with ⟨ra, _⟩; dsimp only; rw [wp_ret_]; exact ⟨Or.inl rfl, hf', _, hcur', hm'⟩)
    hm

/-- `callsOk` preservation for lowered Wasm instruction helpers and sequences. -/
private theorem emitBrTable_callsOk (allowed : List SigEntry) (exits : List Sym)
    (locTys retTys : List WValTy) (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) locTys))
    (locs : Tup (Arg (fun _ => Unit)) (locTys.map WValTy.toTy)) (f : Arg (fun _ => Unit) T.i64)
    (idx : Arg (fun _ => Unit) T.i32) (defLbl : WLabel (fun _ => Unit) (fun _ => Unit) locTys)
    (ba : Tup (Arg (fun _ => Unit)) (defLbl.argTys.map WValTy.toTy)) (i : Nat) (ts : List Nat) :
    (emitBrTable locTys retTys labs locs f idx defLbl ba i ts).callsOk allowed exits := by
  induction ts generalizing i with
  | nil => simp only [emitBrTable, Expr.callsOk]
  | cons t _ ih =>
    simp only [emitBrTable]; cases labs[t]? with | none => exact trivial | some l =>
    by_cases hlt : l.argTys = defLbl.argTys
    · simp only [hlt, ↓reduceDIte, Expr.callsOk]; exact ⟨trivial, ih (i + 1)⟩
    · simp only [hlt, ↓reduceDIte]; exact trivial

private theorem lowerSimpleInstr_callsOk (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym) (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed)
    (vc f : Arg (fun _ => Unit) T.i64)
    (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal (fun _ => Unit)))
    (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys)) (instr : WInstr)
    (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys)
    (hk : ∀ f' l' s', (k f' l' s').callsOk allowed exits) :
    (lowerSimpleInstr ctx vc f locs stk labs instr k).callsOk allowed exits := by
  cases instr with
  | load resTy width signed _ =>
    simp only [lowerSimpleInstr]; c_mem (ctx.hasMem && validateLoad resTy width signed) = true
    w_pop (pop32 stk), idx32 s1
    refine emitMemBounds_callsOk allowed exits ctx.retTys vc f idx32 _ _ _ fun _ => ?_
    cases resTy <;> cases width <;> cases signed <;> simp only [emitLoadCast, Expr.callsOk] <;>
      first | exact trivial | exact hk _ _ _
  | store srcTy width _ =>
    simp only [lowerSimpleInstr]; c_mem (ctx.hasMem && validateStore srcTy width) = true
    w_pop (popExpectS _ stk), sv s1; w_pop (pop32 s1), idx32 s2
    refine emitMemBounds_callsOk allowed exits ctx.retTys vc f idx32 _ _ _ fun _ => ?_
    cases srcTy <;> cases width <;> simp only [emitStoreCast, Expr.callsOk] <;>
      first | exact trivial | exact hk _ _ _
  | _ =>
  simp only [lowerSimpleInstr] <;> first
  | exact trivial | exact hk f locs _
  | (w_pop (pop32 stk), c r; cases labs[‹Nat›]? with | none => exact trivial | some l =>
     dsimp only; w_pop (popArgsAux l.argTys r), ba s_; exact ⟨trivial, hk f locs r⟩)
  | (cases hc : ctx.funcs[‹Nat›]? with | none => exact trivial | some callee =>
     dsimp only; cases hft : ctx.types[callee.typeIdx]? with | none => exact trivial | some ft =>
     dsimp only; w_pop (popArgsAux ft.params stk), ca s1
     exact ⟨trivial, hcal _ callee ft hc hft, hk _ locs _, trivial⟩)
  | (cases stk with | nil => exact trivial | cons _ r => exact hk f locs r)
  | (w_pop (pop32 stk), c r; cases r with | nil => exact trivial | cons v₂ r2 =>
     cases r2 with | nil => exact trivial | cons v₁ r3 =>
     cases v₁ <;> cases v₂ <;> simp only [Expr.callsOk] <;>
       first | exact trivial | exact hk f locs _)
  | (cases getLocal ctx.locTys locs ‹Nat› with
     | none => exact trivial | some _ => exact hk f locs _)
  | (cases stk with | nil => exact trivial | cons v r =>
     dsimp only; cases setLocal ctx.locTys locs ‹Nat› v with
     | none => exact trivial | some l' => exact hk f l' _)
  | (cases ctx.globals[‹Nat›]? with | none => exact trivial | some _ => exact hk f locs _)
  | (c_mem ctx.hasMem = true; exact emitMemSize_callsOk allowed exits vc _ fun _ => hk f locs _)
  | (c_mem ctx.hasMem = true; w_pop (pop32 stk), delta s1
     exact emitMemGrow_callsOk allowed exits ctx.retTys ctx.memMaxBytes vc f delta _
       fun f' r => hk f' locs (.i32 r :: s1))
  | (c_mem ctx.hasMem = true
     w_pop (pop32 stk), n32 s1; w_pop (pop32 s1), v32 s2; w_pop (pop32 s2), d32 s3
     exact emitMemFill_callsOk allowed exits ctx.retTys vc f d32 v32 n32 _ fun f' => hk f' locs s3)
  | (c_mem ctx.hasMem = true
     w_pop (pop32 stk), n32 s1; w_pop (pop32 s1), sr32 s2; w_pop (pop32 s2), d32 s3
     exact emitMemCopy_callsOk allowed exits ctx.retTys vc f d32 sr32 n32 _ fun f' => hk f' locs s3)
  | (cases ‹WValTy› <;> cases stk with | nil => exact trivial | cons x _ =>
     cases x <;> first | exact trivial | exact hk f locs _)
  | (w_pop (popExpectS _ stk), x s1
     cases ‹WValTy› <;> cases ‹WUnOp› <;> simp only [emitUnOp, emitPopcnt, emitPopcntCore,
       Expr.callsOk] <;> first | exact trivial | exact hk f locs _)
  | (w_pop (popExpectS _ stk), b s1; w_pop (popExpectS _ s1), a s2
     cases ‹WBinOp› <;> cases ‹WValTy› <;> simp only [emitBinOp, emitDivRemCore, Expr.callsOk] <;>
       repeat first | exact trivial | apply And.intro | exact hk f locs _)
  | (w_pop (popExpectS _ stk), b s1; w_pop (popExpectS _ s1), a s2
     cases ‹WValTy› <;> simp only [Expr.callsOk] <;> exact hk f locs _)
  | (w_pop (pop64 stk), x_ s1; exact hk f locs _)
  | (w_pop (pop32 stk), x_ s1; exact hk f locs _)

private theorem lowerGroupJoin_callsOk (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym) (ft : WFuncTy) (sa : List (SVal (fun _ => Unit)))
    (body : WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys →
      WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys →
      Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig ctx.retTys))
    (after : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys)
    (hbody : ∀ lbl fall, (∀ f' l' s', (fall f' l' s').callsOk allowed exits) →
      (body lbl fall).callsOk allowed exits)
    (hafter : ∀ f' l' s', (after f' l' s').callsOk allowed exits) :
    (lowerGroupJoin ctx ft sa body after).callsOk allowed exits :=
  ⟨⟨hafter _ _ _, trivial⟩,
    hbody _ _ fun _ _ s' => by w_pop (popArgsAux ft.results s'), ra s1; exact trivial⟩

private theorem lowerSeq_callsOk_aux (ctx : WLowerCtx) (allowed : List SigEntry) (exits : List Sym)
    (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed) :
    ∀ (sz : Nat) (vc f : Arg (fun _ => Unit) T.i64)
      (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal (fun _ => Unit)))
      (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys)) (instrs : List WInstr)
      (_hsz : sizeOf instrs ≤ sz) (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys),
      (∀ f' l' s', (k f' l' s').callsOk allowed exits) →
      (lowerSeq ctx vc f locs stk labs instrs k).callsOk allowed exits := by
  intro sz; induction sz using Nat.strongRecOn with | _ sz ih =>
  intro vc f locs stk labs instrs hsz k hk
  cases instrs with
  | nil => simp only [lowerSeq]; exact hk f locs stk
  | cons i rest =>
    have hlt {b : List WInstr} (h : sizeOf b < sizeOf (i :: rest)) : sizeOf b < sz :=
      Nat.lt_of_lt_of_le h hsz
    let hafter := fun (f' : Arg (fun _ => Unit) T.i64) l' s' =>
      ih _ (hlt (by simp +arith)) vc f' l' s' labs rest (Nat.le_refl _) k hk
    cases i with
    | unreachable => simp only [lowerSeq]; exact trivial
    | br depth =>
      simp only [lowerSeq]; cases labs[depth]? with | none => exact trivial | some lbl =>
      dsimp only; w_pop (popArgsAux lbl.argTys stk), ba s_; exact trivial
    | br_table targets defTarget =>
      simp only [lowerSeq]; w_pop (pop32 stk), idx32 s1
      cases labs[defTarget]? with | none => exact trivial | some defLbl =>
      dsimp only; w_pop (popArgsAux defLbl.argTys s1), ba s_
      exact emitBrTable_callsOk allowed exits ctx.locTys ctx.retTys labs locs f idx32 defLbl ba
        0 targets
    | return_ => simp only [lowerSeq]; w_pop (popArgsAux ctx.retTys stk), ra s_; exact trivial
    | block bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact trivial | some ft =>
      dsimp only; w_pop (popArgsAux ft.params stk), ia sa
      exact lowerGroupJoin_callsOk ctx allowed exits ft sa _ _ (fun _ fall hfall =>
        ih _ (hlt (by simp +arith)) vc f locs _ _ body (Nat.le_refl _) fall hfall) hafter
    | loop bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact trivial | some ft =>
      dsimp only; w_pop (popArgsAux ft.params stk), ia sa
      refine lowerGroupJoin_callsOk ctx allowed exits ft sa _ _ (fun _ fall hfall => ?_) hafter
      exact ⟨⟨⟨trivial, ih _ (hlt (by simp +arith)) vc _ _ _ _ body (Nat.le_refl _)
        fall hfall⟩, trivial⟩, trivial⟩
    | if_ bt thenBody elseBody =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact trivial | some ft =>
      dsimp only; w_pop (pop32 stk), c s1; w_pop (popArgsAux ft.params s1), ia sa
      refine lowerGroupJoin_callsOk ctx allowed exits ft sa _ _ (fun _ fall hfall => ?_) hafter
      simp only [Expr.callsOk]
      constructor <;> exact ih _ (hlt (by simp +arith)) vc f locs _ _ _ (Nat.le_refl _) fall hfall
    | _ =>
      simp only [lowerSeq]
      exact lowerSimpleInstr_callsOk ctx allowed exits hcal vc f locs stk labs _ _ hafter

/-- Every lowered function only invokes intra-module functions at their lowered ABI signatures. -/
theorem lowerFn_callsOk (m : WModule) (f : WFunc) :
    (lowerFn m f).callsOk (lowerModule m).sigs (lowerModule m).exits := by
  simp only [Fn.callsOk, lowerFn, lowerFuncBody, Expr.callsOk, Blocks.callsOk]
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  let ft := (m.types[f.typeIdx]?).getD {}
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  refine lowerSeq_callsOk_aux ctx (lowerModule m).sigs (lowerModule m).exits
    (fun _ callee cft hc hft => by
      have hsig : (lowerFn m callee).sig ∈ (lowerModule m).fns.map Fn.sig :=
        List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_of_getElem? hc, rfl⟩, rfl⟩
      have hceq : (m.types[callee.typeIdx]?).getD {} = cft := by
        simp [show m.types = ctx.types from rfl, hft]
      simp only [Fn.sig, lowerFn] at hsig; rw [hceq] at hsig; exact List.mem_append_left _ hsig)
    (sizeOf f.body) _ _ _ [] _ f.body (Nat.le_refl _) _ fun _ _ s' => by
      cases popArgsAux ft.results s' with | none => exact trivial | some _ => exact trivial

/-- Helper: when `m.funcs.map WFunc.name` is `Nodup`, any two functions with the same name are
identical. -/
private theorem func_eq_of_namesNodup {fs : List WFunc} (hnd : (fs.map WFunc.name).Nodup)
    {f₁ f₂ : WFunc} (h1 : f₁ ∈ fs) (h2 : f₂ ∈ fs) (heq : f₁.name = f₂.name) : f₁ = f₂ := by
  induction fs with
  | nil => cases h1
  | cons _ _ ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd heq.symm (hnd.1 f₂ h2')
    · exact absurd heq (hnd.1 f₁ h1')
    · exact ih hnd.2 h1' h2'

private theorem wasmSandboxEnv_callee (m : WModule) (callee : WFunc) (hmem : callee ∈ m.funcs)
    (ft : WFuncTy) (hft : m.types[callee.typeIdx]? = some ft)
    {vmCtx memBase curLen memCap f' : BitVec 64} {args : Tup Val (ft.params.map WValTy.toTy)}
    {mem' : Mem 64} {R : Mem 64 → Prop}
    (hm' : WasmMemInv m.memory.isSome vmCtx memBase curLen memCap R mem') :
    WasmSandboxEnv m f'.toNat callee.name (wasmAbiParams ft) (wasmAbiResults ft)
      (vmCtx, f', args) mem' (WasmPost m.memory.isSome vmCtx memBase curLen memCap f' ft.results R)
      (fun _ _ _ _ => False) := by
  have hftEq : ft = (m.types[callee.typeIdx]?).getD {} := by simp [hft]
  subst hftEq; exact ⟨callee, hmem, rfl, rfl, rfl, Nat.le_refl _, memBase, curLen, memCap, R, hm',
    fun _ _ h => h⟩

private theorem wasmSandboxEnv_wp {m : WModule} (hnd : (m.funcs.map WFunc.name).Nodup) {Γ : Env}
    {i : Nat} {f : WFunc} (hf : f ∈ m.funcs)
    {xs : Tup Val (wasmAbiParams ((m.types[f.typeIdx]?).getD {}))} {mem : Mem 64}
    {Q : Post (wasmAbiResults ((m.types[f.typeIdx]?).getD {}))} {X : XPost}
    (hspec : WasmSandboxEnv m i f.name (wasmAbiParams ((m.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((m.types[f.typeIdx]?).getD {})) xs mem Q X)
    (hcal : ∀ memBase curLen memCap R, xs.2.1.toNat ≤ i →
      WasmMemInv m.memory.isSome xs.1 memBase curLen memCap R mem →
      WasmCalleeEnvOk Γ m.funcs m.types m.memory.isSome xs.1 memBase memCap xs.2.1 R) :
    Func.wp Γ (lowerFn m f).body xs mem Q X := by
  rcases hspec with ⟨f', hf', ha, hb, heq, hfuel, memBase, curLen, memCap, R, hm, hpost⟩
  cases func_eq_of_namesNodup hnd hf hf' heq
  have hba : ha = rfl := Subsingleton.elim _ _; have hbb : hb = rfl := Subsingleton.elim _ _
  subst hba; subst hbb; dsimp only at hfuel hm hpost
  exact wp_mono hpost (fun _ _ _ _ h => h) _ mem
    (lowerFuncBody_wp m f _ hm (hcal memBase curLen memCap R hfuel hm) (X := X))

/-- Universal `ModuleSccOk` theorem: EVERY validated Wasm module lowered via `lowerModule`
satisfies `ModuleSccOk` under fuel-indexed `WasmSandboxEnv` (for arbitrary external contracts
`Γext` and arbitrary host memory frame `R`). -/
theorem lowerModule_moduleSccOk {m : WModule} (hv : validateModule m = true) (Γext : Env) :
    ModuleSccOk natRecIdx (WasmSandboxEnv m) Γext false (lowerModule m) := by
  have hnd := lowerModule_namesNodup hv
  have hfnd : (m.funcs.map WFunc.name).Nodup := by
    simpa [Module.namesNodup, Module.names, lowerModule, Function.comp_def, lowerFn] using hnd
  refine ⟨hnd, fun fn hfn => ?_⟩; obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfn
  refine ⟨lowerFuncBody_wf m f _, lowerFn_callsOk m f, fun i xs mem Q X hspec =>
    wasmSandboxEnv_wp hfnd hf hspec fun _ _ _ _ hfuel _ _ callee ft hc hft _ f' _ m' hlt hm' => ?_⟩
  have hcmem := List.mem_of_getElem? hc
  have hsig :
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ (lowerModule m).fns.map Fn.sig := by
    have hm2 : (lowerFn m callee).sig ∈ (lowerModule m).fns.map Fn.sig :=
      List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, hcmem, rfl⟩, rfl⟩
    simp only [Fn.sig, lowerFn, hft, Option.getD_some] at hm2; exact hm2
  exact Or.inl ⟨hsig, f'.toNat, Nat.lt_of_lt_of_le hlt hfuel, Or.inl rfl,
    wasmSandboxEnv_callee m callee hcmem ft hft hm'⟩

/-- Universal `Env.semScc` soundness theorem: ANY validated Wasm module `m` lowered via
`lowerModule` embeds `WasmSandboxEnv m` into `Env.semScc (lowerModule m) Γext`. -/
theorem lowerModule_semScc {m : WModule} (hv : validateModule m = true) (Γext : Env) :
    ∀ i, Env.le (Env.restrict (WasmSandboxEnv m i) ((lowerModule m).fns.map Fn.sig))
      (Env.semScc (lowerModule m) Γext) :=
  moduleSccOk_le_semScc (lowerModule_moduleSccOk hv Γext)

/-- Acyclic `ModuleOk` theorem: whenever `validateModule m = true` and
`(lowerModule m).checkAcyclic = true`, `(lowerModule m)` satisfies `ModuleOk (WasmSandboxEnvAny m)`.
-/
theorem lowerModule_moduleOk {m : WModule} (hv : validateModule m = true)
    (hacyc : (lowerModule m).checkAcyclic = true) :
    ModuleOk (WasmSandboxEnvAny m) (lowerModule m) := by
  have hfnd := (validateModule_elim hv).1
  refine Module.moduleOk_of_checkAcyclic hacyc (lowerModule_wf m) fun fn hfn xs mem Q X hspec => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfn; rcases hspec with ⟨i, hi⟩
  exact wasmSandboxEnv_wp hfnd hf hi fun _ _ _ _ _ _ _ callee ft hc hft _ f' _ m' _ hm' =>
    ⟨f'.toNat, wasmSandboxEnv_callee m callee (List.mem_of_getElem? hc) ft hft hm'⟩

/-- Primary user-facing theorem: ANY validated Wasm module lowered via `lowerModule` preserves
arbitrary host memory `R` outside the VM context + backing guest region (`vmCtx`, `memBase`,
`memCap`), grows memory length monotonically (`memLen ≤ memLen'`), never performs OOB accesses or
division-by-zero / `INT_MIN / -1`, and terminates cleanly with status `{0#32, 1#32, 2#32}`. -/
theorem wasm_preserves_host_mem {m : WModule} (hv : validateModule m = true)
    (Γext : Env) {f : WFunc} (hf : f ∈ m.funcs)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (args : Tup Val (((m.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv m.memory.isSome vmCtx memBase memLen memCap R mem)
    (Q : Post (wasmAbiResults ((m.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost m.memory.isSome vmCtx memBase memLen memCap fuel
      ((m.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc (lowerModule m) Γext f.name
      (wasmAbiParams ((m.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((m.types[f.typeIdx]?).getD {})) (vmCtx, fuel, args) mem Q X :=
  lowerModule_semScc hv Γext fuel.toNat _ _ _ _ _ _ _
    ⟨List.mem_map.mpr ⟨lowerFn m f, List.mem_map.mpr ⟨f, hf, rfl⟩, rfl⟩,
     ⟨f, hf, rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap, R, hmem, hpost⟩⟩

mutual
/-- Check that all `.call` targets inside `i` have function index `< bound`. -/
@[expose] def wasmInstrCallsBelow (bound : Nat) : WInstr → Bool
  | .block _ body => wasmSeqCallsBelow bound body
  | .loop _ body => wasmSeqCallsBelow bound body
  | .if_ _ t e => wasmSeqCallsBelow bound t && wasmSeqCallsBelow bound e
  | .call fnIdx => decide (fnIdx < bound)
  | _ => true

/-- Check that all `.call` targets in an instruction sequence have function index `< bound`. -/
@[expose] def wasmSeqCallsBelow (bound : Nat) : List WInstr → Bool
  | [] => true
  | i :: rest => wasmInstrCallsBelow bound i && wasmSeqCallsBelow bound rest
end

/-- Check that every function in `fs` (starting at index `idx`) only calls earlier functions. -/
@[expose] def wasmAcyclicAux (idx : Nat) : List WFunc → Bool
  | [] => true
  | f :: fs => wasmSeqCallsBelow idx f.body && wasmAcyclicAux (idx + 1) fs

/-- Decidable syntactic callee-first acyclicity check on a `WModule`. -/
@[expose] def wasmAcyclic (m : WModule) : Bool := wasmAcyclicAux 0 m.funcs

private theorem lowerSimpleInstr_take_eq {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs)
    (vc f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instr : WInstr)
    (hb : wasmInstrCallsBelow bound instr = true) (k : WCont V L ctx.locTys ctx.retTys) :
    lowerSimpleInstr { ctx with funcs := fs.take bound } vc f locs stk labs instr k =
      lowerSimpleInstr ctx vc f locs stk labs instr k := by
  subst hfs; cases instr with
  | call fnIdx =>
    simp only [wasmInstrCallsBelow, decide_eq_true_eq] at hb
    simp only [lowerSimpleInstr, List.getElem?_take_of_lt hb]
  | br_if depth =>
    simp only [lowerSimpleInstr]; cases pop32 stk <;> cases labs[depth]? <;>
    first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
  | local_set idx | local_tee idx =>
    simp only [lowerSimpleInstr]; cases stk <;>
    first | rfl | (dsimp only; cases setLocal ctx.locTys locs idx _ <;> rfl)
  | _ => simp only [lowerSimpleInstr] <;> try rfl

private theorem lowerGroupJoin_take_eq {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (funcs' : List WFunc) (ft : WFuncTy) (sa : List (SVal V))
    (body₁ body₂ : WLabel V L ctx.locTys → WCont V L ctx.locTys ctx.retTys →
      Expr V L (wasmRetSig ctx.retTys))
    (after₁ after₂ : WCont V L ctx.locTys ctx.retTys)
    (hbody : ∀ lbl fall, body₁ lbl fall = body₂ lbl fall)
    (hafter : ∀ f' l' s', after₁ f' l' s' = after₂ f' l' s') :
    lowerGroupJoin { ctx with funcs := funcs' } ft sa body₁ after₁ =
      lowerGroupJoin ctx ft sa body₂ after₂ := by
  simp only [lowerGroupJoin]
  exact congr (congrArg Expr.group (funext fun ⟨_, ()⟩ =>
    congrArg (Blocks.cons · Blocks.nil) (funext fun ⟨_, _⟩ => hafter _ _ _)))
    (funext fun ⟨_, ()⟩ => hbody _ _)

private theorem lowerSeq_take_eq_aux {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs) (sz : Nat) :
    ∀ (vc f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instrs : List WInstr),
      sizeOf instrs ≤ sz → wasmSeqCallsBelow bound instrs = true →
      ∀ (k₁ k₂ : WCont V L ctx.locTys ctx.retTys), (∀ f' l' s', k₁ f' l' s' = k₂ f' l' s') →
        lowerSeq { ctx with funcs := fs.take bound } vc f locs stk labs instrs k₁ =
          lowerSeq ctx vc f locs stk labs instrs k₂ := by
  induction sz with
  | zero => intro _ _ _ _ _ instrs hsz _ _ _ hk; cases instrs with
    | nil => simp only [lowerSeq]; exact hk _ _ _
    | cons _ _ => simp +arith at hsz
  | succ sz ih =>
    intro vc f locs stk labs instrs hsz hb k₁ k₂ hk
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk
    | cons instr rest =>
      have hsle {b : List WInstr} (h : sizeOf b < sizeOf (instr :: rest)) : sizeOf b ≤ sz :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hsz)
      simp only [wasmSeqCallsBelow, Bool.and_eq_true] at hb; rcases hb with ⟨hi, hrest⟩
      have hsr : sizeOf rest ≤ sz := hsle (by simp +arith)
      cases instr with
      | block bt body =>
        simp only [wasmInstrCallsBelow] at hi; simp only [lowerSeq]
        cases bt.resolve ctx.types with | none => rfl | some ft =>
        dsimp only; cases popArgsAux ft.params stk with | none => rfl | some _ =>
        exact lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
          (fun _ _ => ih _ _ _ _ _ body (hsle (by simp +arith)) hi _ _ fun _ _ _ => rfl)
          (fun _ _ _ => ih _ _ _ _ _ rest hsr hrest _ _ hk)
      | loop bt body =>
        simp only [wasmInstrCallsBelow] at hi; simp only [lowerSeq]
        cases bt.resolve ctx.types with | none => rfl | some ft =>
        dsimp only; cases popArgsAux ft.params stk with | none => rfl | some _ =>
        refine lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
          (fun _ _ => congrArg (Expr.group · _) (funext fun _ =>
            congrArg (Blocks.cons · Blocks.nil) (funext fun _ =>
              congrArg (Expr.let_ _) (funext fun _ => congrArg (Expr.jnz _ _)
                (congrArg (Expr.let_ _) (funext fun _ =>
                  ih _ _ _ _ _ body (hsle (by simp +arith)) hi _ _ fun _ _ _ => rfl))))))
          (fun _ _ _ => ih _ _ _ _ _ rest hsr hrest _ _ hk)
      | if_ bt thenBody elseBody =>
        simp only [wasmInstrCallsBelow, Bool.and_eq_true] at hi; simp only [lowerSeq]
        cases bt.resolve ctx.types with | none => rfl | some ft =>
        dsimp only; cases pop32 stk with | none => rfl | some _ =>
        dsimp only; cases popArgsAux ft.params _ with | none => rfl | some _ =>
        refine lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
          (fun _ _ => congrArg (Expr.let_ _) (funext fun _ =>
            congr (congrArg (Expr.jnz _)
              (ih _ _ _ _ _ thenBody (hsle (by simp +arith)) hi.1 _ _ fun _ _ _ => rfl))
              (ih _ _ _ _ _ elseBody (hsle (by simp +arith)) hi.2 _ _ fun _ _ _ => rfl)))
          (fun _ _ _ => ih _ _ _ _ _ rest hsr hrest _ _ hk)
      | unreachable => simp only [lowerSeq]
      | br depth =>
        simp only [lowerSeq]; cases labs[depth]? <;>
        first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
      | br_table _ defT =>
        simp only [lowerSeq]; cases pop32 stk <;> cases labs[defT]? <;>
        first | rfl | (dsimp only; cases popArgsAux _ _ <;> rfl)
      | return_ => simp only [lowerSeq]; cases popArgsAux ctx.retTys stk <;> rfl
      | _ =>
        simp only [lowerSeq]; first | rfl | (
          rw [lowerSimpleInstr_take_eq ctx fs bound hfs vc f locs stk labs _ hi]
          exact congrArg (lowerSimpleInstr ctx vc f locs stk labs _)
            (funext fun _ => funext fun _ => funext fun _ =>
              ih _ _ _ _ _ rest hsr hrest k₁ k₂ hk))

private theorem lowerFn_callsOk_take (m : WModule) (bound : Nat) (f : WFunc)
    (hb : wasmSeqCallsBelow bound f.body = true) :
    (lowerFn m f).callsOk ((m.funcs.take bound).map (fun c => (lowerFn m c).sig)) [] := by
  have h1 := lowerFn_callsOk { m with funcs := m.funcs.take bound } f
  have hmodEq : (lowerModule { m with funcs := m.funcs.take bound }).sigs =
      (m.funcs.take bound).map (fun c => (lowerFn m c).sig) := by
    simp only [Module.sigs, lowerModule, List.map_map, List.map_nil, List.append_nil]; try rfl
  have hbodyEq :
      ((lowerFn { m with funcs := m.funcs.take bound } f).body (fun _ => Unit) (fun _ => Unit)
        (Tup.units (lowerFn { m with funcs := m.funcs.take bound } f).as)) =
      ((lowerFn m f).body (fun _ => Unit) (fun _ => Unit) (Tup.units (lowerFn m f).as)) := by
    simp only [lowerFn, lowerFuncBody]
    refine congrArg (Expr.group _) (funext fun _ => ?_)
    let ctx : WLowerCtx :=
      { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
        memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64, globals := m.globals,
        locTys := ((m.types[f.typeIdx]?).getD {}).params ++ f.locals,
        retTys := ((m.types[f.typeIdx]?).getD {}).results }
    exact lowerSeq_take_eq_aux ctx m.funcs bound rfl (sizeOf f.body)
      _ _ _ [] _ f.body (Nat.le_refl _) hb _ _ (fun _ _ _ => rfl)
  rw [hmodEq] at h1
  change Expr.callsOk ((m.funcs.take bound).map (fun c => (lowerFn m c).sig)) []
      ((lowerFn { m with funcs := m.funcs.take bound } f).body (fun _ => Unit) (fun _ => Unit)
        (Tup.units (lowerFn { m with funcs := m.funcs.take bound } f).as)) at h1
  rwa [hbodyEq] at h1

private theorem wasmAcyclicAux_drop :
    ∀ (fs : List WFunc) (idx : Nat), wasmAcyclicAux idx fs = true →
      ∀ (k : Nat) (f : WFunc), fs[k]? = some f → wasmSeqCallsBelow (idx + k) f.body = true
  | [], _, _, _, _, hk => by cases hk
  | _ :: _, idx, ha, 0, _, hk => by
    cases hk; simp only [wasmAcyclicAux, Bool.and_eq_true] at ha; simpa using ha.1
  | _ :: rest, idx, ha, k + 1, f, hk => by
    simp only [wasmAcyclicAux, Bool.and_eq_true] at ha
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      wasmAcyclicAux_drop rest (idx + 1) ha.2 k f hk

/-- Universal acyclicity theorem: ANY validated callee-first Wasm module (`validateModule m = true`
and `wasmAcyclic m = true`) lowers to a QBE module satisfying `(lowerModule m).checkAcyclic = true`
without requiring kernel reduction of `lowerSeq`. -/
theorem lowerModule_checkAcyclic {m : WModule} (hv : validateModule m = true)
    (hacyc : wasmAcyclic m = true) : (lowerModule m).checkAcyclic = true := by
  have hnd : (lowerModule m).checkNamesNodup = true := by
    rw [Module.checkNamesNodup, listNodup_iff]; exact lowerModule_namesNodup hv
  have hcalls : Module.checkFnsCallsOk [] [] [] (m.funcs.map (lowerFn m)) = true := by
    refine checkFnsCallsOk_of_forall [] [] [] (m.funcs.map (lowerFn m)) fun pre fn post hsp => ?_
    have hfnEq : (m.funcs.map (lowerFn m))[pre.length]? = some fn := by
      rw [hsp, List.getElem?_append_right (Nat.le_refl _)]; simp
    rw [List.getElem?_map] at hfnEq
    cases hw : m.funcs[pre.length]? with
    | none => simp [hw] at hfnEq
    | some f =>
      simp only [hw, Option.map_some, Option.some.injEq] at hfnEq; subst hfnEq
      have htake : pre = (m.funcs.take pre.length).map (lowerFn m) := by
        have h1 : (m.funcs.map (lowerFn m)).take pre.length = pre := by rw [hsp, List.take_left]
        rw [← List.map_take] at h1; exact h1.symm
      have hsig :
          pre.map Fn.sig = (m.funcs.take pre.length).map (fun c => (lowerFn m c).sig) := by
        conv => lhs; rw [htake]
        rw [List.map_map]; rfl
      simpa [List.append_nil, hsig] using lowerFn_callsOk_take m pre.length f
        (by simpa using wasmAcyclicAux_drop m.funcs 0 hacyc pre.length f hw)
  simp only [Module.checkAcyclic, Bool.and_eq_true, lowerModule] at hnd ⊢; exact ⟨hnd, hcalls⟩

end LeanQbe.T.Wasm
