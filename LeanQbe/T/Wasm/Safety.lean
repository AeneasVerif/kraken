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


private theorem emitPopcntCore_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (n : Nat) (m1 m2 m4 mul sh : BitVec n) (x : Arg Val (.bits n))
    (k : Arg Val (.bits n) → Expr Val Cont rs) (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitPopcntCore n m1 m2 m4 mul sh x k) m := by
  simp only [emitPopcntCore]
  repeat' (rw [wp_let_]; simp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte])
  exact hk _

private theorem emitPopcnt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (w : WValTy) (x : Arg Val w.toTy) (k : Arg Val w.toTy → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitPopcnt w x k) m := by
  cases w <;> exact emitPopcntCore_wp _ _ _ _ _ _ x k hk

private theorem emitUnOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (w : WValTy) (op : WUnOp) (x : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitUnOp retTys fuel w op x k) mem := by
  cases w <;> cases op <;> simp only [emitUnOp] <;>
  first
  | exact emitPopcnt_wp _ x k hk
  | exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  | (repeat' wasm_wp_let); exact hk _

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

private theorem emitDivRemCore_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (n : Nat) (minC neg1C : BitVec n) (signed trapOvf : Bool)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (hcode : ∀ (x y : BitVec n) (Q' : Tup Val [.bits n] → Prop),
      decide (y = 0#n) = false →
      (signed = true → (decide (x = minC) && decide (y = neg1C)) = false) →
      (∀ r, Q' (r, ())) → OpCode.wp code (x, y, ()) Q')
    (a b : Arg Val (.bits n))
    (k : Arg Val (.bits n) → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitDivRemCore retTys fuel n minC neg1C signed trapOvf code a b k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  simp only [emitDivRemCore]
  wasm_wp_let
  rw [wp_jnz_]
  refine ⟨fun _ => htrap, fun hz => ?_⟩
  rw [arg_var_val] at hz
  cases signed <;> simp only [↓reduceIte, Bool.false_eq_true]
  · rw [wp_let_]; exact hcode a.val b.val _ hz (fun h => by cases h) (fun r => hk (.var r))
  · repeat' wasm_wp_let
    rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun hov => ?_⟩
    · cases trapOvf <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
        first | exact htrap | exact hk _
    · rw [arg_var_val] at hov
      rw [wp_let_]; exact hcode a.val b.val _ hz (fun _ => hov) (fun r => hk (.var r))

private theorem emitBinOp_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (w : WValTy) (op : WBinOp) (a b : Arg Val w.toTy)
    (k : Arg Val w.toTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitBinOp retTys fuel w op a b k) mem := by
  cases op <;> cases w <;> simp only [emitBinOp] <;>
  first
  | (wasm_wp_let; exact hk _)
  | (refine emitDivRemCore_wp hf hlen0 hm _ _ _ false false _ ?_ a b k hk
     intro x y Q' hz _ hQ; simp only [OpCode.wp]
     exact ⟨by simpa [BitVec.toNat_eq] using of_decide_eq_false hz, hQ _⟩)
  | (refine emitDivRemCore_wp hf hlen0 hm _ _ _ true _ _ ?_ a b k hk
     intro x y Q' hz hs hQ; simp only [OpCode.wp]
     exact ⟨sdivDefined_of_guards rfl rfl hz (hs rfl), hQ _⟩)

private theorem emitLoadCast_wp {Γ : Env} {X : XPost} {hasMem : Bool}
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {retTys : List WValTy}
    {fuel : Arg Val T.i64} (hf : fuel.val.toNat ≤ fuel0.toNat)
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
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
    (hlen0 : memLen0.toNat ≤ curLen.toNat)
    {R : Mem 64 → Prop} {mem : Mem 64} (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem)
    (srcTy : WValTy) (width : WMemWidth) (v : Arg Val srcTy.toTy)
    (k : Arg Val width.memTy → Expr Val Cont (wasmRetSig retTys))
    (hk : ∀ y, wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X (k y) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
      (emitStoreCast (mkTrapExpr retTys 1#32 fuel) srcTy width v k) mem := by
  have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) retTys 1#32 (Or.inr (Or.inl rfl)) hf hlen0 hm
  cases srcTy <;> cases width <;> simp only [emitStoreCast] <;>
  first | exact htrap | exact hk _ | (wasm_wp_let; exact hk _)

private theorem emitSelect_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {trap : Expr Val Cont rs} (htrap : wp Γ Q X trap m)
    (c : Arg Val T.i32) (v1 v2 : SVal Val) (k : SVal Val → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitSelect trap c v1 v2 k) m := by
  cases v1 <;> cases v2 <;> simp only [emitSelect] <;>
  first | exact htrap | ((repeat' wasm_wp_let); exact hk _)

private theorem emitEqz_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (w : WValTy) (x : Arg Val w.toTy) (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitEqz w x k) m := by
  cases w <;> simp only [emitEqz] <;> (repeat' wasm_wp_let) <;> exact hk _

private theorem emitRelOp_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (w : WValTy) (op : WRelOp) (a b : Arg Val w.toTy) (k : Arg Val T.i32 → Expr Val Cont rs)
    (hk : ∀ y, wp Γ Q X (k y) m) :
    wp Γ Q X (emitRelOp w op a b k) m := by
  cases w <;> simp only [emitRelOp] <;> (repeat' wasm_wp_let) <;> exact hk _

private theorem eqRec_cont_wp {locTys : List WValTy} {ts₁ ts₂ : List WValTy}
    {hasMem : Bool} {vmCtx memBase curLen memCap fuel : BitVec 64} {R : Mem 64 → Prop}
    (h : ts₁ = ts₂) (J : Cont (labelSig locTys ts₁))
    (args : Tup Val (labelSig locTys ts₂)) (m : Mem 64)
    (hJ : ∀ curLen' (xs : Tup Val (labelSig locTys ts₁)) m', curLen.toNat ≤ curLen'.toNat →
      xs.1.toNat ≤ fuel.toNat → WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → J xs m')
    (hf : args.1.toNat ≤ fuel.toNat)
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R m) :
    (h ▸ J) args m := by
  subst h
  exact hJ curLen args m (Nat.le_refl _) hf hm

private theorem emitBrTable_wp {Γ : Env} {X : XPost} {locTys retTys : List WValTy}
    {hasMem : Bool} {vmCtx memBase memLen0 curLen memCap fuel0 curFuel : BitVec 64}
    {R : Mem 64 → Prop} (labs : List (WLabel Val Cont locTys))
    (hlabs : LabsSafe locTys hasMem vmCtx memBase curLen memCap curFuel R labs)
    (locs : Tup (Arg Val) (locTys.map WValTy.toTy))
    (f : Arg Val T.i64) (hf0 : f.val.toNat ≤ fuel0.toNat) (hf : f.val.toNat ≤ curFuel.toNat)
    (idx : Arg Val T.i32) (defLbl : WLabel Val Cont locTys) (hdef : defLbl ∈ labs)
    (ba : Tup (Arg Val) (defLbl.argTys.map WValTy.toTy))
    (hlen0 : memLen0.toNat ≤ curLen.toNat) {mem : Mem 64}
    (hm : WasmMemInv hasMem vmCtx memBase curLen memCap R mem) :
    ∀ (i : Nat) (ts : List Nat),
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 retTys R) X
        (emitBrTable locTys retTys labs locs f idx defLbl ba i ts) mem := by
  intro i ts
  induction ts generalizing i with
  | nil =>
    simp only [emitBrTable]; rw [wp_jump_]
    exact hlabs defLbl hdef curLen _ mem (Nat.le_refl _) hf hm
  | cons t rest ih =>
    simp only [emitBrTable]
    cases hget : labs[t]? with
    | none => exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hlen0 hm
    | some lbl =>
      have hlblMem : lbl ∈ labs := List.mem_of_getElem? hget
      by_cases hty : lbl.argTys = defLbl.argTys
      · simp only [hty, ↓reduceDIte]
        wasm_wp_let
        rw [wp_jnz_]
        refine ⟨fun _ => ?_, fun _ => ih (i + 1)⟩
        rw [wp_jump_]
        exact eqRec_cont_wp hty lbl.lbl (vals (f, tupAppend locs ba)) mem
          (hlabs lbl hlblMem) hf hm
      · simp only [hty, ↓reduceDIte]
        exact wp_mkTrapExpr retTys 1#32 (Or.inr (Or.inl rfl)) hf0 hlen0 hm

private theorem lowerSimpleInstr_wp {Γ : Env} {X : XPost} (ctx : WLowerCtx)
    {hasMem : Bool} (hmem : ctx.hasMem = hasMem)
    {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64}
    {R : Mem 64 → Prop} (vc f : Arg Val T.i64)
    (hvc : vc.val = vmCtx) (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (hcal : WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R)
    (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
    (labs : List (WLabel Val Cont ctx.locTys))
    (hlabs : LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs)
    (instr : WInstr) (k : WCont Val Cont ctx.locTys ctx.retTys)
    (hk : ∀ f' curLen' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
      curLen.toNat ≤ curLen'.toNat →
      WasmMemInv hasMem vmCtx memBase curLen' memCap R mem' →
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
  have hk0 : ∀ (locs' : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) stk',
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (k f locs' stk') mem :=
    fun locs' stk' => hk f curLen locs' stk' mem (Nat.le_refl _) (Nat.le_refl _) hm hlabs hcal
  cases instr with
  | load resTy width signed _ =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]
      have hhm : hasMem = true := by simp only [Bool.and_eq_true] at hok; rw [← hmem, hok.1]
      subst hhm
      cases pop32 stk with
      | none => exact htrap
      | some p =>
        rcases p with ⟨idx32, s1⟩; dsimp only
        refine emitMemBounds_wp vc f hvc hf0 hlen0 hm idx32 _ _ _ fun ea hba =>
          wp_wasm_load_w hm _ hba fun raw =>
            emitLoadCast_wp hf0 hlen0 hm _ _ _ raw _ fun v => hk0 locs (SVal.ofArg _ v :: s1)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | store srcTy width _ =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]
      have hhm : hasMem = true := by simp only [Bool.and_eq_true] at hok; rw [← hmem, hok.1]
      subst hhm
      cases popExpectS _ stk with
      | none => exact htrap
      | some p =>
        rcases p with ⟨sv, s1⟩; dsimp only
        cases pop32 s1 with
        | none => exact htrap
        | some p2 =>
          rcases p2 with ⟨idx32, s2⟩; dsimp only
          refine emitMemBounds_wp vc f hvc hf0 hlen0 hm idx32 _ _ _ fun ea hba =>
            emitStoreCast_wp hf0 hlen0 hm _ _ sv _ fun memVal =>
              wp_wasm_store_w hm _ hba memVal fun _ hm' =>
                hk f curLen locs s2 _ (Nat.le_refl _) (Nat.le_refl _) hm' hlabs hcal
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap
  | _ =>
  simp only [lowerSimpleInstr] <;>
  first
  | exact htrap
  | exact hk0 locs _
  | (cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨c, r⟩
      cases hget : labs[‹Nat›]? with
      | none => exact htrap
      | some lbl =>
        have hlblMem : lbl ∈ labs := List.mem_of_getElem? hget
        dsimp only
        cases popArgsAux lbl.argTys r with
        | none => exact htrap
        | some p' =>
          rcases p' with ⟨ba, _⟩; dsimp only
          wasm_wp_let; rw [wp_jnz_]
          refine ⟨fun _ => ?_, fun _ => hk0 locs r⟩
          rw [wp_jump_]
          exact hlabs lbl hlblMem curLen _ mem (Nat.le_refl _) (Nat.le_refl _) hm)
  | (cases hc : ctx.funcs[‹Nat›]? with
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
          rcases p with ⟨ca, s1⟩; dsimp only
          wasm_wp_let; rw [wp_jnz_]
          refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl)) hf0 hlen0 hm,
            fun hz => ?_⟩
          have hlt : (f.val - 1#64).toNat < f.val.toNat :=
            bv64_sub_one_lt (decide_eq_false_iff_not.mp hz)
          wasm_wp_let; rw [wp_call_]
          refine ⟨WasmPost hasMem vmCtx memBase curLen memCap (f.val - 1#64) ft.results R,
            fun _ _ _ _ => False, ?_, ?_, fun _ _ _ _ h => False.elim h⟩
          · rw [vals_wasmAbi, hvc]
            exact hcal _ callee ft hc hft curLen (f.val - 1#64) (vals ca) mem hlt hm
          · intro r m' ⟨hst, hrf, curLen', hcurLe, hm'⟩
            wasm_wp_let; rw [wp_jnz_]
            have hle : r.2.1.toNat ≤ f.val.toNat := Nat.le_trans hrf (Nat.le_of_lt hlt)
            refine ⟨fun _ => hk (.var r.2.1) curLen' locs
                (pushArgsAux ft.results (varsTup r.2.2) s1) m' hle hcurLe hm'
                (LabsSafe.mono hcurLe hle hlabs) (WasmCalleeEnvOk.mono_fuel hle hcal),
              fun _ => wp_mkStatusTrapExpr ctx.retTys (status := .var r.1) hst
                (Nat.le_trans hle hf0) (Nat.le_trans hlen0 hcurLe) hm'⟩)
  | (cases stk with | nil => exact htrap | cons _ r => exact hk0 locs r)
  | (cases pop32 stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨c, r⟩
      cases r with
      | nil => exact htrap
      | cons v₂ r2 =>
        cases r2 with
        | nil => exact htrap
        | cons v₁ r3 => exact emitSelect_wp htrap c v₁ v₂ _ fun y => hk0 locs (y :: r3))
  | (cases getLocal ctx.locTys locs ‹Nat› with | none => exact htrap | some v => exact hk0 locs _)
  | (cases stk with
    | nil => exact htrap
    | cons v r => dsimp only; cases setLocal ctx.locTys locs ‹Nat› v with
      | none => exact htrap | some locs' => exact hk0 locs' _)
  | (cases ctx.globals[‹Nat›]? with | none => exact htrap | some g => exact hk0 locs _)
  | (by_cases hmFlag : ctx.hasMem = true
     · simp only [hmFlag, ↓reduceIte]
       have hhm : hasMem = true := hmem.symm.trans hmFlag; subst hhm
       exact emitMemSize_wp vc hvc hm _ (hk0 locs _)
     · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap)
  | (by_cases hmFlag : ctx.hasMem = true
     · simp only [hmFlag, ↓reduceIte]
       have hhm : hasMem = true := hmem.symm.trans hmFlag; subst hhm
       cases pop32 stk with
       | none => exact htrap
       | some p =>
         rcases p with ⟨delta, s1⟩; dsimp only
         exact emitMemGrow_wp ctx.memMaxBytes vc f delta hvc hf0 hlen0 hm _
           fun f' res len' m' hf' hle hm' =>
             hk f' len' locs (.i32 res :: s1) m' hf' hle hm'
               (LabsSafe.mono hle hf' hlabs) (WasmCalleeEnvOk.mono_fuel hf' hcal)
     · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap)
  | (by_cases hmFlag : ctx.hasMem = true
     · simp only [hmFlag, ↓reduceIte]
       have hhm : hasMem = true := hmem.symm.trans hmFlag; subst hhm
       cases pop32 stk with
       | none => exact htrap
       | some p1 =>
         rcases p1 with ⟨n32, s1⟩; dsimp only
         cases pop32 s1 with
         | none => exact htrap
         | some p2 =>
           rcases p2 with ⟨v32, s2⟩; dsimp only
           cases pop32 s2 with
           | none => exact htrap
           | some p3 =>
             rcases p3 with ⟨d32, s3⟩; dsimp only
             exact emitMemFill_wp vc f d32 v32 n32 hvc hf0 hlen0 hm _ fun f' m' hf' hm' =>
               hk f' curLen locs s3 m' hf' (Nat.le_refl _) hm'
                 (LabsSafe.mono (Nat.le_refl _) hf' hlabs) (WasmCalleeEnvOk.mono_fuel hf' hcal)
     · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap)
  | (by_cases hmFlag : ctx.hasMem = true
     · simp only [hmFlag, ↓reduceIte]
       have hhm : hasMem = true := hmem.symm.trans hmFlag; subst hhm
       cases pop32 stk with
       | none => exact htrap
       | some p1 =>
         rcases p1 with ⟨n32, s1⟩; dsimp only
         cases pop32 s1 with
         | none => exact htrap
         | some p2 =>
           rcases p2 with ⟨sr32, s2⟩; dsimp only
           cases pop32 s2 with
           | none => exact htrap
           | some p3 =>
             rcases p3 with ⟨d32, s3⟩; dsimp only
             exact emitMemCopy_wp vc f d32 sr32 n32 hvc hf0 hlen0 hm _ fun f' m' hf' hm' =>
               hk f' curLen locs s3 m' hf' (Nat.le_refl _) hm'
                 (LabsSafe.mono (Nat.le_refl _) hf' hlabs) (WasmCalleeEnvOk.mono_fuel hf' hcal)
     · simp only [hmFlag, Bool.false_eq_true, ↓reduceIte]; exact htrap)
  | (cases ‹WValTy› <;> cases stk with
    | nil => exact htrap
    | cons x r =>
      cases x <;> first | exact htrap | exact emitEqz_wp _ _ _ fun y => hk0 locs (.i32 y :: r))
  | (cases popExpectS _ stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨x, _⟩; dsimp only
      exact emitUnOp_wp hf0 hlen0 hm _ _ x _ fun _ => hk0 locs _)
  | (cases popExpectS _ stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨b, s1⟩; dsimp only
      cases popExpectS _ s1 with
      | none => exact htrap
      | some p2 =>
        rcases p2 with ⟨a, _⟩; dsimp only
        exact emitBinOp_wp hf0 hlen0 hm _ _ a b _ fun _ => hk0 locs _)
  | (cases popExpectS _ stk with
    | none => exact htrap
    | some p =>
      rcases p with ⟨b, s1⟩; dsimp only
      cases popExpectS _ s1 with
      | none => exact htrap
      | some p2 =>
        rcases p2 with ⟨a, _⟩; dsimp only
        exact emitRelOp_wp _ _ a b _ fun _ => hk0 locs _)
  | (cases pop64 stk with
    | none => exact htrap
    | some p => rcases p with ⟨_, _⟩; dsimp only; wasm_wp_let; exact hk0 locs _)
  | (cases pop32 stk with
    | none => exact htrap
    | some p => rcases p with ⟨_, _⟩; dsimp only; wasm_wp_let; exact hk0 locs _)
  | (cases pop32 stk with
    | none => exact htrap
    | some p => rcases p with ⟨_, _⟩; dsimp only; wasm_wp_let; exact hk0 locs _)

private theorem lowerGroupJoin_wp {Γ : Env} {X : XPost} (ctx : WLowerCtx) (ft : WFuncTy)
    {hasMem : Bool} {vmCtx memBase memLen0 curLen memCap fuel0 : BitVec 64} {R : Mem 64 → Prop}
    {f : Arg Val T.i64} (hf0 : f.val.toNat ≤ fuel0.toNat) (hlen0 : memLen0.toNat ≤ curLen.toNat)
    (labs : List (WLabel Val Cont ctx.locTys)) (sa : List (SVal Val))
    (hlabs : LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs)
    (hcal : WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R)
    (body : WLabel Val Cont ctx.locTys → WCont Val Cont ctx.locTys ctx.retTys →
      Expr Val Cont (wasmRetSig ctx.retTys))
    (after : WCont Val Cont ctx.locTys ctx.retTys) {mem : Mem 64}
    (hafter : ∀ curLen' (f' : Arg Val T.i64) locs' stk' m',
      curLen.toNat ≤ curLen'.toNat → f'.val.toNat ≤ f.val.toNat →
      WasmMemInv hasMem vmCtx memBase curLen' memCap R m' →
      LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap f'.val R labs →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f'.val R →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (after f' locs' stk') m')
    (hbody : ∀ (lbl' : WLabel Val Cont ctx.locTys) (fall : WCont Val Cont ctx.locTys ctx.retTys),
      LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R (lbl' :: labs) →
      (∀ f' curLen' locs' stk' m', f'.val.toNat ≤ f.val.toNat → curLen.toNat ≤ curLen'.toNat →
        WasmMemInv hasMem vmCtx memBase curLen' memCap R m' →
        wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
          (fall f' locs' stk') m') →
      wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
        (body lbl' fall) mem) :
    wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
      (lowerGroupJoin ctx ft sa body after) mem := by
  simp only [lowerGroupJoin]
  rw [wp_group_]
  intro Js hcl
  rw [closed_cons_] at hcl
  have hJoin : ∀ curLen' (xs : Tup Val (labelSig ctx.locTys ft.results)) m',
      curLen.toNat ≤ curLen'.toNat → xs.1.toNat ≤ f.val.toNat →
      WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → Js.1 xs m' := by
    intro curLen' xs m' hcur hxs hm'
    exact hcl.1 xs m' (hafter curLen' (.var xs.1) _ _ m' hcur hxs hm'
      (LabsSafe.mono hcur hxs hlabs) (WasmCalleeEnvOk.mono_fuel hxs hcal))
  let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.results, Js.1⟩
  have hlabs' : LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R (lbl' :: labs) := by
    intro l hl curLen' xs m' hcur hxs hm'
    rcases List.mem_cons.mp hl with rfl | hl
    · exact hJoin curLen' xs m' hcur hxs hm'
    · exact hlabs l hl curLen' xs m' hcur hxs hm'
  refine hbody lbl' _ hlabs' fun f' curLen' locs' stk' m' hf' hcur' hm' => ?_
  cases popArgsAux ft.results stk' with
  | none =>
    exact wp_mkTrapExpr ctx.retTys 1#32 (Or.inr (Or.inl rfl))
      (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur') hm'
  | some p' =>
    rcases p' with ⟨ra, _⟩; dsimp only; rw [wp_jump_]
    exact hJoin curLen' _ m' hcur' hf' hm'

/-- Universal WP theorem for `lowerSeq`: arbitrary instruction sequences preserve host frame `R`,
respect fuel bounds, grow memory monotonically (`curLen ≤ curLen'`), and never trap outside
`{1#32, 2#32}`. -/
theorem lowerSeq_wp_aux {Γ : Env} {X : XPost} (ctx : WLowerCtx)
    {hasMem : Bool} (hmem : ctx.hasMem = hasMem) {vmCtx memBase memLen0 memCap fuel0 : BitVec 64}
    {R : Mem 64 → Prop} (vc : Arg Val T.i64) (hvc : vc.val = vmCtx) :
    ∀ (sz : Nat) (curLen : BitVec 64) (f : Arg Val T.i64),
      f.val.toNat ≤ fuel0.toNat →
      memLen0.toNat ≤ curLen.toNat →
      WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f.val R →
      ∀ (locs : Tup (Arg Val) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal Val))
        (labs : List (WLabel Val Cont ctx.locTys)),
        LabsSafe ctx.locTys hasMem vmCtx memBase curLen memCap f.val R labs →
        ∀ (instrs : List WInstr), sizeOf instrs ≤ sz →
          ∀ (k : WCont Val Cont ctx.locTys ctx.retTys),
            (∀ f' curLen' locs' stk' mem', f'.val.toNat ≤ f.val.toNat →
              curLen.toNat ≤ curLen'.toNat →
              WasmMemInv hasMem vmCtx memBase curLen' memCap R mem' →
              LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap f'.val R labs →
              WasmCalleeEnvOk Γ ctx.funcs ctx.types hasMem vmCtx memBase memCap f'.val R →
              wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
                (k f' locs' stk') mem') →
            ∀ {mem : Mem 64}, WasmMemInv hasMem vmCtx memBase curLen memCap R mem →
              wp Γ (WasmPost hasMem vmCtx memBase memLen0 memCap fuel0 ctx.retTys R) X
                (lowerSeq ctx vc f locs stk labs instrs k) mem := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro curLen f hf0 hlen0 hcal locs stk labs hlabs instrs hsz k hk mem hm
    have htrap := wp_mkTrapExpr (Γ := Γ) (X := X) (vmCtx := vmCtx) (memBase := memBase)
      (memLen0 := memLen0) (memCap := memCap) (fuel0 := fuel0) ctx.retTys 1#32
      (Or.inr (Or.inl rfl)) hf0 hlen0 hm
    cases instrs with
    | nil =>
      simp only [lowerSeq]
      exact hk f curLen locs stk mem (Nat.le_refl _) (Nat.le_refl _) hm hlabs hcal
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
            rcases p with ⟨ba, _⟩; dsimp only; rw [wp_jump_]
            exact hlabs lbl hlblMem curLen _ mem (Nat.le_refl _) (Nat.le_refl _) hm
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
              rcases p' with ⟨ba, _⟩; dsimp only
              exact emitBrTable_wp labs hlabs locs f hf0 (Nat.le_refl _) idx32 defLbl hdefMem ba
                hlen0 hm 0 targets
      | return_ =>
        simp only [lowerSeq]
        cases popArgsAux ctx.retTys stk with
        | none => exact htrap
        | some p =>
          rcases p with ⟨ra, _⟩; dsimp only; rw [wp_ret_]
          exact ⟨Or.inl rfl, hf0, curLen, hlen0, hm⟩
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨ia, sa⟩; dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            refine lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _
              (fun curLen' f' l' s' m' hcur hf' hm' hl' hc' =>
                ih _ hszRest' curLen' f' (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur) hc'
                  l' s' labs hl' rest (Nat.le_refl _) k
                  (fun f'' curLen'' l'' s'' m'' hf'' hcur'' hm'' hl'' hc'' =>
                    hk f'' curLen'' l'' s'' m'' (Nat.le_trans hf'' hf')
                      (Nat.le_trans hcur hcur'') hm'' hl'' hc'') hm')
              (fun lbl' fall hlabs' hfall =>
                ih _ hszBody curLen f hf0 hlen0 hcal locs _ (lbl' :: labs) hlabs' body
                  (Nat.le_refl _) fall
                  (fun f' curLen' locs' stk' m' hf' hcur' hm' _ _ =>
                    hfall f' curLen' locs' stk' m' hf' hcur' hm') hm)
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨ia, sa⟩; dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            refine lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _
              (fun curLen' f' l' s' m' hcur hf' hm' hl' hc' =>
                ih _ hszRest' curLen' f' (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur) hc'
                  l' s' labs hl' rest (Nat.le_refl _) k
                  (fun f'' curLen'' l'' s'' m'' hf'' hcur'' hm'' hl'' hc'' =>
                    hk f'' curLen'' l'' s'' m'' (Nat.le_trans hf'' hf')
                      (Nat.le_trans hcur hcur'') hm'' hl'' hc'') hm')
              (fun _ fall hlabsAfter hfall => ?_)
            rw [wp_group_]
            intro JsHdr hclHdr
            rw [closed_cons_] at hclHdr
            have hHdr : ∀ (n : Nat) curLen' (xs : Tup Val (labelSig ctx.locTys ft.params)) m',
                curLen.toNat ≤ curLen'.toNat → xs.1.toNat = n → n ≤ f.val.toNat →
                WasmMemInv hasMem vmCtx memBase curLen' memCap R m' → JsHdr.1 xs m' := by
              intro n
              induction n using Nat.strongRecOn with
              | _ n ihn =>
                intro curLen' xs m' hcur' hxn hnf hm'
                apply hclHdr.1 xs m'
                wasm_wp_let; rw [wp_jnz_]
                refine ⟨fun _ => wp_mkTrapExpr ctx.retTys 2#32 (Or.inr (Or.inr rfl))
                  (Nat.le_trans (hxn.symm ▸ hnf) hf0) (Nat.le_trans hlen0 hcur') hm', fun hz => ?_⟩
                have hlt : (xs.1 - 1#64).toNat < xs.1.toNat :=
                  bv64_sub_one_lt (decide_eq_false_iff_not.mp hz)
                have hnextLe : (xs.1 - 1#64).toNat ≤ f.val.toNat := by omega
                wasm_wp_let
                let fNext : Arg Val T.i64 := .var (xs.1 - 1#64)
                let lbl' : WLabel Val Cont ctx.locTys := ⟨ft.params, JsHdr.1⟩
                have hlabs' : LabsSafe ctx.locTys hasMem vmCtx memBase curLen' memCap fNext.val R
                    (lbl' :: labs) := by
                  intro l hl curLen'' ys m'' hcur'' hys hm''
                  rcases List.mem_cons.mp hl with rfl | hl
                  · have hlt' : ys.1.toNat < n := Nat.lt_of_le_of_lt hys (hxn ▸ hlt)
                    exact ihn ys.1.toNat hlt' curLen'' ys m'' (Nat.le_trans hcur' hcur'') rfl
                      (Nat.le_trans (Nat.le_of_lt hlt') hnf) hm''
                  · exact hlabs l hl curLen'' ys m'' (Nat.le_trans hcur' hcur'')
                      (Nat.le_trans hys hnextLe) hm''
                exact ih _ hszBody curLen' fNext (Nat.le_trans hnextLe hf0)
                  (Nat.le_trans hlen0 hcur') (WasmCalleeEnvOk.mono_fuel hnextLe hcal) _ _
                  (lbl' :: labs) hlabs' body (Nat.le_refl _) fall
                  (fun f' curLen'' locs' stk' m'' hf' hcur'' hm'' _ _ =>
                    hfall f' curLen'' locs' stk' m'' (Nat.le_trans hf' hnextLe)
                      (Nat.le_trans hcur' hcur'') hm'') hm'
            rw [wp_jump_]
            exact hHdr f.val.toNat curLen (vals (f, tupAppend locs ia)) mem
              (Nat.le_refl _) rfl (Nat.le_refl _) hm
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap
        | some ft =>
          dsimp only
          cases pop32 stk with
          | none => exact htrap
          | some p =>
            rcases p with ⟨cond, stk1⟩; dsimp only
            cases popArgsAux ft.params stk1 with
            | none => exact htrap
            | some p' =>
              rcases p' with ⟨ia, sa⟩; dsimp only
              have hszT : sizeOf thenBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              refine lowerGroupJoin_wp ctx ft hf0 hlen0 labs sa hlabs hcal _ _
                (fun curLen' f' l' s' m' hcur hf' hm' hl' hc' =>
                  ih _ hszRest' curLen' f' (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur) hc'
                    l' s' labs hl' rest (Nat.le_refl _) k
                    (fun f'' curLen'' l'' s'' m'' hf'' hcur'' hm'' hl'' hc'' =>
                      hk f'' curLen'' l'' s'' m'' (Nat.le_trans hf'' hf')
                        (Nat.le_trans hcur hcur'') hm'' hl'' hc'') hm')
                (fun lbl' fall hlabs' hfall => by
                  wasm_wp_let; rw [wp_jnz_]
                  refine ⟨
                    fun _ => ih _ hszT curLen f hf0 hlen0 hcal locs _ (lbl' :: labs) hlabs'
                      thenBody (Nat.le_refl _) fall (fun f' curLen' locs' stk' m' hf' hcur' hm'
                        _ _ => hfall f' curLen' locs' stk' m' hf' hcur' hm') hm,
                    fun _ => ih _ hszE curLen f hf0 hlen0 hcal locs _ (lbl' :: labs) hlabs'
                      elseBody (Nat.le_refl _) fall (fun f' curLen' locs' stk' m' hf' hcur' hm'
                        _ _ => hfall f' curLen' locs' stk' m' hf' hcur' hm') hm⟩)
      | _ =>
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        exact lowerSimpleInstr_wp ctx hmem vc f hvc hf0 hlen0 hcal locs stk labs hlabs _ _
          (fun f' curLen' locs' stk' m' hf' hcur' hm' hl' hc' =>
            ih _ hszRest' curLen' f' (Nat.le_trans hf' hf0) (Nat.le_trans hlen0 hcur') hc'
              locs' stk' labs hl' rest (Nat.le_refl _) k
              (fun f'' curLen'' l'' s'' m'' hf'' hcur'' hm'' hl'' hc'' =>
                hk f'' curLen'' l'' s'' m'' (Nat.le_trans hf'' hf') (Nat.le_trans hcur' hcur'')
                  hm'' hl'' hc'')
              hm')
          hm

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
  simp only [Func.wp, lowerFuncBody]
  rw [wp_group_]
  intro Js hcl
  rw [closed_cons_] at hcl
  have hRet : ∀ curLen' rxs m', memLen.toNat ≤ curLen'.toNat → rxs.1.toNat ≤ xs.2.1.toNat →
      WasmMemInv m.memory.isSome xs.1 memBase curLen' memCap R m' → Js.1 rxs m' := by
    intro curLen' rxs m' hlen' hr hm'
    apply hcl.1 rxs m'
    rw [wp_ret_]
    exact ⟨Or.inl rfl, hr, curLen', hlen', hm'⟩
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  let retLbl : WLabel Val Cont ctx.locTys := ⟨ft.results, Js.1⟩
  have hlabs : LabsSafe ctx.locTys m.memory.isSome xs.1 memBase memLen memCap xs.2.1 R
      [retLbl] := by
    intro l hl curLen' rxs m' hlen' hr hm'
    rcases List.mem_singleton.mp hl with rfl
    exact hRet curLen' rxs m' hlen' hr hm'
  refine lowerSeq_wp_aux ctx rfl (.var xs.1) rfl (sizeOf f.body) memLen (.var xs.2.1)
    (Nat.le_refl _) (Nat.le_refl _) hcal _ [] [retLbl] hlabs f.body (Nat.le_refl _) _
    (fun f' curLen' _ stk' m' hf' hcur' hm' _ _ => ?_) hm
  cases popArgsAux ft.results stk' with
  | none => exact wp_mkTrapExpr ft.results 1#32 (Or.inr (Or.inl rfl)) hf' hcur' hm'
  | some p =>
    rcases p with ⟨ra, _⟩
    dsimp only
    rw [wp_ret_]
    exact ⟨Or.inl rfl, hf', curLen', hcur', hm'⟩

/-- `callsOk` preservation for lowered Wasm instruction helpers and sequences. -/
private theorem emitPopcntCore_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (n : Nat) (m1 m2 m4 mul sh : BitVec n) (x : Arg (fun _ => Unit) (.bits n))
    (k : Arg (fun _ => Unit) (.bits n) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitPopcntCore n m1 m2 m4 mul sh x k).callsOk allowed exits := by
  simp only [emitPopcntCore, Expr.callsOk]; exact hk _

private theorem emitUnOp_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (f : Arg (fun _ => Unit) T.i64) (w : WValTy) (op : WUnOp)
    (x : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) w.toTy → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitUnOp retTys f w op x k).callsOk allowed exits := by
  cases w <;> cases op <;> simp only [emitUnOp, emitPopcnt, Expr.callsOk] <;>
  first | exact hk _ | exact emitPopcntCore_callsOk allowed exits _ _ _ _ _ _ x k hk | trivial

private theorem emitBinOp_callsOk (allowed : List SigEntry) (exits : List Sym)
    (retTys : List WValTy) (f : Arg (fun _ => Unit) T.i64) (w : WValTy) (op : WBinOp)
    (a b : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) w.toTy → Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig retTys))
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitBinOp retTys f w op a b k).callsOk allowed exits := by
  cases op <;> cases w <;> simp only [emitBinOp, emitDivRemCore, Expr.callsOk] <;>
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

private theorem emitSelect_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    {trap : Expr (fun _ => Unit) (fun _ => Unit) rs} (htrap : trap.callsOk allowed exits)
    (c : Arg (fun _ => Unit) T.i32) (v1 v2 : SVal (fun _ => Unit))
    (k : SVal (fun _ => Unit) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitSelect trap c v1 v2 k).callsOk allowed exits := by
  cases v1 <;> cases v2 <;> simp only [emitSelect, Expr.callsOk] <;>
  first | exact htrap | exact hk _

private theorem emitEqz_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (w : WValTy) (x : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) T.i32 → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitEqz w x k).callsOk allowed exits := by
  cases w <;> simp only [Expr.callsOk] <;> exact hk _

private theorem emitRelOp_callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (w : WValTy) (op : WRelOp) (a b : Arg (fun _ => Unit) w.toTy)
    (k : Arg (fun _ => Unit) T.i32 → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ y, (k y).callsOk allowed exits) :
    (emitRelOp w op a b k).callsOk allowed exits := by
  cases w <;> simp only [Expr.callsOk] <;> exact hk _

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
      · simp only [hlt, ↓reduceDIte, Expr.callsOk]; exact ⟨trivial, ih (i + 1)⟩
      · simp only [hlt, ↓reduceDIte]; exact trivial

private theorem lowerSimpleInstr_callsOk (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym)
    (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed)
    (vc f : Arg (fun _ => Unit) T.i64)
    (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal (fun _ => Unit)))
    (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys))
    (instr : WInstr) (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys)
    (hk : ∀ f' l' s', (k f' l' s').callsOk allowed exits) :
    (lowerSimpleInstr ctx vc f locs stk labs instr k).callsOk allowed exits := by
  cases instr with
  | load resTy width signed _ =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]; cases pop32 stk with
      | none => exact trivial
      | some p =>
        rcases p with ⟨idx32, s1⟩; dsimp only
        exact emitMemBounds_callsOk allowed exits ctx.retTys vc f idx32 _ _ _ fun _ => by
          simp only [Expr.callsOk]
          exact emitLoadCast_callsOk allowed exits (by simp [Expr.callsOk]) _ _ _ () _
            fun v => hk f locs (SVal.ofArg _ v :: s1)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | store srcTy width _ =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]; cases popExpectS _ stk with
      | none => exact trivial
      | some p =>
        rcases p with ⟨sv, s1⟩; dsimp only
        cases pop32 s1 with
        | none => exact trivial
        | some p2 =>
          rcases p2 with ⟨idx32, s2⟩; dsimp only
          exact emitMemBounds_callsOk allowed exits ctx.retTys vc f idx32 _ _ _ fun _ =>
            emitStoreCast_callsOk allowed exits (by simp [Expr.callsOk]) _ _ sv _ fun _ => by
              simp only [Expr.callsOk]; exact hk f locs s2
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact trivial
  | _ =>
  simp only [lowerSimpleInstr] <;>
  first
  | exact trivial
  | exact hk f locs _
  | (cases pop32 stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨c, r⟩
      cases labs[‹Nat›]? with
      | none => exact trivial
      | some l => dsimp only; cases popArgsAux l.argTys r with
        | none => exact trivial
        | some p' => rcases p' with ⟨_, _⟩; simp only [Expr.callsOk]; exact ⟨trivial, hk f locs r⟩)
  | (cases hc : ctx.funcs[‹Nat›]? with
    | none => exact trivial
    | some callee => dsimp only; cases hft : ctx.types[callee.typeIdx]? with
      | none => exact trivial
      | some ft => dsimp only; cases popArgsAux ft.params stk with
        | none => exact trivial
        | some p => rcases p with ⟨_, _⟩; simp only [Expr.callsOk]
                    exact ⟨trivial, hcal _ callee ft hc hft, hk _ locs _, trivial⟩)
  | (cases stk with | nil => exact trivial | cons _ r => exact hk f locs r)
  | (cases pop32 stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨c, r⟩
      cases r with
      | nil => exact trivial
      | cons v₂ r2 =>
        cases r2 with
        | nil => exact trivial
        | cons v₁ r3 =>
          exact emitSelect_callsOk allowed exits (by simp [Expr.callsOk]) c v₁ v₂ _
            fun y => hk f locs (y :: r3))
  | (cases getLocal ctx.locTys locs ‹Nat› with
    | none => exact trivial
    | some v => exact hk f locs _)
  | (cases stk with
    | nil => exact trivial
    | cons v r => dsimp only; cases setLocal ctx.locTys locs ‹Nat› v with
      | none => exact trivial | some l' => exact hk f l' _)
  | (cases ctx.globals[‹Nat›]? with | none => exact trivial | some g => exact hk f locs _)
  | (by_cases hm : ctx.hasMem = true
     · simp only [hm, ↓reduceIte]; exact emitMemSize_callsOk allowed exits vc _ fun _ => hk f locs _
     · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial)
  | (by_cases hm : ctx.hasMem = true
     · simp only [hm, ↓reduceIte]; cases pop32 stk with
       | none => exact trivial
       | some p =>
         rcases p with ⟨delta, s1⟩; dsimp only
         exact emitMemGrow_callsOk allowed exits ctx.retTys ctx.memMaxBytes vc f delta _
           fun f' r => hk f' locs (.i32 r :: s1)
     · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial)
  | (by_cases hm : ctx.hasMem = true
     · simp only [hm, ↓reduceIte]; cases pop32 stk with
       | none => exact trivial
       | some p1 =>
         rcases p1 with ⟨n32, s1⟩; dsimp only; cases pop32 s1 with
         | none => exact trivial
         | some p2 =>
           rcases p2 with ⟨v32, s2⟩; dsimp only; cases pop32 s2 with
           | none => exact trivial
           | some p3 =>
             rcases p3 with ⟨d32, s3⟩; dsimp only
             exact emitMemFill_callsOk allowed exits ctx.retTys vc f d32 v32 n32 _
               fun f' => hk f' locs s3
     · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial)
  | (by_cases hm : ctx.hasMem = true
     · simp only [hm, ↓reduceIte]; cases pop32 stk with
       | none => exact trivial
       | some p1 =>
         rcases p1 with ⟨n32, s1⟩; dsimp only; cases pop32 s1 with
         | none => exact trivial
         | some p2 =>
           rcases p2 with ⟨sr32, s2⟩; dsimp only; cases pop32 s2 with
           | none => exact trivial
           | some p3 =>
             rcases p3 with ⟨d32, s3⟩; dsimp only
             exact emitMemCopy_callsOk allowed exits ctx.retTys vc f d32 sr32 n32 _
               fun f' => hk f' locs s3
     · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact trivial)
  | (cases ‹WValTy› <;> cases stk with
    | nil => exact trivial
    | cons x t =>
      cases x <;> first
        | exact trivial
        | exact emitEqz_callsOk allowed exits _ _ _ fun r => hk f locs (.i32 r :: t))
  | (cases popExpectS _ stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨x, _⟩; dsimp only
      exact emitUnOp_callsOk allowed exits ctx.retTys f _ _ x _ fun _ => hk f locs _)
  | (cases popExpectS _ stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨b, s1⟩; dsimp only; cases popExpectS _ s1 with
      | none => exact trivial
      | some p2 =>
        rcases p2 with ⟨a, _⟩; dsimp only
        exact emitBinOp_callsOk allowed exits ctx.retTys f _ _ a b _ fun _ => hk f locs _)
  | (cases popExpectS _ stk with
    | none => exact trivial
    | some p =>
      rcases p with ⟨b, s1⟩; dsimp only; cases popExpectS _ s1 with
      | none => exact trivial
      | some p2 =>
        rcases p2 with ⟨a, _⟩; dsimp only
        exact emitRelOp_callsOk allowed exits _ _ a b _ fun _ => hk f locs _)
  | (cases pop64 stk with
    | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _)
  | (cases pop32 stk with
    | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _)
  | (cases pop32 stk with
    | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact hk f locs _)

private theorem lowerGroupJoin_callsOk (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym) (ft : WFuncTy) (sa : List (SVal (fun _ => Unit)))
    (body : WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys →
      WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys →
      Expr (fun _ => Unit) (fun _ => Unit) (wasmRetSig ctx.retTys))
    (after : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys)
    (hbody : ∀ lbl fall, (∀ f' l' s', (fall f' l' s').callsOk allowed exits) →
      (body lbl fall).callsOk allowed exits)
    (hafter : ∀ f' l' s', (after f' l' s').callsOk allowed exits) :
    (lowerGroupJoin ctx ft sa body after).callsOk allowed exits := by
  simp only [Expr.callsOk, Blocks.callsOk]
  refine ⟨⟨hafter _ _ _, trivial⟩, hbody _ _ fun _ _ s' => ?_⟩
  cases popArgsAux ft.results s' with
  | none => simp [Expr.callsOk]
  | some p' => rcases p' with ⟨_, _⟩; exact trivial

private theorem lowerSeq_callsOk_aux (ctx : WLowerCtx) (allowed : List SigEntry)
    (exits : List Sym)
    (hcal : ∀ (fnIdx : Nat) (callee : WFunc) (ft : WFuncTy),
      ctx.funcs[fnIdx]? = some callee → ctx.types[callee.typeIdx]? = some ft →
      (callee.name, wasmAbiParams ft, wasmAbiResults ft) ∈ allowed) :
    ∀ (sz : Nat) (vc f : Arg (fun _ => Unit) T.i64)
      (locs : Tup (Arg (fun _ => Unit)) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal (fun _ => Unit)))
      (labs : List (WLabel (fun _ => Unit) (fun _ => Unit) ctx.locTys))
      (instrs : List WInstr) (_hsz : sizeOf instrs ≤ sz)
      (k : WCont (fun _ => Unit) (fun _ => Unit) ctx.locTys ctx.retTys),
      (∀ f' l' s', (k f' l' s').callsOk allowed exits) →
      (lowerSeq ctx vc f locs stk labs instrs k).callsOk allowed exits := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro vc f locs stk labs instrs hsz k hk
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
        | some lbl => dsimp only; cases popArgsAux lbl.argTys stk with
          | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact trivial
      | br_table targets defTarget =>
        simp only [lowerSeq]
        cases pop32 stk with
        | none => exact trivial
        | some p => rcases p with ⟨idx32, s1⟩; cases labs[defTarget]? with
          | none => exact trivial
          | some defLbl => dsimp only; cases popArgsAux defLbl.argTys s1 with
            | none => exact trivial
            | some p' => rcases p' with ⟨ba, _⟩; dsimp only
                         exact emitBrTable_callsOk allowed exits ctx.locTys ctx.retTys labs locs
                           f idx32 defLbl ba 0 targets
      | return_ =>
        simp only [lowerSeq]; cases popArgsAux ctx.retTys stk with
        | none => exact trivial | some p => rcases p with ⟨_, _⟩; exact trivial
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft => dsimp only; cases popArgsAux ft.params stk with
          | none => exact trivial
          | some p => rcases p with ⟨_, sa⟩; dsimp only
                      have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
                      have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
                      exact lowerGroupJoin_callsOk ctx allowed exits ft sa _ _
                        (fun _ fall hfall =>
                          ih _ hszBody vc f locs _ _ body (Nat.le_refl _) fall hfall)
                        (fun _ _ _ => ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk)
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft => dsimp only; cases popArgsAux ft.params stk with
          | none => exact trivial
          | some p => rcases p with ⟨_, sa⟩; dsimp only
                      have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
                      have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
                      refine lowerGroupJoin_callsOk ctx allowed exits ft sa _ _
                        (fun _ fall hfall => ?_)
                        (fun _ _ _ => ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk)
                      simp only [Expr.callsOk, Blocks.callsOk]
                      exact ⟨⟨⟨trivial,
                        ih _ hszBody vc _ _ _ _ body (Nat.le_refl _) fall hfall⟩, trivial⟩, trivial⟩
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact trivial
        | some ft => dsimp only; cases pop32 stk with
          | none => exact trivial
          | some p => rcases p with ⟨_, s1⟩; dsimp only; cases popArgsAux ft.params s1 with
            | none => exact trivial
            | some p' =>
              rcases p' with ⟨_, sa⟩; dsimp only
              have hszT : sizeOf thenBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              refine lowerGroupJoin_callsOk ctx allowed exits ft sa _ _
                (fun _ fall hfall => ?_)
                (fun _ _ _ => ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk)
              simp only [Expr.callsOk]
              exact ⟨ih _ hszT vc f locs _ _ thenBody (Nat.le_refl _) fall hfall,
                     ih _ hszE vc f locs _ _ elseBody (Nat.le_refl _) fall hfall⟩
      | _ =>
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        exact lowerSimpleInstr_callsOk ctx allowed exits hcal vc f locs stk labs _ _
          fun f' l' s' => ih _ hszRest' vc f' l' s' labs rest (Nat.le_refl _) k hk

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
    (sizeOf f.body) _ _ _ [] _ f.body (Nat.le_refl _) _ fun _ _ s' => ?_
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
    {vmCtx memBase curLen memCap f' : BitVec 64}
    {args : Tup Val (ft.params.map WValTy.toTy)}
    {mem' : Mem 64} {R : Mem 64 → Prop}
    (hm' : WasmMemInv m.memory.isSome vmCtx memBase curLen memCap R mem') :
    WasmSandboxEnv m f'.toNat callee.name (wasmAbiParams ft) (wasmAbiResults ft)
      (vmCtx, f', args) mem'
      (WasmPost m.memory.isSome vmCtx memBase curLen memCap f' ft.results R)
      (fun _ _ _ _ => False) := by
  have hftEq : ft = (m.types[callee.typeIdx]?).getD {} := by simp [hft]
  subst hftEq
  exact ⟨callee, hmem, rfl, rfl, rfl, Nat.le_refl _, memBase, curLen, memCap, R, hm',
    fun _ _ h => h⟩

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
  rcases hspec with ⟨f', hf', ha, hb, heq, hfuel, memBase, curLen, memCap, R, hm, hpost⟩
  have heqf : f = f' := func_eq_of_namesNodup hfnd hf hf' heq
  subst heqf
  have hba : ha = rfl := Subsingleton.elim _ _
  have hbb : hb = rfl := Subsingleton.elim _ _
  subst hba; subst hbb
  dsimp only at hfuel hm hpost
  have hstep : WasmCalleeEnvOk
      (Env.stepIdx natRecIdx ((lowerModule m).fns.map Fn.sig)
        ((lowerModule m).externs.map Extern.sig) (WasmSandboxEnv m) Γext false i)
      m.funcs m.types m.memory.isSome xs.1 memBase memCap xs.2.1 R := by
    intro fnIdx callee ft hc hft _ f' args m' hlt hm'
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
  rcases hi with ⟨f', hf', ha, hb, heq, hfuel, memBase, curLen, memCap, R, hm, hpost⟩
  have heqf : f = f' := func_eq_of_namesNodup hfnd hf hf' heq
  subst heqf
  have hba : ha = rfl := Subsingleton.elim _ _
  have hbb : hb = rfl := Subsingleton.elim _ _
  subst hba; subst hbb
  dsimp only at hfuel hm hpost
  have hcal : WasmCalleeEnvOk (WasmSandboxEnvAny m) m.funcs m.types m.memory.isSome
      xs.1 memBase memCap xs.2.1 R := by
    intro fnIdx callee ft hc hft _ f' args m' _ hm'
    exact ⟨f'.toNat, wasmSandboxEnv_callee m callee (List.mem_of_getElem? hc) ft hft hm'⟩
  have hwp := lowerFuncBody_wp m f _ hm hcal (X := X)
  exact wp_mono hpost (fun _ _ _ _ h => h) _ mem hwp

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
      (wasmAbiResults ((m.types[f.typeIdx]?).getD {}))
      (vmCtx, fuel, args) mem Q X := by
  have hfn : lowerFn m f ∈ (lowerModule m).fns :=
    List.mem_map.mpr ⟨f, hf, rfl⟩
  have hsig : (f.name, wasmAbiParams ((m.types[f.typeIdx]?).getD {}),
      wasmAbiResults ((m.types[f.typeIdx]?).getD {})) ∈ (lowerModule m).fns.map Fn.sig :=
    List.mem_map.mpr ⟨lowerFn m f, hfn, rfl⟩
  refine lowerModule_semScc hv Γext fuel.toNat _ _ _ _ _ _ _ ⟨hsig, ?_⟩
  exact ⟨f, hf, rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap, R, hmem, hpost⟩

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
@[expose] def wasmAcyclic (m : WModule) : Bool :=
  wasmAcyclicAux 0 m.funcs

private theorem lowerSimpleInstr_take_eq {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs)
    (vc f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instr : WInstr)
    (hb : wasmInstrCallsBelow bound instr = true)
    (k : WCont V L ctx.locTys ctx.retTys) :
    lowerSimpleInstr { ctx with funcs := fs.take bound } vc f locs stk labs instr k =
      lowerSimpleInstr ctx vc f locs stk labs instr k := by
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
  exact congr
    (congrArg Expr.group (funext fun _ => congrArg (fun b => Blocks.cons b Blocks.nil)
      (funext fun _ => hafter _ _ _)))
    (funext fun _ => hbody _ _)

private theorem lowerSeq_take_eq_aux {V : Ty → Type} {L : List Ty → Type}
    (ctx : WLowerCtx) (fs : List WFunc) (bound : Nat) (hfs : ctx.funcs = fs)
    (sz : Nat) :
    ∀ (vc f : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instrs : List WInstr),
      sizeOf instrs ≤ sz → wasmSeqCallsBelow bound instrs = true →
      ∀ (k₁ k₂ : WCont V L ctx.locTys ctx.retTys),
        (∀ f' l' s', k₁ f' l' s' = k₂ f' l' s') →
        lowerSeq { ctx with funcs := fs.take bound } vc f locs stk labs instrs k₁ =
          lowerSeq ctx vc f locs stk labs instrs k₂ := by
  induction sz with
  | zero =>
    intro vc f locs stk labs instrs hsz _ k₁ k₂ hk
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk
    | cons _ _ => simp +arith at hsz
  | succ sz ih =>
    intro vc f locs stk labs instrs hsz hb k₁ k₂ hk
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
        have hszBody' : sizeOf body ≤ sz :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by simp +arith) hsz)
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => rfl
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => rfl
          | some _ =>
            exact lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
              (fun _ _ => ih _ _ _ _ _ body hszBody' hi _ _ (fun _ _ _ => rfl))
              (fun _ _ _ => ih _ _ _ _ _ rest hszRest' hrest _ _ hk)
      | loop bt body =>
        simp only [wasmInstrCallsBelow] at hi
        have hszBody' : sizeOf body ≤ sz :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by simp +arith) hsz)
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => rfl
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => rfl
          | some _ =>
            refine lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
              (fun _ fall => congrArg (fun b => Expr.group b _) (funext fun _ =>
                congrArg (fun b => Blocks.cons b Blocks.nil) (funext fun _ =>
                  congrArg (Expr.let_ _) (funext fun _ => congrArg (Expr.jnz _ _)
                    (congrArg (Expr.let_ _) (funext fun _ =>
                      ih _ _ _ _ _ body hszBody' hi _ _ (fun _ _ _ => rfl)))))))
              (fun _ _ _ => ih _ _ _ _ _ rest hszRest' hrest _ _ hk)
      | if_ bt thenBody elseBody =>
        simp only [wasmInstrCallsBelow, Bool.and_eq_true] at hi
        rcases hi with ⟨hT, hE⟩
        have hszT' : sizeOf thenBody ≤ sz :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by simp +arith) hsz)
        have hszE' : sizeOf elseBody ≤ sz :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by simp +arith) hsz)
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => rfl
        | some ft =>
          dsimp only
          cases pop32 stk with
          | none => rfl
          | some _ =>
            dsimp only
            cases popArgsAux ft.params _ with
            | none => rfl
            | some _ =>
              refine lowerGroupJoin_take_eq ctx (fs.take bound) ft _ _ _ _ _
                (fun _ _ => congrArg (Expr.let_ _) (funext fun _ =>
                  congr (congrArg (Expr.jnz _)
                    (ih _ _ _ _ _ thenBody hszT' hT _ _ (fun _ _ _ => rfl)))
                    (ih _ _ _ _ _ elseBody hszE' hE _ _ (fun _ _ _ => rfl))))
                (fun _ _ _ => ih _ _ _ _ _ rest hszRest' hrest _ _ hk)
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
        | (rw [lowerSimpleInstr_take_eq ctx fs bound hfs vc f locs stk labs _ hi]
           exact congrArg (lowerSimpleInstr ctx vc f locs stk labs _)
             (funext fun _ => funext fun _ => funext fun _ =>
               ih _ _ _ _ _ rest hszRest' hrest k₁ k₂ hk))

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
        memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
        globals := m.globals,
        locTys := ((m.types[f.typeIdx]?).getD {}).params ++ f.locals,
        retTys := ((m.types[f.typeIdx]?).getD {}).results }
    exact lowerSeq_take_eq_aux ctx m.funcs bound rfl (sizeOf f.body)
      _ _ _ [] _ f.body (Nat.le_refl _) hb _ _ (fun _ _ _ => rfl)
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
