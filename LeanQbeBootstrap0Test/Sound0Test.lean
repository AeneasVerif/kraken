module

public import LeanQbe.T.Bootstrap0.Sound0
public import LeanQbe.T.Bootstrap0.Dummies0
public import LeanQbe.T.Amd64.ScalarTarg
public import Kraken.X64.PrintATT
import LeanQbe.T.FlatLemmas
meta import Lean
meta import LeanQbe.T.Bootstrap0.Sound0

/-!
# Verification Suite for Stage B Semantic Soundness (`Sound0Test`)

End-to-end machine-checked validation of `LeanQbe.T.Bootstrap0.Sound0`:
1. Arm64 zero-cross-import check (confirming zero `LeanQbe.T.Arm64` / `Kraken.AArch64` imports).
2. `dummyAddMod0` (`add2(a, b) = a + b`): soundness, `PrintAsm0` parity, and closed execution.
3. `dummyLoopMod0` (`sumto(n)`): `wp0` loop invariant, soundness, and `sumto 5#64 = 15#64`.
4. Bridged `Frontend.C0.TFlatFn` multi-function module (`c0_add_one` / `c0_add_two`):
   `ofTFlatModule`, `ModuleOk`, `bridge_leanqbe0Compile_layout`, and `c0_add_two 40#64 = 42#64`.
5. Negative kernel witnesses for Bugs A/B/C and strict `#print axioms` audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeBootstrap0Test.Sound0Test

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0

#eval show Lean.CoreM Unit from do
  let arm := (← Lean.getEnv).allImportedModuleNames.filter fun n =>
    n.toString.startsWith "LeanQbe.T.Arm64" || n.toString.startsWith "Kraken.AArch64"
  if !arm.isEmpty then throwError "forbidden Arm64/AArch64 imports: {arm.toList}"

private def dirsOf (r : CompileRes0) : List Dir0 := match r with | .ok d _ => d | .err _ _ => []
private def maxSlOf (r : CompileRes0) : UInt32 := match r with | .ok _ m => m | .err _ _ => 0

private theorem wp0_let1_op {Γ symName curRs vs ls Q X} {op : OpCode0} {args : List Arg0}
    {argv : Tup Val (ty0ListToTy (op0ArgTys op))} {k m}
    (hev : evalArgs0Ty vs (ty0ListToTy (op0ArgTys op)) args = some argv)
    (h : OpCode.wp (op0ToOpCode op) argv fun rvs =>
      wp0 Γ symName curRs (pushTup rvs vs) ls Q X k m) :
    wp0 Γ symName curRs vs ls Q X (.let1 op args k) m := by
  rw [wp0_let1, hev]; exact h

private theorem wp0_jnz_bool {Γ symName curRs vs ls Q X} {c : Arg0} {t e : TFlat0}
    {b : Bool} {m : Mem 64} (hev : evalArg0Ty vs .bool c = some b)
    (ht : b = true → wp0 Γ symName curRs vs ls Q X t m)
    (he : b = false → wp0 Γ symName curRs vs ls Q X e m) :
    wp0 Γ symName curRs vs ls Q X (.jnz c t e) m := by
  rw [wp0_jnz, hev]; exact ⟨ht, he⟩

private theorem wp0_ret64 {Γ symName vs ls Q X} {args : List Arg0} {v : BitVec 64} {m : Mem 64}
    (hev : evalArgs0Ty vs (ty0ListToTy [.b64]) args =
      (some (v, ()) : Option (Tup Val (ty0ListToTy [.b64]))))
    (hq : Q (v, ()) m) : wp0 Γ symName [.b64] vs ls Q X (.ret args) m := by
  rw [wp0_ret, hev]; exact hq

private theorem wp0_jump0_two64 {Γ symName curRs vs Q X}
    {J : Cont (ty0ListToTy [.b64, .b64])} {args : List Arg0} {a b : BitVec 64} {m : Mem 64}
    (hev : evalArgs0Ty vs (ty0ListToTy [.b64, .b64]) args =
      (some (a, b, ()) : Option (Tup Val (ty0ListToTy [.b64, .b64]))))
    (hj : J (a, b, ()) m) :
    wp0 Γ symName curRs vs [⟨ty0ListToTy [.b64, .b64], J⟩] Q X (.jump 0 args) m := by
  rw [wp0_jump]
  have hget : listGet? [(⟨ty0ListToTy [.b64, .b64], J⟩ : (ts : List Ty) × Cont ts)]
      (UInt32.toNat 0) = some ⟨ty0ListToTy [.b64, .b64], J⟩ := rfl
  rw [hget]; dsimp only; rw [hev]; exact hj

private theorem singleFn_host_ok {fn : TFlatFn0} {symName : Sym0 → Sym} {Γ : Env}
    {dirs : List Dir0} {ms : UInt32} {bounds : List (Sym0 × Nat)}
    (hc : leanqbe0Compile { fns := [fn], externs := [], exits := [] } = .ok dirs ms)
    (hg : ({ fns := [fn], externs := [], exits := [] } : TFlatModule0).okGuardsFull = true)
    (hacyc : ({ fns := [fn], externs := [], exits := [] } : TFlatModule0).checkAcyclic0 = true)
    (hb : ({ fns := [fn], externs := [], exits := [] } : TFlatModule0).computeBounds0 [] 0 =
      some bounds)
    (hnoloc : symNoLocPrefix0 (symName fn.name) = true)
    (hsmall : x64ScalarProgSmall (toAmd64Program symName dirs ++ []) = true)
    (hwp : ∀ g ∈ [fn], ∀ (args : Tup Val (ty0ListToTy g.as)) m Q X,
      Γ (symName g.name) (ty0ListToTy g.as) (ty0ListToTy g.rs) args m Q X →
      wp0 Γ symName g.rs (pushTup args []) [] Q X g.body m) :
    let h := x64ScalarLayout.layoutOf (toAmd64Program symName dirs ++ []) hsmall
    x64ScalarTarget.LabelsUnique h ∧
    printAsm0 (toAmd64Program symName dirs) = Kraken.X64.toATT (toAmd64Program symName dirs) ∧
    x64ScalarTarget.Defined h (symName fn.name) ∧
    x64ScalarTarget.FnSpec h (symName fn.name)
      (Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs))
      ((lookupBound0 bounds fn.name).getD 0) 0 := by
  have hbd := modBoundsOk0_of_computeBounds0 hacyc hb (fun _ h => nomatch h)
  have hnd : ([fn].map (fun f => symName f.name) ++ ([] : List Sym0).map symName).Nodup := by simp
  obtain ⟨hu, hfns⟩ := leanqbe0Compile_sound_layout (Γ := Γ) hc hg hnd
    (fun _ hm => by simp at hm; subst hm; exact hnoloc)
    (fun _ h => nomatch h) hsmall hbd (fun _ h => nomatch h) hwp
  obtain ⟨hdef, hspec⟩ := hfns fn (by simp)
  exact ⟨hu, leanqbe0Compile_printAsm0 hc, hdef, hspec⟩

private theorem run_i64_of_host {h : x64ScalarMach.Host} {nm : Sym} {as : List Ty}
    {spec : Spec as [i64]} {b : Nat} (hf : x64ScalarTarget.FnSpec h nm spec b 0)
    (args : Tup Val as) (v : BitVec 64) (hb : b ≤ 2048)
    (hargs : (x64ScalarTarget.toIsa.assignArgs as).isSome = true)
    (hspec : spec args (([] : List UInt8).At 0x1000#64) (fun r _ => r = (v, ()))
      (fun _ _ _ _ => False)) :
    Eventually (x64ScalarMach.step h)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = v)
      (x64ScalarMach.mkState (x64ScalarInit.initState (as := as) b [] args)
        (x64ScalarMach.labelAddr h nm)) :=
  TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit h hf [] args v hb (by decide) hargs hspec
    (fun _ _ h => h)

local macro "single_mod_bundle" okId:ident execId:ident mod:term:max fnSym:term:max fnNm:str
    spec:term:max asTy:term:max dirs:term:max ms:term:max small:term:max bounds:term:max
    compOk:term:max hostOk:term:max execArgs:term:max "[" execBinds:bracketedBinder* "]"
    "=>" execVal:term:max "by" hspecPf:tacticSeq : command =>
  `(theorem $okId :
      ∃ (dirs : List Dir0) (ms : UInt32)
        (hsmall : x64ScalarProgSmall
          (toAmd64Program $fnSym dirs ++
            ($mod).exits.map (fun g => x64Frame.label ($fnSym g))) = true)
        (bound : Nat),
        leanqbe0Compile $mod = .ok dirs ms ∧ bound ≤ 2048 ∧
        let h := x64ScalarLayout.layoutOf
          (toAmd64Program $fnSym dirs ++
            ($mod).exits.map (fun g => x64Frame.label ($fnSym g))) hsmall
        x64ScalarTarget.LabelsUnique h ∧
        printAsm0 (toAmd64Program $fnSym dirs) = Kraken.X64.toATT (toAmd64Program $fnSym dirs) ∧
        x64ScalarTarget.Defined h $fnNm ∧
        x64ScalarTarget.FnSpec (as := $asTy) (bs := [i64]) h $fnNm $spec bound 0 :=
      ⟨$dirs, $ms, $small, (lookupBound0 $bounds 0).getD 0,
        $compOk, of_decide_eq_true (by t_kernel_rfl), $hostOk⟩
    theorem $execId $execBinds* :
      ∃ (dirs : List Dir0) (ms : UInt32)
        (hsmall : x64ScalarProgSmall
          (toAmd64Program $fnSym dirs ++
            ($mod).exits.map (fun g => x64Frame.label ($fnSym g))) = true)
        (bound : Nat),
        leanqbe0Compile $mod = .ok dirs ms ∧ bound ≤ 2048 ∧
        let h := x64ScalarLayout.layoutOf
          (toAmd64Program $fnSym dirs ++
            ($mod).exits.map (fun g => x64Frame.label ($fnSym g))) hsmall
        Eventually (x64ScalarMach.step h)
          (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = $execVal)
          (x64ScalarMach.mkState (x64ScalarInit.initState (as := $asTy) bound [] $execArgs)
            (x64ScalarMach.labelAddr h $fnNm)) :=
      ⟨$dirs, $ms, $small, (lookupBound0 $bounds 0).getD 0,
        $compOk, of_decide_eq_true (by t_kernel_rfl),
        run_i64_of_host ($hostOk).2.2.2 $execArgs $execVal
          (of_decide_eq_true (by t_kernel_rfl)) (by decide) (by $hspecPf)⟩)

/-! ## 1. `dummyAddMod0` (`add2(a, b) = a + b`): Soundness, `PrintAsm0`, & Execution -/

private def symNameAdd (id : Sym0) : Sym := if id == 0 then "add2" else s!"sym_{id.toNat}"
private def addDirs : List Dir0 := dirsOf (leanqbe0Compile dummyAddMod0)
private def addMaxSl : UInt32 := maxSlOf (leanqbe0Compile dummyAddMod0)
private def addBounds : List (Sym0 × Nat) := (dummyAddMod0.computeBounds0 [] 0).getD []
private theorem add_compile_ok :
    leanqbe0Compile dummyAddMod0 = .ok addDirs addMaxSl := by t_kernel_rfl
private theorem add_bounds_ok : dummyAddMod0.computeBounds0 [] 0 = some addBounds := by t_kernel_rfl
private theorem add_small :
    x64ScalarProgSmall (toAmd64Program symNameAdd addDirs ++ []) = true := by t_kernel_rfl

private def addEnv : Env := fun nm as rs =>
  match nm, as, rs with
  | "add2", [.bits 64, .bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + args.2.1, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem add_wp0 :
    ∀ fn ∈ dummyAddMod0.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      addEnv (symNameAdd fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 addEnv symNameAdd fn.rs (pushTup args []) [] Q X fn.body m := by
  intro fn hfn; simp only [dummyAddMod0, List.mem_singleton] at hfn; subst hfn
  change ∀ (args : Tup Val [i64, i64]) m (Q : Post [i64]) X,
    addEnv "add2" [i64, i64] [i64] args m Q X →
    wp0 addEnv symNameAdd [.b64] [⟨i64, args.2.1⟩, ⟨i64, args.1⟩] [] Q X dummyAddFn0.body m
  intro args m Q X hΓ; rcases args with ⟨a, b, ⟨⟩⟩
  dsimp only [dummyAddFn0, addEnv] at hΓ ⊢
  refine wp0_let1_op (op := .bin .add .b64) (argv := (a, b, ())) rfl ?_
  dsimp only [op0ToOpCode, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, pushTup]
  exact wp0_ret64 (v := a + b) rfl hΓ

set_option warn.classDefReducibility false in
private def addHost : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf (toAmd64Program symNameAdd addDirs ++ []) add_small

private theorem add_host_ok :
    x64ScalarTarget.LabelsUnique addHost ∧
    printAsm0 (toAmd64Program symNameAdd addDirs) =
      Kraken.X64.toATT (toAmd64Program symNameAdd addDirs) ∧
    x64ScalarTarget.Defined addHost "add2" ∧
    x64ScalarTarget.FnSpec (as := [i64, i64]) (bs := [i64]) addHost "add2"
      (fun args m Q _ => Q (args.1 + args.2.1, ()) m)
      ((lookupBound0 addBounds 0).getD 0) 0 :=
  singleFn_host_ok add_compile_ok (by t_kernel_rfl) (by t_kernel_rfl) add_bounds_ok
    (by t_kernel_rfl) add_small add_wp0

single_mod_bundle add_ok add_exec dummyAddMod0
  (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") "add2"
  (fun args m Q _ => Q (args.1 + args.2.1, ()) m) [i64, i64]
  addDirs addMaxSl add_small addBounds add_compile_ok add_host_ok
  (a, b, ()) [(a : BitVec 64) (b : BitVec 64)] => (a + b) by rfl

/-! ## 2. `dummyLoopMod0` (`sumto(n)`): Loop Invariant `wp0` + Soundness + Execution -/

private def symNameLoop (id : Sym0) : Sym := if id == 0 then "sumto" else s!"sym_{id.toNat}"

private def sumAcc64 (k : Nat) (n acc : BitVec 64) : BitVec 64 :=
  match k with | 0 => acc | k' + 1 => sumAcc64 k' (n - 1#64) (acc + n)

private theorem sumAcc64_eq_natRec (k : Nat) (x acc : BitVec 64) :
    sumAcc64 k x acc =
      Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
        (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y)) k x acc := by
  induction k generalizing x acc with
  | zero => rfl
  | succ _ ih => exact ih (x - 1#64) (acc + x)

private def loopDirs : List Dir0 := dirsOf (leanqbe0Compile dummyLoopMod0)
private def loopMaxSl : UInt32 := maxSlOf (leanqbe0Compile dummyLoopMod0)
private def loopBounds : List (Sym0 × Nat) := (dummyLoopMod0.computeBounds0 [] 0).getD []
private theorem loop_compile_ok : leanqbe0Compile dummyLoopMod0 = .ok loopDirs loopMaxSl := by
  t_kernel_rfl
private theorem loop_bounds_ok : dummyLoopMod0.computeBounds0 [] 0 = some loopBounds := by
  t_kernel_rfl
private theorem loop_small :
    x64ScalarProgSmall (toAmd64Program symNameLoop loopDirs ++ []) = true := by t_kernel_rfl

private def loopEnv : Env := fun nm as rs =>
  match nm, as, rs with
  | "sumto", [.bits 64], [.bits 64] =>
    fun args m Q _ => Q (sumAcc64 args.1.toNat args.1 0#64, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem loop_wp0 :
    ∀ fn ∈ dummyLoopMod0.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      loopEnv (symNameLoop fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 loopEnv symNameLoop fn.rs (pushTup args []) [] Q X fn.body m := by
  intro fn hfn; simp only [dummyLoopMod0, List.mem_singleton] at hfn; subst hfn
  change ∀ (args : Tup Val [i64]) m (Q : Post (ty0ListToTy [.b64])) X,
    loopEnv "sumto" [i64] (ty0ListToTy [.b64]) args m Q X →
    wp0 loopEnv symNameLoop [.b64] (pushTup (f := Val) (as := [i64]) args []) [] Q X
      dummySumToFn0.body m
  intro args m Q X hΓ; rcases args with ⟨n, ⟨⟩⟩
  dsimp only [dummySumToFn0, pushTup, loopEnv] at hΓ ⊢
  rw [wp0_group]; intro Js hcl; rcases Js with ⟨J, ⟨⟩⟩; rw [closed0_cons] at hcl
  have hstep := hcl.1
  have hinv : ∀ (k : Nat) (x acc : BitVec 64),
      x.toNat = k → Q (sumAcc64 k x acc, ()) m → J (x, acc, ()) m := by
    intro k; induction k with
    | zero =>
      intro x acc hkx hQ
      have hx0 : x = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hkx)
      refine hstep (x, acc, ()) m ?_
      refine wp0_let1_op (op := .cmp .eq .b64) (argv := (x, 0#64, ())) rfl ?_
      dsimp only [op0ToOpCode, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        pushTup]
      refine wp0_jnz_bool (b := decide (x = 0#64)) rfl
        (fun _ => wp0_ret64 (v := acc) rfl hQ) (fun hne => by simp [hx0] at hne)
    | succ k' ih =>
      intro x acc hkx hQ
      have hxne : x ≠ 0#64 := fun he => by have := congrArg BitVec.toNat he; simp at this; omega
      have hsub : (x - 1#64).toNat = k' := by
        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      refine hstep (x, acc, ()) m ?_
      refine wp0_let1_op (op := .cmp .eq .b64) (argv := (x, 0#64, ())) rfl ?_
      dsimp only [op0ToOpCode, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        pushTup]
      refine wp0_jnz_bool (b := decide (x = 0#64)) rfl (fun he => by simp [hxne] at he) fun _ => ?_
      refine wp0_let1_op (op := .bin .add .b64) (argv := (acc, x, ())) rfl ?_
      dsimp only [op0ToOpCode, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        pushTup]
      refine wp0_let1_op (op := .bin .sub .b64) (argv := (x, 1#64, ())) rfl ?_
      dsimp only [op0ToOpCode, OpCode.wp, lift2, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        pushTup]
      exact wp0_jump0_two64 (a := x - 1#64) (b := acc + x) rfl (ih (x - 1#64) (acc + x) hsub hQ)
  exact wp0_jump0_two64 (a := n) (b := 0#64) rfl (hinv n.toNat n 0#64 rfl hΓ)

set_option warn.classDefReducibility false in
private def loopHost : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf (toAmd64Program symNameLoop loopDirs ++ []) loop_small

private theorem loop_host_ok :
    x64ScalarTarget.LabelsUnique loopHost ∧
    printAsm0 (toAmd64Program symNameLoop loopDirs) =
      Kraken.X64.toATT (toAmd64Program symNameLoop loopDirs) ∧
    x64ScalarTarget.Defined loopHost "sumto" ∧
    x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) loopHost "sumto"
      (fun args m Q _ =>
        let sum := Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
          (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y))
        Q (sum args.1.toNat args.1 0#64, ()) m)
      ((lookupBound0 loopBounds 0).getD 0) 0 := by
  have ⟨h0, h1, h2, h3⟩ := singleFn_host_ok loop_compile_ok (by t_kernel_rfl) (by t_kernel_rfl)
    loop_bounds_ok (by t_kernel_rfl) loop_small loop_wp0
  have hspec₀ : x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) loopHost "sumto"
      (loopEnv "sumto" [i64] [i64]) ((lookupBound0 loopBounds 0).getD 0) 0 := h3
  have hspec_eq : loopEnv "sumto" [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ =>
        let sum := Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
          (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y))
        Q (sum args.1.toNat args.1 0#64, ()) m) := by
    funext args m Q X; simp only [loopEnv, i64, sumAcc64_eq_natRec]
  rw [hspec_eq] at hspec₀; exact ⟨h0, h1, h2, hspec₀⟩

single_mod_bundle loop_ok loop_exec5 dummyLoopMod0
  (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") "sumto"
  (fun args m Q _ =>
    let sum := Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
      (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y))
    Q (sum args.1.toNat args.1 0#64, ()) m) [i64]
  loopDirs loopMaxSl loop_small loopBounds loop_compile_ok loop_host_ok (5#64, ()) [] => 15#64 by
  decide

/-! ## 3. Bridged `Frontend.C0.TFlatFn` Two-Function Pipeline (`c0_add_one`, `c0_add_two`) -/

private def c0AddOneTf : Frontend.C0.TFlatFn :=
  { name := "c0_add_one", as := [i64], rs := [i64]
    flat := .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) }

private def c0AddTwoTf : Frontend.C0.TFlatFn :=
  { name := "c0_add_two", as := [i64], rs := [i64]
    flat := .call "c0_add_one" (as := [i64]) [i64] (.var 0, ())
      (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ()))) }

private def c0Tfs : List Frontend.C0.TFlatFn := [c0AddOneTf, c0AddTwoTf]
private def c0Mod : Module :=
  { fns := c0Tfs.map Frontend.C0.TFlatFn.toFn, externs := [], exits := [] }
private def c0BridgePair : TFlatModule0 × List (Sym × Sym0) :=
  (ofTFlatModule c0Tfs [] []).toOption.getD ({ fns := [], externs := [], exits := [] }, [])
private def c0Mod0 : TFlatModule0 := c0BridgePair.1
private def c0Tbl : List (Sym × Sym0) := c0BridgePair.2
private def c0Dirs : List Dir0 := dirsOf (leanqbe0Compile c0Mod0)
private def c0MaxSl : UInt32 := maxSlOf (leanqbe0Compile c0Mod0)
private def c0Bounds : List (Sym0 × Nat) := (c0Mod0.computeBounds0 [] 0).getD []
private theorem c0_bridge_ok : ofTFlatModule c0Tfs [] [] = .ok (c0Mod0, c0Tbl) := by t_kernel_rfl
private theorem c0_compile_ok : leanqbe0Compile c0Mod0 = .ok c0Dirs c0MaxSl := by t_kernel_rfl
private theorem c0_bounds_ok : c0Mod0.computeBounds0 [] 0 = some c0Bounds := by t_kernel_rfl
private theorem c0_small :
    x64ScalarProgSmall (toAmd64Program (symNameOf c0Tbl) c0Dirs ++ []) = true := by t_kernel_rfl

private def c0Env : Env := fun nm as rs =>
  match nm, as, rs with
  | "c0_add_one", [.bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + 1#64, ()) m
  | "c0_add_two", [.bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + 1#64 + 1#64, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem c0_add1_wp (Γ : Env) (a : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (tail : List ((t : Ty) × Val t)) (hq : Q (a + 1#64, ()) m) :
    wp Γ Q X (denote Val Cont (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) :
      TFlat [i64]) (pushTup (f := Val) (as := [i64]) (a, ()) tail) []) m := by
  have hx0 : denoteArg (⟨i64, a⟩ :: tail) (Arg.var 0 : Arg K i64) = some (Arg.var a) := by
    simp [denoteArg, lookupV, listGet?, castTy]
  have hden : denote Val Cont
      (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) : TFlat [i64])
      (pushTup (f := Val) (as := [i64]) (a, ()) tail) [] =
      Expr.let_ (op2 (.add i64) (.var a) (.imm 1#64)) (fun xs => Expr.ret (.var xs.1, ())) := by
    dsimp only [denote, op2, denoteArgs, pushTup]; rw [hx0]; rfl
  rw [hden]; dsimp only [wp, Op.wp, OpCode.wp, op2, lift2, vals, Arg.val]
  simpa [Ty.hasFloat] using hq

private theorem c0_moduleOk : ModuleOk c0Env c0Mod := by
  refine Module.moduleOk_of_checkAcyclic (by t_kernel_rfl) (fun fn hmem => ?_)
    (fun fn hmem => ?_) <;>
  · simp only [c0Mod, c0Tfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    all_goals first
      | exact Frontend.C0.TFlatFn.toFn_wf _
      | (intro xs m Q X hΓ; rcases xs with ⟨a, ⟨⟩⟩
         dsimp only [c0AddOneTf, c0AddTwoTf, Frontend.C0.TFlatFn.toFn, Func.wp, denoteFunc,
           c0Env] at hΓ ⊢
         first
         | exact c0_add1_wp c0Env a m Q X [] hΓ
         | (have hden : denote Val Cont (TFlat.call "c0_add_one" (as := [i64]) [i64] (.var 0, ())
                (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ()))) : TFlat [i64])
                (pushTup (f := Val) (as := [i64]) (a, ()) []) [] =
                Expr.call "c0_add_one" (as := [i64]) (bs := [i64]) (Arg.var a, ()) (fun xs =>
                  denote Val Cont (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())))
                    (pushTup (f := Val) (as := [i64]) xs [⟨i64, a⟩]) []) := rfl
            rw [hden]; dsimp only [wp, vals, Arg.val]
            exact ⟨fun r m' => r = (a + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False, ⟨rfl, rfl⟩,
              fun _ _ ⟨hr, hm⟩ => hr ▸ hm ▸ c0_add1_wp c0Env (a + 1#64) m Q X [⟨i64, a⟩] hΓ,
              fun _ _ _ _ hf => hf.elim⟩))

set_option warn.classDefReducibility false in
private def c0Host : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf (toAmd64Program (symNameOf c0Tbl) c0Dirs ++ []) c0_small

private theorem c0_host_ok :
    x64ScalarTarget.LabelsUnique c0Host ∧
    printAsm0 (toAmd64Program (symNameOf c0Tbl) c0Dirs) =
      Kraken.X64.toATT (toAmd64Program (symNameOf c0Tbl) c0Dirs) ∧
    x64ScalarTarget.Defined c0Host "c0_add_two" ∧
    x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) c0Host "c0_add_two"
      (fun args m Q _ => Q (args.1 + 1#64 + 1#64, ()) m)
      ((lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0) 0 := by
  obtain ⟨hu, hprint, hfns⟩ := bridge_leanqbe0Compile_layout (Γ := c0Env) c0Tfs [] []
    c0_bridge_ok c0_compile_ok (by t_kernel_rfl) (of_decide_eq_true (by t_kernel_rfl))
    (List.all_eq_true.mp (by t_kernel_rfl :
      c0Tfs.all (fun tf => tf.flat.wfCheck (pushTypes tf.as []) []) = true))
    (List.all_eq_true.mp (by t_kernel_rfl : c0Tfs.all (fun tf => tflatIdxLtU32 tf.flat) = true))
    (by t_kernel_rfl) List.nodup_nil (fun _ h => nomatch h)
    (List.all_eq_true.mp (by t_kernel_rfl : c0Tfs.all (fun tf => symNoLocPrefix0 tf.name) = true))
    (fun _ h => nomatch h) c0_bounds_ok (fun _ h => nomatch h)
    c0_small c0_moduleOk (fun _ h => nomatch h)
  obtain ⟨hdef, hspec⟩ := hfns c0AddTwoTf (by simp [c0Tfs])
  have hspec₀ : x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) c0Host "c0_add_two"
      (Env.ofModule c0Mod c0Env "c0_add_two" [i64] [i64])
      ((lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0) 0 := hspec
  have hspec_eq : Env.ofModule c0Mod c0Env "c0_add_two" [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ => Q (args.1 + 1#64 + 1#64, ()) m) := by
    funext args m Q X
    exact propext ⟨fun h => h.2, fun h => ⟨by simp [c0Mod, c0Tfs, Module.sigs,
      Frontend.C0.TFlatFn.toFn, Fn.sig, c0AddTwoTf], h⟩⟩
  rw [hspec_eq] at hspec₀; exact ⟨hu, hprint, hdef, hspec₀⟩

local macro "c0_mod_bundle" okId:ident execId:ident : command =>
  `(theorem $okId :
      ∃ (mod : TFlatModule0) (tbl : List (Sym × Sym0)) (dirs : List Dir0) (ms : UInt32)
        (hsmall : x64ScalarProgSmall (toAmd64Program (symNameOf tbl) dirs ++ []) = true)
        (bound : Nat),
        let add1 : Frontend.C0.TFlatFn :=
          { name := "c0_add_one", as := [i64], rs := [i64]
            flat := .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) }
        let add2 : Frontend.C0.TFlatFn :=
          { name := "c0_add_two", as := [i64], rs := [i64]
            flat := .call "c0_add_one" (as := [i64]) [i64] (.var 0, ())
              (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ()))) }
        ofTFlatModule [add1, add2] [] [] = .ok (mod, tbl) ∧
        leanqbe0Compile mod = .ok dirs ms ∧ bound ≤ 2048 ∧
        let h := x64ScalarLayout.layoutOf (toAmd64Program (symNameOf tbl) dirs ++ []) hsmall
        x64ScalarTarget.LabelsUnique h ∧
        printAsm0 (toAmd64Program (symNameOf tbl) dirs) =
          Kraken.X64.toATT (toAmd64Program (symNameOf tbl) dirs) ∧
        x64ScalarTarget.Defined h "c0_add_two" ∧
        x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) h "c0_add_two"
          (fun args m Q _ => Q (args.1 + 1#64 + 1#64, ()) m) bound 0 :=
      ⟨c0Mod0, c0Tbl, c0Dirs, c0MaxSl, c0_small,
        (lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0,
        c0_bridge_ok, c0_compile_ok, of_decide_eq_true (by t_kernel_rfl), c0_host_ok⟩
    theorem $execId :
      ∃ (mod : TFlatModule0) (tbl : List (Sym × Sym0)) (dirs : List Dir0) (ms : UInt32)
        (hsmall : x64ScalarProgSmall (toAmd64Program (symNameOf tbl) dirs ++ []) = true)
        (bound : Nat),
        let add1 : Frontend.C0.TFlatFn :=
          { name := "c0_add_one", as := [i64], rs := [i64]
            flat := .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) }
        let add2 : Frontend.C0.TFlatFn :=
          { name := "c0_add_two", as := [i64], rs := [i64]
            flat := .call "c0_add_one" (as := [i64]) [i64] (.var 0, ())
              (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ()))) }
        ofTFlatModule [add1, add2] [] [] = .ok (mod, tbl) ∧
        leanqbe0Compile mod = .ok dirs ms ∧ bound ≤ 2048 ∧
        let h := x64ScalarLayout.layoutOf (toAmd64Program (symNameOf tbl) dirs ++ []) hsmall
        Eventually (x64ScalarMach.step h)
          (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42#64)
          (x64ScalarMach.mkState (x64ScalarInit.initState (as := [i64]) bound [] (40#64, ()))
            (x64ScalarMach.labelAddr h "c0_add_two")) :=
      ⟨c0Mod0, c0Tbl, c0Dirs, c0MaxSl, c0_small,
        (lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0,
        c0_bridge_ok, c0_compile_ok, of_decide_eq_true (by t_kernel_rfl),
        run_i64_of_host c0_host_ok.2.2.2 (40#64, ()) 42#64
          (of_decide_eq_true (by t_kernel_rfl)) (by decide) (by decide)⟩)

c0_mod_bundle c0_ok c0_exec40

/-! ## 4. Negative Guard Rejection Witnesses & Axiom Hygiene Audit -/

theorem neg_bug_a : (TFlat0.group [([], .hlt), ([], .hlt)] .hlt).singleBlockGroups = false := by
  t_kernel_rfl
theorem neg_bug_b :
    (TFlat0.let1 (.un .neg .bool) [.immBool true] (.ret [.var 0])).noNegBool = false := by
  t_kernel_rfl
theorem neg_bug_c :
    (TFlat0.jnz (.immBool true) (.group [] (.ret [])) (.ret [])).noGroupAfterJnz = false := by
  t_kernel_rfl
theorem pos_dummy_add_guards : dummyAddMod0.okGuardsFull = true := by t_kernel_rfl
theorem pos_dummy_loop_guards : dummyLoopMod0.okGuardsFull = true := by t_kernel_rfl
theorem neg_dummy_call_tail_guards : dummyCallTailMod0.okGuardsFull = false := by t_kernel_rfl

#print axioms compileFn0_fnSpec
#print axioms compileModuleLoop0_sound
#print axioms leanqbe0Compile_fnSpec
#print axioms leanqbe0Compile_sound_layout
#print axioms leanqbe0Compile_printAsm0
#print axioms bridge_leanqbe0Compile_fnSpec
#print axioms bridge_leanqbe0Compile_layout
#print axioms add_ok
#print axioms add_exec
#print axioms loop_ok
#print axioms loop_exec5
#print axioms c0_ok
#print axioms c0_exec40

end LeanQbeBootstrap0Test.Sound0Test
