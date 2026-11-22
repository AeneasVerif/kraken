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
2. `dummyAddMod0` (`add2(a, b) = a + b`): `leanqbe0Compile_sound_layout`, `PrintAsm0` AT&T
   agreement, and closed `Eventually (x64ScalarMach.step h)` execution via `x64ScalarInit`.
3. `dummyLoopMod0` (`sumto(n)`): `wp0` loop invariant proof + `leanqbe0Compile_sound_layout`
   + closed machine execution on `sumto 5#64 = 15#64`.
4. Real `Frontend.C0.TFlatFn` multi-function bridged module (`c0_add_one` / `c0_add_two`):
   `Bridge0.ofTFlatModule` + `Module.checkAcyclic` + `ModuleOk` + `bridge_leanqbe0Compile_layout`
   + closed `x64ScalarInit` machine run `c0_add_two 40#64 = 42#64`.
5. Negative kernel witnesses for Bugs A (`singleBlockGroups`), B (`noNegBool`), and C
   (`noGroupAfterJnz`), plus strict `[propext, Classical.choice, Quot.sound]` `#print axioms`.
-/

set_option autoImplicit false

public section

namespace LeanQbeBootstrap0Test.Sound0Test

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let arm := env.allImportedModuleNames.filter fun n =>
    n.toString.startsWith "LeanQbe.T.Arm64" || n.toString.startsWith "Kraken.AArch64"
  if !arm.isEmpty then
    throwError "forbidden Arm64/AArch64 imports: {arm.toList}"

private theorem wp0_let1_add64 {Γ symName curRs vs ls Q X} {args : List Arg0}
    {a b : BitVec 64} {k m}
    (hev : evalArgs0Ty vs (ty0ListToTy (op0ArgTys (.bin .add .b64))) args = some (a, b, ()))
    (h : wp0 Γ symName curRs (⟨i64, a + b⟩ :: vs) ls Q X k m) :
    wp0 Γ symName curRs vs ls Q X (.let1 (.bin .add .b64) args k) m := by
  rw [wp0_let1, hev]
  exact h

private theorem wp0_let1_sub64 {Γ symName curRs vs ls Q X} {args : List Arg0}
    {a b : BitVec 64} {k m}
    (hev : evalArgs0Ty vs (ty0ListToTy (op0ArgTys (.bin .sub .b64))) args = some (a, b, ()))
    (h : wp0 Γ symName curRs (⟨i64, a - b⟩ :: vs) ls Q X k m) :
    wp0 Γ symName curRs vs ls Q X (.let1 (.bin .sub .b64) args k) m := by
  rw [wp0_let1, hev]
  exact h

private theorem wp0_let1_cmp_eq64 {Γ symName curRs vs ls Q X} {args : List Arg0}
    {a b : BitVec 64} {k m}
    (hev : evalArgs0Ty vs (ty0ListToTy (op0ArgTys (.cmp .eq .b64))) args = some (a, b, ()))
    (h : wp0 Γ symName curRs (⟨.bool, decide (a = b)⟩ :: vs) ls Q X k m) :
    wp0 Γ symName curRs vs ls Q X (.let1 (.cmp .eq .b64) args k) m := by
  rw [wp0_let1, hev]
  exact h

private theorem wp0_jnz_bool {Γ symName curRs vs ls Q X} {c : Arg0} {t e : TFlat0}
    {b : Bool} {m : Mem 64}
    (hev : evalArg0Ty vs .bool c = some b)
    (ht : b = true → wp0 Γ symName curRs vs ls Q X t m)
    (he : b = false → wp0 Γ symName curRs vs ls Q X e m) :
    wp0 Γ symName curRs vs ls Q X (.jnz c t e) m := by
  rw [wp0_jnz, hev]
  exact ⟨ht, he⟩

private theorem wp0_ret64 {Γ symName vs ls Q X} {args : List Arg0} {v : BitVec 64} {m : Mem 64}
    (hev : evalArgs0Ty vs (ty0ListToTy [.b64]) args =
      (some (v, ()) : Option (Tup Val (ty0ListToTy [.b64]))))
    (hq : Q (v, ()) m) :
    wp0 Γ symName [.b64] vs ls Q X (.ret args) m := by
  rw [wp0_ret, hev]
  exact hq

private theorem wp0_jump0_two64 {Γ symName curRs vs Q X}
    {J : Cont (ty0ListToTy [.b64, .b64])} {args : List Arg0} {a b : BitVec 64} {m : Mem 64}
    (hev : evalArgs0Ty vs (ty0ListToTy [.b64, .b64]) args =
      (some (a, b, ()) : Option (Tup Val (ty0ListToTy [.b64, .b64]))))
    (hj : J (a, b, ()) m) :
    wp0 Γ symName curRs vs [⟨ty0ListToTy [.b64, .b64], J⟩] Q X (.jump 0 args) m := by
  rw [wp0_jump]
  have hget : listGet? [(⟨ty0ListToTy [.b64, .b64], J⟩ : (ts : List Ty) × Cont ts)]
      (UInt32.toNat 0) = some ⟨ty0ListToTy [.b64, .b64], J⟩ := rfl
  rw [hget]
  dsimp only
  rw [hev]
  exact hj

private theorem wp0_step_loop_body {Γ symName} {J : Cont (ty0ListToTy [.b64, .b64])}
    {Q X} {x acc n : BitVec 64} {body : TFlat0} {m : Mem 64}
    (h : wp0 Γ symName [.b64] [⟨i64, acc⟩, ⟨i64, x⟩, ⟨i64, n⟩]
      [⟨ty0ListToTy [.b64, .b64], J⟩] Q X body m) :
    wp0 Γ symName [.b64]
      (pushTup (f := Val) (as := ty0ListToTy [.b64, .b64]) (x, acc, ()) [⟨i64, n⟩])
      (pushConts0 [([.b64, .b64], body)] (J, ()) []) Q X body m := h

private theorem wp0_step_loop_entry {Γ symName} {J : Cont (ty0ListToTy [.b64, .b64])}
    {Q X} {n : BitVec 64} {body : TFlat0} {args : List Arg0} {m : Mem 64}
    (h : wp0 Γ symName [.b64] [⟨i64, n⟩] [⟨ty0ListToTy [.b64, .b64], J⟩] Q X (.jump 0 args) m) :
    wp0 Γ symName [.b64] [⟨i64, n⟩] (pushConts0 [([.b64, .b64], body)] (J, ()) []) Q X
      (.jump 0 args) m := h

/-! ## 1. `dummyAddMod0` (`add2(a, b) = a + b`): Soundness, `PrintAsm0`, & Execution -/

private def symNameAdd (id : Sym0) : Sym :=
  if id == 0 then "add2" else s!"sym_{id.toNat}"

private def addDirs : List Dir0 :=
  match leanqbe0Compile dummyAddMod0 with
  | .ok dirs _ => dirs
  | .err _ _ => []

private def addMaxSl : UInt32 :=
  match leanqbe0Compile dummyAddMod0 with
  | .ok _ ms => ms
  | .err _ _ => 0

private def addBounds : List (Sym0 × Nat) :=
  (dummyAddMod0.computeBounds0 [] 0).getD []

private theorem add_compile_ok :
    leanqbe0Compile dummyAddMod0 = .ok addDirs addMaxSl := by
  t_kernel_rfl

private theorem add_bounds_ok : dummyAddMod0.computeBounds0 [] 0 = some addBounds := by
  t_kernel_rfl

private theorem add_small :
    x64ScalarProgSmall
      (toAmd64Program symNameAdd addDirs ++
        dummyAddMod0.exits.map (fun g => x64Frame.label (symNameAdd g))) = true := by
  t_kernel_rfl

private def addEnv : Env := fun nm as rs =>
  match nm, as, rs with
  | "add2", [.bits 64, .bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + args.2.1, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem add_wp0 :
    ∀ fn ∈ dummyAddMod0.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      addEnv (symNameAdd fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 addEnv symNameAdd fn.rs (pushTup args []) [] Q X fn.body m := by
  intro fn hfn
  simp only [dummyAddMod0, List.mem_singleton] at hfn
  subst hfn
  change ∀ (args : Tup Val [i64, i64]) m (Q : Post (ty0ListToTy [.b64])) X,
    addEnv "add2" [i64, i64] (ty0ListToTy [.b64]) args m Q X →
    wp0 addEnv symNameAdd [.b64] [⟨i64, args.2.1⟩, ⟨i64, args.1⟩] [] Q X dummyAddFn0.body m
  intro args m Q X hΓ
  rcases args with ⟨a, b, ⟨⟩⟩
  dsimp only [dummyAddFn0]
  refine wp0_let1_add64 (a := a) (b := b) rfl ?_
  exact wp0_ret64 (v := a + b) rfl hΓ

set_option warn.classDefReducibility false in
private def addHost : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf
    (toAmd64Program symNameAdd addDirs ++
      dummyAddMod0.exits.map (fun g => x64Frame.label (symNameAdd g)))
    add_small

private theorem add_host_ok :
    x64ScalarTarget.LabelsUnique addHost ∧
    printAsm0 (toAmd64Program symNameAdd addDirs) =
      Kraken.X64.toATT (toAmd64Program symNameAdd addDirs) ∧
    x64ScalarTarget.Defined addHost "add2" ∧
    x64ScalarTarget.FnSpec (as := [i64, i64]) (bs := [i64]) addHost "add2"
      (fun args m Q _ => Q (args.1 + args.2.1, ()) m)
      ((lookupBound0 addBounds 0).getD 0) 0 := by
  have hbd := modBoundsOk0_of_computeBounds0 (mod := dummyAddMod0)
    (by t_kernel_rfl) add_bounds_ok (fun _ h => nomatch h)
  have hnd : (dummyAddMod0.fns.map (fun fn => symNameAdd fn.name) ++
      dummyAddMod0.exits.map symNameAdd).Nodup := by
    dsimp only [dummyAddMod0, List.map_cons, List.map_nil, List.append_nil]
    simp
  have hnoloc : ∀ fn ∈ dummyAddMod0.fns, symNoLocPrefix0 (symNameAdd fn.name) = true := by
    intro _ hm
    simp only [dummyAddMod0, List.mem_singleton] at hm
    subst hm; t_kernel_rfl
  obtain ⟨hu, hfns⟩ := leanqbe0Compile_sound_layout (Γ := addEnv)
    add_compile_ok (by t_kernel_rfl) hnd hnoloc
    (fun _ h => nomatch h) add_small hbd (fun _ h => nomatch h) add_wp0
  obtain ⟨hdef, hspec⟩ := hfns dummyAddFn0 (by simp [dummyAddMod0])
  exact ⟨hu, leanqbe0Compile_printAsm0 add_compile_ok, hdef, hspec⟩

theorem add_ok :
    ∃ (dirs : List Dir0) (ms : UInt32)
      (hsmall : x64ScalarProgSmall
        (toAmd64Program (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs ++
          dummyAddMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "add2" else s!"sym_{g.toNat}"))) = true)
      (bound : Nat),
      leanqbe0Compile dummyAddMod0 = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs ++
          dummyAddMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "add2" else s!"sym_{g.toNat}")))
        hsmall
      x64ScalarTarget.LabelsUnique h ∧
      printAsm0 (toAmd64Program
          (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs) =
        Kraken.X64.toATT (toAmd64Program
          (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs) ∧
      x64ScalarTarget.Defined h "add2" ∧
      x64ScalarTarget.FnSpec (as := [i64, i64]) (bs := [i64]) h "add2"
        (fun args m Q _ => Q (args.1 + args.2.1, ()) m)
        bound 0 :=
  ⟨addDirs, addMaxSl, add_small, (lookupBound0 addBounds 0).getD 0,
    add_compile_ok, of_decide_eq_true (by t_kernel_rfl), add_host_ok⟩

theorem add_exec (a b : BitVec 64) :
    ∃ (dirs : List Dir0) (ms : UInt32)
      (hsmall : x64ScalarProgSmall
        (toAmd64Program (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs ++
          dummyAddMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "add2" else s!"sym_{g.toNat}"))) = true)
      (bound : Nat),
      leanqbe0Compile dummyAddMod0 = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program (fun id => if id == 0 then "add2" else s!"sym_{id.toNat}") dirs ++
          dummyAddMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "add2" else s!"sym_{g.toNat}")))
        hsmall
      Eventually (x64ScalarMach.step h)
        (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = a + b)
        (x64ScalarMach.mkState
          (x64ScalarInit.initState (as := [i64, i64]) bound [] (a, b, ()))
          (x64ScalarMach.labelAddr h "add2")) :=
  ⟨addDirs, addMaxSl, add_small, (lookupBound0 addBounds 0).getD 0,
    add_compile_ok, of_decide_eq_true (by t_kernel_rfl),
    TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit addHost add_host_ok.2.2.2 [] (a, b, ())
      (a + b) (of_decide_eq_true (by t_kernel_rfl)) (by decide) (by decide)
      (Q := fun r _ => r = (a + b, ())) rfl (fun _ _ h => h)⟩

/-! ## 2. `dummyLoopMod0` (`sumto(n)`): Loop Invariant `wp0` + Soundness + Execution -/

private def symNameLoop (id : Sym0) : Sym :=
  if id == 0 then "sumto" else s!"sym_{id.toNat}"

private def sumAcc64 (k : Nat) (n acc : BitVec 64) : BitVec 64 :=
  match k with
  | 0 => acc
  | k' + 1 => sumAcc64 k' (n - 1#64) (acc + n)

private theorem sumAcc64_eq_natRec (k : Nat) (x acc : BitVec 64) :
    sumAcc64 k x acc =
      Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
        (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y)) k x acc := by
  induction k generalizing x acc with
  | zero => rfl
  | succ _ ih => exact ih (x - 1#64) (acc + x)

private def loopDirs : List Dir0 :=
  match leanqbe0Compile dummyLoopMod0 with
  | .ok dirs _ => dirs
  | .err _ _ => []

private def loopMaxSl : UInt32 :=
  match leanqbe0Compile dummyLoopMod0 with
  | .ok _ ms => ms
  | .err _ _ => 0

private def loopBounds : List (Sym0 × Nat) :=
  (dummyLoopMod0.computeBounds0 [] 0).getD []

private theorem loop_compile_ok :
    leanqbe0Compile dummyLoopMod0 = .ok loopDirs loopMaxSl := by
  t_kernel_rfl

private theorem loop_bounds_ok : dummyLoopMod0.computeBounds0 [] 0 = some loopBounds := by
  t_kernel_rfl

private theorem loop_small :
    x64ScalarProgSmall
      (toAmd64Program symNameLoop loopDirs ++
        dummyLoopMod0.exits.map (fun g => x64Frame.label (symNameLoop g))) = true := by
  t_kernel_rfl

private def loopEnv : Env := fun nm as rs =>
  match nm, as, rs with
  | "sumto", [.bits 64], [.bits 64] =>
    fun args m Q _ => Q (sumAcc64 args.1.toNat args.1 0#64, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem loop_wp0 :
    ∀ fn ∈ dummyLoopMod0.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      loopEnv (symNameLoop fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 loopEnv symNameLoop fn.rs (pushTup args []) [] Q X fn.body m := by
  intro fn hfn
  simp only [dummyLoopMod0, List.mem_singleton] at hfn
  subst hfn
  change ∀ (args : Tup Val [i64]) m (Q : Post (ty0ListToTy [.b64])) X,
    loopEnv "sumto" [i64] (ty0ListToTy [.b64]) args m Q X →
    wp0 loopEnv symNameLoop [.b64]
      (pushTup (f := Val) (as := [i64]) args []) [] Q X dummySumToFn0.body m
  intro args m Q X hΓ
  rcases args with ⟨n, ⟨⟩⟩
  dsimp only [dummySumToFn0, pushTup]
  rw [wp0_group]
  intro Js hcl
  rcases Js with ⟨J, ⟨⟩⟩
  rw [closed0_cons] at hcl
  have hstep := hcl.1
  have hinv : ∀ (k : Nat) (x acc : BitVec 64),
      x.toNat = k → Q (sumAcc64 k x acc, ()) m → J (x, acc, ()) m := by
    intro k
    induction k with
    | zero =>
      intro x acc hkx hQ
      have hx0 : x = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hkx)
      apply hstep (x, acc, ()) m
      apply wp0_step_loop_body
      refine wp0_let1_cmp_eq64 (a := x) (b := 0#64) rfl ?_
      refine wp0_jnz_bool (b := decide (x = 0#64)) rfl (fun _ => ?_)
        (fun hne => by simp [hx0] at hne)
      exact wp0_ret64 (v := acc) rfl hQ
    | succ k' ih =>
      intro x acc hkx hQ
      have hxne : x ≠ 0#64 := fun he => by
        have := congrArg BitVec.toNat he
        simp at this
        omega
      have hsub : (x - 1#64).toNat = k' := by
        rw [BitVec.toNat_sub]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hj_rec : J (x - 1#64, acc + x, ()) m := ih (x - 1#64) (acc + x) hsub hQ
      apply hstep (x, acc, ()) m
      apply wp0_step_loop_body
      refine wp0_let1_cmp_eq64 (a := x) (b := 0#64) rfl ?_
      refine wp0_jnz_bool (b := decide (x = 0#64)) rfl (fun he => by simp [hxne] at he)
        (fun _ => ?_)
      refine wp0_let1_add64 (a := acc) (b := x) rfl ?_
      refine wp0_let1_sub64 (a := x) (b := 1#64) rfl ?_
      exact wp0_jump0_two64 (a := x - 1#64) (b := acc + x) rfl hj_rec
  apply wp0_step_loop_entry
  exact wp0_jump0_two64 (a := n) (b := 0#64) rfl (hinv n.toNat n 0#64 rfl hΓ)

set_option warn.classDefReducibility false in
private def loopHost : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf
    (toAmd64Program symNameLoop loopDirs ++
      dummyLoopMod0.exits.map (fun g => x64Frame.label (symNameLoop g)))
    loop_small

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
  have hbd := modBoundsOk0_of_computeBounds0 (mod := dummyLoopMod0)
    (by t_kernel_rfl) loop_bounds_ok (fun _ h => nomatch h)
  have hnd : (dummyLoopMod0.fns.map (fun fn => symNameLoop fn.name) ++
      dummyLoopMod0.exits.map symNameLoop).Nodup := by
    dsimp only [dummyLoopMod0, List.map_cons, List.map_nil, List.append_nil]
    simp
  have hnoloc : ∀ fn ∈ dummyLoopMod0.fns, symNoLocPrefix0 (symNameLoop fn.name) = true := by
    intro _ hm
    simp only [dummyLoopMod0, List.mem_singleton] at hm
    subst hm; t_kernel_rfl
  obtain ⟨hu, hfns⟩ := leanqbe0Compile_sound_layout (Γ := loopEnv)
    loop_compile_ok (by t_kernel_rfl) hnd hnoloc
    (fun _ h => nomatch h) loop_small hbd (fun _ h => nomatch h) loop_wp0
  obtain ⟨hdef, hspec⟩ := hfns dummySumToFn0 (by simp [dummyLoopMod0])
  have hdef₀ : x64ScalarTarget.Defined loopHost "sumto" := hdef
  have hspec₀ : x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) loopHost "sumto"
      (loopEnv "sumto" [i64] [i64]) ((lookupBound0 loopBounds 0).getD 0) 0 := hspec
  have hspec_eq : loopEnv "sumto" [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ =>
        let sum := Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
          (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y))
        Q (sum args.1.toNat args.1 0#64, ()) m) := by
    funext args m Q X
    simp only [loopEnv, i64, sumAcc64_eq_natRec]
  rw [hspec_eq] at hspec₀
  exact ⟨hu, leanqbe0Compile_printAsm0 loop_compile_ok, hdef₀, hspec₀⟩

theorem loop_ok :
    ∃ (dirs : List Dir0) (ms : UInt32)
      (hsmall : x64ScalarProgSmall
        (toAmd64Program (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs ++
          dummyLoopMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "sumto" else s!"sym_{g.toNat}"))) = true)
      (bound : Nat),
      leanqbe0Compile dummyLoopMod0 = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs ++
          dummyLoopMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "sumto" else s!"sym_{g.toNat}")))
        hsmall
      x64ScalarTarget.LabelsUnique h ∧
      printAsm0 (toAmd64Program
          (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs) =
        Kraken.X64.toATT (toAmd64Program
          (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs) ∧
      x64ScalarTarget.Defined h "sumto" ∧
      x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) h "sumto"
        (fun args m Q _ =>
          let sum := Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
            (fun _ a => a) (fun _ ih y a => ih (y - 1#64) (a + y))
          Q (sum args.1.toNat args.1 0#64, ()) m)
        bound 0 :=
  ⟨loopDirs, loopMaxSl, loop_small, (lookupBound0 loopBounds 0).getD 0,
    loop_compile_ok, of_decide_eq_true (by t_kernel_rfl), loop_host_ok⟩

theorem loop_exec5 :
    ∃ (dirs : List Dir0) (ms : UInt32)
      (hsmall : x64ScalarProgSmall
        (toAmd64Program (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs ++
          dummyLoopMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "sumto" else s!"sym_{g.toNat}"))) = true)
      (bound : Nat),
      leanqbe0Compile dummyLoopMod0 = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program (fun id => if id == 0 then "sumto" else s!"sym_{id.toNat}") dirs ++
          dummyLoopMod0.exits.map
            (fun g => x64Frame.label (if g == 0 then "sumto" else s!"sym_{g.toNat}")))
        hsmall
      Eventually (x64ScalarMach.step h)
        (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 15#64)
        (x64ScalarMach.mkState
          (x64ScalarInit.initState (as := [i64]) bound [] (5#64, ()))
          (x64ScalarMach.labelAddr h "sumto")) :=
  ⟨loopDirs, loopMaxSl, loop_small, (lookupBound0 loopBounds 0).getD 0,
    loop_compile_ok, of_decide_eq_true (by t_kernel_rfl),
    TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit loopHost loop_host_ok.2.2.2 [] (5#64, ())
      15#64 (of_decide_eq_true (by t_kernel_rfl)) (by decide) (by decide)
      (Q := fun r _ => r = (15#64, ())) (by decide) (fun _ _ h => h)⟩

/-! ## 3. Bridged `Frontend.C0.TFlatFn` Two-Function Pipeline (`c0_add_one`, `c0_add_two`) -/

private def c0AddOneTf : Frontend.C0.TFlatFn :=
  { name := "c0_add_one"
    as := [i64]
    rs := [i64]
    flat := .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ())) }

private def c0AddTwoTf : Frontend.C0.TFlatFn :=
  { name := "c0_add_two"
    as := [i64]
    rs := [i64]
    flat :=
      .call "c0_add_one" (as := [i64]) [i64] (.var 0, ())
        (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (.var 0, ()))) }

private def c0Tfs : List Frontend.C0.TFlatFn := [c0AddOneTf, c0AddTwoTf]

private def c0Mod : Module :=
  { fns := c0Tfs.map Frontend.C0.TFlatFn.toFn, externs := [], exits := [] }

private def c0BridgePair : TFlatModule0 × List (Sym × Sym0) :=
  match ofTFlatModule c0Tfs [] [] with
  | .ok p => p
  | .error _ => ({ fns := [], externs := [], exits := [] }, [])

private def c0Mod0 : TFlatModule0 := c0BridgePair.1
private def c0Tbl : List (Sym × Sym0) := c0BridgePair.2

private def c0Dirs : List Dir0 :=
  match leanqbe0Compile c0Mod0 with
  | .ok dirs _ => dirs
  | .err _ _ => []

private def c0MaxSl : UInt32 :=
  match leanqbe0Compile c0Mod0 with
  | .ok _ ms => ms
  | .err _ _ => 0

private def c0Bounds : List (Sym0 × Nat) :=
  (c0Mod0.computeBounds0 [] 0).getD []

private theorem c0_bridge_ok : ofTFlatModule c0Tfs [] [] = .ok (c0Mod0, c0Tbl) := by
  t_kernel_rfl

private theorem c0_compile_ok : leanqbe0Compile c0Mod0 = .ok c0Dirs c0MaxSl := by
  t_kernel_rfl

private theorem c0_bounds_ok : c0Mod0.computeBounds0 [] 0 = some c0Bounds := by
  t_kernel_rfl

private theorem c0_small :
    x64ScalarProgSmall (toAmd64Program (symNameOf c0Tbl) c0Dirs ++ []) = true := by
  t_kernel_rfl

private def c0Env : Env := fun nm as rs =>
  match nm, as, rs with
  | "c0_add_one", [.bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + 1#64, ()) m
  | "c0_add_two", [.bits 64], [.bits 64] => fun args m Q _ => Q (args.1 + 1#64 + 1#64, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem c0_moduleOk : ModuleOk c0Env c0Mod := by
  refine Module.moduleOk_of_checkAcyclic (by t_kernel_rfl) (fun fn hmem => ?_)
    (fun fn hmem => ?_)
  · simp only [c0Mod, c0Tfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Frontend.C0.TFlatFn.toFn_wf c0AddOneTf
    · exact Frontend.C0.TFlatFn.toFn_wf c0AddTwoTf
  · simp only [c0Mod, c0Tfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · change ∀ (xs : Tup Val [i64]) m (Q : Post [i64]) X,
        c0Env "c0_add_one" [i64] [i64] xs m Q X →
        Func.wp c0Env c0AddOneTf.toFn.body xs m Q X
      intro xs m Q X hΓ
      rcases xs with ⟨a, ⟨⟩⟩
      dsimp only [c0Env] at hΓ
      dsimp only [c0AddOneTf, Frontend.C0.TFlatFn.toFn, Func.wp, denoteFunc]
      have hden : denote Val Cont
          (TFlat.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (Arg.var 0, ())) : TFlat [i64])
          (pushTup (f := Val) (as := [i64]) (a, ()) []) [] =
          (Expr.let_ (op2 (.add i64) (.var a) (.imm 1#64))
            (fun xs => Expr.ret (Arg.var xs.1, ())) : Expr Val Cont [i64]) := rfl
      rw [hden]
      dsimp only [wp, Op.wp, OpCode.wp, op2, lift2, vals, Arg.val]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
      exact hΓ
    · change ∀ (xs : Tup Val [i64]) m (Q : Post [i64]) X,
        c0Env "c0_add_two" [i64] [i64] xs m Q X →
        Func.wp c0Env c0AddTwoTf.toFn.body xs m Q X
      intro xs m Q X hΓ
      rcases xs with ⟨a, ⟨⟩⟩
      dsimp only [c0Env] at hΓ
      dsimp only [c0AddTwoTf, Frontend.C0.TFlatFn.toFn, Func.wp, denoteFunc]
      have hden : denote Val Cont
          (TFlat.call "c0_add_one" (as := [i64]) [i64] (Arg.var 0, ())
            (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (Arg.var 0, ()))) : TFlat [i64])
          (pushTup (f := Val) (as := [i64]) (a, ()) []) [] =
          (Expr.call "c0_add_one" (as := [i64]) (bs := [i64]) (Arg.var a, ()) (fun xs =>
            denote Val Cont (.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (Arg.var 0, ())))
              (pushTup (f := Val) (as := [i64]) xs [⟨i64, a⟩]) []) : Expr Val Cont [i64]) :=
        rfl
      rw [hden]
      dsimp only [wp, vals, Arg.val]
      refine ⟨fun r m' => r = (a + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False, ⟨rfl, rfl⟩,
        fun r m' ⟨hr, hm⟩ => ?_, fun _ _ _ _ hf => hf.elim⟩
      subst hr; subst hm
      have hden2 : denote Val Cont
          (TFlat.let_ (op2 (.add i64) (.var 0) (.imm 1#64)) (.ret (Arg.var 0, ())) : TFlat [i64])
          (pushTup (f := Val) (as := [i64]) (a + 1#64, ()) [⟨i64, a⟩]) [] =
          (Expr.let_ (op2 (.add i64) (.var (a + 1#64)) (.imm 1#64))
            (fun xs => Expr.ret (Arg.var xs.1, ())) : Expr Val Cont [i64]) := rfl
      rw [hden2]
      dsimp only [wp, Op.wp, OpCode.wp, op2, lift2, vals, Arg.val]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
      exact hΓ

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
  have hok_g : c0Mod0.okGuardsFull = true := by t_kernel_rfl
  have hlt32 : decide (c0Tbl.length < 2 ^ 32) = true := by t_kernel_rfl
  have hwf_c : ∀ tf ∈ c0Tfs, tf.flat.wfCheck (pushTypes tf.as []) [] = true := by
    intro tf htf
    simp only [c0Tfs, List.mem_cons, List.not_mem_nil, or_false] at htf
    rcases htf with rfl | rfl <;> t_kernel_rfl
  have hu32_c : ∀ tf ∈ c0Tfs, tflatIdxLtU32 tf.flat = true := by
    intro tf htf
    simp only [c0Tfs, List.mem_cons, List.not_mem_nil, or_false] at htf
    rcases htf with rfl | rfl <;> t_kernel_rfl
  have hacyc_c : c0Mod.checkAcyclic = true := by t_kernel_rfl
  have hnoloc_c : ∀ tf ∈ c0Tfs, symNoLocPrefix0 tf.name = true := by
    intro tf htf
    simp only [c0Tfs, List.mem_cons, List.not_mem_nil, or_false] at htf
    rcases htf with rfl | rfl <;> t_kernel_rfl
  obtain ⟨hu, hprint, hfns⟩ := bridge_leanqbe0Compile_layout (Γ := c0Env)
    c0Tfs [] [] c0_bridge_ok c0_compile_ok hok_g (of_decide_eq_true hlt32)
    hwf_c hu32_c hacyc_c List.nodup_nil (fun _ h => nomatch h)
    hnoloc_c (fun _ h => nomatch h) c0_bounds_ok (fun _ h => nomatch h)
    c0_small c0_moduleOk (fun _ h => nomatch h)
  obtain ⟨hdef, hspec⟩ := hfns c0AddTwoTf (by simp [c0Tfs])
  have hdef₀ : x64ScalarTarget.Defined c0Host "c0_add_two" := hdef
  have hspec₀ : x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) c0Host "c0_add_two"
      (Env.ofModule c0Mod c0Env "c0_add_two" [i64] [i64])
      ((lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0) 0 := hspec
  have hspec_eq : Env.ofModule c0Mod c0Env "c0_add_two" [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ => Q (args.1 + 1#64 + 1#64, ()) m) := by
    funext args m Q X
    exact propext ⟨fun h => h.2, fun h => ⟨by simp [c0Mod, c0Tfs, Module.sigs,
      Frontend.C0.TFlatFn.toFn, Fn.sig, c0AddTwoTf], h⟩⟩
  rw [hspec_eq] at hspec₀
  exact ⟨hu, hprint, hdef₀, hspec₀⟩

theorem c0_ok :
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
      leanqbe0Compile mod = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf (toAmd64Program (symNameOf tbl) dirs ++ []) hsmall
      x64ScalarTarget.LabelsUnique h ∧
      printAsm0 (toAmd64Program (symNameOf tbl) dirs) =
        Kraken.X64.toATT (toAmd64Program (symNameOf tbl) dirs) ∧
      x64ScalarTarget.Defined h "c0_add_two" ∧
      x64ScalarTarget.FnSpec (as := [i64]) (bs := [i64]) h "c0_add_two"
        (fun args m Q _ => Q (args.1 + 1#64 + 1#64, ()) m)
        bound 0 :=
  ⟨c0Mod0, c0Tbl, c0Dirs, c0MaxSl, c0_small,
    (lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0,
    c0_bridge_ok, c0_compile_ok, of_decide_eq_true (by t_kernel_rfl), c0_host_ok⟩

theorem c0_exec40 :
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
      leanqbe0Compile mod = .ok dirs ms ∧
      bound ≤ 2048 ∧
      let h := x64ScalarLayout.layoutOf (toAmd64Program (symNameOf tbl) dirs ++ []) hsmall
      Eventually (x64ScalarMach.step h)
        (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42#64)
        (x64ScalarMach.mkState
          (x64ScalarInit.initState (as := [i64]) bound [] (40#64, ()))
          (x64ScalarMach.labelAddr h "c0_add_two")) :=
  ⟨c0Mod0, c0Tbl, c0Dirs, c0MaxSl, c0_small,
    (lookupBound0 c0Bounds (lookupSymId? c0Tbl "c0_add_two").get!).getD 0,
    c0_bridge_ok, c0_compile_ok, of_decide_eq_true (by t_kernel_rfl),
    TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit c0Host c0_host_ok.2.2.2 [] (40#64, ())
      42#64 (of_decide_eq_true (by t_kernel_rfl)) (by decide) (by decide)
      (Q := fun r _ => r = (42#64, ())) (by decide) (fun _ _ h => h)⟩

/-! ## 4. Negative Guard Rejection Witnesses & Axiom Hygiene Audit -/

theorem neg_bug_a :
    (TFlat0.group [([], .hlt), ([], .hlt)] .hlt).singleBlockGroups = false := by
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
