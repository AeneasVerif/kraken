module

public import LeanQbe.T.Bedrock2.Phoas
public import LeanQbe.T.Bedrock2.Flat
public import LeanQbe.T.Bedrock2.ToT
public import LeanQbe.T.Bedrock2.FromKraken
public import LeanQbe.T.MainLemmas
public import Kraken.Bedrock2.Test.Cases
import LeanQbe.T.RegaLemmas3
import all Kraken.Separation

/-!
# End-to-End Bedrock2 Typed-PHOAS, `FromKraken`, & `Fn.mid` Verification Suite

Exercises every layer of `LeanQbe.T.Bedrock2`:
1. **`arrSum`** (typed PHOAS): `FuncB.Wf` via `t_b2_wf_reify`, `checkBFlat = true`, `toFunc_wf`,
   exact `arrSumT_spec`, and transport through real `Fn.mid` (`arrSumMid_x64_spec`,
   `arrSumMid_aarch64_spec`) on `LegalTarget.x64` and `LegalTarget.aarch64`.
2. **`scratchSwap`** (`stackalloc`): `FuncB.Wf`, `toFunc_wf`, and `FuncB.toFunc_wp_sound`.
3. **`logAndInc` & `ioMod`** (`call` + `store` + `interact`): `ModuleOkB` via
   `ModuleB.moduleOk_of_checkAcyclic` and `FuncB.toFunc_wp_sound`.
4. **`FromKraken`** (`Kraken.Bedrock2.Func` → typed PHOAS → `LeanQbe.T.Func` → `Fn.mid`):
   * Concrete end-to-end `Kraken.Bedrock2.Exec ↔ LeanQbe.T.Func.wp → Fn.mid` theorems for
     `Kraken.Bedrock2.Test.mulh` (`mulhuu` + `mul`) and `divmod` (`divu` + `remu`).
   * Exact `Func.fromKraken_toFunc_wp_iff` bridges for `sum` (`while` + `load4`), `wide`
     (`load8` + `store8`), and `absdiff` (`ite`).
   * Soundness bridges via `Func.fromKraken_toFunc_wp_sound` for `stackNested` (`stackalloc`),
     `table` (`inlinetable1/2/4/8`), `krakenCallTxFn` (`call` + `interact`), and
     `krakenStoreTxFn` (`store` + `interact`).
   * Target legality across 15 `Kraken.Bedrock2.Test` functions on both `x64` and `aarch64`.
5. **Negative checks & `#print axioms` audit** (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Bedrock2PhoasTest

open LeanQbe.T LeanQbe.T.Bedrock2 Kraken.Bedrock2.Test

private theorem bv64_mul8 (i : BitVec 64) : i * 8#64 = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem bv64_add1_toNat {i n : BitVec 64} (hlt : i.toNat < n.toNat) :
    (i + 1#64).toNat = i.toNat + 1 := by
  have hn : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem legalPost_i64_elim {P : LeanQbe.T.Post [i64]} {r : Tup Val [i64]}
    {m : Mem 64} (h : legalPost LegalTarget.x64 P r m) : P r m := by
  rcases h with ⟨⟨v, ⟨⟩⟩, heq, hp⟩
  dsimp [encodeTup] at heq
  subst heq
  exact hp

private theorem legalPost_i64_aarch64_elim {P : LeanQbe.T.Post [i64]} {r : Tup Val [i64]}
    {m : Mem 64} (h : legalPost LegalTarget.aarch64 P r m) : P r m := by
  rcases h with ⟨⟨v, ⟨⟩⟩, heq, hp⟩
  dsimp [encodeTup] at heq
  subst heq
  exact hp

private theorem legalPost_i64_2_x64_elim {P : LeanQbe.T.Post [i64, i64]}
    {r : Tup Val [i64, i64]} {m : Mem 64}
    (h : legalPost LegalTarget.x64 P r m) : P r m := by
  rcases h with ⟨⟨a, b, ⟨⟩⟩, heq, hp⟩
  dsimp [encodeTup] at heq
  subst heq
  exact hp

private theorem legalPost_i64_2_aarch64_elim {P : LeanQbe.T.Post [i64, i64]}
    {r : Tup Val [i64, i64]} {m : Mem 64}
    (h : legalPost LegalTarget.aarch64 P r m) : P r m := by
  rcases h with ⟨⟨a, b, ⟨⟩⟩, heq, hp⟩
  dsimp [encodeTup] at heq
  subst heq
  exact hp

/-! ## 1. `arrSum`: Typed PHOAS → `ToT` → `Fn.mid` (`x64` & `aarch64`) -/

/-- Sum an array of `n` 64-bit words starting at `ptr`. -/
def arrSum : FuncB [i64, i64] [i64] := fun _ (ptr, n, ()) =>
  .while_ (st := [i64, i64]) (.imm 0#64, .imm 0#64, ())
    (fun (i, _, ()) =>
      .letOp2 (.ult i64) (.var i) (.var n) fun b => .ret1 (.var b))
    (fun (i, acc, ()) =>
      .letOp2 (.mul i64) (.var i) (.imm 8#64) fun off =>
      .letOp2 (.add i64) (.var ptr) (.var off) fun addr =>
      .load i64 (.var addr) fun elem =>
      .letOp2 (.add i64) (.var acc) (.var elem) fun acc' =>
      .letOp2 (.add i64) (.var i) (.imm 1#64) fun i' =>
      .ret (.var i', .var acc', ()))
    (fun (_, acc, ()) => .ret1 (.var acc))

theorem arrSum_wf : arrSum.Wf := by t_b2_wf_reify

theorem arrSum_checkBFlat : arrSum.checkBFlat = true := rfl

theorem arrSum_noStackNoIO (V : Ty → Type) (xs : Tup V [i64, i64]) :
    (arrSum V xs).NoStackNoIO :=
  .while_ (fun _ => .let_ fun _ => .ret)
    (fun _ => .let_ fun _ => .let_ fun _ => .load fun _ => .let_ fun _ => .let_ fun _ => .ret)
    (fun _ => .ret)

/-- Lowered `LeanQbe.T` function for `arrSum`. -/
def arrSumT : Func [i64, i64] [i64] := arrSum.toFunc

theorem arrSumT_wf : arrSumT.Wf := FuncB.toFunc_wf arrSum_wf

theorem arrSum_wp {ext : ExtSpecB} {Γ : EnvB} {B : Nat}
    {ptr n : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    {t : TraceB} {m : Mem 64}
    (hlen : n.toNat = xs.length) (hm : (array64 ptr xs ⋆ R) m) :
    FuncB.wp ext Γ arrSum B (ptr, n, ()) t m
      (fun (res, ()) t' m' => res = xs.foldl (· + ·) 0#64 ∧ t' = t ∧ m' = m) := by
  dsimp only [FuncB.wp, arrSum]
  refine Cmd.wp_while_nat (st := [i64, i64]) _ _ _ _
    (fun r (i, acc, ()) t' m' =>
      i.toNat ≤ xs.length ∧ r = xs.length - i.toNat ∧
      acc = (xs.take i.toNat).foldl (· + ·) 0#64 ∧ t' = t ∧ m' = m)
    (n₀ := xs.length) (by simp [vals, Arg.val]) ?_
  rintro r ⟨i, acc, ⟨⟩⟩ t' m' ⟨hle, rfl, hacc, ht, hm'⟩
  subst ht; subst hm'
  dsimp only [Cmd.wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat]
  constructor
  · intro hlt
    have hi : i.toNat < xs.length := by
      rw [BitVec.ult] at hlt; simp only [decide_eq_true_eq] at hlt; omega
    have hload : loadVal m' i64 (ptr + lift2 (· * ·) (· && ·) i64 i 8#64) = some xs[i.toNat] := by
      dsimp only [lift2]; rw [bv64_mul8]; exact loadVal_array64 hi hm
    refine ⟨xs[i.toNat], hload, ?_⟩
    dsimp only [Cmd.wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat]
    have hadd1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (n := n) (by omega)
    refine ⟨xs.length - (i.toNat + 1), by omega, by omega, by rw [hadd1], ?_, rfl, rfl⟩
    rw [hadd1, List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons,
      List.foldl_nil, hacc]
  · intro hge
    have heq : i.toNat = xs.length := by
      rw [BitVec.ult] at hge; simp only [decide_eq_false_iff_not] at hge; omega
    refine ⟨?_, rfl, rfl⟩
    rw [hacc, heq, List.take_length]

/-- Source-level `LeanQbe.T.Func.wp` specification of lowered `arrSumT`. -/
theorem arrSumT_spec {Γ : Env} {X : XPost} {ptr n : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : n.toNat = xs.length) (hm : (array64 ptr xs ⋆ R) m) :
    Func.wp Γ arrSumT (ptr, n, ()) m
      (fun (res, ()) m' => res = xs.foldl (· + ·) 0#64 ∧ m' = m) X := by
  rw [arrSumT, FuncB.toFunc_wp_iff (fun xs => arrSum_noStackNoIO Val xs)]
  exact ⟨0, Cmd.wp_mono (fun (_, ()) _ _ h => ⟨h.1, h.2.2⟩) _ [] m (arrSum_wp hlen hm)⟩

def arrSumFn : Fn := ⟨"arrSum", [i64, i64], [i64], arrSumT⟩

theorem arrSumFn_wf : arrSumFn.Wf := arrSumT_wf

theorem arrSumFn_supports_x64 :
    (arrSumFn.earlyOpt).body.supportsSource LegalTarget.x64 = true := by t_kernel_rfl

theorem arrSumFn_supports_aarch64 :
    (arrSumFn.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by t_kernel_rfl

theorem arrSumMid_x64_wf : (arrSumFn.mid LegalTarget.x64).Wf :=
  fn_mid_wf arrSumFn_wf

theorem arrSumMid_aarch64_wf : (arrSumFn.mid LegalTarget.aarch64).Wf :=
  fn_mid_wf arrSumFn_wf

/-- End-to-end verified `Fn.mid LegalTarget.x64` specification of `arrSum`. -/
theorem arrSumMid_x64_spec {Γ : Env} {X : XPost} {ptr n : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : n.toNat = xs.length) (hm : (array64 ptr xs ⋆ R) m) :
    Func.wp (legalEnv LegalTarget.x64 Γ) (arrSumFn.mid LegalTarget.x64).body
      (ptr, n, ()) m
      (fun (res, ()) m' => res = xs.foldl (· + ·) 0#64 ∧ m' = m) (legalXPost LegalTarget.x64 X) :=
  fn_mid_spec (lt := LegalTarget.x64) arrSumFn_wf arrSumFn_supports_x64 Γ rfl
    (fun _ _ h => legalPost_i64_elim h) (fun _ _ _ _ h => h) (arrSumT_spec hlen hm)

/-- End-to-end verified `Fn.mid LegalTarget.aarch64` specification of `arrSum`. -/
theorem arrSumMid_aarch64_spec {Γ : Env} {X : XPost} {ptr n : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : n.toNat = xs.length) (hm : (array64 ptr xs ⋆ R) m) :
    Func.wp (legalEnv LegalTarget.aarch64 Γ) (arrSumFn.mid LegalTarget.aarch64).body
      (ptr, n, ()) m
      (fun (res, ()) m' => res = xs.foldl (· + ·) 0#64 ∧ m' = m)
      (legalXPost LegalTarget.aarch64 X) :=
  fn_mid_spec (lt := LegalTarget.aarch64) arrSumFn_wf arrSumFn_supports_aarch64 Γ rfl
    (fun _ _ h => legalPost_i64_aarch64_elim h) (fun _ _ _ _ h => h) (arrSumT_spec hlen hm)

/-! ## 2. `scratchSwap`: `stackalloc` + `store` + `load` + `toFunc_wp_sound` -/

/-- Swap two 64-bit cells at `pa` and `pb` via an 8-byte stack-allocated scratch slot. -/
def scratchSwap : FuncB [i64, i64] [] := fun _ (pa, pb, ()) =>
  .stackalloc 8 fun tmp =>
    .load i64 (.var pa) fun va =>
    .store (.var va) (.var tmp) <|
    .load i64 (.var pb) fun vb =>
    .store (.var vb) (.var pa) <|
    .load i64 (.var tmp) fun vtmp =>
    .store (.var vtmp) (.var pb) .skip

theorem scratchSwap_wf : scratchSwap.Wf := by t_b2_wf_reify

theorem scratchSwap_checkBFlat : scratchSwap.checkBFlat = true := rfl

def scratchSwapFn : Fn := ⟨"scratchSwap", [i64, i64], [], scratchSwap.toFunc⟩

theorem scratchSwapFn_wf : scratchSwapFn.Wf := FuncB.toFunc_wf scratchSwap_wf

theorem scratchSwapFn_supports_x64 :
    (scratchSwapFn.earlyOpt).body.supportsSource LegalTarget.x64 = true := by t_kernel_rfl

theorem scratchSwapFn_supports_aarch64 :
    (scratchSwapFn.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by t_kernel_rfl

theorem scratchSwapMid_x64_wf : (scratchSwapFn.mid LegalTarget.x64).Wf :=
  fn_mid_wf scratchSwapFn_wf

theorem scratchSwapMid_aarch64_wf : (scratchSwapFn.mid LegalTarget.aarch64).Wf :=
  fn_mid_wf scratchSwapFn_wf

theorem scratchSwap_wp {ext : ExtSpecB} {Γ : EnvB} {B : Nat}
    {pa pb a b : BitVec 64} {R : Mem 64 → Prop} {t : TraceB} {m : Mem 64}
    (hB : 8 ≤ B) (hm : (cell64 pa a ⋆ cell64 pb b ⋆ R) m) :
    FuncB.wp ext Γ scratchSwap B (pa, pb, ()) t m
      (fun () t' m' => t' = t ∧ (cell64 pa b ⋆ cell64 pb a ⋆ R) m') := by
  dsimp only [FuncB.wp, scratchSwap, Cmd.wp]
  refine ⟨hB, fun tmp mStack mComb hany hsp => ?_⟩
  obtain ⟨v0, hv0⟩ := anybytes8_exists_cell64 hany
  have hm0 : ((cell64 pa a ⋆ cell64 pb b ⋆ R) ⋆ cell64 tmp v0) mComb :=
    split_sep hsp hm hv0
  have hloadA : loadVal mComb i64 pa = some a :=
    loadVal_cell64 (R := cell64 pb b ⋆ R ⋆ cell64 tmp v0) (sep_cast hm0 (by ac_rfl))
  refine ⟨a, hloadA, ?_⟩
  obtain ⟨hok1, hm1⟩ := store_cell64 (a := tmp) (v0 := v0) a (R := cell64 pa a ⋆ cell64 pb b ⋆ R)
    (sep_cast hm0 (by ac_rfl))
  refine ⟨hok1, ?_⟩
  have hloadB : loadVal (storeMem mComb i64 tmp a) i64 pb = some b :=
    loadVal_cell64 (R := cell64 pa a ⋆ R ⋆ cell64 tmp a) (sep_cast hm1 (by ac_rfl))
  refine ⟨b, hloadB, ?_⟩
  obtain ⟨hok2, hm2⟩ := store_cell64 (a := pa) (v0 := a) b (R := cell64 pb b ⋆ R ⋆ cell64 tmp a)
    (sep_cast hm1 (by ac_rfl))
  refine ⟨hok2, ?_⟩
  have hloadT : loadVal (storeMem (storeMem mComb i64 tmp a) i64 pa b) i64 tmp = some a :=
    loadVal_cell64 (R := cell64 pa b ⋆ cell64 pb b ⋆ R) (sep_cast hm2 (by ac_rfl))
  refine ⟨a, hloadT, ?_⟩
  obtain ⟨hok3, hm3⟩ := store_cell64 (a := pb) (v0 := b) a (R := cell64 pa b ⋆ R ⋆ cell64 tmp a)
    (sep_cast hm2 (by ac_rfl))
  refine ⟨hok3, ?_⟩
  have hm4 : ((cell64 pa b ⋆ cell64 pb a ⋆ R) ⋆ cell64 tmp a) _ := sep_cast hm3 (by ac_rfl)
  rcases hm4 with ⟨mSmall', mStack', hu, hi, hSmall', hStack'⟩
  exact ⟨mSmall', mStack', cell64_anybytes8 hStack', ⟨hu, hi⟩, rfl, hSmall'⟩

theorem scratchSwapT_spec {ext : ExtSpecB} {Γ : EnvB}
    {pa pb a b : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hm : (cell64 pa a ⋆ cell64 pb b ⋆ R) m) :
    Func.wp (Env.ofBedrock2Sound LowerCfg.default ext Γ) scratchSwap.toFunc (pa, pb, ()) m
      (fun () m' => (cell64 pa b ⋆ cell64 pb a ⋆ R) m') X := by
  refine FuncB.toFunc_wp_sound (ext := ext) (Γ := Γ) (f := scratchSwap) (B := 8) (by decide)
    (pa, pb, ()) [] m X ?_ (scratchSwap_wp (Nat.le_refl 8) hm) LowerCfg.default
  intro _ _ _ h
  exact h.2

/-! ## 3. `logAndInc` & `ioMod`: `call` + `store` + `interact` + `ModuleOkB` -/

/-- Pure helper incremented by 1. -/
def incB : FuncB [i64] [i64] := fun _ (x, ()) =>
  .letOp2 (.add i64) (.var x) (.imm 1#64) fun y => .ret1 (.var y)

/-- I/O wrapper calling `"inc"`, storing at `ptr`, and running `"tx_word"` interaction. -/
def logAndInc : FuncB [i64, i64] [i64] := fun _ (ptr, x, ()) =>
  .call1 (as := [i64]) (b := i64) "inc" (.var x, ()) fun y =>
  .store (.var y) (.var ptr) <|
  .interact1 (as := [i64]) (b := i64) "tx_word" (.var ptr, ()) fun rc =>
  .ret1 (.var rc)

theorem incB_wf : incB.Wf := by t_b2_wf_reify
theorem incB_wf_tac : incB.Wf := by t_b2_wf_tac
theorem logAndInc_wf : logAndInc.Wf := by t_b2_wf_reify
theorem logAndInc_checkBFlat : logAndInc.checkBFlat = true := rfl

def extTx : ExtSpecB := fun _ mGive action as bs args post =>
  ∃ (h1 : as = [i64]) (h2 : bs = [i64]),
    action = "tx_word" ∧
    ∃ v : BitVec 64,
      cell64 (h1 ▸ args).1 v mGive ∧
      ∀ mRec : Mem 64, cell64 (h1 ▸ args).1 (v ^^^ 1#64) mRec →
        post mRec (h2 ▸ (v, ()))

def ioEnv : EnvB := fun f as bs _ args t m Q =>
  match f, as, bs with
  | "inc", [.bits 64], [.bits 64] => Q (args.1 + 1#64, ()) t m
  | "logAndInc", [.bits 64, .bits 64], [.bits 64] =>
      ∃ (v0 : BitVec 64) (R : Mem 64 → Prop),
        (cell64 args.1 v0 ⋆ R) m ∧
        ∀ mGive mRec m',
          cell64 args.1 (args.2.1 + 1#64) mGive →
          cell64 args.1 ((args.2.1 + 1#64) ^^^ 1#64) mRec →
          (cell64 args.1 ((args.2.1 + 1#64) ^^^ 1#64) ⋆ R) m' →
          Q (args.2.1 + 1#64, ())
            (⟨[i64], [i64], mGive, "tx_word", (args.1, ()), mRec, (args.2.1 + 1#64, ())⟩ :: t)
            m'
  | _, _, _ => False

def ioMod : ModuleB where
  fns := [⟨"inc", [i64], [i64], incB⟩, ⟨"logAndInc", [i64, i64], [i64], logAndInc⟩]

theorem incB_wp {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {x : BitVec 64} {t : TraceB}
    {m : Mem 64} {Q : PostB [i64]} (hQ : Q (x + 1#64, ()) t m) :
    FuncB.wp ext Γ incB B (x, ()) t m Q := hQ

theorem logAndInc_wp {B : Nat} {ptr x v0 : BitVec 64} {R : Mem 64 → Prop}
    {t : TraceB} {m : Mem 64} {Q : PostB [i64]}
    (hm : (cell64 ptr v0 ⋆ R) m)
    (hQ : ∀ mGive mRec m',
      cell64 ptr (x + 1#64) mGive →
      cell64 ptr ((x + 1#64) ^^^ 1#64) mRec →
      (cell64 ptr ((x + 1#64) ^^^ 1#64) ⋆ R) m' →
      Q (x + 1#64, ())
        (⟨[i64], [i64], mGive, "tx_word", (ptr, ()), mRec, (x + 1#64, ())⟩ :: t) m') :
    FuncB.wp extTx ioEnv logAndInc B (ptr, x, ()) t m Q := by
  dsimp only [FuncB.wp, logAndInc, Cmd.wp]
  refine ⟨fun (y, ()) t₁ m₁ => y = x + 1#64 ∧ t₁ = t ∧ m₁ = m, ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨y, ⟨⟩⟩ t₁ m₁ ⟨rfl, ht, hm'⟩
  subst ht; subst hm'
  dsimp only [Cmd.wp, vals, Arg.val]
  obtain ⟨hok, hm1⟩ := store_cell64 (x + 1#64) hm
  refine ⟨hok, ?_⟩
  have hm1' : (R ⋆ cell64 ptr (x + 1#64)) (storeMem m₁ i64 ptr (x + 1#64)) :=
    sep_cast hm1 (by ac_rfl)
  rcases hm1' with ⟨mKeep, mGive, hu, hi, hKeep, hGive⟩
  refine ⟨mKeep, mGive,
    fun mRec res => cell64 ptr ((x + 1#64) ^^^ 1#64) mRec ∧ res = (x + 1#64, ()),
    ⟨hu, hi⟩, ⟨rfl, rfl, rfl, x + 1#64, hGive, fun mRec hmRec => ⟨hmRec, rfl⟩⟩, ?_⟩
  rintro mRec _ ⟨hmRec, rfl⟩ m' hsp'
  exact hQ mGive mRec m' hGive hmRec (sep_cast (split_sep hsp' hKeep hmRec) (by ac_rfl))

theorem ioMod_ok : ModuleOkB extTx ioEnv ioMod := by
  refine ModuleB.moduleOk_of_checkAcyclic rfl ?_ ?_
  · intro fn hfn
    simp only [ioMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl
    · exact incB_wf
    · exact logAndInc_wf
  · intro fn hfn B xs t m Q hspec
    simp only [ioMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl
    · exact incB_wp hspec
    · rcases xs with ⟨ptr, x, ⟨⟩⟩
      rcases hspec with ⟨v0, R, hm, hQ⟩
      exact logAndInc_wp hm hQ

theorem logAndIncT_wf : (logAndInc.toFunc).Wf := FuncB.toFunc_wf logAndInc_wf

theorem logAndIncT_spec {ptr x v0 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hm : (cell64 ptr v0 ⋆ R) m) :
    Func.wp (Env.ofBedrock2Sound LowerCfg.default extTx ioEnv) logAndInc.toFunc (ptr, x, ()) m
      (fun (res, ()) m' => res = x + 1#64 ∧ (cell64 ptr ((x + 1#64) ^^^ 1#64) ⋆ R) m') X := by
  refine FuncB.toFunc_wp_sound (ext := extTx) (Γ := ioEnv) (f := logAndInc) (B := 0) (by decide)
    (ptr, x, ()) [] m X ?_
    (logAndInc_wp (Q := fun (res, ()) _ m' =>
      res = x + 1#64 ∧ (cell64 ptr ((x + 1#64) ^^^ 1#64) ⋆ R) m')
      hm (fun _ _ _ _ _ hm' => ⟨rfl, hm'⟩))
    LowerCfg.default
  rintro ⟨res, ⟨⟩⟩ _ m' h
  exact h

/-! ## 4. `FromKraken`: Real `Kraken.Bedrock2` Programs → `LeanQbe.T.Func` → `Fn.mid` -/

private theorem envB_ofTEnv_empty_iff_ofKraken_empty (ext : Kraken.Bedrock2.ExtSpec 64)
    (X : XPost) :
    ∀ sym as bs B args tb m P,
      EnvB.ofTEnv (fun _ _ _ _ _ _ _ => False) X sym as bs B args tb m P ↔
        EnvB.ofKraken ext [] sym as bs B args tb m P := by
  intro sym as bs B args tb m P
  constructor
  · rintro ⟨_, _, h, _⟩; exact h.elim
  · rintro ⟨_, _, _, _, _, hlk, _⟩; cases hlk

def krakenEmptyEnv : Env := fun _ _ _ _ _ _ _ => False

/-- Lowered `mulh` from `Kraken.Bedrock2.Test.mulh`. -/
def mulhBf : BFlat [i64, i64] :=
  (Func.toBFlat? mulh.2).get (rfl : (Func.toBFlat? mulh.2).isSome = true)

def mulhFb : FuncB [i64, i64] [i64, i64] :=
  denoteFuncB (as := [i64, i64]) mulhBf

theorem mulh_toBFlat : Func.toBFlat? mulh.2 = some mulhBf := rfl
theorem mulh_noStackNoIO : mulhBf.noStackNoIO = true := rfl
theorem mulh_fromKraken : Func.fromKraken mulh.2 = some mulhFb := rfl

def mulhT : Func [i64, i64] [i64, i64] := mulhFb.toFunc

theorem mulhT_wf : mulhT.Wf := Func.fromKraken_toFunc_wf mulh_fromKraken

def mulhFn : Fn := ⟨"mulh", [i64, i64], [i64, i64], mulhT⟩

theorem mulhFn_wf : mulhFn.Wf := mulhT_wf

theorem mulhFn_supports_x64 :
    (mulhFn.earlyOpt).body.supportsSource LegalTarget.x64 = true := by t_kernel_rfl

theorem mulhFn_supports_aarch64 :
    (mulhFn.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by t_kernel_rfl

theorem mulhMid_x64_wf : (mulhFn.mid LegalTarget.x64).Wf := fn_mid_wf mulhFn_wf
theorem mulhMid_aarch64_wf : (mulhFn.mid LegalTarget.aarch64).Wf := fn_mid_wf mulhFn_wf

theorem mulh_toFunc_wp_iff {ext : Kraken.Bedrock2.ExtSpec 64} {X : XPost}
    {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : LeanQbe.T.Post [i64, i64]} :
    LeanQbe.T.Func.wp krakenEmptyEnv mulhT xs m Q X ↔
      Kraken.Bedrock2.Exec ext [] 0 mulh.2.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany
          (mulh.2.params.zip (tupToList (n := 2) xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' mulh.2.rets = some retvs ∧
            ∃ resTup : Tup Val [i64, i64],
              tupToList (n := 2) resTup = retvs ∧ Q resTup m' :=
  Func.fromKraken_toFunc_wp_iff mulh_toBFlat mulh_noStackNoIO
    (envB_ofTEnv_empty_iff_ofKraken_empty ext X)

theorem mulh_exec {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env} {B : Nat}
    (x y : BitVec 64) (m : Mem 64) :
    Kraken.Bedrock2.Exec ext e B mulh.2.body [] m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (mulh.2.params.zip [x, y]))
      fun _ m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' mulh.2.rets = some retvs ∧
          ∃ resTup : Tup Val [i64, i64],
            tupToList (n := 2) resTup = retvs ∧
            resTup = (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y, ()) ∧
            m' = m := by
  dsimp [mulh]
  refine .seq _ _ _ _ _ _ _
    (fun t1 m1 l1 => t1 = [] ∧ m1 = m ∧ l1 =
      (((∅ : Kraken.Bedrock2.Locals 64).insertMany [("x", x), ("y", y)]).insert "h"
        (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)))) ?_ ?_
  · refine .set "h" _ B [] m _ _ _ ?_ ⟨rfl, rfl, rfl⟩
    simp [Kraken.Bedrock2.Expr.eval, Kraken.Bedrock2.interpBinop,
      Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
  · rintro t1 m1 l1 ⟨rfl, rfl, rfl⟩
    refine .set "l" _ B [] _ _ _ (x * y) ?_ ?_
    · simp [Kraken.Bedrock2.Expr.eval, Kraken.Bedrock2.interpBinop,
        Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
    · refine ⟨[BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y], ?_,
        (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y, ()), ?_, rfl, rfl⟩
      · simp [Kraken.Bedrock2.getMany,
          Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
      · simp [tupToList]

theorem mulhT_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp krakenEmptyEnv mulhT (x, y, ()) m
      (fun res m' =>
        res = (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y, ()) ∧ m' = m) X :=
  (mulh_toFunc_wp_iff (ext := fun _ _ _ _ _ => False)).2 (mulh_exec x y m)

/-- End-to-end verified `Fn.mid LegalTarget.x64` spec for `Kraken.Bedrock2.Test.mulh`. -/
theorem mulhMid_x64_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp (legalEnv LegalTarget.x64 krakenEmptyEnv) (mulhFn.mid LegalTarget.x64).body
      (x, y, ()) m
      (fun res m' =>
        res = (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y, ()) ∧ m' = m)
      (legalXPost LegalTarget.x64 X) :=
  fn_mid_spec (lt := LegalTarget.x64) mulhFn_wf mulhFn_supports_x64 krakenEmptyEnv rfl
    (fun _ _ h => legalPost_i64_2_x64_elim h) (fun _ _ _ _ h => h) (mulhT_spec x y m)

/-- End-to-end verified `Fn.mid LegalTarget.aarch64` spec for `Kraken.Bedrock2.Test.mulh`. -/
theorem mulhMid_aarch64_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp (legalEnv LegalTarget.aarch64 krakenEmptyEnv) (mulhFn.mid LegalTarget.aarch64).body
      (x, y, ()) m
      (fun res m' =>
        res = (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64), x * y, ()) ∧ m' = m)
      (legalXPost LegalTarget.aarch64 X) :=
  fn_mid_spec (lt := LegalTarget.aarch64) mulhFn_wf mulhFn_supports_aarch64 krakenEmptyEnv rfl
    (fun _ _ h => legalPost_i64_2_aarch64_elim h) (fun _ _ _ _ h => h) (mulhT_spec x y m)

/-- Lowered `divmod` (`divu` + `remu`) from `Kraken.Bedrock2.Test.divmod`. -/
def divmodBf : BFlat [i64, i64] :=
  (Func.toBFlat? divmod.2).get (rfl : (Func.toBFlat? divmod.2).isSome = true)

def divmodFb : FuncB [i64, i64] [i64, i64] :=
  denoteFuncB (as := [i64, i64]) divmodBf

theorem divmod_toBFlat : Func.toBFlat? divmod.2 = some divmodBf := rfl
theorem divmod_noStackNoIO : divmodBf.noStackNoIO = true := rfl
theorem divmod_fromKraken : Func.fromKraken divmod.2 = some divmodFb := rfl

def divmodT : Func [i64, i64] [i64, i64] := divmodFb.toFunc

theorem divmodT_wf : divmodT.Wf := Func.fromKraken_toFunc_wf divmod_fromKraken

def divmodFn : Fn := ⟨"divmod", [i64, i64], [i64, i64], divmodT⟩

theorem divmodFn_wf : divmodFn.Wf := divmodT_wf

theorem divmodFn_supports_x64 :
    (divmodFn.earlyOpt).body.supportsSource LegalTarget.x64 = true := by t_kernel_rfl

theorem divmodFn_supports_aarch64 :
    (divmodFn.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by t_kernel_rfl

theorem divmodMid_x64_wf : (divmodFn.mid LegalTarget.x64).Wf := fn_mid_wf divmodFn_wf
theorem divmodMid_aarch64_wf : (divmodFn.mid LegalTarget.aarch64).Wf := fn_mid_wf divmodFn_wf

theorem divmod_toFunc_wp_iff {ext : Kraken.Bedrock2.ExtSpec 64} {X : XPost}
    {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : LeanQbe.T.Post [i64, i64]} :
    LeanQbe.T.Func.wp krakenEmptyEnv divmodT xs m Q X ↔
      Kraken.Bedrock2.Exec ext [] 0 divmod.2.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany
          (divmod.2.params.zip (tupToList (n := 2) xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' divmod.2.rets = some retvs ∧
            ∃ resTup : Tup Val [i64, i64],
              tupToList (n := 2) resTup = retvs ∧ Q resTup m' :=
  Func.fromKraken_toFunc_wp_iff divmod_toBFlat divmod_noStackNoIO
    (envB_ofTEnv_empty_iff_ofKraken_empty ext X)

theorem divmod_exec {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env} {B : Nat}
    (x y : BitVec 64) (m : Mem 64) :
    Kraken.Bedrock2.Exec ext e B divmod.2.body [] m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (divmod.2.params.zip [x, y]))
      fun _ m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' divmod.2.rets = some retvs ∧
          ∃ resTup : Tup Val [i64, i64],
            tupToList (n := 2) resTup = retvs ∧
            resTup = ((if y = 0#64 then BitVec.allOnes 64 else x / y), x % y, ()) ∧
            m' = m := by
  dsimp [divmod]
  refine .seq _ _ _ _ _ _ _
    (fun t1 m1 l1 => t1 = [] ∧ m1 = m ∧ l1 =
      (((∅ : Kraken.Bedrock2.Locals 64).insertMany [("x", x), ("y", y)]).insert "q"
        (if y = 0#64 then BitVec.allOnes 64 else x / y)))
    ?_ ?_
  · refine .set "q" _ B [] m _ _ _ ?_ ⟨rfl, rfl, rfl⟩
    simp [Kraken.Bedrock2.Expr.eval, Kraken.Bedrock2.interpBinop,
      Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
  · rintro t1 m1 l1 ⟨rfl, rfl, rfl⟩
    refine .set "r" _ B [] _ _ _ (x % y) ?_ ?_
    · simp [Kraken.Bedrock2.Expr.eval, Kraken.Bedrock2.interpBinop,
        Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
    · refine ⟨[(if y = 0#64 then BitVec.allOnes 64 else x / y), x % y], ?_,
        ((if y = 0#64 then BitVec.allOnes 64 else x / y), x % y, ()), ?_, rfl, rfl⟩
      · simp [Kraken.Bedrock2.getMany,
          Std.ExtHashMap.insertMany_cons, Std.ExtHashMap.insertMany_nil]
      · simp [tupToList]

theorem divmodT_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp krakenEmptyEnv divmodT (x, y, ()) m
      (fun res m' =>
        res = ((if y = 0#64 then BitVec.allOnes 64 else x / y), x % y, ()) ∧ m' = m) X :=
  (divmod_toFunc_wp_iff (ext := fun _ _ _ _ _ => False)).2 (divmod_exec x y m)

/-- End-to-end verified `Fn.mid LegalTarget.x64` spec for `Kraken.Bedrock2.Test.divmod`. -/
theorem divmodMid_x64_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp (legalEnv LegalTarget.x64 krakenEmptyEnv) (divmodFn.mid LegalTarget.x64).body
      (x, y, ()) m
      (fun res m' =>
        res = ((if y = 0#64 then BitVec.allOnes 64 else x / y), x % y, ()) ∧ m' = m)
      (legalXPost LegalTarget.x64 X) :=
  fn_mid_spec (lt := LegalTarget.x64) divmodFn_wf divmodFn_supports_x64 krakenEmptyEnv rfl
    (fun _ _ h => legalPost_i64_2_x64_elim h) (fun _ _ _ _ h => h) (divmodT_spec x y m)

/-- End-to-end verified `Fn.mid LegalTarget.aarch64` spec for `Kraken.Bedrock2.Test.divmod`. -/
theorem divmodMid_aarch64_spec {X : XPost} (x y : BitVec 64) (m : Mem 64) :
    Func.wp (legalEnv LegalTarget.aarch64 krakenEmptyEnv) (divmodFn.mid LegalTarget.aarch64).body
      (x, y, ()) m
      (fun res m' =>
        res = ((if y = 0#64 then BitVec.allOnes 64 else x / y), x % y, ()) ∧ m' = m)
      (legalXPost LegalTarget.aarch64 X) :=
  fn_mid_spec (lt := LegalTarget.aarch64) divmodFn_wf divmodFn_supports_aarch64 krakenEmptyEnv rfl
    (fun _ _ h => legalPost_i64_2_aarch64_elim h) (fun _ _ _ _ h => h) (divmodT_spec x y m)

/-! ### Exact `Exec ↔ Func.wp` bridges for `sum`, `wide`, `absdiff` -/

theorem sum_toFunc_wp_iff :
    let bf := (Func.toBFlat? sum.2).get (rfl : (Func.toBFlat? sum.2).isSome = true)
    ∀ (ext : Kraken.Bedrock2.ExtSpec 64) (X : XPost)
      (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : LeanQbe.T.Post [i64]),
      LeanQbe.T.Func.wp krakenEmptyEnv
        ((denoteFuncB (as := [i64, i64]) bf).toFunc) xs m Q X ↔
      Kraken.Bedrock2.Exec ext [] 0 sum.2.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany
          (sum.2.params.zip (tupToList (n := 2) xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' sum.2.rets = some retvs ∧
            ∃ resTup : Tup Val [i64], tupToList (n := 1) resTup = retvs ∧ Q resTup m' :=
  fun ext X _ _ _ =>
    Func.fromKraken_toFunc_wp_iff (f := sum.2) rfl rfl
      (envB_ofTEnv_empty_iff_ofKraken_empty ext X)

theorem wide_toFunc_wp_iff :
    let bf := (Func.toBFlat? wide.2).get (rfl : (Func.toBFlat? wide.2).isSome = true)
    ∀ (ext : Kraken.Bedrock2.ExtSpec 64) (X : XPost)
      (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : LeanQbe.T.Post [i64]),
      LeanQbe.T.Func.wp krakenEmptyEnv
        ((denoteFuncB (as := [i64, i64]) bf).toFunc) xs m Q X ↔
      Kraken.Bedrock2.Exec ext [] 0 wide.2.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany
          (wide.2.params.zip (tupToList (n := 2) xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' wide.2.rets = some retvs ∧
            ∃ resTup : Tup Val [i64], tupToList (n := 1) resTup = retvs ∧ Q resTup m' :=
  fun ext X _ _ _ =>
    Func.fromKraken_toFunc_wp_iff (f := wide.2) rfl rfl
      (envB_ofTEnv_empty_iff_ofKraken_empty ext X)

theorem absdiff_toFunc_wp_iff :
    let bf := (Func.toBFlat? absdiff.2).get (rfl : (Func.toBFlat? absdiff.2).isSome = true)
    ∀ (ext : Kraken.Bedrock2.ExtSpec 64) (X : XPost)
      (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : LeanQbe.T.Post [i64, i64]),
      LeanQbe.T.Func.wp krakenEmptyEnv
        ((denoteFuncB (as := [i64, i64]) bf).toFunc) xs m Q X ↔
      Kraken.Bedrock2.Exec ext [] 0 absdiff.2.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany
          (absdiff.2.params.zip (tupToList (n := 2) xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' absdiff.2.rets = some retvs ∧
            ∃ resTup : Tup Val [i64, i64],
              tupToList (n := 2) resTup = retvs ∧ Q resTup m' :=
  fun ext X _ _ _ =>
    Func.fromKraken_toFunc_wp_iff (f := absdiff.2) rfl rfl
      (envB_ofTEnv_empty_iff_ofKraken_empty ext X)

/-! ### `stackNested` (`stackalloc`), `table` (`inlinetable1/2/4/8`), & `interact` Soundness -/

def stackNestedBf : BFlat [i64] :=
  (Func.toBFlat? stackNested.2).get (rfl : (Func.toBFlat? stackNested.2).isSome = true)

def stackNestedFb : FuncB [i64] [i64] := denoteFuncB (as := [i64]) stackNestedBf

theorem stackNested_fromKraken : Func.fromKraken stackNested.2 = some stackNestedFb := rfl

theorem stackNested_toFunc_wp_sound
    (ext : Kraken.Bedrock2.ExtSpec 64) (e : Kraken.Bedrock2.Env) {B : Nat} (hB : B < 2 ^ 64)
    (xs : Tup Val [i64]) (t : Kraken.Bedrock2.Trace 64) (m : Mem 64)
    (Q' : LeanQbe.T.Post [i64]) (X : XPost)
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hQ : ∀ resTup t' m', post t' m' (tupToList (n := 1) resTup) → Q' resTup m')
    (hex : Kraken.Bedrock2.Exec ext e B stackNested.2.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany
        (stackNested.2.params.zip (tupToList (n := 1) xs)))
      fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' stackNested.2.rets = some retvs ∧ post t' m' retvs) :
    LeanQbe.T.Func.wp (Env.ofBedrock2Sound {} (extToB ext) (EnvB.ofKraken ext e))
      stackNestedFb.toFunc xs m Q' X :=
  Func.fromKraken_toFunc_wp_sound stackNested_fromKraken hB X hQ hex

def tableBf : BFlat [i64, i64, i64] :=
  (Func.toBFlat? table.2).get (rfl : (Func.toBFlat? table.2).isSome = true)

def tableFb : FuncB [i64] [i64, i64, i64] := denoteFuncB (as := [i64]) tableBf

theorem table_fromKraken : Func.fromKraken table.2 = some tableFb := rfl
theorem table_toFunc_wf : tableFb.toFunc.Wf := Func.fromKraken_toFunc_wf table_fromKraken

theorem table_toFunc_wp_sound
    (ext : Kraken.Bedrock2.ExtSpec 64) (e : Kraken.Bedrock2.Env) {B : Nat} (hB : B < 2 ^ 64)
    (xs : Tup Val [i64]) (t : Kraken.Bedrock2.Trace 64) (m : Mem 64)
    (Q' : LeanQbe.T.Post [i64, i64, i64]) (X : XPost)
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hQ : ∀ resTup t' m', post t' m' (tupToList (n := 3) resTup) → Q' resTup m')
    (hex : Kraken.Bedrock2.Exec ext e B table.2.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany
        (table.2.params.zip (tupToList (n := 1) xs)))
      fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' table.2.rets = some retvs ∧ post t' m' retvs) :
    LeanQbe.T.Func.wp (Env.ofBedrock2Sound {} (extToB ext) (EnvB.ofKraken ext e))
      tableFb.toFunc xs m Q' X :=
  Func.fromKraken_toFunc_wp_sound table_fromKraken hB X hQ hex

/-- Custom `Kraken.Bedrock2` function exercising `call` + `interact`. -/
def krakenCallTxFn : Kraken.Bedrock2.Func where
  params := ["x"]
  rets := ["rc"]
  body :=
    .seq (.call ["y"] "inc" [.var "x"])
      (.interact ["rc"] "tx_word" [.var "y"])

/-- Custom `Kraken.Bedrock2` function exercising `store` + `interact`. -/
def krakenStoreTxFn : Kraken.Bedrock2.Func where
  params := ["p", "x"]
  rets := ["rc"]
  body :=
    .seq (.set "y" (.op .add (.var "x") (.literal 1)))
      (.seq (.store .eight (.var "p") (.var "y"))
        (.interact ["rc"] "tx_word" [.var "p"]))

def krakenCallTxBf : BFlat [i64] :=
  (Func.toBFlat? krakenCallTxFn).get (rfl : (Func.toBFlat? krakenCallTxFn).isSome = true)

def krakenCallTxFb : FuncB [i64] [i64] := denoteFuncB (as := [i64]) krakenCallTxBf

theorem krakenCallTx_fromKraken : Func.fromKraken krakenCallTxFn = some krakenCallTxFb := rfl

def krakenStoreTxBf : BFlat [i64] :=
  (Func.toBFlat? krakenStoreTxFn).get (rfl : (Func.toBFlat? krakenStoreTxFn).isSome = true)

def krakenStoreTxFb : FuncB [i64, i64] [i64] := denoteFuncB (as := [i64, i64]) krakenStoreTxBf

theorem krakenStoreTx_fromKraken : Func.fromKraken krakenStoreTxFn = some krakenStoreTxFb := rfl

theorem krakenCallTx_toFunc_wf : krakenCallTxFb.toFunc.Wf :=
  Func.fromKraken_toFunc_wf krakenCallTx_fromKraken

theorem krakenStoreTx_toFunc_wf : krakenStoreTxFb.toFunc.Wf :=
  Func.fromKraken_toFunc_wf krakenStoreTx_fromKraken

theorem krakenCallTx_toFunc_wp_sound
    (ext : Kraken.Bedrock2.ExtSpec 64) (e : Kraken.Bedrock2.Env) {B : Nat} (hB : B < 2 ^ 64)
    (xs : Tup Val [i64]) (t : Kraken.Bedrock2.Trace 64) (m : Mem 64)
    (Q' : LeanQbe.T.Post [i64]) (X : XPost)
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hQ : ∀ resTup t' m', post t' m' (tupToList (n := 1) resTup) → Q' resTup m')
    (hex : Kraken.Bedrock2.Exec ext e B krakenCallTxFn.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany
        (krakenCallTxFn.params.zip (tupToList (n := 1) xs)))
      fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' krakenCallTxFn.rets = some retvs ∧ post t' m' retvs) :
    LeanQbe.T.Func.wp (Env.ofBedrock2Sound {} (extToB ext) (EnvB.ofKraken ext e))
      krakenCallTxFb.toFunc xs m Q' X :=
  Func.fromKraken_toFunc_wp_sound krakenCallTx_fromKraken hB X hQ hex

theorem krakenStoreTx_toFunc_wp_sound
    (ext : Kraken.Bedrock2.ExtSpec 64) (e : Kraken.Bedrock2.Env) {B : Nat} (hB : B < 2 ^ 64)
    (xs : Tup Val [i64, i64]) (t : Kraken.Bedrock2.Trace 64) (m : Mem 64)
    (Q' : LeanQbe.T.Post [i64]) (X : XPost)
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hQ : ∀ resTup t' m', post t' m' (tupToList (n := 1) resTup) → Q' resTup m')
    (hex : Kraken.Bedrock2.Exec ext e B krakenStoreTxFn.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany
        (krakenStoreTxFn.params.zip (tupToList (n := 2) xs)))
      fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' krakenStoreTxFn.rets = some retvs ∧ post t' m' retvs) :
    LeanQbe.T.Func.wp (Env.ofBedrock2Sound {} (extToB ext) (EnvB.ofKraken ext e))
      krakenStoreTxFb.toFunc xs m Q' X :=
  Func.fromKraken_toFunc_wp_sound krakenStoreTx_fromKraken hB X hQ hex

/-- Suite check over 14 concrete `Kraken.Bedrock2.Test` functions proving translation to `BFlat`,
lowering to `LeanQbe.T.Func`, and target legality on both `x64` & `aarch64`. -/
def supportedKrakenFuncs : List (String × Kraken.Bedrock2.Func) :=
  [ Examples.swap 64, sum, Examples.set_bytes, stackNested, stackLoop, divmod, useDivmod,
    shifts, divZero, mulh, wide, absdiff, signed, Examples.same_slot ]

def krakenMidOk (p : String × Kraken.Bedrock2.Func) : Bool :=
  match Func.toBFlat? p.2 with
  | none => false
  | some bf =>
    let f := (denoteFuncB (as := List.replicate p.2.params.length i64) bf).toFunc
    let fn : Fn := ⟨p.1, _, _, f⟩
    (fn.earlyOpt).body.supportsSource LegalTarget.x64 &&
    (fn.earlyOpt).body.supportsSource LegalTarget.aarch64

theorem supportedKrakenFuncs_lower_and_legal :
    supportedKrakenFuncs.all krakenMidOk = true := by
  t_kernel_rfl

/-! ## 5. Negative Checks & Axiom Audit (`std3` only) -/

theorem badIdxBFlat_rejected :
    BFlat.wfCheck (rs := [i64]) (.ret (.var 99, ())) [] = false := rfl

theorem badTyBFlat_rejected :
    BFlat.wfCheck (rs := [i64])
      (.let_ ⟨.add i64, (.var 0, .var 0, ())⟩ (.ret (.var 0, ()))) [.bool] = false := rfl

theorem fib_fromKraken_rejected : Func.toBFlat? fib.2 = none := rfl

#print axioms arrSum_wf
#print axioms arrSumT_spec
#print axioms arrSumMid_x64_spec
#print axioms arrSumMid_aarch64_spec
#print axioms scratchSwapT_spec
#print axioms logAndIncT_spec
#print axioms ioMod_ok
#print axioms mulhMid_x64_spec
#print axioms mulhMid_aarch64_spec
#print axioms divmodMid_x64_spec
#print axioms divmodMid_aarch64_spec
#print axioms sum_toFunc_wp_iff
#print axioms wide_toFunc_wp_iff
#print axioms absdiff_toFunc_wp_iff
#print axioms stackNested_toFunc_wp_sound
#print axioms table_toFunc_wf
#print axioms table_toFunc_wp_sound
#print axioms krakenCallTx_toFunc_wp_sound
#print axioms krakenStoreTx_toFunc_wp_sound
#print axioms supportedKrakenFuncs_lower_and_legal

end LeanQbeTest.T.Bedrock2PhoasTest
