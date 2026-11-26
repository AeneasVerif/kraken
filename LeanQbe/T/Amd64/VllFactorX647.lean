module

public import LeanQbe.T.Amd64.VllFactorX646

/-!
# BedrockMach SysV x86-64 `Fn.mid` & Top-Level Parity (`Amd64.VllFactorX647`)

Part 2c–2d of the exact `asmX64List` lowering equality proof between `vllX64Isa` (`vllX64Target`)
and `x64Isa` (`x64Target`):
* `fnNoSameExt_mid`: every function lowered through `Fn.mid` satisfies `ExprNoSameExt`.
* Unconditional parity theorems (`vllX64_lowerFn_eq`, `vllX64_effFrame_eq`,
  `vllX64_checkAndBoundExt_eq`, `vllX64_compileFn_eq`, `vllX64_compile_eq`,
  `vllX64_compileModule_eq`) under `hintsNoRsp`.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 2c. `fnNoSameExt_mid`: `opNoSameExt` Closure Across `Fn.mid` -/

mutual
private inductive ExprNoSameExtGen {V : Ty → Type} {L : List Ty → Type} :
    {rs : List Ty} → Expr V L rs → Prop where
  | let_ {rs ts : List Ty} {op : Op V ts} {k : Tup V ts → Expr V L rs} :
      opNoSameExt op.code = true → (∀ xs, ExprNoSameExtGen (k xs)) →
      ExprNoSameExtGen (.let_ op k)
  | load {rs : List Ty} {t : Ty} {a : Arg V i64} {k : V t → Expr V L rs} :
      (∀ x, ExprNoSameExtGen (k x)) → ExprNoSameExtGen (.load t a k)
  | store {rs : List Ty} {t : Ty} {v : Arg V t} {a : Arg V i64} {k : Expr V L rs} :
      ExprNoSameExtGen k → ExprNoSameExtGen (.store v a k)
  | call {rs as : List Ty} {f : Sym} {bs : List Ty} {args : Tup (Arg V) as}
      {k : Tup V bs → Expr V L rs} :
      (∀ xs, ExprNoSameExtGen (k xs)) → ExprNoSameExtGen (.call f args k)
  | jnz {rs : List Ty} {c : Arg V .bool} {t e : Expr V L rs} :
      ExprNoSameExtGen t → ExprNoSameExtGen e → ExprNoSameExtGen (.jnz c t e)
  | jump {rs ts : List Ty} {j : L ts} {args : Tup (Arg V) ts} :
      ExprNoSameExtGen (.jump (rs := rs) j args)
  | ret {rs : List Ty} {vs : Tup (Arg V) rs} : ExprNoSameExtGen (.ret vs)
  | exit {rs as : List Ty} {f : Sym} {args : Tup (Arg V) as} :
      ExprNoSameExtGen (.exit (rs := rs) f args)
  | hlt {rs : List Ty} : ExprNoSameExtGen (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      {bodies : Tup L sig → Blocks V L rs sig} {k : Tup L sig → Expr V L rs} :
      (∀ ls, BlocksNoSameExtGen (bodies ls)) → (∀ ls, ExprNoSameExtGen (k ls)) →
      ExprNoSameExtGen (.group bodies k)

private inductive BlocksNoSameExtGen {V : Ty → Type} {L : List Ty → Type} :
    {rs : List Ty} → {sig : List (List Ty)} → Blocks V L rs sig → Prop where
  | nil {rs : List Ty} : BlocksNoSameExtGen (.nil (rs := rs))
  | cons {rs ts : List Ty} {sig : List (List Ty)}
      {b : Tup V ts → Expr V L rs} {bs : Blocks V L rs sig} :
      (∀ xs, ExprNoSameExtGen (b xs)) → BlocksNoSameExtGen bs →
      BlocksNoSameExtGen (.cons b bs)
end

mutual
private inductive TFlatNoSameExt : {rs : List Ty} → TFlat rs → Prop where
  | let_ {rs ts : List Ty} {op : Op K ts} {k : TFlat rs} :
      opNoSameExt op.code = true → TFlatNoSameExt k → TFlatNoSameExt (.let_ op k)
  | load {rs : List Ty} {t : Ty} {a : Arg K i64} {k : TFlat rs} :
      TFlatNoSameExt k → TFlatNoSameExt (.load t a k)
  | store {rs : List Ty} {t : Ty} {v : Arg K t} {a : Arg K i64} {k : TFlat rs} :
      TFlatNoSameExt k → TFlatNoSameExt (.store v a k)
  | call {rs as : List Ty} {f : Sym} {bs : List Ty} {args : Tup (Arg K) as} {k : TFlat rs} :
      TFlatNoSameExt k → TFlatNoSameExt (.call f bs args k)
  | jnz {rs : List Ty} {c : Arg K .bool} {t e : TFlat rs} :
      TFlatNoSameExt t → TFlatNoSameExt e → TFlatNoSameExt (.jnz c t e)
  | jump {rs ts : List Ty} {j : Nat} {args : Tup (Arg K) ts} :
      TFlatNoSameExt (.jump (rs := rs) (ts := ts) j args)
  | ret {rs : List Ty} {vs : Tup (Arg K) rs} : TFlatNoSameExt (.ret vs)
  | exit {rs as : List Ty} {f : Sym} {args : Tup (Arg K) as} :
      TFlatNoSameExt (.exit (rs := rs) f args)
  | hlt {rs : List Ty} : TFlatNoSameExt (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      {bodies : TBlocks rs sig} {k : TFlat rs} :
      TBlocksNoSameExt bodies → TFlatNoSameExt k → TFlatNoSameExt (.group bodies k)

private inductive TBlocksNoSameExt : {rs : List Ty} → {sig : List (List Ty)} →
    TBlocks rs sig → Prop where
  | nil {rs : List Ty} : TBlocksNoSameExt (.nil (rs := rs))
  | cons {rs ts : List Ty} {sig : List (List Ty)} {b : TFlat rs} {bs : TBlocks rs sig} :
      TFlatNoSameExt b → TBlocksNoSameExt bs → TBlocksNoSameExt (.cons (ts := ts) b bs)
end

private theorem opNoSameExt_ite {V : Ty → Type} {ts : List Ty} (c : Bool)
    {a b : Op V ts} (ha : opNoSameExt a.code = true) (hb : opNoSameExt b.code = true) :
    opNoSameExt (if c then a else b).code = true := by
  cases c <;> simp [ha, hb]

private theorem dite_pos {P : Prop} [Decidable P] {α : Type} {t : P → α} {e : ¬ P → α}
    (h : P) : (if h' : P then t h' else e h') = t h := by
  split <;> first | rfl | contradiction

private theorem dite_neg {P : Prop} [Decidable P] {α : Type} {t : P → α} {e : ¬ P → α}
    (h : ¬ P) : (if h' : P then t h' else e h') = e h := by
  split <;> first | contradiction | rfl

private theorem foldRewrite_opNoSameExt {V : Ty → Type} {ts : List Ty} (op : Op (FVal V) ts)
    (hsa : op.simpAct = none) (hsp : op.simpProv? = none) :
    opNoSameExt op.foldRewrite.code = true := by
  rcases op with ⟨code, args⟩
  cases code with
  | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    have hne : m ≠ n := by
      intro e; subst e; dsimp only [Op.simpAct] at hsa
      cases hev : (tupImms? (tupMapArg (fun _ => Arg.fout) (a, ()))).bind
          (OpCode.sext m m).eval? with
      | none => simp only [hev, ↓reduceDIte] at hsa; cases hsa
      | some _ => simp only [hev] at hsa; cases hsa
    dsimp only [Op.foldRewrite]
    cases extTarget (n := n) .sext a with
    | none => exact bne_iff_ne.mpr hne
    | some tg => exact bne_iff_ne.mpr (Nat.ne_of_lt tg.hlt)
  | zext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    have hne : m ≠ n := by
      intro e; subst e; dsimp only [Op.simpAct] at hsa
      cases hev : (tupImms? (tupMapArg (fun _ => Arg.fout) (a, ()))).bind
          (OpCode.zext m m).eval? with
      | none => simp only [hev, ↓reduceDIte] at hsa; cases hsa
      | some _ => simp only [hev] at hsa; cases hsa
    dsimp only [Op.foldRewrite]
    cases extTarget (n := n) .zext a with
    | none => exact bne_iff_ne.mpr hne
    | some tg => exact bne_iff_ne.mpr (Nat.ne_of_lt tg.hlt)
  | trunc m n =>
    rcases args with ⟨a, ⟨⟩⟩
    have hne : m ≠ n := by
      intro e; subst e; dsimp only [Op.simpAct] at hsa
      cases hev : (tupImms? (tupMapArg (fun _ => Arg.fout) (a, ()))).bind
          (OpCode.trunc m m).eval? with
      | none => simp only [hev, ↓reduceDIte] at hsa; cases hsa
      | some _ => simp only [hev] at hsa; cases hsa
    by_cases hnm : n < m
    · cases ha : a.fext with
      | none =>
        dsimp only [Op.foldRewrite, truncTarget?]; rw [dite_pos hnm, ha]
        exact bne_iff_ne.mpr hne
      | some e =>
        have hem : e.m ≠ n := by
          intro h0
          dsimp only [Op.simpProv?] at hsp; rw [ha] at hsp
          simp only [h0, ↓reduceDIte] at hsp; cases hsp
        dsimp only [Op.foldRewrite, truncTarget?]; rw [dite_pos hnm, ha]
        by_cases hle : n ≤ e.m
        · dsimp only; rw [dite_pos hle]; exact bne_iff_ne.mpr hem
        · dsimp only; rw [dite_neg hle]
          cases e.kind <;> exact bne_iff_ne.mpr (Nat.ne_of_lt (Nat.lt_of_not_ge hle))
    · dsimp only [Op.foldRewrite, truncTarget?]; rw [dite_neg hnm]
      exact bne_iff_ne.mpr hne
  | cmp o t m hc =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases t with
    | bits _ => dsimp only [Op.foldRewrite]; split <;> rfl
    | bool | float _ | pair _ _ =>
      dsimp only [Op.foldRewrite]; exact opNoSameExt_ite _ rfl rfl
  | select t =>
    rcases args with ⟨c, a, b, ⟨⟩⟩
    cases t with
    | bool =>
      dsimp only [Op.foldRewrite]
      exact opNoSameExt_ite _ rfl (opNoSameExt_ite _ rfl (opNoSameExt_ite _ rfl rfl))
    | bits _ => dsimp only [Op.foldRewrite]; exact opNoSameExt_ite _ rfl rfl
    | float _ | pair _ _ => rfl
  | mul t =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [Op.foldRewrite, tupMapArg, Op.rewrite]
    refine opNoSameExt_ite _ rfl ?_
    cases b.fout.imm?.bind (leafPow2Shift? t) with
    | some _ => rfl
    | none => cases a.fout.imm?.bind (leafPow2Shift? t) <;> rfl
  | udiv n =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [Op.foldRewrite, Op.rewrite]
    split <;> rfl
  | urem n =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [Op.foldRewrite, Op.rewrite]
    split <;> rfl
  | _ => rfl

mutual
private theorem fold_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (next : Nat) (e : Expr (FVal V) L rs), ExprNoSameExtGen (LeanQbe.T.fold next e)
  | next, .let_ (ts := ts) op k => by
    unfold LeanQbe.T.fold
    cases hsa : op.simpAct with
    | some act => exact fold_noSameExt next (k (act.apply op.args))
    | none =>
      cases hsp : op.simpProv? with
      | some res => exact fold_noSameExt next (k res)
      | none =>
        exact .let_ (foldRewrite_opNoSameExt op hsa hsp)
          (fun xs => fold_noSameExt (next + ts.length) (k (op.foldWrap next xs)))
  | next, .load t a k => .load fun v => fold_noSameExt (next + 1) (k (FVal.fresh v next))
  | next, .store v a k => .store (fold_noSameExt next k)
  | next, .call f (bs := bs) args k =>
    .call fun xs => fold_noSameExt (next + bs.length) (k (freshFVals bs xs next))
  | next, .jnz c t e => by
    unfold LeanQbe.T.fold
    cases c.fout with
    | imm b => cases b <;> exact fold_noSameExt next _
    | var _ => exact .jnz (fold_noSameExt next t) (fold_noSameExt next e)
  | _, .jump _ _ => .jump
  | _, .ret _ => .ret
  | _, .exit _ _ => .exit
  | _, .hlt => .hlt
  | next, .group bodies k =>
    .group (fun Js => foldB_noSameExt next (bodies Js)) (fun Js => fold_noSameExt next (k Js))

private theorem foldB_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (next : Nat) {sig : List (List Ty)} (bs : Blocks (FVal V) L rs sig),
      BlocksNoSameExtGen (foldB next bs)
  | _, _, .nil => .nil
  | next, _, .cons (ts := ts) b bs =>
    .cons (fun xs => fold_noSameExt (next + ts.length) (b (freshFVals ts xs next)))
      (foldB_noSameExt next bs)
end

mutual
private theorem dceSweep_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (kt : KeepTree) (e : Expr (OptV V) L rs),
      ExprNoSameExtGen e → ExprNoSameExtGen (dceSweep kt e)
  | kt, .let_ op k, .let_ hok hk => by
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true => exact .let_ hok fun xs => dceSweep_noSameExt kt' _ (hk _)
      | false => exact dceSweep_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .load t a k, .load hk => by
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true => exact .load fun v => dceSweep_noSameExt kt' _ (hk _)
      | false => exact dceSweep_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .store v a k, .store hk => by
    cases kt with
    | node1 kt' => exact .store (dceSweep_noSameExt kt' k hk)
    | _ => exact .hlt
  | kt, .call f args k, .call hk => by
    cases kt with
    | node1 kt' => exact .call fun xs => dceSweep_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .jnz c t e, .jnz ht he => by
    cases kt with
    | node2 ktt kte => exact .jnz (dceSweep_noSameExt ktt t ht) (dceSweep_noSameExt kte e he)
    | _ => exact .hlt
  | _, .jump _ _, .jump => .jump
  | _, .ret _, .ret => .ret
  | _, .exit _ _, .exit => .exit
  | _, .hlt, .hlt => .hlt
  | kt, .group bodies k, .group hb hk => by
    cases kt with
    | groupNode kbs ktk =>
      exact .group (fun Js => dceSweepB_noSameExt kbs _ (hb Js))
        (fun Js => dceSweep_noSameExt ktk _ (hk Js))
    | _ => exact .hlt

private theorem dceSweepB_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (kbs : KeepBlocks) {sig : List (List Ty)} (bs : Blocks (OptV V) L rs sig),
      BlocksNoSameExtGen bs → BlocksNoSameExtGen (dceSweepB kbs bs)
  | _, _, .nil, .nil => .nil
  | kbs, _, .cons b bs, .cons hb hbs => by
    cases kbs with
    | cons kh kt =>
      exact .cons (fun xs => dceSweep_noSameExt kh _ (hb _)) (dceSweepB_noSameExt kt bs hbs)
    | _ =>
      exact .cons (fun _ => .hlt) (dceSweepB_noSameExt .nil bs hbs)
end

mutual
private theorem dceSweepP_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (kt : DceParam.PTree) (e : Expr (OptV V) (DceParam.NLabel L) rs),
      ExprNoSameExtGen e → ExprNoSameExtGen (DceParam.dceSweepP kt e)
  | kt, .let_ op k, .let_ hok hk => by
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true => exact .let_ hok fun xs => dceSweepP_noSameExt kt' _ (hk _)
      | false => exact dceSweepP_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .load t a k, .load hk => by
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true => exact .load fun v => dceSweepP_noSameExt kt' _ (hk _)
      | false => exact dceSweepP_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .store v a k, .store hk => by
    cases kt with
    | node1 kt' => exact .store (dceSweepP_noSameExt kt' k hk)
    | _ => exact .hlt
  | kt, .call f args k, .call hk => by
    cases kt with
    | node1 kt' => exact .call fun xs => dceSweepP_noSameExt kt' _ (hk _)
    | _ => exact .hlt
  | kt, .jnz c t e, .jnz ht he => by
    cases kt with
    | node2 ktt kte => exact .jnz (dceSweepP_noSameExt ktt t ht) (dceSweepP_noSameExt kte e he)
    | _ => exact .hlt
  | _, .jump _ _, .jump => .jump
  | _, .ret _, .ret => .ret
  | _, .exit _ _, .exit => .exit
  | _, .hlt, .hlt => .hlt
  | kt, .group bodies k, .group hb hk => by
    cases kt with
    | groupNode kbs ktk =>
      exact .group (fun Js => dceSweepBP_noSameExt kbs _ (hb _))
        (fun Js => dceSweepP_noSameExt ktk _ (hk _))
    | _ => exact .hlt

private theorem dceSweepBP_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (kbs : DceParam.PBlocks) {sig : List (List Ty)}
      (bs : Blocks (OptV V) (DceParam.NLabel L) rs sig),
      BlocksNoSameExtGen bs → BlocksNoSameExtGen (DceParam.dceSweepBP kbs bs)
  | _, _, .nil, .nil => .nil
  | kbs, _, .cons _ bs, .cons hb hbs =>
    .cons (fun _ => dceSweepP_noSameExt kbs.hd _ (hb _)) (dceSweepBP_noSameExt kbs.tl bs hbs)
end

mutual
private theorem mergeRets_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) :
    ∀ (e : Expr V L rs), ExprNoSameExtGen e → ExprNoSameExtGen (e.mergeRets exit_lbl)
  | .let_ _ _, .let_ hok hk => .let_ hok fun xs => mergeRets_noSameExt exit_lbl _ (hk xs)
  | .load _ _ _, .load hk => .load fun v => mergeRets_noSameExt exit_lbl _ (hk v)
  | .store _ _ k, .store hk => .store (mergeRets_noSameExt exit_lbl k hk)
  | .call _ _ _, .call hk => .call fun xs => mergeRets_noSameExt exit_lbl _ (hk xs)
  | .jnz _ t e, .jnz ht he =>
    .jnz (mergeRets_noSameExt exit_lbl t ht) (mergeRets_noSameExt exit_lbl e he)
  | .jump _ _, .jump => .jump
  | .ret _, .ret => .jump
  | .exit _ _, .exit => .exit
  | .hlt, .hlt => .hlt
  | .group _ _, .group hb hk =>
    .group (fun Js => blocks_mergeRets_noSameExt exit_lbl _ (hb Js))
      (fun Js => mergeRets_noSameExt exit_lbl _ (hk Js))

private theorem blocks_mergeRets_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) :
    ∀ {sig : List (List Ty)} (bs : Blocks V L rs sig),
      BlocksNoSameExtGen bs → BlocksNoSameExtGen (bs.mergeRets exit_lbl)
  | _, .nil, .nil => .nil
  | _, .cons _ _, .cons hb hbs =>
    .cons (fun xs => mergeRets_noSameExt exit_lbl _ (hb xs))
      (blocks_mergeRets_noSameExt exit_lbl _ hbs)
end

mutual
private theorem toTFlat_noSameExt {rs : List Ty} :
    ∀ (e : Expr K KL rs) (nv nl : Nat),
      ExprNoSameExtGen e → TFlatNoSameExt (toTFlat e nv nl)
  | .let_ (ts := ts) _ k, nv, nl, .let_ hok hk =>
    .let_ hok (toTFlat_noSameExt (k (Tup.levels ts nv)) (nv + ts.length) nl (hk _))
  | .load _ _ k, nv, nl, .load hk => .load (toTFlat_noSameExt (k nv) (nv + 1) nl (hk nv))
  | .store _ _ k, nv, nl, .store hk => .store (toTFlat_noSameExt k nv nl hk)
  | .call _ (bs := bs) _ k, nv, nl, .call hk =>
    .call (toTFlat_noSameExt (k (Tup.levels bs nv)) (nv + bs.length) nl (hk _))
  | .jnz _ t e, nv, nl, .jnz ht he =>
    .jnz (toTFlat_noSameExt t nv nl ht) (toTFlat_noSameExt e nv nl he)
  | .jump _ _, _, _, .jump => .jump
  | .ret _, _, _, .ret => .ret
  | .exit _ _, _, _, .exit => .exit
  | .hlt, _, _, .hlt => .hlt
  | .group (sig := sig) bodies k, nv, nl, .group hb hk =>
    .group (toTBlocks_noSameExt (bodies (Tup.levels sig nl)) nv (nl + sig.length) (hb _))
      (toTFlat_noSameExt (k (Tup.levels sig nl)) nv (nl + sig.length) (hk _))

private theorem toTBlocks_noSameExt {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) (nv nl : Nat),
      BlocksNoSameExtGen bs → TBlocksNoSameExt (toTBlocks bs nv nl)
  | _, .nil, _, _, .nil => .nil
  | _, .cons (ts := ts) b bs, nv, nl, .cons hb hbs =>
    .cons (toTFlat_noSameExt (b (Tup.levels ts nv)) (nv + ts.length) nl (hb _))
      (toTBlocks_noSameExt bs nv nl hbs)
end

mutual
private theorem denote_noSameExt (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    ∀ (tf : TFlat rs) (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)),
      TFlatNoSameExt tf → ExprNoSameExtGen (denote V L tf vs ls)
  | .let_ op k, vs, ls, .let_ hok hk => by
    dsimp only [denote]
    cases denoteArgs vs op.args with
    | none => exact .hlt
    | some _ => exact .let_ hok fun xs => denote_noSameExt V L k (pushTup xs vs) ls hk
  | .load _ a k, vs, ls, .load hk => by
    dsimp only [denote]
    cases denoteArg vs a with
    | none => exact .hlt
    | some _ => exact .load fun v => denote_noSameExt V L k _ ls hk
  | .store v a k, vs, ls, .store hk => by
    dsimp only [denote]
    cases denoteArg vs v with
    | none => exact .hlt
    | some _ => cases denoteArg vs a with
      | none => exact .hlt
      | some _ => exact .store (denote_noSameExt V L k vs ls hk)
  | .call _ _ args k, vs, ls, .call hk => by
    dsimp only [denote]
    cases denoteArgs vs args with
    | none => exact .hlt
    | some _ => exact .call fun xs => denote_noSameExt V L k (pushTup xs vs) ls hk
  | .jnz c t e, vs, ls, .jnz ht he => by
    dsimp only [denote]
    cases denoteArg vs c with
    | none => exact .hlt
    | some _ => exact .jnz (denote_noSameExt V L t vs ls ht) (denote_noSameExt V L e vs ls he)
  | .jump (ts := ts) j args, vs, ls, .jump => by
    dsimp only [denote]
    cases lookupL ls ts j with
    | none => exact .hlt
    | some _ => cases denoteArgs vs args with
      | none => exact .hlt
      | some _ => exact .jump
  | .ret vs', vs, _, .ret => by
    dsimp only [denote]; cases denoteArgs vs vs' <;> first | exact .hlt | exact .ret
  | .exit _ args, vs, _, .exit => by
    dsimp only [denote]; cases denoteArgs vs args <;> first | exact .hlt | exact .exit
  | .hlt, _, _, .hlt => .hlt
  | .group bodies k, vs, ls, .group hb hk =>
    .group (fun Js => denoteB_noSameExt V L bodies vs (pushTup Js ls) hb)
      (fun Js => denote_noSameExt V L k vs (pushTup Js ls) hk)

private theorem denoteB_noSameExt (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : TBlocks rs sig)
      (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)),
      TBlocksNoSameExt bs → BlocksNoSameExtGen (denoteB V L bs vs ls)
  | _, .nil, _, _, .nil => .nil
  | _, .cons b bs, vs, ls, .cons hb hbs =>
    .cons (fun xs => denote_noSameExt V L b (pushTup xs vs) ls hb)
      (denoteB_noSameExt V L bs vs ls hbs)
end

mutual
private theorem exprNoSameExtGen_to_expr {rs : List Ty} :
    ∀ (e : Expr Rega.VNat Rega.LNat rs), ExprNoSameExtGen e → ExprNoSameExt e
  | .let_ _ _, .let_ hok hk => .let_ hok fun xs => exprNoSameExtGen_to_expr _ (hk xs)
  | .load _ _ _, .load hk => .load fun x => exprNoSameExtGen_to_expr _ (hk x)
  | .store _ _ k, .store hk => .store (exprNoSameExtGen_to_expr k hk)
  | .call _ _ _, .call hk => .call fun xs => exprNoSameExtGen_to_expr _ (hk xs)
  | .jnz _ t e, .jnz ht he =>
    .jnz (exprNoSameExtGen_to_expr t ht) (exprNoSameExtGen_to_expr e he)
  | .jump _ _, .jump => @ExprNoSameExt.jump rs rs _ _ _
  | .ret _, .ret => .ret
  | .exit _ _, .exit => @ExprNoSameExt.exit rs rs _ _ _
  | .hlt, .hlt => .hlt
  | .group _ _, .group hb hk =>
    .group (fun ls => blocksNoSameExtGen_to_blocks _ (hb ls))
      (fun ls => exprNoSameExtGen_to_expr _ (hk ls))

private theorem blocksNoSameExtGen_to_blocks {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks Rega.VNat Rega.LNat rs sig),
      BlocksNoSameExtGen bs → BlocksNoSameExt bs
  | _, .nil, .nil => .nil
  | _, .cons _ _, .cons hb hbs =>
    .cons (fun xs => exprNoSameExtGen_to_expr _ (hb xs))
      (blocksNoSameExtGen_to_blocks _ hbs)
end

private def DupLSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {ts : List Ty} → TailDup.DupL V L rs ts → Prop
  | _, .keep _ => True
  | _, .dead => True
  | _, .dup body => ∀ args, ExprNoSameExtGen (body args)

private def TupDupLSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Tup (TailDup.DupL V L rs) sig → Prop
  | [], () => True
  | _ :: _, (l, ls) => DupLSafe l ∧ TupDupLSafe ls

private theorem pushTup_listDupLSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (Js : Tup (TailDup.DupL V L rs) sig)
      {ls : List ((ts : List Ty) × TailDup.DupL V L rs ts)},
      TupDupLSafe Js → (∀ p ∈ ls, DupLSafe p.2) →
      ∀ p ∈ pushTup Js ls, DupLSafe p.2
  | [], (), _, _, hls => hls
  | _ :: _, (_, Js), _, ⟨hl, hJs⟩, hls =>
    pushTup_listDupLSafe Js hJs fun p hp =>
      (List.mem_cons.mp hp).elim (fun e => e ▸ hl) (hls p)

private theorem listGet?_mem {α : Type} :
    ∀ (xs : List α) (idx : Nat) {a : α}, listGet? xs idx = some a → a ∈ xs
  | a :: _, 0, _, h => by cases h; exact .head _
  | _ :: as, idx + 1, a, h => .tail _ (listGet?_mem as idx h)

private theorem lookupL_dupLSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ls : List ((ts : List Ty) × TailDup.DupL V L rs ts))
    (hls : ∀ p ∈ ls, DupLSafe p.2) {ts : List Ty} {idx : Nat}
    {l : TailDup.DupL V L rs ts} (hl : lookupL ls ts idx = some l) :
    DupLSafe l := by
  dsimp only [lookupL] at hl
  cases hget : listGet? ls idx with
  | none => rw [hget] at hl; cases hl
  | some p =>
    rw [hget] at hl
    obtain ⟨ts', l'⟩ := p
    have hmem := hls ⟨ts', l'⟩ (listGet?_mem ls idx hget)
    dsimp only [castListTy] at hl
    cases hdec : listTyDecEq ts' ts with
    | isFalse => rw [hdec] at hl; cases hl
    | isTrue h => rw [hdec] at hl; cases h; cases hl; exact hmem

mutual
private inductive ExprDupSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (Arg V) (TailDup.DupL V L rs) rs → Prop where
  | let_ {ts : List Ty} {op : Op (Arg V) ts}
      {k : Tup (Arg V) ts → Expr (Arg V) (TailDup.DupL V L rs) rs} :
      opNoSameExt op.code = true → (∀ xs, ExprDupSafe (k xs)) →
      ExprDupSafe (.let_ op k)
  | load {t : Ty} {a : Arg (Arg V) i64}
      {k : Arg V t → Expr (Arg V) (TailDup.DupL V L rs) rs} :
      (∀ x, ExprDupSafe (k x)) → ExprDupSafe (.load t a k)
  | store {t : Ty} {v : Arg (Arg V) t} {a : Arg (Arg V) i64}
      {k : Expr (Arg V) (TailDup.DupL V L rs) rs} :
      ExprDupSafe k → ExprDupSafe (.store v a k)
  | call {as : List Ty} {f : Sym} {bs : List Ty} {args : Tup (Arg (Arg V)) as}
      {k : Tup (Arg V) bs → Expr (Arg V) (TailDup.DupL V L rs) rs} :
      (∀ xs, ExprDupSafe (k xs)) → ExprDupSafe (.call f args k)
  | jnz {c : Arg (Arg V) .bool} {t e : Expr (Arg V) (TailDup.DupL V L rs) rs} :
      ExprDupSafe t → ExprDupSafe e → ExprDupSafe (.jnz c t e)
  | jump {ts : List Ty} {j : TailDup.DupL V L rs ts}
      {args : Tup (Arg (Arg V)) ts} :
      DupLSafe j → ExprDupSafe (.jump j args)
  | ret {vs : Tup (Arg (Arg V)) rs} : ExprDupSafe (.ret vs)
  | exit {as : List Ty} {f : Sym} {args : Tup (Arg (Arg V)) as} :
      ExprDupSafe (.exit f args)
  | hlt : ExprDupSafe .hlt
  | group {sig : List (List Ty)}
      {bodies : Tup (TailDup.DupL V L rs) sig → Blocks (Arg V) (TailDup.DupL V L rs) rs sig}
      {k : Tup (TailDup.DupL V L rs) sig → Expr (Arg V) (TailDup.DupL V L rs) rs} :
      (∀ ls, TupDupLSafe ls → BlocksDupSafe (bodies ls)) →
      (∀ ls, TupDupLSafe ls → ExprDupSafe (k ls)) →
      ExprDupSafe (.group bodies k)

private inductive BlocksDupSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (Arg V) (TailDup.DupL V L rs) rs sig → Prop where
  | nil : BlocksDupSafe .nil
  | cons {ts : List Ty} {sig : List (List Ty)}
      {b : Tup (Arg V) ts → Expr (Arg V) (TailDup.DupL V L rs) rs}
      {bs : Blocks (Arg V) (TailDup.DupL V L rs) rs sig} :
      (∀ xs, ExprDupSafe (b xs)) → BlocksDupSafe bs → BlocksDupSafe (.cons b bs)
end

mutual
private theorem denote_dupSafe (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    ∀ (tf : TFlat rs) (vs : List ((t : Ty) × Arg V t))
      (ls : List ((ts : List Ty) × TailDup.DupL V L rs ts)),
      TFlatNoSameExt tf → (∀ p ∈ ls, DupLSafe p.2) →
      ExprDupSafe (denote (Arg V) (TailDup.DupL V L rs) tf vs ls)
  | .let_ op k, vs, ls, .let_ hok hk, hls => by
    dsimp only [denote]
    cases denoteArgs vs op.args with
    | none => exact .hlt
    | some _ => exact .let_ hok fun xs => denote_dupSafe V L k (pushTup xs vs) ls hk hls
  | .load _ a k, vs, ls, .load hk, hls => by
    dsimp only [denote]
    cases denoteArg vs a with
    | none => exact .hlt
    | some _ => exact .load fun v => denote_dupSafe V L k _ ls hk hls
  | .store v a k, vs, ls, .store hk, hls => by
    dsimp only [denote]
    cases denoteArg vs v with
    | none => exact .hlt
    | some _ => cases denoteArg vs a with
      | none => exact .hlt
      | some _ => exact .store (denote_dupSafe V L k vs ls hk hls)
  | .call _ _ args k, vs, ls, .call hk, hls => by
    dsimp only [denote]
    cases denoteArgs vs args with
    | none => exact .hlt
    | some _ => exact .call fun xs => denote_dupSafe V L k (pushTup xs vs) ls hk hls
  | .jnz c t e, vs, ls, .jnz ht he, hls => by
    dsimp only [denote]
    cases denoteArg vs c with
    | none => exact .hlt
    | some _ => exact .jnz (denote_dupSafe V L t vs ls ht hls) (denote_dupSafe V L e vs ls he hls)
  | .jump (ts := ts) j args, vs, ls, .jump, hls => by
    dsimp only [denote]
    cases hlk : lookupL ls ts j with
    | none => exact .hlt
    | some j' =>
      cases denoteArgs vs args with
      | none => exact .hlt
      | some _ => exact .jump (lookupL_dupLSafe ls hls hlk)
  | .ret vs', vs, _, .ret, _ => by
    dsimp only [denote]; cases denoteArgs vs vs' <;> first | exact .hlt | exact .ret
  | .exit _ args, vs, _, .exit, _ => by
    dsimp only [denote]; cases denoteArgs vs args <;> first | exact .hlt | exact .exit
  | .hlt, _, _, .hlt, _ => .hlt
  | .group bodies k, vs, ls, .group hb hk, hls =>
    .group (fun Js hJs => denoteB_dupSafe V L bodies vs (pushTup Js ls) hb
        (pushTup_listDupLSafe Js hJs hls))
      (fun Js hJs => denote_dupSafe V L k vs (pushTup Js ls) hk
        (pushTup_listDupLSafe Js hJs hls))

private theorem denoteB_dupSafe (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : TBlocks rs sig)
      (vs : List ((t : Ty) × Arg V t)) (ls : List ((ts : List Ty) × TailDup.DupL V L rs ts)),
      TBlocksNoSameExt bs → (∀ p ∈ ls, DupLSafe p.2) →
      BlocksDupSafe (denoteB (Arg V) (TailDup.DupL V L rs) bs vs ls)
  | _, .nil, _, _, .nil, _ => .nil
  | _, .cons b bs, vs, ls, .cons hb hbs, hls =>
    .cons (fun xs => denote_dupSafe V L b (pushTup xs vs) ls hb hls)
      (denoteB_dupSafe V L bs vs ls hbs hls)
end

private theorem deadTup_dupSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (sig : List (List Ty)),
      TupDupLSafe (TailDup.deadTup (V := V) (L := L) (rs := rs) sig)
  | [] => trivial
  | _ :: sig => ⟨trivial, deadTup_dupSafe sig⟩

private theorem expandKeepLabels_dupSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    ∀ (acts : List TailDup.DupAct) (sig : List (List Ty))
      (Js : Tup L (TailDup.filterActsSig acts sig)),
      TupDupLSafe (TailDup.expandKeepLabels (V := V) (rs := rs) acts sig Js)
  | _, [], () => trivial
  | [], _ :: sig, () => ⟨trivial, deadTup_dupSafe sig⟩
  | .keep :: acts, _ :: sig, (_, Js) => ⟨trivial, expandKeepLabels_dupSafe acts sig Js⟩
  | .dup :: acts, _ :: sig, Js | .drop :: acts, _ :: sig, Js =>
    ⟨trivial, expandKeepLabels_dupSafe acts sig Js⟩

mutual
private theorem rewriteExpr_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (plan : TailDup.DupPlan) :
    ∀ (e : Expr (Arg V) (TailDup.DupL V L rs) rs),
      ExprDupSafe e → ExprNoSameExtGen (TailDup.rewriteExpr plan e)
  | .let_ op k, .let_ hok hk => by
    cases plan with
    | node1 pk => exact .let_ hok fun xs => rewriteExpr_noSameExt pk _ (hk _)
    | _ => exact .hlt
  | .load t a k, .load hk => by
    cases plan with
    | node1 pk => exact .load fun v => rewriteExpr_noSameExt pk _ (hk _)
    | _ => exact .hlt
  | .store v a k, .store hk => by
    cases plan with
    | node1 pk => exact .store (rewriteExpr_noSameExt pk k hk)
    | _ => exact .hlt
  | .call f args k, .call hk => by
    cases plan with
    | node1 pk => exact .call fun xs => rewriteExpr_noSameExt pk _ (hk _)
    | _ => exact .hlt
  | .jnz c t e, .jnz ht he => by
    cases plan with
    | node2 pt pe =>
      exact .jnz (rewriteExpr_noSameExt pt t ht) (rewriteExpr_noSameExt pe e he)
    | _ => exact .hlt
  | .jump j args, .jump hj => by
    cases plan with
    | leaf =>
      cases j with
      | keep _ => exact .jump
      | dead => exact .hlt
      | dup body => exact hj _
    | _ => exact .hlt
  | .ret _, .ret => by
    cases plan <;> first | exact .ret | exact .hlt
  | .exit _ _, .exit => by
    cases plan <;> first | exact .exit | exact .hlt
  | .hlt, .hlt => by
    cases plan <;> exact .hlt
  | .group (sig := sig) bodies k, .group hb hk => by
    cases plan with
    | group acts pbs pk =>
      dsimp only [TailDup.rewriteExpr]
      split
      · refine .group (fun Js => ?_) (fun Js => ?_)
        · have hNo := expandKeepLabels_dupSafe (V := V) (rs := rs) acts sig Js
          have hDup := buildDupLabels_dupSafe acts pbs (bodies _) _ (hb _ hNo) hNo
          exact rewriteKeptBlocks_noSameExt acts pbs _ (hb _ hDup)
        · have hNo := expandKeepLabels_dupSafe (V := V) (rs := rs) acts sig Js
          have hDup := buildDupLabels_dupSafe acts pbs (bodies _) _ (hb _ hNo) hNo
          exact rewriteExpr_noSameExt pk _ (hk _ hDup)
      · have hNo := deadTup_dupSafe (V := V) (L := L) (rs := rs) sig
        have hDup := buildDupLabels_dupSafe acts pbs (bodies _) _ (hb _ hNo) hNo
        exact rewriteExpr_noSameExt pk _ (hk _ hDup)
    | _ => exact .hlt

private theorem buildDupLabels_dupSafe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (acts : List TailDup.DupAct) (pbs : TailDup.DupPlanB) :
    ∀ {sig : List (List Ty)} (bs : Blocks (Arg V) (TailDup.DupL V L rs) rs sig)
      (ls : Tup (TailDup.DupL V L rs) sig),
      BlocksDupSafe bs → TupDupLSafe ls →
      TupDupLSafe (TailDup.buildDupLabels acts pbs bs ls)
  | [], .nil, (), .nil, _ => trivial
  | _ :: sig, .cons b bs, (l, ls), .cons hb hbs, ⟨hl, hls⟩ => by
    cases acts with
    | nil => exact ⟨trivial, deadTup_dupSafe sig⟩
    | cons a acts' =>
      cases pbs with
      | nil => cases a <;> exact ⟨trivial, deadTup_dupSafe sig⟩
      | cons pb pbs' =>
        cases a with
        | dup => exact ⟨fun args => rewriteExpr_noSameExt pb _ (hb args),
            buildDupLabels_dupSafe acts' pbs' bs ls hbs hls⟩
        | keep => exact ⟨hl, buildDupLabels_dupSafe acts' pbs' bs ls hbs hls⟩
        | drop => exact ⟨trivial, buildDupLabels_dupSafe acts' pbs' bs ls hbs hls⟩

private theorem rewriteKeptBlocks_noSameExt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (acts : List TailDup.DupAct) (pbs : TailDup.DupPlanB) :
    ∀ {sig : List (List Ty)} (bs : Blocks (Arg V) (TailDup.DupL V L rs) rs sig),
      BlocksDupSafe bs →
      BlocksNoSameExtGen (TailDup.rewriteKeptBlocks acts pbs bs)
  | [], .nil, .nil => .nil
  | _ :: _, .cons b bs, .cons hb hbs => by
    cases acts with
    | nil => exact .nil
    | cons a acts' =>
      cases pbs with
      | nil =>
        cases a with
        | keep => exact .cons (fun _ => .hlt) (rewriteKeptBlocks_noSameExt acts' .nil bs hbs)
        | dup | drop => exact rewriteKeptBlocks_noSameExt acts' .nil bs hbs
      | cons pb pbs' =>
        cases a with
        | keep =>
          exact .cons (fun xs => rewriteExpr_noSameExt pb _ (hb _))
            (rewriteKeptBlocks_noSameExt acts' pbs' bs hbs)
        | dup | drop => exact rewriteKeptBlocks_noSameExt acts' pbs' bs hbs
end

private theorem ite_func {as rs : List Ty} (c : Prop) [Decidable c]
    (t e : Func as rs) (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as) :
    (if c then t else e) V L xs = if c then t V L xs else e V L xs := by
  by_cases h : c <;> simp [h]

private theorem tailDupOnce_noSameExt (cfg : TailDup.TailDupConfig) {as rs : List Ty}
    (f : Func as rs)
    (hf : ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as), ExprNoSameExtGen (f V L xs))
    (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as) :
    ExprNoSameExtGen ((Func.tailDupOnce f cfg).1 V L xs) := by
  dsimp only [Func.tailDupOnce]
  have htf : TFlatNoSameExt (reifyFunc f) := toTFlat_noSameExt _ _ _ (hf K KL _)
  split
  · dsimp only [Func.tailDupWithPlan]
    rw [ite_func]
    split
    · exact rewriteExpr_noSameExt _ _
        (denote_dupSafe V L (reifyFunc f) _ [] htf fun _ hp => nomatch hp)
    · dsimp only [denoteFunc]
      exact denote_noSameExt V L (reifyFunc f) _ [] htf
  · dsimp only [denoteFunc]
    exact denote_noSameExt V L (reifyFunc f) _ [] htf

private theorem tailDupLoop_noSameExt (cfg : TailDup.TailDupConfig) :
    ∀ (fuel : Nat) {as rs : List Ty} (f : Func as rs),
      (∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
        ExprNoSameExtGen (f V L xs)) →
      ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
        ExprNoSameExtGen ((Func.tailDupLoop cfg fuel f) V L xs)
  | 0, _, _, _, hf, V, L, xs => hf V L xs
  | fuel + 1, _, _, f, hf, V, L, xs => by
    dsimp only [Func.tailDupLoop]
    rw [ite_func]
    split
    · exact tailDupLoop_noSameExt cfg fuel _ (tailDupOnce_noSameExt cfg f hf) V L xs
    · exact tailDupOnce_noSameExt cfg f hf V L xs

private theorem tailDup_noSameExt {as rs : List Ty} (f : Func as rs)
    (hf : ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as), ExprNoSameExtGen (f V L xs))
    (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as) :
    ExprNoSameExtGen ((Func.tailDup f) V L xs) :=
  tailDupLoop_noSameExt _ _ f hf V L xs

private theorem renorm_lateCondThread_noSameExt {as rs : List Ty} (g : Func as rs)
    (xs : Tup Rega.VNat as) :
    ExprNoSameExt (Func.renorm (Func.lateCondThread g) Rega.VNat Rega.LNat xs) := by
  rw [Func.lateCondThread_eq g]
  have hfold : ∀ {as rs : List Ty} (h : Func as rs)
      (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
      ExprNoSameExtGen ((Func.fold h) V L xs) := fun h V L xs =>
    fold_noSameExt _ _
  have hdceP : ∀ {as rs : List Ty} (h : Func as rs),
      (∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as), ExprNoSameExtGen (h V L xs)) →
      ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
        ExprNoSameExtGen ((Func.dceP h) V L xs) := by
    intro as rs h hh V L xs
    dsimp only [Func.dceP, Func.dcePWith]
    split
    · exact dceSweepP_noSameExt _ _ (hh _ _ _)
    · dsimp only [Func.dceWith]
      exact dceSweep_noSameExt _ _ (hh _ _ _)
  have hmerge : ∀ {as rs : List Ty} (h : Func as rs),
      (∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as), ExprNoSameExtGen (h V L xs)) →
      ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
        ExprNoSameExtGen ((Func.mergeRets h) V L xs) := by
    intro as rs h hh V L xs
    rw [Func.mergeRets_eq h]
    dsimp only
    split
    · refine .group (fun _ => .cons (fun _ => .ret) .nil) (fun ls => ?_)
      exact mergeRets_noSameExt ls.1 _ (hh V L xs)
    · exact hh V L xs
  have hren : ∀ {as rs : List Ty} (h : Func as rs),
      (∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as), ExprNoSameExtGen (h V L xs)) →
      ∀ (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as),
        ExprNoSameExtGen ((Func.renorm h) V L xs) := by
    intro as rs h hh V L xs
    dsimp only [Func.renorm, denoteFunc, reifyFunc]
    exact denote_noSameExt V L _ _ _ (toTFlat_noSameExt _ _ _ (hh K KL _))
  exact exprNoSameExtGen_to_expr _
    ((hren _ (hmerge _ (tailDup_noSameExt _ (hdceP _ (hfold _))))) Rega.VNat Rega.LNat xs)

theorem fnNoSameExt_mid (lt : LegalTarget) (f : Fn) :
    ExprNoSameExt ((f.mid lt).body Rega.VNat Rega.LNat (Tup.levels (f.mid lt).as 0)) :=
  Eq.mp
    (congrArg (fun b : Func (f.mid lt).as (f.mid lt).rs =>
      ExprNoSameExt (b Rega.VNat Rega.LNat (Tup.levels (f.mid lt).as 0)))
      (Fn.midStage_eq lt f.earlyOpt).symm)
    (renorm_lateCondThread_noSameExt _ _)

/-! ## 2d. Top-Level Transport (`vllX64_lowerFn_eq`, `compileFn`, `compile`, `compileModule`) -/

private theorem listNodup_decEq_congr {α : Type} (i₁ i₂ : DecidableEq α) (xs : List α) :
    @listNodup α (@instBEqOfDecidableEq α i₁) xs =
      @listNodup α (@instBEqOfDecidableEq α i₂) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [listNodup]
    rw [list_contains_decEq_congr i₁ i₂ xs x, ih]

private theorem x64CalleeSaved_contains_iff (r : Reg64) :
    x64Frame.calleeSaved.contains r = true ↔ r ∈ x64Frame.calleeSaved := by
  cases r <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals first
    | exact ⟨(fun _ => by simp), (fun _ => rfl)⟩
    | exact ⟨(fun h => False.elim (Bool.false_ne_true h)), (fun h => by simp at h)⟩

private theorem reg64_contains_callee_congr (d : DecidableEq Reg64) (r : Reg64) :
    @List.contains Reg64 (@instBEqOfDecidableEq Reg64 d) x64Isa.frame.calleeSaved r =
      x64Frame.calleeSaved.contains r := by
  have h1 : @List.contains Reg64 (@instBEqOfDecidableEq Reg64 d)
      x64Isa.frame.calleeSaved r = true ↔ r ∈ x64Frame.calleeSaved := by
    letI : DecidableEq Reg64 := d
    letI : BEq Reg64 := @instBEqOfDecidableEq Reg64 d
    simp [List.contains_eq_mem]
  have h2 := x64CalleeSaved_contains_iff r
  cases ha : @List.contains Reg64 (@instBEqOfDecidableEq Reg64 d)
      x64Isa.frame.calleeSaved r <;>
    cases hb : x64Frame.calleeSaved.contains r
  · rfl
  · have ht := h1.mpr (h2.mp hb); rw [ha] at ht; cases ht
  · have ht := h2.mpr (h1.mp ha); rw [hb] at ht; cases ht
  · rfl

private theorem savedNoRsp_of_all (saved : List Reg64) (d : DecidableEq Reg64)
    (h : (saved.all fun x => @List.contains Reg64 (@instBEqOfDecidableEq Reg64 d)
      x64Isa.frame.calleeSaved x) = true) :
    savedNoRsp saved = true := by
  induction saved with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [savedNoRsp, List.all_cons, Bool.and_eq_true]
    exact ⟨(reg64_contains_callee_congr d r).symm.trans h.1, ih h.2⟩

private theorem vllDir_append_asm (a b : List vllX64Isa.Directive) :
    asmX64List (a ++ b) = asmX64List a ++ asmX64List b :=
  asmX64List_append a b

private theorem lowerFn_eq_vllIsaR (h : x64Isa.Hints) (E : Rega.Ext) (f : Fn) :
    Rega.lowerFn vllX64Isa h E f = Rega.lowerFn vllX64IsaR h E f := by
  have aux : ∀ {I₁ I₂ : Isa} (hI : I₁ = I₂)
      (hh₁ : I₁.Hints = x64Isa.Hints) (hh₂ : I₂.Hints = x64Isa.Hints),
      HEq (Rega.lowerFn I₁ (hh₁ ▸ h) E f) (Rega.lowerFn I₂ (hh₂ ▸ h) E f) := by
    intro I₁ I₂ hI hh₁ hh₂; subst hI; exact HEq.rfl
  exact eq_of_heq (aux vllX64IsaR_eq.symm rfl rfl)

theorem vllX64_lowerFn_eq (h : x64Isa.Hints) (hh : hintsNoRsp h = true) (E : Rega.Ext) (f : Fn)
    (hf : ExprNoSameExt (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0))) :
    (Rega.lowerFn vllX64Isa h E f).map asmX64List = Rega.lowerFn x64Isa h E f := by
  rw [lowerFn_eq_vllIsaR]
  dsimp only [Rega.lowerFn]
  have hnd_eq :
      (@listNodup _ (@instBEqOfDecidableEq _ vllX64IsaR.decEqReg) h.saved &&
        h.saved.all (fun x => @List.contains _ (@instBEqOfDecidableEq _ vllX64IsaR.decEqReg)
          vllX64IsaR.frame.calleeSaved x)) =
      (@listNodup _ (@instBEqOfDecidableEq _ x64Isa.decEqReg) h.saved &&
        h.saved.all (fun x => @List.contains _ (@instBEqOfDecidableEq _ x64Isa.decEqReg)
          x64Isa.frame.calleeSaved x)) := by
    rw [listNodup_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg h.saved]
    congr 2
  rw [hnd_eq]
  cases hnd : (@listNodup _ (@instBEqOfDecidableEq _ x64Isa.decEqReg) h.saved &&
      h.saved.all (fun x => @List.contains _ (@instBEqOfDecidableEq _ x64Isa.decEqReg)
        x64Isa.frame.calleeSaved x)) with
  | false => rfl
  | true =>
    have hs : savedNoRsp h.saved = true :=
      savedNoRsp_of_all h.saved x64Isa.decEqReg (Bool.and_eq_true_iff.mp hnd).2
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [vllR_assignArgs_eq, vllR_assignRets_eq]
    cases hal : x64Isa.assignArgs f.as with
    | none => rfl
    | some argLocs =>
      cases x64Isa.assignRets f.rs with
      | none => rfl
      | some _ =>
        dsimp only
        have harg_no : locsNoRsp argLocs = true :=
          assignArgs_locsNoRsp (by rw [vllR_assignArgs_eq]; exact hal)
        obtain ⟨hbp_eq, hbp_no⟩ := bindAbiParams_eq_and_noRsp argLocs 0
          { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } harg_no rfl
        cases h0 : Rega.bindAbiParams vllX64IsaR argLocs 0
            { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
        | none =>
          have hx : Rega.bindAbiParams x64Isa argLocs 0
              { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } = none := by
            rw [← hbp_eq, h0]; rfl
          rw [hx]; rfl
        | some st0 =>
          have hx : Rega.bindAbiParams x64Isa argLocs 0
              { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } =
              some (symStToX64 st0) := by rw [← hbp_eq, h0]; rfl
          rw [hx]
          dsimp only
          have hno0 := hbp_no st0 h0
          have ih := lowerExpr_eq h hh hs E f.name (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0))
            f.as.length 0 0 st0 none .empty .empty hno0 hf
          cases hl0 : Rega.lowerExpr vllX64IsaR h E f.name
              (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
          | error err =>
            have hlx : Rega.lowerExpr x64Isa h E f.name
                (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0
                (symStToX64 st0) none = .error err := by rw [← ih, hl0]; rfl
            rw [hlx]; rfl
          | ok res =>
            rcases res with ⟨c, nv, nl, ip⟩
            have hlx : Rega.lowerExpr x64Isa h E f.name
                (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0
                (symStToX64 st0) none = .ok (asmX64List c, nv, nl, ip) := by
              rw [← ih, hl0]; rfl
            rw [hlx]
            dsimp only [Except.map, Rega.fnPrologue]
            have hlbl : asmX64List [vllX64FrameR.label f.name] = [x64Isa.frame.label f.name] :=
              vllR_label_eq f.name
            have hscs := saveCs_eq h.nslots h.saved
            have hzl : Rega.isZeroLeaf vllX64IsaR h E = Rega.isZeroLeaf x64Isa h E := rfl
            cases hz : Rega.isZeroLeaf vllX64IsaR h E with
            | true =>
              have hzx : Rega.isZeroLeaf x64Isa h E = true := hzl.symm.trans hz
              simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hlbl
              simp only [asmX64List] at hscs
              simp only [hzx, ↓reduceIte, asmX64List, List.flatMap_cons,
                List.flatMap_append, List.nil_append, hlbl, hscs, List.cons_append]
            | false =>
              have hzx : Rega.isZeroLeaf x64Isa h E = false := hzl.symm.trans hz
              simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hlbl
              have hpr := vllR_prologue_eq h.totalSlots
              simp only [asmX64List] at hscs hpr
              simp only [hzx, Bool.false_eq_true, ↓reduceIte, asmX64List,
                List.flatMap_cons, List.flatMap_append, List.nil_append, hlbl, hscs, hpr,
                List.cons_append]

theorem vllX64_effFrame_eq (h : x64Isa.Hints) (ext : Rega.Ext) :
    Rega.effFrame vllX64Isa h ext = Rega.effFrame x64Isa h ext := rfl

theorem vllX64_checkAndBoundExt_eq (raBytes : Nat) (exits : List Sym) (nX : Nat)
    (bounds : List (SigEntry × Nat)) (h : x64Isa.Hints) (ext : Rega.Ext) :
    checkAndBoundExt vllX64Isa raBytes exits nX bounds h ext =
      checkAndBoundExt x64Isa raBytes exits nX bounds h ext := rfl

theorem vllX64_compileFn_eq (lt : LegalTarget) (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (f : Fn) :
    (compileFn vllX64Isa lt h f).map asmX64List = compileFn x64Isa lt h f :=
  vllX64_lowerFn_eq h hh (f.mid lt).ext (f.mid lt) (fnNoSameExt_mid lt f)

theorem vllX64_compile_eq (lt : LegalTarget) :
    ∀ (fs : List Fn) (hints : List x64Isa.Hints),
      hints.all hintsNoRsp = true →
      (compile vllX64Isa lt fs hints).map asmX64List = compile x64Isa lt fs hints
  | [], [], _ => rfl
  | [], _ :: _, _ | _ :: _, [], _ => rfl
  | f :: fs, h :: hs, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    dsimp only [compile]
    have h1 := vllX64_compileFn_eq lt h hall.1 f
    have h2 := vllX64_compile_eq lt fs hs hall.2
    cases c1 : compileFn vllX64Isa lt h f with
    | error e =>
      have cx : compileFn x64Isa lt h f = .error e := by rw [← h1, c1]; rfl
      rw [cx]; rfl
    | ok code1 =>
      have cx : compileFn x64Isa lt h f = .ok (asmX64List code1) := by rw [← h1, c1]; rfl
      rw [cx]
      cases c2 : compile vllX64Isa lt fs hs with
      | error e =>
        have c2x : compile x64Isa lt fs hs = .error e := by rw [← h2, c2]; rfl
        rw [c2x]; rfl
      | ok code2 =>
        have c2x : compile x64Isa lt fs hs = .ok (asmX64List code2) := by rw [← h2, c2]; rfl
        rw [c2x]
        simp only [Except.map, vllDir_append_asm]

theorem vllX64_compileModule_eq (lt : LegalTarget) (raBytes : Nat) (exits : List Sym) (nX : Nat) :
    ∀ (extCallees : List (SigEntry × Nat)) (fs : List Fn) (hints : List x64Isa.Hints),
      hints.all hintsNoRsp = true →
      (compileModule vllX64Isa lt raBytes extCallees exits nX fs hints).map
          (fun p => (asmX64List p.1, p.2)) =
        compileModule x64Isa lt raBytes extCallees exits nX fs hints
  | _, [], [], _ => rfl
  | _, [], _ :: _, _ | _, _ :: _, [], _ => rfl
  | extCallees, f :: fs, h :: hs, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    dsimp only [compileModule]
    split
    · have hfn := vllX64_lowerFn_eq h hall.1 (Fn.midFromEarly lt f.earlyOpt).ext
        (Fn.midFromEarly lt f.earlyOpt) (fnNoSameExt_mid lt f)
      rw [vllX64_checkAndBoundExt_eq]
      cases hl : Rega.lowerFn vllX64Isa h (Fn.midFromEarly lt f.earlyOpt).ext
          (Fn.midFromEarly lt f.earlyOpt) with
      | error e =>
        have hlx : Rega.lowerFn x64Isa h (Fn.midFromEarly lt f.earlyOpt).ext
            (Fn.midFromEarly lt f.earlyOpt) = .error e := by rw [← hfn, hl]; rfl
        rw [hlx]
        cases checkAndBoundExt x64Isa raBytes exits nX extCallees h
            (Fn.midFromEarly lt f.earlyOpt).ext <;> rfl
      | ok c =>
        have hlx : Rega.lowerFn x64Isa h (Fn.midFromEarly lt f.earlyOpt).ext
            (Fn.midFromEarly lt f.earlyOpt) = .ok (asmX64List c) := by rw [← hfn, hl]; rfl
        rw [hlx]
        cases hchk : checkAndBoundExt x64Isa raBytes exits nX extCallees h
            (Fn.midFromEarly lt f.earlyOpt).ext with
        | none => rfl
        | some b =>
          have ih := vllX64_compileModule_eq lt raBytes exits nX
            (((Fn.midFromEarly lt f.earlyOpt).sig, b) :: extCallees) fs hs hall.2
          cases hrest : compileModule vllX64Isa lt raBytes
              (((Fn.midFromEarly lt f.earlyOpt).sig, b) :: extCallees) exits nX fs hs with
          | error e =>
            have hrx : compileModule x64Isa lt raBytes
                (((Fn.midFromEarly lt f.earlyOpt).sig, b) :: extCallees) exits nX fs hs =
                .error e := by rw [← ih, hrest]; rfl
            simp only [hrest, hrx]; rfl
          | ok p =>
            rcases p with ⟨cs, bs⟩
            have hrx : compileModule x64Isa lt raBytes
                (((Fn.midFromEarly lt f.earlyOpt).sig, b) :: extCallees) exits nX fs hs =
                .ok (asmX64List cs, bs) := by rw [← ih, hrest]; rfl
            simp only [hrest, hrx, Except.map, vllDir_append_asm]
    · rfl

end LeanQbe.T.Amd64
