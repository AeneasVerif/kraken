module

public import LeanQbe.T.Bootstrap0.Sound0Part1
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part2`): `Isel0` & `Frame0` `FallsTo` / `Program.wp` Specs

Provides self-contained `Dir0` forward-emission / `patchEpilogues0` stability lemmas and x86-64
functional correctness specifications (`x64ScalarMach.FallsTo` / `_root_.Program.wp`) for
`Frame0` and `Isel0` helpers in `LeanQbe.T.Bootstrap0.Compiler0`:
1. Forward `Dir0` prepend decomposition & `ListNoSpZero0` / `patchEpilogues0` invariants.
2. `Frame0` specs: `emitSpAdj0` (prologue/epilogue), `emitSlotMem0` (slot ld/st), `emitCanon0`.
3. `Isel0` operand & ABI loading: `emitLoadArg0`, `loadRegArgs0` (`canon = false` and `true`).
4. Scalar ALU, shift, compare/select, conversion, & div/rem (`emitOp0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. `emitFwd0`, `ListNoSpZero0`, & Prepend Decomposition -/

/-- Reverse a reverse-accumulated `List Dir0` into execution order. -/
@[expose] def emitFwd0 (rs : List Dir0) : List Dir0 :=
  rs.reverse

/-- Predicate ensuring a `Dir0` list contains no placeholder epilogue marker `.spAdd false 0`. -/
@[expose] def ListNoSpZero0 (xs : List Dir0) : Prop :=
  ∀ d ∈ xs, d ≠ .spAdd false 0

theorem emitFwd0_revDirAux0 (xs : List Dir0) : revDirAux0 xs [] = emitFwd0 xs := by
  rw [revDirAux0_eq, List.append_nil]; rfl

theorem emitFwd0_append (xs ys : List Dir0) :
    emitFwd0 (xs ++ ys) = emitFwd0 ys ++ emitFwd0 xs :=
  List.reverse_append

theorem emitFwd0_cons (d : Dir0) (xs : List Dir0) :
    emitFwd0 (d :: xs) = emitFwd0 xs ++ [d] :=
  List.reverse_cons

theorem listNoSpZero0_nil : ListNoSpZero0 [] := fun _ hm => nomatch hm

theorem listNoSpZero0_cons {d : Dir0} {xs : List Dir0} (hd : d ≠ .spAdd false 0)
    (hxs : ListNoSpZero0 xs) : ListNoSpZero0 (d :: xs) := fun x hx =>
  (List.mem_cons.mp hx).elim (fun e => e ▸ hd) (hxs x)

theorem listNoSpZero0_append {xs ys : List Dir0} (hx : ListNoSpZero0 xs)
    (hy : ListNoSpZero0 ys) : ListNoSpZero0 (xs ++ ys) := fun d hd =>
  (List.mem_append.mp hd).elim (hx d) (hy d)

theorem listNoSpZero0_reverse {xs : List Dir0} (h : ListNoSpZero0 xs) :
    ListNoSpZero0 xs.reverse := fun d hd =>
  h d (List.mem_reverse.mp hd)

private theorem patchDir0_of_ne {bytes : UInt64} {d : Dir0} (hd : d ≠ .spAdd false 0) :
    patchDir0 bytes d = [d] := by
  cases d with
  | spAdd isSub imm =>
    cases isSub
    · have hne : imm ≠ 0 := fun e => hd (e ▸ rfl)
      by_cases h0 : imm = 0
      · exact absurd h0 hne
      · simp [patchDir0]
    · rfl
  | _ => rfl

theorem patchEpilogues0_of_listNoSpZero0 (bytes : UInt64) {xs : List Dir0}
    (h : ListNoSpZero0 xs) : patchEpilogues0 bytes xs [] = xs := by
  rw [patchEpilogues0_eq]
  induction xs with
  | nil => rfl
  | cons d rest ih =>
    rw [List.flatMap_cons, patchDir0_of_ne (h d List.mem_cons_self), List.singleton_append]
    exact congrArg (d :: ·) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem patchEpilogues0_prepend (bytes : UInt64) {d acc : List Dir0}
    (h : ListNoSpZero0 d) :
    patchEpilogues0 bytes (emitFwd0 (d ++ acc)) [] =
      patchEpilogues0 bytes (emitFwd0 acc) [] ++ emitFwd0 d := by
  rw [emitFwd0_append, patchEpilogues0_append]
  exact congrArg (_ ++ ·)
    (patchEpilogues0_of_listNoSpZero0 bytes (xs := emitFwd0 d) (listNoSpZero0_reverse h))

theorem patchEpilogues0_spZero_cons (bytes : UInt64) (acc : List Dir0) :
    patchEpilogues0 bytes (emitFwd0 (.spAdd false 0 :: acc)) [] =
      patchEpilogues0 bytes (emitFwd0 acc) [] ++ emitFwd0 (emitSpAdj0 false bytes []) := by
  rw [emitFwd0_cons, patchEpilogues0_append, patchEpilogues0_eq]
  congr 1
  rw [patchEpilogues0_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil, patchDir0,
    emitFwd0_revDirAux0]

private theorem comp_acc {f g : List Dir0 → List Dir0}
    (hf : ∀ a, f a = f [] ++ a ∧ ListNoSpZero0 (f []))
    (hg : ∀ a, g a = g [] ++ a ∧ ListNoSpZero0 (g [])) (acc : List Dir0) :
    g (f acc) = g (f []) ++ acc ∧ ListNoSpZero0 (g (f [])) := by
  obtain ⟨e1, n1⟩ := hf acc
  obtain ⟨e2, n2⟩ := hg (f acc)
  obtain ⟨e20, _⟩ := hg (f [])
  rw [e20, e2, e1, ← List.append_assoc]
  exact ⟨rfl, listNoSpZero0_append n2 n1⟩

theorem pushDRR0_acc (tag : UInt32) (w : Width) (rd rs : Reg64) (acc : List Dir0) :
    pushDRR0 tag w rd rs acc = pushDRR0 tag w rd rs [] ++ acc ∧
      ListNoSpZero0 (pushDRR0 tag w rd rs []) := by
  dsimp only [pushDRR0]; repeat' split
  all_goals exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩

theorem pushDUnary0_acc (tag : UInt32) (w : Width) (rd rs : Reg64) (acc : List Dir0) :
    pushDUnary0 tag w rd rs acc = pushDUnary0 tag w rd rs [] ++ acc ∧
      ListNoSpZero0 (pushDUnary0 tag w rd rs []) := by
  dsimp only [pushDUnary0]; repeat' split
  all_goals exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩

theorem pushDImm0_acc (tag : UInt32) (rd : Reg64) (imm : UInt64) (acc : List Dir0)
    (htag : tag ≠ 1 ∨ imm ≠ 0) :
    pushDImm0 tag rd imm acc = pushDImm0 tag rd imm [] ++ acc ∧
      ListNoSpZero0 (pushDImm0 tag rd imm []) := by
  dsimp only [pushDImm0]
  split
  · exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
  · split
    · rename_i h1
      have him : imm ≠ 0 :=
        htag.elim (fun hne => absurd (decide_eq_true_eq.mp h1) hne) id
      exact ⟨rfl, listNoSpZero0_cons (fun he => him (Dir0.spAdd.inj he).2) listNoSpZero0_nil⟩
    · split <;> exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩

theorem emitCanon0_acc (w : Width) (r : Reg64) (acc : List Dir0) :
    emitCanon0 w r acc = emitCanon0 w r [] ++ acc ∧ ListNoSpZero0 (emitCanon0 w r []) := by
  cases w
  · exact pushDRR0_acc 1 .W8 r r acc
  · exact pushDRR0_acc 1 .W16 r r acc
  · exact pushDRR0_acc 0 .W32 r r acc
  · exact ⟨rfl, listNoSpZero0_nil⟩

theorem emitSlotMem0_acc (isLd : Bool) (reg : Reg64) (slot : UInt32) (acc : List Dir0) :
    emitSlotMem0 isLd reg slot acc = emitSlotMem0 isLd reg slot [] ++ acc ∧
      ListNoSpZero0 (emitSlotMem0 isLd reg slot []) := by
  cases isLd
  · simp only [emitSlotMem0, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
    · obtain ⟨h1, h2⟩ := pushDImm0_acc 0 .r10 (UInt64.mul slot.toUInt64 8) acc (Or.inl (by decide))
      rw [h1]; exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) h2⟩
  · simp only [emitSlotMem0, ↓reduceIte]
    split
    · exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
    · obtain ⟨h1, h2⟩ := pushDImm0_acc 0 .r10 (UInt64.mul slot.toUInt64 8) acc (Or.inl (by decide))
      rw [h1]; exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) h2⟩

theorem emitLoadArg0_acc (rd : Reg64) (a : Arg0) (venv : List UInt32) (vslot : Array Nat)
    (acc : List Dir0) :
    emitLoadArg0 rd a venv vslot acc = emitLoadArg0 rd a venv vslot [] ++ acc ∧
      ListNoSpZero0 (emitLoadArg0 rd a venv vslot []) := by
  cases a with
  | var idx => exact emitSlotMem0_acc true rd (arrGetU0 vslot (listGetU32 venv idx)) acc
  | immBool b => exact pushDImm0_acc 0 rd (if b then 1 else 0) acc (Or.inl (by decide))
  | immBits w val => exact pushDImm0_acc 0 rd (maskImmW0 w val) acc (Or.inl (by decide))

theorem loadRegArgs0_acc (cfg : LoadCfg0) (ts : List Ty0) (args : List Arg0) (i : UInt32)
    (acc : List Dir0) :
    loadRegArgs0 cfg ts args i acc = loadRegArgs0 cfg ts args i [] ++ acc ∧
      ListNoSpZero0 (loadRegArgs0 cfg ts args i []) := by
  induction args generalizing ts i acc with
  | nil => exact ⟨rfl, listNoSpZero0_nil⟩
  | cons a aRest ih =>
    cases ts with
    | nil =>
      let f := emitLoadArg0 (abiRegAt0 cfg.useRet i) a cfg.venv cfg.vslot
      have hf : ∀ x, f x = f [] ++ x ∧ ListNoSpZero0 (f []) :=
        fun x => emitLoadArg0_acc _ a cfg.venv cfg.vslot x
      exact comp_acc hf (fun x => ih [] (i + 1) x) acc
    | cons t tRest =>
      let rd := abiRegAt0 cfg.useRet i
      let f := emitLoadArg0 rd a cfg.venv cfg.vslot
      let g := fun x => if cfg.canon then emitCanon0 (tyWidth0 t) rd x else x
      have hf : ∀ x, f x = f [] ++ x ∧ ListNoSpZero0 (f []) :=
        fun x => emitLoadArg0_acc rd a cfg.venv cfg.vslot x
      have hg : ∀ x, g x = g [] ++ x ∧ ListNoSpZero0 (g []) := fun x => by
        dsimp only [g]; cases cfg.canon
        · exact ⟨rfl, listNoSpZero0_nil⟩
        · exact emitCanon0_acc (tyWidth0 t) rd x
      exact comp_acc (fun x => comp_acc hf hg x) (fun x => ih tRest (i + 1) x) acc

private theorem emitUn0_acc (u : UnOp0) (t : Ty0) (acc : List Dir0) :
    emitUn0 u t acc = emitUn0 u t [] ++ acc ∧ ListNoSpZero0 (emitUn0 u t []) := by
  cases u with
  | copy => exact comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (emitCanon0_acc (tyWidth0 t) .rax) acc
  | neg =>
    exact comp_acc
      (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (pushDUnary0_acc 1 (tyWidth0 t) .rax .rax))
      (emitCanon0_acc (tyWidth0 t) .rax) acc
  | not =>
    cases t with
    | bool =>
      exact comp_acc
        (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
          (comp_acc (fun x => pushDImm0_acc 0 .r11 1 x (Or.inl (by decide)))
            (pushDUnary0_acc 6 .W32 .rax .r11)))
        (pushDRR0_acc 1 .W8 .rax .rax) acc
    | b8 =>
      exact comp_acc
        (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
          (pushDUnary0_acc 0 (tyWidth0 .b8) .rax .rax))
        (emitCanon0_acc (tyWidth0 .b8) .rax) acc
    | b16 =>
      exact comp_acc
        (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
          (pushDUnary0_acc 0 (tyWidth0 .b16) .rax .rax))
        (emitCanon0_acc (tyWidth0 .b16) .rax) acc
    | b32 =>
      exact comp_acc
        (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
          (pushDUnary0_acc 0 (tyWidth0 .b32) .rax .rax))
        (emitCanon0_acc (tyWidth0 .b32) .rax) acc
    | b64 =>
      exact comp_acc
        (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
          (pushDUnary0_acc 0 (tyWidth0 .b64) .rax .rax))
        (emitCanon0_acc (tyWidth0 .b64) .rax) acc

private theorem emitBinShift0_acc (b : BinOp0) (t : Ty0) (acc : List Dir0) :
    emitBinShift0 b t acc = emitBinShift0 b t [] ++ acc ∧
      ListNoSpZero0 (emitBinShift0 b t []) := by
  dsimp only [emitBinShift0]
  let sk : ShiftKind0 :=
    match b with
    | .shl => .shl | .lshr => .lshr | .ashr => .ashr | .rotl => .rotl | _ => .rotr
  have hf1 : ∀ x, pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi x) =
      pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi []) ++ x ∧
      ListNoSpZero0 (pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi [])) :=
    comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (pushDRR0_acc 0 .W64 .rcx .rsi)
  have hf2 : ∀ x, (match tyWidth0 t with
        | .W8 => pushDImm0 3 .rcx 7 x | .W16 => pushDImm0 3 .rcx 15 x | _ => x) =
      (match tyWidth0 t with
        | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []) ++ x ∧
      ListNoSpZero0 (match tyWidth0 t with
        | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []) := by
    intro x; cases tyWidth0 t
    · exact pushDImm0_acc 3 .rcx 7 x (Or.inl (by decide))
    · exact pushDImm0_acc 3 .rcx 15 x (Or.inl (by decide))
    · exact ⟨rfl, listNoSpZero0_nil⟩
    · exact ⟨rfl, listNoSpZero0_nil⟩
  have hf3 : ∀ x, pushDShift0 (tyWidth0 t) sk .rax x =
      pushDShift0 (tyWidth0 t) sk .rax [] ++ x ∧
      ListNoSpZero0 (pushDShift0 (tyWidth0 t) sk .rax []) := fun x =>
    ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
  exact comp_acc (comp_acc (comp_acc hf1 hf2) hf3) (emitCanon0_acc (tyWidth0 t) .rax) acc

private theorem emitBinAlu0_acc (b : BinOp0) (t : Ty0) (acc : List Dir0) :
    emitBinAlu0 b t acc = emitBinAlu0 b t [] ++ acc ∧ ListNoSpZero0 (emitBinAlu0 b t []) := by
  dsimp only [emitBinAlu0]
  cases t with
  | bool =>
    exact comp_acc
      (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (fun _ =>
        ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩))
      (pushDRR0_acc 1 .W8 .rax .rax) acc
  | b8 =>
    exact comp_acc
      (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (fun _ =>
        ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩))
      (pushDRR0_acc 1 .W8 .rax .rax) acc
  | b16 | b32 | b64 =>
    exact comp_acc
      (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (fun _ =>
        ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩))
      (emitCanon0_acc (tyWidth0 _) .rax) acc

private theorem emitCmpSelect0_acc (isSel : Bool) (co : CmpOp) (t : Ty0) (acc : List Dir0) :
    emitCmpSelect0 isSel co t acc = emitCmpSelect0 isSel co t [] ++ acc ∧
      ListNoSpZero0 (emitCmpSelect0 isSel co t []) := by
  dsimp only [emitCmpSelect0]
  cases isSel with
  | true =>
    let cw := match t with | .b64 => Width.W64 | _ => Width.W32
    exact comp_acc (comp_acc (pushDRR0_acc 4 .W8 .rdi .rdi) (pushDRR0_acc 0 cw .rax .rdx))
      (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩) acc
  | false =>
    let f : List Dir0 → List Dir0 :=
      fun x => .setcc (condOf0 co) .rax :: .cmpRR (tyWidth0 t) .rdi .rsi :: x
    exact comp_acc (f := f)
      (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h)
        (listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil)⟩)
      (pushDRR0_acc 1 .W8 .rax .rax) acc

private theorem emitConvZextTrunc0_acc (op : ConvOp0) (wSrc wDst : Width) (acc : List Dir0) :
    emitConvZextTrunc0 op wSrc wDst acc = emitConvZextTrunc0 op wSrc wDst [] ++ acc ∧
      ListNoSpZero0 (emitConvZextTrunc0 op wSrc wDst []) := by
  dsimp only [emitConvZextTrunc0]
  cases op with
  | ofBool => exact pushDRR0_acc 1 .W8 .rax .rdi acc
  | zext =>
    cases widthEq0 wSrc wDst
    · dsimp only
      cases wSrc
      · exact pushDRR0_acc 1 .W8 .rax .rdi acc
      · exact pushDRR0_acc 1 .W16 .rax .rdi acc
      · exact pushDRR0_acc 0 .W32 .rax .rdi acc
      · exact pushDRR0_acc 0 .W32 .rax .rdi acc
    · exact comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (emitCanon0_acc wDst .rax) acc
  | sext | trunc =>
    exact comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (emitCanon0_acc wDst .rax) acc

private theorem emitConvSext0_acc (wSrc wDst : Width) (acc : List Dir0) :
    emitConvSext0 wSrc wDst acc = emitConvSext0 wSrc wDst [] ++ acc ∧
      ListNoSpZero0 (emitConvSext0 wSrc wDst []) := by
  dsimp only [emitConvSext0]
  split
  · exact comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (emitCanon0_acc wSrc .rax) acc
  · split
    · exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
    · exact comp_acc (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩)
        (emitCanon0_acc wDst .rax) acc

private theorem emitDiv0_acc (op : DivOp0) (w : Width) (acc : List Dir0) :
    emitDiv0 op w acc = emitDiv0 op w [] ++ acc ∧ ListNoSpZero0 (emitDiv0 op w []) := by
  dsimp only [emitDiv0]
  let isS := match op with | .sdiv | .srem => true | _ => false
  let isR := match op with | .urem | .srem => true | _ => false
  let dt : UInt32 := if isS then 3 else 2
  have hTail : ∀ (w' : Width) (f : List Dir0 → List Dir0),
      (∀ x, f x = f [] ++ x ∧ ListNoSpZero0 (f [])) → ∀ x,
      (if isR then pushDRR0 0 w' .rax .rdx (f x) else f x) =
      (if isR then pushDRR0 0 w' .rax .rdx (f []) else f []) ++ x ∧
      ListNoSpZero0 (if isR then pushDRR0 0 w' .rax .rdx (f []) else f []) := by
    intro w' f hf x; cases isR
    · exact hf x
    · exact comp_acc hf (pushDRR0_acc 0 w' .rax .rdx) x
  cases w with
  | W64 =>
    exact hTail .W64 _ (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi)
      (pushDUnary0_acc dt .W64 .rax .rsi)) acc
  | W32 =>
    exact hTail .W32 _ (comp_acc (comp_acc (pushDRR0_acc 0 .W32 .rax .rdi)
      (pushDRR0_acc 0 .W32 .r11 .rsi)) (pushDUnary0_acc dt .W32 .rax .r11)) acc
  | W8 =>
    have hpre : ∀ x, (if isS then pushDMovsx0 .W32 .r11 .W8 .rsi (pushDMovsx0 .W32 .rax .W8 .rdi x)
        else pushDRR0 1 .W8 .r11 .rsi (pushDRR0 1 .W8 .rax .rdi x)) =
        (if isS then pushDMovsx0 .W32 .r11 .W8 .rsi (pushDMovsx0 .W32 .rax .W8 .rdi [])
        else pushDRR0 1 .W8 .r11 .rsi (pushDRR0 1 .W8 .rax .rdi [])) ++ x ∧
        ListNoSpZero0 (if isS
          then pushDMovsx0 .W32 .r11 .W8 .rsi (pushDMovsx0 .W32 .rax .W8 .rdi [])
          else pushDRR0 1 .W8 .r11 .rsi (pushDRR0 1 .W8 .rax .rdi [])) := by
      intro x; cases isS
      · exact comp_acc (pushDRR0_acc 1 .W8 .rax .rdi) (pushDRR0_acc 1 .W8 .r11 .rsi) x
      · exact comp_acc (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩)
          (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩) x
    exact comp_acc (hTail .W32 _ (comp_acc hpre (pushDUnary0_acc dt .W32 .rax .r11)))
      (emitCanon0_acc .W8 .rax) acc
  | W16 =>
    have hpre : ∀ x,
        (if isS then pushDMovsx0 .W32 .r11 .W16 .rsi (pushDMovsx0 .W32 .rax .W16 .rdi x)
         else pushDRR0 1 .W16 .r11 .rsi (pushDRR0 1 .W16 .rax .rdi x)) =
        (if isS then pushDMovsx0 .W32 .r11 .W16 .rsi (pushDMovsx0 .W32 .rax .W16 .rdi [])
         else pushDRR0 1 .W16 .r11 .rsi (pushDRR0 1 .W16 .rax .rdi [])) ++ x ∧
        ListNoSpZero0 (if isS
          then pushDMovsx0 .W32 .r11 .W16 .rsi (pushDMovsx0 .W32 .rax .W16 .rdi [])
          else pushDRR0 1 .W16 .r11 .rsi (pushDRR0 1 .W16 .rax .rdi [])) := by
      intro x; cases isS
      · exact comp_acc (pushDRR0_acc 1 .W16 .rax .rdi) (pushDRR0_acc 1 .W16 .r11 .rsi) x
      · exact comp_acc (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩)
          (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩) x
    exact comp_acc (hTail .W32 _ (comp_acc hpre (pushDUnary0_acc dt .W32 .rax .r11)))
      (emitCanon0_acc .W16 .rax) acc

theorem emitOp0_acc (op : OpCode0) (acc : List Dir0) :
    emitOp0 op acc = emitOp0 op [] ++ acc ∧ ListNoSpZero0 (emitOp0 op []) := by
  cases op with
  | un u t => exact emitUn0_acc u t acc
  | bin b t =>
    cases b with
    | shl => exact emitBinShift0_acc .shl t acc
    | lshr => exact emitBinShift0_acc .lshr t acc
    | ashr => exact emitBinShift0_acc .ashr t acc
    | rotl => exact emitBinShift0_acc .rotl t acc
    | rotr => exact emitBinShift0_acc .rotr t acc
    | add => exact emitBinAlu0_acc .add t acc
    | sub => exact emitBinAlu0_acc .sub t acc
    | mul => exact emitBinAlu0_acc .mul t acc
    | and => exact emitBinAlu0_acc .and t acc
    | or => exact emitBinAlu0_acc .or t acc
    | xor => exact emitBinAlu0_acc .xor t acc
  | cmp co t => exact emitCmpSelect0_acc false co t acc
  | select t => exact emitCmpSelect0_acc true .eq t acc
  | conv c m n =>
    cases c
    · exact emitConvZextTrunc0_acc .ofBool m n acc
    · exact emitConvZextTrunc0_acc .zext m n acc
    · exact emitConvSext0_acc m n acc
    · exact emitConvZextTrunc0_acc .trunc m n acc
  | div d w => exact emitDiv0_acc d w acc
  | umulw64 => exact ⟨rfl, listNoSpZero0_nil⟩

theorem emitSpAdj0_acc (isSub : Bool) (bytes : UInt64) (hb : isSub = true ∨ bytes ≠ 0)
    (acc : List Dir0) :
    emitSpAdj0 isSub bytes acc = emitSpAdj0 isSub bytes [] ++ acc ∧
      ListNoSpZero0 (emitSpAdj0 isSub bytes []) := by
  dsimp only [emitSpAdj0]
  split
  · exact pushDImm0_acc (if isSub then 2 else 1) .rsp bytes acc
      (by cases isSub; · right; rcases hb with h | h; exact absurd h Bool.false_ne_true; exact h
          · left; decide)
  · exact comp_acc (fun x => pushDImm0_acc 0 .r10 bytes x (Or.inl (by decide)))
      (pushDUnary0_acc (if isSub then 4 else 5) .W64 .r10 .r10) acc

theorem jumpStageLoop0_acc (args : List Arg0) (tmpIdx : UInt32) (venv : List UInt32)
    (vslot : Array Nat) (acc : List Dir0) :
    jumpStageLoop0 args tmpIdx venv vslot acc =
      jumpStageLoop0 args tmpIdx venv vslot [] ++ acc ∧
      ListNoSpZero0 (jumpStageLoop0 args tmpIdx venv vslot []) := by
  induction args generalizing tmpIdx acc with
  | nil => exact ⟨rfl, listNoSpZero0_nil⟩
  | cons a rest ih =>
    have hf := comp_acc (emitLoadArg0_acc .rax a venv vslot)
      (emitSlotMem0_acc false .rax tmpIdx)
    exact comp_acc hf (fun x => ih (tmpIdx + 1) x) acc

theorem jumpCopyLoop0_acc (tgts : List UInt32) (tmpIdx : UInt32) (acc : List Dir0) :
    jumpCopyLoop0 tgts tmpIdx acc =
      jumpCopyLoop0 tgts tmpIdx [] ++ acc ∧ ListNoSpZero0 (jumpCopyLoop0 tgts tmpIdx []) := by
  induction tgts generalizing tmpIdx acc with
  | nil => exact ⟨rfl, listNoSpZero0_nil⟩
  | cons s rest ih =>
    have hf := comp_acc (emitSlotMem0_acc true .rax tmpIdx) (emitSlotMem0_acc false .rax s)
    exact comp_acc hf (fun x => ih (tmpIdx + 1) x) acc

theorem emitJumpOneDir0_acc (tgts : List UInt32) (a : Arg0) (venv : List UInt32)
    (vslot : Array Nat) (acc : List Dir0) :
    emitJumpOneDir0 tgts a venv vslot acc =
      emitJumpOneDir0 tgts a venv vslot [] ++ acc ∧
      ListNoSpZero0 (emitJumpOneDir0 tgts a venv vslot []) := by
  dsimp only [emitJumpOneDir0]
  split
  · exact comp_acc (emitLoadArg0_acc .rax a venv vslot) (emitSlotMem0_acc false .rax _) acc
  · exact ⟨rfl, listNoSpZero0_nil⟩

theorem emitLinUmulw0_acc (a b : Arg0) (cur : RegaTask0) (st : RegaSt0) :
    emitLinUmulw0 a b cur st =
      emitLinUmulw0 a b cur { st with revDirs := [] } ++ st.revDirs ∧
      ListNoSpZero0 (emitLinUmulw0 a b cur { st with revDirs := [] }) := by
  dsimp only [emitLinUmulw0]
  exact comp_acc
    (comp_acc (emitLoadArg0_acc .rdi a cur.venv st.vslot)
      (emitLoadArg0_acc .rsi b cur.venv st.vslot))
    (comp_acc (pushDRR0_acc 0 .W64 .rax .rdi) (pushDRR0_acc 5 .W64 .rsi .rsi)) st.revDirs

theorem emitLinStore0_acc (t : Ty0) (val addr : Arg0) (cur : RegaTask0) (st : RegaSt0) :
    emitLinStore0 t val addr cur st =
      emitLinStore0 t val addr cur { st with revDirs := [] } ++ st.revDirs ∧
      ListNoSpZero0 (emitLinStore0 t val addr cur { st with revDirs := [] }) := by
  dsimp only [emitLinStore0]
  exact comp_acc
    (comp_acc (emitLoadArg0_acc .rdi val cur.venv st.vslot)
      (emitLoadArg0_acc .rsi addr cur.venv st.vslot))
    (pushDRR0_acc 3 (tyWidth0 t) .rsi .rdi) st.revDirs

theorem emitLinNode0_acc (cur : RegaTask0) (st : RegaSt0) :
    emitLinNode0 cur st =
      emitLinNode0 cur { st with revDirs := [] } ++ st.revDirs ∧
      ListNoSpZero0 (emitLinNode0 cur { st with revDirs := [] }) := by
  dsimp only [emitLinNode0, emitLinMem0]
  cases cur.node with
  | let1 op args _ =>
    exact comp_acc (loadRegArgs0_acc (LoadCfg0.mk false false cur.venv st.vslot) [] args 0)
      (emitOp0_acc op) st.revDirs
  | call fnSym as bs args k =>
    exact comp_acc (loadRegArgs0_acc (LoadCfg0.mk false true cur.venv st.vslot) as args 0)
      (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩) st.revDirs
  | let2Umulw64 a b _ => exact emitLinUmulw0_acc a b cur st
  | load t addr _ =>
    exact comp_acc (emitLoadArg0_acc .rdi addr cur.venv st.vslot)
      (pushDRR0_acc 2 (tyWidth0 t) .rax .rdi) st.revDirs
  | store t val addr _ => exact emitLinStore0_acc t val addr cur st
  | _ => exact ⟨rfl, listNoSpZero0_nil⟩

theorem jnzPrep0_revDirs (esc : Array Nat) (c : Arg0) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) :
    (jnzPrep0 esc c cur st ctrl).2 =
      (jnzPrep0 esc c cur { st with revDirs := [] } ctrl).2 ++ st.revDirs ∧
      ListNoSpZero0 (jnzPrep0 esc c cur { st with revDirs := [] } ctrl).2 := by
  dsimp only [jnzPrep0]
  exact comp_acc (comp_acc (emitLoadArg0_acc .rax c cur.venv st.vslot)
    (pushDRR0_acc 4 .W8 .rax .rax))
    (fun _ => ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩) st.revDirs

/-! ## 2. Scalar Machine Framing, `Frame0`, & Slot/Canon Specifications -/

/-- Caller-saved + ABI registers clobbered across Stage-0 `Isel0` helpers (disjoint from `%rsp`
and all `x64Frame.calleeSaved`). -/
@[expose] def x64ScratchAndAbi : List Reg64 :=
  [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem rsp_not_mem_scratchAndAbi : .rsp ∉ x64ScratchAndAbi := by
  simp [x64ScratchAndAbi]

theorem calleeSaved_not_mem_scratchAndAbi :
    ∀ r ∈ x64Frame.calleeSaved, r ∉ x64ScratchAndAbi := by
  intro r hr
  simp only [x64ScratchAndAbi, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem x64Scratch_sub_scratchAndAbi : ∀ r ∈ x64Scratch, r ∈ x64ScratchAndAbi := by
  intro r hr
  simp only [x64Scratch, x64ScratchAndAbi, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl <;> simp

theorem scalarFrame_of_x64 {s s' : MachineData} {gClob : List Reg64} {fClob : FlagMask}
    (h : x64Mach.Frame x64CondReads s s' gClob [] fClob) :
    x64ScalarMach.Frame x64CondReads s s' gClob [] fClob :=
  ⟨h.1, fun v _ => v.elim, h.2.2⟩

theorem scalarFrame_of_eq {s s' : MachineData} {gClob : List Reg64} {fClob : FlagMask}
    (hregs : ∀ r, r ∉ gClob → s'.regs.get64 r = s.regs.get64 r)
    (hflags : x64ScalarMach.UpdFlags x64CondReads s s' fClob) :
    x64ScalarMach.Frame x64CondReads s s' gClob [] fClob :=
  ⟨hregs, fun v _ => v.elim, hflags⟩

theorem scalarUpdFlags_maskAll (s s' : MachineData) :
    x64ScalarMach.UpdFlags x64CondReads s s' maskAll := fun cc h => by
  cases cc <;> simp [x64CondReads, FlagMask.disjoint, maskAll, maskOF, maskCF, maskZF, maskSF,
    maskPF] at h

theorem scalarUpdFlags_of_status_eq {s s' : MachineData} (h : s'.status = s.status) (m : FlagMask) :
    x64ScalarMach.UpdFlags x64CondReads s s' m := fun _ _ => by simp only [h]

theorem scalar_fallsTo_of_wp {c : List _root_.Directive} {g : List Reg64} {f : FlagMask}
    {s : MachineData} {Q : MachineData → Prop}
    (hwp : ∀ [Host] (E : Int64 → MachineData → Prop),
      _root_.Program.wp c
        (fun s' => Q s' ∧ x64ScalarMach.Frame x64CondReads s s' g [] f) E s)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k c g [] f s Q post :=
  fun hinf hcont =>
    Program.wp.eventually (@hwp h (fun _ _ => False)) hinf
      (fun s' ⟨hq, hf⟩ => hcont s' hq hf) (fun _ _ hf => hf.elim)

theorem scalar_fallsTo_single {d : _root_.Directive} {g : List Reg64} {f : FlagMask}
    {s : MachineData} {Q P : MachineData → Prop}
    (hd : Directive.FallsTo d s Q)
    (hqp : ∀ s', Q s' → P s' ∧ x64ScalarMach.Frame x64CondReads s s' g [] f)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k [d] g [] f s P post :=
  scalar_fallsTo_of_wp fun {_} _ => Program.wp.mono (Directive.FallsTo.wp hd) hqp

theorem scalar_fallsTo_of_x64 {h : Host} {k : Nat} {c : List _root_.Directive}
    {gClob : List Reg64} {fClob : FlagMask} {s : MachineData}
    {Q : MachineData → Prop} {post : MachineState → Prop}
    (hft : x64Mach.FallsTo x64CondReads h k c gClob [] fClob s Q post) :
    x64ScalarMach.FallsTo x64CondReads h k c gClob [] fClob s Q post :=
  fun hc hk => hft hc fun s' hq hfr => hk s' hq (scalarFrame_of_x64 hfr)

private theorem u64_land_one_eq_zero_iff (n : UInt32) :
    (UInt64.land n.toUInt64 1 = 0) ↔ n.toNat % 2 = 0 := by
  have hv : (UInt64.land n.toUInt64 1).toNat = n.toNat % 2 := by
    change (n.toUInt64.toBitVec &&& 1#64).toNat = n.toNat % 2
    rw [BitVec.toNat_and, UInt64.toNat_toBitVec, UInt32.toNat_toUInt64,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · intro h; rw [← hv, h]; rfl
  · intro h; apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    simpa [UInt64.toNat_zero, hv] using h

theorem x64FrameSizeU0_toNat (ns : UInt32) :
    (x64FrameSizeU0 ns).toNat = x64FrameSize ns.toNat := by
  have hlt := UInt32.toNat_lt ns
  have hle : 8 * ns.toNat + 8 < 2 ^ 64 := by omega
  dsimp only [x64FrameSizeU0, x64FrameSize]
  have h1 : (UInt64.mul ns.toUInt64 8).toNat = 8 * ns.toNat := by
    change (ns.toUInt64 * 8).toNat = 8 * ns.toNat
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    rw [show (8 : UInt64).toNat = 8 from rfl, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega : 8 * ns.toNat < 2 ^ 64)]
  by_cases hp : ns.toNat % 2 = 0
  · have hu : UInt64.land ns.toUInt64 1 = 0 := (u64_land_one_eq_zero_iff ns).2 hp
    have hnp : (ns.toNat % 2 == 0) = true := beq_iff_eq.2 hp
    simp only [hu, decide_true, ↓reduceIte, hnp]
    change (UInt64.mul ns.toUInt64 8 + 8).toNat = 8 * ns.toNat + 8
    rw [UInt64.toNat_add, h1, show (8 : UInt64).toNat = 8 from rfl, Nat.mod_eq_of_lt hle]
  · have hu : UInt64.land ns.toUInt64 1 ≠ 0 := fun h => hp ((u64_land_one_eq_zero_iff ns).1 h)
    have hdec : decide (UInt64.land ns.toUInt64 1 = 0) = false := decide_eq_false hu
    have hnp : (ns.toNat % 2 == 0) = false := beq_eq_false_iff_ne.2 hp
    simp only [hdec, Bool.false_eq_true, ↓reduceIte, hnp]
    change (UInt64.mul ns.toUInt64 8 + 0).toNat = 8 * ns.toNat + 0
    rw [UInt64.toNat_add, h1, show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : 8 * ns.toNat < 2 ^ 64)]

theorem x64FrameSizeU0_ne_zero (ns : UInt32) : x64FrameSizeU0 ns ≠ 0 := by
  intro h
  have hsz := congrArg UInt64.toNat h
  rw [x64FrameSizeU0_toNat, UInt64.toNat_zero] at hsz
  dsimp only [x64FrameSize] at hsz
  split at hsz
  · omega
  · rename_i hne
    have hns0 : ns.toNat ≠ 0 := fun h0 => hne (by simp [h0])
    omega

theorem x64FrameSize_lt_pow64 (ns : UInt32) : x64FrameSize ns.toNat + 8 ≤ 2 ^ 64 := by
  have hlt := UInt32.toNat_lt ns
  dsimp only [x64FrameSize]
  split <;> omega

private theorem fallsTo_subSpD (c : Int64) (s : MachineData) :
    Directive.FallsTo (x64SubSpD c) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - c.toBitVec) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ _ _ _ _ hk; dsimp only [x64SubSpD]; simp only [t_step_simp]; exact hk _ ⟨rfl, rfl, rfl⟩

private theorem fallsTo_addSpD (c : Int64) (s : MachineData) :
    Directive.FallsTo (x64AddSpD c) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + c.toBitVec) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ _ _ _ _ hk; dsimp only [x64AddSpD]; simp only [t_step_simp, BitVec.add_comm]
  exact hk _ ⟨rfl, rfl, rfl⟩

private theorem fallsTo_subSpR10 (s : MachineData) :
    Directive.FallsTo (ins (.sub (.reg (q .rsp)) (.reg (q .r10)))) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - s.regs.get64 .r10) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; exact hk _ ⟨rfl, rfl, rfl⟩

private theorem fallsTo_addSpR10 (s : MachineData) :
    Directive.FallsTo (ins (.add (.reg (q .rsp)) (.reg (q .r10)))) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + s.regs.get64 .r10) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]
  rw [BitVec.add_comm (s.regs.get64 .r10)]; exact hk _ ⟨rfl, rfl, rfl⟩

theorem emitSpAdj0_prologue_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (ns : UInt32)
    {s : MachineData} {ra : Int64} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hmem : s.dmem =⋆ x64ScalarFramePreds.RetAddr (s.regs.get64 .rsp) ra ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
        (x64FrameSize ns.toNat) ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitSpAdj0 true (x64FrameSizeU0 ns) [])))
      [.rsp, .r10, .r11] [] maskAll s
      (fun s' =>
        s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) ∧
        (s'.dmem =⋆ x64ScalarFramePreds.Saved (s.regs.get64 .rsp) ra ns.toNat ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
            (8 * ns.toNat) ⋆ G)) post := by
  have hle : 8 * ns.toNat ≤ x64FrameSize ns.toNat := x64FrameSize_ge ns.toNat
  have hF : x64FrameSize ns.toNat + 8 ≤ 2 ^ 64 := x64FrameSize_lt_pow64 ns
  have hsplit : region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
      (x64FrameSize ns.toNat) =
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) (8 * ns.toNat) ⋆
        region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) +
          BitVec.ofNat 64 (8 * ns.toNat)) (x64FrameSize ns.toNat - 8 * ns.toNat)) :=
    region_frame_split hle (by omega)
  have hmem' : (s.dmem =⋆ x64ScalarFramePreds.Saved (s.regs.get64 .rsp) ra ns.toNat ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
        (8 * ns.toNat) ⋆ G) := by
    rw [hsplit] at hmem
    exact sep_cast hmem (by dsimp only [x64ScalarFramePreds, x64FramePreds]; ac_rfl)
  apply scalar_fallsTo_of_wp; intro _ E
  dsimp only [emitSpAdj0]
  split
  · change _root_.Program.wp
      (toAmd64Program symName (emitFwd0 [Dir0.spAdd true (x64FrameSizeU0 ns)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil, x64FrameSizeU0_toNat]
    refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_subSpD (Int64.ofNat (x64FrameSize ns.toNat)) s)) ?_
    rintro s' ⟨hregs, _, hdmem⟩
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) :=
      by rw [hregs, Reg64s.get64_set64_same]; rfl
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    exact hregs ▸ Reg64s.get64_set64_of_ne _ .rsp r _
      (Ne.symm (fun e => hr (e ▸ List.mem_cons_self)))
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.spAddReg true .r10, Dir0.movRI .r10 (x64FrameSizeU0 ns)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.cons_append, List.append_nil,
      x64FrameSizeU0_toNat]
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_moviD s .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat)))) ?_
    rintro _ rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_subSpR10 _)) ?_
    rintro s' ⟨hregs, _, hdmem⟩
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat))).get64 .r10 =
        BitVec.ofNat 64 (x64FrameSize ns.toNat) := Reg64s.get64_set64_same _ _ _
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) :=
      by rw [hregs, Reg64s.get64_set64_same, hrsp1, hr10]
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [hregs, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hr.1),
      Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

theorem emitSpAdj0_epilogue_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (ns : UInt32)
    {s : MachineData} {ra : Int64} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hmem : s.dmem =⋆
      x64ScalarFramePreds.Saved (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat)) ra
        ns.toNat ⋆
      region (s.regs.get64 .rsp) (8 * ns.toNat) ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) [])))
      [.rsp, .r10, .r11] [] maskAll s
      (fun s' =>
        s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat) ∧
        (s'.dmem =⋆
          x64ScalarFramePreds.RetAddr (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat))
            ra ⋆
          region (s.regs.get64 .rsp) (x64FrameSize ns.toNat) ⋆ G)) post := by
  have hle : 8 * ns.toNat ≤ x64FrameSize ns.toNat := x64FrameSize_ge ns.toNat
  have hF : x64FrameSize ns.toNat + 8 ≤ 2 ^ 64 := x64FrameSize_lt_pow64 ns
  have hsplit : region (s.regs.get64 .rsp) (x64FrameSize ns.toNat) =
      (region (s.regs.get64 .rsp) (8 * ns.toNat) ⋆
        region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * ns.toNat))
          (x64FrameSize ns.toNat - 8 * ns.toNat)) :=
    region_frame_split hle (by omega)
  have hmem' : (s.dmem =⋆
      x64ScalarFramePreds.RetAddr (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat)) ra ⋆
      region (s.regs.get64 .rsp) (x64FrameSize ns.toNat) ⋆ G) := by
    dsimp only [x64ScalarFramePreds, x64FramePreds] at hmem ⊢
    rw [BitVec.add_sub_cancel] at hmem
    rw [hsplit]
    exact sep_cast hmem (by ac_rfl)
  apply scalar_fallsTo_of_wp; intro _ E
  dsimp only [emitSpAdj0]
  split
  · change _root_.Program.wp
      (toAmd64Program symName (emitFwd0 [Dir0.spAdd false (x64FrameSizeU0 ns)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil, x64FrameSizeU0_toNat]
    refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_addSpD (Int64.ofNat (x64FrameSize ns.toNat)) s)) ?_
    rintro s' ⟨hregs, _, hdmem⟩
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat) :=
      by rw [hregs, Reg64s.get64_set64_same]; rfl
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    exact hregs ▸ Reg64s.get64_set64_of_ne _ .rsp r _
      (Ne.symm (fun e => hr (e ▸ List.mem_cons_self)))
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.spAddReg false .r10, Dir0.movRI .r10 (x64FrameSizeU0 ns)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.cons_append, List.append_nil,
      x64FrameSizeU0_toNat]
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_moviD s .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat)))) ?_
    rintro _ rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_addSpR10 _)) ?_
    rintro s' ⟨hregs, _, hdmem⟩
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns.toNat))).get64 .r10 =
        BitVec.ofNat 64 (x64FrameSize ns.toNat) := Reg64s.get64_set64_same _ _ _
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat) :=
      by rw [hregs, Reg64s.get64_set64_same, hrsp1, hr10]
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [hregs, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hr.1),
      Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

private theorem uint64_mul_slot_toNat (slot : UInt32) :
    (UInt64.mul slot.toUInt64 8).toNat = 8 * slot.toNat := by
  have hlt := UInt32.toNat_lt slot
  change (slot.toUInt64 * 8).toNat = 8 * slot.toNat
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  rw [show (8 : UInt64).toNat = 8 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega : 8 * slot.toNat < 2 ^ 64)]

private theorem fallsTo_ldAddr64 (rd : Reg64) (addr : AddrExpr) (a v : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hmem : (cell64 a v ⋆ R) s.dmem) :
    Directive.FallsTo (ins (.mov (.reg (q rd)) (.mem addr))) s
      (fun s' => s' = { s with regs := s.regs.set64 rd v }) := by
  intro _ p _ _ _ hk
  simp only [t_step_simp, haddr p]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) R hmem (Int.toBytes_length _ _)]
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [hv]; exact hk _ rfl

private theorem fallsTo_stAddr64 (r : Reg64) (addr : AddrExpr) (a : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hmem : (region a 8 ⋆ R) s.dmem) :
    Directive.FallsTo (ins (.mov (.mem addr) (.reg (q r)))) s
      (fun s' => s'.regs = s.regs ∧ s'.zmms = s.zmms ∧ s'.status = s.status ∧
        (cell64 a (s.regs.get64 r) ⋆ R) s'.dmem) := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  intro _ p _ _ _ hk
  simp only [t_step_simp, haddr p]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs R hbs hl]
  exact hk _ ⟨rfl, rfl, rfl, Mem.storeInt_sep _ 8 bs R s.dmem ⟨hbs, hl⟩ (s.regs.get64 r).toInt⟩

theorem emitSlotMem0_ld_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (rd : Reg64)
    (_hrd : rd ≠ .rsp) (slot : UInt32) {σ : List (BitVec 64)} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hslot : slot.toNat < σ.length)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitSlotMem0 true rd slot [])))
      [rd, .r10] [] maskNone s
      (fun s' => s'.regs.get64 rd = σ[slot.toNat] ∧ s'.dmem = s.dmem) post := by
  have hm' : (cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) σ[slot.toNat] ⋆
      ((array64 (s.regs.get64 .rsp) (σ.take slot.toNat) ⋆
        array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat) + 8)
          (σ.drop (slot.toNat + 1))) ⋆ G)) s.dmem := by
    rw [array64_focus (s.regs.get64 .rsp) σ hslot, sep_assoc] at hmem; exact hmem
  apply scalar_fallsTo_of_wp; intro _ E
  simp only [emitSlotMem0, ↓reduceIte]
  split
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.ldSlot rd (UInt64.mul slot.toUInt64 8)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil, uint64_mul_slot_toNat]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_ldAddr64 rd
      (x64AtSp (Int64.ofNat (8 * slot.toNat)))
      (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) σ[slot.toNat] s
      (fun p => by rw [x64AtSp_interp, Int64_toBitVec_ofNat]) hm')) ?_
    rintro s' rfl
    refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq (fun r hr => ?_)
      (scalarUpdFlags_of_status_eq rfl _)⟩
    exact Reg64s.get64_set64_of_ne _ rd r _ (fun e => hr (e ▸ List.mem_cons_self))
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.ldSlotIdx rd .r10, Dir0.movRI .r10 (UInt64.mul slot.toUInt64 8)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.cons_append, List.append_nil,
      uint64_mul_slot_toNat]
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_moviD s .r10 (BitVec.ofNat 64 (8 * slot.toNat)))) ?_
    rintro _ rfl
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat))).get64 .r10 =
        BitVec.ofNat 64 (8 * slot.toNat) := Reg64s.get64_set64_same _ _ _
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_ldAddr64 rd x64AtSpR10
      (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) σ[slot.toNat]
      { s with regs := s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat)) }
      (fun p => by rw [x64AtSpR10_interp, hrsp1, hr10]) hm')) ?_
    rintro s' rfl
    refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq (fun r hr => ?_)
      (scalarUpdFlags_of_status_eq rfl _)⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
      Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2)]

theorem emitSlotMem0_st_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (rs : Reg64)
    (hrs : rs ≠ .r10) (slot : UInt32) {σ : List (BitVec 64)} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hslot : slot.toNat < σ.length)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitSlotMem0 false rs slot [])))
      [.r10] [] maskNone s
      (fun s' => s'.dmem =⋆ array64 (s.regs.get64 .rsp) (σ.set slot.toNat (s.regs.get64 rs)) ⋆ G)
      post := by
  have hm_cell : (cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) σ[slot.toNat] ⋆
      ((array64 (s.regs.get64 .rsp) (σ.take slot.toNat) ⋆
        array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat) + 8)
          (σ.drop (slot.toNat + 1))) ⋆ G)) s.dmem := by
    rw [array64_focus (s.regs.get64 .rsp) σ hslot, sep_assoc] at hmem; exact hmem
  have hm_reg : (region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) 8 ⋆
      ((array64 (s.regs.get64 .rsp) (σ.take slot.toNat) ⋆
        array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat) + 8)
          (σ.drop (slot.toNat + 1))) ⋆ G)) s.dmem :=
    sep_mono (fun _ => cell64_region) hm_cell
  have hcast : ∀ m',
      (cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) (s.regs.get64 rs) ⋆
        ((array64 (s.regs.get64 .rsp) (σ.take slot.toNat) ⋆
          array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat) + 8)
            (σ.drop (slot.toNat + 1))) ⋆ G)) m' →
      m' =⋆ array64 (s.regs.get64 .rsp) (σ.set slot.toNat (s.regs.get64 rs)) ⋆ G := by
    intro m' hm'; rwa [array64_set (s.regs.get64 .rsp) σ hslot, sep_assoc]
  apply scalar_fallsTo_of_wp; intro _ E
  simp only [emitSlotMem0, Bool.false_eq_true, ↓reduceIte]
  split
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.stSlot (UInt64.mul slot.toUInt64 8) rs])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil, uint64_mul_slot_toNat]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_stAddr64 rs
      (x64AtSp (Int64.ofNat (8 * slot.toNat)))
      (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat)) s
      (fun p => by rw [x64AtSp_interp, Int64_toBitVec_ofNat]) hm_reg)) ?_
    rintro s' ⟨hregs, _, hst, hdmem⟩
    exact ⟨hcast s'.dmem hdmem, scalarFrame_of_eq (fun r _ => by rw [hregs])
      (scalarUpdFlags_of_status_eq hst _)⟩
  · change _root_.Program.wp (toAmd64Program symName
      (emitFwd0 [Dir0.stSlotIdx .r10 rs, Dir0.movRI .r10 (UInt64.mul slot.toUInt64 8)])) _ E s
    simp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
      List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.cons_append, List.append_nil,
      uint64_mul_slot_toNat]
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_moviD s .r10 (BitVec.ofNat 64 (8 * slot.toNat)))) ?_
    rintro _ rfl
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat))).get64 .r10 =
        BitVec.ofNat 64 (8 * slot.toNat) := Reg64s.get64_set64_same _ _ _
    have hrs_val : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat))).get64 rs =
        s.regs.get64 rs := Reg64s.get64_set64_of_ne _ _ _ _ hrs.symm
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_stAddr64 rs x64AtSpR10
      (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * slot.toNat))
      { s with regs := s.regs.set64 .r10 (BitVec.ofNat 64 (8 * slot.toNat)) }
      (fun p => by rw [x64AtSpR10_interp, hrsp1, hr10]) hm_reg)) ?_
    rintro s' ⟨hregs, _, hst, hdmem⟩
    rw [hrs_val] at hdmem
    refine ⟨hcast s'.dmem hdmem, scalarFrame_of_eq (fun r hr => ?_)
      (scalarUpdFlags_of_status_eq hst _)⟩
    have hne : .r10 ≠ r := fun e => hr (e ▸ List.mem_cons_self)
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne]

theorem emitCanon0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (w : Width) (r : Reg64)
    {s : MachineData} {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitCanon0 w r []))) [r] [] maskNone s
      (fun s' => s'.regs.get64 r = ((s.regs.get64 r).setWidth w.bits).setWidth 64 ∧
        s'.dmem = s.dmem) post := by
  have hsingle : ∀ (d : Directive)
      (hd : Directive.FallsTo d s
        (fun s' => s' =
          { s with regs := s.regs.set64 r (((s.regs.get64 r).setWidth w.bits).setWidth 64) })),
      x64ScalarMach.FallsTo x64CondReads h k [d] [r] [] maskNone s
        (fun s' => s'.regs.get64 r = ((s.regs.get64 r).setWidth w.bits).setWidth 64 ∧
          s'.dmem = s.dmem) post := by
    intro d hd
    refine scalar_fallsTo_single hd fun s' hs' => by
      subst hs'
      refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq (fun r' hr' => ?_)
        (scalarUpdFlags_of_status_eq rfl _)⟩
      exact Reg64s.get64_set64_of_ne _ r r' _ (fun e => hr' (List.mem_singleton.mpr e.symm))
  cases w with
  | W8 =>
    dsimp only [emitCanon0, pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil,
      List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
      List.append_nil]
    exact hsingle _ (fallsTo_movzx8 s r r)
  | W16 =>
    dsimp only [emitCanon0, pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil,
      List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
      List.append_nil]
    exact hsingle _ (fallsTo_movzx16 s r r)
  | W32 =>
    dsimp only [emitCanon0, pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil,
      List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
      List.append_nil]
    have hfl := fallsTo_movlD s r r
    simp only [BitVec.zeroExtend_eq_setWidth] at hfl
    dsimp only [Width.bits]
    exact hsingle _ hfl
  | W64 =>
    dsimp only [emitCanon0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    exact Machine.FallsTo.nil ⟨by simp [Width.bits, BitVec.setWidth_eq], rfl⟩

theorem emitCanon0_ty_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (t : Ty0) (r : Reg64)
    {v : Val (ty0ToTy t)} {s : MachineData} {post : MachineState → Prop}
    (hh : GprHolds (s.regs.get64 r) (ty0ToTy t) v) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) r []))) [r] [] maskNone s
      (fun s' => s'.regs.get64 r = toCanon64 t v ∧ s'.dmem = s.dmem) post :=
  Machine.FallsTo.conseq (emitCanon0_spec (tyWidth0 t) r) fun _ ⟨hr, hm⟩ _ =>
    ⟨hr.trans (canon64_of_gprHolds hh), hm⟩

/-! ## 3. Operand Evaluation, `emitLoadArg0`, & `loadRegArgs0` Specifications -/

/-- Meaning of `Arg0` `a` evaluating to 64-bit canonical word `val64` in slot array `σ`. -/
@[expose] def ArgSlotVal64 (venv : List UInt32) (vslot : Array Nat) (σ : List (BitVec 64)) :
    Arg0 → BitVec 64 → Prop
  | .var idx, val64 =>
    let sl := (arrGetU0 vslot (listGetU32 venv idx)).toNat
    ∃ _ : sl < σ.length, σ[sl] = val64
  | .immBool b, val64 => val64 = BitVec.ofNat 64 b.toNat
  | .immBits w val, val64 => val64 = (BitVec.ofNat w.bits val.toNat).setWidth 64

/-- List version of `ArgSlotVal64` pairing `List Arg0` against canonical 64-bit words. -/
@[expose] def ArgsSlotVal64 (venv : List UInt32) (vslot : Array Nat) (σ : List (BitVec 64)) :
    List Arg0 → List (BitVec 64) → Prop
  | [], [] => True
  | a :: as, v :: vs => ArgSlotVal64 venv vslot σ a v ∧ ArgsSlotVal64 venv vslot σ as vs
  | _, _ => False

theorem bitvec_ofNat_maskImmW0 (w : Width) (val : UInt64) :
    BitVec.ofNat 64 (maskImmW0 w val).toNat = (BitVec.ofNat w.bits val.toNat).setWidth 64 := by
  have hlt := UInt64.toNat_lt val
  have hmask : ∀ (m : UInt64) (k : Nat), m.toBitVec.toNat = 2 ^ k - 1 →
      (UInt64.land val m).toNat = val.toNat % 2 ^ k := fun m k hm => by
    rw [show (UInt64.land val m).toNat = (val.toBitVec &&& m.toBitVec).toNat from rfl,
      BitVec.toNat_and, UInt64.toNat_toBitVec, hm, Nat.and_two_pow_sub_one_eq_mod]
  cases w <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [maskImmW0, Width.bits, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · rw [hmask 0xff 8 rfl]
  · rw [hmask 0xffff 16 rfl]
  · rw [hmask 0xffffffff 32 rfl]
  · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

theorem abiRegAt0_ne_r10 (useRet : Bool) (i : UInt32) : abiRegAt0 useRet i ≠ .r10 := by
  dsimp only [abiRegAt0]; cases useRet <;> repeat' split
  all_goals decide

theorem abiRegAt0_inj_lt (useRet : Bool) {i j : Nat}
    (hi : i < if useRet then 7 else 6) (hj : j < if useRet then 7 else 6)
    (heq : abiRegAt0 useRet (UInt32.ofNat i) = abiRegAt0 useRet (UInt32.ofNat j)) : i = j := by
  cases useRet
  · simp only [Bool.false_eq_true, ↓reduceIte] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; revert heq; decide)
  · simp only [↓reduceIte] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; revert heq; decide)

theorem abiRegAt0_mem_scratchAndAbi (useRet : Bool) (i : UInt32) :
    abiRegAt0 useRet i ∈ x64ScratchAndAbi := by
  dsimp only [abiRegAt0, x64ScratchAndAbi]; cases useRet <;> repeat' split
  all_goals simp

theorem abiRegAt0_ne_rsp (useRet : Bool) (i : UInt32) : abiRegAt0 useRet i ≠ .rsp :=
  fun h => rsp_not_mem_scratchAndAbi (h ▸ abiRegAt0_mem_scratchAndAbi useRet i)

theorem emitLoadArg0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (rd : Reg64)
    (hrd : rd ≠ .rsp) (a : Arg0) (venv : List UInt32) (vslot : Array Nat)
    {σ : List (BitVec 64)} {val64 : BitVec 64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (ha : ArgSlotVal64 venv vslot σ a val64)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLoadArg0 rd a venv vslot [])))
      [rd, .r10] [] maskNone s
      (fun s' => s'.regs.get64 rd = val64 ∧ s'.dmem = s.dmem) post := by
  cases a with
  | var idx =>
    obtain ⟨hsl, hval⟩ := ha
    simpa [emitLoadArg0, hval] using emitSlotMem0_ld_spec rd hrd
      (arrGetU0 vslot (listGetU32 venv idx)) hsl hmem
  | immBool b =>
    dsimp only [ArgSlotVal64] at ha; subst ha
    cases b
    · simp only [emitLoadArg0, pushDImm0, emitFwd0, decide_true, ↓reduceIte, List.reverse_cons,
        List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
        dir0ToAmd64, List.append_nil, Bool.false_eq_true, UInt64.toNat_zero, Bool.toNat]
      have hft : x64ScalarMach.FallsTo x64CondReads h k [moviD rd (BitVec.ofNat 64 0)] [rd] []
          maskNone s (fun s' => s'.regs.get64 rd = BitVec.ofNat 64 0 ∧ s'.dmem = s.dmem) post :=
        scalar_fallsTo_single (fallsTo_moviD s rd (BitVec.ofNat 64 0))
          (by rintro s' rfl; exact
            ⟨⟨Reg64s.get64_set64_same .., rfl⟩,
              scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
                (fun e => hr (List.mem_singleton.mpr e.symm)))
                (scalarUpdFlags_of_status_eq rfl _)⟩)
      exact Machine.FallsTo.weaken hft (fun r hr => by simp_all) (fun _ hv => nomatch hv)
        (by decide)
    · simp only [emitLoadArg0, pushDImm0, emitFwd0, decide_true, ↓reduceIte, List.reverse_cons,
        List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
        dir0ToAmd64, List.append_nil, UInt64.toNat_one, Bool.toNat]
      have hft : x64ScalarMach.FallsTo x64CondReads h k [moviD rd (BitVec.ofNat 64 1)] [rd] []
          maskNone s (fun s' => s'.regs.get64 rd = BitVec.ofNat 64 1 ∧ s'.dmem = s.dmem) post :=
        scalar_fallsTo_single (fallsTo_moviD s rd (BitVec.ofNat 64 1))
          (by rintro s' rfl; exact
            ⟨⟨Reg64s.get64_set64_same .., rfl⟩,
              scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
                (fun e => hr (List.mem_singleton.mpr e.symm)))
                (scalarUpdFlags_of_status_eq rfl _)⟩)
      exact Machine.FallsTo.weaken hft (fun r hr => by simp_all) (fun _ hv => nomatch hv)
        (by decide)
  | immBits w val =>
    dsimp only [ArgSlotVal64] at ha; subst ha
    simp only [emitLoadArg0, pushDImm0, emitFwd0, decide_true, ↓reduceIte, List.reverse_cons,
      List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
      dir0ToAmd64, List.append_nil]
    have hft : x64ScalarMach.FallsTo x64CondReads h k
        [moviD rd (BitVec.ofNat 64 (maskImmW0 w val).toNat)] [rd] [] maskNone s
        (fun s' =>
          s'.regs.get64 rd = (BitVec.ofNat w.bits val.toNat).setWidth 64 ∧ s'.dmem = s.dmem)
        post :=
      scalar_fallsTo_single (fallsTo_moviD s rd (BitVec.ofNat 64 (maskImmW0 w val).toNat))
        (by rintro s' rfl; exact
          ⟨⟨(Reg64s.get64_set64_same ..).trans (bitvec_ofNat_maskImmW0 w val), rfl⟩,
            scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
              (fun e => hr (List.mem_singleton.mpr e.symm)))
              (scalarUpdFlags_of_status_eq rfl _)⟩)
    exact Machine.FallsTo.weaken hft (fun r hr => by simp_all) (fun _ hv => nomatch hv) (by decide)

private theorem loadRegArgs0_spec_exact {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (cfg : LoadCfg0) (ts : List Ty0) (args : List Arg0) (i : UInt32) {σ : List (BitVec 64)}
    {vals : List (BitVec 64)} {s : MachineData} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : cfg.canon = false → ts = [])
    (hlen : i.toNat + args.length ≤ if cfg.useRet then 7 else 6)
    (hts : cfg.canon = true → ts.length = args.length ∧
      ∀ (j : Nat) (hj1 : j < ts.length) (hj2 : j < vals.length),
        ((vals[j].setWidth (tyWidth0 ts[j]).bits).setWidth 64) = vals[j])
    (hvals : ArgsSlotVal64 cfg.venv cfg.vslot σ args vals)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    let clobs := .r10 :: (List.range args.length).map
      (fun j => abiRegAt0 cfg.useRet (UInt32.ofNat (i.toNat + j)))
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (loadRegArgs0 cfg ts args i [])))
      clobs [] maskNone s
      (fun s' => s'.dmem = s.dmem ∧
        ∀ (j : Nat) (_hj1 : j < args.length) (_hj2 : j < vals.length),
          s'.regs.get64 (abiRegAt0 cfg.useRet (UInt32.ofNat (i.toNat + j))) = vals[j])
      post := by
  induction args generalizing k ts i vals s with
  | nil =>
    cases vals with
    | nil =>
      dsimp only [loadRegArgs0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
      exact Machine.FallsTo.nil ⟨rfl, fun _ hj _ => absurd hj (Nat.not_lt_zero _)⟩
    | cons _ _ => exact False.elim hvals
  | cons a aRest ih =>
    cases vals with
    | nil => exact False.elim hvals
    | cons v vRest =>
      obtain ⟨hva, hvr⟩ := hvals
      have hcap : (if cfg.useRet then 7 else 6) ≤ 7 := by cases cfg.useRet <;> decide
      have hilt : i.toNat + 1 ≤ if cfg.useRet then 7 else 6 := by
        simp only [List.length_cons] at hlen; omega
      have hi_lt : i.toNat < if cfg.useRet then 7 else 6 := by omega
      have hi1_u32 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
      have hi_u32 : UInt32.ofNat (i.toNat + 0) = i := by
        simpa only [Nat.add_zero] using UInt32.ofNat_toNat
      have hstep : ∃ (tsNext : List Ty0) (dHead : List Dir0),
          loadRegArgs0 cfg ts (a :: aRest) i [] =
            loadRegArgs0 cfg tsNext aRest (i + 1) [] ++ dHead ∧
          (cfg.canon = false → tsNext = []) ∧
          (cfg.canon = true → tsNext.length = aRest.length ∧
            ∀ (j : Nat) (hj1 : j < tsNext.length) (hj2 : j < vRest.length),
              ((vRest[j].setWidth (tyWidth0 tsNext[j]).bits).setWidth 64) = vRest[j]) ∧
          x64ScalarMach.FallsTo x64CondReads h k (toAmd64Program symName (emitFwd0 dHead))
            [abiRegAt0 cfg.useRet i, .r10] [] maskNone s
            (fun s1 => s1.regs.get64 (abiRegAt0 cfg.useRet i) = v ∧ s1.dmem = s.dmem) post := by
        cases hcan : cfg.canon with
        | false =>
          rw [hc hcan]
          refine ⟨[], emitLoadArg0 (abiRegAt0 cfg.useRet i) a cfg.venv cfg.vslot [], ?_,
            fun _ => rfl, (fun h => by cases h), ?_⟩
          · exact (loadRegArgs0_acc cfg [] aRest (i + 1) _).1
          · exact emitLoadArg0_spec _ (abiRegAt0_ne_rsp cfg.useRet i) a cfg.venv cfg.vslot hva hmem
        | true =>
          obtain ⟨htl, htv⟩ := hts hcan
          cases ts with
          | nil => simp at htl
          | cons t tRest =>
            have htw0 : (v.setWidth (tyWidth0 t).bits).setWidth 64 = v := htv 0 (by simp) (by simp)
            have htRest : tRest.length = aRest.length ∧
                ∀ (j : Nat) (hj1 : j < tRest.length) (hj2 : j < vRest.length),
                  ((vRest[j].setWidth (tyWidth0 tRest[j]).bits).setWidth 64) = vRest[j] :=
              ⟨by simpa using htl, fun j hj1 hj2 =>
                htv (j + 1) (Nat.succ_lt_succ hj1) (Nat.succ_lt_succ hj2)⟩
            let dH := emitCanon0 (tyWidth0 t) (abiRegAt0 cfg.useRet i)
              (emitLoadArg0 (abiRegAt0 cfg.useRet i) a cfg.venv cfg.vslot [])
            refine ⟨tRest, dH, ?_, (fun h => by cases h), fun _ => htRest, ?_⟩
            · dsimp only [loadRegArgs0]; rw [hcan]
              exact (loadRegArgs0_acc cfg tRest aRest (i + 1) dH).1
            · have hdEq : dH = emitCanon0 (tyWidth0 t) (abiRegAt0 cfg.useRet i) [] ++
                  emitLoadArg0 (abiRegAt0 cfg.useRet i) a cfg.venv cfg.vslot [] :=
                (emitCanon0_acc (tyWidth0 t) (abiRegAt0 cfg.useRet i) _).1
              rw [hdEq, emitFwd0_append, toAmd64Program_append]
              have hcomp : x64ScalarMach.FallsTo x64CondReads h k
                  (toAmd64Program symName (emitFwd0 (emitLoadArg0 (abiRegAt0 cfg.useRet i) a
                    cfg.venv cfg.vslot [])) ++
                   toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t)
                    (abiRegAt0 cfg.useRet i) [])))
                  ([abiRegAt0 cfg.useRet i, .r10] ++ [abiRegAt0 cfg.useRet i]) ([] ++ [])
                  (maskNone ||| maskNone) s
                  (fun s2 => s2.regs.get64 (abiRegAt0 cfg.useRet i) = v ∧ s2.dmem = s.dmem)
                  post :=
                Machine.FallsTo.comp
                  (emitLoadArg0_spec _ (abiRegAt0_ne_rsp cfg.useRet i) a cfg.venv cfg.vslot
                    hva hmem)
                  fun s1 ⟨hr1, hm1⟩ _ => Machine.FallsTo.conseq
                    (emitCanon0_spec (tyWidth0 t) (abiRegAt0 cfg.useRet i))
                    fun s2 ⟨hr2, hm2⟩ _ => ⟨hr2.trans (by rw [hr1, htw0]), hm2.trans hm1⟩
              exact Machine.FallsTo.weaken hcomp
                (fun r hr => by
                  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                  rcases hr with (rfl | rfl) | rfl <;> simp)
                (fun _ hv => nomatch hv) (by decide)
      obtain ⟨tsNext, dHead, hsplit, hcN, htsN, hft1⟩ := hstep
      rw [hsplit, emitFwd0_append, toAmd64Program_append]
      have hsub : ∀ r ∈ ([abiRegAt0 cfg.useRet i, .r10] ++ (.r10 :: (List.range aRest.length).map
            (fun j => abiRegAt0 cfg.useRet (UInt32.ofNat ((i + 1).toNat + j))))),
          r ∈ (.r10 :: (List.range (a :: aRest).length).map
            (fun j => abiRegAt0 cfg.useRet (UInt32.ofNat (i.toNat + j)))) := by
        intro r hr
        simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
          List.map_map, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
          Function.comp_def, List.mem_map] at hr ⊢
        rcases hr with (rfl | rfl) | (rfl | ⟨j, hj, rfl⟩)
        · exact Or.inr (Or.inl (congrArg (abiRegAt0 cfg.useRet) UInt32.ofNat_toNat.symm))
        · exact Or.inl rfl
        · exact Or.inl rfl
        · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
          rw [hi1_u32, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc]
      have hcomp : x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 dHead) ++
            toAmd64Program symName (emitFwd0 (loadRegArgs0 cfg tsNext aRest (i + 1) [])))
          ([abiRegAt0 cfg.useRet i, .r10] ++ (.r10 :: (List.range aRest.length).map
            (fun j => abiRegAt0 cfg.useRet (UInt32.ofNat ((i + 1).toNat + j)))))
          ([] ++ []) (maskNone ||| maskNone) s
          (fun s' => s'.dmem = s.dmem ∧
            ∀ (j : Nat) (_hj1 : j < (a :: aRest).length) (_hj2 : j < (v :: vRest).length),
              s'.regs.get64 (abiRegAt0 cfg.useRet (UInt32.ofNat (i.toNat + j))) =
                (v :: vRest)[j])
          post :=
        Machine.FallsTo.comp hft1 fun s1 ⟨hr1, hm1⟩ hfr1 => by
          have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp := hfr1.1 .rsp (by
            simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
            exact ⟨(abiRegAt0_ne_rsp cfg.useRet i).symm, by decide⟩)
          have hm1' : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
            rw [hm1, hrsp1]; exact hmem
          have ih1 := ih (k := k + (toAmd64Program symName (emitFwd0 dHead)).length) tsNext (i + 1)
            hcN (by rw [List.length_cons] at hlen; rw [hi1_u32]; omega) htsN hvr hm1'
          refine Machine.FallsTo.conseq ih1 fun s2 ⟨hm2, hregs2⟩ hfr2 => ?_
          refine ⟨hm2.trans hm1, fun j hj1 hj2 => ?_⟩
          cases j with
          | zero =>
            rw [Nat.add_zero, UInt32.ofNat_toNat]
            have hnot : abiRegAt0 cfg.useRet i ∉ (.r10 :: (List.range aRest.length).map
                (fun j => abiRegAt0 cfg.useRet (UInt32.ofNat ((i + 1).toNat + j)))) := by
              simp only [List.mem_cons, List.mem_map, not_or, not_exists, not_and]
              refine ⟨abiRegAt0_ne_r10 cfg.useRet i, fun m hm heq => ?_⟩
              rw [List.mem_range] at hm
              have hm_lt : (i + 1).toNat + m < if cfg.useRet then 7 else 6 := by
                rw [hi1_u32]; simp only [List.length_cons] at hlen; omega
              have heq' := abiRegAt0_inj_lt cfg.useRet hi_lt hm_lt
                (by simpa [UInt32.ofNat_toNat] using heq.symm)
              omega
            exact (hfr2.1 (abiRegAt0 cfg.useRet i) hnot).trans hr1
          | succ j' =>
            have h' := hregs2 j' (Nat.lt_of_succ_lt_succ hj1) (Nat.lt_of_succ_lt_succ hj2)
            have hidx : UInt32.ofNat (i.toNat + (j' + 1)) =
                UInt32.ofNat ((i + 1).toNat + j') := by
              rw [hi1_u32, Nat.add_assoc, Nat.add_comm 1 j']
            rw [hidx]; exact h'
      exact Machine.FallsTo.weaken hcomp hsub (fun _ hv => nomatch hv) (by decide)

theorem loadRegArgs0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (cfg : LoadCfg0)
    (ts : List Ty0) (args : List Arg0) (i : UInt32) {σ : List (BitVec 64)}
    {vals : List (BitVec 64)} {s : MachineData} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : cfg.canon = false → ts = [])
    (hlen : i.toNat + args.length ≤ if cfg.useRet then 7 else 6)
    (hts : cfg.canon = true → ts.length = args.length ∧
      ∀ (j : Nat) (hj1 : j < ts.length) (hj2 : j < vals.length),
        ((vals[j].setWidth (tyWidth0 ts[j]).bits).setWidth 64) = vals[j])
    (hvals : ArgsSlotVal64 cfg.venv cfg.vslot σ args vals)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (loadRegArgs0 cfg ts args i [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.dmem = s.dmem ∧
        ∀ (j : Nat) (_hj1 : j < args.length) (_hj2 : j < vals.length),
          s'.regs.get64 (abiRegAt0 cfg.useRet (UInt32.ofNat (i.toNat + j))) = vals[j])
      post :=
  Machine.FallsTo.weaken (loadRegArgs0_spec_exact cfg ts args i hc hlen hts hvals hmem)
    (fun r hr => by
      simp only [List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨_, _, rfl⟩
      · simp [x64ScratchAndAbi]
      · exact abiRegAt0_mem_scratchAndAbi cfg.useRet _)
    (fun _ hv => nomatch hv) (by decide)

/-! ## 4. `emitOp0`, `emitLinNode0`, & `jnzPrep0` Specifications -/

theorem setWidth_up_down {m n k : Nat} (hmn : m ≤ n) (_hnk : n ≤ k) (v : BitVec m) :
    (v.setWidth n).setWidth k = v.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hik
  by_cases him : i < n
  · simp [hik, him]
  · have hm : m ≤ i := Nat.le_of_not_lt fun h => him (Nat.lt_of_lt_of_le h hmn)
    simp only [BitVec.getLsbD_setWidth, hik, him, decide_true, decide_false, Bool.true_and,
      Bool.false_and, BitVec.getLsbD_of_ge v i hm]

theorem canon64_setWidth32_64 {t : Ty0} (ht : t ≠ .b64) {v : Val (ty0ToTy t)} :
    ((toCanon64 t v).setWidth 32).setWidth 64 = toCanon64 t v := by
  cases t with
  | bool => cases v <;> decide
  | b8 =>
    dsimp only [toCanon64]
    rw [BitVec.setWidth_setWidth_of_le v (by decide : 32 ≤ 64), setWidth_up_down (by decide)
      (by decide) v]
  | b16 =>
    dsimp only [toCanon64]
    rw [BitVec.setWidth_setWidth_of_le v (by decide : 32 ≤ 64), setWidth_up_down (by decide)
      (by decide) v]
  | b32 =>
    dsimp only [toCanon64]
    rw [setWidth_64_setWidth .W32 v]
  | b64 => exact absurd rfl ht

theorem op0_argsIn_to_regs_bool {rv : BitVec 64} {b : Bool} (h : rv = toCanon64 .bool b) :
    GprHolds rv .bool b := by
  rw [h]; exact toCanon64_toGprHolds .bool b

/-- ABI register holds canonical inputs for `op : OpCode0` (`rdi`, `rsi`, `rdx`). -/
@[expose] def OpArgsIn0 (s : MachineData) :
    (op : OpCode0) → Tup Val (ty0ListToTy (op0ArgTys op)) → Prop
  | .un _ t, (a, ()) => s.regs.get64 .rdi = toCanon64 t a
  | .bin _ t, (a, b, ()) => s.regs.get64 .rdi = toCanon64 t a ∧ s.regs.get64 .rsi = toCanon64 t b
  | .cmp _ t, (a, b, ()) => s.regs.get64 .rdi = toCanon64 t a ∧ s.regs.get64 .rsi = toCanon64 t b
  | .select t, (c, a, b, ()) =>
    s.regs.get64 .rdi = toCanon64 .bool c ∧ s.regs.get64 .rsi = toCanon64 t a ∧
      s.regs.get64 .rdx = toCanon64 t b
  | .conv .ofBool _ _, (c, ()) => s.regs.get64 .rdi = toCanon64 .bool c
  | .conv .zext m _, (a, ()) | .conv .sext m _, (a, ()) | .conv .trunc m _, (a, ()) =>
    s.regs.get64 .rdi = toCanon64 (widthTy0 m) a
  | .div _ w, (a, b, ()) =>
    s.regs.get64 .rdi = toCanon64 (widthTy0 w) a ∧ s.regs.get64 .rsi = toCanon64 (widthTy0 w) b
  | .umulw64, (a, b, ()) =>
    s.regs.get64 .rdi = toCanon64 .b64 a ∧ s.regs.get64 .rsi = toCanon64 .b64 b

/-- Valid opcode side-condition enforced by `checkOp0` + `noNegBool`. -/
@[expose] def ValidOp0 : OpCode0 → Prop
  | .un .neg .bool => False
  | .bin .add .bool | .bin .sub .bool | .bin .mul .bool | .bin .shl .bool
  | .bin .lshr .bool | .bin .ashr .bool | .bin .rotl .bool | .bin .rotr .bool => False
  | .cmp _ .bool => False
  | .conv .zext m n => m.bits ≤ n.bits
  | .conv .sext m n => m.bits ≤ n.bits
  | .conv .trunc m n => n.bits ≤ m.bits
  | .umulw64 => False
  | _ => True

theorem validOp0_of_checkOp0 {venv : List Ty0} {op : OpCode0} {args : List Arg0}
    (hc : checkOp0 venv op args = true) (hnb : op ≠ .un .neg .bool) : ValidOp0 op := by
  cases op with
  | un u t => cases u <;> cases t <;> first | trivial | exact absurd rfl hnb
  | bin b t =>
    cases t
    · rcases args with _ | ⟨a, _ | ⟨bArg, _ | c⟩⟩ <;>
        cases b <;> first | trivial | simp [checkOp0, checkOpArith0, checkBinOp0] at hc
    · cases b <;> trivial
    · cases b <;> trivial
    · cases b <;> trivial
    · cases b <;> trivial
  | cmp _ t =>
    cases t
    · rcases args with _ | ⟨a, _ | ⟨bArg, _ | c⟩⟩ <;> simp [checkOp0] at hc
    · trivial
    · trivial
    · trivial
    · trivial
  | select _ => trivial
  | conv c m n =>
    dsimp only [ValidOp0]
    cases c
    · trivial
    · cases args with
      | nil => simp [checkOp0, checkConv0] at hc
      | cons a rest =>
        cases rest <;> cases m <;> cases n <;> simp_all [checkOp0, checkConv0, widthBits0,
          Width.bits]
    · cases args with
      | nil => simp [checkOp0, checkConv0] at hc
      | cons a rest =>
        cases rest <;> cases m <;> cases n <;> simp_all [checkOp0, checkConv0, widthBits0,
          Width.bits]
    · cases args with
      | nil => simp [checkOp0, checkConv0] at hc
      | cons a rest =>
        cases rest <;> cases m <;> cases n <;> simp_all [checkOp0, checkConv0, widthBits0,
          Width.bits]
  | div _ _ => trivial
  | umulw64 => simp [checkOp0] at hc

theorem scalar_movD_fallsTo {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (rd rs : Reg64) (s : MachineData) {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 rd rs []))) [rd] [] maskNone s
      (fun s' => s'.regs.get64 rd = s.regs.get64 rs ∧ s'.dmem = s.dmem) post := by
  dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
    toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
  exact scalar_fallsTo_single (fallsTo_movD s rd rs) (by
    rintro _ rfl; exact ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq
      (fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
      (scalarUpdFlags_of_status_eq rfl _)⟩)

theorem scalar_movlD_fallsTo {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (rd rs : Reg64) (s : MachineData) {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W32 rd rs []))) [rd] [] maskNone s
      (fun s' => s'.regs.get64 rd = ((s.regs.get64 rs).setWidth 32).setWidth 64 ∧
        s'.dmem = s.dmem) post := by
  dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
    toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
  refine scalar_fallsTo_single (fallsTo_movlD s rd rs) (by
    rintro _ rfl; exact ⟨⟨by rw [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth], rfl⟩,
      scalarFrame_of_eq
        (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
          (fun e => hr (List.mem_singleton.mpr e.symm)))
        (scalarUpdFlags_of_status_eq rfl _)⟩)

theorem scalar_movzx8_fallsTo {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (rd rs : Reg64) (s : MachineData) {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 1 .W8 rd rs []))) [rd] [] maskNone s
      (fun s' => s'.regs.get64 rd = ((s.regs.get64 rs).setWidth 8).setWidth 64 ∧
        s'.dmem = s.dmem) post := by
  dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
    toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
  exact scalar_fallsTo_single (fallsTo_movzx8 s rd rs) (by
    rintro _ rfl; exact ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq
      (fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
      (scalarUpdFlags_of_status_eq rfl _)⟩)

theorem scalar_movzx16_fallsTo {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (rd rs : Reg64) (s : MachineData) {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 1 .W16 rd rs []))) [rd] [] maskNone s
      (fun s' => s'.regs.get64 rd = ((s.regs.get64 rs).setWidth 16).setWidth 64 ∧
        s'.dmem = s.dmem) post := by
  dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
    toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
  exact scalar_fallsTo_single (fallsTo_movzx16 s rd rs) (by
    rintro _ rfl; exact ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq
      (fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
      (scalarUpdFlags_of_status_eq rfl _)⟩)

theorem scalar_movsx_fallsTo {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (wDst : Width) (hw : wDst = .W32 ∨ wDst = .W64) (rd : Reg64) (wSrc : Width) (rs : Reg64)
    (hs : wSrc.bits ≤ wDst.bits ∧ (wDst = .W64 ∨ wSrc = .W8 ∨ wSrc = .W16))
    (s : MachineData) {post : MachineState → Prop} :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDMovsx0 wDst rd wSrc rs []))) [rd] [] maskNone s
      (fun s' =>
        s'.regs.get64 rd =
          (((s.regs.get64 rs).setWidth wSrc.bits).signExtend wDst.bits).setWidth 64 ∧
        s'.dmem = s.dmem) post := by
  let insSx : Directive := insW wDst (match wSrc with
    | .W8 => .movsx (.reg (regW wDst rd)) (.reg (b8 rs))
    | .W16 => .movsx (.reg (regW wDst rd)) (.reg (h16 rs))
    | .W32 => .movsx (.reg (regW wDst rd)) (.reg (d rs))
    | .W64 => .mov (.reg (regW wDst rd)) (.reg (regW wDst rs)))
  have hd : ∃ df : Directive.FallsTo insSx s
      (fun s' => s' =
        { s with
          regs := s.regs.set64 rd
            ((((s.regs.get64 rs).setWidth wSrc.bits).signExtend wDst.bits).setWidth 64) }),
      (toAmd64Program symName (emitFwd0 (pushDMovsx0 wDst rd wSrc rs []))) = [insSx] := by
    rcases hw with rfl | rfl
    · rcases hs.2 with h64 | rfl | rfl
      · cases h64
      · exact ⟨fallsTo_movsx8 .W32 (.inl rfl) s rd rs, rfl⟩
      · exact ⟨fallsTo_movsx16 .W32 (.inl rfl) s rd rs, rfl⟩
    · cases wSrc with
      | W8 => exact ⟨fallsTo_movsx8 .W64 (.inr rfl) s rd rs, rfl⟩
      | W16 => exact ⟨fallsTo_movsx16 .W64 (.inr rfl) s rd rs, rfl⟩
      | W32 =>
        have hfl := fallsTo_movsx32 s rd rs
        dsimp only [Width.bits]
        rw [BitVec.setWidth_eq]
        exact ⟨hfl, rfl⟩
      | W64 =>
        have hfl := fallsTo_movD s rd rs
        have heq64 : ∀ x : BitVec 64, ((x.setWidth 64).signExtend 64).setWidth 64 = x :=
          fun x => by
            rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
            exact BitVec.eq_of_toInt_eq (BitVec.toInt_signExtend_of_le (le_refl 64))
        dsimp only [Width.bits]
        rw [heq64]
        exact ⟨hfl, rfl⟩
  obtain ⟨df, heq⟩ := hd
  rw [heq]
  exact scalar_fallsTo_single (g := [rd]) (f := maskNone) (P := fun s' =>
    s'.regs.get64 rd =
      (((s.regs.get64 rs).setWidth wSrc.bits).signExtend wDst.bits).setWidth 64 ∧
    s'.dmem = s.dmem) df (by
    rintro _ rfl; exact ⟨⟨Reg64s.get64_set64_same .., rfl⟩, scalarFrame_of_eq
      (fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
      (scalarUpdFlags_of_status_eq rfl _)⟩)

end LeanQbe.T.Bootstrap0
