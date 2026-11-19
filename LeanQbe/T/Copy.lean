module

public import LeanQbe.T.OptUtil

/-!
# Copy and tuple-pair propagation (`T6`)

PHOAS-to-PHOAS optimisation pass `copy : Nat → Expr (CVal V) L rs → Expr V L rs` where every
variable carries:
* its replacement operand `out : Arg V t`,
* an optional fresh lexical identity `id : Option Nat`,
* known pair decomposition `parts : CParts V t` (when constructed via `mkpair` or immediate pair),
* optional projection provenance `fstOf` / `sndOf` (when projected via `unpair`).

Eliminates:
* `OpCode.copy t a` → forwards `a`;
* `OpCode.unpair a b p` when `p` is an immediate pair or has known `.pair x y` components →
  forwards `(x, y)` (so `fst`/`snd` of constructed or constant pairs vanish);
* `OpCode.mkpair a b x y` when both operands are immediates → immediate pair `(c₁, c₂)`;
* `OpCode.mkpair a b x y` when `x` is the `fst` and `y` is the `snd` of the same `unpair`
  (`pid₁ = pid₂` and types match) → forwards original pair `p` (while preserving `.pair x y`
  knowledge in case it is projected again).
* When `mkpair` is kept, records `.pair x y` on the result so subsequent `unpair`/`fst`/`snd`
  operations are still eliminated.

Correctness (`LeanQbe/T/CopyLemmas.lean`): `copy_wp`, `copy_wf`, `Func.copy_spec`, `Func.copy_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

mutual
/-- Input value representation in `copy`, tracking copy/pair/projection provenance. -/
inductive CVal (V : Ty → Type) : Ty → Type
  | mk {t : Ty} (out : Arg V t) (id : Option Nat)
      (parts : CParts V t) (fstOf : CProjFst V t) (sndOf : CProjSnd V t) : CVal V t

/-- Known pair decomposition for `CVal`. -/
inductive CParts (V : Ty → Type) : Ty → Type
  | unknown {t : Ty} : CParts V t
  | pair {a b : Ty} (x : CVal V a) (y : CVal V b) : CParts V (.pair a b)

/-- Provenance recording that a value came from `fst` of an `unpair` with identity `pid`. -/
inductive CProjFst (V : Ty → Type) : Ty → Type
  | none {t : Ty} : CProjFst V t
  | some {a b : Ty} (pid : Nat) (p : CVal V (.pair a b)) : CProjFst V a

/-- Provenance recording that a value came from `snd` of an `unpair` with identity `pid`. -/
inductive CProjSnd (V : Ty → Type) : Ty → Type
  | none {t : Ty} : CProjSnd V t
  | some {a b : Ty} (pid : Nat) (p : CVal V (.pair a b)) : CProjSnd V b
end

def CVal.out {V : Ty → Type} {t : Ty} : CVal V t → Arg V t
  | .mk out _ _ _ _ => out

def CVal.id {V : Ty → Type} {t : Ty} : CVal V t → Option Nat
  | .mk _ id _ _ _ => id

def CVal.parts {V : Ty → Type} {t : Ty} : CVal V t → CParts V t
  | .mk _ _ parts _ _ => parts

def CVal.fstOf {V : Ty → Type} {t : Ty} : CVal V t → CProjFst V t
  | .mk _ _ _ fstOf _ => fstOf

def CVal.sndOf {V : Ty → Type} {t : Ty} : CVal V t → CProjSnd V t
  | .mk _ _ _ _ sndOf => sndOf

/-- Build a `CVal` from an immediate constant, decomposing nested constant pairs recursively. -/
def CVal.ofImm {V : Ty → Type} : (t : Ty) → Val t → CVal V t
  | .pair a b, (c₁, c₂) =>
    .mk (.imm (c₁, c₂)) none (.pair (CVal.ofImm a c₁) (CVal.ofImm b c₂)) .none .none
  | _, c => .mk (.imm c) none .unknown .none .none

/-- Fresh variable `CVal` with unique lexical identity `next`. -/
def CVal.fresh {V : Ty → Type} {t : Ty} (v : V t) (next : Nat) : CVal V t :=
  .mk (.var v) (some next) .unknown .none .none

/-- Promote an `Arg (CVal V)` to `CVal V` by expanding `.imm`. -/
def Arg.toCVal {V : Ty → Type} {t : Ty} : Arg (CVal V) t → CVal V t
  | .var c => c
  | .imm c => CVal.ofImm t c

/-- Output operand `Arg V t` of an `Arg (CVal V) t`. -/
def Arg.cout {V : Ty → Type} {t : Ty} : Arg (CVal V) t → Arg V t
  | .var c => c.out
  | .imm c => .imm c

/-- Map `Arg.cout` across a tuple of operands. -/
abbrev tupCOut {V : Ty → Type} : {ts : List Ty} → Tup (Arg (CVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.cout

/-- Wrap bound output variables `xs : Tup V ts` into fresh `CVal V`s starting at `next`. -/
abbrev freshCVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (CVal V) ts :=
  tupFreshWith fun x next => CVal.fresh x next

/-- Outcome of lowering a `let_` binding in `copy`: either eliminate or emit with wrapper. -/
inductive CopyLetStep (V : Ty → Type) : List Ty → Type
  | elim {ts : List Ty} (res : Tup (CVal V) ts) : CopyLetStep V ts
  | emit {ts : List Ty} (op : Op V ts) (next' : Nat) (wrap : Tup V ts → Tup (CVal V) ts) :
      CopyLetStep V ts

/-- Fallback step when `mkpair` is not eliminated: emit `mkpair` and record `.pair cx cy`. -/
def mkpairEmitStep {V : Ty → Type} (next : Nat) (a b : Ty) (cx : CVal V a) (cy : CVal V b) :
    CopyLetStep V [.pair a b] :=
  .emit (op2 (.mkpair a b) cx.out cy.out) (next + 1) fun (vp, ()) =>
    (.mk (.var vp) (some next) (.pair cx cy) .none .none, ())

/-- Eliminate `mkpair (fst p) (snd p) → p` when both sides share the same `unpair` identity. -/
def mkpairProjStep {V : Ty → Type} (next : Nat) (a b : Ty) (cx : CVal V a) (cy : CVal V b) :
    CopyLetStep V [.pair a b] :=
  match cx.fstOf, cy.sndOf with
  | .some pid₁ (b := b₁) p₁, .some pid₂ _ =>
    if pid₁ == pid₂ then
      match tyDecEq b₁ b with
      | isTrue hb =>
        let p₁' : CVal V (.pair a b) :=
          cast (congrArg (fun u => CVal V (.pair a u)) hb) p₁
        .elim (.mk p₁'.out p₁'.id (.pair cx cy) p₁'.fstOf p₁'.sndOf, ())
      | isFalse _ => mkpairEmitStep next a b cx cy
    else mkpairEmitStep next a b cx cy
  | _, _ => mkpairEmitStep next a b cx cy

/-- Simplify or emit `mkpair a b cx cy`. -/
def mkpairStep {V : Ty → Type} (next : Nat) (a b : Ty) (cx : CVal V a) (cy : CVal V b) :
    CopyLetStep V [.pair a b] :=
  match cx.out, cy.out with
  | .imm c₁, .imm c₂ =>
    .elim (.mk (.imm (c₁, c₂)) none (.pair cx cy) .none .none, ())
  | _, _ => mkpairProjStep next a b cx cy

/-- Lower one `let_` operation in `copy` (copy/unpair/mkpair elimination and provenance). -/
def Op.copyLet {V : Ty → Type} {ts : List Ty} (op : Op (CVal V) ts) (next : Nat) :
    CopyLetStep V ts :=
  let ⟨code, args⟩ := op
  match code, args with
  | .copy _, (a, ()) => .elim (a.toCVal, ())
  | .unpair a b, (p, ()) =>
    let cp := p.toCVal
    match cp.parts with
    | .pair x y => .elim (x, y, ())
    | .unknown =>
      .emit (op1 (.unpair a b) cp.out) (next + 2) fun (vx, vy, ()) =>
        match cp.id with
        | some pid =>
          (.mk (.var vx) (some next) .unknown (.some pid cp) .none,
           .mk (.var vy) (some (next + 1)) .unknown .none (.some pid cp), ())
        | none => (CVal.fresh vx next, CVal.fresh vy (next + 1), ())
  | .mkpair a b, (x, y, ()) => mkpairStep next a b x.toCVal y.toCVal
  | code, args =>
    .emit ⟨code, tupCOut args⟩ (next + ts.length) fun xs => freshCVals ts xs next

mutual
def copy {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    Expr (CVal V) L rs → Expr V L rs
  | .let_ op k =>
    match op.copyLet next with
    | .elim res => copy next (k res)
    | .emit op' next' wrap => .let_ op' fun xs => copy next' (k (wrap xs))
  | .load t a k =>
    .load t a.cout fun v => copy (next + 1) (k (CVal.fresh v next))
  | .store v a k =>
    .store v.cout a.cout (copy next k)
  | .call f (bs := bs) args k =>
    .call f (tupCOut args) fun xs =>
      copy (next + bs.length) (k (freshCVals bs xs next))
  | .jnz c t e =>
    .jnz c.cout (copy next t) (copy next e)
  | .jump j args => .jump j (tupCOut args)
  | .ret vs => .ret (tupCOut vs)
  | .exit f args => .exit f (tupCOut args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => copyB next (bodies Js)) (fun Js => copy next (k Js))

def copyB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    {sig : List (List Ty)} → Blocks (CVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => copy (next + ts.length) (b (freshCVals ts xs next))) (copyB next bs)
end

/-- Propagate copies, known pair constructions/projections, and identity tuple copies on `Func`. -/
def Func.copy {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.copy as.length (f (CVal V) L (freshCVals as xs 0))

end LeanQbe.T
