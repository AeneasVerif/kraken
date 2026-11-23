module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.Examples.ChaChaProg

/-!
# ChaCha20 Block on 128-bit `v4i32` Rows

100%-PHOAS typed IR implementation and `wp` verification against an RFC 8439 functional model
(128-bit `vec 2 i32` rows only, no SHA-NI, no wider vector widths, no `TFlat` dependencies):

* RFC 8439 §2.1–2.3 functional specification (`quarterRound`, `rfcInnerBlock`, `rfcChaCha20Core`,
  `rfcChaCha20Block`, little-endian byte serialization) + `decide`-checked RFC 8439 §2.1.1 and
  §2.3.2 test vectors.
* `chacha20Block`: 128-bit row-SIMD IR using 128-bit vector opcodes (`load`/`store` `v4i32`,
  `add`, `xor`, `rotl` by constant splat, `shufd` = `pshufd`) in a 10-double-round `loop`.
* `chacha20Block_correct` (`wp` via `wp_loop_break_group`), `chacha20Block_rfc8439_vector`, and
  100%-PHOAS `chacha20Block_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.ChaCha

open Std.ExtHashMap
open LeanQbe.T.ProofUtil

/-! ## RFC 8439 functional model -/

abbrev Word := BitVec 32
abbrev Row := Val v4i32

def mkRow (w0 w1 w2 w3 : Word) : Row := ((w0, w1), (w2, w3))

/-- 4×4 matrix of 32-bit words represented as four 128-bit rows. -/
structure State where
  r0 : Row
  r1 : Row
  r2 : Row
  r3 : Row
  deriving DecidableEq, Repr

def rowToList (r : Row) : List Word := [r.1.1, r.1.2, r.2.1, r.2.2]

def State.toRows (s : State) : List Row := [s.r0, s.r1, s.r2, s.r3]

def State.toWords (s : State) : List Word :=
  rowToList s.r0 ++ rowToList s.r1 ++ rowToList s.r2 ++ rowToList s.r3

def wordToLEBytes (w : Word) : List UInt8 :=
  [ UInt8.ofNat (w.toNat % 256)
  , UInt8.ofNat ((w.toNat / 256) % 256)
  , UInt8.ofNat ((w.toNat / 65536) % 256)
  , UInt8.ofNat ((w.toNat / 16777216) % 256) ]

def State.toBytes (s : State) : List UInt8 :=
  s.toWords.flatMap wordToLEBytes

/-- RFC 8439 §2.1: ChaCha quarter round on four 32-bit words. -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  let a := a + b; let d := (d ^^^ a).rotateLeft 16
  let c := c + d; let b := (b ^^^ c).rotateLeft 12
  let a := a + b; let d := (d ^^^ a).rotateLeft 8
  let c := c + d; let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- RFC 8439 §2.3: Column round — four quarter rounds on columns `(0,4,8,12)` .. `(3,7,11,15)`. -/
def rfcColumnRound (s : State) : State :=
  let (s0, s4, s8,  s12) := quarterRound s.r0.1.1 s.r1.1.1 s.r2.1.1 s.r3.1.1
  let (s1, s5, s9,  s13) := quarterRound s.r0.1.2 s.r1.1.2 s.r2.1.2 s.r3.1.2
  let (s2, s6, s10, s14) := quarterRound s.r0.2.1 s.r1.2.1 s.r2.2.1 s.r3.2.1
  let (s3, s7, s11, s15) := quarterRound s.r0.2.2 s.r1.2.2 s.r2.2.2 s.r3.2.2
  ⟨mkRow s0 s1 s2 s3, mkRow s4 s5 s6 s7, mkRow s8 s9 s10 s11, mkRow s12 s13 s14 s15⟩

/-- RFC 8439 §2.3: Diagonal round — four quarter rounds on `(0,5,10,15)`, `(1,6,11,12)`,
`(2,7,8,13)`, `(3,4,9,14)`. -/
def rfcDiagonalRound (s : State) : State :=
  let (s0, s5, s10, s15) := quarterRound s.r0.1.1 s.r1.1.2 s.r2.2.1 s.r3.2.2
  let (s1, s6, s11, s12) := quarterRound s.r0.1.2 s.r1.2.1 s.r2.2.2 s.r3.1.1
  let (s2, s7, s8,  s13) := quarterRound s.r0.2.1 s.r1.2.2 s.r2.1.1 s.r3.1.2
  let (s3, s4, s9,  s14) := quarterRound s.r0.2.2 s.r1.1.1 s.r2.1.2 s.r3.2.1
  ⟨mkRow s0 s1 s2 s3, mkRow s4 s5 s6 s7, mkRow s8 s9 s10 s11, mkRow s12 s13 s14 s15⟩

/-- RFC 8439 §2.3: `inner_block` = one column round followed by one diagonal round (2 rounds). -/
def rfcInnerBlock (s : State) : State :=
  rfcDiagonalRound (rfcColumnRound s)

/-- Iterate `rfcInnerBlock` `n` times. -/
def rfcRounds : Nat → State → State
  | 0, s => s
  | n + 1, s => rfcRounds n (rfcInnerBlock s)

def rowAdd (a b : Row) : Row :=
  mkRow (a.1.1 + b.1.1) (a.1.2 + b.1.2) (a.2.1 + b.2.1) (a.2.2 + b.2.2)

def State.add (a b : State) : State :=
  ⟨rowAdd a.r0 b.r0, rowAdd a.r1 b.r1, rowAdd a.r2 b.r2, rowAdd a.r3 b.r3⟩

/-- RFC 8439 §2.3: ChaCha20 core permutation (10 double rounds + feedforward addition). -/
def rfcChaCha20Core (init : State) : State :=
  (rfcRounds 10 init).add init

/-- RFC 8439 §2.3 constants `"expand 32-byte k"` in little-endian 32-bit words. -/
def constRow : Row := mkRow 0x61707865#32 0x3320646e#32 0x79622d32#32 0x6b206574#32

/-- RFC 8439 §2.3 initial state from 8 key words, 1 counter word, and 3 nonce words. -/
def rfcInitState (k0 k1 k2 k3 k4 k5 k6 k7 counter n0 n1 n2 : Word) : State :=
  ⟨constRow, mkRow k0 k1 k2 k3, mkRow k4 k5 k6 k7, mkRow counter n0 n1 n2⟩

/-- RFC 8439 §2.3 `chacha20_block(key, counter, nonce)`. -/
def rfcChaCha20Block (k0 k1 k2 k3 k4 k5 k6 k7 counter n0 n1 n2 : Word) : State :=
  rfcChaCha20Core (rfcInitState k0 k1 k2 k3 k4 k5 k6 k7 counter n0 n1 n2)

/-! ## RFC 8439 test vector checks (by `decide`) -/

/-- RFC 8439 §2.1.1 Quarter Round test vector. -/
theorem rfc8439_quarterRound_test :
    quarterRound 0x11111111#32 0x01020304#32 0x9b8d6f43#32 0x01234567#32 =
      (0xea2a92f4#32, 0xcb1cf8ce#32, 0x4581472e#32, 0x5881c4bb#32) := by
  decide

/-- RFC 8439 §2.3.2 ChaCha20 block test vector input state. -/
def rfc8439_test_init : State :=
  rfcInitState
    0x03020100#32 0x07060504#32 0x0b0a0908#32 0x0f0e0d0c#32
    0x13121110#32 0x17161514#32 0x1b1a1918#32 0x1f1e1d1c#32
    0x00000001#32 0x09000000#32 0x4a000000#32 0x00000000#32

def rfc8439_expected_words : List Word :=
  [ 0xe4e7f110#32, 0x15593bd1#32, 0x1fdd0f50#32, 0xc47120a3#32
  , 0xc7f4d1c7#32, 0x0368c033#32, 0x9aaa2204#32, 0x4e6cd4c3#32
  , 0x466482d2#32, 0x09aa9f07#32, 0x05d7c214#32, 0xa2028bd9#32
  , 0xd19c12b5#32, 0xb94e16de#32, 0xe883d0cb#32, 0x4e3c50a2#32 ]

def rfc8439_expected_bytes : List UInt8 :=
  [ 0x10, 0xf1, 0xe7, 0xe4, 0xd1, 0x3b, 0x59, 0x15
  , 0x50, 0x0f, 0xdd, 0x1f, 0xa3, 0x20, 0x71, 0xc4
  , 0xc7, 0xd1, 0xf4, 0xc7, 0x33, 0xc0, 0x68, 0x03
  , 0x04, 0x22, 0xaa, 0x9a, 0xc3, 0xd4, 0x6c, 0x4e
  , 0xd2, 0x82, 0x64, 0x46, 0x07, 0x9f, 0xaa, 0x09
  , 0x14, 0xc2, 0xd7, 0x05, 0xd9, 0x8b, 0x02, 0xa2
  , 0xb5, 0x12, 0x9c, 0xd1, 0xde, 0x16, 0x4e, 0xb9
  , 0xcb, 0xd0, 0x83, 0xe8, 0xa2, 0x50, 0x3c, 0x4e ]

theorem rfc8439_test_vector_words :
    (rfcChaCha20Core rfc8439_test_init).toWords = rfc8439_expected_words := by
  decide

theorem rfc8439_test_vector_bytes :
    (rfcChaCha20Core rfc8439_test_init).toBytes = rfc8439_expected_bytes := by
  decide

/-! ## Public specification -/

def chacha20BlockSpec : Spec [i64, i64] [] := fun (out, inp, ()) m Q _ =>
  ∃ (init : State) (old : List Row) (R : Mem 64 → Prop),
    old.length = 4 ∧
    (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows ⋆ R) m ∧
    ∀ m',
      (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
        array (t := v4i32) inp init.toRows ⋆ R) m' →
      Q () m'

/-! ## Fragment and top-level `wp` proofs -/

theorem vecQrK_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (s : State)
    (k : Row → Row → Row → Row → Expr Val Cont rs)
    (hk : let s' := rfcColumnRound s; wp Γ Q X (k s'.r0 s'.r1 s'.r2 s'.r3) m) :
    wp Γ Q X (vecQrK s.r0 s.r1 s.r2 s.r3 k) m := by
  rcases s with ⟨⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩, ⟨⟨b0, b1⟩, ⟨b2, b3⟩⟩,
    ⟨⟨c0, c1⟩, ⟨c2, c3⟩⟩, ⟨⟨d0, d1⟩, ⟨d2, d3⟩⟩⟩
  unfold vecQrK
  wp_unfold
  simpa [rfcColumnRound, quarterRound, mkRow] using hk

theorem doubleRoundK_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (s : State)
    (k : Row → Row → Row → Row → Expr Val Cont rs)
    (hk : let s' := rfcInnerBlock s; wp Γ Q X (k s'.r0 s'.r1 s'.r2 s'.r3) m) :
    wp Γ Q X (doubleRoundK s.r0 s.r1 s.r2 s.r3 k) m := by
  unfold doubleRoundK
  refine vecQrK_spec s _ ?_
  dsimp only
  wp_unfold
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [shufd_v4i32_39, shufd_v4i32_4e, shufd_v4i32_93]
  refine vecQrK_spec
    ⟨(rfcColumnRound s).r0,
     mkRow (rfcColumnRound s).r1.1.2 (rfcColumnRound s).r1.2.1
       (rfcColumnRound s).r1.2.2 (rfcColumnRound s).r1.1.1,
     mkRow (rfcColumnRound s).r2.2.1 (rfcColumnRound s).r2.2.2
       (rfcColumnRound s).r2.1.1 (rfcColumnRound s).r2.1.2,
     mkRow (rfcColumnRound s).r3.2.2 (rfcColumnRound s).r3.1.1
       (rfcColumnRound s).r3.1.2 (rfcColumnRound s).r3.2.1⟩
    _ ?_
  dsimp only
  wp_unfold
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [shufd_v4i32_93, shufd_v4i32_4e, shufd_v4i32_39]
  simpa [rfcInnerBlock, rfcDiagonalRound, rfcColumnRound, mkRow] using hk

theorem chacha20Block_correct (Γ : Env) :
    ∀ args m Q X, chacha20BlockSpec args m Q X → Func.spec Γ chacha20Block args m Q X := by
  rintro ⟨out, inp, ⟨⟩⟩ m Q X ⟨init, old, R, hold, hm, hQ⟩
  rcases old with _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, _ | _⟩⟩⟩⟩ <;> simp at hold
  dsimp only [Func.spec, Func.wp, chacha20Block]
  wp_unfold
  have hb : v4i32.bytes ≤ 2 ^ 64 := by decide
  have hmInp : (array (t := v4i32) inp init.toRows ⋆
      (array (t := v4i32) out [o0, o1, o2, o3] ⋆ R)) m := sep_ac hm
  refine ⟨init.r0, by simpa [State.toRows, Ty.bytes, Ty.size]
    using loadVal_array (i := 0) hb (by simp [State.toRows]) hmInp, ?_⟩
  refine ⟨init.r1, by simpa [State.toRows, Ty.bytes, Ty.size]
    using loadVal_array (i := 1) hb (by simp [State.toRows]) hmInp, ?_⟩
  refine ⟨init.r2, by simpa [State.toRows, Ty.bytes, Ty.size]
    using loadVal_array (i := 2) hb (by simp [State.toRows]) hmInp, ?_⟩
  refine ⟨init.r3, by simpa [State.toRows, Ty.bytes, Ty.size]
    using loadVal_array (i := 3) hb (by simp [State.toRows]) hmInp, ?_⟩
  refine wp_loop_break_group
    (fun (r0, r1, r2, r3, ()) m' =>
      m' = m ∧ State.mk r0 r1 r2 r3 = rfcRounds 10 init)
    (fun n (r0, r1, r2, r3, cnt, ()) m' =>
      m' = m ∧ 1 ≤ n ∧ n ≤ 10 ∧ cnt = BitVec.ofNat 32 n ∧
      rfcRounds n (State.mk r0 r1 r2 r3) = rfcRounds 10 init)
    ?_ ?_ ?_
  · intro _ ⟨f0, f1, f2, f3, ⟨⟩⟩ m' ⟨hm', hst⟩
    subst hm'
    dsimp only [Blocks.get_here]
    wp_unfold
    have hfin : State.mk (rowAdd f0 init.r0) (rowAdd f1 init.r1)
                         (rowAdd f2 init.r2) (rowAdd f3 init.r3) = rfcChaCha20Core init := by
      show State.add ⟨f0, f1, f2, f3⟩ init = (rfcRounds 10 init).add init
      rw [hst]
    have hmOut : (array (t := v4i32) out [o0, o1, o2, o3] ⋆
        (array (t := v4i32) inp init.toRows ⋆ R)) m' := sep_ac hm
    obtain ⟨ok0, hm0⟩ := store_array (i := 0) (rowAdd f0 init.r0) hb (by simp) hmOut
    refine ⟨by simpa [Ty.bytes, Ty.size] using ok0, ?_⟩
    obtain ⟨ok1, hm1⟩ := store_array (i := 1) (rowAdd f1 init.r1) hb (by simp) hm0
    refine ⟨by simpa [Ty.bytes, Ty.size, rowAdd, mkRow] using ok1, ?_⟩
    obtain ⟨ok2, hm2⟩ := store_array (i := 2) (rowAdd f2 init.r2) hb (by simp) hm1
    refine ⟨by simpa [Ty.bytes, Ty.size, rowAdd, mkRow] using ok2, ?_⟩
    obtain ⟨ok3, hm3⟩ := store_array (i := 3) (rowAdd f3 init.r3) hb (by simp) hm2
    refine ⟨by simpa [Ty.bytes, Ty.size, rowAdd, mkRow] using ok3, hQ _ ?_⟩
    have hrows : [rowAdd f0 init.r0, rowAdd f1 init.r1,
                  rowAdd f2 init.r2, rowAdd f3 init.r3] = (rfcChaCha20Core init).toRows := by
      rw [← hfin]; rfl
    rw [← hrows]
    exact sep_ac (by simpa [Ty.bytes, Ty.size, rowAdd, mkRow] using hm3)
  · intro B L n ⟨r0, r1, r2, r3, cnt, ⟨⟩⟩ m' hB hL ⟨hm', hge1, hle10, hcnt, hrnd⟩
    subst hm'
    dsimp only [Blocks.get_here]
    refine doubleRoundK_spec ⟨r0, r1, r2, r3⟩ _ ?_
    dsimp only
    wp_unfold
    subst hcnt
    have hsub : BitVec.ofNat 32 n - (1 : BitVec 32) = BitVec.ofNat 32 (n - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp; omega
    rw [hsub]
    have hrnd' : rfcRounds (n - 1) (rfcInnerBlock ⟨r0, r1, r2, r3⟩) = rfcRounds 10 init := by
      cases n with
      | zero => omega
      | succ k => simpa [rfcRounds] using hrnd
    refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hne0 : n - 1 ≠ 0 := by
        intro h0; apply hne; rw [h0]; rfl
      exact hL (n - 1) _ m' (by omega) ⟨rfl, by omega, by omega, rfl, hrnd'⟩
    · have h0 : n - 1 = 0 := by
        have := congrArg BitVec.toNat heq
        have h0_val : (0 : BitVec 32).toNat = 0 := rfl
        rw [BitVec.toNat_ofNat, h0_val] at this
        omega
      rw [h0, rfcRounds] at hrnd'
      exact hB _ m' ⟨rfl, hrnd'⟩
  · intro _ L _ hL
    wp_unfold
    exact hL 10 (init.r0, init.r1, init.r2, init.r3, (10 : BitVec 32), ()) m
      ⟨rfl, by decide, by decide, rfl, rfl⟩

/-- Concrete non-vacuous RFC 8439 §2.3.2 corollary: `chacha20Block` on `rfc8439_test_init`
writes the exact RFC 8439 §2.3.2 output state. -/
theorem chacha20Block_rfc8439_vector (Γ : Env) (out inp : BitVec 64) (old : List Row)
    (R : Mem 64 → Prop) (m : Mem 64) (hold : old.length = 4)
    (hm : (array (t := v4i32) out old ⋆ array (t := v4i32) inp rfc8439_test_init.toRows ⋆ R) m) :
    Func.spec Γ chacha20Block (out, inp, ()) m
      (fun _ m' => ∃ res : State,
        res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
        (array (t := v4i32) out res.toRows ⋆
          array (t := v4i32) inp rfc8439_test_init.toRows ⋆ R) m')
      (fun _ _ _ _ => False) :=
  chacha20Block_correct Γ (out, inp, ()) m _ _
    ⟨rfc8439_test_init, old, R, hold, hm, fun _ hm' =>
      ⟨rfcChaCha20Core rfc8439_test_init, rfc8439_test_vector_words,
        rfc8439_test_vector_bytes, hm'⟩⟩

/-! ## 100%-PHOAS `Func.Wf` proof (no `TFlat`) -/

theorem chacha20Block_wf : Func.Wf chacha20Block := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  dsimp only [chacha20Block]
  t_wf_tac

/-! ## `Module`, `Env`, and `ModuleOk` bundle -/

def chacha20Module : Module := ⟨[chacha20Fn], [], []⟩

def chacha20Env : Env
  | "chacha20Block", [.bits 64, .bits 64], [] => chacha20BlockSpec
  | _, _, _ => fun _ _ _ _ => False

theorem chacha20Module_checkAcyclic : chacha20Module.checkAcyclic = true := by rfl

theorem chacha20_moduleOk : ModuleOk chacha20Env chacha20Module :=
  Module.moduleOk_of_checkAcyclic chacha20Module_checkAcyclic
    (fun fn hmem => by
      simp only [chacha20Module, List.mem_singleton] at hmem
      subst hmem; exact chacha20Block_wf)
    (fun fn hmem => by
      simp only [chacha20Module, List.mem_singleton] at hmem
      subst hmem; exact chacha20Block_correct chacha20Env)

end LeanQbe.T.Examples.ChaCha
