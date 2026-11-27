module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1

/-!
# Shared Copy-on-Write Combinators for `r2_ensure_excl_ba` / `r2_ensure_excl_array`

The two C0 COW helpers in `lcnf_c0_containers.c` share one control skeleton and differ only in
their capacity constants (`8`/`268435416` vs `4`/`33554428`) and the element copy loop. This file
states that skeleton once, as constant-parameterized `Expr` fragments matching the elaborated
bodies definitionally, and proves their `wp` rules:
- `ensureCapGen` / `ensureCapGen_props`: the generic new-capacity function behind `baEnsureCap`
  and `arrEnsureCap`.
- `ensureExclCore_wp`: header/size/capacity fast path, panic paths and the 5-branch `new_cap`
  computation, leaving only the allocate-and-copy block to the caller.
- `cowTail_wp`: the shared tail freeing (`rc == 1`) or decrementing (`1 < rc < 2^31`) the old
  object.
- `headerStores_wp`: the header/size/capacity initialization shared by `r2_alloc_sarray` and
  `r2_alloc_array`.
Also hosts small load/RC helpers shared by `LcnfC0ContainersProof2` and `LcnfC0ContainersProof3`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

/-! ## 1. Shared Memory and RC Helpers -/

theorem region_pop_cell64 {a : BitVec 64} {rem : Nat} (hrem : 8 ≤ rem) (hfit : rem ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a rem ⋆ R) m) :
    ∃ w : BitVec 64, (cell64 a w ⋆ region (a + 8#64) (rem - 8) ⋆ R) m := by
  have heq : rem = 8 + (rem - 8) := by omega
  rw [heq, region_split (by omega), sep_assoc] at hm
  obtain ⟨w, hw⟩ := sep_ex_l.mp (sep_mono (fun _ hf => region_to_cell64 hf) hm)
  have hw' : (cell64 a w ⋆ (region (a + 8#64) (rem - 8) ⋆ R)) m := hw
  exact ⟨w, sep_cast hw' (by ac_rfl)⟩

theorem region_to_3cells_rem {p : BitVec 64} {bytes : Nat} (hge : 24 ≤ bytes)
    (hfit : bytes ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ R) m) :
    ∃ w0 w1 w2 : BitVec 64,
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
        region (p + 24#64) (bytes - 24) ⋆ R) m := by
  obtain ⟨w0, h0⟩ := region_pop_cell64 (by omega) hfit hm
  have h1in : (region (p + 8#64) (bytes - 8) ⋆ (cell64 p w0 ⋆ R)) m := sep_cast h0 (by ac_rfl)
  obtain ⟨w1, h1⟩ := region_pop_cell64 (by omega) (by omega) h1in
  have h2in : (region (p + 16#64) (bytes - 16) ⋆ (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ R)) m := by
    rw [ptr_add_nat_r2, show bytes - 8 - 8 = bytes - 16 by omega] at h1
    exact sep_cast h1 (by ac_rfl)
  obtain ⟨w2, h2⟩ := region_pop_cell64 (by omega) (by omega) h2in
  rw [ptr_add_nat_r2, show bytes - 16 - 8 = bytes - 24 by omega] at h2
  exact ⟨w0, w1, w2, sep_cast h2 (by ac_rfl)⟩

theorem ba_rc_of_mask_eq1 {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) = 1#64) : o.rc = 1#32 := by
  have hrcEq := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  rw [hrcEq] at hm
  have htn : (BitVec.ofNat 64 o.rc.toNat).toNat = 1 := by rw [hm]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans o.rc.isLt (by decide))] at htn
  exact BitVec.eq_of_toNat_eq htn

theorem ba_rc_ne1_of_mask {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) ≠ 1#64) : o.rc ≠ 1#32 := by
  have hrcEq := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  intro h1
  rw [h1] at hrcEq
  apply hm
  rw [hrcEq]
  rfl

theorem lcnfObjMem_array_elim {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    (cell64 o.addr o.header ⋆
      cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
        (8 * (o.cap - o.fields.length)) ⋆ R) m := by
  rw [lcnfObjMem_array_eq h.2.2.2.2.2.1] at hm
  exact sep_cast hm (by ac_rfl)

theorem arr_load_sz_mid {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_cell64_add8 hs'

theorem arr_load_cap_mid {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 16#64) = some (BitVec.ofNat 64 o.cap) := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_cell64_add16 hs'

theorem arr_load_elem_mid {o : LcnfObj} {i : BitVec 64} (h : ArrCanon o)
    (hi : i.toNat < o.fields.length) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 24#64 + 8#64 * i) = some o.fields[i.toNat] := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (array64 (o.addr + 24#64) o.fields ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_array64_add24_mul8 hs' hi

/-! ## 2. Generic New-Capacity Function -/

/-- New capacity chosen by both COW helpers, parameterized by the initial capacity `init` and
the maximum capacity `maxc`. -/
def ensureCapGen (init maxc sz cap : Nat) (expand : BitVec 64) : Nat :=
  if expand = 0#64 then cap
  else if sz < cap then cap
  else if cap = 0 then init
  else min maxc (cap * 2)

theorem baEnsureCap_eq_gen (sz cap : Nat) (expand : BitVec 64) :
    baEnsureCap sz cap expand = ensureCapGen 8 baMaxCap sz cap expand := rfl

theorem arrEnsureCap_eq_gen (sz cap : Nat) (expand : BitVec 64) :
    arrEnsureCap sz cap expand = ensureCapGen 4 arrMaxCap sz cap expand := rfl

theorem ensureCapGen_props {init maxc sz cap : Nat} {expand : BitVec 64} (hinit : 0 < init)
    (hinitMax : init ≤ maxc) (hsz : sz ≤ cap) (hcap : cap ≤ maxc)
    (hnp : ¬ (expand ≠ 0#64 ∧ cap ≤ sz ∧ maxc ≤ cap)) :
    sz ≤ ensureCapGen init maxc sz cap expand ∧ ensureCapGen init maxc sz cap expand ≤ maxc ∧
      (expand ≠ 0#64 → sz < ensureCapGen init maxc sz cap expand) := by
  unfold ensureCapGen
  by_cases hexp : expand = 0#64
  · simp [hexp, hsz, hcap]
  · have hnge : sz < cap ∨ cap < maxc := by
      by_cases h : sz < cap
      · exact Or.inl h
      · exact Or.inr (Nat.lt_of_not_le fun h' => hnp ⟨hexp, by omega, h'⟩)
    simp only [hexp, ↓reduceIte]
    refine ⟨?_, ?_, fun _ => ?_⟩ <;> (repeat' split) <;> omega

theorem ensureCapGen_of_fast {init maxc sz cap : Nat} {expand : BitVec 64}
    (hfast : expand = 0#64 ∨ sz < cap) : ensureCapGen init maxc sz cap expand = cap := by
  unfold ensureCapGen
  rcases hfast with h | h
  · simp [h]
  · by_cases hexp : expand = 0#64 <;> simp [hexp, h]

theorem slow_not_fast {rc : BitVec 32} {expand : BitVec 64} {sz cap : Nat}
    (hslow : rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ cap ≤ sz)) (hrc1 : rc = 1#32)
    (hfast : expand = 0#64 ∨ sz < cap) : False := by
  rcases hslow with hne | ⟨hex, hge⟩
  · exact hne hrc1
  · rcases hfast with h | h
    · exact hex h
    · omega

/-! ## 3. Shared `Expr` Skeleton of `r2_ensure_excl_{ba,array}` -/

/-- Fast-path test `rc == 1 && (expand == 0 || sz < cap)`, returning `a` or jumping to `J`. -/
def ensureFastExpr (rcv expand sz cap a : Val i64) (J : Cont []) : Expr Val Cont [i64] :=
  .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (Eq.refl Ty.bool),
          args := (Arg.var rcv, Arg.imm 1, ()) } fun p =>
  .jnz (Arg.var p.fst)
    (.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (Eq.refl Ty.bool),
             args := (Arg.var expand, Arg.imm 0, ()) } fun p =>
      .jnz (Arg.var p.fst) (.ret (Arg.var a, ()))
        (.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
                 args := (Arg.var sz, Arg.var cap, ()) } fun p =>
          .jnz (Arg.var p.fst) (.ret (Arg.var a, ())) (.jump J ())))
    (.jump J ())

/-- `lcnf_panic(rt, 2)`. -/
def panicExit (rt : Val i64) : Expr Val Cont [i64] :=
  .exit "lcnf_panic" (as := [i64, i64]) (Arg.var rt, Arg.imm 2, ())

/-- The 5-branch `new_cap` computation (with its `lcnf_panic(rt, 2)` exits), jumping to `J`. -/
def ensureNewCapExpr (init maxc rt expand sz cap : Val i64) (J : Cont [i64]) :
    Expr Val Cont [i64] :=
  .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (Eq.refl Ty.bool),
          args := (Arg.var expand, Arg.imm 0, ()) } fun p =>
  .jnz (Arg.var p.fst)
    (.group (sig := [[i64]]) (fun _ => .cons (fun p => .jump J (Arg.var p.fst, ())) .nil)
      fun K1 =>
      .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (Eq.refl Ty.bool),
              args := (Arg.var cap, Arg.imm 0, ()) } fun p =>
      .jnz (Arg.var p.fst)
        (.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool (Eq.refl Ty.bool),
                 args := (Arg.var sz, Arg.imm init, ()) } fun p =>
          .jnz (Arg.var p.fst) (panicExit rt)
            (.jump K1.fst (Arg.imm init, ())))
        (.group (sig := [[i64]]) (fun _ => .cons (fun p => .jump K1.fst (Arg.var p.fst, ())) .nil)
          fun K2 =>
          .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
                  args := (Arg.var sz, Arg.var cap, ()) } fun p =>
          .jnz (Arg.var p.fst) (.jump K2.fst (Arg.var cap, ()))
            (.group (sig := [[]])
              (fun _ => .cons (fun _ => panicExit rt) .nil)
              fun K3 =>
              .let_ { sig := [i64, i64],
                      code := OpCode.cmp CmpOp.uge i64 Ty.bool (Eq.refl Ty.bool),
                      args := (Arg.var cap, Arg.imm maxc, ()) } fun p =>
              .jnz (Arg.var p.fst) (.jump K3.fst ())
                (.let_ { sig := [i64, i64],
                         code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
                         args := (Arg.var sz, Arg.imm maxc, ()) } fun p =>
                  .jnz (Arg.var p.fst) (.jump K3.fst ())
                    (.let_ { sig := [i64, i64], code := OpCode.mul i64,
                             args := (Arg.var cap, Arg.imm 2, ()) } fun p2 =>
                      .group (sig := [[i64]])
                        (fun _ => .cons (fun p11 =>
                          .group (sig := [[i64]])
                            (fun _ => .cons (fun p => .jump K2.fst (Arg.var p.fst, ())) .nil)
                            fun K5 =>
                            .let_ { sig := [i64, i64],
                                    code := OpCode.cmp CmpOp.uge i64 Ty.bool (Eq.refl Ty.bool),
                                    args := (Arg.var sz, Arg.var p11.fst, ()) } fun p =>
                            .jnz (Arg.var p.fst)
                              (.let_ { sig := [i64, i64], code := OpCode.add i64,
                                       args := (Arg.var sz, Arg.imm 1, ()) } fun p13 =>
                                .let_ { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
                                        args := (Arg.var p13.fst, Arg.imm maxc, ()) } fun p =>
                                .jnz (Arg.var p.fst) (panicExit rt)
                                  (.jump K5.fst (Arg.var p13.fst, ())))
                              (.jump K5.fst (Arg.var p11.fst, ()))) .nil)
                        fun K4 =>
                        .let_ { sig := [i64, i64],
                                code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
                                args := (Arg.var p2.fst, Arg.imm maxc, ()) } fun p =>
                        .jnz (Arg.var p.fst) (.jump K4.fst (Arg.imm maxc, ()))
                          (.jump K4.fst (Arg.var p2.fst, ())))))))
    (.jump J (Arg.var cap, ()))

/-- Everything of `r2_ensure_excl_{ba,array}` after the three header loads, except the
allocate-and-copy block `copy` (which receives the new capacity). -/
def ensureExclCore (init maxc rt a expand rcv sz cap : Val i64)
    (copy : Tup Cont [[i64]] → Blocks Val Cont [i64] [[i64]]) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => .cons (fun _ =>
      .group (sig := [[i64]]) copy fun J => ensureNewCapExpr init maxc rt expand sz cap J.fst) .nil)
    fun J => ensureFastExpr rcv expand sz cap a J.fst

/-- Shared tail: `ret r` after freeing (`rc == 1`) or decrementing (`1 < rc < 2^31`) `a`. -/
def cowTailExpr (rt a hdr rcv r : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[]]) (fun _ => .cons (fun _ => .ret (Arg.var r, ())) .nil) fun J =>
  .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (Eq.refl Ty.bool),
          args := (Arg.var rcv, Arg.imm 1, ()) } fun p =>
  .jnz (Arg.var p.fst)
    (.call "lcnf_free_obj" (as := [i64, i64]) (bs := []) (Arg.var rt, Arg.var a, ())
      fun _ => .jump J.fst ())
    (.group (sig := [[]]) (fun _ => .cons (fun _ => .jump J.fst ()) .nil) fun J' =>
      .let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
              args := (Arg.var rcv, Arg.imm 1, ()) } fun p =>
      .jnz (Arg.var p.fst)
        (.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
                 args := (Arg.var rcv, Arg.imm 2147483648, ()) } fun p =>
          .jnz (Arg.var p.fst)
            (.let_ { sig := [i64, i64], code := OpCode.sub i64,
                     args := (Arg.var hdr, Arg.imm 1, ()) } fun p =>
              .store (Arg.var p.fst) (Arg.var a) (.jump J'.fst ()))
            (.jump J'.fst ()))
        (.jump J'.fst ()))

/-! ## 4. `wp` Rules for the Shared Skeleton -/

theorem val_toNat_two : BitVec.toNat (2 : Val i64) = 2 := rfl

theorem bv64_ofNat_eq_zero_iff {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hn] using this
  · intro h; simp [h]

theorem ensureExclCore_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {init maxc : Nat} (hinit : 0 < init) (hinitMax : init ≤ maxc) (hmax : maxc < 2 ^ 62)
    {rt a expand rcv : BitVec 64} {sz cap : Nat} (hsz : sz ≤ cap) (hcap : cap ≤ maxc)
    {copy : Tup Cont [[i64]] → Blocks Val Cont [i64] [[i64]]}
    (hfast : rcv = 1#64 → (expand = 0#64 ∨ sz < cap) → Q (a, ()) m)
    (hpanic : expand ≠ 0#64 ∧ cap ≤ sz ∧ maxc ≤ cap →
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m)
    (hslow : (rcv ≠ 1#64 ∨ (expand ≠ 0#64 ∧ cap ≤ sz)) →
      ¬ (expand ≠ 0#64 ∧ cap ≤ sz ∧ maxc ≤ cap) → ∀ J : Cont [i64],
      wp Γ Q X (Blocks.get (copy (J, ())) .here
        (BitVec.ofNat 64 (ensureCapGen init maxc sz cap expand), ())) m) :
    wp Γ Q X (ensureExclCore (BitVec.ofNat 64 init) (BitVec.ofNat 64 maxc) rt a expand rcv
      (BitVec.ofNat 64 sz) (BitVec.ofNat 64 cap) copy) m := by
  have hc0 : BitVec.ofNat 64 cap = 0 ↔ cap = 0 := bv64_ofNat_eq_zero_iff (by omega)
  unfold ensureExclCore
  apply wp_join_group (P := fun _ m' => m' = m ∧ (rcv ≠ 1#64 ∨ (expand ≠ 0#64 ∧ cap ≤ sz)))
  · intro _ ⟨⟩ m' ⟨hm', hslow'⟩
    rw [hm']
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hp : expand ≠ 0#64 ∧ cap ≤ sz ∧ maxc ≤ cap
    · apply wp_join_group (P := fun _ _ => False)
      · intro _ _ _ hFalse; exact hFalse.elim
      · intro J _
        unfold ensureNewCapExpr panicExit
        r2_steps <;> exact hpanic hp
    · apply wp_join_group (P := fun (xs : Tup Val [i64]) m1 => match xs with
          | (nc, PUnit.unit) =>
            m1 = m ∧ nc = BitVec.ofNat 64 (ensureCapGen init maxc sz cap expand))
      · intro J ⟨nc, ⟨⟩⟩ m1 ⟨hm1, hnc⟩
        rw [hm1, hnc]
        exact hslow hslow' hp J
      · intro Jnc hJnc
        unfold ensureNewCapExpr panicExit
        by_cases hex : expand = 0#64 <;> r2_steps <;> first
          | exact absurd hex ‹¬expand = 0›
          | exact absurd ‹expand = 0› hex
          | (try simp only [val_toNat_two, hc0] at *
             first
             | (exfalso; omega)
             | (refine hJnc _ _ ⟨rfl, BitVec.eq_of_toNat_eq ?_⟩
                simp only [ensureCapGen, hex, ↓reduceIte, BitVec.toNat_ofNat, BitVec.toNat_mul,
                  val_toNat_two]
                all_goals (repeat' split) <;> omega))
  · intro J hJ
    unfold ensureFastExpr
    r2_steps
    all_goals first
      | exact hfast ‹_› (Or.inl ‹_›)
      | exact hJ _ _ ⟨rfl, Or.inl ‹_›⟩
      | exact hfast ‹_› (Or.inr (by omega))
      | exact hJ _ _ ⟨rfl, Or.inr ⟨‹_›, by omega⟩⟩

/-- Header initialization shared by `r2_alloc_sarray` / `r2_alloc_array`: store `hdr`, `size`,
`cap` at `p`, `p + 8`, `p + 16` and return `p`. -/
def headerStoresExpr (hdr size cap p : Val i64) : Expr Val Cont [i64] :=
  .store (Arg.imm hdr) (Arg.var p)
    (.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p, Arg.imm 8, ()) }
      fun p8 => .store (Arg.var size) (Arg.var p8.fst)
        (.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p, Arg.imm 16, ()) }
          fun p16 => .store (Arg.var cap) (Arg.var p16.fst) (.ret (Arg.var p, ()))))

theorem headerStores_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {hdr size cap p : BitVec 64}
    {bytes : Nat} (hge : 24 ≤ bytes) (hfit : bytes ≤ 2 ^ 64) {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ F) m)
    (hk : ∀ m', (cell64 p hdr ⋆ cell64 (p + 8#64) size ⋆ cell64 (p + 16#64) cap ⋆
      region (p + 24#64) (bytes - 24) ⋆ F) m' → Q (p, ()) m') :
    wp Γ Q X (headerStoresExpr hdr size cap p) m := by
  obtain ⟨w0, w1, w2, hp3⟩ := region_to_3cells_rem hge hfit hm
  unfold headerStoresExpr
  have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
      region (p + 24#64) (bytes - 24) ⋆ F)) m := sep_cast hp3 (by ac_rfl)
  apply wp_store_sep (store_cell64 hdr hpc)
  intro m2 hm2
  c0_step
  have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p hdr ⋆ cell64 (p + 16#64) w2 ⋆
      region (p + 24#64) (bytes - 24) ⋆ F)) m2 := sep_cast hm2 (by ac_rfl)
  apply wp_store_sep (store_cell64 size hm2')
  intro m3 hm3
  c0_step
  have hm3' : (cell64 (p + 16#64) w2 ⋆ (cell64 p hdr ⋆ cell64 (p + 8#64) size ⋆
      region (p + 24#64) (bytes - 24) ⋆ F)) m3 := sep_cast hm3 (by ac_rfl)
  apply wp_store_sep (store_cell64 cap hm3')
  intro m4 hm4
  r2_steps
  exact hk m4 (sep_cast hm4 (by ac_rfl))

/-- `wp` of the shared tail: frees the old object `o` when `rc == 1`, decrements its header when
`1 < rc < 2^31`, and leaves persistent (`rc == 0`) objects untouched. -/
theorem cowTail_wp {rt r : BitVec 64} {o : LcnfObj} (hwf : o.Wf) {st : RtC0State}
    {F : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hm : (lcnfObjMem o ⋆ (rtC0Inv rt st ⋆ F)) m)
    (hk : ∀ st' m', st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆
        (if o.rc = 1#32 then emp else lcnfObjMem (o.withRc (decNonExclRc o.rc))) ⋆ F) m' →
      Q (r, ()) m') :
    wp rtR2Env Q X (cowTailExpr rt o.addr o.header (o.header &&& 4294967295#64) r) m := by
  have hrcEq := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  have hrcLt : o.rc.toNat < 2 ^ 64 := Nat.lt_trans o.rc.isLt (by decide)
  have hmaskTo : (o.header &&& 4294967295#64).toNat = o.rc.toNat := by
    rw [hrcEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrcLt]
  have h0 := hwf.2.2.1
  rw [BitVec.toInt_eq_toNat_cond] at h0
  unfold cowTailExpr
  r2_steps
  · have hrc1 := ba_rc_of_mask_eq1 hwf (by assumption)
    have hnotAnd : ¬ (o.addr &&& 1#64) ≠ 0#64 := by simp [bv64_and1_zero_of_mod8 hwf.2.1]
    r2_call rtR2Env_lcnf_free_obj
    dsimp only [lcnfFreeObjSpec, vals, Tup.map, Arg.val]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnotAnd)]
    have hmFree0 := sep_mono (fun _ hf => lcnfObjMem_to_freeObjLayout hwf hf) hm
    have hmFree : (rtC0Inv rt st ⋆ freeObjLayout o.addr o.totalBytes o.header ⋆ F) m :=
      sep_cast hmFree0 (by ac_rfl)
    refine ⟨st, o.header, o.totalBytes, _, hwf.1, hwf.2.1, hwf.2.2.2.2.2.2.1,
      hwf.2.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.2.1, hmFree, ?_⟩
    intro st2 m3 hpr2 hrem2 _ hm3
    r2_steps
    refine hk st2 m3 hpr2 (Nat.le_of_eq hrem2) ?_
    rw [ite_eq_left_of_eq_true _ _ (eq_true hrc1)]
    exact sep_cast hm3 (by ac_rfl)
  · have hrcNe1 := ba_rc_ne1_of_mask hwf (by assumption)
    have hgt1 : 1 < o.rc.toNat := by
      have hc1 : 1 < (o.header &&& 4294967295#64).toNat := by assumption
      rwa [hmaskTo] at hc1
    have hgtInt : 1 < o.rc.toInt := by
      have hc2 : (o.header &&& 4294967295#64).toNat < 2147483648 := by assumption
      rw [hmaskTo] at hc2
      rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
    obtain ⟨hok, hm3⟩ := lcnfObjMem_store_rc (o.rc - 1#32) hm
    rw [← lcnfObjHeader_sub1 o hwf hgt1] at hm3
    apply wp_store_sep ⟨hok, hm3⟩
    intro m3 hm3'
    r2_steps
    refine hk st m3 (RtC0State.PreservesMeta.refl st) (Nat.le_refl _) ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1)]
    simp only [decNonExclRc, hgtInt, ↓reduceIte]
    exact sep_cast hm3' (by ac_rfl)
  · have hrcNe1 := ba_rc_ne1_of_mask hwf (by assumption)
    have hnot : ¬ 1 < (o.header &&& 4294967295#64).toNat := hc
    rw [hmaskTo] at hnot
    have hrc0 : o.rc = 0#32 := by
      have hne1 : o.rc.toNat ≠ 1 := fun h => hrcNe1 (BitVec.eq_of_toNat_eq h)
      exact BitVec.eq_of_toNat_eq (by simp; omega)
    r2_steps
    refine hk st m (RtC0State.PreservesMeta.refl st) (Nat.le_refl _) ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1)]
    have hwid : o.withRc (decNonExclRc o.rc) = o := by
      rw [show decNonExclRc o.rc = o.rc by simp [decNonExclRc, hrc0]]
      cases o; rfl
    rw [hwid]
    exact sep_cast hm (by ac_rfl)

end LeanQbe.T.LeanLCNF
