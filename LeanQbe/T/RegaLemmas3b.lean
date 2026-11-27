module

public import LeanQbe.T.RegaLemmas3a
public import LeanQbe.T.RegaLemmasZero
public import LeanQbe.T.RegaLemmasRemat

/-!
# `RegaLemmas` Part 3b: Slot Operations, `lowerOp_ok`, and Structural `LabelsUnique`

`trySlotOp_ok`, `lowerOp_ok`, and structural label bounds (`LabelClean`, `lname_inj`,
`lowerExpr_labels`/`lowerBlocks_labels`, `lowerFn_labelsUnique`, `lowerFn_label_mem`,
`lowerExpr_nv_le`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

private theorem tryTestSlot_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {neg : Bool}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vt : BitVec w} {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hmt : ⟨.bits w, vt, t⟩ ∈ G) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryTestSlot T.toIsa hints st neg w t pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits vt 0#w
        T.mach.PDstHolds s' .bool pd res ∧
        (∀ cc, testBoolExtra? T.toIsa neg clob pd = some cc → T.mach.evalCond s' cc = res) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  have hsp : ∀ idx r, r ∈ (spAddr T.toIsa idx).regs → r ∉ T.frame.scratch := fun idx r hr => by
    simp only [spAddr, AddrArg.regs, List.mem_singleton] at hr
    subst hr; exact T.frameSpec.sp_disj.1
  unfold tryTestSlot at h
  split at h; · simp at h
  rename_i hstd
  replace hstd : isStdBitWidth w = true := by simpa using hstd
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm w' x ci =>
      simp only [hdef] at h
      split at h
      · rename_i hweq
        obtain rfl : w' = w := Nat.beq_eq.mp hweq
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, hmx, rfl⟩ := hfun vt hmt
        obtain ⟨idx, hf, htm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
        exact testMem_with_extra htm (by simpa [PArg.gprs] using hsp idx) hdg
          (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) rfl
      · simp at h
    | andVarVar w' x y =>
      simp only [hdef] at h
      split at h
      · rename_i hweq
        obtain rfl : w' = w := Nat.beq_eq.mp hweq
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, vy, hmx, hmy, rfl⟩ := hfun vt hmt
        rcases orElse_eq_some h with h1 | h2
        · obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h1
          obtain ⟨pb, htm, hpg, -, hpb⟩ := tryArg_ok hA (.var hmy) hta
          obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
          exact testMem_with_extra htm
            (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg
            (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb
        · obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨pa, htm, hpg, -, hpa⟩ := tryArg_ok hA (.var hmx) hta
          obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
          simpa [BitVec.and_comm] using testMem_with_extra htm
            (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg
            (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa
      · simp at h
    | _ => simp [hdef] at h

private theorem tryExtSlot_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {co : CmpOp}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vt ci : BitVec w} {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive}
    {clob : FlagMask} (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hmt : ⟨.bits w, vt, t⟩ ∈ G) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryExtSlot T.toIsa hints st co w t ci pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' => T.mach.PDstHolds s' .bool pd (co.evalBits vt ci) ∧
        (∀ cc, (extCmpMemRes T.toIsa co pd c clob).2.2 = some cc →
          T.mach.evalCond s' cc = co.evalBits vt ci) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  have hsp : ∀ idx r, r ∈ (spAddr T.toIsa idx).regs → r ∉ T.frame.scratch := fun idx r hr => by
    simp only [spAddr, AddrArg.regs, List.mem_singleton] at hr
    subst hr; exact T.frameSpec.sp_disj.1
  unfold tryExtSlot at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · rename_i hgd
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨⟨rfl, hm0⟩, hmn⟩, hco⟩, hci⟩, hstd⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        obtain ⟨idx, hf, hcm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
        rw [cmpOp_evalBits_signExtend hm0 hmn hco va ci hci]
        exact cmpMem_with_ext hcm (by simpa [PArg.gprs] using hsp idx) hdg
          (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) rfl
      · simp at h
    | zextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · rename_i hgd
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨⟨rfl, _⟩, hmn⟩, hco⟩, hci⟩, hstd⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        obtain ⟨idx, hf, hcm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
        rw [cmpOp_evalBits_zeroExtend hmn hco va ci hci]
        exact cmpMem_with_ext hcm (by simpa [PArg.gprs] using hsp idx) hdg
          (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) rfl
      · simp at h
    | _ => simp [hdef] at h

private theorem lowerOp_z32_finish {zl : Bool} {G : VCtx} {nv k : Nat} {m : Mem 64}
    {st : SymState T.toIsa} {s s' : T.mach.MData} {σ : List (BitVec 64)} {clob : FlagMask}
    {sig : List Ty} {code : OpCode sig [.bits 32]} {args : Tup (Arg VNat) sig}
    {rd : T.Reg} {rv : BitVec 32} {P : Tup Val [.bits 32] → Prop}
    {flagsPost : Option FlagFact}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk (Tup.zip (rv, ()) (Tup.levels [.bits 32] nv) ++ G) m (nv + 1) st.memDefs)
    (hdef : ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
      0 < 1 ∧ DefOk (Tup.zip (rv, ()) (Tup.levels [.bits 32] nv) ++ G) nv df)
    (hflOk : FlagFactOk T (Tup.zip (rv, ()) (Tup.levels [.bits 32] nv) ++ G) s' flagsPost)
    (hflLt : FlagFactScope (nv + 1) flagsPost)
    (hP : P (rv, ()))
    (hrd_eq : T.mach.getGpr s' rd = rv.setWidth 64)
    (hm : T.mach.mem s' = T.mach.mem s)
    (hfr : T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob)
    (hrda : isAllocGpr T.toIsa hints.saved rd = true)
    (kont : ∀ (rvs : Tup Val [.bits 32]) s'', P rvs →
      Agree T (Tup.zip rvs (Tup.levels [.bits 32] nv) ++ G) (nv + 1)
        { regs := (.var nv, .gprZ rd) :: killRegs T.toIsa (rd :: T.frame.scratch) [] clob st.regs
          slots := st.slots
          defs := match recordDefC T.toIsa.gpr.addrCse st.defs code args with
            | some df => st.defs.insert nv df | none => st.defs
          vecWidths := st.vecWidths
          memDefs := st.memDefs
          zeroExt32 := rd :: killZeroExt (rd :: T.frame.scratch) st.zeroExt32
          flags := flagsPost } s'' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels [.bits 32] nv) ++ G) m (nv + 1) st.memDefs →
      Inv T hints s₀ ra n Rf m s'' σ zl → T.mach.Run host k s'' post) :
    T.mach.Run host k s' post := by
  have hK := hA.kill hfr
  have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
    Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
  have hA1 := hK.push (.bits 32) rv st.vecWidths (fun _ _ => rfl)
    (fun w h => absurd (hnone nv (Nat.le_refl _)) (by simp [h]))
    (fun x hx => hnone x (Nat.le_of_lt hx)) (fun _ a b h => by cases h)
  have hzk : T.mach.getGpr s' rd = ((T.mach.getGpr s' rd).setWidth 32).setWidth 64 := by
    rw [hrd_eq]; exact (setWidth_32_64_val rv).symm
  have hA2 := hA1.consRegZ (sa := .var nv) (r := rd)
    ⟨fun t' v' hm' => by
      cases mem_cons_top hA.ctx_lt hm'
      exact ⟨by decide, by rw [hrd_eq, BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq]⟩,
     fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨by decide, hrd_eq⟩⟩
    (by simp [symArgScopeOk]) hzk
  have hd1 : ∀ y d, Trie.find? (match recordDefC T.toIsa.gpr.addrCse st.defs code args with
      | some df => st.defs.insert nv df | none => st.defs) y = some d →
      DefOk (Tup.zip (rv, ()) (Tup.levels [.bits 32] nv) ++ G) y d ∧ y < nv + 1 := by
    intro y d hy; split at hy
    · rw [Trie.find?_insert] at hy; split at hy
      · cases hy; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_succ_self _⟩
      · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
    · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
  have hdg : ∀ r ∈ [rd], isAllocGpr T.toIsa hints.saved r = true := by simpa using hrda
  exact kont (rv, ()) s' hP ⟨hA2.ctx_lt, hA2.ctx_uniq, hA2.regs, hA2.slots,
    fun y d hy => (hd1 y d hy).1, hA2.vw, hA2.regs_lt, hA2.slots_lt,
    fun y d hy => (hd1 y d hy).2, hA2.vw_lt, hA2.vt, hA2.zeroExt32_ok, hflOk, hflLt⟩
    hM (hI.keep hm (keep_of_frame (gs := [rd]) hfr.1 hdg))

private theorem tryAluSlot_ok {G : VCtx} {nv w k : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {zl : Bool}
    {code : OpCode [.bits w, .bits w] [.bits w]}
    {a₁ b₁ : Arg Val (.bits w)} {a b : Arg VNat (.bits w)} {rd : T.Reg}
    {P : Tup Val [.bits w] → Prop} {c : List T.Directive} {clob : FlagMask} {z32 : Bool}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (ha : ArgRel G (.bits w) a₁ a) (hb : ArgRel G (.bits w) b₁ b)
    (hdg : ∀ r ∈ [rd], r ∉ T.frame.scratch)
    (hwp : code.wp (a₁.val, b₁.val, ()) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : tryAluSlot T.toIsa hints st w code a b rd = some (c, clob, z32))
    (fin : z32 = false → ∀ s',
      (∃ rvs : Tup Val [.bits w], P rvs ∧ TRel (T.mach.PDstHolds s') (.gpr rd, ()) rvs) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post)
    (fin32 : z32 = true → (hw : w = 32) → ∀ s' (rv : BitVec 32), P (hw ▸ (rv, ())) →
      T.mach.getGpr s' rd = rv.setWidth 64 → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have hsp : ∀ idx r, r ∈ (spAddr T.toIsa idx).regs → r ∉ T.frame.scratch := fun idx r hr => by
    simp only [spAddr, AddrArg.regs, List.mem_singleton] at hr
    subst hr; exact T.frameSpec.sp_disj.1
  unfold tryAluSlot at h
  split at h; · simp at h
  rename_i hstd
  replace hstd : isStdBitWidth w = true := by simpa using hstd
  obtain ⟨⟨c', cl'⟩, hs', hmp⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hmp
  obtain ⟨rfl, rfl, rfl⟩ := hmp
  have hrd : rd ∉ T.frame.scratch := hdg rd (List.mem_singleton_self _)
  have stepMem : ∀ (memRhs : Bool) {va vb : BitVec w} {idx : Nat} {pb : _},
      loadVal (T.mach.mem s) (.bits w) ((spAddr T.toIsa idx).eval (T.mach.getGpr s)) = some va →
      (∀ r ∈ pb.gprs, r ∉ T.frame.scratch) →
      T.mach.PArgHolds s (.bits w) pb vb →
      code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P →
      T.gpr.aluMem w code memRhs (spAddr T.toIsa idx) pb rd = some (c', cl') →
      T.mach.Run host k s post := by
    intro memRhs va vb idx pb hlm hpg hpb hwp' hal
    have hrall : ∀ r ∈ (spAddr T.toIsa idx).regs ++ pb.gprs, r ∉ T.frame.scratch :=
      fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)
    by_cases hz : (Nat.beq w 32 && T.toIsa.gpr.zeroUpper32AluMem) = true
    · obtain ⟨rfl, hz0⟩ := by simpa [Bool.and_eq_true, Nat.beq_eq] using hz
      exact T.gprSpec.aluMem_zero32 hz0 hal hrall hrd hlm hpb hwp' hc
        fun s' ⟨⟨rv, hPv, hrd_eq⟩, hms⟩ hfr => fin32 hz rfl s' rv hPv hrd_eq hms hfr
    · have hzf := Bool.eq_false_iff.mpr hz
      exact T.gprSpec.aluMem_spec hal hrall hrd hlm hpb hwp' hc
        fun s' ⟨⟨rv, hPv, hg⟩, hms⟩ hfr => fin hzf s' ⟨(rv, ()), hPv, .cons hg .nil⟩ hms hfr
  rcases orElse_eq_some hs' with h1 | h2
  · cases a with
    | imm _ => simp at h1
    | var x =>
      cases ha with | var hmx =>
      obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨pb, hal, hpg, -, hpb⟩ := tryArg_ok hA hb hta
      obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
      exact stepMem false (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpg hpb hwp hal
  · cases b with
    | imm _ => simp at h2
    | var y =>
      cases hb with | var hmy =>
      obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h2
      obtain ⟨pa, hal, hpg, -, hpa⟩ := tryArg_ok hA ha hta
      obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
      exact stepMem true (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpg hpa hwp hal

private theorem trySlotOp_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {zl : Bool} {sig ts : List Ty}
    {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {z32 : Bool}
    {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargs : TRel (ArgRel G) args₁ args) (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : trySlotOp T.toIsa hints st code args dsts = some (c, clob, z32, flPost, ex))
    (fin : z32 = false → ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (∀ cc, ex = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
          rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b)) →
      FlagFactOk T G s' flPost → FlagFactScope nv flPost →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post)
    (fin32 : z32 = true → ∀ {rd : T.Reg} (ht : ts = [.bits 32]),
      dsts = ht ▸ (.gpr rd, ()) →
      ∀ s' (rv : BitVec 32), P (ht ▸ (rv, ())) →
      T.mach.getGpr s' rd = rv.setWidth 64 →
      FlagFactOk T G s' flPost → FlagFactScope nv flPost →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have hsp : ∀ idx r, r ∈ (spAddr T.toIsa idx).regs → r ∉ T.frame.scratch := fun idx r hr => by
    simp only [spAddr, AddrArg.regs, List.mem_singleton] at hr
    subst hr; exact T.frameSpec.sp_disj.1
  cases code with
  | cmp co ty mty hmty =>
    cases ty with
    | bits w =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
        have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch := fun r hr =>
          hdg r (by simpa [tupDstGprs] using hr)
        have hP : P (co.evalBits a₁.val b₁.val, ()) := by
          simpa [OpCode.wp_cmp, vals, liftCmp] using hwp
        unfold trySlotOp at h; dsimp only at h
        split at h; · simp at h
        rename_i hwn
        have hw : w ≤ 64 := Nat.ble_eq.mp (by simpa using hwn)
        obtain ⟨⟨c', cl', fl', ex'⟩, hs', hmp⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hmp
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmp
        have wrap : ∀ {bval : Bool}, bval = co.evalBits a₁.val b₁.val →
            T.mach.FallsTo T.gpr.condReads host k c' (pd.gprs ++ T.frame.scratch) [] cl' s
              (fun s' => T.mach.PDstHolds s' .bool pd bval ∧
                FlagFactOk T G s' fl' ∧ FlagFactScope nv fl' ∧
                (∀ cc, ex' = some cc → T.mach.evalCond s' cc = bval) ∧
                T.mach.mem s' = T.mach.mem s) post →
            T.mach.Run host k s post := fun heq hft =>
          hft hc fun s' ⟨hd, hfo, hfl, hex, hms⟩ hfr =>
            fin rfl s' ⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons (heq ▸ hd) .nil,
              fun cc hcc => ⟨rfl, _, rfl, heq ▸ hex cc hcc⟩⟩
              hfo hfl hms (by simpa [tupDstGprs] using hfr)
        rcases orElse_eq_some hs' with ht | hrest
        · split at ht
          · rename_i hco
            have hcoEq : (if co == .ne then CmpOp.ne else CmpOp.eq) = co := by
              cases co <;> simp at hco ⊢
            obtain ⟨⟨c0, cl0⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl⟩
            cases a with
            | var t =>
              cases b with
              | imm c0 =>
                dsimp only at ht'
                split at ht'
                · rename_i hc0
                  cases ha with | var hmt => cases hb with | imm =>
                  exact wrap (by rw [hcoEq, beq_iff_eq.mp hc0]; rfl)
                    ((tryTestSlot_ok hA hI hmt hdg1 ht').conseq fun s' ⟨h1, h2, h3⟩ hfr =>
                      ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
                · simp at ht'
              | var _ => simp at ht'
            | imm c0 =>
              cases b with
              | var t =>
                dsimp only at ht'
                split at ht'
                · rename_i hc0
                  cases ha with | imm => cases hb with | var hmt =>
                  refine wrap ?_
                    ((tryTestSlot_ok hA hI hmt hdg1 ht').conseq fun s' ⟨h1, h2, h3⟩ hfr =>
                      ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
                  rw [hcoEq, ← CmpOp.swap_evalBits]
                  cases co <;> simp [CmpOp.swap, beq_iff_eq.mp hc0] at hco ⊢
                · simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some hrest with he | hm
        · cases a with
          | var t =>
            cases b with
            | imm _ =>
              cases ha with | var hmt => cases hb with | imm =>
              obtain ⟨⟨d0, cl0⟩, he', hmap⟩ := Option.map_eq_some_iff.mp he
              simp only [Prod.mk.injEq] at hmap
              rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
              exact wrap rfl ((tryExtSlot_ok hA hI hmt hdg1 he').conseq
                fun s' ⟨h1, h2, h3⟩ hfr => ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
            | var _ => simp at he
          | imm _ =>
            cases b with
            | var t =>
              cases ha with | imm => cases hb with | var hmt =>
              obtain ⟨⟨d0, cl0⟩, he', hmap⟩ := Option.map_eq_some_iff.mp he
              simp only [Prod.mk.injEq] at hmap
              rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
              exact wrap (CmpOp.swap_evalBits co _ _) ((tryExtSlot_ok hA hI hmt hdg1 he').conseq
                fun s' ⟨h1, h2, h3⟩ hfr => ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
            | imm _ => simp at he
        · split at hm; · simp at hm
          rename_i hstd
          replace hstd : isStdBitWidth w = true := by simpa using hstd
          rcases orElse_eq_some hm with h1 | h2
          · cases a with
            | imm _ => simp at h1
            | var x =>
              cases ha with | var hmx =>
              rename_i vx
              obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h1
              obtain ⟨pb, hk, hpg, -, hpb⟩ := tryArg_ok hA hb hta
              obtain ⟨⟨d0, cl0⟩, hcm, hmap⟩ := Option.map_eq_some_iff.mp hk
              obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
              have hsx : SymBits G w vx (.var x) := fun v hv =>
                (hgpr (.bits w) v hv).2.symm.trans (hgpr (.bits w) vx hmx).2
              have hsx_lt : symArgScopeOk nv (.var x) = true := by
                simp [symArgScopeOk, Nat.ble_eq]; exact hA.ctx_lt _ hmx
              cases hsb : toSymArg T.toIsa (.bits w) b with
              | none =>
                rw [hsb] at hmap; dsimp only at hmap
                simp only [Prod.mk.injEq] at hmap; rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
                exact wrap rfl ((T.gprSpec.cmpMem_spec hcm
                  (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                  (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb).conseq
                  fun s' ⟨hd, hm'⟩ hfr =>
                    ⟨hd, hA.flags_ok.kill hfr, hA.flags_lt.kill, (fun _ h => nomatch h), hm'⟩)
              | some sb =>
                rw [hsb] at hmap; dsimp only at hmap
                have hsb_ok := tryArg_bits_det hA hw hb hta hsb
                have hsb_lt := symArgScopeOk_of_argRel hA.ctx_lt hb hsb
                have hcm_eq : d0 = c' ∧ cl0 = cl' := by
                  unfold cmpMemRes at hmap; split at hmap <;> simp only [Prod.mk.injEq] at hmap <;>
                    exact ⟨hmap.1, hmap.2.1⟩
                rcases hcm_eq with ⟨rfl, rfl⟩
                have hsb_at := symValAt_of_toSymArg (T := T) hw hb hsb
                exact wrap rfl (cmpMemRes_with_flags hw hA.flags_ok hA.flags_lt hsx hsb_ok hmx
                  hsb_at hsx_lt hsb_lt hmap hcm
                  (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r))
                  hdg1 (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb)
          · cases b with
            | imm _ => simp at h2
            | var y =>
              cases hb with | var hmy =>
              rename_i vy
              obtain ⟨idx, hf, hta⟩ := Option.bind_eq_some_iff.mp h2
              obtain ⟨pa, hk, hpg, -, hpa⟩ := tryArg_ok hA ha hta
              obtain ⟨⟨d0, cl0⟩, hcm, hmap⟩ := Option.map_eq_some_iff.mp hk
              obtain ⟨hlt, w64, hσ, hgpr⟩ := findSlotGpr_ok hA hf
              have hsy : SymBits G w vy (.var y) := fun v hv =>
                (hgpr (.bits w) v hv).2.symm.trans (hgpr (.bits w) vy hmy).2
              have hsy_lt : symArgScopeOk nv (.var y) = true := by
                simp [symArgScopeOk, Nat.ble_eq]; exact hA.ctx_lt _ hmy
              cases hsa : toSymArg T.toIsa (.bits w) a with
              | none =>
                rw [hsa] at hmap; dsimp only at hmap
                simp only [Prod.mk.injEq] at hmap; rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
                exact wrap (CmpOp.swap_evalBits co _ _) ((T.gprSpec.cmpMem_spec hcm
                  (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                  (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa).conseq
                  fun s' ⟨hd, hm'⟩ hfr =>
                    ⟨hd, hA.flags_ok.kill hfr, hA.flags_lt.kill, (fun _ h => nomatch h), hm'⟩)
              | some sa =>
                rw [hsa] at hmap; dsimp only at hmap
                have hsa_ok := tryArg_bits_det hA hw ha hta hsa
                have hsa_lt := symArgScopeOk_of_argRel hA.ctx_lt ha hsa
                have hcm_eq : d0 = c' ∧ cl0 = cl' := by
                  unfold cmpMemRes at hmap; split at hmap <;> simp only [Prod.mk.injEq] at hmap <;>
                    exact ⟨hmap.1, hmap.2.1⟩
                rcases hcm_eq with ⟨rfl, rfl⟩
                have hsa_at := symValAt_of_toSymArg (T := T) hw ha hsa
                exact wrap (CmpOp.swap_evalBits co _ _)
                  (cmpMemRes_with_flags hw hA.flags_ok hA.flags_lt hsy hsa_ok hmy hsa_at hsy_lt
                    hsa_lt hmap hcm
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa)
      | _ => simp [trySlotOp] at h
    | _ => simp [trySlotOp] at h
  | add ty | sub ty | mul ty | and ty | or ty | xor ty =>
    cases ty with
    | float _ | bool | pair _ _ => simp [trySlotOp] at h
    | bits w =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      rcases dsts with ⟨d0, ⟨⟩⟩
      cases d0 with
      | vec _ => simp [trySlotOp] at h
      | gpr rd =>
        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
        unfold trySlotOp at h; dsimp only at h
        obtain ⟨⟨c0, cl0, z0⟩, halu, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
        exact tryAluSlot_ok hA hI ha hb (by simpa [tupDstGprs] using hdg)
          (by simpa [vals, Arg.val] using hwp) hc halu
          (fun hzf s' ⟨rvs, hPrvs, hdl⟩ hms hfr =>
            fin hzf s' ⟨rvs, hPrvs, hdl, fun _ h => nomatch h⟩
              (hA.flags_ok.kill hfr) hA.flags_lt.kill hms (by simpa [tupDstGprs] using hfr))
          (fun hz h32 s' rv hPv hrd hms hfr => by
            subst h32
            exact fin32 hz rfl rfl s' rv hPv hrd (hA.flags_ok.kill hfr) hA.flags_lt.kill hms hfr)
  | _ => simp [trySlotOp] at h


private theorem cmpOpFlags_cmp (I : Isa) (st : SymState I) (co : CmpOp) (w nv : Nat)
    (hpf : Ty.bool = (Ty.bits w).mask)
    (a b : Arg VNat (Ty.bits w)) (pa pb : PArg I.Reg I.VReg I.Cond (Ty.bits w))
    (pd : PDst I.Reg I.VReg I.Cond Ty.bool) (cl : FlagMask) :
    cmpOpFlags? I st (.cmp co (.bits w) .bool hpf) (a, b, ()) (pa, pb, ()) (pd, ()) nv cl =
    (if Nat.ble w 64 then
       match I.gpr.cmpFlagsOut? co w pa pb pd, toSymArg I (.bits w) a, toSymArg I (.bits w) b with
       | some lf, some sa, some sb =>
         some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
       | _, _, _ => killFlags I cl st.flags
     else killFlags I cl st.flags,
     match pd with
     | .gpr _ =>
       if Nat.ble w 64 then
         (I.gpr.cmpFlagsOut? co w pa pb pd).bind fun lf =>
           I.gpr.condOfCmp? (if lf then co else co.swap)
       else none
     | _ => none) := rfl

private theorem gprOp_with_flags {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {pas : Tup (PArg T.Reg T.VReg T.Cond) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ)
    (hargs : TRel (ArgRel G) args₁ args)
    (hpick : pickPArgs T.toIsa st (tupDstFlags dsts) args (fun pas' =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas').isEmpty then
        ((T.gpr.op code pas' dsts vh).map fun p =>
          let flx := cmpOpFlags? T.toIsa st code args pas' dsts nv p.2
          (p.1, p.2, false, opProducesZ32 T.toIsa code pas' dsts, flx.1, flx.2)) <|>
        ((T.vec.vop code pas' dsts vh).map fun p =>
          (p.1, p.2, true, false, killFlags T.toIsa p.2 st.flags, none))
      else (T.vec.vop code pas' dsts vh).map fun p =>
        (p.1, p.2, true, false, killFlags T.toIsa p.2 st.flags, none)) =
      some (c, clob, false, false,
        (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1,
        (cmpOpFlags? T.toIsa st code args pas dsts nv clob).2))
    (hop' : T.gpr.op code pas dsts vh = some (c, clob))
    (hpg : ∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch)
    (hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hph : TRel (T.mach.PArgHolds s) pas (vals args₁))
    (hwp : code.wp (vals args₁) P)
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (fin : ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (∀ cc, (cmpOpFlags? T.toIsa st code args pas dsts nv clob).2 = some cc →
          ∃ (ht : ts = [.bool]) (b : Bool), rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b) ∧
        FlagFactOk T (Tup.zip rvs (Tup.levels ts nv) ++ G) s'
          (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1 ∧
        FlagFactScope (nv + ts.length)
          (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have htr : ∀ (rvs : Tup Val ts) {s'} {fl : Option FlagFact},
      FlagFactOk T G s' fl → FlagFactScope nv fl →
      FlagFactOk T (Tup.zip rvs (Tup.levels ts nv) ++ G) s' fl ∧
      FlagFactScope (nv + ts.length) fl := by
    intro rvs s' fl hfo hfl
    exact ⟨hfo.tr (fun _ hp => List.mem_append_right _ hp)
      (fun p hp => (zip_levels_mem hp).imp id (·.1)) hfl,
      hfl.mono (Nat.le_add_right _ _)⟩
  have fallback : (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1 =
        killFlags T.toIsa clob st.flags →
      (cmpOpFlags? T.toIsa st code args pas dsts nv clob).2 = none →
      T.mach.Run host k s post := by
    intro hfl1 hfl2
    exact T.gprSpec.op_spec hop' hpg hdg' hph hwp hc fun s' ⟨⟨rvs, hP, hdl⟩, hm⟩ hfr =>
      fin s' ⟨rvs, hP, hdl, (fun _ h => by rw [hfl2] at h; cases h),
        (by rw [hfl1]; exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1),
        (by rw [hfl1]; exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2)⟩ hm hfr
  cases ts with
  | nil => exact fallback rfl rfl
  | cons t0 ts0 =>
    cases ts0 with
    | cons _ _ => cases t0 <;> exact fallback rfl rfl
    | nil =>
      cases t0 with
      | float _ | pair _ _ => exact fallback rfl rfl
      | bits w =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        have hcmpEq : cmpOpFlags? T.toIsa st code args pas (pd, ()) nv clob =
            (if Nat.ble w 64 && !(clob == FlagMask.none) then
              match T.gpr.aluZeroOut? w code pd with
              | some eqNe => some (.cmp w (.var nv) (.immBits w 0#64) eqNe)
              | none => killFlags T.toIsa clob st.flags
            else killFlags T.toIsa clob st.flags, none) := by
          cases code <;> rfl
        by_cases hgd : (Nat.ble w 64 && !(clob == FlagMask.none)) = true
        · obtain ⟨hw64, hcl⟩ : w ≤ 64 ∧ clob ≠ FlagMask.none := by
            simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq] at hgd
            exact ⟨hgd.1, fun h => by subst h; simp at hgd⟩
          cases halu : T.gpr.aluZeroOut? w code pd with
          | none =>
            exact fallback (by simp [hcmpEq, hgd, halu]) (by simp [hcmpEq])
          | some eqNe =>
            refine T.gprSpec.op_aluZero_spec halu hcl hop' hpg
              (fun r hr => hdg' r (by simpa [tupDstGprs] using hr)) hph hwp hc
              fun s' ⟨⟨rv, hP, hpd, _, hflCmp⟩, hm⟩ hfr => ?_
            have hfok : FlagFactOk T (Tup.zip (rv, ()) (Tup.levels [.bits w] nv) ++ G) s'
                (some (.cmp w (.var nv) (.immBits w 0#64) eqNe)) := by
              refine ⟨hw64, rv, 0#w, List.mem_cons_self .., fun v hv => ?_, ⟨rfl, by simp⟩,
                ⟨rfl, by simp⟩, hflCmp⟩
              cases mem_cons_top hA.ctx_lt hv; rfl
            have hfsc : FlagFactScope (nv + [Ty.bits w].length)
                (some (.cmp w (.var nv) (.immBits w 0#64) eqNe)) :=
              ⟨by simp [symArgScopeOk], rfl⟩
            exact fin s' ⟨(rv, ()), hP, .cons hpd .nil, (fun _ h => by simp [hcmpEq] at h),
              by simpa [hcmpEq, hgd, halu] using hfok,
              by simpa [hcmpEq, hgd, halu] using hfsc⟩ hm (by simpa [tupDstGprs] using hfr)
        · have hgdf : (Nat.ble w 64 && !(clob == FlagMask.none)) = false :=
            Bool.eq_false_iff.mpr hgd
          exact fallback (by simp [hcmpEq, hgdf]) (by simp [hcmpEq])
      | bool =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        have boolFlagArm :
            ((cmpOpFlags? T.toIsa st code args pas (pd, ()) nv clob).1 =
              killFlags T.toIsa clob st.flags) →
            ((cmpOpFlags? T.toIsa st code args pas (pd, ()) nv clob).2 =
              match pd with | .gpr rd => T.gpr.boolFlagOut? code pas (.gpr rd) | _ => none) →
            T.mach.Run host k s post := by
          intro hfl1 hfl2
          cases pd with
          | flag _ | vec _ => exact fallback hfl1 hfl2
          | gpr rd =>
            dsimp only at hfl2
            cases hbf : T.gpr.boolFlagOut? code pas (.gpr rd) with
            | none => exact fallback hfl1 (hfl2.trans hbf)
            | some cc =>
              refine T.gprSpec.op_boolFlag_spec hbf hop' hpg hdg' hph hwp hc
                fun s' ⟨⟨b, hP, hpd, heval⟩, hm⟩ hfr => ?_
              exact fin s' ⟨(b, ()), hP, .cons hpd .nil,
                (fun cc' hcc' => by
                  rw [hfl2, hbf, Option.some.injEq] at hcc'; subst hcc'
                  exact ⟨rfl, b, rfl, heval⟩),
                by rw [hfl1]; exact (htr (b, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
                by rw [hfl1]; exact (htr (b, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩
                hm hfr
        cases code
        case cmp co ty hmty =>
          cases ty with
          | float _ | bool | pair _ _ =>
            cases pd <;> exact boolFlagArm rfl rfl
          | bits w =>
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
            rcases pas with ⟨pa, pb, ⟨⟩⟩
            cases hargs with | cons ha hb => cases hb with | cons hb _ =>
            cases hph with | cons hpa hpb => cases hpb with | cons hpb _ =>
            have hP : P (co.evalBits a₁.val b₁.val, ()) := by
              simpa [OpCode.wp_cmp, vals, liftCmp] using hwp
            have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch := fun r hr =>
              hdg' r (by simpa [tupDstGprs] using hr)
            have hpg1 : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch := fun r hr =>
              hpg r (by
                rcases List.mem_append.mp hr with hr | hr
                · exact List.mem_append_left _ hr
                · exact List.mem_append_right _ (by simpa [tupArgGprs] using hr))
            by_cases hw : w ≤ 64
            · have hwb : Nat.ble w 64 = true := Nat.ble_eq.mpr hw
              cases hcmo : T.gpr.cmpFlagsOut? co w pa pb pd with
              | none =>
                exact fallback (by rw [cmpOpFlags_cmp]; simp [hwb, hcmo])
                  (by rw [cmpOpFlags_cmp]; cases pd <;> simp [hwb, hcmo])
              | some lf =>
                refine T.gprSpec.op_cmpFlags_spec hcmo hop' hpg1 hdg1 hpa hpb hc
                  fun s' ⟨hd, hflCmp, hm⟩ hfr => ?_
                have exOk : ∀ cc,
                    (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                      (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).2 = some cc →
                    T.mach.evalCond s' cc = co.evalBits a₁.val b₁.val := by
                  intro cc hcc
                  rw [cmpOpFlags_cmp] at hcc
                  cases pd with
                  | flag _ | vec _ => cases hcc
                  | gpr _ =>
                    simp [hwb, hcmo] at hcc
                    have hf := hflCmp (if lf then co else co.swap) cc (by simp) hcc
                    rw [hf]; cases lf <;> simp [CmpOp.swap_evalBits]
                cases hsa : toSymArg T.toIsa (.bits w) a with
                | none =>
                  refine fin s' ⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons hd .nil,
                    fun cc hcc => ⟨rfl, _, rfl, exOk cc hcc⟩,
                    ?_, ?_⟩ hm (by simpa [tupDstGprs] using hfr)
                  · rw [show (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                        (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).1 =
                        killFlags T.toIsa clob st.flags by rw [cmpOpFlags_cmp]; simp [hwb, hcmo,
                          hsa]]
                    exact (htr _ (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                  · rw [show (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                        (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).1 =
                        killFlags T.toIsa clob st.flags by rw [cmpOpFlags_cmp]; simp [hwb, hcmo,
                          hsa]]
                    exact (htr (co.evalBits a₁.val b₁.val,
                      ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                | some sa =>
                  cases hsb : toSymArg T.toIsa (.bits w) b with
                  | none =>
                    refine fin s' ⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons hd .nil,
                      fun cc hcc => ⟨rfl, _, rfl, exOk cc hcc⟩,
                      ?_, ?_⟩ hm (by simpa [tupDstGprs] using hfr)
                    · rw [show (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                          (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).1 =
                          killFlags T.toIsa clob st.flags by
                        rw [cmpOpFlags_cmp]; simp [hwb, hcmo, hsa, hsb]]
                      exact (htr _ (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                    · rw [show (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                          (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).1 =
                          killFlags T.toIsa clob st.flags by
                        rw [cmpOpFlags_cmp]; simp [hwb, hcmo, hsa, hsb]]
                      exact (htr (co.evalBits a₁.val b₁.val,
                        ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                  | some sb =>
                    simp only [pickPArgs] at hpick
                    have hsa_ok := tryArg_bits_det hA hw ha hpick hsa
                    obtain ⟨pa0, hpick_b, -, -, -⟩ := tryArg_ok hA ha hpick
                    have hsb_ok := tryArg_bits_det hA hw hb hpick_b hsb
                    have hsa_lt := symArgScopeOk_of_argRel hA.ctx_lt ha hsa
                    have hsb_lt := symArgScopeOk_of_argRel hA.ctx_lt hb hsb
                    have hsa_at := symValAt_of_toSymArg (T := T) hw ha hsa
                    have hsb_at := symValAt_of_toSymArg (T := T) hw hb hsb
                    have hflG : FlagFactOk T G s'
                        (some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)) := by
                      refine ⟨hw, if lf then a₁.val else b₁.val, if lf then b₁.val else a₁.val,
                        ?_, ?_, ?_, ?_, hflCmp⟩
                      · cases lf <;> simp [hsa_at, hsb_at]
                      · cases lf <;> simp [hsa_ok, hsb_ok]
                      · cases lf <;> simp [hsa_at, hsb_at]
                      · cases lf <;> simp [hsa_ok, hsb_ok]
                    have hflSc : FlagFactScope nv
                        (some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)) := by
                      refine ⟨?_, ?_⟩ <;> cases lf <;> simp [hsa_lt, hsb_lt]
                    have hflEq : (cmpOpFlags? T.toIsa st (.cmp co (.bits w) .bool hmty)
                          (a, b, ()) (pa, pb, ()) (pd, ()) nv clob).1 =
                        some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false) := by
                      rw [cmpOpFlags_cmp]; simp [hwb, hcmo, hsa, hsb]
                    refine fin s' ⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons hd .nil,
                      fun cc hcc => ⟨rfl, _, rfl, exOk cc hcc⟩, ?_, ?_⟩ hm
                      (by simpa [tupDstGprs] using hfr)
                    · rw [hflEq]; exact (htr _ hflG hflSc).1
                    · rw [hflEq]; exact (htr (co.evalBits a₁.val b₁.val, ()) hflG hflSc).2
            · have hwb : Nat.ble w 64 = false :=
                Bool.eq_false_iff.mpr (by simpa [Nat.ble_eq] using hw)
              exact fallback (by rw [cmpOpFlags_cmp]; simp [hwb])
                (by rw [cmpOpFlags_cmp]; cases pd <;> simp [hwb])
        all_goals
          cases pd <;> exact boolFlagArm rfl rfl

private theorem lowerOpBody_ok {zl : Bool}
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {ts : List Ty} {op₁ : Op Val ts} {op : Op VNat ts}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    (hop : OpRel G op₁ op) (hdst : resolveDsts T.toIsa hints ts nv = some dsts)
    (hl : lowerOpBody T.toIsa hints nv ip st op dsts = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    {P : Tup Val ts → Prop} (hwp : op₁.wp P)
    (kont : ∀ (rvs : Tup Val ts) s', P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st'.memDefs →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  cases hop with
  | mk code hargs =>
  rename_i sig args₁ args
  have hMgrow : ∀ rvs : Tup Val ts,
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs := fun rvs =>
    hM.grow (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun _ h => List.mem_append_right _ h)
  unfold lowerOpBody at hl
  obtain ⟨hdg, hdv, hdo⟩ := resolveDsts_spec hdst
  have hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch :=
    fun r hr => not_scratch_of_isAllocGpr hsv (hdg r hr)
  have hdv' : ∀ v ∈ tupDstVecs dsts, v ∉ T.vec.vecScratch :=
    fun v hv => not_vecScratch_of_isAllocVec (hdv v hv)
  let G' : Tup Val ts → VCtx := fun rvs => Tup.zip rvs (Tup.levels ts nv) ++ G
  have hwp' : code.wp (vals args₁) (fun rvs => P rvs ∧
      ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) := by
    cases hd : recordDefC T.toIsa.gpr.addrCse st.defs code args with
    | none => exact OpCode.wp_mono code _ (fun r hp => ⟨hp, by simp⟩) hwp
    | some df =>
      exact OpCode.wp_mono code _ (fun r hp => ⟨hp.1, fun df' he => by cases he; exact hp.2⟩)
        (wp_recordDefC hA.defs hargs hA.ctx_lt hwp hd)
  have hGtop : ∀ {rvs : Tup Val ts} t v x, ⟨t, v, x⟩ ∈ G' rvs → nv ≤ x →
      ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx) := fun {rvs} t v x hm hx => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hm
    · exact absurd hx (Nat.not_le_of_lt (hA.ctx_lt _ hm))
  split at hl
  · -- elided `zext m n` of a `.gprZ rd` source: no code, every register fact is kept
    rename_i hel
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    cases code with
    | zext m0 n0 =>
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a with
      | imm _ => simp [elideZext32?] at hel
      | var x =>
        cases d0 with
        | vec _ => simp [elideZext32?] at hel
        | gpr rd =>
          simp only [elideZext32?, Bool.and_eq_true, Nat.ble_eq, Bool.or_eq_true] at hel
          obtain ⟨⟨hn, _⟩, hsrc⟩ := hel
          rcases args₁ with ⟨a₁, ⟨⟩⟩
          cases hargs with
          | cons ha₁ _ =>
            cases ha₁ with
            | var hmG =>
              rename_i vx
              simp only [OpCode.wp, vals, Arg.val] at hwp'
              obtain ⟨hmn, hP, hdef⟩ := hwp'
              have hw : T.mach.getGpr s rd = (vx.setWidth n0).setWidth 64 := by
                cases hsrc with
                | inl hgprz =>
                  simp only [hasVarGprZ, List.any_eq_true, Bool.and_eq_true] at hgprz
                  obtain ⟨⟨sa', rl'⟩, hmem, hsa⟩ := hgprz
                  have heq1 := symArgEq_eq hsa.1; have heq2 := regLocEq_eq hsa.2
                  subst heq1; subst heq2
                  have hz := (hA.regs _ hmem).2 _ vx hmG
                  rw [hz.2, setWidth_widen_64 vx hmn]
                | inr hgpr =>
                  simp only [Nat.beq_eq] at hgpr
                  obtain ⟨⟨hm32, hzer⟩, hhas⟩ := hgpr
                  subst hm32
                  simp only [hasVarGpr, List.any_eq_true, Bool.and_eq_true] at hhas
                  obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := hhas
                  obtain rfl := symArgEq_iff.mp he1
                  have gsym : GprSym G (T.mach.getGpr s rd) (SymArg.var x) := by
                    have h0 := hA.regs _ hmem
                    cases rl' with
                    | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0
                    | gprZ r' =>
                      simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0.1
                    | _ => simp [regLocMatchesGpr] at he2
                  have hgs : GprHolds (T.mach.getGpr s rd) (.bits 32) vx := gsym (.bits 32) vx hmG
                  have hzk := hA.zeroExt32_ok rd (List.contains_iff_mem.mp hzer)
                  rw [hzk, hgs.2, ← setWidth_widen_64 vx hmn]
              have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
                Option.eq_none_iff_forall_ne_some.mpr fun w h =>
                  absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
              have hA1 := hA.push (.bits n0) (vx.setWidth n0) st.vecWidths (fun _ _ => rfl)
                (fun w h => absurd (hnone nv (Nat.le_refl _)) (by simp [h]))
                (fun x hx => hnone x (Nat.le_of_lt hx)) (fun _ a b h => by cases h)
              have hA2 := hA1.consReg (sa := .var nv) (rl := .gprZ rd)
                ⟨fun t' v' hm' => by
                  cases mem_cons_top hA.ctx_lt hm'
                  exact ⟨hn, by rw [hw, BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]⟩,
                  fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hw⟩⟩
                (by simp [symArgScopeOk])
              have hd1 : ∀ y d, Trie.find? (match recordDef st.defs (.zext m0 n0) (.var x, ()) with
                  | some df => st.defs.insert nv df | none => st.defs) y = some d →
                  DefOk (G' (vx.setWidth n0, ())) y d ∧ y < nv + 1 := by
                intro y d hy; split at hy
                · rw [Trie.find?_insert] at hy; split at hy
                  · cases hy; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_succ_self _⟩
                  · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
                · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
              refine kont (vx.setWidth n0, ()) s hP ?_ (hMgrow _) hI
              exact { hA2 with
                defs := fun y d hy => (hd1 y d hy).1
                defs_lt := fun y d hy => (hd1 y d hy).2 }
    | _ => simp [elideZext32?] at hel
  split at hl
  · -- elided `trunc m n` of a `.var x` already in `rd`
    rename_i hel
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    cases code with
    | trunc m0 n0 =>
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a with
      | imm _ => simp [elideTrunc?] at hel
      | var x =>
        cases d0 with
        | vec _ => simp [elideTrunc?] at hel
        | gpr rd =>
          simp only [elideTrunc?, Bool.and_eq_true, Nat.ble_eq] at hel
          obtain ⟨⟨⟨hnm, hn⟩, hhas⟩, -⟩ := hel
          rcases args₁ with ⟨a₁, ⟨⟩⟩
          cases hargs with
          | cons ha₁ _ =>
            cases ha₁ with
            | var hmG =>
              rename_i vx
              simp only [OpCode.wp, vals, Arg.val] at hwp'
              obtain ⟨-, hP, hdef⟩ := hwp'
              simp only [hasVarGpr, List.any_eq_true, Bool.and_eq_true] at hhas
              obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := hhas
              obtain rfl := symArgEq_iff.mp he1
              have gsym : GprSym G (T.mach.getGpr s rd) (SymArg.var x) := by
                have h0 := hA.regs _ hmem
                cases rl' with
                | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0
                | gprZ r' =>
                  simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0.1
                | _ => simp [regLocMatchesGpr] at he2
              have hgs : GprHolds (T.mach.getGpr s rd) (.bits m0) vx := gsym (.bits m0) vx hmG
              have hw : (T.mach.getGpr s rd).setWidth n0 = vx.setWidth n0 := by
                rw [← BitVec.setWidth_setWidth_of_le (T.mach.getGpr s rd) hnm, hgs.2]
              have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
                Option.eq_none_iff_forall_ne_some.mpr fun w h =>
                  absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
              have hA1 := hA.push (.bits n0) (vx.setWidth n0) st.vecWidths (fun _ _ => rfl)
                (fun w h => absurd (hnone nv (Nat.le_refl _)) (by simp [h]))
                (fun x hx => hnone x (Nat.le_of_lt hx)) (fun _ a b h => by cases h)
              have hA2 := hA1.consReg (sa := .var nv) (rl := .gpr rd)
                (fun t' v' hm' => by
                  cases mem_cons_top hA.ctx_lt hm'
                  exact ⟨hn, hw⟩)
                (by simp [symArgScopeOk])
              have hd1 : ∀ y d, Trie.find? (match recordDef st.defs (.trunc m0 n0) (.var x, ()) with
                  | some df => st.defs.insert nv df | none => st.defs) y = some d →
                  DefOk (G' (vx.setWidth n0, ())) y d ∧ y < nv + 1 := by
                intro y d hy; split at hy
                · rw [Trie.find?_insert] at hy; split at hy
                  · cases hy; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_succ_self _⟩
                  · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
                · exact ⟨hA2.defs y d hy, hA2.defs_lt y d hy⟩
              refine kont (vx.setWidth n0, ()) s hP ?_ (hMgrow _) hI
              exact { hA2 with
                defs := fun y d hy => (hd1 y d hy).1
                defs_lt := fun y d hy => (hd1 y d hy).2 }
    | _ => simp [elideTrunc?] at hel
  obtain ⟨op₁N, hopN, hwpN_fn⟩ := normCmpOp_ok (T := T) hargs dsts
  have hwpN := hwpN_fn _ hwp'
  try dsimp only at hl
  generalize hOpN : normCmpOp (I := T.toIsa) { code := code, args := args } dsts = opN at hl
  rw [hOpN] at hopN
  cases hopN with
  | mk codeN hargsN =>
  rename_i sigN args₁N argsN
  obtain ⟨⟨c', clob, isVec, z32, flagsPost, extraBool?⟩, hpick, heq⟩ :=
    Option.map_eq_some_iff.mp hl
  cases heq
  have fin : z32 = false → ∀ s' (vC : List T.VReg),
      (∃ rvs, (P rvs ∧ ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (∀ cc, extraBool? = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
          rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b) ∧
        FlagFactOk T (G' rvs) s' flagsPost ∧ FlagFactScope (nv + ts.length) flagsPost) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) vC clob →
      vC = (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) →
      T.mach.Run host (k + c'.length) s' post := by
    rintro rfl s' vC ⟨rvs, ⟨hP, hdef⟩, hdh, hex, hflOk, hflLt⟩ hm hfr rfl
    have hK := hA.kill hfr
    obtain ⟨hb1, hb2, hb3, hb4⟩ := bindDsts_ok dsts rvs nv
      (killRegs T.toIsa (tupDstGprs dsts ++ T.frame.scratch)
        (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) clob st.regs)
      st.vecWidths hdh hdo (hGtop (rvs := rvs))
    have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
      Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
    have hA1 := hK.extend (G' := G' rvs) (nv' := nv + ts.length) (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun p hp => (zip_levels_mem hp).elim (fun h => Nat.lt_of_lt_of_le (hA.ctx_lt p h)
        (Nat.le_add_right _ _)) (·.2))
      (fun p hp => List.mem_append_right _ hp)
      (ctx_uniq_zip hA.ctx_lt hA.ctx_uniq ts rvs nv (Nat.le_refl _)) hb2
      (fun x w hx hle => (hb3 x w hx hle).resolve_left (by simp [hnone x hle]))
      (fun p hp hle hn => hb4 p.1 p.2.1 p.2.2 hp hle hn)
    have hr1 := fun p hp => (hb1 p hp).elim (fun hp => ⟨hA1.regs p hp, hA1.regs_lt p hp⟩) id
    have hd1 : ∀ x d, Trie.find? (match recordDefC T.toIsa.gpr.addrCse st.defs code args with
        | some df => st.defs.insert nv df | none => st.defs) x = some d →
        DefOk (G' rvs) x d ∧ x < nv + ts.length := by
      intro x d hx; split at hx
      · rw [Trie.find?_insert] at hx; split at hx
        · cases hx; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_add_of_pos_right (hdef _ ‹_›).1⟩
        · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
      · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
    refine kont rvs s' hP ⟨hA1.ctx_lt, hA1.ctx_uniq, ?_, hA1.slots,
      fun x d hx => (hd1 x d hx).1, hA1.vw, ?_,
      hA1.slots_lt, fun x d hx => (hd1 x d hx).2, hA1.vw_lt, hA1.vt, hA1.zeroExt32_ok,
      hflOk, hflLt⟩ (hMgrow rvs) (hI.keep hm (keep_of_frame hfr.1 hdg))
    · intro p hp
      dsimp only at hp
      cases hex_eq : extraBool? with
      | none =>
        rw [hex_eq] at hp
        cases ts with
        | nil => exact (hr1 p hp).1
        | cons t0 ts0 =>
          cases ts0 with
          | cons _ _ => cases t0 <;> exact (hr1 p hp).1
          | nil => cases t0 <;> exact (hr1 p hp).1
      | some cc =>
        rw [hex_eq] at hp
        cases ts with
        | nil => exact (hr1 p hp).1
        | cons t0 ts0 =>
          cases ts0 with
          | cons _ _ => cases t0 <;> exact (hr1 p hp).1
          | nil =>
            cases t0 with
            | bits _ | float _ | pair _ _ => exact (hr1 p hp).1
            | bool =>
              rcases List.mem_cons.mp hp with rfl | hp'
              · obtain ⟨ht, b, rfl, heval⟩ := hex cc hex_eq
                intro t' v' hm'
                have htp := hGtop t' v' nv hm' (Nat.le_refl _)
                simp only [Tup.zip, Tup.levels, List.mem_singleton] at htp
                cases htp; exact heval.symm
              · exact (hr1 p hp').1
    · intro p hp
      dsimp only at hp
      cases hex_eq : extraBool? with
      | none =>
        rw [hex_eq] at hp
        cases ts with
        | nil => exact (hr1 p hp).2
        | cons t0 ts0 =>
          cases ts0 with
          | cons _ _ => cases t0 <;> exact (hr1 p hp).2
          | nil => cases t0 <;> exact (hr1 p hp).2
      | some cc =>
        rw [hex_eq] at hp
        cases ts with
        | nil => exact (hr1 p hp).2
        | cons t0 ts0 =>
          cases ts0 with
          | cons _ _ => cases t0 <;> exact (hr1 p hp).2
          | nil =>
            cases t0 with
            | bits _ | float _ | pair _ _ => exact (hr1 p hp).2
            | bool =>
              rcases List.mem_cons.mp hp with rfl | hp'
              · simp [symArgScopeOk]
              · exact (hr1 p hp').2
  have hflTr : ∀ rvs {s'} {fl : Option FlagFact},
      FlagFactOk T G s' fl → FlagFactScope nv fl →
      FlagFactOk T (G' rvs) s' fl ∧ FlagFactScope (nv + ts.length) fl := by
    intro rvs s' fl hfo hfl
    exact ⟨hfo.tr (fun _ hp => List.mem_append_right _ hp)
      (fun p hp => (zip_levels_mem hp).imp id (·.1)) hfl,
      hfl.mono (Nat.le_add_right _ _)⟩
  rcases orElse_eq_some hpick with hreuse | hpick
  · obtain ⟨⟨c'', cl, fl, ex⟩, hr, he⟩ := Option.map_eq_some_iff.mp hreuse
    cases he
    rcases orElse_eq_some hr with hr1 | hr2
    · refine tryReuseFlagCmp_ok hA hargs hdg' hwp' hr1 hc fun s' ⟨⟨rvs, hP, hdh, hex⟩, hfo, hfl,
        hm⟩ hfr =>
        fin rfl s' [] ⟨rvs, hP, hdh, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩ hm hfr rfl
    · refine tryReuseFlagCmp_ok hA hargsN hdg' hwpN hr2 hc fun s' ⟨⟨rvs, hP, hdh, hex⟩, hfo, hfl,
        hm⟩ hfr =>
        fin rfl s' [] ⟨rvs, hP, hdh, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hfuse | hpick
  · obtain ⟨⟨c'', cl, fl, ex⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse
    cases he
    refine tryFuseCmp_ok hA hI hM hargsN hdg' hwpN hfc hc fun s' ⟨⟨rvs, hP, hdh, hex⟩, hfo, hfl,
      hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hlx | hpick
  · obtain ⟨⟨c'', cl⟩, hls, he⟩ := Option.map_eq_some_iff.mp hlx
    cases he
    refine tryLoadSext_ok hA hI hM hargsN hdg' hwpN hls hc fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hlea | hpick
  · obtain ⟨⟨c'', cl, z''⟩, htl, he⟩ := Option.map_eq_some_iff.mp hlea
    cases he
    refine tryLeaArith_ok hA hI hargsN hdg' hwpN hc htl
      (fun hz s' ⟨rvs, hP, hdh⟩ hm hfr => fin hz s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true :=
      hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
      hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]
    dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
    exact hA''
  rcases orElse_eq_some hpick with hzero | hpick
  · obtain ⟨⟨c'', cl, z''⟩, htz, he⟩ := Option.map_eq_some_iff.mp hzero
    cases he
    refine tryMoviZero_ok hargsN hwpN hc htz
      (fun hz s' ⟨rvs, hP, hdh⟩ hm hfr => fin hz s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true :=
      hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
      hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]
    dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
    exact hA''
  rcases orElse_eq_some hpick with hpick | hpick
  · obtain ⟨pas, hk, hpg, hpv, hph⟩ := pickPArgs_ok hA hargsN hpick
    split at hk <;> (try rcases orElse_eq_some hk with hk | hk) <;>
      obtain ⟨⟨c'', cl⟩, hop', he⟩ := Option.map_eq_some_iff.mp hk <;> cases he
    · by_cases hz : opProducesZ32 T.toIsa codeN pas dsts = true
      · have hz_eq := hz
        cases ts with
        | nil => simp [opProducesZ32] at hz
        | cons t0 ts0 =>
          cases ts0 with
          | cons _ _ => simp [opProducesZ32] at hz
          | nil =>
            cases t0 with
            | bool | float _ | pair _ _ => simp [opProducesZ32] at hz
            | bits n0 =>
              rcases dsts with ⟨d0, ⟨⟩⟩
              cases d0 with
              | vec _ => simp [opProducesZ32] at hz
              | gpr rd =>
                simp only [opProducesZ32, Bool.and_eq_true, Nat.beq_eq] at hz
                obtain ⟨rfl, hzop⟩ := hz
                have hrd : rd ∉ T.frame.scratch := hdg' rd (by simp [tupDstGprs])
                have hrda : isAllocGpr T.toIsa hints.saved rd = true :=
                  hdg rd (by simp [tupDstGprs])
                have hcmpEq : (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1 =
                    (if Nat.ble 32 64 && !(cl == FlagMask.none) then
                      match T.gpr.aluZeroOut? 32 codeN (.gpr rd) with
                      | some eqNe => some (.cmp 32 (.var nv) (.immBits 32 0#64) eqNe)
                      | none => killFlags T.toIsa cl st.flags
                    else killFlags T.toIsa cl st.flags) := by
                  cases codeN <;> rfl
                by_cases hflc : (!(cl == FlagMask.none)) = true
                · cases halu : T.gpr.aluZeroOut? 32 codeN (.gpr rd) with
                  | none =>
                    refine T.gprSpec.op_zero32 hzop hop' rfl hpg hrd hph hwpN hc
                      fun s' ⟨⟨rv, ⟨hP, hdef⟩, hrd_eq⟩, hm⟩ hfr => ?_
                    refine lowerOp_z32_finish
                      (flagsPost :=
                          (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1)
                      hA hI (hMgrow (rv, ())) hdef ?_ ?_
                      hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
                    · simpa [hcmpEq, halu, hflc] using
                        (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                    · simpa [hcmpEq, halu, hflc] using
                        (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                    · refine kont rvs s'' hP'' ?_ hM'' hI''
                      dsimp only; rw [hz_eq]
                      dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
                      exact hA''
                  | some eqNe =>
                    have hcl : cl ≠ FlagMask.none := fun h => by subst h; simp at hflc
                    refine T.gprSpec.op_aluZero_spec halu hcl hop' hpg hdg' hph hwpN hc
                      fun s' ⟨⟨rv, ⟨hP, hdef⟩, _, hzfn, hflCmp⟩, hm⟩ hfr => ?_
                    have hrd_eq : T.mach.getGpr s' rd = rv.setWidth 64 :=
                      hzfn rd rfl rfl hzop
                    have hfok : FlagFactOk T (G' (rv, ())) s'
                        (some (.cmp 32 (.var nv) (.immBits 32 0#64) eqNe)) := by
                      refine ⟨by decide, rv, 0#32, List.mem_cons_self .., fun v hv => ?_,
                        ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, hflCmp⟩
                      cases mem_cons_top hA.ctx_lt hv; rfl
                    have hfsc : FlagFactScope (nv + 1)
                        (some (.cmp 32 (.var nv) (.immBits 32 0#64) eqNe)) :=
                      ⟨by simp [symArgScopeOk], rfl⟩
                    refine lowerOp_z32_finish
                      (flagsPost :=
                          (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1)
                      hA hI (hMgrow (rv, ())) hdef ?_ ?_
                      hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
                    · simpa [hcmpEq, hflc, halu] using hfok
                    · simpa [hcmpEq, hflc, halu] using hfsc
                    · refine kont rvs s'' hP'' ?_ hM'' hI''
                      dsimp only; rw [hz_eq]
                      dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
                      exact hA''
                · refine T.gprSpec.op_zero32 hzop hop' rfl hpg hrd hph hwpN hc
                    fun s' ⟨⟨rv, ⟨hP, hdef⟩, hrd_eq⟩, hm⟩ hfr => ?_
                  refine lowerOp_z32_finish
                    (flagsPost :=
                        (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1)
                    hA hI (hMgrow (rv, ())) hdef ?_ ?_
                    hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
                  · simpa [hcmpEq, hflc] using
                      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                  · simpa [hcmpEq, hflc] using
                      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                  · refine kont rvs s'' hP'' ?_ hM'' hI''
                    dsimp only; rw [hz_eq]
                    dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
                    exact hA''
      · have hzf : opProducesZ32 T.toIsa codeN pas dsts = false := Bool.eq_false_iff.mpr hz
        have hpick' := hpick
        rw [hzf] at fin
        exact gprOp_with_flags hA hargsN (by simpa [hzf] using hpick') hop' hpg hdg' hph hwpN hc
          fun s' hQ hm hfr => fin rfl s' [] hQ hm hfr rfl
    all_goals
      exact T.vecSpec.vop_spec hop' hpg hpv hdg' hdv' hph hwpN hc
        fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
          fin rfl s' _ ⟨rvs, hP, hdh, (fun _ h => nomatch h),
            (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
            (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hremD | hpick
  · obtain ⟨⟨c'', cl⟩, hrd, he⟩ := Option.map_eq_some_iff.mp hremD; cases he
    refine tryRematDirect_ok hA hargs hdg' hwp' hc hrd fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hremC | hpick
  · obtain ⟨⟨c'', cl⟩, hrc, he⟩ := Option.map_eq_some_iff.mp hremC; cases he
    refine tryRematCmpEqImm_ok hA hargsN hdg' hwpN hc hrc fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl
  rcases orElse_eq_some hpick with hremA | hslot
  · obtain ⟨⟨c'', cl⟩, hra, he⟩ := Option.map_eq_some_iff.mp hremA; cases he
    refine tryRematAdd64SameDst_ok hA hargsN hdg' hwpN hc hra fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hfr rfl
  · obtain ⟨⟨c'', cl, z'', fl, ex⟩, hsl, he⟩ := Option.map_eq_some_iff.mp hslot
    cases he
    refine trySlotOp_ok hA hI hargsN hdg' hwpN hc hsl
      (fun hz s' ⟨rvs, hP, hdh, hex⟩ hfo hfl hm hfr =>
        fin hz s' [] ⟨rvs, hP, hdh, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩ hm hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hfo hfl hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true :=
      hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) hfo hfl).1 (hflTr (rv, ()) hfo hfl).2
      hP hrd_eq hm hfr hrda fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]
    dsimp only [tupDstGprs, tupFlatMap, PDst.gprs]
    exact hA''

theorem lowerOp_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {ts : List Ty} {op₁ : Op Val ts} {op : Op VNat ts}
    {deferFuse : Bool}
    (hop : OpRel G op₁ op) (hl : lowerOp T.toIsa hints nv ip st op deferFuse = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    {P : Tup Val ts → Prop} (hwp : op₁.wp P)
    (kont : ∀ (rvs : Tup Val ts) s', P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st'.memDefs →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hMgrow : ∀ rvs : Tup Val ts,
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs := fun rvs =>
    hM.grow (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun _ h => List.mem_append_right _ h)
  have elide_push : ∀ (t0 : Ty) (hrs : ts = [t0]), (∀ a b, t0 ≠ .pair a b) →
      ∀ (rvs : Tup Val ts) (df : DefFact),
      c = [] → st' = { st with defs := st.defs.insert nv df } →
      P rvs → DefOk (Tup.zip rvs (Tup.levels ts nv) ++ G) nv df →
      T.mach.Run host (k + ([] : List T.Directive).length) s post := by
    intro t0 hrs hnp rvs df hc0 hst hP hdef
    subst hrs; subst hc0; subst hst; rcases rvs with ⟨rv, ⟨⟩⟩
    have hvw : ∀ sw, st.vecWidths.find? nv = some sw →
        t0.size ≤ sw.bits ∧ ∃ a b, t0 = .pair a b := fun sw hw =>
      absurd (hA.vw_lt _ _ hw) (Nat.lt_irrefl _)
    have hvw1 : ∀ x, nv < x → st.vecWidths.find? x = none := fun x hx =>
      Option.eq_none_iff_forall_ne_some.mpr fun sw hw =>
        absurd (hA.vw_lt _ _ hw) (Nat.not_lt.mpr (Nat.le_of_lt hx))
    have hA1 := hA.push t0 rv st.vecWidths (fun _ _ => rfl) hvw hvw1
      (fun _ a b h => absurd h (hnp a b))
    refine kont (rv, ()) s hP ?_ (hMgrow (rv, ())) hI
    simpa only [Tup.zip, Tup.levels, List.cons_append, List.nil_append,
      List.length_cons, List.length_nil] using
      ({ hA1 with
         defs := fun x d hx => by
           dsimp only at hx; rw [Trie.find?_insert] at hx; split at hx
           · cases hx; subst_vars
             simpa only [Tup.zip, Tup.levels, List.cons_append, List.nil_append,
               List.length_cons, List.length_nil] using hdef
           · exact hA1.defs x d hx
         defs_lt := fun x d hx => by
           dsimp only at hx; rw [Trie.find?_insert] at hx; split at hx
           · subst_vars; exact Nat.lt_succ_self _
           · exact hA1.defs_lt x d hx } :
        Agree T (⟨t0, rv, nv⟩ :: G) (nv + 1) { st with defs := st.defs.insert nv df } s σ)
  unfold lowerOp at hl
  split at hl
  · cases hop with | mk code hargs =>
    rcases orElse_eq_some hl with hrb_m | hrd_m
    · obtain ⟨df, hrb, rfl, rfl⟩ := Option.map_eq_some_iff.mp hrb_m
      obtain ⟨hrs, rvs, hP, hdef⟩ := recordBoolDef_ok hA.defs hargs hA.ctx_lt hwp hrb
      exact elide_push .bool hrs (fun _ _ h => by cases h) rvs df rfl rfl hP hdef
    · obtain ⟨df, hd, rfl, rfl⟩ := Option.map_eq_some_iff.mp hrd_m
      obtain ⟨w, hrs, rvs, hP, hdef⟩ := recordDefC_elide_ok hA.defs hargs hA.ctx_lt hwp hd
      exact elide_push (.bits w) hrs (fun _ _ h => by cases h) rvs df rfl rfl hP hdef
  split at hl
  · cases hop with | mk code hargs =>
    rename_i sig args₁ args
    cases hd : recordDefC T.toIsa.gpr.addrCse st.defs code args with
    | none => simp [hd] at hl
    | some df =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      obtain ⟨w, hrs, rvs, hP, hdef⟩ := recordDefC_elide_ok hA.defs hargs hA.ctx_lt hwp hd
      exact elide_push (.bits w) hrs (fun _ _ h => by cases h) rvs df rfl rfl hP hdef
  obtain ⟨dsts, hdst, hl⟩ := Option.bind_eq_some_iff.mp hl
  rcases orElse_eq_some hl with hbody | hrem
  · exact lowerOpBody_ok hsv hop hdst hbody hc hA hM hI hwp kont
  · obtain ⟨⟨x, base, disp, rb⟩, hmiss, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨hdef, hrb⟩ := findMissingRematArg_ok hmiss
    obtain ⟨tmp, htmp_mem, hrem⟩ := List.exists_of_findSome?_eq_some hrem
    obtain ⟨cPre, hcPre, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨⟨cOp, st2⟩, hbody, heq⟩ := Option.map_eq_some_iff.mp hrem
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have htmp_alloc : isAllocGpr T.toIsa hints.saved tmp = true :=
      rematTempCands_isAllocGpr (resolveDsts_spec hdst).1 htmp_mem
    have hc' := hc.append
    exact rematAddImm64_ok hA hI htmp_alloc hdef hrb hcPre hc'.1 fun s1 hA1 hI1 =>
      lowerOpBody_ok hsv hop hdst hbody hc'.2 hA1 hM hI1 hwp fun rvs s2 hP hA2 hM2 hI2 => by
        simpa [List.length_append, Nat.add_assoc] using kont rvs s2 hP hA2 hM2 hI2

end Lemmas

/-! ## Part B: structural `LabelsUnique` -/

section Labels
variable {I : Isa}

theorem NoLab.nil : NoLab I [] := fun _ h => nomatch h

theorem NoLab.append {a b : List I.Directive} (ha : NoLab I a) (hb : NoLab I b) :
    NoLab I (a ++ b) := fun l h => (List.mem_append.mp h).elim (ha l) (hb l)

/-! ### Label names -/

private def digF (a : Nat) (c : Char) : Nat := a * 10 + (c.toNat - 48)

private theorem natDigits_fold : ∀ (fuel n : Nat) (acc : List Char), n < fuel →
    (natDigits fuel n acc).foldl digF 0 = acc.foldl digF n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, acc, h => by
    have hc : ∀ d < 10, (Char.ofNat (48 + d)).toNat - 48 = d := by decide
    simp only [natDigits]
    split
    · next h10 =>
      rw [natDigits_fold fuel (n / 10) _ (by have := Nat.le_of_ble_eq_true h10; omega)]
      simp only [List.foldl, digF, hc _ (Nat.mod_lt _ (by decide))]
      rw [Nat.div_add_mod' n 10]
    · next h10 =>
      have : n < 10 := by simpa [Nat.ble_eq] using h10
      simp only [List.foldl, digF, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt this, hc n this]

theorem lname_inj {fn : Sym} {a b : Nat} (h : lname fn a = lname fn b) : a = b := by
  have h' := congrArg String.toList h
  simp only [lname, String.toList_append, String.toList_ofList, List.append_assoc] at h'
  have h'' := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left h'))
  have := congrArg (List.foldl digF 0) h''
  rwa [natDigits_fold _ _ _ (Nat.lt_succ_self a), natDigits_fold _ _ _ (Nat.lt_succ_self b)] at this

theorem lname_ne {fn : Sym} {a : Nat} : lname fn a ≠ fn := fun h => by
  have := congrArg String.length h
  simp only [lname, String.length_append] at this
  have : ".L".length = 2 := rfl
  omega

/-- Labels `lname fn j` with `a ≤ j < b`. -/
def lrange (fn : Sym) (a b : Nat) (l : Sym) : Prop := ∃ j, a ≤ j ∧ j < b ∧ l = lname fn j

theorem lrange_disj {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l)
    (h' : lrange fn a' b' l) (hd : b ≤ a' ∨ b' ≤ a) : False := by
  obtain ⟨j, h1, h2, rfl⟩ := h; obtain ⟨j', h1', h2', he⟩ := h'
  have := lname_inj he; omega

theorem lrange_mono {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l) (ha : a' ≤ a)
    (hb : b ≤ b') : lrange fn a' b' l := by
  obtain ⟨j, h1, h2, rfl⟩ := h; exact ⟨j, by omega, by omega, rfl⟩

/-! ### Label-range invariant -/

/-- Equal labels of `c` sit at equal positions, and all labels satisfy `S`. -/
def LabOk (I : Isa) (S : Sym → Prop) (c : List I.Directive) : Prop :=
  (∀ (i j : Nat) l, c[i]? = some (I.frame.label l) → c[j]? = some (I.frame.label l) → i = j) ∧
  ∀ l, I.frame.label l ∈ c → S l

theorem LabOk.clean {S : Sym → Prop} {c : List I.Directive} (h : NoLab I c) : LabOk I S c :=
  ⟨fun _ _ l hi _ => absurd (List.mem_of_getElem? hi) (h l), fun l hl => absurd hl (h l)⟩

theorem LabOk.mono {S S' : Sym → Prop} {c : List I.Directive} (h : LabOk I S c)
    (hs : ∀ l, S l → S' l) : LabOk I S' c := ⟨h.1, fun l hl => hs l (h.2 l hl)⟩

theorem LabOk.single (hcl : LabelClean I) (l : Sym) : LabOk I (· = l) [I.frame.label l] := by
  refine ⟨fun i j l' hi hj => ?_, fun l' hl => hcl.label_inj _ _ (List.mem_singleton.mp hl)⟩
  cases i <;> cases j <;> simp_all

theorem LabOk.append {S₁ S₂ S : Sym → Prop} {c₁ c₂ : List I.Directive} (h₁ : LabOk I S₁ c₁)
    (h₂ : LabOk I S₂ c₂) (hd : ∀ l, S₁ l → S₂ l → False) (hs : ∀ l, S₁ l ∨ S₂ l → S l) :
    LabOk I S (c₁ ++ c₂) := by
  refine ⟨fun i j l hi hj => ?_, fun l hl => hs l ((List.mem_append.mp hl).imp (h₁.2 l) (h₂.2 l))⟩
  rw [List.getElem?_append] at hi hj
  split at hi <;> split at hj
  · exact h₁.1 i j l hi hj
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hi)) (h₂.2 l (List.mem_of_getElem? hj))).elim
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hj)) (h₂.2 l (List.mem_of_getElem? hi))).elim
  · have := h₂.1 _ _ l hi hj; omega

theorem LabOk.pre {S : Sym → Prop} {a c : List I.Directive} (ha : NoLab I a) (h : LabOk I S c) :
    LabOk I S (a ++ c) :=
  (LabOk.clean (S := fun _ => False) ha).append h (fun _ h _ => h) (fun _ h => h.elim False.elim id)

/-! ### Snippet code is label-free -/

theorem tryArg_some {st : SymState I} {pref : List I.Cond} {α : Type} {t : Ty} {a : Arg VNat t}
    {k : PArg I.Reg I.VReg I.Cond t → Option α} {res : α} (h : tryArg I st pref t a k = some res) :
    ∃ pa, k pa = some res := by
  have fs : ∀ {β γ : Type} {l : List β} {g : β → Option α} {f : γ → PArg I.Reg I.VReg I.Cond t},
      (∀ b, g b = some res → ∃ x, k (f x) = some res) → l.findSome? g = some res →
      ∃ pa, k pa = some res := fun hg h => by
    obtain ⟨b, -, hb⟩ := List.exists_of_findSome?_eq_some h; obtain ⟨x, hx⟩ :=
        hg b hb; exact ⟨_, hx⟩
  have gpr : ∀ {sa}, tryGpr I st.regs sa (k ∘ .gpr) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.gpr) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  have vec : ∀ {sa}, tryVec I st.regs sa (k ∘ .vec) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.vec) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  cases t with
  | bool =>
    have flag : ∀ {sa}, tryFlag I st.regs pref sa (k ∘ .flag) = some res → ∃ pa, k pa = some res :=
        by
        intro sa h; rcases orElse_eq_some h with h | h
        · obtain ⟨c, -, hb⟩ := List.exists_of_findSome?_eq_some h
          split at hb <;> first | exact ⟨_, hb⟩ | simp at hb
        · exact fs (f := PArg.flag) (fun ⟨_, rl⟩ hb => by
            cases rl <;> simp only at hb <;> (try split at hb) <;>
              first | exact ⟨_, hb⟩ | simp at hb) h
    cases a with
    | var x => rcases orElse_eq_some h with h | h <;> first | exact flag h | exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact flag h
      rcases orElse_eq_some h with h | h <;> first | exact ⟨_, h⟩ | exact gpr h
  | bits w =>
    cases a with
    | var x => exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact gpr h | simp at h
  | pair x y =>
    cases a with
    | var x => exact vec h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact vec h | simp at h
  | float _ => simp [tryArg] at h

theorem pickPArgs_some {st : SymState I} {pref : List I.Cond} {α : Type} :
    ∀ {sig : List Ty} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α} {res : α},
    pickPArgs I st pref args k = some res → ∃ pas, k pas = some res
  | [], (), _, _, h => ⟨(), h⟩
  | _ :: _, (_, _), _, _, h => by
    obtain ⟨pa, h⟩ := tryArg_some h
    obtain ⟨pas, h⟩ := pickPArgs_some h
    exact ⟨_, h⟩

theorem tryAddr_some {st : SymState I} {vh : VariantHint} {α : Type} {a : Arg VNat i64}
    {k : AddrArg I.Reg → Option α} {res : α} (h : tryAddr I st vh a k = some res) :
    ∃ aa, k aa = some res := by
  cases a with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨_, h⟩
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
  | var x =>
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h <;> (try split at h) <;>
        first | (obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩) | simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
    rcases orElse_eq_some h with h | h
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · simp at h
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, h⟩
      · simp at h

theorem tryAddrZext_some {st : SymState I} {α : Type} {a : Arg VNat i64}
    {k : I.Reg → I.Reg → AddrScale → Int64 → Option α} {res : α}
    (h : tryAddrZext I st a k = some res) :
    ∃ rb ri sc disp, k rb ri sc disp = some res := by
  cases a with
  | imm _ => simp [tryAddrZext] at h
  | var x =>
    simp only [tryAddrZext] at h
    cases hdef : addrDefOf I.gpr.addrCse st.defs x with
    | none => simp [hdef] at h
    | some df =>
      cases df with
      | addrSum base idx sh d =>
        rw [hdef] at h; dsimp only at h
        cases hz : zextAddrSumVar? st.defs base idx sh with
        | none => simp [hz] at h
        | some _ =>
          rw [hz] at h; dsimp only at h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
          exact ⟨_, _, _, _, h⟩
      | _ => simp [hdef] at h

variable (hcl : LabelClean I)
include hcl

private theorem execMovi_clean (st : SymState I) (deadHint : Bool) (d : I.Reg) (c : BitVec 64) :
    NoLab I (execMovi I st deadHint d c).1 := by
  unfold execMovi
  split
  · rename_i fn hmd
    split
    · exact hcl.moviDeadFlags fn d c hmd
    · exact hcl.movi d c
  · exact hcl.movi d c

theorem execMove_clean {nslots : Nat} {saved : List I.Reg} {mv : I.Move} {st st' : SymState I}
    {deadHint : Bool} {c : List I.Directive}
    (h : execMove I nslots saved mv st deadHint = some (c, st')) : NoLab I c := by
  cases mv <;> simp only [execMove] at h <;> (repeat' split at h) <;>
    first | (simp at h; done) | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl,
      -⟩ := h)
  all_goals first
    | exact hcl.mov _ _
    | exact execMovi_clean hcl _ _ _ _
    | exact hcl.slotLd _ _
    | exact hcl.slotSt _ _
    | exact hcl.setcc _ _
    | exact hcl.vmov _ _ _
    | exact hcl.vslotLd _ _ _
    | exact hcl.vslotSt _ _ _
    | exact hcl.vmovi _ _ _ _ ‹_›

theorem execMoves_clean {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List I.Move} {st st' : SymState I} {c : List I.Directive},
    execMoves I nslots saved mvs st deadHint = some (c, st') → NoLab I c
  | [], _, _, _, h => by
    simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact NoLab.nil
  | _ :: _, _, _, _, h => by
    simp only [execMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    exact (execMove_clean hcl h1).append (execMoves_clean h2)

theorem stepPre_clean {h : I.Hints} {ip : Nat} {st st' : SymState I} {c : List I.Directive}
    (hs : stepPre I h ip st = some (c, st')) : NoLab I c := by
  simp only [stepPre] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · obtain ⟨⟨mc, st1⟩, h1, he⟩ := Option.map_eq_some_iff.mp hs
    split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1]
    · exact (execMoves_clean hcl h1).append hcl.clearFlags
    · exact execMoves_clean hcl h1

theorem execShufMoves_clean {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List (ShufMove I.Reg I.VReg I.Cond)} {st st' : SymState I} {c : List I.Directive},
    execShufMoves I nslots saved mvs st deadHint = some (c, st') → NoLab I c
  | [], _, _, _, h => by
    simp only [execShufMoves, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact NoLab.nil
  | mv :: _, _, _, _, h => by
    simp only [execShufMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    refine NoLab.append ?_ (execShufMoves_clean h2)
    cases mv with
    | base _ => exact execMove_clean hcl h1
    | rematAdd _ _ _ _ =>
      simp only [execShufMove] at h1
      repeat' (split at h1 <;> try (simp at h1; done))
      obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨_, hrm, hp⟩ := Option.map_eq_some_iff.mp h1
      simp only [Prod.mk.injEq] at hp; rw [← hp.1]; exact rematAddImm64_clean hcl hrm

theorem shuffle_clean {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {deadHint : Bool} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts deadHint = some (c, st')) : NoLab I c := by
  simp only [shuffle] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · split at hs
    · simp at hs
    · split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rw [← hs.1]; exact execShufMoves_clean hcl ‹_›
      · simp at hs

theorem canonAbiCode_clean : ∀ {ts : List Ty} (locs : Tup (AbiReg I.Reg I.VReg) ts)
    (sk : List Bool), NoLab I (canonAbiCode I locs sk)
  | [], (), _ => NoLab.nil
  | _ :: _, (.gpr _, locs), sk => by
    refine NoLab.append ?_ (canonAbiCode_clean locs sk.tail)
    split
    · exact NoLab.nil
    · exact hcl.canonAbi _ _
  | _ :: _, (.vec _, locs), sk => canonAbiCode_clean locs sk.tail

theorem restoreCsList_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (restoreCsList I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotLd _ _).append (restoreCsList_clean _ rs)

theorem saveCsList_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (saveCsList I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotSt _ _).append (saveCsList_clean _ rs)

theorem restoreCs_clean (base : Nat) (rs : List I.Reg) : NoLab I (restoreCs I base rs) := by
  cases rs with
  | nil => exact NoLab.nil
  | cons r rs' =>
    dsimp only [restoreCs]
    cases hfn : I.frame.restoreRegs? with
    | none => exact restoreCsList_clean hcl base (r :: rs')
    | some fn => exact hcl.restoreRegs fn base (r :: rs') hfn

theorem saveCs_clean (base : Nat) (rs : List I.Reg) : NoLab I (saveCs I base rs) := by
  cases rs with
  | nil => exact NoLab.nil
  | cons r rs' =>
    dsimp only [saveCs]
    cases hfn : I.frame.saveRegs? with
    | none => exact saveCsList_clean hcl base (r :: rs')
    | some fn => exact hcl.saveRegs fn base (r :: rs') hfn

omit hcl in
private theorem tryGpr_some {st : SymState I} {α : Type} {sa : SymArg}
    {k : I.Reg → Option α} {res : α} (h : tryGpr I st.regs sa k = some res) :
    ∃ r, k r = some res := by
  obtain ⟨⟨_, rl⟩, -, hb⟩ := List.exists_of_findSome?_eq_some h
  cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb

private theorem tryTestMemVar_clean {st : SymState I} {neg : Bool} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryTestMemVar I st neg w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryTestMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩; cases tm with
    | bits _ =>
      simp only [hmd] at h; split at h <;> try (simp at h; done)
      obtain ⟨_, h1⟩ := tryAddr_some h; obtain ⟨_, h2⟩ := tryArg_some h1
      exact hcl.testMem _ _ _ _ _ _ _ h2
    | _ => simp [hmd] at h

private theorem tryCmpMemVar_clean {st : SymState I} {co : CmpOp} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryCmpMemVar I st co w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryCmpMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩; cases tm with
    | bits _ =>
      simp only [hmd] at h; split at h <;> try (simp at h; done)
      obtain ⟨_, h1⟩ := tryAddr_some h; obtain ⟨_, h2⟩ := tryArg_some h1
      exact hcl.cmpMem _ _ _ _ _ _ _ h2
    | _ => simp [hmd] at h

private theorem tryTestFuse_clean {st : SymState I} {neg : Bool} {w t : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryTestFuse I st neg w t pd = some (c, cl)) : NoLab I c := by
  unfold tryTestFuse at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · exact tryTestMemVar_clean hcl h1
      · obtain ⟨_, hk⟩ := tryArg_some h2; exact hcl.testOp _ _ _ _ _ _ _ hk
    | andVarVar _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h
      · exact tryTestMemVar_clean hcl h1
      rcases orElse_eq_some h with h2 | h3
      · exact tryTestMemVar_clean hcl h2
      · obtain ⟨_, hk1⟩ := tryArg_some h3
        obtain ⟨_, hk2⟩ := tryArg_some hk1
        exact hcl.testOp _ _ _ _ _ _ _ hk2
    | _ => simp [hdef] at h

omit hcl in
private theorem cmpMemRes_fst {st : SymState I} {co : CmpOp} {w : Nat}
    {a b : SymArg} {pd : PDst I.Reg I.VReg I.Cond .bool} {d c : List I.Directive}
    {cl cl' : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : cmpMemRes I st co w a b pd d cl = (c, cl', fl, ex)) : d = c := by
  unfold cmpMemRes at h; split at h <;> (simp only [Prod.mk.injEq] at h; exact h.1)

private theorem tryWidenZextCmp_clean {st : SymState I} {vh : VariantHint} {co : CmpOp}
    {w : Nat} {a b : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool}
    {c : List I.Directive} {cl : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : tryWidenZextCmp I st vh co w a b pd = some (c, cl, fl, ex)) : NoLab I c := by
  unfold tryWidenZextCmp at h; split at h; · simp at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he; rw [← he.1]; exact hcl.op _ _ _ _ _ _ hop

private theorem shiftCmpGo_clean {st : SymState I} {co : CmpOp} {w x y : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask} {ls : Bool}
    (h : shiftCmpGo I st co w x y pd = some (c, cl, ls)) : NoLab I c := by
  unfold shiftCmpGo at h
  rcases orElse_eq_some h with h' | h' <;>
  · obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨⟨_, _⟩, hsc, he⟩ := Option.map_eq_some_iff.mp h'
    rcases he with ⟨rfl, rfl, rfl⟩; exact hcl.shiftCmp _ _ _ _ _ _ _ _ _ _ hsc

private theorem tryExtCmp_clean {st : SymState I} {vh : VariantHint} {co : CmpOp} {w t : Nat}
    {ci : BitVec w} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    {fl : Option FlagFact} {ex : Option I.Cond}
    (h : tryExtCmp I st vh co w t ci pd = some (c, cl, fl, ex)) : NoLab I c := by
  unfold tryExtCmp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw _ x | zextVar mw _ x =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · cases hmd : st.memDefs.find? x with
        | none => simp [hmd] at h1
        | some p =>
          rcases p with ⟨tm, addr⟩
          cases tm with
          | bits _ =>
            simp only [hmd] at h1; split at h1 <;> try (simp at h1; done)
            obtain ⟨_, hk⟩ := tryAddr_some h1
            obtain ⟨⟨c0, cl0⟩, hcm, he⟩ := Option.map_eq_some_iff.mp hk
            rw [← cmpMemRes_fst he]; exact hcl.cmpMem _ _ _ _ _ _ _ hcm
          | _ => simp [hmd] at h1
      · split at h2 <;> try (simp at h2; done)
        rcases orElse_eq_some h2 with hwz | h2
        · exact tryWidenZextCmp_clean hcl hwz
        · obtain ⟨_, hk⟩ := tryGpr_some h2
          obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk
          simp only [Prod.mk.injEq] at he; rw [← he.1]; exact hcl.op _ _ _ _ _ _ hop
    | _ => simp [hdef] at h

private theorem tryFuseCmp_clean {st : SymState I} {vh : VariantHint} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : tryFuseCmp I st vh code args dsts = some (c, cl, fl, ex)) : NoLab I c := by
  cases code with
  | cmp _ ty mty _ =>
    cases ty with
    | bits _ =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
        unfold tryFuseCmp at h; dsimp only at h
        split at h; · simp at h
        rcases orElse_eq_some h with ht | h
        · split at ht
          · obtain ⟨⟨_, _⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he; rw [← he.1]
            cases a with
            | var _ =>
              cases b with
              | imm _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestFuse_clean hcl ht' | simp at ht'
              | var _ => simp at ht'
            | imm _ =>
              cases b with
              | var _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestFuse_clean hcl ht' | simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some h with he | hm
        · cases a <;> cases b <;> first | exact tryExtCmp_clean hcl he | simp at he
        · rcases orElse_eq_some hm with hm | hsw
          · rcases orElse_eq_some hm with hm' | hm' <;>
            · cases a <;> cases b <;> try (simp at hm'; done)
              all_goals
                obtain ⟨⟨c0, _⟩, hcmv, hmap⟩ := Option.map_eq_some_iff.mp hm'
                have hce : c0 = c := by
                  split at hmap; · exact cmpMemRes_fst hmap
                  simp only [Prod.mk.injEq] at hmap; exact hmap.1
                subst hce; exact tryCmpMemVar_clean hcl hcmv
          · rcases orElse_eq_some hsw with hs | hwz
            · cases a <;> cases b <;> try (simp at hs; done)
              obtain ⟨⟨_, _, _⟩, hgo, he⟩ := Option.map_eq_some_iff.mp hs
              simp only [Prod.mk.injEq] at he; rw [← he.1]
              exact shiftCmpGo_clean hcl hgo
            · exact tryWidenZextCmp_clean hcl hwz
      | _ => simp [tryFuseCmp] at h
    | _ => simp [tryFuseCmp] at h
  | _ => simp [tryFuseCmp] at h

private theorem tryLoadSext_clean {st : SymState I} {vh : VariantHint} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask}
    (h : tryLoadSext I st vh code args dsts = some (c, cl)) : NoLab I c := by
  cases code <;> try (simp [tryLoadSext] at h; done)
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
  cases a with
  | imm _ => simp [tryLoadSext] at h
  | var x =>
    cases d0 with
    | vec _ => simp [tryLoadSext] at h
    | gpr rd =>
      simp only [tryLoadSext] at h
      cases hmd : st.memDefs.find? x with
      | none => simp [hmd] at h
      | some p =>
        rcases p with ⟨tm, addr⟩
        cases tm with
        | bits w' =>
          simp only [hmd] at h
          split at h
          · rcases orElse_eq_some h with h1 | h1
            · obtain ⟨_, h2⟩ := tryAddr_some h1; exact hcl.loadSext _ _ _ _ _ _ h2
            · obtain ⟨_, _, _, _, h2⟩ := tryAddrZext_some h1
              exact hcl.loadSextZextIdx _ _ _ _ _ _ _ _ _ h2
          · simp at h
        | _ => simp [hmd] at h

private theorem tryTestSlot_clean {h' : I.Hints} {st : SymState I} {neg : Bool} {n t : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryTestSlot I h' st neg n t pd = some (c, cl)) : NoLab I c := by
  unfold tryTestSlot at h
  split at h; · simp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm _ _ _ =>
      simp only [hdef] at h
      split at h
      · obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h
        exact hcl.testMem _ _ _ _ _ _ _ hk
      · simp at h
    | andVarVar _ _ _ =>
      simp only [hdef] at h
      split at h
      · rcases orElse_eq_some h with h1 | h1 <;>
          (obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h1;
           obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.testMem _ _ _ _ _ _ _ hk')
      · simp at h
    | _ => simp [hdef] at h

private theorem tryExtSlot_clean {h' : I.Hints} {st : SymState I} {co : CmpOp} {n t : Nat}
    {ci : BitVec n} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryExtSlot I h' st co n t ci pd = some (c, cl)) : NoLab I c := by
  unfold tryExtSlot at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar _ _ _ | zextVar _ _ _ =>
      simp only [hdef] at h
      split at h
      · obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h
        exact hcl.cmpMem _ _ _ _ _ _ _ hk
      · simp at h
    | _ => simp [hdef] at h

private theorem trySlotOp_clean {h' : I.Hints} {st : SymState I} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask} {z : Bool} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : trySlotOp I h' st code args dsts = some (c, cl, z, fl, ex)) : NoLab I c := by
  cases code with
  | cmp _ ty mty _ =>
    cases ty with
    | bits _ =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
        unfold trySlotOp at h; dsimp only at h
        split at h; · simp at h
        obtain ⟨⟨c1, cl1, fl1, ex1⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
        rcases orElse_eq_some hs with ht | hs
        · split at ht
          · obtain ⟨⟨_, _⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he; rw [← he.1]
            cases a with
            | var _ =>
              cases b with
              | imm _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestSlot_clean hcl ht' | simp at ht'
              | var _ => simp at ht'
            | imm _ =>
              cases b with
              | var _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestSlot_clean hcl ht' | simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some hs with he' | hm
        · cases a <;> cases b <;> try (simp at he'; done)
          all_goals
            obtain ⟨⟨_, _⟩, he'', hmap⟩ := Option.map_eq_some_iff.mp he'
            simp only [extCmpMemRes, Prod.mk.injEq] at hmap; rw [← hmap.1]
            exact tryExtSlot_clean hcl he''
        · split at hm; · simp at hm
          rcases orElse_eq_some hm with h' | h' <;>
          · cases a <;> cases b <;> try (simp at h'; done)
            all_goals
              obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h'
              obtain ⟨_, hk'⟩ := tryArg_some hk
              obtain ⟨⟨c0, _⟩, hcm, hmap⟩ := Option.map_eq_some_iff.mp hk'
              have hce : c0 = c1 := by
                split at hmap; · exact cmpMemRes_fst hmap
                simp only [Prod.mk.injEq] at hmap; exact hmap.1
              subst hce; exact hcl.cmpMem _ _ _ _ _ _ _ hcm
      | _ => simp [trySlotOp] at h
    | _ => simp [trySlotOp] at h
  | add ty | sub ty | mul ty | and ty | or ty | xor ty =>
    cases ty with
    | bits _ =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases d0 with
      | vec _ => simp [trySlotOp] at h
      | gpr _ =>
        unfold trySlotOp tryAluSlot at h; dsimp only at h
        split at h; · simp at h
        obtain ⟨⟨_, _, _⟩, hs, he⟩ := Option.map_eq_some_iff.mp h; cases he
        obtain ⟨⟨_, _⟩, hs', he0⟩ := Option.map_eq_some_iff.mp hs; cases he0
        rcases orElse_eq_some hs' with h1 | h2
        · cases a <;> try simp at h1
          obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h1
          obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.aluMem _ _ _ _ _ _ _ _ hk'
        · cases b <;> try simp at h2
          obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.aluMem _ _ _ _ _ _ _ _ hk'
    | _ => simp [trySlotOp] at h
  | _ => simp [trySlotOp] at h

private theorem tryLeaArith_clean {st : SymState I} {sig : List Ty}
    {args : Tup (Arg VNat) sig} {c : List I.Directive} {cl : FlagMask} {z : Bool} :
    ∀ {ts : List Ty} {code : OpCode sig ts} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts},
    tryLeaArith I st code args dsts = some (c, cl, z) → NoLab I c
  | [.bits w], _, (.gpr _, ()), htl => by
    unfold tryLeaArith at htl; dsimp only at htl
    rcases orElse_eq_some htl with htl | hsa
    case inr => exact tryShiftAlu_clean hcl hsa
    rcases orElse_eq_some htl with htl | hzext
    · obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨⟨_, _⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp htl; cases heq
      exact hcl.leaArith _ _ _ _ _ _ _ _ hlea
    · by_cases h64 : w = 64
      · subst h64; dsimp only [tryLeaArithZext] at hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨⟨_, _⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp hzext; cases heq
        exact hcl.leaArithZext _ _ _ _ _ _ _ hlea
      · simp only [tryLeaArithZext] at hzext; split at hzext <;> simp_all
  | [], _, _, htl | [_], _, (.vec _, ()), htl | [_], _, (.flag _, ()), htl
  | .bool :: [], _, _, htl | .float _ :: [], _, _, htl | .pair _ _ :: [], _, _, htl
  | _ :: _ :: _, _, _, htl => by simp [tryLeaArith] at htl

private theorem tryReuseFlagCmp_clean {st : SymState I} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    {fl : Option FlagFact} {ex : Option I.Cond}
    (h : tryReuseFlagCmp I st code args dsts = some (c, cl, fl, ex)) : NoLab I c := by
  cases hstf : st.flags with
  | none => simp [tryReuseFlagCmp, hstf] at h
  | some ff =>
    cases ff; cases code <;> try (simp [tryReuseFlagCmp, hstf] at h; done)
    rename_i co ty mty hm
    cases ty <;> cases mty <;> try (simp [tryReuseFlagCmp, hstf] at h; done)
    rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    simp only [tryReuseFlagCmp, hstf] at h
    obtain ⟨⟨_, _, _⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h; · simp at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases pd with
    | vec _ => simp at h
    | flag _ =>
      simp only at h; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact NoLab.nil
      · simp at h
    | gpr _ =>
      obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rw [← he.1]; exact hcl.op _ _ _ _ _ _ hop

private theorem lowerOpBody_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive}
    (hl : lowerOpBody I h nv ip st op dsts = some (c, st')) :
    NoLab I c := by
  unfold lowerOpBody at hl
  split at hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  split at hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  obtain ⟨⟨c', cl, iv, _z, _fl, _ex⟩, hp, he⟩ := Option.map_eq_some_iff.mp hl
  cases he
  rcases orElse_eq_some hp with hreuse | hp
  · obtain ⟨⟨_, _, _, _⟩, hr, he⟩ := Option.map_eq_some_iff.mp hreuse; cases he
    rcases orElse_eq_some hr with hr | hr <;> exact tryReuseFlagCmp_clean hcl hr
  rcases orElse_eq_some hp with hfuse | hp
  · obtain ⟨⟨_, _, _, _⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse; cases he
    exact tryFuseCmp_clean hcl hfc
  rcases orElse_eq_some hp with hlx | hp
  · obtain ⟨⟨_, _⟩, hls, he⟩ := Option.map_eq_some_iff.mp hlx; cases he
    exact tryLoadSext_clean hcl hls
  rcases orElse_eq_some hp with hlea | hp
  · obtain ⟨⟨_, _, _⟩, htl, he⟩ := Option.map_eq_some_iff.mp hlea; cases he
    exact tryLeaArith_clean hcl htl
  rcases orElse_eq_some hp with hzero | hp
  · obtain ⟨⟨_, _, _⟩, htz, he⟩ := Option.map_eq_some_iff.mp hzero; cases he
    exact tryMoviZero_clean hcl htz
  rcases orElse_eq_some hp with hp | hp
  · obtain ⟨pas, hk⟩ := pickPArgs_some hp
    have hv : ((I.vec.vop (normCmpOp op dsts).code pas dsts (h.variant.getD ip .default)).map
        fun x => (x.1, x.2, true, false, killFlags I x.2 st.flags, none)) =
        some (c, cl, iv, _z, _fl, _ex) → NoLab I c := fun hk => by
      obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he
      exact hcl.vop _ _ _ _ _ _ hop
    split at hk
    · rcases orElse_eq_some hk with hk | hk
      · obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he
        exact hcl.op _ _ _ _ _ _ hop
      · exact hv hk
    · exact hv hk
  rcases orElse_eq_some hp with hrd | hp
  · obtain ⟨⟨_, _⟩, hrd', he⟩ := Option.map_eq_some_iff.mp hrd; cases he
    exact tryRematDirect_clean hcl hrd'
  rcases orElse_eq_some hp with hrc | hp
  · obtain ⟨⟨_, _⟩, hrc', he⟩ := Option.map_eq_some_iff.mp hrc; cases he
    exact tryRematCmpEqImm_clean hcl hrc'
  rcases orElse_eq_some hp with hra | hslot
  · obtain ⟨⟨_, _⟩, hra', he⟩ := Option.map_eq_some_iff.mp hra; cases he
    exact tryRematAdd64SameDst_clean hcl hra'
  · obtain ⟨⟨_, _, _, _, _⟩, hsl, he⟩ := Option.map_eq_some_iff.mp hslot; cases he
    exact trySlotOp_clean hcl hsl

theorem lowerOp_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {deferFuse : Bool} {c : List I.Directive}
    (hl : lowerOp I h nv ip st op deferFuse = some (c, st')) :
    NoLab I c := by
  unfold lowerOp at hl
  split at hl
  · rcases orElse_eq_some hl with h | h <;>
    · obtain ⟨df, -, rfl, -⟩ := Option.map_eq_some_iff.mp h; exact NoLab.nil
  split at hl
  · cases hd : recordDefC I.gpr.addrCse st.defs op.code op.args <;> simp [hd] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  obtain ⟨dsts, -, hl⟩ := Option.bind_eq_some_iff.mp hl
  rcases orElse_eq_some hl with hbody | hrem
  · exact lowerOpBody_clean hcl hbody
  · obtain ⟨_, -, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨_, -, hrem⟩ := List.exists_of_findSome?_eq_some hrem
    obtain ⟨cPre, hrm, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨⟨cOp, _⟩, hbody, he⟩ := Option.map_eq_some_iff.mp hrem
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    exact (rematAddImm64_clean hcl hrm).append (lowerOpBody_clean hcl hbody)

theorem lowerLoad_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {t : Ty}
    {a : Arg VNat i64} {fz : Bool} {c : List I.Directive}
    (hl : lowerLoad I h nv ip st t a fz = some (c, st')) :
    NoLab I c := by
  unfold lowerLoad at hl
  split at hl
  · split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl; rcases hl with ⟨rfl, -⟩; exact NoLab.nil
    · simp at hl
  split at hl
  · split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    rcases orElse_eq_some hta with hta | htz
    · obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.load _ _ _ _ _ hk
    · obtain ⟨_, _, _, _, hk⟩ := tryAddrZext_some htz; exact hcl.loadZextIdx _ _ _ _ _ _ _ _ hk
  · obtain ⟨_, -, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.vload _ _ _ _ _ hk
  · simp at hl

private theorem tryRmwHalf_clean {st : SymState I} {vh : VariantHint} {n x : Nat}
    {op : RmwOp} {other : Arg VNat (.bits n)} {a : Arg VNat i64} {c : List I.Directive}
    {clob : FlagMask} (h : tryRmwHalf I st vh n op x other a = some (c, clob)) : NoLab I c := by
  unfold tryRmwHalf at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, loadAddr⟩
    cases tm with
    | bits m' =>
      simp only [hmd] at h
      split at h
      · obtain ⟨_, hk1⟩ := tryAddr_some h
        obtain ⟨_, hk2⟩ := tryAddr_some hk1
        split at hk2
        · obtain ⟨_, hk3⟩ := tryArg_some hk2
          exact hcl.rmwMem _ _ _ _ _ _ hk3
        · simp at hk2
      · simp at h
    | _ => simp [hmd] at h

private theorem tryRmwStore_clean {st : SymState I} {vh : VariantHint} {t : Ty}
    {v : Arg VNat t} {a : Arg VNat i64} {c : List I.Directive} {clob : FlagMask}
    (h : tryRmwStore I st vh t v a = some (c, clob)) : NoLab I c := by
  cases t <;> cases v <;> try (simp [tryRmwStore] at h; done)
  simp only [tryRmwStore] at h
  split at h; · simp at h
  split at h
  · obtain ⟨⟨op, x, rhs⟩, -, hk⟩ := Option.bind_eq_some_iff.mp h
    rcases orElse_eq_some hk with hk1 | hk2
    · exact tryRmwHalf_clean hcl hk1
    · split at hk2
      · cases rhs with
        | imm _ => simp at hk2
        | var z => exact tryRmwHalf_clean hcl hk2
      · simp at hk2
  · simp at h

theorem lowerStore_clean {st st' : SymState I} {vh : VariantHint} {t : Ty} {v : Arg VNat t}
    {a : Arg VNat i64} {c : List I.Directive} (hl : lowerStore I st vh t v a = some (c, st')) :
    NoLab I c := by
  cases t with
  | pair x y =>
    simp only [lowerStore] at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨pa, hk⟩ := tryArg_some hta
    cases pa with
    | vec vs => obtain ⟨_, hk⟩ := tryAddr_some hk; exact hcl.vstore _ _ _ _ _ hk
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl; split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    rcases orElse_eq_some hta with hta | hrmw
    · obtain ⟨_, hk⟩ := tryArg_some hta
      rcases orElse_eq_some hk with hk | hkz
      · obtain ⟨_, hk⟩ := tryAddr_some hk
        exact hcl.store _ _ _ _ _ hk
      · obtain ⟨_, _, _, _, hk⟩ := tryAddrZext_some hkz
        exact hcl.storeZextIdx _ _ _ _ _ _ _ _ hk
    · exact tryRmwStore_clean hcl hrmw

theorem fnPrologue_clean (h : I.Hints) (E : Ext) : NoLab I (fnPrologue I h E) := by
  unfold fnPrologue; split
  · exact NoLab.nil
  · exact hcl.prologue _

theorem fnEpilogue_clean (h : I.Hints) (E : Ext) : NoLab I (fnEpilogue I h E) := by
  unfold fnEpilogue; split
  · exact NoLab.nil
  · exact hcl.epilogue _

omit hcl in
theorem lowerTail_spec {h : I.Hints} {E : Ext} {st : SymState I} {mc tail : List I.Directive}
    {ts : List Ty} {args : Tup (Arg VNat) ts} {locs : Tup (AbiReg I.Reg I.VReg) ts} {nv nl ip : Nat}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (hl : lowerTail I h E st mc tail args locs nv nl ip = .ok (c, nv', nl', ip')) :
    nv' = nv ∧ nl' = nl ∧ (LabelClean I → NoLab I mc → NoLab I tail → NoLab I c) := by
  unfold lowerTail at hl; repeat' (split at hl <;> try (simp at hl; done))
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl, rfl, -⟩ := hl
  exact ⟨rfl, rfl, fun hcl hm ht => ((((hm.append (shuffle_clean hcl ‹_›)).append
    (canonAbiCode_clean hcl _ _)).append (restoreCs_clean hcl _ _)).append
      (fnEpilogue_clean hcl h E)).append ht⟩

end Labels

section Labels2
variable {I : Isa}

/-! ### Structural label bounds for `lowerExpr`/`lowerBlocks` -/

theorem prepend_ok {pre : List I.Directive} {r : Res I} {c : List I.Directive} {nv nl ip : Nat}
    (h : prepend pre r = .ok (c, nv, nl, ip)) : ∃ c0, r = .ok (c0, nv, nl, ip) ∧ c = pre ++ c0 := by
  cases r with
  | error e => simp [prepend] at h
  | ok q =>
    obtain ⟨c0, a, b, d⟩ := q; simp only [prepend, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨c0, rfl, rfl⟩

theorem ite_cases {α : Type} {p : Prop} [Decidable p] {a b r : α} (h : (if p then a else b) = r) :
    a = r ∨ b = r := by
  by_cases hp : p <;> simp_all

theorem finishJnz_ok {rs : List Ty} {fn : Sym} {nl : Nat} {tgt : Option Nat}
    {b : Expr VNat LNat rs} {br c₁ c₂ : List I.Directive} {nv₂ nl₂ ip₂ : Nat} {c : List I.Directive}
    {nv' nl' ip' : Nat} (h : finishJnzBranch I fn nl tgt b br c₁ c₂ nv₂ nl₂ ip₂ = .ok (c, nv', nl',
      ip')) :
    nv' = nv₂ ∧ nl' = nl₂ ∧ (c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂) :=
        by
  unfold finishJnzBranch at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, -⟩ := h; simp)

/-- `jnz` code: `br ++ c₁ ++ [label nl] ++ c₂` with `c₁`, `c₂` in disjoint ranges above `nl`. -/
theorem LabOk.jnz (hcl : LabelClean I) {fn : Sym} {nl a b d : Nat} {br c₁ c₂ : List I.Directive}
    (hbr : NoLab I br) (hab : nl < a ∧ a ≤ b ∧ b ≤ d) (h₁ : LabOk I (lrange fn (nl + 1) b) c₁)
    (h₂ : LabOk I (lrange fn b d) c₂) {c : List I.Directive}
    (hc : c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂ ∨
      c = br ++ c₂ ∨ c = br ++ c₂ ++ [I.frame.label (lname fn nl)] ++ c₁) :
    LabOk I (lrange fn nl d) c := by
  have hl : LabOk I (lrange fn nl (nl + 1)) [I.frame.label (lname fn nl)] :=
    (LabOk.single hcl _).mono fun l hl => ⟨nl, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
  have m : ∀ {x y l}, lrange fn x y l → nl ≤ x → y ≤ d → lrange fn nl d l :=
    fun h hx hy => lrange_mono h hx hy
  have three : ∀ {x y : List I.Directive} {S T : Sym → Prop}, LabOk I S x → LabOk I T y →
      (∀ l, S l → lrange fn (nl + 1) d l) → (∀ l, T l → lrange fn (nl + 1) d l) →
      (∀ l, S l → T l → False) → LabOk I (lrange fn nl d)
          (br ++ x ++ [I.frame.label (lname fn nl)] ++ y) := by
      intro x y S T hx hy hS hT hST
      refine (((hx.pre hbr).append (S := fun l => S l ∨ lrange fn nl (nl + 1) l) hl
        (fun l h1 h2 => lrange_disj (hS l h1) h2 (by omega)) (fun l h => h)).append hy
        (fun l h1 h2 => ?_) (fun l h => ?_))
      · exact h1.elim (fun h1 => hST l h1 h2) (fun h1 => lrange_disj h1 (hT l h2) (by omega))
      · rcases h with (h | h) | h
        · exact m (hS l h) (by omega) (Nat.le_refl _)
        · exact m h (Nat.le_refl _) (by omega)
        · exact m (hT l h) (by omega) (Nat.le_refl _)
  rcases hc with rfl | rfl | rfl | rfl
  · exact (h₁.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₁ h₂ (fun l h => lrange_mono h (Nat.le_refl _) (by omega))
      (fun l h => lrange_mono h (by omega) (Nat.le_refl _)) (fun l h1 h2 =>
        lrange_disj h1 h2 (by omega))
  · exact (h₂.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₂ h₁ (fun l h => lrange_mono h (by omega) (Nat.le_refl _))
      (fun l h => lrange_mono h (Nat.le_refl _) (by omega)) (fun l h1 h2 =>
        lrange_disj h1 h2 (by omega))

private theorem fuseJnzChoice_clean {I : Isa} {h : I.Hints} {fn : Sym} {nl ipT ipE : Nat}
    {rs : List Ty} {st1 : SymState I} {t e : Expr VNat LNat rs} {ft : Option Nat}
    {emit : Bool → Sym → Option (List I.Directive × FlagMask)} {fwd : Trie Nat}
    (hem : ∀ inv l c cl, emit inv l = some (c, cl) → NoLab I c)
    {inv : Bool} {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hf : fuseJnzChoice I h fn nl ipT ipE st1 t e ft emit fwd = some (inv, tgt, br, stBr)) :
    NoLab I br := by
  unfold fuseJnzChoice at hf
  obtain ⟨⟨brNl, clNl⟩, heNl, hm⟩ := Option.map_eq_some_iff.mp hf
  have hArm : ∀ {inv0 ip0} {arm0 : Expr VNat LNat rs} {j b s},
      threadFusedArm I h fn ip0 st1 (emit inv0) arm0 fwd = some (j, b, s) → NoLab I b := by
    intro inv0 ip0 arm0 j b s ha
    unfold threadFusedArm at ha
    split at ha
    · simp only [Option.bind_eq_some_iff] at ha
      obtain ⟨⟨b', c'⟩, h1, h2⟩ := ha
      split at h2
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨-, rfl, -⟩ := h2; exact hem _ _ _ _ h1
      · simp at h2
    · simp at ha
  cases hfwd : threadFusedArm I h fn ipT st1 (emit false) t fwd <;>
    cases hinv : threadFusedArm I h fn ipE st1 (emit true) e fwd
  · rw [hfwd, hinv] at hm; cases hm; exact hem _ _ _ _ heNl
  · rw [hfwd, hinv] at hm; cases hm; exact hArm hinv
  · rw [hfwd, hinv] at hm; cases hm; exact hArm hfwd
  · rw [hfwd, hinv] at hm; dsimp only at hm
    split at hm <;> cases hm
    · exact hArm hinv
    · exact hArm hfwd

private theorem jnzSetup_clean (hcl : LabelClean I) {h : I.Hints} {fn : Sym} {nl ipT ipE : Nat}
    {rs : List Ty} {st1 : SymState I} {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : JnzCond I}
    {fwd : Trie Nat} {inv : Bool} {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hj : jnzSetup I h fn nl ipT ipE st1 t e ft cond fwd = some (inv, tgt, br, stBr)) :
    NoLab I br := by
  cases cond with
  | flag cc =>
    simp only [jnzSetup, Option.some.injEq, Prod.mk.injEq] at hj
    cases hj.2.2.1; exact hcl.jcc _ _
  | gpr r =>
    dsimp only [jnzSetup] at hj
    cases hfn : I.gpr.jnzGprInv? with
    | none =>
      rw [hfn] at hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      cases hj.2.2.1; exact hcl.jnzGpr _ _
    | some jnzFn =>
      rw [hfn] at hj
      exact fuseJnzChoice_clean (fun inv l c cl he => by
        simp only [Option.some.injEq] at he
        have hc : c = (jnzFn r inv l).1 := (congrArg Prod.fst he).symm
        rw [hc]; exact hcl.jnzGprInv _ _ _ _ hfn) hj
  | slot idx =>
    simp only [jnzSetup, Option.bind_eq_some_iff] at hj
    obtain ⟨⟨_, _⟩, hjbr, hc⟩ := hj
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, -, rfl, -⟩ := hc; exact hcl.jnzMem _ _ _ _ _ hjbr
    · simp at hc
  | cmpZero co w r =>
    dsimp only [jnzSetup] at hj
    exact fuseJnzChoice_clean (fun _ _ _ _ he => hcl.cmpZeroJcc _ _ _ _ _ _ he) hj
  | cmpZeroMem co w x aa cc =>
    simp only [jnzSetup] at hj
    obtain ⟨⟨c0, cl0⟩, hcm, he⟩ := Option.map_eq_some_iff.mp hj
    simp only [finishCmpJnz, Prod.mk.injEq] at he; rw [← he.2.2.1]
    exact fun l hl => (List.mem_append.mp hl).elim
      (hcl.cmpMem _ _ _ _ _ _ _ hcm l) (hcl.jcc _ _ l)
  | cmpZeroFlag co w x r cc =>
    simp only [jnzSetup] at hj
    obtain ⟨⟨c0, cl0⟩, hop, he⟩ := Option.map_eq_some_iff.mp hj
    simp only [finishCmpJnz, Prod.mk.injEq] at he; rw [← he.2.2.1]
    exact fun l hl => (List.mem_append.mp hl).elim
      (hcl.op _ _ _ _ _ _ hop l) (hcl.jcc _ _ l)
  | testImm neg w r mask =>
    dsimp only [jnzSetup] at hj
    exact fuseJnzChoice_clean (fun _ _ _ _ he => hcl.testJcc _ _ _ _ _ _ _ he) hj

mutual
/-- `lowerExpr` is monotone in `nv`/`nl`, and (for a `LabelClean` ISA) its labels are distinct
`lname fn j` with `nl ≤ j < nl'`. -/
theorem lowerExpr_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ (e : Expr VNat LNat rs) (nv nl ip : Nat) (st : SymState I) (ft : Option Nat)
      (fwd : Trie Nat) (fwdTgts : Trie Bool) (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerExpr I h E fn e nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → LabOk I (lrange fn nl nl') c)
  | .let_ op k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerOp_clean hcl ‹_›))⟩
  | .load t a k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerLoad_clean hcl ‹_›))⟩
  | .store v a k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨h1, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerStore_clean hcl ‹_›))⟩
  | .call f args k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((((stepPre_clean hcl ‹_›).append
      (shuffle_clean hcl ‹_›)).append (canonAbiCode_clean hcl _ _)).append (hcl.call _))⟩
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    rcases ite_cases hr with hr | hr <;> obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr <;>
      exact ⟨h1, h2, fun hcl => (h3 hcl).pre (stepPre_clean hcl ‹_›)⟩
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    rename_i inv tgt br stBr hs
    split at he <;> try (simp at he; done)
    rename_i ce nv₁ nl₁ ip₁ he₁
    split at he <;> try (simp at he; done)
    rename_i ct nv₂ nl₂ ip₂ he₂
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₂
    rcases ite_cases hr with hr | hr <;> obtain ⟨rfl, rfl, hc⟩ := finishJnz_ok hr
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl (jnzSetup_clean hcl hs)
        ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl) (b3 hcl)
        (hc.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          fun h => Or.inr (Or.inr (Or.inr h)))).pre (stepPre_clean hcl ‹_›)⟩
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl (jnzSetup_clean hcl hs)
        ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl) (b3 hcl)
        (hc.elim Or.inl fun h => Or.inr (Or.inl h))).pre (stepPre_clean hcl ‹_›)⟩
  | .jump j args, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    repeat' (split at he <;> try (simp at he; done))
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      refine ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean ((((stepPre_clean hcl ‹_›).append
        (shuffle_clean hcl ‹_›))).append ?_)⟩
      first | exact NoLab.nil | exact hcl.jmp _
  | .ret vs, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun hcl => LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) hcl.ret)⟩
  | .exit f args, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl =>
      LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) (hcl.exitJmp _))⟩
  | .hlt, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr, Except.ok.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => LabOk.clean NoLab.nil⟩
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    rename_i ck nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl => (a3 hcl).append (b3 hcl a2) (fun l h1 h2 =>
      ?_) (fun l h => ?_)⟩
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h <;> exact lrange_mono h (by omega) (by omega)

/-- `lowerBlocks` analogue: block labels `lname fn j` for `lid ≤ j < lid + sig.length`, plus body
labels in `[nl, nl')`. -/
theorem lowerBlocks_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat)
      (defs : Trie DefFact) (vw : Trie SlotWidth) (ft : Option Nat)
      (fwd : Trie Nat) (fwdTgts : Trie Bool) (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft fwd fwdTgts = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → lid + sig.length ≤ nl →
      LabOk I (fun l => lrange fn lid (lid + sig.length) l ∨ lrange fn nl nl' l) c)
  | _, .nil, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => LabOk.clean NoLab.nil⟩
  | _, .cons (sig :=
      sig) b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerBlocks] at he
    cases hfw : fwd.find? lid with
    | some fwdTgt =>
      rw [hfw] at he; dsimp only at he
      split at he <;> try (simp at he; done)
      split at he <;> try (simp at he; done)
      obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ he
      refine ⟨by omega, b2, fun hcl hlid => ?_⟩
      simp only [List.length_cons] at hlid ⊢
      exact (b3 hcl (by omega)).mono fun l hl =>
        hl.imp (fun h => lrange_mono h (by omega) (by omega)) id
    | none =>
      rw [hfw] at he; dsimp only at he
      repeat' (split at he <;> try (simp at he; done))
      rename_i cb nv₁ nl₁ ip₁ he₁
      obtain ⟨c0, hr, rfl⟩ := prepend_ok he
      obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
      obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr
      refine ⟨by omega, by omega, fun hcl hlid => ?_⟩
      simp only [List.length_cons] at hlid ⊢
      have hl : LabOk I (lrange fn lid (lid + 1)) [I.frame.label (lname fn lid)] :=
        (LabOk.single hcl _).mono fun l hl => ⟨lid, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
      refine (hl.append ((a3 hcl).append (b3 hcl (by omega)) (fun l h1 h2 => ?_) (fun l h => h))
        (fun l h1 h2 => ?_) (fun l h => ?_))
      · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
      · rcases h2 with h2 | h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
      · rcases h with h | h | h | h <;> first
          | exact Or.inl (lrange_mono h (by omega) (by omega))
          | exact Or.inr (lrange_mono h (by omega) (by omega))
end

theorem lowerExpr_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {e : Expr VNat LNat rs}
    {nv nl ip : Nat} {st : SymState I} {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerExpr I h E fn e nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerExpr_labels e nv nl ip st ft fwd fwdTgts c nv' nl' ip' he; ⟨hl.1, hl.2.1⟩

theorem lowerBlocks_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {sig : List (List Ty)}
    {bs : Blocks VNat LNat rs sig} {lid nv nl ip : Nat} {defs : Trie DefFact} {vw : Trie SlotWidth}
    {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool} {c : List I.Directive}
    {nv' nl' ip' : Nat}
    (he : lowerBlocks I h E fn bs lid nv nl ip defs vw ft fwd fwdTgts = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerBlocks_labels bs lid nv nl ip defs vw ft fwd fwdTgts c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerFn_labOk {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (hf : lowerFn I hints E f = .ok code) :
    LabOk I (fun l => l = f.name ∨ ∃ j, l = lname f.name j) code := by
  unfold lowerFn at hf
  repeat' (split at hf <;> try (simp at hf; done))
  rename_i c _ _ _ he
  simp only [Except.ok.injEq] at hf; subst hf
  have h3 := (lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he).2.2 hcl
  refine (LabOk.single hcl f.name).append
    (h3.pre ((fnPrologue_clean hcl hints E).append (saveCs_clean hcl _ _)))
    (fun l h1 h2 => ?_) (fun l h => ?_)
  · obtain ⟨j, -, -, rfl⟩ := h2; exact lname_ne h1
  · exact h.imp id fun ⟨j, _, _, e⟩ => ⟨j, e⟩

/-- Labels of a lowered function are pairwise distinct (proved structurally, without `decide`). -/
theorem lowerFn_labelsUnique {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) :
    ∀ (i j : Nat) l, code[i]? = some (I.frame.label l) →
      code[j]? = some (I.frame.label l) → i = j := (lowerFn_labOk hcl h).1

theorem lowerFn_label_mem {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) {i : Nat} {l : Sym}
    (hi : code[i]? = some (I.frame.label l)) : l = f.name ∨ ∃ j, l = lname f.name j :=
  (lowerFn_labOk hcl h).2 l (List.mem_of_getElem? hi)

end Labels2

end Rega
end LeanQbe.T
