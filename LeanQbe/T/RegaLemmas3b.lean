module

public import LeanQbe.T.RegaLemmas3a
public import LeanQbe.T.RegaLemmasZero
public import LeanQbe.T.RegaLemmasRemat
public import LeanQbe.T.RegaLabClean

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
        ((T.gpr.zeroExtBoolCmp && (testBoolExtra? T.toIsa neg clob pd).isNone) = true →
          ∀ rd, pd = .gpr rd → AbiGprHolds (T.mach.getGpr s' rd) .bool res) ∧
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
          have ht := testMem_with_extra (host := host) (k := k) (post := post) htm
            (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg
            (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa
          exact ht.conseq fun s' hs _ => by
            dsimp only [Arg.val] at hs
            rwa [BitVec.and_comm vy vx] at hs
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
        ((T.gpr.zeroExtBoolCmp && (T.gpr.cmpMemFlagsOut? co pd).isNone) = true →
          ∀ rd, pd = .gpr rd → AbiGprHolds (T.mach.getGpr s' rd) .bool (co.evalBits vt ci)) ∧
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
    {flagsPost : Option FlagFact} {scrOut : List (T.Reg × BitVec 64)}
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
    (hscr : ScrOk T.mach T.frame.scratch scrOut s')
    (kont : ∀ (rvs : Tup Val [.bits 32]) s'', P rvs →
      Agree T (Tup.zip rvs (Tup.levels [.bits 32] nv) ++ G) (nv + 1)
        { regs := (.var nv, .gprZ rd) :: killRegs T.toIsa (rd :: T.frame.scratch) [] clob st.regs
          slots := st.slots
          defs := match recordDefC T.toIsa.gpr.addrCse st.defs code args with
            | some df => st.defs.insert nv df | none => st.defs
          vecWidths := st.vecWidths
          memDefs := st.memDefs
          zeroExt32 := rd :: killZeroExt (rd :: T.frame.scratch) st.zeroExt32
          flags := flagsPost
          scrConsts := scrOut } s'' σ →
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
    fun y d hy => (hd1 y d hy).2, hA2.vw_lt, hA2.vt, hA2.zeroExt32_ok, hflOk, hflLt, hscr⟩
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
    {c : List T.Directive} {clob : FlagMask} {isZ z32 : Bool}
    {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargs : TRel (ArgRel G) args₁ args) (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : trySlotOp T.toIsa hints st code args dsts = some (c, clob, isZ, z32, flPost, ex))
    (fin : z32 = false → ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (isZ = true → ∀ {t0} {ht : ts = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
          AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
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
        obtain ⟨⟨c', cl', fl', ex', iz'⟩, hs', hmp⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hmp
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hmp
        have wrap : ∀ {bval : Bool}, bval = co.evalBits a₁.val b₁.val →
            T.mach.FallsTo T.gpr.condReads host k c' (pd.gprs ++ T.frame.scratch) [] cl' s
              (fun s' => T.mach.PDstHolds s' .bool pd bval ∧
                (iz' = true → ∀ rd, pd = .gpr rd → AbiGprHolds (T.mach.getGpr s' rd) .bool bval) ∧
                FlagFactOk T G s' fl' ∧ FlagFactScope nv fl' ∧
                (∀ cc, ex' = some cc → T.mach.evalCond s' cc = bval) ∧
                T.mach.mem s' = T.mach.mem s) post →
            T.mach.Run host k s post := fun heq hft =>
          hft hc fun s' ⟨hd, hzb, hfo, hfl, hex, hms⟩ hfr =>
            fin rfl s' ⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons (heq ▸ hd) .nil,
              (fun hiz {t0} ht {rd} hrd => by
                obtain rfl : Ty.bool = t0 := (List.cons.inj ht).1
                have hpd : pd = .gpr rd := (Prod.mk.inj hrd).1
                exact heq ▸ hzb hiz rd hpd),
              fun cc hcc => ⟨rfl, _, rfl, heq ▸ hex cc hcc⟩⟩
              hfo hfl hms (by simpa [tupDstGprs] using hfr)
        rcases orElse_eq_some hs' with ht | hrest
        · split at ht
          · rename_i hco
            have hcoEq : (if co == .ne then CmpOp.ne else CmpOp.eq) = co := by
              cases co <;> simp at hco ⊢
            obtain ⟨⟨c0, cl0⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
            cases a with
            | var t =>
              cases b with
              | imm c0 =>
                dsimp only at ht'
                split at ht'
                · rename_i hc0
                  cases ha with | var hmt => cases hb with | imm =>
                  refine wrap ?_
                    ((tryTestSlot_ok hA hI hmt hdg1 ht').conseq fun s' ⟨h1, hzb, h2, h3⟩ hfr =>
                      ⟨h1, hzb, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
                  rw [hcoEq, beq_iff_eq.mp hc0]; rfl
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
                    ((tryTestSlot_ok hA hI hmt hdg1 ht').conseq fun s' ⟨h1, hzb, h2, h3⟩ hfr =>
                      ⟨h1, hzb, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
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
              rcases hmap with ⟨rfl, rfl, rfl, rfl, rfl⟩
              exact wrap rfl ((tryExtSlot_ok hA hI hmt hdg1 he').conseq
                fun s' ⟨h1, hzb, h2, h3⟩ hfr =>
                  ⟨h1, hzb, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
            | var _ => simp at he
          | imm _ =>
            cases b with
            | var t =>
              cases ha with | imm => cases hb with | var hmt =>
              obtain ⟨⟨d0, cl0⟩, he', hmap⟩ := Option.map_eq_some_iff.mp he
              simp only [Prod.mk.injEq] at hmap
              rcases hmap with ⟨rfl, rfl, rfl, rfl, rfl⟩
              exact wrap (CmpOp.swap_evalBits co _ _) ((tryExtSlot_ok hA hI hmt hdg1 he').conseq
                fun s' ⟨h1, hzb, h2, h3⟩ hfr =>
                  ⟨h1, hzb, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
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
                simp only [Prod.mk.injEq] at hmap; rcases hmap with ⟨rfl, rfl, rfl, rfl, rfl⟩
                refine wrap rfl ?_
                by_cases hz : T.gpr.zeroExtBoolCmp = true
                · cases pd with
                  | flag _ | vec _ =>
                    exact (T.gprSpec.cmpMem_spec hcm
                      (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                      (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb).conseq
                      fun s' ⟨hd, hm'⟩ hfr =>
                        ⟨hd, (fun _ _ h => by cases h), hA.flags_ok.kill hfr, hA.flags_lt.kill,
                          (fun _ h => nomatch h), hm'⟩
                  | gpr rd =>
                    have hrd : rd ∉ T.frame.scratch := hdg1 rd (by simp [PDst.gprs])
                    exact (T.gprSpec.cmpMem_zext hz hcm
                      (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hrd
                      (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb).conseq
                      fun s' ⟨hd, hm'⟩ hfr =>
                        ⟨hd.toGprHolds, (fun _ _ h => by cases h; exact hd),
                          hA.flags_ok.kill hfr, hA.flags_lt.kill, (fun _ h => nomatch h), hm'⟩
                · have hzf : T.gpr.zeroExtBoolCmp = false := Bool.eq_false_iff.mpr hz
                  exact (T.gprSpec.cmpMem_spec hcm
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb).conseq
                    fun s' ⟨hd, hm'⟩ hfr =>
                      ⟨hd, (fun hz' => by simp [hzf] at hz'), hA.flags_ok.kill hfr,
                        hA.flags_lt.kill,
                        (fun _ h => nomatch h), hm'⟩
              | some sb =>
                rw [hsb] at hmap; dsimp only at hmap
                have hsb_ok := tryArg_bits_det hA hw hb hta hsb
                have hsb_lt := symArgScopeOk_of_argRel hA.ctx_lt hb hsb
                simp only [Prod.mk.injEq] at hmap
                obtain ⟨hmap1, hmap2, hmap3, hmap4, rfl⟩ := hmap
                cases hcmo : T.gpr.cmpMemFlagsOut? co pd <;>
                  simp only [cmpMemRes, hcmo] at hmap1 hmap2 hmap3 hmap4
                · have hcmp_eq : cmpMemRes T.toIsa st co w (.var x) sb pd c' cl' =
                      (c', cl', fl', ex') := by
                    simp only [cmpMemRes, hcmo]
                    rw [← hmap1, ← hmap2]
                    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hmap3 hmap4))
                  have hsb_at := symValAt_of_toSymArg (T := T) hw hb hsb
                  exact wrap rfl (cmpMemRes_with_flags (T := T) (nv := nv) hw hA.flags_ok
                    hA.flags_lt hsx hsb_ok hmx hsb_at hsx_lt hsb_lt hcmp_eq (hmap1 ▸ hmap2 ▸ hcm)
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb)
                · have hcmp_eq : cmpMemRes T.toIsa st co w (.var x) sb pd c' cl' =
                      (c', cl', fl', ex') := by
                    simp only [cmpMemRes, hcmo]
                    rw [← hmap1, ← hmap2]
                    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hmap3 hmap4))
                  have hsb_at := symValAt_of_toSymArg (T := T) hw hb hsb
                  exact wrap rfl (cmpMemRes_with_flags (T := T) (nv := nv) hw hA.flags_ok
                    hA.flags_lt hsx hsb_ok hmx hsb_at hsx_lt hsb_lt hcmp_eq (hmap1 ▸ hmap2 ▸ hcm)
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmx)) hpb)
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
                simp only [Prod.mk.injEq] at hmap; rcases hmap with ⟨rfl, rfl, rfl, rfl, rfl⟩
                refine wrap (CmpOp.swap_evalBits co _ _) ?_
                by_cases hz : T.gpr.zeroExtBoolCmp = true
                · cases pd with
                  | flag _ | vec _ =>
                    exact (T.gprSpec.cmpMem_spec hcm
                      (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                      (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa).conseq
                      fun s' ⟨hd, hm'⟩ hfr =>
                        ⟨hd, (fun _ _ h => by cases h), hA.flags_ok.kill hfr, hA.flags_lt.kill,
                          (fun _ h => nomatch h), hm'⟩
                  | gpr rd =>
                    have hrd : rd ∉ T.frame.scratch := hdg1 rd (by simp [PDst.gprs])
                    exact (T.gprSpec.cmpMem_zext hz hcm
                      (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hrd
                      (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa).conseq
                      fun s' ⟨hd, hm'⟩ hfr =>
                        ⟨hd.toGprHolds, (fun _ _ h => by cases h; exact hd),
                          hA.flags_ok.kill hfr, hA.flags_lt.kill, (fun _ h => nomatch h), hm'⟩
                · have hzf : T.gpr.zeroExtBoolCmp = false := Bool.eq_false_iff.mpr hz
                  exact (T.gprSpec.cmpMem_spec hcm
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa).conseq
                    fun s' ⟨hd, hm'⟩ hfr =>
                      ⟨hd, (fun hz' => by simp [hzf] at hz'), hA.flags_ok.kill hfr,
                        hA.flags_lt.kill,
                        (fun _ h => nomatch h), hm'⟩
              | some sa =>
                rw [hsa] at hmap; dsimp only at hmap
                have hsa_ok := tryArg_bits_det hA hw ha hta hsa
                have hsa_lt := symArgScopeOk_of_argRel hA.ctx_lt ha hsa
                simp only [Prod.mk.injEq] at hmap
                obtain ⟨hmap1, hmap2, hmap3, hmap4, rfl⟩ := hmap
                cases hcmo : T.gpr.cmpMemFlagsOut? co.swap pd <;>
                  simp only [cmpMemRes, hcmo] at hmap1 hmap2 hmap3 hmap4
                · have hcmp_eq : cmpMemRes T.toIsa st co.swap w (.var y) sa pd c' cl' =
                      (c', cl', fl', ex') := by
                    simp only [cmpMemRes, hcmo]
                    rw [← hmap1, ← hmap2]
                    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hmap3 hmap4))
                  have hsa_at := symValAt_of_toSymArg (T := T) hw ha hsa
                  exact wrap (CmpOp.swap_evalBits co _ _) (cmpMemRes_with_flags (T := T) (nv := nv)
                    hw hA.flags_ok hA.flags_lt hsy hsa_ok hmy hsa_at hsy_lt hsa_lt hcmp_eq
                    (hmap1 ▸ hmap2 ▸ hcm)
                    (fun r hr => (List.mem_append.mp hr).elim (hsp idx r) (hpg r)) hdg1
                    (spAddr_load_bits hlt hI hstd hσ (hgpr _ _ hmy)) hpa)
                · have hcmp_eq : cmpMemRes T.toIsa st co.swap w (.var y) sa pd c' cl' =
                      (c', cl', fl', ex') := by
                    simp only [cmpMemRes, hcmo]
                    rw [← hmap1, ← hmap2]
                    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hmap3 hmap4))
                  have hsa_at := symValAt_of_toSymArg (T := T) hw ha hsa
                  exact wrap (CmpOp.swap_evalBits co _ _) (cmpMemRes_with_flags (T := T) (nv := nv)
                    hw hA.flags_ok hA.flags_lt hsy hsa_ok hmy hsa_at hsy_lt hsa_lt hcmp_eq
                    (hmap1 ▸ hmap2 ▸ hcm)
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
        rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact tryAluSlot_ok hA hI ha hb (by simpa [tupDstGprs] using hdg)
          (by simpa [vals, Arg.val] using hwp) hc halu
          (fun hzf s' ⟨rvs, hPrvs, hdl⟩ hms hfr =>
            fin hzf s' ⟨rvs, hPrvs, hdl, (fun hiz => by simp [hzf] at hiz),
              fun _ h => nomatch h⟩
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

private theorem cmpOpFlags_snd_nonbool (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts)
    (nv : Nat) (cl : FlagMask) (hts : ts ≠ [.bool]) :
    (cmpOpFlags? I st code args pas dsts nv cl).2 = none := by
  cases ts with
  | nil => cases code <;> rfl
  | cons t0 ts0 =>
    cases ts0 with
    | cons _ _ =>
      cases code with
      | unpair _ _ => cases t0 <;> (rcases dsts with ⟨_, _, ⟨⟩⟩; rfl)
      | addc _ | subb _ | umulw _ | smulw _ => rcases dsts with ⟨_, _, ⟨⟩⟩; rfl
      | _ => rcases dsts with ⟨_, _, _⟩; rfl
    | nil =>
      cases t0 with
      | bool => exact absurd rfl hts
      | float _ =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases code with
        | cmp co ty mty hmty =>
          cases ty <;> (try dsimp only [Ty.mask] at hmty) <;> cases hmty
        | _ => rfl
      | pair _ _ =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases code with
        | cmp co ty mty hmty =>
          cases ty with
          | bool | bits _ | float _ => dsimp only [Ty.mask] at hmty; cases hmty
          | pair _ _ =>
            cases hmty
            rcases args with ⟨_, _, ⟨⟩⟩; rcases pas with ⟨_, _, ⟨⟩⟩; rfl
        | _ => rfl
      | bits _ =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases code with
        | cmp co ty mty hmty =>
          cases ty <;> (try dsimp only [Ty.mask] at hmty) <;> cases hmty
        | _ => rfl

private theorem cmpOpFlags_bool_other (I : Isa) (st : SymState I) {sig : List Ty}
    (code : OpCode sig [.bool]) (args : Tup (Arg VNat) sig)
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (pd : PDst I.Reg I.VReg I.Cond .bool)
    (nv : Nat) (cl : FlagMask) (hnc : isCmpOp code = false) :
    cmpOpFlags? I st code args pas (pd, ()) nv cl =
      (killFlags I cl st.flags,
        match pd with | .gpr rd => I.gpr.boolFlagOut? code pas (.gpr rd) | _ => none) := by
  cases code
  case cmp co ty hmty =>
    cases ty with
    | bits w => simp [isCmpOp] at hnc
    | bool | float _ => cases hmty; cases pd <;> rfl
    | pair _ _ => dsimp only [Ty.mask] at hmty; cases hmty
  all_goals cases pd <;> rfl

private theorem zeroExtOpEff_bool_inv (I : Isa) {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (rd : I.Reg)
    (h : zeroExtOpEff I code pas (.gpr rd, ()) = true) :
    (I.gpr.boolFlagOut? code pas (.gpr rd)).isNone = true ∧
    ∀ {co w pa pb}, (h1 : sig = [.bits w, .bits w]) → (h2 : code = h1 ▸ .cmp co
      (.bits w) .bool rfl) →
      pas = h1 ▸ (pa, pb, ()) → I.gpr.opScr?.isSome = true ∨
        (I.gpr.cmpFlagsOut? co w pa pb (.gpr rd)).isNone = true := by
  cases code
  case cmp co ty hmty =>
    cases ty with
    | bits w =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩
      cases hmty
      change (I.gpr.zeroExtOp (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (.gpr rd, ()) &&
        ((I.gpr.opScr?.isSome || (I.gpr.cmpFlagsOut? co w pa pb (.gpr rd)).isNone) &&
         (I.gpr.boolFlagOut? (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (.gpr rd)).isNone)) =
        true at h
      simp only [Bool.and_eq_true] at h
      refine ⟨h.2.2, fun {co' w' pa' pb'} h1 h2 hp => ?_⟩
      cases h1; cases h2; cases hp
      exact (Bool.or_eq_true _ _).mp h.2.1
    | bool | float _ =>
      (try cases hmty)
      unfold zeroExtOpEff at h; (try dsimp only at h)
      exact ⟨((Bool.and_eq_true _ _).mp h).2, fun h1 _ => by cases h1⟩
    | pair _ _ => dsimp only [Ty.mask] at hmty; cases hmty
  case fcmp o t hmty =>
    cases t with
    | pair _ _ => dsimp only [Ty.mask] at hmty; cases hmty
    | bool | bits _ | float _ =>
      unfold zeroExtOpEff at h; (try dsimp only at h)
      exact ⟨((Bool.and_eq_true _ _).mp h).2, fun h1 h2 => by cases h1 <;> cases h2⟩
  case blend m hm =>
    dsimp only [Ty.mask] at hm; cases hm
    unfold zeroExtOpEff at h; dsimp only at h
    exact ⟨((Bool.and_eq_true _ _).mp h).2, fun h1 h2 => by cases h1 <;> cases h2⟩
  case bitcast t hsz =>
    cases t <;>
      · unfold zeroExtOpEff at h; (try dsimp only at h)
        exact ⟨((Bool.and_eq_true _ _).mp h).2, fun h1 h2 => by cases h1 <;> cases h2⟩
  all_goals
    unfold zeroExtOpEff at h; (try dsimp only at h)
    exact ⟨((Bool.and_eq_true _ _).mp h).2, fun h1 h2 => by cases h1 <;> cases h2⟩

private theorem zeroExtOpEff_bits_aluZeroOut_none (I : Isa) {sig : List Ty} {w : Nat}
    (code : OpCode sig [.bits w]) (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (rd : I.Reg)
    (hw : Nat.ble w 64 = true) (h : zeroExtOpEff I code pas (.gpr rd, ()) = true) :
    I.gpr.aluZeroOut? w code (.gpr rd) = none := by
  cases code
  case cmp => cases ‹Ty› <;> (try dsimp only [Ty.mask] at *) <;> cases ‹_ = Ty.mask _›
  case fcmp o t hmty =>
    cases t <;> (try dsimp only [Ty.mask] at hmty) <;> cases hmty
  case blend m hm =>
    dsimp only [Ty.mask] at hm; cases hm
    unfold zeroExtOpEff at h; dsimp only at h
    have h2 := ((Bool.and_eq_true _ _).mp h).2
    exact Option.isNone_iff_eq_none.mp (((Bool.or_eq_true _ _).mp h2).resolve_left (by simp [hw]))
  case bitcast t hsz =>
    cases t <;>
      · unfold zeroExtOpEff at h; (try dsimp only at h)
        have h2 := ((Bool.and_eq_true _ _).mp h).2
        exact Option.isNone_iff_eq_none.mp (((Bool.or_eq_true _ _).mp h2).resolve_left (by
          simp [hw]))
  all_goals
    unfold zeroExtOpEff at h; (try dsimp only at h)
    have h2 := ((Bool.and_eq_true _ _).mp h).2
    exact Option.isNone_iff_eq_none.mp (((Bool.or_eq_true _ _).mp h2).resolve_left (by simp [hw]))

private theorem gprOp_with_flags {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {pas : Tup (PArg T.Reg T.VReg T.Cond) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {scrOut : List (T.Reg × BitVec 64)}
    (hA : Agree T G nv st s σ)
    (hargs : TRel (ArgRel G) args₁ args)
    (hop' : lowerOpScr T.toIsa st vh code pas dsts = some (c, clob, scrOut))
    (hpg : ∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch)
    (hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hph : TRel (T.mach.PArgHolds s) pas (vals args₁))
    (hwp : code.wp (vals args₁) P)
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (fin : ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (zeroExtOpEff T.toIsa code pas dsts = true → ∀ {t0} {ht : ts = [t0]} {rd},
          dsts = ht ▸ (.gpr rd, ()) → AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
        (∀ cc, (cmpOpFlags? T.toIsa st code args pas dsts nv clob).2 = some cc →
          ∃ (ht : ts = [.bool]) (b : Bool), rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b) ∧
        FlagFactOk T (Tup.zip rvs (Tup.levels ts nv) ++ G) s'
          (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1 ∧
        FlagFactScope (nv + ts.length)
          (cmpOpFlags? T.toIsa st code args pas dsts nv clob).1) →
      T.mach.mem s' = T.mach.mem s →
      ScrOk T.mach T.frame.scratch scrOut s' →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have htr : ∀ (rvs : Tup Val ts) {s'} {fl : Option FlagFact},
      FlagFactOk T G s' fl → FlagFactScope nv fl →
      FlagFactOk T (Tup.zip rvs (Tup.levels ts nv) ++ G) s' fl ∧
      FlagFactScope (nv + ts.length) fl := fun rvs _ _ hfo hfl =>
    ⟨hfo.tr (fun _ hp => List.mem_append_right _ hp)
      (fun p hp => (zip_levels_mem hp).imp id (·.1)) hfl, hfl.mono (Nat.le_add_right _ _)⟩
  have hsymBits_of : ∀ {w} (hw : w ≤ 64) {a₁ : Arg Val (.bits w)} {a : Arg VNat (.bits w)}
      {sa : SymArg}, ArgRel G (.bits w) a₁ a → toSymArg T.toIsa (.bits w) a = some sa →
      SymBits G w a₁.val sa := by
    intro w hw a₁ a sa ha hsa
    cases ha with
    | var hmx =>
      simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
      exact fun _ hv => hA.ctx_uniq hv hmx
    | imm ci =>
      simp only [toSymArg] at hsa; split at hsa
      · simp only [Option.some.injEq] at hsa; subst hsa
        exact ⟨rfl, BitVec.eq_of_getLsbD_eq fun j hj => by simp [hj, show j < 64 by omega]⟩
      · cases hsa
  have ⟨Q, hwpQ, hQP, hQcmp⟩ : ∃ Q : Tup Val ts → Prop, code.wp (vals args₁) Q ∧
      (∀ r, Q r → P r) ∧
      (∀ {w : Nat} {co : CmpOp} {hm : Ty.bool = (Ty.bits w).mask}
        (h1 : sig = [.bits w, .bits w]) (h2 : ts = [.bool]),
        code = h1 ▸ h2 ▸ .cmp co (.bits w) .bool hm →
        ∀ r, Q r → ∃ a b : BitVec w, vals args₁ = h1 ▸ (a, b, ()) ∧ r = h2 ▸ (co.evalBits a b,
          ())) := by
    by_cases hts : ts = [.bool]
    · subst hts
      by_cases hcmp : isCmpOp code = true
      · cases code with
        | cmp co ty mty hmty =>
          cases ty with
          | float _ | bool | pair _ _ => simp [isCmpOp] at hcmp
          | bits w =>
            cases hmty
            exact ⟨fun r => P r ∧ r = (co.evalBits (vals args₁).1 (vals args₁).2.1, ()),
              ⟨by simpa [OpCode.wp, liftCmp, Ty.hasFloat, vals] using hwp, rfl⟩,
              fun _ hr => hr.1,
              fun h1 h2 hce r hr => by
                cases h1; cases h2; cases hce
                exact ⟨(vals args₁).1, (vals args₁).2.1, rfl, hr.2⟩⟩
        | fcmp _ t _ => cases t <;> simp [isCmpOp] at hcmp
        | _ => simp [isCmpOp] at hcmp
      · refine ⟨P, hwp, fun _ h => h, fun h1 h2 hce => ?_⟩
        cases h1; cases h2; subst hce; simp [isCmpOp] at hcmp
    · refine ⟨P, hwp, fun _ h => h, fun _ h2 => absurd h2 hts⟩
  refine lowerOpScr_ok hA hpg hdg' hph hwpQ hop' hc fun s' ⟨⟨rvs, hQ, hdl, hzExt, _, hcmpFl,
    hboolFl, haluZ⟩, hm, hscr⟩ hfr => ?_
  have hP : P rvs := hQP rvs hQ
  refine fin s' ⟨rvs, hP, hdl, ?_, ?_, ?_, ?_⟩ hm hscr hfr
  · intro hze t0 ht rd hrd
    have hze0 : T.gpr.zeroExtOp code pas dsts = true := by
      unfold zeroExtOpEff at hze; exact (Bool.and_eq_true _ _).mp hze |>.1
    refine hzExt hrd hze0 ?_ ?_ ?_
    · intro h1 hdr'
      subst ht; cases h1; dsimp only at hrd; subst hrd
      exact Option.isNone_iff_eq_none.mp (zeroExtOpEff_bool_inv T.toIsa code pas rd hze).1
    · intro w h1 hw
      subst ht; cases h1; dsimp only at hrd; subst hrd
      exact zeroExtOpEff_bits_aluZeroOut_none T.toIsa code pas rd hw hze
    · cases hox_eq : T.gpr.opScr?.isSome
      · refine Or.inr fun {co' w' pa pb pd} {h1 h2} hce hpa hpd => ?_
        subst h1; cases h2; cases hce; cases hpa; cases hpd
        cases ht; dsimp only at hrd; cases hrd
        exact ((zeroExtOpEff_bool_inv T.toIsa (.cmp co' (.bits w') .bool rfl)
          (pa, pb, ()) rd (by simpa using hze)).2 rfl rfl rfl).resolve_left
            (by simp [hox_eq])
      · exact Or.inl rfl
  · intro cc hcc
    by_cases hts : ts = [.bool]
    · subst hts
      rcases dsts with ⟨pd, ⟨⟩⟩
      by_cases hcmp : isCmpOp code = true
      · cases code with
        | cmp co ty mty hmty =>
          cases ty with
          | float _ | bool | pair _ _ => simp [isCmpOp] at hcmp
          | bits w =>
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
            rcases pas with ⟨pa, pb, ⟨⟩⟩
            cases pd with
            | flag _ | vec _ => rw [cmpOpFlags_cmp] at hcc; cases hcc
            | gpr rd =>
              rw [cmpOpFlags_cmp] at hcc
              by_cases hwb : Nat.ble w 64 = true
              · simp only [hwb, ↓reduceIte] at hcc
                cases hcmo : T.gpr.cmpFlagsOut? co w pa pb (.gpr rd) with
                | none => simp [hcmo] at hcc
                | some lf =>
                  rw [hcmo] at hcc; (try dsimp only at hcc)
                  have hco := hcmpFl (h1 := rfl) (h2 := rfl) (_he := rfl) rfl rfl hcmo
                    (if lf then co else co.swap) cc (by simp) hcc
                  obtain ⟨a', b', hab, hr_eq⟩ := hQcmp rfl rfl rfl rvs hQ
                  cases hab; rw [hco, hr_eq]; refine ⟨rfl, co.evalBits a₁.val b₁.val, rfl, ?_⟩
                  cases hph with | cons hpa hpb => cases hpb with | cons hpb _ =>
                  cases lf <;> simp [vals, CmpOp.swap_evalBits]
              · simp [hwb] at hcc
        | fcmp _ t _ => cases t <;> simp [isCmpOp] at hcmp
        | _ => simp [isCmpOp] at hcmp
      · have hnc : isCmpOp code = false := Bool.eq_false_iff.mpr hcmp
        rw [cmpOpFlags_bool_other T.toIsa st code args pas pd nv clob hnc] at hcc
        cases pd with
        | gpr rd => exact ⟨rfl, _, rfl, hboolFl (h1 := rfl) rfl hnc hcc⟩
        | flag _ | vec _ => cases hcc
    · rw [cmpOpFlags_snd_nonbool T.toIsa st code args pas dsts nv clob hts] at hcc; cases hcc
  · cases ts with
    | nil => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
    | cons t0 ts0 =>
      cases ts0 with
      | cons _ _ => cases t0 <;> exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
      | nil =>
        cases t0 with
        | float _ | pair _ _ => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
        | bits w =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          have hcmpEq : (cmpOpFlags? T.toIsa st code args pas (pd, ()) nv clob).1 =
              if Nat.ble w 64 && !(clob == FlagMask.none) then
                match T.gpr.aluZeroOut? w code pd with
                | some eqNe => some (.cmp w (.var nv) (.immBits w 0#64) eqNe)
                | none => killFlags T.toIsa clob st.flags
              else killFlags T.toIsa clob st.flags := by cases code <;> rfl
          rw [hcmpEq]; split
          · rename_i hgd
            simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq] at hgd
            have hcl : clob ≠ FlagMask.none := fun h => by subst h; simp at hgd
            cases halu : T.gpr.aluZeroOut? w code pd with
            | none => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
            | some eqNe =>
              rcases rvs with ⟨rv, ⟨⟩⟩
              refine ⟨hgd.1, rv, 0#w, List.mem_cons_self .., fun v hv => ?_,
                ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, haluZ (h1 := rfl) (Nat.ble_eq.mpr hgd.1)
                  hcl rfl halu⟩
              cases mem_cons_top hA.ctx_lt hv; rfl
          · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
        | bool =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          by_cases hcmp : isCmpOp code = true
          · cases code with
            | cmp co ty mty hmty =>
              cases ty with
              | pair _ _ => dsimp only [Ty.mask] at hmty; cases hmty
              | bool | float _ => simp [isCmpOp] at hcmp
              | bits w =>
                rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
                rcases pas with ⟨pa, pb, ⟨⟩⟩
                rw [cmpOpFlags_cmp]; dsimp only
                split
                · rename_i hwb
                  have hw : w ≤ 64 := Nat.ble_eq.mp hwb
                  cases hcmo : T.gpr.cmpFlagsOut? co w pa pb pd
                  · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                  · rename_i lf
                    cases hsa : toSymArg T.toIsa (.bits w) a
                    · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                    · rename_i sa
                      cases hsb : toSymArg T.toIsa (.bits w) b
                      · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
                      · rename_i sb
                        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
                        have hflG : FlagFactOk T G s'
                            (some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)) :=
                              by
                          have hcmp := hcmpFl (h1 := rfl) (h2 := rfl) (_he := rfl) rfl rfl hcmo
                          refine ⟨hw, if lf then a₁.val else b₁.val, if lf then b₁.val else a₁.val,
                            ?_, ?_, ?_, ?_, by cases lf <;> exact hcmp⟩
                          · cases lf <;> simp [symValAt_of_toSymArg hw ha hsa,
                              symValAt_of_toSymArg hw hb hsb]
                          · cases lf <;> simp [hsymBits_of hw ha hsa, hsymBits_of hw hb hsb]
                          · cases lf <;> simp [symValAt_of_toSymArg hw ha hsa,
                              symValAt_of_toSymArg hw hb hsb]
                          · cases lf <;> simp [hsymBits_of hw ha hsa, hsymBits_of hw hb hsb]
                        have hflSc : FlagFactScope nv
                            (some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)) :=
                              by
                          have haL := symArgScopeOk_of_argRel hA.ctx_lt ha hsa
                          have hbL := symArgScopeOk_of_argRel hA.ctx_lt hb hsb
                          refine ⟨?_, ?_⟩ <;> cases lf <;> simp [haL, hbL]
                        exact (htr rvs hflG hflSc).1
                · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
            | fcmp _ t _ => cases t <;> simp [isCmpOp] at hcmp
            | _ => simp [isCmpOp] at hcmp
          · have hnc : isCmpOp code = false := Bool.eq_false_iff.mpr hcmp
            rw [congrArg Prod.fst (cmpOpFlags_bool_other T.toIsa st code args pas pd nv clob hnc)]
            exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
  · cases ts with
    | nil => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
    | cons t0 ts0 =>
      cases ts0 with
      | cons _ _ => cases t0 <;> exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
      | nil =>
        cases t0 with
        | float _ | pair _ _ => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
        | bits w =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          have hcmpEq : (cmpOpFlags? T.toIsa st code args pas (pd, ()) nv clob).1 =
              if Nat.ble w 64 && !(clob == FlagMask.none) then
                match T.gpr.aluZeroOut? w code pd with
                | some eqNe => some (.cmp w (.var nv) (.immBits w 0#64) eqNe)
                | none => killFlags T.toIsa clob st.flags
              else killFlags T.toIsa clob st.flags := by cases code <;> rfl
          rw [hcmpEq]; split
          · cases halu : T.gpr.aluZeroOut? w code pd
            · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
            · exact ⟨by simp [symArgScopeOk], rfl⟩
          · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
        | bool =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          by_cases hcmp : isCmpOp code = true
          · cases code with
            | cmp co ty mty hmty =>
              cases ty with
              | pair _ _ => dsimp only [Ty.mask] at hmty; cases hmty
              | bool | float _ => simp [isCmpOp] at hcmp
              | bits w =>
                rcases args with ⟨a, b, ⟨⟩⟩
                rw [cmpOpFlags_cmp]; dsimp only
                split
                · cases hcmo : T.gpr.cmpFlagsOut? co w pas.1 pas.2.1 pd
                  · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                  · rename_i lf
                    cases hsa : toSymArg T.toIsa (.bits w) a with
                    | none => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                    | some sa =>
                      cases hsb : toSymArg T.toIsa (.bits w) b with
                      | none => exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
                      | some sb =>
                        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
                        have haL := symArgScopeOk_of_argRel hA.ctx_lt ha hsa
                        have hbL := symArgScopeOk_of_argRel hA.ctx_lt hb hsb
                        have hflSc : FlagFactScope nv
                            (some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)) :=
                              by
                          refine ⟨?_, ?_⟩ <;> cases lf <;> simp [haL, hbL]
                        exact hflSc.mono (Nat.le_add_right _ _)
                · exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
            | fcmp _ t _ => cases t <;> simp [isCmpOp] at hcmp
            | _ => simp [isCmpOp] at hcmp
          · have hnc : isCmpOp code = false := Bool.eq_false_iff.mpr hcmp
            rw [congrArg Prod.fst (cmpOpFlags_bool_other T.toIsa st code args pas pd nv clob hnc)]
            exact (htr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2

private theorem lowerOpBody_pickPArgs_ok {zl : Bool}
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {c' : List T.Directive} {clob : FlagMask}
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {ts sigN : List Ty} {codeN : OpCode sigN ts} {args₁N : Tup (Arg Val) sigN}
    {argsN : Tup (Arg VNat) sigN} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P' : Tup Val ts → Prop} {isVec isZ z32 : Bool} {flagsPost : Option FlagFact}
    {extraBool? : Option T.Cond} {scrOut : List (T.Reg × BitVec 64)}
    {hdef : Tup Val ts → Trie DefFact}
    (hdefOk : ∀ rvs : Tup Val ts, P' rvs →
      ∀ x d, Trie.find? (hdef rvs) x = some d → DefOk (Tup.zip rvs (Tup.levels ts nv) ++ G) x d ∧
        x < nv + ts.length)
    (hMgrow : ∀ rvs : Tup Val ts,
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargsN : TRel (ArgRel G) args₁N argsN) (hwpN : codeN.wp (vals args₁N) P')
    (hdg : ∀ r ∈ tupDstGprs dsts, isAllocGpr T.toIsa hints.saved r = true)
    (hdv : ∀ v ∈ tupDstVecs dsts,
      isAllocVec T.toIsa v = true) (hc : c'.IsInfixAt (T.mach.prog host) k)
    (hpick : pickPArgsCode T.toIsa st (tupDstFlags dsts) codeN argsN (fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((lowerOpScr T.toIsa st vh codeN pas dsts).map fun (c, cl, scr) =>
          let (fl, ex) := cmpOpFlags? T.toIsa st codeN argsN pas dsts nv cl
          let isZ := zeroExtOpEff T.toIsa codeN pas dsts
          (c, cl, false, isZ, opProducesZ32 T.toIsa codeN pas dsts, fl, ex, scr)) <|>
        ((T.vec.vop codeN pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, false, killFlags T.toIsa cl st.flags, none, []))
      else (T.vec.vop codeN pas dsts vh).map fun (c, cl) =>
        (c, cl, true, false, false, killFlags T.toIsa cl st.flags, none, [])) =
      some (c', clob, isVec, isZ, z32, flagsPost, extraBool?, scrOut))
    (fin : z32 = false → ∀ s' (vC : List T.VReg),
      (∃ rvs, P' rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (isZ = true → ∀ {t0} {ht : ts = [t0]} {rd},
          @Eq (Tup (PDst T.Reg T.VReg T.Cond) ts) dsts (ht ▸ (.gpr rd, ())) →
          AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
        (∀ cc, extraBool? = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
          rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b) ∧
        FlagFactOk T (Tup.zip rvs (Tup.levels ts nv) ++ G) s' flagsPost ∧
        FlagFactScope (nv + ts.length) flagsPost) →
      T.mach.mem s' = T.mach.mem s → ScrOk T.mach T.frame.scratch scrOut s' →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) vC clob →
      vC = (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) →
      T.mach.Run host (k + c'.length) s' post)
    (kont : ∀ (rvs : Tup Val ts) s', P' rvs →
      let killed := killRegs T.toIsa (tupDstGprs dsts ++ T.frame.scratch)
        (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) clob st.regs
      let zExt := killZeroExt (tupDstGprs dsts ++ T.frame.scratch) st.zeroExt32
      let (regsBase, vw1, zExt1) :=
        match ts, dsts with
        | [t0], (.gpr rd, ()) =>
          if isZ || z32 then
            ((SymArg.var nv, RegLoc.gprZ rd) :: killed, st.vecWidths,
              if z32 && tyEq t0 (.bits 32) then rd :: zExt else zExt)
          else
            ((bindDsts T.toIsa dsts nv (killed, st.vecWidths)).1,
              (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2, zExt)
        | _, _ =>
          ((bindDsts T.toIsa dsts nv (killed, st.vecWidths)).1,
            (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2, zExt)
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length)
        { st with
          regs := match ts, extraBool? with
            | [.bool], some cc => (SymArg.var nv, RegLoc.flag cc) :: regsBase
            | _, _ => regsBase
          defs := hdef rvs
          vecWidths := vw1
          zeroExt32 := zExt1
          flags := flagsPost
          scrConsts := scrOut } s' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c'.length) s' post) :
    T.mach.Run host k s post := by
  have hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch :=
    fun r hr => not_scratch_of_isAllocGpr hsv (hdg r hr)
  have hdv' : ∀ v ∈ tupDstVecs dsts, v ∉ T.vec.vecScratch :=
    fun v hv => not_vecScratch_of_isAllocVec (hdv v hv)
  let G' : Tup Val ts → VCtx := fun rvs => Tup.zip rvs (Tup.levels ts nv) ++ G
  have hflTr : ∀ rvs {s'} {fl : Option FlagFact},
      FlagFactOk T G s' fl → FlagFactScope nv fl →
      FlagFactOk T (G' rvs) s' fl ∧ FlagFactScope (nv + ts.length) fl := fun rvs _ _ hfo hfl =>
    ⟨hfo.tr (fun _ hp => List.mem_append_right _ hp)
      (fun p hp => (zip_levels_mem hp).imp id (·.1)) hfl, hfl.mono (Nat.le_add_right _ _)⟩
  have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
    Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
  obtain ⟨pas, hk, hpg, hpv, hph⟩ := pickPArgsCode_ok hA codeN hargsN hpick
  split at hk <;> (try rcases orElse_eq_some hk with hk | hk) <;>
    obtain ⟨⟨c'', cl, rest⟩, hop', he⟩ := Option.map_eq_some_iff.mp hk <;>
    simp only [Prod.mk.injEq] at he
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
    by_cases hz : opProducesZ32 T.toIsa codeN pas dsts = true
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
              obtain ⟨rfl, hzu, hplain⟩ := hz
              have hrd : rd ∉ T.frame.scratch := hdg' rd (by simp [tupDstGprs])
              have hrda : isAllocGpr T.toIsa hints.saved rd = true :=
                hdg rd (by simp [tupDstGprs])
              have hcmpEq : (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1 =
                  (if Nat.ble 32 64 && !(cl == FlagMask.none) then
                    match T.gpr.aluZeroOut? 32 codeN (.gpr rd) with
                    | some eqNe => some (.cmp 32 (.var nv) (.immBits 32 0#64) eqNe)
                    | none => killFlags T.toIsa cl st.flags
                  else killFlags T.toIsa cl st.flags) := by cases codeN <;> rfl
              have hflPost : (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).2 =
                  none := by cases codeN <;> rfl
              refine lowerOpScr_ok hA hpg hdg' hph hwpN hop' hc fun s' ⟨⟨rv_t, hPrv, hdh, _, hz32,
                _, _, haluZ⟩, hm, hscr⟩ hfr => ?_
              rcases rv_t with ⟨rv, ⟨⟩⟩
              have hrd_eq : T.mach.getGpr s' rd = rv.setWidth 64 := hz32 (h1 := rfl) rfl hzu hplain
              have hflPair : FlagFactOk T (G' (rv, ())) s'
                    (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1 ∧
                  FlagFactScope (nv + 1)
                    (cmpOpFlags? T.toIsa st codeN argsN pas (PDst.gpr rd, ()) nv cl).1 := by
                rw [hcmpEq]
                by_cases hflc : (!(cl == FlagMask.none)) = true
                · cases halu : T.gpr.aluZeroOut? 32 codeN (.gpr rd) with
                  | none =>
                    simpa [hflc, halu] using
                      hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill
                  | some eqNe =>
                    have hcl : cl ≠ FlagMask.none := fun h => by subst h; simp at hflc
                    have hfc := haluZ (h1 := rfl) (by decide) hcl rfl halu
                    simp only [hflc, Bool.true_and, Nat.ble]
                    refine ⟨⟨by decide, rv, 0#32, List.mem_cons_self .., fun v hv => ?_,
                      ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, hfc⟩,
                      ⟨by simp [symArgScopeOk], rfl⟩⟩
                    cases mem_cons_top hA.ctx_lt hv; rfl
                · simpa [hflc] using hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill
              have hK := hA.kill hfr
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
              have hd1 := hdefOk (rv, ()) hPrv
              have hdg1 : ∀ r ∈ [rd], isAllocGpr T.toIsa hints.saved r = true := by
                simpa using hrda
              refine kont (rv, ()) s' hPrv ?_ (hMgrow (rv, ()))
                (hI.keep hm (keep_of_frame (gs := [rd]) hfr.1 hdg1))
              have horTrue : (zeroExtOpEff T.toIsa codeN pas (PDst.gpr rd, ()) ||
                  opProducesZ32 T.toIsa codeN pas (PDst.gpr rd, ())) = true := by simp [hz_eq]
              rw [horTrue, hz_eq]
              change Agree T (Tup.zip (rv, ()) (Tup.levels [Ty.bits 32] nv) ++ G)
                (nv + [Ty.bits 32].length)
                { regs := (SymArg.var nv, RegLoc.gprZ rd) ::
                    killRegs T.toIsa (rd :: T.frame.scratch) [] cl st.regs,
                  slots := st.slots, defs := hdef (rv, ()), vecWidths := st.vecWidths,
                  memDefs := st.memDefs,
                  zeroExt32 := rd :: killZeroExt (rd :: T.frame.scratch) st.zeroExt32,
                  flags := (cmpOpFlags? T.toIsa st codeN argsN pas (.gpr rd, ()) nv cl).1,
                  scrConsts := rest } s' σ
              exact { hA2 with
                regs := by
                  simpa [Tup.zip, Tup.levels, tupDstGprs, tupFlatMap, PDst.gprs,
                    List.cons_append, List.nil_append] using hA2.regs
                regs_lt := by
                  simpa [tupDstGprs, tupFlatMap, PDst.gprs, List.cons_append, List.nil_append] using
                    hA2.regs_lt
                defs := fun y d hy => (hd1 y d hy).1
                defs_lt := fun y d hy => (hd1 y d hy).2
                zeroExt32_ok := by
                  simpa [tupDstGprs, tupFlatMap, PDst.gprs, List.cons_append, List.nil_append] using
                    hA2.zeroExt32_ok
                flags_ok := hflPair.1
                flags_lt := hflPair.2
                scrConsts_ok := hscr }
    · have hzf : opProducesZ32 T.toIsa codeN pas dsts = false := Bool.eq_false_iff.mpr hz
      have hfl? := cmpOpFlags? T.toIsa st codeN argsN pas dsts nv cl
      exact gprOp_with_flags hA hargsN hop' hpg hdg' hph hwpN hc
        fun s' ⟨rvs, hP, hdh, hze, hex, hfo, hfl⟩ hm hscr hfr =>
          fin hzf s' [] ⟨rvs, hP, hdh, hze, hex, hfo, hfl⟩ hm hscr hfr rfl
  all_goals
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
    exact T.vecSpec.vop_spec hop' hpg hpv hdg' hdv' hph hwpN hc
      fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
        fin rfl s' _ ⟨rvs, hP, hdh, (fun h => by cases h),
          (fun _ h => nomatch h),
          (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
          (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl

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
  · -- elided `zext`/`trunc`/`ofBool`/`copy`/`bitcast` into the same register: no code
    rename_i rd isZ addZ32 hel
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    have hwp0 : code.wp (vals args₁) P := hwp
    rcases ts with _ | ⟨t0, _ | _⟩
    · exact elideRegOp?_ok (code := code) hA hM hI hargs hwp0 hel
        fun rvs hP hA' hM' hI' => kont rvs s hP hA' hM' hI'
    · exact elideRegOp?_ok (code := code) hA hM hI hargs hwp0 hel
        fun rvs hP hA' hM' hI' => kont rvs s hP hA' hM' hI'
    · exact elideRegOp?_ok (code := code) hA hM hI hargs hwp0 hel
        fun rvs hP hA' hM' hI' => kont rvs s hP hA' hM' hI'
  obtain ⟨op₁N, hopN, hwpN_fn⟩ := normCmpOp_ok (T := T) hargs dsts
  have hwpN := hwpN_fn _ hwp'
  try dsimp only at hl
  generalize hOpN : normCmpOp (I := T.toIsa) { code := code, args := args } dsts = opN at hl
  rw [hOpN] at hopN
  cases hopN with
  | mk codeN hargsN =>
  rename_i sigN args₁N argsN
  obtain ⟨⟨c', clob, isVec, isZ, z32, flagsPost, extraBool?, scrOut⟩, hpick, heq⟩ :=
    Option.map_eq_some_iff.mp hl
  dsimp only at heq
  cases heq
  have fin : z32 = false → ∀ s' (vC : List T.VReg),
      (∃ rvs, (P rvs ∧ ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
        (isZ = true → ∀ {t0} {ht : ts = [t0]} {rd},
          @Eq (Tup (PDst T.Reg T.VReg T.Cond) ts) dsts (ht ▸ (.gpr rd, ())) →
          AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
        (∀ cc, extraBool? = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
          rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b) ∧
        FlagFactOk T (G' rvs) s' flagsPost ∧ FlagFactScope (nv + ts.length) flagsPost) →
      T.mach.mem s' = T.mach.mem s → ScrOk T.mach T.frame.scratch scrOut s' →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) vC clob →
      vC = (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) →
      T.mach.Run host (k + c.length) s' post := by
    rintro rfl s' vC ⟨rvs, ⟨hP, hdef⟩, hdh, hiz, hex, hflOk, hflLt⟩ hm hscr hfr rfl
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
    let killed := killRegs T.toIsa (tupDstGprs dsts ++ T.frame.scratch)
      (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) clob st.regs
    let zExt := killZeroExt (tupDstGprs dsts ++ T.frame.scratch) st.zeroExt32
    let rvw :=
      match ts, dsts with
      | [t0], (.gpr rd, ()) =>
        if isZ || false then
          ((SymArg.var nv, RegLoc.gprZ rd) :: killed, st.vecWidths,
            if false && tyEq t0 (.bits 32) then rd :: zExt else zExt)
        else
          ((bindDsts T.toIsa dsts nv (killed, st.vecWidths)).1,
            (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2, zExt)
      | _, _ =>
        ((bindDsts T.toIsa dsts nv (killed, st.vecWidths)).1,
          (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2, zExt)
    have hregsBase :
        (∀ p ∈ rvw.1, RegLocOk T.mach (G' rvs) s' p.1 p.2 ∧ symArgScopeOk (nv + ts.length)
          p.1 = true) ∧
        rvw.2.1 = (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2 := by
      cases ts with
      | nil => exact ⟨hr1, rfl⟩
      | cons t0 ts0 =>
        cases ts0 with
        | cons _ _ => exact ⟨hr1, rfl⟩
        | nil =>
          cases dsts with
          | mk d0 rest =>
            cases rest; cases d0 with
            | flag _ | vec _ => exact ⟨hr1, rfl⟩
            | gpr rd =>
              by_cases hiz_t : isZ = true
              · simp only [rvw, hiz_t, Bool.true_or, ↓reduceIte]
                refine ⟨fun p hp => ?_, rfl⟩
                rcases List.mem_cons.mp hp with rfl | hp'
                · rcases rvs with ⟨rv, ⟨⟩⟩
                  refine ⟨⟨fun t' v' hm' => ?_, fun t' v' hm' => ?_⟩, ?_⟩
                  · have htp := hGtop t' v' nv hm' (Nat.le_refl _)
                    simp only [Tup.zip, Tup.levels, List.mem_singleton] at htp
                    cases htp; cases hdh with | cons hd0 _ => exact hd0
                  · have htp := hGtop t' v' nv hm' (Nat.le_refl _)
                    simp only [Tup.zip, Tup.levels, List.mem_singleton] at htp
                    cases htp; exact hiz hiz_t (ht := rfl) rfl
                  · simp [symArgScopeOk, Nat.ble_eq]
                · exact ⟨hA1.regs p hp', hA1.regs_lt p hp'⟩
              · have hiz_f : isZ = false := Bool.eq_false_iff.mpr hiz_t
                simp only [rvw, hiz_f, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
                exact ⟨hr1, trivial⟩
    have hvwEq : ∀ r ∈ rvw.2.2,
        T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64 := by
      intro r hr
      have hzk0 : r ∈ zExt := by
        rcases ts with _ | ⟨t0, _ | _⟩
        · exact hr
        · rcases dsts with ⟨d0, ⟨⟩⟩
          cases d0 with
          | flag _ | vec _ => exact hr
          | gpr rd =>
            by_cases hiz_t : isZ = true
            · simpa only [rvw, hiz_t, Bool.true_or, Bool.false_and, Bool.false_eq_true,
                ↓reduceIte] using hr
            · simpa only [rvw, hiz_t, Bool.false_or, Bool.false_eq_true, ↓reduceIte] using hr
        · exact hr
      exact zeroExt32_frame hA hfr r hzk0
    have hinv := hI.keep hm (keep_of_frame hfr.1 hdg)
    refine kont rvs s' hP ?_ (hMgrow rvs) hinv
    have mkAgree : ∀ (regs1 : List (SymArg × RegLoc T.Reg T.VReg T.Cond))
        (vw1 : Trie SlotWidth) (zExt1 : List T.Reg),
        (∀ p ∈ regs1, RegLocOk T.mach (Tup.zip rvs (Tup.levels ts nv) ++ G) s' p.1 p.2 ∧
          symArgScopeOk (nv + ts.length) p.1 = true) →
        vw1 = (bindDsts T.toIsa dsts nv (killed, st.vecWidths)).2 →
        (∀ r ∈ zExt1, T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64) →
        Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length)
          { regs := regs1, slots := st.slots,
            defs := match recordDefC T.toIsa.gpr.addrCse st.defs code args with
              | some df => st.defs.insert nv df | none => st.defs,
            vecWidths := vw1, memDefs := st.memDefs, zeroExt32 := zExt1,
            flags := flagsPost, scrConsts := scrOut } s' σ := fun regs1 vw1 zExt1 hr hv hz =>
      ⟨hA1.ctx_lt, hA1.ctx_uniq, fun p hp => (hr p hp).1, hA1.slots,
        fun x d hx => (hd1 x d hx).1, by rw [hv]; exact hA1.vw,
        fun p hp => (hr p hp).2, hA1.slots_lt, fun x d hx => (hd1 x d hx).2,
        by rw [hv]; exact hA1.vw_lt, by rw [hv]; exact hA1.vt, hz, hflOk, hflLt, hscr⟩
    cases hex_eq : extraBool? with
    | none =>
      rcases ts with _ | ⟨t0, _ | _⟩
      · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
        exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
      · rcases dsts with ⟨d0, ⟨⟩⟩; cases d0 <;> (try cases t0) <;>
          · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
            exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
      · cases t0 <;>
          · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
            exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
    | some cc =>
      cases ts with
      | nil =>
        dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
        exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
      | cons t0 ts0 =>
        cases ts0 with
        | cons _ _ =>
          cases t0 <;>
            · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
              exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
        | nil =>
          cases t0 with
          | bits _ | float _ | pair _ _ =>
            rcases dsts with ⟨d0, ⟨⟩⟩; cases d0 <;>
              · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
                exact mkAgree _ _ _ hregsBase.1 hregsBase.2 hvwEq
          | bool =>
            obtain ⟨ht, b, rfl, heval⟩ := hex cc hex_eq
            rcases dsts with ⟨d0, ⟨⟩⟩
            cases d0 <;>
              · dsimp only [G', rvw, killed, zExt] at hregsBase hvwEq ⊢
                refine mkAgree _ _ _ ?_ hregsBase.2 hvwEq
                intro p hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · refine ⟨fun t' v' hm' => ?_, by simp [symArgScopeOk]⟩
                  have htp := hGtop t' v' nv hm' (Nat.le_refl _)
                  simp only [Tup.zip, Tup.levels, List.mem_singleton] at htp
                  cases htp; exact heval.symm
                · exact hregsBase.1 p hp'
  have hflTr : ∀ rvs {s'} {fl : Option FlagFact},
      FlagFactOk T G s' fl → FlagFactScope nv fl →
      FlagFactOk T (G' rvs) s' fl ∧ FlagFactScope (nv + ts.length) fl := fun rvs _ _ hfo hfl =>
    ⟨hfo.tr (fun _ hp => List.mem_append_right _ hp)
      (fun p hp => (zip_levels_mem hp).imp id (·.1)) hfl, hfl.mono (Nat.le_add_right _ _)⟩
  rcases orElse_eq_some hpick with hreuse | hpick
  · obtain ⟨⟨c'', cl, fl, ex, iz, scr⟩, hr, he⟩ := Option.map_eq_some_iff.mp hreuse
    cases he
    rcases orElse_eq_some hr with hr1 | hr2
    · refine tryReuseFlagCmp_ok hA hargs hdg' hwp' hr1 hc
        fun s' ⟨⟨rvs, hP, hdh, hiz, hex⟩, hfo, hfl, hm, hscr⟩ hfr =>
          fin rfl s' [] ⟨rvs, hP, hdh, hiz, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩
            hm hscr hfr rfl
    · refine tryReuseFlagCmp_ok hA hargsN hdg' hwpN hr2 hc
        fun s' ⟨⟨rvs, hP, hdh, hiz, hex⟩, hfo, hfl, hm, hscr⟩ hfr =>
          fin rfl s' [] ⟨rvs, hP, hdh, hiz, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩
            hm hscr hfr rfl
  rcases orElse_eq_some hpick with hfuse | hpick
  · obtain ⟨⟨c'', cl, fl, ex, iz⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse
    cases he
    refine tryFuseCmp_ok hA hI hM hargsN hdg' hwpN hfc hc
      fun s' ⟨⟨rvs, hP, hdh, hiz, hex⟩, hfo, hfl, hm⟩ hfr =>
        fin rfl s' [] ⟨rvs, hP, hdh, hiz, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩
          hm (scrOk_nil _ _ _) hfr rfl
  rcases orElse_eq_some hpick with hlx | hpick
  · obtain ⟨⟨c'', cl⟩, hls, he⟩ := Option.map_eq_some_iff.mp hlx
    cases he
    refine tryLoadSext_ok hA hI hM hargsN hdg' hwpN hls hc fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun h => by cases h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl
  rcases orElse_eq_some hpick with hlt | hpick
  · obtain ⟨⟨c'', cl, iz, z'', scr⟩, hlt', he⟩ := Option.map_eq_some_iff.mp hlt
    cases he
    by_cases hz : z'' = true
    · refine tryLoadTrunc_ok hA hI hM hargsN hdg' hwpN hlt' hc
        fun s' ⟨⟨rvs, hP, _, _, hzu⟩, hm, hscr⟩ hfr => ?_
      obtain ⟨ht32, rd', hdr', hrd_eq⟩ := hzu hz
      subst ht32; dsimp only at hdr'; subst hdr'
      rcases rvs with ⟨rv, ⟨⟩⟩; dsimp only at hrd_eq hP
      have hrda : isAllocGpr T.toIsa hints.saved rd' = true := hdg rd' (by simp [tupDstGprs])
      refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hP.2
        (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
        (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
        hP.1 hrd_eq hm hfr hrda hscr fun rvs s'' hP'' hA'' hM'' hI'' => ?_
      refine kont rvs s'' hP'' ?_ hM'' hI''
      dsimp only [tupDstGprs, tupFlatMap, PDst.gprs] at hA'' ⊢
      simp only [hz, Bool.or_true, ↓reduceIte, Bool.true_and, tyEq]
      exact hA''
    · have hzf : z'' = false := Bool.eq_false_iff.mpr hz
      refine tryLoadTrunc_ok hA hI hM hargsN hdg' hwpN hlt' hc
        fun s' ⟨⟨rvs, hP, hdh, hiz, _⟩, hm, hscr⟩ hfr =>
          fin hzf s' [] ⟨rvs, hP, hdh,
            (fun hiz_t {t0} {ht} {rd} hdr => by
              obtain ⟨t0', ht', rd', hdr', hab⟩ := hiz hiz_t
              cases ht; cases ht'; dsimp only at hdr hdr'
              have hpr : rd' = rd := by cases hdr.symm.trans hdr'; rfl
              subst hpr; exact hab),
            (fun _ h => nomatch h),
            (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
            (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm hscr hfr rfl
  rcases orElse_eq_some hpick with hlea | hpick
  · obtain ⟨⟨c'', cl, z''⟩, htl, he⟩ := Option.map_eq_some_iff.mp hlea
    cases he
    refine tryLeaArith_ok hA hI hargsN hdg' hwpN hc htl
      (fun hz s' ⟨rvs, hP, hdh⟩ hm hfr => fin hz s' [] ⟨rvs, hP, hdh,
        (fun h => by cases hz.symm.trans h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true := hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
      hP hrd_eq hm hfr hrda (scrOk_nil _ _ _) fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]; dsimp only [tupDstGprs, tupFlatMap, PDst.gprs, tyEq]; exact hA''
  rcases orElse_eq_some hpick with hzero | hpick
  · obtain ⟨⟨c'', cl, z''⟩, htz, he⟩ := Option.map_eq_some_iff.mp hzero
    cases he
    refine tryMoviZero_ok hargsN hwpN hc htz
      (fun hz s' ⟨rvs, hP, hdh⟩ hm hfr => fin hz s' [] ⟨rvs, hP, hdh,
        (fun h => by cases hz.symm.trans h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true := hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).1
      (hflTr (rv, ()) (hA.flags_ok.kill hfr) hA.flags_lt.kill).2
      hP hrd_eq hm hfr hrda (scrOk_nil _ _ _) fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]; dsimp only [tupDstGprs, tupFlatMap, PDst.gprs, tyEq]; exact hA''
  rcases orElse_eq_some hpick with hpick' | hpick
  · refine lowerOpBody_pickPArgs_ok hsv (hdef := fun _ =>
        match recordDefC T.toIsa.gpr.addrCse st.defs code args with
        | some df => st.defs.insert nv df | none => st.defs)
      (fun rvs ⟨_, hdef⟩ x d hx => by
        split at hx
        · rw [Trie.find?_insert] at hx; split at hx
          · cases hx; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_add_of_pos_right (hdef _ ‹_›).1⟩
          · exact ⟨DefOk.grow (fun p hp => (zip_levels_mem hp).imp id (·.1))
              (fun _ hp => List.mem_append_right _ hp) (hA.defs_lt x d hx) (hA.defs x d hx),
              Nat.lt_of_lt_of_le (hA.defs_lt x d hx) (Nat.le_add_right _ _)⟩
        · exact ⟨DefOk.grow (fun p hp => (zip_levels_mem hp).imp id (·.1))
            (fun _ hp => List.mem_append_right _ hp) (hA.defs_lt x d hx) (hA.defs x d hx),
            Nat.lt_of_lt_of_le (hA.defs_lt x d hx) (Nat.le_add_right _ _)⟩)
      hMgrow hA hI hargsN hwpN hdg hdv hc hpick'
      (fun hz s' vC hQ hm hscr hfr hvC => fin hz s' vC hQ hm hscr hfr hvC)
      fun rvs s' ⟨hP, _⟩ hA' hM' hI' => by
        refine kont rvs s' hP ?_ hM' hI'
        rcases ts with _ | ⟨t0, _ | _⟩
        · cases extraBool? <;> dsimp only at hA' ⊢ <;> exact hA'
        · cases t0 <;> rcases dsts with ⟨d0, ⟨⟩⟩ <;> cases d0 <;> cases extraBool? <;>
            dsimp only at hA' ⊢ <;> exact hA'
        · cases t0 <;> cases extraBool? <;> dsimp only at hA' ⊢ <;> exact hA'
  rcases orElse_eq_some hpick with hremD | hpick
  · obtain ⟨⟨c'', cl⟩, hrd, he⟩ := Option.map_eq_some_iff.mp hremD; cases he
    refine tryRematDirect_ok hA hargs hdg' hwp' hc hrd fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun h => by cases h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl
  rcases orElse_eq_some hpick with hremC | hpick
  · obtain ⟨⟨c'', cl⟩, hrc, he⟩ := Option.map_eq_some_iff.mp hremC; cases he
    refine tryRematCmpEqImm_ok hA hargsN hdg' hwpN hc hrc fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun h => by cases h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl
  rcases orElse_eq_some hpick with hremA | hslot
  · obtain ⟨⟨c'', cl⟩, hra, he⟩ := Option.map_eq_some_iff.mp hremA; cases he
    refine tryRematAdd64SameDst_ok hA hargsN hdg' hwpN hc hra fun s' ⟨⟨rvs, hP, hdh⟩, hm⟩ hfr =>
      fin rfl s' [] ⟨rvs, hP, hdh, (fun h => by cases h), (fun _ h => nomatch h),
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).1,
        (hflTr rvs (hA.flags_ok.kill hfr) hA.flags_lt.kill).2⟩ hm (scrOk_nil _ _ _) hfr rfl
  · obtain ⟨⟨c'', cl, iz, z'', fl, ex⟩, hsl, he⟩ := Option.map_eq_some_iff.mp hslot
    cases he
    refine trySlotOp_ok hA hI hargsN hdg' hwpN hc hsl
      (fun hz s' ⟨rvs, hP, hdh, hiz, hex⟩ hfo hfl hm hfr =>
        fin hz s' [] ⟨rvs, hP, hdh, hiz, hex, (hflTr rvs hfo hfl).1, (hflTr rvs hfo hfl).2⟩
          hm (scrOk_nil _ _ _) hfr rfl)
      (fun hz {rd} ht hd s' rv ⟨hP, hdef⟩ hrd_eq hfo hfl hm hfr => ?_)
    subst ht; dsimp only at hd; subst hd
    have hrda : isAllocGpr T.toIsa hints.saved rd = true := hdg rd (by simp [tupDstGprs])
    refine lowerOp_z32_finish hA hI (hMgrow (rv, ())) hdef
      (hflTr (rv, ()) hfo hfl).1 (hflTr (rv, ()) hfo hfl).2
      hP hrd_eq hm hfr hrda (scrOk_nil _ _ _) fun rvs s'' hP'' hA'' hM'' hI'' => ?_
    refine kont rvs s'' hP'' ?_ hM'' hI''
    dsimp only; rw [hz]
    simp only [Bool.or_true, Bool.true_and, tyEq, ↓reduceIte, tupDstGprs, tupFlatMap, PDst.gprs,
      List.cons_append, List.nil_append]
    exact hA''

theorem lowerOp_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {ts : List Ty} {op₁ : Op Val ts} {op : Op VNat ts}
    {deferFuse : Bool} {mulHiOk : Bool}
    (hop : OpRel G op₁ op) (hl : lowerOp T.toIsa hints nv ip st op deferFuse mulHiOk = some (c,
      st'))
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
  rcases orElse_eq_some hl with hmul | hl
  · split at hmul
    · cases hop with | mk code hargs =>
      obtain ⟨⟨c0, cl0, dhi⟩, hm, he⟩ := Option.map_eq_some_iff.mp hmul
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      exact tryMulHi_ok hsv hA hM hI hargs hwp hm hc kont
    · simp at hmul
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

end Rega
end LeanQbe.T
