module

public import LeanQbe.T.RegaLemmas3a
public import LeanQbe.T.RegaW62Lemmas

/-!
# Soundness for Wave 6.2-B `trySelectNeg` (`CSNEG`) & `ccmpPickStep` (`CCMP`/`CCMN`)

* `trySelectNeg_ok`: verifies dynamic `select (.bits w) c x (-x)` / `select (.bits w) c (-x) x`
  lowering via `GprTarget.selectNeg_spec`, `DefOk (.negVar w x)`, and `zeroUpper32SelectNeg`.
* `ccmpPickStep_ok`: verifies one `CCMP`/`CCMN` (`isOr := true`) step at `[32, 64]` (via
  `tryArg_ok`) or `< 32` unsigned/eq (via `widenZextArg32_ok` + `cmpOp_evalBits_zeroExtend_both`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}

private theorem asNegOf_ok {G : VCtx} {nv w : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} (hA : Agree T G nv st s σ)
    {a₁ : Arg Val (.bits w)} {a : Arg VNat (.bits w)} {x : Nat} {isNeg : Bool}
    (hrel : ArgRel G (.bits w) a₁ a)
    (h : asNegOf? st.defs w a = some (x, isNeg)) :
    ∃ vx : BitVec w, ⟨.bits w, vx, x⟩ ∈ G ∧ a₁.val = (if isNeg then -vx else vx) := by
  cases hrel with
  | imm _ => simp [asNegOf?] at h
  | var hm =>
    rename_i v
    simp only [asNegOf?] at h
    cases hd : st.defs.find? v with
    | none =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; exact ⟨_, hm, rfl⟩
    | some df =>
      cases df with
      | negVar w' ax =>
        simp only [hd] at h
        split at h
        · rename_i heq
          obtain rfl := Nat.beq_eq.mp heq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact (hA.defs v _ hd).2 _ hm
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩; exact ⟨_, hm, rfl⟩
      | _ =>
        simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; exact ⟨_, hm, rfl⟩

private theorem findGprFor_var_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} (hA : Agree T G nv st s σ)
    {t : Ty} {v : Val t} {x : Nat} {rx : T.Reg}
    (hm : ⟨t, v, x⟩ ∈ G) (hg : findGprFor T.toIsa true st.regs (.var x) = some rx) :
    rx ∉ T.frame.scratch ∧ GprHolds (T.mach.getGpr s rx) t v := by
  unfold findGprFor at hg
  obtain ⟨⟨sa, rl⟩, hp, he⟩ := List.exists_of_findSome?_eq_some hg
  cases rl with
  | gpr _ =>
    simp only at he; split at he
    · rename_i hc
      cases he
      simp only [Bool.and_eq_true] at hc
      have hns : rx ∉ T.frame.scratch := fun hmem => by
        have ht : T.frame.scratch.contains rx = true := List.elem_eq_true_of_mem hmem
        rw [ht] at hc; cases hc.1
      have hsa : sa = .var x := by
        have hm' : symArgMatchesGpr sa (.var x) = true := hc.2
        unfold symArgMatchesGpr at hm'
        split at hm'
        · cases sa <;> simp_all [symArgEq]
        · cases sa <;> simp_all
      subst hsa
      have h1 := hA.regs _ hp
      exact ⟨hns, by first | exact h1 t v hm | exact h1.1 t v hm⟩
    · cases he
  | gprZ _ =>
    simp only at he; split at he
    · rename_i hc
      cases he
      simp only [Bool.and_eq_true] at hc
      have hns : rx ∉ T.frame.scratch := fun hmem => by
        have ht : T.frame.scratch.contains rx = true := List.elem_eq_true_of_mem hmem
        rw [ht] at hc; cases hc.1
      have hsa : sa = .var x := by
        have hm' : symArgMatchesGpr sa (.var x) = true := hc.2
        unfold symArgMatchesGpr at hm'
        split at hm'
        · cases sa <;> simp_all [symArgEq]
        · cases sa <;> simp_all
      subst hsa
      have h1 := hA.regs _ hp
      exact ⟨hns, by first | exact h1 t v hm | exact h1.1 t v hm⟩
    · cases he
  | _ => simp at he

theorem trySelectNeg_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {sig ts : List Ty}
    {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {z32 : Bool}
    (hA : Agree T G nv st s σ) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hinf : c.IsInfixAt (T.mach.prog host) k)
    (h : trySelectNeg T.toIsa st code args dsts = some (c, clob, z32))
    (fin : z32 = false → ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post)
    (fin32 : z32 = true → ∀ {rd} (ht : ts = [.bits 32]),
      dsts = (ht ▸ (PDst.gpr rd, ())) → ∀ s' (rv : BitVec 32), P (ht ▸ (rv, ())) →
      T.mach.getGpr s' rd = rv.setWidth 64 → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  unfold trySelectNeg at h
  cases hsn : T.gpr.selectNeg? with
  | none => simp [hsn] at h
  | some selNegFn =>
    rw [hsn] at h
    cases code with
    | select t =>
      cases t with
      | bits w =>
        rcases args with ⟨ca, aa, ba, ⟨⟩⟩
        rcases args₁ with ⟨ca₁, aa₁, ba₁, ⟨⟩⟩
        rcases dsts with ⟨d0, ⟨⟩⟩
        cases d0 with
        | vec _ => dsimp only at h; cases h
        | gpr rd =>
          dsimp only at h
          split at h; · simp at h
          rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, -⟩⟩⟩
          obtain ⟨⟨x, negFirst⟩, hpair, h⟩ := Option.bind_eq_some_iff.mp h
          have hpairOk : ∃ vx : BitVec w, ⟨.bits w, vx, x⟩ ∈ G ∧
              aa₁.val = (if negFirst then -vx else vx) ∧
              ba₁.val = (if negFirst then vx else -vx) := by
            cases haN : asNegOf? st.defs w aa <;> cases hbN : asNegOf? st.defs w ba <;>
              simp [haN, hbN] at hpair
            rename_i pa pb
            rcases pa with ⟨xa, na⟩; rcases pb with ⟨xb, nb⟩
            cases na <;> cases nb <;> dsimp only at hpair
            · cases hpair
            · split at hpair
              · rename_i heq
                subst heq
                cases hpair
                obtain ⟨va, hma, hva⟩ := asNegOf_ok hA ha haN
                obtain ⟨vb, hmb, hvb⟩ := asNegOf_ok hA hb hbN
                have hbv := hA.ctx_uniq hma hmb
                subst hbv
                exact ⟨va, hma, by simpa using hva, by simpa using hvb⟩
              · cases hpair
            · split at hpair
              · rename_i heq
                subst heq
                cases hpair
                obtain ⟨va, hma, hva⟩ := asNegOf_ok hA ha haN
                obtain ⟨vb, hmb, hvb⟩ := asNegOf_ok hA hb hbN
                have hbv := hA.ctx_uniq hma hmb
                subst hbv
                exact ⟨va, hma, by simpa using hva, by simpa using hvb⟩
              · cases hpair
            · cases hpair
          obtain ⟨vx, hmx, haEq, hbEq⟩ := hpairOk
          obtain ⟨rx, hrx, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨pc, hsel, hregc, _, hpc⟩ := tryArg_ok hA hc h
          obtain ⟨⟨c0, cl0⟩, hfn, hex⟩ := Option.map_eq_some_iff.mp hsel
          simp only [Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          have ⟨hrxNS, hrxH⟩ := findGprFor_var_ok hA hmx hrx
          have hrdNS : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs, tupFlatMap, PDst.gprs])
          simp only [OpCode.wp_select, vals] at hwp
          rw [haEq, hbEq] at hwp
          refine T.gprSpec.selectNeg_spec hsn hfn hregc hrxNS hrdNS hpc hrxH hinf
            fun s' ⟨hrd, hz32, hm⟩ hfr => ?_
          by_cases hz : (Nat.beq w 32 && T.toIsa.gpr.zeroUpper32SelectNeg) = true
          · have hzb := hz
            simp only [Bool.and_eq_true] at hzb
            obtain ⟨hw32, hzu⟩ := hzb
            obtain rfl := Nat.beq_eq.mp hw32
            exact fin32 hz rfl rfl s' _ hwp (hz32 rfl hzu) hm hfr
          · have hzf : (Nat.beq w 32 && T.toIsa.gpr.zeroUpper32SelectNeg) = false :=
              Bool.eq_false_iff.mpr hz
            exact fin hzf s' ⟨(_, ()), hwp, .cons hrd .nil⟩ hm
              (by simpa [tupDstGprs, tupFlatMap, PDst.gprs] using hfr)
      | _ => dsimp only at h; cases h
    | _ => dsimp only at h; cases h

theorem ccmpPickStep_ok {G : VCtx} {nv k w : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {prevCond dstCond : T.Cond} {co : CmpOp}
    {a₁ b₁ : Arg Val (.bits w)} {a b : Arg VNat (.bits w)}
    {c : List T.Directive} {clob : FlagMask} {isNonCb : Bool}
    (hA : Agree T G nv st s σ)
    (ha : ArgRel G (.bits w) a₁ a) (hb : ArgRel G (.bits w) b₁ b)
    (hinf : c.IsInfixAt (T.mach.prog host) k)
    (h : ccmpPickStep T.toIsa st prevCond co a b = some (dstCond, c, clob, isNonCb))
    (kont : ∀ s',
      T.mach.evalCond s' dstCond = (T.mach.evalCond s prevCond || co.evalBits a₁.val b₁.val) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' T.frame.scratch [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  unfold ccmpPickStep at h
  obtain ⟨ccmpFn, hccmp, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · obtain ⟨pa, hb', hra, _, hpa⟩ := tryArg_ok hA ha h
    obtain ⟨pb, hm', hrb, _, hpb⟩ := tryArg_ok hA hb hb'
    obtain ⟨⟨d0, c0, cl0⟩, hfn, hex⟩ := Option.map_eq_some_iff.mp hm'
    simp only [Prod.mk.injEq] at hex
    rcases hex with ⟨rfl, rfl, rfl, rfl⟩
    have hreg : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch :=
      fun r hr => (List.mem_append.mp hr).elim (hra r) (hrb r)
    exact T.gprSpec.ccmp_spec hccmp hfn hreg hpa hpb hinf fun s' ⟨hev, hm⟩ hfr =>
      kont s' (by simpa using hev) hm hfr
  · split at h
    · rename_i hlt
      simp only [Bool.and_eq_true, Nat.blt_eq] at hlt
      obtain ⟨pa, hpa, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨pb, hpb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨d0, c0, cl0⟩, hfn, hex⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hex
      rcases hex with ⟨rfl, rfl, rfl, rfl⟩
      have ⟨hra, hpaH⟩ := widenZextArg32_ok hlt.1 hA ha hpa
      have ⟨hrb, hpbH⟩ := widenZextArg32_ok hlt.1 hA hb hpb
      have hreg : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch :=
        fun r hr => (List.mem_append.mp hr).elim (hra r) (hrb r)
      have hevEq := cmpOp_evalBits_zeroExtend_both hlt.1 hlt.2 a₁.val b₁.val
      exact T.gprSpec.ccmp_spec hccmp hfn hreg hpaH hpbH hinf fun s' ⟨hev, hm⟩ hfr =>
        kont s' (by rw [← hevEq]; simpa using hev) hm hfr
    · simp at h

theorem Agree_ccmpKill {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s s' : T.mach.MData}
    {σ : List (BitVec 64)} {cl : FlagMask} (hA : Agree T G nv st s σ)
    (hfr : T.mach.Frame T.gpr.condReads s s' T.frame.scratch [] cl) :
    Agree T G nv (ccmpKillState T.toIsa st cl) s' σ :=
  have hk := hA.kill hfr
  { hk with flags_ok := trivial, flags_lt := trivial }

theorem Agree_ccmpKill_frameNone {G : VCtx} {nv : Nat} {st st' : SymState T.toIsa}
    {s s' : T.mach.MData} {σ : List (BitVec 64)} {cl : FlagMask}
    (hst : st' = ccmpKillState T.toIsa st cl) (hA : Agree T G nv st' s σ)
    (hfr : T.mach.Frame T.gpr.condReads s s' T.frame.scratch [] FlagMask.none) :
    Agree T G nv st' s' σ := by
  subst hst
  refine { hA with
    regs := fun p hp => keepRegLoc_frame hfr ?_ (hA.regs p hp)
    zeroExt32_ok := fun r hr => ?_
    flags_ok := trivial
    scrConsts_ok := scrOk_nil _ _ _ }
  · simp only [ccmpKillState, killRegs, List.mem_filter] at hp
    have hkp := hp.2
    cases hrl : p.2 with
    | gpr r => simpa [keepRegLoc, hrl] using hkp
    | gprZ r => simpa [keepRegLoc, hrl] using hkp
    | vec _ => simp [keepRegLoc]
    | flag c => simp [keepRegLoc, FlagMask.disjoint_none]
  · simp only [ccmpKillState, killZeroExt, List.mem_filter, Bool.not_eq_true'] at hr
    have hns : r ∉ T.frame.scratch := fun hm => by
      have ht : T.frame.scratch.contains r = true := List.elem_eq_true_of_mem hm
      rw [ht] at hr; cases hr.2
    rw [hfr.1 r hns]
    exact hA.zeroExt32_ok r (by
      simp only [ccmpKillState, killZeroExt, List.mem_filter, Bool.not_eq_true']
      exact hr)

theorem Agree_push_bool {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (v : Bool) :
    Agree T (⟨.bool, v, nv⟩ :: G) (nv + 1) st s σ :=
  hA.push .bool v st.vecWidths (fun _ _ => rfl)
    (fun w hw => absurd (hA.vw_lt nv w hw) (Nat.not_lt.mpr (Nat.le_refl _)))
    (fun x hx => match hf : st.vecWidths.find? x with
      | none => rfl
      | some w => absurd (hA.vw_lt x w hf) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
    (fun _ _ _ he => by cases he)

end Lemmas

theorem opRel_ccmpAsCmp {G : VCtx} {op₁ : Op Val [.bool]} {op₂ : Op VNat [.bool]}
    (hop : OpRel G op₁ op₂) {w : Nat} {co : CmpOp} {a₂ b₂ : Arg VNat (.bits w)}
    (hc : ccmpAsCmp? op₂.code op₂.args = some ⟨w, co, a₂, b₂⟩) :
    ∃ a₁ b₁ : Arg Val (.bits w),
      ArgRel G (.bits w) a₁ a₂ ∧ ArgRel G (.bits w) b₁ b₂ ∧
      ∀ (P : Tup Val [.bool] → Prop), op₁.wp P → P (co.evalBits a₁.val b₁.val, ()) := by
  cases hop with
  | mk code hargs =>
    cases code with
    | cmp co' t _ hm =>
      cases t <;> try (simp [ccmpAsCmp?] at hc; done)
      rcases hargs with _ | ⟨ha, _ | ⟨hb, -⟩⟩
      simp only [ccmpAsCmp?, Option.some.injEq, Sigma.mk.injEq] at hc
      obtain ⟨rfl, hrest⟩ := hc
      simp only [heq_eq_eq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl, rfl⟩ := hrest
      refine ⟨_, _, ha, hb, fun P hwp => ?_⟩
      simp only [Op.wp, OpCode.wp_cmp, liftCmp, vals, Ty.hasFloat] at hwp
      simpa using hwp
    | _ => simp [ccmpAsCmp?] at hc

theorem preEmpty_stepPre {I : Isa} {h : I.Hints} {ip : Nat} {st : SymState I}
    (hp : preEmpty h ip = true) : stepPre I h ip st = some ([], st) := by
  unfold preEmpty at hp; unfold stepPre
  cases hf : h.pre.find? ip with
  | none => rfl
  | some ps =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true'] at hp
    cases hc : ps.clearFlags <;> cases hm : ps.moves <;> simp_all [execMoves]

theorem jumpTargets_loc_mem {I : Isa} :
    ∀ {ts : List Ty} {args : Tup (Arg VNat) ts} {ploc : List I.Loc}
      {argTgts : List (SymArg × I.Loc)},
    jumpTargets I args ploc = some argTgts → ∀ p ∈ argTgts, p.2 ∈ ploc
  | [], (), [], _, h => by
    simp only [jumpTargets, Option.some.injEq] at h; subst h; intro _ hp; cases hp
  | [], (), _ :: _, _, h => by simp [jumpTargets] at h
  | _ :: _, _, [], _, h => by simp [jumpTargets] at h
  | _ :: _, (a, args), loc :: locs, argTgts, h => by
    dsimp only [jumpTargets] at h
    split at h
    · rename_i sa rest hsa hrest
      simp only [Option.some.injEq] at h; subst h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | htl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (jumpTargets_loc_mem hrest p htl)
    · simp at h

end Rega
end LeanQbe.T
