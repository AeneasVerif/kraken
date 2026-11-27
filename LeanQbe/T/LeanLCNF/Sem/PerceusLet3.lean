module

public import LeanQbe.T.LeanLCNF.Sem.PerceusLet1
public import LeanQbe.T.LeanLCNF.Sem.PerceusLet2
public import LeanQbe.T.LeanLCNF.Sem.PerceusCall
public import LeanQbe.T.LeanLCNF.Sem.PerceusPrims
public import LeanQbe.T.LeanLCNF.Sem.PerceusJp1
public import LeanQbe.T.LeanLCNF.Sem.PerceusJp3
public import LeanQbe.T.LeanLCNF.Sem.PerceusJp5
public import LeanQbe.T.Logic.ProofKit

/-!
# Perceus `let_` Step Simulation (`PerceusLet`)

Simulates all well-formed `LcCode.let_ x ty v k` bindings (`lit`, `erased`, `ctor`, `oproj`,
`uproj`, `sproj`, `box`, `unbox`, `isShared`, module `.fap` calls, and primitive `.fap` calls)
between `PRWp` and `HWp`, preserving all Perceus frame, shadow, resource, and join-point
invariants.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. Bitvector, Word, Type, Context, Shadow, and Join-Point Utilities -/

theorem bv_odd_of_mul2_add1 (n : Nat) :
    BitVec.ofNat 64 (2 * n + 1) &&& 1#64 ≠ 0#64 := by
  intro h
  have h0 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h0
  rw [show (1 : Nat) % 2 ^ 64 = 1 by decide, Nat.and_one_is_mod,
    Nat.mod_mod_of_dvd _ (by decide)] at h0
  omega

theorem bv_shift1_or1_and_one (v : BitVec 64) :
    (v <<< 1 ||| 1#64) &&& 1#64 ≠ 0#64 := by
  intro h
  have h0 : ((v <<< 1 ||| 1#64) &&& 1#64).getLsbD 0 = (0#64).getLsbD 0 := congrArg (·.getLsbD 0) h
  simp [BitVec.getLsbD_eq_getElem] at h0

theorem bv_setWidth_shift1_or1_ushift1 {w : Nat} (hw : w < 64) (v : BitVec 64) :
    BitVec.setWidth w ((v <<< 1 ||| 1#64) >>> 1) = BitVec.setWidth w v := by
  ext i hi
  simp only [BitVec.getElem_setWidth]
  have h1i : 1 + i < 64 := by omega
  have hi64 : i < 64 := by omega
  simp [hi64, h1i, BitVec.getLsbD_eq_getElem]

theorem bv_setWidth_ofNat_2n1_ushift1 {w n : Nat} (_hw : w ≤ 64) (hn : n < 2 ^ 63) :
    BitVec.setWidth w (BitVec.ofNat 64 (2 * n + 1) >>> 1) = BitVec.ofNat w n := by
  have hlt : 2 * n + 1 < 2 ^ 64 := by omega
  have hval : (BitVec.ofNat 64 (2 * n + 1) >>> 1) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.shiftRight_eq_div_pow]
    have hlt2 : n < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    omega
  rw [hval]
  ext i hi
  simp [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.testBit_mod_two_pow, hi]

theorem ty_width_of_not_scalar {ty : LcTy} (h : ty.isScalar = false) :
    ty.width = 64 := by
  cases ty <;> simp_all [LcTy.isScalar, LcTy.width]

theorem ty_width_le_32_of_not_64 {ty : LcTy}
    (hsc : ty.isScalar = true) (h64 : ty ≠ .uint64) (huz : ty ≠ .usize) (hfl : ty ≠ .float) :
    ty.width ≤ 32 := by
  cases ty <;> simp [LcTy.isScalar, LcTy.width] at hsc h64 huz hfl ⊢ <;> omega

theorem ty_needsRc_ne_tagged {ty : LcTy} (h : ty.needsRc = true) :
    ty ≠ .tagged ∧ ty.isScalar = false := by
  cases ty <;> simp [LcTy.needsRc, LcTy.isScalar] at h ⊢

theorem find?_filter_ne {α : Type} (l : List (Nat × α)) {x y : Nat} (hne : y ≠ x) :
    (l.filter (·.1 != x)).find? (·.1 == y) = l.find? (·.1 == y) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h1 : hd.1 = x
    · have hne_hd : (hd.1 == y) = false := by simp [h1, Ne.symm hne]
      have hfb : (hd.1 != x) = false := by simp [h1]
      simp only [List.filter_cons, hfb, Bool.false_eq_true, ↓reduceIte, List.find?_cons,
        hne_hd]
      exact ih
    · have htb : (hd.1 != x) = true := by simp [h1]
      simp only [List.filter_cons, htb, ↓reduceIte, List.find?_cons]
      cases (hd.1 == y) <;> simp [ih]

theorem bv_and_one_eq_zero_of_wf {o : LcnfObj} (hwf : o.Wf) :
    o.addr &&& 1#64 = 0#64 := by
  have hmod : o.addr.toNat % 8 = 0 := hwf.2.1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega

theorem word_toWidth_eq_self {ty : LcTy} {pv : PVal} {w : Word} {objs : List LcnfObj}
    (hvr : ValRep ty pv w objs) : Word.toWidth ty.width w = some w := by
  unfold ValRep at hvr
  split at hvr
  · rcases hvr with ⟨bv, _, rfl⟩ | ⟨c, _, _, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [Word.toWidth, BitVec.setWidth_eq]
  · rcases hvr with ⟨bv, rfl, _⟩
    have hns : ty.isScalar = false := by cases hsc : ty.isScalar <;> simp_all
    cases ty <;> simp [LcTy.isScalar] at hns <;> simp [Word.toWidth, Word.i64, LcTy.width]

theorem evalArgOwn_var_eq {envH : HValEnv} {x : Nat} {ty : LcTy} {w : Word}
    (h : envH x = some (ty, w)) :
    envH.evalArgOwn (.var x) = some w := by
  simp [HValEnv.evalArgOwn, h]

theorem getBV64_of_envH {envH : HValEnv} {x : Nat} {ty : LcTy} {bv : BitVec 64}
    (h : envH x = some (ty, Word.i64 bv)) :
    envH.getBV64? x = some bv := by
  simp [HValEnv.getBV64?, evalArgOwn_var_eq h, Word.toBV64?, Word.i64]

theorem obj_addr_inj_nodup {objs : List LcnfObj}
    (hnd : (objs.map LcnfObj.addr).Nodup)
    {o1 o2 : LcnfObj} (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (ha : o1.addr = o2.addr) :
    o1 = o2 := by
  induction objs with
  | nil => cases h1
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1t <;> rcases List.mem_cons.mp h2 with rfl | h2t
    · rfl
    · exfalso; exact hnd.1 (ha ▸ List.mem_map.mpr ⟨o2, h2t, rfl⟩)
    · exfalso; exact hnd.1 (ha.symm ▸ List.mem_map.mpr ⟨o1, h1t, rfl⟩)
    · exact ih hnd.2 h1t h2t

private theorem put_go_get? {v : RcVar} {vs : List RcVar} (hnd : (vs.map RcVar.id).Nodup)
    (x : Nat) :
    (RcCtx.put.go v vs).find? (·.id == x) =
      if x = v.id then some v else vs.find? (·.id == x) := by
  induction vs with
  | nil =>
    have hdef : RcCtx.put.go v [] = [v] := rfl
    rw [hdef]
    by_cases heq : x = v.id
    · subst heq; simp
    · have hne : (v.id == x) = false := by simp [Ne.symm heq]
      simp [heq, hne]
  | cons u rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hdef : RcCtx.put.go v (u :: rest) =
        if (u.id == v.id) = true then v :: rest else u :: RcCtx.put.go v rest := rfl
    rw [hdef]
    by_cases huv : u.id = v.id
    · have hb : (u.id == v.id) = true := by simp [huv]
      simp only [hb, ↓reduceIte, List.find?_cons]
      by_cases hxv : x = v.id
      · subst hxv; simp
      · have hne1 : (v.id == x) = false := by simp [Ne.symm hxv]
        have hne2 : (u.id == x) = false := by rw [huv]; exact hne1
        simp [hxv, hne1, hne2]
    · have hbf : (u.id == v.id) = false := by simp [huv]
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      by_cases hxu : u.id = x
      · have hbt : (u.id == x) = true := by simp [hxu]
        have hne : x ≠ v.id := hxu ▸ huv
        simp [hbt, hne]
      · have hbuf : (u.id == x) = false := by simp [hxu]
        simp only [hbuf]
        exact ih hnd.2

theorem get?_put_self (ctx : RcCtx) (hnd : (ctx.vars.map RcVar.id).Nodup) (v : RcVar) :
    (ctx.put v).get? v.id = some v := by
  simp [RcCtx.get?, RcCtx.put, put_go_get? hnd]

theorem get?_put_ne (ctx : RcCtx) (hnd : (ctx.vars.map RcVar.id).Nodup) {v : RcVar} {x : Nat}
    (hne : x ≠ v.id) :
    (ctx.put v).get? x = ctx.get? x := by
  simp [RcCtx.get?, RcCtx.put, put_go_get? hnd, hne]

theorem mem_put_vars {ctx : RcCtx} {v u : RcVar} (hu : u ∈ (ctx.put v).vars) :
    u = v ∨ u ∈ ctx.vars := by
  change u ∈ RcCtx.put.go v ctx.vars at hu
  generalize hvs : ctx.vars = vs at hu ⊢
  clear hvs
  induction vs with
  | nil =>
    have hdef : RcCtx.put.go v [] = [v] := rfl
    rw [hdef, List.mem_singleton] at hu
    exact Or.inl hu
  | cons w rest ih =>
    have hdef : RcCtx.put.go v (w :: rest) =
        if (w.id == v.id) = true then v :: rest else w :: RcCtx.put.go v rest := rfl
    rw [hdef] at hu
    split at hu
    · rcases List.mem_cons.mp hu with rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (.tail _ hr)
    · rcases List.mem_cons.mp hu with rfl | hr
      · exact Or.inr (.head _)
      · rcases ih hr with rfl | hw
        · exact Or.inl rfl
        · exact Or.inr (.tail _ hw)

theorem get?_of_mem_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {u : RcVar} (hu : u ∈ ctx.vars) :
    ctx.get? u.id = some u := by
  unfold RcCtx.get?
  generalize hvs : ctx.vars = vs at hnd hu ⊢
  clear hvs
  induction vs with
  | nil => cases hu
  | cons w rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hu with rfl | hr
    · simp
    · have hne : w.id ≠ u.id := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨u, hr, rfl⟩)
      have hbf : (w.id == u.id) = false := by simp [hne]
      simp [hbf, ih hnd.2 hr]

theorem get?_bindOwned_ne (ctx : RcCtx) (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x z : Nat} (hne : z ≠ x) (ty : LcTy)
    (excl : Bool := false) (pers : Bool := false) (rtok : Bool := false) :
    (ctx.bindOwned x ty excl pers rtok).get? z = ctx.get? z :=
  get?_put_ne ctx hnd hne

theorem get?_bindBorrowed_ne (ctx : RcCtx) (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x z : Nat} (hne : z ≠ x) (ty : LcTy)
    (p? : Option Nat := none) (pers : Bool := false) :
    (ctx.bindBorrowed x ty p? pers).get? z = ctx.get? z :=
  get?_put_ne ctx hnd hne

theorem readNatLE_eq_pval (bs : List UInt8) (off k : Nat) :
    PVal.readNatLE bs off k = readNatLE bs off k := by
  induction k generalizing off with
  | zero => rfl
  | succ k ih => rw [PVal.readNatLE.eq_2, readNatLE.eq_2, ih (off + 1)]

theorem shadowSmWf_filter_ne {sm : List (Nat × Nat × List Bool)} {x : Nat}
    (hwf : ShadowSmWf sm) : ShadowSmWf (sm.filter (·.1 != x)) := by
  unfold ShadowSmWf at hwf ⊢
  induction sm with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hwf
    simp only [List.filter_cons]
    split
    · refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hwf.2⟩
      rw [List.mem_map] at hmem
      rcases hmem with ⟨e, he, hid⟩
      exact hwf.1 (hid ▸ List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, rfl⟩)
    · exact ih hwf.2

theorem shadowOk_isVarInit {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} {y : Nat} {vy : RcVar}
    (hsh : ShadowOk sm ctx ρP envP) (hget : ctx.get? y = some vy)
    (hlive : vy.isLive = true) (hinit : isVarScalarInit sm y = true) :
    ρP y = envP y := by
  have h := hsh vy (RcCtx.get?_mem hget).1 hlive
  rw [(RcCtx.get?_mem hget).2, hinit] at h
  exact h

theorem shadowOk_evalArgs_init {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hsh : ShadowOk sm ctx ρP envP)
    {as : List LcArg} (hinit : ∀ a ∈ as, argScalarInit sm a = true)
    (hlive : ∀ a ∈ as, match a with
      | .erased => True
      | .var z => ∃ v, ctx.get? z = some v ∧ v.isLive = true) :
    ρP.evalArgs as = envP.evalArgs as := by
  induction as with
  | nil => rfl
  | cons a rest ih =>
    have ha_init := hinit a (.head _)
    have ha_live := hlive a (.head _)
    have harg : ρP.evalArg a = envP.evalArg a := by
      cases a with
      | erased => rfl
      | var z =>
        rcases ha_live with ⟨v, hv, hvl⟩
        exact shadowOk_isVarInit hsh hv hvl ha_init
    have hrest := ih (fun b hb => hinit b (.tail _ hb)) (fun b hb => hlive b (.tail _ hb))
    show (match ρP.evalArg a, ρP.evalArgs rest with
      | some v, some vs => some (v :: vs) | _, _ => none) =
      (match envP.evalArg a, envP.evalArgs rest with
      | some v, some vs => some (v :: vs) | _, _ => none)
    rw [harg, hrest]

theorem shadowOk_getObj?_eq {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} {y : Nat} {vy : RcVar} {i : Nat}
    (hsh : ShadowOk sm ctx ρP envP) (hget : ctx.get? y = some vy) (hlive : vy.isLive = true) :
    (ρP y).bind (·.getObj? i) = (envP y).bind (·.getObj? i) := by
  have h := hsh vy (RcCtx.get?_mem hget).1 hlive
  rw [(RcCtx.get?_mem hget).2] at h
  by_cases hi : isVarScalarInit sm y = true
  · simp only [hi, ↓reduceIte] at h; rw [h]
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨_, _, _, cidx, fs, pscal, hscal, hp, he, _⟩
    rw [hp, he]
    rfl

theorem shadowOk_ctor_bytes {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} {y n off nb cidx : Nat} {vy : RcVar} {fs : List PVal}
    {pscal : List UInt8}
    (hsh : ShadowOk sm ctx ρP envP) (hget : ctx.get? y = some vy) (hlive : vy.isLive = true)
    (hrdy : scalarSlotReady sm y n off nb = true)
    (hrho : ρP y = some (.ctor cidx fs pscal))
    (_hlen : fs.length ≤ n) (_hb : 8 * (n - fs.length) + off + nb ≤ pscal.length) :
    ∃ hscal, envP y = some (.ctor cidx fs hscal) ∧ hscal.length = pscal.length ∧
      ∀ d, d < nb →
        pscal[8 * (n - fs.length) + off + d]? = hscal[8 * (n - fs.length) + off + d]? := by
  have h := hsh vy (RcCtx.get?_mem hget).1 hlive
  rw [(RcCtx.get?_mem hget).2] at h
  by_cases hi : isVarScalarInit sm y = true
  · simp only [hi, ↓reduceIte] at h; rw [← h, hrho]
    exact ⟨pscal, rfl, rfl, fun _ _ => rfl⟩
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨sz, m, hfind, cidx', fs', pscal', hscal, hp', he', hpl, hhl, hfl, hagree⟩
    rw [hrho] at hp'; cases hp'
    unfold scalarSlotReady at hrdy
    rw [hfind] at hrdy
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hrdy
    rcases hrdy with ⟨⟨_, hmb⟩, hall⟩
    refine ⟨hscal, he', hhl.trans hpl.symm, fun d hd => ?_⟩
    have hidx : 8 * (n - fs.length) + off + d < m.length := by omega
    have hmget := hall d hd
    have hmbang : m[8 * (n - fs.length) + off + d]! = true := by
      have hidx' : 8 * (n - sz) + off + d < m.length := by simpa [hfl] using hidx
      have hgetd : m[8 * (n - sz) + off + d]? = some m[8 * (n - sz) + off + d] :=
        getElem?_pos m _ hidx'
      rw [hfl]
      rw [hgetd] at hmget
      simpa [List.getD_eq_getElem?_getD, hidx'] using hmget
    exact hagree (8 * (n - fs.length) + off + d) hidx (by simpa [hfl] using hmbang)

theorem shadowOk_isTaggedPVal_false {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} {y : Nat} {vy : RcVar} {pv : PVal}
    (hsh : ShadowOk sm ctx ρP envP) (hget : ctx.get? y = some vy) (hlive : vy.isLive = true)
    (hrho : ρP y = some pv) (hnt : isTaggedPVal pv = false) :
    ∃ pvH, envP y = some pvH ∧ isTaggedPVal pvH = false := by
  have h := hsh vy (RcCtx.get?_mem hget).1 hlive
  rw [(RcCtx.get?_mem hget).2] at h
  by_cases hi : isVarScalarInit sm y = true
  · simp only [hi, ↓reduceIte] at h; exact ⟨pv, h.symm.trans hrho, hnt⟩
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨_, m, _, cidx, fs, pscal, hscal, hp, he, hpl, hhl, _⟩
    rw [hrho] at hp; cases hp
    refine ⟨.ctor cidx fs hscal, he, ?_⟩
    rcases fs with _ | _ <;> rcases pscal with _ | _ <;> rcases hscal with _ | _ <;>
      simp [isTaggedPVal] at hnt ⊢ <;> first | exact hnt | (exfalso; simp at hpl hhl; omega)

theorem objRep_not_tagged_mem {pv : PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (hr : ObjRep pv bv objs) (hnt : isTaggedPVal pv = false) :
    ∃ o ∈ objs, o.addr = bv := by
  cases pv with
  | erased => simp [isTaggedPVal] at hnt
  | bits w v =>
    simp [isTaggedPVal] at hnt
    unfold ObjRep at hr
    rcases hr with ⟨hw, _⟩ | ⟨_, o, ho, ha, _⟩
    · omega
    · exact ⟨o, ho, ha⟩
  | nat n =>
    simp [isTaggedPVal] at hnt
    unfold ObjRep natRep at hr
    have hge : ¬n < 2 ^ 63 := by omega
    simp only [hge, ↓reduceIte] at hr
    rcases hr with ⟨_, o, ho, ha, _⟩
    exact ⟨o, ho, ha⟩
  | ctor c fs sc =>
    unfold ObjRep at hr
    rcases hr with ⟨rfl, rfl, hc, _⟩ | ⟨_, o, ho, ha, _⟩
    · simp [isTaggedPVal, hc] at hnt
    · exact ⟨o, ho, ha⟩
  | str s =>
    unfold ObjRep at hr
    rcases hr with ⟨o, ho, ha, _⟩
    exact ⟨o, ho, ha⟩
  | arr xs =>
    unfold ObjRep at hr
    rcases hr with ⟨o, ho, ha, _⟩
    exact ⟨o, ho, ha⟩
  | barr bs =>
    unfold ObjRep at hr
    rcases hr with ⟨o, ho, ha, _⟩
    exact ⟨o, ho, ha⟩
  | int _ => simp [ObjRep] at hr
  | clo _ _ _ => simp [ObjRep] at hr

theorem ctxStaticInv_of {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hcl : CleanVars ctx)
    (hno : NoRcCorrect ctx) (hsbp : SharedBoolPreds ctx) :
    CtxStaticInv ctx :=
  ⟨hnd, hno, hsbp, fun v hv hnb => (hcl v hv).2.2.2.1 hnb⟩

theorem jpsScopeIn_put {jps : List RcJpInfo} {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) {v : RcVar}
    (h : JpsScopeIn jps ctx) : JpsScopeIn jps (ctx.put v) := by
  refine ⟨h.1, fun info hi => ?_⟩
  have hinfo := h.2 info hi
  refine ⟨hinfo.1, hinfo.2.1, fun id hid => ?_⟩
  have his := hinfo.2.2 id hid
  by_cases heq : id = v.id
  · subst heq; simp [get?_put_self ctx hnd v]
  · rw [get?_put_ne ctx hnd heq]; exact his

theorem jpsScopeIn_applyArgs {jps : List RcJpInfo} {ctx ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (happ : ctx.applyArgs as bs = .ok ctx1) (h : JpsScopeIn jps ctx) :
    JpsScopeIn jps ctx1 := by
  have hprops := applyArgs_ctx_props hnd happ
  refine ⟨h.1, fun info hi => ?_⟩
  have hinfo := h.2 info hi
  exact ⟨hinfo.1, hinfo.2.1, fun id hid => hprops.2.2.1 id (hinfo.2.2 id hid)⟩

theorem sharedBoolVars_put_fresh {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbv : SharedBoolVars ctx) {v : RcVar}
    (hfr : ∀ p ∈ ctx.sharedPreds, p.1 ≠ v.id) :
    SharedBoolVars (ctx.put v) := by
  intro p hp vb hget
  have hne : p.1 ≠ v.id := hfr p hp
  have hget0 : ctx.get? p.1 = some vb := by rwa [get?_put_ne ctx hnd hne] at hget
  exact hsbv p hp vb hget0

theorem sharedBool_applyArgs_bindOwned {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hsbv : SharedBoolVars ctx) (hsbp : SharedBoolPreds ctx)
    (happ : ctx.applyArgs as bs = .ok ctx1) {x : Nat} (hfr : binderFreshOwned ctx x = true)
    (ty : LcTy) (excl : Bool := false) (pers : Bool := false) (rtok : Bool := false) :
    SharedBoolVars (ctx1.bindOwned x ty excl pers rtok) ∧
      SharedBoolPreds (ctx1.bindOwned x ty excl pers rtok) := by
  have hsb1 := sharedBool_applyArgs hnd hsbv hsbp happ
  have hnd1 := applyArgs_nodup hnd happ
  have hpreds : ∀ p ∈ ctx1.sharedPreds, p.1 ≠ x := by
    intro p hp heq
    have hsp := (applyArgs_ctx_props hnd happ).2.1 p hp
    unfold binderFreshOwned at hfr
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
    exact (hfr.1.2 p hsp).1 heq
  exact ⟨sharedBoolVars_put_fresh hnd1 hsb1.1 hpreds, sharedBoolPreds_put_fresh hnd1 hsb1.2 hpreds⟩

theorem exclCtorHeap_applyArgs_bindOwned {rf : RcFrame} {ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool} {x : Nat} {ty : LcTy} {pv : PVal} {w : Word}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hex : ExclCtorHeap rf) (happ : rf.ctx.applyArgs as bs = .ok ctx1) :
    let ctx' := ctx1.bindOwned x ty
    ExclCtorHeap
      { rf with ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty w } := by
  have hex1 := exclCtorHeap_applyArgs hnd hex happ
  have hnd1 := applyArgs_nodup hnd happ
  intro ctx' u hu hlive huex hunr hupr cidx fs sc hp
  have hne : u.id ≠ x := by
    intro heq
    have hget := get?_of_mem_nodup (RcCtx.put_nodup hnd1 _) hu
    rw [heq] at hget
    simp only [get?_put_self ctx1 hnd1 _] at hget
    cases hget
    simp at huex
  have hget' := get?_of_mem_nodup (RcCtx.put_nodup hnd1 _) hu
  change (ctx1.bindOwned x ty).get? u.id = some u at hget'
  rw [get?_bindOwned_ne ctx1 hnd1 hne] at hget'
  have hu1 := (RcCtx.get?_mem hget').1
  simp only [PValEnv.set, hne, ↓reduceIte] at hp
  obtain ⟨bv, hh, hev⟩ := hex1 u hu1 hlive huex hunr hupr cidx fs sc hp
  exact ⟨bv, by simp only [HValEnv.set, hne, ↓reduceIte]; exact hh, hev⟩

theorem sharedTargetsHeap_applyArgs_bindOwned {rf : RcFrame} {ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool} {x : Nat} {ty : LcTy} {pv : PVal} {w : Word}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hcl : CleanVars rf.ctx)
    (hsth : SharedTargetsHeap rf) (happ : rf.ctx.applyArgs as bs = .ok ctx1)
    (hfr : binderFreshOwned rf.ctx x = true) :
    let ctx' := ctx1.bindOwned x ty
    SharedTargetsHeap
      { rf with ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty w } := by
  have hsth1 := sharedTargetsHeap_applyArgs hnd hsth happ
  have hnd1 := applyArgs_nodup hnd happ
  have hfr1 := binderFreshOwned_applyArgs hnd hcl happ hfr
  intro ctx' p hp vx hget hunr
  have hp1 : p ∈ ctx1.sharedPreds := hp
  have hne : p.2 ≠ x := by
    unfold binderFreshOwned at hfr1
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr1
    exact (hfr1.1.2 p hp1).2
  change (ctx1.bindOwned x ty).get? p.2 = some vx at hget
  rw [get?_bindOwned_ne ctx1 hnd1 hne] at hget
  obtain ⟨bv, hh, hev⟩ := hsth1 p hp1 vx hget hunr
  exact ⟨bv, by simp only [HValEnv.set, hne, ↓reduceIte]; exact hh, hev⟩

theorem shadowOk_applyArgs_bindOwned {sm : List (Nat × Nat × List Bool)} {rf : RcFrame}
    {ctx1 : RcCtx} {ρP : PValEnv} {as : List LcArg} {bs : List Bool}
    {x : Nat} {ty : LcTy} {pv : PVal}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (happ : rf.ctx.applyArgs as bs = .ok ctx1) :
    ShadowOk (sm.filter (·.1 != x)) (ctx1.bindOwned x ty) (ρP.set x pv) (rf.envP.set x pv) := by
  have hsh1 := shadowOk_applyArgs hnd hsh happ
  have hnd1 := applyArgs_nodup hnd happ
  intro u hu hlive
  have hgetu := get?_of_mem_nodup (RcCtx.put_nodup hnd1 _) hu
  by_cases heq : u.id = x
  · have his : isVarScalarInit (sm.filter (·.1 != x)) x = true := by
      simp [isVarScalarInit]
    rw [heq, his]
    simp [PValEnv.set]
  · change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
    rw [get?_bindOwned_ne ctx1 hnd1 heq] at hgetu
    have hu1 := (RcCtx.get?_mem hgetu).1
    have h0 := hsh1 u hu1 hlive
    have his : isVarScalarInit (sm.filter (·.1 != x)) u.id = isVarScalarInit sm u.id := by
      simp only [isVarScalarInit, List.all_filter]
      congr 1; ext e
      by_cases h1 : e.1 = x
      · simp [h1, show x ≠ u.id from Ne.symm heq]
      · simp [h1]
    have hfind : (sm.filter (·.1 != x)).find? (·.1 == u.id) = sm.find? (·.1 == u.id) :=
      find?_filter_ne sm heq
    rw [his]
    simp only [PValEnv.set, heq, ↓reduceIte]
    by_cases hisu : isVarScalarInit sm u.id = true
    · simp only [hisu, ↓reduceIte] at h0 ⊢; exact h0
    · simp only [hisu, Bool.false_eq_true, ↓reduceIte] at h0 ⊢; rw [hfind]; exact h0

theorem jpsOk_let_step {rt : BitVec 64} {rf0 rf rf' : RcFrame} {σ0 : HState}
    {Jp : PResJEnv} {Jh : HJEnv} {jpsOk : List JpEntry} {ρP ρP' : PValEnv}
    {jumps : List (Nat × RcCtx)} {x : Nat}
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hctx : (∀ z, z ≠ x →
        Option.map RcVar.ty (rf'.ctx.get? z) = Option.map RcVar.ty (rf.ctx.get? z) ∧
        (Option.map RcVar.isLive (rf'.ctx.get? z) = some true →
          Option.map RcVar.isLive (rf.ctx.get? z) = some true)) ∧
      ∀ p, p ∈ rf'.ctx.sharedPreds → p.1 ≠ x → p ∈ rf.ctx.sharedPreds ∧ p.2 ≠ x)
    (henv : ∀ z, z ≠ x → rf'.envP z = rf.envP z ∧ rf'.envH z = rf.envH z ∧ ρP' z = ρP z)
    (hext : rf'.extH = rf.extH) :
    JpsOk rt rf0 σ0 Jp Jh
      (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }) rf' ρP' jumps := by
  cases rf'
  simp only at hext hctx henv ⊢
  subst hext
  exact jpsOk_mut_step hjok hctx henv (fun _ h => h)

theorem ctx_step_props_bindOwned {ctx : RcCtx} {x : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hfr : binderFreshOwned ctx x = true)
    (ty : LcTy) (excl : Bool := false) (pers : Bool := false) (rtok : Bool := false) :
    (∀ z, z ≠ x →
        Option.map RcVar.ty ((ctx.bindOwned x ty excl pers rtok).get? z) =
          Option.map RcVar.ty (ctx.get? z) ∧
        (Option.map RcVar.isLive ((ctx.bindOwned x ty excl pers rtok).get? z) = some true →
          Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      ∀ p, p ∈ (ctx.bindOwned x ty excl pers rtok).sharedPreds → p.1 ≠ x →
        p ∈ ctx.sharedPreds ∧ p.2 ≠ x := by
  refine ⟨fun z hz => ?_, fun p hp _ => ?_⟩
  · rw [get?_bindOwned_ne ctx hnd hz ty excl pers rtok]; simp
  refine ⟨hp, ?_⟩
  unfold binderFreshOwned at hfr
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
  exact (hfr.1.2 p hp).2

theorem ctx_step_props_applyArgs_bindOwned {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    {x : Nat} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (happ : ctx.applyArgs as bs = .ok ctx1) (hfr : binderFreshOwned ctx x = true)
    (ty : LcTy) (excl : Bool := false) (pers : Bool := false) (rtok : Bool := false) :
    (∀ z, z ≠ x →
        Option.map RcVar.ty ((ctx1.bindOwned x ty excl pers rtok).get? z) =
          Option.map RcVar.ty (ctx.get? z) ∧
        (Option.map RcVar.isLive ((ctx1.bindOwned x ty excl pers rtok).get? z) = some true →
          Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      ∀ p, p ∈ (ctx1.bindOwned x ty excl pers rtok).sharedPreds → p.1 ≠ x →
        p ∈ ctx.sharedPreds ∧ p.2 ≠ x := by
  have hprops := applyArgs_ctx_props hnd happ
  have hnd1 := applyArgs_nodup hnd happ
  refine ⟨fun z hz => ?_, fun p hp _ => ?_⟩
  · rw [get?_bindOwned_ne ctx1 hnd1 hz ty excl pers rtok]
    exact hprops.1 z
  · have hp0 : p ∈ ctx.sharedPreds := hprops.2.1 p hp
    refine ⟨hp0, ?_⟩
    unfold binderFreshOwned at hfr
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
    exact (hfr.1.2 p hp0).2

/-! ## 2. Call, `ParentChildBacked`, and Primitive Simulation Helpers -/

theorem nonPersistReach_lift_stepRel {ext : List (BitVec 64)} {σ σ' : HState}
    (hstep : HeapStepRel ext σ σ') (hwf : ∀ o ∈ σ.objs, o.Wf)
    (hnd : (σ.objs.map LcnfObj.addr).Nodup)
    {r a : BitVec 64} (hr : r ∈ ext) (hreach : NonPersistReach σ.objs r a) :
    NonPersistReach σ'.objs r a ∧
      ∀ o ∈ σ.objs, o.addr = a → ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ o'.rc ≠ 0#32 := by
  induction hreach with
  | refl hroot =>
    rcases hroot with ⟨o, ho, ha, hrc⟩
    have hbk : Backed σ.objs ext o.addr := by
      rw [ha]; exact Or.inr ⟨r, hr, NonPersistReach.refl ⟨o, ho, ha, hrc⟩⟩
    obtain ⟨o', ho', heq, _, hpos⟩ := hstep.2.2.2.1 o ho (hwf o ho) hbk
    have hne0 : o'.rc ≠ 0#32 := by
      have hpos1 : 0 < o.rc.toInt := rc_toInt_pos_of_ne_zero (hwf o ho).2.2.1 hrc
      intro h0; have := hpos hpos1; simp [h0] at this
    refine ⟨NonPersistReach.refl ⟨o', ho', heq.1.symm ▸ ha, hne0⟩, fun q hq hqa => ?_⟩
    have hqe : q = o := obj_addr_inj_nodup hnd hq ho (hqa.trans ha.symm)
    subst hqe
    exact ⟨o', ho', heq, hne0⟩
  | @step u v hpre hch hven hvo ih =>
    rcases hch with ⟨o, ho, ha, hvmem⟩
    rcases hvo with ⟨ov, hov, hva, hvrc⟩
    obtain ⟨o', ho', heqo, _⟩ := ih.2 o ho ha
    have hvmem' : v ∈ o'.childFields := by rw [objDataEq_childFields heqo]; exact hvmem
    have hreachv : NonPersistReach σ.objs r v :=
      NonPersistReach.step hpre ⟨o, ho, ha, hvmem⟩ hven ⟨ov, hov, hva, hvrc⟩
    have hbkv : Backed σ.objs ext ov.addr := by
      rw [hva]; exact Or.inr ⟨r, hr, hreachv⟩
    obtain ⟨ov', hov', heqv, _, hvpos⟩ := hstep.2.2.2.1 ov hov (hwf ov hov) hbkv
    have hvne0 : ov'.rc ≠ 0#32 := by
      have hpos1 : 0 < ov.rc.toInt := rc_toInt_pos_of_ne_zero (hwf ov hov).2.2.1 hvrc
      intro h0; have := hvpos hpos1; simp [h0] at this
    refine ⟨NonPersistReach.step ih.1 ⟨o', ho', heqo.1.symm ▸ ha, hvmem'⟩ hven
      ⟨ov', hov', heqv.1.symm ▸ hva, hvne0⟩, fun q hq hqa => ?_⟩
    have hqe : q = ov := obj_addr_inj_nodup hnd hq hov (hqa.trans hva.symm)
    subst hqe
    exact ⟨ov', hov', heqv, hvne0⟩

theorem nonPersistReach_root_rc_ne_zero {objs : List LcnfObj} {r a : BitVec 64}
    (hreach : NonPersistReach objs r a) :
    ∃ o ∈ objs, o.addr = r ∧ o.rc ≠ 0#32 := by
  induction hreach with
  | refl h => exact h
  | step _ _ _ _ ih => exact ih

theorem backed_lift_of_sub_stepRel {sub ext : List (BitVec 64)} {σ σ' : HState} {a : BitVec 64}
    (hsub : ∀ r ∈ sub, r ∈ ext) (hstep : HeapStepRel ext σ σ')
    (hwf : ∀ o ∈ σ.objs, o.Wf) (hnd : (σ.objs.map LcnfObj.addr).Nodup)
    (hbk : Backed σ.objs sub a) :
    Backed σ'.objs sub a := by
  rcases hbk with ⟨o, ho, ha, hrc⟩ | ⟨r, hr, hreach⟩
  · have hbke : Backed σ.objs ext o.addr := by rw [ha]; exact Or.inl ⟨o, ho, ha, hrc⟩
    obtain ⟨o', ho', heq, hz, _⟩ := hstep.2.2.2.1 o ho (hwf o ho) hbke
    exact Or.inl ⟨o', ho', heq.1.symm ▸ ha, hz hrc⟩
  · exact Or.inr ⟨r, hr, (nonPersistReach_lift_stepRel hstep hwf hnd (hsub r hr) hreach).1⟩

theorem varHandles_mem_of_owned {envH : HValEnv} {v : RcVar} {bv : BitVec 64}
    (hnr : v.noRc = false) (hpr : v.persistent = false) (hrk : v.resetTok = false)
    (ho : 0 < v.owned) (hh : ∃ wp, envH v.id = some wp ∧ wp.2.toBV64? = some bv)
    (hev : bv &&& 1#64 = 0#64) :
    bv ∈ varHandles envH v := by
  rcases hh with ⟨wp, hw, hbv⟩
  have hno0 : (v.owned == 0) = false := by simp; omega
  unfold varHandles
  simp only [hnr, hpr, hrk, hno0, Bool.false_or, ↓reduceIte, hw, hbv, hev, beq_self_eq_true]
  exact List.mem_replicate.mpr ⟨by omega, rfl⟩

theorem mem_localHandles_of_varHandles {ctx : RcCtx} {envH : HValEnv} {v : RcVar} {bv : BitVec 64}
    (hm : v ∈ ctx.vars) (hvh : bv ∈ varHandles envH v) :
    bv ∈ localHandles ctx envH := by
  unfold localHandles
  exact List.mem_flatten.mpr ⟨varHandles envH v, List.mem_map.mpr ⟨v, hm, rfl⟩, hvh⟩

theorem parentChildBacked_after_call {rt : BitVec 64} {rf : RcFrame} {σ σ' : HState}
    {x : Nat} {ty : LcTy} {as : List LcArg} {borrows : List Bool} {ctx1 : RcCtx}
    {pv : PVal} {rw : Word}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hcl : CleanVars rf.ctx)
    (hpcb : ParentChildBacked rf σ.objs) (happ : rf.ctx.applyArgs as borrows = .ok ctx1)
    (hpo1 : ParentsOwned ctx1) (hcl1 : CleanVars ctx1)
    (hfr : binderFreshOwned rf.ctx x = true) (hclean : HeapClean rt σ)
    (hstep : HeapStepRel (localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH) σ σ') :
    let ctx' := ctx1.bindOwned x ty
    ParentChildBacked
      { rf with ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty rw }
      σ'.objs := by
  have hnd1 := applyArgs_nodup hnd happ
  have hfr1 := binderFreshOwned_applyArgs hnd hcl happ hfr
  intro ctx' u hu hlive hunr hupr hubr p hpar bv hbu heven
  have hne : u.id ≠ x := by
    intro heq
    have hget := get?_of_mem_nodup (RcCtx.put_nodup hnd1 _) hu
    rw [heq] at hget
    simp only [get?_put_self ctx1 hnd1 _] at hget
    cases hget
    simp at hubr
  have hget' := get?_of_mem_nodup (RcCtx.put_nodup hnd1 _) hu
  change (ctx1.bindOwned x ty).get? u.id = some u at hget'
  rw [get?_bindOwned_ne ctx1 hnd1 hne] at hget'
  have hu1 := (RcCtx.get?_mem hget').1
  have hne_p : p ≠ x := by
    intro heq
    unfold binderFreshOwned at hfr1
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr1
    exact absurd (heq ▸ hpar) (hfr1.1.1 u hu1)
  obtain ⟨u0, hget0, hl0, hnr0, hpr0, hty0, _, hbr0, _⟩ :=
    applyArgs_get?_live_back hnd hcl happ u.id hget' hlive
  have hu0 := (RcCtx.get?_mem hget0).1
  have hid0 := (RcCtx.get?_mem hget0).2
  have hbr0' := hbr0 hubr
  simp only [HValEnv.set, hne, ↓reduceIte] at hbu
  have h0 := hpcb u0 hu0 hl0 (by rw [hnr0]; exact hunr) (by rw [hpr0]; exact hupr)
    hbr0'.1 p (by rw [hbr0'.2, hpar]) bv (by simpa [hid0, hty0] using hbu) heven
  have hwf : ∀ o ∈ σ.objs, o.Wf := hclean.1.2.1
  have hnd_o : (σ.objs.map LcnfObj.addr).Nodup := hclean.2
  rcases h0 with hbk | ⟨wp, o_p, hhp, hbv_p, ho_p, o_mid, ho_mid, hreach, hchild⟩
  · left
    exact backed_lift_of_sub_stepRel
      (fun r hr => List.mem_append.mpr (by
        rcases List.mem_append.mp hr with hr1 | hr2
        · left; exact List.mem_append.mpr (Or.inr hr1)
        · right; exact hr2))
      hstep hwf hnd_o hbk
  · right
    obtain ⟨vp, hvp_mem, hidvp, hvp_nr, hvp_pr, hovp, _⟩ := hpo1 u hu1 p hpar
    have hvp_rk : vp.resetTok = false := (hcl1 vp hvp_mem).2.2.2.2
    have hev_p : o_p.addr &&& 1#64 = 0#64 := bv_and_one_eq_zero_of_wf (hwf o_p ho_p)
    have hvh_p : o_p.addr ∈ varHandles rf.envH vp := by
      have := varHandles_mem_of_owned (envH := rf.envH) hvp_nr hvp_pr hvp_rk hovp
        ⟨wp, by rw [hidvp]; exact hhp, hbv_p⟩ hev_p
      simpa using this
    have hloc_p : o_p.addr ∈ localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inl (mem_localHandles_of_varHandles hvp_mem hvh_p))))
    obtain ⟨o_r0, hor0, har0, hrcr0⟩ := nonPersistReach_root_rc_ne_zero hreach
    have hbkp : Backed σ.objs (localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH) o_r0.addr := by
      rw [har0]; exact Or.inr ⟨o_p.addr, hloc_p, NonPersistReach.refl ⟨o_r0, hor0, har0, hrcr0⟩⟩
    obtain ⟨o_p', ho_p', heqp, _⟩ := hstep.2.2.2.1 o_r0 hor0 (hwf o_r0 hor0) hbkp
    have hreach_l := nonPersistReach_lift_stepRel hstep hwf hnd_o hloc_p hreach
    obtain ⟨o_mid', ho_mid', heqm, _⟩ := hreach_l.2 o_mid ho_mid rfl
    refine ⟨wp, o_p', by simp [HValEnv.set, hne_p, hhp], ?_, ho_p',
      o_mid', ho_mid', ?_, ?_⟩
    · simpa [heqp.1, har0] using hbv_p
    · simpa [heqp.1, har0, heqm.1] using hreach_l.1
    · rw [objDataEq_childFields heqm]; exact hchild

theorem nonScalarWords_subset {ps : List LcParam} {ws : List Word} :
    ∀ w ∈ nonScalarWords ps ws, w ∈ ws := by
  intro w hw
  simp only [nonScalarWords, List.mem_filterMap] at hw
  rcases hw with ⟨⟨p, w0⟩, hm, hif⟩
  split at hif
  · cases hif; exact (List.of_mem_zip hm).2
  · cases hif

private theorem nonScalarWords_disjoint_aux {rf : RcFrame} {objs : List LcnfObj}
    {as : List LcArg} {ps : List LcParam} {pts : List LcTy} {ws : List Word}
    (hvi : ∀ v ∈ rf.ctx.vars, VarInv v rf objs)
    (hpts : pts = ps.map LcParam.ty)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hmt : argsMatchTys rf.ctx as pts = true)
    (hevo : rf.envH.evalArgsOwn as = some ws)
    {a : BitVec 64} (heven : a &&& 1#64 = 0#64)
    (hall : ∀ v ∈ rf.ctx.vars, v.isLive = true → (!decide (v.ty.isScalar = true)) = true →
      ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some a) :
    ∀ w ∈ nonScalarWords ps ws, w.toBV64? ≠ some a := by
  subst hpts
  induction as generalizing ps ws with
  | nil =>
    cases ps with
    | nil => cases ws <;> simp [nonScalarWords]
    | cons _ _ => simp [argsMatchTys] at hmt
  | cons arg rest ih =>
    cases ps with
    | nil => simp [argsMatchTys] at hmt
    | cons p ps' =>
      have hstep : rf.envH.evalArgsOwn (arg :: rest) =
          match rf.envH.evalArgOwn arg, rf.envH.evalArgsOwn rest with
          | some v, some vs => some (v :: vs) | _, _ => none := rfl
      rw [hstep] at hevo
      cases ha_ev : rf.envH.evalArgOwn arg with
      | none => simp [ha_ev] at hevo
      | some wh' =>
        cases hr_ev : rf.envH.evalArgsOwn rest with
        | none => simp [ha_ev, hr_ev] at hevo
        | some wt' =>
          simp only [ha_ev, hr_ev, Option.some.injEq] at hevo
          subst hevo
          have hmt_pair : argsMatchTys rf.ctx [arg] [p.ty] = true ∧
              argsMatchTys rf.ctx rest (ps'.map LcParam.ty) = true := by
            unfold argsMatchTys at hmt ⊢
            simp only [List.length_cons, List.map_cons, List.zip_cons_cons,
              List.all_cons, List.zip_nil_right, List.all_nil, Bool.and_true,
              Bool.and_eq_true, beq_iff_eq, List.length_map] at hmt ⊢
            exact ⟨⟨rfl, hmt.2.1⟩, ⟨by omega, hmt.2.2⟩⟩
          have iht := ih (fun x hx => hlive x (.tail _ hx)) hr_ev hmt_pair.2
          intro w hw
          simp only [nonScalarWords, List.zip_cons_cons, List.filterMap_cons] at hw
          by_cases hns_p : (!p.ty.isScalar) = true
          · simp only [hns_p, ↓reduceIte, List.mem_cons] at hw
            rcases hw with rfl | hwt
            · rcases hlive arg (.head _) with rfl | ⟨z, vz, rfl, hgetz, hlvz⟩
              · simp [HValEnv.evalArgOwn] at ha_ev
                subst ha_ev
                intro h1; simp [Word.toBV64?, Word.i64] at h1
                rw [← h1] at heven; simp at heven
              · have hsc : vz.ty.isScalar = p.ty.isScalar := by
                  have hm1 := hmt_pair.1
                  unfold argsMatchTys at hm1
                  simp only [List.zip_cons_cons, List.zip_nil_right, List.all_cons,
                    List.all_nil, Bool.and_true, Bool.and_eq_true, hgetz,
                    beq_iff_eq] at hm1
                  exact hm1.2.1.1.1.1
                have hns_z : (!decide (vz.ty.isScalar = true)) = true := by
                  simpa [hsc] using hns_p
                have hv_mem := (RcCtx.get?_mem hgetz).1
                have hv_id := (RcCtx.get?_mem hgetz).2
                obtain ⟨_, w0, _, hhz, _⟩ := hvi vz hv_mem hlvz
                rw [hv_id] at hhz
                have hew : w0 = w := by simpa [HValEnv.evalArgOwn, hhz] using ha_ev
                subst hew
                exact hall vz hv_mem hlvz hns_z w0 (by rw [hv_id]; exact hhz)
            · exact iht w hwt
          · simp only [hns_p, Bool.false_eq_true, ↓reduceIte] at hw
            exact iht w hw

theorem mkRcModEnv_find_decl {m : LcModule} {f nm : String}
    {borrows : List Bool} {pts : List LcTy} {rty : LcTy} {isConst : Bool}
    (hfind : (mkRcModEnv m).decls.find? (·.1 == f) = some (nm, borrows, pts, rty, isConst)) :
    ∃ d ∈ m.decls, d.name = f ∧ d.params.map (·.borrow) = borrows ∧
      d.params.map (·.ty) = pts ∧ d.retTy = rty ∧
      isConst = (d.params.isEmpty && !d.retTy.isScalar) := by
  unfold mkRcModEnv at hfind
  simp only [List.find?_map] at hfind
  cases hdm : m.decls.find? (fun d => (d.name == f)) with
  | none =>
    have hno : m.decls.find? (fun d => (Function.comp (·.1 == f)
        (fun d : LcDecl => (d.name, d.params.map (·.borrow), d.params.map (·.ty), d.retTy,
          d.params.isEmpty && !d.retTy.isScalar)) d)) = none := hdm
    rw [hno] at hfind
    cases hfind
  | some d =>
    have hdm' : m.decls.find? (fun d => (Function.comp (·.1 == f)
        (fun d : LcDecl => (d.name, d.params.map (·.borrow), d.params.map (·.ty), d.retTy,
          d.params.isEmpty && !d.retTy.isScalar)) d)) = some d := hdm
    rw [hdm'] at hfind
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfind
    rcases hfind with ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hdmem := List.mem_of_find?_eq_some hdm
    have hnm : d.name = f := by
      have hp := List.find?_some hdm
      simpa using hp
    exact ⟨d, hdmem, hnm, rfl, rfl, rfl, rfl⟩

@[expose] def CallPostOk (rt : BitVec 64) (d : LcDecl) (calleeExtH : List (BitVec 64))
    (nsWs : List Word) (σ σ' : HState) (rw : Word) (P : PResPost) : Prop :=
  ∃ pv rem' wr' rcr',
    P pv rem' wr' rcr' ∧ HeapClean rt σ' ∧ ValRep d.retTy pv rw σ'.objs ∧
      (¬d.retTy.isScalar = true → ¬d.retTy.needsRc = true →
        ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) ∧
      HandlesRcSound (retHandles d.retTy rw ++ calleeExtH) σ'.objs ∧
      CallPreserve nsWs calleeExtH σ σ' ∧
      ResStateInv σ' rem' wr' rcr'

@[expose] def CallExcOk (_rt : BitVec 64) (_σ' : HState) (c : BitVec 64) (E : PResXPost) : Prop :=
  ∃ cn rem' wr' rcr', E cn rem' wr' rcr' ∧ BitVec.ofNat 64 cn = c

@[expose] def PRCallCompat (m : LcModule) (Δr : PResEnv) (Δh : HEnv) : Prop :=
  ∀ (rt : BitVec 64) (d : LcDecl) (calleeRf : RcFrame) (σ : HState)
    (pvs : List PVal) (ws : List Word) (rem wr rcr : Nat)
    (P : PResPost) (E : PResXPost),
    d ∈ m.decls →
    calleeRf = entryRcFrame d pvs ws calleeRf.extH calleeRf.ghostH →
    pvs.length = d.params.length →
    ws.length = d.params.length →
    RcInv rt calleeRf σ →
    CleanVars calleeRf.ctx →
    ParentsOwned calleeRf.ctx →
    HandlesInHeap (calleeRf.extH ++ calleeRf.ghostH) σ.objs →
    ResStateInv σ rem wr rcr →
    Δr d.name pvs rem wr rcr P E →
    ∃ Ph Eh, Δh d.name ws σ Ph Eh ∧
      (∀ rw σ', Ph rw σ' →
        CallPostOk rt d (calleeRf.extH ++ calleeRf.ghostH)
          (nonScalarWords d.params ws) σ σ' rw P) ∧
      (∀ c σ', Eh c σ' → CallExcOk rt σ' c E)

theorem fap_decl_step {m : LcModule} {Δr : PResEnv} {Δh : HEnv}
    {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)}
    {ρP : PValEnv} {rem wr rcr x : Nat} {ty : LcTy} {f : String} {as : List LcArg}
    {nm : String} {borrows : List Bool} {pts : List LcTy} {rty : LcTy} {isConst : Bool}
    {ctx' : RcCtx} {K : PResPost} {Xp : PResXPost} {Kh : HPost} {Xh : HXPost}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    (hcompat : PRCallCompat m Δr Δh)
    (hfind : (mkRcModEnv m).decls.find? (·.1 == f) = some (nm, borrows, pts, rty, isConst))
    (hpvwf : perceusValWf (mkRcModEnv m) rf.ctx x ty (.fap f as) = true)
    (hinit : ∀ a ∈ as, argScalarInit sm a = true)
    (hcv : checkVal (mkRcModEnv m) rf.ctx x ty (.fap f as) = .ok ctx')
    (hpr : PRValWp (mkRcModEnv m) Δr ρP ty (.fap f as) rem wr rcr K Xp)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv} {rem' wr' rcr' : Nat}
      {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.extH = rf.extH →
      rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      (∀ z, z ≠ x → rf'.envP z = rf.envP z ∧ rf'.envH z = rf.envH z ∧ ρP' z = ρP z) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowOk (sm.filter (·.1 != x)) rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' → Kh rw σ')
    (hx : ∀ {c : Nat} {rem' wr' rcr' : Nat} {σ' : HState},
      Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ') :
    HVal.wp Δh rt rf.envH ty (.fap f as) Kh Xh σ := by
  obtain ⟨d, hd, rfl, hbrs, hpts, hrty, hcst⟩ := mkRcModEnv_find_decl hfind
  have hd_props := hmwf d hd
  have hpvwf' := hpvwf
  unfold perceusValWf at hpvwf'
  simp only [Bool.and_eq_true, hfind] at hpvwf'
  rcases hpvwf' with ⟨hfr, hwf_rest⟩
  simp only [beq_iff_eq, decide_eq_true_eq] at hwf_rest
  rcases hwf_rest with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hncst, hmt⟩, hnost⟩, hnoex⟩, happw⟩, hshpreds⟩, hsc_eq⟩,
    hw_eq⟩, hnr_eq⟩, hobj_imp⟩, htag_imp⟩
  have hncst_b : (isConst && as.isEmpty) = false := by
    cases h : isConst && as.isEmpty <;> simp_all
  cases happ : rf.ctx.applyArgs as borrows with
  | error e => simp [happ] at happw
  | ok ctx1 =>
    simp only [happ, Bool.and_eq_true] at happw
    rcases happw with ⟨hbsurv, hex_excl⟩
    have hctx'_eq : ctx' = ctx1.bindOwned x ty := by
      unfold checkVal at hcv
      simp [hfind, hncst_b, happ, Functor.map, Except.map] at hcv
      exact hcv.symm
    subst hctx'_eq
    unfold PRValWp at hpr
    have hnoob : (d.name == "outOfBounds._redArg") = false := by
      rw [Bool.eq_false_iff]
      intro h
      have heq : d.name = "outOfBounds._redArg" := by simpa using h
      have hp := hd_props.1
      rw [heq] at hp
      exact absurd hp (by decide)
    have hfind_isSome :
        (List.find? (fun x => x.fst == d.name) (mkRcModEnv m).decls).isSome = true := by
      rw [hfind]; rfl
    cases hevp : ρP.evalArgs as with
    | none => simp [hevp] at hpr
    | some pvs =>
      simp only [hevp, hnoob, hfind_isSome, Bool.false_eq_true, ↓reduceIte] at hpr
      rcases hpr with ⟨P, E, hspec, hPK, hEX⟩
      have hlive_as := applyArgs_var_live hrc.2.1 hcl happ
      have hl_eval : ∀ a ∈ as, match a with
          | .erased => True
          | .var z => ∃ v, rf.ctx.get? z = some v ∧ v.isLive = true := by
        intro a ha
        rcases hlive_as a ha with rfl | ⟨z, v, rfl, hgz, hlv⟩
        · trivial
        · exact ⟨v, hgz, hlv⟩
      have hevp_rf : rf.envP.evalArgs as = some pvs := by
        rw [← shadowOk_evalArgs_init hsh hinit hl_eval]
        exact hevp
      obtain ⟨ws, hevh, _⟩ := evalArgsOwn_sim hrc.2.2.2.1 hl_eval hevp_rf
      have hevh_var : rf.envH.evalArgsOwn as = some ws := hevh
      have hfok := entryRcFrame_fap_ok hrc hcl hpo hhih d hd_props.2
        (by simpa [hbrs] using happ) (by simpa [hpts] using hmt)
        (by simpa [hbrs] using hnost) (by simpa [hbrs] using hbsurv) hevp_rf hevh
      rcases hfok with ⟨hpvs_len, hws_len, hrc_c, hcl_c, hpo_c, hhih_c, hrc1, hcl1, hpo1⟩
      let calleeExtH := localHandles ctx1 rf.envH ++ rf.extH
      let calleeRf := entryRcFrame d pvs ws calleeExtH rf.ghostH
      obtain ⟨Ph, Eh, hcall_spec, hPh, hEh⟩ := hcompat rt d calleeRf σ pvs ws rem wr rcr P E
        hd rfl hpvs_len hws_len hrc_c hcl_c hpo_c hhih_c hres hspec
      have hprim_f : isPrimName d.name = false := by
        cases h : isPrimName d.name <;> simp_all
      simp only [HVal.wp, hevh_var, hprim_f]
      refine ⟨Ph, Eh, hcall_spec, fun rw σ' hph => ?_, fun c σ' heh => ?_⟩
      · obtain ⟨pv, rem', wr', rcr', hP, hcln', hvr_d, hnrc_d, hhrs', hcpres, hres'⟩ :=
          hPh rw σ' hph
        have hns_disj : ∀ a, a &&& 1#64 = 0#64 →
            (∀ v ∈ rf.ctx.vars, v.isLive = true → !v.ty.isScalar = true →
              ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some a) →
            ∀ w ∈ nonScalarWords d.params ws, w.toBV64? ≠ some a := by
          intro a heven hall w hw
          refine nonScalarWords_disjoint_aux hrc.2.2.2.1 hpts.symm hlive_as
            (by simpa [hpts] using hmt) hevh heven ?_ w hw
          intro v hv hlv hns w0 hhw0
          exact hall v hv hlv (by simpa using hns) w0 hhw0
        have hsh_p : ∀ p ∈ rf.ctx.sharedPreds, match rf.ctx.get? p.1, rf.ctx.get? p.2 with
            | some vb, some vt =>
              (!vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 ||
                vt.excl && as.all fun x => x != .var p.2) = true
            | _, _ => true = true := by
          intro p hp
          have hm := List.all_eq_true.mp hshpreds p hp
          cases hb : rf.ctx.get? p.1 <;> cases ht : rf.ctx.get? p.2 <;> simp_all
        have hex_u : ∀ u ∈ ctx1.vars, u.excl = true → ∀ a ∈ as, match a with
            | .erased => True
            | .var z => match rf.ctx.get? z with
              | some vz => vz.parent? ≠ some u.id ∧ ¬(vz.ty.isScalar = true ∧ vz.ty.width = 64)
              | none => True := by
          intro u hu huex a ha
          have hu_b := List.all_eq_true.mp hex_excl u hu
          simp [huex] at hu_b
          have ha_b := hu_b a ha
          cases a with
          | erased => trivial
          | var z =>
            dsimp only at ha_b ⊢
            cases hgz : rf.ctx.get? z with
            | none => simp
            | some vz =>
              simp only [hgz, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                bne_iff_ne] at ha_b
              refine ⟨ha_b.1, ?_⟩
              rcases ha_b.2 with hns | hnw
              · intro ⟨hsc, _⟩; simp [hns] at hsc
              · intro ⟨_, hw⟩; simp [hw] at hnw
        have hty_compat : ty.isScalar = d.retTy.isScalar ∧ ty.width = d.retTy.width ∧
            (ty.needsRc = d.retTy.needsRc ∨ ty = .tobject ∧ d.retTy = .tagged) ∧
            (ty = .object → d.retTy = .object) ∧ (ty = .tagged → d.retTy = .tagged) := by
          rw [← hrty] at hnr_eq hobj_imp htag_imp hw_eq hsc_eq
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, lcTy_beq_iff]
            at hnr_eq hobj_imp htag_imp
          exact ⟨hsc_eq, hw_eq, hnr_eq, hobj_imp, htag_imp⟩
        have hpost := rcInv_after_call (rty := d.retTy) hrc hcl hpo hhih happ hfr
          (by simpa [hbrs] using hnost) (by simpa [hbrs] using hnoex) hsh_p hex_u hty_compat
          hevh (nonScalarWords_subset (ps := d.params) (ws := ws)) hns_disj hcln' hvr_d hnrc_d
          (by simpa [calleeRf, calleeExtH, entryRcFrame, List.append_assoc] using hhrs')
          (by simpa [calleeRf, calleeExtH, entryRcFrame, List.append_assoc] using hcpres)
        rcases hpost with ⟨hrc_p, hcl_p, hpo_p, hhih_p, hisol_p, hvr_p⟩
        have hep_p := entryPres_afterCall (rty := d.retTy) (pv := pv) (rw := rw)
          hrc.2.1 hcl hrc.1.1.2.1 hcln'.1.2.1 happ hfr hty_compat.1 hnrc_d
          (by simpa [calleeRf, calleeExtH, entryRcFrame, List.append_assoc] using hhrs')
          (by simpa [calleeRf, calleeExtH, entryRcFrame, List.append_assoc] using hcpres.1)
          hisol_p hep
        let rf_p : RcFrame :=
          ⟨ctx1.bindOwned x ty, rf.envP.set x pv, rf.envH.set x ty rw, rf.extH, rf.ghostH⟩
        have hpcb_p := parentChildBacked_after_call (ty := ty) (pv := pv) (rw := rw)
          hrc.2.1 hcl hpcb happ hpo1 hcl1 hfr hrc.1
          (by simpa [calleeRf, calleeExtH, entryRcFrame, List.append_assoc] using hcpres.1)
        have hno_p := noRcCorrect_bindOwned (applyArgs_nodup hrc.2.1 happ)
          (noRcCorrect_applyArgs hrc.2.1 hno as borrows happ) x ty false false false
        have hsb_p := sharedBool_applyArgs_bindOwned hrc.2.1 hsbv hsbp happ hfr ty
        have hex_p := exclCtorHeap_applyArgs_bindOwned (x := x) (ty := ty) (pv := pv) (w := rw)
          hrc.2.1 hex happ
        have hsth_p := sharedTargetsHeap_applyArgs_bindOwned (ty := ty) (pv := pv) (w := rw)
          hrc.2.1 hcl hsth happ hfr
        have hsh_p' := shadowOk_applyArgs_bindOwned (x := x) (ty := ty) (pv := pv)
          hrc.2.1 hsh happ
        have hj_rw : Word.toWidth ty.width rw = some rw := word_toWidth_eq_self hvr_p
        refine ⟨rw, hj_rw, hk (rf' := rf_p) (ρP' := ρP.set x pv) (pv := pv) (rw := rw)
          (hPK pv rem' wr' rcr' hP) rfl rfl rfl rfl
          (fun z hz => by simp [rf_p, PValEnv.set, HValEnv.set, hz])
          hrc_p hcl_p hpo_p hno_p hpcb_p hsth_p hhih_p hep_p
          hsb_p.1 hsb_p.2 hex_p hsh_p' hres'⟩
      · obtain ⟨cn, rem', wr', rcr', hE, rfl⟩ := hEh c σ' heh
        exact hx (hEX cn rem' wr' rcr' hE)
