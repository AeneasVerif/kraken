module

-- Ported from bedrock2/src/bedrock2/{Semantics,Loops,Memory}.v at mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13

public import Kraken.Bedrock2.Semantics
public import Kraken.SeparationMem
import all Kraken.Separation

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2

attribute [simp, grind =] ofBytes_toBytes Int.toBytes_ofBytes_all Int.toBytes_length

variable {w : Nat} {ext : ExtSpec w} {e : Env}

theorem split_iff_sep {m m1 m2 : Mem w} : split m m1 m2 ↔ (m =⋆ Eq m1 ⋆ Eq m2) :=
  ⟨fun ⟨hu, hi⟩ => ⟨m1, m2, hu, hi, rfl, rfl⟩, fun ⟨_, _, hu, hi, rfl, rfl⟩ => ⟨hu, hi⟩⟩

theorem shamt_small (hw : w = 32 ∨ w = 64) {k : Nat} (hk : k < w) : k % 2 ^ Nat.log2 w = k := by
  rcases hw with rfl | rfl <;> exact Nat.mod_eq_of_lt (by simpa using hk)

theorem shamt_ofNat_small (hw : w = 32 ∨ w = 64) {k : Nat} (hk : k < w) :
    shamt (BitVec.ofNat w k) = k := by
  have hk' : k < 2 ^ w := Nat.lt_of_lt_of_le hk (Nat.le_of_lt (Nat.lt_two_pow_self))
  rw [shamt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk', shamt_small hw hk]

theorem unsigned_slu_shamtZ (hw : w = 32 ∨ w = 64) (x : BitVec w) {n : Nat} (hn : n < w) :
    (interpBinop .slu x (BitVec.ofNat w n)).toNat = (x.toNat <<< n) % 2 ^ w := by
  rw [interpBinop, shamt_ofNat_small hw hn, BitVec.toNat_shiftLeft]

theorem unsigned_sru_shamtZ (hw : w = 32 ∨ w = 64) (x : BitVec w) {n : Nat} (hn : n < w) :
    (interpBinop .sru x (BitVec.ofNat w n)).toNat = x.toNat >>> n := by
  rw [interpBinop, shamt_ofNat_small hw hn, BitVec.toNat_ushiftRight]

theorem signed_srs_shamtZ (hw : w = 32 ∨ w = 64) (x : BitVec w) {n : Nat} (hn : n < w) :
    (interpBinop .srs x (BitVec.ofNat w n)).toInt = x.toInt >>> n := by
  rw [interpBinop, shamt_ofNat_small hw hn, BitVec.toInt_sshiftRight]

theorem Exec.weaken {c t m l} {post1 post2 : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e c t m l post1) (himpl : ∀ t' m' l', post1 t' m' l' → post2 t' m' l') :
    Exec ext e c t m l post2 := by
  induction h generalizing post2 with
  | skip => exact .skip _ _ _ _ (himpl _ _ _ ‹_›)
  | set _ _ _ _ _ _ _ hv hp => exact .set _ _ _ _ _ _ _ hv (himpl _ _ _ hp)
  | unset _ _ _ _ _ hp => exact .unset _ _ _ _ _ (himpl _ _ _ hp)
  | store _ _ _ _ _ _ _ _ _ _ ha hv hs hp => exact .store _ _ _ _ _ _ _ _ _ _ ha hv hs (himpl _ _ _ hp)
  | stackalloc _ _ _ _ _ _ _ _ ih =>
    exact .stackalloc _ _ _ _ _ _ _ fun a ms mc ha hs => ih a ms mc ha hs
      fun _ _ _ ⟨s, st, h1, h2, h3⟩ => ⟨s, st, h1, h2, himpl _ _ _ h3⟩
  | if_true _ _ _ _ _ _ _ _ hv hnz _ ih => exact .if_true _ _ _ _ _ _ _ _ hv hnz (ih himpl)
  | if_false _ _ _ _ _ _ _ _ hv hz _ ih => exact .if_false _ _ _ _ _ _ _ _ hv hz (ih himpl)
  | seq _ _ _ _ _ _ _ h1 _ _ ih2 => exact .seq _ _ _ _ _ _ _ h1 fun _ _ _ hm => ih2 _ _ _ hm himpl
  | while_false _ _ _ _ _ _ _ hv hz hp => exact .while_false _ _ _ _ _ _ _ hv hz (himpl _ _ _ hp)
  | while_true _ _ _ _ _ _ _ _ hv hnz hc _ _ ih2 =>
    exact .while_true _ _ _ _ _ _ _ _ hv hnz hc fun _ _ _ hm => ih2 _ _ _ hm himpl
  | call _ _ _ _ _ _ _ _ _ _ _ hf ha hl hb hk _ =>
    refine .call _ _ _ _ _ _ _ _ _ _ _ hf ha hl hb fun _ _ _ hm => ?_
    obtain ⟨rv, hrv, l', hl', hp⟩ := hk _ _ _ hm
    exact ⟨rv, hrv, l', hl', himpl _ _ _ hp⟩
  | interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx hk =>
    refine .interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx fun _ _ hm => ?_
    obtain ⟨l', hl', hp⟩ := hk _ _ hm
    exact ⟨l', hl', fun m' hm' => himpl _ _ _ (hp m' hm')⟩

theorem Exec.seq_cps {c1 c2 t m l post} :
    Exec ext e c1 t m l (fun t' m' l' => Exec ext e c2 t' m' l' post) →
    Exec ext e (.seq c1 c2) t m l post :=
  fun h => .seq _ _ _ _ _ _ _ h fun _ _ _ => id

theorem Exec.interact_cps {binds action arges args t m l post mKeep mGive} :
    split m mKeep mGive →
    evalArgs m l arges = some args →
    ext t mGive action args (fun mReceive resvals =>
      ∃ l', putManyZip binds resvals l = some l' ∧
      ∀ m', split m' mKeep mReceive →
      post (((mGive, action, args), (mReceive, resvals)) :: t) m' l') →
    Exec ext e (.interact binds action arges) t m l post :=
  fun hs ha hx => .interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx fun _ _ => id

theorem Exec.cond_cps {ec c1 c2 t m l post v} :
    ec.eval m l = some v →
    (v ≠ 0 → Exec ext e c1 t m l post) →
    (v = 0 → Exec ext e c2 t m l post) →
    Exec ext e (.cond ec c1 c2) t m l post := fun hv h1 h2 =>
  if hz : v = 0 then .if_false _ _ _ _ _ _ _ _ hv hz (h2 hz)
  else .if_true _ _ _ _ _ _ _ _ hv hz (h1 hz)

theorem Exec.while_true_cps {ec c t m l post v} :
    ec.eval m l = some v → v ≠ 0 →
    Exec ext e c t m l (fun t' m' l' => Exec ext e (.while ec c) t' m' l' post) →
    Exec ext e (.while ec c) t m l post :=
  fun hv hnz h => .while_true _ _ _ _ _ _ _ _ hv hnz h fun _ _ _ => id

theorem Exec.set_cps {x ex t m l post v} (hv : ex.eval m l = some v)
    (h : post t m (l.insert x v)) : Exec ext e (.set x ex) t m l post :=
  .set _ _ _ _ _ _ _ hv h

theorem Exec.store_cps {sz ea ev t m l post a v m'} (ha : ea.eval m l = some a)
    (hv : ev.eval m l = some v) (hs : store? sz m a v = some m') (h : post t m' l) :
    Exec ext e (.store sz ea ev) t m l post :=
  .store _ _ _ _ _ _ _ _ _ _ ha hv hs h

theorem Exec.stackalloc_cps {x n body t mSmall l post}
    (h : ∀ a mStack mCombined, anybytes a n mStack → split mCombined mSmall mStack →
      Exec ext e body t mCombined (l.insert x a) fun t' mCombined' l' =>
        ∃ mSmall' mStack', anybytes a n mStack' ∧ split mCombined' mSmall' mStack' ∧
          post t' mSmall' l') :
    Exec ext e (.stackalloc x n body) t mSmall l post :=
  .stackalloc _ _ _ _ _ _ _ h

@[simp high] theorem Locals.getElem?_insert (l : Locals w) (k a : String) (v : BitVec w) :
    (l.insert k v)[a]? = if k = a then some v else l[a]? := by
  simp [ExtHashMap.getElem?_insert]

@[simp] theorem putManyZip_nil (l : Locals w) : putManyZip [] [] l = some l := by
  simp [putManyZip]

@[simp] theorem putManyZip_cons (k : String) (ks : List String) (v : BitVec w)
    (vs : List (BitVec w)) (l : Locals w) :
    putManyZip (k :: ks) (v :: vs) l = putManyZip ks vs (l.insert k v) := by
  simp [putManyZip, insertMany_cons]

@[simp] theorem getMany_nil (l : Locals w) : getMany l [] = some [] := rfl

private theorem anybytes_unique_domain {a : BitVec w} {n : Nat} {m1 m2 : Mem w}
    (h1 : anybytes a n m1) (h2 : anybytes a n m2) : ∀ k, k ∈ m1 ↔ k ∈ m2 := by
  obtain ⟨bs1, rfl, hl1, -⟩ := h1
  obtain ⟨bs2, rfl, hl2, -⟩ := h2
  intro k
  simp [mem_At_iff, hl1, hl2]

private theorem split_diff {m a1 b1 a2 b2 : Mem w} (h1 : split m a1 b1) (h2 : split m a2 b2)
    (hd : ∀ k, k ∈ b1 ↔ k ∈ b2) : a1 = a2 ∧ b1 = b2 := by
  obtain ⟨hu1, hi1⟩ := h1
  obtain ⟨hu2, hi2⟩ := h2
  have hi1 := eq_empty_iff_forall_not_mem.mp hi1
  have hi2 := eq_empty_iff_forall_not_mem.mp hi2
  have hm := fun k : BitVec w => congrArg (fun x : Mem w => x[k]?) (hu1.trans hu2.symm)
  simp only [inter_eq, mem_inter_iff, union_eq, getElem?_union] at hi1 hi2 hm
  constructor <;> apply ext_getElem? <;> intro k <;>
    have hmk := hm k <;> have hdk := hd k <;> have h1k := hi1 k <;> have h2k := hi2 k <;>
    simp only [mem_iff_isSome_getElem?] at hdk h1k h2k <;> revert hmk hdk h1k h2k <;>
    cases a1[k]? <;> cases b1[k]? <;> cases a2[k]? <;> cases b2[k]? <;> simp

theorem Exec.intersect (hext : ExtSpec.Ok ext) {c t m l}
    {post1 post2 : Trace w → Mem w → Locals w → Prop}
    (h1 : Exec ext e c t m l post1) (h2 : Exec ext e c t m l post2) :
    Exec ext e c t m l (fun t' m' l' => post1 t' m' l' ∧ post2 t' m' l') := by
  induction h1 generalizing post2 with
  | skip _ _ _ _ hp => cases h2 with | skip _ _ _ _ hp' => exact .skip _ _ _ _ ⟨hp, hp'⟩
  | set _ _ _ _ _ _ _ hv hp =>
    cases h2 with | set _ _ _ _ _ _ _ hv' hp' =>
    cases hv.symm.trans hv'
    exact .set _ _ _ _ _ _ _ hv ⟨hp, hp'⟩
  | unset _ _ _ _ _ hp => cases h2 with | unset _ _ _ _ _ hp' => exact .unset _ _ _ _ _ ⟨hp, hp'⟩
  | store _ _ _ _ _ _ _ _ _ _ ha hv hs hp =>
    cases h2 with | store _ _ _ _ _ _ _ _ _ _ ha' hv' hs' hp' =>
    cases ha.symm.trans ha'; cases hv.symm.trans hv'; cases hs.symm.trans hs'
    exact .store _ _ _ _ _ _ _ _ _ _ ha hv hs ⟨hp, hp'⟩
  | stackalloc _ _ _ _ _ _ _ _ ih =>
    cases h2 with | stackalloc _ _ _ _ _ _ _ hb' =>
    refine .stackalloc _ _ _ _ _ _ _ fun a ms mc ha hs => (ih a ms mc ha hs (hb' a ms mc ha hs)).weaken ?_
    rintro _ _ _ ⟨⟨s1, st1, ha1, hs1, hp1⟩, ⟨s2, st2, ha2, hs2, hp2⟩⟩
    obtain ⟨rfl, rfl⟩ := split_diff hs1 hs2 (anybytes_unique_domain ha1 ha2)
    exact ⟨s1, st1, ha1, hs1, hp1, hp2⟩
  | if_true _ _ _ _ _ _ _ _ hv hnz _ ih =>
    cases h2 with
    | if_true _ _ _ _ _ _ _ _ _ _ hc' => exact .if_true _ _ _ _ _ _ _ _ hv hnz (ih hc')
    | if_false _ _ _ _ _ _ _ _ hv' hz' _ => exact absurd (Option.some.inj (hv.symm.trans hv') ▸ hz') hnz
  | if_false _ _ _ _ _ _ _ _ hv hz _ ih =>
    cases h2 with
    | if_true _ _ _ _ _ _ _ _ hv' hnz' _ => exact absurd (Option.some.inj (hv.symm.trans hv') ▸ hz) hnz'
    | if_false _ _ _ _ _ _ _ _ _ _ hc' => exact .if_false _ _ _ _ _ _ _ _ hv hz (ih hc')
  | seq _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    cases h2 with | seq _ _ _ _ _ _ _ hc1' hc2' =>
    exact .seq _ _ _ _ _ _ _ (ih1 hc1') fun _ _ _ ⟨hm, hm'⟩ => ih2 _ _ _ hm (hc2' _ _ _ hm')
  | while_false _ _ _ _ _ _ _ hv hz hp =>
    cases h2 with
    | while_false _ _ _ _ _ _ _ _ _ hp' => exact .while_false _ _ _ _ _ _ _ hv hz ⟨hp, hp'⟩
    | while_true _ _ _ _ _ _ _ _ hv' hnz' _ _ =>
      exact absurd (Option.some.inj (hv.symm.trans hv') ▸ hz) hnz'
  | while_true _ _ _ _ _ _ _ _ hv hnz _ _ ih1 ih2 =>
    cases h2 with
    | while_false _ _ _ _ _ _ _ hv' hz' _ =>
      exact absurd (Option.some.inj (hv.symm.trans hv') ▸ hz') hnz
    | while_true _ _ _ _ _ _ _ _ _ _ hc' hk' =>
      exact .while_true _ _ _ _ _ _ _ _ hv hnz (ih1 hc') fun _ _ _ ⟨hm, hm'⟩ => ih2 _ _ _ hm (hk' _ _ _ hm')
  | call _ _ _ _ _ _ _ _ _ _ _ hf ha hl _ hk ih =>
    cases h2 with | call _ _ _ _ _ _ _ _ _ _ _ hf' ha' hl' hb' hk' =>
    cases hf.symm.trans hf'; cases ha.symm.trans ha'; cases hl.symm.trans hl'
    refine .call _ _ _ _ _ _ _ _ _ _ _ hf ha hl (ih hb') fun _ _ _ ⟨hm, hm'⟩ => ?_
    obtain ⟨rv, hrv, l', hl1, hp⟩ := hk _ _ _ hm
    obtain ⟨rv', hrv', l'', hl2, hp'⟩ := hk' _ _ _ hm'
    cases hrv.symm.trans hrv'; cases hl1.symm.trans hl2
    exact ⟨rv, hrv, l', hl1, hp, hp'⟩
  | interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx hk =>
    cases h2 with | interact _ _ _ _ _ _ _ _ _ _ _ hs' ha' hx' hk' =>
    cases ha.symm.trans ha'
    obtain rfl := hext.mGive_unique _ _ _ _ _ _ _ _ _ _ hs hs' hx hx'
    obtain ⟨rfl, -⟩ := split_diff hs hs' fun _ => Iff.rfl
    refine .interact _ _ _ _ _ _ _ _ _ _ _ hs ha (hext.intersect _ _ _ _ _ _ hx hx')
      fun _ _ ⟨hm, hm'⟩ => ?_
    obtain ⟨l', hl1, hp⟩ := hk _ _ hm
    obtain ⟨l'', hl2, hp'⟩ := hk' _ _ hm'
    cases hl1.symm.trans hl2
    exact ⟨l', hl1, fun m' hm' => ⟨hp m' hm', hp' m' hm'⟩⟩

def Env.Extends (e2 e1 : Env) : Prop :=
  ∀ f fn, e1.lookup f = some fn → e2.lookup f = some fn

theorem Exec.extend_env {e1 e2 : Env} (hext : e2.Extends e1) {c t m l post}
    (h : Exec ext e1 c t m l post) : Exec ext e2 c t m l post := by
  induction h with
  | skip _ _ _ _ hp => exact .skip _ _ _ _ hp
  | set _ _ _ _ _ _ _ hv hp => exact .set _ _ _ _ _ _ _ hv hp
  | unset _ _ _ _ _ hp => exact .unset _ _ _ _ _ hp
  | store _ _ _ _ _ _ _ _ _ _ ha hv hs hp => exact .store _ _ _ _ _ _ _ _ _ _ ha hv hs hp
  | stackalloc _ _ _ _ _ _ _ _ ih => exact .stackalloc _ _ _ _ _ _ _ ih
  | if_true _ _ _ _ _ _ _ _ hv hnz _ ih => exact .if_true _ _ _ _ _ _ _ _ hv hnz ih
  | if_false _ _ _ _ _ _ _ _ hv hz _ ih => exact .if_false _ _ _ _ _ _ _ _ hv hz ih
  | seq _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .seq _ _ _ _ _ _ _ ih1 ih2
  | while_false _ _ _ _ _ _ _ hv hz hp => exact .while_false _ _ _ _ _ _ _ hv hz hp
  | while_true _ _ _ _ _ _ _ _ hv hnz _ _ ih1 ih2 => exact .while_true _ _ _ _ _ _ _ _ hv hnz ih1 ih2
  | call _ _ _ _ _ _ _ _ _ _ _ hf ha hl _ hk ih =>
    exact .call _ _ _ _ _ _ _ _ _ _ _ (hext _ _ hf) ha hl ih hk
  | interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx hk => exact .interact _ _ _ _ _ _ _ _ _ _ _ hs ha hx hk

def call (ext : ExtSpec w) (e : Env) (fname : String) (t : Trace w) (m : Mem w)
    (args : List (BitVec w)) (post : Trace w → Mem w → List (BitVec w) → Prop) : Prop :=
  ∃ f, e.lookup fname = some f ∧ ∃ l, putManyZip f.params args ∅ = some l ∧
    Exec ext e f.body t m l fun t' m' l' => ∃ rets, getMany l' f.rets = some rets ∧ post t' m' rets

theorem call.of_body {fname t m args post f l} (hf : e.lookup fname = some f)
    (hl : putManyZip f.params args ∅ = some l)
    (hb : Exec ext e f.body t m l fun t' m' l' =>
      ∃ rets, getMany l' f.rets = some rets ∧ post t' m' rets) :
    call ext e fname t m args post :=
  ⟨f, hf, l, hl, hb⟩

theorem call.weaken {fname t m args} {post1 post2 : Trace w → Mem w → List (BitVec w) → Prop}
    (h : call ext e fname t m args post1)
    (himpl : ∀ t' m' rets, post1 t' m' rets → post2 t' m' rets) :
    call ext e fname t m args post2 :=
  let ⟨f, hf, l, hl, hb⟩ := h
  ⟨f, hf, l, hl, hb.weaken fun _ _ _ ⟨rets, hr, hp⟩ => ⟨rets, hr, himpl _ _ _ hp⟩⟩

theorem call.extend_env {e1 e2 : Env} (hext : e2.Extends e1) {fname t m args post}
    (h : call ext e1 fname t m args post) : call ext e2 fname t m args post :=
  let ⟨f, hf, l, hl, hb⟩ := h
  ⟨f, hext _ _ hf, l, hl, hb.extend_env hext⟩

theorem Exec.call_cps {binds fname arges t m l post args} :
    evalArgs m l arges = some args →
    Bedrock2.call ext e fname t m args (fun t' m' rets =>
      ∃ l', putManyZip binds rets l = some l' ∧ post t' m' l') →
    Exec ext e (.call binds fname arges) t m l post := fun ha ⟨_, hf, _, hl, hb⟩ =>
  .call _ _ _ _ _ _ _ _ _ _ _ hf ha hl hb fun _ _ _ ⟨rets, hr, l', hl', hp⟩ => ⟨rets, hr, l', hl', hp⟩

universe u v

theorem Exec.while_wf {ec : Expr} {c : Cmd} {t m l} {post : Trace w → Mem w → Locals w → Prop}
    {Measure : Sort u} {lt : Measure → Measure → Prop} (hwf : WellFounded lt)
    (inv : Measure → Trace w → Mem w → Locals w → Prop) (v0 : Measure) (hinit : inv v0 t m l)
    (hbody : ∀ v t m l, inv v t m l → ∃ b, ec.eval m l = some b ∧
      (b ≠ 0 → Exec ext e c t m l fun t' m' l' => ∃ v', inv v' t' m' l' ∧ lt v' v) ∧
      (b = 0 → post t m l)) :
    Exec ext e (.while ec c) t m l post := by
  induction v0 using hwf.induction generalizing t m l with
  | _ v ih =>
  obtain ⟨b, hb, ht, hf⟩ := hbody v t m l hinit
  if hz : b = 0 then exact .while_false _ _ _ _ _ _ _ hb hz (hf hz)
  else exact .while_true _ _ _ _ _ _ _ _ hb hz (ht hz) fun _ _ _ ⟨v', hv', hlt⟩ => ih v' hlt hv'

theorem Exec.tailrec {ec : Expr} {c : Cmd} {t m l} {post : Trace w → Mem w → Locals w → Prop}
    {Measure : Sort u} {Ghost : Sort v}
    (P Q : Measure → Ghost → Trace w → Mem w → Locals w → Prop)
    (lt : Measure → Measure → Prop) (hwf : WellFounded lt) (v0 : Measure) (g0 : Ghost)
    (hpre : P v0 g0 t m l)
    (hbody : ∀ v g t m l, P v g t m l → ∃ br, ec.eval m l = some br ∧
      (br ≠ 0 → Exec ext e c t m l fun t' m' l' => ∃ v' g', P v' g' t' m' l' ∧ lt v' v ∧
        ∀ t'' m'' l'', Q v' g' t'' m'' l'' → Q v g t'' m'' l'') ∧
      (br = 0 → Q v g t m l))
    (hpost : ∀ t m l, Q v0 g0 t m l → post t m l) :
    Exec ext e (.while ec c) t m l post := by
  refine Exec.while_wf hwf
    (fun v t m l => ∃ g, P v g t m l ∧ ∀ t'' m'' l'', Q v g t'' m'' l'' → Q v0 g0 t'' m'' l'')
    v0 ⟨g0, hpre, fun _ _ _ => id⟩ ?_
  rintro v t m l ⟨g, hP, hQ⟩
  obtain ⟨br, hbr, ht, hf⟩ := hbody v g t m l hP
  refine ⟨br, hbr, fun hnz => (ht hnz).weaken ?_, fun hz => hpost _ _ _ (hQ _ _ _ (hf hz))⟩
  rintro _ _ _ ⟨v', g', hP', hlt, hQ'⟩
  exact ⟨v', ⟨g', hP', fun _ _ _ h => hQ _ _ _ (hQ' _ _ _ h)⟩, hlt⟩

theorem load?_sep {sz : AccessSize} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    {R : Mem w → Prop} (hsep : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = sz.bytes)
    (hw : sz.bytes ≤ 2 ^ w) :
    load? sz m a = some (.ofInt w (Int.ofBytes bs)) := by
  simp [load?, Mem.loadInt_sep bs a _ R m hsep hl hw]

theorem store?_eq {sz : AccessSize} {m : Mem w} {a v : BitVec w} {bs : List UInt8}
    {R : Mem w → Prop} (hsep : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = sz.bytes)
    (hw : sz.bytes ≤ 2 ^ w) :
    store? sz m a v = some (m.storeInt a sz.bytes v.toNat) := by
  simp [store?, Mem.loadBytes_sep bs a _ R m hsep hl hw]

theorem storeInt_sep {sz : AccessSize} {m : Mem w} {a v : BitVec w} {bs : List UInt8}
    {R : Mem w → Prop} (hsep : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = sz.bytes) :
    m.storeInt a sz.bytes v.toNat =⋆ Eq ((Int.toBytes sz.bytes v.toNat).At a) ⋆ R :=
  Mem.storeInt_sep a _ bs R m ⟨hsep, hl⟩ _

theorem store?_sep {sz : AccessSize} {m : Mem w} {a v : BitVec w} {bs : List UInt8}
    {R : Mem w → Prop} (hsep : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = sz.bytes)
    (hw : sz.bytes ≤ 2 ^ w) :
    ∃ m', store? sz m a v = some m' ∧ (m' =⋆ Eq ((Int.toBytes sz.bytes v.toNat).At a) ⋆ R) :=
  ⟨_, store?_eq hsep hl hw, storeInt_sep hsep hl⟩

@[simp, grind =] theorem toBytes_toNat_ofInt_ofBytes {bs : List UInt8} (hw : 8 * bs.length ≤ w) :
    Int.toBytes bs.length ((BitVec.ofInt w (Int.ofBytes bs)).toNat : Int) = bs := by
  have := Int.ofBytes_ge_zero bs
  have := Int.ofBytes_lt bs
  have : (256 : Nat) ^ bs.length ≤ 2 ^ w :=
    (Nat.pow_mul 2 8 bs.length).symm ▸ Nat.pow_le_pow_right (by decide) hw
  have : ((256 ^ bs.length : Nat) : Int) = (256 : Int) ^ bs.length := Int.natCast_pow _ _
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega),
    Int.toBytes_ofBytes_all]

theorem bytes_ofWidth (hw : w = 32 ∨ w = 64) : (AccessSize.ofWidth w).bytes = w / 8 := by
  obtain rfl | rfl := hw <;> rfl

theorem bytes_ofWidth_le (hw : w = 32 ∨ w = 64) : (AccessSize.ofWidth w).bytes ≤ 2 ^ w := by
  obtain rfl | rfl := hw <;> decide

@[simp, grind =] theorem toBytes_one (v : BitVec w) :
    Int.toBytes AccessSize.one.bytes (v.toNat : Int) = [v.toNat.toUInt8] := by
  simp [AccessSize.bytes, Int.toBytes, Int.take]
  grind

@[simp, grind =] theorem ofBytes_singleton (b : UInt8) :
    Int.ofBytes [b] = b.toNat := by
  simp [Int.ofBytes]

theorem ofInt_ofBytes_byte (hw : 8 ≤ w) (x : BitVec w) :
    BitVec.ofInt w (Int.ofBytes [x.toNat.toUInt8]) = x &&& 0xff := by
  have : 256 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have := Nat.and_two_pow_sub_one_eq_mod x.toNat 8
  exact BitVec.eq_of_toNat_eq (by grind)

theorem toNat_sub_one {x : BitVec w} (h : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hlt := x.isLt
  have hw : 0 < w := Nat.pos_of_ne_zero fun hw => by subst hw; simp at hlt; omega
  have h1 : (1 : BitVec w).toNat = 1 := BitVec.toNat_one hw
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]

theorem Exec.store_sep {sz ea ev t m l post a v} {bs : List UInt8} {R : Mem w → Prop}
    (ha : ea.eval m l = some a) (hv : ev.eval m l = some v)
    (hsep : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = sz.bytes) (hw : sz.bytes ≤ 2 ^ w)
    (h : ∀ m', (m' =⋆ Eq ((Int.toBytes sz.bytes v.toNat).At a) ⋆ R) → post t m' l) :
    Exec ext e (.store sz ea ev) t m l post :=
  .store_cps ha hv (store?_eq hsep hl hw) (h _ (storeInt_sep hsep hl))

theorem At_cons_sep (b : UInt8) (bs : List UInt8) (a : BitVec w) (h : bs.length + 1 ≤ 2 ^ w) :
    Eq ((b :: bs).At a) = Eq ([b].At a) ⋆ Eq (bs.At (a + 1)) := by
  have := Mem.At_append_sep [b] bs a (by simp only [List.length_singleton]; omega)
  rwa [List.singleton_append, List.length_singleton] at this

end Kraken.Bedrock2
