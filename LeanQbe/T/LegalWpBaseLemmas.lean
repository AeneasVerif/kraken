module

public import LeanQbe.T.LegalWpBaseLemmas2

/-!
# Legalization semantic preservation relational tree `_wp` lemmas (`T5`, Part 1c)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp

/-! ### Relational tree weakest-precondition specs -/

def TreeRel1 (onB : Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → (Val u → Prop) → Prop
  | .bool, x, post => onB x post
  | .bits n, x, post => onBits n x post
  | .float f, x, post => onF f x post
  | .pair a b, p, post =>
    TreeRel1 onB onBits onF a p.1 fun r1 =>
    TreeRel1 onB onBits onF b p.2 fun r2 => post (r1, r2)

theorem TreeRel1.mono {onB onBits onF}
    (hB : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBits : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x p → onBits n x q)
    (hF : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ {u : Ty} {x : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel1 onB onBits onF u x p → TreeRel1 onB onBits onF u x q
  | .bool, _, _, _, hpq, h => hB _ hpq h
  | .bits n, _, _, _, hpq, h => hBits n _ hpq h
  | .float f, _, _, _, hpq, h => hF f _ hpq h
  | .pair a b, (_, _), _, _, hpq, h =>
    TreeRel1.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel1.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

def TreeRel2 (onB : Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, post => onB x y post
  | .bits n, x, y, post => onBits n x y post
  | .float f, x, y, post => onF f x y post
  | .pair a b, p, q, post =>
    TreeRel2 onB onBits onF a p.1 q.1 fun r1 =>
    TreeRel2 onB onBits onF b p.2 q.2 fun r2 => post (r1, r2)

theorem TreeRel2.mono {onB onBits onF}
    (hB : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBits : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y p → onBits n x y q)
    (hF : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p →
      onF f x y q) :
    ∀ {u : Ty} {x y : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel2 onB onBits onF u x y p → TreeRel2 onB onBits onF u x y q
  | .bool, _, _, _, _, hpq, h => hB _ _ hpq h
  | .bits n, _, _, _, _, hpq, h => hBits n _ _ hpq h
  | .float f, _, _, _, _, hpq, h => hF f _ _ hpq h
  | .pair a b, (_, _), (_, _), _, _, hpq, h =>
    TreeRel2.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel2.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

def TreeRel3 (onB : Bool → Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) →
      Prop) :
    (u : Ty) → Val u → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, z, post => onB x y z post
  | .bits n, x, y, z, post => onBits n x y z post
  | .float f, x, y, z, post => onF f x y z post
  | .pair a b, p, q, r, post =>
    TreeRel3 onB onBits onF a p.1 q.1 r.1 fun r1 =>
    TreeRel3 onB onBits onF b p.2 q.2 r.2 fun r2 => post (r1, r2)

theorem TreeRel3.mono {onB onBits onF}
    (hB : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBits : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y z p →
      onBits n x y z q)
    (hF : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p →
      onF f x y z q) :
    ∀ {u : Ty} {x y z : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel3 onB onBits onF u x y z p → TreeRel3 onB onBits onF u x y z q
  | .bool, _, _, _, _, _, hpq, h => hB _ _ _ hpq h
  | .bits n, _, _, _, _, _, hpq, h => hBits n _ _ _ hpq h
  | .float f, _, _, _, _, _, hpq, h => hF f _ _ _ hpq h
  | .pair a b, (_, _), (_, _), (_, _), _, _, hpq, h =>
    TreeRel3.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel3.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

private theorem legalUnaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx : Tup (Arg Val) (target.leafTys u)) (x : Val u), valsTup fx = leafVals target u x →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel1 onB onBi onF u x (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalUnaryTree.goS target onBool onBits onFloat u fx k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, x, hx, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx hx
    dsimp only [legalUnaryTree.goS]
    have h12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at h12
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1 x.1
      (congrArg Prod.fst h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2 x.2
      (congrArg Prod.snd h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalUnaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (mkCode u) (x, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (t : Ty), target.supportsTy t = true → (xs : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup xs = encodeVal target t x →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel1 onB onBi onF t x (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, p, hxs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalUnaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      simp only [valsTup, Tup.map] at hxt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op1]
        rw [hxt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (p, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) p _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs
          p hxs fun fx hfx => ?_
        refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2)
          (by simp [LegalTarget.supportsTy, ht]) fx p hfx _ m ?_
        refine TreeRel1.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres
          res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1 (tupSplit (splitToTup hf xs)).1 p.1
        (congrArg Prod.fst h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2 (tupSplit (splitToTup hf xs)).2 p.2
        (congrArg Prod.snd h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem treeRel1_bswap {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hBi : ∀ n (a : BitVec n) (p : BitVec n → Prop), n % 8 = 0 → p (bswapBits a) → onBi n a p) :
    ∀ (u : Ty), u.bswapOk = true → ∀ (x : Val u) (p : Val u → Prop),
      p (lift1 bswapBits id u x) → TreeRel1 onB onBi onF u x p
  | .bool, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .float _, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .bits n, hu, x, p, hp => hBi n x p (beq_iff_eq.mp (by simpa [Ty.bswapOk] using hu)) hp
  | .pair a b, hu, (x1, x2), p, hp => by
    simp only [Ty.bswapOk, Bool.and_eq_true] at hu
    exact treeRel1_bswap hBi a hu.1 x1 _ (treeRel1_bswap hBi b hu.2 x2 _ hp)

theorem legalBswapTree_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true) (hb : t.bswapOk = true)
    (xs : Tup (Arg Val) (target.legalTys t)) (x : Val t) (hxs : valsTup xs = encodeVal target t x)
    {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ res, valsTup res = encodeVal target t (lift1 bswapBits id t x) → wp Γ Q X (k res) m) :
    wp Γ Q X (legalBswapTree target t xs k) m := by
  dsimp only [legalBswapTree]
  simp only [show (!t.bswapOk) = false by simp [hb], Bool.false_eq_true, ↓reduceIte]
  let onB := fun (_ : Bool) (_ : Bool → Prop) => False
  let onBi := fun (n : Nat) (a : BitVec n) (post : BitVec n → Prop) =>
    n % 8 = 0 ∧ post (bswapBits a)
  let onF := fun (f : Fmt) (_ : BitVec f.width) (_ : BitVec f.width → Prop) => False
  have hB : ∀ (x' : Arg Val .bool) (x : Bool) (k : Arg Val .bool → Expr Val Cont rs) (m : Mem 64),
    x'.val = x →
      onB x (fun res => ∀ (r : Arg Val .bool), r.val = res → wp Γ Q X (k r) m) →
        wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ h => False.elim h
  have hBi : ∀ (n : Nat), target.supportsTy (.bits n) = true →
      ∀ (x' : Arg Val (.bits (target.widenWidth n))) (x : BitVec n)
        (k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) (m : Mem 64),
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ (r : Arg Val (.bits (target.widenWidth n))),
        r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (
        if n == 0 then k (.imm 0#(target.widenWidth n))
        else if n == 8 then k x'
        else if n == target.widenWidth n then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw => k (.var bw.1)
        else if target.widenWidth n % 8 == 0 then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw =>
          .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
            (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
          k (.var r.1)
        else .hlt) m := by
    intro n hsn x' a k' m' hax ⟨hn8, hk'⟩
    have hnw := le_widenWidth_of_supports hsn
    have hwSpec := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsn)
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      have ha0 : a = 0#0 := bitVec0_eq_zero a
      subst ha0
      exact hk' _ (by rw [bitVec0_eq_zero (bswapBits 0#0), BitVec.setWidth_zero]; rfl)
    · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn0f : (n == 0) = false := beq_false_of_ne hn0
      simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
      by_cases hn8eq : n = 8
      · subst hn8eq
        simp only [beq_self_eq_true, ↓reduceIte]
        exact hk' x' (by rw [hax, bswapBits_8])
      · have hn8f : (n == 8) = false := beq_false_of_ne hn8eq
        simp only [hn8f, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : n = target.widenWidth n
        · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
          simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op1, vals, lift1, Ty.bswapOk]
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hw8t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          revert x' a k' hax hk'
          rw [← heq]
          intro x' a k' hax hk'
          rw [BitVec.setWidth_eq] at hax hk'
          exact hk' _ (by change bswapBits x'.val = _; rw [hax])
        · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
          have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hneqf, Bool.false_eq_true, ↓reduceIte, hw8t, wp, Op.wp, OpCode.wp, op1, op2,
            vals, lift1, lift2, Ty.bswapOk, Bool.not_true]
          have hpow : target.widenWidth n < 2 ^ target.widenWidth n :=
            @Nat.lt_pow_self (target.widenWidth n) 2 (by decide)
          have hsub_lt : target.widenWidth n - n < 2 ^ target.widenWidth n :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
          have hsh : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat %
              target.widenWidth n = target.widenWidth n - n := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
          exact hk' _ (by
            change (bswapBits x'.val) >>> ((BitVec.ofNat (target.widenWidth n)
              (target.widenWidth n - n)).toNat % target.widenWidth n) = _
            rw [hax, hsh, setWidth_bswap_of_lt hn0pos hlt hn8 hwSpec.2.1])
  have hF : ∀ (f : Fmt), target.supportsTy (.float f) = true →
      ∀ (x' : Arg Val (.float f)) (x : BitVec f.width)
        (k : Arg Val (.float f) → Expr Val Cont rs) (m : Mem 64), x'.val = x →
      onF f x (fun res => ∀ (r : Arg Val (.float f)), r.val = res → wp Γ Q X (k r) m) →
        wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ _ _ h => False.elim h
  have hVec : ∀ u, target.keepsPacked u = true → false = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (.bswap u) (x, ()) (fun (res, ()) => p res) :=
    fun _ _ hc => by cases hc
  exact legalUnaryTree_wp target .bswap (fun _ => false) (fun _ _ => .hlt)
    (fun n x cont =>
      if n == 0 then cont (.imm 0#(target.widenWidth n))
      else if n == 8 then cont x
      else if n == target.widenWidth n then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw => cont (.var bw.1)
      else if target.widenWidth n % 8 == 0 then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw =>
        .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
          (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
        cont (.var r.1)
      else .hlt)
    (fun _ _ _ => .hlt)
    hB hBi hF hVec (fun _ _ _ _ h => False.elim h) (fun n _ _ _ h1 h2 => ⟨h2.1, h1 _ h2.2⟩)
    (fun _ _ _ _ _ h => False.elim h)
    t ht xs x hxs k m
    (treeRel1_bswap (fun _ _ _ hn8 hp => ⟨hn8, hp⟩) t hb x _ hk)

private theorem legalTernaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) →
      Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p →
      onF f x y z q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy fz : Tup (Arg Val) (target.leafTys u)) (x y z : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        valsTup fz = leafVals target u z →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel3 onB onBi onF u x y z (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalTernaryTree.goS target onBool onBits onFloat u fx fy fz k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, fz, x, y, z, hx, hy, hz, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy fz hx hy hz
    dsimp only [legalTernaryTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    have hz12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hz
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12 hz12
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).1
      x.1 y.1 z.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).2
      x.2 y.2 z.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalTernaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) →
      Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x y z (p : Val u → Prop), TreeRel3 onB onBi onF u x y z p →
        OpCode.wp (mkCode u) (x, y, z, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p →
      onF f x y z q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys zs : Tup (Arg Val) (target.legalTys t)) → (x y z : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      valsTup zs = encodeVal target t z →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel3 onB onBi onF t x y z (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, zs, px, py, pz, hxs, hys, hzs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalTernaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      have hzt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hzs)
      simp only [valsTup, Tup.map] at hxt hyt hzt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op3]
        rw [hxt, hyt, hzt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, pz, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) px py pz _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs
          px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) ys py
            hys fun fy hfy =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) zs pz
            hzs fun fz hfz => ?_
        refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fx fy fz px py pz hfx hfy hfz _ m ?_
        refine TreeRel3.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres
          res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      have hz12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hzs)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12 hz12
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1
          (tupSplit (splitToTup hf zs)).1
        px.1 py.1 pz.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _
          m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2
          (tupSplit (splitToTup hf zs)).2
        px.2 py.2 pz.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _
          m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalBinTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a →
      b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p →
      onF f x y q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy : Tup (Arg Val) (target.leafTys u)) (x y : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel2 onB onBi onF u x y (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalBinTree.goS target onBool onBits onFloat u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, x, y, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalBinTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      x.1 y.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      x.2 y.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalBinTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target Val) u → Bool)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a →
      b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hVec : ∀ u unif, target.keepsPacked u = true → vecSupported u unif = true →
      target.supportsTy u = true → ∀ x y (p : Val u → Prop),
        TreeRel2 onB onBi onF u x y p → OpCode.wp (mkCode u) (x, y, ()) (fun (res, ()) => p res))
    (hRotl : ∀ u c w s, opShiftKind (mkCode u) = some true → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ())
          (fun (r, ()) => p r))
    (hShl : ∀ u c w s, opShiftKind (mkCode u) = some false → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ()) (fun (rt, ()) =>
          OpCode.wp (.and u) (rt, splatBits w (BitVec.allOnes w <<< s) u, ()) (fun (r, ()) => p r)))
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ f x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (rawRhs : Option (Arg (LVar target Val) t)) →
      (x y : Val t) → valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (∀ c, rawRhs = some (.imm c) → y = c) →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel2 onB onBi onF t x y (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X
        (legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t xs ys rawRhs
        k) m
  | .bool, _, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, rawRhs, px, py, hxs, hys, hraw, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    have ht_pair : target.supportsTy (.pair t1 t2) = true := by simp [LegalTarget.supportsTy, ht]
    dsimp only [legalBinTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      simp only [valsTup, Tup.map] at hxt hyt
      have hscalar : wp Γ Q X (
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
            packLeavesToLegal target (.pair t1 t2) fres k) m := by
        refine splitLegalToLeaves_wp target (.pair t1 t2) ht_pair xs px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) ht_pair ys py hys fun fy hfy => ?_
        refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) ht_pair fx fy px py hfx hfy _ m ?_
        refine TreeRel2.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) ht_pair fres res hfres hres
      cases hrr : rawRhs with
      | none =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) =
                false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b => cases b <;> exact hscalar
      | some r =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) =
                false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases hsk : opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b =>
            cases r with
            | var _ => cases b <;> exact hscalar
            | imm c =>
              have hpy : py = c := hraw c hrr
              subst hpy
              cases b with
              | true =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hrl := hRotl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hrl
                    exact hrl (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp
                        (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hrl
                    by_cases hsup :
                      target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (r, ()) hr =>
                        hr (tupToPacked hp (.var r, ()))
                          (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))) hrl
                    · rw [ite_eq_right hsup]
                      exact hscalar
              | false =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hsh := hShl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hsh
                    exact hsh (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp
                        (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hsh
                    by_cases hsup :
                      (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                        target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (rt, ()) hrt =>
                        OpCode.wp_mono (.and (.pair t1 t2)) _ (fun (r, ()) hr =>
                          hr (tupToPacked hp (.var r, ()))
                            (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
                              hrt) hsh
                    · rw [ite_eq_right hsup]
                      exact hscalar
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1 none px.1 py.1
        (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2 none px.2 py.2
        (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalCmpBits_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBits a b → wp Γ Q X (k r) m) :
    wp Γ Q X (
      if n == 0 then k (.imm (o.evalBits 0#0 0#0))
      else if n == target.widenWidth n then
        .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)
      else
        if (match o with | .slt | .sle | .sgt | .sge => true | _ => false) then
          emitSextToW n (target.widenWidth n) a' fun sa =>
            emitSextToW n (target.widenWidth n) b' fun sb =>
              .let_ (op2 (.cmp o (.bits (target.widenWidth n))) sa sb) fun r => k (.var r.1)
        else .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)) m := by
  have hnw := le_widenWidth_of_supports hn
  by_cases hn0 : n = 0
  · subst hn0
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bitVec0_eq_zero a, bitVec0_eq_zero b] at hk
    exact hk _ rfl
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat,
        Bool.false_eq_true, liftCmp]
      revert a' b' ha hb hk
      rw [← heq]
      intro a' b' ha hb hk
      rw [BitVec.setWidth_eq] at ha hb
      exact hk _ (by change o.evalBits a'.val b'.val = _; rw [ha, hb])
    · have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
      simp only [hneqf, Bool.false_eq_true, ↓reduceIte]
      cases o <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact hk _ (by
          change CmpOp.evalBits .eq a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .eq trivial a b)
      · exact hk _ (by
          change CmpOp.evalBits .ne a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .ne trivial a b)
      · exact hk _ (by
          change CmpOp.evalBits .ult a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .ult trivial a b)
      · exact hk _ (by
          change CmpOp.evalBits .ule a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .ule trivial a b)
      · exact hk _ (by
          change CmpOp.evalBits .ugt a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .ugt trivial a b)
      · exact hk _ (by
          change CmpOp.evalBits .uge a'.val b'.val = _; rw [ha, hb]
          exact evalBits_setWidth_unsigned hnw .uge trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb =>
          ?_
        simp only
          [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by
          change CmpOp.evalBits .slt sa.val sb.val = _; rw [hsa, hsb]
          exact evalBits_signExtend_signed hn0pos hnw .slt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb =>
          ?_
        simp only
          [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by
          change CmpOp.evalBits .sle sa.val sb.val = _; rw [hsa, hsb]
          exact evalBits_signExtend_signed hn0pos hnw .sle trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb =>
          ?_
        simp only
          [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by
          change CmpOp.evalBits .sgt sa.val sb.val = _; rw [hsa, hsb]
          exact evalBits_signExtend_signed hn0pos hnw .sgt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb =>
          ?_
        simp only
          [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by
          change CmpOp.evalBits .sge sa.val sb.val = _; rw [hsa, hsb]
          exact evalBits_signExtend_signed hn0pos hnw .sge trivial a b)

private theorem legalCmpTree_goMask_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.hasFloat = false →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftCmp o.evalBits o.evalBool u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree.goMask target o u fx fy k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, Ty.mask, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree.goMask]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only
        [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree.goMask]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [leafVals]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalCmpTree.goMask]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalCmpTree_goMask_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalCmpTree_goMask_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

theorem legalCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.hasFloat = false →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftCmp o.evalBits o.evalBool t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree target o t xs ys k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, Ty.mask, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only
        [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [encodeVal]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalCmpTree_goMask_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres
      hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftCmp o.evalBits o.evalBool (.pair t1 t2) px py) hmres hk

private theorem op3_select_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c)
    (a' b' : Arg Val t) (a b : Val t) (ha : a'.val = a) (hb : b'.val = b)
    (k : Arg Val t → Expr Val Cont rs) (m : Mem 64)
    (hk : ∀ r, r.val = (if c then a else b) → wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (op3 (.select t) c' a' b') fun r => k (.var r.1)) m := by
  cases c' <;> cases a' <;> cases b' <;>
    · dsimp only [wp, Op.wp, OpCode.wp, op3, vals, Arg.val] at hc ha hb ⊢
      cases c <;> simp_all [Arg.val]

private theorem legalSelectTree_goSel_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (u : Ty), target.supportsTy u = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree.goSel target c' u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n))
      (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair u1 u2, ht, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalSelectTree.goSel]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalSelectTree_goSel_wp target c' c hc u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 => ?_
    refine legalSelectTree_goSel_wp target c' c hc u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 => ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]
      cases c <;> rfl)

theorem legalSelectTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree target c' t xs ys k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n))
      (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair t1 t2, ht, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalSelectTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalSelectTree_goSel_wp target c' c hc (.pair t1 t2) htp fx fy px py hfx hfy _ m
      fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (if c then px else py) hfres hk

private theorem legalBlendTree_goBlend_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
      (fm : Tup (Arg Val) (target.leafTys u.mask)) →
      (fx fy : Tup (Arg Val) (target.leafTys u)) →
      (msk : Val u.mask) → (x y : Val u) →
      valsTup fm = leafVals target u.mask msk →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (blendV u msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree.goBlend target u fm fx fy k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n))
      (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair u1 u2, ht, fm, fx, fy, msk, px, py, hm, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [Ty.mask, LegalTarget.leafTys] at fm fx fy hm hx hy
    dsimp only [legalBlendTree.goBlend]
    have hm12 :=
      congrArg (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask)) hm
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hm12 hx12 hy12
    refine legalBlendTree_goBlend_wp target u1 ht.1
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 msk.1 px.1 py.1
      (congrArg Prod.fst hm12) (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 =>
        ?_
    refine legalBlendTree_goBlend_wp target u2 ht.2
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 msk.2 px.2 py.2
      (congrArg Prod.snd hm12) (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 =>
        ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]; rfl)

theorem legalBlendTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true →
      (ms : Tup (Arg Val) (target.legalTys t.mask)) →
      (xs ys : Tup (Arg Val) (target.legalTys t)) →
      (msk : Val t.mask) → (x y : Val t) →
      valsTup ms = encodeVal target t.mask msk →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (blendV t msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree target t ms xs ys k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n))
      (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair t1 t2, ht, ms, xs, ys, msk, px, py, hms, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalBlendTree]
    refine splitLegalToLeaves_wp target (Ty.mask (.pair t1 t2))
      (supportsTy_mask target (.pair t1 t2))
        ms msk hms fun fm hfm =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalBlendTree_goBlend_wp target (.pair t1 t2) htp fm fx fy msk px py hfm hfx hfy _ m
      fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (blendV (.pair t1 t2) msk px py) hfres
      hk

private theorem legalFCmpTree_goFCmp_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.isFloatTree = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftFCmp o u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree.goFCmp target o u fx fy k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree.goFCmp, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.isFloatTree, Bool.and_eq_true] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalFCmpTree.goFCmp]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalFCmpTree_goFCmp_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalFCmpTree_goFCmp_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

theorem legalFCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.isFloatTree = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftFCmp o t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree target o t xs ys k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalFCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalFCmpTree_goFCmp_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres
      hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftFCmp o (.pair t1 t2) px py) hmres hk

theorem op1_bitcast_wp_top {t u : Ty} (h : t.size = u.size) (a : Val t)
    (post : Tup Val [u] → Prop) :
    OpCode.wp (.bitcast t u h) (a, ()) post = post (ofBits u (BitVec.cast h (toBits t a)), ()) :=
      rfl

theorem legalFloatBit2_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (g : BitVec f.width → BitVec f.width → BitVec f.width)
    (hF : ∀ (a b : BitVec f.width) post, OpCode.wp (mkFOp f) (a, b, ()) post ↔ post (g a b, ()))
    (hB : ∀ (a b : BitVec f.width) post, OpCode.wp (mkOp f.width) (a, b, ()) post ↔
      post (g a b, ()))
    (x' y' : Arg Val (.float f)) (x y : BitVec f.width)
    (hx : x'.val = x) (hy : y'.val = y)
    {k : Arg Val (.float f) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = g x y → wp Γ Q X (k r) m) :
    wp Γ Q X (legalFloatBit2 target mkOp mkFOp f x' y' k) m := by
  dsimp only [legalFloatBit2]
  by_cases hsb : target.scalarFloatBitwise = true
  · rw [ite_eq_left hsb]
    dsimp only [wp, Op.wp, op2, vals]
    rw [hx, hy, hF]
    exact hk _ rfl
  · rw [ite_eq_right hsb]
    dsimp only [wp, Op.wp, op1, op2, vals]
    rw [op1_bitcast_wp_top, op1_bitcast_wp_top]
    dsimp only [Arg.val_var, toBits, ofBits]
    simp only [BitVec.cast_eq]
    rw [hB x'.val y'.val]
    rw [op1_bitcast_wp_top]
    dsimp only [toBits, ofBits]
    simp only [BitVec.cast_eq]
    exact hk _ (by change g x'.val y'.val = _; rw [hx, hy])


end LegalWp

end LeanQbe.T
