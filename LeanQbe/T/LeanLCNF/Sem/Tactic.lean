module

public import LeanQbe.T.LeanLCNF.Sem.E2E

/-!
# Pure Tier-P & Resource Symbolic Simulation Tactic (`lcnf_sim`, `lcnf_res_sim`, `Tactic.lean`)

Provides lightweight `PWp`, `PVal.wp`, `PRWp`, and `PRValWp` reduction lemmas plus
`lcnf_sim` / `lcnf_res_sim` tactics so proving `PModuleOk{,Idx}` and `PResOk{,Idx}`
for concrete Lean functions takes ~20–60 lines with zero hand-written Tier-H or Tier-T WP.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T.LeanLCNF

/-! ## 1. Pure `PWp` & `PVal.wp` Step Lemmas -/

theorem PWp_let_nat {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {n : Nat} {k : LcCode}
    (hk : PWp ar Δ J (ρ.set x (.nat n)) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.lit (.nat n)) k) := hk

theorem PWp_let_scalar {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {n : Nat} {k : LcCode}
    (hk : PWp ar Δ J (ρ.set x (.bits ty.width (BitVec.ofNat ty.width n))) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.lit (.scalar n)) k) := hk

theorem PWp_let_erased {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {k : LcCode}
    (hk : PWp ar Δ J (ρ.set x .erased) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty .erased k) := hk

theorem PWp_let_ctor {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {ci : LcCtor} {as : List LcArg} {k : LcCode}
    {vs : List PVal} {r : PVal}
    (hargs : ρ.evalArgs as = some vs) (hmk : PVal.mkCtor ty ci vs = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.ctor ci as) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hargs]; dsimp only
  rw [hmk]; exact hk

theorem PWp_let_oproj {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x i y : Nat} {ty : LcTy} {k : LcCode} {r : PVal}
    (hget : (ρ y).bind (·.getObj? i) = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.oproj i y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hget]; exact hk

theorem PWp_let_uproj {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x i y : Nat} {ty : LcTy} {k : LcCode} {r : PVal}
    (hget : (ρ y).bind (·.getUsize? i) = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.uproj i y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hget]; exact hk

theorem PWp_let_sproj {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x n off y : Nat} {ty : LcTy} {k : LcCode} {r : PVal}
    (hget : (ρ y).bind (·.getScalar? n off ty) = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.sproj n off y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hget]; exact hk

theorem PWp_let_box {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty t : LcTy} {y : Nat} {k : LcCode} {r : PVal}
    (hbox : (ρ y).bind (PVal.box t) = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.box t y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hbox]; exact hk

theorem PWp_let_unbox {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {y : Nat} {k : LcCode} {r : PVal}
    (hub : (ρ y).bind (PVal.unbox ty) = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.unbox y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hub]; exact hk

theorem PWp_let_isShared {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {y : Nat} {k : LcCode} {pv : PVal}
    (hy : ρ y = some pv)
    (hk : ∀ b : Bool, PWp ar Δ J (ρ.set x (PVal.bool b)) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.isShared y) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hy]; exact ⟨rfl, hk⟩

theorem PWp_let_prim {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {f : String} {as : List LcArg} {k : LcCode}
    {vs : List PVal} {r : PVal}
    (hargs : ρ.evalArgs as = some vs) (hnoob : (f == "outOfBounds._redArg") = false)
    (hp : pIsPrimName f = true) (heval : primP f vs = some r)
    (hk : PWp ar Δ J (ρ.set x r) Q X k) :
    PWp ar Δ J ρ Q X (.let_ x ty (.fap f as) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hargs]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hnoob; cases hnoob)]
  rw [ite_eq_left hp, heval]
  exact hk

theorem PWp_let_call {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {ty : LcTy} {f : String} {as : List LcArg} {k : LcCode}
    {vs : List PVal}
    (hargs : ρ.evalArgs as = some vs) (hnoob : (f == "outOfBounds._redArg") = false)
    (hnp : pIsPrimName f = false)
    (P : PPost) (E : PXPost) (hcall : Δ f vs P E)
    (hk : ∀ r, P r → PWp ar Δ J (ρ.set x r) Q X k)
    (hx : ∀ c, E c → X c) :
    PWp ar Δ J ρ Q X (.let_ x ty (.fap f as) k) := by
  dsimp only [PWp, PVal.wp]
  rw [hargs]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hnoob; cases hnoob)]
  rw [ite_eq_right (by intro h; rw [h] at hnp; cases hnp)]
  exact ⟨P, E, hcall, hk, hx⟩

theorem PWp_inc_skip {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x n : Nat} {chk : Bool} {k : LcCode}
    (hk : PWp ar Δ J ρ Q X k) : PWp ar Δ J ρ Q X (.inc x n chk k) := hk

theorem PWp_dec_skip {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x n : Nat} {chk : Bool} {k : LcCode}
    (hk : PWp ar Δ J ρ Q X k) : PWp ar Δ J ρ Q X (.dec x n chk k) := hk

theorem PWp_del_skip {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {k : LcCode}
    (hk : PWp ar Δ J ρ Q X k) : PWp ar Δ J ρ Q X (.del x k) := hk

theorem PWp_oset_step {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x i : Nat} {y : LcArg} {k : LcCode}
    {xv yv xv' : PVal}
    (hx : ρ x = some xv) (hy : ρ.evalArg y = some yv) (hset : xv.setObj i yv = some xv')
    (hk : PWp ar Δ J (ρ.set x xv') Q X k) :
    PWp ar Δ J ρ Q X (.oset x i y k) := by
  dsimp only [PWp]
  rw [hx, hy]; dsimp only; rw [hset]; exact hk

theorem PWp_ret_step {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {a : LcArg} {v : PVal}
    (ha : ρ.evalArg a = some v) (hq : Q v) :
    PWp ar Δ J ρ Q X (.ret a) := by
  dsimp only [PWp]; rw [ha]; exact hq

theorem PWp_cases_tag {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {x : Nat} {alts : List (LcPat × LcCode)} {tag : Nat}
    (htag : (ρ x).bind PVal.tag? = some tag)
    (hk : PWpCtorAlts ar Δ J ρ Q X tag alts (PWpDfltAlts ar Δ J ρ Q X alts)) :
    PWp ar Δ J ρ Q X (.cases x alts) := by
  dsimp only [PWp]; rw [htag]; exact hk

theorem PWp_jmp_step {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {j : Nat} {as : List LcArg} {vs : List PVal}
    (hargs : ρ.evalArgs as = some vs) (hj : J j vs) :
    PWp ar Δ J ρ Q X (.jmp j as) := by
  dsimp only [PWp]; rw [hargs]; exact hj

/-! ## 2. Resource-Aware `PRWp` & `PRValWp` Step Lemmas -/

theorem PRWp_let_ok {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx ctx' : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x : Nat} {ty : LcTy} {v : LcVal} {k : LcCode}
    (hcv : checkVal env ctx x ty v = .ok ctx')
    (hv : PRValWp env Δr ρ ty v rem wr rcr
      (fun r rem' wr' rcr' => PRWp m env retTy Δr jps ctx' J (ρ.set x r) rem' wr' rcr' Q X k) X) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.let_ x ty v k) := by
  dsimp only [PRWp]; rw [hcv]; exact hv

theorem PRValWp_nat {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {n rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    (hlt : n < 2 ^ 63) (hk : K (.nat n) rem wr rcr) :
    PRValWp env Δr ρ ty (.lit (.nat n)) rem wr rcr K X := ⟨hlt, hk⟩

theorem PRValWp_scalar {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {n rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    (hk : K (.bits ty.width (BitVec.ofNat ty.width n)) rem wr rcr) :
    PRValWp env Δr ρ ty (.lit (.scalar n)) rem wr rcr K X := hk

theorem PRValWp_erased {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    (hk : K .erased rem wr rcr) :
    PRValWp env Δr ρ ty .erased rem wr rcr K X := hk

theorem PRValWp_ctor_scalar {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {ci : LcCtor} {as : List LcArg} {rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    {vs : List PVal} {r : PVal}
    (hargs : ρ.evalArgs as = some vs) (hmk : PVal.mkCtor ty ci vs = some r)
    (hsc : ci.isScalar = true) (hk : K r rem wr rcr) :
    PRValWp env Δr ρ ty (.ctor ci as) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hargs]; dsimp only; rw [hmk]; dsimp only
  rw [ite_eq_left hsc]; exact hk

theorem PRValWp_ctor_alloc {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {ci : LcCtor} {as : List LcArg} {rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    {vs : List PVal} {r : PVal}
    (hargs : ρ.evalArgs as = some vs) (hmk : PVal.mkCtor ty ci vs = some r)
    (hsc : ci.isScalar = false) (hrem : ci.byteSize ≤ rem) (hwr : 1 ≤ wr)
    (hk : K r (rem - ci.byteSize) (wr - 1) rcr) :
    PRValWp env Δr ρ ty (.ctor ci as) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hargs]; dsimp only; rw [hmk]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hsc; cases hsc)]
  exact ⟨hrem, hwr, hk⟩

theorem PRValWp_oproj {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {i y rem wr rcr : Nat} {K : PResPost} {X : PResXPost} {r : PVal}
    (hget : (ρ y).bind (·.getObj? i) = some r) (hk : K r rem wr rcr) :
    PRValWp env Δr ρ ty (.oproj i y) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hget]; exact hk

theorem PRValWp_isShared {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {y rem wr rcr : Nat} {K : PResPost} {X : PResXPost} {pv : PVal}
    (hy : ρ y = some pv) (hnt : isTaggedPVal pv = false)
    (hk : ∀ b : Bool, K (PVal.bool b) rem wr rcr) :
    PRValWp env Δr ρ ty (.isShared y) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hy]; exact ⟨hnt, hk⟩

theorem PRValWp_prim {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {f : String} {as : List LcArg} {rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    {vs : List PVal} {r : PVal}
    (hargs : ρ.evalArgs as = some vs) (hnoob : (f == "outOfBounds._redArg") = false)
    (hnd : (env.decls.find? (·.1 == f)).isSome = false)
    (hp : pIsPrimName f = true) (heval : primP f vs = some r)
    (hsafe : primResSafe f vs) (hk : K r rem wr rcr) :
    PRValWp env Δr ρ ty (.fap f as) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hargs]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hnoob; cases hnoob)]
  rw [ite_eq_right (by intro h; rw [h] at hnd; cases hnd)]
  refine ⟨hp, ?_⟩; rw [heval]; exact ⟨hsafe, hk⟩

theorem PRValWp_call {env : RcModEnv} {Δr : PResEnv} {ρ : PValEnv} {ty : LcTy}
    {f : String} {as : List LcArg} {rem wr rcr : Nat} {K : PResPost} {X : PResXPost}
    {vs : List PVal}
    (hargs : ρ.evalArgs as = some vs) (hnoob : (f == "outOfBounds._redArg") = false)
    (hmem : (env.decls.find? (·.1 == f)).isSome = true)
    (P : PResPost) (E : PResXPost) (hcall : Δr f vs rem wr rcr P E)
    (hk : ∀ r rem' wr' rcr', P r rem' wr' rcr' → K r rem' wr' rcr')
    (hx : ∀ c rem' wr' rcr', E c rem' wr' rcr' → X c rem' wr' rcr') :
    PRValWp env Δr ρ ty (.fap f as) rem wr rcr K X := by
  dsimp only [PRValWp]; rw [hargs]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hnoob; cases hnoob)]
  rw [ite_eq_left hmem]
  exact ⟨P, E, hcall, hk, hx⟩

theorem PRWp_inc_skip {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x n : Nat} {chk : Bool} {k : LcCode} {v : RcVar}
    (hgx : ctx.get? x = some v) (hskip : (v.noRc || v.persistent || n == 0) = true)
    (hk : PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X k) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.inc x n chk k) := by
  dsimp only [PRWp]; rw [hgx]; dsimp only; rw [ite_eq_left hskip]; exact hk

theorem PRWp_inc_rc {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x n : Nat} {chk : Bool} {k : LcCode} {v : RcVar}
    (hgx : ctx.get? x = some v) (hskip : (v.noRc || v.persistent || n == 0) = false)
    (hn : n ≤ rcr)
    (hk : PRWp m env retTy Δr jps (ctx.put { v with owned := v.owned + n, excl := false })
      J ρ rem wr (rcr - n) Q X k) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.inc x n chk k) := by
  dsimp only [PRWp]; rw [hgx]; dsimp only
  rw [ite_eq_right (by intro h; rw [h] at hskip; cases hskip)]
  exact ⟨hn, hk⟩

theorem PRWp_dec_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx ctx1 : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x n : Nat} {chk : Bool} {k : LcCode}
    (hcons : ctx.consumeVar x n = .ok ctx1)
    (hsafe : safeNonColdDec ctx ρ x n)
    (hk : PRWp m env retTy Δr jps ctx1 J ρ rem wr rcr Q X k) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.dec x n chk k) := by
  dsimp only [PRWp]; rw [hcons]; exact ⟨hsafe, hk⟩

theorem PRWp_del_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx ctx1 : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x : Nat} {k : LcCode}
    (hcons : ctx.consumeVar x = .ok ctx1)
    (hk : PRWp m env retTy Δr jps ctx1 J ρ rem wr rcr Q X k) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.del x k) := by
  dsimp only [PRWp]; rw [hcons]; exact hk

theorem PRWp_oset_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx ctx1 : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x i : Nat} {y : LcArg} {k : LcCode} {xv yv xv' : PVal}
    (hx : ρ x = some xv) (hy : ρ.evalArg y = some yv) (hcons : ctx.consumeArg y = .ok ctx1)
    (hset : xv.setObj i yv = some xv')
    (hk : PRWp m env retTy Δr jps ctx1 J (ρ.set x xv') rem wr rcr Q X k) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.oset x i y k) := by
  dsimp only [PRWp]; rw [hx, hy, hcons]; dsimp only; rw [hset]; exact hk

theorem primResSafe_nat_decEq {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    primResSafe "Nat.decEq" [.nat a, .nat b] := by
  have hs : splitDot "Nat.decEq" = ["Nat", "decEq"] := rfl
  simp only [primResSafe, hs]; exact ⟨ha, hb⟩

theorem primResSafe_nat_sub {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    primResSafe "Nat.sub" [.nat a, .nat b] := by
  have hs : splitDot "Nat.sub" = ["Nat", "sub"] := rfl
  simp only [primResSafe, hs]; exact ⟨ha, hb⟩

theorem primResSafe_nat_add {a b : Nat} (h : a + b < 2 ^ 63) :
    primResSafe "Nat.add" [.nat a, .nat b] := by
  have hs : splitDot "Nat.add" = ["Nat", "add"] := rfl
  simp only [primResSafe, hs]; exact h

theorem primResSafe_nat_mul {a b : Nat}
    (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (hab : a * b < 2 ^ 63) :
    primResSafe "Nat.mul" [.nat a, .nat b] := by
  have hs : splitDot "Nat.mul" = ["Nat", "mul"] := rfl
  simp only [primResSafe, hs]; exact ⟨ha, hb, hab⟩

theorem PRWp_ret_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost} {a : LcArg} {r : PVal}
    (ha : ρ.evalArg a = some r) (hq : Q r rem wr rcr) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.ret a) := by
  dsimp only [PRWp]; rw [ha]; exact hq

theorem PRWp_cases_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {x : Nat} {alts : List (LcPat × LcCode)} {vx : RcVar} {tag : Nat} {pv : PVal}
    (hgx : ctx.get? x = some vx) (htag : (ρ x).bind PVal.tag? = some tag) (hpv : ρ x = some pv)
    (hsafe : casesResSafe vx.ty pv)
    (hk : PRWpCtorAlts m env retTy Δr jps ctx x
      ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) pv J ρ tag rem wr rcr Q X alts
      (PRWpDfltAlts m env retTy Δr jps ctx J ρ rem wr rcr Q X alts)) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.cases x alts) := by
  dsimp only [PRWp]; rw [hgx, htag, hpv]; exact ⟨hsafe, hk⟩

theorem PRWp_jmp_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {jps : List RcJpInfo} {ctx : RcCtx} {J : PResJEnv} {ρ : PValEnv}
    {rem wr rcr : Nat} {Q : PResPost} {X : PResXPost}
    {j : Nat} {as : List LcArg} {vs : List PVal}
    (hargs : ρ.evalArgs as = some vs) (hj : J j vs rem wr rcr) :
    PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X (.jmp j as) := by
  dsimp only [PRWp]; rw [hargs]; exact hj

/-! ## 3. Symbolic Evaluators (`lcnf_step` / `lcnf_sim` / `lcnf_res_step` / `lcnf_res_sim`) -/

/-- Execute one pure `PWp` symbolic step (`let_`, `inc`/`dec`/`del`, `ret`, known-tag `cases`). -/
macro "lcnf_step" : tactic =>
  `(tactic|
    first
    | refine PWp_let_nat ?_
    | refine PWp_let_scalar ?_
    | refine PWp_let_erased ?_
    | refine PWp_let_ctor rfl rfl ?_
    | refine PWp_let_oproj rfl ?_
    | refine PWp_let_uproj rfl ?_
    | refine PWp_let_sproj rfl ?_
    | refine PWp_let_box rfl ?_
    | refine PWp_let_unbox rfl ?_
    | refine PWp_let_isShared rfl ?_
    | refine PWp_let_prim rfl rfl rfl rfl ?_
    | refine PWp_inc_skip ?_
    | refine PWp_dec_skip ?_
    | refine PWp_del_skip ?_
    | refine PWp_oset_step rfl rfl rfl ?_
    | (refine PWp_ret_step rfl ?_)
    | (refine PWp_jmp_step rfl ?_)
    | (refine PWp_cases_tag rfl ?_;
       dsimp only [PWpCtorAlts, PWpDfltAlts];
       (repeat' (rw [ite_eq_right]; rotate_left 1; · (first | decide | simp)));
       try (rw [ite_eq_left]; rotate_left 1; · (first | rfl | decide | simp))))

/-- Repeat pure `PWp` symbolic steps until a branch, recursive call, or join point is reached. -/
macro "lcnf_sim" : tactic => `(tactic| repeat lcnf_step)

/-- Step a non-primitive function call in `PWp` with postcondition `P` and empty `PXPost`. -/
macro "lcnf_call " P:term : tactic =>
  `(tactic| (apply PWp_let_call (P := $P) (E := fun _ => False);
             · exact rfl
             · exact rfl
             · exact rfl
             rotate_left 2
             · exact fun _ h => False.elim h))

/-- Execute one resource-aware `PRWp` step (`let_`, `inc`, `dec`, `del`, `oset`, `ret`, `cases`). -/
macro "lcnf_res_step" : tactic =>
  `(tactic|
    first
    | (refine PRWp_let_ok rfl ?_;
       first
       | refine PRValWp_nat (by omega) ?_
       | refine PRValWp_scalar ?_
       | refine PRValWp_erased ?_
       | refine PRValWp_ctor_scalar rfl rfl rfl ?_
       | refine PRValWp_ctor_alloc rfl rfl rfl (by omega) (by omega) ?_
       | refine PRValWp_oproj rfl ?_
       | refine PRValWp_isShared rfl (by first | rfl | decide) ?_
       | (apply PRValWp_prim;
          · exact rfl
          · exact rfl
          · exact rfl
          · exact rfl
          · exact rfl
          · (try dsimp only [PEnc.enc];
             first
             | exact trivial
             | exact primResSafe_nat_decEq (by omega) (by omega)
             | exact primResSafe_nat_sub (by omega) (by omega)
             | exact primResSafe_nat_add (by omega)
             | exact primResSafe_nat_mul (by omega) (by omega) (by omega)
             | omega
             | decide)))
    | refine PRWp_inc_skip rfl rfl ?_
    | refine PRWp_inc_rc rfl rfl (by omega) ?_
    | refine PRWp_dec_step rfl
        (by first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl))
          | exact Or.inr (Or.inr (Or.inl
              (by
                try dsimp only [PEnc.enc, isTaggedPVal]
                exact decide_eq_true_iff.mpr (by omega))))
          | exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, List.mem_cons_self, rfl⟩)))) ?_
    | refine PRWp_del_step rfl ?_
    | refine PRWp_oset_step rfl rfl rfl rfl ?_
    | refine PRWp_ret_step rfl ?_
    | refine PRWp_jmp_step rfl ?_
    | (refine PRWp_cases_step rfl rfl rfl
         (by first
           | exact trivial | exact ⟨by omega, by decide⟩
           | exact Or.inl rfl | exact Or.inr (by decide)) ?_;
       dsimp only [PRWpCtorAlts, PRWpDfltAlts];
       (repeat' (rw [ite_eq_right]; rotate_left 1; · (first | decide | simp)));
       try (rw [ite_eq_left]; rotate_left 1; · (first | rfl | decide | simp);
            refine ⟨(by
                first
                | exact fun _ => rfl
                | exact fun _ => Or.inl rfl
                | exact fun h => by cases h), ?_⟩)))

/-- Repeat resource-aware `PRWp` symbolic steps until a branch, call, or join point is reached. -/
macro "lcnf_res_sim" : tactic => `(tactic| repeat lcnf_res_step)

/-- Step a non-primitive function call in `PRWp` with postcondition `P` and empty `PResXPost`. -/
macro "lcnf_res_call " P:term : tactic =>
  `(tactic| (refine PRWp_let_ok rfl ?_;
             apply PRValWp_call (P := $P) (E := fun _ _ _ _ => False);
             · exact rfl
             · exact rfl
             · exact rfl
             rotate_left 2
             · exact fun _ _ _ _ hf => False.elim hf))

end LeanQbe.T.LeanLCNF.Sem
