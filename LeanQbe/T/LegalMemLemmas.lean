module

public import LeanQbe.T.LegalOpWpLemmas2
import all Kraken.Mem

/-!
# Legalization memory chunking and `Func.legal_wp` / `Func.legal_spec` (`T5`, Part 4)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp

/-! ### Chunk 4.4: Memory widening/byte-chunking (`emitLoadBits`, `emitStoreBits`, `legalLoad`, `legalStore`) and `Func.legal_wp` -/

private theorem memWp_int_toBytes_add :
    ∀ (n1 n2 : Nat) (v : Int),
      Int.toBytes (n1 + n2) v = Int.toBytes n1 v ++ Int.toBytes n2 (v / (256 : Int) ^ n1)
  | 0, n2, v => by simp [Int.toBytes]
  | n1 + 1, n2, v => by
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    rw [memWp_int_toBytes_add n1 n2 (v / 256)]
    congr 2
    rw [Int.pow_succ, Int.mul_comm ((256 : Int) ^ n1) 256]
    exact Int.ediv_ediv_of_nonneg (by decide)

private theorem memWp_int_toBytes_bitVec_toNat (n w : Nat) (_hn : 8 * n ≤ w) (x : BitVec w) :
    Int.toBytes n (BitVec.setWidth (8 * n) x).toInt = Int.toBytes n (x.toNat : Int) := by
  rw [← Int.toBytes_emod n (BitVec.setWidth (8 * n) x).toInt,
      ← Int.toBytes_emod n (x.toNat : Int)]
  congr 1
  dsimp only [Int.take]
  have hp : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := (Int.natCast_pow 2 (8 * n)).symm
  have h1 : (BitVec.setWidth (8 * n) x).toInt % (2 : Int) ^ (8 * n) =
      ((BitVec.setWidth (8 * n) x).toNat : Int) := by
    have hnn : 0 ≤ (BitVec.setWidth (8 * n) x).toInt % (2 : Int) ^ (8 * n) :=
      Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
    rw [← Int.toNat_of_nonneg hnn]
    congr 1
    have hbv : (BitVec.ofInt (8 * n) (BitVec.setWidth (8 * n) x).toInt).toNat =
        (BitVec.setWidth (8 * n) x).toNat := by rw [BitVec.ofInt_toInt]
    rw [BitVec.toNat_ofInt, ← hp] at hbv
    exact hbv
  rw [h1, BitVec.toNat_setWidth, hp, ← Int.natCast_emod]

private theorem memWp_int_toBytes_shift {c w off : Nat} (hle : 8 * (off + c) ≤ w) (x : BitVec w) :
    Int.toBytes c ((x >>> (8 * off)).setWidth (8 * c)).toInt =
      Int.toBytes c ((x.toNat : Int) / (256 : Int) ^ off) := by
  rw [memWp_int_toBytes_bitVec_toNat c w (by omega) (x >>> (8 * off))]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp : (256 : Int) ^ off = ((2 ^ (8 * off) : Nat) : Int) := by
    rw [show (256 : Int) = ((2 ^ 8 : Nat) : Int) by decide, ← Int.natCast_pow, ← Nat.pow_mul]
  rw [hp, ← Int.natCast_ediv]

private theorem memWp_storeBytes_append (m : Mem 64) (a : BitVec 64) (bs1 bs2 : List UInt8)
    (hlen : bs1.length + bs2.length ≤ 2 ^ 64) :
    m.storeBytes a (bs1 ++ bs2) =
      (m.storeBytes a bs1).storeBytes (a + BitVec.ofNat 64 bs1.length) bs2 := by
  simp only [Mem.storeBytes, List.At_append bs1 bs2 a hlen]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases (bs2.At (a + BitVec.ofNat 64 bs1.length))[k]? <;>
    cases (bs1.At a)[k]? <;> cases m[k]? <;> rfl

private theorem memWp_storeBytes_nil (m : Mem 64) (a : BitVec 64) : m.storeBytes a [] = m := by
  simp only [Mem.storeBytes]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  have hnone : (([] : List UInt8).At a)[k]? = none := by
    rw [Std.ExtHashMap.getElem?_eq_none]
    simp [mem_At_iff]
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, hnone]
  cases m[k]? <;> rfl

private theorem memWp_list_range_add (n1 n2 : Nat) :
    List.range (n1 + n2) = List.range n1 ++ (List.range n2).map (n1 + ·) := by
  induction n2 with
  | zero => simp
  | succ n2 ih =>
    rw [Nat.add_succ, List.range_succ, ih, List.range_succ, List.map_append, List.map_singleton,
      List.append_assoc]

private theorem memWp_list_mapM_id_append {α : Type} :
    ∀ (xs ys : List (Option α)) {zs : List α},
      (xs ++ ys).mapM id = some zs ↔
        ∃ x' y', xs.mapM id = some x' ∧ ys.mapM id = some y' ∧ zs = x' ++ y'
  | [], ys, zs => by
    simp only [List.nil_append, List.mapM_nil, Option.pure_def, Option.some.injEq]
    constructor
    · intro h; exact ⟨[], zs, rfl, h, rfl⟩
    · rintro ⟨_, y', rfl, hy, rfl⟩; exact hy
  | x :: xs, ys, zs => by
    simp only [List.cons_append, List.mapM_cons, id_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨a, ha, rest, hrest, rfl⟩
      obtain ⟨x', y', hx, hy, rfl⟩ := (memWp_list_mapM_id_append xs ys).mp hrest
      exact ⟨a :: x', y', ⟨a, ha, x', hx, rfl⟩, hy, rfl⟩
    · rintro ⟨_, y', ⟨a, ha, x', hx, rfl⟩, hy, rfl⟩
      have hrest : (xs ++ ys).mapM id = some (x' ++ y') :=
        (memWp_list_mapM_id_append xs ys).mpr ⟨x', y', hx, hy, rfl⟩
      exact ⟨a, ha, x' ++ y', hrest, rfl⟩

private theorem memWp_loadBytes_length (m : Mem 64) (a : BitVec 64) :
    ∀ (n : Nat) {bs : List UInt8}, m.loadBytes a n = some bs → bs.length = n := by
  intro n bs h
  unfold Mem.loadBytes at h
  induction n generalizing bs with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton] at h
    obtain ⟨x', y', hx, hy, rfl⟩ := (memWp_list_mapM_id_append _ _).mp h
    simp only [List.mapM_cons, List.mapM_nil, id_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hy
    rcases hy with ⟨b, _, _, hnil, rfl⟩
    cases hnil
    simp [ih hx]

private theorem memWp_loadBytes_add (m : Mem 64) (a : BitVec 64) (n1 n2 : Nat) {bs : List UInt8} :
    m.loadBytes a (n1 + n2) = some bs ↔
      ∃ bs1 bs2, m.loadBytes a n1 = some bs1 ∧
        m.loadBytes (a + BitVec.ofNat 64 n1) n2 = some bs2 ∧ bs = bs1 ++ bs2 := by
  unfold Mem.loadBytes
  rw [memWp_list_range_add, List.map_append, List.map_map, memWp_list_mapM_id_append]
  have hmap :
      ((List.range n2).map ((fun i => m.get? (a + BitVec.ofNat 64 i)) ∘ (n1 + ·))) =
      ((List.range n2).map fun j => m.get? ((a + BitVec.ofNat 64 n1) + BitVec.ofNat 64 j)) := by
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hmap]

private theorem memWp_loadBytes_one (m : Mem 64) (a : BitVec 64) {bs : List UInt8} :
    m.loadBytes a 1 = some bs ↔ ∃ b, m.get? a = some b ∧ bs = [b] := by
  unfold Mem.loadBytes
  simp only [List.range_one, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id_eq,
    Option.pure_def, Option.bind_eq_bind, BitVec.add_zero, Std.ExtHashMap.get?_eq_getElem?]
  cases m[a]? <;> simp [eq_comm]

private theorem memWp_loadBytes_isSome_storeBytes {m : Mem 64} {a b : BitVec 64} {n : Nat}
    (hbs : List UInt8) (hm : ∃ ys, m.loadBytes b n = some ys) :
    ∃ ys', (m.storeBytes a hbs).loadBytes b n = some ys' := by
  rcases hm with ⟨ys, hys⟩
  induction n generalizing b ys with
  | zero => exact ⟨[], by simp [Mem.loadBytes]⟩
  | succ n ih =>
    rw [memWp_loadBytes_add] at hys
    rcases hys with ⟨ys1, ys2, h1, h2, _⟩
    obtain ⟨ys1', h1'⟩ := ih ys1 h1
    obtain ⟨y, hy, _⟩ := memWp_loadBytes_one m (b + BitVec.ofNat 64 n) |>.mp h2
    have hget : ((m.storeBytes a hbs).get? (b + BitVec.ofNat 64 n)).isSome = true := by
      simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
        Std.ExtHashMap.getElem?_union]
      rw [Std.ExtHashMap.get?_eq_getElem?] at hy
      rw [hy]
      cases (hbs.At a)[b + BitVec.ofNat 64 n]? <;> simp
    rcases Option.isSome_iff_exists.1 hget with ⟨y', hy'⟩
    have h2' : (m.storeBytes a hbs).loadBytes (b + BitVec.ofNat 64 n) 1 = some [y'] :=
      (memWp_loadBytes_one _ _).mpr ⟨y', hy', rfl⟩
    exact ⟨ys1' ++ [y'], (memWp_loadBytes_add _ _ n 1).mpr ⟨ys1', [y'], h1', h2', rfl⟩⟩

private theorem memWp_getLsbD_ofNat_pow_add (a k b i : Nat) (ha : a < 2 ^ k) :
    Nat.testBit (a + 2 ^ k * b) i =
      if i < k then a.testBit i else b.testBit (i - k) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hik)]
    have hd : (a + 2 ^ k * b) / 2 ^ i = a / 2 ^ i + 2 ^ (k - i) * b := by
      rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
    have h2 : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
      conv => lhs; rw [show k - i = (k - i - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm _ 2]
    rw [hd, h2, Nat.mul_assoc, Nat.and_comm 1 _, Nat.and_one_is_mod, Nat.add_mul_mod_self_left]
    conv => rhs; rw [Nat.and_comm 1 _, Nat.and_one_is_mod]
  · simp only [hik, ↓reduceIte]
    have hge : k ≤ i := Nat.le_of_not_lt hik
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt ha, Nat.zero_add]

private theorem memWp_getLsbD_ofInt_nonneg {w : Nat} {z : Int} (hz : 0 ≤ z) (i : Nat) :
    (BitVec.ofInt w z).getLsbD i = (decide (i < w) && z.toNat.testBit i) := by
  have hc : z = ((z.toNat : Nat) : Int) := (Int.toNat_of_nonneg hz).symm
  rw [hc, show BitVec.ofInt w (z.toNat : Int) = BitVec.ofNat w z.toNat from rfl, BitVec.getLsbD_ofNat,
    Int.toNat_natCast]

private theorem memWp_getLsbD_ofInt_ofBytes_append (n : Nat) (bs1 bs2 : List UInt8)
    (h : bs1.length + bs2.length = n) (i : Nat) :
    (BitVec.ofInt (8 * n) (Int.ofBytes (bs1 ++ bs2))).getLsbD i =
      if i < 8 * bs1.length then (BitVec.ofInt (8 * bs1.length) (Int.ofBytes bs1)).getLsbD i
      else (BitVec.ofInt (8 * bs2.length) (Int.ofBytes bs2)).getLsbD (i - 8 * bs1.length) := by
  have ha0 := Int.ofBytes_ge_zero bs1
  have hb0 := Int.ofBytes_ge_zero bs2
  have haLt : Int.ofBytes bs1 < 256 ^ bs1.length := Int.ofBytes_lt bs1
  have hc1 : ((Int.ofBytes bs1).toNat : Int) = Int.ofBytes bs1 := Int.toNat_of_nonneg ha0
  have hc2 : ((Int.ofBytes bs2).toNat : Int) = Int.ofBytes bs2 := Int.toNat_of_nonneg hb0
  have hp1 : (256 : Int) ^ bs1.length = ((2 ^ (8 * bs1.length) : Nat) : Int) := by
    rw [show (256 : Int) = ((2 ^ 8 : Nat) : Int) by decide, ← Int.natCast_pow, ← Nat.pow_mul]
  have hsum : Int.ofBytes (bs1 ++ bs2) =
      (((Int.ofBytes bs1).toNat + 2 ^ (8 * bs1.length) * (Int.ofBytes bs2).toNat : Nat) : Int) := by
    rw [Int.ofBytes_append, hp1]
    push_cast
    rw [hc1, hc2]
  have haLt' : (Int.ofBytes bs1).toNat < 2 ^ (8 * bs1.length) := by omega
  rw [memWp_getLsbD_ofInt_nonneg (Int.ofBytes_ge_zero _), memWp_getLsbD_ofInt_nonneg ha0,
    memWp_getLsbD_ofInt_nonneg hb0, hsum, Int.toNat_natCast,
    memWp_getLsbD_ofNat_pow_add _ _ _ i haLt']
  by_cases hi1 : i < 8 * bs1.length
  · have hi_n : i < 8 * n := by omega
    simp [hi1, hi_n]
  · by_cases hi_n : i < 8 * n
    · have hi2 : i - 8 * bs1.length < 8 * bs2.length := by omega
      simp [hi1, hi_n, hi2]
    · have hi2 : ¬ (i - 8 * bs1.length < 8 * bs2.length) := by omega
      simp [hi1, hi_n, hi2]

private theorem memWp_loadVal_bits_of_loadBytes {m : Mem 64} {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a (Ty.bits n).bytes = some bs) :
    loadVal m (.bits n) a = some (BitVec.ofInt n (Int.ofBytes bs)) := by
  simp only [loadVal, Mem.loadInt, h, Option.map_some, Option.bind_some, ofBits]

private theorem memWp_storeOk_of_loadBytes {m : Mem 64} {a : BitVec 64} {t : Ty} {bs : List UInt8}
    (h : m.loadBytes a t.bytes = some bs) : storeOk m t a :=
  ⟨Int.ofBytes bs, by simp [Mem.loadInt, h]⟩

private theorem memWp_storeOk_iff_exists_loadBytes {m : Mem 64} {a : BitVec 64} {t : Ty} :
    storeOk m t a ↔ ∃ bs, m.loadBytes a t.bytes = some bs := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [Mem.loadInt, Option.map_eq_some_iff] at hi
    rcases hi with ⟨bs, hbs, _⟩
    exact ⟨bs, hbs⟩
  · rintro ⟨bs, hbs⟩
    exact memWp_storeOk_of_loadBytes hbs

private theorem memWp_chunkBytes_pos_of_valid (target : LegalTarget) (hv : target.valid = true) (b : Nat) :
    (∀ c ∈ chunkBytes target.bitWidths b, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) ∧
    (chunkBytes target.bitWidths b).sum = b := by
  have h8 : 8 ∈ target.bitWidths := valid_mem8 hv
  have h := chunkBytes_pos_mem_sum target.bitWidths h8 b
  refine ⟨fun c hc => ?_, h.2⟩
  obtain ⟨hp, hm⟩ := h.1 c hc
  exact ⟨hp, hm, (valid_bitWidth_spec hv hm).2.2⟩

private theorem memWp_loadBytes_split3 {m : Mem 64} {a : BitVec 64} {off c rest : Nat} {bs : List UInt8}
    (h : m.loadBytes a (off + (c + rest)) = some bs) :
    ∃ bs1 bs2 bs3,
      bs = bs1 ++ (bs2 ++ bs3) ∧ bs1.length = off ∧ bs2.length = c ∧ bs3.length = rest ∧
      m.loadBytes a off = some bs1 ∧
      m.loadBytes (a + BitVec.ofNat 64 off) c = some bs2 ∧
      m.loadBytes (a + BitVec.ofNat 64 (off + c)) rest = some bs3 := by
  rw [memWp_loadBytes_add] at h
  rcases h with ⟨bs1, bs23, h1, h23, rfl⟩
  rw [memWp_loadBytes_add] at h23
  rcases h23 with ⟨bs2, bs3, h2, h3, rfl⟩
  have hl1 := memWp_loadBytes_length _ _ _ h1
  have hl2 := memWp_loadBytes_length _ _ _ h2
  have hl3 := memWp_loadBytes_length _ _ _ h3
  have ha : (a + BitVec.ofNat 64 off) + BitVec.ofNat 64 c = a + BitVec.ofNat 64 (off + c) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [ha] at h3
  exact ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, h1, h2, h3⟩

private theorem emitLoadChunk_wp (w c byteOff : Nat) (hcw_le_w : 8 * c ≤ w)
    (hltw : 8 * byteOff < w)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {ptr : Arg Val i64} {chunkVal : BitVec (8 * c)}
    (hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) = some chunkVal)
    (cont : Arg Val (.bits w) → Expr Val Cont rs)
    (hk : ∀ sv : Arg Val (.bits w),
      sv.val = chunkVal.setWidth w <<< (8 * byteOff) → wp Γ Q X (cont sv) m) :
    wp Γ Q X
      (if byteOff == 0 then
        Expr.load (.bits (8 * c)) ptr fun raw =>
          if h : 8 * c = w then
            if byteOff == 0 then cont (castArgBits h (.var raw))
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)
          else if 8 * c < w then
            Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
              if byteOff == 0 then cont (.var z)
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
          else
            Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
              if byteOff == 0 then cont (.var z)
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
      else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.load (.bits (8 * c)) (.var ap) fun raw =>
            if h : 8 * c = w then
              if byteOff == 0 then cont (castArgBits h (.var raw))
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
            else if 8 * c < w then
              Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
                if byteOff == 0 then cont (.var z)
                else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                  cont (.var s)
            else
              Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
                if byteOff == 0 then cont (.var z)
                else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                  cont (.var s)) m := by
  have hShift : ∀ (vw : Arg Val (.bits w)), vw.val = chunkVal.setWidth w →
      wp Γ Q X (if byteOff == 0 then cont vw
        else Expr.let_ (op2 (OpCode.shl (.bits w)) vw (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) => cont (.var s)) m := by
    intro vw hvw
    by_cases hb0 : byteOff = 0
    · simp only [hb0, beq_self_eq_true, ↓reduceIte]
      subst hb0
      exact hk vw (by simp [hvw])
    · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
      have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
      have hmod : (BitVec.ofNat w (8 * byteOff)).toNat % w = 8 * byteOff := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hltw hw2), Nat.mod_eq_of_lt hltw]
      simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_shl,
        Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
      exact hk (.var _) (by dsimp only [Arg.val_var]; rw [hmod, hvw])
  have hLoadStep : ∀ (ap : Arg Val i64), ap.val = ptr.val + BitVec.ofNat 64 byteOff →
      wp Γ Q X (Expr.load (.bits (8 * c)) ap fun raw =>
        if h : 8 * c = w then
          if byteOff == 0 then cont (castArgBits h (.var raw))
          else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
            cont (.var s)
        else if 8 * c < w then
          Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
            if byteOff == 0 then cont (.var z)
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)
        else
          Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
            if byteOff == 0 then cont (.var z)
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)) m := by
    intro ap hap
    rw [wp_load, hap]
    refine ⟨chunkVal, hLoadChunk, ?_⟩
    by_cases heq : 8 * c = w
    · simp only [heq, ↓reduceDIte]
      apply hShift (castArgBits heq (.var chunkVal))
      rw [val_castArgBits, Arg.val_var, cast_eq_setWidth heq]
    · have hlt : 8 * c < w := by omega
      simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_zext]
      exact ⟨Nat.le_of_lt hlt, hShift (.var _) rfl⟩
  by_cases hb0 : byteOff = 0
  · simp only [hb0, beq_self_eq_true, ↓reduceIte]
    subst hb0
    exact hLoadStep ptr (by simp)
  · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hLoadStep
    simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
      Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
    exact hLoadStep (.var _) rfl

private theorem emitLoadBits_go_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n w : Nat}
    (hnw : n ≤ w) (hw64 : w ≤ 64) (hw8 : w % 8 = 0) (_hn_pos : 0 < n)
    {m : Mem 64} {ptr : Arg Val i64} {bs : List UInt8}
    (hMem : m.loadBytes ptr.val ((n + 7) / 8) = some bs) :
    ∀ (cs : List Nat) (byteOff : Nat) (acc : Option (Arg Val (.bits w))),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = (n + 7) / 8 →
      (acc = none → byteOff = 0) →
      (∀ ac, acc = some ac → ∀ i, ac.val.getLsbD i =
        if i < 8 * byteOff then (BitVec.ofInt (8 * ((n + 7) / 8)) (Int.ofBytes bs)).getLsbD i
        else false) →
      ∀ {k : Arg Val (.bits w) → Expr Val Cont rs},
        (∀ r : Arg Val (.bits w),
          r.val = (BitVec.ofInt n (Int.ofBytes bs)).setWidth w → wp Γ Q X (k r) m) →
        wp Γ Q X (emitLoadBits.go n w ptr k byteOff cs acc) m
  | [], byteOff, acc, _, hsum, hnone, hacc, k, hk => by
    simp only [List.sum_nil, Nat.add_zero] at hsum
    subst hsum
    cases acc with
    | none =>
      exfalso
      have h0 := hnone rfl
      omega
    | some v =>
      dsimp only [emitLoadBits.go]
      refine emitMaskToN_wp hnw rfl fun r hr => ?_
      apply hk r
      rw [hr]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hv' := hacc v rfl i
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, hv']
      have hlt : i < 8 * ((n + 7) / 8) := by omega
      simp only [hlt, ↓reduceIte]
      have h0 := Int.ofBytes_ge_zero bs
      rw [memWp_getLsbD_ofInt_nonneg h0, memWp_getLsbD_ofInt_nonneg h0]
      simp [hi, hlt]
  | c :: rest, byteOff, acc, hcs, hsum, _hnone, hacc, k, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hb_le_w : 8 * ((n + 7) / 8) ≤ w := by omega
    have hsum' : byteOff + (c + rest.sum) = (n + 7) / 8 := by simpa [List.sum_cons] using hsum
    have hcw_le_w : 8 * c ≤ w := by omega
    have hbl := memWp_loadBytes_length _ _ _ hMem
    have hMem_rw : m.loadBytes ptr.val (byteOff + (c + rest.sum)) = some bs := by rwa [hsum']
    obtain ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, _h1, h2, _h3⟩ := memWp_loadBytes_split3 hMem_rw
    have hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) =
        some (BitVec.ofInt (8 * c) (Int.ofBytes bs2)) := by
      apply memWp_loadVal_bits_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using h2
    have hSvBits : ∀ (sv : Arg Val (.bits w)),
        sv.val = (BitVec.ofInt (8 * c) (Int.ofBytes bs2)).setWidth w <<< (8 * byteOff) →
        ∀ i, sv.val.getLsbD i =
          if 8 * byteOff ≤ i ∧ i < 8 * (byteOff + c) then
            (BitVec.ofInt (8 * ((n + 7) / 8)) (Int.ofBytes (bs1 ++ (bs2 ++ bs3)))).getLsbD i
          else false := by
      intro sv hsv i
      rw [hsv, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      by_cases hi_w : i < w
      · by_cases hi_lo : i < 8 * byteOff
        · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
          simp [hi_lo, hnot]
        · by_cases hi_hi : i < 8 * (byteOff + c)
          · have hsub : i - 8 * byteOff < 8 * c := by omega
            have hsp1 := memWp_getLsbD_ofInt_ofBytes_append (byteOff + (c + rest.sum)) bs1 (bs2 ++ bs3)
              (by simp [hl1, hl2, hl3]) i
            rw [hsum', hl1] at hsp1
            rw [hsp1, ite_eq_right hi_lo]
            have hsp2 := memWp_getLsbD_ofInt_ofBytes_append ((bs2 ++ bs3).length) bs2 bs3
              List.length_append.symm (i - 8 * byteOff)
            rw [List.length_append, hl2, hl3] at hsp2
            rw [List.length_append, hl2, hl3, hsp2, ite_eq_left hsub]
            simp [hi_w, hi_lo, hi_hi, show 8 * byteOff ≤ i by omega, show i - 8 * byteOff < w by omega]
          · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
            rw [BitVec.getLsbD_of_ge _ _ (by omega)]
            simp [hi_w, hi_lo, hnot]
      · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
        simp only [decide_eq_false hi_w, Bool.false_and, hnot, ↓reduceIte]
    dsimp only [emitLoadBits.go]
    cases acc with
    | none =>
      refine emitLoadChunk_wp w c byteOff hcw_le_w (by omega) hLoadChunk
        (fun sv => emitLoadBits.go n w ptr k (byteOff + c) rest (some sv))
        fun sv hsv => ?_
      refine emitLoadBits_go_wp target _hv hnw hw64 hw8 _hn_pos (bs := bs1 ++ (bs2 ++ bs3)) hMem
        rest (byteOff + c) (some sv)
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) (fun h => by cases h)
        (fun ac hac i => ?_) hk
      cases hac
      rw [hSvBits sv hsv i]
      by_cases hi_hi : i < 8 * (byteOff + c)
      · have hb0 := _hnone rfl
        simp [hb0]
      · simp [hi_hi]
    | some prev =>
      refine emitLoadChunk_wp w c byteOff hcw_le_w (by omega) hLoadChunk
        (fun sv => Expr.let_ (op2 (OpCode.or (.bits w)) prev sv) fun (u, _) =>
          emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u)))
        fun sv hsv => ?_
      dsimp only [wp, Op.wp, op2, vals, OpCode.wp_or, lift2, Ty.hasFloat, Bool.false_eq_true]
      refine emitLoadBits_go_wp target _hv hnw hw64 hw8 _hn_pos (bs := bs1 ++ (bs2 ++ bs3)) hMem
        rest (byteOff + c) (some (.var _))
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) (fun h => by cases h)
        (fun ac hac i => ?_) hk
      cases hac
      dsimp only [Arg.val_var]
      rw [BitVec.getLsbD_or, hacc prev rfl i, hSvBits sv hsv i]
      by_cases hi_lo : i < 8 * byteOff
      · have hi_hi : i < 8 * (byteOff + c) := by omega
        simp [hi_lo, hi_hi]
      · by_cases hi_hi : i < 8 * (byteOff + c)
        · simp [hi_lo, hi_hi, show 8 * byteOff ≤ i from by omega]
        · simp [hi_lo, hi_hi]

private theorem emitLoadBits_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n : Nat}
    (hsupp : target.supportsTy (.bits n) = true) (_hnw_ne : n ≠ target.widenWidth n)
    {m : Mem 64} {ptr : Arg Val i64} {v : BitVec n}
    (hLoad : loadVal m (.bits n) ptr.val = some v)
    {k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs}
    (hk : ∀ r : Arg Val (.bits (target.widenWidth n)),
      r.val = v.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitLoadBits target.bitWidths n (target.widenWidth n) ptr k) m := by
  have hnw := le_widenWidth_of_supports hsupp
  have hws := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsupp)
  have hw8 := hws.2.1
  have hw64 := hws.2.2
  unfold emitLoadBits
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.zero_add, show (7 : Nat) / 8 = 0 by decide, beq_self_eq_true, ↓reduceIte]
    apply hk (.imm 0#(target.widenWidth 0))
    rw [Arg.val_imm, Subsingleton.elim v (0#0)]
    apply BitVec.eq_of_toNat_eq; simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hb_ne : ((n + 7) / 8 == 0) = false := beq_false_of_ne (by omega)
    simp only [hb_ne, Bool.false_eq_true, ↓reduceIte]
    simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq] at hLoad
    rcases hLoad with ⟨i, ⟨bs, hMem, rfl⟩, rfl⟩
    obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv ((n + 7) / 8)
    exact emitLoadBits_go_wp target hv hnw hw64 hw8 hn_pos hMem
      (chunkBytes target.bitWidths ((n + 7) / 8)) 0 none hcs (by omega) (fun _ => rfl)
      (fun _ h => by cases h) hk

private theorem emitStoreBits_go_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n w : Nat}
    (hnw : n ≤ w) (hw64 : w ≤ 64) (hw8 : w % 8 = 0) (_hn_pos : 0 < n)
    (v : Arg Val (.bits w)) (ptr : Arg Val i64) (k : Expr Val Cont rs) :
    ∀ (cs : List Nat) (byteOff : Nat) (m : Mem 64),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = (n + 7) / 8 →
      (∃ bs, m.loadBytes (ptr.val + BitVec.ofNat 64 byteOff) cs.sum = some bs) →
      wp Γ Q X k (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes cs.sum ((v.val.toNat : Int) / (256 : Int) ^ byteOff))) →
      wp Γ Q X (emitStoreBits.go w v ptr k byteOff cs) m
  | [], byteOff, m, _, _, _, hk => by
    rw [emitStoreBits.go.eq_1]
    simpa [List.sum_nil, Int.toBytes, memWp_storeBytes_nil] using hk
  | c :: rest, byteOff, m, hcs, hsum, hOk, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hb_le_w : 8 * ((n + 7) / 8) ≤ w := by omega
    have hsum' : byteOff + (c + rest.sum) = (n + 7) / 8 := by simpa [List.sum_cons] using hsum
    have hcw_le_w : 8 * c ≤ w := by omega
    rcases hOk with ⟨bs, hLoad⟩
    rw [List.sum_cons, memWp_loadBytes_add] at hLoad
    rcases hLoad with ⟨bs1, bs2, hLoadC, hLoadRest, _⟩
    have hOkC : storeOk m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) := by
      apply memWp_storeOk_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using hLoadC
    rw [emitStoreBits.go.eq_2]
    dsimp only
    have hShifted : ∀ (cont : Arg Val (.bits w) → Expr Val Cont rs),
        (∀ sv : Arg Val (.bits w), sv.val = v.val >>> (8 * byteOff) → wp Γ Q X (cont sv) m) →
        wp Γ Q X (if byteOff == 0 then cont v
          else Expr.let_ (op2 (OpCode.lshr (.bits w)) v (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) => cont (.var s)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont v (by rw [Nat.mul_zero]; rfl)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
        have hltw : 8 * byteOff < w := by omega
        have hmod : (BitVec.ofNat w (8 * byteOff)).toNat % w = 8 * byteOff := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hltw hw2), Nat.mod_eq_of_lt hltw]
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_lshr,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) (by dsimp only [Arg.val_var]; rw [hmod])
    refine hShifted (fun sv =>
      (fun val =>
        (fun ap => .store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest)) |>
          fun f => if byteOff == 0 then f ptr else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => f (.var ap)) |>
        fun g => if h : 8 * c = w then g (castArgBits h.symm sv)
          else if 8 * c < w then Expr.let_ (op1 (OpCode.trunc w (8 * c)) sv) fun (tr, _) => g (.var tr)
          else Expr.let_ (op1 (OpCode.zext w (8 * c)) sv) fun (tr, _) => g (.var tr))
      fun sv hsv => ?_
    have hToCw : ∀ (cont : Arg Val (.bits (8 * c)) → Expr Val Cont rs),
        (∀ val : Arg Val (.bits (8 * c)),
          val.val = (v.val >>> (8 * byteOff)).setWidth (8 * c) → wp Γ Q X (cont val) m) →
        wp Γ Q X (if h : 8 * c = w then cont (castArgBits h.symm sv)
          else if 8 * c < w then Expr.let_ (op1 (OpCode.trunc w (8 * c)) sv) fun (tr, _) => cont (.var tr)
          else Expr.let_ (op1 (OpCode.zext w (8 * c)) sv) fun (tr, _) => cont (.var tr)) m := by
      intro cont hcont
      by_cases heq : 8 * c = w
      · simp only [heq, ↓reduceDIte]
        apply hcont (castArgBits heq.symm sv)
        rw [val_castArgBits, hsv, cast_eq_setWidth heq.symm]
      · have hlt : 8 * c < w := by omega
        simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hlt, hcont (.var _) (by simp [hsv])⟩
    refine hToCw (fun val =>
      if byteOff == 0 then .store (t := .bits (8 * c)) val ptr (emitStoreBits.go w v ptr k (byteOff + c) rest)
      else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
        .store (t := .bits (8 * c)) val (.var ap) (emitStoreBits.go w v ptr k (byteOff + c) rest))
      fun val hval => ?_
    have hAddr : ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff → wp Γ Q X (cont ap) m) →
        wp Γ Q X (if byteOff == 0 then cont ptr
          else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => cont (.var ap)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont ptr (by simp)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) rfl
    refine hAddr (fun ap => .store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest))
      fun ap hap => ?_
    rw [wp_store, hap]
    refine ⟨hOkC, ?_⟩
    have hbytes_eq : Int.toBytes c (((val.val : BitVec (8 * c)).setWidth (8 * (Ty.bits (8 * c)).bytes)).toInt) =
        Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff) := by
      have hbw : (Ty.bits (8 * c)).bytes = c := by simp [Ty.bytes, Ty.size]; omega
      rw [hbw, BitVec.setWidth_eq, hval]
      exact memWp_int_toBytes_shift (by omega) v.val
    have hm' : storeMem m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) val.val =
        m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
          (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)) := by
      simp only [storeMem, Mem.storeInt, toBits,
        show (Ty.bits (8 * c)).bytes = c by simp [Ty.bytes, Ty.size]; omega]
      exact congrArg (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)) hbytes_eq
    rw [hm']
    have ha_rest : (ptr.val + BitVec.ofNat 64 byteOff) + BitVec.ofNat 64 c =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hOkRest : ∃ bs', (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff))).loadBytes
        (ptr.val + BitVec.ofNat 64 (byteOff + c)) rest.sum = some bs' := by
      apply memWp_loadBytes_isSome_storeBytes
      rw [← ha_rest]
      exact ⟨bs2, hLoadRest⟩
    refine emitStoreBits_go_wp target _hv hnw hw64 hw8 _hn_pos v ptr k rest (byteOff + c) _
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hOkRest ?_
    have hlen_le : (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)).length +
        (Int.toBytes rest.sum ((v.val.toNat : Int) / (256 : Int) ^ (byteOff + c))).length ≤ 2 ^ 64 := by
      rw [Int.toBytes_length, Int.toBytes_length]; omega
    have ha_len : (ptr.val + BitVec.ofNat 64 byteOff) +
        BitVec.ofNat 64 (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)).length =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [Int.toBytes_length, ha_rest]
    rw [← ha_len, ← memWp_storeBytes_append m (ptr.val + BitVec.ofNat 64 byteOff) _ _ hlen_le]
    have hAddBytes :
        Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff) ++
          Int.toBytes rest.sum ((v.val.toNat : Int) / (256 : Int) ^ (byteOff + c)) =
        Int.toBytes (c + rest.sum) ((v.val.toNat : Int) / (256 : Int) ^ byteOff) := by
      rw [memWp_int_toBytes_add c rest.sum ((v.val.toNat : Int) / (256 : Int) ^ byteOff)]
      congr 2
      have hdiv : ((v.val.toNat : Int) / (256 : Int) ^ byteOff) / (256 : Int) ^ c =
          (v.val.toNat : Int) / (256 : Int) ^ (byteOff + c) := by
        rw [Int.pow_add]
        exact (Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)))
      exact hdiv.symm
    rw [hAddBytes]
    simpa [List.sum_cons] using hk

private theorem emitStoreBits_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n : Nat}
    (hsupp : target.supportsTy (.bits n) = true) (_hnw_ne : n ≠ target.widenWidth n)
    {m : Mem 64} {v' : Arg Val (.bits (target.widenWidth n))} {v : BitVec n}
    (hv' : v'.val = v.setWidth (target.widenWidth n)) {ptr : Arg Val i64}
    {k : Expr Val Cont rs}
    (hOk : storeOk m (.bits n) ptr.val)
    (hk : wp Γ Q X k (storeMem m (.bits n) ptr.val v)) :
    wp Γ Q X (emitStoreBits target.bitWidths n (target.widenWidth n) v' ptr k) m := by
  have hnw := le_widenWidth_of_supports hsupp
  have hws := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsupp)
  have hw8 := hws.2.1
  have hw64 := hws.2.2
  unfold emitStoreBits
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.zero_add, show (7 : Nat) / 8 = 0 by decide, beq_self_eq_true, ↓reduceIte]
    simpa [storeMem, Mem.storeInt, Ty.bytes, Ty.size, Int.toBytes, memWp_storeBytes_nil] using hk
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hb_ne : ((n + 7) / 8 == 0) = false := beq_false_of_ne (by omega)
    simp only [hb_ne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bs, hLoad⟩ := memWp_storeOk_iff_exists_loadBytes.mp hOk
    obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv ((n + 7) / 8)
    refine emitStoreBits_go_wp target hv hnw hw64 hw8 hn_pos v' ptr k
      (chunkBytes target.bitWidths ((n + 7) / 8)) 0 m hcs (by omega)
      ⟨bs, by simpa [BitVec.add_zero, hsum, Ty.bytes, Ty.size] using hLoad⟩ ?_
    simp only [BitVec.add_zero, hsum, Int.pow_zero, Int.ediv_one]
    rw [← memWp_int_toBytes_bitVec_toNat ((n + 7) / 8) (target.widenWidth n) (by omega) v'.val]
    have hsw : v'.val.setWidth (8 * ((n + 7) / 8)) = v.setWidth (8 * ((n + 7) / 8)) := by
      rw [hv', BitVec.setWidth_setWidth_of_le _ (by omega)]
    rw [hsw]
    simpa [storeMem, Mem.storeInt, Ty.bytes, Ty.size, toBits] using hk

private theorem size_eq_eight_mul_bytes_of_isByteAlignedStruct :
    ∀ (t : Ty), t.isByteAlignedStruct = true →
      0 < t.size ∧ t.size % 8 = 0 ∧ t.size = 8 * t.bytes ∧ 0 < t.bytes
  | .bool, h => by simp [Ty.isByteAlignedStruct] at h
  | .bits n, h => by
    simp only [Ty.isByteAlignedStruct, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨hpos, hm8⟩
    simp only [Ty.size, Ty.bytes]
    refine ⟨hpos, hm8, by omega, by omega⟩
  | .float f, _ => by cases f <;> decide
  | .pair a b, h => by
    simp only [Ty.isByteAlignedStruct, Bool.and_eq_true] at h
    have ha := size_eq_eight_mul_bytes_of_isByteAlignedStruct a h.1
    have hb := size_eq_eight_mul_bytes_of_isByteAlignedStruct b h.2
    simp only [Ty.size, Ty.bytes] at ha hb ⊢
    omega

private theorem bytes_pair_of_isByteAlignedStruct {a b : Ty}
    (h : (a.pair b).isByteAlignedStruct = true) :
    a.isByteAlignedStruct = true ∧ b.isByteAlignedStruct = true ∧
      (a.pair b).bytes = a.bytes + b.bytes ∧
      a.size = 8 * a.bytes ∧ b.size = 8 * b.bytes ∧ 0 < a.bytes ∧ 0 < b.bytes := by
  simp only [Ty.isByteAlignedStruct, Bool.and_eq_true] at h
  have ha := size_eq_eight_mul_bytes_of_isByteAlignedStruct a h.1
  have hb := size_eq_eight_mul_bytes_of_isByteAlignedStruct b h.2
  refine ⟨h.1, h.2, ?_, ha.2.2.1, hb.2.2.1, ha.2.2.2, hb.2.2.2⟩
  simp only [Ty.bytes, Ty.size] at ha hb ⊢
  omega

private theorem loadVal_eq_of_loadBytes_of_isByteAlignedStruct {m : Mem 64} {p : BitVec 64}
    {t : Ty} (ht : t.isByteAlignedStruct = true) {bs : List UInt8}
    (hm : m.loadBytes p t.bytes = some bs) :
    loadVal m t p = some (ofBits t (BitVec.ofInt t.size (Int.ofBytes bs))) := by
  cases t with
  | bool => simp [Ty.isByteAlignedStruct] at ht
  | bits n => simp [loadVal, Mem.loadInt, hm]
  | float f => simp [loadVal, Mem.loadInt, hm]
  | pair a b => simp [loadVal, Mem.loadInt, hm, Ty.size]

private theorem loadVal_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    {va : Val a} {vb : Val b}
    (hLoad : loadVal m (.pair a b) ptr = some (va, vb)) :
    loadVal m a ptr = some va ∧ loadVal m b (ptr + BitVec.ofNat 64 a.bytes) = some vb := by
  obtain ⟨ha, hb, hbytes, hsa, hsb, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq] at hLoad
  rcases hLoad with ⟨i, ⟨bs, hMem, rfl⟩, hEq⟩
  rw [hbytes, memWp_loadBytes_add] at hMem
  rcases hMem with ⟨bs1, bs2, h1, h2, rfl⟩
  have hl1 := memWp_loadBytes_length _ _ _ h1
  have hl2 := memWp_loadBytes_length _ _ _ h2
  rw [loadVal_eq_of_loadBytes_of_isByteAlignedStruct ha h1,
      loadVal_eq_of_loadBytes_of_isByteAlignedStruct hb h2]
  simp only [ofBits, Prod.mk.injEq] at hEq
  rcases hEq with ⟨hva, hvb⟩
  have hext1 : BitVec.extractLsb' 0 a.size (BitVec.ofInt (a.size + b.size) (Int.ofBytes (bs1 ++ bs2))) =
      BitVec.ofInt a.size (Int.ofBytes bs1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', Nat.zero_add, decide_eq_true hj, Bool.true_and]
    have hsp := memWp_getLsbD_ofInt_ofBytes_append (bs1.length + bs2.length) bs1 bs2 rfl j
    rw [hl1, hl2, Nat.mul_add, ← hsa, ← hsb] at hsp
    rw [hsp, ite_eq_left (by omega)]
  have hext2 : BitVec.extractLsb' a.size b.size (BitVec.ofInt (a.size + b.size) (Int.ofBytes (bs1 ++ bs2))) =
      BitVec.ofInt b.size (Int.ofBytes bs2) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    have hsp := memWp_getLsbD_ofInt_ofBytes_append (bs1.length + bs2.length) bs1 bs2 rfl (a.size + j)
    rw [hl1, hl2, Nat.mul_add, ← hsa, ← hsb] at hsp
    rw [hsp, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rw [hext1] at hva
  rw [hext2] at hvb
  simp [hva, hvb]

private theorem storeOk_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    (hOk : storeOk m (.pair a b) ptr) :
    storeOk m a ptr ∧ ∀ va : Val a, storeOk (storeMem m a ptr va) b (ptr + BitVec.ofNat 64 a.bytes) := by
  obtain ⟨_ha, _hb, hbytes, _, _, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  rw [memWp_storeOk_iff_exists_loadBytes] at hOk
  rcases hOk with ⟨bs, hLoad⟩
  rw [hbytes, memWp_loadBytes_add] at hLoad
  rcases hLoad with ⟨bs1, bs2, h1, h2, _⟩
  refine ⟨memWp_storeOk_of_loadBytes h1, fun va => ?_⟩
  rw [memWp_storeOk_iff_exists_loadBytes]
  exact memWp_loadBytes_isSome_storeBytes _ ⟨bs2, h2⟩

private theorem memWp_toNat_append_bv {n m : Nat} (y : BitVec m) (x : BitVec n) :
    (y ++ x).toNat = x.toNat + 2 ^ n * y.toNat := by
  have hbveq : ∀ {k : Nat} (v : BitVec k), BitVec.ofNat k v.toNat = v := by
    intro k v; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [memWp_getLsbD_ofNat_pow_add x.toNat n y.toNat i x.isLt]
  have hget : (y ++ x).toNat.testBit i = (y ++ x).getLsbD i := by
    conv => rhs; rw [← hbveq (y ++ x)]
    rw [BitVec.getLsbD_ofNat]
    by_cases him : i < m + n
    · simp [him]
    · have hge : (y ++ x).toNat < 2 ^ i :=
        Nat.lt_of_lt_of_le (y ++ x).isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hge]
      simp [him]
  rw [hget, BitVec.getLsbD_append]
  by_cases hin : i < n
  · rw [ite_eq_left hin, ite_eq_left hin]
    conv => lhs; rw [← hbveq x]
    rw [BitVec.getLsbD_ofNat]
    simp [hin]
  · rw [ite_eq_right hin, ite_eq_right hin]
    conv => lhs; rw [← hbveq y]
    rw [BitVec.getLsbD_ofNat]
    by_cases him : i - n < m
    · simp [him]
    · have hge : y.toNat < 2 ^ (i - n) :=
        Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hge]
      simp [him]

private theorem storeMem_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    (hle : (a.pair b).bytes ≤ 2 ^ 64) (va : Val a) (vb : Val b) :
    storeMem (storeMem m a ptr va) b (ptr + BitVec.ofNat 64 a.bytes) vb =
      storeMem m (.pair a b) ptr (va, vb) := by
  obtain ⟨_ha, _hb, hbytes, hsa, hsb, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  simp only [storeMem, Mem.storeInt]
  rw [memWp_int_toBytes_bitVec_toNat a.bytes a.size (by omega) (toBits a va),
      memWp_int_toBytes_bitVec_toNat b.bytes b.size (by omega) (toBits b vb),
      memWp_int_toBytes_bitVec_toNat (a.pair b).bytes (a.pair b).size (by
        simp only [Ty.size] at hsa hsb ⊢; rw [hbytes]; omega) (toBits (.pair a b) (va, vb))]
  have hlen : (Int.toBytes a.bytes ((toBits a va).toNat : Int)).length +
      (Int.toBytes b.bytes ((toBits b vb).toNat : Int)).length ≤ 2 ^ 64 := by
    rw [Int.toBytes_length, Int.toBytes_length, ← hbytes]; exact hle
  have ha_len : ptr + BitVec.ofNat 64 (Int.toBytes a.bytes ((toBits a va).toNat : Int)).length =
      ptr + BitVec.ofNat 64 a.bytes := by rw [Int.toBytes_length]
  rw [← ha_len, ← memWp_storeBytes_append m ptr _ _ hlen]
  congr 1
  rw [hbytes, memWp_int_toBytes_add]
  have hcat : (toBits (.pair a b) (va, vb)).toNat =
      (toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat := by
    simp only [toBits, BitVec.toNat_cast, memWp_toNat_append_bv, hsa]
  rw [hcat]
  have hp : (256 : Int) ^ a.bytes = (2 : Int) ^ (8 * a.bytes) := by
    rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_mul]
  have ha_lt : ((toBits a va).toNat : Int) < (256 : Int) ^ a.bytes := by
    rw [hp, show ((2 : Int) ^ (8 * a.bytes)) = ((2 ^ (8 * a.bytes) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
    exact Int.ofNat_lt.mpr (by rw [← hsa]; exact (toBits a va).isLt)
  have hp_pos : (0 : Int) < (256 : Int) ^ a.bytes := Int.pow_pos (by decide)
  have hmod1 : ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) %
      (2 : Int) ^ (8 * a.bytes) = ((toBits a va).toNat : Int) := by
    push_cast
    rw [← hp, Int.mul_comm ((256 : Int) ^ a.bytes), Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) ha_lt]
  have hdiv1 : ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) /
      (256 : Int) ^ a.bytes = ((toBits b vb).toNat : Int) := by
    push_cast
    rw [← hp, Int.mul_comm ((256 : Int) ^ a.bytes), Int.add_mul_ediv_right _ _ (Int.ne_of_gt hp_pos),
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) ha_lt, Int.zero_add]
  have hleft : Int.toBytes a.bytes ((toBits a va).toNat : Int) =
      Int.toBytes a.bytes ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) := by
    conv => rhs; rw [← Int.toBytes_emod a.bytes]
    dsimp only [Int.take]
    rw [hmod1]
  rw [hleft, hdiv1]

private theorem emitLoadChunk64_wp (c byteOff : Nat) (hc64 : 8 * c ≤ 64)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {ptr : Arg Val i64} {chunkVal : BitVec (8 * c)}
    (hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) = some chunkVal)
    (cont : Arg Val i64 → Expr Val Cont rs)
    (hk : ∀ wd : Arg Val i64, wd.val = chunkVal.setWidth 64 → wp Γ Q X (cont wd) m) :
    wp Γ Q X
      (if byteOff == 0 then
        Expr.load (.bits (8 * c)) ptr fun raw =>
          if h : 8 * c = 64 then cont (castArgBits h (.var raw))
          else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
          else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
       else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.load (.bits (8 * c)) (.var ap) fun raw =>
            if h : 8 * c = 64 then cont (castArgBits h (.var raw))
            else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
            else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)) m := by
  have hStep : ∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff →
      wp Γ Q X (Expr.load (.bits (8 * c)) ap fun raw =>
        if h : 8 * c = 64 then cont (castArgBits h (.var raw))
        else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
        else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)) m := by
    intro ap hap
    rw [wp_load, hap]
    refine ⟨chunkVal, hLoadChunk, ?_⟩
    by_cases heq : 8 * c = 64
    · simp only [heq, ↓reduceDIte]
      apply hk (castArgBits heq (.var chunkVal))
      rw [val_castArgBits, Arg.val_var, cast_eq_setWidth heq]
    · have hlt : 8 * c < 64 := by omega
      simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_zext]
      exact ⟨Nat.le_of_lt hlt, hk (.var _) rfl⟩
  by_cases hb0 : byteOff = 0
  · simp only [hb0, beq_self_eq_true, ↓reduceIte]
    subst hb0
    exact hStep ptr (by simp)
  · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
    simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
      Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
    exact hStep (.var _) rfl

private theorem loadByteChunksToWords64_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bTotal : Nat}
    {m : Mem 64} {ptr : Arg Val i64} {bs : List UInt8}
    (hMem : m.loadBytes ptr.val bTotal = some bs) :
    ∀ (cs : List Nat) (byteOff : Nat)
      (ws : List (Arg Val i64)) (acc : Arg Val i64) (accBits : Nat),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = bTotal →
      Words64Stream ws acc accBits (8 * byteOff)
        (fun i => (BitVec.ofInt (8 * bTotal) (Int.ofBytes bs)).getLsbD i) →
      ∀ {k : List (Arg Val i64) → Expr Val Cont rs},
        (∀ words : List (Arg Val i64),
          (∀ i, i < 8 * bTotal →
            words64GetLsb words i = (BitVec.ofInt (8 * bTotal) (Int.ofBytes bs)).getLsbD i) →
          wp Γ Q X (k words) m) →
        wp Γ Q X (loadByteChunksToWords64 ptr byteOff cs ws acc accBits k) m
  | [], byteOff, ws, acc, accBits, _, hsum, hS, k, hk => by
    simp only [List.sum_nil, Nat.add_zero] at hsum
    subst hsum
    rw [loadByteChunksToWords64.eq_1]
    have ⟨hBits, _, _⟩ := Words64Stream.finish hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits ⊢
      exact hk ws hBits
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits ⊢
      exact hk (ws ++ [acc]) hBits
  | c :: rest, byteOff, ws, acc, accBits, hcs, hsum, hS, k, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hsum' : byteOff + (c + rest.sum) = bTotal := by simpa [List.sum_cons] using hsum
    have hMem_rw : m.loadBytes ptr.val (byteOff + (c + rest.sum)) = some bs := by rwa [hsum']
    obtain ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, _h1, h2, _h3⟩ := memWp_loadBytes_split3 hMem_rw
    have hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) =
        some (BitVec.ofInt (8 * c) (Int.ofBytes bs2)) := by
      apply memWp_loadVal_bits_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using h2
    rw [loadByteChunksToWords64.eq_2]
    dsimp only
    refine emitLoadChunk64_wp c byteOff hcw64 hLoadChunk
      (fun wd => pushLeafWord64 (min (8 * c) 64) wd ws acc accBits fun ws' acc' bits' =>
        loadByteChunksToWords64 ptr (byteOff + c) rest ws' acc' bits' k)
      fun wd hwd => ?_
    refine pushLeafWord64_wp (by omega) hS ?_ (fun _ _ => rfl) ?_ ?_
    · intro j hj
      rw [hwd, BitVec.getLsbD_setWidth]
      have hge : 8 * c ≤ j := by omega
      simp [BitVec.getLsbD_of_ge _ j hge]
    · intro j hj
      have hjc : j < 8 * c := by omega
      rw [hwd, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and]
      have hsp1 := memWp_getLsbD_ofInt_ofBytes_append (byteOff + (c + rest.sum)) bs1 (bs2 ++ bs3)
        (by simp [hl1, hl2, hl3]) (8 * byteOff + j)
      rw [hsum', hl1] at hsp1
      have hnot_lo : ¬ (8 * byteOff + j < 8 * byteOff) := by omega
      rw [hsp1, ite_eq_right hnot_lo]
      have hsp2 := memWp_getLsbD_ofInt_ofBytes_append ((bs2 ++ bs3).length) bs2 bs3
        List.length_append.symm ((8 * byteOff + j) - 8 * byteOff)
      rw [List.length_append, hl2, hl3] at hsp2 ⊢
      rw [Nat.add_sub_cancel_left] at hsp2 ⊢
      rw [hsp2, ite_eq_left hjc]
    · intro ws' acc' accBits' hS'
      rw [show 8 * byteOff + min (8 * c) 64 = 8 * (byteOff + c) by omega] at hS'
      exact loadByteChunksToWords64_wp target _hv hMem rest (byteOff + c) ws' acc' accBits'
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hS' hk

private theorem storeByteChunksFromWords64_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bTotal : Nat} (hb_le : bTotal ≤ 2 ^ 64)
    (words : List (Arg Val i64)) (vec : BitVec (8 * bTotal))
    (hWords : ∀ i, i < 8 * bTotal → words64GetLsb words i = vec.getLsbD i)
    (ptr : Arg Val i64) (k : Expr Val Cont rs) :
    ∀ (cs : List Nat) (byteOff : Nat) (m : Mem 64),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = bTotal →
      (∃ bs, m.loadBytes (ptr.val + BitVec.ofNat 64 byteOff) cs.sum = some bs) →
      wp Γ Q X k (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes cs.sum ((vec.toNat : Int) / (256 : Int) ^ byteOff))) →
      wp Γ Q X (storeByteChunksFromWords64 words ptr byteOff cs k) m
  | [], byteOff, m, _, _, _, hk => by
    rw [storeByteChunksFromWords64.eq_1]
    simpa [List.sum_nil, Int.toBytes, memWp_storeBytes_nil] using hk
  | c :: rest, byteOff, m, hcs, hsum, hOk, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hsum' : byteOff + (c + rest.sum) = bTotal := by simpa [List.sum_cons] using hsum
    rcases hOk with ⟨bs, hLoad⟩
    rw [List.sum_cons, memWp_loadBytes_add] at hLoad
    rcases hLoad with ⟨bs1, bs2, hLoadC, hLoadRest, _⟩
    have hOkC : storeOk m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) := by
      apply memWp_storeOk_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using hLoadC
    rw [storeByteChunksFromWords64.eq_2]
    dsimp only
    refine extractBitsFromWords64_wp (by omega)
      (bits := fun j => vec.getLsbD (8 * byteOff + j))
      (fun j hj => hWords (8 * byteOff + j) (by omega))
      fun raw hRaw => ?_
    have hToCw : ∀ (cont : Arg Val (.bits (8 * c)) → Expr Val Cont rs),
        (∀ val : Arg Val (.bits (8 * c)),
          val.val = (vec >>> (8 * byteOff)).setWidth (8 * c) → wp Γ Q X (cont val) m) →
        wp Γ Q X (if h : 8 * c = 64 then cont (castArgBits h.symm raw)
          else if 8 * c < 64 then Expr.let_ (op1 (OpCode.trunc 64 (8 * c)) raw) fun (tr, _) => cont (.var tr)
          else Expr.let_ (op1 (OpCode.zext 64 (8 * c)) raw) fun (tr, _) => cont (.var tr)) m := by
      intro cont hcont
      by_cases heq : 8 * c = 64
      · simp only [heq, ↓reduceDIte]
        apply hcont (castArgBits heq.symm raw)
        rw [val_castArgBits, cast_eq_setWidth heq.symm]
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hmin : j < min (8 * c) 64 := by omega
        rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, hRaw j,
          BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
        simp [hmin]
      · have hlt : 8 * c < 64 := by omega
        simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hlt, hcont (.var _) ?_⟩
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hmin : j < min (8 * c) 64 := by omega
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, hRaw j,
          BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
        simp [hmin]
    refine hToCw (fun val =>
      if byteOff == 0 then
        Expr.store (t := .bits (8 * c)) val ptr (storeByteChunksFromWords64 words ptr (byteOff + c) rest k)
      else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.store (t := .bits (8 * c)) val (.var ap) (storeByteChunksFromWords64 words ptr (byteOff + c) rest k))
      fun val hval => ?_
    have hAddr : ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff → wp Γ Q X (cont ap) m) →
        wp Γ Q X (if byteOff == 0 then cont ptr
          else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => cont (.var ap)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont ptr (by simp)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) rfl
    refine hAddr (fun ap => .store (t := .bits (8 * c)) val ap (storeByteChunksFromWords64 words ptr (byteOff + c) rest k))
      fun ap hap => ?_
    rw [wp_store, hap]
    refine ⟨hOkC, ?_⟩
    have hbytes_eq : Int.toBytes c (((val.val : BitVec (8 * c)).setWidth (8 * (Ty.bits (8 * c)).bytes)).toInt) =
        Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff) := by
      have hbw : (Ty.bits (8 * c)).bytes = c := by simp [Ty.bytes, Ty.size]; omega
      rw [hbw, BitVec.setWidth_eq, hval]
      exact memWp_int_toBytes_shift (by omega) vec
    have hm' : storeMem m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) val.val =
        m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
          (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)) := by
      simp only [storeMem, Mem.storeInt, toBits,
        show (Ty.bits (8 * c)).bytes = c by simp [Ty.bytes, Ty.size]; omega]
      exact congrArg (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)) hbytes_eq
    rw [hm']
    have ha_rest : (ptr.val + BitVec.ofNat 64 byteOff) + BitVec.ofNat 64 c =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hOkRest : ∃ bs', (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff))).loadBytes
        (ptr.val + BitVec.ofNat 64 (byteOff + c)) rest.sum = some bs' := by
      apply memWp_loadBytes_isSome_storeBytes
      rw [← ha_rest]
      exact ⟨bs2, hLoadRest⟩
    refine storeByteChunksFromWords64_wp target _hv hb_le words vec hWords ptr k rest (byteOff + c) _
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hOkRest ?_
    have hlen_le : (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)).length +
        (Int.toBytes rest.sum ((vec.toNat : Int) / (256 : Int) ^ (byteOff + c))).length ≤ 2 ^ 64 := by
      rw [Int.toBytes_length, Int.toBytes_length]; omega
    have ha_len : (ptr.val + BitVec.ofNat 64 byteOff) +
        BitVec.ofNat 64 (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)).length =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [Int.toBytes_length, ha_rest]
    rw [← ha_len, ← memWp_storeBytes_append m (ptr.val + BitVec.ofNat 64 byteOff) _ _ hlen_le]
    have hAddBytes :
        Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff) ++
          Int.toBytes rest.sum ((vec.toNat : Int) / (256 : Int) ^ (byteOff + c)) =
        Int.toBytes (c + rest.sum) ((vec.toNat : Int) / (256 : Int) ^ byteOff) := by
      rw [memWp_int_toBytes_add c rest.sum ((vec.toNat : Int) / (256 : Int) ^ byteOff)]
      congr 2
      have hdiv : ((vec.toNat : Int) / (256 : Int) ^ byteOff) / (256 : Int) ^ c =
          (vec.toNat : Int) / (256 : Int) ^ (byteOff + c) := by
        rw [Int.pow_add]
        exact (Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)))
      exact hdiv.symm
    rw [hAddBytes]
    simpa [List.sum_cons] using hk

private theorem legalLoad_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
      ∀ {m : Mem 64} {ptr : Arg Val i64} {v : Val t},
        loadVal m t ptr.val = some v →
        ∀ {k : LVar target Val t → Expr Val Cont rs},
          (∀ r : LVar target Val t, valsTup r = encodeVal target t v → wp Γ Q X (k r) m) →
          wp Γ Q X (legalLoad target t ptr k) m
  | .bool, _, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_1, wp_load]
    exact ⟨v, hLoad, hk _ (by dsimp only [LegalTarget.legalTys, encodeVal]; rw [valsTup_single]; rfl)⟩
  | .bits n, hSup, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_2]
    dsimp only
    by_cases hnw : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr hnw
      simp only [hbeq, ↓reduceIte]
      rw [wp_load]
      have hW : ∀ (w : Nat) (h : n = w), loadVal m (.bits w) ptr.val = some (h ▸ v) :=
        fun _ h => by cases h; exact hLoad
      refine ⟨hnw ▸ v, hW (target.widenWidth n) hnw, ?_⟩
      apply hk (.var _, ())
      dsimp only [LegalTarget.legalTys, encodeVal]
      rw [valsTup_single]
      refine congrArg (·, ()) ?_
      dsimp only [Arg.val_var]
      rw [cast_eq_setWidth hnw]
    · have hne : (n == target.widenWidth n) = false := beq_false_of_ne hnw
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      refine emitLoadBits_wp target hv hSup hnw hLoad fun r hr => ?_
      apply hk (r, ())
      dsimp only [LegalTarget.legalTys, encodeVal]
      rw [valsTup_single]
      exact congrArg (·, ()) hr
  | .float f, _, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_3, wp_load]
    exact ⟨v, hLoad, hk _ (by dsimp only [LegalTarget.legalTys, encodeVal]; rw [valsTup_single]; rfl)⟩
  | .pair a b, hSup, hble, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_4]
    dsimp only
    by_cases hp : target.keepsPacked (.pair a b) = true
    · simp only [hp, ↓reduceDIte, wp_load]
      refine ⟨v, hLoad, hk _ (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))⟩
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hp
      rw [dite_eq_right hp]
      have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
        simpa [LegalTarget.supportsTy] using hSup
      by_cases hba : (a.pair b).isByteAlignedStruct = true
      · simp only [hba, ↓reduceIte]
        obtain ⟨_ha, _hb, hbytes, _, _, hapos, _⟩ := bytes_pair_of_isByteAlignedStruct hba
        obtain ⟨hLa, hLb⟩ := loadVal_pair_of_isByteAlignedStruct hba hLoad
        refine legalLoad_wp target hv a hSupPair.1 (by omega) hLa fun la hla => ?_
        have hane : (a.bytes == 0) = false := beq_false_of_ne (by omega)
        simp only [hane, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        refine legalLoad_wp target hv b hSupPair.2 (by omega) (ptr := .var _) hLb fun lb hlb => ?_
        exact hk _ (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hla, hlb]))
      · simp only [hba, Bool.false_eq_true, ↓reduceIte]
        by_cases hbc0 : (a.pair b).bytes = 0
        · have hbe : ((a.pair b).bytes == 0) = true := beq_iff_eq.mpr hbc0
          simp only [hbe, ↓reduceIte]
          have hsz0 : (a.pair b).size = 0 := by simp only [Ty.bytes] at hbc0; omega
          refine unpackWords64ToLeaves_wp target hv (.pair a b) hSup (words := []) (off := 0) (v := v)
            (fun i hi => by omega) fun fres hfres => ?_
          exact packLeavesToLegal_wp target (.pair a b) hSup fres v hfres hk
        · have hbe : ((a.pair b).bytes == 0) = false := beq_false_of_ne hbc0
          simp only [hbe, Bool.false_eq_true, ↓reduceIte]
          have hLoadRaw := hLoad
          simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            Option.some.injEq] at hLoadRaw
          rcases hLoadRaw with ⟨i, ⟨bs, hMem, rfl⟩, rfl⟩
          obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv (a.pair b).bytes
          have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 (8 * 0)
              (fun i => (BitVec.ofInt (8 * (a.pair b).bytes) (Int.ofBytes bs)).getLsbD i) :=
            ⟨by omega, by simp, fun _ _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
          refine loadByteChunksToWords64_wp target hv hMem (chunkBytes target.bitWidths (a.pair b).bytes) 0
            [] (.imm 0#64) 0 hcs (by omega) hS0 fun words hWords => ?_
          refine unpackWords64ToLeaves_wp target hv (.pair a b) hSup (words := words) (off := 0)
            (v := ofBits (.pair a b) (BitVec.ofInt (a.size + b.size) (Int.ofBytes bs))) ?_
            fun fres hfres => ?_
          · intro j hj
            rw [Nat.zero_add, hWords j (by simp only [Ty.bytes] at *; omega)]
            rw [toBits_ofBits]
            have h0 := Int.ofBytes_ge_zero bs
            rw [memWp_getLsbD_ofInt_nonneg h0, memWp_getLsbD_ofInt_nonneg h0]
            have hj1 : j < a.size + b.size := by simpa [Ty.size] using hj
            have hj2 : j < 8 * (a.pair b).bytes := by simp only [Ty.bytes, Ty.size] at *; omega
            simp [hj1, hj2]
          · exact packLeavesToLegal_wp target (.pair a b) hSup fres _ hfres hk

private theorem legalStore_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
      ∀ {m : Mem 64} {xs : LVar target Val t} {ptr : Arg Val i64} {v : Val t},
        valsTup xs = encodeVal target t v →
        storeOk m t ptr.val →
        ∀ {k : Expr Val Cont rs},
          wp Γ Q X k (storeMem m t ptr.val v) →
          wp Γ Q X (legalStore target t xs ptr k) m
  | .bool, _, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v := congrArg Prod.fst hxs
    rw [legalStore.eq_1, wp_store, hvx]
    exact ⟨hOk, hk⟩
  | .bits n, hSup, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v.setWidth (target.widenWidth n) := congrArg Prod.fst hxs
    rw [legalStore.eq_2]
    dsimp only
    by_cases hnw : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr hnw
      simp only [hbeq, ↓reduceIte]
      rw [wp_store]
      have hW : ∀ (w : Nat) (h : n = w) (vx' : Arg Val (.bits w)), vx'.val = v.setWidth w →
          storeOk m (.bits w) ptr.val ∧ wp Γ Q X k (storeMem m (.bits w) ptr.val vx'.val) := by
        intro w h vx' hvx'
        cases h
        simpa [BitVec.setWidth_eq, hvx'] using ⟨hOk, hk⟩
      exact hW (target.widenWidth n) hnw vx hvx
    · have hne : (n == target.widenWidth n) = false := beq_false_of_ne hnw
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact emitStoreBits_wp target hv hSup hnw hvx hOk hk
  | .float f, _, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v := congrArg Prod.fst hxs
    rw [legalStore.eq_3, wp_store, hvx]
    exact ⟨hOk, hk⟩
  | .pair a b, hSup, hble, m, xs, ptr, (va, vb), hxs, hOk, k, hk => by
    rw [legalStore.eq_4]
    dsimp only
    by_cases hp : target.keepsPacked (.pair a b) = true
    · simp only [hp, ↓reduceDIte, wp_store]
      have hpx := valsTup_packedToTup_encode target hp hxs
      dsimp only [valsTup] at hpx
      have hfst : (packedToTup hp xs).fst.val = (va, vb) := congrArg Prod.fst hpx
      rw [hfst]
      exact ⟨hOk, hk⟩
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hp
      rw [dite_eq_right hp]
      have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
        simpa [LegalTarget.supportsTy] using hSup
      by_cases hba : (a.pair b).isByteAlignedStruct = true
      · simp only [hba, ↓reduceIte]
        obtain ⟨_ha, _hb, hbytes, _, _, hapos, _⟩ := bytes_pair_of_isByteAlignedStruct hba
        obtain ⟨hOkA, hOkB⟩ := storeOk_pair_of_isByteAlignedStruct hba hOk
        have hsp := valsTup_splitToTup_encode target hf hxs
        replace hsp := congrArg tupSplit hsp
        rw [tupSplit_valsTup] at hsp
        have hla : valsTup (tupSplit (splitToTup hf xs)).1 = encodeVal target a va := by
          have := congrArg Prod.fst hsp
          simpa [tupSplit_tupAppend] using this
        have hlb : valsTup (tupSplit (splitToTup hf xs)).2 = encodeVal target b vb := by
          have := congrArg Prod.snd hsp
          simpa [tupSplit_tupAppend] using this
        refine legalStore_wp target hv a hSupPair.1 (by omega) hla hOkA ?_
        have hane : (a.bytes == 0) = false := beq_false_of_ne (by omega)
        simp only [hane, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        refine legalStore_wp target hv b hSupPair.2 (by omega) (ptr := .var _) hlb (hOkB va) ?_
        dsimp only [Arg.val_var]
        rwa [storeMem_pair_of_isByteAlignedStruct hba hble va vb]
      · simp only [hba, Bool.false_eq_true, ↓reduceIte]
        by_cases hbc0 : (a.pair b).bytes = 0
        · have hbe : ((a.pair b).bytes == 0) = true := beq_iff_eq.mpr hbc0
          simp only [hbe, ↓reduceIte]
          simpa [storeMem, Mem.storeInt, hbc0, Int.toBytes, memWp_storeBytes_nil] using hk
        · have hbe : ((a.pair b).bytes == 0) = false := beq_false_of_ne hbc0
          simp only [hbe, Bool.false_eq_true, ↓reduceIte]
          refine splitLegalToLeaves_wp target (.pair a b) hSup xs (va, vb) hxs fun fx hfx => ?_
          refine packLeavesToWords64_wp_all target hv (.pair a b) hSup hfx fun words hWords _ _ => ?_
          obtain ⟨bs, hLoad⟩ := memWp_storeOk_iff_exists_loadBytes.mp hOk
          obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv (a.pair b).bytes
          let vec : BitVec (8 * (a.pair b).bytes) := (toBits (.pair a b) (va, vb)).setWidth (8 * (a.pair b).bytes)
          refine storeByteChunksFromWords64_wp target hv hble words vec ?_ ptr k
            (chunkBytes target.bitWidths (a.pair b).bytes) 0 m hcs (by omega)
            ⟨bs, by simpa [BitVec.add_zero, hsum] using hLoad⟩ ?_
          · intro j hj
            rw [hWords j]
            simp only [vec, BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and]
            by_cases hjs : j < (a.pair b).size
            · simp [hjs]
            · simp only [hjs, ↓reduceIte]
              exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
          · simp only [BitVec.add_zero, hsum, Int.pow_zero, Int.ediv_one]
            rw [← memWp_int_toBytes_bitVec_toNat (a.pair b).bytes (8 * (a.pair b).bytes) (by omega) vec]
            have hsw : vec.setWidth (8 * (a.pair b).bytes) = (toBits (.pair a b) (va, vb)).setWidth (8 * (a.pair b).bytes) := by
              simp only [vec, BitVec.setWidth_eq]
            rw [hsw]
            simpa [storeMem, Mem.storeInt] using hk

/-! ### Source support reification, `legalExpr_wp`, `Func.legal_wp`, `Func.legal_spec` -/

private inductive ExprSupports (target : LegalTarget) : {rs : List Ty} → Expr Val Cont rs → Prop
  | let_ {rs ts : List Ty} (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) :
    target.supportsOpCode op.code = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.let_ op k)
  | load {rs : List Ty} (t : Ty) (a : Arg Val i64) (k : Val t → Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    (∀ v, ExprSupports target (k v)) →
    ExprSupports target (.load t a k)
  | store {rs : List Ty} {t : Ty} (v : Arg Val t) (a : Arg Val i64) (k : Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    ExprSupports target k →
    ExprSupports target (.store v a k)
  | call {rs as bs : List Ty} (f : Sym) (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs) :
    as.all target.supportsTy = true → bs.all target.supportsTy = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.call f args k)
  | jnz {rs : List Ty} (c : Arg Val .bool) (t e : Expr Val Cont rs) :
    ExprSupports target t → ExprSupports target e →
    ExprSupports target (.jnz c t e)
  | jump {rs ts : List Ty} (j : Cont ts) (args : Tup (Arg Val) ts) :
    ts.all target.supportsTy = true →
    ExprSupports target (.jump j args)
  | ret {rs : List Ty} (vs : Tup (Arg Val) rs) :
    rs.all target.supportsTy = true →
    ExprSupports target (.ret vs)
  | exit {rs as : List Ty} (f : Sym) (args : Tup (Arg Val) as) :
    as.all target.supportsTy = true →
    ExprSupports target (.exit f args)
  | hlt {rs : List Ty} :
    ExprSupports target (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      (bodies : Tup Cont sig → Blocks Val Cont rs sig)
      (k : Tup Cont sig → Expr Val Cont rs) :
    (sig.all (·.all target.supportsTy)) = true →
    (∀ Js {ts} (i : Member ts sig) xs, ExprSupports target ((bodies Js).get i xs)) →
    (∀ Js, ExprSupports target (k Js)) →
    ExprSupports target (.group bodies k)

private theorem exprSupports_of_wf_toTFlat (target : LegalTarget) :
    {rs : List Ty} → {G : Ctx K Val} → {D : Ctx KL Cont} →
    {eK : Expr K KL rs} → {eV : Expr Val Cont rs} →
    Wf G D eK eV →
    ∀ nv nl, (toTFlat eK nv nl).supportsSource target = true → ExprSupports target eV := by
  intro rs G D eK eV hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_1] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rcases hop with ⟨code, _⟩
    exact ExprSupports.let_ _ k₂ hs.1 fun xs =>
      ih (Tup.levels ts nv) xs (nv + ts.length) nl hs.2
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_2] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.load t a₂ k₂ hs.1.1 hs.1.2 fun v => ih nv v (nv + 1) nl hs.2
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_3] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.store v₂ a₂ k₂ hs.1.1 hs.1.2 (ih nv nl hs.2)
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_4] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    exact ExprSupports.call f args₂ k₂ hs.1.1 hs.1.2 fun xs =>
      ih (Tup.levels bs nv) xs (nv + bs.length) nl hs.2
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro nv nl hs
    rw [toTFlat.eq_5] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    exact ExprSupports.jnz c₂ t₂ e₂ (iht nv nl hs.1) (ihe nv nl hs.2)
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro nv nl hs
    rw [toTFlat.eq_6] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.jump (rs := rs) j₂ args₂ hs
  | @ret G D vs₁ vs₂ hvs =>
    intro nv nl hs
    rw [toTFlat.eq_7] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.ret vs₂ hs
  | @exit G D f as args₁ args₂ hargs =>
    intro nv nl hs
    rw [toTFlat.eq_8] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.exit (rs := rs) f args₂ hs
  | @hlt G D =>
    intro _ _ _
    exact ExprSupports.hlt
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro nv nl hs
    rw [toTFlat.eq_10] at hs
    dsimp only at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    refine ExprSupports.group b₂ k₂ hs.1.1 (fun Js ts i xs => ?_) (fun Js => ?_)
    · have hget := toTBlocks_get target (b₁ (Tup.levels sig nl)) i nv (nl + sig.length) hs.1.2
      exact ihb (Tup.levels sig nl) Js i (Tup.levels ts nv) xs (nv + ts.length) (nl + sig.length) hget.2
    · exact ihk (Tup.levels sig nl) Js nv (nl + sig.length) hs.2

private theorem exprSupports_of_reify (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) (xs : Tup Val as) :
    ExprSupports target (f Val Cont xs) := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
  exact exprSupports_of_wf_toTFlat target (hf K Val KL Cont (Tup.levels as 0) xs) as.length 0 hsupp.2

private theorem cast_legalArg_i64_val (target : LegalTarget) (_hv : target.valid = true)
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {a₁ : Arg Val i64} {a₂ : Arg (LVar target Val) i64} (ha : ArgRel G i64 a₁ a₂)
    (h64 : target.widenWidth 64 = 64) :
    (castArgBits h64 (legalArg target a₂).fst).val = a₁.val := by
  have hval := valsTup_legalArg target hG ha
  dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hval
  have hfst : (legalArg target a₂).fst.val = a₁.val.setWidth (target.widenWidth 64) :=
    congrArg Prod.fst hval
  rw [val_castArgBits, cast_eq_setWidth h64, hfst, BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq]

private theorem legalExpr_wp (target : LegalTarget) (hv : target.valid = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    {rs : List Ty} :
    ∀ {G : Ctx Val (LVar target Val)} {D : Ctx Cont (LLab target Cont)}
      {e₁ : Expr Val Cont rs} {e₂ : Expr (LVar target Val) (LLab target Cont) rs},
      Wf G D e₁ e₂ →
      CGoodWp target G → DGoodWp target D →
      ExprSupports target e₁ →
      ∀ {Q : Post rs} {X : XPost} {m : Mem 64},
        wp Γsrc Q X e₁ m →
        wp Γtgt (legalPost target Q) (legalXPost target X) (legalExpr target e₂) m := by
  intro G D e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_let] at hwp
    rw [legalExpr.eq_1]
    cases hSupp with | let_ _ _ hs_op hs_k =>
    refine legalOp_wp target hv hG hop hs_op hwp fun r lr hrel hr => ?_
    exact ih r lr (CGoodWp.pushTRel target hG hrel) hD (hs_k r) hr
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_load] at hwp
    rcases hwp with ⟨v, hLoad, hwpk⟩
    cases hSupp with | load _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    rw [legalExpr.eq_2, dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalLoad_wp target hv t hst hble (ptr := castArgBits h64 (legalArg target a₂).fst)
      (by rwa [hap]) fun lr hlr => ?_
    refine ih v lr ?_ hD (hs_k v) hwpk
    intro t' x' lv' hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hlr
    · exact hG _ _ _ htail
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv_rel ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_store] at hwp
    rcases hwp with ⟨hOk, hwpk⟩
    cases hSupp with | store _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    rw [legalExpr.eq_3, dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalStore_wp target hv t hst hble (xs := legalArg target v₂)
      (ptr := castArgBits h64 (legalArg target a₂).fst) (v := v₁.val)
      (valsTup_legalArg target hG hv_rel) (by rwa [hap]) ?_
    rw [hap]
    exact ih hG hD hs_k hwpk
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | call _ _ _ _ _ hs_k =>
    rw [legalExpr.eq_4]
    dsimp only [wp, wp._f] at hwp ⊢
    rcases hwp with ⟨P, E, hCall, hPost, hExit⟩
    refine ⟨legalPost target P, legalXPost target E, ?_, ?_, ?_⟩
    · have hJoin := valsTup_joinArgs target hG hargs
      rw [valsTup_eq_vals] at hJoin
      rw [valsTup_eq_vals] at hJoin
      rw [hJoin]
      exact hEnv f as bs (vals args₁) m P E hCall
    · rintro ys m' ⟨xs, rfl, hP⟩
      exact ih xs (splitParams target bs (encodeTup target bs xs))
        (CGoodWp.pushSplit target hG bs xs) hD (hs_k xs) (hPost xs m' hP)
    · rintro g cs' ys m' ⟨cs, hcs, xs, rfl, hE⟩
      exact ⟨cs, hcs, xs, rfl, hExit g cs xs m' hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | jnz _ _ _ hst hse =>
    rw [wp_jnz] at hwp
    rw [legalExpr.eq_5, wp_jnz]
    have hcv := valsTup_legalArg target hG hc
    dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hcv
    have hceq : (legalArg target c₂).fst.val = c₁.val := congrArg Prod.fst hcv
    rw [hceq]
    exact ⟨fun h => iht hG hD hst (hwp.1 h), fun h => ihe hG hD hse (hwp.2 h)⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro hG hD _ Q X m hwp
    rw [wp_jump] at hwp
    rw [legalExpr.eq_6, wp_jump]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    rw [hJoin]
    exact hD ts j₁ j₂ hj (vals args₁) m hwp
  | @ret G D vs₁ vs₂ hvs =>
    intro hG _ _ Q X m hwp
    rw [wp_ret] at hwp
    rw [legalExpr.eq_7, wp_ret]
    have hJoin := valsTup_joinArgs target hG hvs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨vals vs₁, hJoin.symm, hwp⟩
  | @exit G D f as args₁ args₂ hargs =>
    intro hG _ _ Q X m hwp
    rw [wp_exit] at hwp
    rw [legalExpr.eq_8, wp_exit]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨as, rfl, vals args₁, hJoin.symm, hwp⟩
  | @hlt G D =>
    intro _ _ _ _ _ _ hwp
    cases hwp
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | group _ _ _ hs_b hs_k =>
    rw [legalExpr.eq_10]
    dsimp only [wp, wp._f] at hwp ⊢
    intro Js2 hClosed2
    have hD' : DGoodWp target (Tup.zip (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) ++ D) :=
      DGoodWp.pushUnlegal target hD Js2
    have hClosed1 : Closed Γsrc Q X (b₁ (unlegalTupCont target Js2)) (unlegalTupCont target Js2) := by
      rw [closed_iff]
      intro ts i xs m' hbody1
      rw [unlegalTupCont_get]
      rw [closed_iff] at hClosed2
      apply hClosed2 (Member.map target.legalSig i) (encodeTup target ts xs) m'
      rw [legalBlocks_get]
      exact ihb (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) i xs
        (splitParams target ts (encodeTup target ts xs))
        (CGoodWp.pushSplit target hG ts xs) hD' (hs_b (unlegalTupCont target Js2) i xs) hbody1
    exact ihk (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2)
      hG hD' (hs_k (unlegalTupCont target Js2)) (hwp (unlegalTupCont target Js2) hClosed1)

/-- `Func.legal` semantic preservation under any target environment refining `Γsrc`. -/
theorem Func.legal_wp_of_refines (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γsrc f xs m Q X →
    Func.wp Γtgt (f.legal target) (encodeTup target as xs) m (legalPost target Q) (legalXPost target X) := by
  intro hwp
  have hv : target.valid = true := by
    simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
    exact hsupp.1.1.1
  unfold Func.wp Func.legal
  exact legalExpr_wp target hv hEnv
    (hf Val (LVar target Val) Cont (LLab target Cont) xs (splitParams target as (encodeTup target as xs)))
    (by simpa using CGoodWp.pushSplit target (fun _ _ _ hm => False.elim (List.not_mem_nil hm)) as xs)
    (fun _ _ _ hm => False.elim (List.not_mem_nil hm))
    (exprSupports_of_reify target f hf hsupp xs)
    hwp

/-- Main `T5` semantic preservation theorem for `Func.legal` with canonical `legalEnv`. -/
theorem Func.legal_wp (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γ f xs m Q X →
    Func.wp (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp_of_refines target f hf hsupp (envRefines_legalEnv target Γ) xs m Q X

/-- Specification-style consequence of `Func.legal_wp` matching E1's `Spec` convention. -/
theorem Func.legal_spec (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.spec Γ f xs m Q X →
    Func.spec (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target f hf hsupp Γ xs m Q X

/-- Specification preservation for closed `Fn` units via `Fn.legal`. -/
theorem Fn.legal_spec (target : LegalTarget) (fn : Fn)
    (hf : fn.body.Wf) (hsupp : fn.body.supportsSource target = true)
    (Γ : Env) (xs : Tup Val fn.as) (m : Mem 64) (Q : Post fn.rs) (X : XPost) :
    Func.spec Γ fn.body xs m Q X →
    Func.spec (legalEnv target Γ) (fn.legal target).body (encodeTup target fn.as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target fn.body hf hsupp Γ xs m Q X

end LegalWp

end LeanQbe.T








