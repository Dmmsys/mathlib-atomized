/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Bitwise
public import Mathlib.Data.Int.Order.Lemmas
public import Mathlib.Order.Interval.Set.Defs

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`Data.Int.Basic` or `Data.Int.Order`.

-/

public section


open Nat

namespace Int

/--
theorem `le_natCast_sub` / 定理 `le_natCast_sub`

English:
theorem le_natCast_sub
  given: (m n : Nat)
  statement: (m - n : Int) <= ↑(m - n : Nat)
  proof: by
  lia

中文:
定理 le_natCast_sub
  条件: (m n : 自然数)
  结论: (m - n : 整数) <= ↑(m - n : 自然数)
  证明: by
  lia
-/
theorem le_natCast_sub (m n : Nat) : (m - n : Int) <= ↑(m - n : Nat) := by
  lia



/--
theorem `succ_natCast_pos` / 定理 `succ_natCast_pos`

English:
theorem succ_natCast_pos
  given: (n : Nat)
  statement: 0 < (n : Int) + 1
  proof: lt_add_one_iff.mpr (by simp)

中文:
定理 succ_natCast_pos
  条件: (n : 自然数)
  结论: 0 < (n : 整数) + 1
  证明: lt_add_one_iff.mpr (by simp)

Depends on / 依赖: lt_add_one_iff, lt_add_one_iff.mpr
-/
theorem succ_natCast_pos (n : Nat) : 0 < (n : Int) + 1 :=
  lt_add_one_iff.mpr (by simp)



/--
theorem `natAbs_eq_iff_sq_eq` / 定理 `natAbs_eq_iff_sq_eq`

English:
theorem natAbs_eq_iff_sq_eq
  given: {a b : Int}
  statement: a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2
  proof: by
  rw [sq]; rw [sq]
  exact natAbs_eq_iff_mul_self_eq

中文:
定理 natAbs_eq_iff_sq_eq
  条件: {a b : 整数}
  结论: a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2
  证明: by
  rw [sq]; rw [sq]
  exact natAbs_eq_iff_mul_self_eq

Depends on / 依赖: natAbs_eq_iff_mul_self_eq
-/
theorem natAbs_eq_iff_sq_eq {a b : Int} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq]; rw [sq]
  exact natAbs_eq_iff_mul_self_eq

/--
theorem `natAbs_lt_iff_sq_lt` / 定理 `natAbs_lt_iff_sq_lt`

English:
theorem natAbs_lt_iff_sq_lt
  given: {a b : Int}
  statement: a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2
  proof: by
  rw [sq]; rw [sq]
  exact natAbs_lt_iff_mul_self_lt

中文:
定理 natAbs_lt_iff_sq_lt
  条件: {a b : 整数}
  结论: a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2
  证明: by
  rw [sq]; rw [sq]
  exact natAbs_lt_iff_mul_self_lt

Depends on / 依赖: natAbs_lt_iff_mul_self_lt
-/
theorem natAbs_lt_iff_sq_lt {a b : Int} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq]; rw [sq]
  exact natAbs_lt_iff_mul_self_lt

/--
theorem `natAbs_le_iff_sq_le` / 定理 `natAbs_le_iff_sq_le`

English:
theorem natAbs_le_iff_sq_le
  given: {a b : Int}
  statement: a.natAbs <= b.natAbs ↔ a ^ 2 <= b ^ 2
  proof: by
  rw [sq]; rw [sq]
  exact natAbs_le_iff_mul_self_le

中文:
定理 natAbs_le_iff_sq_le
  条件: {a b : 整数}
  结论: a.natAbs <= b.natAbs ↔ a ^ 2 <= b ^ 2
  证明: by
  rw [sq]; rw [sq]
  exact natAbs_le_iff_mul_self_le

Depends on / 依赖: natAbs_le_iff_mul_self_le
-/
theorem natAbs_le_iff_sq_le {a b : Int} : a.natAbs <= b.natAbs ↔ a ^ 2 <= b ^ 2 := by
  rw [sq]; rw [sq]
  exact natAbs_le_iff_mul_self_le

/--
theorem `natAbs_inj_of_nonneg_of_nonneg` / 定理 `natAbs_inj_of_nonneg_of_nonneg`

English:
theorem natAbs_inj_of_nonneg_of_nonneg
  given: {a b : Int} (ha : 0 <= a) (hb : 0 <= b)
  proof: by rw [← sq_eq_sq₀ ha hb, ← natAbs_eq_iff_sq_eq]

中文:
定理 natAbs_inj_of_nonneg_of_nonneg
  条件: {a b : 整数} (ha : 0 <= a) (hb : 0 <= b)
  证明: by rw [← sq_eq_sq₀ ha hb, ← natAbs_eq_iff_sq_eq]

Depends on / 依赖: natAbs_eq_iff_sq_eq
-/
theorem natAbs_inj_of_nonneg_of_nonneg {a b : Int} (ha : 0 <= a) (hb : 0 <= b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq₀ ha hb, ← natAbs_eq_iff_sq_eq]

/--
theorem `natAbs_inj_of_nonpos_of_nonpos` / 定理 `natAbs_inj_of_nonpos_of_nonpos`

English:
theorem natAbs_inj_of_nonpos_of_nonpos
  given: {a b : Int} (ha : a <= 0) (hb : b <= 0)
  proof: by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

中文:
定理 natAbs_inj_of_nonpos_of_nonpos
  条件: {a b : 整数} (ha : a <= 0) (hb : b <= 0)
  证明: by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

Depends on / 依赖: Int.natAbs_neg, natAbs_inj_of_nonneg_of_nonneg, natAbs_neg, neg_inj, neg_nonneg_of_nonpos
-/
theorem natAbs_inj_of_nonpos_of_nonpos {a b : Int} (ha : a <= 0) (hb : b <= 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

/--
theorem `natAbs_inj_of_nonneg_of_nonpos` / 定理 `natAbs_inj_of_nonneg_of_nonpos`

English:
theorem natAbs_inj_of_nonneg_of_nonpos
  given: {a b : Int} (ha : 0 <= a) (hb : b <= 0)
  proof: by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

中文:
定理 natAbs_inj_of_nonneg_of_nonpos
  条件: {a b : 整数} (ha : 0 <= a) (hb : b <= 0)
  证明: by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

Depends on / 依赖: Int.natAbs_neg, natAbs_inj_of_nonneg_of_nonneg, natAbs_neg, neg_nonneg_of_nonpos
-/
theorem natAbs_inj_of_nonneg_of_nonpos {a b : Int} (ha : 0 <= a) (hb : b <= 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

/--
theorem `natAbs_inj_of_nonpos_of_nonneg` / 定理 `natAbs_inj_of_nonpos_of_nonneg`

English:
theorem natAbs_inj_of_nonpos_of_nonneg
  given: {a b : Int} (ha : a <= 0) (hb : 0 <= b)
  proof: by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

中文:
定理 natAbs_inj_of_nonpos_of_nonneg
  条件: {a b : 整数} (ha : a <= 0) (hb : 0 <= b)
  证明: by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

Depends on / 依赖: Int.natAbs_neg, natAbs_inj_of_nonneg_of_nonneg, natAbs_neg, neg_nonneg_of_nonpos
-/
theorem natAbs_inj_of_nonpos_of_nonneg {a b : Int} (ha : a <= 0) (hb : 0 <= b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

/--
theorem `natAbs_coe_sub_coe_le_of_le` / 定理 `natAbs_coe_sub_coe_le_of_le`

English:
theorem natAbs_coe_sub_coe_le_of_le
  given: {a b n : Nat} (a_le_n : a <= n) (b_le_n : b <= n)
  proof: by
  rw [← Nat.cast_le (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (natCast_nonneg a) (ofNat_le.mpr a_le_n)
    (natCast_nonneg b) (ofNat_le.mpr b_le_n)

中文:
定理 natAbs_coe_sub_coe_le_of_le
  条件: {a b n : 自然数} (a_le_n : a <= n) (b_le_n : b <= n)
  证明: by
  rw [← Nat.cast_le (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (natCast_nonneg a) (ofNat_le.mpr a_le_n)
    (natCast_nonneg b) (ofNat_le.mpr b_le_n)

Depends on / 依赖: Nat.cast_le, a_le_n, abs_sub_le_of_nonneg_of_le, b_le_n, cast_le, natCast_natAbs, natCast_nonneg, ofNat_le, ofNat_le.mpr
-/
theorem natAbs_coe_sub_coe_le_of_le {a b n : Nat} (a_le_n : a <= n) (b_le_n : b <= n) :
    natAbs (a - b : Int) <= n := by
  rw [← Nat.cast_le (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (natCast_nonneg a) (ofNat_le.mpr a_le_n)
    (natCast_nonneg b) (ofNat_le.mpr b_le_n)

/--
theorem `natAbs_coe_sub_coe_lt_of_lt` / 定理 `natAbs_coe_sub_coe_lt_of_lt`

English:
theorem natAbs_coe_sub_coe_lt_of_lt
  given: {a b n : Nat} (a_lt_n : a < n) (b_lt_n : b < n)
  proof: by
  rw [← Nat.cast_lt (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (natCast_nonneg a) (ofNat_lt.mpr a_lt_n)
    (natCast_nonneg b) (ofNat_lt.mpr b_lt_n)

中文:
定理 natAbs_coe_sub_coe_lt_of_lt
  条件: {a b n : 自然数} (a_lt_n : a < n) (b_lt_n : b < n)
  证明: by
  rw [← Nat.cast_lt (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (natCast_nonneg a) (ofNat_lt.mpr a_lt_n)
    (natCast_nonneg b) (ofNat_lt.mpr b_lt_n)

Depends on / 依赖: Nat.cast_lt, a_lt_n, abs_sub_lt_of_nonneg_of_lt, b_lt_n, cast_lt, natCast_natAbs, natCast_nonneg, ofNat_lt, ofNat_lt.mpr
-/
theorem natAbs_coe_sub_coe_lt_of_lt {a b n : Nat} (a_lt_n : a < n) (b_lt_n : b < n) :
    natAbs (a - b : Int) < n := by
  rw [← Nat.cast_lt (α := Int)]; rw [natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (natCast_nonneg a) (ofNat_lt.mpr a_lt_n)
    (natCast_nonneg b) (ofNat_lt.mpr b_lt_n)

section Intervals

open Set

/--
theorem `strictMonoOn_natAbs` / 定理 `strictMonoOn_natAbs`

English:
theorem strictMonoOn_natAbs
  statement: StrictMonoOn natAbs (Ici 0)
  proof: fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab

中文:
定理 strictMonoOn_natAbs
  结论: StrictMonoOn natAbs (Ici 0)
  证明: fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab
-/
theorem strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0) := fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab

/--
theorem `strictAntiOn_natAbs` / 定理 `strictAntiOn_natAbs`

English:
theorem strictAntiOn_natAbs
  statement: StrictAntiOn natAbs (Iic 0)
  proof: fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

中文:
定理 strictAntiOn_natAbs
  结论: StrictAntiOn natAbs (Iic 0)
  证明: fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

Depends on / 依赖: Int.natAbs_neg, Right.nonneg_neg_iff.mpr, natAbs_lt_natAbs_of_nonneg_of_lt, natAbs_neg, neg_lt_neg_iff, neg_lt_neg_iff.mpr, nonneg_neg_iff
-/
theorem strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0) := fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

/--
theorem `injOn_natAbs_Ici` / 定理 `injOn_natAbs_Ici`

English:
theorem injOn_natAbs_Ici
  statement: InjOn natAbs (Ici 0)
  proof: strictMonoOn_natAbs.injOn

中文:
定理 injOn_natAbs_Ici
  结论: InjOn natAbs (Ici 0)
  证明: strictMonoOn_natAbs.injOn

Depends on / 依赖: strictMonoOn_natAbs, strictMonoOn_natAbs.injOn
-/
theorem injOn_natAbs_Ici : InjOn natAbs (Ici 0) :=
  strictMonoOn_natAbs.injOn

/--
theorem `injOn_natAbs_Iic` / 定理 `injOn_natAbs_Iic`

English:
theorem injOn_natAbs_Iic
  statement: InjOn natAbs (Iic 0)
  proof: strictAntiOn_natAbs.injOn

中文:
定理 injOn_natAbs_Iic
  结论: InjOn natAbs (Iic 0)
  证明: strictAntiOn_natAbs.injOn

Depends on / 依赖: strictAntiOn_natAbs, strictAntiOn_natAbs.injOn
-/
theorem injOn_natAbs_Iic : InjOn natAbs (Iic 0) :=
  strictAntiOn_natAbs.injOn

end Intervals

/-! ### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from `Data.Int.Order`.
-/

@[simp]
/--
theorem `div2_bit` / 定理 `div2_bit`

English:
theorem div2_bit
  given: (b n)
  statement: div2 (bit b n) = n
  proof: by
  rw [bit_val]; rw [div2_val]; rw [add_comm]; rw [Int.add_mul_ediv_left]; rw [(_ : (_ / 2 : Int) = 0)]; rw [zero_add]
  cases b
  · decide
  · change ofNat _ = _
    rw [Nat.div_eq_of_lt] <;> simp
  · decide

中文:
定理 div2_bit
  条件: (b n)
  结论: div2 (bit b n) = n
  证明: by
  rw [bit_val]; rw [div2_val]; rw [add_comm]; rw [Int.add_mul_ediv_left]; rw [(_ : (_ / 2 : Int) = 0)]; rw [zero_add]
  cases b
  · decide
  · change ofNat _ = _
    rw [Nat.div_eq_of_lt] <;> simp
  · decide

Depends on / 依赖: Int.add_mul_ediv_left, Nat.div_eq_of_lt, add_comm, add_mul_ediv_left, bit_val, div2_val, div_eq_of_lt, zero_add
-/
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val]; rw [div2_val]; rw [add_comm]; rw [Int.add_mul_ediv_left]; rw [(_ : (_ / 2 : Int) = 0)]; rw [zero_add]
  cases b
  · decide
  · change ofNat _ = _
    rw [Nat.div_eq_of_lt] <;> simp
  · decide

/--
theorem `ediv_emod_unique''` / 定理 `ediv_emod_unique''`

English:
theorem ediv_emod_unique''
  given: {a b r q : Int} (h : b != 0)
  proof: by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_mul_ediv a b, emod_nonneg _ h, emod_lt_abs _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q h, ediv_eq_zero_of_lt_abs hz hb]
      simp
    · rw [add_mul_emod_self_left, ← emod_abs, emod_eq_of_lt hz hb]

中文:
定理 ediv_emod_unique''
  条件: {a b r q : 整数} (h : b != 0)
  证明: by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_mul_ediv a b, emod_nonneg _ h, emod_lt_abs _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q h, ediv_eq_zero_of_lt_abs hz hb]
      simp
    · rw [add_mul_emod_self_left, ← emod_abs, emod_eq_of_lt hz hb]

Depends on / 依赖: Int.add_mul_ediv_left, add_mul_ediv_left, add_mul_emod_self_left, ediv_eq_zero_of_lt_abs, emod_abs, emod_add_mul_ediv, emod_eq_of_lt, emod_lt_abs, emod_nonneg
-/
theorem ediv_emod_unique'' {a b r q : Int} (h : b != 0) :
    a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 <= r ∧ r < |b| := by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_mul_ediv a b, emod_nonneg _ h, emod_lt_abs _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q h, ediv_eq_zero_of_lt_abs hz hb]
      simp
    · rw [add_mul_emod_self_left, ← emod_abs, emod_eq_of_lt hz hb]

end Int
