/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Data.ENNReal.Inv

/-! # Hölder triples

This file defines a new class: `ENNReal.HolderTriple` which takes arguments `p q r : ℝ≥0∞`,
with `r` marked as a `semiOutParam`, and states that `p⁻¹ + q⁻¹ = r⁻¹`. This is exactly the
condition for which **Hölder's inequality** is valid (see `MeasureTheory.MemLp.smul`).
This allows us to declare a heterogeneous scalar multiplication (`HSMul`) instance on
`MeasureTheory.Lp` spaces.

In this file we provide many convenience lemmas in the presence of a `HolderTriple` instance.
All these are easily provable from facts about `ℝ≥0∞`, but it's convenient not to be forced
to reprove them each time.

For convenience we also define `ENNReal.HolderConjugate` (with arguments `p q`) as an
abbreviation for `ENNReal.HolderTriple p q 1`.
-/

public section

namespace ENNReal

/-- A class stating that `p q r : ℝ≥0∞` satisfy `p⁻¹ + q⁻¹ = r⁻¹`.
This is exactly the condition for which **Hölder's inequality** is valid
(see `MeasureTheory.MemLp.smul`).

When `r := 1`, one generally says that `p q` are **Hölder conjugate**.

This class exists so that we can define a heterogeneous scalar multiplication
on `MeasureTheory.Lp`, and this is why `r` must be marked as a
`semiOutParam`. We don't mark it as an `outParam` because this would
prevent Lean from using `HolderTriple p q r` and `HolderTriple p q r'`
within a single proof, as may be occasionally convenient. -/
@[mk_iff]
/--
Definition of `HolderTriple` / `HolderTriple` 的定义

English:
class HolderTriple
  parameters: (p q : Real>=0∞) (r : semiOutParam Real>=0∞)
  axioms and operations (1):
    - inv_add_inv_eq_inv((p q r)) : p⁻¹ + q⁻¹ = r⁻¹

中文:
类 HolderTriple
  参数: (p q : 实数>=0∞) (r : semiOutParam 实数>=0∞)
  公理与运算 (1 个):
    - inv_add_inv_eq_inv((p q r)) : p⁻¹ + q⁻¹ = r⁻¹
-/
class HolderTriple (p q : Real>=0∞) (r : semiOutParam Real>=0∞) : Prop where
  inv_add_inv_eq_inv (p q r) : p⁻¹ + q⁻¹ = r⁻¹

/--
Definition of `HolderConjugate` / `HolderConjugate` 的定义

English:
abbreviation HolderConjugate
  signature: (p q : Real>=0∞)
  body: HolderTriple p q 1

中文:
缩写 HolderConjugate
  签名: (p q : 实数>=0∞)
  定义体: HolderTriple p q 1

Depends on / 依赖: HolderTriple
-/
abbrev HolderConjugate (p q : Real>=0∞) := HolderTriple p q 1

/--
lemma `holderConjugate_iff` / 引理 `holderConjugate_iff`

English:
lemma holderConjugate_iff
  given: {p q : Real>=0∞}
  statement: HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1
  proof: by
  simp [holderTriple_iff]

中文:
引理 holderConjugate_iff
  条件: {p q : 实数>=0∞}
  结论: HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1
  证明: by
  simp [holderTriple_iff]

Depends on / 依赖: holderTriple_iff
-/
lemma holderConjugate_iff {p q : Real>=0∞} : HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1 := by
  simp [holderTriple_iff]

/-! ### Hölder triples -/

namespace HolderTriple

/--
lemma `of` / 引理 `of`

English:
lemma of
  given: (p q : Real>=0∞)
  statement: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  proof: inv_inv _

中文:
引理 of
  条件: (p q : 实数>=0∞)
  结论: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  证明: inv_inv _

Depends on / 依赖: inv_inv
-/
lemma of (p q : Real>=0∞) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
.symm inv_add_inv_eq_inv := inv_inv _

/--
Instance `symm` / 实例 `symm`

English:
instance symm
  signature: {p q r : Real>=0∞} [hpqr : HolderTriple p q r]
  body: add_comm p⁻¹ q⁻¹ ▸ hpqr.inv_add_inv_eq_inv

中文:
实例 symm
  签名: {p q r : 实数>=0∞} [hpqr : HolderTriple p q r]
  定义体: add_comm p⁻¹ q⁻¹ ▸ hpqr.inv_add_inv_eq_inv

Depends on / 依赖: add_comm, hpqr.inv_add_inv_eq_inv, inv_add_inv_eq_inv
-/
instance symm {p q r : Real>=0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ hpqr.inv_add_inv_eq_inv

/--
Instance `instInfty` / 实例 `instInfty`

English:
instance instInfty
  signature: (p : Real>=0∞)
  body: by simp

中文:
实例 instInfty
  签名: (p : 实数>=0∞)
  定义体: by simp
-/
instance instInfty (p : Real>=0∞) : HolderTriple p ∞ p where
  inv_add_inv_eq_inv := by simp

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: (p : Real>=0∞)
  body: by simp

中文:
实例 instZero
  签名: (p : 实数>=0∞)
  定义体: by simp
-/
instance instZero (p : Real>=0∞) : HolderTriple p 0 0 where
  inv_add_inv_eq_inv := by simp

variable (p q r : Real>=0∞) [HolderTriple p q r]

/--
lemma `inv_eq` / 引理 `inv_eq`

English:
lemma inv_eq
  statement: r⁻¹ = p⁻¹ + q⁻¹
  proof: (inv_add_inv_eq_inv ..).symm

中文:
引理 inv_eq
  结论: r⁻¹ = p⁻¹ + q⁻¹
  证明: (inv_add_inv_eq_inv ..).symm

Depends on / 依赖: inv_add_inv_eq_inv
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := (inv_add_inv_eq_inv ..).symm

/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: (r' : Real>=0∞) [hr' : HolderTriple p q r']
  statement: r = r'
  proof: by
  rw [← inv_inj]; rw [inv_eq p q r]; rw [inv_eq p q r']

中文:
引理 unique
  条件: (r' : 实数>=0∞) [hr' : HolderTriple p q r']
  结论: r = r'
  证明: by
  rw [← inv_inj]; rw [inv_eq p q r]; rw [inv_eq p q r']

Depends on / 依赖: _cons_of_neg, _cons_of_pos, dropWhile_cons_of_neg, dropWhile_cons_of_pos, inv_eq, inv_inj, phh.symm
-/
lemma unique (r' : Real>=0∞) [hr' : HolderTriple p q r'] : r = r' := by
  rw [← inv_inj]; rw [inv_eq p q r]; rw [inv_eq p q r']

/--
lemma `one_div_add_one_div` / 引理 `one_div_add_one_div`

English:
lemma one_div_add_one_div
  statement: 1 / p + 1 / q = 1 / r
  proof: by simpa using inv_add_inv_eq_inv ..

中文:
引理 one_div_add_one_div
  结论: 1 / p + 1 / q = 1 / r
  证明: by simpa using inv_add_inv_eq_inv ..

Depends on / 依赖: _dropWhile_not, _eq_head, convert, inv_add_inv_eq_inv, l.find
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using inv_add_inv_eq_inv ..

/--
lemma `one_div_eq` / 引理 `one_div_eq`

English:
lemma one_div_eq
  statement: 1 / r = 1 / p + 1 / q
  proof: .symm one_div_add_one_div p q r

中文:
引理 one_div_eq
  结论: 1 / r = 1 / p + 1 / q
  证明: .symm one_div_add_one_div p q r

Depends on / 依赖: _dropWhile_not, _eq_head, _eq_some, head_eq_iff_head, l.find, one_div_add_one_div
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q :=
.symm one_div_add_one_div p q r

/--
lemma `inv_inv_add_inv` / 引理 `inv_inv_add_inv`

English:
lemma inv_inv_add_inv
  statement: (p⁻¹ + q⁻¹)⁻¹ = r
  proof: by
  simp [inv_add_inv_eq_inv p q r]

include q in

中文:
引理 inv_inv_add_inv
  结论: (p⁻¹ + q⁻¹)⁻¹ = r
  证明: by
  simp [inv_add_inv_eq_inv p q r]

include q in

Depends on / 依赖: _eq_head_dropWhile_not, convert, inv_add_inv_eq_inv, l.find
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by
  simp [inv_add_inv_eq_inv p q r]

include q in
/--
lemma `le` / 引理 `le`

English:
lemma le
  statement: r <= p
  proof: by
  simp [← ENNReal.inv_le_inv, ← @inv_inv_add_inv p q r, inv_inv]

include q in

中文:
引理 le
  结论: r <= p
  证明: by
  simp [← ENNReal.inv_le_inv, ← @inv_inv_add_inv p q r, inv_inv]

include q in

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, inv_inv, inv_inv_add_inv, inv_le_inv
-/
lemma le : r <= p := by
  simp [← ENNReal.inv_le_inv, ← @inv_inv_add_inv p q r, inv_inv]

include q in
/--
lemma `inv_le_inv` / 引理 `inv_le_inv`

English:
lemma inv_le_inv
  statement: p⁻¹ <= r⁻¹
  proof: by
  simp [ENNReal.inv_le_inv, le p q r]

中文:
引理 inv_le_inv
  结论: p⁻¹ <= r⁻¹
  证明: by
  simp [ENNReal.inv_le_inv, le p q r]
-/
protected lemma inv_le_inv : p⁻¹ <= r⁻¹ := by
  simp [ENNReal.inv_le_inv, le p q r]

variable {r} in
/--
lemma `inv_sub_inv_eq_inv` / 引理 `inv_sub_inv_eq_inv`

English:
lemma inv_sub_inv_eq_inv
  given: (hr : r != 0)
  statement: r⁻¹ - q⁻¹ = p⁻¹
  proof: by
  apply ENNReal.sub_eq_of_eq_add (ne_of_lt ?_) (inv_eq p q r)
  calc
    q⁻¹ <= r⁻¹ := HolderTriple.inv_le_inv q p r
    _ < ∞ := by simpa using pos_iff_ne_zero.mpr hr

中文:
引理 inv_sub_inv_eq_inv
  条件: (hr : r != 0)
  结论: r⁻¹ - q⁻¹ = p⁻¹
  证明: by
  apply ENNReal.sub_eq_of_eq_add (ne_of_lt ?_) (inv_eq p q r)
  calc
    q⁻¹ <= r⁻¹ := HolderTriple.inv_le_inv q p r
    _ < ∞ := by simpa using pos_iff_ne_zero.mpr hr

Depends on / 依赖: ENNReal, ENNReal.sub_eq_of_eq_add, HolderTriple, HolderTriple.inv_le_inv, inv_eq, inv_le_inv, ne_of_lt, pos_iff_ne_zero, pos_iff_ne_zero.mpr, sub_eq_of_eq_add
-/
lemma inv_sub_inv_eq_inv (hr : r != 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  apply ENNReal.sub_eq_of_eq_add (ne_of_lt ?_) (inv_eq p q r)
  calc
    q⁻¹ <= r⁻¹ := HolderTriple.inv_le_inv q p r
    _ < ∞ := by simpa using pos_iff_ne_zero.mpr hr

/--
lemma `inv_sub_inv_eq_inv'` / 引理 `inv_sub_inv_eq_inv'`

English:
lemma inv_sub_inv_eq_inv'
  given: (hq : q != 0)
  statement: r⁻¹ - q⁻¹ = p⁻¹
  proof: by
  obtain (rfl | hr) := eq_zero_or_pos r
  · suffices p = 0 by simpa [this]
    by_contra! hp
    have := calc
      0⁻¹ = p⁻¹ + q⁻¹ := inv_eq p q 0
      _ < ⊤ + ⊤ := by simp [hp, hq, pos_iff_ne_zero]
      _ = ⊤ := by simp
    simp_all
  · exact inv_sub_inv_eq_inv p q hr.ne'

中文:
引理 inv_sub_inv_eq_inv'
  条件: (hq : q != 0)
  结论: r⁻¹ - q⁻¹ = p⁻¹
  证明: by
  obtain (rfl | hr) := eq_zero_or_pos r
  · suffices p = 0 by simpa [this]
    by_contra! hp
    have := calc
      0⁻¹ = p⁻¹ + q⁻¹ := inv_eq p q 0
      _ < ⊤ + ⊤ := by simp [hp, hq, pos_iff_ne_zero]
      _ = ⊤ := by simp
    simp_all
  · exact inv_sub_inv_eq_inv p q hr.ne'

Depends on / 依赖: eq_zero_or_pos, hr.ne, inv_eq, inv_sub_inv_eq_inv, pos_iff_ne_zero
-/
lemma inv_sub_inv_eq_inv' (hq : q != 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · suffices p = 0 by simpa [this]
    by_contra! hp
    have := calc
      0⁻¹ = p⁻¹ + q⁻¹ := inv_eq p q 0
      _ < ⊤ + ⊤ := by simp [hp, hq, pos_iff_ne_zero]
      _ = ⊤ := by simp
    simp_all
  · exact inv_sub_inv_eq_inv p q hr.ne'

variable {r} in
/--
lemma `unique_of_ne_zero` / 引理 `unique_of_ne_zero`

English:
lemma unique_of_ne_zero
  given: (q' : Real>=0∞) (hr : r != 0) [HolderTriple p q' r]
  statement: q = q'
  proof: by
  rw [← inv_inj]; rw [← inv_sub_inv_eq_inv q p hr]; rw [← inv_sub_inv_eq_inv q' p hr]

中文:
引理 unique_of_ne_zero
  条件: (q' : 实数>=0∞) (hr : r != 0) [HolderTriple p q' r]
  结论: q = q'
  证明: by
  rw [← inv_inj]; rw [← inv_sub_inv_eq_inv q p hr]; rw [← inv_sub_inv_eq_inv q' p hr]

Depends on / 依赖: inv_inj, inv_sub_inv_eq_inv
-/
lemma unique_of_ne_zero (q' : Real>=0∞) (hr : r != 0) [HolderTriple p q' r] : q = q' := by
  rw [← inv_inj]; rw [← inv_sub_inv_eq_inv q p hr]; rw [← inv_sub_inv_eq_inv q' p hr]

/--
lemma `holderConjugate_div_div` / 引理 `holderConjugate_div_div`

English:
lemma holderConjugate_div_div
  given: (hr₀ : r != 0) (hr : r != ∞)
  statement: HolderConjugate (p / r) (q / r) where
  proof: by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_add_inv_eq_inv p q r]; rw [ENNReal.mul_inv_cancel hr₀ hr]; rw [inv_one]

中文:
引理 holderConjugate_div_div
  条件: (hr₀ : r != 0) (hr : r != ∞)
  结论: HolderConjugate (p / r) (q / r) where
  证明: by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_add_inv_eq_inv p q r]; rw [ENNReal.mul_inv_cancel hr₀ hr]; rw [inv_one]

Depends on / 依赖: ENNReal, ENNReal.inv_div, ENNReal.mul_inv_cancel, div_eq_mul_inv, inv_add_inv_eq_inv, inv_div, inv_one, mul_add, mul_inv_cancel
-/
lemma holderConjugate_div_div (hr₀ : r != 0) (hr : r != ∞) : HolderConjugate (p / r) (q / r) where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [ENNReal.inv_div (.inl hr) (.inl hr₀)]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_add_inv_eq_inv p q r]; rw [ENNReal.mul_inv_cancel hr₀ hr]; rw [inv_one]

end HolderTriple

/-! ### Hölder conjugates -/

namespace HolderConjugate

/--
Instance `symm` / 实例 `symm`

English:
instance symm
  signature: {p q : Real>=0∞} [hpq : HolderConjugate p q]
  body: inferInstance

中文:
实例 symm
  签名: {p q : 实数>=0∞} [hpq : HolderConjugate p q]
  定义体: inferInstance
-/
instance symm {p q : Real>=0∞} [hpq : HolderConjugate p q] : HolderConjugate q p :=
  inferInstance

/--
Instance `instTwoTwo` / 实例 `instTwoTwo`

English:
instance instTwoTwo
  signature: : HolderConjugate 2 2 where
  body: by
    rw [← two_mul]; rw [ENNReal.mul_inv_cancel]
    all_goals norm_num

中文:
实例 instTwoTwo
  签名: : HolderConjugate 2 2 where
  定义体: by
    rw [← two_mul]; rw [ENNReal.mul_inv_cancel]
    all_goals norm_num

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, all_goals, mul_inv_cancel, two_mul
-/
instance instTwoTwo : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by
    rw [← two_mul]; rw [ENNReal.mul_inv_cancel]
    all_goals norm_num

-- I'm not sure this is necessary, but maybe it's nice to have around given the `abbrev`.
/--
Instance `instOneInfty` / 实例 `instOneInfty`

English:
instance instOneInfty
  signature: : HolderConjugate 1 ∞
  body: inferInstance

中文:
实例 instOneInfty
  签名: : HolderConjugate 1 ∞
  定义体: inferInstance
-/
instance instOneInfty : HolderConjugate 1 ∞ := inferInstance

variable (p q : Real>=0∞) [HolderConjugate p q]

include q in
/--
lemma `one_le` / 引理 `one_le`

English:
lemma one_le
  statement: 1 <= p
  proof: HolderTriple.le p q 1

include q in

中文:
引理 one_le
  结论: 1 <= p
  证明: HolderTriple.le p q 1

include q in

Depends on / 依赖: HolderTriple, HolderTriple.le
-/
lemma one_le : 1 <= p := HolderTriple.le p q 1

include q in
/--
lemma `pos` / 引理 `pos`

English:
lemma pos
  statement: 0 < p
  proof: zero_lt_one.trans_le (one_le p q)

include q in
.ne' lemma ne_zero : p != 0 := pos p q

中文:
引理 pos
  结论: 0 < p
  证明: zero_lt_one.trans_le (one_le p q)

include q in
.ne' lemma ne_zero : p != 0 := pos p q

Depends on / 依赖: one_le, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma pos : 0 < p := zero_lt_one.trans_le (one_le p q)

include q in
.ne' lemma ne_zero : p != 0 := pos p q

/--
lemma `inv_add_inv_eq_one` / 引理 `inv_add_inv_eq_one`

English:
lemma inv_add_inv_eq_one
  statement: p⁻¹ + q⁻¹ = 1
  proof: @inv_one Real>=0∞ _ ▸ HolderTriple.inv_add_inv_eq_inv p q 1

中文:
引理 inv_add_inv_eq_one
  结论: p⁻¹ + q⁻¹ = 1
  证明: @inv_one Real>=0∞ _ ▸ HolderTriple.inv_add_inv_eq_inv p q 1

Depends on / 依赖: HolderTriple, HolderTriple.inv_add_inv_eq_inv, inv_add_inv_eq_inv, inv_one
-/
lemma inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := @inv_one Real>=0∞ _ ▸ HolderTriple.inv_add_inv_eq_inv p q 1

/--
lemma `one_sub_inv` / 引理 `one_sub_inv`

English:
lemma one_sub_inv
  statement: 1 - p⁻¹ = q⁻¹
  proof: @inv_one Real>=0∞ _ ▸ HolderTriple.inv_sub_inv_eq_inv q p one_ne_zero

中文:
引理 one_sub_inv
  结论: 1 - p⁻¹ = q⁻¹
  证明: @inv_one Real>=0∞ _ ▸ HolderTriple.inv_sub_inv_eq_inv q p one_ne_zero

Depends on / 依赖: HolderTriple, HolderTriple.inv_sub_inv_eq_inv, inv_one, inv_sub_inv_eq_inv, one_ne_zero
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ :=
  @inv_one Real>=0∞ _ ▸ HolderTriple.inv_sub_inv_eq_inv q p one_ne_zero

/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: (q' : Real>=0∞) [hq' : HolderConjugate p q']
  statement: q = q'
  proof: HolderTriple.unique_of_ne_zero p q q' one_ne_zero

中文:
引理 unique
  条件: (q' : 实数>=0∞) [hq' : HolderConjugate p q']
  结论: q = q'
  证明: HolderTriple.unique_of_ne_zero p q q' one_ne_zero

Depends on / 依赖: HolderTriple, HolderTriple.unique_of_ne_zero, one_ne_zero, unique_of_ne_zero
-/
lemma unique (q' : Real>=0∞) [hq' : HolderConjugate p q'] : q = q' :=
  HolderTriple.unique_of_ne_zero p q q' one_ne_zero

/--
lemma `eq_top_iff_eq_one` / 引理 `eq_top_iff_eq_one`

English:
lemma eq_top_iff_eq_one
  statement: p = ∞ ↔ q = 1
  proof: by
  constructor
  · rintro rfl
    rw [← inv_inv q]; rw [← one_sub_inv ∞ q]
    simp
  · rintro rfl
    rw [← inv_inv p]; rw [← one_sub_inv 1 p]
    simp

中文:
引理 eq_top_iff_eq_one
  结论: p = ∞ ↔ q = 1
  证明: by
  constructor
  · rintro rfl
    rw [← inv_inv q]; rw [← one_sub_inv ∞ q]
    simp
  · rintro rfl
    rw [← inv_inv p]; rw [← one_sub_inv 1 p]
    simp

Depends on / 依赖: inv_inv, one_sub_inv
-/
lemma eq_top_iff_eq_one : p = ∞ ↔ q = 1 := by
  constructor
  · rintro rfl
    rw [← inv_inv q]; rw [← one_sub_inv ∞ q]
    simp
  · rintro rfl
    rw [← inv_inv p]; rw [← one_sub_inv 1 p]
    simp

/--
lemma `ne_top_iff_ne_one` / 引理 `ne_top_iff_ne_one`

English:
lemma ne_top_iff_ne_one
  statement: p != ∞ ↔ q != 1
  proof: by
  rw [not_iff_not]; rw [eq_top_iff_eq_one p q]

中文:
引理 ne_top_iff_ne_one
  结论: p != ∞ ↔ q != 1
  证明: by
  rw [not_iff_not]; rw [eq_top_iff_eq_one p q]

Depends on / 依赖: eq_top_iff_eq_one, not_iff_not
-/
lemma ne_top_iff_ne_one : p != ∞ ↔ q != 1 := by
  rw [not_iff_not]; rw [eq_top_iff_eq_one p q]

/--
lemma `lt_top_iff_one_lt` / 引理 `lt_top_iff_one_lt`

English:
lemma lt_top_iff_one_lt
  statement: p < ∞ ↔ 1 < q
  proof: by
  rw [lt_top_iff_ne_top]; rw [ne_top_iff_ne_one _ q]; rw [ne_comm]; rw [lt_iff_le_and_ne]
  simp [one_le q p]

中文:
引理 lt_top_iff_one_lt
  结论: p < ∞ ↔ 1 < q
  证明: by
  rw [lt_top_iff_ne_top]; rw [ne_top_iff_ne_one _ q]; rw [ne_comm]; rw [lt_iff_le_and_ne]
  simp [one_le q p]

Depends on / 依赖: lt_iff_le_and_ne, lt_top_iff_ne_top, ne_comm, ne_top_iff_ne_one, one_le
-/
lemma lt_top_iff_one_lt : p < ∞ ↔ 1 < q := by
  rw [lt_top_iff_ne_top]; rw [ne_top_iff_ne_one _ q]; rw [ne_comm]; rw [lt_iff_le_and_ne]
  simp [one_le q p]

/--
lemma `sub_one_mul_inv` / 引理 `sub_one_mul_inv`

English:
lemma sub_one_mul_inv
  given: (hp : p != ⊤)
  statement: (p - 1) * p⁻¹ = q⁻¹
  proof: by
.ne' have := pos p q
  rw [ENNReal.sub_mul (by simp_all)]; rw [ENNReal.mul_inv_cancel this (by lia)]
  simp [one_sub_inv p q]

中文:
引理 sub_one_mul_inv
  条件: (hp : p != ⊤)
  结论: (p - 1) * p⁻¹ = q⁻¹
  证明: by
.ne' have := pos p q
  rw [ENNReal.sub_mul (by simp_all)]; rw [ENNReal.mul_inv_cancel this (by lia)]
  simp [one_sub_inv p q]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.sub_mul, mul_inv_cancel, one_sub_inv, sub_mul
-/
lemma sub_one_mul_inv (hp : p != ⊤) : (p - 1) * p⁻¹ = q⁻¹ := by
.ne' have := pos p q
  rw [ENNReal.sub_mul (by simp_all)]; rw [ENNReal.mul_inv_cancel this (by lia)]
  simp [one_sub_inv p q]

end HolderConjugate

end ENNReal
