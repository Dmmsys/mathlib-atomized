/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Ring.Defs

/-!
# Theorems about additively and multiplicatively invertible elements in rings

-/

@[expose] public section

open scoped Ring

variable {R : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

/--
Definition of `AddUnits.mulLeft` / `AddUnits.mulLeft` 的定义

English:
definition AddUnits.mulLeft
  signature: : AddUnits R where
  body: y * x.val
  neg := y * x.neg
  val_neg := by simp [← mul_add]
  neg_val := by simp [← mul_add]

中文:
定义 AddUnits.mulLeft
  签名: : AddUnits R where
  定义体: y * x.val
  neg := y * x.neg
  val_neg := by simp [← mul_add]
  neg_val := by simp [← mul_add]
-/
@[simps] def AddUnits.mulLeft : AddUnits R where
  val := y * x.val
  neg := y * x.neg
  val_neg := by simp [← mul_add]
  neg_val := by simp [← mul_add]

/--
Definition of `AddUnits.mulRight` / `AddUnits.mulRight` 的定义

English:
definition AddUnits.mulRight
  signature: : AddUnits R where
  body: x.val * y
  neg := x.neg * y
  val_neg := by simp [← add_mul]
  neg_val := by simp [← add_mul]

中文:
定义 AddUnits.mulRight
  签名: : AddUnits R where
  定义体: x.val * y
  neg := x.neg * y
  val_neg := by simp [← add_mul]
  neg_val := by simp [← add_mul]

Depends on / 依赖: IsIntegralHom, f.normalizationDesc, f.normalizationDesc_comp, infer_instance, normalizationDesc, normalizationDesc_comp, of_comp
-/
@[simps] def AddUnits.mulRight : AddUnits R where
  val := x.val * y
  neg := x.neg * y
  val_neg := by simp [← add_mul]
  neg_val := by simp [← add_mul]

variable {x y}

/--
theorem `AddUnits.neg_mulLeft` / 定理 `AddUnits.neg_mulLeft`

English:
theorem AddUnits.neg_mulLeft
  statement: -(x.mulLeft y) = (-x).mulLeft y
  proof: rfl

中文:
定理 AddUnits.neg_mulLeft
  结论: -(x.mulLeft y) = (-x).mulLeft y
  证明: rfl
-/
theorem AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLeft y := rfl
/--
theorem `AddUnits.neg_mulRight` / 定理 `AddUnits.neg_mulRight`

English:
theorem AddUnits.neg_mulRight
  statement: -(x.mulRight y) = (-x).mulRight y
  proof: rfl

中文:
定理 AddUnits.neg_mulRight
  结论: -(x.mulRight y) = (-x).mulRight y
  证明: rfl
-/
theorem AddUnits.neg_mulRight : -(x.mulRight y) = (-x).mulRight y := rfl

/--
theorem `AddUnits.neg_mul_eq_mul_neg` / 定理 `AddUnits.neg_mul_eq_mul_neg`

English:
theorem AddUnits.neg_mul_eq_mul_neg
  given: {x y : AddUnits R}
  statement: (↑(-x) * y : R) = x * ↑(-y)
  proof: by
  rw [← neg_eq_val_neg]; rw [← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]

中文:
定理 AddUnits.neg_mul_eq_mul_neg
  条件: {x y : AddUnits R}
  结论: (↑(-x) * y : R) = x * ↑(-y)
  证明: by
  rw [← neg_eq_val_neg]; rw [← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]

Depends on / 依赖: AddUnits, AddUnits.neg_eq_of_add_eq_zero_left, mul_add, neg_eq_of_add_eq_zero_left, neg_eq_val_neg, val_neg_mulRight
-/
theorem AddUnits.neg_mul_eq_mul_neg {x y : AddUnits R} : (↑(-x) * y : R) = x * ↑(-y) := by
  rw [← neg_eq_val_neg]; rw [← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]

/--
theorem `AddUnits.neg_mul_neg` / 定理 `AddUnits.neg_mul_neg`

English:
theorem AddUnits.neg_mul_neg
  given: {x y : AddUnits R}
  statement: ↑(-x) * ↑(-y) = (x * y : R)
  proof: by
  rw [← val_mulLeft]; rw [← val_mulLeft]; rw [← AddUnits.ext_iff]; rw [← neg_inj]; rw [← y.neg_mulLeft]; rw [neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]

中文:
定理 AddUnits.neg_mul_neg
  条件: {x y : AddUnits R}
  结论: ↑(-x) * ↑(-y) = (x * y : R)
  证明: by
  rw [← val_mulLeft]; rw [← val_mulLeft]; rw [← AddUnits.ext_iff]; rw [← neg_inj]; rw [← y.neg_mulLeft]; rw [neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]

Depends on / 依赖: AddUnits, AddUnits.ext, AddUnits.ext_iff, ext_iff, neg_inj, neg_mulLeft, neg_mul_eq_mul_neg, neg_neg, val_mulLeft, y.neg_mulLeft
-/
theorem AddUnits.neg_mul_neg {x y : AddUnits R} : ↑(-x) * ↑(-y) = (x * y : R) := by
  rw [← val_mulLeft]; rw [← val_mulLeft]; rw [← AddUnits.ext_iff]; rw [← neg_inj]; rw [← y.neg_mulLeft]; rw [neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]

/--
theorem `IsAddUnit.mul_left` / 定理 `IsAddUnit.mul_left`

English:
theorem IsAddUnit.mul_left
  given: {x : R} (h : IsAddUnit x) (y : R)
  statement: IsAddUnit (y * x)
  proof: (h.addUnit.mulLeft y).isAddUnit

中文:
定理 IsAddUnit.mul_left
  条件: {x : R} (h : IsAddUnit x) (y : R)
  结论: IsAddUnit (y * x)
  证明: (h.addUnit.mulLeft y).isAddUnit

Depends on / 依赖: addUnit, h.addUnit.mulLeft, isAddUnit, mulLeft
-/
theorem IsAddUnit.mul_left {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (y * x) :=
  (h.addUnit.mulLeft y).isAddUnit

/--
theorem `IsAddUnit.mul_right` / 定理 `IsAddUnit.mul_right`

English:
theorem IsAddUnit.mul_right
  given: {x : R} (h : IsAddUnit x) (y : R)
  statement: IsAddUnit (x * y)
  proof: (h.addUnit.mulRight y).isAddUnit

中文:
定理 IsAddUnit.mul_right
  条件: {x : R} (h : IsAddUnit x) (y : R)
  结论: IsAddUnit (x * y)
  证明: (h.addUnit.mulRight y).isAddUnit

Depends on / 依赖: addUnit, h.addUnit.mulRight, isAddUnit, mulRight
-/
theorem IsAddUnit.mul_right {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (x * y) :=
  (h.addUnit.mulRight y).isAddUnit

end NonUnitalNonAssocSemiring

/-- `-⅟a` is the inverse of `-a` -/
@[instance_reducible]
/--
Definition of `invertibleNeg` / `invertibleNeg` 的定义

English:
definition invertibleNeg
  signature: [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a]
  body: ⟨-⅟a, by simp, by simp⟩

@[simp]

中文:
定义 invertibleNeg
  签名: [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a]
  定义体: ⟨-⅟a, by simp, by simp⟩

@[simp]
-/
def invertibleNeg [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a] : Invertible (-a) :=
  ⟨-⅟a, by simp, by simp⟩

@[simp]
/--
theorem `invOf_neg` / 定理 `invOf_neg`

English:
theorem invOf_neg
  given: [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)]
  proof: invOf_eq_right_inv (by simp)

@[simp]

中文:
定理 invOf_neg
  条件: [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)]
  证明: invOf_eq_right_inv (by simp)

@[simp]

Depends on / 依赖: invOf_eq_right_inv
-/
theorem invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)] :
    ⅟(-a) = -⅟a :=
  invOf_eq_right_inv (by simp)

@[simp]
/--
theorem `one_sub_invOf_two` / 定理 `one_sub_invOf_two`

English:
theorem one_sub_invOf_two
  given: [Ring R] [Invertible (2 : R)]
  statement: 1 - (⅟2 : R) = ⅟2
  proof: (isUnit_of_invertible (2 : R)).mul_right_inj.1 by
    rw [mul_sub]; rw [mul_invOf_self]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [add_sub_cancel_right]

@[simp]

中文:
定理 one_sub_invOf_two
  条件: [Ring R] [Invertible (2 : R)]
  结论: 1 - (⅟2 : R) = ⅟2
  证明: (isUnit_of_invertible (2 : R)).mul_right_inj.1 by
    rw [mul_sub]; rw [mul_invOf_self]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [add_sub_cancel_right]

@[simp]

Depends on / 依赖: add_sub_cancel_right, isUnit_of_invertible, mul_invOf_self, mul_one, mul_right_inj, mul_sub, one_add_one_eq_two
-/
theorem one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 - (⅟2 : R) = ⅟2 :=
(isUnit_of_invertible (2 : R)).mul_right_inj.1 by
    rw [mul_sub]; rw [mul_invOf_self]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [add_sub_cancel_right]

@[simp]
/--
theorem `invOf_two_add_invOf_two` / 定理 `invOf_two_add_invOf_two`

English:
theorem invOf_two_add_invOf_two
  given: [NonAssocSemiring R] [Invertible (2 : R)]
  proof: by rw [← two_mul, mul_invOf_self]

中文:
定理 invOf_two_add_invOf_two
  条件: [NonAssocSemiring R] [Invertible (2 : R)]
  证明: by rw [← two_mul, mul_invOf_self]

Depends on / 依赖: mul_invOf_self, two_mul
-/
theorem invOf_two_add_invOf_two [NonAssocSemiring R] [Invertible (2 : R)] :
    (⅟2 : R) + (⅟2 : R) = 1 := by rw [← two_mul, mul_invOf_self]

/--
theorem `pos_of_invertible_cast` / 定理 `pos_of_invertible_cast`

English:
theorem pos_of_invertible_cast
  given: [NonAssocSemiring R] [Nontrivial R] (n : Nat) [Invertible (n : R)]
  proof: Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)

中文:
定理 pos_of_invertible_cast
  条件: [NonAssocSemiring R] [Nontrivial R] (n : 自然数) [Invertible (n : R)]
  证明: Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)

Depends on / 依赖: Invertible, Invertible.ne_zero, Nat.cast_zero, Nat.zero_lt_of_ne_zero, cast_zero, ne_zero, zero_lt_of_ne_zero
-/
theorem pos_of_invertible_cast [NonAssocSemiring R] [Nontrivial R] (n : Nat) [Invertible (n : R)] :
    0 < n :=
  Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)

/--
theorem `invOf_add_invOf` / 定理 `invOf_add_invOf`

English:
theorem invOf_add_invOf
  given: [Semiring R] (a b : R) [Invertible a] [Invertible b]
  proof: by
  rw [mul_add]; rw [invOf_mul_self]; rw [add_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [add_comm]

中文:
定理 invOf_add_invOf
  条件: [Semiring R] (a b : R) [Invertible a] [Invertible b]
  证明: by
  rw [mul_add]; rw [invOf_mul_self]; rw [add_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [add_comm]

Depends on / 依赖: add_comm, add_mul, invOf_mul_self, mul_add, mul_assoc, mul_invOf_self, mul_one, one_mul
-/
theorem invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a + ⅟b = ⅟a * (a + b) * ⅟b := by
  rw [mul_add]; rw [invOf_mul_self]; rw [add_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [add_comm]

/--
theorem `invOf_sub_invOf` / 定理 `invOf_sub_invOf`

English:
theorem invOf_sub_invOf
  given: [Ring R] (a b : R) [Invertible a] [Invertible b]
  proof: by
  rw [mul_sub]; rw [invOf_mul_self]; rw [sub_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]

中文:
定理 invOf_sub_invOf
  条件: [Ring R] (a b : R) [Invertible a] [Invertible b]
  证明: by
  rw [mul_sub]; rw [invOf_mul_self]; rw [sub_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]

Depends on / 依赖: invOf_mul_self, mul_assoc, mul_invOf_self, mul_one, mul_sub, one_mul, sub_mul
-/
theorem invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a - ⅟b = ⅟a * (b - a) * ⅟b := by
  rw [mul_sub]; rw [invOf_mul_self]; rw [sub_mul]; rw [one_mul]; rw [mul_assoc]; rw [mul_invOf_self]; rw [mul_one]

/--
lemma `neg_add_eq_mul_invOf_mul_same_iff` / 引理 `neg_add_eq_mul_invOf_mul_same_iff`

English:
lemma neg_add_eq_mul_invOf_mul_same_iff
  given: [Ring R] {a b : R} [Invertible a] [Invertible b]
  proof: calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h => by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h => by simpa using congr_ar

中文:
引理 neg_add_eq_mul_invOf_mul_same_iff
  条件: [Ring R] {a b : R} [Invertible a] [Invertible b]
  证明: calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h => by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h => by simpa using congr_ar

Depends on / 依赖: congr_arg, mul_add, mul_assoc, mul_invOf_self, one_mul
-/
lemma neg_add_eq_mul_invOf_mul_same_iff [Ring R] {a b : R} [Invertible a] [Invertible b] :
    -(b + a) = a * ⅟b * a ↔ -1 = ⅟a * b + ⅟b * a :=
  calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h => by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h => by simpa using congr_arg (⅟a * ·) h, fun h => by simp [← h]⟩

/--
lemma `neg_one_eq_invOf_mul_add_invOf_mul_iff` / 引理 `neg_one_eq_invOf_mul_add_invOf_mul_iff`

English:
lemma neg_one_eq_invOf_mul_add_invOf_mul_iff
  statement: [Ring R] {a b : R} [Invertible a]
  proof: by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add

中文:
引理 neg_one_eq_invOf_mul_add_invOf_mul_iff
  结论: [Ring R] {a b : R} [Invertible a]
  证明: by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add

Depends on / 依赖: add_assoc, add_comm, add_mul, add_right_inj, invOf_mul_self, mul_add, mul_left_inj_of_invertible, one_add_one_eq_two
-/
lemma neg_one_eq_invOf_mul_add_invOf_mul_iff [Ring R] {a b : R} [Invertible a]
    [Invertible b] [Invertible (a + b)] : ⅟(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a * b + ⅟b * a := by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add_comm _ 1]
    _ ↔ 1 = 1 + 1 + ⅟b * a + ⅟a * b := by rw [← add_assoc, add_comm _ 1, ← add_assoc]
    _ ↔ -2 + 1 = -2 + (2 + ⅟b * a + ⅟a * b) := by rw [one_add_one_eq_two, add_right_inj]
    _ ↔ -2 + 1 = ⅟b * a + ⅟a * b := by rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add]
    _ ↔ -1 + 0 = ⅟b * a + ⅟a * b := by rw [← one_add_one_eq_two, neg_add, add_assoc, neg_add_cancel]
    _ ↔ -1 = ⅟a * b + ⅟b * a := by rw [add_zero, add_comm]

/--
theorem `eq_of_invOf_add_eq_invOf_add_invOf` / 定理 `eq_of_invOf_add_eq_invOf_add_invOf`

English:
theorem eq_of_invOf_add_eq_invOf_add_invOf
  statement: [Ring R] {a b : R} [Invertible a] [Invertible b]
  proof: by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a]; rw [← h_b_

中文:
定理 eq_of_invOf_add_eq_invOf_add_invOf
  结论: [Ring R] {a b : R} [Invertible a] [Invertible b]
  证明: by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a]; rw [← h_b_

Depends on / 依赖: add_comm, h_a_binv_a, h_b_ainv_b, neg_add_eq_mul_invOf_mul_same_iff, neg_add_eq_mul_invOf_mul_same_iff.mpr, neg_one_eq_invOf_mul_add_invOf_mul_iff, neg_one_eq_invOf_mul_add_invOf_mul_iff.mp
-/
theorem eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a]; rw [← h_b_ainv_b]; rw [add_comm]

/--
theorem `Ring.inverse_add_inverse` / 定理 `Ring.inverse_add_inverse`

English:
theorem Ring.inverse_add_inverse
  given: [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b)
  proof: by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

中文:
定理 Ring.inverse_add_inverse
  条件: [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b)
  证明: by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

Depends on / 依赖: IsUnit, h.mp, h.not.mp, ha.nonempty_invertible, hb.nonempty_invertible, invOf_add_invOf, inverse_invertible, inverse_non_unit, nonempty_invertible, simp_rw
-/
theorem Ring.inverse_add_inverse [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ + b⁻¹ʳ = a⁻¹ʳ * (a + b) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

/--
theorem `Ring.inverse_sub_inverse` / 定理 `Ring.inverse_sub_inverse`

English:
theorem Ring.inverse_sub_inverse
  given: [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b)
  proof: by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

中文:
定理 Ring.inverse_sub_inverse
  条件: [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b)
  证明: by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

Depends on / 依赖: IsUnit, h.mp, h.not.mp, ha.nonempty_invertible, hb.nonempty_invertible, invOf_sub_invOf, inverse_invertible, inverse_non_unit, nonempty_invertible, simp_rw
-/
theorem Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]
