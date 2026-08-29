/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith.Frontend

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * (x * x) + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.
- `discrim_le_zero_of_nonpos`, `discrim_lt_zero`, `discrim_lt_zero_of_neg`: versions of this
  statement with other inequalities.

## Tags

polynomial, quadratic, discriminant, root
-/

@[expose] public section

assert_not_exists Finite Finset

open Filter

section Ring

variable {R : Type*}

/--
Definition of `discrim` / `discrim` 的定义

English:
definition discrim
  signature: [Ring R] (a b c : R)
  body: b ^ 2 - 4 * a * c

中文:
定义 discrim
  签名: [环 R] (a b c : R)
  定义体: b ^ 2 - 4 * a * c
-/
def discrim [Ring R] (a b c : R) : R :=
  b ^ 2 - 4 * a * c

/--
lemma `discrim_neg` / 引理 `discrim_neg`

English:
lemma discrim_neg
  given: [Ring R] (a b c : R)
  statement: discrim (-a) (-b) (-c) = discrim a b c
  proof: by
  simp [discrim]

中文:
引理 discrim_neg
  条件: [环 R] (a b c : R)
  结论: discrim (-a) (-b) (-c) = discrim a b c
  证明: by
  simp [discrim]
-/
@[simp] lemma discrim_neg [Ring R] (a b c : R) : discrim (-a) (-b) (-c) = discrim a b c := by
  simp [discrim]

variable [CommRing R] {a b c : R}

/--
lemma `discrim_eq_sq_of_quadratic_eq_zero` / 引理 `discrim_eq_sq_of_quadratic_eq_zero`

English:
lemma discrim_eq_sq_of_quadratic_eq_zero
  given: {x : R} (h : a * (x * x) + b * x + c = 0)
  proof: by
  rw [discrim]
  linear_combination -4 * a * h

中文:
引理 discrim_eq_sq_of_quadratic_eq_zero
  条件: {x : R} (h : a * (x * x) + b * x + c = 0)
  证明: by
  rw [discrim]
  linear_combination -4 * a * h

Depends on / 依赖: discrim, linear_combination
-/
lemma discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * (x * x) + b * x + c = 0) :
    discrim a b c = (2 * a * x + b) ^ 2 := by
  rw [discrim]
  linear_combination -4 * a * h

/--
theorem `quadratic_eq_zero_iff_discrim_eq_sq` / 定理 `quadratic_eq_zero_iff_discrim_eq_sq`

English:
theorem quadratic_eq_zero_iff_discrim_eq_sq
  statement: [NeZero (2 : R)] [NoZeroDivisors R]
  proof: by
  refine ⟨discrim_eq_sq_of_quadratic_eq_zero, fun h => ?_⟩
  rw [discrim] at h
  have ha : 2 * 2 * a != 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _)) ha
  apply mul_left_cancel₀ ha
  linear_combination -h

中文:
定理 quadratic_eq_zero_iff_discrim_eq_sq
  结论: [NeZero (2 : R)] [无零因子 R]
  证明: by
  refine ⟨discrim_eq_sq_of_quadratic_eq_zero, fun h => ?_⟩
  rw [discrim] at h
  have ha : 2 * 2 * a != 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _)) ha
  apply mul_left_cancel₀ ha
  linear_combination -h

Depends on / 依赖: NeZero, NeZero.ne, discrim, discrim_eq_sq_of_quadratic_eq_zero, linear_combination, mul_ne_zero
-/
theorem quadratic_eq_zero_iff_discrim_eq_sq [NeZero (2 : R)] [NoZeroDivisors R]
    (ha : a != 0) (x : R) :
    a * (x * x) + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 := by
  refine ⟨discrim_eq_sq_of_quadratic_eq_zero, fun h => ?_⟩
  rw [discrim] at h
  have ha : 2 * 2 * a != 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _)) ha
  apply mul_left_cancel₀ ha
  linear_combination -h

/--
theorem `quadratic_ne_zero_of_discrim_ne_sq` / 定理 `quadratic_ne_zero_of_discrim_ne_sq`

English:
theorem quadratic_ne_zero_of_discrim_ne_sq
  given: (h : forall s : R, discrim a b c != s ^ 2) (x : R)
  proof: mt discrim_eq_sq_of_quadratic_eq_zero (h _)

中文:
定理 quadratic_ne_zero_of_discrim_ne_sq
  条件: (h : 对任意 s : R, discrim a b c != s ^ 2) (x : R)
  证明: mt discrim_eq_sq_of_quadratic_eq_zero (h _)

Depends on / 依赖: discrim_eq_sq_of_quadratic_eq_zero
-/
theorem quadratic_ne_zero_of_discrim_ne_sq (h : forall s : R, discrim a b c != s ^ 2) (x : R) :
    a * (x * x) + b * x + c != 0 :=
  mt discrim_eq_sq_of_quadratic_eq_zero (h _)

end Ring

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

/--
theorem `quadratic_eq_zero_iff` / 定理 `quadratic_eq_zero_iff`

English:
theorem quadratic_eq_zero_iff
  given: (ha : a != 0) {s : K} (h : discrim a b c = s * s) (x : K)
  proof: by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha]; rw [h]; rw [sq]; rw [mul_self_eq_mul_self_iff]
  field_simp
  grind

中文:
定理 quadratic_eq_zero_iff
  条件: (ha : a != 0) {s : K} (h : discrim a b c = s * s) (x : K)
  证明: by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha]; rw [h]; rw [sq]; rw [mul_self_eq_mul_self_iff]
  field_simp
  grind

Depends on / 依赖: mul_self_eq_mul_self_iff, quadratic_eq_zero_iff_discrim_eq_sq
-/
theorem quadratic_eq_zero_iff (ha : a != 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha]; rw [h]; rw [sq]; rw [mul_self_eq_mul_self_iff]
  field_simp
  grind

/--
theorem `exists_quadratic_eq_zero` / 定理 `exists_quadratic_eq_zero`

English:
theorem exists_quadratic_eq_zero
  given: (ha : a != 0) (h : exists s, discrim a b c = s * s)
  proof: by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp

中文:
定理 存在_quadratic_eq_zero
  条件: (ha : a != 0) (h : 存在 s, discrim a b c = s * s)
  证明: by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp

Depends on / 依赖: quadratic_eq_zero_iff
-/
theorem exists_quadratic_eq_zero (ha : a != 0) (h : exists s, discrim a b c = s * s) :
    exists x, a * (x * x) + b * x + c = 0 := by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp

/--
theorem `quadratic_eq_zero_iff_of_discrim_eq_zero` / 定理 `quadratic_eq_zero_iff_of_discrim_eq_zero`

English:
theorem quadratic_eq_zero_iff_of_discrim_eq_zero
  given: (ha : a != 0) (h : discrim a b c = 0) (x : K)
  proof: by
  have : discrim a b c = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_eq_zero_iff ha this]; rw [add_zero]; rw [sub_zero]; rw [or_self_iff]

中文:
定理 quadratic_eq_zero_iff_of_discrim_eq_zero
  条件: (ha : a != 0) (h : discrim a b c = 0) (x : K)
  证明: by
  have : discrim a b c = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_eq_zero_iff ha this]; rw [add_zero]; rw [sub_zero]; rw [or_self_iff]

Depends on / 依赖: add_zero, discrim, mul_zero, or_self_iff, quadratic_eq_zero_iff, sub_zero
-/
theorem quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a != 0) (h : discrim a b c = 0) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = -b / (2 * a) := by
  have : discrim a b c = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_eq_zero_iff ha this]; rw [add_zero]; rw [sub_zero]; rw [or_self_iff]

/--
theorem `discrim_eq_zero_of_existsUnique` / 定理 `discrim_eq_zero_of_existsUnique`

English:
theorem discrim_eq_zero_of_existsUnique
  given: (ha : a != 0) (h : exists! x, a * (x * x) + b * x + c = 0)
  proof: by
  simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
  generalize discrim a b c = d at h
  obtain ⟨x, rfl, hx⟩ := h
  specialize hx (-(x + b / a))
  grind

中文:
定理 discrim_eq_zero_of_存在Unique
  条件: (ha : a != 0) (h : 存在! x, a * (x * x) + b * x + c = 0)
  证明: by
  simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
  generalize discrim a b c = d at h
  obtain ⟨x, rfl, hx⟩ := h
  specialize hx (-(x + b / a))
  grind

Depends on / 依赖: discrim, generalize, quadratic_eq_zero_iff_discrim_eq_sq, simp_rw, specialize
-/
theorem discrim_eq_zero_of_existsUnique (ha : a != 0) (h : exists! x, a * (x * x) + b * x + c = 0) :
    discrim a b c = 0 := by
  simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
  generalize discrim a b c = d at h
  obtain ⟨x, rfl, hx⟩ := h
  specialize hx (-(x + b / a))
  grind

/--
theorem `discrim_eq_zero_iff` / 定理 `discrim_eq_zero_iff`

English:
theorem discrim_eq_zero_iff
  given: (ha : a != 0)
  proof: by
  refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique ha⟩
  simp_rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha hd, existsUnique_eq]

中文:
定理 discrim_eq_zero_iff
  条件: (ha : a != 0)
  证明: by
  refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique ha⟩
  simp_rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha hd, existsUnique_eq]

Depends on / 依赖: discrim_eq_zero_of_existsUnique, existsUnique_eq, quadratic_eq_zero_iff_of_discrim_eq_zero, simp_rw
-/
theorem discrim_eq_zero_iff (ha : a != 0) :
    discrim a b c = 0 ↔ (exists! x, a * (x * x) + b * x + c = 0) := by
  refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique ha⟩
  simp_rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha hd, existsUnique_eq]

end Field

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : K}

/--
theorem `discrim_le_zero` / 定理 `discrim_le_zero`

English:
theorem discrim_le_zero
  given: (h : forall x : K, 0 <= a * (x * x) + b * x + c)
  statement: discrim a b c <= 0
  proof: by
  rw [discrim]; rw [sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  -- if a < 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
tendsto_atBot_add_const_right _ c
        (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
          tendsto_id
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_gt <| by rwa [← mul_assoc, ← add_mul])
  -- if a = 0
  · rcases eq_or_ne b 0 with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel₀ _ hb] at this
      linarith
  -- if a > 0
  · have ha' : 0 <= 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a))))
    field

中文:
定理 discrim_le_zero
  条件: (h : 对任意 x : K, 0 <= a * (x * x) + b * x + c)
  结论: discrim a b c <= 0
  证明: by
  rw [discrim]; rw [sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  -- if a < 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
tendsto_atBot_add_const_right _ c
        (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
          tendsto_id
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_gt <| by rwa [← mul_assoc, ← add_mul])
  -- if a = 0
  · rcases eq_or_ne b 0 with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel₀ _ hb] at this
      linarith
  -- if a > 0
  · have ha' : 0 <= 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a))))
    field

Depends on / 依赖: discrim, lt_trichotomy
-/
theorem discrim_le_zero (h : forall x : K, 0 <= a * (x * x) + b * x + c) : discrim a b c <= 0 := by
  rw [discrim]; rw [sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  -- if a < 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
tendsto_atBot_add_const_right _ c
        (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
          tendsto_id
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_gt <| by rwa [← mul_assoc, ← add_mul])
  -- if a = 0
  · rcases eq_or_ne b 0 with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel₀ _ hb] at this
      linarith
  -- if a > 0
  · have ha' : 0 <= 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a))))
    field

/--
lemma `discrim_le_zero_of_nonpos` / 引理 `discrim_le_zero_of_nonpos`

English:
lemma discrim_le_zero_of_nonpos
  given: (h : forall x : K, a * (x * x) + b * x + c <= 0)
  statement: discrim a b c <= 0
  proof: discrim_neg a b c ▸ discrim_le_zero by simpa only [neg_mul, ← neg_add, neg_nonneg]

中文:
引理 discrim_le_zero_of_nonpos
  条件: (h : 对任意 x : K, a * (x * x) + b * x + c <= 0)
  结论: discrim a b c <= 0
  证明: discrim_neg a b c ▸ discrim_le_zero by simpa only [neg_mul, ← neg_add, neg_nonneg]

Depends on / 依赖: discrim_le_zero, discrim_neg, neg_add, neg_mul, neg_nonneg
-/
lemma discrim_le_zero_of_nonpos (h : forall x : K, a * (x * x) + b * x + c <= 0) : discrim a b c <= 0 :=
discrim_neg a b c ▸ discrim_le_zero by simpa only [neg_mul, ← neg_add, neg_nonneg]

/--
theorem `discrim_lt_zero` / 定理 `discrim_lt_zero`

English:
theorem discrim_lt_zero
  given: (ha : a != 0) (h : forall x : K, 0 < a * (x * x) + b * x + c)
  proof: by
  have : forall x : K, 0 <= a * (x * x) + b * x + c := fun x => le_of_lt (h x)
  refine lt_of_le_of_ne (discrim_le_zero this) fun h' => ?_
  have := h (-b / (2 * a))
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0 := by
    rw [mul_assoc]; rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))]
  linarith

中文:
定理 discrim_lt_zero
  条件: (ha : a != 0) (h : 对任意 x : K, 0 < a * (x * x) + b * x + c)
  证明: by
  have : forall x : K, 0 <= a * (x * x) + b * x + c := fun x => le_of_lt (h x)
  refine lt_of_le_of_ne (discrim_le_zero this) fun h' => ?_
  have := h (-b / (2 * a))
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0 := by
    rw [mul_assoc]; rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))]
  linarith

Depends on / 依赖: discrim_le_zero, le_of_lt, lt_of_le_of_ne, mul_assoc, quadratic_eq_zero_iff_of_discrim_eq_zero
-/
theorem discrim_lt_zero (ha : a != 0) (h : forall x : K, 0 < a * (x * x) + b * x + c) :
    discrim a b c < 0 := by
  have : forall x : K, 0 <= a * (x * x) + b * x + c := fun x => le_of_lt (h x)
  refine lt_of_le_of_ne (discrim_le_zero this) fun h' => ?_
  have := h (-b / (2 * a))
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0 := by
    rw [mul_assoc]; rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))]
  linarith

/--
lemma `discrim_lt_zero_of_neg` / 引理 `discrim_lt_zero_of_neg`

English:
lemma discrim_lt_zero_of_neg
  given: (ha : a != 0) (h : forall x : K, a * (x * x) + b * x + c < 0)
  proof: discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) by
    simpa only [neg_mul, ← neg_add, neg_pos]

中文:
引理 discrim_lt_zero_of_neg
  条件: (ha : a != 0) (h : 对任意 x : K, a * (x * x) + b * x + c < 0)
  证明: discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) by
    simpa only [neg_mul, ← neg_add, neg_pos]

Depends on / 依赖: discrim_lt_zero, discrim_neg, neg_add, neg_mul, neg_ne_zero, neg_pos
-/
lemma discrim_lt_zero_of_neg (ha : a != 0) (h : forall x : K, a * (x * x) + b * x + c < 0) :
    discrim a b c < 0 :=
discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) by
    simpa only [neg_mul, ← neg_add, neg_pos]

end LinearOrderedField
