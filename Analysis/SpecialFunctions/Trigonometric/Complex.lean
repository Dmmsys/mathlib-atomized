/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`Analysis.SpecialFunctions.Trigonometric.Basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/

public section


noncomputable section

namespace Complex

open Set Filter Finset

open scoped Real

/--
theorem `cos_eq_zero_iff` / 定理 `cos_eq_zero_iff`

English:
theorem cos_eq_zero_iff
  given: {θ : Complex}
  statement: cos θ = 0 ↔ exists k : Int, θ = (2 * k + 1) * π / 2
  proof: by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero]; rw [zero_mul]; rw [add_eq_zero_iff_eq_neg]; rw [neg_eq_neg_one_mul]; rw [← div_eq_iff (exp_ne_zero _)]; rw [← exp_sub]
    ring_nf
  rw [cos]; rw [h]

中文:
定理 cos_eq_zero_iff
  条件: {θ : 复形}
  结论: cos θ = 0 ↔ 存在 k : 整数, θ = (2 * k + 1) * π / 2
  证明: by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero]; rw [zero_mul]; rw [add_eq_zero_iff_eq_neg]; rw [neg_eq_neg_one_mul]; rw [← div_eq_iff (exp_ne_zero _)]; rw [← exp_sub]
    ring_nf
  rw [cos]; rw [h]

Depends on / 依赖: I_ne_zero, add_eq_zero_iff_eq_neg, congr_arg, div_eq_iff, exists_congr, exp_eq_exp_iff_exists_int, exp_ne_zero, exp_pi_mul_I, exp_sub, iff_of_eq, mul_ne_zero, mul_right_comm, mul_right_inj, neg_eq_neg_one_mul, ring_nf, two_ne_zero, zero_mul
-/
theorem cos_eq_zero_iff {θ : Complex} : cos θ = 0 ↔ exists k : Int, θ = (2 * k + 1) * π / 2 := by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero]; rw [zero_mul]; rw [add_eq_zero_iff_eq_neg]; rw [neg_eq_neg_one_mul]; rw [← div_eq_iff (exp_ne_zero _)]; rw [← exp_sub]
    ring_nf
  rw [cos]; rw [h]; rw [← exp_pi_mul_I]; rw [exp_eq_exp_iff_exists_int]; rw [mul_right_comm]
  refine exists_congr fun x => ?_
  refine (iff_of_eq <| congr_arg _ ?_).trans (mul_right_inj' <| mul_ne_zero two_ne_zero I_ne_zero)
  ring

/--
theorem `cos_ne_zero_iff` / 定理 `cos_ne_zero_iff`

English:
theorem cos_ne_zero_iff
  given: {θ : Complex}
  statement: cos θ != 0 ↔ forall k : Int, θ != (2 * k + 1) * π / 2
  proof: by
  contrapose!; exact cos_eq_zero_iff

中文:
定理 cos_ne_zero_iff
  条件: {θ : 复形}
  结论: cos θ != 0 ↔ 对任意 k : 整数, θ != (2 * k + 1) * π / 2
  证明: by
  contrapose!; exact cos_eq_zero_iff

Depends on / 依赖: contrapose, cos_eq_zero_iff
-/
theorem cos_ne_zero_iff {θ : Complex} : cos θ != 0 ↔ forall k : Int, θ != (2 * k + 1) * π / 2 := by
  contrapose!; exact cos_eq_zero_iff

/--
theorem `sin_eq_zero_iff` / 定理 `sin_eq_zero_iff`

English:
theorem sin_eq_zero_iff
  given: {θ : Complex}
  statement: sin θ = 0 ↔ exists k : Int, θ = k * π
  proof: by
  rw [← Complex.cos_sub_pi_div_two]; rw [cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    simp
    ring

中文:
定理 sin_eq_zero_iff
  条件: {θ : 复形}
  结论: sin θ = 0 ↔ 存在 k : 整数, θ = k * π
  证明: by
  rw [← Complex.cos_sub_pi_div_two]; rw [cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    simp
    ring

Depends on / 依赖: Complex.cos_sub_pi_div_two, cos_eq_zero_iff, cos_sub_pi_div_two, eq_add_of_sub_eq
-/
theorem sin_eq_zero_iff {θ : Complex} : sin θ = 0 ↔ exists k : Int, θ = k * π := by
  rw [← Complex.cos_sub_pi_div_two]; rw [cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    simp
    ring

/--
theorem `sin_ne_zero_iff` / 定理 `sin_ne_zero_iff`

English:
theorem sin_ne_zero_iff
  given: {θ : Complex}
  statement: sin θ != 0 ↔ forall k : Int, θ != k * π
  proof: by
  contrapose!; exact sin_eq_zero_iff

中文:
定理 sin_ne_zero_iff
  条件: {θ : 复形}
  结论: sin θ != 0 ↔ 对任意 k : 整数, θ != k * π
  证明: by
  contrapose!; exact sin_eq_zero_iff

Depends on / 依赖: contrapose, sin_eq_zero_iff
-/
theorem sin_ne_zero_iff {θ : Complex} : sin θ != 0 ↔ forall k : Int, θ != k * π := by
  contrapose!; exact sin_eq_zero_iff

/--
theorem `tan_eq_zero_iff` / 定理 `tan_eq_zero_iff`

English:
theorem tan_eq_zero_iff
  given: {θ : Complex}
  statement: tan θ = 0 ↔ exists k : Int, k * π / 2 = θ
  proof: by
  rw [tan]; rw [div_eq_zero_iff]; rw [← mul_eq_zero]; rw [← mul_right_inj' two_ne_zero]; rw [mul_zero]; rw [← mul_assoc]; rw [← sin_two_mul]; rw [sin_eq_zero_iff]
  simp [field, mul_comm, eq_comm]

中文:
定理 tan_eq_zero_iff
  条件: {θ : 复形}
  结论: tan θ = 0 ↔ 存在 k : 整数, k * π / 2 = θ
  证明: by
  rw [tan]; rw [div_eq_zero_iff]; rw [← mul_eq_zero]; rw [← mul_right_inj' two_ne_zero]; rw [mul_zero]; rw [← mul_assoc]; rw [← sin_two_mul]; rw [sin_eq_zero_iff]
  simp [field, mul_comm, eq_comm]

Depends on / 依赖: div_eq_zero_iff, eq_comm, mul_assoc, mul_comm, mul_eq_zero, mul_right_inj, mul_zero, sin_eq_zero_iff, sin_two_mul, two_ne_zero
-/
theorem tan_eq_zero_iff {θ : Complex} : tan θ = 0 ↔ exists k : Int, k * π / 2 = θ := by
  rw [tan]; rw [div_eq_zero_iff]; rw [← mul_eq_zero]; rw [← mul_right_inj' two_ne_zero]; rw [mul_zero]; rw [← mul_assoc]; rw [← sin_two_mul]; rw [sin_eq_zero_iff]
  simp [field, mul_comm, eq_comm]

/--
theorem `tan_ne_zero_iff` / 定理 `tan_ne_zero_iff`

English:
theorem tan_ne_zero_iff
  given: {θ : Complex}
  statement: tan θ != 0 ↔ forall k : Int, (k * π / 2 : Complex) != θ
  proof: by
  contrapose!; exact tan_eq_zero_iff

中文:
定理 tan_ne_zero_iff
  条件: {θ : 复形}
  结论: tan θ != 0 ↔ 对任意 k : 整数, (k * π / 2 : 复形) != θ
  证明: by
  contrapose!; exact tan_eq_zero_iff

Depends on / 依赖: contrapose, tan_eq_zero_iff
-/
theorem tan_ne_zero_iff {θ : Complex} : tan θ != 0 ↔ forall k : Int, (k * π / 2 : Complex) != θ := by
  contrapose!; exact tan_eq_zero_iff

/--
theorem `tan_int_mul_pi_div_two` / 定理 `tan_int_mul_pi_div_two`

English:
theorem tan_int_mul_pi_div_two
  given: (n : Int)
  statement: tan (n * π / 2) = 0
  proof: tan_eq_zero_iff.mpr (by use n)

中文:
定理 tan_int_mul_pi_div_two
  条件: (n : 整数)
  结论: tan (n * π / 2) = 0
  证明: tan_eq_zero_iff.mpr (by use n)

Depends on / 依赖: tan_eq_zero_iff, tan_eq_zero_iff.mpr
-/
theorem tan_int_mul_pi_div_two (n : Int) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)

/--
theorem `tan_eq_zero_iff'` / 定理 `tan_eq_zero_iff'`

English:
theorem tan_eq_zero_iff'
  given: {θ : Complex} (hθ : cos θ != 0)
  statement: tan θ = 0 ↔ exists k : Int, k * π = θ
  proof: by
  simp only [tan, hθ, div_eq_zero_iff, sin_eq_zero_iff]; simp [eq_comm]

中文:
定理 tan_eq_zero_iff'
  条件: {θ : 复形} (hθ : cos θ != 0)
  结论: tan θ = 0 ↔ 存在 k : 整数, k * π = θ
  证明: by
  simp only [tan, hθ, div_eq_zero_iff, sin_eq_zero_iff]; simp [eq_comm]

Depends on / 依赖: div_eq_zero_iff, eq_comm, sin_eq_zero_iff
-/
theorem tan_eq_zero_iff' {θ : Complex} (hθ : cos θ != 0) : tan θ = 0 ↔ exists k : Int, k * π = θ := by
  simp only [tan, hθ, div_eq_zero_iff, sin_eq_zero_iff]; simp [eq_comm]

set_option linter.flexible false in -- Non-terminal simp, used to be field_simp
/--
theorem `cos_eq_cos_iff` / 定理 `cos_eq_cos_iff`

English:
theorem cos_eq_cos_iff
  given: {x y : Complex}
  statement: cos x = cos y ↔ exists k : Int, y = 2 * k * π + x ∨ y = 2 * k * π - x
  proof: calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by simp : (2 : Complex) != 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_c

中文:
定理 cos_eq_cos_iff
  条件: {x y : 复形}
  结论: cos x = cos y ↔ 存在 k : 整数, y = 2 * k * π + x ∨ y = 2 * k * π - x
  证明: calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by simp : (2 : Complex) != 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_c

Depends on / 依赖: cos_sub_cos, eq_sub_iff_add_eq, mul_comm, mul_right_comm, or_comm, or_congr, sin_eq_zero_iff, sub_eq_iff_eq_add, sub_eq_zero, sub_eq_zero.symm
-/
theorem cos_eq_cos_iff {x y : Complex} : cos x = cos y ↔ exists k : Int, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by simp : (2 : Complex) != 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_comm
    _ ↔ (exists k : Int, y = 2 * k * π + x) ∨ exists k : Int, y = 2 * k * π - x := by
      apply or_congr <;>
        simp [field, sin_eq_zero_iff, eq_sub_iff_add_eq',
          sub_eq_iff_eq_add, mul_comm (2 : Complex), mul_right_comm _ (2 : Complex)]
      constructor <;> · rintro ⟨k, rfl⟩; use -k; simp
    _ ↔ exists k : Int, y = 2 * k * π + x ∨ y = 2 * k * π - x := exists_or.symm

/--
theorem `sin_eq_sin_iff` / 定理 `sin_eq_sin_iff`

English:
theorem sin_eq_sin_iff
  given: {x y : Complex}
  proof: by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine exists_congr fun k => or_congr ?_ ?_ <;> refine Eq.congr rfl ?_ <;> simp [field] <;> ring

中文:
定理 sin_eq_sin_iff
  条件: {x y : 复形}
  证明: by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine exists_congr fun k => or_congr ?_ ?_ <;> refine Eq.congr rfl ?_ <;> simp [field] <;> ring

Depends on / 依赖: Complex.cos_sub_pi_div_two, Eq.congr, cos_eq_cos_iff, cos_sub_pi_div_two, exists_congr, or_congr, sub_eq_iff_eq_add
-/
theorem sin_eq_sin_iff {x y : Complex} :
    sin x = sin y ↔ exists k : Int, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x := by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine exists_congr fun k => or_congr ?_ ?_ <;> refine Eq.congr rfl ?_ <;> simp [field] <;> ring

/--
theorem `cos_eq_one_iff` / 定理 `cos_eq_one_iff`

English:
theorem cos_eq_one_iff
  given: {x : Complex}
  statement: cos x = 1 ↔ exists k : Int, k * (2 * π) = x
  proof: by
  rw [← cos_zero]; rw [eq_comm]; rw [cos_eq_cos_iff]
  simp [mul_assoc, mul_left_comm, eq_comm]

中文:
定理 cos_eq_one_iff
  条件: {x : 复形}
  结论: cos x = 1 ↔ 存在 k : 整数, k * (2 * π) = x
  证明: by
  rw [← cos_zero]; rw [eq_comm]; rw [cos_eq_cos_iff]
  simp [mul_assoc, mul_left_comm, eq_comm]

Depends on / 依赖: cos_eq_cos_iff, cos_zero, eq_comm, mul_assoc, mul_left_comm
-/
theorem cos_eq_one_iff {x : Complex} : cos x = 1 ↔ exists k : Int, k * (2 * π) = x := by
  rw [← cos_zero]; rw [eq_comm]; rw [cos_eq_cos_iff]
  simp [mul_assoc, mul_left_comm, eq_comm]

/--
theorem `cos_eq_neg_one_iff` / 定理 `cos_eq_neg_one_iff`

English:
theorem cos_eq_neg_one_iff
  given: {x : Complex}
  statement: cos x = -1 ↔ exists k : Int, π + k * (2 * π) = x
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_sub_pi]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

中文:
定理 cos_eq_neg_one_iff
  条件: {x : 复形}
  结论: cos x = -1 ↔ 存在 k : 整数, π + k * (2 * π) = x
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_sub_pi]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

Depends on / 依赖: cos_eq_one_iff, cos_sub_pi, eq_sub_iff_add_eq, neg_eq_iff_eq_neg
-/
theorem cos_eq_neg_one_iff {x : Complex} : cos x = -1 ↔ exists k : Int, π + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_sub_pi]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

/--
theorem `sin_eq_one_iff` / 定理 `sin_eq_one_iff`

English:
theorem sin_eq_one_iff
  given: {x : Complex}
  statement: sin x = 1 ↔ exists k : Int, π / 2 + k * (2 * π) = x
  proof: by
  rw [← cos_sub_pi_div_two]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

中文:
定理 sin_eq_one_iff
  条件: {x : 复形}
  结论: sin x = 1 ↔ 存在 k : 整数, π / 2 + k * (2 * π) = x
  证明: by
  rw [← cos_sub_pi_div_two]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

Depends on / 依赖: cos_eq_one_iff, cos_sub_pi_div_two, eq_sub_iff_add_eq
-/
theorem sin_eq_one_iff {x : Complex} : sin x = 1 ↔ exists k : Int, π / 2 + k * (2 * π) = x := by
  rw [← cos_sub_pi_div_two]; rw [cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

/--
theorem `sin_eq_neg_one_iff` / 定理 `sin_eq_neg_one_iff`

English:
theorem sin_eq_neg_one_iff
  given: {x : Complex}
  statement: sin x = -1 ↔ exists k : Int, -(π / 2) + k * (2 * π) = x
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_add_pi_div_two]; rw [cos_eq_one_iff]
  simp only [← sub_eq_neg_add, sub_eq_iff_eq_add]

中文:
定理 sin_eq_neg_one_iff
  条件: {x : 复形}
  结论: sin x = -1 ↔ 存在 k : 整数, -(π / 2) + k * (2 * π) = x
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_add_pi_div_two]; rw [cos_eq_one_iff]
  simp only [← sub_eq_neg_add, sub_eq_iff_eq_add]

Depends on / 依赖: cos_add_pi_div_two, cos_eq_one_iff, neg_eq_iff_eq_neg, sub_eq_iff_eq_add, sub_eq_neg_add
-/
theorem sin_eq_neg_one_iff {x : Complex} : sin x = -1 ↔ exists k : Int, -(π / 2) + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg]; rw [← cos_add_pi_div_two]; rw [cos_eq_one_iff]
  simp only [← sub_eq_neg_add, sub_eq_iff_eq_add]

/--
theorem `tan_add` / 定理 `tan_add`

English:
theorem tan_add
  statement: {x y : Complex}
  proof: by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right₀ (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),


中文:
定理 tan_add
  结论: {x y : 复形}
  证明: by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right₀ (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),


Depends on / 依赖: Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_two, add_div, cast_add, cast_mul, cast_one, cast_two, cos_add, cos_ne_zero_iff, cos_ne_zero_iff.mpr, div_mul_div_comm, div_self, mul_ne_zero, mul_one, one_mul, sin_add, sub_div, tan_int_mul_pi_div_two
-/
theorem tan_add {x y : Complex}
    (h : ((forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) ∨
      (exists k : Int, x = (2 * k + 1) * π / 2) ∧ exists l : Int, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right₀ (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),
      div_self (cos_ne_zero_iff.mpr h2)]
  · have t := tan_int_mul_pi_div_two
    obtain ⟨hx, hy, hxy⟩ := t (2 * k + 1), t (2 * l + 1), t (2 * k + 1 + (2 * l + 1))
    simp only [Int.cast_add, Int.cast_two, Int.cast_mul, Int.cast_one] at hx hy hxy
    rw [hx]; rw [hy]; rw [add_zero]; rw [zero_div]; rw [mul_div_assoc]; rw [mul_div_assoc]; rw [←
      add_mul (2 * (k : Complex) + 1) (2 * l + 1) (π / 2)]; rw [← mul_div_assoc]; rw [hxy]

/--
theorem `tan_add'` / 定理 `tan_add'`

English:
theorem tan_add'
  statement: {x y : Complex}
  proof: tan_add (Or.inl h)

中文:
定理 tan_add'
  结论: {x y : 复形}
  证明: tan_add (Or.inl h)

Depends on / 依赖: Or.inl, tan_add
-/
theorem tan_add' {x y : Complex}
    (h : (forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

/--
theorem `tan_sub` / 定理 `tan_sub`

English:
theorem tan_sub
  statement: {x y : Complex}
  proof: by
have := tan_add (x := x) (y := -y) by
    rcases h with ⟨x_ne, minus_y_ne⟩ | ⟨x_eq, minus_y_eq⟩
    · refine .inl ⟨x_ne, fun l => ?_⟩
      rw [Ne]; rw [neg_eq_iff_eq_neg]
      convert! minus_y_ne (-l - 1) using 2
      push_cast
      ring
    · refine .inr ⟨x_eq, ?_⟩
      rcases minus_y_eq wi

中文:
定理 tan_sub
  结论: {x y : 复形}
  证明: by
have := tan_add (x := x) (y := -y) by
    rcases h with ⟨x_ne, minus_y_ne⟩ | ⟨x_eq, minus_y_eq⟩
    · refine .inl ⟨x_ne, fun l => ?_⟩
      rw [Ne]; rw [neg_eq_iff_eq_neg]
      convert! minus_y_ne (-l - 1) using 2
      push_cast
      ring
    · refine .inr ⟨x_eq, ?_⟩
      rcases minus_y_eq wi

Depends on / 依赖: convert, minus_y_eq, minus_y_ne, neg_eq_iff_eq_neg, tan_add, tan_neg, x_eq, x_ne
-/
theorem tan_sub {x y : Complex}
    (h : ((forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) ∨
      (exists k : Int, x = (2 * k + 1) * π / 2) ∧ exists l : Int, y = (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
have := tan_add (x := x) (y := -y) by
    rcases h with ⟨x_ne, minus_y_ne⟩ | ⟨x_eq, minus_y_eq⟩
    · refine .inl ⟨x_ne, fun l => ?_⟩
      rw [Ne]; rw [neg_eq_iff_eq_neg]
      convert! minus_y_ne (-l - 1) using 2
      push_cast
      ring
    · refine .inr ⟨x_eq, ?_⟩
      rcases minus_y_eq with ⟨l, rfl⟩
      use -l - 1
      push_cast
      ring
  rw [tan_neg] at this
  convert! this using 2
  ring

/--
theorem `tan_sub'` / 定理 `tan_sub'`

English:
theorem tan_sub'
  statement: {x y : Complex}
  proof: tan_sub (Or.inl h)

中文:
定理 tan_sub'
  结论: {x y : 复形}
  证明: tan_sub (Or.inl h)

Depends on / 依赖: Or.inl, tan_sub
-/
theorem tan_sub' {x y : Complex}
    (h : (forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) :=
  tan_sub (Or.inl h)

/--
theorem `tan_two_mul` / 定理 `tan_two_mul`

English:
theorem tan_two_mul
  given: {z : Complex}
  statement: tan (2 * z) = (2 : Complex) * tan z / ((1 : Complex) - tan z ^ 2)
  proof: by
  by_cases! h : forall k : Int, z != (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

中文:
定理 tan_two_mul
  条件: {z : 复形}
  结论: tan (2 * z) = (2 : 复形) * tan z / ((1 : 复形) - tan z ^ 2)
  证明: by
  by_cases! h : forall k : Int, z != (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

Depends on / 依赖: Or.inl, Or.inr, tan_add, two_mul
-/
theorem tan_two_mul {z : Complex} : tan (2 * z) = (2 : Complex) * tan z / ((1 : Complex) - tan z ^ 2) := by
  by_cases! h : forall k : Int, z != (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

/--
theorem `tan_add_mul_I` / 定理 `tan_add_mul_I`

English:
theorem tan_add_mul_I
  statement: {x y : Complex}
  proof: by
  rw [tan_add h]; rw [tan_mul_I]; rw [mul_assoc]

中文:
定理 tan_add_mul_I
  结论: {x y : 复形}
  证明: by
  rw [tan_add h]; rw [tan_mul_I]; rw [mul_assoc]

Depends on / 依赖: mul_assoc, tan_add, tan_mul_I
-/
theorem tan_add_mul_I {x y : Complex}
    (h :
      ((forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y * I != (2 * l + 1) * π / 2) ∨
        (exists k : Int, x = (2 * k + 1) * π / 2) ∧ exists l : Int, y * I = (2 * l + 1) * π / 2) :
    tan (x + y * I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) := by
  rw [tan_add h]; rw [tan_mul_I]; rw [mul_assoc]

/--
theorem `tan_eq` / 定理 `tan_eq`

English:
theorem tan_eq
  statement: {z : Complex}
  proof: by
  convert! tan_add_mul_I h; exact (re_add_im z).symm

中文:
定理 tan_eq
  结论: {z : 复形}
  证明: by
  convert! tan_add_mul_I h; exact (re_add_im z).symm

Depends on / 依赖: convert, re_add_im, tan_add_mul_I
-/
theorem tan_eq {z : Complex}
    (h :
      ((forall k : Int, (z.re : Complex) != (2 * k + 1) * π / 2) ∧
          forall l : Int, (z.im : Complex) * I != (2 * l + 1) * π / 2) ∨
        (exists k : Int, (z.re : Complex) = (2 * k + 1) * π / 2) ∧
          exists l : Int, (z.im : Complex) * I = (2 * l + 1) * π / 2) :
    tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) := by
  convert! tan_add_mul_I h; exact (re_add_im z).symm

/--
lemma `tan_eq_zero_of_cos_eq_zero` / 引理 `tan_eq_zero_of_cos_eq_zero`

English:
lemma tan_eq_zero_of_cos_eq_zero
  given: {x} (h : cos x = 0)
  statement: tan x = 0
  proof: by
  obtain ⟨k, hxk⟩ := cos_eq_zero_iff.mp h
  exact tan_eq_zero_iff.mpr ⟨2 * k + 1, by simp [hxk]⟩

中文:
引理 tan_eq_zero_of_cos_eq_zero
  条件: {x} (h : cos x = 0)
  结论: tan x = 0
  证明: by
  obtain ⟨k, hxk⟩ := cos_eq_zero_iff.mp h
  exact tan_eq_zero_iff.mpr ⟨2 * k + 1, by simp [hxk]⟩

Depends on / 依赖: cos_eq_zero_iff, cos_eq_zero_iff.mp, tan_eq_zero_iff, tan_eq_zero_iff.mpr
-/
lemma tan_eq_zero_of_cos_eq_zero {x} (h : cos x = 0) : tan x = 0 := by
  obtain ⟨k, hxk⟩ := cos_eq_zero_iff.mp h
  exact tan_eq_zero_iff.mpr ⟨2 * k + 1, by simp [hxk]⟩

-- tangent half-angle substitution formulas

/--
theorem `cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq` / 定理 `cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq`

English:
theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
  given: (x : Complex) (h : cos x != -1)
  proof: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, cos_two_mul']
  have : cos (x / 2) != 0 := by grind [cos_ne_zero_iff, cos_eq_neg_one_iff]
  rw [div_eq_mul_inv (1 - tan (x / 2) ^ 2) (1 + tan (x / 2) ^ 2)]; rw [inv_one_add_tan_sq this]; rw [← tan_mul_cos this]
  ring

中文:
定理 cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
  条件: (x : 复形) (h : cos x != -1)
  证明: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, cos_two_mul']
  have : cos (x / 2) != 0 := by grind [cos_ne_zero_iff, cos_eq_neg_one_iff]
  rw [div_eq_mul_inv (1 - tan (x / 2) ^ 2) (1 + tan (x / 2) ^ 2)]; rw [inv_one_add_tan_sq this]; rw [← tan_mul_cos this]
  ring

Depends on / 依赖: conv_lhs, cos_eq_neg_one_iff, cos_ne_zero_iff, cos_two_mul, div_eq_mul_inv, inv_one_add_tan_sq, tan_mul_cos, two_ne_zero
-/
theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (x : Complex) (h : cos x != -1) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, cos_two_mul']
  have : cos (x / 2) != 0 := by grind [cos_ne_zero_iff, cos_eq_neg_one_iff]
  rw [div_eq_mul_inv (1 - tan (x / 2) ^ 2) (1 + tan (x / 2) ^ 2)]; rw [inv_one_add_tan_sq this]; rw [← tan_mul_cos this]
  ring

/--
theorem `sin_eq_two_mul_tan_half_div_one_add_tan_half_sq` / 定理 `sin_eq_two_mul_tan_half_div_one_add_tan_half_sq`

English:
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq
  given: (x : Complex)
  proof: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h, tan_eq_zero_of_cos_eq_zero]
  · rw [div_eq_mul_inv (2 * tan (x / 2)) (1 + tan (x / 2) ^ 2), inv_one_add_tan_sq h,
      ← tan_mul_cos h]
    ring

中文:
定理 sin_eq_two_mul_tan_half_div_one_add_tan_half_sq
  条件: (x : 复形)
  证明: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h, tan_eq_zero_of_cos_eq_zero]
  · rw [div_eq_mul_inv (2 * tan (x / 2)) (1 + tan (x / 2) ^ 2), inv_one_add_tan_sq h,
      ← tan_mul_cos h]
    ring

Depends on / 依赖: conv_lhs, div_eq_mul_inv, inv_one_add_tan_sq, sin_two_mul, tan_eq_zero_of_cos_eq_zero, tan_mul_cos, two_ne_zero
-/
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq (x : Complex) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h, tan_eq_zero_of_cos_eq_zero]
  · rw [div_eq_mul_inv (2 * tan (x / 2)) (1 + tan (x / 2) ^ 2), inv_one_add_tan_sq h,
      ← tan_mul_cos h]
    ring

/--
theorem `tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq` / 定理 `tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq`

English:
theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq
  given: (x : Complex)
  proof: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, tan_two_mul]

中文:
定理 tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq
  条件: (x : 复形)
  证明: by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, tan_two_mul]

Depends on / 依赖: conv_lhs, tan_two_mul, two_ne_zero
-/
theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq (x : Complex) :
    tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, tan_two_mul]

open scoped Topology

/--
theorem `continuousOn_tan` / 定理 `continuousOn_tan`

English:
theorem continuousOn_tan
  statement: ContinuousOn tan {x | cos x != 0}
  proof: continuousOn_sin.div continuousOn_cos fun _x => id

@[continuity]

中文:
定理 continuousOn_tan
  结论: ContinuousOn tan {x | cos x != 0}
  证明: continuousOn_sin.div continuousOn_cos fun _x => id

@[continuity]

Depends on / 依赖: continuousOn_cos, continuousOn_sin, continuousOn_sin.div
-/
theorem continuousOn_tan : ContinuousOn tan {x | cos x != 0} :=
  continuousOn_sin.div continuousOn_cos fun _x => id

@[continuity]
/--
theorem `continuous_tan` / 定理 `continuous_tan`

English:
theorem continuous_tan
  statement: Continuous fun x : {x | cos x != 0} => tan x
  proof: continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

中文:
定理 continuous_tan
  结论: 连续 fun x : {x | cos x != 0} => tan x
  证明: continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuousOn_tan
-/
theorem continuous_tan : Continuous fun x : {x | cos x != 0} => tan x :=
  continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

/--
theorem `cos_eq_iff_quadratic` / 定理 `cos_eq_iff_quadratic`

English:
theorem cos_eq_iff_quadratic
  given: {z w : Complex}
  proof: by
  rw [← sub_eq_zero]
  simpa [field, cos, exp_neg] using Eq.congr (by ring) rfl

中文:
定理 cos_eq_iff_quadratic
  条件: {z w : 复形}
  证明: by
  rw [← sub_eq_zero]
  simpa [field, cos, exp_neg] using Eq.congr (by ring) rfl

Depends on / 依赖: Eq.congr, exp_neg, sub_eq_zero
-/
theorem cos_eq_iff_quadratic {z w : Complex} :
    cos z = w ↔ exp (z * I) ^ 2 - 2 * w * exp (z * I) + 1 = 0 := by
  rw [← sub_eq_zero]
  simpa [field, cos, exp_neg] using Eq.congr (by ring) rfl

/--
theorem `cos_surjective` / 定理 `cos_surjective`

English:
theorem cos_surjective
  statement: Function.Surjective cos
  proof: by
  intro x
  obtain ⟨w, w₀, hw⟩ : exists w != 0, 1 * (w * w) + -2 * x * w + 1 = 0 := by
    rcases exists_quadratic_eq_zero one_ne_zero
⟨_, (cpow_nat_inv_pow _ two_ne_zero).symm.trans pow_two _⟩ with
      ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rintro rfl
    simp only [zero_add, one_ne_zero, mul_zero

中文:
定理 cos_surjective
  结论: 函数.满射 cos
  证明: by
  intro x
  obtain ⟨w, w₀, hw⟩ : exists w != 0, 1 * (w * w) + -2 * x * w + 1 = 0 := by
    rcases exists_quadratic_eq_zero one_ne_zero
⟨_, (cpow_nat_inv_pow _ two_ne_zero).symm.trans pow_two _⟩ with
      ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rintro rfl
    simp only [zero_add, one_ne_zero, mul_zero

Depends on / 依赖: I_ne_zero, convert, cos_eq_iff_quadratic, cpow_nat_inv_pow, exists_quadratic_eq_zero, exp_log, mul_zero, one_ne_zero, pow_two, symm.trans, two_ne_zero, zero_add
-/
theorem cos_surjective : Function.Surjective cos := by
  intro x
  obtain ⟨w, w₀, hw⟩ : exists w != 0, 1 * (w * w) + -2 * x * w + 1 = 0 := by
    rcases exists_quadratic_eq_zero one_ne_zero
⟨_, (cpow_nat_inv_pow _ two_ne_zero).symm.trans pow_two _⟩ with
      ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rintro rfl
    simp only [zero_add, one_ne_zero, mul_zero] at hw
  refine ⟨log w / I, cos_eq_iff_quadratic.2 ?_⟩
  rw [div_mul_cancel₀ _ I_ne_zero]; rw [exp_log w₀]
  convert! hw using 1
  ring

@[simp]
/--
theorem `range_cos` / 定理 `range_cos`

English:
theorem range_cos
  statement: Set.range cos = Set.univ
  proof: cos_surjective.range_eq

中文:
定理 range_cos
  结论: 集合.range cos = 集合.univ
  证明: cos_surjective.range_eq

Depends on / 依赖: cos_surjective, cos_surjective.range_eq, range_eq
-/
theorem range_cos : Set.range cos = Set.univ :=
  cos_surjective.range_eq

/--
theorem `sin_surjective` / 定理 `sin_surjective`

English:
theorem sin_surjective
  statement: Function.Surjective sin
  proof: by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩

@[simp]

中文:
定理 sin_surjective
  结论: 函数.满射 sin
  证明: by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩

@[simp]

Depends on / 依赖: cos_surjective, sin_add_pi_div_two
-/
theorem sin_surjective : Function.Surjective sin := by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩

@[simp]
/--
theorem `range_sin` / 定理 `range_sin`

English:
theorem range_sin
  statement: Set.range sin = Set.univ
  proof: sin_surjective.range_eq

中文:
定理 range_sin
  结论: 集合.range sin = 集合.univ
  证明: sin_surjective.range_eq

Depends on / 依赖: range_eq, sin_surjective, sin_surjective.range_eq
-/
theorem range_sin : Set.range sin = Set.univ :=
  sin_surjective.range_eq

/--
theorem `sin_mul_sum_sin` / 定理 `sin_mul_sum_sin`

English:
theorem sin_mul_sum_sin
  given: (n : Nat) (a b : Complex)
  proof: by
  apply mul_left_cancel₀ (show (-2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, -2 * sin (a / 2) * sin (a * i + b)
      = ∑ x in range n, (cos (a * (↑(x + 1) - 1 / 2) + b) - cos (-(a * (x - 1 / 2) + b))) := by
      congr! 1 with x hx
      rw [cos_sub_cos

中文:
定理 sin_mul_sum_sin
  条件: (n : 自然数) (a b : 复形)
  证明: by
  apply mul_left_cancel₀ (show (-2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, -2 * sin (a / 2) * sin (a * i + b)
      = ∑ x in range n, (cos (a * (↑(x + 1) - 1 / 2) + b) - cos (-(a * (x - 1 / 2) + b))) := by
      congr! 1 with x hx
      rw [cos_sub_cos

Depends on / 依赖: cos_neg, cos_sub_cos, mul_assoc, mul_sum, ring_nf, simp_rw, sum_range_sub
-/
theorem sin_mul_sum_sin (n : Nat) (a b : Complex) :
    sin (a / 2) * ∑ i in range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (-2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, -2 * sin (a / 2) * sin (a * i + b)
      = ∑ x in range n, (cos (a * (↑(x + 1) - 1 / 2) + b) - cos (-(a * (x - 1 / 2) + b))) := by
      congr! 1 with x hx
      rw [cos_sub_cos]
      push_cast
      ring_nf
    _ = -2 * sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
      simp_rw [cos_neg, sum_range_sub (fun i => cos (a * (i - 1 / 2) + b)), cos_sub_cos]
      ring_nf

/--
theorem `sum_sin` / 定理 `sum_sin`

English:
theorem sum_sin
  given: (n : Nat) {a : Complex} (h : forall k : Int, a != k * (2 * π)) (b : Complex)
  proof: by
  rw [← sin_mul_sum_sin]
  grind [sin_ne_zero_iff]

中文:
定理 sum_sin
  条件: (n : 自然数) {a : 复形} (h : 对任意 k : 整数, a != k * (2 * π)) (b : 复形)
  证明: by
  rw [← sin_mul_sum_sin]
  grind [sin_ne_zero_iff]

Depends on / 依赖: sin_mul_sum_sin, sin_ne_zero_iff
-/
theorem sum_sin (n : Nat) {a : Complex} (h : forall k : Int, a != k * (2 * π)) (b : Complex) :
    ∑ i in range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) / sin (a / 2) := by
  rw [← sin_mul_sum_sin]
  grind [sin_ne_zero_iff]

/--
theorem `sin_mul_sum_cos` / 定理 `sin_mul_sum_cos`

English:
theorem sin_mul_sum_cos
  given: (n : Nat) (a b : Complex)
  proof: by
  apply mul_left_cancel₀ (show (2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, 2 * sin (a / 2) * cos (a * i + b)
      = ∑ x in range n, (sin (a * (↑(x + 1) - 1 / 2) + b) - sin (a * (x - 1 / 2) + b)) := by
      congr! 1 with x hx
      rw [sin_sub_sin]
   

中文:
定理 sin_mul_sum_cos
  条件: (n : 自然数) (a b : 复形)
  证明: by
  apply mul_left_cancel₀ (show (2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, 2 * sin (a / 2) * cos (a * i + b)
      = ∑ x in range n, (sin (a * (↑(x + 1) - 1 / 2) + b) - sin (a * (x - 1 / 2) + b)) := by
      congr! 1 with x hx
      rw [sin_sub_sin]
   

Depends on / 依赖: mul_assoc, mul_sum, ring_nf, simp_rw, sin_sub_sin, sum_range_sub
-/
theorem sin_mul_sum_cos (n : Nat) (a b : Complex) :
    sin (a / 2) * ∑ i in range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (2 : Complex) != 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i in range n, 2 * sin (a / 2) * cos (a * i + b)
      = ∑ x in range n, (sin (a * (↑(x + 1) - 1 / 2) + b) - sin (a * (x - 1 / 2) + b)) := by
      congr! 1 with x hx
      rw [sin_sub_sin]
      push_cast
      ring_nf
    _ = 2 * sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
      simp_rw [sum_range_sub (fun i => sin (a * (i - 1 / 2) + b)), sin_sub_sin]
      ring_nf

/--
theorem `sum_cos` / 定理 `sum_cos`

English:
theorem sum_cos
  given: (n : Nat) {a : Complex} (h : forall k : Int, a != k * (2 * π)) (b : Complex)
  proof: by
  rw [← sin_mul_sum_cos]
  grind [sin_ne_zero_iff]

中文:
定理 sum_cos
  条件: (n : 自然数) {a : 复形} (h : 对任意 k : 整数, a != k * (2 * π)) (b : 复形)
  证明: by
  rw [← sin_mul_sum_cos]
  grind [sin_ne_zero_iff]

Depends on / 依赖: sin_mul_sum_cos, sin_ne_zero_iff
-/
theorem sum_cos (n : Nat) {a : Complex} (h : forall k : Int, a != k * (2 * π)) (b : Complex) :
    ∑ i in range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) / sin (a / 2) := by
  rw [← sin_mul_sum_cos]
  grind [sin_ne_zero_iff]

end Complex

namespace Real

open scoped Real
open Finset

/--
theorem `cos_eq_zero_iff` / 定理 `cos_eq_zero_iff`

English:
theorem cos_eq_zero_iff
  given: {θ : Real}
  statement: cos θ = 0 ↔ exists k : Int, θ = (2 * k + 1) * π / 2
  proof: mod_cast @Complex.cos_eq_zero_iff θ

中文:
定理 cos_eq_zero_iff
  条件: {θ : 实数}
  结论: cos θ = 0 ↔ 存在 k : 整数, θ = (2 * k + 1) * π / 2
  证明: mod_cast @Complex.cos_eq_zero_iff θ

Depends on / 依赖: Complex.cos_eq_zero_iff, cos_eq_zero_iff, mod_cast
-/
theorem cos_eq_zero_iff {θ : Real} : cos θ = 0 ↔ exists k : Int, θ = (2 * k + 1) * π / 2 :=
  mod_cast @Complex.cos_eq_zero_iff θ

/--
theorem `cos_ne_zero_iff` / 定理 `cos_ne_zero_iff`

English:
theorem cos_ne_zero_iff
  given: {θ : Real}
  statement: cos θ != 0 ↔ forall k : Int, θ != (2 * k + 1) * π / 2
  proof: mod_cast @Complex.cos_ne_zero_iff θ

中文:
定理 cos_ne_zero_iff
  条件: {θ : 实数}
  结论: cos θ != 0 ↔ 对任意 k : 整数, θ != (2 * k + 1) * π / 2
  证明: mod_cast @Complex.cos_ne_zero_iff θ

Depends on / 依赖: Complex.cos_ne_zero_iff, cos_ne_zero_iff, mod_cast
-/
theorem cos_ne_zero_iff {θ : Real} : cos θ != 0 ↔ forall k : Int, θ != (2 * k + 1) * π / 2 :=
  mod_cast @Complex.cos_ne_zero_iff θ

/--
theorem `cos_eq_cos_iff` / 定理 `cos_eq_cos_iff`

English:
theorem cos_eq_cos_iff
  given: {x y : Real}
  statement: cos x = cos y ↔ exists k : Int, y = 2 * k * π + x ∨ y = 2 * k * π - x
  proof: mod_cast @Complex.cos_eq_cos_iff x y

中文:
定理 cos_eq_cos_iff
  条件: {x y : 实数}
  结论: cos x = cos y ↔ 存在 k : 整数, y = 2 * k * π + x ∨ y = 2 * k * π - x
  证明: mod_cast @Complex.cos_eq_cos_iff x y

Depends on / 依赖: Complex.cos_eq_cos_iff, cos_eq_cos_iff, mod_cast
-/
theorem cos_eq_cos_iff {x y : Real} : cos x = cos y ↔ exists k : Int, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  mod_cast @Complex.cos_eq_cos_iff x y

/--
theorem `sin_eq_sin_iff` / 定理 `sin_eq_sin_iff`

English:
theorem sin_eq_sin_iff
  given: {x y : Real}
  proof: mod_cast @Complex.sin_eq_sin_iff x y

中文:
定理 sin_eq_sin_iff
  条件: {x y : 实数}
  证明: mod_cast @Complex.sin_eq_sin_iff x y

Depends on / 依赖: Complex.sin_eq_sin_iff, mod_cast, sin_eq_sin_iff
-/
theorem sin_eq_sin_iff {x y : Real} :
    sin x = sin y ↔ exists k : Int, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
  mod_cast @Complex.sin_eq_sin_iff x y

/--
theorem `cos_eq_neg_one_iff` / 定理 `cos_eq_neg_one_iff`

English:
theorem cos_eq_neg_one_iff
  given: {x : Real}
  statement: cos x = -1 ↔ exists k : Int, π + k * (2 * π) = x
  proof: mod_cast @Complex.cos_eq_neg_one_iff x

中文:
定理 cos_eq_neg_one_iff
  条件: {x : 实数}
  结论: cos x = -1 ↔ 存在 k : 整数, π + k * (2 * π) = x
  证明: mod_cast @Complex.cos_eq_neg_one_iff x

Depends on / 依赖: Complex.cos_eq_neg_one_iff, cos_eq_neg_one_iff, mod_cast
-/
theorem cos_eq_neg_one_iff {x : Real} : cos x = -1 ↔ exists k : Int, π + k * (2 * π) = x :=
  mod_cast @Complex.cos_eq_neg_one_iff x

/--
lemma `abs_cos_eq_one_iff` / 引理 `abs_cos_eq_one_iff`

English:
lemma abs_cos_eq_one_iff
  given: {x : Real}
  proof: by
  rw [← abs_one]; rw [abs_eq_abs]; rw [cos_eq_one_iff]; rw [cos_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exa

中文:
引理 abs_cos_eq_one_iff
  条件: {x : 实数}
  证明: by
  rw [← abs_one]; rw [abs_eq_abs]; rw [cos_eq_one_iff]; rw [cos_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exa

Depends on / 依赖: abs_eq_abs, abs_one, cos_eq_neg_one_iff, cos_eq_one_iff, even_or_odd, n.even_or_odd
-/
lemma abs_cos_eq_one_iff {x : Real} :
    |cos x| = 1 ↔ exists k : Int, k * π = x := by
  rw [← abs_one]; rw [abs_eq_abs]; rw [cos_eq_one_iff]; rw [cos_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exact .inr ⟨n, by grind⟩

/--
theorem `sin_eq_one_iff` / 定理 `sin_eq_one_iff`

English:
theorem sin_eq_one_iff
  given: {x : Real}
  statement: sin x = 1 ↔ exists k : Int, π / 2 + k * (2 * π) = x
  proof: mod_cast @Complex.sin_eq_one_iff x

中文:
定理 sin_eq_one_iff
  条件: {x : 实数}
  结论: sin x = 1 ↔ 存在 k : 整数, π / 2 + k * (2 * π) = x
  证明: mod_cast @Complex.sin_eq_one_iff x

Depends on / 依赖: Complex.sin_eq_one_iff, mod_cast, sin_eq_one_iff
-/
theorem sin_eq_one_iff {x : Real} : sin x = 1 ↔ exists k : Int, π / 2 + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_one_iff x

/--
theorem `sin_eq_neg_one_iff` / 定理 `sin_eq_neg_one_iff`

English:
theorem sin_eq_neg_one_iff
  given: {x : Real}
  statement: sin x = -1 ↔ exists k : Int, -(π / 2) + k * (2 * π) = x
  proof: mod_cast @Complex.sin_eq_neg_one_iff x

中文:
定理 sin_eq_neg_one_iff
  条件: {x : 实数}
  结论: sin x = -1 ↔ 存在 k : 整数, -(π / 2) + k * (2 * π) = x
  证明: mod_cast @Complex.sin_eq_neg_one_iff x

Depends on / 依赖: Complex.sin_eq_neg_one_iff, mod_cast, sin_eq_neg_one_iff
-/
theorem sin_eq_neg_one_iff {x : Real} : sin x = -1 ↔ exists k : Int, -(π / 2) + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_neg_one_iff x

/--
lemma `abs_sin_eq_one_iff` / 引理 `abs_sin_eq_one_iff`

English:
lemma abs_sin_eq_one_iff
  given: {x : Real}
  proof: by
  rw [← abs_one]; rw [abs_eq_abs]; rw [sin_eq_one_iff]; rw [sin_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨-1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · ex

中文:
引理 abs_sin_eq_one_iff
  条件: {x : 实数}
  证明: by
  rw [← abs_one]; rw [abs_eq_abs]; rw [sin_eq_one_iff]; rw [sin_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨-1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · ex

Depends on / 依赖: abs_eq_abs, abs_one, even_or_odd, n.even_or_odd, sin_eq_neg_one_iff, sin_eq_one_iff
-/
lemma abs_sin_eq_one_iff {x : Real} :
    |sin x| = 1 ↔ exists k : Int, π / 2 + k * π = x := by
  rw [← abs_one]; rw [abs_eq_abs]; rw [sin_eq_one_iff]; rw [sin_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨-1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exact .inr ⟨n + 1, by grind⟩

/--
theorem `tan_eq_zero_iff` / 定理 `tan_eq_zero_iff`

English:
theorem tan_eq_zero_iff
  given: {θ : Real}
  statement: tan θ = 0 ↔ exists k : Int, k * π / 2 = θ
  proof: mod_cast @Complex.tan_eq_zero_iff θ

中文:
定理 tan_eq_zero_iff
  条件: {θ : 实数}
  结论: tan θ = 0 ↔ 存在 k : 整数, k * π / 2 = θ
  证明: mod_cast @Complex.tan_eq_zero_iff θ

Depends on / 依赖: Complex.tan_eq_zero_iff, mod_cast, tan_eq_zero_iff
-/
theorem tan_eq_zero_iff {θ : Real} : tan θ = 0 ↔ exists k : Int, k * π / 2 = θ :=
  mod_cast @Complex.tan_eq_zero_iff θ

/--
theorem `tan_eq_zero_iff'` / 定理 `tan_eq_zero_iff'`

English:
theorem tan_eq_zero_iff'
  given: {θ : Real} (hθ : cos θ != 0)
  statement: tan θ = 0 ↔ exists k : Int, k * π = θ
  proof: by
  revert hθ
  exact_mod_cast @Complex.tan_eq_zero_iff' θ

中文:
定理 tan_eq_zero_iff'
  条件: {θ : 实数} (hθ : cos θ != 0)
  结论: tan θ = 0 ↔ 存在 k : 整数, k * π = θ
  证明: by
  revert hθ
  exact_mod_cast @Complex.tan_eq_zero_iff' θ

Depends on / 依赖: Complex.tan_eq_zero_iff, revert, tan_eq_zero_iff
-/
theorem tan_eq_zero_iff' {θ : Real} (hθ : cos θ != 0) : tan θ = 0 ↔ exists k : Int, k * π = θ := by
  revert hθ
  exact_mod_cast @Complex.tan_eq_zero_iff' θ

/--
theorem `tan_ne_zero_iff` / 定理 `tan_ne_zero_iff`

English:
theorem tan_ne_zero_iff
  given: {θ : Real}
  statement: tan θ != 0 ↔ forall k : Int, k * π / 2 != θ
  proof: mod_cast @Complex.tan_ne_zero_iff θ

中文:
定理 tan_ne_zero_iff
  条件: {θ : 实数}
  结论: tan θ != 0 ↔ 对任意 k : 整数, k * π / 2 != θ
  证明: mod_cast @Complex.tan_ne_zero_iff θ

Depends on / 依赖: Complex.tan_ne_zero_iff, mod_cast, tan_ne_zero_iff
-/
theorem tan_ne_zero_iff {θ : Real} : tan θ != 0 ↔ forall k : Int, k * π / 2 != θ :=
  mod_cast @Complex.tan_ne_zero_iff θ

/--
lemma `tan_eq_zero_of_cos_eq_zero` / 引理 `tan_eq_zero_of_cos_eq_zero`

English:
lemma tan_eq_zero_of_cos_eq_zero
  given: {x} (h : cos x = 0)
  statement: tan x = 0
  proof: mod_cast @Complex.tan_eq_zero_of_cos_eq_zero x (mod_cast h)

中文:
引理 tan_eq_zero_of_cos_eq_zero
  条件: {x} (h : cos x = 0)
  结论: tan x = 0
  证明: mod_cast @Complex.tan_eq_zero_of_cos_eq_zero x (mod_cast h)

Depends on / 依赖: Complex.tan_eq_zero_of_cos_eq_zero, mod_cast, tan_eq_zero_of_cos_eq_zero
-/
lemma tan_eq_zero_of_cos_eq_zero {x} (h : cos x = 0) : tan x = 0 :=
  mod_cast @Complex.tan_eq_zero_of_cos_eq_zero x (mod_cast h)

-- tangent half-angle substitution formulas

/--
theorem `cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq` / 定理 `cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq`

English:
theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
  given: (x : Real) (h : cos x != -1)
  proof: mod_cast @Complex.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq x (mod_cast h)

中文:
定理 cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
  条件: (x : 实数) (h : cos x != -1)
  证明: mod_cast @Complex.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq x (mod_cast h)

Depends on / 依赖: Complex.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq, cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq, mod_cast
-/
theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (x : Real) (h : cos x != -1) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) :=
  mod_cast @Complex.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq x (mod_cast h)

/--
theorem `sin_eq_two_mul_tan_half_div_one_add_tan_half_sq` / 定理 `sin_eq_two_mul_tan_half_div_one_add_tan_half_sq`

English:
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq
  given: (x : Real)
  proof: mod_cast @Complex.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq x

中文:
定理 sin_eq_two_mul_tan_half_div_one_add_tan_half_sq
  条件: (x : 实数)
  证明: mod_cast @Complex.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq x

Depends on / 依赖: Complex.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, mod_cast, sin_eq_two_mul_tan_half_div_one_add_tan_half_sq
-/
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq (x : Real) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) :=
  mod_cast @Complex.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq x

/--
theorem `tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq` / 定理 `tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq`

English:
theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq
  given: (x : Real)
  proof: mod_cast @Complex.tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq x

中文:
定理 tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq
  条件: (x : 实数)
  证明: mod_cast @Complex.tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq x

Depends on / 依赖: Complex.tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq, mod_cast, tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq
-/
theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq (x : Real) :
    tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) :=
  mod_cast @Complex.tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq x

/--
theorem `sin_mul_sum_sin` / 定理 `sin_mul_sum_sin`

English:
theorem sin_mul_sum_sin
  given: (n : Nat) (a b : Real)
  proof: by
  exact_mod_cast congr($(Complex.sin_mul_sum_sin n a b).re)

中文:
定理 sin_mul_sum_sin
  条件: (n : 自然数) (a b : 实数)
  证明: by
  exact_mod_cast congr($(Complex.sin_mul_sum_sin n a b).re)

Depends on / 依赖: Complex.sin_mul_sum_sin, sin_mul_sum_sin
-/
theorem sin_mul_sum_sin (n : Nat) (a b : Real) :
    sin (a / 2) * ∑ i in range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_sin n a b).re)

/--
theorem `sum_sin` / 定理 `sum_sin`

English:
theorem sum_sin
  given: (n : Nat) {a : Real} (h : forall k : Int, a != k * (2 * π)) (b : Real)
  proof: by
  have h := Complex.sum_sin n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

中文:
定理 sum_sin
  条件: (n : 自然数) {a : 实数} (h : 对任意 k : 整数, a != k * (2 * π)) (b : 实数)
  证明: by
  have h := Complex.sum_sin n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

Depends on / 依赖: Complex.sum_sin, sum_sin
-/
theorem sum_sin (n : Nat) {a : Real} (h : forall k : Int, a != k * (2 * π)) (b : Real) :
    ∑ i in range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) / sin (a / 2) := by
  have h := Complex.sum_sin n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

/--
theorem `sin_mul_sum_cos` / 定理 `sin_mul_sum_cos`

English:
theorem sin_mul_sum_cos
  given: (n : Nat) (a b : Real)
  proof: by
  exact_mod_cast congr($(Complex.sin_mul_sum_cos n a b).re)

中文:
定理 sin_mul_sum_cos
  条件: (n : 自然数) (a b : 实数)
  证明: by
  exact_mod_cast congr($(Complex.sin_mul_sum_cos n a b).re)

Depends on / 依赖: Complex.sin_mul_sum_cos, sin_mul_sum_cos
-/
theorem sin_mul_sum_cos (n : Nat) (a b : Real) :
    sin (a / 2) * ∑ i in range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_cos n a b).re)

/--
theorem `sum_cos` / 定理 `sum_cos`

English:
theorem sum_cos
  given: (n : Nat) {a : Real} (h : forall k : Int, a != k * (2 * π)) (b : Real)
  proof: by
  have h := Complex.sum_cos n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

中文:
定理 sum_cos
  条件: (n : 自然数) {a : 实数} (h : 对任意 k : 整数, a != k * (2 * π)) (b : 实数)
  证明: by
  have h := Complex.sum_cos n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

Depends on / 依赖: Complex.sum_cos, sum_cos
-/
theorem sum_cos (n : Nat) {a : Real} (h : forall k : Int, a != k * (2 * π)) (b : Real) :
    ∑ i in range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) / sin (a / 2) := by
  have h := Complex.sum_cos n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

end Real
