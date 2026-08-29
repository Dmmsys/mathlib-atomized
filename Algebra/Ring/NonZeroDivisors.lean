/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Algebra.Ring.Basic

/-!
# Non-zero divisors in a ring
-/

public section

assert_not_exists Field

open scoped nonZeroDivisors

section Monoid

variable {R : Type*} [Monoid R] {r : R}

@[to_additive]
/--
theorem `IsLeftRegular.pow_injective` / 定理 `IsLeftRegular.pow_injective`

English:
theorem IsLeftRegular.pow_injective
  statement: [IsMulTorsionFree R]
  proof: by
  intro n m hnm
  have main {n m} (h₁ : n <= m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add]; rw [eq_comm]; rw [IsLeftRegular.mul_left_eq_self_iff (hx.pow n)]; rw [pow_eq_one_iff_right hx']
      at h₂
    rw [h₂]; rw [Nat.add_zero]
  obtai

中文:
定理 IsLeftRegular.pow_injective
  结论: [IsMulTorsionFree R]
  证明: by
  intro n m hnm
  have main {n m} (h₁ : n <= m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add]; rw [eq_comm]; rw [IsLeftRegular.mul_left_eq_self_iff (hx.pow n)]; rw [pow_eq_one_iff_right hx']
      at h₂
    rw [h₂]; rw [Nat.add_zero]
  obtai

Depends on / 依赖: IsLeftRegular, IsLeftRegular.mul_left_eq_self_iff, Nat.add_zero, Nat.exists_eq_add_of_le, Nat.le_or_le, add_zero, eq_comm, exists_eq_add_of_le, hnm.symm, hx.pow, le_or_le, mul_left_eq_self_iff, pow_add, pow_eq_one_iff_right
-/
theorem IsLeftRegular.pow_injective [IsMulTorsionFree R]
    (hx : IsLeftRegular r) (hx' : r != 1) : Function.Injective (fun n => r ^ n) := by
  intro n m hnm
  have main {n m} (h₁ : n <= m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add]; rw [eq_comm]; rw [IsLeftRegular.mul_left_eq_self_iff (hx.pow n)]; rw [pow_eq_one_iff_right hx']
      at h₂
    rw [h₂]; rw [Nat.add_zero]
  obtain h | h := Nat.le_or_le n m
  · exact main h hnm
  · exact (main h hnm.symm).symm

@[to_additive]
/--
theorem `IsRightRegular.pow_injective` / 定理 `IsRightRegular.pow_injective`

English:
theorem IsRightRegular.pow_injective
  statement: {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M}
  proof: MulOpposite.unop_injective.comp (isLeftRegular_op.mpr hx).pow_injective
    (MulOpposite.op_eq_one_iff x).not.mpr hx'

中文:
定理 IsRightRegular.pow_injective
  结论: {M : 类型} [Monoid M] [IsMulTorsionFree M] {x : M}
  证明: MulOpposite.unop_injective.comp (isLeftRegular_op.mpr hx).pow_injective
    (MulOpposite.op_eq_one_iff x).not.mpr hx'

Depends on / 依赖: MulOpposite, MulOpposite.op_eq_one_iff, MulOpposite.unop_injective.comp, isLeftRegular_op, isLeftRegular_op.mpr, not.mpr, op_eq_one_iff, pow_injective, unop_injective
-/
theorem IsRightRegular.pow_injective {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M}
    (hx : IsRightRegular x) (hx' : x != 1) : Function.Injective (fun n => x ^ n) :=
MulOpposite.unop_injective.comp (isLeftRegular_op.mpr hx).pow_injective
    (MulOpposite.op_eq_one_iff x).not.mpr hx'

/--
theorem `IsMulTorsionFree.pow_right_injective` / 定理 `IsMulTorsionFree.pow_right_injective`

English:
theorem IsMulTorsionFree.pow_right_injective
  statement: {M : Type*} [CancelMonoid M] [IsMulTorsionFree M]
  proof: IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

@[simp]

中文:
定理 IsMulTorsionFree.pow_right_injective
  结论: {M : 类型} [CancelMonoid M] [IsMulTorsionFree M]
  证明: IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

@[simp]

Depends on / 依赖: IsLeftRegular, IsLeftRegular.all, IsLeftRegular.pow_injective, pow_injective
-/
theorem IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTorsionFree M]
    {x : M} (hx : x != 1) : Function.Injective (fun n => x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

@[simp]
/--
theorem `IsMulTorsionFree.pow_right_inj` / 定理 `IsMulTorsionFree.pow_right_inj`

English:
theorem IsMulTorsionFree.pow_right_inj
  statement: {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
  proof: (pow_right_injective hx).eq_iff

中文:
定理 IsMulTorsionFree.pow_right_inj
  结论: {M : 类型} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
  证明: (pow_right_injective hx).eq_iff

Depends on / 依赖: eq_iff, pow_right_injective
-/
theorem IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
    (hx : x != 1) {n m : Nat} : x ^ n = x ^ m ↔ n = m := (pow_right_injective hx).eq_iff

/--
theorem `IsMulTorsionFree.pow_right_injective₀` / 定理 `IsMulTorsionFree.pow_right_injective₀`

English:
theorem IsMulTorsionFree.pow_right_injective₀
  statement: {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
  proof: IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

@[simp]

中文:
定理 IsMulTorsionFree.pow_right_injective₀
  结论: {M : 类型} [MonoidWithZero M] [IsLeftCancelMulZero M]
  证明: IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

@[simp]

Depends on / 依赖: IsLeftCancelMulZero, IsLeftCancelMulZero.mul_left_cancel_of_ne_zero, IsLeftRegular, IsLeftRegular.pow_injective, mul_left_cancel_of_ne_zero, pow_injective
-/
theorem IsMulTorsionFree.pow_right_injective₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x != 1) (hx' : x != 0) : Function.Injective (fun n => x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

@[simp]
/--
theorem `IsMulTorsionFree.pow_right_inj₀` / 定理 `IsMulTorsionFree.pow_right_inj₀`

English:
theorem IsMulTorsionFree.pow_right_inj₀
  statement: {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
  proof: (pow_right_injective₀ hx hx').eq_iff

中文:
定理 IsMulTorsionFree.pow_right_inj₀
  结论: {M : 类型} [MonoidWithZero M] [IsLeftCancelMulZero M]
  证明: (pow_right_injective₀ hx hx').eq_iff

Depends on / 依赖: eq_iff
-/
theorem IsMulTorsionFree.pow_right_inj₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x != 1) (hx' : x != 0) {n m : Nat} : x ^ n = x ^ m ↔ n = m :=
  (pow_right_injective₀ hx hx').eq_iff

variable [Finite R]

/--
theorem `IsLeftRegular.isUnit_of_finite` / 定理 `IsLeftRegular.isUnit_of_finite`

English:
theorem IsLeftRegular.isUnit_of_finite
  given: (h : IsLeftRegular r)
  statement: IsUnit r
  proof: by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

中文:
定理 IsLeftRegular.isUnit_of_finite
  条件: (h : IsLeftRegular r)
  结论: IsUnit r
  证明: by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

Depends on / 依赖: Finite, Finite.injective_iff_bijective, IsUnit, IsUnit.isUnit_iff_mulLeft_bijective, injective_iff_bijective, isUnit_iff_mulLeft_bijective
-/
theorem IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

/--
theorem `IsRightRegular.isUnit_of_finite` / 定理 `IsRightRegular.isUnit_of_finite`

English:
theorem IsRightRegular.isUnit_of_finite
  given: (h : IsRightRegular r)
  statement: IsUnit r
  proof: by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

中文:
定理 IsRightRegular.isUnit_of_finite
  条件: (h : IsRightRegular r)
  结论: IsUnit r
  证明: by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

Depends on / 依赖: Finite, Finite.injective_iff_bijective, IsUnit, IsUnit.isUnit_iff_mulRight_bijective, injective_iff_bijective, isUnit_iff_mulRight_bijective
-/
theorem IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

/--
theorem `isRegular_iff_isUnit_of_finite` / 定理 `isRegular_iff_isUnit_of_finite`

English:
theorem isRegular_iff_isUnit_of_finite
  statement: IsRegular r ↔ IsUnit r where
  proof: h.1.isUnit_of_finite
  mpr h := h.isRegular

中文:
定理 isRegular_iff_isUnit_of_finite
  结论: IsRegular r ↔ IsUnit r where
  证明: h.1.isUnit_of_finite
  mpr h := h.isRegular

Depends on / 依赖: isUnit_of_finite
-/
theorem isRegular_iff_isUnit_of_finite : IsRegular r ↔ IsUnit r where
  mp h := h.1.isUnit_of_finite
  mpr h := h.isRegular

end Monoid

section Ring

variable {R : Type*} [Ring R] {a x y r : R}

/--
lemma `isLeftRegular_iff_mem_nonZeroDivisorsLeft` / 引理 `isLeftRegular_iff_mem_nonZeroDivisorsLeft`

English:
lemma isLeftRegular_iff_mem_nonZeroDivisorsLeft
  statement: IsLeftRegular r ↔ r in nonZeroDivisorsLeft R
  proof: isLeftRegular_iff_right_eq_zero_of_mul

中文:
引理 isLeftRegular_iff_mem_nonZeroDivisorsLeft
  结论: IsLeftRegular r ↔ r in nonZeroDivisorsLeft R
  证明: isLeftRegular_iff_right_eq_zero_of_mul

Depends on / 依赖: isLeftRegular_iff_right_eq_zero_of_mul
-/
lemma isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r in nonZeroDivisorsLeft R :=
  isLeftRegular_iff_right_eq_zero_of_mul

/--
lemma `isRightRegular_iff_mem_nonZeroDivisorsRight` / 引理 `isRightRegular_iff_mem_nonZeroDivisorsRight`

English:
lemma isRightRegular_iff_mem_nonZeroDivisorsRight
  statement: IsRightRegular r ↔ r in nonZeroDivisorsRight R
  proof: isRightRegular_iff_left_eq_zero_of_mul

中文:
引理 isRightRegular_iff_mem_nonZeroDivisorsRight
  结论: IsRightRegular r ↔ r in nonZeroDivisorsRight R
  证明: isRightRegular_iff_left_eq_zero_of_mul

Depends on / 依赖: isRightRegular_iff_left_eq_zero_of_mul
-/
lemma isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r in nonZeroDivisorsRight R :=
  isRightRegular_iff_left_eq_zero_of_mul

/--
lemma `isRegular_iff_mem_nonZeroDivisors` / 引理 `isRegular_iff_mem_nonZeroDivisors`

English:
lemma isRegular_iff_mem_nonZeroDivisors
  statement: IsRegular r ↔ r in R⁰
  proof: isRegular_iff_eq_zero_of_mul

中文:
引理 isRegular_iff_mem_nonZeroDivisors
  结论: IsRegular r ↔ r in R⁰
  证明: isRegular_iff_eq_zero_of_mul

Depends on / 依赖: isRegular_iff_eq_zero_of_mul
-/
lemma isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r in R⁰ := isRegular_iff_eq_zero_of_mul

/--
lemma `le_nonZeroDivisorsLeft_iff_isLeftRegular` / 引理 `le_nonZeroDivisorsLeft_iff_isLeftRegular`

English:
lemma le_nonZeroDivisorsLeft_iff_isLeftRegular
  given: {S : Submonoid R}
  proof: by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]

中文:
引理 le_nonZeroDivisorsLeft_iff_isLeftRegular
  条件: {S : Submonoid R}
  证明: by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]

Depends on / 依赖: SetLike, SetLike.le_def, Subtype, Subtype.forall, isLeftRegular_iff_mem_nonZeroDivisorsLeft, le_def, simp_rw
-/
lemma le_nonZeroDivisorsLeft_iff_isLeftRegular {S : Submonoid R} :
    S <= nonZeroDivisorsLeft R ↔ forall s : S, IsLeftRegular (s : R) := by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]

/--
lemma `le_nonZeroDivisorsRight_iff_isRightRegular` / 引理 `le_nonZeroDivisorsRight_iff_isRightRegular`

English:
lemma le_nonZeroDivisorsRight_iff_isRightRegular
  given: {S : Submonoid R}
  proof: by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]

中文:
引理 le_nonZeroDivisorsRight_iff_isRightRegular
  条件: {S : Submonoid R}
  证明: by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]

Depends on / 依赖: SetLike, SetLike.le_def, Subtype, Subtype.forall, isRightRegular_iff_mem_nonZeroDivisorsRight, le_def, simp_rw
-/
lemma le_nonZeroDivisorsRight_iff_isRightRegular {S : Submonoid R} :
    S <= nonZeroDivisorsRight R ↔ forall s : S, IsRightRegular (s : R) := by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]

/--
lemma `le_nonZeroDivisors_iff_isRegular` / 引理 `le_nonZeroDivisors_iff_isRegular`

English:
lemma le_nonZeroDivisors_iff_isRegular
  given: {S : Submonoid R}
  proof: by
  simp_rw [nonZeroDivisors, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular,
    le_nonZeroDivisorsRight_iff_isRightRegular, isRegular_iff, forall_and]

中文:
引理 le_nonZeroDivisors_iff_isRegular
  条件: {S : Submonoid R}
  证明: by
  simp_rw [nonZeroDivisors, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular,
    le_nonZeroDivisorsRight_iff_isRightRegular, isRegular_iff, forall_and]

Depends on / 依赖: forall_and, isRegular_iff, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular, le_nonZeroDivisorsRight_iff_isRightRegular, nonZeroDivisors, simp_rw
-/
lemma le_nonZeroDivisors_iff_isRegular {S : Submonoid R} :
    S <= R⁰ ↔ forall s : S, IsRegular (s : R) := by
  simp_rw [nonZeroDivisors, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular,
    le_nonZeroDivisorsRight_iff_isRightRegular, isRegular_iff, forall_and]

/--
lemma `mul_cancel_left_mem_nonZeroDivisorsLeft` / 引理 `mul_cancel_left_mem_nonZeroDivisorsLeft`

English:
lemma mul_cancel_left_mem_nonZeroDivisorsLeft
  given: (hr : r in nonZeroDivisorsLeft R)
  proof: ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩

中文:
引理 mul_cancel_left_mem_nonZeroDivisorsLeft
  条件: (hr : r in nonZeroDivisorsLeft R)
  证明: ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩

Depends on / 依赖: congr_arg, isLeftRegular_iff_mem_nonZeroDivisorsLeft, isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr
-/
lemma mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r in nonZeroDivisorsLeft R) :
    r * x = r * y ↔ x = y :=
  ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩

/--
lemma `mul_cancel_right_mem_nonZeroDivisorsRight` / 引理 `mul_cancel_right_mem_nonZeroDivisorsRight`

English:
lemma mul_cancel_right_mem_nonZeroDivisorsRight
  given: (hr : r in nonZeroDivisorsRight R)
  proof: ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩

@[simp]

中文:
引理 mul_cancel_right_mem_nonZeroDivisorsRight
  条件: (hr : r in nonZeroDivisorsRight R)
  证明: ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩

@[simp]

Depends on / 依赖: congr_arg, isRightRegular_iff_mem_nonZeroDivisorsRight, isRightRegular_iff_mem_nonZeroDivisorsRight.mpr
-/
lemma mul_cancel_right_mem_nonZeroDivisorsRight (hr : r in nonZeroDivisorsRight R) :
    x * r = y * r ↔ x = y :=
  ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩

@[simp]
/--
lemma `mul_cancel_left_mem_nonZeroDivisors` / 引理 `mul_cancel_left_mem_nonZeroDivisors`

English:
lemma mul_cancel_left_mem_nonZeroDivisors
  given: (hr : r in R⁰)
  statement: r * x = r * y ↔ x = y
  proof: mul_cancel_left_mem_nonZeroDivisorsLeft hr.1

中文:
引理 mul_cancel_left_mem_nonZeroDivisors
  条件: (hr : r in R⁰)
  结论: r * x = r * y ↔ x = y
  证明: mul_cancel_left_mem_nonZeroDivisorsLeft hr.1

Depends on / 依赖: mul_cancel_left_mem_nonZeroDivisorsLeft
-/
lemma mul_cancel_left_mem_nonZeroDivisors (hr : r in R⁰) : r * x = r * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisorsLeft hr.1

/--
lemma `mul_cancel_left_coe_nonZeroDivisors` / 引理 `mul_cancel_left_coe_nonZeroDivisors`

English:
lemma mul_cancel_left_coe_nonZeroDivisors
  given: {c : R⁰}
  statement: (c : R) * x = c * y ↔ x = y
  proof: mul_cancel_left_mem_nonZeroDivisors c.prop

中文:
引理 mul_cancel_left_coe_nonZeroDivisors
  条件: {c : R⁰}
  结论: (c : R) * x = c * y ↔ x = y
  证明: mul_cancel_left_mem_nonZeroDivisors c.prop

Depends on / 依赖: IsOpenImmersion, c.prop, mul_cancel_left_mem_nonZeroDivisors, of_isIso
-/
lemma mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop

/--
lemma `mul_cancel_right_mem_nonZeroDivisors` / 引理 `mul_cancel_right_mem_nonZeroDivisors`

English:
lemma mul_cancel_right_mem_nonZeroDivisors
  given: (hr : r in R⁰)
  statement: x * r = y * r ↔ x = y
  proof: mul_cancel_right_mem_nonZeroDivisorsRight hr.2

中文:
引理 mul_cancel_right_mem_nonZeroDivisors
  条件: (hr : r in R⁰)
  结论: x * r = y * r ↔ x = y
  证明: mul_cancel_right_mem_nonZeroDivisorsRight hr.2

Depends on / 依赖: mul_cancel_right_mem_nonZeroDivisorsRight
-/
lemma mul_cancel_right_mem_nonZeroDivisors (hr : r in R⁰) : x * r = y * r ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisorsRight hr.2

/--
lemma `mul_cancel_right_coe_nonZeroDivisors` / 引理 `mul_cancel_right_coe_nonZeroDivisors`

English:
lemma mul_cancel_right_coe_nonZeroDivisors
  given: {c : R⁰}
  statement: x * c = y * c ↔ x = y
  proof: mul_cancel_right_mem_nonZeroDivisors c.prop

中文:
引理 mul_cancel_right_coe_nonZeroDivisors
  条件: {c : R⁰}
  结论: x * c = y * c ↔ x = y
  证明: mul_cancel_right_mem_nonZeroDivisors c.prop

Depends on / 依赖: c.prop, mul_cancel_right_mem_nonZeroDivisors
-/
lemma mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop

/--
lemma `isUnit_iff_mem_nonZeroDivisors_of_finite` / 引理 `isUnit_iff_mem_nonZeroDivisors_of_finite`

English:
lemma isUnit_iff_mem_nonZeroDivisors_of_finite
  given: [Finite R]
  statement: IsUnit a ↔ a in nonZeroDivisors R
  proof: by
  rw [← isRegular_iff_mem_nonZeroDivisors]; rw [isRegular_iff_isUnit_of_finite]

中文:
引理 isUnit_iff_mem_nonZeroDivisors_of_finite
  条件: [Finite R]
  结论: IsUnit a ↔ a in nonZeroDivisors R
  证明: by
  rw [← isRegular_iff_mem_nonZeroDivisors]; rw [isRegular_iff_isUnit_of_finite]

Depends on / 依赖: f.toLRSHom.stalkMap, isRegular_iff_isUnit_of_finite, isRegular_iff_mem_nonZeroDivisors, stalkMap, toLRSHom
-/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a in nonZeroDivisors R := by
  rw [← isRegular_iff_mem_nonZeroDivisors]; rw [isRegular_iff_isUnit_of_finite]

/--
lemma `dvd_cancel_left_mem_nonZeroDivisors` / 引理 `dvd_cancel_left_mem_nonZeroDivisors`

English:
lemma dvd_cancel_left_mem_nonZeroDivisors
  given: (hr : r in R⁰)
  statement: r * x ∣ r * y ↔ x ∣ y
  proof: (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left

中文:
引理 dvd_cancel_left_mem_nonZeroDivisors
  条件: (hr : r in R⁰)
  结论: r * x ∣ r * y ↔ x ∣ y
  证明: (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left

Depends on / 依赖: dvd_cancel_left, isLeftRegular_iff_mem_nonZeroDivisorsLeft, isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr
-/
lemma dvd_cancel_left_mem_nonZeroDivisors (hr : r in R⁰) : r * x ∣ r * y ↔ x ∣ y :=
  (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left

/--
lemma `dvd_cancel_left_coe_nonZeroDivisors` / 引理 `dvd_cancel_left_coe_nonZeroDivisors`

English:
lemma dvd_cancel_left_coe_nonZeroDivisors
  given: {c : R⁰}
  statement: c * x ∣ c * y ↔ x ∣ y
  proof: dvd_cancel_left_mem_nonZeroDivisors c.prop

中文:
引理 dvd_cancel_left_coe_nonZeroDivisors
  条件: {c : R⁰}
  结论: c * x ∣ c * y ↔ x ∣ y
  证明: dvd_cancel_left_mem_nonZeroDivisors c.prop

Depends on / 依赖: c.prop, dvd_cancel_left_mem_nonZeroDivisors
-/
lemma dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

end Ring

section CommRing
variable {R : Type*} [CommRing R] {r x y : R}

/--
lemma `dvd_cancel_right_mem_nonZeroDivisors` / 引理 `dvd_cancel_right_mem_nonZeroDivisors`

English:
lemma dvd_cancel_right_mem_nonZeroDivisors
  given: (hr : r in R⁰)
  statement: x * r ∣ y * r ↔ x ∣ y
  proof: by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]

中文:
引理 dvd_cancel_right_mem_nonZeroDivisors
  条件: (hr : r in R⁰)
  结论: x * r ∣ y * r ↔ x ∣ y
  证明: by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]

Depends on / 依赖: dvd_cancel_left_mem_nonZeroDivisors, mul_comm, simp_rw
-/
lemma dvd_cancel_right_mem_nonZeroDivisors (hr : r in R⁰) : x * r ∣ y * r ↔ x ∣ y := by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]

/--
lemma `dvd_cancel_right_coe_nonZeroDivisors` / 引理 `dvd_cancel_right_coe_nonZeroDivisors`

English:
lemma dvd_cancel_right_coe_nonZeroDivisors
  given: {c : R⁰}
  statement: x * c ∣ y * c ↔ x ∣ y
  proof: dvd_cancel_right_mem_nonZeroDivisors c.prop

中文:
引理 dvd_cancel_right_coe_nonZeroDivisors
  条件: {c : R⁰}
  结论: x * c ∣ y * c ↔ x ∣ y
  证明: dvd_cancel_right_mem_nonZeroDivisors c.prop

Depends on / 依赖: c.prop, dvd_cancel_right_mem_nonZeroDivisors
-/
lemma dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y :=
  dvd_cancel_right_mem_nonZeroDivisors c.prop

end CommRing
