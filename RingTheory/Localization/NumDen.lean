/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Numerator and denominator in a localization

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


namespace IsFractionRing

open IsLocalization

section NumDen

variable (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/--
theorem `exists_reduced_fraction` / 定理 `exists_reduced_fraction`

English:
theorem exists_reduced_fraction
  given: (x : K)
  proof: by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_

中文:
定理 exists_reduced_fraction
  条件: (x : K)
  证明: by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors, UniqueFactorizationMonoid, UniqueFactorizationMonoid.exists_reduced_factors, _nonzero, b_nonzero, exists_integer_multiple, exists_reduced_factors, map_mul, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mul_assoc, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors.mp, no_factor, nonZeroDivisors, smul_def, to_map_ne_zero_of_mem_nonZeroDivisors
-/
theorem exists_reduced_fraction (x : K) :
    exists (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x := by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_nonzero
  refine ⟨a', ⟨b', b'_nonzero⟩, no_factor, ?_⟩
  refine mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) ?_
  simp only [map_mul, Algebra.smul_def] at *
  rw [← hab]; rw [mul_assoc]; rw [mk'_spec' _ a' ⟨b']; rw [b'_nonzero⟩]

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (x : K)
  body: Classical.choose (exists_reduced_fraction A x)

中文:
定义 num
  签名: (x : K)
  定义体: Classical.choose (exists_reduced_fraction A x)

Depends on / 依赖: Classical, Classical.choose, exists_reduced_fraction
-/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)

/--
Definition of `den` / `den` 的定义

English:
definition den
  signature: (x : K)
  body: Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))

中文:
定义 den
  签名: (x : K)
  定义体: Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, DiscreteTopology, Monoid, TopologicalSpace, choose_spec, exists_reduced_fraction
-/
noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))

/--
theorem `num_den_reduced` / 定理 `num_den_reduced`

English:
theorem num_den_reduced
  given: (x : K)
  statement: IsRelPrime (num A x) (den A x)
  proof: (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

中文:
定理 num_den_reduced
  条件: (x : K)
  结论: IsRelPrime (num A x) (den A x)
  证明: (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

Depends on / 依赖: Classical, Classical.choose_spec, ContinuousInv, TopologicalSpace, choose_spec, exists_reduced_fraction
-/
theorem num_den_reduced (x : K) : IsRelPrime (num A x) (den A x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

-- `@[simp]` normal form is called `mk'_num_den'`.
/--
theorem `mk'_num_den` / 定理 `mk'_num_den`

English:
theorem mk'_num_den
  given: (x : K)
  statement: mk' K (num A x) (den A x) = x
  proof: (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2

@[simp]

中文:
定理 mk'_num_den
  条件: (x : K)
  结论: mk' K (num A x) (den A x) = x
  证明: (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2

@[simp]

Depends on / 依赖: GroupWithZero
-/
theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2

@[simp]
/--
theorem `mk'_num_den'` / 定理 `mk'_num_den'`

English:
theorem mk'_num_den'
  given: (x : K)
  statement: algebraMap A K (num A x) / algebraMap A K (den A x) = x
  proof: by
  rw [← mk'_eq_div]
  apply mk'_num_den

中文:
定理 mk'_num_den'
  条件: (x : K)
  结论: algebraMap A K (num A x) / algebraMap A K (den A x) = x
  证明: by
  rw [← mk'_eq_div]
  apply mk'_num_den
-/
theorem mk'_num_den' (x : K) : algebraMap A K (num A x) / algebraMap A K (den A x) = x := by
  rw [← mk'_eq_div]
  apply mk'_num_den

variable {A}

/--
theorem `num_mul_den_eq_num_iff_eq` / 定理 `num_mul_den_eq_num_iff_eq`

English:
theorem num_mul_den_eq_num_iff_eq
  given: {x y : K}
  proof: ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

中文:
定理 num_mul_den_eq_num_iff_eq
  条件: {x y : K}
  证明: ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

Depends on / 依赖: _iff_mul_eq, _iff_mul_eq.mp, _iff_mul_eq.mpr, _num_den, eq_mk
-/
theorem num_mul_den_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (den A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

/--
theorem `num_mul_den_eq_num_iff_eq'` / 定理 `num_mul_den_eq_num_iff_eq'`

English:
theorem num_mul_den_eq_num_iff_eq'
  given: {x y : K}
  proof: ⟨fun h => by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

中文:
定理 num_mul_den_eq_num_iff_eq'
  条件: {x y : K}
  证明: ⟨fun h => by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

Depends on / 依赖: _iff_mul_eq, _iff_mul_eq.mp, _iff_mul_eq.mpr, _num_den, eq_comm, eq_mk
-/
theorem num_mul_den_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h => by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

/--
theorem `num_mul_den_eq_num_mul_den_iff_eq` / 定理 `num_mul_den_eq_num_mul_den_iff_eq`

English:
theorem num_mul_den_eq_num_mul_den_iff_eq
  given: {x y : K}
  proof: ⟨fun h => by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h => by rw [h]⟩

中文:
定理 num_mul_den_eq_num_mul_den_iff_eq
  条件: {x y : K}
  证明: ⟨fun h => by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h => by rw [h]⟩

Depends on / 依赖: _eq_of_eq, _num_den
-/
theorem num_mul_den_eq_num_mul_den_iff_eq {x y : K} :
    num A y * den A x = num A x * den A y ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h => by rw [h]⟩

/--
theorem `eq_zero_of_num_eq_zero` / 定理 `eq_zero_of_num_eq_zero`

English:
theorem eq_zero_of_num_eq_zero
  given: {x : K} (h : num A x = 0)
  statement: x = 0
  proof: (num_mul_den_eq_num_iff_eq' (A := A)).mp (by rw [zero_mul, h, map_zero])

@[simp]

中文:
定理 eq_zero_of_num_eq_zero
  条件: {x : K} (h : num A x = 0)
  结论: x = 0
  证明: (num_mul_den_eq_num_iff_eq' (A := A)).mp (by rw [zero_mul, h, map_zero])

@[simp]

Depends on / 依赖: map_zero, num_mul_den_eq_num_iff_eq, zero_mul
-/
theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  (num_mul_den_eq_num_iff_eq' (A := A)).mp (by rw [zero_mul, h, map_zero])

@[simp]
/--
lemma `num_zero` / 引理 `num_zero`

English:
lemma num_zero
  statement: IsFractionRing.num A (0 : K) = 0
  proof: by
  have := mk'_num_den' A (0 : K)
  simp only [div_eq_zero_iff] at this
  simp_all

@[simp]

中文:
引理 num_zero
  结论: IsFractionRing.num A (0 : K) = 0
  证明: by
  have := mk'_num_den' A (0 : K)
  simp only [div_eq_zero_iff] at this
  simp_all

@[simp]

Depends on / 依赖: _num_den, div_eq_zero_iff
-/
lemma num_zero : IsFractionRing.num A (0 : K) = 0 := by
  have := mk'_num_den' A (0 : K)
  simp only [div_eq_zero_iff] at this
  simp_all

@[simp]
/--
lemma `num_eq_zero` / 引理 `num_eq_zero`

English:
lemma num_eq_zero
  given: (x : K)
  statement: IsFractionRing.num A x = 0 ↔ x = 0
  proof: ⟨eq_zero_of_num_eq_zero, fun h => h ▸ num_zero⟩

中文:
引理 num_eq_zero
  条件: (x : K)
  结论: IsFractionRing.num A x = 0 ↔ x = 0
  证明: ⟨eq_zero_of_num_eq_zero, fun h => h ▸ num_zero⟩

Depends on / 依赖: eq_zero_of_num_eq_zero, num_zero
-/
lemma num_eq_zero (x : K) : IsFractionRing.num A x = 0 ↔ x = 0 :=
  ⟨eq_zero_of_num_eq_zero, fun h => h ▸ num_zero⟩

/--
theorem `isInteger_of_isUnit_den` / 定理 `isInteger_of_isUnit_den`

English:
theorem isInteger_of_isUnit_den
  given: {x : K} (h : IsUnit (den A x : A))
  statement: IsInteger A x
  proof: by
  obtain ⟨d, hd⟩ := h
  have d_ne_zero : algebraMap A K (den A x) != 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul]; rw [map_units_inv]; rw [hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul

中文:
定理 isInteger_of_isUnit_den
  条件: {x : K} (h : IsUnit (den A x : A))
  结论: Is整数eger A x
  证明: by
  obtain ⟨d, hd⟩ := h
  have d_ne_zero : algebraMap A K (den A x) != 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul]; rw [map_units_inv]; rw [hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul

Depends on / 依赖: IsFractionRing, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors, _num_den, _root_, _root_.trans, _spec, algebraMap, d_ne_zero, map_mul, map_units_inv, mul_assoc, one_mul, to_map_ne_zero_of_mem_nonZeroDivisors
-/
theorem isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x := by
  obtain ⟨d, hd⟩ := h
  have d_ne_zero : algebraMap A K (den A x) != 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul]; rw [map_units_inv]; rw [hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc]; rw [mul_inv_cancel₀ d_ne_zero]; rw [one_mul]; rw [mk'_spec']

/--
theorem `isUnit_den_iff` / 定理 `isUnit_den_iff`

English:
theorem isUnit_den_iff
  given: (x : K)
  statement: IsUnit (den A x : A) ↔ IsLocalization.IsInteger A x where
  proof: isInteger_of_isUnit_den
  mpr h := by
    have ⟨v, h⟩ := h
    apply IsRelPrime.isUnit_of_dvd (num_den_reduced A x).symm
    use v
    apply_fun algebraMap A K
    · simp only [map_mul, h]
      rw [mul_comm]; rw [← div_eq_iff]
      · simp only [mk'_num_den']
      simp
    exact FaithfulSMul.algeb

中文:
定理 isUnit_den_iff
  条件: (x : K)
  结论: IsUnit (den A x : A) ↔ IsLocalization.Is整数eger A x where
  证明: isInteger_of_isUnit_den
  mpr h := by
    have ⟨v, h⟩ := h
    apply IsRelPrime.isUnit_of_dvd (num_den_reduced A x).symm
    use v
    apply_fun algebraMap A K
    · simp only [map_mul, h]
      rw [mul_comm]; rw [← div_eq_iff]
      · simp only [mk'_num_den']
      simp
    exact FaithfulSMul.algeb

Depends on / 依赖: isInteger_of_isUnit_den
-/
theorem isUnit_den_iff (x : K) : IsUnit (den A x : A) ↔ IsLocalization.IsInteger A x where
  mp := isInteger_of_isUnit_den
  mpr h := by
    have ⟨v, h⟩ := h
    apply IsRelPrime.isUnit_of_dvd (num_den_reduced A x).symm
    use v
    apply_fun algebraMap A K
    · simp only [map_mul, h]
      rw [mul_comm]; rw [← div_eq_iff]
      · simp only [mk'_num_den']
      simp
    exact FaithfulSMul.algebraMap_injective A K

/--
theorem `isUnit_den_zero` / 定理 `isUnit_den_zero`

English:
theorem isUnit_den_zero
  statement: IsUnit (den A (0 : K) : A)
  proof: by
  simp [isUnit_den_iff, IsLocalization.isInteger_zero]

中文:
定理 isUnit_den_zero
  结论: IsUnit (den A (0 : K) : A)
  证明: by
  simp [isUnit_den_iff, IsLocalization.isInteger_zero]

Depends on / 依赖: IsLocalization, IsLocalization.isInteger_zero, isInteger_zero, isUnit_den_iff
-/
theorem isUnit_den_zero : IsUnit (den A (0 : K) : A) := by
  simp [isUnit_den_iff, IsLocalization.isInteger_zero]

/--
lemma `associated_den_num_inv` / 引理 `associated_den_num_inv`

English:
lemma associated_den_num_inv
  given: (x : K) (hx : x != 0)
  statement: Associated (den A x : A) (num A x⁻¹)
  proof: associated_of_dvd_dvd
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x).symm <|
dvd_of_mul_left_dvd (a := (den A x⁻¹ : A)) dvd_of_eq
FaithfulSMul.algebraMap_injective A K Eq.symm eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
    (IsRelPrime.dvd_of_dvd_mul_right (Is

中文:
引理 associated_den_num_inv
  条件: (x : K) (hx : x != 0)
  结论: Associated (den A x : A) (num A x⁻¹)
  证明: associated_of_dvd_dvd
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x).symm <|
dvd_of_mul_left_dvd (a := (den A x⁻¹ : A)) dvd_of_eq
FaithfulSMul.algebraMap_injective A K Eq.symm eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
    (IsRelPrime.dvd_of_dvd_mul_right (Is

Depends on / 依赖: Eq.symm, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.num_den_reduced, IsRelPrime, IsRelPrime.dvd_of_dvd_mul_right, algebraMap_injective, associated_of_dvd_dvd, dvd_of_dvd_mul_right, dvd_of_eq, dvd_of_mul_left_dvd, eq_of_div_eq_one, mul_div_mul_comm, num_den_reduced
-/
lemma associated_den_num_inv (x : K) (hx : x != 0) : Associated (den A x : A) (num A x⁻¹) :=
  associated_of_dvd_dvd
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x).symm <|
dvd_of_mul_left_dvd (a := (den A x⁻¹ : A)) dvd_of_eq
FaithfulSMul.algebraMap_injective A K Eq.symm eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x⁻¹) <|
dvd_of_mul_left_dvd (a := (num A x : A)) dvd_of_eq
FaithfulSMul.algebraMap_injective A K eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))

/--
lemma `associated_num_den_inv` / 引理 `associated_num_den_inv`

English:
lemma associated_num_den_inv
  given: (x : K) (hx : x != 0)
  statement: Associated (num A x : A) (den A x⁻¹)
  proof: by
  have : Associated (num A x⁻¹⁻¹ : A) (den A x⁻¹) :=
    (associated_den_num_inv x⁻¹ (inv_ne_zero hx)).symm
  rw [inv_inv] at this
  exact this

中文:
引理 associated_num_den_inv
  条件: (x : K) (hx : x != 0)
  结论: Associated (num A x : A) (den A x⁻¹)
  证明: by
  have : Associated (num A x⁻¹⁻¹ : A) (den A x⁻¹) :=
    (associated_den_num_inv x⁻¹ (inv_ne_zero hx)).symm
  rw [inv_inv] at this
  exact this

Depends on / 依赖: Associated, associated_den_num_inv, inv_inv, inv_ne_zero
-/
lemma associated_num_den_inv (x : K) (hx : x != 0) : Associated (num A x : A) (den A x⁻¹) := by
  have : Associated (num A x⁻¹⁻¹ : A) (den A x⁻¹) :=
    (associated_den_num_inv x⁻¹ (inv_ne_zero hx)).symm
  rw [inv_inv] at this
  exact this

variable (A) in
/--
theorem `num_den_unique` / 定理 `num_den_unique`

English:
theorem num_den_unique
  statement: (x : K) (n : A) (d : nonZeroDivisors A) (pr : IsRelPrime n d)
  proof: by
  rw [← IsFractionRing.mk'_num_den A x]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(FaithfulSMul.algebraMap_injective _ _).eq_iff] at h
  refine ⟨associated_of_dvd_dvd
      ((num_den_reduced A x).dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _)
      (pr.dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _

中文:
定理 num_den_unique
  结论: (x : K) (n : A) (d : nonZeroDivisors A) (pr : IsRelPrime n d)
  证明: by
  rw [← IsFractionRing.mk'_num_den A x]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(FaithfulSMul.algebraMap_injective _ _).eq_iff] at h
  refine ⟨associated_of_dvd_dvd
      ((num_den_reduced A x).dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _)
      (pr.dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.mk, IsLocalization, IsLocalization.mk, _eq_iff_eq, _num_den, algebraMap_injective, associated_of_dvd_dvd, dvd_mul_left, dvd_mul_right, dvd_of_dvd_mul_left, dvd_of_dvd_mul_right, eq_iff, num_den_reduced, pr.dvd_of_dvd_mul_right, pr.symm.dvd_of_dvd_mul_left, symm.dvd_of_dvd_mul_left
-/
theorem num_den_unique (x : K) (n : A) (d : nonZeroDivisors A) (pr : IsRelPrime n d)
    (h : IsLocalization.mk' K n d = x) :
    Associated (num A x) n ∧ Associated (den A x : A) d := by
  rw [← IsFractionRing.mk'_num_den A x]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(FaithfulSMul.algebraMap_injective _ _).eq_iff] at h
  refine ⟨associated_of_dvd_dvd
      ((num_den_reduced A x).dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _)
      (pr.dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _),
    associated_of_dvd_dvd
      ((num_den_reduced A x).symm.dvd_of_dvd_mul_left <| h ▸ dvd_mul_left _ _)
      (pr.symm.dvd_of_dvd_mul_left <| h ▸ dvd_mul_left _ _)⟩


end NumDen

end IsFractionRing
