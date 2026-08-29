/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Submonoid
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

* `IsFractionRing R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
  `IsLocalization (NonZeroDivisors R) K`

## Main results

* `IsFractionRing.field`: a definition (not an instance) stating the localization of an integral
  domain `R` at `R \ {0}` is a field
* `Rat.isFractionRing` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists Ideal

open nonZeroDivisors

variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]
variable {A : Type*} [CommRing A] (K : Type*)

-- TODO: should this extend `Algebra` instead of assuming it?
-- TODO: this was recently generalized from `CommRing` to `CommSemiring`, but all lemmas below are
-- still stated for `CommRing`. Generalize these lemmas where it is appropriate.
/--
Definition of `IsFractionRing` / `IsFractionRing` 的定义

English:
abbreviation IsFractionRing
  signature: (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K]
  body: IsLocalization (nonZeroDivisors R) K

中文:
缩写 IsFractionRing
  签名: (R : 类型) [交换半环 R] (K : 类型) [交换半环 K] [代数 R K]
  定义体: IsLocalization (nonZeroDivisors R) K

Depends on / 依赖: IsLocalization, nonZeroDivisors
-/
abbrev IsFractionRing (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K

instance {R : Type*} [Field R] : IsFractionRing R R :=
  IsLocalization.of_le_isUnit fun _ => isUnit_of_mem_nonZeroDivisors

/--
theorem `IsFractionRing.of_algEquiv` / 定理 `IsFractionRing.of_algEquiv`

English:
theorem IsFractionRing.of_algEquiv
  statement: {R : Type*} [CommSemiring R] {K L : Type*}
  proof: IsLocalization.isLocalization_of_algEquiv _ e

中文:
定理 IsFractionRing.of_algEquiv
  结论: {R : 类型} [交换半环 R] {K L : 类型}
  证明: IsLocalization.isLocalization_of_algEquiv _ e

Depends on / 依赖: IsLocalization, IsLocalization.isLocalization_of_algEquiv, isLocalization_of_algEquiv
-/
theorem IsFractionRing.of_algEquiv {R : Type*} [CommSemiring R] {K L : Type*}
    [CommSemiring K] [Algebra R K] [CommSemiring L] [Algebra R L] [h : IsFractionRing R K]
    (e : K ≃ₐ[R] L) :
    IsFractionRing R L := IsLocalization.isLocalization_of_algEquiv _ e

/--
Instance `Rat.isFractionRing` / 实例 `Rat.isFractionRing`

English:
instance Rat.isFractionRing
  signature: : IsFractionRing Int Rat where
  body: by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]; rw [Int.

中文:
实例 有理数.isFractionRing
  签名: : IsFractionRing 整数 有理数 where
  定义体: by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]; rw [Int.

Depends on / 依赖: Int.cast_eq_zero, Int.cast_inj, Int.natCast_ne_zero_iff_pos, Nat.zero_lt_of_ne_zero, Rat.mul_den_eq_num, Subtype, Subtype.coe_mk, cast_eq_zero, cast_inj, coe_mk, eq_intCast, exists_of_eq, isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero, mul_den_eq_num, natCast_ne_zero_iff_pos, zero_lt_of_ne_zero
-/
instance Rat.isFractionRing : IsFractionRing Int Rat where
  map_units := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]; rw [Int.natCast_ne_zero_iff_pos]
    exact Nat.zero_lt_of_ne_zero hd
  exists_of_eq {x y} := by
    rw [eq_intCast]; rw [eq_intCast]; rw [Int.cast_inj]
    rintro rfl
    use 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (Submonoid.pos Int) Rat
  body: by simpa using y.prop.ne'
  surj z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors Int) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val != 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_

中文:
实例 :
  签名: 是Localization (子幺半群.pos 整数) 有理数
  定义体: by simpa using y.prop.ne'
  surj z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors Int) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val != 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_

Depends on / 依赖: IsLocalization, IsLocalization.surj, Rat.intCast_inj.mp, exists_of_eq, intCast_inj, lt_or_gt_of_ne, nonZeroDivisors, x2.val, y.prop.ne
-/
instance : IsLocalization (Submonoid.pos Int) Rat where
  map_units y := by simpa using y.prop.ne'
  surj z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors Int) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val != 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_eq {x y} h := ⟨1, by simpa using Rat.intCast_inj.mp h⟩

/--
Instance `NNRat.isFractionRing` / 实例 `NNRat.isFractionRing`

English:
instance NNRat.isFractionRing
  signature: : IsFractionRing Nat Rat>=0 where
  body: by simp
  surj z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

中文:
实例 NNRat.isFractionRing
  签名: : IsFractionRing 自然数 有理数>=0 where
  定义体: by simp
  surj z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

Depends on / 依赖: exists_of_eq, z.den, z.num
-/
instance NNRat.isFractionRing : IsFractionRing Nat Rat>=0 where
  map_units y := by simp
  surj z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

namespace IsFractionRing

open IsLocalization

/--
theorem `of_field` / 定理 `of_field`

English:
theorem of_field
  statement: [Field K] [Algebra R K] [FaithfulSMul R K]
  proof: have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K
{ map_units x :=
.mk0 _ (map_ne_zero_iff _ inj).mpr mem_nonZeroDivisors_iff_ne_zero.mp x.2
  surj z := by
    have ⟨x, y, eq⟩ := surj z
    obtain rfl | hy := eq_

中文:
定理 of_field
  结论: [域 K] [代数 R K] [忠实标量乘法 R K]
  证明: have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K
{ map_units x :=
.mk0 _ (map_ne_zero_iff _ inj).mpr mem_nonZeroDivisors_iff_ne_zero.mp x.2
  surj z := by
    have ⟨x, y, eq⟩ := surj z
    obtain rfl | hy := eq_

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Module, Module.nontrivial, algebraMap_injective, eq_div_iff_mul_eq, eq_or_ne, exists_of_eq, inj.noZeroDivisors, map_mul, map_ne_zero_iff, map_units, map_zero, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mem_nonZeroDivisors_iff_ne_zero.mpr, noZeroDivisors, nontrivial
-/
theorem of_field [Field K] [Algebra R K] [FaithfulSMul R K]
    (surj : forall z : K, exists x y, z = algebraMap R K x / algebraMap R K y) :
    IsFractionRing R K :=
  have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K
{ map_units x :=
.mk0 _ (map_ne_zero_iff _ inj).mpr mem_nonZeroDivisors_iff_ne_zero.mp x.2
  surj z := by
    have ⟨x, y, eq⟩ := surj z
    obtain rfl | hy := eq_or_ne y 0
    · obtain rfl : z = 0 := by simpa using eq
      exact ⟨(0, 1), by simp⟩
    exact ⟨⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mpr hy⟩,
      (eq_div_iff_mul_eq <| (map_ne_zero_iff _ inj).mpr hy).mp eq⟩
  exists_of_eq eq := ⟨1, by simpa using inj eq⟩ }

variable {R K}

section CommSemiring

/--
theorem `of_ringEquiv_left` / 定理 `of_ringEquiv_left`

English:
theorem of_ringEquiv_left
  statement: {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
  proof: IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

中文:
定理 of_ringEquiv_left
  结论: {R : 类型} [交换半环 R] {S : 类型} [交换半环 S]
  证明: IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

Depends on / 依赖: IsLocalization, IsLocalization.of_ringEquiv_left, MulEquivClass, MulEquivClass.map_nonZeroDivisors, map_nonZeroDivisors, of_ringEquiv_left
-/
theorem of_ringEquiv_left {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K]
    (h : forall x, algebraMap R K x = algebraMap S K (e x)) [IsFractionRing S K] :
    IsFractionRing R K := IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

end CommSemiring

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

/--
theorem `to_map_eq_zero_iff` / 定理 `to_map_eq_zero_iff`

English:
theorem to_map_eq_zero_iff
  given: {x : R}
  statement: algebraMap R K x = 0 ↔ x = 0
  proof: IsLocalization.to_map_eq_zero_iff _ le_rfl

中文:
定理 to_map_eq_zero_iff
  条件: {x : R}
  结论: algebraMap R K x = 0 ↔ x = 0
  证明: IsLocalization.to_map_eq_zero_iff _ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.to_map_eq_zero_iff, le_rfl, to_map_eq_zero_iff
-/
theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl

variable (R K)

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Function.Injective (algebraMap R K)
  proof: IsLocalization.injective _ (le_of_eq rfl)

include R in

中文:
定理 injective
  结论: 函数.单射 (algebraMap R K)
  证明: IsLocalization.injective _ (le_of_eq rfl)

include R in
-/
protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)

include R in
/--
theorem `nonZeroDivisors_eq_isUnit` / 定理 `nonZeroDivisors_eq_isUnit`

English:
theorem nonZeroDivisors_eq_isUnit
  statement: K⁰ = IsUnit.submonoid K
  proof: by
  refine le_antisymm (fun x hx => ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
exact isUnit_of_mul_isUnit_left eq ▸ map_units K r'

inc

中文:
定理 nonZeroDivisors_eq_isUnit
  结论: K⁰ = 是单位.submonoid K
  证明: by
  refine le_antisymm (fun x hx => ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
exact isUnit_of_mul_isUnit_left eq ▸ map_units K r'

inc

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, injective, isUnit_le_nonZeroDivisors, isUnit_of_mul_isUnit_left, le_antisymm, map_units, mem_nonZeroDivisors, mem_nonZeroDivisors_of_injective, mul_mem
-/
theorem nonZeroDivisors_eq_isUnit : K⁰ = IsUnit.submonoid K := by
  refine le_antisymm (fun x hx => ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
exact isUnit_of_mul_isUnit_left eq ▸ map_units K r'

include R in
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (L) [CommRing L] [Algebra K L] [IsFractionRing K L]
  body: atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in

中文:
定义 algEquiv
  签名: (L) [交换环 L] [代数 K L] [IsFractionRing K L]
  定义体: atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in

Depends on / 依赖: atUnits, nonZeroDivisors_eq_isUnit
-/
noncomputable def algEquiv (L) [CommRing L] [Algebra K L] [IsFractionRing K L] : K ≃ₐ[K] L :=
  atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in
/--
theorem `idem` / 定理 `idem`

English:
theorem idem
  statement: IsFractionRing K K
  proof: IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

中文:
定理 idem
  结论: IsFractionRing K K
  证明: IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

Depends on / 依赖: IsLocalization, IsLocalization.self, nonZeroDivisors_eq_isUnit
-/
theorem idem : IsFractionRing K K := IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
  proof: isLocalization_of_algEquiv _ (algEquiv R K L).restrictScalars R

中文:
定理 trans
  结论: (L) [交换环 L] [代数 K L] [IsFractionRing K L] [代数 R L]
  证明: isLocalization_of_algEquiv _ (algEquiv R K L).restrictScalars R

Depends on / 依赖: algEquiv, isLocalization_of_algEquiv, restrictScalars
-/
theorem trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
    [IsScalarTower R K L] : IsFractionRing R L :=
isLocalization_of_algEquiv _ (algEquiv R K L).restrictScalars R

instance (priority := 100) : FaithfulSMul R K :=
(faithfulSMul_iff_algebraMap_injective R K).mpr IsFractionRing.injective R K

variable {R}

/--
theorem `self_iff_nonZeroDivisors_eq_isUnit` / 定理 `self_iff_nonZeroDivisors_eq_isUnit`

English:
theorem self_iff_nonZeroDivisors_eq_isUnit
  statement: IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where
  proof: nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le

中文:
定理 self_iff_nonZeroDivisors_eq_isUnit
  结论: IsFractionRing R R ↔ R⁰ = 是单位.submonoid R where
  证明: nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le

Depends on / 依赖: nonZeroDivisors_eq_isUnit
-/
theorem self_iff_nonZeroDivisors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where
  mp _ := nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le

/--
theorem `self_iff_nonZeroDivisors_le_isUnit` / 定理 `self_iff_nonZeroDivisors_le_isUnit`

English:
theorem self_iff_nonZeroDivisors_le_isUnit
  statement: IsFractionRing R R ↔ R⁰ <= IsUnit.submonoid R
  proof: by
  rw [self_iff_nonZeroDivisors_eq_isUnit]; rw [le_antisymm_iff]; rw [and_iff_left (isUnit_le_nonZeroDivisors R)]

中文:
定理 self_iff_nonZeroDivisors_le_isUnit
  结论: IsFractionRing R R ↔ R⁰ <= 是单位.submonoid R
  证明: by
  rw [self_iff_nonZeroDivisors_eq_isUnit]; rw [le_antisymm_iff]; rw [and_iff_left (isUnit_le_nonZeroDivisors R)]

Depends on / 依赖: and_iff_left, isUnit_le_nonZeroDivisors, le_antisymm_iff, self_iff_nonZeroDivisors_eq_isUnit
-/
theorem self_iff_nonZeroDivisors_le_isUnit : IsFractionRing R R ↔ R⁰ <= IsUnit.submonoid R := by
  rw [self_iff_nonZeroDivisors_eq_isUnit]; rw [le_antisymm_iff]; rw [and_iff_left (isUnit_le_nonZeroDivisors R)]

/--
theorem `self_iff_bijective` / 定理 `self_iff_bijective`

English:
theorem self_iff_bijective
  statement: IsFractionRing R R ↔ Function.Bijective (algebraMap R K) where
  proof: (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm

中文:
定理 self_iff_bijective
  结论: IsFractionRing R R ↔ 函数.双射 (algebraMap R K) where
  证明: (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm

Depends on / 依赖: atUnits, bijective, self_iff_nonZeroDivisors_le_isUnit, self_iff_nonZeroDivisors_le_isUnit.mp
-/
theorem self_iff_bijective : IsFractionRing R R ↔ Function.Bijective (algebraMap R K) where
  mp h := (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm

/--
theorem `self_iff_surjective` / 定理 `self_iff_surjective`

English:
theorem self_iff_surjective
  statement: IsFractionRing R R ↔ Function.Surjective (algebraMap R K)
  proof: by
  rw [self_iff_bijective K]; rw [Function.Bijective]; rw [and_iff_right (IsFractionRing.injective R K)]

中文:
定理 self_iff_surjective
  结论: IsFractionRing R R ↔ 函数.满射 (algebraMap R K)
  证明: by
  rw [self_iff_bijective K]; rw [Function.Bijective]; rw [and_iff_right (IsFractionRing.injective R K)]

Depends on / 依赖: Bijective, Function, Function.Bijective, IsFractionRing, IsFractionRing.injective, and_iff_right, injective, self_iff_bijective
-/
theorem self_iff_surjective : IsFractionRing R R ↔ Function.Surjective (algebraMap R K) := by
  rw [self_iff_bijective K]; rw [Function.Bijective]; rw [and_iff_right (IsFractionRing.injective R K)]

variable {K}

open algebraMap in
@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : R}
  statement: (↑a : K) = ↑b ↔ a = b
  proof: algebraMap.coe_inj _ _

中文:
定理 coe_inj
  条件: {a b : R}
  结论: (↑a : K) = ↑b ↔ a = b
  证明: algebraMap.coe_inj _ _

Depends on / 依赖: algebraMap, algebraMap.coe_inj, coe_inj
-/
theorem coe_inj {a b : R} : (↑a : K) = ↑b ↔ a = b :=
  algebraMap.coe_inj _ _

/--
theorem `to_map_ne_zero_of_mem_nonZeroDivisors` / 定理 `to_map_ne_zero_of_mem_nonZeroDivisors`

English:
theorem to_map_ne_zero_of_mem_nonZeroDivisors
  statement: [Nontrivial R] {x : R}
  proof: IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx

中文:
定理 to_map_ne_zero_of_mem_nonZeroDivisors
  结论: [非平凡 R] {x : R}
  证明: IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx
-/
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] {x : R}
    (hx : x in nonZeroDivisors R) : algebraMap R K x != 0 :=
  IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx

variable (A) [IsDomain A]

include A in
/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  statement: IsDomain K
  proof: isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))

中文:
定理 isDomain
  结论: 是整环 K
  证明: isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))
-/
protected theorem isDomain : IsDomain K :=
  isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable irreducible_def inv (z : K) : K := open scoped Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
h eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (x : K) (hx : x != 0)
  statement: x * IsFractionRing.inv A x = 1
  proof: by
  rw [IsFractionRing.inv]; rw [dif_neg hx]; rw [←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1]; rw [mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
hx eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩)]; rw [one_mul]; rw [mul_assoc]
  rw [mk'_spec]; rw [← eq_mk'_iff_mul_

中文:
定理 mul_inv_cancel
  条件: (x : K) (hx : x != 0)
  结论: x * IsFractionRing.inv A x = 1
  证明: by
  rw [IsFractionRing.inv]; rw [dif_neg hx]; rw [←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1]; rw [mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
hx eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩)]; rw [one_mul]; rw [mul_assoc]
  rw [mk'_spec]; rw [← eq_mk'_iff_mul_
-/
protected theorem mul_inv_cancel (x : K) (hx : x != 0) : x * IsFractionRing.inv A x = 1 := by
  rw [IsFractionRing.inv]; rw [dif_neg hx]; rw [←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1]; rw [mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
hx eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩)]; rw [one_mul]; rw [mul_assoc]
  rw [mk'_spec]; rw [← eq_mk'_iff_mul_eq]
  exact (mk'_sec _ x).symm

/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[stacks 09FJ]
/--
Definition of `toField` / `toField` 的定义

English:
abbreviation toField
  signature: : Field K where
  body: IsFractionRing.isDomain A
  inv := IsFractionRing.inv A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
缩写 toField
  签名: : 域 K where
  定义体: IsFractionRing.isDomain A
  inv := IsFractionRing.inv A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: IsFractionRing, IsFractionRing.isDomain, isDomain
-/
noncomputable abbrev toField : Field K where
  __ := IsFractionRing.isDomain A
  inv := IsFractionRing.inv A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
lemma `surjective_iff_isField` / 引理 `surjective_iff_isField`

English:
lemma surjective_iff_isField
  given: [IsDomain R]
  statement: Function.Surjective (algebraMap R K) ↔ IsField R where
  proof: (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx => Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective

中文:
引理 surjective_iff_isField
  条件: [是整环 R]
  结论: 函数.满射 (algebraMap R K) ↔ 是域 R where
  证明: (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx => Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, algebraMap, ofBijective
-/
lemma surjective_iff_isField [IsDomain R] : Function.Surjective (algebraMap R K) ↔ IsField R where
  mp h := (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx => Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective

end CommRing

variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A ->+* L}

/--
theorem `mk'_mk_eq_div` / 定理 `mk'_mk_eq_div`

English:
theorem mk'_mk_eq_div
  given: {r s} (hs : s in nonZeroDivisors A)
  proof: haveI := (algebraMap A K).domain_nontrivial
mk'_eq_iff_eq_mul.2
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm

@[simp]

中文:
定理 mk'_mk_eq_div
  条件: {r s} (hs : s in nonZeroDivisors A)
  证明: haveI := (algebraMap A K).domain_nontrivial
mk'_eq_iff_eq_mul.2
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm

@[simp]

Depends on / 依赖: IsFractionRing, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors, _eq_iff_eq_mul, algebraMap, domain_nontrivial, to_map_ne_zero_of_mem_nonZeroDivisors
-/
theorem mk'_mk_eq_div {r s} (hs : s in nonZeroDivisors A) :
    mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  haveI := (algebraMap A K).domain_nontrivial
mk'_eq_iff_eq_mul.2
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm

@[simp]
/--
theorem `mk'_eq_div` / 定理 `mk'_eq_div`

English:
theorem mk'_eq_div
  given: {r} (s : nonZeroDivisors A)
  statement: mk' K r s = algebraMap A K r / algebraMap A K s
  proof: mk'_mk_eq_div s.2

中文:
定理 mk'_eq_div
  条件: {r} (s : nonZeroDivisors A)
  结论: mk' K r s = algebraMap A K r / algebraMap A K s
  证明: mk'_mk_eq_div s.2
-/
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2

variable (A) in
/--
theorem `div_surjective` / 定理 `div_surjective`

English:
theorem div_surjective
  given: (z : K)
  proof: let ⟨x, ⟨y, hy⟩, h⟩ := exists_mk'_eq (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩

中文:
定理 div_surjective
  条件: (z : K)
  证明: let ⟨x, ⟨y, hy⟩, h⟩ := exists_mk'_eq (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩

Depends on / 依赖: _eq_div, exists_mk, nonZeroDivisors
-/
theorem div_surjective (z : K) :
    exists x y : A, y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := exists_mk'_eq (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩

/--
theorem `isUnit_map_of_injective` / 定理 `isUnit_map_of_injective`

English:
theorem isUnit_map_of_injective
  given: (hg : Function.Injective g) (y : nonZeroDivisors A)
  proof: haveI := g.domain_nontrivial
IsUnit.mk0 (g y)
    show g.toMonoidWithZeroHom y != 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2

中文:
定理 isUnit_map_of_injective
  条件: (hg : 函数.单射 g) (y : nonZeroDivisors A)
  证明: haveI := g.domain_nontrivial
IsUnit.mk0 (g y)
    show g.toMonoidWithZeroHom y != 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2

Depends on / 依赖: IsUnit, IsUnit.mk0, domain_nontrivial, g.domain_nontrivial, g.toMonoidWithZeroHom, map_ne_zero_of_mem_nonZeroDivisors, toMonoidWithZeroHom
-/
theorem isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) :
    IsUnit (g y) :=
  haveI := g.domain_nontrivial
IsUnit.mk0 (g y)
    show g.toMonoidWithZeroHom y != 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2

/--
theorem `mk'_eq_zero_iff_eq_zero` / 定理 `mk'_eq_zero_iff_eq_zero`

English:
theorem mk'_eq_zero_iff_eq_zero
  given: [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R}
  proof: by
  have := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]

中文:
定理 mk'_eq_zero_iff_eq_zero
  条件: [代数 R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R}
  证明: by
  have := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]
-/
theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  have := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]

/--
theorem `mk'_eq_one_iff_eq` / 定理 `mk'_eq_one_iff_eq`

English:
theorem mk'_eq_one_iff_eq
  given: {x : A} {y : nonZeroDivisors A}
  statement: mk' K x y = 1 ↔ x = y
  proof: by
  have := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y != (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div]; rw [div_eq_one_iff_eq hy] at hxy
  exact Is

中文:
定理 mk'_eq_one_iff_eq
  条件: {x : A} {y : nonZeroDivisors A}
  结论: mk' K x y = 1 ↔ x = y
  证明: by
  have := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y != (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div]; rw [div_eq_one_iff_eq hy] at hxy
  exact Is
-/
theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  have := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y != (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div]; rw [div_eq_one_iff_eq hy] at hxy
  exact IsFractionRing.injective A K hxy

/--
theorem `of_algHom` / 定理 `of_algHom`

English:
theorem of_algHom
  given: [Algebra A L] (f : L ->ₐ[A] K)
  statement: IsFractionRing A L
  proof: by
refine IsFractionRing.of_algEquiv .symm .ofBijective f ⟨f.injective, fun x => ?_⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A x
  exact ⟨algebraMap A L x / algebraMap A L y, by simp⟩

中文:
定理 of_algHom
  条件: [代数 A L] (f : L ->ₐ[A] K)
  结论: IsFractionRing A L
  证明: by
refine IsFractionRing.of_algEquiv .symm .ofBijective f ⟨f.injective, fun x => ?_⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A x
  exact ⟨algebraMap A L x / algebraMap A L y, by simp⟩

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, IsFractionRing.of_algEquiv, algebraMap, div_surjective, f.injective, injective, ofBijective, of_algEquiv
-/
theorem of_algHom [Algebra A L] (f : L ->ₐ[A] K) : IsFractionRing A L := by
refine IsFractionRing.of_algEquiv .symm .ofBijective f ⟨f.injective, fun x => ?_⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A x
  exact ⟨algebraMap A L x / algebraMap A L y, by simp⟩

section commutes

variable [Algebra A B] {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra A K₁] [Algebra A K₂]
  [IsFractionRing A K₁] {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra B L₁] [Algebra B L₂]
  [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra A L₁] [Algebra A L₂] [IsScalarTower A K₁ L₁]
  [IsScalarTower A K₂ L₂] [IsScalarTower A B L₁] [IsScalarTower A B L₂]

omit [IsDomain B]

/--
theorem `algHom_commutes` / 定理 `algHom_commutes`

English:
theorem algHom_commutes
  given: (e : K₁ ->ₐ[A] K₂) (f : L₁ ->ₐ[B] L₂) (x : K₁)
  proof: by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  simp_rw [map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L₁, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

中文:
定理 algHom_commutes
  条件: (e : K₁ ->ₐ[A] K₂) (f : L₁ ->ₐ[B] L₂) (x : K₁)
  证明: by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  simp_rw [map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L₁, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

Depends on / 依赖: AlgHom, AlgHom.commutes, IsFractionRing, IsFractionRing.div_surjective, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, commutes, div_surjective, simp_rw
-/
theorem algHom_commutes (e : K₁ ->ₐ[A] K₂) (f : L₁ ->ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  simp_rw [map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L₁, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/--
theorem `algEquiv_commutes` / 定理 `algEquiv_commutes`

English:
theorem algEquiv_commutes
  given: (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁)
  proof: by
  exact algHom_commutes e.toAlgHom f.toAlgHom _

中文:
定理 algEquiv_commutes
  条件: (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁)
  证明: by
  exact algHom_commutes e.toAlgHom f.toAlgHom _

Depends on / 依赖: algHom_commutes, e.toAlgHom, f.toAlgHom, toAlgHom
-/
theorem algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  exact algHom_commutes e.toAlgHom f.toAlgHom _

end commutes

section Subfield

variable (A K) in
/--
theorem `closure_range_algebraMap` / 定理 `closure_range_algebraMap`

English:
theorem closure_range_algebraMap
  statement: Subfield.closure (Set.range (algebraMap A K)) = ⊤
  proof: top_unique fun z _ => by
    obtain ⟨_, _, -, rfl⟩ := div_surjective A z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

中文:
定理 closure_range_algebraMap
  结论: 子域.closure (集合.range (algebraMap A K)) = ⊤
  证明: top_unique fun z _ => by
    obtain ⟨_, _, -, rfl⟩ := div_surjective A z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

Depends on / 依赖: Subfield, Subfield.subset_closure, div_mem, div_surjective, subset_closure, top_unique
-/
theorem closure_range_algebraMap : Subfield.closure (Set.range (algebraMap A K)) = ⊤ :=
  top_unique fun z _ => by
    obtain ⟨_, _, -, rfl⟩ := div_surjective A z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

variable {L : Type*} [Field L] {g : A ->+* L} {f : K ->+* L}

/--
theorem `ringHom_fieldRange_eq_of_comp_eq` / 定理 `ringHom_fieldRange_eq_of_comp_eq`

English:
theorem ringHom_fieldRange_eq_of_comp_eq
  given: (h : RingHom.comp f (algebraMap A K) = g)
  proof: by
  rw [f.fieldRange_eq_map]; rw [← closure_range_algebraMap A K]; rw [f.map_field_closure]; rw [← Set.range_comp]; rw [← f.coe_comp]; rw [h]; rw [g.coe_range]

中文:
定理 ringHom_fieldRange_eq_of_comp_eq
  条件: (h : 环态射.comp f (algebraMap A K) = g)
  证明: by
  rw [f.fieldRange_eq_map]; rw [← closure_range_algebraMap A K]; rw [f.map_field_closure]; rw [← Set.range_comp]; rw [← f.coe_comp]; rw [h]; rw [g.coe_range]

Depends on / 依赖: Set.range_comp, closure_range_algebraMap, coe_comp, coe_range, f.coe_comp, f.fieldRange_eq_map, f.map_field_closure, fieldRange_eq_map, g.coe_range, map_field_closure, range_comp
-/
theorem ringHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = g) :
    f.fieldRange = Subfield.closure g.range := by
  rw [f.fieldRange_eq_map]; rw [← closure_range_algebraMap A K]; rw [f.map_field_closure]; rw [← Set.range_comp]; rw [← f.coe_comp]; rw [h]; rw [g.coe_range]

/--
theorem `ringHom_fieldRange_eq_of_comp_eq_of_range_eq` / 定理 `ringHom_fieldRange_eq_of_comp_eq_of_range_eq`

English:
theorem ringHom_fieldRange_eq_of_comp_eq_of_range_eq
  statement: (h : RingHom.comp f (algebraMap A K) = g)
  proof: by
  rw [ringHom_fieldRange_eq_of_comp_eq h]; rw [hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]

中文:
定理 ringHom_fieldRange_eq_of_comp_eq_of_range_eq
  结论: (h : 环态射.comp f (algebraMap A K) = g)
  证明: by
  rw [ringHom_fieldRange_eq_of_comp_eq h]; rw [hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]

Depends on / 依赖: Subfield, Subfield.mem_closure_iff, Subring, Subring.closure_eq, closure_eq, mem_closure_iff, ringHom_fieldRange_eq_of_comp_eq, simp_rw
-/
theorem ringHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g)
    {s : Set L} (hs : g.range = Subring.closure s) : f.fieldRange = Subfield.closure s := by
  rw [ringHom_fieldRange_eq_of_comp_eq h]; rw [hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]

end Subfield

open Function

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (hg : Injective g)
  body: IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

中文:
定义 lift
  签名: (hg : 单射 g)
  定义体: IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

Depends on / 依赖: IsLocalization, IsLocalization.lift, isUnit_map_of_injective, nonZeroDivisors
-/
noncomputable def lift (hg : Injective g) : K ->+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (hg : Function.Injective g) {f : K ->+* L}
  proof: IsLocalization.lift_unique _ hf1

中文:
定理 lift_unique
  结论: (hg : 函数.单射 g) {f : K ->+* L}
  证明: IsLocalization.lift_unique _ hf1

Depends on / 依赖: IsLocalization, IsLocalization.lift_unique, lift_unique
-/
theorem lift_unique (hg : Function.Injective g) {f : K ->+* L}
    (hf1 : forall x, f (algebraMap A K x) = g x) : IsFractionRing.lift hg = f :=
  IsLocalization.lift_unique _ hf1

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  statement: {f1 f2 : K ->+* L}
  proof: by
  ext z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀]; rw [map_div₀]; rw [hf]; rw [hf]

中文:
定理 ringHom_ext
  结论: {f1 f2 : K ->+* L}
  证明: by
  ext z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀]; rw [map_div₀]; rw [hf]; rw [hf]

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, div_surjective
-/
theorem ringHom_ext {f1 f2 : K ->+* L}
    (hf : forall x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)) : f1 = f2 := by
  ext z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀]; rw [map_div₀]; rw [hf]; rw [hf]

/--
theorem `injective_comp_algebraMap` / 定理 `injective_comp_algebraMap`

English:
theorem injective_comp_algebraMap
  proof: fun _ _ h => ringHom_ext (fun x => RingHom.congr_fun h x)

中文:
定理 injective_comp_algebraMap
  证明: fun _ _ h => ringHom_ext (fun x => RingHom.congr_fun h x)

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun, ringHom_ext
-/
theorem injective_comp_algebraMap :
    Function.Injective fun (f : K ->+* L) => f.comp (algebraMap A K) :=
  fun _ _ h => ringHom_ext (fun x => RingHom.congr_fun h x)

section liftAlgHom

variable [Algebra R A] [Algebra R K] [IsScalarTower R A K] [Algebra R L]
  {g : A ->ₐ[R] L} (hg : Injective g) (x : K)
include hg

/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: : K ->ₐ[R] L
  body: IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

中文:
定义 liftAlgHom
  签名: : K ->ₐ[R] L
  定义体: IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

Depends on / 依赖: IsLocalization, IsLocalization.liftAlgHom, isUnit_map_of_injective, liftAlgHom, nonZeroDivisors
-/
noncomputable def liftAlgHom : K ->ₐ[R] L :=
  IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

/--
theorem `liftAlgHom_toRingHom` / 定理 `liftAlgHom_toRingHom`

English:
theorem liftAlgHom_toRingHom
  statement: (liftAlgHom hg : K ->ₐ[R] L).toRingHom = lift hg
  proof: rfl

@[simp]

中文:
定理 liftAlgHom_toRingHom
  结论: (liftAlgHom hg : K ->ₐ[R] L).toRingHom = lift hg
  证明: rfl

@[simp]
-/
theorem liftAlgHom_toRingHom : (liftAlgHom hg : K ->ₐ[R] L).toRingHom = lift hg := rfl

@[simp]
/--
theorem `coe_liftAlgHom` / 定理 `coe_liftAlgHom`

English:
theorem coe_liftAlgHom
  statement: ⇑(liftAlgHom hg : K ->ₐ[R] L) = lift hg
  proof: rfl

中文:
定理 coe_liftAlgHom
  结论: ⇑(liftAlgHom hg : K ->ₐ[R] L) = lift hg
  证明: rfl
-/
theorem coe_liftAlgHom : ⇑(liftAlgHom hg : K ->ₐ[R] L) = lift hg := rfl

/--
theorem `liftAlgHom_apply` / 定理 `liftAlgHom_apply`

English:
theorem liftAlgHom_apply
  statement: liftAlgHom hg x = lift hg x
  proof: rfl

中文:
定理 liftAlgHom_apply
  结论: liftAlgHom hg x = lift hg x
  证明: rfl
-/
theorem liftAlgHom_apply : liftAlgHom hg x = lift hg x := rfl

end liftAlgHom

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
/--
theorem `lift_algebraMap` / 定理 `lift_algebraMap`

English:
theorem lift_algebraMap
  given: (hg : Injective g) (x)
  statement: lift hg (algebraMap A K x) = g x
  proof: lift_eq _ _

中文:
定理 lift_algebraMap
  条件: (hg : 单射 g) (x)
  结论: lift hg (algebraMap A K x) = g x
  证明: lift_eq _ _

Depends on / 依赖: lift_eq
-/
theorem lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _

/--
theorem `lift_fieldRange` / 定理 `lift_fieldRange`

English:
theorem lift_fieldRange
  given: (hg : Injective g)
  proof: ringHom_fieldRange_eq_of_comp_eq (by ext; simp)

中文:
定理 lift_fieldRange
  条件: (hg : 单射 g)
  证明: ringHom_fieldRange_eq_of_comp_eq (by ext; simp)

Depends on / 依赖: ringHom_fieldRange_eq_of_comp_eq
-/
theorem lift_fieldRange (hg : Injective g) :
    (lift hg : K ->+* L).fieldRange = Subfield.closure g.range :=
  ringHom_fieldRange_eq_of_comp_eq (by ext; simp)

/--
theorem `lift_fieldRange_eq_of_range_eq` / 定理 `lift_fieldRange_eq_of_range_eq`

English:
theorem lift_fieldRange_eq_of_range_eq
  statement: (hg : Injective g)
  proof: ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

中文:
定理 lift_fieldRange_eq_of_range_eq
  结论: (hg : 单射 g)
  证明: ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

Depends on / 依赖: ringHom_fieldRange_eq_of_comp_eq_of_range_eq
-/
theorem lift_fieldRange_eq_of_range_eq (hg : Injective g)
    {s : Set L} (hs : g.range = Subring.closure s) :
    (lift hg : K ->+* L).fieldRange = Subfield.closure s :=
  ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

/--
theorem `lift_mk'` / 定理 `lift_mk'`

English:
theorem lift_mk'
  given: (hg : Injective g) (x) (y : nonZeroDivisors A)
  proof: by simp only [mk'_eq_div, map_div₀, lift_algebraMap]

中文:
定理 lift_mk'
  条件: (hg : 单射 g) (x) (y : nonZeroDivisors A)
  证明: by simp only [mk'_eq_div, map_div₀, lift_algebraMap]

Depends on / 依赖: _eq_div, lift_algebraMap
-/
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) :
    lift hg (mk' K x y) = g x / g y := by simp only [mk'_eq_div, map_div₀, lift_algebraMap]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
  body: IsLocalization.map L j
    (show nonZeroDivisors A <= (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)

中文:
定义 map
  签名: {A B K L : 类型} [交换环 A] [交换环 B] [是整环 B] [交换环 K]
  定义体: IsLocalization.map L j
    (show nonZeroDivisors A <= (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)

Depends on / 依赖: IsLocalization, IsLocalization.map, nonZeroDivisors, nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
noncomputable def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A ->+* B}
    (hj : Injective j) : K ->+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A <= (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)

section ringEquivOfRingEquiv

variable {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  (h : A ≃+* B)

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces an isomorphism of
fraction rings `K ≃+* L`. -/
@[simps! apply]
/--
Definition of `ringEquivOfRingEquiv` / `ringEquivOfRingEquiv` 的定义

English:
definition ringEquivOfRingEquiv
  signature: : K ≃+* L
  body: IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

中文:
定义 ringEquivOfRingEquiv
  签名: : K ≃+* L
  定义体: IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

Depends on / 依赖: IsLocalization, IsLocalization.ringEquivOfRingEquiv, MulEquivClass, MulEquivClass.map_nonZeroDivisors, map_nonZeroDivisors, ringEquivOfRingEquiv
-/
noncomputable def ringEquivOfRingEquiv : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ringEquivOfRingEquiv_algebraMap` / 引理 `ringEquivOfRingEquiv_algebraMap`

English:
lemma ringEquivOfRingEquiv_algebraMap
  proof: by
  simp

@[simp]

中文:
引理 ringEquivOfRingEquiv_algebraMap
  证明: by
  simp

@[simp]
-/
lemma ringEquivOfRingEquiv_algebraMap
    (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp

@[simp]
/--
lemma `ringEquivOfRingEquiv_refl` / 引理 `ringEquivOfRingEquiv_refl`

English:
lemma ringEquivOfRingEquiv_refl
  proof: by ext; simp

@[simp]

中文:
引理 ringEquivOfRingEquiv_refl
  证明: by ext; simp

@[simp]
-/
lemma ringEquivOfRingEquiv_refl :
    ringEquivOfRingEquiv (.refl A) = .refl K := by ext; simp

@[simp]
/--
lemma `ringEquivOfRingEquiv_symm` / 引理 `ringEquivOfRingEquiv_symm`

English:
lemma ringEquivOfRingEquiv_symm
  proof: rfl

中文:
引理 ringEquivOfRingEquiv_symm
  证明: rfl
-/
lemma ringEquivOfRingEquiv_symm :
    (ringEquivOfRingEquiv h : K ≃+* L).symm = ringEquivOfRingEquiv h.symm := rfl

variable (K L) in
/--
theorem `ringEquivOfRingEquiv_comp` / 定理 `ringEquivOfRingEquiv_comp`

English:
theorem ringEquivOfRingEquiv_comp
  statement: {C : Type*} (M : Type*) [CommRing C]
  proof: by
  ext a
  simp [IsLocalization.map_map]

中文:
定理 ringEquivOfRingEquiv_comp
  结论: {C : 类型} (M : 类型) [交换环 C]
  证明: by
  ext a
  simp [IsLocalization.map_map]

Depends on / 依赖: IsLocalization, IsLocalization.map_map, map_map, ringEquivOfRingEquiv
-/
theorem ringEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C]
  [CommRing M] [Algebra C M] [IsFractionRing C M] (f : A ≃+* B) (g : B ≃+* C) :
  (ringEquivOfRingEquiv (f.trans g)) =
    (ringEquivOfRingEquiv (K := K) f).trans (ringEquivOfRingEquiv (K := L) (L := M) g) := by
  ext a
  simp [IsLocalization.map_map]

variable (A K)

/--
Definition of `ringEquivOfRingEquivHom` / `ringEquivOfRingEquivHom` 的定义

English:
definition ringEquivOfRingEquivHom
  signature: : (A ≃+* A) ->* (K ≃+* K) where
  body: ringEquivOfRingEquiv
  map_one' := ringEquivOfRingEquiv_refl
  map_mul' f g := ringEquivOfRingEquiv_comp K K K g f

@[simp]

中文:
定义 ringEquivOfRingEquivHom
  签名: : (A ≃+* A) ->* (K ≃+* K) where
  定义体: ringEquivOfRingEquiv
  map_one' := ringEquivOfRingEquiv_refl
  map_mul' f g := ringEquivOfRingEquiv_comp K K K g f

@[simp]

Depends on / 依赖: ringEquivOfRingEquiv
-/
noncomputable def ringEquivOfRingEquivHom : (A ≃+* A) ->* (K ≃+* K) where
  toFun := ringEquivOfRingEquiv
  map_one' := ringEquivOfRingEquiv_refl
  map_mul' f g := ringEquivOfRingEquiv_comp K K K g f

@[simp]
/--
lemma `ringEquivOfRingEquivHom_apply` / 引理 `ringEquivOfRingEquivHom_apply`

English:
lemma ringEquivOfRingEquivHom_apply
  given: (f : A ≃+* A)
  proof: rfl

中文:
引理 ringEquivOfRingEquivHom_apply
  条件: (f : A ≃+* A)
  证明: rfl
-/
lemma ringEquivOfRingEquivHom_apply (f : A ≃+* A) :
    ringEquivOfRingEquivHom A K f = ringEquivOfRingEquiv f :=
  rfl

/--
lemma `ringEquivOfRingEquivHom_injective` / 引理 `ringEquivOfRingEquivHom_injective`

English:
lemma ringEquivOfRingEquivHom_injective
  statement: Function.Injective (ringEquivOfRingEquivHom A K)
  proof: by
  intro f g h
  ext b
  simpa using RingEquiv.ext_iff.mp h (algebraMap A K b)

中文:
引理 ringEquivOfRingEquivHom_injective
  结论: 函数.单射 (ringEquivOfRingEquivHom A K)
  证明: by
  intro f g h
  ext b
  simpa using RingEquiv.ext_iff.mp h (algebraMap A K b)

Depends on / 依赖: RingEquiv, RingEquiv.ext_iff.mp, algebraMap, ext_iff
-/
lemma ringEquivOfRingEquivHom_injective : Function.Injective (ringEquivOfRingEquivHom A K) := by
  intro f g h
  ext b
  simpa using RingEquiv.ext_iff.mp h (algebraMap A K b)

end ringEquivOfRingEquiv

section semilinearEquivOfRingEquiv

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] (f : A ≃+* B)

local instance : RingHomInvPair (f : A ->+* B) f.symm :=
  RingHomInvPair.of_ringEquiv f

/--
Definition of `semilinearEquivOfRingEquiv` / `semilinearEquivOfRingEquiv` 的定义

English:
definition semilinearEquivOfRingEquiv
  signature: : K ≃ₛₗ[(f : A ->+* B)] L
  body: { ringEquivOfRingEquiv f with
  map_smul' r x := by simp [Algebra.smul_def] }

中文:
定义 semilinearEquivOfRingEquiv
  签名: : K ≃ₛₗ[(f : A ->+* B)] L
  定义体: { ringEquivOfRingEquiv f with
  map_smul' r x := by simp [Algebra.smul_def] }

Depends on / 依赖: Algebra, Algebra.smul_def, map_smul, ringEquivOfRingEquiv, smul_def
-/
noncomputable def semilinearEquivOfRingEquiv : K ≃ₛₗ[(f : A ->+* B)] L :=
{ ringEquivOfRingEquiv f with
  map_smul' r x := by simp [Algebra.smul_def] }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `semilinearEquivOfRingEquiv_apply` / 引理 `semilinearEquivOfRingEquiv_apply`

English:
lemma semilinearEquivOfRingEquiv_apply
  given: (x : K)
  proof: rfl

中文:
引理 semilinearEquivOfRingEquiv_apply
  条件: (x : K)
  证明: rfl
-/
lemma semilinearEquivOfRingEquiv_apply (x : K) :
    (semilinearEquivOfRingEquiv K L f) x = (ringEquivOfRingEquiv f) x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `semilinearEquivOfRingEquiv_algebraMap` / 引理 `semilinearEquivOfRingEquiv_algebraMap`

English:
lemma semilinearEquivOfRingEquiv_algebraMap
  given: (a : A)
  proof: by
  simp [semilinearEquivOfRingEquiv, ringEquivOfRingEquiv]

中文:
引理 semilinearEquivOfRingEquiv_algebraMap
  条件: (a : A)
  证明: by
  simp [semilinearEquivOfRingEquiv, ringEquivOfRingEquiv]

Depends on / 依赖: ringEquivOfRingEquiv, semilinearEquivOfRingEquiv
-/
lemma semilinearEquivOfRingEquiv_algebraMap (a : A) :
    semilinearEquivOfRingEquiv K L f (algebraMap A K a) = algebraMap B L (f a) := by
  simp [semilinearEquivOfRingEquiv, ringEquivOfRingEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `semilinearEquivOfRingEquiv_symm_apply` / 引理 `semilinearEquivOfRingEquiv_symm_apply`

English:
lemma semilinearEquivOfRingEquiv_symm_apply
  given: (x : L)
  proof: rfl

中文:
引理 semilinearEquivOfRingEquiv_symm_apply
  条件: (x : L)
  证明: rfl
-/
lemma semilinearEquivOfRingEquiv_symm_apply (x : L) :
    (semilinearEquivOfRingEquiv K L f).symm x = (ringEquivOfRingEquiv f).symm x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `semilinearEquivOfRingEquiv_comp` / 引理 `semilinearEquivOfRingEquiv_comp`

English:
lemma semilinearEquivOfRingEquiv_comp
  statement: {C : Type*} (M : Type*) [CommRing C] [CommRing M]
  proof: ⟨rfl⟩
    let : RingHomCompTriple g.symm (f.symm : B ->+* A) ((f.trans g).symm : C ->+* A) := ⟨rfl⟩
    (semilinearEquivOfRingEquiv K M (f.trans g)) =
      LinearEquiv.trans (σ₁₃ := (f.trans g)) (σ₃₁ := (f.trans g).symm)
      (semilinearEquivOfRingEquiv K L f)
      (semilinearEquivOfRingEquiv L M

中文:
引理 semilinearEquivOfRingEquiv_comp
  结论: {C : 类型} (M : 类型) [交换环 C] [交换环 M]
  证明: ⟨rfl⟩
    let : RingHomCompTriple g.symm (f.symm : B ->+* A) ((f.trans g).symm : C ->+* A) := ⟨rfl⟩
    (semilinearEquivOfRingEquiv K M (f.trans g)) =
      LinearEquiv.trans (σ₁₃ := (f.trans g)) (σ₃₁ := (f.trans g).symm)
      (semilinearEquivOfRingEquiv K L f)
      (semilinearEquivOfRingEquiv L M
-/
lemma semilinearEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C] [CommRing M]
    [Algebra C M] [IsFractionRing C M] (g : B ≃+* C) :
    let : RingHomCompTriple f (g : B ->+* C) (f.trans g : A ->+* C) := ⟨rfl⟩
    let : RingHomCompTriple g.symm (f.symm : B ->+* A) ((f.trans g).symm : C ->+* A) := ⟨rfl⟩
    (semilinearEquivOfRingEquiv K M (f.trans g)) =
      LinearEquiv.trans (σ₁₃ := (f.trans g)) (σ₃₁ := (f.trans g).symm)
      (semilinearEquivOfRingEquiv K L f)
      (semilinearEquivOfRingEquiv L M g) := by
  ext a
  simp [-RingEquiv.coe_ringHom_trans, semilinearEquivOfRingEquiv_apply,
    semilinearEquivOfRingEquiv_apply K M, ringEquivOfRingEquiv_comp K L M]

end semilinearEquivOfRingEquiv

section algEquivOfAlgEquiv

variable {R A K B L : Type*} [CommSemiring R] [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra R A] [Algebra R K] [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (h : A ≃ₐ[R] B)

/--
Definition of `algEquivOfAlgEquiv` / `algEquivOfAlgEquiv` 的定义

English:
definition algEquivOfAlgEquiv
  signature: : K ≃ₐ[R] L
  body: IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

中文:
定义 algEquivOfAlgEquiv
  签名: : K ≃ₐ[R] L
  定义体: IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

Depends on / 依赖: IsLocalization, IsLocalization.algEquivOfAlgEquiv, MulEquivClass, MulEquivClass.map_nonZeroDivisors, algEquivOfAlgEquiv, map_nonZeroDivisors
-/
noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=
  IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `algEquivOfAlgEquiv_algebraMap` / 引理 `algEquivOfAlgEquiv_algebraMap`

English:
lemma algEquivOfAlgEquiv_algebraMap
  proof: by
  simp [algEquivOfAlgEquiv]

@[simp]

中文:
引理 algEquivOfAlgEquiv_algebraMap
  证明: by
  simp [algEquivOfAlgEquiv]

@[simp]

Depends on / 依赖: algEquivOfAlgEquiv
-/
lemma algEquivOfAlgEquiv_algebraMap
    (a : A) : algEquivOfAlgEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp [algEquivOfAlgEquiv]

@[simp]
/--
lemma `algEquivOfAlgEquiv_symm` / 引理 `algEquivOfAlgEquiv_symm`

English:
lemma algEquivOfAlgEquiv_symm
  proof: rfl

中文:
引理 algEquivOfAlgEquiv_symm
  证明: rfl
-/
lemma algEquivOfAlgEquiv_symm :
    (algEquivOfAlgEquiv h : K ≃ₐ[R] L).symm = algEquivOfAlgEquiv h.symm := rfl

end algEquivOfAlgEquiv

section fieldEquivOfAlgEquiv

variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  (FA FB FC FD : Type*) [Field FA] [Field FB] [Field FC] [Field FD]
  [Algebra A FA] [Algebra B FB] [Algebra C FC] [Algebra D FD]
  [IsFractionRing A FA] [IsFractionRing B FB] [IsFractionRing C FC] [IsFractionRing D FD]
  [Algebra A FB] [IsScalarTower A B FB]
  [Algebra A FC] [IsScalarTower A C FC]
  [Algebra A FD] [IsScalarTower A D FD]
  [Algebra FA FB] [IsScalarTower A FA FB]
  [Algebra FA FC] [IsScalarTower A FA FC]
  [Algebra FA FD] [IsScalarTower A FA FD]

/--
Definition of `fieldEquivOfAlgEquiv` / `fieldEquivOfAlgEquiv` 的定义

English:
definition fieldEquivOfAlgEquiv
  signature: (f : B ≃ₐ[A] C)
  body: IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective A x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]

中文:
定义 fieldEquivOfAlgEquiv
  签名: (f : B ≃ₐ[A] C)
  定义体: IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective A x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]

Depends on / 依赖: IsFractionRing, IsFractionRing.ringEquivOfRingEquiv, f.toRingEquiv, ringEquivOfRingEquiv, toRingEquiv
-/
noncomputable def fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : FB ≃ₐ[FA] FC where
  __ := IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective A x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]

/--
lemma `restrictScalars_fieldEquivOfAlgEquiv` / 引理 `restrictScalars_fieldEquivOfAlgEquiv`

English:
lemma restrictScalars_fieldEquivOfAlgEquiv
  given: (f : B ≃ₐ[A] C)
  proof: by
  ext; rfl

中文:
引理 restrictScalars_fieldEquivOfAlgEquiv
  条件: (f : B ≃ₐ[A] C)
  证明: by
  ext; rfl
-/
lemma restrictScalars_fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) :
    (fieldEquivOfAlgEquiv FA FB FC f).restrictScalars A = algEquivOfAlgEquiv f := by
  ext; rfl

/-- This says that `fieldEquivOfAlgEquiv f` is an extension of `f` (i.e., it agrees with `f` on
`B`). Whereas `(fieldEquivOfAlgEquiv f).commutes` says that `fieldEquivOfAlgEquiv f` fixes `K`. -/
@[simp]
/--
lemma `fieldEquivOfAlgEquiv_algebraMap` / 引理 `fieldEquivOfAlgEquiv_algebraMap`

English:
lemma fieldEquivOfAlgEquiv_algebraMap
  given: (f : B ≃ₐ[A] C) (b : B)
  proof: ringEquivOfRingEquiv_algebraMap f.toRingEquiv b

中文:
引理 fieldEquivOfAlgEquiv_algebraMap
  条件: (f : B ≃ₐ[A] C) (b : B)
  证明: ringEquivOfRingEquiv_algebraMap f.toRingEquiv b

Depends on / 依赖: f.toRingEquiv, ringEquivOfRingEquiv_algebraMap, toRingEquiv
-/
lemma fieldEquivOfAlgEquiv_algebraMap (f : B ≃ₐ[A] C) (b : B) :
    fieldEquivOfAlgEquiv FA FB FC f (algebraMap B FB b) = algebraMap C FC (f b) :=
  ringEquivOfRingEquiv_algebraMap f.toRingEquiv b

variable (A B) in
@[simp]
/--
lemma `fieldEquivOfAlgEquiv_refl` / 引理 `fieldEquivOfAlgEquiv_refl`

English:
lemma fieldEquivOfAlgEquiv_refl
  proof: by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

中文:
引理 fieldEquivOfAlgEquiv_refl
  证明: by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, div_surjective
-/
lemma fieldEquivOfAlgEquiv_refl :
    fieldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl : B ≃ₐ[A] B) = AlgEquiv.refl := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

/--
lemma `fieldEquivOfAlgEquiv_trans` / 引理 `fieldEquivOfAlgEquiv_trans`

English:
lemma fieldEquivOfAlgEquiv_trans
  given: (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D)
  proof: by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

中文:
引理 fieldEquivOfAlgEquiv_trans
  条件: (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D)
  证明: by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, div_surjective
-/
lemma fieldEquivOfAlgEquiv_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) :
    fieldEquivOfAlgEquiv FA FB FD (f.trans g) =
      (fieldEquivOfAlgEquiv FA FB FC f).trans (fieldEquivOfAlgEquiv FA FC FD g) := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

end fieldEquivOfAlgEquiv

section fieldEquivOfAlgEquivHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]

/--
Definition of `fieldEquivOfAlgEquivHom` / `fieldEquivOfAlgEquivHom` 的定义

English:
definition fieldEquivOfAlgEquivHom
  signature: : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L) where
  body: fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f

@[simp]

中文:
定义 fieldEquivOfAlgEquivHom
  签名: : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L) where
  定义体: fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f

@[simp]

Depends on / 依赖: fieldEquivOfAlgEquiv
-/
noncomputable def fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L) where
  toFun := fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f

@[simp]
/--
lemma `fieldEquivOfAlgEquivHom_apply` / 引理 `fieldEquivOfAlgEquivHom_apply`

English:
lemma fieldEquivOfAlgEquivHom_apply
  given: (f : B ≃ₐ[A] B)
  proof: rfl

中文:
引理 fieldEquivOfAlgEquivHom_apply
  条件: (f : B ≃ₐ[A] B)
  证明: rfl
-/
lemma fieldEquivOfAlgEquivHom_apply (f : B ≃ₐ[A] B) :
    fieldEquivOfAlgEquivHom K L f = fieldEquivOfAlgEquiv K L L f :=
  rfl

variable (A B)

/--
lemma `fieldEquivOfAlgEquivHom_injective` / 引理 `fieldEquivOfAlgEquivHom_injective`

English:
lemma fieldEquivOfAlgEquivHom_injective
  proof: by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)

中文:
引理 fieldEquivOfAlgEquivHom_injective
  证明: by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff.mp, algebraMap, ext_iff
-/
lemma fieldEquivOfAlgEquivHom_injective :
    Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L)) := by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)

end fieldEquivOfAlgEquivHom

/--
theorem `isFractionRing_iff_of_base_ringEquiv` / 定理 `isFractionRing_iff_of_base_ringEquiv`

English:
theorem isFractionRing_iff_of_base_ringEquiv
  given: (h : R ≃+* P)
  proof: by
  delta IsFractionRing
  convert! isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  exact (MulEquivClass.map_nonZeroDivisors h).symm

中文:
定理 isFractionRing_iff_of_base_ringEquiv
  条件: (h : R ≃+* P)
  证明: by
  delta IsFractionRing
  convert! isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  exact (MulEquivClass.map_nonZeroDivisors h).symm

Depends on / 依赖: IsFractionRing, MulEquivClass, MulEquivClass.map_nonZeroDivisors, convert, isLocalization_iff_of_base_ringEquiv, map_nonZeroDivisors, nonZeroDivisors
-/
theorem isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsFractionRing R S ↔
      @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta IsFractionRing
  convert! isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  exact (MulEquivClass.map_nonZeroDivisors h).symm

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [h : IsFractionRing R S]

/--
theorem `nontrivial_iff_nontrivial` / 定理 `nontrivial_iff_nontrivial`

English:
theorem nontrivial_iff_nontrivial
  statement: Nontrivial R ↔ Nontrivial S
  proof: by
  by_contra! ⟨_, _⟩ | ⟨_, _⟩
  · obtain ⟨c, hc⟩ := h.exists_of_eq (x := 1) (y := 0) (Subsingleton.elim _ _)
    simp at hc
  · apply (h.map_units S 1).ne_zero
    rw [Subsingleton.eq_zero ((1 : nonZeroDivisors R) : R)]; rw [map_zero]

中文:
定理 nontrivial_iff_nontrivial
  结论: 非平凡 R ↔ 非平凡 S
  证明: by
  by_contra! ⟨_, _⟩ | ⟨_, _⟩
  · obtain ⟨c, hc⟩ := h.exists_of_eq (x := 1) (y := 0) (Subsingleton.elim _ _)
    simp at hc
  · apply (h.map_units S 1).ne_zero
    rw [Subsingleton.eq_zero ((1 : nonZeroDivisors R) : R)]; rw [map_zero]

Depends on / 依赖: Subsingleton, Subsingleton.elim, Subsingleton.eq_zero, eq_zero, exists_of_eq, h.exists_of_eq, h.map_units, map_units, map_zero, ne_zero, nonZeroDivisors
-/
theorem nontrivial_iff_nontrivial : Nontrivial R ↔ Nontrivial S := by
  by_contra! ⟨_, _⟩ | ⟨_, _⟩
  · obtain ⟨c, hc⟩ := h.exists_of_eq (x := 1) (y := 0) (Subsingleton.elim _ _)
    simp at hc
  · apply (h.map_units S 1).ne_zero
    rw [Subsingleton.eq_zero ((1 : nonZeroDivisors R) : R)]; rw [map_zero]

/--
theorem `nontrivial` / 定理 `nontrivial`

English:
theorem nontrivial
  given: [hR : Nontrivial R]
  statement: Nontrivial S
  proof: h.nontrivial_iff_nontrivial.mp hR

中文:
定理 nontrivial
  条件: [hR : 非平凡 R]
  结论: 非平凡 S
  证明: h.nontrivial_iff_nontrivial.mp hR
-/
protected theorem nontrivial [hR : Nontrivial R] : Nontrivial S :=
  h.nontrivial_iff_nontrivial.mp hR

section MulAction

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]

/-- Given a `MulSemiringAction G B`, extend the action of `G` on `B` to a `MulSemiringAction G L`
on the fraction field `L` of `B`. -/
@[instance_reducible]
/--
Definition of `mulSemiringAction` / `mulSemiringAction` 的定义

English:
definition mulSemiringAction
  signature: :
  body: MulSemiringAction.compHom L
    ((ringEquivOfRingEquivHom B L).comp (MulSemiringAction.toRingEquiv G B))

中文:
定义 mulSemiringAction
  签名: :
  定义体: MulSemiringAction.compHom L
    ((ringEquivOfRingEquivHom B L).comp (MulSemiringAction.toRingEquiv G B))

Depends on / 依赖: MulSemiringAction, MulSemiringAction.compHom, MulSemiringAction.toRingEquiv, compHom, ringEquivOfRingEquivHom, toRingEquiv
-/
noncomputable def mulSemiringAction :
    MulSemiringAction G L :=
  MulSemiringAction.compHom L
    ((ringEquivOfRingEquivHom B L).comp (MulSemiringAction.toRingEquiv G B))

/--
Instance `smulDistribClass` / 实例 `smulDistribClass`

English:
instance smulDistribClass
  signature: :
  body: mulSemiringAction G B L
    SMulDistribClass G B L :=
  let := mulSemiringAction G B L
  ⟨fun g b x => by
    rw [Algebra.smul_def']; rw [Algebra.smul_def']; rw [smul_mul']
    congr
    apply ringEquivOfRingEquiv_algebraMap⟩

中文:
实例 smulDistribClass
  签名: :
  定义体: mulSemiringAction G B L
    SMulDistribClass G B L :=
  let := mulSemiringAction G B L
  ⟨fun g b x => by
    rw [Algebra.smul_def']; rw [Algebra.smul_def']; rw [smul_mul']
    congr
    apply ringEquivOfRingEquiv_algebraMap⟩

Depends on / 依赖: mulSemiringAction
-/
instance smulDistribClass :
    letI := mulSemiringAction G B L
    SMulDistribClass G B L :=
  let := mulSemiringAction G B L
  ⟨fun g b x => by
    rw [Algebra.smul_def']; rw [Algebra.smul_def']; rw [smul_mul']
    congr
    apply ringEquivOfRingEquiv_algebraMap⟩

variable [MulSemiringAction G L] [SMulDistribClass G B L]

/--
theorem `faithfulSMul` / 定理 `faithfulSMul`

English:
theorem faithfulSMul
  given: [FaithfulSMul G B]
  statement: FaithfulSMul G L
  proof: ⟨fun h => eq_of_smul_eq_smul fun x => by simpa [← algebraMap.coe_smul'] using h (algebraMap B L x)⟩

中文:
定理 faithfulSMul
  条件: [忠实标量乘法 G B]
  结论: 忠实标量乘法 G L
  证明: ⟨fun h => eq_of_smul_eq_smul fun x => by simpa [← algebraMap.coe_smul'] using h (algebraMap B L x)⟩
-/
protected theorem faithfulSMul [FaithfulSMul G B] : FaithfulSMul G L :=
  ⟨fun h => eq_of_smul_eq_smul fun x => by simpa [← algebraMap.coe_smul'] using h (algebraMap B L x)⟩

/--
theorem `smulCommClass` / 定理 `smulCommClass`

English:
theorem smulCommClass
  given: [SMulCommClass G A B]
  statement: SMulCommClass G K L
  proof: ⟨fun g x y => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, smul_mul', smul_div₀',
      ← al

中文:
定理 smulCommClass
  条件: [标量交换类 G A B]
  结论: 标量交换类 G K L
  证明: ⟨fun g x y => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, smul_mul', smul_div₀',
      ← al
-/
protected theorem smulCommClass [SMulCommClass G A B] : SMulCommClass G K L :=
  ⟨fun g x y => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, smul_mul', smul_div₀',
      ← algebraMap.coe_smul', smul_algebraMap]⟩

end MulAction

end IsFractionRing

section algebraMap_injective

/--
theorem `algebraMap_injective_of_field_isFractionRing` / 定理 `algebraMap_injective_of_field_isFractionRing`

English:
theorem algebraMap_injective_of_field_isFractionRing
  statement: (K L : Type*) [Field K] [Semiring L]
  proof: by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)

中文:
定理 algebraMap_injective_of_field_isFractionRing
  结论: (K L : 类型) [域 K] [半环 L]
  证明: by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)

Depends on / 依赖: Function, Function.Injective.of_comp, Injective, IsFractionRing, IsFractionRing.injective, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.coe_comp, algebraMap, algebraMap_eq, coe_comp, injective, injective.comp, of_comp
-/
theorem algebraMap_injective_of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : Function.Injective (algebraMap R S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)

/--
theorem `FaithfulSMul.of_field_isFractionRing` / 定理 `FaithfulSMul.of_field_isFractionRing`

English:
theorem FaithfulSMul.of_field_isFractionRing
  statement: (K L : Type*) [Field K] [Semiring L]
  proof: (faithfulSMul_iff_algebraMap_injective R S).mpr
    algebraMap_injective_of_field_isFractionRing R S K L

中文:
定理 忠实标量乘法.of_field_isFractionRing
  结论: (K L : 类型) [域 K] [半环 L]
  证明: (faithfulSMul_iff_algebraMap_injective R S).mpr
    algebraMap_injective_of_field_isFractionRing R S K L

Depends on / 依赖: algebraMap_injective_of_field_isFractionRing, faithfulSMul_iff_algebraMap_injective
-/
theorem FaithfulSMul.of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : FaithfulSMul R S :=
(faithfulSMul_iff_algebraMap_injective R S).mpr
    algebraMap_injective_of_field_isFractionRing R S K L

end algebraMap_injective

variable (A)

/--
Definition of `FractionRing` / `FractionRing` 的定义

English:
abbreviation FractionRing
  body: Localization (nonZeroDivisors R)

中文:
缩写 FractionRing
  定义体: Localization (nonZeroDivisors R)

Depends on / 依赖: Localization, nonZeroDivisors
-/
abbrev FractionRing :=
  Localization (nonZeroDivisors R)

namespace FractionRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing (FractionRing R) (FractionRing R)
  body: IsFractionRing.idem R _

中文:
实例 :
  签名: IsFractionRing (FractionRing R) (FractionRing R)
  定义体: IsFractionRing.idem R _

Depends on / 依赖: IsFractionRing, IsFractionRing.idem
-/
instance : IsFractionRing (FractionRing R) (FractionRing R) := IsFractionRing.idem R _

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [Subsingleton R]
  body: inferInstance

中文:
实例 unique
  签名: [子单例 R]
  定义体: inferInstance
-/
instance unique [Subsingleton R] : Unique (FractionRing R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (FractionRing R)
  body: inferInstance

中文:
实例 [非平凡
  签名: R] : 非平凡 (FractionRing R)
  定义体: inferInstance
-/
instance [Nontrivial R] : Nontrivial (FractionRing R) := inferInstance

variable {R} in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : DecidableEq (FractionRing R)
  body: by
  intro x y
  apply Localization.recOnSubsingleton₂ x y (r := fun x y => Decidable (x = y))
  intro a c b d
  simp only [Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

中文:
实例 [DecidableEq
  签名: R] : DecidableEq (FractionRing R)
  定义体: by
  intro x y
  apply Localization.recOnSubsingleton₂ x y (r := fun x y => Decidable (x = y))
  intro a c b d
  simp only [Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

Depends on / 依赖: Decidable, Localization, Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors, Localization.recOnSubsingleton, infer_instance, le_refl, mk_eq_mk_iff, r_iff_of_le_nonZeroDivisors
-/
instance [DecidableEq R] : DecidableEq (FractionRing R) := by
  intro x y
  apply Localization.recOnSubsingleton₂ x y (r := fun x y => Decidable (x = y))
  intro a c b d
  simp only [Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

variable [IsDomain A]

/--
Instance `field` / 实例 `field`

English:
instance field
  signature: : Field (FractionRing A)
  body: inferInstance

@[simp]

中文:
实例 field
  签名: : 域 (FractionRing A)
  定义体: inferInstance

@[simp]
-/
noncomputable instance field : Field (FractionRing A) := inferInstance

@[simp]
/--
theorem `mk_eq_div` / 定理 `mk_eq_div`

English:
theorem mk_eq_div
  given: {r s}
  proof: by
  rw [Localization.mk_eq_mk']; rw [IsFractionRing.mk'_eq_div]

中文:
定理 mk_eq_div
  条件: {r s}
  证明: by
  rw [Localization.mk_eq_mk']; rw [IsFractionRing.mk'_eq_div]

Depends on / 依赖: IsFractionRing, IsFractionRing.mk, Localization, Localization.mk_eq_mk, _eq_div, mk_eq_mk
-/
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) =
      (algebraMap _ _ r / algebraMap A _ s : FractionRing A) := by
  rw [Localization.mk_eq_mk']; rw [IsFractionRing.mk'_eq_div]

section liftAlgebra

variable [Field K] [Algebra R K] [FaithfulSMul R K]

/--
Definition of `liftAlgebra` / `liftAlgebra` 的定义

English:
abbreviation liftAlgebra
  signature: : Algebra (FractionRing R) K
  body: have := IsDomain.of_faithfulSMul R K
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K))

中文:
缩写 liftAlgebra
  签名: : 代数 (FractionRing R) K
  定义体: have := IsDomain.of_faithfulSMul R K
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, IsDomain.of_faithfulSMul, IsFractionRing, IsFractionRing.lift, RingHom, RingHom.toAlgebra, algebraMap_injective, of_faithfulSMul, toAlgebra
-/
noncomputable abbrev liftAlgebra : Algebra (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K))

attribute [local instance] liftAlgebra

/--
Instance `isScalarTower_liftAlgebra` / 实例 `isScalarTower_liftAlgebra`

English:
instance isScalarTower_liftAlgebra
  signature: : IsScalarTower R (FractionRing R) K
  body: have := IsDomain.of_faithfulSMul R K
  .of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm

中文:
实例 isScalarTower_liftAlgebra
  签名: : 标量塔 R (FractionRing R) K
  定义体: have := IsDomain.of_faithfulSMul R K
  .of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, IsDomain.of_faithfulSMul, IsFractionRing, IsFractionRing.lift_algebraMap, algebraMap_injective, lift_algebraMap, of_algebraMap_eq, of_faithfulSMul
-/
instance isScalarTower_liftAlgebra : IsScalarTower R (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  .of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm

/--
lemma `algebraMap_liftAlgebra` / 引理 `algebraMap_liftAlgebra`

English:
lemma algebraMap_liftAlgebra
  proof: IsDomain.of_faithfulSMul R K
    algebraMap (FractionRing R) K = IsFractionRing.lift (FaithfulSMul.algebraMap_injective R _) :=
  rfl

中文:
引理 algebraMap_liftAlgebra
  证明: IsDomain.of_faithfulSMul R K
    algebraMap (FractionRing R) K = IsFractionRing.lift (FaithfulSMul.algebraMap_injective R _) :=
  rfl

Depends on / 依赖: IsDomain, IsDomain.of_faithfulSMul, of_faithfulSMul
-/
lemma algebraMap_liftAlgebra :
    have := IsDomain.of_faithfulSMul R K
    algebraMap (FractionRing R) K = IsFractionRing.lift (FaithfulSMul.algebraMap_injective R _) :=
  rfl

instance {R₀} [SMul R₀ R] [IsScalarTower R₀ R R] [SMul R₀ K] [IsScalarTower R₀ R K] :
    IsScalarTower R₀ (FractionRing R) K := IsScalarTower.to₁₃₄ _ R _ _

end liftAlgebra

/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K]
  body: Localization.algEquiv (nonZeroDivisors A) K

中文:
定义 algEquiv
  签名: (K : 类型) [交换环 K] [代数 A K] [IsFractionRing A K]
  定义体: Localization.algEquiv (nonZeroDivisors A) K

Depends on / 依赖: Localization, Localization.algEquiv, algEquiv, nonZeroDivisors
-/
noncomputable def algEquiv (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: R A] [FaithfulSMul R A] : FaithfulSMul R (FractionRing A)
  body: by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R A]
  exact (FaithfulSMul.algebraMap_injective A (FractionRing A)).comp
    (FaithfulSMul.algebraMap_injective R A)

中文:
实例 [代数
  签名: R A] [忠实标量乘法 R A] : 忠实标量乘法 R (FractionRing A)
  定义体: by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R A]
  exact (FaithfulSMul.algebraMap_injective A (FractionRing A)).comp
    (FaithfulSMul.algebraMap_injective R A)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, algebraMap_injective, faithfulSMul_iff_algebraMap_injective
-/
instance [Algebra R A] [FaithfulSMul R A] : FaithfulSMul R (FractionRing A) := by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R A]
  exact (FaithfulSMul.algebraMap_injective A (FractionRing A)).comp
    (FaithfulSMul.algebraMap_injective R A)

section IsScalarTower

attribute [local instance] liftAlgebra

instance (k K : Type*) [Field k] [Field K] [Algebra A k] [Algebra A K] [Algebra k K]
    [FaithfulSMul A k] [FaithfulSMul A K] [IsScalarTower A k K] :
    IsScalarTower (FractionRing A) k K where
  smul_assoc a b c := a.ind fun ⟨a₁, a₂⟩ => by
    rw [← smul_right_inj (nonZeroDivisors.coe_ne_zero a₂)]
    simp_rw [← smul_assoc, Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk',
      IsLocalization.mk'_mul_cancel_left, algebraMap_smul, smul_assoc]

end IsScalarTower

end FractionRing
