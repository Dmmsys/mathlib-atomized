/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Ring.Associated

/-!
# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `CommMonoidWithZero`s.

## Main Definitions

* `NormalizationMonoid`
* `StrongNormalizationMonoid`
* `GCDMonoid`
* `IsGCDMonoid`
* `NormalizedGCDMonoid`
* `StrongNormalizedGCDMonoid`
* `gcdMonoidOfGCD`, `gcdMonoidOfExistsGCD`, `normalizedGCDMonoidOfGCD`,
  `normalizedGCDMonoidOfExistsGCD`
* `gcdMonoidOfLCM`, `gcdMonoidOfExistsLCM`, `normalizedGCDMonoidOfLCM`,
  `normalizedGCDMonoidOfExistsLCM`

For the `NormalizedGCDMonoid` instances on `ℕ` and `ℤ`, see `Mathlib/Algebra/GCDMonoid/Nat.lean`.

## Implementation Notes

* `NormalizationMonoid` is defined by assigning to each element a `normUnit` such that multiplying
  by that unit normalizes the monoid, and `normalize` is an idempotent function. This
  definition as currently implemented does casework on `0`.

* `StrongNormalizationMonoid` further requires `normalize` to be a monoid homomorphism.

* `GCDMonoid` contains the definitions of `gcd` and `lcm` with the usual properties. They are
  both determined up to a unit.

* `IsGCDMonoid` is the predicate for the existence of a `GCDMonoid` structure.

* `NormalizedGCDMonoid` extends `NormalizationMonoid`, so the `gcd` and `lcm` are always
  normalized. This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains,
  and monoids without zero.

* `StrongNormalizedGCDMonoid` similarly extends `StrongNormalizationMonoid`.

* `gcdMonoidOfGCD` and `normalizedGCDMonoidOfGCD` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `gcd` and its properties.

* `gcdMonoidOfExistsGCD` and `normalizedGCDMonoidOfExistsGCD` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `gcd`.

* `gcdMonoidOfLCM` and `normalizedGCDMonoidOfLCM` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `lcm` and its properties.

* `gcdMonoidOfExistsLCM` and `normalizedGCDMonoidOfExistsLCM` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `lcm`.

## TODO

* Port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero

## Tags

divisibility, gcd, lcm, normalize
-/

@[expose] public section


variable {α : Type*}

/--
Definition of `NormalizationMonoid` / `NormalizationMonoid` 的定义

English:
class NormalizationMonoid
  parameters: (α : Type*) [MonoidWithZero α]
  axioms and operations (4):
    - normUnit : α -> αˣ
    - normUnit_zero : normUnit 0 = 1
    - normUnit_one : normUnit 1 = 1
    - normUnit_mul_units({a : α} (u : αˣ)) : a != 0 -> normUnit (a * u) = u⁻¹ * normUnit a

中文:
类 Normalization幺半群
  参数: (α : 类型) [带零幺半群 α]
  公理与运算 (4 个):
    - normUnit : α -> αˣ
    - normUnit_zero : normUnit 0 = 1
    - normUnit_one : normUnit 1 = 1
    - normUnit_mul_units({a : α} (u : αˣ)) : a != 0 -> normUnit (a * u) = u⁻¹ * normUnit a
-/
class NormalizationMonoid (α : Type*) [MonoidWithZero α] where
  /-- `normUnit` assigns to each element of the monoid a unit of the monoid. -/
  normUnit : α -> αˣ
  normUnit_zero : normUnit 0 = 1
  normUnit_one : normUnit 1 = 1
  /-- The condition that ensures associated elements are normalized to the same element. -/
  normUnit_mul_units {a : α} (u : αˣ) : a != 0 -> normUnit (a * u) = u⁻¹ * normUnit a

/--
Definition of `NormalizationMonoid.ofRightInverse` / `NormalizationMonoid.ofRightInverse` 的定义

English:
abbreviation NormalizationMonoid.ofRightInverse
  signature: {α : Type*} [MonoidWithZero α]
  body: have assoc a := (Associates.mk_eq_mk_iff_associated.mp <| mk_out (.mk a)).symm
  let := Classical.dec
  { normUnit a := if a = 0 then 1 else (assoc a).choose
    normUnit_zero := if_pos rfl
    normUnit_one := by
      nontriviality α; rw [← Units.val_inj]; convert ← (assoc 1).choose_spec <;> simp [out_one]
    normUnit_mul_units {a} u ha := by
      simp_rw [Units.mul_left_eq_zero, if_neg ha, eq_inv_mul_iff_mul_eq, ← Units.val_inj]
      rw [Units.val_mul]; rw [← (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha).eq_iff]; rw [(assoc a).choose_spec]; rw [← mul_assoc]; rw [(assoc _).choose_spec]; rw [Associates.mk_eq_mk_iff_associated.mpr (associated_mul_unit_right a u u.isUnit)] }

中文:
缩写 Normalization幺半群.ofRightInverse
  签名: {α : 类型} [带零幺半群 α]
  定义体: have assoc a := (Associates.mk_eq_mk_iff_associated.mp <| mk_out (.mk a)).symm
  let := Classical.dec
  { normUnit a := if a = 0 then 1 else (assoc a).choose
    normUnit_zero := if_pos rfl
    normUnit_one := by
      nontriviality α; rw [← Units.val_inj]; convert ← (assoc 1).choose_spec <;> simp [out_one]
    normUnit_mul_units {a} u ha := by
      simp_rw [Units.mul_left_eq_zero, if_neg ha, eq_inv_mul_iff_mul_eq, ← Units.val_inj]
      rw [Units.val_mul]; rw [← (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha).eq_iff]; rw [(assoc a).choose_spec]; rw [← mul_assoc]; rw [(assoc _).choose_spec]; rw [Associates.mk_eq_mk_iff_associated.mpr (associated_mul_unit_right a u u.isUnit)] }

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated.mp, Classical, Classical.dec, IsLeftCancelMulZero, IsLeftCancelMulZero.mul_left_cancel_of_ne_zero, Units.mul_left_eq_zero, Units.val_inj, Units.val_mul, choose_spec, convert, eq_iff, eq_inv_mul_iff_mul_eq, if_neg, if_pos, mk_eq_mk_iff_associated, mk_out, mul_left_cancel_of_ne_zero, mul_left_eq_zero, nontriviality
-/
noncomputable abbrev NormalizationMonoid.ofRightInverse {α : Type*} [MonoidWithZero α]
    [IsLeftCancelMulZero α] (out : Associates α -> α)
    (mk_out : forall a, Associates.mk (out a) = a) (out_one : out 1 = 1) :
    NormalizationMonoid α :=
  have assoc a := (Associates.mk_eq_mk_iff_associated.mp <| mk_out (.mk a)).symm
  let := Classical.dec
  { normUnit a := if a = 0 then 1 else (assoc a).choose
    normUnit_zero := if_pos rfl
    normUnit_one := by
      nontriviality α; rw [← Units.val_inj]; convert ← (assoc 1).choose_spec <;> simp [out_one]
    normUnit_mul_units {a} u ha := by
      simp_rw [Units.mul_left_eq_zero, if_neg ha, eq_inv_mul_iff_mul_eq, ← Units.val_inj]
      rw [Units.val_mul]; rw [← (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha).eq_iff]; rw [(assoc a).choose_spec]; rw [← mul_assoc]; rw [(assoc _).choose_spec]; rw [Associates.mk_eq_mk_iff_associated.mpr (associated_mul_unit_right a u u.isUnit)] }

/-- A cancellative monoid with zero always admits a `NormalizationMonoid` structure. -/
instance (α) [MonoidWithZero α] [IsLeftCancelMulZero α] :
Nonempty (NormalizationMonoid α) := .intro by
  exact .ofRightInverse
    (fun a => by classical exact if a = 1 then 1 else a.out)
    (fun _ => by split_ifs with h <;> simp [h]) (by simp)

/--
Definition of `StrongNormalizationMonoid` / `StrongNormalizationMonoid` 的定义

English:
class StrongNormalizationMonoid
  parameters: (α) [CommMonoidWithZero α]
  extends: NormalizationMonoid α
  axioms and operations (4):
    - normUnit_mul : forall {a b}, a != 0 -> b != 0 -> normUnit (a * b) = normUnit a * normUnit b
    - normUnit_coe_units : forall u : αˣ, normUnit u = u⁻¹
    - normUnit_one : = normUnit_coe_units 1
    - normUnit_mul_units({a} u ha) : = (by nontriviality α; simp [normUnit_mul, ha, normUnit_coe_units, mul_comm])

中文:
类 StrongNormalization幺半群
  参数: (α) [带零交换幺半群 α]
  继承: Normalization幺半群 α
  公理与运算 (4 个):
    - normUnit_mul : 对任意 {a b}, a != 0 -> b != 0 -> normUnit (a * b) = normUnit a * normUnit b
    - normUnit_coe_units : 对任意 u : αˣ, normUnit u = u⁻¹
    - normUnit_one : = normUnit_coe_units 1
    - normUnit_mul_units({a} u ha) : = (by nontriviality α; simp [normUnit_mul, ha, normUnit_coe_units, mul_comm])

Depends on / 依赖: normUnit_coe_units
-/
class StrongNormalizationMonoid (α) [CommMonoidWithZero α] extends NormalizationMonoid α where
  /-- The proposition that `normUnit` respects multiplication of non-zero elements. -/
  normUnit_mul : forall {a b}, a != 0 -> b != 0 -> normUnit (a * b) = normUnit a * normUnit b
  /-- The proposition that `normUnit` maps units to their inverses. -/
  normUnit_coe_units : forall u : αˣ, normUnit u = u⁻¹
  normUnit_one := normUnit_coe_units 1
  normUnit_mul_units {a} u ha :=
    (by nontriviality α; simp [normUnit_mul, ha, normUnit_coe_units, mul_comm])

export NormalizationMonoid (normUnit normUnit_zero normUnit_one normUnit_mul_units)
export StrongNormalizationMonoid (normUnit_mul)

attribute [simp] normUnit_zero normUnit_mul normUnit_one

section NormalizationMonoid

variable [MonoidWithZero α] [NormalizationMonoid α]

/--
theorem `normUnit_coe_units` / 定理 `normUnit_coe_units`

English:
theorem normUnit_coe_units
  given: (u : αˣ)
  statement: normUnit u.1 = u⁻¹
  proof: by
  nontriviality α; convert normUnit_mul_units u one_ne_zero using 1 <;> simp

中文:
定理 normUnit_coe_units
  条件: (u : αˣ)
  结论: normUnit u.1 = u⁻¹
  证明: by
  nontriviality α; convert normUnit_mul_units u one_ne_zero using 1 <;> simp
-/
@[simp] theorem normUnit_coe_units (u : αˣ) : normUnit u.1 = u⁻¹ := by
  nontriviality α; convert normUnit_mul_units u one_ne_zero using 1 <;> simp

/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: (x : α)
  body: x * normUnit x

中文:
定义 normalize
  签名: (x : α)
  定义体: x * normUnit x

Depends on / 依赖: normUnit
-/
def normalize (x : α) : α := x * normUnit x

/--
theorem `associated_normalize` / 定理 `associated_normalize`

English:
theorem associated_normalize
  given: (x : α)
  statement: Associated x (normalize x)
  proof: ⟨_, rfl⟩

中文:
定理 associated_normalize
  条件: (x : α)
  结论: Associated x (normalize x)
  证明: ⟨_, rfl⟩
-/
theorem associated_normalize (x : α) : Associated x (normalize x) :=
  ⟨_, rfl⟩

/--
theorem `normalize_associated` / 定理 `normalize_associated`

English:
theorem normalize_associated
  given: (x : α)
  statement: Associated (normalize x) x
  proof: (associated_normalize _).symm

中文:
定理 normalize_associated
  条件: (x : α)
  结论: Associated (normalize x) x
  证明: (associated_normalize _).symm

Depends on / 依赖: associated_normalize
-/
theorem normalize_associated (x : α) : Associated (normalize x) x :=
  (associated_normalize _).symm

/--
theorem `associated_normalize_iff` / 定理 `associated_normalize_iff`

English:
theorem associated_normalize_iff
  given: {x y : α}
  statement: Associated x (normalize y) ↔ Associated x y
  proof: ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩

中文:
定理 associated_normalize_iff
  条件: {x y : α}
  结论: Associated x (normalize y) ↔ Associated x y
  证明: ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩

Depends on / 依赖: associated_normalize, h.trans, normalize_associated
-/
theorem associated_normalize_iff {x y : α} : Associated x (normalize y) ↔ Associated x y :=
  ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩

/--
theorem `normalize_associated_iff` / 定理 `normalize_associated_iff`

English:
theorem normalize_associated_iff
  given: {x y : α}
  statement: Associated (normalize x) y ↔ Associated x y
  proof: ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩

中文:
定理 normalize_associated_iff
  条件: {x y : α}
  结论: Associated (normalize x) y ↔ Associated x y
  证明: ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩

Depends on / 依赖: associated_normalize, normalize_associated
-/
theorem normalize_associated_iff {x y : α} : Associated (normalize x) y ↔ Associated x y :=
  ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩

/--
theorem `Associates.mk_normalize` / 定理 `Associates.mk_normalize`

English:
theorem Associates.mk_normalize
  given: (x : α)
  statement: Associates.mk (normalize x) = Associates.mk x
  proof: Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

中文:
定理 Associates.mk_normalize
  条件: (x : α)
  结论: Associates.mk (normalize x) = Associates.mk x
  证明: Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated, mk_eq_mk_iff_associated, normalize_associated
-/
theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x :=
  Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

/--
theorem `normalize_apply` / 定理 `normalize_apply`

English:
theorem normalize_apply
  given: (x : α)
  statement: normalize x = x * normUnit x
  proof: rfl

中文:
定理 normalize_apply
  条件: (x : α)
  结论: normalize x = x * normUnit x
  证明: rfl
-/
theorem normalize_apply (x : α) : normalize x = x * normUnit x :=
  rfl

/--
theorem `normalize_zero` / 定理 `normalize_zero`

English:
theorem normalize_zero
  statement: normalize (0 : α) = 0
  proof: by simp [normalize]

中文:
定理 normalize_zero
  结论: normalize (0 : α) = 0
  证明: by simp [normalize]
-/
@[simp] theorem normalize_zero : normalize (0 : α) = 0 := by simp [normalize]

/--
theorem `normalize_one` / 定理 `normalize_one`

English:
theorem normalize_one
  statement: normalize (1 : α) = 1
  proof: by simp [normalize]

中文:
定理 normalize_one
  结论: normalize (1 : α) = 1
  证明: by simp [normalize]
-/
@[simp] theorem normalize_one : normalize (1 : α) = 1 := by simp [normalize]

/--
theorem `normalize_coe_units` / 定理 `normalize_coe_units`

English:
theorem normalize_coe_units
  given: (u : αˣ)
  statement: normalize (u : α) = 1
  proof: by simp [normalize]

@[simp]

中文:
定理 normalize_coe_units
  条件: (u : αˣ)
  结论: normalize (u : α) = 1
  证明: by simp [normalize]

@[simp]

Depends on / 依赖: normalize
-/
theorem normalize_coe_units (u : αˣ) : normalize (u : α) = 1 := by simp [normalize]

@[simp]
/--
theorem `normalize_eq_zero` / 定理 `normalize_eq_zero`

English:
theorem normalize_eq_zero
  given: {x : α}
  statement: normalize x = 0 ↔ x = 0
  proof: ⟨fun hx => (associated_zero_iff_eq_zero x).1 hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩

中文:
定理 normalize_eq_zero
  条件: {x : α}
  结论: normalize x = 0 ↔ x = 0
  证明: ⟨fun hx => (associated_zero_iff_eq_zero x).1 hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩

Depends on / 依赖: associated_normalize, associated_zero_iff_eq_zero, normalize_zero
-/
theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
⟨fun hx => (associated_zero_iff_eq_zero x).1 hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩

/--
theorem `normalize_eq_one` / 定理 `normalize_eq_one`

English:
theorem normalize_eq_one
  given: {x : α}
  statement: normalize x = 1 ↔ IsUnit x where
  proof: Units.eq_inv_of_mul_eq_one_right hx ▸ Units.isUnit _
  mpr := fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u

@[simp]

中文:
定理 normalize_eq_one
  条件: {x : α}
  结论: normalize x = 1 ↔ 是单位 x where
  证明: Units.eq_inv_of_mul_eq_one_right hx ▸ Units.isUnit _
  mpr := fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u

@[simp]

Depends on / 依赖: Units.eq_inv_of_mul_eq_one_right, Units.isUnit, eq_inv_of_mul_eq_one_right, isUnit
-/
theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x where
  mp hx := Units.eq_inv_of_mul_eq_one_right hx ▸ Units.isUnit _
  mpr := fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u

@[simp]
/--
theorem `normUnit_mul_normUnit` / 定理 `normUnit_mul_normUnit`

English:
theorem normUnit_mul_normUnit
  given: (a : α)
  statement: normUnit (a * normUnit a) = 1
  proof: by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · simp [normUnit_mul_units _ h]

@[simp]

中文:
定理 normUnit_mul_normUnit
  条件: (a : α)
  结论: normUnit (a * normUnit a) = 1
  证明: by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · simp [normUnit_mul_units _ h]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, eq_or_ne, nontriviality, normUnit_mul_units, normUnit_zero, zero_mul
-/
theorem normUnit_mul_normUnit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · simp [normUnit_mul_units _ h]

@[simp]
/--
theorem `normalize_idem` / 定理 `normalize_idem`

English:
theorem normalize_idem
  given: (x : α)
  statement: normalize (normalize x) = normalize x
  proof: by simp [normalize_apply]

中文:
定理 normalize_idem
  条件: (x : α)
  结论: normalize (normalize x) = normalize x
  证明: by simp [normalize_apply]

Depends on / 依赖: normalize_apply
-/
theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp [normalize_apply]

/--
theorem `normalize_eq_normalize_iff_associated` / 定理 `normalize_eq_normalize_iff_associated`

English:
theorem normalize_eq_normalize_iff_associated
  given: {a b : α}
  proof: (associated_normalize a).trans .trans (.of_eq h) (associated_normalize b).symm
  mpr := by
    rintro ⟨u, rfl⟩
    nontriviality α
    refine by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a != 0 => ?_
    simp [normalize, normUnit_mul_units _ ha, mul_assoc]

中文:
定理 normalize_eq_normalize_iff_associated
  条件: {a b : α}
  证明: (associated_normalize a).trans .trans (.of_eq h) (associated_normalize b).symm
  mpr := by
    rintro ⟨u, rfl⟩
    nontriviality α
    refine by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a != 0 => ?_
    simp [normalize, normUnit_mul_units _ ha, mul_assoc]

Depends on / 依赖: associated_normalize, of_eq
-/
theorem normalize_eq_normalize_iff_associated {a b : α} :
    normalize a = normalize b ↔ Associated a b where
mp h := (associated_normalize a).trans .trans (.of_eq h) (associated_normalize b).symm
  mpr := by
    rintro ⟨u, rfl⟩
    nontriviality α
    refine by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a != 0 => ?_
    simp [normalize, normUnit_mul_units _ ha, mul_assoc]

/--
theorem `Associated.eq_of_normalized` / 定理 `Associated.eq_of_normalized`

English:
theorem Associated.eq_of_normalized
  proof: by
  rw [← ha]; rw [normalize_eq_normalize_iff_associated.mpr h]; rw [hb]

@[simp]

中文:
定理 Associated.eq_of_normalized
  证明: by
  rw [← ha]; rw [normalize_eq_normalize_iff_associated.mpr h]; rw [hb]

@[simp]

Depends on / 依赖: normalize_eq_normalize_iff_associated, normalize_eq_normalize_iff_associated.mpr
-/
theorem Associated.eq_of_normalized
    {a b : α} (h : Associated a b) (ha : normalize a = a) (hb : normalize b = b) :
    a = b := by
  rw [← ha]; rw [normalize_eq_normalize_iff_associated.mpr h]; rw [hb]

@[simp]
/--
theorem `dvd_normalize_iff` / 定理 `dvd_normalize_iff`

English:
theorem dvd_normalize_iff
  given: {a b : α}
  statement: a ∣ normalize b ↔ a ∣ b
  proof: Units.dvd_mul_right

@[simp]

中文:
定理 dvd_normalize_iff
  条件: {a b : α}
  结论: a ∣ normalize b ↔ a ∣ b
  证明: Units.dvd_mul_right

@[simp]

Depends on / 依赖: Units.dvd_mul_right, dvd_mul_right
-/
theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
  Units.dvd_mul_right

@[simp]
/--
theorem `normalize_dvd_iff` / 定理 `normalize_dvd_iff`

English:
theorem normalize_dvd_iff
  given: {a b : α}
  statement: normalize a ∣ b ↔ a ∣ b
  proof: Units.mul_right_dvd

中文:
定理 normalize_dvd_iff
  条件: {a b : α}
  结论: normalize a ∣ b ↔ a ∣ b
  证明: Units.mul_right_dvd

Depends on / 依赖: Units.mul_right_dvd, mul_right_dvd
-/
theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
  Units.mul_right_dvd

section

variable [IsLeftCancelMulZero α]

/--
theorem `normalize_eq_normalize` / 定理 `normalize_eq_normalize`

English:
theorem normalize_eq_normalize
  given: {a b : α} (hab : a ∣ b) (hba : b ∣ a)
  proof: normalize_eq_normalize_iff_associated.mpr (associated_of_dvd_dvd hab hba)

中文:
定理 normalize_eq_normalize
  条件: {a b : α} (hab : a ∣ b) (hba : b ∣ a)
  证明: normalize_eq_normalize_iff_associated.mpr (associated_of_dvd_dvd hab hba)

Depends on / 依赖: associated_of_dvd_dvd, normalize_eq_normalize_iff_associated, normalize_eq_normalize_iff_associated.mpr
-/
theorem normalize_eq_normalize {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    normalize a = normalize b :=
  normalize_eq_normalize_iff_associated.mpr (associated_of_dvd_dvd hab hba)

/--
theorem `normalize_eq_normalize_iff` / 定理 `normalize_eq_normalize_iff`

English:
theorem normalize_eq_normalize_iff
  given: {x y : α}
  statement: normalize x = normalize y ↔ x ∣ y ∧ y ∣ x
  proof: by
  rw [normalize_eq_normalize_iff_associated]; rw [dvd_dvd_iff_associated]

中文:
定理 normalize_eq_normalize_iff
  条件: {x y : α}
  结论: normalize x = normalize y ↔ x ∣ y ∧ y ∣ x
  证明: by
  rw [normalize_eq_normalize_iff_associated]; rw [dvd_dvd_iff_associated]

Depends on / 依赖: dvd_dvd_iff_associated, normalize_eq_normalize_iff_associated
-/
theorem normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x := by
  rw [normalize_eq_normalize_iff_associated]; rw [dvd_dvd_iff_associated]

/--
theorem `dvd_antisymm_of_normalize_eq` / 定理 `dvd_antisymm_of_normalize_eq`

English:
theorem dvd_antisymm_of_normalize_eq
  statement: {a b : α} (ha : normalize a = a) (hb : normalize b = b)
  proof: ha ▸ hb ▸ normalize_eq_normalize hab hba

中文:
定理 dvd_antisymm_of_normalize_eq
  结论: {a b : α} (ha : normalize a = a) (hb : normalize b = b)
  证明: ha ▸ hb ▸ normalize_eq_normalize hab hba

Depends on / 依赖: normalize_eq_normalize
-/
theorem dvd_antisymm_of_normalize_eq {a b : α} (ha : normalize a = a) (hb : normalize b = b)
    (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba

end

end NormalizationMonoid

namespace Associates

variable [MonoidWithZero α] [NormalizationMonoid α]

/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: : Associates α -> α
  body: (Quotient.lift (normalize : α -> α)) fun _ _ ⟨_, hu⟩ =>
    hu ▸ normalize_eq_normalize_iff_associated.mpr ⟨_, rfl⟩

@[simp]

中文:
定义 out
  签名: : Associates α -> α
  定义体: (Quotient.lift (normalize : α -> α)) fun _ _ ⟨_, hu⟩ =>
    hu ▸ normalize_eq_normalize_iff_associated.mpr ⟨_, rfl⟩

@[simp]
-/
protected def out : Associates α -> α :=
  (Quotient.lift (normalize : α -> α)) fun _ _ ⟨_, hu⟩ =>
    hu ▸ normalize_eq_normalize_iff_associated.mpr ⟨_, rfl⟩

@[simp]
/--
theorem `out_mk` / 定理 `out_mk`

English:
theorem out_mk
  given: (a : α)
  statement: (Associates.mk a).out = normalize a
  proof: rfl

@[simp]

中文:
定理 out_mk
  条件: (a : α)
  结论: (Associates.mk a).out = normalize a
  证明: rfl

@[simp]
-/
theorem out_mk (a : α) : (Associates.mk a).out = normalize a :=
  rfl

@[simp]
/--
theorem `out_one` / 定理 `out_one`

English:
theorem out_one
  statement: (1 : Associates α).out = 1
  proof: normalize_one

@[simp]

中文:
定理 out_one
  结论: (1 : Associates α).out = 1
  证明: normalize_one

@[simp]

Depends on / 依赖: normalize_one
-/
theorem out_one : (1 : Associates α).out = 1 :=
  normalize_one

@[simp]
/--
theorem `out_top` / 定理 `out_top`

English:
theorem out_top
  statement: (⊤ : Associates α).out = 0
  proof: normalize_zero

@[simp]

中文:
定理 out_top
  结论: (⊤ : Associates α).out = 0
  证明: normalize_zero

@[simp]

Depends on / 依赖: normalize_zero
-/
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero

@[simp]
/--
theorem `normalize_out` / 定理 `normalize_out`

English:
theorem normalize_out
  given: (a : Associates α)
  statement: normalize a.out = a.out
  proof: Quotient.inductionOn a normalize_idem

@[simp]

中文:
定理 normalize_out
  条件: (a : Associates α)
  结论: normalize a.out = a.out
  证明: Quotient.inductionOn a normalize_idem

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, normalize_idem
-/
theorem normalize_out (a : Associates α) : normalize a.out = a.out :=
  Quotient.inductionOn a normalize_idem

@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: (a : Associates α)
  statement: Associates.mk a.out = a
  proof: Quotient.inductionOn a mk_normalize

中文:
定理 mk_out
  条件: (a : Associates α)
  结论: Associates.mk a.out = a
  证明: Quotient.inductionOn a mk_normalize

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, mk_normalize
-/
theorem mk_out (a : Associates α) : Associates.mk a.out = a :=
  Quotient.inductionOn a mk_normalize

/--
theorem `out_injective` / 定理 `out_injective`

English:
theorem out_injective
  statement: Function.Injective (Associates.out : _ -> α)
  proof: Function.LeftInverse.injective mk_out

@[simp]

中文:
定理 out_injective
  结论: 函数.单射 (Associates.out : _ -> α)
  证明: Function.LeftInverse.injective mk_out

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, mk_out
-/
theorem out_injective : Function.Injective (Associates.out : _ -> α) :=
  Function.LeftInverse.injective mk_out

@[simp]
/--
theorem `out_eq_zero_iff` / 定理 `out_eq_zero_iff`

English:
theorem out_eq_zero_iff
  given: {a : Associates α}
  statement: a.out = 0 ↔ a = 0
  proof: Quotient.inductionOn a (by simp)

中文:
定理 out_eq_zero_iff
  条件: {a : Associates α}
  结论: a.out = 0 ↔ a = 0
  证明: Quotient.inductionOn a (by simp)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem out_eq_zero_iff {a : Associates α} : a.out = 0 ↔ a = 0 :=
  Quotient.inductionOn a (by simp)

/--
theorem `out_zero` / 定理 `out_zero`

English:
theorem out_zero
  statement: (0 : Associates α).out = 0
  proof: by
  simp

中文:
定理 out_zero
  结论: (0 : Associates α).out = 0
  证明: by
  simp
-/
theorem out_zero : (0 : Associates α).out = 0 := by
  simp

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]

/--
theorem `out_mul'` / 定理 `out_mul'`

English:
theorem out_mul'
  given: (a b : Associates α)
  statement: Associated (a * b).out (a.out * b.out)
  proof: Quotient.inductionOn₂ a b fun _ _ => normalize_associated_iff.mpr
    .mul_mul (associated_normalize _) (associated_normalize _)

中文:
定理 out_mul'
  条件: (a b : Associates α)
  结论: Associated (a * b).out (a.out * b.out)
  证明: Quotient.inductionOn₂ a b fun _ _ => normalize_associated_iff.mpr
    .mul_mul (associated_normalize _) (associated_normalize _)

Depends on / 依赖: Quotient, Quotient.inductionOn, associated_normalize, mul_mul, normalize_associated_iff, normalize_associated_iff.mpr
-/
theorem out_mul' (a b : Associates α) : Associated (a * b).out (a.out * b.out) :=
Quotient.inductionOn₂ a b fun _ _ => normalize_associated_iff.mpr
    .mul_mul (associated_normalize _) (associated_normalize _)

/--
theorem `dvd_out_iff` / 定理 `dvd_out_iff`

English:
theorem dvd_out_iff
  given: (a : α) (b : Associates α)
  statement: a ∣ b.out ↔ Associates.mk a <= b
  proof: Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

中文:
定理 dvd_out_iff
  条件: (a : α) (b : Associates α)
  结论: a ∣ b.out ↔ Associates.mk a <= b
  证明: Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

Depends on / 依赖: Associates, Associates.out_mk, Associates.quotient_mk_eq_mk, Quotient, Quotient.inductionOn, inductionOn, mk_le_mk_iff_dvd, out_mk, quotient_mk_eq_mk
-/
theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a <= b :=
Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

/--
theorem `out_dvd_iff` / 定理 `out_dvd_iff`

English:
theorem out_dvd_iff
  given: (a : α) (b : Associates α)
  statement: b.out ∣ a ↔ b <= Associates.mk a
  proof: Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

中文:
定理 out_dvd_iff
  条件: (a : α) (b : Associates α)
  结论: b.out ∣ a ↔ b <= Associates.mk a
  证明: Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

Depends on / 依赖: Associates, Associates.out_mk, Associates.quotient_mk_eq_mk, Quotient, Quotient.inductionOn, inductionOn, mk_le_mk_iff_dvd, out_mk, quotient_mk_eq_mk
-/
theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b <= Associates.mk a :=
Quotient.inductionOn b by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

end Associates

section StrongNormalizationMonoid

variable [CommMonoidWithZero α] [StrongNormalizationMonoid α]

/--
theorem `normalize_mul` / 定理 `normalize_mul`

English:
theorem normalize_mul
  given: (x y : α)
  statement: normalize (x * y) = normalize x * normalize y
  proof: by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  simp_rw [normalize, normUnit_mul hx hy]
  ac_rfl

中文:
定理 normalize_mul
  条件: (x y : α)
  结论: normalize (x * y) = normalize x * normalize y
  证明: by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  simp_rw [normalize, normUnit_mul hx hy]
  ac_rfl
-/
@[simp] theorem normalize_mul (x y : α) : normalize (x * y) = normalize x * normalize y := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  simp_rw [normalize, normUnit_mul hx hy]
  ac_rfl

/--
Definition of `normalizeHom` / `normalizeHom` 的定义

English:
definition normalizeHom
  signature: : α ->*₀ α where
  body: normalize
  map_zero' := normalize_zero
  map_one' := normalize_one
  map_mul' := normalize_mul

中文:
定义 normalizeHom
  签名: : α ->*₀ α where
  定义体: normalize
  map_zero' := normalize_zero
  map_one' := normalize_one
  map_mul' := normalize_mul

Depends on / 依赖: normalize
-/
def normalizeHom : α ->*₀ α where
  toFun := normalize
  map_zero' := normalize_zero
  map_one' := normalize_one
  map_mul' := normalize_mul

/--
theorem `coe_normalizeHom` / 定理 `coe_normalizeHom`

English:
theorem coe_normalizeHom
  statement: normalizeHom (α := α) = normalize (α := α)
  proof: rfl

中文:
定理 coe_normalizeHom
  结论: normalizeHom (α := α) = normalize (α := α)
  证明: rfl

Depends on / 依赖: normalize
-/
theorem coe_normalizeHom : normalizeHom (α := α) = normalize (α := α) :=
  rfl

/--
theorem `Associates.out_mul` / 定理 `Associates.out_mul`

English:
theorem Associates.out_mul
  given: (a b : Associates α)
  statement: (a * b).out = a.out * b.out
  proof: Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize_mul]

中文:
定理 Associates.out_mul
  条件: (a b : Associates α)
  结论: (a * b).out = a.out * b.out
  证明: Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize_mul]

Depends on / 依赖: Associates, Associates.quotient_mk_eq_mk, Quotient, Quotient.inductionOn, mk_mul_mk, normalize_mul, out_mk, quotient_mk_eq_mk
-/
theorem Associates.out_mul (a b : Associates α) : (a * b).out = a.out * b.out :=
  Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize_mul]

end StrongNormalizationMonoid

/--
Definition of `GCDMonoid` / `GCDMonoid` 的定义

English:
class GCDMonoid
  parameters: (α : Type*) [CommMonoidWithZero α]
  extends: IsCancelMulZero α
  axioms and operations (8):
    - gcd : α -> α -> α
    - lcm : α -> α -> α
    - gcd_dvd_left : forall a b, gcd a b ∣ a
    - gcd_dvd_right : forall a b, gcd a b ∣ b
    - dvd_gcd : forall {a b c}, a ∣ c -> a ∣ b -> a ∣ gcd c b
    - gcd_mul_lcm : forall a b, Associated (gcd a b * lcm a b) (a * b)
    - lcm_zero_left : forall a, lcm 0 a = 0
    - lcm_zero_right : forall a, lcm a 0 = 0

中文:
类 最大公约数幺半群
  参数: (α : 类型) [带零交换幺半群 α]
  继承: 是乘零消去 α
  公理与运算 (8 个):
    - gcd : α -> α -> α
    - lcm : α -> α -> α
    - gcd_dvd_left : 对任意 a b, 最大公约数 a b ∣ a
    - gcd_dvd_right : 对任意 a b, 最大公约数 a b ∣ b
    - dvd_gcd : 对任意 {a b c}, a ∣ c -> a ∣ b -> a ∣ 最大公约数 c b
    - gcd_mul_lcm : 对任意 a b, Associated (最大公约数 a b * 最小公倍数 a b) (a * b)
    - lcm_zero_left : 对任意 a, 最小公倍数 0 a = 0
    - lcm_zero_right : 对任意 a, 最小公倍数 a 0 = 0
-/
class GCDMonoid (α : Type*) [CommMonoidWithZero α] extends IsCancelMulZero α where
  /-- The greatest common divisor between two elements. -/
  gcd : α -> α -> α
  /-- The least common multiple between two elements. -/
  lcm : α -> α -> α
  /-- The GCD is a divisor of the first element. -/
  gcd_dvd_left : forall a b, gcd a b ∣ a
  /-- The GCD is a divisor of the second element. -/
  gcd_dvd_right : forall a b, gcd a b ∣ b
  /-- Any common divisor of both elements is a divisor of the GCD. -/
  dvd_gcd : forall {a b c}, a ∣ c -> a ∣ b -> a ∣ gcd c b
  /-- The product of two elements is `Associated` with the product of their GCD and LCM. -/
  gcd_mul_lcm : forall a b, Associated (gcd a b * lcm a b) (a * b)
  /-- `0` is left-absorbing. -/
  lcm_zero_left : forall a, lcm 0 a = 0
  /-- `0` is right-absorbing. -/
  lcm_zero_right : forall a, lcm a 0 = 0

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: IsGCDMonoid (α : Type*) [CommMonoidWithZero α]
  (no additional axioms)

中文:
类 inductive
  参数: IsGCDMonoid (α : 类型) [带零交换幺半群 α]
  (无附加公理)
-/
class inductive IsGCDMonoid (α : Type*) [CommMonoidWithZero α] : Prop
  | intro : GCDMonoid α -> IsGCDMonoid α

attribute [instance 100] GCDMonoid.toIsCancelMulZero

/--
Definition of `NormalizedGCDMonoid` / `NormalizedGCDMonoid` 的定义

English:
class NormalizedGCDMonoid
  parameters: (α : Type*) [CommMonoidWithZero α]
  extends: NormalizationMonoid α, 
  axioms and operations (2):
    - normalize_gcd : forall a b, normalize (gcd a b) = gcd a b
    - normalize_lcm : forall a b, normalize (lcm a b) = lcm a b

中文:
类 正规化最大公约数幺半群
  参数: (α : 类型) [带零交换幺半群 α]
  继承: Normalization幺半群 α, 
  公理与运算 (2 个):
    - normalize_gcd : 对任意 a b, normalize (最大公约数 a b) = 最大公约数 a b
    - normalize_lcm : 对任意 a b, normalize (最小公倍数 a b) = 最小公倍数 a b
-/
class NormalizedGCDMonoid (α : Type*) [CommMonoidWithZero α] extends NormalizationMonoid α,
  GCDMonoid α where
  /-- The GCD is normalized to itself. -/
  normalize_gcd : forall a b, normalize (gcd a b) = gcd a b
  /-- The LCM is normalized to itself. -/
  normalize_lcm : forall a b, normalize (lcm a b) = lcm a b

/--
Definition of `StrongNormalizedGCDMonoid` / `StrongNormalizedGCDMonoid` 的定义

English:
class StrongNormalizedGCDMonoid
  parameters: (α : Type*) [CommMonoidWithZero α]
  axioms and operations (2):
    - normalize_gcd : forall a b, normalize (gcd a b) = gcd a b
    - normalize_lcm : forall a b, normalize (lcm a b) = lcm a b

中文:
类 StrongNormalizedGCD幺半群
  参数: (α : 类型) [带零交换幺半群 α]
  公理与运算 (2 个):
    - normalize_gcd : 对任意 a b, normalize (最大公约数 a b) = 最大公约数 a b
    - normalize_lcm : 对任意 a b, normalize (最小公倍数 a b) = 最小公倍数 a b
-/
class StrongNormalizedGCDMonoid (α : Type*) [CommMonoidWithZero α] extends
  StrongNormalizationMonoid α, GCDMonoid α where
  /-- The GCD is normalized to itself. -/
  normalize_gcd : forall a b, normalize (gcd a b) = gcd a b
  /-- The LCM is normalized to itself. -/
  normalize_lcm : forall a b, normalize (lcm a b) = lcm a b

export GCDMonoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd
  gcd_mul_lcm lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

instance (α) [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α] : NormalizedGCDMonoid α where
  normalize_gcd := StrongNormalizedGCDMonoid.normalize_gcd
  normalize_lcm := StrongNormalizedGCDMonoid.normalize_lcm

section GCDMonoid

variable [CommMonoidWithZero α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalizationMonoid
  signature: α] : Nonempty (NormalizationMonoid α)
  body: ⟨‹_›⟩

中文:
实例 [Normalization幺半群
  签名: α] : 非空 (Normalization幺半群 α)
  定义体: ⟨‹_›⟩
-/
instance [NormalizationMonoid α] : Nonempty (NormalizationMonoid α) := ⟨‹_›⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StrongNormalizationMonoid
  signature: α] : Nonempty (StrongNormalizationMonoid α)
  body: ⟨‹_›⟩

中文:
实例 [StrongNormalization幺半群
  签名: α] : 非空 (StrongNormalization幺半群 α)
  定义体: ⟨‹_›⟩
-/
instance [StrongNormalizationMonoid α] : Nonempty (StrongNormalizationMonoid α) := ⟨‹_›⟩

instance (priority := 100) [GCDMonoid α] : IsGCDMonoid α := ⟨‹_›⟩

variable (α) in
-- This is not an instance due to performance reasons.
/--
theorem `IsGCDMonoid.isCancelMulZero` / 定理 `IsGCDMonoid.isCancelMulZero`

English:
theorem IsGCDMonoid.isCancelMulZero
  given: [h : IsGCDMonoid α]
  statement: IsCancelMulZero α
  proof: h.rec fun _ => inferInstance

中文:
定理 IsGCDMonoid.isCancelMulZero
  条件: [h : IsGCDMonoid α]
  结论: 是乘零消去 α
  证明: h.rec fun _ => inferInstance

Depends on / 依赖: h.rec
-/
theorem IsGCDMonoid.isCancelMulZero [h : IsGCDMonoid α] : IsCancelMulZero α :=
  h.rec fun _ => inferInstance

/--
theorem `gcd_isUnit_iff_isRelPrime` / 定理 `gcd_isUnit_iff_isRelPrime`

English:
theorem gcd_isUnit_iff_isRelPrime
  given: [GCDMonoid α] {a b : α}
  proof: ⟨fun h _ ha hb => isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩

@[simp]

中文:
定理 gcd_isUnit_iff_isRelPrime
  条件: [最大公约数幺半群 α] {a b : α}
  证明: ⟨fun h _ ha hb => isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩

@[simp]

Depends on / 依赖: dvd_gcd, gcd_dvd_left, gcd_dvd_right, isUnit_of_dvd_unit
-/
theorem gcd_isUnit_iff_isRelPrime [GCDMonoid α] {a b : α} :
    IsUnit (gcd a b) ↔ IsRelPrime a b :=
  ⟨fun h _ ha hb => isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩

@[simp]
/--
theorem `normalize_gcd` / 定理 `normalize_gcd`

English:
theorem normalize_gcd
  given: [NormalizedGCDMonoid α]
  statement: forall a b : α, normalize (gcd a b) = gcd a b
  proof: NormalizedGCDMonoid.normalize_gcd

中文:
定理 normalize_gcd
  条件: [正规化最大公约数幺半群 α]
  结论: 对任意 a b : α, normalize (最大公约数 a b) = 最大公约数 a b
  证明: NormalizedGCDMonoid.normalize_gcd

Depends on / 依赖: NormalizedGCDMonoid, NormalizedGCDMonoid.normalize_gcd, normalize_gcd
-/
theorem normalize_gcd [NormalizedGCDMonoid α] : forall a b : α, normalize (gcd a b) = gcd a b :=
  NormalizedGCDMonoid.normalize_gcd

section GCD

/--
theorem `dvd_gcd_iff` / 定理 `dvd_gcd_iff`

English:
theorem dvd_gcd_iff
  given: [GCDMonoid α] (a b c : α)
  statement: a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c
  proof: Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac

中文:
定理 dvd_gcd_iff
  条件: [最大公约数幺半群 α] (a b c : α)
  结论: a ∣ 最大公约数 b c ↔ a ∣ b ∧ a ∣ c
  证明: Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac

Depends on / 依赖: Iff.intro, dvd_gcd, gcd_dvd_left, gcd_dvd_right, h.trans
-/
theorem dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac

/--
theorem `gcd_comm` / 定理 `gcd_comm`

English:
theorem gcd_comm
  given: [NormalizedGCDMonoid α] (a b : α)
  statement: gcd a b = gcd b a
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

中文:
定理 gcd_comm
  条件: [正规化最大公约数幺半群 α] (a b : α)
  结论: 最大公约数 a b = 最大公约数 b a
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_gcd, gcd_dvd_left, gcd_dvd_right, normalize_gcd
-/
theorem gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

/--
theorem `gcd_comm'` / 定理 `gcd_comm'`

English:
theorem gcd_comm'
  given: [GCDMonoid α] (a b : α)
  statement: Associated (gcd a b) (gcd b a)
  proof: associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

中文:
定理 gcd_comm'
  条件: [最大公约数幺半群 α] (a b : α)
  结论: Associated (最大公约数 a b) (最大公约数 b a)
  证明: associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem gcd_comm' [GCDMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) :=
  associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

/--
theorem `gcd_assoc` / 定理 `gcd_assoc`

English:
theorem gcd_assoc
  given: [NormalizedGCDMonoid α] (m n k : α)
  statement: gcd (gcd m n) k = gcd m (gcd n k)
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

中文:
定理 gcd_assoc
  条件: [正规化最大公约数幺半群 α] (m n k : α)
  结论: 最大公约数 (最大公约数 m n) k = 最大公约数 m (最大公约数 n k)
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_gcd, gcd_dvd_left, gcd_dvd_right, normalize_gcd
-/
theorem gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

/--
theorem `gcd_assoc'` / 定理 `gcd_assoc'`

English:
theorem gcd_assoc'
  given: [GCDMonoid α] (m n k : α)
  statement: Associated (gcd (gcd m n) k) (gcd m (gcd n k))
  proof: associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

中文:
定理 gcd_assoc'
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: Associated (最大公约数 (最大公约数 m n) k) (最大公约数 m (最大公约数 n k))
  证明: associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem gcd_assoc' [GCDMonoid α] (m n k : α) : Associated (gcd (gcd m n) k) (gcd m (gcd n k)) :=
  associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalizedGCDMonoid
  signature: α] : Std.Commutative (α
  body: gcd_comm

中文:
实例 [正规化最大公约数幺半群
  签名: α] : Std.交换 (α
  定义体: gcd_comm
-/
instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) gcd where
  comm := gcd_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalizedGCDMonoid
  signature: α] : Std.Associative (α
  body: gcd_assoc

中文:
实例 [正规化最大公约数幺半群
  签名: α] : Std.结合 (α
  定义体: gcd_assoc
-/
instance [NormalizedGCDMonoid α] : Std.Associative (α := α) gcd where
  assoc := gcd_assoc

/--
theorem `gcd_eq_normalize` / 定理 `gcd_eq_normalize`

English:
theorem gcd_eq_normalize
  statement: [NormalizedGCDMonoid α] {a b c : α} (habc : gcd a b ∣ c)
  proof: normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]

中文:
定理 gcd_eq_normalize
  结论: [正规化最大公约数幺半群 α] {a b c : α} (habc : 最大公约数 a b ∣ c)
  证明: normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]

Depends on / 依赖: normalize_eq_normalize, normalize_gcd
-/
theorem gcd_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : gcd a b ∣ c)
    (hcab : c ∣ gcd a b) : gcd a b = normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]
/--
theorem `gcd_zero_left` / 定理 `gcd_zero_left`

English:
theorem gcd_zero_left
  given: [NormalizedGCDMonoid α] (a : α)
  statement: gcd 0 a = normalize a
  proof: gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

中文:
定理 gcd_zero_left
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最大公约数 0 a = normalize a
  证明: gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

Depends on / 依赖: dvd_gcd, dvd_refl, dvd_zero, gcd_dvd_right, gcd_eq_normalize
-/
theorem gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a = normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

/--
theorem `gcd_zero_left'` / 定理 `gcd_zero_left'`

English:
theorem gcd_zero_left'
  given: [GCDMonoid α] (a : α)
  statement: Associated (gcd 0 a) a
  proof: associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]

中文:
定理 gcd_zero_left'
  条件: [最大公约数幺半群 α] (a : α)
  结论: Associated (最大公约数 0 a) a
  证明: associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, dvd_refl, dvd_zero, gcd_dvd_right
-/
theorem gcd_zero_left' [GCDMonoid α] (a : α) : Associated (gcd 0 a) a :=
  associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]
/--
theorem `gcd_zero_right` / 定理 `gcd_zero_right`

English:
theorem gcd_zero_right
  given: [NormalizedGCDMonoid α] (a : α)
  statement: gcd a 0 = normalize a
  proof: gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

中文:
定理 gcd_zero_right
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最大公约数 a 0 = normalize a
  证明: gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

Depends on / 依赖: dvd_gcd, dvd_refl, dvd_zero, gcd_dvd_left, gcd_eq_normalize
-/
theorem gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0 = normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

/--
theorem `gcd_zero_right'` / 定理 `gcd_zero_right'`

English:
theorem gcd_zero_right'
  given: [GCDMonoid α] (a : α)
  statement: Associated (gcd a 0) a
  proof: associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]

中文:
定理 gcd_zero_right'
  条件: [最大公约数幺半群 α] (a : α)
  结论: Associated (最大公约数 a 0) a
  证明: associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, dvd_refl, dvd_zero, gcd_dvd_left
-/
theorem gcd_zero_right' [GCDMonoid α] (a : α) : Associated (gcd a 0) a :=
  associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]
/--
theorem `gcd_eq_zero_iff` / 定理 `gcd_eq_zero_iff`

English:
theorem gcd_eq_zero_iff
  given: [GCDMonoid α] (a b : α)
  statement: gcd a b = 0 ↔ a = 0 ∧ b = 0
  proof: Iff.intro
    (fun h => by
      let ⟨ca, ha⟩ := gcd_dvd_left a b
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      rw [h]; rw [zero_mul] at ha hb
      exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ => by
    rw [ha]; rw [hb]; rw [← zero_dvd_iff]
    apply dvd_gcd <;> rfl

中文:
定理 gcd_eq_zero_iff
  条件: [最大公约数幺半群 α] (a b : α)
  结论: 最大公约数 a b = 0 ↔ a = 0 ∧ b = 0
  证明: Iff.intro
    (fun h => by
      let ⟨ca, ha⟩ := gcd_dvd_left a b
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      rw [h]; rw [zero_mul] at ha hb
      exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ => by
    rw [ha]; rw [hb]; rw [← zero_dvd_iff]
    apply dvd_gcd <;> rfl

Depends on / 依赖: Iff.intro, dvd_gcd, gcd_dvd_left, gcd_dvd_right, zero_dvd_iff, zero_mul
-/
theorem gcd_eq_zero_iff [GCDMonoid α] (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  Iff.intro
    (fun h => by
      let ⟨ca, ha⟩ := gcd_dvd_left a b
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      rw [h]; rw [zero_mul] at ha hb
      exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ => by
    rw [ha]; rw [hb]; rw [← zero_dvd_iff]
    apply dvd_gcd <;> rfl

/--
theorem `gcd_ne_zero_of_left` / 定理 `gcd_ne_zero_of_left`

English:
theorem gcd_ne_zero_of_left
  given: [GCDMonoid α] {a b : α} (ha : a != 0)
  statement: gcd a b != 0
  proof: by
  simp_all

中文:
定理 gcd_ne_zero_of_left
  条件: [最大公约数幺半群 α] {a b : α} (ha : a != 0)
  结论: 最大公约数 a b != 0
  证明: by
  simp_all
-/
theorem gcd_ne_zero_of_left [GCDMonoid α] {a b : α} (ha : a != 0) : gcd a b != 0 := by
  simp_all

/--
theorem `gcd_ne_zero_of_right` / 定理 `gcd_ne_zero_of_right`

English:
theorem gcd_ne_zero_of_right
  given: [GCDMonoid α] {a b : α} (hb : b != 0)
  statement: gcd a b != 0
  proof: by
  simp_all

@[simp]

中文:
定理 gcd_ne_zero_of_right
  条件: [最大公约数幺半群 α] {a b : α} (hb : b != 0)
  结论: 最大公约数 a b != 0
  证明: by
  simp_all

@[simp]
-/
theorem gcd_ne_zero_of_right [GCDMonoid α] {a b : α} (hb : b != 0) : gcd a b != 0 := by
  simp_all

@[simp]
/--
theorem `gcd_one_left` / 定理 `gcd_one_left`

English:
theorem gcd_one_left
  given: [NormalizedGCDMonoid α] (a : α)
  statement: gcd 1 a = 1
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]

中文:
定理 gcd_one_left
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最大公约数 1 a = 1
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]

Depends on / 依赖: StrongNormalizationMonoid, dvd_antisymm_of_normalize_eq, gcd_dvd_left, normalize_gcd, normalize_one, one_dvd
-/
theorem gcd_one_left [NormalizedGCDMonoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]
/--
theorem `isUnit_gcd_one_left` / 定理 `isUnit_gcd_one_left`

English:
theorem isUnit_gcd_one_left
  given: [GCDMonoid α] (a : α)
  statement: IsUnit (gcd 1 a)
  proof: isUnit_of_dvd_one (gcd_dvd_left _ _)

中文:
定理 isUnit_gcd_one_left
  条件: [最大公约数幺半群 α] (a : α)
  结论: 是单位 (最大公约数 1 a)
  证明: isUnit_of_dvd_one (gcd_dvd_left _ _)

Depends on / 依赖: gcd_dvd_left, isUnit_of_dvd_one
-/
theorem isUnit_gcd_one_left [GCDMonoid α] (a : α) : IsUnit (gcd 1 a) :=
  isUnit_of_dvd_one (gcd_dvd_left _ _)

/--
theorem `gcd_one_left'` / 定理 `gcd_one_left'`

English:
theorem gcd_one_left'
  given: [GCDMonoid α] (a : α)
  statement: Associated (gcd 1 a) 1
  proof: by simp

@[simp]

中文:
定理 gcd_one_left'
  条件: [最大公约数幺半群 α] (a : α)
  结论: Associated (最大公约数 1 a) 1
  证明: by simp

@[simp]
-/
theorem gcd_one_left' [GCDMonoid α] (a : α) : Associated (gcd 1 a) 1 := by simp

@[simp]
/--
theorem `gcd_one_right` / 定理 `gcd_one_right`

English:
theorem gcd_one_right
  given: [NormalizedGCDMonoid α] (a : α)
  statement: gcd a 1 = 1
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]

中文:
定理 gcd_one_right
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最大公约数 a 1 = 1
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]

Depends on / 依赖: dvd_antisymm_of_normalize_eq, gcd_dvd_right, normalize_gcd, normalize_one, one_dvd
-/
theorem gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]
/--
theorem `isUnit_gcd_one_right` / 定理 `isUnit_gcd_one_right`

English:
theorem isUnit_gcd_one_right
  given: [GCDMonoid α] (a : α)
  statement: IsUnit (gcd a 1)
  proof: isUnit_of_dvd_one (gcd_dvd_right _ _)

中文:
定理 isUnit_gcd_one_right
  条件: [最大公约数幺半群 α] (a : α)
  结论: 是单位 (最大公约数 a 1)
  证明: isUnit_of_dvd_one (gcd_dvd_right _ _)

Depends on / 依赖: gcd_dvd_right, isUnit_of_dvd_one
-/
theorem isUnit_gcd_one_right [GCDMonoid α] (a : α) : IsUnit (gcd a 1) :=
  isUnit_of_dvd_one (gcd_dvd_right _ _)

/--
theorem `gcd_one_right'` / 定理 `gcd_one_right'`

English:
theorem gcd_one_right'
  given: [GCDMonoid α] (a : α)
  statement: Associated (gcd a 1) 1
  proof: by simp

@[gcongr]

中文:
定理 gcd_one_right'
  条件: [最大公约数幺半群 α] (a : α)
  结论: Associated (最大公约数 a 1) 1
  证明: by simp

@[gcongr]
-/
theorem gcd_one_right' [GCDMonoid α] (a : α) : Associated (gcd a 1) 1 := by simp

@[gcongr]
/--
theorem `gcd_dvd_gcd` / 定理 `gcd_dvd_gcd`

English:
theorem gcd_dvd_gcd
  given: [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d)
  statement: gcd a c ∣ gcd b d
  proof: dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

中文:
定理 gcd_dvd_gcd
  条件: [最大公约数幺半群 α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d)
  结论: 最大公约数 a c ∣ 最大公约数 b d
  证明: dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

Depends on / 依赖: dvd_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem gcd_dvd_gcd [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

/--
theorem `Associated.gcd` / 定理 `Associated.gcd`

English:
theorem Associated.gcd
  statement: [GCDMonoid α]
  proof: associated_of_dvd_dvd (gcd_dvd_gcd ha.dvd hb.dvd) (gcd_dvd_gcd ha.dvd' hb.dvd')

@[simp]

中文:
定理 Associated.最大公约数
  结论: [最大公约数幺半群 α]
  证明: associated_of_dvd_dvd (gcd_dvd_gcd ha.dvd hb.dvd) (gcd_dvd_gcd ha.dvd' hb.dvd')

@[simp]
-/
protected theorem Associated.gcd [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (gcd a₁ b₁) (gcd a₂ b₂) :=
  associated_of_dvd_dvd (gcd_dvd_gcd ha.dvd hb.dvd) (gcd_dvd_gcd ha.dvd' hb.dvd')

@[simp]
/--
theorem `gcd_same` / 定理 `gcd_same`

English:
theorem gcd_same
  given: [NormalizedGCDMonoid α] (a : α)
  statement: gcd a a = normalize a
  proof: gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp]

中文:
定理 gcd_same
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最大公约数 a a = normalize a
  证明: gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp]

Depends on / 依赖: dvd_gcd, dvd_refl, gcd_dvd_left, gcd_eq_normalize
-/
theorem gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize a :=
  gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp]
/--
theorem `gcd_mul_left` / 定理 `gcd_mul_left`

English:
theorem gcd_mul_left
  given: [StrongNormalizedGCDMonoid α] (a b c : α)
  proof: (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
    let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (eq.symm ▸ mul_dvd_mul_left a
        (show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))

中文:
定理 gcd_mul_left
  条件: [StrongNormalizedGCD幺半群 α] (a b c : α)
  证明: (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
    let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (eq.symm ▸ mul_dvd_mul_left a
        (show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))

Depends on / 依赖: dvd_gcd, dvd_mul_right, eq.symm, gcd_dvd_left, gcd_dvd_right, gcd_eq_normalize, mul_dvd_mul_iff_left, mul_dvd_mul_left, normalize
-/
theorem gcd_mul_left [StrongNormalizedGCDMonoid α] (a b c : α) :
    gcd (a * b) (a * c) = normalize a * gcd b c :=
  (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
    let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (eq.symm ▸ mul_dvd_mul_left a
        (show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))

/--
theorem `gcd_mul_left'` / 定理 `gcd_mul_left'`

English:
theorem gcd_mul_left'
  given: [GCDMonoid α] (a b c : α)
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    gcongr
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)

@[simp]

中文:
定理 gcd_mul_left'
  条件: [最大公约数幺半群 α] (a b c : α)
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    gcongr
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)

@[simp]

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, dvd_mul_right, eq_or_ne, gcd_dvd_left, gcd_dvd_right, gcd_zero_left, mul_dvd_mul_iff_left, mul_dvd_mul_left, zero_mul
-/
theorem gcd_mul_left' [GCDMonoid α] (a b c : α) :
    Associated (gcd (a * b) (a * c)) (a * gcd b c) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    gcongr
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)

@[simp]
/--
theorem `gcd_mul_right` / 定理 `gcd_mul_right`

English:
theorem gcd_mul_right
  given: [StrongNormalizedGCDMonoid α] (a b c : α)
  proof: by simp only [mul_comm, gcd_mul_left]

@[simp]

中文:
定理 gcd_mul_right
  条件: [StrongNormalizedGCD幺半群 α] (a b c : α)
  证明: by simp only [mul_comm, gcd_mul_left]

@[simp]

Depends on / 依赖: gcd_mul_left, mul_comm
-/
theorem gcd_mul_right [StrongNormalizedGCDMonoid α] (a b c : α) :
    gcd (b * a) (c * a) = gcd b c * normalize a := by simp only [mul_comm, gcd_mul_left]

@[simp]
/--
theorem `gcd_mul_right'` / 定理 `gcd_mul_right'`

English:
theorem gcd_mul_right'
  given: [GCDMonoid α] (a b c : α)
  proof: by
  simp only [mul_comm, gcd_mul_left']

中文:
定理 gcd_mul_right'
  条件: [最大公约数幺半群 α] (a b c : α)
  证明: by
  simp only [mul_comm, gcd_mul_left']

Depends on / 依赖: gcd_mul_left, mul_comm
-/
theorem gcd_mul_right' [GCDMonoid α] (a b c : α) :
    Associated (gcd (b * a) (c * a)) (gcd b c * a) := by
  simp only [mul_comm, gcd_mul_left']

/--
theorem `gcd_eq_left_iff` / 定理 `gcd_eq_left_iff`

English:
theorem gcd_eq_left_iff
  given: [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a)
  proof: (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

中文:
定理 gcd_eq_left_iff
  条件: [正规化最大公约数幺半群 α] (a b : α) (h : normalize a = a)
  证明: (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

Depends on / 依赖: Iff.intro, dvd_antisymm_of_normalize_eq, dvd_gcd, dvd_refl, gcd_dvd_left, gcd_dvd_right, normalize_gcd
-/
theorem gcd_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

/--
theorem `gcd_eq_right_iff` / 定理 `gcd_eq_right_iff`

English:
theorem gcd_eq_right_iff
  given: [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b)
  proof: by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

中文:
定理 gcd_eq_right_iff
  条件: [正规化最大公约数幺半群 α] (a b : α) (h : normalize b = b)
  证明: by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

Depends on / 依赖: gcd_comm, gcd_eq_left_iff
-/
theorem gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    gcd a b = b ↔ b ∣ a := by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

/--
theorem `gcd_dvd_gcd_mul_left` / 定理 `gcd_dvd_gcd_mul_left`

English:
theorem gcd_dvd_gcd_mul_left
  given: [GCDMonoid α] (m n k : α)
  statement: gcd m n ∣ gcd (k * m) n
  proof: by
  grw [← dvd_mul_left]

中文:
定理 gcd_dvd_gcd_mul_left
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最大公约数 m n ∣ 最大公约数 (k * m) n
  证明: by
  grw [← dvd_mul_left]

Depends on / 依赖: dvd_mul_left
-/
theorem gcd_dvd_gcd_mul_left [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (k * m) n := by
  grw [← dvd_mul_left]

/--
theorem `gcd_dvd_gcd_mul_right` / 定理 `gcd_dvd_gcd_mul_right`

English:
theorem gcd_dvd_gcd_mul_right
  given: [GCDMonoid α] (m n k : α)
  statement: gcd m n ∣ gcd (m * k) n
  proof: by
  grw [← dvd_mul_right]

中文:
定理 gcd_dvd_gcd_mul_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最大公约数 m n ∣ 最大公约数 (m * k) n
  证明: by
  grw [← dvd_mul_right]

Depends on / 依赖: dvd_mul_right
-/
theorem gcd_dvd_gcd_mul_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (m * k) n := by
  grw [← dvd_mul_right]

/--
theorem `gcd_dvd_gcd_mul_left_right` / 定理 `gcd_dvd_gcd_mul_left_right`

English:
theorem gcd_dvd_gcd_mul_left_right
  given: [GCDMonoid α] (m n k : α)
  statement: gcd m n ∣ gcd m (k * n)
  proof: by
  grw [← dvd_mul_left]

中文:
定理 gcd_dvd_gcd_mul_left_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最大公约数 m n ∣ 最大公约数 m (k * n)
  证明: by
  grw [← dvd_mul_left]

Depends on / 依赖: dvd_mul_left
-/
theorem gcd_dvd_gcd_mul_left_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (k * n) := by
  grw [← dvd_mul_left]

/--
theorem `gcd_dvd_gcd_mul_right_right` / 定理 `gcd_dvd_gcd_mul_right_right`

English:
theorem gcd_dvd_gcd_mul_right_right
  given: [GCDMonoid α] (m n k : α)
  statement: gcd m n ∣ gcd m (n * k)
  proof: by
  grw [← dvd_mul_right]

中文:
定理 gcd_dvd_gcd_mul_right_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最大公约数 m n ∣ 最大公约数 m (n * k)
  证明: by
  grw [← dvd_mul_right]

Depends on / 依赖: dvd_mul_right
-/
theorem gcd_dvd_gcd_mul_right_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (n * k) := by
  grw [← dvd_mul_right]

/--
theorem `Associated.gcd_eq_left` / 定理 `Associated.gcd_eq_left`

English:
theorem Associated.gcd_eq_left
  given: [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α)
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

中文:
定理 Associated.gcd_eq_left
  条件: [正规化最大公约数幺半群 α] {m n : α} (h : Associated m n) (k : α)
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_rfl, gcd_dvd_gcd, h.dvd, h.symm.dvd, normalize_gcd
-/
theorem Associated.gcd_eq_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

/--
theorem `Associated.gcd_eq_right` / 定理 `Associated.gcd_eq_right`

English:
theorem Associated.gcd_eq_right
  given: [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α)
  proof: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

中文:
定理 Associated.gcd_eq_right
  条件: [正规化最大公约数幺半群 α] {m n : α} (h : Associated m n) (k : α)
  证明: dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_rfl, gcd_dvd_gcd, h.dvd, h.symm.dvd, nonempty_normalizedGCDMonoid_iff_isGCDMonoid, nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mpr, normalize_gcd
-/
theorem Associated.gcd_eq_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

/--
theorem `dvd_gcd_mul_of_dvd_mul` / 定理 `dvd_gcd_mul_of_dvd_mul`

English:
theorem dvd_gcd_mul_of_dvd_mul
  given: [GCDMonoid α] {m n k : α} (H : k ∣ m * n)
  statement: k ∣ gcd k m * n
  proof: (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd

中文:
定理 dvd_gcd_mul_of_dvd_mul
  条件: [最大公约数幺半群 α] {m n k : α} (H : k ∣ m * n)
  结论: k ∣ 最大公约数 k m * n
  证明: (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd

Depends on / 依赖: dvd_gcd, dvd_mul_right, gcd_mul_right
-/
theorem dvd_gcd_mul_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ gcd k m * n :=
  (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd

/--
theorem `dvd_gcd_mul_iff_dvd_mul` / 定理 `dvd_gcd_mul_iff_dvd_mul`

English:
theorem dvd_gcd_mul_iff_dvd_mul
  given: [GCDMonoid α] {m n k : α}
  statement: k ∣ gcd k m * n ↔ k ∣ m * n
  proof: ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩

中文:
定理 dvd_gcd_mul_iff_dvd_mul
  条件: [最大公约数幺半群 α] {m n k : α}
  结论: k ∣ 最大公约数 k m * n ↔ k ∣ m * n
  证明: ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩

Depends on / 依赖: dvd_gcd_mul_of_dvd_mul, dvd_rfl, gcd_dvd_right, h.trans, mul_dvd_mul
-/
theorem dvd_gcd_mul_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ gcd k m * n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩

/--
theorem `dvd_mul_gcd_of_dvd_mul` / 定理 `dvd_mul_gcd_of_dvd_mul`

English:
theorem dvd_mul_gcd_of_dvd_mul
  given: [GCDMonoid α] {m n k : α} (H : k ∣ m * n)
  statement: k ∣ m * gcd k n
  proof: by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H

中文:
定理 dvd_mul_gcd_of_dvd_mul
  条件: [最大公约数幺半群 α] {m n k : α} (H : k ∣ m * n)
  结论: k ∣ m * 最大公约数 k n
  证明: by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H

Depends on / 依赖: dvd_gcd_mul_of_dvd_mul, mul_comm
-/
theorem dvd_mul_gcd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H

/--
theorem `dvd_mul_gcd_iff_dvd_mul` / 定理 `dvd_mul_gcd_iff_dvd_mul`

English:
theorem dvd_mul_gcd_iff_dvd_mul
  given: [GCDMonoid α] {m n k : α}
  statement: k ∣ m * gcd k n ↔ k ∣ m * n
  proof: ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩

中文:
定理 dvd_mul_gcd_iff_dvd_mul
  条件: [最大公约数幺半群 α] {m n k : α}
  结论: k ∣ m * 最大公约数 k n ↔ k ∣ m * n
  证明: ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩

Depends on / 依赖: dvd_mul_gcd_of_dvd_mul, dvd_rfl, gcd_dvd_right, h.trans, mul_dvd_mul
-/
theorem dvd_mul_gcd_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ m * gcd k n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : IsGCDMonoid α] : DecompositionMonoid α where
  body: by
    cases h
    by_cases h0 : gcd k m = 0
    · rw [gcd_eq_zero_iff] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨0, n, dvd_refl 0, dvd_refl n, by simp⟩
    · obtain ⟨a, ha⟩ := gcd_dvd_left k m
      refine ⟨gcd k m, a, gcd_dvd_right _ _, ?_, ha⟩
      rw [← mul_dvd_mul_iff_left h0]; rw [← ha]
      exact dvd_gcd_mul_of_dvd_mul H

中文:
实例 [h
  签名: : IsGCDMonoid α] : 分解幺半群 α where
  定义体: by
    cases h
    by_cases h0 : gcd k m = 0
    · rw [gcd_eq_zero_iff] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨0, n, dvd_refl 0, dvd_refl n, by simp⟩
    · obtain ⟨a, ha⟩ := gcd_dvd_left k m
      refine ⟨gcd k m, a, gcd_dvd_right _ _, ?_, ha⟩
      rw [← mul_dvd_mul_iff_left h0]; rw [← ha]
      exact dvd_gcd_mul_of_dvd_mul H

Depends on / 依赖: dvd_gcd_mul_of_dvd_mul, dvd_refl, gcd_dvd_left, gcd_dvd_right, gcd_eq_zero_iff, mul_dvd_mul_iff_left
-/
instance [h : IsGCDMonoid α] : DecompositionMonoid α where
  primal k m n H := by
    cases h
    by_cases h0 : gcd k m = 0
    · rw [gcd_eq_zero_iff] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨0, n, dvd_refl 0, dvd_refl n, by simp⟩
    · obtain ⟨a, ha⟩ := gcd_dvd_left k m
      refine ⟨gcd k m, a, gcd_dvd_right _ _, ?_, ha⟩
      rw [← mul_dvd_mul_iff_left h0]; rw [← ha]
      exact dvd_gcd_mul_of_dvd_mul H

/--
theorem `gcd_mul_dvd_mul_gcd` / 定理 `gcd_mul_dvd_mul_gcd`

English:
theorem gcd_mul_dvd_mul_gcd
  given: [GCDMonoid α] (k m n : α)
  statement: gcd k (m * n) ∣ gcd k m * gcd k n
  proof: by
  obtain ⟨m', n', hm', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul (gcd_dvd_right k (m * n))
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'

中文:
定理 gcd_mul_dvd_mul_gcd
  条件: [最大公约数幺半群 α] (k m n : α)
  结论: 最大公约数 k (m * n) ∣ 最大公约数 k m * 最大公约数 k n
  证明: by
  obtain ⟨m', n', hm', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul (gcd_dvd_right k (m * n))
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'

Depends on / 依赖: dvd_gcd, dvd_mul_left, dvd_mul_right, exists_dvd_and_dvd_of_dvd_mul, gcd_dvd_left, gcd_dvd_right, mul_dvd_mul, replace
-/
theorem gcd_mul_dvd_mul_gcd [GCDMonoid α] (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  obtain ⟨m', n', hm', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul (gcd_dvd_right k (m * n))
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'

/--
theorem `gcd_pow_right_dvd_pow_gcd` / 定理 `gcd_pow_right_dvd_pow_gcd`

English:
theorem gcd_pow_right_dvd_pow_gcd
  given: [GCDMonoid α] {a b : α} {k : Nat}
  proof: by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction k with
    | zero => rw [pow_zero, pow_zero]; exact (gcd_one_right' a).dvd
    | succ k hk =>
      rw [pow_succ']; rw [pow_succ']
      trans gcd a b * gcd a (b ^ k)
      · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      · exact (mul_dvd_mul_iff_left hg).mpr hk

中文:
定理 gcd_pow_right_dvd_pow_gcd
  条件: [最大公约数幺半群 α] {a b : α} {k : 自然数}
  证明: by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction k with
    | zero => rw [pow_zero, pow_zero]; exact (gcd_one_right' a).dvd
    | succ k hk =>
      rw [pow_succ']; rw [pow_succ']
      trans gcd a b * gcd a (b ^ k)
      · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      · exact (mul_dvd_mul_iff_left hg).mpr hk

Depends on / 依赖: StrongNormalizedGCDMonoid, dvd.trans, gcd_eq_zero_iff, gcd_mul_dvd_mul_gcd, gcd_one_right, gcd_zero_left, mul_dvd_mul_iff_left, pow_dvd_pow_of_dvd, pow_succ, pow_zero, symm.dvd
-/
theorem gcd_pow_right_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : Nat} :
    gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction k with
    | zero => rw [pow_zero, pow_zero]; exact (gcd_one_right' a).dvd
    | succ k hk =>
      rw [pow_succ']; rw [pow_succ']
      trans gcd a b * gcd a (b ^ k)
      · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      · exact (mul_dvd_mul_iff_left hg).mpr hk

/--
theorem `gcd_pow_left_dvd_pow_gcd` / 定理 `gcd_pow_left_dvd_pow_gcd`

English:
theorem gcd_pow_left_dvd_pow_gcd
  given: [GCDMonoid α] {a b : α} {k : Nat}
  statement: gcd (a ^ k) b ∣ gcd a b ^ k
  proof: calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _

中文:
定理 gcd_pow_left_dvd_pow_gcd
  条件: [最大公约数幺半群 α] {a b : α} {k : 自然数}
  结论: 最大公约数 (a ^ k) b ∣ 最大公约数 a b ^ k
  证明: calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _

Depends on / 依赖: gcd_comm, gcd_pow_right_dvd_pow_gcd, pow_dvd_pow_of_dvd
-/
theorem gcd_pow_left_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : Nat} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _

/--
theorem `pow_dvd_of_mul_eq_pow` / 定理 `pow_dvd_of_mul_eq_pow`

English:
theorem pow_dvd_of_mul_eq_pow
  statement: [GCDMonoid α] {a b c d₁ d₂ : α} (ha : a != 0) (hab : IsUnit (gcd a b))
  proof: by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      grw [hd₁, hab.dvd]
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h]; rw [hc]
    exact mul_pow d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [h1.mul_left_dvd]
  have h4 : d₁ ^ k != 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

中文:
定理 pow_dvd_of_mul_eq_pow
  结论: [最大公约数幺半群 α] {a b c d₁ d₂ : α} (ha : a != 0) (hab : 是单位 (最大公约数 a b))
  证明: by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      grw [hd₁, hab.dvd]
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h]; rw [hc]
    exact mul_pow d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [h1.mul_left_dvd]
  have h4 : d₁ ^ k != 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

Depends on / 依赖: IsUnit, IsUnit.dvd, IsUnit.pow, absurd, dvd_gcd_mul_of_dvd_mul, gcd_pow_left_dvd_pow_gcd, h1.mul_left_dvd, hab.dvd, isUnit_of_dvd_one, mul_comm, mul_left_dvd, mul_pow, zero_dvd_iff, zero_dvd_iff.mp
-/
theorem pow_dvd_of_mul_eq_pow [GCDMonoid α] {a b c d₁ d₂ : α} (ha : a != 0) (hab : IsUnit (gcd a b))
    {k : Nat} (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k != 0 ∧ d₁ ^ k ∣ a := by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      grw [hd₁, hab.dvd]
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h]; rw [hc]
    exact mul_pow d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [h1.mul_left_dvd]
  have h4 : d₁ ^ k != 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

/--
theorem `exists_associated_pow_of_mul_eq_pow` / 定理 `exists_associated_pow_of_mul_eq_pow`

English:
theorem exists_associated_pow_of_mul_eq_pow
  statement: [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b))
  proof: by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elim a (0 ^ k)]
  by_cases ha : a = 0
  · use 0
    obtain rfl | hk := eq_or_ne k 0
    · simp [ha] at h
    · rw [ha, zero_pow hk]
  by_cases hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zero] at h ⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.val_mkOfMulEqOne]; rw [one_mul]
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).isUnit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha']; rw [hb']; rw [hc]; rw [mul_pow] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc]; rw [mul_comm a']; rw [← mul_assoc _ b']; rw [← mul_assoc b']; rw [mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.val_mkOfMulEqOne]; rw [ha']

中文:
定理 存在_associated_pow_of_mul_eq_pow
  结论: [最大公约数幺半群 α] {a b c : α} (hab : 是单位 (最大公约数 a b))
  证明: by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elim a (0 ^ k)]
  by_cases ha : a = 0
  · use 0
    obtain rfl | hk := eq_or_ne k 0
    · simp [ha] at h
    · rw [ha, zero_pow hk]
  by_cases hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zero] at h ⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.val_mkOfMulEqOne]; rw [one_mul]
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).isUnit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha']; rw [hb']; rw [hc]; rw [mul_pow] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc]; rw [mul_comm a']; rw [← mul_assoc _ b']; rw [← mul_assoc b']; rw [mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.val_mkOfMulEqOne]; rw [ha']

Depends on / 依赖: Subsingleton, Subsingleton.elim, Units.mkOfMulEqOne, Units.val_mkOfMulEqOne, associated_one_iff_isUnit, associated_one_iff_isUnit.mpr, dvd_pow_self, eq_or_ne, eq_zero_or_pos, gcd_zero_right, hk.ne, k.eq_zero_or_pos, mkOfMulEqOne, one_mul, one_pow, pow_zero, subsingleton_or_nontrivial, symm.trans, val_mkOfMulEqOne, zero_pow
-/
theorem exists_associated_pow_of_mul_eq_pow [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b))
    {k : Nat} (h : a * b = c ^ k) : exists d : α, Associated (d ^ k) a := by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elim a (0 ^ k)]
  by_cases ha : a = 0
  · use 0
    obtain rfl | hk := eq_or_ne k 0
    · simp [ha] at h
    · rw [ha, zero_pow hk]
  by_cases hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zero] at h ⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.val_mkOfMulEqOne]; rw [one_mul]
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).isUnit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha']; rw [hb']; rw [hc]; rw [mul_pow] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc]; rw [mul_comm a']; rw [← mul_assoc _ b']; rw [← mul_assoc b']; rw [mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.val_mkOfMulEqOne]; rw [ha']

/--
theorem `exists_eq_pow_of_mul_eq_pow` / 定理 `exists_eq_pow_of_mul_eq_pow`

English:
theorem exists_eq_pow_of_mul_eq_pow
  statement: [GCDMonoid α] [Subsingleton αˣ]
  proof: let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

中文:
定理 存在_eq_pow_of_mul_eq_pow
  结论: [最大公约数幺半群 α] [子单例 αˣ]
  证明: let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

Depends on / 依赖: associated_iff_eq, associated_iff_eq.mp, exists_associated_pow_of_mul_eq_pow
-/
theorem exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [Subsingleton αˣ]
    {a b c : α} (hab : IsUnit (gcd a b)) {k : Nat} (h : a * b = c ^ k) : exists d : α, a = d ^ k :=
  let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

/--
theorem `gcd_greatest` / 定理 `gcd_greatest`

English:
theorem gcd_greatest
  statement: {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α] {a b d : α}
  proof: haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)

中文:
定理 gcd_greatest
  结论: {α : 类型} [带零交换幺半群 α] [正规化最大公约数幺半群 α] {a b d : α}
  证明: haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)

Depends on / 依赖: GCDMonoid, GCDMonoid.dvd_gcd, dvd_gcd, gcd_dvd_left, gcd_dvd_right, gcd_eq_normalize
-/
theorem gcd_greatest {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e : α, e ∣ a -> e ∣ b -> e ∣ d) :
    gcd a b = normalize d :=
  haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)

/--
theorem `gcd_greatest_associated` / 定理 `gcd_greatest_associated`

English:
theorem gcd_greatest_associated
  statement: {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] {a b d : α}
  proof: haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h

中文:
定理 gcd_greatest_associated
  结论: {α : 类型} [带零交换幺半群 α] [最大公约数幺半群 α] {a b d : α}
  证明: haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h

Depends on / 依赖: GCDMonoid, GCDMonoid.dvd_gcd, associated_of_dvd_dvd, dvd_gcd, gcd_dvd_left, gcd_dvd_right
-/
theorem gcd_greatest_associated {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e : α, e ∣ a -> e ∣ b -> e ∣ d) :
    Associated d (gcd a b) :=
  haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h

/--
theorem `isUnit_gcd_of_eq_mul_gcd` / 定理 `isUnit_gcd_of_eq_mul_gcd`

English:
theorem isUnit_gcd_of_eq_mul_gcd
  statement: {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
  proof: by
  rw [← associated_one_iff_isUnit]
  refine Associated.of_mul_left ?_ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm
  rw [← ex]; rw [← ey]; rw [mul_one]

中文:
定理 isUnit_gcd_of_eq_mul_gcd
  结论: {α : 类型} [带零交换幺半群 α] [最大公约数幺半群 α]
  证明: by
  rw [← associated_one_iff_isUnit]
  refine Associated.of_mul_left ?_ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm
  rw [← ex]; rw [← ey]; rw [mul_one]

Depends on / 依赖: Associated, Associated.of_mul_left, Associated.refl, associated_one_iff_isUnit, convert, gcd_mul_left, mul_one, of_mul_left
-/
theorem isUnit_gcd_of_eq_mul_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
    {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gcd x y * y') (h : gcd x y != 0) :
    IsUnit (gcd x' y') := by
  rw [← associated_one_iff_isUnit]
  refine Associated.of_mul_left ?_ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm
  rw [← ex]; rw [← ey]; rw [mul_one]

/--
theorem `extract_gcd` / 定理 `extract_gcd`

English:
theorem extract_gcd
  given: {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] (x y : α)
  proof: by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩

中文:
定理 extract_gcd
  条件: {α : 类型} [带零交换幺半群 α] [最大公约数幺半群 α] (x y : α)
  证明: by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩

Depends on / 依赖: associated_one_iff_isUnit, gcd_dvd_left, gcd_dvd_right, gcd_eq_zero_iff, gcd_one_left, isUnit_gcd_of_eq_mul_gcd, simp_rw, zero_mul
-/
theorem extract_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] (x y : α) :
    exists x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y') := by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩

/--
theorem `associated_gcd_left_iff` / 定理 `associated_gcd_left_iff`

English:
theorem associated_gcd_left_iff
  given: [GCDMonoid α] {x y : α}
  statement: Associated x (gcd x y) ↔ x ∣ y
  proof: ⟨fun hx => hx.dvd.trans (gcd_dvd_right x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd dvd_rfl hxy) (gcd_dvd_left x y)⟩

中文:
定理 associated_gcd_left_iff
  条件: [最大公约数幺半群 α] {x y : α}
  结论: Associated x (最大公约数 x y) ↔ x ∣ y
  证明: ⟨fun hx => hx.dvd.trans (gcd_dvd_right x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd dvd_rfl hxy) (gcd_dvd_left x y)⟩

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, dvd_rfl, gcd_dvd_left, gcd_dvd_right, hx.dvd.trans
-/
theorem associated_gcd_left_iff [GCDMonoid α] {x y : α} : Associated x (gcd x y) ↔ x ∣ y :=
  ⟨fun hx => hx.dvd.trans (gcd_dvd_right x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd dvd_rfl hxy) (gcd_dvd_left x y)⟩

/--
theorem `associated_gcd_right_iff` / 定理 `associated_gcd_right_iff`

English:
theorem associated_gcd_right_iff
  given: [GCDMonoid α] {x y : α}
  statement: Associated y (gcd x y) ↔ y ∣ x
  proof: ⟨fun hx => hx.dvd.trans (gcd_dvd_left x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd hxy dvd_rfl) (gcd_dvd_right x y)⟩

中文:
定理 associated_gcd_right_iff
  条件: [最大公约数幺半群 α] {x y : α}
  结论: Associated y (最大公约数 x y) ↔ y ∣ x
  证明: ⟨fun hx => hx.dvd.trans (gcd_dvd_left x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd hxy dvd_rfl) (gcd_dvd_right x y)⟩

Depends on / 依赖: associated_of_dvd_dvd, dvd_gcd, dvd_rfl, gcd_dvd_left, gcd_dvd_right, hx.dvd.trans
-/
theorem associated_gcd_right_iff [GCDMonoid α] {x y : α} : Associated y (gcd x y) ↔ y ∣ x :=
  ⟨fun hx => hx.dvd.trans (gcd_dvd_left x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd hxy dvd_rfl) (gcd_dvd_right x y)⟩

/--
theorem `Irreducible.isUnit_gcd_iff` / 定理 `Irreducible.isUnit_gcd_iff`

English:
theorem Irreducible.isUnit_gcd_iff
  given: [GCDMonoid α] {x y : α} (hx : Irreducible x)
  proof: by
  rw [hx.isUnit_iff_not_associated_of_dvd (gcd_dvd_left x y)]; rw [not_iff_not]; rw [associated_gcd_left_iff]

中文:
定理 不可约.isUnit_gcd_iff
  条件: [最大公约数幺半群 α] {x y : α} (hx : 不可约 x)
  证明: by
  rw [hx.isUnit_iff_not_associated_of_dvd (gcd_dvd_left x y)]; rw [not_iff_not]; rw [associated_gcd_left_iff]

Depends on / 依赖: associated_gcd_left_iff, gcd_dvd_left, hx.isUnit_iff_not_associated_of_dvd, isUnit_iff_not_associated_of_dvd, not_iff_not
-/
theorem Irreducible.isUnit_gcd_iff [GCDMonoid α] {x y : α} (hx : Irreducible x) :
    IsUnit (gcd x y) ↔ ¬(x ∣ y) := by
  rw [hx.isUnit_iff_not_associated_of_dvd (gcd_dvd_left x y)]; rw [not_iff_not]; rw [associated_gcd_left_iff]

/--
theorem `Irreducible.gcd_eq_one_iff` / 定理 `Irreducible.gcd_eq_one_iff`

English:
theorem Irreducible.gcd_eq_one_iff
  given: [NormalizedGCDMonoid α] {x y : α} (hx : Irreducible x)
  proof: by
  rw [← hx.isUnit_gcd_iff]; rw [← normalize_eq_one]; rw [NormalizedGCDMonoid.normalize_gcd]

中文:
定理 不可约.gcd_eq_one_iff
  条件: [正规化最大公约数幺半群 α] {x y : α} (hx : 不可约 x)
  证明: by
  rw [← hx.isUnit_gcd_iff]; rw [← normalize_eq_one]; rw [NormalizedGCDMonoid.normalize_gcd]

Depends on / 依赖: NormalizedGCDMonoid, NormalizedGCDMonoid.normalize_gcd, hx.isUnit_gcd_iff, isUnit_gcd_iff, normalize_eq_one, normalize_gcd
-/
theorem Irreducible.gcd_eq_one_iff [NormalizedGCDMonoid α] {x y : α} (hx : Irreducible x) :
    gcd x y = 1 ↔ ¬(x ∣ y) := by
  rw [← hx.isUnit_gcd_iff]; rw [← normalize_eq_one]; rw [NormalizedGCDMonoid.normalize_gcd]

section Neg

variable [HasDistribNeg α]

/--
lemma `gcd_neg'` / 引理 `gcd_neg'`

English:
lemma gcd_neg'
  given: [GCDMonoid α] {a b : α}
  statement: Associated (gcd a (-b)) (gcd a b)
  proof: Associated.gcd .rfl (.neg_left .rfl)

中文:
引理 gcd_neg'
  条件: [最大公约数幺半群 α] {a b : α}
  结论: Associated (最大公约数 a (-b)) (最大公约数 a b)
  证明: Associated.gcd .rfl (.neg_left .rfl)

Depends on / 依赖: Associated, Associated.gcd, neg_left
-/
lemma gcd_neg' [GCDMonoid α] {a b : α} : Associated (gcd a (-b)) (gcd a b) :=
  Associated.gcd .rfl (.neg_left .rfl)

/--
lemma `gcd_neg` / 引理 `gcd_neg`

English:
lemma gcd_neg
  given: [NormalizedGCDMonoid α] {a b : α}
  statement: gcd a (-b) = gcd a b
  proof: gcd_neg'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

中文:
引理 gcd_neg
  条件: [正规化最大公约数幺半群 α] {a b : α}
  结论: 最大公约数 a (-b) = 最大公约数 a b
  证明: gcd_neg'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

Depends on / 依赖: eq_of_normalized, gcd_neg, normalize_gcd
-/
lemma gcd_neg [NormalizedGCDMonoid α] {a b : α} : gcd a (-b) = gcd a b :=
  gcd_neg'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

/--
lemma `neg_gcd'` / 引理 `neg_gcd'`

English:
lemma neg_gcd'
  given: [GCDMonoid α] {a b : α}
  statement: Associated (gcd (-a) b) (gcd a b)
  proof: Associated.gcd (.neg_left .rfl) .rfl

中文:
引理 neg_gcd'
  条件: [最大公约数幺半群 α] {a b : α}
  结论: Associated (最大公约数 (-a) b) (最大公约数 a b)
  证明: Associated.gcd (.neg_left .rfl) .rfl

Depends on / 依赖: Associated, Associated.gcd, neg_left
-/
lemma neg_gcd' [GCDMonoid α] {a b : α} : Associated (gcd (-a) b) (gcd a b) :=
  Associated.gcd (.neg_left .rfl) .rfl

/--
lemma `neg_gcd` / 引理 `neg_gcd`

English:
lemma neg_gcd
  given: [NormalizedGCDMonoid α] {a b : α}
  statement: gcd (-a) b = gcd a b
  proof: neg_gcd'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

中文:
引理 neg_gcd
  条件: [正规化最大公约数幺半群 α] {a b : α}
  结论: 最大公约数 (-a) b = 最大公约数 a b
  证明: neg_gcd'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

Depends on / 依赖: eq_of_normalized, neg_gcd, normalize_gcd
-/
lemma neg_gcd [NormalizedGCDMonoid α] {a b : α} : gcd (-a) b = gcd a b :=
  neg_gcd'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

end Neg

end GCD

section LCM

/--
theorem `lcm_dvd_iff` / 定理 `lcm_dvd_iff`

English:
theorem lcm_dvd_iff
  given: [GCDMonoid α] {a b c : α}
  statement: lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c
  proof: by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with (rfl | rfl) <;>
      simp +contextual only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, and_true, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    have h : gcd a b != 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h]; rw [(gcd_mul_lcm a b).dvd_iff_dvd_left]; rw [←
      (gcd_mul_right' c a b).dvd_iff_dvd_right]; rw [dvd_gcd_iff]; rw [mul_comm b c]; rw [mul_dvd_mul_iff_left h1]; rw [mul_dvd_mul_iff_right h2]; rw [and_comm]

中文:
定理 lcm_dvd_iff
  条件: [最大公约数幺半群 α] {a b c : α}
  结论: 最小公倍数 a b ∣ c ↔ a ∣ c ∧ b ∣ c
  证明: by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with (rfl | rfl) <;>
      simp +contextual only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, and_true, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    have h : gcd a b != 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h]; rw [(gcd_mul_lcm a b).dvd_iff_dvd_left]; rw [←
      (gcd_mul_right' c a b).dvd_iff_dvd_right]; rw [dvd_gcd_iff]; rw [mul_comm b c]; rw [mul_dvd_mul_iff_left h1]; rw [mul_dvd_mul_iff_right h2]; rw [and_comm]

Depends on / 依赖: and_c, and_true, contextual, dvd_gcd_iff, dvd_iff_dvd_left, dvd_iff_dvd_right, dvd_zero, gcd_eq_zero_iff, gcd_mul_lcm, gcd_mul_right, iff_def, imp_true_iff, lcm_zero_left, lcm_zero_right, mul_comm, mul_dvd_mul_iff_left, mul_dvd_mul_iff_right, not_or, zero_dvd_iff
-/
theorem lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with (rfl | rfl) <;>
      simp +contextual only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, and_true, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    have h : gcd a b != 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h]; rw [(gcd_mul_lcm a b).dvd_iff_dvd_left]; rw [←
      (gcd_mul_right' c a b).dvd_iff_dvd_right]; rw [dvd_gcd_iff]; rw [mul_comm b c]; rw [mul_dvd_mul_iff_left h1]; rw [mul_dvd_mul_iff_right h2]; rw [and_comm]

/--
theorem `dvd_lcm_left` / 定理 `dvd_lcm_left`

English:
theorem dvd_lcm_left
  given: [GCDMonoid α] (a b : α)
  statement: a ∣ lcm a b
  proof: (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

中文:
定理 dvd_lcm_left
  条件: [最大公约数幺半群 α] (a b : α)
  结论: a ∣ 最小公倍数 a b
  证明: (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

Depends on / 依赖: dvd_refl, lcm_dvd_iff
-/
theorem dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

/--
theorem `dvd_lcm_right` / 定理 `dvd_lcm_right`

English:
theorem dvd_lcm_right
  given: [GCDMonoid α] (a b : α)
  statement: b ∣ lcm a b
  proof: (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

中文:
定理 dvd_lcm_right
  条件: [最大公约数幺半群 α] (a b : α)
  结论: b ∣ 最小公倍数 a b
  证明: (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

Depends on / 依赖: dvd_refl, lcm_dvd_iff
-/
theorem dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

/--
theorem `lcm_dvd` / 定理 `lcm_dvd`

English:
theorem lcm_dvd
  given: [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b)
  statement: lcm a c ∣ b
  proof: lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp]

中文:
定理 lcm_dvd
  条件: [最大公约数幺半群 α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b)
  结论: 最小公倍数 a c ∣ b
  证明: lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp]

Depends on / 依赖: lcm_dvd_iff
-/
theorem lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp]
/--
theorem `lcm_eq_zero_iff` / 定理 `lcm_eq_zero_iff`

English:
theorem lcm_eq_zero_iff
  given: [GCDMonoid α] (a b : α)
  statement: lcm a b = 0 ↔ a = 0 ∨ b = 0
  proof: Iff.intro
    (fun h : lcm a b = 0 => by
have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])

中文:
定理 lcm_eq_zero_iff
  条件: [最大公约数幺半群 α] (a b : α)
  结论: 最小公倍数 a b = 0 ↔ a = 0 ∨ b = 0
  证明: Iff.intro
    (fun h : lcm a b = 0 => by
have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])

Depends on / 依赖: Associated, Iff.intro, associated_zero_iff_eq_zero, gcd_mul_lcm, lcm_zero_left, lcm_zero_right, mul_eq_zero, mul_zero, symm.trans
-/
theorem lcm_eq_zero_iff [GCDMonoid α] (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
  Iff.intro
    (fun h : lcm a b = 0 => by
have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])

/--
theorem `lcm_ne_zero_iff` / 定理 `lcm_ne_zero_iff`

English:
theorem lcm_ne_zero_iff
  given: [GCDMonoid α] {a b : α}
  statement: lcm a b != 0 ↔ a != 0 ∧ b != 0
  proof: by
  simp

@[simp]

中文:
定理 lcm_ne_zero_iff
  条件: [最大公约数幺半群 α] {a b : α}
  结论: 最小公倍数 a b != 0 ↔ a != 0 ∧ b != 0
  证明: by
  simp

@[simp]
-/
theorem lcm_ne_zero_iff [GCDMonoid α] {a b : α} : lcm a b != 0 ↔ a != 0 ∧ b != 0 := by
  simp

@[simp]
/--
theorem `normalize_lcm` / 定理 `normalize_lcm`

English:
theorem normalize_lcm
  given: [NormalizedGCDMonoid α] (a b : α)
  statement: normalize (lcm a b) = lcm a b
  proof: NormalizedGCDMonoid.normalize_lcm a b

中文:
定理 normalize_lcm
  条件: [正规化最大公约数幺半群 α] (a b : α)
  结论: normalize (最小公倍数 a b) = 最小公倍数 a b
  证明: NormalizedGCDMonoid.normalize_lcm a b

Depends on / 依赖: NormalizedGCDMonoid, NormalizedGCDMonoid.normalize_lcm, normalize_lcm
-/
theorem normalize_lcm [NormalizedGCDMonoid α] (a b : α) : normalize (lcm a b) = lcm a b :=
  NormalizedGCDMonoid.normalize_lcm a b

/--
theorem `lcm_comm` / 定理 `lcm_comm`

English:
theorem lcm_comm
  given: [NormalizedGCDMonoid α] (a b : α)
  statement: lcm a b = lcm b a
  proof: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

中文:
定理 lcm_comm
  条件: [正规化最大公约数幺半群 α] (a b : α)
  结论: 最小公倍数 a b = 最小公倍数 b a
  证明: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_lcm_left, dvd_lcm_right, lcm_dvd, normalize_lcm
-/
theorem lcm_comm [NormalizedGCDMonoid α] (a b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

/--
theorem `lcm_comm'` / 定理 `lcm_comm'`

English:
theorem lcm_comm'
  given: [GCDMonoid α] (a b : α)
  statement: Associated (lcm a b) (lcm b a)
  proof: associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

中文:
定理 lcm_comm'
  条件: [最大公约数幺半群 α] (a b : α)
  结论: Associated (最小公倍数 a b) (最小公倍数 b a)
  证明: associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

Depends on / 依赖: associated_of_dvd_dvd, dvd_lcm_left, dvd_lcm_right, lcm_dvd
-/
theorem lcm_comm' [GCDMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) :=
  associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

/--
theorem `lcm_assoc` / 定理 `lcm_assoc`

English:
theorem lcm_assoc
  given: [NormalizedGCDMonoid α] (m n k : α)
  statement: lcm (lcm m n) k = lcm m (lcm n k)
  proof: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

中文:
定理 lcm_assoc
  条件: [正规化最大公约数幺半群 α] (m n k : α)
  结论: 最小公倍数 (最小公倍数 m n) k = 最小公倍数 m (最小公倍数 n k)
  证明: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_lcm_left, dvd_lcm_right, lcm_dvd, normalize_lcm
-/
theorem lcm_assoc [NormalizedGCDMonoid α] (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

/--
theorem `lcm_assoc'` / 定理 `lcm_assoc'`

English:
theorem lcm_assoc'
  given: [GCDMonoid α] (m n k : α)
  statement: Associated (lcm (lcm m n) k) (lcm m (lcm n k))
  proof: associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

中文:
定理 lcm_assoc'
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: Associated (最小公倍数 (最小公倍数 m n) k) (最小公倍数 m (最小公倍数 n k))
  证明: associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

Depends on / 依赖: associated_of_dvd_dvd, dvd_lcm_left, dvd_lcm_right, lcm_dvd
-/
theorem lcm_assoc' [GCDMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) :=
  associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalizedGCDMonoid
  signature: α] : Std.Commutative (α
  body: lcm_comm

中文:
实例 [正规化最大公约数幺半群
  签名: α] : Std.交换 (α
  定义体: lcm_comm
-/
instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) lcm where
  comm := lcm_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalizedGCDMonoid
  signature: α] : Std.Associative (α
  body: lcm_assoc

中文:
实例 [正规化最大公约数幺半群
  签名: α] : Std.结合 (α
  定义体: lcm_assoc
-/
instance [NormalizedGCDMonoid α] : Std.Associative (α := α) lcm where
  assoc := lcm_assoc

/--
theorem `lcm_eq_normalize` / 定理 `lcm_eq_normalize`

English:
theorem lcm_eq_normalize
  statement: [NormalizedGCDMonoid α] {a b c : α} (habc : lcm a b ∣ c)
  proof: normalize_lcm a b ▸ normalize_eq_normalize habc hcab

中文:
定理 lcm_eq_normalize
  结论: [正规化最大公约数幺半群 α] {a b c : α} (habc : 最小公倍数 a b ∣ c)
  证明: normalize_lcm a b ▸ normalize_eq_normalize habc hcab

Depends on / 依赖: normalize_eq_normalize, normalize_lcm
-/
theorem lcm_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : lcm a b ∣ c)
    (hcab : c ∣ lcm a b) : lcm a b = normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab

/--
theorem `lcm_dvd_lcm` / 定理 `lcm_dvd_lcm`

English:
theorem lcm_dvd_lcm
  given: [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d)
  statement: lcm a c ∣ lcm b d
  proof: lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

中文:
定理 lcm_dvd_lcm
  条件: [最大公约数幺半群 α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d)
  结论: 最小公倍数 a c ∣ 最小公倍数 b d
  证明: lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

Depends on / 依赖: dvd_lcm_left, dvd_lcm_right, hab.trans, hcd.trans, lcm_dvd
-/
theorem lcm_dvd_lcm [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

/--
theorem `Associated.lcm` / 定理 `Associated.lcm`

English:
theorem Associated.lcm
  statement: [GCDMonoid α]
  proof: associated_of_dvd_dvd (lcm_dvd_lcm ha.dvd hb.dvd) (lcm_dvd_lcm ha.dvd' hb.dvd')

@[simp]

中文:
定理 Associated.最小公倍数
  结论: [最大公约数幺半群 α]
  证明: associated_of_dvd_dvd (lcm_dvd_lcm ha.dvd hb.dvd) (lcm_dvd_lcm ha.dvd' hb.dvd')

@[simp]
-/
protected theorem Associated.lcm [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (lcm a₁ b₁) (lcm a₂ b₂) :=
  associated_of_dvd_dvd (lcm_dvd_lcm ha.dvd hb.dvd) (lcm_dvd_lcm ha.dvd' hb.dvd')

@[simp]
/--
theorem `lcm_units_coe_left` / 定理 `lcm_units_coe_left`

English:
theorem lcm_units_coe_left
  given: [NormalizedGCDMonoid α] (u : αˣ) (a : α)
  statement: lcm (↑u) a = normalize a
  proof: lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]

中文:
定理 lcm_units_coe_left
  条件: [正规化最大公约数幺半群 α] (u : αˣ) (a : α)
  结论: 最小公倍数 (↑u) a = normalize a
  证明: lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]

Depends on / 依赖: Units.coe_dvd, coe_dvd, dvd_lcm_right, dvd_rfl, lcm_dvd, lcm_eq_normalize
-/
theorem lcm_units_coe_left [NormalizedGCDMonoid α] (u : αˣ) (a : α) : lcm (↑u) a = normalize a :=
  lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]
/--
theorem `lcm_units_coe_right` / 定理 `lcm_units_coe_right`

English:
theorem lcm_units_coe_right
  given: [NormalizedGCDMonoid α] (a : α) (u : αˣ)
  statement: lcm a ↑u = normalize a
  proof: (lcm_comm a u).trans lcm_units_coe_left _ _

@[simp]

中文:
定理 lcm_units_coe_right
  条件: [正规化最大公约数幺半群 α] (a : α) (u : αˣ)
  结论: 最小公倍数 a ↑u = normalize a
  证明: (lcm_comm a u).trans lcm_units_coe_left _ _

@[simp]

Depends on / 依赖: lcm_comm, lcm_units_coe_left
-/
theorem lcm_units_coe_right [NormalizedGCDMonoid α] (a : α) (u : αˣ) : lcm a ↑u = normalize a :=
(lcm_comm a u).trans lcm_units_coe_left _ _

@[simp]
/--
theorem `lcm_one_left` / 定理 `lcm_one_left`

English:
theorem lcm_one_left
  given: [NormalizedGCDMonoid α] (a : α)
  statement: lcm 1 a = normalize a
  proof: lcm_units_coe_left 1 a

@[simp]

中文:
定理 lcm_one_left
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最小公倍数 1 a = normalize a
  证明: lcm_units_coe_left 1 a

@[simp]

Depends on / 依赖: lcm_units_coe_left
-/
theorem lcm_one_left [NormalizedGCDMonoid α] (a : α) : lcm 1 a = normalize a :=
  lcm_units_coe_left 1 a

@[simp]
/--
theorem `lcm_one_right` / 定理 `lcm_one_right`

English:
theorem lcm_one_right
  given: [NormalizedGCDMonoid α] (a : α)
  statement: lcm a 1 = normalize a
  proof: lcm_units_coe_right a 1

@[simp]

中文:
定理 lcm_one_right
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最小公倍数 a 1 = normalize a
  证明: lcm_units_coe_right a 1

@[simp]

Depends on / 依赖: lcm_units_coe_right
-/
theorem lcm_one_right [NormalizedGCDMonoid α] (a : α) : lcm a 1 = normalize a :=
  lcm_units_coe_right a 1

@[simp]
/--
theorem `lcm_same` / 定理 `lcm_same`

English:
theorem lcm_same
  given: [NormalizedGCDMonoid α] (a : α)
  statement: lcm a a = normalize a
  proof: lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]

中文:
定理 lcm_same
  条件: [正规化最大公约数幺半群 α] (a : α)
  结论: 最小公倍数 a a = normalize a
  证明: lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]

Depends on / 依赖: dvd_lcm_left, dvd_rfl, lcm_dvd, lcm_eq_normalize
-/
theorem lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize a :=
  lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]
/--
theorem `lcm_eq_one_iff` / 定理 `lcm_eq_one_iff`

English:
theorem lcm_eq_one_iff
  given: [NormalizedGCDMonoid α] (a b : α)
  statement: lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1
  proof: Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left]; rw [normalize_coe_units]

@[simp]

中文:
定理 lcm_eq_one_iff
  条件: [正规化最大公约数幺半群 α] (a b : α)
  结论: 最小公倍数 a b = 1 ↔ a ∣ 1 ∧ b ∣ 1
  证明: Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left]; rw [normalize_coe_units]

@[simp]

Depends on / 依赖: Iff.intro, Units.mkOfMulEqOne, dvd_lcm_left, dvd_lcm_right, hc.symm, hd.symm, lcm_units_coe_left, mkOfMulEqOne, normalize_coe_units
-/
theorem lcm_eq_one_iff [NormalizedGCDMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
  Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left]; rw [normalize_coe_units]

@[simp]
/--
theorem `lcm_mul_left` / 定理 `lcm_mul_left`

English:
theorem lcm_mul_left
  given: [StrongNormalizedGCDMonoid α] (a b c : α)
  proof: (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨_, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))

@[simp]

中文:
定理 lcm_mul_left
  条件: [StrongNormalizedGCD幺半群 α] (a b c : α)
  证明: (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨_, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))

@[simp]

Depends on / 依赖: dvd_lcm_left, dvd_lcm_right, dvd_mul_right, eq.symm, lcm_dvd, lcm_eq_normalize, mul_dvd_mul_iff_left, mul_dvd_mul_left, normalize
-/
theorem lcm_mul_left [StrongNormalizedGCDMonoid α] (a b c : α) :
    lcm (a * b) (a * c) = normalize a * lcm b c :=
  (by_cases (by rintro rfl; simp))
    fun ha : a != 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨_, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))

@[simp]
/--
theorem `lcm_mul_right` / 定理 `lcm_mul_right`

English:
theorem lcm_mul_right
  given: [StrongNormalizedGCDMonoid α] (a b c : α)
  proof: by simp only [mul_comm, lcm_mul_left]

中文:
定理 lcm_mul_right
  条件: [StrongNormalizedGCD幺半群 α] (a b c : α)
  证明: by simp only [mul_comm, lcm_mul_left]

Depends on / 依赖: lcm_mul_left, mul_comm
-/
theorem lcm_mul_right [StrongNormalizedGCDMonoid α] (a b c : α) :
    lcm (b * a) (c * a) = lcm b c * normalize a := by simp only [mul_comm, lcm_mul_left]

/--
theorem `lcm_eq_left_iff` / 定理 `lcm_eq_left_iff`

English:
theorem lcm_eq_left_iff
  given: [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a)
  proof: (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

中文:
定理 lcm_eq_left_iff
  条件: [正规化最大公约数幺半群 α] (a b : α) (h : normalize a = a)
  证明: (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

Depends on / 依赖: Iff.intro, dvd_antisymm_of_normalize_eq, dvd_lcm_left, dvd_lcm_right, dvd_refl, lcm_dvd, normalize_lcm
-/
theorem lcm_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

/--
theorem `lcm_eq_right_iff` / 定理 `lcm_eq_right_iff`

English:
theorem lcm_eq_right_iff
  given: [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b)
  proof: by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

中文:
定理 lcm_eq_right_iff
  条件: [正规化最大公约数幺半群 α] (a b : α) (h : normalize b = b)
  证明: by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

Depends on / 依赖: lcm_comm, lcm_eq_left_iff
-/
theorem lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    lcm a b = b ↔ a ∣ b := by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

/--
theorem `lcm_dvd_lcm_mul_left` / 定理 `lcm_dvd_lcm_mul_left`

English:
theorem lcm_dvd_lcm_mul_left
  given: [GCDMonoid α] (m n k : α)
  statement: lcm m n ∣ lcm (k * m) n
  proof: lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

中文:
定理 lcm_dvd_lcm_mul_left
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最小公倍数 m n ∣ 最小公倍数 (k * m) n
  证明: lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

Depends on / 依赖: dvd_mul_left, dvd_rfl, lcm_dvd_lcm
-/
theorem lcm_dvd_lcm_mul_left [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

/--
theorem `lcm_dvd_lcm_mul_right` / 定理 `lcm_dvd_lcm_mul_right`

English:
theorem lcm_dvd_lcm_mul_right
  given: [GCDMonoid α] (m n k : α)
  statement: lcm m n ∣ lcm (m * k) n
  proof: lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

中文:
定理 lcm_dvd_lcm_mul_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最小公倍数 m n ∣ 最小公倍数 (m * k) n
  证明: lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

Depends on / 依赖: dvd_mul_right, dvd_rfl, lcm_dvd_lcm
-/
theorem lcm_dvd_lcm_mul_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

/--
theorem `lcm_dvd_lcm_mul_left_right` / 定理 `lcm_dvd_lcm_mul_left_right`

English:
theorem lcm_dvd_lcm_mul_left_right
  given: [GCDMonoid α] (m n k : α)
  statement: lcm m n ∣ lcm m (k * n)
  proof: lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

中文:
定理 lcm_dvd_lcm_mul_left_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最小公倍数 m n ∣ 最小公倍数 m (k * n)
  证明: lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

Depends on / 依赖: dvd_mul_left, dvd_rfl, lcm_dvd_lcm
-/
theorem lcm_dvd_lcm_mul_left_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

/--
theorem `lcm_dvd_lcm_mul_right_right` / 定理 `lcm_dvd_lcm_mul_right_right`

English:
theorem lcm_dvd_lcm_mul_right_right
  given: [GCDMonoid α] (m n k : α)
  statement: lcm m n ∣ lcm m (n * k)
  proof: lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

中文:
定理 lcm_dvd_lcm_mul_right_right
  条件: [最大公约数幺半群 α] (m n k : α)
  结论: 最小公倍数 m n ∣ 最小公倍数 m (n * k)
  证明: lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

Depends on / 依赖: dvd_mul_right, dvd_rfl, lcm_dvd_lcm
-/
theorem lcm_dvd_lcm_mul_right_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

/--
theorem `lcm_eq_of_associated_left` / 定理 `lcm_eq_of_associated_left`

English:
theorem lcm_eq_of_associated_left
  given: [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α)
  proof: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

中文:
定理 lcm_eq_of_associated_left
  条件: [正规化最大公约数幺半群 α] {m n : α} (h : Associated m n) (k : α)
  证明: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_rfl, h.dvd, h.symm.dvd, lcm_dvd_lcm, normalize_lcm
-/
theorem lcm_eq_of_associated_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

/--
theorem `lcm_eq_of_associated_right` / 定理 `lcm_eq_of_associated_right`

English:
theorem lcm_eq_of_associated_right
  given: [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α)
  proof: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

中文:
定理 lcm_eq_of_associated_right
  条件: [正规化最大公约数幺半群 α] {m n : α} (h : Associated m n) (k : α)
  证明: dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_rfl, h.dvd, h.symm.dvd, lcm_dvd_lcm, normalize_lcm
-/
theorem lcm_eq_of_associated_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

section Divisibility

variable [GCDMonoid α] {m n a b c : α}

variable (m n) in
/--
theorem `lcm_dvd_mul` / 定理 `lcm_dvd_mul`

English:
theorem lcm_dvd_mul
  statement: lcm m n ∣ m * n
  proof: lcm_dvd (by simp) (by simp)

中文:
定理 lcm_dvd_mul
  结论: 最小公倍数 m n ∣ m * n
  证明: lcm_dvd (by simp) (by simp)
-/
@[simp] theorem lcm_dvd_mul : lcm m n ∣ m * n :=
  lcm_dvd (by simp) (by simp)

/--
theorem `dvd_lcm_of_dvd_left` / 定理 `dvd_lcm_of_dvd_left`

English:
theorem dvd_lcm_of_dvd_left
  given: (h : a ∣ b) (c : α)
  statement: a ∣ lcm b c
  proof: h.trans (dvd_lcm_left b c)

alias Dvd.dvd.lcm_right := dvd_lcm_of_dvd_left

中文:
定理 dvd_lcm_of_dvd_left
  条件: (h : a ∣ b) (c : α)
  结论: a ∣ 最小公倍数 b c
  证明: h.trans (dvd_lcm_left b c)

alias Dvd.dvd.lcm_right := dvd_lcm_of_dvd_left

Depends on / 依赖: dvd_lcm_left, h.trans
-/
theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : α) : a ∣ lcm b c :=
  h.trans (dvd_lcm_left b c)

alias Dvd.dvd.lcm_right := dvd_lcm_of_dvd_left

/--
theorem `dvd_of_lcm_right_dvd` / 定理 `dvd_of_lcm_right_dvd`

English:
theorem dvd_of_lcm_right_dvd
  given: (h : lcm a b ∣ c)
  statement: a ∣ c
  proof: (dvd_lcm_left a b).trans h

中文:
定理 dvd_of_lcm_right_dvd
  条件: (h : 最小公倍数 a b ∣ c)
  结论: a ∣ c
  证明: (dvd_lcm_left a b).trans h

Depends on / 依赖: dvd_lcm_left
-/
theorem dvd_of_lcm_right_dvd (h : lcm a b ∣ c) : a ∣ c :=
  (dvd_lcm_left a b).trans h

/--
theorem `dvd_lcm_of_dvd_right` / 定理 `dvd_lcm_of_dvd_right`

English:
theorem dvd_lcm_of_dvd_right
  given: (h : a ∣ b) (c : α)
  statement: a ∣ lcm c b
  proof: h.trans (dvd_lcm_right c b)

alias Dvd.dvd.lcm_left := dvd_lcm_of_dvd_right

中文:
定理 dvd_lcm_of_dvd_right
  条件: (h : a ∣ b) (c : α)
  结论: a ∣ 最小公倍数 c b
  证明: h.trans (dvd_lcm_right c b)

alias Dvd.dvd.lcm_left := dvd_lcm_of_dvd_right

Depends on / 依赖: dvd_lcm_right, h.trans
-/
theorem dvd_lcm_of_dvd_right (h : a ∣ b) (c : α) : a ∣ lcm c b :=
  h.trans (dvd_lcm_right c b)

alias Dvd.dvd.lcm_left := dvd_lcm_of_dvd_right

/--
theorem `dvd_of_lcm_left_dvd` / 定理 `dvd_of_lcm_left_dvd`

English:
theorem dvd_of_lcm_left_dvd
  given: (h : lcm a b ∣ c)
  statement: b ∣ c
  proof: (dvd_lcm_right a b).trans h

中文:
定理 dvd_of_lcm_left_dvd
  条件: (h : 最小公倍数 a b ∣ c)
  结论: b ∣ c
  证明: (dvd_lcm_right a b).trans h

Depends on / 依赖: dvd_lcm_right
-/
theorem dvd_of_lcm_left_dvd (h : lcm a b ∣ c) : b ∣ c :=
  (dvd_lcm_right a b).trans h

namespace Prime
variable {p : α} (hp : Prime p)

include hp

/--
theorem `dvd_or_dvd_of_dvd_lcm` / 定理 `dvd_or_dvd_of_dvd_lcm`

English:
theorem dvd_or_dvd_of_dvd_lcm
  given: (h : p ∣ lcm a b)
  statement: p ∣ a ∨ p ∣ b
  proof: dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

中文:
定理 dvd_or_dvd_of_dvd_lcm
  条件: (h : p ∣ 最小公倍数 a b)
  结论: p ∣ a ∨ p ∣ b
  证明: dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

Depends on / 依赖: dvd_or_dvd, h.trans, lcm_dvd_mul
-/
theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b :=
  dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

/--
theorem `dvd_lcm` / 定理 `dvd_lcm`

English:
theorem dvd_lcm
  statement: p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b
  proof: ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

中文:
定理 dvd_lcm
  结论: p ∣ 最小公倍数 a b ↔ p ∣ a ∨ p ∣ b
  证明: ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

Depends on / 依赖: Or.elim, dvd_lcm_of_dvd_left, dvd_lcm_of_dvd_right, dvd_or_dvd_of_dvd_lcm, hp.dvd_or_dvd_of_dvd_lcm
-/
theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

/--
theorem `not_dvd_lcm` / 定理 `not_dvd_lcm`

English:
theorem not_dvd_lcm
  given: (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  statement: ¬ p ∣ lcm a b
  proof: hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

中文:
定理 not_dvd_lcm
  条件: (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  结论: ¬ p ∣ 最小公倍数 a b
  证明: hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

Depends on / 依赖: GCDMonoid, GCDMonoid.toIsIntegrallyClosed, dvd_lcm, hp.dvd_lcm.not.mpr, not_or, not_or.mpr, toIsIntegrallyClosed
-/
theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b :=
hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

end Prime

end Divisibility

end LCM

end GCDMonoid

section UniqueUnit

variable [CommMonoidWithZero α] [Subsingleton αˣ]

-- see Note [lower instance priority]
instance (priority := 100) : StrongNormalizationMonoid α where
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul _ _ := (mul_one 1).symm
  normUnit_coe_units _ := Subsingleton.elim _ _

@[deprecated (since := "2026-07-08")]
alias NormalizationMonoid.ofUniqueUnits := instStrongNormalizationMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (NormalizationMonoid α)
  body: inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

中文:
实例 :
  签名: 唯一 (Normalization幺半群 α)
  定义体: inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim
-/
instance : Unique (NormalizationMonoid α) where
  default := inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (StrongNormalizationMonoid α)
  body: inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

中文:
实例 :
  签名: 唯一 (StrongNormalization幺半群 α)
  定义体: inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim
-/
instance : Unique (StrongNormalizationMonoid α) where
  default := inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

/--
Instance `subsingleton_gcdMonoid_of_unique_units` / 实例 `subsingleton_gcdMonoid_of_unique_units`

English:
instance subsingleton_gcdMonoid_of_unique_units
  signature: : Subsingleton (GCDMonoid α)
  body: ⟨fun g₁ g₂ => by
    have hgcd : g₁.gcd = g₂.gcd := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [dvd_gcd, gcd_dvd_left, gcd_dvd_right]
    have hlcm : g₁.lcm = g₂.lcm := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [lcm_dvd, dvd_lcm_left, dvd_lcm_right]
    cases g₁
    cases g₂
    dsimp only at hgcd hlcm
    simp only [hgcd, hlcm]⟩

中文:
实例 subsingleton_gcdMonoid_of_unique_units
  签名: : 子单例 (最大公约数幺半群 α)
  定义体: ⟨fun g₁ g₂ => by
    have hgcd : g₁.gcd = g₂.gcd := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [dvd_gcd, gcd_dvd_left, gcd_dvd_right]
    have hlcm : g₁.lcm = g₂.lcm := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [lcm_dvd, dvd_lcm_left, dvd_lcm_right]
    cases g₁
    cases g₂
    dsimp only at hgcd hlcm
    simp only [hgcd, hlcm]⟩

Depends on / 依赖: allowSynthFailures, apply_rules, associated_iff_eq, associated_iff_eq.mp, associated_of_dvd_dvd, dvd_gcd, dvd_lcm_left, dvd_lcm_right, gcd_dvd_left, gcd_dvd_right, lcm_dvd
-/
instance subsingleton_gcdMonoid_of_unique_units : Subsingleton (GCDMonoid α) :=
  ⟨fun g₁ g₂ => by
    have hgcd : g₁.gcd = g₂.gcd := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [dvd_gcd, gcd_dvd_left, gcd_dvd_right]
    have hlcm : g₁.lcm = g₂.lcm := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [lcm_dvd, dvd_lcm_left, dvd_lcm_right]
    cases g₁
    cases g₂
    dsimp only at hgcd hlcm
    simp only [hgcd, hlcm]⟩

/--
Instance `subsingleton_normalizedGCDMonoid_of_unique_units` / 实例 `subsingleton_normalizedGCDMonoid_of_unique_units`

English:
instance subsingleton_normalizedGCDMonoid_of_unique_units
  signature: : Subsingleton (NormalizedGCDMonoid α)
  body: ⟨by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl⟩

中文:
实例 subsingleton_normalizedGCDMonoid_of_unique_units
  签名: : 子单例 (正规化最大公约数幺半群 α)
  定义体: ⟨by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, a_gcd, a_norm, b_gcd, b_norm
-/
instance subsingleton_normalizedGCDMonoid_of_unique_units : Subsingleton (NormalizedGCDMonoid α) :=
  ⟨by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (StrongNormalizedGCDMonoid α)
  body: by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl

@[simp]

中文:
实例 :
  签名: 子单例 (StrongNormalizedGCD幺半群 α)
  定义体: by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, a_gcd, a_norm, b_gcd, b_norm
-/
instance : Subsingleton (StrongNormalizedGCDMonoid α) where
  allEq := by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl

@[simp]
/--
theorem `normUnit_eq_one` / 定理 `normUnit_eq_one`

English:
theorem normUnit_eq_one
  given: (x : α)
  statement: normUnit x = 1
  proof: rfl

@[simp]

中文:
定理 normUnit_eq_one
  条件: (x : α)
  结论: normUnit x = 1
  证明: rfl

@[simp]
-/
theorem normUnit_eq_one (x : α) : normUnit x = 1 :=
  rfl

@[simp]
/--
theorem `normalize_eq` / 定理 `normalize_eq`

English:
theorem normalize_eq
  given: (x : α)
  statement: normalize x = x
  proof: mul_one x

中文:
定理 normalize_eq
  条件: (x : α)
  结论: normalize x = x
  证明: mul_one x

Depends on / 依赖: mul_one
-/
theorem normalize_eq (x : α) : normalize x = x :=
  mul_one x

/-- If a monoid's only unit is `1`, then it is isomorphic to its associates. -/
@[simps]
/--
Definition of `associatesEquivOfUniqueUnits` / `associatesEquivOfUniqueUnits` 的定义

English:
definition associatesEquivOfUniqueUnits
  signature: : Associates α ≃* α where
  body: Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
right_inv _ := (Associates.out_mk _).trans normalize_eq _
  map_mul' := Associates.out_mul

中文:
定义 associatesEquivOfUniqueUnits
  签名: : Associates α ≃* α where
  定义体: Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
right_inv _ := (Associates.out_mk _).trans normalize_eq _
  map_mul' := Associates.out_mul

Depends on / 依赖: Associates, Associates.out
-/
def associatesEquivOfUniqueUnits : Associates α ≃* α where
  toFun := Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
right_inv _ := (Associates.out_mk _).trans normalize_eq _
  map_mul' := Associates.out_mul

end UniqueUnit

section IsDomain

variable [CommRing α] [NormalizedGCDMonoid α]

/--
theorem `gcd_eq_of_dvd_sub_right` / 定理 `gcd_eq_of_dvd_sub_right`

English:
theorem gcd_eq_of_dvd_sub_right
  given: {a b c : α} (h : a ∣ b - c)
  statement: gcd a b = gcd a c
  proof: by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;>
    refine ⟨gcd_dvd_left _ _, ?_⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [sub_sub_cancel]
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_add]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [← add_sub_assoc]; rw [add_comm c b]; rw [add_sub_cancel_right]

中文:
定理 gcd_eq_of_dvd_sub_right
  条件: {a b c : α} (h : a ∣ b - c)
  结论: 最大公约数 a b = 最大公约数 a c
  证明: by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;>
    refine ⟨gcd_dvd_left _ _, ?_⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [sub_sub_cancel]
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_add]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [← add_sub_assoc]; rw [add_comm c b]; rw [add_sub_cancel_right]

Depends on / 依赖: dvd_antisymm_of_normalize_eq, dvd_gcd_iff, gcd_dvd_left, gcd_dvd_right, mul_add, mul_assoc, mul_sub, normalize_gcd, sub_sub_cancel
-/
theorem gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;>
    refine ⟨gcd_dvd_left _ _, ?_⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [sub_sub_cancel]
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_add]; rw [← he]; rw [← mul_assoc]; rw [← hf]; rw [← hd]; rw [← add_sub_assoc]; rw [add_comm c b]; rw [add_sub_cancel_right]

/--
theorem `gcd_eq_of_dvd_sub_left` / 定理 `gcd_eq_of_dvd_sub_left`

English:
theorem gcd_eq_of_dvd_sub_left
  given: {a b c : α} (h : a ∣ b - c)
  statement: gcd b a = gcd c a
  proof: by
  rw [gcd_comm _ a]; rw [gcd_comm _ a]; rw [gcd_eq_of_dvd_sub_right h]

中文:
定理 gcd_eq_of_dvd_sub_left
  条件: {a b c : α} (h : a ∣ b - c)
  结论: 最大公约数 b a = 最大公约数 c a
  证明: by
  rw [gcd_comm _ a]; rw [gcd_comm _ a]; rw [gcd_eq_of_dvd_sub_right h]

Depends on / 依赖: gcd_comm, gcd_eq_of_dvd_sub_right
-/
theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a]; rw [gcd_comm _ a]; rw [gcd_eq_of_dvd_sub_right h]

end IsDomain

noncomputable section Constructors

open Associates

variable [CommMonoidWithZero α]

/--
theorem `map_mk_unit_aux` / 定理 `map_mk_unit_aux`

English:
theorem map_mk_unit_aux
  statement: {f : Associates α ->* α}
  proof: Classical.choose_spec (associated_map_mk hinv a)

中文:
定理 map_mk_unit_aux
  结论: {f : Associates α ->* α}
  证明: Classical.choose_spec (associated_map_mk hinv a)
-/
private theorem map_mk_unit_aux {f : Associates α ->* α}
    (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a * ↑(Classical.choose (associated_map_mk hinv a)) = f (Associates.mk a) :=
  Classical.choose_spec (associated_map_mk hinv a)

variable [IsCancelMulZero α]

/-- Define `NormalizationMonoid` on a structure from a `MonoidHom` inverse to `Associates.mk`. -/
@[instance_reducible]
/--
Definition of `strongNormalizationMonoidOfMonoidHomRightInverse` / `strongNormalizationMonoidOfMonoidHomRightInverse` 的定义

English:
definition strongNormalizationMonoidOfMonoidHomRightInverse
  signature: [DecidableEq α] (f : Associates α ->* α)
  body: if a = 0 then 1
    else Classical.choose (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm)
  normUnit_zero := if_pos rfl
  normUnit_mul {a b} ha hb := by
    simp_rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.val_mul]
    suffices a * b * ↑(Classical.choose (associated_map_mk hinv (a * b))) =
        a * ↑(Classical.choose (associated_map_mk hinv a)) *
        (b * ↑(Classical.choose (associated_map_mk hinv b))) by
      apply mul_left_cancel₀ (mul_ne_zero ha hb) _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    rw [map_mk_unit_aux hinv a]; rw [map_mk_unit_aux hinv (a * b)]; rw [map_mk_unit_aux hinv b]; rw [←
      map_mul]; rw [Associates.mk_mul_mk]
  normUnit_coe_units u := by
    nontriviality α
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv]; rw [map_mk_unit_aux hinv u]; rw [Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_isUnit.2 ⟨u]; rw [rfl⟩)]; rw [Associates.mk_one]; rw [map_one]

@[deprecated (since := "2026-07-08")]
noncomputable alias normalizationMonoidOfMonoidHomRightInverse :=
  strongNormalizationMonoidOfMonoidHomRightInverse

中文:
定义 strongNormalizationMonoidOfMonoidHomRightInverse
  签名: [DecidableEq α] (f : Associates α ->* α)
  定义体: if a = 0 then 1
    else Classical.choose (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm)
  normUnit_zero := if_pos rfl
  normUnit_mul {a b} ha hb := by
    simp_rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.val_mul]
    suffices a * b * ↑(Classical.choose (associated_map_mk hinv (a * b))) =
        a * ↑(Classical.choose (associated_map_mk hinv a)) *
        (b * ↑(Classical.choose (associated_map_mk hinv b))) by
      apply mul_left_cancel₀ (mul_ne_zero ha hb) _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    rw [map_mk_unit_aux hinv a]; rw [map_mk_unit_aux hinv (a * b)]; rw [map_mk_unit_aux hinv b]; rw [←
      map_mul]; rw [Associates.mk_mul_mk]
  normUnit_coe_units u := by
    nontriviality α
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv]; rw [map_mk_unit_aux hinv u]; rw [Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_isUnit.2 ⟨u]; rw [rfl⟩)]; rw [Associates.mk_one]; rw [map_one]

@[deprecated (since := "2026-07-08")]
noncomputable alias normalizationMonoidOfMonoidHomRightInverse :=
  strongNormalizationMonoidOfMonoidHomRightInverse

Depends on / 依赖: Associates, Associates.mk, Associates.mk_eq_mk_iff_associated, Classical, Classical.choose, Units.ext_iff, Units.val_mul, associated_map_mk, ext_iff, if_neg, if_pos, mk_eq_mk_iff_associated, mul_ass, mul_ne_zero, normUnit_mul, normUnit_zero, simp_rw, val_mul
-/
def strongNormalizationMonoidOfMonoidHomRightInverse [DecidableEq α] (f : Associates α ->* α)
    (hinv : Function.RightInverse f Associates.mk) :
    StrongNormalizationMonoid α where
  normUnit a :=
    if a = 0 then 1
    else Classical.choose (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm)
  normUnit_zero := if_pos rfl
  normUnit_mul {a b} ha hb := by
    simp_rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.val_mul]
    suffices a * b * ↑(Classical.choose (associated_map_mk hinv (a * b))) =
        a * ↑(Classical.choose (associated_map_mk hinv a)) *
        (b * ↑(Classical.choose (associated_map_mk hinv b))) by
      apply mul_left_cancel₀ (mul_ne_zero ha hb) _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    rw [map_mk_unit_aux hinv a]; rw [map_mk_unit_aux hinv (a * b)]; rw [map_mk_unit_aux hinv b]; rw [←
      map_mul]; rw [Associates.mk_mul_mk]
  normUnit_coe_units u := by
    nontriviality α
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv]; rw [map_mk_unit_aux hinv u]; rw [Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_isUnit.2 ⟨u]; rw [rfl⟩)]; rw [Associates.mk_one]; rw [map_one]

@[deprecated (since := "2026-07-08")]
noncomputable alias normalizationMonoidOfMonoidHomRightInverse :=
  strongNormalizationMonoidOfMonoidHomRightInverse

/-- Define `GCDMonoid` on a structure just from the `gcd` and its properties. -/
@[instance_reducible]
/--
Definition of `gcdMonoidOfGCD` / `gcdMonoidOfGCD` 的定义

English:
definition gcdMonoidOfGCD
  signature: [DecidableEq α] (gcd : α -> α -> α)
  body: { gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {_ _ _} => dvd_gcd
    lcm := fun a b =>
      if a = 0 then 0 else Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl))
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
    lcm_zero_left := fun _ => if_pos rfl
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 != 0 := by
        contrapose a0
        rw [← associated_zero_iff_eq_zero]; rw [← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h]; rw [mul_zero] }

中文:
定义 gcdMonoidOfGCD
  签名: [DecidableEq α] (最大公约数 : α -> α -> α)
  定义体: { gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {_ _ _} => dvd_gcd
    lcm := fun a b =>
      if a = 0 then 0 else Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl))
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
    lcm_zero_left := fun _ => if_pos rfl
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 != 0 := by
        contrapose a0
        rw [← associated_zero_iff_eq_zero]; rw [← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h]; rw [mul_zero] }

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Dvd.intro, choose_spec, dvd_gcd, gcd_dvd_left, gcd_dvd_right, gcd_mul_lcm, if_pos, lcm_zero_left, lcm_zero_right, mul_zero, split_ifs, zero_mul
-/
noncomputable def gcdMonoidOfGCD [DecidableEq α] (gcd : α -> α -> α)
    (gcd_dvd_left : forall a b, gcd a b ∣ a) (gcd_dvd_right : forall a b, gcd a b ∣ b)
    (dvd_gcd : forall {a b c}, a ∣ c -> a ∣ b -> a ∣ gcd c b) : GCDMonoid α :=
  { gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {_ _ _} => dvd_gcd
    lcm := fun a b =>
      if a = 0 then 0 else Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl))
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
    lcm_zero_left := fun _ => if_pos rfl
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 != 0 := by
        contrapose a0
        rw [← associated_zero_iff_eq_zero]; rw [← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h]; rw [mul_zero] }

set_option backward.isDefEq.respectTransparency false in
/-- Define `NormalizedGCDMonoid` on a structure just from the `gcd` and its properties. -/
@[instance_reducible]
/--
Definition of `normalizedGCDMonoidOfGCD` / `normalizedGCDMonoidOfGCD` 的定义

English:
definition normalizedGCDMonoidOfGCD
  signature: [NormalizationMonoid α] [DecidableEq α] (gcd : α -> α -> α)
  body: { (inferInstance : NormalizationMonoid α) with
    gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd
    normalize_gcd
    lcm a b :=
      if a = 0 then 0
      else normalize (Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
    normalize_lcm a b := by split_ifs <;> simp
    gcd_mul_lcm a b := by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · exact .trans ((normalize_associated _).mul_left _)
          (.of_eq (Classical.choose_spec (_ : _ ∣ a * b)).symm)
    lcm_zero_left _ := if_pos rfl
    lcm_zero_right a := by
      split_ifs with a0
      · rfl
      let := gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right dvd_gcd
      simpa [gcd_ne_zero_of_left a0] using show GCDMonoid.gcd .. * _ = _
        from (Classical.choose_spec ((gcd_dvd_left a 0).trans (.intro 0 rfl))).symm }

中文:
定义 normalizedGCDMonoidOfGCD
  签名: [Normalization幺半群 α] [DecidableEq α] (最大公约数 : α -> α -> α)
  定义体: { (inferInstance : NormalizationMonoid α) with
    gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd
    normalize_gcd
    lcm a b :=
      if a = 0 then 0
      else normalize (Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
    normalize_lcm a b := by split_ifs <;> simp
    gcd_mul_lcm a b := by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · exact .trans ((normalize_associated _).mul_left _)
          (.of_eq (Classical.choose_spec (_ : _ ∣ a * b)).symm)
    lcm_zero_left _ := if_pos rfl
    lcm_zero_right a := by
      split_ifs with a0
      · rfl
      let := gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right dvd_gcd
      simpa [gcd_ne_zero_of_left a0] using show GCDMonoid.gcd .. * _ = _
        from (Classical.choose_spec ((gcd_dvd_left a 0).trans (.intro 0 rfl))).symm }

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Dvd.intro, NormalizationMonoid, choose_spec, dvd_gcd, gcd_dvd_left, gcd_dvd_right, gcd_mul_lcm, if_pos, lcm_zero_left, lcm_zero_right, mul_left, mul_zero, normalize, normalize_associated, normalize_gcd, normalize_lcm, of_eq
-/
noncomputable def normalizedGCDMonoidOfGCD [NormalizationMonoid α] [DecidableEq α] (gcd : α -> α -> α)
    (gcd_dvd_left : forall a b, gcd a b ∣ a) (gcd_dvd_right : forall a b, gcd a b ∣ b)
    (dvd_gcd : forall {a b c}, a ∣ c -> a ∣ b -> a ∣ gcd c b)
    (normalize_gcd : forall a b, normalize (gcd a b) = gcd a b) : NormalizedGCDMonoid α :=
  { (inferInstance : NormalizationMonoid α) with
    gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd
    normalize_gcd
    lcm a b :=
      if a = 0 then 0
      else normalize (Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
    normalize_lcm a b := by split_ifs <;> simp
    gcd_mul_lcm a b := by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · exact .trans ((normalize_associated _).mul_left _)
          (.of_eq (Classical.choose_spec (_ : _ ∣ a * b)).symm)
    lcm_zero_left _ := if_pos rfl
    lcm_zero_right a := by
      split_ifs with a0
      · rfl
      let := gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right dvd_gcd
      simpa [gcd_ne_zero_of_left a0] using show GCDMonoid.gcd .. * _ = _
        from (Classical.choose_spec ((gcd_dvd_left a 0).trans (.intro 0 rfl))).symm }

/-- Define `GCDMonoid` on a structure just from the `lcm` and its properties. -/
@[instance_reducible]
/--
Definition of `gcdMonoidOfLCM` / `gcdMonoidOfLCM` 的定义

English:
definition gcdMonoidOfLCM
  signature: [DecidableEq α] (lcm : α -> α -> α)
  body: let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm
    gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _)]
      rw [mul_comm]; rw [← Classical.choose_spec (exists_gcd a b)]
    lcm_zero_left := fun _ => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun _ => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact dvd_rfl
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
      split_ifs with h h_1
      · exact dvd_rfl
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
      split_ifs with h h_1
      · exact ab
      · exact ac
      have h0 : lcm c b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹c = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at ‹a * d != 0›
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

中文:
定义 gcdMonoidOfLCM
  签名: [DecidableEq α] (最小公倍数 : α -> α -> α)
  定义体: let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm
    gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _)]
      rw [mul_comm]; rw [← Classical.choose_spec (exists_gcd a b)]
    lcm_zero_left := fun _ => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun _ => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact dvd_rfl
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
      split_ifs with h h_1
      · exact dvd_rfl
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
      split_ifs with h h_1
      · exact ab
      · exact ac
      have h0 : lcm c b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹c = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at ‹a * d != 0›
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Dvd.intro, Dvd.intro_left, choose_spec, dvd_lcm_left, dvd_lcm_right, eq_ze, eq_zero_of_zero_dvd, exists_gcd, gcd_mul_lcm, intro_left, lcm_dvd, lcm_zero_left, lcm_zero_right, mul_comm, mul_zero, split_ifs, zero_mul
-/
noncomputable def gcdMonoidOfLCM [DecidableEq α] (lcm : α -> α -> α)
    (dvd_lcm_left : forall a b, a ∣ lcm a b) (dvd_lcm_right : forall a b, b ∣ lcm a b)
    (lcm_dvd : forall {a b c}, c ∣ a -> b ∣ a -> lcm c b ∣ a) : GCDMonoid α :=
  let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm
    gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _)]
      rw [mul_comm]; rw [← Classical.choose_spec (exists_gcd a b)]
    lcm_zero_left := fun _ => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun _ => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact dvd_rfl
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
      split_ifs with h h_1
      · exact dvd_rfl
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
      split_ifs with h h_1
      · exact ab
      · exact ac
      have h0 : lcm c b != 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con]; rw [zero_dvd_iff]; rw [mul_eq_zero] at h
        cases h
        · exact absurd ‹c = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at ‹a * d != 0›
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

set_option backward.isDefEq.respectTransparency false in
/-- Define `NormalizedGCDMonoid` on a structure just from the `lcm` and its properties. -/
@[instance_reducible]
/--
Definition of `normalizedGCDMonoidOfLCM` / `normalizedGCDMonoidOfLCM` 的定义

English:
definition normalizedGCDMonoidOfLCM
  signature: [NormalizationMonoid α] [DecidableEq α] (lcm : α -> α -> α)
  body: let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  let := gcdMonoidOfLCM lcm dvd_lcm_left dvd_lcm_right lcm_dvd
  { (inferInstance : NormalizationMonoid α) with
    lcm
gcd a b := normalize
      if a = 0 then b
      else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm a b := by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
      rw [mul_comm]
      exact ((normalize_associated _).mul_left _).trans
        (.of_eq (Classical.choose_spec (exists_gcd a b)).symm)
    normalize_lcm
    normalize_gcd a b := normalize_idem _
    lcm_zero_left _ := eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right _ := eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left a b := by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact (normalize_associated _).dvd
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right a b := by
      split_ifs with h h_1
      · exact (normalize_associated _).dvd
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd {a b c} ac ab := by
      split_ifs with h h_1
      · apply dvd_normalize_iff.2 ab
      · apply dvd_normalize_iff.2 ac
      have h0 : lcm c b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [dvd_normalize_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

中文:
定义 normalizedGCDMonoidOfLCM
  签名: [Normalization幺半群 α] [DecidableEq α] (最小公倍数 : α -> α -> α)
  定义体: let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  let := gcdMonoidOfLCM lcm dvd_lcm_left dvd_lcm_right lcm_dvd
  { (inferInstance : NormalizationMonoid α) with
    lcm
gcd a b := normalize
      if a = 0 then b
      else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm a b := by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
      rw [mul_comm]
      exact ((normalize_associated _).mul_left _).trans
        (.of_eq (Classical.choose_spec (exists_gcd a b)).symm)
    normalize_lcm
    normalize_gcd a b := normalize_idem _
    lcm_zero_left _ := eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right _ := eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left a b := by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact (normalize_associated _).dvd
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right a b := by
      split_ifs with h h_1
      · exact (normalize_associated _).dvd
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd {a b c} ac ab := by
      split_ifs with h h_1
      · apply dvd_normalize_iff.2 ab
      · apply dvd_normalize_iff.2 ac
      have h0 : lcm c b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [dvd_normalize_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

Depends on / 依赖: Classical, Classical.choose, Dvd.intro, Dvd.intro_left, NormalizationMonoid, dvd_lcm_left, dvd_lcm_right, eq_zero_of_zero_dvd, exists_gcd, gcdMonoidOfLCM, gcd_mul_lcm, intro_left, lcm_dvd, mul_comm, mul_zero, normalize, normalize_asso, split_ifs, zero_mul
-/
noncomputable def normalizedGCDMonoidOfLCM [NormalizationMonoid α] [DecidableEq α] (lcm : α -> α -> α)
    (dvd_lcm_left : forall a b, a ∣ lcm a b) (dvd_lcm_right : forall a b, b ∣ lcm a b)
    (lcm_dvd : forall {a b c}, c ∣ a -> b ∣ a -> lcm c b ∣ a)
    (normalize_lcm : forall a b, normalize (lcm a b) = lcm a b) : NormalizedGCDMonoid α :=
  let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  let := gcdMonoidOfLCM lcm dvd_lcm_left dvd_lcm_right lcm_dvd
  { (inferInstance : NormalizationMonoid α) with
    lcm
gcd a b := normalize
      if a = 0 then b
      else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm a b := by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
      rw [mul_comm]
      exact ((normalize_associated _).mul_left _).trans
        (.of_eq (Classical.choose_spec (exists_gcd a b)).symm)
    normalize_lcm
    normalize_gcd a b := normalize_idem _
    lcm_zero_left _ := eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right _ := eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left a b := by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact (normalize_associated _).dvd
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_comm]; rw [mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right a b := by
      split_ifs with h h_1
      · exact (normalize_associated _).dvd
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd a b)]; rw [mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd {a b c} ac ab := by
      split_ifs with h h_1
      · apply dvd_normalize_iff.2 ab
      · apply dvd_normalize_iff.2 ac
      have h0 : lcm c b != 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [dvd_normalize_iff]; rw [← mul_dvd_mul_iff_left h0]; rw [← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push Not at h_1
      rw [mul_comm a]; rw [← mul_assoc]; rw [mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm]; rw [mul_dvd_mul_iff_right h_1.2]
      apply ac }

/-- Define a `GCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
@[instance_reducible]
/--
Definition of `gcdMonoidOfExistsGCD` / `gcdMonoidOfExistsGCD` 的定义

English:
definition gcdMonoidOfExistsGCD
  signature: [DecidableEq α]
  body: gcdMonoidOfGCD (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

中文:
定义 gcdMonoidOfExistsGCD
  签名: [DecidableEq α]
  定义体: gcdMonoidOfGCD (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, dvd_rfl, gcdMonoidOfGCD
-/
noncomputable def gcdMonoidOfExistsGCD [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : GCDMonoid α :=
  gcdMonoidOfGCD (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
@[instance_reducible]
/--
Definition of `normalizedGCDMonoidOfExistsGCD` / `normalizedGCDMonoidOfExistsGCD` 的定义

English:
definition normalizedGCDMonoidOfExistsGCD
  signature: [NormalizationMonoid α] [DecidableEq α]
  body: normalizedGCDMonoidOfGCD (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => dvd_normalize_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

中文:
定义 normalizedGCDMonoidOfExistsGCD
  签名: [Normalization幺半群 α] [DecidableEq α]
  定义体: normalizedGCDMonoidOfGCD (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => dvd_normalize_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, dvd_normalize_iff, dvd_rfl, normalize, normalize_dvd_iff, normalize_idem, normalizedGCDMonoidOfGCD
-/
noncomputable def normalizedGCDMonoidOfExistsGCD [NormalizationMonoid α] [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfGCD (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => dvd_normalize_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

/--
Definition of `strongNormalizedGCDMonoidOfExistsGCD` / `strongNormalizedGCDMonoidOfExistsGCD` 的定义

English:
abbreviation strongNormalizedGCDMonoidOfExistsGCD
  signature: [StrongNormalizationMonoid α] [DecidableEq α]
  body: normalizedGCDMonoidOfExistsGCD h
  __ := ‹StrongNormalizationMonoid α›

中文:
缩写 strongNormalizedGCDMonoidOfExistsGCD
  签名: [StrongNormalization幺半群 α] [DecidableEq α]
  定义体: normalizedGCDMonoidOfExistsGCD h
  __ := ‹StrongNormalizationMonoid α›

Depends on / 依赖: normalizedGCDMonoidOfExistsGCD
-/
abbrev strongNormalizedGCDMonoidOfExistsGCD [StrongNormalizationMonoid α] [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : StrongNormalizedGCDMonoid α where
  __ := normalizedGCDMonoidOfExistsGCD h
  __ := ‹StrongNormalizationMonoid α›

/--
theorem `nonempty_normalizedGCDMonoid_iff_isGCDMonoid` / 定理 `nonempty_normalizedGCDMonoid_iff_isGCDMonoid`

English:
theorem nonempty_normalizedGCDMonoid_iff_isGCDMonoid
  given: {α} [CommMonoidWithZero α]
  proof: fun ⟨_⟩ => inferInstance
  mpr := fun ⟨_⟩ => by
    have := Classical.arbitrary (NormalizationMonoid α)
    classical exact ⟨normalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩

中文:
定理 nonempty_normalizedGCDMonoid_iff_isGCDMonoid
  条件: {α} [带零交换幺半群 α]
  证明: fun ⟨_⟩ => inferInstance
  mpr := fun ⟨_⟩ => by
    have := Classical.arbitrary (NormalizationMonoid α)
    classical exact ⟨normalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩
-/
theorem nonempty_normalizedGCDMonoid_iff_isGCDMonoid {α} [CommMonoidWithZero α] :
    Nonempty (NormalizedGCDMonoid α) ↔ IsGCDMonoid α where
  mp := fun ⟨_⟩ => inferInstance
  mpr := fun ⟨_⟩ => by
    have := Classical.arbitrary (NormalizationMonoid α)
    classical exact ⟨normalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩

instance (α) [CommMonoidWithZero α] [IsGCDMonoid α] : Nonempty (NormalizedGCDMonoid α) :=
  nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mpr ‹_›

/--
theorem `nonempty_strongNormalizedGCDMonoid_iff` / 定理 `nonempty_strongNormalizedGCDMonoid_iff`

English:
theorem nonempty_strongNormalizedGCDMonoid_iff
  given: {α} [CommMonoidWithZero α]
  proof: ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨⟨_⟩, ⟨_⟩⟩ => by classical exact
    ⟨strongNormalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩⟩

中文:
定理 nonempty_strongNormalizedGCDMonoid_iff
  条件: {α} [带零交换幺半群 α]
  证明: ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨⟨_⟩, ⟨_⟩⟩ => by classical exact
    ⟨strongNormalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩⟩

Depends on / 依赖: classical, dvd_gcd_iff, strongNormalizedGCDMonoidOfExistsGCD
-/
theorem nonempty_strongNormalizedGCDMonoid_iff {α} [CommMonoidWithZero α] :
    Nonempty (StrongNormalizedGCDMonoid α) ↔
    IsGCDMonoid α ∧ Nonempty (StrongNormalizationMonoid α) :=
  ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨⟨_⟩, ⟨_⟩⟩ => by classical exact
    ⟨strongNormalizedGCDMonoidOfExistsGCD fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩⟩

/-- Define a `GCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
@[instance_reducible]
/--
Definition of `gcdMonoidOfExistsLCM` / `gcdMonoidOfExistsLCM` 的定义

English:
definition gcdMonoidOfExistsLCM
  signature: [DecidableEq α]
  body: gcdMonoidOfLCM (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

中文:
定义 gcdMonoidOfExistsLCM
  签名: [DecidableEq α]
  定义体: gcdMonoidOfLCM (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, dvd_rfl, gcdMonoidOfLCM
-/
noncomputable def gcdMonoidOfExistsLCM [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : GCDMonoid α :=
  gcdMonoidOfLCM (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
@[instance_reducible]
/--
Definition of `normalizedGCDMonoidOfExistsLCM` / `normalizedGCDMonoidOfExistsLCM` 的定义

English:
definition normalizedGCDMonoidOfExistsLCM
  signature: [NormalizationMonoid α] [DecidableEq α]
  body: normalizedGCDMonoidOfLCM (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => normalize_dvd_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

中文:
定义 normalizedGCDMonoidOfExistsLCM
  签名: [Normalization幺半群 α] [DecidableEq α]
  定义体: normalizedGCDMonoidOfLCM (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => normalize_dvd_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, dvd_normalize_iff, dvd_rfl, normalize, normalize_dvd_iff, normalize_idem, normalizedGCDMonoidOfLCM
-/
noncomputable def normalizedGCDMonoidOfExistsLCM [NormalizationMonoid α] [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfLCM (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => normalize_dvd_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

/--
Definition of `strongNormalizedGCDMonoidOfExistsLCM` / `strongNormalizedGCDMonoidOfExistsLCM` 的定义

English:
abbreviation strongNormalizedGCDMonoidOfExistsLCM
  signature: [StrongNormalizationMonoid α] [DecidableEq α]
  body: normalizedGCDMonoidOfExistsLCM h
  __ := ‹StrongNormalizationMonoid α›

中文:
缩写 strongNormalizedGCDMonoidOfExistsLCM
  签名: [StrongNormalization幺半群 α] [DecidableEq α]
  定义体: normalizedGCDMonoidOfExistsLCM h
  __ := ‹StrongNormalizationMonoid α›

Depends on / 依赖: normalizedGCDMonoidOfExistsLCM
-/
abbrev strongNormalizedGCDMonoidOfExistsLCM [StrongNormalizationMonoid α] [DecidableEq α]
    (h : forall a b : α, exists c : α, forall d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : StrongNormalizedGCDMonoid α where
  __ := normalizedGCDMonoidOfExistsLCM h
  __ := ‹StrongNormalizationMonoid α›

/--
theorem `isGCDMonoid_iff_exists_gcd` / 定理 `isGCDMonoid_iff_exists_gcd`

English:
theorem isGCDMonoid_iff_exists_gcd
  given: {α} [CommMonoidWithZero α]
  proof: fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsGCD h⟩

中文:
定理 isGCDMonoid_iff_存在_gcd
  条件: {α} [带零交换幺半群 α]
  证明: fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsGCD h⟩

Depends on / 依赖: dvd_gcd_iff
-/
theorem isGCDMonoid_iff_exists_gcd {α} [CommMonoidWithZero α] :
    IsGCDMonoid α ↔ IsCancelMulZero α ∧ forall a b : α, exists c : α, forall d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c where
  mp := fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (dvd_gcd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsGCD h⟩

/--
theorem `isGCDMonoid_iff_exists_lcm` / 定理 `isGCDMonoid_iff_exists_lcm`

English:
theorem isGCDMonoid_iff_exists_lcm
  given: {α} [CommMonoidWithZero α]
  proof: fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (lcm_dvd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsLCM h⟩

中文:
定理 isGCDMonoid_iff_存在_lcm
  条件: {α} [带零交换幺半群 α]
  证明: fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (lcm_dvd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsLCM h⟩

Depends on / 依赖: lcm_dvd_iff
-/
theorem isGCDMonoid_iff_exists_lcm {α} [CommMonoidWithZero α] :
    IsGCDMonoid α ↔ IsCancelMulZero α ∧ forall a b : α, exists c : α, forall d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d where
  mp := fun ⟨_⟩ => ⟨inferInstance, fun _ _ => ⟨_, fun _ => (lcm_dvd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ => by classical exact ⟨gcdMonoidOfExistsLCM h⟩

end Constructors

namespace CommGroupWithZero

variable (G₀ : Type*) [CommGroupWithZero G₀] [DecidableEq G₀]

-- see Note [lower instance priority]
instance (priority := 100) : StrongNormalizedGCDMonoid G₀ where
  normUnit x := if h : x = 0 then 1 else (Units.mk0 x h)⁻¹
  normUnit_zero := dif_pos rfl
normUnit_mul {x y} x0 y0 := Units.ext by simp [x0, y0, mul_comm]
  normUnit_coe_units u := by simp
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  lcm a b := if a = 0 ∨ b = 0 then 0 else 1
  gcd_dvd_left a b := by simp +contextual
  gcd_dvd_right a b := by simp +contextual
  dvd_gcd {a b c} hac hab := by simp_all
  gcd_mul_lcm a b := by
    split_ifs <;> simp_all [Associated.comm]
  lcm_zero_left _ := if_pos (Or.inl rfl)
  lcm_zero_right _ := if_pos (Or.inr rfl)
  -- `split_ifs` wants to split `normalize`, so handle the cases manually
  normalize_gcd a b := if h : a = 0 ∧ b = 0 then by simp [if_pos h] else by simp [if_neg h]
  normalize_lcm a b := if h : a = 0 ∨ b = 0 then by simp [if_pos h] else by simp [if_neg h]

@[simp]
/--
theorem `coe_normUnit` / 定理 `coe_normUnit`

English:
theorem coe_normUnit
  given: {a : G₀} (h0 : a != 0)
  statement: (↑(normUnit a) : G₀) = a⁻¹
  proof: by
  simp [normUnit, h0]

中文:
定理 coe_normUnit
  条件: {a : G₀} (h0 : a != 0)
  结论: (↑(normUnit a) : G₀) = a⁻¹
  证明: by
  simp [normUnit, h0]

Depends on / 依赖: normUnit
-/
theorem coe_normUnit {a : G₀} (h0 : a != 0) : (↑(normUnit a) : G₀) = a⁻¹ := by
  simp [normUnit, h0]

/--
theorem `normalize_eq_one` / 定理 `normalize_eq_one`

English:
theorem normalize_eq_one
  given: {a : G₀} (h0 : a != 0)
  statement: normalize a = 1
  proof: by simp [normalize_apply, h0]

中文:
定理 normalize_eq_one
  条件: {a : G₀} (h0 : a != 0)
  结论: normalize a = 1
  证明: by simp [normalize_apply, h0]

Depends on / 依赖: normalize_apply
-/
theorem normalize_eq_one {a : G₀} (h0 : a != 0) : normalize a = 1 := by simp [normalize_apply, h0]

end CommGroupWithZero

namespace Associates

variable [CommMonoidWithZero α] [GCDMonoid α]

/--
Instance `instGCDMonoid` / 实例 `instGCDMonoid`

English:
instance instGCDMonoid
  signature: : GCDMonoid (Associates α) where
  body: Quotient.map₂ gcd fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.gcd hb
  lcm := Quotient.map₂ lcm fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.lcm hb
  gcd_dvd_left := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_left _ _)
  gcd_dvd_right := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_right _ _)
  dvd_gcd := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hac hbc
    exact mk_le_mk_of_dvd (dvd_gcd (dvd_of_mk_le_mk hac) (dvd_of_mk_le_mk hbc))
  gcd_mul_lcm := by
    rintro ⟨a⟩ ⟨b⟩
    rw [associated_iff_eq]
exact Quotient.sound gcd_mul_lcm _ _
lcm_zero_left := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_left _
lcm_zero_right := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_right _

中文:
实例 instGCDMonoid
  签名: : 最大公约数幺半群 (Associates α) where
  定义体: Quotient.map₂ gcd fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.gcd hb
  lcm := Quotient.map₂ lcm fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.lcm hb
  gcd_dvd_left := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_left _ _)
  gcd_dvd_right := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_right _ _)
  dvd_gcd := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hac hbc
    exact mk_le_mk_of_dvd (dvd_gcd (dvd_of_mk_le_mk hac) (dvd_of_mk_le_mk hbc))
  gcd_mul_lcm := by
    rintro ⟨a⟩ ⟨b⟩
    rw [associated_iff_eq]
exact Quotient.sound gcd_mul_lcm _ _
lcm_zero_left := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_left _
lcm_zero_right := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_right _

Depends on / 依赖: Associated, Quotient, Quotient.map, ha.gcd
-/
instance instGCDMonoid : GCDMonoid (Associates α) where
  gcd := Quotient.map₂ gcd fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.gcd hb
  lcm := Quotient.map₂ lcm fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.lcm hb
  gcd_dvd_left := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_left _ _)
  gcd_dvd_right := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_right _ _)
  dvd_gcd := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hac hbc
    exact mk_le_mk_of_dvd (dvd_gcd (dvd_of_mk_le_mk hac) (dvd_of_mk_le_mk hbc))
  gcd_mul_lcm := by
    rintro ⟨a⟩ ⟨b⟩
    rw [associated_iff_eq]
exact Quotient.sound gcd_mul_lcm _ _
lcm_zero_left := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_left _
lcm_zero_right := by rintro ⟨a⟩; exact congr_arg Associates.mk lcm_zero_right _

/--
theorem `gcd_mk_mk` / 定理 `gcd_mk_mk`

English:
theorem gcd_mk_mk
  given: {a b : α}
  statement: gcd (Associates.mk a) (Associates.mk b) = Associates.mk (gcd a b)
  proof: rfl

中文:
定理 gcd_mk_mk
  条件: {a b : α}
  结论: 最大公约数 (Associates.mk a) (Associates.mk b) = Associates.mk (最大公约数 a b)
  证明: rfl
-/
theorem gcd_mk_mk {a b : α} : gcd (Associates.mk a) (Associates.mk b) = Associates.mk (gcd a b) :=
  rfl
/--
theorem `lcm_mk_mk` / 定理 `lcm_mk_mk`

English:
theorem lcm_mk_mk
  given: {a b : α}
  statement: lcm (Associates.mk a) (Associates.mk b) = Associates.mk (lcm a b)
  proof: rfl

中文:
定理 lcm_mk_mk
  条件: {a b : α}
  结论: 最小公倍数 (Associates.mk a) (Associates.mk b) = Associates.mk (最小公倍数 a b)
  证明: rfl
-/
theorem lcm_mk_mk {a b : α} : lcm (Associates.mk a) (Associates.mk b) = Associates.mk (lcm a b) :=
  rfl

end Associates
