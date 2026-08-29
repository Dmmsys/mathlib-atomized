/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Order.Star.Prod
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`. Note that these are
  low-priority instances, in order to avoid overriding instances such as `Pow ℝ ℝ`,
  `Pow (A × B) ℝ` or `Pow (∀ i, A i) ℝ`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

@[expose] public section

open scoped NNReal

namespace NNReal

/--
Definition of `nnrpow` / `nnrpow` 的定义

English:
abbreviation nnrpow
  signature: (a : Real>=0) (b : Real>=0)
  body: a ^ (b : Real)

中文:
缩写 nnrpow
  签名: (a : 实数>=0) (b : 实数>=0)
  定义体: a ^ (b : Real)
-/
noncomputable abbrev nnrpow (a : Real>=0) (b : Real>=0) : Real>=0 := a ^ (b : Real)

/--
lemma `nnrpow_def` / 引理 `nnrpow_def`

English:
lemma nnrpow_def
  given: (a b : Real>=0)
  statement: nnrpow a b = a ^ (b : Real)
  proof: rfl

@[fun_prop]

中文:
引理 nnrpow_def
  条件: (a b : 实数>=0)
  结论: nnrpow a b = a ^ (b : 实数)
  证明: rfl

@[fun_prop]
-/
@[simp] lemma nnrpow_def (a b : Real>=0) : nnrpow a b = a ^ (b : Real) := rfl

@[fun_prop]
/--
lemma `continuous_nnrpow_const` / 引理 `continuous_nnrpow_const`

English:
lemma continuous_nnrpow_const
  given: (y : Real>=0)
  statement: Continuous (nnrpow · y)
  proof: continuous_rpow_const zero_le_coe

中文:
引理 continuous_nnrpow_const
  条件: (y : 实数>=0)
  结论: 连续 (nnrpow · y)
  证明: continuous_rpow_const zero_le_coe

Depends on / 依赖: continuous_rpow_const, zero_le_coe
-/
lemma continuous_nnrpow_const (y : Real>=0) : Continuous (nnrpow · y) :=
  continuous_rpow_const zero_le_coe

/- This is a "redeclaration" of the attribute to speed up the proofs in this file. -/
attribute [fun_prop] continuousOn_rpow_const

/--
lemma `monotone_nnrpow_const` / 引理 `monotone_nnrpow_const`

English:
lemma monotone_nnrpow_const
  given: (y : Real>=0)
  statement: Monotone (nnrpow · y)
  proof: monotone_rpow_of_nonneg zero_le_coe

中文:
引理 monotone_nnrpow_const
  条件: (y : 实数>=0)
  结论: 递增 (nnrpow · y)
  证明: monotone_rpow_of_nonneg zero_le_coe

Depends on / 依赖: monotone_rpow_of_nonneg, zero_le_coe
-/
lemma monotone_nnrpow_const (y : Real>=0) : Monotone (nnrpow · y) :=
  monotone_rpow_of_nonneg zero_le_coe

end NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module Real A] [SMulCommClass Real A A] [IsScalarTower Real A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [NonnegSpectrumClass Real A]


/- ## `nnrpow` -/

/--
Definition of `nnrpow` / `nnrpow` 的定义

English:
definition nnrpow
  signature: (a : A) (y : Real>=0)
  body: cfcₙ (NNReal.nnrpow · y) a

中文:
定义 nnrpow
  签名: (a : A) (y : 实数>=0)
  定义体: cfcₙ (NNReal.nnrpow · y) a

Depends on / 依赖: NNReal, NNReal.nnrpow, nnrpow
-/
noncomputable def nnrpow (a : A) (y : Real>=0) : A := cfcₙ (NNReal.nnrpow · y) a

/-- Enable `a ^ y` notation for `CFC.nnrpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available. -/
noncomputable instance (priority := 100) : Pow A Real>=0 where
  pow a y := nnrpow a y

@[simp]
/--
lemma `nnrpow_eq_pow` / 引理 `nnrpow_eq_pow`

English:
lemma nnrpow_eq_pow
  given: {a : A} {y : Real>=0}
  statement: nnrpow a y = a ^ y
  proof: rfl

@[simp]

中文:
引理 nnrpow_eq_pow
  条件: {a : A} {y : 实数>=0}
  结论: nnrpow a y = a ^ y
  证明: rfl

@[simp]
-/
lemma nnrpow_eq_pow {a : A} {y : Real>=0} : nnrpow a y = a ^ y := rfl

@[simp]
/--
lemma `nnrpow_nonneg` / 引理 `nnrpow_nonneg`

English:
lemma nnrpow_nonneg
  given: {a : A} {x : Real>=0}
  statement: 0 <= a ^ x
  proof: cfcₙ_predicate _ a

grind_pattern nnrpow_nonneg => NonnegSpectrumClass Real A, a ^ x

中文:
引理 nnrpow_nonneg
  条件: {a : A} {x : 实数>=0}
  结论: 0 <= a ^ x
  证明: cfcₙ_predicate _ a

grind_pattern nnrpow_nonneg => NonnegSpectrumClass Real A, a ^ x
-/
lemma nnrpow_nonneg {a : A} {x : Real>=0} : 0 <= a ^ x := cfcₙ_predicate _ a

grind_pattern nnrpow_nonneg => NonnegSpectrumClass Real A, a ^ x

/--
lemma `nnrpow_def` / 引理 `nnrpow_def`

English:
lemma nnrpow_def
  given: {a : A} {y : Real>=0}
  statement: a ^ y = cfcₙ (NNReal.nnrpow · y) a
  proof: rfl

中文:
引理 nnrpow_def
  条件: {a : A} {y : 实数>=0}
  结论: a ^ y = cfcₙ (非负实数.nnrpow · y) a
  证明: rfl
-/
lemma nnrpow_def {a : A} {y : Real>=0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a := rfl

/--
lemma `nnrpow_eq_cfcₙ_real` / 引理 `nnrpow_eq_cfcₙ_real`

English:
lemma nnrpow_eq_cfcₙ_real
  statement: [T2Space A] [IsSemitopologicalRing A] (a : A)
  proof: by
  rw [nnrpow_def]; rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr ?_
  intro x hx
  have : 0 <= x := by grind
  simp [this]

中文:
引理 nnrpow_eq_cfcₙ_real
  结论: [T2空间 A] [是Semitopological环 A] (a : A)
  证明: by
  rw [nnrpow_def]; rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr ?_
  intro x hx
  have : 0 <= x := by grind
  simp [this]

Depends on / 依赖: cfc_tac, nnrpow_def
-/
lemma nnrpow_eq_cfcₙ_real [T2Space A] [IsSemitopologicalRing A] (a : A)
    (y : Real>=0) (ha : 0 <= a := by cfc_tac) : a ^ y = cfcₙ (fun x : Real => x ^ (y : Real)) a := by
  rw [nnrpow_def]; rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr ?_
  intro x hx
  have : 0 <= x := by grind
  simp [this]

/--
lemma `nnrpow_add` / 引理 `nnrpow_add`

English:
lemma nnrpow_add
  given: {a : A} {x y : Real>=0} (hx : 0 < x) (hy : 0 < y)
  proof: by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
exact mod_cast z.rpow_add' ne_of_gt (add_pos hx hy)

@[simp]

中文:
引理 nnrpow_add
  条件: {a : A} {x y : 实数>=0} (hx : 0 < x) (hy : 0 < y)
  证明: by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
exact mod_cast z.rpow_add' ne_of_gt (add_pos hx hy)

@[simp]

Depends on / 依赖: add_pos, mod_cast, ne_of_gt, nnrpow_def, rpow_add, z.rpow_add
-/
lemma nnrpow_add {a : A} {x y : Real>=0} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
exact mod_cast z.rpow_add' ne_of_gt (add_pos hx hy)

@[simp]
/--
lemma `nnrpow_zero` / 引理 `nnrpow_zero`

English:
lemma nnrpow_zero
  given: {a : A}
  statement: a ^ (0 : Real>=0) = 0
  proof: by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

中文:
引理 nnrpow_zero
  条件: {a : A}
  结论: a ^ (0 : 实数>=0) = 0
  证明: by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

Depends on / 依赖: nnrpow_def
-/
lemma nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0 := by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

/--
lemma `nnrpow_one` / 引理 `nnrpow_one`

English:
lemma nnrpow_one
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (1 : Real>=0) = a
  proof: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : Real>=0 -> Real>=0) a = a
  rw [cfcₙ_id Real>=0 a]

中文:
引理 nnrpow_one
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (1 : 实数>=0) = a
  证明: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : Real>=0 -> Real>=0) a = a
  rw [cfcₙ_id Real>=0 a]

Depends on / 依赖: NNReal, NNReal.coe_one, NNReal.nnrpow_def, NNReal.rpow_one, cfc_tac, coe_one, nnrpow_def, rpow_one
-/
lemma nnrpow_one (a : A) (ha : 0 <= a := by cfc_tac) : a ^ (1 : Real>=0) = a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : Real>=0 -> Real>=0) a = a
  rw [cfcₙ_id Real>=0 a]

/--
lemma `nnrpow_one_eqOn` / 引理 `nnrpow_one_eqOn`

English:
lemma nnrpow_one_eqOn
  statement: (Set.Ici (0 : A)).EqOn (fun a : A => a ^ (1 : Real>=0)) id
  proof: fun _ ha => CFC.nnrpow_one _ ha

中文:
引理 nnrpow_one_eqOn
  结论: (集合.左闭右无界区间 (0 : A)).EqOn (fun a : A => a ^ (1 : 实数>=0)) id
  证明: fun _ ha => CFC.nnrpow_one _ ha

Depends on / 依赖: CFC.nnrpow_one, nnrpow_one
-/
lemma nnrpow_one_eqOn : (Set.Ici (0 : A)).EqOn (fun a : A => a ^ (1 : Real>=0)) id :=
  fun _ ha => CFC.nnrpow_one _ ha

/--
lemma `nnrpow_two` / 引理 `nnrpow_two`

English:
lemma nnrpow_two
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (2 : Real>=0) = a * a
  proof: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : Real>=0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a]; rw [cfcₙ_id Real>=0 a]

中文:
引理 nnrpow_two
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (2 : 实数>=0) = a * a
  证明: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : Real>=0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a]; rw [cfcₙ_id Real>=0 a]

Depends on / 依赖: NNReal, NNReal.coe_ofNat, NNReal.nnrpow_def, NNReal.rpow_ofNat, cfc_tac, coe_ofNat, nnrpow_def, pow_two, rpow_ofNat
-/
lemma nnrpow_two (a : A) (ha : 0 <= a := by cfc_tac) : a ^ (2 : Real>=0) = a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : Real>=0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a]; rw [cfcₙ_id Real>=0 a]

/--
lemma `nnrpow_three` / 引理 `nnrpow_three`

English:
lemma nnrpow_three
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (3 : Real>=0) = a * a * a
  proof: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : Real>=0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a]; rw [cfcₙ_mul id _ a]; rw [← mul_assoc]; rw [cfcₙ_id Real>=0 a]

@[simp]

中文:
引理 nnrpow_three
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (3 : 实数>=0) = a * a * a
  证明: by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : Real>=0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a]; rw [cfcₙ_mul id _ a]; rw [← mul_assoc]; rw [cfcₙ_id Real>=0 a]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_ofNat, NNReal.nnrpow_def, NNReal.rpow_ofNat, cfc_tac, coe_ofNat, mul_assoc, nnrpow_def, pow_three, rpow_ofNat
-/
lemma nnrpow_three (a : A) (ha : 0 <= a := by cfc_tac) : a ^ (3 : Real>=0) = a * a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : Real>=0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a]; rw [cfcₙ_mul id _ a]; rw [← mul_assoc]; rw [cfcₙ_id Real>=0 a]

@[simp]
/--
lemma `zero_nnrpow` / 引理 `zero_nnrpow`

English:
lemma zero_nnrpow
  given: {x : Real>=0}
  statement: (0 : A) ^ x = 0
  proof: by simp [nnrpow_def]

中文:
引理 zero_nnrpow
  条件: {x : 实数>=0}
  结论: (0 : A) ^ x = 0
  证明: by simp [nnrpow_def]

Depends on / 依赖: nnrpow_def
-/
lemma zero_nnrpow {x : Real>=0} : (0 : A) ^ x = 0 := by simp [nnrpow_def]

section Unique

variable [IsSemitopologicalRing A] [T2Space A]

@[simp]
/--
lemma `nnrpow_nnrpow` / 引理 `nnrpow_nnrpow`

English:
lemma nnrpow_nnrpow
  given: {a : A} {x y : Real>=0}
  statement: (a ^ x) ^ y = a ^ (x * y)
  proof: by
  by_cases ha : 0 <= a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply

中文:
引理 nnrpow_nnrpow
  条件: {a : A} {x y : 实数>=0}
  结论: (a ^ x) ^ y = a ^ (x * y)
  证明: by
  by_cases ha : 0 <= a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply

Depends on / 依赖: Real.rpow_mul, all_goals, eq_zero_or_pos, nnrpow_def, rpow_mul
-/
lemma nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y = a ^ (x * y) := by
  by_cases ha : 0 <= a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]

/--
lemma `nnrpow_nnrpow_inv` / 引理 `nnrpow_nnrpow_inv`

English:
lemma nnrpow_nnrpow_inv
  given: (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  proof: by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]

中文:
引理 nnrpow_nnrpow_inv
  条件: (a : A) {x : 实数>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  证明: by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]

Depends on / 依赖: cfc_tac, nnrpow_one
-/
lemma nnrpow_nnrpow_inv (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]

/--
lemma `nnrpow_inv_nnrpow` / 引理 `nnrpow_inv_nnrpow`

English:
lemma nnrpow_inv_nnrpow
  given: (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  proof: by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]

中文:
引理 nnrpow_inv_nnrpow
  条件: (a : A) {x : 实数>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  证明: by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]

Depends on / 依赖: cfc_tac, nnrpow_one
-/
lemma nnrpow_inv_nnrpow (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]

/--
lemma `nnrpow_inv_eq` / 引理 `nnrpow_inv_eq`

English:
lemma nnrpow_inv_eq
  statement: (a b : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  proof: ⟨fun h => nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h => nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

中文:
引理 nnrpow_inv_eq
  结论: (a b : A) {x : 实数>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
  证明: ⟨fun h => nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h => nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

Depends on / 依赖: cfc_tac, nnrpow_inv_nnrpow, nnrpow_nnrpow_inv
-/
lemma nnrpow_inv_eq (a b : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a := by cfc_tac)
    (hb : 0 <= b := by cfc_tac) : a ^ x⁻¹ = b ↔ b ^ x = a :=
  ⟨fun h => nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h => nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module Real B] [SMulCommClass Real B B] [IsScalarTower Real B B]
  [NonUnitalContinuousFunctionalCalculus Real B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus Real (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B]
  [NonnegSpectrumClass Real B] [NonnegSpectrumClass Real (A × B)]
  [StarOrderedRing B]

/--
lemma `nnrpow_map_prod` / 引理 `nnrpow_map_prod`

English:
lemma nnrpow_map_prod
  statement: {a : A} {b : B} {x : Real>=0}
  proof: by
  simp only [nnrpow_def]
  unfold nnrpow
  refine cfcₙ_map_prod (S := Real) _ a b (by fun_prop) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha, hb]

中文:
引理 nnrpow_map_prod
  结论: {a : A} {b : B} {x : 实数>=0}
  证明: by
  simp only [nnrpow_def]
  unfold nnrpow
  refine cfcₙ_map_prod (S := Real) _ a b (by fun_prop) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha, hb]

Depends on / 依赖: Prod.le_def, cfc_tac, fun_prop, le_def, nnrpow, nnrpow_def
-/
lemma nnrpow_map_prod {a : A} {b : B} {x : Real>=0}
    (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    nnrpow (a, b) x = (a ^ x, b ^ x) := by
  simp only [nnrpow_def]
  unfold nnrpow
  refine cfcₙ_map_prod (S := Real) _ a b (by fun_prop) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha, hb]

/--
lemma `nnrpow_eq_nnrpow_prod` / 引理 `nnrpow_eq_nnrpow_prod`

English:
lemma nnrpow_eq_nnrpow_prod
  statement: {a : A} {b : B} {x : Real>=0}
  proof: nnrpow_map_prod

中文:
引理 nnrpow_eq_nnrpow_prod
  结论: {a : A} {b : B} {x : 实数>=0}
  证明: nnrpow_map_prod

Depends on / 依赖: CochainComplex, CochainComplex.isZero_of_isStrictlyGE, Injective, Injective.of_iso, Int.eq_ofNat_of_zero_le, IsZero, IsZero.injective, R.cochainComplexXIso, cfc_tac, cochainComplexXIso, eq_ofNat_of_zero_le, injective, isZero_of_isStrictlyGE, nnrpow, nnrpow_map_prod, of_iso
-/
lemma nnrpow_eq_nnrpow_prod {a : A} {b : B} {x : Real>=0}
    (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    nnrpow (a, b) x = (a, b) ^ x := nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι -> Type*} [forall i, PartialOrder (C i)] [forall i, NonUnitalRing (C i)]
  [forall i, TopologicalSpace (C i)] [forall i, StarRing (C i)]
  [forall i, StarOrderedRing (C i)] [StarOrderedRing (forall i, C i)]
  [forall i, Module Real (C i)] [forall i, SMulCommClass Real (C i) (C i)] [forall i, IsScalarTower Real (C i) (C i)]
  [forall i, NonUnitalContinuousFunctionalCalculus Real (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus Real (forall i, C i) IsSelfAdjoint]
  [forall i, IsSemitopologicalRing (C i)] [forall i, T2Space (C i)]
  [NonnegSpectrumClass Real (forall i, C i)] [forall i, NonnegSpectrumClass Real (C i)]

/--
lemma `nnrpow_map_pi` / 引理 `nnrpow_map_pi`

English:
lemma nnrpow_map_pi
  given: {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <= c i := by cfc_tac)
  proof: by
  simp only [nnrpow_def]
  unfold nnrpow
  exact cfcₙ_map_pi (S := Real) _ c

中文:
引理 nnrpow_map_pi
  条件: {c : 对任意 i, C i} {x : 实数>=0} (hc : 对任意 i, 0 <= c i := by cfc_tac)
  证明: by
  simp only [nnrpow_def]
  unfold nnrpow
  exact cfcₙ_map_pi (S := Real) _ c

Depends on / 依赖: cfc_tac, nnrpow, nnrpow_def
-/
lemma nnrpow_map_pi {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <= c i := by cfc_tac) :
    nnrpow c x = fun i => (c i) ^ x := by
  simp only [nnrpow_def]
  unfold nnrpow
  exact cfcₙ_map_pi (S := Real) _ c

/--
lemma `nnrpow_eq_nnrpow_pi` / 引理 `nnrpow_eq_nnrpow_pi`

English:
lemma nnrpow_eq_nnrpow_pi
  given: {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <= c i := by cfc_tac)
  proof: nnrpow_map_pi

中文:
引理 nnrpow_eq_nnrpow_pi
  条件: {c : 对任意 i, C i} {x : 实数>=0} (hc : 对任意 i, 0 <= c i := by cfc_tac)
  证明: nnrpow_map_pi

Depends on / 依赖: HomologicalComplex, HomologicalComplex.extendMap_f, HomologicalComplex.extendSingleIso_inv_f, cat_disch, cfc_tac, extendMap_f, extendSingleIso_inv_f, nnrpow, nnrpow_map_pi
-/
lemma nnrpow_eq_nnrpow_pi {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <= c i := by cfc_tac) :
    nnrpow c x = c ^ x := nnrpow_map_pi

end pi

end Unique

/- ## `sqrt` -/

section sqrt

/--
Definition of `sqrt` / `sqrt` 的定义

English:
definition sqrt
  signature: (a : A)
  body: cfcₙ NNReal.sqrt a

@[simp]

中文:
定义 sqrt
  签名: (a : A)
  定义体: cfcₙ NNReal.sqrt a

@[simp]

Depends on / 依赖: NNReal, NNReal.sqrt
-/
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp]
/--
lemma `sqrt_nonneg` / 引理 `sqrt_nonneg`

English:
lemma sqrt_nonneg
  given: (a : A)
  statement: 0 <= sqrt a
  proof: cfcₙ_predicate _ a

grind_pattern sqrt_nonneg => NonnegSpectrumClass Real A, sqrt a

中文:
引理 sqrt_nonneg
  条件: (a : A)
  结论: 0 <= sqrt a
  证明: cfcₙ_predicate _ a

grind_pattern sqrt_nonneg => NonnegSpectrumClass Real A, sqrt a
-/
lemma sqrt_nonneg (a : A) : 0 <= sqrt a := cfcₙ_predicate _ a

grind_pattern sqrt_nonneg => NonnegSpectrumClass Real A, sqrt a

/--
lemma `sqrt_eq_nnrpow` / 引理 `sqrt_eq_nnrpow`

English:
lemma sqrt_eq_nnrpow
  given: (a : A)
  statement: sqrt a = a ^ (1 / 2 : Real>=0)
  proof: by
  simp only [sqrt]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

中文:
引理 sqrt_eq_nnrpow
  条件: (a : A)
  结论: sqrt a = a ^ (1 / 2 : 实数>=0)
  证明: by
  simp only [sqrt]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

Depends on / 依赖: NNReal, NNReal.sqrt_eq_rpow, sqrt_eq_rpow
-/
lemma sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>=0) := by
  simp only [sqrt]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

/--
lemma `sqrt_of_not_nonneg` / 引理 `sqrt_of_not_nonneg`

English:
lemma sqrt_of_not_nonneg
  given: {a : A} (ha : ¬0 <= a)
  statement: sqrt a = 0
  proof: cfcₙ_apply_of_not_predicate a ha

@[simp]

中文:
引理 sqrt_of_not_nonneg
  条件: {a : A} (ha : ¬0 <= a)
  结论: sqrt a = 0
  证明: cfcₙ_apply_of_not_predicate a ha

@[simp]

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpNat, HomologicalComplex, HomologicalComplex.extendMap_f, cochainComplexXIso, embeddingUpNat, extendMap_f
-/
lemma sqrt_of_not_nonneg {a : A} (ha : ¬0 <= a) : sqrt a = 0 :=
  cfcₙ_apply_of_not_predicate a ha

@[simp]
/--
lemma `sqrt_zero` / 引理 `sqrt_zero`

English:
lemma sqrt_zero
  statement: sqrt (0 : A) = 0
  proof: by simp [sqrt]

中文:
引理 sqrt_zero
  结论: sqrt (0 : A) = 0
  证明: by simp [sqrt]
-/
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

variable [IsSemitopologicalRing A] [T2Space A]

@[simp]
/--
lemma `nnrpow_sqrt` / 引理 `nnrpow_sqrt`

English:
lemma nnrpow_sqrt
  given: {a : A} {x : Real>=0}
  statement: (sqrt a) ^ x = a ^ (x / 2)
  proof: by
  rw [sqrt_eq_nnrpow]; rw [nnrpow_nnrpow]; rw [one_div_mul_eq_div 2 x]

中文:
引理 nnrpow_sqrt
  条件: {a : A} {x : 实数>=0}
  结论: (sqrt a) ^ x = a ^ (x / 2)
  证明: by
  rw [sqrt_eq_nnrpow]; rw [nnrpow_nnrpow]; rw [one_div_mul_eq_div 2 x]

Depends on / 依赖: nnrpow_nnrpow, one_div_mul_eq_div, sqrt_eq_nnrpow
-/
lemma nnrpow_sqrt {a : A} {x : Real>=0} : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_nnrpow]; rw [nnrpow_nnrpow]; rw [one_div_mul_eq_div 2 x]

/--
lemma `nnrpow_sqrt_two` / 引理 `nnrpow_sqrt_two`

English:
lemma nnrpow_sqrt_two
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: (sqrt a) ^ (2 : Real>=0) = a
  proof: by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]

中文:
引理 nnrpow_sqrt_two
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: (sqrt a) ^ (2 : 实数>=0) = a
  证明: by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]

Depends on / 依赖: OfNat.ofNat_ne_zero, cfc_tac, div_self, ne_eq, nnrpow_one, nnrpow_sqrt, not_false_eq_true, ofNat_ne_zero
-/
lemma nnrpow_sqrt_two (a : A) (ha : 0 <= a := by cfc_tac) : (sqrt a) ^ (2 : Real>=0) = a := by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]

/--
lemma `sqrt_mul_sqrt_self` / 引理 `sqrt_mul_sqrt_self`

English:
lemma sqrt_mul_sqrt_self
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: sqrt a * sqrt a = a
  proof: by
  rw [← nnrpow_two _]; rw [nnrpow_sqrt_two _]

@[simp]

中文:
引理 sqrt_mul_sqrt_self
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: sqrt a * sqrt a = a
  证明: by
  rw [← nnrpow_two _]; rw [nnrpow_sqrt_two _]

@[simp]

Depends on / 依赖: cfc_tac, nnrpow_sqrt_two, nnrpow_two
-/
lemma sqrt_mul_sqrt_self (a : A) (ha : 0 <= a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← nnrpow_two _]; rw [nnrpow_sqrt_two _]

@[simp]
/--
lemma `sqrt_nnrpow` / 引理 `sqrt_nnrpow`

English:
lemma sqrt_nnrpow
  given: {a : A} {x : Real>=0}
  statement: sqrt (a ^ x) = a ^ (x / 2)
  proof: by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

中文:
引理 sqrt_nnrpow
  条件: {a : A} {x : 实数>=0}
  结论: sqrt (a ^ x) = a ^ (x / 2)
  证明: by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, sqrt_eq_nnrpow
-/
lemma sqrt_nnrpow {a : A} {x : Real>=0} : sqrt (a ^ x) = a ^ (x / 2) := by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

/--
lemma `sqrt_nnrpow_two` / 引理 `sqrt_nnrpow_two`

English:
lemma sqrt_nnrpow_two
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: sqrt (a ^ (2 : Real>=0)) = a
  proof: by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]

中文:
引理 sqrt_nnrpow_two
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: sqrt (a ^ (2 : 实数>=0)) = a
  证明: by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]

Depends on / 依赖: OfNat.ofNat_ne_zero, cfc_tac, div_self, ne_eq, nnrpow_one, not_false_eq_true, ofNat_ne_zero, sqrt_nnrpow
-/
lemma sqrt_nnrpow_two (a : A) (ha : 0 <= a := by cfc_tac) : sqrt (a ^ (2 : Real>=0)) = a := by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]

/--
lemma `sqrt_mul_self` / 引理 `sqrt_mul_self`

English:
lemma sqrt_mul_self
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: sqrt (a * a) = a
  proof: by
  rw [← nnrpow_two _]; rw [sqrt_nnrpow_two _]

中文:
引理 sqrt_mul_self
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: sqrt (a * a) = a
  证明: by
  rw [← nnrpow_two _]; rw [sqrt_nnrpow_two _]

Depends on / 依赖: cfc_tac, nnrpow_two, sqrt_nnrpow_two
-/
lemma sqrt_mul_self (a : A) (ha : 0 <= a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← nnrpow_two _]; rw [sqrt_nnrpow_two _]

/--
lemma `mul_self_eq` / 引理 `mul_self_eq`

English:
lemma mul_self_eq
  given: {a b : A} (h : sqrt a = b) (ha : 0 <= a := by cfc_tac)
  proof: h ▸ sqrt_mul_sqrt_self _ ha

中文:
引理 mul_self_eq
  条件: {a b : A} (h : sqrt a = b) (ha : 0 <= a := by cfc_tac)
  证明: h ▸ sqrt_mul_sqrt_self _ ha

Depends on / 依赖: cfc_tac, sqrt_mul_sqrt_self
-/
lemma mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 <= a := by cfc_tac) :
    b * b = a :=
  h ▸ sqrt_mul_sqrt_self _ ha

/--
lemma `sqrt_unique` / 引理 `sqrt_unique`

English:
lemma sqrt_unique
  given: {a b : A} (h : b * b = a) (hb : 0 <= b := by cfc_tac)
  proof: h ▸ sqrt_mul_self b

中文:
引理 sqrt_unique
  条件: {a b : A} (h : b * b = a) (hb : 0 <= b := by cfc_tac)
  证明: h ▸ sqrt_mul_self b

Depends on / 依赖: cfc_tac, sqrt_mul_self
-/
lemma sqrt_unique {a b : A} (h : b * b = a) (hb : 0 <= b := by cfc_tac) :
    sqrt a = b :=
  h ▸ sqrt_mul_self b

/--
lemma `sqrt_eq_iff` / 引理 `sqrt_eq_iff`

English:
lemma sqrt_eq_iff
  given: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  proof: ⟨(mul_self_eq ·), (sqrt_unique ·)⟩

中文:
引理 sqrt_eq_iff
  条件: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  证明: ⟨(mul_self_eq ·), (sqrt_unique ·)⟩

Depends on / 依赖: cfc_tac, mul_self_eq, sqrt_unique
-/
lemma sqrt_eq_iff (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    sqrt a = b ↔ b * b = a :=
  ⟨(mul_self_eq ·), (sqrt_unique ·)⟩

/--
lemma `sqrt_eq_zero_iff` / 引理 `sqrt_eq_zero_iff`

English:
lemma sqrt_eq_zero_iff
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: sqrt a = 0 ↔ a = 0
  proof: by
  rw [sqrt_eq_iff a _]; rw [mul_zero]; rw [eq_comm]

中文:
引理 sqrt_eq_zero_iff
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: sqrt a = 0 ↔ a = 0
  证明: by
  rw [sqrt_eq_iff a _]; rw [mul_zero]; rw [eq_comm]

Depends on / 依赖: cfc_tac, eq_comm, mul_zero, sqrt_eq_iff
-/
lemma sqrt_eq_zero_iff (a : A) (ha : 0 <= a := by cfc_tac) : sqrt a = 0 ↔ a = 0 := by
  rw [sqrt_eq_iff a _]; rw [mul_zero]; rw [eq_comm]

/--
lemma `mul_self_eq_mul_self_iff` / 引理 `mul_self_eq_mul_self_iff`

English:
lemma mul_self_eq_mul_self_iff
  given: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  proof: ⟨fun h => sqrt_mul_self a ▸ sqrt_unique h.symm, fun h => h ▸ rfl⟩

中文:
引理 mul_self_eq_mul_self_iff
  条件: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  证明: ⟨fun h => sqrt_mul_self a ▸ sqrt_unique h.symm, fun h => h ▸ rfl⟩

Depends on / 依赖: cfc_tac, h.symm, sqrt_mul_self, sqrt_unique
-/
lemma mul_self_eq_mul_self_iff (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    a * a = b * b ↔ a = b :=
  ⟨fun h => sqrt_mul_self a ▸ sqrt_unique h.symm, fun h => h ▸ rfl⟩

/--
lemma `sqrt_eq_real_sqrt` / 引理 `sqrt_eq_real_sqrt`

English:
lemma sqrt_eq_real_sqrt
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  suffices cfcₙ (fun x : Real => √x * √x) a = cfcₙ (fun x : Real => x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ => Real.sqrt_nonneg x))] at this
exact cfcₙ_congr fun x hx => Real.mul_self_sqrt quasispectrum_nonneg_of_nonneg a ha x hx

中文:
引理 sqrt_eq_real_sqrt
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  suffices cfcₙ (fun x : Real => √x * √x) a = cfcₙ (fun x : Real => x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ => Real.sqrt_nonneg x))] at this
exact cfcₙ_congr fun x hx => Real.mul_self_sqrt quasispectrum_nonneg_of_nonneg a ha x hx

Depends on / 依赖: CFC.sqrt, Real.mul_self_sqrt, Real.sqrt, Real.sqrt_nonneg, cfc_tac, mul_self_sqrt, quasispectrum_nonneg_of_nonneg, sqrt_eq_iff, sqrt_nonneg
-/
lemma sqrt_eq_real_sqrt (a : A) (ha : 0 <= a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  suffices cfcₙ (fun x : Real => √x * √x) a = cfcₙ (fun x : Real => x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ => Real.sqrt_nonneg x))] at this
exact cfcₙ_congr fun x hx => Real.mul_self_sqrt quasispectrum_nonneg_of_nonneg a ha x hx

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module Real B] [SMulCommClass Real B B] [IsScalarTower Real B B] [StarOrderedRing B]
  [NonUnitalContinuousFunctionalCalculus Real B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus Real (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B]
  [NonnegSpectrumClass Real B] [NonnegSpectrumClass Real (A × B)]

/--
lemma `sqrt_map_prod` / 引理 `sqrt_map_prod`

English:
lemma sqrt_map_prod
  given: {a : A} {b : B} (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  proof: by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_prod

中文:
引理 sqrt_map_prod
  条件: {a : A} {b : B} (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  证明: by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_prod

Depends on / 依赖: cfc_tac, nnrpow_map_prod, sqrt_eq_nnrpow
-/
lemma sqrt_map_prod {a : A} {b : B} (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    sqrt (a, b) = (sqrt a, sqrt b) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι -> Type*} [forall i, PartialOrder (C i)] [forall i, NonUnitalRing (C i)]
  [forall i, TopologicalSpace (C i)] [forall i, StarRing (C i)]
  [forall i, StarOrderedRing (C i)] [StarOrderedRing (forall i, C i)]
  [forall i, Module Real (C i)] [forall i, SMulCommClass Real (C i) (C i)] [forall i, IsScalarTower Real (C i) (C i)]
  [forall i, NonUnitalContinuousFunctionalCalculus Real (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus Real (forall i, C i) IsSelfAdjoint]
  [forall i, IsSemitopologicalRing (C i)] [forall i, T2Space (C i)]
  [NonnegSpectrumClass Real (forall i, C i)] [forall i, NonnegSpectrumClass Real (C i)]

/--
lemma `sqrt_map_pi` / 引理 `sqrt_map_pi`

English:
lemma sqrt_map_pi
  given: {c : forall i, C i} (hc : forall i, 0 <= c i := by cfc_tac)
  proof: by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_pi

中文:
引理 sqrt_map_pi
  条件: {c : 对任意 i, C i} (hc : 对任意 i, 0 <= c i := by cfc_tac)
  证明: by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_pi

Depends on / 依赖: cfc_tac, nnrpow_map_pi, sqrt_eq_nnrpow
-/
lemma sqrt_map_pi {c : forall i, C i} (hc : forall i, 0 <= c i := by cfc_tac) :
    sqrt c = fun i => sqrt (c i) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_pi

end pi

/--
theorem `_root_.CStarAlgebra.nonneg_TFAE` / 定理 `_root_.CStarAlgebra.nonneg_TFAE`

English:
theorem _root_.CStarAlgebra.nonneg_TFAE
  given: {a : A}
  proof: by
  tfae_have 1 ↔ 9 := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  tfae_have 1 ↔ 7 := eq_comm.eq ▸ (CFC.posPart_eq_self a).symm
.mpr h⟩, tfae_have 1 ↔ 8 := ⟨fun h => ⟨h.isSelfAdjoint, negPart_eq_zero_iff a
.mp h.2⟩ fun h => negPart_eq_zero_iff a
.symm tfae_have 1 -> 2 := fun h => sqrt_mul

中文:
定理 _root_.CStar代数.nonneg_TFAE
  条件: {a : A}
  证明: by
  tfae_have 1 ↔ 9 := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  tfae_have 1 ↔ 7 := eq_comm.eq ▸ (CFC.posPart_eq_self a).symm
.mpr h⟩, tfae_have 1 ↔ 8 := ⟨fun h => ⟨h.isSelfAdjoint, negPart_eq_zero_iff a
.mp h.2⟩ fun h => negPart_eq_zero_iff a
.symm tfae_have 1 -> 2 := fun h => sqrt_mul

Depends on / 依赖: CFC.posPart_eq_self, eq_comm, eq_comm.eq, h.isSelfAdjoint, isSelfAdjoint, negPart_eq_zero_iff, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, posPart_eq_self, sqrt_mul_sqrt_self, sqrt_nonneg, tfae_have
-/
theorem _root_.CStarAlgebra.nonneg_TFAE {a : A} :
    [ 0 <= a,
      a = sqrt a * sqrt a,
      exists b : A, 0 <= b ∧ a = b * b,
      exists b : A, IsSelfAdjoint b ∧ a = b * b,
      exists b : A, a = star b * b,
      exists b : A, a = b * star b,
      a = a⁺,
      IsSelfAdjoint a ∧ a⁻ = 0,
      IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal ].TFAE := by
  tfae_have 1 ↔ 9 := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  tfae_have 1 ↔ 7 := eq_comm.eq ▸ (CFC.posPart_eq_self a).symm
.mpr h⟩, tfae_have 1 ↔ 8 := ⟨fun h => ⟨h.isSelfAdjoint, negPart_eq_zero_iff a
.mp h.2⟩ fun h => negPart_eq_zero_iff a
.symm tfae_have 1 -> 2 := fun h => sqrt_mul_sqrt_self a
  tfae_have 2 -> 3 := fun h => ⟨sqrt a, sqrt_nonneg a, h⟩
  tfae_have 3 -> 4 := fun ⟨b, hb⟩ => ⟨b, hb.1.isSelfAdjoint, hb.2⟩
  tfae_have 4 -> 5 := fun ⟨b, hb⟩ => ⟨b, hb.1.symm ▸ hb.2⟩
.symm ▸ hb⟩ tfae_have 5 -> 6 := fun ⟨b, hb⟩ => ⟨star b, star_star b
  tfae_have 6 -> 1 := fun ⟨b, hb⟩ => hb ▸ mul_star_self_nonneg _
  tfae_finish

/--
theorem `_root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt` / 定理 `_root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt`

English:
theorem _root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 1

中文:
定理 _root_.CStar代数.nonneg_iff_eq_sqrt_mul_sqrt
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 1

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt {a : A} :
    0 <= a ↔ a = sqrt a * sqrt a := CStarAlgebra.nonneg_TFAE.out 0 1
/--
theorem `_root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self` / 定理 `_root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self`

English:
theorem _root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 2

中文:
定理 _root_.CStar代数.nonneg_iff_存在_nonneg_and_eq_mul_self
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 2

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self {a : A} :
    0 <= a ↔ exists b, 0 <= b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 2
/--
theorem `_root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self` / 定理 `_root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self`

English:
theorem _root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 3

中文:
定理 _root_.CStar代数.nonneg_iff_存在_isSelfAdjoint_and_eq_mul_self
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 3

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self {a : A} :
    0 <= a ↔ exists b, IsSelfAdjoint b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 3
/--
theorem `_root_.CStarAlgebra.nonneg_iff_eq_star_mul_self` / 定理 `_root_.CStarAlgebra.nonneg_iff_eq_star_mul_self`

English:
theorem _root_.CStarAlgebra.nonneg_iff_eq_star_mul_self
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 4

中文:
定理 _root_.CStar代数.nonneg_iff_eq_star_mul_self
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 4

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_star_mul_self {a : A} :
    0 <= a ↔ exists b, a = star b * b := CStarAlgebra.nonneg_TFAE.out 0 4
/--
theorem `_root_.CStarAlgebra.nonneg_iff_eq_mul_star_self` / 定理 `_root_.CStarAlgebra.nonneg_iff_eq_mul_star_self`

English:
theorem _root_.CStarAlgebra.nonneg_iff_eq_mul_star_self
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 5

中文:
定理 _root_.CStar代数.nonneg_iff_eq_mul_star_self
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 5

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_mul_star_self {a : A} :
    0 <= a ↔ exists b, a = b * star b := CStarAlgebra.nonneg_TFAE.out 0 5
/--
theorem `_root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero` / 定理 `_root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero`

English:
theorem _root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero
  given: {a : A}
  proof: CStarAlgebra.nonneg_TFAE.out 0 7

中文:
定理 _root_.CStar代数.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero
  条件: {a : A}
  证明: CStarAlgebra.nonneg_TFAE.out 0 7

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_TFAE.out, nonneg_TFAE
-/
theorem _root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero {a : A} :
    0 <= a ↔ IsSelfAdjoint a ∧ a⁻ = 0 := CStarAlgebra.nonneg_TFAE.out 0 7

end sqrt

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra Real A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [NonnegSpectrumClass Real A]

/- ## `rpow` -/

/--
Definition of `rpow` / `rpow` 的定义

English:
definition rpow
  signature: (a : A) (y : Real)
  body: cfc (fun x : Real>=0 => x ^ y) a

中文:
定义 rpow
  签名: (a : A) (y : 实数)
  定义体: cfc (fun x : Real>=0 => x ^ y) a
-/
noncomputable def rpow (a : A) (y : Real) : A := cfc (fun x : Real>=0 => x ^ y) a

/-- Enable `a ^ y` notation for `CFC.rpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available (such as `Pow ℝ ℝ`). -/
noncomputable instance (priority := 100) : Pow A Real where
  pow a y := rpow a y

@[simp]
/--
lemma `rpow_eq_pow` / 引理 `rpow_eq_pow`

English:
lemma rpow_eq_pow
  given: {a : A} {y : Real}
  statement: rpow a y = a ^ y
  proof: rfl

@[simp]

中文:
引理 rpow_eq_pow
  条件: {a : A} {y : 实数}
  结论: rpow a y = a ^ y
  证明: rfl

@[simp]
-/
lemma rpow_eq_pow {a : A} {y : Real} : rpow a y = a ^ y := rfl

@[simp]
/--
lemma `rpow_nonneg` / 引理 `rpow_nonneg`

English:
lemma rpow_nonneg
  given: {a : A} {y : Real}
  statement: 0 <= a ^ y
  proof: cfc_predicate _ a

grind_pattern rpow_nonneg => NonnegSpectrumClass Real A, a ^ y

中文:
引理 rpow_nonneg
  条件: {a : A} {y : 实数}
  结论: 0 <= a ^ y
  证明: cfc_predicate _ a

grind_pattern rpow_nonneg => NonnegSpectrumClass Real A, a ^ y

Depends on / 依赖: cfc_predicate
-/
lemma rpow_nonneg {a : A} {y : Real} : 0 <= a ^ y := cfc_predicate _ a

grind_pattern rpow_nonneg => NonnegSpectrumClass Real A, a ^ y

/--
lemma `rpow_def` / 引理 `rpow_def`

English:
lemma rpow_def
  given: {a : A} {y : Real}
  statement: a ^ y = cfc (fun x : Real>=0 => x ^ y) a
  proof: rfl

中文:
引理 rpow_def
  条件: {a : A} {y : 实数}
  结论: a ^ y = cfc (fun x : 实数>=0 => x ^ y) a
  证明: rfl
-/
lemma rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0 => x ^ y) a := rfl

/--
lemma `rpow_eq_cfc_real` / 引理 `rpow_eq_cfc_real`

English:
lemma rpow_eq_cfc_real
  statement: [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real}
  proof: by
  rw [CFC.rpow_def]; rw [cfc_nnreal_eq_real ..]
  refine cfc_congr ?_
  intro x hx
  simp only [NNReal.coe_rpow, Real.coe_toNNReal']
  grind

中文:
引理 rpow_eq_cfc_real
  结论: [是Semitopological环 A] [T2空间 A] {a : A} {y : 实数}
  证明: by
  rw [CFC.rpow_def]; rw [cfc_nnreal_eq_real ..]
  refine cfc_congr ?_
  intro x hx
  simp only [NNReal.coe_rpow, Real.coe_toNNReal']
  grind

Depends on / 依赖: CFC.rpow_def, NNReal, NNReal.coe_rpow, Real.coe_toNNReal, cfc_congr, cfc_nnreal_eq_real, cfc_tac, coe_rpow, coe_toNNReal, rpow_def
-/
lemma rpow_eq_cfc_real [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real}
    (ha : 0 <= a := by cfc_tac) : a ^ y = cfc (fun x : Real => x ^ y) a := by
  rw [CFC.rpow_def]; rw [cfc_nnreal_eq_real ..]
  refine cfc_congr ?_
  intro x hx
  simp only [NNReal.coe_rpow, Real.coe_toNNReal']
  grind

/--
lemma `cfc_rpow` / 引理 `cfc_rpow`

English:
lemma cfc_rpow
  statement: [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real} {f : Real -> Real}
  proof: by
  have hg : ContinuousOn (fun r => r ^ y) (f '' spectrum Real a) :=
    ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
  rw [CFC.rpow_eq_cfc_real (by grind [cfc_nonneg]), ← cfc_comp _ _ a ha]
  rfl

中文:
引理 cfc_rpow
  结论: [是Semitopological环 A] [T2空间 A] {a : A} {y : 实数} {f : 实数 -> 实数}
  证明: by
  have hg : ContinuousOn (fun r => r ^ y) (f '' spectrum Real a) :=
    ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
  rw [CFC.rpow_eq_cfc_real (by grind [cfc_nonneg]), ← cfc_comp _ _ a ha]
  rfl

Depends on / 依赖: CFC.rpow_eq_cfc_real, ContinuousOn, ContinuousOn.rpow_const, IsSelfAdjoint, cfc_comp, cfc_cont_tac, cfc_nonneg, cfc_tac, fun_prop, rpow_const, rpow_eq_cfc_real, spectrum
-/
lemma cfc_rpow [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real} {f : Real -> Real}
    (hf₁ : forall x in spectrum Real a, 0 < f x) (hf₂ : ContinuousOn f (spectrum Real a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) : cfc f a ^ y = cfc (fun r => f r ^ y) a := by
  have hg : ContinuousOn (fun r => r ^ y) (f '' spectrum Real a) :=
    ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
  rw [CFC.rpow_eq_cfc_real (by grind [cfc_nonneg]), ← cfc_comp _ _ a ha]
  rfl

/--
lemma `rpow_one` / 引理 `rpow_one`

English:
lemma rpow_one
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (1 : Real) = a
  proof: by
  simp only [rpow_def, NNReal.rpow_one, cfc_id' Real>=0 a]

@[simp]

中文:
引理 rpow_one
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (1 : 实数) = a
  证明: by
  simp only [rpow_def, NNReal.rpow_one, cfc_id' Real>=0 a]

@[simp]

Depends on / 依赖: NNReal, NNReal.rpow_one, cfc_id, cfc_tac, rpow_def, rpow_one
-/
lemma rpow_one (a : A) (ha : 0 <= a := by cfc_tac) : a ^ (1 : Real) = a := by
  simp only [rpow_def, NNReal.rpow_one, cfc_id' Real>=0 a]

@[simp]
/--
lemma `one_rpow` / 引理 `one_rpow`

English:
lemma one_rpow
  given: {x : Real}
  statement: (1 : A) ^ x = (1 : A)
  proof: by simp [rpow_def]

中文:
引理 one_rpow
  条件: {x : 实数}
  结论: (1 : A) ^ x = (1 : A)
  证明: by simp [rpow_def]

Depends on / 依赖: rpow_def
-/
lemma one_rpow {x : Real} : (1 : A) ^ x = (1 : A) := by simp [rpow_def]

/--
lemma `rpow_zero` / 引理 `rpow_zero`

English:
lemma rpow_zero
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (0 : Real) = 1
  proof: by
  simp [rpow_def, cfc_const_one Real>=0 a]

中文:
引理 rpow_zero
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (0 : 实数) = 1
  证明: by
  simp [rpow_def, cfc_const_one Real>=0 a]

Depends on / 依赖: cfc_const_one, cfc_tac, rpow_def
-/
lemma rpow_zero (a : A) (ha : 0 <= a := by cfc_tac) : a ^ (0 : Real) = 1 := by
  simp [rpow_def, cfc_const_one Real>=0 a]

/--
lemma `rpow_zero_eqOn` / 引理 `rpow_zero_eqOn`

English:
lemma rpow_zero_eqOn
  statement: (Set.Ici (0 : A)).EqOn (fun a => a ^ (0 : Real)) (fun _ => 1)
  proof: by
  intro a ha
  simp [rpow_zero a ha]

中文:
引理 rpow_zero_eqOn
  结论: (集合.左闭右无界区间 (0 : A)).EqOn (fun a => a ^ (0 : 实数)) (fun _ => 1)
  证明: by
  intro a ha
  simp [rpow_zero a ha]

Depends on / 依赖: Injective, Injective.injective_under, injective_under, rpow_zero
-/
lemma rpow_zero_eqOn : (Set.Ici (0 : A)).EqOn (fun a => a ^ (0 : Real)) (fun _ => 1) := by
  intro a ha
  simp [rpow_zero a ha]

/--
lemma `zero_rpow` / 引理 `zero_rpow`

English:
lemma zero_rpow
  given: {x : Real} (hx : x != 0)
  statement: rpow (0 : A) x = 0
  proof: by simp [rpow, NNReal.zero_rpow hx]

中文:
引理 zero_rpow
  条件: {x : 实数} (hx : x != 0)
  结论: rpow (0 : A) x = 0
  证明: by simp [rpow, NNReal.zero_rpow hx]

Depends on / 依赖: HasInjectiveResolution, NNReal, NNReal.zero_rpow, zero_rpow
-/
lemma zero_rpow {x : Real} (hx : x != 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]

/--
lemma `rpow_natCast` / 引理 `rpow_natCast`

English:
lemma rpow_natCast
  given: (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac)
  statement: a ^ (n : Real) = a ^ n
  proof: by
  rw [← cfc_pow_id (R := Real>=0) a n]; rw [rpow_def]
  congr
  simp

@[simp]

中文:
引理 rpow_natCast
  条件: (a : A) (n : 自然数) (ha : 0 <= a := by cfc_tac)
  结论: a ^ (n : 实数) = a ^ n
  证明: by
  rw [← cfc_pow_id (R := Real>=0) a n]; rw [rpow_def]
  congr
  simp

@[simp]

Depends on / 依赖: HasInjectiveResolutions, cfc_pow_id, cfc_tac, rpow_def
-/
lemma rpow_natCast (a : A) (n : Nat) (ha : 0 <= a := by cfc_tac) : a ^ (n : Real) = a ^ n := by
  rw [← cfc_pow_id (R := Real>=0) a n]; rw [rpow_def]
  congr
  simp

@[simp]
/--
lemma `rpow_algebraMap` / 引理 `rpow_algebraMap`

English:
lemma rpow_algebraMap
  given: {x : Real>=0} {y : Real}
  proof: by
  rw [rpow_def]; rw [cfc_algebraMap ..]

中文:
引理 rpow_algebraMap
  条件: {x : 实数>=0} {y : 实数}
  证明: by
  rw [rpow_def]; rw [cfc_algebraMap ..]

Depends on / 依赖: cfc_algebraMap, rpow_def
-/
lemma rpow_algebraMap {x : Real>=0} {y : Real} :
    (algebraMap Real>=0 A x) ^ y = algebraMap Real>=0 A (x ^ y) := by
  rw [rpow_def]; rw [cfc_algebraMap ..]

/--
lemma `rpow_add` / 引理 `rpow_add`

English:
lemma rpow_add
  given: {a : A} {x y : Real} (ha : IsUnit a)
  proof: by
  have ha' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  simp only [rpow_def]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z != 0 := by aesop
  simp [NNReal.rpow_add this _ _]

中文:
引理 rpow_add
  条件: {a : A} {x y : 实数} (ha : 是单位 a)
  证明: by
  have ha' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  simp only [rpow_def]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z != 0 := by aesop
  simp [NNReal.rpow_add this _ _]

Depends on / 依赖: NNReal, NNReal.rpow_add, cfc_congr, cfc_mul, rpow_add, rpow_def, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma rpow_add {a : A} {x y : Real} (ha : IsUnit a) :
    a ^ (x + y) = a ^ x * a ^ y := by
  have ha' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  simp only [rpow_def]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z != 0 := by aesop
  simp [NNReal.rpow_add this _ _]

/--
lemma `rpow_rpow` / 引理 `rpow_rpow`

English:
lemma rpow_rpow
  statement: [IsSemitopologicalRing A] [T2Space A]
  proof: by
  have ha₁' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha.isUnit
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha.nonneg]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

中文:
引理 rpow_rpow
  结论: [是Semitopological环 A] [T2空间 A]
  证明: by
  have ha₁' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha.isUnit
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha.nonneg]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

Depends on / 依赖: NNReal, NNReal.rpow_mul, cfc_comp, cfc_congr, cfc_tac, ha.isUnit, ha.nonneg, isUnit, nonneg, rpow_def, rpow_mul, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma rpow_rpow [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x) ^ y = a ^ (x * y) := by
  have ha₁' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha.isUnit
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha.nonneg]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

/--
lemma `rpow_rpow_inv` / 引理 `rpow_rpow_inv`

English:
lemma rpow_rpow_inv
  statement: [IsSemitopologicalRing A] [T2Space A]
  proof: by
  rw [rpow_rpow a x x⁻¹ hx]; rw [mul_inv_cancel₀ hx]; rw [rpow_one a ha.nonneg]

中文:
引理 rpow_rpow_inv
  结论: [是Semitopological环 A] [T2空间 A]
  证明: by
  rw [rpow_rpow a x x⁻¹ hx]; rw [mul_inv_cancel₀ hx]; rw [rpow_one a ha.nonneg]

Depends on / 依赖: cfc_tac, ha.nonneg, nonneg, rpow_one, rpow_rpow
-/
lemma rpow_rpow_inv [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  rw [rpow_rpow a x x⁻¹ hx]; rw [mul_inv_cancel₀ hx]; rw [rpow_one a ha.nonneg]

/--
lemma `rpow_inv_rpow` / 引理 `rpow_inv_rpow`

English:
lemma rpow_inv_rpow
  statement: [IsSemitopologicalRing A] [T2Space A]
  proof: by
  simpa using rpow_rpow_inv a x⁻¹ (inv_ne_zero hx)

中文:
引理 rpow_inv_rpow
  结论: [是Semitopological环 A] [T2空间 A]
  证明: by
  simpa using rpow_rpow_inv a x⁻¹ (inv_ne_zero hx)

Depends on / 依赖: cfc_tac, inv_ne_zero, rpow_rpow_inv
-/
lemma rpow_inv_rpow [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simpa using rpow_rpow_inv a x⁻¹ (inv_ne_zero hx)

/--
lemma `rpow_rpow_of_exponent_nonneg` / 引理 `rpow_rpow_of_exponent_nonneg`

English:
lemma rpow_rpow_of_exponent_nonneg
  statement: [IsSemitopologicalRing A] [T2Space A] (a : A) (x y : Real)
  proof: by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

中文:
引理 rpow_rpow_of_exponent_nonneg
  结论: [是Semitopological环 A] [T2空间 A] (a : A) (x y : 实数)
  证明: by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

Depends on / 依赖: NNReal, NNReal.rpow_mul, cfc_comp, cfc_congr, cfc_tac, rpow_def, rpow_mul
-/
lemma rpow_rpow_of_exponent_nonneg [IsSemitopologicalRing A] [T2Space A] (a : A) (x y : Real)
    (hx : 0 <= x) (hy : 0 <= y) (ha : 0 <= a := by cfc_tac) : (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

/--
lemma `rpow_mul_rpow_neg` / 引理 `rpow_mul_rpow_neg`

English:
lemma rpow_mul_rpow_neg
  given: {a : A} (x : Real) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by
  rw [← rpow_add ha.isUnit]; rw [add_neg_cancel]; rw [rpow_zero a]

中文:
引理 rpow_mul_rpow_neg
  条件: {a : A} (x : 实数) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by
  rw [← rpow_add ha.isUnit]; rw [add_neg_cancel]; rw [rpow_zero a]

Depends on / 依赖: add_neg_cancel, cfc_tac, ha.isUnit, isUnit, rpow_add, rpow_zero
-/
lemma rpow_mul_rpow_neg {a : A} (x : Real) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ x * a ^ (-x) = 1 := by
  rw [← rpow_add ha.isUnit]; rw [add_neg_cancel]; rw [rpow_zero a]

/--
lemma `rpow_neg_mul_rpow` / 引理 `rpow_neg_mul_rpow`

English:
lemma rpow_neg_mul_rpow
  given: {a : A} (x : Real) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by
  rw [← rpow_add ha.isUnit]; rw [neg_add_cancel]; rw [rpow_zero a]

中文:
引理 rpow_neg_mul_rpow
  条件: {a : A} (x : 实数) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by
  rw [← rpow_add ha.isUnit]; rw [neg_add_cancel]; rw [rpow_zero a]

Depends on / 依赖: cfc_tac, ha.isUnit, isUnit, neg_add_cancel, rpow_add, rpow_zero
-/
lemma rpow_neg_mul_rpow {a : A} (x : Real) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ (-x) * a ^ x = 1 := by
  rw [← rpow_add ha.isUnit]; rw [neg_add_cancel]; rw [rpow_zero a]

/--
lemma `rpow_neg_one_eq_inv` / 引理 `rpow_neg_one_eq_inv`

English:
lemma rpow_neg_one_eq_inv
  given: (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac)
  proof: by
.symm refine a.inv_eq_of_mul_eq_one_left ?_
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 (a.isStrictlyPositive_iff.mpr ha)

中文:
引理 rpow_neg_one_eq_inv
  条件: (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac)
  证明: by
.symm refine a.inv_eq_of_mul_eq_one_left ?_
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 (a.isStrictlyPositive_iff.mpr ha)

Depends on / 依赖: NatTrans, NatTrans.mono_iff_mono_app, a.inv_eq_of_mul_eq_one_left, a.isStrictlyPositive_iff.mpr, cfc_tac, infer_instance, inv_eq_of_mul_eq_one_left, isStrictlyPositive_iff, mono_iff_mono_app, rpow_neg_mul_rpow, rpow_one
-/
lemma rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac) :
    a ^ (-1 : Real) = (↑a⁻¹ : A) := by
.symm refine a.inv_eq_of_mul_eq_one_left ?_
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 (a.isStrictlyPositive_iff.mpr ha)

/--
lemma `rpow_neg_one_eq_cfc_inv` / 引理 `rpow_neg_one_eq_cfc_inv`

English:
lemma rpow_neg_one_eq_cfc_inv
  statement: {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
  proof: cfc_congr fun x _ => NNReal.rpow_neg_one x

中文:
引理 rpow_neg_one_eq_cfc_inv
  结论: {A : 类型} [偏序 A] [赋范环 A] [对合环 A]
  证明: cfc_congr fun x _ => NNReal.rpow_neg_one x

Depends on / 依赖: NNReal, NNReal.rpow_neg_one, cfc_congr, rpow_neg_one
-/
lemma rpow_neg_one_eq_cfc_inv {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
    [StarOrderedRing A] [NormedAlgebra Real A] [NonnegSpectrumClass Real A]
    [ContinuousFunctionalCalculus Real A IsSelfAdjoint] (a : A) :
    a ^ (-1 : Real) = cfc (·⁻¹ : Real>=0 -> Real>=0) a :=
  cfc_congr fun x _ => NNReal.rpow_neg_one x

/--
lemma `inverse_eq_rpow_neg_one` / 引理 `inverse_eq_rpow_neg_one`

English:
lemma inverse_eq_rpow_neg_one
  given: {a : A} (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by
  obtain ⟨ax, hax⟩ := ha.isUnit
  simp only [← hax, Ring.inverse_invertible, invOf_units, CFC.rpow_neg_one_eq_inv ax]

中文:
引理 inverse_eq_rpow_neg_one
  条件: {a : A} (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by
  obtain ⟨ax, hax⟩ := ha.isUnit
  simp only [← hax, Ring.inverse_invertible, invOf_units, CFC.rpow_neg_one_eq_inv ax]

Depends on / 依赖: CFC.rpow_neg_one_eq_inv, Ring.inverse, Ring.inverse_invertible, cfc_tac, ha.isUnit, invOf_units, inverse, inverse_invertible, isUnit, rpow_neg_one_eq_inv
-/
lemma inverse_eq_rpow_neg_one {a : A} (ha : IsStrictlyPositive a := by cfc_tac) :
    Ring.inverse a = a ^ (-1 : Real) := by
  obtain ⟨ax, hax⟩ := ha.isUnit
  simp only [← hax, Ring.inverse_invertible, invOf_units, CFC.rpow_neg_one_eq_inv ax]

/--
lemma `rpow_neg` / 引理 `rpow_neg`

English:
lemma rpow_neg
  statement: [IsSemitopologicalRing A] [T2Space A] (a : Aˣ) (x : Real)
  proof: by
  suffices h₁ : ContinuousOn (fun z => z ^ x) (Inv.inv '' (spectrum Real>=0 (a : A))) by
    rw [← cfc_inv_id (R := Real>=0) a]; rw [rpow_def]; rw [rpow_def]; rw [← cfc_comp' (fun z => z ^ x) (Inv.inv : Real>=0 -> Real>=0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, 

中文:
引理 rpow_neg
  结论: [是Semitopological环 A] [T2空间 A] (a : Aˣ) (x : 实数)
  证明: by
  suffices h₁ : ContinuousOn (fun z => z ^ x) (Inv.inv '' (spectrum Real>=0 (a : A))) by
    rw [← cfc_inv_id (R := Real>=0) a]; rw [rpow_def]; rw [rpow_def]; rw [← cfc_comp' (fun z => z ^ x) (Inv.inv : Real>=0 -> Real>=0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, 

Depends on / 依赖: ContinuousOn, Inv.inv, NNReal, NNReal.continuousOn_rpow_const, NNReal.inv_rpow, NNReal.rpow_neg, a.isUnit, cfc_comp, cfc_congr, cfc_inv_id, cfc_tac, continuousOn_rpow_const, inv_eq_zero, inv_eq_zero.mp, inv_rpow, isUnit, rpow_def, rpow_neg, spectrum, spectrum.zero_notMem
-/
lemma rpow_neg [IsSemitopologicalRing A] [T2Space A] (a : Aˣ) (x : Real)
    (ha' : (0 : A) <= a := by cfc_tac) : (a : A) ^ (-x) = (↑a⁻¹ : A) ^ x := by
  suffices h₁ : ContinuousOn (fun z => z ^ x) (Inv.inv '' (spectrum Real>=0 (a : A))) by
    rw [← cfc_inv_id (R := Real>=0) a]; rw [rpow_def]; rw [rpow_def]; rw [← cfc_comp' (fun z => z ^ x) (Inv.inv : Real>=0 -> Real>=0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, NNReal.inv_rpow]
  refine NNReal.continuousOn_rpow_const (.inl ?_)
  rintro ⟨z, hz, hz'⟩
exact spectrum.zero_notMem Real>=0 a.isUnit inv_eq_zero.mp hz' ▸ hz

/--
lemma `rpow_intCast` / 引理 `rpow_intCast`

English:
lemma rpow_intCast
  given: (a : Aˣ) (n : Int) (ha : (0 : A) <= a := by cfc_tac)
  proof: by
  rw [← cfc_zpow (R := Real>=0) a n]; rw [rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

中文:
引理 rpow_intCast
  条件: (a : Aˣ) (n : 整数) (ha : (0 : A) <= a := by cfc_tac)
  证明: by
  rw [← cfc_zpow (R := Real>=0) a n]; rw [rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

Depends on / 依赖: cfc_congr, cfc_tac, cfc_zpow, rpow_def
-/
lemma rpow_intCast (a : Aˣ) (n : Int) (ha : (0 : A) <= a := by cfc_tac) :
    (a : A) ^ (n : Real) = (↑(a ^ n) : A) := by
  rw [← cfc_zpow (R := Real>=0) a n]; rw [rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

/-- `a ^ x` bundled as an element of `Aˣ` for `a : Aˣ`. -/
@[simps]
/--
Definition of `_root_.Units.cfcRpow` / `_root_.Units.cfcRpow` 的定义

English:
definition _root_.Units.cfcRpow
  signature: (a : Aˣ) (x : Real) (ha : (0 : A) <= a := by cfc_tac)
  body: ⟨(a : A) ^ x, (a : A) ^ (-x), rpow_mul_rpow_neg x, rpow_neg_mul_rpow x⟩

@[aesop safe apply, grind ←]

中文:
定义 _root_.单位群.cfcRpow
  签名: (a : Aˣ) (x : 实数) (ha : (0 : A) <= a := by cfc_tac)
  定义体: ⟨(a : A) ^ x, (a : A) ^ (-x), rpow_mul_rpow_neg x, rpow_neg_mul_rpow x⟩

@[aesop safe apply, grind ←]

Depends on / 依赖: cfc_tac, rpow_mul_rpow_neg, rpow_neg_mul_rpow
-/
noncomputable def _root_.Units.cfcRpow (a : Aˣ) (x : Real) (ha : (0 : A) <= a := by cfc_tac) : Aˣ :=
  ⟨(a : A) ^ x, (a : A) ^ (-x), rpow_mul_rpow_neg x, rpow_neg_mul_rpow x⟩

@[aesop safe apply, grind ←]
/--
lemma `_root_.IsUnit.cfcRpow` / 引理 `_root_.IsUnit.cfcRpow`

English:
lemma _root_.IsUnit.cfcRpow
  given: {a : A} (ha : IsUnit a) (x : Real) (ha_nonneg : 0 <= a := by cfc_tac)
  proof: .isUnit ha.unit.cfcRpow x

中文:
引理 _root_.是单位.cfcRpow
  条件: {a : A} (ha : 是单位 a) (x : 实数) (ha_nonneg : 0 <= a := by cfc_tac)
  证明: .isUnit ha.unit.cfcRpow x

Depends on / 依赖: IsUnit, cfcRpow, cfc_tac, ha.unit.cfcRpow, isUnit
-/
lemma _root_.IsUnit.cfcRpow {a : A} (ha : IsUnit a) (x : Real) (ha_nonneg : 0 <= a := by cfc_tac) :
    IsUnit (a ^ x) :=
.isUnit ha.unit.cfcRpow x

/--
lemma `spectrum_rpow` / 引理 `spectrum_rpow`

English:
lemma spectrum_rpow
  statement: (a : A) (x : Real)
  proof: cfc_map_spectrum (· ^ x : Real>=0 -> Real>=0) a ha h

@[grind =]

中文:
引理 spectrum_rpow
  结论: (a : A) (x : 实数)
  证明: cfc_map_spectrum (· ^ x : Real>=0 -> Real>=0) a ha h

@[grind =]

Depends on / 依赖: cfc_cont_tac, cfc_map_spectrum, cfc_tac, spectrum
-/
lemma spectrum_rpow (a : A) (x : Real)
    (h : ContinuousOn (· ^ x) (spectrum Real>=0 a) := by cfc_cont_tac)
    (ha : 0 <= a := by cfc_tac) :
    spectrum Real>=0 (a ^ x) = (· ^ x) '' spectrum Real>=0 a :=
  cfc_map_spectrum (· ^ x : Real>=0 -> Real>=0) a ha h

@[grind =]
/--
lemma `isUnit_rpow_iff` / 引理 `isUnit_rpow_iff`

English:
lemma isUnit_rpow_iff
  given: (a : A) (y : Real) (hy : y != 0) (ha : 0 <= a := by cfc_tac)
  proof: by
  nontriviality A
  refine ⟨fun h => ?_, fun h => h.cfcRpow y ha⟩
  rw [rpow_def] at h
  by_cases hf : ContinuousOn (fun x : Real>=0 => x ^ y) (spectrum Real>=0 a)
  · rw [isUnit_cfc_iff _ a hf] at h
    refine spectrum.isUnit_of_zero_notMem Real>=0 ?_
    intro h0
    specialize h 0 h0
    simp 

中文:
引理 isUnit_rpow_iff
  条件: (a : A) (y : 实数) (hy : y != 0) (ha : 0 <= a := by cfc_tac)
  证明: by
  nontriviality A
  refine ⟨fun h => ?_, fun h => h.cfcRpow y ha⟩
  rw [rpow_def] at h
  by_cases hf : ContinuousOn (fun x : Real>=0 => x ^ y) (spectrum Real>=0 a)
  · rw [isUnit_cfc_iff _ a hf] at h
    refine spectrum.isUnit_of_zero_notMem Real>=0 ?_
    intro h0
    specialize h 0 h0
    simp 

Depends on / 依赖: ContinuousOn, Decidable, Decidable.not_not, False.elim, IsUnit, NNReal, NNReal.rpow_eq_zero_iff, cfcRpow, cfc_apply_of_not_continuousOn, cfc_tac, h.cfcRpow, isUnit_cfc_iff, isUnit_of_zero_notMem, ne_eq, nontriviality, not_isUnit_zero, not_not, rpow_def, rpow_eq_zero_iff, specialize
-/
lemma isUnit_rpow_iff (a : A) (y : Real) (hy : y != 0) (ha : 0 <= a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  nontriviality A
  refine ⟨fun h => ?_, fun h => h.cfcRpow y ha⟩
  rw [rpow_def] at h
  by_cases hf : ContinuousOn (fun x : Real>=0 => x ^ y) (spectrum Real>=0 a)
  · rw [isUnit_cfc_iff _ a hf] at h
    refine spectrum.isUnit_of_zero_notMem Real>=0 ?_
    intro h0
    specialize h 0 h0
    simp only [ne_eq, NNReal.rpow_eq_zero_iff, true_and, Decidable.not_not] at h
    exact hy h
  · rw [cfc_apply_of_not_continuousOn a hf] at h
exact False.elim not_isUnit_zero h

section prod

variable [IsSemitopologicalRing A] [T2Space A]
variable {B : Type*} [PartialOrder B] [Ring B] [StarRing B] [TopologicalSpace B]
  [StarOrderedRing B]
  [Algebra Real B] [ContinuousFunctionalCalculus Real B IsSelfAdjoint]
  [ContinuousFunctionalCalculus Real (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B] [StarOrderedRing (A × B)]
  [NonnegSpectrumClass Real B] [NonnegSpectrumClass Real (A × B)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `rpow_map_prod` / 引理 `rpow_map_prod`

English:
lemma rpow_map_prod
  statement: {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit b)
  proof: by
  have ha'' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  have hb'' : 0 ∉ spectrum Real>=0 b := spectrum.zero_notMem _ hb
  simp only [rpow_def]
  unfold rpow
  refine cfc_map_prod (R := Real>=0) (S := Real) _ a b (by cfc_cont_tac) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha', hb']

中文:
引理 rpow_map_prod
  结论: {a : A} {b : B} {x : 实数} (ha : 是单位 a) (hb : 是单位 b)
  证明: by
  have ha'' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  have hb'' : 0 ∉ spectrum Real>=0 b := spectrum.zero_notMem _ hb
  simp only [rpow_def]
  unfold rpow
  refine cfc_map_prod (R := Real>=0) (S := Real) _ a b (by cfc_cont_tac) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha', hb']

Depends on / 依赖: Prod.le_def, cfc_cont_tac, cfc_map_prod, cfc_tac, le_def, rpow_def, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma rpow_map_prod {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 <= a := by cfc_tac) (hb' : 0 <= b := by cfc_tac) :
    rpow (a, b) x = (a ^ x, b ^ x) := by
  have ha'' : 0 ∉ spectrum Real>=0 a := spectrum.zero_notMem _ ha
  have hb'' : 0 ∉ spectrum Real>=0 b := spectrum.zero_notMem _ hb
  simp only [rpow_def]
  unfold rpow
  refine cfc_map_prod (R := Real>=0) (S := Real) _ a b (by cfc_cont_tac) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha', hb']

/--
lemma `rpow_eq_rpow_prod` / 引理 `rpow_eq_rpow_prod`

English:
lemma rpow_eq_rpow_prod
  statement: {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit b)
  proof: rpow_map_prod ha hb

中文:
引理 rpow_eq_rpow_prod
  结论: {a : A} {b : B} {x : 实数} (ha : 是单位 a) (hb : 是单位 b)
  证明: rpow_map_prod ha hb

Depends on / 依赖: cfc_tac, rpow_map_prod
-/
lemma rpow_eq_rpow_prod {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 <= a := by cfc_tac) (hb' : 0 <= b := by cfc_tac) :
    rpow (a, b) x = (a, b) ^ x := rpow_map_prod ha hb

end prod

section pi

variable [IsSemitopologicalRing A] [T2Space A]
variable {ι : Type*} {C : ι -> Type*} [forall i, PartialOrder (C i)] [forall i, Ring (C i)]
  [forall i, StarRing (C i)] [forall i, TopologicalSpace (C i)] [forall i, StarOrderedRing (C i)]
  [StarOrderedRing (forall i, C i)]
  [forall i, Algebra Real (C i)] [forall i, ContinuousFunctionalCalculus Real (C i) IsSelfAdjoint]
  [ContinuousFunctionalCalculus Real (forall i, C i) IsSelfAdjoint]
  [forall i, IsSemitopologicalRing (C i)] [forall i, T2Space (C i)]
  [NonnegSpectrumClass Real (forall i, C i)] [forall i, NonnegSpectrumClass Real (C i)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `rpow_map_pi` / 引理 `rpow_map_pi`

English:
lemma rpow_map_pi
  statement: {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i))
  proof: by
  have hc'' : forall i, 0 ∉ spectrum Real>=0 (c i) := fun i => spectrum.zero_notMem _ (hc i)
  simp only [rpow_def]
  unfold rpow
  exact cfc_map_pi (S := Real) _ c

中文:
引理 rpow_map_pi
  结论: {c : 对任意 i, C i} {x : 实数} (hc : 对任意 i, 是单位 (c i))
  证明: by
  have hc'' : forall i, 0 ∉ spectrum Real>=0 (c i) := fun i => spectrum.zero_notMem _ (hc i)
  simp only [rpow_def]
  unfold rpow
  exact cfc_map_pi (S := Real) _ c

Depends on / 依赖: cfc_map_pi, cfc_tac, rpow_def, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma rpow_map_pi {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i))
    (hc' : forall i, 0 <= c i := by cfc_tac) :
    rpow c x = fun i => (c i) ^ x := by
  have hc'' : forall i, 0 ∉ spectrum Real>=0 (c i) := fun i => spectrum.zero_notMem _ (hc i)
  simp only [rpow_def]
  unfold rpow
  exact cfc_map_pi (S := Real) _ c

/--
lemma `rpow_eq_rpow_pi` / 引理 `rpow_eq_rpow_pi`

English:
lemma rpow_eq_rpow_pi
  statement: {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i))
  proof: rpow_map_pi hc

中文:
引理 rpow_eq_rpow_pi
  结论: {c : 对任意 i, C i} {x : 实数} (hc : 对任意 i, 是单位 (c i))
  证明: rpow_map_pi hc

Depends on / 依赖: cfc_tac, infer_instance, rpow_map_pi
-/
lemma rpow_eq_rpow_pi {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i))
    (hc' : forall i, 0 <= c i := by cfc_tac) :
    rpow c x = c ^ x := rpow_map_pi hc

end pi

section unital_vs_nonunital

open Ring
variable [IsSemitopologicalRing A] [T2Space A]

-- provides instance `ContinuousFunctionalCalculus.compactSpace_spectrum`
open scoped ContinuousFunctionalCalculus

/--
lemma `nnrpow_eq_rpow` / 引理 `nnrpow_eq_rpow`

English:
lemma nnrpow_eq_rpow
  given: {a : A} {x : Real>=0} (hx : 0 < x)
  statement: a ^ x = a ^ (x : Real)
  proof: by
  rw [nnrpow_def (A := A)]; rw [rpow_def]; rw [cfcₙ_eq_cfc]

中文:
引理 nnrpow_eq_rpow
  条件: {a : A} {x : 实数>=0} (hx : 0 < x)
  结论: a ^ x = a ^ (x : 实数)
  证明: by
  rw [nnrpow_def (A := A)]; rw [rpow_def]; rw [cfcₙ_eq_cfc]

Depends on / 依赖: infer_instance, nnrpow_def, rpow_def
-/
lemma nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : a ^ x = a ^ (x : Real) := by
  rw [nnrpow_def (A := A)]; rw [rpow_def]; rw [cfcₙ_eq_cfc]

/--
lemma `sqrt_eq_rpow` / 引理 `sqrt_eq_rpow`

English:
lemma sqrt_eq_rpow
  given: {a : A}
  statement: sqrt a = a ^ (1 / 2 : Real)
  proof: by
  have : a ^ (1 / 2 : Real) = a ^ ((1 / 2 : Real>=0) : Real) := rfl
  rw [this]; rw [← nnrpow_eq_rpow (by simp)]; rw [sqrt_eq_nnrpow a]

中文:
引理 sqrt_eq_rpow
  条件: {a : A}
  结论: sqrt a = a ^ (1 / 2 : 实数)
  证明: by
  have : a ^ (1 / 2 : Real) = a ^ ((1 / 2 : Real>=0) : Real) := rfl
  rw [this]; rw [← nnrpow_eq_rpow (by simp)]; rw [sqrt_eq_nnrpow a]

Depends on / 依赖: nnrpow_eq_rpow, sqrt_eq_nnrpow
-/
lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real) := by
  have : a ^ (1 / 2 : Real) = a ^ ((1 / 2 : Real>=0) : Real) := rfl
  rw [this]; rw [← nnrpow_eq_rpow (by simp)]; rw [sqrt_eq_nnrpow a]

/--
lemma `sqrt_eq_cfc` / 引理 `sqrt_eq_cfc`

English:
lemma sqrt_eq_cfc
  given: {a : A}
  statement: sqrt a = cfc NNReal.sqrt a
  proof: by
  unfold sqrt
  rw [cfcₙ_eq_cfc]

中文:
引理 sqrt_eq_cfc
  条件: {a : A}
  结论: sqrt a = cfc 非负实数.sqrt a
  证明: by
  unfold sqrt
  rw [cfcₙ_eq_cfc]
-/
lemma sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a := by
  unfold sqrt
  rw [cfcₙ_eq_cfc]

/--
lemma `sqrt_sq` / 引理 `sqrt_sq`

English:
lemma sqrt_sq
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: sqrt (a ^ 2) = a
  proof: by
  rw [pow_two]; rw [sqrt_mul_self (A := A) a]

中文:
引理 sqrt_sq
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: sqrt (a ^ 2) = a
  证明: by
  rw [pow_two]; rw [sqrt_mul_self (A := A) a]

Depends on / 依赖: cfc_tac, pow_two, sqrt_mul_self
-/
lemma sqrt_sq (a : A) (ha : 0 <= a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [pow_two]; rw [sqrt_mul_self (A := A) a]

/--
lemma `sq_sqrt` / 引理 `sq_sqrt`

English:
lemma sq_sqrt
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: (sqrt a) ^ 2 = a
  proof: by
  rw [pow_two]; rw [sqrt_mul_sqrt_self (A := A) a]

中文:
引理 sq_sqrt
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: (sqrt a) ^ 2 = a
  证明: by
  rw [pow_two]; rw [sqrt_mul_sqrt_self (A := A) a]

Depends on / 依赖: cfc_tac, pow_two, sqrt_mul_sqrt_self
-/
lemma sq_sqrt (a : A) (ha : 0 <= a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  rw [pow_two]; rw [sqrt_mul_sqrt_self (A := A) a]

/--
lemma `sq_eq_sq_iff` / 引理 `sq_eq_sq_iff`

English:
lemma sq_eq_sq_iff
  given: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  proof: by
  simp_rw [sq, mul_self_eq_mul_self_iff a b]

@[simp]

中文:
引理 sq_eq_sq_iff
  条件: (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac)
  证明: by
  simp_rw [sq, mul_self_eq_mul_self_iff a b]

@[simp]

Depends on / 依赖: cfc_tac, mul_self_eq_mul_self_iff, simp_rw
-/
lemma sq_eq_sq_iff (a b : A) (ha : 0 <= a := by cfc_tac) (hb : 0 <= b := by cfc_tac) :
    a ^ 2 = b ^ 2 ↔ a = b := by
  simp_rw [sq, mul_self_eq_mul_self_iff a b]

@[simp]
/--
lemma `sqrt_algebraMap` / 引理 `sqrt_algebraMap`

English:
lemma sqrt_algebraMap
  given: {r : Real>=0}
  statement: sqrt (algebraMap Real>=0 A r) = algebraMap Real>=0 A (NNReal.sqrt r)
  proof: by
  rw [sqrt_eq_cfc]; rw [cfc_algebraMap]

@[simp]

中文:
引理 sqrt_algebraMap
  条件: {r : 实数>=0}
  结论: sqrt (algebraMap 实数>=0 A r) = algebraMap 实数>=0 A (非负实数.sqrt r)
  证明: by
  rw [sqrt_eq_cfc]; rw [cfc_algebraMap]

@[simp]

Depends on / 依赖: cfc_algebraMap, sqrt_eq_cfc
-/
lemma sqrt_algebraMap {r : Real>=0} : sqrt (algebraMap Real>=0 A r) = algebraMap Real>=0 A (NNReal.sqrt r) := by
  rw [sqrt_eq_cfc]; rw [cfc_algebraMap]

@[simp]
/--
lemma `sqrt_one` / 引理 `sqrt_one`

English:
lemma sqrt_one
  statement: sqrt (1 : A) = 1
  proof: by simp [sqrt_eq_cfc]

中文:
引理 sqrt_one
  结论: sqrt (1 : A) = 1
  证明: by simp [sqrt_eq_cfc]

Depends on / 依赖: instEpiAppOfFunctor, sqrt_eq_cfc
-/
lemma sqrt_one : sqrt (1 : A) = 1 := by simp [sqrt_eq_cfc]

/--
lemma `sqrt_eq_one_iff` / 引理 `sqrt_eq_one_iff`

English:
lemma sqrt_eq_one_iff
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [sqrt_eq_iff a _]; rw [mul_one]; rw [eq_comm]

中文:
引理 sqrt_eq_one_iff
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [sqrt_eq_iff a _]; rw [mul_one]; rw [eq_comm]

Depends on / 依赖: cfc_tac, eq_comm, mul_one, sqrt_eq_iff
-/
lemma sqrt_eq_one_iff (a : A) (ha : 0 <= a := by cfc_tac) :
    sqrt a = 1 ↔ a = 1 := by
  rw [sqrt_eq_iff a _]; rw [mul_one]; rw [eq_comm]

/--
lemma `sqrt_eq_one_iff'` / 引理 `sqrt_eq_one_iff'`

English:
lemma sqrt_eq_one_iff'
  given: [Nontrivial A] (a : A)
  proof: by
.mp h, fun h => by subst h; exact sqrt_one⟩ refine ⟨fun h => sqrt_eq_one_iff a ?_
  rw [sqrt]; rw [cfcₙ] at h
  cfc_tac

中文:
引理 sqrt_eq_one_iff'
  条件: [非平凡 A] (a : A)
  证明: by
.mp h, fun h => by subst h; exact sqrt_one⟩ refine ⟨fun h => sqrt_eq_one_iff a ?_
  rw [sqrt]; rw [cfcₙ] at h
  cfc_tac

Depends on / 依赖: cfc_tac, sqrt_eq_one_iff, sqrt_one
-/
lemma sqrt_eq_one_iff' [Nontrivial A] (a : A) :
    sqrt a = 1 ↔ a = 1 := by
.mp h, fun h => by subst h; exact sqrt_one⟩ refine ⟨fun h => sqrt_eq_one_iff a ?_
  rw [sqrt]; rw [cfcₙ] at h
  cfc_tac

-- TODO: relate to a strict positivity condition
/--
lemma `sqrt_rpow` / 引理 `sqrt_rpow`

English:
lemma sqrt_rpow
  statement: {a : A} {x : Real} (h : IsUnit a)
  proof: by
  by_cases hnonneg : 0 <= a
  case pos =>
    have : IsStrictlyPositive a := by grind
    simp [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

中文:
引理 sqrt_rpow
  结论: {a : A} {x : 实数} (h : 是单位 a)
  证明: by
  by_cases hnonneg : 0 <= a
  case pos =>
    have : IsStrictlyPositive a := by grind
    simp [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

Depends on / 依赖: IsStrictlyPositive, cfc_apply_of_not_predicate, div_eq_mul_inv, hnonneg, one_mul, rpow_def, rpow_rpow, sqrt_eq_cfc, sqrt_eq_rpow
-/
lemma sqrt_rpow {a : A} {x : Real} (h : IsUnit a)
    (hx : x != 0) : sqrt (a ^ x) = a ^ (x / 2) := by
  by_cases hnonneg : 0 <= a
  case pos =>
    have : IsStrictlyPositive a := by grind
    simp [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

-- TODO: relate to a strict positivity condition
/--
lemma `rpow_sqrt` / 引理 `rpow_sqrt`

English:
lemma rpow_sqrt
  statement: (a : A) (x : Real) (h : IsUnit a)
  proof: by
  have : IsStrictlyPositive a := by grind
  rw [sqrt_eq_rpow]; rw [div_eq_mul_inv]; rw [one_mul]; rw [rpow_rpow _ _ _ (by simp)]; rw [inv_mul_eq_div]

中文:
引理 rpow_sqrt
  结论: (a : A) (x : 实数) (h : 是单位 a)
  证明: by
  have : IsStrictlyPositive a := by grind
  rw [sqrt_eq_rpow]; rw [div_eq_mul_inv]; rw [one_mul]; rw [rpow_rpow _ _ _ (by simp)]; rw [inv_mul_eq_div]

Depends on / 依赖: IsStrictlyPositive, cfc_tac, div_eq_mul_inv, inv_mul_eq_div, one_mul, rpow_rpow, sqrt_eq_rpow
-/
lemma rpow_sqrt (a : A) (x : Real) (h : IsUnit a)
    (ha : 0 <= a := by cfc_tac) : (sqrt a) ^ x = a ^ (x / 2) := by
  have : IsStrictlyPositive a := by grind
  rw [sqrt_eq_rpow]; rw [div_eq_mul_inv]; rw [one_mul]; rw [rpow_rpow _ _ _ (by simp)]; rw [inv_mul_eq_div]

/--
lemma `sqrt_rpow_nnreal` / 引理 `sqrt_rpow_nnreal`

English:
lemma sqrt_rpow_nnreal
  given: {a : A} {x : Real>=0}
  statement: sqrt (a ^ (x : Real)) = a ^ (x / 2 : Real)
  proof: by
  by_cases htriv : 0 <= a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    cases eq_zero_or_pos x with
    | inl hx => simp [hx, rpow_zero _ htriv]
    | inr h₁ =>
      have h₂ : (x : Real) / 2 = NNReal.toReal (x / 2) := by simp
      have h₃ : 0 <

中文:
引理 sqrt_rpow_nnreal
  条件: {a : A} {x : 实数>=0}
  结论: sqrt (a ^ (x : 实数)) = a ^ (x / 2 : 实数)
  证明: by
  by_cases htriv : 0 <= a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    cases eq_zero_or_pos x with
    | inl hx => simp [hx, rpow_zero _ htriv]
    | inr h₁ =>
      have h₂ : (x : Real) / 2 = NNReal.toReal (x / 2) := by simp
      have h₃ : 0 <

Depends on / 依赖: NNReal, NNReal.toReal, cfc_apply_of_not_predicate, eq_zero_or_pos, nnrpow_eq_rpow, rpow_def, rpow_zero, sqrt_eq_cfc, sqrt_nnrpow, toReal
-/
lemma sqrt_rpow_nnreal {a : A} {x : Real>=0} : sqrt (a ^ (x : Real)) = a ^ (x / 2 : Real) := by
  by_cases htriv : 0 <= a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    cases eq_zero_or_pos x with
    | inl hx => simp [hx, rpow_zero _ htriv]
    | inr h₁ =>
      have h₂ : (x : Real) / 2 = NNReal.toReal (x / 2) := by simp
      have h₃ : 0 < x / 2 := by positivity
      rw [← nnrpow_eq_rpow h₁]; rw [h₂]; rw [← nnrpow_eq_rpow h₃]; rw [sqrt_nnrpow (A := A)]

/--
lemma `rpow_sqrt_nnreal` / 引理 `rpow_sqrt_nnreal`

English:
lemma rpow_sqrt_nnreal
  statement: {a : A} {x : Real>=0}
  proof: by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 <= sqrt a := sqrt_nonneg _
    simp [hx, rpow_zero _ ha', rpow_zero _ ha]
  case neg =>
    have h₁ : 0 <= (x : Real) := NNReal.zero_le_coe
    rw [sqrt_eq_rpow]; rw [rpow_rpow_of_exponent_nonneg _ _ _ (by simp) h₁]; rw [one_div_mul_eq_div]

@[

中文:
引理 rpow_sqrt_nnreal
  结论: {a : A} {x : 实数>=0}
  证明: by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 <= sqrt a := sqrt_nonneg _
    simp [hx, rpow_zero _ ha', rpow_zero _ ha]
  case neg =>
    have h₁ : 0 <= (x : Real) := NNReal.zero_le_coe
    rw [sqrt_eq_rpow]; rw [rpow_rpow_of_exponent_nonneg _ _ _ (by simp) h₁]; rw [one_div_mul_eq_div]

@[

Depends on / 依赖: NNReal, NNReal.zero_le_coe, cfc_tac, one_div_mul_eq_div, rpow_rpow_of_exponent_nonneg, rpow_zero, sqrt_eq_rpow, sqrt_nonneg, zero_le_coe
-/
lemma rpow_sqrt_nnreal {a : A} {x : Real>=0}
    (ha : 0 <= a := by cfc_tac) : (sqrt a) ^ (x : Real) = a ^ (x / 2 : Real) := by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 <= sqrt a := sqrt_nonneg _
    simp [hx, rpow_zero _ ha', rpow_zero _ ha]
  case neg =>
    have h₁ : 0 <= (x : Real) := NNReal.zero_le_coe
    rw [sqrt_eq_rpow]; rw [rpow_rpow_of_exponent_nonneg _ _ _ (by simp) h₁]; rw [one_div_mul_eq_div]

@[grind =]
/--
lemma `isUnit_nnrpow_iff` / 引理 `isUnit_nnrpow_iff`

English:
lemma isUnit_nnrpow_iff
  given: (a : A) (y : Real>=0) (hy : y != 0) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [nnrpow_eq_rpow (pos_of_ne_zero hy)]
  refine isUnit_rpow_iff a y ?_ ha
  exact_mod_cast hy

@[aesop safe apply]

中文:
引理 isUnit_nnrpow_iff
  条件: (a : A) (y : 实数>=0) (hy : y != 0) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [nnrpow_eq_rpow (pos_of_ne_zero hy)]
  refine isUnit_rpow_iff a y ?_ ha
  exact_mod_cast hy

@[aesop safe apply]

Depends on / 依赖: IsUnit, cfc_tac, isUnit_rpow_iff, nnrpow_eq_rpow, pos_of_ne_zero
-/
lemma isUnit_nnrpow_iff (a : A) (y : Real>=0) (hy : y != 0) (ha : 0 <= a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  rw [nnrpow_eq_rpow (pos_of_ne_zero hy)]
  refine isUnit_rpow_iff a y ?_ ha
  exact_mod_cast hy

@[aesop safe apply]
/--
lemma `_root_.IsUnit.cfcNNRpow` / 引理 `_root_.IsUnit.cfcNNRpow`

English:
lemma _root_.IsUnit.cfcNNRpow
  statement: (a : A) (y : Real>=0) (ha_unit : IsUnit a) (hy : y != 0)
  proof: (isUnit_nnrpow_iff a y hy ha).mpr ha_unit

中文:
引理 _root_.是单位.cfcNNRpow
  结论: (a : A) (y : 实数>=0) (ha_unit : 是单位 a) (hy : y != 0)
  证明: (isUnit_nnrpow_iff a y hy ha).mpr ha_unit

Depends on / 依赖: IsUnit, cfc_tac, ha_unit, isUnit_nnrpow_iff
-/
lemma _root_.IsUnit.cfcNNRpow (a : A) (y : Real>=0) (ha_unit : IsUnit a) (hy : y != 0)
    (ha : 0 <= a := by cfc_tac) : IsUnit (a ^ y) :=
  (isUnit_nnrpow_iff a y hy ha).mpr ha_unit

/--
lemma `isUnit_sqrt_iff` / 引理 `isUnit_sqrt_iff`

English:
lemma isUnit_sqrt_iff
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: IsUnit (sqrt a) ↔ IsUnit a
  proof: by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

@[grind =]

中文:
引理 isUnit_sqrt_iff
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: 是单位 (sqrt a) ↔ 是单位 a
  证明: by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

@[grind =]

Depends on / 依赖: IsUnit, cfc_tac, isUnit_rpow_iff, sqrt_eq_rpow
-/
lemma isUnit_sqrt_iff (a : A) (ha : 0 <= a := by cfc_tac) : IsUnit (sqrt a) ↔ IsUnit a := by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

@[grind =]
/--
lemma `isUnit_sqrt_iff_isStrictlyPositive` / 引理 `isUnit_sqrt_iff_isStrictlyPositive`

English:
lemma isUnit_sqrt_iff_isStrictlyPositive
  given: {a : A}
  statement: IsUnit (sqrt a) ↔ IsStrictlyPositive a
  proof: by
  refine ⟨fun h => ?_, by grind [isUnit_sqrt_iff]⟩
  rw [IsStrictlyPositive.iff_of_unital]
  have ha : 0 <= a := by
    nontriviality
    by_contra H
    rw [CFC.sqrt_of_not_nonneg H] at h
    exact not_isUnit_zero h
  refine ⟨ha, ?_⟩
  rwa [isUnit_sqrt_iff _ ha] at h

@[aesop safe apply]

中文:
引理 isUnit_sqrt_iff_isStrictlyPositive
  条件: {a : A}
  结论: 是单位 (sqrt a) ↔ IsStrictlyPositive a
  证明: by
  refine ⟨fun h => ?_, by grind [isUnit_sqrt_iff]⟩
  rw [IsStrictlyPositive.iff_of_unital]
  have ha : 0 <= a := by
    nontriviality
    by_contra H
    rw [CFC.sqrt_of_not_nonneg H] at h
    exact not_isUnit_zero h
  refine ⟨ha, ?_⟩
  rwa [isUnit_sqrt_iff _ ha] at h

@[aesop safe apply]

Depends on / 依赖: CFC.sqrt_of_not_nonneg, IsStrictlyPositive, IsStrictlyPositive.iff_of_unital, iff_of_unital, isUnit_sqrt_iff, nontriviality, not_isUnit_zero, sqrt_of_not_nonneg
-/
lemma isUnit_sqrt_iff_isStrictlyPositive {a : A} : IsUnit (sqrt a) ↔ IsStrictlyPositive a := by
  refine ⟨fun h => ?_, by grind [isUnit_sqrt_iff]⟩
  rw [IsStrictlyPositive.iff_of_unital]
  have ha : 0 <= a := by
    nontriviality
    by_contra H
    rw [CFC.sqrt_of_not_nonneg H] at h
    exact not_isUnit_zero h
  refine ⟨ha, ?_⟩
  rwa [isUnit_sqrt_iff _ ha] at h

@[aesop safe apply]
/--
lemma `_root_.IsStrictlyPositive.isUnit_cfcSqrt` / 引理 `_root_.IsStrictlyPositive.isUnit_cfcSqrt`

English:
lemma _root_.IsStrictlyPositive.isUnit_cfcSqrt
  given: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by grind

@[aesop safe apply]

中文:
引理 _root_.IsStrictlyPositive.isUnit_cfcSqrt
  条件: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by grind

@[aesop safe apply]

Depends on / 依赖: IsUnit, cfc_tac
-/
lemma _root_.IsStrictlyPositive.isUnit_cfcSqrt (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsUnit (sqrt a) := by grind

@[aesop safe apply]
/--
lemma `_root_.IsStrictlyPositive.nnrpow` / 引理 `_root_.IsStrictlyPositive.nnrpow`

English:
lemma _root_.IsStrictlyPositive.nnrpow
  statement: (a : A) (y : Real>=0) (hy : y != 0)
  proof: by grind

@[aesop safe apply]

中文:
引理 _root_.IsStrictlyPositive.nnrpow
  结论: (a : A) (y : 实数>=0) (hy : y != 0)
  证明: by grind

@[aesop safe apply]

Depends on / 依赖: IsStrictlyPositive, cfc_tac
-/
lemma _root_.IsStrictlyPositive.nnrpow (a : A) (y : Real>=0) (hy : y != 0)
    (ha : IsStrictlyPositive a := by cfc_tac) : IsStrictlyPositive (a ^ y) := by grind

@[aesop safe apply]
/--
lemma `_root_.IsStrictlyPositive.sqrt` / 引理 `_root_.IsStrictlyPositive.sqrt`

English:
lemma _root_.IsStrictlyPositive.sqrt
  given: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by grind

omit [T2Space A] [IsSemitopologicalRing A] in
@[aesop safe apply]

中文:
引理 _root_.IsStrictlyPositive.sqrt
  条件: (a : A) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by grind

omit [T2Space A] [IsSemitopologicalRing A] in
@[aesop safe apply]

Depends on / 依赖: IsStrictlyPositive, cfc_tac
-/
lemma _root_.IsStrictlyPositive.sqrt (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsStrictlyPositive (sqrt a) := by grind

omit [T2Space A] [IsSemitopologicalRing A] in
@[aesop safe apply]
/--
lemma `_root_.IsStrictlyPositive.rpow` / 引理 `_root_.IsStrictlyPositive.rpow`

English:
lemma _root_.IsStrictlyPositive.rpow
  given: (a : A) (y : Real) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by grind

中文:
引理 _root_.IsStrictlyPositive.rpow
  条件: (a : A) (y : 实数) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by grind

Depends on / 依赖: IsStrictlyPositive, cfc_tac, property
-/
lemma _root_.IsStrictlyPositive.rpow (a : A) (y : Real) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsStrictlyPositive (a ^ y) := by grind

/--
lemma `inverse_rpow` / 引理 `inverse_rpow`

English:
lemma inverse_rpow
  given: (a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac)
  proof: by
  have : a ^ (-x) = (a ^ x) ^ (-1 : Real) := by
    rw [rpow_rpow (hx := hx) (ha := by grind)]
    simp
  rw [← inverse_eq_rpow_neg_one (by grind)] at this
  rw [this]

omit [IsSemitopologicalRing A] [T2Space A] in
@[aesop safe apply]

中文:
引理 inverse_rpow
  条件: (a : A) (x : 实数) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac)
  证明: by
  have : a ^ (-x) = (a ^ x) ^ (-1 : Real) := by
    rw [rpow_rpow (hx := hx) (ha := by grind)]
    simp
  rw [← inverse_eq_rpow_neg_one (by grind)] at this
  rw [this]

omit [IsSemitopologicalRing A] [T2Space A] in
@[aesop safe apply]

Depends on / 依赖: Ring.inverse, cfc_tac, inverse, inverse_eq_rpow_neg_one, rpow_rpow
-/
lemma inverse_rpow (a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    Ring.inverse (a ^ x) = a ^ (-x) := by
  have : a ^ (-x) = (a ^ x) ^ (-1 : Real) := by
    rw [rpow_rpow (hx := hx) (ha := by grind)]
    simp
  rw [← inverse_eq_rpow_neg_one (by grind)] at this
  rw [this]

omit [IsSemitopologicalRing A] [T2Space A] in
@[aesop safe apply]
/--
lemma `_root_.IsStrictlyPositive.ringInverse` / 引理 `_root_.IsStrictlyPositive.ringInverse`

English:
lemma _root_.IsStrictlyPositive.ringInverse
  given: {a : A} (ha : IsStrictlyPositive a)
  proof: by
  rw [CFC.inverse_eq_rpow_neg_one]
  cfc_tac

omit [IsSemitopologicalRing A] [T2Space A] in
@[grind =]

中文:
引理 _root_.IsStrictlyPositive.ringInverse
  条件: {a : A} (ha : IsStrictlyPositive a)
  证明: by
  rw [CFC.inverse_eq_rpow_neg_one]
  cfc_tac

omit [IsSemitopologicalRing A] [T2Space A] in
@[grind =]

Depends on / 依赖: CFC.inverse_eq_rpow_neg_one, cfc_tac, inverse_eq_rpow_neg_one
-/
lemma _root_.IsStrictlyPositive.ringInverse {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive a⁻¹ʳ := by
  rw [CFC.inverse_eq_rpow_neg_one]
  cfc_tac

omit [IsSemitopologicalRing A] [T2Space A] in
@[grind =]
/--
lemma `_root_.isStrictlyPositive_ringInverse_iff` / 引理 `_root_.isStrictlyPositive_ringInverse_iff`

English:
lemma _root_.isStrictlyPositive_ringInverse_iff
  given: {a : A}
  proof: by
  nontriviality A
  refine ⟨fun h => ?_, IsStrictlyPositive.ringInverse⟩
  have ha : IsUnit a := by
    by_contra H
    rw [Ring.inverse_non_unit _ H]; rw [IsStrictlyPositive.iff_of_unital] at h
    exact not_isUnit_zero h.2
  rw [← Ring.inverse_inverse ha]
  exact h.ringInverse

omit [IsSemitopo

中文:
引理 _root_.isStrictlyPositive_ringInverse_iff
  条件: {a : A}
  证明: by
  nontriviality A
  refine ⟨fun h => ?_, IsStrictlyPositive.ringInverse⟩
  have ha : IsUnit a := by
    by_contra H
    rw [Ring.inverse_non_unit _ H]; rw [IsStrictlyPositive.iff_of_unital] at h
    exact not_isUnit_zero h.2
  rw [← Ring.inverse_inverse ha]
  exact h.ringInverse

omit [IsSemitopo

Depends on / 依赖: IsStrictlyPositive, IsStrictlyPositive.iff_of_unital, IsStrictlyPositive.ringInverse, IsUnit, Ring.inverse_inverse, Ring.inverse_non_unit, h.ringInverse, iff_of_unital, inverse_inverse, inverse_non_unit, nontriviality, not_isUnit_zero, ringInverse
-/
lemma _root_.isStrictlyPositive_ringInverse_iff {a : A} :
    IsStrictlyPositive a⁻¹ʳ ↔ IsStrictlyPositive a := by
  nontriviality A
  refine ⟨fun h => ?_, IsStrictlyPositive.ringInverse⟩
  have ha : IsUnit a := by
    by_contra H
    rw [Ring.inverse_non_unit _ H]; rw [IsStrictlyPositive.iff_of_unital] at h
    exact not_isUnit_zero h.2
  rw [← Ring.inverse_inverse ha]
  exact h.ringInverse

omit [IsSemitopologicalRing A] [T2Space A] in
open Ring in
@[grind =]
/--
lemma `ringInverse_nonneg_iff_nonneg_of_isUnit` / 引理 `ringInverse_nonneg_iff_nonneg_of_isUnit`

English:
lemma ringInverse_nonneg_iff_nonneg_of_isUnit
  given: {a : A} (ha : IsUnit a)
  proof: by
  grind [isStrictlyPositive_ringInverse_iff]

中文:
引理 ringInverse_nonneg_iff_nonneg_of_isUnit
  条件: {a : A} (ha : 是单位 a)
  证明: by
  grind [isStrictlyPositive_ringInverse_iff]

Depends on / 依赖: isStrictlyPositive_ringInverse_iff
-/
lemma ringInverse_nonneg_iff_nonneg_of_isUnit {a : A} (ha : IsUnit a) :
    0 <= a⁻¹ʳ ↔ 0 <= a := by
  grind [isStrictlyPositive_ringInverse_iff]

open Ring in
@[grind _=_]
/--
lemma `sqrt_ringInverse` / 引理 `sqrt_ringInverse`

English:
lemma sqrt_ringInverse
  given: {a : A}
  statement: sqrt a⁻¹ʳ = (sqrt a)⁻¹ʳ
  proof: by
  by_cases ha : IsStrictlyPositive a
  · rw [sqrt_eq_rpow, sqrt_eq_rpow, inverse_rpow _ _ (by grind),
        inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind)]
    grind only
  · have ha' : ¬IsUnit (sqrt a) := by rwa [CFC.isUnit_sqrt_iff_isStrictlyPositive]
    obtain (H | H) : ¬0 <= a ∨ ¬IsUn

中文:
引理 sqrt_ringInverse
  条件: {a : A}
  结论: sqrt a⁻¹ʳ = (sqrt a)⁻¹ʳ
  证明: by
  by_cases ha : IsStrictlyPositive a
  · rw [sqrt_eq_rpow, sqrt_eq_rpow, inverse_rpow _ _ (by grind),
        inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind)]
    grind only
  · have ha' : ¬IsUnit (sqrt a) := by rwa [CFC.isUnit_sqrt_iff_isStrictlyPositive]
    obtain (H | H) : ¬0 <= a ∨ ¬IsUn

Depends on / 依赖: CFC.isUnit_sqrt_iff_isStrictlyPositive, CFC.ringInverse_nonneg_iff_nonneg_of_isUnit, IsStrictlyPositive, IsUnit, inverse, inverse_eq_rpow_neg_one, inverse_non_unit, inverse_rpow, inverse_zero, isUnit_sqrt_iff_isStrictlyPositive, ringInverse_nonneg_iff_nonneg_of_isUnit, rpow_rpow, sqrt_eq_rpow, sqrt_of_not_nonneg
-/
lemma sqrt_ringInverse {a : A} : sqrt a⁻¹ʳ = (sqrt a)⁻¹ʳ := by
  by_cases ha : IsStrictlyPositive a
  · rw [sqrt_eq_rpow, sqrt_eq_rpow, inverse_rpow _ _ (by grind),
        inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind)]
    grind only
  · have ha' : ¬IsUnit (sqrt a) := by rwa [CFC.isUnit_sqrt_iff_isStrictlyPositive]
    obtain (H | H) : ¬0 <= a ∨ ¬IsUnit a := by grind
    · rw [sqrt_of_not_nonneg H, inverse_zero]
      by_cases hunit : IsUnit a
      · have h₂ : ¬0 <= inverse a := by grind [CFC.ringInverse_nonneg_iff_nonneg_of_isUnit]
        rw [sqrt_of_not_nonneg h₂]
      · simp [inverse_non_unit _ hunit]
    · simp [inverse_non_unit _ ha', inverse_non_unit _ H]

/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_TFAE` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_TFAE`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_TFAE
  given: {a : A}
  proof: by
  tfae_have 1 ↔ 8 := IsStrictlyPositive.iff_of_unital
  tfae_have 1 ↔ 9 := ⟨fun h => ⟨h.isSelfAdjoint,
.mp h⟩, StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a
    fun h => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).mpr h.2⟩
.symm⟩ tfae_have 1 -> 2 := fun h => ⟨h.sqrt, sqrt_mul_

中文:
定理 _root_.CStar代数.isStrictlyPositive_TFAE
  条件: {a : A}
  证明: by
  tfae_have 1 ↔ 8 := IsStrictlyPositive.iff_of_unital
  tfae_have 1 ↔ 9 := ⟨fun h => ⟨h.isSelfAdjoint,
.mp h⟩, StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a
    fun h => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).mpr h.2⟩
.symm⟩ tfae_have 1 -> 2 := fun h => ⟨h.sqrt, sqrt_mul_

Depends on / 依赖: IsStrictlyPositive, IsStrictlyPositive.iff_of_unital, StarOrderedRing, StarOrderedRing.isStrictlyPositive_iff_spectrum_pos, h.isSelfAdjoint, h.sqrt, hb.isSelfAd, hb.isUnit, iff_of_unital, isSelfAd, isSelfAdjoint, isStrictlyPositive, isStrictlyPositive_iff_spectrum_pos, isUnit, sqrt_mul_sqrt_self, sqrt_nonneg, tfae_have
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_TFAE {a : A} :
    [IsStrictlyPositive a,
     IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a,
     IsUnit (sqrt a) ∧ a = sqrt a * sqrt a,
     exists b, IsStrictlyPositive b ∧ a = b * b,
     exists b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b,
     exists b, IsUnit b ∧ a = star b * b,
     exists b, IsUnit b ∧ a = b * star b,
     0 <= a ∧ IsUnit a,
     IsSelfAdjoint a ∧ forall x in spectrum Real a, 0 < x].TFAE := by
  tfae_have 1 ↔ 8 := IsStrictlyPositive.iff_of_unital
  tfae_have 1 ↔ 9 := ⟨fun h => ⟨h.isSelfAdjoint,
.mp h⟩, StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a
    fun h => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).mpr h.2⟩
.symm⟩ tfae_have 1 -> 2 := fun h => ⟨h.sqrt, sqrt_mul_sqrt_self a
  tfae_have 2 -> 3 := fun h => ⟨h.1.isUnit, h.2⟩
  tfae_have 3 -> 4 := fun h => ⟨sqrt a, h.1.isStrictlyPositive (sqrt_nonneg _), h.2⟩
  tfae_have 4 -> 5 := fun ⟨b, hb, hab⟩ => ⟨b, hb.isUnit, hb.isSelfAdjoint, hab⟩
  tfae_have 5 -> 6 := fun ⟨b, hb, hbsa, hab⟩ => ⟨b, hb, hbsa.symm ▸ hab⟩
.symm ▸ hab⟩ tfae_have 6 -> 7 := fun ⟨b, hb, hab⟩ => ⟨star b, hb.star, star_star b
  tfae_have 7 -> 8 := fun ⟨b, hb, hab⟩ => ⟨hab ▸ mul_star_self_nonneg _, hab ▸ hb.mul hb.star⟩
  tfae_finish

/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 1

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 1

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 1
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 2

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 2

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsUnit (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 2
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 3

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_存在_isStrictlyPositive_and_eq_mul_self
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 3

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ exists b, IsStrictlyPositive b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 3
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 4

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_存在_isUnit_and_isSelfAdjoint_and_eq_mul_self
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 4

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ exists b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 4
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 5

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_eq_star_mul_self
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 5

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
    {a : A} : IsStrictlyPositive a ↔ exists b, IsUnit b ∧ a = star b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 5
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 6

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_eq_mul_star_self
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 6

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, hasProjectiveDimensionLT_zero, isStrictlyPositive_TFAE, isZero_zero
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self
    {a : A} : IsStrictlyPositive a ↔ exists b, IsUnit b ∧ a = b * star b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 6
/--
theorem `_root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos` / 定理 `_root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos`

English:
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
  proof: CStarAlgebra.isStrictlyPositive_TFAE.out 0 8

中文:
定理 _root_.CStar代数.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
  证明: CStarAlgebra.isStrictlyPositive_TFAE.out 0 8

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_TFAE.out, isStrictlyPositive_TFAE
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
    {a : A} : IsStrictlyPositive a ↔ IsSelfAdjoint a ∧ forall x in spectrum Real a, 0 < x :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 8

end unital_vs_nonunital

end Unital

end CFC
