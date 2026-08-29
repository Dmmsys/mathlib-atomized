/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Basic

/-!
# (Semi)normed groups: basic theory

We prove basic properties of (semi)normed groups.

## Tags

normed group
-/

@[expose] public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : Real}

@[to_additive]
/--
theorem `dist_eq_norm_inv_mul` / 定理 `dist_eq_norm_inv_mul`

English:
theorem dist_eq_norm_inv_mul
  given: (a b : E)
  statement: dist a b = ‖a⁻¹ * b‖
  proof: SeminormedGroup.dist_eq _ _

@[to_additive]

中文:
定理 dist_eq_norm_inv_mul
  条件: (a b : E)
  结论: dist a b = ‖a⁻¹ * b‖
  证明: SeminormedGroup.dist_eq _ _

@[to_additive]

Depends on / 依赖: SeminormedGroup, SeminormedGroup.dist_eq, dist_eq
-/
theorem dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ * b‖ :=
  SeminormedGroup.dist_eq _ _

@[to_additive]
/--
theorem `dist_eq_norm_inv_mul'` / 定理 `dist_eq_norm_inv_mul'`

English:
theorem dist_eq_norm_inv_mul'
  given: (a b : E)
  statement: dist a b = ‖b⁻¹ * a‖
  proof: by
  rw [dist_comm]; rw [dist_eq_norm_inv_mul]

@[to_additive of_forall_le_norm]

中文:
定理 dist_eq_norm_inv_mul'
  条件: (a b : E)
  结论: dist a b = ‖b⁻¹ * a‖
  证明: by
  rw [dist_comm]; rw [dist_eq_norm_inv_mul]

@[to_additive of_forall_le_norm]

Depends on / 依赖: dist_comm, dist_eq_norm_inv_mul
-/
theorem dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹ * a‖ := by
  rw [dist_comm]; rw [dist_eq_norm_inv_mul]

@[to_additive of_forall_le_norm]
/--
lemma `DiscreteTopology.of_forall_le_norm'` / 引理 `DiscreteTopology.of_forall_le_norm'`

English:
lemma DiscreteTopology.of_forall_le_norm'
  given: (hpos : 0 < r) (hr : forall x : E, x != 1 -> r <= ‖x‖)
  proof: .of_forall_le_dist hpos fun x y hne => by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]

中文:
引理 DiscreteTopology.of_forall_le_norm'
  条件: (hpos : 0 < r) (hr : 对任意 x : E, x != 1 -> r <= ‖x‖)
  证明: .of_forall_le_dist hpos fun x y hne => by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]

Depends on / 依赖: dist_eq_norm_inv_mul, inv_mul_eq_one, of_forall_le_dist
-/
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : forall x : E, x != 1 -> r <= ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne => by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]
/--
theorem `dist_one_right` / 定理 `dist_one_right`

English:
theorem dist_one_right
  given: (a : E)
  statement: dist a 1 = ‖a‖
  proof: by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]

中文:
定理 dist_one_right
  条件: (a : E)
  结论: dist a 1 = ‖a‖
  证明: by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, inv_one, one_mul
-/
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]
/--
theorem `inseparable_one_iff_norm` / 定理 `inseparable_one_iff_norm`

English:
theorem inseparable_one_iff_norm
  given: {a : E}
  statement: Inseparable a 1 ↔ ‖a‖ = 0
  proof: by
  rw [Metric.inseparable_iff]; rw [dist_one_right]

@[to_additive]

中文:
定理 inseparable_one_iff_norm
  条件: {a : E}
  结论: Inseparable a 1 ↔ ‖a‖ = 0
  证明: by
  rw [Metric.inseparable_iff]; rw [dist_one_right]

@[to_additive]

Depends on / 依赖: Metric, Metric.inseparable_iff, dist_one_right, inseparable_iff
-/
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by
  rw [Metric.inseparable_iff]; rw [dist_one_right]

@[to_additive]
/--
lemma `dist_one_left` / 引理 `dist_one_left`

English:
lemma dist_one_left
  given: (a : E)
  statement: dist 1 a = ‖a‖
  proof: by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]

中文:
引理 dist_one_left
  条件: (a : E)
  结论: dist 1 a = ‖a‖
  证明: by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_comm, dist_one_right
-/
lemma dist_one_left (a : E) : dist 1 a = ‖a‖ := by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]
/--
lemma `dist_one` / 引理 `dist_one`

English:
lemma dist_one
  statement: dist (1 : E) = norm
  proof: funext dist_one_left

@[to_additive]

中文:
引理 dist_one
  结论: dist (1 : E) = norm
  证明: funext dist_one_left

@[to_additive]

Depends on / 依赖: dist_one_left
-/
lemma dist_one : dist (1 : E) = norm := funext dist_one_left

@[to_additive]
/--
theorem `norm_div_rev` / 定理 `norm_div_rev`

English:
theorem norm_div_rev
  given: (a b : E)
  statement: ‖a / b‖ = ‖b / a‖
  proof: by
  rw [← dist_one]; rw [dist_eq_norm_inv_mul]; rw [dist_eq_norm_inv_mul']
  simp

@[to_additive (attr := simp) norm_neg]

中文:
定理 norm_div_rev
  条件: (a b : E)
  结论: ‖a / b‖ = ‖b / a‖
  证明: by
  rw [← dist_one]; rw [dist_eq_norm_inv_mul]; rw [dist_eq_norm_inv_mul']
  simp

@[to_additive (attr := simp) norm_neg]

Depends on / 依赖: dist_eq_norm_inv_mul, dist_one
-/
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  rw [← dist_one]; rw [dist_eq_norm_inv_mul]; rw [dist_eq_norm_inv_mul']
  simp

@[to_additive (attr := simp) norm_neg]
/--
theorem `norm_inv'` / 定理 `norm_inv'`

English:
theorem norm_inv'
  given: (a : E)
  statement: ‖a⁻¹‖ = ‖a‖
  proof: by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]

中文:
定理 norm_inv'
  条件: (a : E)
  结论: ‖a⁻¹‖ = ‖a‖
  证明: by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]

Depends on / 依赖: norm_div_rev
-/
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]
/--
theorem `norm_zpow_abs` / 定理 `norm_zpow_abs`

English:
theorem norm_zpow_abs
  given: (a : E) (n : Int)
  statement: ‖a ^ |n|‖ = ‖a ^ n‖
  proof: by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]

中文:
定理 norm_zpow_abs
  条件: (a : E) (n : 整数)
  结论: ‖a ^ |n|‖ = ‖a ^ n‖
  证明: by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_total
-/
theorem norm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖ = ‖a ^ n‖ := by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]
/--
theorem `norm_pow_natAbs` / 定理 `norm_pow_natAbs`

English:
theorem norm_pow_natAbs
  given: (a : E) (n : Int)
  statement: ‖a ^ n.natAbs‖ = ‖a ^ n‖
  proof: by
  rw [← zpow_natCast]; rw [← Int.abs_eq_natAbs]; rw [norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]

中文:
定理 norm_pow_natAbs
  条件: (a : E) (n : 整数)
  结论: ‖a ^ n.natAbs‖ = ‖a ^ n‖
  证明: by
  rw [← zpow_natCast]; rw [← Int.abs_eq_natAbs]; rw [norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]

Depends on / 依赖: Int.abs_eq_natAbs, abs_eq_natAbs, norm_zpow_abs, zpow_natCast
-/
theorem norm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖ = ‖a ^ n‖ := by
  rw [← zpow_natCast]; rw [← Int.abs_eq_natAbs]; rw [norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]
/--
theorem `norm_zpow_isUnit` / 定理 `norm_zpow_isUnit`

English:
theorem norm_zpow_isUnit
  given: (a : E) {n : Int} (hn : IsUnit n)
  statement: ‖a ^ n‖ = ‖a‖
  proof: by
  rw [← norm_pow_natAbs]; rw [Int.isUnit_iff_natAbs_eq.mp hn]; rw [pow_one]

@[simp]

中文:
定理 norm_zpow_isUnit
  条件: (a : E) {n : 整数} (hn : IsUnit n)
  结论: ‖a ^ n‖ = ‖a‖
  证明: by
  rw [← norm_pow_natAbs]; rw [Int.isUnit_iff_natAbs_eq.mp hn]; rw [pow_one]

@[simp]

Depends on / 依赖: Int.isUnit_iff_natAbs_eq.mp, isUnit_iff_natAbs_eq, norm_pow_natAbs, pow_one
-/
theorem norm_zpow_isUnit (a : E) {n : Int} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖ := by
  rw [← norm_pow_natAbs]; rw [Int.isUnit_iff_natAbs_eq.mp hn]; rw [pow_one]

@[simp]
/--
theorem `norm_units_zsmul` / 定理 `norm_units_zsmul`

English:
theorem norm_units_zsmul
  given: {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E)
  statement: ‖n • a‖ = ‖a‖
  proof: norm_isUnit_zsmul a n.isUnit

中文:
定理 norm_units_zsmul
  条件: {E : 类型} [SeminormedAddGroup E] (n : 整数ˣ) (a : E)
  结论: ‖n • a‖ = ‖a‖
  证明: norm_isUnit_zsmul a n.isUnit

Depends on / 依赖: isUnit, n.isUnit, norm_isUnit_zsmul
-/
theorem norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E) : ‖n • a‖ = ‖a‖ :=
  norm_isUnit_zsmul a n.isUnit

open scoped symmDiff in
@[to_additive]
/--
theorem `dist_mulIndicator` / 定理 `dist_mulIndicator`

English:
theorem dist_mulIndicator
  given: (s t : Set α) (f : α -> E) (x : α)
  proof: by
  rw [dist_eq_norm_inv_mul]; rw [Set.apply_mulIndicator_symmDiff norm_inv']
  simp only [Set.mulIndicator, mul_ite, mul_one]
  split_ifs <;> simp

中文:
定理 dist_mulIndicator
  条件: (s t : Set α) (f : α -> E) (x : α)
  证明: by
  rw [dist_eq_norm_inv_mul]; rw [Set.apply_mulIndicator_symmDiff norm_inv']
  simp only [Set.mulIndicator, mul_ite, mul_one]
  split_ifs <;> simp

Depends on / 依赖: Set.apply_mulIndicator_symmDiff, Set.mulIndicator, apply_mulIndicator_symmDiff, dist_eq_norm_inv_mul, mulIndicator, mul_ite, mul_one, norm_inv, split_ifs
-/
theorem dist_mulIndicator (s t : Set α) (f : α -> E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_inv_mul]; rw [Set.apply_mulIndicator_symmDiff norm_inv']
  simp only [Set.mulIndicator, mul_ite, mul_one]
  split_ifs <;> simp

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le /-- **Triangle inequality** for the norm. -/]
/--
theorem `norm_mul_le'` / 定理 `norm_mul_le'`

English:
theorem norm_mul_le'
  given: (a b : E)
  statement: ‖a * b‖ <= ‖a‖ + ‖b‖
  proof: by
  simpa [dist_eq_norm_inv_mul] using dist_triangle a⁻¹ 1 b

中文:
定理 norm_mul_le'
  条件: (a b : E)
  结论: ‖a * b‖ <= ‖a‖ + ‖b‖
  证明: by
  simpa [dist_eq_norm_inv_mul] using dist_triangle a⁻¹ 1 b

Depends on / 依赖: dist_eq_norm_inv_mul, dist_triangle
-/
theorem norm_mul_le' (a b : E) : ‖a * b‖ <= ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using dist_triangle a⁻¹ 1 b

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le_of_le /-- **Triangle inequality** for the norm. -/]
/--
theorem `norm_mul_le_of_le'` / 定理 `norm_mul_le_of_le'`

English:
theorem norm_mul_le_of_le'
  given: (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂)
  statement: ‖a₁ * a₂‖ <= r₁ + r₂
  proof: (norm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

中文:
定理 norm_mul_le_of_le'
  条件: (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂)
  结论: ‖a₁ * a₂‖ <= r₁ + r₂
  证明: (norm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

Depends on / 依赖: add_le_add, norm_mul_le
-/
theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂) : ‖a₁ * a₂‖ <= r₁ + r₂ :=
(norm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₃_le /-- **Triangle inequality** for the norm. -/]
/--
lemma `norm_mul₃_le'` / 引理 `norm_mul₃_le'`

English:
lemma norm_mul₃_le'
  statement: ‖a * b * c‖ <= ‖a‖ + ‖b‖ + ‖c‖
  proof: norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

中文:
引理 norm_mul₃_le'
  结论: ‖a * b * c‖ <= ‖a‖ + ‖b‖ + ‖c‖
  证明: norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

Depends on / 依赖: le_rfl, norm_mul_le, norm_mul_le_of_le
-/
lemma norm_mul₃_le' : ‖a * b * c‖ <= ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₄_le /-- **Triangle inequality** for the norm. -/]
/--
lemma `norm_mul₄_le'` / 引理 `norm_mul₄_le'`

English:
lemma norm_mul₄_le'
  statement: ‖a * b * c * d‖ <= ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
  proof: norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]

中文:
引理 norm_mul₄_le'
  结论: ‖a * b * c * d‖ <= ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
  证明: norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]

Depends on / 依赖: le_rfl, norm_mul_le_of_le
-/
lemma norm_mul₄_le' : ‖a * b * c * d‖ <= ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]
/--
lemma `norm_div_le_norm_div_add_norm_div` / 引理 `norm_div_le_norm_div_add_norm_div`

English:
lemma norm_div_le_norm_div_add_norm_div
  given: (a b c : E)
  statement: ‖a / c‖ <= ‖a / b‖ + ‖b / c‖
  proof: by
  simpa using norm_mul_le' (a / b) (b / c)

@[to_additive]

中文:
引理 norm_div_le_norm_div_add_norm_div
  条件: (a b c : E)
  结论: ‖a / c‖ <= ‖a / b‖ + ‖b / c‖
  证明: by
  simpa using norm_mul_le' (a / b) (b / c)

@[to_additive]

Depends on / 依赖: norm_mul_le
-/
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ <= ‖a / b‖ + ‖b / c‖ := by
  simpa using norm_mul_le' (a / b) (b / c)

@[to_additive]
/--
lemma `norm_le_norm_div_add` / 引理 `norm_le_norm_div_add`

English:
lemma norm_le_norm_div_add
  given: (a b : E)
  statement: ‖a‖ <= ‖a / b‖ + ‖b‖
  proof: by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]

中文:
引理 norm_le_norm_div_add
  条件: (a b : E)
  结论: ‖a‖ <= ‖a / b‖ + ‖b‖
  证明: by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]

Depends on / 依赖: div_one, norm_div_le_norm_div_add_norm_div
-/
lemma norm_le_norm_div_add (a b : E) : ‖a‖ <= ‖a / b‖ + ‖b‖ := by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]
/--
theorem `norm_nonneg'` / 定理 `norm_nonneg'`

English:
theorem norm_nonneg'
  given: (a : E)
  statement: 0 <= ‖a‖
  proof: by
  rw [← dist_one_right]
  exact dist_nonneg

中文:
定理 norm_nonneg'
  条件: (a : E)
  结论: 0 <= ‖a‖
  证明: by
  rw [← dist_one_right]
  exact dist_nonneg

Depends on / 依赖: dist_nonneg, dist_one_right
-/
theorem norm_nonneg' (a : E) : 0 <= ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg

attribute [bound] norm_nonneg
attribute [grind .] norm_nonneg

@[to_additive (attr := simp) abs_norm]
/--
theorem `abs_norm'` / 定理 `abs_norm'`

English:
theorem abs_norm'
  given: (z : E)
  statement: |‖z‖| = ‖z‖
  proof: abs_of_nonneg norm_nonneg' _

@[to_additive (attr := simp) norm_zero]

中文:
定理 abs_norm'
  条件: (z : E)
  结论: |‖z‖| = ‖z‖
  证明: abs_of_nonneg norm_nonneg' _

@[to_additive (attr := simp) norm_zero]

Depends on / 依赖: abs_of_nonneg, norm_nonneg
-/
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg norm_nonneg' _

@[to_additive (attr := simp) norm_zero]
/--
theorem `norm_one'` / 定理 `norm_one'`

English:
theorem norm_one'
  statement: ‖(1 : E)‖ = 0
  proof: by rw [← dist_one_right, dist_self]

@[to_additive]

中文:
定理 norm_one'
  结论: ‖(1 : E)‖ = 0
  证明: by rw [← dist_one_right, dist_self]

@[to_additive]

Depends on / 依赖: dist_one_right, dist_self
-/
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]

@[to_additive]
/--
theorem `ne_one_of_norm_ne_zero` / 定理 `ne_one_of_norm_ne_zero`

English:
theorem ne_one_of_norm_ne_zero
  statement: ‖a‖ != 0 -> a != 1
  proof: mt by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]

中文:
定理 ne_one_of_norm_ne_zero
  结论: ‖a‖ != 0 -> a != 1
  证明: mt by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]

Depends on / 依赖: norm_one
-/
theorem ne_one_of_norm_ne_zero : ‖a‖ != 0 -> a != 1 :=
mt by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]
/--
theorem `norm_of_subsingleton'` / 定理 `norm_of_subsingleton'`

English:
theorem norm_of_subsingleton'
  given: [Subsingleton E] (a : E)
  statement: ‖a‖ = 0
  proof: by
  rw [Subsingleton.elim a 1]; rw [norm_one']

@[to_additive zero_lt_one_add_norm_sq]

中文:
定理 norm_of_subsingleton'
  条件: [Subsingleton E] (a : E)
  结论: ‖a‖ = 0
  证明: by
  rw [Subsingleton.elim a 1]; rw [norm_one']

@[to_additive zero_lt_one_add_norm_sq]

Depends on / 依赖: Subsingleton, Subsingleton.elim, norm_one
-/
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by
  rw [Subsingleton.elim a 1]; rw [norm_one']

@[to_additive zero_lt_one_add_norm_sq]
/--
theorem `zero_lt_one_add_norm_sq'` / 定理 `zero_lt_one_add_norm_sq'`

English:
theorem zero_lt_one_add_norm_sq'
  given: (x : E)
  statement: 0 < 1 + ‖x‖ ^ 2
  proof: by
  positivity

@[to_additive]

中文:
定理 zero_lt_one_add_norm_sq'
  条件: (x : E)
  结论: 0 < 1 + ‖x‖ ^ 2
  证明: by
  positivity

@[to_additive]
-/
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by
  positivity

@[to_additive]
/--
theorem `norm_div_le` / 定理 `norm_div_le`

English:
theorem norm_div_le
  given: (a b : E)
  statement: ‖a / b‖ <= ‖a‖ + ‖b‖
  proof: by
  simpa [div_eq_mul_inv] using norm_mul_le' a b⁻¹

中文:
定理 norm_div_le
  条件: (a b : E)
  结论: ‖a / b‖ <= ‖a‖ + ‖b‖
  证明: by
  simpa [div_eq_mul_inv] using norm_mul_le' a b⁻¹

Depends on / 依赖: div_eq_mul_inv, norm_mul_le
-/
theorem norm_div_le (a b : E) : ‖a / b‖ <= ‖a‖ + ‖b‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le' a b⁻¹

attribute [bound] norm_sub_le

@[to_additive]
/--
theorem `norm_div_le_of_le` / 定理 `norm_div_le_of_le`

English:
theorem norm_div_le_of_le
  given: {r₁ r₂ : Real} (H₁ : ‖a₁‖ <= r₁) (H₂ : ‖a₂‖ <= r₂)
  statement: ‖a₁ / a₂‖ <= r₁ + r₂
  proof: (norm_div_le a₁ a₂).trans add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]

中文:
定理 norm_div_le_of_le
  条件: {r₁ r₂ : 实数} (H₁ : ‖a₁‖ <= r₁) (H₂ : ‖a₂‖ <= r₂)
  结论: ‖a₁ / a₂‖ <= r₁ + r₂
  证明: (norm_div_le a₁ a₂).trans add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]

Depends on / 依赖: add_le_add, norm_div_le
-/
theorem norm_div_le_of_le {r₁ r₂ : Real} (H₁ : ‖a₁‖ <= r₁) (H₂ : ‖a₂‖ <= r₂) : ‖a₁ / a₂‖ <= r₁ + r₂ :=
(norm_div_le a₁ a₂).trans add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]
/--
theorem `dist_le_norm_add_norm'` / 定理 `dist_le_norm_add_norm'`

English:
theorem dist_le_norm_add_norm'
  given: (a b : E)
  statement: dist a b <= ‖a‖ + ‖b‖
  proof: by
  simpa [dist_eq_norm_inv_mul] using norm_mul_le' a⁻¹ b

@[to_additive]

中文:
定理 dist_le_norm_add_norm'
  条件: (a b : E)
  结论: dist a b <= ‖a‖ + ‖b‖
  证明: by
  simpa [dist_eq_norm_inv_mul] using norm_mul_le' a⁻¹ b

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, norm_mul_le
-/
theorem dist_le_norm_add_norm' (a b : E) : dist a b <= ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using norm_mul_le' a⁻¹ b

@[to_additive]
/--
theorem `abs_norm_sub_norm_le_norm_inv_mul` / 定理 `abs_norm_sub_norm_le_norm_inv_mul`

English:
theorem abs_norm_sub_norm_le_norm_inv_mul
  given: (a b : E)
  statement: |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
  proof: by
  simpa [dist_eq_norm_inv_mul] using abs_dist_sub_le a b 1

@[to_additive]

中文:
定理 abs_norm_sub_norm_le_norm_inv_mul
  条件: (a b : E)
  结论: |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖
  证明: by
  simpa [dist_eq_norm_inv_mul] using abs_dist_sub_le a b 1

@[to_additive]

Depends on / 依赖: abs_dist_sub_le, dist_eq_norm_inv_mul
-/
theorem abs_norm_sub_norm_le_norm_inv_mul (a b : E) : |‖a‖ - ‖b‖| <= ‖a⁻¹ * b‖ := by
  simpa [dist_eq_norm_inv_mul] using abs_dist_sub_le a b 1

@[to_additive]
/--
theorem `norm_sub_norm_le_norm_inv_mul` / 定理 `norm_sub_norm_le_norm_inv_mul`

English:
theorem norm_sub_norm_le_norm_inv_mul
  given: (a b : E)
  statement: ‖a‖ - ‖b‖ <= ‖a⁻¹ * b‖
  proof: (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]

中文:
定理 norm_sub_norm_le_norm_inv_mul
  条件: (a b : E)
  结论: ‖a‖ - ‖b‖ <= ‖a⁻¹ * b‖
  证明: (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]

Depends on / 依赖: abs_norm_sub_norm_le_norm_inv_mul, le_abs_self
-/
theorem norm_sub_norm_le_norm_inv_mul (a b : E) : ‖a‖ - ‖b‖ <= ‖a⁻¹ * b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]
/--
theorem `norm_sub_le_norm_mul` / 定理 `norm_sub_le_norm_mul`

English:
theorem norm_sub_le_norm_mul
  given: (a b : E)
  statement: ‖a‖ - ‖b‖ <= ‖a * b‖
  proof: by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive]

中文:
定理 norm_sub_le_norm_mul
  条件: (a b : E)
  结论: ‖a‖ - ‖b‖ <= ‖a * b‖
  证明: by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive]

Depends on / 依赖: norm_mul_le
-/
theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ <= ‖a * b‖ := by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive]
/--
theorem `dist_norm_norm_le_norm_inv_mul` / 定理 `dist_norm_norm_le_norm_inv_mul`

English:
theorem dist_norm_norm_le_norm_inv_mul
  given: (a b : E)
  statement: dist ‖a‖ ‖b‖ <= ‖a⁻¹ * b‖
  proof: abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]

中文:
定理 dist_norm_norm_le_norm_inv_mul
  条件: (a b : E)
  结论: dist ‖a‖ ‖b‖ <= ‖a⁻¹ * b‖
  证明: abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]

Depends on / 依赖: abs_norm_sub_norm_le_norm_inv_mul
-/
theorem dist_norm_norm_le_norm_inv_mul (a b : E) : dist ‖a‖ ‖b‖ <= ‖a⁻¹ * b‖ :=
  abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]
/--
theorem `norm_le_norm_add_norm_div'` / 定理 `norm_le_norm_add_norm_div'`

English:
theorem norm_le_norm_add_norm_div'
  given: (u v : E)
  statement: ‖u‖ <= ‖v‖ + ‖u / v‖
  proof: by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]

中文:
定理 norm_le_norm_add_norm_div'
  条件: (u v : E)
  结论: ‖u‖ <= ‖v‖ + ‖u / v‖
  证明: by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]

Depends on / 依赖: add_comm, div_mul_cancel, norm_mul_le, trans_eq
-/
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ <= ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]
/--
theorem `norm_le_norm_add_norm_inv_mul` / 定理 `norm_le_norm_add_norm_inv_mul`

English:
theorem norm_le_norm_add_norm_inv_mul
  given: (u v : E)
  statement: ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
  proof: by
  rw [add_comm]; rw [← norm_inv' v]; rw [← norm_inv' u]
  refine (norm_mul_le' _ _).trans_eq' ?_
  group

@[to_additive]

中文:
定理 norm_le_norm_add_norm_inv_mul
  条件: (u v : E)
  结论: ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
  证明: by
  rw [add_comm]; rw [← norm_inv' v]; rw [← norm_inv' u]
  refine (norm_mul_le' _ _).trans_eq' ?_
  group

@[to_additive]

Depends on / 依赖: add_comm, norm_inv, norm_mul_le, trans_eq
-/
theorem norm_le_norm_add_norm_inv_mul (u v : E) : ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖ := by
  rw [add_comm]; rw [← norm_inv' v]; rw [← norm_inv' u]
  refine (norm_mul_le' _ _).trans_eq' ?_
  group

@[to_additive]
/--
theorem `norm_le_norm_add_norm_div` / 定理 `norm_le_norm_add_norm_div`

English:
theorem norm_le_norm_add_norm_div
  given: (u v : E)
  statement: ‖v‖ <= ‖u‖ + ‖u / v‖
  proof: by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]

中文:
定理 norm_le_norm_add_norm_div
  条件: (u v : E)
  结论: ‖v‖ <= ‖u‖ + ‖u / v‖
  证明: by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]

Depends on / 依赖: norm_div_rev, norm_le_norm_add_norm_div
-/
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ <= ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]
/--
theorem `norm_le_mul_norm_add` / 定理 `norm_le_mul_norm_add`

English:
theorem norm_le_mul_norm_add
  given: (u v : E)
  statement: ‖u‖ <= ‖u * v‖ + ‖v‖
  proof: calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ <= ‖u * v‖ + ‖v‖ := norm_div_le _ _

中文:
定理 norm_le_mul_norm_add
  条件: (u v : E)
  结论: ‖u‖ <= ‖u * v‖ + ‖v‖
  证明: calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ <= ‖u * v‖ + ‖v‖ := norm_div_le _ _

Depends on / 依赖: mul_div_cancel_right, norm_div_le
-/
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ <= ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ <= ‖u * v‖ + ‖v‖ := norm_div_le _ _

/-- An analogue of `norm_le_mul_norm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `norm_le_add_norm_add` for the addition from the left. -/]
/--
theorem `norm_le_mul_norm_add'` / 定理 `norm_le_mul_norm_add'`

English:
theorem norm_le_mul_norm_add'
  given: (u v : E)
  statement: ‖v‖ <= ‖u * v‖ + ‖u‖
  proof: calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ <= ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]

中文:
定理 norm_le_mul_norm_add'
  条件: (u v : E)
  结论: ‖v‖ <= ‖u * v‖ + ‖u‖
  证明: calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ <= ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]

Depends on / 依赖: add_comm, inv_mul_cancel, mul_assoc, norm_inv, norm_mul_le, one_mul
-/
theorem norm_le_mul_norm_add' (u v : E) : ‖v‖ <= ‖u * v‖ + ‖u‖ :=
  calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ <= ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]
/--
lemma `norm_mul_eq_norm_right` / 引理 `norm_mul_eq_norm_right`

English:
lemma norm_mul_eq_norm_right
  given: {x : E} (y : E) (h : ‖x‖ = 0)
  statement: ‖x * y‖ = ‖y‖
  proof: by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]

中文:
引理 norm_mul_eq_norm_right
  条件: {x : E} (y : E) (h : ‖x‖ = 0)
  结论: ‖x * y‖ = ‖y‖
  证明: by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]

Depends on / 依赖: le_antisymm, norm_le_mul_norm_add, norm_mul_le
-/
lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]
/--
lemma `norm_mul_eq_norm_left` / 引理 `norm_mul_eq_norm_left`

English:
lemma norm_mul_eq_norm_left
  given: (x : E) {y : E} (h : ‖y‖ = 0)
  statement: ‖x * y‖ = ‖x‖
  proof: by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]

中文:
引理 norm_mul_eq_norm_left
  条件: (x : E) {y : E} (h : ‖y‖ = 0)
  结论: ‖x * y‖ = ‖x‖
  证明: by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]

Depends on / 依赖: le_antisymm, norm_le_mul_norm_add, norm_mul_le
-/
lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]
/--
lemma `norm_div_eq_norm_right` / 引理 `norm_div_eq_norm_right`

English:
lemma norm_div_eq_norm_right
  given: {x : E} (y : E) (h : ‖x‖ = 0)
  statement: ‖x / y‖ = ‖y‖
  proof: by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_right _ h]; rw [norm_inv']

@[to_additive]

中文:
引理 norm_div_eq_norm_right
  条件: {x : E} (y : E) (h : ‖x‖ = 0)
  结论: ‖x / y‖ = ‖y‖
  证明: by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_right _ h]; rw [norm_inv']

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, norm_inv, norm_mul_eq_norm_right
-/
lemma norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖ := by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_right _ h]; rw [norm_inv']

@[to_additive]
/--
lemma `norm_div_eq_norm_left` / 引理 `norm_div_eq_norm_left`

English:
lemma norm_div_eq_norm_left
  given: (x : E) {y : E} (h : ‖y‖ = 0)
  statement: ‖x / y‖ = ‖x‖
  proof: by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_left]
  rwa [norm_inv']

@[to_additive]

中文:
引理 norm_div_eq_norm_left
  条件: (x : E) {y : E} (h : ‖y‖ = 0)
  结论: ‖x / y‖ = ‖x‖
  证明: by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_left]
  rwa [norm_inv']

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, norm_inv, norm_mul_eq_norm_left
-/
lemma norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖ := by
  rw [div_eq_mul_inv]; rw [norm_mul_eq_norm_left]
  rwa [norm_inv']

@[to_additive]
/--
theorem `ball_eq_norm_inv_mul_lt` / 定理 `ball_eq_norm_inv_mul_lt`

English:
theorem ball_eq_norm_inv_mul_lt
  given: (y : E) (ε : Real)
  statement: ball y ε = { x | ‖x⁻¹ * y‖ < ε }
  proof: Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 ball_eq_norm_inv_mul_lt
  条件: (y : E) (ε : 实数)
  结论: ball y ε = { x | ‖x⁻¹ * y‖ < ε }
  证明: Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: Set.ext, dist_eq_norm_inv_mul
-/
theorem ball_eq_norm_inv_mul_lt (y : E) (ε : Real) : ball y ε = { x | ‖x⁻¹ * y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `ball_one_eq` / 定理 `ball_one_eq`

English:
theorem ball_one_eq
  given: (r : Real)
  statement: ball (1 : E) r = { x | ‖x‖ < r }
  proof: Set.ext fun a => by simp

@[to_additive]

中文:
定理 ball_one_eq
  条件: (r : 实数)
  结论: ball (1 : E) r = { x | ‖x‖ < r }
  证明: Set.ext fun a => by simp

@[to_additive]

Depends on / 依赖: Set.ext
-/
theorem ball_one_eq (r : Real) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp

@[to_additive]
/--
theorem `mem_ball_iff_norm_inv_mul_lt` / 定理 `mem_ball_iff_norm_inv_mul_lt`

English:
theorem mem_ball_iff_norm_inv_mul_lt
  statement: b in ball a r ↔ ‖b⁻¹ * a‖ < r
  proof: by
  rw [mem_ball]; rw [dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 mem_ball_iff_norm_inv_mul_lt
  结论: b in ball a r ↔ ‖b⁻¹ * a‖ < r
  证明: by
  rw [mem_ball]; rw [dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_ball
-/
theorem mem_ball_iff_norm_inv_mul_lt : b in ball a r ↔ ‖b⁻¹ * a‖ < r := by
  rw [mem_ball]; rw [dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `mem_ball_iff_norm_inv_mul_lt'` / 定理 `mem_ball_iff_norm_inv_mul_lt'`

English:
theorem mem_ball_iff_norm_inv_mul_lt'
  statement: b in ball a r ↔ ‖a⁻¹ * b‖ < r
  proof: by
  rw [mem_ball']; rw [dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 mem_ball_iff_norm_inv_mul_lt'
  结论: b in ball a r ↔ ‖a⁻¹ * b‖ < r
  证明: by
  rw [mem_ball']; rw [dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_ball
-/
theorem mem_ball_iff_norm_inv_mul_lt' : b in ball a r ↔ ‖a⁻¹ * b‖ < r := by
  rw [mem_ball']; rw [dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `mem_ball_one_iff` / 定理 `mem_ball_one_iff`

English:
theorem mem_ball_one_iff
  statement: a in ball (1 : E) r ↔ ‖a‖ < r
  proof: by rw [mem_ball, dist_one_right]

@[to_additive]

中文:
定理 mem_ball_one_iff
  结论: a in ball (1 : E) r ↔ ‖a‖ < r
  证明: by rw [mem_ball, dist_one_right]

@[to_additive]

Depends on / 依赖: dist_one_right, mem_ball
-/
theorem mem_ball_one_iff : a in ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive]
/--
theorem `mem_closedBall_iff_norm_inv_mul_le` / 定理 `mem_closedBall_iff_norm_inv_mul_le`

English:
theorem mem_closedBall_iff_norm_inv_mul_le
  statement: b in closedBall a r ↔ ‖b⁻¹ * a‖ <= r
  proof: by
  rw [mem_closedBall]; rw [dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 mem_closedBall_iff_norm_inv_mul_le
  结论: b in closedBall a r ↔ ‖b⁻¹ * a‖ <= r
  证明: by
  rw [mem_closedBall]; rw [dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_closedBall
-/
theorem mem_closedBall_iff_norm_inv_mul_le : b in closedBall a r ↔ ‖b⁻¹ * a‖ <= r := by
  rw [mem_closedBall]; rw [dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `mem_closedBall_one_iff` / 定理 `mem_closedBall_one_iff`

English:
theorem mem_closedBall_one_iff
  statement: a in closedBall (1 : E) r ↔ ‖a‖ <= r
  proof: by
  rw [mem_closedBall]; rw [dist_one_right]

@[to_additive]

中文:
定理 mem_closedBall_one_iff
  结论: a in closedBall (1 : E) r ↔ ‖a‖ <= r
  证明: by
  rw [mem_closedBall]; rw [dist_one_right]

@[to_additive]

Depends on / 依赖: dist_one_right, mem_closedBall
-/
theorem mem_closedBall_one_iff : a in closedBall (1 : E) r ↔ ‖a‖ <= r := by
  rw [mem_closedBall]; rw [dist_one_right]

@[to_additive]
/--
theorem `mem_closedBall_iff_norm_inv_mul_le'` / 定理 `mem_closedBall_iff_norm_inv_mul_le'`

English:
theorem mem_closedBall_iff_norm_inv_mul_le'
  statement: b in closedBall a r ↔ ‖a⁻¹ * b‖ <= r
  proof: by
  rw [mem_closedBall']; rw [dist_eq_norm_inv_mul]

@[to_additive norm_le_of_mem_closedBall]

中文:
定理 mem_closedBall_iff_norm_inv_mul_le'
  结论: b in closedBall a r ↔ ‖a⁻¹ * b‖ <= r
  证明: by
  rw [mem_closedBall']; rw [dist_eq_norm_inv_mul]

@[to_additive norm_le_of_mem_closedBall]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_closedBall
-/
theorem mem_closedBall_iff_norm_inv_mul_le' : b in closedBall a r ↔ ‖a⁻¹ * b‖ <= r := by
  rw [mem_closedBall']; rw [dist_eq_norm_inv_mul]

@[to_additive norm_le_of_mem_closedBall]
/--
theorem `norm_le_of_mem_closedBall'` / 定理 `norm_le_of_mem_closedBall'`

English:
theorem norm_le_of_mem_closedBall'
  given: (h : b in closedBall a r)
  statement: ‖b‖ <= ‖a‖ + r
  proof: (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]

中文:
定理 norm_le_of_mem_closedBall'
  条件: (h : b in closedBall a r)
  结论: ‖b‖ <= ‖a‖ + r
  证明: (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]

Depends on / 依赖: mem_closedBall_iff_norm_inv_mul_le, norm_le_norm_add_norm_inv_mul
-/
theorem norm_le_of_mem_closedBall' (h : b in closedBall a r) : ‖b‖ <= ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]
/--
theorem `norm_le_norm_add_const_of_dist_le'` / 定理 `norm_le_norm_add_const_of_dist_le'`

English:
theorem norm_le_norm_add_const_of_dist_le'
  statement: dist a b <= r -> ‖a‖ <= ‖b‖ + r
  proof: norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]

中文:
定理 norm_le_norm_add_const_of_dist_le'
  结论: dist a b <= r -> ‖a‖ <= ‖b‖ + r
  证明: norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]

Depends on / 依赖: norm_le_of_mem_closedBall
-/
theorem norm_le_norm_add_const_of_dist_le' : dist a b <= r -> ‖a‖ <= ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
/--
theorem `norm_lt_of_mem_ball'` / 定理 `norm_lt_of_mem_ball'`

English:
theorem norm_lt_of_mem_ball'
  given: (h : b in ball a r)
  statement: ‖b‖ < ‖a‖ + r
  proof: (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]

中文:
定理 norm_lt_of_mem_ball'
  条件: (h : b in ball a r)
  结论: ‖b‖ < ‖a‖ + r
  证明: (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]

Depends on / 依赖: mem_ball_iff_norm_inv_mul_lt, norm_le_norm_add_norm_inv_mul, trans_lt
-/
theorem norm_lt_of_mem_ball' (h : b in ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]
/--
theorem `norm_div_sub_norm_div_le_norm_div` / 定理 `norm_div_sub_norm_div_le_norm_div`

English:
theorem norm_div_sub_norm_div_le_norm_div
  given: (u v w : E)
  statement: ‖u / w‖ - ‖v / w‖ <= ‖u / v‖
  proof: by
  simpa using norm_mul_le' (u / v) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]

中文:
定理 norm_div_sub_norm_div_le_norm_div
  条件: (u v w : E)
  结论: ‖u / w‖ - ‖v / w‖ <= ‖u / v‖
  证明: by
  simpa using norm_mul_le' (u / v) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]

Depends on / 依赖: norm_mul_le
-/
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ <= ‖u / v‖ := by
  simpa using norm_mul_le' (u / v) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]
/--
lemma `norm_mul_sub_norm_div_le_two_mul` / 引理 `norm_mul_sub_norm_div_le_two_mul`

English:
lemma norm_mul_sub_norm_div_le_two_mul
  given: {E : Type*} [SeminormedGroup E] (u v : E)
  proof: by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]

中文:
引理 norm_mul_sub_norm_div_le_two_mul
  条件: {E : 类型} [SeminormedGroup E] (u v : E)
  证明: by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]

Depends on / 依赖: add_assoc, tsub_le_iff_left, tsub_le_iff_right, two_mul
-/
lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ <= 2 * ‖v‖ := by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]
/--
lemma `norm_mul_sub_norm_div_le_two_mul_min` / 引理 `norm_mul_sub_norm_div_le_two_mul_min`

English:
lemma norm_mul_sub_norm_div_le_two_mul_min
  given: {E : Type*} [SeminormedCommGroup E] (u v : E)
  proof: by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev]; rw [mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

中文:
引理 norm_mul_sub_norm_div_le_two_mul_min
  条件: {E : 类型} [SeminormedCommGroup E] (u v : E)
  证明: by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev]; rw [mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

Depends on / 依赖: le_min, mul_comm, mul_min_of_nonneg, norm_div_rev, norm_mul_sub_norm_div_le_two_mul
-/
lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ <= 2 * min ‖u‖ ‖v‖ := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev]; rw [mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

-- Higher priority to fire before `mem_sphere`.
@[to_additive]
/--
theorem `mem_sphere_iff_norm_inv_mul_eq` / 定理 `mem_sphere_iff_norm_inv_mul_eq`

English:
theorem mem_sphere_iff_norm_inv_mul_eq
  statement: b in sphere a r ↔ ‖b⁻¹ * a‖ = r
  proof: by
  simp [dist_eq_norm_inv_mul]

@[to_additive] -- `simp` can prove this

中文:
定理 mem_sphere_iff_norm_inv_mul_eq
  结论: b in sphere a r ↔ ‖b⁻¹ * a‖ = r
  证明: by
  simp [dist_eq_norm_inv_mul]

@[to_additive] -- `simp` can prove this

Depends on / 依赖: dist_eq_norm_inv_mul
-/
theorem mem_sphere_iff_norm_inv_mul_eq : b in sphere a r ↔ ‖b⁻¹ * a‖ = r := by
  simp [dist_eq_norm_inv_mul]

@[to_additive] -- `simp` can prove this
/--
theorem `mem_sphere_one_iff_norm` / 定理 `mem_sphere_one_iff_norm`

English:
theorem mem_sphere_one_iff_norm
  statement: a in sphere (1 : E) r ↔ ‖a‖ = r
  proof: by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]

中文:
定理 mem_sphere_one_iff_norm
  结论: a in sphere (1 : E) r ↔ ‖a‖ = r
  证明: by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
-/
theorem mem_sphere_one_iff_norm : a in sphere (1 : E) r ↔ ‖a‖ = r := by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
/--
theorem `norm_eq_of_mem_sphere'` / 定理 `norm_eq_of_mem_sphere'`

English:
theorem norm_eq_of_mem_sphere'
  given: (x : sphere (1 : E) r)
  statement: ‖(x : E)‖ = r
  proof: mem_sphere_one_iff_norm.mp x.2

@[to_additive]

中文:
定理 norm_eq_of_mem_sphere'
  条件: (x : sphere (1 : E) r)
  结论: ‖(x : E)‖ = r
  证明: mem_sphere_one_iff_norm.mp x.2

@[to_additive]

Depends on / 依赖: mem_sphere_one_iff_norm, mem_sphere_one_iff_norm.mp
-/
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2

@[to_additive]
/--
theorem `ne_one_of_mem_sphere` / 定理 `ne_one_of_mem_sphere`

English:
theorem ne_one_of_mem_sphere
  given: (hr : r != 0) (x : sphere (1 : E) r)
  statement: (x : E) != 1
  proof: ne_one_of_norm_ne_zero by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]

中文:
定理 ne_one_of_mem_sphere
  条件: (hr : r != 0) (x : sphere (1 : E) r)
  结论: (x : E) != 1
  证明: ne_one_of_norm_ne_zero by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]

Depends on / 依赖: ne_one_of_norm_ne_zero, norm_eq_of_mem_sphere
-/
theorem ne_one_of_mem_sphere (hr : r != 0) (x : sphere (1 : E) r) : (x : E) != 1 :=
ne_one_of_norm_ne_zero by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]
/--
theorem `ne_one_of_mem_unit_sphere` / 定理 `ne_one_of_mem_unit_sphere`

English:
theorem ne_one_of_mem_unit_sphere
  given: (x : sphere (1 : E) 1)
  statement: (x : E) != 1
  proof: ne_one_of_mem_sphere one_ne_zero _

中文:
定理 ne_one_of_mem_unit_sphere
  条件: (x : sphere (1 : E) 1)
  结论: (x : E) != 1
  证明: ne_one_of_mem_sphere one_ne_zero _

Depends on / 依赖: ne_one_of_mem_sphere, one_ne_zero
-/
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) != 1 :=
  ne_one_of_mem_sphere one_ne_zero _

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive /-- The norm of a seminormed group as an additive group seminorm. -/]
/--
Definition of `normGroupSeminorm` / `normGroupSeminorm` 的定义

English:
definition normGroupSeminorm
  signature: : GroupSeminorm E
  body: ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]

中文:
定义 normGroupSeminorm
  签名: : GroupSeminorm E
  定义体: ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]

Depends on / 依赖: norm_inv, norm_mul_le, norm_one
-/
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]
/--
theorem `coe_normGroupSeminorm` / 定理 `coe_normGroupSeminorm`

English:
theorem coe_normGroupSeminorm
  statement: ⇑(normGroupSeminorm E) = norm
  proof: rfl

中文:
定理 coe_normGroupSeminorm
  结论: ⇑(normGroupSeminorm E) = norm
  证明: rfl
-/
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl

variable {E}

@[to_additive]
/--
theorem `NormedGroup.tendsto_nhds_one` / 定理 `NormedGroup.tendsto_nhds_one`

English:
theorem NormedGroup.tendsto_nhds_one
  given: {f : α -> E} {l : Filter α}
  proof: Metric.tendsto_nhds.trans by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]

中文:
定理 NormedGroup.tendsto_nhds_one
  条件: {f : α -> E} {l : Filter α}
  证明: Metric.tendsto_nhds.trans by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]

Depends on / 依赖: Metric, Metric.tendsto_nhds.trans, dist_one_right, tendsto_nhds
-/
theorem NormedGroup.tendsto_nhds_one {f : α -> E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ forall ε > 0, forallᶠ x in l, ‖f x‖ < ε :=
Metric.tendsto_nhds.trans by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]
/--
theorem `NormedGroup.tendsto_nhds_nhds` / 定理 `NormedGroup.tendsto_nhds_nhds`

English:
theorem NormedGroup.tendsto_nhds_nhds
  given: {f : E -> F} {x : E} {y : F}
  proof: by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 NormedGroup.tendsto_nhds_nhds
  条件: {f : E -> F} {x : E} {y : F}
  证明: by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: Metric, Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul, simp_rw, tendsto_nhds_nhds
-/
theorem NormedGroup.tendsto_nhds_nhds {f : E -> F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ forall ε > 0, exists δ > 0, forall x', ‖x'⁻¹ * x‖ < δ -> ‖(f x')⁻¹ * y‖ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `NormedGroup.nhds_basis_norm_lt` / 定理 `NormedGroup.nhds_basis_norm_lt`

English:
theorem NormedGroup.nhds_basis_norm_lt
  given: (x : E)
  proof: by
  simp_rw [← ball_eq_norm_inv_mul_lt]
  exact Metric.nhds_basis_ball

@[to_additive]

中文:
定理 NormedGroup.nhds_basis_norm_lt
  条件: (x : E)
  证明: by
  simp_rw [← ball_eq_norm_inv_mul_lt]
  exact Metric.nhds_basis_ball

@[to_additive]

Depends on / 依赖: Metric, Metric.nhds_basis_ball, ball_eq_norm_inv_mul_lt, nhds_basis_ball, simp_rw
-/
theorem NormedGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε } := by
  simp_rw [← ball_eq_norm_inv_mul_lt]
  exact Metric.nhds_basis_ball

@[to_additive]
/--
theorem `NormedGroup.nhds_one_basis_norm_lt` / 定理 `NormedGroup.nhds_one_basis_norm_lt`

English:
theorem NormedGroup.nhds_one_basis_norm_lt
  proof: by
  convert! NormedGroup.nhds_basis_norm_lt (1 : E) using 1
  simp

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.nhds_one_basis_norm_lt := NormedGroup.nhds_one_basis_norm_lt

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.nhds_zero_basis_norm_lt := NormedAddGroup.nhds

中文:
定理 NormedGroup.nhds_one_basis_norm_lt
  证明: by
  convert! NormedGroup.nhds_basis_norm_lt (1 : E) using 1
  simp

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.nhds_one_basis_norm_lt := NormedGroup.nhds_one_basis_norm_lt

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.nhds_zero_basis_norm_lt := NormedAddGroup.nhds

Depends on / 依赖: NormedGroup, NormedGroup.nhds_basis_norm_lt, convert, nhds_basis_norm_lt
-/
theorem NormedGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y‖ < ε } := by
  convert! NormedGroup.nhds_basis_norm_lt (1 : E) using 1
  simp

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.nhds_one_basis_norm_lt := NormedGroup.nhds_one_basis_norm_lt

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.nhds_zero_basis_norm_lt := NormedAddGroup.nhds_zero_basis_norm_lt

@[to_additive]
/--
theorem `NormedGroup.uniformity_basis_dist` / 定理 `NormedGroup.uniformity_basis_dist`

English:
theorem NormedGroup.uniformity_basis_dist
  proof: by
  convert Metric.uniformity_basis_dist (α := E)
  simp [dist_eq_norm_inv_mul]

中文:
定理 NormedGroup.uniformity_basis_dist
  证明: by
  convert Metric.uniformity_basis_dist (α := E)
  simp [dist_eq_norm_inv_mul]

Depends on / 依赖: Metric, Metric.uniformity_basis_dist, convert, dist_eq_norm_inv_mul, uniformity_basis_dist
-/
theorem NormedGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : Real => 0 < ε) fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ < ε } := by
  convert Metric.uniformity_basis_dist (α := E)
  simp [dist_eq_norm_inv_mul]

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
/--
theorem `coe_nnnorm'` / 定理 `coe_nnnorm'`

English:
theorem coe_nnnorm'
  given: (a : E)
  statement: (‖a‖₊ : Real) = ‖a‖
  proof: rfl

@[to_additive (attr := simp) coe_comp_nnnorm]

中文:
定理 coe_nnnorm'
  条件: (a : E)
  结论: (‖a‖₊ : 实数) = ‖a‖
  证明: rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
-/
theorem coe_nnnorm' (a : E) : (‖a‖₊ : Real) = ‖a‖ := rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
/--
theorem `coe_comp_nnnorm'` / 定理 `coe_comp_nnnorm'`

English:
theorem coe_comp_nnnorm'
  statement: (toReal : Real>=0 -> Real) ∘ (nnnorm : E -> Real>=0) = norm
  proof: rfl

@[to_additive (attr := simp) norm_toNNReal]

中文:
定理 coe_comp_nnnorm'
  结论: (to实数 : 实数>=0 -> 实数) ∘ (nnnorm : E -> 实数>=0) = norm
  证明: rfl

@[to_additive (attr := simp) norm_toNNReal]
-/
theorem coe_comp_nnnorm' : (toReal : Real>=0 -> Real) ∘ (nnnorm : E -> Real>=0) = norm :=
  rfl

@[to_additive (attr := simp) norm_toNNReal]
/--
theorem `norm_toNNReal'` / 定理 `norm_toNNReal'`

English:
theorem norm_toNNReal'
  statement: ‖a‖.toNNReal = ‖a‖₊
  proof: @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]

中文:
定理 norm_toNNReal'
  结论: ‖a‖.toNN实数 = ‖a‖₊
  证明: @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]

Depends on / 依赖: Real.toNNReal_coe, toNNReal_coe
-/
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]
/--
lemma `toReal_enorm'` / 引理 `toReal_enorm'`

English:
lemma toReal_enorm'
  given: (x : E)
  statement: ‖x‖ₑ.toReal = ‖x‖
  proof: by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]

中文:
引理 toReal_enorm'
  条件: (x : E)
  结论: ‖x‖ₑ.to实数 = ‖x‖
  证明: by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
-/
lemma toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖ := by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
/--
lemma `ofReal_norm'` / 引理 `ofReal_norm'`

English:
lemma ofReal_norm'
  given: (x : E)
  statement: .ofReal ‖x‖ = ‖x‖ₑ
  proof: ENNReal.ofReal_eq_coe_nnreal _

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm := ofReal_norm

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm' := ofReal_norm'

@[to_additive enorm_eq_iff_norm_eq]

中文:
引理 ofReal_norm'
  条件: (x : E)
  结论: .of实数 ‖x‖ = ‖x‖ₑ
  证明: ENNReal.ofReal_eq_coe_nnreal _

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm := ofReal_norm

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm' := ofReal_norm'

@[to_additive enorm_eq_iff_norm_eq]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_coe_nnreal, ofReal_eq_coe_nnreal
-/
lemma ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := ENNReal.ofReal_eq_coe_nnreal _

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm := ofReal_norm

@[deprecated (since := "2026-05-25")] alias ofReal_norm_eq_enorm' := ofReal_norm'

@[to_additive enorm_eq_iff_norm_eq]
/--
theorem `enorm'_eq_iff_norm_eq` / 定理 `enorm'_eq_iff_norm_eq`

English:
theorem enorm'_eq_iff_norm_eq
  given: {x : E} {y : F}
  statement: ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖
  proof: by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]

中文:
定理 enorm'_eq_iff_norm_eq
  条件: {x : E} {y : F}
  结论: ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖
  证明: by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]

Depends on / 依赖: ENNReal, ENNReal.coe_inj.mp, Real.toNNReal_eq_toNNReal_iff, coe_inj, norm_nonneg, ofReal_norm, toNNReal_eq_toNNReal_iff
-/
theorem enorm'_eq_iff_norm_eq {x : E} {y : F} : ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]
/--
theorem `enorm'_le_iff_norm_le` / 定理 `enorm'_le_iff_norm_le`

English:
theorem enorm'_le_iff_norm_le
  given: {x : E} {y : F}
  statement: ‖x‖ₑ <= ‖y‖ₑ ↔ ‖x‖ <= ‖y‖
  proof: by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]

中文:
定理 enorm'_le_iff_norm_le
  条件: {x : E} {y : F}
  结论: ‖x‖ₑ <= ‖y‖ₑ ↔ ‖x‖ <= ‖y‖
  证明: by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]
-/
theorem enorm'_le_iff_norm_le {x : E} {y : F} : ‖x‖ₑ <= ‖y‖ₑ ↔ ‖x‖ <= ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h => ?_, fun h => by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]
/--
theorem `nndist_eq_nnnorm_inv_mul` / 定理 `nndist_eq_nnnorm_inv_mul`

English:
theorem nndist_eq_nnnorm_inv_mul
  given: (a b : E)
  statement: nndist a b = ‖a⁻¹ * b‖₊
  proof: NNReal.eq dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]

中文:
定理 nndist_eq_nnnorm_inv_mul
  条件: (a b : E)
  结论: nndist a b = ‖a⁻¹ * b‖₊
  证明: NNReal.eq dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_norm_inv_mul
-/
theorem nndist_eq_nnnorm_inv_mul (a b : E) : nndist a b = ‖a⁻¹ * b‖₊ :=
NNReal.eq dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]
/--
theorem `nnnorm_inv'` / 定理 `nnnorm_inv'`

English:
theorem nnnorm_inv'
  given: (a : E)
  statement: ‖a⁻¹‖₊ = ‖a‖₊
  proof: NNReal.eq norm_inv' a

@[to_additive (attr := simp)]

中文:
定理 nnnorm_inv'
  条件: (a : E)
  结论: ‖a⁻¹‖₊ = ‖a‖₊
  证明: NNReal.eq norm_inv' a

@[to_additive (attr := simp)]

Depends on / 依赖: NNReal, NNReal.eq, norm_inv
-/
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
NNReal.eq norm_inv' a

@[to_additive (attr := simp)]
/--
theorem `nndist_one_right` / 定理 `nndist_one_right`

English:
theorem nndist_one_right
  given: (a : E)
  statement: nndist a 1 = ‖a‖₊
  proof: by
  simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]

中文:
定理 nndist_one_right
  条件: (a : E)
  结论: nndist a 1 = ‖a‖₊
  证明: by
  simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: nndist_eq_nnnorm_inv_mul
-/
theorem nndist_one_right (a : E) : nndist a 1 = ‖a‖₊ := by
  simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
/--
lemma `edist_one_right` / 引理 `edist_one_right`

English:
lemma edist_one_right
  given: (a : E)
  statement: edist a 1 = ‖a‖ₑ
  proof: by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]

中文:
引理 edist_one_right
  条件: (a : E)
  结论: edist a 1 = ‖a‖ₑ
  证明: by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]

Depends on / 依赖: edist_nndist, nndist_one_right
-/
lemma edist_one_right (a : E) : edist a 1 = ‖a‖ₑ := by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]
/--
theorem `nnnorm_one'` / 定理 `nnnorm_one'`

English:
theorem nnnorm_one'
  statement: ‖(1 : E)‖₊ = 0
  proof: NNReal.eq norm_one'

@[to_additive]

中文:
定理 nnnorm_one'
  结论: ‖(1 : E)‖₊ = 0
  证明: NNReal.eq norm_one'

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, norm_one
-/
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 := NNReal.eq norm_one'

@[to_additive]
/--
theorem `ne_one_of_nnnorm_ne_zero` / 定理 `ne_one_of_nnnorm_ne_zero`

English:
theorem ne_one_of_nnnorm_ne_zero
  given: {a : E}
  statement: ‖a‖₊ != 0 -> a != 1
  proof: mt by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]

中文:
定理 ne_one_of_nnnorm_ne_zero
  条件: {a : E}
  结论: ‖a‖₊ != 0 -> a != 1
  证明: mt by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]

Depends on / 依赖: nnnorm_one
-/
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ != 0 -> a != 1 :=
mt by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
/--
theorem `nnnorm_mul_le'` / 定理 `nnnorm_mul_le'`

English:
theorem nnnorm_mul_le'
  given: (a b : E)
  statement: ‖a * b‖₊ <= ‖a‖₊ + ‖b‖₊
  proof: NNReal.coe_le_coe.1 norm_mul_le' a b

@[to_additive norm_nsmul_le]

中文:
定理 nnnorm_mul_le'
  条件: (a b : E)
  结论: ‖a * b‖₊ <= ‖a‖₊ + ‖b‖₊
  证明: NNReal.coe_le_coe.1 norm_mul_le' a b

@[to_additive norm_nsmul_le]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, norm_mul_le
-/
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ <= ‖a‖₊ + ‖b‖₊ :=
NNReal.coe_le_coe.1 norm_mul_le' a b

@[to_additive norm_nsmul_le]
/--
lemma `norm_pow_le_mul_norm` / 引理 `norm_pow_le_mul_norm`

English:
lemma norm_pow_le_mul_norm
  statement: forall {n : Nat}, ‖a ^ n‖ <= n * ‖a‖

中文:
引理 norm_pow_le_mul_norm
  结论: 对任意 {n : 自然数}, ‖a ^ n‖ <= n * ‖a‖
-/
lemma norm_pow_le_mul_norm : forall {n : Nat}, ‖a ^ n‖ <= n * ‖a‖
  | 0 => by simp
  | n + 1 => by simpa [pow_succ, add_mul] using norm_mul_le_of_le' norm_pow_le_mul_norm le_rfl

@[to_additive nnnorm_nsmul_le]
/--
lemma `nnnorm_pow_le_mul_norm` / 引理 `nnnorm_pow_le_mul_norm`

English:
lemma nnnorm_pow_le_mul_norm
  given: {n : Nat}
  statement: ‖a ^ n‖₊ <= n * ‖a‖₊
  proof: by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using! norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_abs_zsmul]

中文:
引理 nnnorm_pow_le_mul_norm
  条件: {n : 自然数}
  结论: ‖a ^ n‖₊ <= n * ‖a‖₊
  证明: by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using! norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_abs_zsmul]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, coe_le_coe, coe_mul, coe_natCast, norm_pow_le_mul_norm
-/
lemma nnnorm_pow_le_mul_norm {n : Nat} : ‖a ^ n‖₊ <= n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using! norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_abs_zsmul]
/--
theorem `nnnorm_zpow_abs` / 定理 `nnnorm_zpow_abs`

English:
theorem nnnorm_zpow_abs
  given: (a : E) (n : Int)
  statement: ‖a ^ |n|‖₊ = ‖a ^ n‖₊
  proof: NNReal.eq norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]

中文:
定理 nnnorm_zpow_abs
  条件: (a : E) (n : 整数)
  结论: ‖a ^ |n|‖₊ = ‖a ^ n‖₊
  证明: NNReal.eq norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]

Depends on / 依赖: NNReal, NNReal.eq, norm_zpow_abs
-/
theorem nnnorm_zpow_abs (a : E) (n : Int) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊ :=
NNReal.eq norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]
/--
theorem `nnnorm_pow_natAbs` / 定理 `nnnorm_pow_natAbs`

English:
theorem nnnorm_pow_natAbs
  given: (a : E) (n : Int)
  statement: ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊
  proof: NNReal.eq norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]

中文:
定理 nnnorm_pow_natAbs
  条件: (a : E) (n : 整数)
  结论: ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊
  证明: NNReal.eq norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]

Depends on / 依赖: NNReal, NNReal.eq, norm_pow_natAbs
-/
theorem nnnorm_pow_natAbs (a : E) (n : Int) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊ :=
NNReal.eq norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]
/--
theorem `nnnorm_zpow_isUnit` / 定理 `nnnorm_zpow_isUnit`

English:
theorem nnnorm_zpow_isUnit
  given: (a : E) {n : Int} (hn : IsUnit n)
  statement: ‖a ^ n‖₊ = ‖a‖₊
  proof: NNReal.eq norm_zpow_isUnit a hn

@[simp]

中文:
定理 nnnorm_zpow_isUnit
  条件: (a : E) {n : 整数} (hn : IsUnit n)
  结论: ‖a ^ n‖₊ = ‖a‖₊
  证明: NNReal.eq norm_zpow_isUnit a hn

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, norm_zpow_isUnit
-/
theorem nnnorm_zpow_isUnit (a : E) {n : Int} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊ :=
NNReal.eq norm_zpow_isUnit a hn

@[simp]
/--
theorem `nnnorm_units_zsmul` / 定理 `nnnorm_units_zsmul`

English:
theorem nnnorm_units_zsmul
  given: {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E)
  statement: ‖n • a‖₊ = ‖a‖₊
  proof: NNReal.eq norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]

中文:
定理 nnnorm_units_zsmul
  条件: {E : 类型} [SeminormedAddGroup E] (n : 整数ˣ) (a : E)
  结论: ‖n • a‖₊ = ‖a‖₊
  证明: NNReal.eq norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]

Depends on / 依赖: NNReal, NNReal.eq, isUnit, n.isUnit, norm_isUnit_zsmul
-/
theorem nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : Intˣ) (a : E) : ‖n • a‖₊ = ‖a‖₊ :=
NNReal.eq norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]
/--
theorem `nndist_one_left` / 定理 `nndist_one_left`

English:
theorem nndist_one_left
  given: (a : E)
  statement: nndist 1 a = ‖a‖₊
  proof: by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]

中文:
定理 nndist_one_left
  条件: (a : E)
  结论: nndist 1 a = ‖a‖₊
  证明: by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: nndist_eq_nnnorm_inv_mul
-/
theorem nndist_one_left (a : E) : nndist 1 a = ‖a‖₊ := by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
/--
theorem `edist_one_left` / 定理 `edist_one_left`

English:
theorem edist_one_left
  given: (a : E)
  statement: edist 1 a = ‖a‖₊
  proof: by
  rw [edist_nndist]; rw [nndist_one_left]

中文:
定理 edist_one_left
  条件: (a : E)
  结论: edist 1 a = ‖a‖₊
  证明: by
  rw [edist_nndist]; rw [nndist_one_left]

Depends on / 依赖: edist_nndist, nndist_one_left
-/
theorem edist_one_left (a : E) : edist 1 a = ‖a‖₊ := by
  rw [edist_nndist]; rw [nndist_one_left]

open scoped symmDiff in
@[to_additive]
/--
theorem `nndist_mulIndicator` / 定理 `nndist_mulIndicator`

English:
theorem nndist_mulIndicator
  given: (s t : Set α) (f : α -> E) (x : α)
  proof: NNReal.eq dist_mulIndicator s t f x

@[to_additive]

中文:
定理 nndist_mulIndicator
  条件: (s t : Set α) (f : α -> E) (x : α)
  证明: NNReal.eq dist_mulIndicator s t f x

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, dist_mulIndicator
-/
theorem nndist_mulIndicator (s t : Set α) (f : α -> E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
NNReal.eq dist_mulIndicator s t f x

@[to_additive]
/--
theorem `nnnorm_div_le` / 定理 `nnnorm_div_le`

English:
theorem nnnorm_div_le
  given: (a b : E)
  statement: ‖a / b‖₊ <= ‖a‖₊ + ‖b‖₊
  proof: NNReal.coe_le_coe.1 norm_div_le _ _

@[to_additive]

中文:
定理 nnnorm_div_le
  条件: (a b : E)
  结论: ‖a / b‖₊ <= ‖a‖₊ + ‖b‖₊
  证明: NNReal.coe_le_coe.1 norm_div_le _ _

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, norm_div_le
-/
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ <= ‖a‖₊ + ‖b‖₊ :=
NNReal.coe_le_coe.1 norm_div_le _ _

@[to_additive]
/--
lemma `enorm_div_le` / 引理 `enorm_div_le`

English:
lemma enorm_div_le
  statement: ‖a / b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
  proof: by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive]

中文:
引理 enorm_div_le
  结论: ‖a / b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
  证明: by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.coe_add, coe_add, nnnorm_div_le
-/
lemma enorm_div_le : ‖a / b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ := by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive]
/--
theorem `nndist_nnnorm_nnnorm_le_nnnorm_inv_mul` / 定理 `nndist_nnnorm_nnnorm_le_nnnorm_inv_mul`

English:
theorem nndist_nnnorm_nnnorm_le_nnnorm_inv_mul
  given: (a b : E)
  statement: nndist ‖a‖₊ ‖b‖₊ <= ‖a⁻¹ * b‖₊
  proof: NNReal.coe_le_coe.1 dist_norm_norm_le_norm_inv_mul a b

@[to_additive]

中文:
定理 nndist_nnnorm_nnnorm_le_nnnorm_inv_mul
  条件: (a b : E)
  结论: nndist ‖a‖₊ ‖b‖₊ <= ‖a⁻¹ * b‖₊
  证明: NNReal.coe_le_coe.1 dist_norm_norm_le_norm_inv_mul a b

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, dist_norm_norm_le_norm_inv_mul
-/
theorem nndist_nnnorm_nnnorm_le_nnnorm_inv_mul (a b : E) : nndist ‖a‖₊ ‖b‖₊ <= ‖a⁻¹ * b‖₊ :=
NNReal.coe_le_coe.1 dist_norm_norm_le_norm_inv_mul a b

@[to_additive]
/--
theorem `nnnorm_le_nnnorm_add_nnnorm_div` / 定理 `nnnorm_le_nnnorm_add_nnnorm_div`

English:
theorem nnnorm_le_nnnorm_add_nnnorm_div
  given: (a b : E)
  statement: ‖b‖₊ <= ‖a‖₊ + ‖a / b‖₊
  proof: norm_le_norm_add_norm_div _ _

@[to_additive]

中文:
定理 nnnorm_le_nnnorm_add_nnnorm_div
  条件: (a b : E)
  结论: ‖b‖₊ <= ‖a‖₊ + ‖a / b‖₊
  证明: norm_le_norm_add_norm_div _ _

@[to_additive]

Depends on / 依赖: norm_le_norm_add_norm_div
-/
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ <= ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _

@[to_additive]
/--
theorem `nnnorm_le_nnnorm_add_nnnorm_div'` / 定理 `nnnorm_le_nnnorm_add_nnnorm_div'`

English:
theorem nnnorm_le_nnnorm_add_nnnorm_div'
  given: (a b : E)
  statement: ‖a‖₊ <= ‖b‖₊ + ‖a / b‖₊
  proof: norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]

中文:
定理 nnnorm_le_nnnorm_add_nnnorm_div'
  条件: (a b : E)
  结论: ‖a‖₊ <= ‖b‖₊ + ‖a / b‖₊
  证明: norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]

Depends on / 依赖: norm_le_norm_add_norm_div
-/
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ <= ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
/--
theorem `nnnorm_le_mul_nnnorm_add` / 定理 `nnnorm_le_mul_nnnorm_add`

English:
theorem nnnorm_le_mul_nnnorm_add
  given: (a b : E)
  statement: ‖a‖₊ <= ‖a * b‖₊ + ‖b‖₊
  proof: norm_le_mul_norm_add _ _

中文:
定理 nnnorm_le_mul_nnnorm_add
  条件: (a b : E)
  结论: ‖a‖₊ <= ‖a * b‖₊ + ‖b‖₊
  证明: norm_le_mul_norm_add _ _

Depends on / 依赖: norm_le_mul_norm_add
-/
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ <= ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _

/-- An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `nnnorm_le_add_nnnorm_add` for the addition from the left. -/]
/--
theorem `nnnorm_le_mul_nnnorm_add'` / 定理 `nnnorm_le_mul_nnnorm_add'`

English:
theorem nnnorm_le_mul_nnnorm_add'
  given: (a b : E)
  statement: ‖b‖₊ <= ‖a * b‖₊ + ‖a‖₊
  proof: norm_le_mul_norm_add' _ _

@[to_additive]

中文:
定理 nnnorm_le_mul_nnnorm_add'
  条件: (a b : E)
  结论: ‖b‖₊ <= ‖a * b‖₊ + ‖a‖₊
  证明: norm_le_mul_norm_add' _ _

@[to_additive]

Depends on / 依赖: norm_le_mul_norm_add
-/
theorem nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ <= ‖a * b‖₊ + ‖a‖₊ :=
  norm_le_mul_norm_add' _ _

@[to_additive]
/--
lemma `nnnorm_mul_eq_nnnorm_right` / 引理 `nnnorm_mul_eq_nnnorm_right`

English:
lemma nnnorm_mul_eq_nnnorm_right
  given: {x : E} (y : E) (h : ‖x‖₊ = 0)
  statement: ‖x * y‖₊ = ‖y‖₊
  proof: NNReal.eq norm_mul_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]

中文:
引理 nnnorm_mul_eq_nnnorm_right
  条件: {x : E} (y : E) (h : ‖x‖₊ = 0)
  结论: ‖x * y‖₊ = ‖y‖₊
  证明: NNReal.eq norm_mul_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, NNReal.toReal, congr_arg, norm_mul_eq_norm_right, toReal
-/
lemma nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖₊ :=
NNReal.eq norm_mul_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]
/--
lemma `nnnorm_mul_eq_nnnorm_left` / 引理 `nnnorm_mul_eq_nnnorm_left`

English:
lemma nnnorm_mul_eq_nnnorm_left
  given: (x : E) {y : E} (h : ‖y‖₊ = 0)
  statement: ‖x * y‖₊ = ‖x‖₊
  proof: NNReal.eq norm_mul_eq_norm_left _ congr_arg NNReal.toReal h

@[to_additive]

中文:
引理 nnnorm_mul_eq_nnnorm_left
  条件: (x : E) {y : E} (h : ‖y‖₊ = 0)
  结论: ‖x * y‖₊ = ‖x‖₊
  证明: NNReal.eq norm_mul_eq_norm_left _ congr_arg NNReal.toReal h

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, NNReal.toReal, congr_arg, norm_mul_eq_norm_left, toReal
-/
lemma nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊ :=
NNReal.eq norm_mul_eq_norm_left _ congr_arg NNReal.toReal h

@[to_additive]
/--
lemma `nnnorm_div_eq_nnnorm_right` / 引理 `nnnorm_div_eq_nnnorm_right`

English:
lemma nnnorm_div_eq_nnnorm_right
  given: {x : E} (y : E) (h : ‖x‖₊ = 0)
  statement: ‖x / y‖₊ = ‖y‖₊
  proof: NNReal.eq norm_div_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]

中文:
引理 nnnorm_div_eq_nnnorm_right
  条件: {x : E} (y : E) (h : ‖x‖₊ = 0)
  结论: ‖x / y‖₊ = ‖y‖₊
  证明: NNReal.eq norm_div_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, NNReal.toReal, congr_arg, norm_div_eq_norm_right, toReal
-/
lemma nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖₊ :=
NNReal.eq norm_div_eq_norm_right _ congr_arg NNReal.toReal h

@[to_additive]
/--
lemma `nnnorm_div_eq_nnnorm_left` / 引理 `nnnorm_div_eq_nnnorm_left`

English:
lemma nnnorm_div_eq_nnnorm_left
  given: (x : E) {y : E} (h : ‖y‖₊ = 0)
  statement: ‖x / y‖₊ = ‖x‖₊
  proof: NNReal.eq norm_div_eq_norm_left _ congr_arg NNReal.toReal h

中文:
引理 nnnorm_div_eq_nnnorm_left
  条件: (x : E) {y : E} (h : ‖y‖₊ = 0)
  结论: ‖x / y‖₊ = ‖x‖₊
  证明: NNReal.eq norm_div_eq_norm_left _ congr_arg NNReal.toReal h

Depends on / 依赖: NNReal, NNReal.eq, NNReal.toReal, congr_arg, norm_div_eq_norm_left, toReal
-/
lemma nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊ :=
NNReal.eq norm_div_eq_norm_left _ congr_arg NNReal.toReal h

/-- The nonnegative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm /-- The nonnegative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm. -/]
/--
theorem `toReal_coe_nnnorm'` / 定理 `toReal_coe_nnnorm'`

English:
theorem toReal_coe_nnnorm'
  given: (a : E)
  statement: (‖a‖₊ : Real>=0∞).toReal = ‖a‖
  proof: rfl

中文:
定理 toReal_coe_nnnorm'
  条件: (a : E)
  结论: (‖a‖₊ : 实数>=0∞).to实数 = ‖a‖
  证明: rfl
-/
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : Real>=0∞).toReal = ‖a‖ := rfl

open scoped symmDiff in
@[to_additive]
/--
theorem `edist_mulIndicator` / 定理 `edist_mulIndicator`

English:
theorem edist_mulIndicator
  given: (s t : Set α) (f : α -> E) (x : α)
  proof: by
  rw [edist_nndist]; rw [nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]

中文:
定理 edist_mulIndicator
  条件: (s t : Set α) (f : α -> E) (x : α)
  证明: by
  rw [edist_nndist]; rw [nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]

Depends on / 依赖: edist_nndist, nndist_mulIndicator
-/
theorem edist_mulIndicator (s t : Set α) (f : α -> E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist]; rw [nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]
/--
theorem `nontrivialTopology_iff_exists_nnnorm_ne_zero'` / 定理 `nontrivialTopology_iff_exists_nnnorm_ne_zero'`

English:
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero'
  proof: by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_inv_mul]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]

中文:
定理 nontrivialTopology_iff_exists_nnnorm_ne_zero'
  证明: by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_inv_mul]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]

Depends on / 依赖: Metric, Metric.inseparable_iff_nndist, TopologicalSpace, TopologicalSpace.nontrivial_iff_exists_not_inseparable, inseparable_iff_nndist, nndist_eq_nnnorm_inv_mul, nontrivial_iff_exists_not_inseparable, simp_rw
-/
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ exists x : E, ‖x‖₊ != 0 := by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_inv_mul]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]
/--
theorem `indiscreteTopology_iff_forall_nnnorm_eq_zero'` / 定理 `indiscreteTopology_iff_forall_nnnorm_eq_zero'`

English:
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero'
  proof: by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

中文:
定理 indiscreteTopology_iff_forall_nnnorm_eq_zero'
  证明: by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

Depends on / 依赖: nontrivialTopology_iff_exists_nnnorm_ne_zero
-/
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ forall x : E, ‖x‖₊ = 0 := by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_nnnorm_ne_zero]
/--
theorem `exists_nnnorm_ne_zero'` / 定理 `exists_nnnorm_ne_zero'`

English:
theorem exists_nnnorm_ne_zero'
  given: [NontrivialTopology E]
  statement: exists x : E, ‖x‖₊ != 0
  proof: nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]

中文:
定理 exists_nnnorm_ne_zero'
  条件: [NontrivialTopology E]
  结论: 存在 x : E, ‖x‖₊ != 0
  证明: nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]

Depends on / 依赖: nontrivialTopology_iff_exists_nnnorm_ne_zero
-/
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : exists x : E, ‖x‖₊ != 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
/--
theorem `IndiscreteTopology.nnnorm_eq_zero'` / 定理 `IndiscreteTopology.nnnorm_eq_zero'`

English:
theorem IndiscreteTopology.nnnorm_eq_zero'
  given: [IndiscreteTopology E]
  statement: forall x : E, ‖x‖₊ = 0
  proof: indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero

中文:
定理 IndiscreteTopology.nnnorm_eq_zero'
  条件: [IndiscreteTopology E]
  结论: 对任意 x : E, ‖x‖₊ = 0
  证明: indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero

Depends on / 依赖: indiscreteTopology_iff_forall_nnnorm_eq_zero
-/
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : forall x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
/--
theorem `nontrivialTopology_iff_exists_norm_ne_zero'` / 定理 `nontrivialTopology_iff_exists_norm_ne_zero'`

English:
theorem nontrivialTopology_iff_exists_norm_ne_zero'
  proof: by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]

中文:
定理 nontrivialTopology_iff_exists_norm_ne_zero'
  证明: by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]

Depends on / 依赖: NNReal, NNReal.ne_iff, ne_iff, nontrivialTopology_iff_exists_nnnorm_ne_zero
-/
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ exists x : E, ‖x‖ != 0 := by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]
/--
theorem `indiscreteTopology_iff_forall_norm_eq_zero'` / 定理 `indiscreteTopology_iff_forall_norm_eq_zero'`

English:
theorem indiscreteTopology_iff_forall_norm_eq_zero'
  proof: by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

中文:
定理 indiscreteTopology_iff_forall_norm_eq_zero'
  证明: by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

Depends on / 依赖: nontrivialTopology_iff_exists_norm_ne_zero
-/
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ forall x : E, ‖x‖ = 0 := by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_norm_ne_zero]
/--
theorem `exists_norm_ne_zero'` / 定理 `exists_norm_ne_zero'`

English:
theorem exists_norm_ne_zero'
  given: [NontrivialTopology E]
  statement: exists x : E, ‖x‖ != 0
  proof: nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]

中文:
定理 exists_norm_ne_zero'
  条件: [NontrivialTopology E]
  结论: 存在 x : E, ‖x‖ != 0
  证明: nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]

Depends on / 依赖: nontrivialTopology_iff_exists_norm_ne_zero
-/
theorem exists_norm_ne_zero' [NontrivialTopology E] : exists x : E, ‖x‖ != 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
/--
theorem `IndiscreteTopology.norm_eq_zero'` / 定理 `IndiscreteTopology.norm_eq_zero'`

English:
theorem IndiscreteTopology.norm_eq_zero'
  given: [IndiscreteTopology E]
  statement: forall x : E, ‖x‖ = 0
  proof: indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero

中文:
定理 IndiscreteTopology.norm_eq_zero'
  条件: [IndiscreteTopology E]
  结论: 对任意 x : E, ‖x‖ = 0
  证明: indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero

Depends on / 依赖: indiscreteTopology_iff_forall_norm_eq_zero
-/
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : forall x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

section ENorm

@[to_additive (attr := simp) enorm_zero]
/--
lemma `enorm_one'` / 引理 `enorm_one'`

English:
lemma enorm_one'
  given: {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]
  statement: ‖(1 : E)‖ₑ = 0
  proof: by
  rw [ESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]

中文:
引理 enorm_one'
  条件: {E : 类型} [TopologicalSpace E] [ESeminormedMonoid E]
  结论: ‖(1 : E)‖ₑ = 0
  证明: by
  rw [ESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]

Depends on / 依赖: ESeminormedMonoid, ESeminormedMonoid.enorm_zero, enorm_zero
-/
lemma enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : E)‖ₑ = 0 := by
  rw [ESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]
/--
lemma `exists_enorm_lt'` / 引理 `exists_enorm_lt'`

English:
lemma exists_enorm_lt'
  statement: (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
  proof: .and_eventually frequently_iff_neBot.mpr hbot
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
.exists

@[to_additive (attr := simp) enorm_neg]

中文:
引理 exists_enorm_lt'
  结论: (E : 类型) [TopologicalSpace E] [ESeminormedMonoid E]
  证明: .and_eventually frequently_iff_neBot.mpr hbot
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
.exists

@[to_additive (attr := simp) enorm_neg]

Depends on / 依赖: ContinuousENorm, ContinuousENorm.continuous_enorm.tendsto, and_eventually, bot_lt, continuous_enorm, eventually_lt_const, frequently_iff_neBot, frequently_iff_neBot.mpr, hc.bot_lt, tendsto
-/
lemma exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
    [hbot : NeBot (𝓝[!=] (1 : E))] {c : Real>=0∞} (hc : c != 0) : exists x != (1 : E), ‖x‖ₑ < c :=
.and_eventually frequently_iff_neBot.mpr hbot
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
.exists

@[to_additive (attr := simp) enorm_neg]
/--
lemma `enorm_inv'` / 引理 `enorm_inv'`

English:
lemma enorm_inv'
  given: (a : E)
  statement: ‖a⁻¹‖ₑ = ‖a‖ₑ
  proof: by simp [enorm]

@[to_additive]

中文:
引理 enorm_inv'
  条件: (a : E)
  结论: ‖a⁻¹‖ₑ = ‖a‖ₑ
  证明: by simp [enorm]

@[to_additive]
-/
lemma enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ := by simp [enorm]

@[to_additive]
/--
theorem `edist_eq_enorm_inv_mul` / 定理 `edist_eq_enorm_inv_mul`

English:
theorem edist_eq_enorm_inv_mul
  given: (a b : E)
  statement: edist a b = ‖a⁻¹ * b‖ₑ
  proof: by
  rw [edist_dist]; rw [dist_eq_norm_inv_mul]; rw [ofReal_norm']

@[deprecated (since := "2026-02-11")] alias edist_one_eq_enorm := edist_one_right

@[deprecated (since := "2026-02-11")] alias edist_zero_eq_enorm := edist_zero_right

@[to_additive]

中文:
定理 edist_eq_enorm_inv_mul
  条件: (a b : E)
  结论: edist a b = ‖a⁻¹ * b‖ₑ
  证明: by
  rw [edist_dist]; rw [dist_eq_norm_inv_mul]; rw [ofReal_norm']

@[deprecated (since := "2026-02-11")] alias edist_one_eq_enorm := edist_one_right

@[deprecated (since := "2026-02-11")] alias edist_zero_eq_enorm := edist_zero_right

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, edist_dist, ofReal_norm
-/
theorem edist_eq_enorm_inv_mul (a b : E) : edist a b = ‖a⁻¹ * b‖ₑ := by
  rw [edist_dist]; rw [dist_eq_norm_inv_mul]; rw [ofReal_norm']

@[deprecated (since := "2026-02-11")] alias edist_one_eq_enorm := edist_one_right

@[deprecated (since := "2026-02-11")] alias edist_zero_eq_enorm := edist_zero_right

@[to_additive]
/--
lemma `enorm_div_rev` / 引理 `enorm_div_rev`

English:
lemma enorm_div_rev
  given: {E : Type*} [SeminormedGroup E] (a b : E)
  statement: ‖a / b‖ₑ = ‖b / a‖ₑ
  proof: by
  rw [← enorm_inv']; rw [inv_div]

@[to_additive]

中文:
引理 enorm_div_rev
  条件: {E : 类型} [SeminormedGroup E] (a b : E)
  结论: ‖a / b‖ₑ = ‖b / a‖ₑ
  证明: by
  rw [← enorm_inv']; rw [inv_div]

@[to_additive]

Depends on / 依赖: enorm_inv, inv_div
-/
lemma enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / a‖ₑ := by
  rw [← enorm_inv']; rw [inv_div]

@[to_additive]
/--
theorem `mem_eball_one_iff` / 定理 `mem_eball_one_iff`

English:
theorem mem_eball_one_iff
  given: {r : Real>=0∞}
  statement: a in eball 1 r ↔ ‖a‖ₑ < r
  proof: by
  rw [Metric.mem_eball]; rw [edist_one_right]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

中文:
定理 mem_eball_one_iff
  条件: {r : 实数>=0∞}
  结论: a in eball 1 r ↔ ‖a‖ₑ < r
  证明: by
  rw [Metric.mem_eball]; rw [edist_one_right]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

Depends on / 依赖: Metric, Metric.mem_eball, edist_one_right, mem_eball
-/
theorem mem_eball_one_iff {r : Real>=0∞} : a in eball 1 r ↔ ‖a‖ₑ < r := by
  rw [Metric.mem_eball]; rw [edist_one_right]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

end ENorm

section ESeminormedMonoid

variable {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]

@[to_additive enorm_add_le]
/--
lemma `enorm_mul_le'` / 引理 `enorm_mul_le'`

English:
lemma enorm_mul_le'
  given: (a b : E)
  statement: ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
  proof: ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]

中文:
引理 enorm_mul_le'
  条件: (a b : E)
  结论: ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ
  证明: ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]

Depends on / 依赖: ESeminormedMonoid, ESeminormedMonoid.enorm_mul_le, enorm_mul_le
-/
lemma enorm_mul_le' (a b : E) : ‖a * b‖ₑ <= ‖a‖ₑ + ‖b‖ₑ := ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]
/--
theorem `enorm_mul_le_of_le'` / 定理 `enorm_mul_le_of_le'`

English:
theorem enorm_mul_le_of_le'
  statement: {r₁ r₂ : Real>=0∞} {a₁ a₂ : E}
  proof: (enorm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

@[to_additive enorm_add₃_le]

中文:
定理 enorm_mul_le_of_le'
  结论: {r₁ r₂ : 实数>=0∞} {a₁ a₂ : E}
  证明: (enorm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

@[to_additive enorm_add₃_le]

Depends on / 依赖: add_le_add, enorm_mul_le
-/
theorem enorm_mul_le_of_le' {r₁ r₂ : Real>=0∞} {a₁ a₂ : E}
    (h₁ : ‖a₁‖ₑ <= r₁) (h₂ : ‖a₂‖ₑ <= r₂) : ‖a₁ * a₂‖ₑ <= r₁ + r₂ :=
(enorm_mul_le' a₁ a₂).trans add_le_add h₁ h₂

@[to_additive enorm_add₃_le]
/--
lemma `enorm_mul₃_le'` / 引理 `enorm_mul₃_le'`

English:
lemma enorm_mul₃_le'
  given: {a b c : E}
  statement: ‖a * b * c‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ
  proof: enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]

中文:
引理 enorm_mul₃_le'
  条件: {a b c : E}
  结论: ‖a * b * c‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ
  证明: enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]

Depends on / 依赖: enorm_mul_le, enorm_mul_le_of_le, le_rfl
-/
lemma enorm_mul₃_le' {a b c : E} : ‖a * b * c‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ :=
  enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]
/--
lemma `enorm_mul₄_le'` / 引理 `enorm_mul₄_le'`

English:
lemma enorm_mul₄_le'
  given: {a b c d : E}
  statement: ‖a * b * c * d‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ
  proof: enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

中文:
引理 enorm_mul₄_le'
  条件: {a b c d : E}
  结论: ‖a * b * c * d‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ
  证明: enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

Depends on / 依赖: enorm_mul_le_of_le, le_rfl
-/
lemma enorm_mul₄_le' {a b c d : E} : ‖a * b * c * d‖ₑ <= ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

end ESeminormedMonoid

section ENormedMonoid

variable {E : Type*} [TopologicalSpace E] [ENormedMonoid E]

@[to_additive (attr := simp) enorm_eq_zero]
/--
lemma `enorm_eq_zero'` / 引理 `enorm_eq_zero'`

English:
lemma enorm_eq_zero'
  given: {a : E}
  statement: ‖a‖ₑ = 0 ↔ a = 1
  proof: by
  simp [ENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]

中文:
引理 enorm_eq_zero'
  条件: {a : E}
  结论: ‖a‖ₑ = 0 ↔ a = 1
  证明: by
  simp [ENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]

Depends on / 依赖: ENormedMonoid, ENormedMonoid.enorm_eq_zero, enorm_eq_zero
-/
lemma enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1 := by
  simp [ENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]
/--
lemma `enorm_ne_zero'` / 引理 `enorm_ne_zero'`

English:
lemma enorm_ne_zero'
  given: {a : E}
  statement: ‖a‖ₑ != 0 ↔ a != 1
  proof: enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]

中文:
引理 enorm_ne_zero'
  条件: {a : E}
  结论: ‖a‖ₑ != 0 ↔ a != 1
  证明: enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]

Depends on / 依赖: enorm_eq_zero
-/
lemma enorm_ne_zero' {a : E} : ‖a‖ₑ != 0 ↔ a != 1 :=
  enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]
/--
lemma `enorm_pos'` / 引理 `enorm_pos'`

English:
lemma enorm_pos'
  given: {a : E}
  statement: 0 < ‖a‖ₑ ↔ a != 1
  proof: pos_iff_ne_zero.trans enorm_ne_zero'

中文:
引理 enorm_pos'
  条件: {a : E}
  结论: 0 < ‖a‖ₑ ↔ a != 1
  证明: pos_iff_ne_zero.trans enorm_ne_zero'

Depends on / 依赖: enorm_ne_zero, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
lemma enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a != 1 :=
  pos_iff_ne_zero.trans enorm_ne_zero'

end ENormedMonoid

open Set in
@[to_additive]
/--
lemma `SeminormedGroup.disjoint_nhds` / 引理 `SeminormedGroup.disjoint_nhds`

English:
lemma SeminormedGroup.disjoint_nhds
  given: (x : E) (f : Filter E)
  proof: by
  simp [NormedGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_ofPred, eventually_iff]

@[to_additive]

中文:
引理 SeminormedGroup.disjoint_nhds
  条件: (x : E) (f : Filter E)
  证明: by
  simp [NormedGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_ofPred, eventually_iff]

@[to_additive]

Depends on / 依赖: NormedGroup, NormedGroup.nhds_basis_norm_lt, compl_ofPred, disjoint_iff_left, eventually_iff, nhds_basis_norm_lt
-/
lemma SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) :
    Disjoint (𝓝 x) f ↔ exists δ > 0, forallᶠ y in f, δ <= ‖y⁻¹ * x‖ := by
  simp [NormedGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_ofPred, eventually_iff]

@[to_additive]
/--
lemma `SeminormedGroup.disjoint_nhds_one` / 引理 `SeminormedGroup.disjoint_nhds_one`

English:
lemma SeminormedGroup.disjoint_nhds_one
  given: (f : Filter E)
  proof: by
  simpa using disjoint_nhds 1 f

中文:
引理 SeminormedGroup.disjoint_nhds_one
  条件: (f : Filter E)
  证明: by
  simpa using disjoint_nhds 1 f

Depends on / 依赖: disjoint_nhds
-/
lemma SeminormedGroup.disjoint_nhds_one (f : Filter E) :
    Disjoint (𝓝 1) f ↔ exists δ > 0, forallᶠ y in f, δ <= ‖y‖ := by
  simpa using disjoint_nhds 1 f

end SeminormedGroup

section Induced

variable (E F)
variable [FunLike 𝓕 E F]

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain. -/]
/--
Definition of `SeminormedGroup.induced` / `SeminormedGroup.induced` 的定义

English:
abbreviation SeminormedGroup.induced
  signature: [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
  body: fast_instance% { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

中文:
缩写 SeminormedGroup.induced
  签名: [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
  定义体: fast_instance% { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.induced, dist_eq, dist_eq_norm_inv_mul, fast_instance, induced, map_inv, map_mul, toPseudoMetricSpace
-/
abbrev SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  fast_instance% { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain. -/]
/--
Definition of `SeminormedCommGroup.induced` / `SeminormedCommGroup.induced` 的定义

English:
abbreviation SeminormedCommGroup.induced
  body: fast_instance% { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

中文:
缩写 SeminormedCommGroup.induced
  定义体: fast_instance% { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

Depends on / 依赖: SeminormedGroup, SeminormedGroup.induced, fast_instance, induced, mul_comm
-/
abbrev SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  fast_instance% { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
structure on the domain. -/
@[to_additive /-- An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain. -/]
/--
Definition of `NormedGroup.induced` / `NormedGroup.induced` 的定义

English:
abbreviation NormedGroup.induced
  body: fast_instance% { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

中文:
缩写 NormedGroup.induced
  定义体: fast_instance% { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

Depends on / 依赖: MetricSpace, MetricSpace.induced, SeminormedGroup, SeminormedGroup.induced, fast_instance, induced
-/
abbrev NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  fast_instance% { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive /-- An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain. -/]
/--
Definition of `NormedCommGroup.induced` / `NormedCommGroup.induced` 的定义

English:
abbreviation NormedCommGroup.induced
  signature: [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
  body: fast_instance% { SeminormedCommGroup.induced E F f, MetricSpace.induced f h _ with }

中文:
缩写 NormedCommGroup.induced
  签名: [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
  定义体: fast_instance% { SeminormedCommGroup.induced E F f, MetricSpace.induced f h _ with }

Depends on / 依赖: MetricSpace, MetricSpace.induced, SeminormedCommGroup, SeminormedCommGroup.induced, fast_instance, induced
-/
abbrev NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  fast_instance% { SeminormedCommGroup.induced E F f, MetricSpace.induced f h _ with }

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : Real}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive]
/--
theorem `dist_eq_norm_div` / 定理 `dist_eq_norm_div`

English:
theorem dist_eq_norm_div
  given: (a b : E)
  statement: dist a b = ‖a / b‖
  proof: by
  rw [dist_eq_norm_inv_mul']; rw [div_eq_inv_mul]

@[to_additive]

中文:
定理 dist_eq_norm_div
  条件: (a b : E)
  结论: dist a b = ‖a / b‖
  证明: by
  rw [dist_eq_norm_inv_mul']; rw [div_eq_inv_mul]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, div_eq_inv_mul
-/
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ := by
  rw [dist_eq_norm_inv_mul']; rw [div_eq_inv_mul]

@[to_additive]
/--
theorem `dist_eq_norm_div'` / 定理 `dist_eq_norm_div'`

English:
theorem dist_eq_norm_div'
  given: (a b : E)
  statement: dist a b = ‖b / a‖
  proof: by
  rw [dist_eq_norm_inv_mul]; rw [div_eq_inv_mul]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]

中文:
定理 dist_eq_norm_div'
  条件: (a b : E)
  结论: dist a b = ‖b / a‖
  证明: by
  rw [dist_eq_norm_inv_mul]; rw [div_eq_inv_mul]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, div_eq_inv_mul
-/
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by
  rw [dist_eq_norm_inv_mul]; rw [div_eq_inv_mul]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]
/--
theorem `norm_inv_mul` / 定理 `norm_inv_mul`

English:
theorem norm_inv_mul
  given: (a b : E)
  statement: ‖a⁻¹ * b‖ = ‖a / b‖
  proof: by
  rw [← dist_eq_norm_inv_mul]; rw [dist_eq_norm_div]

@[to_additive abs_norm_sub_norm_le]

中文:
定理 norm_inv_mul
  条件: (a b : E)
  结论: ‖a⁻¹ * b‖ = ‖a / b‖
  证明: by
  rw [← dist_eq_norm_inv_mul]; rw [dist_eq_norm_div]

@[to_additive abs_norm_sub_norm_le]

Depends on / 依赖: dist_eq_norm_div, dist_eq_norm_inv_mul
-/
theorem norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖ := by
  rw [← dist_eq_norm_inv_mul]; rw [dist_eq_norm_div]

@[to_additive abs_norm_sub_norm_le]
/--
theorem `abs_norm_sub_norm_le'` / 定理 `abs_norm_sub_norm_le'`

English:
theorem abs_norm_sub_norm_le'
  given: (a b : E)
  statement: |‖a‖ - ‖b‖| <= ‖a / b‖
  proof: (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]

中文:
定理 abs_norm_sub_norm_le'
  条件: (a b : E)
  结论: |‖a‖ - ‖b‖| <= ‖a / b‖
  证明: (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]

Depends on / 依赖: abs_norm_sub_norm_le_norm_inv_mul, norm_inv_mul, trans_eq
-/
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| <= ‖a / b‖ :=
  (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]
/--
theorem `norm_sub_norm_le'` / 定理 `norm_sub_norm_le'`

English:
theorem norm_sub_norm_le'
  given: (a b : E)
  statement: ‖a‖ - ‖b‖ <= ‖a / b‖
  proof: (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]

中文:
定理 norm_sub_norm_le'
  条件: (a b : E)
  结论: ‖a‖ - ‖b‖ <= ‖a / b‖
  证明: (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]

Depends on / 依赖: abs_norm_sub_norm_le, le_abs_self
-/
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ <= ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]
/--
theorem `dist_norm_norm_le'` / 定理 `dist_norm_norm_le'`

English:
theorem dist_norm_norm_le'
  given: (a b : E)
  statement: dist ‖a‖ ‖b‖ <= ‖a / b‖
  proof: abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]

中文:
定理 dist_norm_norm_le'
  条件: (a b : E)
  结论: dist ‖a‖ ‖b‖ <= ‖a / b‖
  证明: abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]

Depends on / 依赖: abs_norm_sub_norm_le
-/
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ <= ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]
/--
theorem `nndist_nnnorm_nnnorm_le'` / 定理 `nndist_nnnorm_nnnorm_le'`

English:
theorem nndist_nnnorm_nnnorm_le'
  given: (a b : E)
  statement: nndist ‖a‖₊ ‖b‖₊ <= ‖a / b‖₊
  proof: NNReal.coe_le_coe.1 dist_norm_norm_le' a b

@[to_additive]

中文:
定理 nndist_nnnorm_nnnorm_le'
  条件: (a b : E)
  结论: nndist ‖a‖₊ ‖b‖₊ <= ‖a / b‖₊
  证明: NNReal.coe_le_coe.1 dist_norm_norm_le' a b

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, dist_norm_norm_le
-/
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ <= ‖a / b‖₊ :=
NNReal.coe_le_coe.1 dist_norm_norm_le' a b

@[to_additive]
/--
theorem `nndist_eq_nnnorm_div` / 定理 `nndist_eq_nnnorm_div`

English:
theorem nndist_eq_nnnorm_div
  given: (a b : E)
  statement: nndist a b = ‖a / b‖₊
  proof: NNReal.eq dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]

中文:
定理 nndist_eq_nnnorm_div
  条件: (a b : E)
  结论: nndist a b = ‖a / b‖₊
  证明: NNReal.eq dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_norm_div
-/
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
NNReal.eq dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]
/--
theorem `edist_eq_enorm_div` / 定理 `edist_eq_enorm_div`

English:
theorem edist_eq_enorm_div
  given: (a b : E)
  statement: edist a b = ‖a / b‖ₑ
  proof: by
  rw [edist_dist]; rw [dist_eq_norm_div]; rw [ofReal_norm']

@[to_additive]

中文:
定理 edist_eq_enorm_div
  条件: (a b : E)
  结论: edist a b = ‖a / b‖ₑ
  证明: by
  rw [edist_dist]; rw [dist_eq_norm_div]; rw [ofReal_norm']

@[to_additive]

Depends on / 依赖: dist_eq_norm_div, edist_dist, ofReal_norm
-/
theorem edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ := by
  rw [edist_dist]; rw [dist_eq_norm_div]; rw [ofReal_norm']

@[to_additive]
/--
theorem `dist_inv` / 定理 `dist_inv`

English:
theorem dist_inv
  given: (x y : E)
  statement: dist x⁻¹ y = dist x y⁻¹
  proof: by
  simp_rw [dist_eq_norm_inv_mul, ← norm_inv' (x⁻¹ * y⁻¹), mul_inv, inv_inv]

中文:
定理 dist_inv
  条件: (x y : E)
  结论: dist x⁻¹ y = dist x y⁻¹
  证明: by
  simp_rw [dist_eq_norm_inv_mul, ← norm_inv' (x⁻¹ * y⁻¹), mul_inv, inv_inv]

Depends on / 依赖: dist_eq_norm_inv_mul, inv_inv, mul_inv, norm_inv, simp_rw
-/
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_inv_mul, ← norm_inv' (x⁻¹ * y⁻¹), mul_inv, inv_inv]

/--
theorem `norm_multiset_sum_le` / 定理 `norm_multiset_sum_le`

English:
theorem norm_multiset_sum_le
  given: {E} [SeminormedAddCommGroup E] (m : Multiset E)
  proof: m.le_sum_of_subadditive norm norm_zero.le norm_add_le

中文:
定理 norm_multiset_sum_le
  条件: {E} [SeminormedAddCommGroup E] (m : Multiset E)
  证明: m.le_sum_of_subadditive norm norm_zero.le norm_add_le

Depends on / 依赖: le_sum_of_subadditive, m.le_sum_of_subadditive, norm_add_le, norm_zero, norm_zero.le
-/
theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ <= (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero.le norm_add_le

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
/--
theorem `enorm_multisetSum_le` / 定理 `enorm_multisetSum_le`

English:
theorem enorm_multisetSum_le
  given: (m : Multiset ε)
  proof: m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]

中文:
定理 enorm_multisetSum_le
  条件: (m : Multiset ε)
  证明: m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]

Depends on / 依赖: enorm_add_le, enorm_zero, enorm_zero.le, le_sum_of_subadditive, m.le_sum_of_subadditive
-/
theorem enorm_multisetSum_le (m : Multiset ε) :
    ‖m.sum‖ₑ <= (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]
/--
theorem `norm_multiset_prod_le` / 定理 `norm_multiset_prod_le`

English:
theorem norm_multiset_prod_le
  given: (m : Multiset E)
  statement: ‖m.prod‖ <= (m.map fun x => ‖x‖).sum
  proof: m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

中文:
定理 norm_multiset_prod_le
  条件: (m : Multiset E)
  结论: ‖m.prod‖ <= (m.map fun x => ‖x‖).sum
  证明: m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

Depends on / 依赖: apply_prod_le_sum_map, m.apply_prod_le_sum_map, norm_mul_le, norm_one
-/
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ <= (m.map fun x => ‖x‖).sum :=
  m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε] in
@[to_additive existing]
/--
theorem `enorm_multisetProd_le` / 定理 `enorm_multisetProd_le`

English:
theorem enorm_multisetProd_le
  given: (m : Multiset ε)
  proof: m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

中文:
定理 enorm_multisetProd_le
  条件: (m : Multiset ε)
  证明: m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

Depends on / 依赖: apply_prod_le_sum_map, enorm_mul_le, enorm_one, m.apply_prod_le_sum_map
-/
theorem enorm_multisetProd_le (m : Multiset ε) :
    ‖m.prod‖ₑ <= (m.map fun x => ‖x‖ₑ).sum :=
  m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
@[bound]
/--
theorem `enorm_sum_le` / 定理 `enorm_sum_le`

English:
theorem enorm_sum_le
  given: (s : Finset ι) (f : ι -> ε)
  proof: s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]

中文:
定理 enorm_sum_le
  条件: (s : Finset ι) (f : ι -> ε)
  证明: s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]

Depends on / 依赖: enorm_add_le, enorm_zero, enorm_zero.le, le_sum_of_subadditive, s.le_sum_of_subadditive
-/
theorem enorm_sum_le (s : Finset ι) (f : ι -> ε) :
    ‖∑ i in s, f i‖ₑ <= ∑ i in s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]
/--
theorem `norm_sum_le` / 定理 `norm_sum_le`

English:
theorem norm_sum_le
  given: {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι -> E)
  proof: s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]

中文:
定理 norm_sum_le
  条件: {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι -> E)
  证明: s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]

Depends on / 依赖: le_sum_of_subadditive, norm_add_le, norm_zero, norm_zero.le, s.le_sum_of_subadditive
-/
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι -> E) :
    ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]
/--
theorem `enorm_prod_le` / 定理 `enorm_prod_le`

English:
theorem enorm_prod_le
  given: (s : Finset ι) (f : ι -> ε)
  statement: ‖∏ i in s, f i‖ₑ <= ∑ i in s, ‖f i‖ₑ
  proof: s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]

中文:
定理 enorm_prod_le
  条件: (s : Finset ι) (f : ι -> ε)
  结论: ‖∏ i in s, f i‖ₑ <= ∑ i in s, ‖f i‖ₑ
  证明: s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]

Depends on / 依赖: apply_prod_le_sum_apply, enorm_mul_le, enorm_one, s.apply_prod_le_sum_apply
-/
theorem enorm_prod_le (s : Finset ι) (f : ι -> ε) : ‖∏ i in s, f i‖ₑ <= ∑ i in s, ‖f i‖ₑ :=
  s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]
/--
theorem `norm_prod_le` / 定理 `norm_prod_le`

English:
theorem norm_prod_le
  given: (s : Finset ι) (f : ι -> E)
  statement: ‖∏ i in s, f i‖ <= ∑ i in s, ‖f i‖
  proof: s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]

中文:
定理 norm_prod_le
  条件: (s : Finset ι) (f : ι -> E)
  结论: ‖∏ i in s, f i‖ <= ∑ i in s, ‖f i‖
  证明: s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]

Depends on / 依赖: apply_prod_le_sum_apply, norm_mul_le, norm_one, s.apply_prod_le_sum_apply
-/
theorem norm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ i in s, f i‖ <= ∑ i in s, ‖f i‖ :=
  s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]
/--
theorem `enorm_prod_le_of_le` / 定理 `enorm_prod_le_of_le`

English:
theorem enorm_prod_le_of_le
  given: (s : Finset ι) {f : ι -> ε} {n : ι -> Real>=0∞} (h : forall b in s, ‖f b‖ₑ <= n b)
  proof: (enorm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]

中文:
定理 enorm_prod_le_of_le
  条件: (s : Finset ι) {f : ι -> ε} {n : ι -> 实数>=0∞} (h : 对任意 b in s, ‖f b‖ₑ <= n b)
  证明: (enorm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]

Depends on / 依赖: Finset, Finset.sum_le_sum, enorm_prod_le, sum_le_sum
-/
theorem enorm_prod_le_of_le (s : Finset ι) {f : ι -> ε} {n : ι -> Real>=0∞} (h : forall b in s, ‖f b‖ₑ <= n b) :
    ‖∏ b in s, f b‖ₑ <= ∑ b in s, n b :=
(enorm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]
/--
theorem `norm_prod_le_of_le` / 定理 `norm_prod_le_of_le`

English:
theorem norm_prod_le_of_le
  given: (s : Finset ι) {f : ι -> E} {n : ι -> Real} (h : forall b in s, ‖f b‖ <= n b)
  proof: (norm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]

中文:
定理 norm_prod_le_of_le
  条件: (s : Finset ι) {f : ι -> E} {n : ι -> 实数} (h : 对任意 b in s, ‖f b‖ <= n b)
  证明: (norm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]

Depends on / 依赖: Finset, Finset.sum_le_sum, norm_prod_le, sum_le_sum
-/
theorem norm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : ι -> Real} (h : forall b in s, ‖f b‖ <= n b) :
    ‖∏ b in s, f b‖ <= ∑ b in s, n b :=
(norm_prod_le s f).trans Finset.sum_le_sum h

@[to_additive]
/--
theorem `dist_prod_prod_le_of_le` / 定理 `dist_prod_prod_le_of_le`

English:
theorem dist_prod_prod_le_of_le
  statement: (s : Finset ι) {f a : ι -> E} {d : ι -> Real}
  proof: by
  simp_rw [dist_eq_norm_inv_mul] at h
  rw [dist_eq_norm_inv_mul]; rw [← Finset.prod_inv_distrib]; rw [← Finset.prod_mul_distrib]
  exact norm_prod_le_of_le s h

@[to_additive]

中文:
定理 dist_prod_prod_le_of_le
  结论: (s : Finset ι) {f a : ι -> E} {d : ι -> 实数}
  证明: by
  simp_rw [dist_eq_norm_inv_mul] at h
  rw [dist_eq_norm_inv_mul]; rw [← Finset.prod_inv_distrib]; rw [← Finset.prod_mul_distrib]
  exact norm_prod_le_of_le s h

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_inv_distrib, Finset.prod_mul_distrib, dist_eq_norm_inv_mul, norm_prod_le_of_le, prod_inv_distrib, prod_mul_distrib, simp_rw
-/
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι -> E} {d : ι -> Real}
    (h : forall b in s, dist (f b) (a b) <= d b) :
    dist (∏ b in s, f b) (∏ b in s, a b) <= ∑ b in s, d b := by
  simp_rw [dist_eq_norm_inv_mul] at h
  rw [dist_eq_norm_inv_mul]; rw [← Finset.prod_inv_distrib]; rw [← Finset.prod_mul_distrib]
  exact norm_prod_le_of_le s h

@[to_additive]
/--
theorem `dist_prod_prod_le` / 定理 `dist_prod_prod_le`

English:
theorem dist_prod_prod_le
  given: (s : Finset ι) (f a : ι -> E)
  proof: dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]

中文:
定理 dist_prod_prod_le
  条件: (s : Finset ι) (f a : ι -> E)
  证明: dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]

Depends on / 依赖: dist_prod_prod_le_of_le, le_rfl
-/
theorem dist_prod_prod_le (s : Finset ι) (f a : ι -> E) :
    dist (∏ b in s, f b) (∏ b in s, a b) <= ∑ b in s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]
/--
theorem `ball_eq'` / 定理 `ball_eq'`

English:
theorem ball_eq'
  given: (y : E) (ε : Real)
  statement: ball y ε = { x | ‖x / y‖ < ε }
  proof: by
  simp_rw [ball_eq_norm_inv_mul_lt, norm_inv_mul]

@[to_additive mem_ball_iff_norm]

中文:
定理 ball_eq'
  条件: (y : E) (ε : 实数)
  结论: ball y ε = { x | ‖x / y‖ < ε }
  证明: by
  simp_rw [ball_eq_norm_inv_mul_lt, norm_inv_mul]

@[to_additive mem_ball_iff_norm]

Depends on / 依赖: ball_eq_norm_inv_mul_lt, norm_inv_mul, simp_rw
-/
theorem ball_eq' (y : E) (ε : Real) : ball y ε = { x | ‖x / y‖ < ε } := by
  simp_rw [ball_eq_norm_inv_mul_lt, norm_inv_mul]

@[to_additive mem_ball_iff_norm]
/--
theorem `mem_ball_iff_norm''` / 定理 `mem_ball_iff_norm''`

English:
theorem mem_ball_iff_norm''
  statement: b in ball a r ↔ ‖b / a‖ < r
  proof: by
  rw [mem_ball]; rw [dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']

中文:
定理 mem_ball_iff_norm''
  结论: b in ball a r ↔ ‖b / a‖ < r
  证明: by
  rw [mem_ball]; rw [dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']

Depends on / 依赖: dist_eq_norm_div, mem_ball
-/
theorem mem_ball_iff_norm'' : b in ball a r ↔ ‖b / a‖ < r := by
  rw [mem_ball]; rw [dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']
/--
theorem `mem_ball_iff_norm'''` / 定理 `mem_ball_iff_norm'''`

English:
theorem mem_ball_iff_norm'''
  statement: b in ball a r ↔ ‖a / b‖ < r
  proof: by
  rw [mem_ball']; rw [dist_eq_norm_div]

中文:
定理 mem_ball_iff_norm'''
  结论: b in ball a r ↔ ‖a / b‖ < r
  证明: by
  rw [mem_ball']; rw [dist_eq_norm_div]

Depends on / 依赖: dist_eq_norm_div, mem_ball
-/
theorem mem_ball_iff_norm''' : b in ball a r ↔ ‖a / b‖ < r := by
  rw [mem_ball']; rw [dist_eq_norm_div]

/-- A scaled ball is a ball. -/
@[to_additive setOf_sub_mem_ball_eq_ball /-- A translated ball is a ball. -/]
/--
theorem `setOf_div_mem_ball_eq_ball''` / 定理 `setOf_div_mem_ball_eq_ball''`

English:
theorem setOf_div_mem_ball_eq_ball''
  proof: by
  ext x
  rw [mem_ball_iff_norm'']
  simp

@[to_additive mem_closedBall_iff_norm]

中文:
定理 setOf_div_mem_ball_eq_ball''
  证明: by
  ext x
  rw [mem_ball_iff_norm'']
  simp

@[to_additive mem_closedBall_iff_norm]

Depends on / 依赖: mem_ball_iff_norm
-/
theorem setOf_div_mem_ball_eq_ball'' :
    {x | x / a in ball 1 r} = Metric.ball a r := by
  ext x
  rw [mem_ball_iff_norm'']
  simp

@[to_additive mem_closedBall_iff_norm]
/--
theorem `mem_closedBall_iff_norm''` / 定理 `mem_closedBall_iff_norm''`

English:
theorem mem_closedBall_iff_norm''
  statement: b in closedBall a r ↔ ‖b / a‖ <= r
  proof: by
  rw [mem_closedBall]; rw [dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm']

中文:
定理 mem_closedBall_iff_norm''
  结论: b in closedBall a r ↔ ‖b / a‖ <= r
  证明: by
  rw [mem_closedBall]; rw [dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm']

Depends on / 依赖: dist_eq_norm_div, mem_closedBall
-/
theorem mem_closedBall_iff_norm'' : b in closedBall a r ↔ ‖b / a‖ <= r := by
  rw [mem_closedBall]; rw [dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm']
/--
theorem `mem_closedBall_iff_norm'''` / 定理 `mem_closedBall_iff_norm'''`

English:
theorem mem_closedBall_iff_norm'''
  statement: b in closedBall a r ↔ ‖a / b‖ <= r
  proof: by
  rw [mem_closedBall']; rw [dist_eq_norm_div]

中文:
定理 mem_closedBall_iff_norm'''
  结论: b in closedBall a r ↔ ‖a / b‖ <= r
  证明: by
  rw [mem_closedBall']; rw [dist_eq_norm_div]

Depends on / 依赖: dist_eq_norm_div, mem_closedBall
-/
theorem mem_closedBall_iff_norm''' : b in closedBall a r ↔ ‖a / b‖ <= r := by
  rw [mem_closedBall']; rw [dist_eq_norm_div]

/-- A scaled closed ball is a closed ball. -/
@[to_additive setOf_sub_mem_closedBall_eq_closedBall
  /-- A translated closed ball is a closed ball. -/]
/--
theorem `setOf_div_mem_closedBall_eq_closedBall''` / 定理 `setOf_div_mem_closedBall_eq_closedBall''`

English:
theorem setOf_div_mem_closedBall_eq_closedBall''
  proof: by
  ext x
  rw [mem_closedBall_iff_norm'']
  simp

中文:
定理 setOf_div_mem_closedBall_eq_closedBall''
  证明: by
  ext x
  rw [mem_closedBall_iff_norm'']
  simp

Depends on / 依赖: mem_closedBall_iff_norm
-/
theorem setOf_div_mem_closedBall_eq_closedBall'' :
    {x | x / a in closedBall 1 r} = Metric.closedBall a r := by
  ext x
  rw [mem_closedBall_iff_norm'']
  simp

-- Higher priority to fire before `mem_sphere`.
@[to_additive (attr := simp high) mem_sphere_iff_norm]
/--
theorem `mem_sphere_iff_norm'` / 定理 `mem_sphere_iff_norm'`

English:
theorem mem_sphere_iff_norm'
  statement: b in sphere a r ↔ ‖b / a‖ = r
  proof: by simp [dist_eq_norm_div]

中文:
定理 mem_sphere_iff_norm'
  结论: b in sphere a r ↔ ‖b / a‖ = r
  证明: by simp [dist_eq_norm_div]

Depends on / 依赖: dist_eq_norm_div
-/
theorem mem_sphere_iff_norm' : b in sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

/-- A scaled sphere is a sphere. -/
@[to_additive setOf_sub_mem_sphere_eq_sphere /-- A translated sphere is a sphere. -/]
/--
theorem `setOf_div_mem_sphere_eq_sphere''` / 定理 `setOf_div_mem_sphere_eq_sphere''`

English:
theorem setOf_div_mem_sphere_eq_sphere''
  proof: by
  ext x
  rw [mem_sphere_iff_norm']
  simp

@[to_additive]

中文:
定理 setOf_div_mem_sphere_eq_sphere''
  证明: by
  ext x
  rw [mem_sphere_iff_norm']
  simp

@[to_additive]

Depends on / 依赖: mem_sphere_iff_norm
-/
theorem setOf_div_mem_sphere_eq_sphere'' :
    {x | x / a in sphere 1 r} = Metric.sphere a r := by
  ext x
  rw [mem_sphere_iff_norm']
  simp

@[to_additive]
/--
theorem `mul_mem_ball_iff_norm` / 定理 `mul_mem_ball_iff_norm`

English:
theorem mul_mem_ball_iff_norm
  statement: a * b in ball a r ↔ ‖b‖ < r
  proof: by
  rw [mem_ball_iff_norm'']
  simp

@[to_additive]

中文:
定理 mul_mem_ball_iff_norm
  结论: a * b in ball a r ↔ ‖b‖ < r
  证明: by
  rw [mem_ball_iff_norm'']
  simp

@[to_additive]

Depends on / 依赖: mem_ball_iff_norm
-/
theorem mul_mem_ball_iff_norm : a * b in ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'']
  simp

@[to_additive]
/--
theorem `mul_mem_closedBall_iff_norm` / 定理 `mul_mem_closedBall_iff_norm`

English:
theorem mul_mem_closedBall_iff_norm
  statement: a * b in closedBall a r ↔ ‖b‖ <= r
  proof: by
  rw [mem_closedBall_iff_norm'']
  simp

中文:
定理 mul_mem_closedBall_iff_norm
  结论: a * b in closedBall a r ↔ ‖b‖ <= r
  证明: by
  rw [mem_closedBall_iff_norm'']
  simp

Depends on / 依赖: mem_closedBall_iff_norm
-/
theorem mul_mem_closedBall_iff_norm : a * b in closedBall a r ↔ ‖b‖ <= r := by
  rw [mem_closedBall_iff_norm'']
  simp

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_ball`.
@[to_additive (attr := simp high)]
/--
theorem `preimage_mul_ball` / 定理 `preimage_mul_ball`

English:
theorem preimage_mul_ball
  given: (a b : E) (r : Real)
  statement: (b * ·) ⁻¹' ball a r = ball (a / b) r
  proof: by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_ball, div_eq_mul_inv, mul_comm, mul_assoc]

中文:
定理 preimage_mul_ball
  条件: (a b : E) (r : 实数)
  结论: (b * ·) ⁻¹' ball a r = ball (a / b) r
  证明: by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_ball, div_eq_mul_inv, mul_comm, mul_assoc]

Depends on / 依赖: Set.mem_preimage, dist_eq_norm_inv_mul, div_eq_mul_inv, mem_ball, mem_preimage, mul_assoc, mul_comm
-/
theorem preimage_mul_ball (a b : E) (r : Real) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_ball, div_eq_mul_inv, mul_comm, mul_assoc]

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_closedBall`.
@[to_additive (attr := simp high)]
/--
theorem `preimage_mul_closedBall` / 定理 `preimage_mul_closedBall`

English:
theorem preimage_mul_closedBall
  given: (a b : E) (r : Real)
  proof: by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_closedBall, div_eq_mul_inv, mul_comm, mul_assoc]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_closedBall
  条件: (a b : E) (r : 实数)
  证明: by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_closedBall, div_eq_mul_inv, mul_comm, mul_assoc]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_preimage, dist_eq_norm_inv_mul, div_eq_mul_inv, mem_closedBall, mem_preimage, mul_assoc, mul_comm
-/
theorem preimage_mul_closedBall (a b : E) (r : Real) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_closedBall, div_eq_mul_inv, mul_comm, mul_assoc]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_sphere` / 定理 `preimage_mul_sphere`

English:
theorem preimage_mul_sphere
  given: (a b : E) (r : Real)
  statement: (b * ·) ⁻¹' sphere a r = sphere (a / b) r
  proof: by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive]

中文:
定理 preimage_mul_sphere
  条件: (a b : E) (r : 实数)
  结论: (b * ·) ⁻¹' sphere a r = sphere (a / b) r
  证明: by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive]

Depends on / 依赖: Set.mem_preimage, div_div_eq_mul_div, mem_preimage, mem_sphere_iff_norm, mul_comm
-/
theorem preimage_mul_sphere (a b : E) (r : Real) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive]
/--
theorem `pow_mem_closedBall` / 定理 `pow_mem_closedBall`

English:
theorem pow_mem_closedBall
  given: {n : Nat} (h : a in closedBall b r)
  proof: by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]

中文:
定理 pow_mem_closedBall
  条件: {n : 自然数} (h : a in closedBall b r)
  证明: by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]

Depends on / 依赖: cast_nonneg, dist_eq_norm_inv_mul, inv_pow, mem_closedBall, mul_le_mul_of_nonneg_left, mul_pow, n.cast_nonneg, norm_pow_le_mul_norm, norm_pow_le_mul_norm.trans, nsmul_eq_mul
-/
theorem pow_mem_closedBall {n : Nat} (h : a in closedBall b r) :
    a ^ n in closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]
/--
theorem `pow_mem_ball` / 定理 `pow_mem_ball`

English:
theorem pow_mem_ball
  given: {n : Nat} (hn : 0 < n) (h : a in ball b r)
  statement: a ^ n in ball (b ^ n) (n • r)
  proof: by
  simp only [mem_ball, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : Real) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]

中文:
定理 pow_mem_ball
  条件: {n : 自然数} (hn : 0 < n) (h : a in ball b r)
  结论: a ^ n in ball (b ^ n) (n • r)
  证明: by
  simp only [mem_ball, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : Real) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, inv_pow, lt_of_le_of_lt, mem_ball, mul_pow, norm_pow_le_mul_norm, nsmul_eq_mul, replace
-/
theorem pow_mem_ball {n : Nat} (hn : 0 < n) (h : a in ball b r) : a ^ n in ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : Real) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]
/--
theorem `mul_mem_closedBall_mul_iff` / 定理 `mul_mem_closedBall_mul_iff`

English:
theorem mul_mem_closedBall_mul_iff
  given: {c : E}
  statement: a * c in closedBall (b * c) r ↔ a in closedBall b r
  proof: by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]

中文:
定理 mul_mem_closedBall_mul_iff
  条件: {c : E}
  结论: a * c in closedBall (b * c) r ↔ a in closedBall b r
  证明: by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_closedBall, mul_comm
-/
theorem mul_mem_closedBall_mul_iff {c : E} : a * c in closedBall (b * c) r ↔ a in closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
/--
theorem `mul_mem_ball_mul_iff` / 定理 `mul_mem_ball_mul_iff`

English:
theorem mul_mem_ball_mul_iff
  given: {c : E}
  statement: a * c in ball (b * c) r ↔ a in ball b r
  proof: by
  simp only [mem_ball, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]

中文:
定理 mul_mem_ball_mul_iff
  条件: {c : E}
  结论: a * c in ball (b * c) r ↔ a in ball b r
  证明: by
  simp only [mem_ball, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, mem_ball, mul_comm
-/
theorem mul_mem_ball_mul_iff {c : E} : a * c in ball (b * c) r ↔ a in ball b r := by
  simp only [mem_ball, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
/--
theorem `smul_closedBall''` / 定理 `smul_closedBall''`

English:
theorem smul_closedBall''
  statement: a • closedBall b r = closedBall (a • b) r
  proof: by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]

中文:
定理 smul_closedBall''
  结论: a • closedBall b r = closedBall (a • b) r
  证明: by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]

Depends on / 依赖: Set.mem_smul_set, dist_eq_norm_inv_mul, eq_inv_mul_iff_mul_eq, mem_closedBall, mem_smul_set, mul_assoc
-/
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
/--
theorem `smul_ball''` / 定理 `smul_ball''`

English:
theorem smul_ball''
  statement: a • ball b r = ball (a • b) r
  proof: by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]

中文:
定理 smul_ball''
  结论: a • ball b r = ball (a • b) r
  证明: by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]

Depends on / 依赖: Set.mem_smul_set, dist_eq_norm_inv_mul, eq_inv_mul_iff_mul_eq, mem_ball, mem_smul_set, mul_assoc
-/
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
/--
theorem `nnnorm_multiset_prod_le` / 定理 `nnnorm_multiset_prod_le`

English:
theorem nnnorm_multiset_prod_le
  given: (m : Multiset E)
  statement: ‖m.prod‖₊ <= (m.map fun x => ‖x‖₊).sum
  proof: NNReal.coe_le_coe.1 by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]

中文:
定理 nnnorm_multiset_prod_le
  条件: (m : Multiset E)
  结论: ‖m.prod‖₊ <= (m.map fun x => ‖x‖₊).sum
  证明: NNReal.coe_le_coe.1 by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]

Depends on / 依赖: Multiset, Multiset.map_map, NNReal, NNReal.coe_le_coe, coe_le_coe, map_map, norm_multiset_prod_le
-/
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ <= (m.map fun x => ‖x‖₊).sum :=
NNReal.coe_le_coe.1 by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
/--
theorem `nnnorm_prod_le` / 定理 `nnnorm_prod_le`

English:
theorem nnnorm_prod_le
  given: (s : Finset ι) (f : ι -> E)
  statement: ‖∏ a in s, f a‖₊ <= ∑ a in s, ‖f a‖₊
  proof: NNReal.coe_le_coe.1 by
    push_cast
    exact norm_prod_le _ _

@[to_additive]

中文:
定理 nnnorm_prod_le
  条件: (s : Finset ι) (f : ι -> E)
  结论: ‖∏ a in s, f a‖₊ <= ∑ a in s, ‖f a‖₊
  证明: NNReal.coe_le_coe.1 by
    push_cast
    exact norm_prod_le _ _

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, norm_prod_le
-/
theorem nnnorm_prod_le (s : Finset ι) (f : ι -> E) : ‖∏ a in s, f a‖₊ <= ∑ a in s, ‖f a‖₊ :=
NNReal.coe_le_coe.1 by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
/--
theorem `nnnorm_prod_le_of_le` / 定理 `nnnorm_prod_le_of_le`

English:
theorem nnnorm_prod_le_of_le
  given: (s : Finset ι) {f : ι -> E} {n : ι -> Real>=0} (h : forall b in s, ‖f b‖₊ <= n b)
  proof: (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]

中文:
定理 nnnorm_prod_le_of_le
  条件: (s : Finset ι) {f : ι -> E} {n : ι -> 实数>=0} (h : 对任意 b in s, ‖f b‖₊ <= n b)
  证明: (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_sum, coe_sum, norm_prod_le_of_le, trans_eq
-/
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι -> E} {n : ι -> Real>=0} (h : forall b in s, ‖f b‖₊ <= n b) :
    ‖∏ b in s, f b‖₊ <= ∑ b in s, n b :=
  (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]
/--
theorem `NormedCommGroup.tendsto_nhds_nhds` / 定理 `NormedCommGroup.tendsto_nhds_nhds`

English:
theorem NormedCommGroup.tendsto_nhds_nhds
  given: {f : E -> F} {x : E} {y : F}
  proof: by
  simpa [norm_inv_mul] using NormedGroup.tendsto_nhds_nhds (f := f) (x := x) (y := y)

@[to_additive]

中文:
定理 NormedCommGroup.tendsto_nhds_nhds
  条件: {f : E -> F} {x : E} {y : F}
  证明: by
  simpa [norm_inv_mul] using NormedGroup.tendsto_nhds_nhds (f := f) (x := x) (y := y)

@[to_additive]

Depends on / 依赖: NormedGroup, NormedGroup.tendsto_nhds_nhds, norm_inv_mul, tendsto_nhds_nhds
-/
theorem NormedCommGroup.tendsto_nhds_nhds {f : E -> F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ forall ε > 0, exists δ > 0, forall x', ‖x' / x‖ < δ -> ‖f x' / y‖ < ε := by
  simpa [norm_inv_mul] using NormedGroup.tendsto_nhds_nhds (f := f) (x := x) (y := y)

@[to_additive]
/--
theorem `NormedCommGroup.nhds_basis_norm_lt` / 定理 `NormedCommGroup.nhds_basis_norm_lt`

English:
theorem NormedCommGroup.nhds_basis_norm_lt
  given: (x : E)
  proof: by
  simpa [norm_inv_mul] using NormedGroup.nhds_basis_norm_lt x

@[to_additive]

中文:
定理 NormedCommGroup.nhds_basis_norm_lt
  条件: (x : E)
  证明: by
  simpa [norm_inv_mul] using NormedGroup.nhds_basis_norm_lt x

@[to_additive]

Depends on / 依赖: NormedGroup, NormedGroup.nhds_basis_norm_lt, nhds_basis_norm_lt, norm_inv_mul
-/
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : Real => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.nhds_basis_norm_lt x

@[to_additive]
/--
theorem `NormedCommGroup.uniformity_basis_dist` / 定理 `NormedCommGroup.uniformity_basis_dist`

English:
theorem NormedCommGroup.uniformity_basis_dist
  proof: by
  simpa [norm_inv_mul] using NormedGroup.uniformity_basis_dist (E := E)

中文:
定理 NormedCommGroup.uniformity_basis_dist
  证明: by
  simpa [norm_inv_mul] using NormedGroup.uniformity_basis_dist (E := E)

Depends on / 依赖: NormedGroup, NormedGroup.uniformity_basis_dist, norm_inv_mul, uniformity_basis_dist
-/
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : Real => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.uniformity_basis_dist (E := E)

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

@[to_additive (attr := simp) norm_le_zero_iff]
/--
lemma `norm_le_zero_iff'` / 引理 `norm_le_zero_iff'`

English:
lemma norm_le_zero_iff'
  statement: ‖a‖ <= 0 ↔ a = 1
  proof: by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]

中文:
引理 norm_le_zero_iff'
  结论: ‖a‖ <= 0 ↔ a = 1
  证明: by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]

Depends on / 依赖: dist_le_zero, dist_one_right
-/
lemma norm_le_zero_iff' : ‖a‖ <= 0 ↔ a = 1 := by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]
/--
lemma `norm_pos_iff'` / 引理 `norm_pos_iff'`

English:
lemma norm_pos_iff'
  statement: 0 < ‖a‖ ↔ a != 1
  proof: by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]

中文:
引理 norm_pos_iff'
  结论: 0 < ‖a‖ ↔ a != 1
  证明: by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]

Depends on / 依赖: norm_le_zero_iff, not_le
-/
lemma norm_pos_iff' : 0 < ‖a‖ ↔ a != 1 := by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]
/--
lemma `norm_eq_zero'` / 引理 `norm_eq_zero'`

English:
lemma norm_eq_zero'
  statement: ‖a‖ = 0 ↔ a = 1
  proof: (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]

中文:
引理 norm_eq_zero'
  结论: ‖a‖ = 0 ↔ a = 1
  证明: (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]

Depends on / 依赖: ge_iff_eq, norm_le_zero_iff, norm_nonneg, symm.trans
-/
lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]
/--
lemma `norm_ne_zero_iff'` / 引理 `norm_ne_zero_iff'`

English:
lemma norm_ne_zero_iff'
  statement: ‖a‖ != 0 ↔ a != 1
  proof: norm_eq_zero'.not

@[to_additive]

中文:
引理 norm_ne_zero_iff'
  结论: ‖a‖ != 0 ↔ a != 1
  证明: norm_eq_zero'.not

@[to_additive]

Depends on / 依赖: norm_eq_zero
-/
lemma norm_ne_zero_iff' : ‖a‖ != 0 ↔ a != 1 := norm_eq_zero'.not

@[to_additive]
/--
theorem `norm_div_eq_zero_iff` / 定理 `norm_div_eq_zero_iff`

English:
theorem norm_div_eq_zero_iff
  statement: ‖a / b‖ = 0 ↔ a = b
  proof: by rw [norm_eq_zero', div_eq_one]

@[to_additive]

中文:
定理 norm_div_eq_zero_iff
  结论: ‖a / b‖ = 0 ↔ a = b
  证明: by rw [norm_eq_zero', div_eq_one]

@[to_additive]

Depends on / 依赖: div_eq_one, norm_eq_zero
-/
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero', div_eq_one]

@[to_additive]
/--
theorem `norm_div_pos_iff` / 定理 `norm_div_pos_iff`

English:
theorem norm_div_pos_iff
  statement: 0 < ‖a / b‖ ↔ a != b
  proof: by
  rw [(norm_nonneg' _).lt_iff_ne]; rw [ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]

中文:
定理 norm_div_pos_iff
  结论: 0 < ‖a / b‖ ↔ a != b
  证明: by
  rw [(norm_nonneg' _).lt_iff_ne]; rw [ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]

Depends on / 依赖: lt_iff_ne, ne_comm, norm_div_eq_zero_iff, norm_div_eq_zero_iff.not, norm_nonneg
-/
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a != b := by
  rw [(norm_nonneg' _).lt_iff_ne]; rw [ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]
/--
theorem `eq_of_norm_div_le_zero` / 定理 `eq_of_norm_div_le_zero`

English:
theorem eq_of_norm_div_le_zero
  given: (h : ‖a / b‖ <= 0)
  statement: a = b
  proof: by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

中文:
定理 eq_of_norm_div_le_zero
  条件: (h : ‖a / b‖ <= 0)
  结论: a = b
  证明: by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

Depends on / 依赖: div_eq_one, norm_le_zero_iff
-/
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ <= 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive]
/--
theorem `eq_one_or_norm_pos` / 定理 `eq_one_or_norm_pos`

English:
theorem eq_one_or_norm_pos
  given: (a : E)
  statement: a = 1 ∨ 0 < ‖a‖
  proof: by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]

中文:
定理 eq_one_or_norm_pos
  条件: (a : E)
  结论: a = 1 ∨ 0 < ‖a‖
  证明: by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]

Depends on / 依赖: eq_comm, eq_or_lt, norm_nonneg
-/
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]
/--
theorem `eq_one_or_nnnorm_pos` / 定理 `eq_one_or_nnnorm_pos`

English:
theorem eq_one_or_nnnorm_pos
  given: (a : E)
  statement: a = 1 ∨ 0 < ‖a‖₊
  proof: eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]

中文:
定理 eq_one_or_nnnorm_pos
  条件: (a : E)
  结论: a = 1 ∨ 0 < ‖a‖₊
  证明: eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]

Depends on / 依赖: eq_one_or_norm_pos
-/
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]
/--
theorem `nnnorm_eq_zero'` / 定理 `nnnorm_eq_zero'`

English:
theorem nnnorm_eq_zero'
  statement: ‖a‖₊ = 0 ↔ a = 1
  proof: by
  rw [← NNReal.coe_eq_zero]; rw [coe_nnnorm']; rw [norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]

中文:
定理 nnnorm_eq_zero'
  结论: ‖a‖₊ = 0 ↔ a = 1
  证明: by
  rw [← NNReal.coe_eq_zero]; rw [coe_nnnorm']; rw [norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]

Depends on / 依赖: NNReal, NNReal.coe_eq_zero, coe_eq_zero, coe_nnnorm, norm_eq_zero
-/
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero]; rw [coe_nnnorm']; rw [norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]
/--
theorem `nnnorm_ne_zero_iff'` / 定理 `nnnorm_ne_zero_iff'`

English:
theorem nnnorm_ne_zero_iff'
  statement: ‖a‖₊ != 0 ↔ a != 1
  proof: nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]

中文:
定理 nnnorm_ne_zero_iff'
  结论: ‖a‖₊ != 0 ↔ a != 1
  证明: nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]

Depends on / 依赖: nnnorm_eq_zero
-/
theorem nnnorm_ne_zero_iff' : ‖a‖₊ != 0 ↔ a != 1 :=
  nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]
/--
lemma `nnnorm_pos'` / 引理 `nnnorm_pos'`

English:
lemma nnnorm_pos'
  statement: 0 < ‖a‖₊ ↔ a != 1
  proof: pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

中文:
引理 nnnorm_pos'
  结论: 0 < ‖a‖₊ ↔ a != 1
  证明: pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

Depends on / 依赖: nnnorm_ne_zero_iff, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a != 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive /-- The norm of a normed group as an additive group norm. -/]
/--
Definition of `normGroupNorm` / `normGroupNorm` 的定义

English:
definition normGroupNorm
  signature: : GroupNorm E
  body: { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]

中文:
定义 normGroupNorm
  签名: : GroupNorm E
  定义体: { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]

Depends on / 依赖: eq_one_of_map_eq_zero, normGroupSeminorm, norm_eq_zero
-/
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]
/--
theorem `coe_normGroupNorm` / 定理 `coe_normGroupNorm`

English:
theorem coe_normGroupNorm
  statement: ⇑(normGroupNorm E) = norm
  proof: rfl

中文:
定理 coe_normGroupNorm
  结论: ⇑(normGroupNorm E) = norm
  证明: rfl
-/
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α -> E}


/--
theorem `hasCompactSupport_norm_iff` / 定理 `hasCompactSupport_norm_iff`

English:
theorem hasCompactSupport_norm_iff
  statement: (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f
  proof: hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

中文:
定理 hasCompactSupport_norm_iff
  结论: (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f
  证明: hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

Depends on / 依赖: hasCompactSupport_comp_left, norm_eq_zero
-/
theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

end NormedAddGroup

/-! ### `positivity` extensions -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are always nonnegative, and positive
on non-one inputs. -/
@[positivity ‖_‖]
meta def evalMulNorm : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedGroup_E ← synthInstanceQ q(SeminormedGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 1` assumption
    let o : Option (Q(NormedGroup $E) × Q($a != 1)) ← do
      let .some normedGroup_E ← trySynthInstanceQ q(NormedGroup $E) | pure none
      let some pa ← findLocalDeclWithTypeQ? q($a != 1) | pure none
pure some (normedGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff'.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg' $a)
  | _, _, _ => throwError "not `‖·‖`"

/-- Extension for the `positivity` tactic: additive norms are always nonnegative, and positive
on non-zero inputs. -/
@[positivity ‖_‖]
meta def evalAddNorm : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedAddGroup_E ← synthInstanceQ q(SeminormedAddGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 0` assumption
    let o : Option (Q(NormedAddGroup $E) × Q($a != 0)) ← do
      let .some normedAddGroup_E ← trySynthInstanceQ q(NormedAddGroup $E) | pure none
      let some pa ← findLocalDeclWithTypeQ? q($a != 0) | pure none
pure some (normedAddGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedAddGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg $a)
  | _, _, _ => throwError "not `‖·‖`"

end Mathlib.Meta.Positivity
