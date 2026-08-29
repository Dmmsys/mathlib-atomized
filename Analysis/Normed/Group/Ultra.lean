/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Ultrametric norms

This file contains results on the behavior of norms in ultrametric groups.

## Main results

* `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`:
  a normed additive group has an ultrametric iff the norm is nonarchimedean
* `IsUltrametricDist.nonarchimedeanGroup` and its additive version: instance showing that a
  commutative group with a nonarchimedean seminorm is a nonarchimedean topological group (i.e.
  there is a neighbourhood basis of the identity consisting of open subgroups).

## Implementation details

Some results are proved first about `nnnorm : X → ℝ≥0` because the bottom element
in `NNReal` is 0, so easier to make statements about maxima of empty sets.

## Tags

ultrametric, nonarchimedean
-/

@[expose] public section
open Metric NNReal

namespace IsUltrametricDist

section Group

variable {S S' ι : Type*} [SeminormedGroup S] [SeminormedGroup S'] [IsUltrametricDist S]

@[to_additive]
/--
lemma `norm_mul_le_max` / 引理 `norm_mul_le_max`

English:
lemma norm_mul_le_max
  given: (x y : S)
  proof: by
  simpa [le_max_iff, dist_eq_norm_inv_mul] using dist_triangle_max x⁻¹ 1 y

@[to_additive]

中文:
引理 norm_mul_le_max
  条件: (x y : S)
  证明: by
  simpa [le_max_iff, dist_eq_norm_inv_mul] using dist_triangle_max x⁻¹ 1 y

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, dist_triangle_max, le_max_iff
-/
lemma norm_mul_le_max (x y : S) :
    ‖x * y‖ <= max ‖x‖ ‖y‖ := by
  simpa [le_max_iff, dist_eq_norm_inv_mul] using dist_triangle_max x⁻¹ 1 y

@[to_additive]
/--
lemma `isUltrametricDist_of_forall_norm_mul_le_max_norm` / 引理 `isUltrametricDist_of_forall_norm_mul_le_max_norm`

English:
lemma isUltrametricDist_of_forall_norm_mul_le_max_norm
  proof: by
    simpa [dist_eq_norm_inv_mul] using h (x⁻¹ * y) (y⁻¹ * z)

中文:
引理 isUltrametricDist_of_对任意_norm_mul_le_max_norm
  证明: by
    simpa [dist_eq_norm_inv_mul] using h (x⁻¹ * y) (y⁻¹ * z)

Depends on / 依赖: dist_eq_norm_inv_mul
-/
lemma isUltrametricDist_of_forall_norm_mul_le_max_norm
    (h : forall x y : S', ‖x * y‖ <= max ‖x‖ ‖y‖) : IsUltrametricDist S' where
  dist_triangle_max x y z := by
    simpa [dist_eq_norm_inv_mul] using h (x⁻¹ * y) (y⁻¹ * z)

/--
lemma `isUltrametricDist_of_isNonarchimedean_norm` / 引理 `isUltrametricDist_of_isNonarchimedean_norm`

English:
lemma isUltrametricDist_of_isNonarchimedean_norm
  statement: {S' : Type*} [SeminormedAddGroup S']
  proof: isUltrametricDist_of_forall_norm_add_le_max_norm h

中文:
引理 isUltrametricDist_of_isNonarchimedean_norm
  结论: {S' : 类型} [半赋范加群 S']
  证明: isUltrametricDist_of_forall_norm_add_le_max_norm h

Depends on / 依赖: isUltrametricDist_of_forall_norm_add_le_max_norm
-/
lemma isUltrametricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean (norm : S' -> Real)) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h

/--
lemma `isNonarchimedean_norm` / 引理 `isNonarchimedean_norm`

English:
lemma isNonarchimedean_norm
  given: {R} [SeminormedAddCommGroup R] [IsUltrametricDist R]
  proof: by
  intro x y
  convert! dist_triangle_max 0 x (x + y) using 1
  · simp
  · congr <;> simp [SeminormedAddGroup.dist_eq]

中文:
引理 isNonarchimedean_norm
  条件: {R} [SeminormedAddComm群 R] [是UltrametricDist R]
  证明: by
  intro x y
  convert! dist_triangle_max 0 x (x + y) using 1
  · simp
  · congr <;> simp [SeminormedAddGroup.dist_eq]

Depends on / 依赖: SeminormedAddGroup, SeminormedAddGroup.dist_eq, convert, dist_eq, dist_triangle_max
-/
lemma isNonarchimedean_norm {R} [SeminormedAddCommGroup R] [IsUltrametricDist R] :
    IsNonarchimedean (‖·‖ : R -> Real) := by
  intro x y
  convert! dist_triangle_max 0 x (x + y) using 1
  · simp
  · congr <;> simp [SeminormedAddGroup.dist_eq]

/--
lemma `isUltrametricDist_iff_isNonarchimedean_norm` / 引理 `isUltrametricDist_iff_isNonarchimedean_norm`

English:
lemma isUltrametricDist_iff_isNonarchimedean_norm
  given: {R} [SeminormedAddCommGroup R]
  proof: ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

@[to_additive]

中文:
引理 isUltrametricDist_iff_isNonarchimedean_norm
  条件: {R} [SeminormedAddComm群 R]
  证明: ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

@[to_additive]

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm, h.isNonarchimedean_norm, isNonarchimedean_norm, isUltrametricDist_of_isNonarchimedean_norm
-/
lemma isUltrametricDist_iff_isNonarchimedean_norm {R} [SeminormedAddCommGroup R] :
    IsUltrametricDist R ↔ IsNonarchimedean (‖·‖ : R -> Real) :=
  ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

@[to_additive]
/--
lemma `nnnorm_mul_le_max` / 引理 `nnnorm_mul_le_max`

English:
lemma nnnorm_mul_le_max
  given: (x y : S)
  proof: norm_mul_le_max _ _

@[to_additive]

中文:
引理 nnnorm_mul_le_max
  条件: (x y : S)
  证明: norm_mul_le_max _ _

@[to_additive]

Depends on / 依赖: norm_mul_le_max
-/
lemma nnnorm_mul_le_max (x y : S) :
    ‖x * y‖₊ <= max ‖x‖₊ ‖y‖₊ :=
  norm_mul_le_max _ _

@[to_additive]
/--
lemma `isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm` / 引理 `isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm`

English:
lemma isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm
  proof: isUltrametricDist_of_forall_norm_mul_le_max_norm h

中文:
引理 isUltrametricDist_of_对任意_nnnorm_mul_le_max_nnnorm
  证明: isUltrametricDist_of_forall_norm_mul_le_max_norm h

Depends on / 依赖: isUltrametricDist_of_forall_norm_mul_le_max_norm
-/
lemma isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm
    (h : forall x y : S', ‖x * y‖₊ <= max ‖x‖₊ ‖y‖₊) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_mul_le_max_norm h

/--
lemma `isUltrametricDist_of_isNonarchimedean_nnnorm` / 引理 `isUltrametricDist_of_isNonarchimedean_nnnorm`

English:
lemma isUltrametricDist_of_isNonarchimedean_nnnorm
  statement: {S' : Type*} [SeminormedAddGroup S']
  proof: isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h

中文:
引理 isUltrametricDist_of_isNonarchimedean_nnnorm
  结论: {S' : 类型} [半赋范加群 S']
  证明: isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h

Depends on / 依赖: isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm
-/
lemma isUltrametricDist_of_isNonarchimedean_nnnorm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean (nnnorm : S' -> Real>=0)) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h

/--
lemma `isNonarchimedean_nnnorm` / 引理 `isNonarchimedean_nnnorm`

English:
lemma isNonarchimedean_nnnorm
  given: {R} [SeminormedAddCommGroup R] [IsUltrametricDist R]
  proof: by
  simpa using isNonarchimedean_norm

中文:
引理 isNonarchimedean_nnnorm
  条件: {R} [SeminormedAddComm群 R] [是UltrametricDist R]
  证明: by
  simpa using isNonarchimedean_norm

Depends on / 依赖: isNonarchimedean_norm
-/
lemma isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup R] [IsUltrametricDist R] :
    IsNonarchimedean (‖·‖₊ : R -> Real) := by
  simpa using isNonarchimedean_norm

/--
lemma `isUltrametricDist_iff_isNonarchimedean_nnnorm` / 引理 `isUltrametricDist_iff_isNonarchimedean_nnnorm`

English:
lemma isUltrametricDist_iff_isNonarchimedean_nnnorm
  given: {R} [SeminormedAddCommGroup R]
  proof: ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

中文:
引理 isUltrametricDist_iff_isNonarchimedean_nnnorm
  条件: {R} [SeminormedAddComm群 R]
  证明: ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm, h.isNonarchimedean_norm, isNonarchimedean_norm, isUltrametricDist_of_isNonarchimedean_norm
-/
lemma isUltrametricDist_iff_isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup R] :
    IsUltrametricDist R ↔ IsNonarchimedean (‖·‖₊ : R -> Real) :=
  ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/--
lemma `norm_mul_eq_max_of_norm_ne_norm` / 引理 `norm_mul_eq_max_of_norm_ne_norm`

English:
lemma norm_mul_eq_max_of_norm_ne_norm
  proof: by
  rw [← inv_inv x]; rw [← dist_eq_norm_inv_mul]; rw [dist_eq_max_of_dist_ne_dist _ 1 _ (by simp [h])]
  simp only [dist_one_right, dist_one_left, norm_inv']

@[to_additive]

中文:
引理 norm_mul_eq_max_of_norm_ne_norm
  证明: by
  rw [← inv_inv x]; rw [← dist_eq_norm_inv_mul]; rw [dist_eq_max_of_dist_ne_dist _ 1 _ (by simp [h])]
  simp only [dist_one_right, dist_one_left, norm_inv']

@[to_additive]

Depends on / 依赖: dist_eq_max_of_dist_ne_dist, dist_eq_norm_inv_mul, dist_one_left, dist_one_right, inv_inv, norm_inv
-/
lemma norm_mul_eq_max_of_norm_ne_norm
    {x y : S} (h : ‖x‖ != ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖ := by
  rw [← inv_inv x]; rw [← dist_eq_norm_inv_mul]; rw [dist_eq_max_of_dist_ne_dist _ 1 _ (by simp [h])]
  simp only [dist_one_right, dist_one_left, norm_inv']

@[to_additive]
/--
lemma `norm_eq_of_mul_norm_lt_max` / 引理 `norm_eq_of_mul_norm_lt_max`

English:
lemma norm_eq_of_mul_norm_lt_max
  given: {x y : S} (h : ‖x * y‖ < max ‖x‖ ‖y‖)
  proof: not_ne_iff.mp (h.ne ∘ norm_mul_eq_max_of_norm_ne_norm)

中文:
引理 norm_eq_of_mul_norm_lt_max
  条件: {x y : S} (h : ‖x * y‖ < 最大值 ‖x‖ ‖y‖)
  证明: not_ne_iff.mp (h.ne ∘ norm_mul_eq_max_of_norm_ne_norm)

Depends on / 依赖: h.ne, norm_mul_eq_max_of_norm_ne_norm, not_ne_iff, not_ne_iff.mp
-/
lemma norm_eq_of_mul_norm_lt_max {x y : S} (h : ‖x * y‖ < max ‖x‖ ‖y‖) :
    ‖x‖ = ‖y‖ :=
  not_ne_iff.mp (h.ne ∘ norm_mul_eq_max_of_norm_ne_norm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/--
lemma `nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm` / 引理 `nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm`

English:
lemma nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm
  proof: by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_mul_eq_max_of_norm_ne_norm (NNReal.coe_injective.ne h)

@[to_additive]

中文:
引理 nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm
  证明: by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_mul_eq_max_of_norm_ne_norm (NNReal.coe_injective.ne h)

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_injective.ne, NNReal.coe_max, coe_inj, coe_injective, coe_max, norm_mul_eq_max_of_norm_ne_norm
-/
lemma nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm
    {x y : S} (h : ‖x‖₊ != ‖y‖₊) : ‖x * y‖₊ = max ‖x‖₊ ‖y‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_mul_eq_max_of_norm_ne_norm (NNReal.coe_injective.ne h)

@[to_additive]
/--
lemma `nnnorm_eq_of_mul_nnnorm_lt_max` / 引理 `nnnorm_eq_of_mul_nnnorm_lt_max`

English:
lemma nnnorm_eq_of_mul_nnnorm_lt_max
  given: {x y : S} (h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊)
  proof: not_ne_iff.mp (h.ne ∘ nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm)

中文:
引理 nnnorm_eq_of_mul_nnnorm_lt_max
  条件: {x y : S} (h : ‖x * y‖₊ < 最大值 ‖x‖₊ ‖y‖₊)
  证明: not_ne_iff.mp (h.ne ∘ nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm)

Depends on / 依赖: h.ne, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm, not_ne_iff, not_ne_iff.mp
-/
lemma nnnorm_eq_of_mul_nnnorm_lt_max {x y : S} (h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊) :
    ‖x‖₊ = ‖y‖₊ :=
  not_ne_iff.mp (h.ne ∘ nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/--
lemma `norm_div_eq_max_of_norm_div_ne_norm_div` / 引理 `norm_div_eq_max_of_norm_div_ne_norm_div`

English:
lemma norm_div_eq_max_of_norm_div_ne_norm_div
  given: (x y z : S) (h : ‖x / y‖ != ‖y / z‖)
  proof: by
  simpa only [div_mul_div_cancel] using norm_mul_eq_max_of_norm_ne_norm h

中文:
引理 norm_div_eq_max_of_norm_div_ne_norm_div
  条件: (x y z : S) (h : ‖x / y‖ != ‖y / z‖)
  证明: by
  simpa only [div_mul_div_cancel] using norm_mul_eq_max_of_norm_ne_norm h

Depends on / 依赖: div_mul_div_cancel, norm_mul_eq_max_of_norm_ne_norm
-/
lemma norm_div_eq_max_of_norm_div_ne_norm_div (x y z : S) (h : ‖x / y‖ != ‖y / z‖) :
    ‖x / z‖ = max ‖x / y‖ ‖y / z‖ := by
  simpa only [div_mul_div_cancel] using norm_mul_eq_max_of_norm_ne_norm h

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/--
lemma `nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div` / 引理 `nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div`

English:
lemma nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div
  given: (x y z : S) (h : ‖x / y‖₊ != ‖y / z‖₊)
  proof: by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_div_eq_max_of_norm_div_ne_norm_div _ _ _ (NNReal.coe_injective.ne h)

@[to_additive]

中文:
引理 nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div
  条件: (x y z : S) (h : ‖x / y‖₊ != ‖y / z‖₊)
  证明: by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_div_eq_max_of_norm_div_ne_norm_div _ _ _ (NNReal.coe_injective.ne h)

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_injective.ne, NNReal.coe_max, coe_inj, coe_injective, coe_max, norm_div_eq_max_of_norm_div_ne_norm_div
-/
lemma nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div (x y z : S) (h : ‖x / y‖₊ != ‖y / z‖₊) :
    ‖x / z‖₊ = max ‖x / y‖₊ ‖y / z‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_div_eq_max_of_norm_div_ne_norm_div _ _ _ (NNReal.coe_injective.ne h)

@[to_additive]
/--
lemma `nnnorm_pow_le` / 引理 `nnnorm_pow_le`

English:
lemma nnnorm_pow_le
  given: (x : S) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_add, hn] using nnnorm_mul_le_max (x ^ n) x

@[to_additive]

中文:
引理 nnnorm_pow_le
  条件: (x : S) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_add, hn] using nnnorm_mul_le_max (x ^ n) x

@[to_additive]

Depends on / 依赖: nnnorm_mul_le_max, pow_add
-/
lemma nnnorm_pow_le (x : S) (n : Nat) :
    ‖x ^ n‖₊ <= ‖x‖₊ := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_add, hn] using nnnorm_mul_le_max (x ^ n) x

@[to_additive]
/--
lemma `norm_pow_le` / 引理 `norm_pow_le`

English:
lemma norm_pow_le
  given: (x : S) (n : Nat)
  proof: nnnorm_pow_le x n

@[to_additive]

中文:
引理 norm_pow_le
  条件: (x : S) (n : 自然数)
  证明: nnnorm_pow_le x n

@[to_additive]

Depends on / 依赖: nnnorm_pow_le
-/
lemma norm_pow_le (x : S) (n : Nat) :
    ‖x ^ n‖ <= ‖x‖ :=
  nnnorm_pow_le x n

@[to_additive]
/--
lemma `nnnorm_zpow_le` / 引理 `nnnorm_zpow_le`

English:
lemma nnnorm_zpow_le
  given: (x : S) (z : Int)
  proof: by
  cases z <;>
  simpa using nnnorm_pow_le _ _

@[to_additive]

中文:
引理 nnnorm_zpow_le
  条件: (x : S) (z : 整数)
  证明: by
  cases z <;>
  simpa using nnnorm_pow_le _ _

@[to_additive]

Depends on / 依赖: nnnorm_pow_le
-/
lemma nnnorm_zpow_le (x : S) (z : Int) :
    ‖x ^ z‖₊ <= ‖x‖₊ := by
  cases z <;>
  simpa using nnnorm_pow_le _ _

@[to_additive]
/--
lemma `norm_zpow_le` / 引理 `norm_zpow_le`

English:
lemma norm_zpow_le
  given: (x : S) (z : Int)
  proof: nnnorm_zpow_le x z

中文:
引理 norm_zpow_le
  条件: (x : S) (z : 整数)
  证明: nnnorm_zpow_le x z

Depends on / 依赖: nnnorm_zpow_le
-/
lemma norm_zpow_le (x : S) (z : Int) :
    ‖x ^ z‖ <= ‖x‖ :=
  nnnorm_zpow_le x z

section nonarch

variable (S)
/--
In a group with an ultrametric norm, open balls around 1 of positive radius are open subgroups.
-/
@[to_additive /-- In an additive group with an ultrametric norm, open balls around 0 of
positive radius are open subgroups. -/]
/--
Definition of `ball_openSubgroup` / `ball_openSubgroup` 的定义

English:
definition ball_openSubgroup
  signature: {r : Real} (hr : 0 < r)
  body: Metric.ball (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_ball, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans_lt (max_lt hx hy)
  one_mem' := Metric.mem_ball_self hr
  inv_mem' := by simp only [Metric.mem_ball, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := Metric.isOpen_ball

中文:
定义 ball_openSubgroup
  签名: {r : 实数} (hr : 0 < r)
  定义体: Metric.ball (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_ball, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans_lt (max_lt hx hy)
  one_mem' := Metric.mem_ball_self hr
  inv_mem' := by simp only [Metric.mem_ball, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := Metric.isOpen_ball

Depends on / 依赖: Metric, Metric.ball
-/
def ball_openSubgroup {r : Real} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.ball (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_ball, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans_lt (max_lt hx hy)
  one_mem' := Metric.mem_ball_self hr
  inv_mem' := by simp only [Metric.mem_ball, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := Metric.isOpen_ball

/--
In a group with an ultrametric norm, closed balls around 1 of positive radius are open subgroups.
-/
@[to_additive /-- In an additive group with an ultrametric norm, closed balls around 0 of positive
radius are open subgroups. -/]
/--
Definition of `closedBall_openSubgroup` / `closedBall_openSubgroup` 的定义

English:
definition closedBall_openSubgroup
  signature: {r : Real} (hr : 0 < r)
  body: Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

中文:
定义 closedBall_openSubgroup
  签名: {r : 实数} (hr : 0 < r)
  定义体: Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

Depends on / 依赖: Metric, Metric.closedBall, closedBall
-/
def closedBall_openSubgroup {r : Real} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

end nonarch

end Group

section CommGroup

variable {M ι : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- A commutative group with an ultrametric group seminorm is nonarchimedean (as a topological
group, i.e. every neighborhood of 1 contains an open subgroup). -/
@[to_additive /-- A commutative additive group with an ultrametric group seminorm is nonarchimedean
(as a topological group, i.e. every neighborhood of 0 contains an open subgroup). -/]
/--
Instance `nonarchimedeanGroup` / 实例 `nonarchimedeanGroup`

English:
instance nonarchimedeanGroup
  signature: : NonarchimedeanGroup M where
  body: by simpa only [Metric.mem_nhds_iff]
    using fun U ⟨ε, hεp, hεU⟩ => ⟨ball_openSubgroup M hεp, hεU⟩

中文:
实例 nonarchimedeanGroup
  签名: : Nonarchimedean群 M where
  定义体: by simpa only [Metric.mem_nhds_iff]
    using fun U ⟨ε, hεp, hεU⟩ => ⟨ball_openSubgroup M hεp, hεU⟩

Depends on / 依赖: Metric, Metric.mem_nhds_iff, ball_openSubgroup, mem_nhds_iff
-/
instance nonarchimedeanGroup : NonarchimedeanGroup M where
  is_nonarchimedean := by simpa only [Metric.mem_nhds_iff]
    using fun U ⟨ε, hεp, hεU⟩ => ⟨ball_openSubgroup M hεp, hεU⟩

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product.
This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not. -/
@[to_additive /-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the
sum. This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not. -/]
/--
lemma `_root_.Finset.Nonempty.norm_prod_le_sup'_norm` / 引理 `_root_.Finset.Nonempty.norm_prod_le_sup'_norm`

English:
lemma _root_.Finset.Nonempty.norm_prod_le_sup'_norm
  given: {s : Finset ι} (hs : s.Nonempty) (f : ι -> M)
  proof: by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.prod_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total ‖∏ i in t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_mul_le_max _ _).trans (max_eq_left h).le
· exact ⟨_, IH.choose_spec.left, (norm_mul_le_max _ _).trans
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

中文:
引理 _root_.有限集.非空.norm_prod_le_sup'_norm
  条件: {s : 有限集 ι} (hs : s.非空) (f : ι -> M)
  证明: by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.prod_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total ‖∏ i in t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_mul_le_max _ _).trans (max_eq_left h).le
· exact ⟨_, IH.choose_spec.left, (norm_mul_le_max _ _).trans
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.le_sup, Finset.mem_cons, Finset.mem_singleton, Finset.prod_cons, Finset.prod_singleton, IH.choose_spec.left, IH.choose_spec.right, Nonempty, _iff, choose_spec, cons_induction, exists_eq_left, exists_eq_or_imp, le.trans, le_refl, le_sup, le_total, max_eq_left
-/
lemma _root_.Finset.Nonempty.norm_prod_le_sup'_norm {s : Finset ι} (hs : s.Nonempty) (f : ι -> M) :
    ‖∏ i in s, f i‖ <= s.sup' hs (‖f ·‖) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.prod_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total ‖∏ i in t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_mul_le_max _ _).trans (max_eq_left h).le
· exact ⟨_, IH.choose_spec.left, (norm_mul_le_max _ _).trans
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

/-- Nonarchimedean norm of a product is less than or equal to the largest norm of a term in the
product. -/
@[to_additive /-- Nonarchimedean norm of a sum is less than or equal to the largest norm of a term
in the sum. -/]
/--
lemma `_root_.Finset.nnnorm_prod_le_sup_nnnorm` / 引理 `_root_.Finset.nnnorm_prod_le_sup_nnnorm`

English:
lemma _root_.Finset.nnnorm_prod_le_sup_nnnorm
  given: (s : Finset ι) (f : ι -> M)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using! hs.norm_prod_le_sup'_norm f

中文:
引理 _root_.有限集.nnnorm_prod_le_sup_nnnorm
  条件: (s : 有限集 ι) (f : ι -> M)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using! hs.norm_prod_le_sup'_norm f

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup, _eq_sup, _iff, _norm, coe_le_coe, coe_nnnorm, eq_empty_or_nonempty, hs.norm_prod_le_sup, le_sup, norm_prod_le_sup, s.eq_empty_or_nonempty
-/
lemma _root_.Finset.nnnorm_prod_le_sup_nnnorm (s : Finset ι) (f : ι -> M) :
    ‖∏ i in s, f i‖₊ <= s.sup (‖f ·‖₊) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using! hs.norm_prod_le_sup'_norm f

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for finite sums in additive
commutative groups with an ultrametric norm. -/]
/--
lemma `nnnorm_prod_le_of_forall_le` / 引理 `nnnorm_prod_le_of_forall_le`

English:
lemma nnnorm_prod_le_of_forall_le
  statement: {s : Finset ι} {f : ι -> M} {C : Real>=0}
  proof: (s.nnnorm_prod_le_sup_nnnorm f).trans Finset.sup_le hC

中文:
引理 nnnorm_prod_le_of_对任意_le
  结论: {s : 有限集 ι} {f : ι -> M} {C : 实数>=0}
  证明: (s.nnnorm_prod_le_sup_nnnorm f).trans Finset.sup_le hC

Depends on / 依赖: Finset, Finset.sup_le, nnnorm_prod_le_sup_nnnorm, s.nnnorm_prod_le_sup_nnnorm, sup_le
-/
lemma nnnorm_prod_le_of_forall_le {s : Finset ι} {f : ι -> M} {C : Real>=0}
    (hC : forall i in s, ‖f i‖₊ <= C) : ‖∏ i in s, f i‖₊ <= C :=
(s.nnnorm_prod_le_sup_nnnorm f).trans Finset.sup_le hC

/--
Generalised ultrametric triangle inequality for nonempty finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for nonempty finite sums in additive
commutative groups with an ultrametric norm. -/]
/--
lemma `norm_prod_le_of_forall_le_of_nonempty` / 引理 `norm_prod_le_of_forall_le_of_nonempty`

English:
lemma norm_prod_le_of_forall_le_of_nonempty
  statement: {s : Finset ι} (hs : s.Nonempty) {f : ι -> M} {C : Real}
  proof: (hs.norm_prod_le_sup'_norm f).trans (Finset.sup'_le hs _ hC)

中文:
引理 norm_prod_le_of_对任意_le_of_nonempty
  结论: {s : 有限集 ι} (hs : s.非空) {f : ι -> M} {C : 实数}
  证明: (hs.norm_prod_le_sup'_norm f).trans (Finset.sup'_le hs _ hC)

Depends on / 依赖: Finset, Finset.sup, _norm, hs.norm_prod_le_sup, norm_prod_le_sup
-/
lemma norm_prod_le_of_forall_le_of_nonempty {s : Finset ι} (hs : s.Nonempty) {f : ι -> M} {C : Real}
    (hC : forall i in s, ‖f i‖ <= C) : ‖∏ i in s, f i‖ <= C :=
  (hs.norm_prod_le_sup'_norm f).trans (Finset.sup'_le hs _ hC)

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for finite sums in additive
commutative groups with an ultrametric norm. -/]
/--
lemma `norm_prod_le_of_forall_le_of_nonneg` / 引理 `norm_prod_le_of_forall_le_of_nonneg`

English:
lemma norm_prod_le_of_forall_le_of_nonneg
  statement: {s : Finset ι} {f : ι -> M} {C : Real}
  proof: by
  lift C to NNReal using h_nonneg
  exact nnnorm_prod_le_of_forall_le hC

中文:
引理 norm_prod_le_of_对任意_le_of_nonneg
  结论: {s : 有限集 ι} {f : ι -> M} {C : 实数}
  证明: by
  lift C to NNReal using h_nonneg
  exact nnnorm_prod_le_of_forall_le hC

Depends on / 依赖: NNReal, h_nonneg, nnnorm_prod_le_of_forall_le
-/
lemma norm_prod_le_of_forall_le_of_nonneg {s : Finset ι} {f : ι -> M} {C : Real}
    (h_nonneg : 0 <= C) (hC : forall i in s, ‖f i‖ <= C) : ‖∏ i in s, f i‖ <= C := by
  lift C to NNReal using h_nonneg
  exact nnnorm_prod_le_of_forall_le hC

/--
Given a function `f : ι → M` and a nonempty finite set `t ⊆ ι`, we can always find `i ∈ t` such that
`‖∏ j in t, f j‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a nonempty finite set `t ⊆ ι`, we can always find
`i ∈ t` such that `‖∑ j ∈ t, f j‖ ≤ ‖f i‖`. -/]
/--
theorem `exists_norm_finsetProd_le_of_nonempty` / 定理 `exists_norm_finsetProd_le_of_nonempty`

English:
theorem exists_norm_finsetProd_le_of_nonempty
  given: {t : Finset ι} (ht : t.Nonempty) (f : ι -> M)
  proof: match t.exists_mem_eq_sup' ht (‖f ·‖) with
  | ⟨j, hj, hj'⟩ => ⟨j, hj, (ht.norm_prod_le_sup'_norm f).trans (le_of_eq hj')⟩

@[deprecated (since := "2026-04-08")]
alias exists_norm_finset_sum_le_of_nonempty := exists_norm_finsetSum_le_of_nonempty

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le_of_nonempty := exists_norm_finsetProd_le_of_nonempty

中文:
定理 存在_norm_finsetProd_le_of_nonempty
  条件: {t : 有限集 ι} (ht : t.非空) (f : ι -> M)
  证明: match t.exists_mem_eq_sup' ht (‖f ·‖) with
  | ⟨j, hj, hj'⟩ => ⟨j, hj, (ht.norm_prod_le_sup'_norm f).trans (le_of_eq hj')⟩

@[deprecated (since := "2026-04-08")]
alias exists_norm_finset_sum_le_of_nonempty := exists_norm_finsetSum_le_of_nonempty

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le_of_nonempty := exists_norm_finsetProd_le_of_nonempty

Depends on / 依赖: _norm, exists_mem_eq_sup, ht.norm_prod_le_sup, le_of_eq, norm_prod_le_sup, t.exists_mem_eq_sup
-/
theorem exists_norm_finsetProd_le_of_nonempty {t : Finset ι} (ht : t.Nonempty) (f : ι -> M) :
    exists i in t, ‖∏ j in t, f j‖ <= ‖f i‖ :=
  match t.exists_mem_eq_sup' ht (‖f ·‖) with
  | ⟨j, hj, hj'⟩ => ⟨j, hj, (ht.norm_prod_le_sup'_norm f).trans (le_of_eq hj')⟩

@[deprecated (since := "2026-04-08")]
alias exists_norm_finset_sum_le_of_nonempty := exists_norm_finsetSum_le_of_nonempty

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le_of_nonempty := exists_norm_finsetProd_le_of_nonempty

/--
Given a function `f : ι → M` and a finite set `t ⊆ ι`, we can always find `i : ι`, belonging to `t`
if `t` is nonempty, such that `‖∏ j ∈ t, f j‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a finite set `t ⊆ ι`, we can always find `i : ι`,
belonging to `t` if `t` is nonempty, such that `‖∑ j ∈ t, f j‖ ≤ ‖f i‖`. -/]
/--
theorem `exists_norm_finsetProd_le` / 定理 `exists_norm_finsetProd_le`

English:
theorem exists_norm_finsetProd_le
  given: (t : Finset ι) [Nonempty ι] (f : ι -> M)
  proof: by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩) exists_norm_finsetProd_le_of_nonempty ht f

@[deprecated (since := "2026-04-08")] alias exists_norm_finset_sum_le := exists_norm_finsetSum_le

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le := exists_norm_finsetProd_le

中文:
定理 存在_norm_finsetProd_le
  条件: (t : 有限集 ι) [非空 ι] (f : ι -> M)
  证明: by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩) exists_norm_finsetProd_le_of_nonempty ht f

@[deprecated (since := "2026-04-08")] alias exists_norm_finset_sum_le := exists_norm_finsetSum_le

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le := exists_norm_finsetProd_le

Depends on / 依赖: eq_empty_or_nonempty, exists_norm_finsetProd_le_of_nonempty, t.eq_empty_or_nonempty
-/
theorem exists_norm_finsetProd_le (t : Finset ι) [Nonempty ι] (f : ι -> M) :
    exists i : ι, (t.Nonempty -> i in t) ∧ ‖∏ j in t, f j‖ <= ‖f i‖ := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩) exists_norm_finsetProd_le_of_nonempty ht f

@[deprecated (since := "2026-04-08")] alias exists_norm_finset_sum_le := exists_norm_finsetSum_le

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le := exists_norm_finsetProd_le

/--
Given a function `f : ι → M` and a multiset `t : Multiset ι`, we can always find `i : ι`, belonging
to `t` if `t` is nonempty, such that `‖(s.map f).prod‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a multiset `t : Multiset ι`, we can always find
`i : ι`, belonging to `t` if `t` is nonempty, such that `‖(s.map f).sum‖ ≤ ‖f i‖`. -/]
/--
theorem `exists_norm_multiset_prod_le` / 定理 `exists_norm_multiset_prod_le`

English:
theorem exists_norm_multiset_prod_le
  given: (s : Multiset ι) [Nonempty ι] {f : ι -> M}
  proof: by
  inhabit ι
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases! hMa : ‖f M‖ <= ‖f a‖
      · refine ⟨a, by simp, ?_⟩
        · rw [Multiset.map_cons, Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le (le_refl _) (le_trans hM hMa))
      · rcases eq_or_ne t 0 with rfl | ht
        · exact ⟨a, by simp, by simp⟩
        · refine ⟨M, ?_, ?_⟩
          · simp [hMs ht]
          rw [Multiset.map_cons]; rw [Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le hMa.le hM)

@[to_additive]

中文:
定理 存在_norm_multiset_prod_le
  条件: (s : Multiset ι) [非空 ι] {f : ι -> M}
  证明: by
  inhabit ι
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases! hMa : ‖f M‖ <= ‖f a‖
      · refine ⟨a, by simp, ?_⟩
        · rw [Multiset.map_cons, Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le (le_refl _) (le_trans hM hMa))
      · rcases eq_or_ne t 0 with rfl | ht
        · exact ⟨a, by simp, by simp⟩
        · refine ⟨M, ?_, ?_⟩
          · simp [hMs ht]
          rw [Multiset.map_cons]; rw [Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le hMa.le hM)

@[to_additive]

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, eq_or_ne, hMa.le, induction_on, inhabit, le_refl, le_trans, map_cons, max_le, norm_mul_le_max, prod_cons
-/
theorem exists_norm_multiset_prod_le (s : Multiset ι) [Nonempty ι] {f : ι -> M} :
    exists i : ι, (s != 0 -> i in s) ∧ ‖(s.map f).prod‖ <= ‖f i‖ := by
  inhabit ι
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases! hMa : ‖f M‖ <= ‖f a‖
      · refine ⟨a, by simp, ?_⟩
        · rw [Multiset.map_cons, Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le (le_refl _) (le_trans hM hMa))
      · rcases eq_or_ne t 0 with rfl | ht
        · exact ⟨a, by simp, by simp⟩
        · refine ⟨M, ?_, ?_⟩
          · simp [hMs ht]
          rw [Multiset.map_cons]; rw [Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le hMa.le hM)

@[to_additive]
/--
lemma `norm_tprod_le` / 引理 `norm_tprod_le`

English:
lemma norm_tprod_le
  given: (f : ι -> M)
  statement: ‖∏' i, f i‖ <= ⨆ i, ‖f i‖
  proof: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Silly case #1 : the index type is empty
    simp only [tprod_empty, norm_one', Real.iSup_of_isEmpty, le_refl]
  by_cases h : Multipliable f; swap
  · -- Silly case #2 : the product is divergent
    rw [tprod_eq_one_of_not_multipliable h]; rw [norm_one']
    by_cases h_bd : BddAbove (Set.range fun i => ‖f i‖)
    · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
    · rw [Real.iSup_of_not_bddAbove h_bd]
  -- now the interesting case
  have h_bd : BddAbove (Set.range fun i => ‖f i‖) :=
    h.tendsto_cofinite_one.norm'.bddAbove_range_of_cofinite
  refine le_of_tendsto' h.hasProd.norm' (fun s => norm_prod_le_of_forall_le_of_nonneg ?_ ?_)
  · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
  · exact fun i _ => le_ciSup h_bd i

@[to_additive]

中文:
引理 norm_tprod_le
  条件: (f : ι -> M)
  结论: ‖∏' i, f i‖ <= ⨆ i, ‖f i‖
  证明: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Silly case #1 : the index type is empty
    simp only [tprod_empty, norm_one', Real.iSup_of_isEmpty, le_refl]
  by_cases h : Multipliable f; swap
  · -- Silly case #2 : the product is divergent
    rw [tprod_eq_one_of_not_multipliable h]; rw [norm_one']
    by_cases h_bd : BddAbove (Set.range fun i => ‖f i‖)
    · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
    · rw [Real.iSup_of_not_bddAbove h_bd]
  -- now the interesting case
  have h_bd : BddAbove (Set.range fun i => ‖f i‖) :=
    h.tendsto_cofinite_one.norm'.bddAbove_range_of_cofinite
  refine le_of_tendsto' h.hasProd.norm' (fun s => norm_prod_le_of_forall_le_of_nonneg ?_ ?_)
  · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
  · exact fun i _ => le_ciSup h_bd i

@[to_additive]

Depends on / 依赖: BddAbove, Multipliable, Real.iSup_of_isEmpty, Real.iSup_of_not_bddAbove, Set.range, divergent, h_bd, iSup_of_isEmpty, iSup_of_not_bddAbove, isEmpty_or_nonempty, le_ciSup_of_le, le_refl, norm_nonneg, norm_one, product, tprod_empty, tprod_eq_one_of_not_multipliable
-/
lemma norm_tprod_le (f : ι -> M) : ‖∏' i, f i‖ <= ⨆ i, ‖f i‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Silly case #1 : the index type is empty
    simp only [tprod_empty, norm_one', Real.iSup_of_isEmpty, le_refl]
  by_cases h : Multipliable f; swap
  · -- Silly case #2 : the product is divergent
    rw [tprod_eq_one_of_not_multipliable h]; rw [norm_one']
    by_cases h_bd : BddAbove (Set.range fun i => ‖f i‖)
    · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
    · rw [Real.iSup_of_not_bddAbove h_bd]
  -- now the interesting case
  have h_bd : BddAbove (Set.range fun i => ‖f i‖) :=
    h.tendsto_cofinite_one.norm'.bddAbove_range_of_cofinite
  refine le_of_tendsto' h.hasProd.norm' (fun s => norm_prod_le_of_forall_le_of_nonneg ?_ ?_)
  · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
  · exact fun i _ => le_ciSup h_bd i

@[to_additive]
/--
lemma `nnnorm_tprod_le` / 引理 `nnnorm_tprod_le`

English:
lemma nnnorm_tprod_le
  given: (f : ι -> M)
  statement: ‖∏' i, f i‖₊ <= ⨆ i, ‖f i‖₊
  proof: by
  simpa only [← NNReal.coe_le_coe, coe_nnnorm', coe_iSup] using norm_tprod_le f

@[to_additive]

中文:
引理 nnnorm_tprod_le
  条件: (f : ι -> M)
  结论: ‖∏' i, f i‖₊ <= ⨆ i, ‖f i‖₊
  证明: by
  simpa only [← NNReal.coe_le_coe, coe_nnnorm', coe_iSup] using norm_tprod_le f

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_iSup, coe_le_coe, coe_nnnorm, norm_tprod_le
-/
lemma nnnorm_tprod_le (f : ι -> M) : ‖∏' i, f i‖₊ <= ⨆ i, ‖f i‖₊ := by
  simpa only [← NNReal.coe_le_coe, coe_nnnorm', coe_iSup] using norm_tprod_le f

@[to_additive]
/--
lemma `norm_tprod_le_of_forall_le` / 引理 `norm_tprod_le_of_forall_le`

English:
lemma norm_tprod_le_of_forall_le
  given: [Nonempty ι] {f : ι -> M} {C : Real} (h : forall i, ‖f i‖ <= C)
  proof: (norm_tprod_le f).trans (ciSup_le h)

@[to_additive]

中文:
引理 norm_tprod_le_of_对任意_le
  条件: [非空 ι] {f : ι -> M} {C : 实数} (h : 对任意 i, ‖f i‖ <= C)
  证明: (norm_tprod_le f).trans (ciSup_le h)

@[to_additive]

Depends on / 依赖: ciSup_le, norm_tprod_le
-/
lemma norm_tprod_le_of_forall_le [Nonempty ι] {f : ι -> M} {C : Real} (h : forall i, ‖f i‖ <= C) :
    ‖∏' i, f i‖ <= C :=
  (norm_tprod_le f).trans (ciSup_le h)

@[to_additive]
/--
lemma `norm_tprod_le_of_forall_le_of_nonneg` / 引理 `norm_tprod_le_of_forall_le_of_nonneg`

English:
lemma norm_tprod_le_of_forall_le_of_nonneg
  given: {f : ι -> M} {C : Real} (hC : 0 <= C) (h : forall i, ‖f i‖ <= C)
  proof: by
  rcases isEmpty_or_nonempty ι
  · simpa only [tprod_empty, norm_one'] using hC
  · exact norm_tprod_le_of_forall_le h

@[to_additive]

中文:
引理 norm_tprod_le_of_对任意_le_of_nonneg
  条件: {f : ι -> M} {C : 实数} (hC : 0 <= C) (h : 对任意 i, ‖f i‖ <= C)
  证明: by
  rcases isEmpty_or_nonempty ι
  · simpa only [tprod_empty, norm_one'] using hC
  · exact norm_tprod_le_of_forall_le h

@[to_additive]

Depends on / 依赖: isEmpty_or_nonempty, norm_one, norm_tprod_le_of_forall_le, tprod_empty
-/
lemma norm_tprod_le_of_forall_le_of_nonneg {f : ι -> M} {C : Real} (hC : 0 <= C) (h : forall i, ‖f i‖ <= C) :
    ‖∏' i, f i‖ <= C := by
  rcases isEmpty_or_nonempty ι
  · simpa only [tprod_empty, norm_one'] using hC
  · exact norm_tprod_le_of_forall_le h

@[to_additive]
/--
lemma `nnnorm_tprod_le_of_forall_le` / 引理 `nnnorm_tprod_le_of_forall_le`

English:
lemma nnnorm_tprod_le_of_forall_le
  given: {f : ι -> M} {C : Real>=0} (h : forall i, ‖f i‖₊ <= C)
  statement: ‖∏' i, f i‖₊ <= C
  proof: (nnnorm_tprod_le f).trans (ciSup_le' h)

@[to_additive]

中文:
引理 nnnorm_tprod_le_of_对任意_le
  条件: {f : ι -> M} {C : 实数>=0} (h : 对任意 i, ‖f i‖₊ <= C)
  结论: ‖∏' i, f i‖₊ <= C
  证明: (nnnorm_tprod_le f).trans (ciSup_le' h)

@[to_additive]

Depends on / 依赖: ciSup_le, nnnorm_tprod_le
-/
lemma nnnorm_tprod_le_of_forall_le {f : ι -> M} {C : Real>=0} (h : forall i, ‖f i‖₊ <= C) : ‖∏' i, f i‖₊ <= C :=
  (nnnorm_tprod_le f).trans (ciSup_le' h)

@[to_additive]
/--
lemma `nnnorm_prod_eq_sup_of_pairwise_ne` / 引理 `nnnorm_prod_eq_sup_of_pairwise_ne`

English:
lemma nnnorm_prod_eq_sup_of_pairwise_ne
  statement: {s : Finset ι} {f : ι -> M}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    specialize IH (hs.mono (by simp))
    obtain ⟨j, hj, hj'⟩ : exists j in s, ‖∏ i in s, f i‖₊ = ‖f j‖₊ := by
      simpa [IH] using s.exists_mem_eq_sup hs' _
    suffices ‖f a‖₊ != ‖∏ x in s, f x‖₊ by simp [← IH, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm this]
    rw [hj']
    apply hs <;> grind

@[to_additive]

中文:
引理 nnnorm_prod_eq_sup_of_pairwise_ne
  结论: {s : 有限集 ι} {f : ι -> M}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    specialize IH (hs.mono (by simp))
    obtain ⟨j, hj, hj'⟩ : exists j in s, ‖∏ i in s, f i‖₊ = ‖f j‖₊ := by
      simpa [IH] using s.exists_mem_eq_sup hs' _
    suffices ‖f a‖₊ != ‖∏ x in s, f x‖₊ by simp [← IH, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm this]
    rw [hj']
    apply hs <;> grind

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, eq_empty_or_nonempty, exists_mem_eq_sup, hs.mono, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm, s.eq_empty_or_nonempty, s.exists_mem_eq_sup, specialize
-/
lemma nnnorm_prod_eq_sup_of_pairwise_ne {s : Finset ι} {f : ι -> M}
    (hs : Set.Pairwise s (fun i j => ‖f i‖₊ != ‖f j‖₊)) :
    ‖∏ i in s, f i‖₊ = s.sup (fun i => ‖f i‖₊) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    specialize IH (hs.mono (by simp))
    obtain ⟨j, hj, hj'⟩ : exists j in s, ‖∏ i in s, f i‖₊ = ‖f j‖₊ := by
      simpa [IH] using s.exists_mem_eq_sup hs' _
    suffices ‖f a‖₊ != ‖∏ x in s, f x‖₊ by simp [← IH, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm this]
    rw [hj']
    apply hs <;> grind

@[to_additive]
/--
lemma `norm_prod_eq_sup'_of_pairwise_ne` / 引理 `norm_prod_eq_sup'_of_pairwise_ne`

English:
lemma norm_prod_eq_sup'_of_pairwise_ne
  statement: {s : Finset ι} {f : ι -> M} (hs' : s.Nonempty)
  proof: by
  rw [← coe_nnnorm']; rw [nnnorm_prod_eq_sup_of_pairwise_ne]; rw [← Finset.sup'_eq_sup hs']
  · exact s.apply_sup'_eq_sup'_comp hs' _ (by tauto)
  · simpa [← NNReal.coe_inj] using hs

中文:
引理 norm_prod_eq_sup'_of_pairwise_ne
  结论: {s : 有限集 ι} {f : ι -> M} (hs' : s.非空)
  证明: by
  rw [← coe_nnnorm']; rw [nnnorm_prod_eq_sup_of_pairwise_ne]; rw [← Finset.sup'_eq_sup hs']
  · exact s.apply_sup'_eq_sup'_comp hs' _ (by tauto)
  · simpa [← NNReal.coe_inj] using hs

Depends on / 依赖: Finset, Finset.sup, NNReal, NNReal.coe_inj, _comp, _eq_sup, apply_sup, coe_inj, coe_nnnorm, nnnorm_prod_eq_sup_of_pairwise_ne, s.apply_sup
-/
lemma norm_prod_eq_sup'_of_pairwise_ne {s : Finset ι} {f : ι -> M} (hs' : s.Nonempty)
    (hs : Set.Pairwise s (fun i j => ‖f i‖ != ‖f j‖)) :
    ‖∏ i in s, f i‖ = s.sup' hs' (fun i => ‖f i‖) := by
  rw [← coe_nnnorm']; rw [nnnorm_prod_eq_sup_of_pairwise_ne]; rw [← Finset.sup'_eq_sup hs']
  · exact s.apply_sup'_eq_sup'_comp hs' _ (by tauto)
  · simpa [← NNReal.coe_inj] using hs

end CommGroup

end IsUltrametricDist
