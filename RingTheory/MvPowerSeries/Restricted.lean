/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.Antidiag.Tendsto
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/--
Definition of `IsRestricted` / `IsRestricted` 的定义

English:
definition IsRestricted
  signature: (c : σ -> Real) (f : MvPowerSeries σ R)
  body: Tendsto (fun (t : σ ->₀ Nat) => ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]

中文:
定义 IsRestricted
  签名: (c : σ -> 实数) (f : MvPowerSeries σ R)
  定义体: Tendsto (fun (t : σ ->₀ Nat) => ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]

Depends on / 依赖: Tendsto, cofinite, t.prod
-/
def IsRestricted (c : σ -> Real) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ ->₀ Nat) => ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
/--
lemma `isRestricted_abs_iff` / 引理 `isRestricted_abs_iff`

English:
lemma isRestricted_abs_iff
  given: (c : σ -> Real) (f : MvPowerSeries σ R)
  proof: by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

中文:
引理 isRestricted_abs_iff
  条件: (c : σ -> 实数) (f : MvPowerSeries σ R)
  证明: by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

Depends on / 依赖: Finsupp, Finsupp.prod, IsRestricted, NormedAddGroup, NormedAddGroup.tendsto_nhds_zero, tendsto_nhds_zero
-/
lemma isRestricted_abs_iff (c : σ -> Real) (f : MvPowerSeries σ R) :
    IsRestricted |c| f ↔ IsRestricted c f := by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

/--
lemma `isRestricted_zero` / 引理 `isRestricted_zero`

English:
lemma isRestricted_zero
  given: (c : σ -> Real)
  statement: IsRestricted c (0 : MvPowerSeries σ R)
  proof: by
  simpa [IsRestricted] using tendsto_const_nhds

中文:
引理 isRestricted_zero
  条件: (c : σ -> 实数)
  结论: IsRestricted c (0 : MvPowerSeries σ R)
  证明: by
  simpa [IsRestricted] using tendsto_const_nhds

Depends on / 依赖: IsRestricted, tendsto_const_nhds
-/
lemma isRestricted_zero (c : σ -> Real) : IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

/--
lemma `isRestricted_monomial` / 引理 `isRestricted_monomial`

English:
lemma isRestricted_monomial
  given: (c : σ -> Real) (n : σ ->₀ Nat) (a : R)
  proof: by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, coeff_monomial]

中文:
引理 isRestricted_monomial
  条件: (c : σ -> 实数) (n : σ ->₀ 自然数) (a : R)
  证明: by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, coeff_monomial]

Depends on / 依赖: Set.Subsingleton, Set.Subsingleton.finite, Subsingleton, classical, coeff_monomial, finite, tendsto_nhds_of_eventually_eq
-/
lemma isRestricted_monomial (c : σ -> Real) (n : σ ->₀ Nat) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, coeff_monomial]

/--
lemma `isRestricted_one` / 引理 `isRestricted_one`

English:
lemma isRestricted_one
  given: (c : σ -> Real)
  statement: IsRestricted c (1 : MvPowerSeries σ R)
  proof: isRestricted_monomial c 0 1

中文:
引理 isRestricted_one
  条件: (c : σ -> 实数)
  结论: IsRestricted c (1 : MvPowerSeries σ R)
  证明: isRestricted_monomial c 0 1

Depends on / 依赖: isRestricted_monomial
-/
lemma isRestricted_one (c : σ -> Real) : IsRestricted c (1 : MvPowerSeries σ R) :=
  isRestricted_monomial c 0 1

/--
lemma `isRestricted_C` / 引理 `isRestricted_C`

English:
lemma isRestricted_C
  given: (c : σ -> Real) (a : R)
  statement: IsRestricted c (C a)
  proof: by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

中文:
引理 isRestricted_C
  条件: (c : σ -> 实数) (a : R)
  结论: IsRestricted c (C a)
  证明: by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

Depends on / 依赖: isRestricted_monomial, monomial_zero_eq_C_apply
-/
lemma isRestricted_C (c : σ -> Real) (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

/--
lemma `isRestricted.add` / 引理 `isRestricted.add`

English:
lemma isRestricted.add
  statement: (c : σ -> Real) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
  proof: by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : Real) ▸ hf.add hg) (fun n => ?_) fun n => ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_a

中文:
引理 isRestricted.add
  结论: (c : σ -> 实数) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
  证明: by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : Real) ▸ hf.add hg) (fun n => ?_) fun n => ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_a

Depends on / 依赖: Finsupp, Finsupp.prod, IsRestricted, add_mul, add_zero, extension, hf.add, isRestricted_abs_iff, mul_le_mul_of_nonneg_right, norm_add_le, squeeze, tendsto_const_nhds, tendsto_const_nhds.squeeze
-/
lemma isRestricted.add (c : σ -> Real) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : Real) ▸ hf.add hg) (fun n => ?_) fun n => ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

/--
lemma `isRestricted.neg` / 引理 `isRestricted.neg`

English:
lemma isRestricted.neg
  given: (c : σ -> Real) {f : MvPowerSeries σ R} (hf : IsRestricted c f)
  proof: by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  simpa [IsRestricted] using hf

中文:
引理 isRestricted.neg
  条件: (c : σ -> 实数) {f : MvPowerSeries σ R} (hf : IsRestricted c f)
  证明: by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  simpa [IsRestricted] using hf

Depends on / 依赖: IsRestricted, isRestricted_abs_iff
-/
lemma isRestricted.neg (c : σ -> Real) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (-f) := by
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  simpa [IsRestricted] using hf

open IsUltrametricDist

open Finset.HasAntidiagonal in
/--
lemma `tendsto_antidiagonal` / 引理 `tendsto_antidiagonal`

English:
lemma tendsto_antidiagonal
  statement: {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
  proof: by
  wlog hC' : 0 <= C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofini

中文:
引理 tendsto_antidiagonal
  结论: {M S : 类型} [加法幺半群 M] [有限集.有Antidiagonal M] [赋范环 S]
  证明: by
  wlog hC' : 0 <= C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofini

Depends on / 依赖: Finset, Finset.sup, _antidiagonal_cofinite, _mono_fun, _norm, generalizing, hf.norm, hg.norm, mul_nonneg, nonempty_antidiagonal, norm_sum_le_sup, squeeze, tendsto_const_nhds, tendsto_mul_cofinite_nhds_zero, tendsto_sup, tendsto_zero_iff_norm_tendsto_zero
-/
lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M -> Real} (hC : forall a b, C (a + b) = C a * C b) {f g : M -> S}
    (hf : Tendsto (fun i => ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i => ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a => ‖∑ p in Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 <= C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x => mul_nonneg (by simp) (hC' x)) fun a => ?_
  have : 0 <= C a := hC' a
  grw [(nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx => ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]

/--
lemma `isRestricted.mul` / 引理 `isRestricted.mul`

English:
lemma isRestricted.mul
  statement: [IsUltrametricDist R] (c : σ -> Real) {f g : MvPowerSeries σ R}
  proof: by
  classical
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

中文:
引理 isRestricted.mul
  结论: [是UltrametricDist R] (c : σ -> 实数) {f g : MvPowerSeries σ R}
  证明: by
  classical
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

Depends on / 依赖: Finsupp, Finsupp.prod_add_index, IsRestricted, classical, isRestricted_abs_iff, pow_add, prod_add_index, tendsto_antidiagonal
-/
lemma isRestricted.mul [IsUltrametricDist R] (c : σ -> Real) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  rw [← isRestricted_abs_iff]; rw [IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

namespace IsRestricted

/--
Definition of `addSubgroup` / `addSubgroup` 的定义

English:
definition addSubgroup
  signature: (c : σ -> Real)
  body: {f | IsRestricted c f}
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

中文:
定义 addSubgroup
  签名: (c : σ -> 实数)
  定义体: {f | IsRestricted c f}
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c
-/
protected def addSubgroup (c : σ -> Real) : AddSubgroup (MvPowerSeries σ R) where
  carrier := {f | IsRestricted c f}
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

variable [IsUltrametricDist R]

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: (c : σ -> Real)
  body: IsRestricted.addSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

中文:
定义 subring
  签名: (c : σ -> 实数)
  定义体: IsRestricted.addSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c
-/
protected def subring (c : σ -> Real) : Subring (MvPowerSeries σ R) where
  __ := IsRestricted.addSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

end MvPowerSeries.IsRestricted
