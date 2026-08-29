/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weightedVSubOfPoint` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weightedVSub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affineCombination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `Finset`; versions for a
`Fintype` may be obtained using `Finset.univ`, while versions for a
`Finsupp` may be obtained using `Finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section


noncomputable section

open Affine

namespace Finset

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [S : AffineSpace V P]
variable {ι : Type*} (s : Finset ι)
variable {ι₂ : Type*} (s₂ : Finset ι₂)

/--
Definition of `weightedVSubOfPoint` / `weightedVSubOfPoint` 的定义

English:
definition weightedVSubOfPoint
  signature: (p : ι -> P) (b : P)
  body: ∑ i in s, (LinearMap.proj i : (ι -> k) ->ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]

中文:
定义 weightedVSubOfPoint
  签名: (p : ι -> P) (b : P)
  定义体: ∑ i in s, (LinearMap.proj i : (ι -> k) ->ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.proj, smulRight
-/
def weightedVSubOfPoint (p : ι -> P) (b : P) : (ι -> k) ->ₗ[k] V :=
  ∑ i in s, (LinearMap.proj i : (ι -> k) ->ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]
/--
theorem `weightedVSubOfPoint_apply` / 定理 `weightedVSubOfPoint_apply`

English:
theorem weightedVSubOfPoint_apply
  given: (w : ι -> k) (p : ι -> P) (b : P)
  proof: by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]

中文:
定理 weightedVSubOfPoint_apply
  条件: (w : ι -> k) (p : ι -> P) (b : P)
  证明: by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]

Depends on / 依赖: LinearMap, LinearMap.sum_apply, sum_apply, weightedVSubOfPoint
-/
theorem weightedVSubOfPoint_apply (w : ι -> k) (p : ι -> P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b) := by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]

/-- The value of `weightedVSubOfPoint`, where the given points are equal. -/
@[simp (high)]
/--
theorem `weightedVSubOfPoint_apply_const` / 定理 `weightedVSubOfPoint_apply_const`

English:
theorem weightedVSubOfPoint_apply_const
  given: (w : ι -> k) (p : P) (b : P)
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [sum_smul]

中文:
定理 weightedVSubOfPoint_apply_const
  条件: (w : ι -> k) (p : P) (b : P)
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [sum_smul]

Depends on / 依赖: sum_smul, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_apply_const (w : ι -> k) (p : P) (b : P) :
    s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in s, w i) • (p -ᵥ b) := by
  rw [weightedVSubOfPoint_apply]; rw [sum_smul]

/--
lemma `weightedVSubOfPoint_vadd` / 引理 `weightedVSubOfPoint_vadd`

English:
lemma weightedVSubOfPoint_vadd
  given: (s : Finset ι) (w : ι -> k) (p : ι -> P) (b : P) (v : V)
  proof: by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

中文:
引理 weightedVSubOfPoint_vadd
  条件: (s : 有限集 ι) (w : ι -> k) (p : ι -> P) (b : P) (v : V)
  证明: by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

Depends on / 依赖: add_comm, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub
-/
lemma weightedVSubOfPoint_vadd (s : Finset ι) (w : ι -> k) (p : ι -> P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

/--
lemma `weightedVSubOfPoint_smul` / 引理 `weightedVSubOfPoint_smul`

English:
lemma weightedVSubOfPoint_smul
  statement: {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
  proof: by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

中文:
引理 weightedVSubOfPoint_smul
  结论: {G : 类型} [群 G] [分配乘法作用 G V] [标量交换类 G k V]
  证明: by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

Depends on / 依赖: smul_comm, smul_sub, smul_sum
-/
lemma weightedVSubOfPoint_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    (s : Finset ι) (w : ι -> k) (p : ι -> V) (b : V) (a : G) :
    s.weightedVSubOfPoint (a • p) b w = a • s.weightedVSubOfPoint p (a⁻¹ • b) w := by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

/--
theorem `weightedVSubOfPoint_congr` / 定理 `weightedVSubOfPoint_congr`

English:
theorem weightedVSubOfPoint_congr
  statement: {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  proof: by
  simp_rw [weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi]; rw [hp i hi]

中文:
定理 weightedVSubOfPoint_congr
  结论: {w₁ w₂ : ι -> k} (hw : 对任意 i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  证明: by
  simp_rw [weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi]; rw [hp i hi]

Depends on / 依赖: simp_rw, sum_congr, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
    (hp : forall i in s, p₁ i = p₂ i) (b : P) :
    s.weightedVSubOfPoint p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂ := by
  simp_rw [weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi]; rw [hp i hi]

/--
theorem `weightedVSubOfPoint_eq_of_weights_eq` / 定理 `weightedVSubOfPoint_eq_of_weights_eq`

English:
theorem weightedVSubOfPoint_eq_of_weights_eq
  statement: (p : ι -> P) (j : ι) (w₁ w₂ : ι -> k)
  proof: by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

中文:
定理 weightedVSubOfPoint_eq_of_weights_eq
  结论: (p : ι -> P) (j : ι) (w₁ w₂ : ι -> k)
  证明: by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

Depends on / 依赖: Finset, Finset.weightedVSubOfPoint_apply, eq_or_ne, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_eq_of_weights_eq (p : ι -> P) (j : ι) (w₁ w₂ : ι -> k)
    (hw : forall i, i != j -> w₁ i = w₂ i) :
    s.weightedVSubOfPoint p (p j) w₁ = s.weightedVSubOfPoint p (p j) w₂ := by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

/--
theorem `weightedVSubOfPoint_eq_of_sum_eq_zero` / 定理 `weightedVSubOfPoint_eq_of_sum_eq_zero`

English:
theorem weightedVSubOfPoint_eq_of_sum_eq_zero
  statement: (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 0)
  proof: by
  apply eq_of_sub_eq_zero
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub]; rw [vsub_sub_vsub_cancel_left]
  rw [← sum_smul]; rw [h]; rw [zero_smul]

中文:
定理 weightedVSubOfPoint_eq_of_sum_eq_zero
  结论: (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 0)
  证明: by
  apply eq_of_sub_eq_zero
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub]; rw [vsub_sub_vsub_cancel_left]
  rw [← sum_smul]; rw [h]; rw [zero_smul]

Depends on / 依赖: conv_lhs, eq_of_sub_eq_zero, smul_sub, sum_smul, sum_sub_distrib, vsub_sub_vsub_cancel_left, weightedVSubOfPoint_apply, zero_smul
-/
theorem weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 0)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint p b₂ w := by
  apply eq_of_sub_eq_zero
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub]; rw [vsub_sub_vsub_cancel_left]
  rw [← sum_smul]; rw [h]; rw [zero_smul]

/--
theorem `weightedVSubOfPoint_vadd_eq_of_sum_eq_one` / 定理 `weightedVSubOfPoint_vadd_eq_of_sum_eq_one`

English:
theorem weightedVSubOfPoint_vadd_eq_of_sum_eq_one
  statement: (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 1)
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq_vsub_sub]; rw [← add_sub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [←
    sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      

中文:
定理 weightedVSubOfPoint_vadd_eq_of_sum_eq_one
  结论: (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 1)
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq_vsub_sub]; rw [← add_sub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [←
    sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      

Depends on / 依赖: add_comm, add_sub_assoc, conv_lhs, one_smul, smul_sub, sum_smul, sum_sub_distrib, vadd_vsub_assoc, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_self, vsub_sub_vsub_cancel_left, vsub_vadd_eq_vsub_sub, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_vadd_eq_of_sum_eq_one (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 1)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁ = s.weightedVSubOfPoint p b₂ w +ᵥ b₂ := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq_vsub_sub]; rw [← add_sub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [←
    sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      · ext
        rw [← smul_sub]; rw [vsub_sub_vsub_cancel_left]
  rw [← sum_smul]; rw [h]; rw [one_smul]; rw [vsub_add_vsub_cancel]; rw [vsub_self]

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp (high)]
/--
theorem `weightedVSubOfPoint_erase` / 定理 `weightedVSubOfPoint_erase`

English:
theorem weightedVSubOfPoint_erase
  given: [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι)
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_erase
  rw [vsub_self]; rw [smul_zero]

中文:
定理 weightedVSubOfPoint_erase
  条件: [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι)
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_erase
  rw [vsub_self]; rw [smul_zero]

Depends on / 依赖: smul_zero, sum_erase, vsub_self, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_erase [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι) :
    (s.erase i).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_erase
  rw [vsub_self]; rw [smul_zero]

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp (high)]
/--
theorem `weightedVSubOfPoint_insert` / 定理 `weightedVSubOfPoint_insert`

English:
theorem weightedVSubOfPoint_insert
  given: [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι)
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self]; rw [smul_zero]

中文:
定理 weightedVSubOfPoint_insert
  条件: [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι)
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self]; rw [smul_zero]

Depends on / 依赖: smul_zero, sum_insert_zero, vsub_self, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_insert [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι) :
    (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self]; rw [smul_zero]

/--
theorem `weightedVSubOfPoint_indicator_subset` / 定理 `weightedVSubOfPoint_indicator_subset`

English:
theorem weightedVSubOfPoint_indicator_subset
  statement: (w : ι -> k) (p : ι -> P) (b : P) {s₁ s₂ : Finset ι}
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
exact Eq.symm
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

中文:
定理 weightedVSubOfPoint_indicator_subset
  结论: (w : ι -> k) (p : ι -> P) (b : P) {s₁ s₂ : 有限集 ι}
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
exact Eq.symm
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

Depends on / 依赖: Eq.symm, sum_indicator_subset_of_eq_zero, weightedVSubOfPoint_apply, zero_smul
-/
theorem weightedVSubOfPoint_indicator_subset (w : ι -> k) (p : ι -> P) (b : P) {s₁ s₂ : Finset ι}
    (h : s₁ subseteq s₂) :
    s₁.weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint p b (Set.indicator (↑s₁) w) := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]
exact Eq.symm
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

/--
theorem `weightedVSubOfPoint_map` / 定理 `weightedVSubOfPoint_map`

English:
theorem weightedVSubOfPoint_map
  given: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) (b : P)
  proof: by
  simp_rw [weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

中文:
定理 weightedVSubOfPoint_map
  条件: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) (b : P)
  证明: by
  simp_rw [weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

Depends on / 依赖: Finset, Finset.sum_map, simp_rw, sum_map, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) (b : P) :
    (s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e) := by
  simp_rw [weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

/--
theorem `sum_smul_vsub_eq_weightedVSubOfPoint_sub` / 定理 `sum_smul_vsub_eq_weightedVSubOfPoint_sub`

English:
theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub
  given: (w : ι -> k) (p₁ p₂ : ι -> P) (b : P)
  proof: by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

中文:
定理 sum_smul_vsub_eq_weightedVSubOfPoint_sub
  条件: (w : ι -> k) (p₁ p₂ : ι -> P) (b : P)
  证明: by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

Depends on / 依赖: simp_rw, smul_sub, sum_sub_distrib, vsub_sub_vsub_cancel_right, weightedVSubOfPoint_apply
-/
theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b : P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) =
      s.weightedVSubOfPoint p₁ b w - s.weightedVSubOfPoint p₂ b w := by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

/--
theorem `sum_smul_vsub_const_eq_weightedVSubOfPoint_sub` / 定理 `sum_smul_vsub_const_eq_weightedVSubOfPoint_sub`

English:
theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub
  given: (w : ι -> k) (p₁ : ι -> P) (p₂ b : P)
  proof: by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

中文:
定理 sum_smul_vsub_const_eq_weightedVSubOfPoint_sub
  条件: (w : ι -> k) (p₁ : ι -> P) (p₂ b : P)
  证明: by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

Depends on / 依赖: sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const
-/
theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι -> k) (p₁ : ι -> P) (p₂ b : P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i in s, w i) • (p₂ -ᵥ b) := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

/--
theorem `sum_smul_const_vsub_eq_sub_weightedVSubOfPoint` / 定理 `sum_smul_const_vsub_eq_sub_weightedVSubOfPoint`

English:
theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint
  given: (w : ι -> k) (p₂ : ι -> P) (p₁ b : P)
  proof: by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

中文:
定理 sum_smul_const_vsub_eq_sub_weightedVSubOfPoint
  条件: (w : ι -> k) (p₂ : ι -> P) (p₁ b : P)
  证明: by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

Depends on / 依赖: sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const
-/
theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι -> k) (p₂ : ι -> P) (p₁ b : P) :
    (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = (∑ i in s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub]; rw [weightedVSubOfPoint_apply_const]

/--
theorem `weightedVSubOfPoint_sdiff` / 定理 `weightedVSubOfPoint_sdiff`

English:
theorem weightedVSubOfPoint_sdiff
  statement: [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
  proof: by
  simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]

中文:
定理 weightedVSubOfPoint_sdiff
  结论: [DecidableEq ι] {s₂ : 有限集 ι} (h : s₂ subseteq s) (w : ι -> k)
  证明: by
  simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]

Depends on / 依赖: simp_rw, sum_sdiff, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
    (p : ι -> P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w + s₂.weightedVSubOfPoint p b w =
      s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]

/--
theorem `weightedVSubOfPoint_sdiff_sub` / 定理 `weightedVSubOfPoint_sdiff_sub`

English:
theorem weightedVSubOfPoint_sdiff_sub
  statement: [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
  proof: by
  rw [map_neg]; rw [sub_neg_eq_add]; rw [s.weightedVSubOfPoint_sdiff h]

中文:
定理 weightedVSubOfPoint_sdiff_sub
  结论: [DecidableEq ι] {s₂ : 有限集 ι} (h : s₂ subseteq s) (w : ι -> k)
  证明: by
  rw [map_neg]; rw [sub_neg_eq_add]; rw [s.weightedVSubOfPoint_sdiff h]

Depends on / 依赖: map_neg, s.weightedVSubOfPoint_sdiff, sub_neg_eq_add, weightedVSubOfPoint_sdiff
-/
theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
    (p : ι -> P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w := by
  rw [map_neg]; rw [sub_neg_eq_add]; rw [s.weightedVSubOfPoint_sdiff h]

/--
theorem `weightedVSubOfPoint_subtype_eq_filter` / 定理 `weightedVSubOfPoint_subtype_eq_filter`

English:
theorem weightedVSubOfPoint_subtype_eq_filter
  statement: (w : ι -> k) (p : ι -> P) (b : P) (pred : ι -> Prop)
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_subtype_eq_sum_filter]

中文:
定理 weightedVSubOfPoint_subtype_eq_filter
  结论: (w : ι -> k) (p : ι -> P) (b : P) (pred : ι -> 命题)
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_subtype_eq_sum_filter]

Depends on / 依赖: sum_subtype_eq_sum_filter, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_subtype_eq_filter (w : ι -> k) (p : ι -> P) (b : P) (pred : ι -> Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSubOfPoint (fun i => p i) b fun i => w i) =
      {x in s | pred x}.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [← sum_subtype_eq_sum_filter]

/--
theorem `weightedVSubOfPoint_filter_of_ne` / 定理 `weightedVSubOfPoint_filter_of_ne`

English:
theorem weightedVSubOfPoint_filter_of_ne
  statement: (w : ι -> k) (p : ι -> P) (b : P) {pred : ι -> Prop}
  proof: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

中文:
定理 weightedVSubOfPoint_filter_of_ne
  结论: (w : ι -> k) (p : ι -> P) (b : P) {pred : ι -> 命题}
  证明: by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

Depends on / 依赖: sum_filter_of_ne, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_filter_of_ne (w : ι -> k) (p : ι -> P) (b : P) {pred : ι -> Prop}
    [DecidablePred pred] (h : forall i in s, w i != 0 -> pred i) :
    {x in s | pred x}.weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply]; rw [weightedVSubOfPoint_apply]; rw [sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

/--
theorem `weightedVSubOfPoint_const_smul` / 定理 `weightedVSubOfPoint_const_smul`

English:
theorem weightedVSubOfPoint_const_smul
  given: (w : ι -> k) (p : ι -> P) (b : P) (c : k)
  proof: by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

中文:
定理 weightedVSubOfPoint_const_smul
  条件: (w : ι -> k) (p : ι -> P) (b : P) (c : k)
  证明: by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

Depends on / 依赖: Pi.smul_apply, simp_rw, smul_apply, smul_eq_mul, smul_smul, smul_sum, weightedVSubOfPoint_apply
-/
theorem weightedVSubOfPoint_const_smul (w : ι -> k) (p : ι -> P) (b : P) (c : k) :
    s.weightedVSubOfPoint p b (c • w) = c • s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

/--
Definition of `weightedVSub` / `weightedVSub` 的定义

English:
definition weightedVSub
  signature: (p : ι -> P)
  body: s.weightedVSubOfPoint p (Classical.choice S.nonempty)

中文:
定义 weightedVSub
  签名: (p : ι -> P)
  定义体: s.weightedVSubOfPoint p (Classical.choice S.nonempty)

Depends on / 依赖: Classical, Classical.choice, S.nonempty, choice, nonempty, s.weightedVSubOfPoint, weightedVSubOfPoint
-/
def weightedVSub (p : ι -> P) : (ι -> k) ->ₗ[k] V :=
  s.weightedVSubOfPoint p (Classical.choice S.nonempty)

/--
theorem `weightedVSub_apply` / 定理 `weightedVSub_apply`

English:
theorem weightedVSub_apply
  given: (w : ι -> k) (p : ι -> P)
  proof: by
  simp [weightedVSub]

中文:
定理 weightedVSub_apply
  条件: (w : ι -> k) (p : ι -> P)
  证明: by
  simp [weightedVSub]

Depends on / 依赖: weightedVSub
-/
theorem weightedVSub_apply (w : ι -> k) (p : ι -> P) :
    s.weightedVSub p w = ∑ i in s, w i • (p i -ᵥ Classical.choice S.nonempty) := by
  simp [weightedVSub]

/--
theorem `weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` / 定理 `weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`

English:
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
  statement: (w : ι -> k) (p : ι -> P)
  proof: s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

中文:
定理 weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
  结论: (w : ι -> k) (p : ι -> P)
  证明: s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

Depends on / 依赖: s.weightedVSubOfPoint_eq_of_sum_eq_zero, weightedVSubOfPoint_eq_of_sum_eq_zero
-/
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P)
    (h : ∑ i in s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w :=
  s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

/-- The value of `weightedVSub`, where the given points are equal and the sum of the weights
is 0. -/
@[simp]
/--
theorem `weightedVSub_apply_const` / 定理 `weightedVSub_apply_const`

English:
theorem weightedVSub_apply_const
  given: (w : ι -> k) (p : P) (h : ∑ i in s, w i = 0)
  proof: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_apply_const]; rw [h]; rw [zero_smul]

中文:
定理 weightedVSub_apply_const
  条件: (w : ι -> k) (p : P) (h : ∑ i in s, w i = 0)
  证明: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_apply_const]; rw [h]; rw [zero_smul]

Depends on / 依赖: weightedVSub, weightedVSubOfPoint_apply_const, zero_smul
-/
theorem weightedVSub_apply_const (w : ι -> k) (p : P) (h : ∑ i in s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  rw [weightedVSub]; rw [weightedVSubOfPoint_apply_const]; rw [h]; rw [zero_smul]

/-- The `weightedVSub` for an empty set is 0. -/
@[simp]
/--
theorem `weightedVSub_empty` / 定理 `weightedVSub_empty`

English:
theorem weightedVSub_empty
  given: (w : ι -> k) (p : ι -> P)
  statement: (∅ : Finset ι).weightedVSub p w = (0 : V)
  proof: by
  simp [weightedVSub_apply]

中文:
定理 weightedVSub_empty
  条件: (w : ι -> k) (p : ι -> P)
  结论: (∅ : 有限集 ι).weightedVSub p w = (0 : V)
  证明: by
  simp [weightedVSub_apply]

Depends on / 依赖: weightedVSub_apply
-/
theorem weightedVSub_empty (w : ι -> k) (p : ι -> P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [weightedVSub_apply]

/--
lemma `weightedVSub_vadd` / 引理 `weightedVSub_vadd`

English:
lemma weightedVSub_vadd
  given: {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> P) (v : V)
  proof: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_vadd]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

中文:
引理 weightedVSub_vadd
  条件: {s : 有限集 ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> P) (v : V)
  证明: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_vadd]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

Depends on / 依赖: weightedVSub, weightedVSubOfPoint_vadd, weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
-/
lemma weightedVSub_vadd {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  rw [weightedVSub]; rw [weightedVSubOfPoint_vadd]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

/--
lemma `weightedVSub_smul` / 引理 `weightedVSub_smul`

English:
lemma weightedVSub_smul
  statement: {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
  proof: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_smul]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

中文:
引理 weightedVSub_smul
  结论: {G : 类型} [群 G] [分配乘法作用 G V] [标量交换类 G k V]
  证明: by
  rw [weightedVSub]; rw [weightedVSubOfPoint_smul]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

Depends on / 依赖: weightedVSub, weightedVSubOfPoint_smul, weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
-/
lemma weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> V) (a : G) :
    s.weightedVSub (a • p) w = a • s.weightedVSub p w := by
  rw [weightedVSub]; rw [weightedVSubOfPoint_smul]; rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

/--
theorem `weightedVSub_congr` / 定理 `weightedVSub_congr`

English:
theorem weightedVSub_congr
  statement: {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  proof: s.weightedVSubOfPoint_congr hw hp _

中文:
定理 weightedVSub_congr
  结论: {w₁ w₂ : ι -> k} (hw : 对任意 i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  证明: s.weightedVSubOfPoint_congr hw hp _

Depends on / 依赖: s.weightedVSubOfPoint_congr, weightedVSubOfPoint_congr
-/
theorem weightedVSub_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
    (hp : forall i in s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weightedVSub p₂ w₂ :=
  s.weightedVSubOfPoint_congr hw hp _

/--
theorem `weightedVSub_indicator_subset` / 定理 `weightedVSub_indicator_subset`

English:
theorem weightedVSub_indicator_subset
  given: (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂)
  proof: weightedVSubOfPoint_indicator_subset _ _ _ h

中文:
定理 weightedVSub_indicator_subset
  条件: (w : ι -> k) (p : ι -> P) {s₁ s₂ : 有限集 ι} (h : s₁ subseteq s₂)
  证明: weightedVSubOfPoint_indicator_subset _ _ _ h

Depends on / 依赖: weightedVSubOfPoint_indicator_subset
-/
theorem weightedVSub_indicator_subset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) :=
  weightedVSubOfPoint_indicator_subset _ _ _ h

/--
theorem `weightedVSub_map` / 定理 `weightedVSub_map`

English:
theorem weightedVSub_map
  given: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P)
  proof: s₂.weightedVSubOfPoint_map _ _ _ _

中文:
定理 weightedVSub_map
  条件: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P)
  证明: s₂.weightedVSubOfPoint_map _ _ _ _

Depends on / 依赖: weightedVSubOfPoint_map
-/
theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) :=
  s₂.weightedVSubOfPoint_map _ _ _ _

/--
theorem `sum_smul_vsub_eq_weightedVSub_sub` / 定理 `sum_smul_vsub_eq_weightedVSub_sub`

English:
theorem sum_smul_vsub_eq_weightedVSub_sub
  given: (w : ι -> k) (p₁ p₂ : ι -> P)
  proof: s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

中文:
定理 sum_smul_vsub_eq_weightedVSub_sub
  条件: (w : ι -> k) (p₁ p₂ : ι -> P)
  证明: s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

Depends on / 依赖: s.sum_smul_vsub_eq_weightedVSubOfPoint_sub, sum_smul_vsub_eq_weightedVSubOfPoint_sub
-/
theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι -> k) (p₁ p₂ : ι -> P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w :=
  s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/--
theorem `sum_smul_vsub_const_eq_weightedVSub` / 定理 `sum_smul_vsub_const_eq_weightedVSub`

English:
theorem sum_smul_vsub_const_eq_weightedVSub
  statement: (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
  proof: by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [sub_zero]

中文:
定理 sum_smul_vsub_const_eq_weightedVSub
  结论: (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
  证明: by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [sub_zero]

Depends on / 依赖: s.weightedVSub_apply_const, sub_zero, sum_smul_vsub_eq_weightedVSub_sub, weightedVSub_apply_const
-/
theorem sum_smul_vsub_const_eq_weightedVSub (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
    (h : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [sub_zero]

/--
theorem `sum_smul_const_vsub_eq_neg_weightedVSub` / 定理 `sum_smul_const_vsub_eq_neg_weightedVSub`

English:
theorem sum_smul_const_vsub_eq_neg_weightedVSub
  statement: (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
  proof: by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [zero_sub]

中文:
定理 sum_smul_const_vsub_eq_neg_weightedVSub
  结论: (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
  证明: by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [zero_sub]

Depends on / 依赖: s.weightedVSub_apply_const, sum_smul_vsub_eq_weightedVSub_sub, weightedVSub_apply_const, zero_sub
-/
theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
    (h : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub]; rw [s.weightedVSub_apply_const _ _ h]; rw [zero_sub]

/--
theorem `weightedVSub_sdiff` / 定理 `weightedVSub_sdiff`

English:
theorem weightedVSub_sdiff
  given: [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P)
  proof: s.weightedVSubOfPoint_sdiff h _ _ _

中文:
定理 weightedVSub_sdiff
  条件: [DecidableEq ι] {s₂ : 有限集 ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P)
  证明: s.weightedVSubOfPoint_sdiff h _ _ _

Depends on / 依赖: s.weightedVSubOfPoint_sdiff, weightedVSubOfPoint_sdiff
-/
theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff h _ _ _

/--
theorem `weightedVSub_sdiff_sub` / 定理 `weightedVSub_sdiff_sub`

English:
theorem weightedVSub_sdiff_sub
  statement: [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
  proof: s.weightedVSubOfPoint_sdiff_sub h _ _ _

中文:
定理 weightedVSub_sdiff_sub
  结论: [DecidableEq ι] {s₂ : 有限集 ι} (h : s₂ subseteq s) (w : ι -> k)
  证明: s.weightedVSubOfPoint_sdiff_sub h _ _ _

Depends on / 依赖: s.weightedVSubOfPoint_sdiff_sub, weightedVSubOfPoint_sdiff_sub
-/
theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
    (p : ι -> P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff_sub h _ _ _

/--
theorem `weightedVSub_subtype_eq_filter` / 定理 `weightedVSub_subtype_eq_filter`

English:
theorem weightedVSub_subtype_eq_filter
  statement: (w : ι -> k) (p : ι -> P) (pred : ι -> Prop)
  proof: s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _

中文:
定理 weightedVSub_subtype_eq_filter
  结论: (w : ι -> k) (p : ι -> P) (pred : ι -> 命题)
  证明: s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _

Depends on / 依赖: s.weightedVSubOfPoint_subtype_eq_filter, weightedVSubOfPoint_subtype_eq_filter
-/
theorem weightedVSub_subtype_eq_filter (w : ι -> k) (p : ι -> P) (pred : ι -> Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSub (fun i => p i) fun i => w i) =
      {x in s | pred x}.weightedVSub p w :=
  s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _

/--
theorem `weightedVSub_filter_of_ne` / 定理 `weightedVSub_filter_of_ne`

English:
theorem weightedVSub_filter_of_ne
  statement: (w : ι -> k) (p : ι -> P) {pred : ι -> Prop} [DecidablePred pred]
  proof: s.weightedVSubOfPoint_filter_of_ne _ _ _ h

中文:
定理 weightedVSub_filter_of_ne
  结论: (w : ι -> k) (p : ι -> P) {pred : ι -> 命题} [DecidablePred pred]
  证明: s.weightedVSubOfPoint_filter_of_ne _ _ _ h

Depends on / 依赖: s.weightedVSubOfPoint_filter_of_ne, weightedVSubOfPoint_filter_of_ne
-/
theorem weightedVSub_filter_of_ne (w : ι -> k) (p : ι -> P) {pred : ι -> Prop} [DecidablePred pred]
    (h : forall i in s, w i != 0 -> pred i) : {x in s | pred x}.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_filter_of_ne _ _ _ h

/--
theorem `weightedVSub_const_smul` / 定理 `weightedVSub_const_smul`

English:
theorem weightedVSub_const_smul
  given: (w : ι -> k) (p : ι -> P) (c : k)
  proof: s.weightedVSubOfPoint_const_smul _ _ _ _

中文:
定理 weightedVSub_const_smul
  条件: (w : ι -> k) (p : ι -> P) (c : k)
  证明: s.weightedVSubOfPoint_const_smul _ _ _ _

Depends on / 依赖: s.weightedVSubOfPoint_const_smul, weightedVSubOfPoint_const_smul
-/
theorem weightedVSub_const_smul (w : ι -> k) (p : ι -> P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w :=
  s.weightedVSubOfPoint_const_smul _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AffineSpace (ι -> k) (ι -> k)
  body: Pi.instAddTorsor

中文:
实例 :
  签名: 仿射空间 (ι -> k) (ι -> k)
  定义体: Pi.instAddTorsor

Depends on / 依赖: Pi.instAddTorsor, instAddTorsor
-/
instance : AffineSpace (ι -> k) (ι -> k) := Pi.instAddTorsor

variable (k)

/--
Definition of `affineCombination` / `affineCombination` 的定义

English:
definition affineCombination
  signature: (p : ι -> P)
  body: s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, map_add]

中文:
定义 affineCombination
  签名: (p : ι -> P)
  定义体: s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, map_add]

Depends on / 依赖: Classical, Classical.choice, S.nonempty, choice, nonempty, s.weightedVSubOfPoint, weightedVSubOfPoint
-/
def affineCombination (p : ι -> P) : (ι -> k) ->ᵃ[k] P where
  toFun w := s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, map_add]

/-- The linear map corresponding to `affineCombination` is
`weightedVSub`. -/
@[simp]
/--
theorem `affineCombination_linear` / 定理 `affineCombination_linear`

English:
theorem affineCombination_linear
  given: (p : ι -> P)
  proof: rfl

中文:
定理 affineCombination_linear
  条件: (p : ι -> P)
  证明: rfl
-/
theorem affineCombination_linear (p : ι -> P) :
    (s.affineCombination k p).linear = s.weightedVSub p :=
  rfl

variable {k}

/--
theorem `affineCombination_apply` / 定理 `affineCombination_apply`

English:
theorem affineCombination_apply
  given: (w : ι -> k) (p : ι -> P)
  proof: rfl

中文:
定理 affineCombination_apply
  条件: (w : ι -> k) (p : ι -> P)
  证明: rfl
-/
theorem affineCombination_apply (w : ι -> k) (p : ι -> P) :
    (s.affineCombination k p) w =
      s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty :=
  rfl

/-- The value of `affineCombination`, where the given points are equal. -/
@[simp]
/--
theorem `affineCombination_apply_const` / 定理 `affineCombination_apply_const`

English:
theorem affineCombination_apply_const
  given: (w : ι -> k) (p : P) (h : ∑ i in s, w i = 1)
  proof: by
  rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_apply_const]; rw [h]; rw [one_smul]; rw [vsub_vadd]

中文:
定理 affineCombination_apply_const
  条件: (w : ι -> k) (p : P) (h : ∑ i in s, w i = 1)
  证明: by
  rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_apply_const]; rw [h]; rw [one_smul]; rw [vsub_vadd]

Depends on / 依赖: affineCombination_apply, one_smul, s.weightedVSubOfPoint_apply_const, vsub_vadd, weightedVSubOfPoint_apply_const
-/
theorem affineCombination_apply_const (w : ι -> k) (p : P) (h : ∑ i in s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_apply_const]; rw [h]; rw [one_smul]; rw [vsub_vadd]

/--
theorem `affineCombination_congr` / 定理 `affineCombination_congr`

English:
theorem affineCombination_congr
  statement: {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  proof: by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]

中文:
定理 affineCombination_congr
  结论: {w₁ w₂ : ι -> k} (hw : 对任意 i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
  证明: by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]

Depends on / 依赖: affineCombination_apply, s.weightedVSubOfPoint_congr, simp_rw, weightedVSubOfPoint_congr
-/
theorem affineCombination_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P}
    (hp : forall i in s, p₁ i = p₂ i) : s.affineCombination k p₁ w₁ = s.affineCombination k p₂ w₂ := by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]

/--
theorem `affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one` / 定理 `affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`

English:
theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
  statement: (w : ι -> k) (p : ι -> P)
  proof: s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _

中文:
定理 affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
  结论: (w : ι -> k) (p : ι -> P)
  证明: s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _

Depends on / 依赖: s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one, weightedVSubOfPoint_vadd_eq_of_sum_eq_one
-/
theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P)
    (h : ∑ i in s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b :=
  s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _

/--
theorem `weightedVSub_vadd_affineCombination` / 定理 `weightedVSub_vadd_affineCombination`

English:
theorem weightedVSub_vadd_affineCombination
  given: (w₁ w₂ : ι -> k) (p : ι -> P)
  proof: by
  rw [← vadd_eq_add]; rw [AffineMap.map_vadd]; rw [affineCombination_linear]

中文:
定理 weightedVSub_vadd_affineCombination
  条件: (w₁ w₂ : ι -> k) (p : ι -> P)
  证明: by
  rw [← vadd_eq_add]; rw [AffineMap.map_vadd]; rw [affineCombination_linear]

Depends on / 依赖: AffineMap, AffineMap.map_vadd, affineCombination_linear, map_vadd, vadd_eq_add
-/
theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι -> k) (p : ι -> P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add]; rw [AffineMap.map_vadd]; rw [affineCombination_linear]

/--
theorem `affineCombination_vsub` / 定理 `affineCombination_vsub`

English:
theorem affineCombination_vsub
  given: (w₁ w₂ : ι -> k) (p : ι -> P)
  proof: by
  rw [← AffineMap.linearMap_vsub]; rw [affineCombination_linear]; rw [vsub_eq_sub]

中文:
定理 affineCombination_vsub
  条件: (w₁ w₂ : ι -> k) (p : ι -> P)
  证明: by
  rw [← AffineMap.linearMap_vsub]; rw [affineCombination_linear]; rw [vsub_eq_sub]

Depends on / 依赖: AffineMap, AffineMap.linearMap_vsub, affineCombination_linear, linearMap_vsub, vsub_eq_sub
-/
theorem affineCombination_vsub (w₁ w₂ : ι -> k) (p : ι -> P) :
    s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂) := by
  rw [← AffineMap.linearMap_vsub]; rw [affineCombination_linear]; rw [vsub_eq_sub]

/--
theorem `attach_affineCombination_of_injective` / 定理 `attach_affineCombination_of_injective`

English:
theorem attach_affineCombination_of_injective
  statement: [DecidableEq P] (s : Finset P) (w : P -> k) (f : s -> P)
  proof: by
  simp [affineCombination, hf]

中文:
定理 attach_affineCombination_of_injective
  结论: [DecidableEq P] (s : 有限集 P) (w : P -> k) (f : s -> P)
  证明: by
  simp [affineCombination, hf]

Depends on / 依赖: affineCombination
-/
theorem attach_affineCombination_of_injective [DecidableEq P] (s : Finset P) (w : P -> k) (f : s -> P)
    (hf : Function.Injective f) :
    s.attach.affineCombination k f (w ∘ f) = (image f univ).affineCombination k id w := by
  simp [affineCombination, hf]

/--
theorem `attach_affineCombination_coe` / 定理 `attach_affineCombination_coe`

English:
theorem attach_affineCombination_coe
  given: (s : Finset P) (w : P -> k)
  proof: by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s -> P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

中文:
定理 attach_affineCombination_coe
  条件: (s : 有限集 P) (w : P -> k)
  证明: by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s -> P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

Depends on / 依赖: Subtype, Subtype.coe_injective, attach_affineCombination_of_injective, attach_image_val, classical, coe_injective, univ_eq_attach
-/
theorem attach_affineCombination_coe (s : Finset P) (w : P -> k) :
    s.attach.affineCombination k ((↑) : s -> P) (w ∘ (↑)) = s.affineCombination k id w := by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s -> P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

/-- Viewing a module as an affine space modelled on itself, a `weightedVSub` is just a linear
combination. -/
@[simp]
/--
theorem `weightedVSub_eq_linear_combination` / 定理 `weightedVSub_eq_linear_combination`

English:
theorem weightedVSub_eq_linear_combination
  statement: {ι} (s : Finset ι) {w : ι -> k} {p : ι -> V}
  proof: by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

中文:
定理 weightedVSub_eq_linear_combination
  结论: {ι} (s : 有限集 ι) {w : ι -> k} {p : ι -> V}
  证明: by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

Depends on / 依赖: Finset, Finset.sum_smul, s.weightedVSub_apply, smul_sub, sum_smul, vsub_eq_sub, weightedVSub_apply
-/
theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι -> k} {p : ι -> V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i in s, w i • p i := by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

/-- Viewing a module as an affine space modelled on itself, affine combinations are just linear
combinations. -/
@[simp]
/--
theorem `affineCombination_eq_linear_combination` / 定理 `affineCombination_eq_linear_combination`

English:
theorem affineCombination_eq_linear_combination
  statement: (s : Finset ι) (p : ι -> V) (w : ι -> k)
  proof: by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]

中文:
定理 affineCombination_eq_linear_combination
  结论: (s : 有限集 ι) (p : ι -> V) (w : ι -> k)
  证明: by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]

Depends on / 依赖: affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
-/
theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k)
    (hw : ∑ i in s, w i = 1) : s.affineCombination k p w = ∑ i in s, w i • p i := by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]

-- Cannot be @[simp] because `i` cannot be inferred by `simp`.
/--
theorem `affineCombination_of_eq_one_of_eq_zero` / 定理 `affineCombination_of_eq_one_of_eq_zero`

English:
theorem affineCombination_of_eq_one_of_eq_zero
  statement: (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s)
  proof: by
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i)]; rw [weightedVSubOfPoint_apply]
  convert! zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · si

中文:
定理 affineCombination_of_eq_one_of_eq_zero
  结论: (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s)
  证明: by
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i)]; rw [weightedVSubOfPoint_apply]
  convert! zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · si

Depends on / 依赖: False.elim, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, convert, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, sum_eq_single, sum_eq_zero, weightedVSubOfPoint_apply, zero_vadd
-/
theorem affineCombination_of_eq_one_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s)
    (hwi : w i = 1) (hw0 : forall i2 in s, i2 != i -> w i2 = 0) : s.affineCombination k p w = p i := by
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i)]; rw [weightedVSubOfPoint_apply]
  convert! zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · simp [h]
  · simp [hw0 i2 hi2 h]

/--
theorem `affineCombination_indicator_subset` / 定理 `affineCombination_indicator_subset`

English:
theorem affineCombination_indicator_subset
  statement: (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι}
  proof: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_indicator_subset _ _ _ h]

中文:
定理 affineCombination_indicator_subset
  结论: (w : ι -> k) (p : ι -> P) {s₁ s₂ : 有限集 ι}
  证明: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_indicator_subset _ _ _ h]

Depends on / 依赖: affineCombination_apply, weightedVSubOfPoint_indicator_subset
-/
theorem affineCombination_indicator_subset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι}
    (h : s₁ subseteq s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_indicator_subset _ _ _ h]

/--
theorem `affineCombination_map` / 定理 `affineCombination_map`

English:
theorem affineCombination_map
  given: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P)
  proof: by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]

中文:
定理 affineCombination_map
  条件: (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P)
  证明: by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]

Depends on / 依赖: affineCombination_apply, simp_rw, weightedVSubOfPoint_map
-/
theorem affineCombination_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) :
    (s₂.map e).affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e) := by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]

/--
theorem `sum_smul_vsub_eq_affineCombination_vsub` / 定理 `sum_smul_vsub_eq_affineCombination_vsub`

English:
theorem sum_smul_vsub_eq_affineCombination_vsub
  given: (w : ι -> k) (p₁ p₂ : ι -> P)
  proof: by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

中文:
定理 sum_smul_vsub_eq_affineCombination_vsub
  条件: (w : ι -> k) (p₁ p₂ : ι -> P)
  证明: by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

Depends on / 依赖: affineCombination_apply, s.sum_smul_vsub_eq_weightedVSubOfPoint_sub, simp_rw, sum_smul_vsub_eq_weightedVSubOfPoint_sub, vadd_vsub_vadd_cancel_right
-/
theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι -> k) (p₁ p₂ : ι -> P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/--
theorem `sum_smul_vsub_const_eq_affineCombination_vsub` / 定理 `sum_smul_vsub_const_eq_affineCombination_vsub`

English:
theorem sum_smul_vsub_const_eq_affineCombination_vsub
  statement: (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
  proof: by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

中文:
定理 sum_smul_vsub_const_eq_affineCombination_vsub
  结论: (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
  证明: by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

Depends on / 依赖: affineCombination_apply_const, sum_smul_vsub_eq_affineCombination_vsub
-/
theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι -> k) (p₁ : ι -> P) (p₂ : P)
    (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ := by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

/--
theorem `sum_smul_const_vsub_eq_vsub_affineCombination` / 定理 `sum_smul_const_vsub_eq_vsub_affineCombination`

English:
theorem sum_smul_const_vsub_eq_vsub_affineCombination
  statement: (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
  proof: by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

中文:
定理 sum_smul_const_vsub_eq_vsub_affineCombination
  结论: (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
  证明: by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

Depends on / 依赖: affineCombination_apply_const, sum_smul_vsub_eq_affineCombination_vsub
-/
theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι -> k) (p₂ : ι -> P) (p₁ : P)
    (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  rw [sum_smul_vsub_eq_affineCombination_vsub]; rw [affineCombination_apply_const _ _ _ h]

/--
theorem `affineCombination_sdiff_sub` / 定理 `affineCombination_sdiff_sub`

English:
theorem affineCombination_sdiff_sub
  statement: [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
  proof: by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.weightedVSub_sdiff_sub h _ _

中文:
定理 affineCombination_sdiff_sub
  结论: [DecidableEq ι] {s₂ : 有限集 ι} (h : s₂ subseteq s) (w : ι -> k)
  证明: by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.weightedVSub_sdiff_sub h _ _

Depends on / 依赖: affineCombination_apply, s.weightedVSub_sdiff_sub, simp_rw, vadd_vsub_vadd_cancel_right, weightedVSub_sdiff_sub
-/
theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k)
    (p : ι -> P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.weightedVSub_sdiff_sub h _ _

/--
theorem `affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one` / 定理 `affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one`

English:
theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one
  statement: {w : ι -> k} {p : ι -> P}
  proof: by
  classical
    rw [← @vsub_eq_zero_iff_eq V]; rw [← hw]; rw [← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his)]; rw [sdiff_singleton_eq_erase]; rw [← filter_ne']
    congr
    refine (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    

中文:
定理 affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one
  结论: {w : ι -> k} {p : ι -> P}
  证明: by
  classical
    rw [← @vsub_eq_zero_iff_eq V]; rw [← hw]; rw [← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his)]; rw [sdiff_singleton_eq_erase]; rw [← filter_ne']
    congr
    refine (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    

Depends on / 依赖: affineCombination_of_eq_one_of_eq_zero, affineCombination_sdiff_sub, classical, filter_ne, mem_singleton_self, s.affineCombination_sdiff_sub, sdiff_singleton_eq_erase, singleton_subset_iff, vsub_eq_zero_iff_eq
-/
theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι -> k} {p : ι -> P}
    (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· != i)] (his : i in s)
    (hwi : w i = -1) : {x in s | x != i}.affineCombination k p w = p i := by
  classical
    rw [← @vsub_eq_zero_iff_eq V]; rw [← hw]; rw [← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his)]; rw [sdiff_singleton_eq_erase]; rw [← filter_ne']
    congr
    refine (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    · simp

/--
theorem `affineCombination_subtype_eq_filter` / 定理 `affineCombination_subtype_eq_filter`

English:
theorem affineCombination_subtype_eq_filter
  statement: (w : ι -> k) (p : ι -> P) (pred : ι -> Prop)
  proof: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_subtype_eq_filter]

中文:
定理 affineCombination_subtype_eq_filter
  结论: (w : ι -> k) (p : ι -> P) (pred : ι -> 命题)
  证明: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_subtype_eq_filter]

Depends on / 依赖: affineCombination_apply, weightedVSubOfPoint_subtype_eq_filter
-/
theorem affineCombination_subtype_eq_filter (w : ι -> k) (p : ι -> P) (pred : ι -> Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      {x in s | pred x}.affineCombination k p w := by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [weightedVSubOfPoint_subtype_eq_filter]

/--
theorem `affineCombination_filter_of_ne` / 定理 `affineCombination_filter_of_ne`

English:
theorem affineCombination_filter_of_ne
  statement: (w : ι -> k) (p : ι -> P) {pred : ι -> Prop}
  proof: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_filter_of_ne _ _ _ h]

中文:
定理 affineCombination_filter_of_ne
  结论: (w : ι -> k) (p : ι -> P) {pred : ι -> 命题}
  证明: by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_filter_of_ne _ _ _ h]

Depends on / 依赖: affineCombination_apply, s.weightedVSubOfPoint_filter_of_ne, weightedVSubOfPoint_filter_of_ne
-/
theorem affineCombination_filter_of_ne (w : ι -> k) (p : ι -> P) {pred : ι -> Prop}
    [DecidablePred pred] (h : forall i in s, w i != 0 -> pred i) :
    {x in s | pred x}.affineCombination k p w = s.affineCombination k p w := by
  rw [affineCombination_apply]; rw [affineCombination_apply]; rw [s.weightedVSubOfPoint_filter_of_ne _ _ _ h]

/--
theorem `eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype` / 定理 `eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype`

English:
theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype
  statement: {v : V} {x : k} {s : Set ι}
  proof: by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype (· in s), fun i => w i, sum_subtype_of_mem _ hfs,
        (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine ⟨fs.map (Function.Embedding.subtyp

中文:
定理 eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype
  结论: {v : V} {x : k} {s : 集合 ι}
  证明: by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype (· in s), fun i => w i, sum_subtype_of_mem _ hfs,
        (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine ⟨fs.map (Function.Embedding.subtyp

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, classical, fs.map, fs.subtype, map_subtype_subset, simp_rw, subtype, sum_subtype_of_mem, weightedVSubOfPoint_apply
-/
theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k} {s : Set ι}
    {p : ι -> P} {b : P} :
    (exists fs : Finset ι, ↑fs subseteq s ∧ exists w : ι -> k, ∑ i in fs, w i = x ∧
        v = fs.weightedVSubOfPoint p b w) ↔
      exists (fs : Finset s) (w : s -> k), ∑ i in fs, w i = x ∧
        v = fs.weightedVSubOfPoint (fun i : s => p i) b w := by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype (· in s), fun i => w i, sum_subtype_of_mem _ hfs,
        (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i =>
        if h : i in s then w ⟨i, h⟩ else 0, ?_, ?_⟩ <;> simp

variable (k)

/--
theorem `eq_weightedVSub_subset_iff_eq_weightedVSub_subtype` / 定理 `eq_weightedVSub_subset_iff_eq_weightedVSub_subtype`

English:
theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype
  given: {v : V} {s : Set ι} {p : ι -> P}
  proof: eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

中文:
定理 eq_weightedVSub_subset_iff_eq_weightedVSub_subtype
  条件: {v : V} {s : 集合 ι} {p : ι -> P}
  证明: eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

Depends on / 依赖: eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype
-/
theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p : ι -> P} :
    (exists fs : Finset ι, ↑fs subseteq s ∧ exists w : ι -> k, ∑ i in fs, w i = 0 ∧
        v = fs.weightedVSub p w) ↔
      exists (fs : Finset s) (w : s -> k), ∑ i in fs, w i = 0 ∧
        v = fs.weightedVSub (fun i : s => p i) w :=
  eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable (V)

/--
theorem `eq_affineCombination_subset_iff_eq_affineCombination_subtype` / 定理 `eq_affineCombination_subset_iff_eq_affineCombination_subtype`

English:
theorem eq_affineCombination_subset_iff_eq_affineCombination_subtype
  statement: {p0 : P} {s : Set ι}
  proof: by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

中文:
定理 eq_affineCombination_subset_iff_eq_affineCombination_subtype
  结论: {p0 : P} {s : 集合 ι}
  证明: by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

Depends on / 依赖: affineCombination_apply, eq_vadd_iff_vsub_eq, eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype, simp_rw
-/
theorem eq_affineCombination_subset_iff_eq_affineCombination_subtype {p0 : P} {s : Set ι}
    {p : ι -> P} :
    (exists fs : Finset ι, ↑fs subseteq s ∧ exists w : ι -> k, ∑ i in fs, w i = 1 ∧
        p0 = fs.affineCombination k p w) ↔
      exists (fs : Finset s) (w : s -> k), ∑ i in fs, w i = 1 ∧
        p0 = fs.affineCombination k (fun i : s => p i) w := by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable {k V}

/--
theorem `map_affineCombination` / 定理 `map_affineCombination`

English:
theorem map_affineCombination
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
  proof: by
  have b := Classical.choice (inferInstance : AffineSpace V P).nonempty
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).nonempty
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b]; rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f 

中文:
定理 map_affineCombination
  结论: {V₂ P₂ : 类型} [加法交换群 V₂] [模 k V₂] [仿射空间 V₂ P₂]
  证明: by
  have b := Classical.choice (inferInstance : AffineSpace V P).nonempty
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).nonempty
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b]; rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f 

Depends on / 依赖: AffineMap, AffineMap.linearMap_vsub, AffineMap.map_vadd, AffineSpace, Classical, Classical.choice, RingHom, RingHom.id_apply, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, choice, id_apply, linearMap_vsub, map_su, map_vadd, nonempty, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one, weightedVSubOfPoint_apply, weightedVSubOfPoint_vadd_eq_of_sum_eq_one
-/
theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    (p : ι -> P) (w : ι -> k) (hw : s.sum w = 1) (f : P ->ᵃ[k] P₂) :
    f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w := by
  have b := Classical.choice (inferInstance : AffineSpace V P).nonempty
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).nonempty
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b]; rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f ∘ p) hw b₂]; rw [←
    s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w (f ∘ p) hw (f b) b₂]
  simp only [weightedVSubOfPoint_apply, RingHom.id_apply, AffineMap.map_vadd, map_smulₛₗ,
    AffineMap.linearMap_vsub, map_sum, Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `affineCombination_apply_eq_lineMap_sum` / 引理 `affineCombination_apply_eq_lineMap_sum`

English:
lemma affineCombination_apply_eq_lineMap_sum
  statement: [DecidableEq ι] (w : ι -> k) (p : ι -> P)
  proof: by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁]; rw [weightedVSubOfPoint_apply]; rw [← s.sum_inter_add_sum_sdiff s']; rw [AffineMap.lineMap_apply]; rw [vadd_right_cancel_iff]; rw [sum_smul]
  convert! add_zero _ with i hi
  · convert! Finset.sum_const_zero with i hi


中文:
引理 affineCombination_apply_eq_lineMap_sum
  结论: [DecidableEq ι] (w : ι -> k) (p : ι -> P)
  证明: by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁]; rw [weightedVSubOfPoint_apply]; rw [← s.sum_inter_add_sum_sdiff s']; rw [AffineMap.lineMap_apply]; rw [vadd_right_cancel_iff]; rw [sum_smul]
  convert! add_zero _ with i hi
  · convert! Finset.sum_const_zero with i hi


Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, Finset, Finset.sum_const_zero, add_zero, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, convert, lineMap_apply, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, s.sum_inter_add_sum_sdiff, sum_const_zero, sum_inter_add_sum_sdiff, sum_smul, vadd_right_cancel_iff, weightedVSubOfPoint_apply
-/
lemma affineCombination_apply_eq_lineMap_sum [DecidableEq ι] (w : ι -> k) (p : ι -> P)
    (p₁ p₂ : P) (s' : Finset ι) (h : ∑ i in s, w i = 1) (hp₂ : forall i in s inter s', p i = p₂)
    (hp₁ : forall i in s \ s', p i = p₁) :
    s.affineCombination k p w = AffineMap.lineMap p₁ p₂ (∑ i in s inter s', w i) := by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁]; rw [weightedVSubOfPoint_apply]; rw [← s.sum_inter_add_sum_sdiff s']; rw [AffineMap.lineMap_apply]; rw [vadd_right_cancel_iff]; rw [sum_smul]
  convert! add_zero _ with i hi
  · convert! Finset.sum_const_zero with i hi
    simp [hp₁ i hi]
  · exact (hp₂ i hi).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_affineCombination` / 定理 `lineMap_affineCombination`

English:
theorem lineMap_affineCombination
  given: (w₁ : ι -> k) (w₂ : ι -> k) (r : k) (p : ι -> P)
  proof: by
  simp_rw [Finset.affineCombination_apply, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
    map_add, map_smul]

中文:
定理 lineMap_affineCombination
  条件: (w₁ : ι -> k) (w₂ : ι -> k) (r : k) (p : ι -> P)
  证明: by
  simp_rw [Finset.affineCombination_apply, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
    map_add, map_smul]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, AffineMap.lineMap_vadd, Finset, Finset.affineCombination_apply, affineCombination_apply, lineMap_apply_module, lineMap_vadd, map_add, map_smul, simp_rw
-/
theorem lineMap_affineCombination (w₁ : ι -> k) (w₂ : ι -> k) (r : k) (p : ι -> P) :
    AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) r =
    s.affineCombination k p (AffineMap.lineMap w₁ w₂ r) := by
  simp_rw [Finset.affineCombination_apply, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
    map_add, map_smul]

variable (k)

/-- Weights for expressing a single point as an affine combination. -/
@[deprecated Pi.single (since := "2026-04-16")]
/--
Definition of `affineCombinationSingleWeights` / `affineCombinationSingleWeights` 的定义

English:
definition affineCombinationSingleWeights
  signature: [DecidableEq ι] (i : ι)
  body: Pi.single i 1

@[deprecated Pi.single_eq_same (since := "2026-04-16")]

中文:
定义 affineCombinationSingleWeights
  签名: [DecidableEq ι] (i : ι)
  定义体: Pi.single i 1

@[deprecated Pi.single_eq_same (since := "2026-04-16")]

Depends on / 依赖: Pi.single, single
-/
def affineCombinationSingleWeights [DecidableEq ι] (i : ι) : ι -> k :=
  Pi.single i 1

@[deprecated Pi.single_eq_same (since := "2026-04-16")]
/--
theorem `affineCombinationSingleWeights_apply_self` / 定理 `affineCombinationSingleWeights_apply_self`

English:
theorem affineCombinationSingleWeights_apply_self
  given: [DecidableEq ι] (i : ι)
  proof: Pi.single_eq_same _ _

@[deprecated Pi.single_eq_of_ne (since := "2026-04-16")]

中文:
定理 affineCombinationSingleWeights_apply_self
  条件: [DecidableEq ι] (i : ι)
  证明: Pi.single_eq_same _ _

@[deprecated Pi.single_eq_of_ne (since := "2026-04-16")]

Depends on / 依赖: Pi.single_eq_same, single_eq_same
-/
theorem affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) :
    affineCombinationSingleWeights k i i = 1 := Pi.single_eq_same _ _

@[deprecated Pi.single_eq_of_ne (since := "2026-04-16")]
/--
theorem `affineCombinationSingleWeights_apply_of_ne` / 定理 `affineCombinationSingleWeights_apply_of_ne`

English:
theorem affineCombinationSingleWeights_apply_of_ne
  given: [DecidableEq ι] {i j : ι} (h : j != i)
  proof: Pi.single_eq_of_ne h _

@[deprecated Finset.sum_pi_single' (since := "2026-04-16")]

中文:
定理 affineCombinationSingleWeights_apply_of_ne
  条件: [DecidableEq ι] {i j : ι} (h : j != i)
  证明: Pi.single_eq_of_ne h _

@[deprecated Finset.sum_pi_single' (since := "2026-04-16")]

Depends on / 依赖: Pi.single_eq_of_ne, single_eq_of_ne
-/
theorem affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : j != i) :
    affineCombinationSingleWeights k i j = 0 := Pi.single_eq_of_ne h _

@[deprecated Finset.sum_pi_single' (since := "2026-04-16")]
/--
theorem `sum_affineCombinationSingleWeights` / 定理 `sum_affineCombinationSingleWeights`

English:
theorem sum_affineCombinationSingleWeights
  given: [DecidableEq ι] {i : ι} (h : i in s)
  proof: by
  rw [affineCombinationSingleWeights]; rw [s.sum_pi_single']; rw [if_pos h]

中文:
定理 sum_affineCombinationSingleWeights
  条件: [DecidableEq ι] {i : ι} (h : i in s)
  证明: by
  rw [affineCombinationSingleWeights]; rw [s.sum_pi_single']; rw [if_pos h]

Depends on / 依赖: affineCombinationSingleWeights, if_pos, s.sum_pi_single, sum_pi_single
-/
theorem sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i in s) :
    ∑ j in s, affineCombinationSingleWeights k i j = 1 := by
  rw [affineCombinationSingleWeights]; rw [s.sum_pi_single']; rw [if_pos h]

/--
Definition of `weightedVSubVSubWeights` / `weightedVSubVSubWeights` 的定义

English:
definition weightedVSubVSubWeights
  signature: [DecidableEq ι] (i j : ι)
  body: Pi.single i 1 - Pi.single j 1

@[simp]

中文:
定义 weightedVSubVSubWeights
  签名: [DecidableEq ι] (i j : ι)
  定义体: Pi.single i 1 - Pi.single j 1

@[simp]

Depends on / 依赖: Pi.single, single
-/
def weightedVSubVSubWeights [DecidableEq ι] (i j : ι) : ι -> k :=
  Pi.single i 1 - Pi.single j 1

@[simp]
/--
theorem `weightedVSubVSubWeights_self` / 定理 `weightedVSubVSubWeights_self`

English:
theorem weightedVSubVSubWeights_self
  given: [DecidableEq ι] (i : ι)
  proof: by simp [weightedVSubVSubWeights]

@[simp]

中文:
定理 weightedVSubVSubWeights_self
  条件: [DecidableEq ι] (i : ι)
  证明: by simp [weightedVSubVSubWeights]

@[simp]

Depends on / 依赖: weightedVSubVSubWeights
-/
theorem weightedVSubVSubWeights_self [DecidableEq ι] (i : ι) :
    weightedVSubVSubWeights k i i = 0 := by simp [weightedVSubVSubWeights]

@[simp]
/--
theorem `weightedVSubVSubWeights_apply_left` / 定理 `weightedVSubVSubWeights_apply_left`

English:
theorem weightedVSubVSubWeights_apply_left
  given: [DecidableEq ι] {i j : ι} (h : i != j)
  proof: by simp [weightedVSubVSubWeights, h]

@[simp]

中文:
定理 weightedVSubVSubWeights_apply_left
  条件: [DecidableEq ι] {i j : ι} (h : i != j)
  证明: by simp [weightedVSubVSubWeights, h]

@[simp]

Depends on / 依赖: weightedVSubVSubWeights
-/
theorem weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) :
    weightedVSubVSubWeights k i j i = 1 := by simp [weightedVSubVSubWeights, h]

@[simp]
/--
theorem `weightedVSubVSubWeights_apply_right` / 定理 `weightedVSubVSubWeights_apply_right`

English:
theorem weightedVSubVSubWeights_apply_right
  given: [DecidableEq ι] {i j : ι} (h : i != j)
  proof: by simp [weightedVSubVSubWeights, h.symm]

@[simp]

中文:
定理 weightedVSubVSubWeights_apply_right
  条件: [DecidableEq ι] {i j : ι} (h : i != j)
  证明: by simp [weightedVSubVSubWeights, h.symm]

@[simp]

Depends on / 依赖: h.symm, weightedVSubVSubWeights
-/
theorem weightedVSubVSubWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) :
    weightedVSubVSubWeights k i j j = -1 := by simp [weightedVSubVSubWeights, h.symm]

@[simp]
/--
theorem `weightedVSubVSubWeights_apply_of_ne` / 定理 `weightedVSubVSubWeights_apply_of_ne`

English:
theorem weightedVSubVSubWeights_apply_of_ne
  given: [DecidableEq ι] {i j t : ι} (hi : t != i) (hj : t != j)
  proof: by simp [weightedVSubVSubWeights, hi, hj]

@[simp]

中文:
定理 weightedVSubVSubWeights_apply_of_ne
  条件: [DecidableEq ι] {i j t : ι} (hi : t != i) (hj : t != j)
  证明: by simp [weightedVSubVSubWeights, hi, hj]

@[simp]

Depends on / 依赖: weightedVSubVSubWeights
-/
theorem weightedVSubVSubWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t != i) (hj : t != j) :
    weightedVSubVSubWeights k i j t = 0 := by simp [weightedVSubVSubWeights, hi, hj]

@[simp]
/--
theorem `sum_weightedVSubVSubWeights` / 定理 `sum_weightedVSubVSubWeights`

English:
theorem sum_weightedVSubVSubWeights
  given: [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s)
  proof: by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  simp [hi, hj]

中文:
定理 sum_weightedVSubVSubWeights
  条件: [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s)
  证明: by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  simp [hi, hj]

Depends on / 依赖: Pi.sub_apply, simp_rw, sub_apply, sum_sub_distrib, weightedVSubVSubWeights
-/
theorem sum_weightedVSubVSubWeights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) :
    ∑ t in s, weightedVSubVSubWeights k i j t = 0 := by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  simp [hi, hj]

variable {k}

/--
Definition of `affineCombinationLineMapWeights` / `affineCombinationLineMapWeights` 的定义

English:
definition affineCombinationLineMapWeights
  signature: [DecidableEq ι] (i j : ι) (c : k)
  body: c • weightedVSubVSubWeights k j i + Pi.single i 1

@[simp]

中文:
定义 affineCombinationLineMapWeights
  签名: [DecidableEq ι] (i j : ι) (c : k)
  定义体: c • weightedVSubVSubWeights k j i + Pi.single i 1

@[simp]

Depends on / 依赖: Pi.single, single, weightedVSubVSubWeights
-/
def affineCombinationLineMapWeights [DecidableEq ι] (i j : ι) (c : k) : ι -> k :=
  c • weightedVSubVSubWeights k j i + Pi.single i 1

@[simp]
/--
theorem `affineCombinationLineMapWeights_self` / 定理 `affineCombinationLineMapWeights_self`

English:
theorem affineCombinationLineMapWeights_self
  given: [DecidableEq ι] (i : ι) (c : k)
  proof: by
  simp [affineCombinationLineMapWeights]

@[simp]

中文:
定理 affineCombinationLineMapWeights_self
  条件: [DecidableEq ι] (i : ι) (c : k)
  证明: by
  simp [affineCombinationLineMapWeights]

@[simp]

Depends on / 依赖: affineCombinationLineMapWeights
-/
theorem affineCombinationLineMapWeights_self [DecidableEq ι] (i : ι) (c : k) :
    affineCombinationLineMapWeights i i c = Pi.single i 1 := by
  simp [affineCombinationLineMapWeights]

@[simp]
/--
theorem `affineCombinationLineMapWeights_apply_left` / 定理 `affineCombinationLineMapWeights_apply_left`

English:
theorem affineCombinationLineMapWeights_apply_left
  given: [DecidableEq ι] {i j : ι} (h : i != j) (c : k)
  proof: by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

@[simp]

中文:
定理 affineCombinationLineMapWeights_apply_left
  条件: [DecidableEq ι] {i j : ι} (h : i != j) (c : k)
  证明: by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

@[simp]

Depends on / 依赖: affineCombinationLineMapWeights, h.symm, sub_eq_neg_add
-/
theorem affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) :
    affineCombinationLineMapWeights i j c i = 1 - c := by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

@[simp]
/--
theorem `affineCombinationLineMapWeights_apply_right` / 定理 `affineCombinationLineMapWeights_apply_right`

English:
theorem affineCombinationLineMapWeights_apply_right
  given: [DecidableEq ι] {i j : ι} (h : i != j) (c : k)
  proof: by
  simp [affineCombinationLineMapWeights, h.symm]

@[simp]

中文:
定理 affineCombinationLineMapWeights_apply_right
  条件: [DecidableEq ι] {i j : ι} (h : i != j) (c : k)
  证明: by
  simp [affineCombinationLineMapWeights, h.symm]

@[simp]

Depends on / 依赖: affineCombinationLineMapWeights, h.symm
-/
theorem affineCombinationLineMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) :
    affineCombinationLineMapWeights i j c j = c := by
  simp [affineCombinationLineMapWeights, h.symm]

@[simp]
/--
theorem `affineCombinationLineMapWeights_apply_of_ne` / 定理 `affineCombinationLineMapWeights_apply_of_ne`

English:
theorem affineCombinationLineMapWeights_apply_of_ne
  statement: [DecidableEq ι] {i j t : ι} (hi : t != i)
  proof: by
  simp [affineCombinationLineMapWeights, hi, hj]

@[simp]

中文:
定理 affineCombinationLineMapWeights_apply_of_ne
  结论: [DecidableEq ι] {i j t : ι} (hi : t != i)
  证明: by
  simp [affineCombinationLineMapWeights, hi, hj]

@[simp]

Depends on / 依赖: affineCombinationLineMapWeights
-/
theorem affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t != i)
    (hj : t != j) (c : k) : affineCombinationLineMapWeights i j c t = 0 := by
  simp [affineCombinationLineMapWeights, hi, hj]

@[simp]
/--
theorem `sum_affineCombinationLineMapWeights` / 定理 `sum_affineCombinationLineMapWeights`

English:
theorem sum_affineCombinationLineMapWeights
  statement: [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s)
  proof: by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

中文:
定理 sum_affineCombinationLineMapWeights
  结论: [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s)
  证明: by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

Depends on / 依赖: Pi.add_apply, add_apply, affineCombinationLineMapWeights, mul_sum, simp_rw, sum_add_distrib
-/
theorem sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s)
    (c : k) : ∑ t in s, affineCombinationLineMapWeights i j c t = 1 := by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

variable (k)

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[simp]
/--
theorem `affineCombination_piSingle` / 定理 `affineCombination_piSingle`

English:
theorem affineCombination_piSingle
  statement: [DecidableEq ι] (p : ι -> P) {i : ι}
  proof: by
  refine s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

中文:
定理 affineCombination_piSingle
  结论: [DecidableEq ι] (p : ι -> P) {i : ι}
  证明: by
  refine s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

Depends on / 依赖: affineCombination_of_eq_one_of_eq_zero, s.affineCombination_of_eq_one_of_eq_zero
-/
theorem affineCombination_piSingle [DecidableEq ι] (p : ι -> P) {i : ι}
    (hi : i in s) : s.affineCombination k p (Pi.single i 1) = p i := by
  refine s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[deprecated affineCombination_piSingle (since := "2026-04-16")]
/--
theorem `affineCombination_affineCombinationSingleWeights` / 定理 `affineCombination_affineCombinationSingleWeights`

English:
theorem affineCombination_affineCombinationSingleWeights
  statement: [DecidableEq ι] (p : ι -> P) {i : ι}
  proof: affineCombination_piSingle _ _ _ hi

中文:
定理 affineCombination_affineCombinationSingleWeights
  结论: [DecidableEq ι] (p : ι -> P) {i : ι}
  证明: affineCombination_piSingle _ _ _ hi

Depends on / 依赖: affineCombination_piSingle
-/
theorem affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι -> P) {i : ι}
    (hi : i in s) : s.affineCombination k p (affineCombinationSingleWeights k i) = p i :=
  affineCombination_piSingle _ _ _ hi

/-- A weighted subtraction with `weightedVSubVSubWeights` gives the result of subtracting the
specified points. -/
@[simp]
/--
theorem `weightedVSub_weightedVSubVSubWeights` / 定理 `weightedVSub_weightedVSubVSubWeights`

English:
theorem weightedVSub_weightedVSubVSubWeights
  statement: [DecidableEq ι] (p : ι -> P) {i j : ι} (hi : i in s)
  proof: by
  rw [weightedVSubVSubWeights]; rw [← affineCombination_vsub]; rw [s.affineCombination_piSingle k p hi]; rw [s.affineCombination_piSingle k p hj]

中文:
定理 weightedVSub_weightedVSubVSubWeights
  结论: [DecidableEq ι] (p : ι -> P) {i j : ι} (hi : i in s)
  证明: by
  rw [weightedVSubVSubWeights]; rw [← affineCombination_vsub]; rw [s.affineCombination_piSingle k p hi]; rw [s.affineCombination_piSingle k p hj]

Depends on / 依赖: affineCombination_piSingle, affineCombination_vsub, s.affineCombination_piSingle, weightedVSubVSubWeights
-/
theorem weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi : i in s)
    (hj : j in s) : s.weightedVSub p (weightedVSubVSubWeights k i j) = p i -ᵥ p j := by
  rw [weightedVSubVSubWeights]; rw [← affineCombination_vsub]; rw [s.affineCombination_piSingle k p hi]; rw [s.affineCombination_piSingle k p hj]

variable {k}

set_option backward.isDefEq.respectTransparency false in
/-- An affine combination with `affineCombinationLineMapWeights` gives the result of
`line_map`. -/
@[simp]
/--
theorem `affineCombination_affineCombinationLineMapWeights` / 定理 `affineCombination_affineCombinationLineMapWeights`

English:
theorem affineCombination_affineCombinationLineMapWeights
  statement: [DecidableEq ι] (p : ι -> P) {i j : ι}
  proof: by
  rw [affineCombinationLineMapWeights]; rw [← weightedVSub_vadd_affineCombination]; rw [weightedVSub_const_smul]; rw [s.affineCombination_piSingle k p hi]; rw [s.weightedVSub_weightedVSubVSubWeights k p hj hi]; rw [AffineMap.lineMap_apply]

中文:
定理 affineCombination_affineCombinationLineMapWeights
  结论: [DecidableEq ι] (p : ι -> P) {i j : ι}
  证明: by
  rw [affineCombinationLineMapWeights]; rw [← weightedVSub_vadd_affineCombination]; rw [weightedVSub_const_smul]; rw [s.affineCombination_piSingle k p hi]; rw [s.weightedVSub_weightedVSubVSubWeights k p hj hi]; rw [AffineMap.lineMap_apply]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, affineCombinationLineMapWeights, affineCombination_piSingle, lineMap_apply, s.affineCombination_piSingle, s.weightedVSub_weightedVSubVSubWeights, weightedVSub_const_smul, weightedVSub_vadd_affineCombination, weightedVSub_weightedVSubVSubWeights
-/
theorem affineCombination_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι}
    (hi : i in s) (hj : j in s) (c : k) :
    s.affineCombination k p (affineCombinationLineMapWeights i j c) =
      AffineMap.lineMap (p i) (p j) c := by
  rw [affineCombinationLineMapWeights]; rw [← weightedVSub_vadd_affineCombination]; rw [weightedVSub_const_smul]; rw [s.affineCombination_piSingle k p hi]; rw [s.weightedVSub_weightedVSubVSubWeights k p hj hi]; rw [AffineMap.lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
-- Redeclaring all variables because `AffineMap.homothety` requires `[CommRing k]`
/--
theorem `homothety_affineCombination` / 定理 `homothety_affineCombination`

English:
theorem homothety_affineCombination
  statement: {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  proof: by
  rw [AffineMap.homothety_eq_lineMap]; rw [← Finset.lineMap_affineCombination]; rw [Finset.affineCombination_piSingle _ _ _ hi]

中文:
定理 homothety_affineCombination
  结论: {k V P : 类型} [交换环 k] [加法交换群 V] [模 k V]
  证明: by
  rw [AffineMap.homothety_eq_lineMap]; rw [← Finset.lineMap_affineCombination]; rw [Finset.affineCombination_piSingle _ _ _ hi]

Depends on / 依赖: AffineMap, AffineMap.homothety_eq_lineMap, Finset, Finset.affineCombination_piSingle, Finset.lineMap_affineCombination, affineCombination_piSingle, homothety_eq_lineMap, lineMap_affineCombination
-/
theorem homothety_affineCombination {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AffineSpace V P] {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι -> P) (w : ι -> k) {i : ι}
    (hi : i in s) (r : k) :
    AffineMap.homothety (p i) r (s.affineCombination k p w) = s.affineCombination k p
      (AffineMap.lineMap (Pi.single i 1) w r) := by
  rw [AffineMap.homothety_eq_lineMap]; rw [← Finset.lineMap_affineCombination]; rw [Finset.affineCombination_piSingle _ _ _ hi]

end Finset

section AffineSpace'

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/--
theorem `weightedVSub_mem_vectorSpan` / 定理 `weightedVSub_mem_vectorSpan`

English:
theorem weightedVSub_mem_vectorSpan
  statement: {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0)
  proof: by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_e

中文:
定理 weightedVSub_mem_vectorSpan
  结论: {s : 有限集 ι} {w : ι -> k} (h : ∑ i in s, w i = 0)
  证明: by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_e

Depends on / 依赖: Finset, Finset.eq_empty_of_isEmpty, Finset.weightedVSubOfPoint_apply, Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero, Finsupp, Finsupp.mem_span_image_iff_linearCombination, Finsupp.onFinset, Set.image_univ, Set.indicator, Set.mem_of_indicator_ne_zero, Set.subset_univ, classical, eq_empty_of_isEmpty, image_univ, indicator, isEmpty_or_nonempty, mem_of_indicator_ne_zero, mem_span_image_iff_linearCombination, onFinset, subset_univ
-/
theorem weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0)
    (p : ι -> P) : s.weightedVSub p w in vectorSpan k (Set.range p) := by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i0),
        Finset.weightedVSubOfPoint_apply]
      let w' := Set.indicator (↑s) w
      have hwx : forall i, w' i != 0 -> i in s := fun i => Set.mem_of_indicator_ne_zero
      use Finsupp.onFinset s w' hwx, Set.subset_univ _
      rw [Finsupp.linearCombination_apply]; rw [Finsupp.onFinset_sum hwx]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [w', Set.indicator_apply, if_pos hi]
      · exact fun _ => zero_smul k _

/--
theorem `affineCombination_mem_affineSpan` / 定理 `affineCombination_mem_affineSpan`

English:
theorem affineCombination_mem_affineSpan
  statement: [Nontrivial k] {s : Finset ι} {w : ι -> k}
  proof: by
  classical
    have hnz : ∑ i in s, w i != 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι -> k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i in s, w1 i = 1 := by
      simp only [w1, Function.co

中文:
定理 affineCombination_mem_affineSpan
  结论: [非平凡 k] {s : 有限集 ι} {w : ι -> k}
  证明: by
  classical
    have hnz : ∑ i in s, w i != 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι -> k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i in s, w1 i = 1 := by
      simp only [w1, Function.co

Depends on / 依赖: Finset, Finset.nonempty_of_sum_ne_zero, Finset.sum_const_zero, Finset.sum_update_of_mem, Function, Function.const, Function.const_zero, Function.update, Function.update_self, Nonempty, Pi.zero_apply, add_zero, affineCombination, affineCombination_of_eq_one_of_eq_zero, classical, const_zero, h.symm, nonempty_of_sum_ne_zero, one_ne_zero, s.Nonempty
-/
theorem affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι -> k}
    (h : ∑ i in s, w i = 1) (p : ι -> P) :
    s.affineCombination k p w in affineSpan k (Set.range p) := by
  classical
    have hnz : ∑ i in s, w i != 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι -> k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i in s, w1 i = 1 := by
      simp only [w1, Function.const_zero, Finset.sum_update_of_mem hi1, Pi.zero_apply,
          Finset.sum_const_zero, add_zero]
    have hw1s : s.affineCombination k p w1 = p i1 :=
      s.affineCombination_of_eq_one_of_eq_zero w1 p hi1 (Function.update_self ..) fun _ _ hne =>
        Function.update_of_ne hne ..
    have hv : s.affineCombination k p w -ᵥ p i1 in (affineSpan k (Set.range p)).direction := by
      rw [direction_affineSpan]; rw [← hw1s]; rw [Finset.affineCombination_vsub]
      apply weightedVSub_mem_vectorSpan
      simp [Pi.sub_apply, h, hw1]
    rw [← vsub_vadd (s.affineCombination k p w) (p i1)]
    exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k (Set.mem_range_self _))

/--
theorem `affineCombination_mem_affineSpan_of_nonempty` / 定理 `affineCombination_mem_affineSpan_of_nonempty`

English:
theorem affineCombination_mem_affineSpan_of_nonempty
  statement: [Nonempty ι] {s : Finset ι} {w : ι -> k}
  proof: by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

中文:
定理 affineCombination_mem_affineSpan_of_nonempty
  结论: [非空 ι] {s : 有限集 ι} {w : ι -> k}
  证明: by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

Depends on / 依赖: AddTorsor, AddTorsor.subsingleton_iff, Module, Module.subsingleton, Set.range_nonempty, affineCombination_mem_affineSpan, affineSpan_eq_top_iff_nonempty_of_subsingleton, range_nonempty, subsingleton, subsingleton_iff, subsingleton_or_nontrivial
-/
theorem affineCombination_mem_affineSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι -> k}
    (h : ∑ i in s, w i = 1) (p : ι -> P) :
    s.affineCombination k p w in affineSpan k (Set.range p) := by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

variable (k) in
/--
theorem `mem_vectorSpan_iff_eq_weightedVSub` / 定理 `mem_vectorSpan_iff_eq_weightedVSub`

English:
theorem mem_vectorSpan_iff_eq_weightedVSub
  given: {v : V} {p : ι -> P}
  proof: by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_linearCombination]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        se

中文:
定理 mem_vectorSpan_iff_eq_weightedVSub
  条件: {v : V} {p : ι -> P}
  证明: by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_linearCombination]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        se

Depends on / 依赖: Finset, Finset.m, Finset.sum_sub_distrib, Finset.sum_update_of_mem, Finsupp, Finsupp.mem_span_image_iff_linearCombination, Function, Function.const, Function.update, Pi.sub_apply, Set.image_univ, classical, image_univ, insert, isEmpty_or_nonempty, l.support, mem_span_image_iff_linearCombination, simp_rw, sub_apply, sum_sub_distrib
-/
theorem mem_vectorSpan_iff_eq_weightedVSub {v : V} {p : ι -> P} :
    v in vectorSpan k (Set.range p) ↔
      exists (s : Finset ι) (w : ι -> k), ∑ i in s, w i = 0 ∧ v = s.weightedVSub p w := by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_linearCombination]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        set w :=
          (l : ι -> k) - Function.update (Function.const ι 0 : ι -> k) i0 (∑ i in l.support, l i) with
          hwdef
        use w
        have hw : ∑ i in insert i0 l.support, w i = 0 := by
          rw [hwdef]
          simp_rw [Pi.sub_apply, Finset.sum_sub_distrib,
            Finset.sum_update_of_mem (Finset.mem_insert_self _ _),
            Finset.sum_insert_of_eq_zero_if_notMem Finsupp.notMem_support_iff.1]
          simp only [Function.const_apply, Finset.sum_const_zero, add_zero, sub_self]
        use hw
        have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self (p i0)).symm ▸ smul_zero _
        change (fun i => w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w p hw (p i0)]; rw [Finset.weightedVSubOfPoint_apply]; rw [← hv]; rw [Finsupp.linearCombination_apply]; rw [@Finset.sum_insert_zero _ _ l.support i0 _ _ _ hz]
        change (∑ i in l.support, l i • _) = _
        congr with i
        by_cases h : i = i0
        · simp [h]
        · simp [hwdef, h]
      · rw [Set.range_eq_empty, vectorSpan_empty, Submodule.mem_bot]
        rintro rfl
        use ∅
        simp
    · rintro ⟨s, w, hw, rfl⟩
      exact weightedVSub_mem_vectorSpan hw p

/--
theorem `eq_affineCombination_of_mem_affineSpan` / 定理 `eq_affineCombination_of_mem_affineSpan`

English:
theorem eq_affineCombination_of_mem_affineSpan
  statement: {p1 : P} {p : ι -> P}
  proof: by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty]; rw [Set.range_nonempty_iff_nonempty] at hn
    obtain ⟨i0⟩ := hn
    have h0 : p i0 in affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 i

中文:
定理 eq_affineCombination_of_mem_affineSpan
  结论: {p1 : P} {p : ι -> P}
  证明: by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty]; rw [Set.range_nonempty_iff_nonempty] at hn
    obtain ⟨i0⟩ := hn
    have h0 : p i0 in affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 i

Depends on / 依赖: AffineSubspace, AffineSubspace.vsub_mem_direction, Nonempty, Set.i, Set.mem_range_self, Set.range, Set.range_nonempty_iff_nonempty, affineSpan, affineSpan_nonempty, classical, direction, direction_affineSpan, insert, mem_affineSpan, mem_range_self, mem_vectorSpan_iff_eq_weightedVSub, range_nonempty_iff_nonempty, vsub_mem_direction
-/
theorem eq_affineCombination_of_mem_affineSpan {p1 : P} {p : ι -> P}
    (h : p1 in affineSpan k (Set.range p)) :
    exists (s : Finset ι) (w : ι -> k), ∑ i in s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty]; rw [Set.range_nonempty_iff_nonempty] at hn
    obtain ⟨i0⟩ := hn
    have h0 : p i0 in affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 in (affineSpan k (Set.range p)).direction :=
      AffineSubspace.vsub_mem_direction h h0
    rw [direction_affineSpan]; rw [mem_vectorSpan_iff_eq_weightedVSub] at hd
    rcases hd with ⟨s, w, h, hs⟩
    let s' := insert i0 s
    let w' := Set.indicator (↑s) w
    have h' : ∑ i in s', w' i = 0 := by
      rw [← h]; rw [Finset.sum_indicator_subset _ (Finset.subset_insert i0 s)]
    have hs' : s'.weightedVSub p w' = p1 -ᵥ p i0 := by
      rw [hs]
      exact (Finset.weightedVSub_indicator_subset _ _ (Finset.subset_insert i0 s)).symm
    let w0 : ι -> k := Function.update (Function.const ι 0) i0 1
    have hw0 : ∑ i in s', w0 i = 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_insert_self _ _)]
      simp only [Function.const_apply, Finset.sum_const_zero,
        add_zero]
    have hw0s : s'.affineCombination k p w0 = p i0 :=
      s'.affineCombination_of_eq_one_of_eq_zero w0 p (Finset.mem_insert_self _ _)
        (Function.update_self ..) fun _ _ hne => Function.update_of_ne hne _ _
    refine ⟨s', w0 + w', ?_, ?_⟩
    · simp [Pi.add_apply, Finset.sum_add_distrib, hw0, h']
    · rw [add_comm, ← Finset.weightedVSub_vadd_affineCombination, hw0s, hs', vsub_vadd]

/--
theorem `eq_affineCombination_of_mem_affineSpan_of_fintype` / 定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`

English:
theorem eq_affineCombination_of_mem_affineSpan_of_fintype
  statement: [Fintype ι] {p1 : P} {p : ι -> P}
  proof: by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

中文:
定理 eq_affineCombination_of_mem_affineSpan_of_fintype
  结论: [有限类型 ι] {p1 : P} {p : ι -> P}
  证明: by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

Depends on / 依赖: Finset, Finset.affineCombination_indicator_subset, Finset.mem_coe, Fintype, Fintype.sum_extend_by_zero, Set.indicator_apply, affineCombination_indicator_subset, classical, eq_affineCombination_of_mem_affineSpan, indicator, indicator_apply, mem_coe, s.subset_univ, subset_univ, sum_extend_by_zero
-/
theorem eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P}
    (h : p1 in affineSpan k (Set.range p)) :
    exists w : ι -> k, ∑ i, w i = 1 ∧ p1 = Finset.univ.affineCombination k p w := by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

/--
lemma `eq_affineCombination_of_mem_affineSpan_image` / 引理 `eq_affineCombination_of_mem_affineSpan_image`

English:
lemma eq_affineCombination_of_mem_affineSpan_image
  statement: {p₁ : P} {p : ι -> P} {s : Set ι}
  proof: by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i => if hi : i in s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Func

中文:
引理 eq_affineCombination_of_mem_affineSpan_image
  结论: {p₁ : P} {p : ι -> P} {s : 集合 ι}
  证明: by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i => if hi : i in s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Func

Depends on / 依赖: Embedding, Finset, Finset.affineCombination_map, Function, Function.Embedding.coe_subtype, Function.Embedding.subtype, Set.image_eq_range, affineCombination_congr, affineCombination_map, classical, coe_subtype, eq_affineCombination_of_mem_affineSpan, image_eq_range, subtype
-/
lemma eq_affineCombination_of_mem_affineSpan_image {p₁ : P} {p : ι -> P} {s : Set ι}
    (h : p₁ in affineSpan k (p '' s)) :
    exists (fs : Finset ι) (w : ι -> k), ↑fs subseteq s ∧ ∑ i in fs, w i = 1 ∧
      p₁ = fs.affineCombination k p w := by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i => if hi : i in s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Function.Embedding.coe_subtype]
  exact fs'.affineCombination_congr (by simp) (by simp)

/--
lemma `affineCombination_mem_affineSpan_image` / 引理 `affineCombination_mem_affineSpan_image`

English:
lemma affineCombination_mem_affineSpan_image
  statement: [Nontrivial k] {s : Finset ι} {w : ι -> k}
  proof: by
  classical
  rw [Set.image_eq_range]
  let w' : s' -> k := fun i => w i
  have h' : ∑ i in s with i in s', w i = 1 := by
    rw [← h]; rw [← Finset.sum_sdiff (s₁ := {x in s | x in s'}) (s₂ := s) (by simp)]; rw [right_eq_add]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.m

中文:
引理 affineCombination_mem_affineSpan_image
  结论: [非平凡 k] {s : 有限集 ι} {w : ι -> k}
  证明: by
  classical
  rw [Set.image_eq_range]
  let w' : s' -> k := fun i => w i
  have h' : ∑ i in s with i in s', w i = 1 := by
    rw [← h]; rw [← Finset.sum_sdiff (s₁ := {x in s | x in s'}) (s₂ := s) (by simp)]; rw [right_eq_add]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.m

Depends on / 依赖: Finset, Finset.affineCombination_subtype_eq_filte, Finset.mem_filter, Finset.mem_sdiff, Finset.sum_eq_zero, Finset.sum_sdiff, Finset.sum_subtype_eq_sum_filter, Set.image_eq_range, affineCombination_mem_affineSpan, affineCombination_subtype_eq_filte, classical, convert, image_eq_range, mem_filter, mem_sdiff, not_and, right_eq_add, sum_eq_zero, sum_sdiff, sum_subtype_eq_sum_filter
-/
lemma affineCombination_mem_affineSpan_image [Nontrivial k] {s : Finset ι} {w : ι -> k}
    (h : ∑ i in s, w i = 1) {s' : Set ι} (hs' : forall i in s, i ∉ s' -> w i = 0) (p : ι -> P) :
    s.affineCombination k p w in affineSpan k (p '' s') := by
  classical
  rw [Set.image_eq_range]
  let w' : s' -> k := fun i => w i
  have h' : ∑ i in s with i in s', w i = 1 := by
    rw [← h]; rw [← Finset.sum_sdiff (s₁ := {x in s | x in s'}) (s₂ := s) (by simp)]; rw [right_eq_add]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
    exact hs' i hi.1 (hi.2 hi.1)
  rw [← Finset.sum_subtype_eq_sum_filter] at h'
  convert! affineCombination_mem_affineSpan h' (fun x => p x)
  rw [Finset.affineCombination_subtype_eq_filter]; rw [Finset.affineCombination_indicator_subset w p
    (Finset.filter_subset _ _)]
  refine Finset.affineCombination_congr _ (fun i hi => ?_) (fun _ _ => rfl)
  simp_all [Set.indicator_apply]

variable (k V)

/--
theorem `mem_affineSpan_iff_eq_affineCombination` / 定理 `mem_affineSpan_iff_eq_affineCombination`

English:
theorem mem_affineSpan_iff_eq_affineCombination
  given: [Nontrivial k] {p1 : P} {p : ι -> P}
  proof: by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

中文:
定理 mem_affineSpan_iff_eq_affineCombination
  条件: [非平凡 k] {p1 : P} {p : ι -> P}
  证明: by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

Depends on / 依赖: affineCombination_mem_affineSpan, eq_affineCombination_of_mem_affineSpan
-/
theorem mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι -> P} :
    p1 in affineSpan k (Set.range p) ↔
      exists (s : Finset ι) (w : ι -> k), ∑ i in s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

/--
theorem `mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd` / 定理 `mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd`

English:
theorem mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd
  given: [Nontrivial k] (p : ι -> P) (j : ι) (q : P)
  proof: by
  constructor
  · intro hq
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
  · rintro ⟨s, w, rfl⟩
    classical
      let w' : ι -> k := Function.update w j (1 - (s \ {j}).sum w)
 

中文:
定理 mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd
  条件: [非平凡 k] (p : ι -> P) (j : ι) (q : P)
  证明: by
  constructor
  · intro hq
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
  · rintro ⟨s, w, rfl⟩
    classical
      let w' : ι -> k := Function.update w j (1 - (s \ {j}).sum w)
 

Depends on / 依赖: Finset, Finset.insert_eq_of_mem, Finset.sum_insert, Finset.sum_update_of_mem, Finset.sum_update_of_notMem, Function, Function.update, Function.update_self, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, classical, eq_affineCombination_of_mem_affineSpan, insert, insert_eq_of_mem, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, simp_rw, sum_insert, sum_update_of_mem, sum_update_of_notMem, update, update_self
-/
theorem mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd [Nontrivial k] (p : ι -> P) (j : ι) (q : P) :
    q in affineSpan k (Set.range p) ↔
      exists (s : Finset ι) (w : ι -> k), q = s.weightedVSubOfPoint p (p j) w +ᵥ p j := by
  constructor
  · intro hq
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
  · rintro ⟨s, w, rfl⟩
    classical
      let w' : ι -> k := Function.update w j (1 - (s \ {j}).sum w)
      have h₁ : (insert j s).sum w' = 1 := by
        by_cases hj : j in s
        · simp [w', Finset.sum_update_of_mem hj, Finset.insert_eq_of_mem hj]
        · simp_rw [w', Finset.sum_insert hj, Finset.sum_update_of_notMem hj, Function.update_self,
            ← Finset.erase_eq, Finset.erase_eq_of_notMem hj, sub_add_cancel]
      have hww : forall i, i != j -> w i = w' i := by
        intro i hij
        simp [w', hij]
      rw [s.weightedVSubOfPoint_eq_of_weights_eq p j w w' hww]; rw [←
        s.weightedVSubOfPoint_insert w' p j]; rw [←
        (insert j s).affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w' p h₁ (p j)]
      exact affineCombination_mem_affineSpan h₁ p

variable {k V}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineSpan_eq_affineSpan_lineMap_units` / 定理 `affineSpan_eq_affineSpan_lineMap_units`

English:
theorem affineSpan_eq_affineSpan_lineMap_units
  statement: [Nontrivial k] {s : Set P} {p : P} (hp : p in s)
  proof: by
  have : s = Set.range ((↑) : s -> P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> rw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun 

中文:
定理 affineSpan_eq_affineSpan_lineMap_units
  结论: [非平凡 k] {s : 集合 P} {p : P} (hp : p in s)
  证明: by
  have : s = Set.range ((↑) : s -> P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> rw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun 

Depends on / 依赖: Set.range, conv_rhs, le_antisymm, mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd, smul_smul
-/
theorem affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} (hp : p in s)
    (w : s -> Units k) :
    affineSpan k (Set.range fun q : s => AffineMap.lineMap p ↑q (w q : k)) = affineSpan k s := by
  have : s = Set.range ((↑) : s -> P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> rw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun x => μ x * ↑(w x)⁻¹]
    <;> simp [smul_smul]

end AffineSpace'

namespace AffineMap

variable {k : Type*} {V : Type*} (P : Type*) [CommRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι)

-- TODO: define `affineMap.proj`, `affineMap.fst`, `affineMap.snd`
/--
Definition of `weightedVSubOfPoint` / `weightedVSubOfPoint` 的定义

English:
definition weightedVSubOfPoint
  signature: (w : ι -> k)
  body: s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i in s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc, ← sub_add_eq_add_s

中文:
定义 weightedVSubOfPoint
  签名: (w : ι -> k)
  定义体: s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i in s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc, ← sub_add_eq_add_s

Depends on / 依赖: p.fst, p.snd, s.weightedVSubOfPoint, weightedVSubOfPoint
-/
def weightedVSubOfPoint (w : ι -> k) : (ι -> P) × P ->ᵃ[k] V where
  toFun p := s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i in s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc, ← sub_add_eq_add_sub, smul_add, Finset.sum_add_distrib]

end AffineMap
