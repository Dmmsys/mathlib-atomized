/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot, Floris van Doorn, Jireh Loreaux, Eric Wieser,
Yongxi Lin, Louis (Yiyang) Liu
-/
module

public import Mathlib.Topology.Order.OrderClosedExtr
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-!
# The First- and Second-Derivative Tests

We prove the first-derivative test from calculus, in the strong form given on [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#First-derivative_test).

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`.

We prove the second-derivative test using the first-derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMax_of_deriv_Ioo`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `Ioo (a − r) a`
  we have `f′(x) ≥ 0`, and for every `x` in `Ioo a (a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `isLocalMin_of_deriv_Ioo`: The dual of `first_derivative_max`, for minima.

* `isLocalMax_of_deriv`: 1st derivative test for maxima using filters.

* `isLocalMin_of_deriv`: 1st derivative test for minima using filters.

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.


## Tags

derivative test, first-derivative test, second-derivative test, calculus
-/

public section


open Set Topology

/--
lemma `continuousOn_Ioc` / 引理 `continuousOn_Ioc`

English:
lemma continuousOn_Ioc
  statement: {f : Real -> Real} {a b : Real} (h : ContinuousAt f b)
  proof: by
  by_cases! g₀ : a < b
  · exact Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ioc_eq_empty_of_le g₀]

中文:
引理 continuousOn_Ioc
  结论: {f : 实数 -> 实数} {a b : 实数} (h : ContinuousAt f b)
  证明: by
  by_cases! g₀ : a < b
  · exact Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ioc_eq_empty_of_le g₀]
-/
private lemma continuousOn_Ioc {f : Real -> Real} {a b : Real} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) : ContinuousOn f (Ioc a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ioc_eq_empty_of_le g₀]

/--
lemma `continuousOn_Ico` / 引理 `continuousOn_Ico`

English:
lemma continuousOn_Ico
  statement: {f : Real -> Real} {a b : Real} (h : ContinuousAt f a)
  proof: by
  by_cases! g₀ : a < b
  · exact Ioo_union_left g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ico_eq_empty_of_le g₀]

中文:
引理 continuousOn_Ico
  结论: {f : 实数 -> 实数} {a b : 实数} (h : ContinuousAt f a)
  证明: by
  by_cases! g₀ : a < b
  · exact Ioo_union_left g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ico_eq_empty_of_le g₀]
-/
private lemma continuousOn_Ico {f : Real -> Real} {a b : Real} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) : ContinuousOn f (Ico a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_left g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ico_eq_empty_of_le g₀]

/--
lemma `continuousOn_Icc` / 引理 `continuousOn_Icc`

English:
lemma continuousOn_Icc
  statement: {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a)
  proof: by
  by_cases! g₀ : a <= b
  · exact Ioo_union_both g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Icc_eq_empty_of_lt g₀]

中文:
引理 continuousOn_Icc
  结论: {f : 实数 -> 实数} {a b : 实数} (ha : ContinuousAt f a)
  证明: by
  by_cases! g₀ : a <= b
  · exact Ioo_union_both g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Icc_eq_empty_of_lt g₀]
-/
private lemma continuousOn_Icc {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a)
    (hb : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) : ContinuousOn f (Icc a b) := by
  by_cases! g₀ : a <= b
  · exact Ioo_union_both g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Icc_eq_empty_of_lt g₀]

/--
lemma `continuousOn_Iic` / 引理 `continuousOn_Iic`

English:
lemma continuousOn_Iic
  statement: {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
  proof: by
  simp_rw [← Iio_union_right]
  apply hd₀.continuousOn.union_continuousAt isOpen_Iio (by simp [h])

中文:
引理 continuousOn_Iic
  结论: {f : 实数 -> 实数} {b : 实数} (h : ContinuousAt f b)
  证明: by
  simp_rw [← Iio_union_right]
  apply hd₀.continuousOn.union_continuousAt isOpen_Iio (by simp [h])
-/
private lemma continuousOn_Iic {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Iio b)) : ContinuousOn f (Iic b) := by
  simp_rw [← Iio_union_right]
  apply hd₀.continuousOn.union_continuousAt isOpen_Iio (by simp [h])

/--
lemma `continuousOn_Ici` / 引理 `continuousOn_Ici`

English:
lemma continuousOn_Ici
  statement: {f : Real -> Real} {a : Real} (h : ContinuousAt f a)
  proof: by
  rw [← Ioi_union_left]
  exact hd₀.continuousOn.union_continuousAt isOpen_Ioi (by simp [h])

中文:
引理 continuousOn_Ici
  结论: {f : 实数 -> 实数} {a : 实数} (h : ContinuousAt f a)
  证明: by
  rw [← Ioi_union_left]
  exact hd₀.continuousOn.union_continuousAt isOpen_Ioi (by simp [h])
-/
private lemma continuousOn_Ici {f : Real -> Real} {a : Real} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn Real f (Ioi a)) : ContinuousOn f (Ici a) := by
  rw [← Ioi_union_left]
  exact hd₀.continuousOn.union_continuousAt isOpen_Ioi (by simp [h])

/--
lemma `isMaxOn_Ioo_of_deriv` / 引理 `isMaxOn_Ioo_of_deriv`

English:
lemma isMaxOn_Ioo_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (h : ContinuousAt f b)
  proof: by
  refine isMaxOn_Ioo_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

中文:
引理 isMaxOn_Ioo_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (h : ContinuousAt f b)
  证明: by
  refine isMaxOn_Ioo_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ico, continuousOn_Ioc, convex_Ico, convex_Ioc, isMaxOn_Ioo_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Ioo_of_deriv {f : Real -> Real} {a b c : Real} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) :
    IsMaxOn f (Ioo a c) b := by
  refine isMaxOn_Ioo_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/--
lemma `isMaxOn_Ioc_of_deriv` / 引理 `isMaxOn_Ioc_of_deriv`

English:
lemma isMaxOn_Ioc_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  proof: by
  refine isMaxOn_Ioc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMaxOn_Ioc_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  证明: by
  refine isMaxOn_Ioc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ioc, convex_Icc, convex_Ioc, isMaxOn_Ioc_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Ioc_of_deriv {f : Real -> Real} {a b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) :
    IsMaxOn f (Ioc a c) b := by
  refine isMaxOn_Ioc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMaxOn_Ico_of_deriv` / 引理 `isMaxOn_Ico_of_deriv`

English:
lemma isMaxOn_Ico_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_Ico_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

中文:
引理 isMaxOn_Ico_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_Ico_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ico, convex_Icc, convex_Ico, isMaxOn_Ico_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Ico_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) :
    IsMaxOn f (Ico a c) b := by
  refine isMaxOn_Ico_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/--
lemma `isMaxOn_Icc_of_deriv` / 引理 `isMaxOn_Icc_of_deriv`

English:
lemma isMaxOn_Icc_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_Icc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMaxOn_Icc_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_Icc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, convex_Icc, isMaxOn_Icc_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Icc_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Ioo a b))
    (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x)
    (h₁ : forall x in Ioo b c, deriv f x <= 0) : IsMaxOn f (Icc a c) b := by
  refine isMaxOn_Icc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMaxOn_Ioi_of_deriv` / 引理 `isMaxOn_Ioi_of_deriv`

English:
lemma isMaxOn_Ioi_of_deriv
  statement: {f : Real -> Real} {a b : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_Ioi_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMaxOn_Ioi_of_deriv
  结论: {f : 实数 -> 实数} {a b : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_Ioi_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ici, continuousOn_Ioc, convex_Ici, convex_Ioc, isMaxOn_Ioi_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Ioi_of_deriv {f : Real -> Real} {a b : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioi b, deriv f x <= 0) :
    IsMaxOn f (Ioi a) b := by
  refine isMaxOn_Ioi_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isMaxOn_Ici_of_deriv` / 引理 `isMaxOn_Ici_of_deriv`

English:
lemma isMaxOn_Ici_of_deriv
  statement: {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_Ici_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMaxOn_Ici_of_deriv
  结论: {f : 实数 -> 实数} {a b : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_Ici_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ici, convex_Icc, convex_Ici, isMaxOn_Ici_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Ici_of_deriv {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioi b, deriv f x <= 0) :
    IsMaxOn f (Ici a) b := by
  refine isMaxOn_Ici_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isMaxOn_Iio_of_deriv` / 引理 `isMaxOn_Iio_of_deriv`

English:
lemma isMaxOn_Iio_of_deriv
  statement: {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_Iio_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

中文:
引理 isMaxOn_Iio_of_deriv
  结论: {f : 实数 -> 实数} {b c : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_Iio_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ico, continuousOn_Iic, convex_Ico, convex_Iic, isMaxOn_Iio_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Iio_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) :
    IsMaxOn f (Iio c) b := by
  refine isMaxOn_Iio_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/--
lemma `isMaxOn_Iic_of_deriv` / 引理 `isMaxOn_Iic_of_deriv`

English:
lemma isMaxOn_Iic_of_deriv
  statement: {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  proof: by
  refine isMaxOn_Iic_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMaxOn_Iic_of_deriv
  结论: {f : 实数 -> 实数} {b c : 实数} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  证明: by
  refine isMaxOn_Iic_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Iic, convex_Icc, convex_Iic, isMaxOn_Iic_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_Iic_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) :
    IsMaxOn f (Iic c) b := by
  refine isMaxOn_Iic_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMaxOn_univ_of_deriv` / 引理 `isMaxOn_univ_of_deriv`

English:
lemma isMaxOn_univ_of_deriv
  statement: {f : Real -> Real} {b : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMaxOn_univ_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMaxOn_univ_of_deriv
  结论: {f : 实数 -> 实数} {b : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMaxOn_univ_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ici, continuousOn_Iic, convex_Ici, convex_Iic, isMaxOn_univ_of_mono_anti, monotoneOn_of_deriv_nonneg
-/
lemma isMaxOn_univ_of_deriv {f : Real -> Real} {b : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : forall x in Ioi b, deriv f x <= 0) :
    IsMaxOn f univ b := by
  refine isMaxOn_univ_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isLocalMax_of_deriv_Ioo` / 引理 `isLocalMax_of_deriv_Ioo`

English:
lemma isLocalMax_of_deriv_Ioo
  statement: {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁ : b < c)
  proof: (isMaxOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

中文:
引理 isLocalMax_of_deriv_Ioo
  结论: {f : 实数 -> 实数} {a b c : 实数} (g₀ : a < b) (g₁ : b < c)
  证明: (isMaxOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

Depends on / 依赖: Ioo_mem_nhds, isLocalMax, isMaxOn_Ioo_of_deriv
-/
lemma isLocalMax_of_deriv_Ioo {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b))
    (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x)
    (h₁ : forall x in Ioo b c, deriv f x <= 0) : IsLocalMax f b :=
  (isMaxOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

/--
lemma `isMinOn_Ioo_of_deriv` / 引理 `isMinOn_Ioo_of_deriv`

English:
lemma isMinOn_Ioo_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (h : ContinuousAt f b)
  proof: by
  refine isMinOn_Ioo_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

中文:
引理 isMinOn_Ioo_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (h : ContinuousAt f b)
  证明: by
  refine isMinOn_Ioo_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ico, continuousOn_Ioc, convex_Ico, convex_Ioc, isMinOn_Ioo_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Ioo_of_deriv {f : Real -> Real} {a b c : Real} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) :
    IsMinOn f (Ioo a c) b := by
  refine isMinOn_Ioo_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/--
lemma `isMinOn_Ioc_of_deriv` / 引理 `isMinOn_Ioc_of_deriv`

English:
lemma isMinOn_Ioc_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  proof: by
  refine isMinOn_Ioc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMinOn_Ioc_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  证明: by
  refine isMinOn_Ioc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ioc, convex_Icc, convex_Ioc, isMinOn_Ioc_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Ioc_of_deriv {f : Real -> Real} {a b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) :
    IsMinOn f (Ioc a c) b := by
  refine isMinOn_Ioc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMinOn_Ico_of_deriv` / 引理 `isMinOn_Ico_of_deriv`

English:
lemma isMinOn_Ico_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_Ico_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

中文:
引理 isMinOn_Ico_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_Ico_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ico, convex_Icc, convex_Ico, isMinOn_Ico_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Ico_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) :
    IsMinOn f (Ico a c) b := by
  refine isMinOn_Ico_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/--
lemma `isMinOn_Icc_of_deriv` / 引理 `isMinOn_Icc_of_deriv`

English:
lemma isMinOn_Icc_of_deriv
  statement: {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMinOn_Icc_of_deriv
  结论: {f : 实数 -> 实数} {a b c : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, convex_Icc, isMinOn_Icc_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Icc_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Ioo a b))
    (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0)
    (h₁ : forall x in Ioo b c, 0 <= deriv f x) : IsMinOn f (Icc a c) b := by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMinOn_Ioi_of_deriv` / 引理 `isMinOn_Ioi_of_deriv`

English:
lemma isMinOn_Ioi_of_deriv
  statement: {f : Real -> Real} {a b : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_Ioi_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMinOn_Ioi_of_deriv
  结论: {f : 实数 -> 实数} {a b : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_Ioi_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ici, continuousOn_Ioc, convex_Ici, convex_Ioc, isMinOn_Ioi_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Ioi_of_deriv {f : Real -> Real} {a b : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioi b, 0 <= deriv f x) :
    IsMinOn f (Ioi a) b := by
  refine isMinOn_Ioi_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isMinOn_Ici_of_deriv` / 引理 `isMinOn_Ici_of_deriv`

English:
lemma isMinOn_Ici_of_deriv
  statement: {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_Ici_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMinOn_Ici_of_deriv
  结论: {f : 实数 -> 实数} {a b : 实数} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_Ici_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Ici, convex_Icc, convex_Ici, isMinOn_Ici_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Ici_of_deriv {f : Real -> Real} {a b : Real} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioi b, 0 <= deriv f x) :
    IsMinOn f (Ici a) b := by
  refine isMinOn_Ici_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isMinOn_Iio_of_deriv` / 引理 `isMinOn_Iio_of_deriv`

English:
lemma isMinOn_Iio_of_deriv
  statement: {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_Iio_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

中文:
引理 isMinOn_Iio_of_deriv
  结论: {f : 实数 -> 实数} {b c : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_Iio_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ico, continuousOn_Iic, convex_Ico, convex_Iic, isMinOn_Iio_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Iio_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) :
    IsMinOn f (Iio c) b := by
  refine isMinOn_Iio_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/--
lemma `isMinOn_Iic_of_deriv` / 引理 `isMinOn_Iic_of_deriv`

English:
lemma isMinOn_Iic_of_deriv
  statement: {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  proof: by
  refine isMinOn_Iic_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

中文:
引理 isMinOn_Iic_of_deriv
  结论: {f : 实数 -> 实数} {b c : 实数} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
  证明: by
  refine isMinOn_Iic_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Icc, continuousOn_Iic, convex_Icc, convex_Iic, isMinOn_Iic_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_Iic_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b c))
    (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) :
    IsMinOn f (Iic c) b := by
  refine isMinOn_Iic_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/--
lemma `isMinOn_univ_of_deriv` / 引理 `isMinOn_univ_of_deriv`

English:
lemma isMinOn_univ_of_deriv
  statement: {f : Real -> Real} {b : Real} (hb : ContinuousAt f b)
  proof: by
  refine isMinOn_univ_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

中文:
引理 isMinOn_univ_of_deriv
  结论: {f : 实数 -> 实数} {b : 实数} (hb : ContinuousAt f b)
  证明: by
  refine isMinOn_univ_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

Depends on / 依赖: antitoneOn_of_deriv_nonpos, continuousOn_Ici, continuousOn_Iic, convex_Ici, convex_Iic, isMinOn_univ_of_anti_mono, monotoneOn_of_deriv_nonneg
-/
lemma isMinOn_univ_of_deriv {f : Real -> Real} {b : Real} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioi b))
    (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : forall x in Ioi b, 0 <= deriv f x) :
    IsMinOn f univ b := by
  refine isMinOn_univ_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/--
lemma `isLocalMin_of_deriv_Ioo` / 引理 `isLocalMin_of_deriv_Ioo`

English:
lemma isLocalMin_of_deriv_Ioo
  statement: {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁ : b < c)
  proof: (isMinOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMin (Ioo_mem_nhds g₀ g₁)

中文:
引理 isLocalMin_of_deriv_Ioo
  结论: {f : 实数 -> 实数} {a b c : 实数} (g₀ : a < b) (g₁ : b < c)
  证明: (isMinOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMin (Ioo_mem_nhds g₀ g₁)

Depends on / 依赖: Ioo_mem_nhds, isLocalMin, isMinOn_Ioo_of_deriv
-/
lemma isLocalMin_of_deriv_Ioo {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b))
    (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0)
    (h₁ : forall x in Ioo b c, 0 <= deriv f x) : IsLocalMin f b :=
  (isMinOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMin (Ioo_mem_nhds g₀ g₁)

/--
lemma `isLocalMax_of_deriv'` / 引理 `isLocalMax_of_deriv'`

English:
lemma isLocalMax_of_deriv'
  statement: {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
  proof: by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

中文:
引理 isLocalMax_of_deriv'
  结论: {f : 实数 -> 实数} {b : 实数} (h : ContinuousAt f b)
  证明: by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

Depends on / 依赖: differentiableWithinAt, eventually_iff, eventually_iff.mp, isLocalMax_of_deriv_Ioo, nhdsGT_basis, nhdsLT_basis
-/
lemma isLocalMax_of_deriv' {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
    (hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (hd₁ : forallᶠ x in 𝓝[>] b, DifferentiableAt Real f x)
    (h₀ : forallᶠ x in 𝓝[<] b, 0 <= deriv f x) (h₁ : forallᶠ x in 𝓝[>] b, deriv f x <= 0) :
    IsLocalMax f b := by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/--
lemma `isLocalMin_of_deriv'` / 引理 `isLocalMin_of_deriv'`

English:
lemma isLocalMin_of_deriv'
  statement: {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
  proof: by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

中文:
引理 isLocalMin_of_deriv'
  结论: {f : 实数 -> 实数} {b : 实数} (h : ContinuousAt f b)
  证明: by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

Depends on / 依赖: differentiableWithinAt, eventually_iff, eventually_iff.mp, isLocalMin_of_deriv_Ioo, nhdsGT_basis, nhdsLT_basis
-/
lemma isLocalMin_of_deriv' {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
    (hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (hd₁ : forallᶠ x in 𝓝[>] b, DifferentiableAt Real f x)
    (h₀ : forallᶠ x in 𝓝[<] b, deriv f x <= 0) (h₁ : forallᶠ x in 𝓝[>] b, deriv f x >= 0) :
    IsLocalMin f b := by
obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp hd₀.and h₀
obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/--
theorem `isLocalMax_of_deriv` / 定理 `isLocalMax_of_deriv`

English:
theorem isLocalMax_of_deriv
  statement: {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
  proof: isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

中文:
定理 isLocalMax_of_deriv
  结论: {f : 实数 -> 实数} {b : 实数} (h : ContinuousAt f b)
  证明: isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

Depends on / 依赖: isLocalMax_of_deriv, nhdsGT_le_nhdsNE, nhdsLT_le_nhdsNE
-/
theorem isLocalMax_of_deriv {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
    (hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x)
    (h₀ : forallᶠ x in 𝓝[<] b, 0 <= deriv f x) (h₁ : forallᶠ x in 𝓝[>] b, deriv f x <= 0) :
    IsLocalMax f b :=
  isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

/--
theorem `isLocalMin_of_deriv` / 定理 `isLocalMin_of_deriv`

English:
theorem isLocalMin_of_deriv
  statement: {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
  proof: isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

中文:
定理 isLocalMin_of_deriv
  结论: {f : 实数 -> 实数} {b : 实数} (h : ContinuousAt f b)
  证明: isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

Depends on / 依赖: isLocalMin_of_deriv, nhdsGT_le_nhdsNE, nhdsLT_le_nhdsNE
-/
theorem isLocalMin_of_deriv {f : Real -> Real} {b : Real} (h : ContinuousAt f b)
    (hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x)
    (h₀ : forallᶠ x in 𝓝[<] b, deriv f x <= 0) (h₁ : forallᶠ x in 𝓝[>] b, 0 <= deriv f x) :
    IsLocalMin f b :=
  isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

open Filter SignType

section SecondDeriv

variable {f : Real -> Real} {x₀ : Real}

/--
lemma `eventually_nhdsWithin_sign_eq_of_deriv_pos` / 引理 `eventually_nhdsWithin_sign_eq_of_deriv_pos`

English:
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos
  given: (hf : deriv f x₀ > 0) (hx : f x₀ = 0)
  proof: by
  rw [← nhdsNE_sup_pure x₀]; rw [eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff]; rw [mem_singleton_iff]; rw [← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_gt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

中文:
引理 eventually_nhdsWithin_sign_eq_of_deriv_pos
  条件: (hf : deriv f x₀ > 0) (hx : f x₀ = 0)
  证明: by
  rw [← nhdsNE_sup_pure x₀]; rw [eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff]; rw [mem_singleton_iff]; rw [← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_gt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

Depends on / 依赖: Ne.eq_def, differentiableAt_of_deriv_ne_zero, eq_def, eventually, eventually_gt_nhds, eventually_sup, filter_upwards, h_tendsto, h_tendsto.eventually, hasDerivAt, hasDerivAt_iff_tendsto_slope, hasDerivAt_iff_tendsto_slope.mp, lt_or_gt, mem_compl_iff, mem_singleton_iff, ne_of_gt, neg_of_slope_pos, nhdsNE_sup_pure, pos_of_slope_pos, self_mem_nhdsWithin
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) :
    forallᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀) := by
  rw [← nhdsNE_sup_pure x₀]; rw [eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff]; rw [mem_singleton_iff]; rw [← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_gt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

/--
lemma `eventually_nhdsWithin_sign_eq_of_deriv_neg` / 引理 `eventually_nhdsWithin_sign_eq_of_deriv_neg`

English:
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg
  given: (hf : deriv f x₀ < 0) (hx : f x₀ = 0)
  proof: by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)

中文:
引理 eventually_nhdsWithin_sign_eq_of_deriv_neg
  条件: (hf : deriv f x₀ < 0) (hx : f x₀ = 0)
  证明: by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)

Depends on / 依赖: Left.sign_neg, deriv.neg, eventually_nhdsWithin_sign_eq_of_deriv_pos, neg_sub, sign_neg
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x₀ = 0) :
    forallᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x) := by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)

/--
lemma `deriv_neg_left_of_sign_deriv` / 引理 `deriv_neg_left_of_sign_deriv`

English:
lemma deriv_neg_left_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real}
  proof: by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

中文:
引理 deriv_neg_left_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数}
  证明: by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

Depends on / 依赖: filter_upwards, nhdsLT_le_nhdsNE, self_mem_nhdsWithin, sign_eq_neg_one_iff, sub_neg
-/
lemma deriv_neg_left_of_sign_deriv {f : Real -> Real} {x₀ : Real}
    (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) :
    forallᶠ (b : Real) in 𝓝[<] x₀, deriv f b < 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

/--
lemma `deriv_neg_right_of_sign_deriv` / 引理 `deriv_neg_right_of_sign_deriv`

English:
lemma deriv_neg_right_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real}
  proof: by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

中文:
引理 deriv_neg_right_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数}
  证明: by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

Depends on / 依赖: filter_upwards, nhdsGT_le_nhdsNE, self_mem_nhdsWithin, sign_eq_neg_one_iff, sub_neg
-/
lemma deriv_neg_right_of_sign_deriv {f : Real -> Real} {x₀ : Real}
    (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) :
     forallᶠ (b : Real) in 𝓝[>] x₀, deriv f b < 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

/--
lemma `deriv_pos_right_of_sign_deriv` / 引理 `deriv_pos_right_of_sign_deriv`

English:
lemma deriv_pos_right_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real}
  proof: by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

中文:
引理 deriv_pos_right_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数}
  证明: by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

Depends on / 依赖: filter_upwards, nhdsGT_le_nhdsNE, self_mem_nhdsWithin, sign_eq_one_iff, sub_pos
-/
lemma deriv_pos_right_of_sign_deriv {f : Real -> Real} {x₀ : Real}
    (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) :
     forallᶠ (b : Real) in 𝓝[>] x₀, deriv f b > 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/--
lemma `deriv_pos_left_of_sign_deriv` / 引理 `deriv_pos_left_of_sign_deriv`

English:
lemma deriv_pos_left_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real}
  proof: by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

中文:
引理 deriv_pos_left_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数}
  证明: by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

Depends on / 依赖: filter_upwards, nhdsLT_le_nhdsNE, self_mem_nhdsWithin, sign_eq_one_iff, sub_pos
-/
lemma deriv_pos_left_of_sign_deriv {f : Real -> Real} {x₀ : Real}
    (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) :
    forallᶠ (b : Real) in 𝓝[<] x₀, deriv f b > 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/--
theorem `isLocalMax_of_sign_deriv` / 定理 `isLocalMax_of_sign_deriv`

English:
theorem isLocalMax_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real} (h : ContinuousAt f x₀)
  proof: by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx => differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

中文:
定理 isLocalMax_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数} (h : ContinuousAt f x₀)
  证明: by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx => differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

Depends on / 依赖: deriv_neg_right_of_sign_deriv, deriv_pos_left_of_sign_deriv, differentiableAt_of_deriv_ne_zero, eventually_sup, eventually_sup.mpr, hf.mono, hg.mono, hl.mono, hx.ne, isLocalMax_of_deriv, le_of_lt, nhdsLT_sup_nhdsGT, replace
-/
theorem isLocalMax_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h : ContinuousAt f x₀)
    (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) :
    IsLocalMax f x₀ := by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx => differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

/--
theorem `isLocalMin_of_sign_deriv` / 定理 `isLocalMin_of_sign_deriv`

English:
theorem isLocalMin_of_sign_deriv
  statement: {f : Real -> Real} {x₀ : Real} (h : ContinuousAt f x₀)
  proof: by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

中文:
定理 isLocalMin_of_sign_deriv
  结论: {f : 实数 -> 实数} {x₀ : 实数} (h : ContinuousAt f x₀)
  证明: by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

Depends on / 依赖: Left.sign_neg, deriv.neg, h.neg, isLocalMax_of_sign_deriv, neg_neg, neg_sub, sign_neg
-/
theorem isLocalMin_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h : ContinuousAt f x₀)
    (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) :
    IsLocalMin f x₀ := by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

/--
theorem `isLocalMin_of_deriv_deriv_pos` / 定理 `isLocalMin_of_deriv_deriv_pos`

English:
theorem isLocalMin_of_deriv_deriv_pos
  statement: (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
  proof: isLocalMin_of_sign_deriv hc nhdsWithin_le_nhds
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

中文:
定理 isLocalMin_of_deriv_deriv_pos
  结论: (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
  证明: isLocalMin_of_sign_deriv hc nhdsWithin_le_nhds
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

Depends on / 依赖: eventually_nhdsWithin_sign_eq_of_deriv_pos, isLocalMin_of_sign_deriv, nhdsWithin_le_nhds
-/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ :=
isLocalMin_of_sign_deriv hc nhdsWithin_le_nhds
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/--
theorem `isLocalMax_of_deriv_deriv_neg` / 定理 `isLocalMax_of_deriv_deriv_neg`

English:
theorem isLocalMax_of_deriv_deriv_neg
  statement: (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
  proof: by
.neg simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg

中文:
定理 isLocalMax_of_deriv_deriv_neg
  结论: (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
  证明: by
.neg simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg

Depends on / 依赖: hc.neg, isLocalMin_of_deriv_deriv_pos
-/
theorem isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMax f x₀ := by
.neg simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg

end SecondDeriv
