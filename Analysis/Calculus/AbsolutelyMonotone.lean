/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Absolutely monotone functions

A function `f : ℝ → ℝ` is *absolutely monotone* on a set `s` if its iterated derivatives are all
nonnegative on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — there exists a Taylor series for `f` on `s` with nonnegative terms at
  each point of `s`.

## Main results

* `AbsolutelyMonotoneOn.contDiffOn` — the function is `C^∞` on `s`.
* `AbsolutelyMonotoneOn.of_contDiff` — a globally `C^∞` function with nonnegative iterated
  derivatives on `s` is absolutely monotone on `s`.
* `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` — under `UniqueDiffOn`, the definition
  is equivalent to `f` being `C^∞` on `s` with every iterated derivative within `s` nonnegative.
* `AbsolutelyMonotoneOn.add` — closure under addition.
* `AbsolutelyMonotoneOn.smul` — closure under nonnegative scalar multiplication.

## Implementation

The precise definition is phrased via the existence of a Taylor series with nonnegative terms
(`HasFTaylorSeriesUpToOn`) rather than via `iteratedDerivWithin`. This avoids forcing a
`UniqueDiffOn s` hypothesis on every result: without `UniqueDiffOn`, "the" iterated derivative
within `s` is not canonical, but the existence of a Taylor series is intrinsic to `f` and `s`.
When `s` does satisfy `UniqueDiffOn`, the condition reduces to `f` being `C^∞` on `s` with every
iterated derivative within `s` nonnegative.

## References

* [D. V. Widder, *The Laplace Transform*][widder1941]
-/

public section

open Set Filter
open scoped ContDiff

/--
Definition of `AbsolutelyMonotoneOn` / `AbsolutelyMonotoneOn` 的定义

English:
definition AbsolutelyMonotoneOn
  signature: (f : Real -> Real) (s : Set Real)
  body: exists p : Real -> FormalMultilinearSeries Real Real Real,
    HasFTaylorSeriesUpToOn ∞ f p s ∧
    forall (n : Nat) ⦃x : Real⦄, x in s -> 0 <= p x n fun _ => (1 : Real)

中文:
定义 AbsolutelyMonotoneOn
  签名: (f : 实数 -> 实数) (s : 集合 实数)
  定义体: exists p : Real -> FormalMultilinearSeries Real Real Real,
    HasFTaylorSeriesUpToOn ∞ f p s ∧
    forall (n : Nat) ⦃x : Real⦄, x in s -> 0 <= p x n fun _ => (1 : Real)

Depends on / 依赖: FormalMultilinearSeries, HasFTaylorSeriesUpToOn
-/
def AbsolutelyMonotoneOn (f : Real -> Real) (s : Set Real) : Prop :=
  exists p : Real -> FormalMultilinearSeries Real Real Real,
    HasFTaylorSeriesUpToOn ∞ f p s ∧
    forall (n : Nat) ⦃x : Real⦄, x in s -> 0 <= p x n fun _ => (1 : Real)

namespace AbsolutelyMonotoneOn

variable {f g : Real -> Real} {s : Set Real}

/--
theorem `contDiffOn` / 定理 `contDiffOn`

English:
theorem contDiffOn
  given: (hf : AbsolutelyMonotoneOn f s)
  statement: ContDiffOn Real ∞ f s
  proof: by
  obtain ⟨_, hp, _⟩ := hf
  exact hp.contDiffOn

中文:
定理 contDiffOn
  条件: (hf : AbsolutelyMonotoneOn f s)
  结论: ContDiffOn 实数 ∞ f s
  证明: by
  obtain ⟨_, hp, _⟩ := hf
  exact hp.contDiffOn

Depends on / 依赖: contDiffOn, hp.contDiffOn
-/
theorem contDiffOn (hf : AbsolutelyMonotoneOn f s) : ContDiffOn Real ∞ f s := by
  obtain ⟨_, hp, _⟩ := hf
  exact hp.contDiffOn

/--
theorem `of_contDiff` / 定理 `of_contDiff`

English:
theorem of_contDiff
  given: (hf : ContDiff Real ∞ f) (h : forall n : Nat, forall x in s, 0 <= iteratedDeriv n f x)
  proof: by
  refine ⟨ftaylorSeries Real f, (hf.ftaylorSeries).hasFTaylorSeriesUpToOn s, fun n x hx => ?_⟩
  exact iteratedDeriv_eq_iteratedFDeriv (𝕜 := Real) (f := f) ▸ h n x hx

中文:
定理 of_contDiff
  条件: (hf : 连续可微 实数 ∞ f) (h : 对任意 n : 自然数, 对任意 x in s, 0 <= iteratedDeriv n f x)
  证明: by
  refine ⟨ftaylorSeries Real f, (hf.ftaylorSeries).hasFTaylorSeriesUpToOn s, fun n x hx => ?_⟩
  exact iteratedDeriv_eq_iteratedFDeriv (𝕜 := Real) (f := f) ▸ h n x hx

Depends on / 依赖: ftaylorSeries, hasFTaylorSeriesUpToOn, hf.ftaylorSeries, iteratedDeriv_eq_iteratedFDeriv
-/
theorem of_contDiff (hf : ContDiff Real ∞ f) (h : forall n : Nat, forall x in s, 0 <= iteratedDeriv n f x) :
    AbsolutelyMonotoneOn f s := by
  refine ⟨ftaylorSeries Real f, (hf.ftaylorSeries).hasFTaylorSeriesUpToOn s, fun n x hx => ?_⟩
  exact iteratedDeriv_eq_iteratedFDeriv (𝕜 := Real) (f := f) ▸ h n x hx

/--
theorem `iteratedDerivWithin_nonneg` / 定理 `iteratedDerivWithin_nonneg`

English:
theorem iteratedDerivWithin_nonneg
  statement: (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn Real s)
  proof: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  have heq : p x n = iteratedFDerivWithin Real n f s x :=
    hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) hs hx
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← heq]
  exact hp_nn n hx

中文:
定理 iteratedDerivWithin_nonneg
  结论: (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn 实数 s)
  证明: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  have heq : p x n = iteratedFDerivWithin Real n f s x :=
    hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) hs hx
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← heq]
  exact hp_nn n hx

Depends on / 依赖: eq_iteratedFDerivWithin_of_uniqueDiffOn, hp.eq_iteratedFDerivWithin_of_uniqueDiffOn, hp_nn, iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin, le_top, mod_cast
-/
theorem iteratedDerivWithin_nonneg (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn Real s)
    (n : Nat) {x : Real} (hx : x in s) : 0 <= iteratedDerivWithin n f s x := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  have heq : p x n = iteratedFDerivWithin Real n f s x :=
    hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) hs hx
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← heq]
  exact hp_nn n hx

/--
theorem `iff_iteratedDerivWithin_nonneg` / 定理 `iff_iteratedDerivWithin_nonneg`

English:
theorem iff_iteratedDerivWithin_nonneg
  given: (hs : UniqueDiffOn Real s)
  proof: by
  refine ⟨fun hf => ⟨hf.contDiffOn, fun n x hx => hf.iteratedDerivWithin_nonneg hs n hx⟩, ?_⟩
  rintro ⟨hcont, hnn⟩
  refine ⟨ftaylorSeriesWithin Real f s, hcont.ftaylorSeriesWithin hs, fun n x hx => ?_⟩
  exact iteratedDerivWithin_eq_iteratedFDerivWithin (𝕜 := Real) (f := f) (s := s) ▸ hnn n x h

中文:
定理 iff_iteratedDerivWithin_nonneg
  条件: (hs : UniqueDiffOn 实数 s)
  证明: by
  refine ⟨fun hf => ⟨hf.contDiffOn, fun n x hx => hf.iteratedDerivWithin_nonneg hs n hx⟩, ?_⟩
  rintro ⟨hcont, hnn⟩
  refine ⟨ftaylorSeriesWithin Real f s, hcont.ftaylorSeriesWithin hs, fun n x hx => ?_⟩
  exact iteratedDerivWithin_eq_iteratedFDerivWithin (𝕜 := Real) (f := f) (s := s) ▸ hnn n x h

Depends on / 依赖: contDiffOn, ftaylorSeriesWithin, hcont.ftaylorSeriesWithin, hf.contDiffOn, hf.iteratedDerivWithin_nonneg, iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_nonneg
-/
theorem iff_iteratedDerivWithin_nonneg (hs : UniqueDiffOn Real s) :
    AbsolutelyMonotoneOn f s ↔
      ContDiffOn Real ∞ f s ∧ forall n : Nat, forall x in s, 0 <= iteratedDerivWithin n f s x := by
  refine ⟨fun hf => ⟨hf.contDiffOn, fun n x hx => hf.iteratedDerivWithin_nonneg hs n hx⟩, ?_⟩
  rintro ⟨hcont, hnn⟩
  refine ⟨ftaylorSeriesWithin Real f s, hcont.ftaylorSeriesWithin hs, fun n x hx => ?_⟩
  exact iteratedDerivWithin_eq_iteratedFDerivWithin (𝕜 := Real) (f := f) (s := s) ▸ hnn n x hx

/-! ### Closure properties -/

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s)
  proof: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  obtain ⟨q, hq, hq_nn⟩ := hg
  refine ⟨p + q, hp.add hq, fun n x hx => ?_⟩
  simp only [Pi.add_apply, FormalMultilinearSeries.add_apply, add_apply]
  exact add_nonneg (hp_nn n hx) (hq_nn n hx)

中文:
定理 add
  条件: (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s)
  证明: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  obtain ⟨q, hq, hq_nn⟩ := hg
  refine ⟨p + q, hp.add hq, fun n x hx => ?_⟩
  simp only [Pi.add_apply, FormalMultilinearSeries.add_apply, add_apply]
  exact add_nonneg (hp_nn n hx) (hq_nn n hx)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.add_apply, Pi.add_apply, add_apply, add_nonneg, hp.add, hp_nn, hq_nn
-/
theorem add (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f + g) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  obtain ⟨q, hq, hq_nn⟩ := hg
  refine ⟨p + q, hp.add hq, fun n x hx => ?_⟩
  simp only [Pi.add_apply, FormalMultilinearSeries.add_apply, add_apply]
  exact add_nonneg (hp_nn n hx) (hq_nn n hx)

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: {c : Real} (hf : AbsolutelyMonotoneOn f s) (hc : 0 <= c)
  proof: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  -- Witness: post-composition by the CLM `y ↦ c * y`.
  set T : Real ->L[Real] Real := c • ContinuousLinearMap.id Real Real with hT
  have hcomp : (T ∘ f) = c • f := by ext x; simp [hT, smul_eq_mul]
  refine ⟨_, hcomp ▸ hp.continuousLinearMap_comp T, fun n x hx => ?

中文:
定理 smul
  条件: {c : 实数} (hf : AbsolutelyMonotoneOn f s) (hc : 0 <= c)
  证明: by
  obtain ⟨p, hp, hp_nn⟩ := hf
  -- Witness: post-composition by the CLM `y ↦ c * y`.
  set T : Real ->L[Real] Real := c • ContinuousLinearMap.id Real Real with hT
  have hcomp : (T ∘ f) = c • f := by ext x; simp [hT, smul_eq_mul]
  refine ⟨_, hcomp ▸ hp.continuousLinearMap_comp T, fun n x hx => ?

Depends on / 依赖: hp_nn
-/
theorem smul {c : Real} (hf : AbsolutelyMonotoneOn f s) (hc : 0 <= c) :
    AbsolutelyMonotoneOn (c • f) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  -- Witness: post-composition by the CLM `y ↦ c * y`.
  set T : Real ->L[Real] Real := c • ContinuousLinearMap.id Real Real with hT
  have hcomp : (T ∘ f) = c • f := by ext x; simp [hT, smul_eq_mul]
  refine ⟨_, hcomp ▸ hp.continuousLinearMap_comp T, fun n x hx => ?_⟩
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, hT,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  exact mul_nonneg hc (hp_nn n hx)

end AbsolutelyMonotoneOn
