/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Symmetry of the second derivative

We show that, over the reals, the second derivative is symmetric.

The most precise result is `Convex.second_derivative_within_at_symmetric`. It asserts that,
if a function is differentiable inside a convex set `s` with nonempty interior, and has a second
derivative within `s` at a point `x`, then this second derivative at `x` is symmetric. Note that
this result does not require continuity of the first derivative.

The following particular cases of this statement are especially relevant:

`second_derivative_symmetric_of_eventually` asserts that, if a function is differentiable on a
neighborhood of `x`, and has a second derivative at `x`, then this second derivative is symmetric.

`second_derivative_symmetric` asserts that, if a function is differentiable, and has a second
derivative at `x`, then this second derivative is symmetric.

There statements are given over `ℝ` or `ℂ`, the general version being deduced from the real
version. We also give statements in terms of `fderiv` and `fderivWithin`, called respectively
`ContDiffAt.isSymmSndFDerivAt` and `ContDiffWithinAt.isSymmSndFDerivWithinAt` (the latter
requiring that the point under consideration is accumulated by points in the interior of the set).
These are written using ad hoc predicates `IsSymmSndFDerivAt` and `IsSymmSndFDerivWithinAt`, which
increase readability of statements in differential geometry where they show up a lot.

We also deduce statements over an arbitrary field, requiring that the function is `C^2` if the field
is `ℝ` or `ℂ`, and analytic otherwise. Formally, we assume that the function is `C^n`
with `minSmoothness 𝕜 2 ≤ n`, where `minSmoothness 𝕜 i` is `i` if `𝕜` is `ℝ` or `ℂ`,
and `ω` otherwise.

## Implementation note

For the proof, we obtain an asymptotic expansion to order two of `f (x + v + w) - f (x + v)`, by
using the mean value inequality applied to a suitable function along the
segment `[x + v, x + v + w]`. This expansion involves `f'' ⬝ w` as we move along a segment directed
by `w` (see `Convex.taylor_approx_two_segment`).

Consider the alternate sum `f (x + v + w) + f x - f (x + v) - f (x + w)`, corresponding to the
values of `f` along a rectangle based at `x` with sides `v` and `w`. One can write it using the two
sides directed by `w`, as `(f (x + v + w) - f (x + v)) - (f (x + w) - f x)`. Together with the
previous asymptotic expansion, one deduces that it equals `f'' v w + o(1)` when `v, w` tends to `0`.
Exchanging the roles of `v` and `w`, one instead gets an asymptotic expansion `f'' w v`, from which
the equality `f'' v w = f'' w v` follows.

In our most general statement, we only assume that `f` is differentiable inside a convex set `s`, so
a few modifications have to be made. Since we don't assume continuity of `f` at `x`, we consider
instead the rectangle based at `x + v + w` with sides `v` and `w`,
in `Convex.isLittleO_alternate_sum_square`, but the argument is essentially the same. It only works
when `v` and `w` both point towards the interior of `s`, to make sure that all the sides of the
rectangle are contained in `s` by convexity. The general case follows by linearity, though.
-/

@[expose] public section


open Asymptotics Set Filter

open scoped Topology ContDiff

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s t : Set E} {f : E -> F} {x : E}

variable (𝕜) in
/--
Definition of `IsSymmSndFDerivWithinAt` / `IsSymmSndFDerivWithinAt` 的定义

English:
definition IsSymmSndFDerivWithinAt
  signature: (f : E -> F) (s : Set E) (x : E)
  body: forall v w, fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v

中文:
定义 IsSymmSndFDerivWithinAt
  签名: (f : E -> F) (s : 集合 E) (x : E)
  定义体: forall v w, fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v

Depends on / 依赖: fderivWithin
-/
def IsSymmSndFDerivWithinAt (f : E -> F) (s : Set E) (x : E) : Prop :=
  forall v w, fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v

variable (𝕜) in
/--
Definition of `IsSymmSndFDerivAt` / `IsSymmSndFDerivAt` 的定义

English:
definition IsSymmSndFDerivAt
  signature: (f : E -> F) (x : E)
  body: forall v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v

中文:
定义 IsSymmSndFDerivAt
  签名: (f : E -> F) (x : E)
  定义体: forall v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v

Depends on / 依赖: fderiv
-/
def IsSymmSndFDerivAt (f : E -> F) (x : E) : Prop :=
  forall v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v

/--
lemma `IsSymmSndFDerivWithinAt.eq` / 引理 `IsSymmSndFDerivWithinAt.eq`

English:
lemma IsSymmSndFDerivWithinAt.eq
  given: (h : IsSymmSndFDerivWithinAt 𝕜 f s x) (v w : E)
  proof: h v w

中文:
引理 IsSymmSndFDerivWithinAt.eq
  条件: (h : IsSymmSndFDerivWithinAt 𝕜 f s x) (v w : E)
  证明: h v w
-/
protected lemma IsSymmSndFDerivWithinAt.eq (h : IsSymmSndFDerivWithinAt 𝕜 f s x) (v w : E) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v :=
  h v w

/--
lemma `IsSymmSndFDerivAt.eq` / 引理 `IsSymmSndFDerivAt.eq`

English:
lemma IsSymmSndFDerivAt.eq
  proof: h v w

中文:
引理 IsSymmSndFDerivAt.eq
  证明: h v w
-/
protected lemma IsSymmSndFDerivAt.eq
    (h : IsSymmSndFDerivAt 𝕜 f x) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v :=
  h v w

/--
lemma `fderivWithin_fderivWithin_eq_of_mem_nhdsWithin` / 引理 `fderivWithin_fderivWithin_eq_of_mem_nhdsWithin`

English:
lemma fderivWithin_fderivWithin_eq_of_mem_nhdsWithin
  statement: (h : t in 𝓝[s] x)
  proof: by
  have A : forallᶠ y in 𝓝[s] x, fderivWithin 𝕜 f s y = fderivWithin 𝕜 f t y := by
    have : forallᶠ y in 𝓝[s] x, ContDiffWithinAt 𝕜 2 f t y :=
      nhdsWithin_le_iff.2 h (nhdsWithin_mono _ (subset_insert x t) (hf.eventually (by simp)))
    filter_upwards [self_mem_nhdsWithin, this, eventually_e

中文:
引理 fderivWithin_fderivWithin_eq_of_mem_nhdsWithin
  结论: (h : t in 𝓝[s] x)
  证明: by
  have A : forallᶠ y in 𝓝[s] x, fderivWithin 𝕜 f s y = fderivWithin 𝕜 f t y := by
    have : forallᶠ y in 𝓝[s] x, ContDiffWithinAt 𝕜 2 f t y :=
      nhdsWithin_le_iff.2 h (nhdsWithin_mono _ (subset_insert x t) (hf.eventually (by simp)))
    filter_upwards [self_mem_nhdsWithin, this, eventually_e

Depends on / 依赖: ContDiffWithinAt, differentiableWithinAt, eventually, eventually_eventually_nhdsWithin, fderivWithin, fderivWithin_of_mem_nhdsWithin, filter_upwards, hf.eventually, nhdsWithin_le_iff, nhdsWithin_mono, self_mem_nhdsWithin, subset_insert, two_ne_zero, y.differentiableWithinAt
-/
lemma fderivWithin_fderivWithin_eq_of_mem_nhdsWithin (h : t in 𝓝[s] x)
    (hf : ContDiffWithinAt 𝕜 2 f t x) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x in s) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := by
  have A : forallᶠ y in 𝓝[s] x, fderivWithin 𝕜 f s y = fderivWithin 𝕜 f t y := by
    have : forallᶠ y in 𝓝[s] x, ContDiffWithinAt 𝕜 2 f t y :=
      nhdsWithin_le_iff.2 h (nhdsWithin_mono _ (subset_insert x t) (hf.eventually (by simp)))
    filter_upwards [self_mem_nhdsWithin, this, eventually_eventually_nhdsWithin.2 h]
      with y hy h'y h''y
    exact fderivWithin_of_mem_nhdsWithin h''y (hs y hy) (h'y.differentiableWithinAt two_ne_zero)
  have : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq A
    exact fderivWithin_of_mem_nhdsWithin h (hs x hx) (hf.differentiableWithinAt two_ne_zero)
  rw [this]
  apply fderivWithin_of_mem_nhdsWithin h (hs x hx)
  exact (hf.fderivWithin_right (m := 1) ht le_rfl
    (mem_of_mem_nhdsWithin hx h)).differentiableWithinAt one_ne_zero

/--
lemma `fderivWithin_fderivWithin_eq_of_eventuallyEq` / 引理 `fderivWithin_fderivWithin_eq_of_eventuallyEq`

English:
lemma fderivWithin_fderivWithin_eq_of_eventuallyEq
  given: (h : s =ᶠ[𝓝 x] t)
  proof: calc
  fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x
    = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x :=
      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
  _ = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := fderivWithin_congr_set h

中文:
引理 fderivWithin_fderivWithin_eq_of_eventuallyEq
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: calc
  fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x
    = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x :=
      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
  _ = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := fderivWithin_congr_set h
-/
lemma fderivWithin_fderivWithin_eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := calc
  fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x
    = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x :=
      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
  _ = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := fderivWithin_congr_set h

/--
lemma `fderivWithin_fderivWithin_eq_of_mem_nhds` / 引理 `fderivWithin_fderivWithin_eq_of_mem_nhds`

English:
lemma fderivWithin_fderivWithin_eq_of_mem_nhds
  statement: {f : E -> F} {x : E} {s : Set E}
  proof: by
  simp only [← fderivWithin_univ]
  apply fderivWithin_fderivWithin_eq_of_eventuallyEq
  simp [h]

中文:
引理 fderivWithin_fderivWithin_eq_of_mem_nhds
  结论: {f : E -> F} {x : E} {s : 集合 E}
  证明: by
  simp only [← fderivWithin_univ]
  apply fderivWithin_fderivWithin_eq_of_eventuallyEq
  simp [h]

Depends on / 依赖: fderivWithin_fderivWithin_eq_of_eventuallyEq, fderivWithin_univ
-/
lemma fderivWithin_fderivWithin_eq_of_mem_nhds {f : E -> F} {x : E} {s : Set E}
    (h : s in 𝓝 x) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderiv 𝕜 (fderiv 𝕜 f) x := by
  simp only [← fderivWithin_univ]
  apply fderivWithin_fderivWithin_eq_of_eventuallyEq
  simp [h]

/--
lemma `isSymmSndFDerivWithinAt_univ` / 引理 `isSymmSndFDerivWithinAt_univ`

English:
lemma isSymmSndFDerivWithinAt_univ
  proof: by
  simp [IsSymmSndFDerivWithinAt, IsSymmSndFDerivAt]

中文:
引理 isSymmSndFDerivWithinAt_univ
  证明: by
  simp [IsSymmSndFDerivWithinAt, IsSymmSndFDerivAt]
-/
@[simp] lemma isSymmSndFDerivWithinAt_univ :
    IsSymmSndFDerivWithinAt 𝕜 f univ x ↔ IsSymmSndFDerivAt 𝕜 f x := by
  simp [IsSymmSndFDerivWithinAt, IsSymmSndFDerivAt]

/--
theorem `IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin` / 定理 `IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin`

English:
theorem IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin
  statement: (h : IsSymmSndFDerivWithinAt 𝕜 f t x)
  proof: by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hst hf hs ht hx]
  exact h v w

中文:
定理 IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin
  结论: (h : IsSymmSndFDerivWithinAt 𝕜 f t x)
  证明: by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hst hf hs ht hx]
  exact h v w

Depends on / 依赖: fderivWithin_fderivWithin_eq_of_mem_nhdsWithin
-/
theorem IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin (h : IsSymmSndFDerivWithinAt 𝕜 f t x)
    (hst : t in 𝓝[s] x) (hf : ContDiffWithinAt 𝕜 2 f t x)
    (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x in s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hst hf hs ht hx]
  exact h v w

/--
theorem `IsSymmSndFDerivWithinAt.congr_set` / 定理 `IsSymmSndFDerivWithinAt.congr_set`

English:
theorem IsSymmSndFDerivWithinAt.congr_set
  statement: (h : IsSymmSndFDerivWithinAt 𝕜 f s x)
  proof: by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_eventuallyEq hst.symm]
  exact h v w

中文:
定理 IsSymmSndFDerivWithinAt.congr_set
  结论: (h : IsSymmSndFDerivWithinAt 𝕜 f s x)
  证明: by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_eventuallyEq hst.symm]
  exact h v w

Depends on / 依赖: fderivWithin_fderivWithin_eq_of_eventuallyEq, hst.symm
-/
theorem IsSymmSndFDerivWithinAt.congr_set (h : IsSymmSndFDerivWithinAt 𝕜 f s x)
    (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt 𝕜 f t x := by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_eventuallyEq hst.symm]
  exact h v w

/--
theorem `isSymmSndFDerivWithinAt_congr_set` / 定理 `isSymmSndFDerivWithinAt_congr_set`

English:
theorem isSymmSndFDerivWithinAt_congr_set
  given: (hst : s =ᶠ[𝓝 x] t)
  proof: ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

中文:
定理 isSymmSndFDerivWithinAt_congr_set
  条件: (hst : s =ᶠ[𝓝 x] t)
  证明: ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

Depends on / 依赖: congr_set, h.congr_set, hst.symm
-/
theorem isSymmSndFDerivWithinAt_congr_set (hst : s =ᶠ[𝓝 x] t) :
    IsSymmSndFDerivWithinAt 𝕜 f s x ↔ IsSymmSndFDerivWithinAt 𝕜 f t x :=
  ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

/--
theorem `IsSymmSndFDerivAt.isSymmSndFDerivWithinAt` / 定理 `IsSymmSndFDerivAt.isSymmSndFDerivWithinAt`

English:
theorem IsSymmSndFDerivAt.isSymmSndFDerivWithinAt
  statement: (h : IsSymmSndFDerivAt 𝕜 f x)
  proof: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at h hf
  exact h.mono_of_mem_nhdsWithin univ_mem hf hs uniqueDiffOn_univ hx

中文:
定理 IsSymmSndFDerivAt.isSymmSndFDerivWithinAt
  结论: (h : IsSymmSndFDerivAt 𝕜 f x)
  证明: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at h hf
  exact h.mono_of_mem_nhdsWithin univ_mem hf hs uniqueDiffOn_univ hx

Depends on / 依赖: contDiffWithinAt_univ, h.mono_of_mem_nhdsWithin, isSymmSndFDerivWithinAt_univ, mono_of_mem_nhdsWithin, uniqueDiffOn_univ, univ_mem
-/
theorem IsSymmSndFDerivAt.isSymmSndFDerivWithinAt (h : IsSymmSndFDerivAt 𝕜 f x)
    (hf : ContDiffAt 𝕜 2 f x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at h hf
  exact h.mono_of_mem_nhdsWithin univ_mem hf hs uniqueDiffOn_univ hx

/--
theorem `isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin` / 定理 `isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin`

English:
theorem isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin
  given: (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  proof: by
  simp_rw [IsSymmSndFDerivWithinAt, ContinuousMultilinearMap.ext_iff, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi]
  simp [iteratedFDerivWithin_two_apply f hs hx, eq_comm]

中文:
定理 isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin
  条件: (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  证明: by
  simp_rw [IsSymmSndFDerivWithinAt, ContinuousMultilinearMap.ext_iff, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi]
  simp [iteratedFDerivWithin_two_apply f hs hx, eq_comm]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.ext_iff, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, IsSymmSndFDerivWithinAt, eq_comm, ext_iff, forall_fin_succ_pi, forall_fin_zero_pi, iteratedFDerivWithin_two_apply, simp_rw
-/
theorem isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x ↔
      (iteratedFDerivWithin 𝕜 2 f s x).domDomCongr Fin.revPerm =
        iteratedFDerivWithin 𝕜 2 f s x := by
  simp_rw [IsSymmSndFDerivWithinAt, ContinuousMultilinearMap.ext_iff, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi]
  simp [iteratedFDerivWithin_two_apply f hs hx, eq_comm]

/--
theorem `isSymmSndFDerivAt_iff_iteratedFDeriv` / 定理 `isSymmSndFDerivAt_iff_iteratedFDeriv`

English:
theorem isSymmSndFDerivAt_iff_iteratedFDeriv
  proof: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ _)

中文:
定理 isSymmSndFDerivAt_iff_iteratedFDeriv
  证明: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ _)

Depends on / 依赖: isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin, isSymmSndFDerivWithinAt_univ, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem isSymmSndFDerivAt_iff_iteratedFDeriv :
    IsSymmSndFDerivAt 𝕜 f x ↔
      (iteratedFDeriv 𝕜 2 f x).domDomCongr Fin.revPerm = iteratedFDeriv 𝕜 2 f x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ _)

/--
theorem `IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons` / 定理 `IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons`

English:
theorem IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons
  statement: {x v w : E}
  proof: by
  simp_rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.domDomCongr_apply] at hf
  convert! hf ![w, v] using 2
  ext i
  fin_cases i <;> simp

中文:
定理 IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons
  结论: {x v w : E}
  证明: by
  simp_rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.domDomCongr_apply] at hf
  convert! hf ![w, v] using 2
  ext i
  fin_cases i <;> simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.ext_iff, convert, domDomCongr_apply, ext_iff, fin_cases, isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin, simp_rw
-/
theorem IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons {x v w : E}
    {hf : IsSymmSndFDerivWithinAt 𝕜 f s x} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 2 f s x ![v, w] = iteratedFDerivWithin 𝕜 2 f s x ![w, v] := by
  simp_rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.domDomCongr_apply] at hf
  convert! hf ![w, v] using 2
  ext i
  fin_cases i <;> simp

/--
theorem `IsSymmSndFDerivAt.iteratedFDeriv_cons` / 定理 `IsSymmSndFDerivAt.iteratedFDeriv_cons`

English:
theorem IsSymmSndFDerivAt.iteratedFDeriv_cons
  given: {x v w : E} {hf : IsSymmSndFDerivAt 𝕜 f x}
  proof: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ] at *
  exact hf.iteratedFDerivWithin_cons uniqueDiffOn_univ (mem_univ _)

中文:
定理 IsSymmSndFDerivAt.iteratedFDeriv_cons
  条件: {x v w : E} {hf : IsSymmSndFDerivAt 𝕜 f x}
  证明: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ] at *
  exact hf.iteratedFDerivWithin_cons uniqueDiffOn_univ (mem_univ _)

Depends on / 依赖: hf.iteratedFDerivWithin_cons, isSymmSndFDerivWithinAt_univ, iteratedFDerivWithin_cons, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem IsSymmSndFDerivAt.iteratedFDeriv_cons {x v w : E} {hf : IsSymmSndFDerivAt 𝕜 f x} :
    iteratedFDeriv 𝕜 2 f x ![v, w] = iteratedFDeriv 𝕜 2 f x ![w, v] := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ] at *
  exact hf.iteratedFDerivWithin_cons uniqueDiffOn_univ (mem_univ _)

/--
theorem `ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega` / 定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega`

English:
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega
  statement: (hf : ContDiffWithinAt 𝕜 ω f s x)
  proof: by
  rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx]
  exact hf.domDomCongr_iteratedFDerivWithin hs hx _

中文:
定理 ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega
  结论: (hf : ContDiffWithinAt 𝕜 ω f s x)
  证明: by
  rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx]
  exact hf.domDomCongr_iteratedFDerivWithin hs hx _

Depends on / 依赖: domDomCongr_iteratedFDerivWithin, hf.domDomCongr_iteratedFDerivWithin, isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin
-/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega (hf : ContDiffWithinAt 𝕜 ω f s x)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx]
  exact hf.domDomCongr_iteratedFDerivWithin hs hx _

/--
theorem `ContDiffAt.isSymmSndFDerivAt_of_omega` / 定理 `ContDiffAt.isSymmSndFDerivAt_of_omega`

English:
theorem ContDiffAt.isSymmSndFDerivAt_of_omega
  given: (hf : ContDiffAt 𝕜 ω f x)
  proof: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at hf ⊢
  exact hf.isSymmSndFDerivWithinAt_of_omega uniqueDiffOn_univ (mem_univ _)

中文:
定理 ContDiffAt.isSymmSndFDerivAt_of_omega
  条件: (hf : ContDiffAt 𝕜 ω f x)
  证明: by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at hf ⊢
  exact hf.isSymmSndFDerivWithinAt_of_omega uniqueDiffOn_univ (mem_univ _)

Depends on / 依赖: contDiffWithinAt_univ, hf.isSymmSndFDerivWithinAt_of_omega, isSymmSndFDerivWithinAt_of_omega, isSymmSndFDerivWithinAt_univ, mem_univ, uniqueDiffOn_univ
-/
theorem ContDiffAt.isSymmSndFDerivAt_of_omega (hf : ContDiffAt 𝕜 ω f x) :
    IsSymmSndFDerivAt 𝕜 f x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at hf ⊢
  exact hf.isSymmSndFDerivWithinAt_of_omega uniqueDiffOn_univ (mem_univ _)

end General

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F]
  [NormedSpace Real F] {s : Set E} (s_conv : Convex Real s) {f : E -> F} {f' : E -> E ->L[Real] F}
  {f'' : E ->L[Real] E ->L[Real] F} (hf : forall x in interior s, HasFDerivAt f (f' x) x) {x : E} (xs : x in s)
  (hx : HasFDerivWithinAt f' f'' (interior s) x)

section
include s_conv hf xs hx

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Convex.taylor_approx_two_segment` / 定理 `Convex.taylor_approx_two_segment`

English:
theorem Convex.taylor_approx_two_segment
  statement: {v w : E} (hv : x + v in interior s)
  proof: by
  -- it suffices to check that the expression is bounded by `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2` for
  -- small enough `h`, for any positive `ε`.
  refine IsLittleO.trans_isBigO
    (isLittleO_iff.2 fun ε εpos => ?_) (isBigO_const_mul_self ((‖v‖ + ‖w‖) * ‖w‖) _ _)
  -- consider a ball of radius `δ` ar

中文:
定理 凸.taylor_approx_two_segment
  结论: {v w : E} (hv : x + v in interior s)
  证明: by
  -- it suffices to check that the expression is bounded by `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2` for
  -- small enough `h`, for any positive `ε`.
  refine IsLittleO.trans_isBigO
    (isLittleO_iff.2 fun ε εpos => ?_) (isBigO_const_mul_self ((‖v‖ + ‖w‖) * ‖w‖) _ _)
  -- consider a ball of radius `δ` ar
-/
theorem Convex.taylor_approx_two_segment {v w : E} (hv : x + v in interior s)
    (hw : x + v + w in interior s) :
    (fun h : Real => f (x + h • v + h • w)
        - f (x + h • v) - h • f' x w - h ^ 2 • f'' v w - (h ^ 2 / 2) • f'' w w) =o[𝓝[>] 0]
      fun h => h ^ 2 := by
  -- it suffices to check that the expression is bounded by `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2` for
  -- small enough `h`, for any positive `ε`.
  refine IsLittleO.trans_isBigO
    (isLittleO_iff.2 fun ε εpos => ?_) (isBigO_const_mul_self ((‖v‖ + ‖w‖) * ‖w‖) _ _)
  -- consider a ball of radius `δ` around `x` in which the Taylor approximation for `f''` is
  -- good up to `δ`.
  rw [hasFDerivWithinAt_iff_isLittleO]; rw [isLittleO_iff] at hx
  rcases Metric.mem_nhdsWithin_iff.1 (hx εpos) with ⟨δ, δpos, sδ⟩
  have E1 : forallᶠ h in 𝓝[>] (0 : Real), h * (‖v‖ + ‖w‖) < δ := by
    have : Filter.Tendsto (fun h => h * (‖v‖ + ‖w‖)) (𝓝[>] (0 : Real)) (𝓝 (0 * (‖v‖ + ‖w‖))) :=
      (continuous_id.mul continuous_const).continuousWithinAt
    apply (tendsto_order.1 this).2 δ
    simpa only [zero_mul] using δpos
  have E2 : forallᶠ h in 𝓝[>] (0 : Real), (h : Real) < 1 :=
mem_nhdsWithin_of_mem_nhds Iio_mem_nhds zero_lt_one
  filter_upwards [E1, E2, self_mem_nhdsWithin] with h hδ h_lt_1 hpos
  -- we consider `h` small enough that all points under consideration belong to this ball,
  -- and also with `0 < h < 1`.
  replace hpos : 0 < h := hpos
  have xt_mem : forall t in Icc (0 : Real) 1, x + h • v + (t * h) • w in interior s := by
    intro t ht
    have : x + h • v in interior s := s_conv.add_smul_mem_interior xs hv ⟨hpos, h_lt_1.le⟩
    rw [← smul_smul]
    apply s_conv.interior.add_smul_mem this _ ht
    rw [add_assoc] at hw
    convert! s_conv.add_smul_mem_interior xs hw ⟨hpos, h_lt_1.le⟩ using 1
    module
  -- define a function `g` on `[0,1]` (identified with `[v, v + w]`) such that `g 1 - g 0` is the
  -- quantity to be estimated. We will check that its derivative is given by an explicit
  -- expression `g'`, that we can bound. Then the desired bound for `g 1 - g 0` follows from the
  -- mean value inequality.
  let g t :=
    f (x + h • v + (t * h) • w) - (t * h) • f' x w - (t * h ^ 2) • f'' v w -
      ((t * h) ^ 2 / 2) • f'' w w
  set g' := fun t =>
    f' (x + h • v + (t * h) • w) (h • w) - h • f' x w - h ^ 2 • f'' v w - (t * h ^ 2) • f'' w w
    with hg'
  -- check that `g'` is the derivative of `g`, by a straightforward computation
  have g_deriv : forall t in Icc (0 : Real) 1, HasDerivWithinAt g (g' t) (Icc 0 1) t := by
    intro t ht
    apply_rules [HasDerivWithinAt.sub, HasDerivWithinAt.add]
    · refine (hf _ ?_).comp_hasDerivWithinAt _ ?_
      · exact xt_mem t ht
      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.const_add, HasDerivAt.smul_const,
        hasDerivAt_mul_const]
    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
    · suffices H : HasDerivWithinAt (fun u => ((u * h) ^ 2 / 2) • f'' w w)
          ((((2 : Nat) : Real) * (t * h) ^ (2 - 1) * (1 * h) / 2) • f'' w w) (Icc 0 1) t by
        convert H
        ring
      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_id',
        HasDerivAt.pow, HasDerivAt.mul_const]
  -- check that `g'` is uniformly bounded, with a suitable bound `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2`.
  have g'_bound : forall t in Ico (0 : Real) 1, ‖g' t‖ <= ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
    intro t ht
    have I : ‖h • v + (t * h) • w‖ <= h * (‖v‖ + ‖w‖) :=
      calc
        ‖h • v + (t * h) • w‖ <= ‖h • v‖ + ‖(t * h) • w‖ := norm_add_le _ _
        _ = h * ‖v‖ + t * (h * ‖w‖) := by
          simp only [norm_smul, Real.norm_eq_abs, hpos.le, abs_of_nonneg, abs_mul, ht.left,
            mul_assoc]
        _ <= h * ‖v‖ + 1 * (h * ‖w‖) := by gcongr; exact ht.2.le
        _ = h * (‖v‖ + ‖w‖) := by ring
    calc
      ‖g' t‖ = ‖(f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)) (h • w)‖ := by
        rw [hg']
        congrm ‖?_‖
        simp only [sub_apply, add_apply, smul_apply, map_add, map_smul]
        module
      _ <= ‖f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)‖ * ‖h • w‖ :=
        (ContinuousLinearMap.le_opNorm _ _)
      _ <= ε * ‖h • v + (t * h) • w‖ * ‖h • w‖ := by
        gcongr
        have H : x + h • v + (t * h) • w in Metric.ball x δ inter interior s := by
          refine ⟨?_, xt_mem t ⟨ht.1, ht.2.le⟩⟩
          rw [add_assoc]; rw [add_mem_ball_iff_norm]
          exact I.trans_lt hδ
        simpa only [mem_ofPred_eq, add_assoc x, add_sub_cancel_left] using sδ H
      _ <= ε * (‖h • v‖ + ‖h • w‖) * ‖h • w‖ := by
        gcongr
        apply (norm_add_le _ _).trans
        gcongr
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg, ht.1, hpos.le, mul_assoc]
        exact mul_le_of_le_one_left (by positivity) ht.2.le
      _ = ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg, hpos.le]; ring
  -- conclude using the mean value inequality
  have I : ‖g 1 - g 0‖ <= ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
    simpa only [mul_one, sub_zero] using
      norm_image_sub_le_of_norm_deriv_le_segment' g_deriv g'_bound 1 (right_mem_Icc.2 zero_le_one)
  convert! I using 1
  · congr 1
    simp only [g, add_zero, one_mul, zero_div, zero_mul, sub_zero,
      zero_smul, Ne, not_false_iff, zero_pow, reduceCtorEq]
    abel
  · simp (discharger := positivity) only [Real.norm_eq_abs, abs_of_nonneg]
    ring

/--
theorem `Convex.isLittleO_alternate_sum_square` / 定理 `Convex.isLittleO_alternate_sum_square`

English:
theorem Convex.isLittleO_alternate_sum_square
  statement: {v w : E} (h4v : x + (4 : Real) • v in interior s)
  proof: by
  have A : (1 : Real) / 2 in Ioc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have B : (1 : Real) / 2 in Icc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have h2v2w : x + (2 : Real) • v + (2 : Real) • w in interior s := by
    convert! s_conv.interior.add_smul_sub_mem h4v h4w B using 1
    module
  have 

中文:
定理 凸.isLittleO_alternate_sum_square
  结论: {v w : E} (h4v : x + (4 : 实数) • v in interior s)
  证明: by
  have A : (1 : Real) / 2 in Ioc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have B : (1 : Real) / 2 in Icc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have h2v2w : x + (2 : Real) • v + (2 : Real) • w in interior s := by
    convert! s_conv.interior.add_smul_sub_mem h4v h4w B using 1
    module
  have 

Depends on / 依赖: add_smul_sub_mem, add_smul_sub_mem_interior, convert, interior, module, s_conv, s_conv.add_smul_sub_mem_interior, s_conv.interior.add_smul_sub_mem
-/
theorem Convex.isLittleO_alternate_sum_square {v w : E} (h4v : x + (4 : Real) • v in interior s)
    (h4w : x + (4 : Real) • w in interior s) :
    (fun h : Real => f (x + h • (2 • v + 2 • w)) + f (x + h • (v + w))
        - f (x + h • (2 • v + w)) - f (x + h • (v + 2 • w)) - h ^ 2 • f'' v w) =o[𝓝[>] 0]
      fun h => h ^ 2 := by
  have A : (1 : Real) / 2 in Ioc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have B : (1 : Real) / 2 in Icc (0 : Real) 1 := ⟨by simp, by norm_num⟩
  have h2v2w : x + (2 : Real) • v + (2 : Real) • w in interior s := by
    convert! s_conv.interior.add_smul_sub_mem h4v h4w B using 1
    module
  have h2vww : x + (2 • v + w) + w in interior s := by
    convert! h2v2w using 1
    module
  have h2v : x + (2 : Real) • v in interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h4v A using 1
    module
  have h2w : x + (2 : Real) • w in interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h4w A using 1
    module
  have hvw : x + (v + w) in interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h2v2w A using 1
    module
  have h2vw : x + (2 • v + w) in interior s := by
    convert! s_conv.interior.add_smul_sub_mem h2v h2v2w B using 1
    module
  have hvww : x + (v + w) + w in interior s := by
    convert! s_conv.interior.add_smul_sub_mem h2w h2v2w B using 1
    module
  have TA1 := s_conv.taylor_approx_two_segment hf xs hx h2vw h2vww
  have TA2 := s_conv.taylor_approx_two_segment hf xs hx hvw hvww
  convert! TA1.sub TA2 using 1
  ext h
  simp only [two_smul, smul_add, ← add_assoc, map_add,
    add_apply]
  abel

/--
theorem `Convex.second_derivative_within_at_symmetric_of_mem_interior` / 定理 `Convex.second_derivative_within_at_symmetric_of_mem_interior`

English:
theorem Convex.second_derivative_within_at_symmetric_of_mem_interior
  statement: {v w : E}
  proof: by
  have A : (fun h : Real => h ^ 2 • (f'' w v - f'' v w)) =o[𝓝[>] 0] fun h => h ^ 2 := by
    convert!
      (s_conv.isLittleO_alternate_sum_square hf xs hx h4v h4w).sub
        (s_conv.isLittleO_alternate_sum_square hf xs hx h4w h4v) using 1
    ext h
    simp only [add_comm, smul_add, smul_sub]


中文:
定理 凸.second_derivative_within_at_symmetric_of_mem_interior
  结论: {v w : E}
  证明: by
  have A : (fun h : Real => h ^ 2 • (f'' w v - f'' v w)) =o[𝓝[>] 0] fun h => h ^ 2 := by
    convert!
      (s_conv.isLittleO_alternate_sum_square hf xs hx h4v h4w).sub
        (s_conv.isLittleO_alternate_sum_square hf xs hx h4w h4v) using 1
    ext h
    simp only [add_comm, smul_add, smul_sub]


Depends on / 依赖: C.congr, add_comm, convert, isBigO_refl, isLittleO_alternate_sum_square, s_conv, s_conv.isLittleO_alternate_sum_square, smul_add, smul_isLittleO, smul_sub, this.smul_isLittleO
-/
theorem Convex.second_derivative_within_at_symmetric_of_mem_interior {v w : E}
    (h4v : x + (4 : Real) • v in interior s) (h4w : x + (4 : Real) • w in interior s) :
    f'' w v = f'' v w := by
  have A : (fun h : Real => h ^ 2 • (f'' w v - f'' v w)) =o[𝓝[>] 0] fun h => h ^ 2 := by
    convert!
      (s_conv.isLittleO_alternate_sum_square hf xs hx h4v h4w).sub
        (s_conv.isLittleO_alternate_sum_square hf xs hx h4w h4v) using 1
    ext h
    simp only [add_comm, smul_add, smul_sub]
    abel
  have B : (fun _ : Real => f'' w v - f'' v w) =o[𝓝[>] 0] fun _ => (1 : Real) := by
    have : (fun h : Real => 1 / h ^ 2) =O[𝓝[>] 0] fun h => 1 / h ^ 2 := isBigO_refl _ _
    have C := this.smul_isLittleO A
    apply C.congr' _ _
    · filter_upwards [self_mem_nhdsWithin]
      intro h (hpos : 0 < h)
      match_scalars <;> field
    · filter_upwards [self_mem_nhdsWithin] with h (hpos : 0 < h)
      simp [field]
  simpa only [sub_eq_zero] using isLittleO_const_const_iff.1 B

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Convex.second_derivative_within_at_symmetric` / 定理 `Convex.second_derivative_within_at_symmetric`

English:
theorem Convex.second_derivative_within_at_symmetric
  statement: {s : Set E} (s_conv : Convex Real s)
  proof: by
  /- we work around a point `x + 4 z` in the interior of `s`. For any vector `m`,
    then `x + 4 (z + t m)` also belongs to the interior of `s` for small enough `t`. This means that
    we will be able to apply `second_derivative_within_at_symmetric_of_mem_interior` to show
    that `f''` is sym

中文:
定理 凸.second_derivative_within_at_symmetric
  结论: {s : 集合 E} (s_conv : 凸 实数 s)
  证明: by
  /- we work around a point `x + 4 z` in the interior of `s`. For any vector `m`,
    then `x + 4 (z + t m)` also belongs to the interior of `s` for small enough `t`. This means that
    we will be able to apply `second_derivative_within_at_symmetric_of_mem_interior` to show
    that `f''` is sym
-/
theorem Convex.second_derivative_within_at_symmetric {s : Set E} (s_conv : Convex Real s)
    (hne : (interior s).Nonempty) {f : E -> F} {f' : E -> E ->L[Real] F} {f'' : E ->L[Real] E ->L[Real] F}
    (hf : forall x in interior s, HasFDerivAt f (f' x) x) {x : E} (xs : x in s)
    (hx : HasFDerivWithinAt f' f'' (interior s) x) (v w : E) : f'' v w = f'' w v := by
  /- we work around a point `x + 4 z` in the interior of `s`. For any vector `m`,
    then `x + 4 (z + t m)` also belongs to the interior of `s` for small enough `t`. This means that
    we will be able to apply `second_derivative_within_at_symmetric_of_mem_interior` to show
    that `f''` is symmetric, after cancelling all the contributions due to `z`. -/
  rcases hne with ⟨y, hy⟩
  obtain ⟨z, hz⟩ : exists z, z = ((1 : Real) / 4) • (y - x) := ⟨((1 : Real) / 4) • (y - x), rfl⟩
  have A : forall m : E, Filter.Tendsto (fun t : Real => x + (4 : Real) • (z + t • m)) (𝓝 0) (𝓝 y) := by
    intro m
    have : x + (4 : Real) • (z + (0 : Real) • m) = y := by simp [hz]
    rw [← this]
refine tendsto_const_nhds.add tendsto_const_nhds.smul tendsto_const_nhds.add ?_
    exact continuousAt_id.smul continuousAt_const
  have B : forall m : E, forallᶠ t in 𝓝[>] (0 : Real), x + (4 : Real) • (z + t • m) in interior s := by
    intro m
    apply nhdsWithin_le_nhds
    apply A m
    rw [mem_interior_iff_mem_nhds] at hy
    exact interior_mem_nhds.2 hy
  -- we choose `t m > 0` such that `x + 4 (z + (t m) m)` belongs to the interior of `s`, for any
  -- vector `m`.
  choose t ts tpos using fun m => ((B m).and self_mem_nhdsWithin).exists
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z`
  -- and `z + (t m) m`, we deduce that `f'' m z = f'' z m` for all `m`.
  have C : forall m : E, f'' m z = f'' z m := by
    intro m
    have : f'' (z + t m • m) (z + t 0 • (0 : E)) = f'' (z + t 0 • (0 : E)) (z + t m • m) :=
      s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts 0) (ts m)
    simp only [map_add, map_smul, add_right_inj, add_apply, smul_apply, add_zero, smul_zero] at this
    exact smul_right_injective F (tpos m).ne' this
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z + (t v) v`
  -- and `z + (t w) w`, we deduce that `f'' v w = f'' w v`. Cross terms involving `z` can be
  -- eliminated thanks to the fact proved above that `f'' m z = f'' z m`.
  have : f'' (z + t v • v) (z + t w • w) = f'' (z + t w • w) (z + t v • v) :=
    s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts w) (ts v)
  simp only [map_add, map_smul, add_apply, smul_apply, C] at this
  have : (t v * t w) • (f'' v) w = (t v * t w) • (f'' w) v := by
    linear_combination (norm := module) this
  apply smul_right_injective F _ this
  simp [(tpos v).ne', (tpos w).ne']

/--
theorem `second_derivative_symmetric_of_eventually_of_real` / 定理 `second_derivative_symmetric_of_eventually_of_real`

English:
theorem second_derivative_symmetric_of_eventually_of_real
  statement: {f : E -> F} {f' : E -> E ->L[Real] F}
  proof: by
  rcases Metric.mem_nhds_iff.1 hf with ⟨ε, εpos, hε⟩
  have A : (interior (Metric.ball x ε)).Nonempty := by
    rwa [Metric.isOpen_ball.interior_eq, Metric.nonempty_ball]
  exact
    Convex.second_derivative_within_at_symmetric (convex_ball x ε) A
      (fun y hy => hε (interior_subset hy)) (Metr

中文:
定理 second_derivative_symmetric_of_eventually_of_real
  结论: {f : E -> F} {f' : E -> E ->L[实数] F}
  证明: by
  rcases Metric.mem_nhds_iff.1 hf with ⟨ε, εpos, hε⟩
  have A : (interior (Metric.ball x ε)).Nonempty := by
    rwa [Metric.isOpen_ball.interior_eq, Metric.nonempty_ball]
  exact
    Convex.second_derivative_within_at_symmetric (convex_ball x ε) A
      (fun y hy => hε (interior_subset hy)) (Metr

Depends on / 依赖: Convex, Convex.second_derivative_within_at_symmetric, Metric, Metric.ball, Metric.isOpen_ball.interior_eq, Metric.mem_ball_self, Metric.mem_nhds_iff, Metric.nonempty_ball, Nonempty, convex_ball, hasFDerivWithinAt, hx.hasFDerivWithinAt, interior, interior_eq, interior_subset, isOpen_ball, mem_ball_self, mem_nhds_iff, nonempty_ball, second_derivative_within_at_symmetric
-/
theorem second_derivative_symmetric_of_eventually_of_real {f : E -> F} {f' : E -> E ->L[Real] F}
    {f'' : E ->L[Real] E ->L[Real] F} (hf : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x)
    (v w : E) : f'' v w = f'' w v := by
  rcases Metric.mem_nhds_iff.1 hf with ⟨ε, εpos, hε⟩
  have A : (interior (Metric.ball x ε)).Nonempty := by
    rwa [Metric.isOpen_ball.interior_eq, Metric.nonempty_ball]
  exact
    Convex.second_derivative_within_at_symmetric (convex_ball x ε) A
      (fun y hy => hε (interior_subset hy)) (Metric.mem_ball_self εpos) hx.hasFDerivWithinAt v w

end Real

section IsRCLikeNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s : Set E} {f : E -> F} {x : E}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `second_derivative_symmetric_of_eventually` / 定理 `second_derivative_symmetric_of_eventually`

English:
theorem second_derivative_symmetric_of_eventually
  statement: [IsRCLikeNormedField 𝕜]
  proof: by
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  let _ : NormedSpace Real F := NormedSpace.restrictScalars Real 𝕜 F
  let f'R : E -> E ->L[Real] F := fun x => (f' x).restrictScalars Real
  let f''R : E ->L[Real] E ->L[Real] F := f''.bi

中文:
定理 second_derivative_symmetric_of_eventually
  结论: [是RCLikeNormedField 𝕜]
  证明: by
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  let _ : NormedSpace Real F := NormedSpace.restrictScalars Real 𝕜 F
  let f'R : E -> E ->L[Real] F := fun x => (f' x).restrictScalars Real
  let f''R : E ->L[Real] E ->L[Real] F := f''.bi

Depends on / 依赖: HasFDerivAt, HasFDerivAt.restrictScalars, IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, NormedSpace.restrictScalars, bilinearRestrictScalars, filter_upwards, rclike, restrictScalars
-/
theorem second_derivative_symmetric_of_eventually [IsRCLikeNormedField 𝕜]
    {f' : E -> E ->L[𝕜] F} {x : E}
    {f'' : E ->L[𝕜] E ->L[𝕜] F} (hf : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v := by
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  let _ : NormedSpace Real F := NormedSpace.restrictScalars Real 𝕜 F
  let f'R : E -> E ->L[Real] F := fun x => (f' x).restrictScalars Real
  let f''R : E ->L[Real] E ->L[Real] F := f''.bilinearRestrictScalars Real
  have hfR : forallᶠ y in 𝓝 x, HasFDerivAt f (f'R y) y := by
    filter_upwards [hf] with y hy using HasFDerivAt.restrictScalars Real hy
  have : HasFDerivAt f'R f''R x := by
    simp only [hasFDerivAt_iff_tendsto] at hx ⊢
    exact hx
  change f''R v w = f''R w v
  exact second_derivative_symmetric_of_eventually_of_real hfR this v w

/--
theorem `second_derivative_symmetric` / 定理 `second_derivative_symmetric`

English:
theorem second_derivative_symmetric
  statement: [IsRCLikeNormedField 𝕜]
  proof: second_derivative_symmetric_of_eventually (Filter.Eventually.of_forall hf) hx v w

中文:
定理 second_derivative_symmetric
  结论: [是RCLikeNormedField 𝕜]
  证明: second_derivative_symmetric_of_eventually (Filter.Eventually.of_forall hf) hx v w

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, of_forall, second_derivative_symmetric_of_eventually
-/
theorem second_derivative_symmetric [IsRCLikeNormedField 𝕜]
    {f' : E -> E ->L[𝕜] F} {f'' : E ->L[𝕜] E ->L[𝕜] F} {x : E}
    (hf : forall y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v :=
  second_derivative_symmetric_of_eventually (Filter.Eventually.of_forall hf) hx v w

open scoped Classical in
variable (𝕜) in
/-- `minSmoothness 𝕜 n` is the minimal smoothness exponent larger than or equal to `n` for which
one can do serious calculus in `𝕜`. If `𝕜` is `ℝ` or `ℂ`, this is just `n`. Otherwise,
this is `ω` as only analytic functions are well behaved on `ℚₚ`, say. -/
noncomputable irreducible_def minSmoothness (n : Nat∞ω) :=
  if IsRCLikeNormedField 𝕜 then n else ω

/--
lemma `minSmoothness_of_isRCLikeNormedField` / 引理 `minSmoothness_of_isRCLikeNormedField`

English:
lemma minSmoothness_of_isRCLikeNormedField
  given: [h : IsRCLikeNormedField 𝕜] {n : Nat∞ω}
  proof: by
  simp [minSmoothness, h]

中文:
引理 minSmoothness_of_isRCLikeNormedField
  条件: [h : 是RCLikeNormedField 𝕜] {n : 自然数∞ω}
  证明: by
  simp [minSmoothness, h]
-/
@[simp] lemma minSmoothness_of_isRCLikeNormedField [h : IsRCLikeNormedField 𝕜] {n : Nat∞ω} :
    minSmoothness 𝕜 n = n := by
  simp [minSmoothness, h]

/--
lemma `le_minSmoothness` / 引理 `le_minSmoothness`

English:
lemma le_minSmoothness
  given: {n : Nat∞ω}
  statement: n <= minSmoothness 𝕜 n
  proof: by
  simp only [minSmoothness]
  split_ifs <;> simp

中文:
引理 le_minSmoothness
  条件: {n : 自然数∞ω}
  结论: n <= minSmoothness 𝕜 n
  证明: by
  simp only [minSmoothness]
  split_ifs <;> simp

Depends on / 依赖: minSmoothness, split_ifs
-/
lemma le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n := by
  simp only [minSmoothness]
  split_ifs <;> simp

/--
lemma `minSmoothness_add` / 引理 `minSmoothness_add`

English:
lemma minSmoothness_add
  given: {n m : Nat∞ω}
  statement: minSmoothness 𝕜 (n + m) = minSmoothness 𝕜 n + m
  proof: by
  simp only [minSmoothness]
  split_ifs <;> simp

中文:
引理 minSmoothness_add
  条件: {n m : 自然数∞ω}
  结论: minSmoothness 𝕜 (n + m) = minSmoothness 𝕜 n + m
  证明: by
  simp only [minSmoothness]
  split_ifs <;> simp

Depends on / 依赖: minSmoothness, split_ifs
-/
lemma minSmoothness_add {n m : Nat∞ω} : minSmoothness 𝕜 (n + m) = minSmoothness 𝕜 n + m := by
  simp only [minSmoothness]
  split_ifs <;> simp

/--
lemma `minSmoothness_monotone` / 引理 `minSmoothness_monotone`

English:
lemma minSmoothness_monotone
  statement: Monotone (minSmoothness 𝕜)
  proof: by
  intro m n hmn
  simp only [minSmoothness]
  split_ifs <;> simp [hmn]

中文:
引理 minSmoothness_monotone
  结论: 递增 (minSmoothness 𝕜)
  证明: by
  intro m n hmn
  simp only [minSmoothness]
  split_ifs <;> simp [hmn]

Depends on / 依赖: minSmoothness, split_ifs
-/
lemma minSmoothness_monotone : Monotone (minSmoothness 𝕜) := by
  intro m n hmn
  simp only [minSmoothness]
  split_ifs <;> simp [hmn]

/--
lemma `minSmoothness_eq_infty` / 引理 `minSmoothness_eq_infty`

English:
lemma minSmoothness_eq_infty
  given: {n : Nat∞ω}
  proof: by
  simp only [minSmoothness]
  split_ifs with h <;> simp [h]

中文:
引理 minSmoothness_eq_infty
  条件: {n : 自然数∞ω}
  证明: by
  simp only [minSmoothness]
  split_ifs with h <;> simp [h]
-/
@[simp] lemma minSmoothness_eq_infty {n : Nat∞ω} :
    minSmoothness 𝕜 n = ∞ ↔ (n = ∞ ∧ IsRCLikeNormedField 𝕜) := by
  simp only [minSmoothness]
  split_ifs with h <;> simp [h]

/--
lemma `exist_minSmoothness_le_ne_infty` / 引理 `exist_minSmoothness_le_ne_infty`

English:
lemma exist_minSmoothness_le_ne_infty
  given: {n : Nat∞ω} {m : Nat} (hm : minSmoothness 𝕜 m <= n)
  proof: by
  simp only [minSmoothness] at hm ⊢
  split_ifs with h
  · simp only [h, ↓reduceIte] at hm
    exact ⟨m, le_rfl, hm, by simp⟩
  · simp only [h, ↓reduceIte] at hm
    refine ⟨ω, le_rfl, by simp [hm], by simp⟩

中文:
引理 exist_minSmoothness_le_ne_infty
  条件: {n : 自然数∞ω} {m : 自然数} (hm : minSmoothness 𝕜 m <= n)
  证明: by
  simp only [minSmoothness] at hm ⊢
  split_ifs with h
  · simp only [h, ↓reduceIte] at hm
    exact ⟨m, le_rfl, hm, by simp⟩
  · simp only [h, ↓reduceIte] at hm
    refine ⟨ω, le_rfl, by simp [hm], by simp⟩

Depends on / 依赖: le_rfl, minSmoothness, reduceIte, split_ifs
-/
lemma exist_minSmoothness_le_ne_infty {n : Nat∞ω} {m : Nat} (hm : minSmoothness 𝕜 m <= n) :
    exists n', minSmoothness 𝕜 m <= n' ∧ n' <= n ∧ n' != ∞ := by
  simp only [minSmoothness] at hm ⊢
  split_ifs with h
  · simp only [h, ↓reduceIte] at hm
    exact ⟨m, le_rfl, hm, by simp⟩
  · simp only [h, ↓reduceIte] at hm
    refine ⟨ω, le_rfl, by simp [hm], by simp⟩

/--
theorem `ContDiffAt.isSymmSndFDerivAt` / 定理 `ContDiffAt.isSymmSndFDerivAt`

English:
theorem ContDiffAt.isSymmSndFDerivAt
  statement: {n : Nat∞ω}
  proof: by
  by_cases h : IsRCLikeNormedField 𝕜
  -- First deal with the `ℝ` or `ℂ` case, where `C^2` is enough.
  · intro v w
    apply second_derivative_symmetric_of_eventually (f := f) (f' := fderiv 𝕜 f) (x := x)
    · obtain ⟨u, hu, h'u⟩ : exists u in 𝓝 x, ContDiffOn 𝕜 2 f u :=
        (hf.of_le hn).con

中文:
定理 ContDiffAt.isSymmSndFDerivAt
  结论: {n : 自然数∞ω}
  证明: by
  by_cases h : IsRCLikeNormedField 𝕜
  -- First deal with the `ℝ` or `ℂ` case, where `C^2` is enough.
  · intro v w
    apply second_derivative_symmetric_of_eventually (f := f) (f' := fderiv 𝕜 f) (x := x)
    · obtain ⟨u, hu, h'u⟩ : exists u in 𝓝 x, ContDiffOn 𝕜 2 f u :=
        (hf.of_le hn).con

Depends on / 依赖: IsRCLikeNormedField
-/
theorem ContDiffAt.isSymmSndFDerivAt {n : Nat∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 <= n) : IsSymmSndFDerivAt 𝕜 f x := by
  by_cases h : IsRCLikeNormedField 𝕜
  -- First deal with the `ℝ` or `ℂ` case, where `C^2` is enough.
  · intro v w
    apply second_derivative_symmetric_of_eventually (f := f) (f' := fderiv 𝕜 f) (x := x)
    · obtain ⟨u, hu, h'u⟩ : exists u in 𝓝 x, ContDiffOn 𝕜 2 f u :=
        (hf.of_le hn).contDiffOn (m := 2) le_minSmoothness (by simp)
      rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, xv⟩
      filter_upwards [v_open.mem_nhds xv] with y hy
      have : DifferentiableAt 𝕜 f y := by
        have := (h'u.mono vu y hy).contDiffAt (v_open.mem_nhds hy)
        exact this.differentiableAt two_ne_zero
      exact DifferentiableAt.hasFDerivAt this
    · have : DifferentiableAt 𝕜 (fderiv 𝕜 f) x := by
        apply ContDiffAt.differentiableAt _ one_ne_zero
        exact hf.fderiv_right (le_minSmoothness.trans hn)
      exact DifferentiableAt.hasFDerivAt this
  -- then deal with the case of an arbitrary field, with analytic functions.
  · simp only [minSmoothness, h, ↓reduceIte, top_le_iff] at hn
    apply ContDiffAt.isSymmSndFDerivAt_of_omega
    simpa [hn] using hf

/--
theorem `ContDiffWithinAt.isSymmSndFDerivWithinAt` / 定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`

English:
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt
  statement: {n : Nat∞ω}
  proof: by
  /- We argue that, at interior points, the second derivative is symmetric, and moreover by
  continuity it converges to the second derivative at `x`. Therefore, the latter is also
  symmetric. -/
  obtain ⟨m, hm, hmn, m_ne⟩ := exist_minSmoothness_le_ne_infty hn
  rcases (hf.of_le hmn).contDiffOn

中文:
定理 ContDiffWithinAt.isSymmSndFDerivWithinAt
  结论: {n : 自然数∞ω}
  证明: by
  /- We argue that, at interior points, the second derivative is symmetric, and moreover by
  continuity it converges to the second derivative at `x`. Therefore, the latter is also
  symmetric. -/
  obtain ⟨m, hm, hmn, m_ne⟩ := exist_minSmoothness_le_ne_infty hn
  rcases (hf.of_le hmn).contDiffOn
-/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt {n : Nat∞ω}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 <= n)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in closure (interior s)) (h'x : x in s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  /- We argue that, at interior points, the second derivative is symmetric, and moreover by
  continuity it converges to the second derivative at `x`. Therefore, the latter is also
  symmetric. -/
  obtain ⟨m, hm, hmn, m_ne⟩ := exist_minSmoothness_le_ne_infty hn
  rcases (hf.of_le hmn).contDiffOn' le_rfl (by simp [m_ne]) with ⟨u, u_open, xu, hu⟩
  simp only [insert_eq_of_mem h'x] at hu
  have h'u : UniqueDiffOn 𝕜 (s inter u) := hs.inter u_open
  obtain ⟨y, hy, y_lim⟩ : exists y, (forall (n : Nat), y n in interior s) ∧ Tendsto y atTop (𝓝 x) :=
    mem_closure_iff_seq_limit.1 hx
  have L : forallᶠ k in atTop, y k in u := y_lim (u_open.mem_nhds xu)
  have I : forallᶠ k in atTop, IsSymmSndFDerivWithinAt 𝕜 f s (y k) := by
    filter_upwards [L] with k hk
    have s_mem : s in 𝓝 (y k) := by
      apply mem_of_superset (isOpen_interior.mem_nhds (hy k))
      exact interior_subset
    have : IsSymmSndFDerivAt 𝕜 f (y k) := by
      apply ContDiffAt.isSymmSndFDerivAt _ (n := m) hm
      apply (hu (y k) ⟨(interior_subset (hy k)), hk⟩).contDiffAt
      exact inter_mem s_mem (u_open.mem_nhds hk)
    intro v w
    rw [fderivWithin_fderivWithin_eq_of_mem_nhds s_mem]
    exact this v w
  have A : ContinuousOn (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s) (s inter u) := by
    have : ContinuousOn (fderivWithin 𝕜 (fderivWithin 𝕜 f (s inter u)) (s inter u)) (s inter u) :=
      ((hu.fderivWithin h'u (m := 1) (le_minSmoothness.trans hm)).fderivWithin h'u
      (m := 0) le_rfl).continuousOn
    apply this.congr
    intro y hy
    apply fderivWithin_fderivWithin_eq_of_eventuallyEq
    filter_upwards [u_open.mem_nhds hy.2] with z hz
    change (z in s) = (z in s inter u)
    simp_all
  have B : Tendsto (fun k => fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k)) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x)) := by
    have : Tendsto y atTop (𝓝[s inter u] x) := by
      apply tendsto_nhdsWithin_iff.2 ⟨y_lim, ?_⟩
      filter_upwards [L] with k hk using ⟨interior_subset (hy k), hk⟩
    exact (A x ⟨h'x, xu⟩ ).tendsto.comp this
  have C (v w : E) : Tendsto (fun k => fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k) v w) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w)) := by
    have : Continuous (fun (A : E ->L[𝕜] E ->L[𝕜] F) => A v w) := by fun_prop
    exact (this.tendsto _).comp B
  have C' (v w : E) : Tendsto (fun k => fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k) w v) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w)) := by
    apply (C v w).congr'
    filter_upwards [I] with k hk using hk v w
  intro v w
  exact tendsto_nhds_unique (C v w) (C' w v)

end IsRCLikeNormedField
