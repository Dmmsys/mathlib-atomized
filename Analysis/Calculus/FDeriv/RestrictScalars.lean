/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of the scalar restriction of a linear map

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
the scalar restriction of a linear map.
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
variable [IsScalarTower 𝕜 𝕜' E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
variable [IsScalarTower 𝕜 𝕜' F]
variable {f : E -> F} {f' : E ->L[𝕜'] F} {s : Set E} {x : E}

/--
theorem `HasFDerivAtFilter.restrictScalars` / 定理 `HasFDerivAtFilter.restrictScalars`

English:
theorem HasFDerivAtFilter.restrictScalars
  given: {L} (h : HasFDerivAtFilter f f' L)
  proof: .of_isLittleO h.isLittleO

@[fun_prop]

中文:
定理 HasFDerivAtFilter.restrictScalars
  条件: {L} (h : HasFDerivAtFilter f f' L)
  证明: .of_isLittleO h.isLittleO

@[fun_prop]

Depends on / 依赖: h.isLittleO, isLittleO, of_isLittleO
-/
theorem HasFDerivAtFilter.restrictScalars {L} (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter f (f'.restrictScalars 𝕜) L :=
  .of_isLittleO h.isLittleO

@[fun_prop]
/--
theorem `HasStrictFDerivAt.restrictScalars` / 定理 `HasStrictFDerivAt.restrictScalars`

English:
theorem HasStrictFDerivAt.restrictScalars
  given: (h : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

中文:
定理 HasStrictFDerivAt.restrictScalars
  条件: (h : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.restrictScalars, restrictScalars
-/
theorem HasStrictFDerivAt.restrictScalars (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/--
theorem `HasFDerivAt.restrictScalars` / 定理 `HasFDerivAt.restrictScalars`

English:
theorem HasFDerivAt.restrictScalars
  given: (h : HasFDerivAt f f' x)
  proof: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

中文:
定理 HasFDerivAt.restrictScalars
  条件: (h : HasFDerivAt f f' x)
  证明: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.restrictScalars, restrictScalars
-/
theorem HasFDerivAt.restrictScalars (h : HasFDerivAt f f' x) :
    HasFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/--
theorem `HasFDerivWithinAt.restrictScalars` / 定理 `HasFDerivWithinAt.restrictScalars`

English:
theorem HasFDerivWithinAt.restrictScalars
  given: (h : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

中文:
定理 HasFDerivWithinAt.restrictScalars
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.restrictScalars, restrictScalars
-/
theorem HasFDerivWithinAt.restrictScalars (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/--
theorem `DifferentiableAt.restrictScalars` / 定理 `DifferentiableAt.restrictScalars`

English:
theorem DifferentiableAt.restrictScalars
  given: (h : DifferentiableAt 𝕜' f x)
  statement: DifferentiableAt 𝕜 f x
  proof: (h.hasFDerivAt.restrictScalars 𝕜).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.restrictScalars
  条件: (h : DifferentiableAt 𝕜' f x)
  结论: DifferentiableAt 𝕜 f x
  证明: (h.hasFDerivAt.restrictScalars 𝕜).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, h.hasFDerivAt.restrictScalars, hasFDerivAt, restrictScalars
-/
theorem DifferentiableAt.restrictScalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt.restrictScalars 𝕜).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.restrictScalars` / 定理 `DifferentiableWithinAt.restrictScalars`

English:
theorem DifferentiableWithinAt.restrictScalars
  given: (h : DifferentiableWithinAt 𝕜' f s x)
  proof: (h.hasFDerivWithinAt.restrictScalars 𝕜).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.restrictScalars
  条件: (h : DifferentiableWithinAt 𝕜' f s x)
  证明: (h.hasFDerivWithinAt.restrictScalars 𝕜).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.restrictScalars, hasFDerivWithinAt, restrictScalars
-/
theorem DifferentiableWithinAt.restrictScalars (h : DifferentiableWithinAt 𝕜' f s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.hasFDerivWithinAt.restrictScalars 𝕜).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableOn.restrictScalars` / 定理 `DifferentiableOn.restrictScalars`

English:
theorem DifferentiableOn.restrictScalars
  given: (h : DifferentiableOn 𝕜' f s)
  statement: DifferentiableOn 𝕜 f s
  proof: fun x hx => (h x hx).restrictScalars 𝕜

@[fun_prop]

中文:
定理 DifferentiableOn.restrictScalars
  条件: (h : DifferentiableOn 𝕜' f s)
  结论: DifferentiableOn 𝕜 f s
  证明: fun x hx => (h x hx).restrictScalars 𝕜

@[fun_prop]

Depends on / 依赖: restrictScalars
-/
theorem DifferentiableOn.restrictScalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜

@[fun_prop]
/--
theorem `Differentiable.restrictScalars` / 定理 `Differentiable.restrictScalars`

English:
theorem Differentiable.restrictScalars
  given: (h : Differentiable 𝕜' f)
  statement: Differentiable 𝕜 f
  proof: fun x =>
  (h x).restrictScalars 𝕜

@[fun_prop]

中文:
定理 Differentiable.restrictScalars
  条件: (h : Differentiable 𝕜' f)
  结论: Differentiable 𝕜 f
  证明: fun x =>
  (h x).restrictScalars 𝕜

@[fun_prop]
-/
theorem Differentiable.restrictScalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f := fun x =>
  (h x).restrictScalars 𝕜

@[fun_prop]
/--
theorem `HasFDerivWithinAt.of_restrictScalars` / 定理 `HasFDerivWithinAt.of_restrictScalars`

English:
theorem HasFDerivWithinAt.of_restrictScalars
  statement: {g' : E ->L[𝕜] F} (h : HasFDerivWithinAt f g' s x)
  proof: by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

@[fun_prop]

中文:
定理 HasFDerivWithinAt.of_restrictScalars
  结论: {g' : E ->L[𝕜] F} (h : HasFDerivWithinAt f g' s x)
  证明: by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

@[fun_prop]

Depends on / 依赖: h.isLittleO, isLittleO, of_isLittleO
-/
theorem HasFDerivWithinAt.of_restrictScalars {g' : E ->L[𝕜] F} (h : HasFDerivWithinAt f g' s x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivWithinAt f f' s x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

@[fun_prop]
/--
theorem `hasFDerivAt_of_restrictScalars` / 定理 `hasFDerivAt_of_restrictScalars`

English:
theorem hasFDerivAt_of_restrictScalars
  statement: {g' : E ->L[𝕜] F} (h : HasFDerivAt f g' x)
  proof: by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

中文:
定理 hasFDerivAt_of_restrictScalars
  结论: {g' : E ->L[𝕜] F} (h : HasFDerivAt f g' x)
  证明: by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

Depends on / 依赖: h.isLittleO, isLittleO, of_isLittleO
-/
theorem hasFDerivAt_of_restrictScalars {g' : E ->L[𝕜] F} (h : HasFDerivAt f g' x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt f f' x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

/--
theorem `DifferentiableAt.fderiv_restrictScalars` / 定理 `DifferentiableAt.fderiv_restrictScalars`

English:
theorem DifferentiableAt.fderiv_restrictScalars
  given: (h : DifferentiableAt 𝕜' f x)
  proof: (h.hasFDerivAt.restrictScalars 𝕜).fderiv

中文:
定理 DifferentiableAt.fderiv_restrictScalars
  条件: (h : DifferentiableAt 𝕜' f x)
  证明: (h.hasFDerivAt.restrictScalars 𝕜).fderiv

Depends on / 依赖: fderiv, h.hasFDerivAt.restrictScalars, hasFDerivAt, restrictScalars
-/
theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
    fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.hasFDerivAt.restrictScalars 𝕜).fderiv

/--
theorem `DifferentiableWithinAt.restrictScalars_fderivWithin` / 定理 `DifferentiableWithinAt.restrictScalars_fderivWithin`

English:
theorem DifferentiableWithinAt.restrictScalars_fderivWithin
  statement: (hf : DifferentiableWithinAt 𝕜' f s x)
  proof: ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm

中文:
定理 DifferentiableWithinAt.restrictScalars_fderivWithin
  结论: (hf : DifferentiableWithinAt 𝕜' f s x)
  证明: ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.restrictScalars, restrictScalars
-/
theorem DifferentiableWithinAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    (fderivWithin 𝕜' f s x).restrictScalars 𝕜 = fderivWithin 𝕜 f s x :=
  ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm

/--
theorem `differentiableWithinAt_iff_restrictScalars` / 定理 `differentiableWithinAt_iff_restrictScalars`

English:
theorem differentiableWithinAt_iff_restrictScalars
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrictScalars 𝕜) hf.hasFDerivWithinAt⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hf.hasFDerivWithinAt.of_restrictScalars 𝕜 hf'⟩

中文:
定理 differentiableWithinAt_iff_restrictScalars
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrictScalars 𝕜) hf.hasFDerivWithinAt⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hf.hasFDerivWithinAt.of_restrictScalars 𝕜 hf'⟩

Depends on / 依赖: hasFDerivWithinAt, hf.hasFDerivWithinAt, hf.hasFDerivWithinAt.of_restrictScalars, hs.eq, of_restrictScalars, restrictScalars
-/
theorem differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) : DifferentiableWithinAt 𝕜' f s x ↔
      exists g' : E ->L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x := by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrictScalars 𝕜) hf.hasFDerivWithinAt⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hf.hasFDerivWithinAt.of_restrictScalars 𝕜 hf'⟩

/--
theorem `differentiableAt_iff_restrictScalars` / 定理 `differentiableAt_iff_restrictScalars`

English:
theorem differentiableAt_iff_restrictScalars
  given: (hf : DifferentiableAt 𝕜 f x)
  proof: by
  rw [← differentiableWithinAt_univ]; rw [← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiableWithinAt uniqueDiffWithinAt_univ

中文:
定理 differentiableAt_iff_restrictScalars
  条件: (hf : DifferentiableAt 𝕜 f x)
  证明: by
  rw [← differentiableWithinAt_univ]; rw [← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiableWithinAt uniqueDiffWithinAt_univ

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_iff_restrictScalars, differentiableWithinAt_univ, fderivWithin_univ, hf.differentiableWithinAt, uniqueDiffWithinAt_univ
-/
theorem differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜' f x ↔ exists g' : E ->L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x := by
  rw [← differentiableWithinAt_univ]; rw [← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiableWithinAt uniqueDiffWithinAt_univ

end RestrictScalars
