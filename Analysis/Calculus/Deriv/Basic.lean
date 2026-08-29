/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.TangentCone.DimOne
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

- `HasDerivAtFilter f f' L` states that the function `f` has the
  derivative `f'` along the filter `L : Filter (𝕜 × 𝕜)`.

- `HasDerivWithinAt f f' s x` states that the function `f` has the
  derivative `f'` at the point `x` within the subset `s`.

- `HasDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x`.

- `HasStrictDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x` in the sense of strict differentiability, i.e.,
  `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

- `derivWithin f s x` is a derivative of `f` at `x` within `s`. If the
  derivative does not exist, then `derivWithin f s x` equals zero.

- `deriv f x` is a derivative of `f` at `x`. If the derivative does not
  exist, then `deriv f x` equals zero.

The theorems `fderivWithin_derivWithin` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps (in `Linear.lean`)
  - addition (in `Add.lean`)
  - sum of finitely many functions (in `Add.lean`)
  - negation (in `Add.lean`)
  - subtraction (in `Add.lean`)
  - star (in `Star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `Mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `Mul.lean`)
  - powers of a function (in `Pow.lean` and `ZPow.lean`)
  - inverse `x → x⁻¹` (in `Inv.lean`)
  - division (in `Inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `Comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `Comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `Inverse.lean`)
  - polynomials (in `Polynomial.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring
```

The relationship between the derivative of a function and its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`
is developed in the file `Mathlib/Analysis/Calculus/Deriv/Slope.lean`.

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. See the explanations there.
-/

@[expose] public section

universe u v w

noncomputable section

open scoped Topology ENNReal NNReal
open Filter Asymptotics Set

open ContinuousLinearMap (smulRight toSpanSingleton_inj toSpanSingleton)

section TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

section
variable [ContinuousSMul 𝕜 F]

/--
Definition of `HasDerivAtFilter` / `HasDerivAtFilter` 的定义

English:
definition HasDerivAtFilter
  signature: (f : 𝕜 -> F) (f' : F) (L : Filter (𝕜 × 𝕜))
  body: HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

中文:
定义 HasDerivAtFilter
  签名: (f : 𝕜 -> F) (f' : F) (L : Filter (𝕜 × 𝕜))
  定义体: HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

Depends on / 依赖: HasFDerivAtFilter, toSpanSingleton
-/
def HasDerivAtFilter (f : 𝕜 -> F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

/--
Definition of `HasDerivWithinAt` / `HasDerivWithinAt` 的定义

English:
definition HasDerivWithinAt
  signature: (f : 𝕜 -> F) (f' : F) (s : Set 𝕜) (x : 𝕜)
  body: HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

中文:
定义 HasDerivWithinAt
  签名: (f : 𝕜 -> F) (f' : F) (s : Set 𝕜) (x : 𝕜)
  定义体: HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

Depends on / 依赖: HasDerivAtFilter
-/
def HasDerivWithinAt (f : 𝕜 -> F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

/--
Definition of `HasDerivAt` / `HasDerivAt` 的定义

English:
definition HasDerivAt
  signature: (f : 𝕜 -> F) (f' : F) (x : 𝕜)
  body: HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

中文:
定义 HasDerivAt
  签名: (f : 𝕜 -> F) (f' : F) (x : 𝕜)
  定义体: HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

Depends on / 依赖: HasDerivAtFilter
-/
def HasDerivAt (f : 𝕜 -> F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

/--
Definition of `HasStrictDerivAt` / `HasStrictDerivAt` 的定义

English:
definition HasStrictDerivAt
  signature: (f : 𝕜 -> F) (f' : F) (x : 𝕜)
  body: HasDerivAtFilter f f' (𝓝 (x, x))

中文:
定义 HasStrictDerivAt
  签名: (f : 𝕜 -> F) (f' : F) (x : 𝕜)
  定义体: HasDerivAtFilter f f' (𝓝 (x, x))

Depends on / 依赖: HasDerivAtFilter
-/
def HasStrictDerivAt (f : 𝕜 -> F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 (x, x))

end
/--
Definition of `derivWithin` / `derivWithin` 的定义

English:
definition derivWithin
  signature: (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜)
  body: fderivWithin 𝕜 f s x 1

中文:
定义 derivWithin
  签名: (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜)
  定义体: fderivWithin 𝕜 f s x 1

Depends on / 依赖: fderivWithin
-/
def derivWithin (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1

/--
Definition of `deriv` / `deriv` 的定义

English:
definition deriv
  signature: (f : 𝕜 -> F) (x : 𝕜)
  body: fderiv 𝕜 f x 1

中文:
定义 deriv
  签名: (f : 𝕜 -> F) (x : 𝕜)
  定义体: fderiv 𝕜 f x 1

Depends on / 依赖: fderiv
-/
def deriv (f : 𝕜 -> F) (x : 𝕜) :=
  fderiv 𝕜 f x 1

variable {f f₀ f₁ : 𝕜 -> F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section
variable [ContinuousSMul 𝕜 F]
/--
theorem `hasFDerivAtFilter_iff_hasDerivAtFilter` / 定理 `hasFDerivAtFilter_iff_hasDerivAtFilter`

English:
theorem hasFDerivAtFilter_iff_hasDerivAtFilter
  given: {f' : 𝕜 ->L[𝕜] F}
  proof: by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter

中文:
定理 hasFDerivAtFilter_iff_hasDerivAtFilter
  条件: {f' : 𝕜 ->L[𝕜] F}
  证明: by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter

Depends on / 依赖: HasDerivAtFilter
-/
theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 ->L[𝕜] F} :
    HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) L := by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter

/--
theorem `hasDerivAtFilter_iff_hasFDerivAtFilter` / 定理 `hasDerivAtFilter_iff_hasFDerivAtFilter`

English:
theorem hasDerivAtFilter_iff_hasFDerivAtFilter
  proof: .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter

中文:
定理 hasDerivAtFilter_iff_hasFDerivAtFilter
  证明: .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter
-/
theorem hasDerivAtFilter_iff_hasFDerivAtFilter :
    HasDerivAtFilter f f' L ↔ HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L :=
  .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter

/--
theorem `hasFDerivWithinAt_iff_hasDerivWithinAt` / 定理 `hasFDerivWithinAt_iff_hasDerivWithinAt`

English:
theorem hasFDerivWithinAt_iff_hasDerivWithinAt
  given: {f' : 𝕜 ->L[𝕜] F}
  proof: hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

中文:
定理 hasFDerivWithinAt_iff_hasDerivWithinAt
  条件: {f' : 𝕜 ->L[𝕜] F}
  证明: hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

Depends on / 依赖: hasFDerivAtFilter_iff_hasDerivAtFilter
-/
theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 ->L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

/--
theorem `hasDerivWithinAt_iff_hasFDerivWithinAt` / 定理 `hasDerivWithinAt_iff_hasFDerivWithinAt`

English:
theorem hasDerivWithinAt_iff_hasFDerivWithinAt
  given: {f' : F}
  proof: Iff.rfl

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=
  hasDerivWithinAt_iff_hasFDerivWithinAt

中文:
定理 hasDerivWithinAt_iff_hasFDerivWithinAt
  条件: {f' : F}
  证明: Iff.rfl

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=
  hasDerivWithinAt_iff_hasFDerivWithinAt

Depends on / 依赖: Iff.rfl
-/
theorem hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSingleton 𝕜 f') s x :=
  Iff.rfl

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=
  hasDerivWithinAt_iff_hasFDerivWithinAt

/--
theorem `hasFDerivAt_iff_hasDerivAt` / 定理 `hasFDerivAt_iff_hasDerivAt`

English:
theorem hasFDerivAt_iff_hasDerivAt
  given: {f' : 𝕜 ->L[𝕜] F}
  statement: HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x
  proof: hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

中文:
定理 hasFDerivAt_iff_hasDerivAt
  条件: {f' : 𝕜 ->L[𝕜] F}
  结论: HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x
  证明: hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

Depends on / 依赖: hasFDerivAtFilter_iff_hasDerivAtFilter
-/
theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 ->L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

/--
theorem `hasDerivAt_iff_hasFDerivAt` / 定理 `hasDerivAt_iff_hasFDerivAt`

English:
theorem hasDerivAt_iff_hasFDerivAt
  given: {f' : F}
  proof: Iff.rfl

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt

中文:
定理 hasDerivAt_iff_hasFDerivAt
  条件: {f' : F}
  证明: Iff.rfl

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt

Depends on / 依赖: Iff.rfl
-/
theorem hasDerivAt_iff_hasFDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt

/--
theorem `hasStrictFDerivAt_iff_hasStrictDerivAt` / 定理 `hasStrictFDerivAt_iff_hasStrictDerivAt`

English:
theorem hasStrictFDerivAt_iff_hasStrictDerivAt
  given: {f' : 𝕜 ->L[𝕜] F}
  proof: hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=
  hasStrictFDerivAt_iff_hasStrictDerivAt

中文:
定理 hasStrictFDerivAt_iff_hasStrictDerivAt
  条件: {f' : 𝕜 ->L[𝕜] F}
  证明: hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=
  hasStrictFDerivAt_iff_hasStrictDerivAt

Depends on / 依赖: hasFDerivAtFilter_iff_hasDerivAtFilter
-/
theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 ->L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=
  hasStrictFDerivAt_iff_hasStrictDerivAt

/--
theorem `hasStrictDerivAt_iff_hasStrictFDerivAt` / 定理 `hasStrictDerivAt_iff_hasStrictFDerivAt`

English:
theorem hasStrictDerivAt_iff_hasStrictFDerivAt
  proof: Iff.rfl

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

中文:
定理 hasStrictDerivAt_iff_hasStrictFDerivAt
  证明: Iff.rfl

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

Depends on / 依赖: Iff.rfl
-/
theorem hasStrictDerivAt_iff_hasStrictFDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictFDerivAt f (toSpanSingleton 𝕜 f') x :=
  Iff.rfl

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

end

/--
theorem `derivWithin_zero_of_not_differentiableWithinAt` / 定理 `derivWithin_zero_of_not_differentiableWithinAt`

English:
theorem derivWithin_zero_of_not_differentiableWithinAt
  given: (h : ¬DifferentiableWithinAt 𝕜 f s x)
  proof: by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp

中文:
定理 derivWithin_zero_of_not_differentiableWithinAt
  条件: (h : ¬DifferentiableWithinAt 𝕜 f s x)
  证明: by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp

Depends on / 依赖: derivWithin, fderivWithin_zero_of_not_differentiableWithinAt
-/
theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp

/--
theorem `differentiableWithinAt_of_derivWithin_ne_zero` / 定理 `differentiableWithinAt_of_derivWithin_ne_zero`

English:
theorem differentiableWithinAt_of_derivWithin_ne_zero
  given: (h : derivWithin f s x != 0)
  proof: not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h

中文:
定理 differentiableWithinAt_of_derivWithin_ne_zero
  条件: (h : derivWithin f s x != 0)
  证明: not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h

Depends on / 依赖: derivWithin_zero_of_not_differentiableWithinAt, not_imp_comm
-/
theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x != 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h

end TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f f₀ f₁ : 𝕜 -> F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter (𝕜 × 𝕜)}

/--
theorem `derivWithin_zero_of_not_accPt` / 定理 `derivWithin_zero_of_not_accPt`

English:
theorem derivWithin_zero_of_not_accPt
  given: (h : ¬AccPt x (𝓟 s))
  statement: derivWithin f s x = 0
  proof: by
  rw [derivWithin]; rw [fderivWithin_zero_of_not_accPt h]; rw [zero_apply]

中文:
定理 derivWithin_zero_of_not_accPt
  条件: (h : ¬AccPt x (𝓟 s))
  结论: derivWithin f s x = 0
  证明: by
  rw [derivWithin]; rw [fderivWithin_zero_of_not_accPt h]; rw [zero_apply]

Depends on / 依赖: derivWithin, fderivWithin_zero_of_not_accPt, zero_apply
-/
theorem derivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : derivWithin f s x = 0 := by
  rw [derivWithin]; rw [fderivWithin_zero_of_not_accPt h]; rw [zero_apply]

/--
theorem `derivWithin_zero_of_not_uniqueDiffWithinAt` / 定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`

English:
theorem derivWithin_zero_of_not_uniqueDiffWithinAt
  given: (h : ¬UniqueDiffWithinAt 𝕜 s x)
  proof: derivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

中文:
定理 derivWithin_zero_of_not_uniqueDiffWithinAt
  条件: (h : ¬UniqueDiffWithinAt 𝕜 s x)
  证明: derivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

Depends on / 依赖: AccPt.uniqueDiffWithinAt, derivWithin_zero_of_not_accPt, uniqueDiffWithinAt
-/
theorem derivWithin_zero_of_not_uniqueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = 0 :=
derivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

/--
theorem `derivWithin_zero_of_notMem_closure` / 定理 `derivWithin_zero_of_notMem_closure`

English:
theorem derivWithin_zero_of_notMem_closure
  given: (h : x ∉ closure s)
  statement: derivWithin f s x = 0
  proof: by
  rw [derivWithin]; rw [fderivWithin_zero_of_notMem_closure h]; rw [zero_apply]

中文:
定理 derivWithin_zero_of_notMem_closure
  条件: (h : x ∉ closure s)
  结论: derivWithin f s x = 0
  证明: by
  rw [derivWithin]; rw [fderivWithin_zero_of_notMem_closure h]; rw [zero_apply]

Depends on / 依赖: derivWithin, fderivWithin_zero_of_notMem_closure, zero_apply
-/
theorem derivWithin_zero_of_notMem_closure (h : x ∉ closure s) : derivWithin f s x = 0 := by
  rw [derivWithin]; rw [fderivWithin_zero_of_notMem_closure h]; rw [zero_apply]

/--
theorem `deriv_zero_of_not_differentiableAt` / 定理 `deriv_zero_of_not_differentiableAt`

English:
theorem deriv_zero_of_not_differentiableAt
  given: (h : ¬DifferentiableAt 𝕜 f x)
  statement: deriv f x = 0
  proof: by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

中文:
定理 deriv_zero_of_not_differentiableAt
  条件: (h : ¬DifferentiableAt 𝕜 f x)
  结论: deriv f x = 0
  证明: by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

Depends on / 依赖: fderiv_zero_of_not_differentiableAt
-/
theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

/--
theorem `differentiableAt_of_deriv_ne_zero` / 定理 `differentiableAt_of_deriv_ne_zero`

English:
theorem differentiableAt_of_deriv_ne_zero
  given: (h : deriv f x != 0)
  statement: DifferentiableAt 𝕜 f x
  proof: not_imp_comm.1 deriv_zero_of_not_differentiableAt h

中文:
定理 differentiableAt_of_deriv_ne_zero
  条件: (h : deriv f x != 0)
  结论: DifferentiableAt 𝕜 f x
  证明: not_imp_comm.1 deriv_zero_of_not_differentiableAt h

Depends on / 依赖: deriv_zero_of_not_differentiableAt, not_imp_comm
-/
theorem differentiableAt_of_deriv_ne_zero (h : deriv f x != 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h

/--
theorem `UniqueDiffWithinAt.eq_deriv` / 定理 `UniqueDiffWithinAt.eq_deriv`

English:
theorem UniqueDiffWithinAt.eq_deriv
  statement: (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
  proof: toSpanSingleton_inj.mp UniqueDiffWithinAt.eq H h h₁

中文:
定理 UniqueDiffWithinAt.eq_deriv
  结论: (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
  证明: toSpanSingleton_inj.mp UniqueDiffWithinAt.eq H h h₁

Depends on / 依赖: UniqueDiffWithinAt, UniqueDiffWithinAt.eq, toSpanSingleton_inj, toSpanSingleton_inj.mp
-/
theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
toSpanSingleton_inj.mp UniqueDiffWithinAt.eq H h h₁

/--
theorem `hasDerivAtFilter_iff_isLittleO` / 定理 `hasDerivAtFilter_iff_isLittleO`

English:
theorem hasDerivAtFilter_iff_isLittleO
  proof: hasFDerivAtFilter_iff_isLittleO ..

中文:
定理 hasDerivAtFilter_iff_isLittleO
  证明: hasFDerivAtFilter_iff_isLittleO ..

Depends on / 依赖: hasFDerivAtFilter_iff_isLittleO
-/
theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - (p.1 - p.2) • f') =o[L] fun p => p.1 - p.2 :=
  hasFDerivAtFilter_iff_isLittleO ..

/--
theorem `hasDerivAtFilter_iff_tendsto` / 定理 `hasDerivAtFilter_iff_tendsto`

English:
theorem hasDerivAtFilter_iff_tendsto
  proof: hasFDerivAtFilter_iff_tendsto

中文:
定理 hasDerivAtFilter_iff_tendsto
  证明: hasFDerivAtFilter_iff_tendsto

Depends on / 依赖: hasFDerivAtFilter_iff_tendsto
-/
theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' L ↔
      Tendsto (fun p => ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - (p.1 - p.2) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

/--
theorem `hasDerivWithinAt_iff_isLittleO` / 定理 `hasDerivWithinAt_iff_isLittleO`

English:
theorem hasDerivWithinAt_iff_isLittleO
  proof: hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO

中文:
定理 hasDerivWithinAt_iff_isLittleO
  证明: hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO

Depends on / 依赖: hasFDerivWithinAt_iff_isLittleO
-/
theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO

/--
theorem `hasDerivWithinAt_iff_tendsto` / 定理 `hasDerivWithinAt_iff_tendsto`

English:
theorem hasDerivWithinAt_iff_tendsto
  proof: hasFDerivWithinAt_iff_tendsto

中文:
定理 hasDerivWithinAt_iff_tendsto
  证明: hasFDerivWithinAt_iff_tendsto

Depends on / 依赖: hasFDerivWithinAt_iff_tendsto
-/
theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

/--
theorem `hasDerivAt_iff_isLittleO` / 定理 `hasDerivAt_iff_isLittleO`

English:
theorem hasDerivAt_iff_isLittleO
  proof: hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO

中文:
定理 hasDerivAt_iff_isLittleO
  证明: hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO

Depends on / 依赖: hasFDerivAt_iff_isLittleO
-/
theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO

/--
theorem `hasDerivAt_iff_tendsto` / 定理 `hasDerivAt_iff_tendsto`

English:
theorem hasDerivAt_iff_tendsto
  proof: hasFDerivAt_iff_tendsto

中文:
定理 hasDerivAt_iff_tendsto
  证明: hasFDerivAt_iff_tendsto

Depends on / 依赖: hasFDerivAt_iff_tendsto
-/
theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

/--
theorem `HasDerivAtFilter.isBigO_sub` / 定理 `HasDerivAtFilter.isBigO_sub`

English:
theorem HasDerivAtFilter.isBigO_sub
  given: (h : HasDerivAtFilter f f' L)
  proof: HasFDerivAtFilter.isBigO_sub h

中文:
定理 HasDerivAtFilter.isBigO_sub
  条件: (h : HasDerivAtFilter f f' L)
  证明: HasFDerivAtFilter.isBigO_sub h

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isBigO_sub, isBigO_sub
-/
theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  HasFDerivAtFilter.isBigO_sub h

/--
theorem `HasDerivAt.isBigO_sub` / 定理 `HasDerivAt.isBigO_sub`

English:
theorem HasDerivAt.isBigO_sub
  given: (h : HasDerivAt f f' x)
  statement: (f · - f x) =O[𝓝 x] (· - x)
  proof: h.hasFDerivAt.isBigO_sub

中文:
定理 HasDerivAt.isBigO_sub
  条件: (h : HasDerivAt f f' x)
  结论: (f · - f x) =O[𝓝 x] (· - x)
  证明: h.hasFDerivAt.isBigO_sub

Depends on / 依赖: h.hasFDerivAt.isBigO_sub, hasFDerivAt, isBigO_sub
-/
theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (f · - f x) =O[𝓝 x] (· - x) :=
  h.hasFDerivAt.isBigO_sub

/--
lemma `isInducing_toSpanSingleton` / 引理 `isInducing_toSpanSingleton`

English:
lemma isInducing_toSpanSingleton
  given: (hf' : f' != 0)
  proof: by
  refine AntilipschitzWith.isInducing (K := ‖f'‖₊⁻¹) ?_ (map_continuous _)
  simp [antilipschitzWith_iff_le_mul_dist, dist_eq_norm, ← sub_smul, norm_smul, field]

中文:
引理 isInducing_toSpanSingleton
  条件: (hf' : f' != 0)
  证明: by
  refine AntilipschitzWith.isInducing (K := ‖f'‖₊⁻¹) ?_ (map_continuous _)
  simp [antilipschitzWith_iff_le_mul_dist, dist_eq_norm, ← sub_smul, norm_smul, field]
-/
private lemma isInducing_toSpanSingleton (hf' : f' != 0) :
    Topology.IsInducing (toSpanSingleton 𝕜 f') := by
  refine AntilipschitzWith.isInducing (K := ‖f'‖₊⁻¹) ?_ (map_continuous _)
  simp [antilipschitzWith_iff_le_mul_dist, dist_eq_norm, ← sub_smul, norm_smul, field]

/--
theorem `HasDerivAtFilter.isEquivalent_sub` / 定理 `HasDerivAtFilter.isEquivalent_sub`

English:
theorem HasDerivAtFilter.isEquivalent_sub
  given: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  proof: HasFDerivAtFilter.isEquivalent_sub hf isInducing_toSpanSingleton hf'

中文:
定理 HasDerivAtFilter.isEquivalent_sub
  条件: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  证明: HasFDerivAtFilter.isEquivalent_sub hf isInducing_toSpanSingleton hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isEquivalent_sub, isEquivalent_sub, isInducing_toSpanSingleton
-/
theorem HasDerivAtFilter.isEquivalent_sub (hf : HasDerivAtFilter f f' L) (hf' : f' != 0) :
    (fun p => f p.1 - f p.2) ~[L] (fun p => (p.1 - p.2) • f') :=
HasFDerivAtFilter.isEquivalent_sub hf isInducing_toSpanSingleton hf'

/--
theorem `HasDerivAtFilter.isTheta_sub` / 定理 `HasDerivAtFilter.isTheta_sub`

English:
theorem HasDerivAtFilter.isTheta_sub
  given: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  proof: HasFDerivAtFilter.isTheta_sub hf isInducing_toSpanSingleton hf'

@[deprecated HasDerivAtFilter.isTheta_sub (since := "2026-02-04")]

中文:
定理 HasDerivAtFilter.isTheta_sub
  条件: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  证明: HasFDerivAtFilter.isTheta_sub hf isInducing_toSpanSingleton hf'

@[deprecated HasDerivAtFilter.isTheta_sub (since := "2026-02-04")]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isTheta_sub, isInducing_toSpanSingleton, isTheta_sub
-/
theorem HasDerivAtFilter.isTheta_sub (hf : HasDerivAtFilter f f' L) (hf' : f' != 0) :
    (fun p => f p.1 - f p.2) =Θ[L] (fun p => p.1 - p.2) :=
HasFDerivAtFilter.isTheta_sub hf isInducing_toSpanSingleton hf'

@[deprecated HasDerivAtFilter.isTheta_sub (since := "2026-02-04")]
/--
theorem `HasDerivAtFilter.isBigO_sub_rev` / 定理 `HasDerivAtFilter.isBigO_sub_rev`

English:
theorem HasDerivAtFilter.isBigO_sub_rev
  given: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  proof: .isBigO_symm hf.isTheta_sub hf'

中文:
定理 HasDerivAtFilter.isBigO_sub_rev
  条件: (hf : HasDerivAtFilter f f' L) (hf' : f' != 0)
  证明: .isBigO_symm hf.isTheta_sub hf'

Depends on / 依赖: hf.isTheta_sub, isBigO_symm, isTheta_sub
-/
theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' L) (hf' : f' != 0) :
    (fun p => p.1 - p.2) =O[L] fun p => f p.1 - f p.2 :=
.isBigO_symm hf.isTheta_sub hf'

/--
theorem `HasStrictDerivAt.hasDerivAt` / 定理 `HasStrictDerivAt.hasDerivAt`

English:
theorem HasStrictDerivAt.hasDerivAt
  given: (h : HasStrictDerivAt f f' x)
  statement: HasDerivAt f f' x
  proof: h.hasStrictFDerivAt.hasFDerivAt

中文:
定理 HasStrictDerivAt.hasDerivAt
  条件: (h : HasStrictDerivAt f f' x)
  结论: HasDerivAt f f' x
  证明: h.hasStrictFDerivAt.hasFDerivAt

Depends on / 依赖: h.hasStrictFDerivAt.hasFDerivAt, hasFDerivAt, hasStrictFDerivAt
-/
theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.hasStrictFDerivAt.hasFDerivAt

/--
theorem `hasDerivWithinAt_congr_set'` / 定理 `hasDerivWithinAt_congr_set'`

English:
theorem hasDerivWithinAt_congr_set'
  given: {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: hasFDerivWithinAt_congr_set' y h

中文:
定理 hasDerivWithinAt_congr_set'
  条件: {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: hasFDerivWithinAt_congr_set' y h

Depends on / 依赖: hasFDerivWithinAt_congr_set
-/
theorem hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

/--
theorem `hasDerivWithinAt_congr_set` / 定理 `hasDerivWithinAt_congr_set`

English:
theorem hasDerivWithinAt_congr_set
  given: {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t)
  proof: hasFDerivWithinAt_congr_set h

alias ⟨HasDerivWithinAt.congr_set, _⟩ := hasDerivWithinAt_congr_set

@[simp]

中文:
定理 hasDerivWithinAt_congr_set
  条件: {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t)
  证明: hasFDerivWithinAt_congr_set h

alias ⟨HasDerivWithinAt.congr_set, _⟩ := hasDerivWithinAt_congr_set

@[simp]

Depends on / 依赖: hasFDerivWithinAt_congr_set
-/
theorem hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

alias ⟨HasDerivWithinAt.congr_set, _⟩ := hasDerivWithinAt_congr_set

@[simp]
/--
theorem `hasDerivWithinAt_sdiff_singleton` / 定理 `hasDerivWithinAt_sdiff_singleton`

English:
theorem hasDerivWithinAt_sdiff_singleton
  proof: hasFDerivWithinAt_sdiff_singleton _

@[deprecated (since := "2026-06-03")]
alias hasDerivWithinAt_diff_singleton := hasDerivWithinAt_sdiff_singleton

@[simp]

中文:
定理 hasDerivWithinAt_sdiff_singleton
  证明: hasFDerivWithinAt_sdiff_singleton _

@[deprecated (since := "2026-06-03")]
alias hasDerivWithinAt_diff_singleton := hasDerivWithinAt_sdiff_singleton

@[simp]

Depends on / 依赖: hasFDerivWithinAt_sdiff_singleton
-/
theorem hasDerivWithinAt_sdiff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_sdiff_singleton _

@[deprecated (since := "2026-06-03")]
alias hasDerivWithinAt_diff_singleton := hasDerivWithinAt_sdiff_singleton

@[simp]
/--
theorem `hasDerivWithinAt_Ioi_iff_Ici` / 定理 `hasDerivWithinAt_Ioi_iff_Ici`

English:
theorem hasDerivWithinAt_Ioi_iff_Ici
  given: [PartialOrder 𝕜]
  proof: by
  rw [← Ici_sdiff_left]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Ici_of_Ioi, HasDerivWithinAt.Ioi_of_Ici⟩ := hasDerivWithinAt_Ioi_iff_Ici

@[simp]

中文:
定理 hasDerivWithinAt_Ioi_iff_Ici
  条件: [PartialOrder 𝕜]
  证明: by
  rw [← Ici_sdiff_left]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Ici_of_Ioi, HasDerivWithinAt.Ioi_of_Ici⟩ := hasDerivWithinAt_Ioi_iff_Ici

@[simp]

Depends on / 依赖: Ici_sdiff_left, hasDerivWithinAt_sdiff_singleton
-/
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_sdiff_left]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Ici_of_Ioi, HasDerivWithinAt.Ioi_of_Ici⟩ := hasDerivWithinAt_Ioi_iff_Ici

@[simp]
/--
theorem `hasDerivWithinAt_Iio_iff_Iic` / 定理 `hasDerivWithinAt_Iio_iff_Iic`

English:
theorem hasDerivWithinAt_Iio_iff_Iic
  given: [PartialOrder 𝕜]
  proof: by
  rw [← Iic_sdiff_right]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Iic_of_Iio, HasDerivWithinAt.Iio_of_Iic⟩ := hasDerivWithinAt_Iio_iff_Iic

中文:
定理 hasDerivWithinAt_Iio_iff_Iic
  条件: [PartialOrder 𝕜]
  证明: by
  rw [← Iic_sdiff_right]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Iic_of_Iio, HasDerivWithinAt.Iio_of_Iic⟩ := hasDerivWithinAt_Iio_iff_Iic

Depends on / 依赖: Iic_sdiff_right, hasDerivWithinAt_sdiff_singleton
-/
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_sdiff_right]; rw [hasDerivWithinAt_sdiff_singleton]

alias ⟨HasDerivWithinAt.Iic_of_Iio, HasDerivWithinAt.Iio_of_Iic⟩ := hasDerivWithinAt_Iio_iff_Iic

/--
theorem `HasDerivWithinAt.Ioi_iff_Ioo` / 定理 `HasDerivWithinAt.Ioi_iff_Ioo`

English:
theorem HasDerivWithinAt.Ioi_iff_Ioo
  given: [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y)
  proof: hasFDerivWithinAt_inter Iio_mem_nhds h

alias ⟨HasDerivWithinAt.Ioi_of_Ioo, HasDerivWithinAt.Ioo_of_Ioi⟩ := HasDerivWithinAt.Ioi_iff_Ioo

中文:
定理 HasDerivWithinAt.Ioi_iff_Ioo
  条件: [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y)
  证明: hasFDerivWithinAt_inter Iio_mem_nhds h

alias ⟨HasDerivWithinAt.Ioi_of_Ioo, HasDerivWithinAt.Ioo_of_Ioi⟩ := HasDerivWithinAt.Ioi_iff_Ioo

Depends on / 依赖: Iio_mem_nhds, hasFDerivWithinAt_inter
-/
theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
hasFDerivWithinAt_inter Iio_mem_nhds h

alias ⟨HasDerivWithinAt.Ioi_of_Ioo, HasDerivWithinAt.Ioo_of_Ioi⟩ := HasDerivWithinAt.Ioi_iff_Ioo

/--
theorem `hasDerivAt_iff_isLittleO_nhds_zero` / 定理 `hasDerivAt_iff_isLittleO_nhds_zero`

English:
theorem hasDerivAt_iff_isLittleO_nhds_zero
  proof: hasFDerivAt_iff_isLittleO_nhds_zero

中文:
定理 hasDerivAt_iff_isLittleO_nhds_zero
  证明: hasFDerivAt_iff_isLittleO_nhds_zero

Depends on / 依赖: hasFDerivAt_iff_isLittleO_nhds_zero
-/
theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

/--
theorem `HasDerivAtFilter.mono` / 定理 `HasDerivAtFilter.mono`

English:
theorem HasDerivAtFilter.mono
  given: (h : HasDerivAtFilter f f' L₂) (hst : L₁ <= L₂)
  proof: HasFDerivAtFilter.mono h hst

中文:
定理 HasDerivAtFilter.mono
  条件: (h : HasDerivAtFilter f f' L₂) (hst : L₁ <= L₂)
  证明: HasFDerivAtFilter.mono h hst

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.mono
-/
theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' L₂) (hst : L₁ <= L₂) :
    HasDerivAtFilter f f' L₁ :=
  HasFDerivAtFilter.mono h hst

/--
theorem `HasDerivWithinAt.mono` / 定理 `HasDerivWithinAt.mono`

English:
theorem HasDerivWithinAt.mono
  given: (h : HasDerivWithinAt f f' t x) (hst : s subseteq t)
  proof: HasFDerivWithinAt.mono h hst

中文:
定理 HasDerivWithinAt.mono
  条件: (h : HasDerivWithinAt f f' t x) (hst : s subseteq t)
  证明: HasFDerivWithinAt.mono h hst

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.mono
-/
theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s subseteq t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst

/--
theorem `HasDerivWithinAt.mono_of_mem_nhdsWithin` / 定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`

English:
theorem HasDerivWithinAt.mono_of_mem_nhdsWithin
  given: (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x)
  proof: HasFDerivWithinAt.mono_of_mem_nhdsWithin h hst

中文:
定理 HasDerivWithinAt.mono_of_mem_nhdsWithin
  条件: (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x)
  证明: HasFDerivWithinAt.mono_of_mem_nhdsWithin h hst

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin
-/
theorem HasDerivWithinAt.mono_of_mem_nhdsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono_of_mem_nhdsWithin h hst

/--
theorem `HasDerivAt.hasDerivAtFilter` / 定理 `HasDerivAt.hasDerivAtFilter`

English:
theorem HasDerivAt.hasDerivAtFilter
  given: (h : HasDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x)
  proof: HasFDerivAt.hasFDerivAtFilter h hL

中文:
定理 HasDerivAt.hasDerivAtFilter
  条件: (h : HasDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x)
  证明: HasFDerivAt.hasFDerivAtFilter h hL

Depends on / 依赖: HasFDerivAt, HasFDerivAt.hasFDerivAtFilter, hasFDerivAtFilter
-/
theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x) :
    HasDerivAtFilter f f' L :=
  HasFDerivAt.hasFDerivAtFilter h hL

/--
theorem `HasDerivAt.hasDerivWithinAt` / 定理 `HasDerivAt.hasDerivWithinAt`

English:
theorem HasDerivAt.hasDerivWithinAt
  given: (h : HasDerivAt f f' x)
  statement: HasDerivWithinAt f f' s x
  proof: HasFDerivAt.hasFDerivWithinAt h

中文:
定理 HasDerivAt.hasDerivWithinAt
  条件: (h : HasDerivAt f f' x)
  结论: HasDerivWithinAt f f' s x
  证明: HasFDerivAt.hasFDerivWithinAt h

Depends on / 依赖: HasFDerivAt, HasFDerivAt.hasFDerivWithinAt, hasFDerivWithinAt
-/
theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h

/--
theorem `HasDerivWithinAt.differentiableWithinAt` / 定理 `HasDerivWithinAt.differentiableWithinAt`

English:
theorem HasDerivWithinAt.differentiableWithinAt
  given: (h : HasDerivWithinAt f f' s x)
  proof: HasFDerivWithinAt.differentiableWithinAt h

中文:
定理 HasDerivWithinAt.differentiableWithinAt
  条件: (h : HasDerivWithinAt f f' s x)
  证明: HasFDerivWithinAt.differentiableWithinAt h

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.differentiableWithinAt, differentiableWithinAt
-/
theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h

/--
theorem `HasDerivAt.differentiableAt` / 定理 `HasDerivAt.differentiableAt`

English:
theorem HasDerivAt.differentiableAt
  given: (h : HasDerivAt f f' x)
  statement: DifferentiableAt 𝕜 f x
  proof: HasFDerivAt.differentiableAt h

@[simp]

中文:
定理 HasDerivAt.differentiableAt
  条件: (h : HasDerivAt f f' x)
  结论: DifferentiableAt 𝕜 f x
  证明: HasFDerivAt.differentiableAt h

@[simp]

Depends on / 依赖: HasFDerivAt, HasFDerivAt.differentiableAt, differentiableAt
-/
theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h

@[simp]
/--
theorem `hasDerivWithinAt_univ` / 定理 `hasDerivWithinAt_univ`

English:
theorem hasDerivWithinAt_univ
  statement: HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x
  proof: hasFDerivWithinAt_univ

中文:
定理 hasDerivWithinAt_univ
  结论: HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x
  证明: hasFDerivWithinAt_univ

Depends on / 依赖: hasFDerivWithinAt_univ
-/
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ

/--
theorem `HasDerivAt.unique` / 定理 `HasDerivAt.unique`

English:
theorem HasDerivAt.unique
  given: (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x)
  statement: f₀' = f₁'
  proof: toSpanSingleton_inj.mp h₀.hasFDerivAt.unique h₁

中文:
定理 HasDerivAt.unique
  条件: (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x)
  结论: f₀' = f₁'
  证明: toSpanSingleton_inj.mp h₀.hasFDerivAt.unique h₁

Depends on / 依赖: hasFDerivAt, hasFDerivAt.unique, toSpanSingleton_inj, toSpanSingleton_inj.mp, unique
-/
theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
toSpanSingleton_inj.mp h₀.hasFDerivAt.unique h₁

/--
theorem `hasDerivWithinAt_inter'` / 定理 `hasDerivWithinAt_inter'`

English:
theorem hasDerivWithinAt_inter'
  given: (h : t in 𝓝[s] x)
  proof: hasFDerivWithinAt_inter' h

中文:
定理 hasDerivWithinAt_inter'
  条件: (h : t in 𝓝[s] x)
  证明: hasFDerivWithinAt_inter' h

Depends on / 依赖: hasFDerivWithinAt_inter
-/
theorem hasDerivWithinAt_inter' (h : t in 𝓝[s] x) :
    HasDerivWithinAt f f' (s inter t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter' h

/--
theorem `hasDerivWithinAt_inter` / 定理 `hasDerivWithinAt_inter`

English:
theorem hasDerivWithinAt_inter
  given: (h : t in 𝓝 x)
  proof: hasFDerivWithinAt_inter h

中文:
定理 hasDerivWithinAt_inter
  条件: (h : t in 𝓝 x)
  证明: hasFDerivWithinAt_inter h

Depends on / 依赖: hasFDerivWithinAt_inter
-/
theorem hasDerivWithinAt_inter (h : t in 𝓝 x) :
    HasDerivWithinAt f f' (s inter t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter h

/--
theorem `HasDerivWithinAt.union` / 定理 `HasDerivWithinAt.union`

English:
theorem HasDerivWithinAt.union
  given: (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x)
  proof: hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt

中文:
定理 HasDerivWithinAt.union
  条件: (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x)
  证明: hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt

Depends on / 依赖: hasFDerivWithinAt, hs.hasFDerivWithinAt.union, ht.hasFDerivWithinAt
-/
theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s union t) x :=
  hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt

/--
theorem `HasDerivWithinAt.hasDerivAt` / 定理 `HasDerivWithinAt.hasDerivAt`

English:
theorem HasDerivWithinAt.hasDerivAt
  given: (h : HasDerivWithinAt f f' s x) (hs : s in 𝓝 x)
  proof: HasFDerivWithinAt.hasFDerivAt h hs

中文:
定理 HasDerivWithinAt.hasDerivAt
  条件: (h : HasDerivWithinAt f f' s x) (hs : s in 𝓝 x)
  证明: HasFDerivWithinAt.hasFDerivAt h hs

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.hasFDerivAt, hasFDerivAt
-/
theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s in 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs

/--
theorem `DifferentiableWithinAt.hasDerivWithinAt` / 定理 `DifferentiableWithinAt.hasDerivWithinAt`

English:
theorem DifferentiableWithinAt.hasDerivWithinAt
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.hasFDerivWithinAt.hasDerivWithinAt

中文:
定理 DifferentiableWithinAt.hasDerivWithinAt
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.hasFDerivWithinAt.hasDerivWithinAt

Depends on / 依赖: h.hasFDerivWithinAt.hasDerivWithinAt, hasDerivWithinAt, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.hasFDerivWithinAt.hasDerivWithinAt

/--
theorem `DifferentiableAt.hasDerivAt` / 定理 `DifferentiableAt.hasDerivAt`

English:
theorem DifferentiableAt.hasDerivAt
  given: (h : DifferentiableAt 𝕜 f x)
  statement: HasDerivAt f (deriv f x) x
  proof: h.hasFDerivAt.hasDerivAt

@[simp]

中文:
定理 DifferentiableAt.hasDerivAt
  条件: (h : DifferentiableAt 𝕜 f x)
  结论: HasDerivAt f (deriv f x) x
  证明: h.hasFDerivAt.hasDerivAt

@[simp]

Depends on / 依赖: h.hasFDerivAt.hasDerivAt, hasDerivAt, hasFDerivAt
-/
theorem DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.hasFDerivAt.hasDerivAt

@[simp]
/--
theorem `hasDerivAt_deriv_iff` / 定理 `hasDerivAt_deriv_iff`

English:
theorem hasDerivAt_deriv_iff
  statement: HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x
  proof: ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩

@[simp]

中文:
定理 hasDerivAt_deriv_iff
  结论: HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x
  证明: ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩

@[simp]

Depends on / 依赖: differentiableAt, h.differentiableAt, h.hasDerivAt, hasDerivAt
-/
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩

@[simp]
/--
theorem `hasDerivWithinAt_derivWithin_iff` / 定理 `hasDerivWithinAt_derivWithin_iff`

English:
theorem hasDerivWithinAt_derivWithin_iff
  proof: ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩

中文:
定理 hasDerivWithinAt_derivWithin_iff
  证明: ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩

Depends on / 依赖: differentiableWithinAt, h.differentiableWithinAt, h.hasDerivWithinAt, hasDerivWithinAt
-/
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩

/--
theorem `DifferentiableOn.hasDerivAt` / 定理 `DifferentiableOn.hasDerivAt`

English:
theorem DifferentiableOn.hasDerivAt
  given: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  proof: (h.hasFDerivAt hs).hasDerivAt

中文:
定理 DifferentiableOn.hasDerivAt
  条件: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  证明: (h.hasFDerivAt hs).hasDerivAt

Depends on / 依赖: h.hasFDerivAt, hasDerivAt, hasFDerivAt
-/
theorem DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.hasFDerivAt hs).hasDerivAt

/--
theorem `HasDerivAt.deriv` / 定理 `HasDerivAt.deriv`

English:
theorem HasDerivAt.deriv
  given: (h : HasDerivAt f f' x)
  statement: deriv f x = f'
  proof: h.differentiableAt.hasDerivAt.unique h

中文:
定理 HasDerivAt.deriv
  条件: (h : HasDerivAt f f' x)
  结论: deriv f x = f'
  证明: h.differentiableAt.hasDerivAt.unique h

Depends on / 依赖: differentiableAt, h.differentiableAt.hasDerivAt.unique, hasDerivAt, unique
-/
theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.differentiableAt.hasDerivAt.unique h

/--
theorem `deriv_eq` / 定理 `deriv_eq`

English:
theorem deriv_eq
  given: {f' : 𝕜 -> F} (h : forall x, HasDerivAt f (f' x) x)
  statement: deriv f = f'
  proof: funext fun x => (h x).deriv

中文:
定理 deriv_eq
  条件: {f' : 𝕜 -> F} (h : 对任意 x, HasDerivAt f (f' x) x)
  结论: deriv f = f'
  证明: funext fun x => (h x).deriv
-/
theorem deriv_eq {f' : 𝕜 -> F} (h : forall x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv

/--
theorem `HasDerivWithinAt.derivWithin` / 定理 `HasDerivWithinAt.derivWithin`

English:
theorem HasDerivWithinAt.derivWithin
  statement: (h : HasDerivWithinAt f f' s x)
  proof: hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h

中文:
定理 HasDerivWithinAt.derivWithin
  结论: (h : HasDerivWithinAt f f' s x)
  证明: hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h

Depends on / 依赖: differentiableWithinAt, eq_deriv, h.differentiableWithinAt.hasDerivWithinAt, hasDerivWithinAt, hxs.eq_deriv
-/
theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h

/--
theorem `fderivWithin_derivWithin` / 定理 `fderivWithin_derivWithin`

English:
theorem fderivWithin_derivWithin
  statement: (fderivWithin 𝕜 f s x : 𝕜 -> F) 1 = derivWithin f s x
  proof: rfl

中文:
定理 fderivWithin_derivWithin
  结论: (fderivWithin 𝕜 f s x : 𝕜 -> F) 1 = derivWithin f s x
  证明: rfl
-/
theorem fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 -> F) 1 = derivWithin f s x :=
  rfl

/--
theorem `toSpanSingleton_derivWithin` / 定理 `toSpanSingleton_derivWithin`

English:
theorem toSpanSingleton_derivWithin
  proof: by simp [derivWithin]

中文:
定理 toSpanSingleton_derivWithin
  证明: by simp [derivWithin]

Depends on / 依赖: derivWithin
-/
theorem toSpanSingleton_derivWithin :
    toSpanSingleton 𝕜 (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]

/--
theorem `norm_derivWithin_eq_norm_fderivWithin` / 定理 `norm_derivWithin_eq_norm_fderivWithin`

English:
theorem norm_derivWithin_eq_norm_fderivWithin
  statement: ‖derivWithin f s x‖ = ‖fderivWithin 𝕜 f s x‖
  proof: by
  simp [← toSpanSingleton_derivWithin]

中文:
定理 norm_derivWithin_eq_norm_fderivWithin
  结论: ‖derivWithin f s x‖ = ‖fderivWithin 𝕜 f s x‖
  证明: by
  simp [← toSpanSingleton_derivWithin]

Depends on / 依赖: toSpanSingleton_derivWithin
-/
theorem norm_derivWithin_eq_norm_fderivWithin : ‖derivWithin f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp [← toSpanSingleton_derivWithin]

/--
theorem `fderiv_apply_one_eq_deriv` / 定理 `fderiv_apply_one_eq_deriv`

English:
theorem fderiv_apply_one_eq_deriv
  statement: (fderiv 𝕜 f x : 𝕜 -> F) 1 = deriv f x
  proof: rfl

@[simp]

中文:
定理 fderiv_apply_one_eq_deriv
  结论: (fderiv 𝕜 f x : 𝕜 -> F) 1 = deriv f x
  证明: rfl

@[simp]
-/
theorem fderiv_apply_one_eq_deriv : (fderiv 𝕜 f x : 𝕜 -> F) 1 = deriv f x := rfl

@[simp]
/--
theorem `fderiv_eq_smul_deriv` / 定理 `fderiv_eq_smul_deriv`

English:
theorem fderiv_eq_smul_deriv
  given: (y : 𝕜)
  statement: (fderiv 𝕜 f x : 𝕜 -> F) y = y • deriv f x
  proof: by
  rw [← fderiv_apply_one_eq_deriv]; rw [← map_smul]
  simp only [smul_eq_mul, mul_one]

中文:
定理 fderiv_eq_smul_deriv
  条件: (y : 𝕜)
  结论: (fderiv 𝕜 f x : 𝕜 -> F) y = y • deriv f x
  证明: by
  rw [← fderiv_apply_one_eq_deriv]; rw [← map_smul]
  simp only [smul_eq_mul, mul_one]

Depends on / 依赖: fderiv_apply_one_eq_deriv, map_smul, mul_one, smul_eq_mul
-/
theorem fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -> F) y = y • deriv f x := by
  rw [← fderiv_apply_one_eq_deriv]; rw [← map_smul]
  simp only [smul_eq_mul, mul_one]

/--
theorem `toSpanSingleton_deriv` / 定理 `toSpanSingleton_deriv`

English:
theorem toSpanSingleton_deriv
  statement: toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x
  proof: by
  simp only [deriv, ContinuousLinearMap.toSpanSingleton_apply_map_one]

中文:
定理 toSpanSingleton_deriv
  结论: toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x
  证明: by
  simp only [deriv, ContinuousLinearMap.toSpanSingleton_apply_map_one]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toSpanSingleton_apply_map_one, toSpanSingleton_apply_map_one
-/
theorem toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x := by
  simp only [deriv, ContinuousLinearMap.toSpanSingleton_apply_map_one]

/--
lemma `fderiv_eq_deriv_mul` / 引理 `fderiv_eq_deriv_mul`

English:
lemma fderiv_eq_deriv_mul
  given: {f : 𝕜 -> 𝕜} {x y : 𝕜}
  statement: (fderiv 𝕜 f x : 𝕜 -> 𝕜) y = (deriv f x) * y
  proof: by
  simp [mul_comm]

中文:
引理 fderiv_eq_deriv_mul
  条件: {f : 𝕜 -> 𝕜} {x y : 𝕜}
  结论: (fderiv 𝕜 f x : 𝕜 -> 𝕜) y = (deriv f x) * y
  证明: by
  simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma fderiv_eq_deriv_mul {f : 𝕜 -> 𝕜} {x y : 𝕜} : (fderiv 𝕜 f x : 𝕜 -> 𝕜) y = (deriv f x) * y := by
  simp [mul_comm]

/--
theorem `norm_deriv_eq_norm_fderiv` / 定理 `norm_deriv_eq_norm_fderiv`

English:
theorem norm_deriv_eq_norm_fderiv
  statement: ‖deriv f x‖ = ‖fderiv 𝕜 f x‖
  proof: by
  simp [← toSpanSingleton_deriv]

中文:
定理 norm_deriv_eq_norm_fderiv
  结论: ‖deriv f x‖ = ‖fderiv 𝕜 f x‖
  证明: by
  simp [← toSpanSingleton_deriv]

Depends on / 依赖: toSpanSingleton_deriv
-/
theorem norm_deriv_eq_norm_fderiv : ‖deriv f x‖ = ‖fderiv 𝕜 f x‖ := by
  simp [← toSpanSingleton_deriv]

/--
theorem `DifferentiableAt.derivWithin` / 定理 `DifferentiableAt.derivWithin`

English:
theorem DifferentiableAt.derivWithin
  given: (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  unfold _root_.derivWithin deriv
  rw [h.fderivWithin hxs]

中文:
定理 DifferentiableAt.derivWithin
  条件: (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  unfold _root_.derivWithin deriv
  rw [h.fderivWithin hxs]

Depends on / 依赖: _root_, _root_.derivWithin, derivWithin, fderivWithin, h.fderivWithin
-/
theorem DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold _root_.derivWithin deriv
  rw [h.fderivWithin hxs]

/--
theorem `HasDerivWithinAt.deriv_eq_zero` / 定理 `HasDerivWithinAt.deriv_eq_zero`

English:
theorem HasDerivWithinAt.deriv_eq_zero
  statement: (hd : HasDerivWithinAt f 0 s x)
  proof: (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd

中文:
定理 HasDerivWithinAt.deriv_eq_zero
  结论: (hd : HasDerivWithinAt f 0 s x)
  证明: (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd

Depends on / 依赖: DifferentiableAt, H.eq_deriv, deriv_zero_of_not_differentiableAt, eq_deriv, h.hasDerivAt.hasDerivWithinAt, hasDerivAt, hasDerivWithinAt
-/
theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd

/--
theorem `derivWithin_of_mem_nhdsWithin` / 定理 `derivWithin_of_mem_nhdsWithin`

English:
theorem derivWithin_of_mem_nhdsWithin
  statement: (st : t in 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
  proof: ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem_nhdsWithin st).derivWithin ht

中文:
定理 derivWithin_of_mem_nhdsWithin
  结论: (st : t in 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
  证明: ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem_nhdsWithin st).derivWithin ht

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasDerivWithinAt, derivWithin, hasDerivWithinAt, mono_of_mem_nhdsWithin
-/
theorem derivWithin_of_mem_nhdsWithin (st : t in 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem_nhdsWithin st).derivWithin ht

/--
theorem `derivWithin_subset` / 定理 `derivWithin_subset`

English:
theorem derivWithin_subset
  statement: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  proof: ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht

中文:
定理 derivWithin_subset
  结论: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  证明: ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasDerivWithinAt, derivWithin, hasDerivWithinAt
-/
theorem derivWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht

/--
theorem `derivWithin_congr_set'` / 定理 `derivWithin_congr_set'`

English:
theorem derivWithin_congr_set'
  given: (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by simp only [derivWithin, fderivWithin_congr_set' y h]

中文:
定理 derivWithin_congr_set'
  条件: (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by simp only [derivWithin, fderivWithin_congr_set' y h]

Depends on / 依赖: derivWithin, fderivWithin_congr_set
-/
theorem derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    derivWithin f s x = derivWithin f t x := by simp only [derivWithin, fderivWithin_congr_set' y h]

/--
theorem `derivWithin_congr_set` / 定理 `derivWithin_congr_set`

English:
theorem derivWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  statement: derivWithin f s x = derivWithin f t x
  proof: by
  simp only [derivWithin, fderivWithin_congr_set h]

@[simp]

中文:
定理 derivWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  结论: derivWithin f s x = derivWithin f t x
  证明: by
  simp only [derivWithin, fderivWithin_congr_set h]

@[simp]

Depends on / 依赖: derivWithin, fderivWithin_congr_set
-/
theorem derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin f t x := by
  simp only [derivWithin, fderivWithin_congr_set h]

@[simp]
/--
theorem `derivWithin_univ` / 定理 `derivWithin_univ`

English:
theorem derivWithin_univ
  statement: derivWithin f univ = deriv f
  proof: by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]

中文:
定理 derivWithin_univ
  结论: derivWithin f univ = deriv f
  证明: by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]

Depends on / 依赖: derivWithin, fderivWithin_univ
-/
theorem derivWithin_univ : derivWithin f univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]

/--
theorem `derivWithin_inter` / 定理 `derivWithin_inter`

English:
theorem derivWithin_inter
  given: (ht : t in 𝓝 x)
  statement: derivWithin f (s inter t) x = derivWithin f s x
  proof: by
  unfold derivWithin
  rw [fderivWithin_inter ht]

中文:
定理 derivWithin_inter
  条件: (ht : t in 𝓝 x)
  结论: derivWithin f (s inter t) x = derivWithin f s x
  证明: by
  unfold derivWithin
  rw [fderivWithin_inter ht]

Depends on / 依赖: derivWithin, fderivWithin_inter
-/
theorem derivWithin_inter (ht : t in 𝓝 x) : derivWithin f (s inter t) x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_inter ht]

/--
theorem `derivWithin_of_mem_nhds` / 定理 `derivWithin_of_mem_nhds`

English:
theorem derivWithin_of_mem_nhds
  given: (h : s in 𝓝 x)
  statement: derivWithin f s x = deriv f x
  proof: by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]

中文:
定理 derivWithin_of_mem_nhds
  条件: (h : s in 𝓝 x)
  结论: derivWithin f s x = deriv f x
  证明: by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]

Depends on / 依赖: derivWithin, fderivWithin_of_mem_nhds
-/
theorem derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]

/--
theorem `derivWithin_of_isOpen` / 定理 `derivWithin_of_isOpen`

English:
theorem derivWithin_of_isOpen
  given: (hs : IsOpen s) (hx : x in s)
  statement: derivWithin f s x = deriv f x
  proof: derivWithin_of_mem_nhds (hs.mem_nhds hx)

中文:
定理 derivWithin_of_isOpen
  条件: (hs : IsOpen s) (hx : x in s)
  结论: derivWithin f s x = deriv f x
  证明: derivWithin_of_mem_nhds (hs.mem_nhds hx)

Depends on / 依赖: derivWithin_of_mem_nhds, hs.mem_nhds, mem_nhds
-/
theorem derivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : derivWithin f s x = deriv f x :=
  derivWithin_of_mem_nhds (hs.mem_nhds hx)

/--
lemma `deriv_eqOn` / 引理 `deriv_eqOn`

English:
lemma deriv_eqOn
  given: {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x)
  proof: fun x hx => by
  rw [← derivWithin_of_isOpen hs hx]; rw [(hf' _ hx).derivWithin <| hs.uniqueDiffWithinAt hx]

中文:
引理 deriv_eqOn
  条件: {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : 对任意 x in s, HasDerivWithinAt f (f' x) s x)
  证明: fun x hx => by
  rw [← derivWithin_of_isOpen hs hx]; rw [(hf' _ hx).derivWithin <| hs.uniqueDiffWithinAt hx]

Depends on / 依赖: derivWithin, derivWithin_of_isOpen, hs.uniqueDiffWithinAt, uniqueDiffWithinAt
-/
lemma deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in s, HasDerivWithinAt f (f' x) s x) :
    s.EqOn (deriv f) f' := fun x hx => by
  rw [← derivWithin_of_isOpen hs hx]; rw [(hf' _ hx).derivWithin <| hs.uniqueDiffWithinAt hx]

/--
theorem `deriv_mem_iff` / 定理 `deriv_mem_iff`

English:
theorem deriv_mem_iff
  given: {f : 𝕜 -> F} {s : Set F} {x : 𝕜}
  proof: by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]

中文:
定理 deriv_mem_iff
  条件: {f : 𝕜 -> F} {s : Set F} {x : 𝕜}
  证明: by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]

Depends on / 依赖: DifferentiableAt, deriv_zero_of_not_differentiableAt
-/
theorem deriv_mem_iff {f : 𝕜 -> F} {s : Set F} {x : 𝕜} :
    deriv f x in s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x in s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) in s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]

/--
theorem `derivWithin_mem_iff` / 定理 `derivWithin_mem_iff`

English:
theorem derivWithin_mem_iff
  given: {f : 𝕜 -> F} {t : Set 𝕜} {s : Set F} {x : 𝕜}
  proof: by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]

中文:
定理 derivWithin_mem_iff
  条件: {f : 𝕜 -> F} {t : Set 𝕜} {s : Set F} {x : 𝕜}
  证明: by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]

Depends on / 依赖: DifferentiableWithinAt, derivWithin_zero_of_not_differentiableWithinAt
-/
theorem derivWithin_mem_iff {f : 𝕜 -> F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x in s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x in s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) in s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]

/--
theorem `differentiableWithinAt_Ioi_iff_Ici` / 定理 `differentiableWithinAt_Ioi_iff_Ici`

English:
theorem differentiableWithinAt_Ioi_iff_Ici
  given: [PartialOrder 𝕜]
  proof: ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩

中文:
定理 differentiableWithinAt_Ioi_iff_Ici
  条件: [PartialOrder 𝕜]
  证明: ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩

Depends on / 依赖: Ici_of_Ioi, Ioi_of_Ici, differentiableWithinAt, h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt, hasDerivWithinAt
-/
theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩

-- Golfed while splitting the file
/--
theorem `derivWithin_Ioi_eq_Ici` / 定理 `derivWithin_Ioi_eq_Ici`

English:
theorem derivWithin_Ioi_eq_Ici
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (f : Real -> E)
  proof: by
  by_cases H : DifferentiableWithinAt Real f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq self_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      deriv

中文:
定理 derivWithin_Ioi_eq_Ici
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E] (f : 实数 -> E)
  证明: by
  by_cases H : DifferentiableWithinAt Real f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq self_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      deriv

Depends on / 依赖: DifferentiableWithinAt, H.hasDerivWithinAt.Ici_of_Ioi, Ici_of_Ioi, derivWithin_zero_of_not_differentiableWithinAt, differentiableWithinAt_Ioi_iff_Ici, hasDerivWithinAt, self_mem_Ici, uniqueDiffOn_Ici
-/
theorem derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (f : Real -> E)
    (x : Real) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases H : DifferentiableWithinAt Real f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq self_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H

section congr


/--
theorem `Filter.EventuallyEq.hasDerivAtFilter_iff` / 定理 `Filter.EventuallyEq.hasDerivAtFilter_iff`

English:
theorem Filter.EventuallyEq.hasDerivAtFilter_iff
  statement: (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
  proof: h₀.hasFDerivAtFilter_iff (by simp [h₁])

中文:
定理 Filter.EventuallyEq.hasDerivAtFilter_iff
  结论: (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
  证明: h₀.hasFDerivAtFilter_iff (by simp [h₁])

Depends on / 依赖: hasFDerivAtFilter_iff
-/
theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' L ↔ HasDerivAtFilter f₁ f₁' L :=
  h₀.hasFDerivAtFilter_iff (by simp [h₁])

/--
theorem `HasDerivAtFilter.congr_of_eventuallyEq` / 定理 `HasDerivAtFilter.congr_of_eventuallyEq`

English:
theorem HasDerivAtFilter.congr_of_eventuallyEq
  statement: (h : HasDerivAtFilter f f' L)
  proof: by
  rwa [hL.hasDerivAtFilter_iff rfl]

中文:
定理 HasDerivAtFilter.congr_of_eventuallyEq
  结论: (h : HasDerivAtFilter f f' L)
  证明: by
  rwa [hL.hasDerivAtFilter_iff rfl]

Depends on / 依赖: hL.hasDerivAtFilter_iff, hasDerivAtFilter_iff
-/
theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasDerivAtFilter f₁ f' L := by
  rwa [hL.hasDerivAtFilter_iff rfl]

/--
theorem `HasDerivWithinAt.congr_mono` / 定理 `HasDerivWithinAt.congr_mono`

English:
theorem HasDerivWithinAt.congr_mono
  statement: (h : HasDerivWithinAt f f' s x) (ht : forall x in t, f₁ x = f x)
  proof: HasFDerivWithinAt.congr_mono h ht hx h₁

中文:
定理 HasDerivWithinAt.congr_mono
  结论: (h : HasDerivWithinAt f f' s x) (ht : 对任意 x in t, f₁ x = f x)
  证明: HasFDerivWithinAt.congr_mono h ht hx h₁

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.congr_mono, congr_mono
-/
theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : forall x in t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t subseteq s) : HasDerivWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

/--
theorem `HasDerivWithinAt.congr` / 定理 `HasDerivWithinAt.congr`

English:
theorem HasDerivWithinAt.congr
  statement: (h : HasDerivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
  proof: h.congr_mono hs hx (Subset.refl _)

中文:
定理 HasDerivWithinAt.congr
  结论: (h : HasDerivWithinAt f f' s x) (hs : 对任意 x in s, f₁ x = f x)
  证明: h.congr_mono hs hx (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, congr_mono, h.congr_mono
-/
theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)

/--
theorem `HasDerivWithinAt.congr_of_mem` / 定理 `HasDerivWithinAt.congr_of_mem`

English:
theorem HasDerivWithinAt.congr_of_mem
  statement: (h : HasDerivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
  proof: h.congr hs (hs _ hx)

中文:
定理 HasDerivWithinAt.congr_of_mem
  结论: (h : HasDerivWithinAt f f' s x) (hs : 对任意 x in s, f₁ x = f x)
  证明: h.congr hs (hs _ hx)

Depends on / 依赖: h.congr
-/
theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
    (hx : x in s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

/--
theorem `HasDerivWithinAt.congr_of_eventuallyEq` / 定理 `HasDerivWithinAt.congr_of_eventuallyEq`

English:
theorem HasDerivWithinAt.congr_of_eventuallyEq
  statement: (h : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap hx

中文:
定理 HasDerivWithinAt.congr_of_eventuallyEq
  结论: (h : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap hx

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.congr_of_eventuallyEq, congr_of_eventuallyEq, prodMap
-/
theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap hx

/--
theorem `Filter.EventuallyEq.hasDerivWithinAt_iff` / 定理 `Filter.EventuallyEq.hasDerivWithinAt_iff`

English:
theorem Filter.EventuallyEq.hasDerivWithinAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: ⟨fun h' => h'.congr_of_eventuallyEq h₁.symm hx.symm, fun h' => h'.congr_of_eventuallyEq h₁ hx⟩

中文:
定理 Filter.EventuallyEq.hasDerivWithinAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: ⟨fun h' => h'.congr_of_eventuallyEq h₁.symm hx.symm, fun h' => h'.congr_of_eventuallyEq h₁ hx⟩

Depends on / 依赖: congr_of_eventuallyEq, hx.symm
-/
theorem Filter.EventuallyEq.hasDerivWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' => h'.congr_of_eventuallyEq h₁.symm hx.symm, fun h' => h'.congr_of_eventuallyEq h₁ hx⟩

/--
theorem `HasDerivWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `HasDerivWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem
  statement: (h : HasDerivWithinAt f f' s x)
  proof: h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

中文:
定理 HasDerivWithinAt.congr_of_eventuallyEq_of_mem
  结论: (h : HasDerivWithinAt f f' s x)
  证明: h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

Depends on / 依赖: congr_of_eventuallyEq, eq_of_nhdsWithin, h.congr_of_eventuallyEq
-/
theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

/--
theorem `Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem` / 定理 `Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem`

English:
theorem Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  proof: ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h₁.symm hx,
  fun h' => h'.congr_of_eventuallyEq_of_mem h₁ hx⟩

中文:
定理 Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  证明: ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h₁.symm hx,
  fun h' => h'.congr_of_eventuallyEq_of_mem h₁ hx⟩

Depends on / 依赖: congr_of_eventuallyEq_of_mem
-/
theorem Filter.EventuallyEq.hasDerivWithinAt_iff_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) :
    HasDerivWithinAt f₁ f' s x ↔ HasDerivWithinAt f f' s x :=
  ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h₁.symm hx,
  fun h' => h'.congr_of_eventuallyEq_of_mem h₁ hx⟩

/--
theorem `HasStrictDerivAt.congr_of_eventuallyEq` / 定理 `HasStrictDerivAt.congr_of_eventuallyEq`

English:
theorem HasStrictDerivAt.congr_of_eventuallyEq
  given: (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁)
  proof: HasDerivAtFilter.congr_of_eventuallyEq h (h₁.symm.prodMap_nhds h₁.symm)

中文:
定理 HasStrictDerivAt.congr_of_eventuallyEq
  条件: (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁)
  证明: HasDerivAtFilter.congr_of_eventuallyEq h (h₁.symm.prodMap_nhds h₁.symm)

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.congr_of_eventuallyEq, congr_of_eventuallyEq, prodMap_nhds, symm.prodMap_nhds
-/
theorem HasStrictDerivAt.congr_of_eventuallyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) :
    HasStrictDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h (h₁.symm.prodMap_nhds h₁.symm)

/--
theorem `HasStrictDerivAt.congr_deriv` / 定理 `HasStrictDerivAt.congr_deriv`

English:
theorem HasStrictDerivAt.congr_deriv
  given: (h : HasStrictDerivAt f f' x) (h' : f' = g')
  proof: h.hasStrictFDerivAt.congr_fderiv congr_arg _ h'

中文:
定理 HasStrictDerivAt.congr_deriv
  条件: (h : HasStrictDerivAt f f' x) (h' : f' = g')
  证明: h.hasStrictFDerivAt.congr_fderiv congr_arg _ h'

Depends on / 依赖: congr_arg, congr_fderiv, h.hasStrictFDerivAt.congr_fderiv, hasStrictFDerivAt
-/
theorem HasStrictDerivAt.congr_deriv (h : HasStrictDerivAt f f' x) (h' : f' = g') :
    HasStrictDerivAt f g' x :=
h.hasStrictFDerivAt.congr_fderiv congr_arg _ h'

/--
theorem `HasDerivAt.congr_deriv` / 定理 `HasDerivAt.congr_deriv`

English:
theorem HasDerivAt.congr_deriv
  given: (h : HasDerivAt f f' x) (h' : f' = g')
  statement: HasDerivAt f g' x
  proof: HasFDerivAt.congr_fderiv h congr_arg _ h'

中文:
定理 HasDerivAt.congr_deriv
  条件: (h : HasDerivAt f f' x) (h' : f' = g')
  结论: HasDerivAt f g' x
  证明: HasFDerivAt.congr_fderiv h congr_arg _ h'

Depends on / 依赖: HasFDerivAt, HasFDerivAt.congr_fderiv, congr_arg, congr_fderiv
-/
theorem HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (h' : f' = g') : HasDerivAt f g' x :=
HasFDerivAt.congr_fderiv h congr_arg _ h'

/--
theorem `HasDerivWithinAt.congr_deriv` / 定理 `HasDerivWithinAt.congr_deriv`

English:
theorem HasDerivWithinAt.congr_deriv
  given: (h : HasDerivWithinAt f f' s x) (h' : f' = g')
  proof: HasFDerivWithinAt.congr_fderiv h congr_arg _ h'

中文:
定理 HasDerivWithinAt.congr_deriv
  条件: (h : HasDerivWithinAt f f' s x) (h' : f' = g')
  证明: HasFDerivWithinAt.congr_fderiv h congr_arg _ h'

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.congr_fderiv, congr_arg, congr_fderiv
-/
theorem HasDerivWithinAt.congr_deriv (h : HasDerivWithinAt f f' s x) (h' : f' = g') :
    HasDerivWithinAt f g' s x :=
HasFDerivWithinAt.congr_fderiv h congr_arg _ h'

/--
theorem `HasDerivAt.congr_of_eventuallyEq` / 定理 `HasDerivAt.congr_of_eventuallyEq`

English:
theorem HasDerivAt.congr_of_eventuallyEq
  given: (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap h₁.filter_mono pure_le_nhds _

中文:
定理 HasDerivAt.congr_of_eventuallyEq
  条件: (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap h₁.filter_mono pure_le_nhds _

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.congr_of_eventuallyEq, congr_of_eventuallyEq, filter_mono, prodMap, pure_le_nhds
-/
theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
HasDerivAtFilter.congr_of_eventuallyEq h h₁.prodMap h₁.filter_mono pure_le_nhds _

/--
theorem `Filter.EventuallyEq.hasDerivAt_iff` / 定理 `Filter.EventuallyEq.hasDerivAt_iff`

English:
theorem Filter.EventuallyEq.hasDerivAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁)
  proof: ⟨fun h' => h'.congr_of_eventuallyEq h.symm, fun h' => h'.congr_of_eventuallyEq h⟩

中文:
定理 Filter.EventuallyEq.hasDerivAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁)
  证明: ⟨fun h' => h'.congr_of_eventuallyEq h.symm, fun h' => h'.congr_of_eventuallyEq h⟩

Depends on / 依赖: congr_of_eventuallyEq, h.symm
-/
theorem Filter.EventuallyEq.hasDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x :=
  ⟨fun h' => h'.congr_of_eventuallyEq h.symm, fun h' => h'.congr_of_eventuallyEq h⟩

/--
theorem `Filter.EventuallyEq.derivWithin_eq` / 定理 `Filter.EventuallyEq.derivWithin_eq`

English:
theorem Filter.EventuallyEq.derivWithin_eq
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: by
  unfold derivWithin
  rw [hs.fderivWithin_eq hx]

中文:
定理 Filter.EventuallyEq.derivWithin_eq
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: by
  unfold derivWithin
  rw [hs.fderivWithin_eq hx]

Depends on / 依赖: derivWithin, fderivWithin_eq, hs.fderivWithin_eq
-/
theorem Filter.EventuallyEq.derivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hs.fderivWithin_eq hx]

/--
theorem `Filter.EventuallyEq.derivWithin_eq_of_mem` / 定理 `Filter.EventuallyEq.derivWithin_eq_of_mem`

English:
theorem Filter.EventuallyEq.derivWithin_eq_of_mem
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  proof: hs.derivWithin_eq hs.self_of_nhdsWithin hx

中文:
定理 Filter.EventuallyEq.derivWithin_eq_of_mem
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  证明: hs.derivWithin_eq hs.self_of_nhdsWithin hx

Depends on / 依赖: derivWithin_eq, hs.derivWithin_eq, hs.self_of_nhdsWithin, self_of_nhdsWithin
-/
theorem Filter.EventuallyEq.derivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) :
    derivWithin f₁ s x = derivWithin f s x :=
hs.derivWithin_eq hs.self_of_nhdsWithin hx

/--
theorem `Filter.EventuallyEq.derivWithin_eq_of_nhds` / 定理 `Filter.EventuallyEq.derivWithin_eq_of_nhds`

English:
theorem Filter.EventuallyEq.derivWithin_eq_of_nhds
  given: (hs : f₁ =ᶠ[𝓝 x] f)
  proof: (hs.filter_mono nhdsWithin_le_nhds).derivWithin_eq hs.self_of_nhds

中文:
定理 Filter.EventuallyEq.derivWithin_eq_of_nhds
  条件: (hs : f₁ =ᶠ[𝓝 x] f)
  证明: (hs.filter_mono nhdsWithin_le_nhds).derivWithin_eq hs.self_of_nhds

Depends on / 依赖: derivWithin_eq, filter_mono, hs.filter_mono, hs.self_of_nhds, nhdsWithin_le_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.derivWithin_eq_of_nhds (hs : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x :=
  (hs.filter_mono nhdsWithin_le_nhds).derivWithin_eq hs.self_of_nhds

/--
theorem `derivWithin_congr` / 定理 `derivWithin_congr`

English:
theorem derivWithin_congr
  given: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  proof: by
  unfold derivWithin
  rw [fderivWithin_congr hs hx]

中文:
定理 derivWithin_congr
  条件: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  证明: by
  unfold derivWithin
  rw [fderivWithin_congr hs hx]

Depends on / 依赖: derivWithin, fderivWithin_congr
-/
theorem derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_congr hs hx]

/--
lemma `Set.EqOn.deriv` / 引理 `Set.EqOn.deriv`

English:
lemma Set.EqOn.deriv
  given: {f g : 𝕜 -> F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s)
  proof: by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]; rw [← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

中文:
引理 Set.EqOn.deriv
  条件: {f g : 𝕜 -> F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s)
  证明: by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]; rw [← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

Depends on / 依赖: derivWithin_congr, derivWithin_of_isOpen
-/
lemma Set.EqOn.deriv {f g : 𝕜 -> F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) (deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]; rw [← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

/--
theorem `Filter.EventuallyEq.deriv_eq` / 定理 `Filter.EventuallyEq.deriv_eq`

English:
theorem Filter.EventuallyEq.deriv_eq
  given: (hL : f₁ =ᶠ[𝓝 x] f)
  statement: deriv f₁ x = deriv f x
  proof: by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]

中文:
定理 Filter.EventuallyEq.deriv_eq
  条件: (hL : f₁ =ᶠ[𝓝 x] f)
  结论: deriv f₁ x = deriv f x
  证明: by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.fderiv_eq, fderiv_eq
-/
theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]

/--
lemma `Filter.EventuallyEq.derivWithin'` / 引理 `Filter.EventuallyEq.derivWithin'`

English:
lemma Filter.EventuallyEq.derivWithin'
  given: (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s)
  proof: by
  unfold derivWithin
.fun_comp (fun a => a 1) exact h.fderivWithin' ht

中文:
引理 Filter.EventuallyEq.derivWithin'
  条件: (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s)
  证明: by
  unfold derivWithin
.fun_comp (fun a => a 1) exact h.fderivWithin' ht

Depends on / 依赖: derivWithin, fderivWithin, fun_comp, h.fderivWithin
-/
lemma Filter.EventuallyEq.derivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) :
    derivWithin f₁ t =ᶠ[𝓝[s] x] derivWithin f t := by
  unfold derivWithin
.fun_comp (fun a => a 1) exact h.fderivWithin' ht

/--
lemma `Filter.EventuallyEq.derivWithin` / 引理 `Filter.EventuallyEq.derivWithin`

English:
lemma Filter.EventuallyEq.derivWithin
  given: (h : f₁ =ᶠ[𝓝[s] x] f)
  proof: h.derivWithin' Subset.rfl

中文:
引理 Filter.EventuallyEq.derivWithin
  条件: (h : f₁ =ᶠ[𝓝[s] x] f)
  证明: h.derivWithin' Subset.rfl
-/
protected lemma Filter.EventuallyEq.derivWithin (h : f₁ =ᶠ[𝓝[s] x] f) :
    derivWithin f₁ s =ᶠ[𝓝[s] x] derivWithin f s := h.derivWithin' Subset.rfl

/--
theorem `Filter.EventuallyEq.deriv` / 定理 `Filter.EventuallyEq.deriv`

English:
theorem Filter.EventuallyEq.deriv
  given: (h : f₁ =ᶠ[𝓝 x] f)
  statement: deriv f₁ =ᶠ[𝓝 x] deriv f
  proof: h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq

中文:
定理 Filter.EventuallyEq.deriv
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  结论: deriv f₁ =ᶠ[𝓝 x] deriv f
  证明: h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq
-/
protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq

/--
theorem `Filter.EventuallyEq.nhdsNE_deriv` / 定理 `Filter.EventuallyEq.nhdsNE_deriv`

English:
theorem Filter.EventuallyEq.nhdsNE_deriv
  given: (h : f₁ =ᶠ[𝓝[!=] x] f)
  statement: deriv f₁ =ᶠ[𝓝[!=] x] deriv f
  proof: by
  rw [Filter.EventuallyEq]; rw [← eventually_nhdsNE_eventually_nhds_iff] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

中文:
定理 Filter.EventuallyEq.nhdsNE_deriv
  条件: (h : f₁ =ᶠ[𝓝[!=] x] f)
  结论: deriv f₁ =ᶠ[𝓝[!=] x] deriv f
  证明: by
  rw [Filter.EventuallyEq]; rw [← eventually_nhdsNE_eventually_nhds_iff] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Filter.EventuallyEq.deriv, eventually_nhdsNE_eventually_nhds_iff, filter_upwards
-/
theorem Filter.EventuallyEq.nhdsNE_deriv (h : f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=] x] deriv f := by
  rw [Filter.EventuallyEq]; rw [← eventually_nhdsNE_eventually_nhds_iff] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

end congr

section id

/-! ### Derivative of the identity -/

variable (s x L)

/--
theorem `hasDerivAtFilter_id` / 定理 `hasDerivAtFilter_id`

English:
theorem hasDerivAtFilter_id
  statement: HasDerivAtFilter id 1 L
  proof: (hasFDerivAtFilter_id L).hasDerivAtFilter

中文:
定理 hasDerivAtFilter_id
  结论: HasDerivAtFilter id 1 L
  证明: (hasFDerivAtFilter_id L).hasDerivAtFilter

Depends on / 依赖: hasDerivAtFilter, hasFDerivAtFilter_id
-/
theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 L :=
  (hasFDerivAtFilter_id L).hasDerivAtFilter

/--
theorem `hasDerivWithinAt_id` / 定理 `hasDerivWithinAt_id`

English:
theorem hasDerivWithinAt_id
  statement: HasDerivWithinAt id 1 s x
  proof: hasDerivAtFilter_id _

中文:
定理 hasDerivWithinAt_id
  结论: HasDerivWithinAt id 1 s x
  证明: hasDerivAtFilter_id _

Depends on / 依赖: hasDerivAtFilter_id
-/
theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _

/--
theorem `hasDerivAt_id` / 定理 `hasDerivAt_id`

English:
theorem hasDerivAt_id
  statement: HasDerivAt id 1 x
  proof: hasDerivAtFilter_id _

中文:
定理 hasDerivAt_id
  结论: HasDerivAt id 1 x
  证明: hasDerivAtFilter_id _

Depends on / 依赖: hasDerivAtFilter_id
-/
theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _

/--
theorem `hasDerivAt_id'` / 定理 `hasDerivAt_id'`

English:
theorem hasDerivAt_id'
  statement: HasDerivAt (fun x : 𝕜 => x) 1 x
  proof: hasDerivAtFilter_id _

中文:
定理 hasDerivAt_id'
  结论: HasDerivAt (fun x : 𝕜 => x) 1 x
  证明: hasDerivAtFilter_id _

Depends on / 依赖: hasDerivAtFilter_id
-/
theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _

/--
theorem `hasStrictDerivAt_id` / 定理 `hasStrictDerivAt_id`

English:
theorem hasStrictDerivAt_id
  statement: HasStrictDerivAt id 1 x
  proof: hasDerivAtFilter_id _

中文:
定理 hasStrictDerivAt_id
  结论: HasStrictDerivAt id 1 x
  证明: hasDerivAtFilter_id _

Depends on / 依赖: hasDerivAtFilter_id
-/
theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  hasDerivAtFilter_id _

/--
theorem `deriv_id` / 定理 `deriv_id`

English:
theorem deriv_id
  statement: deriv id x = 1
  proof: HasDerivAt.deriv (hasDerivAt_id x)

@[simp]

中文:
定理 deriv_id
  结论: deriv id x = 1
  证明: HasDerivAt.deriv (hasDerivAt_id x)

@[simp]

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, hasDerivAt_id
-/
theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)

@[simp]
/--
theorem `deriv_id'` / 定理 `deriv_id'`

English:
theorem deriv_id'
  statement: deriv (@id 𝕜) = fun _ => 1
  proof: funext deriv_id

中文:
定理 deriv_id'
  结论: deriv (@id 𝕜) = fun _ => 1
  证明: funext deriv_id

Depends on / 依赖: deriv_id
-/
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id

/-- Variant with `fun x => x` rather than `id` -/
@[simp]
/--
theorem `deriv_id''` / 定理 `deriv_id''`

English:
theorem deriv_id''
  statement: (deriv fun x : 𝕜 => x) = fun _ => 1
  proof: deriv_id'

中文:
定理 deriv_id''
  结论: (deriv fun x : 𝕜 => x) = fun _ => 1
  证明: deriv_id'

Depends on / 依赖: deriv_id
-/
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'

/--
theorem `derivWithin_id` / 定理 `derivWithin_id`

English:
theorem derivWithin_id
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  statement: derivWithin id s x = 1
  proof: (hasDerivWithinAt_id x s).derivWithin hxs

中文:
定理 derivWithin_id
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  结论: derivWithin id s x = 1
  证明: (hasDerivWithinAt_id x s).derivWithin hxs

Depends on / 依赖: derivWithin, hasDerivWithinAt_id
-/
theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs

/--
theorem `derivWithin_id'` / 定理 `derivWithin_id'`

English:
theorem derivWithin_id'
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  statement: derivWithin (fun x => x) s x = 1
  proof: derivWithin_id x s hxs

中文:
定理 derivWithin_id'
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  结论: derivWithin (fun x => x) s x = 1
  证明: derivWithin_id x s hxs

Depends on / 依赖: derivWithin_id
-/
theorem derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => x) s x = 1 :=
  derivWithin_id x s hxs

end id

section Const

/-! ### Derivative of constant functions

This include the constant functions `0`, `1`, `Nat.cast n`, `Int.cast z`, and other numerals.
-/

variable (c : F) (s x L)

/--
theorem `hasDerivAtFilter_const` / 定理 `hasDerivAtFilter_const`

English:
theorem hasDerivAtFilter_const
  statement: HasDerivAtFilter (fun _ => c) 0 L
  proof: (hasFDerivAtFilter_const c L).hasDerivAtFilter

中文:
定理 hasDerivAtFilter_const
  结论: HasDerivAtFilter (fun _ => c) 0 L
  证明: (hasFDerivAtFilter_const c L).hasDerivAtFilter

Depends on / 依赖: hasDerivAtFilter, hasFDerivAtFilter_const
-/
theorem hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 L :=
  (hasFDerivAtFilter_const c L).hasDerivAtFilter

/--
theorem `hasDerivAtFilter_zero` / 定理 `hasDerivAtFilter_zero`

English:
theorem hasDerivAtFilter_zero
  statement: HasDerivAtFilter (0 : 𝕜 -> F) 0 L
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivAtFilter_zero
  结论: HasDerivAtFilter (0 : 𝕜 -> F) 0 L
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAtFilter_zero : HasDerivAtFilter (0 : 𝕜 -> F) 0 L :=
  hasDerivAtFilter_const _ _

/--
theorem `hasDerivAtFilter_one` / 定理 `hasDerivAtFilter_one`

English:
theorem hasDerivAtFilter_one
  given: [One F]
  statement: HasDerivAtFilter (1 : 𝕜 -> F) 0 L
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivAtFilter_one
  条件: [One F]
  结论: HasDerivAtFilter (1 : 𝕜 -> F) 0 L
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAtFilter_one [One F] : HasDerivAtFilter (1 : 𝕜 -> F) 0 L :=
  hasDerivAtFilter_const _ _

/--
theorem `hasDerivAtFilter_natCast` / 定理 `hasDerivAtFilter_natCast`

English:
theorem hasDerivAtFilter_natCast
  given: [NatCast F] (n : Nat)
  statement: HasDerivAtFilter (n : 𝕜 -> F) 0 L
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivAtFilter_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: HasDerivAtFilter (n : 𝕜 -> F) 0 L
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAtFilter_natCast [NatCast F] (n : Nat) : HasDerivAtFilter (n : 𝕜 -> F) 0 L :=
  hasDerivAtFilter_const _ _

/--
theorem `hasDerivAtFilter_intCast` / 定理 `hasDerivAtFilter_intCast`

English:
theorem hasDerivAtFilter_intCast
  given: [IntCast F] (z : Int)
  statement: HasDerivAtFilter (z : 𝕜 -> F) 0 L
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivAtFilter_intCast
  条件: [整数Cast F] (z : 整数)
  结论: HasDerivAtFilter (z : 𝕜 -> F) 0 L
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAtFilter_intCast [IntCast F] (z : Int) : HasDerivAtFilter (z : 𝕜 -> F) 0 L :=
  hasDerivAtFilter_const _ _

/--
theorem `hasDerivAtFilter_ofNat` / 定理 `hasDerivAtFilter_ofNat`

English:
theorem hasDerivAtFilter_ofNat
  given: (n : Nat) [OfNat F n]
  statement: HasDerivAtFilter (ofNat(n) : 𝕜 -> F) 0 L
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivAtFilter_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: HasDerivAtFilter (of自然数(n) : 𝕜 -> F) 0 L
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAtFilter_ofNat (n : Nat) [OfNat F n] : HasDerivAtFilter (ofNat(n) : 𝕜 -> F) 0 L :=
  hasDerivAtFilter_const _ _

/--
theorem `hasStrictDerivAt_const` / 定理 `hasStrictDerivAt_const`

English:
theorem hasStrictDerivAt_const
  statement: HasStrictDerivAt (fun _ => c) 0 x
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasStrictDerivAt_const
  结论: HasStrictDerivAt (fun _ => c) 0 x
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _

/--
theorem `hasStrictDerivAt_zero` / 定理 `hasStrictDerivAt_zero`

English:
theorem hasStrictDerivAt_zero
  statement: HasStrictDerivAt (0 : 𝕜 -> F) 0 x
  proof: hasStrictDerivAt_const _ _

中文:
定理 hasStrictDerivAt_zero
  结论: HasStrictDerivAt (0 : 𝕜 -> F) 0 x
  证明: hasStrictDerivAt_const _ _

Depends on / 依赖: hasStrictDerivAt_const
-/
theorem hasStrictDerivAt_zero : HasStrictDerivAt (0 : 𝕜 -> F) 0 x :=
  hasStrictDerivAt_const _ _

/--
theorem `hasStrictDerivAt_one` / 定理 `hasStrictDerivAt_one`

English:
theorem hasStrictDerivAt_one
  given: [One F]
  statement: HasStrictDerivAt (1 : 𝕜 -> F) 0 x
  proof: hasStrictDerivAt_const _ _

中文:
定理 hasStrictDerivAt_one
  条件: [One F]
  结论: HasStrictDerivAt (1 : 𝕜 -> F) 0 x
  证明: hasStrictDerivAt_const _ _

Depends on / 依赖: hasStrictDerivAt_const
-/
theorem hasStrictDerivAt_one [One F] : HasStrictDerivAt (1 : 𝕜 -> F) 0 x :=
  hasStrictDerivAt_const _ _

/--
theorem `hasStrictDerivAt_natCast` / 定理 `hasStrictDerivAt_natCast`

English:
theorem hasStrictDerivAt_natCast
  given: [NatCast F] (n : Nat)
  statement: HasStrictDerivAt (n : 𝕜 -> F) 0 x
  proof: hasStrictDerivAt_const _ _

中文:
定理 hasStrictDerivAt_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: HasStrictDerivAt (n : 𝕜 -> F) 0 x
  证明: hasStrictDerivAt_const _ _

Depends on / 依赖: hasStrictDerivAt_const
-/
theorem hasStrictDerivAt_natCast [NatCast F] (n : Nat) : HasStrictDerivAt (n : 𝕜 -> F) 0 x :=
  hasStrictDerivAt_const _ _

/--
theorem `hasStrictDerivAt_intCast` / 定理 `hasStrictDerivAt_intCast`

English:
theorem hasStrictDerivAt_intCast
  given: [IntCast F] (z : Int)
  statement: HasStrictDerivAt (z : 𝕜 -> F) 0 x
  proof: hasStrictDerivAt_const _ _

中文:
定理 hasStrictDerivAt_intCast
  条件: [整数Cast F] (z : 整数)
  结论: HasStrictDerivAt (z : 𝕜 -> F) 0 x
  证明: hasStrictDerivAt_const _ _

Depends on / 依赖: hasStrictDerivAt_const
-/
theorem hasStrictDerivAt_intCast [IntCast F] (z : Int) : HasStrictDerivAt (z : 𝕜 -> F) 0 x :=
  hasStrictDerivAt_const _ _

/--
theorem `HasStrictDerivAt_ofNat` / 定理 `HasStrictDerivAt_ofNat`

English:
theorem HasStrictDerivAt_ofNat
  given: (n : Nat) [OfNat F n]
  statement: HasStrictDerivAt (ofNat(n) : 𝕜 -> F) 0 x
  proof: hasStrictDerivAt_const _ _

中文:
定理 HasStrictDerivAt_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: HasStrictDerivAt (of自然数(n) : 𝕜 -> F) 0 x
  证明: hasStrictDerivAt_const _ _

Depends on / 依赖: hasStrictDerivAt_const
-/
theorem HasStrictDerivAt_ofNat (n : Nat) [OfNat F n] : HasStrictDerivAt (ofNat(n) : 𝕜 -> F) 0 x :=
  hasStrictDerivAt_const _ _

/--
theorem `hasDerivWithinAt_const` / 定理 `hasDerivWithinAt_const`

English:
theorem hasDerivWithinAt_const
  statement: HasDerivWithinAt (fun _ => c) 0 s x
  proof: hasDerivAtFilter_const _ _

中文:
定理 hasDerivWithinAt_const
  结论: HasDerivWithinAt (fun _ => c) 0 s x
  证明: hasDerivAtFilter_const _ _

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
  hasDerivAtFilter_const _ _

/--
theorem `hasDerivWithinAt_zero` / 定理 `hasDerivWithinAt_zero`

English:
theorem hasDerivWithinAt_zero
  statement: HasDerivWithinAt (0 : 𝕜 -> F) 0 s x
  proof: hasDerivAtFilter_zero _

中文:
定理 hasDerivWithinAt_zero
  结论: HasDerivWithinAt (0 : 𝕜 -> F) 0 s x
  证明: hasDerivAtFilter_zero _

Depends on / 依赖: hasDerivAtFilter_zero
-/
theorem hasDerivWithinAt_zero : HasDerivWithinAt (0 : 𝕜 -> F) 0 s x :=
  hasDerivAtFilter_zero _

/--
theorem `hasDerivWithinAt_one` / 定理 `hasDerivWithinAt_one`

English:
theorem hasDerivWithinAt_one
  given: [One F]
  statement: HasDerivWithinAt (1 : 𝕜 -> F) 0 s x
  proof: hasDerivWithinAt_const _ _ _

中文:
定理 hasDerivWithinAt_one
  条件: [One F]
  结论: HasDerivWithinAt (1 : 𝕜 -> F) 0 s x
  证明: hasDerivWithinAt_const _ _ _

Depends on / 依赖: hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_one [One F] : HasDerivWithinAt (1 : 𝕜 -> F) 0 s x :=
  hasDerivWithinAt_const _ _ _

/--
theorem `hasDerivWithinAt_natCast` / 定理 `hasDerivWithinAt_natCast`

English:
theorem hasDerivWithinAt_natCast
  given: [NatCast F] (n : Nat)
  statement: HasDerivWithinAt (n : 𝕜 -> F) 0 s x
  proof: hasDerivWithinAt_const _ _ _

中文:
定理 hasDerivWithinAt_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: HasDerivWithinAt (n : 𝕜 -> F) 0 s x
  证明: hasDerivWithinAt_const _ _ _

Depends on / 依赖: hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_natCast [NatCast F] (n : Nat) : HasDerivWithinAt (n : 𝕜 -> F) 0 s x :=
  hasDerivWithinAt_const _ _ _

/--
theorem `hasDerivWithinAt_intCast` / 定理 `hasDerivWithinAt_intCast`

English:
theorem hasDerivWithinAt_intCast
  given: [IntCast F] (z : Int)
  statement: HasDerivWithinAt (z : 𝕜 -> F) 0 s x
  proof: hasDerivWithinAt_const _ _ _

中文:
定理 hasDerivWithinAt_intCast
  条件: [整数Cast F] (z : 整数)
  结论: HasDerivWithinAt (z : 𝕜 -> F) 0 s x
  证明: hasDerivWithinAt_const _ _ _

Depends on / 依赖: hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_intCast [IntCast F] (z : Int) : HasDerivWithinAt (z : 𝕜 -> F) 0 s x :=
  hasDerivWithinAt_const _ _ _

/--
theorem `hasDerivWithinAt_ofNat` / 定理 `hasDerivWithinAt_ofNat`

English:
theorem hasDerivWithinAt_ofNat
  given: (n : Nat) [OfNat F n]
  statement: HasDerivWithinAt (ofNat(n) : 𝕜 -> F) 0 s x
  proof: hasDerivWithinAt_const _ _ _

中文:
定理 hasDerivWithinAt_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: HasDerivWithinAt (of自然数(n) : 𝕜 -> F) 0 s x
  证明: hasDerivWithinAt_const _ _ _

Depends on / 依赖: hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_ofNat (n : Nat) [OfNat F n] : HasDerivWithinAt (ofNat(n) : 𝕜 -> F) 0 s x :=
  hasDerivWithinAt_const _ _ _

/--
theorem `hasDerivAt_const` / 定理 `hasDerivAt_const`

English:
theorem hasDerivAt_const
  statement: HasDerivAt (fun _ => c) 0 x
  proof: hasDerivAtFilter_const _ _

@[simp]

中文:
定理 hasDerivAt_const
  结论: HasDerivAt (fun _ => c) 0 x
  证明: hasDerivAtFilter_const _ _

@[simp]

Depends on / 依赖: hasDerivAtFilter_const
-/
theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _

@[simp]
/--
theorem `hasDerivAt_zero` / 定理 `hasDerivAt_zero`

English:
theorem hasDerivAt_zero
  statement: HasDerivAt (0 : 𝕜 -> F) 0 x
  proof: hasDerivAtFilter_zero _

中文:
定理 hasDerivAt_zero
  结论: HasDerivAt (0 : 𝕜 -> F) 0 x
  证明: hasDerivAtFilter_zero _

Depends on / 依赖: hasDerivAtFilter_zero
-/
theorem hasDerivAt_zero : HasDerivAt (0 : 𝕜 -> F) 0 x :=
  hasDerivAtFilter_zero _

/--
theorem `hasDerivAt_one` / 定理 `hasDerivAt_one`

English:
theorem hasDerivAt_one
  given: [One F]
  statement: HasDerivAt (1 : 𝕜 -> F) 0 x
  proof: hasDerivAt_const _ _

中文:
定理 hasDerivAt_one
  条件: [One F]
  结论: HasDerivAt (1 : 𝕜 -> F) 0 x
  证明: hasDerivAt_const _ _

Depends on / 依赖: hasDerivAt_const
-/
theorem hasDerivAt_one [One F] : HasDerivAt (1 : 𝕜 -> F) 0 x :=
  hasDerivAt_const _ _

/--
theorem `hasDerivAt_natCast` / 定理 `hasDerivAt_natCast`

English:
theorem hasDerivAt_natCast
  given: [NatCast F] (n : Nat)
  statement: HasDerivAt (n : 𝕜 -> F) 0 x
  proof: hasDerivAt_const _ _

中文:
定理 hasDerivAt_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: HasDerivAt (n : 𝕜 -> F) 0 x
  证明: hasDerivAt_const _ _

Depends on / 依赖: hasDerivAt_const
-/
theorem hasDerivAt_natCast [NatCast F] (n : Nat) : HasDerivAt (n : 𝕜 -> F) 0 x :=
  hasDerivAt_const _ _

/--
theorem `hasDerivAt_intCast` / 定理 `hasDerivAt_intCast`

English:
theorem hasDerivAt_intCast
  given: [IntCast F] (z : Int)
  statement: HasDerivAt (z : 𝕜 -> F) 0 x
  proof: hasDerivAt_const _ _

中文:
定理 hasDerivAt_intCast
  条件: [整数Cast F] (z : 整数)
  结论: HasDerivAt (z : 𝕜 -> F) 0 x
  证明: hasDerivAt_const _ _

Depends on / 依赖: hasDerivAt_const
-/
theorem hasDerivAt_intCast [IntCast F] (z : Int) : HasDerivAt (z : 𝕜 -> F) 0 x :=
  hasDerivAt_const _ _

/--
theorem `hasDerivAt_ofNat` / 定理 `hasDerivAt_ofNat`

English:
theorem hasDerivAt_ofNat
  given: (n : Nat) [OfNat F n]
  statement: HasDerivAt (ofNat(n) : 𝕜 -> F) 0 x
  proof: hasDerivAt_const _ _

中文:
定理 hasDerivAt_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: HasDerivAt (of自然数(n) : 𝕜 -> F) 0 x
  证明: hasDerivAt_const _ _

Depends on / 依赖: hasDerivAt_const
-/
theorem hasDerivAt_ofNat (n : Nat) [OfNat F n] : HasDerivAt (ofNat(n) : 𝕜 -> F) 0 x :=
  hasDerivAt_const _ _

/--
theorem `deriv_const` / 定理 `deriv_const`

English:
theorem deriv_const
  statement: deriv (fun _ => c) x = 0
  proof: HasDerivAt.deriv (hasDerivAt_const x c)

@[simp]

中文:
定理 deriv_const
  结论: deriv (fun _ => c) x = 0
  证明: HasDerivAt.deriv (hasDerivAt_const x c)

@[simp]

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, hasDerivAt_const
-/
theorem deriv_const : deriv (fun _ => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)

@[simp]
/--
theorem `deriv_const'` / 定理 `deriv_const'`

English:
theorem deriv_const'
  statement: (deriv fun _ : 𝕜 => c) = fun _ => 0
  proof: funext fun x => deriv_const x c

@[simp]

中文:
定理 deriv_const'
  结论: (deriv fun _ : 𝕜 => c) = fun _ => 0
  证明: funext fun x => deriv_const x c

@[simp]

Depends on / 依赖: deriv_const
-/
theorem deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => deriv_const x c

@[simp]
/--
theorem `deriv_zero` / 定理 `deriv_zero`

English:
theorem deriv_zero
  statement: deriv (0 : 𝕜 -> F) = 0
  proof: funext fun _ => deriv_const _ _

@[simp]

中文:
定理 deriv_zero
  结论: deriv (0 : 𝕜 -> F) = 0
  证明: funext fun _ => deriv_const _ _

@[simp]

Depends on / 依赖: deriv_const
-/
theorem deriv_zero : deriv (0 : 𝕜 -> F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/--
theorem `deriv_one` / 定理 `deriv_one`

English:
theorem deriv_one
  given: [One F]
  statement: deriv (1 : 𝕜 -> F) = 0
  proof: funext fun _ => deriv_const _ _

@[simp]

中文:
定理 deriv_one
  条件: [One F]
  结论: deriv (1 : 𝕜 -> F) = 0
  证明: funext fun _ => deriv_const _ _

@[simp]

Depends on / 依赖: deriv_const
-/
theorem deriv_one [One F] : deriv (1 : 𝕜 -> F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/--
theorem `deriv_natCast` / 定理 `deriv_natCast`

English:
theorem deriv_natCast
  given: [NatCast F] (n : Nat)
  statement: deriv (n : 𝕜 -> F) = 0
  proof: funext fun _ => deriv_const _ _

@[simp]

中文:
定理 deriv_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: deriv (n : 𝕜 -> F) = 0
  证明: funext fun _ => deriv_const _ _

@[simp]

Depends on / 依赖: deriv_const
-/
theorem deriv_natCast [NatCast F] (n : Nat) : deriv (n : 𝕜 -> F) = 0 := funext fun _ => deriv_const _ _

@[simp]
/--
theorem `deriv_intCast` / 定理 `deriv_intCast`

English:
theorem deriv_intCast
  given: [IntCast F] (z : Int)
  statement: deriv (z : 𝕜 -> F) = 0
  proof: funext fun _ => deriv_const _ _

@[simp low]

中文:
定理 deriv_intCast
  条件: [整数Cast F] (z : 整数)
  结论: deriv (z : 𝕜 -> F) = 0
  证明: funext fun _ => deriv_const _ _

@[simp low]

Depends on / 依赖: deriv_const
-/
theorem deriv_intCast [IntCast F] (z : Int) : deriv (z : 𝕜 -> F) = 0 := funext fun _ => deriv_const _ _

@[simp low]
/--
theorem `deriv_ofNat` / 定理 `deriv_ofNat`

English:
theorem deriv_ofNat
  given: (n : Nat) [OfNat F n]
  statement: deriv (ofNat(n) : 𝕜 -> F) = 0
  proof: funext fun _ => deriv_const _ _

@[simp]

中文:
定理 deriv_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: deriv (of自然数(n) : 𝕜 -> F) = 0
  证明: funext fun _ => deriv_const _ _

@[simp]

Depends on / 依赖: deriv_const
-/
theorem deriv_ofNat (n : Nat) [OfNat F n] : deriv (ofNat(n) : 𝕜 -> F) = 0 :=
  funext fun _ => deriv_const _ _

@[simp]
/--
theorem `derivWithin_fun_const` / 定理 `derivWithin_fun_const`

English:
theorem derivWithin_fun_const
  statement: derivWithin (fun _ => c) s = 0
  proof: by
  ext; simp [derivWithin]

@[simp]

中文:
定理 derivWithin_fun_const
  结论: derivWithin (fun _ => c) s = 0
  证明: by
  ext; simp [derivWithin]

@[simp]

Depends on / 依赖: derivWithin
-/
theorem derivWithin_fun_const : derivWithin (fun _ => c) s = 0 := by
  ext; simp [derivWithin]

@[simp]
/--
theorem `derivWithin_const` / 定理 `derivWithin_const`

English:
theorem derivWithin_const
  statement: derivWithin (Function.const 𝕜 c) s = 0
  proof: derivWithin_fun_const _ _

@[simp]

中文:
定理 derivWithin_const
  结论: derivWithin (Function.const 𝕜 c) s = 0
  证明: derivWithin_fun_const _ _

@[simp]

Depends on / 依赖: derivWithin_fun_const
-/
theorem derivWithin_const : derivWithin (Function.const 𝕜 c) s = 0 :=
  derivWithin_fun_const _ _

@[simp]
/--
theorem `derivWithin_zero` / 定理 `derivWithin_zero`

English:
theorem derivWithin_zero
  statement: derivWithin (0 : 𝕜 -> F) s = 0
  proof: derivWithin_const _ _

@[simp]

中文:
定理 derivWithin_zero
  结论: derivWithin (0 : 𝕜 -> F) s = 0
  证明: derivWithin_const _ _

@[simp]

Depends on / 依赖: derivWithin_const
-/
theorem derivWithin_zero : derivWithin (0 : 𝕜 -> F) s = 0 := derivWithin_const _ _

@[simp]
/--
theorem `derivWithin_one` / 定理 `derivWithin_one`

English:
theorem derivWithin_one
  given: [One F]
  statement: derivWithin (1 : 𝕜 -> F) s = 0
  proof: derivWithin_const _ _

@[simp]

中文:
定理 derivWithin_one
  条件: [One F]
  结论: derivWithin (1 : 𝕜 -> F) s = 0
  证明: derivWithin_const _ _

@[simp]

Depends on / 依赖: derivWithin_const
-/
theorem derivWithin_one [One F] : derivWithin (1 : 𝕜 -> F) s = 0 := derivWithin_const _ _

@[simp]
/--
theorem `derivWithin_natCast` / 定理 `derivWithin_natCast`

English:
theorem derivWithin_natCast
  given: [NatCast F] (n : Nat)
  statement: derivWithin (n : 𝕜 -> F) s = 0
  proof: derivWithin_const _ _

@[simp]

中文:
定理 derivWithin_natCast
  条件: [自然数Cast F] (n : 自然数)
  结论: derivWithin (n : 𝕜 -> F) s = 0
  证明: derivWithin_const _ _

@[simp]

Depends on / 依赖: derivWithin_const
-/
theorem derivWithin_natCast [NatCast F] (n : Nat) : derivWithin (n : 𝕜 -> F) s = 0 :=
  derivWithin_const _ _

@[simp]
/--
theorem `derivWithin_intCast` / 定理 `derivWithin_intCast`

English:
theorem derivWithin_intCast
  given: [IntCast F] (z : Int)
  statement: derivWithin (z : 𝕜 -> F) s = 0
  proof: derivWithin_const _ _

@[simp low]

中文:
定理 derivWithin_intCast
  条件: [整数Cast F] (z : 整数)
  结论: derivWithin (z : 𝕜 -> F) s = 0
  证明: derivWithin_const _ _

@[simp low]

Depends on / 依赖: derivWithin_const
-/
theorem derivWithin_intCast [IntCast F] (z : Int) : derivWithin (z : 𝕜 -> F) s = 0 :=
  derivWithin_const _ _

@[simp low]
/--
theorem `derivWithin_ofNat` / 定理 `derivWithin_ofNat`

English:
theorem derivWithin_ofNat
  given: (n : Nat) [OfNat F n]
  statement: derivWithin (ofNat(n) : 𝕜 -> F) s = 0
  proof: derivWithin_const _ _

中文:
定理 derivWithin_ofNat
  条件: (n : 自然数) [Of自然数 F n]
  结论: derivWithin (of自然数(n) : 𝕜 -> F) s = 0
  证明: derivWithin_const _ _

Depends on / 依赖: derivWithin_const
-/
theorem derivWithin_ofNat (n : Nat) [OfNat F n] : derivWithin (ofNat(n) : 𝕜 -> F) s = 0 :=
  derivWithin_const _ _

end Const

section Continuous


/--
theorem `HasDerivAtFilter.tendsto_nhds` / 定理 `HasDerivAtFilter.tendsto_nhds`

English:
theorem HasDerivAtFilter.tendsto_nhds
  statement: {L : Filter 𝕜} (hL : L <= 𝓝 x)
  proof: h.hasFDerivAtFilter.tendsto_nhds hL

中文:
定理 HasDerivAtFilter.tendsto_nhds
  结论: {L : Filter 𝕜} (hL : L <= 𝓝 x)
  证明: h.hasFDerivAtFilter.tendsto_nhds hL

Depends on / 依赖: h.hasFDerivAtFilter.tendsto_nhds, hasFDerivAtFilter, tendsto_nhds
-/
theorem HasDerivAtFilter.tendsto_nhds {L : Filter 𝕜} (hL : L <= 𝓝 x)
    (h : HasDerivAtFilter f f' (L ×ˢ pure x)) :
    Tendsto f L (𝓝 (f x)) :=
  h.hasFDerivAtFilter.tendsto_nhds hL

/--
theorem `HasDerivWithinAt.continuousWithinAt` / 定理 `HasDerivWithinAt.continuousWithinAt`

English:
theorem HasDerivWithinAt.continuousWithinAt
  given: (h : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.tendsto_nhds inf_le_left h

中文:
定理 HasDerivWithinAt.continuousWithinAt
  条件: (h : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.tendsto_nhds inf_le_left h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.tendsto_nhds, inf_le_left, tendsto_nhds
-/
theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h

/--
theorem `HasDerivAt.continuousAt` / 定理 `HasDerivAt.continuousAt`

English:
theorem HasDerivAt.continuousAt
  given: (h : HasDerivAt f f' x)
  statement: ContinuousAt f x
  proof: HasDerivAtFilter.tendsto_nhds le_rfl h

中文:
定理 HasDerivAt.continuousAt
  条件: (h : HasDerivAt f f' x)
  结论: ContinuousAt f x
  证明: HasDerivAtFilter.tendsto_nhds le_rfl h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.tendsto_nhds, le_rfl, tendsto_nhds
-/
theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h

/--
theorem `HasDerivWithinAt.continuousOn` / 定理 `HasDerivWithinAt.continuousOn`

English:
theorem HasDerivWithinAt.continuousOn
  given: {f f' : 𝕜 -> F} (h : forall x in s, HasDerivWithinAt f (f' x) s x)
  proof: fun x hx => (h x hx).continuousWithinAt

中文:
定理 HasDerivWithinAt.continuousOn
  条件: {f f' : 𝕜 -> F} (h : 对任意 x in s, HasDerivWithinAt f (f' x) s x)
  证明: fun x hx => (h x hx).continuousWithinAt

Depends on / 依赖: continuousWithinAt
-/
theorem HasDerivWithinAt.continuousOn {f f' : 𝕜 -> F} (h : forall x in s, HasDerivWithinAt f (f' x) s x) :
    ContinuousOn f s := fun x hx => (h x hx).continuousWithinAt

/--
theorem `HasDerivAt.continuousOn` / 定理 `HasDerivAt.continuousOn`

English:
theorem HasDerivAt.continuousOn
  given: {f f' : 𝕜 -> F} (hderiv : forall x in s, HasDerivAt f (f' x) x)
  proof: fun x hx => (hderiv x hx).continuousAt.continuousWithinAt

中文:
定理 HasDerivAt.continuousOn
  条件: {f f' : 𝕜 -> F} (hderiv : 对任意 x in s, HasDerivAt f (f' x) x)
  证明: fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
-/
protected theorem HasDerivAt.continuousOn {f f' : 𝕜 -> F} (hderiv : forall x in s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt

end Continuous

section MeanValue

/--
theorem `HasDerivAt.le_of_lip'` / 定理 `HasDerivAt.le_of_lip'`

English:
theorem HasDerivAt.le_of_lip'
  statement: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  proof: by
  simpa using HasFDerivAt.le_of_lip' hf.hasFDerivAt hC₀ hlip

中文:
定理 HasDerivAt.le_of_lip'
  结论: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  证明: by
  simpa using HasFDerivAt.le_of_lip' hf.hasFDerivAt hC₀ hlip

Depends on / 依赖: HasFDerivAt, HasFDerivAt.le_of_lip, hasFDerivAt, hf.hasFDerivAt, le_of_lip
-/
theorem HasDerivAt.le_of_lip' {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) :
    ‖f'‖ <= C := by
  simpa using HasFDerivAt.le_of_lip' hf.hasFDerivAt hC₀ hlip

/--
theorem `HasDerivAt.le_of_lipschitzOn` / 定理 `HasDerivAt.le_of_lipschitzOn`

English:
theorem HasDerivAt.le_of_lipschitzOn
  statement: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  proof: by
  simpa using HasFDerivAt.le_of_lipschitzOn hf.hasFDerivAt hs hlip

中文:
定理 HasDerivAt.le_of_lipschitzOn
  结论: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  证明: by
  simpa using HasFDerivAt.le_of_lipschitzOn hf.hasFDerivAt hs hlip

Depends on / 依赖: HasFDerivAt, HasFDerivAt.le_of_lipschitzOn, hasFDerivAt, hf.hasFDerivAt, le_of_lipschitzOn
-/
theorem HasDerivAt.le_of_lipschitzOn {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {s : Set 𝕜} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖f'‖ <= C := by
  simpa using HasFDerivAt.le_of_lipschitzOn hf.hasFDerivAt hs hlip

/--
theorem `HasDerivAt.le_of_lipschitz` / 定理 `HasDerivAt.le_of_lipschitz`

English:
theorem HasDerivAt.le_of_lipschitz
  statement: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  proof: by
  simpa using HasFDerivAt.le_of_lipschitz hf.hasFDerivAt hlip

中文:
定理 HasDerivAt.le_of_lipschitz
  结论: {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
  证明: by
  simpa using HasFDerivAt.le_of_lipschitz hf.hasFDerivAt hlip

Depends on / 依赖: HasFDerivAt, HasFDerivAt.le_of_lipschitz, hasFDerivAt, hf.hasFDerivAt, le_of_lipschitz
-/
theorem HasDerivAt.le_of_lipschitz {f : 𝕜 -> F} {f' : F} {x₀ : 𝕜} (hf : HasDerivAt f f' x₀)
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C := by
  simpa using HasFDerivAt.le_of_lipschitz hf.hasFDerivAt hlip

/--
theorem `norm_deriv_le_of_lip'` / 定理 `norm_deriv_le_of_lip'`

English:
theorem norm_deriv_le_of_lip'
  statement: {f : 𝕜 -> F} {x₀ : 𝕜}
  proof: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lip' 𝕜 hC₀ hlip

中文:
定理 norm_deriv_le_of_lip'
  结论: {f : 𝕜 -> F} {x₀ : 𝕜}
  证明: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lip' 𝕜 hC₀ hlip

Depends on / 依赖: norm_deriv_eq_norm_fderiv, norm_fderiv_le_of_lip
-/
theorem norm_deriv_le_of_lip' {f : 𝕜 -> F} {x₀ : 𝕜}
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) :
    ‖deriv f x₀‖ <= C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lip' 𝕜 hC₀ hlip

/--
theorem `norm_deriv_le_of_lipschitzOn` / 定理 `norm_deriv_le_of_lipschitzOn`

English:
theorem norm_deriv_le_of_lipschitzOn
  statement: {f : 𝕜 -> F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s in 𝓝 x₀)
  proof: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitzOn 𝕜 hs hlip

中文:
定理 norm_deriv_le_of_lipschitzOn
  结论: {f : 𝕜 -> F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s in 𝓝 x₀)
  证明: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitzOn 𝕜 hs hlip

Depends on / 依赖: norm_deriv_eq_norm_fderiv, norm_fderiv_le_of_lipschitzOn
-/
theorem norm_deriv_le_of_lipschitzOn {f : 𝕜 -> F} {x₀ : 𝕜} {s : Set 𝕜} (hs : s in 𝓝 x₀)
    {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖deriv f x₀‖ <= C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitzOn 𝕜 hs hlip

/--
theorem `norm_deriv_le_of_lipschitz` / 定理 `norm_deriv_le_of_lipschitz`

English:
theorem norm_deriv_le_of_lipschitz
  statement: {f : 𝕜 -> F} {x₀ : 𝕜}
  proof: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip

中文:
定理 norm_deriv_le_of_lipschitz
  结论: {f : 𝕜 -> F} {x₀ : 𝕜}
  证明: by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip

Depends on / 依赖: norm_deriv_eq_norm_fderiv, norm_fderiv_le_of_lipschitz
-/
theorem norm_deriv_le_of_lipschitz {f : 𝕜 -> F} {x₀ : 𝕜}
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖deriv f x₀‖ <= C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip

end MeanValue

section Semilinear

variable {σ σ' : RingHom 𝕜 𝕜} [RingHomIsometric σ] [RingHomInvPair σ σ']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] (L : F ->SL[σ] F')

variable (σ')

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasDerivAt.comp_semilinear` / 引理 `HasDerivAt.comp_semilinear`

English:
lemma HasDerivAt.comp_semilinear
  given: (hf : HasDerivAt f f' x)
  proof: by
  have : RingHomIsometric σ' := .inv σ
  let R : 𝕜 ->SL[σ'] 𝕜 := ⟨σ'.toSemilinearMap, σ'.isometry.continuous⟩
  have hR (k : 𝕜) : R k = σ' k := rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! HasFDerivAt.comp_semilinear L R (f' := toSpanSingleton 𝕜 f') ?_
  · ext
    simp [R]
  · rwa [← hasDeriv

中文:
引理 HasDerivAt.comp_semilinear
  条件: (hf : HasDerivAt f f' x)
  证明: by
  have : RingHomIsometric σ' := .inv σ
  let R : 𝕜 ->SL[σ'] 𝕜 := ⟨σ'.toSemilinearMap, σ'.isometry.continuous⟩
  have hR (k : 𝕜) : R k = σ' k := rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! HasFDerivAt.comp_semilinear L R (f' := toSpanSingleton 𝕜 f') ?_
  · ext
    simp [R]
  · rwa [← hasDeriv

Depends on / 依赖: HasFDerivAt, HasFDerivAt.comp_semilinear, RingHomInvPair, RingHomInvPair.comp_apply_eq, RingHomIsometric, comp_apply_eq, comp_semilinear, continuous, convert, hasDerivAt_iff_hasFDerivAt, isometry, isometry.continuous, toSemilinearMap, toSpanSingleton
-/
lemma HasDerivAt.comp_semilinear (hf : HasDerivAt f f' x) :
    HasDerivAt (L ∘ f ∘ σ') (L f') (σ x) := by
  have : RingHomIsometric σ' := .inv σ
  let R : 𝕜 ->SL[σ'] 𝕜 := ⟨σ'.toSemilinearMap, σ'.isometry.continuous⟩
  have hR (k : 𝕜) : R k = σ' k := rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! HasFDerivAt.comp_semilinear L R (f' := toSpanSingleton 𝕜 f') ?_
  · ext
    simp [R]
  · rwa [← hasDerivAt_iff_hasFDerivAt, hR, RingHomInvPair.comp_apply_eq]

/--
lemma `DifferentiableAt.comp_semilinear₁` / 引理 `DifferentiableAt.comp_semilinear₁`

English:
lemma DifferentiableAt.comp_semilinear₁
  given: (hf : DifferentiableAt 𝕜 f x)
  proof: (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt

中文:
引理 DifferentiableAt.comp_semilinear₁
  条件: (hf : DifferentiableAt 𝕜 f x)
  证明: (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt

Depends on / 依赖: comp_semilinear, differentiableAt, hasDerivAt, hf.hasDerivAt.comp_semilinear
-/
lemma DifferentiableAt.comp_semilinear₁ (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (L ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt

variable (σ) {f : 𝕜 -> 𝕜} {f' : 𝕜}

/--
lemma `HasDerivAt.comp_ringHom` / 引理 `HasDerivAt.comp_ringHom`

English:
lemma HasDerivAt.comp_ringHom
  given: (hf : HasDerivAt f f' x)
  statement: HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x)
  proof: hf.comp_semilinear σ' ⟨σ.toSemilinearMap, σ.isometry.continuous⟩

中文:
引理 HasDerivAt.comp_ringHom
  条件: (hf : HasDerivAt f f' x)
  结论: HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x)
  证明: hf.comp_semilinear σ' ⟨σ.toSemilinearMap, σ.isometry.continuous⟩

Depends on / 依赖: comp_semilinear, continuous, hf.comp_semilinear, isometry, isometry.continuous, toSemilinearMap
-/
lemma HasDerivAt.comp_ringHom (hf : HasDerivAt f f' x) : HasDerivAt (σ ∘ f ∘ σ') (σ f') (σ x) :=
  hf.comp_semilinear σ' ⟨σ.toSemilinearMap, σ.isometry.continuous⟩

/--
lemma `DifferentiableAt.comp_ringHom` / 引理 `DifferentiableAt.comp_ringHom`

English:
lemma DifferentiableAt.comp_ringHom
  given: (hf : DifferentiableAt 𝕜 f x)
  proof: (hf.hasDerivAt.comp_ringHom σ σ').differentiableAt

中文:
引理 DifferentiableAt.comp_ringHom
  条件: (hf : DifferentiableAt 𝕜 f x)
  证明: (hf.hasDerivAt.comp_ringHom σ σ').differentiableAt

Depends on / 依赖: comp_ringHom, differentiableAt, hasDerivAt, hf.hasDerivAt.comp_ringHom
-/
lemma DifferentiableAt.comp_ringHom (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (σ ∘ f ∘ σ') (σ x) :=
  (hf.hasDerivAt.comp_ringHom σ σ').differentiableAt

end Semilinear
