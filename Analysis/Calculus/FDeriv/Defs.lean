/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.TVS

/-!
# The Fréchet derivative: definition

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `HasFDerivWithinAt f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasFDerivAt f f' x := HasFDerivWithinAt f f' x univ`

Finally,

  `HasStrictFDerivAt f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`IsBoundedBilinearMap.hasFDerivAt` twice: first for `HasFDerivAt`, then for
`HasStrictFDerivAt`.

This file `Defs.lean` is intended to just contain the definitions and the bare minimum of
supporting lemmas; a much wider range of elementary properties are proved in the file `Basic.lean`.

Other files in the folder `Analysis/Calculus/FDeriv/` contain the usual formulas
(and existence assertions) for the derivative of
* constants (`Const.lean`)
* the identity
* bounded linear maps (`Linear.lean`)
* bounded bilinear maps (`Bilinear.lean`)
* sum of two functions (`Add.lean`)
* sum of finitely many functions (`Add.lean`)
* multiplication of a function by a scalar constant (`Add.lean`)
* negative of a function (`Add.lean`)
* subtraction of two functions (`Add.lean`)
* multiplication of a function by a scalar function (`Mul.lean`)
* multiplication of two scalar functions (`Mul.lean`)
* composition of functions (the chain rule) (`Comp.lean`)
* inverse function (`Mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../Inverse.lean`)

## Implementation details

The derivative is defined in terms of the `IsLittleOTVS` relation to ensure the definition does not
ingrain a choice of norm, and is then quickly translated to the more convenient `IsLittleO` in the
subsequent theorems. It is also characterized in terms of the `Tendsto` relation.

We also introduce predicates `DifferentiableWithinAt 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `DifferentiableAt 𝕜 f x`,
`DifferentiableOn 𝕜 f s` and `Differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderivWithin 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `UniqueDiffWithinAt s x` and
`UniqueDiffOn s`, defined in `TangentCone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

@[expose] public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

noncomputable section TVS
/-!
## Definitions valid in an arbitrary topological vector space
-/

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x₁ = f x₂ + f' (x₁ - x₂) + o (x₁ - x₂)` when `x = (x₁, x₂)` converges along the filter `L`.
This definition is designed to be specialized

- for `L = 𝓝 (x, x)` (in `HasStrictFDerivAt`),
  giving rise to the derivative in the sense of strict differentiability;
- for `L = 𝓝 x ×ˢ pure x` (in `HasFDerivAt`), giving rise to the usual notion of Fréchet derivative;
- for `L = 𝓝[s] x ×ˢ pure x` (in `HasFDerivWithinAt`),
  giving rise to the notion of Fréchet derivative along the set `s`.
-/
@[mk_iff hasFDerivAtFilter_iff_isLittleOTVS]
/--
Definition of `HasFDerivAtFilter` / `HasFDerivAtFilter` 的定义

English:
structure HasFDerivAtFilter
  parameters: (f : E -> F) (f' : E ->L[𝕜] F) (L : Filter (E × E))
  axioms and operations (1):
    - of_isLittleOTVS : : isLittleOTVS : (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p => p.1 - p.2)

中文:
结构 有FDerivAtFilter
  参数: (f : E -> F) (f' : E ->L[𝕜] F) (L : 滤子 (E × E))
  公理与运算 (1 个):
    - of_isLittleOTVS : : isLittleOTVS : (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p => p.1 - p.2)
-/
structure HasFDerivAtFilter (f : E -> F) (f' : E ->L[𝕜] F) (L : Filter (E × E)) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS : (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p => p.1 - p.2)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
@[fun_prop]
/--
Definition of `HasFDerivWithinAt` / `HasFDerivWithinAt` 的定义

English:
definition HasFDerivWithinAt
  signature: (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (x : E)
  body: HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

中文:
定义 HasFDerivWithinAt
  签名: (f : E -> F) (f' : E ->L[𝕜] F) (s : 集合 E) (x : E)
  定义体: HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

Depends on / 依赖: HasFDerivAtFilter
-/
def HasFDerivWithinAt (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (x : E) :=
  HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
@[fun_prop]
/--
Definition of `HasFDerivAt` / `HasFDerivAt` 的定义

English:
definition HasFDerivAt
  signature: (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
  body: HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x)

中文:
定义 在点处Fréchet可导
  签名: (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
  定义体: HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x)

Depends on / 依赖: HasFDerivAtFilter
-/
def HasFDerivAt (f : E -> F) (f' : E ->L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x)

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
@[fun_prop]
/--
Definition of `HasStrictFDerivAt` / `HasStrictFDerivAt` 的定义

English:
definition HasStrictFDerivAt
  signature: (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
  body: HasFDerivAtFilter f f' (𝓝 (x, x))

中文:
定义 HasStrictFDerivAt
  签名: (f : E -> F) (f' : E ->L[𝕜] F) (x : E)
  定义体: HasFDerivAtFilter f f' (𝓝 (x, x))

Depends on / 依赖: HasFDerivAtFilter
-/
def HasStrictFDerivAt (f : E -> F) (f' : E ->L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (𝓝 (x, x))

variable (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
@[fun_prop]
/--
Definition of `DifferentiableWithinAt` / `DifferentiableWithinAt` 的定义

English:
definition DifferentiableWithinAt
  signature: (f : E -> F) (s : Set E) (x : E)
  body: exists f' : E ->L[𝕜] F, HasFDerivWithinAt f f' s x

中文:
定义 DifferentiableWithinAt
  签名: (f : E -> F) (s : 集合 E) (x : E)
  定义体: exists f' : E ->L[𝕜] F, HasFDerivWithinAt f f' s x

Depends on / 依赖: HasFDerivWithinAt
-/
def DifferentiableWithinAt (f : E -> F) (s : Set E) (x : E) :=
  exists f' : E ->L[𝕜] F, HasFDerivWithinAt f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
@[fun_prop]
/--
Definition of `DifferentiableAt` / `DifferentiableAt` 的定义

English:
definition DifferentiableAt
  signature: (f : E -> F) (x : E)
  body: exists f' : E ->L[𝕜] F, HasFDerivAt f f' x

中文:
定义 DifferentiableAt
  签名: (f : E -> F) (x : E)
  定义体: exists f' : E ->L[𝕜] F, HasFDerivAt f f' x

Depends on / 依赖: HasFDerivAt
-/
def DifferentiableAt (f : E -> F) (x : E) :=
  exists f' : E ->L[𝕜] F, HasFDerivAt f f' x

open scoped Classical in
/-- If `f` has a derivative at `x` within `s`, then `fderivWithin 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. We also set it to be zero, if zero is one of possible derivatives. -/
irreducible_def fderivWithin (f : E -> F) (s : Set E) (x : E) : E ->L[𝕜] F :=
  if HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x
    then 0
  else if h : DifferentiableWithinAt 𝕜 f s x
    then Classical.choose h
  else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
irreducible_def fderiv (f : E -> F) (x : E) : E ->L[𝕜] F :=
  fderivWithin 𝕜 f univ x

/-- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
@[fun_prop]
/--
Definition of `DifferentiableOn` / `DifferentiableOn` 的定义

English:
definition DifferentiableOn
  signature: (f : E -> F) (s : Set E)
  body: forall x in s, DifferentiableWithinAt 𝕜 f s x

中文:
定义 DifferentiableOn
  签名: (f : E -> F) (s : 集合 E)
  定义体: forall x in s, DifferentiableWithinAt 𝕜 f s x

Depends on / 依赖: DifferentiableWithinAt
-/
def DifferentiableOn (f : E -> F) (s : Set E) :=
  forall x in s, DifferentiableWithinAt 𝕜 f s x

/-- `Differentiable 𝕜 f` means that `f` is differentiable at any point. -/
@[fun_prop]
/--
Definition of `Differentiable` / `Differentiable` 的定义

English:
definition Differentiable
  signature: (f : E -> F)
  body: forall x, DifferentiableAt 𝕜 f x

中文:
定义 可微
  签名: (f : E -> F)
  定义体: forall x, DifferentiableAt 𝕜 f x

Depends on / 依赖: DifferentiableAt
-/
def Differentiable (f : E -> F) :=
  forall x, DifferentiableAt 𝕜 f x

variable {𝕜}
variable {f f₀ f₁ g : E -> F}
variable {f' f₀' f₁' g' : E ->L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

/--
theorem `hasFDerivAt_iff_isLittleOTVS` / 定理 `hasFDerivAt_iff_isLittleOTVS`

English:
theorem hasFDerivAt_iff_isLittleOTVS
  proof: by
  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS

中文:
定理 hasFDerivAt_iff_isLittleOTVS
  证明: by
  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS

Depends on / 依赖: Function, Function.comp_def, HasFDerivAt, comp_def, hasFDerivAtFilter_iff_isLittleOTVS
-/
theorem hasFDerivAt_iff_isLittleOTVS :
    HasFDerivAt f f' x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝕜; 𝓝 x] (fun x' => x' - x) := by
  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS

/--
theorem `hasFDerivWithinAt_iff_isLittleOTVS` / 定理 `hasFDerivWithinAt_iff_isLittleOTVS`

English:
theorem hasFDerivWithinAt_iff_isLittleOTVS
  proof: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
  hasFDerivWithinAt_iff_isLittleOTVS

中文:
定理 hasFDerivWithinAt_iff_isLittleOTVS
  证明: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
  hasFDerivWithinAt_iff_isLittleOTVS

Depends on / 依赖: Function, Function.comp_def, HasFDerivWithinAt, comp_def, hasFDerivAtFilter_iff_isLittleOTVS
-/
theorem hasFDerivWithinAt_iff_isLittleOTVS :
    HasFDerivWithinAt f f' s x ↔
      (fun x' => f x' - f x - f' (x' - x)) =o[𝕜; 𝓝[s] x] (fun x' => x' - x) := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
  hasFDerivWithinAt_iff_isLittleOTVS

/--
theorem `hasStrictFDerivAt_iff_isLittleOTVS` / 定理 `hasStrictFDerivAt_iff_isLittleOTVS`

English:
theorem hasStrictFDerivAt_iff_isLittleOTVS
  proof: hasFDerivAtFilter_iff_isLittleOTVS ..

中文:
定理 hasStrictFDerivAt_iff_isLittleOTVS
  证明: hasFDerivAtFilter_iff_isLittleOTVS ..

Depends on / 依赖: hasFDerivAtFilter_iff_isLittleOTVS
-/
theorem hasStrictFDerivAt_iff_isLittleOTVS :
    HasStrictFDerivAt f f' x ↔
      (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; 𝓝 (x, x)] (fun p => p.1 - p.2) :=
  hasFDerivAtFilter_iff_isLittleOTVS ..

/--
theorem `fderivWithin_zero_of_not_differentiableWithinAt` / 定理 `fderivWithin_zero_of_not_differentiableWithinAt`

English:
theorem fderivWithin_zero_of_not_differentiableWithinAt
  given: (h : ¬DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simp [fderivWithin, h]

@[simp]

中文:
定理 fderivWithin_zero_of_not_differentiableWithinAt
  条件: (h : ¬DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simp [fderivWithin, h]

@[simp]

Depends on / 依赖: fderivWithin
-/
theorem fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 f s x = 0 := by
  simp [fderivWithin, h]

@[simp]
/--
theorem `fderivWithin_univ` / 定理 `fderivWithin_univ`

English:
theorem fderivWithin_univ
  statement: fderivWithin 𝕜 f univ = fderiv 𝕜 f
  proof: by
  ext
  rw [fderiv]

中文:
定理 fderivWithin_univ
  结论: fderivWithin 𝕜 f univ = fderiv 𝕜 f
  证明: by
  ext
  rw [fderiv]

Depends on / 依赖: fderiv
-/
theorem fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f := by
  ext
  rw [fderiv]

end TVS

section Normed
/-!
## Reformulations for seminormed spaces
-/

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E -> F} {f' : E ->L[𝕜] F} {s : Set E} {x : E}

/--
theorem `hasFDerivAtFilter_iff_isLittleO` / 定理 `hasFDerivAtFilter_iff_isLittleO`

English:
theorem hasFDerivAtFilter_iff_isLittleO
  given: {L : Filter (E × E)}
  proof: (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
  hasFDerivAtFilter_iff_isLittleO

中文:
定理 hasFDerivAtFilter_iff_isLittleO
  条件: {L : 滤子 (E × E)}
  证明: (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
  hasFDerivAtFilter_iff_isLittleO

Depends on / 依赖: hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_iff_isLittleO
-/
theorem hasFDerivAtFilter_iff_isLittleO {L : Filter (E × E)} :
    HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] fun p => p.1 - p.2 :=
  (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
  hasFDerivAtFilter_iff_isLittleO

/--
theorem `hasFDerivAt_iff_isLittleO` / 定理 `hasFDerivAt_iff_isLittleO`

English:
theorem hasFDerivAt_iff_isLittleO
  proof: hasFDerivAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO

中文:
定理 hasFDerivAt_iff_isLittleO
  证明: hasFDerivAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO

Depends on / 依赖: hasFDerivAt_iff_isLittleOTVS, hasFDerivAt_iff_isLittleOTVS.trans, isLittleOTVS_iff_isLittleO
-/
theorem hasFDerivAt_iff_isLittleO :
    HasFDerivAt f f' x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' => x' - x) :=
  hasFDerivAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO

/--
theorem `hasFDerivWithinAt_iff_isLittleO` / 定理 `hasFDerivWithinAt_iff_isLittleO`

English:
theorem hasFDerivWithinAt_iff_isLittleO
  proof: hasFDerivWithinAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
  hasFDerivWithinAt_iff_isLittleO

中文:
定理 hasFDerivWithinAt_iff_isLittleO
  证明: hasFDerivWithinAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
  hasFDerivWithinAt_iff_isLittleO

Depends on / 依赖: hasFDerivWithinAt_iff_isLittleOTVS, hasFDerivWithinAt_iff_isLittleOTVS.trans, isLittleOTVS_iff_isLittleO
-/
theorem hasFDerivWithinAt_iff_isLittleO :
    HasFDerivWithinAt f f' s x ↔
      (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' => x' - x) :=
  hasFDerivWithinAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
  hasFDerivWithinAt_iff_isLittleO

/--
theorem `hasStrictFDerivAt_iff_isLittleO` / 定理 `hasStrictFDerivAt_iff_isLittleO`

English:
theorem hasStrictFDerivAt_iff_isLittleO
  proof: (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
  hasStrictFDerivAt_iff_isLittleO

中文:
定理 hasStrictFDerivAt_iff_isLittleO
  证明: (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
  hasStrictFDerivAt_iff_isLittleO

Depends on / 依赖: hasStrictFDerivAt_iff_isLittleOTVS, isLittleOTVS_iff_isLittleO
-/
theorem hasStrictFDerivAt_iff_isLittleO :
    HasStrictFDerivAt f f' x ↔
      (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO

alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
  hasStrictFDerivAt_iff_isLittleO

end Normed
