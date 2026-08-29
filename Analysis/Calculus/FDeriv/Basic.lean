/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.DimOne

/-!
# The Fréchet derivative: basic properties

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

## Main results

This file builds on the bare-bones definition given in `Defs.lean` by establishing a variety of
relatively straightforward properties of the derivative.

Deeper properties are defined in other files in the folder `Analysis/Calculus/FDeriv/`, which
contain the usual formulas (and existence assertions) for the derivative of
* constants (`Const.lean`)
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

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `Deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : Differentiable ℝ (fun x ↦ sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : DifferentiableAt ℝ (fun x ↦ exp x / (1 + sin x)) x := by
  simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `Deriv.lean`.

## Implementation details

For a discussion of the definitions and their rationale, see the file docstring of
`Mathlib.Analysis.Calculus.FDeriv.Defs`.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their Cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(fun x ↦ exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section
section DerivativeUniqueness
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

variable {f : E -> F}
variable {f' f₁' : E ->L[𝕜] F}
variable {x : E}
variable {s : Set E}

/-!
### Uniqueness of the derivative

In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `UniqueDiffWithinAt` and `UniqueDiffOn` indeed imply the
uniqueness of the derivative. -/

/--
theorem `HasFDerivWithinAt.lim` / 定理 `HasFDerivWithinAt.lim`

English:
theorem HasFDerivWithinAt.lim
  statement: (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Filter α}
  proof: by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n => c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n => c n • d n := by
.smul_left c simpa [smul_sub] us

中文:
定理 HasFDerivWithinAt.lim
  结论: (h : HasFDerivWithinAt f f' s x) {α : 类型} {l : 滤子 α}
  证明: by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n => c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n => c n • d n := by
.smul_left c simpa [smul_sub] us

Depends on / 依赖: Tendsto, cdlim.isBigOTVS_one, comp_tendsto, h.isLittleOTVS.comp_tendsto, isBigOTVS_one, isLittleOTVS, isLittleOTVS_one, map_continuous, smul_left, smul_sub, tendsto, tendsto_arg, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_nhdsWithin_iff, this.add
-/
theorem HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Filter α}
    {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tendsto d l (𝓝 0)) (dtop : forallᶠ n in l, x + d n in s)
    (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) := by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n => c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n => c n • d n := by
.smul_left c simpa [smul_sub] using h.isLittleOTVS.comp_tendsto tendsto_arg
    _ =O[𝕜; l] (1 : α -> 𝕜) := cdlim.isBigOTVS_one _
  rw [isLittleOTVS_one] at this
simpa using this.add ((map_continuous f').tendsto v).comp cdlim

variable [T2Space F]

/--
theorem `HasFDerivWithinAt.unique_on` / 定理 `HasFDerivWithinAt.unique_on`

English:
theorem HasFDerivWithinAt.unique_on
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

中文:
定理 HasFDerivWithinAt.unique_on
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

Depends on / 依赖: exists_fun_of_mem_tangentConeAt, hf.lim, hg.lim, tendsto_nhds_unique
-/
theorem HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

/--
theorem `UniqueDiffWithinAt.eq` / 定理 `UniqueDiffWithinAt.eq`

English:
theorem UniqueDiffWithinAt.eq
  statement: (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
  proof: ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

中文:
定理 UniqueDiffWithinAt.eq
  结论: (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
  证明: ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_on, ext_on, hf.unique_on, unique_on
-/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

/--
theorem `UniqueDiffOn.eq` / 定理 `UniqueDiffOn.eq`

English:
theorem UniqueDiffOn.eq
  statement: (H : UniqueDiffOn 𝕜 s) (hx : x in s) (h : HasFDerivWithinAt f f' s x)
  proof: (H x hx).eq h h₁

中文:
定理 UniqueDiffOn.eq
  结论: (H : UniqueDiffOn 𝕜 s) (hx : x in s) (h : HasFDerivWithinAt f f' s x)
  证明: (H x hx).eq h h₁
-/
theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x in s) (h : HasFDerivWithinAt f f' s x)
    (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).eq h h₁

/--
theorem `HasFDerivAt.unique` / 定理 `HasFDerivAt.unique`

English:
theorem HasFDerivAt.unique
  given: (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x)
  statement: f' = f₁'
  proof: by
  rw [HasFDerivAt]; rw [← nhdsWithin_univ] at *
  exact uniqueDiffWithinAt_univ.eq h₀ h₁

中文:
定理 在点处Fréchet可导.unique
  条件: (h₀ : 在点处Fréchet可导 f f' x) (h₁ : 在点处Fréchet可导 f f₁' x)
  结论: f' = f₁'
  证明: by
  rw [HasFDerivAt]; rw [← nhdsWithin_univ] at *
  exact uniqueDiffWithinAt_univ.eq h₀ h₁

Depends on / 依赖: HasFDerivAt, nhdsWithin_univ, uniqueDiffWithinAt_univ, uniqueDiffWithinAt_univ.eq
-/
theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
  rw [HasFDerivAt]; rw [← nhdsWithin_univ] at *
  exact uniqueDiffWithinAt_univ.eq h₀ h₁

end DerivativeUniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E -> F}
variable {f' f₀' f₁' g' : E ->L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter (E × E)}

section FDerivProperties

/-! ### Basic properties of the derivative -/

nonrec theorem HasFDerivAtFilter.mono (h : HasFDerivAtFilter f f' L₂) (hst : L₁ <= L₂) :
    HasFDerivAtFilter f f' L₁ :=
.of_isLittleOTVS h.isLittleOTVS.mono hst

/--
theorem `HasFDerivWithinAt.mono_of_mem_nhdsWithin` / 定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`

English:
theorem HasFDerivWithinAt.mono_of_mem_nhdsWithin
  proof: h.mono prod_mono_left _ (nhdsWithin_le_iff.mpr hst)

nonrec theorem HasFDerivWithinAt.mono (h : HasFDerivWithinAt f f' t x) (hst : s subseteq t) :
    HasFDerivWithinAt f f' s x :=
h.mono by gcongr

中文:
定理 HasFDerivWithinAt.mono_of_mem_nhdsWithin
  证明: h.mono prod_mono_left _ (nhdsWithin_le_iff.mpr hst)

nonrec theorem HasFDerivWithinAt.mono (h : HasFDerivWithinAt f f' t x) (hst : s subseteq t) :
    HasFDerivWithinAt f f' s x :=
h.mono by gcongr

Depends on / 依赖: h.mono, nhdsWithin_le_iff, nhdsWithin_le_iff.mpr, prod_mono_left
-/
theorem HasFDerivWithinAt.mono_of_mem_nhdsWithin
    (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) :
    HasFDerivWithinAt f f' s x :=
h.mono prod_mono_left _ (nhdsWithin_le_iff.mpr hst)

nonrec theorem HasFDerivWithinAt.mono (h : HasFDerivWithinAt f f' t x) (hst : s subseteq t) :
    HasFDerivWithinAt f f' s x :=
h.mono by gcongr

/--
theorem `HasFDerivAt.hasFDerivAtFilter` / 定理 `HasFDerivAt.hasFDerivAtFilter`

English:
theorem HasFDerivAt.hasFDerivAtFilter
  given: (h : HasFDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x)
  proof: h.mono hL

@[fun_prop]

中文:
定理 在点处Fréchet可导.hasFDerivAtFilter
  条件: (h : 在点处Fréchet可导 f f' x) (hL : L <= 𝓝 x ×ˢ pure x)
  证明: h.mono hL

@[fun_prop]

Depends on / 依赖: h.mono
-/
theorem HasFDerivAt.hasFDerivAtFilter (h : HasFDerivAt f f' x) (hL : L <= 𝓝 x ×ˢ pure x) :
    HasFDerivAtFilter f f' L :=
  h.mono hL

@[fun_prop]
/--
theorem `HasFDerivAt.hasFDerivWithinAt` / 定理 `HasFDerivAt.hasFDerivWithinAt`

English:
theorem HasFDerivAt.hasFDerivWithinAt
  given: (h : HasFDerivAt f f' x)
  statement: HasFDerivWithinAt f f' s x
  proof: h.hasFDerivAtFilter prod_mono_left _ nhdsWithin_le_nhds

@[fun_prop]

中文:
定理 在点处Fréchet可导.hasFDerivWithinAt
  条件: (h : 在点处Fréchet可导 f f' x)
  结论: HasFDerivWithinAt f f' s x
  证明: h.hasFDerivAtFilter prod_mono_left _ nhdsWithin_le_nhds

@[fun_prop]

Depends on / 依赖: h.hasFDerivAtFilter, hasFDerivAtFilter, nhdsWithin_le_nhds, prod_mono_left
-/
theorem HasFDerivAt.hasFDerivWithinAt (h : HasFDerivAt f f' x) : HasFDerivWithinAt f f' s x :=
h.hasFDerivAtFilter prod_mono_left _ nhdsWithin_le_nhds

@[fun_prop]
/--
theorem `HasFDerivWithinAt.differentiableWithinAt` / 定理 `HasFDerivWithinAt.differentiableWithinAt`

English:
theorem HasFDerivWithinAt.differentiableWithinAt
  given: (h : HasFDerivWithinAt f f' s x)
  proof: ⟨f', h⟩

@[fun_prop]

中文:
定理 HasFDerivWithinAt.differentiableWithinAt
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: ⟨f', h⟩

@[fun_prop]
-/
theorem HasFDerivWithinAt.differentiableWithinAt (h : HasFDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨f', h⟩

@[fun_prop]
/--
theorem `HasFDerivAt.differentiableAt` / 定理 `HasFDerivAt.differentiableAt`

English:
theorem HasFDerivAt.differentiableAt
  given: (h : HasFDerivAt f f' x)
  statement: DifferentiableAt 𝕜 f x
  proof: ⟨f', h⟩

@[simp]

中文:
定理 在点处Fréchet可导.differentiableAt
  条件: (h : 在点处Fréchet可导 f f' x)
  结论: DifferentiableAt 𝕜 f x
  证明: ⟨f', h⟩

@[simp]
-/
theorem HasFDerivAt.differentiableAt (h : HasFDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  ⟨f', h⟩

@[simp]
/--
theorem `hasFDerivWithinAt_univ` / 定理 `hasFDerivWithinAt_univ`

English:
theorem hasFDerivWithinAt_univ
  statement: HasFDerivWithinAt f f' univ x ↔ HasFDerivAt f f' x
  proof: by
  simp only [HasFDerivWithinAt, nhdsWithin_univ, HasFDerivAt]

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ

中文:
定理 hasFDerivWithinAt_univ
  结论: HasFDerivWithinAt f f' univ x ↔ 在点处Fréchet可导 f f' x
  证明: by
  simp only [HasFDerivWithinAt, nhdsWithin_univ, HasFDerivAt]

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ

Depends on / 依赖: HasFDerivAt, HasFDerivWithinAt, nhdsWithin_univ
-/
theorem hasFDerivWithinAt_univ : HasFDerivWithinAt f f' univ x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivWithinAt, nhdsWithin_univ, HasFDerivAt]

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ

/--
theorem `differentiableWithinAt_univ` / 定理 `differentiableWithinAt_univ`

English:
theorem differentiableWithinAt_univ
  proof: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]

中文:
定理 differentiableWithinAt_univ
  证明: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]

Depends on / 依赖: DifferentiableAt, DifferentiableWithinAt, hasFDerivWithinAt_univ
-/
theorem differentiableWithinAt_univ :
    DifferentiableWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]

/--
theorem `fderiv_zero_of_not_differentiableAt` / 定理 `fderiv_zero_of_not_differentiableAt`

English:
theorem fderiv_zero_of_not_differentiableAt
  given: (h : ¬DifferentiableAt 𝕜 f x)
  statement: fderiv 𝕜 f x = 0
  proof: by
  rw [fderiv]; rw [fderivWithin_zero_of_not_differentiableWithinAt]
  rwa [differentiableWithinAt_univ]

中文:
定理 fderiv_zero_of_not_differentiableAt
  条件: (h : ¬DifferentiableAt 𝕜 f x)
  结论: fderiv 𝕜 f x = 0
  证明: by
  rw [fderiv]; rw [fderivWithin_zero_of_not_differentiableWithinAt]
  rwa [differentiableWithinAt_univ]

Depends on / 依赖: differentiableWithinAt_univ, fderiv, fderivWithin_zero_of_not_differentiableWithinAt
-/
theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 := by
  rw [fderiv]; rw [fderivWithin_zero_of_not_differentiableWithinAt]
  rwa [differentiableWithinAt_univ]

/--
theorem `hasFDerivWithinAt_of_mem_nhds` / 定理 `hasFDerivWithinAt_of_mem_nhds`

English:
theorem hasFDerivWithinAt_of_mem_nhds
  given: (h : s in 𝓝 x)
  proof: by
  rw [HasFDerivAt]; rw [HasFDerivWithinAt]; rw [nhdsWithin_eq_nhds.mpr h]

中文:
定理 hasFDerivWithinAt_of_mem_nhds
  条件: (h : s in 𝓝 x)
  证明: by
  rw [HasFDerivAt]; rw [HasFDerivWithinAt]; rw [nhdsWithin_eq_nhds.mpr h]

Depends on / 依赖: HasFDerivAt, HasFDerivWithinAt, nhdsWithin_eq_nhds, nhdsWithin_eq_nhds.mpr
-/
theorem hasFDerivWithinAt_of_mem_nhds (h : s in 𝓝 x) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  rw [HasFDerivAt]; rw [HasFDerivWithinAt]; rw [nhdsWithin_eq_nhds.mpr h]

/--
lemma `hasFDerivWithinAt_of_isOpen` / 引理 `hasFDerivWithinAt_of_isOpen`

English:
lemma hasFDerivWithinAt_of_isOpen
  given: (h : IsOpen s) (hx : x in s)
  proof: hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

@[simp]

中文:
引理 hasFDerivWithinAt_of_isOpen
  条件: (h : 是开集 s) (hx : x in s)
  证明: hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

@[simp]

Depends on / 依赖: h.mem_nhds, hasFDerivWithinAt_of_mem_nhds, mem_nhds
-/
lemma hasFDerivWithinAt_of_isOpen (h : IsOpen s) (hx : x in s) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x :=
  hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

@[simp]
/--
theorem `hasFDerivWithinAt_insert_self` / 定理 `hasFDerivWithinAt_insert_self`

English:
theorem hasFDerivWithinAt_insert_self
  proof: by
  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
  apply isLittleOTVS_insert
  simp only [sub_self, map_zero]

protected alias ⟨_, HasFDerivWithinAt.insert⟩ := hasFDerivWithinAt_insert_self

中文:
定理 hasFDerivWithinAt_insert_self
  证明: by
  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
  apply isLittleOTVS_insert
  simp only [sub_self, map_zero]

protected alias ⟨_, HasFDerivWithinAt.insert⟩ := hasFDerivWithinAt_insert_self

Depends on / 依赖: hasFDerivWithinAt_iff_isLittleOTVS, isLittleOTVS_insert, map_zero, simp_rw, sub_self
-/
theorem hasFDerivWithinAt_insert_self :
    HasFDerivWithinAt f f' (insert x s) x ↔ HasFDerivWithinAt f f' s x := by
  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
  apply isLittleOTVS_insert
  simp only [sub_self, map_zero]

protected alias ⟨_, HasFDerivWithinAt.insert⟩ := hasFDerivWithinAt_insert_self

/--
theorem `HasFDerivWithinAt.of_insert` / 定理 `HasFDerivWithinAt.of_insert`

English:
theorem HasFDerivWithinAt.of_insert
  given: {y : E} (h : HasFDerivWithinAt f f' (insert y s) x)
  proof: h.mono subset_insert y s

@[simp]

中文:
定理 HasFDerivWithinAt.of_insert
  条件: {y : E} (h : HasFDerivWithinAt f f' (insert y s) x)
  证明: h.mono subset_insert y s

@[simp]

Depends on / 依赖: h.mono, subset_insert
-/
theorem HasFDerivWithinAt.of_insert {y : E} (h : HasFDerivWithinAt f f' (insert y s) x) :
    HasFDerivWithinAt f f' s x :=
h.mono subset_insert y s

@[simp]
/--
theorem `hasFDerivWithinAt_insert` / 定理 `hasFDerivWithinAt_insert`

English:
theorem hasFDerivWithinAt_insert
  given: [T1Space E] {y : E}
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · apply hasFDerivWithinAt_insert_self
  · refine ⟨.of_insert, fun hf => hf.mono_of_mem_nhdsWithin ?_⟩
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨_, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert

@[simp]

中文:
定理 hasFDerivWithinAt_insert
  条件: [T1空间 E] {y : E}
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · apply hasFDerivWithinAt_insert_self
  · refine ⟨.of_insert, fun hf => hf.mono_of_mem_nhdsWithin ?_⟩
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨_, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert

@[simp]

Depends on / 依赖: eq_or_ne, hasFDerivWithinAt_insert_self, hf.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_insert_of_ne, of_insert, self_mem_nhdsWithin, simp_rw
-/
theorem hasFDerivWithinAt_insert [T1Space E] {y : E} :
    HasFDerivWithinAt f f' (insert y s) x ↔ HasFDerivWithinAt f f' s x := by
  rcases eq_or_ne x y with (rfl | h)
  · apply hasFDerivWithinAt_insert_self
  · refine ⟨.of_insert, fun hf => hf.mono_of_mem_nhdsWithin ?_⟩
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨_, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert

@[simp]
/--
theorem `hasFDerivWithinAt_sdiff_singleton_self` / 定理 `hasFDerivWithinAt_sdiff_singleton_self`

English:
theorem hasFDerivWithinAt_sdiff_singleton_self
  proof: by
  rw [← hasFDerivWithinAt_insert_self]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert_self]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton_self := hasFDerivWithinAt_sdiff_singleton_self

@[simp]

中文:
定理 hasFDerivWithinAt_sdiff_singleton_self
  证明: by
  rw [← hasFDerivWithinAt_insert_self]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert_self]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton_self := hasFDerivWithinAt_sdiff_singleton_self

@[simp]

Depends on / 依赖: hasFDerivWithinAt_insert_self, insert_sdiff_singleton
-/
theorem hasFDerivWithinAt_sdiff_singleton_self :
    HasFDerivWithinAt f f' (s \ {x}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert_self]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert_self]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton_self := hasFDerivWithinAt_sdiff_singleton_self

@[simp]
/--
theorem `hasFDerivWithinAt_sdiff_singleton` / 定理 `hasFDerivWithinAt_sdiff_singleton`

English:
theorem hasFDerivWithinAt_sdiff_singleton
  given: [T1Space E] (y : E)
  proof: by
  rw [← hasFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton := hasFDerivWithinAt_sdiff_singleton

@[simp]

中文:
定理 hasFDerivWithinAt_sdiff_singleton
  条件: [T1空间 E] (y : E)
  证明: by
  rw [← hasFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton := hasFDerivWithinAt_sdiff_singleton

@[simp]

Depends on / 依赖: hasFDerivWithinAt_insert, insert_sdiff_singleton
-/
theorem hasFDerivWithinAt_sdiff_singleton [T1Space E] (y : E) :
    HasFDerivWithinAt f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton := hasFDerivWithinAt_sdiff_singleton

@[simp]
/--
theorem `HasFDerivWithinAt.empty` / 定理 `HasFDerivWithinAt.empty`

English:
theorem HasFDerivWithinAt.empty
  statement: HasFDerivWithinAt f f' ∅ x
  proof: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

@[simp]

中文:
定理 HasFDerivWithinAt.empty
  结论: HasFDerivWithinAt f f' ∅ x
  证明: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

@[simp]
-/
protected theorem HasFDerivWithinAt.empty : HasFDerivWithinAt f f' ∅ x := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

@[simp]
/--
theorem `DifferentiableWithinAt.empty` / 定理 `DifferentiableWithinAt.empty`

English:
theorem DifferentiableWithinAt.empty
  statement: DifferentiableWithinAt 𝕜 f ∅ x
  proof: ⟨0, .empty⟩

@[fun_prop]

中文:
定理 DifferentiableWithinAt.empty
  结论: DifferentiableWithinAt 𝕜 f ∅ x
  证明: ⟨0, .empty⟩

@[fun_prop]
-/
protected theorem DifferentiableWithinAt.empty : DifferentiableWithinAt 𝕜 f ∅ x :=
  ⟨0, .empty⟩

@[fun_prop]
/--
theorem `differentiableOn_empty` / 定理 `differentiableOn_empty`

English:
theorem differentiableOn_empty
  statement: DifferentiableOn 𝕜 f ∅
  proof: fun _ => False.elim

中文:
定理 differentiableOn_empty
  结论: DifferentiableOn 𝕜 f ∅
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem differentiableOn_empty : DifferentiableOn 𝕜 f ∅ := fun _ => False.elim

/--
theorem `HasFDerivWithinAt.of_finite` / 定理 `HasFDerivWithinAt.of_finite`

English:
theorem HasFDerivWithinAt.of_finite
  given: [T1Space E] (h : s.Finite)
  statement: HasFDerivWithinAt f f' s x
  proof: by
  induction s, h using Set.Finite.induction_on with
  | empty => exact .empty
  | insert _ _ ih => exact ih.insert'

中文:
定理 HasFDerivWithinAt.of_finite
  条件: [T1空间 E] (h : s.有限)
  结论: HasFDerivWithinAt f f' s x
  证明: by
  induction s, h using Set.Finite.induction_on with
  | empty => exact .empty
  | insert _ _ ih => exact ih.insert'

Depends on / 依赖: Finite, Set.Finite.induction_on, ih.insert, induction_on, insert
-/
theorem HasFDerivWithinAt.of_finite [T1Space E] (h : s.Finite) : HasFDerivWithinAt f f' s x := by
  induction s, h using Set.Finite.induction_on with
  | empty => exact .empty
  | insert _ _ ih => exact ih.insert'

/--
theorem `DifferentiableWithinAt.of_finite` / 定理 `DifferentiableWithinAt.of_finite`

English:
theorem DifferentiableWithinAt.of_finite
  given: [T1Space E] (h : s.Finite)
  proof: ⟨0, .of_finite h⟩

@[simp]

中文:
定理 DifferentiableWithinAt.of_finite
  条件: [T1空间 E] (h : s.有限)
  证明: ⟨0, .of_finite h⟩

@[simp]

Depends on / 依赖: of_finite
-/
theorem DifferentiableWithinAt.of_finite [T1Space E] (h : s.Finite) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨0, .of_finite h⟩

@[simp]
/--
theorem `HasFDerivWithinAt.singleton` / 定理 `HasFDerivWithinAt.singleton`

English:
theorem HasFDerivWithinAt.singleton
  given: [T1Space E] {y}
  statement: HasFDerivWithinAt f f' {x} y
  proof: .of_finite finite_singleton _

@[simp]

中文:
定理 HasFDerivWithinAt.singleton
  条件: [T1空间 E] {y}
  结论: HasFDerivWithinAt f f' {x} y
  证明: .of_finite finite_singleton _

@[simp]
-/
protected theorem HasFDerivWithinAt.singleton [T1Space E] {y} : HasFDerivWithinAt f f' {x} y :=
.of_finite finite_singleton _

@[simp]
/--
theorem `DifferentiableWithinAt.singleton` / 定理 `DifferentiableWithinAt.singleton`

English:
theorem DifferentiableWithinAt.singleton
  given: [T1Space E] {y}
  proof: ⟨0, .singleton⟩

中文:
定理 DifferentiableWithinAt.singleton
  条件: [T1空间 E] {y}
  证明: ⟨0, .singleton⟩
-/
protected theorem DifferentiableWithinAt.singleton [T1Space E] {y} :
    DifferentiableWithinAt 𝕜 f {x} y :=
  ⟨0, .singleton⟩

/--
theorem `HasFDerivWithinAt.of_subsingleton` / 定理 `HasFDerivWithinAt.of_subsingleton`

English:
theorem HasFDerivWithinAt.of_subsingleton
  given: [T1Space E] (h : s.Subsingleton)
  proof: .of_finite h.finite

中文:
定理 HasFDerivWithinAt.of_subsingleton
  条件: [T1空间 E] (h : s.子单例)
  证明: .of_finite h.finite

Depends on / 依赖: finite, h.finite, of_finite
-/
theorem HasFDerivWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    HasFDerivWithinAt f f' s x :=
  .of_finite h.finite

/--
theorem `DifferentiableWithinAt.of_subsingleton` / 定理 `DifferentiableWithinAt.of_subsingleton`

English:
theorem DifferentiableWithinAt.of_subsingleton
  given: [T1Space E] (h : s.Subsingleton)
  proof: .of_finite h.finite

@[fun_prop]

中文:
定理 DifferentiableWithinAt.of_subsingleton
  条件: [T1空间 E] (h : s.子单例)
  证明: .of_finite h.finite

@[fun_prop]

Depends on / 依赖: finite, h.finite, of_finite
-/
theorem DifferentiableWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    DifferentiableWithinAt 𝕜 f s x :=
  .of_finite h.finite

@[fun_prop]
/--
theorem `HasStrictFDerivAt.hasFDerivAt` / 定理 `HasStrictFDerivAt.hasFDerivAt`

English:
theorem HasStrictFDerivAt.hasFDerivAt
  given: (hf : HasStrictFDerivAt f f' x)
  proof: .of_isLittleOTVS by
    simpa only using! hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)

中文:
定理 HasStrictFDerivAt.hasFDerivAt
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: .of_isLittleOTVS by
    simpa only using! hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)
-/
protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
    HasFDerivAt f f' x :=
.of_isLittleOTVS by
    simpa only using! hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)

/--
theorem `HasStrictFDerivAt.differentiableAt` / 定理 `HasStrictFDerivAt.differentiableAt`

English:
theorem HasStrictFDerivAt.differentiableAt
  given: (hf : HasStrictFDerivAt f f' x)
  proof: hf.hasFDerivAt.differentiableAt

中文:
定理 HasStrictFDerivAt.differentiableAt
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: hf.hasFDerivAt.differentiableAt
-/
protected theorem HasStrictFDerivAt.differentiableAt (hf : HasStrictFDerivAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  hf.hasFDerivAt.differentiableAt

/--
theorem `HasFDerivAt.lim` / 定理 `HasFDerivAt.lim`

English:
theorem HasFDerivAt.lim
  proof: by
  refine (hasFDerivWithinAt_univ.2 hf).lim ?_ (.of_forall fun _ => mem_univ _) ?_
  · rw [tendsto_norm_atTop_iff_cobounded] at hc
    simpa using (tendsto_inv₀_cobounded.comp hc).smul (tendsto_const_nhds (x := v))
  · refine tendsto_nhds_of_eventually_eq ?_
    refine (eventually_ne_of_tendsto_no

中文:
定理 在点处Fréchet可导.lim
  证明: by
  refine (hasFDerivWithinAt_univ.2 hf).lim ?_ (.of_forall fun _ => mem_univ _) ?_
  · rw [tendsto_norm_atTop_iff_cobounded] at hc
    simpa using (tendsto_inv₀_cobounded.comp hc).smul (tendsto_const_nhds (x := v))
  · refine tendsto_nhds_of_eventually_eq ?_
    refine (eventually_ne_of_tendsto_no

Depends on / 依赖: _cobounded.comp, eventually_ne_of_tendsto_norm_atTop, hasFDerivWithinAt_univ, mem_univ, of_forall, tendsto_const_nhds, tendsto_nhds_of_eventually_eq, tendsto_norm_atTop_iff_cobounded
-/
theorem HasFDerivAt.lim
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (hf : HasFDerivAt f f' x) (v : E) {α : Type*} {c : α -> 𝕜} {l : Filter α}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    Tendsto (fun n => c n • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) := by
  refine (hasFDerivWithinAt_univ.2 hf).lim ?_ (.of_forall fun _ => mem_univ _) ?_
  · rw [tendsto_norm_atTop_iff_cobounded] at hc
    simpa using (tendsto_inv₀_cobounded.comp hc).smul (tendsto_const_nhds (x := v))
  · refine tendsto_nhds_of_eventually_eq ?_
    refine (eventually_ne_of_tendsto_norm_atTop hc (0 : 𝕜)).mono fun y hy => ?_
    simp [hy]

/--
theorem `hasFDerivWithinAt_inter'` / 定理 `hasFDerivWithinAt_inter'`

English:
theorem hasFDerivWithinAt_inter'
  given: (h : t in 𝓝[s] x)
  proof: by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]

中文:
定理 hasFDerivWithinAt_inter'
  条件: (h : t in 𝓝[s] x)
  证明: by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]

Depends on / 依赖: HasFDerivWithinAt, nhdsWithin_restrict
-/
theorem hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) :
    HasFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]

/--
theorem `hasFDerivWithinAt_inter` / 定理 `hasFDerivWithinAt_inter`

English:
theorem hasFDerivWithinAt_inter
  given: (h : t in 𝓝 x)
  proof: by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]

中文:
定理 hasFDerivWithinAt_inter
  条件: (h : t in 𝓝 x)
  证明: by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]

Depends on / 依赖: HasFDerivWithinAt, nhdsWithin_restrict
-/
theorem hasFDerivWithinAt_inter (h : t in 𝓝 x) :
    HasFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]

/--
theorem `HasFDerivWithinAt.union` / 定理 `HasFDerivWithinAt.union`

English:
theorem HasFDerivWithinAt.union
  statement: (hs : HasFDerivWithinAt f f' s x)
  proof: by
  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
  exact hs.sup ht

中文:
定理 HasFDerivWithinAt.union
  结论: (hs : HasFDerivWithinAt f f' s x)
  证明: by
  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
  exact hs.sup ht

Depends on / 依赖: hasFDerivWithinAt_iff_isLittleOTVS, hs.sup, nhdsWithin_union
-/
theorem HasFDerivWithinAt.union (hs : HasFDerivWithinAt f f' s x)
    (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s union t) x := by
  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
  exact hs.sup ht

/--
theorem `HasFDerivWithinAt.hasFDerivAt` / 定理 `HasFDerivWithinAt.hasFDerivAt`

English:
theorem HasFDerivWithinAt.hasFDerivAt
  given: (h : HasFDerivWithinAt f f' s x) (hs : s in 𝓝 x)
  proof: by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h

中文:
定理 HasFDerivWithinAt.hasFDerivAt
  条件: (h : HasFDerivWithinAt f f' s x) (hs : s in 𝓝 x)
  证明: by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h

Depends on / 依赖: hasFDerivWithinAt_inter, hasFDerivWithinAt_univ, univ_inter
-/
theorem HasFDerivWithinAt.hasFDerivAt (h : HasFDerivWithinAt f f' s x) (hs : s in 𝓝 x) :
    HasFDerivAt f f' x := by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h

/--
theorem `DifferentiableWithinAt.differentiableAt` / 定理 `DifferentiableWithinAt.differentiableAt`

English:
theorem DifferentiableWithinAt.differentiableAt
  statement: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.imp fun _ hf' => hf'.hasFDerivAt hs

中文:
定理 DifferentiableWithinAt.differentiableAt
  结论: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.imp fun _ hf' => hf'.hasFDerivAt hs

Depends on / 依赖: h.imp, hasFDerivAt
-/
theorem DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.imp fun _ hf' => hf'.hasFDerivAt hs

/--
theorem `HasFDerivWithinAt.of_not_accPt` / 定理 `HasFDerivWithinAt.of_not_accPt`

English:
theorem HasFDerivWithinAt.of_not_accPt
  given: (h : ¬AccPt x (𝓟 s))
  proof: by
  rw [accPt_principal_iff_nhdsWithin]; rw [not_neBot] at h
  rw [← hasFDerivWithinAt_sdiff_singleton_self]; rw [hasFDerivWithinAt_iff_isLittleOTVS]; rw [h]
  exact .bot

中文:
定理 HasFDerivWithinAt.of_not_accPt
  条件: (h : ¬聚点 x (𝓟 s))
  证明: by
  rw [accPt_principal_iff_nhdsWithin]; rw [not_neBot] at h
  rw [← hasFDerivWithinAt_sdiff_singleton_self]; rw [hasFDerivWithinAt_iff_isLittleOTVS]; rw [h]
  exact .bot

Depends on / 依赖: accPt_principal_iff_nhdsWithin, hasFDerivWithinAt_iff_isLittleOTVS, hasFDerivWithinAt_sdiff_singleton_self, not_neBot
-/
theorem HasFDerivWithinAt.of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    HasFDerivWithinAt f f' s x := by
  rw [accPt_principal_iff_nhdsWithin]; rw [not_neBot] at h
  rw [← hasFDerivWithinAt_sdiff_singleton_self]; rw [hasFDerivWithinAt_iff_isLittleOTVS]; rw [h]
  exact .bot

/--
theorem `HasFDerivWithinAt.of_notMem_closure` / 定理 `HasFDerivWithinAt.of_notMem_closure`

English:
theorem HasFDerivWithinAt.of_notMem_closure
  given: (h : x ∉ closure s)
  statement: HasFDerivWithinAt f f' s x
  proof: .of_not_accPt (h ·.clusterPt.mem_closure)

中文:
定理 HasFDerivWithinAt.of_notMem_closure
  条件: (h : x ∉ closure s)
  结论: HasFDerivWithinAt f f' s x
  证明: .of_not_accPt (h ·.clusterPt.mem_closure)

Depends on / 依赖: clusterPt, clusterPt.mem_closure, mem_closure, of_not_accPt
-/
theorem HasFDerivWithinAt.of_notMem_closure (h : x ∉ closure s) : HasFDerivWithinAt f f' s x :=
  .of_not_accPt (h ·.clusterPt.mem_closure)

/--
theorem `fderivWithin_zero_of_not_accPt` / 定理 `fderivWithin_zero_of_not_accPt`

English:
theorem fderivWithin_zero_of_not_accPt
  given: (h : ¬AccPt x (𝓟 s))
  proof: by
  rw [fderivWithin]; rw [if_pos (.of_not_accPt h)]

中文:
定理 fderivWithin_zero_of_not_accPt
  条件: (h : ¬聚点 x (𝓟 s))
  证明: by
  rw [fderivWithin]; rw [if_pos (.of_not_accPt h)]

Depends on / 依赖: fderivWithin, if_pos, of_not_accPt
-/
theorem fderivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    fderivWithin 𝕜 f s x = 0 := by
  rw [fderivWithin]; rw [if_pos (.of_not_accPt h)]

/--
theorem `fderivWithin_zero_of_notMem_closure` / 定理 `fderivWithin_zero_of_notMem_closure`

English:
theorem fderivWithin_zero_of_notMem_closure
  given: (h : x ∉ closure s)
  proof: fderivWithin_zero_of_not_accPt (h ·.clusterPt.mem_closure)

中文:
定理 fderivWithin_zero_of_notMem_closure
  条件: (h : x ∉ closure s)
  证明: fderivWithin_zero_of_not_accPt (h ·.clusterPt.mem_closure)

Depends on / 依赖: clusterPt, clusterPt.mem_closure, fderivWithin_zero_of_not_accPt, mem_closure
-/
theorem fderivWithin_zero_of_notMem_closure (h : x ∉ closure s) :
    fderivWithin 𝕜 f s x = 0 :=
  fderivWithin_zero_of_not_accPt (h ·.clusterPt.mem_closure)

/--
theorem `fderivWithin_zero_of_not_uniqueDiffWithinAt` / 定理 `fderivWithin_zero_of_not_uniqueDiffWithinAt`

English:
theorem fderivWithin_zero_of_not_uniqueDiffWithinAt
  statement: {f : 𝕜 -> F} {x : 𝕜} {s : Set 𝕜}
  proof: fderivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

中文:
定理 fderivWithin_zero_of_not_uniqueDiffWithinAt
  结论: {f : 𝕜 -> F} {x : 𝕜} {s : 集合 𝕜}
  证明: fderivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

Depends on / 依赖: AccPt.uniqueDiffWithinAt, fderivWithin_zero_of_not_accPt, uniqueDiffWithinAt
-/
theorem fderivWithin_zero_of_not_uniqueDiffWithinAt {f : 𝕜 -> F} {x : 𝕜} {s : Set 𝕜}
    (h : ¬UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = 0 :=
fderivWithin_zero_of_not_accPt mt AccPt.uniqueDiffWithinAt h

/--
theorem `DifferentiableWithinAt.hasFDerivWithinAt` / 定理 `DifferentiableWithinAt.hasFDerivWithinAt`

English:
theorem DifferentiableWithinAt.hasFDerivWithinAt
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simp only [fderivWithin, dif_pos h]
  split_ifs with h₀
  exacts [h₀, Classical.choose_spec h]

中文:
定理 DifferentiableWithinAt.hasFDerivWithinAt
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simp only [fderivWithin, dif_pos h]
  split_ifs with h₀
  exacts [h₀, Classical.choose_spec h]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, exacts, fderivWithin, split_ifs
-/
theorem DifferentiableWithinAt.hasFDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasFDerivWithinAt f (fderivWithin 𝕜 f s x) s x := by
  simp only [fderivWithin, dif_pos h]
  split_ifs with h₀
  exacts [h₀, Classical.choose_spec h]

/--
theorem `DifferentiableAt.hasFDerivAt` / 定理 `DifferentiableAt.hasFDerivAt`

English:
theorem DifferentiableAt.hasFDerivAt
  given: (h : DifferentiableAt 𝕜 f x)
  proof: by
  rw [fderiv]; rw [← hasFDerivWithinAt_univ]
  rw [← differentiableWithinAt_univ] at h
  exact h.hasFDerivWithinAt

中文:
定理 DifferentiableAt.hasFDerivAt
  条件: (h : DifferentiableAt 𝕜 f x)
  证明: by
  rw [fderiv]; rw [← hasFDerivWithinAt_univ]
  rw [← differentiableWithinAt_univ] at h
  exact h.hasFDerivWithinAt

Depends on / 依赖: differentiableWithinAt_univ, fderiv, h.hasFDerivWithinAt, hasFDerivWithinAt, hasFDerivWithinAt_univ
-/
theorem DifferentiableAt.hasFDerivAt (h : DifferentiableAt 𝕜 f x) :
    HasFDerivAt f (fderiv 𝕜 f x) x := by
  rw [fderiv]; rw [← hasFDerivWithinAt_univ]
  rw [← differentiableWithinAt_univ] at h
  exact h.hasFDerivWithinAt

/--
theorem `DifferentiableOn.hasFDerivAt` / 定理 `DifferentiableOn.hasFDerivAt`

English:
theorem DifferentiableOn.hasFDerivAt
  given: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  proof: ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt

中文:
定理 DifferentiableOn.hasFDerivAt
  条件: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  证明: ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt

Depends on / 依赖: differentiableAt, hasFDerivAt, mem_of_mem_nhds
-/
theorem DifferentiableOn.hasFDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
    HasFDerivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt

/--
theorem `DifferentiableOn.differentiableAt` / 定理 `DifferentiableOn.differentiableAt`

English:
theorem DifferentiableOn.differentiableAt
  given: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  proof: (h.hasFDerivAt hs).differentiableAt

中文:
定理 DifferentiableOn.differentiableAt
  条件: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  证明: (h.hasFDerivAt hs).differentiableAt

Depends on / 依赖: differentiableAt, h.hasFDerivAt, hasFDerivAt
-/
theorem DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hs).differentiableAt

/--
theorem `DifferentiableOn.eventually_differentiableAt` / 定理 `DifferentiableOn.eventually_differentiableAt`

English:
theorem DifferentiableOn.eventually_differentiableAt
  given: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  proof: (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

中文:
定理 DifferentiableOn.eventually_differentiableAt
  条件: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  证明: (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

Depends on / 依赖: differentiableAt, eventually_eventually_nhds, h.differentiableAt
-/
theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
    forallᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

/--
theorem `HasFDerivAt.fderiv` / 定理 `HasFDerivAt.fderiv`

English:
theorem HasFDerivAt.fderiv
  proof: by
  rw [h.unique h.differentiableAt.hasFDerivAt]

中文:
定理 在点处Fréchet可导.fderiv
  证明: by
  rw [h.unique h.differentiableAt.hasFDerivAt]
-/
protected theorem HasFDerivAt.fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivAt f f' x) :
    fderiv 𝕜 f x = f' := by
  rw [h.unique h.differentiableAt.hasFDerivAt]

/--
theorem `fderiv_eq` / 定理 `fderiv_eq`

English:
theorem fderiv_eq
  proof: funext fun x => (h x).fderiv

中文:
定理 fderiv_eq
  证明: funext fun x => (h x).fderiv

Depends on / 依赖: fderiv
-/
theorem fderiv_eq
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {f' : E -> E ->L[𝕜] F} (h : forall x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv

/--
theorem `HasFDerivWithinAt.fderivWithin` / 定理 `HasFDerivWithinAt.fderivWithin`

English:
theorem HasFDerivWithinAt.fderivWithin
  proof: (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm

中文:
定理 HasFDerivWithinAt.fderivWithin
  证明: (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm
-/
protected theorem HasFDerivWithinAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = f' :=
  (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm

/--
theorem `DifferentiableWithinAt.mono` / 定理 `DifferentiableWithinAt.mono`

English:
theorem DifferentiableWithinAt.mono
  given: (h : DifferentiableWithinAt 𝕜 f t x) (st : s subseteq t)
  proof: by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩

中文:
定理 DifferentiableWithinAt.mono
  条件: (h : DifferentiableWithinAt 𝕜 f t x) (st : s subseteq t)
  证明: by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩
-/
theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s subseteq t) :
    DifferentiableWithinAt 𝕜 f s x := by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩

/--
theorem `DifferentiableWithinAt.mono_of_mem_nhdsWithin` / 定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`

English:
theorem DifferentiableWithinAt.mono_of_mem_nhdsWithin
  proof: (h.hasFDerivWithinAt.mono_of_mem_nhdsWithin hst).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.mono_of_mem_nhdsWithin
  证明: (h.hasFDerivWithinAt.mono_of_mem_nhdsWithin hst).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.mono_of_mem_nhdsWithin, hasFDerivWithinAt, mono_of_mem_nhdsWithin
-/
theorem DifferentiableWithinAt.mono_of_mem_nhdsWithin
    (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s in 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f t x :=
  (h.hasFDerivWithinAt.mono_of_mem_nhdsWithin hst).differentiableWithinAt

/--
theorem `DifferentiableWithinAt.congr_nhds` / 定理 `DifferentiableWithinAt.congr_nhds`

English:
theorem DifferentiableWithinAt.congr_nhds
  statement: (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
  proof: h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

中文:
定理 DifferentiableWithinAt.congr_nhds
  结论: (h : DifferentiableWithinAt 𝕜 f s x) {t : 集合 E}
  证明: h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

Depends on / 依赖: h.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem DifferentiableWithinAt.congr_nhds (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
    (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x :=
h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

/--
theorem `differentiableWithinAt_congr_nhds` / 定理 `differentiableWithinAt_congr_nhds`

English:
theorem differentiableWithinAt_congr_nhds
  given: {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x)
  proof: ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

中文:
定理 differentiableWithinAt_congr_nhds
  条件: {t : 集合 E} (hst : 𝓝[s] x = 𝓝[t] x)
  证明: ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

Depends on / 依赖: congr_nhds, h.congr_nhds, hst.symm
-/
theorem differentiableWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

/--
theorem `differentiableWithinAt_inter` / 定理 `differentiableWithinAt_inter`

English:
theorem differentiableWithinAt_inter
  given: (ht : t in 𝓝 x)
  proof: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]

中文:
定理 differentiableWithinAt_inter
  条件: (ht : t in 𝓝 x)
  证明: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_inter
-/
theorem differentiableWithinAt_inter (ht : t in 𝓝 x) :
    DifferentiableWithinAt 𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]

/--
theorem `differentiableWithinAt_inter'` / 定理 `differentiableWithinAt_inter'`

English:
theorem differentiableWithinAt_inter'
  given: (ht : t in 𝓝[s] x)
  proof: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]

中文:
定理 differentiableWithinAt_inter'
  条件: (ht : t in 𝓝[s] x)
  证明: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_inter
-/
theorem differentiableWithinAt_inter' (ht : t in 𝓝[s] x) :
    DifferentiableWithinAt 𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]

/--
theorem `differentiableWithinAt_insert_self` / 定理 `differentiableWithinAt_insert_self`

English:
theorem differentiableWithinAt_insert_self
  proof: ⟨fun h => h.mono (subset_insert x s), fun h => h.hasFDerivWithinAt.insert.differentiableWithinAt⟩

protected alias ⟨_, DifferentiableWithinAt.insert⟩ := differentiableWithinAt_insert_self

中文:
定理 differentiableWithinAt_insert_self
  证明: ⟨fun h => h.mono (subset_insert x s), fun h => h.hasFDerivWithinAt.insert.differentiableWithinAt⟩

protected alias ⟨_, DifferentiableWithinAt.insert⟩ := differentiableWithinAt_insert_self

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.insert.differentiableWithinAt, h.mono, hasFDerivWithinAt, insert, subset_insert
-/
theorem differentiableWithinAt_insert_self :
    DifferentiableWithinAt 𝕜 f (insert x s) x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.mono (subset_insert x s), fun h => h.hasFDerivWithinAt.insert.differentiableWithinAt⟩

protected alias ⟨_, DifferentiableWithinAt.insert⟩ := differentiableWithinAt_insert_self

/--
theorem `DifferentiableWithinAt.of_insert` / 定理 `DifferentiableWithinAt.of_insert`

English:
theorem DifferentiableWithinAt.of_insert
  given: {y : E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x)
  proof: h.mono subset_insert _ _

中文:
定理 DifferentiableWithinAt.of_insert
  条件: {y : E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x)
  证明: h.mono subset_insert _ _

Depends on / 依赖: h.mono, subset_insert
-/
theorem DifferentiableWithinAt.of_insert {y : E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x) :
    DifferentiableWithinAt 𝕜 f s x :=
h.mono subset_insert _ _

/--
theorem `differentiableWithinAt_insert` / 定理 `differentiableWithinAt_insert`

English:
theorem differentiableWithinAt_insert
  given: [T1Space E] {y : E}
  proof: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_insert]

alias ⟨_, DifferentiableWithinAt.insert'⟩ := differentiableWithinAt_insert

中文:
定理 differentiableWithinAt_insert
  条件: [T1空间 E] {y : E}
  证明: by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_insert]

alias ⟨_, DifferentiableWithinAt.insert'⟩ := differentiableWithinAt_insert

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_insert
-/
theorem differentiableWithinAt_insert [T1Space E] {y : E} :
    DifferentiableWithinAt 𝕜 f (insert y s) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_insert]

alias ⟨_, DifferentiableWithinAt.insert'⟩ := differentiableWithinAt_insert

/--
theorem `DifferentiableAt.differentiableWithinAt` / 定理 `DifferentiableAt.differentiableWithinAt`

English:
theorem DifferentiableAt.differentiableWithinAt
  given: (h : DifferentiableAt 𝕜 f x)
  proof: (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[fun_prop]

中文:
定理 DifferentiableAt.differentiableWithinAt
  条件: (h : DifferentiableAt 𝕜 f x)
  证明: (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_univ, subset_univ
-/
theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[fun_prop]
/--
theorem `Differentiable.differentiableAt` / 定理 `Differentiable.differentiableAt`

English:
theorem Differentiable.differentiableAt
  given: (h : Differentiable 𝕜 f)
  statement: DifferentiableAt 𝕜 f x
  proof: h x

中文:
定理 可微.differentiableAt
  条件: (h : 可微 𝕜 f)
  结论: DifferentiableAt 𝕜 f x
  证明: h x
-/
theorem Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x

/--
theorem `DifferentiableAt.fderivWithin` / 定理 `DifferentiableAt.fderivWithin`

English:
theorem DifferentiableAt.fderivWithin
  proof: h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs

中文:
定理 DifferentiableAt.fderivWithin
  证明: h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
-/
protected theorem DifferentiableAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs

/--
theorem `DifferentiableOn.mono` / 定理 `DifferentiableOn.mono`

English:
theorem DifferentiableOn.mono
  given: (h : DifferentiableOn 𝕜 f t) (st : s subseteq t)
  statement: DifferentiableOn 𝕜 f s
  proof: fun x hx => (h x (st hx)).mono st

中文:
定理 DifferentiableOn.mono
  条件: (h : DifferentiableOn 𝕜 f t) (st : s subseteq t)
  结论: DifferentiableOn 𝕜 f s
  证明: fun x hx => (h x (st hx)).mono st
-/
theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s subseteq t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st

/--
theorem `differentiableOn_univ` / 定理 `differentiableOn_univ`

English:
theorem differentiableOn_univ
  statement: DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f
  proof: by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]

@[fun_prop]

中文:
定理 differentiableOn_univ
  结论: DifferentiableOn 𝕜 f univ ↔ 可微 𝕜 f
  证明: by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]

@[fun_prop]

Depends on / 依赖: Differentiable, DifferentiableOn, differentiableWithinAt_univ, forall_true_left, mem_univ
-/
theorem differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f := by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]

@[fun_prop]
/--
theorem `Differentiable.differentiableOn` / 定理 `Differentiable.differentiableOn`

English:
theorem Differentiable.differentiableOn
  given: (h : Differentiable 𝕜 f)
  statement: DifferentiableOn 𝕜 f s
  proof: (differentiableOn_univ.2 h).mono (subset_univ _)

中文:
定理 可微.differentiableOn
  条件: (h : 可微 𝕜 f)
  结论: DifferentiableOn 𝕜 f s
  证明: (differentiableOn_univ.2 h).mono (subset_univ _)

Depends on / 依赖: differentiableOn_univ, subset_univ
-/
theorem Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)

/--
theorem `differentiableOn_of_locally_differentiableOn` / 定理 `differentiableOn_of_locally_differentiableOn`

English:
theorem differentiableOn_of_locally_differentiableOn
  proof: by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

中文:
定理 differentiableOn_of_locally_differentiableOn
  证明: by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, differentiableWithinAt_inter, mem_nhds, t_open
-/
theorem differentiableOn_of_locally_differentiableOn
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ DifferentiableOn 𝕜 f (s inter u)) :
    DifferentiableOn 𝕜 f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

/--
theorem `fderivWithin_of_mem_nhdsWithin` / 定理 `fderivWithin_of_mem_nhdsWithin`

English:
theorem fderivWithin_of_mem_nhdsWithin
  proof: ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht

中文:
定理 fderivWithin_of_mem_nhdsWithin
  证明: ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasFDerivWithinAt, fderivWithin, hasFDerivWithinAt, mono_of_mem_nhdsWithin
-/
theorem fderivWithin_of_mem_nhdsWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (st : t in 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht

/--
theorem `fderivWithin_subset` / 定理 `fderivWithin_subset`

English:
theorem fderivWithin_subset
  statement: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  proof: fderivWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h

中文:
定理 fderivWithin_subset
  结论: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  证明: fderivWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h

Depends on / 依赖: fderivWithin_of_mem_nhdsWithin, nhdsWithin_mono, self_mem_nhdsWithin
-/
theorem fderivWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fderivWithin_inter` / 定理 `fderivWithin_inter`

English:
theorem fderivWithin_inter
  given: (ht : t in 𝓝 x)
  statement: fderivWithin 𝕜 f (s inter t) x = fderivWithin 𝕜 f s x
  proof: by
  classical
  simp [fderivWithin, hasFDerivWithinAt_inter ht, DifferentiableWithinAt]

中文:
定理 fderivWithin_inter
  条件: (ht : t in 𝓝 x)
  结论: fderivWithin 𝕜 f (s inter t) x = fderivWithin 𝕜 f s x
  证明: by
  classical
  simp [fderivWithin, hasFDerivWithinAt_inter ht, DifferentiableWithinAt]

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin, hasFDerivWithinAt_inter
-/
theorem fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 f (s inter t) x = fderivWithin 𝕜 f s x := by
  classical
  simp [fderivWithin, hasFDerivWithinAt_inter ht, DifferentiableWithinAt]

/--
theorem `fderivWithin_of_mem_nhds` / 定理 `fderivWithin_of_mem_nhds`

English:
theorem fderivWithin_of_mem_nhds
  given: (h : s in 𝓝 x)
  statement: fderivWithin 𝕜 f s x = fderiv 𝕜 f x
  proof: by
  rw [← fderivWithin_univ]; rw [← univ_inter s]; rw [fderivWithin_inter h]

中文:
定理 fderivWithin_of_mem_nhds
  条件: (h : s in 𝓝 x)
  结论: fderivWithin 𝕜 f s x = fderiv 𝕜 f x
  证明: by
  rw [← fderivWithin_univ]; rw [← univ_inter s]; rw [fderivWithin_inter h]

Depends on / 依赖: fderivWithin_inter, fderivWithin_univ, univ_inter
-/
theorem fderivWithin_of_mem_nhds (h : s in 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ]; rw [← univ_inter s]; rw [fderivWithin_inter h]

/--
theorem `fderivWithin_of_isOpen` / 定理 `fderivWithin_of_isOpen`

English:
theorem fderivWithin_of_isOpen
  given: (hs : IsOpen s) (hx : x in s)
  statement: fderivWithin 𝕜 f s x = fderiv 𝕜 f x
  proof: fderivWithin_of_mem_nhds (hs.mem_nhds hx)

中文:
定理 fderivWithin_of_isOpen
  条件: (hs : 是开集 s) (hx : x in s)
  结论: fderivWithin 𝕜 f s x = fderiv 𝕜 f x
  证明: fderivWithin_of_mem_nhds (hs.mem_nhds hx)

Depends on / 依赖: fderivWithin_of_mem_nhds, hs.mem_nhds, mem_nhds
-/
theorem fderivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderivWithin_of_mem_nhds (hs.mem_nhds hx)

/--
theorem `fderivWithin_eq_fderiv` / 定理 `fderivWithin_eq_fderiv`

English:
theorem fderivWithin_eq_fderiv
  proof: by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt

中文:
定理 fderivWithin_eq_fderiv
  证明: by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, fderivWithin_subset, fderivWithin_univ, h.differentiableWithinAt, subset_univ
-/
theorem fderivWithin_eq_fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt

/--
theorem `fderiv_mem_iff` / 定理 `fderiv_mem_iff`

English:
theorem fderiv_mem_iff
  given: {f : E -> F} {s : Set (E ->L[𝕜] F)} {x : E}
  statement: fderiv 𝕜 f x in s ↔
  proof: by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]

中文:
定理 fderiv_mem_iff
  条件: {f : E -> F} {s : 集合 (E ->L[𝕜] F)} {x : E}
  结论: fderiv 𝕜 f x in s ↔
  证明: by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]

Depends on / 依赖: DifferentiableAt, fderiv_zero_of_not_differentiableAt
-/
theorem fderiv_mem_iff {f : E -> F} {s : Set (E ->L[𝕜] F)} {x : E} : fderiv 𝕜 f x in s ↔
    DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E ->L[𝕜] F) in s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]

/--
theorem `fderivWithin_mem_iff` / 定理 `fderivWithin_mem_iff`

English:
theorem fderivWithin_mem_iff
  given: {f : E -> F} {t : Set E} {s : Set (E ->L[𝕜] F)} {x : E}
  proof: by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]

中文:
定理 fderivWithin_mem_iff
  条件: {f : E -> F} {t : 集合 E} {s : 集合 (E ->L[𝕜] F)} {x : E}
  证明: by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]

Depends on / 依赖: DifferentiableWithinAt, fderivWithin_zero_of_not_differentiableWithinAt
-/
theorem fderivWithin_mem_iff {f : E -> F} {t : Set E} {s : Set (E ->L[𝕜] F)} {x : E} :
    fderivWithin 𝕜 f t x in s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜 f t x in s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E ->L[𝕜] F) in s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]

end FDerivProperties

/-! ### Being differentiable on a union of open sets can be tested on each set -/
section differentiableOn_union

/--
lemma `DifferentiableOn.union_of_isOpen` / 引理 `DifferentiableOn.union_of_isOpen`

English:
lemma DifferentiableOn.union_of_isOpen
  proof: by
  intro x hx
  obtain (hx | hx) := hx
.differentiableWithinAt · exact (hf x hx).differentiableAt (hs.mem_nhds hx)
.differentiableWithinAt · exact (hf' x hx).differentiableAt (ht.mem_nhds hx)

中文:
引理 DifferentiableOn.union_of_isOpen
  证明: by
  intro x hx
  obtain (hx | hx) := hx
.differentiableWithinAt · exact (hf x hx).differentiableAt (hs.mem_nhds hx)
.differentiableWithinAt · exact (hf' x hx).differentiableAt (ht.mem_nhds hx)

Depends on / 依赖: differentiableAt, differentiableWithinAt, hs.mem_nhds, ht.mem_nhds, mem_nhds
-/
lemma DifferentiableOn.union_of_isOpen
    (hf : DifferentiableOn 𝕜 f s) (hf' : DifferentiableOn 𝕜 f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s union t) := by
  intro x hx
  obtain (hx | hx) := hx
.differentiableWithinAt · exact (hf x hx).differentiableAt (hs.mem_nhds hx)
.differentiableWithinAt · exact (hf' x hx).differentiableAt (ht.mem_nhds hx)

/--
lemma `differentiableOn_union_iff_of_isOpen` / 引理 `differentiableOn_union_iff_of_isOpen`

English:
lemma differentiableOn_union_iff_of_isOpen
  given: (hs : IsOpen s) (ht : IsOpen t)
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => DifferentiableOn.union_of_isOpen hfs hft hs ht⟩

中文:
引理 differentiableOn_union_iff_of_isOpen
  条件: (hs : 是开集 s) (ht : 是开集 t)
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => DifferentiableOn.union_of_isOpen hfs hft hs ht⟩

Depends on / 依赖: DifferentiableOn, DifferentiableOn.union_of_isOpen, h.mono, subset_union_left, subset_union_right, union_of_isOpen
-/
lemma differentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s union t) ↔ DifferentiableOn 𝕜 f s ∧ DifferentiableOn 𝕜 f t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => DifferentiableOn.union_of_isOpen hfs hft hs ht⟩

/--
lemma `differentiable_of_differentiableOn_union_of_isOpen` / 引理 `differentiable_of_differentiableOn_union_of_isOpen`

English:
lemma differentiable_of_differentiableOn_union_of_isOpen
  statement: (hf : DifferentiableOn 𝕜 f s)
  proof: by
  rw [← differentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

中文:
引理 differentiable_of_differentiableOn_union_of_isOpen
  结论: (hf : DifferentiableOn 𝕜 f s)
  证明: by
  rw [← differentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

Depends on / 依赖: differentiableOn_univ, hf.union_of_isOpen, union_of_isOpen
-/
lemma differentiable_of_differentiableOn_union_of_isOpen (hf : DifferentiableOn 𝕜 f s)
    (hf' : DifferentiableOn 𝕜 f t) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

/--
lemma `DifferentiableOn.iUnion_of_isOpen` / 引理 `DifferentiableOn.iUnion_of_isOpen`

English:
lemma DifferentiableOn.iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.differentiableWithinAt exact (hf i).differentiableAt ((hs i).mem_nhds hxsi)

中文:
引理 DifferentiableOn.iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.differentiableWithinAt exact (hf i).differentiableAt ((hs i).mem_nhds hxsi)

Depends on / 依赖: differentiableAt, differentiableWithinAt, mem_nhds
-/
lemma DifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hf : forall i : ι, DifferentiableOn 𝕜 f (s i)) (hs : forall i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.differentiableWithinAt exact (hf i).differentiableAt ((hs i).mem_nhds hxsi)

/--
lemma `differentiableOn_iUnion_iff_of_isOpen` / 引理 `differentiableOn_iUnion_iff_of_isOpen`

English:
lemma differentiableOn_iUnion_iff_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => DifferentiableOn.iUnion_of_isOpen h hs⟩

中文:
引理 differentiableOn_iUnion_iff_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => DifferentiableOn.iUnion_of_isOpen h hs⟩

Depends on / 依赖: DifferentiableOn, DifferentiableOn.iUnion_of_isOpen, h.mono, iUnion_of_isOpen, subset_iUnion_of_subset
-/
lemma differentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hs : forall i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) ↔ forall i : ι, DifferentiableOn 𝕜 f (s i) :=
⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => DifferentiableOn.iUnion_of_isOpen h hs⟩

/--
lemma `differentiable_of_differentiableOn_iUnion_of_isOpen` / 引理 `differentiable_of_differentiableOn_iUnion_of_isOpen`

English:
lemma differentiable_of_differentiableOn_iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: by
  rw [← differentiableOn_univ]; rw [← hs']
  exact DifferentiableOn.iUnion_of_isOpen hf hs

中文:
引理 differentiable_of_differentiableOn_iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: by
  rw [← differentiableOn_univ]; rw [← hs']
  exact DifferentiableOn.iUnion_of_isOpen hf hs

Depends on / 依赖: DifferentiableOn, DifferentiableOn.iUnion_of_isOpen, differentiableOn_univ, iUnion_of_isOpen
-/
lemma differentiable_of_differentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hf : forall i : ι, DifferentiableOn 𝕜 f (s i))
    (hs : forall i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ]; rw [← hs']
  exact DifferentiableOn.iUnion_of_isOpen hf hs

end differentiableOn_union

/-! ### Asymptotics, both spaces are TVS

In this section we prove big-O and little-O lemmas about differentiable functions
between two topological vector spaces.
-/
section Asymptotics
variable [ContinuousAdd F] [ContinuousSMul 𝕜 F]

/--
theorem `HasFDerivAtFilter.isBigOTVS_sub` / 定理 `HasFDerivAtFilter.isBigOTVS_sub`

English:
theorem HasFDerivAtFilter.isBigOTVS_sub
  given: (hf : HasFDerivAtFilter f f' L)
  proof: by
  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp

中文:
定理 有FDerivAtFilter.isBigOTVS_sub
  条件: (hf : 有FDerivAtFilter f f' L)
  证明: by
  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp

Depends on / 依赖: fun_add, hf.isLittleOTVS.isBigOTVS.fun_add, isBigOTVS, isBigOTVS_comp, isLittleOTVS
-/
theorem HasFDerivAtFilter.isBigOTVS_sub (hf : HasFDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2 := by
  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp

/--
theorem `HasStrictFDerivAt.isBigOTVS_sub` / 定理 `HasStrictFDerivAt.isBigOTVS_sub`

English:
theorem HasStrictFDerivAt.isBigOTVS_sub
  given: (hf : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.isBigOTVS_sub hf

中文:
定理 HasStrictFDerivAt.isBigOTVS_sub
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.isBigOTVS_sub hf

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isBigOTVS_sub, isBigOTVS_sub
-/
theorem HasStrictFDerivAt.isBigOTVS_sub (hf : HasStrictFDerivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝕜; 𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  HasFDerivAtFilter.isBigOTVS_sub hf

/--
theorem `HasFDerivWithinAt.isBigOTVS_sub` / 定理 `HasFDerivWithinAt.isBigOTVS_sub`

English:
theorem HasFDerivWithinAt.isBigOTVS_sub
  given: (h : HasFDerivWithinAt f f' s x)
  proof: by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

中文:
定理 HasFDerivWithinAt.isBigOTVS_sub
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isBigOTVS_sub, isBigOTVS_sub
-/
theorem HasFDerivWithinAt.isBigOTVS_sub (h : HasFDerivWithinAt f f' s x) :
    (f · - f x) =O[𝕜; 𝓝[s] x] (· - x) := by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

/--
lemma `DifferentiableWithinAt.isBigOTVS_sub` / 引理 `DifferentiableWithinAt.isBigOTVS_sub`

English:
lemma DifferentiableWithinAt.isBigOTVS_sub
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.hasFDerivWithinAt.isBigOTVS_sub

中文:
引理 DifferentiableWithinAt.isBigOTVS_sub
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.hasFDerivWithinAt.isBigOTVS_sub

Depends on / 依赖: h.hasFDerivWithinAt.isBigOTVS_sub, hasFDerivWithinAt, isBigOTVS_sub
-/
lemma DifferentiableWithinAt.isBigOTVS_sub (h : DifferentiableWithinAt 𝕜 f s x) :
    (f · - f x) =O[𝕜; 𝓝[s] x] (· - x) :=
  h.hasFDerivWithinAt.isBigOTVS_sub

/--
theorem `HasFDerivAt.isBigOTVS_sub` / 定理 `HasFDerivAt.isBigOTVS_sub`

English:
theorem HasFDerivAt.isBigOTVS_sub
  given: (h : HasFDerivAt f f' x)
  statement: (f · - f x) =O[𝕜; 𝓝 x] (· - x)
  proof: by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

中文:
定理 在点处Fréchet可导.isBigOTVS_sub
  条件: (h : 在点处Fréchet可导 f f' x)
  结论: (f · - f x) =O[𝕜; 𝓝 x] (· - x)
  证明: by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isBigOTVS_sub, isBigOTVS_sub
-/
theorem HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f f' x) : (f · - f x) =O[𝕜; 𝓝 x] (· - x) := by
  simpa using! HasFDerivAtFilter.isBigOTVS_sub h

/--
theorem `DifferentiableAt.isBigOTVS_sub` / 定理 `DifferentiableAt.isBigOTVS_sub`

English:
theorem DifferentiableAt.isBigOTVS_sub
  given: (h : DifferentiableAt 𝕜 f x)
  proof: h.hasFDerivAt.isBigOTVS_sub

中文:
定理 DifferentiableAt.isBigOTVS_sub
  条件: (h : DifferentiableAt 𝕜 f x)
  证明: h.hasFDerivAt.isBigOTVS_sub

Depends on / 依赖: h.hasFDerivAt.isBigOTVS_sub, hasFDerivAt, isBigOTVS_sub
-/
theorem DifferentiableAt.isBigOTVS_sub (h : DifferentiableAt 𝕜 f x) :
    (f · - f x) =O[𝕜; 𝓝 x] (· - x) :=
  h.hasFDerivAt.isBigOTVS_sub

end Asymptotics

section Continuous

/-! ### Deducing continuity from differentiability -/
variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

/--
theorem `HasFDerivAtFilter.tendsto_nhds` / 定理 `HasFDerivAtFilter.tendsto_nhds`

English:
theorem HasFDerivAtFilter.tendsto_nhds
  statement: {L : Filter E} (hL : L <= 𝓝 x)
  proof: by
  have : (f · - f x) =o[𝕜; L] (1 : E -> 𝕜) := by
.trans_isLittleOTVS ?_ .comp_tendsto prod_pure.ge refine h.isBigOTVS_sub
    rw [isLittleOTVS_one]
    simpa [sub_eq_add_neg] using! (tendsto_id'.mpr hL).add_const (-x)
  rw [isLittleOTVS_one] at this
  simpa using! this.add_const (f x)

中文:
定理 有FDerivAtFilter.tendsto_nhds
  结论: {L : 滤子 E} (hL : L <= 𝓝 x)
  证明: by
  have : (f · - f x) =o[𝕜; L] (1 : E -> 𝕜) := by
.trans_isLittleOTVS ?_ .comp_tendsto prod_pure.ge refine h.isBigOTVS_sub
    rw [isLittleOTVS_one]
    simpa [sub_eq_add_neg] using! (tendsto_id'.mpr hL).add_const (-x)
  rw [isLittleOTVS_one] at this
  simpa using! this.add_const (f x)

Depends on / 依赖: add_const, comp_tendsto, h.isBigOTVS_sub, isBigOTVS_sub, isLittleOTVS_one, prod_pure, prod_pure.ge, sub_eq_add_neg, tendsto_id, this.add_const, trans_isLittleOTVS
-/
theorem HasFDerivAtFilter.tendsto_nhds {L : Filter E} (hL : L <= 𝓝 x)
    (h : HasFDerivAtFilter f f' (L ×ˢ pure x)) :
    Tendsto f L (𝓝 (f x)) := by
  have : (f · - f x) =o[𝕜; L] (1 : E -> 𝕜) := by
.trans_isLittleOTVS ?_ .comp_tendsto prod_pure.ge refine h.isBigOTVS_sub
    rw [isLittleOTVS_one]
    simpa [sub_eq_add_neg] using! (tendsto_id'.mpr hL).add_const (-x)
  rw [isLittleOTVS_one] at this
  simpa using! this.add_const (f x)

/--
theorem `HasFDerivWithinAt.continuousWithinAt` / 定理 `HasFDerivWithinAt.continuousWithinAt`

English:
theorem HasFDerivWithinAt.continuousWithinAt
  given: (h : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.tendsto_nhds inf_le_left h

中文:
定理 HasFDerivWithinAt.continuousWithinAt
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.tendsto_nhds inf_le_left h

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.tendsto_nhds, inf_le_left, tendsto_nhds
-/
theorem HasFDerivWithinAt.continuousWithinAt (h : HasFDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasFDerivAtFilter.tendsto_nhds inf_le_left h

/--
theorem `HasFDerivAt.continuousAt` / 定理 `HasFDerivAt.continuousAt`

English:
theorem HasFDerivAt.continuousAt
  given: (h : HasFDerivAt f f' x)
  statement: ContinuousAt f x
  proof: HasFDerivAtFilter.tendsto_nhds le_rfl h

@[fun_prop]

中文:
定理 在点处Fréchet可导.continuousAt
  条件: (h : 在点处Fréchet可导 f f' x)
  结论: ContinuousAt f x
  证明: HasFDerivAtFilter.tendsto_nhds le_rfl h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.tendsto_nhds, le_rfl, tendsto_nhds
-/
theorem HasFDerivAt.continuousAt (h : HasFDerivAt f f' x) : ContinuousAt f x :=
  HasFDerivAtFilter.tendsto_nhds le_rfl h

@[fun_prop]
/--
theorem `DifferentiableWithinAt.continuousWithinAt` / 定理 `DifferentiableWithinAt.continuousWithinAt`

English:
theorem DifferentiableWithinAt.continuousWithinAt
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.continuousWithinAt
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt

@[fun_prop]

Depends on / 依赖: continuousWithinAt
-/
theorem DifferentiableWithinAt.continuousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.continuousAt` / 定理 `DifferentiableAt.continuousAt`

English:
theorem DifferentiableAt.continuousAt
  given: (h : DifferentiableAt 𝕜 f x)
  statement: ContinuousAt f x
  proof: let ⟨_, hf'⟩ := h
  hf'.continuousAt

@[fun_prop]

中文:
定理 DifferentiableAt.continuousAt
  条件: (h : DifferentiableAt 𝕜 f x)
  结论: ContinuousAt f x
  证明: let ⟨_, hf'⟩ := h
  hf'.continuousAt

@[fun_prop]

Depends on / 依赖: continuousAt
-/
theorem DifferentiableAt.continuousAt (h : DifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousAt

@[fun_prop]
/--
theorem `DifferentiableOn.continuousOn` / 定理 `DifferentiableOn.continuousOn`

English:
theorem DifferentiableOn.continuousOn
  given: (h : DifferentiableOn 𝕜 f s)
  statement: ContinuousOn f s
  proof: fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]

中文:
定理 DifferentiableOn.continuousOn
  条件: (h : DifferentiableOn 𝕜 f s)
  结论: ContinuousOn f s
  证明: fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
-/
theorem DifferentiableOn.continuousOn (h : DifferentiableOn 𝕜 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
/--
theorem `Differentiable.continuous` / 定理 `Differentiable.continuous`

English:
theorem Differentiable.continuous
  given: (h : Differentiable 𝕜 f)
  statement: Continuous f
  proof: continuous_iff_continuousAt.2 fun x => (h x).continuousAt

中文:
定理 可微.continuous
  条件: (h : 可微 𝕜 f)
  结论: 连续 f
  证明: continuous_iff_continuousAt.2 fun x => (h x).continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt
-/
theorem Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

/--
theorem `HasStrictFDerivAt.continuousAt` / 定理 `HasStrictFDerivAt.continuousAt`

English:
theorem HasStrictFDerivAt.continuousAt
  given: (hf : HasStrictFDerivAt f f' x)
  proof: hf.hasFDerivAt.continuousAt

中文:
定理 HasStrictFDerivAt.continuousAt
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: hf.hasFDerivAt.continuousAt
-/
protected theorem HasStrictFDerivAt.continuousAt (hf : HasStrictFDerivAt f f' x) :
    ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt

end Continuous

section id


/--
theorem `hasFDerivAtFilter_id` / 定理 `hasFDerivAtFilter_id`

English:
theorem hasFDerivAtFilter_id
  given: (L : Filter (E × E))
  statement: HasFDerivAtFilter id (.id 𝕜 E) L
  proof: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left by simp

@[fun_prop]

中文:
定理 hasFDerivAtFilter_id
  条件: (L : 滤子 (E × E))
  结论: 有FDerivAtFilter id (.id 𝕜 E) L
  证明: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left by simp

@[fun_prop]

Depends on / 依赖: IsLittleOTVS, IsLittleOTVS.zero, congr_left, of_isLittleOTVS
-/
theorem hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDerivAtFilter id (.id 𝕜 E) L :=
.of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left by simp

@[fun_prop]
/--
theorem `hasStrictFDerivAt_id` / 定理 `hasStrictFDerivAt_id`

English:
theorem hasStrictFDerivAt_id
  given: (x : E)
  statement: HasStrictFDerivAt id (.id 𝕜 E) x
  proof: hasFDerivAtFilter_id _

@[fun_prop]

中文:
定理 hasStrictFDerivAt_id
  条件: (x : E)
  结论: HasStrictFDerivAt id (.id 𝕜 E) x
  证明: hasFDerivAtFilter_id _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_id
-/
theorem hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[fun_prop]
/--
theorem `hasFDerivWithinAt_id` / 定理 `hasFDerivWithinAt_id`

English:
theorem hasFDerivWithinAt_id
  given: (x : E) (s : Set E)
  statement: HasFDerivWithinAt id (.id 𝕜 E) s x
  proof: hasFDerivAtFilter_id _

@[fun_prop]

中文:
定理 hasFDerivWithinAt_id
  条件: (x : E) (s : 集合 E)
  结论: HasFDerivWithinAt id (.id 𝕜 E) s x
  证明: hasFDerivAtFilter_id _

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_id
-/
theorem hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDerivWithinAt id (.id 𝕜 E) s x :=
  hasFDerivAtFilter_id _

@[fun_prop]
/--
theorem `hasFDerivAt_id` / 定理 `hasFDerivAt_id`

English:
theorem hasFDerivAt_id
  given: (x : E)
  statement: HasFDerivAt id (.id 𝕜 E) x
  proof: hasFDerivAtFilter_id _

@[to_fun (attr := simp, fun_prop) differentiableAt_fun_id]

中文:
定理 hasFDerivAt_id
  条件: (x : E)
  结论: 在点处Fréchet可导 id (.id 𝕜 E) x
  证明: hasFDerivAtFilter_id _

@[to_fun (attr := simp, fun_prop) differentiableAt_fun_id]

Depends on / 依赖: hasFDerivAtFilter_id
-/
theorem hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[to_fun (attr := simp, fun_prop) differentiableAt_fun_id]
/--
theorem `differentiableAt_id` / 定理 `differentiableAt_id`

English:
theorem differentiableAt_id
  statement: DifferentiableAt 𝕜 id x
  proof: (hasFDerivAt_id x).differentiableAt

@[to_fun (attr := fun_prop) differentiableWithinAt_fun_id]

中文:
定理 differentiableAt_id
  结论: DifferentiableAt 𝕜 id x
  证明: (hasFDerivAt_id x).differentiableAt

@[to_fun (attr := fun_prop) differentiableWithinAt_fun_id]

Depends on / 依赖: differentiableAt, hasFDerivAt_id
-/
theorem differentiableAt_id : DifferentiableAt 𝕜 id x :=
  (hasFDerivAt_id x).differentiableAt

@[to_fun (attr := fun_prop) differentiableWithinAt_fun_id]
/--
theorem `differentiableWithinAt_id` / 定理 `differentiableWithinAt_id`

English:
theorem differentiableWithinAt_id
  statement: DifferentiableWithinAt 𝕜 id s x
  proof: differentiableAt_id.differentiableWithinAt

@[deprecated (since := "2026-05-17")]
alias differentiableWithinAt_id' := differentiableWithinAt_fun_id

@[to_fun (attr := simp, fun_prop) differentiable_fun_id]

中文:
定理 differentiableWithinAt_id
  结论: DifferentiableWithinAt 𝕜 id s x
  证明: differentiableAt_id.differentiableWithinAt

@[deprecated (since := "2026-05-17")]
alias differentiableWithinAt_id' := differentiableWithinAt_fun_id

@[to_fun (attr := simp, fun_prop) differentiable_fun_id]

Depends on / 依赖: differentiableAt_id, differentiableAt_id.differentiableWithinAt, differentiableWithinAt
-/
theorem differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.differentiableWithinAt

@[deprecated (since := "2026-05-17")]
alias differentiableWithinAt_id' := differentiableWithinAt_fun_id

@[to_fun (attr := simp, fun_prop) differentiable_fun_id]
/--
theorem `differentiable_id` / 定理 `differentiable_id`

English:
theorem differentiable_id
  statement: Differentiable 𝕜 (id : E -> E)
  proof: fun _ => differentiableAt_id

@[fun_prop]

中文:
定理 differentiable_id
  结论: 可微 𝕜 (id : E -> E)
  证明: fun _ => differentiableAt_id

@[fun_prop]

Depends on / 依赖: differentiableAt_id
-/
theorem differentiable_id : Differentiable 𝕜 (id : E -> E) := fun _ => differentiableAt_id

@[fun_prop]
/--
theorem `differentiableOn_id` / 定理 `differentiableOn_id`

English:
theorem differentiableOn_id
  statement: DifferentiableOn 𝕜 id s
  proof: differentiable_id.differentiableOn

@[to_fun (attr := simp) fderiv_fun_id]

中文:
定理 differentiableOn_id
  结论: DifferentiableOn 𝕜 id s
  证明: differentiable_id.differentiableOn

@[to_fun (attr := simp) fderiv_fun_id]

Depends on / 依赖: differentiableOn, differentiable_id, differentiable_id.differentiableOn
-/
theorem differentiableOn_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.differentiableOn

@[to_fun (attr := simp) fderiv_fun_id]
/--
theorem `fderiv_id` / 定理 `fderiv_id`

English:
theorem fderiv_id
  given: [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
  statement: fderiv 𝕜 id x = .id 𝕜 E
  proof: HasFDerivAt.fderiv (hasFDerivAt_id x)

@[deprecated (since := "2026-05-17")] alias fderiv_id' := fderiv_fun_id

@[to_fun fderivWithin_fun_id]

中文:
定理 fderiv_id
  条件: [连续加法 E] [连续标量乘法 𝕜 E] [T2空间 E]
  结论: fderiv 𝕜 id x = .id 𝕜 E
  证明: HasFDerivAt.fderiv (hasFDerivAt_id x)

@[deprecated (since := "2026-05-17")] alias fderiv_id' := fderiv_fun_id

@[to_fun fderivWithin_fun_id]

Depends on / 依赖: HasFDerivAt, HasFDerivAt.fderiv, fderiv, hasFDerivAt_id
-/
theorem fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] : fderiv 𝕜 id x = .id 𝕜 E :=
  HasFDerivAt.fderiv (hasFDerivAt_id x)

@[deprecated (since := "2026-05-17")] alias fderiv_id' := fderiv_fun_id

@[to_fun fderivWithin_fun_id]
/--
theorem `fderivWithin_id` / 定理 `fderivWithin_id`

English:
theorem fderivWithin_id
  statement: [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
  proof: by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id

@[deprecated (since := "2026-05-17")] alias fderivWithin_id' := fderivWithin_fun_id

中文:
定理 fderivWithin_id
  结论: [连续加法 E] [连续标量乘法 𝕜 E] [T2空间 E]
  证明: by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id

@[deprecated (since := "2026-05-17")] alias fderivWithin_id' := fderivWithin_fun_id

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fderivWithin, differentiableAt_id, fderivWithin, fderiv_id
-/
theorem fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E := by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id

@[deprecated (since := "2026-05-17")] alias fderivWithin_id' := fderivWithin_fun_id

end id

end

section NormedCodomain
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E -> F}
variable {f' : E ->L[𝕜] F}
variable {x x₀ : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/--
theorem `HasFDerivAtFilter.isEquivalent_sub` / 定理 `HasFDerivAtFilter.isEquivalent_sub`

English:
theorem HasFDerivAtFilter.isEquivalent_sub
  statement: (hf : HasFDerivAtFilter f f' L)
  proof: by
  rw [IsEquivalent]; rw [← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
exact hf.isLittleOTVS.trans_isBigOTVS .symm.isBigOTVS f'.isThetaTVS_comp hf'

中文:
定理 有FDerivAtFilter.isEquivalent_sub
  结论: (hf : 有FDerivAtFilter f f' L)
  证明: by
  rw [IsEquivalent]; rw [← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
exact hf.isLittleOTVS.trans_isBigOTVS .symm.isBigOTVS f'.isThetaTVS_comp hf'

Depends on / 依赖: IsEquivalent, hf.isLittleOTVS.trans_isBigOTVS, isBigOTVS, isLittleOTVS, isLittleOTVS_iff_isLittleO, isThetaTVS_comp, symm.isBigOTVS, trans_isBigOTVS
-/
theorem HasFDerivAtFilter.isEquivalent_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p => f p.1 - f p.2) ~[L] (fun p => f' (p.1 - p.2)) := by
  rw [IsEquivalent]; rw [← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
exact hf.isLittleOTVS.trans_isBigOTVS .symm.isBigOTVS f'.isThetaTVS_comp hf'

/--
theorem `HasFDerivAtFilter.isThetaTVS_sub` / 定理 `HasFDerivAtFilter.isThetaTVS_sub`

English:
theorem HasFDerivAtFilter.isThetaTVS_sub
  statement: (hf : HasFDerivAtFilter f f' L)
  proof: .isTheta.isThetaTVS.trans f'.isThetaTVS_comp hf' hf.isEquivalent_sub hf'

中文:
定理 有FDerivAtFilter.isThetaTVS_sub
  结论: (hf : 有FDerivAtFilter f f' L)
  证明: .isTheta.isThetaTVS.trans f'.isThetaTVS_comp hf' hf.isEquivalent_sub hf'

Depends on / 依赖: hf.isEquivalent_sub, isEquivalent_sub, isTheta, isTheta.isThetaTVS.trans, isThetaTVS, isThetaTVS_comp
-/
theorem HasFDerivAtFilter.isThetaTVS_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p => f p.1 - f p.2) =Θ[𝕜; L] (fun p => p.1 - p.2) :=
.isTheta.isThetaTVS.trans f'.isThetaTVS_comp hf' hf.isEquivalent_sub hf'

/--
theorem `HasFDerivAt.isEquivalent_sub` / 定理 `HasFDerivAt.isEquivalent_sub`

English:
theorem HasFDerivAt.isEquivalent_sub
  given: (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f')
  proof: by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

中文:
定理 在点处Fréchet可导.isEquivalent_sub
  条件: (hf : 在点处Fréchet可导 f f' x) (hf' : 拓扑.是Inducing f')
  证明: by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isEquivalent_sub, isEquivalent_sub
-/
theorem HasFDerivAt.isEquivalent_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝 x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

/--
theorem `HasFDerivAt.isThetaTVS_sub` / 定理 `HasFDerivAt.isThetaTVS_sub`

English:
theorem HasFDerivAt.isThetaTVS_sub
  given: (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f')
  proof: by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

中文:
定理 在点处Fréchet可导.isThetaTVS_sub
  条件: (hf : 在点处Fréchet可导 f f' x) (hf' : 拓扑.是Inducing f')
  证明: by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isThetaTVS_sub, IsThetaTVS, isThetaTVS_sub
-/
theorem HasFDerivAt.isThetaTVS_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝 x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

/--
theorem `HasFDerivWithinAt.isEquivalent_sub` / 定理 `HasFDerivWithinAt.isEquivalent_sub`

English:
theorem HasFDerivWithinAt.isEquivalent_sub
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

中文:
定理 HasFDerivWithinAt.isEquivalent_sub
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isEquivalent_sub, isEquivalent_sub
-/
theorem HasFDerivWithinAt.isEquivalent_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝[s] x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

/--
theorem `HasFDerivWithinAt.isThetaTVS_sub` / 定理 `HasFDerivWithinAt.isThetaTVS_sub`

English:
theorem HasFDerivWithinAt.isThetaTVS_sub
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

中文:
定理 HasFDerivWithinAt.isThetaTVS_sub
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isThetaTVS_sub, IsThetaTVS, isThetaTVS_sub
-/
theorem HasFDerivWithinAt.isThetaTVS_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝[s] x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

/--
theorem `HasStrictFDerivAt.isEquivalent_sub` / 定理 `HasStrictFDerivAt.isEquivalent_sub`

English:
theorem HasStrictFDerivAt.isEquivalent_sub
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.isEquivalent_sub hf hf'

中文:
定理 HasStrictFDerivAt.isEquivalent_sub
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.isEquivalent_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isEquivalent_sub, isEquivalent_sub
-/
theorem HasStrictFDerivAt.isEquivalent_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E => f p.1 - f p.2) ~[𝓝 (x, x)] (fun p => f' (p.1 - p.2)) :=
  HasFDerivAtFilter.isEquivalent_sub hf hf'

/--
theorem `HasStrictFDerivAt.isThetaTVS_sub` / 定理 `HasStrictFDerivAt.isThetaTVS_sub`

English:
theorem HasStrictFDerivAt.isThetaTVS_sub
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.isThetaTVS_sub hf hf'

中文:
定理 HasStrictFDerivAt.isThetaTVS_sub
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.isThetaTVS_sub hf hf'

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isThetaTVS_sub, isThetaTVS_sub
-/
theorem HasStrictFDerivAt.isThetaTVS_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E => f p.1 - f p.2) =Θ[𝕜; 𝓝 (x, x)] (fun p => p.1 - p.2) :=
  HasFDerivAtFilter.isThetaTVS_sub hf hf'

end NormedCodomain

-- These lemmas won't generalize to Topological Vector Spaces, at least without changing the
-- statement.
section not_TVS
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E -> F}
variable {f' : E ->L[𝕜] F}
variable {x x₀ : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/--
theorem `hasFDerivAtFilter_iff_tendsto` / 定理 `hasFDerivAtFilter_iff_tendsto`

English:
theorem hasFDerivAtFilter_iff_tendsto
  proof: by
  rw [hasFDerivAtFilter_iff_isLittleO]; rw [← isLittleO_norm_left]; rw [← isLittleO_norm_right]; rw [isLittleO_iff_tendsto]
  · simp [div_eq_inv_mul]
  · simp +contextual [sub_eq_zero]

中文:
定理 hasFDerivAtFilter_iff_tendsto
  证明: by
  rw [hasFDerivAtFilter_iff_isLittleO]; rw [← isLittleO_norm_left]; rw [← isLittleO_norm_right]; rw [isLittleO_iff_tendsto]
  · simp [div_eq_inv_mul]
  · simp +contextual [sub_eq_zero]

Depends on / 依赖: contextual, div_eq_inv_mul, hasFDerivAtFilter_iff_isLittleO, isLittleO_iff_tendsto, isLittleO_norm_left, isLittleO_norm_right, sub_eq_zero
-/
theorem hasFDerivAtFilter_iff_tendsto :
    HasFDerivAtFilter f f' L ↔
      Tendsto (fun p => ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - f' (p.1 - p.2)‖) L (𝓝 0) := by
  rw [hasFDerivAtFilter_iff_isLittleO]; rw [← isLittleO_norm_left]; rw [← isLittleO_norm_right]; rw [isLittleO_iff_tendsto]
  · simp [div_eq_inv_mul]
  · simp +contextual [sub_eq_zero]

/--
theorem `hasFDerivWithinAt_iff_tendsto` / 定理 `hasFDerivWithinAt_iff_tendsto`

English:
theorem hasFDerivWithinAt_iff_tendsto
  proof: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_tendsto, Function.comp_def]

中文:
定理 hasFDerivWithinAt_iff_tendsto
  证明: by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_tendsto, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, HasFDerivWithinAt, comp_def, hasFDerivAtFilter_iff_tendsto
-/
theorem hasFDerivWithinAt_iff_tendsto :
    HasFDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_tendsto, Function.comp_def]

/--
theorem `hasFDerivAt_iff_tendsto` / 定理 `hasFDerivAt_iff_tendsto`

English:
theorem hasFDerivAt_iff_tendsto
  proof: by
  rw [← hasFDerivWithinAt_univ]; rw [hasFDerivWithinAt_iff_tendsto]; rw [nhdsWithin_univ]

中文:
定理 hasFDerivAt_iff_tendsto
  证明: by
  rw [← hasFDerivWithinAt_univ]; rw [hasFDerivWithinAt_iff_tendsto]; rw [nhdsWithin_univ]

Depends on / 依赖: hasFDerivWithinAt_iff_tendsto, hasFDerivWithinAt_univ, nhdsWithin_univ
-/
theorem hasFDerivAt_iff_tendsto :
    HasFDerivAt f f' x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) := by
  rw [← hasFDerivWithinAt_univ]; rw [hasFDerivWithinAt_iff_tendsto]; rw [nhdsWithin_univ]

/--
theorem `hasFDerivAt_iff_isLittleO_nhds_zero` / 定理 `hasFDerivAt_iff_isLittleO_nhds_zero`

English:
theorem hasFDerivAt_iff_isLittleO_nhds_zero
  proof: by
  rw [hasFDerivAt_iff_isLittleO]; rw [← map_add_left_nhds_zero x]; rw [isLittleO_map]
  simp [Function.comp_def]

中文:
定理 hasFDerivAt_iff_isLittleO_nhds_zero
  证明: by
  rw [hasFDerivAt_iff_isLittleO]; rw [← map_add_left_nhds_zero x]; rw [isLittleO_map]
  simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, hasFDerivAt_iff_isLittleO, isLittleO_map, map_add_left_nhds_zero
-/
theorem hasFDerivAt_iff_isLittleO_nhds_zero :
    HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h := by
  rw [hasFDerivAt_iff_isLittleO]; rw [← map_add_left_nhds_zero x]; rw [isLittleO_map]
  simp [Function.comp_def]

/--
theorem `HasStrictFDerivAt.isBigO_sub` / 定理 `HasStrictFDerivAt.isBigO_sub`

English:
theorem HasStrictFDerivAt.isBigO_sub
  given: (hf : HasStrictFDerivAt f f' x)
  proof: hf.isBigOTVS_sub.isBigO

中文:
定理 HasStrictFDerivAt.isBigO_sub
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: hf.isBigOTVS_sub.isBigO

Depends on / 依赖: hf.isBigOTVS_sub.isBigO, isBigO, isBigOTVS_sub
-/
theorem HasStrictFDerivAt.isBigO_sub (hf : HasStrictFDerivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  hf.isBigOTVS_sub.isBigO

/--
theorem `HasFDerivAtFilter.isBigO_sub` / 定理 `HasFDerivAtFilter.isBigO_sub`

English:
theorem HasFDerivAtFilter.isBigO_sub
  given: (h : HasFDerivAtFilter f f' L)
  proof: h.isBigOTVS_sub.isBigO

中文:
定理 有FDerivAtFilter.isBigO_sub
  条件: (h : 有FDerivAtFilter f f' L)
  证明: h.isBigOTVS_sub.isBigO

Depends on / 依赖: h.isBigOTVS_sub.isBigO, isBigO, isBigOTVS_sub
-/
theorem HasFDerivAtFilter.isBigO_sub (h : HasFDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  h.isBigOTVS_sub.isBigO

/--
theorem `HasFDerivWithinAt.isBigO_sub` / 定理 `HasFDerivWithinAt.isBigO_sub`

English:
theorem HasFDerivWithinAt.isBigO_sub
  given: (h : HasFDerivWithinAt f f' s x₀)
  proof: h.isBigOTVS_sub.isBigO

中文:
定理 HasFDerivWithinAt.isBigO_sub
  条件: (h : HasFDerivWithinAt f f' s x₀)
  证明: h.isBigOTVS_sub.isBigO

Depends on / 依赖: h.isBigOTVS_sub.isBigO, isBigO, isBigOTVS_sub
-/
theorem HasFDerivWithinAt.isBigO_sub (h : HasFDerivWithinAt f f' s x₀) :
    (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.isBigOTVS_sub.isBigO

/--
lemma `DifferentiableWithinAt.isBigO_sub` / 引理 `DifferentiableWithinAt.isBigO_sub`

English:
lemma DifferentiableWithinAt.isBigO_sub
  given: (h : DifferentiableWithinAt 𝕜 f s x₀)
  proof: h.hasFDerivWithinAt.isBigO_sub

中文:
引理 DifferentiableWithinAt.isBigO_sub
  条件: (h : DifferentiableWithinAt 𝕜 f s x₀)
  证明: h.hasFDerivWithinAt.isBigO_sub

Depends on / 依赖: h.hasFDerivWithinAt.isBigO_sub, hasFDerivWithinAt, isBigO_sub
-/
lemma DifferentiableWithinAt.isBigO_sub (h : DifferentiableWithinAt 𝕜 f s x₀) :
    (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.hasFDerivWithinAt.isBigO_sub

/--
theorem `HasFDerivAt.isBigO_sub` / 定理 `HasFDerivAt.isBigO_sub`

English:
theorem HasFDerivAt.isBigO_sub
  given: (h : HasFDerivAt f f' x₀)
  statement: (f · - f x₀) =O[𝓝 x₀] (· - x₀)
  proof: h.isBigOTVS_sub.isBigO

中文:
定理 在点处Fréchet可导.isBigO_sub
  条件: (h : 在点处Fréchet可导 f f' x₀)
  结论: (f · - f x₀) =O[𝓝 x₀] (· - x₀)
  证明: h.isBigOTVS_sub.isBigO

Depends on / 依赖: h.isBigOTVS_sub.isBigO, isBigO, isBigOTVS_sub
-/
theorem HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.isBigOTVS_sub.isBigO

/--
theorem `DifferentiableAt.isBigO_sub` / 定理 `DifferentiableAt.isBigO_sub`

English:
theorem DifferentiableAt.isBigO_sub
  given: (h : DifferentiableAt 𝕜 f x₀)
  proof: h.hasFDerivAt.isBigO_sub

中文:
定理 DifferentiableAt.isBigO_sub
  条件: (h : DifferentiableAt 𝕜 f x₀)
  证明: h.hasFDerivAt.isBigO_sub

Depends on / 依赖: h.hasFDerivAt.isBigO_sub, hasFDerivAt, isBigO_sub
-/
theorem DifferentiableAt.isBigO_sub (h : DifferentiableAt 𝕜 f x₀) :
    (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.hasFDerivAt.isBigO_sub

/--
theorem `Asymptotics.IsBigO.hasFDerivWithinAt` / 定理 `Asymptotics.IsBigO.hasFDerivWithinAt`

English:
theorem Asymptotics.IsBigO.hasFDerivWithinAt
  statement: {n : Nat}
  proof: by
  simp_rw [hasFDerivWithinAt_iff_isLittleO,
    h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]

中文:
定理 Asymptotics.IsBigO.hasFDerivWithinAt
  结论: {n : 自然数}
  证明: by
  simp_rw [hasFDerivWithinAt_iff_isLittleO,
    h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]

Depends on / 依赖: eq_zero_of_norm_pow_within, h.eq_zero_of_norm_pow_within, h.trans_isLittleO, hasFDerivWithinAt_iff_isLittleO, hn.ne_bot, isLittleO_pow_sub_sub, ne_bot, nhdsWithin_le_nhds, simp_rw, sub_zero, trans_isLittleO, zero_apply
-/
theorem Asymptotics.IsBigO.hasFDerivWithinAt {n : Nat}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ in s) (hn : 1 < n) :
    HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x₀ := by
  simp_rw [hasFDerivWithinAt_iff_isLittleO,
    h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]

/--
theorem `Asymptotics.IsBigO.hasFDerivAt` / 定理 `Asymptotics.IsBigO.hasFDerivAt`

English:
theorem Asymptotics.IsBigO.hasFDerivAt
  statement: {x₀ : E} {n : Nat} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
  proof: by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ

中文:
定理 Asymptotics.IsBigO.hasFDerivAt
  结论: {x₀ : E} {n : 自然数} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
  证明: by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ

Depends on / 依赖: h.hasFDerivWithinAt, hasFDerivAt_of_univ, hasFDerivWithinAt, mem_univ, nhdsWithin_univ
-/
theorem Asymptotics.IsBigO.hasFDerivAt {x₀ : E} {n : Nat} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasFDerivAt f (0 : E ->L[𝕜] F) x₀ := by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ

/--
theorem `HasStrictFDerivAt.isTheta_sub` / 定理 `HasStrictFDerivAt.isTheta_sub`

English:
theorem HasStrictFDerivAt.isTheta_sub
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: .isTheta hf.isThetaTVS_sub hf'

中文:
定理 HasStrictFDerivAt.isTheta_sub
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: .isTheta hf.isThetaTVS_sub hf'

Depends on / 依赖: hf.isThetaTVS_sub, isTheta, isThetaTVS_sub
-/
theorem HasStrictFDerivAt.isTheta_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E => f p.1 - f p.2) =Θ[𝓝 (x, x)] (fun p => p.1 - p.2) :=
.isTheta hf.isThetaTVS_sub hf'

/--
theorem `HasFDerivAtFilter.isTheta_sub` / 定理 `HasFDerivAtFilter.isTheta_sub`

English:
theorem HasFDerivAtFilter.isTheta_sub
  statement: (hf : HasFDerivAtFilter f f' L)
  proof: .isTheta hf.isThetaTVS_sub hf'

中文:
定理 有FDerivAtFilter.isTheta_sub
  结论: (hf : 有FDerivAtFilter f f' L)
  证明: .isTheta hf.isThetaTVS_sub hf'

Depends on / 依赖: hf.isThetaTVS_sub, isTheta, isThetaTVS_sub
-/
theorem HasFDerivAtFilter.isTheta_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p => f p.1 - f p.2) =Θ[L] (fun p => p.1 - p.2) :=
.isTheta hf.isThetaTVS_sub hf'

/--
theorem `HasFDerivWithinAt.isTheta_sub` / 定理 `HasFDerivWithinAt.isTheta_sub`

English:
theorem HasFDerivWithinAt.isTheta_sub
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: .isTheta hf.isThetaTVS_sub hf'

中文:
定理 HasFDerivWithinAt.isTheta_sub
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: .isTheta hf.isThetaTVS_sub hf'

Depends on / 依赖: hf.isThetaTVS_sub, isTheta, isThetaTVS_sub
-/
theorem HasFDerivWithinAt.isTheta_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝[s] x] (· - x) :=
.isTheta hf.isThetaTVS_sub hf'

/--
theorem `HasFDerivAt.isTheta_sub` / 定理 `HasFDerivAt.isTheta_sub`

English:
theorem HasFDerivAt.isTheta_sub
  given: (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f')
  proof: .isTheta hf.isThetaTVS_sub hf'

中文:
定理 在点处Fréchet可导.isTheta_sub
  条件: (hf : 在点处Fréchet可导 f f' x) (hf' : 拓扑.是Inducing f')
  证明: .isTheta hf.isThetaTVS_sub hf'

Depends on / 依赖: hf.isThetaTVS_sub, isTheta, isThetaTVS_sub
-/
theorem HasFDerivAt.isTheta_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝 x] (· - x) :=
.isTheta hf.isThetaTVS_sub hf'

section Lipschitz
/-! ### Estimates on the norm of the derivative vs Lipschitz-like estimates on `f` -/

/--
theorem `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt` / 定理 `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt`

English:
theorem HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: by
  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩

中文:
定理 HasStrictFDerivAt.存在_lipschitzOnWith_of_nnnorm_lt
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: by
  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩

Depends on / 依赖: IsBigOWith, Uo.mem_nhds, add_isBigOWith, exists_nhds_square, hf.isLittleO.add_isBigOWith, isBigOWith_comp, isLittleO, lipschitzOnWith_iff_norm_sub_le, mem_nhds, mk_mem_prod, sub_add_cancel
-/
theorem HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x)
    (K : Real>=0) (hK : ‖f'‖₊ < K) : exists s in 𝓝 x, LipschitzOnWith K f s := by
  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩

/--
theorem `HasStrictFDerivAt.exists_lipschitzOnWith` / 定理 `HasStrictFDerivAt.exists_lipschitzOnWith`

English:
theorem HasStrictFDerivAt.exists_lipschitzOnWith
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt

中文:
定理 HasStrictFDerivAt.存在_lipschitzOnWith
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt

Depends on / 依赖: exists_gt, exists_lipschitzOnWith_of_nnnorm_lt, hf.exists_lipschitzOnWith_of_nnnorm_lt
-/
theorem HasStrictFDerivAt.exists_lipschitzOnWith (hf : HasStrictFDerivAt f f' x) :
    exists K, exists s in 𝓝 x, LipschitzOnWith K f s :=
  (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt

/--
theorem `HasFDerivAt.le_of_lip'` / 定理 `HasFDerivAt.le_of_lip'`

English:
theorem HasFDerivAt.le_of_lip'
  statement: {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
  proof: by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀]; rw [eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] 

中文:
定理 在点处Fréchet可导.le_of_lip'
  结论: {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : 在点处Fréchet可导 f f' x₀)
  证明: by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀]; rw [eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] 

Depends on / 依赖: add_le_add, add_mul, add_nonneg, add_sub_cancel_left, eventually_map, filter_upwards, hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff, le_of_forall_pos_le_add, map_add_left_nhds_zero, norm_le_insert, opNorm_le_of_nhds_zero
-/
theorem HasFDerivAt.le_of_lip' {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) : ‖f'‖ <= C := by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀]; rw [eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] at hyC
  calc
    ‖f' y‖ <= ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ := norm_le_insert _ _
    _ <= C * ‖y‖ + ε * ‖y‖ := add_le_add hyC hy
    _ = (C + ε) * ‖y‖ := (add_mul _ _ _).symm

/--
theorem `HasFDerivAt.le_of_lipschitzOn` / 定理 `HasFDerivAt.le_of_lipschitzOn`

English:
theorem HasFDerivAt.le_of_lipschitzOn
  proof: by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

中文:
定理 在点处Fréchet可导.le_of_lipschitzOn
  证明: by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

Depends on / 依赖: C.coe_nonneg, coe_nonneg, filter_upwards, hf.le_of_lip, hlip.norm_sub_le, le_of_lip, mem_of_mem_nhds, norm_sub_le
-/
theorem HasFDerivAt.le_of_lipschitzOn
    {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖f'‖ <= C := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/--
theorem `HasFDerivAt.le_of_lipschitz` / 定理 `HasFDerivAt.le_of_lipschitz`

English:
theorem HasFDerivAt.le_of_lipschitz
  statement: {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
  proof: hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

中文:
定理 在点处Fréchet可导.le_of_lipschitz
  结论: {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : 在点处Fréchet可导 f f' x₀)
  证明: hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

Depends on / 依赖: hf.le_of_lipschitzOn, le_of_lipschitzOn, lipschitzOnWith_univ, univ_mem
-/
theorem HasFDerivAt.le_of_lipschitz {f : E -> F} {f' : E ->L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

variable (𝕜)

/--
theorem `norm_fderiv_le_of_lip'` / 定理 `norm_fderiv_le_of_lip'`

English:
theorem norm_fderiv_le_of_lip'
  statement: {f : E -> F} {x₀ : E}
  proof: by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

中文:
定理 norm_fderiv_le_of_lip'
  结论: {f : E -> F} {x₀ : E}
  证明: by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

Depends on / 依赖: DifferentiableAt, fderiv_zero_of_not_differentiableAt, hasFDerivAt, hf.hasFDerivAt.le_of_lip, le_of_lip
-/
theorem norm_fderiv_le_of_lip' {f : E -> F} {x₀ : E}
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) :
    ‖fderiv 𝕜 f x₀‖ <= C := by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

/--
theorem `norm_fderiv_le_of_lipschitzOn` / 定理 `norm_fderiv_le_of_lipschitzOn`

English:
theorem norm_fderiv_le_of_lipschitzOn
  statement: {f : E -> F} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀)
  proof: by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

中文:
定理 norm_fderiv_le_of_lipschitzOn
  结论: {f : E -> F} {x₀ : E} {s : 集合 E} (hs : s in 𝓝 x₀)
  证明: by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

Depends on / 依赖: C.coe_nonneg, coe_nonneg, filter_upwards, hlip.norm_sub_le, mem_of_mem_nhds, norm_fderiv_le_of_lip, norm_sub_le
-/
theorem norm_fderiv_le_of_lipschitzOn {f : E -> F} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀)
    {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ <= C := by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/--
theorem `norm_fderiv_le_of_lipschitz` / 定理 `norm_fderiv_le_of_lipschitz`

English:
theorem norm_fderiv_le_of_lipschitz
  statement: {f : E -> F} {x₀ : E}
  proof: norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

中文:
定理 norm_fderiv_le_of_lipschitz
  结论: {f : E -> F} {x₀ : E}
  证明: norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

Depends on / 依赖: lipschitzOnWith_univ, norm_fderiv_le_of_lipschitzOn, univ_mem
-/
theorem norm_fderiv_le_of_lipschitz {f : E -> F} {x₀ : E}
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ <= C :=
  norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

end Lipschitz

end not_TVS

section Semilinear
/-!
## Results involving semilinear maps
-/
variable {𝕜 V V' W W' : Type*} [NontriviallyNormedField 𝕜] {σ σ' : RingHom 𝕜 𝕜}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup W'] [NormedSpace 𝕜 W']
  [RingHomIsometric σ] [RingHomInvPair σ σ'] (L : W ->SL[σ] W') (R : V' ->SL[σ'] V)

/--
lemma `HasFDerivAt.comp_semilinear` / 引理 `HasFDerivAt.comp_semilinear`

English:
lemma HasFDerivAt.comp_semilinear
  statement: {f : V -> W} {z : V'} {f' : V ->L[𝕜] W}
  proof: by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
  have := hf.comp_tendsto (R.map_zero ▸ R.continuous.continuousAt.tendsto)
  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)

中文:
引理 在点处Fréchet可导.comp_semilinear
  结论: {f : V -> W} {z : V'} {f' : V ->L[𝕜] W}
  证明: by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
  have := hf.comp_tendsto (R.map_zero ▸ R.continuous.continuousAt.tendsto)
  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)

Depends on / 依赖: L.isBigO_comp, R.continuous.continuousAt.tendsto, R.isBigO_id, R.map_zero, RingHomIsometric, comp_tendsto, continuous, continuousAt, hasFDerivAt_iff_isLittleO_nhds_zero, hf.comp_tendsto, isBigO_comp, isBigO_id, map_zero, tendsto, trans_isBigO, trans_isLittleO
-/
lemma HasFDerivAt.comp_semilinear {f : V -> W} {z : V'} {f' : V ->L[𝕜] W}
    (hf : HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R) (L.comp (f'.comp R)) z := by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
  have := hf.comp_tendsto (R.map_zero ▸ R.continuous.continuousAt.tendsto)
  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)

/--
lemma `DifferentiableAt.comp_semilinear₂` / 引理 `DifferentiableAt.comp_semilinear₂`

English:
lemma DifferentiableAt.comp_semilinear₂
  given: {f : V -> W} {z : V'} (hf : DifferentiableAt 𝕜 f (R z))
  proof: by
  simpa using (hf.hasFDerivAt.comp_semilinear L R).differentiableAt

中文:
引理 DifferentiableAt.comp_semilinear₂
  条件: {f : V -> W} {z : V'} (hf : DifferentiableAt 𝕜 f (R z))
  证明: by
  simpa using (hf.hasFDerivAt.comp_semilinear L R).differentiableAt

Depends on / 依赖: comp_semilinear, differentiableAt, hasFDerivAt, hf.hasFDerivAt.comp_semilinear
-/
lemma DifferentiableAt.comp_semilinear₂ {f : V -> W} {z : V'} (hf : DifferentiableAt 𝕜 f (R z)) :
    DifferentiableAt 𝕜 (L ∘ f ∘ R) z := by
  simpa using (hf.hasFDerivAt.comp_semilinear L R).differentiableAt

end Semilinear
