/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the Fréchet derivative of the
star operation. For detailed documentation of the Fréchet derivative, see the module docstring of
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasFDerivAt.star_star` and `DifferentiableAt.star_star`, showing that `star ∘ f ∘ star` is
differentiable when `f` is (and giving a formula for its derivative).
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [StarAddMonoid F] [NormedSpace 𝕜 F] [StarModule 𝕜 F]
  [ContinuousStar F]

variable {f : E -> F} {f' : E ->L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section TrivialStar

variable [TrivialStar 𝕜]

/--
theorem `HasFDerivAtFilter.star` / 定理 `HasFDerivAtFilter.star`

English:
theorem HasFDerivAtFilter.star
  given: (h : HasFDerivAtFilter f f' L)
  proof: (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp h Filter.tendsto_map

@[fun_prop]

中文:
定理 HasFDerivAtFilter.star
  条件: (h : HasFDerivAtFilter f f' L)
  证明: (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp h Filter.tendsto_map

@[fun_prop]
-/
protected theorem HasFDerivAtFilter.star (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L f') L :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp h Filter.tendsto_map

@[fun_prop]
/--
theorem `HasStrictFDerivAt.star` / 定理 `HasStrictFDerivAt.star`

English:
theorem HasStrictFDerivAt.star
  given: (h : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.star h

@[fun_prop]

中文:
定理 HasStrictFDerivAt.star
  条件: (h : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.star h

@[fun_prop]
-/
protected theorem HasStrictFDerivAt.star (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L f') x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/--
theorem `HasFDerivWithinAt.star` / 定理 `HasFDerivWithinAt.star`

English:
theorem HasFDerivWithinAt.star
  given: (h : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.star h

@[fun_prop]

中文:
定理 HasFDerivWithinAt.star
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.star h

@[fun_prop]
-/
protected theorem HasFDerivWithinAt.star (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L f') s x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/--
theorem `HasFDerivAt.star` / 定理 `HasFDerivAt.star`

English:
theorem HasFDerivAt.star
  given: (h : HasFDerivAt f f' x)
  proof: HasFDerivAtFilter.star h

@[fun_prop]

中文:
定理 HasFDerivAt.star
  条件: (h : HasFDerivAt f f' x)
  证明: HasFDerivAtFilter.star h

@[fun_prop]
-/
protected theorem HasFDerivAt.star (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L f') x :=
  HasFDerivAtFilter.star h

@[fun_prop]
/--
theorem `DifferentiableWithinAt.star` / 定理 `DifferentiableWithinAt.star`

English:
theorem DifferentiableWithinAt.star
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.hasFDerivWithinAt.star.differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.star
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.hasFDerivWithinAt.star.differentiableWithinAt

@[simp]
-/
protected theorem DifferentiableWithinAt.star (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x :=
  h.hasFDerivWithinAt.star.differentiableWithinAt

@[simp]
/--
theorem `differentiableWithinAt_star_iff` / 定理 `differentiableWithinAt_star_iff`

English:
theorem differentiableWithinAt_star_iff
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff

@[fun_prop]

中文:
定理 differentiableWithinAt_star_iff
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff

@[fun_prop]

Depends on / 依赖: comp_differentiableWithinAt_iff
-/
theorem differentiableWithinAt_star_iff :
    DifferentiableWithinAt 𝕜 (fun y => star (f y)) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableWithinAt_iff

@[fun_prop]
/--
theorem `DifferentiableAt.star` / 定理 `DifferentiableAt.star`

English:
theorem DifferentiableAt.star
  given: (h : DifferentiableAt 𝕜 f x)
  proof: h.hasFDerivAt.star.differentiableAt

@[simp]

中文:
定理 DifferentiableAt.star
  条件: (h : DifferentiableAt 𝕜 f x)
  证明: h.hasFDerivAt.star.differentiableAt

@[simp]
-/
protected theorem DifferentiableAt.star (h : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => star (f y)) x :=
  h.hasFDerivAt.star.differentiableAt

@[simp]
/--
theorem `differentiableAt_star_iff` / 定理 `differentiableAt_star_iff`

English:
theorem differentiableAt_star_iff
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff

@[fun_prop]

中文:
定理 differentiableAt_star_iff
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff

@[fun_prop]

Depends on / 依赖: comp_differentiableAt_iff
-/
theorem differentiableAt_star_iff :
    DifferentiableAt 𝕜 (fun y => star (f y)) x ↔ DifferentiableAt 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableAt_iff

@[fun_prop]
/--
theorem `DifferentiableOn.star` / 定理 `DifferentiableOn.star`

English:
theorem DifferentiableOn.star
  given: (h : DifferentiableOn 𝕜 f s)
  proof: fun x hx => (h x hx).star

@[simp]

中文:
定理 DifferentiableOn.star
  条件: (h : DifferentiableOn 𝕜 f s)
  证明: fun x hx => (h x hx).star

@[simp]
-/
protected theorem DifferentiableOn.star (h : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => star (f y)) s := fun x hx => (h x hx).star

@[simp]
/--
theorem `differentiableOn_star_iff` / 定理 `differentiableOn_star_iff`

English:
theorem differentiableOn_star_iff
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff

@[fun_prop]

中文:
定理 differentiableOn_star_iff
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff

@[fun_prop]

Depends on / 依赖: comp_differentiableOn_iff
-/
theorem differentiableOn_star_iff :
    DifferentiableOn 𝕜 (fun y => star (f y)) s ↔ DifferentiableOn 𝕜 f s :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiableOn_iff

@[fun_prop]
/--
theorem `Differentiable.star` / 定理 `Differentiable.star`

English:
theorem Differentiable.star
  given: (h : Differentiable 𝕜 f)
  proof: fun x => (h x).star

@[simp]

中文:
定理 Differentiable.star
  条件: (h : Differentiable 𝕜 f)
  证明: fun x => (h x).star

@[simp]
-/
protected theorem Differentiable.star (h : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => star (f y) :=
  fun x => (h x).star

@[simp]
/--
theorem `differentiable_star_iff` / 定理 `differentiable_star_iff`

English:
theorem differentiable_star_iff
  statement: (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff

中文:
定理 differentiable_star_iff
  结论: (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff

Depends on / 依赖: comp_differentiable_iff
-/
theorem differentiable_star_iff : (Differentiable 𝕜 fun y => star (f y)) ↔ Differentiable 𝕜 f :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff

/--
theorem `fderivWithin_star` / 定理 `fderivWithin_star`

English:
theorem fderivWithin_star
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_star
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs

@[simp]

Depends on / 依赖: comp_fderivWithin
-/
theorem fderivWithin_star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => star (f y)) s x =
      ((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L fderivWithin 𝕜 f s x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderivWithin hxs

@[simp]
/--
theorem `fderiv_star` / 定理 `fderiv_star`

English:
theorem fderiv_star
  proof: (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv

中文:
定理 fderiv_star
  证明: (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv

Depends on / 依赖: comp_fderiv
-/
theorem fderiv_star :
    fderiv 𝕜 (fun y => star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) : F ->L[𝕜] F) ∘L fderiv 𝕜 f x :=
  (starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv

end TrivialStar

section NontrivialStar

/-!
## Composing on the left and right with `star`
-/

variable [StarAddMonoid E] [StarModule 𝕜 E] [ContinuousStar E] [NormedStarGroup 𝕜]

/-- If `f` has derivative `f'` at `z`, then `star ∘ f ∘ star` has derivative `starL ∘ f' ∘ starL`
at `star z`. -/
@[fun_prop]
/--
lemma `HasFDerivAt.star_star` / 引理 `HasFDerivAt.star_star`

English:
lemma HasFDerivAt.star_star
  given: {f : E -> F} {z : E} {f' : E ->L[𝕜] F} (hf : HasFDerivAt f f' z)
  proof: .comp_semilinear (starL 𝕜).toContinuousLinearMap (starL 𝕜).toContinuousLinearMap
    (by simpa using hf)

中文:
引理 HasFDerivAt.star_star
  条件: {f : E -> F} {z : E} {f' : E ->L[𝕜] F} (hf : HasFDerivAt f f' z)
  证明: .comp_semilinear (starL 𝕜).toContinuousLinearMap (starL 𝕜).toContinuousLinearMap
    (by simpa using hf)

Depends on / 依赖: comp_semilinear, toContinuousLinearMap
-/
lemma HasFDerivAt.star_star {f : E -> F} {z : E} {f' : E ->L[𝕜] F} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (star ∘ f ∘ star)
      ((starL 𝕜).toContinuousLinearMap.comp <| f'.comp (starL 𝕜).toContinuousLinearMap) (star z) :=
  .comp_semilinear (starL 𝕜).toContinuousLinearMap (starL 𝕜).toContinuousLinearMap
    (by simpa using hf)

/-- If `f` is differentiable at `z`, then `star ∘ f ∘ star` is differentiable at `star z`. -/
@[fun_prop]
/--
lemma `DifferentiableAt.star_star` / 引理 `DifferentiableAt.star_star`

English:
lemma DifferentiableAt.star_star
  given: {f : E -> F} {z : E} (hf : DifferentiableAt 𝕜 f z)
  proof: hf.hasFDerivAt.star_star.differentiableAt

中文:
引理 DifferentiableAt.star_star
  条件: {f : E -> F} {z : E} (hf : DifferentiableAt 𝕜 f z)
  证明: hf.hasFDerivAt.star_star.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.star_star.differentiableAt, star_star
-/
lemma DifferentiableAt.star_star {f : E -> F} {z : E} (hf : DifferentiableAt 𝕜 f z) :
    DifferentiableAt 𝕜 (star ∘ f ∘ star) (star z) :=
  hf.hasFDerivAt.star_star.differentiableAt

end NontrivialStar
