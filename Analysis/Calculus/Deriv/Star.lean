/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasDerivAt.conj_conj` and `DifferentiableAt.conj_conj`, showing that `conj ∘ f ∘ conj` is
differentiable when `f` is (and giving a formula for its derivative).
-/

public section

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F] {f : 𝕜 -> F} {f' : F} {x : 𝕜}

/-! ### Derivative of `x ↦ star x` -/

section TrivialStar

variable [TrivialStar 𝕜] {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `HasDerivAtFilter.star` / 定理 `HasDerivAtFilter.star`

English:
theorem HasDerivAtFilter.star
  given: (h : HasDerivAtFilter f f' L)
  proof: by
  simpa using h.hasFDerivAtFilter.star.hasDerivAtFilter

中文:
定理 HasDerivAtFilter.star
  条件: (h : HasDerivAtFilter f f' L)
  证明: by
  simpa using h.hasFDerivAtFilter.star.hasDerivAtFilter
-/
protected theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') L := by
  simpa using h.hasFDerivAtFilter.star.hasDerivAtFilter

/--
theorem `HasDerivWithinAt.star` / 定理 `HasDerivWithinAt.star`

English:
theorem HasDerivWithinAt.star
  given: (h : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.star h

中文:
定理 HasDerivWithinAt.star
  条件: (h : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.star h
-/
protected theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  HasDerivAtFilter.star h

/--
theorem `HasDerivAt.star` / 定理 `HasDerivAt.star`

English:
theorem HasDerivAt.star
  given: (h : HasDerivAt f f' x)
  proof: HasDerivAtFilter.star h

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

中文:
定理 HasDerivAt.star
  条件: (h : HasDerivAt f f' x)
  证明: HasDerivAtFilter.star h

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h
-/
protected theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

/--
theorem `derivWithin.star` / 定理 `derivWithin.star`

English:
theorem derivWithin.star
  proof: by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]

中文:
定理 derivWithin.star
  证明: by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]
-/
protected theorem derivWithin.star :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) := by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]

/--
theorem `deriv.star` / 定理 `deriv.star`

English:
theorem deriv.star
  statement: deriv (fun y => star (f y)) x = star (deriv f x)
  proof: DFunLike.congr_fun fderiv_star _

@[simp]

中文:
定理 deriv.star
  结论: deriv (fun y => star (f y)) x = star (deriv f x)
  证明: DFunLike.congr_fun fderiv_star _

@[simp]
-/
protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  DFunLike.congr_fun fderiv_star _

@[simp]
/--
theorem `deriv.star'` / 定理 `deriv.star'`

English:
theorem deriv.star'
  statement: (deriv fun y => star (f y)) = fun x => star (deriv f x)
  proof: funext fun _ => deriv.star

中文:
定理 deriv.star'
  结论: (deriv fun y => star (f y)) = fun x => star (deriv f x)
  证明: funext fun _ => deriv.star
-/
protected theorem deriv.star' : (deriv fun y => star (f y)) = fun x => star (deriv f x) :=
  funext fun _ => deriv.star

end TrivialStar

section NontrivialStar

variable [NormedStarGroup 𝕜]

open scoped ComplexConjugate

/--
lemma `HasDerivAt.star_conj` / 引理 `HasDerivAt.star_conj`

English:
lemma HasDerivAt.star_conj
  given: {f : 𝕜 -> F} {f' : F} (hf : HasDerivAt f f' x)
  proof: by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! hf.hasFDerivAt.star_star
  ext
  simp

中文:
引理 HasDerivAt.star_conj
  条件: {f : 𝕜 -> F} {f' : F} (hf : HasDerivAt f f' x)
  证明: by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! hf.hasFDerivAt.star_star
  ext
  simp

Depends on / 依赖: convert, hasDerivAt_iff_hasFDerivAt, hasFDerivAt, hf.hasFDerivAt.star_star, star_star
-/
lemma HasDerivAt.star_conj {f : 𝕜 -> F} {f' : F} (hf : HasDerivAt f f' x) :
    HasDerivAt (star ∘ f ∘ conj) (star f') (conj x) := by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert! hf.hasFDerivAt.star_star
  ext
  simp

/-- A function `f` has derivative `f'` at `z` iff `star ∘ f ∘ conj` has derivative `star f'` at
`conj z`. -/
@[simp]
/--
lemma `hasDerivAt_star_conj_iff` / 引理 `hasDerivAt_star_conj_iff`

English:
lemma hasDerivAt_star_conj_iff
  given: {f : 𝕜 -> F} {x : 𝕜} {f' : F}
  proof: ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj <;> simp⟩

中文:
引理 hasDerivAt_star_conj_iff
  条件: {f : 𝕜 -> F} {x : 𝕜} {f' : F}
  证明: ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj <;> simp⟩

Depends on / 依赖: Function, Function.comp_def, comp_def, convert, hf.star_conj, star_conj
-/
lemma hasDerivAt_star_conj_iff {f : 𝕜 -> F} {x : 𝕜} {f' : F} :
    HasDerivAt (star ∘ f ∘ conj) f' x ↔ HasDerivAt f (star f') (conj x) :=
  ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj <;> simp⟩

/--
lemma `HasDerivAt.conj_conj` / 引理 `HasDerivAt.conj_conj`

English:
lemma HasDerivAt.conj_conj
  given: {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
  proof: hf.star_conj

中文:
引理 HasDerivAt.conj_conj
  条件: {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
  证明: hf.star_conj

Depends on / 依赖: hf.star_conj, star_conj
-/
lemma HasDerivAt.conj_conj {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) :
    HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x) :=
  hf.star_conj

/-- A function `f` has derivative `f'` at `z` iff `conj ∘ f ∘ conj` has derivative `conj f'` at
`conj z`. -/
@[simp]
/--
lemma `hasDerivAt_conj_conj_iff` / 引理 `hasDerivAt_conj_conj_iff`

English:
lemma hasDerivAt_conj_conj_iff
  given: {f : 𝕜 -> 𝕜} {x f' : 𝕜}
  proof: hasDerivAt_star_conj_iff

中文:
引理 hasDerivAt_conj_conj_iff
  条件: {f : 𝕜 -> 𝕜} {x f' : 𝕜}
  证明: hasDerivAt_star_conj_iff

Depends on / 依赖: hasDerivAt_star_conj_iff
-/
lemma hasDerivAt_conj_conj_iff {f : 𝕜 -> 𝕜} {x f' : 𝕜} :
    HasDerivAt (conj ∘ f ∘ conj) f' x ↔ HasDerivAt f (conj f') (conj x) :=
  hasDerivAt_star_conj_iff

/--
lemma `DifferentiableAt.star_conj` / 引理 `DifferentiableAt.star_conj`

English:
lemma DifferentiableAt.star_conj
  given: {f : 𝕜 -> F} (hf : DifferentiableAt 𝕜 f x)
  proof: hf.star_star

中文:
引理 DifferentiableAt.star_conj
  条件: {f : 𝕜 -> F} (hf : DifferentiableAt 𝕜 f x)
  证明: hf.star_star

Depends on / 依赖: hf.star_star, star_star
-/
lemma DifferentiableAt.star_conj {f : 𝕜 -> F} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `star ∘ f ∘ conj` is differentiable at `z`. -/
@[simp]
/--
lemma `differentiableAt_star_conj_iff` / 引理 `differentiableAt_star_conj_iff`

English:
lemma differentiableAt_star_conj_iff
  given: {f : 𝕜 -> F}
  proof: ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj; simp⟩

中文:
引理 differentiableAt_star_conj_iff
  条件: {f : 𝕜 -> F}
  证明: ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj; simp⟩

Depends on / 依赖: Function, Function.comp_def, comp_def, convert, hf.star_conj, star_conj
-/
lemma differentiableAt_star_conj_iff {f : 𝕜 -> F} :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x) :=
  ⟨fun hf => by convert! hf.star_conj; simp [Function.comp_def],
    fun hf => by convert! hf.star_conj; simp⟩

/--
lemma `DifferentiableAt.conj_conj` / 引理 `DifferentiableAt.conj_conj`

English:
lemma DifferentiableAt.conj_conj
  given: {f : 𝕜 -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  proof: hf.star_star

中文:
引理 DifferentiableAt.conj_conj
  条件: {f : 𝕜 -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  证明: hf.star_star

Depends on / 依赖: hf.star_star, star_star
-/
lemma DifferentiableAt.conj_conj {f : 𝕜 -> 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `conj ∘ f ∘ conj` is differentiable at `z`. -/
@[simp]
/--
lemma `differentiableAt_conj_conj_iff` / 引理 `differentiableAt_conj_conj_iff`

English:
lemma differentiableAt_conj_conj_iff
  given: {f : 𝕜 -> 𝕜}
  proof: differentiableAt_star_conj_iff

中文:
引理 differentiableAt_conj_conj_iff
  条件: {f : 𝕜 -> 𝕜}
  证明: differentiableAt_star_conj_iff

Depends on / 依赖: differentiableAt_star_conj_iff
-/
lemma differentiableAt_conj_conj_iff {f : 𝕜 -> 𝕜} :
    DifferentiableAt 𝕜 (conj ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x) :=
  differentiableAt_star_conj_iff

/-- The derivative of `star ∘ f ∘ conj` is `star ∘ deriv f ∘ conj`. -/
@[simp]
/--
lemma `deriv_star_conj` / 引理 `deriv_star_conj`

English:
lemma deriv_star_conj
  given: {f : 𝕜 -> F}
  proof: by
  ext z
  by_cases hf : DifferentiableAt 𝕜 f (conj z)
  · convert! hf.hasDerivAt.star_conj.deriv; simp
  · have := differentiableAt_star_conj_iff.not.2 hf
    simp_all [deriv_zero_of_not_differentiableAt]

中文:
引理 deriv_star_conj
  条件: {f : 𝕜 -> F}
  证明: by
  ext z
  by_cases hf : DifferentiableAt 𝕜 f (conj z)
  · convert! hf.hasDerivAt.star_conj.deriv; simp
  · have := differentiableAt_star_conj_iff.not.2 hf
    simp_all [deriv_zero_of_not_differentiableAt]

Depends on / 依赖: DifferentiableAt, convert, deriv_zero_of_not_differentiableAt, differentiableAt_star_conj_iff, differentiableAt_star_conj_iff.not, hasDerivAt, hf.hasDerivAt.star_conj.deriv, star_conj
-/
lemma deriv_star_conj {f : 𝕜 -> F} :
    deriv (star ∘ f ∘ conj) = star ∘ deriv f ∘ conj := by
  ext z
  by_cases hf : DifferentiableAt 𝕜 f (conj z)
  · convert! hf.hasDerivAt.star_conj.deriv; simp
  · have := differentiableAt_star_conj_iff.not.2 hf
    simp_all [deriv_zero_of_not_differentiableAt]

/-- The derivative of `conj ∘ f ∘ conj` is `conj ∘ deriv f ∘ conj`. -/
@[simp]
/--
lemma `deriv_conj_conj` / 引理 `deriv_conj_conj`

English:
lemma deriv_conj_conj
  given: {f : 𝕜 -> 𝕜}
  proof: deriv_star_conj

中文:
引理 deriv_conj_conj
  条件: {f : 𝕜 -> 𝕜}
  证明: deriv_star_conj

Depends on / 依赖: deriv_star_conj
-/
lemma deriv_conj_conj {f : 𝕜 -> 𝕜} :
    deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj := deriv_star_conj

end NontrivialStar
