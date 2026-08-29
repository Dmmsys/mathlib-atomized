/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyu Wang, Chenyi Li, Sébastien Gouëzel, Penghao Yu, Zhipeng Cao
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`), `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file develops the following aspects of the theory of gradients:
* definitions of gradients, both within a set and on the whole space.
* translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `gradient` and `fderiv`.
* uniqueness of gradients.
* translating between `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `gradient` and `deriv` when `F = 𝕜`.
* the theorems about the inner product of the gradient.
* the congruence of the gradient.
* the gradient of constant functions.
* the continuity of a function admitting a gradient.
-/

@[expose] public section

@[expose] public section

open ComplexConjugate Topology InnerProductSpace Function Set

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F -> 𝕜} {f' x y : F}

/--
Definition of `HasGradientAtFilter` / `HasGradientAtFilter` 的定义

English:
definition HasGradientAtFilter
  signature: (f : F -> 𝕜) (f' x : F) (L : Filter F)
  body: HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

中文:
定义 HasGradientAtFilter
  签名: (f : F -> 𝕜) (f' x : F) (L : Filter F)
  定义体: HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

Depends on / 依赖: HasFDerivAtFilter, toDual
-/
def HasGradientAtFilter (f : F -> 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

/--
Definition of `HasGradientWithinAt` / `HasGradientWithinAt` 的定义

English:
definition HasGradientWithinAt
  signature: (f : F -> 𝕜) (f' : F) (s : Set F) (x : F)
  body: HasGradientAtFilter f f' x (𝓝[s] x)

中文:
定义 HasGradientWithinAt
  签名: (f : F -> 𝕜) (f' : F) (s : Set F) (x : F)
  定义体: HasGradientAtFilter f f' x (𝓝[s] x)

Depends on / 依赖: HasGradientAtFilter
-/
def HasGradientWithinAt (f : F -> 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)

/--
Definition of `HasGradientAt` / `HasGradientAt` 的定义

English:
definition HasGradientAt
  signature: (f : F -> 𝕜) (f' x : F)
  body: HasGradientAtFilter f f' x (𝓝 x)

中文:
定义 HasGradientAt
  签名: (f : F -> 𝕜) (f' x : F)
  定义体: HasGradientAtFilter f f' x (𝓝 x)

Depends on / 依赖: HasGradientAtFilter
-/
def HasGradientAt (f : F -> 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)

/--
Definition of `gradientWithin` / `gradientWithin` 的定义

English:
definition gradientWithin
  signature: (f : F -> 𝕜) (s : Set F) (x : F)
  body: (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

中文:
定义 gradientWithin
  签名: (f : F -> 𝕜) (s : Set F) (x : F)
  定义体: (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

Depends on / 依赖: fderivWithin, toDual
-/
def gradientWithin (f : F -> 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

/--
Definition of `gradient` / `gradient` 的定义

English:
definition gradient
  signature: (f : F -> 𝕜) (x : F)
  body: (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

中文:
定义 gradient
  签名: (f : F -> 𝕜) (x : F)
  定义体: (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

Depends on / 依赖: fderiv, toDual
-/
def gradient (f : F -> 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped Gradient

variable {s : Set F} {L : Filter F}

/--
theorem `hasGradientWithinAt_iff_hasFDerivWithinAt` / 定理 `hasGradientWithinAt_iff_hasFDerivWithinAt`

English:
theorem hasGradientWithinAt_iff_hasFDerivWithinAt
  given: {s : Set F}
  proof: Iff.rfl

中文:
定理 hasGradientWithinAt_iff_hasFDerivWithinAt
  条件: {s : Set F}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x :=
  Iff.rfl

/--
theorem `hasFDerivWithinAt_iff_hasGradientWithinAt` / 定理 `hasFDerivWithinAt_iff_hasGradientWithinAt`

English:
theorem hasFDerivWithinAt_iff_hasGradientWithinAt
  given: {frechet : StrongDual 𝕜 F} {s : Set F}
  proof: by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

中文:
定理 hasFDerivWithinAt_iff_hasGradientWithinAt
  条件: {frechet : StrongDual 𝕜 F} {s : Set F}
  证明: by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

Depends on / 依赖: apply_symm_apply, frechet, hasGradientWithinAt_iff_hasFDerivWithinAt, toDual
-/
theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : StrongDual 𝕜 F} {s : Set F} :
    HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

/--
theorem `hasGradientAt_iff_hasFDerivAt` / 定理 `hasGradientAt_iff_hasFDerivAt`

English:
theorem hasGradientAt_iff_hasFDerivAt
  proof: Iff.rfl

中文:
定理 hasGradientAt_iff_hasFDerivAt
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x :=
  Iff.rfl

/--
theorem `hasFDerivAt_iff_hasGradientAt` / 定理 `hasFDerivAt_iff_hasGradientAt`

English:
theorem hasFDerivAt_iff_hasGradientAt
  given: {frechet : StrongDual 𝕜 F}
  proof: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

alias ⟨HasGradientAt.hasF

中文:
定理 hasFDerivAt_iff_hasGradientAt
  条件: {frechet : StrongDual 𝕜 F}
  证明: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

alias ⟨HasGradientAt.hasF

Depends on / 依赖: apply_symm_apply, frechet, hasGradientAt_iff_hasFDerivAt, toDual
-/
theorem hasFDerivAt_iff_hasGradientAt {frechet : StrongDual 𝕜 F} :
    HasFDerivAt f frechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [(toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt

alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt

/--
theorem `gradient_eq_zero_of_not_differentiableAt` / 定理 `gradient_eq_zero_of_not_differentiableAt`

English:
theorem gradient_eq_zero_of_not_differentiableAt
  given: (h : ¬DifferentiableAt 𝕜 f x)
  statement: ∇ f x = 0
  proof: by
  rw [gradient]; rw [fderiv_zero_of_not_differentiableAt h]; rw [map_zero]

@[simp]

中文:
定理 gradient_eq_zero_of_not_differentiableAt
  条件: (h : ¬DifferentiableAt 𝕜 f x)
  结论: ∇ f x = 0
  证明: by
  rw [gradient]; rw [fderiv_zero_of_not_differentiableAt h]; rw [map_zero]

@[simp]

Depends on / 依赖: fderiv_zero_of_not_differentiableAt, gradient, map_zero
-/
theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient]; rw [fderiv_zero_of_not_differentiableAt h]; rw [map_zero]

@[simp]
/--
lemma `toDual_gradientWithin` / 引理 `toDual_gradientWithin`

English:
lemma toDual_gradientWithin
  proof: by
  rw [gradientWithin]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]

中文:
引理 toDual_gradientWithin
  证明: by
  rw [gradientWithin]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, gradientWithin, toDual
-/
lemma toDual_gradientWithin :
    (toDual 𝕜 F) (gradientWithin f s x) = fderivWithin 𝕜 f s x := by
  rw [gradientWithin]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]
/--
lemma `toDual_gradient` / 引理 `toDual_gradient`

English:
lemma toDual_gradient
  statement: (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x
  proof: by
  rw [gradient]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]

中文:
引理 toDual_gradient
  结论: (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x
  证明: by
  rw [gradient]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, gradient, toDual
-/
lemma toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x := by
  rw [gradient]; rw [(toDual 𝕜 F).apply_symm_apply]

@[simp]
/--
lemma `toDual_comp_gradientWithin` / 引理 `toDual_comp_gradientWithin`

English:
lemma toDual_comp_gradientWithin
  proof: funext fun _ => toDual_gradientWithin

@[simp]

中文:
引理 toDual_comp_gradientWithin
  证明: funext fun _ => toDual_gradientWithin

@[simp]

Depends on / 依赖: toDual_gradientWithin
-/
lemma toDual_comp_gradientWithin :
    (toDual 𝕜 F) ∘ gradientWithin f s = fderivWithin 𝕜 f s :=
  funext fun _ => toDual_gradientWithin

@[simp]
/--
lemma `toDual_comp_gradient` / 引理 `toDual_comp_gradient`

English:
lemma toDual_comp_gradient
  statement: (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f
  proof: funext fun _ => toDual_gradient

中文:
引理 toDual_comp_gradient
  结论: (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f
  证明: funext fun _ => toDual_gradient

Depends on / 依赖: toDual_gradient
-/
lemma toDual_comp_gradient : (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f :=
  funext fun _ => toDual_gradient

/--
theorem `HasGradientAt.unique` / 定理 `HasGradientAt.unique`

English:
theorem HasGradientAt.unique
  statement: {gradf gradg : F}
  proof: (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

中文:
定理 HasGradientAt.unique
  结论: {gradf gradg : F}
  证明: (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

Depends on / 依赖: hasFDerivAt, hf.hasFDerivAt.unique, hg.hasFDerivAt, injective, toDual, unique
-/
theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

/--
theorem `DifferentiableAt.hasGradientAt` / 定理 `DifferentiableAt.hasGradientAt`

English:
theorem DifferentiableAt.hasGradientAt
  given: (h : DifferentiableAt 𝕜 f x)
  proof: by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt

中文:
定理 DifferentiableAt.hasGradientAt
  条件: (h : DifferentiableAt 𝕜 f x)
  证明: by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt

Depends on / 依赖: h.hasFDerivAt, hasFDerivAt, hasGradientAt_iff_hasFDerivAt
-/
theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt

/--
theorem `HasGradientAt.differentiableAt` / 定理 `HasGradientAt.differentiableAt`

English:
theorem HasGradientAt.differentiableAt
  given: (h : HasGradientAt f f' x)
  proof: h.hasFDerivAt.differentiableAt

中文:
定理 HasGradientAt.differentiableAt
  条件: (h : HasGradientAt f f' x)
  证明: h.hasFDerivAt.differentiableAt

Depends on / 依赖: differentiableAt, h.hasFDerivAt.differentiableAt, hasFDerivAt
-/
theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

/--
theorem `DifferentiableWithinAt.hasGradientWithinAt` / 定理 `DifferentiableWithinAt.hasGradientWithinAt`

English:
theorem DifferentiableWithinAt.hasGradientWithinAt
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt

中文:
定理 DifferentiableWithinAt.hasGradientWithinAt
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt

Depends on / 依赖: h.hasFDerivWithinAt, hasFDerivWithinAt, hasGradientWithinAt_iff_hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt

/--
theorem `HasGradientWithinAt.differentiableWithinAt` / 定理 `HasGradientWithinAt.differentiableWithinAt`

English:
theorem HasGradientWithinAt.differentiableWithinAt
  given: (h : HasGradientWithinAt f f' s x)
  proof: h.hasFDerivWithinAt.differentiableWithinAt

@[simp]

中文:
定理 HasGradientWithinAt.differentiableWithinAt
  条件: (h : HasGradientWithinAt f f' s x)
  证明: h.hasFDerivWithinAt.differentiableWithinAt

@[simp]

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.differentiableWithinAt, hasFDerivWithinAt
-/
theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.hasFDerivWithinAt.differentiableWithinAt

@[simp]
/--
theorem `hasGradientWithinAt_univ` / 定理 `hasGradientWithinAt_univ`

English:
theorem hasGradientWithinAt_univ
  statement: HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x
  proof: by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

@[simp]

中文:
定理 hasGradientWithinAt_univ
  结论: HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x
  证明: by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

@[simp]

Depends on / 依赖: hasFDerivWithinAt_univ, hasGradientAt_iff_hasFDerivAt, hasGradientWithinAt_iff_hasFDerivWithinAt
-/
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]; rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

@[simp]
/--
lemma `gradientWithin_univ` / 引理 `gradientWithin_univ`

English:
lemma gradientWithin_univ
  statement: gradientWithin f univ = gradient f
  proof: by
  ext; simp [gradientWithin, gradient]

中文:
引理 gradientWithin_univ
  结论: gradientWithin f univ = gradient f
  证明: by
  ext; simp [gradientWithin, gradient]

Depends on / 依赖: gradient, gradientWithin
-/
lemma gradientWithin_univ : gradientWithin f univ = gradient f := by
  ext; simp [gradientWithin, gradient]

/--
theorem `DifferentiableOn.hasGradientAt` / 定理 `DifferentiableOn.hasGradientAt`

English:
theorem DifferentiableOn.hasGradientAt
  given: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  proof: (h.hasFDerivAt hs).hasGradientAt

中文:
定理 DifferentiableOn.hasGradientAt
  条件: (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x)
  证明: (h.hasFDerivAt hs).hasGradientAt

Depends on / 依赖: h.hasFDerivAt, hasFDerivAt, hasGradientAt
-/
theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt

/--
theorem `HasGradientAt.gradient` / 定理 `HasGradientAt.gradient`

English:
theorem HasGradientAt.gradient
  given: (h : HasGradientAt f f' x)
  statement: ∇ f x = f'
  proof: h.differentiableAt.hasGradientAt.unique h

中文:
定理 HasGradientAt.gradient
  条件: (h : HasGradientAt f f' x)
  结论: ∇ f x = f'
  证明: h.differentiableAt.hasGradientAt.unique h

Depends on / 依赖: differentiableAt, h.differentiableAt.hasGradientAt.unique, hasGradientAt, unique
-/
theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h

/--
theorem `gradient_eq` / 定理 `gradient_eq`

English:
theorem gradient_eq
  given: {f' : F -> F} (h : forall x, HasGradientAt f (f' x) x)
  statement: ∇ f = f'
  proof: funext fun x => (h x).gradient

中文:
定理 gradient_eq
  条件: {f' : F -> F} (h : 对任意 x, HasGradientAt f (f' x) x)
  结论: ∇ f = f'
  证明: funext fun x => (h x).gradient

Depends on / 依赖: gradient
-/
theorem gradient_eq {f' : F -> F} (h : forall x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient

section OneDimension

variable {g : 𝕜 -> 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

/--
theorem `HasGradientAtFilter.hasDerivAtFilter` / 定理 `HasGradientAtFilter.hasDerivAtFilter`

English:
theorem HasGradientAtFilter.hasDerivAtFilter
  given: (h : HasGradientAtFilter g g' u L')
  proof: h

中文:
定理 HasGradientAtFilter.hasDerivAtFilter
  条件: (h : HasGradientAtFilter g g' u L')
  证明: h
-/
theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (conj g') (L' ×ˢ pure u) :=
  h

/--
theorem `HasDerivAtFilter.hasGradientAtFilter` / 定理 `HasDerivAtFilter.hasGradientAtFilter`

English:
theorem HasDerivAtFilter.hasGradientAtFilter
  given: (h : HasDerivAtFilter g g' (L' ×ˢ pure u))
  proof: by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 ->L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

中文:
定理 HasDerivAtFilter.hasGradientAtFilter
  条件: (h : HasDerivAtFilter g g' (L' ×ˢ pure u))
  证明: by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 ->L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight, HasGradientAtFilter, smulRight, toDual
-/
theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g (conj g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 ->L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

/--
theorem `HasGradientAt.hasDerivAt` / 定理 `HasGradientAt.hasDerivAt`

English:
theorem HasGradientAt.hasDerivAt
  given: (h : HasGradientAt g g' u)
  statement: HasDerivAt g (conj g') u
  proof: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

中文:
定理 HasGradientAt.hasDerivAt
  条件: (h : HasGradientAt g g' u)
  结论: HasDerivAt g (conj g') u
  证明: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

Depends on / 依赖: hasFDerivAt_iff_hasDerivAt, hasGradientAt_iff_hasFDerivAt
-/
theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) : HasDerivAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

/--
theorem `HasDerivAt.hasGradientAt` / 定理 `HasDerivAt.hasGradientAt`

English:
theorem HasDerivAt.hasGradientAt
  given: (h : HasDerivAt g g' u)
  statement: HasGradientAt g (conj g') u
  proof: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt]
  simpa

中文:
定理 HasDerivAt.hasGradientAt
  条件: (h : HasDerivAt g g' u)
  结论: HasGradientAt g (conj g') u
  证明: by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt]
  simpa

Depends on / 依赖: hasFDerivAt_iff_hasDerivAt, hasGradientAt_iff_hasFDerivAt
-/
theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) : HasGradientAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt]; rw [hasFDerivAt_iff_hasDerivAt]
  simpa

/--
theorem `gradient_eq_deriv` / 定理 `gradient_eq_deriv`

English:
theorem gradient_eq_deriv
  statement: ∇ g u = conj (deriv g u)
  proof: by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

中文:
定理 gradient_eq_deriv
  结论: ∇ g u = conj (deriv g u)
  证明: by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

Depends on / 依赖: DifferentiableAt, RCLike, RCLike.conj_conj, conj_conj, deriv_zero_of_not_differentiableAt, gradient_eq_zero_of_not_differentiableAt, h.hasGradientAt.hasDerivAt.deriv, hasDerivAt, hasGradientAt, map_zero
-/
theorem gradient_eq_deriv : ∇ g u = conj (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

end OneDimension

section OneDimensionReal

variable {g : Real -> Real} {g' u : Real} {L' : Filter Real}

/--
theorem `HasGradientAtFilter.hasDerivAtFilter'` / 定理 `HasGradientAtFilter.hasDerivAtFilter'`

English:
theorem HasGradientAtFilter.hasDerivAtFilter'
  given: (h : HasGradientAtFilter g g' u L')
  proof: h.hasDerivAtFilter

中文:
定理 HasGradientAtFilter.hasDerivAtFilter'
  条件: (h : HasGradientAtFilter g g' u L')
  证明: h.hasDerivAtFilter

Depends on / 依赖: h.hasDerivAtFilter, hasDerivAtFilter
-/
theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' (L' ×ˢ pure u) := h.hasDerivAtFilter

/--
theorem `HasDerivAtFilter.hasGradientAtFilter'` / 定理 `HasDerivAtFilter.hasGradientAtFilter'`

English:
theorem HasDerivAtFilter.hasGradientAtFilter'
  given: (h : HasDerivAtFilter g g' (L' ×ˢ pure u))
  proof: h.hasGradientAtFilter

中文:
定理 HasDerivAtFilter.hasGradientAtFilter'
  条件: (h : HasDerivAtFilter g g' (L' ×ˢ pure u))
  证明: h.hasGradientAtFilter

Depends on / 依赖: h.hasGradientAtFilter, hasGradientAtFilter
-/
theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter

/--
theorem `HasGradientAt.hasDerivAt'` / 定理 `HasGradientAt.hasDerivAt'`

English:
theorem HasGradientAt.hasDerivAt'
  given: (h : HasGradientAt g g' u)
  proof: h.hasDerivAt

中文:
定理 HasGradientAt.hasDerivAt'
  条件: (h : HasGradientAt g g' u)
  证明: h.hasDerivAt

Depends on / 依赖: h.hasDerivAt, hasDerivAt
-/
theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt

/--
theorem `HasDerivAt.hasGradientAt'` / 定理 `HasDerivAt.hasGradientAt'`

English:
theorem HasDerivAt.hasGradientAt'
  given: (h : HasDerivAt g g' u)
  proof: h.hasGradientAt

中文:
定理 HasDerivAt.hasGradientAt'
  条件: (h : HasDerivAt g g' u)
  证明: h.hasGradientAt

Depends on / 依赖: h.hasGradientAt, hasGradientAt
-/
theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt

/--
theorem `gradient_eq_deriv'` / 定理 `gradient_eq_deriv'`

English:
theorem gradient_eq_deriv'
  statement: ∇ g u = deriv g u
  proof: gradient_eq_deriv

中文:
定理 gradient_eq_deriv'
  结论: ∇ g u = deriv g u
  证明: gradient_eq_deriv

Depends on / 依赖: gradient_eq_deriv
-/
theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv

end OneDimensionReal

open Filter

section GradientProperties

/--
theorem `hasGradientAtFilter_iff_isLittleO` / 定理 `hasGradientAtFilter_iff_isLittleO`

English:
theorem hasGradientAtFilter_iff_isLittleO
  proof: hasFDerivAtFilter_iff_isLittleO.trans by simp [Function.comp_def]

中文:
定理 hasGradientAtFilter_iff_isLittleO
  证明: hasFDerivAtFilter_iff_isLittleO.trans by simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, hasFDerivAtFilter_iff_isLittleO, hasFDerivAtFilter_iff_isLittleO.trans
-/
theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x :=
hasFDerivAtFilter_iff_isLittleO.trans by simp [Function.comp_def]

/--
theorem `hasGradientWithinAt_iff_isLittleO` / 定理 `hasGradientWithinAt_iff_isLittleO`

English:
theorem hasGradientWithinAt_iff_isLittleO
  proof: hasGradientAtFilter_iff_isLittleO

中文:
定理 hasGradientWithinAt_iff_isLittleO
  证明: hasGradientAtFilter_iff_isLittleO

Depends on / 依赖: hasGradientAtFilter_iff_isLittleO
-/
theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

/--
theorem `hasGradientWithinAt_iff_tendsto` / 定理 `hasGradientWithinAt_iff_tendsto`

English:
theorem hasGradientWithinAt_iff_tendsto
  proof: hasFDerivWithinAt_iff_tendsto

中文:
定理 hasGradientWithinAt_iff_tendsto
  证明: hasFDerivWithinAt_iff_tendsto

Depends on / 依赖: hasFDerivWithinAt_iff_tendsto
-/
theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

/--
theorem `hasGradientAt_iff_isLittleO` / 定理 `hasGradientAt_iff_isLittleO`

English:
theorem hasGradientAt_iff_isLittleO
  statement: HasGradientAt f f' x ↔
  proof: hasGradientAtFilter_iff_isLittleO

中文:
定理 hasGradientAt_iff_isLittleO
  结论: HasGradientAt f f' x ↔
  证明: hasGradientAtFilter_iff_isLittleO

Depends on / 依赖: hasGradientAtFilter_iff_isLittleO
-/
theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

/--
theorem `hasGradientAt_iff_tendsto` / 定理 `hasGradientAt_iff_tendsto`

English:
theorem hasGradientAt_iff_tendsto
  proof: hasFDerivAt_iff_tendsto

中文:
定理 hasGradientAt_iff_tendsto
  证明: hasFDerivAt_iff_tendsto

Depends on / 依赖: hasFDerivAt_iff_tendsto
-/
theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

/--
theorem `HasGradientAtFilter.isBigO_sub` / 定理 `HasGradientAtFilter.isBigO_sub`

English:
theorem HasGradientAtFilter.isBigO_sub
  given: (h : HasGradientAtFilter f f' x L)
  proof: .comp_tendsto prod_pure.ge HasFDerivAtFilter.isBigO_sub h

中文:
定理 HasGradientAtFilter.isBigO_sub
  条件: (h : HasGradientAtFilter f f' x L)
  证明: .comp_tendsto prod_pure.ge HasFDerivAtFilter.isBigO_sub h

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.isBigO_sub, comp_tendsto, isBigO_sub, prod_pure, prod_pure.ge
-/
theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
.comp_tendsto prod_pure.ge HasFDerivAtFilter.isBigO_sub h

/--
theorem `hasGradientWithinAt_congr_set'` / 定理 `hasGradientWithinAt_congr_set'`

English:
theorem hasGradientWithinAt_congr_set'
  given: {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: hasFDerivWithinAt_congr_set' y h

中文:
定理 hasGradientWithinAt_congr_set'
  条件: {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: hasFDerivWithinAt_congr_set' y h

Depends on / 依赖: hasFDerivWithinAt_congr_set
-/
theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

/--
theorem `hasGradientWithinAt_congr_set` / 定理 `hasGradientWithinAt_congr_set`

English:
theorem hasGradientWithinAt_congr_set
  given: {s t : Set F} (h : s =ᶠ[𝓝 x] t)
  proof: hasFDerivWithinAt_congr_set h

中文:
定理 hasGradientWithinAt_congr_set
  条件: {s t : Set F} (h : s =ᶠ[𝓝 x] t)
  证明: hasFDerivWithinAt_congr_set h

Depends on / 依赖: hasFDerivWithinAt_congr_set
-/
theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

/--
theorem `hasGradientAt_iff_isLittleO_nhds_zero` / 定理 `hasGradientAt_iff_isLittleO_nhds_zero`

English:
theorem hasGradientAt_iff_isLittleO_nhds_zero
  statement: HasGradientAt f f' x ↔
  proof: hasFDerivAt_iff_isLittleO_nhds_zero

中文:
定理 hasGradientAt_iff_isLittleO_nhds_zero
  结论: HasGradientAt f f' x ↔
  证明: hasFDerivAt_iff_isLittleO_nhds_zero

Depends on / 依赖: hasFDerivAt_iff_isLittleO_nhds_zero
-/
theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties

section Inner

/--
lemma `HasGradientWithinAt.fderivWithin_apply` / 引理 `HasGradientWithinAt.fderivWithin_apply`

English:
lemma HasGradientWithinAt.fderivWithin_apply
  proof: by
  rw [h.hasFDerivWithinAt.fderivWithin hs]; rw [toDual_apply_apply]

中文:
引理 HasGradientWithinAt.fderivWithin_apply
  证明: by
  rw [h.hasFDerivWithinAt.fderivWithin hs]; rw [toDual_apply_apply]

Depends on / 依赖: fderivWithin, h.hasFDerivWithinAt.fderivWithin, hasFDerivWithinAt, toDual_apply_apply
-/
lemma HasGradientWithinAt.fderivWithin_apply
    (h : HasGradientWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x y = ⟪f', y⟫ := by
  rw [h.hasFDerivWithinAt.fderivWithin hs]; rw [toDual_apply_apply]

/--
lemma `HasGradientAt.fderiv_apply` / 引理 `HasGradientAt.fderiv_apply`

English:
lemma HasGradientAt.fderiv_apply
  given: (h : HasGradientAt f f' x)
  statement: fderiv 𝕜 f x y = ⟪f', y⟫
  proof: by
  rw [h.hasFDerivAt.fderiv]; rw [toDual_apply_apply]

@[simp]

中文:
引理 HasGradientAt.fderiv_apply
  条件: (h : HasGradientAt f f' x)
  结论: fderiv 𝕜 f x y = ⟪f', y⟫
  证明: by
  rw [h.hasFDerivAt.fderiv]; rw [toDual_apply_apply]

@[simp]

Depends on / 依赖: fderiv, h.hasFDerivAt.fderiv, hasFDerivAt, toDual_apply_apply
-/
lemma HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) : fderiv 𝕜 f x y = ⟪f', y⟫ := by
  rw [h.hasFDerivAt.fderiv]; rw [toDual_apply_apply]

@[simp]
/--
lemma `inner_gradientWithin_left` / 引理 `inner_gradientWithin_left`

English:
lemma inner_gradientWithin_left
  proof: by
  rw [gradientWithin]; rw [← toDual_apply_apply (𝕜 := 𝕜) (E := F)]; rw [LinearIsometryEquiv.apply_symm_apply]

@[simp]

中文:
引理 inner_gradientWithin_left
  证明: by
  rw [gradientWithin]; rw [← toDual_apply_apply (𝕜 := 𝕜) (E := F)]; rw [LinearIsometryEquiv.apply_symm_apply]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply, apply_symm_apply, gradientWithin, toDual_apply_apply
-/
lemma inner_gradientWithin_left :
    ⟪gradientWithin f s x, y⟫ = fderivWithin 𝕜 f s x y := by
  rw [gradientWithin]; rw [← toDual_apply_apply (𝕜 := 𝕜) (E := F)]; rw [LinearIsometryEquiv.apply_symm_apply]

@[simp]
/--
lemma `inner_gradient_left` / 引理 `inner_gradient_left`

English:
lemma inner_gradient_left
  statement: ⟪∇ f x, y⟫ = fderiv 𝕜 f x y
  proof: by
  simp [← gradientWithin_univ]

@[simp]

中文:
引理 inner_gradient_left
  结论: ⟪∇ f x, y⟫ = fderiv 𝕜 f x y
  证明: by
  simp [← gradientWithin_univ]

@[simp]

Depends on / 依赖: gradientWithin_univ
-/
lemma inner_gradient_left : ⟪∇ f x, y⟫ = fderiv 𝕜 f x y := by
  simp [← gradientWithin_univ]

@[simp]
/--
lemma `inner_gradientWithin_right` / 引理 `inner_gradientWithin_right`

English:
lemma inner_gradientWithin_right
  proof: by
  rw [← inner_conj_symm]; rw [inner_gradientWithin_left]

@[simp]

中文:
引理 inner_gradientWithin_right
  证明: by
  rw [← inner_conj_symm]; rw [inner_gradientWithin_left]

@[simp]

Depends on / 依赖: inner_conj_symm, inner_gradientWithin_left
-/
lemma inner_gradientWithin_right :
    ⟪x, gradientWithin f s y⟫ = conj (fderivWithin 𝕜 f s y x) := by
  rw [← inner_conj_symm]; rw [inner_gradientWithin_left]

@[simp]
/--
lemma `inner_gradient_right` / 引理 `inner_gradient_right`

English:
lemma inner_gradient_right
  statement: ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x)
  proof: by
  rw [← inner_conj_symm]; rw [inner_gradient_left]

中文:
引理 inner_gradient_right
  结论: ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x)
  证明: by
  rw [← inner_conj_symm]; rw [inner_gradient_left]

Depends on / 依赖: inner_conj_symm, inner_gradient_left
-/
lemma inner_gradient_right : ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x) := by
  rw [← inner_conj_symm]; rw [inner_gradient_left]

end Inner

section congr

/-! ### Congruence properties of the Gradient -/

variable {f₀ f₁ : F -> 𝕜} {f₀' f₁' : F} {t : Set F}

/--
theorem `Filter.EventuallyEq.hasGradientAtFilter_iff` / 定理 `Filter.EventuallyEq.hasGradientAtFilter_iff`

English:
theorem Filter.EventuallyEq.hasGradientAtFilter_iff
  statement: (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
  proof: (h₀.prodMap <| by assumption).hasFDerivAtFilter_iff by simp [h₁]

中文:
定理 Filter.EventuallyEq.hasGradientAtFilter_iff
  结论: (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
  证明: (h₀.prodMap <| by assumption).hasFDerivAtFilter_iff by simp [h₁]

Depends on / 依赖: hasFDerivAtFilter_iff, prodMap
-/
theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
(h₀.prodMap <| by assumption).hasFDerivAtFilter_iff by simp [h₁]

/--
theorem `HasGradientAtFilter.congr_of_eventuallyEq` / 定理 `HasGradientAtFilter.congr_of_eventuallyEq`

English:
theorem HasGradientAtFilter.congr_of_eventuallyEq
  statement: (h : HasGradientAtFilter f f' x L)
  proof: by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

中文:
定理 HasGradientAtFilter.congr_of_eventuallyEq
  结论: (h : HasGradientAtFilter f f' x L)
  证明: by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

Depends on / 依赖: hL.hasGradientAtFilter_iff, hasGradientAtFilter_iff
-/
theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

/--
theorem `HasGradientWithinAt.congr_mono` / 定理 `HasGradientWithinAt.congr_mono`

English:
theorem HasGradientWithinAt.congr_mono
  statement: (h : HasGradientWithinAt f f' s x) (ht : forall x in t, f₁ x = f x)
  proof: HasFDerivWithinAt.congr_mono h ht hx h₁

中文:
定理 HasGradientWithinAt.congr_mono
  结论: (h : HasGradientWithinAt f f' s x) (ht : 对任意 x in t, f₁ x = f x)
  证明: HasFDerivWithinAt.congr_mono h ht hx h₁

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.congr_mono, congr_mono
-/
theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : forall x in t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t subseteq s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

/--
theorem `HasGradientWithinAt.congr` / 定理 `HasGradientWithinAt.congr`

English:
theorem HasGradientWithinAt.congr
  statement: (h : HasGradientWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
  proof: h.congr_mono hs hx (by tauto)

中文:
定理 HasGradientWithinAt.congr
  结论: (h : HasGradientWithinAt f f' s x) (hs : 对任意 x in s, f₁ x = f x)
  证明: h.congr_mono hs hx (by tauto)

Depends on / 依赖: congr_mono, h.congr_mono
-/
theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : forall x in s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)

/--
theorem `HasGradientWithinAt.congr_of_mem` / 定理 `HasGradientWithinAt.congr_of_mem`

English:
theorem HasGradientWithinAt.congr_of_mem
  statement: (h : HasGradientWithinAt f f' s x)
  proof: h.congr hs (hs _ hx)

中文:
定理 HasGradientWithinAt.congr_of_mem
  结论: (h : HasGradientWithinAt f f' s x)
  证明: h.congr hs (hs _ hx)

Depends on / 依赖: h.congr
-/
theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : forall x in s, f₁ x = f x) (hx : x in s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

/--
theorem `HasGradientWithinAt.congr_of_eventuallyEq` / 定理 `HasGradientWithinAt.congr_of_eventuallyEq`

English:
theorem HasGradientWithinAt.congr_of_eventuallyEq
  statement: (h : HasGradientWithinAt f f' s x)
  proof: HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

中文:
定理 HasGradientWithinAt.congr_of_eventuallyEq
  结论: (h : HasGradientWithinAt f f' s x)
  证明: HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

Depends on / 依赖: HasGradientAtFilter, HasGradientAtFilter.congr_of_eventuallyEq, congr_of_eventuallyEq
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

/--
theorem `HasGradientWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `HasGradientWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem
  statement: (h : HasGradientWithinAt f f' s x)
  proof: h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

中文:
定理 HasGradientWithinAt.congr_of_eventuallyEq_of_mem
  结论: (h : HasGradientWithinAt f f' s x)
  证明: h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

Depends on / 依赖: congr_of_eventuallyEq, eq_of_nhdsWithin, h.congr_of_eventuallyEq
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

/--
theorem `HasGradientAt.congr_of_eventuallyEq` / 定理 `HasGradientAt.congr_of_eventuallyEq`

English:
theorem HasGradientAt.congr_of_eventuallyEq
  given: (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

中文:
定理 HasGradientAt.congr_of_eventuallyEq
  条件: (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

Depends on / 依赖: HasGradientAtFilter, HasGradientAtFilter.congr_of_eventuallyEq, congr_of_eventuallyEq, mem_of_mem_nhds
-/
theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

/--
theorem `Filter.EventuallyEq.gradient_eq` / 定理 `Filter.EventuallyEq.gradient_eq`

English:
theorem Filter.EventuallyEq.gradient_eq
  given: (hL : f₁ =ᶠ[𝓝 x] f)
  statement: ∇ f₁ x = ∇ f x
  proof: by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

中文:
定理 Filter.EventuallyEq.gradient_eq
  条件: (hL : f₁ =ᶠ[𝓝 x] f)
  结论: ∇ f₁ x = ∇ f x
  证明: by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.fderiv_eq, fderiv_eq, gradient
-/
theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

/--
theorem `Filter.EventuallyEq.gradient` / 定理 `Filter.EventuallyEq.gradient`

English:
theorem Filter.EventuallyEq.gradient
  given: (h : f₁ =ᶠ[𝓝 x] f)
  statement: ∇ f₁ =ᶠ[𝓝 x] ∇ f
  proof: h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

中文:
定理 Filter.EventuallyEq.gradient
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  结论: ∇ f₁ =ᶠ[𝓝 x] ∇ f
  证明: h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq
-/
protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr

/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

/--
theorem `hasGradientAtFilter_const` / 定理 `hasGradientAtFilter_const`

English:
theorem hasGradientAtFilter_const
  statement: HasGradientAtFilter (fun _ => c) 0 x L
  proof: by
  rw [HasGradientAtFilter]; rw [map_zero]; exact hasFDerivAtFilter_const c _

中文:
定理 hasGradientAtFilter_const
  结论: HasGradientAtFilter (fun _ => c) 0 x L
  证明: by
  rw [HasGradientAtFilter]; rw [map_zero]; exact hasFDerivAtFilter_const c _

Depends on / 依赖: HasGradientAtFilter, hasFDerivAtFilter_const, map_zero
-/
theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter]; rw [map_zero]; exact hasFDerivAtFilter_const c _

/--
theorem `hasGradientWithinAt_const` / 定理 `hasGradientWithinAt_const`

English:
theorem hasGradientWithinAt_const
  statement: HasGradientWithinAt (fun _ => c) 0 s x
  proof: hasGradientAtFilter_const _ _ _

中文:
定理 hasGradientWithinAt_const
  结论: HasGradientWithinAt (fun _ => c) 0 s x
  证明: hasGradientAtFilter_const _ _ _

Depends on / 依赖: hasGradientAtFilter_const
-/
theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _

/--
theorem `hasGradientAt_const` / 定理 `hasGradientAt_const`

English:
theorem hasGradientAt_const
  statement: HasGradientAt (fun _ => c) 0 x
  proof: hasGradientAtFilter_const _ _ _

中文:
定理 hasGradientAt_const
  结论: HasGradientAt (fun _ => c) 0 x
  证明: hasGradientAtFilter_const _ _ _

Depends on / 依赖: hasGradientAtFilter_const
-/
theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x :=
  hasGradientAtFilter_const _ _ _

/--
theorem `gradient_fun_const` / 定理 `gradient_fun_const`

English:
theorem gradient_fun_const
  statement: ∇ (fun _ => c) x = 0
  proof: by simp [gradient]

中文:
定理 gradient_fun_const
  结论: ∇ (fun _ => c) x = 0
  证明: by simp [gradient]

Depends on / 依赖: gradient
-/
theorem gradient_fun_const : ∇ (fun _ => c) x = 0 := by simp [gradient]

/--
theorem `gradient_const` / 定理 `gradient_const`

English:
theorem gradient_const
  statement: ∇ (const F c) x = 0
  proof: gradient_fun_const x c

@[simp]

中文:
定理 gradient_const
  结论: ∇ (const F c) x = 0
  证明: gradient_fun_const x c

@[simp]

Depends on / 依赖: gradient_fun_const
-/
theorem gradient_const : ∇ (const F c) x = 0 := gradient_fun_const x c

@[simp]
/--
theorem `gradient_fun_const'` / 定理 `gradient_fun_const'`

English:
theorem gradient_fun_const'
  statement: (∇ fun _ : F => c) = fun _ => 0
  proof: funext fun x => gradient_const x c

@[simp]

中文:
定理 gradient_fun_const'
  结论: (∇ fun _ : F => c) = fun _ => 0
  证明: funext fun x => gradient_const x c

@[simp]

Depends on / 依赖: gradient_const
-/
theorem gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0 :=
  funext fun x => gradient_const x c

@[simp]
/--
theorem `gradient_const'` / 定理 `gradient_const'`

English:
theorem gradient_const'
  statement: ∇ (const F c) = 0
  proof: gradient_fun_const' c

中文:
定理 gradient_const'
  结论: ∇ (const F c) = 0
  证明: gradient_fun_const' c

Depends on / 依赖: gradient_fun_const
-/
theorem gradient_const' : ∇ (const F c) = 0 := gradient_fun_const' c

end Const

section Continuous

/-! ### Continuity of a function admitting a gradient -/

nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L <= 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL

/--
theorem `HasGradientWithinAt.continuousWithinAt` / 定理 `HasGradientWithinAt.continuousWithinAt`

English:
theorem HasGradientWithinAt.continuousWithinAt
  given: (h : HasGradientWithinAt f f' s x)
  proof: HasGradientAtFilter.tendsto_nhds inf_le_left h

中文:
定理 HasGradientWithinAt.continuousWithinAt
  条件: (h : HasGradientWithinAt f f' s x)
  证明: HasGradientAtFilter.tendsto_nhds inf_le_left h

Depends on / 依赖: HasGradientAtFilter, HasGradientAtFilter.tendsto_nhds, inf_le_left, tendsto_nhds
-/
theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h

/--
theorem `HasGradientAt.continuousAt` / 定理 `HasGradientAt.continuousAt`

English:
theorem HasGradientAt.continuousAt
  given: (h : HasGradientAt f f' x)
  statement: ContinuousAt f x
  proof: HasGradientAtFilter.tendsto_nhds le_rfl h

中文:
定理 HasGradientAt.continuousAt
  条件: (h : HasGradientAt f f' x)
  结论: ContinuousAt f x
  证明: HasGradientAtFilter.tendsto_nhds le_rfl h

Depends on / 依赖: HasGradientAtFilter, HasGradientAtFilter.tendsto_nhds, le_rfl, tendsto_nhds
-/
theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h

/--
theorem `HasGradientAt.continuousOn` / 定理 `HasGradientAt.continuousOn`

English:
theorem HasGradientAt.continuousOn
  given: {f' : F -> F} (h : forall x in s, HasGradientAt f (f' x) x)
  proof: fun x hx => (h x hx).continuousAt.continuousWithinAt

中文:
定理 HasGradientAt.continuousOn
  条件: {f' : F -> F} (h : 对任意 x in s, HasGradientAt f (f' x) x)
  证明: fun x hx => (h x hx).continuousAt.continuousWithinAt
-/
protected theorem HasGradientAt.continuousOn {f' : F -> F} (h : forall x in s, HasGradientAt f (f' x) x) :
    ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

end Continuous
