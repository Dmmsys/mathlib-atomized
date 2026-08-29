/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives of functions taking values in product types

In this file we prove lemmas about derivatives of functions `f : 𝕜 → E × F` and of functions
`f : 𝕜 → (Π i, E i)`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative
-/

public section

universe u v w

open Topology Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f₁ : 𝕜 -> F} {f₁' : F} {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f₂ : 𝕜 -> G} {f₂' : G}

/--
theorem `HasDerivAtFilter.prodMk` / 定理 `HasDerivAtFilter.prodMk`

English:
theorem HasDerivAtFilter.prodMk
  statement: (hf₁ : HasDerivAtFilter f₁ f₁' L)
  proof: HasFDerivAtFilter.prodMk hf₁ hf₂

中文:
定理 HasDerivAtFilter.prodMk
  结论: (hf₁ : HasDerivAtFilter f₁ f₁' L)
  证明: HasFDerivAtFilter.prodMk hf₁ hf₂

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.prodMk, prodMk
-/
theorem HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' L)
    (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') L :=
  HasFDerivAtFilter.prodMk hf₁ hf₂

/--
theorem `HasDerivWithinAt.prodMk` / 定理 `HasDerivWithinAt.prodMk`

English:
theorem HasDerivWithinAt.prodMk
  statement: (hf₁ : HasDerivWithinAt f₁ f₁' s x)
  proof: HasDerivAtFilter.prodMk hf₁ hf₂

中文:
定理 HasDerivWithinAt.prodMk
  结论: (hf₁ : HasDerivWithinAt f₁ f₁' s x)
  证明: HasDerivAtFilter.prodMk hf₁ hf₂

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.prodMk, prodMk
-/
theorem HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

/--
theorem `HasDerivAt.prodMk` / 定理 `HasDerivAt.prodMk`

English:
theorem HasDerivAt.prodMk
  given: (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x)
  proof: HasDerivAtFilter.prodMk hf₁ hf₂

中文:
定理 在点处可导.prodMk
  条件: (hf₁ : 在点处可导 f₁ f₁' x) (hf₂ : 在点处可导 f₂ f₂' x)
  证明: HasDerivAtFilter.prodMk hf₁ hf₂

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.prodMk, prodMk
-/
theorem HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

/--
theorem `HasStrictDerivAt.prodMk` / 定理 `HasStrictDerivAt.prodMk`

English:
theorem HasStrictDerivAt.prodMk
  statement: (hf₁ : HasStrictDerivAt f₁ f₁' x)
  proof: HasDerivAtFilter.prodMk hf₁ hf₂

中文:
定理 HasStrictDerivAt.prodMk
  结论: (hf₁ : HasStrictDerivAt f₁ f₁' x)
  证明: HasDerivAtFilter.prodMk hf₁ hf₂

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.prodMk, prodMk
-/
theorem HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x)
    (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

end CartesianProduct

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variable {ι : Type*} {E' : ι -> Type*} [forall i, NormedAddCommGroup (E' i)]
  [forall i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 -> forall i, E' i} {φ' : forall i, E' i}

@[simp]
/--
theorem `hasDerivAtFilter_pi` / 定理 `hasDerivAtFilter_pi`

English:
theorem hasDerivAtFilter_pi
  proof: hasFDerivAtFilter_pi'

@[simp]

中文:
定理 hasDerivAtFilter_pi
  证明: hasFDerivAtFilter_pi'

@[simp]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasDerivAtFilter_pi :
    HasDerivAtFilter φ φ' L ↔ forall i, HasDerivAtFilter (fun x => φ x i) (φ' i) L :=
  hasFDerivAtFilter_pi'

@[simp]
/--
theorem `hasStrictDerivAt_pi` / 定理 `hasStrictDerivAt_pi`

English:
theorem hasStrictDerivAt_pi
  proof: hasDerivAtFilter_pi

中文:
定理 hasStrictDerivAt_pi
  证明: hasDerivAtFilter_pi

Depends on / 依赖: hasDerivAtFilter_pi
-/
theorem hasStrictDerivAt_pi :
    HasStrictDerivAt φ φ' x ↔ forall i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi

/--
theorem `hasDerivAt_pi` / 定理 `hasDerivAt_pi`

English:
theorem hasDerivAt_pi
  statement: HasDerivAt φ φ' x ↔ forall i, HasDerivAt (fun x => φ x i) (φ' i) x
  proof: hasDerivAtFilter_pi

中文:
定理 hasDerivAt_pi
  结论: 在点处可导 φ φ' x ↔ 对任意 i, 在点处可导 (fun x => φ x i) (φ' i) x
  证明: hasDerivAtFilter_pi

Depends on / 依赖: hasDerivAtFilter_pi
-/
theorem hasDerivAt_pi : HasDerivAt φ φ' x ↔ forall i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi

/--
theorem `hasDerivWithinAt_pi` / 定理 `hasDerivWithinAt_pi`

English:
theorem hasDerivWithinAt_pi
  proof: hasDerivAtFilter_pi

中文:
定理 hasDerivWithinAt_pi
  证明: hasDerivAtFilter_pi

Depends on / 依赖: hasDerivAtFilter_pi
-/
theorem hasDerivWithinAt_pi :
    HasDerivWithinAt φ φ' s x ↔ forall i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  hasDerivAtFilter_pi

/--
theorem `derivWithin_pi` / 定理 `derivWithin_pi`

English:
theorem derivWithin_pi
  given: (h : forall i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · rw [derivWithin, fderivWithin_pi h hsx]
    simp [derivWithin]
    -- TODO: restore exact (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hsx
  · rw [uniqueDiffWithinAt_iff_accPt] at hsx
    simp [derivWithin, fderivWithin_zero_of_not_accPt hsx, Pi.zero_def]
    -- TODO: restore simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hsx, Pi.zero_def]

中文:
定理 derivWithin_pi
  条件: (h : 对任意 i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · rw [derivWithin, fderivWithin_pi h hsx]
    simp [derivWithin]
    -- TODO: restore exact (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hsx
  · rw [uniqueDiffWithinAt_iff_accPt] at hsx
    simp [derivWithin, fderivWithin_zero_of_not_accPt hsx, Pi.zero_def]
    -- TODO: restore simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hsx, Pi.zero_def]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, fderivWithin_pi
-/
theorem derivWithin_pi (h : forall i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · rw [derivWithin, fderivWithin_pi h hsx]
    simp [derivWithin]
    -- TODO: restore exact (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hsx
  · rw [uniqueDiffWithinAt_iff_accPt] at hsx
    simp [derivWithin, fderivWithin_zero_of_not_accPt hsx, Pi.zero_def]
    -- TODO: restore simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hsx, Pi.zero_def]

/--
theorem `deriv_pi` / 定理 `deriv_pi`

English:
theorem deriv_pi
  given: (h : forall i, DifferentiableAt 𝕜 (fun x => φ x i) x)
  proof: by
  -- TODO: restore (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv
  simp only [deriv, fderiv_pi h]
  simp

中文:
定理 deriv_pi
  条件: (h : 对任意 i, DifferentiableAt 𝕜 (fun x => φ x i) x)
  证明: by
  -- TODO: restore (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv
  simp only [deriv, fderiv_pi h]
  simp
-/
theorem deriv_pi (h : forall i, DifferentiableAt 𝕜 (fun x => φ x i) x) :
    deriv φ x = fun i => deriv (fun x => φ x i) x := by
  -- TODO: restore (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv
  simp only [deriv, fderiv_pi h]
  simp

end Pi


/-!
### Derivatives of tuples `f : 𝕜 → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ -> Type*}
variable [forall i, NormedAddCommGroup (F' i)] [forall i, NormedSpace 𝕜 (F' i)]
variable {φ : 𝕜 -> F' 0} {φs : 𝕜 -> forall i, F' (Fin.succ i)}

/--
theorem `hasStrictDerivAt_finCons` / 定理 `hasStrictDerivAt_finCons`

English:
theorem hasStrictDerivAt_finCons
  given: {φ' : Π i, F' i}
  proof: hasStrictFDerivAt_finCons

中文:
定理 hasStrictDerivAt_finCons
  条件: {φ' : Π i, F' i}
  证明: hasStrictFDerivAt_finCons

Depends on / 依赖: hasStrictFDerivAt_finCons
-/
theorem hasStrictDerivAt_finCons {φ' : Π i, F' i} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictDerivAt φ (φ' 0) x ∧ HasStrictDerivAt φs (fun i => φ' i.succ) x :=
  hasStrictFDerivAt_finCons

/--
theorem `hasStrictDerivAt_finCons'` / 定理 `hasStrictDerivAt_finCons'`

English:
theorem hasStrictDerivAt_finCons'
  given: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasStrictDerivAt_finCons

中文:
定理 hasStrictDerivAt_finCons'
  条件: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasStrictDerivAt_finCons

Depends on / 依赖: hasStrictDerivAt_finCons
-/
theorem hasStrictDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasStrictDerivAt φ φ' x ∧ HasStrictDerivAt φs φs' x :=
  hasStrictDerivAt_finCons

/--
theorem `HasStrictDerivAt.finCons` / 定理 `HasStrictDerivAt.finCons`

English:
theorem HasStrictDerivAt.finCons
  statement: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasStrictDerivAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 HasStrictDerivAt.finCons
  结论: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasStrictDerivAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasStrictDerivAt_finCons
-/
theorem HasStrictDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasStrictDerivAt φ φ' x) (hs : HasStrictDerivAt φs φs' x) :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasStrictDerivAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasDerivAtFilter_finCons` / 定理 `hasDerivAtFilter_finCons`

English:
theorem hasDerivAtFilter_finCons
  given: {φ' : Π i, F' i} {l : Filter (𝕜 × 𝕜)}
  proof: hasFDerivAtFilter_finCons

中文:
定理 hasDerivAtFilter_finCons
  条件: {φ' : Π i, F' i} {l : 滤子 (𝕜 × 𝕜)}
  证明: hasFDerivAtFilter_finCons

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasDerivAtFilter_finCons {φ' : Π i, F' i} {l : Filter (𝕜 × 𝕜)} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔
      HasDerivAtFilter φ (φ' 0) l ∧ HasDerivAtFilter φs (fun i => φ' i.succ) l :=
  hasFDerivAtFilter_finCons

/--
theorem `hasDerivAtFilter_finCons'` / 定理 `hasDerivAtFilter_finCons'`

English:
theorem hasDerivAtFilter_finCons'
  given: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)}
  proof: hasDerivAtFilter_finCons

中文:
定理 hasDerivAtFilter_finCons'
  条件: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)} {l : 滤子 (𝕜 × 𝕜)}
  证明: hasDerivAtFilter_finCons

Depends on / 依赖: hasDerivAtFilter_finCons
-/
theorem hasDerivAtFilter_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') l ↔
      HasDerivAtFilter φ φ' l ∧ HasDerivAtFilter φs φs' l :=
  hasDerivAtFilter_finCons

/--
theorem `HasDerivAtFilter.finCons` / 定理 `HasDerivAtFilter.finCons`

English:
theorem HasDerivAtFilter.finCons
  statement: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)}
  proof: hasDerivAtFilter_finCons'.mpr ⟨h, hs⟩

中文:
定理 HasDerivAtFilter.finCons
  结论: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)} {l : 滤子 (𝕜 × 𝕜)}
  证明: hasDerivAtFilter_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasDerivAtFilter_finCons
-/
theorem HasDerivAtFilter.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)}
    (h : HasDerivAtFilter φ φ' l) (hs : HasDerivAtFilter φs φs' l) :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') l :=
  hasDerivAtFilter_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasDerivAt_finCons` / 定理 `hasDerivAt_finCons`

English:
theorem hasDerivAt_finCons
  given: {φ' : Π i, F' i}
  proof: hasDerivAtFilter_finCons

中文:
定理 hasDerivAt_finCons
  条件: {φ' : Π i, F' i}
  证明: hasDerivAtFilter_finCons

Depends on / 依赖: hasDerivAtFilter_finCons
-/
theorem hasDerivAt_finCons {φ' : Π i, F' i} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasDerivAt φ (φ' 0) x ∧ HasDerivAt φs (fun i => φ' i.succ) x :=
  hasDerivAtFilter_finCons

/--
theorem `hasDerivAt_finCons'` / 定理 `hasDerivAt_finCons'`

English:
theorem hasDerivAt_finCons'
  given: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasDerivAt_finCons

中文:
定理 hasDerivAt_finCons'
  条件: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasDerivAt_finCons

Depends on / 依赖: hasDerivAt_finCons
-/
theorem hasDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasDerivAt φ φ' x ∧ HasDerivAt φs φs' x :=
  hasDerivAt_finCons

/--
theorem `HasDerivAt.finCons` / 定理 `HasDerivAt.finCons`

English:
theorem HasDerivAt.finCons
  statement: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasDerivAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 在点处可导.finCons
  结论: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasDerivAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasDerivAt_finCons
-/
theorem HasDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivAt φ φ' x) (hs : HasDerivAt φs φs' x) :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasDerivAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasDerivWithinAt_finCons` / 定理 `hasDerivWithinAt_finCons`

English:
theorem hasDerivWithinAt_finCons
  given: {φ' : Π i, F' i}
  proof: hasDerivAtFilter_finCons

中文:
定理 hasDerivWithinAt_finCons
  条件: {φ' : Π i, F' i}
  证明: hasDerivAtFilter_finCons

Depends on / 依赖: hasDerivAtFilter_finCons
-/
theorem hasDerivWithinAt_finCons {φ' : Π i, F' i} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasDerivWithinAt φ (φ' 0) s x ∧ HasDerivWithinAt φs (fun i => φ' i.succ) s x :=
  hasDerivAtFilter_finCons

/--
theorem `hasDerivWithinAt_finCons'` / 定理 `hasDerivWithinAt_finCons'`

English:
theorem hasDerivWithinAt_finCons'
  given: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasDerivAtFilter_finCons

中文:
定理 hasDerivWithinAt_finCons'
  条件: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasDerivAtFilter_finCons

Depends on / 依赖: hasDerivAtFilter_finCons
-/
theorem hasDerivWithinAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x ↔
      HasDerivWithinAt φ φ' s x ∧ HasDerivWithinAt φs φs' s x :=
  hasDerivAtFilter_finCons

/--
theorem `HasDerivWithinAt.finCons` / 定理 `HasDerivWithinAt.finCons`

English:
theorem HasDerivWithinAt.finCons
  statement: {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
  proof: hasDerivWithinAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 HasDerivWithinAt.finCons
  结论: {φ' : F' 0} {φs' : Π i, F' (有限集.succ i)}
  证明: hasDerivWithinAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasDerivWithinAt_finCons
-/
theorem HasDerivWithinAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivWithinAt φ φ' s x) (hs : HasDerivWithinAt φs φs' s x) :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x :=
  hasDerivWithinAt_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `derivWithin_pi` and `deriv_pi`

end PiFin
