/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Line derivatives

We define the line derivative of a function `f : E → F`, at a point `x : E` along a vector `v : E`,
as the element `f' : F` such that `f (x + t • v) = f x + t • f' + o (t)` as `t` tends to `0` in
the scalar field `𝕜`, if it exists. It is denoted by `lineDeriv 𝕜 f x v`.

This notion is generally less well behaved than the full Fréchet derivative (for instance, the
composition of functions which are line-differentiable is not line-differentiable in general).
The Fréchet derivative should therefore be favored over this one in general, although the line
derivative may sometimes prove handy.

The line derivative in direction `v` is also called the Gateaux derivative in direction `v`,
although the term "Gateaux derivative" is sometimes reserved for the situation where there is
such a derivative in all directions, for the map `v ↦ lineDeriv 𝕜 f x v` (which doesn't have to be
linear in general).

## Main definition and results

We mimic the definitions and statements for the Fréchet derivative and the one-dimensional
derivative. We define in particular the following objects:

* `LineDifferentiableWithinAt 𝕜 f s x v`
* `LineDifferentiableAt 𝕜 f x v`
* `HasLineDerivWithinAt 𝕜 f f' s x v`
* `HasLineDerivAt 𝕜 f s x v`
* `lineDerivWithin 𝕜 f s x v`
* `lineDeriv 𝕜 f x v`

and develop about them a basic API inspired by the one for the Fréchet derivative.

We depart from the Fréchet derivative in two places, as the dependence of the following predicates
on the direction would make them barely usable:
* We do not define an analogue of the predicate `UniqueDiffOn`;
* We do not define `LineDifferentiableOn` nor `LineDifferentiable`.
-/

@[expose] public section

noncomputable section

open scoped Topology Filter ENNReal NNReal

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module
/-!
Results that do not rely on a topological structure on `E`
-/

variable (𝕜)
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/--
Definition of `HasLineDerivWithinAt` / `HasLineDerivWithinAt` 的定义

English:
definition HasLineDerivWithinAt
  signature: (f : E -> F) (f' : F) (s : Set E) (x : E) (v : E)
  body: HasDerivWithinAt (fun t => f (x + t • v)) f' ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

中文:
定义 HasLineDerivWithinAt
  签名: (f : E -> F) (f' : F) (s : 集合 E) (x : E) (v : E)
  定义体: HasDerivWithinAt (fun t => f (x + t • v)) f' ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

Depends on / 依赖: HasDerivWithinAt
-/
def HasLineDerivWithinAt (f : E -> F) (f' : F) (s : Set E) (x : E) (v : E) :=
  HasDerivWithinAt (fun t => f (x + t • v)) f' ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

/--
Definition of `HasLineDerivAt` / `HasLineDerivAt` 的定义

English:
definition HasLineDerivAt
  signature: (f : E -> F) (f' : F) (x : E) (v : E)
  body: HasDerivAt (fun t => f (x + t • v)) f' (0 : 𝕜)

中文:
定义 HasLineDerivAt
  签名: (f : E -> F) (f' : F) (x : E) (v : E)
  定义体: HasDerivAt (fun t => f (x + t • v)) f' (0 : 𝕜)

Depends on / 依赖: HasDerivAt
-/
def HasLineDerivAt (f : E -> F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t => f (x + t • v)) f' (0 : 𝕜)

/--
Definition of `LineDifferentiableWithinAt` / `LineDifferentiableWithinAt` 的定义

English:
definition LineDifferentiableWithinAt
  signature: (f : E -> F) (s : Set E) (x : E) (v : E)
  body: DifferentiableWithinAt 𝕜 (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

中文:
定义 LineDifferentiableWithinAt
  签名: (f : E -> F) (s : 集合 E) (x : E) (v : E)
  定义体: DifferentiableWithinAt 𝕜 (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

Depends on / 依赖: DifferentiableWithinAt
-/
def LineDifferentiableWithinAt (f : E -> F) (s : Set E) (x : E) (v : E) : Prop :=
  DifferentiableWithinAt 𝕜 (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

/--
Definition of `LineDifferentiableAt` / `LineDifferentiableAt` 的定义

English:
definition LineDifferentiableAt
  signature: (f : E -> F) (x : E) (v : E)
  body: DifferentiableAt 𝕜 (fun t => f (x + t • v)) (0 : 𝕜)

中文:
定义 LineDifferentiableAt
  签名: (f : E -> F) (x : E) (v : E)
  定义体: DifferentiableAt 𝕜 (fun t => f (x + t • v)) (0 : 𝕜)

Depends on / 依赖: DifferentiableAt
-/
def LineDifferentiableAt (f : E -> F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t => f (x + t • v)) (0 : 𝕜)

/--
Definition of `lineDerivWithin` / `lineDerivWithin` 的定义

English:
definition lineDerivWithin
  signature: (f : E -> F) (s : Set E) (x : E) (v : E)
  body: derivWithin (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

中文:
定义 lineDerivWithin
  签名: (f : E -> F) (s : 集合 E) (x : E) (v : E)
  定义体: derivWithin (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

Depends on / 依赖: derivWithin
-/
def lineDerivWithin (f : E -> F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t => f (x + t • v)) ((fun t => x + t • v) ⁻¹' s) (0 : 𝕜)

/--
Definition of `lineDeriv` / `lineDeriv` 的定义

English:
definition lineDeriv
  signature: (f : E -> F) (x : E) (v : E)
  body: deriv (fun t => f (x + t • v)) (0 : 𝕜)

中文:
定义 lineDeriv
  签名: (f : E -> F) (x : E) (v : E)
  定义体: deriv (fun t => f (x + t • v)) (0 : 𝕜)
-/
def lineDeriv (f : E -> F) (x : E) (v : E) : F :=
  deriv (fun t => f (x + t • v)) (0 : 𝕜)

variable {𝕜}
variable {f f₁ : E -> F} {f' f₀' f₁' : F} {s t : Set E} {x v : E}

/--
lemma `HasLineDerivWithinAt.mono` / 引理 `HasLineDerivWithinAt.mono`

English:
lemma HasLineDerivWithinAt.mono
  given: (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t subseteq s)
  proof: HasDerivWithinAt.mono hf (preimage_mono hst)

中文:
引理 HasLineDerivWithinAt.mono
  条件: (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t subseteq s)
  证明: HasDerivWithinAt.mono hf (preimage_mono hst)

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.mono, preimage_mono
-/
lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t subseteq s) :
    HasLineDerivWithinAt 𝕜 f f' t x v :=
  HasDerivWithinAt.mono hf (preimage_mono hst)

/--
lemma `HasLineDerivAt.hasLineDerivWithinAt` / 引理 `HasLineDerivAt.hasLineDerivWithinAt`

English:
lemma HasLineDerivAt.hasLineDerivWithinAt
  given: (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E)
  proof: HasDerivAt.hasDerivWithinAt hf

中文:
引理 HasLineDerivAt.hasLineDerivWithinAt
  条件: (hf : HasLineDerivAt 𝕜 f f' x v) (s : 集合 E)
  证明: HasDerivAt.hasDerivWithinAt hf

Depends on / 依赖: HasDerivAt, HasDerivAt.hasDerivWithinAt, hasDerivWithinAt
-/
lemma HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E) :
    HasLineDerivWithinAt 𝕜 f f' s x v :=
  HasDerivAt.hasDerivWithinAt hf

/--
lemma `HasLineDerivWithinAt.lineDifferentiableWithinAt` / 引理 `HasLineDerivWithinAt.lineDifferentiableWithinAt`

English:
lemma HasLineDerivWithinAt.lineDifferentiableWithinAt
  given: (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
  proof: HasDerivWithinAt.differentiableWithinAt hf

中文:
引理 HasLineDerivWithinAt.lineDifferentiableWithinAt
  条件: (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
  证明: HasDerivWithinAt.differentiableWithinAt hf

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.differentiableWithinAt, differentiableWithinAt
-/
lemma HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  HasDerivWithinAt.differentiableWithinAt hf

/--
theorem `HasLineDerivAt.lineDifferentiableAt` / 定理 `HasLineDerivAt.lineDifferentiableAt`

English:
theorem HasLineDerivAt.lineDifferentiableAt
  given: (hf : HasLineDerivAt 𝕜 f f' x v)
  proof: HasDerivAt.differentiableAt hf

中文:
定理 HasLineDerivAt.lineDifferentiableAt
  条件: (hf : HasLineDerivAt 𝕜 f f' x v)
  证明: HasDerivAt.differentiableAt hf

Depends on / 依赖: HasDerivAt, HasDerivAt.differentiableAt, differentiableAt
-/
theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
    LineDifferentiableAt 𝕜 f x v :=
  HasDerivAt.differentiableAt hf

/--
theorem `LineDifferentiableWithinAt.hasLineDerivWithinAt` / 定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`

English:
theorem LineDifferentiableWithinAt.hasLineDerivWithinAt
  given: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: DifferentiableWithinAt.hasDerivWithinAt h

中文:
定理 LineDifferentiableWithinAt.hasLineDerivWithinAt
  条件: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: DifferentiableWithinAt.hasDerivWithinAt h

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasDerivWithinAt, Fintype, Matrix, hasDerivWithinAt
-/
theorem LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) :
    HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v :=
  DifferentiableWithinAt.hasDerivWithinAt h

/--
theorem `LineDifferentiableAt.hasLineDerivAt` / 定理 `LineDifferentiableAt.hasLineDerivAt`

English:
theorem LineDifferentiableAt.hasLineDerivAt
  given: (h : LineDifferentiableAt 𝕜 f x v)
  proof: DifferentiableAt.hasDerivAt h

中文:
定理 LineDifferentiableAt.hasLineDerivAt
  条件: (h : LineDifferentiableAt 𝕜 f x v)
  证明: DifferentiableAt.hasDerivAt h

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, Finite, Matrix, hasDerivAt
-/
theorem LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  DifferentiableAt.hasDerivAt h

/--
lemma `hasLineDerivWithinAt_univ` / 引理 `hasLineDerivWithinAt_univ`

English:
lemma hasLineDerivWithinAt_univ
  proof: by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]

中文:
引理 hasLineDerivWithinAt_univ
  证明: by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]
-/
@[simp] lemma hasLineDerivWithinAt_univ :
    HasLineDerivWithinAt 𝕜 f f' univ x v ↔ HasLineDerivAt 𝕜 f f' x v := by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]

/--
theorem `lineDerivWithin_zero_of_not_lineDifferentiableWithinAt` / 定理 `lineDerivWithin_zero_of_not_lineDifferentiableWithinAt`

English:
theorem lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
  proof: derivWithin_zero_of_not_differentiableWithinAt h

中文:
定理 lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
  证明: derivWithin_zero_of_not_differentiableWithinAt h

Depends on / 依赖: derivWithin_zero_of_not_differentiableWithinAt
-/
theorem lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
    (h : ¬LineDifferentiableWithinAt 𝕜 f s x v) :
    lineDerivWithin 𝕜 f s x v = 0 :=
  derivWithin_zero_of_not_differentiableWithinAt h

/--
theorem `lineDeriv_zero_of_not_lineDifferentiableAt` / 定理 `lineDeriv_zero_of_not_lineDifferentiableAt`

English:
theorem lineDeriv_zero_of_not_lineDifferentiableAt
  given: (h : ¬LineDifferentiableAt 𝕜 f x v)
  proof: deriv_zero_of_not_differentiableAt h

中文:
定理 lineDeriv_zero_of_not_lineDifferentiableAt
  条件: (h : ¬LineDifferentiableAt 𝕜 f x v)
  证明: deriv_zero_of_not_differentiableAt h

Depends on / 依赖: deriv_zero_of_not_differentiableAt
-/
theorem lineDeriv_zero_of_not_lineDifferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) :
    lineDeriv 𝕜 f x v = 0 :=
  deriv_zero_of_not_differentiableAt h

/--
theorem `hasLineDerivAt_iff_isLittleO_nhds_zero` / 定理 `hasLineDerivAt_iff_isLittleO_nhds_zero`

English:
theorem hasLineDerivAt_iff_isLittleO_nhds_zero
  proof: by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]

中文:
定理 hasLineDerivAt_iff_isLittleO_nhds_zero
  证明: by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]

Depends on / 依赖: HasLineDerivAt, add_zero, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul
-/
theorem hasLineDerivAt_iff_isLittleO_nhds_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      (fun t : 𝕜 => f (x + t • v) - f x - t • f') =o[𝓝 0] fun t => t := by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]

/--
theorem `HasLineDerivAt.unique` / 定理 `HasLineDerivAt.unique`

English:
theorem HasLineDerivAt.unique
  given: (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v)
  proof: HasDerivAt.unique h₀ h₁

中文:
定理 HasLineDerivAt.unique
  条件: (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v)
  证明: HasDerivAt.unique h₀ h₁

Depends on / 依赖: HasDerivAt, HasDerivAt.unique, unique
-/
theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
    f₀' = f₁' :=
  HasDerivAt.unique h₀ h₁

/--
theorem `HasLineDerivAt.lineDeriv` / 定理 `HasLineDerivAt.lineDeriv`

English:
theorem HasLineDerivAt.lineDeriv
  given: (h : HasLineDerivAt 𝕜 f f' x v)
  proof: by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]

中文:
定理 HasLineDerivAt.lineDeriv
  条件: (h : HasLineDerivAt 𝕜 f f' x v)
  证明: by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]
-/
protected theorem HasLineDerivAt.lineDeriv (h : HasLineDerivAt 𝕜 f f' x v) :
    lineDeriv 𝕜 f x v = f' := by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]

/--
theorem `lineDifferentiableWithinAt_univ` / 定理 `lineDifferentiableWithinAt_univ`

English:
theorem lineDifferentiableWithinAt_univ
  proof: by
  simp only [LineDifferentiableWithinAt, LineDifferentiableAt, preimage_univ,
    differentiableWithinAt_univ]

中文:
定理 lineDifferentiableWithinAt_univ
  证明: by
  simp only [LineDifferentiableWithinAt, LineDifferentiableAt, preimage_univ,
    differentiableWithinAt_univ]

Depends on / 依赖: LineDifferentiableAt, LineDifferentiableWithinAt, differentiableWithinAt_univ, preimage_univ
-/
theorem lineDifferentiableWithinAt_univ :
    LineDifferentiableWithinAt 𝕜 f univ x v ↔ LineDifferentiableAt 𝕜 f x v := by
  simp only [LineDifferentiableWithinAt, LineDifferentiableAt, preimage_univ,
    differentiableWithinAt_univ]

/--
theorem `LineDifferentiableAt.lineDifferentiableWithinAt` / 定理 `LineDifferentiableAt.lineDifferentiableWithinAt`

English:
theorem LineDifferentiableAt.lineDifferentiableWithinAt
  given: (h : LineDifferentiableAt 𝕜 f x v)
  proof: (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[simp]

中文:
定理 LineDifferentiableAt.lineDifferentiableWithinAt
  条件: (h : LineDifferentiableAt 𝕜 f x v)
  证明: (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[simp]

Depends on / 依赖: differentiableWithinAt_univ, subset_univ
-/
theorem LineDifferentiableAt.lineDifferentiableWithinAt (h : LineDifferentiableAt 𝕜 f x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[simp]
/--
theorem `lineDerivWithin_univ` / 定理 `lineDerivWithin_univ`

English:
theorem lineDerivWithin_univ
  statement: lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v
  proof: by
  simp [lineDerivWithin, lineDeriv]

中文:
定理 lineDerivWithin_univ
  结论: lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v
  证明: by
  simp [lineDerivWithin, lineDeriv]

Depends on / 依赖: lineDeriv, lineDerivWithin
-/
theorem lineDerivWithin_univ : lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v := by
  simp [lineDerivWithin, lineDeriv]

/--
theorem `LineDifferentiableWithinAt.mono` / 定理 `LineDifferentiableWithinAt.mono`

English:
theorem LineDifferentiableWithinAt.mono
  given: (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s subseteq t)
  proof: (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt

中文:
定理 LineDifferentiableWithinAt.mono
  条件: (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s subseteq t)
  证明: (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt

Depends on / 依赖: h.hasLineDerivWithinAt.mono, hasLineDerivWithinAt, lineDifferentiableWithinAt
-/
theorem LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s subseteq t) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt

/--
theorem `HasLineDerivWithinAt.congr_mono` / 定理 `HasLineDerivWithinAt.congr_mono`

English:
theorem HasLineDerivWithinAt.congr_mono
  statement: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t)
  proof: HasDerivWithinAt.congr_mono h (fun _ hy => ht hy) (by simpa using hx) (preimage_mono h₁)

中文:
定理 HasLineDerivWithinAt.congr_mono
  结论: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t)
  证明: HasDerivWithinAt.congr_mono h (fun _ hy => ht hy) (by simpa using hx) (preimage_mono h₁)

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.congr_mono, congr_mono, preimage_mono
-/
theorem HasLineDerivWithinAt.congr_mono (h : HasLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t subseteq s) : HasLineDerivWithinAt 𝕜 f₁ f' t x v :=
  HasDerivWithinAt.congr_mono h (fun _ hy => ht hy) (by simpa using hx) (preimage_mono h₁)

/--
theorem `HasLineDerivWithinAt.congr` / 定理 `HasLineDerivWithinAt.congr`

English:
theorem HasLineDerivWithinAt.congr
  statement: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s)
  proof: h.congr_mono hs hx (Subset.refl _)

中文:
定理 HasLineDerivWithinAt.congr
  结论: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s)
  证明: h.congr_mono hs hx (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, congr_mono, h.congr_mono
-/
theorem HasLineDerivWithinAt.congr (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr_mono hs hx (Subset.refl _)

/--
theorem `HasLineDerivWithinAt.congr'` / 定理 `HasLineDerivWithinAt.congr'`

English:
theorem HasLineDerivWithinAt.congr'
  statement: (h : HasLineDerivWithinAt 𝕜 f f' s x v)
  proof: h.congr hs (hs hx)

中文:
定理 HasLineDerivWithinAt.congr'
  结论: (h : HasLineDerivWithinAt 𝕜 f f' s x v)
  证明: h.congr hs (hs hx)

Depends on / 依赖: h.congr
-/
theorem HasLineDerivWithinAt.congr' (h : HasLineDerivWithinAt 𝕜 f f' s x v)
    (hs : EqOn f₁ f s) (hx : x in s) :
    HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr hs (hs hx)

/--
theorem `LineDifferentiableWithinAt.congr_mono` / 定理 `LineDifferentiableWithinAt.congr_mono`

English:
theorem LineDifferentiableWithinAt.congr_mono
  statement: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt

中文:
定理 LineDifferentiableWithinAt.congr_mono
  结论: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt

Depends on / 依赖: HasLineDerivWithinAt, HasLineDerivWithinAt.congr_mono, congr_mono, differentiableWithinAt, h.hasLineDerivWithinAt, hasLineDerivWithinAt
-/
theorem LineDifferentiableWithinAt.congr_mono (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t subseteq s) :
    LineDifferentiableWithinAt 𝕜 f₁ t x v :=
  (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt

/--
theorem `LineDifferentiableWithinAt.congr` / 定理 `LineDifferentiableWithinAt.congr`

English:
theorem LineDifferentiableWithinAt.congr
  statement: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

中文:
定理 LineDifferentiableWithinAt.congr
  结论: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

Depends on / 依赖: LineDifferentiableWithinAt, LineDifferentiableWithinAt.congr_mono, Subset, Subset.refl, congr_mono
-/
theorem LineDifferentiableWithinAt.congr (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) :
    LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

/--
theorem `lineDerivWithin_congr` / 定理 `lineDerivWithin_congr`

English:
theorem lineDerivWithin_congr
  given: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  proof: derivWithin_congr (fun _ hy => hs hy) (by simpa using hx)

中文:
定理 lineDerivWithin_congr
  条件: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  证明: derivWithin_congr (fun _ hy => hs hy) (by simpa using hx)

Depends on / 依赖: derivWithin_congr
-/
theorem lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  derivWithin_congr (fun _ hy => hs hy) (by simpa using hx)

/--
theorem `lineDerivWithin_congr'` / 定理 `lineDerivWithin_congr'`

English:
theorem lineDerivWithin_congr'
  given: (hs : EqOn f₁ f s) (hx : x in s)
  proof: lineDerivWithin_congr hs (hs hx)

中文:
定理 lineDerivWithin_congr'
  条件: (hs : EqOn f₁ f s) (hx : x in s)
  证明: lineDerivWithin_congr hs (hs hx)

Depends on / 依赖: lineDerivWithin_congr
-/
theorem lineDerivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  lineDerivWithin_congr hs (hs hx)

/--
theorem `hasLineDerivAt_iff_tendsto_slope_zero` / 定理 `hasLineDerivAt_iff_tendsto_slope_zero`

English:
theorem hasLineDerivAt_iff_tendsto_slope_zero
  proof: by
  simp only [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_zero, zero_add,
    zero_smul, add_zero]

alias ⟨HasLineDerivAt.tendsto_slope_zero, _⟩ := hasLineDerivAt_iff_tendsto_slope_zero

中文:
定理 hasLineDerivAt_iff_tendsto_slope_zero
  证明: by
  simp only [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_zero, zero_add,
    zero_smul, add_zero]

alias ⟨HasLineDerivAt.tendsto_slope_zero, _⟩ := hasLineDerivAt_iff_tendsto_slope_zero

Depends on / 依赖: HasLineDerivAt, add_zero, hasDerivAt_iff_tendsto_slope_zero, zero_add, zero_smul
-/
theorem hasLineDerivAt_iff_tendsto_slope_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      Tendsto (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[!=] 0) (𝓝 f') := by
  simp only [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_zero, zero_add,
    zero_smul, add_zero]

alias ⟨HasLineDerivAt.tendsto_slope_zero, _⟩ := hasLineDerivAt_iff_tendsto_slope_zero

/--
theorem `HasLineDerivAt.tendsto_slope_zero_right` / 定理 `HasLineDerivAt.tendsto_slope_zero_right`

English:
theorem HasLineDerivAt.tendsto_slope_zero_right
  given: [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v)
  proof: h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

中文:
定理 HasLineDerivAt.tendsto_slope_zero_right
  条件: [预序 𝕜] (h : HasLineDerivAt 𝕜 f f' x v)
  证明: h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

Depends on / 依赖: h.tendsto_slope_zero.mono_left, mono_left, nhdsGT_le_nhdsNE, tendsto_slope_zero
-/
theorem HasLineDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
    Tendsto (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[>] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

/--
theorem `HasLineDerivAt.tendsto_slope_zero_left` / 定理 `HasLineDerivAt.tendsto_slope_zero_left`

English:
theorem HasLineDerivAt.tendsto_slope_zero_left
  given: [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v)
  proof: h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

中文:
定理 HasLineDerivAt.tendsto_slope_zero_left
  条件: [预序 𝕜] (h : HasLineDerivAt 𝕜 f f' x v)
  证明: h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

Depends on / 依赖: h.tendsto_slope_zero.mono_left, mono_left, nhdsLT_le_nhdsNE, tendsto_slope_zero
-/
theorem HasLineDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
    Tendsto (fun (t : 𝕜) => t⁻¹ • (f (x + t • v) - f x)) (𝓝[<] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

/--
theorem `HasLineDerivWithinAt.hasLineDerivAt'` / 定理 `HasLineDerivWithinAt.hasLineDerivAt'`

English:
theorem HasLineDerivWithinAt.hasLineDerivAt'
  proof: h.hasDerivAt hs

中文:
定理 HasLineDerivWithinAt.hasLineDerivAt'
  证明: h.hasDerivAt hs

Depends on / 依赖: h.hasDerivAt, hasDerivAt
-/
theorem HasLineDerivWithinAt.hasLineDerivAt'
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : forallᶠ t : 𝕜 in 𝓝 0, x + t • v in s) :
    HasLineDerivAt 𝕜 f f' x v :=
  h.hasDerivAt hs

end Module

section NormedSpace

/-!
Results that need a normed space structure on `E`
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₀ f₁ : E -> F} {f' : F} {s t : Set E} {x v : E} {L : E ->L[𝕜] F}

/--
theorem `HasLineDerivWithinAt.mono_of_mem_nhdsWithin` / 定理 `HasLineDerivWithinAt.mono_of_mem_nhdsWithin`

English:
theorem HasLineDerivWithinAt.mono_of_mem_nhdsWithin
  proof: by
  apply HasDerivWithinAt.mono_of_mem_nhdsWithin h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; fun_prop

中文:
定理 HasLineDerivWithinAt.mono_of_mem_nhdsWithin
  证明: by
  apply HasDerivWithinAt.mono_of_mem_nhdsWithin h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; fun_prop

Depends on / 依赖: Continuous, Continuous.continuousWithinAt, ContinuousWithinAt, ContinuousWithinAt.preimage_mem_nhdsWithin, HasDerivWithinAt, HasDerivWithinAt.mono_of_mem_nhdsWithin, continuousWithinAt, fun_prop, mono_of_mem_nhdsWithin, preimage_mem_nhdsWithin
-/
theorem HasLineDerivWithinAt.mono_of_mem_nhdsWithin
    (h : HasLineDerivWithinAt 𝕜 f f' t x v) (hst : t in 𝓝[s] x) :
    HasLineDerivWithinAt 𝕜 f f' s x v := by
  apply HasDerivWithinAt.mono_of_mem_nhdsWithin h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; fun_prop

/--
theorem `HasLineDerivWithinAt.hasLineDerivAt` / 定理 `HasLineDerivWithinAt.hasLineDerivAt`

English:
theorem HasLineDerivWithinAt.hasLineDerivAt
  proof: h.hasLineDerivAt' (Continuous.tendsto' (by fun_prop) 0 _ (by simp)).eventually hs

中文:
定理 HasLineDerivWithinAt.hasLineDerivAt
  证明: h.hasLineDerivAt' (Continuous.tendsto' (by fun_prop) 0 _ (by simp)).eventually hs

Depends on / 依赖: Continuous, Continuous.tendsto, eventually, fun_prop, h.hasLineDerivAt, hasLineDerivAt, tendsto
-/
theorem HasLineDerivWithinAt.hasLineDerivAt
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : s in 𝓝 x) :
    HasLineDerivAt 𝕜 f f' x v :=
h.hasLineDerivAt' (Continuous.tendsto' (by fun_prop) 0 _ (by simp)).eventually hs

/--
theorem `LineDifferentiableWithinAt.lineDifferentiableAt` / 定理 `LineDifferentiableWithinAt.lineDifferentiableAt`

English:
theorem LineDifferentiableWithinAt.lineDifferentiableAt
  statement: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

中文:
定理 LineDifferentiableWithinAt.lineDifferentiableAt
  结论: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

Depends on / 依赖: h.hasLineDerivWithinAt.hasLineDerivAt, hasLineDerivAt, hasLineDerivWithinAt, lineDifferentiableAt
-/
theorem LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hs : s in 𝓝 x) : LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

/--
lemma `HasFDerivWithinAt.hasLineDerivWithinAt` / 引理 `HasFDerivWithinAt.hasLineDerivWithinAt`

English:
lemma HasFDerivWithinAt.hasLineDerivWithinAt
  given: (hf : HasFDerivWithinAt f L s x) (v : E)
  proof: by
  let F := fun (t : 𝕜) => x + t • v
  rw [show x = F (0 : 𝕜) by simp [F]] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

中文:
引理 HasFDerivWithinAt.hasLineDerivWithinAt
  条件: (hf : HasFDerivWithinAt f L s x) (v : E)
  证明: by
  let F := fun (t : 𝕜) => x + t • v
  rw [show x = F (0 : 𝕜) by simp [F]] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

Depends on / 依赖: HasDerivWithinAt, comp_hasDerivWithinAt, hasDerivAt_const, hasDerivAt_id, hasDerivWithinAt, hf.comp_hasDerivWithinAt, mapsTo_preimage, one_smul, smul_const, zero_add
-/
lemma HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) (v : E) :
    HasLineDerivWithinAt 𝕜 f (L v) s x v := by
  let F := fun (t : 𝕜) => x + t • v
  rw [show x = F (0 : 𝕜) by simp [F]] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

/--
theorem `DifferentiableWithinAt.lineDifferentiableWithinAt` / 定理 `DifferentiableWithinAt.lineDifferentiableWithinAt`

English:
theorem DifferentiableWithinAt.lineDifferentiableWithinAt
  proof: .lineDifferentiableWithinAt hf.hasFDerivWithinAt.hasLineDerivWithinAt _

中文:
定理 DifferentiableWithinAt.lineDifferentiableWithinAt
  证明: .lineDifferentiableWithinAt hf.hasFDerivWithinAt.hasLineDerivWithinAt _

Depends on / 依赖: hasFDerivWithinAt, hasLineDerivWithinAt, hf.hasFDerivWithinAt.hasLineDerivWithinAt, lineDifferentiableWithinAt
-/
theorem DifferentiableWithinAt.lineDifferentiableWithinAt
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
.lineDifferentiableWithinAt hf.hasFDerivWithinAt.hasLineDerivWithinAt _

/--
lemma `HasFDerivAt.hasLineDerivAt` / 引理 `HasFDerivAt.hasLineDerivAt`

English:
lemma HasFDerivAt.hasLineDerivAt
  given: (hf : HasFDerivAt f L x) (v : E)
  proof: by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt v

中文:
引理 在点处Fréchet可导.hasLineDerivAt
  条件: (hf : 在点处Fréchet可导 f L x) (v : E)
  证明: by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt v

Depends on / 依赖: hasFDerivWithinAt, hasLineDerivWithinAt, hasLineDerivWithinAt_univ, hf.hasFDerivWithinAt.hasLineDerivWithinAt
-/
lemma HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) (v : E) :
    HasLineDerivAt 𝕜 f (L v) x v := by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt v

/--
theorem `DifferentiableAt.lineDifferentiableAt` / 定理 `DifferentiableAt.lineDifferentiableAt`

English:
theorem DifferentiableAt.lineDifferentiableAt
  given: (hf : DifferentiableAt 𝕜 f x)
  proof: .lineDifferentiableAt hf.hasFDerivAt.hasLineDerivAt _

中文:
定理 DifferentiableAt.lineDifferentiableAt
  条件: (hf : DifferentiableAt 𝕜 f x)
  证明: .lineDifferentiableAt hf.hasFDerivAt.hasLineDerivAt _

Depends on / 依赖: hasFDerivAt, hasLineDerivAt, hf.hasFDerivAt.hasLineDerivAt, lineDifferentiableAt
-/
theorem DifferentiableAt.lineDifferentiableAt (hf : DifferentiableAt 𝕜 f x) :
    LineDifferentiableAt 𝕜 f x v :=
.lineDifferentiableAt hf.hasFDerivAt.hasLineDerivAt _

/--
lemma `DifferentiableAt.lineDeriv_eq_fderiv` / 引理 `DifferentiableAt.lineDeriv_eq_fderiv`

English:
lemma DifferentiableAt.lineDeriv_eq_fderiv
  given: (hf : DifferentiableAt 𝕜 f x)
  proof: (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv

中文:
引理 DifferentiableAt.lineDeriv_eq_fderiv
  条件: (hf : DifferentiableAt 𝕜 f x)
  证明: (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv

Depends on / 依赖: hasFDerivAt, hasLineDerivAt, hf.hasFDerivAt.hasLineDerivAt, lineDeriv
-/
lemma DifferentiableAt.lineDeriv_eq_fderiv (hf : DifferentiableAt 𝕜 f x) :
    lineDeriv 𝕜 f x v = fderiv 𝕜 f x v :=
  (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv

/--
theorem `LineDifferentiableWithinAt.mono_of_mem_nhdsWithin` / 定理 `LineDifferentiableWithinAt.mono_of_mem_nhdsWithin`

English:
theorem LineDifferentiableWithinAt.mono_of_mem_nhdsWithin
  statement: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: (h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin hst).lineDifferentiableWithinAt

中文:
定理 LineDifferentiableWithinAt.mono_of_mem_nhdsWithin
  结论: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: (h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin hst).lineDifferentiableWithinAt

Depends on / 依赖: h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin, hasLineDerivWithinAt, lineDifferentiableWithinAt, mono_of_mem_nhdsWithin
-/
theorem LineDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hst : s in 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v :=
  (h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin hst).lineDifferentiableWithinAt

/--
theorem `lineDerivWithin_of_mem_nhds` / 定理 `lineDerivWithin_of_mem_nhds`

English:
theorem lineDerivWithin_of_mem_nhds
  given: (h : s in 𝓝 x)
  proof: by
  apply derivWithin_of_mem_nhds
  apply (Continuous.continuousAt _).preimage_mem_nhds (by simpa using h)
  fun_prop

中文:
定理 lineDerivWithin_of_mem_nhds
  条件: (h : s in 𝓝 x)
  证明: by
  apply derivWithin_of_mem_nhds
  apply (Continuous.continuousAt _).preimage_mem_nhds (by simpa using h)
  fun_prop

Depends on / 依赖: Continuous, Continuous.continuousAt, continuousAt, derivWithin_of_mem_nhds, fun_prop, preimage_mem_nhds
-/
theorem lineDerivWithin_of_mem_nhds (h : s in 𝓝 x) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v := by
  apply derivWithin_of_mem_nhds
  apply (Continuous.continuousAt _).preimage_mem_nhds (by simpa using h)
  fun_prop

/--
theorem `lineDerivWithin_of_isOpen` / 定理 `lineDerivWithin_of_isOpen`

English:
theorem lineDerivWithin_of_isOpen
  given: (hs : IsOpen s) (hx : x in s)
  proof: lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)

中文:
定理 lineDerivWithin_of_isOpen
  条件: (hs : 是开集 s) (hx : x in s)
  证明: lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)

Depends on / 依赖: hs.mem_nhds, lineDerivWithin_of_mem_nhds, mem_nhds
-/
theorem lineDerivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v :=
  lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)

/--
theorem `hasLineDerivWithinAt_congr_set` / 定理 `hasLineDerivWithinAt_congr_set`

English:
theorem hasLineDerivWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: by
  apply hasDerivWithinAt_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

中文:
定理 hasLineDerivWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: by
  apply hasDerivWithinAt_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

Depends on / 依赖: B.preimage_mem_nhds, Continuous, Continuous.continuousAt, ContinuousAt, continuousAt, convert, fun_prop, hasDerivWithinAt_congr_set, preimage_mem_nhds
-/
theorem hasLineDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasLineDerivWithinAt 𝕜 f f' s x v ↔ HasLineDerivWithinAt 𝕜 f f' t x v := by
  apply hasDerivWithinAt_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

/--
theorem `lineDifferentiableWithinAt_congr_set` / 定理 `lineDifferentiableWithinAt_congr_set`

English:
theorem lineDifferentiableWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: ⟨fun h' => ((hasLineDerivWithinAt_congr_set h).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((hasLineDerivWithinAt_congr_set h.symm).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

中文:
定理 lineDifferentiableWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: ⟨fun h' => ((hasLineDerivWithinAt_congr_set h).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((hasLineDerivWithinAt_congr_set h.symm).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

Depends on / 依赖: h.symm, hasLineDerivWithinAt, hasLineDerivWithinAt_congr_set, lineDifferentiableWithinAt
-/
theorem lineDifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    LineDifferentiableWithinAt 𝕜 f s x v ↔ LineDifferentiableWithinAt 𝕜 f t x v :=
  ⟨fun h' => ((hasLineDerivWithinAt_congr_set h).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((hasLineDerivWithinAt_congr_set h.symm).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

/--
theorem `lineDerivWithin_congr_set` / 定理 `lineDerivWithin_congr_set`

English:
theorem lineDerivWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: by
  apply derivWithin_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

中文:
定理 lineDerivWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: by
  apply derivWithin_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

Depends on / 依赖: B.preimage_mem_nhds, Continuous, Continuous.continuousAt, ContinuousAt, continuousAt, convert, derivWithin_congr_set, fun_prop, preimage_mem_nhds
-/
theorem lineDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lineDerivWithin 𝕜 f s x v = lineDerivWithin 𝕜 f t x v := by
  apply derivWithin_congr_set
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : s =ᶠ[𝓝 (F 0)] t := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

/--
theorem `Filter.EventuallyEq.hasLineDerivAt_iff` / 定理 `Filter.EventuallyEq.hasLineDerivAt_iff`

English:
theorem Filter.EventuallyEq.hasLineDerivAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁)
  proof: by
  apply hasDerivAt_iff
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : f₀ =ᶠ[𝓝 (F 0)] f₁ := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

中文:
定理 滤子.EventuallyEq.hasLineDerivAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁)
  证明: by
  apply hasDerivAt_iff
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : f₀ =ᶠ[𝓝 (F 0)] f₁ := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

Depends on / 依赖: B.preimage_mem_nhds, Continuous, Continuous.continuousAt, ContinuousAt, continuousAt, convert, fun_prop, hasDerivAt_iff, preimage_mem_nhds
-/
theorem Filter.EventuallyEq.hasLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasLineDerivAt 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f' x v := by
  apply hasDerivAt_iff
  let F := fun (t : 𝕜) => x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; fun_prop
  have : f₀ =ᶠ[𝓝 (F 0)] f₁ := by convert! h; simp [F]
  exact B.preimage_mem_nhds this

/--
theorem `Filter.EventuallyEq.lineDifferentiableAt_iff` / 定理 `Filter.EventuallyEq.lineDifferentiableAt_iff`

English:
theorem Filter.EventuallyEq.lineDifferentiableAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁)
  proof: ⟨fun h' => (h.hasLineDerivAt_iff.1 h'.hasLineDerivAt).lineDifferentiableAt,
  fun h' => (h.hasLineDerivAt_iff.2 h'.hasLineDerivAt).lineDifferentiableAt⟩

中文:
定理 滤子.EventuallyEq.lineDifferentiableAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁)
  证明: ⟨fun h' => (h.hasLineDerivAt_iff.1 h'.hasLineDerivAt).lineDifferentiableAt,
  fun h' => (h.hasLineDerivAt_iff.2 h'.hasLineDerivAt).lineDifferentiableAt⟩

Depends on / 依赖: h.hasLineDerivAt_iff, hasLineDerivAt, hasLineDerivAt_iff, lineDifferentiableAt
-/
theorem Filter.EventuallyEq.lineDifferentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    LineDifferentiableAt 𝕜 f₀ x v ↔ LineDifferentiableAt 𝕜 f₁ x v :=
  ⟨fun h' => (h.hasLineDerivAt_iff.1 h'.hasLineDerivAt).lineDifferentiableAt,
  fun h' => (h.hasLineDerivAt_iff.2 h'.hasLineDerivAt).lineDifferentiableAt⟩

/--
theorem `Filter.EventuallyEq.hasLineDerivWithinAt_iff` / 定理 `Filter.EventuallyEq.hasLineDerivWithinAt_iff`

English:
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  proof: by
  apply hasDerivWithinAt_iff
  · have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
    exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h (by simp)
  · simpa using hx

中文:
定理 滤子.EventuallyEq.hasLineDerivWithinAt_iff
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  证明: by
  apply hasDerivWithinAt_iff
  · have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
    exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h (by simp)
  · simpa using hx

Depends on / 依赖: A.continuousWithinAt.preimage_mem_nhdsWithin, Continuous, continuousWithinAt, fun_prop, hasDerivWithinAt_iff, preimage_mem_nhdsWithin
-/
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v := by
  apply hasDerivWithinAt_iff
  · have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
    exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h (by simp)
  · simpa using hx

/--
theorem `Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem` / 定理 `Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem`

English:
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  proof: h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

中文:
定理 滤子.EventuallyEq.hasLineDerivWithinAt_iff_of_mem
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  证明: h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

Depends on / 依赖: eq_of_nhdsWithin, h.eq_of_nhdsWithin, h.hasLineDerivWithinAt_iff, hasLineDerivWithinAt_iff, ofMatrix, ofMatrix.symm
-/
theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

/--
theorem `Filter.EventuallyEq.lineDifferentiableWithinAt_iff` / 定理 `Filter.EventuallyEq.lineDifferentiableWithinAt_iff`

English:
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff
  proof: ⟨fun h' => ((h.hasLineDerivWithinAt_iff hx).1 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((h.hasLineDerivWithinAt_iff hx).2 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

中文:
定理 滤子.EventuallyEq.lineDifferentiableWithinAt_iff
  证明: ⟨fun h' => ((h.hasLineDerivWithinAt_iff hx).1 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((h.hasLineDerivWithinAt_iff hx).2 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

Depends on / 依赖: h.hasLineDerivWithinAt_iff, hasLineDerivWithinAt, hasLineDerivWithinAt_iff, lineDifferentiableWithinAt
-/
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  ⟨fun h' => ((h.hasLineDerivWithinAt_iff hx).1 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' => ((h.hasLineDerivWithinAt_iff hx).2 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

/--
theorem `Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem` / 定理 `Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem`

English:
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem
  proof: h.lineDifferentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

中文:
定理 滤子.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem
  证明: h.lineDifferentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

Depends on / 依赖: eq_of_nhdsWithin, h.eq_of_nhdsWithin, h.lineDifferentiableWithinAt_iff, lineDifferentiableWithinAt_iff
-/
theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  h.lineDifferentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

/--
lemma `HasLineDerivWithinAt.congr_of_eventuallyEq` / 引理 `HasLineDerivWithinAt.congr_of_eventuallyEq`

English:
lemma HasLineDerivWithinAt.congr_of_eventuallyEq
  statement: (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
  proof: .mp hf h'f.symm.hasLineDerivWithinAt_iff hx.symm

中文:
引理 HasLineDerivWithinAt.congr_of_eventuallyEq
  结论: (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
  证明: .mp hf h'f.symm.hasLineDerivWithinAt_iff hx.symm

Depends on / 依赖: f.symm.hasLineDerivWithinAt_iff, hasLineDerivWithinAt_iff, hx.symm
-/
lemma HasLineDerivWithinAt.congr_of_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
    (h'f : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
.mp hf h'f.symm.hasLineDerivWithinAt_iff hx.symm

/--
theorem `HasLineDerivAt.congr_of_eventuallyEq` / 定理 `HasLineDerivAt.congr_of_eventuallyEq`

English:
theorem HasLineDerivAt.congr_of_eventuallyEq
  given: (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: (EventuallyEq.hasLineDerivAt_iff h₁.symm).mp h

中文:
定理 HasLineDerivAt.congr_of_eventuallyEq
  条件: (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: (EventuallyEq.hasLineDerivAt_iff h₁.symm).mp h

Depends on / 依赖: EventuallyEq, EventuallyEq.hasLineDerivAt_iff, hasLineDerivAt_iff
-/
theorem HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasLineDerivAt 𝕜 f₁ f' x v :=
  (EventuallyEq.hasLineDerivAt_iff h₁.symm).mp h

/--
theorem `LineDifferentiableWithinAt.congr_of_eventuallyEq` / 定理 `LineDifferentiableWithinAt.congr_of_eventuallyEq`

English:
theorem LineDifferentiableWithinAt.congr_of_eventuallyEq
  statement: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  proof: (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

中文:
定理 LineDifferentiableWithinAt.congr_of_eventuallyEq
  结论: (h : LineDifferentiableWithinAt 𝕜 f s x v)
  证明: (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

Depends on / 依赖: congr_of_eventuallyEq, differentiableWithinAt, h.hasLineDerivWithinAt.congr_of_eventuallyEq, hasLineDerivWithinAt
-/
theorem LineDifferentiableWithinAt.congr_of_eventuallyEq (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

/--
theorem `LineDifferentiableAt.congr_of_eventuallyEq` / 定理 `LineDifferentiableAt.congr_of_eventuallyEq`

English:
theorem LineDifferentiableAt.congr_of_eventuallyEq
  proof: hL.symm.lineDifferentiableAt_iff.mp h

中文:
定理 LineDifferentiableAt.congr_of_eventuallyEq
  证明: hL.symm.lineDifferentiableAt_iff.mp h

Depends on / 依赖: hL.symm.lineDifferentiableAt_iff.mp, lineDifferentiableAt_iff
-/
theorem LineDifferentiableAt.congr_of_eventuallyEq
    (h : LineDifferentiableAt 𝕜 f x v) (hL : f₁ =ᶠ[𝓝 x] f) :
    LineDifferentiableAt 𝕜 f₁ x v :=
  hL.symm.lineDifferentiableAt_iff.mp h

/--
theorem `Filter.EventuallyEq.lineDerivWithin_eq` / 定理 `Filter.EventuallyEq.lineDerivWithin_eq`

English:
theorem Filter.EventuallyEq.lineDerivWithin_eq
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: by
  apply derivWithin_eq ?_ (by simpa using hx)
  have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' hs (by simp)

中文:
定理 滤子.EventuallyEq.lineDerivWithin_eq
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: by
  apply derivWithin_eq ?_ (by simpa using hx)
  have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' hs (by simp)

Depends on / 依赖: A.continuousWithinAt.preimage_mem_nhdsWithin, Continuous, continuousWithinAt, derivWithin_eq, fun_prop, preimage_mem_nhdsWithin
-/
theorem Filter.EventuallyEq.lineDerivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v := by
  apply derivWithin_eq ?_ (by simpa using hx)
  have A : Continuous (fun (t : 𝕜) => x + t • v) := by fun_prop
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' hs (by simp)

/--
theorem `Filter.EventuallyEq.lineDerivWithin_eq_nhds` / 定理 `Filter.EventuallyEq.lineDerivWithin_eq_nhds`

English:
theorem Filter.EventuallyEq.lineDerivWithin_eq_nhds
  given: (h : f₁ =ᶠ[𝓝 x] f)
  proof: (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds

中文:
定理 滤子.EventuallyEq.lineDerivWithin_eq_nhds
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  证明: (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds

Depends on / 依赖: filter_mono, h.filter_mono, h.self_of_nhds, lineDerivWithin_eq, nhdsWithin_le_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.lineDerivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds

/--
theorem `Filter.EventuallyEq.lineDeriv_eq` / 定理 `Filter.EventuallyEq.lineDeriv_eq`

English:
theorem Filter.EventuallyEq.lineDeriv_eq
  given: (h : f₁ =ᶠ[𝓝 x] f)
  proof: by
  rw [← lineDerivWithin_univ]; rw [← lineDerivWithin_univ]; rw [h.lineDerivWithin_eq_nhds]

中文:
定理 滤子.EventuallyEq.lineDeriv_eq
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  证明: by
  rw [← lineDerivWithin_univ]; rw [← lineDerivWithin_univ]; rw [h.lineDerivWithin_eq_nhds]

Depends on / 依赖: h.lineDerivWithin_eq_nhds, lineDerivWithin_eq_nhds, lineDerivWithin_univ
-/
theorem Filter.EventuallyEq.lineDeriv_eq (h : f₁ =ᶠ[𝓝 x] f) :
    lineDeriv 𝕜 f₁ x v = lineDeriv 𝕜 f x v := by
  rw [← lineDerivWithin_univ]; rw [← lineDerivWithin_univ]; rw [h.lineDerivWithin_eq_nhds]

/--
theorem `HasLineDerivAt.le_of_lip'` / 定理 `HasLineDerivAt.le_of_lip'`

English:
theorem HasLineDerivAt.le_of_lip'
  statement: {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
  proof: by
  apply HasDerivAt.le_of_lip' hf (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

中文:
定理 HasLineDerivAt.le_of_lip'
  结论: {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
  证明: by
  apply HasDerivAt.le_of_lip' hf (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

Depends on / 依赖: A.continuousAt, Continuous, HasDerivAt, HasDerivAt.le_of_lip, add_sub_cancel_left, continuousAt, filter_upwards, fun_prop, le_of_lip, mem_ofPred_eq, mul_assoc, mul_comm, norm_smul, preimage_mem_nhds, preimage_ofPred_eq
-/
theorem HasLineDerivAt.le_of_lip' {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) :
    ‖f'‖ <= C * ‖v‖ := by
  apply HasDerivAt.le_of_lip' hf (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

/--
theorem `HasLineDerivAt.le_of_lipschitzOn` / 定理 `HasLineDerivAt.le_of_lipschitzOn`

English:
theorem HasLineDerivAt.le_of_lipschitzOn
  proof: by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

中文:
定理 HasLineDerivAt.le_of_lipschitzOn
  证明: by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

Depends on / 依赖: C.coe_nonneg, coe_nonneg, filter_upwards, hf.le_of_lip, hlip.norm_sub_le, le_of_lip, mem_of_mem_nhds, norm_sub_le
-/
theorem HasLineDerivAt.le_of_lipschitzOn
    {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {s : Set E} (hs : s in 𝓝 x₀) {C : Real>=0} (hlip : LipschitzOnWith C f s) :
    ‖f'‖ <= C * ‖v‖ := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/--
theorem `HasLineDerivAt.le_of_lipschitz` / 定理 `HasLineDerivAt.le_of_lipschitz`

English:
theorem HasLineDerivAt.le_of_lipschitz
  proof: hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

中文:
定理 HasLineDerivAt.le_of_lipschitz
  证明: hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

Depends on / 依赖: hf.le_of_lipschitzOn, le_of_lipschitzOn, lipschitzOnWith_univ, univ_mem
-/
theorem HasLineDerivAt.le_of_lipschitz
    {f : E -> F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖f'‖ <= C * ‖v‖ :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

variable (𝕜)

/--
theorem `norm_lineDeriv_le_of_lip'` / 定理 `norm_lineDeriv_le_of_lip'`

English:
theorem norm_lineDeriv_le_of_lip'
  statement: {f : E -> F} {x₀ : E}
  proof: by
  apply norm_deriv_le_of_lip' (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

中文:
定理 norm_lineDeriv_le_of_lip'
  结论: {f : E -> F} {x₀ : E}
  证明: by
  apply norm_deriv_le_of_lip' (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

Depends on / 依赖: A.continuousAt, Continuous, add_sub_cancel_left, continuousAt, filter_upwards, fun_prop, mem_ofPred_eq, mul_assoc, mul_comm, norm_deriv_le_of_lip, norm_smul, preimage_mem_nhds, preimage_ofPred_eq
-/
theorem norm_lineDeriv_le_of_lip' {f : E -> F} {x₀ : E}
    {C : Real} (hC₀ : 0 <= C) (hlip : forallᶠ x in 𝓝 x₀, ‖f x - f x₀‖ <= C * ‖x - x₀‖) :
    ‖lineDeriv 𝕜 f x₀ v‖ <= C * ‖v‖ := by
  apply norm_deriv_le_of_lip' (by positivity)
  have A : Continuous (fun (t : 𝕜) => x₀ + t • v) := by fun_prop
  have : forallᶠ x in 𝓝 (x₀ + (0 : 𝕜) • v), ‖f x - f x₀‖ <= C * ‖x - x₀‖ := by simpa using hlip
  filter_upwards [(A.continuousAt (x := 0)).preimage_mem_nhds this] with t ht
  simp only [preimage_ofPred_eq, add_sub_cancel_left, norm_smul, mem_ofPred_eq,
    mul_comm (‖t‖)] at ht
  simpa [mul_assoc] using ht

/--
theorem `norm_lineDeriv_le_of_lipschitzOn` / 定理 `norm_lineDeriv_le_of_lipschitzOn`

English:
theorem norm_lineDeriv_le_of_lipschitzOn
  statement: {f : E -> F} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀)
  proof: by
  refine norm_lineDeriv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

中文:
定理 norm_lineDeriv_le_of_lipschitzOn
  结论: {f : E -> F} {x₀ : E} {s : 集合 E} (hs : s in 𝓝 x₀)
  证明: by
  refine norm_lineDeriv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

Depends on / 依赖: C.coe_nonneg, coe_nonneg, filter_upwards, hlip.norm_sub_le, mem_of_mem_nhds, norm_lineDeriv_le_of_lip, norm_sub_le
-/
theorem norm_lineDeriv_le_of_lipschitzOn {f : E -> F} {x₀ : E} {s : Set E} (hs : s in 𝓝 x₀)
    {C : Real>=0} (hlip : LipschitzOnWith C f s) : ‖lineDeriv 𝕜 f x₀ v‖ <= C * ‖v‖ := by
  refine norm_lineDeriv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/--
theorem `norm_lineDeriv_le_of_lipschitz` / 定理 `norm_lineDeriv_le_of_lipschitz`

English:
theorem norm_lineDeriv_le_of_lipschitz
  statement: {f : E -> F} {x₀ : E}
  proof: norm_lineDeriv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

中文:
定理 norm_lineDeriv_le_of_lipschitz
  结论: {f : E -> F} {x₀ : E}
  证明: norm_lineDeriv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

Depends on / 依赖: lipschitzOnWith_univ, norm_lineDeriv_le_of_lipschitzOn, univ_mem
-/
theorem norm_lineDeriv_le_of_lipschitz {f : E -> F} {x₀ : E}
    {C : Real>=0} (hlip : LipschitzWith C f) : ‖lineDeriv 𝕜 f x₀ v‖ <= C * ‖v‖ :=
  norm_lineDeriv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

end NormedSpace

section Zero

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E -> F} {s : Set E} {x : E}

/--
theorem `hasLineDerivWithinAt_zero` / 定理 `hasLineDerivWithinAt_zero`

English:
theorem hasLineDerivWithinAt_zero
  statement: HasLineDerivWithinAt 𝕜 f 0 s x 0
  proof: by
  simp [HasLineDerivWithinAt, hasDerivWithinAt_const]

中文:
定理 hasLineDerivWithinAt_zero
  结论: HasLineDerivWithinAt 𝕜 f 0 s x 0
  证明: by
  simp [HasLineDerivWithinAt, hasDerivWithinAt_const]

Depends on / 依赖: HasLineDerivWithinAt, hasDerivWithinAt_const
-/
theorem hasLineDerivWithinAt_zero : HasLineDerivWithinAt 𝕜 f 0 s x 0 := by
  simp [HasLineDerivWithinAt, hasDerivWithinAt_const]

/--
theorem `hasLineDerivAt_zero` / 定理 `hasLineDerivAt_zero`

English:
theorem hasLineDerivAt_zero
  statement: HasLineDerivAt 𝕜 f 0 x 0
  proof: by
  simp [HasLineDerivAt, hasDerivAt_const]

中文:
定理 hasLineDerivAt_zero
  结论: HasLineDerivAt 𝕜 f 0 x 0
  证明: by
  simp [HasLineDerivAt, hasDerivAt_const]

Depends on / 依赖: HasLineDerivAt, hasDerivAt_const
-/
theorem hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0 := by
  simp [HasLineDerivAt, hasDerivAt_const]

/--
theorem `lineDifferentiableWithinAt_zero` / 定理 `lineDifferentiableWithinAt_zero`

English:
theorem lineDifferentiableWithinAt_zero
  statement: LineDifferentiableWithinAt 𝕜 f s x 0
  proof: hasLineDerivWithinAt_zero.lineDifferentiableWithinAt

中文:
定理 lineDifferentiableWithinAt_zero
  结论: LineDifferentiableWithinAt 𝕜 f s x 0
  证明: hasLineDerivWithinAt_zero.lineDifferentiableWithinAt

Depends on / 依赖: hasLineDerivWithinAt_zero, hasLineDerivWithinAt_zero.lineDifferentiableWithinAt, lineDifferentiableWithinAt
-/
theorem lineDifferentiableWithinAt_zero : LineDifferentiableWithinAt 𝕜 f s x 0 :=
  hasLineDerivWithinAt_zero.lineDifferentiableWithinAt

/--
theorem `lineDifferentiableAt_zero` / 定理 `lineDifferentiableAt_zero`

English:
theorem lineDifferentiableAt_zero
  statement: LineDifferentiableAt 𝕜 f x 0
  proof: hasLineDerivAt_zero.lineDifferentiableAt

中文:
定理 lineDifferentiableAt_zero
  结论: LineDifferentiableAt 𝕜 f x 0
  证明: hasLineDerivAt_zero.lineDifferentiableAt

Depends on / 依赖: hasLineDerivAt_zero, hasLineDerivAt_zero.lineDifferentiableAt, lineDifferentiableAt
-/
theorem lineDifferentiableAt_zero : LineDifferentiableAt 𝕜 f x 0 :=
  hasLineDerivAt_zero.lineDifferentiableAt

/--
theorem `lineDeriv_zero` / 定理 `lineDeriv_zero`

English:
theorem lineDeriv_zero
  statement: lineDeriv 𝕜 f x 0 = 0
  proof: hasLineDerivAt_zero.lineDeriv

中文:
定理 lineDeriv_zero
  结论: lineDeriv 𝕜 f x 0 = 0
  证明: hasLineDerivAt_zero.lineDeriv

Depends on / 依赖: hasLineDerivAt_zero, hasLineDerivAt_zero.lineDeriv, lineDeriv
-/
theorem lineDeriv_zero : lineDeriv 𝕜 f x 0 = 0 :=
  hasLineDerivAt_zero.lineDeriv

end Zero

section CompRight

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
  {f : E -> F} {f' : F} {x : E'} {L : E' ->ₗ[𝕜] E}

/--
theorem `HasLineDerivAt.of_comp` / 定理 `HasLineDerivAt.of_comp`

English:
theorem HasLineDerivAt.of_comp
  given: {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v)
  proof: by
  simpa [HasLineDerivAt] using hf

中文:
定理 HasLineDerivAt.of_comp
  条件: {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v)
  证明: by
  simpa [HasLineDerivAt] using hf

Depends on / 依赖: HasLineDerivAt
-/
theorem HasLineDerivAt.of_comp {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v) :
    HasLineDerivAt 𝕜 f f' (L x) (L v) := by
  simpa [HasLineDerivAt] using hf

/--
theorem `LineDifferentiableAt.of_comp` / 定理 `LineDifferentiableAt.of_comp`

English:
theorem LineDifferentiableAt.of_comp
  given: {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L) x v)
  proof: hf.hasLineDerivAt.of_comp.lineDifferentiableAt

中文:
定理 LineDifferentiableAt.of_comp
  条件: {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L) x v)
  证明: hf.hasLineDerivAt.of_comp.lineDifferentiableAt

Depends on / 依赖: hasLineDerivAt, hf.hasLineDerivAt.of_comp.lineDifferentiableAt, lineDifferentiableAt, of_comp
-/
theorem LineDifferentiableAt.of_comp {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L) x v) :
    LineDifferentiableAt 𝕜 f (L x) (L v) :=
  hf.hasLineDerivAt.of_comp.lineDifferentiableAt

end CompRight

section SMul

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E -> F} {s : Set E} {x v : E} {f' : F}

/--
theorem `HasLineDerivWithinAt.smul` / 定理 `HasLineDerivWithinAt.smul`

English:
theorem HasLineDerivWithinAt.smul
  given: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜)
  proof: by
  simp only [HasLineDerivWithinAt] at h ⊢
  let g := fun (t : 𝕜) => c • t
  let s' := (fun (t : 𝕜) => x + t • v) ⁻¹' s
  have A : HasDerivAt g c 0 := by simpa using! (hasDerivAt_id (0 : 𝕜)).const_smul c
  have B : HasDerivWithinAt (fun t => f (x + t • v)) f' s' (g 0) := by simpa [g] using! h
  have Z := B.scomp (0 : 𝕜) A.hasDerivWithinAt (mapsTo_preimage g s')
  simp only [g, s', Function.comp_def, smul_eq_mul, mul_comm c, ← smul_smul] at Z
  convert! Z
  ext t
  simp [← smul_smul]

中文:
定理 HasLineDerivWithinAt.smul
  条件: (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜)
  证明: by
  simp only [HasLineDerivWithinAt] at h ⊢
  let g := fun (t : 𝕜) => c • t
  let s' := (fun (t : 𝕜) => x + t • v) ⁻¹' s
  have A : HasDerivAt g c 0 := by simpa using! (hasDerivAt_id (0 : 𝕜)).const_smul c
  have B : HasDerivWithinAt (fun t => f (x + t • v)) f' s' (g 0) := by simpa [g] using! h
  have Z := B.scomp (0 : 𝕜) A.hasDerivWithinAt (mapsTo_preimage g s')
  simp only [g, s', Function.comp_def, smul_eq_mul, mul_comm c, ← smul_smul] at Z
  convert! Z
  ext t
  simp [← smul_smul]

Depends on / 依赖: A.hasDerivWithinAt, B.scomp, Function, Function.comp_def, HasDerivAt, HasDerivWithinAt, HasLineDerivWithinAt, comp_def, const_smul, convert, hasDerivAt_id, hasDerivWithinAt, mapsTo_preimage, mul_comm, smul_eq_mul, smul_smul
-/
theorem HasLineDerivWithinAt.smul (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜) :
    HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v) := by
  simp only [HasLineDerivWithinAt] at h ⊢
  let g := fun (t : 𝕜) => c • t
  let s' := (fun (t : 𝕜) => x + t • v) ⁻¹' s
  have A : HasDerivAt g c 0 := by simpa using! (hasDerivAt_id (0 : 𝕜)).const_smul c
  have B : HasDerivWithinAt (fun t => f (x + t • v)) f' s' (g 0) := by simpa [g] using! h
  have Z := B.scomp (0 : 𝕜) A.hasDerivWithinAt (mapsTo_preimage g s')
  simp only [g, s', Function.comp_def, smul_eq_mul, mul_comm c, ← smul_smul] at Z
  convert! Z
  ext t
  simp [← smul_smul]

/--
theorem `hasLineDerivWithinAt_smul_iff` / 定理 `hasLineDerivWithinAt_smul_iff`

English:
theorem hasLineDerivWithinAt_smul_iff
  given: {c : 𝕜} (hc : c != 0)
  proof: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

中文:
定理 hasLineDerivWithinAt_smul_iff
  条件: {c : 𝕜} (hc : c != 0)
  证明: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

Depends on / 依赖: h.smul, smul_smul
-/
theorem hasLineDerivWithinAt_smul_iff {c : 𝕜} (hc : c != 0) :
    HasLineDerivWithinAt 𝕜 f (c • f') s x (c • v) ↔ HasLineDerivWithinAt 𝕜 f f' s x v :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

/--
theorem `HasLineDerivAt.smul` / 定理 `HasLineDerivAt.smul`

English:
theorem HasLineDerivAt.smul
  given: (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜)
  proof: by
  simp only [← hasLineDerivWithinAt_univ] at h ⊢
  exact HasLineDerivWithinAt.smul h c

中文:
定理 HasLineDerivAt.smul
  条件: (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜)
  证明: by
  simp only [← hasLineDerivWithinAt_univ] at h ⊢
  exact HasLineDerivWithinAt.smul h c

Depends on / 依赖: HasLineDerivWithinAt, HasLineDerivWithinAt.smul, hasLineDerivWithinAt_univ
-/
theorem HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜) :
    HasLineDerivAt 𝕜 f (c • f') x (c • v) := by
  simp only [← hasLineDerivWithinAt_univ] at h ⊢
  exact HasLineDerivWithinAt.smul h c

/--
theorem `hasLineDerivAt_smul_iff` / 定理 `hasLineDerivAt_smul_iff`

English:
theorem hasLineDerivAt_smul_iff
  given: {c : 𝕜} (hc : c != 0)
  proof: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

中文:
定理 hasLineDerivAt_smul_iff
  条件: {c : 𝕜} (hc : c != 0)
  证明: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

Depends on / 依赖: h.smul, smul_smul
-/
theorem hasLineDerivAt_smul_iff {c : 𝕜} (hc : c != 0) :
    HasLineDerivAt 𝕜 f (c • f') x (c • v) ↔ HasLineDerivAt 𝕜 f f' x v :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

/--
theorem `LineDifferentiableWithinAt.smul` / 定理 `LineDifferentiableWithinAt.smul`

English:
theorem LineDifferentiableWithinAt.smul
  given: (h : LineDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜)
  proof: (h.hasLineDerivWithinAt.smul c).lineDifferentiableWithinAt

中文:
定理 LineDifferentiableWithinAt.smul
  条件: (h : LineDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜)
  证明: (h.hasLineDerivWithinAt.smul c).lineDifferentiableWithinAt

Depends on / 依赖: h.hasLineDerivWithinAt.smul, hasLineDerivWithinAt, lineDifferentiableWithinAt
-/
theorem LineDifferentiableWithinAt.smul (h : LineDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜) :
    LineDifferentiableWithinAt 𝕜 f s x (c • v) :=
  (h.hasLineDerivWithinAt.smul c).lineDifferentiableWithinAt

/--
theorem `lineDifferentiableWithinAt_smul_iff` / 定理 `lineDifferentiableWithinAt_smul_iff`

English:
theorem lineDifferentiableWithinAt_smul_iff
  given: {c : 𝕜} (hc : c != 0)
  proof: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

中文:
定理 lineDifferentiableWithinAt_smul_iff
  条件: {c : 𝕜} (hc : c != 0)
  证明: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

Depends on / 依赖: h.smul, smul_smul
-/
theorem lineDifferentiableWithinAt_smul_iff {c : 𝕜} (hc : c != 0) :
    LineDifferentiableWithinAt 𝕜 f s x (c • v) ↔ LineDifferentiableWithinAt 𝕜 f s x v :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

/--
theorem `LineDifferentiableAt.smul` / 定理 `LineDifferentiableAt.smul`

English:
theorem LineDifferentiableAt.smul
  given: (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜)
  proof: (h.hasLineDerivAt.smul c).lineDifferentiableAt

中文:
定理 LineDifferentiableAt.smul
  条件: (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜)
  证明: (h.hasLineDerivAt.smul c).lineDifferentiableAt

Depends on / 依赖: h.hasLineDerivAt.smul, hasLineDerivAt, lineDifferentiableAt
-/
theorem LineDifferentiableAt.smul (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜) :
    LineDifferentiableAt 𝕜 f x (c • v) :=
  (h.hasLineDerivAt.smul c).lineDifferentiableAt

/--
theorem `lineDifferentiableAt_smul_iff` / 定理 `lineDifferentiableAt_smul_iff`

English:
theorem lineDifferentiableAt_smul_iff
  given: {c : 𝕜} (hc : c != 0)
  proof: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

中文:
定理 lineDifferentiableAt_smul_iff
  条件: {c : 𝕜} (hc : c != 0)
  证明: ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

Depends on / 依赖: h.smul, smul_smul
-/
theorem lineDifferentiableAt_smul_iff {c : 𝕜} (hc : c != 0) :
    LineDifferentiableAt 𝕜 f x (c • v) ↔ LineDifferentiableAt 𝕜 f x v :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul (c ⁻¹), fun h => h.smul c⟩

/--
theorem `lineDeriv_smul` / 定理 `lineDeriv_smul`

English:
theorem lineDeriv_smul
  given: {c : 𝕜}
  statement: lineDeriv 𝕜 f x (c • v) = c • lineDeriv 𝕜 f x v
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [lineDeriv_zero]
  by_cases H : LineDifferentiableAt 𝕜 f x v
  · exact (H.hasLineDerivAt.smul c).lineDeriv
  · have H' : ¬ (LineDifferentiableAt 𝕜 f x (c • v)) := by
      simpa [lineDifferentiableAt_smul_iff hc] using H
    simp [lineDeriv_zero_of_not_lineDifferentiableAt, H, H']

中文:
定理 lineDeriv_smul
  条件: {c : 𝕜}
  结论: lineDeriv 𝕜 f x (c • v) = c • lineDeriv 𝕜 f x v
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [lineDeriv_zero]
  by_cases H : LineDifferentiableAt 𝕜 f x v
  · exact (H.hasLineDerivAt.smul c).lineDeriv
  · have H' : ¬ (LineDifferentiableAt 𝕜 f x (c • v)) := by
      simpa [lineDifferentiableAt_smul_iff hc] using H
    simp [lineDeriv_zero_of_not_lineDifferentiableAt, H, H']

Depends on / 依赖: H.hasLineDerivAt.smul, LineDifferentiableAt, eq_or_ne, hasLineDerivAt, lineDeriv, lineDeriv_zero, lineDeriv_zero_of_not_lineDifferentiableAt, lineDifferentiableAt_smul_iff
-/
theorem lineDeriv_smul {c : 𝕜} : lineDeriv 𝕜 f x (c • v) = c • lineDeriv 𝕜 f x v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [lineDeriv_zero]
  by_cases H : LineDifferentiableAt 𝕜 f x v
  · exact (H.hasLineDerivAt.smul c).lineDeriv
  · have H' : ¬ (LineDifferentiableAt 𝕜 f x (c • v)) := by
      simpa [lineDifferentiableAt_smul_iff hc] using H
    simp [lineDeriv_zero_of_not_lineDifferentiableAt, H, H']

/--
theorem `lineDeriv_neg` / 定理 `lineDeriv_neg`

English:
theorem lineDeriv_neg
  statement: lineDeriv 𝕜 f x (-v) = - lineDeriv 𝕜 f x v
  proof: by
  rw [← neg_one_smul (R := 𝕜) v]; rw [lineDeriv_smul]; rw [neg_one_smul]

中文:
定理 lineDeriv_neg
  结论: lineDeriv 𝕜 f x (-v) = - lineDeriv 𝕜 f x v
  证明: by
  rw [← neg_one_smul (R := 𝕜) v]; rw [lineDeriv_smul]; rw [neg_one_smul]

Depends on / 依赖: lineDeriv_smul, neg_one_smul
-/
theorem lineDeriv_neg : lineDeriv 𝕜 f x (-v) = - lineDeriv 𝕜 f x v := by
  rw [← neg_one_smul (R := 𝕜) v]; rw [lineDeriv_smul]; rw [neg_one_smul]

end SMul
