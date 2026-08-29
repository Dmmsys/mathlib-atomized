/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Analysis.Normed.Operator.Prod

/-! ## Equivalence of smoothness with the basic definition for functions between vector spaces

* `contMDiff_iff_contDiff`: for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.
* `ContinuousLinearMap.contMDiff`: continuous linear maps between normed spaces are smooth

Smoothness of addition and scalar multiplication in normed spaces is proven not here but in
`Mathlib/Geometry/Manifold/Algebra/LieGroup.lean` and `Mathlib/Geometry/Manifold/Algebra/SMul.lean`
in the form of `LieAddGroup` and `ContMDiffSMul` instances.

-/

public section

open Set ChartedSpace
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare normed spaces `E'`, `F`, `F'`, `F₁`, `F₂`, `F₃`, `F₄`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {s : Set M} {x : M} {n : WithTop Nat∞}

section Module

set_option backward.isDefEq.respectTransparency false in
/--
theorem `contMDiffWithinAt_iff_contDiffWithinAt` / 定理 `contMDiffWithinAt_iff_contDiffWithinAt`

English:
theorem contMDiffWithinAt_iff_contDiffWithinAt
  given: {f : E -> E'} {s : Set E} {x : E}
  proof: by
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

alias ⟨ContMDiffWithinAt.contDiffWithinAt, ContDiffWithinAt.contMDiffWithinAt⟩ :=
  contMDiffWithinAt_iff_contDiffWithinAt

中文:
定理 contMDiffWithinAt_iff_contDiffWithinAt
  条件: {f : E -> E'} {s : 集合 E} {x : E}
  证明: by
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

alias ⟨ContMDiffWithinAt.contDiffWithinAt, ContDiffWithinAt.contMDiffWithinAt⟩ :=
  contMDiffWithinAt_iff_contDiffWithinAt

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.continuousWithinAt, ContDiffWithinAtProp, ContMDiffWithinAt, contextual, continuousWithinAt, iff_def, liftPropWithinAt_iff, mfld_simps
-/
theorem contMDiffWithinAt_iff_contDiffWithinAt {f : E -> E'} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

alias ⟨ContMDiffWithinAt.contDiffWithinAt, ContDiffWithinAt.contMDiffWithinAt⟩ :=
  contMDiffWithinAt_iff_contDiffWithinAt

/--
theorem `contMDiffAt_iff_contDiffAt` / 定理 `contMDiffAt_iff_contDiffAt`

English:
theorem contMDiffAt_iff_contDiffAt
  given: {f : E -> E'} {x : E}
  proof: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_contDiffWithinAt]; rw [contDiffWithinAt_univ]

alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt

中文:
定理 contMDiffAt_iff_contDiffAt
  条件: {f : E -> E'} {x : E}
  证明: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_contDiffWithinAt]; rw [contDiffWithinAt_univ]

alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt

Depends on / 依赖: contDiffWithinAt_univ, contMDiffWithinAt_iff_contDiffWithinAt, contMDiffWithinAt_univ
-/
theorem contMDiffAt_iff_contDiffAt {f : E -> E'} {x : E} :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x := by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_contDiffWithinAt]; rw [contDiffWithinAt_univ]

alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt

/--
theorem `contMDiffOn_iff_contDiffOn` / 定理 `contMDiffOn_iff_contDiffOn`

English:
theorem contMDiffOn_iff_contDiffOn
  given: {f : E -> E'} {s : Set E}
  proof: forall_congr' by simp [contMDiffWithinAt_iff_contDiffWithinAt]

alias ⟨ContMDiffOn.contDiffOn, ContDiffOn.contMDiffOn⟩ := contMDiffOn_iff_contDiffOn

中文:
定理 contMDiffOn_iff_contDiffOn
  条件: {f : E -> E'} {s : 集合 E}
  证明: forall_congr' by simp [contMDiffWithinAt_iff_contDiffWithinAt]

alias ⟨ContMDiffOn.contDiffOn, ContDiffOn.contMDiffOn⟩ := contMDiffOn_iff_contDiffOn

Depends on / 依赖: contMDiffWithinAt_iff_contDiffWithinAt, forall_congr
-/
theorem contMDiffOn_iff_contDiffOn {f : E -> E'} {s : Set E} :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s :=
forall_congr' by simp [contMDiffWithinAt_iff_contDiffWithinAt]

alias ⟨ContMDiffOn.contDiffOn, ContDiffOn.contMDiffOn⟩ := contMDiffOn_iff_contDiffOn

/--
theorem `contMDiff_iff_contDiff` / 定理 `contMDiff_iff_contDiff`

English:
theorem contMDiff_iff_contDiff
  given: {f : E -> E'}
  statement: ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f
  proof: by
  rw [← contDiffOn_univ]; rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_contDiffOn]

alias ⟨ContMDiff.contDiff, ContDiff.contMDiff⟩ := contMDiff_iff_contDiff

中文:
定理 contMDiff_iff_contDiff
  条件: {f : E -> E'}
  结论: ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ 连续可微 𝕜 n f
  证明: by
  rw [← contDiffOn_univ]; rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_contDiffOn]

alias ⟨ContMDiff.contDiff, ContDiff.contMDiff⟩ := contMDiff_iff_contDiff

Depends on / 依赖: contDiffOn_univ, contMDiffOn_iff_contDiffOn, contMDiffOn_univ
-/
theorem contMDiff_iff_contDiff {f : E -> E'} : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]; rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_contDiffOn]

alias ⟨ContMDiff.contDiff, ContDiff.contMDiff⟩ := contMDiff_iff_contDiff

/--
theorem `ContDiffWithinAt.comp_contMDiffWithinAt` / 定理 `ContDiffWithinAt.comp_contMDiffWithinAt`

English:
theorem ContDiffWithinAt.comp_contMDiffWithinAt
  statement: {g : F -> F'} {f : M -> F} {s : Set M} {t : Set F}
  proof: hg.contMDiffWithinAt.comp x hf h

中文:
定理 ContDiffWithinAt.comp_contMDiffWithinAt
  结论: {g : F -> F'} {f : M -> F} {s : 集合 M} {t : 集合 F}
  证明: hg.contMDiffWithinAt.comp x hf h

Depends on / 依赖: contMDiffWithinAt, hg.contMDiffWithinAt.comp
-/
theorem ContDiffWithinAt.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {t : Set F}
    {x : M} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x)
    (h : s subseteq f ⁻¹' t) : ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffWithinAt.comp x hf h

/--
theorem `ContDiffAt.comp_contMDiffWithinAt` / 定理 `ContDiffAt.comp_contMDiffWithinAt`

English:
theorem ContDiffAt.comp_contMDiffWithinAt
  statement: {g : F -> F'} {f : M -> F} {s : Set M}
  proof: hg.contMDiffAt.comp_contMDiffWithinAt x hf

中文:
定理 ContDiffAt.comp_contMDiffWithinAt
  结论: {g : F -> F'} {f : M -> F} {s : 集合 M}
  证明: hg.contMDiffAt.comp_contMDiffWithinAt x hf

Depends on / 依赖: comp_contMDiffWithinAt, contMDiffAt, hg.contMDiffAt.comp_contMDiffWithinAt
-/
theorem ContDiffAt.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Set M}
    {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffAt.comp_contMDiffWithinAt x hf

/--
theorem `ContDiffAt.comp_contMDiffAt` / 定理 `ContDiffAt.comp_contMDiffAt`

English:
theorem ContDiffAt.comp_contMDiffAt
  statement: {g : F -> F'} {f : M -> F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
  proof: hg.comp_contMDiffWithinAt hf

中文:
定理 ContDiffAt.comp_contMDiffAt
  结论: {g : F -> F'} {f : M -> F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
  证明: hg.comp_contMDiffWithinAt hf

Depends on / 依赖: comp_contMDiffWithinAt, hg.comp_contMDiffWithinAt
-/
theorem ContDiffAt.comp_contMDiffAt {g : F -> F'} {f : M -> F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf

/--
theorem `ContDiff.comp_contMDiffWithinAt` / 定理 `ContDiff.comp_contMDiffWithinAt`

English:
theorem ContDiff.comp_contMDiffWithinAt
  statement: {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
  proof: hg.contDiffAt.comp_contMDiffWithinAt hf

中文:
定理 连续可微.comp_contMDiffWithinAt
  结论: {g : F -> F'} {f : M -> F} {s : 集合 M} {x : M}
  证明: hg.contDiffAt.comp_contMDiffWithinAt hf

Depends on / 依赖: comp_contMDiffWithinAt, contDiffAt, hg.contDiffAt.comp_contMDiffWithinAt
-/
theorem ContDiff.comp_contMDiffWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
    (hg : ContDiff 𝕜 n g) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contDiffAt.comp_contMDiffWithinAt hf

/--
theorem `ContDiff.comp_contMDiffAt` / 定理 `ContDiff.comp_contMDiffAt`

English:
theorem ContDiff.comp_contMDiffAt
  statement: {g : F -> F'} {f : M -> F} {x : M} (hg : ContDiff 𝕜 n g)
  proof: hg.comp_contMDiffWithinAt hf

中文:
定理 连续可微.comp_contMDiffAt
  结论: {g : F -> F'} {f : M -> F} {x : M} (hg : 连续可微 𝕜 n g)
  证明: hg.comp_contMDiffWithinAt hf

Depends on / 依赖: comp_contMDiffWithinAt, hg.comp_contMDiffWithinAt
-/
theorem ContDiff.comp_contMDiffAt {g : F -> F'} {f : M -> F} {x : M} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf

/--
theorem `ContDiff.comp_contMDiff` / 定理 `ContDiff.comp_contMDiff`

English:
theorem ContDiff.comp_contMDiff
  statement: {g : F -> F'} {f : M -> F} (hg : ContDiff 𝕜 n g)
  proof: fun x =>
  hg.contDiffAt.comp_contMDiffAt (hf x)

中文:
定理 连续可微.comp_contMDiff
  结论: {g : F -> F'} {f : M -> F} (hg : 连续可微 𝕜 n g)
  证明: fun x =>
  hg.contDiffAt.comp_contMDiffAt (hf x)
-/
theorem ContDiff.comp_contMDiff {g : F -> F'} {f : M -> F} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiff I 𝓘(𝕜, F) n f) : ContMDiff I 𝓘(𝕜, F') n (g ∘ f) := fun x =>
  hg.contDiffAt.comp_contMDiffAt (hf x)

end Module


/--
theorem `ContinuousLinearMap.contMDiff` / 定理 `ContinuousLinearMap.contMDiff`

English:
theorem ContinuousLinearMap.contMDiff
  given: (L : E ->L[𝕜] F)
  statement: ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L
  proof: L.contDiff.contMDiff

中文:
定理 连续线性映射.contMDiff
  条件: (L : E ->L[𝕜] F)
  结论: ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L
  证明: L.contDiff.contMDiff

Depends on / 依赖: L.contDiff.contMDiff, contDiff, contMDiff
-/
theorem ContinuousLinearMap.contMDiff (L : E ->L[𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
  L.contDiff.contMDiff

/--
theorem `ContinuousLinearMap.contMDiffAt` / 定理 `ContinuousLinearMap.contMDiffAt`

English:
theorem ContinuousLinearMap.contMDiffAt
  given: (L : E ->L[𝕜] F) {x}
  statement: ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x
  proof: L.contMDiff _

中文:
定理 连续线性映射.contMDiffAt
  条件: (L : E ->L[𝕜] F) {x}
  结论: ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x
  证明: L.contMDiff _

Depends on / 依赖: L.contMDiff, contMDiff
-/
theorem ContinuousLinearMap.contMDiffAt (L : E ->L[𝕜] F) {x} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x :=
  L.contMDiff _

/--
theorem `ContinuousLinearMap.contMDiffWithinAt` / 定理 `ContinuousLinearMap.contMDiffWithinAt`

English:
theorem ContinuousLinearMap.contMDiffWithinAt
  given: (L : E ->L[𝕜] F) {s x}
  proof: L.contMDiffAt.contMDiffWithinAt

中文:
定理 连续线性映射.contMDiffWithinAt
  条件: (L : E ->L[𝕜] F) {s x}
  证明: L.contMDiffAt.contMDiffWithinAt

Depends on / 依赖: L.contMDiffAt.contMDiffWithinAt, contMDiffAt, contMDiffWithinAt
-/
theorem ContinuousLinearMap.contMDiffWithinAt (L : E ->L[𝕜] F) {s x} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L s x :=
  L.contMDiffAt.contMDiffWithinAt

/--
theorem `ContinuousLinearMap.contMDiffOn` / 定理 `ContinuousLinearMap.contMDiffOn`

English:
theorem ContinuousLinearMap.contMDiffOn
  given: (L : E ->L[𝕜] F) {s}
  statement: ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n L s
  proof: L.contMDiff.contMDiffOn

中文:
定理 连续线性映射.contMDiffOn
  条件: (L : E ->L[𝕜] F) {s}
  结论: ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n L s
  证明: L.contMDiff.contMDiffOn

Depends on / 依赖: L.contMDiff.contMDiffOn, contMDiff, contMDiffOn
-/
theorem ContinuousLinearMap.contMDiffOn (L : E ->L[𝕜] F) {s} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n L s :=
  L.contMDiff.contMDiffOn

/--
theorem `ContMDiffWithinAt.clm_precomp` / 定理 `ContMDiffWithinAt.clm_precomp`

English:
theorem ContMDiffWithinAt.clm_precomp
  statement: {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M}
  proof: ContDiff.comp_contMDiffWithinAt (g := (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip)
    (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_precomp

中文:
定理 ContMDiffWithinAt.clm_precomp
  结论: {f : M -> F₁ ->L[𝕜] F₂} {s : 集合 M} {x : M}
  证明: ContDiff.comp_contMDiffWithinAt (g := (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip)
    (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_precomp

Depends on / 依赖: ContDiff, ContDiff.comp_contMDiffWithinAt, ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.contDiff, comp_contMDiffWithinAt, contDiff
-/
theorem ContMDiffWithinAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip)
    (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_precomp

/--
theorem `ContMDiffOn.clm_precomp` / 定理 `ContMDiffOn.clm_precomp`

English:
theorem ContMDiffOn.clm_precomp
  statement: {f : M -> F₁ ->L[𝕜] F₂} {s : Set M}
  proof: fun x hx =>
  (hf x hx).clm_precomp

中文:
定理 ContMDiffOn.clm_precomp
  结论: {f : M -> F₁ ->L[𝕜] F₂} {s : 集合 M}
  证明: fun x hx =>
  (hf x hx).clm_precomp
-/
theorem ContMDiffOn.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s := fun x hx =>
  (hf x hx).clm_precomp

/--
theorem `ContMDiff.clm_precomp` / 定理 `ContMDiff.clm_precomp`

English:
theorem ContMDiff.clm_precomp
  given: {f : M -> F₁ ->L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f)
  proof: fun x =>
  (hf x).clm_precomp

中文:
定理 ContMDiff.clm_precomp
  条件: {f : M -> F₁ ->L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f)
  证明: fun x =>
  (hf x).clm_precomp
-/
theorem ContMDiff.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n f) :
    ContMDiff I 𝓘(𝕜, (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) := fun x =>
  (hf x).clm_precomp

/--
theorem `ContMDiffWithinAt.clm_postcomp` / 定理 `ContMDiffWithinAt.clm_postcomp`

English:
theorem ContMDiffWithinAt.clm_postcomp
  statement: {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M}
  proof: ContDiff.comp_contMDiffWithinAt (F' := (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃))
    (g := ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃) (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_postcomp

nonrec theorem ContMDiffOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s := fun x hx =>
  (hf x hx).clm_postcomp

中文:
定理 ContMDiffWithinAt.clm_postcomp
  结论: {f : M -> F₂ ->L[𝕜] F₃} {s : 集合 M} {x : M}
  证明: ContDiff.comp_contMDiffWithinAt (F' := (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃))
    (g := ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃) (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_postcomp

nonrec theorem ContMDiffOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s := fun x hx =>
  (hf x hx).clm_postcomp

Depends on / 依赖: ContDiff, ContDiff.comp_contMDiffWithinAt, ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.contDiff, comp_contMDiffWithinAt, contDiff
-/
theorem ContMDiffWithinAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (F' := (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃))
    (g := ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃) (ContinuousLinearMap.contDiff _) hf

nonrec theorem ContMDiffAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  hf.clm_postcomp

nonrec theorem ContMDiffOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) s := fun x hx =>
  (hf x hx).clm_postcomp

/--
theorem `ContMDiff.clm_postcomp` / 定理 `ContMDiff.clm_postcomp`

English:
theorem ContMDiff.clm_postcomp
  given: {f : M -> F₂ ->L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f)
  proof: fun x =>
  (hf x).clm_postcomp

中文:
定理 ContMDiff.clm_postcomp
  条件: {f : M -> F₂ ->L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f)
  证明: fun x =>
  (hf x).clm_postcomp
-/
theorem ContMDiff.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n f) :
    ContMDiff I 𝓘(𝕜, (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) n
      (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) := fun x =>
  (hf x).clm_postcomp

/--
theorem `ContMDiffWithinAt.clm_comp` / 定理 `ContMDiffWithinAt.clm_comp`

English:
theorem ContMDiffWithinAt.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M}
  proof: ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (contDiff_fst.clm_comp contDiff_snd) (hg.prodMk_space hf)

中文:
定理 ContMDiffWithinAt.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : 集合 M} {x : M}
  证明: ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (contDiff_fst.clm_comp contDiff_snd) (hg.prodMk_space hf)

Depends on / 依赖: ContDiff, ContDiff.comp_contMDiffWithinAt, clm_comp, comp_contMDiffWithinAt, contDiff_fst, contDiff_fst.clm_comp, contDiff_snd, hg.prodMk_space, prodMk_space
-/
theorem ContMDiffWithinAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n (fun x => (g x).comp (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (contDiff_fst.clm_comp contDiff_snd) (hg.prodMk_space hf)

/--
theorem `ContMDiffAt.clm_comp` / 定理 `ContMDiffAt.clm_comp`

English:
theorem ContMDiffAt.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
  proof: (hg.contMDiffWithinAt.clm_comp hf.contMDiffWithinAt).contMDiffAt Filter.univ_mem

中文:
定理 ContMDiffAt.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
  证明: (hg.contMDiffWithinAt.clm_comp hf.contMDiffWithinAt).contMDiffAt Filter.univ_mem

Depends on / 依赖: Filter, Filter.univ_mem, clm_comp, contMDiffAt, contMDiffWithinAt, hf.contMDiffWithinAt, hg.contMDiffWithinAt.clm_comp, univ_mem
-/
theorem ContMDiffAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n (fun x => (g x).comp (f x)) x :=
  (hg.contMDiffWithinAt.clm_comp hf.contMDiffWithinAt).contMDiffAt Filter.univ_mem

/--
theorem `ContMDiffOn.clm_comp` / 定理 `ContMDiffOn.clm_comp`

English:
theorem ContMDiffOn.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M}
  proof: fun x hx =>
  (hg x hx).clm_comp (hf x hx)

中文:
定理 ContMDiffOn.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : 集合 M}
  证明: fun x hx =>
  (hg x hx).clm_comp (hf x hx)
-/
theorem ContMDiffOn.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n (fun x => (g x).comp (f x)) s := fun x hx =>
  (hg x hx).clm_comp (hf x hx)

/--
theorem `ContMDiff.clm_comp` / 定理 `ContMDiff.clm_comp`

English:
theorem ContMDiff.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
  proof: fun x => (hg x).clm_comp (hf x)

中文:
定理 ContMDiff.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
  证明: fun x => (hg x).clm_comp (hf x)

Depends on / 依赖: clm_comp
-/
theorem ContMDiff.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₃) n fun x => (g x).comp (f x) := fun x => (hg x).clm_comp (hf x)

/--
theorem `ContMDiffWithinAt.clm_apply` / 定理 `ContMDiffWithinAt.clm_apply`

English:
theorem ContMDiffWithinAt.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M}
  proof: ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply ContDiff.contDiffAt; exact contDiff_fst.clm_apply contDiff_snd) (hg.prodMk_space hf)
    (by simp_rw [preimage_univ, subset_univ])

中文:
定理 ContMDiffWithinAt.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : 集合 M} {x : M}
  证明: ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply ContDiff.contDiffAt; exact contDiff_fst.clm_apply contDiff_snd) (hg.prodMk_space hf)
    (by simp_rw [preimage_univ, subset_univ])

Depends on / 依赖: ContDiff, ContDiff.contDiffAt, ContDiffWithinAt, ContDiffWithinAt.comp_contMDiffWithinAt, clm_apply, comp_contMDiffWithinAt, contDiffAt, contDiff_fst, contDiff_fst.clm_apply, contDiff_snd, hg.prodMk_space, preimage_univ, prodMk_space, simp_rw, subset_univ
-/
theorem ContMDiffWithinAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s x :=
  ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply ContDiff.contDiffAt; exact contDiff_fst.clm_apply contDiff_snd) (hg.prodMk_space hf)
    (by simp_rw [preimage_univ, subset_univ])

/-- Applying a linear map to a vector is smooth. Version in vector spaces. For
versions in nontrivial vector bundles, see `ContMDiffAt.clm_apply_of_inCoordinates` and
`ContMDiffAt.clm_bundle_apply`. -/
nonrec theorem ContMDiffAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) x :=
  hg.clm_apply hf

/--
theorem `ContMDiffOn.clm_apply` / 定理 `ContMDiffOn.clm_apply`

English:
theorem ContMDiffOn.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M}
  proof: fun x hx => (hg x hx).clm_apply (hf x hx)

中文:
定理 ContMDiffOn.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : 集合 M}
  证明: fun x hx => (hg x hx).clm_apply (hf x hx)

Depends on / 依赖: clm_apply
-/
theorem ContMDiffOn.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s := fun x hx => (hg x hx).clm_apply (hf x hx)

/--
theorem `ContMDiff.clm_apply` / 定理 `ContMDiff.clm_apply`

English:
theorem ContMDiff.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
  proof: fun x => (hg x).clm_apply (hf x)

中文:
定理 ContMDiff.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
  证明: fun x => (hg x).clm_apply (hf x)

Depends on / 依赖: clm_apply
-/
theorem ContMDiff.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g) (hf : ContMDiff I 𝓘(𝕜, F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂) n fun x => g x (f x) := fun x => (hg x).clm_apply (hf x)

/--
theorem `ContMDiffWithinAt.cle_arrowCongr` / 定理 `ContMDiffWithinAt.cle_arrowCongr`

English:
theorem ContMDiffWithinAt.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  proof: show ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

nonrec theorem ContMDiffAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x)
    (hg : ContMDiffAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x :=
  hf.cle_arrowCongr hg

中文:
定理 ContMDiffWithinAt.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  证明: show ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

nonrec theorem ContMDiffAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x)
    (hg : ContMDiffAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x :=
  hf.cle_arrowCongr hg

Depends on / 依赖: ContMDiffWithinAt, clm_comp, clm_postcomp, clm_precomp, hf.clm_precomp, hg.clm_postcomp, postcomp, precomp
-/
theorem ContMDiffWithinAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
    {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) s x)
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) s x :=
  show ContMDiffWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

nonrec theorem ContMDiffAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x)
    (hg : ContMDiffAt I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x :=
  hf.cle_arrowCongr hg

/--
theorem `ContMDiffOn.cle_arrowCongr` / 定理 `ContMDiffOn.cle_arrowCongr`

English:
theorem ContMDiffOn.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M}
  proof: fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)

中文:
定理 ContMDiffOn.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : 集合 M}
  证明: fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)
-/
theorem ContMDiffOn.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) s)
    (hg : ContMDiffOn I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄)) s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) s := fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)

/--
theorem `ContMDiff.cle_arrowCongr` / 定理 `ContMDiff.cle_arrowCongr`

English:
theorem ContMDiff.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  proof: fun x =>
  (hf x).cle_arrowCongr (hg x)

中文:
定理 ContMDiff.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  证明: fun x =>
  (hf x).cle_arrowCongr (hg x)
-/
theorem ContMDiff.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
    (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₁) n (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)))
    (hg : ContMDiff I 𝓘(𝕜, F₃ ->L[𝕜] F₄) n (fun x => (g x : F₃ ->L[𝕜] F₄))) :
    ContMDiff I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) n
      (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) := fun x =>
  (hf x).cle_arrowCongr (hg x)

/--
theorem `ContMDiffWithinAt.clm_prodMap` / 定理 `ContMDiffWithinAt.clm_prodMap`

English:
theorem ContMDiffWithinAt.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
  proof: ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).contDiff
    (hg.prodMk_space hf)

nonrec theorem ContMDiffAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) x :=
  hg.clm_prodMap hf

中文:
定理 ContMDiffWithinAt.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : 集合 M}
  证明: ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).contDiff
    (hg.prodMk_space hf)

nonrec theorem ContMDiffAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) x :=
  hg.clm_prodMap hf

Depends on / 依赖: ContDiff, ContDiff.comp_contMDiffWithinAt, ContinuousLinearMap, ContinuousLinearMap.prodMapL, comp_contMDiffWithinAt, contDiff, hg.prodMk_space, prodMap, prodMapL, prodMk_space
-/
theorem ContMDiffWithinAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
    {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).contDiff
    (hg.prodMk_space hf)

nonrec theorem ContMDiffAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) x :=
  hg.clm_prodMap hf

/--
theorem `ContMDiffOn.clm_prodMap` / 定理 `ContMDiffOn.clm_prodMap`

English:
theorem ContMDiffOn.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
  proof: fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)

中文:
定理 ContMDiffOn.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : 集合 M}
  证明: fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)
-/
theorem ContMDiffOn.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s := fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)

/--
theorem `ContMDiff.clm_prodMap` / 定理 `ContMDiff.clm_prodMap`

English:
theorem ContMDiff.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
  proof: fun x =>
  (hg x).clm_prodMap (hf x)

中文:
定理 ContMDiff.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
  证明: fun x =>
  (hg x).clm_prodMap (hf x)
-/
theorem ContMDiff.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
    (hg : ContMDiff I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ ->L[𝕜] F₄) n f) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂ ->L[𝕜] F₃ × F₄) n fun x => (g x).prodMap (f x) := fun x =>
  (hg x).clm_prodMap (hf x)
