/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Harmonic Functions

This file defines harmonic functions on real, finite-dimensional, inner product spaces `E`.
-/

@[expose] public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
  {f f₁ f₂ : E -> F}
  {x : E} {s t : Set E} {c : Real}

open Topology Laplacian

namespace InnerProductSpace

/-!
## Definition
-/

variable (f x) in
/--
Definition of `HarmonicAt` / `HarmonicAt` 的定义

English:
definition HarmonicAt
  body: (ContDiffAt Real 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

中文:
定义 HarmonicAt
  定义体: (ContDiffAt Real 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

Depends on / 依赖: ContDiffAt
-/
def HarmonicAt := (ContDiffAt Real 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

variable (f s) in
/--
Definition of `HarmonicOnNhd` / `HarmonicOnNhd` 的定义

English:
definition HarmonicOnNhd
  body: forall x in s, HarmonicAt f x

中文:
定义 HarmonicOnNhd
  定义体: forall x in s, HarmonicAt f x

Depends on / 依赖: HarmonicAt
-/
def HarmonicOnNhd := forall x in s, HarmonicAt f x

/--
lemma `HarmonicOnNhd.contDiffOn` / 引理 `HarmonicOnNhd.contDiffOn`

English:
lemma HarmonicOnNhd.contDiffOn
  given: (hf : HarmonicOnNhd f s)
  statement: ContDiffOn Real 2 f s
  proof: fun x hx => (hf x hx).1.contDiffWithinAt

中文:
引理 HarmonicOnNhd.contDiffOn
  条件: (hf : HarmonicOnNhd f s)
  结论: ContDiffOn 实数 2 f s
  证明: fun x hx => (hf x hx).1.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt
-/
lemma HarmonicOnNhd.contDiffOn (hf : HarmonicOnNhd f s) : ContDiffOn Real 2 f s :=
  fun x hx => (hf x hx).1.contDiffWithinAt

/-!
## Elementary Properties
-/

/--
theorem `harmonicAt_congr_nhds` / 定理 `harmonicAt_congr_nhds`

English:
theorem harmonicAt_congr_nhds
  given: {f₁ f₂ : E -> F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂)
  proof: by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

中文:
定理 harmonicAt_congr_nhds
  条件: {f₁ f₂ : E -> F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂)
  证明: by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

Depends on / 依赖: congr_of_eventuallyEq, h.symm, laplacian_congr_nhds
-/
theorem harmonicAt_congr_nhds {f₁ f₂ : E -> F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

/--
theorem `HarmonicAt.eventually` / 定理 `HarmonicAt.eventually`

English:
theorem HarmonicAt.eventually
  given: {f : E -> F} {x : E} (h : HarmonicAt f x)
  proof: by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

中文:
定理 HarmonicAt.eventually
  条件: {f : E -> F} {x : E} (h : HarmonicAt f x)
  证明: by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

Depends on / 依赖: eventually, eventually_nhds, filter_upwards
-/
theorem HarmonicAt.eventually {f : E -> F} {x : E} (h : HarmonicAt f x) :
    forallᶠ y in 𝓝 x, HarmonicAt f y := by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

/--
theorem `harmonicAt_const` / 定理 `harmonicAt_const`

English:
theorem harmonicAt_const
  given: (c : F)
  proof: ⟨by fun_prop, by simp⟩

中文:
定理 harmonicAt_const
  条件: (c : F)
  证明: ⟨by fun_prop, by simp⟩
-/
@[simp] theorem harmonicAt_const (c : F) :
    HarmonicAt (fun _ => c) x := ⟨by fun_prop, by simp⟩

/--
theorem `harmonicOnNhd_const` / 定理 `harmonicOnNhd_const`

English:
theorem harmonicOnNhd_const
  given: (c : F)
  proof: fun _ _ => by simp

中文:
定理 harmonicOnNhd_const
  条件: (c : F)
  证明: fun _ _ => by simp
-/
@[simp] theorem harmonicOnNhd_const (c : F) :
    HarmonicOnNhd (fun _ => c) s := fun _ _ => by simp

variable (f) in
/--
theorem `isOpen_setOfPred_harmonicAt` / 定理 `isOpen_setOfPred_harmonicAt`

English:
theorem isOpen_setOfPred_harmonicAt
  statement: IsOpen { x : E | HarmonicAt f x }
  proof: isOpen_iff_mem_nhds.2 (fun _ hx => hx.eventually)

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_harmonicAt := isOpen_setOfPred_harmonicAt

中文:
定理 isOpen_setOfPred_harmonicAt
  结论: IsOpen { x : E | HarmonicAt f x }
  证明: isOpen_iff_mem_nhds.2 (fun _ hx => hx.eventually)

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_harmonicAt := isOpen_setOfPred_harmonicAt

Depends on / 依赖: eventually, hx.eventually, isOpen_iff_mem_nhds
-/
theorem isOpen_setOfPred_harmonicAt : IsOpen { x : E | HarmonicAt f x } :=
  isOpen_iff_mem_nhds.2 (fun _ hx => hx.eventually)

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_harmonicAt := isOpen_setOfPred_harmonicAt

/--
lemma `HarmonicOnNhd.mono` / 引理 `HarmonicOnNhd.mono`

English:
lemma HarmonicOnNhd.mono
  given: (h : HarmonicOnNhd f s) (hst : t subseteq s)
  proof: fun x hx => h x (hst hx)

中文:
引理 HarmonicOnNhd.mono
  条件: (h : HarmonicOnNhd f s) (hst : t subseteq s)
  证明: fun x hx => h x (hst hx)
-/
lemma HarmonicOnNhd.mono (h : HarmonicOnNhd f s) (hst : t subseteq s) :
    HarmonicOnNhd f t := fun x hx => h x (hst hx)

/--
theorem `HarmonicOnNhd.continuousOn` / 定理 `HarmonicOnNhd.continuousOn`

English:
theorem HarmonicOnNhd.continuousOn
  given: (h : HarmonicOnNhd f s)
  proof: fun x hx => (h x hx).1.continuousAt.continuousWithinAt (s := s)

中文:
定理 HarmonicOnNhd.continuousOn
  条件: (h : HarmonicOnNhd f s)
  证明: fun x hx => (h x hx).1.continuousAt.continuousWithinAt (s := s)
-/
@[fun_prop] theorem HarmonicOnNhd.continuousOn (h : HarmonicOnNhd f s) :
    ContinuousOn f s :=
  fun x hx => (h x hx).1.continuousAt.continuousWithinAt (s := s)

/-!
## Vector Space Structure
-/

/--
theorem `HarmonicAt.add` / 定理 `HarmonicAt.add`

English:
theorem HarmonicAt.add
  given: (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x)
  proof: by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplacian_add_nhds h₂.1, h₁.2, h₂.2]
    simp_all

中文:
定理 HarmonicAt.add
  条件: (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x)
  证明: by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplacian_add_nhds h₂.1, h₁.2, h₂.2]
    simp_all

Depends on / 依赖: filter_upwards, laplacian_add_nhds
-/
theorem HarmonicAt.add (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ + f₂) x := by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplacian_add_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
theorem `HarmonicAt.sub` / 定理 `HarmonicAt.sub`

English:
theorem HarmonicAt.sub
  given: (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x)
  proof: by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

中文:
定理 HarmonicAt.sub
  条件: (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x)
  证明: by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

Depends on / 依赖: filter_upwards, laplacian_sub_nhds
-/
theorem HarmonicAt.sub (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ - f₂) x := by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

/--
theorem `HarmonicOnNhd.add` / 定理 `HarmonicOnNhd.add`

English:
theorem HarmonicOnNhd.add
  given: (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s)
  proof: fun x hx => (h₁ x hx).add (h₂ x hx)

中文:
定理 HarmonicOnNhd.add
  条件: (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s)
  证明: fun x hx => (h₁ x hx).add (h₂ x hx)
-/
theorem HarmonicOnNhd.add (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ + f₂) s := fun x hx => (h₁ x hx).add (h₂ x hx)

/--
theorem `HarmonicOnNhd.sub` / 定理 `HarmonicOnNhd.sub`

English:
theorem HarmonicOnNhd.sub
  given: (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s)
  proof: fun x hx => (h₁ x hx).sub (h₂ x hx)

中文:
定理 HarmonicOnNhd.sub
  条件: (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s)
  证明: fun x hx => (h₁ x hx).sub (h₂ x hx)
-/
theorem HarmonicOnNhd.sub (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ - f₂) s := fun x hx => (h₁ x hx).sub (h₂ x hx)

/--
theorem `HarmonicAt.neg` / 定理 `HarmonicAt.neg`

English:
theorem HarmonicAt.neg
  given: (h : HarmonicAt f x)
  proof: by
  constructor
  · simpa using! h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

中文:
定理 HarmonicAt.neg
  条件: (h : HarmonicAt f x)
  证明: by
  constructor
  · simpa using! h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

Depends on / 依赖: filter_upwards, laplacian_neg
-/
theorem HarmonicAt.neg (h : HarmonicAt f x) :
    HarmonicAt (-f) x := by
  constructor
  · simpa using! h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

/--
theorem `HarmonicOnNhd.neg` / 定理 `HarmonicOnNhd.neg`

English:
theorem HarmonicOnNhd.neg
  given: (h : HarmonicOnNhd f s)
  proof: fun x hx => (h x hx).neg

中文:
定理 HarmonicOnNhd.neg
  条件: (h : HarmonicOnNhd f s)
  证明: fun x hx => (h x hx).neg
-/
theorem HarmonicOnNhd.neg (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (-f) s := fun x hx => (h x hx).neg

/--
theorem `HarmonicAt.const_smul` / 定理 `HarmonicAt.const_smul`

English:
theorem HarmonicAt.const_smul
  given: (h : HarmonicAt f x)
  proof: by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplacian_smul_nhds c h.1, h.2]
    simp_all

中文:
定理 HarmonicAt.const_smul
  条件: (h : HarmonicAt f x)
  证明: by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplacian_smul_nhds c h.1, h.2]
    simp_all

Depends on / 依赖: const_smul, filter_upwards, laplacian_smul_nhds
-/
theorem HarmonicAt.const_smul (h : HarmonicAt f x) :
    HarmonicAt (c • f) x := by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplacian_smul_nhds c h.1, h.2]
    simp_all

/--
theorem `HarmonicOnNhd.const_smul` / 定理 `HarmonicOnNhd.const_smul`

English:
theorem HarmonicOnNhd.const_smul
  given: (h : HarmonicOnNhd f s)
  proof: fun x hx => (h x hx).const_smul

中文:
定理 HarmonicOnNhd.const_smul
  条件: (h : HarmonicOnNhd f s)
  证明: fun x hx => (h x hx).const_smul

Depends on / 依赖: const_smul
-/
theorem HarmonicOnNhd.const_smul (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (c • f) s := fun x hx => (h x hx).const_smul

/-!
## Compatibility with Linear Maps
-/

/--
theorem `HarmonicAt.comp_CLM` / 定理 `HarmonicAt.comp_CLM`

English:
theorem HarmonicAt.comp_CLM
  given: (h : HarmonicAt f x) (l : F ->L[Real] G)
  proof: by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplacian_CLM_comp_left_nhds (l := l), h.2]
    simp_all

中文:
定理 HarmonicAt.comp_CLM
  条件: (h : HarmonicAt f x) (l : F ->L[实数] G)
  证明: by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplacian_CLM_comp_left_nhds (l := l), h.2]
    simp_all

Depends on / 依赖: continuousLinearMap_comp, filter_upwards, laplacian_CLM_comp_left_nhds
-/
theorem HarmonicAt.comp_CLM (h : HarmonicAt f x) (l : F ->L[Real] G) :
    HarmonicAt (l ∘ f) x := by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplacian_CLM_comp_left_nhds (l := l), h.2]
    simp_all

/--
theorem `HarmonicOnNhd.comp_CLM` / 定理 `HarmonicOnNhd.comp_CLM`

English:
theorem HarmonicOnNhd.comp_CLM
  given: (h : HarmonicOnNhd f s) (l : F ->L[Real] G)
  proof: fun x hx => (h x hx).comp_CLM l

中文:
定理 HarmonicOnNhd.comp_CLM
  条件: (h : HarmonicOnNhd f s) (l : F ->L[实数] G)
  证明: fun x hx => (h x hx).comp_CLM l

Depends on / 依赖: comp_CLM
-/
theorem HarmonicOnNhd.comp_CLM (h : HarmonicOnNhd f s) (l : F ->L[Real] G) :
    HarmonicOnNhd (l ∘ f) s := fun x hx => (h x hx).comp_CLM l

/--
theorem `harmonicAt_comp_CLE_iff` / 定理 `harmonicAt_comp_CLE_iff`

English:
theorem harmonicAt_comp_CLE_iff
  given: (l : F ≃L[Real] G)
  proof: by
  constructor <;> intro h
  · simpa [Function.comp_def] using h.comp_CLM l.symm.toContinuousLinearMap
  · exact h.comp_CLM l.toContinuousLinearMap

中文:
定理 harmonicAt_comp_CLE_iff
  条件: (l : F ≃L[实数] G)
  证明: by
  constructor <;> intro h
  · simpa [Function.comp_def] using h.comp_CLM l.symm.toContinuousLinearMap
  · exact h.comp_CLM l.toContinuousLinearMap

Depends on / 依赖: Function, Function.comp_def, comp_CLM, comp_def, h.comp_CLM, l.symm.toContinuousLinearMap, l.toContinuousLinearMap, toContinuousLinearMap
-/
theorem harmonicAt_comp_CLE_iff (l : F ≃L[Real] G) :
    HarmonicAt (l ∘ f) x ↔ HarmonicAt f x := by
  constructor <;> intro h
  · simpa [Function.comp_def] using h.comp_CLM l.symm.toContinuousLinearMap
  · exact h.comp_CLM l.toContinuousLinearMap

/--
theorem `harmonicOnNhd_comp_CLE_iff` / 定理 `harmonicOnNhd_comp_CLE_iff`

English:
theorem harmonicOnNhd_comp_CLE_iff
  given: (l : F ≃L[Real] G)
  proof: forall₂_congr fun _ _ => harmonicAt_comp_CLE_iff l

中文:
定理 harmonicOnNhd_comp_CLE_iff
  条件: (l : F ≃L[实数] G)
  证明: forall₂_congr fun _ _ => harmonicAt_comp_CLE_iff l

Depends on / 依赖: harmonicAt_comp_CLE_iff
-/
theorem harmonicOnNhd_comp_CLE_iff (l : F ≃L[Real] G) :
    HarmonicOnNhd (l ∘ f) s ↔ HarmonicOnNhd f s :=
  forall₂_congr fun _ _ => harmonicAt_comp_CLE_iff l

end InnerProductSpace
