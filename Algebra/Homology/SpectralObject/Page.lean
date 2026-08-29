/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.ComposableArrows.Three

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is to introduce the homology `X.E` of the short complex `X.shortComplex`
`(X.H n₀).obj (mk₁ f₃) ⟶ (X.H n₁).obj (mk₁ f₂) ⟶ (X.H n₂).obj (mk₁ f₁)`
when `f₁`, `f₂` and `f₃` are composable morphisms in `ι` and the
equalities `n₀ + 1 = n₁` and `n₁ + 1 = n₂` hold (both maps in the
short complex are given by `X.δ`). All the relevant objects in the
spectral sequence attached to spectral objects can be defined
in terms of this homology `X.E`: the objects in all pages, including
the page at infinity.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : Int)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
/--
Definition of `shortComplex` / `shortComplex` 的定义

English:
definition shortComplex
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ f₂ f₃ n₀ n₁
  g := X.δ f₁ f₂ n₁ n₂

中文:
定义 shortComplex
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ f₂ f₃ n₀ n₁
  g := X.δ f₁ f₂ n₁ n₂

Depends on / 依赖: ShortComplex
-/
def shortComplex (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ f₂ f₃ n₀ n₁
  g := X.δ f₁ f₂ n₁ n₂

/--
Definition of `E` / `E` 的定义

English:
definition E
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homology

中文:
定义 E
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homology

Depends on / 依赖: X.shortComplex, homology, shortComplex
-/
noncomputable def E (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) : C :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homology

/--
lemma `isZero_E_of_isZero_H` / 引理 `isZero_E_of_isZero_H`

English:
lemma isZero_E_of_isZero_H
  statement: (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
  proof: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

中文:
引理 isZero_E_of_isZero_H
  结论: (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
  证明: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

Depends on / 依赖: IsZero, ShortComplex, ShortComplex.exact_of_isZero_X, X.shortComplex, exact_iff_isZero_homology, shortComplex
-/
lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (X.E f₁ f₂ f₃ n₀ n₁ n₂) :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')
  (n₀ n₁ n₂ : Int)

/-- The functoriality of `shortComplex` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
/--
Definition of `shortComplexMap` / `shortComplexMap` 的定义

English:
definition shortComplexMap
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

中文:
定义 shortComplexMap
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

Depends on / 依赖: X.shortComplex, naturality, shortComplex
-/
def shortComplexMap (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ ⟶
      X.shortComplex f₁' f₂' f₃' n₀ n₁ n₂ where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `shortComplexMap_id` / 引理 `shortComplexMap_id`

English:
lemma shortComplexMap_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  ext
  all_goals dsimp; convert! (X.H _).map_id _; cat_disch

中文:
引理 shortComplexMap_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  ext
  all_goals dsimp; convert! (X.H _).map_id _; cat_disch

Depends on / 依赖: X.shortComplexMap, all_goals, cat_disch, convert, map_id, shortComplexMap
-/
lemma shortComplexMap_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  ext
  all_goals dsimp; convert! (X.H _).map_id _; cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc, simp]
/--
lemma `shortComplexMap_comp` / 引理 `shortComplexMap_comp`

English:
lemma shortComplexMap_comp
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

中文:
引理 shortComplexMap_comp
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

Depends on / 依赖: Functor, Functor.map_comp, X.shortComplexMap, all_goals, cat_disch, map_comp, shortComplexMap
-/
lemma shortComplexMap_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.shortComplexMap f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: ShortComplex.homologyMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂)

@[simp]

中文:
定义 map
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: ShortComplex.homologyMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂)

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap, X.shortComplexMap, homologyMap, shortComplexMap
-/
noncomputable def map (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  dsimp only [map]
  simp [shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

中文:
引理 map_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  dsimp only [map]
  simp [shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_id, X.map, homologyMap_id, shortComplexMap_id
-/
lemma map_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  dsimp only [map]
  simp [shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

中文:
引理 map_comp
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_comp, X.map, homologyMap_comp, shortComplexMap_comp
-/
lemma map_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.map f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_map` / 引理 `isIso_map`

English:
lemma isIso_map
  proof: by
  have : IsIso (shortComplexMap X f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂) := by
    apply +allowSynthFailures ShortComplex.isIso_of_isIso <;> assumption
  dsimp [map]
  infer_instance

中文:
引理 isIso_map
  证明: by
  have : IsIso (shortComplexMap X f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂) := by
    apply +allowSynthFailures ShortComplex.isIso_of_isIso <;> assumption
  dsimp [map]
  infer_instance

Depends on / 依赖: ShortComplex, ShortComplex.isIso_of_isIso, X.map, allowSynthFailures, infer_instance, isIso_of_isIso, shortComplexMap
-/
lemma isIso_map
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) := by
  have : IsIso (shortComplexMap X f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂) := by
    apply +allowSynthFailures ShortComplex.isIso_of_isIso <;> assumption
  dsimp [map]
  infer_instance

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/--
lemma `δ_eq_zero_of_isIso₁` / 引理 `δ_eq_zero_of_isIso₁`

English:
lemma δ_eq_zero_of_isIso₁
  given: (hf : IsIso f) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁

中文:
引理 δ_eq_zero_of_isIso₁
  条件: (hf : IsIso f) (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁

Depends on / 依赖: Preadditive, Preadditive.IsIso.comp_left_eq_zero, X.zero, comp_left_eq_zero
-/
lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁

/--
lemma `δ_eq_zero_of_isIso₂` / 引理 `δ_eq_zero_of_isIso₂`

English:
lemma δ_eq_zero_of_isIso₂
  given: (hg : IsIso g) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ f g _ rfl n₀ n₁

中文:
引理 δ_eq_zero_of_isIso₂
  条件: (hg : IsIso g) (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ f g _ rfl n₀ n₁

Depends on / 依赖: Preadditive, Preadditive.IsIso.comp_right_eq_zero, X.zero, comp_right_eq_zero
-/
lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ f g _ rfl n₀ n₁

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isZero_H_obj_of_isIso` / 引理 `isZero_H_obj_of_isIso`

English:
lemma isZero_H_obj_of_isIso
  given: {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : Int)
  proof: by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero]; rw [← Functor.map_id]; rw [← h]
  congr 1
  cat_disch

中文:
引理 isZero_H_obj_of_isIso
  条件: {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : 整数)
  证明: by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero]; rw [← Functor.map_id]; rw [← h]
  congr 1
  cat_disch

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, IsZero, IsZero.iff_id_eq_zero, IsZero.of_iso, Iso.refl, X.zero, cat_disch, e.symm, iff_id_eq_zero, mapIso, map_comp, map_id, of_iso
-/
lemma isZero_H_obj_of_isIso {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : Int) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero]; rw [← Functor.map_id]; rw [← h]
  congr 1
  cat_disch

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : Int)

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`. -/
@[simps]
/--
Definition of `leftHomologyDataShortComplex` / `leftHomologyDataShortComplex` 的定义

English:
definition leftHomologyDataShortComplex
  body: by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).zero) =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ :=
    Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)
  exact {
    K := X.cycles f₁ f₂ n₁
    H := cokernel 

中文:
定义 leftHomologyDataShortComplex
  定义体: by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).zero) =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ :=
    Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)
  exact {
    K := X.cycles f₁ f₂ n₁
    H := cokernel 

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, KernelFork, KernelFork.of, LeftHomologyData, X.cycles, X.iCycles, X.kernelSequenceCycles_exact, X.shortComplex, cokernel, cycles, fIsKernel, hi.fac, hi.lift, hom_ext, iCycles, kernelSequenceCycles_exact, shortComplex
-/
noncomputable def leftHomologyDataShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).LeftHomologyData := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).zero) =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ :=
    Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)
  exact {
    K := X.cycles f₁ f₂ n₁
    H := cokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁)
    i := X.iCycles f₁ f₂ n₁
    π := cokernel.π _
    wi := by simp
    hi := hi
    wπ := by rw [this]; simp
    hπ := by
      refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (cokernelIsCokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Cofork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `leftHomologyDataShortComplex_f'` / 引理 `leftHomologyDataShortComplex_f'`

English:
lemma leftHomologyDataShortComplex_f'
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)

中文:
引理 leftHomologyDataShortComplex_f'
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, X.kernelSequenceCycles_exact, X.leftHomologyDataShortComplex, fIsKernel, hi.fac, hom_ext, kernelSequenceCycles_exact, leftHomologyDataShortComplex
-/
lemma leftHomologyDataShortComplex_f' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f' =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)

/--
Definition of `cyclesIso` / `cyclesIso` 的定义

English:
definition cyclesIso
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]

中文:
定义 cyclesIso
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]

Depends on / 依赖: X.cycles, X.leftHomologyDataShortComplex, X.shortComplex, cycles, cyclesIso, leftHomologyDataShortComplex, shortComplex
-/
noncomputable def cyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).cycles ≅ X.cycles f₁ f₂ n₁ :=
  (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]
/--
lemma `cyclesIso_inv_i` / 引理 `cyclesIso_inv_i`

English:
lemma cyclesIso_inv_i
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]

中文:
引理 cyclesIso_inv_i
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, X.cyclesIso, X.iCycles, X.shortComplex, cyclesIso, cyclesIso_inv_comp_iCycles, iCycles, shortComplex
-/
lemma cyclesIso_inv_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles = X.iCycles f₁ f₂ n₁ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
/--
lemma `cyclesIso_hom_i` / 引理 `cyclesIso_hom_i`

English:
lemma cyclesIso_hom_i
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

中文:
引理 cyclesIso_hom_i
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

Depends on / 依赖: LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i, X.cyclesIso, X.iCycles, X.shortComplex, cyclesIso, cyclesIso_hom_comp_i, iCycles, shortComplex
-/
lemma cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.iCycles f₁ f₂ n₁ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

/--
Definition of `πE` / `πE` 的定义

English:
definition πE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ

中文:
定义 πE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ

Depends on / 依赖: X.cycles, X.cyclesIso, X.shortComplex, cycles, cyclesIso, shortComplex
-/
noncomputable def πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cycles f₁ f₂ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ

set_option backward.isDefEq.respectTransparency false in
deriving instance Epi for πE

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `δToCycles_cyclesIso_inv` / 引理 `δToCycles_cyclesIso_inv`

English:
lemma δToCycles_cyclesIso_inv
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

中文:
引理 δToCycles_cyclesIso_inv
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

Depends on / 依赖: X.cyclesIso, X.shortComplex, cancel_mono, cyclesIso, iCycles, shortComplex, toCycles
-/
lemma δToCycles_cyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles := by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `δToCycles_πE` / 引理 `δToCycles_πE`

English:
lemma δToCycles_πE
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [πE]

中文:
引理 δToCycles_πE
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [πE]
-/
lemma δToCycles_πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  simp [πE]

/-- The (exact) sequence `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/--
Definition of `cokernelSequenceCyclesE` / `cokernelSequenceCyclesE` 的定义

English:
definition cokernelSequenceCyclesE
  body: ShortComplex.mk _ _ (X.δToCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

中文:
定义 cokernelSequenceCyclesE
  定义体: ShortComplex.mk _ _ (X.δToCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
noncomputable def cokernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δToCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency false in
/-- The short complex `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃)` identifies
to the cokernel sequence of the definition of the homology of the short
complex `shortComplex` as a cokernel of `ShortComplex.toCycles`. -/
@[simps!]
/--
Definition of `cokernelSequenceCyclesEIso` / `cokernelSequenceCyclesEIso` 的定义

English:
definition cokernelSequenceCyclesEIso
  body: ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])

中文:
定义 cokernelSequenceCyclesEIso
  定义体: ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])

Depends on / 依赖: Iso.refl, ShortComplex, ShortComplex.isoMk, ShortComplex.mk, X.cokernelSequenceCyclesE, X.cyclesIso, X.shortComplex, cokernelSequenceCyclesE, cyclesIso, shortComplex
-/
noncomputable def cokernelSequenceCyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅ ShortComplex.mk _ _
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])

/--
lemma `cokernelSequenceCyclesE_exact` / 引理 `cokernelSequenceCyclesE_exact`

English:
lemma cokernelSequenceCyclesE_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

中文:
引理 cokernelSequenceCyclesE_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_g_is_cokernel, ShortComplex.exact_of_iso, ShortComplex.homologyIsCokernel, X.cokernelSequenceCyclesE, X.cokernelSequenceCyclesEIso, cokernelSequenceCyclesE, cokernelSequenceCyclesEIso, exact_of_g_is_cokernel, exact_of_iso, homologyIsCokernel
-/
lemma cokernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`. -/
@[simps]
/--
Definition of `rightHomologyDataShortComplex` / `rightHomologyDataShortComplex` 的定义

English:
definition rightHomologyDataShortComplex
  body: by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).zero) =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ :=
    Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)
  exact {
    Q := X.opcyc

中文:
定义 rightHomologyDataShortComplex
  定义体: by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).zero) =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ :=
    Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)
  exact {
    Q := X.opcyc

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, CokernelCofork, CokernelCofork.of, IsColimit, RightHomologyData, X.cokernelSequenceOpcycles_exact, X.opcycles, X.pOpcycles, X.shortComplex, cokernelSequenceOpcycles_exact, gIsCokernel, hom_ext, hp.desc, hp.fac, kernel, opcycles, pOpcycles, shortComplex
-/
noncomputable def rightHomologyDataShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).RightHomologyData := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).zero) =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ :=
    Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)
  exact {
    Q := X.opcycles f₂ f₃ n₁
    H := kernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂)
    p := X.pOpcycles f₂ f₃ n₁
    ι := kernel.ι _
    wp := by simp
    hp := hp
    wι := by rw [this]; simp
    hι := by
      refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (kernelIsKernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Fork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightHomologyDataShortComplex_g'` / 引理 `rightHomologyDataShortComplex_g'`

English:
lemma rightHomologyDataShortComplex_g'
  proof: by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)

中文:
引理 rightHomologyDataShortComplex_g'
  证明: by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, X.cokernelSequenceOpcycles_exact, X.rightHomologyDataShortComplex, cokernelSequenceOpcycles_exact, gIsCokernel, hom_ext, hp.fac, rightHomologyDataShortComplex
-/
lemma rightHomologyDataShortComplex_g'
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g' =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)

/--
Definition of `opcyclesIso` / `opcyclesIso` 的定义

English:
definition opcyclesIso
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcyclesIso

@[reassoc (attr := simp)]

中文:
定义 opcyclesIso
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcyclesIso

@[reassoc (attr := simp)]

Depends on / 依赖: X.opcycles, X.rightHomologyDataShortComplex, X.shortComplex, opcycles, opcyclesIso, rightHomologyDataShortComplex, shortComplex
-/
noncomputable def opcyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcycles ≅ X.opcycles f₂ f₃ n₁ :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcyclesIso

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesIso_hom` / 引理 `p_opcyclesIso_hom`

English:
lemma p_opcyclesIso_hom
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]

中文:
引理 p_opcyclesIso_hom
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]

Depends on / 依赖: RightHomologyData, ShortComplex, ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom, X.opcyclesIso, X.pOpcycles, X.shortComplex, opcyclesIso, pOpcycles, pOpcycles_comp_opcyclesIso_hom, shortComplex
-/
lemma p_opcyclesIso_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles ≫
      (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    X.pOpcycles f₂ f₃ n₁ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesIso_inv` / 引理 `p_opcyclesIso_inv`

English:
lemma p_opcyclesIso_inv
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).p_comp_opcyclesIso_inv

中文:
引理 p_opcyclesIso_inv
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).p_comp_opcyclesIso_inv

Depends on / 依赖: X.opcyclesIso, X.pOpcycles, X.rightHomologyDataShortComplex, X.shortComplex, opcyclesIso, pOpcycles, p_comp_opcyclesIso_inv, rightHomologyDataShortComplex, shortComplex
-/
lemma p_opcyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₂ f₃ n₁ ≫ (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).p_comp_opcyclesIso_inv

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ιE` / `ιE` 的定义

English:
definition ιE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom
  deriving Mono

中文:
定义 ιE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom
  deriving Mono

Depends on / 依赖: X.opcycles, X.opcyclesIso, X.shortComplex, opcycles, opcyclesIso, shortComplex
-/
noncomputable def ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.opcycles f₂ f₃ n₁ :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom
  deriving Mono

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opcyclesIso_hom_δFromOpcycles` / 引理 `opcyclesIso_hom_δFromOpcycles`

English:
lemma opcyclesIso_hom_δFromOpcycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [← cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]

中文:
引理 opcyclesIso_hom_δFromOpcycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [← cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]

Depends on / 依赖: X.opcyclesIso, X.shortComplex, cancel_epi, fromOpcycles, opcyclesIso, pOpcycles, shortComplex
-/
lemma opcyclesIso_hom_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).fromOpcycles := by
  simp [← cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιE_δFromOpcycles` / 引理 `ιE_δFromOpcycles`

English:
lemma ιE_δFromOpcycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [ιE]

中文:
引理 ιE_δFromOpcycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [ιE]
-/
lemma ιE_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ = 0 := by
  simp [ιE]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `πE_ιE` / 引理 `πE_ιE`

English:
lemma πE_ιE
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [πE, ιE]

中文:
引理 πE_ιE
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [πE, ιE]

Depends on / 依赖: X.iCycles, X.pOpcycles, iCycles, pOpcycles
-/
lemma πE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.iCycles f₁ f₂ n₁ ≫ X.pOpcycles f₂ f₃ n₁ := by
  simp [πE, ιE]

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)`. -/
@[simps]
/--
Definition of `kernelSequenceOpcyclesE` / `kernelSequenceOpcyclesE` 的定义

English:
definition kernelSequenceOpcyclesE
  body: ShortComplex.mk _ _ (X.ιE_δFromOpcycles f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

中文:
定义 kernelSequenceOpcyclesE
  定义体: ShortComplex.mk _ _ (X.ιE_δFromOpcycles f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
noncomputable def kernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.ιE_δFromOpcycles f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency false in
/-- The short complex `E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)` identifies
to the kernel sequence of the definition of the homology of the short
complex `shortComplex` as a kernel of `ShortComplex.fromOpcycles`. -/
@[simps!]
/--
Definition of `kernelSequenceOpcyclesEIso` / `kernelSequenceOpcyclesEIso` 的定义

English:
definition kernelSequenceOpcyclesEIso
  body: Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (Iso.refl _) (by simp [ιE]) (by simp))

中文:
定义 kernelSequenceOpcyclesEIso
  定义体: Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (Iso.refl _) (by simp [ιE]) (by simp))

Depends on / 依赖: Iso.refl, Iso.symm, ShortComplex, ShortComplex.isoMk, ShortComplex.mk, X.kernelSequenceOpcyclesE, X.opcyclesIso, X.shortComplex, kernelSequenceOpcyclesE, opcyclesIso, shortComplex
-/
noncomputable def kernelSequenceOpcyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅
      ShortComplex.mk _ _
        (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (Iso.refl _) (by simp [ιE]) (by simp))

/--
lemma `kernelSequenceOpcyclesE_exact` / 引理 `kernelSequenceOpcyclesE_exact`

English:
lemma kernelSequenceOpcyclesE_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

中文:
引理 kernelSequenceOpcyclesE_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_f_is_kernel, ShortComplex.exact_of_iso, ShortComplex.homologyIsKernel, X.kernelSequenceOpcyclesE, X.kernelSequenceOpcyclesEIso, exact_of_f_is_kernel, exact_of_iso, homologyIsKernel, kernelSequenceOpcyclesE, kernelSequenceOpcyclesEIso
-/
lemma kernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

/-- The (exact) sequence `H^n(f₁) ⊞ H^{n-1}(f₃) ⟶ H^n(f₁ ≫ f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/--
Definition of `cokernelSequenceE` / `cokernelSequenceE` 的定义

English:
definition cokernelSequenceE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ f₁₂ f₃ n₀ n₁)
  g := X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂

中文:
定义 cokernelSequenceE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ f₁₂ f₃ n₀ n₁)
  g := X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂

Depends on / 依赖: ShortComplex, X.toCycles, biprod, biprod.desc, toCycles
-/
noncomputable def cokernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ f₁₂ f₃ n₀ n₁)
  g := X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
lemma `cokernelSequenceE_exact` / 引理 `cokernelSequenceE_exact`

English:
lemma cokernelSequenceE_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using! hx₂)
  dsimp at y₁ hy₁
  let z := π₁ 

中文:
引理 cokernelSequenceE_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using! hx₂)
  dsimp at y₁ hy₁
  let z := π₁ 

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, X.cokernelSequenceCyclesE_exact, X.cokernelSequenceE, X.exact, X.toCycles, cokernelSequenceCyclesE_exact, cokernelSequenceE, exact_iff_exact_up_to_refinements, exact_up_to_refinements, toCycles
-/
lemma cokernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using! hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ f₁₂ f₃ n₀ n₁
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ f₁ f₂ f₁₂ h₁₂ n₁).exact_up_to_refinements z (by
      have : z ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using! this =≫ X.iCycles f₁ f₂ n₁)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (hn₁ : n₀ + 1 = n₁) (h' : X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ x = 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `descE` / `descE` 的定义

English:
definition descE
  signature: (hn₂ : n₁ + 1 = n₂ := by lia)
  body: (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).desc x (by cat_disch)

中文:
定义 descE
  签名: (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).desc x (by cat_disch)

Depends on / 依赖: X.cokernelSequenceE_exact, cat_disch, cokernelSequenceE_exact
-/
noncomputable def descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ A :=
  (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).desc x (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `toCycles_πE_descE` / 引理 `toCycles_πE_descE`

English:
lemma toCycles_πE_descE
  given: (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

中文:
引理 toCycles_πE_descE
  条件: (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

Depends on / 依赖: Category, Category.assoc, X.cokernelSequenceE_exact, X.descE, X.toCycles, cokernelSequenceE_exact, g_desc, toCycles
-/
lemma toCycles_πE_descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.descE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ x h hn₁ h' hn₂ = x := by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

end

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ H^n(f₂ ≫ f₃) ⟶ H^n(f₃) ⊞ H^{n+1}(f₁)`. -/
@[simps]
/--
Definition of `kernelSequenceE` / `kernelSequenceE` 的定义

English:
definition kernelSequenceE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE f₁ f₂ f₃ n₀ n₁ n₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ f₁ f₂₃ n₁ n₂)
  zero := by ext <;> simp

中文:
定义 kernelSequenceE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE f₁ f₂ f₃ n₀ n₁ n₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ f₁ f₂₃ n₁ n₂)
  zero := by ext <;> simp

Depends on / 依赖: ShortComplex, X.fromOpcycles, biprod, biprod.lift, fromOpcycles
-/
noncomputable def kernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE f₁ f₂ f₃ n₀ n₁ n₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ f₁ f₂₃ n₁ n₂)
  zero := by ext <;> simp

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `kernelSequenceE_exact` / 引理 `kernelSequenceE_exact`

English:
lemma kernelSequenceE_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        

中文:
引理 kernelSequenceE_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, X.fromOpcyles_, X.kernelSequenceE, X.kernelSequenceOpcyclesE_exact, X.liftOpcycles, X.liftOpcycles_fromOpcycles_assoc, biprod, biprod.fst, biprod.snd, exact_iff_exact_up_to_refinements, exact_up_to_refinements, kernelSequenceE, kernelSequenceOpcyclesE_exact, liftOpcycles, liftOpcycles_fromOpcycles_assoc
-/
lemma kernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ f₁ f₂ f₃ f₂₃ h₂₃ n₁ n₂]; rw [X.liftOpcycles_fromOpcycles_assoc]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁]; rw [liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (hn₂ : n₁ + 1 = n₂)
  (h' : x ≫ X.δ f₁ f₂₃ n₁ n₂ hn₂ = 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftE` / `liftE` 的定义

English:
definition liftE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).lift x (by cat_disch)

@[reassoc (attr := simp)]

中文:
定义 liftE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).lift x (by cat_disch)

@[reassoc (attr := simp)]

Depends on / 依赖: X.kernelSequenceE_exact, cat_disch, kernelSequenceE_exact
-/
noncomputable def liftE (hn₁ : n₀ + 1 = n₁ := by lia) :
    A ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).lift x (by cat_disch)

@[reassoc (attr := simp)]
/--
lemma `liftE_ιE_fromOpcycles` / 引理 `liftE_ιE_fromOpcycles`

English:
lemma liftE_ιE_fromOpcycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

中文:
引理 liftE_ιE_fromOpcycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

Depends on / 依赖: X.fromOpcycles, X.kernelSequenceE_exact, X.liftE, fromOpcycles, kernelSequenceE_exact, lift_f
-/
lemma liftE_ιE_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.liftE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ x h hn₂ h' hn₁ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ = x := by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

end

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `cyclesIso_inv_cyclesMap` / 引理 `cyclesIso_inv_cyclesMap`

English:
lemma cyclesIso_inv_cyclesMap
  proof: by
  subst hβ
  simp [← cancel_mono (ShortComplex.iCycles _), cyclesMap_i]

中文:
引理 cyclesIso_inv_cyclesMap
  证明: by
  subst hβ
  simp [← cancel_mono (ShortComplex.iCycles _), cyclesMap_i]

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap, ShortComplex.iCycles, X.cyclesIso, X.cyclesMap, X.shortComplexMap, cancel_mono, cyclesIso, cyclesMap, cyclesMap_i, iCycles, shortComplexMap
-/
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)))
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      ShortComplex.cyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) =
    X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ (X.cyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).inv := by
  subst hβ
  simp [← cancel_mono (ShortComplex.iCycles _), cyclesMap_i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `opcyclesMap_opcyclesIso_hom` / 引理 `opcyclesMap_opcyclesIso_hom`

English:
lemma opcyclesMap_opcyclesIso_hom
  proof: by
  subst hγ
  simp [← cancel_epi (ShortComplex.pOpcycles _), p_opcyclesMap]

中文:
引理 opcyclesMap_opcyclesIso_hom
  证明: by
  subst hγ
  simp [← cancel_epi (ShortComplex.pOpcycles _), p_opcyclesMap]

Depends on / 依赖: ShortComplex, ShortComplex.opcyclesMap, ShortComplex.pOpcycles, X.opcyclesIso, X.opcyclesMap, X.shortComplexMap, cancel_epi, cat_disch, opcyclesIso, opcyclesMap, pOpcycles, p_opcyclesMap, shortComplexMap
-/
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.opcyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) ≫
      (X.opcyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  subst hγ
  simp [← cancel_epi (ShortComplex.pOpcycles _), p_opcyclesMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `πE_map` / 引理 `πE_map`

English:
lemma πE_map
  statement: (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : Int)
  proof: by
  simp [πE, map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

中文:
引理 πE_map
  结论: (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : 整数)
  证明: by
  simp [πE, map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

Depends on / 依赖: X.cyclesIso_inv_cyclesMap_assoc, X.cyclesMap, X.map, cat_disch, cyclesIso_inv_cyclesMap_assoc, cyclesMap
-/
lemma πE_map (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : Int)
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ X.πE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  simp [πE, map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_ιE` / 引理 `map_ιE`

English:
lemma map_ιE
  proof: by
  simp [ιE, map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

中文:
引理 map_ιE
  证明: by
  simp [ιE, map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

Depends on / 依赖: X.map, X.opcyclesMap, X.opcyclesMap_opcyclesIso_hom, cat_disch, opcyclesMap, opcyclesMap_opcyclesIso_hom
-/
lemma map_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃') (n₀ n₁ n₂ : Int)
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  simp [ιE, map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : Int)

/--
Definition of `opcyclesToE` / `opcyclesToE` 的定义

English:
definition opcyclesToE
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: X.descOpcycles _ _ _ _ hn₁ (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂) (by simp)

@[reassoc (attr := simp)]

中文:
定义 opcyclesToE
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: X.descOpcycles _ _ _ _ hn₁ (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: X.descOpcycles, X.opcycles, X.toCycles, descOpcycles, opcycles, toCycles
-/
noncomputable def opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcycles f₁₂ f₃ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  X.descOpcycles _ _ _ _ hn₁ (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂) (by simp)

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesToE` / 引理 `p_opcyclesToE`

English:
lemma p_opcyclesToE
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [opcyclesToE]

@[reassoc (attr := simp)]

中文:
引理 p_opcyclesToE
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [opcyclesToE]

@[reassoc (attr := simp)]

Depends on / 依赖: X.opcyclesToE, X.pOpcycles, X.toCycles, opcyclesToE, pOpcycles, toCycles
-/
lemma p_opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₁₂ f₃ n₁ ≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ =
      X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp [opcyclesToE]

@[reassoc (attr := simp)]
/--
lemma `opcyclesToE_ιE` / 引理 `opcyclesToE_ιE`

English:
lemma opcyclesToE_ιE
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simpa [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁)] using (X.p_opcyclesMap ..).symm

中文:
引理 opcyclesToE_ιE
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simpa [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁)] using (X.p_opcyclesMap ..).symm

Depends on / 依赖: X.opcyclesMap, X.opcyclesToE, X.pOpcycles, X.p_opcyclesMap, cancel_epi, opcyclesMap, opcyclesToE, pOpcycles, p_opcyclesMap
-/
lemma opcyclesToE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.opcyclesMap f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₁ := by
  simpa [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁)] using (X.p_opcyclesMap ..).symm

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂) :=
  epi_of_epi_fac (X.p_opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps!]
/--
Definition of `cokernelSequenceOpcyclesE` / `cokernelSequenceOpcyclesE` 的定义

English:
definition cokernelSequenceOpcyclesE
  body: (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles f₁₂ f₃ n₁
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n₁
  g := X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

中文:
定义 cokernelSequenceOpcyclesE
  定义体: (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles f₁₂ f₃ n₁
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n₁
  g := X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

Depends on / 依赖: ShortComplex, X.opcycles, X.opcyclesToE, X.pOpcycles, opcycles, opcyclesToE, pOpcycles
-/
noncomputable def cokernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles f₁₂ f₃ n₁
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n₁
  g := X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cokernelSequenceOpcyclesE_exact` / 引理 `cokernelSequenceOpcyclesE_exact`

English:
lemma cokernelSequenceOpcyclesE_exact
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_

中文:
引理 cokernelSequenceOpcyclesE_exact
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_

Depends on / 依赖: Category, Category.assoc, ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, X.cokernelSequenceE_exact, X.cokernelSequenceOpcyclesE, X.opc, X.pOpcycles, cokernelSequenceE_exact, cokernelSequenceOpcyclesE, comp_zero, exact_iff_exact_up_to_refinements, exact_up_to_refinements, pOpcycles, p_opcyclesToE, surjective_up_to_refinements_of_epi
-/
lemma cokernelSequenceOpcyclesE_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements y₂
      (by simpa only [Category.assoc, p_opcyclesToE, hx₂, comp_zero]
        using! hy₂.symm =≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : exists a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, a, ?_⟩
  simp [Category.assoc, hy₂, reassoc_of% hy₁, Preadditive.add_comp, δ_pOpcycles,
    comp_zero, add_zero]

-- TODO: add dual statement to `cokernelSequenceOpcyclesE_exact`?

/--
Definition of `EToCycles` / `EToCycles` 的定义

English:
definition EToCycles
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: X.liftCycles _ _ _ _ hn₂
    (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) (by simp)

@[reassoc (attr := simp)]

中文:
定义 EToCycles
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: X.liftCycles _ _ _ _ hn₂
    (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: X.cycles, X.fromOpcycles, X.liftCycles, cycles, fromOpcycles, liftCycles
-/
noncomputable def EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.cycles f₁ f₂₃ n₁ :=
  X.liftCycles _ _ _ _ hn₂
    (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) (by simp)

@[reassoc (attr := simp)]
/--
lemma `EToCycles_i` / 引理 `EToCycles_i`

English:
lemma EToCycles_i
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [EToCycles]

@[reassoc (attr := simp)]

中文:
引理 EToCycles_i
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [EToCycles]

@[reassoc (attr := simp)]

Depends on / 依赖: EToCycles, X.EToCycles, X.fromOpcycles, X.iCycles, fromOpcycles, iCycles
-/
lemma EToCycles_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.iCycles f₁ f₂₃ n₁ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ := by
  simp [EToCycles]

@[reassoc (attr := simp)]
/--
lemma `πE_EToCycles` / 引理 `πE_EToCycles`

English:
lemma πE_EToCycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm

中文:
引理 πE_EToCycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm

Depends on / 依赖: CoeOut, EToCycles, LieSubmodule, Submodule, X.EToCycles, X.cyclesMap, X.cyclesMap_i, X.iCycles, cancel_mono, coeSubmodule, cyclesMap, cyclesMap_i, iCycles
-/
lemma πE_EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ := by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂) :=
  mono_of_mono_fac (X.EToCycles_i f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃) ⟶ H^n(f₃)`. -/
@[simps!]
/--
Definition of `kernelSequenceCyclesE` / `kernelSequenceCyclesE` 的定义

English:
definition kernelSequenceCyclesE
  body: X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := X.cycles f₁ f₂₃ n₁
  X₃ := (X.H n₁).obj (mk₁ f₃)
  f := X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂
  g := X.iCycles f₁ f₂₃ n₁ ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)

中文:
定义 kernelSequenceCyclesE
  定义体: X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := X.cycles f₁ f₂₃ n₁
  X₃ := (X.H n₁).obj (mk₁ f₃)
  f := X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂
  g := X.iCycles f₁ f₂₃ n₁ ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)

Depends on / 依赖: EToCycles, ShortComplex, X.EToCycles, X.cycles, X.iCycles, cycles, iCycles
-/
noncomputable def kernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := X.cycles f₁ f₂₃ n₁
  X₃ := (X.H n₁).obj (mk₁ f₃)
  f := X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂
  g := X.iCycles f₁ f₂₃ n₁ ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `kernelSequenceCyclesE_exact` / 引理 `kernelSequenceCyclesE_exact`

English:
lemma kernelSequenceCyclesE_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [←

中文:
引理 kernelSequenceCyclesE_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [←

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, X.iCycles, X.kernelSequenceCyclesE, X.kernelSequenceE_exact, cancel_mono, cat_disch, exact_iff_exact_up_to_refinements, exact_up_to_refinements, iCycles, kernelSequenceCyclesE, kernelSequenceE_exact
-/
lemma kernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [← cancel_mono (X.iCycles ..)]⟩

end

section

variable {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An homology data for `X.shortComplex n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
/--
Definition of `homologyDataIdId` / `homologyDataIdId` 的定义

English:
definition homologyDataIdId
  signature: (n₀ n₁ n₂ : Int)
  body: (ShortComplex.HomologyData.ofZeros (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂))

中文:
定义 homologyDataIdId
  签名: (n₀ n₁ n₂ : 整数)
  定义体: (ShortComplex.HomologyData.ofZeros (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂))

Depends on / 依赖: HomologyData, ShortComplex, ShortComplex.HomologyData.ofZeros, X.shortComplex, ofZeros, shortComplex
-/
noncomputable def homologyDataIdId (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂))

/--
Definition of `EIsoH` / `EIsoH` 的定义

English:
definition EIsoH
  signature: (n₀ n₁ n₂ : Int)
  body: (X.homologyDataIdId ..).left.homologyIso

中文:
定义 EIsoH
  签名: (n₀ n₁ n₂ : 整数)
  定义体: (X.homologyDataIdId ..).left.homologyIso

Depends on / 依赖: X.homologyDataIdId, homologyDataIdId, homologyIso, left.homologyIso
-/
noncomputable def EIsoH (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.homologyDataIdId ..).left.homologyIso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `EIsoH_hom_naturality` / 引理 `EIsoH_hom_naturality`

English:
lemma EIsoH_hom_naturality
  proof: by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

中文:
引理 EIsoH_hom_naturality
  证明: by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

Depends on / 依赖: LeftHomologyMapData, ShortComplex, ShortComplex.LeftHomologyMapData.ofZeros, X.EIsoH, X.map, X.shortComplexMap, cat_disch, homologyMap_comm, naturality, ofZeros, shortComplexMap
-/
lemma EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (n₀ n₁ n₂ : Int)
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map]) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.EIsoH f' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

end

section

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : Int)

/--
Definition of `cyclesIsoH` / `cyclesIsoH` 的定义

English:
definition cyclesIsoH
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: (X.cyclesIso (𝟙 i₀) f (𝟙 i₁) (n₀ - 1) n₀ n₁ (by lia) hn₁).symm ≪≫
    (X.homologyDataIdId ..).left.cyclesIso

中文:
定义 cyclesIsoH
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: (X.cyclesIso (𝟙 i₀) f (𝟙 i₁) (n₀ - 1) n₀ n₁ (by lia) hn₁).symm ≪≫
    (X.homologyDataIdId ..).left.cyclesIso

Depends on / 依赖: X.cycles, X.cyclesIso, X.homologyDataIdId, cycles, cyclesIso, homologyDataIdId, left.cyclesIso
-/
noncomputable def cyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cycles (𝟙 i₀) f n₀ ≅ (X.H n₀).obj (mk₁ f) :=
  (X.cyclesIso (𝟙 i₀) f (𝟙 i₁) (n₀ - 1) n₀ n₁ (by lia) hn₁).symm ≪≫
    (X.homologyDataIdId ..).left.cyclesIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `cyclesIsoH_inv` / 引理 `cyclesIsoH_inv`

English:
lemma cyclesIsoH_inv
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀)]; rw [toCycles_i]
  dsimp [cyclesIsoH]
  simp only [Category.assoc, cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 cyclesIsoH_inv
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀)]; rw [toCycles_i]
  dsimp [cyclesIsoH]
  simp only [Category.assoc, cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_id, LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, X.cyclesIsoH, X.iCycles, X.toCycles, cancel_mono, cat_disch, cyclesIsoH, cyclesIso_hom_i, cyclesIso_inv_comp_iCycles, homologyDataIdId_left_i, iCycles, map_id, toCycles, toCycles_i
-/
lemma cyclesIsoH_inv (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).inv = X.toCycles (𝟙 _) f f (by simp) n₀ := by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀)]; rw [toCycles_i]
  dsimp [cyclesIsoH]
  simp only [Category.assoc, cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoH_hom_inv_id` / 引理 `cyclesIsoH_hom_inv_id`

English:
lemma cyclesIsoH_hom_inv_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 cyclesIsoH_hom_inv_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: X.cyclesIsoH, X.toCycles, cyclesIsoH, hom_inv_id, toCycles
-/
lemma cyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).hom ≫
      X.toCycles (𝟙 _) f f (by simp) n₀ = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoH_inv_hom_id` / 引理 `cyclesIsoH_inv_hom_id`

English:
lemma cyclesIsoH_inv_hom_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

中文:
引理 cyclesIsoH_inv_hom_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

Depends on / 依赖: X.cyclesIsoH, X.toCycles, cyclesIsoH, inv_hom_id, toCycles
-/
lemma cyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles (𝟙 _) f f (by simp) n₀ ≫
      (X.cyclesIsoH f n₀ n₁ hn₁).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

/--
Definition of `opcyclesIsoH` / `opcyclesIsoH` 的定义

English:
definition opcyclesIsoH
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: (X.opcyclesIso (𝟙 i₀) f (𝟙 i₁) n₀ n₁ (n₁ + 1) hn₁ (by lia)).symm ≪≫
    (X.homologyDataIdId ..).right.opcyclesIso

中文:
定义 opcyclesIsoH
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: (X.opcyclesIso (𝟙 i₀) f (𝟙 i₁) n₀ n₁ (n₁ + 1) hn₁ (by lia)).symm ≪≫
    (X.homologyDataIdId ..).right.opcyclesIso

Depends on / 依赖: X.homologyDataIdId, X.opcycles, X.opcyclesIso, homologyDataIdId, opcycles, opcyclesIso, right.opcyclesIso
-/
noncomputable def opcyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f (𝟙 i₁) n₁ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.opcyclesIso (𝟙 i₀) f (𝟙 i₁) n₀ n₁ (n₁ + 1) hn₁ (by lia)).symm ≪≫
    (X.homologyDataIdId ..).right.opcyclesIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `opcyclesIsoH_hom` / 引理 `opcyclesIsoH_hom`

English:
lemma opcyclesIsoH_hom
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁)]; rw [p_fromOpcycles]
  dsimp [opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 opcyclesIsoH_hom
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁)]; rw [p_fromOpcycles]
  dsimp [opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_id, RightHomologyData, ShortComplex, ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom, X.fromOpcycles, X.opcyclesIsoH, X.pOpcycles, cancel_epi, cat_disch, fromOpcycles, homologyDataIdId_right_p, map_id, opcyclesIsoH, pOpcycles, pOpcycles_comp_opcyclesIso_hom, p_fromOpcycles, p_opcyclesIso_inv_assoc
-/
lemma opcyclesIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).hom = X.fromOpcycles f (𝟙 _) f (by simp) n₁ := by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁)]; rw [p_fromOpcycles]
  dsimp [opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoH_hom_inv_id` / 引理 `opcyclesIsoH_hom_inv_id`

English:
lemma opcyclesIsoH_hom_inv_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 opcyclesIsoH_hom_inv_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: X.fromOpcycles, X.opcyclesIsoH, fromOpcycles, hom_inv_id, opcyclesIsoH
-/
lemma opcyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ ≫
        (X.opcyclesIsoH f n₀ n₁ hn₁).inv = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoH_inv_hom_id` / 引理 `opcyclesIsoH_inv_hom_id`

English:
lemma opcyclesIsoH_inv_hom_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).inv_hom_id

中文:
引理 opcyclesIsoH_inv_hom_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).inv_hom_id

Depends on / 依赖: X.fromOpcycles, X.opcyclesIsoH, fromOpcycles, inv_hom_id, opcyclesIsoH
-/
lemma opcyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).inv ≫
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).inv_hom_id

end

section

variable (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cyclesIsoH_hom_EIsoH_inv` / 引理 `cyclesIsoH_hom_EIsoH_inv`

English:
lemma cyclesIsoH_hom_EIsoH_inv
  proof: by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id];

中文:
引理 cyclesIsoH_hom_EIsoH_inv
  证明: by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id];

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Functor, Functor.map_id, Iso.inv_hom_id, X.cyclesIso, X.homologyDataIdId, X.iCycles, X.toCycles, cancel_mono, cat_disch, comp_id, cyclesIso, cyclesIso_hom_i, cyclesIso_inv_comp_iCycles, h.cyclesIso.inv, h.cyclesIso_inv_comp_iCycles, homologyDataIdId, iCycles
-/
lemma cyclesIsoH_hom_EIsoH_inv :
    (X.cyclesIsoH f n₁ n₂ hn₂).hom ≫ (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).inv =
      X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]; rw [← cancel_mono (X.iCycles ..)]; rw [Category.assoc]; rw [cyclesIso_hom_i ..]; rw [h.cyclesIso_inv_comp_iCycles]; rw [toCycles_i]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₀ = n₁ - 1 := by lia
  rw [← cancel_epi (X.cyclesIsoH f n₁ n₂ hn₂).inv]; rw [cyclesIsoH_inv ..]; rw [cyclesIsoH_inv_hom_id_assoc ..]
  dsimp [EIsoH]
  rw [← cancel_epi h.π]; rw [h.π_comp_homologyIso_inv]
  simp [πE, h, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `EIsoH_hom_opcyclesIsoH_inv` / 引理 `EIsoH_hom_opcyclesIsoH_inv`

English:
lemma EIsoH_hom_opcyclesIsoH_inv
  proof: by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (X.pOpcycl

中文:
引理 EIsoH_hom_opcyclesIsoH_inv
  证明: by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (X.pOpcycl

Depends on / 依赖: Functor, Functor.map_id, Iso.inv_hom_id_assoc, X.fromOpcycles, X.homologyDataIdId, X.opcyclesI, X.opcyclesIso, X.pOpcycles, cancel_epi, cancel_mono, cat_disch, fromOpcycles, h.right.opcyclesIso.hom, h.right.pOpcycles_comp_opcyclesIso_hom, homologyDataIdId, inv_hom_id_assoc, map_id, opcyclesI, opcyclesIso, pOpcycles
-/
lemma EIsoH_hom_opcyclesIsoH_inv :
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.opcyclesIsoH f n₀ n₁ hn₁).inv =
      X.ιE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (X.pOpcycles ..)]; rw [p_opcyclesIso_inv_assoc ..]; rw [h.right.pOpcycles_comp_opcyclesIso_hom]; rw [p_fromOpcycles]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₂ = n₁ + 1 := by lia
  rw [← cancel_mono (X.opcyclesIsoH f n₀ n₁ hn₁).hom]; rw [Category.assoc]; rw [opcyclesIsoH_hom ..]; rw [opcyclesIsoH_inv_hom_id ..]
  dsimp [EIsoH, ιE]
  rw [Category.assoc]; rw [← this]; rw [h.left_homologyIso_eq_right_homologyIso_trans_iso_symm]; rw [← ShortComplex.RightHomologyData.homologyIso_hom_comp_ι]
  simp [h]

end

section

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

@[reassoc (attr := simp)]
/--
lemma `opcyclesMap_threeδ₂Toδ₁_opcyclesToE` / 引理 `opcyclesMap_threeδ₂Toδ₁_opcyclesToE`

English:
lemma opcyclesMap_threeδ₂Toδ₁_opcyclesToE
  proof: by
  rw [← cancel_epi (X.pOpcycles ..)]; rw [comp_zero]; rw [p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

中文:
引理 opcyclesMap_threeδ₂Toδ₁_opcyclesToE
  证明: by
  rw [← cancel_epi (X.pOpcycles ..)]; rw [comp_zero]; rw [p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

Depends on / 依赖: X.opcyclesMap, X.opcyclesToE, X.pOpcycles, cancel_epi, comp_zero, opcyclesMap, opcyclesToE, pOpcycles, p_opcyclesMap_assoc
-/
lemma opcyclesMap_threeδ₂Toδ₁_opcyclesToE
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) n₁ ≫
      X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  rw [← cancel_epi (X.pOpcycles ..)]; rw [comp_zero]; rw [p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

/-- The short exact sequence
`0 ⟶ opZ^(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ H^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/--
Definition of `shortComplexOpcyclesThreeδ₂Toδ₁` / `shortComplexOpcyclesThreeδ₂Toδ₁` 的定义

English:
definition shortComplexOpcyclesThreeδ₂Toδ₁
  body: ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

中文:
定义 shortComplexOpcyclesThreeδ₂Toδ₁
  定义体: ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.opcyclesMap_three
-/
noncomputable def shortComplexOpcyclesThreeδ₂Toδ₁
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  replace hx := hx =≫ X.fromOpcycles f₁₂ f₃ _ rfl n₁
  rw [zero_comp]; rw [Category.assoc]; rw [X.opcyclesMap_fromOpcycles f₁ f₂₃ f₁₂ f₃ (f₁₂ ≫ f₃) (by cat_disch) _ rfl _ (𝟙 _) n₁
      (by simp) (by cat_disch)]; rw [Functor.map_id]; rw [Category.comp_id] at hx
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁₂ ≫ f₃) (by cat_disch) n₁)]; rw [hx]; rw [zero_comp]

set_option backward.defeqAttrib.useBackward true in
instance (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shortComplexOpcyclesThreeδ₂Toδ₁_exact` / 引理 `shortComplexOpcyclesThreeδ₂Toδ₁_exact`

English:
lemma shortComplexOpcyclesThreeδ₂Toδ₁_exact
  proof: by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [X.p_opcyclesMap _ 

中文:
引理 shortComplexOpcyclesThreeδ₂Toδ₁_exact
  证明: by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [X.p_opcyclesMap _ 

Depends on / 依赖: Category, Category.comp_id, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, X.cokernelSequenceOpcycl, X.cokernelSequenceOpcyclesE, X.pOpcycles, X.p_opcyclesMap, X.shortComplexOpcyclesThree, cokernelSequenceOpcycl, cokernelSequenceOpcyclesE, comp_id, exact_iff_of_epi_of_isIso_of_mono, pOpcycles, p_opcyclesMap
-/
lemma shortComplexOpcyclesThreeδ₂Toδ₁_exact
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [X.p_opcyclesMap _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂)] }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂

/--
lemma `shortComplexOpcyclesThreeδ₂Toδ₁_shortExact` / 引理 `shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`

English:
lemma shortComplexOpcyclesThreeδ₂Toδ₁_shortExact
  proof: X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

中文:
引理 shortComplexOpcyclesThreeδ₂Toδ₁_shortExact
  证明: X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

Depends on / 依赖: ShortExact, X.shortComplexOpcyclesThree
-/
lemma shortComplexOpcyclesThreeδ₂Toδ₁_shortExact
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).ShortExact where
  exact := X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

end

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  {i₀' i₁' i₂' i₃' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `opcyclesToE_map` / 引理 `opcyclesToE_map`

English:
lemma opcyclesToE_map
  statement: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
  proof: by
  rw [← cancel_mono (X.ιE ..)]; rw [Category.assoc]; rw [Category.assoc]; rw [opcyclesToE_ιE ..]; rw [← cancel_epi (X.pOpcycles ..)]; rw [p_opcyclesToE_assoc ..]; rw [X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..]; rw [πE_ιE .

中文:
引理 opcyclesToE_map
  结论: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
  证明: by
  rw [← cancel_mono (X.ιE ..)]; rw [Category.assoc]; rw [Category.assoc]; rw [opcyclesToE_ιE ..]; rw [← cancel_epi (X.pOpcycles ..)]; rw [p_opcyclesToE_assoc ..]; rw [X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..]; rw [πE_ιE .

Depends on / 依赖: Category, Category.assoc, X.map, X.opcyclesMap, X.opcyclesToE, X.pOpcycles, cancel_epi, cancel_mono, cat_disch, opcyclesMap, opcyclesToE, pOpcycles, p_opcyclesToE_assoc
-/
lemma opcyclesToE_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
    (n₀ n₁ n₂ : Int) (h₀ : β.app 0 = α.app 0 := by cat_disch) (h₁ : β.app 1 = α.app 2 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map _ _ _ _ _ _ α _ _ _ =
      X.opcyclesMap _ _ _ _ β _ ≫ X.opcyclesToE f₁' f₂' f₃' f₁₂' h₁₂' n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_mono (X.ιE ..)]; rw [Category.assoc]; rw [Category.assoc]; rw [opcyclesToE_ιE ..]; rw [← cancel_epi (X.pOpcycles ..)]; rw [p_opcyclesToE_assoc ..]; rw [X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..]; rw [πE_ιE ..]; rw [X.cyclesMap_i_assoc ..]; rw [toCycles_i_assoc]; rw [X.p_opcyclesMap_assoc ..]; rw [X.p_opcyclesMap ..]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]
  congr 2
  ext
  · simpa [h₀] using naturality' α 0 1
  · simp [h₁]

end SpectralObject

end Abelian

end CategoryTheory
