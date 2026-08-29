/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes

/-!
# Normalization of morphisms in monoidal categories

This file provides the implementation of the normalization given in
`Mathlib/Tactic/CategoryTheory/Coherence/Normalize.lean`. See this file for more details.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike MonoidalCategory

namespace Mathlib.Tactic.Monoidal

section

universe v u

variable {C : Type u} [Category.{v} C]

variable {f f' g g' h h' i i' j : C}

@[nolint synTaut]
/--
theorem `evalComp_nil_nil` / 定理 `evalComp_nil_nil`

English:
theorem evalComp_nil_nil
  given: {f g h : C} (α : f ≅ g) (β : g ≅ h)
  proof: by
  simp

中文:
定理 evalComp_nil_nil
  条件: {f g h : C} (α : f ≅ g) (β : g ≅ h)
  证明: by
  simp
-/
theorem evalComp_nil_nil {f g h : C} (α : f ≅ g) (β : g ≅ h) :
    (α ≪≫ β).hom = (α ≪≫ β).hom := by
  simp

/--
theorem `evalComp_nil_cons` / 定理 `evalComp_nil_cons`

English:
theorem evalComp_nil_cons
  given: {f g h i j : C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j)
  proof: by
  simp

中文:
定理 evalComp_nil_cons
  条件: {f g h i j : C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j)
  证明: by
  simp
-/
theorem evalComp_nil_cons {f g h i j : C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).hom ≫ η ≫ ηs := by
  simp

/--
theorem `evalComp_cons` / 定理 `evalComp_cons`

English:
theorem evalComp_cons
  statement: {f g h i j : C} (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
  proof: by
  simp [e_ι]

中文:
定理 evalComp_cons
  结论: {f g h i j : C} (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
  证明: by
  simp [e_ι]
-/
theorem evalComp_cons {f g h i j : C} (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
    (e_ι : ηs ≫ θ = ι) :
    (α.hom ≫ η ≫ ηs) ≫ θ = α.hom ≫ η ≫ ι := by
  simp [e_ι]

/--
theorem `eval_comp` / 定理 `eval_comp`

English:
theorem eval_comp
  proof: by
  simp [e_η, e_θ, e_ηθ]

中文:
定理 eval_comp
  证明: by
  simp [e_η, e_θ, e_ηθ]
-/
theorem eval_comp
    {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h}
    (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by
  simp [e_η, e_θ, e_ηθ]

/--
theorem `eval_of` / 定理 `eval_of`

English:
theorem eval_of
  given: (η : f ⟶ g)
  proof: by
  simp

中文:
定理 eval_of
  条件: (η : f ⟶ g)
  证明: by
  simp
-/
theorem eval_of (η : f ⟶ g) :
    η = (Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom := by
  simp

/--
theorem `eval_monoidalComp` / 定理 `eval_monoidalComp`

English:
theorem eval_monoidalComp
  proof: by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

中文:
定理 eval_monoidalComp
  证明: by
  simp [e_η, e_θ, e_αθ, e_ηαθ]
-/
theorem eval_monoidalComp
    {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α.hom ≫ θ = ηαθ := by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

variable [MonoidalCategory C]

@[nolint synTaut]
/--
theorem `evalWhiskerLeft_nil` / 定理 `evalWhiskerLeft_nil`

English:
theorem evalWhiskerLeft_nil
  given: (f : C) {g h : C} (α : g ≅ h)
  proof: by
  simp

中文:
定理 evalWhiskerLeft_nil
  条件: (f : C) {g h : C} (α : g ≅ h)
  证明: by
  simp
-/
theorem evalWhiskerLeft_nil (f : C) {g h : C} (α : g ≅ h) :
    (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom := by
  simp

/--
theorem `evalWhiskerLeft_of_cons` / 定理 `evalWhiskerLeft_of_cons`

English:
theorem evalWhiskerLeft_of_cons
  statement: {f g h i j : C}
  proof: by
  simp [e_θ]

中文:
定理 evalWhiskerLeft_of_cons
  结论: {f g h i j : C}
  证明: by
  simp [e_θ]
-/
theorem evalWhiskerLeft_of_cons {f g h i j : C}
    (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes j} (e_θ : f ◁ ηs = θ) :
    f ◁ (α.hom ≫ η ≫ ηs) = (whiskerLeftIso f α).hom ≫ f ◁ η ≫ θ := by
  simp [e_θ]

/--
theorem `evalWhiskerLeft_comp` / 定理 `evalWhiskerLeft_comp`

English:
theorem evalWhiskerLeft_comp
  statement: {f g h i : C}
  proof: by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]

中文:
定理 evalWhiskerLeft_comp
  结论: {f g h i : C}
  证明: by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]
-/
theorem evalWhiskerLeft_comp {f g h i : C}
    {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ f otimes g otimes i}
    {η₃ : f otimes g otimes h ⟶ (f otimes g) otimes i} {η₄ : (f otimes g) otimes h ⟶ (f otimes g) otimes i}
    (e_η₁ : g ◁ η = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_η₃ : η₂ ≫ (α_ _ _ _).inv = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) :
    (f otimes g) ◁ η = η₄ := by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]

/--
theorem `evalWhiskerLeft_id` / 定理 `evalWhiskerLeft_id`

English:
theorem evalWhiskerLeft_id
  statement: {f g : C} {η : f ⟶ g}
  proof: by
  simp [e_η₁, e_η₂]

中文:
定理 evalWhiskerLeft_id
  结论: {f g : C} {η : f ⟶ g}
  证明: by
  simp [e_η₁, e_η₂]
-/
theorem evalWhiskerLeft_id {f g : C} {η : f ⟶ g}
    {η₁ : f ⟶ 𝟙_ C otimes g} {η₂ : 𝟙_ C otimes f ⟶ 𝟙_ C otimes g}
    (e_η₁ : η ≫ (fun_ _).inv = η₁) (e_η₂ : (fun_ _).hom ≫ η₁ = η₂) :
    𝟙_ C ◁ η = η₂ := by
  simp [e_η₁, e_η₂]

/--
theorem `eval_whiskerLeft` / 定理 `eval_whiskerLeft`

English:
theorem eval_whiskerLeft
  statement: {f g h : C}
  proof: by
  simp [e_η, e_θ]

中文:
定理 eval_whiskerLeft
  结论: {f g h : C}
  证明: by
  simp [e_η, e_θ]
-/
theorem eval_whiskerLeft {f g h : C}
    {η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h}
    (e_η : η = η') (e_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [e_η, e_θ]

/--
theorem `eval_whiskerRight` / 定理 `eval_whiskerRight`

English:
theorem eval_whiskerRight
  statement: {f g h : C}
  proof: by
  simp [e_η, e_θ]

中文:
定理 eval_whiskerRight
  结论: {f g h : C}
  证明: by
  simp [e_η, e_θ]
-/
theorem eval_whiskerRight {f g h : C}
    {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h}
    (e_η : η = η') (e_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [e_η, e_θ]

/--
theorem `eval_tensorHom` / 定理 `eval_tensorHom`

English:
theorem eval_tensorHom
  statement: {f g h i : C}
  proof: by
  simp [e_η, e_θ, e_ι]

@[nolint synTaut]

中文:
定理 eval_tensorHom
  结论: {f g h i : C}
  证明: by
  simp [e_η, e_θ, e_ι]

@[nolint synTaut]
-/
theorem eval_tensorHom {f g h i : C}
    {η η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i}
    (e_η : η = η') (e_θ : θ = θ') (e_ι : η' otimesₘ θ' = ι) :
    η otimesₘ θ = ι := by
  simp [e_η, e_θ, e_ι]

@[nolint synTaut]
/--
theorem `evalWhiskerRight_nil` / 定理 `evalWhiskerRight_nil`

English:
theorem evalWhiskerRight_nil
  given: {f g : C} (α : f ≅ g) (h : C)
  proof: by
  simp

中文:
定理 evalWhiskerRight_nil
  条件: {f g : C} (α : f ≅ g) (h : C)
  证明: by
  simp
-/
theorem evalWhiskerRight_nil {f g : C} (α : f ≅ g) (h : C) :
    (whiskerRightIso α h).hom = (whiskerRightIso α h).hom := by
  simp

/--
theorem `evalWhiskerRight_cons_of_of` / 定理 `evalWhiskerRight_cons_of_of`

English:
theorem evalWhiskerRight_cons_of_of
  statement: {f g h i j : C}
  proof: by
  simp_all

中文:
定理 evalWhiskerRight_cons_of_of
  结论: {f g h i j : C}
  证明: by
  simp_all
-/
theorem evalWhiskerRight_cons_of_of {f g h i j : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j ⟶ i otimes j}
    {η₁ : g otimes j ⟶ h otimes j} {η₂ : g otimes j ⟶ i otimes j} {η₃ : f otimes j ⟶ i otimes j}
    (e_ηs₁ : ηs ▷ j = ηs₁) (e_η₁ : η ▷ j = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α j).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ j = η₃ := by
  simp_all

/--
theorem `evalWhiskerRight_cons_whisker` / 定理 `evalWhiskerRight_cons_whisker`

English:
theorem evalWhiskerRight_cons_whisker
  statement: {f g h i j k : C}
  proof: by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

中文:
定理 evalWhiskerRight_cons_whisker
  结论: {f g h i j k : C}
  证明: by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]
-/
theorem evalWhiskerRight_cons_whisker {f g h i j k : C}
    {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i ⟶ j}
    {η₁ : h otimes k ⟶ i otimes k} {η₂ : f otimes (h otimes k) ⟶ f otimes (i otimes k)} {ηs₁ : (f otimes i) otimes k ⟶ j otimes k}
    {ηs₂ : f otimes (i otimes k) ⟶ j otimes k} {η₃ : f otimes (h otimes k) ⟶ j otimes k} {η₄ : (f otimes h) otimes k ⟶ j otimes k}
    {η₅ : g otimes k ⟶ j otimes k}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ k = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_ηs₁ : ηs ▷ k = ηs₁) (e_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (e_η₃ : η₂ ≫ ηs₂ = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄)
    (e_η₅ : (whiskerRightIso α k).hom ≫ η₄ = η₅) :
    (α.hom ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

/--
theorem `evalWhiskerRight_comp` / 定理 `evalWhiskerRight_comp`

English:
theorem evalWhiskerRight_comp
  statement: {f f' g h : C}
  proof: by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]

中文:
定理 evalWhiskerRight_comp
  结论: {f f' g h : C}
  证明: by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]
-/
theorem evalWhiskerRight_comp {f f' g h : C}
    {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otimes h ⟶ (f' otimes g) otimes h}
    {η₃ : (f otimes g) otimes h ⟶ f' otimes (g otimes h)} {η₄ : f otimes (g otimes h) ⟶ f' otimes (g otimes h)}
    (e_η₁ : η ▷ g = η₁) (e_η₂ : η₁ ▷ h = η₂)
    (e_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (e_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g otimes h) = η₄ := by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]

/--
theorem `evalWhiskerRight_id` / 定理 `evalWhiskerRight_id`

English:
theorem evalWhiskerRight_id
  statement: {f g : C}
  proof: by
  simp [e_η₁, e_η₂]

中文:
定理 evalWhiskerRight_id
  结论: {f g : C}
  证明: by
  simp [e_η₁, e_η₂]
-/
theorem evalWhiskerRight_id {f g : C}
    {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C}
    (e_η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙_ C = η₂ := by
  simp [e_η₁, e_η₂]

/--
theorem `evalWhiskerRightAux_of` / 定理 `evalWhiskerRightAux_of`

English:
theorem evalWhiskerRightAux_of
  given: {f g : C} (η : f ⟶ g) (h : C)
  proof: by
  simp

中文:
定理 evalWhiskerRightAux_of
  条件: {f g : C} (η : f ⟶ g) (h : C)
  证明: by
  simp
-/
theorem evalWhiskerRightAux_of {f g : C} (η : f ⟶ g) (h : C) :
    η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).hom := by
  simp

/--
theorem `evalWhiskerRightAux_cons` / 定理 `evalWhiskerRightAux_cons`

English:
theorem evalWhiskerRightAux_cons
  statement: {f g h i j : C} {η : g ⟶ h} {ηs : i ⟶ j}
  proof: by
  simp [← e_ηs', ← e_η₁, ← e_η₂, ← e_η₃, MonoidalCategory.tensorHom_def]

中文:
定理 evalWhiskerRightAux_cons
  结论: {f g h i j : C} {η : g ⟶ h} {ηs : i ⟶ j}
  证明: by
  simp [← e_ηs', ← e_η₁, ← e_η₂, ← e_η₃, MonoidalCategory.tensorHom_def]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_def, tensorHom_def
-/
theorem evalWhiskerRightAux_cons {f g h i j : C} {η : g ⟶ h} {ηs : i ⟶ j}
    {ηs' : i otimes f ⟶ j otimes f} {η₁ : g otimes (i otimes f) ⟶ h otimes (j otimes f)}
    {η₂ : g otimes (i otimes f) ⟶ (h otimes j) otimes f} {η₃ : (g otimes i) otimes f ⟶ (h otimes j) otimes f}
    (e_ηs' : ηs ▷ f = ηs') (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) otimesₘ ηs' = η₁)
    (e_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (e_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (η otimesₘ ηs) ▷ f = η₃ := by
  simp [← e_ηs', ← e_η₁, ← e_η₂, ← e_η₃, MonoidalCategory.tensorHom_def]

/--
theorem `evalWhiskerRight_cons_of` / 定理 `evalWhiskerRight_cons_of`

English:
theorem evalWhiskerRight_cons_of
  statement: {f f' g h i : C} {α : f' ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
  proof: by
  simp_all

中文:
定理 evalWhiskerRight_cons_of
  结论: {f f' g h i : C} {α : f' ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
  证明: by
  simp_all
-/
theorem evalWhiskerRight_cons_of {f f' g h i : C} {α : f' ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {ηs₁ : h otimes f ⟶ i otimes f} {η₁ : g otimes f ⟶ h otimes f} {η₂ : g otimes f ⟶ i otimes f}
    {η₃ : f' otimes f ⟶ i otimes f}
    (e_ηs₁ : ηs ▷ f = ηs₁) (e_η₁ : η ▷ f = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α f).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ f = η₃ := by
  simp_all

/--
theorem `evalHorizontalCompAux_of` / 定理 `evalHorizontalCompAux_of`

English:
theorem evalHorizontalCompAux_of
  given: {f g h i : C} (η : f ⟶ g) (θ : h ⟶ i)
  proof: by
  simp

中文:
定理 evalHorizontalCompAux_of
  条件: {f g h i : C} (η : f ⟶ g) (θ : h ⟶ i)
  证明: by
  simp
-/
theorem evalHorizontalCompAux_of {f g h i : C} (η : f ⟶ g) (θ : h ⟶ i) :
    η otimesₘ θ = (Iso.refl _).hom ≫ (η otimesₘ θ) ≫ (Iso.refl _).hom := by
  simp

/--
theorem `evalHorizontalCompAux_cons` / 定理 `evalHorizontalCompAux_cons`

English:
theorem evalHorizontalCompAux_cons
  statement: {f f' g g' h i : C} {η : f ⟶ g} {ηs : f' ⟶ g'} {θ : h ⟶ i}
  proof: by
  simp_all

中文:
定理 evalHorizontalCompAux_cons
  结论: {f f' g g' h i : C} {η : f ⟶ g} {ηs : f' ⟶ g'} {θ : h ⟶ i}
  证明: by
  simp_all
-/
theorem evalHorizontalCompAux_cons {f f' g g' h i : C} {η : f ⟶ g} {ηs : f' ⟶ g'} {θ : h ⟶ i}
    {ηθ : f' otimes h ⟶ g' otimes i} {η₁ : f otimes (f' otimes h) ⟶ g otimes (g' otimes i)}
    {ηθ₁ : f otimes (f' otimes h) ⟶ (g otimes g') otimes i} {ηθ₂ : (f otimes f') otimes h ⟶ (g otimes g') otimes i}
    (e_ηθ : ηs otimesₘ θ = ηθ) (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) otimesₘ ηθ = η₁)
    (e_ηθ₁ : η₁ ≫ (α_ _ _ _).inv = ηθ₁) (e_ηθ₂ : (α_ _ _ _).hom ≫ ηθ₁ = ηθ₂) :
    (η otimesₘ ηs) otimesₘ θ = ηθ₂ := by
  simp_all

/--
theorem `evalHorizontalCompAux'_whisker` / 定理 `evalHorizontalCompAux'_whisker`

English:
theorem evalHorizontalCompAux'_whisker
  statement: {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
  proof: by
  simp only [← e_ηθ, ← e_η₁, ← e_η₂, ← e_η₃]
  simp [MonoidalCategory.tensorHom_def]

中文:
定理 evalHorizontalCompAux'_whisker
  结论: {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
  证明: by
  simp only [← e_ηθ, ← e_η₁, ← e_η₂, ← e_η₃]
  simp [MonoidalCategory.tensorHom_def]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_def, tensorHom_def
-/
theorem evalHorizontalCompAux'_whisker {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
    {ηθ : g otimes f' ⟶ h otimes g'} {η₁ : f otimes (g otimes f') ⟶ f otimes (h otimes g')}
    {η₂ : f otimes (g otimes f') ⟶ (f otimes h) otimes g'} {η₃ : (f otimes g) otimes f' ⟶ (f otimes h) otimes g'}
    (e_ηθ : η otimesₘ θ = ηθ) (e_η₁ : f ◁ ηθ = η₁)
    (e_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (e_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (f ◁ η) otimesₘ θ = η₃ := by
  simp only [← e_ηθ, ← e_η₁, ← e_η₂, ← e_η₃]
  simp [MonoidalCategory.tensorHom_def]

/--
theorem `evalHorizontalCompAux'_of_whisker` / 定理 `evalHorizontalCompAux'_of_whisker`

English:
theorem evalHorizontalCompAux'_of_whisker
  statement: {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
  proof: by
  simp only [← e_η₁, ← e_ηθ, ← e_ηθ₁, ← e_ηθ₂]
  simp [MonoidalCategory.tensorHom_def]

@[nolint synTaut]

中文:
定理 evalHorizontalCompAux'_of_whisker
  结论: {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
  证明: by
  simp only [← e_η₁, ← e_ηθ, ← e_ηθ₁, ← e_ηθ₂]
  simp [MonoidalCategory.tensorHom_def]

@[nolint synTaut]
-/
theorem evalHorizontalCompAux'_of_whisker {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
    {η₁ : g otimes f ⟶ h otimes f} {ηθ : (g otimes f) otimes f' ⟶ (h otimes f) otimes g'}
    {ηθ₁ : (g otimes f) otimes f' ⟶ h otimes (f otimes g')}
    {ηθ₂ : g otimes (f otimes f') ⟶ h otimes (f otimes g')}
    (e_η₁ : η ▷ f = η₁) (e_ηθ : η₁ otimesₘ ((Iso.refl _).hom ≫ θ ≫ (Iso.refl _).hom) = ηθ)
    (e_ηθ₁ : ηθ ≫ (α_ _ _ _).hom = ηθ₁) (e_ηθ₂ : (α_ _ _ _).inv ≫ ηθ₁ = ηθ₂) :
    η otimesₘ (f ◁ θ) = ηθ₂ := by
  simp only [← e_η₁, ← e_ηθ, ← e_ηθ₁, ← e_ηθ₂]
  simp [MonoidalCategory.tensorHom_def]

@[nolint synTaut]
/--
theorem `evalHorizontalComp_nil_nil` / 定理 `evalHorizontalComp_nil_nil`

English:
theorem evalHorizontalComp_nil_nil
  given: {f g h i : C} (α : f ≅ g) (β : h ≅ i)
  proof: by
  simp

中文:
定理 evalHorizontalComp_nil_nil
  条件: {f g h i : C} (α : f ≅ g) (β : h ≅ i)
  证明: by
  simp
-/
theorem evalHorizontalComp_nil_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) :
    (α otimesᵢ β).hom = (α otimesᵢ β).hom := by
  simp

/--
theorem `evalHorizontalComp_nil_cons` / 定理 `evalHorizontalComp_nil_cons`

English:
theorem evalHorizontalComp_nil_cons
  statement: {f f' g g' h i : C}
  proof: by
  simp_all [MonoidalCategory.tensorHom_def]

中文:
定理 evalHorizontalComp_nil_cons
  结论: {f f' g g' h i : C}
  证明: by
  simp_all [MonoidalCategory.tensorHom_def]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_def, tensorHom_def
-/
theorem evalHorizontalComp_nil_cons {f f' g g' h i : C}
    {α : f ≅ g} {β : f' ≅ g'} {η : g' ⟶ h} {ηs : h ⟶ i}
    {η₁ : g otimes g' ⟶ g otimes h} {ηs₁ : g otimes h ⟶ g otimes i}
    {η₂ : g otimes g' ⟶ g otimes i} {η₃ : f otimes f' ⟶ g otimes i}
    (e_η₁ : g ◁ ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) = η₁)
    (e_ηs₁ : g ◁ ηs = ηs₁) (e_η₂ : η₁ ≫ ηs₁ = η₂)
    (e_η₃ : (α otimesᵢ β).hom ≫ η₂ = η₃) :
    α.hom otimesₘ (β.hom ≫ η ≫ ηs) = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def]

/--
theorem `evalHorizontalComp_cons_nil` / 定理 `evalHorizontalComp_cons_nil`

English:
theorem evalHorizontalComp_cons_nil
  statement: {f f' g g' h i : C}
  proof: by
  simp_all [MonoidalCategory.tensorHom_def']

中文:
定理 evalHorizontalComp_cons_nil
  结论: {f f' g g' h i : C}
  证明: by
  simp_all [MonoidalCategory.tensorHom_def']

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_def, tensorHom_def
-/
theorem evalHorizontalComp_cons_nil {f f' g g' h i : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {β : f' ≅ g'}
    {η₁ : g otimes g' ⟶ h otimes g'} {ηs₁ : h otimes g' ⟶ i otimes g'} {η₂ : g otimes g' ⟶ i otimes g'} {η₃ : f otimes f' ⟶ i otimes g'}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ g' = η₁) (e_ηs₁ : ηs ▷ g' = ηs₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (α otimesᵢ β).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) otimesₘ β.hom = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def']

/--
theorem `evalHorizontalComp_cons_cons` / 定理 `evalHorizontalComp_cons_cons`

English:
theorem evalHorizontalComp_cons_cons
  statement: {f f' g g' h h' i i' : C}
  proof: by
  simp [← e_ηθ, ← e_ηθs, ← e_ηθ₁, ← e_ηθ₂]

中文:
定理 evalHorizontalComp_cons_cons
  结论: {f f' g g' h h' i i' : C}
  证明: by
  simp [← e_ηθ, ← e_ηθs, ← e_ηθ₁, ← e_ηθ₂]
-/
theorem evalHorizontalComp_cons_cons {f f' g g' h h' i i' : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {β : f' ≅ g'} {θ : g' ⟶ h'} {θs : h' ⟶ i'}
    {ηθ : g otimes g' ⟶ h otimes h'} {ηθs : h otimes h' ⟶ i otimes i'}
    {ηθ₁ : g otimes g' ⟶ i otimes i'} {ηθ₂ : f otimes f' ⟶ i otimes i'}
    (e_ηθ : η otimesₘ θ = ηθ) (e_ηθs : ηs otimesₘ θs = ηθs)
    (e_ηθ₁ : ηθ ≫ ηθs = ηθ₁) (e_ηθ₂ : (α otimesᵢ β).hom ≫ ηθ₁ = ηθ₂) :
    (α.hom ≫ η ≫ ηs) otimesₘ (β.hom ≫ θ ≫ θs) = ηθ₂ := by
  simp [← e_ηθ, ← e_ηθs, ← e_ηθ₁, ← e_ηθ₂]

end

open Mor₂Iso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEvalComp MonoidalM
  body: do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    return q(evalComp_nil_nil $α $β)
  mk

中文:
实例 :
  签名: MkEvalComp MonoidalM
  定义体: do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    return q(evalComp_nil_nil $α $β)
  mk
-/
instance : MkEvalComp MonoidalM where
  mkEvalCompNilNil α β := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    return q(evalComp_nil_nil $α $β)
  mkEvalCompNilCons α β η ηs := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($i ⟶ $j) := ηs.e.e
    return q(evalComp_nil_cons $α $β $η $ηs)
  mkEvalCompCons α η ηs θ ι e_ι := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let j ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have θ : Q($i ⟶ $j) := θ.e.e
    have ι : Q($h ⟶ $j) := ι.e.e
    have e_ι : Q($ηs ≫ $θ = $ι) := e_ι
    return q(evalComp_cons $α $η $e_ι)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEvalWhiskerLeft MonoidalM
  body: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← α.srcM
    let h ← α.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have α_e : Q($g_e ≅ $h_e) := α.e
    return q(evalWhiskerLeft_nil $f_e $α_e

中文:
实例 :
  签名: MkEvalWhiskerLeft MonoidalM
  定义体: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← α.srcM
    let h ← α.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have α_e : Q($g_e ≅ $h_e) := α.e
    return q(evalWhiskerLeft_nil $f_e $α_e
-/
instance : MkEvalWhiskerLeft MonoidalM where
  mkEvalWhiskerLeftNil f α := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← α.srcM
    let h ← α.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have α_e : Q($g_e ≅ $h_e) := α.e
    return q(evalWhiskerLeft_nil $f_e $α_e)
  mkEvalWhiskerLeftOfCons f α η ηs θ e_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← α.srcM
    let h ← α.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have α : Q($g ≅ $h) := α.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($i ⟶ $j) := ηs.e.e
    have θ : Q($f otimes $i ⟶ $f otimes $j) := θ.e.e
    have e_θ : Q($f ◁ $ηs = $θ) := e_θ
    return q(evalWhiskerLeft_of_cons $α $η $e_θ)
  mkEvalWhiskerLeftComp f g η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let h ← η.srcM
    let i ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($h ⟶ $i) := η.e.e
    have η₁ : Q($g otimes $h ⟶ $g otimes $i) := η₁.e.e
    have η₂ : Q($f otimes $g otimes $h ⟶ $f otimes $g otimes $i) := η₂.e.e
    have η₃ : Q($f otimes $g otimes $h ⟶ ($f otimes $g) otimes $i) := η₃.e.e
    have η₄ : Q(($f otimes $g) otimes $h ⟶ ($f otimes $g) otimes $i) := η₄.e.e
    have e_η₁ : Q($g ◁ $η = $η₁) := e_η₁
    have e_η₂ : Q($f ◁ $η₁ = $η₂) := e_η₂
    have e_η₃ : Q($η₂ ≫ (α_ _ _ _).inv = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).hom ≫ $η₃ = $η₄) := e_η₄
    return q(evalWhiskerLeft_comp $e_η₁ $e_η₂ $e_η₃ $e_η₄)
  mkEvalWhiskerLeftId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have η₁ : Q($f ⟶ 𝟙_ _ otimes $g) := η₁.e.e
    have η₂ : Q(𝟙_ _ otimes $f ⟶ 𝟙_ _ otimes $g) := η₂.e.e
    have e_η₁ : Q($η ≫ (fun_ _).inv = $η₁) := e_η₁
    have e_η₂ : Q((fun_ _).hom ≫ $η₁ = $η₂) := e_η₂
    return q(evalWhiskerLeft_id $e_η₁ $e_η₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEvalWhiskerRight MonoidalM
  body: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have h : Q($ctx.C) := h.e
    return q(evalWhiskerRightAux_of $η $h)
  mkEvalW

中文:
实例 :
  签名: MkEvalWhiskerRight MonoidalM
  定义体: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have h : Q($ctx.C) := h.e
    return q(evalWhiskerRightAux_of $η $h)
  mkEvalW
-/
instance : MkEvalWhiskerRight MonoidalM where
  mkEvalWhiskerRightAuxOf η h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have h : Q($ctx.C) := h.e
    return q(evalWhiskerRightAux_of $η $h)
  mkEvalWhiskerRightAuxCons f η ηs ηs' η₁ η₂ η₃ e_ηs' e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η.srcM
    let h ← η.tgtM
    let i ← ηs.srcM
    let j ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($i ⟶ $j) := ηs.e.e
    have ηs' : Q($i otimes $f ⟶ $j otimes $f) := ηs'.e.e
    have η₁ : Q($g otimes ($i otimes $f) ⟶ $h otimes ($j otimes $f)) := η₁.e.e
    have η₂ : Q($g otimes ($i otimes $f) ⟶ ($h otimes $j) otimes $f) := η₂.e.e
    have η₃ : Q(($g otimes $i) otimes $f ⟶ ($h otimes $j) otimes $f) := η₃.e.e
    have e_ηs' : Q($ηs ▷ $f = $ηs') := e_ηs'
    have e_η₁ : Q(((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) otimesₘ $ηs' = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ≫ (α_ _ _ _).inv = $η₂) := e_η₂
    have e_η₃ : Q((α_ _ _ _).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalWhiskerRightAux_cons $e_ηs' $e_η₁ $e_η₂ $e_η₃)
  mkEvalWhiskerRightNil α h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have α : Q($f ≅ $g) := α.e
    return q(evalWhiskerRight_nil $α $h)
  mkEvalWhiskerRightConsOfOf j α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have ηs₁ : Q($h otimes $j ⟶ $i otimes $j) := ηs₁.e.e
    have η₁ : Q($g otimes $j ⟶ $h otimes $j) := η₁.e.e
    have η₂ : Q($g otimes $j ⟶ $i otimes $j) := η₂.e.e
    have η₃ : Q($f otimes $j ⟶ $i otimes $j) := η₃.e.e
    have e_ηs₁ : Q($ηs ▷ $j = $ηs₁) := e_ηs₁
    have e_η₁ : Q($η ▷ $j = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ≫ $ηs₁ = $η₂) := e_η₂
    have e_η₃ : Q((whiskerRightIso $α $j).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalWhiskerRight_cons_of_of $e_ηs₁ $e_η₁ $e_η₂ $e_η₃)
  mkEvalWhiskerRightConsWhisker f k α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← α.srcM
    let h ← η.srcM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have j : Q($ctx.C) := j.e
    have k : Q($ctx.C) := k.e
    have α : Q($g ≅ $f otimes $h) := α.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($f otimes $i ⟶ $j) := ηs.e.e
    have η₁ : Q($h otimes $k ⟶ $i otimes $k) := η₁.e.e
    have η₂ : Q($f otimes ($h otimes $k) ⟶ $f otimes ($i otimes $k)) := η₂.e.e
    have ηs₁ : Q(($f otimes $i) otimes $k ⟶ $j otimes $k) := ηs₁.e.e
    have ηs₂ : Q($f otimes ($i otimes $k) ⟶ $j otimes $k) := ηs₂.e.e
    have η₃ : Q($f otimes ($h otimes $k) ⟶ $j otimes $k) := η₃.e.e
    have η₄ : Q(($f otimes $h) otimes $k ⟶ $j otimes $k) := η₄.e.e
    have η₅ : Q($g otimes $k ⟶ $j otimes $k) := η₅.e.e
    have e_η₁ : Q(((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) ▷ $k = $η₁) := e_η₁
    have e_η₂ : Q($f ◁ $η₁ = $η₂) := e_η₂
    have e_ηs₁ : Q($ηs ▷ $k = $ηs₁) := e_ηs₁
    have e_ηs₂ : Q((α_ _ _ _).inv ≫ $ηs₁ = $ηs₂) := e_ηs₂
    have e_η₃ : Q($η₂ ≫ $ηs₂ = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).hom ≫ $η₃ = $η₄) := e_η₄
    have e_η₅ : Q((whiskerRightIso $α $k).hom ≫ $η₄ = $η₅) := e_η₅
    return q(evalWhiskerRight_cons_whisker $e_η₁ $e_η₂ $e_ηs₁ $e_ηs₂ $e_η₃ $e_η₄ $e_η₅)
  mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let f' ← η.tgtM
    have f : Q($ctx.C) := f.e
    have f' : Q($ctx.C) := f'.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($f ⟶ $f') := η.e.e
    have η₁ : Q($f otimes $g ⟶ $f' otimes $g) := η₁.e.e
    have η₂ : Q(($f otimes $g) otimes $h ⟶ ($f' otimes $g) otimes $h) := η₂.e.e
    have η₃ : Q(($f otimes $g) otimes $h ⟶ $f' otimes ($g otimes $h)) := η₃.e.e
    have η₄ : Q($f otimes ($g otimes $h) ⟶ $f' otimes ($g otimes $h)) := η₄.e.e
    have e_η₁ : Q($η ▷ $g = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ▷ $h = $η₂) := e_η₂
    have e_η₃ : Q($η₂ ≫ (α_ _ _ _).hom = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).inv ≫ $η₃ = $η₄) := e_η₄
    return q(evalWhiskerRight_comp $e_η₁ $e_η₂ $e_η₃ $e_η₄)
  mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have η₁ : Q($f ⟶ $g otimes 𝟙_ _) := η₁.e.e
    have η₂ : Q($f otimes 𝟙_ _ ⟶ $g otimes 𝟙_ _) := η₂.e.e
    have e_η₁ : Q($η ≫ (ρ_ _).inv = $η₁) := e_η₁
    have e_η₂ : Q((ρ_ _).hom ≫ $η₁ = $η₂) := e_η₂
    return q(evalWhiskerRight_id $e_η₁ $e_η₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEvalHorizontalComp MonoidalM
  body: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f

中文:
实例 :
  签名: MkEvalHorizontalComp MonoidalM
  定义体: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f
-/
instance : MkEvalHorizontalComp MonoidalM where
  mkEvalHorizontalCompAuxOf η θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f ⟶ $g) := η.e.e
    have θ : Q($h ⟶ $i) := θ.e.e
    return q(evalHorizontalCompAux_of $η $θ)
  mkEvalHorizontalCompAuxCons η ηs θ ηθ η₁ ηθ₁ ηθ₂ e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    let f' ← ηs.srcM
    let g' ← ηs.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f ⟶ $g) := η.e.e
    have ηs : Q($f' ⟶ $g') := ηs.e.e
    have θ : Q($h ⟶ $i) := θ.e.e
    have ηθ : Q($f' otimes $h ⟶ $g' otimes $i) := ηθ.e.e
    have η₁ : Q($f otimes ($f' otimes $h) ⟶ $g otimes ($g' otimes $i)) := η₁.e.e
    have ηθ₁ : Q($f otimes ($f' otimes $h) ⟶ ($g otimes $g') otimes $i) := ηθ₁.e.e
    have ηθ₂ : Q(($f otimes $f') otimes $h ⟶ ($g otimes $g') otimes $i) := ηθ₂.e.e
    have e_ηθ : Q($ηs otimesₘ $θ = $ηθ) := e_ηθ
    have e_η₁ : Q(((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) otimesₘ $ηθ = $η₁) := e_η₁
    have e_ηθ₁ : Q($η₁ ≫ (α_ _ _ _).inv = $ηθ₁) := e_ηθ₁
    have e_ηθ₂ : Q((α_ _ _ _).hom ≫ $ηθ₁ = $ηθ₂) := e_ηθ₂
    return q(evalHorizontalCompAux_cons $e_ηθ $e_η₁ $e_ηθ₁ $e_ηθ₂)
  mkEvalHorizontalCompAux'Whisker f η θ ηθ η₁ η₂ η₃ e_ηθ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η.srcM
    let h ← η.tgtM
    let f' ← θ.srcM
    let g' ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have η : Q($g ⟶ $h) := η.e.e
    have θ : Q($f' ⟶ $g') := θ.e.e
    have ηθ : Q($g otimes $f' ⟶ $h otimes $g') := ηθ.e.e
    have η₁ : Q($f otimes ($g otimes $f') ⟶ $f otimes ($h otimes $g')) := η₁.e.e
    have η₂ : Q($f otimes ($g otimes $f') ⟶ ($f otimes $h) otimes $g') := η₂.e.e
    have η₃ : Q(($f otimes $g) otimes $f' ⟶ ($f otimes $h) otimes $g') := η₃.e.e
    have e_ηθ : Q($η otimesₘ $θ = $ηθ) := e_ηθ
    have e_η₁ : Q($f ◁ $ηθ = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ≫ (α_ _ _ _).inv = $η₂) := e_η₂
    have e_η₃ : Q((α_ _ _ _).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalHorizontalCompAux'_whisker $e_ηθ $e_η₁ $e_η₂ $e_η₃)
  mkEvalHorizontalCompAux'OfWhisker f η θ η₁ ηθ ηθ₁ ηθ₂ e_η₁ e_ηθ e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η.srcM
    let h ← η.tgtM
    let f' ← θ.srcM
    let g' ← θ.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have η : Q($g ⟶ $h) := η.e.e
    have θ : Q($f' ⟶ $g') := θ.e.e
    have η₁ : Q($g otimes $f ⟶ $h otimes $f) := η₁.e.e
    have ηθ : Q(($g otimes $f) otimes $f' ⟶ ($h otimes $f) otimes $g') := ηθ.e.e
    have ηθ₁ : Q(($g otimes $f) otimes $f' ⟶ $h otimes ($f otimes $g')) := ηθ₁.e.e
    have ηθ₂ : Q($g otimes ($f otimes $f') ⟶ $h otimes ($f otimes $g')) := ηθ₂.e.e
    have e_η₁ : Q($η ▷ $f = $η₁) := e_η₁
    have e_ηθ : Q($η₁ otimesₘ ((Iso.refl _).hom ≫ $θ ≫ (Iso.refl _).hom) = $ηθ) := e_ηθ
    have e_ηθ₁ : Q($ηθ ≫ (α_ _ _ _).hom = $ηθ₁) := e_ηθ₁
    have e_ηθ₂ : Q((α_ _ _ _).inv ≫ $ηθ₁ = $ηθ₂) := e_ηθ₂
    return q(evalHorizontalCompAux'_of_whisker $e_η₁ $e_ηθ $e_ηθ₁ $e_ηθ₂)
  mkEvalHorizontalCompNilNil α β := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.srcM
    let i ← β.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($h ≅ $i) := β.e
    return q(evalHorizontalComp_nil_nil $α $β)
  mkEvalHorizontalCompNilCons α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($f' ≅ $g') := β.e
    have η : Q($g' ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have η₁ : Q($g otimes $g' ⟶ $g otimes $h) := η₁.e.e
    have ηs₁ : Q($g otimes $h ⟶ $g otimes $i) := ηs₁.e.e
    have η₂ : Q($g otimes $g' ⟶ $g otimes $i) := η₂.e.e
    have η₃ : Q($f otimes $f' ⟶ $g otimes $i) := η₃.e.e
    have e_η₁ : Q($g ◁ ((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) = $η₁) := e_η₁
    have e_ηs₁ : Q($g ◁ $ηs = $ηs₁) := e_ηs₁
    have e_η₂ : Q($η₁ ≫ $ηs₁ = $η₂) := e_η₂
    have e_η₃ : Q(($α otimesᵢ $β).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalHorizontalComp_nil_cons $e_η₁ $e_ηs₁ $e_η₂ $e_η₃)
  mkEvalHorizontalCompConsNil α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have β : Q($f' ≅ $g') := β.e
    have η₁ : Q($g otimes $g' ⟶ $h otimes $g') := η₁.e.e
    have ηs₁ : Q($h otimes $g' ⟶ $i otimes $g') := ηs₁.e.e
    have η₂ : Q($g otimes $g' ⟶ $i otimes $g') := η₂.e.e
    have η₃ : Q($f otimes $f' ⟶ $i otimes $g') := η₃.e.e
    have e_η₁ : Q(((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) ▷ $g' = $η₁) := e_η₁
    have e_ηs₁ : Q($ηs ▷ $g' = $ηs₁) := e_ηs₁
    have e_η₂ : Q($η₁ ≫ $ηs₁ = $η₂) := e_η₂
    have e_η₃ : Q(($α otimesᵢ $β).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalHorizontalComp_cons_nil $e_η₁ $e_ηs₁ $e_η₂ $e_η₃)
  mkEvalHorizontalCompConsCons α β η θ ηs θs ηθ ηθs ηθ₁ ηθ₂ e_ηθ e_ηθs e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    let h' ← θ.tgtM
    let i' ← θs.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have f' : Q($ctx.C) := f'.e
    have g' : Q($ctx.C) := g'.e
    have h' : Q($ctx.C) := h'.e
    have i' : Q($ctx.C) := i'.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have β : Q($f' ≅ $g') := β.e
    have θ : Q($g' ⟶ $h') := θ.e.e
    have θs : Q($h' ⟶ $i') := θs.e.e
    have ηθ : Q($g otimes $g' ⟶ $h otimes $h') := ηθ.e.e
    have ηθs : Q($h otimes $h' ⟶ $i otimes $i') := ηθs.e.e
    have ηθ₁ : Q($g otimes $g' ⟶ $i otimes $i') := ηθ₁.e.e
    have ηθ₂ : Q($f otimes $f' ⟶ $i otimes $i') := ηθ₂.e.e
    have e_ηθ : Q($η otimesₘ $θ = $ηθ) := e_ηθ
    have e_ηθs : Q($ηs otimesₘ $θs = $ηθs) := e_ηθs
    have e_ηθ₁ : Q($ηθ ≫ $ηθs = $ηθ₁) := e_ηθ₁
    have e_ηθ₂ : Q(($α otimesᵢ $β).hom ≫ $ηθ₁ = $ηθ₂) := e_ηθ₂
    return q(evalHorizontalComp_cons_cons $e_ηθ $e_ηθs $e_ηθ₁ $e_ηθ₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEval MonoidalM
  body: do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($g ⟶ $h) := θ.e
   

中文:
实例 :
  签名: MkEval MonoidalM
  定义体: do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($g ⟶ $h) := θ.e
   
-/
instance : MkEval MonoidalM where
  mkEvalComp η θ η' θ' ι e_η e_θ e_ηθ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($g ⟶ $h) := θ.e
    have θ' : Q($g ⟶ $h) := θ'.e.e
    have ι : Q($f ⟶ $h) := ι.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($θ = $θ') := e_θ
    have e_ηθ : Q($η' ≫ $θ' = $ι) := e_ηθ
    return q(eval_comp $e_η $e_θ $e_ηθ)
  mkEvalWhiskerLeft f η η' θ e_η e_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η'.srcM
    let h ← η'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($g ⟶ $h) := η.e
    have η' : Q($g ⟶ $h) := η'.e.e
    have θ : Q($f otimes $g ⟶ $f otimes $h) := θ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($f ◁ $η' = $θ) := e_θ
    return q(eval_whiskerLeft $e_η $e_θ)
  mkEvalWhiskerRight η h η' θ e_η e_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η'.srcM
    let g ← η'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($f otimes $h ⟶ $g otimes $h) := θ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($η' ▷ $h = $θ) := e_θ
    return q(eval_whiskerRight $e_η $e_θ)
  mkEvalHorizontalComp η θ η' θ' ι e_η e_θ e_ι := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.srcM
    let i ← θ'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($h ⟶ $i) := θ.e
    have θ' : Q($h ⟶ $i) := θ'.e.e
    have ι : Q($f otimes $h ⟶ $g otimes $i) := ι.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($θ = $θ') := e_θ
    have e_ι : Q($η' otimesₘ $θ' = $ι) := e_ι
    return q(eval_tensorHom $e_η $e_θ $e_ι)
  mkEvalOf η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f := η.src
    let g := η.tgt
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have η : Q($f ⟶ $g) := η.e
    return q(eval_of $η)
  mkEvalMonoidalComp η θ α η' θ' αθ ηαθ e_η e_θ e_αθ e_ηαθ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← α.tgtM
    let i ← θ'.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have i : Q($ctx.C) := i.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have α : Q($g ≅ $h) := α.e
    have θ : Q($h ⟶ $i) := θ.e
    have θ' : Q($h ⟶ $i) := θ'.e.e
    have αθ : Q($g ⟶ $i) := αθ.e.e
    have ηαθ : Q($f ⟶ $i) := ηαθ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($θ = $θ') := e_θ
    have e_αθ : Q(Iso.hom $α ≫ $θ' = $αθ) := e_αθ
    have e_ηαθ : Q($η' ≫ $αθ = $ηαθ) := e_ηαθ
    return q(eval_monoidalComp $e_η $e_θ $e_αθ $e_ηαθ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadNormalExpr MonoidalM
  body: do
    return .whisker (← MonadMor₂.whiskerRightM η.e (.of h)) η h
  hConsM η θ := do
    return .cons (← MonadMor₂.horizontalCompM η.e θ.e) η θ
  whiskerLeftM f η := do
    return .whisker (← MonadMor₂.whiskerLeftM (.of f) η.e) f η
  nilM α := do
    return .nil (← MonadMor₂.homM α) α
  consM α η η

中文:
实例 :
  签名: MonadNormalExpr MonoidalM
  定义体: do
    return .whisker (← MonadMor₂.whiskerRightM η.e (.of h)) η h
  hConsM η θ := do
    return .cons (← MonadMor₂.horizontalCompM η.e θ.e) η θ
  whiskerLeftM f η := do
    return .whisker (← MonadMor₂.whiskerLeftM (.of f) η.e) f η
  nilM α := do
    return .nil (← MonadMor₂.homM α) α
  consM α η η
-/
instance : MonadNormalExpr MonoidalM where
  whiskerRightM η h := do
    return .whisker (← MonadMor₂.whiskerRightM η.e (.of h)) η h
  hConsM η θ := do
    return .cons (← MonadMor₂.horizontalCompM η.e θ.e) η θ
  whiskerLeftM f η := do
    return .whisker (← MonadMor₂.whiskerLeftM (.of f) η.e) f η
  nilM α := do
    return .nil (← MonadMor₂.homM α) α
  consM α η ηs := do
    return .cons (← MonadMor₂.comp₂M (← MonadMor₂.homM α) (← MonadMor₂.comp₂M η.e ηs.e)) α η ηs

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkMor₂ MonoidalM
  body: Mor₂OfExpr

中文:
实例 :
  签名: MkMor₂ MonoidalM
  定义体: Mor₂OfExpr
-/
instance : MkMor₂ MonoidalM where
  ofExpr := Mor₂OfExpr

end Mathlib.Tactic.Monoidal
