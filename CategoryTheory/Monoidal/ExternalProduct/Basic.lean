/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# External product of diagrams in a monoidal category

In a monoidal category `C`, given a pair of diagrams `K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, we
introduce the external product `K₁ ⊠ K₂ : J₁ × J₂ ⥤ C` as the bifunctor `(j₁, j₂) ↦ K₁ j₁ ⊗ K₂ j₂`.
The notation `- ⊠ -` is scoped to `MonoidalCategory.ExternalProduct`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.MonoidalCategory
open CategoryTheory.Functor

variable (J₁ : Type u₁) (J₂ : Type u₂) (C : Type u₃)
    [Category.{v₁} J₁] [Category.{v₂} J₂] [Category.{v₃} C] [MonoidalCategory C]

/-- The (curried version of the) external product bifunctor: given diagrams
`K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, this is the bifunctor `j₁ ↦ j₂ ↦ K₁ j₁ ⊗ K₂ j₂`. -/
@[simps!, implicit_reducible]
/--
Definition of `externalProductBifunctorCurried` / `externalProductBifunctorCurried` 的定义

English:
definition externalProductBifunctorCurried
  signature: : (J₁ ⥤ C) ⥤ (J₂ ⥤ C) ⥤ J₁ ⥤ J₂ ⥤ C
  body: (Functor.postcompose₂.obj <| (evaluation _ _).obj <| curriedTensor C).obj whiskeringLeft₂ C

中文:
定义 externalProductBifunctorCurried
  签名: : (J₁ ⥤ C) ⥤ (J₂ ⥤ C) ⥤ J₁ ⥤ J₂ ⥤ C
  定义体: (Functor.postcompose₂.obj <| (evaluation _ _).obj <| curriedTensor C).obj whiskeringLeft₂ C

Depends on / 依赖: Functor, Functor.postcompose, curriedTensor, evaluation
-/
def externalProductBifunctorCurried : (J₁ ⥤ C) ⥤ (J₂ ⥤ C) ⥤ J₁ ⥤ J₂ ⥤ C :=
(Functor.postcompose₂.obj <| (evaluation _ _).obj <| curriedTensor C).obj whiskeringLeft₂ C

/-- The external product bifunctor: given diagrams
`K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, this is the bifunctor `(j₁, j₂) ↦ K₁ j₁ ⊗ K₂ j₂`. -/
@[simps!, implicit_reducible]
/--
Definition of `externalProductBifunctor` / `externalProductBifunctor` 的定义

English:
definition externalProductBifunctor
  signature: : ((J₁ ⥤ C) × (J₂ ⥤ C)) ⥤ J₁ × J₂ ⥤ C
  body: uncurry.obj (Functor.postcompose₂.obj <| uncurry).obj
    externalProductBifunctorCurried J₁ J₂ C

中文:
定义 externalProductBifunctor
  签名: : ((J₁ ⥤ C) × (J₂ ⥤ C)) ⥤ J₁ × J₂ ⥤ C
  定义体: uncurry.obj (Functor.postcompose₂.obj <| uncurry).obj
    externalProductBifunctorCurried J₁ J₂ C

Depends on / 依赖: Functor, Functor.postcompose, externalProductBifunctorCurried, uncurry, uncurry.obj
-/
def externalProductBifunctor : ((J₁ ⥤ C) × (J₂ ⥤ C)) ⥤ J₁ × J₂ ⥤ C :=
uncurry.obj (Functor.postcompose₂.obj <| uncurry).obj
    externalProductBifunctorCurried J₁ J₂ C

variable {J₁ J₂ C}
/--
Definition of `externalProduct` / `externalProduct` 的定义

English:
abbreviation externalProduct
  signature: (F₁ : J₁ ⥤ C) (F₂ : J₂ ⥤ C)
  body: .obj (F₁, F₂) externalProductBifunctor J₁ J₂ C

中文:
缩写 externalProduct
  签名: (F₁ : J₁ ⥤ C) (F₂ : J₂ ⥤ C)
  定义体: .obj (F₁, F₂) externalProductBifunctor J₁ J₂ C

Depends on / 依赖: externalProductBifunctor
-/
abbrev externalProduct (F₁ : J₁ ⥤ C) (F₂ : J₂ ⥤ C) :=
.obj (F₁, F₂) externalProductBifunctor J₁ J₂ C

namespace ExternalProduct
/-- Notation for `externalProduct`.
Do `open scoped CategoryTheory.MonoidalCategory.ExternalProduct`
to bring this notation in scope. -/
scoped infixr:80 " ⊠ " => externalProduct

end ExternalProduct

open scoped ExternalProduct

variable (J₁ J₂ C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When both diagrams have the same source category, composing the external product with
the diagonal gives the pointwise functor tensor product.
Note that `(externalProductCompDiagIso _ _).app (F₁, F₂) : Functor.diag J₁ ⋙ F₁ ⊠ F₂ ≅ F₁ ⊗ F₂`
type checks. -/
@[simps!]
/--
Definition of `externalProductCompDiagIso` / `externalProductCompDiagIso` 的定义

English:
definition externalProductCompDiagIso
  signature: :
  body: NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by simp [tensorHom_def]))
    (fun _ => by ext; simp [tensorHom_def])

中文:
定义 externalProductCompDiagIso
  签名: :
  定义体: NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by simp [tensorHom_def]))
    (fun _ => by ext; simp [tensorHom_def])

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents, tensorHom_def
-/
def externalProductCompDiagIso :
    externalProductBifunctor J₁ J₁ C ⋙ (whiskeringLeft _ _ _ |>.obj <| Functor.diag J₁) ≅
    tensor (J₁ ⥤ C) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by simp [tensorHom_def]))
    (fun _ => by ext; simp [tensorHom_def])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `C` is braided, there is an isomorphism `Prod.swap _ _ ⋙ F₁ ⊠ F₂ ≅ F₂ ⊠ F₁`, natural
in both `F₁` and `F₂`.
Note that `(externalProductSwap _ _ _).app (F₁, F₂) : Prod.swap _ _ ⋙ F₁ ⊠ F₂ ≅ F₂ ⊠ F₁`
type checks. -/
@[simps!]
/--
Definition of `externalProductSwap` / `externalProductSwap` 的定义

English:
definition externalProductSwap
  signature: [BraidedCategory C]
  body: NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => β_ _ _) (by simp [whisker_exchange]))
    (fun _ => by ext; simp [whisker_exchange])

中文:
定义 externalProductSwap
  签名: [BraidedCategory C]
  定义体: NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => β_ _ _) (by simp [whisker_exchange]))
    (fun _ => by ext; simp [whisker_exchange])

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, whisker_exchange
-/
def externalProductSwap [BraidedCategory C] :
    externalProductBifunctor J₁ J₂ C ⋙ (whiskeringLeft _ _ _ |>.obj <| Prod.swap _ _) ≅
    Prod.swap _ _ ⋙ externalProductBifunctor J₂ J₁ C :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => β_ _ _) (by simp [whisker_exchange]))
    (fun _ => by ext; simp [whisker_exchange])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A version of `externalProductSwap` phrased in terms of the curried functors. -/
@[simps!]
/--
Definition of `externalProductFlip` / `externalProductFlip` 的定义

English:
definition externalProductFlip
  signature: [BraidedCategory C]
  body: NatIso.ofComponents fun _ => NatIso.ofComponents
fun _ => NatIso.ofComponents fun _ => NatIso.ofComponents (fun _ => β_ _ _)

中文:
定义 externalProductFlip
  签名: [BraidedCategory C]
  定义体: NatIso.ofComponents fun _ => NatIso.ofComponents
fun _ => NatIso.ofComponents fun _ => NatIso.ofComponents (fun _ => β_ _ _)

Depends on / 依赖: E.toPullback, NatIso, NatIso.ofComponents, Sieve.ofArrows, ofArrows, ofComponents, toPullback
-/
def externalProductFlip [BraidedCategory C] :
    (Functor.postcompose₂.obj <| flipFunctor _ _ _).obj
      (externalProductBifunctorCurried J₁ J₂ C) ≅
    (externalProductBifunctorCurried J₂ J₁ C).flip :=
NatIso.ofComponents fun _ => NatIso.ofComponents
fun _ => NatIso.ofComponents fun _ => NatIso.ofComponents (fun _ => β_ _ _)

section Composition

variable {J₁ J₂ C} {I₁ : Type u₃} {I₂ : Type u₄} [Category.{v₃} I₁] [Category.{v₄} I₂]

set_option backward.defeqAttrib.useBackward true in
/-- Composing `F₁ × F₂` with `G₁ ⊠ G₂` is isomorphic to `(F₁ ⋙ G₁) ⊠ (F₂ ⋙ G₂)`. -/
@[simps!]
/--
Definition of `prodCompExternalProduct` / `prodCompExternalProduct` 的定义

English:
definition prodCompExternalProduct
  signature: (F₁ : I₁ ⥤ J₁) (G₁ : J₁ ⥤ C) (F₂ : I₂ ⥤ J₂) (G₂ : J₂ ⥤ C)
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 prodCompExternalProduct
  签名: (F₁ : I₁ ⥤ J₁) (G₁ : J₁ ⥤ C) (F₂ : I₂ ⥤ J₂) (G₂ : J₂ ⥤ C)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def prodCompExternalProduct (F₁ : I₁ ⥤ J₁) (G₁ : J₁ ⥤ C) (F₂ : I₂ ⥤ J₂) (G₂ : J₂ ⥤ C) :
     F₁.prod F₂ ⋙ G₁ ⊠ G₂ ≅ (F₁ ⋙ G₁) ⊠ (F₂ ⋙ G₂) := NatIso.ofComponents (fun _ => Iso.refl _)

end Composition

end CategoryTheory.MonoidalCategory
