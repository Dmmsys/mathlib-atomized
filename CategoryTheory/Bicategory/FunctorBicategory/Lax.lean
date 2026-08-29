/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Lax

/-!
# Bicategories of lax functors

Given bicategories `B` and `C`, we give bicategory structures on `LaxFunctor B C` whose
* objects are lax functors,
* 1-morphisms are lax or oplax natural transformations, and
* 2-morphisms are modifications.
-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {F G H I : B ⥤ᴸ C}

namespace LaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Left whiskering of a lax natural transformation and a modification. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  body: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ η.app a ◁ ((Γ.as.app a ▷ H.map f ≫ ι.naturality f)) otimes≫
              η.naturality f ▷ (ι.app b) otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _

中文:
定义 whiskerLeft
  签名: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  定义体: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ η.app a ◁ ((Γ.as.app a ▷ H.map f ≫ ι.naturality f)) otimes≫
              η.naturality f ▷ (ι.app b) otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _
-/
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ η.app a ◁ ((Γ.as.app a ▷ H.map f ≫ ι.naturality f)) otimes≫
              η.naturality f ▷ (ι.app b) otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality f otimes≫
              ((η.app a ≫ G.map f) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) otimes≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [whisker_exchange]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of a lax natural transformation and a modification. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  body: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (Γ.as.app a ▷ (ι.app a ≫ H.map f) ≫ θ.app a ◁ ι.naturality f) otimes≫
              θ.naturality f ▷ ι.app b otimes≫ 𝟙 _ := by
          bicategory
       

中文:
定义 whiskerRight
  签名: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  定义体: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (Γ.as.app a ▷ (ι.app a ≫ H.map f) ≫ θ.app a ◁ ι.naturality f) otimes≫
              θ.naturality f ▷ ι.app b otimes≫ 𝟙 _ := by
          bicategory
       
-/
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (Γ.as.app a ▷ (ι.app a ≫ H.map f) ≫ θ.app a ◁ ι.naturality f) otimes≫
              θ.naturality f ▷ ι.app b otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ (η.app a ◁ ι.naturality f otimes≫ (Γ.as.app a ▷ G.map f ≫
              θ.naturality f) ▷ ι.app b) otimes≫ 𝟙 _ := by
          rw [← whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of lax natural transformations. -/
@[simps!]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  body: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

中文:
定义 associator
  签名: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  定义体: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

Depends on / 依赖: bicategory, comp_app, comp_naturality
-/
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of lax natural transformations. -/
@[simps!]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => fun_ (η.app a))

中文:
定义 leftUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => fun_ (η.app a))

Depends on / 依赖: fun_
-/
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => fun_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of lax natural transformations. -/
@[simps!]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => ρ_ (η.app a))

中文:
定义 rightUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => ρ_ (η.app a))
-/
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the lax functors between bicategories, with lax transformations. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance LaxFunctor.bicategory : Bicategory (B ⥤ᴸ C) where
  whiskerLeft {_ _ _} η _ _ Γ := whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ := whiskerRight Γ
  associator {_ _ _} _ := associator
  leftUnitor {_ _} := leftUnitor
  rightUnitor {_ _} := rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end LaxTrans

namespace OplaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Left whiskering of an oplax natural transformation and a modification. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  body: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ ((F.map f ≫ η.app b) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) otimes≫
            η.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _

中文:
定义 whiskerLeft
  签名: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  定义体: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ ((F.map f ≫ η.app b) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) otimes≫
            η.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _
-/
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ ((F.map f ≫ η.app b) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) otimes≫
            η.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ η.naturality f ▷ θ.app b otimes≫ η.app a ◁ (G.map f ◁ Γ.as.app b ≫
            ι.naturality f) otimes≫ 𝟙 _ := by
          rw [whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  body: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (F.map f ◁ Γ.as.app b ≫ θ.naturality f) ▷ ι.app b otimes≫
              θ.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ oti

中文:
定义 whiskerRight
  签名: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  定义体: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (F.map f ◁ Γ.as.app b ≫ θ.naturality f) ▷ ι.app b otimes≫
              θ.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ oti
-/
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ otimes≫ (F.map f ◁ Γ.as.app b ≫ θ.naturality f) ▷ ι.app b otimes≫
              θ.app a ◁ ι.naturality f otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ η.naturality f ▷ ι.app b otimes≫ (Γ.as.app a ▷ (G.map f ≫ ι.app b) ≫
              θ.app a ◁ ι.naturality f) otimes≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [← whisker_exchange]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of oplax natural transformations. -/
@[simps!]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  body: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

中文:
定义 associator
  签名: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  定义体: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

Depends on / 依赖: bicategory, comp_app, comp_naturality
-/
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => fun_ (η.app a))

中文:
定义 leftUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => fun_ (η.app a))

Depends on / 依赖: fun_
-/
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => fun_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => ρ_ (η.app a))

中文:
定义 rightUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => ρ_ (η.app a))
-/
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the lax functors between bicategories, with oplax transformations. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance LaxFunctor.bicategory : Bicategory (B ⥤ᴸ C) where
  whiskerLeft {_ _ _} η _ _ Γ := whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ := whiskerRight Γ
  associator {_ _ _} _ := associator
  leftUnitor {_ _} := leftUnitor
  rightUnitor {_ _} := rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end OplaxTrans

end CategoryTheory.Lax
