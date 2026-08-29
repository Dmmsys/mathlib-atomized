/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# The bicategory of pseudofunctors

Given bicategories `B` and `C`, we define a bicategory structure on `Pseudofunctor B C` whose
* objects are pseudofunctors,
* 1-morphisms are strong natural transformations, and
* 2-morphisms are modifications.

We scope this instance to the `CategoryTheory.Pseudofunctor.StrongTrans` namespace to avoid
potential future conflicts with other bicategory instances on `Pseudofunctor B C`.
-/

set_option backward.defeqAttrib.useBackward true

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace StrongTrans

variable {F G H I : Pseudofunctor B C}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
abbreviation whiskerLeft
  signature: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  body: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
      simp }

中文:
缩写 whiskerLeft
  签名: (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι)
  定义体: {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
      simp }
-/
abbrev whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
abbreviation whiskerRight
  signature: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  body: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

中文:
缩写 whiskerRight
  签名: {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H)
  定义体: {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }
-/
abbrev whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `associator` / `associator` 的定义

English:
abbreviation associator
  signature: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  body: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

中文:
缩写 associator
  签名: (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I)
  定义体: isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))
-/
abbrev associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
abbreviation leftUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => fun_ (η.app a))

中文:
缩写 leftUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => fun_ (η.app a))

Depends on / 依赖: fun_
-/
abbrev leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => fun_ (η.app a))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
abbreviation rightUnitor
  signature: (η : F ⟶ G)
  body: isoMk (fun a => ρ_ (η.app a))

中文:
缩写 rightUnitor
  签名: (η : F ⟶ G)
  定义体: isoMk (fun a => ρ_ (η.app a))
-/
abbrev rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.isDefEq.respectTransparency.types false in
/-- A bicategory structure on pseudofunctors, with strong transformations as 1-morphisms.

Note that this instance is scoped to the `Pseudofunctor.StrongTrans` namespace. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end StrongTrans

end CategoryTheory.Pseudofunctor
