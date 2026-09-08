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
/-- Left whiskering of a strong natural transformation between pseudofunctors
and a modification. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerLeft** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where as
参数：η : F ⟶ G；Γ : θ ⟶ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left whiskering of a strong natural transformation between pseudofunctors
and a modification.
-/
abbrev whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering of a strong natural transformation between pseudofunctors
and a modification. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerRight** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where a
s
参数：Γ : η ⟶ θ；ι : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right whiskering of a strong natural transformation between pseudofunctors
and a modification.
-/
abbrev whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in
/-- Associator for the vertical composition of strong natural transformations
between pseudofunctors. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.associator** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι
参数：η : F ⟶ G；θ : G ⟶ H；ι : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associator for the vertical composition of strong natural transformations
between pseudofunctors.
-/
abbrev associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

set_option backward.isDefEq.respectTransparency false in
/-- Left unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.leftUnitor** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unitor for the vertical composition of strong natural transformations
between pseudofunctors.
-/
abbrev leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

set_option backward.isDefEq.respectTransparency false in
/-- Right unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.rightUnitor** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unitor for the vertical composition of strong natural transformations
between pseudofunctors.
-/
abbrev rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.isDefEq.respectTransparency.types false in
/-- A bicategory structure on pseudofunctors, with strong transformations as 1-morphisms.

Note that this instance is scoped to the `Pseudofunctor.StrongTrans` namespace. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end StrongTrans

end CategoryTheory.Pseudofunctor

