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
/-
**CategoryTheory.Lax.LaxTrans.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Lax.LaxTrans`。
形式化陈述：whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where as
参数：η : F ⟶ G；Γ : θ ⟶ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left whiskering of a lax natural transformation and a modification.
-/
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ η.app a ◁ ((Γ.as.app a ▷ H.map f ≫ ι.naturality f)) ⊗≫
              η.naturality f ▷ (ι.app b) ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫
              ((η.app a ≫ G.map f) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) ⊗≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [whisker_exchange]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of a lax natural transformation and a modification. -/
@[simps]
/-
**CategoryTheory.Lax.LaxTrans.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Lax.LaxTrans`。
形式化陈述：whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where a
s
参数：Γ : η ⟶ θ；ι : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right whiskering of a lax natural transformation and a modification.
-/
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ (Γ.as.app a ▷ (ι.app a ≫ H.map f) ≫ θ.app a ◁ ι.naturality f) ⊗≫
              θ.naturality f ▷ ι.app b ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ (η.app a ◁ ι.naturality f ⊗≫ (Γ.as.app a ▷ G.map f ≫
              θ.naturality f) ▷ ι.app b) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of lax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.LaxTrans.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Lax.LaxTrans`。
形式化陈述：associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι
参数：η : F ⟶ G；θ : G ⟶ H；ι : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associator for the vertical composition of lax natural transformations.
-/
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) <| by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of lax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.LaxTrans.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Lax.LaxTrans`。
形式化陈述：leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unitor for the vertical composition of lax natural transformations.
-/
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of lax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.LaxTrans.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Lax.LaxTrans`。
形式化陈述：rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unitor for the vertical composition of lax natural transformations.
-/
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the lax functors between bicategories, with lax transformations. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
/-
**CategoryTheory.Lax.LaxTrans.LaxFunctor.bicategory** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Lax.LaxTrans.LaxFunctor`。
形式化陈述：(B : Type u₁) →   [inst : CategoryTheory.Bicategory B] →     (C : Type u₂)
 → [inst_1 : CategoryTheory.Bicategory C] → CategoryTheory.Bicategory (CategoryT
heory.LaxFunctor B C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**CategoryTheory.Lax.OplaxTrans.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Lax.OplaxTrans`。
形式化陈述：whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where as
参数：η : F ⟶ G；Γ : θ ⟶ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left whiskering of an oplax natural transformation and a modification.
-/
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ ((F.map f ≫ η.app b) ◁ Γ.as.app b ≫ η.naturality f ▷ ι.app b) ⊗≫
            η.app a ◁ ι.naturality f ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.naturality f ▷ θ.app b ⊗≫ η.app a ◁ (G.map f ◁ Γ.as.app b ≫
            ι.naturality f) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
/-
**CategoryTheory.Lax.OplaxTrans.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Lax.OplaxTrans`。
形式化陈述：whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where a
s
参数：Γ : η ⟶ θ；ι : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right whiskering of an oplax natural transformation and a modification.
-/
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ (F.map f ◁ Γ.as.app b ≫ θ.naturality f) ▷ ι.app b ⊗≫
              θ.app a ◁ ι.naturality f ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.naturality f ▷ ι.app b ⊗≫ (Γ.as.app a ▷ (G.map f ≫ ι.app b) ≫
              θ.app a ◁ ι.naturality f) ⊗≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [← whisker_exchange]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of oplax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.OplaxTrans.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Lax.OplaxTrans`。
形式化陈述：associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι
参数：η : F ⟶ G；θ : G ⟶ H；ι : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associator for the vertical composition of oplax natural transformations.
-/
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a)) <| by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.OplaxTrans.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Lax.OplaxTrans`。
形式化陈述：leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unitor for the vertical composition of oplax natural transformations.
-/
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.OplaxTrans.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Lax.OplaxTrans`。
形式化陈述：rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unitor for the vertical composition of oplax natural transformations.
-/
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the lax functors between bicategories, with oplax transformations. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
/-
**CategoryTheory.Lax.OplaxTrans.LaxFunctor.bicategory** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Lax.OplaxTrans.LaxFunctor`。
形式化陈述：(B : Type u₁) →   [inst : CategoryTheory.Bicategory B] →     (C : Type u₂)
 → [inst_1 : CategoryTheory.Bicategory C] → CategoryTheory.Bicategory (CategoryT
heory.LaxFunctor B C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance LaxFunctor.bicategory : Bicategory (B ⥤ᴸ C) where
  whiskerLeft {_ _ _} η _ _ Γ := whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ := whiskerRight Γ
  associator {_ _ _} _ := associator
  leftUnitor {_ _} := leftUnitor
  rightUnitor {_ _} := rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end OplaxTrans

end CategoryTheory.Lax

