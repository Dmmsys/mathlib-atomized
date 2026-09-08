/-
Copyright (c) 2019 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# Thin categories

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.
Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.
To construct a category instance one only needs to specify the `CategoryStruct` part,
as the axioms hold for free.
If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁}

section

variable [CategoryStruct.{v₁} C] [Quiver.IsThin C]

/-- Construct a category instance from a `CategoryStruct`, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
@[instance_reducible]
/-
**CategoryTheory.thin_category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.CategoryStruct.{v₁, u₁} C] → [Qui
ver.IsThin C] → CategoryTheory.Category.{v₁, u₁} C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a category instance from a `CategoryStruct`, using the fact that
    hom spaces are subsingletons to prove the axioms.
-/
def thin_category : Category C where

end

-- We don't assume anything about where the category instance on `C` came from.
-- In particular this allows `C` to be a preorder, with the category instance inherited from the
-- preorder structure.
variable [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [Quiver.IsThin C]

/-- If `C` is a thin category, then `D ⥤ C` is a thin category. -/
/-
**CategoryTheory.functor_thin** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：functor_thin : Quiver.IsThin (D ⥤ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)

--- 原说明 ---
If `C` is a thin category, then `D ⥤ C` is a thin category.
-/
instance functor_thin : Quiver.IsThin (D ⥤ C) := fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩

/-- To show `X ≅ Y` in a thin category, it suffices to just give any morphism in each direction. -/
/-
**CategoryTheory.iso_of_both_ways** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y where hom
参数：f : X ⟶ Y；g : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show `X ≅ Y` in a thin category, it suffices to just give any morphism in eac
h direction.
-/
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    X ≅ Y where
  hom := f
  inv := g
/-
**CategoryTheory.subsingleton_iso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩

end CategoryTheory

