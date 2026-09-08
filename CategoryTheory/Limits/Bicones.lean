/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Bicones

Given a category `J`, a walking `Bicone J` is a category whose objects are the objects of `J` and
two extra vertices `Bicone.left` and `Bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `(· ⟶ j)` and `(· ⟶ k)` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C` via
`biconeMk`.

This is used in `CategoryTheory.Functor.Flat`.
-/

@[expose] public section


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

section Bicone

/-- Given a category `J`, construct a walking `Bicone J` by adjoining two elements. -/
/-
**CategoryTheory.Bicone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u₁ → Type u₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category `J`, construct a walking `Bicone J` by adjoining two elements.
-/
inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq

variable (J : Type u₁)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩

open scoped Classical in
/-
**CategoryTheory.finBicone** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：finBicone [Fintype J] : Fintype (Bicone J) where elems
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finBicone [Fintype J] : Fintype (Bicone J) where
  elems := [Bicone.left, Bicone.right].toFinset ∪ Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp [Fintype.complete]

variable [Category.{v₁} J]

/-- The homs for a walking `Bicone J`. -/
/-
**CategoryTheory.BiconeHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type u₁) →   [CategoryTheory.Category.{v₁, u₁} J] → CategoryTheory.Bi
cone J → CategoryTheory.Bicone J → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homs for a walking `Bicone J`.
-/
inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩
/-
**CategoryTheory.BiconeHom.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.BiconeHom`。
形式化陈述：(J : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {j k :
 CategoryTheory.Bicone J} → DecidableEq (CategoryTheory.BiconeHom J j k)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  classical cases f <;> cases g <;> simp only [diagram.injEq] <;> infer_instance

@[simps]
/-
**CategoryTheory.biconeCategoryStruct** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`
。
形式化陈述：biconeCategoryStruct : CategoryStruct (Bicone J) where Hom
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance biconeCategoryStruct : CategoryStruct (Bicone J) where
  Hom := BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
    · exact g
    · cases g
      apply BiconeHom.left
    · cases g
      apply BiconeHom.right
    · rcases g with (_ | _ | _ | _ | g)
      exact BiconeHom.diagram (f ≫ g)
/-
**CategoryTheory.biconeCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：biconeCategory : Category (Bicone J) where id_comp f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance biconeCategory : Category (Bicone J) where
  id_comp f := by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp

end Bicone

section SmallCategory

variable (J : Type v₁) [SmallCategory J]

/-- Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C`.
-/
@[simps]
/-
**CategoryTheory.biconeMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bi
cone J ⥤ C where obj X
参数：c₁ c₂ : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `
Bicone J ⥤ C`.
-/
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C where
  obj X := Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_ | _ | _ | _ | f)
    · exact 𝟙 _
    · exact 𝟙 _
    · exact c₁.π.app _
    · exact c₂.π.app _
    · exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_ | _ | _ | _ | _)
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · cases g
      exact (Category.id_comp _).symm.trans (c₁.π.naturality _)
    · cases g
      exact (Category.id_comp _).symm.trans (c₂.π.naturality _)
    · cases g
      apply F.map_comp

open scoped Classical in
/-
**CategoryTheory.finBiconeHom** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k)
参数：j k : Bicone J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
      { elems := {BiconeHom.right_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := {BiconeHom.right _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := Finset.image BiconeHom.diagram Fintype.elems
      complete := fun f => by
        rcases f with (_ | _ | _ | _ | f)
        simp only [Finset.mem_image]
        use f
        simpa using Fintype.complete _ }
/-
**CategoryTheory.biconeSmallCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：biconeSmallCategory : SmallCategory (Bicone J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J
/-
**CategoryTheory.biconeFinCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type v₁) →   [inst : CategoryTheory.SmallCategory J] →     [CategoryT
heory.FinCategory J] → CategoryTheory.FinCategory (CategoryTheory.Bicone J)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where

end SmallCategory

end CategoryTheory

