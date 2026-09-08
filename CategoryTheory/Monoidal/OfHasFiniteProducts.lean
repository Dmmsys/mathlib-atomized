/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co-)Cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## TODO

Once we have cocartesian-monoidal categories, replace `monoidalOfHasFiniteCoproducts` and
`symmetricOfHasFiniteCoproducts` with `CocartesianMonoidalCategory.ofHasFiniteCoproducts`.
-/

@[expose] public section


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

#adaptation_note /-- prior to nightly-2026-02-05
the four fields starting from `id_tensorHom_id` were provided by the auto_param -/
/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
@[instance_reducible]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : Mon
oidalCategory C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.associator_naturality`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCo
products C]   {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f…
· 使用定理 `CategoryTheory.Limits.coprod.leftUnitor_naturality`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits
.HasBinaryCoproducts C] [inst_2 : Catego…
· 使用定理 `CategoryTheory.Limits.coprod.rightUnitor_naturality`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limit
s.HasBinaryCoproducts C] [inst_2 : Catego…
· 使用定理 `CategoryTheory.Limits.coprod.pentagon`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts C]  
 (W X Y Z : C),   CategoryT…
· 使用定理 `CategoryTheory.Limits.coprod.triangle`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts C]  
 [inst_2 : CategoryTheory.L…

--- 原说明 ---
A category with an initial object and binary coproducts has a natural monoidal s
tructure.
-/
def monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y ↦ X ⨿ Y
    whiskerLeft := fun _ _ _ g ↦ Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ ↦ Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g ↦ Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associator
    leftUnitor := coprod.leftUnitor
    rightUnitor := coprod.rightUnitor
  }
  .ofTensorHom
    (pentagon := coprod.pentagon)
    (triangle := coprod.triangle)
    (associator_naturality := @coprod.associator_naturality _ _ _)
    (id_tensorHom_id := fun _ _ => coprod.map_id_id)
    (tensorHom_comp_tensorHom := coprod.map_map)
    (leftUnitor_naturality := coprod.leftUnitor_naturality)
    (rightUnitor_naturality := coprod.rightUnitor_naturality)

end

namespace monoidalOfHasFiniteCoproducts

variable [HasInitial C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteCoproducts

open scoped MonoidalCategory

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.tensorObj** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：tensorObj (X Y : C) : X otimes Y = (X ⨿ Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.tensorHom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f otimesₘ g = Limits.cop
rod.map f g
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ₘ g = Limits.coprod.map f g :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.whiskerLeft** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.coprod.map (𝟙 X
) f
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.coprod.map (𝟙 X) f :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.whiskerRight** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.coprod.map f (
𝟙 Z)
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.coprod.map f (𝟙 Z) :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.leftUnitor_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：leftUnitor_hom (X : C) : (fun_ X).hom = coprod.desc (initial.to X) (𝟙 _)
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.rightUnitor_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.leftUnitor_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：leftUnitor_inv (X : C) : (fun_ X).inv = Limits.coprod.inr
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_inv (X : C) : (λ_ X).inv = Limits.coprod.inr :=
  rfl

@[simp]
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.rightUnitor_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right-hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.associator_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：associator_hom (X Y Z : C) : (α_ X Y Z).hom = coprod.desc (coprod.desc cop
rod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl
/-
**CategoryTheory.monoidalOfHasFiniteCoproducts.associator_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.monoidalOfHasFiniteCoproducts`。
形式化陈述：associator_inv (X Y Z : C) : (α_ X Y Z).inv = coprod.desc (coprod.inl ≫ co
prod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) :=
  rfl

end monoidalOfHasFiniteCoproducts

section

attribute [local instance] monoidalOfHasFiniteCoproducts

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps, instance_reducible]
/-
**CategoryTheory.symmetricOfHasFiniteCoproducts** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : Sy
mmetricCategory C where braiding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal structure coming from finite coproducts is symmetric.
-/
def symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] :
    SymmetricCategory C where
  braiding := Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y := by simp

end

end CategoryTheory

