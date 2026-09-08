/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace Monoidal

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
@[simps]
/-
**CategoryTheory.Monoidal.FunctorCategory.tensorObj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Monoidal.FunctorCategory`。
形式化陈述：tensorObj : C ⥤ D where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
def tensorObj : C ⥤ D where
  obj X := F.obj X ⊗ G.obj X
  map f := F.map f ⊗ₘ G.map f

variable {F G F' G'}
variable (α : F ⟶ G) (β : F' ⟶ G')

set_option backward.defeqAttrib.useBackward true in
/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
/-
**CategoryTheory.Monoidal.FunctorCategory.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Monoidal.FunctorCategory`。
形式化陈述：tensorHom : tensorObj F F' ⟶ tensorObj G G' where app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
def tensorHom : tensorObj F F' ⟶ tensorObj G G' where
  app X := α.app X ⊗ₘ β.app X
  naturality X Y f := by
    dsimp; rw [tensorHom_comp_tensorHom, α.naturality, β.naturality, ← tensorHom_comp_tensorHom]

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
/-
**CategoryTheory.Monoidal.FunctorCategory.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Monoidal.FunctorCategory`。
形式化陈述：whiskerLeft (F) (β : F' ⟶ G') : tensorObj F F' ⟶ tensorObj F G' where app 
X
参数：F；β : F' ⟶ G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(An auxiliary definition for `functorCategoryMonoidal`.)
-/
def whiskerLeft (F) (β : F' ⟶ G') : tensorObj F F' ⟶ tensorObj F G' where
  app X := F.obj X ◁ β.app X
  naturality X Y f := by
    simp only [← id_tensorHom]
    apply (tensorHom (𝟙 F) β).naturality

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
/-
**CategoryTheory.Monoidal.FunctorCategory.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Monoidal.FunctorCategory`。
形式化陈述：whiskerRight (F') : tensorObj F F' ⟶ tensorObj G F' where app X
参数：F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(An auxiliary definition for `functorCategoryMonoidal`.)
-/
def whiskerRight (F') : tensorObj F F' ⟶ tensorObj G F' where
  app X := α.app X ▷ F'.obj X
  naturality X Y f := by
    simp only [← tensorHom_id]
    apply (tensorHom α (𝟙 F')).naturality

end FunctorCategory

open CategoryTheory.Monoidal.FunctorCategory

set_option backward.defeqAttrib.useBackward true in
/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
/-
**CategoryTheory.Monoidal.functorCategoryMonoidalStruct** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Monoidal`。
形式化陈述：functorCategoryMonoidalStruct : MonoidalCategoryStruct (C ⥤ D) where tenso
rObj F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidalStruct : MonoidalCategoryStruct (C ⥤ D) where
  tensorObj F G := tensorObj F G
  tensorHom α β := tensorHom α β
  whiskerLeft F _ _ α := FunctorCategory.whiskerLeft F α
  whiskerRight α F := FunctorCategory.whiskerRight α F
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents fun X => λ_ (F.obj X)
  rightUnitor F := NatIso.ofComponents fun X => ρ_ (F.obj X)
  associator F G H := NatIso.ofComponents fun X => α_ (F.obj X) (G.obj X) (H.obj X)

@[simp]
/-
**CategoryTheory.Monoidal.tensorUnit_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：tensorUnit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorUnit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.tensorUnit_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：tensorUnit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorUnit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.tensorObj_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Monoidal`。
形式化陈述：tensorObj_obj {F G : C ⥤ D} {X} : (F otimes G).obj X = F.obj X otimes G.ob
j X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_obj {F G : C ⥤ D} {X} : (F ⊗ G).obj X = F.obj X ⊗ G.obj X :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.tensorObj_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Monoidal`。
形式化陈述：tensorObj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F otimes G).map f = F.map
 f otimesₘ G.map f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F ⊗ G).map f = F.map f ⊗ₘ G.map f :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.tensorHom_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Monoidal`。
形式化陈述：tensorHom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} : (α otime
sₘ β).app X = α.app X otimesₘ β.app X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorHom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} :
    (α ⊗ₘ β).app X = α.app X ⊗ₘ β.app X :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.whiskerLeft_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：whiskerLeft_app {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X} : (F ◁ β).app X = F.ob
j X ◁ β.app X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_app {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X} :
    (F ◁ β).app X = F.obj X ◁ β.app X :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.whiskerRight_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Monoidal`。
形式化陈述：whiskerRight_app {F G F' : C ⥤ D} {α : F ⟶ G} {X} : (α ▷ F').app X = α.app
 X ▷ F'.obj X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_app {F G F' : C ⥤ D} {α : F ⟶ G} {X} :
    (α ▷ F').app X = α.app X ▷ F'.obj X :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.leftUnitor_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Monoidal`。
形式化陈述：leftUnitor_hom_app {F : C ⥤ D} {X} : ((fun_ F).hom : 𝟙_ _ otimes F ⟶ F).ap
p X = (fun_ (F.obj X)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_hom_app {F : C ⥤ D} {X} :
    ((λ_ F).hom : 𝟙_ _ ⊗ F ⟶ F).app X = (λ_ (F.obj X)).hom :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.leftUnitor_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Monoidal`。
形式化陈述：leftUnitor_inv_app {F : C ⥤ D} {X} : ((fun_ F).inv : F ⟶ 𝟙_ _ otimes F).ap
p X = (fun_ (F.obj X)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_inv_app {F : C ⥤ D} {X} :
    ((λ_ F).inv : F ⟶ 𝟙_ _ ⊗ F).app X = (λ_ (F.obj X)).inv :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.rightUnitor_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Monoidal`。
形式化陈述：rightUnitor_hom_app {F : C ⥤ D} {X} : ((ρ_ F).hom : F otimes 𝟙_ _ ⟶ F).app
 X = (ρ_ (F.obj X)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_hom_app {F : C ⥤ D} {X} :
    ((ρ_ F).hom : F ⊗ 𝟙_ _ ⟶ F).app X = (ρ_ (F.obj X)).hom :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.rightUnitor_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Monoidal`。
形式化陈述：rightUnitor_inv_app {F : C ⥤ D} {X} : ((ρ_ F).inv : F ⟶ F otimes 𝟙_ _).app
 X = (ρ_ (F.obj X)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_inv_app {F : C ⥤ D} {X} :
    ((ρ_ F).inv : F ⟶ F ⊗ 𝟙_ _).app X = (ρ_ (F.obj X)).inv :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.associator_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Monoidal`。
形式化陈述：associator_hom_app {F G H : C ⥤ D} {X} : ((α_ F G H).hom : (F otimes G) ot
imes H ⟶ F otimes G otimes H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).hom : (F ⊗ G) ⊗ H ⟶ F ⊗ G ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom :=
  rfl

@[simp]
/-
**CategoryTheory.Monoidal.associator_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Monoidal`。
形式化陈述：associator_inv_app {F G H : C ⥤ D} {X} : ((α_ F G H).inv : F otimes G otim
es H ⟶ (F otimes G) otimes H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).inv : F ⊗ G ⊗ H ⟶ (F ⊗ G) ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv :=
  rfl

/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
/-
**CategoryTheory.Monoidal.functorCategoryMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Monoidal`。
形式化陈述：functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where tensorHom_def
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [BraidedCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/-- When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
/-
**CategoryTheory.Monoidal.functorCategoryBraided** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Monoidal`。
形式化陈述：functorCategoryBraided : BraidedCategory (C ⥤ D) where braiding F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
instance functorCategoryBraided : BraidedCategory (C ⥤ D) where
  braiding F G := NatIso.ofComponents fun _ => β_ _ _
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : BraidedCategory (C ⥤ D) :=
  CategoryTheory.Monoidal.functorCategoryBraided

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [SymmetricCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/-- When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
/-
**CategoryTheory.Monoidal.functorCategorySymmetric** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Monoidal`。
形式化陈述：functorCategorySymmetric : SymmetricCategory (C ⥤ D) where symmetry F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functorCategorySymmetric : SymmetricCategory (C ⥤ D) where
  symmetry F G := by ext X; apply symmetry

end SymmetricCategory

end Monoidal

set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Functor.LaxMonoidal.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {E : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       [inst_3 : CategoryTheory.MonoidalCategory D] →               [inst_4 : Ca
tegoryTheory.MonoidalCategory E] →                 (L : CategoryTheory.Functor D
 E) →                   [L.LaxMonoidal] → ((CategoryTheory.Functor.whiskeringRig
ht C D E).obj L).LaxMonoidal
参数：L : CategoryTheory.Functor D E；(CategoryTheory.Functor.whiskeringRight C D E)
.obj L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Functor.LaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.LaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).LaxMonoidal where
  ε := { app X := Functor.LaxMonoidal.ε L }
  μ F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Functor.OplaxMonoidal.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.OplaxMonoidal`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {E : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       [inst_3 : CategoryTheory.MonoidalCategory D] →               [inst_4 : Ca
tegoryTheory.MonoidalCategory E] →                 (L : CategoryTheory.Functor D
 E) →                   [L.OplaxMonoidal] → ((CategoryTheory.Functor.whiskeringR
ight C D E).obj L).OplaxMonoidal
参数：L : CategoryTheory.Functor D E；(CategoryTheory.Functor.whiskeringRight C D E)
.obj L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Functor.OplaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.OplaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).OplaxMonoidal where
  η := { app X := Functor.OplaxMonoidal.η L }
  δ F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality := by aesop
  oplax_right_unitality := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.Monoidal] :
    ((Functor.whiskeringRight C D E).obj L).Monoidal where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u_1) →           [inst_2 : CategoryTheory.Category.{v_1, u_1} E] →            
 [inst_3 : CategoryTheory.MonoidalCategory E] →               (F : CategoryTheor
y.Functor C D) → ((CategoryTheory.Functor.whiskeringLeft C D E).obj F).Monoidal
参数：E : Type u_1；F : CategoryTheory.Functor C D；(CategoryTheory.Functor.whiskerin
gLeft C D E).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Functor.Monoidal.whiskeringLeft
    (E : Type*) [Category* E] [MonoidalCategory E] (F : C ⥤ D) :
    ((whiskeringLeft _ _ E).obj F).Monoidal :=
  CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).functor.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.inverse).Monoidal
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).inverse.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.functor).Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).IsMonoidal where
  leftAdjoint_μ X Y := by
    ext
    simp [← Functor.map_comp]

end CategoryTheory

