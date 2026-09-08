/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v u

namespace CategoryTheory

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable (C : Type u) [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/-- The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).

Note: due to the fact that composition of functors in mathlib is reversed compared to the
one usually found in the literature, this monoidal structure is in fact the monoidal
opposite of the one usually considered in the literature.
-/
@[instance_reducible]
/-
**CategoryTheory.endofunctorMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C) where tensorObj F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).

Note: due to the fact that composition of functors in mathlib is reversed compar
ed to the
one usually found in the literature, this monoidal structure is in fact the mono
idal
opposite of the one usually considered in the literature.
-/
def endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C) where
  tensorObj F G := F ⋙ G
  whiskerLeft X _ _ F := Functor.whiskerLeft X F
  whiskerRight F X := Functor.whiskerRight F X
  tensorHom α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F

open CategoryTheory.MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory
/-
**CategoryTheory.endofunctorMonoidalCategory_tensorUnit_obj** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (X : C),   (Categ
oryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Functor C C)).obj X 
= X
参数：C : Type u；X : C；CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTh
eory.Functor C C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_tensorUnit_obj (X : C) :
    (𝟙_ (C ⥤ C)).obj X = X := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_tensorUnit_map** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y),   (CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Functo
r C C)).map f = f
参数：C : Type u；f : X ⟶ Y；CategoryTheory.MonoidalCategoryStruct.tensorUnit (Catego
ryTheory.Functor C C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_tensorUnit_map {X Y : C} (f : X ⟶ Y) :
    (𝟙_ (C ⥤ C)).map f = f := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_tensorObj_obj** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F G : CategoryTh
eory.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.tensorObj F 
G).obj X = G.obj (F.obj X)
参数：C : Type u；F G : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCate
goryStruct.tensorObj F G；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_tensorObj_obj (F G : C ⥤ C) (X : C) :
    (F ⊗ G).obj X = G.obj (F.obj X) := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_tensorObj_map** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F G : CategoryTh
eory.Functor C C) {X Y : C} (f : X ⟶ Y),   (CategoryTheory.MonoidalCategoryStruc
t.tensorObj F G).map f = G.map (F.map f)
参数：C : Type u；F G : CategoryTheory.Functor C C；f : X ⟶ Y；CategoryTheory.Monoidal
CategoryStruct.tensorObj F G；F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_tensorObj_map (F G : C ⥤ C) {X Y : C} (f : X ⟶ Y) :
    (F ⊗ G).map f = G.map (F.map f) := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_tensorMap_app** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {F G H K : Catego
ryTheory.Functor C C} {α : F ⟶ G} {β : H ⟶ K}   (X : C),   (CategoryTheory.Monoi
dalCategoryStruct.tensorHom α β).app X =     CategoryTheory.CategoryStruct.comp 
(β.app (F.obj X)) (K.map (α.app X))
参数：C : Type u；X : C；CategoryTheory.MonoidalCategoryStruct.tensorHom α β；β.app (F
.obj X)；K.map (α.app X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_tensorMap_app
    {F G H K : C ⥤ C} {α : F ⟶ G} {β : H ⟶ K} (X : C) :
    (α ⊗ₘ β).app X = β.app (F.obj X) ≫ K.map (α.app X) := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_whiskerLeft_app** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {F H K : Category
Theory.Functor C C} {β : H ⟶ K} (X : C),   (CategoryTheory.MonoidalCategoryStruc
t.whiskerLeft F β).app X = β.app (F.obj X)
参数：C : Type u；X : C；CategoryTheory.MonoidalCategoryStruct.whiskerLeft F β；F.obj 
X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_whiskerLeft_app
    {F H K : C ⥤ C} {β : H ⟶ K} (X : C) :
    (F ◁ β).app X = β.app (F.obj X) := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_whiskerRight_app** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {F G H : Category
Theory.Functor C C} {α : F ⟶ G} (X : C),   (CategoryTheory.MonoidalCategoryStruc
t.whiskerRight α H).app X = H.map (α.app X)
参数：C : Type u；X : C；CategoryTheory.MonoidalCategoryStruct.whiskerRight α H；α.app
 X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_whiskerRight_app
    {F G H : C ⥤ C} {α : F ⟶ G} (X : C) :
    (α ▷ H).app X = H.map (α.app X) := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_associator_hom_app** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F G H : Category
Theory.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.associator
 F G H).hom.app X =     CategoryTheory.CategoryStruct.id       ((CategoryTheory.
MonoidalCategoryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.tensorOb
j F G) H).obj X)
参数：C : Type u；F G H : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCa
tegoryStruct.associator F G H；(CategoryTheory.MonoidalCategoryStruct.tensorObj (
CategoryTheory.MonoidalCategoryStruct.tensorObj F G) H).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_associator_hom_app (F G H : C ⥤ C) (X : C) :
    (α_ F G H).hom.app X = 𝟙 _ := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_associator_inv_app** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F G H : Category
Theory.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.associator
 F G H).inv.app X =     CategoryTheory.CategoryStruct.id       ((CategoryTheory.
MonoidalCategoryStruct.tensorObj F (CategoryTheory.MonoidalCategoryStruct.tensor
Obj G H)).obj X)
参数：C : Type u；F G H : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCa
tegoryStruct.associator F G H；(CategoryTheory.MonoidalCategoryStruct.tensorObj F
 (CategoryTheory.MonoidalCategoryStruct.tensorObj G H)).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_associator_inv_app (F G H : C ⥤ C) (X : C) :
    (α_ F G H).inv.app X = 𝟙 _ := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_leftUnitor_hom_app** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.leftUnitor F).
hom.app X =     CategoryTheory.CategoryStruct.id       ((CategoryTheory.Monoidal
CategoryStruct.tensorObj             (CategoryTheory.MonoidalCategoryStruct.tens
orUnit (CategoryTheory.Functor C C)) F).obj         X)
参数：C : Type u；F : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCatego
ryStruct.leftUnitor F；(CategoryTheory.MonoidalCategoryStruct.tensorObj          
   (CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Functor C C
)) F).obj         X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_leftUnitor_hom_app (F : C ⥤ C) (X : C) :
    (λ_ F).hom.app X = 𝟙 _ := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_leftUnitor_inv_app** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.leftUnitor F).
inv.app X = CategoryTheory.CategoryStruct.id (F.obj X)
参数：C : Type u；F : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCatego
ryStruct.leftUnitor F；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_leftUnitor_inv_app (F : C ⥤ C) (X : C) :
    (λ_ F).inv.app X = 𝟙 _ := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_rightUnitor_hom_app** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.rightUnitor F)
.hom.app X =     CategoryTheory.CategoryStruct.id       ((CategoryTheory.Monoida
lCategoryStruct.tensorObj F             (CategoryTheory.MonoidalCategoryStruct.t
ensorUnit (CategoryTheory.Functor C C))).obj         X)
参数：C : Type u；F : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCatego
ryStruct.rightUnitor F；(CategoryTheory.MonoidalCategoryStruct.tensorObj F       
      (CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Functor 
C C))).obj         X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_rightUnitor_hom_app (F : C ⥤ C) (X : C) :
    (ρ_ F).hom.app X = 𝟙 _ := rfl
/-
**CategoryTheory.endofunctorMonoidalCategory_rightUnitor_inv_app** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C C) (X : C),   (CategoryTheory.MonoidalCategoryStruct.rightUnitor F)
.inv.app X = CategoryTheory.CategoryStruct.id (F.obj X)
参数：C : Type u；F : CategoryTheory.Functor C C；X : C；CategoryTheory.MonoidalCatego
ryStruct.rightUnitor F；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem endofunctorMonoidalCategory_rightUnitor_inv_app (F : C ⥤ C) (X : C) :
    (ρ_ F).inv.app X = 𝟙 _ := rfl

namespace MonoidalCategory

variable [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
/-
**CategoryTheory.MonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C
`.
-/
instance : (tensoringRight C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (rightUnitorNatIso C).symm
      μIso := fun X Y => (Functor.isoWhiskerRight (curriedAssociatorNatIso C)
      ((evaluation C (C ⥤ C)).obj X ⋙ (evaluation C C).obj Y)) }

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalCategory.tensoringRight_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensoringRight_ε :
    ε (tensoringRight C) = (rightUnitorNatIso C).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalCategory.tensoringRight_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensoringRight_η :
    η (tensoringRight C) = (rightUnitorNatIso C).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalCategory.tensoringRight_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensoringRight_μ (X Y : C) (Z : C) :
    (μ (tensoringRight C) X Y).app Z = (α_ Z X Y).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalCategory.tensoringRight_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensoringRight_δ (X Y : C) (Z : C) :
    (δ (tensoringRight C) X Y).app Z = (α_ Z X Y).inv := rfl

end MonoidalCategory

variable {C}
variable {M : Type*} [Category* M] [MonoidalCategory M] (F : M ⥤ (C ⥤ C))

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_δ_app (i j : M) (X : C) [F.Monoidal] :
    (μ F i j).app X ≫ (δ F i j).app X = 𝟙 _ :=
  (μIso F i j).hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_μ_app (i j : M) (X : C) [F.Monoidal] :
    (δ F i j).app X ≫ (μ F i j).app X = 𝟙 _ :=
  (μIso F i j).inv_hom_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ε_η_app (X : C) [F.Monoidal] : (ε F).app X ≫ (η F).app X = 𝟙 _ :=
  (εIso F).hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem η_ε_app (X : C) [F.Monoidal] : (η F).app X ≫ (ε F).app X = 𝟙 _ :=
  (εIso F).inv_hom_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ε_naturality {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (ε F).app X ≫ (F.obj (𝟙_ M)).map f = f ≫ (ε F).app Y :=
  ((ε F).naturality f).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem η_naturality {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal] :
    (η F).app X ≫ (𝟙_ (C ⥤ C)).map f = (η F).app X ≫ f := by
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (F.obj n).map ((F.obj m).map f) ≫ (μ F m n).app Y = (μ F m n).app X ≫ (F.obj _).map f :=
  (μ F m n).naturality f

-- This is a simp lemma in the reverse direction via `NatTrans.naturality`.
@[reassoc]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.obj n).map ((F.obj m).map f) =
      (F.obj _).map f ≫ (δ F m n).app Y := by simp

-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (μ F m' n').app X =
      (μ F m n).app X ≫ (F.map (f ⊗ₘ g)).app X := by
  have := congr_app (μ_natural F f g) X
  dsimp at this
  simpa using this

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.LaxMonoidal] :
    (F.obj n).map ((F.map f).app X) ≫ (μ F m' n).app X =
      (μ F m n).app X ≫ (F.map (f ▷ n)).app X := by
  rw [← tensorHom_id, ← μ_naturality₂ F f (𝟙 n) X]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (μ F m n').app X =
      (μ F m n).app X ≫ (F.map (m ◁ g)).app X := by
  rw [← id_tensorHom, ← μ_naturality₂ F (𝟙 m) g X]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.obj n).map ((F.map f).app X) =
      (F.map (f ▷ n)).app X ≫ (δ F m' n).app X :=
  congr_app (δ_natural_left F f n) X

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.map g).app ((F.obj m).obj X) =
      (F.map (m ◁ g)).app X ≫ (δ F m n').app X :=
  congr_app (δ_natural_right F m g) X

@[reassoc]
/-
**CategoryTheory.left_unitality_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：left_unitality_app (n : M) (X : C) [F.LaxMonoidal] : (F.obj n).map ((ε F).
app X) ≫ (μ F (𝟙_ M) n).app X ≫ (F.map (fun_ n).hom).app X = 𝟙 _
参数：n : M；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.left_unitality`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
-/
theorem left_unitality_app (n : M) (X : C) [F.LaxMonoidal] :
    (F.obj n).map ((ε F).app X) ≫ (μ F (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X = 𝟙 _ :=
  congr_app (left_unitality F n).symm X

@[simp, reassoc]
/-
**CategoryTheory.obj_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_ε_app (n : M) (X : C) [F.Monoidal] :
    (F.obj n).map ((ε F).app X) = (F.map (λ_ n).inv).app X ≫ (δ F (𝟙_ M) n).app X := by
  rw [map_leftUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app, endofunctorMonoidalCategory_tensorObj_obj,
    Category.comp_id]

@[simp, reassoc]
/-
**CategoryTheory.obj_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_η_app (n : M) (X : C) [F.Monoidal] :
    (F.obj n).map ((η F).app X) = (μ F (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X := by
  rw [← cancel_mono ((F.obj n).map ((ε F).app X)), ← Functor.map_comp]
  simp

@[reassoc]
/-
**CategoryTheory.right_unitality_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：right_unitality_app (n : M) (X : C) [F.Monoidal] : (ε F).app ((F.obj n).ob
j X) ≫ (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _
参数：n : M；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.right_unitality`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
-/
theorem right_unitality_app (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) ≫ (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _ :=
  congr_app (Functor.LaxMonoidal.right_unitality F n).symm X

@[simp]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ε_app_obj (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) = (F.map (ρ_ n).inv).app X ≫ (δ F n (𝟙_ M)).app X := by
  rw [map_rightUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[simp]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem η_app_obj (n : M) (X : C) [F.Monoidal] :
    (η F).app ((F.obj n).obj X) = (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X := by
  rw [map_rightUnitor]
  dsimp
  simp only [Category.comp_id, μ_δ_app_assoc]

set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc]
/-
**CategoryTheory.associativity_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：associativity_app (m₁ m₂ m₃ : M) (X : C) [F.LaxMonoidal] : (F.obj m₃).map 
((μ F m₁ m₂).app X) ≫ (μ F (m₁ otimes m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).
app X = (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫ (μ F m₁ (m₂ otimes m₃)).app X
参数：m₁ m₂ m₃ : M；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory 
C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem associativity_app (m₁ m₂ m₃ : M) (X : C) [F.LaxMonoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) ≫
        (μ F (m₁ ⊗ m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).app X =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫ (μ F m₁ (m₂ ⊗ m₃)).app X := by
  have := congr_app (associativity F m₁ m₂ m₃) X
  dsimp at this
  simpa using this

@[simp, reassoc]
/-
**CategoryTheory.obj_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_μ_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫
        (μ F m₁ (m₂ ⊗ m₃)).app X ≫
          (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (δ F (m₁ ⊗ m₂) m₃).app X := by
  rw [← associativity_app_assoc]
  simp

@[simp, reassoc]
/-
**CategoryTheory.obj_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((δ F m₁ m₂).app X) =
      (μ F (m₁ ⊗ m₂) m₃).app X ≫
        (F.map (α_ m₁ m₂ m₃).hom).app X ≫
          (δ F m₁ (m₂ ⊗ m₃)).app X ≫ (δ F m₂ m₃).app ((F.obj m₁).obj X) := by
  rw [map_associator]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app_assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.obj_zero_map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) [F.Monoidal] :
    (F.obj (𝟙_ M)).map f ≫ (μ F m (𝟙_ M)).app _ =
    (η F).app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ := by
  rw [← cancel_epi ((ε F).app _), ← cancel_mono ((δ F _ _).app _)]
  simp

@[simp]
/-
**CategoryTheory.obj_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem obj_μ_zero_app (m₁ m₂ : M) (X : C) [F.Monoidal] :
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫ (μ F m₁ (𝟙_ M ⊗ m₂)).app X ≫
    (F.map (α_ m₁ (𝟙_ M) m₂).inv).app X ≫ (δ F (m₁ ⊗ 𝟙_ M) m₂).app X =
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫
    (F.map (λ_ m₂).hom).app ((F.obj m₁).obj X) ≫ (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) := by
  rw [← obj_η_app_assoc, ← Functor.map_comp]
  simp

/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps!]
/-
**CategoryTheory.unitOfTensorIsoUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：unitOfTensorIsoUnit (m n : M) (h : m otimes n ≅ 𝟙_ M) [F.Monoidal] : F.obj
 m ⋙ F.obj n ≅ 𝟭 C
参数：m n : M；h : m otimes n ≅ 𝟙_ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`.
-/
noncomputable def unitOfTensorIsoUnit (m n : M) (h : m ⊗ n ≅ 𝟙_ M) [F.Monoidal] :
    F.obj m ⋙ F.obj n ≅ 𝟭 C :=
  μIso F m n ≪≫ F.mapIso h ≪≫ (εIso F).symm

/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps]
/-
**CategoryTheory.equivOfTensorIsoUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：equivOfTensorIsoUnit (m n : M) (h₁ : m otimes n ≅ 𝟙_ M) (h₂ : n otimes m ≅
 𝟙_ M) (H : h₁.hom ▷ m ≫ (fun_ m).hom = (α_ m n m).hom ≫ m ◁ h₂.hom ≫ (ρ_ m).hom
) [F.Monoidal] : C ≌ C where functor
参数：m n : M；h₁ : m otimes n ≅ 𝟙_ M；h₂ : n otimes m ≅ 𝟙_ M；H : h₁.hom ▷ m ≫ (fun_ 
m).hom = (α_ m n m).hom ≫ m ◁ h₂.hom ≫ (ρ_ m).hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`.
-/
noncomputable def equivOfTensorIsoUnit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_ M) (h₂ : n ⊗ m ≅ 𝟙_ M)
    (H : h₁.hom ▷ m ≫ (λ_ m).hom = (α_ m n m).hom ≫ m ◁ h₂.hom ≫ (ρ_ m).hom) [F.Monoidal] :
    C ≌ C where
  functor := F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp X := by
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, η_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, δ_μ_app_assoc, obj_ε_app,
      unitOfTensorIsoUnit_inv_app]
    simp only [← NatTrans.comp_app, ← F.map_comp, ← H, inv_hom_whiskerRight_assoc,
      Iso.inv_hom_id, Functor.map_id, NatTrans.id_app]

end CategoryTheory

