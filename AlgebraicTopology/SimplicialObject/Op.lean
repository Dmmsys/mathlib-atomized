/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The covariant involution of the category of simplicial objects

In this file, we define the covariant involution `SimplicialObject.opFunctor`
of the category of simplicial objects that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

-/

@[expose] public section

universe v

open CategoryTheory

namespace SimplicialObject

variable {C : Type*} [Category.{v} C]

/-- The covariant involution of the category of simplicial objects
that is induced by the involution
`SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.
This functor is purposely not made `implicit_reducible` so as to avoid
confusion between `(opFunctor.obj X) _⦋n⦌` and `X _⦋n⦌`: use the
isomorphism `opObjIso`. -/
/-
**SimplicialObject.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SimplicialObject`。
形式化陈述：opFunctor : SimplicialObject C ⥤ SimplicialObject C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covariant involution of the category of simplicial objects
that is induced by the involution
`SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.
This functor is purposely not made `implicit_reducible` so as to avoid
confusion between `(opFunctor.obj X) _⦋n⦌` and `X _⦋n⦌`: use the
isomorphism `opObjIso`.
-/
def opFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

/-- The isomorphism `(opFunctor.obj X).obj n ≅ X.obj n` when `X` is a simplicial object. -/
/-
**SimplicialObject.opObjIso** 是 Mathlib 中的一个定义，位于命名空间 `SimplicialObject`。
形式化陈述：opObjIso {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ} : (opFunctor.obj
 X).obj n ≅ X.obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(opFunctor.obj X).obj n ≅ X.obj n` when `X` is a simplicial obj
ect.
-/
def opObjIso {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _

@[simp]
/-
**SimplicialObject.opFunctor_map_app** 是 Mathlib 中的一个引理，位于命名空间 `SimplicialObject
`。
形式化陈述：opFunctor_map_app {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCateg
oryᵒᵖ) : (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv
参数：f : X ⟶ Y；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opFunctor_map_app {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
/-
**SimplicialObject.opFunctor_obj_map** 是 Mathlib 中的一个引理，位于命名空间 `SimplicialObject
`。
形式化陈述：opFunctor_obj_map (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : 
n ⟶ m) : (opFunctor.obj X).map f = opObjIso.hom ≫ X.map (SimplexCategory.rev.map
 f.unop).op ≫ opObjIso.inv
参数：X : SimplicialObject C；f : n ⟶ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opFunctor_obj_map (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (opFunctor.obj X).map f =
      opObjIso.hom ≫ X.map (SimplexCategory.rev.map f.unop).op ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
/-
**SimplicialObject.opFunctor_obj_** 是 Mathlib 中的一个引理，位于命名空间 `SimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opFunctor_obj_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).δ i = opObjIso.hom ≫ X.δ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, SimplicialObject.δ]

@[simp]
/-
**SimplicialObject.opFunctor_obj_** 是 Mathlib 中的一个引理，位于命名空间 `SimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opFunctor_obj_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).σ i = opObjIso.hom ≫ X.σ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, SimplicialObject.σ]

/-- The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
is a covariant involution. -/
/-
**SimplicialObject.opFunctorCompOpFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Simplici
alObject`。
形式化陈述：opFunctorCompOpFunctorIso : opFunctor (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
is a covariant involution.
-/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]
/-
**SimplicialObject.opFunctorCompOpFunctorIso_hom_app_app** 是 Mathlib 中的一个引理，位于命名
空间 `SimplicialObject`。
形式化陈述：opFunctorCompOpFunctorIso_hom_app_app (X : SimplicialObject C) (n : Simple
xCategoryᵒᵖ) : (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opOb
jIso.hom
参数：X : SimplicialObject C；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `CategoryTheory.Functor.whiskeringLeftObjCompIso_inv_app_app`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `SimplexCategory.revCompRevIso_inv_app`：∀ (X : SimplexCategory), SimplexC
ategory.revCompRevIso.inv.app X = CategoryTheory.CategoryStruct.id X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.whiskeringLeftObjIdIso_hom_app_app`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {E : Type u₃} [inst_1 : CategoryT
heory.Category.{v₃, u₃} E]   (X : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opFunctorCompOpFunctorIso_hom_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opObjIso.hom := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]
/-
**SimplicialObject.opFunctorCompOpFunctorIso_inv_app_app** 是 Mathlib 中的一个引理，位于命名
空间 `SimplicialObject`。
形式化陈述：opFunctorCompOpFunctorIso_inv_app_app (X : SimplicialObject C) (n : Simple
xCategoryᵒᵖ) : (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opOb
jIso.inv
参数：X : SimplicialObject C；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskeringLeftObjIdIso_inv_app_app`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {E : Type u₃} [inst_1 : CategoryT
heory.Category.{v₃, u₃} E]   (X : CategoryTheor…
· 使用定理 `SimplexCategory.revCompRevIso_hom_app`：∀ (X : SimplexCategory), SimplexC
ategory.revCompRevIso.hom.app X = CategoryTheory.CategoryStruct.id X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.whiskeringLeftObjCompIso_hom_app_app`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opFunctorCompOpFunctorIso_inv_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opObjIso.inv := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

/-- The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
as an equivalence of categories. -/
@[simps]
/-
**SimplicialObject.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `SimplicialObject`。
形式化陈述：opEquivalence : SimplicialObject C ≌ SimplicialObject C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
as an equivalence of categories.
-/
def opEquivalence : SimplicialObject C ≌ SimplicialObject C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SimplicialObject

