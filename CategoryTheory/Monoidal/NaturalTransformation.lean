/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

namespace NatTrans

open Functor.LaxMonoidal

/-- A natural transformation between (lax) monoidal functors is monoidal if it satisfies
`ε F ≫ τ.app (𝟙_ C) = ε G` and `μ F X Y ≫ app (X ⊗ Y) = (app X ⊗ₘ app Y) ≫ μ G X Y`. -/
/-
**CategoryTheory.NatTrans.IsMonoidal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：IsMonoidal : Prop where unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation between (lax) monoidal functors is monoidal if it satis
fies
`ε F ≫ τ.app (𝟙_ C) = ε G` and `μ F X Y ≫ app (X ⊗ Y) = (app X ⊗ₘ app Y) ≫ μ G X
 Y`.
-/
class IsMonoidal : Prop where
  unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂ := by cat_disch
  tensor (X Y : C) : μ F₁ _ _ ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ F₂ _ _ := by cat_disch

namespace IsMonoidal

attribute [reassoc (attr := simp)] unit tensor

/-
**CategoryTheory.NatTrans.IsMonoidal.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.NatTrans.IsMonoidal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F₁ : CategoryTheory
.Functor C D} [inst_4 : F₁.LaxMonoidal],   CategoryTheory.NatTrans.IsMonoidal (C
ategoryTheory.CategoryStruct.id F₁)
参数：CategoryTheory.CategoryStruct.id F₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance id : IsMonoidal (𝟙 F₁) where
/-
**CategoryTheory.NatTrans.IsMonoidal.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.NatTrans.IsMonoidal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F₁ F₂ F₃ : Category
Theory.Functor C D} (τ : F₁ ⟶ F₂) [inst_4 : F₁.LaxMonoidal] [inst_5 : F₂.LaxMono
idal]   [inst_6 : F₃.LaxMonoidal] (τ' : F₂ ⟶ F₃) [CategoryTheory.NatTrans.IsMono
idal τ]   [CategoryTheory.NatTrans.IsMonoidal τ'], CategoryTheory.NatTrans.IsMon
oidal (CategoryTheory.CategoryStruct.comp τ τ')
参数：τ : F₁ ⟶ F₂；τ' : F₂ ⟶ F₃；CategoryTheory.CategoryStruct.comp τ τ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.unit_assoc`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} 
{D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.unit`：∀ {C : Type u₁} {inst : Categor
yTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : T
ype u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.tensor_assoc`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C
} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.tensor`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
-/
instance comp (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ'] :
    IsMonoidal (τ ≫ τ') where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.IsMonoidal.hcomp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.NatTrans.IsMonoidal`。
形式化陈述：hcomp {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂) [Is
Monoidal τ] [IsMonoidal τ'] : IsMonoidal (τ ◫ τ') where unit
参数：τ' : G₁ ⟶ G₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.unit`：∀ {C : Type u₁} {inst : Categor
yTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : T
ype u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.unit_assoc`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} 
{D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.tensor_assoc`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C
} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.tensor`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
-/
instance hcomp {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
    [IsMonoidal τ] [IsMonoidal τ'] : IsMonoidal (τ ◫ τ') where
  unit := by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, ← tensorHom_comp_tensorHom, μ_natural_assoc]
    simp only [← map_comp, tensor]
/-
**CategoryTheory.NatTrans.IsMonoidal.whiskerRight** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.NatTrans.IsMonoidal`。
形式化陈述：whiskerRight {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ] : IsMonoidal (Fu
nctor.whiskerRight τ G₁)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hcomp_id`：hcomp_id {G H : C ⥤ D} (α : G ⟶ H) (F :
 D ⥤ E) : α ◫ 𝟙 F = whiskerRight α F
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.id`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : Typ
e u₂}   [inst_2 : CategoryT…
-/
instance whiskerRight {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ] :
    IsMonoidal (Functor.whiskerRight τ G₁) := by
  rw [← Functor.hcomp_id]
  infer_instance
/-
**CategoryTheory.NatTrans.IsMonoidal.whiskerLeft** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.NatTrans.IsMonoidal`。
形式化陈述：whiskerLeft {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G
₂) [IsMonoidal τ'] : IsMonoidal (Functor.whiskerLeft F₁ τ')
参数：τ' : G₁ ⟶ G₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.id_hcomp`：id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α :
 G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.id`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : Typ
e u₂}   [inst_2 : CategoryT…
-/
instance whiskerLeft {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
    (τ' : G₁ ⟶ G₂) [IsMonoidal τ'] :
    IsMonoidal (Functor.whiskerLeft F₁ τ') := by
  rw [← Functor.id_hcomp]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.IsMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
NatTrans.IsMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.leftUnitor.hom where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.IsMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
NatTrans.IsMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.rightUnitor.hom where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.IsMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
NatTrans.IsMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] :
    NatTrans.IsMonoidal (Functor.associator F G H).hom where
  unit := by
    simp only [comp_obj, comp_ε, assoc, Functor.map_comp, associator_hom_app, comp_id,
      Functor.comp_map]
  tensor X Y := by
    simp only [comp_obj, comp_μ, associator_hom_app, Functor.comp_map, map_comp,
      comp_id, tensorHom_id, id_whiskerRight, assoc, id_comp]

end IsMonoidal

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : C ⥤ D} {H K : C ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
    [F.LaxMonoidal] [G.LaxMonoidal] [IsMonoidal α]
    [H.LaxMonoidal] [K.LaxMonoidal] [IsMonoidal β] :
    IsMonoidal (NatTrans.prod' α β) where
  unit := by
    ext
    · rw [prod_comp_fst, prod'_ε_fst, prod'_ε_fst, prod'_app_fst, IsMonoidal.unit]
    · rw [prod_comp_snd, prod'_ε_snd, prod'_ε_snd, prod'_app_snd, IsMonoidal.unit]
  tensor X Y := by
    ext
    · simp only [prod_comp_fst, prod'_μ_fst, prod'_app_fst,
        prodMonoidal_tensorHom, IsMonoidal.tensor]
    · simp only [prod_comp_snd, prod'_μ_snd, prod'_app_snd,
        prodMonoidal_tensorHom, IsMonoidal.tensor]

end NatTrans

namespace Iso

variable (e : F₁ ≅ F₂) [NatTrans.IsMonoidal e.hom]

/-
**CategoryTheory.Iso.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Iso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.IsMonoidal e.inv where
  unit := by rw [← NatTrans.IsMonoidal.unit (τ := e.hom), assoc, hom_inv_id_app, comp_id]
  tensor X Y := by
    rw [← cancel_mono (e.hom.app (X ⊗ Y)), assoc, assoc, inv_hom_id_app, comp_id,
      NatTrans.IsMonoidal.tensor, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      inv_hom_id_app, inv_hom_id_app, tensorHom_id, id_whiskerRight, id_comp]

end Iso

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace IsMonoidal

variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.IsMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Adjunction.IsMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.IsMonoidal adj.unit where
  unit := by
    dsimp
    rw [id_comp, ← unit_app_unit_comp_map_η adj, assoc, Monoidal.map_η_ε]
    dsimp
    rw [comp_id]
  tensor X Y := by
    dsimp
    rw [← unit_app_tensor_comp_map_δ_assoc, id_comp, Monoidal.map_δ_μ, comp_id]
/-
**CategoryTheory.Adjunction.IsMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Adjunction.IsMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.IsMonoidal adj.counit where
  unit := by
    dsimp
    rw [assoc, map_ε_comp_counit_app_unit adj, ε_η]
  tensor X Y := by
    dsimp
    rw [assoc, map_μ_comp_counit_app_tensor, μ_δ_assoc, comp_id]

end IsMonoidal

namespace Equivalence

variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

/-
**CategoryTheory.Adjunction.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Adjunction.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.IsMonoidal e.unit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.unit)
/-
**CategoryTheory.Adjunction.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Adjunction.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.IsMonoidal e.counit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.counit)

end Equivalence

end Adjunction

namespace LaxMonoidalFunctor

/-- The type of monoidal natural transformations between (bundled) lax monoidal functors. -/
/-
**CategoryTheory.LaxMonoidalFunctor.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.LaxMonoidalFunctor`。
形式化陈述：Hom (F G : LaxMonoidalFunctor C D) where /-- the natural transformation be
tween the underlying functors -/ hom : F.toFunctor ⟶ G.toFunctor isMonoidal : Na
tTrans.IsMonoidal hom
参数：F G : LaxMonoidalFunctor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of monoidal natural transformations between (bundled) lax monoidal func
tors.
-/
structure Hom (F G : LaxMonoidalFunctor C D) where
  /-- the natural transformation between the underlying functors -/
  hom : F.toFunctor ⟶ G.toFunctor
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal
/-
**CategoryTheory.LaxMonoidalFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
axMonoidalFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (LaxMonoidalFunctor C D) where
  Hom := Hom
  comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[simp]
/-
**CategoryTheory.LaxMonoidalFunctor.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.LaxMonoidalFunctor`。
形式化陈述：id_hom (F : LaxMonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 _
参数：F : LaxMonoidalFunctor C D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (F : LaxMonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 _ := rfl

@[reassoc, simp]
/-
**CategoryTheory.LaxMonoidalFunctor.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.LaxMonoidalFunctor`。
形式化陈述：comp_hom {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β
).hom = α.hom ≫ β.hom
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
/-
**CategoryTheory.LaxMonoidalFunctor.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.LaxMonoidalFunctor`。
形式化陈述：hom_ext {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) :
 α = β
参数：h : α.hom = β.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hom_ext {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β := by
  cases α; cases β; subst h; rfl

/-- Constructor for morphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
/-
**CategoryTheory.LaxMonoidalFunctor.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LaxMonoidalFunctor`。
形式化陈述：homMk {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatT
rans.IsMonoidal f] : F ⟶ G
参数：f : F.toFunctor ⟶ G.toFunctor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in the category `LaxMonoidalFunctor C D`.
-/
def homMk {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

/-- Constructor for isomorphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
/-
**CategoryTheory.LaxMonoidalFunctor.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LaxMonoidalFunctor`。
形式化陈述：isoMk {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor) [NatT
rans.IsMonoidal e.hom] : F ≅ G where hom
参数：e : F.toFunctor ≅ G.toFunctor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category `LaxMonoidalFunctor C D`.
-/
def isoMk {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

open Functor.LaxMonoidal

/-- Constructor for isomorphisms between lax monoidal functors. -/
@[simps!]
/-
**CategoryTheory.LaxMonoidalFunctor.isoOfComponents** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.LaxMonoidalFunctor`。
形式化陈述：isoOfComponents {F G : LaxMonoidalFunctor C D} (e : forall X, F.obj X ≅ G.
obj X) (naturality : forall {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).h
om ≫ G.map f
参数：e : forall X, F.obj X ≅ G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms between lax monoidal functors.
-/
def isoOfComponents {F G : LaxMonoidalFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

end LaxMonoidalFunctor

namespace Functor.Monoidal

/--
Transporting a monoidal structure along a natural isomorphism of functors makes the isomorphism
a monoidal natural transformation.
-/
/-
**CategoryTheory.Functor.Monoidal.natTransIsMonoidal_of_transport** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：natTransIsMonoidal_of_transport {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G) : l
etI : G.Monoidal
参数：e : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transporting a monoidal structure along a natural isomorphism of functors makes 
the isomorphism
a monoidal natural transformation.
-/
lemma natTransIsMonoidal_of_transport {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G) :
    letI : G.Monoidal := transport e
    e.hom.IsMonoidal := by
  let : G.Monoidal := transport e
  refine ⟨rfl, fun X Y ↦ ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

end Functor.Monoidal

end CategoryTheory

