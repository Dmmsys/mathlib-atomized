/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

public section


noncomputable section

universe v u w t

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category* J]

namespace TopCat

/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : HasLimitsOfShape J (Presheaf C X) :=
  functorCategoryHasLimitsOfShape
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] (X : TopCat.{v}) : HasLimits.{v} (Presheaf C X) where
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape J C] (X : TopCat) : HasColimitsOfShape J (Presheaf C X) :=
  functorCategoryHasColimitsOfShape
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits.{v, u} C] (X : TopCat.{t}) : HasColimitsOfSize.{v, v} (Presheaf C X) where
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : CreatesLimitsOfShape J (Sheaf.forget C X) :=
  inferInstanceAs <| CreatesLimitsOfShape J (sheafToPresheaf _ _)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : HasLimitsOfShape J (Sheaf C X) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Sheaf.forget C X)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] (X : TopCat) : CreatesLimits.{v, v} (Sheaf.forget C X) where
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] (X : TopCat.{v}) : HasLimitsOfSize.{v, v} (Sheaf.{v} C X) where

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.isSheaf_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isSheaf_of_isLimit [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Preshe
af.{v} C X) (H : forall j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.
pt.IsSheaf
参数：F : J ⥤ Presheaf.{v} C X；H : forall j, (F.obj j).IsSheaf；hc : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `TopCat.Presheaf.isSheaf_of_iso`：isSheaf_of_iso {F G : Presheaf C X} (α :
 F ≅ G) (h : F.IsSheaf) : G.IsSheaf
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `TopCat.instHasLimitsOfShapeSheaf`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]   
[CategoryTheory.Limits…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem isSheaf_of_isLimit [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf := by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso hc e)
    (limit F').2
/-
**TopCat.limit_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：limit_isSheaf [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v
} C X) (H : forall j, (F.obj j).IsSheaf) : (limit F).IsSheaf
参数：F : J ⥤ Presheaf.{v} C X；H : forall j, (F.obj j).IsSheaf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.isSheaf_of_isLimit`：isSheaf_of_isLimit [HasLimitsOfShape J C] {X 
: TopCat.{v}} (F : J ⥤ Presheaf.{v} C X) (H : forall j, (F.obj j).IsSheaf) {c : 
Cone F} (hc : I…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
-/
theorem limit_isSheaf [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)

end TopCat

