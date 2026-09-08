/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, the inclusion of the full subcategory
of `κ`-presentable objects is a dense functor. This expresses canonically
any object `X : C` as a colimit of `κ`-presentable objects, and we show
that this is a `κ`-filtered colimit.

-/

public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (C κ) in
/-
**CategoryTheory.isCardinalFilteredGenerator_isCardinalPresentable** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isCardinalFilteredGenerator_isCardinalPresentable [IsCardinalAccessibleCat
egory C κ] : (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.exists_generator`：∀ (C : Typ
e u) [hC : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [hκ : Fact κ.IsR
egular]   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.of_le_isoClosu
re`：of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure) (h₂ : P' 
<= isCardinalPresentable C κ) : P'.IsCardinalFilteredGenerator κ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_eq_self`：isoClosure_eq_self [Is
ClosedUnderIsomorphisms P] : isoClosure P = P
· 使用定理 `CategoryTheory.instIsClosedUnderIsomorphismsIsCardinalPresentable`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (κ : Cardinal.{w}) [inst_
1 : Fact κ.IsRegular],   (CategoryTheory.isCardinalPres…
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

namespace IsCardinalAccessibleCategory

/-
**CategoryTheory.IsCardinalAccessibleCategory.final_toCostructuredArrow** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.IsCardinalAccessibleCategory`。
形式化陈述：final_toCostructuredArrow {J : Type u'} [Category.{v'} J] [EssentiallySmal
l.{w} J] [IsCardinalFiltered J κ] {X : C} (p : (isCardinalPresentable C κ).Colim
itOfShape J X) : p.toCostructuredArrow.Final
参数：p : (isCardinalPresentable C κ).ColimitOfShape J X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `CategoryTheory.instIsCardinalPresentableObjFullSubcategoryIsCardinalPres
entableι`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (κ : Cardi
nal.{w}) [inst_1 : Fact κ.IsRegular]   (X : (CategoryTheory.isCardinal…
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit'`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `CategoryTheory.instIsCardinalPresentableObjIsCardinalPresentable`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (κ : Cardinal.{w}) [inst_1
 : Fact κ.IsRegular]   (X : (CategoryTheory.isCardinal…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.toCostructuredArrow_map`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory
.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
-/
instance final_toCostructuredArrow
    {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    [IsCardinalFiltered J κ] {X : C}
    (p : (isCardinalPresentable C κ).ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsCardinalAccessibleCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.IsCardinalAccessibleCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).ι.IsDense where
  isDenseAt X := by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩
/-
**CategoryTheory.IsCardinalAccessibleCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.IsCardinalAccessibleCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCardinalAccessibleCategory C κ] (X : C) :
    IsCardinalFiltered (CostructuredArrow (isCardinalPresentable C κ).ι X) κ := by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  exact IsCardinalFiltered.of_final p.toCostructuredArrow κ

end IsCardinalAccessibleCategory

namespace IsFinitelyAccessibleCategory

/-
**CategoryTheory.IsFinitelyAccessibleCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.IsFinitelyAccessibleCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFinitelyAccessibleCategory.{w} C] (X : C) :
    IsFiltered (CostructuredArrow (ObjectProperty.isFinitelyPresentable.{w} C).ι X) := by
  rw [← CategoryTheory.isCardinalFiltered_aleph0_iff.{w},
    ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance
/-
**CategoryTheory.IsFinitelyAccessibleCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.IsFinitelyAccessibleCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFinitelyAccessibleCategory.{w} C] :
    (ObjectProperty.isFinitelyPresentable.{w} C).ι.IsDense := by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance
/-
**CategoryTheory.IsFinitelyAccessibleCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.IsFinitelyAccessibleCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFinitelyAccessibleCategory.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (ObjectProperty.isFinitelyPresentable.{w} C) := by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

end IsFinitelyAccessibleCategory

end CategoryTheory

