/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Tensor product of colimits

In this file, we apply the `PreservesColimit₂` API to the bifunctor
`curriedTensor C` on a monoidal category `C`.

Given cocones `c₁` and `c₂` for functors `F₁ : J₁ ⥤ C` and `F₂ : J₂ ⥤ C`,
we define a cocone `c₁.tensor₂ c₂` for the functor `J₁ × J₂ ⥤ C` obtained
using the tensor product on `C`, and we obtain that it is a colimit cocone
if both `c₁` and `c₂` are, and `PreservesColimit₂ F₁ F₂ (curriedTensor C)` holds.

We also introduce a definition `Cocone.tensor` which takes as an input two
cocones `c₁` and `c₂` for two functors `F₁ : J ⥤ C` and `F₂ : J ⥤ C` and
produces a cocone for `F₁ ⊗ F₂ : J ⥤ C` with point `c₁.pt ⊗ c₂.pt` and we show
that it is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds and `J` is sifted.

-/

@[expose] public section

namespace CategoryTheory.Limits

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J J₁ J₂ : Type*} [Category* J] [Category* J₁] [Category* J₂]

section

variable {F₁ : J₁ ⥤ C} {F₂ : J₂ ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

variable (c₁ c₂) in
/-- The external tensor product of two cocones. -/
/-
**CategoryTheory.Limits.Cocone.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cocone`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       {J : Type u_2} →         [inst
_2 : CategoryTheory.Category.{v_2, u_2} J] →           {F₁ F₂ : CategoryTheory.F
unctor J C} →             CategoryTheory.Limits.Cocone F₁ →               Catego
ryTheory.Limits.Cocone F₂ →                 CategoryTheory.Limits.Cocone (Catego
ryTheory.MonoidalCategoryStruct.tensorObj F₁ F₂)
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj F₁ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The external tensor product of two cocones.
-/
abbrev Cocone.tensor₂ :
    Cocone (externalProduct F₁ F₂) :=
  (curriedTensor C).mapCocone₂ c₁ c₂

/-- The external tensor product of colimit cocones for functors `F₁ : J₁ ⥤ C`
and `F₂ : J₂ ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds. -/
/-
**CategoryTheory.Limits.IsColimit.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsColimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       {J : Type u_2} →         [inst
_2 : CategoryTheory.Category.{v_2, u_2} J] →           {F₁ F₂ : CategoryTheory.F
unctor J C} →             {c₁ : CategoryTheory.Limits.Cocone F₁} →              
 {c₂ : CategoryTheory.Limits.Cocone F₂} →                 [CategoryTheory.Limits
.PreservesColimit₂ F₁ F₂ (CategoryTheory.MonoidalCategory.curriedTensor C)] →   
                [CategoryTheory.IsSifted J] →                     CategoryTheory
.Limits.IsColimit c₁ →                       CategoryTheory.Limits.IsColimit c₂ 
→ CategoryTheory.Limits.IsColimit (c₁.tensor c₂)
参数：CategoryTheory.MonoidalCategory.curriedTensor C；c₁.tensor c₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSifted.toFinal`：∀ {C : Type u} {inst : CategoryTheory.C
ategory.{v, u} C} [self : CategoryTheory.IsSifted C],   (CategoryTheory.Functor.
diag C).Final

--- 原说明 ---
The external tensor product of colimit cocones for functors `F₁ : J₁ ⥤ C`
and `F₂ : J₂ ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTens
or C)`
holds.
-/
noncomputable def IsColimit.tensor₂ [PreservesColimit₂ F₁ F₂ (curriedTensor C)]
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.tensor₂ c₂) :=
  isColimitOfPreserves₂ (curriedTensor C) hc₁ hc₂

end

section

variable {F₁ F₂ : J ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

set_option backward.defeqAttrib.useBackward true in
variable (c₁ c₂) in
/-- The tensor product of two cocones. -/
@[simps!]
/-
**CategoryTheory.Limits.Cocone.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cocone`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       {J : Type u_2} →         [inst
_2 : CategoryTheory.Category.{v_2, u_2} J] →           {F₁ F₂ : CategoryTheory.F
unctor J C} →             CategoryTheory.Limits.Cocone F₁ →               Catego
ryTheory.Limits.Cocone F₂ →                 CategoryTheory.Limits.Cocone (Catego
ryTheory.MonoidalCategoryStruct.tensorObj F₁ F₂)
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj F₁ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two cocones.
-/
def Cocone.tensor : Cocone (F₁ ⊗ F₂) where
  pt := c₁.pt ⊗ c₂.pt
  ι.app j := c₁.ι.app j ⊗ₘ c₂.ι.app j

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] tensorHom_def in
/-- The tensor product of colimit cocones for functors `F₁ : J ⥤ C`
and `F₂ : J ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds and `J` is sifted. -/
/-
**CategoryTheory.Limits.IsColimit.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsColimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       {J : Type u_2} →         [inst
_2 : CategoryTheory.Category.{v_2, u_2} J] →           {F₁ F₂ : CategoryTheory.F
unctor J C} →             {c₁ : CategoryTheory.Limits.Cocone F₁} →              
 {c₂ : CategoryTheory.Limits.Cocone F₂} →                 [CategoryTheory.Limits
.PreservesColimit₂ F₁ F₂ (CategoryTheory.MonoidalCategory.curriedTensor C)] →   
                [CategoryTheory.IsSifted J] →                     CategoryTheory
.Limits.IsColimit c₁ →                       CategoryTheory.Limits.IsColimit c₂ 
→ CategoryTheory.Limits.IsColimit (c₁.tensor c₂)
参数：CategoryTheory.MonoidalCategory.curriedTensor C；c₁.tensor c₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSifted.toFinal`：∀ {C : Type u} {inst : CategoryTheory.C
ategory.{v, u} C} [self : CategoryTheory.IsSifted C],   (CategoryTheory.Functor.
diag C).Final

--- 原说明 ---
The tensor product of colimit cocones for functors `F₁ : J ⥤ C`
and `F₂ : J ⥤ C` is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTenso
r C)`
holds and `J` is sifted.
-/
noncomputable def IsColimit.tensor [PreservesColimit₂ F₁ F₂ (curriedTensor C)] [IsSifted J]
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.tensor c₂) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    ((Functor.Final.isColimitWhiskerEquiv (Functor.diag J) _).2 (hc₁.tensor₂ hc₂))
  · exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp)
  · exact Cocone.ext (Iso.refl _)

end

end CategoryTheory.Limits

