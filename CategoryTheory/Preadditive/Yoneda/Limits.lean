/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The Yoneda embedding for preadditive categories preserves limits

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`ModuleCat` in the main file about the preadditive Yoneda embedding.

-/

public section


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-
**CategoryTheory.preservesLimits_preadditiveYonedaObj** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory`。
形式化陈述：preservesLimits_preadditiveYonedaObj (X : C) : PreservesLimits (preadditiv
eYonedaObj X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.yoneda_preservesLimits`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (X : C),   CategoryTheory.Limits.PreservesLimitsOfSize.{
t, w, v, v, u, v + 1} (Cate…
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves`：preserve
sLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)] [Reflec
tsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w…
-/
instance preservesLimits_preadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preservesLimits_of_reflects_of_preserves _ (forget _)
/-
**CategoryTheory.preservesLimits_preadditiveCoyonedaObj** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory`。
形式化陈述：preservesLimits_preadditiveCoyonedaObj (X : C) : PreservesLimits (preaddit
iveCoyonedaObj X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.coyoneda_preservesLimits`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesLimitsOfSi
ze.{t, w, v, v, u, v + 1} (Ca…
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves`：preserve
sLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)] [Reflec
tsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w…
-/
instance preservesLimits_preadditiveCoyonedaObj (X : C) :
    PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj (op X)))
  preservesLimits_of_reflects_of_preserves _ (forget _)
/-
**CategoryTheory.preservesLimits_preadditiveYoneda_obj** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory`。
形式化陈述：preservesLimits_preadditiveYoneda_obj (X : C) : PreservesLimits (preadditi
veYoneda.obj X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
-/
instance preservesLimits_preadditiveYoneda_obj (X : C) :
    PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance
/-
**CategoryTheory.preservesLimits_preadditiveCoyoneda_obj** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory`。
形式化陈述：preservesLimits_preadditiveCoyoneda_obj (X : Cᵒᵖ) : PreservesLimits (pread
ditiveCoyoneda.obj X)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
-/
instance preservesLimits_preadditiveCoyoneda_obj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _) from inferInstance

end CategoryTheory

