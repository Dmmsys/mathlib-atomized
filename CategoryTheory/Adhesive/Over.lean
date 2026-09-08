/-
Copyright (c) 2026 Dénes Pápai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dénes Pápai
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Adhesive structure on slice categories

The slice category `Over B` inherits the property of being adhesive from the
base category.

## TODO
- The dual result for `Under B`.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- Slices of adhesive categories are adhesive. See [adhesive2004], Proposition 8 (ii). -/
/-
**CategoryTheory.adhesive_over** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：adhesive_over [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) : Adhe
sive (Over B)
参数：B : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.adhesive_of_preserves_and_reflects_isomorphism`：adhesive_
of_preserves_and_reflects_isomorphism (F : C ⥤ D) [Adhesive D] [HasPullbacks C] 
[HasPushouts C] [PreservesLimitsOfShape WalkingCosp…
· 使用定理 `CategoryTheory.Over.hasLimitsOfShape_of_isConnected`：∀ {J : Type u'} [in
st : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} C]   {B : C} [CategoryTheo…
· 使用定理 `CategoryTheory.Over.instHasColimitsOfShape`：∀ {J : Type w} [inst : Categ
oryTheory.Category.{w', w} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {X : C} [CategoryTheory…
· 使用定理 `CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected`：∀ {J :
 Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : Cat
egoryTheory.Category.{v, u} C]   [CategoryTheory.IsCon…
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Slices of adhesive categories are adhesive. See [adhesive2004], Proposition 8 (i
i).
-/
instance adhesive_over [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) :
    Adhesive (Over B) :=
  adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

end CategoryTheory

