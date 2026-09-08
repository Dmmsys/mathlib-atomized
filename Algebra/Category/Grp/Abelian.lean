/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The category of abelian groups is abelian
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AddCommGrpCat

variable {X Y Z : AddCommGrpCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- In the category of abelian groups, every monomorphism is normal. -/
@[instance_reducible]
/-
**AddCommGrpCat.normalMono** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：normalMono (_ : Mono f) : NormalMono f
参数：_ : Mono f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.forget₂AddCommGroupIsEquivalence`：(CategoryTheory.forget₂ (Mod
uleCat ℤ) AddCommGrpCat).IsEquivalence

--- 原说明 ---
In the category of abelian groups, every monomorphism is normal.
-/
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
@[instance_reducible]
/-
**AddCommGrpCat.normalEpi** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：normalEpi (_ : Epi f) : NormalEpi f
参数：_ : Epi f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.forget₂AddCommGroupIsEquivalence`：(CategoryTheory.forget₂ (Mod
uleCat ℤ) AddCommGrpCat).IsEquivalence

--- 原说明 ---
In the category of abelian groups, every epimorphism is normal.
-/
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance

/-- The category of abelian groups is abelian. -/
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of abelian groups is abelian.
-/
instance : Abelian AddCommGrpCat.{u} where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

end AddCommGrpCat

