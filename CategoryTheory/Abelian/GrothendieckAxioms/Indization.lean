/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Abelian.Indization
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Generator.Indization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# AB axioms in the category of ind-objects

We show that `Ind C` satisfies Grothendieck's axiom AB5 if `C` has finite limits and deduce that
`Ind C` is Grothendieck abelian if `C` is small and abelian.
-/

public section

universe v u

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [SmallCategory J] [IsFiltered J] [HasFiniteLimits C] :
    HasExactColimitsOfShape J (Ind C) :=
  HasExactColimitsOfShape.domain_of_functor J (Ind.inclusion C)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] : AB5 (Ind C) where
  ofShape _ _ _ := inferInstance

end

section

variable {C : Type u} [SmallCategory C] [Abelian C]

/-
**CategoryTheory.Limits.isGrothendieckAbelian_ind** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isGrothendieckAbelian_ind : IsGrothendieckAbelian.{u} (Ind C) where hasSep
arator
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.instHasFilteredColimitsInd`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C],   CategoryTheory.Limits.HasFilteredColimits (Catego
ryTheory.Ind C)
· 使用定理 `CategoryTheory.Limits.instAB5IndOfHasFiniteLimits`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimits C],  
 CategoryTheory.AB5 (CategoryTheory.Ind…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instHasCoproductsIndOfHasFiniteCoproducts`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteCopro
ducts C],   CategoryTheory.Limits.HasCoproduct…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Ind.isSeparator_range_yoneda`：∀ {C : Type u} [inst : Cate
goryTheory.SmallCategory C] [CategoryTheory.Preadditive C]   [inst_2 : CategoryT
heory.Limits.HasFiniteColimits C]…
-/
instance isGrothendieckAbelian_ind : IsGrothendieckAbelian.{u} (Ind C) where
  hasSeparator := ⟨⟨_, Ind.isSeparator_range_yoneda⟩⟩

end

end CategoryTheory.Limits

