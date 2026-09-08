/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transport a symmetric monoidal structure along an equivalence of categories
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Monoidal.Transported.instBraidedCategory** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Monoidal.Transported`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (e : C ≌
 D) →           [inst_2 : CategoryTheory.MonoidalCategory C] →             [Cate
goryTheory.BraidedCategory C] → CategoryTheory.BraidedCategory (CategoryTheory.M
onoidal.Transported e)
参数：e : C ≌ D；CategoryTheory.Monoidal.Transported e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Transported.instBraidedCategory (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  .ofFaithful e.inverse (fun _ _ ↦ e.functor.mapIso (β_ _ _)) fun _ _ ↦ by
    simp +instances [fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

local notation "e'" e => equivalenceTransported e

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).inverse.Braided where
  braided X Y := by
    simp +instances [Transported.instBraidedCategory, BraidedCategory.ofFaithful,
      fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

noncomputable section

/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
@[instance_reducible]
/-
**CategoryTheory.Monoidal.transportedFunctorCompInverseLaxBraided** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Monoidal`。
形式化陈述：transportedFunctorCompInverseLaxBraided (e : C ≌ D) [MonoidalCategory C] [
BraidedCategory C] : ((e' e).functor ⋙ (e' e).inverse).LaxBraided
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monoidal.instIsMonoidalUnitTransportedEquivalenceTranspor
ted`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryT…

--- 原说明 ---
This is a def because once we have that both `(e' e).inverse` and `(e' e).functo
r` are
braided, this causes a diamond.
-/
def transportedFunctorCompInverseLaxBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).LaxBraided :=
  Functor.LaxBraided.ofNatIso (e' e).unitIso

attribute [local instance] transportedFunctorCompInverseLaxBraided in
/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
@[instance_reducible]
/-
**CategoryTheory.Monoidal.transportedFunctorCompInverseBraided** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (e : C ≌
 D) →           [inst_2 : CategoryTheory.MonoidalCategory C] →             [inst
_3 : CategoryTheory.BraidedCategory C] →               ((CategoryTheory.Monoidal
.equivalenceTransported e).functor.comp                   (CategoryTheory.Monoid
al.equivalenceTransported e).inverse).Braided
参数：e : C ≌ D；(CategoryTheory.Monoidal.equivalenceTransported e).functor.comp    
               (CategoryTheory.Monoidal.equivalenceTransported e).inverse。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a def because once we have that both `(e' e).inverse` and `(e' e).functo
r` are
braided, this causes a diamond.
-/
def transportedFunctorCompInverseBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).Braided where

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] transportedFunctorCompInverseBraided in
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).functor.Braided where
  braided X Y := by
    apply (e' e).inverse.map_injective
    have : (β_ (((e' e).functor ⋙ (e' e).inverse).obj X)
        (((e' e).functor ⋙ (e' e).inverse).obj Y)).hom =
          Functor.LaxMonoidal.μ (((e' e).functor ⋙ (e' e).inverse)) X Y ≫
            ((e' e).functor ⋙ (e' e).inverse).map (β_ X Y).hom ≫
              Functor.OplaxMonoidal.δ ((e' e).functor ⋙ (e' e).inverse) Y X := by
      simp only [((e' e).functor ⋙ (e' e).inverse).map_braiding X Y,
        assoc, Functor.Monoidal.μ_δ, comp_id, Functor.Monoidal.μ_δ_assoc]
    simp_all

end

/-
**CategoryTheory.Monoidal.Transported.instSymmetricCategory** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Monoidal.Transported`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (e : C ≌
 D) →           [inst_2 : CategoryTheory.MonoidalCategory C] →             [Cate
goryTheory.SymmetricCategory C] →               CategoryTheory.SymmetricCategory
 (CategoryTheory.Monoidal.Transported e)
参数：e : C ≌ D；CategoryTheory.Monoidal.Transported e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Transported.instSymmetricCategory (e : C ≌ D) [MonoidalCategory C]
    [SymmetricCategory C] : SymmetricCategory (Transported e) :=
  .ofFaithful (equivalenceTransported e).inverse

end CategoryTheory.Monoidal

