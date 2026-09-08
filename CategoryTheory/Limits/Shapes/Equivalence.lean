/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transporting existence of specific limits across equivalences

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/

public section


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-
**CategoryTheory.hasInitial_of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：hasInitial_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasInitial C] : H
asInitial D
参数：e : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence`：hasColimits
OfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] : 
HasColimitsOfShape J C
-/
theorem hasInitial_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasInitial C] : HasInitial D :=
  Adjunction.hasColimitsOfShape_of_equivalence e
/-
**CategoryTheory.Equivalence.hasInitial_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (e : C ≌ D), CategoryTheory.Limi
ts.HasInitial C ↔ CategoryTheory.Limits.HasInitial D
参数：e : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasInitial_of_equivalence`：hasInitial_of_equivalence (e :
 D ⥤ C) [e.IsEquivalence] [HasInitial C] : HasInitial D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
theorem Equivalence.hasInitial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩
/-
**CategoryTheory.hasTerminal_of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：hasTerminal_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasTerminal C] :
 HasTerminal D
参数：e : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
-/
theorem hasTerminal_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasTerminal C] : HasTerminal D :=
  Adjunction.hasLimitsOfShape_of_equivalence e
/-
**CategoryTheory.Equivalence.hasTerminal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (e : C ≌ D), CategoryTheory.Limi
ts.HasTerminal C ↔ CategoryTheory.Limits.HasTerminal D
参数：e : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasTerminal_of_equivalence`：hasTerminal_of_equivalence (e
 : D ⥤ C) [e.IsEquivalence] [HasTerminal C] : HasTerminal D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
theorem Equivalence.hasTerminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩

end CategoryTheory

