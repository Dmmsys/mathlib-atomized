/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# The category of abelian groups is well-powered
-/

public section


open CategoryTheory

universe u

namespace AddCommGrpCat

/-
**AddCommGrpCat.wellPowered_addCommGrp** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`
。
形式化陈述：wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_equiv`：wellPowered_of_equiv (e : C ≌ D) [L
ocallySmall.{w} C] [LocallySmall.{w} D] [WellPowered.{w} C] : WellPowered.{w} D
· 使用定理 `ModuleCat.forget₂AddCommGroupIsEquivalence`：(CategoryTheory.forget₂ (Mod
uleCat ℤ) AddCommGrpCat).IsEquivalence
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u} :=
  wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

end AddCommGrpCat

