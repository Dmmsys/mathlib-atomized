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

/--
Instance `wellPowered_addCommGrp` / 实例 `wellPowered_addCommGrp`

English:
instance wellPowered_addCommGrp
  signature: : WellPowered.{u} AddCommGrpCat.{u}
  body: wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).asEquivalence

中文:
实例 wellPowered_addCommGrp
  签名: : 良幂.{u} 加法交换群范畴.{u}
  定义体: wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).asEquivalence

Depends on / 依赖: AddCommGrpCat, ModuleCat, asEquivalence, wellPowered_of_equiv
-/
instance wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u} :=
  wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).asEquivalence

end AddCommGrpCat
