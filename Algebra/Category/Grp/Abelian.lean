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
/--
Definition of `normalMono` / `normalMono` 的定义

English:
definition normalMono
  signature: (_ : Mono f)
  body: equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalMono _ inferInstance

中文:
定义 normalMono
  签名: (_ : 单态射 f)
  定义体: equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalMono _ inferInstance

Depends on / 依赖: AddCommGrpCat, ModuleCat, ModuleCat.normalMono, equivalenceReflectsNormalMono, normalMono
-/
def normalMono (_ : Mono f) : NormalMono f :=
equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
@[instance_reducible]
/--
Definition of `normalEpi` / `normalEpi` 的定义

English:
definition normalEpi
  signature: (_ : Epi f)
  body: equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalEpi _ inferInstance

中文:
定义 normalEpi
  签名: (_ : 满态射 f)
  定义体: equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalEpi _ inferInstance

Depends on / 依赖: AddCommGrpCat, ModuleCat, ModuleCat.normalEpi, equivalenceReflectsNormalEpi, normalEpi
-/
def normalEpi (_ : Epi f) : NormalEpi f :=
equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} Int) AddCommGrpCat.{u}).inv
    ModuleCat.normalEpi _ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian AddCommGrpCat.{u}
  body: ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

中文:
实例 :
  签名: 交换 加法交换群范畴.{u}
  定义体: ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

Depends on / 依赖: normalMono
-/
instance : Abelian AddCommGrpCat.{u} where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

end AddCommGrpCat
