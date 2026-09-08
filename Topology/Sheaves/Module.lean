/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Specialized results for sheaves of modules over topological spaces -/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{v})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheaves of modules over `R.over U` are equivalent to sheaves of modules over `R |_ U`. -/
/-
**TopologicalSpace.Opens.sheafOfModulesEquivOver** 是 Mathlib 中的一个定义，位于命名空间 `Topo
logicalSpace.Opens`。
形式化陈述：sheafOfModulesEquivOver : SheafOfModules.{w} (R.over U) ≌ SheafOfModules.{
w} (U.sheafRestrict.obj R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sheaves of modules over `R.over U` are equivalent to sheaves of modules over `R 
|_ U`.
-/
def sheafOfModulesEquivOver :
    SheafOfModules.{w} (R.over U) ≌ SheafOfModules.{w} (U.sheafRestrict.obj R) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence (eqv := U.overEquivalence.symm)
    (U.overPullbackSheafEquivOver.app _).inv (U.sheafRestrictSheafEquivOver.app _).inv rfl ?_
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOpenMap.functor]

/-- `sheafOfModulesEquivOver` takes `R.over U` to `R |_ U`. -/
/-
**TopologicalSpace.Opens.sheafOfModulesEquivOverUnit** 是 Mathlib 中的一个定义，位于命名空间 `
TopologicalSpace.Opens`。
形式化陈述：sheafOfModulesEquivOverUnit (R : X.Sheaf RingCat.{u}) : (U.sheafOfModulesE
quivOver R).functor.obj (SheafOfModules.unit.{u} _) ≅ SheafOfModules.unit.{u} _
参数：R : X.Sheaf RingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sheafOfModulesEquivOver` takes `R.over U` to `R |_ U`.
-/
def sheafOfModulesEquivOverUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ := .refl _

/-- `sheafOfModulesEquivOver.inverse` takes `R |_ U` to `R.over U`. -/
/-
**TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit** 是 Mathlib 中的一个定义，位
于命名空间 `TopologicalSpace.Opens`。
形式化陈述：sheafOfModulesEquivOverInverseUnit (R : X.Sheaf RingCat.{u}) : (U.sheafOfM
odulesEquivOver R).inverse.obj (SheafOfModules.unit.{u} _) ≅ SheafOfModules.unit
.{u} _
参数：R : X.Sheaf RingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sheafOfModulesEquivOver.inverse` takes `R |_ U` to `R.over U`.
-/
def sheafOfModulesEquivOverInverseUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).inverse.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ :=
  (U.sheafOfModulesEquivOver R).inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
    ((U.sheafOfModulesEquivOver R).unitIso.app _).symm

end TopologicalSpace.Opens

