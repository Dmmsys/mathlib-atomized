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
/--
Definition of `sheafOfModulesEquivOver` / `sheafOfModulesEquivOver` 的定义

English:
definition sheafOfModulesEquivOver
  signature: :
  body: by
  refine SheafOfModules.pushforwardPushforwardEquivalence (eqv := U.overEquivalence.symm)
    (U.overPullbackSheafEquivOver.app _).inv (U.sheafRestrictSheafEquivOver.app _).inv rfl ?_
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOp

中文:
定义 sheafOfModulesEquivOver
  签名: :
  定义体: by
  refine SheafOfModules.pushforwardPushforwardEquivalence (eqv := U.overEquivalence.symm)
    (U.overPullbackSheafEquivOver.app _).inv (U.sheafRestrictSheafEquivOver.app _).inv rfl ?_
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOp

Depends on / 依赖: IsOpenMap, IsOpenMap.functor, SheafOfModules, SheafOfModules.pushforwardPushforwardEquivalence, U.overEquivalence.symm, U.overPullbackSheafEquivOver.app, U.sheafRestrictSheafEquivOver.app, eqToHom_map, functor, overEquivalence, overPullbackSheafEquivOver, pushforwardPushforwardEquivalence, sheafRestrictSheafEquivOver
-/
def sheafOfModulesEquivOver :
    SheafOfModules.{w} (R.over U) ≌ SheafOfModules.{w} (U.sheafRestrict.obj R) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence (eqv := U.overEquivalence.symm)
    (U.overPullbackSheafEquivOver.app _).inv (U.sheafRestrictSheafEquivOver.app _).inv rfl ?_
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOpenMap.functor]

/--
Definition of `sheafOfModulesEquivOverUnit` / `sheafOfModulesEquivOverUnit` 的定义

English:
definition sheafOfModulesEquivOverUnit
  signature: (R : X.Sheaf RingCat.{u})
  body: .refl _

中文:
定义 sheafOfModulesEquivOverUnit
  签名: (R : X.层 环范畴.{u})
  定义体: .refl _
-/
def sheafOfModulesEquivOverUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ := .refl _

/--
Definition of `sheafOfModulesEquivOverInverseUnit` / `sheafOfModulesEquivOverInverseUnit` 的定义

English:
definition sheafOfModulesEquivOverInverseUnit
  signature: (R : X.Sheaf RingCat.{u})
  body: (U.sheafOfModulesEquivOver R).inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
    ((U.sheafOfModulesEquivOver R).unitIso.app _).symm

中文:
定义 sheafOfModulesEquivOverInverseUnit
  签名: (R : X.层 环范畴.{u})
  定义体: (U.sheafOfModulesEquivOver R).inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
    ((U.sheafOfModulesEquivOver R).unitIso.app _).symm

Depends on / 依赖: U.sheafOfModulesEquivOver, U.sheafOfModulesEquivOverUnit, inverse, inverse.mapIso, mapIso, sheafOfModulesEquivOver, sheafOfModulesEquivOverUnit, unitIso, unitIso.app
-/
def sheafOfModulesEquivOverInverseUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).inverse.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ :=
  (U.sheafOfModulesEquivOver R).inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
    ((U.sheafOfModulesEquivOver R).unitIso.app _).symm

end TopologicalSpace.Opens
