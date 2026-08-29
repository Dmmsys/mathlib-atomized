/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Colimits in categories of sheaves of modules

In this file, we show that colimits of shape `J` exist in a category
of sheaves of modules if it exists in the corresponding category
of presheaves of modules.

-/

public section

universe w' w v v' u' u

namespace SheafOfModules

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

variable (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] (K : Type w) [Category.{w'} K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: K (PresheafOfModules.{v} R.obj)] :
  body: by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact hasColimit_of_iso e

中文:
实例 [有形状余极限
  签名: K (预模层.{v} R.obj)] :
  定义体: by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact hasColimit_of_iso e

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, PresheafOfModules, PresheafOfModules.sheafification, PresheafOfModules.sheafificationAdjunction, R.obj, counit, forget, hasColimit_of_iso, isoWhiskerLeft, sheafification, sheafificationAdjunction
-/
instance [HasColimitsOfShape K (PresheafOfModules.{v} R.obj)] :
    HasColimitsOfShape K (SheafOfModules.{v} R) where
  has_colimit F := by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact hasColimit_of_iso e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfSize.{w',
  signature: w} (PresheafOfModules.{v} R.obj)] :

中文:
实例 [有余limitsOfSize.{w',
  签名: w} (预模层.{v} R.obj)] :
-/
instance [HasColimitsOfSize.{w', w} (PresheafOfModules.{v} R.obj)] :
    HasColimitsOfSize.{w', w} (SheafOfModules.{v} R) where

end SheafOfModules
