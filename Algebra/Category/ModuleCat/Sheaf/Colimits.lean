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

/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape K (PresheafOfModules.{v} R.obj)] :
    HasColimitsOfShape K (SheafOfModules.{v} R) where
  has_colimit F := by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact hasColimit_of_iso e
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfSize.{w', w} (PresheafOfModules.{v} R.obj)] :
    HasColimitsOfSize.{w', w} (SheafOfModules.{v} R) where

end SheafOfModules

