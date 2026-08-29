/-
Copyright (c) 2025 Yaël Dillies, Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Moisés Herradón Cueto
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.WithTerminal.FinCategory
public import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# If a functor preserves limits, so does the induced functor in the `Over` or `Under` category

Suppose we are given categories `C` and `D`, and object `X : C`, and a functor `F : C ⥤ D`.
`F` induces a functor `Over.post F : Over X ⥤ Over (F.obj X)`. If `F` preserves limits of a
certain shape `WithTerminal J`, then `Over.post F` preserves limits of shape `J`.
As a corollary, if `F` preserves finite limits, or limits of a certain size, so does `Over.post F`.

Dually, if `F` preserves certain colimits, `Under.post F` will preserve certain colimits as well.
-/

public section

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {X : C} {F : C ⥤ D}

-- TODO: Do we even want to keep `WidePullbackShape` around?
/--
Instance `PreservesLimitsOfShape.ofWidePullbacks` / 实例 `PreservesLimitsOfShape.ofWidePullbacks`

English:
instance PreservesLimitsOfShape.ofWidePullbacks
  signature: {J : Type*}
  body: preservesLimitsOfShape_of_equiv WithTerminal.widePullbackShapeEquiv F

中文:
实例 PreservesLimitsOfShape.ofWidePullbacks
  签名: {J : 类型}
  定义体: preservesLimitsOfShape_of_equiv WithTerminal.widePullbackShapeEquiv F

Depends on / 依赖: WithTerminal, WithTerminal.widePullbackShapeEquiv, preservesLimitsOfShape_of_equiv, widePullbackShapeEquiv
-/
instance PreservesLimitsOfShape.ofWidePullbacks {J : Type*}
    [PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesLimitsOfShape (WithTerminal <| Discrete J) F :=
  preservesLimitsOfShape_of_equiv WithTerminal.widePullbackShapeEquiv F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open WithTerminal in
/--
Instance `PreservesLimitsOfShape.overPost` / 实例 `PreservesLimitsOfShape.overPost`

English:
instance PreservesLimitsOfShape.overPost
  signature: [PreservesLimitsOfShape (WithTerminal J) F]
  body: have isLimitConeD := (IsLimit.postcomposeHomEquiv liftFromOverComp.symm _).symm
      isLimitOfPreserves F (isLimitEquiv.symm isLimitConeK)
⟨isLimitEquiv isLimitConeD.ofIsoLimit Cone.ext (.refl _) fun | .star | .of a => by aesop⟩

中文:
实例 PreservesLimitsOfShape.overPost
  签名: [PreservesLimitsOfShape (WithTerminal J) F]
  定义体: have isLimitConeD := (IsLimit.postcomposeHomEquiv liftFromOverComp.symm _).symm
      isLimitOfPreserves F (isLimitEquiv.symm isLimitConeK)
⟨isLimitEquiv isLimitConeD.ofIsoLimit Cone.ext (.refl _) fun | .star | .of a => by aesop⟩
-/
instance PreservesLimitsOfShape.overPost [PreservesLimitsOfShape (WithTerminal J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
  preservesLimit.preserves {coneK} isLimitConeK :=
have isLimitConeD := (IsLimit.postcomposeHomEquiv liftFromOverComp.symm _).symm
      isLimitOfPreserves F (isLimitEquiv.symm isLimitConeK)
⟨isLimitEquiv isLimitConeD.ofIsoLimit Cone.ext (.refl _) fun | .star | .of a => by aesop⟩

/--
Instance `PreservesFiniteLimits.overPost` / 实例 `PreservesFiniteLimits.overPost`

English:
instance PreservesFiniteLimits.overPost
  signature: [PreservesFiniteLimits F]
  body: inferInstance

中文:
实例 PreservesFiniteLimits.overPost
  签名: [PreservesFiniteLimits F]
  定义体: inferInstance
-/
instance PreservesFiniteLimits.overPost [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Over.post F (X := X)) where
  preservesFiniteLimits _ := inferInstance

/--
Instance `PreservesLimitsOfSize.overPost` / 实例 `PreservesLimitsOfSize.overPost`

English:
instance PreservesLimitsOfSize.overPost
  signature: [PreservesLimitsOfSize.{w', w} F]

中文:
实例 PreservesLimitsOfSize.overPost
  签名: [PreservesLimitsOfSize.{w', w} F]
-/
instance PreservesLimitsOfSize.overPost [PreservesLimitsOfSize.{w', w} F] :
    PreservesLimitsOfSize.{w', w} (Over.post F (X := X)) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open WithInitial in
/--
Instance `PreservesColimitsOfShape.underPost` / 实例 `PreservesColimitsOfShape.underPost`

English:
instance PreservesColimitsOfShape.underPost
  signature: [PreservesColimitsOfShape (WithInitial J) F]
  body: have isColimitCoconeD := (IsColimit.precomposeHomEquiv liftFromUnderComp _).symm
      isColimitOfPreserves F (isColimitEquiv.symm isColimitCoconeK)
⟨isColimitEquiv isColimitCoconeD.ofIsoColimit
      Cocone.ext (.refl _) fun | .star | .of a => by aesop⟩

中文:
实例 PreservesColimitsOfShape.underPost
  签名: [PreservesColimitsOfShape (WithInitial J) F]
  定义体: have isColimitCoconeD := (IsColimit.precomposeHomEquiv liftFromUnderComp _).symm
      isColimitOfPreserves F (isColimitEquiv.symm isColimitCoconeK)
⟨isColimitEquiv isColimitCoconeD.ofIsoColimit
      Cocone.ext (.refl _) fun | .star | .of a => by aesop⟩
-/
instance PreservesColimitsOfShape.underPost [PreservesColimitsOfShape (WithInitial J) F] :
    PreservesColimitsOfShape J (Under.post F (X := X)) where
  preservesColimit.preserves {coconeK} isColimitCoconeK :=
have isColimitCoconeD := (IsColimit.precomposeHomEquiv liftFromUnderComp _).symm
      isColimitOfPreserves F (isColimitEquiv.symm isColimitCoconeK)
⟨isColimitEquiv isColimitCoconeD.ofIsoColimit
      Cocone.ext (.refl _) fun | .star | .of a => by aesop⟩

/--
Instance `PreservesFiniteColimits.underPost` / 实例 `PreservesFiniteColimits.underPost`

English:
instance PreservesFiniteColimits.underPost
  signature: [PreservesFiniteColimits F]
  body: inferInstance

中文:
实例 PreservesFiniteColimits.underPost
  签名: [PreservesFiniteColimits F]
  定义体: inferInstance
-/
instance PreservesFiniteColimits.underPost [PreservesFiniteColimits F] :
    PreservesFiniteColimits (Under.post F (X := X)) where
  preservesFiniteColimits _ := inferInstance

/--
Instance `PreservesColimitsOfSize.underPost` / 实例 `PreservesColimitsOfSize.underPost`

English:
instance PreservesColimitsOfSize.underPost
  signature: [PreservesColimitsOfSize.{w', w} F]

中文:
实例 PreservesColimitsOfSize.underPost
  签名: [PreservesColimitsOfSize.{w', w} F]
-/
instance PreservesColimitsOfSize.underPost [PreservesColimitsOfSize.{w', w} F] :
    PreservesColimitsOfSize.{w', w} (Under.post F (X := X)) where

end CategoryTheory.Limits
