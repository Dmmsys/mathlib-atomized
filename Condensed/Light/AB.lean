/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Condensed.Light.Epi

/-!
# Grothendieck's AB axioms for light condensed modules

The category of light condensed `R`-modules over a ring satisfies the countable version of
Grothendieck's AB4\* axiom
-/

public section

universe u

open CategoryTheory Limits

namespace LightCondensed

variable {R : Type u} [Ring R]

attribute [local instance] Abelian.hasFiniteBiproducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CountableAB4Star (LightCondMod.{u} R)
  body: have := hasExactLimitsOfShape_of_preservesEpi (LightCondMod R) (Discrete Nat)
  CountableAB4Star.of_hasExactLimitsOfShape_nat _

中文:
实例 :
  签名: CountableAB4Star (LightCondMod.{u} R)
  定义体: have := hasExactLimitsOfShape_of_preservesEpi (LightCondMod R) (Discrete Nat)
  CountableAB4Star.of_hasExactLimitsOfShape_nat _

Depends on / 依赖: CountableAB4Star, CountableAB4Star.of_hasExactLimitsOfShape_nat, Discrete, LightCondMod, hasExactLimitsOfShape_of_preservesEpi, of_hasExactLimitsOfShape_nat
-/
noncomputable instance : CountableAB4Star (LightCondMod.{u} R) :=
  have := hasExactLimitsOfShape_of_preservesEpi (LightCondMod R) (Discrete Nat)
  CountableAB4Star.of_hasExactLimitsOfShape_nat _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGrothendieckAbelian.{u} (LightCondMod.{u} R)
  body: Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

中文:
实例 :
  签名: IsGrothendieckAbelian.{u} (LightCondMod.{u} R)
  定义体: Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

Depends on / 依赖: Sheaf.isGrothendieckAbelian_of_essentiallySmall, isGrothendieckAbelian_of_essentiallySmall
-/
instance : IsGrothendieckAbelian.{u} (LightCondMod.{u} R) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

end LightCondensed
