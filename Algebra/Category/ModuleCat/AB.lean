/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
/-!

# AB axioms in module categories

This file proves that the category of modules over a ring satisfies Grothendieck's axioms AB5, AB4,
and AB4\*. Further, it proves that `R` is a separator in the category of modules over `R`, and
concludes that this category is Grothendieck abelian.
-/

public section

universe u v

open CategoryTheory Limits

variable (R : Type u) [Ring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB5 (ModuleCat.{u} R)
  body: HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrpCat)

中文:
实例 :
  签名: AB5 (模范畴.{u} R)
  定义体: HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrpCat)
-/
instance : AB5 (ModuleCat.{u} R) where
  ofShape J _ _ :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrpCat)

attribute [local instance] Abelian.hasFiniteBiproducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB4 (ModuleCat.{u} R)
  body: AB4.of_AB5 _

中文:
实例 :
  签名: AB4 (模范畴.{u} R)
  定义体: AB4.of_AB5 _

Depends on / 依赖: AB4.of_AB5, of_AB5
-/
instance : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB4Star (ModuleCat.{u} R)
  body: HasExactLimitsOfShape.domain_of_functor (Discrete J) (forget₂ (ModuleCat R) AddCommGrpCat.{u})

中文:
实例 :
  签名: AB4Star (模范畴.{u} R)
  定义体: HasExactLimitsOfShape.domain_of_functor (Discrete J) (forget₂ (ModuleCat R) AddCommGrpCat.{u})

Depends on / 依赖: AddCommGrpCat, Discrete, HasExactLimitsOfShape, HasExactLimitsOfShape.domain_of_functor, ModuleCat, domain_of_functor
-/
instance : AB4Star (ModuleCat.{u} R) where
  ofShape J :=
    HasExactLimitsOfShape.domain_of_functor (Discrete J) (forget₂ (ModuleCat R) AddCommGrpCat.{u})

/--
lemma `ModuleCat.isSeparator` / 引理 `ModuleCat.isSeparator`

English:
lemma ModuleCat.isSeparator
  given: [Small.{v} R]
  statement: IsSeparator (ModuleCat.of.{v} R (Shrink.{v} R))
  proof: fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
    (Shrink.linearEquiv R R : Shrink R ->ₗ[R] R))) 1

中文:
引理 模范畴.isSeparator
  条件: [Small.{v} R]
  结论: IsSeparator (模范畴.of.{v} R (Shrink.{v} R))
  证明: fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
    (Shrink.linearEquiv R R : Shrink R ->ₗ[R] R))) 1

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.ext_iff, LinearMap.toSpanSingleton, ModuleCat, ModuleCat.hom_ext_iff, ModuleCat.ofHom, ObjectProperty, ObjectProperty.singleton_iff, Shrink, Shrink.linearEquiv, coe_comp, comp_apply, ext_iff, forall_eq, hom_comp, hom_ext_iff, linearEquiv
-/
lemma ModuleCat.isSeparator [Small.{v} R] : IsSeparator (ModuleCat.of.{v} R (Shrink.{v} R)) :=
    fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
    (Shrink.linearEquiv R R : Shrink R ->ₗ[R] R))) 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] : HasSeparator (ModuleCat.{v} R) where
  body: ⟨ModuleCat.of R (Shrink.{v} R), ModuleCat.isSeparator R⟩

中文:
实例 [Small.{v}
  签名: R] : 有Separator (模范畴.{v} R) where
  定义体: ⟨ModuleCat.of R (Shrink.{v} R), ModuleCat.isSeparator R⟩

Depends on / 依赖: ModuleCat, ModuleCat.isSeparator, ModuleCat.of, Shrink, isSeparator
-/
instance [Small.{v} R] : HasSeparator (ModuleCat.{v} R) where
  hasSeparator := ⟨ModuleCat.of R (Shrink.{v} R), ModuleCat.isSeparator R⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGrothendieckAbelian.{u} (ModuleCat.{u} R)

中文:
实例 :
  签名: 是GrothendieckAbelian.{u} (模范畴.{u} R)
-/
instance : IsGrothendieckAbelian.{u} (ModuleCat.{u} R) where
