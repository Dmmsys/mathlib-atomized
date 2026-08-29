/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.EssSurj
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

/-!
# Fiber functors induce an equivalence of categories

Let `C` be a Galois category with fiber functor `F`.

In this file we conclude that the induced functor from `C` to the category of finite,
discrete `Aut F`-sets is an equivalence of categories.
-/

@[expose] public section

universe u₂ u₁ w

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{w}}

namespace PreGaloisCategory

variable [GaloisCategory C] [FiberFunctor F]

open scoped FintypeCatDiscrete

variable (F) in
/-- The induced functor from `C` to the category of finite, discrete `Aut F`-sets. -/
@[simps! obj_obj map]
/--
Definition of `functorToContAction` / `functorToContAction` 的定义

English:
definition functorToContAction
  signature: : C ⥤ ContAction FintypeCat (Aut F)
  body: ObjectProperty.lift _ (functorToAction F) (fun X => continuousSMul_aut_fiber F X)

中文:
定义 functorToContAction
  签名: : C ⥤ ContAction FintypeCat (Aut F)
  定义体: ObjectProperty.lift _ (functorToAction F) (fun X => continuousSMul_aut_fiber F X)

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, continuousSMul_aut_fiber, functorToAction
-/
def functorToContAction : C ⥤ ContAction FintypeCat (Aut F) :=
  ObjectProperty.lift _ (functorToAction F) (fun X => continuousSMul_aut_fiber F X)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorToContAction F).Faithful
  body: inferInstanceAs (ObjectProperty.lift _ _ _).Faithful

中文:
实例 :
  签名: (functorToContAction F).Faithful
  定义体: inferInstanceAs (ObjectProperty.lift _ _ _).Faithful

Depends on / 依赖: Faithful, ObjectProperty, ObjectProperty.lift, cat_disch
-/
instance : (functorToContAction F).Faithful :=
inferInstanceAs (ObjectProperty.lift _ _ _).Faithful

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorToContAction F).Full
  body: inferInstanceAs (ObjectProperty.lift _ _ _).Full

中文:
实例 :
  签名: (functorToContAction F).Full
  定义体: inferInstanceAs (ObjectProperty.lift _ _ _).Full

Depends on / 依赖: ObjectProperty, ObjectProperty.lift
-/
instance : (functorToContAction F).Full :=
inferInstanceAs (ObjectProperty.lift _ _ _).Full

instance {F : C ⥤ FintypeCat.{u₁}} [FiberFunctor F] : (functorToContAction F).EssSurj where
  mem_essImage X := by
    have : ContinuousSMul (Aut F) X.obj.V := X.2
    obtain ⟨A, ⟨i⟩⟩ := exists_lift_of_continuous (F := F) X
    exact ⟨A, ⟨ObjectProperty.isoMk _ i⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorToContAction F).EssSurj
  body: by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  let : FiberFunctor F' := FiberFunctor.comp_right _
  have : (functorToContAction F').EssSurj := inferInstance
  let f : Aut F ≃ₜ* Aut F' :=
    (autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFuncto

中文:
实例 :
  签名: (functorToContAction F).EssSurj
  定义体: by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  let : FiberFunctor F' := FiberFunctor.comp_right _
  have : (functorToContAction F').EssSurj := inferInstance
  let f : Aut F ≃ₜ* Aut F' :=
    (autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFuncto

Depends on / 依赖: Action, Action.isContinuous_def, ContAction, Continuous, EssSurj, FiberFunctor, FiberFunctor.comp_right, FintypeCat, FintypeCat.uSwitch, FintypeCat.uSwitchEquivalence, autEquivAutWhiskerRight, comp_right, fullyFaithfulFunctor, functorToContAction, isContinuous_def, mapContAction, uSwitch, uSwitchEquivalence
-/
instance : (functorToContAction F).EssSurj := by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  let : FiberFunctor F' := FiberFunctor.comp_right _
  have : (functorToContAction F').EssSurj := inferInstance
  let f : Aut F ≃ₜ* Aut F' :=
    (autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFunctor)
  let equiv : ContAction FintypeCat.{u₁} (Aut F') ≌ ContAction FintypeCat.{w} (Aut F) :=
    (FintypeCat.uSwitchEquivalence.{u₁, w}.mapContAction (Aut F')
       (fun X => by
          rw [Action.isContinuous_def]
          change Continuous ((fun p => (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ => (X.obj.ρ p.1).hom p.2) ∘
              (fun p : Aut F' × _ => (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          exact Continuous.comp (by fun_prop) (Continuous.comp X.2.1 (by fun_prop)))
       (fun X => by
          rw [Action.isContinuous_def]
          change Continuous ((fun p => (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ => (X.obj.ρ p.1).hom p.2) ∘
              (fun p : Aut F' × _ => (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          exact Continuous.comp (by fun_prop) (Continuous.comp X.2.1 (by fun_prop)))).trans <|
      ContAction.resEquiv _ f
  have : functorToContAction F ≅ functorToContAction F' ⋙ equiv.functor :=
    NatIso.ofComponents
      (fun X => ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.uSwitchEquivalence.unitIso.app _)
      (fun g => FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (g.hom.app X))))
      (fun f => by
        ext : 2
        exact FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (F.map f))
  exact Functor.essSurj_of_iso this.symm

/-- Any fiber functor `F` induces an equivalence of categories with the category of finite and
discrete `Aut F`-sets. -/
@[stacks 0BN4]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorToContAction F).IsEquivalence

中文:
实例 :
  签名: (functorToContAction F).IsEquivalence
-/
instance : (functorToContAction F).IsEquivalence where

end PreGaloisCategory

end CategoryTheory
