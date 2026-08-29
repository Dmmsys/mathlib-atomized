/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Junyan Xu, Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Data.Set.Subsingleton

/-!
# `ULift` creates small (co)limits


This file shows that `uliftFunctor.{v, u}` preserves all limits and colimits, including those
potentially too big to exist in `Type u`.

As this functor is fully faithful, we also deduce that it creates `u`-small limits and
colimits.

-/

@[expose] public section

universe v w w' u

namespace CategoryTheory.Limits.Types

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sectionsEquiv` / `sectionsEquiv` 的定义

English:
definition sectionsEquiv
  signature: {J : Type*} [Category* J] (K : J ⥤ Type u)
  body: fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩

中文:
定义 sectionsEquiv
  签名: {J : 类型} [Category* J] (K : J ⥤ 类型u)
  定义体: fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩
-/
def sectionsEquiv {J : Type*} [Category* J] (K : J ⥤ Type u) :
    K.sections ≃ (K ⋙ uliftFunctor.{v, u}).sections where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u}
  body: {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        rw [Types.isLimit_iff ((uliftFunctor.{v]; rw [u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext 

中文:
实例 :
  签名: PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u}
  定义体: {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        rw [Types.isLimit_iff ((uliftFunctor.{v]; rw [u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext 
-/
noncomputable instance : PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesLimitsOfShape {J} := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        rw [Types.isLimit_iff ((uliftFunctor.{v]; rw [u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext _ _ (hx₁ i),
          fun y hy => ULift.ext _ _ (hx₂ y.down fun i => ULift.ext_iff.mp (hy i))⟩ } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u}
  body: { CreatesLimit := fun {_} => createsLimitOfFullyFaithfulOfPreserves }

中文:
实例 :
  签名: CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u}
  定义体: { CreatesLimit := fun {_} => createsLimitOfFullyFaithfulOfPreserves }

Depends on / 依赖: CreatesLimit, createsLimitOfFullyFaithfulOfPreserves
-/
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} => createsLimitOfFullyFaithfulOfPreserves }

variable {J : Type*} [Category* J] {K : J ⥤ Type u} {c : Cocone K} (hc : IsColimit c)
variable {lc : Cocone (K ⋙ uliftFunctor.{v, u})}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u}
  body: { preservesColimit := fun {F} =>
    { preserves := fun {c} hc => by
        rw [isColimit_iff_coconeTypesIsColimit]
        exact (((isColimit_iff_coconeTypesIsColimit _).1 ⟨hc⟩).precompose
          (G := F ⋙ uliftFunctor.{v}) (fun _ => Equiv.ulift)
          (fun _ => rfl)).of_equiv Equiv.ulift.s

中文:
实例 :
  签名: PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u}
  定义体: { preservesColimit := fun {F} =>
    { preserves := fun {c} hc => by
        rw [isColimit_iff_coconeTypesIsColimit]
        exact (((isColimit_iff_coconeTypesIsColimit _).1 ⟨hc⟩).precompose
          (G := F ⋙ uliftFunctor.{v}) (fun _ => Equiv.ulift)
          (fun _ => rfl)).of_equiv Equiv.ulift.s

Depends on / 依赖: Equiv.ulift, Equiv.ulift.symm, isColimit_iff_coconeTypesIsColimit, of_equiv, precompose, preserves, preservesColimit, uliftFunctor
-/
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} =>
    { preserves := fun {c} hc => by
        rw [isColimit_iff_coconeTypesIsColimit]
        exact (((isColimit_iff_coconeTypesIsColimit _).1 ⟨hc⟩).precompose
          (G := F ⋙ uliftFunctor.{v}) (fun _ => Equiv.ulift)
          (fun _ => rfl)).of_equiv Equiv.ulift.symm (fun _ _ => rfl) } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u}
  body: { CreatesColimit := fun {_} => createsColimitOfReflectsIsomorphismsOfPreserves }

中文:
实例 :
  签名: CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u}
  定义体: { CreatesColimit := fun {_} => createsColimitOfReflectsIsomorphismsOfPreserves }

Depends on / 依赖: CreatesColimit, createsColimitOfReflectsIsomorphismsOfPreserves
-/
noncomputable instance : CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape :=
    { CreatesColimit := fun {_} => createsColimitOfReflectsIsomorphismsOfPreserves }

end CategoryTheory.Limits.Types
