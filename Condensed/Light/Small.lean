/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Module

/-!

# Equivalence of light condensed objects with sheaves on a small site
-/

@[expose] public section

universe u v w

open CategoryTheory Sheaf Functor

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

variable (C) in
/--
Definition of `equivSmall` / `equivSmall` 的定义

English:
abbreviation equivSmall
  signature: :
  body: (equivSmallModel LightProfinite).sheafCongr _ _ _

中文:
缩写 equivSmall
  签名: :
  定义体: (equivSmallModel LightProfinite).sheafCongr _ _ _

Depends on / 依赖: LightProfinite, equivSmallModel, sheafCongr
-/
noncomputable abbrev equivSmall :
    LightCondensed.{u} C ≌
      Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
        (coherentTopology LightProfinite.{u})) C :=
  (equivSmallModel LightProfinite).sheafCongr _ _ _

instance (X Y : LightCondensed.{u} C) : Small.{max u v} (X ⟶ Y) where
  equiv_small :=
    ⟨(equivSmall C).functor.obj X ⟶ (equivSmall C).functor.obj Y,
      ⟨(equivSmall C).fullyFaithfulFunctor.homEquiv⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `equivSmallSheafificationIso` / `equivSmallSheafificationIso` 的定义

English:
definition equivSmallSheafificationIso
  body: (conjugateIsoEquiv (sheafificationAdjunction _ _)
    (((equivSmallModel LightProfinite.{u}).op.congrLeft.symm.toAdjunction.comp
    (sheafificationAdjunction _ _)).comp (equivSmall C).toAdjunction)).symm <|
  NatIso.ofComponents (fun X => ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm)

中文:
定义 equivSmallSheafificationIso
  定义体: (conjugateIsoEquiv (sheafificationAdjunction _ _)
    (((equivSmallModel LightProfinite.{u}).op.congrLeft.symm.toAdjunction.comp
    (sheafificationAdjunction _ _)).comp (equivSmall C).toAdjunction)).symm <|
  NatIso.ofComponents (fun X => ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm)

Depends on / 依赖: LightProfinite, NatIso, NatIso.ofComponents, congrLeft, conjugateIsoEquiv, equivSmall, equivSmallModel, invFunIdAssoc, ofComponents, op.congrLeft.symm.toAdjunction.comp, op.invFunIdAssoc, sheafificationAdjunction, toAdjunction
-/
noncomputable def equivSmallSheafificationIso
    [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]
    [HasWeakSheafify ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) C] :
    (equivSmallModel LightProfinite.{u}).op.congrLeft.inverse ⋙ presheafToSheaf _ _ ⋙
      (equivSmall C).functor ≅
    presheafToSheaf _ _ :=
  (conjugateIsoEquiv (sheafificationAdjunction _ _)
    (((equivSmallModel LightProfinite.{u}).op.congrLeft.symm.toAdjunction.comp
    (sheafificationAdjunction _ _)).comp (equivSmall C).toAdjunction)).symm <|
  NatIso.ofComponents (fun X => ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm)

variable (R : Type u) [CommRing R]

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] LightCondensed.forget in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equivSmallFreeIso` / `equivSmallFreeIso` 的定义

English:
definition equivSmallFreeIso
  signature: :
  body: conjugateIsoEquiv (Sheaf.adjunction _ (ModuleCat.adj R))
    (((equivSmall _).symm.toAdjunction.comp
      (freeForgetAdjunction R)).comp (equivSmall _).toAdjunction) |>.symm <| by
  refine NatIso.ofComponents
    (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (isoWhiskerRight ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm _ ≪≫
        (Functor.associator _ _ _)))

中文:
定义 equivSmallFreeIso
  签名: :
  定义体: conjugateIsoEquiv (Sheaf.adjunction _ (ModuleCat.adj R))
    (((equivSmall _).symm.toAdjunction.comp
      (freeForgetAdjunction R)).comp (equivSmall _).toAdjunction) |>.symm <| by
  refine NatIso.ofComponents
    (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (isoWhiskerRight ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm _ ≪≫
        (Functor.associator _ _ _)))

Depends on / 依赖: Functor, Functor.associator, LightProfinite, ModuleCat, ModuleCat.adj, NatIso, NatIso.ofComponents, Sheaf.adjunction, adjunction, associator, conjugateIsoEquiv, equivSmall, equivSmallModel, freeForgetAdjunction, fullyFaithfulSheafToPresheaf, invFunIdAssoc, isoWhiskerRight, ofComponents, op.invFunIdAssoc, preimageIso
-/
noncomputable def equivSmallFreeIso :
    (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (ModuleCat R)).functor ≅
    Sheaf.composeAndSheafify _ (ModuleCat.free R) :=
  conjugateIsoEquiv (Sheaf.adjunction _ (ModuleCat.adj R))
    (((equivSmall _).symm.toAdjunction.comp
      (freeForgetAdjunction R)).comp (equivSmall _).toAdjunction) |>.symm <| by
  refine NatIso.ofComponents
    (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (isoWhiskerRight ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm _ ≪≫
        (Functor.associator _ _ _)))

end LightCondensed
