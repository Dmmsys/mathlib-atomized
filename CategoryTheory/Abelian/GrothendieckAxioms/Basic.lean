/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Isaac Hernando, Coleton Kotch, Adam Topaz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Logic.Equiv.List
/-!

# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

- `HasExactColimitsOfShape J C` -- colimits of shape `J` in `C` are exact.
- The dual of the above definitions, called `HasExactLimitsOfShape`.
- `AB4` -- coproducts are exact (this is formulated in terms of `HasExactColimitsOfShape`).
- `AB5` -- filtered colimits are exact (this is formulated in terms of `HasExactColimitsOfShape`).

## Theorems

- The implication from `AB5` to `AB4` is established in `AB4.ofAB5`.
- That `HasExactColimitsOfShape J C` is invariant under equivalences in both parameters is shown
  in `HasExactColimitsOfShape.of_domain_equivalence` and
  `HasExactColimitsOfShape.of_codomain_equivalence`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`Mathlib/CategoryTheory/Abelian/Exact.lean`.

We do not require `Abelian` in the definition of `AB4` and `AB5` because these classes represent
individual axioms. An `AB4` category is an _abelian_ category satisfying `AB4`, and similarly for
`AB5`.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

public section

namespace CategoryTheory

open Limits CategoryTheory.Functor

attribute [instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w w' w₂ w₂' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C]

/--
Definition of `HasExactColimitsOfShape` / `HasExactColimitsOfShape` 的定义

English:
class HasExactColimitsOfShape
  parameters: (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

中文:
类 有ExactColimitsOfShape
  参数: (J : 类型u') [范畴.{v'} J] (C : 类型u) [范畴.{v} C]
  公理与运算 (1 个):
    - preservesFiniteLimits : 保持FiniteLimits (colim (J := J) (C := C))
-/
class HasExactColimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C] where
  /-- Exactness of `J`-shaped colimits stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

/--
Definition of `HasExactLimitsOfShape` / `HasExactLimitsOfShape` 的定义

English:
class HasExactLimitsOfShape
  parameters: (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

中文:
类 有ExactLimitsOfShape
  参数: (J : 类型u') [范畴.{v'} J] (C : 类型u) [范畴.{v} C]
  公理与运算 (1 个):
    - preservesFiniteColimits : 保持FiniteColimits (lim (J := J) (C := C))
-/
class HasExactLimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasLimitsOfShape J C] where
  /-- Exactness of `J`-shaped limits stated as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] HasExactColimitsOfShape.preservesFiniteLimits
  HasExactLimitsOfShape.preservesFiniteColimits

variable {C} in
/--
lemma `HasExactColimitsOfShape.domain_of_functor` / 引理 `HasExactColimitsOfShape.domain_of_functor`

English:
lemma HasExactColimitsOfShape.domain_of_functor
  statement: {D : Type*} (J : Type*) [Category* J] [Category* D]
  proof: { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cone.ext ((preservesColimitNatIso F).symm.app _)
        fun i => (preservesColimitNatIso F).inv.naturality _ } } }

中文:
引理 有ExactColimitsOfShape.domain_of_functor
  结论: {D : 类型} (J : 类型) [范畴* J] [范畴* D]
  证明: { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cone.ext ((preservesColimitNatIso F).symm.app _)
        fun i => (preservesColimitNatIso F).inv.naturality _ } } }

Depends on / 依赖: preservesFiniteLimits, preservesLimit
-/
lemma HasExactColimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* J] [Category* D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [ReflectsFiniteLimits F] [HasFiniteLimits C]
    [PreservesColimitsOfShape J F] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cone.ext ((preservesColimitNatIso F).symm.app _)
        fun i => (preservesColimitNatIso F).inv.naturality _ } } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {C} in
/--
lemma `HasExactLimitsOfShape.domain_of_functor` / 引理 `HasExactLimitsOfShape.domain_of_functor`

English:
lemma HasExactLimitsOfShape.domain_of_functor
  statement: {D : Type*} (J : Type*) [Category* D] [Category* J]
  proof: { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocone.ext ((preservesLimitNatIso F).symm.app _) fun i => ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocone.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

中文:
引理 有ExactLimitsOfShape.domain_of_functor
  结论: {D : 类型} (J : 类型) [范畴* D] [范畴* J]
  证明: { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocone.ext ((preservesLimitNatIso F).symm.app _) fun i => ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocone.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

Depends on / 依赖: preservesColimit, preservesFiniteColimits
-/
lemma HasExactLimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* D] [Category* J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteColimits F] [ReflectsFiniteColimits F] [HasFiniteColimits C]
    [PreservesLimitsOfShape J F] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocone.ext ((preservesLimitNatIso F).symm.app _) fun i => ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocone.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

/--
lemma `HasExactColimitsOfShape.of_domain_equivalence` / 引理 `HasExactColimitsOfShape.of_domain_equivalence`

English:
lemma HasExactColimitsOfShape.of_domain_equivalence
  statement: {J J' : Type*} [Category* J] [Category* J']
  proof: hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

中文:
引理 有ExactColimitsOfShape.of_domain_equivalence
  结论: {J J' : 类型} [范畴* J] [范畴* J']
  证明: hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

Depends on / 依赖: hasColimitsOfShape_of_equivalence
-/
lemma HasExactColimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

variable {C} in
/--
lemma `HasExactColimitsOfShape.of_codomain_equivalence` / 引理 `HasExactColimitsOfShape.of_codomain_equivalence`

English:
lemma HasExactColimitsOfShape.of_codomain_equivalence
  statement: (J : Type*) [Category* J] {D : Type*}
  proof: Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

中文:
引理 有ExactColimitsOfShape.of_codomain_equivalence
  结论: (J : 类型) [范畴* J] {D : 类型}
  证明: Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

Depends on / 依赖: Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, e.inverse, hasColimitsOfShape_of_equivalence, inverse
-/
lemma HasExactColimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

/--
lemma `HasExactLimitsOfShape.of_domain_equivalence` / 引理 `HasExactLimitsOfShape.of_domain_equivalence`

English:
lemma HasExactLimitsOfShape.of_domain_equivalence
  statement: {J J' : Type*} [Category* J] [Category* J']
  proof: hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

中文:
引理 有ExactLimitsOfShape.of_domain_equivalence
  结论: {J J' : 类型} [范畴* J] [范畴* J']
  证明: hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

Depends on / 依赖: hasLimitsOfShape_of_equivalence
-/
lemma HasExactLimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

variable {C} in
/--
lemma `HasExactLimitsOfShape.of_codomain_equivalence` / 引理 `HasExactLimitsOfShape.of_codomain_equivalence`

English:
lemma HasExactLimitsOfShape.of_codomain_equivalence
  statement: (J : Type*) [Category* J] {D : Type*}
  proof: Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  have : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

中文:
引理 有ExactLimitsOfShape.of_codomain_equivalence
  结论: (J : 类型) [范畴* J] {D : 类型}
  证明: Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  have : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

Depends on / 依赖: Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, e.inverse, hasLimitsOfShape_of_equivalence, inverse
-/
lemma HasExactLimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  have : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

namespace Adjunction

variable {C} {D : Type u''} [Category.{v''} D] {F : C ⥤ D} {G : D ⥤ C}

/--
lemma `hasExactColimitsOfShape` / 引理 `hasExactColimitsOfShape`

English:
lemma hasExactColimitsOfShape
  statement: (adj : F ⊣ G) [G.Full] [G.Faithful]
  proof: ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

中文:
引理 hasExactColimitsOfShape
  结论: (adj : F ⊣ G) [G.满] [G.忠实]
  证明: ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

Depends on / 依赖: Functor, Functor.associator, PreservesColimitsOfSize, PreservesLimitsOfSize, adj.counit, adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits, associator, counit, isoWhiskerLeft, isoWhiskerRight, leftAdjoint_preservesColimits, mapIso, preservesColimitNatIso, rightAdjoint_preservesLimits, whiskeringRight, whiskeringRightObjCompIso, whiskeringRightObjIdIso
-/
lemma hasExactColimitsOfShape (adj : F ⊣ G) [G.Full] [G.Faithful]
    (J : Type u') [Category.{v'} J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasExactColimitsOfShape J C] [HasFiniteLimits D] [PreservesFiniteLimits F] :
    HasExactColimitsOfShape J D where
  preservesFiniteLimits := ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

/--
lemma `hasExactLimitsOfShape` / 引理 `hasExactLimitsOfShape`

English:
lemma hasExactLimitsOfShape
  statement: (adj : F ⊣ G) [F.Full] [F.Faithful]
  proof: ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

中文:
引理 hasExactLimitsOfShape
  结论: (adj : F ⊣ G) [F.满] [F.忠实]
  证明: ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

Depends on / 依赖: Functor, Functor.associator, PreservesColimitsOfSize, PreservesLimitsOfSize, adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits, adj.unit, associator, isoWhiskerLeft, isoWhiskerRight, leftAdjoint_preservesColimits, lim.lef, mapIso, preservesLimitNatIso, rightAdjoint_preservesLimits, whiskeringRight, whiskeringRightObjCompIso, whiskeringRightObjIdIso
-/
lemma hasExactLimitsOfShape (adj : F ⊣ G) [F.Full] [F.Faithful]
    (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [HasExactLimitsOfShape J D] [HasFiniteColimits C] [PreservesFiniteColimits G] :
    HasExactLimitsOfShape J C where
  preservesFiniteColimits := ⟨fun K _ _ => ⟨fun {H} => by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

end Adjunction

/--
A category `C` which has coproducts is said to have `AB4` of size `w` provided that
coproducts of size `w` are exact.
-/
@[pp_with_univ]
/--
Definition of `AB4OfSize` / `AB4OfSize` 的定义

English:
class AB4OfSize
  parameters: [HasCoproducts.{w} C]
  axioms and operations (1):
    - ofShape((α : Type w)) : HasExactColimitsOfShape (Discrete α) C

中文:
类 AB4OfSize
  参数: [HasCoproducts.{w} C]
  公理与运算 (1 个):
    - ofShape((α : 类型 w)) : 有ExactColimitsOfShape (离散 α) C
-/
class AB4OfSize [HasCoproducts.{w} C] where
  ofShape (α : Type w) : HasExactColimitsOfShape (Discrete α) C

attribute [instance] AB4OfSize.ofShape

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
@[stacks 079B]
/--
Definition of `AB4` / `AB4` 的定义

English:
abbreviation AB4
  signature: [HasCoproducts C]
  body: AB4OfSize.{v} C

中文:
缩写 AB4
  签名: [HasCoproducts C]
  定义体: AB4OfSize.{v} C

Depends on / 依赖: AB4OfSize
-/
abbrev AB4 [HasCoproducts C] := AB4OfSize.{v} C

/--
lemma `AB4OfSize_shrink` / 引理 `AB4OfSize_shrink`

English:
lemma AB4OfSize_shrink
  given: [HasCoproducts.{max w w'} C] [AB4OfSize.{max w w'} C]
  proof: hasCoproducts_shrink.{w, w'}
    AB4OfSize.{w} C :=
  haveI := hasCoproducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

中文:
引理 AB4OfSize_shrink
  条件: [HasCoproducts.{最大值 w w'} C] [AB4OfSize.{最大值 w w'} C]
  证明: hasCoproducts_shrink.{w, w'}
    AB4OfSize.{w} C :=
  haveI := hasCoproducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

Depends on / 依赖: hasCoproducts_shrink
-/
lemma AB4OfSize_shrink [HasCoproducts.{max w w'} C] [AB4OfSize.{max w w'} C] :
    haveI : HasCoproducts.{w} C := hasCoproducts_shrink.{w, w'}
    AB4OfSize.{w} C :=
  haveI := hasCoproducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

instance (priority := 100) [HasCoproducts.{w} C] [AB4OfSize.{w} C] :
    haveI : HasCoproducts.{0} C := hasCoproducts_shrink
    AB4OfSize.{0} C := AB4OfSize_shrink C

/-- A category `C` which has products is said to have `AB4Star` (in literature AB4\*)
provided that products are exact. -/
@[pp_with_univ, stacks 079B]
/--
Definition of `AB4StarOfSize` / `AB4StarOfSize` 的定义

English:
class AB4StarOfSize
  parameters: [HasProducts.{w} C]
  axioms and operations (1):
    - ofShape((α : Type w)) : HasExactLimitsOfShape (Discrete α) C

中文:
类 AB4StarOfSize
  参数: [HasProducts.{w} C]
  公理与运算 (1 个):
    - ofShape((α : 类型 w)) : 有ExactLimitsOfShape (离散 α) C
-/
class AB4StarOfSize [HasProducts.{w} C] where
  ofShape (α : Type w) : HasExactLimitsOfShape (Discrete α) C

attribute [instance] AB4StarOfSize.ofShape

/--
Definition of `AB4Star` / `AB4Star` 的定义

English:
abbreviation AB4Star
  signature: [HasProducts C]
  body: AB4StarOfSize.{v} C

中文:
缩写 AB4Star
  签名: [HasProducts C]
  定义体: AB4StarOfSize.{v} C

Depends on / 依赖: AB4StarOfSize
-/
abbrev AB4Star [HasProducts C] := AB4StarOfSize.{v} C

/--
lemma `AB4StarOfSize_shrink` / 引理 `AB4StarOfSize_shrink`

English:
lemma AB4StarOfSize_shrink
  given: [HasProducts.{max w w'} C] [AB4StarOfSize.{max w w'} C]
  proof: hasProducts_shrink.{w, w'}
    AB4StarOfSize.{w} C :=
  haveI := hasProducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactLimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

中文:
引理 AB4StarOfSize_shrink
  条件: [HasProducts.{最大值 w w'} C] [AB4StarOfSize.{最大值 w w'} C]
  证明: hasProducts_shrink.{w, w'}
    AB4StarOfSize.{w} C :=
  haveI := hasProducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactLimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

Depends on / 依赖: hasProducts_shrink
-/
lemma AB4StarOfSize_shrink [HasProducts.{max w w'} C] [AB4StarOfSize.{max w w'} C] :
    haveI : HasProducts.{w} C := hasProducts_shrink.{w, w'}
    AB4StarOfSize.{w} C :=
  haveI := hasProducts_shrink.{w, w'} (C := C)
  ⟨fun J => HasExactLimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

instance (priority := 100) [HasProducts.{w} C] [AB4StarOfSize.{w} C] :
    haveI : HasProducts.{0} C := hasProducts_shrink
    AB4StarOfSize.{0} C := AB4StarOfSize_shrink C

/--
Definition of `CountableAB4` / `CountableAB4` 的定义

English:
class CountableAB4
  parameters: [HasCountableCoproducts C]
  axioms and operations (1):
    - ofShape((α : Type) [Countable α]) : HasExactColimitsOfShape (Discrete α) C

中文:
类 余untableAB4
  参数: [有余untableCoproducts C]
  公理与运算 (1 个):
    - ofShape((α : 类型) [可数 α]) : 有ExactColimitsOfShape (离散 α) C
-/
class CountableAB4 [HasCountableCoproducts C] where
  ofShape (α : Type) [Countable α] : HasExactColimitsOfShape (Discrete α) C

instance (priority := 100) [HasCoproducts.{0} C] [AB4OfSize.{0} C] : CountableAB4 C :=
  ⟨inferInstance⟩

/--
Definition of `CountableAB4Star` / `CountableAB4Star` 的定义

English:
class CountableAB4Star
  parameters: [HasCountableProducts C]
  axioms and operations (1):
    - ofShape((α : Type) [Countable α]) : HasExactLimitsOfShape (Discrete α) C

中文:
类 余untableAB4Star
  参数: [有余untableProducts C]
  公理与运算 (1 个):
    - ofShape((α : 类型) [可数 α]) : 有ExactLimitsOfShape (离散 α) C
-/
class CountableAB4Star [HasCountableProducts C] where
  ofShape (α : Type) [Countable α] : HasExactLimitsOfShape (Discrete α) C

instance (priority := 100) [HasProducts.{0} C] [AB4StarOfSize.{0} C] : CountableAB4Star C :=
  ⟨inferInstance⟩

attribute [instance] CountableAB4.ofShape CountableAB4Star.ofShape

/--
A category `C` which has filtered colimits of a given size is said to have `AB5` of that size
provided that these filtered colimits are exact.

`AB5OfSize.{w, w'} C` means that `C` has exact colimits of shape `J : Type w'` with
`Category.{w} J` such that `J` is filtered.
-/
@[pp_with_univ]
/--
Definition of `AB5OfSize` / `AB5OfSize` 的定义

English:
class AB5OfSize
  parameters: [HasFilteredColimitsOfSize.{w, w'} C]
  axioms and operations (1):
    - ofShape((J : Type w') [Category.{w} J] [IsFiltered J]) : HasExactColimitsOfShape J C

中文:
类 AB5OfSize
  参数: [有FilteredColimitsOfSize.{w, w'} C]
  公理与运算 (1 个):
    - ofShape((J : 类型 w') [范畴.{w} J] [是Filtered J]) : 有ExactColimitsOfShape J C
-/
class AB5OfSize [HasFilteredColimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsFiltered J] : HasExactColimitsOfShape J C

attribute [instance] AB5OfSize.ofShape

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
@[stacks 079B]
/--
Definition of `AB5` / `AB5` 的定义

English:
abbreviation AB5
  signature: [HasFilteredColimits C]
  body: AB5OfSize.{v, v} C

中文:
缩写 AB5
  签名: [HasFilteredColimits C]
  定义体: AB5OfSize.{v, v} C

Depends on / 依赖: AB5OfSize
-/
abbrev AB5 [HasFilteredColimits C] := AB5OfSize.{v, v} C

/--
lemma `AB5OfSize_of_univLE` / 引理 `AB5OfSize_of_univLE`

English:
lemma AB5OfSize_of_univLE
  statement: [HasFilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
  proof: hasFilteredColimitsOfSize_of_univLE.{w}
    AB5OfSize.{w, w'} C := by
  have : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactColimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

中文:
引理 AB5OfSize_of_univLE
  结论: [有FilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
  证明: hasFilteredColimitsOfSize_of_univLE.{w}
    AB5OfSize.{w, w'} C := by
  have : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactColimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

Depends on / 依赖: hasFilteredColimitsOfSize_of_univLE
-/
lemma AB5OfSize_of_univLE [HasFilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5OfSize.{w₂, w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
    AB5OfSize.{w, w'} C := by
  have : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactColimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

/--
lemma `AB5OfSize_shrink` / 引理 `AB5OfSize_shrink`

English:
lemma AB5OfSize_shrink
  statement: [HasFilteredColimitsOfSize.{max w w₂, max w' w₂'} C]
  proof: hasFilteredColimitsOfSize_shrink
    AB5OfSize.{w, w'} C :=
  AB5OfSize_of_univLE C

中文:
引理 AB5OfSize_shrink
  结论: [有FilteredColimitsOfSize.{最大值 w w₂, 最大值 w' w₂'} C]
  证明: hasFilteredColimitsOfSize_shrink
    AB5OfSize.{w, w'} C :=
  AB5OfSize_of_univLE C

Depends on / 依赖: hasFilteredColimitsOfSize_shrink
-/
lemma AB5OfSize_shrink [HasFilteredColimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5OfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_shrink
    AB5OfSize.{w, w'} C :=
  AB5OfSize_of_univLE C

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
@[pp_with_univ, stacks 079B]
/--
Definition of `AB5StarOfSize` / `AB5StarOfSize` 的定义

English:
class AB5StarOfSize
  parameters: [HasCofilteredLimitsOfSize.{w, w'} C]
  axioms and operations (1):
    - ofShape((J : Type w') [Category.{w} J] [IsCofiltered J]) : HasExactLimitsOfShape J C

中文:
类 AB5StarOfSize
  参数: [有余filteredLimitsOfSize.{w, w'} C]
  公理与运算 (1 个):
    - ofShape((J : 类型 w') [范畴.{w} J] [是余filtered J]) : 有ExactLimitsOfShape J C
-/
class AB5StarOfSize [HasCofilteredLimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsCofiltered J] : HasExactLimitsOfShape J C

attribute [instance] AB5StarOfSize.ofShape

/--
Definition of `AB5Star` / `AB5Star` 的定义

English:
abbreviation AB5Star
  signature: [HasCofilteredLimits C]
  body: AB5StarOfSize.{v, v} C

中文:
缩写 AB5Star
  签名: [HasCofilteredLimits C]
  定义体: AB5StarOfSize.{v, v} C

Depends on / 依赖: AB5StarOfSize
-/
abbrev AB5Star [HasCofilteredLimits C] := AB5StarOfSize.{v, v} C

/--
lemma `AB5StarOfSize_of_univLE` / 引理 `AB5StarOfSize_of_univLE`

English:
lemma AB5StarOfSize_of_univLE
  statement: [HasCofilteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
  proof: hasCofilteredLimitsOfSize_of_univLE.{w}
    AB5StarOfSize.{w, w'} C := by
  have : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactLimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

中文:
引理 AB5StarOfSize_of_univLE
  结论: [有余filteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
  证明: hasCofilteredLimitsOfSize_of_univLE.{w}
    AB5StarOfSize.{w, w'} C := by
  have : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactLimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

Depends on / 依赖: hasCofilteredLimitsOfSize_of_univLE
-/
lemma AB5StarOfSize_of_univLE [HasCofilteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5StarOfSize.{w₂, w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
    AB5StarOfSize.{w, w'} C := by
  have : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  have := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactLimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

/--
lemma `AB5StarOfSize_shrink` / 引理 `AB5StarOfSize_shrink`

English:
lemma AB5StarOfSize_shrink
  statement: [HasCofilteredLimitsOfSize.{max w w₂, max w' w₂'} C]
  proof: hasCofilteredLimitsOfSize_shrink
    AB5StarOfSize.{w, w'} C :=
  AB5StarOfSize_of_univLE C

中文:
引理 AB5StarOfSize_shrink
  结论: [有余filteredLimitsOfSize.{最大值 w w₂, 最大值 w' w₂'} C]
  证明: hasCofilteredLimitsOfSize_shrink
    AB5StarOfSize.{w, w'} C :=
  AB5StarOfSize_of_univLE C

Depends on / 依赖: hasCofilteredLimitsOfSize_shrink
-/
lemma AB5StarOfSize_shrink [HasCofilteredLimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5StarOfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_shrink
    AB5StarOfSize.{w, w'} C :=
  AB5StarOfSize_of_univLE C

/--
lemma `hasExactColimitsOfShape_of_final` / 引理 `hasExactColimitsOfShape_of_final`

English:
lemma hasExactColimitsOfShape_of_final
  statement: [HasFiniteLimits C]
  proof: letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

中文:
引理 hasExactColimitsOfShape_of_final
  结论: [有有限极限 C]
  证明: letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

Depends on / 依赖: Functor, Functor.Final.colimIso, PreservesFiniteLimits, colimIso, comp_preservesFiniteLimits, preservesFiniteLimits_of_natIso, whiskeringLeft
-/
lemma hasExactColimitsOfShape_of_final [HasFiniteLimits C]
    {J J' : Type*} [Category* J] [Category* J']
    (F : J ⥤ J') [F.Final] [HasColimitsOfShape J' C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] : HasExactColimitsOfShape J' C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

/--
lemma `hasExactLimitsOfShape_of_initial` / 引理 `hasExactLimitsOfShape_of_initial`

English:
lemma hasExactLimitsOfShape_of_initial
  statement: [HasFiniteColimits C] {J J' : Type*} [Category* J]
  proof: letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

中文:
引理 hasExactLimitsOfShape_of_initial
  结论: [有有限余极限 C] {J J' : 类型} [范畴* J]
  证明: letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

Depends on / 依赖: Functor, Functor.Initial.limIso, Initial, PreservesFiniteColimits, comp_preservesFiniteColimits, limIso, preservesFiniteColimits_of_natIso, whiskeringLeft
-/
lemma hasExactLimitsOfShape_of_initial [HasFiniteColimits C] {J J' : Type*} [Category* J]
    [Category* J'] (F : J ⥤ J') [F.Initial] [HasLimitsOfShape J' C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] : HasExactLimitsOfShape J' C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ => inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

section AB4OfAB5

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]

open CoproductsFromFiniteFiltered

/--
Instance `preservesFiniteLimits_liftToFinset` / 实例 `preservesFiniteLimits_liftToFinset`

English:
instance preservesFiniteLimits_liftToFinset
  signature: : PreservesFiniteLimits (liftToFinset C α)
  body: preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso I).symm

中文:
实例 preservesFiniteLimits_liftToFinset
  签名: : 保持FiniteLimits (liftToFinset C α)
  定义体: preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso I).symm

Depends on / 依赖: Discrete, Discrete.functor, HasBiproductsOfShape, HasBiproductsOfShape.colimIsoLim.symm, PreservesFiniteLimits, colimIsoLim, comp_preservesFiniteLimits, functor, preservesFiniteLimits_of_evaluation, preservesFiniteLimits_of_natIso, whiskeringLeft, whiskeringLeft_preservesLimitsOfShape
-/
instance preservesFiniteLimits_liftToFinset : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso I).symm

variable (J : Type*)

/--
lemma `hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete` / 引理 `hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete`

English:
lemma hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
  proof: letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

中文:
引理 hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
  证明: letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

Depends on / 依赖: PreservesFiniteLimits, comp_preservesFiniteLimits, liftToFinset, liftToFinsetColimIso, preservesFiniteLimits_of_natIso
-/
lemma hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C]
    [HasExactColimitsOfShape (Finset (Discrete J)) C] : HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

attribute [local instance] hasCoproducts_of_finite_and_filtered in
/--
lemma `AB4.of_AB5` / 引理 `AB4.of_AB5`

English:
lemma AB4.of_AB5
  statement: [HasFilteredColimitsOfSize.{w, w} C]
  proof: hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

中文:
引理 AB4.of_AB5
  结论: [有FilteredColimitsOfSize.{w, w} C]
  证明: hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

Depends on / 依赖: hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
-/
lemma AB4.of_AB5 [HasFilteredColimitsOfSize.{w, w} C]
    [AB5OfSize.{w, w} C] : AB4OfSize.{w} C where
  ofShape _ := hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

/--
lemma `CountableAB4.of_countableAB5` / 引理 `CountableAB4.of_countableAB5`

English:
lemma CountableAB4.of_countableAB5
  statement: [HasColimitsOfShape Nat C] [HasExactColimitsOfShape Nat C]
  proof: have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := hasExactColimitsOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

中文:
引理 余untableAB4.of_countableAB5
  结论: [有形状余极限 自然数 C] [有ExactColimitsOfShape 自然数 C]
  证明: have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := hasExactColimitsOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

Depends on / 依赖: Discrete, Finset, Functor, Functor.Final.hasColimitsOfShape_of_final, HasColimitsOfShape, IsFiltered, IsFiltered.sequentialFunctor, hasColimitsOfShape_of_final, hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete, hasExactColimitsOfShape_of_final, sequentialFunctor
-/
lemma CountableAB4.of_countableAB5 [HasColimitsOfShape Nat C] [HasExactColimitsOfShape Nat C]
    [HasCountableCoproducts C] : CountableAB4 C where
  ofShape J :=
    have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := hasExactColimitsOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

end AB4OfAB5

section AB4StarOfAB5Star

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteColimits C]

open ProductsFromFiniteCofiltered

/--
Instance `preservesFiniteColimits_liftToFinset` / 实例 `preservesFiniteColimits_liftToFinset`

English:
instance preservesFiniteColimits_liftToFinset
  signature: : PreservesFiniteColimits (liftToFinset C α)
  body: preservesFiniteColimits_of_evaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso _ _ I).symm

中文:
实例 preservesFiniteColimits_liftToFinset
  签名: : 保持FiniteColimits (liftToFinset C α)
  定义体: preservesFiniteColimits_of_evaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso _ _ I).symm

Depends on / 依赖: Discrete, Discrete.functor, HasBiproductsOfShape, HasBiproductsOfShape.colimIsoLim, PreservesFiniteColimits, colimIsoLim, comp_preservesFiniteColimits, functor, preservesFiniteColi, preservesFiniteColimits_of_evaluation, preservesFiniteColimits_of_natIso, whiskeringLeft
-/
instance preservesFiniteColimits_liftToFinset : PreservesFiniteColimits (liftToFinset C α) :=
  preservesFiniteColimits_of_evaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x => ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso _ _ I).symm

variable (J : Type*)

/--
lemma `hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op` / 引理 `hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op`

English:
lemma hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
  proof: letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

中文:
引理 hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
  证明: letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

Depends on / 依赖: PreservesFiniteColimits, ProductsFromFiniteCofiltered, ProductsFromFiniteCofiltered.liftToFinset, ProductsFromFiniteCofiltered.liftToFinsetLimIso, comp_preservesFiniteColimits, liftToFinset, liftToFinsetLimIso, preservesFiniteColimits_of_natIso
-/
lemma hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
    [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C]
    [HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

attribute [local instance] hasProducts_of_finite_and_cofiltered in
/--
lemma `AB4Star.of_AB5Star` / 引理 `AB4Star.of_AB5Star`

English:
lemma AB4Star.of_AB5Star
  given: [HasCofilteredLimitsOfSize.{w, w} C] [AB5StarOfSize.{w, w} C]
  proof: hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

中文:
引理 AB4Star.of_AB5Star
  条件: [有余filteredLimitsOfSize.{w, w} C] [AB5StarOfSize.{w, w} C]
  证明: hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

Depends on / 依赖: hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
-/
lemma AB4Star.of_AB5Star [HasCofilteredLimitsOfSize.{w, w} C] [AB5StarOfSize.{w, w} C] :
    AB4StarOfSize.{w} C where
  ofShape _ := hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

/--
lemma `CountableAB4Star.of_countableAB5Star` / 引理 `CountableAB4Star.of_countableAB5Star`

English:
lemma CountableAB4Star.of_countableAB5Star
  statement: [HasLimitsOfShape Natᵒᵖ C] [HasExactLimitsOfShape Natᵒᵖ C]
  proof: have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := hasExactLimitsOfShape_of_initial C
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

中文:
引理 余untableAB4Star.of_countableAB5Star
  结论: [有形状极限 自然数ᵒᵖ C] [有ExactLimitsOfShape 自然数ᵒᵖ C]
  证明: have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := hasExactLimitsOfShape_of_initial C
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

Depends on / 依赖: Discrete, Finset, Functor, Functor.Initial.hasLimitsOfShape_of_initial, HasLimitsOfShape, Initial, IsFiltered, IsFiltered.sequentialFunctor, hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op, hasExactLimitsOfShape_of_initial, hasLimitsOfShape_of_initial, sequentialFunctor
-/
lemma CountableAB4Star.of_countableAB5Star [HasLimitsOfShape Natᵒᵖ C] [HasExactLimitsOfShape Natᵒᵖ C]
    [HasCountableProducts C] : CountableAB4Star C where
  ofShape J :=
    have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := hasExactLimitsOfShape_of_initial C
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

end AB4StarOfAB5Star

/--
lemma `CountableAB4.of_hasExactColimitsOfShape_nat_and_finite` / 引理 `CountableAB4.of_hasExactColimitsOfShape_nat_and_finite`

English:
lemma CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  statement: [HasCountableCoproducts C]
  proof: by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactColimitsOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

中文:
引理 余untableAB4.of_hasExactColimitsOfShape_nat_and_finite
  结论: [有余untableCoproducts C]
  证明: by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactColimitsOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

Depends on / 依赖: Denumerable, Denumerable.eqv, Denumerable.ofEncodableOfInfinite, Discrete, Discrete.equivalence, Encodable, Encodable.ofCountable, Finite, Infinite, equivalence, hasExactColimitsOfShape_of_final, infer_instance, inverse, ofCountable, ofEncodableOfInfinite
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat_and_finite [HasCountableCoproducts C]
    [HasFiniteLimits C] [forall (J : Type) [Finite J], HasExactColimitsOfShape (Discrete J) C]
    [HasExactColimitsOfShape (Discrete Nat) C] :
    CountableAB4 C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactColimitsOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

/--
lemma `CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite` / 引理 `CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite`

English:
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  statement: [HasCountableProducts C]
  proof: by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactLimitsOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

中文:
引理 余untableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  结论: [有余untableProducts C]
  证明: by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactLimitsOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

Depends on / 依赖: Denumerable, Denumerable.eqv, Denumerable.ofEncodableOfInfinite, Discrete, Discrete.equivalence, Encodable, Encodable.ofCountable, Finite, Infinite, equivalence, hasExactLimitsOfShape_of_initial, infer_instance, inverse, ofCountable, ofEncodableOfInfinite
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite [HasCountableProducts C]
    [HasFiniteColimits C] [forall (J : Type) [Finite J], HasExactLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete Nat) C] :
    CountableAB4Star C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactLimitsOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

section EpiMono


section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/--
Instance `hasExactColimitsOfShape_discrete_finite` / 实例 `hasExactColimitsOfShape_discrete_finite`

English:
instance hasExactColimitsOfShape_discrete_finite
  signature: (J : Type*) [Finite J]
  body: preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm

中文:
实例 hasExactColimitsOfShape_discrete_finite
  签名: (J : 类型) [有限 J]
  定义体: preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm

Depends on / 依赖: HasBiproductsOfShape, HasBiproductsOfShape.colimIsoLim.symm, colimIsoLim, preservesFiniteLimits_of_natIso
-/
noncomputable instance hasExactColimitsOfShape_discrete_finite (J : Type*) [Finite J] :
    HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits := preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm

/--
Instance `hasExactLimitsOfShape_discrete_finite` / 实例 `hasExactLimitsOfShape_discrete_finite`

English:
instance hasExactLimitsOfShape_discrete_finite
  signature: {J : Type*} [Finite J]
  body: preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

中文:
实例 hasExactLimitsOfShape_discrete_finite
  签名: {J : 类型} [有限 J]
  定义体: preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

Depends on / 依赖: HasBiproductsOfShape, HasBiproductsOfShape.colimIsoLim, colimIsoLim, preservesFiniteColimits_of_natIso
-/
noncomputable instance hasExactLimitsOfShape_discrete_finite {J : Type*} [Finite J] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits := preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

/--
lemma `CountableAB4.of_hasExactColimitsOfShape_nat` / 引理 `CountableAB4.of_hasExactColimitsOfShape_nat`

English:
lemma CountableAB4.of_hasExactColimitsOfShape_nat
  statement: [HasFiniteLimits C] [HasCountableCoproducts C]
  proof: by
  apply +allowSynthFailures CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

中文:
引理 余untableAB4.of_hasExactColimitsOfShape_nat
  结论: [有有限极限 C] [有余untableCoproducts C]
  证明: by
  apply +allowSynthFailures CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

Depends on / 依赖: CountableAB4, CountableAB4.of_hasExactColimitsOfShape_nat_and_finite, allowSynthFailures, of_hasExactColimitsOfShape_nat_and_finite
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat [HasFiniteLimits C] [HasCountableCoproducts C]
    [HasExactColimitsOfShape (Discrete Nat) C] : CountableAB4 C := by
  apply +allowSynthFailures CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

/--
lemma `CountableAB4Star.of_hasExactLimitsOfShape_nat` / 引理 `CountableAB4Star.of_hasExactLimitsOfShape_nat`

English:
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat
  statement: [HasFiniteColimits C]
  proof: by
  apply +allowSynthFailures CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

中文:
引理 余untableAB4Star.of_hasExactLimitsOfShape_nat
  结论: [有有限余极限 C]
  证明: by
  apply +allowSynthFailures CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

Depends on / 依赖: CountableAB4Star, CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite, allowSynthFailures, of_hasExactLimitsOfShape_nat_and_finite
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat [HasFiniteColimits C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete Nat) C] : CountableAB4Star C := by
  apply +allowSynthFailures CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  exact fun _ => inferInstance

end

variable [Abelian C] (J : Type u') [Category.{v'} J]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/--
lemma `hasExactColimitsOfShape_of_preservesMono` / 引理 `hasExactColimitsOfShape_of_preservesMono`

English:
lemma hasExactColimitsOfShape_of_preservesMono
  statement: [HasColimitsOfShape J C]
  proof: by
    apply +allowSynthFailures preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

中文:
引理 hasExactColimitsOfShape_of_preservesMono
  结论: [有形状余极限 J C]
  证明: by
    apply +allowSynthFailures preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

Depends on / 依赖: HasExactColimitsOfShape
-/
lemma hasExactColimitsOfShape_of_preservesMono [HasColimitsOfShape J C]
    [PreservesMonomorphisms (colim (J := J) (C := C))] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := by
    apply +allowSynthFailures preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

/--
lemma `hasExactLimitsOfShape_of_preservesEpi` / 引理 `hasExactLimitsOfShape_of_preservesEpi`

English:
lemma hasExactLimitsOfShape_of_preservesEpi
  statement: [HasLimitsOfShape J C]
  proof: by
    apply +allowSynthFailures preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

中文:
引理 hasExactLimitsOfShape_of_preservesEpi
  结论: [有形状极限 J C]
  证明: by
    apply +allowSynthFailures preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

Depends on / 依赖: HasExactLimitsOfShape
-/
lemma hasExactLimitsOfShape_of_preservesEpi [HasLimitsOfShape J C]
    [PreservesEpimorphisms (lim (J := J) (C := C))] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := by
    apply +allowSynthFailures preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

end EpiMono

end CategoryTheory
