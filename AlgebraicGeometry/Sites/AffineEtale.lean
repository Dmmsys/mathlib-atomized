/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

-- these `ModuleCat` instances are only used by the `example` below, which `shake` cannot see
public import Mathlib.Algebra.Category.ModuleCat.AB -- shake: keep
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits -- shake: keep
public import Mathlib.AlgebraicGeometry.Sites.Affine
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Affine étale site

In this file we define the small affine étale site of a scheme `S`. The underlying
category is the category of commutative rings `R` equipped with an étale structure
morphism `Spec R ⟶ S`. We show that this category is essentially small,
that it is a dense subsite of the small étale site, and that it is `1`-hypercover
dense, which allows to show that if `S : Scheme.{u}`, then we can sheafify
étale presheaves with values in `Type u`, `AddCommGrpCat.{u}`, etc.

## Main results

- `AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv`: The category of sheaves on the
  small affine étale site is equivalent to the category of schemes on the small étale site.
- `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`: The category of
  sheaves on the étale site with values in a Grothendieck abelian category is Grothendieck abelian.
-/

@[expose] public noncomputable section

universe u v u'

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `AffineEtale` / `AffineEtale` 的定义

English:
definition AffineEtale
  signature: (S : Scheme.{u})
  body: MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S
deriving Category, HasPullbacks

中文:
定义 AffineEtale
  签名: (S : Scheme.{u})
  定义体: MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S
deriving Category, HasPullbacks

Depends on / 依赖: CostructuredArrow, MorphismProperty, MorphismProperty.CostructuredArrow, Scheme, Scheme.Spec
-/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S
deriving Category, HasPullbacks

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f]
  body: MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

中文:
定义 mk
  签名: {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f]
  定义体: MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›
-/
protected def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

/-- The `Spec` functor from the small affine étale site of `S` to the small étale site of `S`. -/
@[simps! obj_left obj_hom map_left]
/--
Definition of `Spec` / `Spec` 的定义

English:
definition Spec
  signature: (S : Scheme.{u})
  body: MorphismProperty.CostructuredArrow.toOver _ _ _

中文:
定义 Spec
  签名: (S : Scheme.{u})
  定义体: MorphismProperty.CostructuredArrow.toOver _ _ _
-/
protected def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (AffineEtale.Spec S).Faithful
  body: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

中文:
实例 :
  签名: (AffineEtale.Spec S).Faithful
  定义体: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

Depends on / 依赖: CostructuredArrow, Faithful, MorphismProperty, MorphismProperty.CostructuredArrow.toOver, toOver
-/
instance : (AffineEtale.Spec S).Faithful :=
inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (AffineEtale.Spec S).Full
  body: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

中文:
实例 :
  签名: (AffineEtale.Spec S).Full
  定义体: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

Depends on / 依赖: CostructuredArrow, MorphismProperty, MorphismProperty.CostructuredArrow.toOver, toOver
-/
instance : (AffineEtale.Spec S).Full :=
inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology
  body: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (S.smallGrothendieckTopology _)

中文:
实例 :
  签名: (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology
  定义体: inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (S.smallGrothendieckTopology _)

Depends on / 依赖: CostructuredArrow, IsCoverDense, MorphismProperty, MorphismProperty.CostructuredArrow.toOver, S.smallGrothendieckTopology, smallGrothendieckTopology, toOver
-/
instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (S.smallGrothendieckTopology _)

variable (S) in
/--
Definition of `topology` / `topology` 的定义

English:
definition topology
  signature: : GrothendieckTopology S.AffineEtale
  body: (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology

中文:
定义 topology
  签名: : GrothendieckTopology S.AffineEtale
  定义体: (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology

Depends on / 依赖: AffineEtale, AffineEtale.Spec, S.smallEtaleTopology, inducedTopology, smallEtaleTopology
-/
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S)
  body: by
  dsimp [topology]
  infer_instance

中文:
实例 :
  签名: Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S)
  定义体: by
  dsimp [topology]
  infer_instance

Depends on / 依赖: infer_instance, topology
-/
instance : Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S) := by
  dsimp [topology]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
  body: isOneHypercoverDense_toOver_Spec _

中文:
实例 :
  签名: Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
  定义体: isOneHypercoverDense_toOver_Spec _

Depends on / 依赖: isOneHypercoverDense_toOver_Spec
-/
instance : Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (topology S) S.smallEtaleTopology :=
  isOneHypercoverDense_toOver_Spec _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{u} S.AffineEtale
  body: essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ => inferInstance

中文:
实例 :
  签名: EssentiallySmall.{u} S.AffineEtale
  定义体: essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ => inferInstance

Depends on / 依赖: essentiallySmall_costructuredArrow_Spec
-/
instance : EssentiallySmall.{u} S.AffineEtale :=
  essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ => inferInstance

end AffineEtale

section

variable {A : Type u'} [Category.{u} A]
  {FA : A -> A -> Type*} {CD : A -> Type u}
  [forall X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSheafify (AffineEtale.topology S) A
  body: hasSheafifyEssentiallySmallSite.{u} _ _

中文:
实例 :
  签名: HasSheafify (AffineEtale.topology S) A
  定义体: hasSheafifyEssentiallySmallSite.{u} _ _

Depends on / 依赖: hasSheafifyEssentiallySmallSite
-/
instance : HasSheafify (AffineEtale.topology S) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((AffineEtale.Spec S).sheafPushforwardContinuous A
  body: Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

中文:
实例 :
  签名: ((AffineEtale.Spec S).sheafPushforwardContinuous A
  定义体: Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

Depends on / 依赖: Functor, Functor.isEquivalence_of_isOneHypercoverDense, isEquivalence_of_isOneHypercoverDense
-/
instance : ((AffineEtale.Spec S).sheafPushforwardContinuous A
    (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSheafify S.smallEtaleTopology A
  body: Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

中文:
实例 :
  签名: HasSheafify S.smallEtaleTopology A
  定义体: Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

Depends on / 依赖: AffineEtale, AffineEtale.Spec, AffineEtale.topology, Functor, Functor.IsDenseSubsite.hasSheafify_of_isEquivalence, IsDenseSubsite, S.smallEtaleTopology, hasSheafify_of_isEquivalence, smallEtaleTopology, topology
-/
instance : HasSheafify S.smallEtaleTopology A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

中文:
实例 :
  定义体: Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

Depends on / 依赖: Functor, Functor.isEquivalence_of_isOneHypercoverDense, isEquivalence_of_isOneHypercoverDense
-/
instance :
    ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (AffineEtale.topology S).WEqualsLocallyBijective A
  body: .ofEssentiallySmall (AffineEtale.topology S)

中文:
实例 :
  签名: (AffineEtale.topology S).WEqualsLocallyBijective A
  定义体: .ofEssentiallySmall (AffineEtale.topology S)

Depends on / 依赖: AffineEtale, AffineEtale.topology, ofEssentiallySmall, topology
-/
instance : (AffineEtale.topology S).WEqualsLocallyBijective A :=
  .ofEssentiallySmall (AffineEtale.topology S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: S.smallEtaleTopology.WEqualsLocallyBijective A
  body: .transport _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

中文:
实例 :
  签名: S.smallEtaleTopology.WEqualsLocallyBijective A
  定义体: .transport _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

Depends on / 依赖: AffineEtale, AffineEtale.Spec, AffineEtale.topology, Functor, Functor.IsDenseSubsite.coverPreserving, IsDenseSubsite, coverPreserving, topology, transport
-/
instance : S.smallEtaleTopology.WEqualsLocallyBijective A :=
  .transport _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

-- The `IsGrothendieckAbelian` instances defined below would fail
-- without the next two instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: A] : Abelian (Sheaf (AffineEtale.topology S) A)
  body: inferInstance

中文:
实例 [Abelian
  签名: A] : Abelian (Sheaf (AffineEtale.topology S) A)
  定义体: inferInstance
-/
instance [Abelian A] : Abelian (Sheaf (AffineEtale.topology S) A) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: A] : Abelian (Sheaf S.smallEtaleTopology A)
  body: inferInstance

中文:
实例 [Abelian
  签名: A] : Abelian (Sheaf S.smallEtaleTopology A)
  定义体: inferInstance
-/
instance [Abelian A] : Abelian (Sheaf S.smallEtaleTopology A) := inferInstance

variable (S A)

/-- The category of sheaves on the small affine étale site is equivalent to the category of
sheaves on the small étale site. -/
@[simps! inverse]
/--
Definition of `AffineEtale.sheafEquiv` / `AffineEtale.sheafEquiv` 的定义

English:
definition AffineEtale.sheafEquiv
  signature: : Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A
  body: ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm

中文:
定义 AffineEtale.sheafEquiv
  签名: : Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A
  定义体: ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm

Depends on / 依赖: AffineEtale, AffineEtale.Spec, S.smallEtaleTopology, asEquivalence, asEquivalence.symm, sheafPushforwardContinuous, smallEtaleTopology, topology
-/
def AffineEtale.sheafEquiv : Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A :=
  ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm

/--
Instance `isGrothendieckAbelian_sheaf_affineEtaleTopology` / 实例 `isGrothendieckAbelian_sheaf_affineEtaleTopology`

English:
instance isGrothendieckAbelian_sheaf_affineEtaleTopology
  body: Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

中文:
实例 isGrothendieckAbelian_sheaf_affineEtaleTopology
  定义体: Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

Depends on / 依赖: Sheaf.isGrothendieckAbelian_of_essentiallySmall, isGrothendieckAbelian_of_essentiallySmall
-/
instance isGrothendieckAbelian_sheaf_affineEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.topology S) A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/--
Instance `isGrothendieckAbelian_sheaf_smallEtaleTopology` / 实例 `isGrothendieckAbelian_sheaf_smallEtaleTopology`

English:
instance isGrothendieckAbelian_sheaf_smallEtaleTopology
  body: IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)

example (R : Type u) [Ring R] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  inferInstance

中文:
实例 isGrothendieckAbelian_sheaf_smallEtaleTopology
  定义体: IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)

example (R : Type u) [Ring R] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  inferInstance

Depends on / 依赖: AffineEtale, AffineEtale.sheafEquiv, IsGrothendieckAbelian, IsGrothendieckAbelian.of_equivalence, of_equivalence, sheafEquiv
-/
instance isGrothendieckAbelian_sheaf_smallEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A) :=
  IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)

example (R : Type u) [Ring R] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  inferInstance

end

end AlgebraicGeometry.Scheme
