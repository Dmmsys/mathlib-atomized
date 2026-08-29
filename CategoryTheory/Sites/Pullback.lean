/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Pullback of sheaves

## Main definitions

* `CategoryTheory.Functor.sheafPullback`: when `G : C ⥤ D` is a continuous functor
  between sites (for topologies `J` on `C` and `K` on `D`) such that the functor
  `G.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` has a left adjoint,
  this is the pullback functor defined as a chosen left adjoint.

* `CategoryTheory.Functor.sheafAdjunctionContinuous`: the adjunction
  `G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K` when the functor
  `G` is continuous. In case `G` is representably flat, the pullback functor
  on sheaves commutes with finite limits: this is a morphism of sites in the
  sense of SGA 4 IV 4.9.

-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory.Functor

open Limits

section GeneralUniverses

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D] (G : C ⥤ D)
  (A : Type u₁) [Category.{v₁} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [Functor.IsContinuous G J K]

section

variable [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/--
Definition of `sheafPullback` / `sheafPullback` 的定义

English:
definition sheafPullback
  signature: : Sheaf J A ⥤ Sheaf K A
  body: (G.sheafPushforwardContinuous A J K).leftAdjoint

中文:
定义 sheafPullback
  签名: : Sheaf J A ⥤ Sheaf K A
  定义体: (G.sheafPushforwardContinuous A J K).leftAdjoint

Depends on / 依赖: G.sheafPushforwardContinuous, leftAdjoint, sheafPushforwardContinuous
-/
def sheafPullback : Sheaf J A ⥤ Sheaf K A :=
  (G.sheafPushforwardContinuous A J K).leftAdjoint

/--
Definition of `sheafAdjunctionContinuous` / `sheafAdjunctionContinuous` 的定义

English:
definition sheafAdjunctionContinuous
  signature: :
  body: Adjunction.ofIsRightAdjoint (G.sheafPushforwardContinuous A J K)

中文:
定义 sheafAdjunctionContinuous
  签名: :
  定义体: Adjunction.ofIsRightAdjoint (G.sheafPushforwardContinuous A J K)

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, G.sheafPushforwardContinuous, ofIsRightAdjoint, sheafPushforwardContinuous
-/
def sheafAdjunctionContinuous :
    G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K :=
  Adjunction.ofIsRightAdjoint (G.sheafPushforwardContinuous A J K)

end

namespace sheafPullbackConstruction

variable [forall (F : Cᵒᵖ ⥤ A), G.op.HasLeftKanExtension F]

/--
Definition of `sheafPullback` / `sheafPullback` 的定义

English:
definition sheafPullback
  signature: [HasWeakSheafify K A]
  body: sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A

中文:
定义 sheafPullback
  签名: [HasWeakSheafify K A]
  定义体: sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A

Depends on / 依赖: G.op.lan, presheafToSheaf, sheafToPresheaf
-/
def sheafPullback [HasWeakSheafify K A] : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A

/--
Definition of `sheafAdjunctionContinuous` / `sheafAdjunctionContinuous` 的定义

English:
definition sheafAdjunctionContinuous
  signature: [HasWeakSheafify K A]
  body: ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

中文:
定义 sheafAdjunctionContinuous
  签名: [HasWeakSheafify K A]
  定义体: ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.id, G.op.lanAdjunction, Iso.refl, fullyFaithfulSheafToPresheaf, lanAdjunction, restrictFullyFaithful, sheafificationAdjunction
-/
def sheafAdjunctionContinuous [HasWeakSheafify K A] :
    sheafPullback G A J K ⊣ G.sheafPushforwardContinuous A J K :=
  ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: K A] :
  body: (sheafAdjunctionContinuous G A J K).isRightAdjoint

中文:
实例 [HasWeakSheafify
  签名: K A] :
  定义体: (sheafAdjunctionContinuous G A J K).isRightAdjoint

Depends on / 依赖: isRightAdjoint, sheafAdjunctionContinuous
-/
instance [HasWeakSheafify K A] :
    (G.sheafPushforwardContinuous A J K).IsRightAdjoint :=
  (sheafAdjunctionContinuous G A J K).isRightAdjoint

/--
Definition of `sheafPullbackIso` / `sheafPullbackIso` 的定义

English:
definition sheafPullbackIso
  signature: [HasWeakSheafify K A]
  body: Adjunction.leftAdjointUniq (Functor.sheafAdjunctionContinuous G A J K)
    (sheafAdjunctionContinuous G A J K)

中文:
定义 sheafPullbackIso
  签名: [HasWeakSheafify K A]
  定义体: Adjunction.leftAdjointUniq (Functor.sheafAdjunctionContinuous G A J K)
    (sheafAdjunctionContinuous G A J K)

Depends on / 依赖: Adjunction, Adjunction.leftAdjointUniq, Functor, Functor.sheafAdjunctionContinuous, leftAdjointUniq, sheafAdjunctionContinuous
-/
def sheafPullbackIso [HasWeakSheafify K A] :
    Functor.sheafPullback G A J K ≅ sheafPullback G A J K :=
  Adjunction.leftAdjointUniq (Functor.sheafAdjunctionContinuous G A J K)
    (sheafAdjunctionContinuous G A J K)

variable [RepresentablyFlat G] [HasSheafify K A] [HasSheafify J A]
  [PreservesFiniteLimits (G.op.lan : (_ ⥤ _ ⥤ A))]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (sheafPullback G A J K)
  body: by
  have : PreservesFiniteLimits (G.op.lan ⋙ presheafToSheaf K A) :=
    comp_preservesFiniteLimits _ _
  apply comp_preservesFiniteLimits

中文:
实例 :
  签名: PreservesFiniteLimits (sheafPullback G A J K)
  定义体: by
  have : PreservesFiniteLimits (G.op.lan ⋙ presheafToSheaf K A) :=
    comp_preservesFiniteLimits _ _
  apply comp_preservesFiniteLimits

Depends on / 依赖: G.op.lan, PreservesFiniteLimits, comp_preservesFiniteLimits, presheafToSheaf
-/
instance : PreservesFiniteLimits (sheafPullback G A J K) := by
  have : PreservesFiniteLimits (G.op.lan ⋙ presheafToSheaf K A) :=
    comp_preservesFiniteLimits _ _
  apply comp_preservesFiniteLimits

/--
Instance `preservesFiniteLimits` / 实例 `preservesFiniteLimits`

English:
instance preservesFiniteLimits
  signature: : PreservesFiniteLimits (Functor.sheafPullback G A J K)
  body: preservesFiniteLimits_of_natIso (sheafPullbackIso G A J K).symm

中文:
实例 preservesFiniteLimits
  签名: : PreservesFiniteLimits (Functor.sheafPullback G A J K)
  定义体: preservesFiniteLimits_of_natIso (sheafPullbackIso G A J K).symm

Depends on / 依赖: preservesFiniteLimits_of_natIso, sheafPullbackIso
-/
instance preservesFiniteLimits : PreservesFiniteLimits (Functor.sheafPullback G A J K) :=
  preservesFiniteLimits_of_natIso (sheafPullbackIso G A J K).symm

end sheafPullbackConstruction

end GeneralUniverses

namespace SmallCategories

variable {C : Type v₁} [SmallCategory C] {D : Type v₁} [SmallCategory D] (G : C ⥤ D)
  (A : Type u₁) [Category.{v₁} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

-- The favourable assumptions under which we have sheafification
variable {FA : A -> A -> Type*} {CA : A -> Type v₁} [forall X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{v₁} A FA] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]
  [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
  [Functor.IsContinuous.{v₁} G J K]

example : (G.sheafPushforwardContinuous A J K).IsRightAdjoint := inferInstance

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RepresentablyFlat
  signature: G] : PreservesFiniteLimits (G.sheafPullback A J K)
  body: by
  apply sheafPullbackConstruction.preservesFiniteLimits

中文:
实例 [RepresentablyFlat
  签名: G] : PreservesFiniteLimits (G.sheafPullback A J K)
  定义体: by
  apply sheafPullbackConstruction.preservesFiniteLimits

Depends on / 依赖: preservesFiniteLimits, sheafPullbackConstruction, sheafPullbackConstruction.preservesFiniteLimits
-/
instance [RepresentablyFlat G] : PreservesFiniteLimits (G.sheafPullback A J K) := by
  apply sheafPullbackConstruction.preservesFiniteLimits

end SmallCategories

end CategoryTheory.Functor
