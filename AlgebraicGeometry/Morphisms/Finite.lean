/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.RingTheory.Finiteness.Prod

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

Also see `AlgebraicGeometry.IsFinite.finite_preimage_singleton` in
`Mathlib/AlgebraicGeometry/Fiber.lean` for the fact that finite morphisms have finite fibers.

-/

public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
/--
Definition of `IsFinite` / `IsFinite` 的定义

English:
class IsFinite
  parameters: {X Y : Scheme} (f : X ⟶ Y)
  extends: IsAffineHom f
  axioms and operations (1):
    - finite_app((f) (U : Y.Opens) (hU : IsAffineOpen U)) : (f.app U).hom.Finite

中文:
类 IsFinite
  参数: {X Y : Scheme} (f : X ⟶ Y)
  继承: IsAffineHom f
  公理与运算 (1 个):
    - finite_app((f) (U : Y.Opens) (hU : IsAffineOpen U)) : (f.app U).hom.Finite

Depends on / 依赖: IsFinite, IsFinite.finite_app, finite_app
-/
class IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  finite_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite

alias Scheme.Hom.finite_app := IsFinite.finite_app

namespace IsFinite

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAffineProperty @IsFinite
  body: by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

中文:
实例 :
  签名: HasAffine命题erty @IsFinite
  定义体: by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

Depends on / 依赖: Finite, HasAffineProperty, HasAffineProperty.affineAnd_iff, IsFinite, RingHom, RingHom.Finite, RingHom.finite_localizationPreserves.away, RingHom.finite_ofLocalizationSpan, RingHom.finite_respectsIso, affineAnd, affineAnd_iff, finite_localizationPreserves, finite_ofLocalizationSpan, finite_respectsIso, isFinite_iff
-/
instance : HasAffineProperty @IsFinite
    (fun X _ f _ => IsAffine X ∧ RingHom.Finite (f.appTop).hom) := by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderComposition @IsFinite
  body: HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

中文:
实例 :
  签名: IsStableUnderComposition @IsFinite
  定义体: HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_isStableUnderComposition, RingHom, RingHom.finite_stableUnderComposition, affineAnd_isStableUnderComposition, finite_stableUnderComposition
-/
instance : IsStableUnderComposition @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @IsFinite
  body: HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

中文:
实例 :
  签名: IsStableUnderBaseChange @IsFinite
  定义体: HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_isStableUnderBaseChange, RingHom, RingHom.finite_isStableUnderBaseChange, RingHom.finite_respectsIso, affineAnd_isStableUnderBaseChange, finite_isStableUnderBaseChange, finite_respectsIso
-/
instance : IsStableUnderBaseChange @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContainsIdentities @IsFinite
  body: HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities

中文:
实例 :
  签名: ContainsIdentities @IsFinite
  定义体: HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_containsIdentities, RingHom, RingHom.finite_containsIdentities, RingHom.finite_respectsIso, affineAnd_containsIdentities, finite_containsIdentities, finite_respectsIso
-/
instance : ContainsIdentities @IsFinite :=
  HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative @IsFinite

中文:
实例 :
  签名: IsMultiplicative @IsFinite
-/
instance : IsMultiplicative @IsFinite where

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `SpecMap_iff` / 引理 `SpecMap_iff`

English:
lemma SpecMap_iff
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]; rw [and_iff_right (by infer_instance)]; rw [RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

中文:
引理 SpecMap_iff
  条件: {R S : CommRingCat.{u}} (f : R ⟶ S)
  证明: by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]; rw [and_iff_right (by infer_instance)]; rw [RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsFinite, RingHom, RingHom.finite_respectsIso.arrow_mk_iso_iff, and_iff_right, arrow_mk_iso_iff, finite_respectsIso, iff_of_isAffine, infer_instance
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsFinite (Spec.map f) ↔ f.hom.Finite := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]; rw [and_iff_right (by infer_instance)]; rw [RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

set_option backward.isDefEq.respectTransparency.types false in
instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g ‹IsFinite f› ‹IsFinite g›

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite g] : IsFinite (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite f] : IsFinite (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [IsFinite f] : IsFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iff_isIntegralHom_and_locallyOfFiniteType` / 引理 `iff_isIntegralHom_and_locallyOfFiniteType`

English:
lemma iff_isIntegralHom_and_locallyOfFiniteType
  proof: by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, for

中文:
引理 iff_isIntegralHom_and_locallyOfFiniteType
  证明: by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, for

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsAffine, IsFinite, IsIntegralHom, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, LocallyOfFiniteType, RingHom, RingHom.finite_iff_isIntegral_and_finiteType, Y.affineCover, affineCover, and_assoc, and_congr_right, finite_iff_isIntegral_and_finiteType, forall_and, iff_of_isAffine, iff_of_openCover, simp_rw
-/
lemma iff_isIntegralHom_and_locallyOfFiniteType :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]; rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)]; rw [RingHom.finite_iff_isIntegral_and_finiteType]; rw [← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ =>
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).symm

/--
lemma `eq_inf` / 引理 `eq_inf`

English:
lemma eq_inf
  proof: by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _

中文:
引理 eq_inf
  证明: by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _

Depends on / 依赖: IsFinite, IsFinite.iff_isIntegralHom_and_locallyOfFiniteType, iff_isIntegralHom_and_locallyOfFiniteType
-/
lemma eq_inf :
    @IsFinite = (@IsIntegralHom ⊓ @LocallyOfFiniteType : MorphismProperty Scheme) := by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _

instance (priority := 900) [IsFinite f] : IsIntegralHom f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).1

instance (priority := 900) [IsFinite f] : LocallyOfFiniteType f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).2

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono` / 引理 `_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`

English:
lemma _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
  proof: by
  wlog hY : IsAffine Y
  · rw [← monomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
  

中文:
引理 _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
  证明: by
  wlog hY : IsAffine Y
  · rw [← monomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
  

Depends on / 依赖: Finset, Finset.card_compl, HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsAffine, IsClosedImmersion, IsFinite, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, RingHom, RingHom.surjective_iff_epi_and_finite, Y.affineCover, affineCover, and_comm, card_compl, forall_and, hasDimensionLT_face, hasDimensionLT_iSup_iff, horn_eq_iSup, iff_of_isAffine
-/
lemma _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  wlog hY : IsAffine Y
  · rw [← monomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]; rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]; rw [RingHom.surjective_iff_epi_and_finite]; rw [@and_comm (Epi _)]; rw [← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ =>
    Iff.trans ?_ (arrow_mk_iso_iff (monomorphisms _) (arrowIsoSpecΓOfIsAffine f).symm)
  trans Mono (f.app ⊤).op
  · exact ⟨fun h => inferInstance, fun h => show Epi (f.app ⊤).op.unop by infer_instance⟩
  exact (Functor.mono_map_iff_mono Scheme.Spec _).symm

/--
lemma `_root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono` / 引理 `_root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono`

English:
lemma _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
  proof: by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _

中文:
引理 _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
  证明: by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _

Depends on / 依赖: IsClosedImmersion, IsClosedImmersion.iff_isFinite_and_mono, iff_isFinite_and_mono
-/
lemma _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono :
    @IsClosedImmersion = (@IsFinite ⊓ monomorphisms Scheme : MorphismProperty _) := by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _

instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsFinite f :=
  ((IsClosedImmersion.iff_isFinite_and_mono f).mp ‹_›).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsFinite @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsFinite _)

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @IsFinite @IsSeparated
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsFinite _)

Depends on / 依赖: IsFinite, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsFinite @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsFinite _)

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsFinite f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
lemma `comp_iff` / 引理 `comp_iff`

English:
lemma comp_iff
  given: {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g]
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 comp_iff
  条件: {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g]
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g] :
    IsFinite (f ≫ g) ↔ IsFinite f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsFinite f] [IsFinite g] :
    IsFinite (Limits.coprod.desc f g) := by
  refine HasAffineProperty.coprodDesc_affineAnd inferInstance RingHom.finite_respectsIso
    ?_ _ _ ‹_› ‹_›
  intros R S T _ _ _ f g _ _
  algebraize [f, g]
  refine RingHom.finite_algebraMap.mpr inferInstance

end IsFinite

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Scheme.Hom.finite_appTop` / 引理 `Scheme.Hom.finite_appTop`

English:
lemma Scheme.Hom.finite_appTop
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsFinite f]
  proof: (HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2

中文:
引理 Scheme.Hom.finite_appTop
  条件: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsFinite f]
  证明: (HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsFinite, iff_of_isAffine
-/
lemma Scheme.Hom.finite_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsFinite f] :
    f.appTop.hom.Finite :=
  (HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` / 引理 `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`

English:
lemma isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
  proof: by
  wlog hY : exists S, Y = Spec S generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.injecti

中文:
引理 isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
  证明: by
  wlog hY : exists S, Y = Spec S generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.injecti

Depends on / 依赖: IsFinite, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, JacobsonSpace, JacobsonSpace.of_isOpenEmbedding, LocallyOfFiniteType, Y.affineCover, Y.affineCover.f, Y.affineCover.pullback, affineCover, forall_congr, generalizing, iff_of_openCover, injective, isOpenEmbedding, isOpenEmbedding.injective.subsingleton, isReduced_of_isOpenImmersion, of_isOpenEmbedding, subsingleton
-/
lemma isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Subsingleton X] [IsReduced X] [JacobsonSpace Y] :
    IsFinite f ↔ LocallyOfFiniteType f := by
  wlog hY : exists S, Y = Spec S generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.injective.subsingleton
    have inst (i) := isReduced_of_isOpenImmersion ((Y.affineCover.pullback₁ f).f i)
    have inst (i) := JacobsonSpace.of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    exact forall_congr' fun i => this ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  wlog hX : exists R, X = Spec R generalizing X
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) X.isoSpec.inv,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) X.isoSpec.inv]
    have inst := X.isoSpec.inv.isOpenEmbedding.injective.subsingleton
    refine this ⟨_, rfl⟩
  cases isEmpty_or_nonempty X
  · exact ⟨inferInstance, inferInstance⟩
  have : IrreducibleSpace X := ⟨‹_›⟩
  obtain ⟨R, rfl⟩ := hX
  have : IsDomain R := (affine_isIntegral_iff R).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [IsFinite.SpecMap_iff]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := (PrimeSpectrum.t1Space_iff_isField (R := R)).mp (show T1Space (Spec R) by infer_instance)
  let := this.toField
  let := φ.hom.toAlgebra
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  change Module.Finite _ _ ↔ Algebra.FiniteType _ _
  exact ⟨fun _ => inferInstance, fun _ => finite_of_finite_type_of_isJacobsonRing _ _⟩

@[stacks 01TB "(1) => (3)"]
/--
lemma `Scheme.Hom.closePoints_subset_preimage_closedPoints` / 引理 `Scheme.Hom.closePoints_subset_preimage_closedPoints`

English:
lemma Scheme.Hom.closePoints_subset_preimage_closedPoints
  proof: by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClos

中文:
引理 Scheme.Hom.closePoints_subset_preimage_closedPoints
  证明: by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClos

Depends on / 依赖: Scheme, Scheme.range_fromSpecResidueField, Set.range_comp, X.fromSpecResidueField, fromSpecResidueField, isClosedMap, isClosedMap.isClosed_range, isClosed_range, isClosed_singleton_iff_isClosedImmersion, isClosed_singleton_iff_isClosedImmersion.mp, isFinite_iff_locallyOfFiniteType_of_jacobsonSpace, range_comp, range_fromSpecResidueField
-/
lemma Scheme.Hom.closePoints_subset_preimage_closedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [JacobsonSpace Y] [LocallyOfFiniteType f] :
    closedPoints X subseteq f ⁻¹' closedPoints Y := by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClosedMap.isClosed_range

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01TB "(1) => (2)"]
/--
lemma `isClosed_singleton_iff_locallyOfFiniteType` / 引理 `isClosed_singleton_iff_locallyOfFiniteType`

English:
lemma isClosed_singleton_iff_locallyOfFiniteType
  given: {X : Scheme.{u}} [JacobsonSpace X] {x : X}
  proof: by
  constructor
  · exact fun H => have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

中文:
引理 isClosed_singleton_iff_locallyOfFiniteType
  条件: {X : Scheme.{u}} [JacobsonSpace X] {x : X}
  证明: by
  constructor
  · exact fun H => have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

Depends on / 依赖: IsLocalRing, IsLocalRing.isClosed_singleton_closedPoint, X.fromSpecResidueField, closePoints_subset_preimage_closedPoints, fromSpecResidueField, isClosed_singleton_closedPoint, isClosed_singleton_iff_isClosedImmersion, isClosed_singleton_iff_isClosedImmersion.mp
-/
lemma isClosed_singleton_iff_locallyOfFiniteType {X : Scheme.{u}} [JacobsonSpace X] {x : X} :
    IsClosed {x} ↔ LocallyOfFiniteType (X.fromSpecResidueField x) := by
  constructor
  · exact fun H => have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

end AlgebraicGeometry
