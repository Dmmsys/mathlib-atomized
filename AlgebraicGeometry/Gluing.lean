/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.
Also see the section about "locally directed" gluing,
which is a special case where the conditions are easier to check.

## Main definitions

* `AlgebraicGeometry.Scheme.GlueData`: A structure containing the family of gluing data.
* `AlgebraicGeometry.Scheme.GlueData.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `AlgebraicGeometry.Scheme.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.isoCarrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `AlgebraicGeometry.Scheme.OpenCover.gluedCover`: The glue data associated with an open cover.
* `AlgebraicGeometry.Scheme.OpenCover.fromGlued`: The canonical morphism
  `𝒰.gluedCover.glued ⟶ X`. This has an `is_iso` instance.
* `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.Scheme.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `AlgebraicGeometry.Scheme.GlueData.ι_eq_iff` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `AlgebraicGeometry.Scheme.GlueData.isOpen_iff` : A subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` where we
glue presheafed spaces, sheafed spaces, and locally ringed spaces.

-/

@[expose] public section


noncomputable section

universe v u

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: extends CategoryTheory.GlueData Scheme
  extends: CategoryTheory.GlueData Scheme
  axioms and operations (1):
    - f_open : forall i j, IsOpenImmersion (f i j)

中文:
结构 粘合数据
  参数: extends 范畴论.粘合数据 概形
  继承: 范畴论.粘合数据 概形
  公理与运算 (1 个):
    - f_open : 对任意 i j, 是开浸入 (f i j)
-/
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : forall i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/--
Definition of `toLocallyRingedSpaceGlueData` / `toLocallyRingedSpaceGlueData` 的定义

English:
abbreviation toLocallyRingedSpaceGlueData
  signature: : LocallyRingedSpace.GlueData
  body: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }

中文:
缩写 toLocallyRingedSpaceGlueData
  签名: : LocallyRinged空间.粘合数据
  定义体: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }

Depends on / 依赖: D.f_open, f_open, forgetToLocallyRingedSpace, mapGlueData, toGlueData
-/
abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }

instance (i j : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.f i j) := by
  apply GlueData.f_open

instance (i j : 𝖣.J) :
    SheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toGlueData.f i j) := by
  apply GlueData.f_open

instance (i j : 𝖣.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.f
        i j) := by
  apply GlueData.f_open

instance (i : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.ι i) := by
  apply LocallyRingedSpace.GlueData.ι_isOpenImmersion

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `gluedScheme` / `gluedScheme` 的定义

English:
definition gluedScheme
  signature: : Scheme
  body: by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨j, z, hz⟩ := (D.U i).affineCover.exists_eq y
  refine ⟨_, ((D.U i).affineCover.f j).toLRSHom ≫
  

中文:
定义 gluedScheme
  签名: : 概形
  定义体: by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨j, z, hz⟩ := (D.U i).affineCover.exists_eq y
  refine ⟨_, ((D.U i).affineCover.f j).toLRSHom ≫
  

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_comp, D.toLocallyRingedSpaceGlueData, D.toLocallyRingedSpaceGlueData.toGlueData, D.toLocallyRingedSpaceGlueData.toGlueData.glued, IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.scheme, LocallyRingedSpace.comp_toHom, PresheafedSpace, PresheafedSpace.comp_base, Set.mem_image_of_me, Set.range_comp, TopCat, TopCat.hom_comp, affineCover, affineCover.exists_eq, affineCover.f, coe_comp, comp_base
-/
def gluedScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨j, z, hz⟩ := (D.U i).affineCover.exists_eq y
  refine ⟨_, ((D.U i).affineCover.f j).toLRSHom ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ?_⟩
  constructor
  · simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    exact Set.mem_image_of_mem _ ⟨z, hz⟩
  · infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimit 𝖣.diagram.multispan forgetToLocallyRingedSpace
  body: createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)

中文:
实例 :
  签名: 创造余极限 𝖣.diagram.multispan forgetToLocallyRingedSpace
  定义体: createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)

Depends on / 依赖: D.gluedScheme, HasColimit, HasColimit.isoOfNatIso, createsColimitOfFullyFaithfulOfIso, diagramIso, forgetToLocallyRingedSpace, gluedScheme, isoOfNatIso
-/
instance : CreatesColimit 𝖣.diagram.multispan forgetToLocallyRingedSpace :=
  createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit (𝖣.diagram.multispan) forgetToTop
  body: inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

中文:
实例 :
  签名: 保持余极限 (𝖣.diagram.multispan) forgetToTop
  定义体: inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

Depends on / 依赖: CommRingCat, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PreservesColimit, SheafedSpace, SheafedSpace.forget, diagram, forget, forgetToLocallyRingedSpace, forgetToSheafedSpace, multispan
-/
instance : PreservesColimit (𝖣.diagram.multispan) forgetToTop :=
  inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit (𝖣.diagram.multispan) forget
  body: inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToTop ⋙ CategoryTheory.forget _))

中文:
实例 :
  签名: 保持余极限 (𝖣.diagram.multispan) forget
  定义体: inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToTop ⋙ CategoryTheory.forget _))

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, PreservesColimit, diagram, forget, forgetToTop, multispan
-/
instance : PreservesColimit (𝖣.diagram.multispan) forget :=
  inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToTop ⋙ CategoryTheory.forget _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMulticoequalizer 𝖣.diagram
  body: hasColimit_of_created _ forgetToLocallyRingedSpace

中文:
实例 :
  签名: HasMulticoequalizer 𝖣.diagram
  定义体: hasColimit_of_created _ forgetToLocallyRingedSpace

Depends on / 依赖: forgetToLocallyRingedSpace, hasColimit_of_created
-/
instance : HasMulticoequalizer 𝖣.diagram :=
  hasColimit_of_created _ forgetToLocallyRingedSpace

/--
Definition of `glued` / `glued` 的定义

English:
abbreviation glued
  signature: : Scheme
  body: 𝖣.glued

中文:
缩写 glued
  签名: : 概形
  定义体: 𝖣.glued
-/
abbrev glued : Scheme :=
  𝖣.glued

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: (i : D.J)
  body: 𝖣.ι i

中文:
缩写 ι
  签名: (i : D.J)
  定义体: 𝖣.ι i
-/
abbrev ι (i : D.J) : D.U i ⟶ D.glued :=
  𝖣.ι i

/--
Definition of `isoLocallyRingedSpace` / `isoLocallyRingedSpace` 的定义

English:
abbreviation isoLocallyRingedSpace
  signature: :
  body: 𝖣.gluedIso forgetToLocallyRingedSpace

中文:
缩写 isoLocallyRingedSpace
  签名: :
  定义体: 𝖣.gluedIso forgetToLocallyRingedSpace

Depends on / 依赖: forgetToLocallyRingedSpace, gluedIso
-/
abbrev isoLocallyRingedSpace :
    D.glued.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToLocallyRingedSpace

/--
theorem `ι_isoLocallyRingedSpace_inv` / 定理 `ι_isoLocallyRingedSpace_inv`

English:
theorem ι_isoLocallyRingedSpace_inv
  given: (i : D.J)
  proof: 𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i

中文:
定理 ι_isoLocallyRingedSpace_inv
  条件: (i : D.J)
  证明: 𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i

Depends on / 依赖: forgetToLocallyRingedSpace
-/
theorem ι_isoLocallyRingedSpace_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i ≫
      D.isoLocallyRingedSpace.inv = (𝖣.ι i).toLRSHom :=
  𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ι_isOpenImmersion` / 实例 `ι_isOpenImmersion`

English:
instance ι_isOpenImmersion
  signature: (i : D.J)
  body: by
  rw [IsOpenImmersion]; rw [← D.ι_isoLocallyRingedSpace_inv]; infer_instance

中文:
实例 ι_isOpenImmersion
  签名: (i : D.J)
  定义体: by
  rw [IsOpenImmersion]; rw [← D.ι_isoLocallyRingedSpace_inv]; infer_instance

Depends on / 依赖: IsOpenImmersion, infer_instance
-/
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [IsOpenImmersion]; rw [← D.ι_isoLocallyRingedSpace_inv]; infer_instance

/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  given: (x : 𝖣.glued.carrier)
  proof: 𝖣.ι_jointly_surjective forget x

中文:
定理 ι_jointly_surjective
  条件: (x : 𝖣.glued.carrier)
  证明: 𝖣.ι_jointly_surjective forget x

Depends on / 依赖: forget
-/
theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    exists (i : D.J) (y : (D.U i).carrier), D.ι i y = x :=
  𝖣.ι_jointly_surjective forget x

/-- Promoted to higher priority to short circuit simplifier. -/
@[simp (high), reassoc]
/--
theorem `glue_condition` / 定理 `glue_condition`

English:
theorem glue_condition
  given: (i j : D.J)
  statement: D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
  proof: 𝖣.glue_condition i j

中文:
定理 glue_condition
  条件: (i j : D.J)
  结论: D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
  证明: 𝖣.glue_condition i j

Depends on / 依赖: glue_condition
-/
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  𝖣.glue_condition i j

/--
Definition of `vPullbackCone` / `vPullbackCone` 的定义

English:
definition vPullbackCone
  signature: (i j : D.J)
  body: PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

中文:
定义 vPullbackCone
  签名: (i j : D.J)
  定义体: PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

Depends on / 依赖: PullbackCone, PullbackCone.mk
-/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

/--
Definition of `vPullbackConeIsLimit` / `vPullbackConeIsLimit` 的定义

English:
definition vPullbackConeIsLimit
  signature: (i j : D.J)
  body: 𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)

local notation "D_" => TopCat.GlueData.toGlueData
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

中文:
定义 vPullbackConeIsLimit
  签名: (i j : D.J)
  定义体: 𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)

local notation "D_" => TopCat.GlueData.toGlueData
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

Depends on / 依赖: D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit, forgetToLocallyRingedSpace, toLocallyRingedSpaceGlueData, vPullbackConeIsLimit, vPullbackConeIsLimitOfMap
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (D.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)

local notation "D_" => TopCat.GlueData.toGlueData
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isoCarrier` / `isoCarrier` 的定义

English:
definition isoCarrier
  signature: :
  body: by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  refine LocallyRingedSpace.forgetToSheafedSpace.mapIso ?_ ≪≫
    LocallyRingedSp

中文:
定义 isoCarrier
  签名: :
  定义体: by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  refine LocallyRingedSpace.forgetToSheafedSpace.mapIso ?_ ≪≫
    LocallyRingedSp

Depends on / 依赖: GlueData, GlueData.gluedIso, LocallyRingedSpace, LocallyRingedSpace.GlueData.isoSheafedSpace, LocallyRingedSpace.forgetToSheafedSpace.mapIso, PresheafedSpace, PresheafedSpace.forget, Scheme, Scheme.GlueData.isoLocallyRingedSpace, SheafedSpace, SheafedSpace.GlueData.isoPresheafedSpace, SheafedSpace.forgetToPresheafedSpace.mapIso, forget, forgetToPresheafedSpace, forgetToSheafedSpace, gluedIso, isoLocallyRingedSpace, isoPresheafedSpace, isoSheafedSpace, mapIso
-/
def isoCarrier :
    D.glued.carrier ≅ (D_).glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  refine LocallyRingedSpace.forgetToSheafedSpace.mapIso ?_ ≪≫
    LocallyRingedSpace.GlueData.isoSheafedSpace _
  exact Scheme.GlueData.isoLocallyRingedSpace _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ι_isoCarrier_inv` / 定理 `ι_isoCarrier_inv`

English:
theorem ι_isoCarrier_inv
  given: (i : D.J)
  proof: by
  delta isoCarrier
  rw [Iso.trans_inv]; rw [GlueData.ι_gluedIso_inv_assoc]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [SheafedSpace.forgetToPresheafedSpace_map]; rw [PresheafedSpace.forget_map]; rw [PresheafedSpace.forget_map]; rw [← PresheafedS

中文:
定理 ι_isoCarrier_inv
  条件: (i : D.J)
  证明: by
  delta isoCarrier
  rw [Iso.trans_inv]; rw [GlueData.ι_gluedIso_inv_assoc]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [SheafedSpace.forgetToPresheafedSpace_map]; rw [PresheafedSpace.forget_map]; rw [PresheafedSpace.forget_map]; rw [← PresheafedS

Depends on / 依赖: Category, Category.assoc, D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData, Functor, Functor.mapIso_inv, GlueData, InducedCa, Iso.trans_inv, PresheafedSpace, PresheafedSpace.comp_base, PresheafedSpace.forget_map, SheafedSpace, SheafedSpace.forgetToPresheafedSpace_map, comp_base, forgetToPresheafedSpace_map, forget_map, isoCarrier, mapIso_inv, toLocallyRingedSpaceGlueData, toSheafedSpaceGlueData
-/
theorem ι_isoCarrier_inv (i : D.J) :
    (D_).ι i ≫ D.isoCarrier.inv = (D.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv]; rw [GlueData.ι_gluedIso_inv_assoc]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [Functor.mapIso_inv]; rw [Iso.trans_inv]; rw [SheafedSpace.forgetToPresheafedSpace_map]; rw [PresheafedSpace.forget_map]; rw [PresheafedSpace.forget_map]; rw [← PresheafedSpace.comp_base]; rw [← Category.assoc]; rw [D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  dsimp
  rw [← Category.assoc]; rw [← PresheafedSpace.comp_base]; rw [← InducedCategory.comp_hom]; rw [D.toLocallyRingedSpaceGlueData.ι_isoSheafedSpace_inv i]; rw [← PresheafedSpace.comp_base]
  change (_ ≫ D.isoLocallyRingedSpace.inv).base = _
  rw [D.ι_isoLocallyRingedSpace_inv i]

/--
Definition of `Rel` / `Rel` 的定义

English:
definition Rel
  signature: (a b : Σ i, ((D.U i).carrier : Type _))
  body: exists x : (D.V (a.1, b.1)).carrier, D.f _ _ x = a.2 ∧ (D.t _ _ ≫ D.f _ _) x = b.2

中文:
定义 关系
  签名: (a b : Σ i, ((D.U i).carrier : 类型 _))
  定义体: exists x : (D.V (a.1, b.1)).carrier, D.f _ _ x = a.2 ∧ (D.t _ _ ≫ D.f _ _) x = b.2

Depends on / 依赖: carrier
-/
def Rel (a b : Σ i, ((D.U i).carrier : Type _)) : Prop :=
  exists x : (D.V (a.1, b.1)).carrier, D.f _ _ x = a.2 ∧ (D.t _ _ ≫ D.f _ _) x = b.2

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ι_eq_iff` / 定理 `ι_eq_iff`

English:
theorem ι_eq_iff
  given: (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier)
  proof: by
  refine Iff.trans ?_
    (TopCat.GlueData.ι_eq_iff_rel
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
      i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp _).eq_iff]; rw [← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_iso

中文:
定理 ι_eq_iff
  条件: (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier)
  证明: by
  refine Iff.trans ?_
    (TopCat.GlueData.ι_eq_iff_rel
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
      i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp _).eq_iff]; rw [← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_iso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, D.isoCarrier.inv, D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData, GlueData, Iff.trans, TopCat, TopCat.GlueData, TopCat.mono_iff_injective, before, community, comp_apply, eq_iff, github, github.com, infer_instance, isoCarrier, leanprover, mathlib4, mono_iff_injective
-/
theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_
    (TopCat.GlueData.ι_eq_iff_rel
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
      i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp _).eq_iff]; rw [← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_isoCarrier_inv]
    rfl -- `rfl` was not needed before https://github.com/leanprover-community/mathlib4/pull/13170
  · infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (U : Set D.glued.carrier)
  statement: IsOpen U ↔ forall i, IsOpen (D.ι i ⁻¹' U)
  proof: by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage]; rw [TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp]; rw [← ι_isoCarrier_inv]
  rfl

中文:
定理 isOpen_iff
  条件: (U : 集合 D.glued.carrier)
  结论: 是开集 U ↔ 对任意 i, 是开集 (D.ι i ⁻¹' U)
  证明: by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage]; rw [TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp]; rw [← ι_isoCarrier_inv]
  rfl

Depends on / 依赖: D.isoCarrier.symm, GlueData, Set.preimage_comp, TopCat, TopCat.GlueData.isOpen_iff, TopCat.homeoOfIso, forall_congr, homeoOfIso, isOpen_iff, isOpen_preimage, isoCarrier, preimage_comp
-/
theorem isOpen_iff (U : Set D.glued.carrier) : IsOpen U ↔ forall i, IsOpen (D.ι i ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage]; rw [TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp]; rw [← ι_isoCarrier_inv]
  rfl

/-- The open cover of the glued space given by the glue data. -/
@[simps -isSimp]
/--
Definition of `openCover` / `openCover` 的定义

English:
definition openCover
  signature: (D : Scheme.GlueData)
  body: D.J
  X := D.U
  f := D.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨D.ι_jointly_surjective, inferInstance⟩

中文:
定义 openCover
  签名: (D : 概形.粘合数据)
  定义体: D.J
  X := D.U
  f := D.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨D.ι_jointly_surjective, inferInstance⟩
-/
def openCover (D : Scheme.GlueData) : OpenCover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨D.ι_jointly_surjective, inferInstance⟩

end GlueData

namespace Cover

variable {X : Scheme.{u}} (𝒰 : OpenCover.{u} X)

/--
Definition of `gluedCoverT'` / `gluedCoverT'` 的定义

English:
definition gluedCoverT'
  signature: (x y z : 𝒰.I₀)
  body: by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

中文:
定义 gluedCoverT'
  签名: (x y z : 𝒰.I₀)
  定义体: by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

Depends on / 依赖: condition, pullback, pullback.condition, pullback.map, pullbackRightPullbackFstIso, pullbackSymmetry
-/
def gluedCoverT' (x y z : 𝒰.I₀) :
    pullback (pullback.fst (𝒰.f x) (𝒰.f y)) (pullback.fst (𝒰.f x) (𝒰.f z)) ⟶
      pullback (pullback.fst (𝒰.f y) (𝒰.f z)) (pullback.fst (𝒰.f y) (𝒰.f x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `gluedCoverT'_fst_fst` / 定理 `gluedCoverT'_fst_fst`

English:
theorem gluedCoverT'_fst_fst
  given: (x y z : 𝒰.I₀)
  proof: by
  delta gluedCoverT'; simp

中文:
定理 gluedCoverT'_fst_fst
  条件: (x y z : 𝒰.I₀)
  证明: by
  delta gluedCoverT'; simp
-/
theorem gluedCoverT'_fst_fst (x y z : 𝒰.I₀) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `gluedCoverT'_fst_snd` / 定理 `gluedCoverT'_fst_snd`

English:
theorem gluedCoverT'_fst_snd
  given: (x y z : 𝒰.I₀)
  proof: by
  delta gluedCoverT'; simp

中文:
定理 gluedCoverT'_fst_snd
  条件: (x y z : 𝒰.I₀)
  证明: by
  delta gluedCoverT'; simp
-/
theorem gluedCoverT'_fst_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `gluedCoverT'_snd_fst` / 定理 `gluedCoverT'_snd_fst`

English:
theorem gluedCoverT'_snd_fst
  given: (x y z : 𝒰.I₀)
  proof: by
  delta gluedCoverT'; simp

中文:
定理 gluedCoverT'_snd_fst
  条件: (x y z : 𝒰.I₀)
  证明: by
  delta gluedCoverT'; simp
-/
theorem gluedCoverT'_snd_fst (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `gluedCoverT'_snd_snd` / 定理 `gluedCoverT'_snd_snd`

English:
theorem gluedCoverT'_snd_snd
  given: (x y z : 𝒰.I₀)
  proof: by
  delta gluedCoverT'; simp

中文:
定理 gluedCoverT'_snd_snd
  条件: (x y z : 𝒰.I₀)
  证明: by
  delta gluedCoverT'; simp
-/
theorem gluedCoverT'_snd_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp

/--
theorem `glued_cover_cocycle_fst` / 定理 `glued_cover_cocycle_fst`

English:
theorem glued_cover_cocycle_fst
  given: (x y z : 𝒰.I₀)
  proof: by
  apply pullback.hom_ext <;> simp

中文:
定理 glued_cover_cocycle_fst
  条件: (x y z : 𝒰.I₀)
  证明: by
  apply pullback.hom_ext <;> simp

Depends on / 依赖: hom_ext, pullback, pullback.hom_ext
-/
theorem glued_cover_cocycle_fst (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

/--
theorem `glued_cover_cocycle_snd` / 定理 `glued_cover_cocycle_snd`

English:
theorem glued_cover_cocycle_snd
  given: (x y z : 𝒰.I₀)
  proof: by
  apply pullback.hom_ext <;> simp [pullback.condition]

中文:
定理 glued_cover_cocycle_snd
  条件: (x y z : 𝒰.I₀)
  证明: by
  apply pullback.hom_ext <;> simp [pullback.condition]

Depends on / 依赖: condition, hom_ext, pullback, pullback.condition, pullback.hom_ext
-/
theorem glued_cover_cocycle_snd (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

/--
theorem `glued_cover_cocycle` / 定理 `glued_cover_cocycle`

English:
theorem glued_cover_cocycle
  given: (x y z : 𝒰.I₀)
  proof: by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

中文:
定理 glued_cover_cocycle
  条件: (x y z : 𝒰.I₀)
  证明: by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

Depends on / 依赖: Category, Category.assoc, Category.id_comp, glued_cover_cocycle_fst, glued_cover_cocycle_snd, hom_ext, id_comp, pullback, pullback.hom_ext, simp_rw
-/
theorem glued_cover_cocycle (x y z : 𝒰.I₀) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.gluedCover.glued ⟶ X` is provided by `𝒰.fromGlued`. -/
@[simps]
/--
Definition of `gluedCover` / `gluedCover` 的定义

English:
definition gluedCover
  signature: : Scheme.GlueData.{u} where
  body: 𝒰.I₀
  U := 𝒰.X
  V := fun ⟨x, y⟩ => pullback (𝒰.f x) (𝒰.f y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have bee

中文:
定义 gluedCover
  签名: : 概形.粘合数据.{u} where
  定义体: 𝒰.I₀
  U := 𝒰.X
  V := fun ⟨x, y⟩ => pullback (𝒰.f x) (𝒰.f y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have bee
-/
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U := 𝒰.X
  V := fun ⟨x, y⟩ => pullback (𝒰.f x) (𝒰.f y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fromGlued` / `fromGlued` 的定义

English:
definition fromGlued
  signature: : 𝒰.gluedCover.glued ⟶ X
  body: by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.f x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition

@[simp, reassoc]

中文:
定义 fromGlued
  签名: : 𝒰.gluedCover.glued ⟶ X
  定义体: by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.f x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition

@[simp, reassoc]

Depends on / 依赖: Multicoequalizer, Multicoequalizer.desc, condition, fapply, pullback, pullback.condition, pullback.fst, pullbackSymmetry
-/
def fromGlued : 𝒰.gluedCover.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.f x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition

@[simp, reassoc]
/--
theorem `ι_fromGlued` / 定理 `ι_fromGlued`

English:
theorem ι_fromGlued
  given: (x : 𝒰.I₀)
  statement: 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x
  proof: Multicoequalizer.π_desc _ _ _ _ _

中文:
定理 ι_fromGlued
  条件: (x : 𝒰.I₀)
  结论: 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x
  证明: Multicoequalizer.π_desc _ _ _ _ _

Depends on / 依赖: Multicoequalizer
-/
theorem ι_fromGlued (x : 𝒰.I₀) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x :=
  Multicoequalizer.π_desc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fromGlued_injective` / 定理 `fromGlued_injective`

English:
theorem fromGlued_injective
  statement: Function.Injective 𝒰.fromGlued
  proof: by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply] at h
  simp_rw [← Scheme.Hom.comp_base] at h
  rw [ι_fromGlued]; rw [ι_fromGlued] at h
  l

中文:
定理 fromGlued_injective
  结论: 函数.单射 𝒰.fromGlued
  证明: by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply] at h
  simp_rw [← Scheme.Hom.comp_base] at h
  rw [ι_fromGlued]; rw [ι_fromGlued] at h
  l

Depends on / 依赖: Concre, ConcreteCategory, ConcreteCategory.comp_apply, Scheme, Scheme.Hom.comp_base, Scheme.forgetToTop, TopCat, TopCat.pullbackConeIsLimit, comp_apply, comp_base, conePointUniqueUpToIso, e.hom, forgetToTop, gluedCover, isLimitOfHasPullbackOfPreservesLimit, pullbackConeIsLimit, simp_rw
-/
theorem fromGlued_injective : Function.Injective 𝒰.fromGlued := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply] at h
  simp_rw [← Scheme.Hom.comp_base] at h
  rw [ι_fromGlued]; rw [ι_fromGlued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit Scheme.forgetToTop (𝒰.f i) (𝒰.f j))
  rw [𝒰.gluedCover.ι_eq_iff]
  use e.hom ⟨⟨x, y⟩, h⟩
  constructor
  · erw [← ConcreteCategory.comp_apply e.hom,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  · erw [← ConcreteCategory.comp_apply e.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance (x : 𝒰.gluedCover.glued.carrier) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  have := Hom.stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) x
  rw [Hom.stalkMap_comp]; rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `isOpenMap_fromGlued` / 定理 `isOpenMap_fromGlued`

English:
theorem isOpenMap_fromGlued
  statement: IsOpenMap 𝒰.fromGlued
  proof: by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.gluedCover.isOpen_iff] at hU
  use 𝒰.fromGlued '' U inter Set.range (𝒰.f (𝒰.idx x))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f (𝒰.idx x)).isOpenEmbedding.isOpenMap
    co

中文:
定理 isOpenMap_fromGlued
  结论: 是开映射 𝒰.fromGlued
  证明: by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.gluedCover.isOpen_iff] at hU
  use 𝒰.fromGlued '' U inter Set.range (𝒰.f (𝒰.idx x))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f (𝒰.idx x)).isOpenEmbedding.isOpenMap
    co

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_comp, Hom.comp_base, Set.image_preimage_eq_inter_range, Set.inter_subset_left, Set.preimage_comp, Set.preimage_image_eq, Set.range, TopCat, TopCat.hom_comp, coe_comp, comp_base, convert, fromGlued, fromGlued_injective, gluedCover, gluedCover.isOpen_iff, gluedCover_U, hom_comp, image_preimage_eq_inter_range
-/
theorem isOpenMap_fromGlued : IsOpenMap 𝒰.fromGlued := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.gluedCover.isOpen_iff] at hU
  use 𝒰.fromGlued '' U inter Set.range (𝒰.f (𝒰.idx x))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f (𝒰.idx x)).isOpenEmbedding.isOpenMap
    convert! hU (𝒰.idx x) using 1
    simp only [← ι_fromGlued, gluedCover_U, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ 𝒰.fromGlued_injective
  · exact ⟨hx, 𝒰.covers x⟩

/--
theorem `isOpenEmbedding_fromGlued` / 定理 `isOpenEmbedding_fromGlued`

English:
theorem isOpenEmbedding_fromGlued
  statement: IsOpenEmbedding 𝒰.fromGlued
  proof: .of_continuous_injective_isOpenMap (by fun_prop) 𝒰.fromGlued_injective 𝒰.isOpenMap_fromGlued

中文:
定理 isOpenEmbedding_fromGlued
  结论: 是开嵌入 𝒰.fromGlued
  证明: .of_continuous_injective_isOpenMap (by fun_prop) 𝒰.fromGlued_injective 𝒰.isOpenMap_fromGlued

Depends on / 依赖: fromGlued_injective, fun_prop, isOpenMap_fromGlued, of_continuous_injective_isOpenMap
-/
theorem isOpenEmbedding_fromGlued : IsOpenEmbedding 𝒰.fromGlued :=
  .of_continuous_injective_isOpenMap (by fun_prop) 𝒰.fromGlued_injective 𝒰.isOpenMap_fromGlued

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi 𝒰.fromGlued.base
  body: by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use 𝒰.gluedCover.ι (𝒰.idx x) y
  rw [← ConcreteCategory.comp_apply]
  rw [← 𝒰.ι_fromGlued (𝒰.idx x)] at h
  exact h

中文:
实例 :
  签名: 满态射 𝒰.fromGlued.base
  定义体: by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use 𝒰.gluedCover.ι (𝒰.idx x) y
  rw [← ConcreteCategory.comp_apply]
  rw [← 𝒰.ι_fromGlued (𝒰.idx x)] at h
  exact h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, TopCat, TopCat.epi_iff_surjective, comp_apply, covers, epi_iff_surjective, gluedCover
-/
instance : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use 𝒰.gluedCover.ι (𝒰.idx x) y
  rw [← ConcreteCategory.comp_apply]
  rw [← 𝒰.ι_fromGlued (𝒰.idx x)] at h
  exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion 𝒰.fromGlued
  body: IsOpenImmersion.of_isIso_stalkMap _ 𝒰.isOpenEmbedding_fromGlued

中文:
实例 :
  签名: 是开浸入 𝒰.fromGlued
  定义体: IsOpenImmersion.of_isIso_stalkMap _ 𝒰.isOpenEmbedding_fromGlued

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.of_isIso_stalkMap, isOpenEmbedding_fromGlued, of_isIso_stalkMap
-/
instance : IsOpenImmersion 𝒰.fromGlued :=
  IsOpenImmersion.of_isIso_stalkMap _ 𝒰.isOpenEmbedding_fromGlued

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso 𝒰.fromGlued
  body: let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F

中文:
实例 :
  签名: 是同构 𝒰.fromGlued
  定义体: let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F

Depends on / 依赖: F.map, IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PresheafedSpace, PresheafedSpace.IsOpenImmersion.to_iso, Scheme, Scheme.forgetToLocallyRingedSpace, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, forgetToLocallyRingedSpace, forgetToPresheafedSpace, forgetToSheafedSpace, fromGlued, fromGlued.toPshHom, isIso_of_reflects_iso, toPshHom, to_iso
-/
instance : IsIso 𝒰.fromGlued :=
  let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `glueMorphisms` / `glueMorphisms` 的定义

English:
definition glueMorphisms
  signature: (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : forall x, 𝒰.X x ⟶ Y)
  body: by
  refine inv 𝒰.ulift.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i => f _
  rintro ⟨i, j⟩
  dsimp
  change pullback.fst _ _ ≫ f _ = (_ ≫ _) ≫ f _
  simpa [pullbackSymmetry_hom_comp_fst] using hf _ _

中文:
定义 glueMorphisms
  签名: (𝒰 : OpenCover.{v} X) {Y : 概形.{u}} (f : 对任意 x, 𝒰.X x ⟶ Y)
  定义体: by
  refine inv 𝒰.ulift.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i => f _
  rintro ⟨i, j⟩
  dsimp
  change pullback.fst _ _ ≫ f _ = (_ ≫ _) ≫ f _
  simpa [pullbackSymmetry_hom_comp_fst] using hf _ _

Depends on / 依赖: Multicoequalizer, Multicoequalizer.desc, fapply, fromGlued, pullback, pullback.fst, pullbackSymmetry_hom_comp_fst, ulift.fromGlued
-/
def glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : forall x, 𝒰.X x ⟶ Y)
    (hf : forall x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y) :
    X ⟶ Y := by
  refine inv 𝒰.ulift.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i => f _
  rintro ⟨i, j⟩
  dsimp
  change pullback.fst _ _ ≫ f _ = (_ ≫ _) ≫ f _
  simpa [pullbackSymmetry_hom_comp_fst] using hf _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
  proof: by
  rw [← cancel_epi 𝒰.ulift.fromGlued]
  apply Multicoequalizer.hom_ext
  intro x
  rw [fromGlued]; rw [Multicoequalizer.π_desc_assoc]; rw [Multicoequalizer.π_desc_assoc]
  exact h _

中文:
定理 hom_ext
  结论: (𝒰 : OpenCover.{v} X) {Y : 概形} (f₁ f₂ : X ⟶ Y)
  证明: by
  rw [← cancel_epi 𝒰.ulift.fromGlued]
  apply Multicoequalizer.hom_ext
  intro x
  rw [fromGlued]; rw [Multicoequalizer.π_desc_assoc]; rw [Multicoequalizer.π_desc_assoc]
  exact h _

Depends on / 依赖: Multicoequalizer, Multicoequalizer.hom_ext, cancel_epi, fromGlued, hom_ext, ulift.fromGlued
-/
theorem hom_ext (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
    (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi 𝒰.ulift.fromGlued]
  apply Multicoequalizer.hom_ext
  intro x
  rw [fromGlued]; rw [Multicoequalizer.π_desc_assoc]; rw [Multicoequalizer.π_desc_assoc]
  exact h _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_glueMorphisms` / 定理 `ι_glueMorphisms`

English:
theorem ι_glueMorphisms
  statement: (𝒰 : OpenCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y)
  proof: by
  refine Cover.hom_ext (𝒰.ulift.pullback₁ (𝒰.f x)) _ _ fun i => ?_
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, ulift_X, ulift_f, PreZeroHypercover.pullback₁_f]
  simp_rw [pullback.condition_assoc, ← ulift_f, ← ι_fromGlued, Category.as

中文:
定理 ι_glueMorphisms
  结论: (𝒰 : OpenCover.{v} X) {Y : 概形} (f : 对任意 x, 𝒰.X x ⟶ Y)
  证明: by
  refine Cover.hom_ext (𝒰.ulift.pullback₁ (𝒰.f x)) _ _ fun i => ?_
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, ulift_X, ulift_f, PreZeroHypercover.pullback₁_f]
  simp_rw [pullback.condition_assoc, ← ulift_f, ← ι_fromGlued, Category.as

Depends on / 依赖: Category, Category.assoc, CategoryTheory, CategoryTheory.GlueData, Cover.hom_ext, GlueData, IsIso.hom_inv_id_assoc, PreZeroHypercover, PreZeroHypercover.pullback, Precoverage, Precoverage.ZeroHypercover.pullback, ZeroHypercover, condition_assoc, glueMorphisms, hom_ext, hom_inv_id_assoc, pullback, pullback.condition_assoc, simp_rw, ulift.pullback
-/
theorem ι_glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y)
    (hf : forall x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y)
    (x : 𝒰.I₀) : 𝒰.f x ≫ 𝒰.glueMorphisms f hf = f x := by
  refine Cover.hom_ext (𝒰.ulift.pullback₁ (𝒰.f x)) _ _ fun i => ?_
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, ulift_X, ulift_f, PreZeroHypercover.pullback₁_f]
  simp_rw [pullback.condition_assoc, ← ulift_f, ← ι_fromGlued, Category.assoc, glueMorphisms,
    IsIso.hom_inv_id_assoc, ulift_f, hf]
  simp [CategoryTheory.GlueData.ι]

end Cover

/--
lemma `hom_ext_of_forall` / 引理 `hom_ext_of_forall`

English:
lemma hom_ext_of_forall
  statement: {X Y : Scheme} (f g : X ⟶ Y)
  proof: by
  choose U hxU hU using H
  let 𝒰 : X.OpenCover := {
    I₀ := X, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  exact 𝒰.hom_ext _ _ hU

中文:
引理 hom_ext_of_对任意
  结论: {X Y : 概形} (f g : X ⟶ Y)
  证明: by
  choose U hxU hU using H
  let 𝒰 : X.OpenCover := {
    I₀ := X, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  exact 𝒰.hom_ext _ _ hU

Depends on / 依赖: OpenCover, X.OpenCover, hom_ext
-/
lemma hom_ext_of_forall {X Y : Scheme} (f g : X ⟶ Y)
    (H : forall x : X, exists U : X.Opens, x in U ∧ U.ι ≫ f = U.ι ≫ g) : f = g := by
  choose U hxU hU using H
  let 𝒰 : X.OpenCover := {
    I₀ := X, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  exact 𝒰.hom_ext _ _ hU

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to covers in subcanonical topologies
open pullback in
attribute [local simp] condition condition_assoc in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.isomorphisms Scheme).IsLocalAtTarget zariskiPrecoverage
  body: .mk_of_isStableUnderBaseChange fun {X Y} f (𝒰 : Y.OpenCover) (H : forall i, IsIso _) =>
    ⟨𝒰.glueMorphisms (fun i => inv (snd f (𝒰.f i)) ≫ fst _ _) fun i j => by
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ map (fst f (𝒰.f i) ≫ f)
      (𝒰.f j) (𝒰.f i) (𝒰.f j) (snd _ _) (𝟙 _) (𝟙

中文:
实例 :
  签名: (MorphismProperty.isomorphisms 概形).是LocalAtTarget zariskiPrecoverage
  定义体: .mk_of_isStableUnderBaseChange fun {X Y} f (𝒰 : Y.OpenCover) (H : forall i, IsIso _) =>
    ⟨𝒰.glueMorphisms (fun i => inv (snd f (𝒰.f i)) ≫ fst _ _) fun i j => by
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ map (fst f (𝒰.f i) ≫ f)
      (𝒰.f j) (𝒰.f i) (𝒰.f j) (snd _ _) (𝟙 _) (𝟙

Depends on / 依赖: Cover.hom_ext, OpenCover, Y.OpenCover, cancel_epi, glueMorphisms, hom_ext, mk_of_isStableUnderBaseChange, pullbackRightPullbackFstIso
-/
instance : (MorphismProperty.isomorphisms Scheme).IsLocalAtTarget zariskiPrecoverage :=
  .mk_of_isStableUnderBaseChange fun {X Y} f (𝒰 : Y.OpenCover) (H : forall i, IsIso _) =>
    ⟨𝒰.glueMorphisms (fun i => inv (snd f (𝒰.f i)) ≫ fst _ _) fun i j => by
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ map (fst f (𝒰.f i) ≫ f)
      (𝒰.f j) (𝒰.f i) (𝒰.f j) (snd _ _) (𝟙 _) (𝟙 _) (by simp) (by simp))]
    simp, Cover.hom_ext (𝒰.pullback₁ f) _ _ fun i => by simp, Cover.hom_ext 𝒰 _ _ fun i => by simp⟩

/-!

## Locally directed gluing

We say that a diagram of open immersions is "locally directed" if for any `V, W ⊆ U` in the diagram,
`V ∩ W` is a union of elements in the diagram. Equivalently, for every `x ∈ U` in the diagram,
the set of elements containing `x` is directed (and hence the name).

For such a diagram, we can glue them directly since the gluing conditions are always satisfied.
The intended usage is to provide the following instances:
- `∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)`
- `(F ⋙ forget).IsLocallyDirected`

and to directly use the `colimit` API.
Also see `AlgebraicGeometry.Scheme.IsLocallyDirected.openCover` for the open cover of the `colimit`.

-/
section IsLocallyDirected

open TopologicalSpace.Opens

universe w

variable {J : Type w} [Category.{v} J] (F : J ⥤ Scheme.{u})
variable [forall {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]

namespace IsLocallyDirected

/-- (Implementation detail)
The intersection `V` in the glue data associated to a locally directed diagram. -/
noncomputable
/--
Definition of `V` / `V` 的定义

English:
definition V
  signature: (i j : J)
  body: ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange

中文:
定义 V
  签名: (i j : J)
  定义体: ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange

Depends on / 依赖: F.map, opensRange
-/
def V (i j : J) : (F.obj i).Opens := ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange

/--
lemma `V_self` / 引理 `V_self`

English:
lemma V_self
  given: (i)
  statement: V F i i = ⊤
  proof: top_le_iff.mp (le_iSup_of_le ⟨i, 𝟙 _, 𝟙 _⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))

中文:
引理 V_self
  条件: (i)
  结论: V F i i = ⊤
  证明: top_le_iff.mp (le_iSup_of_le ⟨i, 𝟙 _, 𝟙 _⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))

Depends on / 依赖: Scheme, Scheme.Hom.opensRange_of_isIso, le_iSup_of_le, opensRange_of_isIso, top_le_iff, top_le_iff.mp
-/
lemma V_self (i) : V F i i = ⊤ :=
  top_le_iff.mp (le_iSup_of_le ⟨i, 𝟙 _, 𝟙 _⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))

variable [(F ⋙ forget).IsLocallyDirected]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_of_pullback_V_V` / 引理 `exists_of_pullback_V_V`

English:
lemma exists_of_pullback_V_V
  given: {i j k : J} (x : pullback (C := Scheme) (V F i j).ι (V F i k).ι)
  proof: by
  obtain ⟨k₁, y₁, hy₁⟩ := mem_iSup.mp ((pullback.fst (C := Scheme) _ _) x).2
  obtain ⟨k₂, y₂, hy₂⟩ := mem_iSup.mp ((pullback.snd (C := Scheme) _ _) x).2
  obtain ⟨l, hli, hlk, z, rfl, rfl⟩ :=
    (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1 y₁ y₂
      (by simpa [hy₁, hy₂] using

中文:
引理 存在_of_pullback_V_V
  条件: {i j k : J} (x : pullback (C := 概形) (V F i j).ι (V F i k).ι)
  证明: by
  obtain ⟨k₁, y₁, hy₁⟩ := mem_iSup.mp ((pullback.fst (C := Scheme) _ _) x).2
  obtain ⟨k₂, y₂, hy₂⟩ := mem_iSup.mp ((pullback.snd (C := Scheme) _ _) x).2
  obtain ⟨l, hli, hlk, z, rfl, rfl⟩ :=
    (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1 y₁ y₂
      (by simpa [hy₁, hy₂] using

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, CategoryStruct.id, MonoidalCategoryStruct, MonoidalCategoryStruct.rightUnitor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, MonoidalCategoryStruct.whiskerLeft, OrderEmbedding, OrderEmbedding.toOrderHom, Scheme, WithInitial, WithInitial.comp, WithInitial.down, WithInitial.id, rightUnitor, tensorHom, tensorObj, tensorUnit, toOrderHom
-/
lemma exists_of_pullback_V_V {i j k : J} (x : pullback (C := Scheme) (V F i j).ι (V F i k).ι) :
    exists (l : J) (fi : l ⟶ i) (fj : l ⟶ j) (fk : l ⟶ k)
      (α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι) (z : F.obj l),
      IsOpenImmersion α ∧
      α ≫ pullback.fst _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, _, fj⟩ le_rfl) ∧
      α ≫ pullback.snd _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, _, fk⟩ le_rfl) ∧
      α z = x := by
  obtain ⟨k₁, y₁, hy₁⟩ := mem_iSup.mp ((pullback.fst (C := Scheme) _ _) x).2
  obtain ⟨k₂, y₂, hy₂⟩ := mem_iSup.mp ((pullback.snd (C := Scheme) _ _) x).2
  obtain ⟨l, hli, hlk, z, rfl, rfl⟩ :=
    (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1 y₁ y₂
      (by simpa [hy₁, hy₂] using congr($(pullback.condition (f := (V F i j).ι)) x))
  let α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι :=
    pullback.lift
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ Scheme.homOfLE _
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2⟩ le_rfl))
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ Scheme.homOfLE _
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hlk ≫ k₂.2.2⟩ le_rfl))
      (by simp)
  have : IsOpenImmersion α := by
    apply +allowSynthFailures IsOpenImmersion.of_comp
    · exact (inferInstance : IsOpenImmersion (pullback.fst (V F i j).ι (V F i k).ι))
    · simp only [limit.lift_π, PullbackCone.mk_π_app, α]
      infer_instance
  have : α z = x := by
    apply (pullback.fst (C := Scheme) _ _).isOpenEmbedding.injective
    apply (V F i j).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]; rw [pullback.lift_fst_assoc]
    simpa using hy₁
  exact ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2, hlk ≫ k₂.2.2, α, z, ‹_›, by simp [α], by simp [α], ‹_›⟩

variable [Quiver.IsThin J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `fst_inv_eq_snd_inv` / 引理 `fst_inv_eq_snd_inv`

English:
lemma fst_inv_eq_snd_inv
  proof: by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨l, hli, hlj, y, hy₁, hy₂⟩ := (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1
    ((pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv) x)
    ((pullback.snd _ _ ≫ (F.map k₂.2.1).isoOpensRange.inv) x) (by
      simp only [Functor.

中文:
引理 fst_inv_eq_snd_inv
  证明: by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨l, hli, hlj, y, hy₁, hy₂⟩ := (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1
    ((pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv) x)
    ((pullback.snd _ _ ≫ (F.map k₂.2.1).isoOpensRange.inv) x) (by
      simp only [Functor.

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, ContinuousMap, ContinuousMap.comp_apply, F.map, Functor, Functor.comp_map, Functor.comp_obj, Hom.comp_apply, Hom.comp_base, MonoidalCategoryStruct, MonoidalCategoryStruct.leftUnitor, MonoidalCategoryStruct.whiskerRight, OrderEmbedding, OrderEmbedding.toOrderHom, Scheme, Scheme.hom_ext_of_forall, TopCat, TopCat.hom_comp, TypeCat
-/
lemma fst_inv_eq_snd_inv
    {i j : J} (k₁ k₂ : (k : J) × (k ⟶ i) × (k ⟶ j)) {U : (F.obj i).Opens}
    (h₁ : (F.map k₁.2.1).opensRange <= U) (h₂ : (F.map k₂.2.1).opensRange <= U) :
    pullback.fst ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₁.2.1).isoOpensRange.inv ≫ F.map k₁.2.2 =
    pullback.snd ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₂.2.1).isoOpensRange.inv ≫ F.map k₂.2.2 := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨l, hli, hlj, y, hy₁, hy₂⟩ := (F ⋙ forget).exists_map_eq_of_isLocallyDirected k₁.2.1 k₂.2.1
    ((pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv) x)
    ((pullback.snd _ _ ≫ (F.map k₂.2.1).isoOpensRange.inv) x) (by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
        TypeCat.Fun.coe_mk]
      simp only [← Hom.comp_apply]
      congr 5
      simpa using congr($(pullback.condition (f := (F.obj i).homOfLE h₁)
        (g := (F.obj i).homOfLE h₂)) ≫ Scheme.Opens.ι _))
  let α : F.obj l ⟶ pullback ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) :=
    pullback.lift
      (F.map hli ≫ (F.map k₁.2.1).isoOpensRange.hom)
      (F.map hlj ≫ (F.map k₂.2.1).isoOpensRange.hom)
      (by simp [← cancel_mono (Scheme.Opens.ι _), ← Functor.map_comp,
        Subsingleton.elim (hli ≫ k₁.2.1) (hlj ≫ k₂.2.1)])
  have : IsOpenImmersion α := by
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by
      simp only [pullback.lift_fst, α]; infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : α y = x := by
    simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map, Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.comp_apply] at hy₁
    apply (pullback.fst ((F.obj i).homOfLE h₁) _).isOpenEmbedding.injective
    simp only [← Scheme.Hom.comp_apply, α, pullback.lift_fst]
    simp_all
  refine ⟨α.opensRange, ⟨y, this⟩, ?_⟩
  rw [← cancel_epi α.isoOpensRange.hom]
  simp [α, ← Functor.map_comp, Subsingleton.elim (hli ≫ k₁.2.2) (hlj ≫ k₂.2.2)]

/--
Definition of `tAux` / `tAux` 的定义

English:
definition tAux
  signature: (i j : J)
  body: (Scheme.Opens.iSupOpenCover _).glueMorphisms
    (fun k => (F.map k.2.1).isoOpensRange.inv ≫ F.map k.2.2) fun k₁ k₂ => by
      dsimp [Scheme.Opens.iSupOpenCover]
      apply fst_inv_eq_snd_inv F

中文:
定义 tAux
  签名: (i j : J)
  定义体: (Scheme.Opens.iSupOpenCover _).glueMorphisms
    (fun k => (F.map k.2.1).isoOpensRange.inv ≫ F.map k.2.2) fun k₁ k₂ => by
      dsimp [Scheme.Opens.iSupOpenCover]
      apply fst_inv_eq_snd_inv F

Depends on / 依赖: F.map, Scheme, Scheme.Opens.iSupOpenCover, fst_inv_eq_snd_inv, glueMorphisms, iSupOpenCover, isoOpensRange, isoOpensRange.inv
-/
def tAux (i j : J) : (V F i j).toScheme ⟶ F.obj j :=
  (Scheme.Opens.iSupOpenCover _).glueMorphisms
    (fun k => (F.map k.2.1).isoOpensRange.inv ≫ F.map k.2.2) fun k₁ k₂ => by
      dsimp [Scheme.Opens.iSupOpenCover]
      apply fst_inv_eq_snd_inv F

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `homOfLE_tAux` / 引理 `homOfLE_tAux`

English:
lemma homOfLE_tAux
  given: (i j : J) {k : J} (fi : k ⟶ i) (fj : k ⟶ j)
  proof: (Scheme.Opens.iSupOpenCover (J := Σ k, (k ⟶ i) × (k ⟶ j)) _).ι_glueMorphisms _ _ ⟨k, fi, fj⟩

中文:
引理 homOfLE_tAux
  条件: (i j : J) {k : J} (fi : k ⟶ i) (fj : k ⟶ j)
  证明: (Scheme.Opens.iSupOpenCover (J := Σ k, (k ⟶ i) × (k ⟶ j)) _).ι_glueMorphisms _ _ ⟨k, fi, fj⟩

Depends on / 依赖: Scheme, Scheme.Opens.iSupOpenCover, iSupOpenCover
-/
lemma homOfLE_tAux (i j : J) {k : J} (fi : k ⟶ i) (fj : k ⟶ j) :
    (F.obj i).homOfLE (le_iSup_of_le ⟨k, fi, fj⟩ le_rfl) ≫
      tAux F i j = (F.map fi).isoOpensRange.inv ≫ F.map fj :=
  (Scheme.Opens.iSupOpenCover (J := Σ k, (k ⟶ i) × (k ⟶ j)) _).ι_glueMorphisms _ _ ⟨k, fi, fj⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `t` / `t` 的定义

English:
definition t
  signature: (i j : J)
  body: IsOpenImmersion.lift (V F j i).ι (tAux F i j) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, x, rfl⟩ := (Scheme.Opens.iSupOpenCover _).exists_eq x
    simp only [V, tAux, ← Scheme.Hom.comp_apply, Cover.ι_glueMorphisms]
    simp only [Opens.range_ι, iSup_mk, carrier_eq_coe, Hom.coe_opensRange, coe_mk, Hom.

中文:
定义 t
  签名: (i j : J)
  定义体: IsOpenImmersion.lift (V F j i).ι (tAux F i j) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, x, rfl⟩ := (Scheme.Opens.iSupOpenCover _).exists_eq x
    simp only [V, tAux, ← Scheme.Hom.comp_apply, Cover.ι_glueMorphisms]
    simp only [Opens.range_ι, iSup_mk, carrier_eq_coe, Hom.coe_opensRange, coe_mk, Hom.

Depends on / 依赖: ContinuousMap, ContinuousMap.comp_apply, Hom.coe_opensRange, Hom.comp_base, IsOpenImmersion, IsOpenImmersion.lift, Opens.range_, Scheme, Scheme.Hom.comp_apply, Scheme.Opens.iSupOpenCover, Set.mem_iUnion.mpr, TopCat, TopCat.hom_comp, carrier_eq_coe, coe_mk, coe_opensRange, comp_apply, comp_base, exists_eq, hom_comp
-/
def t (i j : J) : (V F i j).toScheme ⟶ (V F j i).toScheme :=
  IsOpenImmersion.lift (V F j i).ι (tAux F i j) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, x, rfl⟩ := (Scheme.Opens.iSupOpenCover _).exists_eq x
    simp only [V, tAux, ← Scheme.Hom.comp_apply, Cover.ι_glueMorphisms]
    simp only [Opens.range_ι, iSup_mk, carrier_eq_coe, Hom.coe_opensRange, coe_mk, Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.comp_apply]
    exact Set.mem_iUnion.mpr ⟨⟨l.1, l.2.2, l.2.1⟩, ⟨_, rfl⟩⟩)

/--
lemma `t_id` / 引理 `t_id`

English:
lemma t_id
  given: (i : J)
  statement: t F i i = 𝟙 _
  proof: by
  refine (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
  simp only [Category.comp_id, ← cancel_mono (Scheme.Opens.ι _), Category.assoc,
    IsOpenImmersion.lift_fac, Scheme.Cover.ι_glueMorphisms, t, tAux, V]
  simp [Scheme.Opens.iSupOpenCover, Iso.inv_comp_eq, Subsingleton.elim k.2.1 k.2

中文:
引理 t_id
  条件: (i : J)
  结论: t F i i = 𝟙 _
  证明: by
  refine (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
  simp only [Category.comp_id, ← cancel_mono (Scheme.Opens.ι _), Category.assoc,
    IsOpenImmersion.lift_fac, Scheme.Cover.ι_glueMorphisms, t, tAux, V]
  simp [Scheme.Opens.iSupOpenCover, Iso.inv_comp_eq, Subsingleton.elim k.2.1 k.2

Depends on / 依赖: Category, Category.assoc, Category.comp_id, IsOpenImmersion, IsOpenImmersion.lift_fac, Iso.inv_comp_eq, Scheme, Scheme.Cover, Scheme.Opens, Scheme.Opens.iSupOpenCover, Subsingleton, Subsingleton.elim, cancel_mono, comp_id, hom_ext, iSupOpenCover, inv_comp_eq, lift_fac
-/
lemma t_id (i : J) : t F i i = 𝟙 _ := by
  refine (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
  simp only [Category.comp_id, ← cancel_mono (Scheme.Opens.ι _), Category.assoc,
    IsOpenImmersion.lift_fac, Scheme.Cover.ι_glueMorphisms, t, tAux, V]
  simp [Scheme.Opens.iSupOpenCover, Iso.inv_comp_eq, Subsingleton.elim k.2.1 k.2.2]

variable [Small.{u} J]

local notation3:max "↓"j:arg => Equiv.symm (equivShrink _) j

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `glueData` / `glueData` 的定义

English:
definition glueData
  signature: : Scheme.GlueData where
  body: Shrink.{u} J
  U j := F.obj ↓j
  V ij := V F ↓ij.1 ↓ij.2
  f i j := Scheme.Opens.ι _
  f_id i := V_self F ↓i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t F ↓i ↓j
  t_id i := t_id F ↓i
  t' i j k := pullback.lift
    (IsOpenImmersion.lift (V F 

中文:
定义 glueData
  签名: : 概形.粘合数据 where
  定义体: Shrink.{u} J
  U j := F.obj ↓j
  V ij := V F ↓ij.1 ↓ij.2
  f i j := Scheme.Opens.ι _
  f_id i := V_self F ↓i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t F ↓i ↓j
  t_id i := t_id F ↓i
  t' i j k := pullback.lift
    (IsOpenImmersion.lift (V F 

Depends on / 依赖: Shrink
-/
def glueData : Scheme.GlueData where
  J := Shrink.{u} J
  U j := F.obj ↓j
  V ij := V F ↓ij.1 ↓ij.2
  f i j := Scheme.Opens.ι _
  f_id i := V_self F ↓i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t F ↓i ↓j
  t_id i := t_id F ↓i
  t' i j k := pullback.lift
    (IsOpenImmersion.lift (V F ↓j ↓k).ι (pullback.fst _ _ ≫ tAux F ↓i ↓j) (by
      rintro _ ⟨x, rfl⟩
      obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, rfl⟩ := exists_of_pullback_V_V F x
      rw [← Scheme.Hom.comp_apply]; rw [reassoc_of% hα₁]; rw [homOfLE_tAux F ↓i ↓j fi fj]; rw [Iso.hom_inv_id_assoc]; rw [Scheme.Opens.range_ι]; rw [SetLike.mem_coe]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨l, fj, fk⟩, ⟨z, rfl⟩⟩))
      (pullback.fst _ _ ≫ t F _ _) (by simp [t])
  t_fac i j k := pullback.lift_snd _ _ _
  cocycle i j k := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    have := exists_of_pullback_V_V F x
    obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, e⟩ := this -- doing them in the same step times out.
    refine ⟨α.opensRange, ⟨_, e⟩, ?_⟩
    rw [← cancel_mono (pullback.snd _ _)]; rw [← cancel_mono (Scheme.Opens.ι _)]
    simp only [t, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      limit.lift_π_assoc, cospan_left, IsOpenImmersion.lift_fac, Category.id_comp]
    rw [IsOpenImmersion.comp_lift_assoc]
    simp only [limit.lift_π_assoc, cospan_left, PullbackCone.mk_π_app]
    rw [← cancel_epi α.isoOpensRange.hom]
    simp_rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, IsOpenImmersion.comp_lift_assoc]
    simp only [reassoc_of% hα₁, homOfLE_tAux F _ _ fi fj, Iso.hom_inv_id_assoc, reassoc_of% hα₂]
    generalize_proofs _ h₁
    have : IsOpenImmersion.lift (V F ↓j ↓k).ι (F.map fj) h₁ = (F.map fj).isoOpensRange.hom ≫
        (F.obj ↓j).homOfLE (le_iSup_of_le ⟨l, fj, fk⟩ le_rfl) := by
      rw [← cancel_mono (Scheme.Opens.ι _)]; rw [Category.assoc]; rw [IsOpenImmersion.lift_fac]; rw [← Iso.inv_comp_eq]; rw [Scheme.Hom.isoOpensRange_inv_comp]
      exact (Scheme.homOfLE_ι _ _).symm
    simp_rw [this, Category.assoc, homOfLE_tAux F _ _ fj fk, Iso.hom_inv_id_assoc]
    generalize_proofs h₂
    have : IsOpenImmersion.lift (V F ↓k ↓i).ι (F.map fk) h₂ = (F.map fk).isoOpensRange.hom ≫
        (F.obj ↓k).homOfLE (le_iSup_of_le ⟨l, fk, fi⟩ le_rfl) := by
      rw [← cancel_mono (Scheme.Opens.ι _)]; rw [Category.assoc]; rw [IsOpenImmersion.lift_fac]; rw [← Iso.inv_comp_eq]; rw [Scheme.Hom.isoOpensRange_inv_comp]
      exact (Scheme.homOfLE_ι _ _).symm
    simp_rw [this, Category.assoc, homOfLE_tAux F _ _ fk fi, Iso.hom_inv_id_assoc,
      ← Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_inv_comp]
    exact (Scheme.homOfLE_ι _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `glueDataι_naturality` / 引理 `glueDataι_naturality`

English:
lemma glueDataι_naturality
  given: {i j : Shrink.{u} J} (f : ↓i ⟶ ↓j)
  proof: by
  have : IsIso (V F ↓i ↓j).ι := by
    have : V F ↓i ↓j = ⊤ :=
      top_le_iff.mp (le_iSup_of_le ⟨_, 𝟙 _, f⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))
    exact this ▸ (topIso _).isIso_hom
  have : t F ↓i ↓j ≫ (V F ↓j ↓i).ι ≫ _ = (V F ↓i ↓j).ι ≫ _ :=
    (glueData F).glue_condition i j
  simp 

中文:
引理 glueDataι_naturality
  条件: {i j : Shrink.{u} J} (f : ↓i ⟶ ↓j)
  证明: by
  have : IsIso (V F ↓i ↓j).ι := by
    have : V F ↓i ↓j = ⊤ :=
      top_le_iff.mp (le_iSup_of_le ⟨_, 𝟙 _, f⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))
    exact this ▸ (topIso _).isIso_hom
  have : t F ↓i ↓j ≫ (V F ↓j ↓i).ι ≫ _ = (V F ↓i ↓j).ι ≫ _ :=
    (glueData F).glue_condition i j
  simp 

Depends on / 依赖: Category, Category.assoc, IsOpenImmersion, IsOpenImmersion.lift_fac_assoc, Iso.eq_inv_comp, Scheme, Scheme.Hom.opensRange_of_isIso, cancel_epi, eq_inv_comp, glueData, glue_condition, homOfLE_tAux, isIso_hom, le_iSup_of_le, lift_fac_assoc, opensRange_of_isIso, topIso, top_le_iff, top_le_iff.mp
-/
lemma glueDataι_naturality {i j : Shrink.{u} J} (f : ↓i ⟶ ↓j) :
    F.map f ≫ (glueData F).ι j = (glueData F).ι i := by
  have : IsIso (V F ↓i ↓j).ι := by
    have : V F ↓i ↓j = ⊤ :=
      top_le_iff.mp (le_iSup_of_le ⟨_, 𝟙 _, f⟩ (by simp [Scheme.Hom.opensRange_of_isIso]))
    exact this ▸ (topIso _).isIso_hom
  have : t F ↓i ↓j ≫ (V F ↓j ↓i).ι ≫ _ = (V F ↓i ↓j).ι ≫ _ :=
    (glueData F).glue_condition i j
  simp only [t, IsOpenImmersion.lift_fac_assoc] at this
  rw [← cancel_epi (V F ↓i ↓j).ι]; rw [← this]; rw [← Category.assoc]; rw [← (Iso.eq_inv_comp _).mp (homOfLE_tAux F ↓i ↓j (𝟙 _) f)]; rw [← Category.assoc]; rw [← Category.assoc]; rw [Category.assoc]
  convert! Category.id_comp _
  simp [← cancel_mono (Opens.ι _), V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone F where
  body: (glueData F).glued
  ι.app j := F.map (eqToHom (by simp)) ≫ (glueData F).ι (equivShrink _ j)
  ι.naturality {i j} f := by
    simp only [← IsIso.inv_comp_eq, ← Functor.map_inv, ← Functor.map_comp_assoc,
      glueDataι_naturality, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]

中文:
定义 cocone
  签名: : 余锥 F where
  定义体: (glueData F).glued
  ι.app j := F.map (eqToHom (by simp)) ≫ (glueData F).ι (equivShrink _ j)
  ι.naturality {i j} f := by
    simp only [← IsIso.inv_comp_eq, ← Functor.map_inv, ← Functor.map_comp_assoc,
      glueDataι_naturality, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]

Depends on / 依赖: glueData
-/
def cocone : Cocone F where
  pt := (glueData F).glued
  ι.app j := F.map (eqToHom (by simp)) ≫ (glueData F).ι (equivShrink _ j)
  ι.naturality {i j} f := by
    simp only [← IsIso.inv_comp_eq, ← Functor.map_inv, ← Functor.map_comp_assoc,
      glueDataι_naturality, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The cocone associated to a locally directed diagram is a colimit.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
noncomputable
/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: : IsColimit (cocone F) where
  body: Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
    rintro ⟨i, j⟩
    dsimp [glueData, GlueData.diagram]
    simp only [t, IsOpenImmersion.lift_fac]
    apply (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
    simp only [Opens.iSupOpenCover, V, Scheme.homOfLE_ι_assoc]
    rw [homOfLE_tAu

中文:
定义 isColimit
  签名: : 是余极限 (cocone F) where
  定义体: Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
    rintro ⟨i, j⟩
    dsimp [glueData, GlueData.diagram]
    simp only [t, IsOpenImmersion.lift_fac]
    apply (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
    simp only [Opens.iSupOpenCover, V, Scheme.homOfLE_ι_assoc]
    rw [homOfLE_tAu

Depends on / 依赖: Category, Category.assoc, GlueData, GlueData.diagram, IsOpenImmersion, IsOpenImmersion.lift_fac, Iso.eq_inv_comp, Multicoequalizer, Multicoequalizer.desc, Multicoequalizer.hom_, Opens.iSupOpenCover, Scheme, Scheme.Opens.iSupOpenCover, Scheme.homOfLE_, conv_lhs, diagram, eq_inv_comp, glueData, homOfLE_tAux_assoc, hom_
-/
def isColimit : IsColimit (cocone F) where
  desc s := Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
    rintro ⟨i, j⟩
    dsimp [glueData, GlueData.diagram]
    simp only [t, IsOpenImmersion.lift_fac]
    apply (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun k => ?_
    simp only [Opens.iSupOpenCover, V, Scheme.homOfLE_ι_assoc]
    rw [homOfLE_tAux_assoc F ↓i ↓j k.2.1 k.2.2]; rw [Iso.eq_inv_comp]
    simp)
  fac s j := by
    refine (Category.assoc _ _ _).trans ?_
    conv_lhs => enter [2]; tactic => exact Multicoequalizer.π_desc _ _ _ _ _
    simp
  uniq s m hm := Multicoequalizer.hom_ext _ _ _ fun i => by
    simp [← hm ↓i, cocone, reassoc_of% glueDataι_naturality]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation detail)
The cocone associated to a locally directed diagram is a colimit as locally ringed spaces.

One usually does not want to use this directly, and instead use the generic `colimit` API.
-/
noncomputable
/--
Definition of `isColimitForgetToLocallyRingedSpace` / `isColimitForgetToLocallyRingedSpace` 的定义

English:
definition isColimitForgetToLocallyRingedSpace
  signature: :
  body: (glueData F).isoLocallyRingedSpace.hom ≫
    Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
      rintro ⟨i, j⟩
      dsimp [glueData, GlueData.diagram]
      simp only [t, IsOpenImmersion.lift_fac, ← Scheme.Hom.comp_toLRSHom]
      rw [← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.fromGlue

中文:
定义 isColimitForgetToLocallyRingedSpace
  签名: :
  定义体: (glueData F).isoLocallyRingedSpace.hom ≫
    Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
      rintro ⟨i, j⟩
      dsimp [glueData, GlueData.diagram]
      simp only [t, IsOpenImmersion.lift_fac, ← Scheme.Hom.comp_toLRSHom]
      rw [← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.fromGlue

Depends on / 依赖: glueData, isoLocallyRingedSpace, isoLocallyRingedSpace.hom
-/
def isColimitForgetToLocallyRingedSpace :
    IsColimit (Scheme.forgetToLocallyRingedSpace.mapCocone (cocone F)) where
  desc s := (glueData F).isoLocallyRingedSpace.hom ≫
    Multicoequalizer.desc _ _ (fun i => s.ι.app ↓i) (by
      rintro ⟨i, j⟩
      dsimp [glueData, GlueData.diagram]
      simp only [t, IsOpenImmersion.lift_fac, ← Scheme.Hom.comp_toLRSHom]
      rw [← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.fromGlued.toLRSHom]; rw [← cancel_epi (Scheme.Opens.iSupOpenCover _).ulift.gluedCover.isoLocallyRingedSpace.inv]
      refine Multicoequalizer.hom_ext _ _ _ fun ⟨k, hk⟩ => ?_
      rw [← CategoryTheory.GlueData.ι]; rw [reassoc_of% GlueData.ι_isoLocallyRingedSpace_inv]; rw [reassoc_of% GlueData.ι_isoLocallyRingedSpace_inv]; rw [← cancel_epi (Hom.isoOpensRange (F.map _)).hom.toLRSHom]
      simp +instances only [Opens.iSupOpenCover, Cover.ulift, V, ← Hom.comp_toLRSHom_assoc,
        Cover.ι_fromGlued_assoc, homOfLE_ι, Hom.isoOpensRange_hom_ι, Cover.idx]
      generalize_proofs _ _ h
      rw [homOfLE_tAux F ↓i ↓j h.choose.2.1 h.choose.2.2]; rw [Iso.hom_inv_id_assoc]
      exact (s.w h.choose.2.1).trans (s.w h.choose.2.2).symm)
  fac s j := by
    simp only [cocone, Functor.mapCocone_ι_app, Scheme.Hom.comp_toLRSHom,
      forgetToLocallyRingedSpace_map, ← GlueData.ι_isoLocallyRingedSpace_inv]
    simpa [CategoryTheory.GlueData.ι] using s.w _
  uniq s m hm := by
    rw [← Iso.inv_comp_eq]
    refine Multicoequalizer.hom_ext _ _ _ fun i => ?_
    conv_lhs => rw [← ι.eq_def]
    dsimp
    simp [cocone, ← hm, glueDataι_naturality,
      ← GlueData.ι_isoLocallyRingedSpace_inv, -ι_gluedIso_inv_assoc, -ι_gluedIso_inv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: ⟨_, isColimit F⟩

中文:
实例 :
  签名: 有余极限 F
  定义体: ⟨_, isColimit F⟩

Depends on / 依赖: isColimit
-/
instance : HasColimit F := ⟨_, isColimit F⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F Scheme.forgetToLocallyRingedSpace
  body: preservesColimit_of_preserves_colimit_cocone (isColimit F) (isColimitForgetToLocallyRingedSpace F)

中文:
实例 :
  签名: 保持余极限 F 概形.forgetToLocallyRingedSpace
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimit F) (isColimitForgetToLocallyRingedSpace F)

Depends on / 依赖: isColimit, isColimitForgetToLocallyRingedSpace, preservesColimit_of_preserves_colimit_cocone
-/
instance : PreservesColimit F Scheme.forgetToLocallyRingedSpace :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (isColimitForgetToLocallyRingedSpace F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimit F Scheme.forgetToLocallyRingedSpace
  body: CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves

中文:
实例 :
  签名: 创造余极限 F 概形.forgetToLocallyRingedSpace
  定义体: CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves

Depends on / 依赖: CategoryTheory, CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves, createsColimitOfReflectsIsomorphismsOfPreserves
-/
instance : CreatesColimit F Scheme.forgetToLocallyRingedSpace :=
  CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the colimit of a locally directed diagram by the components. -/
@[simps! I₀ X f]
/--
Definition of `openCover` / `openCover` 的定义

English:
definition openCover
  signature: : (colimit F).OpenCover
  body: Cover.copy ((coverOfIsIso ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).hom).bind
    fun i => (glueData F).openCover) J F.obj (colimit.ι F)
    ((equivShrink J).trans <| (Equiv.uniqueSigma fun (_ : Unit) => Shrink J).symm)
    (fun _ => F.mapIso (eqToIso (by simp [GlueData.openCove

中文:
定义 openCover
  签名: : (colimit F).OpenCover
  定义体: Cover.copy ((coverOfIsIso ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).hom).bind
    fun i => (glueData F).openCover) J F.obj (colimit.ι F)
    ((equivShrink J).trans <| (Equiv.uniqueSigma fun (_ : Unit) => Shrink J).symm)
    (fun _ => F.mapIso (eqToIso (by simp [GlueData.openCove

Depends on / 依赖: Category, Category.assoc, Cover.copy, Equiv.uniqueSigma, F.mapIso, F.obj, GlueData, GlueData.openCover, Iso.comp_inv_eq, Shrink, cocone, coconePointUniqueUpToIso, colimit, colimit.isColimit, comp_inv_eq, coverOfIsIso, eqToIso, equivShrink, glueData, isColimit
-/
def openCover : (colimit F).OpenCover :=
  Cover.copy ((coverOfIsIso ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).hom).bind
    fun i => (glueData F).openCover) J F.obj (colimit.ι F)
    ((equivShrink J).trans <| (Equiv.uniqueSigma fun (_ : Unit) => Shrink J).symm)
    (fun _ => F.mapIso (eqToIso (by simp [GlueData.openCover, glueData]))) fun i => by
  change colimit.ι F i = _ ≫ (glueData F).ι (equivShrink J i) ≫ _
  simp [← Category.assoc, ← Iso.comp_inv_eq, cocone]

set_option backward.isDefEq.respectTransparency.types false in
instance (i) : IsOpenImmersion (colimit.ι F i) :=
  inferInstanceAs (IsOpenImmersion ((openCover F).f i))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ι_eq_ι_iff` / 引理 `ι_eq_ι_iff`

English:
lemma ι_eq_ι_iff
  given: {i j : J} {xi : F.obj i} {xj : F.obj j}
  proof: by
  constructor; swap
  · rintro ⟨k, fi, fj, x, rfl, rfl⟩; simp only [← Scheme.Hom.comp_apply, colimit.w]
  obtain ⟨i, rfl⟩ := (equivShrink J).symm.surjective i
  obtain ⟨j, rfl⟩ := (equivShrink J).symm.surjective j
  rw [← ((isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)).inv.isOp

中文:
引理 ι_eq_ι_iff
  条件: {i j : J} {xi : F.obj i} {xj : F.obj j}
  证明: by
  constructor; swap
  · rintro ⟨k, fi, fj, x, rfl, rfl⟩; simp only [← Scheme.Hom.comp_apply, colimit.w]
  obtain ⟨i, rfl⟩ := (equivShrink J).symm.surjective i
  obtain ⟨j, rfl⟩ := (equivShrink J).symm.surjective j
  rw [← ((isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)).inv.isOp

Depends on / 依赖: Limits, Limits.colimit, Scheme, Scheme.Hom.comp_apply, cocone, coconePointUniqueUpToIso, colimit, colimit.comp_coconePointUniqueUpToIso_inv, colimit.isColimit, colimit.w, comp_apply, comp_coconePointUniqueUpToIso_inv, eq_iff, equivShrink, glueData, injective, inv.isOpenEmbedding.injective.eq_iff, isColimit, isOpenEmbedding, surjective
-/
lemma ι_eq_ι_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      exists k fi fj, exists (x : F.obj k), F.map fi x = xi ∧ F.map fj x = xj := by
  constructor; swap
  · rintro ⟨k, fi, fj, x, rfl, rfl⟩; simp only [← Scheme.Hom.comp_apply, colimit.w]
  obtain ⟨i, rfl⟩ := (equivShrink J).symm.surjective i
  obtain ⟨j, rfl⟩ := (equivShrink J).symm.surjective j
  rw [← ((isColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)).inv.isOpenEmbedding.injective.eq_iff]
  simp only [Limits.colimit, ← Scheme.Hom.comp_apply,
    colimit.comp_coconePointUniqueUpToIso_inv, cocone, glueDataι_naturality]
  refine ?_ ∘ ((glueData F).ι_eq_iff _ _ _ _).mp
  dsimp +instances only [GlueData.Rel]
  rintro ⟨x, rfl, rfl⟩
  obtain ⟨⟨k, ki, kj⟩, y, hy : F.map ki y = (glueData F).f i j x⟩ := mem_iSup.mp x.2
  refine ⟨k, ki, kj, y, hy, ?_⟩
  obtain ⟨k, rfl⟩ := (equivShrink J).symm.surjective k
  apply ((glueData F).ι _).isOpenEmbedding.injective
  simp only [← Scheme.Hom.comp_apply, Category.assoc, GlueData.glue_condition]
  trans (glueData F).ι k y
  · simp [← glueDataι_naturality F kj]; rfl
  · simp [← glueDataι_naturality F ki, ← hy]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ι_jointly_surjective` / 引理 `ι_jointly_surjective`

English:
lemma ι_jointly_surjective
  given: (x : ↑(colimit F))
  proof: by
  obtain ⟨i, xi, h⟩ :=
    (IsLocallyDirected.glueData F).ι_jointly_surjective
      (((IsLocallyDirected.isColimit F).coconePointUniqueUpToIso (colimit.isColimit _)).inv x)
  use (equivShrink J).symm i, xi
  apply ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).inv.isOpenEmbedding

中文:
引理 ι_jointly_surjective
  条件: (x : ↑(colimit F))
  证明: by
  obtain ⟨i, xi, h⟩ :=
    (IsLocallyDirected.glueData F).ι_jointly_surjective
      (((IsLocallyDirected.isColimit F).coconePointUniqueUpToIso (colimit.isColimit _)).inv x)
  use (equivShrink J).symm i, xi
  apply ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).inv.isOpenEmbedding

Depends on / 依赖: IsLocallyDirected, IsLocallyDirected.glueData, IsLocallyDirected.isColimit, Scheme, Scheme.Hom.comp_apply, cocone, coconePointUniqueUpToIso, cocone_x, colimit, colimit.cocone_x, colimit.isColimit, comp_apply, eqToHom_m, eqToHom_naturality, equivShrink, glueData, injective, inv.isOpenEmbedding.injective, isColimit, isOpenEmbedding
-/
lemma ι_jointly_surjective (x : ↑(colimit F)) :
    exists (i : J) (xi : F.obj i), colimit.ι F i xi = x := by
  obtain ⟨i, xi, h⟩ :=
    (IsLocallyDirected.glueData F).ι_jointly_surjective
      (((IsLocallyDirected.isColimit F).coconePointUniqueUpToIso (colimit.isColimit _)).inv x)
  use (equivShrink J).symm i, xi
  apply ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).inv.isOpenEmbedding.injective
  simp_rw [← h, colimit.cocone_x, ← Scheme.Hom.comp_apply]
  congr 5
  have := eqToHom_naturality (fun j => (glueData F).ι j)
    (show i = ((equivShrink J) ((equivShrink J).symm i)) by simp)
  simp [cocone, eqToHom_map, ← this]

instance (F : WidePushoutShape J ⥤ Scheme.{u}) [forall {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] :
    (F ⋙ forget).IsLocallyDirected :=
  have (i : _) : Mono ((F ⋙ forget).map (.init i)) :=
    (mono_iff_injective _).mpr (F.map _).isOpenEmbedding.injective
  inferInstance

end IsLocallyDirected

end IsLocallyDirected

end Scheme

end AlgebraicGeometry
