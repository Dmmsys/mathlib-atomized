/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.CompactlyGenerated
/-!

# The adjunction between condensed sets and topological spaces

This file defines the functor `condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1}` which is
left adjoint to `topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for compactly generated spaces, and we conclude that the functor
`topCatToCondensedSet` is fully faithful when restricted to compactly generated spaces.
-/

@[expose] public section

universe u

open Condensed CondensedSet CategoryTheory CompHaus

variable (X : CondensedSet.{u})

set_option backward.privateInPublic true in
/--
Definition of `CondensedSet.coinducingCoprod` / `CondensedSet.coinducingCoprod` 的定义

English:
definition CondensedSet.coinducingCoprod
  signature: :
  body: fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i

中文:
定义 CondensedSet.coinducingCoprod
  签名: :
  定义体: fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i
-/
private def CondensedSet.coinducingCoprod :
    (Σ (i : (S : CompHaus.{u}) × X.obj.obj ⟨S⟩), i.fst) -> X.obj.obj ⟨of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Let `X` be a condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from compact Hausdorff `S` spaces to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `CondensedSet.coinducingCoprod` above. -/
local instance : TopologicalSpace (X.obj.obj ⟨CompHaus.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/--
Definition of `CondensedSet.toTopCat` / `CondensedSet.toTopCat` 的定义

English:
abbreviation CondensedSet.toTopCat
  signature: : TopCat.{u + 1}
  body: TopCat.of (X.obj.obj ⟨of PUnit⟩)

中文:
缩写 CondensedSet.toTopCat
  签名: : TopCat.{u + 1}
  定义体: TopCat.of (X.obj.obj ⟨of PUnit⟩)

Depends on / 依赖: TopCat, TopCat.of, X.obj.obj
-/
abbrev CondensedSet.toTopCat : TopCat.{u + 1} := TopCat.of (X.obj.obj ⟨of PUnit⟩)

namespace CondensedSet

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `continuous_coinducingCoprod` / 引理 `continuous_coinducingCoprod`

English:
lemma continuous_coinducingCoprod
  given: {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩)
  proof: by
  suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

中文:
引理 continuous_coinducingCoprod
  条件: {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩)
  证明: by
  suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

Depends on / 依赖: CompHaus, Continuous, X.coinducingCoprod, X.obj.obj, coinducingCoprod, continuous_coinduced_rng, continuous_sigma_iff, i.fst
-/
lemma continuous_coinducingCoprod {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩) :
    Continuous fun a => (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : CondensedSet} (f : X ⟶ Y)

/-- The map part of the functor `CondensedSet ⥤ TopCat` -/
@[simps!]
/--
Definition of `toTopCatMap` / `toTopCatMap` 的定义

English:
definition toTopCatMap
  signature: : X.toTopCat ⟶ Y.toTopCat
  body: TopCat.ofHom
  { toFun := f.hom.app ⟨of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) =>
          f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u

中文:
定义 toTopCatMap
  签名: : X.toTopCat ⟶ Y.toTopCat
  定义体: TopCat.ofHom
  { toFun := f.hom.app ⟨of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) =>
          f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u

Depends on / 依赖: Function, Function.comp_apply, NatTrans, NatTrans.naturality_apply, TopCat, TopCat.ofHom, X.obj.map, coinducingCoprod, comp_apply, continuous_coinduced_dom, continuous_coinducingCoprod, continuous_sigma, continuous_toFun, f.hom, f.hom.app, naturality_apply
-/
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.hom.app ⟨of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) =>
          f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u + 1}).const a).op x)) = _
        from funext fun a => NatTrans.naturality_apply f.hom ((of PUnit.{u + 1}).const a).op x]
      exact continuous_coinducingCoprod Y _ }

end CondensedSet

/-- The functor `CondensedSet ⥤ TopCat` -/
@[simps]
/--
Definition of `condensedSetToTopCat` / `condensedSetToTopCat` 的定义

English:
definition condensedSetToTopCat
  signature: : CondensedSet.{u} ⥤ TopCat.{u + 1} where
  body: X.toTopCat
  map f := toTopCatMap f

中文:
定义 condensedSetToTopCat
  签名: : CondensedSet.{u} ⥤ TopCat.{u + 1} where
  定义体: X.toTopCat
  map f := toTopCatMap f

Depends on / 依赖: X.toTopCat, toTopCat
-/
def condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1} where
  obj X := X.toTopCat
  map f := toTopCatMap f

namespace CondensedSet

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `topCatAdjunctionCounit` / `topCatAdjunctionCounit` 的定义

English:
definition topCatAdjunctionCounit
  signature: (X : TopCat.{u + 1})
  body: TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

中文:
定义 topCatAdjunctionCounit
  签名: (X : TopCat.{u + 1})
  定义体: TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

Depends on / 依赖: PUnit.unit, TopCat, TopCat.ofHom, continuity, continuous_coinduced_dom, continuous_toFun
-/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u + 1}) : X.toCondensedSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `topCatAdjunctionCounit_hom_apply` / 引理 `topCatAdjunctionCounit_hom_apply`

English:
lemma topCatAdjunctionCounit_hom_apply
  given: (X : TopCat) (x)
  proof: rfl

中文:
引理 topCatAdjunctionCounit_hom_apply
  条件: (X : TopCat) (x)
  证明: rfl
-/
@[simp] lemma topCatAdjunctionCounit_hom_apply (X : TopCat) (x) :
    -- We have to specify here to not infer the `TopologicalSpace` instance on `C(PUnit, X)`,
    -- which suggests type synonyms are being unfolded too far somewhere.
    DFunLike.coe (F := @ContinuousMap C(PUnit, X) X (_) _)
        (TopCat.Hom.hom (topCatAdjunctionCounit X)) x =
      x PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `topCatAdjunctionCounitEquiv` / `topCatAdjunctionCounitEquiv` 的定义

English:
definition topCatAdjunctionCounitEquiv
  signature: (X : TopCat.{u + 1})
  body: topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

中文:
定义 topCatAdjunctionCounitEquiv
  签名: (X : TopCat.{u + 1})
  定义体: topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

Depends on / 依赖: topCatAdjunctionCounit
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u + 1}) :
    X.toCondensedSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

/--
lemma `topCatAdjunctionCounit_bijective` / 引理 `topCatAdjunctionCounit_bijective`

English:
lemma topCatAdjunctionCounit_bijective
  given: (X : TopCat.{u + 1})
  proof: (topCatAdjunctionCounitEquiv X).bijective

中文:
引理 topCatAdjunctionCounit_bijective
  条件: (X : TopCat.{u + 1})
  证明: (topCatAdjunctionCounitEquiv X).bijective

Depends on / 依赖: bijective, topCatAdjunctionCounitEquiv
-/
lemma topCatAdjunctionCounit_bijective (X : TopCat.{u + 1}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
@[simps hom_app]
/--
Definition of `topCatAdjunctionUnit` / `topCatAdjunctionUnit` 的定义

English:
definition topCatAdjunctionUnit
  signature: (X : CondensedSet.{u})
  body: {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_

中文:
定义 topCatAdjunctionUnit
  签名: (X : CondensedSet.{u})
  定义体: {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_
-/
noncomputable def topCatAdjunctionUnit (X : CondensedSet.{u}) : X ⟶ X.toTopCat.toCondensedSet where
  hom := {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ => by
      ext
      simp only [TypeCat.Fun.toFun_apply,
        comp_apply, TopCat.toSheafCompHausLike_obj_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, ← Functor.map_comp_apply]
      rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `topCatAdjunction` / `topCatAdjunction` 的定义

English:
definition topCatAdjunction
  signature: : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where
  body: topCatAdjunctionUnit
  counit.app := topCatAdjunctionCounit
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

中文:
定义 topCatAdjunction
  签名: : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where
  定义体: topCatAdjunctionUnit
  counit.app := topCatAdjunctionCounit
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

Depends on / 依赖: topCatAdjunctionUnit
-/
noncomputable def topCatAdjunction : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where
  unit.app := topCatAdjunctionUnit
  counit.app := topCatAdjunctionCounit
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

set_option backward.isDefEq.respectTransparency.types false in
instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: topCatToCondensedSet.Faithful
  body: topCatAdjunction.faithful_R_of_epi_counit_app

中文:
实例 :
  签名: topCatToCondensedSet.Faithful
  定义体: topCatAdjunction.faithful_R_of_epi_counit_app

Depends on / 依赖: faithful_R_of_epi_counit_app, topCatAdjunction, topCatAdjunction.faithful_R_of_epi_counit_app
-/
instance : topCatToCondensedSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open CompactlyGenerated

instance (X : CondensedSet.{u}) : UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f h
  rw [continuous_coinduced_dom]; rw [continuous_sigma_iff]
  exact fun ⟨S, s⟩ => h S ⟨_, continuous_coinducingCoprod X _⟩

instance (X : CondensedSet.{u}) :
    UCompactlyGeneratedSpace.{u, u + 1} (condensedSetToTopCat.obj X) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat)

/--
Definition of `condensedSetToCompactlyGenerated` / `condensedSetToCompactlyGenerated` 的定义

English:
definition condensedSetToCompactlyGenerated
  signature: : CondensedSet.{u} ⥤ CompactlyGenerated.{u, u + 1} where
  body: CompactlyGenerated.of (condensedSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

中文:
定义 condensedSetToCompactlyGenerated
  签名: : CondensedSet.{u} ⥤ CompactlyGenerated.{u, u + 1} where
  定义体: CompactlyGenerated.of (condensedSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

Depends on / 依赖: CompactlyGenerated, CompactlyGenerated.of, condensedSetToTopCat, condensedSetToTopCat.obj
-/
def condensedSetToCompactlyGenerated : CondensedSet.{u} ⥤ CompactlyGenerated.{u, u + 1} where
  obj X := CompactlyGenerated.of (condensedSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

/--
Definition of `compactlyGeneratedToCondensedSet` / `compactlyGeneratedToCondensedSet` 的定义

English:
definition compactlyGeneratedToCondensedSet
  signature: :
  body: compactlyGeneratedToTop ⋙ topCatToCondensedSet

中文:
定义 compactlyGeneratedToCondensedSet
  签名: :
  定义体: compactlyGeneratedToTop ⋙ topCatToCondensedSet

Depends on / 依赖: compactlyGeneratedToTop, topCatToCondensedSet
-/
noncomputable def compactlyGeneratedToCondensedSet :
    CompactlyGenerated.{u, u + 1} ⥤ CondensedSet.{u} :=
  compactlyGeneratedToTop ⋙ topCatToCondensedSet


/--
Definition of `compactlyGeneratedAdjunction` / `compactlyGeneratedAdjunction` 的定义

English:
definition compactlyGeneratedAdjunction
  signature: :
  body: topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := compactlyGeneratedToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulCompactlyGeneratedToTop
    (Iso.refl _) (Iso.refl _)

中文:
定义 compactlyGeneratedAdjunction
  签名: :
  定义体: topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := compactlyGeneratedToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulCompactlyGeneratedToTop
    (Iso.refl _) (Iso.refl _)

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.id, Iso.refl, compactlyGeneratedToTop, fullyFaithfulCompactlyGeneratedToTop, restrictFullyFaithful, topCatAdjunction, topCatAdjunction.restrictFullyFaithful
-/
noncomputable def compactlyGeneratedAdjunction :
    condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := compactlyGeneratedToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulCompactlyGeneratedToTop
    (Iso.refl _) (Iso.refl _)

/--
Definition of `compactlyGeneratedAdjunctionCounitHomeo` / `compactlyGeneratedAdjunctionCounitHomeo` 的定义

English:
definition compactlyGeneratedAdjunctionCounitHomeo
  body: topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply continuous_from_uCompactlyGeneratedSpace
    exact fun _ _ => continuous_coinducingCoprod X.toCondensedSet _

中文:
定义 compactlyGeneratedAdjunctionCounitHomeo
  定义体: topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply continuous_from_uCompactlyGeneratedSpace
    exact fun _ _ => continuous_coinducingCoprod X.toCondensedSet _

Depends on / 依赖: topCatAdjunctionCounitEquiv
-/
noncomputable def compactlyGeneratedAdjunctionCounitHomeo
    (X : TopCat.{u + 1}) [UCompactlyGeneratedSpace.{u} X] :
    X.toCondensedSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply continuous_from_uCompactlyGeneratedSpace
    exact fun _ _ => continuous_coinducingCoprod X.toCondensedSet _

/--
Definition of `compactlyGeneratedAdjunctionCounitIso` / `compactlyGeneratedAdjunctionCounitIso` 的定义

English:
definition compactlyGeneratedAdjunctionCounitIso
  signature: (X : CompactlyGenerated.{u, u + 1})
  body: isoOfHomeo (compactlyGeneratedAdjunctionCounitHomeo X.toTop)

中文:
定义 compactlyGeneratedAdjunctionCounitIso
  签名: (X : CompactlyGenerated.{u, u + 1})
  定义体: isoOfHomeo (compactlyGeneratedAdjunctionCounitHomeo X.toTop)

Depends on / 依赖: X.toTop, compactlyGeneratedAdjunctionCounitHomeo, isoOfHomeo
-/
noncomputable def compactlyGeneratedAdjunctionCounitIso (X : CompactlyGenerated.{u, u + 1}) :
    condensedSetToCompactlyGenerated.obj (compactlyGeneratedToCondensedSet.obj X) ≅ X :=
  isoOfHomeo (compactlyGeneratedAdjunctionCounitHomeo X.toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso compactlyGeneratedAdjunction.counit
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (compactlyGeneratedAdjunctionCounitIso X).hom)

中文:
实例 :
  签名: IsIso compactlyGeneratedAdjunction.counit
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (compactlyGeneratedAdjunctionCounitIso X).hom)

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, compactlyGeneratedAdjunctionCounitIso, isIso_iff_isIso_app
-/
instance : IsIso compactlyGeneratedAdjunction.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (compactlyGeneratedAdjunctionCounitIso X).hom)

/--
Definition of `fullyFaithfulCompactlyGeneratedToCondensedSet` / `fullyFaithfulCompactlyGeneratedToCondensedSet` 的定义

English:
definition fullyFaithfulCompactlyGeneratedToCondensedSet
  signature: :
  body: compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit

中文:
定义 fullyFaithfulCompactlyGeneratedToCondensedSet
  签名: :
  定义体: compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit

Depends on / 依赖: compactlyGeneratedAdjunction, compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit
-/
noncomputable def fullyFaithfulCompactlyGeneratedToCondensedSet :
    compactlyGeneratedToCondensedSet.FullyFaithful :=
  compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit

end CondensedSet
