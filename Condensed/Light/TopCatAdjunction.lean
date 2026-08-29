/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.TopComparison
public import Mathlib.Topology.Category.Sequential
public import Mathlib.Topology.Category.LightProfinite.Sequence
/-!

# The adjunction between light condensed sets and topological spaces

This file defines the functor `lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u}` which is
left adjoint to `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for sequential spaces, and we conclude that the functor
`topCatToLightCondSet` is fully faithful when restricted to sequential spaces.
-/

@[expose] public section

universe u

open LightCondensed LightCondSet CategoryTheory LightProfinite

namespace LightCondSet

variable (X : LightCondSet.{u})

set_option backward.privateInPublic true in
/--
Definition of `coinducingCoprod` / `coinducingCoprod` 的定义

English:
definition coinducingCoprod
  signature: :
  body: fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i

中文:
定义 coinducingCoprod
  签名: :
  定义体: fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i
-/
private def coinducingCoprod :
    (Σ (i : (S : LightProfinite.{u}) × X.obj.obj ⟨S⟩), i.fst) ->
      X.obj.obj ⟨LightProfinite.of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ => X.obj.map ((of PUnit.{u + 1}).const s).op i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Let `X` be a light condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from light profinite sets `S` to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `LightCondSet.coinducingCoprod` above. -/
local instance underlyingTopologicalSpace :
    TopologicalSpace (X.obj.obj ⟨LightProfinite.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/--
Definition of `toTopCat` / `toTopCat` 的定义

English:
abbreviation toTopCat
  signature: : TopCat.{u}
  body: TopCat.of (X.obj.obj ⟨LightProfinite.of PUnit⟩)

中文:
缩写 toTopCat
  签名: : 顶元素范畴.{u}
  定义体: TopCat.of (X.obj.obj ⟨LightProfinite.of PUnit⟩)

Depends on / 依赖: LightProfinite, LightProfinite.of, TopCat, TopCat.of, X.obj.obj
-/
abbrev toTopCat : TopCat.{u} := TopCat.of (X.obj.obj ⟨LightProfinite.of PUnit⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `continuous_coinducingCoprod` / 引理 `continuous_coinducingCoprod`

English:
lemma continuous_coinducingCoprod
  given: {S : LightProfinite.{u}} (x : X.obj.obj ⟨S⟩)
  proof: by
  suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

中文:
引理 continuous_coinducingCoprod
  条件: {S : LightProfinite.{u}} (x : X.obj.obj ⟨S⟩)
  证明: by
  suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

Depends on / 依赖: Continuous, LightProfinite, X.coinducingCoprod, X.obj.obj, coinducingCoprod, continuous_coinduced_rng, continuous_sigma_iff, i.fst
-/
lemma continuous_coinducingCoprod {S : LightProfinite.{u}} (x : X.obj.obj ⟨S⟩) :
    Continuous fun a => (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : LightCondSet} (f : X ⟶ Y)

/-- The map part of the functor `LightCondSet ⥤ TopCat` -/
@[simps!]
/--
Definition of `toTopCatMap` / `toTopCatMap` 的定义

English:
definition toTopCatMap
  signature: : X.toTopCat ⟶ Y.toTopCat
  body: TopCat.ofHom
  { toFun := f.hom.app ⟨LightProfinite.of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw
        [show (fun (a : S) => f.hom.app ⟨of PUnit⟩ (X.obj.map 

中文:
定义 toTopCatMap
  签名: : X.toTopCat ⟶ Y.toTopCat
  定义体: TopCat.ofHom
  { toFun := f.hom.app ⟨LightProfinite.of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw
        [show (fun (a : S) => f.hom.app ⟨of PUnit⟩ (X.obj.map 

Depends on / 依赖: Function, Function.comp_apply, LightProfinite, LightProfinite.of, NatTrans, NatTrans.naturality_apply, TopCat, TopCat.ofHom, X.obj.map, coinducingCoprod, comp_apply, continuous_coinduced_dom, continuous_coinducingCoprod, continuous_sigma, continuous_toFun, f.hom, f.hom.app, naturality_apply
-/
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.hom.app ⟨LightProfinite.of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw
        [show (fun (a : S) => f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u + 1}).const a).op x)) = _
        from funext fun a => NatTrans.naturality_apply f.hom ((of PUnit.{u + 1}).const a).op x]
      exact continuous_coinducingCoprod _ _ }

/-- The functor `LightCondSet ⥤ TopCat` -/
@[simps]
/--
Definition of `_root_.lightCondSetToTopCat` / `_root_.lightCondSetToTopCat` 的定义

English:
definition _root_.lightCondSetToTopCat
  signature: : LightCondSet.{u} ⥤ TopCat.{u} where
  body: X.toTopCat
  map f := toTopCatMap f

中文:
定义 _root_.lightCondSetToTopCat
  签名: : LightCondSet.{u} ⥤ 顶元素范畴.{u} where
  定义体: X.toTopCat
  map f := toTopCatMap f

Depends on / 依赖: X.toTopCat, toTopCat
-/
def _root_.lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u} where
  obj X := X.toTopCat
  map f := toTopCatMap f

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `topCatAdjunctionCounit` / `topCatAdjunctionCounit` 的定义

English:
definition topCatAdjunctionCounit
  signature: (X : TopCat.{u})
  body: TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

中文:
定义 topCatAdjunctionCounit
  签名: (X : 顶元素范畴.{u})
  定义体: TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

Depends on / 依赖: PUnit.unit, TopCat, TopCat.ofHom, continuity, continuous_coinduced_dom, continuous_toFun
-/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u}) : X.toLightCondSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `topCatAdjunctionCounitEquiv` / `topCatAdjunctionCounitEquiv` 的定义

English:
definition topCatAdjunctionCounitEquiv
  signature: (X : TopCat.{u})
  body: topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

中文:
定义 topCatAdjunctionCounitEquiv
  签名: (X : 顶元素范畴.{u})
  定义体: topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

Depends on / 依赖: topCatAdjunctionCounit
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u}) : X.toLightCondSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

/--
lemma `topCatAdjunctionCounit_bijective` / 引理 `topCatAdjunctionCounit_bijective`

English:
lemma topCatAdjunctionCounit_bijective
  given: (X : TopCat.{u})
  proof: (topCatAdjunctionCounitEquiv X).bijective

中文:
引理 topCatAdjunctionCounit_bijective
  条件: (X : 顶元素范畴.{u})
  证明: (topCatAdjunctionCounitEquiv X).bijective

Depends on / 依赖: bijective, topCatAdjunctionCounitEquiv
-/
lemma topCatAdjunctionCounit_bijective (X : TopCat.{u}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
@[simps hom_app]
/--
Definition of `topCatAdjunctionUnit` / `topCatAdjunctionUnit` 的定义

English:
definition topCatAdjunctionUnit
  signature: (X : LightCondSet.{u})
  body: {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← conti

中文:
定义 topCatAdjunctionUnit
  签名: (X : LightCondSet.{u})
  定义体: {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← conti
-/
noncomputable def topCatAdjunctionUnit (X : LightCondSet.{u}) : X ⟶ X.toTopCat.toLightCondSet where
  hom := {
    app S := ↾fun x => {
      toFun := fun s => X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices forall (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) => X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ => by
      ext
      simp only [Opposite.op_unop, TypeCat.Fun.toFun_apply,
        comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        TopCat.toSheafCompHausLike_obj_map, ← Functor.map_comp_apply]
      rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `topCatAdjunction` / `topCatAdjunction` 的定义

English:
definition topCatAdjunction
  signature: : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where
  body: { app := topCatAdjunctionUnit }
  counit := { app := topCatAdjunctionCounit }
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

中文:
定义 topCatAdjunction
  签名: : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where
  定义体: { app := topCatAdjunctionUnit }
  counit := { app := topCatAdjunctionCounit }
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

Depends on / 依赖: topCatAdjunctionUnit
-/
noncomputable def topCatAdjunction : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where
  unit := { app := topCatAdjunctionUnit }
  counit := { app := topCatAdjunctionCounit }
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
  signature: topCatToLightCondSet.Faithful
  body: topCatAdjunction.faithful_R_of_epi_counit_app

中文:
实例 :
  签名: topCatToLightCondSet.忠实
  定义体: topCatAdjunction.faithful_R_of_epi_counit_app

Depends on / 依赖: Int.inductionOn, faithful_R_of_epi_counit_app, inductionOn, topCatAdjunction, topCatAdjunction.faithful_R_of_epi_counit_app
-/
instance : topCatToLightCondSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open Sequential

instance (X : LightCondSet.{u}) : SequentialSpace X.toTopCat := by
  apply SequentialSpace.coinduced

instance (X : LightCondSet.{u}) : SequentialSpace (lightCondSetToTopCat.obj X) :=
  inferInstanceAs (SequentialSpace X.toTopCat)

/--
Definition of `lightCondSetToSequential` / `lightCondSetToSequential` 的定义

English:
definition lightCondSetToSequential
  signature: : LightCondSet.{u} ⥤ Sequential.{u} where
  body: Sequential.of (lightCondSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

中文:
定义 lightCondSetToSequential
  签名: : LightCondSet.{u} ⥤ Sequential.{u} where
  定义体: Sequential.of (lightCondSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

Depends on / 依赖: Int.inductionOn, Sequential, Sequential.of, inductionOn, lightCondSetToTopCat, lightCondSetToTopCat.obj
-/
def lightCondSetToSequential : LightCondSet.{u} ⥤ Sequential.{u} where
  obj X := Sequential.of (lightCondSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

/--
Definition of `sequentialToLightCondSet` / `sequentialToLightCondSet` 的定义

English:
definition sequentialToLightCondSet
  signature: :
  body: sequentialToTop ⋙ topCatToLightCondSet

中文:
定义 sequentialToLightCondSet
  签名: :
  定义体: sequentialToTop ⋙ topCatToLightCondSet

Depends on / 依赖: sequentialToTop, topCatToLightCondSet
-/
noncomputable def sequentialToLightCondSet :
    Sequential.{u} ⥤ LightCondSet.{u} :=
  sequentialToTop ⋙ topCatToLightCondSet

/--
Definition of `sequentialAdjunction` / `sequentialAdjunction` 的定义

English:
definition sequentialAdjunction
  signature: :
  body: topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := sequentialToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulSequentialToTop
    (Iso.refl _) (Iso.refl _)

中文:
定义 sequentialAdjunction
  签名: :
  定义体: topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := sequentialToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulSequentialToTop
    (Iso.refl _) (Iso.refl _)

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.id, Iso.refl, fullyFaithfulSequentialToTop, restrictFullyFaithful, sequentialToTop, topCatAdjunction, topCatAdjunction.restrictFullyFaithful
-/
noncomputable def sequentialAdjunction :
    lightCondSetToSequential ⊣ sequentialToLightCondSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := sequentialToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulSequentialToTop
    (Iso.refl _) (Iso.refl _)

/--
Definition of `sequentialAdjunctionHomeo` / `sequentialAdjunctionHomeo` 的定义

English:
definition sequentialAdjunctionHomeo
  signature: (X : TopCat.{0}) [SequentialSpace X]
  body: topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply SeqContinuous.continuous
    unfold SeqContinuous
    intro f p h
    let g := (topCatAdjunctionCounitEquiv X).invFun ∘ (OnePoint.continuousMapMkNat f p h)
    change Filter.Tendsto (fun n : Nat => g n) _ _
    erw [← OnePoint.continu

中文:
定义 sequentialAdjunctionHomeo
  签名: (X : 顶元素范畴.{0}) [Sequential空间 X]
  定义体: topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply SeqContinuous.continuous
    unfold SeqContinuous
    intro f p h
    let g := (topCatAdjunctionCounitEquiv X).invFun ∘ (OnePoint.continuousMapMkNat f p h)
    change Filter.Tendsto (fun n : Nat => g n) _ _
    erw [← OnePoint.continu

Depends on / 依赖: topCatAdjunctionCounitEquiv
-/
noncomputable def sequentialAdjunctionHomeo (X : TopCat.{0}) [SequentialSpace X] :
    X.toLightCondSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply SeqContinuous.continuous
    unfold SeqContinuous
    intro f p h
    let g := (topCatAdjunctionCounitEquiv X).invFun ∘ (OnePoint.continuousMapMkNat f p h)
    change Filter.Tendsto (fun n : Nat => g n) _ _
    erw [← OnePoint.continuous_iff_from_nat]
    let x : X.toLightCondSet.obj.obj ⟨(Natunion{∞})⟩ := OnePoint.continuousMapMkNat f p h
    exact continuous_coinducingCoprod X.toLightCondSet x

/--
Definition of `sequentialAdjunctionCounitIso` / `sequentialAdjunctionCounitIso` 的定义

English:
definition sequentialAdjunctionCounitIso
  signature: (X : Sequential.{0})
  body: isoOfHomeo (sequentialAdjunctionHomeo X.toTop)

中文:
定义 sequentialAdjunctionCounitIso
  签名: (X : Sequential.{0})
  定义体: isoOfHomeo (sequentialAdjunctionHomeo X.toTop)

Depends on / 依赖: X.toTop, isoOfHomeo, sequentialAdjunctionHomeo
-/
noncomputable def sequentialAdjunctionCounitIso (X : Sequential.{0}) :
    lightCondSetToSequential.obj (sequentialToLightCondSet.obj X) ≅ X :=
  isoOfHomeo (sequentialAdjunctionHomeo X.toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso sequentialAdjunction.{0}.counit
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (sequentialAdjunctionCounitIso X).hom)

中文:
实例 :
  签名: 是同构 sequentialAdjunction.{0}.counit
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (sequentialAdjunctionCounitIso X).hom)

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, isIso_iff_isIso_app, sequentialAdjunctionCounitIso
-/
instance : IsIso sequentialAdjunction.{0}.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (sequentialAdjunctionCounitIso X).hom)

/--
Definition of `fullyFaithfulSequentialToLightCondSet` / `fullyFaithfulSequentialToLightCondSet` 的定义

English:
definition fullyFaithfulSequentialToLightCondSet
  signature: :
  body: sequentialAdjunction.fullyFaithfulROfIsIsoCounit

中文:
定义 fullyFaithfulSequentialToLightCondSet
  签名: :
  定义体: sequentialAdjunction.fullyFaithfulROfIsIsoCounit

Depends on / 依赖: fullyFaithfulROfIsIsoCounit, sequentialAdjunction, sequentialAdjunction.fullyFaithfulROfIsIsoCounit
-/
noncomputable def fullyFaithfulSequentialToLightCondSet :
    sequentialToLightCondSet.{0}.FullyFaithful :=
  sequentialAdjunction.fullyFaithfulROfIsIsoCounit

end LightCondSet
