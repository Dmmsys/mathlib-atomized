/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Tactic.DepRewrite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Relative Normalization

Given a qcqs morphism `f : X ⟶ Y`, we define the relative normalization `f.normalization`,
along with the maps that `f` factor into:
- `f.toNormalization : X ⟶ f.normalization`: a dominant morphism
- `f.fromNormalization : f.normalization ⟶ Y`: an integral morphism

It satisfies the universal property:
For any factorization `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
The factorization map is `AlgebraicGeometry.Scheme.Hom.normalizationDesc`, and the uniqueness result
is `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext`.

We also show that normalization commutes with disjoint unions and smooth base change.

-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `normalizationDiagram` / `normalizationDiagram` 的定义

English:
definition normalizationDiagram
  signature: : Y.Opensᵒᵖ ⥤ CommRingCat where
  body: letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx => by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rf

中文:
定义 normalizationDiagram
  签名: : Y.Opensᵒᵖ ⥤ CommRingCat where
  定义体: letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx => by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rf

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsScal, Opposite, Opposite.op_surjective, U.unop, X.presheaf.map, Y.presheaf.map, algebraize, f.app, f.appLE, f.preimage_mono, hom.restrict, hom.toAlgebra, homOfLE, i.unop.le, integralClosure, op_surjective, preimage_mono, presheaf
-/
def normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx => by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_mono i.unop.le)).hom]
have : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' by
        simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]; rfl
      have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le)]; rw [op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

/--
Definition of `normalizationDiagramMap` / `normalizationDiagramMap` 的定义

English:
definition normalizationDiagramMap
  signature: : Y.presheaf ⟶ f.normalizationDiagram where
  body: letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

中文:
定义 normalizationDiagramMap
  签名: : Y.presheaf ⟶ f.normalizationDiagram where
  定义体: letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Subtype, Subtype.ext, U.unop, algebraMap, f.app, f.naturality, hom.toAlgebra, integralClosure, naturality, toAlgebra
-/
def normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

variable [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coequifibered_normalizationDiagramMap` / 引理 `coequifibered_normalizationDiagramMap`

English:
lemma coequifibered_normalizationDiagramMap
  proof: by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X

中文:
引理 coequifibered_normalizationDiagramMap
  证明: by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X

Depends on / 依赖: Algebra, U.basicOpen, Y.basicO, Y.basicOpen, Y.basicOpen_le, basicO, basicOpen, basicOpen_le, coequifibered_iff_forall_isLocalizationAway, coequifibered_iff_forall_isLocalizationAway.mpr, decidable_of_iff, f.app, hom.toAlgebra, homOfLE, integralClosure, normalizationDiagram, toAlgebra, yonedaEquiv
-/
lemma coequifibered_normalizationDiagramMap :
    ((toOpensFunctor Y).op.whiskerLeft f.normalizationDiagramMap).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) :=
    ((normalizationDiagram f).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ U.1)) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  change IsLocalization.Away ((algebraMap Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) r)
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  let : Algebra ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
.of_algebraMap_eq' by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE, AffineZariskiSite.basicOpen]
  have : IsScalarTower (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := .of_algebraMap_eq' rfl
  exact IsLocalization.Away.integralClosure r

@[deprecated (since := "2026-02-01")]
alias preservesLocalization_normalizationDiagramMap := coequifibered_normalizationDiagramMap

/--
Definition of `normalizationGlueData` / `normalizationGlueData` 的定义

English:
definition normalizationGlueData
  body: relativeGluingData f.coequifibered_normalizationDiagramMap

中文:
定义 normalizationGlueData
  定义体: relativeGluingData f.coequifibered_normalizationDiagramMap

Depends on / 依赖: coequifibered_normalizationDiagramMap, f.coequifibered_normalizationDiagramMap, relativeGluingData
-/
def normalizationGlueData := relativeGluingData f.coequifibered_normalizationDiagramMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (f.normalizationGlueData.functor ⋙ Scheme.forget).IsLocallyDirected
  body: Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

中文:
实例 :
  签名: (f.normalizationGlueData.functor ⋙ Scheme.forget).IsLocallyDirected
  定义体: Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

Depends on / 依赖: Cover.RelativeGluingData.instIsLocallyDirectedI, RelativeGluingData
-/
instance : (f.normalizationGlueData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- Given `f : X ⟶ Y`, `f.normalization` is the relative normalization of `Y` in `X`. -/
@[stacks 035H]
/--
Definition of `normalization` / `normalization` 的定义

English:
definition normalization
  signature: : Scheme
  body: f.normalizationGlueData.glued

中文:
定义 normalization
  签名: : Scheme
  定义体: f.normalizationGlueData.glued

Depends on / 依赖: f.normalizationGlueData.glued, normalizationGlueData
-/
def normalization : Scheme := f.normalizationGlueData.glued

/--
Definition of `normalizationOpenCover` / `normalizationOpenCover` 的定义

English:
definition normalizationOpenCover
  signature: : f.normalization.OpenCover
  body: f.normalizationGlueData.cover

中文:
定义 normalizationOpenCover
  签名: : f.normalization.OpenCover
  定义体: f.normalizationGlueData.cover

Depends on / 依赖: f.normalizationGlueData.cover, normalizationGlueData
-/
def normalizationOpenCover : f.normalization.OpenCover :=
  f.normalizationGlueData.cover

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toNormalization` / `toNormalization` 的定义

English:
definition toNormalization
  signature: : X ⟶ f.normalization
  body: Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U => letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
.val.toRingHom) ≫ f.n

中文:
定义 toNormalization
  签名: : X ⟶ f.normalization
  定义体: Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U => letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
.val.toRingHom) ≫ f.n

Depends on / 依赖: AffineZariskiSite, CommRingCat, CommRingCat.ofHom, Cover.trans, OpenCover, Scheme, Scheme.OpenCover.glueMorphismsOfLocallyDirected, Spec.map, X.homOfLE, Y.AffineZariskiSite, directedCover, f.app, f.normalizationOpenCover.f, glueMorphismsOfLocallyDirected, hom.toAlgebra, homOfLE, integralClosure, normalizationOpenCover, pullbackRestrictIsoRestrict, toAlgebra
-/
def toNormalization : X ⟶ f.normalization :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U => letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
.val.toRingHom) ≫ f.normalizationOpenCover.f U) fun {U V : Y.AffineZariskiSite} i => by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq]; rw [reassoc_of% this]; rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]; rw [← Spec.map_comp_assoc]
  dsimp [normalizationOpenCover]
  rw [← colimit.w f.normalizationGlueData.functor i]
  dsimp [normalizationGlueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ι_toNormalization` / 引理 `ι_toNormalization`

English:
lemma ι_toNormalization
  given: (U : Y.affineOpens)
  proof: (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom]; rw [← Cat

中文:
引理 ι_toNormalization
  条件: (U : Y.affineOpens)
  证明: (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom]; rw [← Cat

Depends on / 依赖: f.app, hom.toAlgebra, toAlgebra
-/
lemma ι_toNormalization (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom]; rw [← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ f.toNormalization
  · congr 1; simp
  delta toNormalization
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

/--
Definition of `fromNormalization` / `fromNormalization` 的定义

English:
definition fromNormalization
  signature: : f.normalization ⟶ Y
  body: f.normalizationGlueData.toBase

@[reassoc]

中文:
定义 fromNormalization
  签名: : f.normalization ⟶ Y
  定义体: f.normalizationGlueData.toBase

@[reassoc]

Depends on / 依赖: f.normalizationGlueData.toBase, normalizationGlueData, toBase
-/
def fromNormalization : f.normalization ⟶ Y :=
  f.normalizationGlueData.toBase

@[reassoc]
/--
lemma `ι_fromNormalization` / 引理 `ι_fromNormalization`

English:
lemma ι_fromNormalization
  given: (U : Y.affineOpens)
  proof: colimit.ι_desc _ _

中文:
引理 ι_fromNormalization
  条件: (U : Y.affineOpens)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
lemma ι_fromNormalization (U : Y.affineOpens) :
    f.normalizationOpenCover.f U ≫ f.fromNormalization =
      Spec.map (f.normalizationDiagramMap.app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `fromNormalization_preimage` / 引理 `fromNormalization_preimage`

English:
lemma fromNormalization_preimage
  given: (U : Y.affineOpens)
  proof: by
  simpa using! f.normalizationGlueData.toBase_preimage_eq_opensRange_ι U

中文:
引理 fromNormalization_preimage
  条件: (U : Y.affineOpens)
  证明: by
  simpa using! f.normalizationGlueData.toBase_preimage_eq_opensRange_ι U

Depends on / 依赖: f.normalizationGlueData.toBase_preimage_eq_opensRange_, normalizationGlueData
-/
lemma fromNormalization_preimage (U : Y.affineOpens) :
    f.fromNormalization ⁻¹ᵁ U = (f.normalizationOpenCover.f U).opensRange := by
  simpa using! f.normalizationGlueData.toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalization_fromNormalization` / 引理 `toNormalization_fromNormalization`

English:
lemma toNormalization_fromNormalization
  proof: by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U => ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization]; rw [← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec 

中文:
引理 toNormalization_fromNormalization
  证明: by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U => ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization]; rw [← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec 

Depends on / 依赖: Scheme, Scheme.Cover.hom_ext, Spec.map, Spec.map_comp_assoc, X.openCoverOfIsOpenCover, f.app, f.base, fromSpec, hom_ext, iSup_affineOpens_eq_top, map_comp_assoc, openCoverOfIsOpenCover
-/
lemma toNormalization_fromNormalization :
    f.toNormalization ≫ f.fromNormalization = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U => ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization]; rw [← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegralHom f.fromNormalization
  body: by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← Morphis

中文:
实例 :
  签名: Is整数egralHom f.fromNormalization
  定义体: by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← Morphis

Depends on / 依赖: IsIntegral, IsIntegralHom, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, MorphismProperty.cancel_right_of_respectsIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, e.inv, f.fromNormalization, f.fromNormalization_preimage, f.normalizationDiagramMap.app, f.normalizationOpenCover.f, fromNormalization, fromNormalization_preimage, hom.IsIntegral, iSup_affineOpens_eq_top
-/
instance : IsIntegralHom f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom e.inv]; rw [← MorphismProperty.cancel_right_of_respectsIso @IsIntegralHom _ U.2.isoSpec.hom]
  have : (f.normalizationDiagramMap.app (.op U)).hom.IsIntegral := by
    let := (f.app U).hom.toAlgebra
    change (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  convert! IsIntegralHom.SpecMap_iff.mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, ι_fromNormalization]

set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of the relative normalization on the preimage of an affine open is isomorphic to
the integral closure. -/
noncomputable
/--
Definition of `normalizationObjIso` / `normalizationObjIso` 的定义

English:
definition normalizationObjIso
  signature: {U : Y.Opens} (hU : IsAffineOpen U)
  body: (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalization.presheaf.mapIso (eqToIso
    (by simpa using! (f.fromNormalization_preimage ⟨U, hU⟩).symm)).op ≪≫
  (f.normalizationOpenCover.f ⟨U, hU⟩).appIso ⊤ ≪≫ Sche

中文:
定义 normalizationObjIso
  签名: {U : Y.Opens} (hU : IsAffineOpen U)
  定义体: (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalization.presheaf.mapIso (eqToIso
    (by simpa using! (f.fromNormalization_preimage ⟨U, hU⟩).symm)).op ≪≫
  (f.normalizationOpenCover.f ⟨U, hU⟩).appIso ⊤ ≪≫ Sche

Depends on / 依赖: f.app, hom.toAlgebra, toAlgebra
-/
def normalizationObjIso {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalization.presheaf.mapIso (eqToIso
    (by simpa using! (f.fromNormalization_preimage ⟨U, hU⟩).symm)).op ≪≫
  (f.normalizationOpenCover.f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toNormalization_app_preimage` / 引理 `toNormalization_app_preimage`

English:
lemma toNormalization_app_preimage
  given: (U : Y.affineOpens)
  proof: (f.app U.1).hom.toAlgebra
    dsimp% f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      (f.normalizationObjIso U.2).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  let :

中文:
引理 toNormalization_app_preimage
  条件: (U : Y.affineOpens)
  证明: (f.app U.1).hom.toAlgebra
    dsimp% f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      (f.normalizationObjIso U.2).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  let :

Depends on / 依赖: f.app, hom.toAlgebra, toAlgebra
-/
lemma toNormalization_app_preimage (U : Y.affineOpens) :
    let := (f.app U.1).hom.toAlgebra
    dsimp% f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      (f.normalizationObjIso U.2).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  let := (f.app U.1).hom.toAlgebra
  dsimp [normalizationObjIso]
  change _ = f.normalization.presheaf.map (eqToHom (by simp [fromNormalization_preimage])).op ≫
      ((f.normalizationOpenCover.f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op
  have H : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ f.toNormalization) ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert! congr($(Scheme.Hom.congr_app (f.ι_toNormalization U) (f.fromNormalization ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp]; rw [← Functor.map_inv]; rw [inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `fromNormalization_app` / 引理 `fromNormalization_app`

English:
lemma fromNormalization_app
  given: {U : Y.Opens} (hU : IsAffineOpen U)
  proof: by
  let := (f.app U).hom.toAlgebra
  have : IsIso (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)) :=
    Scheme.Hom.isIso_app _ _ (by simp [← fromNormalization_preimage])
  have H : ⊤ = ((normalizationOpenCover f).f ⟨U, hU⟩ ≫ fromNormalization f) ⁻¹ᵁ U := by
    rw [f.ι_fro

中文:
引理 fromNormalization_app
  条件: {U : Y.Opens} (hU : IsAffineOpen U)
  证明: by
  let := (f.app U).hom.toAlgebra
  have : IsIso (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)) :=
    Scheme.Hom.isIso_app _ _ (by simp [← fromNormalization_preimage])
  have H : ⊤ = ((normalizationOpenCover f).f ⟨U, hU⟩ ≫ fromNormalization f) ⁻¹ᵁ U := by
    rw [f.ι_fro

Depends on / 依赖: Scheme, Scheme.Hom.comp_app, Scheme.Hom.congr_app, Scheme.Hom.isIso_app, cancel_mono, comp_app, congr_app, f.app, f.fromNormalization, fromNormalization, fromNormalization_preimage, hom.toAlgebra, isIso_app, normalizationOpenCover, toAlgebra
-/
lemma fromNormalization_app {U : Y.Opens} (hU : IsAffineOpen U) :
    f.fromNormalization.app U = CommRingCat.ofHom (algebraMap _ _) ≫
      (f.normalizationObjIso hU).inv := by
  let := (f.app U).hom.toAlgebra
  have : IsIso (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)) :=
    Scheme.Hom.isIso_app _ _ (by simp [← fromNormalization_preimage])
  have H : ⊤ = ((normalizationOpenCover f).f ⟨U, hU⟩ ≫ fromNormalization f) ⁻¹ᵁ U := by
    rw [f.ι_fromNormalization]; simp
  rw [← cancel_mono (((normalizationOpenCover f).f ⟨U]; rw [hU⟩).app (f.fromNormalization ⁻¹ᵁ U))]; rw [← Scheme.Hom.comp_app]; rw [Scheme.Hom.congr_app (f.ι_fromNormalization ⟨U]; rw [hU⟩) U]; rw [← cancel_mono (((normalizationOpenCover f).X ⟨U]; rw [hU⟩).presheaf.map (eqToHom H).op)]
  dsimp [normalizationObjIso]
  rw [IsAffineOpen.fromSpec_app_self]
  simp only [app_eq_appLE, Category.assoc, map_appLE, appLE_map]
  simp [Scheme.Hom.appLE, ← ΓSpecIso_inv_naturality]
  rfl

/--
lemma `normalizationObjIso_hom_val` / 引理 `normalizationObjIso_hom_val`

English:
lemma normalizationObjIso_hom_val
  given: {U : Y.Opens} (hU : IsAffineOpen U)
  proof: (f.app U).hom.toAlgebra
    (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
    f.toNormalization.appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [appLE]; rw [f.toNormalization_app_preimage ⟨U]; rw [hU⟩]; rw [Category.assoc]
  simp [← Functor.map_comp]
 

中文:
引理 normalizationObjIso_hom_val
  条件: {U : Y.Opens} (hU : IsAffineOpen U)
  证明: (f.app U).hom.toAlgebra
    (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
    f.toNormalization.appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [appLE]; rw [f.toNormalization_app_preimage ⟨U]; rw [hU⟩]; rw [Category.assoc]
  simp [← Functor.map_comp]
 

Depends on / 依赖: f.app, hom.toAlgebra, toAlgebra
-/
lemma normalizationObjIso_hom_val {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
    f.toNormalization.appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [appLE]; rw [f.toNormalization_app_preimage ⟨U]; rw [hU⟩]; rw [Category.assoc]
  simp [← Functor.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[stacks 03GP]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegralHom
  signature: f] : IsIso f.toNormalization
  body: by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U => ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pul

中文:
实例 [IsIntegralHom
  签名: f] : IsIso f.toNormalization
  定义体: by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U => ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pul

Depends on / 依赖: Hom.coe_opensRange, Hom.opensRange_pullbackFst, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, Scheme, Scheme.Hom.comp_preimage, cancel_left_of_respectsIso, coe_opensRange, comp_preimage, convert_t, f.app, f.fromNormalization_preimage, f.normalizationOpenCover, f.normalizationOpenCover.f, f.toNormalization, fromNormalization_preimage
-/
instance [IsIntegralHom f] : IsIso f.toNormalization := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U => ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pullbackFst, ← f.fromNormalization_preimage, ← Scheme.Hom.comp_preimage])
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _)
    (e ≪≫ (U.2.preimage f).isoSpec).inv]
  let := (f.app U.1).hom.toAlgebra
  convert_to! IsIso (Spec.map (CommRingCat.ofHom
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom))
  · rw [← cancel_mono (f.normalizationOpenCover.f U), ← cancel_epi (U.2.preimage f).isoSpec.hom]
    simp [e, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom,
      Hom.ι_toNormalization]
  have : integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
    rw [integralClosure_eq_top_iff]; rw [← algebraMap_isIntegral_iff]; rw [RingHom.algebraMap_toAlgebra]
    exact IsIntegralHom.isIntegral_app _ _ U.2
  rw [this]
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso (Subalgebra.topEquiv
    (R := Γ(Y, U.1)) (A := ↑Γ(X, f ⁻¹ᵁ U.1))).toCommRingCatIso.op).hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffineHom
  signature: f] : IsAffineHom f.toNormalization
  body: by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

中文:
实例 [IsAffineHom
  签名: f] : IsAffineHom f.toNormalization
  定义体: by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

Depends on / 依赖: Hom.toNormalization_fromNormalization, IsAffineHom, IsSeparated, MorphismProperty, MorphismProperty.of_postcomp, f.fromNormalization, fromNormalization, infer_instance, of_postcomp, toNormalization_fromNormalization
-/
instance [IsAffineHom f] : IsAffineHom f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiCompact f.toNormalization
  body: by
  apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

中文:
实例 :
  签名: QuasiCompact f.toNormalization
  定义体: by
  apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

Depends on / 依赖: Hom.toNormalization_fromNormalization, MorphismProperty, MorphismProperty.of_postcomp, QuasiCompact, QuasiSeparated, f.fromNormalization, fromNormalization, infer_instance, of_postcomp, toNormalization_fromNormalization
-/
instance : QuasiCompact f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiSeparated f.toNormalization
  body: by
  suffices QuasiSeparated (Hom.toNormalization f ≫ Hom.fromNormalization f) from
    .of_comp _ f.fromNormalization
  rw [Hom.toNormalization_fromNormalization]
  infer_instance

@[simp]

中文:
实例 :
  签名: QuasiSeparated f.toNormalization
  定义体: by
  suffices QuasiSeparated (Hom.toNormalization f ≫ Hom.fromNormalization f) from
    .of_comp _ f.fromNormalization
  rw [Hom.toNormalization_fromNormalization]
  infer_instance

@[simp]

Depends on / 依赖: Hom.fromNormalization, Hom.toNormalization, Hom.toNormalization_fromNormalization, QuasiSeparated, f.fromNormalization, fromNormalization, infer_instance, of_comp, toNormalization, toNormalization_fromNormalization
-/
instance : QuasiSeparated f.toNormalization := by
  suffices QuasiSeparated (Hom.toNormalization f ≫ Hom.fromNormalization f) from
    .of_comp _ f.fromNormalization
  rw [Hom.toNormalization_fromNormalization]
  infer_instance

@[simp]
/--
lemma `ker_toNormalization` / 引理 `ker_toNormalization`

English:
lemma ker_toNormalization
  statement: f.toNormalization.ker = ⊥
  proof: by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => ⟨f.fromNormalization ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U => ?_
  simp only [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injecti

中文:
引理 ker_toNormalization
  结论: f.toNormalization.ker = ⊥
  证明: by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => ⟨f.fromNormalization ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U => ?_
  simp only [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injecti

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_iff_injective_of_preservesPullback, IdealSheafData, IdealSheafData.ideal_bot, IsOpenCover, MorphismProperty, MorphismProperty.cancel_left_of_respec, MorphismProperty.monomorphisms, Pi.bot_apply, RingHom, RingHom.injective_iff_ker_eq_bot, Scheme, Scheme.IdealSheafData.ext_of_iSup_eq_top, TopologicalSpace, TopologicalSpace.IsOpenCover.comap, Y.affineOpens, affineOpens, bot_apply, cancel_left_of_respec, eqToHom_op
-/
lemma ker_toNormalization : f.toNormalization.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => ⟨f.fromNormalization ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U => ?_
  simp only [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]; rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback]; rw [← MorphismProperty.monomorphisms]
  simp only [toNormalization_app_preimage,
    eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso]
  rw [MorphismProperty.monomorphisms]; rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact Subtype.val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDominant f.toNormalization
  body: by
  have := congr(($(f.ker_toNormalization).support : Set f.normalization))
  rw [IdealSheafData.support_bot]; rw [Scheme.Hom.support_ker]; rw [TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

中文:
实例 :
  签名: IsDominant f.toNormalization
  定义体: by
  have := congr(($(f.ker_toNormalization).support : Set f.normalization))
  rw [IdealSheafData.support_bot]; rw [Scheme.Hom.support_ker]; rw [TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

Depends on / 依赖: Closeds, IdealSheafData, IdealSheafData.support_bot, Scheme, Scheme.Hom.support_ker, TopologicalSpace, TopologicalSpace.Closeds.coe_top, coe_top, dense_iff_closure_eq, dense_iff_closure_eq.mpr, f.ker_toNormalization, f.normalization, ker_toNormalization, normalization, support, support_bot, support_ker
-/
instance : IsDominant f.toNormalization := by
  have := congr(($(f.ker_toNormalization).support : Set f.normalization))
  rw [IdealSheafData.support_bot]; rw [Scheme.Hom.support_ker]; rw [TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[stacks 0AXN]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsReduced
  signature: X] : IsReduced f.normalization
  body: have (i : _) : IsReduced ((normalizationOpenCover f).X i) := by
    have : _root_.IsReduced ((normalizationDiagram f).obj (.op i.1)) :=
      let := (f.app i.1).hom.toAlgebra
      isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
    dsimp [normalizationOpenCover, normalizationGlueDat

中文:
实例 [IsReduced
  签名: X] : IsReduced f.normalization
  定义体: have (i : _) : IsReduced ((normalizationOpenCover f).X i) := by
    have : _root_.IsReduced ((normalizationDiagram f).obj (.op i.1)) :=
      let := (f.app i.1).hom.toAlgebra
      isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
    dsimp [normalizationOpenCover, normalizationGlueDat

Depends on / 依赖: IsReduced, Subalgebra, Subalgebra.val, Subtype, Subtype.val_injective, _root_, _root_.IsReduced, f.app, f.normalizationOpenCover, hom.toAlgebra, infer_instance, isReduced_of_injective, normalizationDiagram, normalizationGlueData, normalizationOpenCover, of_openCover, relativeGluingData, toAlgebra, val_injective
-/
instance [IsReduced X] : IsReduced f.normalization :=
  have (i : _) : IsReduced ((normalizationOpenCover f).X i) := by
    have : _root_.IsReduced ((normalizationDiagram f).obj (.op i.1)) :=
      let := (f.app i.1).hom.toAlgebra
      isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
    dsimp [normalizationOpenCover, normalizationGlueData, relativeGluingData]
    infer_instance
  .of_openCover _ f.normalizationOpenCover

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] : IsIntegral f.normalization
  body: have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toNormalization.continuous.continuousOn).closure
    simpa using f.toNormalization.denseRange.closure_range.symm
  isIntegral_of_irreducibleSpac

中文:
实例 [IsIntegral
  签名: X] : Is整数egral f.normalization
  定义体: have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toNormalization.continuous.continuousOn).closure
    simpa using f.toNormalization.denseRange.closure_range.symm
  isIntegral_of_irreducibleSpac

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, closure, closure_range, continuous, continuousOn, convert, denseRange, f.normalization, f.toNormalization.continuous.continuousOn, f.toNormalization.denseRange.closure_range.symm, irreducibleSpace_def, isIntegral_of_irreducibleSpace_of_isReduced, isIrreducible_univ, normalization, toNormalization
-/
instance [IsIntegral X] : IsIntegral f.normalization :=
  have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toNormalization.continuous.continuousOn).closure
    simpa using f.toNormalization.denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _

section UniversalProperty

variable {T : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an qcqs morphism `f : X ⟶ Y`, which factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
(See `normalization.hom_ext` for the uniqueness result) -/
noncomputable
/--
Definition of `normalizationDesc` / `normalizationDesc` 的定义

English:
definition normalizationDesc
  signature: (H : f = f₁ ≫ f₂)
  body: by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x => ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · algebraize [(f.app U.1).hom, (f₂.app U.1).hom,
      (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ 

中文:
定义 normalizationDesc
  签名: (H : f = f₁ ≫ f₂)
  定义体: by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x => ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · algebraize [(f.app U.1).hom, (f₂.app U.1).hom,
      (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ 

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, CommRingCat.ofHom, Hom.appLE_comp_appLE, Hom.app_eq_appLE, IsScalarTower, RingHom, RingHom.algebraMap_toAlgebra, Spec.map, algebraMap_toAlgebra, algebraize, appLE_comp_appLE, app_eq_appLE, codRestrict, colimit, colimit.desc, f.app, fromSpec, hom.codRestrict, hom_comp
-/
def normalizationDesc (H : f = f₁ ≫ f₂) : f.normalization ⟶ T := by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x => ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · algebraize [(f.app U.1).hom, (f₂.app U.1).hom,
      (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])).hom]
have : IsScalarTower Γ(Y, U.1) Γ(T, f₂ ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ U.1) := .of_algebraMap_eq' by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Hom.app_eq_appLE, Hom.appLE_comp_appLE, ← H]
    exact .algebraMap (R := Γ(Y, U.1)) (B := Γ(X, f ⁻¹ᵁ U.1)) (f₂.isIntegral_app U.1 U.2 x)
  · intros U V i
    dsimp [normalizationGlueData, relativeGluingData]
    rw [Category.comp_id]; rw [← Spec.map_comp_assoc]; rw [← (V.2.preimage f₂).map_fromSpec (U.2.preimage f₂)
      (homOfLE (f₂.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le))).op]; rw [← Spec.map_comp_assoc]
    congr 2
    ext i
    apply Subtype.ext
    dsimp [normalizationDiagram]
    simp only [← CommRingCat.comp_apply, appLE_map, map_appLE]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalization_normalizationDesc` / 引理 `toNormalization_normalizationDesc`

English:
lemma toNormalization_normalizationDesc
  given: (H : f = f₁ ≫ f₂)
  proof: by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_de

中文:
引理 toNormalization_normalizationDesc
  条件: (H : f = f₁ ≫ f₂)
  证明: by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_de

Depends on / 依赖: Scheme, Scheme.Cover.hom_ext, Scheme.Hom, Spec.map, Spec.map_comp_assoc, X.openCoverOfIsOpenCover, colimit, f.app, f.base.hom, fromSpec, hom.toAlgebra, hom_ext, iSup_affineOpens_eq_top, map_comp_assoc, normalizationDesc, normalizationOpenCover, openCoverOfIsOpenCover, preimage, toAlgebra
-/
lemma toNormalization_normalizationDesc (H : f = f₁ ≫ f₂) :
    f.toNormalization ≫ f.normalizationDesc f₁ f₂ H = f₁ := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_desc, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])) ≫
    (U.2.preimage f₂).fromSpec = (f ⁻¹ᵁ U.1).ι ≫ f₁
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `normalizationDesc_comp` / 引理 `normalizationDesc_comp`

English:
lemma normalizationDesc_comp
  given: (H : f = f₁ ≫ f₂)
  proof: by
  refine colimit.hom_ext fun U => ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc]; rw [(normalizationGlueData f).ι_toBase]; rw [Category.assoc]; rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl]; rw [← Spec.map_comp_assoc]
  dsimp [normalizationGlueData, rela

中文:
引理 normalizationDesc_comp
  条件: (H : f = f₁ ≫ f₂)
  证明: by
  refine colimit.hom_ext fun U => ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc]; rw [(normalizationGlueData f).ι_toBase]; rw [Category.assoc]; rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl]; rw [← Spec.map_comp_assoc]
  dsimp [normalizationGlueData, rela

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.comp_apply, Hom.appLE_comp_appLE, IsAffineOpen, IsAffineOpen.SpecMap_appLE_fromSpec, RingHom, RingHom.algebraMap_toAlgebra, Spec.map_comp_assoc, SpecMap_appLE_fromSpec, algebraMap_toAlgebra, appLE_comp_appLE, colimit, colimit.hom_ext, comp_apply, fromNormalization, hom_ext, le_rfl, map_comp_assoc
-/
lemma normalizationDesc_comp (H : f = f₁ ≫ f₂) :
    f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization := by
  refine colimit.hom_ext fun U => ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc]; rw [(normalizationGlueData f).ι_toBase]; rw [Category.assoc]; rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl]; rw [← Spec.map_comp_assoc]
  dsimp [normalizationGlueData, relativeGluingData, restrictIsoSpec]
  rw [Category.assoc]
  congr 2
  ext i
  dsimp [normalizationDiagram, normalizationDiagramMap, RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply]; rw [Hom.appLE_comp_appLE]; rw [app_eq_appLE]
  simp_rw [H]

instance (H : f = f₁ ≫ f₂) : IsIntegralHom (f.normalizationDesc f₁ f₂ H) := by
  have : IsIntegralHom (f.normalizationDesc f₁ f₂ H ≫ f₂) := by
    rw [f.normalizationDesc_comp]; infer_instance
  exact .of_comp _ f₂

set_option backward.isDefEq.respectTransparency false in
/--
lemma `normalization.hom_ext` / 引理 `normalization.hom_ext`

English:
lemma normalization.hom_ext
  statement: (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
  proof: by
  apply f.normalizationOpenCover.hom_ext _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormali

中文:
引理 normalization.hom_ext
  结论: (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
  证明: by
  apply f.normalizationOpenCover.hom_ext _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormali

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsAffineHom, Subtype, Subtype.val_injective, eq_of_SpecMap_comp_eq_of_isAffineOpen, f.app, f.normalizationOpenCover.hom_ext, hom.toAlgebra, hom_ext, integralClosure, normalizationOpenCover, of_comp, toAlgebra, toNormalization, toRingHom, val.toRingHom, val_injective
-/
lemma normalization.hom_ext (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
    (H₁ : f.toNormalization ≫ f₁ = f.toNormalization ≫ f₂)
    (hf₁ : f₁ ≫ g = f.fromNormalization) (hf₂ : f₂ ≫ g = f.fromNormalization) : f₁ = f₂ := by
  apply f.normalizationOpenCover.hom_ext _ _ fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormalization f ≫ f₁
  have hf₀ : f₀ = toNormalization f ≫ f₂ := H₁
  refine eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom)
    Subtype.val_injective _ (U.2.preimage g) ?_ ?_ ?_
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₁, ι_fromNormalization]; simp
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₂, ι_fromNormalization]; simp
  · have h₁ : f ⁻¹ᵁ U.1 <= f₀ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, f₀, Category.assoc,
        hf₁, toNormalization_fromNormalization]; rfl
    have h₁' : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂, toNormalization_fromNormalization]
    have h₂ : fromNormalization f ⁻¹ᵁ U.1 = f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₁]
    have h₂' : fromNormalization f ⁻¹ᵁ U.1 = f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂]
    have h₃ : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ fromNormalization f ⁻¹ᵁ U.1 := by
      simp [← Scheme.Hom.comp_preimage]
    trans Spec.map (f₀.appLE (g ⁻¹ᵁ U.val) (f ⁻¹ᵁ U.val) h₁) ≫ (U.prop.preimage g).fromSpec
    · simp only [AlgHom.toRingHom_eq_coe, comp_appLE, Spec.map_comp, Category.assoc, f₀]
      rw [app_eq_appLE]; rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₁ ⁻¹ᵁ g ⁻¹ᵁ U.val) (f ⁻¹ᵁ U.val) h₁ =
        f.normalization.presheaf.map (eqToHom h₂).op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.val) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this]; rw [f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top, normalizationObjIso, normalizationDiagram]
      #adaptation_note /-- Before #36613, the following simp call was not needed. -/
      simp [← Spec.map_comp_assoc, -Spec.map_comp]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, hf₀, comp_appLE, Spec.map_comp, Category.assoc,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁'.le =
        f.normalization.presheaf.map (eqToHom h₂').op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this]; rw [f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top, normalizationObjIso, normalizationDiagram]
      #adaptation_note /-- Before #36613, the following simp call was not needed. -/
      simp [← Spec.map_comp_assoc, -Spec.map_comp]
      rfl

end UniversalProperty

section Coproduct

variable {U V : Scheme} {iU : U ⟶ X} {iV : V ⟶ X} (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact iU] [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `normalizationCoprodIso` / `normalizationCoprodIso` 的定义

English:
definition normalizationCoprodIso
  signature: :
  body: coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU 

中文:
定义 normalizationCoprodIso
  签名: :
  定义体: coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU 

Depends on / 依赖: coprod, coprod.desc
-/
noncomputable def normalizationCoprodIso :
    (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅ f.normalization where
  hom := coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU ≫ f).toNormalization (iV ≫ f).toNormalization)
(coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) by
    simp only [← Iso.inv_comp_eq, Category.assoc]
    apply coprod.hom_ext <;> simp
  hom_inv_id := by
    ext
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iU ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inl :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.left⟩
      simp [reassoc_of% H]
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iV ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inr :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.right⟩
      simp [reassoc_of% H]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization ?_ (by simp) (by simp)
    rw [← cancel_epi (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).inv]
    apply coprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalization_inl_normalizationCoprodIso_hom` / 引理 `toNormalization_inl_normalizationCoprodIso_hom`

English:
lemma toNormalization_inl_normalizationCoprodIso_hom
  proof: by
  simp [Scheme.Hom.normalizationCoprodIso]

中文:
引理 toNormalization_inl_normalizationCoprodIso_hom
  证明: by
  simp [Scheme.Hom.normalizationCoprodIso]

Depends on / 依赖: Scheme, Scheme.Hom.normalizationCoprodIso, normalizationCoprodIso
-/
lemma toNormalization_inl_normalizationCoprodIso_hom :
    (iU ≫ f).toNormalization ≫ coprod.inl ≫ (f.normalizationCoprodIso e).hom =
      iU ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalization_inr_normalizationCoprodIso_hom` / 引理 `toNormalization_inr_normalizationCoprodIso_hom`

English:
lemma toNormalization_inr_normalizationCoprodIso_hom
  proof: by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]

中文:
引理 toNormalization_inr_normalizationCoprodIso_hom
  证明: by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme, Scheme.Hom.normalizationCoprodIso, normalizationCoprodIso
-/
lemma toNormalization_inr_normalizationCoprodIso_hom :
    (iV ≫ f).toNormalization ≫ coprod.inr ≫ (f.normalizationCoprodIso e).hom =
      iV ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]
/--
lemma `inl_toNormalization_normalizationCoprodIso_inv` / 引理 `inl_toNormalization_normalizationCoprodIso_inv`

English:
lemma inl_toNormalization_normalizationCoprodIso_inv
  proof: by
  simp [← toNormalization_inl_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]

中文:
引理 inl_toNormalization_normalizationCoprodIso_inv
  证明: by
  simp [← toNormalization_inl_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]

Depends on / 依赖: toNormalization_inl_normalizationCoprodIso_hom_assoc
-/
lemma inl_toNormalization_normalizationCoprodIso_inv :
    iU ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iU ≫ f).toNormalization ≫ coprod.inl := by
  simp [← toNormalization_inl_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]
/--
lemma `inr_toNormalization_normalizationCoprodIso_inv` / 引理 `inr_toNormalization_normalizationCoprodIso_inv`

English:
lemma inr_toNormalization_normalizationCoprodIso_inv
  proof: by
  simp [← toNormalization_inr_normalizationCoprodIso_hom_assoc f e]

中文:
引理 inr_toNormalization_normalizationCoprodIso_inv
  证明: by
  simp [← toNormalization_inr_normalizationCoprodIso_hom_assoc f e]

Depends on / 依赖: toNormalization_inr_normalizationCoprodIso_hom_assoc
-/
lemma inr_toNormalization_normalizationCoprodIso_inv :
    iV ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iV ≫ f).toNormalization ≫ coprod.inr := by
  simp [← toNormalization_inr_normalizationCoprodIso_hom_assoc f e]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_normalizationCoprodIso_hom_fromNormalization` / 引理 `inl_normalizationCoprodIso_hom_fromNormalization`

English:
lemma inl_normalizationCoprodIso_hom_fromNormalization
  proof: by
  simp [Scheme.Hom.normalizationCoprodIso]

中文:
引理 inl_normalizationCoprodIso_hom_fromNormalization
  证明: by
  simp [Scheme.Hom.normalizationCoprodIso]

Depends on / 依赖: Scheme, Scheme.Hom.normalizationCoprodIso, normalizationCoprodIso
-/
lemma inl_normalizationCoprodIso_hom_fromNormalization :
    coprod.inl ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iU ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_normalizationCoprodIso_hom_fromNormalization` / 引理 `inr_normalizationCoprodIso_hom_fromNormalization`

English:
lemma inr_normalizationCoprodIso_hom_fromNormalization
  proof: by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc, simp]

中文:
引理 inr_normalizationCoprodIso_hom_fromNormalization
  证明: by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc, simp]

Depends on / 依赖: Scheme, Scheme.Hom.normalizationCoprodIso, normalizationCoprodIso
-/
lemma inr_normalizationCoprodIso_hom_fromNormalization :
    coprod.inr ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iV ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc, simp]
/--
lemma `normalizationCoprodIso_inv_coprodDesc_fromNormalization` / 引理 `normalizationCoprodIso_inv_coprodDesc_fromNormalization`

English:
lemma normalizationCoprodIso_inv_coprodDesc_fromNormalization
  proof: by
  simp [Scheme.Hom.normalizationCoprodIso]

中文:
引理 normalizationCoprodIso_inv_coprodDesc_fromNormalization
  证明: by
  simp [Scheme.Hom.normalizationCoprodIso]

Depends on / 依赖: Scheme, Scheme.Hom.normalizationCoprodIso, normalizationCoprodIso
-/
lemma normalizationCoprodIso_inv_coprodDesc_fromNormalization :
    (f.normalizationCoprodIso e).inv ≫
      coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization =
    f.fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

end Coproduct

section Smooth

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `normalizationPullback` / `normalizationPullback` 的定义

English:
definition normalizationPullback
  signature: :
  body: (pullback.snd f g).normalizationDesc (pullback.map _ _ _ _ f.toNormalization
    (𝟙 _) (𝟙 _) (by simp) (by simp)) (pullback.snd _ _) (by simp)
  deriving IsIntegralHom

@[reassoc (attr := simp)]

中文:
定义 normalizationPullback
  签名: :
  定义体: (pullback.snd f g).normalizationDesc (pullback.map _ _ _ _ f.toNormalization
    (𝟙 _) (𝟙 _) (by simp) (by simp)) (pullback.snd _ _) (by simp)
  deriving IsIntegralHom

@[reassoc (attr := simp)]

Depends on / 依赖: f.toNormalization, normalizationDesc, pullback, pullback.map, pullback.snd, toNormalization
-/
noncomputable def normalizationPullback :
    (pullback.snd f g).normalization ⟶ pullback f.fromNormalization g :=
  (pullback.snd f g).normalizationDesc (pullback.map _ _ _ _ f.toNormalization
    (𝟙 _) (𝟙 _) (by simp) (by simp)) (pullback.snd _ _) (by simp)
  deriving IsIntegralHom

@[reassoc (attr := simp)]
/--
lemma `normalizationPullback_snd` / 引理 `normalizationPullback_snd`

English:
lemma normalizationPullback_snd
  proof: (pullback.snd f g).normalizationDesc_comp ..

中文:
引理 normalizationPullback_snd
  证明: (pullback.snd f g).normalizationDesc_comp ..

Depends on / 依赖: normalizationDesc_comp, pullback, pullback.snd
-/
lemma normalizationPullback_snd :
    f.normalizationPullback g ≫ pullback.snd _ _ = (pullback.snd f g).fromNormalization :=
  (pullback.snd f g).normalizationDesc_comp ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalization_normalizationPullback_fst` / 引理 `toNormalization_normalizationPullback_fst`

English:
lemma toNormalization_normalizationPullback_fst
  proof: by
  simp [normalizationPullback]

中文:
引理 toNormalization_normalizationPullback_fst
  证明: by
  simp [normalizationPullback]

Depends on / 依赖: normalizationPullback
-/
lemma toNormalization_normalizationPullback_fst :
    (pullback.snd f g).toNormalization ≫ f.normalizationPullback g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f.toNormalization := by
  simp [normalizationPullback]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- Normalization commutes with smooth base change. -/
@[stacks 03GV]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Smooth
  signature: g] : IsIso (f.normalizationPullback g)
  body: by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= g ⁻¹ᵁ U⟩ :

中文:
实例 [Smooth
  签名: g] : IsIso (f.normalizationPullback g)
  定义体: by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= g ⁻¹ᵁ U⟩ :

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict, S.isBasis_affineOpens.exists_subset_of_mem_open, Scheme, Scheme.Hom.fromNormalization, Set.mem_univ, Y.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, fromNormalization, isBasis_affineOpens, isIso_morphismRestrict_iff_isIso_app, isOpen_univ, isomorphisms, mem_univ, of_forall_exists_morphismRestrict, pullback, pullback.snd
-/
instance [Smooth g] : IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= g ⁻¹ᵁ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := pullback.snd _ g x) hxU (g ⁻¹ᵁ U).2
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this]; rw [← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  have : (g.appLE U V hVU).hom.Smooth := g.smooth_appLE hU hV hVU
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) otimes[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) otimes[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) ->ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    TensorProduct.toIntegralClosure_bijective_of_smooth
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V <= pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage]; rw [pullback.condition]; rw [Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

end Smooth

end AlgebraicGeometry.Scheme.Hom
