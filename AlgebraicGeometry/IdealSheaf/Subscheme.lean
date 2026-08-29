/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Subscheme associated to an ideal sheaf

We construct the subscheme associated to an ideal sheaf.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`: The subscheme associated to an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: The inclusion from the subscheme.
* `AlgebraicGeometry.Scheme.Hom.image`: The scheme-theoretic image of a morphism.
* `AlgebraicGeometry.Scheme.kerAdjunction`:
  The adjunction between taking kernels and taking the associated subscheme.

## Note

Some instances are in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion` and
`Mathlib/AlgebraicGeometry/Morphisms/Separated` because they need more API to prove.

-/

@[expose] public section

open CategoryTheory TopologicalSpace PrimeSpectrum Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

variable (I : IdealSheafData X)

/-- `Spec (𝒪ₓ(U)/I(U))`, the object to be glued into the closed subscheme. -/
noncomputable
/--
Definition of `glueDataObj` / `glueDataObj` 的定义

English:
definition glueDataObj
  signature: (U : X.affineOpens)
  body: Spec .of Γ(X, U) ⧸ I.ideal U

中文:
定义 glueDataObj
  签名: (U : X.affineOpens)
  定义体: Spec .of Γ(X, U) ⧸ I.ideal U

Depends on / 依赖: I.ideal
-/
def glueDataObj (U : X.affineOpens) : Scheme :=
Spec .of Γ(X, U) ⧸ I.ideal U

/-- `Spec (𝒪ₓ(U)/I(U)) ⟶ Spec (𝒪ₓ(U)) = U`, the closed immersion into `U`. -/
noncomputable
/--
Definition of `glueDataObjι` / `glueDataObjι` 的定义

English:
definition glueDataObjι
  signature: (U : X.affineOpens)
  body: Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

中文:
定义 glueDataObjι
  签名: (U : X.affineOpens)
  定义体: Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.Quotient.mk, Quotient, Spec.map, isoSpec, isoSpec.inv
-/
def glueDataObjι (U : X.affineOpens) : I.glueDataObj U ⟶ U.1 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
instance (U : X.affineOpens) : IsPreimmersion (I.glueDataObjι U) :=
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) :=
    .mk_SpecMap
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
  .comp _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `glueDataObjι_ι` / 引理 `glueDataObjι_ι`

English:
lemma glueDataObjι_ι
  given: (U : X.affineOpens)
  statement: I.glueDataObjι U ≫ U.1.ι =
  proof: by
  rw [glueDataObjι]; rw [Category.assoc]; rfl

中文:
引理 glueDataObjι_ι
  条件: (U : X.affineOpens)
  结论: I.glueDataObjι U ≫ U.1.ι =
  证明: by
  rw [glueDataObjι]; rw [Category.assoc]; rfl

Depends on / 依赖: Category, Category.assoc
-/
lemma glueDataObjι_ι (U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.fromSpec := by
  rw [glueDataObjι]; rw [Category.assoc]; rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ker_glueDataObjι_appTop` / 引理 `ker_glueDataObjι_appTop`

English:
lemma ker_glueDataObjι_appTop
  given: (U : X.affineOpens)
  proof: by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatI

中文:
引理 ker_glueDataObjι_appTop
  条件: (U : X.affineOpens)
  证明: by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatI

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, CommRingCat.of, CommRingCat.ofHom, I.ideal, Ideal.Quotient.mk, Ideal.mk_ker, Iso.commRingCatIsoToRingEquiv_toRingHom, Quotient, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.comap_ker, RingHom.ker, RingHom.ker_equiv_comp, Scheme, Scheme.Hom.comp_a, Spec.map, appTop, appTop.hom
-/
lemma ker_glueDataObjι_appTop (U : X.affineOpens) :
    RingHom.ker (I.glueDataObjι U).appTop.hom = (I.ideal U).comap U.1.topIso.hom.hom := by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]; rw [RingHom.comap_ker]; rw [RingEquiv.toRingHom_eq_coe]; rw [Iso.commRingCatIsoToRingEquiv_toRingHom]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_comp]
  congr 2
  simp only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.Opens.topIso_hom]
  rw [← Scheme.Hom.appTop]; rw [U.2.isoSpec_inv_appTop]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
open scoped Set.Notation in
/--
lemma `range_glueDataObjι` / 引理 `range_glueDataObjι`

English:
lemma range_glueDataObjι
  given: (U : X.affineOpens)
  proof: by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

中文:
引理 range_glueDataObjι
  条件: (U : X.affineOpens)
  证明: by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, Scheme, Scheme.Hom.comp_base, Set.range_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, mk_surjective, range_comap_of_surjective, range_comp
-/
lemma range_glueDataObjι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U) =
      U.2.isoSpec.inv '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `range_glueDataObjι_ι` / 引理 `range_glueDataObjι_ι`

English:
lemma range_glueDataObjι_ι
  given: (U : X.affineOpens)
  proof: by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [IsAffineOpen.isoSpec_inv_ι]; rw [IsAffineOpen.fromSpec_image_zeroLocus]

中文:
引理 range_glueDataObjι_ι
  条件: (U : X.affineOpens)
  证明: by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [IsAffineOpen.isoSpec_inv_ι]; rw [IsAffineOpen.fromSpec_image_zeroLocus]

Depends on / 依赖: I.ideal, IsAffineOpen, IsAffineOpen.fromSpec_image_zeroLocus, IsAffineOpen.isoSpec_inv_, Scheme, Scheme.Hom.comp_base, Set.image_comp, Set.range_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, fromSpec_image_zeroLocus, image_comp, range_comp
-/
lemma range_glueDataObjι_ι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = X.zeroLocus (U := U) (I.ideal U) inter U := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [IsAffineOpen.isoSpec_inv_ι]; rw [IsAffineOpen.fromSpec_image_zeroLocus]

/-- The underlying space of `Spec (𝒪ₓ(U)/I(U))` is homeomorphic to its image in `X`. -/
noncomputable
/--
Definition of `glueDataObjCarrierIso` / `glueDataObjCarrierIso` 的定义

English:
definition glueDataObjCarrierIso
  signature: (U : X.affineOpens)
  body: TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

中文:
定义 glueDataObjCarrierIso
  签名: (U : X.affineOpens)
  定义体: TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

Depends on / 依赖: I.ideal
-/
def glueDataObjCarrierIso (U : X.affineOpens) :
    (I.glueDataObj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) inter U) :=
  TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

/-- The open immersion `Spec Γ(𝒪ₓ/I, U) ⟶ Spec Γ(𝒪ₓ/I, V)` if `U ≤ V`. -/
noncomputable
/--
Definition of `glueDataObjMap` / `glueDataObjMap` 的定义

English:
definition glueDataObjMap
  signature: {U V : X.affineOpens} (h : U <= V)
  body: Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

中文:
定义 glueDataObjMap
  签名: {U V : X.affineOpens} (h : U <= V)
  定义体: Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, I.ideal_le_comap_ideal, Ideal.quotientMap, Spec.map, ideal_le_comap_ideal, quotientMap
-/
def glueDataObjMap {U V : X.affineOpens} (h : U <= V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

/--
lemma `isLocalization_away` / 引理 `isLocalization_away`

English:
lemma isLocalization_away
  statement: {U V : X.affineOpens}
  proof: (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : 

中文:
引理 isLocalization_away
  结论: {U V : X.affineOpens}
  证明: (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : 

Depends on / 依赖: I.ideal_le_comap_ideal, Ideal.quotientMap, ideal_le_comap_ideal, quotientMap, toAlgebra
-/
lemma isLocalization_away {U V : X.affineOpens}
    (h : U <= V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
      letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U) := by
    subst hU; exact V.2.isLocalization_of_eq_basicOpen _ _ rfl
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]; rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal', le_refl]

/--
Instance `isOpenImmersion_glueDataObjMap` / 实例 `isOpenImmersion_glueDataObjMap`

English:
instance isOpenImmersion_glueDataObjMap
  signature: {V : X.affineOpens} (f : Γ(X, V.1))
  body: by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)

中文:
实例 isOpenImmersion_glueDataObjMap
  签名: {V : X.affineOpens} (f : Γ(X, V.1))
  定义体: by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)

Depends on / 依赖: I.ideal_le_comap_ideal, I.isLocalization_away, Ideal.Quotient.mk, Ideal.quotientMap, IsOpenImmersion, IsOpenImmersion.of_isLocalization, Quotient, X.affineBasicOpen_le, affineBasicOpen_le, ideal_le_comap_ideal, isLocalization_away, of_isLocalization, quotientMap, toAlgebra
-/
instance isOpenImmersion_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
    IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le f)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)

/--
lemma `opensRange_glueDataObjMap` / 引理 `opensRange_glueDataObjMap`

English:
lemma opensRange_glueDataObjMap
  given: {V : X.affineOpens} (f : Γ(X, V.1))
  proof: by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen

中文:
引理 opensRange_glueDataObjMap
  条件: {V : X.affineOpens} (f : Γ(X, V.1))
  证明: by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen

Depends on / 依赖: I.ideal, I.ideal_le_comap_ideal, I.isLocalization_away, Ideal.Quotient.mk, Ideal.quotientMap, Quotient, Scheme, Scheme.Hom.comp_preimage, X.affineBasicOpen_le, affineBasicOpen_le, comap_basicOpen, comp_preimage, fromSpec_preimage_basicOpen, ideal_le_comap_ideal, isLocalization_away, localization_away_comap_range, quotientMap, toAlgebra
-/
lemma opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
      (I.glueDataObjMap (X.affineBasicOpen_le f)).opensRange =
        (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen]; rw [← V.2.fromSpec_preimage_basicOpen]; rw [← Scheme.Hom.comp_preimage]; rw [glueDataObjι_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `glueDataObjMap_glueDataObjι` / 引理 `glueDataObjMap_glueDataObjι`

English:
lemma glueDataObjMap_glueDataObjι
  given: {U V : X.affineOpens} (h : U <= V)
  proof: by
  rw [glueDataObjMap]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.quotientMap_comp_mk]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp_assoc]; rw [glueDataObjι]; rw [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp]; rw [IsAffineOpen.isoSpec_hom]; rw [C

中文:
引理 glueDataObjMap_glueDataObjι
  条件: {U V : X.affineOpens} (h : U <= V)
  证明: by
  rw [glueDataObjMap]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.quotientMap_comp_mk]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp_assoc]; rw [glueDataObjι]; rw [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp]; rw [IsAffineOpen.isoSpec_hom]; rw [C

Depends on / 依赖: Category, Category.assoc, Category.comp_id, CommRingCat, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Ideal.quotientMap_comp_mk, IsAffineOpen, IsAffineOpen.isoSpec_hom, Iso.eq_inv_comp, Iso.hom_inv_id, Scheme, Scheme.Opens.toSpec, Spec.map_comp_assoc, comp_id, eq_inv_comp, glueDataObjMap, hom_inv_id, isoSpec_hom, map_comp_assoc
-/
lemma glueDataObjMap_glueDataObjι {U V : X.affineOpens} (h : U <= V) :
    I.glueDataObjMap h ≫ I.glueDataObjι V = I.glueDataObjι U ≫ X.homOfLE h := by
  rw [glueDataObjMap]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.quotientMap_comp_mk]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp_assoc]; rw [glueDataObjι]; rw [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp]; rw [IsAffineOpen.isoSpec_hom]; rw [CommRingCat.ofHom_hom]
  erw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc U.1 V.1 h]
  rw [← IsAffineOpen.isoSpec_hom V.2]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ideal_le_ker_glueDataObjι` / 引理 `ideal_le_ker_glueDataObjι`

English:
lemma ideal_le_ker_glueDataObjι
  given: (U V : X.affineOpens)
  proof: by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (I.glueDataObjι U p).1
      ⟨(I.glueDataObjι U p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx => X.basicOpen_le g (hfg ▸ 

中文:
引理 ideal_le_ker_glueDataObjι
  条件: (U V : X.affineOpens)
  证明: by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (I.glueDataObjι U p).1
      ⟨(I.glueDataObjι U p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx => X.basicOpen_le g (hfg ▸ 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Hom.isIso_app, I.glueDataObj, I.glueDataObjMap, IsSheaf, IsSheaf.section_ext, X.affineBasicOpen_le, X.basicOpen, X.basicOpen_le, affineBasicOpen_le, basicOpen, basicOpen_le, exists_basicOpen_le_affine_inter, glueDataObj, glueDataObjMap, isIso_app, isIso_iff_bijective, opensRange_glueDataObjMap, section_ext
-/
lemma ideal_le_ker_glueDataObjι (U V : X.affineOpens) :
    I.ideal V <= RingHom.ker (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app _).hom := by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (I.glueDataObjι U p).1
      ⟨(I.glueDataObjι U p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx => X.basicOpen_le g (hfg ▸ hx), hf, ?_⟩
  have := Hom.isIso_app (I.glueDataObjMap (X.affineBasicOpen_le f))
    (I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f) (by rw [opensRange_glueDataObjMap])
  apply ((ConcreteCategory.isIso_iff_bijective _).mp this).1
  simp only [map_zero, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Category.assoc]
  simp only [Scheme.Hom.app_eq_appLE, homOfLE_leOfHom, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_comp_appLE, Category.assoc, glueDataObjMap_glueDataObjι_assoc]
  rw [Scheme.Hom.appLE]
  have H : (X.homOfLE (X.basicOpen_le f) ≫ U.1.ι) ⁻¹ᵁ V.1 = ⊤ := by
    simp only [Scheme.homOfLE_ι, ← top_le_iff]
    exact fun x _ => (hfg.trans_le (X.basicOpen_le g)) x.2
  simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app, ← Functor.map_comp_assoc,
    Scheme.Hom.app_eq _ H, Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp, Category.assoc]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  convert RingHom.map_zero _
  rw [← RingHom.mem_ker]; rw [ker_glueDataObjι_appTop]; rw [← Ideal.mem_comap]; rw [Ideal.comap_comap]; rw [← CommRingCat.hom_comp]
  simp only [homOfLE_leOfHom, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, eqToHom_op, eqToHom_unop, ← Functor.map_comp,
    Scheme.Opens.topIso_hom, Category.assoc]
  exact I.ideal_le_comap_ideal (U := X.affineBasicOpen f) (V := V)
    (hfg.trans_le (X.basicOpen_le g)) hx

/-- (Implementation) The intersections `Spec Γ(𝒪ₓ/I, U) ∩ V` useful for gluing. -/
noncomputable
/--
Definition of `glueDataObjPullback` / `glueDataObjPullback` 的定义

English:
abbreviation glueDataObjPullback
  signature: (U V : X.affineOpens)
  body: pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

中文:
缩写 glueDataObjPullback
  签名: (U V : X.affineOpens)
  定义体: pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

Depends on / 依赖: I.glueDataObj, X.homOfLE, homOfLE, inf_le_left, pullback
-/
abbrev glueDataObjPullback (U V : X.affineOpens) : Scheme :=
  pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `glueDataT` / `glueDataT` 的定义

English:
definition glueDataT
  signature: (U V : X.affineOpens)
  body: by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [Hom.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_ob

中文:
定义 glueDataT
  签名: (U V : X.affineOpens)
  定义体: by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [Hom.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_ob

Depends on / 依赖: Category, Category.assoc, Hom.comp_app, Hom.comp_base, I.glueDataObj, RingHom, RingHom.mem_ker, Scheme, Scheme.Hom.comp_preimage, TopologicalSpace, TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top, X.homOfLE, comp_app, comp_base, comp_preimage, convert_to, homOfLE, homOfLE_app, homOfLE_leOfHom
-/
noncomputable def glueDataT (U V : X.affineOpens) :
    I.glueDataObjPullback U V ⟶ I.glueDataObjPullback V U := by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [Hom.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, homOfLE_app, homOfLE_leOfHom, Category.assoc, RingHom.mem_ker]
    convert_to (U.1.ι.app V.1 ≫ (F ≫ X.homOfLE inf_le_left).appLE (U.1.ι ⁻¹ᵁ V.1) ⊤
      (by rw [← Scheme.Hom.comp_preimage, Category.assoc, X.homOfLE_ι]
          exact fun x _ => by simpa using (F x).2.2)).hom x = 0 using 3
    · simp only [homOfLE_leOfHom, Opens.ι_app, Hom.comp_appLE, homOfLE_app]
      have H : ⊤ <= X.homOfLE (inf_le_left (b := V.1)) ⁻¹ᵁ U.1.ι ⁻¹ᵁ V.1 := by
        rw [← Scheme.Hom.comp_preimage]; rw [X.homOfLE_ι]; exact fun x _ => by simpa using x.2.2
      rw [← F.map_appLE (show ⊤ <= F ⁻¹ᵁ ⊤ from le_rfl) (homOfLE H).op]
      simp only [homOfLE_leOfHom, Opens.toScheme_presheaf_map, Quiver.Hom.unop_op,
        Hom.opensFunctor_map_homOfLE, ← Functor.map_comp_assoc, IsAffineOpen.isoSpec_hom_appTop,
        Opens.topIso_inv, eqToHom_op, homOfLE_leOfHom, Category.assoc,
        Iso.inv_hom_id_assoc, F.app_eq_appLE]
      rfl
    · have : (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app (U.1.ι ⁻¹ᵁ V.1)).hom x = 0 :=
        I.ideal_le_ker_glueDataObjι U V hx
      simp_rw [F, ← pullback.condition]
      simp only [Scheme.Opens.ι_app, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc] at this ⊢
      simp only [this, map_zero]
  · conv_lhs => enter [2]; rw [glueDataObjι]
    rw [Scheme.Hom.liftQuotient_comp_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]; rw [Category.assoc]; rw [X.homOfLE_homOfLE]

@[reassoc (attr := simp)]
/--
lemma `glueDataT_snd` / 引理 `glueDataT_snd`

English:
lemma glueDataT_snd
  given: (U V : X.affineOpens)
  proof: pullback.lift_snd _ _ _

中文:
引理 glueDataT_snd
  条件: (U V : X.affineOpens)
  证明: pullback.lift_snd _ _ _
-/
private lemma glueDataT_snd (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.snd _ _ = pullback.snd _ _ ≫ X.homOfLE (by simp) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `glueDataT_fst` / 引理 `glueDataT_fst`

English:
lemma glueDataT_fst
  given: (U V : X.affineOpens)
  proof: by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 glueDataT_fst
  条件: (U V : X.affineOpens)
  证明: by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]
-/
private lemma glueDataT_fst (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.fst _ _ ≫ glueDataObjι _ _ =
      pullback.snd _ _ ≫ X.homOfLE inf_le_right := by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

/-- (Implementation) `t'` in the glue data for `𝒪ₓ/I`. -/
noncomputable
/--
Definition of `glueDataT'Aux` / `glueDataT'Aux` 的定义

English:
definition glueDataT'Aux
  signature: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  body: pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor

中文:
定义 glueDataT'Aux
  签名: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  定义体: pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor

Depends on / 依赖: Category, Category.assoc, I.glueDataObj, I.glueDataT, IsOpenImmersion, IsOpenImmersion.lift, Scheme, Scheme.Hom.comp_base, Scheme.Opens.range_, Set.range_comp_subset_range, Set.subset_inter_iff, TopCat, TopCat.coe_comp, TopologicalSpace, TopologicalSpace.Opens.coe_inf, X.homOfLE_, coe_comp, coe_inf, comp_base, condition_assoc
-/
def glueDataT'Aux (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀) :
    pullback
      (pullback.fst _ _ : I.glueDataObjPullback U V ⟶ _)
      (pullback.fst _ _ : I.glueDataObjPullback U W ⟶ _) ⟶ I.glueDataObjPullback V U₀ :=
  pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor
      · rw [pullback.condition_assoc (f := I.glueDataObjι U), X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simp)
      · rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simpa using! hU₀))) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc])

@[reassoc (attr := simp)]
/--
lemma `glueDataT'Aux_fst` / 引理 `glueDataT'Aux_fst`

English:
lemma glueDataT'Aux_fst
  given: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  proof: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
引理 glueDataT'Aux_fst
  条件: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  证明: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
-/
private lemma glueDataT'Aux_fst (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/--
lemma `glueDataT'Aux_snd_ι` / 引理 `glueDataT'Aux_snd_ι`

English:
lemma glueDataT'Aux_snd_ι
  given: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  proof: (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)

中文:
引理 glueDataT'Aux_snd_ι
  条件: (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀)
  证明: (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)
-/
private lemma glueDataT'Aux_snd_ι (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W <= U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.snd _ _ ≫ (V.1 ⊓ U₀.1).ι =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι :=
  (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The glue data for `𝒪ₓ/I`. -/
@[simps]
noncomputable
/--
Definition of `glueData` / `glueData` 的定义

English:
definition glueData
  signature: : Scheme.GlueData where
  body: X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply

中文:
定义 glueData
  签名: : Scheme.GlueData where
  定义体: X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply

Depends on / 依赖: X.affineOpens, affineOpens
-/
def glueData : Scheme.GlueData where
  J := X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp [pullback.condition]
    · simp
  t' i j k := pullback.lift
    (I.glueDataT'Aux _ _ _ _ inf_le_right) (I.glueDataT'Aux _ _ _ _ inf_le_left) (by simp)
  t_fac i j k := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp
    · rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc]
  cocycle i j k := by
    dsimp only
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [pullback.condition_assoc (f := I.glueDataObjι i)]
        simp
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [pullback.condition_assoc]
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [← pullback.condition_assoc]; rw [pullback.condition_assoc (f := I.glueDataObjι i)]; rw [X.homOfLE_ι]
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_snd_ι, limit.lift_π_assoc, cospan_left, glueDataT'Aux_fst_assoc,
          glueDataT_fst_assoc, Scheme.homOfLE_ι, Category.id_comp]
        rw [pullback.condition_assoc]; rw [pullback.condition_assoc]; rw [X.homOfLE_ι]
  f_open i j := inferInstance

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The map from `Spec(𝒪ₓ/I)` to `X`. See `IdealSheafData.subschemeι` instead. -/
noncomputable
/--
Definition of `gluedTo` / `gluedTo` 的定义

English:
definition gluedTo
  signature: : I.glueData.glued ⟶ X
  body: Multicoequalizer.desc _ _ (fun i => I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]

中文:
定义 gluedTo
  签名: : I.glueData.glued ⟶ X
  定义体: Multicoequalizer.desc _ _ (fun i => I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]

Depends on / 依赖: GlueData, GlueData.diagram, I.glueDataObj, Multicoequalizer, Multicoequalizer.desc, condition_assoc, diagram, pullback, pullback.condition_assoc
-/
def gluedTo : I.glueData.glued ⟶ X :=
  Multicoequalizer.desc _ _ (fun i => I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]
/--
lemma `ι_gluedTo` / 引理 `ι_gluedTo`

English:
lemma ι_gluedTo
  given: (U : X.affineOpens)
  proof: Multicoequalizer.π_desc _ _ _ _ _

中文:
引理 ι_gluedTo
  条件: (U : X.affineOpens)
  证明: Multicoequalizer.π_desc _ _ _ _ _
-/
private lemma ι_gluedTo (U : X.affineOpens) :
    I.glueData.ι U ≫ I.gluedTo = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `glueDataObjMap_ι` / 引理 `glueDataObjMap_ι`

English:
lemma glueDataObjMap_ι
  given: (U V : X.affineOpens) (h : U <= V)
  proof: by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm]; rw [← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  

中文:
引理 glueDataObjMap_ι
  条件: (U V : X.affineOpens) (h : U <= V)
  证明: by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm]; rw [← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  
-/
private lemma glueDataObjMap_ι (U V : X.affineOpens) (h : U <= V) :
    I.glueDataObjMap h ≫ I.glueData.ι V = I.glueData.ι U := by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm]; rw [← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  simp only [glueData_J, glueData_V, glueData_t, glueData_U, glueData_f] at this
  rw [← IsIso.inv_comp_eq] at this
  rw [← Category.id_comp (I.glueData.ι U)]; rw [← this]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (glueDataObjι _ _)]
  simp [pullback_inv_fst_snd_of_right_isIso_assoc, H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `gluedTo_injective` / 引理 `gluedTo_injective`

English:
lemma gluedTo_injective
  proof: by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget b
  change I.glueData.ι ia a = I.glueData.ι ib b
  have : (I.glueDataObjι ia a).1 = (

中文:
引理 gluedTo_injective
  证明: by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget b
  change I.glueData.ι ia a = I.glueData.ι ib b
  have : (I.glueDataObjι ia a).1 = (
-/
private lemma gluedTo_injective :
    Function.Injective I.gluedTo := by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget b
  change I.glueData.ι ia a = I.glueData.ι ib b
  have : (I.glueDataObjι ia a).1 = (I.glueDataObjι ib b).1 := by
    have : (I.glueData.ι ia ≫ I.gluedTo) a = (I.glueData.ι ib ≫ I.gluedTo) b := e
    rwa [ι_gluedTo, ι_gluedTo] at this
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    (I.glueDataObjι ia a).1
      ⟨(I.glueDataObjι ia a).2, this ▸ (I.glueDataObjι ib b).2⟩
  have hmem (W) (hW : W = X.affineBasicOpen g) :
      b in Set.range (I.glueDataObjMap (hW.trans_le (X.affineBasicOpen_le g))) := by
    subst hW
    refine (I.opensRange_glueDataObjMap g).ge ?_
    change (I.glueDataObjι ib b).1 in X.basicOpen g
    rwa [← this, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueDataObjMap f).ge H
  obtain ⟨b, rfl⟩ := hmem (X.affineBasicOpen f) (Subtype.ext hfg)
  simp only [glueData_U, ← Scheme.Hom.comp_apply, glueDataObjMap_glueDataObjι] at this ⊢
  simp only [Scheme.affineBasicOpen_coe, Scheme.Hom.comp_base, TopCat.comp_app,
    Scheme.homOfLE_apply, SetLike.coe_eq_coe] at this
  obtain rfl := (I.glueDataObjι (X.affineBasicOpen f)).isEmbedding.injective this
  simp only [glueDataObjMap_ι]

/--
lemma `range_glueDataObjι_ι_eq_support_inter` / 引理 `range_glueDataObjι_ι_eq_support_inter`

English:
lemma range_glueDataObjι_ι_eq_support_inter
  given: (U : X.affineOpens)
  proof: (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

中文:
引理 range_glueDataObjι_ι_eq_support_inter
  条件: (U : X.affineOpens)
  证明: (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

Depends on / 依赖: I.coe_support_inter, I.range_glueDataObj, coe_support_inter
-/
lemma range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = (I.support : Set X) inter U :=
  (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `range_gluedTo` / 引理 `range_gluedTo`

English:
lemma range_gluedTo
  statement: Set.range I.gluedTo = I.support
  proof: by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x => ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective forget x
    change (I.glueData.ι _ ≫ I.gluedTo) x in I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter 

中文:
引理 range_gluedTo
  结论: Set.range I.gluedTo = I.support
  证明: by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x => ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective forget x
    change (I.glueData.ι _ ≫ I.gluedTo) x in I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter 

Depends on / 依赖: I.glueData, I.glueData.toGlueData, I.glueDataObj, I.gluedTo, I.range_glueDataObj, I.support, Set.mem_univ, Set.range_subset_iff.mpr, X.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, forget, glueData, glueDataObj, gluedTo, isBasis_affineOpens, isOpen_univ, mem_univ, range_subset_iff, subset_antisymm, support
-/
lemma range_gluedTo : Set.range I.gluedTo = I.support := by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x => ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective forget x
    change (I.glueData.ι _ ≫ I.gluedTo) x in I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter ix).le ⟨_, rfl⟩).1
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := (I.range_glueDataObjι_ι_eq_support_inter ⟨U, hU⟩).ge ⟨hx, hxU⟩
    rw [← ι_gluedTo]
    exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_glueData_ι` / 引理 `range_glueData_ι`

English:
lemma range_glueData_ι
  given: (U : X.affineOpens)
  proof: by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [ι_gluedTo]; rw [range_glueDataObjι_ι]; rw [Set.image_preimage_eq_inter_range]; rw [range_gluedTo]; rw [← coe_support_inter]; r

中文:
引理 range_glueData_ι
  条件: (U : X.affineOpens)
  证明: by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [ι_gluedTo]; rw [range_glueDataObjι_ι]; rw [Set.image_preimage_eq_inter_range]; rw [range_gluedTo]; rw [← coe_support_inter]; r
-/
private lemma range_glueData_ι (U : X.affineOpens) :
    Set.range (Scheme.Hom.toLRSHom' (X := I.glueDataObj U) <|
      I.glueData.ι U).base = (I.gluedTo ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [ι_gluedTo]; rw [range_glueDataObjι_ι]; rw [Set.image_preimage_eq_inter_range]; rw [range_gluedTo]; rw [← coe_support_inter]; rw [Set.inter_comm]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) identifying `Spec(Γ(X, U)/I(U))` with its image in `Spec(𝒪ₓ/I)`. -/
private noncomputable
/--
Definition of `glueDataObjIso` / `glueDataObjIso` 的定义

English:
definition glueDataObjIso
  signature: (U : X.affineOpens)
  body: IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, range_glueData_ι])

中文:
定义 glueDataObjIso
  签名: (U : X.affineOpens)
  定义体: IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, range_glueData_ι])

Depends on / 依赖: I.glueData, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Scheme, Scheme.Opens, Scheme.Opens.range_, TopologicalSpace, TopologicalSpace.Opens.map_coe, glueData, isoOfRangeEq, map_coe
-/
def glueDataObjIso (U : X.affineOpens) :
    I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, range_glueData_ι])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `glueDataObjIso_hom_ι` / 引理 `glueDataObjIso_hom_ι`

English:
lemma glueDataObjIso_hom_ι
  given: (U : X.affineOpens)
  proof: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

中文:
引理 glueDataObjIso_hom_ι
  条件: (U : X.affineOpens)
  证明: IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
-/
private lemma glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.gluedTo ⁻¹ᵁ U).ι = I.glueData.ι U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `glueDataObjIso_hom_restrict` / 引理 `glueDataObjIso_hom_restrict`

English:
lemma glueDataObjIso_hom_restrict
  given: (U : X.affineOpens)
  proof: by
  rw [← cancel_mono U.1.ι]; simp

中文:
引理 glueDataObjIso_hom_restrict
  条件: (U : X.affineOpens)
  证明: by
  rw [← cancel_mono U.1.ι]; simp
-/
private lemma glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ ↑U = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreimmersion I.gluedTo
  body: by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom]; rw [glueDataObjIso_hom_restrict]
  infer_instance

中文:
实例 :
  签名: IsPreimmersion I.gluedTo
  定义体: by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom]; rw [glueDataObjIso_hom_restrict]
  infer_instance

Depends on / 依赖: I.glueDataObjIso, IsPreimmersion, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, cancel_left_of_respectsIso, glueDataObjIso, glueDataObjIso_hom_restrict, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, infer_instance
-/
instance : IsPreimmersion I.gluedTo := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom]; rw [glueDataObjIso_hom_restrict]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiCompact I.gluedTo
  body: ⟨fun _ _ => (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.support.isClosed⟩).isCompact_preimage⟩

中文:
实例 :
  签名: QuasiCompact I.gluedTo
  定义体: ⟨fun _ _ => (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.support.isClosed⟩).isCompact_preimage⟩
-/
private instance : QuasiCompact I.gluedTo :=
  ⟨fun _ _ => (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.support.isClosed⟩).isCompact_preimage⟩

/-- (Implementation) The underlying space of `Spec(𝒪ₓ/I)` is homeomorphic to the support of `I`. -/
noncomputable
/--
Definition of `gluedHomeo` / `gluedHomeo` 的定义

English:
definition gluedHomeo
  signature: : I.glueData.glued ≃ₜ I.support
  body: I.gluedTo.isEmbedding.toHomeomorph.trans (.setCongr I.range_gluedTo)

中文:
定义 gluedHomeo
  签名: : I.glueData.glued ≃ₜ I.support
  定义体: I.gluedTo.isEmbedding.toHomeomorph.trans (.setCongr I.range_gluedTo)

Depends on / 依赖: I.gluedTo.isEmbedding.toHomeomorph.trans, I.range_gluedTo, gluedTo, isEmbedding, range_gluedTo, setCongr, toHomeomorph
-/
def gluedHomeo : I.glueData.glued ≃ₜ I.support :=
  I.gluedTo.isEmbedding.toHomeomorph.trans (.setCongr I.range_gluedTo)

/--
Definition of `subscheme` / `subscheme` 的定义

English:
definition subscheme
  signature: : Scheme
  body: I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

中文:
定义 subscheme
  签名: : Scheme
  定义体: I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

Depends on / 依赖: I.glueData.glued.restrict, I.gluedHomeo.symm, I.gluedHomeo.symm.isOpenEmbedding, TopCat, TopCat.ofHom, glueData, gluedHomeo, isOpenEmbedding, restrict, toContinuousMap
-/
noncomputable def subscheme : Scheme :=
  I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The isomorphism between the subscheme and the glued scheme. -/
noncomputable
/--
Definition of `subschemeIso` / `subschemeIso` 的定义

English:
definition subschemeIso
  signature: : I.subscheme ≅ I.glueData.glued
  body: letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.isIso F
  asIso F

中文:
定义 subschemeIso
  签名: : I.subscheme ≅ I.glueData.glued
  定义体: letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.isIso F
  asIso F

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, F.base, I.glueData.glued.ofRestrict, I.gluedHomeo.symm, I.gluedHomeo.symm.isOpenEmbedding, I.gluedHomeo.symm.surjective, IsOpenImmersion, IsOpenImmersion.isIso, TopCat, TopCat.ofHom, epi_of_surjective, glueData, gluedHomeo, isOpenEmbedding, ofRestrict, surjective, toContinuousMap
-/
def subschemeIso : I.subscheme ≅ I.glueData.glued :=
  letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.isIso F
  asIso F

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion from the subscheme associated to an ideal sheaf. -/
noncomputable
/--
Definition of `subschemeι` / `subschemeι` 的定义

English:
definition subschemeι
  signature: : I.subscheme ⟶ X
  body: (I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]

中文:
定义 subschemeι
  签名: : I.subscheme ⟶ X
  定义体: (I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]

Depends on / 依赖: I.gluedHomeo, I.gluedHomeo.apply_symm_apply, I.gluedHomeo.symm, I.gluedTo, I.subschemeIso.hom, Subtype, Subtype.val, apply_symm_apply, copyBase, gluedHomeo, gluedTo, subschemeIso
-/
def subschemeι : I.subscheme ⟶ X :=
(I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]

/--
lemma `subschemeι_apply` / 引理 `subschemeι_apply`

English:
lemma subschemeι_apply
  given: (x : I.subscheme)
  statement: I.subschemeι x = x.1
  proof: rfl

中文:
引理 subschemeι_apply
  条件: (x : I.subscheme)
  结论: I.subschemeι x = x.1
  证明: rfl
-/
lemma subschemeι_apply (x : I.subscheme) : I.subschemeι x = x.1 := rfl

/--
lemma `subschemeι_def` / 引理 `subschemeι_def`

English:
lemma subschemeι_def
  statement: I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo
  proof: Scheme.Hom.copyBase_eq _ _ _

中文:
引理 subschemeι_def
  结论: I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo
  证明: Scheme.Hom.copyBase_eq _ _ _
-/
private lemma subschemeι_def : I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo :=
  Scheme.Hom.copyBase_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreimmersion I.subschemeι
  body: by
  rw [subschemeι_def]
  infer_instance

中文:
实例 :
  签名: IsPreimmersion I.subschemeι
  定义体: by
  rw [subschemeι_def]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsPreimmersion I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiCompact I.subschemeι
  body: by
  rw [subschemeι_def]
  infer_instance

@[simp]

中文:
实例 :
  签名: QuasiCompact I.subschemeι
  定义体: by
  rw [subschemeι_def]
  infer_instance

@[simp]

Depends on / 依赖: infer_instance
-/
instance : QuasiCompact I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

@[simp]
/--
lemma `range_subschemeι` / 引理 `range_subschemeι`

English:
lemma range_subschemeι
  statement: Set.range I.subschemeι = I.support
  proof: by
  simp [← range_gluedTo, I.subschemeι_def, Set.range_comp]

中文:
引理 range_subschemeι
  结论: Set.range I.subschemeι = I.support
  证明: by
  simp [← range_gluedTo, I.subschemeι_def, Set.range_comp]

Depends on / 依赖: I.subscheme, Set.range_comp, range_comp, range_gluedTo
-/
lemma range_subschemeι : Set.range I.subschemeι = I.support := by
  simp [← range_gluedTo, I.subschemeι_def, Set.range_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `opensRange_glueData_ι_subschemeIso_inv` / 引理 `opensRange_glueData_ι_subschemeIso_inv`

English:
lemma opensRange_glueData_ι_subschemeIso_inv
  given: (U : X.affineOpens)
  proof: by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]

中文:
引理 opensRange_glueData_ι_subschemeIso_inv
  条件: (U : X.affineOpens)
  证明: by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]
-/
private lemma opensRange_glueData_ι_subschemeIso_inv (U : X.affineOpens) :
    (I.glueData.ι U ≫ I.subschemeIso.inv).opensRange = I.subschemeι ⁻¹ᵁ U := by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]

set_option backward.isDefEq.respectTransparency false in
/-- The subscheme associated to an ideal sheaf `I` is covered by `Spec(Γ(X, U)/I(U))`. -/
noncomputable
/--
Definition of `subschemeCover` / `subschemeCover` 的定义

English:
definition subschemeCover
  signature: : I.subscheme.AffineOpenCover where
  body: X.affineOpens
X U := .of Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.ι U ≫ I.subschemeIso.inv
  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
  covers x := by
    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
    obtain ⟨⟨y, hy : y in U.1⟩, rfl : y

中文:
定义 subschemeCover
  签名: : I.subscheme.AffineOpenCover where
  定义体: X.affineOpens
X U := .of Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.ι U ≫ I.subschemeIso.inv
  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
  covers x := by
    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
    obtain ⟨⟨y, hy : y in U.1⟩, rfl : y

Depends on / 依赖: X.affineOpens, affineOpens
-/
def subschemeCover : I.subscheme.AffineOpenCover where
  I₀ := X.affineOpens
X U := .of Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.ι U ≫ I.subschemeIso.inv
  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
  covers x := by
    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
    obtain ⟨⟨y, hy : y in U.1⟩, rfl : y = x.1⟩ :=
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).covers x.1
    exact (I.opensRange_glueData_ι_subschemeIso_inv U).ge hy

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `opensRange_subschemeCover_map` / 引理 `opensRange_subschemeCover_map`

English:
lemma opensRange_subschemeCover_map
  given: (U : X.affineOpens)
  proof: I.opensRange_glueData_ι_subschemeIso_inv U

中文:
引理 opensRange_subschemeCover_map
  条件: (U : X.affineOpens)
  证明: I.opensRange_glueData_ι_subschemeIso_inv U

Depends on / 依赖: I.opensRange_glueData_
-/
lemma opensRange_subschemeCover_map (U : X.affineOpens) :
    (I.subschemeCover.f U).opensRange = I.subschemeι ⁻¹ᵁ U :=
  I.opensRange_glueData_ι_subschemeIso_inv U

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `subschemeCover_map_subschemeι` / 引理 `subschemeCover_map_subschemeι`

English:
lemma subschemeCover_map_subschemeι
  given: (U : X.affineOpens)
  proof: by
  simp [subschemeCover, subschemeι_def]

中文:
引理 subschemeCover_map_subschemeι
  条件: (U : X.affineOpens)
  证明: by
  simp [subschemeCover, subschemeι_def]

Depends on / 依赖: subschemeCover
-/
lemma subschemeCover_map_subschemeι (U : X.affineOpens) :
    I.subschemeCover.f U ≫ I.subschemeι = I.glueDataObjι U ≫ U.1.ι := by
  simp [subschemeCover, subschemeι_def]

set_option backward.isDefEq.respectTransparency false in
/-- `Γ(𝒪ₓ/I, U) ≅ 𝒪ₓ(U)/I(U)`. -/
noncomputable
/--
Definition of `subschemeObjIso` / `subschemeObjIso` 的定义

English:
definition subschemeObjIso
  signature: (U : X.affineOpens)
  body: I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

中文:
定义 subschemeObjIso
  签名: (U : X.affineOpens)
  定义体: I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

Depends on / 依赖: I.ideal, I.subscheme.presheaf.mapIso, I.subschemeCover.f, Scheme, appIso, eqToIso, mapIso, mono_of_mono_fac, presheaf, subscheme, subschemeCover
-/
def subschemeObjIso (U : X.affineOpens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅ .of (Γ(X, U) ⧸ I.ideal U) :=
  I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `subschemeι_app` / 引理 `subschemeι_app`

English:
lemma subschemeι_app
  given: (U : X.affineOpens)
  statement: I.subschemeι.app U =
  proof: by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, C

中文:
引理 subschemeι_app
  条件: (U : X.affineOpens)
  结论: I.subschemeι.app U =
  证明: by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, C

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_inv, Hom.comp_app, Hom.comp_base, Hom.naturality_assoc, I.subschemeCover_map_subscheme, IsAffineOpen, IsAffineOpen.fromSpec_app_self, IsAffineOpen.isoSpec_inv_, IsIso.comp_inv_eq, Scheme, Scheme.Hom.congr_app, TopologicalSpace, TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top, comp_app, comp_base, comp_inv_eq
-/
lemma subschemeι_app (U : X.affineOpens) : I.subschemeι.app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
    (I.subschemeObjIso U).inv := by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, Category.assoc, Hom.naturality_assoc,
    TopologicalSpace.Opens.map_top, ← ΓSpecIso_inv_naturality_assoc] at this
  simp_rw [← Category.assoc, ← IsIso.comp_inv_eq] at this
  simp only [← this, ← Functor.map_inv, inv_eqToHom, Category.assoc, eqToHom_unop,
    ← Functor.map_comp, IsIso.Iso.inv_inv, subschemeObjIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.hom_inv_id_assoc, Hom.appIso_inv_naturality_assoc,
      Functor.op_map, unop_comp, unop_inv, Quiver.Hom.unop_op,
    Hom.app_appIso_inv_assoc, TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.map_coe,
    homOfLE_leOfHom]
  convert! (Category.comp_id _).symm
  exact CategoryTheory.Functor.map_id _ _

/--
lemma `subschemeι_app_surjective` / 引理 `subschemeι_app_surjective`

English:
lemma subschemeι_app_surjective
  given: (U : X.affineOpens)
  proof: by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

中文:
引理 subschemeι_app_surjective
  条件: (U : X.affineOpens)
  证明: by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

Depends on / 依赖: I.subscheme, I.subschemeObjIso, Ideal.Quotient.mk_surjective, Quotient, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.symm.surjective.comp, mk_surjective, subschemeObjIso, surjective
-/
lemma subschemeι_app_surjective (U : X.affineOpens) :
    Function.Surjective (I.subschemeι.app U) := by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ker_subschemeι_app` / 引理 `ker_subschemeι_app`

English:
lemma ker_subschemeι_app
  given: (U : X.affineOpens)
  proof: by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.f U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  change RingHom.ker (e.commRingCatIsoToRingEquiv.toRingH

中文:
引理 ker_subschemeι_app
  条件: (U : X.affineOpens)
  证明: by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.f U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  change RingHom.ker (e.commRingCatIsoToRingEquiv.toRingH

Depends on / 依赖: CommRingCat, CommRingCat.of, I.ideal, I.subscheme, I.subscheme.presheaf.mapIso, I.subschemeCover.f, Ideal.Quotient.mk, Ideal.mk_ker, Quotient, RingHom, RingHom.ker, RingHom.ker_equiv_comp, Scheme, appIso, commRingCatIsoToRingEquiv, e.commRingCatIsoToRingEquiv.toRingHom.comp, eqToIso, ker_equiv_comp, mapIso, mk_ker
-/
lemma ker_subschemeι_app (U : X.affineOpens) :
    RingHom.ker (I.subschemeι.app U).hom = I.ideal U := by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.f U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  change RingHom.ker (e.commRingCatIsoToRingEquiv.toRingHom.comp
    (Ideal.Quotient.mk (I.ideal U))) = _
  rw [RingHom.ker_equiv_comp]; rw [Ideal.mk_ker]

@[simp]
/--
lemma `ker_subschemeι` / 引理 `ker_subschemeι`

English:
lemma ker_subschemeι
  statement: I.subschemeι.ker = I
  proof: by
  ext; simp [ker_subschemeι_app]

中文:
引理 ker_subschemeι
  结论: I.subschemeι.ker = I
  证明: by
  ext; simp [ker_subschemeι_app]
-/
lemma ker_subschemeι : I.subschemeι.ker = I := by
  ext; simp [ker_subschemeι_app]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (⊤ : X.IdealSheafData).subscheme
  body: by
  rw [← (subschemeι _).ker_eq_top_iff_isEmpty]; rw [ker_subschemeι]

中文:
实例 :
  签名: IsEmpty (⊤ : X.IdealSheafData).subscheme
  定义体: by
  rw [← (subschemeι _).ker_eq_top_iff_isEmpty]; rw [ker_subschemeι]

Depends on / 依赖: ker_eq_top_iff_isEmpty
-/
instance : IsEmpty (⊤ : X.IdealSheafData).subscheme := by
  rw [← (subschemeι _).ker_eq_top_iff_isEmpty]; rw [ker_subschemeι]

/-- Given `I ≤ J`, this is the map `Spec(Γ(X, U)/J(U)) ⟶ Spec(Γ(X, U)/I(U))`. -/
noncomputable
/--
Definition of `glueDataObjHom` / `glueDataObjHom` 的定义

English:
definition glueDataObjHom
  signature: {I J : IdealSheafData X} (h : I <= J) (U)
  body: Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

中文:
定义 glueDataObjHom
  签名: {I J : IdealSheafData X} (h : I <= J) (U)
  定义体: Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.Quotient.factor, Quotient, Spec.map, factor
-/
def glueDataObjHom {I J : IdealSheafData X} (h : I <= J) (U) :
    J.glueDataObj U ⟶ I.glueDataObj U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `glueDataObjHom_ι` / 引理 `glueDataObjHom_ι`

English:
lemma glueDataObjHom_ι
  given: {I J : IdealSheafData X} (h : I <= J) (U)
  proof: by
  rw [glueDataObjHom]; rw [glueDataObjι]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.factor_comp_mk]

@[simp]

中文:
引理 glueDataObjHom_ι
  条件: {I J : IdealSheafData X} (h : I <= J) (U)
  证明: by
  rw [glueDataObjHom]; rw [glueDataObjι]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.factor_comp_mk]

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk, Quotient, Spec.map_comp_assoc, factor_comp_mk, glueDataObjHom, map_comp_assoc, ofHom_comp
-/
lemma glueDataObjHom_ι {I J : IdealSheafData X} (h : I <= J) (U) :
    glueDataObjHom h U ≫ I.glueDataObjι U = J.glueDataObjι U := by
  rw [glueDataObjHom]; rw [glueDataObjι]; rw [glueDataObjι]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.factor_comp_mk]

@[simp]
/--
lemma `glueDataObjHom_id` / 引理 `glueDataObjHom_id`

English:
lemma glueDataObjHom_id
  given: {I : IdealSheafData X} (U)
  proof: by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]

中文:
引理 glueDataObjHom_id
  条件: {I : IdealSheafData X} (U)
  证明: by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: I.glueDataObj, cancel_mono
-/
lemma glueDataObjHom_id {I : IdealSheafData X} (U) :
    glueDataObjHom (le_refl I) U = 𝟙 _ := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]
/--
lemma `glueDataObjHom_comp` / 引理 `glueDataObjHom_comp`

English:
lemma glueDataObjHom_comp
  given: {I J K : IdealSheafData X} (hIJ : I <= J) (hJK : J <= K) (U)
  proof: by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

中文:
引理 glueDataObjHom_comp
  条件: {I J K : IdealSheafData X} (hIJ : I <= J) (hJK : J <= K) (U)
  证明: by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

Depends on / 依赖: I.glueDataObj, cancel_mono
-/
lemma glueDataObjHom_comp {I J K : IdealSheafData X} (hIJ : I <= J) (hJK : J <= K) (U) :
    glueDataObjHom hJK U ≫ glueDataObjHom hIJ U = glueDataObjHom (hIJ.trans hJK) U := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of ideal sheaf induces an inclusion of subschemes -/
noncomputable
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {I J : IdealSheafData X} (h : I <= J)
  body: J.subschemeCover.openCover.glueMorphisms (fun U => glueDataObjHom h U ≫ I.subschemeCover.f U)
  (by
    intro U V
    simp only [← cancel_mono I.subschemeι, AffineOpenCover.openCover_X, glueDataObjHom_ι_assoc,
      AffineOpenCover.openCover_f, Category.assoc, subschemeCover_map_subschemeι]
    rw [

中文:
定义 inclusion
  签名: {I J : IdealSheafData X} (h : I <= J)
  定义体: J.subschemeCover.openCover.glueMorphisms (fun U => glueDataObjHom h U ≫ I.subschemeCover.f U)
  (by
    intro U V
    simp only [← cancel_mono I.subschemeι, AffineOpenCover.openCover_X, glueDataObjHom_ι_assoc,
      AffineOpenCover.openCover_f, Category.assoc, subschemeCover_map_subschemeι]
    rw [

Depends on / 依赖: AffineOpenCover, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f, Category, Category.assoc, I.subscheme, I.subschemeCover.f, J.subschemeCover.openCover.glueMorphisms, cancel_mono, condition_assoc, glueDataObjHom, glueMorphisms, openCover, openCover_X, openCover_f, pullback, pullback.condition_assoc, subschemeCover
-/
def inclusion {I J : IdealSheafData X} (h : I <= J) :
    J.subscheme ⟶ I.subscheme :=
  J.subschemeCover.openCover.glueMorphisms (fun U => glueDataObjHom h U ≫ I.subschemeCover.f U)
  (by
    intro U V
    simp only [← cancel_mono I.subschemeι, AffineOpenCover.openCover_X, glueDataObjHom_ι_assoc,
      AffineOpenCover.openCover_f, Category.assoc, subschemeCover_map_subschemeι]
    rw [← subschemeCover_map_subschemeι]; rw [pullback.condition_assoc]; rw [subschemeCover_map_subschemeι])

@[reassoc (attr := simp)]
/--
lemma `subSchemeCover_map_inclusion` / 引理 `subSchemeCover_map_inclusion`

English:
lemma subSchemeCover_map_inclusion
  given: {I J : IdealSheafData X} (h : I <= J) (U)
  proof: J.subschemeCover.openCover.ι_glueMorphisms _ _ _

中文:
引理 subSchemeCover_map_inclusion
  条件: {I J : IdealSheafData X} (h : I <= J) (U)
  证明: J.subschemeCover.openCover.ι_glueMorphisms _ _ _

Depends on / 依赖: J.subschemeCover.openCover, openCover, subschemeCover
-/
lemma subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I <= J) (U) :
    J.subschemeCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subschemeCover.f U :=
  J.subschemeCover.openCover.ι_glueMorphisms _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inclusion_subschemeι` / 引理 `inclusion_subschemeι`

English:
lemma inclusion_subschemeι
  given: {I J : IdealSheafData X} (h : I <= J)
  proof: J.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

中文:
引理 inclusion_subschemeι
  条件: {I J : IdealSheafData X} (h : I <= J)
  证明: J.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

Depends on / 依赖: J.subschemeCover.openCover.hom_ext, hom_ext, openCover, subschemeCover
-/
lemma inclusion_subschemeι {I J : IdealSheafData X} (h : I <= J) :
    inclusion h ≫ I.subschemeι = J.subschemeι :=
  J.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `inclusion_id` / 引理 `inclusion_id`

English:
lemma inclusion_id
  given: (I : IdealSheafData X)
  proof: I.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

中文:
引理 inclusion_id
  条件: (I : IdealSheafData X)
  证明: I.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

Depends on / 依赖: I.subschemeCover.openCover.hom_ext, hom_ext, openCover, subschemeCover
-/
lemma inclusion_id (I : IdealSheafData X) :
    inclusion le_rfl = 𝟙 I.subscheme :=
  I.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inclusion_comp` / 引理 `inclusion_comp`

English:
lemma inclusion_comp
  given: {I J K : IdealSheafData X} (h₁ : I <= J) (h₂ : J <= K)
  proof: K.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

中文:
引理 inclusion_comp
  条件: {I J K : IdealSheafData X} (h₁ : I <= J) (h₂ : J <= K)
  证明: K.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

Depends on / 依赖: Fin.eq_castSucc_of_ne_last, Fin.last_le_iff, Finset, Finset.min, K.subschemeCover.openCover.hom_ext, _eq_iff, castSucc, castSucc_mem_finset_iff, castSucc_ne_last, eq_castSucc_of_ne_last, hi.not_gt, hom_ext, i.castSucc, i.castSucc_ne_last, last_le_iff, last_mem_finset, not_gt, openCover, subschemeCover, true_and
-/
lemma inclusion_comp {I J K : IdealSheafData X} (h₁ : I <= J) (h₂ : J <= K) :
    inclusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂) :=
  K.subschemeCover.openCover.hom_ext _ _ fun _ => by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor taking an ideal sheaf to its associated subscheme. -/
@[simps]
noncomputable
/--
Definition of `subschemeFunctor` / `subschemeFunctor` 的定义

English:
definition subschemeFunctor
  signature: (Y : Scheme.{u})
  body: .mk I.unop.subschemeι
  map {I J} h := Over.homMk (IdealSheafData.inclusion h.unop.le)

中文:
定义 subschemeFunctor
  签名: (Y : Scheme.{u})
  定义体: .mk I.unop.subschemeι
  map {I J} h := Over.homMk (IdealSheafData.inclusion h.unop.le)

Depends on / 依赖: Fin.castSucc_le_castSucc_iff, Fin.le_last, Finset, Finset.min, I.unop.subscheme, _eq_iff, and_congr_right_iff, castSucc, castSucc_le_castSucc_iff, castSucc_mem_finset_iff, eq_castSucc_or_eq_last, hi.not_ge, i.castSucc, i.eq_castSucc_or_eq_last, le_last, not_ge
-/
def subschemeFunctor (Y : Scheme.{u}) : (IdealSheafData Y)ᵒᵖ ⥤ Over Y where
  obj I := .mk I.unop.subschemeι
  map {I J} h := Over.homMk (IdealSheafData.inclusion h.unop.le)

end IdealSheafData

noncomputable section image

open Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens)

/--
Definition of `Hom.image` / `Hom.image` 的定义

English:
abbreviation Hom.image
  signature: : Scheme.{u}
  body: f.ker.subscheme

中文:
缩写 Hom.image
  签名: : Scheme.{u}
  定义体: f.ker.subscheme

Depends on / 依赖: _eq_last_iff, f.ker.subscheme, subscheme
-/
abbrev Hom.image : Scheme.{u} := f.ker.subscheme

/--
Definition of `Hom.imageι` / `Hom.imageι` 的定义

English:
abbreviation Hom.imageι
  signature: : f.image ⟶ Y
  body: f.ker.subschemeι

中文:
缩写 Hom.imageι
  签名: : f.image ⟶ Y
  定义体: f.ker.subschemeι

Depends on / 依赖: Fin.castSucc_zero, _eq_castSucc_iff, castSucc_zero, f.ker.subscheme
-/
abbrev Hom.imageι : f.image ⟶ Y := f.ker.subschemeι

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ideal_ker_le_ker_ΓSpecIso_inv_comp` / 引理 `ideal_ker_le_ker_ΓSpecIso_inv_comp`

English:
lemma ideal_ker_le_ker_ΓSpecIso_inv_comp
  proof: by
  let e : Γ(X, f ⁻¹ᵁ ↑U) ≅ Γ(Limits.pullback (C := Scheme) f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by simp [Scheme.Hom.opensRange_pullbackFst])).op
      ≪≫ (Limits.pullback.fst (C := Scheme) f U.1.ι).appIso ⊤
  have he : f.app U ≫ e.hom =
      (ΓSpecIso Γ(Y, ↑U)).inv ≫ (pullback.snd f U.

中文:
引理 ideal_ker_le_ker_ΓSpecIso_inv_comp
  证明: by
  let e : Γ(X, f ⁻¹ᵁ ↑U) ≅ Γ(Limits.pullback (C := Scheme) f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by simp [Scheme.Hom.opensRange_pullbackFst])).op
      ≪≫ (Limits.pullback.fst (C := Scheme) f U.1.ι).appIso ⊤
  have he : f.app U ≫ e.hom =
      (ΓSpecIso Γ(Y, ↑U)).inv ≫ (pullback.snd f U.

Depends on / 依赖: Category, Category.assoc, Fin.eq_castSucc_or_eq_last, Functor, Functor.mapIso_ho, Hom.app_eq_appLE, Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.trans_hom, Limits, Limits.pullback, Limits.pullback.fst, Opens.topIso_hom, Scheme, Scheme.Hom.opensRange_pullbackFst, X.presheaf.mapIso, _eq_castSucc_iff, appIso, appTop, app_eq_appLE
-/
lemma ideal_ker_le_ker_ΓSpecIso_inv_comp :
    f.ker.ideal U <= RingHom.ker ((ΓSpecIso Γ(Y, ↑U)).inv ≫
      (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop).hom := by
  let e : Γ(X, f ⁻¹ᵁ ↑U) ≅ Γ(Limits.pullback (C := Scheme) f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by simp [Scheme.Hom.opensRange_pullbackFst])).op
      ≪≫ (Limits.pullback.fst (C := Scheme) f U.1.ι).appIso ⊤
  have he : f.app U ≫ e.hom =
      (ΓSpecIso Γ(Y, ↑U)).inv ≫ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop := by
    rw [← (Iso.inv_comp_eq _).mpr U.2.isoSpec_inv_appTop]; rw [Category.assoc]; rw [Iso.eq_inv_comp]
    simp only [Opens.topIso_hom, eqToHom_op, Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, Hom.appIso_hom, Hom.appLE_map, Hom.map_appLE, Hom.appLE_comp_appLE,
      Opens.map_top, e, pullback.condition, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.assoc]
    rw [Hom.comp_appLE]; rw [Opens.ι_app]
    exact Hom.map_appLE _ _ (homOfLE le_top).op
  rw [← he]
  refine (IdealSheafData.ideal_ofIdeals_le _ _).trans_eq
    (RingHom.ker_equiv_comp _ e.commRingCatIsoToRingEquiv).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): Use `Hom.toImage` instead which has better def-eqs. -/
noncomputable
/--
Definition of `Hom.toImageAux` / `Hom.toImageAux` 的定义

English:
definition Hom.toImageAux
  signature: : X ⟶ f.image
  body: Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U => (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp 

中文:
定义 Hom.toImageAux
  签名: : X ⟶ f.image
  定义体: Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U => (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp 

Depends on / 依赖: Cover.glueMorphisms, Eq.comm, Fin.castSucc_le_castSucc_iff, Fin.eq_castSucc_or_eq_last, Function, Function.comp_apply, IdealSheafData, IdealSheafData.glueDataObj, OrderHom, OrderHom.comp_coe, Scheme, Scheme.Hom.liftQuotient_comp_assoc, Y.openCoverOfIsOpenCover, _eq_castSucc_iff, cancel_mono, castSucc, castSucc_le_castSucc_iff, comp_apply, comp_coe, condition
-/
def Hom.toImageAux : X ⟶ f.image :=
  Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U => (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc,
      ← pullback.condition, ← pullback.condition_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.toImageAux_spec` / 引理 `Hom.toImageAux_spec`

English:
lemma Hom.toImageAux_spec
  proof: by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc, pullback.condition]

中文:
引理 Hom.toImageAux_spec
  证明: by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc, pullback.condition]

Depends on / 依赖: Cover.hom_ext, Fin.castPred_castSucc, Fin.castSucc_, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff, Fin.predAbove_of_le_castSucc, Fin.succAboveOrderEmb_apply, Fin.succAbove_castSucc_self, Fin.succAbove_of_castSucc_lt, Hom.toImageAux, IdealSheafData, IdealSheafData.glueDataObj, OrderEmbedding, OrderEmbedding.toOrderHom_coe, Scheme, Scheme.Hom.liftQuotient_comp_assoc, Y.openCoverOfIsOpenCover, _eq_castSucc_iff, castPred_castSucc, castSucc_
-/
lemma Hom.toImageAux_spec :
    f.toImageAux ≫ f.imageι = f := by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc, pullback.condition]

/-- The morphism from the domain to the scheme-theoretic image. -/
noncomputable
/--
Definition of `Hom.toImage` / `Hom.toImage` 的定义

English:
definition Hom.toImage
  signature: : X ⟶ f.image
  body: f.toImageAux.copyBase (fun x => ⟨f x, f.range_subset_ker_support ⟨x, rfl⟩⟩)
    (funext fun x => Subtype.ext congr($f.toImageAux_spec x))

@[reassoc (attr := simp)]

中文:
定义 Hom.toImage
  签名: : X ⟶ f.image
  定义体: f.toImageAux.copyBase (fun x => ⟨f x, f.range_subset_ker_support ⟨x, rfl⟩⟩)
    (funext fun x => Subtype.ext congr($f.toImageAux_spec x))

@[reassoc (attr := simp)]

Depends on / 依赖: Fin.predAbove_right_monotone, Subtype, Subtype.ext, copyBase, f.range_subset_ker_support, f.toImageAux.copyBase, f.toImageAux_spec, i.predAbove, monotone, predAbove, predAbove_right_monotone, range_subset_ker_support, toImageAux, toImageAux_spec
-/
def Hom.toImage : X ⟶ f.image :=
  f.toImageAux.copyBase (fun x => ⟨f x, f.range_subset_ker_support ⟨x, rfl⟩⟩)
    (funext fun x => Subtype.ext congr($f.toImageAux_spec x))

@[reassoc (attr := simp)]
/--
lemma `Hom.toImage_imageι` / 引理 `Hom.toImage_imageι`

English:
lemma Hom.toImage_imageι
  proof: by
  convert f.toImageAux_spec
  exact Scheme.Hom.copyBase_eq _ _ _

中文:
引理 Hom.toImage_imageι
  证明: by
  convert f.toImageAux_spec
  exact Scheme.Hom.copyBase_eq _ _ _

Depends on / 依赖: Scheme, Scheme.Hom.copyBase_eq, convert, copyBase_eq, f.toImageAux_spec, toImageAux_spec
-/
lemma Hom.toImage_imageι :
    f.toImage ≫ f.imageι = f := by
  convert f.toImageAux_spec
  exact Scheme.Hom.copyBase_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiCompact
  signature: f] : IsDominant f.toImage where
  body: by
    rw [denseRange_iff_closure_range]; rw [f.imageι.isEmbedding.closure_eq_preimage_closure_image]; rw [← Set.univ_subset_iff]; rw [← Set.image_subset_iff]; rw [Set.image_univ]; rw [IdealSheafData.range_subschemeι]; rw [Hom.support_ker]; rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme

中文:
实例 [QuasiCompact
  签名: f] : IsDominant f.toImage where
  定义体: by
    rw [denseRange_iff_closure_range]; rw [f.imageι.isEmbedding.closure_eq_preimage_closure_image]; rw [← Set.univ_subset_iff]; rw [← Set.image_subset_iff]; rw [Set.image_univ]; rw [IdealSheafData.range_subschemeι]; rw [Hom.support_ker]; rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme

Depends on / 依赖: Hom.support_ker, IdealSheafData, IdealSheafData.range_subscheme, Scheme, Scheme.Hom.comp_base, Set.image_subset_iff, Set.image_univ, Set.range_comp, Set.univ_subset_iff, TopCat, TopCat.coe_comp, closure_eq_preimage_closure_image, coe_comp, comp_base, denseRange_iff_closure_range, f.image, f.toImage_image, image_subset_iff, image_univ, isEmbedding
-/
instance [QuasiCompact f] : IsDominant f.toImage where
  denseRange := by
    rw [denseRange_iff_closure_range]; rw [f.imageι.isEmbedding.closure_eq_preimage_closure_image]; rw [← Set.univ_subset_iff]; rw [← Set.image_subset_iff]; rw [Set.image_univ]; rw [IdealSheafData.range_subschemeι]; rw [Hom.support_ker]; rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [f.toImage_imageι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiCompact
  signature: f] : QuasiCompact f.toImage
  body: have : QuasiCompact (f.toImage ≫ f.imageι) := by simpa
  .of_comp _ f.imageι

中文:
实例 [QuasiCompact
  签名: f] : QuasiCompact f.toImage
  定义体: have : QuasiCompact (f.toImage ≫ f.imageι) := by simpa
  .of_comp _ f.imageι

Depends on / 依赖: QuasiCompact, f.image, f.toImage, of_comp, toImage
-/
instance [QuasiCompact f] : QuasiCompact f.toImage :=
  have : QuasiCompact (f.toImage ≫ f.imageι) := by simpa
  .of_comp _ f.imageι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (IdealSheafData.subschemeι ⊥ : _ ⟶ X)
  body: ⟨Scheme.Hom.toImage (𝟙 X) ≫ IdealSheafData.inclusion bot_le,
    by simp [← cancel_mono (IdealSheafData.subschemeι _)], by simp⟩

中文:
实例 :
  签名: IsIso (IdealSheafData.subschemeι ⊥ : _ ⟶ X)
  定义体: ⟨Scheme.Hom.toImage (𝟙 X) ≫ IdealSheafData.inclusion bot_le,
    by simp [← cancel_mono (IdealSheafData.subschemeι _)], by simp⟩

Depends on / 依赖: IdealSheafData, IdealSheafData.inclusion, IdealSheafData.subscheme, Scheme, Scheme.Hom.toImage, bot_le, cancel_mono, inclusion, toImage
-/
instance : IsIso (IdealSheafData.subschemeι ⊥ : _ ⟶ X) :=
  ⟨Scheme.Hom.toImage (𝟙 X) ≫ IdealSheafData.inclusion bot_le,
    by simp [← cancel_mono (IdealSheafData.subschemeι _)], by simp⟩

/--
lemma `isIso_subschemeι_iff_eq_bot` / 引理 `isIso_subschemeι_iff_eq_bot`

English:
lemma isIso_subschemeι_iff_eq_bot
  given: (I : X.IdealSheafData)
  statement: IsIso I.subschemeι ↔ I = ⊥
  proof: ⟨fun h => by simp [← I.ker_subschemeι], fun h => h ▸ inferInstance⟩

中文:
引理 isIso_subschemeι_iff_eq_bot
  条件: (I : X.IdealSheafData)
  结论: IsIso I.subschemeι ↔ I = ⊥
  证明: ⟨fun h => by simp [← I.ker_subschemeι], fun h => h ▸ inferInstance⟩

Depends on / 依赖: I.ker_subscheme
-/
lemma isIso_subschemeι_iff_eq_bot (I : X.IdealSheafData) : IsIso I.subschemeι ↔ I = ⊥ :=
  ⟨fun h => by simp [← I.ker_subschemeι], fun h => h ▸ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.toImage_app` / 引理 `Hom.toImage_app`

English:
lemma Hom.toImage_app
  proof: by
  have := ConcreteCategory.epi_of_surjective _ (f.ker.subschemeι_app_surjective U)
  rw [← cancel_epi (f.ker.subschemeι.app U)]; rw [← Scheme.Hom.comp_app]; rw [Scheme.Hom.congr_app f.toImage_imageι]; rw [f.ker.subschemeι_app]; rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]
  simp only [Hom.com

中文:
引理 Hom.toImage_app
  证明: by
  have := ConcreteCategory.epi_of_surjective _ (f.ker.subschemeι_app_surjective U)
  rw [← cancel_epi (f.ker.subschemeι.app U)]; rw [← Scheme.Hom.comp_app]; rw [Scheme.Hom.congr_app f.toImage_imageι]; rw [f.ker.subschemeι_app]; rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]
  simp only [Hom.com

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, ConcreteCategory, ConcreteCategory.epi_of_surjective, Functor, Functor.map_inv, Hom.comp_base, Ideal.Quotient.lift_comp_mk, IsIso.eq_comp_inv, Iso.inv_hom_id_assoc, Opens.map_comp_obj, Quotient, Scheme, Scheme.Hom.comp_app, Scheme.Hom.congr_app, cancel_epi, comp_app
-/
lemma Hom.toImage_app :
    f.toImage.app (f.imageι ⁻¹ᵁ U) =
      (f.ker.subschemeObjIso U).hom ≫ CommRingCat.ofHom
        (Ideal.Quotient.lift _ (f.app U.1).hom (IdealSheafData.ideal_ofIdeals_le _ _)) := by
  have := ConcreteCategory.epi_of_surjective _ (f.ker.subschemeι_app_surjective U)
  rw [← cancel_epi (f.ker.subschemeι.app U)]; rw [← Scheme.Hom.comp_app]; rw [Scheme.Hom.congr_app f.toImage_imageι]; rw [f.ker.subschemeι_app]; rw [← IsIso.eq_comp_inv]; rw [← Functor.map_inv]
  simp only [Hom.comp_base, Opens.map_comp_obj, Category.assoc,
    Iso.inv_hom_id_assoc, eqToHom_op, inv_eqToHom]
  rw [← reassoc_of% CommRingCat.ofHom_comp]; rw [Ideal.Quotient.lift_comp_mk]; rw [CommRingCat.ofHom_hom]; rw [eqToHom_refl]; rw [CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.toImage_app_injective` / 引理 `Hom.toImage_app_injective`

English:
lemma Hom.toImage_app_injective
  given: [QuasiCompact f]
  proof: by
  simp only [f.toImage_app U, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp]
  exact (RingHom.lift_injective_of_ker_le_ideal _ _ (by simp)).comp
    (f.ker.subschemeObjIso U).commRingCatIsoToRingEquiv.injective

中文:
引理 Hom.toImage_app_injective
  条件: [QuasiCompact f]
  证明: by
  simp only [f.toImage_app U, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp]
  exact (RingHom.lift_injective_of_ker_le_ideal _ _ (by simp)).comp
    (f.ker.subschemeObjIso U).commRingCatIsoToRingEquiv.injective

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom, RingHom.coe_comp, RingHom.lift_injective_of_ker_le_ideal, coe_comp, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.injective, f.ker.subschemeObjIso, f.toImage_app, hom_comp, hom_ofHom, injective, lift_injective_of_ker_le_ideal, subschemeObjIso, toImage_app
-/
lemma Hom.toImage_app_injective [QuasiCompact f] :
    Function.Injective (f.toImage.app (f.imageι ⁻¹ᵁ U)) := by
  simp only [f.toImage_app U, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp]
  exact (RingHom.lift_injective_of_ker_le_ideal _ _ (by simp)).comp
    (f.ker.subschemeObjIso U).commRingCatIsoToRingEquiv.injective

/--
lemma `Hom.stalkFunctor_toImage_injective` / 引理 `Hom.stalkFunctor_toImage_injective`

English:
lemma Hom.stalkFunctor_toImage_injective
  given: [QuasiCompact f] (x)
  proof: by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    (hB := (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing))
  rintro _ ⟨U, hU, rfl⟩
  exact f.toImage_app_injective ⟨U, hU⟩

中文:
引理 Hom.stalkFunctor_toImage_injective
  条件: [QuasiCompact f] (x)
  证明: by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    (hB := (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing))
  rintro _ ⟨U, hU, rfl⟩
  exact f.toImage_app_injective ⟨U, hU⟩

Depends on / 依赖: Presheaf, TopCat, TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis, Y.isBasis_affineOpens.of_isInducing, f.image, f.toImage_app_injective, isBasis_affineOpens, isEmbedding, isEmbedding.isInducing, isInducing, of_isInducing, stalkFunctor_map_injective_of_isBasis, toImage_app_injective
-/
lemma Hom.stalkFunctor_toImage_injective [QuasiCompact f] (x) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor _ x).map f.toImage.c) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    (hB := (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing))
  rintro _ ⟨U, hU, rfl⟩
  exact f.toImage_app_injective ⟨U, hU⟩

set_option backward.defeqAttrib.useBackward true in
open IdealSheafData in
/-- The adjunction between `Y.IdealSheafData` and `(Over Y)ᵒᵖ` given by taking kernels. -/
@[simps]
noncomputable
/--
Definition of `kerAdjunction` / `kerAdjunction` 的定义

English:
definition kerAdjunction
  signature: (Y : Scheme.{u})
  body: eqToHom (by simp)
  counit.app f := (Over.homMk f.unop.hom.toImage f.unop.hom.toImage_imageι).op
  counit.naturality _ _ _ := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])
  left_triangle_components I := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])

中文:
定义 kerAdjunction
  签名: (Y : Scheme.{u})
  定义体: eqToHom (by simp)
  counit.app f := (Over.homMk f.unop.hom.toImage f.unop.hom.toImage_imageι).op
  counit.naturality _ _ _ := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])
  left_triangle_components I := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])

Depends on / 依赖: eqToHom
-/
def kerAdjunction (Y : Scheme.{u}) : (subschemeFunctor Y).rightOp ⊣ Y.kerFunctor where
  unit.app I := eqToHom (by simp)
  counit.app f := (Over.homMk f.unop.hom.toImage f.unop.hom.toImage_imageι).op
  counit.naturality _ _ _ := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])
  left_triangle_components I := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (IdealSheafData.subschemeFunctor Y).Full
  body: have : IsIso Y.kerAdjunction.rightOp.counit := by
    simp [NatTrans.isIso_iff_isIso_app, CategoryTheory.instIsIsoEqToHom]
  Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full

中文:
实例 :
  签名: (IdealSheafData.subschemeFunctor Y).Full
  定义体: have : IsIso Y.kerAdjunction.rightOp.counit := by
    simp [NatTrans.isIso_iff_isIso_app, CategoryTheory.instIsIsoEqToHom]
  Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full

Depends on / 依赖: CategoryTheory, CategoryTheory.instIsIsoEqToHom, NatTrans, NatTrans.isIso_iff_isIso_app, Y.kerAdjunction.rightOp.counit, Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full, counit, fullyFaithfulROfIsIsoCounit, instIsIsoEqToHom, isIso_iff_isIso_app, kerAdjunction, rightOp
-/
instance : (IdealSheafData.subschemeFunctor Y).Full :=
  have : IsIso Y.kerAdjunction.rightOp.counit := by
    simp [NatTrans.isIso_iff_isIso_app, CategoryTheory.instIsIsoEqToHom]
  Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full

end image

end Scheme

end AlgebraicGeometry
