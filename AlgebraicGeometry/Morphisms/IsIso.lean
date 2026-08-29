/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!

# Being an isomorphism is local at the target

-/

universe u

public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

/--
lemma `isIso_iff_isOpenImmersion_and_surjective` / 引理 `isIso_iff_isOpenImmersion_and_surjective`

English:
lemma isIso_iff_isOpenImmersion_and_surjective
  given: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: by
  rw [surjective_iff]; rw [← TopCat.epi_iff_surjective]; rw [isIso_iff_isOpenImmersion_and_epi_base]

中文:
引理 isIso_iff_isOpenImmersion_and_surjective
  条件: {X Y : Scheme.{u}} (f : X ⟶ Y)
  证明: by
  rw [surjective_iff]; rw [← TopCat.epi_iff_surjective]; rw [isIso_iff_isOpenImmersion_and_epi_base]

Depends on / 依赖: TopCat, TopCat.epi_iff_surjective, epi_iff_surjective, isIso_iff_isOpenImmersion_and_epi_base, surjective_iff
-/
lemma isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f := by
  rw [surjective_iff]; rw [← TopCat.epi_iff_surjective]; rw [isIso_iff_isOpenImmersion_and_epi_base]

/--
lemma `isomorphisms_eq_isOpenImmersion_inf_surjective` / 引理 `isomorphisms_eq_isOpenImmersion_inf_surjective`

English:
lemma isomorphisms_eq_isOpenImmersion_inf_surjective
  proof: by
  ext
  rw [isomorphisms.iff]; rw [isIso_iff_isOpenImmersion_and_surjective]
  rfl

中文:
引理 isomorphisms_eq_isOpenImmersion_inf_surjective
  证明: by
  ext
  rw [isomorphisms.iff]; rw [isIso_iff_isOpenImmersion_and_surjective]
  rfl

Depends on / 依赖: isIso_iff_isOpenImmersion_and_surjective, isomorphisms, isomorphisms.iff
-/
lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  rw [isomorphisms.iff]; rw [isIso_iff_isOpenImmersion_and_surjective]
  rfl

/--
lemma `isomorphisms_eq_stalkwise` / 引理 `isomorphisms_eq_stalkwise`

English:
lemma isomorphisms_eq_stalkwise
  proof: by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective]; rw [isOpenImmersion_eq_inf]; rw [surjective_eq_topologically]; rw [inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H => inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) =>
   

中文:
引理 isomorphisms_eq_stalkwise
  证明: by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective]; rw [isOpenImmersion_eq_inf]; rw [surjective_eq_topologically]; rw [inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H => inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) =>
   

Depends on / 依赖: TopCat, TopCat.homeoOfIso, TopCat.isoOfHomeo, e.isOpenEmbedding, e.surjective, f.base, homeoOfIso, inf_right_comm, isOpenEmbedding, isOpenImmersion_eq_inf, isoOfHomeo, isomorphisms_eq_isOpenImmersion_inf_surjective, surjective, surjective_eq_topologically, toHomeomorphOfSurjective
-/
lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f => Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective]; rw [isOpenImmersion_eq_inf]; rw [surjective_eq_topologically]; rw [inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H => inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) =>
    let e := (TopCat.homeoOfIso <| asIso f.base); ⟨e.isOpenEmbedding, e.surjective⟩⟩

example : IsZariskiLocalAtTarget (isomorphisms Scheme) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAffineProperty (isomorphisms Scheme) fun X _ f _ => IsAffine X ∧ IsIso (f.appTop)
  body: by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ => (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) => ⟨.of_isIso f, inferInstance⟩⟩

中文:
实例 :
  签名: HasAffine命题erty (isomorphisms Scheme) fun X _ f _ => IsAffine X ∧ IsIso (f.appTop)
  定义体: by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ => (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) => ⟨.of_isIso f, inferInstance⟩⟩

Depends on / 依赖: HasAffineProperty, HasAffineProperty.of_isZariskiLocalAtTarget, Scheme, Spec.map, appTop, arrow_mk_iso_iff, convert, f.appTop, isomorphisms, of_isIso, of_isZariskiLocalAtTarget
-/
instance : HasAffineProperty (isomorphisms Scheme) fun X _ f _ => IsAffine X ∧ IsIso (f.appTop) := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ => (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) => ⟨.of_isIso f, inferInstance⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget (monomorphisms Scheme)
  body: diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

中文:
实例 :
  签名: IsZariskiLocalAtTarget (monomorphisms Scheme)
  定义体: diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

Depends on / 依赖: Scheme, diagonal_isomorphisms
-/
instance : IsZariskiLocalAtTarget (monomorphisms Scheme) :=
  diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_SpecMap_iff` / 引理 `isIso_SpecMap_iff`

English:
lemma isIso_SpecMap_iff
  given: {R S : CommRingCat.{u}} {f : R ⟶ S}
  proof: by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  rw [← isomorphisms.iff]; rw [(isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]; rw [isomorphisms.iff]
  infer_instance

中文:
引理 isIso_SpecMap_iff
  条件: {R S : CommRingCat.{u}} {f : R ⟶ S}
  证明: by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  rw [← isomorphisms.iff]; rw [(isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]; rw [isomorphisms.iff]
  infer_instance

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, arrow_mk_iso_iff, infer_instance, isIso_iff_bijective, isomorphisms, isomorphisms.iff
-/
lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  rw [← isomorphisms.iff]; rw [(isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]; rw [isomorphisms.iff]
  infer_instance

end AlgebraicGeometry
