/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant

/-!
# Composition of rational maps

This file defines composition for partial maps and rational maps between schemes.

## Main definitions

- `Scheme.PartialMap.comp`: given a dominant partial map `f : X.PartialMap Y` and any partial map
  `g : Y.PartialMap Z`, their composition `f.comp g : X.PartialMap Z` is defined on the preimage
  of `g`'s domain under `f`.
- `Scheme.RationalMap.comp`: composition of rational maps, defined via a dominant representative.

## Main statements

- `Scheme.PartialMap.comp_equiv_of_equiv`: Composition respects equivalence of partial maps.
- `Scheme.PartialMap.comp_assoc`: Composition of partial maps is associative.
- `Scheme.RationalMap.comp_assoc`: Composition of rational maps is associative.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

section PreirreducibleSpace

variable [PreirreducibleSpace X] [Nonempty Y]

namespace PartialMap

/-- Composition of partial maps. The domain of `f.comp g` is the preimage of `g.domain` under `f`,
viewed as an open subscheme of `X`. Requires `f.hom` to be dominant so that the domain is dense. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  body: f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

中文:
定义 comp
  签名: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  定义体: f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

Depends on / 依赖: domain, f.domain, f.hom, g.domain
-/
noncomputable def comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_restrict_left` / 引理 `comp_restrict_left`

English:
lemma comp_restrict_left
  statement: (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
  proof: by
  ext
  · simp [ι_image_homOfLE_eq_ι_image_inf]
  · simp [morphismRestrict_comp, isoImage_ι_inv_morphismRestrict_homOfLE_assoc, isoOfEq_hom]

中文:
引理 comp_restrict_left
  结论: (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
  证明: by
  ext
  · simp [ι_image_homOfLE_eq_ι_image_inf]
  · simp [morphismRestrict_comp, isoImage_ι_inv_morphismRestrict_homOfLE_assoc, isoOfEq_hom]

Depends on / 依赖: isoOfEq_hom, morphismRestrict_comp
-/
lemma comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  ext
  · simp [ι_image_homOfLE_eq_ι_image_inf]
  · simp [morphismRestrict_comp, isoImage_ι_inv_morphismRestrict_homOfLE_assoc, isoOfEq_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_restrict_right` / 引理 `comp_restrict_right`

English:
lemma comp_restrict_right
  statement: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  proof: by
  ext
  · simp
  · simp [← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

中文:
引理 comp_restrict_right
  结论: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  证明: by
  ext
  · simp
  · simp [← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

Depends on / 依赖: domain, f.domain, f.hom, f.hom.preimage_mono, isoImage_inv_homOfLE_assoc, morphismRestrict_homOfLE_assoc, preimage_mono
-/
lemma comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V <= g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ((f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense <| by
        simpa [← Set.nonempty_preimage_iff] using
          f.hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty)
      (f.domain.ι.image_mono (f.hom.preimage_mono hV')) := by
  ext
  · simp
  · simp [← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_equiv_of_equiv_left` / 引理 `comp_equiv_of_equiv_left`

English:
lemma comp_equiv_of_equiv_left
  statement: {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom]
  proof: by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left]; rw [comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

中文:
引理 comp_equiv_of_equiv_left
  结论: {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom]
  证明: by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left]; rw [comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

Depends on / 依赖: PartialMap, PartialMap.ext, comp_restrict_left, equiv_of_restrict_eq, replace, restrict
-/
lemma comp_equiv_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left]; rw [comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_equiv_of_equiv_right` / 引理 `comp_equiv_of_equiv_right`

English:
lemma comp_equiv_of_equiv_right
  statement: (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z}
  proof: by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right]; rw [comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

中文:
引理 comp_equiv_of_equiv_right
  结论: (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z}
  证明: by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right]; rw [comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

Depends on / 依赖: PartialMap, PartialMap.ext, comp_restrict_right, equiv_of_restrict_eq, f.comp, replace, restrict
-/
lemma comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z}
    (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right]; rw [comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

/--
lemma `comp_equiv_of_equiv` / 引理 `comp_equiv_of_equiv`

English:
lemma comp_equiv_of_equiv
  statement: (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
  proof: equivalence_rel.trans (comp_equiv_of_equiv_left hf _) (comp_equiv_of_equiv_right _ hg)

中文:
引理 comp_equiv_of_equiv
  结论: (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
  证明: equivalence_rel.trans (comp_equiv_of_equiv_left hf _) (comp_equiv_of_equiv_right _ hg)

Depends on / 依赖: comp_equiv_of_equiv_left, comp_equiv_of_equiv_right, equivalence_rel, equivalence_rel.trans
-/
lemma comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) :=
  equivalence_rel.trans (comp_equiv_of_equiv_left hf _) (comp_equiv_of_equiv_right _ hg)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `isDominant_comp_hom` / 实例 `isDominant_comp_hom`

English:
instance isDominant_comp_hom
  signature: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  body: by
  dsimp only [comp_domain, comp_hom]
  have := IsZariskiLocalAtTarget.restrict ‹IsDominant f.hom› g.domain
  infer_instance

中文:
实例 isDominant_comp_hom
  签名: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  定义体: by
  dsimp only [comp_domain, comp_hom]
  have := IsZariskiLocalAtTarget.restrict ‹IsDominant f.hom› g.domain
  infer_instance

Depends on / 依赖: IsDominant, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, comp_domain, comp_hom, domain, f.hom, g.domain, infer_instance, restrict
-/
instance isDominant_comp_hom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    [IsDominant g.hom] : IsDominant (f.comp g).hom := by
  dsimp only [comp_domain, comp_hom]
  have := IsZariskiLocalAtTarget.restrict ‹IsDominant f.hom› g.domain
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
  proof: by
  ext
  · simp_rw [comp_domain, comp_hom, ← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
      ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image, image_morphismRestrict_preimage]
  · dsimp
    simp_rw [morphismRestrict_comp, morphismRestrict_ι_image_ι_isoImage_inv_assoc,
      Hom.comp

中文:
引理 comp_assoc
  结论: {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
  证明: by
  ext
  · simp_rw [comp_domain, comp_hom, ← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
      ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image, image_morphismRestrict_preimage]
  · dsimp
    simp_rw [morphismRestrict_comp, morphismRestrict_ι_image_ι_isoImage_inv_assoc,
      Hom.comp

Depends on / 依赖: Category, Category.assoc, Hom.comp_image, Hom.comp_preimage, Hom.inv_preimage, Hom.isoImage_hom_, cancel_mono, comp_domain, comp_hom, comp_image, comp_preimage, conv_lhs, conv_rhs, image_morphismRestrict_preimage, inv_preimage, morphismRestrict_comp, simp_rw
-/
lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f : X₁.PartialMap X₂) [IsDominant f.hom] (g : X₂.PartialMap X₃)
    [IsDominant g.hom] (h : X₃.PartialMap Y) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext
  · simp_rw [comp_domain, comp_hom, ← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
      ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image, image_morphismRestrict_preimage]
  · dsimp
    simp_rw [morphismRestrict_comp, morphismRestrict_ι_image_ι_isoImage_inv_assoc,
      Hom.comp_preimage, Category.assoc]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp [← cancel_mono (Opens.ι _)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `comp_toPartialMap` / 引理 `comp_toPartialMap`

English:
lemma comp_toPartialMap
  given: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z)
  proof: by
  ext1
  · simp
  · simp_rw [comp_hom, Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, topIso_hom,
      morphismRestrict_ι_assoc, f.domain.isoImage_ι_inv_ι_assoc, isoOfEq_hom]

中文:
引理 comp_toPartialMap
  条件: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z)
  证明: by
  ext1
  · simp
  · simp_rw [comp_hom, Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, topIso_hom,
      morphismRestrict_ι_assoc, f.domain.isoImage_ι_inv_ι_assoc, isoOfEq_hom]

Depends on / 依赖: Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, comp_hom, domain, f.domain.isoImage_, isoOfEq_hom, simp_rw, toPartialMap_domain, toPartialMap_hom, topIso_hom
-/
lemma comp_toPartialMap (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) :
    f.comp g.toPartialMap = f.compHom g := by
  ext1
  · simp
  · simp_rw [comp_hom, Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, topIso_hom,
      morphismRestrict_ι_assoc, f.domain.isoImage_ι_inv_ι_assoc, isoOfEq_hom]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (f : X.PartialMap Y) [IsDominant f.hom]
  statement: f.comp (PartialMap.id Y) = f
  proof: by simp

中文:
引理 comp_id
  条件: (f : X.PartialMap Y) [IsDominant f.hom]
  结论: f.comp (PartialMap.id Y) = f
  证明: by simp
-/
lemma comp_id (f : X.PartialMap Y) [IsDominant f.hom] : f.comp (PartialMap.id Y) = f := by simp

end PartialMap

namespace RationalMap

-- If better def-eqs are required, consider refactoring this by using `Quotient.liftOn₂`
-- and a bundled structure `DominantPartialMap`.
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
  body: Quotient.liftOn g (PartialMap.toRationalMap ∘ f.representative.comp) fun _ _ h => by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ h

中文:
定义 comp
  签名: (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
  定义体: Quotient.liftOn g (PartialMap.toRationalMap ∘ f.representative.comp) fun _ _ h => by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ h

Depends on / 依赖: Function, Function.comp_apply, PartialMap, PartialMap.comp_equiv_of_equiv_right, PartialMap.toRationalMap, PartialMap.toRationalMap_eq_iff, Quotient, Quotient.liftOn, comp_apply, comp_equiv_of_equiv_right, f.representative.comp, liftOn, representative, toRationalMap, toRationalMap_eq_iff
-/
noncomputable def comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
Quotient.liftOn g (PartialMap.toRationalMap ∘ f.representative.comp) fun _ _ h => by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ h

/--
lemma `comp_def` / 引理 `comp_def`

English:
lemma comp_def
  given: (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z)
  proof: rfl

中文:
引理 comp_def
  条件: (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z)
  证明: rfl
-/
lemma comp_def (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z) :
    f.comp g.toRationalMap = (f.representative.comp g).toRationalMap :=
  rfl

/--
lemma `toRationalMap_comp` / 引理 `toRationalMap_comp`

English:
lemma toRationalMap_comp
  given: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  proof: by
  rw [RationalMap.comp_def]; rw [PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.representative_toRationalMap_equiv _

@[simp]

中文:
引理 toRationalMap_comp
  条件: (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
  证明: by
  rw [RationalMap.comp_def]; rw [PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.representative_toRationalMap_equiv _

@[simp]

Depends on / 依赖: PartialMap, PartialMap.comp_equiv_of_equiv_left, PartialMap.toRationalMap_eq_iff, RationalMap, RationalMap.comp_def, comp_def, comp_equiv_of_equiv_left, f.representative_toRationalMap_equiv, representative_toRationalMap_equiv, toRationalMap_eq_iff
-/
lemma toRationalMap_comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    f.toRationalMap.comp g.toRationalMap = (f.comp g).toRationalMap := by
  rw [RationalMap.comp_def]; rw [PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.representative_toRationalMap_equiv _

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (f : X ⤏ Y) [f.IsDominant]
  statement: f.comp (RationalMap.id Y) = f
  proof: by
  simp [RationalMap.comp_def]

中文:
引理 comp_id
  条件: (f : X ⤏ Y) [f.IsDominant]
  结论: f.comp (RationalMap.id Y) = f
  证明: by
  simp [RationalMap.comp_def]

Depends on / 依赖: RationalMap, RationalMap.comp_def, comp_def
-/
lemma comp_id (f : X ⤏ Y) [f.IsDominant] : f.comp (RationalMap.id Y) = f := by
  simp [RationalMap.comp_def]

instance (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) [g.IsDominant] : (f.comp g).IsDominant := by
  rw [← g.toRationalMap_representative]; rw [RationalMap.comp_def]
  infer_instance

/--
lemma `comp_toRationalMap` / 引理 `comp_toRationalMap`

English:
lemma comp_toRationalMap
  given: (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z)
  proof: by
  simp [comp_def, PartialMap.comp_toPartialMap]

@[grind _=_]

中文:
引理 comp_toRationalMap
  条件: (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z)
  证明: by
  simp [comp_def, PartialMap.comp_toPartialMap]

@[grind _=_]

Depends on / 依赖: PartialMap, PartialMap.comp_toPartialMap, comp_def, comp_toPartialMap
-/
lemma comp_toRationalMap (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z) :
    f.comp h.toRationalMap = f.compHom h := by
  simp [comp_def, PartialMap.comp_toPartialMap]

@[grind _=_]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
  proof: by
  rw [← f₃.toRationalMap_representative]
  simp_rw [comp_def, ← PartialMap.comp_assoc, PartialMap.toRationalMap_eq_iff]
  apply PartialMap.comp_equiv_of_equiv_left
  rw [← f₂.toRationalMap_representative]; rw [comp_def]
  apply (f₁.representative.comp f₂.representative).representative_toRationalM

中文:
引理 comp_assoc
  结论: {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
  证明: by
  rw [← f₃.toRationalMap_representative]
  simp_rw [comp_def, ← PartialMap.comp_assoc, PartialMap.toRationalMap_eq_iff]
  apply PartialMap.comp_equiv_of_equiv_left
  rw [← f₂.toRationalMap_representative]; rw [comp_def]
  apply (f₁.representative.comp f₂.representative).representative_toRationalM

Depends on / 依赖: PartialMap, PartialMap.comp_assoc, PartialMap.comp_equiv_of_equiv_left, PartialMap.comp_equiv_of_equiv_right, PartialMap.toRationalMap_eq_iff, comp_assoc, comp_def, comp_equiv_of_equiv_left, comp_equiv_of_equiv_right, representative, representative.comp, representative_toRationalMap_equiv, representative_toRationalMap_equiv.trans, simp_rw, toRationalMap_eq_iff, toRationalMap_representative
-/
lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f₁ : X₁ ⤏ X₂) [f₁.IsDominant] (f₂ : X₂ ⤏ X₃) [f₂.IsDominant] (f₃ : X₃ ⤏ Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) := by
  rw [← f₃.toRationalMap_representative]
  simp_rw [comp_def, ← PartialMap.comp_assoc, PartialMap.toRationalMap_eq_iff]
  apply PartialMap.comp_equiv_of_equiv_left
  rw [← f₂.toRationalMap_representative]; rw [comp_def]
  apply (f₁.representative.comp f₂.representative).representative_toRationalMap_equiv.trans
  apply PartialMap.comp_equiv_of_equiv_right
  rw [toRationalMap_representative]

/--
Instance `isOver_comp` / 实例 `isOver_comp`

English:
instance isOver_comp
  signature: {S : Scheme.{u}} [IrreducibleSpace Y] [Nonempty Z] [X.Over S] [Y.Over S]
  body: by
  rw [isOver_iff]; rw [← comp_toRationalMap]; rw [comp_assoc]; rw [comp_toRationalMap]; rw [isOver_iff.mp ‹g.IsOver S›]; rw [comp_toRationalMap]; rw [RationalMap.isOver_iff.mp ‹f.IsOver S›]

中文:
实例 isOver_comp
  签名: {S : Scheme.{u}} [IrreducibleSpace Y] [Nonempty Z] [X.Over S] [Y.Over S]
  定义体: by
  rw [isOver_iff]; rw [← comp_toRationalMap]; rw [comp_assoc]; rw [comp_toRationalMap]; rw [isOver_iff.mp ‹g.IsOver S›]; rw [comp_toRationalMap]; rw [RationalMap.isOver_iff.mp ‹f.IsOver S›]

Depends on / 依赖: IsOver, RationalMap, RationalMap.isOver_iff.mp, comp_assoc, comp_toRationalMap, f.IsOver, g.IsOver, isOver_iff, isOver_iff.mp
-/
instance isOver_comp {S : Scheme.{u}} [IrreducibleSpace Y] [Nonempty Z] [X.Over S] [Y.Over S]
    [Z.Over S] (f : X ⤏ Y) [f.IsDominant] [f.IsOver S] (g : Y ⤏ Z) [g.IsDominant] [g.IsOver S] :
    (f.comp g).IsOver S := by
  rw [isOver_iff]; rw [← comp_toRationalMap]; rw [comp_assoc]; rw [comp_toRationalMap]; rw [isOver_iff.mp ‹g.IsOver S›]; rw [comp_toRationalMap]; rw [RationalMap.isOver_iff.mp ‹f.IsOver S›]

end RationalMap

end PreirreducibleSpace

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `PartialMap.id_comp` / 引理 `PartialMap.id_comp`

English:
lemma PartialMap.id_comp
  given: {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y)
  proof: by
  ext1
  · simp_rw [comp_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Category.comp_id,
      ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image, Iso.inv_hom_id, Hom.id_image]
  · simp_rw [comp_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain, morphismRestrict_comp,
      morphismRestr

中文:
引理 PartialMap.id_comp
  条件: {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y)
  证明: by
  ext1
  · simp_rw [comp_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Category.comp_id,
      ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image, Iso.inv_hom_id, Hom.id_image]
  · simp_rw [comp_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain, morphismRestrict_comp,
      morphismRestr

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Hom.comp_image, Hom.comp_preimage, Hom.id_image, Hom.id_preimage, Hom.inv_image, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Iso.inv_hom_id, Iso.inv_hom_id_assoc, X.topIso.hom.isoImage_preimage_hom_homOfLE, X.topIso_hom, comp_domain, comp_hom, comp_id, comp_image, comp_preimage, id_image
-/
lemma PartialMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y) :
    (PartialMap.id X).comp f = f := by
  ext1
  · simp_rw [comp_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Category.comp_id,
      ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image, Iso.inv_hom_id, Hom.id_image]
  · simp_rw [comp_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain, morphismRestrict_comp,
      morphismRestrict_id, ← X.topIso_hom, Hom.comp_preimage, Hom.id_preimage,
      Category.comp_id, ← X.topIso.hom.isoImage_preimage_hom_homOfLE, Category.assoc,
      Iso.inv_hom_id_assoc]
    rfl

@[simp, grind =]
/--
lemma `RationalMap.id_comp` / 引理 `RationalMap.id_comp`

English:
lemma RationalMap.id_comp
  given: {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⤏ Y)
  proof: by
  rw [← f.toRationalMap_representative]; rw [toRationalMap_comp]; rw [PartialMap.id_comp]

中文:
引理 RationalMap.id_comp
  条件: {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⤏ Y)
  证明: by
  rw [← f.toRationalMap_representative]; rw [toRationalMap_comp]; rw [PartialMap.id_comp]

Depends on / 依赖: PartialMap, PartialMap.id_comp, f.toRationalMap_representative, id_comp, toRationalMap_comp, toRationalMap_representative
-/
lemma RationalMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⤏ Y) :
    (RationalMap.id X).comp f = f := by
  rw [← f.toRationalMap_representative]; rw [toRationalMap_comp]; rw [PartialMap.id_comp]

end AlgebraicGeometry.Scheme
