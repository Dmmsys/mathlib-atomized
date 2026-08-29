/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# Localization with respect to a Serre class

The main definition in this file is `ObjectProperty.SerreClassLocalization.abelian`
which shows that if `L : C ⥤ D` is a localization functor with respect to
the class of morphisms `P.isoModSerre` for a Serre class `P : ObjectProperty C`
in the abelian category `C`, then `D` is an abelian category.

We also show that a functor `G : D ⥤ E` to an abelian category is exact iff
the composition `L ⋙ G` is.

-/

@[expose] public section

universe v'' v' v u'' u' u

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/--
lemma `exists_epiModSerre_comp_eq_zero_iff` / 引理 `exists_epiModSerre_comp_eq_zero_iff`

English:
lemma exists_epiModSerre_comp_eq_zero_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · exact ⟨_, kernel.ι f, P.prop_of_iso (Abelian.coimageIsoImage f).symm hf, by simp⟩

中文:
引理 存在_epiModSerre_comp_eq_zero_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · exact ⟨_, kernel.ι f, P.prop_of_iso (Abelian.coimageIsoImage f).symm hf, by simp⟩

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, Abelian.factorThruImage, P.epiModSerre.comp_mem, P.prop_of_iso, cat_disch, coimageIsoImage, comp_mem, epiModSerre, epiModSerre_of_epi, epiModSerre_zero_iff, factorThruImage, kernel, prop_of_iso
-/
lemma exists_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (exists (X' : C) (s : X' ⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · exact ⟨_, kernel.ι f, P.prop_of_iso (Abelian.coimageIsoImage f).symm hf, by simp⟩

/--
lemma `exists_isoModSerre_comp_eq_zero_iff` / 引理 `exists_isoModSerre_comp_eq_zero_iff`

English:
lemma exists_isoModSerre_comp_eq_zero_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_epiModSerre_comp_eq_zero_iff P]
    exact ⟨Y', s, hs.2, eq⟩
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    simpa only [isoModSerre_iff_of_mono] using!
      P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

中文:
引理 存在_isoModSerre_comp_eq_zero_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_epiModSerre_comp_eq_zero_iff P]
    exact ⟨Y', s, hs.2, eq⟩
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    simpa only [isoModSerre_iff_of_mono] using!
      P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, P.prop_of_iso, coimageIsoImage, exists_epiModSerre_comp_eq_zero_iff, isoModSerre_iff_of_mono, kernel, prop_of_iso
-/
lemma exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (exists (X' : C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_epiModSerre_comp_eq_zero_iff P]
    exact ⟨Y', s, hs.2, eq⟩
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    simpa only [isoModSerre_iff_of_mono] using!
      P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

/--
lemma `exists_comp_monoModSerre_eq_zero_iff` / 引理 `exists_comp_monoModSerre_eq_zero_iff`

English:
lemma exists_comp_monoModSerre_eq_zero_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, hf, by simp⟩

中文:
引理 存在_comp_monoModSerre_eq_zero_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, hf, by simp⟩

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, Abelian.factorThruCoimage, P.monoModSerre.comp_mem, P.prop_of_iso, cat_disch, coimageIsoImage, cokernel, comp_mem, factorThruCoimage, monoModSerre, monoModSerre_of_mono, monoModSerre_zero_iff, prop_of_iso
-/
lemma exists_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (exists (Y' : C) (s : Y ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, hf, by simp⟩

/--
lemma `exists_comp_isoModSerre_eq_zero_iff` / 引理 `exists_comp_isoModSerre_eq_zero_iff`

English:
lemma exists_comp_isoModSerre_eq_zero_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_comp_monoModSerre_eq_zero_iff P]
    exact ⟨Y', s, hs.1, eq⟩
  · refine ⟨_, cokernel.π f, by rwa [isoModSerre_iff_of_epi], by simp⟩

中文:
引理 存在_comp_isoModSerre_eq_zero_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_comp_monoModSerre_eq_zero_iff P]
    exact ⟨Y', s, hs.1, eq⟩
  · refine ⟨_, cokernel.π f, by rwa [isoModSerre_iff_of_epi], by simp⟩

Depends on / 依赖: cokernel, exists_comp_monoModSerre_eq_zero_iff, isoModSerre_iff_of_epi
-/
lemma exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (exists (Y' : C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_comp_monoModSerre_eq_zero_iff P]
    exact ⟨Y', s, hs.1, eq⟩
  · refine ⟨_, cokernel.π f, by rwa [isoModSerre_iff_of_epi], by simp⟩

variable {P} in
/--
lemma `monoModSerre.isoModSerre_factorThruImage` / 引理 `monoModSerre.isoModSerre_factorThruImage`

English:
lemma monoModSerre.isoModSerre_factorThruImage
  proof: by
  rw [isoModSerre_iff_of_epi]
  exact P.prop_of_iso
    (asIso (kernel.map _ f (𝟙 _) (Abelian.image.ι f) (by simp))).symm hf

中文:
引理 monoModSerre.isoModSerre_factorThruImage
  证明: by
  rw [isoModSerre_iff_of_epi]
  exact P.prop_of_iso
    (asIso (kernel.map _ f (𝟙 _) (Abelian.image.ι f) (by simp))).symm hf

Depends on / 依赖: Abelian, Abelian.image, P.prop_of_iso, isoModSerre_iff_of_epi, kernel, kernel.map, prop_of_iso
-/
lemma monoModSerre.isoModSerre_factorThruImage
    {X Y : C} {f : X ⟶ Y} (hf : P.monoModSerre f) :
    P.isoModSerre (Abelian.factorThruImage f) := by
  rw [isoModSerre_iff_of_epi]
  exact P.prop_of_iso
    (asIso (kernel.map _ f (𝟙 _) (Abelian.image.ι f) (by simp))).symm hf

variable {P} in
/--
lemma `epiModSerre.isoModSerre_image_ι` / 引理 `epiModSerre.isoModSerre_image_ι`

English:
lemma epiModSerre.isoModSerre_image_ι
  proof: by
  rw [isoModSerre_iff_of_mono]
  dsimp [epiModSerre] at hf ⊢
  exact P.prop_of_iso
    (asIso (cokernel.map f _ (Abelian.factorThruImage f) (𝟙 Y) (by simp))) hf

中文:
引理 epiModSerre.isoModSerre_image_ι
  证明: by
  rw [isoModSerre_iff_of_mono]
  dsimp [epiModSerre] at hf ⊢
  exact P.prop_of_iso
    (asIso (cokernel.map f _ (Abelian.factorThruImage f) (𝟙 Y) (by simp))) hf

Depends on / 依赖: Abelian, Abelian.factorThruImage, P.prop_of_iso, cokernel, cokernel.map, epiModSerre, factorThruImage, isoModSerre_iff_of_mono, prop_of_iso
-/
lemma epiModSerre.isoModSerre_image_ι
    {X Y : C} {f : X ⟶ Y} (hf : P.epiModSerre f) :
    P.isoModSerre (Abelian.image.ι f) := by
  rw [isoModSerre_iff_of_mono]
  dsimp [epiModSerre] at hf ⊢
  exact P.prop_of_iso
    (asIso (cokernel.map f _ (Abelian.factorThruImage f) (𝟙 Y) (by simp))) hf

namespace SerreClassLocalization

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.HasLeftCalculusOfFractions
  body: ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)

中文:
实例 :
  签名: P.isoModSerre.有LeftCalculusOfFractions
  定义体: ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)

Depends on / 依赖: MorphismProperty, MorphismProperty.pushout_inl, Preadditive, Preadditive.sub_comp, cokernel, cokernel.condition, condition, exists_isoModSerre_comp_eq_zero_iff, isoModSerre_iff_of_epi, pushout, pushout.condition, pushout.inl, pushout.inr, pushout_inl, sub_comp, sub_eq_zero
-/
instance : P.isoModSerre.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ :=
    ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.HasRightCalculusOfFractions
  body: ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)

noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance
noncomputable example : P.isoModSerre.Q.Additive := inferInstance

中文:
实例 :
  签名: P.isoModSerre.有RightCalculusOfFractions
  定义体: ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)

noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance
noncomputable example : P.isoModSerre.Q.Additive := inferInstance

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, MorphismProperty, MorphismProperty.pullback_fst, P.prop_of_iso, Preadditive, Preadditive.comp_sub, coimageIsoImage, comp_sub, condition, exists_comp_isoModSerre_eq_zero_iff, isoModSerre_iff_of_mono, kernel, kernel.condition, prop_of_iso, pullback, pullback.condition, pullback.fst, pullback.snd, pullback_fst
-/
instance : P.isoModSerre.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ :=
    ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)

noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance
noncomputable example : P.isoModSerre.Q.Additive := inferInstance

variable [L.IsLocalization P.isoModSerre] [Preadditive D] [L.Additive]

include L P

/--
lemma `isZero_obj_iff` / 引理 `isZero_obj_iff`

English:
lemma isZero_obj_iff
  given: (X : C)
  proof: by
  simp only [IsZero.iff_id_eq_zero, ← L.map_id, ← L.map_zero,
    MorphismProperty.map_eq_iff_precomp L P.isoModSerre,
    Category.comp_id, comp_zero, exists_prop, exists_eq_right]
  refine ⟨?_, fun _ => ⟨X, by simpa⟩⟩
  rintro ⟨Y, h⟩
  simpa using h.2

中文:
引理 isZero_obj_iff
  条件: (X : C)
  证明: by
  simp only [IsZero.iff_id_eq_zero, ← L.map_id, ← L.map_zero,
    MorphismProperty.map_eq_iff_precomp L P.isoModSerre,
    Category.comp_id, comp_zero, exists_prop, exists_eq_right]
  refine ⟨?_, fun _ => ⟨X, by simpa⟩⟩
  rintro ⟨Y, h⟩
  simpa using h.2

Depends on / 依赖: Category, Category.comp_id, IsZero, IsZero.iff_id_eq_zero, L.map_id, L.map_zero, MorphismProperty, MorphismProperty.map_eq_iff_precomp, P.isoModSerre, comp_id, comp_zero, exists_eq_right, exists_prop, iff_id_eq_zero, isoModSerre, map_eq_iff_precomp, map_id, map_zero
-/
lemma isZero_obj_iff (X : C) :
    IsZero (L.obj X) ↔ P X := by
  simp only [IsZero.iff_id_eq_zero, ← L.map_id, ← L.map_zero,
    MorphismProperty.map_eq_iff_precomp L P.isoModSerre,
    Category.comp_id, comp_zero, exists_prop, exists_eq_right]
  refine ⟨?_, fun _ => ⟨X, by simpa⟩⟩
  rintro ⟨Y, h⟩
  simpa using h.2

/--
lemma `map_eq_zero_iff` / 引理 `map_eq_zero_iff`

English:
lemma map_eq_zero_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← L.map_zero]; rw [MorphismProperty.map_eq_iff_precomp L P.isoModSerre]
  simp [← exists_isoModSerre_comp_eq_zero_iff P]

中文:
引理 map_eq_zero_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← L.map_zero]; rw [MorphismProperty.map_eq_iff_precomp L P.isoModSerre]
  simp [← exists_isoModSerre_comp_eq_zero_iff P]

Depends on / 依赖: L.map_zero, MorphismProperty, MorphismProperty.map_eq_iff_precomp, P.isoModSerre, exists_isoModSerre_comp_eq_zero_iff, isoModSerre, map_eq_iff_precomp, map_zero
-/
lemma map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    L.map f = 0 ↔ P (Abelian.image f) := by
  rw [← L.map_zero]; rw [MorphismProperty.map_eq_iff_precomp L P.isoModSerre]
  simp [← exists_isoModSerre_comp_eq_zero_iff P]

/--
lemma `map_comp_eq_zero_iff_of_epi_mono` / 引理 `map_comp_eq_zero_iff_of_epi_mono`

English:
lemma map_comp_eq_zero_iff_of_epi_mono
  statement: {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
  proof: by
  rw [← L.map_comp]; rw [map_eq_zero_iff L P]
  have := strongEpi_of_epi f
  exact P.prop_iff_of_iso (Abelian.imageIsoImage _ ≪≫ (image.isoStrongEpiMono f g rfl).symm)

中文:
引理 map_comp_eq_zero_iff_of_epi_mono
  结论: {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
  证明: by
  rw [← L.map_comp]; rw [map_eq_zero_iff L P]
  have := strongEpi_of_epi f
  exact P.prop_iff_of_iso (Abelian.imageIsoImage _ ≪≫ (image.isoStrongEpiMono f g rfl).symm)

Depends on / 依赖: Abelian, Abelian.imageIsoImage, L.map_comp, P.prop_iff_of_iso, image.isoStrongEpiMono, imageIsoImage, isoStrongEpiMono, map_comp, map_eq_zero_iff, prop_iff_of_iso, strongEpi_of_epi
-/
lemma map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
    [Epi f] [Mono g] :
    L.map f ≫ L.map g = 0 ↔ P Z := by
  rw [← L.map_comp]; rw [map_eq_zero_iff L P]
  have := strongEpi_of_epi f
  exact P.prop_iff_of_iso (Abelian.imageIsoImage _ ≪≫ (image.isoStrongEpiMono f g rfl).symm)

/--
lemma `mono_map_tfae` / 引理 `mono_map_tfae`

English:
lemma mono_map_tfae
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (kernel.ι f) = 0 := by
      rw [← cancel_mono (L.map f)]; rw [zero_comp]; rw [← L.map_comp]; rw [kernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (𝟙 _) (kernel.ι f)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_comp_monoModSerre_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    exact ⟨W, f ≫ s, MorphismProperty.comp_mem _ _ _ hf hs, by simpa using! eq⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.mono_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ z)
    rw [← cancel_epi (L.objObjPreimageIso W).hom]; rw [comp_zero]; rw [hφ]; rw [← cancel_epi (L.map φ.s)]; rw [comp_zero]; rw [MorphismProperty.RightFraction.map_s_comp_map]
    apply hf φ.f
    have : L.map φ.s ≫ (L.objObjPreimageIso W).hom ≫ z = L.map φ.f := by cat_disch
    rw [← this]; rw [Category.assoc]; rw [Category.assoc]; rw [hz]; rw [comp_zero]; rw [comp_zero]
  tfae_finish

中文:
引理 mono_map_tfae
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (kernel.ι f) = 0 := by
      rw [← cancel_mono (L.map f)]; rw [zero_comp]; rw [← L.map_comp]; rw [kernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (𝟙 _) (kernel.ι f)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_comp_monoModSerre_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    exact ⟨W, f ≫ s, MorphismProperty.comp_mem _ _ _ hf hs, by simpa using! eq⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.mono_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ z)
    rw [← cancel_epi (L.objObjPreimageIso W).hom]; rw [comp_zero]; rw [hφ]; rw [← cancel_epi (L.map φ.s)]; rw [comp_zero]; rw [MorphismProperty.RightFraction.map_s_comp_map]
    apply hf φ.f
    have : L.map φ.s ≫ (L.objObjPreimageIso W).hom ≫ z = L.map φ.f := by cat_disch
    rw [← this]; rw [Category.assoc]; rw [Category.assoc]; rw [hz]; rw [comp_zero]; rw [comp_zero]
  tfae_finish

Depends on / 依赖: L.map, L.map_comp, L.map_zero, Localization, Localization.essSurj, Morphism, P.isoModSerre, cancel_mono, condition, essSurj, exists_comp_monoModSerre_eq_zero_iff, isoModSerre, kernel, kernel.condition, map_comp, map_comp_eq_zero_iff_of_epi_mono, map_eq_zero_iff, map_zero, tfae_have, zero_comp
-/
lemma mono_map_tfae {X Y : C} (f : X ⟶ Y) :
    List.TFAE [Mono (L.map f),
      P.monoModSerre f,
      forall ⦃Z : C⦄ (z : Z ⟶ X), L.map z ≫ L.map f = 0 -> L.map z = 0] := by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (kernel.ι f) = 0 := by
      rw [← cancel_mono (L.map f)]; rw [zero_comp]; rw [← L.map_comp]; rw [kernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (𝟙 _) (kernel.ι f)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_comp_monoModSerre_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    exact ⟨W, f ≫ s, MorphismProperty.comp_mem _ _ _ hf hs, by simpa using! eq⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.mono_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ z)
    rw [← cancel_epi (L.objObjPreimageIso W).hom]; rw [comp_zero]; rw [hφ]; rw [← cancel_epi (L.map φ.s)]; rw [comp_zero]; rw [MorphismProperty.RightFraction.map_s_comp_map]
    apply hf φ.f
    have : L.map φ.s ≫ (L.objObjPreimageIso W).hom ≫ z = L.map φ.f := by cat_disch
    rw [← this]; rw [Category.assoc]; rw [Category.assoc]; rw [hz]; rw [comp_zero]; rw [comp_zero]
  tfae_finish

/--
lemma `mono_map_iff` / 引理 `mono_map_iff`

English:
lemma mono_map_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: (mono_map_tfae L P f).out 0 1

中文:
引理 mono_map_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (mono_map_tfae L P f).out 0 1

Depends on / 依赖: mono_map_tfae
-/
lemma mono_map_iff {X Y : C} (f : X ⟶ Y) :
    Mono (L.map f) ↔ P.monoModSerre f :=
  (mono_map_tfae L P f).out 0 1

/--
lemma `epi_map_tfae` / 引理 `epi_map_tfae`

English:
lemma epi_map_tfae
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (cokernel.π f) = 0 := by
      rw [← cancel_epi (L.map f)]; rw [comp_zero]; rw [← L.map_comp]; rw [cokernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (cokernel.π f) (𝟙 _)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_epiModSerre_comp_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    refine ⟨_, s ≫ f, MorphismProperty.comp_mem _ _ _ hs hf, by simpa⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.epi_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (z ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.objObjPreimageIso W).inv]; rw [zero_comp]; rw [hφ]; rw [← cancel_mono (L.map φ.s)]; rw [zero_comp]; rw [MorphismProperty.LeftFraction.map_comp_map_s]
    apply hf φ.f
    have : L.map φ.f = z ≫ (L.objObjPreimageIso W).inv ≫ L.map φ.s := by
      simp [reassoc_of% hφ]
    rw [this]; rw [reassoc_of% hz]; rw [zero_comp]
  tfae_finish

中文:
引理 epi_map_tfae
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (cokernel.π f) = 0 := by
      rw [← cancel_epi (L.map f)]; rw [comp_zero]; rw [← L.map_comp]; rw [cokernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (cokernel.π f) (𝟙 _)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_epiModSerre_comp_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    refine ⟨_, s ≫ f, MorphismProperty.comp_mem _ _ _ hs hf, by simpa⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.epi_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (z ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.objObjPreimageIso W).inv]; rw [zero_comp]; rw [hφ]; rw [← cancel_mono (L.map φ.s)]; rw [zero_comp]; rw [MorphismProperty.LeftFraction.map_comp_map_s]
    apply hf φ.f
    have : L.map φ.f = z ≫ (L.objObjPreimageIso W).inv ≫ L.map φ.s := by
      simp [reassoc_of% hφ]
    rw [this]; rw [reassoc_of% hz]; rw [zero_comp]
  tfae_finish

Depends on / 依赖: L.map, L.map_comp, L.map_zero, Localization, Localization.essSurj, P.isoModSerre, cancel_epi, cokernel, cokernel.condition, comp_zero, condition, essSurj, exists_epiModSerre_comp_eq_zero_iff, isoModSerre, map_comp, map_comp_eq_zero_iff_of_epi_mono, map_eq_zero_iff, map_zero, tfae_have
-/
lemma epi_map_tfae {X Y : C} (f : X ⟶ Y) :
    List.TFAE [Epi (L.map f),
      P.epiModSerre f,
      forall ⦃Z : C⦄ (z : Y ⟶ Z), L.map f ≫ L.map z = 0 -> L.map z = 0] := by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 -> 2 := fun _ => by
    have hf : L.map (cokernel.π f) = 0 := by
      rw [← cancel_epi (L.map f)]; rw [comp_zero]; rw [← L.map_comp]; rw [cokernel.condition]; rw [L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (cokernel.π f) (𝟙 _)
  tfae_have 2 -> 3 := fun hf => by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P]; rw [← exists_epiModSerre_comp_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    refine ⟨_, s ≫ f, MorphismProperty.comp_mem _ _ _ hs hf, by simpa⟩
  tfae_have 3 -> 1 := fun hf => by
    rw [Preadditive.epi_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (z ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.objObjPreimageIso W).inv]; rw [zero_comp]; rw [hφ]; rw [← cancel_mono (L.map φ.s)]; rw [zero_comp]; rw [MorphismProperty.LeftFraction.map_comp_map_s]
    apply hf φ.f
    have : L.map φ.f = z ≫ (L.objObjPreimageIso W).inv ≫ L.map φ.s := by
      simp [reassoc_of% hφ]
    rw [this]; rw [reassoc_of% hz]; rw [zero_comp]
  tfae_finish

/--
lemma `epi_map_iff` / 引理 `epi_map_iff`

English:
lemma epi_map_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: (epi_map_tfae L P f).out 0 1

中文:
引理 epi_map_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (epi_map_tfae L P f).out 0 1

Depends on / 依赖: epi_map_tfae
-/
lemma epi_map_iff {X Y : C} (f : X ⟶ Y) :
    Epi (L.map f) ↔ P.epiModSerre f :=
  (epi_map_tfae L P f).out 0 1

/--
lemma `inverseImage_monomorphisms` / 引理 `inverseImage_monomorphisms`

English:
lemma inverseImage_monomorphisms
  proof: by
  ext
  simp [mono_map_iff L P]

中文:
引理 inverseImage_monomorphisms
  证明: by
  ext
  simp [mono_map_iff L P]

Depends on / 依赖: mono_map_iff
-/
lemma inverseImage_monomorphisms :
    (MorphismProperty.monomorphisms _).inverseImage L = P.monoModSerre := by
  ext
  simp [mono_map_iff L P]

/--
lemma `inverseImage_epimorphisms` / 引理 `inverseImage_epimorphisms`

English:
lemma inverseImage_epimorphisms
  proof: by
  ext
  simp [epi_map_iff L P]

中文:
引理 inverseImage_epimorphisms
  证明: by
  ext
  simp [epi_map_iff L P]

Depends on / 依赖: epi_map_iff
-/
lemma inverseImage_epimorphisms :
    (MorphismProperty.epimorphisms _).inverseImage L = P.epiModSerre := by
  ext
  simp [epi_map_iff L P]

/--
lemma `preservesMonomorphisms` / 引理 `preservesMonomorphisms`

English:
lemma preservesMonomorphisms
  statement: L.PreservesMonomorphisms where
  proof: by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f

中文:
引理 preservesMonomorphisms
  结论: L.保持Monomorphisms where
  证明: by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f

Depends on / 依赖: P.monoModSerre_of_mono, monoModSerre_of_mono, mono_map_iff
-/
lemma preservesMonomorphisms : L.PreservesMonomorphisms where
  preserves f _ := by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f

/--
lemma `preservesEpimorphisms` / 引理 `preservesEpimorphisms`

English:
lemma preservesEpimorphisms
  statement: L.PreservesEpimorphisms where
  proof: by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

中文:
引理 preservesEpimorphisms
  结论: L.保持Epimorphisms where
  证明: by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

Depends on / 依赖: P.epiModSerre_of_epi, epiModSerre_of_epi, epi_map_iff
-/
lemma preservesEpimorphisms : L.PreservesEpimorphisms where
  preserves f _ := by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_iff` / 引理 `mono_iff`

English:
lemma mono_iff
  given: {X Y : D} (f : X ⟶ Y)
  proof: by
  have := preservesMonomorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Mono (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.monomorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [mono_map_iff L P] at hf
    refine ⟨_, _, Abelian.image.ι f, inferInstance, ⟨Iso.symm ?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_factorThruImage
    exact Arrow.isoMk (asIso (L.map (Abelian.factorThruImage f))) (Iso.refl _)
      (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Mono (L.map f')))

中文:
引理 mono_iff
  条件: {X Y : D} (f : X ⟶ Y)
  证明: by
  have := preservesMonomorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Mono (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.monomorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [mono_map_iff L P] at hf
    refine ⟨_, _, Abelian.image.ι f, inferInstance, ⟨Iso.symm ?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_factorThruImage
    exact Arrow.isoMk (asIso (L.map (Abelian.factorThruImage f))) (Iso.refl _)
      (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Mono (L.map f')))

Depends on / 依赖: Arrow.mk, L.map, L.mapArrow.objObjPreimageIso, Localization, Localization.essSurj_mapArrow, MorphismProperty, MorphismProperty.monomorphisms, Nonempty, P.isoModSerre, arrow_iso_iff, essSurj_mapArrow, infer_property, isoModSerre, mapArrow, monomorphisms, objObjPreimageIso, preservesMonomorphisms
-/
lemma mono_iff {X Y : D} (f : X ⟶ Y) :
    Mono f ↔ exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Mono (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.monomorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [mono_map_iff L P] at hf
    refine ⟨_, _, Abelian.image.ι f, inferInstance, ⟨Iso.symm ?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_factorThruImage
    exact Arrow.isoMk (asIso (L.map (Abelian.factorThruImage f))) (Iso.refl _)
      (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Mono (L.map f')))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_iff` / 引理 `epi_iff`

English:
lemma epi_iff
  given: {X Y : D} (f : X ⟶ Y)
  proof: by
  have := preservesEpimorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Epi (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.epimorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [epi_map_iff L P] at hf
    refine ⟨_, _, Abelian.factorThruImage f, inferInstance, ⟨?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_image_ι
    refine Arrow.isoMk (Iso.refl _) (asIso (L.map (Abelian.image.ι f))) (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Epi (L.map f')))

中文:
引理 epi_iff
  条件: {X Y : D} (f : X ⟶ Y)
  证明: by
  have := preservesEpimorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Epi (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.epimorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [epi_map_iff L P] at hf
    refine ⟨_, _, Abelian.factorThruImage f, inferInstance, ⟨?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_image_ι
    refine Arrow.isoMk (Iso.refl _) (asIso (L.map (Abelian.image.ι f))) (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Epi (L.map f')))

Depends on / 依赖: Arrow.mk, L.map, L.mapArrow.objObjPreimageIso, Localization, Localization.essSurj_mapArrow, MorphismProperty, MorphismProperty.epimorphisms, Nonempty, P.isoModSerre, arrow_iso_iff, epimorphisms, essSurj_mapArrow, infer_property, isoModSerre, mapArrow, objObjPreimageIso, preservesEpimorphisms
-/
lemma epi_iff {X Y : D} (f : X ⟶ Y) :
    Epi f ↔ exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ => ?_, ?_⟩
  · suffices forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Epi (L.map f)),
      exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.epimorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [epi_map_iff L P] at hf
    refine ⟨_, _, Abelian.factorThruImage f, inferInstance, ⟨?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_image_ι
    refine Arrow.isoMk (Iso.refl _) (asIso (L.map (Abelian.image.ι f))) (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Epi (L.map f')))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesKernel` / 引理 `preservesKernel`

English:
lemma preservesKernel
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have := preservesMonomorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : W ⟶ L.obj X) (hz : z ≫ L.map f = 0),
      exists (l : W ⟶ L.obj (kernel f)), l ≫ L.map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ L).2
        (Fork.IsLimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : W = L.obj Z) (z : Z ⟶ X), w = eqToHom hZ ≫ L.map z
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ w)
    rw [← cancel_epi (L.map φ.s)]; rw [MorphismProperty.RightFraction.map_s_comp_map] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by
      rw [← hφ]; rw [Category.assoc]; rw [Category.assoc]; rw [hw]; rw [comp_zero]; rw [comp_zero]) ⟨_, rfl, by simp⟩
    exact ⟨(L.objObjPreimageIso W).inv ≫ inv (L.map φ.s) ≫ l, by simp [hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.id_comp, ← L.map_comp, map_eq_zero_iff L P,
    ← exists_isoModSerre_comp_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  have := Localization.inverts L P.isoModSerre t ht
  rw [← Category.assoc] at fac
  exact ⟨inv (L.map t) ≫ L.map (kernel.lift _ _ fac), by simp [← Functor.map_comp]⟩

中文:
引理 preservesKernel
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have := preservesMonomorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : W ⟶ L.obj X) (hz : z ≫ L.map f = 0),
      exists (l : W ⟶ L.obj (kernel f)), l ≫ L.map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ L).2
        (Fork.IsLimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : W = L.obj Z) (z : Z ⟶ X), w = eqToHom hZ ≫ L.map z
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ w)
    rw [← cancel_epi (L.map φ.s)]; rw [MorphismProperty.RightFraction.map_s_comp_map] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by
      rw [← hφ]; rw [Category.assoc]; rw [Category.assoc]; rw [hw]; rw [comp_zero]; rw [comp_zero]) ⟨_, rfl, by simp⟩
    exact ⟨(L.objObjPreimageIso W).inv ≫ inv (L.map φ.s) ≫ l, by simp [hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.id_comp, ← L.map_comp, map_eq_zero_iff L P,
    ← exists_isoModSerre_comp_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  have := Localization.inverts L P.isoModSerre t ht
  rw [← Category.assoc] at fac
  exact ⟨inv (L.map t) ≫ L.map (kernel.lift _ _ fac), by simp [← Functor.map_comp]⟩

Depends on / 依赖: Fork.IsLimit.ofExistsUnique, IsLimit, KernelFork, KernelFork.condition, KernelFork.isLimitMapConeEquiv, L.map, L.obj, Localization, Localization.essSurj, P.isoModSerre, cancel_mono, condition, essSurj, existsUnique_of_exists_of_unique, isLimitMapConeEquiv, isoModSerre, kernel, kernelIsKernel, ofExistsUnique, preservesLimit_of_preserves_limit_cone
-/
lemma preservesKernel {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) L := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : W ⟶ L.obj X) (hz : z ≫ L.map f = 0),
      exists (l : W ⟶ L.obj (kernel f)), l ≫ L.map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ L).2
        (Fork.IsLimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : W = L.obj Z) (z : Z ⟶ X), w = eqToHom hZ ≫ L.map z
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ w)
    rw [← cancel_epi (L.map φ.s)]; rw [MorphismProperty.RightFraction.map_s_comp_map] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by
      rw [← hφ]; rw [Category.assoc]; rw [Category.assoc]; rw [hw]; rw [comp_zero]; rw [comp_zero]) ⟨_, rfl, by simp⟩
    exact ⟨(L.objObjPreimageIso W).inv ≫ inv (L.map φ.s) ≫ l, by simp [hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.id_comp, ← L.map_comp, map_eq_zero_iff L P,
    ← exists_isoModSerre_comp_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  have := Localization.inverts L P.isoModSerre t ht
  rw [← Category.assoc] at fac
  exact ⟨inv (L.map t) ≫ L.map (kernel.lift _ _ fac), by simp [← Functor.map_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesCokernel` / 引理 `preservesCokernel`

English:
lemma preservesCokernel
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have := preservesEpimorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : L.obj Y ⟶ W) (hz : L.map f ≫ z = 0),
      exists (l : L.obj (cokernel f) ⟶ W), L.map (cokernel.π f) ≫ l = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : L.obj Z = W) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (w ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.map φ.s)]; rw [Category.assoc]; rw [MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso W).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp,
    map_eq_zero_iff L P, ← exists_comp_isoModSerre_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  rw [Category.assoc] at fac
  have := Localization.inverts L P.isoModSerre t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

中文:
引理 preservesCokernel
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have := preservesEpimorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : L.obj Y ⟶ W) (hz : L.map f ≫ z = 0),
      exists (l : L.obj (cokernel f) ⟶ W), L.map (cokernel.π f) ≫ l = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : L.obj Z = W) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (w ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.map φ.s)]; rw [Category.assoc]; rw [MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso W).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp,
    map_eq_zero_iff L P, ← exists_comp_isoModSerre_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  rw [Category.assoc] at fac
  have := Localization.inverts L P.isoModSerre t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.ofExistsUnique, CokernelCofork, CokernelCofork.condition, CokernelCofork.isColimitMapCoconeEquiv, IsColimit, L.map, L.obj, Localization, Localization.essSurj, P.isoModSerre, cancel_epi, cokernel, cokernelIsCokernel, condition, essSurj, existsUnique_of_exists_of_unique, isColimitMapCoconeEquiv, isoModSerre, ofExistsUnique
-/
lemma preservesCokernel {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices forall (W : D) (z : L.obj Y ⟶ W) (hz : L.map f ≫ z = 0),
      exists (l : L.obj (cokernel f) ⟶ W), L.map (cokernel.π f) ≫ l = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s => existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ => by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : exists (Z : C) (hZ : L.obj Z = W) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (w ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.map φ.s)]; rw [Category.assoc]; rw [MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso W).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp,
    map_eq_zero_iff L P, ← exists_comp_isoModSerre_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  rw [Category.assoc] at fac
  have := Localization.inverts L P.isoModSerre t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasKernels` / 引理 `hasKernels`

English:
lemma hasKernels
  statement: HasKernels D where
  proof: by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e))

中文:
引理 hasKernels
  结论: 有Kernels D where
  证明: by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e))

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.mk, Arrow.rightFunc.mapIso, HasLimit, KernelFork, KernelFork.isLimitMapConeEquiv, L.map, Localization, Localization.essSurj_mapArrow, P.isoModSerre, essSurj_mapArrow, g.hom, hasLimit_of_iso, isLimitMapConeEquiv, isLimitOfPreserves, isoModSerre, kernelIsKernel, leftFunc, mapIso, mem_essImage
-/
lemma hasKernels : HasKernels D where
  has_limit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasCokernels` / 引理 `hasCokernels`

English:
lemma hasCokernels
  statement: HasCokernels D where
  proof: by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm))

中文:
引理 hasCokernels
  结论: 有余kernels D where
  证明: by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm))

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.mk, Arrow.rightFunc.mapIso, CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, HasColimit, L.map, Localization, Localization.essSurj_mapArrow, P.isoModSerre, cokernelIsCokernel, e.symm, essSurj_mapArrow, g.hom, hasColimit_of_iso, isColimitMapCoconeEquiv, isColimitOfPreserves, isoModSerre, leftFunc, mapIso
-/
lemma hasCokernels : HasCokernels D where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm))

/--
lemma `hasEqualizers` / 引理 `hasEqualizers`

English:
lemma hasEqualizers
  statement: HasEqualizers D
  proof: have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _

中文:
引理 hasEqualizers
  结论: HasEqualizers D
  证明: have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _

Depends on / 依赖: HasEqualizer, Preadditive, Preadditive.hasEqualizer_of_hasKernel, hasEqualizer_of_hasKernel, hasEqualizers_of_hasLimit_parallelPair, hasKernels
-/
lemma hasEqualizers : HasEqualizers D :=
  have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _

/--
lemma `hasCoequalizers` / 引理 `hasCoequalizers`

English:
lemma hasCoequalizers
  statement: HasCoequalizers D
  proof: have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g :=
    Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _

中文:
引理 hasCoequalizers
  结论: HasCoequalizers D
  证明: have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g :=
    Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _

Depends on / 依赖: HasCoequalizer, Preadditive, Preadditive.hasCoequalizer_of_hasCokernel, hasCoequalizer_of_hasCokernel, hasCoequalizers_of_hasColimit_parallelPair, hasCokernels
-/
lemma hasCoequalizers : HasCoequalizers D :=
  have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g :=
    Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _

/--
lemma `hasFiniteProducts` / 引理 `hasFiniteProducts`

English:
lemma hasFiniteProducts
  statement: HasFiniteProducts D
  proof: have := Localization.essSurj L P.isoModSerre
  L.hasFiniteProducts_of_additive_of_essSurj

中文:
引理 hasFiniteProducts
  结论: 有FiniteProducts D
  证明: have := Localization.essSurj L P.isoModSerre
  L.hasFiniteProducts_of_additive_of_essSurj

Depends on / 依赖: L.hasFiniteProducts_of_additive_of_essSurj, Localization, Localization.essSurj, P.isoModSerre, essSurj, hasFiniteProducts_of_additive_of_essSurj, isoModSerre
-/
lemma hasFiniteProducts : HasFiniteProducts D :=
  have := Localization.essSurj L P.isoModSerre
  L.hasFiniteProducts_of_additive_of_essSurj

/--
lemma `isNormalMonoCategory` / 引理 `isNormalMonoCategory`

English:
lemma isNormalMonoCategory
  statement: IsNormalMonoCategory D where
  proof: by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    have := preservesKernel L P hf'.g
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }

中文:
引理 isNormalMonoCategory
  结论: 是正规单态射范畴 D where
  证明: by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    have := preservesKernel L P hf'.g
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }

Depends on / 依赖: KernelFork, KernelFork.isLimitMapConeEquiv, L.map, L.map_comp, L.obj, NormalMono, NormalMono.ofArrowIso, isLimit, isLimitMapConeEquiv, isLimitOfPreserves, map_comp, mono_iff, normalMonoOfMono, ofArrowIso, preservesKernel
-/
lemma isNormalMonoCategory : IsNormalMonoCategory D where
  normalMonoOfMono f hf := by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    have := preservesKernel L P hf'.g
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }

/--
lemma `isNormalEpiCategory` / 引理 `isNormalEpiCategory`

English:
lemma isNormalEpiCategory
  statement: IsNormalEpiCategory D where
  proof: by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    have := preservesCokernel L P hf'.g
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

中文:
引理 isNormalEpiCategory
  结论: 是正规满态射范畴 D where
  证明: by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    have := preservesCokernel L P hf'.g
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

Depends on / 依赖: CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, L.map, L.map_comp, L.obj, NormalEpi, NormalEpi.ofArrowIso, epi_iff, isColimit, isColimitMapCoconeEquiv, isColimitOfPreserves, map_comp, normalEpiOfEpi, ofArrowIso, preservesCokernel
-/
lemma isNormalEpiCategory : IsNormalEpiCategory D where
  normalEpiOfEpi f hf := by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    have := preservesCokernel L P hf'.g
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

/-- If `L : C ⥤ D` is a localization functor with respect to a Serre class `P` in
the abelian category `C`, then `D` is an abelian category.
Note that we assume that `D` has already been equipped with a preadditive structure,
and that `L` is additive. Otherwise, see the results in the file
`Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`
which applies because `P.isoModSerre` has a calculus of left and right fractions. -/
@[stacks 02MS, instance_reducible]
/--
Definition of `abelian` / `abelian` 的定义

English:
definition abelian
  signature: : Abelian D
  body: by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor

中文:
定义 abelian
  签名: : 交换 D
  定义体: by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor

Depends on / 依赖: hasCokernels, hasFiniteProducts, hasKernels, isNormalEpiCategory, isNormalMonoCategory
-/
def abelian : Abelian D := by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor

/--
lemma `hasZeroObject` / 引理 `hasZeroObject`

English:
lemma hasZeroObject
  statement: HasZeroObject D
  proof: have := abelian L P
  Abelian.hasZeroObject

中文:
引理 hasZeroObject
  结论: 有ZeroObject D
  证明: have := abelian L P
  Abelian.hasZeroObject

Depends on / 依赖: Abelian, Abelian.hasZeroObject, abelian, hasZeroObject
-/
lemma hasZeroObject : HasZeroObject D :=
  have := abelian L P
  Abelian.hasZeroObject

/--
lemma `preservesFiniteLimits` / 引理 `preservesFiniteLimits`

English:
lemma preservesFiniteLimits
  statement: PreservesFiniteLimits L
  proof: by
  let := abelian L P
  rw [((Functor.preservesFiniteLimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesKernel L P f

中文:
引理 preservesFiniteLimits
  结论: 保持FiniteLimits L
  证明: by
  let := abelian L P
  rw [((Functor.preservesFiniteLimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesKernel L P f

Depends on / 依赖: Functor, Functor.preservesFiniteLimits_tfae, abelian, preservesFiniteLimits_tfae, preservesKernel
-/
lemma preservesFiniteLimits : PreservesFiniteLimits L := by
  let := abelian L P
  rw [((Functor.preservesFiniteLimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesKernel L P f

/--
lemma `preservesFiniteColimits` / 引理 `preservesFiniteColimits`

English:
lemma preservesFiniteColimits
  statement: PreservesFiniteColimits L
  proof: by
  let := abelian L P
  rw [((Functor.preservesFiniteColimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesCokernel L P f

中文:
引理 preservesFiniteColimits
  结论: 保持FiniteColimits L
  证明: by
  let := abelian L P
  rw [((Functor.preservesFiniteColimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesCokernel L P f

Depends on / 依赖: Functor, Functor.preservesFiniteColimits_tfae, abelian, preservesCokernel, preservesFiniteColimits_tfae
-/
lemma preservesFiniteColimits : PreservesFiniteColimits L := by
  let := abelian L P
  rw [((Functor.preservesFiniteColimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesCokernel L P f

/--
lemma `isIso_map_iff` / 引理 `isIso_map_iff`

English:
lemma isIso_map_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  let := abelian L P
  rw [isIso_iff_mono_and_epi]; rw [mono_map_iff L P]; rw [epi_map_iff L P]; rw [isoModSerre_iff]

中文:
引理 isIso_map_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  let := abelian L P
  rw [isIso_iff_mono_and_epi]; rw [mono_map_iff L P]; rw [epi_map_iff L P]; rw [isoModSerre_iff]

Depends on / 依赖: abelian, epi_map_iff, isIso_iff_mono_and_epi, isoModSerre_iff, mono_map_iff
-/
lemma isIso_map_iff {X Y : C} (f : X ⟶ Y) :
    IsIso (L.map f) ↔ P.isoModSerre f := by
  let := abelian L P
  rw [isIso_iff_mono_and_epi]; rw [mono_map_iff L P]; rw [epi_map_iff L P]; rw [isoModSerre_iff]

/--
lemma `inverseImage_isomorphisms` / 引理 `inverseImage_isomorphisms`

English:
lemma inverseImage_isomorphisms
  proof: by
  ext
  simp [isIso_map_iff L P]

中文:
引理 inverseImage_isomorphisms
  证明: by
  ext
  simp [isIso_map_iff L P]

Depends on / 依赖: isIso_map_iff
-/
lemma inverseImage_isomorphisms :
    (MorphismProperty.isomorphisms _).inverseImage L = P.isoModSerre := by
  ext
  simp [isIso_map_iff L P]

variable (G : D ⥤ E)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesFiniteLimits_comp_iff` / 引理 `preservesFiniteLimits_comp_iff`

English:
lemma preservesFiniteLimits_comp_iff
  proof: by
  let := abelian L P
  have := preservesFiniteLimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteLimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr
    (L ⋙ G).additive_of_preserves_binary_products
  refine ((Functor.preservesFiniteLimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesLimit (parallelPair (L.map f'.hom) 0) G :=
    preservesLimit_of_preserves_limit_cone
      (KernelFork.isLimitMapConeEquiv _ _
        (isLimitOfPreserves L (kernelIsKernel f'.hom)))
          ((KernelFork.isLimitMapConeEquiv _ G).symm
            (KernelFork.isLimitMapConeEquiv _ (L ⋙ G)
              (isLimitOfPreserves (L ⋙ G) (kernelIsKernel f'.hom))))
  exact preservesLimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

中文:
引理 preservesFiniteLimits_comp_iff
  证明: by
  let := abelian L P
  have := preservesFiniteLimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteLimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr
    (L ⋙ G).additive_of_preserves_binary_products
  refine ((Functor.preservesFiniteLimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesLimit (parallelPair (L.map f'.hom) 0) G :=
    preservesLimit_of_preserves_limit_cone
      (KernelFork.isLimitMapConeEquiv _ _
        (isLimitOfPreserves L (kernelIsKernel f'.hom)))
          ((KernelFork.isLimitMapConeEquiv _ G).symm
            (KernelFork.isLimitMapConeEquiv _ (L ⋙ G)
              (isLimitOfPreserves (L ⋙ G) (kernelIsKernel f'.hom))))
  exact preservesLimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

Depends on / 依赖: Arrow.mk, Functor, Functor.preservesFiniteLimits_tfae, L.map, Localization, Localization.essSurj_mapArrow, Localization.functor_additive_iff, P.isoModSerre, PreservesLimit, abelian, additive_of_preserves_binary_products, comp_preservesFiniteLimits, essSurj_mapArrow, functor_additive_iff, isoModSerre, mem_essImage, parallelPair, preservesFiniteLimits, preservesFiniteLimits_tfae, preservesLimit_of_preserves_limit_cone
-/
lemma preservesFiniteLimits_comp_iff :
    PreservesFiniteLimits (L ⋙ G) ↔ PreservesFiniteLimits G := by
  let := abelian L P
  have := preservesFiniteLimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteLimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr
    (L ⋙ G).additive_of_preserves_binary_products
  refine ((Functor.preservesFiniteLimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesLimit (parallelPair (L.map f'.hom) 0) G :=
    preservesLimit_of_preserves_limit_cone
      (KernelFork.isLimitMapConeEquiv _ _
        (isLimitOfPreserves L (kernelIsKernel f'.hom)))
          ((KernelFork.isLimitMapConeEquiv _ G).symm
            (KernelFork.isLimitMapConeEquiv _ (L ⋙ G)
              (isLimitOfPreserves (L ⋙ G) (kernelIsKernel f'.hom))))
  exact preservesLimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesFiniteColimits_comp_iff` / 引理 `preservesFiniteColimits_comp_iff`

English:
lemma preservesFiniteColimits_comp_iff
  proof: by
  let := abelian L P
  have := preservesFiniteColimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteColimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr (by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (L ⋙ G)
    exact Functor.additive_of_preservesBinaryBiproducts _)
  refine ((Functor.preservesFiniteColimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesColimit (parallelPair (L.map f'.hom) 0) G :=
    preservesColimit_of_preserves_colimit_cocone
      (CokernelCofork.isColimitMapCoconeEquiv _ _
        (isColimitOfPreserves L (cokernelIsCokernel f'.hom)))
          ((CokernelCofork.isColimitMapCoconeEquiv _ G).symm
            (CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ G)
              (isColimitOfPreserves (L ⋙ G) (cokernelIsCokernel f'.hom))))
  exact preservesColimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

中文:
引理 preservesFiniteColimits_comp_iff
  证明: by
  let := abelian L P
  have := preservesFiniteColimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteColimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr (by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (L ⋙ G)
    exact Functor.additive_of_preservesBinaryBiproducts _)
  refine ((Functor.preservesFiniteColimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesColimit (parallelPair (L.map f'.hom) 0) G :=
    preservesColimit_of_preserves_colimit_cocone
      (CokernelCofork.isColimitMapCoconeEquiv _ _
        (isColimitOfPreserves L (cokernelIsCokernel f'.hom)))
          ((CokernelCofork.isColimitMapCoconeEquiv _ G).symm
            (CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ G)
              (isColimitOfPreserves (L ⋙ G) (cokernelIsCokernel f'.hom))))
  exact preservesColimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

Depends on / 依赖: Arrow.mk, Functor, Functor.additive_of_preservesBinaryBiproducts, Functor.preservesFiniteColimits_tfae, Localization, Localization.essSurj_mapArrow, Localization.functor_additive_iff, P.isoModSerre, abelian, additive_of_preservesBinaryBiproducts, comp_preservesFiniteColimits, essSurj_mapArrow, functor_additive_iff, isoModSerre, mem_essImage, preservesBinaryBiproducts_of_preservesBinaryCoproducts, preservesFiniteColimits, preservesFiniteColimits_tfae
-/
lemma preservesFiniteColimits_comp_iff :
    PreservesFiniteColimits (L ⋙ G) ↔ PreservesFiniteColimits G := by
  let := abelian L P
  have := preservesFiniteColimits L P
  refine ⟨fun _ => ?_, fun _ => comp_preservesFiniteColimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr (by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (L ⋙ G)
    exact Functor.additive_of_preservesBinaryBiproducts _)
  refine ((Functor.preservesFiniteColimits_tfae G).out 2 3).mp (fun _ _ f => ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesColimit (parallelPair (L.map f'.hom) 0) G :=
    preservesColimit_of_preserves_colimit_cocone
      (CokernelCofork.isColimitMapCoconeEquiv _ _
        (isColimitOfPreserves L (cokernelIsCokernel f'.hom)))
          ((CokernelCofork.isColimitMapCoconeEquiv _ G).symm
            (CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ G)
              (isColimitOfPreserves (L ⋙ G) (cokernelIsCokernel f'.hom))))
  exact preservesColimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

/--
lemma `exactFunctor_comp_iff` / 引理 `exactFunctor_comp_iff`

English:
lemma exactFunctor_comp_iff
  proof: by
  simp [preservesFiniteLimits_comp_iff L P, preservesFiniteColimits_comp_iff L P]

中文:
引理 exactFunctor_comp_iff
  证明: by
  simp [preservesFiniteLimits_comp_iff L P, preservesFiniteColimits_comp_iff L P]

Depends on / 依赖: preservesFiniteColimits_comp_iff, preservesFiniteLimits_comp_iff
-/
lemma exactFunctor_comp_iff :
    exactFunctor _ _ (L ⋙ G) ↔ exactFunctor _ _ G := by
  simp [preservesFiniteLimits_comp_iff L P, preservesFiniteColimits_comp_iff L P]

variable (E)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `whiskeringLeft` / `whiskeringLeft` 的定义

English:
definition whiskeringLeft
  signature: : (D ⥤ₑ E) ⥤ C ⥤ₑ E
  body: ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj L) (fun G => by
      dsimp
      simpa only [exactFunctor_comp_iff L P] using G.property)

@[simp]

中文:
定义 whiskeringLeft
  签名: : (D ⥤ₑ E) ⥤ C ⥤ₑ E
  定义体: ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj L) (fun G => by
      dsimp
      simpa only [exactFunctor_comp_iff L P] using G.property)

@[simp]

Depends on / 依赖: Functor, Functor.whiskeringLeft, G.property, ObjectProperty, ObjectProperty.lift, exactFunctor_comp_iff, property, whiskeringLeft
-/
def whiskeringLeft : (D ⥤ₑ E) ⥤ C ⥤ₑ E :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj L) (fun G => by
      dsimp
      simpa only [exactFunctor_comp_iff L P] using G.property)

@[simp]
/--
lemma `whiskeringLeft_obj_obj` / 引理 `whiskeringLeft_obj_obj`

English:
lemma whiskeringLeft_obj_obj
  given: (G : D ⥤ₑ E)
  proof: rfl

中文:
引理 whiskeringLeft_obj_obj
  条件: (G : D ⥤ₑ E)
  证明: rfl
-/
lemma whiskeringLeft_obj_obj (G : D ⥤ₑ E) :
    ((whiskeringLeft L P E).obj G).obj = L ⋙ G.obj := rfl

/--
Definition of `fullyFaithfulWhiskeringLeft` / `fullyFaithfulWhiskeringLeft` 的定义

English:
definition fullyFaithfulWhiskeringLeft
  signature: :
  body: Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((exactFunctor D E).fullyFaithfulι.comp
      (Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre E))

中文:
定义 fullyFaithfulWhiskeringLeft
  签名: :
  定义体: Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((exactFunctor D E).fullyFaithfulι.comp
      (Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre E))

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofCompFaithful, Localization, Localization.fullyFaithfulWhiskeringLeft, ObjectProperty, P.isoModSerre, exactFunctor, fullyFaithfulWhiskeringLeft, isoModSerre, ofCompFaithful
-/
noncomputable def fullyFaithfulWhiskeringLeft :
    (whiskeringLeft L P E).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((exactFunctor D E).fullyFaithfulι.comp
      (Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre E))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (whiskeringLeft L P E).Faithful
  body: (fullyFaithfulWhiskeringLeft L P E).faithful

中文:
实例 :
  签名: (whiskeringLeft L P E).忠实
  定义体: (fullyFaithfulWhiskeringLeft L P E).faithful

Depends on / 依赖: faithful, fullyFaithfulWhiskeringLeft
-/
instance : (whiskeringLeft L P E).Faithful :=
  (fullyFaithfulWhiskeringLeft L P E).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (whiskeringLeft L P E).Full
  body: (fullyFaithfulWhiskeringLeft L P E).full

中文:
实例 :
  签名: (whiskeringLeft L P E).满
  定义体: (fullyFaithfulWhiskeringLeft L P E).full

Depends on / 依赖: fullyFaithfulWhiskeringLeft
-/
instance : (whiskeringLeft L P E).Full :=
  (fullyFaithfulWhiskeringLeft L P E).full

/--
lemma `essImage_whiskeringLeft` / 引理 `essImage_whiskeringLeft`

English:
lemma essImage_whiskeringLeft
  proof: by
  ext F
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _
      (show L ⋙ G.obj ≅ F.obj from (ObjectProperty.ι _).mapIso e)]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  · refine ⟨⟨Localization.lift F.obj hF L, ?_⟩,
      ⟨ObjectProperty.isoMk _ (Localization.fac F.obj hF L)⟩⟩
    rw [← exactFunctor_comp_iff L P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac F.obj hF L).symm F.property

中文:
引理 essImage_whiskeringLeft
  证明: by
  ext F
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _
      (show L ⋙ G.obj ≅ F.obj from (ObjectProperty.ι _).mapIso e)]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  · refine ⟨⟨Localization.lift F.obj hF L, ?_⟩,
      ⟨ObjectProperty.isoMk _ (Localization.fac F.obj hF L)⟩⟩
    rw [← exactFunctor_comp_iff L P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac F.obj hF L).symm F.property

Depends on / 依赖: F.obj, F.property, G.obj, IsInvertedBy, Localization, Localization.fac, Localization.inverts, Localization.lift, MorphismProperty, MorphismProperty.IsInvertedBy.iff_of_iso, MorphismProperty.IsInvertedBy.of_comp, ObjectProperty, ObjectProperty.isoMk, ObjectProperty.prop_of_iso, exactFunctor_comp_iff, iff_of_iso, inverts, mapIso, of_comp, prop_of_iso
-/
lemma essImage_whiskeringLeft :
    (whiskeringLeft L P E).essImage =
      fun G => P.isoModSerre.IsInvertedBy G.obj := by
  ext F
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _
      (show L ⋙ G.obj ≅ F.obj from (ObjectProperty.ι _).mapIso e)]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  · refine ⟨⟨Localization.lift F.obj hF L, ?_⟩,
      ⟨ObjectProperty.isoMk _ (Localization.fac F.obj hF L)⟩⟩
    rw [← exactFunctor_comp_iff L P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac F.obj hF L).symm F.property

end SerreClassLocalization

end ObjectProperty

end CategoryTheory
