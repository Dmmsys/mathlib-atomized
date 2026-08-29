/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of cofibrant objects

Let `C` be a model category. By using the right homotopy relation,
we introduce the homotopy category `CofibrantObject.HoCat C` of cofibrant objects
in `C`, and we define a cofibrant resolution functor
`CofibrantObject.HoCat.resolution : C ⥤ CofibrantObject.HoCat C`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace CofibrantObject

variable (C) in
/--
Definition of `homRel` / `homRel` 的定义

English:
definition homRel
  signature: : HomRel (CofibrantObject C)
  body: fun _ _ f g => RightHomotopyRel f.hom g.hom

中文:
定义 homRel
  签名: : HomRel (CofibrantObject C)
  定义体: fun _ _ f g => RightHomotopyRel f.hom g.hom

Depends on / 依赖: RightHomotopyRel, f.hom, g.hom
-/
def homRel : HomRel (CofibrantObject C) :=
  fun _ _ f g => RightHomotopyRel f.hom g.hom

/--
lemma `homRel_iff_rightHomotopyRel` / 引理 `homRel_iff_rightHomotopyRel`

English:
lemma homRel_iff_rightHomotopyRel
  given: {X Y : CofibrantObject C} {f g : X ⟶ Y}
  proof: Iff.rfl

中文:
引理 homRel_iff_rightHomotopyRel
  条件: {X Y : CofibrantObject C} {f g : X ⟶ Y}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomRel.IsStableUnderPostcomp (homRel C)
  body: h.postcomp _

中文:
实例 :
  签名: HomRel.是StableUnderPostcomp (homRel C)
  定义体: h.postcomp _

Depends on / 依赖: h.postcomp, postcomp
-/
instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomRel.IsStableUnderPrecomp (homRel C)
  body: h.precomp _

中文:
实例 :
  签名: HomRel.是StableUnderPrecomp (homRel C)
  定义体: h.precomp _

Depends on / 依赖: h.precomp, precomp
-/
instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _

/--
lemma `homRel_equivalence_of_isFibrant_tgt` / 引理 `homRel_equivalence_of_isFibrant_tgt`

English:
lemma homRel_equivalence_of_isFibrant_tgt
  given: {X Y : CofibrantObject C} [IsFibrant Y.obj]
  proof: (RightHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)

中文:
引理 homRel_equivalence_of_isFibrant_tgt
  条件: {X Y : CofibrantObject C} [IsFibrant Y.obj]
  证明: (RightHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)
-/
lemma homRel_equivalence_of_isFibrant_tgt {X Y : CofibrantObject C} [IsFibrant Y.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (RightHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)

variable (C) in
/--
Definition of `HoCat` / `HoCat` 的定义

English:
abbreviation HoCat
  body: Quotient (CofibrantObject.homRel C)

中文:
缩写 HoCat
  定义体: Quotient (CofibrantObject.homRel C)

Depends on / 依赖: CofibrantObject, CofibrantObject.homRel, Quotient, homRel
-/
abbrev HoCat := Quotient (CofibrantObject.homRel C)

/-- The quotient functor from the category of cofibrant objects to its
homotopy category. -/
@[implicit_reducible]
/--
Definition of `toHoCat` / `toHoCat` 的定义

English:
definition toHoCat
  signature: : CofibrantObject C ⥤ HoCat C
  body: Quotient.functor _

中文:
定义 toHoCat
  签名: : CofibrantObject C ⥤ HoCat C
  定义体: Quotient.functor _

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def toHoCat : CofibrantObject C ⥤ HoCat C := Quotient.functor _

/--
lemma `toHoCat_obj_surjective` / 引理 `toHoCat_obj_surjective`

English:
lemma toHoCat_obj_surjective
  statement: Function.Surjective (toHoCat (C := C)).obj
  proof: fun ⟨_⟩ => ⟨_, rfl⟩

中文:
引理 toHoCat_obj_surjective
  结论: 函数.满射 (toHoCat (C := C)).obj
  证明: fun ⟨_⟩ => ⟨_, rfl⟩
-/
lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ => ⟨_, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Full (toHoCat (C := C))
  body: by dsimp [toHoCat]; infer_instance

中文:
实例 :
  签名: 函子.满 (toHoCat (C := C))
  定义体: by dsimp [toHoCat]; infer_instance

Depends on / 依赖: infer_instance, toHoCat
-/
instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance

/--
lemma `toHoCat_map_eq` / 引理 `toHoCat_map_eq`

English:
lemma toHoCat_map_eq
  statement: {X Y : CofibrantObject C} {f g : X ⟶ Y}
  proof: CategoryTheory.Quotient.sound _ h

中文:
引理 toHoCat_map_eq
  结论: {X Y : CofibrantObject C} {f g : X ⟶ Y}
  证明: CategoryTheory.Quotient.sound _ h

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient
-/
lemma toHoCat_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

/--
lemma `toHoCat_map_eq_iff` / 引理 `toHoCat_map_eq_iff`

English:
lemma toHoCat_map_eq_iff
  given: {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y)
  proof: by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isFibrant_tgt.eqvGen_eq]

中文:
引理 toHoCat_map_eq_iff
  条件: {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y)
  证明: by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isFibrant_tgt.eqvGen_eq]

Depends on / 依赖: Functor, Functor.homRel_iff, HomRel, HomRel.compClosure_eq_self, Quotient, Quotient.functor_homRel_eq_compClosure_eqvGen, compClosure_eq_self, eqvGen_eq, functor_homRel_eq_compClosure_eqvGen, homRel_equivalence_of_isFibrant_tgt, homRel_equivalence_of_isFibrant_tgt.eqvGen_eq, homRel_iff, toHoCat
-/
lemma toHoCat_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isFibrant_tgt.eqvGen_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C)
  body: by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

中文:
实例 :
  签名: (weakEquivalences (CofibrantObject C)).有商 (homRel C)
  定义体: by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

Depends on / 依赖: h.weakEquivalence_iff, weakEquivalence_iff, weakEquivalence_iff_of_objectProperty
-/
instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithWeakEquivalences (CofibrantObject.HoCat C)
  body: (weakEquivalences _).quotient _

中文:
实例 :
  签名: 带弱等价范畴 (CofibrantObject.HoCat C)
  定义体: (weakEquivalences _).quotient _

Depends on / 依赖: quotient, weakEquivalences
-/
instance : CategoryWithWeakEquivalences (CofibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _

/--
lemma `weakEquivalence_toHoCat_map_iff` / 引理 `weakEquivalence_toHoCat_map_iff`

English:
lemma weakEquivalence_toHoCat_map_iff
  given: {X Y : CofibrantObject C} (f : X ⟶ Y)
  proof: by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

中文:
引理 weakEquivalence_toHoCat_map_iff
  条件: {X Y : CofibrantObject C} (f : X ⟶ Y)
  证明: by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

Depends on / 依赖: MorphismProperty, MorphismProperty.quotient_iff, quotient_iff, weakEquivalence_iff
-/
lemma weakEquivalence_toHoCat_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/--
Definition of `toHoCatLocalizerMorphism` / `toHoCatLocalizerMorphism` 的定义

English:
definition toHoCatLocalizerMorphism
  signature: :
  body: toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

中文:
定义 toHoCatLocalizerMorphism
  签名: :
  定义体: toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

Depends on / 依赖: toHoCat
-/
def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in
/--
lemma `factorsThroughLocalization` / 引理 `factorsThroughLocalization`

English:
lemma factorsThroughLocalization
  proof: by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

中文:
引理 factorsThroughLocalization
  证明: by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

Depends on / 依赖: CofibrantObject, Functor, Functor.map_comp, L.map, Localization, Localization.inverts, areEqualizedByLocalization_iff, cat_disch, exists_very_good_pathObject, h.exists_very_good_pathObject, infer_instance, inverts, map_comp, weakEquivalence_homMk_iff, weakEquivalence_iff, weakEquivalences
-/
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (CofibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toHoCatLocalizerMorphism C).IsLocalizedEquivalence
  body: by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

中文:
实例 :
  签名: (toHoCatLocalizerMorphism C).是LocalizedEquivalence
  定义体: by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

Depends on / 依赖: MorphismProperty, MorphismProperty.eq_inverseImage_quotientFunctor, eq_inverseImage_quotientFunctor, factorsThroughLocalization, isLocalizedEquivalence
-/
instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)

/--
lemma `HoCat.exists_resolution` / 引理 `HoCat.exists_resolution`

English:
lemma HoCat.exists_resolution
  given: (X : C)
  proof: by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

中文:
引理 HoCat.存在_resolution
  条件: (X : C)
  证明: by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, cofibrations, factorizationData, infer_instance, initial, initial.to, initialIsInitial, isCofibrant_iff_of_isInitial, trivialFibrations
-/
lemma HoCat.exists_resolution (X : C) :
    exists (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

/--
Definition of `HoCat.resolutionObj` / `HoCat.resolutionObj` 的定义

English:
definition HoCat.resolutionObj
  signature: (X : C)
  body: (exists_resolution X).choose

中文:
定义 HoCat.resolutionObj
  签名: (X : C)
  定义体: (exists_resolution X).choose

Depends on / 依赖: exists_resolution
-/
noncomputable def HoCat.resolutionObj (X : C) : C :=
  (exists_resolution X).choose

instance (X : C) : IsCofibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/--
Definition of `HoCat.pResolutionObj` / `HoCat.pResolutionObj` 的定义

English:
definition HoCat.pResolutionObj
  signature: (X : C)
  body: (exists_resolution X).choose_spec.choose_spec.choose

中文:
定义 HoCat.pResolutionObj
  签名: (X : C)
  定义体: (exists_resolution X).choose_spec.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose, exists_resolution
-/
noncomputable def HoCat.pResolutionObj (X : C) : resolutionObj X ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Fibration (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2

instance (X : C) [IsFibrant X] : IsFibrant (HoCat.resolutionObj X) :=
  isFibrant_of_fibration (HoCat.pResolutionObj X)

/--
lemma `HoCat.exists_resolution_map` / 引理 `HoCat.exists_resolution_map`

English:
lemma HoCat.exists_resolution_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

中文:
引理 HoCat.存在_resolution_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

Depends on / 依赖: CommSq, fac_right, initial, initial.to, pResolutionObj, sq.fac_right, sq.lift
-/
lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    exists (g : resolutionObj X ⟶ resolutionObj Y),
      g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/--
Definition of `HoCat.resolutionMap` / `HoCat.resolutionMap` 的定义

English:
definition HoCat.resolutionMap
  signature: {X Y : C} (f : X ⟶ Y)
  body: (exists_resolution_map f).choose

@[reassoc (attr := simp)]

中文:
定义 HoCat.resolutionMap
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: (exists_resolution_map f).choose

@[reassoc (attr := simp)]

Depends on / 依赖: exists_resolution_map
-/
noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
/--
lemma `HoCat.resolutionMap_fac` / 引理 `HoCat.resolutionMap_fac`

English:
lemma HoCat.resolutionMap_fac
  given: {X Y : C} (f : X ⟶ Y)
  proof: (exists_resolution_map f).choose_spec

@[simp]

中文:
引理 HoCat.resolutionMap_fac
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (exists_resolution_map f).choose_spec

@[simp]

Depends on / 依赖: choose_spec, exists_resolution_map
-/
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    resolutionMap f ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
/--
lemma `HoCat.weakEquivalence_resolutionMap_iff` / 引理 `HoCat.weakEquivalence_resolutionMap_iff`

English:
lemma HoCat.weakEquivalence_resolutionMap_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_precomp_iff]

中文:
引理 HoCat.weakEquivalence_resolutionMap_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_precomp_iff]

Depends on / 依赖: HoCat.resolutionMap_fac, pResolutionObj, resolutionMap_fac, weakEquivalence_postcomp_iff, weakEquivalence_precomp_iff
-/
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_precomp_iff]

/--
lemma `HoCat.resolutionObj_hom_ext` / 引理 `HoCat.resolutionObj_hom_ext`

English:
lemma HoCat.resolutionObj_hom_ext
  statement: {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
  proof: by
  apply toHoCat_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).injective h

中文:
引理 HoCat.resolutionObj_hom_ext
  结论: {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
  证明: by
  apply toHoCat_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).injective h

Depends on / 依赖: LeftHomotopyClass, LeftHomotopyClass.mk_eq_mk_iff, LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence, LeftHomotopyRel, LeftHomotopyRel.rightHomotopyRel, homRel_iff_rightHomotopyRel, injective, mk_eq_mk_iff, pResolutionObj, postcomp_bijective_of_fibration_of_weakEquivalence, rightHomotopyRel, toHoCat_map_eq
-/
lemma HoCat.resolutionObj_hom_ext {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (f ≫ pResolutionObj Y) (g ≫ pResolutionObj Y)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).injective h

/--
Definition of `HoCat.resolution` / `HoCat.resolution` 的定义

English:
definition HoCat.resolution
  signature: : C ⥤ CofibrantObject.HoCat C where
  body: toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

中文:
定义 HoCat.resolution
  签名: : C ⥤ CofibrantObject.HoCat C where
  定义体: toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

Depends on / 依赖: resolutionObj, toHoCat, toHoCat.obj
-/
noncomputable def HoCat.resolution : C ⥤ CofibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The cofibrant resolution functor `HoCat.resolution`, as a localizer morphism. -/
@[simps]
/--
Definition of `HoCat.localizerMorphismResolution` / `HoCat.localizerMorphismResolution` 的定义

English:
definition HoCat.localizerMorphismResolution
  signature: :
  body: HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

中文:
定义 HoCat.localizerMorphismResolution
  签名: :
  定义体: HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

Depends on / 依赖: HoCat.resolution, resolution
-/
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.pResolutionObj`, when applied to already cofibrant objects, gives
a natural transformation `ι ⋙ HoCat.resolution ⟶ toHoCat`. -/
@[simps]
/--
Definition of `HoCat.ιCompResolutionNatTrans` / `HoCat.ιCompResolutionNatTrans` 的定义

English:
definition HoCat.ιCompResolutionNatTrans
  signature: :
  body: toHoCat.map { hom := (HoCat.pResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact HoCat.resolutionMap_fac f.hom)

中文:
定义 HoCat.ιCompResolution自然数Trans
  签名: :
  定义体: toHoCat.map { hom := (HoCat.pResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact HoCat.resolutionMap_fac f.hom)

Depends on / 依赖: toHoCat
-/
noncomputable def HoCat.ιCompResolutionNatTrans :
    ι ⋙ HoCat.resolution (C := C) ⟶ toHoCat where
  app X := toHoCat.map { hom := (HoCat.pResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact HoCat.resolutionMap_fac f.hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (X : CofibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff]; rw [weakEquivalence_iff_of_objectProperty]
  infer_instance

instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight HoCat.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/--
Definition of `HoCat.toLocalization` / `HoCat.toLocalization` 的定义

English:
definition HoCat.toLocalization
  signature: : HoCat C ⥤ D
  body: CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h => (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ => Localization.inverts L (weakEquivalences _) _))

中文:
定义 HoCat.toLocalization
  签名: : HoCat C ⥤ D
  定义体: CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h => (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ => Localization.inverts L (weakEquivalences _) _))

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, Localization, Localization.inverts, Quotient, factorsThroughLocalization, inverts, map_eq_of_isInvertedBy, weakEquivalences
-/
def HoCat.toLocalization : HoCat C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h => (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ => Localization.inverts L (weakEquivalences _) _))

/--
Definition of `HoCat.toHoCatCompToLocalizationIso` / `HoCat.toHoCatCompToLocalizationIso` 的定义

English:
definition HoCat.toHoCatCompToLocalizationIso
  signature: : toHoCat ⋙ toLocalization L ≅ ι ⋙ L
  body: Iso.refl _

@[deprecated (since := "2026-01-31")]
alias HoCat.toπCompToLocalizationIso := HoCat.toHoCatCompToLocalizationIso

中文:
定义 HoCat.toHoCatCompToLocalizationIso
  签名: : toHoCat ⋙ toLocalization L ≅ ι ⋙ L
  定义体: Iso.refl _

@[deprecated (since := "2026-01-31")]
alias HoCat.toπCompToLocalizationIso := HoCat.toHoCatCompToLocalizationIso

Depends on / 依赖: Iso.refl
-/
def HoCat.toHoCatCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

@[deprecated (since := "2026-01-31")]
alias HoCat.toπCompToLocalizationIso := HoCat.toHoCatCompToLocalizationIso

/--
Definition of `HoCat.resolutionCompToLocalizationNatTrans` / `HoCat.resolutionCompToLocalizationNatTrans` 的定义

English:
definition HoCat.resolutionCompToLocalizationNatTrans
  signature: :
  body: L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f)

中文:
定义 HoCat.resolutionCompToLocalization自然数Trans
  签名: :
  定义体: L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f)

Depends on / 依赖: L.map, pResolutionObj
-/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L where
  app X := L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (HoCat.resolutionCompToLocalizationNatTrans L)
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

中文:
实例 :
  签名: 是同构 (HoCat.resolutionCompToLocalization自然数Trans L)
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

Depends on / 依赖: Localization, Localization.inverts, NatTrans, NatTrans.isIso_iff_isIso_app, infer_instance, inverts, isIso_iff_isIso_app, weakEquivalence_iff, weakEquivalences
-/
instance : IsIso (HoCat.resolutionCompToLocalizationNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

end

variable (C) in
/-- The inclusion `CofibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
/--
Definition of `localizerMorphism` / `localizerMorphism` 的定义

English:
definition localizerMorphism
  signature: : LocalizerMorphism (weakEquivalences (CofibrantObject C))
  body: ι
  map := by rfl

中文:
定义 localizerMorphism
  签名: : Localizer态射 (weakEquivalences (CofibrantObject C))
  定义体: ι
  map := by rfl
-/
def localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (localizerMorphism C).IsLocalizedEquivalence
  body: by
  let Hcof := (weakEquivalences (HoCat C)).Localization
  let Lcofπ : HoCat C ⥤ Hcof := (weakEquivalences (CofibrantObject.HoCat C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toHoCat ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : HoCat.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (HoCat.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : HoCat.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ HoCat.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

中文:
实例 :
  签名: (localizerMorphism C).是LocalizedEquivalence
  定义体: by
  let Hcof := (weakEquivalences (HoCat C)).Localization
  let Lcofπ : HoCat C ⥤ Hcof := (weakEquivalences (CofibrantObject.HoCat C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toHoCat ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : HoCat.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (HoCat.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : HoCat.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ HoCat.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

Depends on / 依赖: CatCommSq, CatCommSq.iso, CategoryTheory, CategoryTheory.Quotient.natIsoLift, CofibrantObject, CofibrantObject.HoCat, HoCat.toLocalization, Localization, Quotient, functor, localizedFunctor, localizerMorphism, natIsoLift, toHoCat, toLocalization, weakEquivalences
-/
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hcof := (weakEquivalences (HoCat C)).Localization
  let Lcofπ : HoCat C ⥤ Hcof := (weakEquivalences (CofibrantObject.HoCat C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toHoCat ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : HoCat.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (HoCat.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : HoCat.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ HoCat.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

set_option backward.defeqAttrib.useBackward true in
instance (X : CofibrantObject C) :
    IsCofibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end CofibrantObject

end HomotopicalAlgebra
