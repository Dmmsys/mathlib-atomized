/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of fibrant objects

Let `C` be a model category. By using the left homotopy relation,
we introduce the homotopy category `FibrantObject.HoCat C` of fibrant objects
in `C`, and we define a fibrant resolution functor
`FibrantObject.HoCat.resolution : C ⥤ FibrantObject.HoCat C`.

This file was obtained by dualizing the definitions in
`Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace FibrantObject

variable (C) in
/--
Definition of `homRel` / `homRel` 的定义

English:
definition homRel
  signature: : HomRel (FibrantObject C)
  body: fun _ _ f g => LeftHomotopyRel f.hom g.hom

中文:
定义 homRel
  签名: : HomRel (FibrantObject C)
  定义体: fun _ _ f g => LeftHomotopyRel f.hom g.hom

Depends on / 依赖: LeftHomotopyRel, f.hom, g.hom
-/
def homRel : HomRel (FibrantObject C) :=
  fun _ _ f g => LeftHomotopyRel f.hom g.hom

/--
lemma `homRel_iff_leftHomotopyRel` / 引理 `homRel_iff_leftHomotopyRel`

English:
lemma homRel_iff_leftHomotopyRel
  given: {X Y : FibrantObject C} {f g : X ⟶ Y}
  proof: Iff.rfl

中文:
引理 homRel_iff_leftHomotopyRel
  条件: {X Y : FibrantObject C} {f g : X ⟶ Y}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomRel.IsStableUnderPostcomp (homRel C)
  body: h.postcomp _

中文:
实例 :
  签名: HomRel.IsStableUnderPostcomp (homRel C)
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
  签名: HomRel.IsStableUnderPrecomp (homRel C)
  定义体: h.precomp _

Depends on / 依赖: h.precomp, precomp
-/
instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _

/--
lemma `homRel_equivalence_of_isCofibrant_src` / 引理 `homRel_equivalence_of_isCofibrant_src`

English:
lemma homRel_equivalence_of_isCofibrant_src
  given: {X Y : FibrantObject C} [IsCofibrant X.obj]
  proof: (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)

中文:
引理 homRel_equivalence_of_isCofibrant_src
  条件: {X Y : FibrantObject C} [IsCofibrant X.obj]
  证明: (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)
-/
lemma homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant X.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) => f.hom)

variable (C) in
/--
Definition of `HoCat` / `HoCat` 的定义

English:
abbreviation HoCat
  body: Quotient (FibrantObject.homRel C)

中文:
缩写 HoCat
  定义体: Quotient (FibrantObject.homRel C)

Depends on / 依赖: FibrantObject, FibrantObject.homRel, Quotient, homRel
-/
abbrev HoCat := Quotient (FibrantObject.homRel C)

/--
Definition of `toHoCat` / `toHoCat` 的定义

English:
definition toHoCat
  signature: : FibrantObject C ⥤ HoCat C
  body: Quotient.functor _

中文:
定义 toHoCat
  签名: : FibrantObject C ⥤ HoCat C
  定义体: Quotient.functor _

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def toHoCat : FibrantObject C ⥤ HoCat C := Quotient.functor _

/--
lemma `toHoCat_obj_surjective` / 引理 `toHoCat_obj_surjective`

English:
lemma toHoCat_obj_surjective
  statement: Function.Surjective (toHoCat (C := C)).obj
  proof: fun ⟨_⟩ => ⟨_, rfl⟩

中文:
引理 toHoCat_obj_surjective
  结论: Function.Surjective (toHoCat (C := C)).obj
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
  签名: Functor.Full (toHoCat (C := C))
  定义体: by dsimp [toHoCat]; infer_instance

Depends on / 依赖: infer_instance, toHoCat
-/
instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance

/--
lemma `toHoCat_map_eq` / 引理 `toHoCat_map_eq`

English:
lemma toHoCat_map_eq
  statement: {X Y : FibrantObject C} {f g : X ⟶ Y}
  proof: CategoryTheory.Quotient.sound _ h

中文:
引理 toHoCat_map_eq
  结论: {X Y : FibrantObject C} {f g : X ⟶ Y}
  证明: CategoryTheory.Quotient.sound _ h

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient
-/
lemma toHoCat_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

/--
lemma `toHoCat_map_eq_iff` / 引理 `toHoCat_map_eq_iff`

English:
lemma toHoCat_map_eq_iff
  given: {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y)
  proof: by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isCofibrant_src.eqvGen_eq]

中文:
引理 toHoCat_map_eq_iff
  条件: {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y)
  证明: by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isCofibrant_src.eqvGen_eq]

Depends on / 依赖: Functor, Functor.homRel_iff, HomRel, HomRel.compClosure_eq_self, Quotient, Quotient.functor_homRel_eq_compClosure_eqvGen, compClosure_eq_self, eqvGen_eq, functor_homRel_eq_compClosure_eqvGen, homRel_equivalence_of_isCofibrant_src, homRel_equivalence_of_isCofibrant_src.eqvGen_eq, homRel_iff, toHoCat
-/
lemma toHoCat_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self]; rw [homRel_equivalence_of_isCofibrant_src.eqvGen_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (weakEquivalences (FibrantObject C)).HasQuotient (homRel C)
  body: by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

中文:
实例 :
  签名: (weakEquivalences (FibrantObject C)).HasQuotient (homRel C)
  定义体: by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

Depends on / 依赖: h.weakEquivalence_iff, weakEquivalence_iff, weakEquivalence_iff_of_objectProperty
-/
instance : (weakEquivalences (FibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithWeakEquivalences (FibrantObject.HoCat C)
  body: (weakEquivalences _).quotient _

中文:
实例 :
  签名: CategoryWithWeakEquivalences (FibrantObject.HoCat C)
  定义体: (weakEquivalences _).quotient _

Depends on / 依赖: quotient, weakEquivalences
-/
instance : CategoryWithWeakEquivalences (FibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _

/--
lemma `weakEquivalence_toHoCat_map_iff` / 引理 `weakEquivalence_toHoCat_map_iff`

English:
lemma weakEquivalence_toHoCat_map_iff
  given: {X Y : FibrantObject C} (f : X ⟶ Y)
  proof: by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

中文:
引理 weakEquivalence_toHoCat_map_iff
  条件: {X Y : FibrantObject C} (f : X ⟶ Y)
  证明: by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

Depends on / 依赖: MorphismProperty, MorphismProperty.quotient_iff, quotient_iff, weakEquivalence_iff
-/
lemma weakEquivalence_toHoCat_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
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
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (FibrantObject.HoCat C)) where
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
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  let L := (weakEquivalences (FibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.i₀) = L.map (homMk P.i₁) by
    simp only [show f = homMk P.i₀ ≫ homMk h.h by cat_disch,
      show g = homMk 

中文:
引理 factorsThroughLocalization
  证明: by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  let L := (weakEquivalences (FibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.i₀) = L.map (homMk P.i₁) by
    simp only [show f = homMk P.i₀ ≫ homMk h.h by cat_disch,
      show g = homMk 

Depends on / 依赖: FibrantObject, Functor, Functor.map_comp, L.map, Localization, Localization.inverts, areEqualizedByLocalization_iff, cancel_mono, cat_disch, exists_very_good_cylinder, h.exists_very_good_cylinder, infer_instance, inverts, map_comp, weakEquivalence_homMk_iff, weakEquivalence_iff, weakEquivalences
-/
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (FibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  let L := (weakEquivalences (FibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.i₀) = L.map (homMk P.i₁) by
    simp only [show f = homMk P.i₀ ≫ homMk h.h by cat_disch,
      show g = homMk P.i₁ ≫ homMk h.h by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.π) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp [← cancel_mono (L.map (homMk P.π)), ← L.map_comp]

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
  签名: (toHoCatLocalizerMorphism C).IsLocalizedEquivalence
  定义体: by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

Depends on / 依赖: MorphismProperty, MorphismProperty.eq_inverseImage_quotientFunctor, eq_inverseImage_quotientFunctor, factorsThroughLocalization, isLocalizedEquivalence
-/
instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)

/--
lemma `HoCat.exists_resolution` / 引理 `HoCat.exists_resolution`

English:
lemma HoCat.exists_resolution
  given: (X : C)
  proof: by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance

中文:
引理 HoCat.exists_resolution
  条件: (X : C)
  证明: by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance
-/
lemma HoCat.exists_resolution (X : C) :
    exists (X' : C) (_ : IsFibrant X') (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
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
-/
noncomputable def HoCat.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

instance (X : C) : IsFibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/--
Definition of `HoCat.iResolutionObj` / `HoCat.iResolutionObj` 的定义

English:
definition HoCat.iResolutionObj
  signature: (X : C)
  body: (exists_resolution X).choose_spec.choose_spec.choose

中文:
定义 HoCat.iResolutionObj
  签名: (X : C)
  定义体: (exists_resolution X).choose_spec.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose, exists_resolution
-/
noncomputable def HoCat.iResolutionObj (X : C) : X ⟶ resolutionObj X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Cofibration (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2

instance (X : C) [IsCofibrant X] : IsCofibrant (HoCat.resolutionObj X) :=
  isCofibrant_of_cofibration (HoCat.iResolutionObj X)

/--
lemma `HoCat.exists_resolution_map` / 引理 `HoCat.exists_resolution_map`

English:
lemma HoCat.exists_resolution_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

中文:
引理 HoCat.exists_resolution_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩
-/
lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    exists (g : resolutionObj X ⟶ resolutionObj Y),
      iResolutionObj X ≫ g = f ≫ iResolutionObj Y := by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

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
-/
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    iResolutionObj X ≫ resolutionMap f =
      f ≫ iResolutionObj Y :=
  (exists_resolution_map f).choose_spec

@[simp]
/--
lemma `HoCat.weakEquivalence_resolutionMap_iff` / 引理 `HoCat.weakEquivalence_resolutionMap_iff`

English:
lemma HoCat.weakEquivalence_resolutionMap_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_postcomp_iff]

中文:
引理 HoCat.weakEquivalence_resolutionMap_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_postcomp_iff]
-/
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X)]; rw [HoCat.resolutionMap_fac]; rw [weakEquivalence_postcomp_iff]

/--
lemma `HoCat.resolutionObj_hom_ext` / 引理 `HoCat.resolutionObj_hom_ext`

English:
lemma HoCat.resolutionObj_hom_ext
  statement: {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
  proof: by
  apply toHoCat_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h

中文:
引理 HoCat.resolutionObj_hom_ext
  结论: {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
  证明: by
  apply toHoCat_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h
-/
lemma HoCat.resolutionObj_hom_ext {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
    (h : RightHomotopyRel (iResolutionObj X ≫ f) (iResolutionObj X ≫ g)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h

/--
Definition of `HoCat.resolution` / `HoCat.resolution` 的定义

English:
definition HoCat.resolution
  signature: : C ⥤ FibrantObject.HoCat C where
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
  签名: : C ⥤ FibrantObject.HoCat C where
  定义体: toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)
-/
noncomputable def HoCat.resolution : C ⥤ FibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The fibrant resolution functor `HoCat.resolution`, as a localizer morphism. -/
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
-/
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.iResolutionObj`, when applied to already fibrant objects, gives
a natural transformation `toHoCat ⟶ ι ⋙ HoCat.resolution`. -/
@[simps]
/--
Definition of `HoCat.ιCompResolutionNatTrans` / `HoCat.ιCompResolutionNatTrans` 的定义

English:
definition HoCat.ιCompResolutionNatTrans
  signature: : toHoCat ⟶ ι ⋙ HoCat.resolution (C := C) where
  body: toHoCat.map { hom := (HoCat.iResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact (HoCat.resolutionMap_fac f.hom).symm)

中文:
定义 HoCat.ιCompResolutionNatTrans
  签名: : toHoCat ⟶ ι ⋙ HoCat.resolution (C := C) where
  定义体: toHoCat.map { hom := (HoCat.iResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact (HoCat.resolutionMap_fac f.hom).symm)
-/
noncomputable def HoCat.ιCompResolutionNatTrans : toHoCat ⟶ ι ⋙ HoCat.resolution (C := C) where
  app X := toHoCat.map { hom := (HoCat.iResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact (HoCat.resolutionMap_fac f.hom).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (X : FibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff]; rw [weakEquivalence_iff_of_objectProperty]
  infer_instance

instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
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

中文:
定义 HoCat.toHoCatCompToLocalizationIso
  签名: : toHoCat ⋙ toLocalization L ≅ ι ⋙ L
  定义体: Iso.refl _
-/
def HoCat.toHoCatCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

/--
Definition of `HoCat.resolutionCompToLocalizationNatTrans` / `HoCat.resolutionCompToLocalizationNatTrans` 的定义

English:
definition HoCat.resolutionCompToLocalizationNatTrans
  signature: :
  body: L.map (iResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f).symm

中文:
定义 HoCat.resolutionCompToLocalizationNatTrans
  签名: :
  定义体: L.map (iResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f).symm
-/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L where
  app X := L.map (iResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f).symm

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
  签名: IsIso (HoCat.resolutionCompToLocalization自然数Trans L)
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
/-- The inclusion `FibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
/--
Definition of `localizerMorphism` / `localizerMorphism` 的定义

English:
definition localizerMorphism
  signature: : LocalizerMorphism (weakEquivalences (FibrantObject C))
  body: ι
  map := by rfl

中文:
定义 localizerMorphism
  签名: : LocalizerMorphism (weakEquivalences (FibrantObject C))
  定义体: ι
  map := by rfl
-/
def localizerMorphism : LocalizerMorphism (weakEquivalences (FibrantObject C))
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
  let Hfib := (weakEquivalences (HoCat C)).Localization
  let Lfibπ : HoCat C ⥤ Hfib := (weakEquivalences (FibrantObject.HoCat C)).Q
  let Lfib : FibrantObject C ⥤ Hfib := toHoCat ⋙ Lfibπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerM

中文:
实例 :
  签名: (localizerMorphism C).IsLocalizedEquivalence
  定义体: by
  let Hfib := (weakEquivalences (HoCat C)).Localization
  let Lfibπ : HoCat C ⥤ Hfib := (weakEquivalences (FibrantObject.HoCat C)).Q
  let Lfib : FibrantObject C ⥤ Hfib := toHoCat ⋙ Lfibπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerM

Depends on / 依赖: CatCommSq, CatCommSq.iso, CategoryTheory, CategoryTheory.Quotient.natIsoLift, FibrantObject, FibrantObject.HoCat, HoCat.toH, HoCat.toLocalization, Localization, Quotient, functor, localizedFunctor, localizerMorphism, natIsoLift, toHoCat, toLocalization, weakEquivalences
-/
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hfib := (weakEquivalences (HoCat C)).Localization
  let Lfibπ : HoCat C ⥤ Hfib := (weakEquivalences (FibrantObject.HoCat C)).Q
  let Lfib : FibrantObject C ⥤ Hfib := toHoCat ⋙ Lfibπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lfib L
  let eF : ι ⋙ L ≅ Lfib ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lfib L F
  let eF' : HoCat.toLocalization L ≅ Lfibπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hfib := (HoCat.localizerMorphismResolution C).localizedFunctor L Lfibπ
  let eG : HoCat.resolution ⋙ Lfibπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lfibπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lfib (weakEquivalences (FibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lfibπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hfib ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lfib (weakEquivalences _) Lfib (ι ⋙ HoCat.resolution ⋙ Lfibπ) _ _
        (asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lfibπ) ≪≫ associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)).symm)
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lfib L F

set_option backward.defeqAttrib.useBackward true in
instance (X : FibrantObject C) :
    IsFibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (FibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end FibrantObject

end HomotopicalAlgebra
