/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import Mathlib.CategoryTheory.Quotient.LocallySmall

/-!
# The homotopy category of bifibrant objects

We construct the homotopy category `BifibrantObject.HoCat C` of bifibrant
objects in a model category `C` and show that the functor
`BifibrantObject.toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`
is a localization functor with respect to weak equivalences.
We also show that certain localizer morphisms are localized weak equivalences,
which can be understood by saying that we obtain the same localized
category (up to equivalence) by inverting weak equivalences in `C`,
`CofibrantObject C`, `FibrantObject C` or `BifibrantObject C`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace BifibrantObject

variable (C) in
/--
Definition of `homRel` / `homRel` 的定义

English:
definition homRel
  signature: : HomRel (BifibrantObject C)
  body: fun _ _ f g => RightHomotopyRel f.hom g.hom

中文:
定义 homRel
  签名: : HomRel (BifibrantObject C)
  定义体: fun _ _ f g => RightHomotopyRel f.hom g.hom

Depends on / 依赖: RightHomotopyRel, f.hom, g.hom
-/
def homRel : HomRel (BifibrantObject C) :=
  fun _ _ f g => RightHomotopyRel f.hom g.hom

/--
lemma `homRel_iff_rightHomotopyRel` / 引理 `homRel_iff_rightHomotopyRel`

English:
lemma homRel_iff_rightHomotopyRel
  given: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  proof: Iff.rfl

中文:
引理 homRel_iff_rightHomotopyRel
  条件: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma homRel_iff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl

/--
lemma `homRel_iff_leftHomotopyRel` / 引理 `homRel_iff_leftHomotopyRel`

English:
lemma homRel_iff_leftHomotopyRel
  given: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  proof: by
  rw [homRel_iff_rightHomotopyRel]; rw [leftHomotopyRel_iff_rightHomotopyRel]

中文:
引理 homRel_iff_leftHomotopyRel
  条件: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  证明: by
  rw [homRel_iff_rightHomotopyRel]; rw [leftHomotopyRel_iff_rightHomotopyRel]

Depends on / 依赖: homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel
-/
lemma homRel_iff_leftHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := by
  rw [homRel_iff_rightHomotopyRel]; rw [leftHomotopyRel_iff_rightHomotopyRel]

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
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Congruence (homRel C)
  body: { refl _ := .refl _
      symm h := .symm h
      trans h₁ h₂ := .trans h₁ h₂ }

中文:
实例 :
  签名: 余ngruence (homRel C)
  定义体: { refl _ := .refl _
      symm h := .symm h
      trans h₁ h₂ := .trans h₁ h₂ }
-/
instance : Congruence (homRel C) where
  equivalence :=
    { refl _ := .refl _
      symm h := .symm h
      trans h₁ h₂ := .trans h₁ h₂ }

variable (C) in
/--
Definition of `HoCat` / `HoCat` 的定义

English:
abbreviation HoCat
  body: Quotient (BifibrantObject.homRel C)

中文:
缩写 HoCat
  定义体: Quotient (BifibrantObject.homRel C)

Depends on / 依赖: BifibrantObject, BifibrantObject.homRel, Quotient, homRel
-/
abbrev HoCat := Quotient (BifibrantObject.homRel C)

/-- The quotient functor from the category of bifibrant objects to its
homotopy category. -/
@[implicit_reducible]
/--
Definition of `toHoCat` / `toHoCat` 的定义

English:
definition toHoCat
  signature: : BifibrantObject C ⥤ HoCat C
  body: Quotient.functor _

中文:
定义 toHoCat
  签名: : BifibrantObject C ⥤ HoCat C
  定义体: Quotient.functor _

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def toHoCat : BifibrantObject C ⥤ HoCat C := Quotient.functor _

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
  statement: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  proof: CategoryTheory.Quotient.sound _ h

中文:
引理 toHoCat_map_eq
  结论: {X Y : BifibrantObject C} {f g : X ⟶ Y}
  证明: CategoryTheory.Quotient.sound _ h

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient
-/
lemma toHoCat_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

/--
lemma `toHoCat_map_eq_iff` / 引理 `toHoCat_map_eq_iff`

English:
lemma toHoCat_map_eq_iff
  given: {X Y : BifibrantObject C} (f g : X ⟶ Y)
  proof: Quotient.functor_map_eq_iff _ _ _

中文:
引理 toHoCat_map_eq_iff
  条件: {X Y : BifibrantObject C} (f g : X ⟶ Y)
  证明: Quotient.functor_map_eq_iff _ _ _

Depends on / 依赖: Quotient, Quotient.functor_map_eq_iff, functor_map_eq_iff
-/
lemma toHoCat_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] : LocallySmall.{w} (HoCat C)
  body: by
  dsimp [HoCat]
  infer_instance

中文:
实例 [LocallySmall.{w}
  签名: C] : LocallySmall.{w} (HoCat C)
  定义体: by
  dsimp [HoCat]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [LocallySmall.{w} C] : LocallySmall.{w} (HoCat C) := by
  dsimp [HoCat]
  infer_instance

section

variable {D : Type*} [Category* D]

/--
lemma `inverts_iff_factors` / 引理 `inverts_iff_factors`

English:
lemma inverts_iff_factors
  given: (F : BifibrantObject C ⥤ D)
  proof: by
  refine ⟨fun H K L f g h => ?_, fun h X Y f hf => ?_⟩
  · obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
    have := isCofibrant_of_cofibration P.ι
    have : IsIso (F.map (homMk P.ι)) := H _ (by
      rw [← weakEquivalence_iff]; rw [weakEquivalence_iff_of_objectProperty]
      exact inferI

中文:
引理 inverts_iff_factors
  条件: (F : BifibrantObject C ⥤ D)
  证明: by
  refine ⟨fun H K L f g h => ?_, fun h X Y f hf => ?_⟩
  · obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
    have := isCofibrant_of_cofibration P.ι
    have : IsIso (F.map (homMk P.ι)) := H _ (by
      rw [← weakEquivalence_iff]; rw [weakEquivalence_iff_of_objectProperty]
      exact inferI

Depends on / 依赖: F.map, Functor, Functor.map_comp, WeakEquivalence, cancel_epi, cat_disch, exists_very_good_pathObject, h.exists_very_good_pathObject, isCofibrant_of_cofibration, map_comp, weakEquivalence_iff, weakEquivalence_iff_of_objectProperty
-/
lemma inverts_iff_factors (F : BifibrantObject C ⥤ D) :
    (weakEquivalences _).IsInvertedBy F ↔
    forall ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L),
      homRel C f g -> F.map f = F.map g := by
  refine ⟨fun H K L f g h => ?_, fun h X Y f hf => ?_⟩
  · obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
    have := isCofibrant_of_cofibration P.ι
    have : IsIso (F.map (homMk P.ι)) := H _ (by
      rw [← weakEquivalence_iff]; rw [weakEquivalence_iff_of_objectProperty]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp]
    congr 1
    simp [← cancel_epi (F.map (homMk P.ι)), ← Functor.map_comp]
  · rw [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty] at hf
    obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.whitehead f.hom
    refine ⟨F.map (homMk g'), ?_, ?_⟩
    all_goals
      rw [← F.map_comp]; rw [← F.map_id]
      apply h
      assumption

/--
Definition of `strictUniversalPropertyFixedTargetToHoCat` / `strictUniversalPropertyFixedTargetToHoCat` 的定义

English:
definition strictUniversalPropertyFixedTargetToHoCat
  signature: :
  body: by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

中文:
定义 strictUniversalPropertyFixedTargetToHoCat
  签名: :
  定义体: by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, CategoryTheory.Quotient.sound, Quotient, Quotient.lift_unique, inverts_iff_factors, lift_unique
-/
def strictUniversalPropertyFixedTargetToHoCat :
    Localization.StrictUniversalPropertyFixedTarget
      toHoCat (weakEquivalences (BifibrantObject C)) D where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: toHoCat.IsLocalization (weakEquivalences (BifibrantObject C))
  body: .mk' _ _ strictUniversalPropertyFixedTargetToHoCat
    strictUniversalPropertyFixedTargetToHoCat

中文:
实例 :
  签名: toHoCat.是Localization (weakEquivalences (BifibrantObject C))
  定义体: .mk' _ _ strictUniversalPropertyFixedTargetToHoCat
    strictUniversalPropertyFixedTargetToHoCat

Depends on / 依赖: strictUniversalPropertyFixedTargetToHoCat
-/
instance : toHoCat.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ strictUniversalPropertyFixedTargetToHoCat
    strictUniversalPropertyFixedTargetToHoCat

instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toHoCat.map f) :=
  Localization.inverts toHoCat (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

section

variable {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `HoCat.homEquivRight` / `HoCat.homEquivRight` 的定义

English:
definition HoCat.homEquivRight
  signature: :
  body: Quot.lift (fun f => toHoCat.map (homMk f)) (fun _ _ h => by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f => .mk f.hom) (fun _ _ h => by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using! h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]

中文:
定义 HoCat.homEquivRight
  签名: :
  定义体: Quot.lift (fun f => toHoCat.map (homMk f)) (fun _ _ h => by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f => .mk f.hom) (fun _ _ h => by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using! h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]

Depends on / 依赖: Quot.lift, toHoCat, toHoCat.map, toHoCat_map_eq_iff
-/
def HoCat.homEquivRight :
    RightHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) where
  toFun := Quot.lift (fun f => toHoCat.map (homMk f)) (fun _ _ h => by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f => .mk f.hom) (fun _ _ h => by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using! h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
/--
lemma `HoCat.homEquivRight_apply` / 引理 `HoCat.homEquivRight_apply`

English:
lemma HoCat.homEquivRight_apply
  given: (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 HoCat.homEquivRight_apply
  条件: (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma HoCat.homEquivRight_apply (f : X ⟶ Y) :
    HoCat.homEquivRight (.mk f) = toHoCat.map (homMk f) := rfl

@[simp]
/--
lemma `HoCat.homEquivRight_symm_apply` / 引理 `HoCat.homEquivRight_symm_apply`

English:
lemma HoCat.homEquivRight_symm_apply
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 HoCat.homEquivRight_symm_apply
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma HoCat.homEquivRight_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

/--
Definition of `HoCat.homEquivLeft` / `HoCat.homEquivLeft` 的定义

English:
definition HoCat.homEquivLeft
  signature: :
  body: leftHomotopyClassEquivRightHomotopyClass.trans HoCat.homEquivRight

@[simp]

中文:
定义 HoCat.homEquivLeft
  签名: :
  定义体: leftHomotopyClassEquivRightHomotopyClass.trans HoCat.homEquivRight

@[simp]

Depends on / 依赖: HoCat.homEquivRight, homEquivRight, leftHomotopyClassEquivRightHomotopyClass, leftHomotopyClassEquivRightHomotopyClass.trans
-/
def HoCat.homEquivLeft :
    LeftHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) :=
  leftHomotopyClassEquivRightHomotopyClass.trans HoCat.homEquivRight

@[simp]
/--
lemma `HoCat.homEquivLeft_apply` / 引理 `HoCat.homEquivLeft_apply`

English:
lemma HoCat.homEquivLeft_apply
  given: (f : X ⟶ Y)
  proof: by
  simp [homEquivLeft]

中文:
引理 HoCat.homEquivLeft_apply
  条件: (f : X ⟶ Y)
  证明: by
  simp [homEquivLeft]

Depends on / 依赖: homEquivLeft
-/
lemma HoCat.homEquivLeft_apply (f : X ⟶ Y) :
    HoCat.homEquivLeft (.mk f) = toHoCat.map (homMk f) := by
  simp [homEquivLeft]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `HoCat.homEquivLeft_symm_apply` / 引理 `HoCat.homEquivLeft_symm_apply`

English:
lemma HoCat.homEquivLeft_symm_apply
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 HoCat.homEquivLeft_symm_apply
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma HoCat.homEquivLeft_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `HoCat.ιFibrantObject` / `HoCat.ιFibrantObject` 的定义

English:
definition HoCat.ιFibrantObject
  signature: : HoCat C ⥤ FibrantObject.HoCat C
  body: CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [FibrantObject.toHoCat_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]

中文:
定义 HoCat.ιFibrantObject
  签名: : HoCat C ⥤ FibrantObject.HoCat C
  定义体: CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [FibrantObject.toHoCat_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]

Depends on / 依赖: BifibrantObject, CategoryTheory, CategoryTheory.Quotient.lift, FibrantObject, FibrantObject.homRel_iff_leftHomotopyRel, FibrantObject.toHoCat, FibrantObject.toHoCat_map_eq_iff, Quotient, homRel_iff_leftHomotopyRel, toHoCat, toHoCat_map_eq_iff
-/
def HoCat.ιFibrantObject : HoCat C ⥤ FibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [FibrantObject.toHoCat_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]
/--
lemma `HoCat.ιFibrantObject_obj` / 引理 `HoCat.ιFibrantObject_obj`

English:
lemma HoCat.ιFibrantObject_obj
  given: (X : BifibrantObject C)
  proof: rfl

@[simp]

中文:
引理 HoCat.ιFibrantObject_obj
  条件: (X : BifibrantObject C)
  证明: rfl

@[simp]
-/
lemma HoCat.ιFibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιFibrantObject.obj (toHoCat.obj X) =
      FibrantObject.toHoCat.obj (BifibrantObject.ιFibrantObject.obj X) :=
  rfl

@[simp]
/--
lemma `HoCat.ιFibrantObject_map_toHoCat_map` / 引理 `HoCat.ιFibrantObject_map_toHoCat_map`

English:
lemma HoCat.ιFibrantObject_map_toHoCat_map
  given: {X Y : BifibrantObject C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 HoCat.ιFibrantObject_map_toHoCat_map
  条件: {X Y : BifibrantObject C} (f : X ⟶ Y)
  证明: rfl
-/
lemma HoCat.ιFibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιFibrantObject.map (toHoCat.map f) =
      FibrantObject.toHoCat.map (FibrantObject.homMk f.hom) :=
  rfl

/--
Definition of `toHoCatCompιFibrantObject` / `toHoCatCompιFibrantObject` 的定义

English:
definition toHoCatCompιFibrantObject
  signature: :
  body: Iso.refl _

中文:
定义 toHoCatCompιFibrantObject
  签名: :
  定义体: Iso.refl _
-/
def toHoCatCompιFibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιFibrantObject ≅
      ιFibrantObject ⋙ FibrantObject.toHoCat := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion functor `BifibrantObject.HoCat C ⥤ CofibrantObject.HoCat C`. -/
@[implicit_reducible]
/--
Definition of `HoCat.ιCofibrantObject` / `HoCat.ιCofibrantObject` 的定义

English:
definition HoCat.ιCofibrantObject
  signature: : HoCat C ⥤ CofibrantObject.HoCat C
  body: CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [CofibrantObject.toHoCat_map_eq_iff])

@[simp]

中文:
定义 HoCat.ιCofibrantObject
  签名: : HoCat C ⥤ CofibrantObject.HoCat C
  定义体: CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [CofibrantObject.toHoCat_map_eq_iff])

@[simp]

Depends on / 依赖: BifibrantObject, CategoryTheory, CategoryTheory.Quotient.lift, CofibrantObject, CofibrantObject.toHoCat, CofibrantObject.toHoCat_map_eq_iff, Quotient, toHoCat, toHoCat_map_eq_iff
-/
def HoCat.ιCofibrantObject : HoCat C ⥤ CofibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toHoCat) (fun _ _ _ _ h => by
      simpa [CofibrantObject.toHoCat_map_eq_iff])

@[simp]
/--
lemma `HoCat.ιCofibrantObject_obj` / 引理 `HoCat.ιCofibrantObject_obj`

English:
lemma HoCat.ιCofibrantObject_obj
  given: (X : BifibrantObject C)
  proof: rfl

@[simp]

中文:
引理 HoCat.ιCofibrantObject_obj
  条件: (X : BifibrantObject C)
  证明: rfl

@[simp]
-/
lemma HoCat.ιCofibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιCofibrantObject.obj (toHoCat.obj X) =
      CofibrantObject.toHoCat.obj (BifibrantObject.ιCofibrantObject.obj X) :=
  rfl

@[simp]
/--
lemma `HoCat.ιCofibrantObject_map_toHoCat_map` / 引理 `HoCat.ιCofibrantObject_map_toHoCat_map`

English:
lemma HoCat.ιCofibrantObject_map_toHoCat_map
  given: {X Y : BifibrantObject C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 HoCat.ιCofibrantObject_map_toHoCat_map
  条件: {X Y : BifibrantObject C} (f : X ⟶ Y)
  证明: rfl
-/
lemma HoCat.ιCofibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιCofibrantObject.map (toHoCat.map f) =
      CofibrantObject.toHoCat.map (CofibrantObject.homMk f.hom) :=
  rfl

/--
Definition of `toHoCatCompιCofibrantObject` / `toHoCatCompιCofibrantObject` 的定义

English:
definition toHoCatCompιCofibrantObject
  signature: :
  body: Iso.refl _

中文:
定义 toHoCatCompιCofibrantObject
  签名: :
  定义体: Iso.refl _
-/
def toHoCatCompιCofibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιCofibrantObject ≅
      ιCofibrantObject ⋙ CofibrantObject.toHoCat := Iso.refl _

end BifibrantObject

namespace CofibrantObject

/--
lemma `exists_bifibrant` / 引理 `exists_bifibrant`

English:
lemma exists_bifibrant
  given: (X : CofibrantObject C)
  proof: by
  let h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, ho

中文:
引理 存在_bifibrant
  条件: (X : CofibrantObject C)
  证明: by
  let h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, ho

Depends on / 依赖: BifibrantObject, BifibrantObject.mk, Cofibration, IsFibrant, MorphismProperty, MorphismProperty.factorizationData, WeakEquivalence, X.obj, factorizationData, fibrations, infer_instance, isCofibrant_of_cofibration, isFibrant_iff_of_isTerminal, terminal, terminal.from, terminalIsTerminal, trivialCofibrations
-/
lemma exists_bifibrant (X : CofibrantObject C) :
    exists (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  let h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, homMk h.i, inferInstanceAs (Cofibration h.i),
    inferInstanceAs (WeakEquivalence h.i)⟩

/--
Definition of `bifibrantResolutionObj` / `bifibrantResolutionObj` 的定义

English:
definition bifibrantResolutionObj
  signature: (X : CofibrantObject C)
  body: (exists_bifibrant X).choose

中文:
定义 bifibrantResolutionObj
  签名: (X : CofibrantObject C)
  定义体: (exists_bifibrant X).choose

Depends on / 依赖: exists_bifibrant
-/
noncomputable def bifibrantResolutionObj (X : CofibrantObject C) :
    BifibrantObject C :=
  (exists_bifibrant X).choose

/--
Definition of `iBifibrantResolutionObj` / `iBifibrantResolutionObj` 的定义

English:
definition iBifibrantResolutionObj
  signature: (X : CofibrantObject C)
  body: (exists_bifibrant X).choose_spec.choose

中文:
定义 iBifibrantResolutionObj
  签名: (X : CofibrantObject C)
  定义体: (exists_bifibrant X).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, exists_bifibrant
-/
noncomputable def iBifibrantResolutionObj (X : CofibrantObject C) :
    X ⟶ BifibrantObject.ιCofibrantObject.obj (bifibrantResolutionObj X) :=
  (exists_bifibrant X).choose_spec.choose

instance (X : CofibrantObject C) :
    Cofibration (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.1

instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.2

instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X) := by
  rw [weakEquivalence_iff_of_objectProperty]
  infer_instance

instance (X : BifibrantObject C) :
    IsFibrant (ι.obj (BifibrantObject.ιCofibrantObject.obj X)) := X.2.2

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_bifibrant_map` / 引理 `exists_bifibrant_map`

English:
lemma exists_bifibrant_map
  given: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  proof: by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

中文:
引理 存在_bifibrant_map
  条件: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  证明: by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

Depends on / 依赖: BifibrantObject, BifibrantObject.homMk, CommSq, cat_disch, iBifibrantResolutionObj, sq.lift, terminal, terminal.from
-/
lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    exists (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

/--
Definition of `bifibrantResolutionMap` / `bifibrantResolutionMap` 的定义

English:
definition bifibrantResolutionMap
  signature: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  body: (exists_bifibrant_map f).choose

#adaptation_note

中文:
定义 bifibrantResolutionMap
  签名: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  定义体: (exists_bifibrant_map f).choose

#adaptation_note

Depends on / 依赖: exists_bifibrant_map
-/
noncomputable def bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `bifibrantResolutionMap_fac` / 引理 `bifibrantResolutionMap_fac`

English:
lemma bifibrantResolutionMap_fac
  given: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  proof: (exists_bifibrant_map f).choose_spec

中文:
引理 bifibrantResolutionMap_fac
  条件: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  证明: (exists_bifibrant_map f).choose_spec

Depends on / 依赖: choose_spec, exists_bifibrant_map
-/
lemma bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    iBifibrantResolutionObj X₁ ≫ homMk (bifibrantResolutionMap f).hom =
      f ≫ iBifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose_spec

set_option backward.isDefEq.respectTransparency false in
instance {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) [WeakEquivalence f] :
    WeakEquivalence (bifibrantResolutionMap f) := by
  rw [weakEquivalence_iff]
  change weakEquivalences _ (CofibrantObject.homMk (bifibrantResolutionMap f).hom)
  rw [← weakEquivalence_iff]; rw [← weakEquivalence_precomp_iff (iBifibrantResolutionObj X₁)]; rw [bifibrantResolutionMap_fac]; rw [weakEquivalence_precomp_iff]
  infer_instance

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `bifibrantResolutionMap_fac'` / 引理 `bifibrantResolutionMap_fac'`

English:
lemma bifibrantResolutionMap_fac'
  given: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  proof: toHoCat.congr_map (bifibrantResolutionMap_fac f)

中文:
引理 bifibrantResolutionMap_fac'
  条件: {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂)
  证明: toHoCat.congr_map (bifibrantResolutionMap_fac f)

Depends on / 依赖: bifibrantResolutionMap_fac, congr_map, toHoCat, toHoCat.congr_map
-/
lemma bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toHoCat.map X₁.iBifibrantResolutionObj ≫
    toHoCat.map (homMk (bifibrantResolutionMap f).hom) =
    toHoCat.map f ≫ toHoCat.map X₂.iBifibrantResolutionObj :=
  toHoCat.congr_map (bifibrantResolutionMap_fac f)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `bifibrantResolutionObj_hom_ext` / 引理 `bifibrantResolutionObj_hom_ext`

English:
lemma bifibrantResolutionObj_hom_ext
  proof: by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toHoCat_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  change toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toHoCat.map (X.

中文:
引理 bifibrantResolutionObj_hom_ext
  证明: by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toHoCat_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  change toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toHoCat.map (X.

Depends on / 依赖: BifibrantObject, BifibrantObject.toHoCat.map_surjective, BifibrantObject.toHoCat_obj_surjective, CofibrantObject, CofibrantObject.homRel_iff_rightHomotopyRel, CofibrantObject.map, CofibrantObject.toHoCat_map_eq_iff, RightHomotopyClass, RightHomotopyClass.mk_eq_mk_iff, X.iBifibrantResolutionObj, homRel_iff_rightHomotopyRel, iBifibrantResolutionObj, map_surjective, mk_eq_mk_iff, toHoCat, toHoCat.map, toHoCat_map_eq_iff, toHoCat_obj_surjective
-/
lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.HoCat C} {f g :
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.HoCat.ιCofibrantObject.map f =
      CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.HoCat.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toHoCat_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  change toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toHoCat_map_eq_iff]; rw [CofibrantObject.homRel_iff_rightHomotopyRel]; rw [← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toHoCat_map_eq_iff]; rw [BifibrantObject.homRel_iff_rightHomotopyRel]; rw [← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    _ (iBifibrantResolutionObj X).hom).1
  simpa using! h

set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the category of cofibrant objects
to the homotopy category of bifibrant objects. -/
@[simps, implicit_reducible]
/--
Definition of `HoCat.bifibrantResolution'` / `HoCat.bifibrantResolution'` 的定义

English:
definition HoCat.bifibrantResolution'
  signature: : CofibrantObject C ⥤ BifibrantObject.HoCat C where
  body: BifibrantObject.toHoCat.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toHoCat.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

中文:
定义 HoCat.bifibrantResolution'
  签名: : CofibrantObject C ⥤ BifibrantObject.HoCat C where
  定义体: BifibrantObject.toHoCat.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toHoCat.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

Depends on / 依赖: BifibrantObject, BifibrantObject.toHoCat.obj, bifibrantResolutionObj, toHoCat
-/
noncomputable def HoCat.bifibrantResolution' : CofibrantObject C ⥤ BifibrantObject.HoCat C where
  obj X := BifibrantObject.toHoCat.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toHoCat.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the homotopy category of
cofibrant objects to the homotopy category of bifibrant objects. -/
@[implicit_reducible]
/--
Definition of `HoCat.bifibrantResolution` / `HoCat.bifibrantResolution` 的定义

English:
definition HoCat.bifibrantResolution
  signature: :
  body: CategoryTheory.Quotient.lift _ CofibrantObject.HoCat.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toHoCat_map_eq_iff] using! h.postcomp _)

@[simp]

中文:
定义 HoCat.bifibrantResolution
  签名: :
  定义体: CategoryTheory.Quotient.lift _ CofibrantObject.HoCat.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toHoCat_map_eq_iff] using! h.postcomp _)

@[simp]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, CofibrantObject, CofibrantObject.HoCat.bifibrantResolution, Functor, Functor.map_comp, Quotient, bifibrantResolution, bifibrantResolutionObj_hom_ext, h.postcomp, map_comp, postcomp, toHoCat_map_eq_iff
-/
noncomputable def HoCat.bifibrantResolution :
    CofibrantObject.HoCat C ⥤ BifibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.HoCat.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toHoCat_map_eq_iff] using! h.postcomp _)

@[simp]
/--
lemma `HoCat.bifibrantResolution_obj` / 引理 `HoCat.bifibrantResolution_obj`

English:
lemma HoCat.bifibrantResolution_obj
  given: (X : CofibrantObject C)
  proof: rfl

@[simp]

中文:
引理 HoCat.bifibrantResolution_obj
  条件: (X : CofibrantObject C)
  证明: rfl

@[simp]
-/
lemma HoCat.bifibrantResolution_obj (X : CofibrantObject C) :
    HoCat.bifibrantResolution.obj (CofibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) := rfl

@[simp]
/--
lemma `HoCat.bifibrantResolution_map` / 引理 `HoCat.bifibrantResolution_map`

English:
lemma HoCat.bifibrantResolution_map
  given: {X Y : CofibrantObject C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 HoCat.bifibrantResolution_map
  条件: {X Y : CofibrantObject C} (f : X ⟶ Y)
  证明: rfl
-/
lemma HoCat.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    HoCat.bifibrantResolution.map (CofibrantObject.toHoCat.map f) =
      BifibrantObject.toHoCat.map (bifibrantResolutionMap f) := rfl

/--
Definition of `HoCat.adjUnit` / `HoCat.adjUnit` 的定义

English:
definition HoCat.adjUnit
  signature: :
  body: Quotient.natTransLift _
    { app X := toHoCat.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

中文:
定义 HoCat.adjUnit
  签名: :
  定义体: Quotient.natTransLift _
    { app X := toHoCat.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

Depends on / 依赖: Quotient, Quotient.natTransLift, bifibrantResolutionMap_fac, iBifibrantResolutionObj, natTransLift, naturality, toHoCat, toHoCat.map
-/
noncomputable def HoCat.adjUnit :
    𝟭 (HoCat C) ⟶ HoCat.bifibrantResolution ⋙ BifibrantObject.HoCat.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toHoCat.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

/--
lemma `HoCat.adjUnit_app` / 引理 `HoCat.adjUnit_app`

English:
lemma HoCat.adjUnit_app
  given: (X : CofibrantObject C)
  proof: rfl

中文:
引理 HoCat.adjUnit_app
  条件: (X : CofibrantObject C)
  证明: rfl
-/
lemma HoCat.adjUnit_app (X : CofibrantObject C) :
    HoCat.adjUnit.app (toHoCat.obj X) =
      toHoCat.map (iBifibrantResolutionObj X) := rfl

set_option backward.isDefEq.respectTransparency false in
instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adjUnit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  rw [HoCat.adjUnit_app]; rw [weakEquivalence_toHoCat_map_iff]; rw [weakEquivalence_iff_of_objectProperty]
  infer_instance

/--
Definition of `HoCat.adjCounit'` / `HoCat.adjCounit'` 的定义

English:
definition HoCat.adjCounit'
  signature: :
  body: Quotient.natTransLift _
    { app X :=
        BifibrantObject.toHoCat.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toHoCat.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fa

中文:
定义 HoCat.adjCounit'
  签名: :
  定义体: Quotient.natTransLift _
    { app X :=
        BifibrantObject.toHoCat.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toHoCat.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fa

Depends on / 依赖: BifibrantObject, BifibrantObject.homMk, BifibrantObject.toHoCat.congr_map, BifibrantObject.toHoCat.map, CofibrantObject, CofibrantObject.homMk, ObjectProperty, Quotient, Quotient.natTransLift, X.obj, bifibrantResolutionMap_fac, congr_map, f.hom, iBifibrantResolutionObj, natTransLift, naturality, toHoCat
-/
noncomputable def HoCat.adjCounit' :
    𝟭 (BifibrantObject.HoCat C) ⟶
      BifibrantObject.HoCat.ιCofibrantObject ⋙ HoCat.bifibrantResolution :=
  Quotient.natTransLift _
    { app X :=
        BifibrantObject.toHoCat.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toHoCat.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fac (CofibrantObject.homMk f.hom)).symm
        ext : 1
        dsimp
        exact this) }

/--
lemma `HoCat.adjCounit'_app` / 引理 `HoCat.adjCounit'_app`

English:
lemma HoCat.adjCounit'_app
  given: (X : BifibrantObject C)
  proof: rfl

中文:
引理 HoCat.adjCounit'_app
  条件: (X : BifibrantObject C)
  证明: rfl
-/
lemma HoCat.adjCounit'_app (X : BifibrantObject C) :
    HoCat.adjCounit'.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        (iBifibrantResolutionObj (.mk X.obj)).hom) := rfl

set_option backward.isDefEq.respectTransparency false in
instance (X : BifibrantObject.HoCat C) : IsIso (HoCat.adjCounit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
  rw [HoCat.adjCounit'_app]
  have : WeakEquivalence (C := BifibrantObject C)
      (BifibrantObject.homMk ((mk X.obj).iBifibrantResolutionObj).hom) := by
    simp only [BifibrantObject.weakEquivalence_homMk_iff]
    infer_instance
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (HoCat.adjCounit' (C := C))
  body: NatIso.isIso_of_isIso_app _

中文:
实例 :
  签名: 是同构 (HoCat.adjCounit' (C := C))
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance : IsIso (HoCat.adjCounit' (C := C)) := NatIso.isIso_of_isIso_app _

/--
Definition of `HoCat.adjCounitIso` / `HoCat.adjCounitIso` 的定义

English:
definition HoCat.adjCounitIso
  signature: :
  body: (asIso HoCat.adjCounit').symm

中文:
定义 HoCat.adjCounitIso
  签名: :
  定义体: (asIso HoCat.adjCounit').symm

Depends on / 依赖: HoCat.adjCounit, adjCounit
-/
noncomputable def HoCat.adjCounitIso :
    BifibrantObject.HoCat.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.HoCat C) :=
  (asIso HoCat.adjCounit').symm

/--
lemma `HoCat.adjCounitIso_inv_app` / 引理 `HoCat.adjCounitIso_inv_app`

English:
lemma HoCat.adjCounitIso_inv_app
  given: (X : BifibrantObject C)
  proof: rfl

中文:
引理 HoCat.adjCounitIso_inv_app
  条件: (X : BifibrantObject C)
  证明: rfl
-/
lemma HoCat.adjCounitIso_inv_app (X : BifibrantObject C) :
    HoCat.adjCounitIso.inv.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        ((iBifibrantResolutionObj (.mk X.obj))).hom) := rfl

/--
Definition of `HoCat.adj` / `HoCat.adj` 的定义

English:
definition HoCat.adj
  signature: :
  body: HoCat.adjUnit
  counit := HoCat.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [comp_hom_eq_id]; push inv
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [HoCat.adjC

中文:
定义 HoCat.adj
  签名: :
  定义体: HoCat.adjUnit
  counit := HoCat.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [comp_hom_eq_id]; push inv
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [HoCat.adjC

Depends on / 依赖: BifibrantObject, BifibrantObject.HoCat
-/
noncomputable def HoCat.adj :
    HoCat.bifibrantResolution (C := C) ⊣ BifibrantObject.HoCat.ιCofibrantObject where
  unit := HoCat.adjUnit
  counit := HoCat.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [comp_hom_eq_id]; push inv
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [HoCat.adjCounitIso_inv_app]
    apply bifibrantResolutionMap_fac'
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
    rw [comp_hom_eq_id]; push inv
    cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (HoCat.adj (C := C)).counit
  body: by
  dsimp [HoCat.adj]
  infer_instance

中文:
实例 :
  签名: 是同构 (HoCat.adj (C := C)).counit
  定义体: by
  dsimp [HoCat.adj]
  infer_instance

Depends on / 依赖: HoCat.adj, counit, infer_instance
-/
instance : IsIso (HoCat.adj (C := C)).counit := by
  dsimp [HoCat.adj]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Full
  body: HoCat.adj.fullyFaithfulROfIsIsoCounit.full

中文:
实例 :
  签名: (BifibrantObject.HoCat.ιCofibrantObject (C := C)).满
  定义体: HoCat.adj.fullyFaithfulROfIsIsoCounit.full
-/
instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Full :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Faithful
  body: HoCat.adj.fullyFaithfulROfIsIsoCounit.faithful

中文:
实例 :
  签名: (BifibrantObject.HoCat.ιCofibrantObject (C := C)).忠实
  定义体: HoCat.adj.fullyFaithfulROfIsIsoCounit.faithful

Depends on / 依赖: Faithful
-/
instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Faithful :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.faithful

instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adj.unit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  dsimp [HoCat.adj]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HoCat.bifibrantResolution.IsLocalization (weakEquivalences (HoCat C))
  body: HoCat.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨Y, rfl⟩ := toHoCat_obj_surjective Y
    obtain ⟨f, rfl⟩ := toHoCat.map_surjective f
    rw [← weakEquivalence_iff]; rw [weakEquivalence_toHoCat_map_iff] at hf
    rw [HoCat.bifib

中文:
实例 :
  签名: HoCat.bifibrantResolution.是Localization (weakEquivalences (HoCat C))
  定义体: HoCat.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨Y, rfl⟩ := toHoCat_obj_surjective Y
    obtain ⟨f, rfl⟩ := toHoCat.map_surjective f
    rw [← weakEquivalence_iff]; rw [weakEquivalence_toHoCat_map_iff] at hf
    rw [HoCat.bifib

Depends on / 依赖: HoCat.adj.isLocalization_leftAdjoint, HoCat.bifibrantResolution_map, Localization, Localization.inverts, bifibrantResolution_map, infer_instance, inverts, isLocalization_leftAdjoint, map_surjective, toHoCat, toHoCat.map_surjective, toHoCat_obj_surjective, weakEquivalence_iff, weakEquivalence_toHoCat_map_iff, weakEquivalences
-/
instance : HoCat.bifibrantResolution.IsLocalization (weakEquivalences (HoCat C)) :=
  HoCat.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨Y, rfl⟩ := toHoCat_obj_surjective Y
    obtain ⟨f, rfl⟩ := toHoCat.map_surjective f
    rw [← weakEquivalence_iff]; rw [weakEquivalence_toHoCat_map_iff] at hf
    rw [HoCat.bifibrantResolution_map]
    apply Localization.inverts _ (weakEquivalences _)
    rw [← weakEquivalence_iff]
    infer_instance) (fun X => by
    rw [← weakEquivalence_iff]
    dsimp
    infer_instance)

end CofibrantObject

namespace BifibrantObject

variable (C) in
/--
Definition of `localizerMorphism` / `localizerMorphism` 的定义

English:
definition localizerMorphism
  signature: :
  body: ι
  map := by rfl

中文:
定义 localizerMorphism
  签名: :
  定义体: ι
  map := by rfl
-/
def localizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C)) (weakEquivalences C) where
  functor := ι
  map := by rfl

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ CofibrantObject C`, as a localizer morphism. -/
@[simps]
/--
Definition of `ιCofibrantObjectLocalizerMorphism` / `ιCofibrantObjectLocalizerMorphism` 的定义

English:
definition ιCofibrantObjectLocalizerMorphism
  signature: :
  body: ιCofibrantObject
  map _ _ _ h := h

中文:
定义 ιCofibrantObjectLocalizerMorphism
  签名: :
  定义体: ιCofibrantObject
  map _ _ _ h := h
-/
def ιCofibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (CofibrantObject C)) where
  functor := ιCofibrantObject
  map _ _ _ h := h

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ FibrantObject C`, as a localizer morphism. -/
@[simps]
/--
Definition of `ιFibrantObjectLocalizerMorphism` / `ιFibrantObjectLocalizerMorphism` 的定义

English:
definition ιFibrantObjectLocalizerMorphism
  signature: :
  body: ιFibrantObject
  map _ _ _ h := h

中文:
定义 ιFibrantObjectLocalizerMorphism
  签名: :
  定义体: ιFibrantObject
  map _ _ _ h := h
-/
def ιFibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (FibrantObject C)) where
  functor := ιFibrantObject
  map _ _ _ h := h

open Functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence
  body: let : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toHoCat
      (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toHoCatCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso Cof

中文:
实例 :
  签名: (ιCofibrantObjectLocalizerMorphism C).是LocalizedEquivalence
  定义体: let : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toHoCat
      (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toHoCatCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso Cof

Depends on / 依赖: BifibrantObject, BifibrantObject.toHoCat, CatCommSq, CofibrantObject, CofibrantObject.HoCat.adj.counit, CofibrantObject.HoCat.bifibrantResolution, CofibrantObject.symm, CofibrantObject.toHoCat, IsLocalizedEquivalence, LocalizerMorphism, LocalizerMorphism.IsLocalizedEquivalence.mk, associator, bifibrantResolution, counit, functor, isoWhiskerLeft, isoWhiskerRight, toHoCat
-/
instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toHoCat
      (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toHoCatCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso CofibrantObject.HoCat.adj.counit)⟩
  LocalizerMorphism.IsLocalizedEquivalence.mk'
    (ιCofibrantObjectLocalizerMorphism C) BifibrantObject.toHoCat
    (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _)

instance {D : Type*} [Category D] (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιCofibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιCofibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (localizerMorphism C).IsLocalizedEquivalence
  body: inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence

中文:
实例 :
  签名: (localizerMorphism C).是LocalizedEquivalence
  定义体: inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence

Depends on / 依赖: CofibrantObject, CofibrantObject.localizerMorphism, IsLocalizedEquivalence, localizerMorphism
-/
instance : (localizerMorphism C).IsLocalizedEquivalence :=
  inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (BifibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ιFibrantObjectLocalizerMorphism C).IsLocalizedEquivalence
  body: let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_

中文:
实例 :
  签名: (ιFibrantObjectLocalizerMorphism C).是LocalizedEquivalence
  定义体: let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_

Depends on / 依赖: FibrantObject, IsLocalization, IsLocalizedEquivalence, LocalizerMorphism, LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization, functor, of_isLocalization_of_isLocalization, weakEquivalences
-/
instance : (ιFibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ L

instance {D : Type*} [Category D] (L : FibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιFibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)

end BifibrantObject

/--
lemma `locallySmall_of_isLocalization` / 引理 `locallySmall_of_isLocalization`

English:
lemma locallySmall_of_isLocalization
  statement: {D : Type*} [Category* D]
  proof: locallySmall_of_faithful ((BifibrantObject.localizerMorphism C).localizedFunctor
    BifibrantObject.toHoCat L).inv

中文:
引理 locallySmall_of_isLocalization
  结论: {D : 类型} [范畴* D]
  证明: locallySmall_of_faithful ((BifibrantObject.localizerMorphism C).localizedFunctor
    BifibrantObject.toHoCat L).inv

Depends on / 依赖: BifibrantObject, BifibrantObject.localizerMorphism, BifibrantObject.toHoCat, localizedFunctor, localizerMorphism, locallySmall_of_faithful, toHoCat
-/
lemma locallySmall_of_isLocalization {D : Type*} [Category* D]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)] [LocallySmall.{w} C] :
    LocallySmall.{w} D :=
  locallySmall_of_faithful ((BifibrantObject.localizerMorphism C).localizedFunctor
    BifibrantObject.toHoCat L).inv

end HomotopicalAlgebra
