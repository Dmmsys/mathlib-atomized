/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback

/-!
# Leibniz constructions associated to monoidal categories.

In a monoidal category with pushouts, the pushout-product is the Leibniz functor associated to the
tensor product. This is the bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y`
to the canonical map from the pushout of `f ◁ X` and `A ▷ g` to `B ⊗ Y`, induced by the following
diagram:
```
  A ⊗ X --> B ⊗ X
     | |
     v v
  A ⊗ Y --> B ⊗ Y
```

In a monoidal closed category with pullbacks, the pullback-hom is the the Leibniz functor associated
to the internal hom. This is the bifunctor of arrow categories that sends `f : A ⟶ B` and
`g : X ⟶ Y` to the canonical map from `B ⟹ X` to the pullback of
`(ihom A).map g : A ⟹ X ⟶ A ⟹ Y` and `(pre f).app Y : B ⟹ Y ⟶ A ⟹ Y`, induced by the
following diagram:
```
  B ⟹ X --> A ⟹ X
     | |
     v v
  B ⟹ Y --> A ⟹ Y
```

In `Mathlib.CategoryTheory.Monoidal.Arrow`, these constructions are used to define a
monoidal (closed) structure on arrow categories.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits MonoidalCategory CategoryTheory.Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

attribute [local simp] PushoutObjObj.ι ofHasPushout_pt ofHasPushout_inl ofHasPushout_inr
  PullbackObjObj.ofHasPullback_π

namespace MonoidalCategory

namespace Arrow

/-- The Leibniz functor associated to the tensor product on a monoidal category. This is the
bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y` to the canonical map from the
pushout of `f ◁ X` and `A ▷ g` to `B ⊗ Y`, induced by the following diagram:
```
  A ⊗ X --> B ⊗ X
     | |
     v v
  A ⊗ Y --> B ⊗ Y
```
-/
noncomputable
/--
Definition of `pushoutProduct` / `pushoutProduct` 的定义

English:
abbreviation pushoutProduct
  signature: [HasPushouts C] [MonoidalCategory C]
  body: (curriedTensor C).leibnizPushout

中文:
缩写 pushoutProduct
  签名: [HasPushouts C] [MonoidalCategory C]
  定义体: (curriedTensor C).leibnizPushout

Depends on / 依赖: curriedTensor, infer_instance, leibnizPushout, ofMkLEMk
-/
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] :
    Arrow C ⥤ Arrow C ⥤ Arrow C := (curriedTensor C).leibnizPushout

/-- Notation for the pushout-product of morphisms. -/
notation3 f " □ " g:10 => (pushoutProduct.obj f).obj g

/-- The Leibniz functor associated to the internal hom on a monoidal closed category. This is the
bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y` to the canonical map from
`B ⟹ X` to the pullback of `(ihom A).map g : A ⟹ X ⟶ A ⟹ Y` and
`(pre f).app Y : B ⟹ Y ⟶ A ⟹ Y`, induced by the following diagram:
```
  B ⟹ X --> A ⟹ X
     | |
     v v
  B ⟹ Y --> A ⟹ Y
```
-/
noncomputable
/--
Definition of `pullbackHom` / `pullbackHom` 的定义

English:
abbreviation pullbackHom
  signature: [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C]
  body: MonoidalClosed.internalHom.leibnizPullback

中文:
缩写 pullbackHom
  签名: [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C]
  定义体: MonoidalClosed.internalHom.leibnizPullback

Depends on / 依赖: MonoidalClosed, MonoidalClosed.internalHom.leibnizPullback, internalHom, leibnizPullback
-/
abbrev pullbackHom [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C] :
    (Arrow C)ᵒᵖ ⥤ Arrow C ⥤ Arrow C := MonoidalClosed.internalHom.leibnizPullback

/-- Notation for the pullback-hom of morphisms. -/
notation3 f " ⋔ " g:10 => (pullbackHom.obj f).obj g

namespace PushoutProduct

section

variable [HasPushouts C]

section Monoidal

variable [MonoidalCategory C] (X₁ X₂ X₃ : Arrow C) {W : C}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Left-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `W ◁ X₁` and `X₂`. -/
@[simps!]
noncomputable
/--
Definition of `whiskerLeftIso` / `whiskerLeftIso` 的定义

English:
definition whiskerLeftIso
  body: Arrow.isoMk
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
      (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_rig

中文:
定义 whiskerLeftIso
  定义体: Arrow.isoMk
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
      (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_rig

Depends on / 依赖: Arrow.isoMk, HasColimit, HasColimit.isoOfNatIso, IsPushout, IsPushout.of_hasPushout, associator_inv_naturality_middle, associator_inv_naturality_right, hom_ext, isoOfNatIso, isoPushout, map_isPushout, of_hasPushout, spanExt, tensorLeft, whiskerLeft_comp_assoc
-/
def whiskerLeftIso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorLeft W)] :
    Arrow.mk (W ◁ (X₁ □ X₂).hom) ≅ (W ◁ X₁.hom) □ X₂ :=
  Arrow.isoMk
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
      (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_right W _ _).symm))
    (α_ W _ _).symm
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).hom_ext
        (by simp [← whiskerLeft_comp_assoc]) (by simp [← whiskerLeft_comp_assoc]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `X₁` and `X₂ ▷ W`. -/
@[simps!]
noncomputable
/--
Definition of `whiskerRightIso` / `whiskerRightIso` 的定义

English:
definition whiskerRightIso
  body: Arrow.isoMk
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ _ _ W) (α_ _ _ W) (α_ _ _ W)
      (associator_naturality_left _ _ W).symm (associator_naturality_middle _ _ W).symm))
    (α

中文:
定义 whiskerRightIso
  定义体: Arrow.isoMk
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ _ _ W) (α_ _ _ W) (α_ _ _ W)
      (associator_naturality_left _ _ W).symm (associator_naturality_middle _ _ W).symm))
    (α

Depends on / 依赖: Arrow.isoMk, HasColimit, HasColimit.isoOfNatIso, IsPushout, IsPushout.of_hasPushout, associator_naturality_left, associator_naturality_middle, comp_whiskerRight_assoc, hom_ext, isoOfNatIso, isoPushout, map_isPushout, of_hasPushout, spanExt, tensorRight
-/
def whiskerRightIso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight W)] :
    Arrow.mk ((X₁ □ X₂).hom ▷ W) ≅ X₁ □ (X₂.hom ▷ W) :=
  Arrow.isoMk
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ _ _ W) (α_ _ _ W) (α_ _ _ W)
      (associator_naturality_left _ _ W).symm (associator_naturality_middle _ _ W).symm))
    (α_ _ _ W)
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).hom_ext
      (by simp [← comp_whiskerRight_assoc]) (by simp [← comp_whiskerRight_assoc]))

-- helper instance for `PushoutProduct.associator`
local instance {F : C ⥤ C}
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) F] :
    PreservesColimit (span (((curriedTensor C).map X₁.hom).app X₂.left)
      (((curriedTensor C).obj X₁.left).map X₂.hom)) F := by
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pushout-product is associative: `(X₁ □ X₂) □ X₃ ≅ X₁ □ X₂ □ X₃`. -/
@[simps!]
noncomputable
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  body: by
  refine Arrow.isoMk ?_ (α_ _ _ _) ?_
  · refine Iso.mk ?_ ?_ ?_ ?_
    · exact pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRightIso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [Limi

中文:
定义 associator
  定义体: by
  refine Arrow.isoMk ?_ (α_ _ _ _) ?_
  · refine Iso.mk ?_ ?_ ?_ ?_
    · exact pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRightIso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [Limi

Depends on / 依赖: Arrow.isoMk, IsPushout, IsPushout.of_hasPushout, Iso.mk, Limits, Limits.pushout.associator_naturality_left_condition, Limits.pushout.whiskerLeft_condition_assoc, associator_naturality_left_condition, comp_whiskerRight_assoc, hom.left, hom_ext, map_isPushout, of_hasPushout, pushout, pushout.desc, pushout.inl, pushout.inr, tensorRight, whiskerLeft_condition_assoc, whiskerRightIso
-/
def associator
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.left)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.right)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.left)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.right)] :
    ((X₁ □ X₂) □ X₃) ≅ X₁ □ X₂ □ X₃ := by
  refine Arrow.isoMk ?_ (α_ _ _ _) ?_
  · refine Iso.mk ?_ ?_ ?_ ?_
    · exact pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRightIso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [Limits.pushout.associator_naturality_left_condition]))
        (((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [Limits.pushout.whiskerLeft_condition_assoc, ← whisker_exchange_assoc,
            ← comp_whiskerRight_assoc])
          (by simp [← whisker_exchange_assoc, Limits.pushout.associator_naturality_left_condition,
            ← comp_whiskerRight_assoc]))
    · exact pushout.desc ((whiskerLeftIso _ _).hom.left ≫
          pushout.desc (pushout.inl _ _) ((pushout.inl _ _ ▷ _) ≫ pushout.inr _ _)
          (by simp [Limits.pushout.associator_inv_naturality_right_condition]))
        ((α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _)
        (((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [whisker_exchange_assoc,
            Limits.pushout.associator_inv_naturality_right_condition, ← whiskerLeft_comp_assoc])
          (by simp [whisker_exchange_assoc, Limits.pushout.condition_whiskerRight_assoc,
            ← whiskerLeft_comp_assoc]))
    · apply pushout.hom_ext (by simp)
      apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · refine pushout.hom_ext ?_ (by simp)
      apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
  · apply pushout.hom_ext (by simp [← MonoidalCategory.whiskerLeft_comp])
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pushout-product is commutative: `X₁ □ X₂ ≅ X₂ □ X₁`. -/
@[simps!]
noncomputable
/--
Definition of `braiding` / `braiding` 的定义

English:
definition braiding
  signature: [BraidedCategory C] (X₁ X₂ : Arrow C)
  body: Arrow.isoMk (pushoutSymmetry _ _ ≪≫
    HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm)) (β_ _ _) (by cat_disch)

中文:
定义 braiding
  签名: [BraidedCategory C] (X₁ X₂ : Arrow C)
  定义体: Arrow.isoMk (pushoutSymmetry _ _ ≪≫
    HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm)) (β_ _ _) (by cat_disch)

Depends on / 依赖: Arrow.isoMk, BraidedCategory, BraidedCategory.braiding_naturality_left, BraidedCategory.braiding_naturality_right, HasColimit, HasColimit.isoOfNatIso, braiding_naturality_left, braiding_naturality_right, cat_disch, isoOfNatIso, pushoutSymmetry, spanExt
-/
def braiding [BraidedCategory C] (X₁ X₂ : Arrow C) : (X₁ □ X₂) ≅ X₂ □ X₁ :=
  Arrow.isoMk (pushoutSymmetry _ _ ≪≫
    HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm)) (β_ _ _) (by cat_disch)

end Monoidal

section CartesianMonoidalClosed

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

noncomputable section

set_option backward.defeqAttrib.useBackward true in
/-- The arrow isomorphism `X □ (∅ ⟶ W) ≅ X ▷ W` in a CCC with pushouts and an
initial object. -/
@[simps!]
/--
Definition of `isInitialIso` / `isInitialIso` 的定义

English:
definition isInitialIso
  signature: (X : Arrow C) {I : C} (i : IsInitial I) {W : C}
  body: haveI : IsIso (X.hom ▷ I) :=
    isIso_of_isInitial (i.ofIso (zeroMul i).symm) (i.ofIso (zeroMul i).symm) _
  haveI : IsPushout (X.hom ▷ I) (_ ◁ i.to W) ((i.ofIso (zeroMul i).symm).to _) (𝟙 _) :=
    .of_horiz_isIso (sq := ⟨(i.ofIso (zeroMul i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.s

中文:
定义 isInitialIso
  签名: (X : Arrow C) {I : C} (i : IsInitial I) {W : C}
  定义体: haveI : IsIso (X.hom ▷ I) :=
    isIso_of_isInitial (i.ofIso (zeroMul i).symm) (i.ofIso (zeroMul i).symm) _
  haveI : IsPushout (X.hom ▷ I) (_ ◁ i.to W) ((i.ofIso (zeroMul i).symm).to _) (𝟙 _) :=
    .of_horiz_isIso (sq := ⟨(i.ofIso (zeroMul i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.s

Depends on / 依赖: Arrow.isoMk, IsPushout, Iso.refl, X.hom, hom_ext, i.ofIso, i.to, inr_desc, isIso_of_isInitial, isoPushout, of_horiz_isIso, pushout, pushout.hom_ext, pushout.inr_desc, this.isoPushout.symm, zeroMul
-/
def isInitialIso (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (X □ i.to W) ≅ X.hom ▷ W :=
  haveI : IsIso (X.hom ▷ I) :=
    isIso_of_isInitial (i.ofIso (zeroMul i).symm) (i.ofIso (zeroMul i).symm) _
  haveI : IsPushout (X.hom ▷ I) (_ ◁ i.to W) ((i.ofIso (zeroMul i).symm).to _) (𝟙 _) :=
    .of_horiz_isIso (sq := ⟨(i.ofIso (zeroMul i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.symm (Iso.refl _)
    (pushout.hom_ext ((i.ofIso (zeroMul i).symm).hom_ext ..) (by simp [pushout.inr_desc]))

set_option backward.defeqAttrib.useBackward true in
/-- The arrow isomorphism `(∅ ⟶ W) □ X ≅ W ◁ X` in a braided CCC with pushouts and
an initial object. -/
@[simps!]
/--
Definition of `isInitialIso'` / `isInitialIso'` 的定义

English:
definition isInitialIso'
  signature: [BraidedCategory C] (X : Arrow C) {I : C} (i : IsInitial I) {W : C}
  body: haveI : IsIso (I ◁ X.hom) :=
    isIso_of_isInitial (i.ofIso (mulZero i).symm) (i.ofIso (mulZero i).symm) _
  haveI : IsPushout (i.to W ▷ _) (I ◁ X.hom) (𝟙 _) ((i.ofIso (mulZero i).symm).to _) :=
    .of_vert_isIso (sq := ⟨(i.ofIso (mulZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.sy

中文:
定义 isInitialIso'
  签名: [BraidedCategory C] (X : Arrow C) {I : C} (i : IsInitial I) {W : C}
  定义体: haveI : IsIso (I ◁ X.hom) :=
    isIso_of_isInitial (i.ofIso (mulZero i).symm) (i.ofIso (mulZero i).symm) _
  haveI : IsPushout (i.to W ▷ _) (I ◁ X.hom) (𝟙 _) ((i.ofIso (mulZero i).symm).to _) :=
    .of_vert_isIso (sq := ⟨(i.ofIso (mulZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.sy

Depends on / 依赖: Arrow.isoMk, IsPushout, Iso.refl, X.hom, hom_ext, i.ofIso, i.to, inl_desc, isIso_of_isInitial, isoPushout, mulZero, of_vert_isIso, pushout, pushout.hom_ext, pushout.inl_desc, this.isoPushout.symm
-/
def isInitialIso' [BraidedCategory C] (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (i.to W □ X) ≅ Arrow.mk (W ◁ X.hom) :=
  haveI : IsIso (I ◁ X.hom) :=
    isIso_of_isInitial (i.ofIso (mulZero i).symm) (i.ofIso (mulZero i).symm) _
  haveI : IsPushout (i.to W ▷ _) (I ◁ X.hom) (𝟙 _) ((i.ofIso (mulZero i).symm).to _) :=
    .of_vert_isIso (sq := ⟨(i.ofIso (mulZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.symm (Iso.refl _)
    (pushout.hom_ext (by simp [pushout.inl_desc]) ((i.ofIso (mulZero i).symm).hom_ext _ _))

/-- The arrow isomorphism `X □ (∅ ⟶ ⋆) ≅ X` in a CCC with pushouts, an initial object, and a
terminal object. -/
@[simps!]
/--
Definition of `isInitialIsTerminalIso` / `isInitialIsTerminalIso` 的定义

English:
definition isInitialIsTerminalIso
  signature: (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T)
  body: (isInitialIso X i) ≪≫ Arrow.isoMk' _ _
    (MonoidalCategory.whiskerLeftIso X.left
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.left)
    (MonoidalCategory.whiskerLeftIso X.right
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.right)
 

中文:
定义 isInitialIsTerminalIso
  签名: (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T)
  定义体: (isInitialIso X i) ≪≫ Arrow.isoMk' _ _
    (MonoidalCategory.whiskerLeftIso X.left
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.left)
    (MonoidalCategory.whiskerLeftIso X.right
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.right)
 

Depends on / 依赖: Arrow.isoMk, CartesianMonoidalCategory, CartesianMonoidalCategory.isTerminalTensorUnit, MonoidalCategory, MonoidalCategory.whiskerLeftIso, X.left, X.right, isInitialIso, isTerminalTensorUnit, t.uniqueUpToIso, uniqueUpToIso, whiskerLeftIso, whisker_exchange_assoc
-/
def isInitialIsTerminalIso (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ i.to T) ≅ X :=
  (isInitialIso X i) ≪≫ Arrow.isoMk' _ _
    (MonoidalCategory.whiskerLeftIso X.left
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.left)
    (MonoidalCategory.whiskerLeftIso X.right
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.right)
    (by simp [← whisker_exchange_assoc])

/-- The arrow isomorphism `X □ (∅ ⟶ ⋆) ≅ X` in a CCC with pushouts, an initial object, and a
terminal object. -/
@[simps!]
/--
Definition of `isInitialIsTerminalIso'` / `isInitialIsTerminalIso'` 的定义

English:
definition isInitialIsTerminalIso'
  signature: (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T)
  body: (mapIso _ (Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (i.hom_ext _ _))) ≪≫
    (isInitialIsTerminalIso X i t)

中文:
定义 isInitialIsTerminalIso'
  签名: (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T)
  定义体: (mapIso _ (Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (i.hom_ext _ _))) ≪≫
    (isInitialIsTerminalIso X i t)

Depends on / 依赖: Arrow.isoMk, Iso.refl, hom_ext, i.hom_ext, isInitialIsTerminalIso, mapIso
-/
def isInitialIsTerminalIso' (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ t.from I) ≅ X :=
  (mapIso _ (Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (i.hom_ext _ _))) ≪≫
    (isInitialIsTerminalIso X i t)

end

variable [HasInitial C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a CCC with pushouts and an initial object, then `X □ (⊥_ C ⟶ 𝟙_ C) ≅ X`. -/
@[simp]
noncomputable
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (X : Arrow C)
  body: by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm)

中文:
定义 rightUnitor
  签名: (X : Arrow C)
  定义体: by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm)

Depends on / 依赖: Arrow.isoMk, Iso.mk, X.left, X.right, hom_ext, initialIsInitial, initialIsInitial.ofIso, pushout, pushout.desc, pushout.hom_ext, pushout.inr, zeroMul
-/
def rightUnitor (X : Arrow C) :
    (X □ initial.to (𝟙_ C)) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · refine pushout.hom_ext ?_ (by simp)
      apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · simp
  · refine pushout.hom_ext ?_ (by simp)
    apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext

/-- If `C` is a braided CCC with pushouts and an initial object, then `(⊥_ C ⟶ 𝟙_ C) □ X ≅ X`. -/
@[simp]
noncomputable
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: [BraidedCategory C]
  body: braiding _ _ ≪≫ rightUnitor _

中文:
定义 leftUnitor
  签名: [BraidedCategory C]
  定义体: braiding _ _ ≪≫ rightUnitor _

Depends on / 依赖: braiding, rightUnitor
-/
def leftUnitor [BraidedCategory C]
    (X : Arrow C) : (initial.to (𝟙_ C) □ X) ≅ X :=
  braiding _ _ ≪≫ rightUnitor _

end CartesianMonoidalClosed

end

end PushoutProduct

namespace PullbackHom

variable [HasPullbacks C]

noncomputable section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The arrow isomorphism `(f : A ⟶ B) ⋔ (W ⟶ ⋆) ≅ (B ⟹ W ⟶ A ⟹ W)` in a monoidal closed
category with pullbacks and a terminal object. -/
@[simps!]
/--
Definition of `isTerminalIso` / `isTerminalIso` 的定义

English:
definition isTerminalIso
  signature: [MonoidalCategory C] [MonoidalClosed C]
  body: haveI : IsIso ((MonoidalClosed.pre X.hom).app T) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj (ihom _) _ t)
      (IsTerminal.isTerminalObj (ihom _) _ t) _
  haveI : IsPullback (𝟙 _) ((IsTerminal.isTerminalObj (ihom _) _ t).from _)
      ((ihom X.left).map (t.from W)) ((MonoidalClosed.pre X.

中文:
定义 isTerminalIso
  签名: [MonoidalCategory C] [MonoidalClosed C]
  定义体: haveI : IsIso ((MonoidalClosed.pre X.hom).app T) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj (ihom _) _ t)
      (IsTerminal.isTerminalObj (ihom _) _ t) _
  haveI : IsPullback (𝟙 _) ((IsTerminal.isTerminalObj (ihom _) _ t).from _)
      ((ihom X.left).map (t.from W)) ((MonoidalClosed.pre X.

Depends on / 依赖: Arrow.isoMk, IsPullback, IsTerminal, IsTerminal.isTerminalObj, Iso.refl, MonoidalClosed, MonoidalClosed.pre, X.hom, X.left, eq_comp_inv, hom_ext, isIso_of_isTerminal, isTerminalObj, isoPullback, of_horiz_isIso, pullback, pullback.hom_ext, t.from, this.isoPullback, this.isoPullback.symm
-/
def isTerminalIso [MonoidalCategory C] [MonoidalClosed C]
    (X : Arrow C) {T : C} (t : IsTerminal T) {W : C} :
    ((Opposite.op X) ⋔ Arrow.mk (t.from W)) ≅ Arrow.mk ((MonoidalClosed.pre X.hom).app W) :=
  haveI : IsIso ((MonoidalClosed.pre X.hom).app T) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj (ihom _) _ t)
      (IsTerminal.isTerminalObj (ihom _) _ t) _
  haveI : IsPullback (𝟙 _) ((IsTerminal.isTerminalObj (ihom _) _ t).from _)
      ((ihom X.left).map (t.from W)) ((MonoidalClosed.pre X.hom).app T) :=
    .of_horiz_isIso (sq := ⟨(IsTerminal.isTerminalObj (ihom _) _ t).hom_ext ..⟩)
  Arrow.isoMk' _ _ (Iso.refl _) this.isoPullback.symm ((this.isoPullback).eq_comp_inv.2
    (pullback.hom_ext (by simp) ((IsTerminal.isTerminalObj (ihom _) _ t).hom_ext ..)))

open CartesianMonoidalCategory in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The arrow isomorphism `(∅ ⟶ W) ⋔ (f : A ⟶ B) ≅ (W ⟹ A ⟶ W ⟹ B)` in a braided CCC with
pullbacks and an initial object. -/
@[simps!]
/--
Definition of `isInitialIso` / `isInitialIso` 的定义

English:
definition isInitialIso
  signature: [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
  body: haveI : IsIso ((ihom I).map X.hom) :=
    isIso_of_isTerminal (isTerminalTensorUnit.ofIso (powZero i).symm)
      (isTerminalTensorUnit.ofIso (powZero i).symm) _
  haveI : IsPullback ((isTerminalTensorUnit.ofIso (powZero i).symm).from _) (𝟙 _)
      ((ihom I).map X.hom) ((MonoidalClosed.pre (i.to W)

中文:
定义 isInitialIso
  签名: [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
  定义体: haveI : IsIso ((ihom I).map X.hom) :=
    isIso_of_isTerminal (isTerminalTensorUnit.ofIso (powZero i).symm)
      (isTerminalTensorUnit.ofIso (powZero i).symm) _
  haveI : IsPullback ((isTerminalTensorUnit.ofIso (powZero i).symm).from _) (𝟙 _)
      ((ihom I).map X.hom) ((MonoidalClosed.pre (i.to W)

Depends on / 依赖: Arrow.isoMk, IsPullback, Iso.refl, MonoidalClosed, MonoidalClosed.pre, X.hom, X.right, eq_comp_inv, hom_ext, i.to, isIso_of_isTerminal, isTerminalTe, isTerminalTensorUnit, isTerminalTensorUnit.ofIso, isoPullback, of_vert_isIso, powZero, pullback, pullback.hom_ext, this.isoPullback
-/
def isInitialIso [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (Opposite.op (Arrow.mk (i.to W)) ⋔ X) ≅ Arrow.mk ((ihom W).map X.hom) :=
  haveI : IsIso ((ihom I).map X.hom) :=
    isIso_of_isTerminal (isTerminalTensorUnit.ofIso (powZero i).symm)
      (isTerminalTensorUnit.ofIso (powZero i).symm) _
  haveI : IsPullback ((isTerminalTensorUnit.ofIso (powZero i).symm).from _) (𝟙 _)
      ((ihom I).map X.hom) ((MonoidalClosed.pre (i.to W)).app X.right) :=
    .of_vert_isIso (sq := ⟨(isTerminalTensorUnit.ofIso (powZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ (Iso.refl _) this.isoPullback.symm ((this.isoPullback).eq_comp_inv.2
    (pullback.hom_ext ((isTerminalTensorUnit.ofIso (powZero i).symm).hom_ext ..) (by simp)))

end

end PullbackHom

end CategoryTheory.MonoidalCategory.Arrow
