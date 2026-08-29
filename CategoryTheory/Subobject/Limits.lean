/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Specific subobjects

We define `equalizerSubobject`, `kernelSubobject` and `imageSubobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: an iff characterisation of `(imageSubobject f).Factors h`

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Pullback

variable {W : C} (f : X ⟶ Y) [HasPullbacks C]

/--
theorem `pullback_factors` / 定理 `pullback_factors`

English:
theorem pullback_factors
  given: (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f))
  proof: let h' := Subobject.factorThru _ _ hF
  let w := Subobject.factorThru_arrow _ _ hF
  (factors_iff _ _).mpr
    ⟨(Subobject.isPullback f y).lift h' h w,
      (Subobject.isPullback f y).lift_snd h' h w⟩

中文:
定理 pullback_factors
  条件: (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f))
  证明: let h' := Subobject.factorThru _ _ hF
  let w := Subobject.factorThru_arrow _ _ hF
  (factors_iff _ _).mpr
    ⟨(Subobject.isPullback f y).lift h' h w,
      (Subobject.isPullback f y).lift_snd h' h w⟩

Depends on / 依赖: Subobject, Subobject.factorThru, Subobject.factorThru_arrow, Subobject.isPullback, factorThru, factorThru_arrow, factors_iff, isPullback, lift_snd
-/
theorem pullback_factors (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) :
    Subobject.Factors ((Subobject.pullback f).obj y) h :=
  let h' := Subobject.factorThru _ _ hF
  let w := Subobject.factorThru_arrow _ _ hF
  (factors_iff _ _).mpr
    ⟨(Subobject.isPullback f y).lift h' h w,
      (Subobject.isPullback f y).lift_snd h' h w⟩

/--
theorem `pullback_factors_iff` / 定理 `pullback_factors_iff`

English:
theorem pullback_factors_iff
  given: (y : Subobject Y) (h : W ⟶ X)
  proof: by
  refine ⟨fun hf => ?_, fun hF => pullback_factors f y h hF⟩
  rw [factors_iff]
  use Subobject.factorThru _ _ hf ≫ Subobject.pullbackπ f y
  simp [(Subobject.isPullback f y).w]

中文:
定理 pullback_factors_iff
  条件: (y : Subobject Y) (h : W ⟶ X)
  证明: by
  refine ⟨fun hf => ?_, fun hF => pullback_factors f y h hF⟩
  rw [factors_iff]
  use Subobject.factorThru _ _ hf ≫ Subobject.pullbackπ f y
  simp [(Subobject.isPullback f y).w]

Depends on / 依赖: Subobject, Subobject.factorThru, Subobject.isPullback, Subobject.pullback, factorThru, factors_iff, isPullback, pullback_factors
-/
theorem pullback_factors_iff (y : Subobject Y) (h : W ⟶ X) :
    Subobject.Factors ((Subobject.pullback f).obj y) h ↔ y.Factors (h ≫ f) := by
  refine ⟨fun hf => ?_, fun hF => pullback_factors f y h hF⟩
  rw [factors_iff]
  use Subobject.factorThru _ _ hf ≫ Subobject.pullbackπ f y
  simp [(Subobject.isPullback f y).w]

end Pullback

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

/--
Definition of `equalizerSubobject` / `equalizerSubobject` 的定义

English:
abbreviation equalizerSubobject
  signature: : Subobject X
  body: Subobject.mk (equalizer.ι f g)

中文:
缩写 equalizerSubobject
  签名: : Subobject X
  定义体: Subobject.mk (equalizer.ι f g)

Depends on / 依赖: Subobject, Subobject.mk, equalizer
-/
abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)

/--
Definition of `equalizerSubobjectIso` / `equalizerSubobjectIso` 的定义

English:
definition equalizerSubobjectIso
  signature: : (equalizerSubobject f g : C) ≅ equalizer f g
  body: Subobject.underlyingIso (equalizer.ι f g)

@[reassoc (attr := simp)]

中文:
定义 equalizerSubobjectIso
  签名: : (equalizerSubobject f g : C) ≅ equalizer f g
  定义体: Subobject.underlyingIso (equalizer.ι f g)

@[reassoc (attr := simp)]

Depends on / 依赖: Subobject, Subobject.underlyingIso, equalizer, underlyingIso
-/
def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)

@[reassoc (attr := simp)]
/--
theorem `equalizerSubobject_arrow` / 定理 `equalizerSubobject_arrow`

English:
theorem equalizerSubobject_arrow
  proof: by
  simp [equalizerSubobjectIso]

@[reassoc (attr := simp)]

中文:
定理 equalizerSubobject_arrow
  证明: by
  simp [equalizerSubobjectIso]

@[reassoc (attr := simp)]

Depends on / 依赖: equalizerSubobjectIso
-/
theorem equalizerSubobject_arrow :
    (equalizerSubobjectIso f g).hom ≫ equalizer.ι f g = (equalizerSubobject f g).arrow := by
  simp [equalizerSubobjectIso]

@[reassoc (attr := simp)]
/--
theorem `equalizerSubobject_arrow'` / 定理 `equalizerSubobject_arrow'`

English:
theorem equalizerSubobject_arrow'
  proof: by
  simp [equalizerSubobjectIso]

@[reassoc]

中文:
定理 equalizerSubobject_arrow'
  证明: by
  simp [equalizerSubobjectIso]

@[reassoc]

Depends on / 依赖: equalizerSubobjectIso
-/
theorem equalizerSubobject_arrow' :
    (equalizerSubobjectIso f g).inv ≫ (equalizerSubobject f g).arrow = equalizer.ι f g := by
  simp [equalizerSubobjectIso]

@[reassoc]
/--
theorem `equalizerSubobject_arrow_comp` / 定理 `equalizerSubobject_arrow_comp`

English:
theorem equalizerSubobject_arrow_comp
  proof: by
  rw [← equalizerSubobject_arrow]; rw [Category.assoc]; rw [Category.assoc]; rw [equalizer.condition]

@[simp]

中文:
定理 equalizerSubobject_arrow_comp
  证明: by
  rw [← equalizerSubobject_arrow]; rw [Category.assoc]; rw [Category.assoc]; rw [equalizer.condition]

@[simp]

Depends on / 依赖: Category, Category.assoc, condition, equalizer, equalizer.condition, equalizerSubobject_arrow
-/
theorem equalizerSubobject_arrow_comp :
    (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow ≫ g := by
  rw [← equalizerSubobject_arrow]; rw [Category.assoc]; rw [Category.assoc]; rw [equalizer.condition]

@[simp]
/--
theorem `equalizerSubobject_of_self` / 定理 `equalizerSubobject_of_self`

English:
theorem equalizerSubobject_of_self
  statement: equalizerSubobject f f = ⊤
  proof: by
  apply mk_eq_top_of_isIso

中文:
定理 equalizerSubobject_of_self
  结论: equalizerSubobject f f = ⊤
  证明: by
  apply mk_eq_top_of_isIso

Depends on / 依赖: mk_eq_top_of_isIso
-/
theorem equalizerSubobject_of_self : equalizerSubobject f f = ⊤ := by
  apply mk_eq_top_of_isIso

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equalizerSubobject_factors` / 定理 `equalizerSubobject_factors`

English:
theorem equalizerSubobject_factors
  given: {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g)
  proof: ⟨equalizer.lift h w, by simp⟩

中文:
定理 equalizerSubobject_factors
  条件: {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g)
  证明: ⟨equalizer.lift h w, by simp⟩

Depends on / 依赖: equalizer, equalizer.lift
-/
theorem equalizerSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
    (equalizerSubobject f g).Factors h :=
  ⟨equalizer.lift h w, by simp⟩

/--
theorem `equalizerSubobject_factors_iff` / 定理 `equalizerSubobject_factors_iff`

English:
theorem equalizerSubobject_factors_iff
  given: {W : C} (h : W ⟶ X)
  proof: ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [equalizerSubobject_arrow_comp]; rw [Category.assoc],
    equalizerSubobject_factors f g h⟩

@[simp]

中文:
定理 equalizerSubobject_factors_iff
  条件: {W : C} (h : W ⟶ X)
  证明: ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [equalizerSubobject_arrow_comp]; rw [Category.assoc],
    equalizerSubobject_factors f g h⟩

@[simp]

Depends on / 依赖: Category, Category.assoc, Subobject, Subobject.factorThru_arrow, equalizerSubobject_arrow_comp, equalizerSubobject_factors, factorThru_arrow
-/
theorem equalizerSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (equalizerSubobject f g).Factors h ↔ h ≫ f = h ≫ g :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [equalizerSubobject_arrow_comp]; rw [Category.assoc],
    equalizerSubobject_factors f g h⟩

@[simp]
/--
lemma `pullback_equalizer` / 引理 `pullback_equalizer`

English:
lemma pullback_equalizer
  given: {W : C} (h : W ⟶ X) [HasPullbacks C]
  proof: by
  refine skeletal _ ⟨iso_of_both_ways (homOfFactors ?_) (homOfFactors ?_)⟩
  · apply equalizerSubobject_factors
    have := (Subobject.isPullback h (equalizerSubobject f g)).w
    rw [← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w]; rw [← reassoc_of% (Subobject.isPullback h (eq

中文:
引理 pullback_equalizer
  条件: {W : C} (h : W ⟶ X) [HasPullbacks C]
  证明: by
  refine skeletal _ ⟨iso_of_both_ways (homOfFactors ?_) (homOfFactors ?_)⟩
  · apply equalizerSubobject_factors
    have := (Subobject.isPullback h (equalizerSubobject f g)).w
    rw [← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w]; rw [← reassoc_of% (Subobject.isPullback h (eq

Depends on / 依赖: Subobject, Subobject.isPullback, equalizerSubobject, equalizerSubobject_arrow_comp, equalizerSubobject_factors, homOfFactors, isPullback, iso_of_both_ways, pullback_factors, reassoc_of, skeletal
-/
lemma pullback_equalizer {W : C} (h : W ⟶ X) [HasPullbacks C] :
  (Subobject.pullback h).obj (equalizerSubobject f g) =
    equalizerSubobject (h ≫ f) (h ≫ g) := by
  refine skeletal _ ⟨iso_of_both_ways (homOfFactors ?_) (homOfFactors ?_)⟩
  · apply equalizerSubobject_factors
    have := (Subobject.isPullback h (equalizerSubobject f g)).w
    rw [← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w]; rw [← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w]; rw [equalizerSubobject_arrow_comp]
  · apply pullback_factors
    apply equalizerSubobject_factors
    rw [assoc]; rw [assoc]; rw [equalizerSubobject_arrow_comp]

end Equalizer

section Kernel

variable [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f]

/--
Definition of `kernelSubobject` / `kernelSubobject` 的定义

English:
abbreviation kernelSubobject
  signature: : Subobject X
  body: Subobject.mk (kernel.ι f)

中文:
缩写 kernelSubobject
  签名: : Subobject X
  定义体: Subobject.mk (kernel.ι f)

Depends on / 依赖: Subobject, Subobject.mk, kernel
-/
abbrev kernelSubobject : Subobject X :=
  Subobject.mk (kernel.ι f)

/--
Definition of `kernelSubobjectIso` / `kernelSubobjectIso` 的定义

English:
definition kernelSubobjectIso
  signature: : (kernelSubobject f : C) ≅ kernel f
  body: Subobject.underlyingIso (kernel.ι f)

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定义 kernelSubobjectIso
  签名: : (kernelSubobject f : C) ≅ kernel f
  定义体: Subobject.underlyingIso (kernel.ι f)

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: Subobject, Subobject.underlyingIso, kernel, underlyingIso
-/
def kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f :=
  Subobject.underlyingIso (kernel.ι f)

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `kernelSubobject_arrow` / 定理 `kernelSubobject_arrow`

English:
theorem kernelSubobject_arrow
  proof: by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 kernelSubobject_arrow
  证明: by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: kernelSubobjectIso
-/
theorem kernelSubobject_arrow :
    (kernelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `kernelSubobject_arrow'` / 定理 `kernelSubobject_arrow'`

English:
theorem kernelSubobject_arrow'
  proof: by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 kernelSubobject_arrow'
  证明: by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: kernelSubobjectIso
-/
theorem kernelSubobject_arrow' :
    (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `kernelSubobject_arrow_comp` / 定理 `kernelSubobject_arrow_comp`

English:
theorem kernelSubobject_arrow_comp
  statement: (kernelSubobject f).arrow ≫ f = 0
  proof: by
  rw [← kernelSubobject_arrow]
  simp only [Category.assoc, kernel.condition, comp_zero]

中文:
定理 kernelSubobject_arrow_comp
  结论: (kernelSubobject f).arrow ≫ f = 0
  证明: by
  rw [← kernelSubobject_arrow]
  simp only [Category.assoc, kernel.condition, comp_zero]

Depends on / 依赖: Category, Category.assoc, comp_zero, condition, kernel, kernel.condition, kernelSubobject_arrow
-/
theorem kernelSubobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0 := by
  rw [← kernelSubobject_arrow]
  simp only [Category.assoc, kernel.condition, comp_zero]

/--
theorem `kernelSubobject_factors` / 定理 `kernelSubobject_factors`

English:
theorem kernelSubobject_factors
  given: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  proof: ⟨kernel.lift _ h w, by simp⟩

中文:
定理 kernelSubobject_factors
  条件: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  证明: ⟨kernel.lift _ h w, by simp⟩

Depends on / 依赖: kernel, kernel.lift
-/
theorem kernelSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    (kernelSubobject f).Factors h :=
  ⟨kernel.lift _ h w, by simp⟩

/--
theorem `kernelSubobject_factors_iff` / 定理 `kernelSubobject_factors_iff`

English:
theorem kernelSubobject_factors_iff
  given: {W : C} (h : W ⟶ X)
  proof: ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero],
    kernelSubobject_factors f h⟩

中文:
定理 kernelSubobject_factors_iff
  条件: {W : C} (h : W ⟶ X)
  证明: ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero],
    kernelSubobject_factors f h⟩

Depends on / 依赖: Category, Category.assoc, Subobject, Subobject.factorThru_arrow, comp_zero, factorThru_arrow, kernelSubobject_arrow_comp, kernelSubobject_factors
-/
theorem kernelSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (kernelSubobject f).Factors h ↔ h ≫ f = 0 :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w]; rw [Category.assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero],
    kernelSubobject_factors f h⟩

/--
Definition of `factorThruKernelSubobject` / `factorThruKernelSubobject` 的定义

English:
definition factorThruKernelSubobject
  signature: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  body: (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)

@[simp]

中文:
定义 factorThruKernelSubobject
  签名: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  定义体: (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)

@[simp]

Depends on / 依赖: factorThru, kernelSubobject, kernelSubobject_factors
-/
def factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernelSubobject f :=
  (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)

@[simp]
/--
theorem `factorThruKernelSubobject_comp_arrow` / 定理 `factorThruKernelSubobject_comp_arrow`

English:
theorem factorThruKernelSubobject_comp_arrow
  given: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  proof: by
  dsimp [factorThruKernelSubobject]
  simp

@[simp]

中文:
定理 factorThruKernelSubobject_comp_arrow
  条件: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  证明: by
  dsimp [factorThruKernelSubobject]
  simp

@[simp]

Depends on / 依赖: factorThruKernelSubobject
-/
theorem factorThruKernelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h := by
  dsimp [factorThruKernelSubobject]
  simp

@[simp]
/--
theorem `factorThruKernelSubobject_comp_kernelSubobjectIso` / 定理 `factorThruKernelSubobject_comp_kernelSubobjectIso`

English:
theorem factorThruKernelSubobject_comp_kernelSubobjectIso
  given: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  proof: (cancel_mono (kernel.ι f)).1 by simp

中文:
定理 factorThruKernelSubobject_comp_kernelSubobjectIso
  条件: {W : C} (h : W ⟶ X) (w : h ≫ f = 0)
  证明: (cancel_mono (kernel.ι f)).1 by simp

Depends on / 依赖: cancel_mono, kernel
-/
theorem factorThruKernelSubobject_comp_kernelSubobjectIso {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).hom = kernel.lift f h w :=
(cancel_mono (kernel.ι f)).1 by simp

section

variable {f} {X' Y' : C} {f' : X' ⟶ Y'} [HasKernel f']

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `kernelSubobjectMap` / `kernelSubobjectMap` 的定义

English:
definition kernelSubobjectMap
  signature: (sq : Arrow.mk f ⟶ Arrow.mk f')
  body: Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp))

#adaptation_note

中文:
定义 kernelSubobjectMap
  签名: (sq : Arrow.mk f ⟶ Arrow.mk f')
  定义体: Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp))

#adaptation_note

Depends on / 依赖: Subobject, Subobject.factorThru, factorThru, kernelSubobject, kernelSubobject_factors, sq.left
-/
def kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobject f : C) ⟶ (kernelSubobject f' : C) :=
  Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `kernelSubobjectMap_arrow` / 定理 `kernelSubobjectMap_arrow`

English:
theorem kernelSubobjectMap_arrow
  given: (sq : Arrow.mk f ⟶ Arrow.mk f')
  proof: by
  simp [kernelSubobjectMap]

中文:
定理 kernelSubobjectMap_arrow
  条件: (sq : Arrow.mk f ⟶ Arrow.mk f')
  证明: by
  simp [kernelSubobjectMap]

Depends on / 依赖: kernelSubobjectMap
-/
theorem kernelSubobjectMap_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernelSubobjectMap sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left := by
  simp [kernelSubobjectMap]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `kernelSubobjectMap_id` / 定理 `kernelSubobjectMap_id`

English:
theorem kernelSubobjectMap_id
  statement: kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _
  proof: by cat_disch

中文:
定理 kernelSubobjectMap_id
  结论: kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem kernelSubobjectMap_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `kernelSubobjectMap_comp` / 定理 `kernelSubobjectMap_comp`

English:
theorem kernelSubobjectMap_comp
  statement: {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
  proof: by
  cat_disch

中文:
定理 kernelSubobjectMap_comp
  结论: {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem kernelSubobjectMap_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
    (sq : Arrow.mk f ⟶ Arrow.mk f') (sq' : Arrow.mk f' ⟶ Arrow.mk f'') :
    kernelSubobjectMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq' := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
theorem `kernel_map_comp_kernelSubobjectIso_inv` / 定理 `kernel_map_comp_kernelSubobjectIso_inv`

English:
theorem kernel_map_comp_kernelSubobjectIso_inv
  given: (sq : Arrow.mk f ⟶ Arrow.mk f')
  proof: by cat_disch

@[reassoc]

中文:
定理 kernel_map_comp_kernelSubobjectIso_inv
  条件: (sq : Arrow.mk f ⟶ Arrow.mk f')
  证明: by cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem kernel_map_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernel.map f f' sq.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv =
      (kernelSubobjectIso _).inv ≫ kernelSubobjectMap sq := by cat_disch

@[reassoc]
/--
theorem `kernelSubobjectIso_comp_kernel_map` / 定理 `kernelSubobjectIso_comp_kernel_map`

English:
theorem kernelSubobjectIso_comp_kernel_map
  given: (sq : Arrow.mk f ⟶ Arrow.mk f')
  proof: by
  simp [← Iso.comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv]

中文:
定理 kernelSubobjectIso_comp_kernel_map
  条件: (sq : Arrow.mk f ⟶ Arrow.mk f')
  证明: by
  simp [← Iso.comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv
-/
theorem kernelSubobjectIso_comp_kernel_map (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobjectIso _).hom ≫ kernel.map f f' sq.1 sq.2 sq.3.symm =
      kernelSubobjectMap sq ≫ (kernelSubobjectIso _).hom := by
  simp [← Iso.comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv]

end

/--
theorem `kernelSubobject_zero` / 定理 `kernelSubobject_zero`

English:
theorem kernelSubobject_zero
  given: {A B : C}
  statement: kernelSubobject (0 : A ⟶ B) = ⊤
  proof: by
  simp

中文:
定理 kernelSubobject_zero
  条件: {A B : C}
  结论: kernelSubobject (0 : A ⟶ B) = ⊤
  证明: by
  simp
-/
theorem kernelSubobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤ := by
  simp

/--
Instance `isIso_kernelSubobject_zero_arrow` / 实例 `isIso_kernelSubobject_zero_arrow`

English:
instance isIso_kernelSubobject_zero_arrow
  signature: : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow
  body: (isIso_arrow_iff_eq_top _).mpr (by simp)

中文:
实例 isIso_kernelSubobject_zero_arrow
  签名: : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow
  定义体: (isIso_arrow_iff_eq_top _).mpr (by simp)

Depends on / 依赖: isIso_arrow_iff_eq_top
-/
instance isIso_kernelSubobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow :=
  (isIso_arrow_iff_eq_top _).mpr (by simp)

/--
theorem `le_kernelSubobject` / 定理 `le_kernelSubobject`

English:
theorem le_kernelSubobject
  given: (A : Subobject X) (h : A.arrow ≫ f = 0)
  statement: A <= kernelSubobject f
  proof: Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

中文:
定理 le_kernelSubobject
  条件: (A : Subobject X) (h : A.arrow ≫ f = 0)
  结论: A <= kernelSubobject f
  证明: Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

Depends on / 依赖: A.arrow, Subobject, Subobject.le_mk_of_comm, kernel, kernel.lift, le_mk_of_comm
-/
theorem le_kernelSubobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A <= kernelSubobject f :=
  Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

/--
Definition of `kernelSubobjectIsoComp` / `kernelSubobjectIsoComp` 的定义

English:
definition kernelSubobjectIsoComp
  signature: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  body: kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]

中文:
定义 kernelSubobjectIsoComp
  签名: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  定义体: kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]

Depends on / 依赖: kernelIsIsoComp, kernelSubobjectIso
-/
def kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C) :=
  kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]
/--
theorem `kernelSubobjectIsoComp_hom_arrow` / 定理 `kernelSubobjectIsoComp_hom_arrow`

English:
theorem kernelSubobjectIsoComp_hom_arrow
  given: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  proof: by
  simp [kernelSubobjectIsoComp]

@[simp]

中文:
定理 kernelSubobjectIsoComp_hom_arrow
  条件: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  证明: by
  simp [kernelSubobjectIsoComp]

@[simp]

Depends on / 依赖: kernelSubobjectIsoComp
-/
theorem kernelSubobjectIsoComp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).hom ≫ (kernelSubobject g).arrow =
      (kernelSubobject (f ≫ g)).arrow ≫ f := by
  simp [kernelSubobjectIsoComp]

@[simp]
/--
theorem `kernelSubobjectIsoComp_inv_arrow` / 定理 `kernelSubobjectIsoComp_inv_arrow`

English:
theorem kernelSubobjectIsoComp_inv_arrow
  given: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  proof: by
  simp [kernelSubobjectIsoComp]

中文:
定理 kernelSubobjectIsoComp_inv_arrow
  条件: {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g]
  证明: by
  simp [kernelSubobjectIsoComp]

Depends on / 依赖: kernelSubobjectIsoComp
-/
theorem kernelSubobjectIsoComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).arrow =
      (kernelSubobject g).arrow ≫ inv f := by
  simp [kernelSubobjectIsoComp]

/--
theorem `kernelSubobject_comp_le` / 定理 `kernelSubobject_comp_le`

English:
theorem kernelSubobject_comp_le
  given: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)]
  proof: le_kernelSubobject _ _ (by simp)

中文:
定理 kernelSubobject_comp_le
  条件: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)]
  证明: le_kernelSubobject _ _ (by simp)

Depends on / 依赖: le_kernelSubobject
-/
theorem kernelSubobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] :
    kernelSubobject f <= kernelSubobject (f ≫ h) :=
  le_kernelSubobject _ _ (by simp)

/-- Postcomposing by a monomorphism does not change the kernel subobject. -/
@[simp]
/--
theorem `kernelSubobject_comp_mono` / 定理 `kernelSubobject_comp_mono`

English:
theorem kernelSubobject_comp_mono
  given: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h]
  proof: le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)

中文:
定理 kernelSubobject_comp_mono
  条件: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h]
  证明: le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)

Depends on / 依赖: cancel_mono, kernelSubobject_comp_le, le_antisymm, le_kernelSubobject
-/
theorem kernelSubobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    kernelSubobject (f ≫ h) = kernelSubobject f :=
  le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)

/--
Instance `kernelSubobject_comp_mono_isIso` / 实例 `kernelSubobject_comp_mono_isIso`

English:
instance kernelSubobject_comp_mono_isIso
  signature: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h]
  body: by
  rw [ofLE_mk_le_mk_of_comm (kernelCompMono f h).inv]
  · infer_instance
  · simp

中文:
实例 kernelSubobject_comp_mono_isIso
  签名: (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h]
  定义体: by
  rw [ofLE_mk_le_mk_of_comm (kernelCompMono f h).inv]
  · infer_instance
  · simp

Depends on / 依赖: infer_instance, kernelCompMono, ofLE_mk_le_mk_of_comm
-/
instance kernelSubobject_comp_mono_isIso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    IsIso (Subobject.ofLE _ _ (kernelSubobject_comp_le f h)) := by
  rw [ofLE_mk_le_mk_of_comm (kernelCompMono f h).inv]
  · infer_instance
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Taking cokernels is an order-reversing map from the subobjects of `X` to the quotient objects
of `X`. -/
@[simps]
/--
Definition of `cokernelOrderHom` / `cokernelOrderHom` 的定义

English:
definition cokernelOrderHom
  signature: [HasCokernels C] (X : C)
  body: Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ (Iso.op ?_) (Quiver.Hom.unop_inj ?_)
        · exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
            (isCokernelEpiComp (colim

中文:
定义 cokernelOrderHom
  签名: [HasCokernels C] (X : C)
  定义体: Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ (Iso.op ?_) (Quiver.Hom.unop_inj ?_)
        · exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
            (isCokernelEpiComp (colim

Depends on / 依赖: Cofork, Cofork.of, IsColimit, IsColimit.coconePointUniqueUpToIso, Iso.comp_inv_eq, Iso.op, Iso.op_hom, Iso.symm_hom, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, Subobject, Subobject.ind, Subobject.lift, Subobject.mk, Subobject.mk_eq_mk_of_comm, coconePointUniqueUpToIso, coequalizer, coequalizer.cofork_, cokernel
-/
def cokernelOrderHom [HasCokernels C] (X : C) : Subobject X ->o (Subobject (op X))ᵒᵈ where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ (Iso.op ?_) (Quiver.Hom.unop_inj ?_)
        · exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
            (isCokernelEpiComp (colimit.isColimit _) i.hom rfl)).symm
        · simp only [Iso.comp_inv_eq, Iso.op_hom, Iso.symm_hom, unop_comp, Quiver.Hom.unop_op,
            colimit.comp_coconePointUniqueUpToIso_hom, Cofork.ofπ_ι_app,
            coequalizer.cofork_π])
  monotone' :=
Subobject.ind₂ _ by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (cokernel.desc f (cokernel.π g) ?_).op ?_
      · rw [← Subobject.ofMkLEMk_comp h, Category.assoc, cokernel.condition, comp_zero]
      · exact Quiver.Hom.unop_inj (cokernel.π_desc _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking kernels is an order-reversing map from the quotient objects of `X` to the subobjects of
`X`. -/
@[simps]
/--
Definition of `kernelOrderHom` / `kernelOrderHom` 的定义

English:
definition kernelOrderHom
  signature: [HasKernels C] (X : C)
  body: Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
        · exact
            IsLimit.conePointUniqueUpToIso (limit.isLimit _)
              (isKernelCompMono (limit.isLimit (parallelPair g.un

中文:
定义 kernelOrderHom
  签名: [HasKernels C] (X : C)
  定义体: Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
        · exact
            IsLimit.conePointUniqueUpToIso (limit.isLimit _)
              (isKernelCompMono (limit.isLimit (parallelPair g.un

Depends on / 依赖: Fork.of, IsLimit, IsLimit.conePointUniqueUpToIso, Iso.eq_inv_comp, Subobject, Subobject.ind, Subobject.lift, Subobject.lift_mk, Subobject.mk, Subobject.mk_eq_mk_of_comm, Subobject.mk_le_mk_of_comm, conePointUniqueUpToIso, conePointUniqueUpToIso_inv_comp, eq_inv_comp, f.unop, g.unop, i.unop.hom, isKernelCompMono, isLimit, kernel
-/
def kernelOrderHom [HasKernels C] (X : C) : (Subobject (op X))ᵒᵈ ->o Subobject X where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
        · exact
            IsLimit.conePointUniqueUpToIso (limit.isLimit _)
              (isKernelCompMono (limit.isLimit (parallelPair g.unop 0)) i.unop.hom rfl)
        · dsimp
          simp only [← Iso.eq_inv_comp, limit.conePointUniqueUpToIso_inv_comp,
            Fork.ofι_π_app])
  monotone' :=
Subobject.ind₂ _ by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (kernel.lift g.unop (kernel.ι f.unop) ?_) ?_
      · rw [← Subobject.ofMkLEMk_comp h, unop_comp, kernel.condition_assoc, zero_comp]
      · exact Quiver.Hom.op_inj (by simp)

end Kernel

section Image

variable (f : X ⟶ Y) [HasImage f]

/--
Definition of `imageSubobject` / `imageSubobject` 的定义

English:
abbreviation imageSubobject
  signature: : Subobject Y
  body: Subobject.mk (image.ι f)

中文:
缩写 imageSubobject
  签名: : Subobject Y
  定义体: Subobject.mk (image.ι f)

Depends on / 依赖: Subobject, Subobject.mk
-/
abbrev imageSubobject : Subobject Y :=
  Subobject.mk (image.ι f)

/--
Definition of `imageSubobjectIso` / `imageSubobjectIso` 的定义

English:
definition imageSubobjectIso
  signature: : (imageSubobject f : C) ≅ image f
  body: Subobject.underlyingIso (image.ι f)

@[reassoc (attr := simp)]

中文:
定义 imageSubobjectIso
  签名: : (imageSubobject f : C) ≅ image f
  定义体: Subobject.underlyingIso (image.ι f)

@[reassoc (attr := simp)]

Depends on / 依赖: Subobject, Subobject.underlyingIso, underlyingIso
-/
def imageSubobjectIso : (imageSubobject f : C) ≅ image f :=
  Subobject.underlyingIso (image.ι f)

@[reassoc (attr := simp)]
/--
theorem `imageSubobject_arrow` / 定理 `imageSubobject_arrow`

English:
theorem imageSubobject_arrow
  proof: by simp [imageSubobjectIso]

@[reassoc (attr := simp)]

中文:
定理 imageSubobject_arrow
  证明: by simp [imageSubobjectIso]

@[reassoc (attr := simp)]

Depends on / 依赖: imageSubobjectIso
-/
theorem imageSubobject_arrow :
    (imageSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow := by simp [imageSubobjectIso]

@[reassoc (attr := simp)]
/--
theorem `imageSubobject_arrow'` / 定理 `imageSubobject_arrow'`

English:
theorem imageSubobject_arrow'
  proof: by simp [imageSubobjectIso]

中文:
定理 imageSubobject_arrow'
  证明: by simp [imageSubobjectIso]

Depends on / 依赖: imageSubobjectIso
-/
theorem imageSubobject_arrow' :
    (imageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f := by simp [imageSubobjectIso]

/--
Definition of `factorThruImageSubobject` / `factorThruImageSubobject` 的定义

English:
definition factorThruImageSubobject
  signature: : X ⟶ imageSubobject f
  body: factorThruImage f ≫ (imageSubobjectIso f).inv

中文:
定义 factorThruImageSubobject
  签名: : X ⟶ imageSubobject f
  定义体: factorThruImage f ≫ (imageSubobjectIso f).inv

Depends on / 依赖: factorThruImage, imageSubobjectIso
-/
def factorThruImageSubobject : X ⟶ imageSubobject f :=
  factorThruImage f ≫ (imageSubobjectIso f).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasEqualizers
  signature: C] : Epi (factorThruImageSubobject f)
  body: by
  dsimp [factorThruImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
实例 [HasEqualizers
  签名: C] : Epi (factorThruImageSubobject f)
  定义体: by
  dsimp [factorThruImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: epi_comp, factorThruImageSubobject
-/
instance [HasEqualizers C] : Epi (factorThruImageSubobject f) := by
  dsimp [factorThruImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `imageSubobject_arrow_comp` / 定理 `imageSubobject_arrow_comp`

English:
theorem imageSubobject_arrow_comp
  statement: factorThruImageSubobject f ≫ (imageSubobject f).arrow = f
  proof: by
  simp [factorThruImageSubobject]

中文:
定理 imageSubobject_arrow_comp
  结论: factorThruImageSubobject f ≫ (imageSubobject f).arrow = f
  证明: by
  simp [factorThruImageSubobject]

Depends on / 依赖: factorThruImageSubobject
-/
theorem imageSubobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f := by
  simp [factorThruImageSubobject]

/--
theorem `imageSubobject_arrow_comp_eq_zero` / 定理 `imageSubobject_arrow_comp_eq_zero`

English:
theorem imageSubobject_arrow_comp_eq_zero
  statement: [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: zero_of_epi_comp (factorThruImageSubobject f) by simp [h]

中文:
定理 imageSubobject_arrow_comp_eq_zero
  结论: [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: zero_of_epi_comp (factorThruImageSubobject f) by simp [h]

Depends on / 依赖: factorThruImageSubobject, zero_of_epi_comp
-/
theorem imageSubobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasImage f] [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0) :
    (imageSubobject f).arrow ≫ g = 0 :=
zero_of_epi_comp (factorThruImageSubobject f) by simp [h]

/--
theorem `imageSubobject_factors_comp_self` / 定理 `imageSubobject_factors_comp_self`

English:
theorem imageSubobject_factors_comp_self
  given: {W : C} (k : W ⟶ X)
  statement: (imageSubobject f).Factors (k ≫ f)
  proof: ⟨k ≫ factorThruImage f, by simp⟩

@[simp]

中文:
定理 imageSubobject_factors_comp_self
  条件: {W : C} (k : W ⟶ X)
  结论: (imageSubobject f).Factors (k ≫ f)
  证明: ⟨k ≫ factorThruImage f, by simp⟩

@[simp]

Depends on / 依赖: factorThruImage
-/
theorem imageSubobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ factorThruImage f, by simp⟩

@[simp]
/--
theorem `factorThruImageSubobject_comp_self` / 定理 `factorThruImageSubobject_comp_self`

English:
theorem factorThruImageSubobject_comp_self
  given: {W : C} (k : W ⟶ X) (h)
  proof: by
  ext
  simp

@[simp]

中文:
定理 factorThruImageSubobject_comp_self
  条件: {W : C} (k : W ⟶ X) (h)
  证明: by
  ext
  simp

@[simp]
-/
theorem factorThruImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f := by
  ext
  simp

@[simp]
/--
theorem `factorThruImageSubobject_comp_self_assoc` / 定理 `factorThruImageSubobject_comp_self_assoc`

English:
theorem factorThruImageSubobject_comp_self_assoc
  given: {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h)
  proof: by
  ext
  simp

中文:
定理 factorThruImageSubobject_comp_self_assoc
  条件: {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h)
  证明: by
  ext
  simp
-/
theorem factorThruImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruImageSubobject f := by
  ext
  simp

/--
theorem `imageSubobject_comp_le` / 定理 `imageSubobject_comp_le`

English:
theorem imageSubobject_comp_le
  given: {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)]
  proof: Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)

中文:
定理 imageSubobject_comp_le
  条件: {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)]
  证明: Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)

Depends on / 依赖: Subobject, Subobject.mk_le_mk_of_comm, image.preComp, mk_le_mk_of_comm, preComp
-/
theorem imageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    imageSubobject (h ≫ f) <= imageSubobject f :=
  Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)

section

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

@[simp]
/--
theorem `imageSubobject_zero_arrow` / 定理 `imageSubobject_zero_arrow`

English:
theorem imageSubobject_zero_arrow
  statement: (imageSubobject (0 : X ⟶ Y)).arrow = 0
  proof: by
  rw [← imageSubobject_arrow]
  simp

@[simp]

中文:
定理 imageSubobject_zero_arrow
  结论: (imageSubobject (0 : X ⟶ Y)).arrow = 0
  证明: by
  rw [← imageSubobject_arrow]
  simp

@[simp]

Depends on / 依赖: imageSubobject_arrow
-/
theorem imageSubobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0 := by
  rw [← imageSubobject_arrow]
  simp

@[simp]
/--
theorem `imageSubobject_zero` / 定理 `imageSubobject_zero`

English:
theorem imageSubobject_zero
  given: {A B : C}
  statement: imageSubobject (0 : A ⟶ B) = ⊥
  proof: Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)

中文:
定理 imageSubobject_zero
  条件: {A B : C}
  结论: imageSubobject (0 : A ⟶ B) = ⊥
  证明: Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)

Depends on / 依赖: Subobject, Subobject.botCoeIsoZero.symm, Subobject.eq_of_comm, botCoeIsoZero, eq_of_comm, imageSubobjectIso, imageZero
-/
theorem imageSubobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥ :=
  Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)

end

section

variable [HasEqualizers C]

/--
Instance `imageSubobject_comp_le_epi_of_epi` / 实例 `imageSubobject_comp_le_epi_of_epi`

English:
instance imageSubobject_comp_le_epi_of_epi
  signature: {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
  body: by
  rw [ofLE_mk_le_mk_of_comm (image.preComp h f)]
  · infer_instance
  · simp

中文:
实例 imageSubobject_comp_le_epi_of_epi
  签名: {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
  定义体: by
  rw [ofLE_mk_le_mk_of_comm (image.preComp h f)]
  · infer_instance
  · simp

Depends on / 依赖: image.preComp, infer_instance, ofLE_mk_le_mk_of_comm, preComp
-/
instance imageSubobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
    [HasImage (h ≫ f)] : Epi (Subobject.ofLE _ _ (imageSubobject_comp_le h f)) := by
  rw [ofLE_mk_le_mk_of_comm (image.preComp h f)]
  · infer_instance
  · simp

end

section

variable [HasEqualizers C]

/--
Definition of `imageSubobjectCompIso` / `imageSubobjectCompIso` 的定义

English:
definition imageSubobjectCompIso
  signature: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  body: imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[reassoc (attr := simp)]

中文:
定义 imageSubobjectCompIso
  签名: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  定义体: imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[reassoc (attr := simp)]

Depends on / 依赖: compIso, image.compIso, imageSubobjectIso
-/
def imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C) :=
  imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[reassoc (attr := simp)]
/--
theorem `imageSubobjectCompIso_hom_arrow` / 定理 `imageSubobjectCompIso_hom_arrow`

English:
theorem imageSubobjectCompIso_hom_arrow
  given: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  proof: by
  simp [imageSubobjectCompIso]

@[reassoc (attr := simp)]

中文:
定理 imageSubobjectCompIso_hom_arrow
  条件: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  证明: by
  simp [imageSubobjectCompIso]

@[reassoc (attr := simp)]

Depends on / 依赖: imageSubobjectCompIso
-/
theorem imageSubobjectCompIso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).hom ≫ (imageSubobject f).arrow =
      (imageSubobject (f ≫ h)).arrow ≫ inv h := by
  simp [imageSubobjectCompIso]

@[reassoc (attr := simp)]
/--
theorem `imageSubobjectCompIso_inv_arrow` / 定理 `imageSubobjectCompIso_inv_arrow`

English:
theorem imageSubobjectCompIso_inv_arrow
  given: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  proof: by
  simp [imageSubobjectCompIso]

中文:
定理 imageSubobjectCompIso_inv_arrow
  条件: (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h]
  证明: by
  simp [imageSubobjectCompIso]

Depends on / 依赖: imageSubobjectCompIso
-/
theorem imageSubobjectCompIso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arrow =
      (imageSubobject f).arrow ≫ h := by
  simp [imageSubobjectCompIso]

end

/--
theorem `imageSubobject_mono` / 定理 `imageSubobject_mono`

English:
theorem imageSubobject_mono
  given: (f : X ⟶ Y) [Mono f]
  statement: imageSubobject f = Subobject.mk f
  proof: eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)

中文:
定理 imageSubobject_mono
  条件: (f : X ⟶ Y) [Mono f]
  结论: imageSubobject f = Subobject.mk f
  证明: eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)

Depends on / 依赖: eq_of_comm, imageMonoIsoSource, imageSubobjectIso, underlyingIso
-/
theorem imageSubobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = Subobject.mk f :=
  eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)

/--
theorem `imageSubobject_iso_comp` / 定理 `imageSubobject_iso_comp`

English:
theorem imageSubobject_iso_comp
  statement: [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
  proof: le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))

中文:
定理 imageSubobject_iso_comp
  结论: [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
  证明: le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))

Depends on / 依赖: Subobject, Subobject.mk_le_mk_of_comm, image.preComp, imageSubobject_comp_le, le_antisymm, mk_le_mk_of_comm, preComp
-/
theorem imageSubobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
    [HasImage f] : imageSubobject (h ≫ f) = imageSubobject f :=
  le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))

/--
theorem `imageSubobject_le` / 定理 `imageSubobject_le`

English:
theorem imageSubobject_le
  statement: {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
  proof: Subobject.le_of_comm
    ((imageSubobjectIso f).hom ≫
      image.lift
        { I := (X : C)
          e := h
          m := X.arrow })
    (by rw [assoc, image.lift_fac, imageSubobject_arrow])

中文:
定理 imageSubobject_le
  结论: {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
  证明: Subobject.le_of_comm
    ((imageSubobjectIso f).hom ≫
      image.lift
        { I := (X : C)
          e := h
          m := X.arrow })
    (by rw [assoc, image.lift_fac, imageSubobject_arrow])

Depends on / 依赖: Subobject, Subobject.le_of_comm, X.arrow, image.lift, image.lift_fac, imageSubobjectIso, imageSubobject_arrow, le_of_comm, lift_fac
-/
theorem imageSubobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
    (w : h ≫ X.arrow = f) : imageSubobject f <= X :=
  Subobject.le_of_comm
    ((imageSubobjectIso f).hom ≫
      image.lift
        { I := (X : C)
          e := h
          m := X.arrow })
    (by rw [assoc, image.lift_fac, imageSubobject_arrow])

/--
theorem `imageSubobject_le_mk` / 定理 `imageSubobject_le_mk`

English:
theorem imageSubobject_le_mk
  statement: {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
  proof: imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])

中文:
定理 imageSubobject_le_mk
  结论: {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
  证明: imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])

Depends on / 依赖: Subobject, Subobject.underlyingIso, imageSubobject_le, underlyingIso
-/
theorem imageSubobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
    (h : A ⟶ X) (w : h ≫ g = f) : imageSubobject f <= Subobject.mk g :=
  imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])

/--
Definition of `imageSubobjectMap` / `imageSubobjectMap` 的定义

English:
definition imageSubobjectMap
  signature: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
  body: (imageSubobjectIso f).hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

#adaptation_note

中文:
定义 imageSubobjectMap
  签名: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
  定义体: (imageSubobjectIso f).hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

#adaptation_note

Depends on / 依赖: image.map, imageSubobjectIso
-/
def imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobject f : C) ⟶ (imageSubobject g : C) :=
  (imageSubobjectIso f).hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `imageSubobjectMap_arrow` / 定理 `imageSubobjectMap_arrow`

English:
theorem imageSubobjectMap_arrow
  statement: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
  proof: by
  simp only [imageSubobjectMap, Category.assoc, Arrow.mk_left, Arrow.mk_right,
    Arrow.mk_hom, imageSubobject_arrow']
  rw [dsimp% image.map_ι sq]
  simp

中文:
定理 imageSubobjectMap_arrow
  结论: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
  证明: by
  simp only [imageSubobjectMap, Category.assoc, Arrow.mk_left, Arrow.mk_right,
    Arrow.mk_hom, imageSubobject_arrow']
  rw [dsimp% image.map_ι sq]
  simp

Depends on / 依赖: Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Category, Category.assoc, image.map_, imageSubobjectMap, imageSubobject_arrow, mk_hom, mk_left, mk_right
-/
theorem imageSubobjectMap_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    imageSubobjectMap sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right := by
  simp only [imageSubobjectMap, Category.assoc, Arrow.mk_left, Arrow.mk_right,
    Arrow.mk_hom, imageSubobject_arrow']
  rw [dsimp% image.map_ι sq]
  simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `image_map_comp_imageSubobjectIso_inv` / 定理 `image_map_comp_imageSubobjectIso_inv`

English:
theorem image_map_comp_imageSubobjectIso_inv
  statement: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
  proof: by
  ext
  simpa using image.map_ι sq

中文:
定理 image_map_comp_imageSubobjectIso_inv
  结论: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
  证明: by
  ext
  simpa using image.map_ι sq

Depends on / 依赖: image.map_
-/
theorem image_map_comp_imageSubobjectIso_inv {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    image.map sq ≫ (imageSubobjectIso _).inv =
      (imageSubobjectIso _).inv ≫ imageSubobjectMap sq := by
  ext
  simpa using image.map_ι sq

set_option backward.defeqAttrib.useBackward true in
/--
theorem `imageSubobjectIso_comp_image_map` / 定理 `imageSubobjectIso_comp_image_map`

English:
theorem imageSubobjectIso_comp_image_map
  statement: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
  proof: by
  simp [imageSubobjectMap]

中文:
定理 imageSubobjectIso_comp_image_map
  结论: {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
  证明: by
  simp [imageSubobjectMap]

Depends on / 依赖: imageSubobjectMap
-/
theorem imageSubobjectIso_comp_image_map {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobjectIso _).hom ≫ image.map sq =
      imageSubobjectMap sq ≫ (imageSubobjectIso _).hom := by
  simp [imageSubobjectMap]

end Image

end Limits

end CategoryTheory
