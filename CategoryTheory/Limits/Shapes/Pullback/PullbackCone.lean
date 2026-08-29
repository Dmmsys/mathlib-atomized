/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# PullbackCone

This file provides API for interacting with cones (resp. cocones) in the case of pullbacks
(resp. pushouts).

## Main definitions

* `PullbackCone f g`: Given morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, a term `t : PullbackCone f g`
  provides the data of a cone pictured as follows
  ```
  t.pt ---t.snd---> Y
    | |
  t.fst g
    | |
    v v
    X -----f------> Z
  ```
  The type `PullbackCone f g` is implemented as an abbreviation for `Cone (cospan f g)`, so general
  results about cones are also available for `PullbackCone f g`.

* `PushoutCone f g`: Given morphisms `f : X ⟶ Y` and `g : X ⟶ Z`, a term `t : PushoutCone f g`
  provides the data of a cocone pictured as follows
  ```
    X -----f------> Y
    | |
    g t.inr
    | |
    v v
    Z ---t.inl---> t.pt
  ```
  Similar to `PullbackCone`, `PushoutCone f g` is implemented as an abbreviation for
  `Cocone (span f g)`, so general results about cocones are also available for `PushoutCone f g`.

## API
We summarize the most important parts of the API for pullback cones here. The dual notions for
pushout cones are also available in this file.

Various ways of constructing pullback cones:
* `PullbackCone.mk` constructs a term of `PullbackCone f g` given morphisms `fst` and `snd` such
  that `fst ≫ f = snd ≫ g`.
* `PullbackCone.flip` is the `PullbackCone` obtained by flipping `fst` and `snd`.

Interaction with `IsLimit`:
* `PullbackCone.isLimitAux` and `PullbackCone.isLimitAux'` provide two convenient ways to show that
  a given `PullbackCone` is a limit cone.
* `PullbackCone.isLimit.mk` provides a convenient way to show that a `PullbackCone` constructed
  using `PullbackCone.mk` is a limit cone.
* `PullbackCone.IsLimit.lift` and `PullbackCone.IsLimit.lift'` provides convenient ways for
  constructing the morphisms to the point of a limit `PullbackCone` from the universal property.
* `PullbackCone.IsLimit.hom_ext` provides a convenient way to show that two morphisms to the point
  of a limit `PullbackCone` are equal.

Interaction with `CommSq`:
* `CommSq.cone` and `CommSq.cocone` provide the implicit (non-limiting) pullback cone and pushout
  cocone associated with a commuting square

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/--
Definition of `PullbackCone` / `PullbackCone` 的定义

English:
abbreviation PullbackCone
  signature: (f : X ⟶ Z) (g : Y ⟶ Z)
  body: Cone (cospan f g)

中文:
缩写 PullbackCone
  签名: (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: Cone (cospan f g)

Depends on / 依赖: cospan
-/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: (t : PullbackCone f g)
  body: t.π.app WalkingCospan.left

中文:
缩写 fst
  签名: (t : PullbackCone f g)
  定义体: t.π.app WalkingCospan.left

Depends on / 依赖: WalkingCospan, WalkingCospan.left
-/
abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: (t : PullbackCone f g)
  body: t.π.app WalkingCospan.right

中文:
缩写 snd
  签名: (t : PullbackCone f g)
  定义体: t.π.app WalkingCospan.right

Depends on / 依赖: WalkingCospan, WalkingCospan.right
-/
abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right

/--
theorem `π_app_left` / 定理 `π_app_left`

English:
theorem π_app_left
  given: (c : PullbackCone f g)
  statement: c.π.app WalkingCospan.left = c.fst
  proof: rfl

中文:
定理 π_app_left
  条件: (c : PullbackCone f g)
  结论: c.π.app WalkingCospan.left = c.fst
  证明: rfl
-/
theorem π_app_left (c : PullbackCone f g) : c.π.app WalkingCospan.left = c.fst := rfl

/--
theorem `π_app_right` / 定理 `π_app_right`

English:
theorem π_app_right
  given: (c : PullbackCone f g)
  statement: c.π.app WalkingCospan.right = c.snd
  proof: rfl

中文:
定理 π_app_right
  条件: (c : PullbackCone f g)
  结论: c.π.app WalkingCospan.right = c.snd
  证明: rfl
-/
theorem π_app_right (c : PullbackCone f g) : c.π.app WalkingCospan.right = c.snd := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `condition_one` / 定理 `condition_one`

English:
theorem condition_one
  given: (t : PullbackCone f g)
  statement: t.π.app WalkingCospan.one = t.fst ≫ f
  proof: by
  have w := t.π.naturality WalkingCospan.Hom.inl
  dsimp at w; simpa using w

中文:
定理 condition_one
  条件: (t : PullbackCone f g)
  结论: t.π.app WalkingCospan.one = t.fst ≫ f
  证明: by
  have w := t.π.naturality WalkingCospan.Hom.inl
  dsimp at w; simpa using w

Depends on / 依赖: WalkingCospan, WalkingCospan.Hom.inl, naturality
-/
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f := by
  have w := t.π.naturality WalkingCospan.Hom.inl
  dsimp at w; simpa using w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
such that `fst ≫ f = snd ≫ g`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g := by cat_disch)
  body: W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] }

@[simp]

中文:
定义 mk
  签名: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g := by cat_disch)
  定义体: W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] }

@[simp]

Depends on / 依赖: Option.casesOn, PullbackCone, WalkingPair, WalkingPair.casesOn, casesOn, cat_disch, naturality
-/
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g := by cat_disch) :
    PullbackCone f g where
  pt := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] }

@[simp]
/--
theorem `mk_π_app_left` / 定理 `mk_π_app_left`

English:
theorem mk_π_app_left
  given: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  proof: rfl

@[simp]

中文:
定理 mk_π_app_left
  条件: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  证明: rfl

@[simp]
-/
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.left = fst := rfl

@[simp]
/--
theorem `mk_π_app_right` / 定理 `mk_π_app_right`

English:
theorem mk_π_app_right
  given: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  proof: rfl

@[simp]

中文:
定理 mk_π_app_right
  条件: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  证明: rfl

@[simp]

Depends on / 依赖: F.mapIso, P.prop_of_iso, mapIso, prop_of_iso
-/
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.right = snd := rfl

@[simp]
/--
theorem `mk_π_app_one` / 定理 `mk_π_app_one`

English:
theorem mk_π_app_one
  given: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  proof: rfl

@[simp]

中文:
定理 mk_π_app_one
  条件: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  证明: rfl

@[simp]
-/
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.one = fst ≫ f := rfl

@[simp]
/--
theorem `mk_fst` / 定理 `mk_fst`

English:
theorem mk_fst
  given: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  proof: rfl

@[simp]

中文:
定理 mk_fst
  条件: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  证明: rfl

@[simp]
-/
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).fst = fst := rfl

@[simp]
/--
theorem `mk_snd` / 定理 `mk_snd`

English:
theorem mk_snd
  given: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  proof: rfl

@[reassoc]

中文:
定理 mk_snd
  条件: {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g)
  证明: rfl

@[reassoc]

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.le_shift, IsStableUnderShiftBy.mk, le_shift
-/
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).snd = snd := rfl

@[reassoc]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (t : PullbackCone f g)
  statement: fst t ≫ f = snd t ≫ g
  proof: (t.w inl).trans (t.w inr).symm

中文:
定理 condition
  条件: (t : PullbackCone f g)
  结论: fst t ≫ f = snd t ≫ g
  证明: (t.w inl).trans (t.w inr).symm

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.le_shift, IsStableUnderShiftBy.mk, le_shift, limitsClosure, limitsClosure.of_isoClosure, limitsClosure.of_limitPresentation, limitsClosure.of_mem, mapIso, of_isoClosure, of_limitPresentation, of_mem, pres.map, shiftFunctor
-/
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equalizer_ext` / 定理 `equalizer_ext`

English:
theorem equalizer_ext
  statement: (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)

中文:
定理 equalizer_ext
  结论: (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
-/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : forall j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w inl, reassoc_of% h₀]

/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
  body: WalkingCospan.ext i w₁ w₂

中文:
定义 ext
  签名: {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
  定义体: WalkingCospan.ext i w₁ w₂

Depends on / 依赖: WalkingCospan, WalkingCospan.ext, cat_disch, i.hom, s.snd, t.snd
-/
def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
    (w₂ : s.snd = i.hom ≫ t.snd := by cat_disch) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pullback cone and the corresponding pullback cone
reconstructed using `PullbackCone.mk`. -/
@[simps!]
/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: (t : PullbackCone f g)
  body: PullbackCone.ext (Iso.refl _)

中文:
定义 eta
  签名: (t : PullbackCone f g)
  定义体: PullbackCone.ext (Iso.refl _)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def eta (t : PullbackCone f g) : t ≅ mk t.fst t.snd t.condition :=
  PullbackCone.ext (Iso.refl _)

/--
Definition of `isLimitAux` / `isLimitAux` 的定义

English:
definition isLimitAux
  signature: (t : PullbackCone f g) (lift : forall s : PullbackCone f g, s.pt ⟶ t.pt)
  body: { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl]; rw [← t.w inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

中文:
定义 isLimitAux
  签名: (t : PullbackCone f g) (lift : 对任意 s : PullbackCone f g, s.pt ⟶ t.pt)
  定义体: { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl]; rw [← t.w inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

Depends on / 依赖: Category, Category.assoc, Option.casesOn, WalkingPair, WalkingPair.casesOn, casesOn, fac_left, fac_right
-/
def isLimitAux (t : PullbackCone f g) (lift : forall s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : forall s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : forall (s : PullbackCone f g) (m : s.pt ⟶ t.pt)
      (_ : forall j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl]; rw [← t.w inl]; rw [← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/--
Definition of `isLimitAux'` / `isLimitAux'` 的定义

English:
definition isLimitAux'
  signature: (t : PullbackCone f g)
  body: PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

中文:
定义 isLimitAux'
  签名: (t : PullbackCone f g)
  定义体: PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

Depends on / 依赖: PullbackCone, PullbackCone.isLimitAux, WalkingCospan, WalkingCospan.left, WalkingCospan.right, colimitsCardinalClosure, create, infer_instance, isLimitAux
-/
def isLimitAux' (t : PullbackCone f g)
    (create :
      forall s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd ∧ forall {m}, m ≫ t.fst = s.fst -> m ≫ t.snd = s.snd -> m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

/--
Definition of `IsLimit.mk` / `IsLimit.mk` 的定义

English:
definition IsLimit.mk
  signature: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
  body: isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

中文:
定义 是极限.mk
  签名: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
  定义体: isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : forall s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : forall s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : forall s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      forall (s : PullbackCone f g) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (mk fst snd eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/--
theorem `IsLimit.hom_ext` / 定理 `IsLimit.hom_ext`

English:
theorem IsLimit.hom_ext
  statement: {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
  proof: ht.hom_ext equalizer_ext _ h₀ h₁

中文:
定理 是极限.hom_ext
  结论: {t : PullbackCone f g} (ht : 是极限 t) {W : C} {k l : W ⟶ t.pt}
  证明: ht.hom_ext equalizer_ext _ h₀ h₁
-/
theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
    (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
ht.hom_ext equalizer_ext _ h₀ h₁

/--
Definition of `IsLimit.lift` / `IsLimit.lift` 的定义

English:
definition IsLimit.lift
  signature: {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  body: ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]

中文:
定义 是极限.lift
  签名: {t : PullbackCone f g} (ht : 是极限 t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  定义体: ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
-/
def IsLimit.lift {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
ht.lift PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
/--
lemma `IsLimit.lift_fst` / 引理 `IsLimit.lift_fst`

English:
lemma IsLimit.lift_fst
  statement: {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  proof: ht.fac _ _

@[reassoc (attr := simp)]

中文:
引理 是极限.lift_fst
  结论: {t : PullbackCone f g} (ht : 是极限 t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  证明: ht.fac _ _

@[reassoc (attr := simp)]

Depends on / 依赖: ht.fac
-/
lemma IsLimit.lift_fst {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ fst t = h := ht.fac _ _

@[reassoc (attr := simp)]
/--
lemma `IsLimit.lift_snd` / 引理 `IsLimit.lift_snd`

English:
lemma IsLimit.lift_snd
  statement: {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  proof: ht.fac _ _

中文:
引理 是极限.lift_snd
  结论: {t : PullbackCone f g} (ht : 是极限 t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  证明: ht.fac _ _

Depends on / 依赖: ht.fac
-/
lemma IsLimit.lift_snd {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ snd t = k := ht.fac _ _

/--
Definition of `IsLimit.lift'` / `IsLimit.lift'` 的定义

English:
definition IsLimit.lift'
  signature: {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  body: ⟨IsLimit.lift ht h k w, by simp⟩

中文:
定义 是极限.lift'
  签名: {t : PullbackCone f g} (ht : 是极限 t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  定义体: ⟨IsLimit.lift ht h k w, by simp⟩

Depends on / 依赖: IsLimit, IsLimit.lift
-/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ t.pt // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨IsLimit.lift ht h k w, by simp⟩

/--
Definition of `mkSelfIsLimit` / `mkSelfIsLimit` 的定义

English:
definition mkSelfIsLimit
  signature: {t : PullbackCone f g} (ht : IsLimit t)
  body: IsLimit.ofIsoLimit ht (eta t)

中文:
定义 mkSelfIsLimit
  签名: {t : PullbackCone f g} (ht : 是极限 t)
  定义体: IsLimit.ofIsoLimit ht (eta t)

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, hX.prop_diag_obj, hX.toColimitPresentation, ofIsoLimit, of_colimitPresentation, prop_diag_obj, toColimitPresentation
-/
def mkSelfIsLimit {t : PullbackCone f g} (ht : IsLimit t) : IsLimit (mk t.fst t.snd t.condition) :=
  IsLimit.ofIsoLimit ht (eta t)

section Flip

variable (t : PullbackCone f g)

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: : PullbackCone g f
  body: PullbackCone.mk _ _ t.condition.symm

中文:
定义 flip
  签名: : PullbackCone g f
  定义体: PullbackCone.mk _ _ t.condition.symm

Depends on / 依赖: PullbackCone, PullbackCone.mk, condition, t.condition.symm
-/
def flip : PullbackCone g f := PullbackCone.mk _ _ t.condition.symm

/--
lemma `flip_pt` / 引理 `flip_pt`

English:
lemma flip_pt
  statement: t.flip.pt = t.pt
  proof: rfl

中文:
引理 flip_pt
  结论: t.flip.pt = t.pt
  证明: rfl
-/
@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
/--
lemma `flip_fst` / 引理 `flip_fst`

English:
lemma flip_fst
  statement: t.flip.fst = t.snd
  proof: rfl

中文:
引理 flip_fst
  结论: t.flip.fst = t.snd
  证明: rfl
-/
@[simp] lemma flip_fst : t.flip.fst = t.snd := rfl
/--
lemma `flip_snd` / 引理 `flip_snd`

English:
lemma flip_snd
  statement: t.flip.snd = t.fst
  proof: rfl

中文:
引理 flip_snd
  结论: t.flip.snd = t.fst
  证明: rfl
-/
@[simp] lemma flip_snd : t.flip.snd = t.fst := rfl

/--
Definition of `flipFlipIso` / `flipFlipIso` 的定义

English:
definition flipFlipIso
  signature: : t.flip.flip ≅ t
  body: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 flipFlipIso
  签名: : t.flip.flip ≅ t
  定义体: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def flipFlipIso : t.flip.flip ≅ t := PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `flipIsLimit` / `flipIsLimit` 的定义

English:
definition flipIsLimit
  signature: (ht : IsLimit t)
  body: IsLimit.mk _ (fun s => ht.lift s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsLimit.hom_ext ht <;> simp [h₁, h₂])

中文:
定义 flipIsLimit
  签名: (ht : 是极限 t)
  定义体: IsLimit.mk _ (fun s => ht.lift s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsLimit.hom_ext ht <;> simp [h₁, h₂])

Depends on / 依赖: IsLimit, IsLimit.hom_ext, IsLimit.mk, hom_ext, ht.lift, s.flip
-/
def flipIsLimit (ht : IsLimit t) : IsLimit t.flip :=
  IsLimit.mk _ (fun s => ht.lift s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsLimit.hom_ext ht <;> simp [h₁, h₂])

/--
Definition of `isLimitOfFlip` / `isLimitOfFlip` 的定义

English:
definition isLimitOfFlip
  signature: (ht : IsLimit t.flip)
  body: IsLimit.ofIsoLimit (flipIsLimit ht) t.flipFlipIso

中文:
定义 isLimitOfFlip
  签名: (ht : 是极限 t.flip)
  定义体: IsLimit.ofIsoLimit (flipIsLimit ht) t.flipFlipIso

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, flipFlipIso, flipIsLimit, ofIsoLimit, t.flipFlipIso
-/
def isLimitOfFlip (ht : IsLimit t.flip) : IsLimit t :=
  IsLimit.ofIsoLimit (flipIsLimit ht) t.flipFlipIso

end Flip

end PullbackCone

/-- This is a helper construction that can be useful when verifying that a category has all
pullbacks. Given `F : WalkingCospan ⥤ C`, which is really the same as
`cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
get a cone on `F`.

If you're thinking about using this, have a look at `hasPullbacks_of_hasLimit_cospan`,
which you may find to be an easier way of achieving your goal. -/
@[simps]
/--
Definition of `Cone.ofPullbackCone` / `Cone.ofPullbackCone` 的定义

English:
definition Cone.ofPullbackCone
  signature: {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr))
  body: t.pt
  π := t.π ≫ (diagramIsoCospan F).inv

中文:
定义 锥.ofPullbackCone
  签名: {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr))
  定义体: t.pt
  π := t.π ≫ (diagramIsoCospan F).inv

Depends on / 依赖: P.instIsClosedUnderColimitsOfShapeColimitsClosure, instIsClosedUnderColimitsOfShapeColimitsClosure, t.pt
-/
def Cone.ofPullbackCone {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) :
    Cone F where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).inv

/-- Given `F : WalkingCospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
/--
Definition of `PullbackCone.ofCone` / `PullbackCone.ofCone` 的定义

English:
definition PullbackCone.ofCone
  signature: {F : WalkingCospan ⥤ C} (t : Cone F)
  body: t.pt
  π := t.π ≫ (diagramIsoCospan F).hom

中文:
定义 PullbackCone.ofCone
  签名: {F : WalkingCospan ⥤ C} (t : 锥 F)
  定义体: t.pt
  π := t.π ≫ (diagramIsoCospan F).hom

Depends on / 依赖: t.pt
-/
def PullbackCone.ofCone {F : WalkingCospan ⥤ C} (t : Cone F) :
    PullbackCone (F.map inl) (F.map inr) where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingCospan ⥤ C` is isomorphic to some `PullbackCone.mk` after
composing with `diagramIsoCospan`. -/
@[simps!]
/--
Definition of `PullbackCone.isoMk` / `PullbackCone.isoMk` 的定义

English:
definition PullbackCone.isoMk
  signature: {F : WalkingCospan ⥤ C} (t : Cone F)
  body: Cone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

中文:
定义 PullbackCone.isoMk
  签名: {F : WalkingCospan ⥤ C} (t : 锥 F)
  定义体: Cone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

Depends on / 依赖: Cone.ext, Iso.refl
-/
def PullbackCone.isoMk {F : WalkingCospan ⥤ C} (t : Cone F) :
    (Cone.postcompose (diagramIsoCospan.{v} _).hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr :)) :=
Cone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

/--
Definition of `PushoutCocone` / `PushoutCocone` 的定义

English:
abbreviation PushoutCocone
  signature: (f : X ⟶ Y) (g : X ⟶ Z)
  body: Cocone (span f g)

中文:
缩写 PushoutCocone
  签名: (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: Cocone (span f g)

Depends on / 依赖: Cocone
-/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/--
Definition of `inl` / `inl` 的定义

English:
abbreviation inl
  signature: (t : PushoutCocone f g)
  body: t.ι.app WalkingSpan.left

中文:
缩写 inl
  签名: (t : PushoutCocone f g)
  定义体: t.ι.app WalkingSpan.left

Depends on / 依赖: WalkingSpan, WalkingSpan.left
-/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.pt :=
  t.ι.app WalkingSpan.left

/--
Definition of `inr` / `inr` 的定义

English:
abbreviation inr
  signature: (t : PushoutCocone f g)
  body: t.ι.app WalkingSpan.right

中文:
缩写 inr
  签名: (t : PushoutCocone f g)
  定义体: t.ι.app WalkingSpan.right

Depends on / 依赖: WalkingSpan, WalkingSpan.right
-/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
  t.ι.app WalkingSpan.right

-- This cannot be `@[simp]` because `c.inl` is reducibly defeq to the LHS.
/--
theorem `ι_app_left` / 定理 `ι_app_left`

English:
theorem ι_app_left
  given: (c : PushoutCocone f g)
  statement: c.ι.app WalkingSpan.left = c.inl
  proof: rfl

中文:
定理 ι_app_left
  条件: (c : PushoutCocone f g)
  结论: c.ι.app WalkingSpan.left = c.inl
  证明: rfl
-/
theorem ι_app_left (c : PushoutCocone f g) : c.ι.app WalkingSpan.left = c.inl := rfl

-- This cannot be `@[simp]` because `c.inr` is reducibly defeq to the LHS.
/--
theorem `ι_app_right` / 定理 `ι_app_right`

English:
theorem ι_app_right
  given: (c : PushoutCocone f g)
  statement: c.ι.app WalkingSpan.right = c.inr
  proof: rfl

中文:
定理 ι_app_right
  条件: (c : PushoutCocone f g)
  结论: c.ι.app WalkingSpan.right = c.inr
  证明: rfl
-/
theorem ι_app_right (c : PushoutCocone f g) : c.ι.app WalkingSpan.right = c.inr := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `condition_zero` / 定理 `condition_zero`

English:
theorem condition_zero
  given: (t : PushoutCocone f g)
  statement: t.ι.app WalkingSpan.zero = f ≫ t.inl
  proof: by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  dsimp at w; simpa using w.symm

中文:
定理 condition_zero
  条件: (t : PushoutCocone f g)
  结论: t.ι.app WalkingSpan.zero = f ≫ t.inl
  证明: by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  dsimp at w; simpa using w.symm

Depends on / 依赖: WalkingSpan, WalkingSpan.Hom.fst, naturality, w.symm
-/
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl := by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  dsimp at w; simpa using w.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
that `f ≫ inl = g ↠ inr`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  body: W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }

@[simp]

中文:
定义 mk
  签名: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  定义体: W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }

@[simp]
-/
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g where
  pt := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }

@[simp]
/--
theorem `mk_ι_app_left` / 定理 `mk_ι_app_left`

English:
theorem mk_ι_app_left
  given: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  proof: rfl

@[simp]

中文:
定理 mk_ι_app_left
  条件: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  证明: rfl

@[simp]
-/
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.left = inl := rfl

@[simp]
/--
theorem `mk_ι_app_right` / 定理 `mk_ι_app_right`

English:
theorem mk_ι_app_right
  given: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  proof: rfl

@[simp]

中文:
定理 mk_ι_app_right
  条件: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  证明: rfl

@[simp]
-/
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.right = inr := rfl

@[simp]
/--
theorem `mk_ι_app_zero` / 定理 `mk_ι_app_zero`

English:
theorem mk_ι_app_zero
  given: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  proof: rfl

@[simp]

中文:
定理 mk_ι_app_zero
  条件: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  证明: rfl

@[simp]
-/
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.zero = f ≫ inl := rfl

@[simp]
/--
theorem `mk_inl` / 定理 `mk_inl`

English:
theorem mk_inl
  given: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  proof: rfl

@[simp]

中文:
定理 mk_inl
  条件: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  证明: rfl

@[simp]
-/
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inl = inl := rfl

@[simp]
/--
theorem `mk_inr` / 定理 `mk_inr`

English:
theorem mk_inr
  given: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  proof: rfl

@[reassoc]

中文:
定理 mk_inr
  条件: {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr)
  证明: rfl

@[reassoc]
-/
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inr = inr := rfl

@[reassoc]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (t : PushoutCocone f g)
  statement: f ≫ inl t = g ≫ inr t
  proof: (t.w fst).trans (t.w snd).symm

中文:
定理 condition
  条件: (t : PushoutCocone f g)
  结论: f ≫ inl t = g ≫ inr t
  证明: (t.w fst).trans (t.w snd).symm
-/
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coequalizer_ext` / 定理 `coequalizer_ext`

English:
theorem coequalizer_ext
  statement: (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}

中文:
定理 coequalizer_ext
  结论: (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
-/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
    forall j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w fst, Category.assoc, Category.assoc, h₀]

/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
  body: WalkingSpan.ext i w₁ w₂

中文:
定义 ext
  签名: {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
  定义体: WalkingSpan.ext i w₁ w₂

Depends on / 依赖: WalkingSpan, WalkingSpan.ext, cat_disch, i.hom, s.inr, t.inr
-/
def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
    (w₂ : s.inr ≫ i.hom = t.inr := by cat_disch) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pushout cocone and the corresponding pushout cocone
reconstructed using `PushoutCocone.mk`. -/
@[simps!]
/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: (t : PushoutCocone f g)
  body: PushoutCocone.ext (Iso.refl _)

中文:
定义 eta
  签名: (t : PushoutCocone f g)
  定义体: PushoutCocone.ext (Iso.refl _)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def eta (t : PushoutCocone f g) : t ≅ mk t.inl t.inr t.condition :=
  PushoutCocone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitAux` / `isColimitAux` 的定义

English:
definition isColimitAux
  signature: (t : PushoutCocone f g) (desc : forall s : PushoutCocone f g, t.pt ⟶ s.pt)
  body: { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

中文:
定义 isColimitAux
  签名: (t : PushoutCocone f g) (desc : 对任意 s : PushoutCocone f g, t.pt ⟶ s.pt)
  定义体: { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

Depends on / 依赖: Option.casesOn, WalkingPair, WalkingPair.casesOn, casesOn, fac_left, fac_right
-/
def isColimitAux (t : PushoutCocone f g) (desc : forall s : PushoutCocone f g, t.pt ⟶ s.pt)
    (fac_left : forall s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : forall s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq : forall (s : PushoutCocone f g) (m : t.pt ⟶ s.pt)
    (_ : forall j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/--
Definition of `isColimitAux'` / `isColimitAux'` 的定义

English:
definition isColimitAux'
  signature: (t : PushoutCocone f g)
  body: isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

中文:
定义 isColimitAux'
  签名: (t : PushoutCocone f g)
  定义体: isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

Depends on / 依赖: WalkingCospan, WalkingCospan.left, WalkingCospan.right, create, isColimitAux
-/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      forall s : PushoutCocone f g,
        { l //
          t.inl ≫ l = s.inl ∧
            t.inr ≫ l = s.inr ∧ forall {m}, t.inl ≫ m = s.inl -> t.inr ≫ m = s.inr -> m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)


/--
theorem `IsColimit.hom_ext` / 定理 `IsColimit.hom_ext`

English:
theorem IsColimit.hom_ext
  statement: {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
  proof: ht.hom_ext coequalizer_ext _ h₀ h₁

中文:
定理 是余极限.hom_ext
  结论: {t : PushoutCocone f g} (ht : 是余极限 t) {W : C} {k l : t.pt ⟶ W}
  证明: ht.hom_ext coequalizer_ext _ h₀ h₁
-/
theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
ht.hom_ext coequalizer_ext _ h₀ h₁

/--
Definition of `IsColimit.desc` / `IsColimit.desc` 的定义

English:
definition IsColimit.desc
  signature: {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  body: ht.desc (PushoutCocone.mk _ _ w)

中文:
定义 是余极限.desc
  签名: {t : PushoutCocone f g} (ht : 是余极限 t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  定义体: ht.desc (PushoutCocone.mk _ _ w)
-/
def IsColimit.desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : t.pt ⟶ W :=
  ht.desc (PushoutCocone.mk _ _ w)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `IsColimit.inl_desc` / 引理 `IsColimit.inl_desc`

English:
lemma IsColimit.inl_desc
  statement: {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  proof: ht.fac _ _

中文:
引理 是余极限.inl_desc
  结论: {t : PushoutCocone f g} (ht : 是余极限 t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  证明: ht.fac _ _

Depends on / 依赖: ht.fac
-/
lemma IsColimit.inl_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inl t ≫ IsColimit.desc ht h k w = h :=
  ht.fac _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `IsColimit.inr_desc` / 引理 `IsColimit.inr_desc`

English:
lemma IsColimit.inr_desc
  statement: {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  proof: ht.fac _ _

中文:
引理 是余极限.inr_desc
  结论: {t : PushoutCocone f g} (ht : 是余极限 t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  证明: ht.fac _ _

Depends on / 依赖: ht.fac
-/
lemma IsColimit.inr_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inr t ≫ IsColimit.desc ht h k w = k :=
  ht.fac _ _

/--
Definition of `IsColimit.desc'` / `IsColimit.desc'` 的定义

English:
definition IsColimit.desc'
  signature: {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  body: ⟨IsColimit.desc ht h k w, by simp⟩

中文:
定义 是余极限.desc'
  签名: {t : PushoutCocone f g} (ht : 是余极限 t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  定义体: ⟨IsColimit.desc ht h k w, by simp⟩

Depends on / 依赖: IsColimit, IsColimit.desc
-/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : t.pt ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨IsColimit.desc ht h k w, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsColimit.mk` / `IsColimit.mk` 的定义

English:
definition IsColimit.mk
  signature: {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
  body: isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

中文:
定义 是余极限.mk
  签名: {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
  定义体: isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
    (desc : forall s : PushoutCocone f g, W ⟶ s.pt)
    (fac_left : forall s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : forall s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq :
      forall (s : PushoutCocone f g) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (mk inl inr eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/--
Definition of `mkSelfIsColimit` / `mkSelfIsColimit` 的定义

English:
definition mkSelfIsColimit
  signature: {t : PushoutCocone f g} (ht : IsColimit t)
  body: IsColimit.ofIsoColimit ht (eta t)

中文:
定义 mkSelfIsColimit
  签名: {t : PushoutCocone f g} (ht : 是余极限 t)
  定义体: IsColimit.ofIsoColimit ht (eta t)

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, ofIsoColimit
-/
def mkSelfIsColimit {t : PushoutCocone f g} (ht : IsColimit t) :
    IsColimit (mk t.inl t.inr t.condition) :=
  IsColimit.ofIsoColimit ht (eta t)

section Flip

variable (t : PushoutCocone f g)

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: : PushoutCocone g f
  body: PushoutCocone.mk _ _ t.condition.symm

中文:
定义 flip
  签名: : PushoutCocone g f
  定义体: PushoutCocone.mk _ _ t.condition.symm

Depends on / 依赖: PushoutCocone, PushoutCocone.mk, condition, t.condition.symm
-/
def flip : PushoutCocone g f := PushoutCocone.mk _ _ t.condition.symm

/--
lemma `flip_pt` / 引理 `flip_pt`

English:
lemma flip_pt
  statement: t.flip.pt = t.pt
  proof: rfl

中文:
引理 flip_pt
  结论: t.flip.pt = t.pt
  证明: rfl
-/
@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
/--
lemma `flip_inl` / 引理 `flip_inl`

English:
lemma flip_inl
  statement: t.flip.inl = t.inr
  proof: rfl

中文:
引理 flip_inl
  结论: t.flip.inl = t.inr
  证明: rfl
-/
@[simp] lemma flip_inl : t.flip.inl = t.inr := rfl
/--
lemma `flip_inr` / 引理 `flip_inr`

English:
lemma flip_inr
  statement: t.flip.inr = t.inl
  proof: rfl

中文:
引理 flip_inr
  结论: t.flip.inr = t.inl
  证明: rfl
-/
@[simp] lemma flip_inr : t.flip.inr = t.inl := rfl

/--
Definition of `flipFlipIso` / `flipFlipIso` 的定义

English:
definition flipFlipIso
  signature: : t.flip.flip ≅ t
  body: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 flipFlipIso
  签名: : t.flip.flip ≅ t
  定义体: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def flipFlipIso : t.flip.flip ≅ t := PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `flipIsColimit` / `flipIsColimit` 的定义

English:
definition flipIsColimit
  signature: (ht : IsColimit t)
  body: IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

中文:
定义 flipIsColimit
  签名: (ht : 是余极限 t)
  定义体: IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

Depends on / 依赖: IsColimit, IsColimit.hom_ext, IsColimit.mk, hom_ext, ht.desc, s.flip
-/
def flipIsColimit (ht : IsColimit t) : IsColimit t.flip :=
  IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

/--
Definition of `isColimitOfFlip` / `isColimitOfFlip` 的定义

English:
definition isColimitOfFlip
  signature: (ht : IsColimit t.flip)
  body: IsColimit.ofIsoColimit (flipIsColimit ht) t.flipFlipIso

中文:
定义 isColimitOfFlip
  签名: (ht : 是余极限 t.flip)
  定义体: IsColimit.ofIsoColimit (flipIsColimit ht) t.flipFlipIso

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, flipFlipIso, flipIsColimit, ofIsoColimit, t.flipFlipIso
-/
def isColimitOfFlip (ht : IsColimit t.flip) : IsColimit t :=
  IsColimit.ofIsoColimit (flipIsColimit ht) t.flipFlipIso

end Flip

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
pushout. Given `F : WalkingSpan ⥤ C`, which is really the same as
`span (F.map fst) (F.map snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
we get a cocone on `F`.

If you're thinking about using this, have a look at `hasPushouts_of_hasColimit_span`, which
you may find to be an easier way of achieving your goal. -/
@[simps]
/--
Definition of `Cocone.ofPushoutCocone` / `Cocone.ofPushoutCocone` 的定义

English:
definition Cocone.ofPushoutCocone
  signature: {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd))
  body: t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι

中文:
定义 余锥.ofPushoutCocone
  签名: {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd))
  定义体: t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι

Depends on / 依赖: t.pt
-/
def Cocone.ofPushoutCocone {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) :
    Cocone F where
  pt := t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι
/-- Given `F : WalkingSpan ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
/--
Definition of `PushoutCocone.ofCocone` / `PushoutCocone.ofCocone` 的定义

English:
definition PushoutCocone.ofCocone
  signature: {F : WalkingSpan ⥤ C} (t : Cocone F)
  body: t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι

中文:
定义 PushoutCocone.ofCocone
  签名: {F : WalkingSpan ⥤ C} (t : 余锥 F)
  定义体: t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι

Depends on / 依赖: t.pt
-/
def PushoutCocone.ofCocone {F : WalkingSpan ⥤ C} (t : Cocone F) :
    PushoutCocone (F.map fst) (F.map snd) where
  pt := t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingSpan ⥤ C` is isomorphic to some `PushoutCocone.mk` after composing with
`diagramIsoSpan`. -/
@[simps!]
/--
Definition of `PushoutCocone.isoMk` / `PushoutCocone.isoMk` 的定义

English:
definition PushoutCocone.isoMk
  signature: {F : WalkingSpan ⥤ C} (t : Cocone F)
  body: Cocone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

中文:
定义 PushoutCocone.isoMk
  签名: {F : WalkingSpan ⥤ C} (t : 余锥 F)
  定义体: Cocone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl
-/
def PushoutCocone.isoMk {F : WalkingSpan ⥤ C} (t : Cocone F) :
    (Cocone.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
Cocone.ext (Iso.refl _) by
    rintro (_ | (_ | _)) <;> simp

end Limits

namespace CommSq
open Limits
variable {C : Type*} [Category* C]

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (s : CommSq f g h i)
  body: PullbackCone.mk _ _ s.w

中文:
定义 cone
  签名: (s : 交换Sq f g h i)
  定义体: PullbackCone.mk _ _ s.w

Depends on / 依赖: PullbackCone, PullbackCone.mk
-/
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w

/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: (s : CommSq f g h i)
  body: PushoutCocone.mk _ _ s.w

@[simp]

中文:
定义 cocone
  签名: (s : 交换Sq f g h i)
  定义体: PushoutCocone.mk _ _ s.w

@[simp]

Depends on / 依赖: PushoutCocone, PushoutCocone.mk
-/
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w

@[simp]
/--
theorem `cone_fst` / 定理 `cone_fst`

English:
theorem cone_fst
  given: (s : CommSq f g h i)
  statement: s.cone.fst = f
  proof: rfl

@[simp]

中文:
定理 cone_fst
  条件: (s : 交换Sq f g h i)
  结论: s.cone.fst = f
  证明: rfl

@[simp]
-/
theorem cone_fst (s : CommSq f g h i) : s.cone.fst = f :=
  rfl

@[simp]
/--
theorem `cone_snd` / 定理 `cone_snd`

English:
theorem cone_snd
  given: (s : CommSq f g h i)
  statement: s.cone.snd = g
  proof: rfl

@[simp]

中文:
定理 cone_snd
  条件: (s : 交换Sq f g h i)
  结论: s.cone.snd = g
  证明: rfl

@[simp]
-/
theorem cone_snd (s : CommSq f g h i) : s.cone.snd = g :=
  rfl

@[simp]
/--
theorem `cocone_inl` / 定理 `cocone_inl`

English:
theorem cocone_inl
  given: (s : CommSq f g h i)
  statement: s.cocone.inl = h
  proof: rfl

@[simp]

中文:
定理 cocone_inl
  条件: (s : 交换Sq f g h i)
  结论: s.cocone.inl = h
  证明: rfl

@[simp]
-/
theorem cocone_inl (s : CommSq f g h i) : s.cocone.inl = h :=
  rfl

@[simp]
/--
theorem `cocone_inr` / 定理 `cocone_inr`

English:
theorem cocone_inr
  given: (s : CommSq f g h i)
  statement: s.cocone.inr = i
  proof: rfl

中文:
定理 cocone_inr
  条件: (s : 交换Sq f g h i)
  结论: s.cocone.inr = i
  证明: rfl
-/
theorem cocone_inr (s : CommSq f g h i) : s.cocone.inr = i :=
  rfl

end CommSq

end CategoryTheory
