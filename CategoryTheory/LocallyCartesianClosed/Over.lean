/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# Cartesian monoidal structure on slices induced by chosen pullbacks

## Main declarations

- `cartesianMonoidalCategoryOver` provides a cartesian monoidal structure on the slice categories
  `Over X` for all objects `X : C`, induced by chosen pullbacks in the base category `C`.
  This is the computable analogue of the noncomputable instance
  `CategoryTheory.Over.cartesianMonoidalCategory`.

- For a cartesian monoidal category `C`, and for any object `X` of `C`,
  `toOver X` is a functor from `C` to `Over X` which maps an object `A : C` to the projection
  `A ⊗ X ⟶ X` in `Over X`. This is the computable analogue of the functor `Over.star`.

## Main results

- `cartesianMonoidalCategoryOver` proves that the slices of a category with chosen pullbacks are
  cartesian monoidal.

- `toOverPullbackIsoToOver` shows that in a category with chosen pullbacks, for any morphism
  `f : Y ⟶ X`, the functors `toOver X ⋙ pullback f` and `toOver Y` are naturally isomorphic.

- `toOverIteratedSliceForwardIsoPullback` shows that in a category with chosen pullbacks the functor
  `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
  `toOver (Over.mk f) : Over X ⥤ Over (Over.mk f)` post-composed with the iterated slice equivalence
  `Over (Over.mk f) ⥤ Over Y`. Note that the functor `toOver (Over.mk f)` exists by the result
  `cartesianMonoidalCategoryOver`.

### TODO

- Show that the functors `pullback f` are monoidal with respect to
  the cartesian monoidal structures on slices.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

namespace ChosenPullbacksAlong

open CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

section

open Limits

variable {X : C} (Y Z : Over X)

/--
Definition of `binaryFan` / `binaryFan` 的定义

English:
abbreviation binaryFan
  signature: [ChosenPullbacksAlong Z.hom]
  body: BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

中文:
缩写 binaryFan
  签名: [ChosenPullbacksAlong Z.hom]
  定义体: BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

Depends on / 依赖: BinaryFan, BinaryFan.mk, Over.map, Over.mk, Y.hom, Z.hom, pullback
-/
abbrev binaryFan [ChosenPullbacksAlong Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `binaryFanIsBinaryProduct` / `binaryFanIsBinaryProduct` 的定义

English:
definition binaryFanIsBinaryProduct
  signature: [ChosenPullbacksAlong Z.hom]
  body: BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

中文:
定义 binaryFanIsBinaryProduct
  签名: [ChosenPullbacksAlong Z.hom]
  定义体: BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.mk, Comma.mapRight, IsLimit, Over.homMk, Over.map, Over.w, binaryFan, cat_disch, mapRight, u.left, v.left
-/
def binaryFanIsBinaryProduct [ChosenPullbacksAlong Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A computable instance of `CartesianMonoidalCategory` for `Over X` when `C` has
chosen pullbacks. Contrast this with the noncomputable instance provided by
`CategoryTheory.Over.cartesianMonoidalCategory`.
-/
@[instance_reducible]
/--
Definition of `cartesianMonoidalCategoryOver` / `cartesianMonoidalCategoryOver` 的定义

English:
definition cartesianMonoidalCategoryOver
  signature: [ChosenPullbacks C] (X : C)
  body: ofChosenFiniteProducts (C := Over X)
    ⟨Limits.asEmptyCone (Over.mk (𝟙 X)), Limits.IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z => ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

中文:
定义 cartesianMonoidalCategoryOver
  签名: [ChosenPullbacks C] (X : C)
  定义体: ofChosenFiniteProducts (C := Over X)
    ⟨Limits.asEmptyCone (Over.mk (𝟙 X)), Limits.IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z => ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.ofUniqueHom, Limits.asEmptyCone, Over.OverMorphism.ext, Over.homMk, Over.mk, OverMorphism, Y.hom, asEmptyCone, binaryFanIsBinaryProduct, ofChosenFiniteProducts, ofUniqueHom
-/
def cartesianMonoidalCategoryOver [ChosenPullbacks C] (X : C) :
    CartesianMonoidalCategory (Over X) :=
  ofChosenFiniteProducts (C := Over X)
    ⟨Limits.asEmptyCone (Over.mk (𝟙 X)), Limits.IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z => ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

namespace Over

open MonoidalCategory

variable [ChosenPullbacks C] {X : C}

attribute [local instance] cartesianMonoidalCategoryOver

@[ext]
/--
lemma `tensorObj_ext` / 引理 `tensorObj_ext`

English:
lemma tensorObj_ext
  statement: {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y otimes Z).left)
  proof: hom_ext Y.hom Z.hom e₁ e₂

@[simp]

中文:
引理 tensorObj_ext
  结论: {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y otimes Z).left)
  证明: hom_ext Y.hom Z.hom e₁ e₂

@[simp]

Depends on / 依赖: Y.hom, Z.hom, hom_ext
-/
lemma tensorObj_ext {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y otimes Z).left)
    (e₁ : f₁ ≫ fst Y.hom Z.hom = f₂ ≫ fst Y.hom Z.hom)
    (e₂ : f₁ ≫ snd Y.hom Z.hom = f₂ ≫ snd Y.hom Z.hom) : f₁ = f₂ :=
  hom_ext Y.hom Z.hom e₁ e₂

@[simp]
/--
lemma `tensorObj_left` / 引理 `tensorObj_left`

English:
lemma tensorObj_left
  given: (Y Z : Over X)
  statement: (Y otimes Z).left = pullbackObj Y.hom Z.hom
  proof: rfl

@[simp]

中文:
引理 tensorObj_left
  条件: (Y Z : Over X)
  结论: (Y otimes Z).left = pullbackObj Y.hom Z.hom
  证明: rfl

@[simp]
-/
lemma tensorObj_left (Y Z : Over X) : (Y otimes Z).left = pullbackObj Y.hom Z.hom := rfl

@[simp]
/--
lemma `tensorObj_hom` / 引理 `tensorObj_hom`

English:
lemma tensorObj_hom
  given: (Y Z : Over X)
  statement: (Y otimes Z).hom = snd Y.hom Z.hom ≫ Z.hom
  proof: rfl

@[simp]

中文:
引理 tensorObj_hom
  条件: (Y Z : Over X)
  结论: (Y otimes Z).hom = snd Y.hom Z.hom ≫ Z.hom
  证明: rfl

@[simp]
-/
lemma tensorObj_hom (Y Z : Over X) : (Y otimes Z).hom = snd Y.hom Z.hom ≫ Z.hom := rfl

@[simp]
/--
lemma `tensorUnit_left` / 引理 `tensorUnit_left`

English:
lemma tensorUnit_left
  statement: (𝟙_ (Over X)).left = X
  proof: rfl

@[simp]

中文:
引理 tensorUnit_left
  结论: (𝟙_ (Over X)).left = X
  证明: rfl

@[simp]
-/
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
/--
lemma `tensorUnit_hom` / 引理 `tensorUnit_hom`

English:
lemma tensorUnit_hom
  statement: (𝟙_ (Over X)).hom = 𝟙 X
  proof: rfl

中文:
引理 tensorUnit_hom
  结论: (𝟙_ (Over X)).hom = 𝟙 X
  证明: rfl
-/
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

/--
lemma `fst_eq_fst'` / 引理 `fst_eq_fst'`

English:
lemma fst_eq_fst'
  given: (Y Z : Over X)
  proof: rfl

中文:
引理 fst_eq_fst'
  条件: (Y Z : Over X)
  证明: rfl
-/
lemma fst_eq_fst' (Y Z : Over X) :
    CartesianMonoidalCategory.fst Y Z = fst' Y.hom Z.hom :=
  rfl

/--
lemma `snd_eq_snd'` / 引理 `snd_eq_snd'`

English:
lemma snd_eq_snd'
  given: (Y Z : Over X)
  proof: rfl

@[simp]

中文:
引理 snd_eq_snd'
  条件: (Y Z : Over X)
  证明: rfl

@[simp]
-/
lemma snd_eq_snd' (Y Z : Over X) :
    CartesianMonoidalCategory.snd Y Z = snd' Y.hom Z.hom :=
  rfl

@[simp]
/--
lemma `lift_left` / 引理 `lift_left`

English:
lemma lift_left
  given: {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z)
  proof: rfl

@[simp]

中文:
引理 lift_left
  条件: {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z)
  证明: rfl

@[simp]
-/
lemma lift_left {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z) :
    (CartesianMonoidalCategory.lift f g).left = lift f.left g.left := rfl

@[simp]
/--
lemma `toUnit_left` / 引理 `toUnit_left`

English:
lemma toUnit_left
  given: {Z : Over X}
  statement: (toUnit Z).left = Z.hom
  proof: rfl

#adaptation_note

中文:
引理 toUnit_left
  条件: {Z : Over X}
  结论: (toUnit Z).left = Z.hom
  证明: rfl

#adaptation_note
-/
lemma toUnit_left {Z : Over X} : (toUnit Z).left = Z.hom := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_fst` / 引理 `associator_hom_left_fst`

English:
lemma associator_hom_left_fst
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_hom_fst R S T)

#adaptation_note

中文:
引理 associator_hom_left_fst
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_hom_fst R S T)

#adaptation_note

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_hom_fst, congr_arg
-/
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ fst R.hom (snd S.hom T.hom ≫ T.hom) =
      fst (R otimes S).hom T.hom ≫ fst R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_fst R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_snd_fst` / 引理 `associator_hom_left_snd_fst`

English:
lemma associator_hom_left_snd_fst
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_hom_snd_fst R S T)

@[reassoc (attr := simp)]

中文:
引理 associator_hom_left_snd_fst
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_hom_snd_fst R S T)

@[reassoc (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_hom_snd_fst, congr_arg
-/
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ fst S.hom T.hom =
      fst (R otimes S).hom T.hom ≫ snd R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_fst R S T)

@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_snd_snd` / 引理 `associator_hom_left_snd_snd`

English:
lemma associator_hom_left_snd_snd
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_hom_snd_snd R S T)

@[reassoc (attr := simp)]

中文:
引理 associator_hom_left_snd_snd
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_hom_snd_snd R S T)

@[reassoc (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_hom_snd_snd, congr_arg
-/
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ snd S.hom T.hom =
      snd (R otimes S).hom T.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_snd R S T)

@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_fst_fst` / 引理 `associator_inv_left_fst_fst`

English:
lemma associator_inv_left_fst_fst
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_inv_fst_fst R S T)

#adaptation_note

中文:
引理 associator_inv_left_fst_fst
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_inv_fst_fst R S T)

#adaptation_note

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_inv_fst_fst, congr_arg
-/
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ fst R.hom S.hom =
      fst R.hom (S otimes T).hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_fst R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_fst_snd` / 引理 `associator_inv_left_fst_snd`

English:
lemma associator_inv_left_fst_snd
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_inv_fst_snd R S T)

#adaptation_note

中文:
引理 associator_inv_left_fst_snd
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_inv_fst_snd R S T)

#adaptation_note

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_inv_fst_snd, congr_arg
-/
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ snd R.hom S.hom =
      snd R.hom (S otimes T).hom ≫ fst S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_snd R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_snd` / 引理 `associator_inv_left_snd`

English:
lemma associator_inv_left_snd
  given: (R S T : Over X)
  proof: congr_arg CommaMorphism.left (associator_inv_snd R S T)

@[simp]

中文:
引理 associator_inv_left_snd
  条件: (R S T : Over X)
  证明: congr_arg CommaMorphism.left (associator_inv_snd R S T)

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, associator_inv_snd, congr_arg
-/
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ snd (snd R.hom S.hom ≫ S.hom) T.hom =
      snd R.hom (S otimes T).hom ≫ snd S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_snd R S T)

@[simp]
/--
lemma `leftUnitor_hom_left` / 引理 `leftUnitor_hom_left`

English:
lemma leftUnitor_hom_left
  given: (Z : Over X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_hom_left
  条件: (Z : Over X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma leftUnitor_hom_left (Z : Over X) :
    (fun_ Z).hom.left = snd _ Z.hom := rfl

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_left_fst` / 引理 `leftUnitor_inv_left_fst`

English:
lemma leftUnitor_inv_left_fst
  given: (Z : Over X)
  proof: congr_arg CommaMorphism.left (leftUnitor_inv_fst Z)

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_inv_left_fst
  条件: (Z : Over X)
  证明: congr_arg CommaMorphism.left (leftUnitor_inv_fst Z)

@[reassoc (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, leftUnitor_inv_fst
-/
lemma leftUnitor_inv_left_fst (Z : Over X) :
    (fun_ Z).inv.left ≫ fst (𝟙 X) Z.hom = Z.hom :=
  congr_arg CommaMorphism.left (leftUnitor_inv_fst Z)

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_left_snd` / 引理 `leftUnitor_inv_left_snd`

English:
lemma leftUnitor_inv_left_snd
  given: (Y : Over X)
  proof: congr_arg CommaMorphism.left (leftUnitor_inv_snd Y)

@[simp]

中文:
引理 leftUnitor_inv_left_snd
  条件: (Y : Over X)
  证明: congr_arg CommaMorphism.left (leftUnitor_inv_snd Y)

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, leftUnitor_inv_snd
-/
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (fun_ Y).inv.left ≫ snd (𝟙 X) Y.hom = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (leftUnitor_inv_snd Y)

@[simp]
/--
lemma `rightUnitor_hom_left` / 引理 `rightUnitor_hom_left`

English:
lemma rightUnitor_hom_left
  given: (Y : Over X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_hom_left
  条件: (Y : Over X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_left_fst` / 引理 `rightUnitor_inv_left_fst`

English:
lemma rightUnitor_inv_left_fst
  given: (Y : Over X)
  proof: congr_arg CommaMorphism.left (rightUnitor_inv_fst Y)

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_inv_left_fst
  条件: (Y : Over X)
  证明: congr_arg CommaMorphism.left (rightUnitor_inv_fst Y)

@[reassoc (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, rightUnitor_inv_fst
-/
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ fst Y.hom (𝟙 X) = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (rightUnitor_inv_fst Y)

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_left_snd` / 引理 `rightUnitor_inv_left_snd`

English:
lemma rightUnitor_inv_left_snd
  given: (Y : Over X)
  proof: congr_arg CommaMorphism.left (rightUnitor_inv_snd Y)

中文:
引理 rightUnitor_inv_left_snd
  条件: (Y : Over X)
  证明: congr_arg CommaMorphism.left (rightUnitor_inv_snd Y)

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, rightUnitor_inv_snd
-/
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ snd Y.hom (𝟙 X) = Y.hom :=
  congr_arg CommaMorphism.left (rightUnitor_inv_snd Y)

/--
lemma `whiskerLeft_left` / 引理 `whiskerLeft_left`

English:
lemma whiskerLeft_left
  given: {R S T : Over X} (f : S ⟶ T)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_left
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullbackMap R.hom T.hom R.hom S.hom (𝟙 _) f.left (𝟙 _) :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_left_fst` / 引理 `whiskerLeft_left_fst`

English:
lemma whiskerLeft_left_fst
  given: {R S T : Over X} (f : S ⟶ T)
  proof: congr_arg CommaMorphism.left (whiskerLeft_fst R f)

#adaptation_note

中文:
引理 whiskerLeft_left_fst
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: congr_arg CommaMorphism.left (whiskerLeft_fst R f)

#adaptation_note

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, whiskerLeft_fst
-/
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ fst R.hom T.hom = fst R.hom S.hom :=
  congr_arg CommaMorphism.left (whiskerLeft_fst R f)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_left_snd` / 引理 `whiskerLeft_left_snd`

English:
lemma whiskerLeft_left_snd
  given: {R S T : Over X} (f : S ⟶ T)
  proof: congr_arg CommaMorphism.left (whiskerLeft_snd R f)

中文:
引理 whiskerLeft_left_snd
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: congr_arg CommaMorphism.left (whiskerLeft_snd R f)

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, whiskerLeft_snd
-/
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ snd R.hom T.hom = snd R.hom S.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerLeft_snd R f)

/--
lemma `whiskerRight_left` / 引理 `whiskerRight_left`

English:
lemma whiskerRight_left
  given: {R S T : Over X} (f : S ⟶ T)
  proof: rfl

#adaptation_note

中文:
引理 whiskerRight_left
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: rfl

#adaptation_note
-/
lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullbackMap T.hom R.hom S.hom R.hom f.left (𝟙 _) (𝟙 _) :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `whiskerRight_left_fst` / 引理 `whiskerRight_left_fst`

English:
lemma whiskerRight_left_fst
  given: {R S T : Over X} (f : S ⟶ T)
  proof: congr_arg CommaMorphism.left (whiskerRight_fst f R)

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_left_fst
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: congr_arg CommaMorphism.left (whiskerRight_fst f R)

@[reassoc (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, whiskerRight_fst
-/
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ fst T.hom R.hom = fst S.hom R.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerRight_fst f R)

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_left_snd` / 引理 `whiskerRight_left_snd`

English:
lemma whiskerRight_left_snd
  given: {R S T : Over X} (f : S ⟶ T)
  proof: congr_arg CommaMorphism.left (whiskerRight_snd f R)

中文:
引理 whiskerRight_left_snd
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: congr_arg CommaMorphism.left (whiskerRight_snd f R)

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, whiskerRight_snd
-/
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ snd T.hom R.hom = snd S.hom R.hom :=
  congr_arg CommaMorphism.left (whiskerRight_snd f R)

/--
lemma `tensorHom_left` / 引理 `tensorHom_left`

English:
lemma tensorHom_left
  given: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  proof: rfl

#adaptation_note

中文:
引理 tensorHom_left
  条件: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  证明: rfl

#adaptation_note
-/
lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f otimesₘ g).left = pullbackMap S.hom U.hom R.hom T.hom f.left g.left (𝟙 _) :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `tensorHom_left_fst` / 引理 `tensorHom_left_fst`

English:
lemma tensorHom_left_fst
  given: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  proof: congr_arg CommaMorphism.left (tensorHom_fst f g)

#adaptation_note

中文:
引理 tensorHom_left_fst
  条件: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  证明: congr_arg CommaMorphism.left (tensorHom_fst f g)

#adaptation_note

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, tensorHom_fst
-/
lemma tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f otimesₘ g).left ≫ fst S.hom U.hom = fst R.hom T.hom ≫ f.left :=
  congr_arg CommaMorphism.left (tensorHom_fst f g)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `tensorHom_left_snd` / 引理 `tensorHom_left_snd`

English:
lemma tensorHom_left_snd
  given: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  proof: congr_arg CommaMorphism.left (tensorHom_snd f g)

中文:
引理 tensorHom_left_snd
  条件: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  证明: congr_arg CommaMorphism.left (tensorHom_snd f g)

Depends on / 依赖: CommaMorphism, CommaMorphism.left, congr_arg, tensorHom_snd
-/
lemma tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f otimesₘ g).left ≫ snd S.hom U.hom = snd R.hom T.hom ≫ g.left :=
  congr_arg CommaMorphism.left (tensorHom_snd f g)

end Over

end ChosenPullbacksAlong

section ToOver

open ChosenPullbacksAlong CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

set_option backward.defeqAttrib.useBackward true in
/-- The functor which maps an object `A` in `C` to the projection `A ⊗ X ⟶ X` in `Over X`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom]
/--
Definition of `toOver` / `toOver` 的定义

English:
definition toOver
  signature: (X : C)
  body: Over.mk CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

中文:
定义 toOver
  签名: (X : C)
  定义体: Over.mk CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.snd, Over.mk
-/
def toOver (X : C) : C ⥤ Over X where
obj A := Over.mk CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `toOver_map` / 引理 `toOver_map`

English:
lemma toOver_map
  given: {X : C} {A A' : C} (f : A ⟶ A')
  proof: by
  simp [toOver]

中文:
引理 toOver_map
  条件: {X : C} {A A' : C} (f : A ⟶ A')
  证明: by
  simp [toOver]

Depends on / 依赖: toOver
-/
lemma toOver_map {X : C} {A A' : C} (f : A ⟶ A') :
    (toOver X).map f = Over.homMk (f ▷ X) := by
  simp [toOver]

variable (C)

/-- The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit X`. -/
@[simps! obj_left obj_hom map_left]
/--
Definition of `toOverUnit` / `toOverUnit` 的定义

English:
definition toOverUnit
  signature: : C ⥤ Over (𝟙_ C) where
  body: Over.mk toUnit X
  map f := Over.homMk f

中文:
定义 toOverUnit
  签名: : C ⥤ Over (𝟙_ C) where
  定义体: Over.mk toUnit X
  map f := Over.homMk f

Depends on / 依赖: Over.mk, toUnit
-/
def toOverUnit : C ⥤ Over (𝟙_ C) where
obj X := Over.mk toUnit X
  map f := Over.homMk f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The slice category over the terminal unit object is equivalent to the original category. -/
@[simps]
/--
Definition of `equivToOverUnit` / `equivToOverUnit` 的定义

English:
definition equivToOverUnit
  signature: : Over (𝟙_ C) ≌ C where
  body: Over.forget _
  inverse := toOverUnit _
  unitIso := NatIso.ofComponents fun X => Over.isoMk (Iso.refl _)
  counitIso := NatIso.ofComponents fun X => Iso.refl _

中文:
定义 equivToOverUnit
  签名: : Over (𝟙_ C) ≌ C where
  定义体: Over.forget _
  inverse := toOverUnit _
  unitIso := NatIso.ofComponents fun X => Over.isoMk (Iso.refl _)
  counitIso := NatIso.ofComponents fun X => Iso.refl _

Depends on / 依赖: Over.forget, forget
-/
def equivToOverUnit : Over (𝟙_ C) ≌ C where
  functor := Over.forget _
  inverse := toOverUnit _
  unitIso := NatIso.ofComponents fun X => Over.isoMk (Iso.refl _)
  counitIso := NatIso.ofComponents fun X => Iso.refl _

variable {C}

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryToUnit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of functors `toOverUnit C ⋙ ChosenPullbacksAlong.pullback (toUnit X)` and
`toOver X`. -/
@[simps!]
/--
Definition of `toOverUnitPullback` / `toOverUnitPullback` 的定义

English:
definition toOverUnitPullback
  signature: (X : C)
  body: NatIso.ofComponents fun X => Iso.refl _

中文:
定义 toOverUnitPullback
  签名: (X : C)
  定义体: NatIso.ofComponents fun X => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def toOverUnitPullback (X : C) :
    toOverUnit C ⋙ pullback (toUnit X) ≅ toOver X :=
  NatIso.ofComponents fun X => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `toOver X` is the right adjoint to the functor `Over.forget X`. -/
@[simps! unit_app counit_app]
/--
Definition of `forgetAdjToOver` / `forgetAdjToOver` 的定义

English:
definition forgetAdjToOver
  signature: (X : C)
  body: Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X

中文:
定义 forgetAdjToOver
  签名: (X : C)
  定义体: Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X

Depends on / 依赖: Over.homMk, Z.hom, Z.left
-/
def forgetAdjToOver (X : C) : Over.forget X ⊣ toOver X where
  unit.app Z := Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X

/--
theorem `forgetAdjToOver.homEquiv_symm` / 定理 `forgetAdjToOver.homEquiv_symm`

English:
theorem forgetAdjToOver.homEquiv_symm
  given: {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A)
  proof: by
  rw [Adjunction.homEquiv_counit]; rw [forgetAdjToOver_counit_app]
  simp

中文:
定理 forgetAdjToOver.homEquiv_symm
  条件: {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A)
  证明: by
  rw [Adjunction.homEquiv_counit]; rw [forgetAdjToOver_counit_app]
  simp

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, forgetAdjToOver_counit_app, homEquiv_counit
-/
theorem forgetAdjToOver.homEquiv_symm {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A) :
    ((forgetAdjToOver X).homEquiv Z A).symm f = f.left ≫ (fst _ _) := by
  rw [Adjunction.homEquiv_counit]; rw [forgetAdjToOver_counit_app]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`. -/
@[simps!]
/--
Definition of `toOverIsoToOverUnit` / `toOverIsoToOverUnit` 的定义

English:
definition toOverIsoToOverUnit
  signature: : toOver (𝟙_ C) ≅ toOverUnit C
  body: (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

#adaptation_note

中文:
定义 toOverIsoToOverUnit
  签名: : toOver (𝟙_ C) ≅ toOverUnit C
  定义体: (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

#adaptation_note

Depends on / 依赖: equivToOverUnit, forgetAdjToOver, rightAdjointUniq, toAdjunction
-/
def toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C :=
  (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism between the functors `toOver Y` and `toOver X ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
@[simps!]
/--
Definition of `toOverPullbackIsoToOver` / `toOverPullbackIsoToOver` 的定义

English:
definition toOverPullbackIsoToOver
  signature: {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f]
  body: conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

中文:
定义 toOverPullbackIsoToOver
  签名: {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f]
  定义体: conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

Depends on / 依赖: Over.mapForget, conjugateIsoEquiv, forgetAdjToOver, mapForget, mapPullbackAdj
-/
def toOverPullbackIsoToOver {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f] :
    toOver X ⋙ pullback f ≅ toOver Y :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

attribute [local instance] cartesianMonoidalCategoryOver

set_option backward.isDefEq.respectTransparency.types false in
omit [CartesianMonoidalCategory C] in
/-- The functor `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
`toOver : Over X ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivalence `Over (Over.mk f) ⥤ Over Y`. -/
@[simps!]
/--
Definition of `toOverIteratedSliceForwardIsoPullback` / `toOverIteratedSliceForwardIsoPullback` 的定义

English:
definition toOverIteratedSliceForwardIsoPullback
  signature: [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X)
  body: conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

中文:
定义 toOverIteratedSliceForwardIsoPullback
  签名: [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X)
  定义体: conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

Depends on / 依赖: Over.iteratedSliceBackward_forget, Over.mk, conjugateIsoEquiv, eqToIso, forgetAdjToOver, iteratedSliceBackward_forget, iteratedSliceEquiv, iteratedSliceEquiv.symm.toAdjunction.comp, mapPullbackAdj, toAdjunction
-/
def toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X) :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

end ToOver

end CategoryTheory
