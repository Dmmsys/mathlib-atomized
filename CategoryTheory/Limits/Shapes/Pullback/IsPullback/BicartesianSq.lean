/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Bi-Cartesian squares

`BicartesianSq f g h i` is the proposition that
```
  W ---f---> X
  | |
  g h
  | |
  v v
  Y ---i---> Z

```
is a pullback square *and* a pushout square.

We show that the pullback and pushout squares for a biproduct are bi-Cartesian.
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
Definition of `BicartesianSq` / `BicartesianSq` 的定义

English:
structure BicartesianSq
  parameters: {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  extends: IsPullback f g h i, IsPushout f g h i
  (no additional axioms)

中文:
结构 BicartesianSq
  参数: {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  继承: 是拉回 f g h i, 是推出 f g h i
  (无附加公理)
-/
structure BicartesianSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop
    extends IsPullback f g h i, IsPushout f g h i


variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
theorem `of_hasBinaryProduct` / 定理 `of_hasBinaryProduct`

English:
theorem of_hasBinaryProduct
  given: [HasBinaryProduct X Y]
  proof: by
  convert! @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton

中文:
定理 of_hasBinaryProduct
  条件: [HasBinaryProduct X Y]
  证明: by
  convert! @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsTerminal, convert, isLimit, limit.isLimit, of_is_product, subsingleton, zeroIsTerminal
-/
theorem of_hasBinaryProduct [HasBinaryProduct X Y] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: (X : C)
  statement: IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)
  proof: { w := by simp
    isLimit' :=
      ⟨{ lift := fun _ => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }

中文:
定理 zero_left
  条件: (X : C)
  结论: 是拉回 (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)
  证明: { w := by simp
    isLimit' :=
      ⟨{ lift := fun _ => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }

Depends on / 依赖: A.hom, A.prop, HasPushoutsAlong, HasPushoutsAlong.hasPushout, PullbackCone, PullbackCone.condition, PullbackCone.equalizer_ext, condition, eq_iff_true_of_subsingleton, equalizer_ext, hasPushout, isLimit
-/
theorem zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  { w := by simp
    isLimit' :=
      ⟨{ lift := fun _ => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
@[simp]
/--
theorem `zero_top` / 定理 `zero_top`

English:
theorem zero_top
  given: (X : C)
  statement: IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X)
  proof: (zero_left X).flip

中文:
定理 zero_top
  条件: (X : C)
  结论: 是拉回 (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X)
  证明: (zero_left X).flip

Depends on / 依赖: A.hom, A.prop, HasPushoutsAlong, HasPushoutsAlong.hasPushout, IsPushout, IsPushout.of_hasPushout, IsStableUnderCobaseChangeAlong, IsStableUnderCobaseChangeAlong.of_isPushout, hasPushout, of_hasPushout, of_isPushout, pushout, pushout.inr, zero_left
-/
theorem zero_top (X : C) : IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pullback square. -/
@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (X : C)
  statement: IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)
  proof: of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)

中文:
定理 zero_right
  条件: (X : C)
  结论: 是拉回 (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)
  证明: of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)

Depends on / 依赖: eq_iff_true_of_subsingleton, of_iso_pullback, pullbackZeroZeroIso, zeroProdIso
-/
theorem zero_right (X : C) : IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pullback square. -/
@[simp]
/--
theorem `zero_bot` / 定理 `zero_bot`

English:
theorem zero_bot
  given: (X : C)
  statement: IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0)
  proof: (zero_right X).flip

中文:
定理 zero_bot
  条件: (X : C)
  结论: 是拉回 (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0)
  证明: (zero_right X).flip

Depends on / 依赖: zero_right
-/
theorem zero_bot (X : C) : IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip

/--
theorem `of_isBilimit` / 定理 `of_isBilimit`

English:
theorem of_isBilimit
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  convert! IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> subsingleton

@[simp]

中文:
定理 of_isBilimit
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  convert! IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> subsingleton

@[simp]

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsTerminal, IsPullback, IsPullback.of_is_product, convert, h.isLimit, isLimit, of_is_product, subsingleton, zeroIsTerminal
-/
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> subsingleton

@[simp]
/--
theorem `of_has_biproduct` / 定理 `of_has_biproduct`

English:
theorem of_has_biproduct
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: of_isBilimit (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_has_biproduct
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: of_isBilimit (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, isBilimit, of_isBilimit
-/
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)

/--
theorem `inl_snd'` / 定理 `inl_snd'`

English:
theorem inl_snd'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp

中文:
定理 inl_snd'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp

Depends on / 依赖: of_isBilimit, of_right
-/
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  X --inl--> X ⊞ Y
  | |
  0 snd
  | |
  v v
  0 ---0-----> Y
```
is a pullback square.
-/
@[simp]
/--
theorem `inl_snd` / 定理 `inl_snd`

English:
theorem inl_snd
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: inl_snd' (BinaryBiproduct.isBilimit X Y)

中文:
定理 inl_snd
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: inl_snd' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, inl_snd, isBilimit
-/
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)

/--
theorem `inr_fst'` / 定理 `inr_fst'`

English:
theorem inr_fst'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp

中文:
定理 inr_fst'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp

Depends on / 依赖: Under.mapPushoutAdj, isRightAdjoint, mapPushoutAdj, of_bot, of_isBilimit
-/
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  Y --inr--> X ⊞ Y
  | |
  0 fst
  | |
  v v
  0 ---0-----> X
```
is a pullback square.
-/
@[simp]
/--
theorem `inr_fst` / 定理 `inr_fst`

English:
theorem inr_fst
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: inr_fst' (BinaryBiproduct.isBilimit X Y)

中文:
定理 inr_fst
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: inr_fst' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, inr_fst, isBilimit
-/
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)

/--
theorem `of_is_bilimit'` / 定理 `of_is_bilimit'`

English:
theorem of_is_bilimit'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp

中文:
定理 of_is_bilimit'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp

Depends on / 依赖: IsPullback, IsPullback.inl_snd, IsPullback.of_right, inl_snd, of_right
-/
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp

/--
theorem `of_hasBinaryBiproduct` / 定理 `of_hasBinaryBiproduct`

English:
theorem of_hasBinaryBiproduct
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_hasBinaryBiproduct
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, isBilimit, of_is_bilimit
-/
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

/--
Instance `hasPullback_biprod_fst_biprod_snd` / 实例 `hasPullback_biprod_fst_biprod_snd`

English:
instance hasPullback_biprod_fst_biprod_snd
  signature: [HasBinaryBiproduct X Y]
  body: HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

中文:
实例 hasPullback_biprod_fst_biprod_snd
  签名: [有BinaryBiproduct X Y]
  定义体: HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

Depends on / 依赖: HasLimit, HasLimit.mk, isLimit, of_hasBinaryBiproduct
-/
instance hasPullback_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) :=
  HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

/--
Definition of `pullbackBiprodInlBiprodInr` / `pullbackBiprodInlBiprodInr` 的定义

English:
definition pullbackBiprodInlBiprodInr
  signature: [HasBinaryBiproduct X Y]
  body: limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

中文:
定义 pullbackBiprodInlBiprodInr
  签名: [有BinaryBiproduct X Y]
  定义体: limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

Depends on / 依赖: isLimit, isoLimitCone, limit.isoLimitCone, of_hasBinaryBiproduct
-/
def pullbackBiprodInlBiprodInr [HasBinaryBiproduct X Y] :
    pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0 :=
  limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
theorem `of_hasBinaryCoproduct` / 定理 `of_hasBinaryCoproduct`

English:
theorem of_hasBinaryCoproduct
  given: [HasBinaryCoproduct X Y]
  proof: by
  convert! @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> subsingleton

中文:
定理 of_hasBinaryCoproduct
  条件: [HasBinaryCoproduct X Y]
  证明: by
  convert! @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> subsingleton

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsInitial, colimit, colimit.isColimit, convert, isColimit, of_is_coproduct, subsingleton, zeroIsInitial
-/
theorem of_hasBinaryCoproduct [HasBinaryCoproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr := by
  convert! @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> subsingleton

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (X : C)
  statement: IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)
  proof: { w := by simp
    isColimit' :=
      ⟨{ desc := fun _ => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp 

中文:
定理 zero_right
  条件: (X : C)
  结论: 是推出 (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)
  证明: { w := by simp
    isColimit' :=
      ⟨{ desc := fun _ => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp 

Depends on / 依赖: PushoutCocone, PushoutCocone.coequalizer_ext, PushoutCocone.condition, coequalizer_ext, condition, eq_iff_true_of_subsingleton, isColimit
-/
theorem zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  { w := by simp
    isColimit' :=
      ⟨{ desc := fun _ => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp at c
            simpa using c }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout square. -/
@[simp]
/--
theorem `zero_bot` / 定理 `zero_bot`

English:
theorem zero_bot
  given: (X : C)
  statement: IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0)
  proof: (zero_right X).flip

中文:
定理 zero_bot
  条件: (X : C)
  结论: 是推出 (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0)
  证明: (zero_right X).flip

Depends on / 依赖: zero_right
-/
theorem zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip

/-- The square with `0 : 0 ⟶ 0` on the right left `𝟙 X` on the right is a pushout square. -/
@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: (X : C)
  statement: IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)
  proof: of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])

中文:
定理 zero_left
  条件: (X : C)
  结论: 是推出 (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)
  证明: of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])

Depends on / 依赖: coprodZeroIso, eq_iff_true_of_subsingleton, of_iso_pushout, pushoutZeroZeroIso
-/
theorem zero_left (X : C) : IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pushout square. -/
@[simp]
/--
theorem `zero_top` / 定理 `zero_top`

English:
theorem zero_top
  given: (X : C)
  statement: IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X)
  proof: (zero_left X).flip

中文:
定理 zero_top
  条件: (X : C)
  结论: 是推出 (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X)
  证明: (zero_left X).flip

Depends on / 依赖: zero_left
-/
theorem zero_top (X : C) : IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip


/--
theorem `of_isBilimit` / 定理 `of_isBilimit`

English:
theorem of_isBilimit
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  convert! IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> subsingleton

@[simp]

中文:
定理 of_isBilimit
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  convert! IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> subsingleton

@[simp]

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsInitial, IsPushout, IsPushout.of_is_coproduct, convert, h.isColimit, isColimit, of_is_coproduct, subsingleton, zeroIsInitial
-/
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  convert! IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> subsingleton

@[simp]
/--
theorem `of_has_biproduct` / 定理 `of_has_biproduct`

English:
theorem of_has_biproduct
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: of_isBilimit (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_has_biproduct
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: of_isBilimit (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, isBilimit, of_isBilimit
-/
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)

/--
theorem `inl_snd'` / 定理 `inl_snd'`

English:
theorem inl_snd'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  apply flip
  refine of_left ?_ (by simp) (of_isBilimit h)
  simp

中文:
定理 inl_snd'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  apply flip
  refine of_left ?_ (by simp) (of_isBilimit h)
  simp

Depends on / 依赖: of_isBilimit, of_left
-/
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  apply flip
  refine of_left ?_ (by simp) (of_isBilimit h)
  simp

/--
theorem `inl_snd` / 定理 `inl_snd`

English:
theorem inl_snd
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: inl_snd' (BinaryBiproduct.isBilimit X Y)

中文:
定理 inl_snd
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: inl_snd' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, inl_snd, isBilimit
-/
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)

/--
theorem `inr_fst'` / 定理 `inr_fst'`

English:
theorem inr_fst'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  refine of_top ?_ (by simp) (of_isBilimit h)
  simp

中文:
定理 inr_fst'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  refine of_top ?_ (by simp) (of_isBilimit h)
  simp

Depends on / 依赖: of_isBilimit, of_top
-/
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  refine of_top ?_ (by simp) (of_isBilimit h)
  simp

/--
theorem `inr_fst` / 定理 `inr_fst`

English:
theorem inr_fst
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: inr_fst' (BinaryBiproduct.isBilimit X Y)

中文:
定理 inr_fst
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: inr_fst' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, inr_fst, isBilimit
-/
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)

/--
theorem `of_is_bilimit'` / 定理 `of_is_bilimit'`

English:
theorem of_is_bilimit'
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: by
  refine IsPushout.of_left ?_ (by simp) (IsPushout.inl_snd' h)
  simp

中文:
定理 of_is_bilimit'
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: by
  refine IsPushout.of_left ?_ (by simp) (IsPushout.inl_snd' h)
  simp

Depends on / 依赖: IsPushout, IsPushout.inl_snd, IsPushout.of_left, inl_snd, of_left
-/
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  refine IsPushout.of_left ?_ (by simp) (IsPushout.inl_snd' h)
  simp

/--
theorem `of_hasBinaryBiproduct` / 定理 `of_hasBinaryBiproduct`

English:
theorem of_hasBinaryBiproduct
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_hasBinaryBiproduct
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, isBilimit, of_is_bilimit
-/
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)

/--
Instance `hasPushout_biprod_fst_biprod_snd` / 实例 `hasPushout_biprod_fst_biprod_snd`

English:
instance hasPushout_biprod_fst_biprod_snd
  signature: [HasBinaryBiproduct X Y]
  body: HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

中文:
实例 hasPushout_biprod_fst_biprod_snd
  签名: [有BinaryBiproduct X Y]
  定义体: HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

Depends on / 依赖: HasColimit, HasColimit.mk, isColimit, of_hasBinaryBiproduct
-/
instance hasPushout_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) :=
  HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

/--
Definition of `pushoutBiprodFstBiprodSnd` / `pushoutBiprodFstBiprodSnd` 的定义

English:
definition pushoutBiprodFstBiprodSnd
  signature: [HasBinaryBiproduct X Y]
  body: colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

中文:
定义 pushoutBiprodFstBiprodSnd
  签名: [有BinaryBiproduct X Y]
  定义体: colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isColimit, isoColimitCocone, of_hasBinaryBiproduct
-/
def pushoutBiprodFstBiprodSnd [HasBinaryBiproduct X Y] :
    pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0 :=
  colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

end IsPushout

namespace BicartesianSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

omit [HasZeroObject C] [HasZeroMorphisms C] in
section

/--
theorem `of_isPullback_isPushout` / 定理 `of_isPullback_isPushout`

English:
theorem of_isPullback_isPushout
  given: (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i)
  proof: BicartesianSq.mk p₁ p₂.isColimit'

中文:
定理 of_isPullback_isPushout
  条件: (p₁ : 是拉回 f g h i) (p₂ : 是推出 f g h i)
  证明: BicartesianSq.mk p₁ p₂.isColimit'

Depends on / 依赖: BicartesianSq, BicartesianSq.mk, isColimit
-/
theorem of_isPullback_isPushout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.mk p₁ p₂.isColimit'

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (p : BicartesianSq f g h i)
  statement: BicartesianSq g f i h
  proof: of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip

中文:
定理 flip
  条件: (p : BicartesianSq f g h i)
  结论: BicartesianSq g f i h
  证明: of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip

Depends on / 依赖: of_isPullback_isPushout, p.toIsPullback.flip, p.toIsPushout.flip, toIsPullback, toIsPushout
-/
theorem flip (p : BicartesianSq f g h i) : BicartesianSq g f i h :=
  of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip

end


/--
theorem `of_is_biproduct₁` / 定理 `of_is_biproduct₁`

English:
theorem of_is_biproduct₁
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)

中文:
定理 of_is_biproduct₁
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)

Depends on / 依赖: F.map_injective, IsPullback, IsPullback.of_isBilimit, IsPushout, IsPushout.of_is_bilimit, map_injective, of_isBilimit, of_isPullback_isPushout, of_is_bilimit
-/
theorem of_is_biproduct₁ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)

/--
theorem `of_is_biproduct₂` / 定理 `of_is_biproduct₂`

English:
theorem of_is_biproduct₂
  given: {b : BinaryBicone X Y} (h : b.IsBilimit)
  proof: of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)

中文:
定理 of_is_biproduct₂
  条件: {b : BinaryBicone X Y} (h : b.是Bilimit)
  证明: of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)

Depends on / 依赖: IsPullback, IsPullback.of_is_bilimit, IsPushout, IsPushout.of_isBilimit, of_isBilimit, of_isPullback_isPushout, of_is_bilimit
-/
theorem of_is_biproduct₂ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
  of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)

/-- ```
 X ⊞ Y --fst--> X
   | |
  snd 0
   | |
   v v
   Y -----0---> 0
```
is a bi-Cartesian square.
-/
@[simp]
/--
theorem `of_has_biproduct₁` / 定理 `of_has_biproduct₁`

English:
theorem of_has_biproduct₁
  given: [HasBinaryBiproduct X Y]
  proof: by
  convert! of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_has_biproduct₁
  条件: [有BinaryBiproduct X Y]
  证明: by
  convert! of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, convert, isBilimit
-/
theorem of_has_biproduct₁ [HasBinaryBiproduct X Y] :
    BicartesianSq biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)

/-- ```
   0 -----0---> X
   | |
   0 inl
   | |
   v v
   Y --inr--> X ⊞ Y
```
is a bi-Cartesian square.
-/
@[simp]
/--
theorem `of_has_biproduct₂` / 定理 `of_has_biproduct₂`

English:
theorem of_has_biproduct₂
  given: [HasBinaryBiproduct X Y]
  proof: by
  convert! of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)

中文:
定理 of_has_biproduct₂
  条件: [有BinaryBiproduct X Y]
  证明: by
  convert! of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, convert, isBilimit
-/
theorem of_has_biproduct₂ [HasBinaryBiproduct X Y] :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
  convert! of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)

end BicartesianSq
end CategoryTheory
