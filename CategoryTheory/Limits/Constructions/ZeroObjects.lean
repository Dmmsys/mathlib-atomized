/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

/-!
# Limits involving zero objects

Binary products and coproducts with a zero object always exist,
and pullbacks/pushouts over a zero object are products/coproducts.
-/

@[expose] public section


noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/--
Definition of `binaryFanZeroLeft` / `binaryFanZeroLeft` 的定义

English:
definition binaryFanZeroLeft
  signature: (X : C)
  body: BinaryFan.mk 0 (𝟙 X)

中文:
定义 binaryFanZeroLeft
  签名: (X : C)
  定义体: BinaryFan.mk 0 (𝟙 X)

Depends on / 依赖: BinaryFan, BinaryFan.mk
-/
def binaryFanZeroLeft (X : C) : BinaryFan (0 : C) X :=
  BinaryFan.mk 0 (𝟙 X)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryFanZeroLeftIsLimit` / `binaryFanZeroLeftIsLimit` 的定义

English:
definition binaryFanZeroLeftIsLimit
  signature: (X : C)
  body: BinaryFan.isLimitMk (fun s => BinaryFan.snd s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

中文:
定义 binaryFanZeroLeftIsLimit
  签名: (X : C)
  定义体: BinaryFan.isLimitMk (fun s => BinaryFan.snd s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

Depends on / 依赖: BinaryFan, BinaryFan.isLimitMk, BinaryFan.snd, cat_disch, isLimitMk
-/
def binaryFanZeroLeftIsLimit (X : C) : IsLimit (binaryFanZeroLeft X) :=
  BinaryFan.isLimitMk (fun s => BinaryFan.snd s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

/--
Instance `hasBinaryProduct_zero_left` / 实例 `hasBinaryProduct_zero_left`

English:
instance hasBinaryProduct_zero_left
  signature: (X : C)
  body: HasLimit.mk ⟨_, binaryFanZeroLeftIsLimit X⟩

中文:
实例 hasBinaryProduct_zero_left
  签名: (X : C)
  定义体: HasLimit.mk ⟨_, binaryFanZeroLeftIsLimit X⟩

Depends on / 依赖: HasLimit, HasLimit.mk, binaryFanZeroLeftIsLimit
-/
instance hasBinaryProduct_zero_left (X : C) : HasBinaryProduct (0 : C) X :=
  HasLimit.mk ⟨_, binaryFanZeroLeftIsLimit X⟩

/--
Definition of `zeroProdIso` / `zeroProdIso` 的定义

English:
definition zeroProdIso
  signature: (X : C)
  body: limit.isoLimitCone ⟨_, binaryFanZeroLeftIsLimit X⟩

@[simp]

中文:
定义 zeroProdIso
  签名: (X : C)
  定义体: limit.isoLimitCone ⟨_, binaryFanZeroLeftIsLimit X⟩

@[simp]

Depends on / 依赖: binaryFanZeroLeftIsLimit, isoLimitCone, limit.isoLimitCone
-/
def zeroProdIso (X : C) : (0 : C) ⨯ X ≅ X :=
  limit.isoLimitCone ⟨_, binaryFanZeroLeftIsLimit X⟩

@[simp]
/--
theorem `zeroProdIso_hom` / 定理 `zeroProdIso_hom`

English:
theorem zeroProdIso_hom
  given: (X : C)
  statement: (zeroProdIso X).hom = prod.snd
  proof: rfl

中文:
定理 zeroProdIso_hom
  条件: (X : C)
  结论: (zeroProdIso X).hom = prod.snd
  证明: rfl
-/
theorem zeroProdIso_hom (X : C) : (zeroProdIso X).hom = prod.snd :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `zeroProdIso_inv_snd` / 定理 `zeroProdIso_inv_snd`

English:
theorem zeroProdIso_inv_snd
  given: (X : C)
  statement: (zeroProdIso X).inv ≫ prod.snd = 𝟙 X
  proof: by
  dsimp [zeroProdIso, binaryFanZeroLeft]
  simp

中文:
定理 zeroProdIso_inv_snd
  条件: (X : C)
  结论: (zeroProdIso X).inv ≫ prod.snd = 𝟙 X
  证明: by
  dsimp [zeroProdIso, binaryFanZeroLeft]
  simp

Depends on / 依赖: binaryFanZeroLeft, zeroProdIso
-/
theorem zeroProdIso_inv_snd (X : C) : (zeroProdIso X).inv ≫ prod.snd = 𝟙 X := by
  dsimp [zeroProdIso, binaryFanZeroLeft]
  simp

/--
Definition of `binaryFanZeroRight` / `binaryFanZeroRight` 的定义

English:
definition binaryFanZeroRight
  signature: (X : C)
  body: BinaryFan.mk (𝟙 X) 0

中文:
定义 binaryFanZeroRight
  签名: (X : C)
  定义体: BinaryFan.mk (𝟙 X) 0

Depends on / 依赖: BinaryFan, BinaryFan.mk
-/
def binaryFanZeroRight (X : C) : BinaryFan X (0 : C) :=
  BinaryFan.mk (𝟙 X) 0

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryFanZeroRightIsLimit` / `binaryFanZeroRightIsLimit` 的定义

English:
definition binaryFanZeroRightIsLimit
  signature: (X : C)
  body: BinaryFan.isLimitMk (fun s => BinaryFan.fst s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

中文:
定义 binaryFanZeroRightIsLimit
  签名: (X : C)
  定义体: BinaryFan.isLimitMk (fun s => BinaryFan.fst s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

Depends on / 依赖: BinaryFan, BinaryFan.fst, BinaryFan.isLimitMk, cat_disch, isLimitMk
-/
def binaryFanZeroRightIsLimit (X : C) : IsLimit (binaryFanZeroRight X) :=
  BinaryFan.isLimitMk (fun s => BinaryFan.fst s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

/--
Instance `hasBinaryProduct_zero_right` / 实例 `hasBinaryProduct_zero_right`

English:
instance hasBinaryProduct_zero_right
  signature: (X : C)
  body: HasLimit.mk ⟨_, binaryFanZeroRightIsLimit X⟩

中文:
实例 hasBinaryProduct_zero_right
  签名: (X : C)
  定义体: HasLimit.mk ⟨_, binaryFanZeroRightIsLimit X⟩

Depends on / 依赖: HasLimit, HasLimit.mk, binaryFanZeroRightIsLimit
-/
instance hasBinaryProduct_zero_right (X : C) : HasBinaryProduct X (0 : C) :=
  HasLimit.mk ⟨_, binaryFanZeroRightIsLimit X⟩

/--
Definition of `prodZeroIso` / `prodZeroIso` 的定义

English:
definition prodZeroIso
  signature: (X : C)
  body: limit.isoLimitCone ⟨_, binaryFanZeroRightIsLimit X⟩

@[simp]

中文:
定义 prodZeroIso
  签名: (X : C)
  定义体: limit.isoLimitCone ⟨_, binaryFanZeroRightIsLimit X⟩

@[simp]

Depends on / 依赖: binaryFanZeroRightIsLimit, isoLimitCone, limit.isoLimitCone
-/
def prodZeroIso (X : C) : X ⨯ (0 : C) ≅ X :=
  limit.isoLimitCone ⟨_, binaryFanZeroRightIsLimit X⟩

@[simp]
/--
theorem `prodZeroIso_hom` / 定理 `prodZeroIso_hom`

English:
theorem prodZeroIso_hom
  given: (X : C)
  statement: (prodZeroIso X).hom = prod.fst
  proof: rfl

中文:
定理 prodZeroIso_hom
  条件: (X : C)
  结论: (prodZeroIso X).hom = prod.fst
  证明: rfl
-/
theorem prodZeroIso_hom (X : C) : (prodZeroIso X).hom = prod.fst :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prodZeroIso_iso_inv_snd` / 定理 `prodZeroIso_iso_inv_snd`

English:
theorem prodZeroIso_iso_inv_snd
  given: (X : C)
  statement: (prodZeroIso X).inv ≫ prod.fst = 𝟙 X
  proof: by
  dsimp [prodZeroIso, binaryFanZeroRight]
  simp

中文:
定理 prodZeroIso_iso_inv_snd
  条件: (X : C)
  结论: (prodZeroIso X).inv ≫ prod.fst = 𝟙 X
  证明: by
  dsimp [prodZeroIso, binaryFanZeroRight]
  simp

Depends on / 依赖: binaryFanZeroRight, prodZeroIso
-/
theorem prodZeroIso_iso_inv_snd (X : C) : (prodZeroIso X).inv ≫ prod.fst = 𝟙 X := by
  dsimp [prodZeroIso, binaryFanZeroRight]
  simp

/--
Definition of `binaryCofanZeroLeft` / `binaryCofanZeroLeft` 的定义

English:
definition binaryCofanZeroLeft
  signature: (X : C)
  body: BinaryCofan.mk 0 (𝟙 X)

中文:
定义 binaryCofanZeroLeft
  签名: (X : C)
  定义体: BinaryCofan.mk 0 (𝟙 X)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk
-/
def binaryCofanZeroLeft (X : C) : BinaryCofan (0 : C) X :=
  BinaryCofan.mk 0 (𝟙 X)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryCofanZeroLeftIsColimit` / `binaryCofanZeroLeftIsColimit` 的定义

English:
definition binaryCofanZeroLeftIsColimit
  signature: (X : C)
  body: BinaryCofan.isColimitMk (fun s => BinaryCofan.inr s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

中文:
定义 binaryCofanZeroLeftIsColimit
  签名: (X : C)
  定义体: BinaryCofan.isColimitMk (fun s => BinaryCofan.inr s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

Depends on / 依赖: BinaryCofan, BinaryCofan.inr, BinaryCofan.isColimitMk, cat_disch, isColimitMk
-/
def binaryCofanZeroLeftIsColimit (X : C) : IsColimit (binaryCofanZeroLeft X) :=
  BinaryCofan.isColimitMk (fun s => BinaryCofan.inr s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

/--
Instance `hasBinaryCoproduct_zero_left` / 实例 `hasBinaryCoproduct_zero_left`

English:
instance hasBinaryCoproduct_zero_left
  signature: (X : C)
  body: HasColimit.mk ⟨_, binaryCofanZeroLeftIsColimit X⟩

中文:
实例 hasBinaryCoproduct_zero_left
  签名: (X : C)
  定义体: HasColimit.mk ⟨_, binaryCofanZeroLeftIsColimit X⟩

Depends on / 依赖: HasColimit, HasColimit.mk, binaryCofanZeroLeftIsColimit
-/
instance hasBinaryCoproduct_zero_left (X : C) : HasBinaryCoproduct (0 : C) X :=
  HasColimit.mk ⟨_, binaryCofanZeroLeftIsColimit X⟩

/--
Definition of `zeroCoprodIso` / `zeroCoprodIso` 的定义

English:
definition zeroCoprodIso
  signature: (X : C)
  body: colimit.isoColimitCocone ⟨_, binaryCofanZeroLeftIsColimit X⟩

中文:
定义 zeroCoprodIso
  签名: (X : C)
  定义体: colimit.isoColimitCocone ⟨_, binaryCofanZeroLeftIsColimit X⟩

Depends on / 依赖: binaryCofanZeroLeftIsColimit, colimit, colimit.isoColimitCocone, isoColimitCocone
-/
def zeroCoprodIso (X : C) : (0 : C) ⨿ X ≅ X :=
  colimit.isoColimitCocone ⟨_, binaryCofanZeroLeftIsColimit X⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inr_zeroCoprodIso_hom` / 定理 `inr_zeroCoprodIso_hom`

English:
theorem inr_zeroCoprodIso_hom
  given: (X : C)
  statement: coprod.inr ≫ (zeroCoprodIso X).hom = 𝟙 X
  proof: by
  dsimp [zeroCoprodIso, binaryCofanZeroLeft]
  simp

@[simp]

中文:
定理 inr_zeroCoprodIso_hom
  条件: (X : C)
  结论: coprod.inr ≫ (zeroCoprodIso X).hom = 𝟙 X
  证明: by
  dsimp [zeroCoprodIso, binaryCofanZeroLeft]
  simp

@[simp]

Depends on / 依赖: binaryCofanZeroLeft, zeroCoprodIso
-/
theorem inr_zeroCoprodIso_hom (X : C) : coprod.inr ≫ (zeroCoprodIso X).hom = 𝟙 X := by
  dsimp [zeroCoprodIso, binaryCofanZeroLeft]
  simp

@[simp]
/--
theorem `zeroCoprodIso_inv` / 定理 `zeroCoprodIso_inv`

English:
theorem zeroCoprodIso_inv
  given: (X : C)
  statement: (zeroCoprodIso X).inv = coprod.inr
  proof: rfl

中文:
定理 zeroCoprodIso_inv
  条件: (X : C)
  结论: (zeroCoprodIso X).inv = coprod.inr
  证明: rfl
-/
theorem zeroCoprodIso_inv (X : C) : (zeroCoprodIso X).inv = coprod.inr :=
  rfl

/--
Definition of `binaryCofanZeroRight` / `binaryCofanZeroRight` 的定义

English:
definition binaryCofanZeroRight
  signature: (X : C)
  body: BinaryCofan.mk (𝟙 X) 0

中文:
定义 binaryCofanZeroRight
  签名: (X : C)
  定义体: BinaryCofan.mk (𝟙 X) 0

Depends on / 依赖: BinaryCofan, BinaryCofan.mk
-/
def binaryCofanZeroRight (X : C) : BinaryCofan X (0 : C) :=
  BinaryCofan.mk (𝟙 X) 0

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryCofanZeroRightIsColimit` / `binaryCofanZeroRightIsColimit` 的定义

English:
definition binaryCofanZeroRightIsColimit
  signature: (X : C)
  body: BinaryCofan.isColimitMk (fun s => BinaryCofan.inl s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

中文:
定义 binaryCofanZeroRightIsColimit
  签名: (X : C)
  定义体: BinaryCofan.isColimitMk (fun s => BinaryCofan.inl s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

Depends on / 依赖: BinaryCofan, BinaryCofan.inl, BinaryCofan.isColimitMk, cat_disch, isColimitMk
-/
def binaryCofanZeroRightIsColimit (X : C) : IsColimit (binaryCofanZeroRight X) :=
  BinaryCofan.isColimitMk (fun s => BinaryCofan.inl s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)

/--
Instance `hasBinaryCoproduct_zero_right` / 实例 `hasBinaryCoproduct_zero_right`

English:
instance hasBinaryCoproduct_zero_right
  signature: (X : C)
  body: HasColimit.mk ⟨_, binaryCofanZeroRightIsColimit X⟩

中文:
实例 hasBinaryCoproduct_zero_right
  签名: (X : C)
  定义体: HasColimit.mk ⟨_, binaryCofanZeroRightIsColimit X⟩

Depends on / 依赖: HasColimit, HasColimit.mk, binaryCofanZeroRightIsColimit
-/
instance hasBinaryCoproduct_zero_right (X : C) : HasBinaryCoproduct X (0 : C) :=
  HasColimit.mk ⟨_, binaryCofanZeroRightIsColimit X⟩

/--
Definition of `coprodZeroIso` / `coprodZeroIso` 的定义

English:
definition coprodZeroIso
  signature: (X : C)
  body: colimit.isoColimitCocone ⟨_, binaryCofanZeroRightIsColimit X⟩

中文:
定义 coprodZeroIso
  签名: (X : C)
  定义体: colimit.isoColimitCocone ⟨_, binaryCofanZeroRightIsColimit X⟩

Depends on / 依赖: binaryCofanZeroRightIsColimit, colimit, colimit.isoColimitCocone, isoColimitCocone
-/
def coprodZeroIso (X : C) : X ⨿ (0 : C) ≅ X :=
  colimit.isoColimitCocone ⟨_, binaryCofanZeroRightIsColimit X⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inr_coprodZeroIso_hom` / 定理 `inr_coprodZeroIso_hom`

English:
theorem inr_coprodZeroIso_hom
  given: (X : C)
  statement: coprod.inl ≫ (coprodZeroIso X).hom = 𝟙 X
  proof: by
  dsimp [coprodZeroIso, binaryCofanZeroRight]
  simp

@[simp]

中文:
定理 inr_coprodZeroIso_hom
  条件: (X : C)
  结论: coprod.inl ≫ (coprodZeroIso X).hom = 𝟙 X
  证明: by
  dsimp [coprodZeroIso, binaryCofanZeroRight]
  simp

@[simp]

Depends on / 依赖: binaryCofanZeroRight, coprodZeroIso
-/
theorem inr_coprodZeroIso_hom (X : C) : coprod.inl ≫ (coprodZeroIso X).hom = 𝟙 X := by
  dsimp [coprodZeroIso, binaryCofanZeroRight]
  simp

@[simp]
/--
theorem `coprodZeroIso_inv` / 定理 `coprodZeroIso_inv`

English:
theorem coprodZeroIso_inv
  given: (X : C)
  statement: (coprodZeroIso X).inv = coprod.inl
  proof: rfl

中文:
定理 coprodZeroIso_inv
  条件: (X : C)
  结论: (coprodZeroIso X).inv = coprod.inl
  证明: rfl
-/
theorem coprodZeroIso_inv (X : C) : (coprodZeroIso X).inv = coprod.inl :=
  rfl

/--
Instance `hasPullback_over_zero` / 实例 `hasPullback_over_zero`

English:
instance hasPullback_over_zero
  signature: (X Y : C) [HasBinaryProduct X Y]
  body: HasLimit.mk
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

中文:
实例 hasPullback_over_zero
  签名: (X Y : C) [HasBinaryProduct X Y]
  定义体: HasLimit.mk
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

Depends on / 依赖: HasLimit, HasLimit.mk, HasZeroObject, HasZeroObject.zeroIsTerminal, isPullbackOfIsTerminalIsProduct, prodIsProd, zeroIsTerminal
-/
instance hasPullback_over_zero (X Y : C) [HasBinaryProduct X Y] :
    HasPullback (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  HasLimit.mk
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

/--
Definition of `pullbackZeroZeroIso` / `pullbackZeroZeroIso` 的定义

English:
definition pullbackZeroZeroIso
  signature: (X Y : C) [HasBinaryProduct X Y]
  body: limit.isoLimitCone
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

中文:
定义 pullbackZeroZeroIso
  签名: (X Y : C) [HasBinaryProduct X Y]
  定义体: limit.isoLimitCone
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsTerminal, isPullbackOfIsTerminalIsProduct, isoLimitCone, limit.isoLimitCone, prodIsProd, zeroIsTerminal
-/
def pullbackZeroZeroIso (X Y : C) [HasBinaryProduct X Y] :
    pullback (0 : X ⟶ 0) (0 : Y ⟶ 0) ≅ X ⨯ Y :=
  limit.isoLimitCone
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pullbackZeroZeroIso_inv_fst` / 定理 `pullbackZeroZeroIso_inv_fst`

English:
theorem pullbackZeroZeroIso_inv_fst
  given: (X Y : C) [HasBinaryProduct X Y]
  proof: by
  dsimp [pullbackZeroZeroIso]
  simp

中文:
定理 pullbackZeroZeroIso_inv_fst
  条件: (X Y : C) [HasBinaryProduct X Y]
  证明: by
  dsimp [pullbackZeroZeroIso]
  simp

Depends on / 依赖: pullbackZeroZeroIso
-/
theorem pullbackZeroZeroIso_inv_fst (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).inv ≫ pullback.fst 0 0 = prod.fst := by
  dsimp [pullbackZeroZeroIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pullbackZeroZeroIso_inv_snd` / 定理 `pullbackZeroZeroIso_inv_snd`

English:
theorem pullbackZeroZeroIso_inv_snd
  given: (X Y : C) [HasBinaryProduct X Y]
  proof: by
  dsimp [pullbackZeroZeroIso]
  simp

@[simp]

中文:
定理 pullbackZeroZeroIso_inv_snd
  条件: (X Y : C) [HasBinaryProduct X Y]
  证明: by
  dsimp [pullbackZeroZeroIso]
  simp

@[simp]

Depends on / 依赖: pullbackZeroZeroIso
-/
theorem pullbackZeroZeroIso_inv_snd (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).inv ≫ pullback.snd 0 0 = prod.snd := by
  dsimp [pullbackZeroZeroIso]
  simp

@[simp]
/--
theorem `pullbackZeroZeroIso_hom_fst` / 定理 `pullbackZeroZeroIso_hom_fst`

English:
theorem pullbackZeroZeroIso_hom_fst
  given: (X Y : C) [HasBinaryProduct X Y]
  proof: by simp [← Iso.eq_inv_comp]

@[simp]

中文:
定理 pullbackZeroZeroIso_hom_fst
  条件: (X Y : C) [HasBinaryProduct X Y]
  证明: by simp [← Iso.eq_inv_comp]

@[simp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
theorem pullbackZeroZeroIso_hom_fst (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).hom ≫ prod.fst = pullback.fst 0 0 := by simp [← Iso.eq_inv_comp]

@[simp]
/--
theorem `pullbackZeroZeroIso_hom_snd` / 定理 `pullbackZeroZeroIso_hom_snd`

English:
theorem pullbackZeroZeroIso_hom_snd
  given: (X Y : C) [HasBinaryProduct X Y]
  proof: by simp [← Iso.eq_inv_comp]

中文:
定理 pullbackZeroZeroIso_hom_snd
  条件: (X Y : C) [HasBinaryProduct X Y]
  证明: by simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
theorem pullbackZeroZeroIso_hom_snd (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).hom ≫ prod.snd = pullback.snd 0 0 := by simp [← Iso.eq_inv_comp]

/--
Instance `hasPushout_over_zero` / 实例 `hasPushout_over_zero`

English:
instance hasPushout_over_zero
  signature: (X Y : C) [HasBinaryCoproduct X Y]
  body: HasColimit.mk
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

中文:
实例 hasPushout_over_zero
  签名: (X Y : C) [HasBinaryCoproduct X Y]
  定义体: HasColimit.mk
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

Depends on / 依赖: HasColimit, HasColimit.mk, HasZeroObject, HasZeroObject.zeroIsInitial, coprodIsCoprod, isPushoutOfIsInitialIsCoproduct, zeroIsInitial
-/
instance hasPushout_over_zero (X Y : C) [HasBinaryCoproduct X Y] :
    HasPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) :=
  HasColimit.mk
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

/--
Definition of `pushoutZeroZeroIso` / `pushoutZeroZeroIso` 的定义

English:
definition pushoutZeroZeroIso
  signature: (X Y : C) [HasBinaryCoproduct X Y]
  body: colimit.isoColimitCocone
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

中文:
定义 pushoutZeroZeroIso
  签名: (X Y : C) [HasBinaryCoproduct X Y]
  定义体: colimit.isoColimitCocone
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsInitial, colimit, colimit.isoColimitCocone, coprodIsCoprod, isPushoutOfIsInitialIsCoproduct, isoColimitCocone, zeroIsInitial
-/
def pushoutZeroZeroIso (X Y : C) [HasBinaryCoproduct X Y] :
    pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) ≅ X ⨿ Y :=
  colimit.isoColimitCocone
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inl_pushoutZeroZeroIso_hom` / 定理 `inl_pushoutZeroZeroIso_hom`

English:
theorem inl_pushoutZeroZeroIso_hom
  given: (X Y : C) [HasBinaryCoproduct X Y]
  proof: by
  dsimp [pushoutZeroZeroIso]
  simp

中文:
定理 inl_pushoutZeroZeroIso_hom
  条件: (X Y : C) [HasBinaryCoproduct X Y]
  证明: by
  dsimp [pushoutZeroZeroIso]
  simp

Depends on / 依赖: pushoutZeroZeroIso
-/
theorem inl_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] :
    pushout.inl _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inl := by
  dsimp [pushoutZeroZeroIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inr_pushoutZeroZeroIso_hom` / 定理 `inr_pushoutZeroZeroIso_hom`

English:
theorem inr_pushoutZeroZeroIso_hom
  given: (X Y : C) [HasBinaryCoproduct X Y]
  proof: by
  dsimp [pushoutZeroZeroIso]
  simp

@[simp]

中文:
定理 inr_pushoutZeroZeroIso_hom
  条件: (X Y : C) [HasBinaryCoproduct X Y]
  证明: by
  dsimp [pushoutZeroZeroIso]
  simp

@[simp]

Depends on / 依赖: pushoutZeroZeroIso
-/
theorem inr_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] :
    pushout.inr _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inr := by
  dsimp [pushoutZeroZeroIso]
  simp

@[simp]
/--
theorem `inl_pushoutZeroZeroIso_inv` / 定理 `inl_pushoutZeroZeroIso_inv`

English:
theorem inl_pushoutZeroZeroIso_inv
  given: (X Y : C) [HasBinaryCoproduct X Y]
  proof: by simp [Iso.comp_inv_eq]

@[simp]

中文:
定理 inl_pushoutZeroZeroIso_inv
  条件: (X Y : C) [HasBinaryCoproduct X Y]
  证明: by simp [Iso.comp_inv_eq]

@[simp]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem inl_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] :
    coprod.inl ≫ (pushoutZeroZeroIso X Y).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

@[simp]
/--
theorem `inr_pushoutZeroZeroIso_inv` / 定理 `inr_pushoutZeroZeroIso_inv`

English:
theorem inr_pushoutZeroZeroIso_inv
  given: (X Y : C) [HasBinaryCoproduct X Y]
  proof: by simp [Iso.comp_inv_eq]

中文:
定理 inr_pushoutZeroZeroIso_inv
  条件: (X Y : C) [HasBinaryCoproduct X Y]
  证明: by simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem inr_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] :
    coprod.inr ≫ (pushoutZeroZeroIso X Y).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

end CategoryTheory.Limits
