/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# A product as a binary product

We write a product indexed by `I` as a binary product of the products indexed by a subset of `I`
and its complement.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C I : Type*} [Category* C] {X Y : I -> C}
  (f : (i : I) -> X i ⟶ Y i) (P : I -> Prop)
  [HasProduct X] [HasProduct Y]
  [HasProduct (fun (i : {x : I // P x}) => X i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) => X i.val)]
  [HasProduct (fun (i : {x : I // P x}) => Y i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) => Y i.val)]

variable (X) in
/--
Definition of `Pi.binaryFanOfProp` / `Pi.binaryFanOfProp` 的定义

English:
definition Pi.binaryFanOfProp
  signature: : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
  body: BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ => 𝟙 _)
    (Pi.map' Subtype.val fun _ => 𝟙 _)

中文:
定义 依赖函数类型.binaryFanOfProp
  签名: : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
  定义体: BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ => 𝟙 _)
    (Pi.map' Subtype.val fun _ => 𝟙 _)

Depends on / 依赖: BinaryFan, BinaryFan.mk, Pi.map, Subtype, Subtype.val
-/
noncomputable def Pi.binaryFanOfProp : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) => X i.val)) :=
  BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ => 𝟙 _)
    (Pi.map' Subtype.val fun _ => 𝟙 _)

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/--
Definition of `Pi.binaryFanOfPropIsLimit` / `Pi.binaryFanOfPropIsLimit` 的定义

English:
definition Pi.binaryFanOfPropIsLimit
  signature: [forall i, Decidable (P i)]
  body: BinaryFan.isLimitMk
    (fun s => Pi.lift fun b => if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) => X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) => X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ => Pi.hom_ext _ _ fun b => by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

中文:
定义 依赖函数类型.binaryFanOfPropIsLimit
  签名: [对任意 i, 可判定 (P i)]
  定义体: BinaryFan.isLimitMk
    (fun s => Pi.lift fun b => if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) => X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) => X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ => Pi.hom_ext _ _ fun b => by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

Depends on / 依赖: BinaryFan, BinaryFan.isLimitMk, Pi.hom_ext, Pi.lift, WalkingPair, WalkingPair.left, WalkingPair.right, dif_neg, dif_pos, hom_ext, i.val, isLimitMk
-/
noncomputable def Pi.binaryFanOfPropIsLimit [forall i, Decidable (P i)] :
    IsLimit (Pi.binaryFanOfProp X P) :=
  BinaryFan.isLimitMk
    (fun s => Pi.lift fun b => if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) => X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) => X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ => Pi.hom_ext _ _ fun b => by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

/--
lemma `hasBinaryProduct_of_products` / 引理 `hasBinaryProduct_of_products`

English:
lemma hasBinaryProduct_of_products
  statement: HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
  proof: by
  classical exact ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

中文:
引理 hasBinaryProduct_of_products
  结论: HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
  证明: by
  classical exact ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

Depends on / 依赖: Pi.binaryFanOfProp, Pi.binaryFanOfPropIsLimit, binaryFanOfProp, binaryFanOfPropIsLimit, classical
-/
lemma hasBinaryProduct_of_products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) => X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) => X i.val)) := by
  classical exact ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

attribute [local instance] hasBinaryProduct_of_products

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Pi.map_eq_prod_map` / 引理 `Pi.map_eq_prod_map`

English:
lemma Pi.map_eq_prod_map
  given: [forall i, Decidable (P i)]
  statement: Pi.map f =
  proof: by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  cat_disch

中文:
引理 依赖函数类型.map_eq_prod_map
  条件: [对任意 i, 可判定 (P i)]
  结论: 依赖函数类型.map f =
  证明: by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  cat_disch

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso, Iso.eq_comp_inv, binaryFanOfProp, cat_disch, conePointUniqueUpToIso, eq_comp_inv, prodIsProd
-/
lemma Pi.map_eq_prod_map [forall i, Decidable (P i)] : Pi.map f =
    ((Pi.binaryFanOfPropIsLimit X P).conePointUniqueUpToIso (prodIsProd _ _)).hom ≫
      prod.map (Pi.map (fun (i : {x : I // P x}) => f i.val))
      (Pi.map (fun (i : {x : I // ¬ P x}) => f i.val)) ≫
        ((Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso (prodIsProd _ _)).inv := by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  cat_disch

end CategoryTheory.Limits
