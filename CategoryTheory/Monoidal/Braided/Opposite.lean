/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# If `C` is braided, so is `Cᵒᵖ`.

Todo: we should also do `Cᵐᵒᵖ`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory Opposite

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory Cᵒᵖ
  body: (β_ (unop Y) (unop X)).op

中文:
实例 :
  签名: 辫范畴 Cᵒᵖ
  定义体: (β_ (unop Y) (unop X)).op
-/
instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ (unop Y) (unop X)).op

namespace CategoryTheory.BraidedCategory

/--
lemma `unop_tensorμ` / 引理 `unop_tensorμ`

English:
lemma unop_tensorμ
  statement: {C : Type*} [Category* C] [MonoidalCategory C]
  proof: by
  simp only [unop_tensorObj, tensorμ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]

中文:
引理 unop_tensorμ
  结论: {C : 类型} [范畴* C] [幺半群范畴 C]
  证明: by
  simp only [unop_tensorObj, tensorμ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]
-/
@[simp] lemma unop_tensorμ {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : Cᵒᵖ) :
    (tensorμ X W Y Z).unop = tensorμ X.unop Y.unop W.unop Z.unop := by
  simp only [unop_tensorObj, tensorμ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]

/--
lemma `op_tensorμ` / 引理 `op_tensorμ`

English:
lemma op_tensorμ
  statement: {C : Type*} [Category* C] [MonoidalCategory C]
  proof: by
  simp only [op_tensorObj, tensorμ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]

中文:
引理 op_tensorμ
  结论: {C : 类型} [范畴* C] [幺半群范畴 C]
  证明: by
  simp only [op_tensorObj, tensorμ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]
-/
@[simp] lemma op_tensorμ {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : C) :
    (tensorμ X W Y Z).op = tensorμ (op X) (op Y) (op W) (op Z) := by
  simp only [op_tensorObj, tensorμ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]

end CategoryTheory.BraidedCategory
