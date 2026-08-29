/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Add/Mul equivalence for order type synonyms
-/

@[expose] public section

variable (α : Type*) [Mul α]

/-- `toLex` as a `MulEquiv`. -/
@[to_additive /-- `toLex` as an `AddEquiv`. -/]
/--
Definition of `toLexMulEquiv` / `toLexMulEquiv` 的定义

English:
definition toLexMulEquiv
  signature: : α ≃* Lex α where
  body: toLex
  map_mul' _ _ := by simp

中文:
定义 toLexMulEquiv
  签名: : α ≃* Lex α where
  定义体: toLex
  map_mul' _ _ := by simp
-/
def toLexMulEquiv : α ≃* Lex α where
  toEquiv := toLex
  map_mul' _ _ := by simp

/-- `ofLex` as a `MulEquiv`. -/
@[to_additive /-- `ofLex` as an `AddEquiv`. -/]
/--
Definition of `ofLexMulEquiv` / `ofLexMulEquiv` 的定义

English:
definition ofLexMulEquiv
  signature: : Lex α ≃* α where
  body: ofLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]

中文:
定义 ofLexMulEquiv
  签名: : Lex α ≃* α where
  定义体: ofLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]
-/
def ofLexMulEquiv : Lex α ≃* α where
  toEquiv := ofLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]
/--
theorem `coe_toLexMulEquiv` / 定理 `coe_toLexMulEquiv`

English:
theorem coe_toLexMulEquiv
  statement: ⇑(toLexMulEquiv α) = toLex
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toLexMulEquiv
  结论: ⇑(toLexMulEquiv α) = toLex
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toLexMulEquiv : ⇑(toLexMulEquiv α) = toLex := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_ofLexMulEquiv` / 定理 `coe_ofLexMulEquiv`

English:
theorem coe_ofLexMulEquiv
  statement: ⇑(ofLexMulEquiv α) = ofLex
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_ofLexMulEquiv
  结论: ⇑(ofLexMulEquiv α) = ofLex
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_ofLexMulEquiv : ⇑(ofLexMulEquiv α) = ofLex := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_toLexMulEquiv` / 引理 `symm_toLexMulEquiv`

English:
lemma symm_toLexMulEquiv
  statement: (toLexMulEquiv α).symm = ofLexMulEquiv α
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_toLexMulEquiv
  结论: (toLexMulEquiv α).symm = ofLexMulEquiv α
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_toLexMulEquiv : (toLexMulEquiv α).symm = ofLexMulEquiv α := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_ofLexMulEquiv` / 引理 `symm_ofLexMulEquiv`

English:
lemma symm_ofLexMulEquiv
  statement: (ofLexMulEquiv α).symm = toLexMulEquiv α
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_ofLexMulEquiv
  结论: (ofLexMulEquiv α).symm = toLexMulEquiv α
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_ofLexMulEquiv : (ofLexMulEquiv α).symm = toLexMulEquiv α := rfl

@[to_additive (attr := simp)]
/--
lemma `toEquiv_toLexMulEquiv` / 引理 `toEquiv_toLexMulEquiv`

English:
lemma toEquiv_toLexMulEquiv
  statement: (toLexMulEquiv α : α ≃ Lex α) = toLex
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 toEquiv_toLexMulEquiv
  结论: (toLexMulEquiv α : α ≃ Lex α) = toLex
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma toEquiv_toLexMulEquiv : (toLexMulEquiv α : α ≃ Lex α) = toLex := rfl

@[to_additive (attr := simp)]
/--
lemma `toEquiv_ofLexMulEquiv` / 引理 `toEquiv_ofLexMulEquiv`

English:
lemma toEquiv_ofLexMulEquiv
  statement: (ofLexMulEquiv α : Lex α ≃ α) = ofLex
  proof: rfl

中文:
引理 toEquiv_ofLexMulEquiv
  结论: (ofLexMulEquiv α : Lex α ≃ α) = ofLex
  证明: rfl
-/
lemma toEquiv_ofLexMulEquiv : (ofLexMulEquiv α : Lex α ≃ α) = ofLex := rfl
