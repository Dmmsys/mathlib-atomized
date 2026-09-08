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
/-
**toLexMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toLexMulEquiv : α ≃* Lex α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toLex` as a `MulEquiv`.
-/
def toLexMulEquiv : α ≃* Lex α where
  toEquiv := toLex
  map_mul' _ _ := by simp

/-- `ofLex` as a `MulEquiv`. -/
@[to_additive /-- `ofLex` as an `AddEquiv`. -/]
/-
**ofLexMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofLexMulEquiv : Lex α ≃* α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLex` as a `MulEquiv`.
-/
def ofLexMulEquiv : Lex α ≃* α where
  toEquiv := ofLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]
/-
**coe_toLexMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_toLexMulEquiv : ⇑(toLexMulEquiv α) = toLex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLexMulEquiv : ⇑(toLexMulEquiv α) = toLex := rfl

@[to_additive (attr := simp)]
/-
**coe_ofLexMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_ofLexMulEquiv : ⇑(ofLexMulEquiv α) = ofLex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofLexMulEquiv : ⇑(ofLexMulEquiv α) = ofLex := rfl

@[to_additive (attr := simp)]
/-
**symm_toLexMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：symm_toLexMulEquiv : (toLexMulEquiv α).symm = ofLexMulEquiv α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_toLexMulEquiv : (toLexMulEquiv α).symm = ofLexMulEquiv α := rfl

@[to_additive (attr := simp)]
/-
**symm_ofLexMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：symm_ofLexMulEquiv : (ofLexMulEquiv α).symm = toLexMulEquiv α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_ofLexMulEquiv : (ofLexMulEquiv α).symm = toLexMulEquiv α := rfl

@[to_additive (attr := simp)]
/-
**toEquiv_toLexMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toEquiv_toLexMulEquiv : (toLexMulEquiv α : α ≃ Lex α) = toLex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_toLexMulEquiv : (toLexMulEquiv α : α ≃ Lex α) = toLex := rfl

@[to_additive (attr := simp)]
/-
**toEquiv_ofLexMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toEquiv_ofLexMulEquiv : (ofLexMulEquiv α : Lex α ≃ α) = ofLex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_ofLexMulEquiv : (ofLexMulEquiv α : Lex α ≃ α) = ofLex := rfl
