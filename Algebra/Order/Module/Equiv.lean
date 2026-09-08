/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Module.Synonym

/-!
# Linear equivalence for order type synonyms
-/

@[expose] public section

variable (α β : Type*)
variable [Semiring α] [AddCommMonoid β] [Module α β]

/-- `toLex` as a linear equivalence -/
/-
**toLexLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toLexLinearEquiv : β ≃ₗ[α] Lex β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toLex` as a linear equivalence
-/
def toLexLinearEquiv : β ≃ₗ[α] Lex β := (toLexAddEquiv β).toLinearEquiv toLex_smul

/-- `ofLex` as a linear equivalence -/
/-
**ofLexLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofLexLinearEquiv : Lex β ≃ₗ[α] β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLex` as a linear equivalence
-/
def ofLexLinearEquiv : Lex β ≃ₗ[α] β := (ofLexAddEquiv β).toLinearEquiv ofLex_smul
/-
**coe_toLexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Semiring α] [inst_1 : AddCommMonoi
d β] [inst_2 : _root_.Module α β],   ⇑(toLexLinearEquiv α β) = ⇑toLex
参数：α : Type u_1；β : Type u_2；toLexLinearEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLexLinearEquiv : ⇑(toLexLinearEquiv α β) = toLex := rfl
/-
**coe_ofLexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Semiring α] [inst_1 : AddCommMonoi
d β] [inst_2 : _root_.Module α β],   ⇑(ofLexLinearEquiv α β) = ⇑ofLex
参数：α : Type u_1；β : Type u_2；ofLexLinearEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofLexLinearEquiv : ⇑(ofLexLinearEquiv α β) = ofLex := rfl
/-
**symm_toLexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Semiring α] [inst_1 : AddCommMonoi
d β] [inst_2 : _root_.Module α β],   (toLexLinearEquiv α β).symm = ofLexLinearEq
uiv α β
参数：α : Type u_1；β : Type u_2；toLexLinearEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_toLexLinearEquiv : (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β := rfl
/-
**symm_ofLexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Semiring α] [inst_1 : AddCommMonoi
d β] [inst_2 : _root_.Module α β],   (ofLexLinearEquiv α β).symm = toLexLinearEq
uiv α β
参数：α : Type u_1；β : Type u_2；ofLexLinearEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_ofLexLinearEquiv : (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β := rfl
