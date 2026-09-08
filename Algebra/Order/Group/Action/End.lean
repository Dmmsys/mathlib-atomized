/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Order.RelIso.Basic

/-!
# Tautological action by relation automorphisms
-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace RelHom
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r →r r` on `α`. -/
/-
**RelHom.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `RelHom`。
形式化陈述：applyMulAction : MulAction (r ->r r) α where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `r →r r` on `α`.
-/
instance applyMulAction : MulAction (r →r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
/-
**RelHom.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (f : r →r r) (a : α), f • a = f a
参数：f : r →r r；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_def (f : r →r r) (a : α) : f • a = f a := rfl
/-
**RelHom.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `RelHom`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (r ->r r) α where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
-/
instance apply_faithfulSMul : FaithfulSMul (r →r r) α where eq_of_smul_eq_smul h := RelHom.ext h

end RelHom

namespace RelEmbedding
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ↪r r` on `α`. -/
/-
**RelEmbedding.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
形式化陈述：applyMulAction : MulAction (r ↪r r) α where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `r ↪r r` on `α`.
-/
instance applyMulAction : MulAction (r ↪r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
/-
**RelEmbedding.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (f : r ↪r r) (a : α), f • a = f a
参数：f : r ↪r r；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_def (f : r ↪r r) (a : α) : f • a = f a := rfl
/-
**RelEmbedding.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (r ↪r r) α where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
-/
instance apply_faithfulSMul : FaithfulSMul (r ↪r r) α where eq_of_smul_eq_smul h := ext h

end RelEmbedding

namespace RelIso
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ≃r r` on `α`. -/
/-
**RelIso.applyMulAction** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
形式化陈述：applyMulAction : MulAction (r ≃r r) α where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `r ≃r r` on `α`.
-/
instance applyMulAction : MulAction (r ≃r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
/-
**RelIso.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (f : r ≃r r) (a : α), f • a = f a
参数：f : r ≃r r；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl
/-
**RelIso.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
-/
instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h := RelIso.ext h

end RelIso

