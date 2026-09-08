/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Logic.Equiv.Option

/-!
# Extending a function from the complement of a singleton

In this file, we define `Function.subtypeNeLift` which allows to
extend a (dependent) function defined on the complement of a singleton.

-/

@[expose] public section

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (j : { i // i ≠ i₀ }), M j) (x : M i₀)

/-- Given `i₀ : ι` and `x : M i₀`, this is the (dependent) map `(i : ι) → M i`
whose value at `i₀` is `x` and which extends a given map on the complement of `{i₀}`. -/
/-
**Function.subtypeNeLift** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：subtypeNeLift (i : ι) : M i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i₀ : ι` and `x : M i₀`, this is the (dependent) map `(i : ι) → M i`
whose value at `i₀` is `x` and which extends a given map on the complement of `{
i₀}`.
-/
def subtypeNeLift (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
/-
**Function.subtypeNeLift_self** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：subtypeNeLift_self : subtypeNeLift i₀ f x i₀ = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma subtypeNeLift_self : subtypeNeLift i₀ f x i₀ = x := dif_pos rfl
/-
**Function.subtypeNeLift_of_neq** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：subtypeNeLift_of_neq (i : ι) (h : i != i₀) : subtypeNeLift i₀ f x i = f ⟨i
, h⟩
参数：i : ι；h : i != i₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma subtypeNeLift_of_neq (i : ι) (h : i ≠ i₀) :
    subtypeNeLift i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
/-
**Function.subtypeNeLift_restriction** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：subtypeNeLift_restriction (φ : forall i, M i) (i₀ : ι) : subtypeNeLift i₀ 
(fun i => φ i) (φ i₀) = φ
参数：φ : forall i, M i；i₀ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.subtypeNeLift_self`：subtypeNeLift_self : subtypeNeLift i₀ f x i
₀ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.subtypeNeLift_of_neq`：subtypeNeLift_of_neq (i : ι) (h : i != i₀
) : subtypeNeLift i₀ f x i = f ⟨i, h⟩
-/
lemma subtypeNeLift_restriction (φ : ∀ i, M i) (i₀ : ι) :
    subtypeNeLift i₀ (fun i ↦ φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [subtypeNeLift_of_neq _ _ _ _ h]

end Function

