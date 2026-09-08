/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions from the symmetric square

This file lifts functions `α →₀ M₀` to functions `Sym2 α →₀ M₀` by precomposing with multiplication.
-/

@[expose] public section

open Sym2

variable {α M₀ : Type*} [CommMonoidWithZero M₀] {f : α →₀ M₀}

namespace Finsupp

/-
**Finsupp.sym2_support_eq_preimage_support_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finsup
p`。
形式化陈述：sym2_support_eq_preimage_support_mul [NoZeroDivisors M₀] (f : α ->₀ M₀) : 
f.support.sym2 = map f ⁻¹' mul.support
参数：f : α ->₀ M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_sym2`：∀ {α : Type u_1} {m : Finset α}, ↑m.sym2 = (↑m).sym2
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sym2_support_eq_preimage_support_mul [NoZeroDivisors M₀] (f : α →₀ M₀) :
    f.support.sym2 = map f ⁻¹' mul.support := by ext ⟨a, b⟩; simp
/-
**Finsupp.mem_sym2_support_of_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mem_sym2_support_of_mul_ne_zero (p : Sym2 α) (hp : mul (p.map f) != 0) : p
 in f.support.sym2
参数：p : Sym2 α；hp : mul (p.map f) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
-/
lemma mem_sym2_support_of_mul_ne_zero (p : Sym2 α) (hp : mul (p.map f) ≠ 0) :
    p ∈ f.support.sym2 := by
  obtain ⟨a, b⟩ := p
  simp only [map_mk, mul_mk, ne_eq] at hp
  simpa using .intro (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

/-- The composition of a `Finsupp` with `Sym2.mul` as a `Finsupp`. -/
/-
**Finsupp.sym2Mul** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sym2Mul (f : α ->₀ M₀) : Sym2 α ->₀ M₀
参数：f : α ->₀ M₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mem_sym2_support_of_mul_ne_zero`：mem_sym2_support_of_mul_ne_zero
 (p : Sym2 α) (hp : mul (p.map f) != 0) : p in f.support.sym2

--- 原说明 ---
The composition of a `Finsupp` with `Sym2.mul` as a `Finsupp`.
-/
noncomputable def sym2Mul (f : α →₀ M₀) : Sym2 α →₀ M₀ :=
  .onFinset f.support.sym2 (fun p ↦ mul (p.map f)) mem_sym2_support_of_mul_ne_zero
/-
**Finsupp.support_sym2Mul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_sym2Mul_subset : f.sym2Mul.support subseteq f.support.sym2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
· 使用引理 `Finsupp.mem_sym2_support_of_mul_ne_zero`：mem_sym2_support_of_mul_ne_zero
 (p : Sym2 α) (hp : mul (p.map f) != 0) : p in f.support.sym2
-/
lemma support_sym2Mul_subset : f.sym2Mul.support ⊆ f.support.sym2 := support_onFinset_subset
/-
**Finsupp.coe_sym2Mul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M₀ : Type u_2} [inst : CommMonoidWithZero M₀] (f : α →₀ 
M₀), ⇑f.sym2Mul = Sym2.mul ∘ Sym2.map ⇑f
参数：f : α →₀ M₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sym2Mul (f : α →₀ M₀) : f.sym2Mul = mul ∘ map f := rfl
/-
**Finsupp.sym2Mul_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sym2Mul_apply_mk (a b : α) : f.sym2Mul s(a, b) = f a * f b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sym2Mul_apply_mk (a b : α) : f.sym2Mul s(a, b) = f a * f b := rfl

end Finsupp

