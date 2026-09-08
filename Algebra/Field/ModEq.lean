/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.MinImports

/-!
# Congruence modulo multiples of an element in a (semi)field

In this file we prove a few theorems about the congruence relation `_ ≡ _ [PMOD _]`
in a division semiring or a semifield.
-/

public section

namespace AddCommGroup

section DivisionSemiring
variable {K : Type*} [DivisionSemiring K] {a b c p : K}

/-
**AddCommGroup.div_modEq_div** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c p : K}, c ≠ 0 → (a / c
 ≡ b / c [PMOD p] ↔ a ≡ b [PMOD p * c])
参数：a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD p * c]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `add_div'`：add_div' (a b c : K) (hc : c != 0) : b + a / c = (b * c + a) /
 c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma div_modEq_div (hc : c ≠ 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [modEq_iff_nsmul, add_div' _ _ _ hc, div_left_inj' hc, mul_assoc]
/-
**AddCommGroup.mul_modEq_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c p : K}, c ≠ 0 → (a * c
 ≡ b * c [PMOD p] ↔ a ≡ b [PMOD p / c])
参数：a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD p / c]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGroup.div_modEq_div`：∀ {K : Type u_1} [inst : DivisionSemiring K]
 {a b c p : K}, c ≠ 0 → (a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD p * c])
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mul_modEq_mul_right (hc : c ≠ 0) : a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv, ← div_modEq_div (inv_ne_zero hc), div_inv_eq_mul, div_inv_eq_mul]

end DivisionSemiring

section Semifield
variable {K : Type*} [Semifield K] {a b c p : K}

/-
**AddCommGroup.mul_modEq_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：∀ {K : Type u_1} [inst : Semifield K] {a b c p : K}, c ≠ 0 → (c * a ≡ c * 
b [PMOD p] ↔ a ≡ b [PMOD p / c])
参数：c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD p / c]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mul_modEq_mul_left (hc : c ≠ 0) : c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simp [mul_comm c, hc]

end Semifield
end AddCommGroup

