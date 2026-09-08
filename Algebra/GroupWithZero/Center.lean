/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Center of a group with zero
-/

public section

assert_not_exists RelIso Finset Ring Subsemigroup

variable {M₀ G₀ : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s : Set M₀}

/-
**Set.zero_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀], 0 ∈ Set.center M₀
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma zero_mem_center : (0 : M₀) ∈ center M₀ where
  comm _ := by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]
/-
**Set.zero_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] {s : Set M₀}, 0 ∈ s.centralizer
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma zero_mem_centralizer : (0 : M₀) ∈ centralizer s := by simp [mem_centralizer_iff]

end MulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

/-
**Set.center_units_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：center_units_subset : center G₀ˣ subseteq ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma center_units_subset : center G₀ˣ ⊆ ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
  · exact congr_arg Units.val <| hu <| Units.mk0 a ha

/-- In a group with zero, the center of the units is the preimage of the center. -/
/-
**Set.center_units_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：center_units_eq : center G₀ˣ = ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Set.center_units_subset`：center_units_subset : center G₀ˣ subseteq ((↑) 
: G₀ˣ -> G₀) ⁻¹' center G₀
· 使用定理 `Set.subset_center_units`：subset_center_units : ((↑) : Mˣ -> M) ⁻¹' cente
r M subseteq Set.center Mˣ

--- 原说明 ---
In a group with zero, the center of the units is the preimage of the center.
-/
lemma center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ :=
  center_units_subset.antisymm subset_center_units
/-
**Set.inv_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_mem_centralizer (ha : a in centralizer S) : a⁻¹ in centralizer S
参数：ha : a in centralizer S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
-/
@[simp] lemma inv_mem_centralizer₀ (ha : a ∈ centralizer s) : a⁻¹ ∈ centralizer s := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_centralizer
  · rintro c hc
    rw [mul_inv_eq_iff_eq_mul₀ ha₀, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha₀, ha c hc]
/-
**Set.div_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：div_mem_centralizer (ha : a in centralizer S) (hb : b in centralizer S) : 
a / b in centralizer S
参数：ha : a in centralizer S；hb : b in centralizer S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Set.mul_mem_centralizer`：mul_mem_centralizer (ha : a in centralizer S) (
hb : b in centralizer S) : a * b in centralizer S
· 使用引理 `Set.inv_mem_centralizer`：inv_mem_centralizer (ha : a in centralizer S) :
 a⁻¹ in centralizer S
-/
@[simp] lemma div_mem_centralizer₀ (ha : a ∈ centralizer s) (hb : b ∈ centralizer s) :
    a / b ∈ centralizer s := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer₀ hb)

end GroupWithZero
end Set

