/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Conversion from WithTop to Base Type

For types α that are instances of `Zero`, we provide a convenient conversion, `WithTop.untop₀`, that
maps elements `a : WithTop α` to `α`, by mapping `⊤` to zero.

For settings where `α` has additional structure, we provide a large number of simplifier lemmas,
akin to those that already exists for `ENat.toNat`.
-/

@[expose] public section

namespace WithTop
variable {α : Type*}

section Zero
variable [Zero α]

/-- Conversion from `WithTop α` to `α`, mapping `⊤` to zero. -/
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conversion from `WithTop α` to `α`, mapping `⊤` to zero.
-/
def untop₀ (a : WithTop α) : α := a.untopD 0

/-!
## Simplifying Lemmas in cases where α is an Instance of Zero
-/

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Simplifying Lemmas in cases where α is an Instance of Zero
-/
lemma untop₀_eq_zero {a : WithTop α} :
    a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤ := by simp [untop₀]

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_top : untop₀ ⊤ = (0 : α) := by simp [untop₀]

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_zero : untop₀ 0 = (0 : α) := by simp [untop₀]

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_coe (a : α) : (a : WithTop α).untop₀ = a := rfl
/-
**WithTop.coe_untop** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.untop hx) = x
参数：x : WithTop α；hx : x ≠ ⊤；x.untop hx。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_untop₀_of_ne_top {a : WithTop α} (ha : a ≠ ⊤) :
    a.untop₀ = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

end Zero

/-!
## Simplifying Lemmas involving addition and negation
-/

@[simp]
/-
**WithTop.untopD_add** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：untopD_add [Add α] {a b : WithTop α} {c : α} (ha : a != ⊤) (hb : b != ⊤) :
 (a + b).untopD c = a.untopD c + b.untopD c
参数：ha : a != ⊤；hb : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Simplifying Lemmas involving addition and negation
-/
lemma untopD_add [Add α] {a b : WithTop α} {c : α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untopD c = a.untopD c + b.untopD c := by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_add [AddZeroClass α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop₀ = a.untop₀ + b.untop₀ := untopD_add ha hb

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_natCast [AddMonoidWithOne α] (n : ℕ) : untop₀ (n : WithTop α) = n := rfl

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untop₀_one {α : Type*} [AddMonoidWithOne α] :
    (1 : WithTop α).untop₀ = 1 := by
  convert WithTop.untop₀_natCast 1
  all_goals exact Nat.cast_one.symm

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_ofNat [AddMonoidWithOne α] (n : ℕ) [n.AtLeastTwo] :
    untop₀ (ofNat(n) : WithTop α) = ofNat(n) := rfl

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_neg [AddCommGroup α] : ∀ a : WithTop α, (-a).untop₀ = -a.untop₀
  | ⊤ => by simp
  | (a : α) => rfl

@[simp]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := untopD_zero_mul a b

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] {a b : WithTop α}

/--
Elements of ordered additive commutative groups are nonnegative iff their untop₀ is nonnegative.
-/
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements of ordered additive commutative groups are nonnegative iff their untop₀
 is nonnegative.
-/
@[simp] lemma untop₀_nonneg : 0 ≤ a.untop₀ ↔ 0 ≤ a := by
  cases a with
  | top => tauto
  | coe a => simp
/-
**WithTop.le_of_untop** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_of_untop₀_le_untop₀ (ha : a ≠ ⊤) (h : a.untop₀ ≤ b.untop₀) : a ≤ b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, gcongr] theorem untop₀_le_untop₀ (hb : b ≠ ⊤) (h : a ≤ b) : a.untop₀ ≤ b.untop₀ := by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untop₀_le_untop₀_iff (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a.untop₀ ≤ b.untop₀ ↔ a ≤ b := by
  lift a to α using ha
  lift b to α using hb
  simp

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] {a b : WithTop α}

/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem untop₀_max (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (max a b).untop₀ = max a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]
/-
**WithTop.untop** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → (x : WithTop α) → x ≠ ⊤ → α
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem untop₀_min (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (min a b).untop₀ = min a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  norm_cast

end LinearOrderedAddCommGroup

end WithTop

