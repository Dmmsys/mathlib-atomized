/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.RelClasses
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Bounded and unbounded sets

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

deprecated_module "Use the following replacements:
- `BddAbove` for `Set.Bounded (· ≤ ·)`
- `BddBelow` for `Set.Bounded (· ≥ ·)`
- `IsCofinal` for `Set.Unbounded (· < ·)` in a linear order
- `IsCoinitial` for `Set.Unbounded (· > ·)` in a linear order" (since := "2026-04-16")

public section

assert_not_exists RelIso

namespace Set

variable {α : Type*} {r : α → α → Prop} {s t : Set α}

/-! ### Subsets of bounded and unbounded sets -/


/-
**Set.Bounded.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Bounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆ t → Set.Bounded r t
 → Set.Bounded r s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a

--- 原说明 ---
### Subsets of bounded and unbounded sets
-/
theorem Bounded.mono (hst : s ⊆ t) (hs : Bounded r t) : Bounded r s :=
  hs.imp fun _ ha b hb => ha b (hst hb)
/-
**Set.Unbounded.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Unbounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆ t → Set.Unbounded r
 s → Set.Unbounded r t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Unbounded.mono (hst : s ⊆ t) (hs : Unbounded r s) : Unbounded r t := fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩

/-! ### Alternate characterizations of unboundedness on orders -/


/-
**Set.unbounded_le_of_forall_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_of_forall_exists_lt [Preorder α] (h : forall a, exists b in s
, a < b) : Unbounded (· <= ·) s
参数：h : forall a, exists b in s, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a

--- 原说明 ---
### Alternate characterizations of unboundedness on orders
-/
theorem unbounded_le_of_forall_exists_lt [Preorder α] (h : ∀ a, ∃ b ∈ s, a < b) :
    Unbounded (· ≤ ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_gt hb'⟩
/-
**Set.unbounded_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_iff [LinearOrder α] : Unbounded (· <= ·) s ↔ forall a, exists
 b in s, a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbounded_le_iff [LinearOrder α] : Unbounded (· ≤ ·) s ↔ ∀ a, ∃ b ∈ s, a < b := by
  simp only [Unbounded, not_le]
/-
**Set.unbounded_lt_of_forall_exists_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_of_forall_exists_le [Preorder α] (h : forall a, exists b in s
, a <= b) : Unbounded (· < ·) s
参数：h : forall a, exists b in s, a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem unbounded_lt_of_forall_exists_le [Preorder α] (h : ∀ a, ∃ b ∈ s, a ≤ b) :
    Unbounded (· < ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_ge hb'⟩
/-
**Set.unbounded_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_iff [LinearOrder α] : Unbounded (· < ·) s ↔ forall a, exists 
b in s, a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbounded_lt_iff [LinearOrder α] : Unbounded (· < ·) s ↔ ∀ a, ∃ b ∈ s, a ≤ b := by
  simp only [Unbounded, not_lt]
/-
**Set.unbounded_ge_of_forall_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_of_forall_exists_gt [Preorder α] (h : forall a, exists b in s
, b < a) : Unbounded (· >= ·) s
参数：h : forall a, exists b in s, b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_le_of_forall_exists_lt`：unbounded_le_of_forall_exists_lt [
Preorder α] (h : forall a, exists b in s, a < b) : Unbounded (· <= ·) s
-/
theorem unbounded_ge_of_forall_exists_gt [Preorder α] (h : ∀ a, ∃ b ∈ s, b < a) :
    Unbounded (· ≥ ·) s :=
  @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h
/-
**Set.unbounded_ge_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_iff [LinearOrder α] : Unbounded (· >= ·) s ↔ forall a, exists
 b in s, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Set.unbounded_ge_of_forall_exists_gt`：unbounded_ge_of_forall_exists_gt [
Preorder α] (h : forall a, exists b in s, b < a) : Unbounded (· >= ·) s
-/
theorem unbounded_ge_iff [LinearOrder α] : Unbounded (· ≥ ·) s ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩
/-
**Set.unbounded_gt_of_forall_exists_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_of_forall_exists_ge [Preorder α] (h : forall a, exists b in s
, b <= a) : Unbounded (· > ·) s
参数：h : forall a, exists b in s, b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem unbounded_gt_of_forall_exists_ge [Preorder α] (h : ∀ a, ∃ b ∈ s, b ≤ a) :
    Unbounded (· > ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩
/-
**Set.unbounded_gt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_iff [LinearOrder α] : Unbounded (· > ·) s ↔ forall a, exists 
b in s, b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Set.unbounded_gt_of_forall_exists_ge`：unbounded_gt_of_forall_exists_ge [
Preorder α] (h : forall a, exists b in s, b <= a) : Unbounded (· > ·) s
-/
theorem unbounded_gt_iff [LinearOrder α] : Unbounded (· > ·) s ↔ ∀ a, ∃ b ∈ s, b ≤ a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩

/-! ### Relation between boundedness by strict and nonstrict orders. -/


/-! #### Less and less or equal -/


/-
**Set.Bounded.rel_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Bounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {r' : α → α → Prop}, Set.B
ounded r s → r ≤ r' → Set.Bounded r' s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### Less and less or equal
-/
theorem Bounded.rel_mono {r' : α → α → Prop} (h : Bounded r s) (hrr' : r ≤ r') : Bounded r' s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩
/-
**Set.bounded_le_of_bounded_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_of_bounded_lt [Preorder α] (h : Bounded (· < ·) s) : Bounded (·
 <= ·) s
参数：h : Bounded (· < ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.rel_mono`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {r
' : α → α → Prop}, Set.Bounded r s → r ≤ r' → Set.Bounded r' s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem bounded_le_of_bounded_lt [Preorder α] (h : Bounded (· < ·) s) : Bounded (· ≤ ·) s :=
  h.rel_mono fun _ _ => le_of_lt
/-
**Set.Unbounded.rel_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Unbounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {r' : α → α → Prop}, r' ≤ 
r → Set.Unbounded r s → Set.Unbounded r' s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Unbounded.rel_mono {r' : α → α → Prop} (hr : r' ≤ r) (h : Unbounded r s) : Unbounded r' s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩
/-
**Set.unbounded_lt_of_unbounded_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_of_unbounded_le [Preorder α] (h : Unbounded (· <= ·) s) : Unb
ounded (· < ·) s
参数：h : Unbounded (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Unbounded.rel_mono`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} 
{r' : α → α → Prop}, r' ≤ r → Set.Unbounded r s → Set.Unbounded r' s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem unbounded_lt_of_unbounded_le [Preorder α] (h : Unbounded (· ≤ ·) s) : Unbounded (· < ·) s :=
  h.rel_mono fun _ _ => le_of_lt
/-
**Set.bounded_le_iff_bounded_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_iff_bounded_lt [Preorder α] [NoMaxOrder α] : Bounded (· <= ·) s
 ↔ Bounded (· < ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Set.bounded_le_of_bounded_lt`：bounded_le_of_bounded_lt [Preorder α] (h :
 Bounded (· < ·) s) : Bounded (· <= ·) s
-/
theorem bounded_le_iff_bounded_lt [Preorder α] [NoMaxOrder α] :
    Bounded (· ≤ ·) s ↔ Bounded (· < ·) s := by
  refine ⟨fun h => ?_, bounded_le_of_bounded_lt⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩
/-
**Set.unbounded_lt_iff_unbounded_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_iff_unbounded_le [Preorder α] [NoMaxOrder α] : Unbounded (· <
 ·) s ↔ Unbounded (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbounded_lt_iff_unbounded_le [Preorder α] [NoMaxOrder α] :
    Unbounded (· < ·) s ↔ Unbounded (· ≤ ·) s := by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]

/-! #### Greater and greater or equal -/


/-
**Set.bounded_ge_of_bounded_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_of_bounded_gt [Preorder α] (h : Bounded (· > ·) s) : Bounded (·
 >= ·) s
参数：h : Bounded (· > ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
#### Greater and greater or equal
-/
theorem bounded_ge_of_bounded_gt [Preorder α] (h : Bounded (· > ·) s) : Bounded (· ≥ ·) s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩
/-
**Set.unbounded_gt_of_unbounded_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_of_unbounded_ge [Preorder α] (h : Unbounded (· >= ·) s) : Unb
ounded (· > ·) s
参数：h : Unbounded (· >= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem unbounded_gt_of_unbounded_ge [Preorder α] (h : Unbounded (· ≥ ·) s) : Unbounded (· > ·) s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩
/-
**Set.bounded_ge_iff_bounded_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_iff_bounded_gt [Preorder α] [NoMinOrder α] : Bounded (· >= ·) s
 ↔ Bounded (· > ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_le_iff_bounded_lt`：bounded_le_iff_bounded_lt [Preorder α] [N
oMaxOrder α] : Bounded (· <= ·) s ↔ Bounded (· < ·) s
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem bounded_ge_iff_bounded_gt [Preorder α] [NoMinOrder α] :
    Bounded (· ≥ ·) s ↔ Bounded (· > ·) s :=
  @bounded_le_iff_bounded_lt αᵒᵈ _ _ _
/-
**Set.unbounded_gt_iff_unbounded_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_iff_unbounded_ge [Preorder α] [NoMinOrder α] : Unbounded (· >
 ·) s ↔ Unbounded (· >= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_iff_unbounded_le`：unbounded_lt_iff_unbounded_le [Preord
er α] [NoMaxOrder α] : Unbounded (· < ·) s ↔ Unbounded (· <= ·) s
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem unbounded_gt_iff_unbounded_ge [Preorder α] [NoMinOrder α] :
    Unbounded (· > ·) s ↔ Unbounded (· ≥ ·) s :=
  @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _

/-! ### The universal set -/


/-
**Set.unbounded_le_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_univ [LE α] [NoTopOrder α] : Unbounded (· <= ·) (@Set.univ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoTopOrder.exists_not_le`：∀ {α : Type u_3} {inst : LE α} [self : NoTopOr
der α] (a : α), ∃ b, ¬b ≤ a

--- 原说明 ---
### The universal set
-/
theorem unbounded_le_univ [LE α] [NoTopOrder α] : Unbounded (· ≤ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩
/-
**Set.unbounded_lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_univ [Preorder α] [NoTopOrder α] : Unbounded (· < ·) (@Set.un
iv α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_of_unbounded_le`：unbounded_lt_of_unbounded_le [Preorder
 α] (h : Unbounded (· <= ·) s) : Unbounded (· < ·) s
· 使用定理 `Set.unbounded_le_univ`：unbounded_le_univ [LE α] [NoTopOrder α] : Unbound
ed (· <= ·) (@Set.univ α)
-/
theorem unbounded_lt_univ [Preorder α] [NoTopOrder α] : Unbounded (· < ·) (@Set.univ α) :=
  unbounded_lt_of_unbounded_le unbounded_le_univ
/-
**Set.unbounded_ge_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_univ [LE α] [NoBotOrder α] : Unbounded (· >= ·) (@Set.univ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoBotOrder.exists_not_ge`：∀ {α : Type u_3} {inst : LE α} [self : NoBotOr
der α] (a : α), ∃ b, ¬a ≤ b
-/
theorem unbounded_ge_univ [LE α] [NoBotOrder α] : Unbounded (· ≥ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩
/-
**Set.unbounded_gt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_univ [Preorder α] [NoBotOrder α] : Unbounded (· > ·) (@Set.un
iv α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_gt_of_unbounded_ge`：unbounded_gt_of_unbounded_ge [Preorder
 α] (h : Unbounded (· >= ·) s) : Unbounded (· > ·) s
· 使用定理 `Set.unbounded_ge_univ`：unbounded_ge_univ [LE α] [NoBotOrder α] : Unbound
ed (· >= ·) (@Set.univ α)
-/
theorem unbounded_gt_univ [Preorder α] [NoBotOrder α] : Unbounded (· > ·) (@Set.univ α) :=
  unbounded_gt_of_unbounded_ge unbounded_ge_univ

/-! ### Bounded and unbounded intervals -/


/-
**Set.bounded_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_self (a : α) : Bounded r { b | r b a }
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Bounded and unbounded intervals
-/
theorem bounded_self (a : α) : Bounded r { b | r b a } :=
  ⟨a, fun _ => id⟩

/-! #### Half-open bounded intervals -/


/-
**Set.bounded_lt_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·) (Iio a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_self`：bounded_self (a : α) : Bounded r { b | r b a }

--- 原说明 ---
#### Half-open bounded intervals
-/
theorem bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·) (Iio a) :=
  bounded_self a
/-
**Set.bounded_le_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Iio [Preorder α] (a : α) : Bounded (· <= ·) (Iio a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_le_of_bounded_lt`：bounded_le_of_bounded_lt [Preorder α] (h :
 Bounded (· < ·) s) : Bounded (· <= ·) s
· 使用定理 `Set.bounded_lt_Iio`：bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·
) (Iio a)
-/
theorem bounded_le_Iio [Preorder α] (a : α) : Bounded (· ≤ ·) (Iio a) :=
  bounded_le_of_bounded_lt (bounded_lt_Iio a)
/-
**Set.bounded_le_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Iic [Preorder α] (a : α) : Bounded (· <= ·) (Iic a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_self`：bounded_self (a : α) : Bounded r { b | r b a }
-/
theorem bounded_le_Iic [Preorder α] (a : α) : Bounded (· ≤ ·) (Iic a) :=
  bounded_self a
/-
**Set.bounded_lt_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) : Bounded (· < ·) (Iic 
a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) : Bounded (· < ·) (Iic a) := by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]
/-
**Set.bounded_gt_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·) (Ioi a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_self`：bounded_self (a : α) : Bounded r { b | r b a }
-/
theorem bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·) (Ioi a) :=
  bounded_self a
/-
**Set.bounded_ge_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· >= ·) (Ioi a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_ge_of_bounded_gt`：bounded_ge_of_bounded_gt [Preorder α] (h :
 Bounded (· > ·) s) : Bounded (· >= ·) s
· 使用定理 `Set.bounded_gt_Ioi`：bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·
) (Ioi a)
-/
theorem bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· ≥ ·) (Ioi a) :=
  bounded_ge_of_bounded_gt (bounded_gt_Ioi a)
/-
**Set.bounded_ge_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Ici [Preorder α] (a : α) : Bounded (· >= ·) (Ici a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_self`：bounded_self (a : α) : Bounded r { b | r b a }
-/
theorem bounded_ge_Ici [Preorder α] (a : α) : Bounded (· ≥ ·) (Ici a) :=
  bounded_self a
/-
**Set.bounded_gt_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) : Bounded (· > ·) (Ici 
a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) : Bounded (· > ·) (Ici a) := by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]

/-! #### Other bounded intervals -/


/-
**Set.bounded_lt_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Ioo [Preorder α] (a b : α) : Bounded (· < ·) (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
· 使用定理 `Set.bounded_lt_Iio`：bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·
) (Iio a)

--- 原说明 ---
#### Other bounded intervals
-/
theorem bounded_lt_Ioo [Preorder α] (a b : α) : Bounded (· < ·) (Ioo a b) :=
  (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self
/-
**Set.bounded_lt_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Ico [Preorder α] (a b : α) : Bounded (· < ·) (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `Set.bounded_lt_Iio`：bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·
) (Iio a)
-/
theorem bounded_lt_Ico [Preorder α] (a b : α) : Bounded (· < ·) (Ico a b) :=
  (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self
/-
**Set.bounded_lt_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Ioc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Io
c a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
· 使用定理 `Set.bounded_lt_Iic`：bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) :
 Bounded (· < ·) (Iic a)
-/
theorem bounded_lt_Ioc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Ioc a b) :=
  (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self
/-
**Set.bounded_lt_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_Icc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Ic
c a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `Set.bounded_lt_Iic`：bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) :
 Bounded (· < ·) (Iic a)
-/
theorem bounded_lt_Icc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Icc a b) :=
  (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self
/-
**Set.bounded_le_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Ioo [Preorder α] (a b : α) : Bounded (· <= ·) (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
· 使用定理 `Set.bounded_le_Iio`：bounded_le_Iio [Preorder α] (a : α) : Bounded (· <= 
·) (Iio a)
-/
theorem bounded_le_Ioo [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ioo a b) :=
  (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self
/-
**Set.bounded_le_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Ico [Preorder α] (a b : α) : Bounded (· <= ·) (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `Set.bounded_le_Iio`：bounded_le_Iio [Preorder α] (a : α) : Bounded (· <= 
·) (Iio a)
-/
theorem bounded_le_Ico [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ico a b) :=
  (bounded_le_Iio b).mono Set.Ico_subset_Iio_self
/-
**Set.bounded_le_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Ioc [Preorder α] (a b : α) : Bounded (· <= ·) (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
· 使用定理 `Set.bounded_le_Iic`：bounded_le_Iic [Preorder α] (a : α) : Bounded (· <= 
·) (Iic a)
-/
theorem bounded_le_Ioc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ioc a b) :=
  (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self
/-
**Set.bounded_le_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_Icc [Preorder α] (a b : α) : Bounded (· <= ·) (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `Set.bounded_le_Iic`：bounded_le_Iic [Preorder α] (a : α) : Bounded (· <= 
·) (Iic a)
-/
theorem bounded_le_Icc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Icc a b) :=
  (bounded_le_Iic b).mono Set.Icc_subset_Iic_self
/-
**Set.bounded_gt_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Ioo [Preorder α] (a b : α) : Bounded (· > ·) (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.bounded_gt_Ioi`：bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·
) (Ioi a)
-/
theorem bounded_gt_Ioo [Preorder α] (a b : α) : Bounded (· > ·) (Ioo a b) :=
  (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self
/-
**Set.bounded_gt_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Ioc [Preorder α] (a b : α) : Bounded (· > ·) (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.bounded_gt_Ioi`：bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·
) (Ioi a)
-/
theorem bounded_gt_Ioc [Preorder α] (a b : α) : Bounded (· > ·) (Ioc a b) :=
  (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self
/-
**Set.bounded_gt_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Ico [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Ic
o a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用定理 `Set.bounded_gt_Ici`：bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) :
 Bounded (· > ·) (Ici a)
-/
theorem bounded_gt_Ico [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Ico a b) :=
  (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self
/-
**Set.bounded_gt_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_Icc [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Ic
c a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `Set.bounded_gt_Ici`：bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) :
 Bounded (· > ·) (Ici a)
-/
theorem bounded_gt_Icc [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Icc a b) :=
  (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self
/-
**Set.bounded_ge_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Ioo [Preorder α] (a b : α) : Bounded (· >= ·) (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.bounded_ge_Ioi`：bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· >= 
·) (Ioi a)
-/
theorem bounded_ge_Ioo [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ioo a b) :=
  (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self
/-
**Set.bounded_ge_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Ioc [Preorder α] (a b : α) : Bounded (· >= ·) (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.bounded_ge_Ioi`：bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· >= 
·) (Ioi a)
-/
theorem bounded_ge_Ioc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ioc a b) :=
  (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self
/-
**Set.bounded_ge_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Ico [Preorder α] (a b : α) : Bounded (· >= ·) (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用定理 `Set.bounded_ge_Ici`：bounded_ge_Ici [Preorder α] (a : α) : Bounded (· >= 
·) (Ici a)
-/
theorem bounded_ge_Ico [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ico a b) :=
  (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self
/-
**Set.bounded_ge_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_Icc [Preorder α] (a b : α) : Bounded (· >= ·) (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `Set.bounded_ge_Ici`：bounded_ge_Ici [Preorder α] (a : α) : Bounded (· >= 
·) (Ici a)
-/
theorem bounded_ge_Icc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Icc a b) :=
  (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self

/-! #### Unbounded intervals -/


/-
**Set.unbounded_le_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) : Unbounded (· 
<= ·) (Ioi a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
#### Unbounded intervals
-/
theorem unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Ioi a) := fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_ge⟩
/-
**Set.unbounded_le_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_Ici [SemilatticeSup α] [NoMaxOrder α] (a : α) : Unbounded (· 
<= ·) (Ici a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Unbounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s
 ⊆ t → Set.Unbounded r s → Set.Unbounded r t
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Set.unbounded_le_Ioi`：unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α]
 (a : α) : Unbounded (· <= ·) (Ioi a)
-/
theorem unbounded_le_Ici [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Ici a) :=
  (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self
/-
**Set.unbounded_lt_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) : Unbounded (· 
< ·) (Ioi a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_of_unbounded_le`：unbounded_lt_of_unbounded_le [Preorder
 α] (h : Unbounded (· <= ·) s) : Unbounded (· < ·) s
· 使用定理 `Set.unbounded_le_Ioi`：unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α]
 (a : α) : Unbounded (· <= ·) (Ioi a)
-/
theorem unbounded_lt_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (Ioi a) :=
  unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)
/-
**Set.unbounded_lt_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_Ici [SemilatticeSup α] (a : α) : Unbounded (· < ·) (Ici a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem unbounded_lt_Ici [SemilatticeSup α] (a : α) : Unbounded (· < ·) (Ici a) := fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_gt⟩

/-! ### Bounded initial segments -/


/-
**Set.bounded_inter_not** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_inter_not (H : forall a b, exists m, forall c, r c a ∨ r c b -> r 
c m) (a : α) : Bounded r (s inter { b | ¬r b a }) ↔ Bounded r s
参数：H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
### Bounded initial segments
-/
theorem bounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Bounded r (s ∩ { b | ¬r b a }) ↔ Bounded r s := by
  refine ⟨?_, Bounded.mono inter_subset_left⟩
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := H a b
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩
/-
**Set.unbounded_inter_not** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_inter_not (H : forall a b, exists m, forall c, r c a ∨ r c b -> 
r c m) (a : α) : Unbounded r (s inter { b | ¬r b a }) ↔ Unbounded r s
参数：H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.bounded_inter_not`：bounded_inter_not (H : forall a b, exists m, fora
ll c, r c a ∨ r c b -> r c m) (a : α) : Bounded r (s inter { b | ¬r b a }) ↔ Bou
nded r s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Unbounded r (s ∩ { b | ¬r b a }) ↔ Unbounded r s := by
  simp_rw [← not_bounded_iff, bounded_inter_not H]

/-! #### Less or equal -/


/-
**Set.bounded_le_inter_not_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_inter_not_le [SemilatticeSup α] (a : α) : Bounded (· <= ·) (s i
nter { b | ¬b <= a }) ↔ Bounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_inter_not`：bounded_inter_not (H : forall a b, exists m, fora
ll c, r c a ∨ r c b -> r c m) (a : α) : Bounded r (s inter { b | ¬r b a }) ↔ Bou
nded r s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b

--- 原说明 ---
#### Less or equal
-/
theorem bounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Bounded (· ≤ ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a
/-
**Set.unbounded_le_inter_not_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_inter_not_le [SemilatticeSup α] (a : α) : Unbounded (· <= ·) 
(s inter { b | ¬b <= a }) ↔ Unbounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.bounded_le_inter_not_le`：bounded_le_inter_not_le [SemilatticeSup α] 
(a : α) : Bounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Bounded (· <= ·) s
-/
theorem unbounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Unbounded (· ≤ ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_not_le a
/-
**Set.bounded_le_inter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_inter_lt [LinearOrder α] (a : α) : Bounded (· <= ·) (s inter { 
b | a < b }) ↔ Bounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bounded_le_inter_lt [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Bounded (· ≤ ·) s := by
  simp_rw [← not_le, bounded_le_inter_not_le]
/-
**Set.unbounded_le_inter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_inter_lt [LinearOrder α] (a : α) : Unbounded (· <= ·) (s inte
r { b | a < b }) ↔ Unbounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Set.unbounded_le_inter_not_le`：unbounded_le_inter_not_le [SemilatticeSup
 α] (a : α) : Unbounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Unbounded (· <= ·) 
s
-/
theorem unbounded_le_inter_lt [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Unbounded (· ≤ ·) s := by
  convert! @unbounded_le_inter_not_le _ s _ a
  exact lt_iff_not_ge
/-
**Set.bounded_le_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_le_inter_le [LinearOrder α] (a : α) : Bounded (· <= ·) (s inter { 
b | a <= b }) ↔ Bounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.bounded_le_inter_lt`：bounded_le_inter_lt [LinearOrder α] (a : α) : B
ounded (· <= ·) (s inter { b | a < b }) ↔ Bounded (· <= ·) s
· 使用定理 `Set.Bounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, s ⊆
 t → Set.Bounded r t → Set.Bounded r s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem bounded_le_inter_le [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· ≤ ·) s := by
  refine ⟨?_, Bounded.mono Set.inter_subset_left⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact Bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩
/-
**Set.unbounded_le_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_le_inter_le [LinearOrder α] (a : α) : Unbounded (· <= ·) (s inte
r { b | a <= b }) ↔ Unbounded (· <= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.bounded_le_inter_le`：bounded_le_inter_le [LinearOrder α] (a : α) : B
ounded (· <= ·) (s inter { b | a <= b }) ↔ Bounded (· <= ·) s
-/
theorem unbounded_le_inter_le [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· ≤ ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_le a

/-! #### Less than -/


/-
**Set.bounded_lt_inter_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_inter_not_lt [SemilatticeSup α] (a : α) : Bounded (· < ·) (s in
ter { b | ¬b < a }) ↔ Bounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_inter_not`：bounded_inter_not (H : forall a b, exists m, fora
ll c, r c a ∨ r c b -> r c m) (a : α) : Bounded r (s inter { b | ¬r b a }) ↔ Bou
nded r s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_sup_of_lt_left`：lt_sup_of_lt_left (h : c < a) : c < a ⊔ b
· 使用定理 `lt_sup_of_lt_right`：lt_sup_of_lt_right (h : c < b) : c < a ⊔ b

--- 原说明 ---
#### Less than
-/
theorem bounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Bounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Bounded (· < ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a
/-
**Set.unbounded_lt_inter_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_inter_not_lt [SemilatticeSup α] (a : α) : Unbounded (· < ·) (
s inter { b | ¬b < a }) ↔ Unbounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.bounded_lt_inter_not_lt`：bounded_lt_inter_not_lt [SemilatticeSup α] 
(a : α) : Bounded (· < ·) (s inter { b | ¬b < a }) ↔ Bounded (· < ·) s
-/
theorem unbounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_not_lt a
/-
**Set.bounded_lt_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_inter_le [LinearOrder α] (a : α) : Bounded (· < ·) (s inter { b
 | a <= b }) ↔ Bounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.bounded_lt_inter_not_lt`：bounded_lt_inter_not_lt [SemilatticeSup α] 
(a : α) : Bounded (· < ·) (s inter { b | ¬b < a }) ↔ Bounded (· < ·) s
-/
theorem bounded_lt_inter_le [LinearOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· < ·) s := by
  convert! @bounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm
/-
**Set.unbounded_lt_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_inter_le [LinearOrder α] (a : α) : Unbounded (· < ·) (s inter
 { b | a <= b }) ↔ Unbounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.unbounded_lt_inter_not_lt`：unbounded_lt_inter_not_lt [SemilatticeSup
 α] (a : α) : Unbounded (· < ·) (s inter { b | ¬b < a }) ↔ Unbounded (· < ·) s
-/
theorem unbounded_lt_inter_le [LinearOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· < ·) s := by
  convert! @unbounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm
/-
**Set.bounded_lt_inter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) : Bounded (· < 
·) (s inter { b | a < b }) ↔ Bounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.bounded_le_iff_bounded_lt`：bounded_le_iff_bounded_lt [Preorder α] [N
oMaxOrder α] : Bounded (· <= ·) s ↔ Bounded (· < ·) s
· 使用定理 `Set.bounded_le_inter_lt`：bounded_le_inter_lt [LinearOrder α] (a : α) : B
ounded (· <= ·) (s inter { b | a < b }) ↔ Bounded (· <= ·) s
-/
theorem bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a < b }) ↔ Bounded (· < ·) s := by
  rw [← bounded_le_iff_bounded_lt, ← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a
/-
**Set.unbounded_lt_inter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) : Unbounded (
· < ·) (s inter { b | a < b }) ↔ Unbounded (· < ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.bounded_lt_inter_lt`：bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder
 α] (a : α) : Bounded (· < ·) (s inter { b | a < b }) ↔ Bounded (· < ·) s
-/
theorem unbounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a < b }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_lt a

/-! #### Greater or equal -/


/-
**Set.bounded_ge_inter_not_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_inter_not_ge [SemilatticeInf α] (a : α) : Bounded (· >= ·) (s i
nter { b | ¬a <= b }) ↔ Bounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_le_inter_not_le`：bounded_le_inter_not_le [SemilatticeSup α] 
(a : α) : Bounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Bounded (· <= ·) s

--- 原说明 ---
#### Greater or equal
-/
theorem bounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_not_le αᵒᵈ s _ a
/-
**Set.unbounded_ge_inter_not_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_inter_not_ge [SemilatticeInf α] (a : α) : Unbounded (· >= ·) 
(s inter { b | ¬a <= b }) ↔ Unbounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_le_inter_not_le`：unbounded_le_inter_not_le [SemilatticeSup
 α] (a : α) : Unbounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Unbounded (· <= ·) 
s
-/
theorem unbounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_not_le αᵒᵈ s _ a
/-
**Set.bounded_ge_inter_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_inter_gt [LinearOrder α] (a : α) : Bounded (· >= ·) (s inter { 
b | b < a }) ↔ Bounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_le_inter_lt`：bounded_le_inter_lt [LinearOrder α] (a : α) : B
ounded (· <= ·) (s inter { b | a < b }) ↔ Bounded (· <= ·) s
-/
theorem bounded_ge_inter_gt [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_lt αᵒᵈ s _ a
/-
**Set.unbounded_ge_inter_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_inter_gt [LinearOrder α] (a : α) : Unbounded (· >= ·) (s inte
r { b | b < a }) ↔ Unbounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_le_inter_lt`：unbounded_le_inter_lt [LinearOrder α] (a : α)
 : Unbounded (· <= ·) (s inter { b | a < b }) ↔ Unbounded (· <= ·) s
-/
theorem unbounded_ge_inter_gt [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_lt αᵒᵈ s _ a
/-
**Set.bounded_ge_inter_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_ge_inter_ge [LinearOrder α] (a : α) : Bounded (· >= ·) (s inter { 
b | b <= a }) ↔ Bounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_le_inter_le`：bounded_le_inter_le [LinearOrder α] (a : α) : B
ounded (· <= ·) (s inter { b | a <= b }) ↔ Bounded (· <= ·) s
-/
theorem bounded_ge_inter_ge [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_le αᵒᵈ s _ a
/-
**Set.unbounded_ge_iff_unbounded_inter_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_ge_iff_unbounded_inter_ge [LinearOrder α] (a : α) : Unbounded (·
 >= ·) (s inter { b | b <= a }) ↔ Unbounded (· >= ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_le_inter_le`：unbounded_le_inter_le [LinearOrder α] (a : α)
 : Unbounded (· <= ·) (s inter { b | a <= b }) ↔ Unbounded (· <= ·) s
-/
theorem unbounded_ge_iff_unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_le αᵒᵈ s _ a

/-! #### Greater than -/


/-
**Set.bounded_gt_inter_not_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_inter_not_gt [SemilatticeInf α] (a : α) : Bounded (· > ·) (s in
ter { b | ¬a < b }) ↔ Bounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_lt_inter_not_lt`：bounded_lt_inter_not_lt [SemilatticeSup α] 
(a : α) : Bounded (· < ·) (s inter { b | ¬b < a }) ↔ Bounded (· < ·) s

--- 原说明 ---
#### Greater than
-/
theorem bounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Bounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_not_lt αᵒᵈ s _ a
/-
**Set.unbounded_gt_inter_not_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_inter_not_gt [SemilatticeInf α] (a : α) : Unbounded (· > ·) (
s inter { b | ¬a < b }) ↔ Unbounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_inter_not_lt`：unbounded_lt_inter_not_lt [SemilatticeSup
 α] (a : α) : Unbounded (· < ·) (s inter { b | ¬b < a }) ↔ Unbounded (· < ·) s
-/
theorem unbounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_not_lt αᵒᵈ s _ a
/-
**Set.bounded_gt_inter_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_inter_ge [LinearOrder α] (a : α) : Bounded (· > ·) (s inter { b
 | b <= a }) ↔ Bounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_lt_inter_le`：bounded_lt_inter_le [LinearOrder α] (a : α) : B
ounded (· < ·) (s inter { b | a <= b }) ↔ Bounded (· < ·) s
-/
theorem bounded_gt_inter_ge [LinearOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_le αᵒᵈ s _ a
/-
**Set.unbounded_inter_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_inter_ge [LinearOrder α] (a : α) : Unbounded (· > ·) (s inter { 
b | b <= a }) ↔ Unbounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_inter_le`：unbounded_lt_inter_le [LinearOrder α] (a : α)
 : Unbounded (· < ·) (s inter { b | a <= b }) ↔ Unbounded (· < ·) s
-/
theorem unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_le αᵒᵈ s _ a
/-
**Set.bounded_gt_inter_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) : Bounded (· > 
·) (s inter { b | b < a }) ↔ Bounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bounded_lt_inter_lt`：bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder
 α] (a : α) : Bounded (· < ·) (s inter { b | a < b }) ↔ Bounded (· < ·) s
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem bounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b < a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_lt αᵒᵈ s _ _ a
/-
**Set.unbounded_gt_inter_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) : Unbounded (
· > ·) (s inter { b | b < a }) ↔ Unbounded (· > ·) s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.unbounded_lt_inter_lt`：unbounded_lt_inter_lt [LinearOrder α] [NoMaxO
rder α] (a : α) : Unbounded (· < ·) (s inter { b | a < b }) ↔ Unbounded (· < ·) 
s
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem unbounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b < a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_lt αᵒᵈ s _ _ a

end Set

