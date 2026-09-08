/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `Set.projIci (a : α)` to be the map `α → [a, ∞)` sending `(-∞, a]` to `a`, and each point
  `x ∈ [a, ∞)` to itself;
* `Set.projIic (b : α)` to be the map `α → (-∞, b[` sending `[b, ∞)` to `b`, and each point
  `x ∈ (-∞, b]` to itself;
* `Set.projIcc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `Set.IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIcc a b h`.
* `Set.IciExtend {a : α} (f : Ici a → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIci a`.
* `Set.IicExtend {b : α} (f : Iic b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIic b`.

We also prove some trivial properties of these maps.
-/

@[expose] public section


variable {α β : Type*} [LinearOrder α]

open Function

namespace Set

/-- Projection of `α` to the closed interval `[a, ∞)`. -/
/-
**Set.projIci** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：projIci (a x : α) : Ici a
参数：a x : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
Projection of `α` to the closed interval `[a, ∞)`.
-/
def projIci (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩

/-- Projection of `α` to the closed interval `(-∞, b]`. -/
/-
**Set.projIic** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：projIic (b x : α) : Iic b
参数：b x : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a

--- 原说明 ---
Projection of `α` to the closed interval `(-∞, b]`.
-/
def projIic (b x : α) : Iic b := ⟨min b x, min_le_left _ _⟩

/-- Projection of `α` to the closed interval `[a, b]`. -/
/-
**Set.projIcc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：projIcc (a b : α) (h : a <= b) (x : α) : Icc a b
参数：a b : α；h : a <= b；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection of `α` to the closed interval `[a, b]`.
-/
def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

variable {a b : α} (h : a ≤ b) {x : α}

@[norm_cast]
/-
**Set.coe_projIci** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_projIci (a x : α) : (projIci a x : α) = max a x
参数：a x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projIci (a x : α) : (projIci a x : α) = max a x := rfl

@[norm_cast]
/-
**Set.coe_projIic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_projIic (b x : α) : (projIic b x : α) = min b x
参数：b x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projIic (b x : α) : (projIic b x : α) = min b x := rfl

@[norm_cast]
/-
**Set.coe_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_projIcc (a b : α) (h : a <= b) (x : α) : (projIcc a b h x : α) = max a
 (min b x)
参数：a b : α；h : a <= b；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projIcc (a b : α) (h : a ≤ b) (x : α) : (projIcc a b h x : α) = max a (min b x) := rfl
/-
**Set.projIci_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_of_le (hx : x <= a) : projIci a x = ⟨a, le_rfl⟩
参数：hx : x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem projIci_of_le (hx : x ≤ a) : projIci a x = ⟨a, le_rfl⟩ := Subtype.ext <| max_eq_left hx
/-
**Set.projIic_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_of_le (hx : b <= x) : projIic b x = ⟨b, le_rfl⟩
参数：hx : b <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
-/
theorem projIic_of_le (hx : b ≤ x) : projIic b x = ⟨b, le_rfl⟩ := Subtype.ext <| min_eq_left hx
/-
**Set.projIcc_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_of_le_left (hx : x <= a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩
参数：hx : x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projIcc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, hx.trans h]
/-
**Set.projIcc_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_of_right_le (hx : b <= x) : projIcc a b h x = ⟨b, right_mem_Icc.2 
h⟩
参数：hx : b <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projIcc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, h]

@[simp]
/-
**Set.projIci_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_self (a : α) : projIci a a = ⟨a, le_rfl⟩
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIci_of_le`：projIci_of_le (hx : x <= a) : projIci a x = ⟨a, le_rf
l⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem projIci_self (a : α) : projIci a a = ⟨a, le_rfl⟩ := projIci_of_le le_rfl

@[simp]
/-
**Set.projIic_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_self (b : α) : projIic b b = ⟨b, le_rfl⟩
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIic_of_le`：projIic_of_le (hx : b <= x) : projIic b x = ⟨b, le_rf
l⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem projIic_self (b : α) : projIic b b = ⟨b, le_rfl⟩ := projIic_of_le le_rfl

@[simp]
/-
**Set.projIcc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_of_le_left`：projIcc_of_le_left (hx : x <= a) : projIcc a b h
 x = ⟨a, left_mem_Icc.2 h⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  projIcc_of_le_left h le_rfl

@[simp]
/-
**Set.projIcc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_of_right_le`：projIcc_of_right_le (hx : b <= x) : projIcc a b
 h x = ⟨b, right_mem_Icc.2 h⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  projIcc_of_right_le h le_rfl
/-
**Set.projIci_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_eq_self : projIci a x = ⟨a, le_rfl⟩ ↔ x <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projIci_eq_self : projIci a x = ⟨a, le_rfl⟩ ↔ x ≤ a := by simp [projIci, Subtype.ext_iff]
/-
**Set.projIic_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_eq_self : projIic b x = ⟨b, le_rfl⟩ ↔ b <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projIic_eq_self : projIic b x = ⟨b, le_rfl⟩ ↔ b ≤ x := by simp [projIic, Subtype.ext_iff]
/-
**Set.projIcc_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.
le⟩ ↔ x <= a
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projIcc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a := by
  simp [projIcc, Subtype.ext_iff, h.not_ge]
/-
**Set.projIcc_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.
le⟩ ↔ b <= x
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `max_min_distrib_left`：max_min_distrib_left (a b c : α) : max a (min b c)
 = min (max a b) (max a c)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projIcc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.le⟩ ↔ b ≤ x := by
  simp [projIcc, Subtype.ext_iff, max_min_distrib_left, h.le, h.not_ge]

set_option backward.isDefEq.respectTransparency false in
/-
**Set.projIci_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_of_mem (hx : x in Ici a) : projIci a x = ⟨x, hx⟩
参数：hx : x in Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem projIci_of_mem (hx : x ∈ Ici a) : projIci a x = ⟨x, hx⟩ := by simpa [projIci]

set_option backward.isDefEq.respectTransparency false in
/-
**Set.projIic_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_of_mem (hx : x in Iic b) : projIic b x = ⟨x, hx⟩
参数：hx : x in Iic b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem projIic_of_mem (hx : x ∈ Iic b) : projIic b x = ⟨x, hx⟩ := by simpa [projIic]
/-
**Set.projIcc_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x = ⟨x, hx⟩
参数：hx : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projIcc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [projIcc, hx.1, hx.2]

@[simp]
/-
**Set.projIci_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_coe (x : Ici a) : projIci a x = x
参数：x : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIci_of_mem`：projIci_of_mem (hx : x in Ici a) : projIci a x = ⟨x,
 hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem projIci_coe (x : Ici a) : projIci a x = x := by cases x; apply projIci_of_mem

@[simp]
/-
**Set.projIic_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_coe (x : Iic b) : projIic b x = x
参数：x : Iic b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIic_of_mem`：projIic_of_mem (hx : x in Iic b) : projIic b x = ⟨x,
 hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem projIic_coe (x : Iic b) : projIic b x = x := by cases x; apply projIic_of_mem

@[simp]
/-
**Set.projIcc_val** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_val (x : Icc a b) : projIcc a b h x = x
参数：x : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem projIcc_val (x : Icc a b) : projIcc a b h x = x := by
  cases x
  apply projIcc_of_mem
/-
**Set.projIci_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_surjOn : SurjOn (projIci a) (Ici a) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.projIci_coe`：projIci_coe (x : Ici a) : projIci a x = x
-/
theorem projIci_surjOn : SurjOn (projIci a) (Ici a) univ := fun x _ => ⟨x, x.2, projIci_coe x⟩
/-
**Set.projIic_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_surjOn : SurjOn (projIic b) (Iic b) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.projIic_coe`：projIic_coe (x : Iic b) : projIic b x = x
-/
theorem projIic_surjOn : SurjOn (projIic b) (Iic b) univ := fun x _ => ⟨x, x.2, projIic_coe x⟩
/-
**Set.projIcc_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_surjOn : SurjOn (projIcc a b h) (Icc a b) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
-/
theorem projIcc_surjOn : SurjOn (projIcc a b h) (Icc a b) univ := fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩
/-
**Set.projIci_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIci_surjective : Surjective (projIci a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIci_coe`：projIci_coe (x : Ici a) : projIci a x = x
-/
theorem projIci_surjective : Surjective (projIci a) := fun x => ⟨x, projIci_coe x⟩
/-
**Set.projIic_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIic_surjective : Surjective (projIic b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIic_coe`：projIic_coe (x : Iic b) : projIic b x = x
-/
theorem projIic_surjective : Surjective (projIic b) := fun x => ⟨x, projIic_coe x⟩
/-
**Set.projIcc_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：projIcc_surjective : Surjective (projIcc a b h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
-/
theorem projIcc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, projIcc_val h x⟩

@[simp]
/-
**Set.range_projIci** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_projIci : range (projIci a) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.projIci_surjective`：projIci_surjective : Surjective (projIci a)
-/
theorem range_projIci : range (projIci a) = univ := projIci_surjective.range_eq

@[simp]
/-
**Set.range_projIic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_projIic : range (projIic a) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.projIic_surjective`：projIic_surjective : Surjective (projIic b)
-/
theorem range_projIic : range (projIic a) = univ := projIic_surjective.range_eq

@[simp]
/-
**Set.range_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_projIcc : range (projIcc a b h) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.projIcc_surjective`：projIcc_surjective : Surjective (projIcc a b h)
-/
theorem range_projIcc : range (projIcc a b h) = univ :=
  (projIcc_surjective h).range_eq
/-
**Set.monotone_projIci** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_projIci : Monotone (projIci a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monotone_projIci : Monotone (projIci a) := fun _ _ => max_le_max le_rfl
/-
**Set.monotone_projIic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_projIic : Monotone (projIic a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monotone_projIic : Monotone (projIic a) := fun _ _ => min_le_min le_rfl
/-
**Set.monotone_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_projIcc : Monotone (projIcc a b h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
-/
theorem monotone_projIcc : Monotone (projIcc a b h) := fun _ _ hxy =>
  max_le_max le_rfl <| min_le_min le_rfl hxy
/-
**Set.strictMonoOn_projIci** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictMonoOn_projIci : StrictMonoOn (projIci a) (Ici a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIci_of_mem`：projIci_of_mem (hx : x in Ici a) : projIci a x = ⟨x,
 hx⟩
-/
theorem strictMonoOn_projIci : StrictMonoOn (projIci a) (Ici a) := fun x hx y hy hxy => by
  simpa only [projIci_of_mem, hx, hy]
/-
**Set.strictMonoOn_projIic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictMonoOn_projIic : StrictMonoOn (projIic b) (Iic b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIic_of_mem`：projIic_of_mem (hx : x in Iic b) : projIic b x = ⟨x,
 hx⟩
-/
theorem strictMonoOn_projIic : StrictMonoOn (projIic b) (Iic b) := fun x hx y hy hxy => by
  simpa only [projIic_of_mem, hx, hy]
/-
**Set.strictMonoOn_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictMonoOn_projIcc : StrictMonoOn (projIcc a b h) (Icc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
-/
theorem strictMonoOn_projIcc : StrictMonoOn (projIcc a b h) (Icc a b) := fun x hx y hy hxy => by
  simpa only [projIcc_of_mem, hx, hy]

/-- Extend a function `[a, ∞) → β` to a map `α → β`. -/
/-
**Set.IciExtend** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IciExtend (f : Ici a -> β) : α -> β
参数：f : Ici a -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a function `[a, ∞) → β` to a map `α → β`.
-/
def IciExtend (f : Ici a → β) : α → β :=
  f ∘ projIci a

/-- Extend a function `(-∞, b] → β` to a map `α → β`. -/
/-
**Set.IicExtend** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IicExtend (f : Iic b -> β) : α -> β
参数：f : Iic b -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a function `(-∞, b] → β` to a map `α → β`.
-/
def IicExtend (f : Iic b → β) : α → β :=
  f ∘ projIic b

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
/-
**Set.IccExtend** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IccExtend {a b : α} (h : a <= b) (f : Icc a b -> β) : α -> β
参数：h : a <= b；f : Icc a b -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a function `[a, b] → β` to a map `α → β`.
-/
def IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
  f ∘ projIcc a b h
/-
**Set.IciExtend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IciExtend_apply (f : Ici a -> β) (x : α) : IciExtend f x = f ⟨max a x, le_
max_left _ _⟩
参数：f : Ici a -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IciExtend_apply (f : Ici a → β) (x : α) : IciExtend f x = f ⟨max a x, le_max_left _ _⟩ :=
  rfl
/-
**Set.IicExtend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IicExtend_apply (f : Iic b -> β) (x : α) : IicExtend f x = f ⟨min b x, min
_le_left _ _⟩
参数：f : Iic b -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IicExtend_apply (f : Iic b → β) (x : α) : IicExtend f x = f ⟨min b x, min_le_left _ _⟩ :=
  rfl
/-
**Set.IccExtend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_apply (h : a <= b) (f : Icc a b -> β) (x : α) : IccExtend h f x 
= f ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩
参数：h : a <= b；f : Icc a b -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IccExtend_apply (h : a ≤ b) (f : Icc a b → β) (x : α) :
    IccExtend h f x = f ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩ := rfl

@[simp]
/-
**Set.range_IciExtend** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_IciExtend (f : Ici a -> β) : range (IciExtend f) = range f
参数：f : Ici a -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.range_projIci`：range_projIci : range (projIci a) = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_IciExtend (f : Ici a → β) : range (IciExtend f) = range f := by
  simp only [IciExtend, range_comp f, range_projIci, image_univ]

@[simp]
/-
**Set.range_IicExtend** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_IicExtend (f : Iic b -> β) : range (IicExtend f) = range f
参数：f : Iic b -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.range_projIic`：range_projIic : range (projIic a) = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_IicExtend (f : Iic b → β) : range (IicExtend f) = range f := by
  simp only [IicExtend, range_comp f, range_projIic, image_univ]

@[simp]
/-
**Set.IccExtend_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_range (f : Icc a b -> β) : range (IccExtend h f) = range f
参数：f : Icc a b -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.range_projIcc`：range_projIcc : range (projIcc a b h) = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IccExtend_range (f : Icc a b → β) : range (IccExtend h f) = range f := by
  simp only [IccExtend, range_comp f, range_projIcc, image_univ]
/-
**Set.IciExtend_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IciExtend_of_le (f : Ici a -> β) (hx : x <= a) : IciExtend f x = f ⟨a, le_
rfl⟩
参数：f : Ici a -> β；hx : x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.projIci_of_le`：projIci_of_le (hx : x <= a) : projIci a x = ⟨a, le_rf
l⟩
-/
theorem IciExtend_of_le (f : Ici a → β) (hx : x ≤ a) : IciExtend f x = f ⟨a, le_rfl⟩ :=
  congr_arg f <| projIci_of_le hx
/-
**Set.IicExtend_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IicExtend_of_le (f : Iic b -> β) (hx : b <= x) : IicExtend f x = f ⟨b, le_
rfl⟩
参数：f : Iic b -> β；hx : b <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.projIic_of_le`：projIic_of_le (hx : b <= x) : projIic b x = ⟨b, le_rf
l⟩
-/
theorem IicExtend_of_le (f : Iic b → β) (hx : b ≤ x) : IicExtend f x = f ⟨b, le_rfl⟩ :=
  congr_arg f <| projIic_of_le hx
/-
**Set.IccExtend_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_of_le_left (f : Icc a b -> β) (hx : x <= a) : IccExtend h f x = 
f ⟨a, left_mem_Icc.2 h⟩
参数：f : Icc a b -> β；hx : x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.projIcc_of_le_left`：projIcc_of_le_left (hx : x <= a) : projIcc a b h
 x = ⟨a, left_mem_Icc.2 h⟩
-/
theorem IccExtend_of_le_left (f : Icc a b → β) (hx : x ≤ a) :
    IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_le_left h hx
/-
**Set.IccExtend_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_of_right_le (f : Icc a b -> β) (hx : b <= x) : IccExtend h f x =
 f ⟨b, right_mem_Icc.2 h⟩
参数：f : Icc a b -> β；hx : b <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.projIcc_of_right_le`：projIcc_of_right_le (hx : b <= x) : projIcc a b
 h x = ⟨b, right_mem_Icc.2 h⟩
-/
theorem IccExtend_of_right_le (f : Icc a b → β) (hx : b ≤ x) :
    IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_right_le h hx

@[simp]
/-
**Set.IciExtend_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IciExtend_self (f : Ici a -> β) : IciExtend f a = f ⟨a, le_rfl⟩
参数：f : Ici a -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IciExtend_of_le`：IciExtend_of_le (f : Ici a -> β) (hx : x <= a) : Ic
iExtend f x = f ⟨a, le_rfl⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IciExtend_self (f : Ici a → β) : IciExtend f a = f ⟨a, le_rfl⟩ :=
  IciExtend_of_le f le_rfl

@[simp]
/-
**Set.IicExtend_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IicExtend_self (f : Iic b -> β) : IicExtend f b = f ⟨b, le_rfl⟩
参数：f : Iic b -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IicExtend_of_le`：IicExtend_of_le (f : Iic b -> β) (hx : b <= x) : Ii
cExtend f x = f ⟨b, le_rfl⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IicExtend_self (f : Iic b → β) : IicExtend f b = f ⟨b, le_rfl⟩ :=
  IicExtend_of_le f le_rfl

@[simp]
/-
**Set.IccExtend_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_left (f : Icc a b -> β) : IccExtend h f a = f ⟨a, left_mem_Icc.2
 h⟩
参数：f : Icc a b -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_of_le_left`：IccExtend_of_le_left (f : Icc a b -> β) (hx : 
x <= a) : IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IccExtend_left (f : Icc a b → β) : IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  IccExtend_of_le_left h f le_rfl

@[simp]
/-
**Set.IccExtend_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_right (f : Icc a b -> β) : IccExtend h f b = f ⟨b, right_mem_Icc
.2 h⟩
参数：f : Icc a b -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_of_right_le`：IccExtend_of_right_le (f : Icc a b -> β) (hx 
: b <= x) : IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IccExtend_right (f : Icc a b → β) : IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  IccExtend_of_right_le h f le_rfl
/-
**Set.IciExtend_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IciExtend_of_mem (f : Ici a -> β) (hx : x in Ici a) : IciExtend f x = f ⟨x
, hx⟩
参数：f : Ici a -> β；hx : x in Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIci_of_mem`：projIci_of_mem (hx : x in Ici a) : projIci a x = ⟨x,
 hx⟩
-/
theorem IciExtend_of_mem (f : Ici a → β) (hx : x ∈ Ici a) : IciExtend f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIci_of_mem hx
/-
**Set.IicExtend_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IicExtend_of_mem (f : Iic b -> β) (hx : x in Iic b) : IicExtend f x = f ⟨x
, hx⟩
参数：f : Iic b -> β；hx : x in Iic b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIic_of_mem`：projIic_of_mem (hx : x in Iic b) : projIic b x = ⟨x,
 hx⟩
-/
theorem IicExtend_of_mem (f : Iic b → β) (hx : x ∈ Iic b) : IicExtend f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIic_of_mem hx
/-
**Set.IccExtend_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc a b) : IccExtend h f x 
= f ⟨x, hx⟩
参数：f : Icc a b -> β；hx : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
-/
theorem IccExtend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) : IccExtend h f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIcc_of_mem h hx

@[simp]
/-
**Set.IciExtend_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IciExtend_coe (f : Ici a -> β) (x : Ici a) : IciExtend f x = f x
参数：f : Ici a -> β；x : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIci_coe`：projIci_coe (x : Ici a) : projIci a x = x
-/
theorem IciExtend_coe (f : Ici a → β) (x : Ici a) : IciExtend f x = f x :=
  congr_arg f <| projIci_coe x

@[simp]
/-
**Set.IicExtend_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IicExtend_coe (f : Iic b -> β) (x : Iic b) : IicExtend f x = f x
参数：f : Iic b -> β；x : Iic b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIic_coe`：projIic_coe (x : Iic b) : projIic b x = x
-/
theorem IicExtend_coe (f : Iic b → β) (x : Iic b) : IicExtend f x = f x :=
  congr_arg f <| projIic_coe x

@[simp]
/-
**Set.IccExtend_val** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccExtend h f x = f x
参数：f : Icc a b -> β；x : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
-/
theorem IccExtend_val (f : Icc a b → β) (x : Icc a b) : IccExtend h f x = f x :=
  congr_arg f <| projIcc_val h x

/-- If `f : α → β` is a constant both on $(-∞, a]$ and on $[b, +∞)$, then the extension of this
function from $[a, b]$ to the whole line is equal to the original function. -/
/-
**Set.IccExtend_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：IccExtend_eq_self (f : α -> β) (ha : forall x < a, f x = f a) (hb : forall
 x, b < x -> f x = f b) : IccExtend h (f ∘ (↑)) = f
参数：f : α -> β；ha : forall x < a, f x = f a；hb : forall x, b < x -> f x = f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IccExtend_of_le_left`：IccExtend_of_le_left (f : Icc a b -> β) (hx : 
x <= a) : IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.IccExtend_val`：IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccE
xtend h f x = f x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Set.IccExtend_of_right_le`：IccExtend_of_right_le (f : Icc a b -> β) (hx 
: b <= x) : IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩

--- 原说明 ---
If `f : α → β` is a constant both on $(-∞, a]$ and on $[b, +∞)$, then the extens
ion of this
function from $[a, b]$ to the whole line is equal to the original function.
-/
theorem IccExtend_eq_self (f : α → β) (ha : ∀ x < a, f x = f a) (hb : ∀ x, b < x → f x = f b) :
    IccExtend h (f ∘ (↑)) = f := by
  ext x
  rcases lt_or_ge x a with hxa | hax
  · simp [IccExtend_of_le_left _ _ hxa.le, ha x hxa]
  · rcases le_or_gt x b with hxb | hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [IccExtend_val, comp_apply]
    · simp [IccExtend_of_right_le _ _ hbx.le, hb x hbx]

end Set

open Set

variable [Preorder β] {s t : Set α} {a b : α} (h : a ≤ b) {f : Icc a b → β}

/-
**Monotone.IciExtend** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a : α} {f : ↑(Set.Ici a) → β},   Monotone f → Monotone (Set.IciExtend f)
参数：Set.Ici a；Set.IciExtend f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Set.monotone_projIci`：monotone_projIci : Monotone (projIci a)
-/
protected theorem Monotone.IciExtend {f : Ici a → β} (hf : Monotone f) : Monotone (IciExtend f) :=
  hf.comp monotone_projIci
/-
**Monotone.IicExtend** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {b : α} {f : ↑(Set.Iic b) → β},   Monotone f → Monotone (Set.IicExtend f)
参数：Set.Iic b；Set.IicExtend f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Set.monotone_projIic`：monotone_projIic : Monotone (projIic a)
-/
protected theorem Monotone.IicExtend {f : Iic b → β} (hf : Monotone f) : Monotone (IicExtend f) :=
  hf.comp monotone_projIic
/-
**Monotone.IccExtend** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a b : α} (h : a ≤ b)   {f : ↑(Set.Icc a b) → β}, Monotone f → Monotone (Set.
IccExtend h f)
参数：h : a ≤ b；Set.Icc a b；Set.IccExtend h f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Set.monotone_projIcc`：monotone_projIcc : Monotone (projIcc a b h)
-/
protected theorem Monotone.IccExtend (hf : Monotone f) : Monotone (IccExtend h f) :=
  hf.comp <| monotone_projIcc h
/-
**StrictMono.strictMonoOn_IciExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.strictMonoOn_IciExtend {f : Ici a -> β} (hf : StrictMono f) : S
trictMonoOn (IciExtend f) (Ici a)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictMonoOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f 
: α → β} {s : Set …
· 使用定理 `Set.strictMonoOn_projIci`：strictMonoOn_projIci : StrictMonoOn (projIci a
) (Ici a)
-/
theorem StrictMono.strictMonoOn_IciExtend {f : Ici a → β} (hf : StrictMono f) :
    StrictMonoOn (IciExtend f) (Ici a) :=
  hf.comp_strictMonoOn strictMonoOn_projIci
/-
**StrictMono.strictMonoOn_IicExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.strictMonoOn_IicExtend {f : Iic b -> β} (hf : StrictMono f) : S
trictMonoOn (IicExtend f) (Iic b)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictMonoOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f 
: α → β} {s : Set …
· 使用定理 `Set.strictMonoOn_projIic`：strictMonoOn_projIic : StrictMonoOn (projIic b
) (Iic b)
-/
theorem StrictMono.strictMonoOn_IicExtend {f : Iic b → β} (hf : StrictMono f) :
    StrictMonoOn (IicExtend f) (Iic b) :=
  hf.comp_strictMonoOn strictMonoOn_projIic
/-
**StrictMono.strictMonoOn_IccExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.strictMonoOn_IccExtend (hf : StrictMono f) : StrictMonoOn (IccE
xtend h f) (Icc a b)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictMonoOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f 
: α → β} {s : Set …
· 使用定理 `Set.strictMonoOn_projIcc`：strictMonoOn_projIcc : StrictMonoOn (projIcc a
 b h) (Icc a b)
-/
theorem StrictMono.strictMonoOn_IccExtend (hf : StrictMono f) :
    StrictMonoOn (IccExtend h f) (Icc a b) :=
  hf.comp_strictMonoOn (strictMonoOn_projIcc h)
/-
**Set.OrdConnected.IciExtend** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a : α} {s : Set ↑(Set.Ici a)},   
s.OrdConnected → {x | Set.IciExtend (fun x => x ∈ s) x}.OrdConnected
参数：Set.Ici a；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Set.OrdConnected.IciExtend {s : Set (Ici a)} (hs : s.OrdConnected) :
    {x | IciExtend (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨max_le_max le_rfl hz.1, max_le_max le_rfl hz.2⟩⟩
/-
**Set.OrdConnected.IicExtend** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {b : α} {s : Set ↑(Set.Iic b)},   
s.OrdConnected → {x | Set.IicExtend (fun x => x ∈ s) x}.OrdConnected
参数：Set.Iic b；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Set.OrdConnected.IicExtend {s : Set (Iic b)} (hs : s.OrdConnected) :
    {x | IicExtend (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨min_le_min le_rfl hz.1, min_le_min le_rfl hz.2⟩⟩
/-
**Set.OrdConnected.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s t : Set α},   s.OrdConnected → 
{x | t.domRestrict (fun x => x ∈ s) x}.OrdConnected
参数：fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
protected theorem Set.OrdConnected.domRestrict (hs : s.OrdConnected) :
    {x | domRestrict t (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy hz⟩

@[deprecated (since := "2026-07-19")]
alias Set.OrdConnected.restrict := Set.OrdConnected.domRestrict
