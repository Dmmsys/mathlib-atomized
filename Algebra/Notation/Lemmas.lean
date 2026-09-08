/-
Copyright (c) 2023 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
module

public import Batteries.Tactic.Init
public import Mathlib.Tactic.ToAdditive

/-! # Lemmas about inequalities with `1`. -/

public section

assert_not_exists Monoid

variable {α : Type*}

section dite
variable [One α] {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α}

@[to_additive dite_nonneg]
/-
**one_le_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_dite [LE α] (ha : forall h, 1 <= a h) (hb : forall h, 1 <= b h) : 1
 <= dite p a b
参数：ha : forall h, 1 <= a h；hb : forall h, 1 <= b h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma one_le_dite [LE α] (ha : ∀ h, 1 ≤ a h) (hb : ∀ h, 1 ≤ b h) : 1 ≤ dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
/-
**dite_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_le_one [LE α] (ha : forall h, a h <= 1) (hb : forall h, b h <= 1) : d
ite p a b <= 1
参数：ha : forall h, a h <= 1；hb : forall h, b h <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_le_one [LE α] (ha : ∀ h, a h ≤ 1) (hb : ∀ h, b h ≤ 1) : dite p a b ≤ 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive dite_pos]
/-
**one_lt_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_dite [LT α] (ha : forall h, 1 < a h) (hb : forall h, 1 < b h) : 1 <
 dite p a b
参数：ha : forall h, 1 < a h；hb : forall h, 1 < b h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma one_lt_dite [LT α] (ha : ∀ h, 1 < a h) (hb : ∀ h, 1 < b h) : 1 < dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
/-
**dite_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_lt_one [LT α] (ha : forall h, a h < 1) (hb : forall h, b h < 1) : dit
e p a b < 1
参数：ha : forall h, a h < 1；hb : forall h, b h < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_lt_one [LT α] (ha : ∀ h, a h < 1) (hb : ∀ h, b h < 1) : dite p a b < 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

end dite

section
variable [One α] {p : Prop} [Decidable p] {a b : α}

@[to_additive ite_nonneg]
/-
**one_le_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_ite [LE α] (ha : 1 <= a) (hb : 1 <= b) : 1 <= ite p a b
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma one_le_ite [LE α] (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ ite p a b := by split <;> assumption

@[to_additive]
/-
**ite_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_le_one [LE α] (ha : a <= 1) (hb : b <= 1) : ite p a b <= 1
参数：ha : a <= 1；hb : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma ite_le_one [LE α] (ha : a ≤ 1) (hb : b ≤ 1) : ite p a b ≤ 1 := by split <;> assumption

@[to_additive ite_pos]
/-
**one_lt_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_ite [LT α] (ha : 1 < a) (hb : 1 < b) : 1 < ite p a b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma one_lt_ite [LT α] (ha : 1 < a) (hb : 1 < b) : 1 < ite p a b := by split <;> assumption

@[to_additive]
/-
**ite_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_lt_one [LT α] (ha : a < 1) (hb : b < 1) : ite p a b < 1
参数：ha : a < 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma ite_lt_one [LT α] (ha : a < 1) (hb : b < 1) : ite p a b < 1 := by split <;> assumption

end

