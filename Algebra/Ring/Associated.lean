/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Units

/-!
# Associated elements in rings
-/

public section

assert_not_exists IsOrderedMonoid Multiset Field

namespace Associated
variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

/-
**Associated.neg_left** 是 Mathlib 中的一个引理，位于命名空间 `Associated`。
形式化陈述：neg_left (h : Associated a b) : Associated (-a) b
参数：h : Associated a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_left (h : Associated a b) : Associated (-a) b := let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩
/-
**Associated.neg_right** 是 Mathlib 中的一个引理，位于命名空间 `Associated`。
形式化陈述：neg_right (h : Associated a b) : Associated a (-b)
参数：h : Associated a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用引理 `Associated.neg_left`：neg_left (h : Associated a b) : Associated (-a) b
-/
lemma neg_right (h : Associated a b) : Associated a (-b) := h.symm.neg_left.symm
/-
**Associated.neg_neg** 是 Mathlib 中的一个引理，位于命名空间 `Associated`。
形式化陈述：neg_neg (h : Associated a b) : Associated (-a) (-b)
参数：h : Associated a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Associated.neg_right`：neg_right (h : Associated a b) : Associated a (-b)
· 使用引理 `Associated.neg_left`：neg_left (h : Associated a b) : Associated (-a) b
-/
lemma neg_neg (h : Associated a b) : Associated (-a) (-b) := h.neg_left.neg_right

@[simp]
/-
**Associated.neg_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Associated`。
形式化陈述：neg_left_iff : Associated (-a) b ↔ Associated a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Associated.neg_left`：neg_left (h : Associated a b) : Associated (-a) b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_left_iff : Associated (-a) b ↔ Associated a b :=
  ⟨fun h ↦ _root_.neg_neg a ▸ h.neg_left, fun h ↦ h.neg_left⟩

@[simp]
/-
**Associated.neg_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Associated`。
形式化陈述：neg_right_iff : Associated a (-b) ↔ Associated a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Associated.neg_right`：neg_right (h : Associated a b) : Associated a (-b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_right_iff : Associated a (-b) ↔ Associated a b :=
  ⟨fun h ↦ _root_.neg_neg b ▸ h.neg_right, fun h ↦ h.neg_right⟩

end Associated

