/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/

public section


open Function

variable {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/

section CommSemigroup
variable [LinearOrder α] [CommSemigroup β]

@[to_additive]
/-
**fn_min_mul_fn_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fn_min_mul_fn_max (f : α -> β) (a b : α) : f (min a b) * f (max a b) = f a
 * f b
参数：f : α -> β；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fn_min_mul_fn_max (f : α → β) (a b : α) : f (min a b) * f (max a b) = f a * f b := by
  grind

@[to_additive]
/-
**fn_max_mul_fn_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fn_max_mul_fn_min (f : α -> β) (a b : α) : f (max a b) * f (min a b) = f a
 * f b
参数：f : α -> β；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fn_max_mul_fn_min (f : α → β) (a b : α) : f (max a b) * f (min a b) = f a * f b := by
  grind

variable [CommSemigroup α]

@[to_additive (attr := simp)]
/-
**min_mul_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_mul_max (a b : α) : min a b * max a b = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `fn_min_mul_fn_max`：fn_min_mul_fn_max (f : α -> β) (a b : α) : f (min a b
) * f (max a b) = f a * f b
-/
lemma min_mul_max (a b : α) : min a b * max a b = a * b := fn_min_mul_fn_max id _ _

@[to_additive (attr := simp)]
/-
**max_mul_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_mul_min (a b : α) : max a b * min a b = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `fn_max_mul_fn_min`：fn_max_mul_fn_min (f : α -> β) (a b : α) : f (max a b
) * f (min a b) = f a * f b
-/
lemma max_mul_min (a b : α) : max a b * min a b = a * b := fn_max_mul_fn_min id _ _

end CommSemigroup

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [MulLeftMono α]

@[to_additive]
/-
**min_mul_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Monotone.const_mul'`：Monotone.const_mul' [MulLeftMono α] (hf : Monotone 
f) (a : α) : Monotone fun x => a * f x
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
/-
**max_mul_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Monotone.const_mul'`：Monotone.const_mul' [MulLeftMono α] (hf : Monotone 
f) (a : α) : Monotone fun x => a * f x
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable [MulRightMono α]

@[to_additive]
/-
**min_mul_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Monotone.mul_const'`：Monotone.mul_const' [MulRightMono α] (hf : Monotone
 f) (a : α) : Monotone fun x => f x * a
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
/-
**max_mul_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Monotone.mul_const'`：Monotone.mul_const' [MulRightMono α] (hf : Monotone
 f) (a : α) : Monotone fun x => f x * a
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

@[to_additive]
/-
**lt_or_lt_of_mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} 
: a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]
/-
**le_or_lt_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_or_lt_of_mul_le_mul [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂
 : α} : a₁ * b₁ <= a₂ * b₂ -> a₁ <= a₂ ∨ b₁ < b₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_or_lt_of_mul_le_mul [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]
/-
**lt_or_le_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂
 : α} : a₁ * b₁ <= a₂ * b₂ -> a₁ < a₂ ∨ b₁ <= b₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lt_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]
/-
**le_or_le_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂
 b₁ b₂ : α} : a₁ * b₁ <= a₂ * b₂ -> a₁ <= a₂ ∨ b₁ <= b₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]
/-
**mul_lt_mul_iff_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_iff_of_le_of_le [MulLeftMono α] [MulRightMono α] [MulLeftStrict
Mono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ <= a₂) (hb : b₁ <= b₂)
 : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
-/
theorem mul_lt_mul_iff_of_le_of_le [MulLeftMono α]
    [MulRightMono α] [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

end Mul

variable [MulOneClass α]

@[to_additive]
/-
**min_le_mul_of_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_le_mul_of_one_le_right [MulLeftMono α] {a b : α} (hb : 1 <= b) : min a
 b <= a * b
参数：hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
-/
theorem min_le_mul_of_one_le_right [MulLeftMono α] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

@[to_additive]
/-
**min_le_mul_of_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_le_mul_of_one_le_left [MulRightMono α] {a b : α} (ha : 1 <= a) : min a
 b <= a * b
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
-/
theorem min_le_mul_of_one_le_left [MulRightMono α] {a b : α} (ha : 1 ≤ a) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

@[to_additive]
/-
**max_le_mul_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_le_mul_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 <=
 a) (hb : 1 <= b) : max a b <= a * b
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
-/
theorem max_le_mul_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe

