/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Chain

/-!
# List of Booleans

In this file we prove lemmas about the number of `false`s and `true`s in a list of Booleans. First
we prove that the number of `false`s plus the number of `true` equals the length of the list. Then
we prove that in a list with alternating `true`s and `false`s, the number of `true`s differs from
the number of `false`s by at most one. We provide several versions of these statements.
-/

public section


namespace List

@[simp]
/-
**List.count_not_add_count** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_not_add_count (l : List Bool) (b : Bool) : count (!b) l + count b l 
= length l
参数：l : List Bool；b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_eq_countP_add_countP`：∀ {α : Type u_1} (p : α → Bool) {l : L
ist α}, l.length = List.countP p l + List.countP (fun a => decide ¬p a = true) l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEqBool`：LawfulBEq Bool
-/
theorem count_not_add_count (l : List Bool) (b : Bool) : count (!b) l + count b l = length l := by
  have := length_eq_countP_add_countP (l := l) (· == !b)
  aesop (add simp this)

grind_pattern count_not_add_count => count (!b) l

@[simp]
/-
**List.count_add_count_not** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_add_count_not (l : List Bool) (b : Bool) : count b l + count (!b) l 
= length l
参数：l : List Bool；b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_add_count_not (l : List Bool) (b : Bool) : count b l + count (!b) l = length l := by
  grind

@[simp]
/-
**List.count_false_add_count_true** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_false_add_count_true (l : List Bool) : count false l + count true l 
= length l
参数：l : List Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_not_add_count`：count_not_add_count (l : List Bool) (b : Bool)
 : count (!b) l + count b l = length l
-/
theorem count_false_add_count_true (l : List Bool) : count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true => count false l
grind_pattern count_false_add_count_true => count true l

@[simp]
/-
**List.count_true_add_count_false** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_true_add_count_false (l : List Bool) : count true l + count false l 
= length l
参数：l : List Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_not_add_count`：count_not_add_count (l : List Bool) (b : Bool)
 : count (!b) l + count b l = length l
-/
theorem count_true_add_count_false (l : List Bool) : count true l + count false l = length l :=
  count_not_add_count l false
/-
**List.IsChain.count_not_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {b : Bool} {l : List Bool},   List.IsChain (fun x1 x2 => x1 ≠ x2) (b :: 
l) → List.count (!b) l = List.count b l + l.length % 2
参数：fun x1 x2 => x1 ≠ x2；b :: l；!b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsChain.count_not_cons :
    ∀ {b : Bool} {l : List Bool}, IsChain (· ≠ ·) (b :: l) →
    count (!b) l = count b l + length l % 2
  | _, [], _h => rfl
  | b, x :: l, h => by
    grind [h.of_cons.count_not_cons]

namespace IsChain

variable {l : List Bool}

/-
**List.IsChain.count_not_eq_count** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：count_not_eq_count (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : B
ool) : count (!b) l = count b l
参数：hl : IsChain (· != ·) l；h2 : Even (length l)；b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_not_eq_count (hl : IsChain (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    count (!b) l = count b l := by
  rcases l with - | ⟨x, l⟩
  · rfl
  grind [count_cons_of_ne x.not_ne_self.symm, hl.count_not_cons]
/-
**List.IsChain.count_false_eq_count_true** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain
`。
形式化陈述：count_false_eq_count_true (hl : IsChain (· != ·) l) (h2 : Even (length l))
 : count false l = count true l
参数：hl : IsChain (· != ·) l；h2 : Even (length l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.count_not_eq_count`：count_not_eq_count (hl : IsChain (· != 
·) l) (h2 : Even (length l)) (b : Bool) : count (!b) l = count b l
-/
theorem count_false_eq_count_true (hl : IsChain (· ≠ ·) l) (h2 : Even (length l)) :
    count false l = count true l :=
  hl.count_not_eq_count h2 true
/-
**List.IsChain.count_not_le_count_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChai
n`。
形式化陈述：count_not_le_count_add_one (hl : IsChain (· != ·) l) (b : Bool) : count (!
b) l <= count b l + 1
参数：hl : IsChain (· != ·) l；b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem count_not_le_count_add_one (hl : IsChain (· ≠ ·) l) (b : Bool) :
    count (!b) l ≤ count b l + 1 := by
  cases l
  · exact zero_le
  grind [hl.count_not_cons]
/-
**List.IsChain.count_false_le_count_true_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List
.IsChain`。
形式化陈述：count_false_le_count_true_add_one (hl : IsChain (· != ·) l) : count false 
l <= count true l + 1
参数：hl : IsChain (· != ·) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.count_not_le_count_add_one`：count_not_le_count_add_one (hl 
: IsChain (· != ·) l) (b : Bool) : count (!b) l <= count b l + 1
-/
theorem count_false_le_count_true_add_one (hl : IsChain (· ≠ ·) l) :
    count false l ≤ count true l + 1 :=
  hl.count_not_le_count_add_one true
/-
**List.IsChain.count_true_le_count_false_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List
.IsChain`。
形式化陈述：count_true_le_count_false_add_one (hl : IsChain (· != ·) l) : count true l
 <= count false l + 1
参数：hl : IsChain (· != ·) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.count_not_le_count_add_one`：count_not_le_count_add_one (hl 
: IsChain (· != ·) l) (b : Bool) : count (!b) l <= count b l + 1
-/
theorem count_true_le_count_false_add_one (hl : IsChain (· ≠ ·) l) :
    count true l ≤ count false l + 1 :=
  hl.count_not_le_count_add_one false
/-
**List.IsChain.two_mul_count_bool_of_even** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChai
n`。
形式化陈述：two_mul_count_bool_of_even (hl : IsChain (· != ·) l) (h2 : Even (length l)
) (b : Bool) : 2 * count b l = length l
参数：hl : IsChain (· != ·) l；h2 : Even (length l)；b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.count_not_add_count`：count_not_add_count (l : List Bool) (b : Bool)
 : count (!b) l + count b l = length l
· 使用定理 `List.IsChain.count_not_eq_count`：count_not_eq_count (hl : IsChain (· != 
·) l) (h2 : Even (length l)) (b : Bool) : count (!b) l = count b l
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem two_mul_count_bool_of_even (hl : IsChain (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    2 * count b l = length l := by
  rw [← count_not_add_count l b, hl.count_not_eq_count h2, two_mul]
/-
**List.IsChain.two_mul_count_bool_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain
`。
形式化陈述：two_mul_count_bool_eq_ite (hl : IsChain (· != ·) l) (b : Bool) : 2 * count
 b l = if Even (length l) then length l else if Option.some b == l.head? then le
ngth l + 1 else length l - 1
参数：hl : IsChain (· != ·) l；b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.IsChain.two_mul_count_bool_of_even`：two_mul_count_bool_of_even (hl 
: IsChain (· != ·) l) (h2 : Even (length l)) (b : Bool) : 2 * count b l = length
 l
· 使用引理 `Even.zero`：Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β))
-/
theorem two_mul_count_bool_eq_ite (hl : IsChain (· ≠ ·) l) (b : Bool) :
    2 * count b l =
      if Even (length l) then length l else
      if Option.some b == l.head? then length l + 1 else length l - 1 := by
  by_cases h2 : Even (length l)
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
  · rcases l with - | ⟨x, l⟩
    · exact (h2 .zero).elim
    grind [hl.tail.two_mul_count_bool_of_even]
/-
**List.IsChain.length_sub_one_le_two_mul_count_bool** 是 Mathlib 中的一个定理，位于命名空间 `L
ist.IsChain`。
形式化陈述：length_sub_one_le_two_mul_count_bool (hl : IsChain (· != ·) l) (b : Bool) 
: length l - 1 <= 2 * count b l
参数：hl : IsChain (· != ·) l；b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_sub_one_le_two_mul_count_bool (hl : IsChain (· ≠ ·) l) (b : Bool) :
    length l - 1 ≤ 2 * count b l := by
  grind [hl.two_mul_count_bool_eq_ite]
/-
**List.IsChain.length_div_two_le_count_bool** 是 Mathlib 中的一个定理，位于命名空间 `List.IsCh
ain`。
形式化陈述：length_div_two_le_count_bool (hl : IsChain (· != ·) l) (b : Bool) : length
 l / 2 <= count b l
参数：hl : IsChain (· != ·) l；b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_le_iff_le_mul_add_pred`：∀ {b a c : ℕ}, 0 < b → (a / b ≤ c ↔ a ≤ 
b * c + (b - 1))
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `List.IsChain.length_sub_one_le_two_mul_count_bool`：length_sub_one_le_two
_mul_count_bool (hl : IsChain (· != ·) l) (b : Bool) : length l - 1 <= 2 * count
 b l
-/
theorem length_div_two_le_count_bool (hl : IsChain (· ≠ ·) l) (b : Bool) :
    length l / 2 ≤ count b l := by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos, ← tsub_le_iff_right]
  exact length_sub_one_le_two_mul_count_bool hl b
/-
**List.IsChain.two_mul_count_bool_le_length_add_one** 是 Mathlib 中的一个定理，位于命名空间 `L
ist.IsChain`。
形式化陈述：two_mul_count_bool_le_length_add_one (hl : IsChain (· != ·) l) (b : Bool) 
: 2 * count b l <= length l + 1
参数：hl : IsChain (· != ·) l；b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem two_mul_count_bool_le_length_add_one (hl : IsChain (· ≠ ·) l) (b : Bool) :
    2 * count b l ≤ length l + 1 := by
  grind [hl.two_mul_count_bool_eq_ite]

end IsChain

end List

