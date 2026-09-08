/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
module

public import Mathlib.Data.List.Induction

/-!
# Palindromes

This module defines *palindromes*, lists which are equal to their reverse.

The main result is the `Palindrome` inductive type, and its associated `Palindrome.rec` induction
principle. Also provided are conversions to and from other equivalent definitions.

## References

* [Pierre Castéran, *On palindromes*][casteran]

[casteran]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html

## Tags

palindrome, reverse, induction
-/

public section


variable {α β : Type*}

namespace List

/-- `Palindrome l` asserts that `l` is a palindrome. This is defined inductively:

* The empty list is a palindrome;
* A list with one element is a palindrome;
* Adding the same element to both ends of a palindrome results in a bigger palindrome.
-/
/-
**List.Palindrome** 是 Mathlib 中的一个归纳类型，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → List α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Palindrome l` asserts that `l` is a palindrome. This is defined inductively:

* The empty list is a palindrome;
* A list with one element is a palindrome;
* Adding the same element to both ends of a palindrome results in a bigger palin
drome.
-/
inductive Palindrome : List α → Prop
  | nil : Palindrome []
  | singleton : ∀ x, Palindrome [x]
  | cons_concat : ∀ (x) {l}, Palindrome l → Palindrome (x :: (l ++ [x]))

namespace Palindrome

variable {l : List α}

/-
**List.Palindrome.reverse_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Palindrome`。
形式化陈述：reverse_eq {l : List α} (p : Palindrome l) : reverse l = l
参数：p : Palindrome l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.append_cancel_right_eq`：∀ {α : Type u_1} (as bs cs : List α), (as +
+ bs = cs ++ bs) = (as = cs)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem reverse_eq {l : List α} (p : Palindrome l) : reverse l = l := by
  induction p <;> try (exact rfl)
  simpa
/-
**List.Palindrome.of_reverse_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Palindrome`。
形式化陈述：of_reverse_eq {l : List α} : reverse l = l -> Palindrome l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head_eq_of_cons_eq`：∀ {α : Type u_1} {h₁ : α} {t₁ : List α} {h₂ : α
} {t₂ : List α}, h₁ :: t₁ = h₂ :: t₂ → h₁ = h₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_inj_left'`：∀ {α : Type u_1} {s₁ t₁ s₂ t₂ : List α}, s₁ ++ t₁
 = s₂ ++ t₂ → t₁.length = t₂.length → s₁ = s₂
· 使用定理 `List.tail_eq_of_cons_eq`：∀ {α : Type u_1} {h₁ : α} {t₁ : List α} {h₂ : α
} {t₂ : List α}, h₁ :: t₁ = h₂ :: t₂ → t₁ = t₂
-/
theorem of_reverse_eq {l : List α} : reverse l = l → Palindrome l := by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons, reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat x this
/-
**List.Palindrome.iff_reverse_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Palindrome`。
形式化陈述：iff_reverse_eq {l : List α} : Palindrome l ↔ reverse l = l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Palindrome.reverse_eq`：reverse_eq {l : List α} (p : Palindrome l) :
 reverse l = l
· 使用定理 `List.Palindrome.of_reverse_eq`：of_reverse_eq {l : List α} : reverse l = 
l -> Palindrome l
-/
theorem iff_reverse_eq {l : List α} : Palindrome l ↔ reverse l = l :=
  Iff.intro reverse_eq of_reverse_eq
/-
**List.Palindrome.append_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List.Palindrome`。
形式化陈述：append_reverse (l : List α) : Palindrome (l ++ reverse l)
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Palindrome.of_reverse_eq`：of_reverse_eq {l : List α} : reverse l = 
l -> Palindrome l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem append_reverse (l : List α) : Palindrome (l ++ reverse l) := by
  apply of_reverse_eq
  rw [reverse_append, reverse_reverse]
/-
**List.Palindrome.map** 是 Mathlib 中的一个定理，位于命名空间 `List.Palindrome`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : List α} (f : α → β), l.Palindrome → (
List.map f l).Palindrome
参数：f : α → β；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Palindrome.of_reverse_eq`：of_reverse_eq {l : List α} : reverse l = 
l -> Palindrome l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.Palindrome.reverse_eq`：reverse_eq {l : List α} (p : Palindrome l) :
 reverse l = l
-/
protected theorem map (f : α → β) (p : Palindrome l) : Palindrome (map f l) :=
  of_reverse_eq <| by rw [← map_reverse, p.reverse_eq]
/-
**List.Palindrome.** 是 Mathlib 中的一个实例，位于命名空间 `List.Palindrome`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (l : List α) : Decidable (Palindrome l) :=
  decidable_of_iff' _ iff_reverse_eq

end Palindrome

end List

