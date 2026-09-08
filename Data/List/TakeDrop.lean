/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Logic.Function.Iterate

/-!
# `Take` and `Drop` lemmas for lists

This file provides lemmas about `List.take` and `List.drop` and related functions.
-/

public section

assert_not_exists GroupWithZero
assert_not_exists Lattice
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Ring
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-! ### take, drop -/

/-
**List.take_one_drop_eq_of_lt_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：take_one_drop_eq_of_lt_length {l : List α} {n : Nat} (h : n < l.length) : 
(l.drop n).take 1 = [l.get ⟨n, h⟩]
参数：h : n < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_eq_getElem_cons`：∀ {α : Type u_1} {i : ℕ} {l : List α} (h : i 
< l.length), List.drop i l = l[i] :: List.drop (i + 1) l
· 使用定理 `List.take.eq_3`：∀ {α : Type u} (n : ℕ) (a : α) (as : List α), List.take 
n.succ (a :: as) = a :: List.take n as
· 使用定理 `List.take.eq_1`：∀ {α : Type u} (x : List α), List.take 0 x = []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### take, drop
-/
theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h, take, take]
  simp
/-
**List.take_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (x : List α) {n : ℕ}, List.take n x = x ↔ x.length ≤ n
参数：x : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
-/
@[simp] lemma take_eq_self_iff (x : List α) {n : ℕ} : x.take n = x ↔ x.length ≤ n :=
  ⟨by grind, take_of_length_le⟩
/-
**List.take_self_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (x : List α) {n : ℕ}, x = List.take n x ↔ x.length ≤ n
参数：x : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `List.take_eq_self_iff`：∀ {α : Type u} (x : List α) {n : ℕ}, List.take n 
x = x ↔ x.length ≤ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma take_self_eq_iff (x : List α) {n : ℕ} : x = x.take n ↔ x.length ≤ n := by
  rw [Eq.comm, take_eq_self_iff]
/-
**List.take_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {x y : List α} {n : ℕ}, List.take n (x ++ y) = List.take n 
x ↔ y = [] ∨ n ≤ x.length
参数：x ++ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma take_eq_left_iff {x y : List α} {n : ℕ} :
    (x ++ y).take n = x.take n ↔ y = [] ∨ n ≤ x.length := by
  simp [take_append, Nat.sub_eq_zero_iff_le, Or.comm]
/-
**List.left_eq_take_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {x y : List α} {n : ℕ}, List.take n x = List.take n (x ++ y
) ↔ y = [] ∨ n ≤ x.length
参数：x ++ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `List.take_eq_left_iff`：∀ {α : Type u} {x y : List α} {n : ℕ}, List.take 
n (x ++ y) = List.take n x ↔ y = [] ∨ n ≤ x.length
-/
@[simp] lemma left_eq_take_iff {x y : List α} {n : ℕ} :
    x.take n = (x ++ y).take n ↔ y = [] ∨ n ≤ x.length := by
  rw [Eq.comm]; apply take_eq_left_iff
/-
**List.drop_take_append_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (x : List α) (m n : ℕ), List.take n (List.drop m x) ++ List
.drop (m + n) x = List.drop m x
参数：x : List α；m n : ℕ；List.drop m x；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
@[simp] lemma drop_take_append_drop (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (m + n) = x.drop m := by rw [← drop_drop, take_append_drop]

/-- Compared to `drop_take_append_drop`, the order of summands is swapped. -/
/-
**List.drop_take_append_drop'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (x : List α) (m n : ℕ), List.take n (List.drop m x) ++ List
.drop (n + m) x = List.drop m x
参数：x : List α；m n : ℕ；List.drop m x；n + m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `List.drop_take_append_drop`：∀ {α : Type u} (x : List α) (m n : ℕ), List.
take n (List.drop m x) ++ List.drop (m + n) x = List.drop m x

--- 原说明 ---
Compared to `drop_take_append_drop`, the order of summands is swapped.
-/
@[simp] lemma drop_take_append_drop' (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (n + m) = x.drop m := by rw [Nat.add_comm, drop_take_append_drop]

/-- `take_concat_get` in simp normal form -/
/-
**List.take_concat_get'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：take_concat_get' (l : List α) (i : Nat) (h : i < l.length) : l.take i ++ [
l[i]] = l.take (i + 1)
参数：l : List α；i : Nat；h : i < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_append_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), List.take i l ++ [l[i]] = List.take (i + 1) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`take_concat_get` in simp normal form
-/
lemma take_concat_get' (l : List α) (i : ℕ) (h : i < l.length) :
    l.take i ++ [l[i]] = l.take (i + 1) := by simp
/-
**List.cons_getElem_drop_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} : l[n] ::
 l.drop (n + 1) = l.drop n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_eq_getElem_cons`：∀ {α : Type u_1} {i : ℕ} {l : List α} (h : i 
< l.length), List.drop i l = l[i] :: List.drop (i + 1) l
-/
theorem cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} :
    l[n] :: l.drop (n + 1) = l.drop n :=
  (drop_eq_getElem_cons h).symm
/-
**List.cons_get_drop_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_get_drop_succ {l : List α} {n} : l.get n :: l.drop (n.1 + 1) = l.drop
 n.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.drop_eq_getElem_cons`：∀ {α : Type u_1} {i : ℕ} {l : List α} (h : i 
< l.length), List.drop i l = l[i] :: List.drop (i + 1) l
-/
theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 :=
  (drop_eq_getElem_cons n.2).symm
/-
**List.drop_length_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：drop_length_sub_one {l : List α} (h : l != []) : l.drop (l.length - 1) = [
l.getLast h]
参数：h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `List.drop_length_cons`：∀ {α : Type u_1} {l : List α} (h : l ≠ []) (a : α
), List.drop l.length (a :: l) = [l.getLast h]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
-/
lemma drop_length_sub_one {l : List α} (h : l ≠ []) : l.drop (l.length - 1) = [l.getLast h] := by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    rw [length_cons, Nat.add_one_sub_one, List.drop_length_cons hl a]
    simp [getLast_cons, hl]

/-- Applying `tail` to a list `n` times is equivalent to dropping `n` elements. -/
/-
**List.tail_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_iterate (l : List α) (n : Nat) : (List.tail^[n]) l = l.drop n
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l

--- 原说明 ---
Applying `tail` to a list `n` times is equivalent to dropping `n` elements.
-/
theorem tail_iterate (l : List α) (n : ℕ) : (List.tail^[n]) l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [*]

section TailDropLast

variable (l : List α) (n : ℕ)

/-
**List.tail_take_eq_take_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_take_eq_take_tail : (l.take n).tail = l.tail.take (n - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
-/
theorem tail_take_eq_take_tail : (l.take n).tail = l.tail.take (n - 1) := by
  ext
  grind
/-
**List.dropLast_take_eq_take_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropLast_take_eq_take_dropLast : (l.take n).dropLast = l.dropLast.take (n 
- 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
-/
theorem dropLast_take_eq_take_dropLast : (l.take n).dropLast = l.dropLast.take (n - 1) := by
  ext
  grind
/-
**List.tail_drop_eq_drop_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_drop_eq_drop_tail : (l.drop n).tail = l.tail.drop n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
-/
theorem tail_drop_eq_drop_tail : (l.drop n).tail = l.tail.drop n := by
  ext
  grind
/-
**List.dropLast_drop_eq_drop_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropLast_drop_eq_drop_dropLast : (l.drop n).dropLast = l.dropLast.drop n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
-/
theorem dropLast_drop_eq_drop_dropLast : (l.drop n).dropLast = l.dropLast.drop n := by
  ext
  grind

end TailDropLast

section TakeI

variable [Inhabited α]

@[simp]
/-
**List.takeI_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} [inst : Inhabited α] (n : ℕ) (l : List α), (List.takeI n l)
.length = n
参数：n : ℕ；l : List α；List.takeI n l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)

@[simp]
/-
**List.takeI_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} [inst : Inhabited α] (n : ℕ), List.takeI n [] = List.replic
ate n default
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)
/-
**List.takeI_eq_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} [inst : Inhabited α] {n : ℕ} {l : List α}, n ≤ l.length → L
ist.takeI n l = List.take n l
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h

@[simp]
/-
**List.takeI_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.takeI_eq_take`：∀ {α : Type u} [inst : Inhabited α] {n : ℕ} {l : Lis
t α}, n ≤ l.length → List.takeI n l = List.take n l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.take_left`：∀ {α : Type u_1} {l₁ l₂ : List α}, List.take l₁.length (
l₁ ++ l₂) = l₁
-/
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans take_left
/-
**List.takeI_left'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) 
= l₁
参数：h : length l₁ = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.takeI_left`：takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ 
l₂) = l₁
-/
theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left

end TakeI

/- The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
/-
**List.takeD_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (n : ℕ) (l : List α) (a : α), (List.takeD n l a).length = n
参数：n : ℕ；l : List α；a : α；List.takeD n l a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- `takeD_nil` is already in batteries
/-
**List.takeD_eq_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {n : ℕ} {l : List α} (a : α), n ≤ l.length → List.takeD n l
 a = List.take n l
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
/-
**List.takeD_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁
参数：l₁ l₂ : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.takeD_eq_take`：∀ {α : Type u} {n : ℕ} {l : List α} (a : α), n ≤ l.l
ength → List.takeD n l a = List.take n l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.take_left`：∀ {α : Type u_1} {l₁ l₂ : List α}, List.take l₁.length (
l₁ ++ l₂) = l₁
-/
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans take_left
/-
**List.takeD_left'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ 
l₂) a = l₁
参数：h : length l₁ = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.takeD_left`：takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁)
 (l₁ ++ l₂) a = l₁
-/
theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ := by
  rw [← h]; apply takeD_left

end TakeD

/-! ### filter -/

section Filter

variable (p)

variable (p : α → Bool)

/-
**List.span.loop_eq_take_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem span.loop_eq_take_drop :
    ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
/-
**List.span_eq_takeWhile_dropWhile** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：span_eq_takeWhile_dropWhile (l : List α) : span p l = (takeWhile p l, drop
While p l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.TakeDrop.0.List.span.loop_eq_take_drop`：∀ {α 
: Type u} (p : α → Bool) (l₁ l₂ : List α),   List.span.loop p l₁ l₂ = (l₂.revers
e ++ List.takeWhile p l₁, List.dropWhile p l₁)
-/
theorem span_eq_takeWhile_dropWhile (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using! span.loop_eq_take_drop p l []

end Filter

/-! ### Miscellaneous lemmas -/

/-
**List.dropSlice_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropSlice_eq (xs : List α) (n m : Nat) : dropSlice n m xs = xs.take n ++ x
s.drop (n + m)
参数：xs : List α；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### Miscellaneous lemmas
-/
theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs with cases xs with grind [dropSlice]

@[simp, grind =]
/-
**List.length_dropSlice** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_dropSlice (i j : Nat) (xs : List α) : (dropSlice i j xs).length = x
s.length - min j (xs.length - i)
参数：i j : Nat；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_dropSlice (i j : ℕ) (xs : List α) :
    (dropSlice i j xs).length = xs.length - min j (xs.length - i) := by
  induction xs generalizing i j with cases i with grind [dropSlice]
/-
**List.length_dropSlice_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_dropSlice_lt (i j : Nat) (hj : 0 < j) (xs : List α) (hi : i < xs.le
ngth) : (dropSlice i j xs).length < xs.length
参数：i j : Nat；hj : 0 < j；xs : List α；hi : i < xs.length。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_dropSlice_lt (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    (dropSlice i j xs).length < xs.length := by grind

end List

