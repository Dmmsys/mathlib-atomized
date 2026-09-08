/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Batteries.Data.List.Lemmas

/-!
# Big operators on a list in ordered rings

This file contains the results concerning the interaction of list big operators with ordered rings.
-/

public section

variable {R : Type*}

/-- A variant of `List.prod_pos` for `CanonicallyOrderedAdd`. -/
/-
**CanonicallyOrderedAdd.list_prod_pos** 是 Mathlib 中的一个定理，位于命名空间 `CanonicallyOrde
redAdd`。
形式化陈述：∀ {α : Type u_2} [inst : CommSemiring α] [inst_1 : PartialOrder α] [Canoni
callyOrderedAdd α] [NoZeroDivisors α]   [Nontrivial α] {l : List α}, 0 < l.prod 
↔ ∀ x ∈ l, 0 < x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `List.prod_pos` for `CanonicallyOrderedAdd`.
-/
@[simp] lemma CanonicallyOrderedAdd.list_prod_pos {α : Type*}
    [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [NoZeroDivisors α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
  | (x :: xs) => by simp_rw [List.prod_cons, List.forall_mem_cons, CanonicallyOrderedAdd.mul_pos,
    list_prod_pos]
