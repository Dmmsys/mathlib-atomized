/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

public section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

/--
theorem `IsGLB.exists_between_self_add` / 定理 `IsGLB.exists_between_self_add`

English:
theorem IsGLB.exists_between_self_add
  given: (h : IsGLB s a) (hε : 0 < ε)
  statement: exists b in s, a <= b ∧ b < a + ε
  proof: h.exists_between lt_add_of_pos_right _ hε

中文:
定理 IsGLB.exists_between_self_add
  条件: (h : IsGLB s a) (hε : 0 < ε)
  结论: 存在 b in s, a <= b ∧ b < a + ε
  证明: h.exists_between lt_add_of_pos_right _ hε

Depends on / 依赖: exists_between, h.exists_between, lt_add_of_pos_right
-/
theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : exists b in s, a <= b ∧ b < a + ε :=
h.exists_between lt_add_of_pos_right _ hε

/--
theorem `IsGLB.exists_between_self_add'` / 定理 `IsGLB.exists_between_self_add'`

English:
theorem IsGLB.exists_between_self_add'
  given: (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε)
  proof: h.exists_between' h₂ lt_add_of_pos_right _ hε

中文:
定理 IsGLB.exists_between_self_add'
  条件: (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε)
  证明: h.exists_between' h₂ lt_add_of_pos_right _ hε

Depends on / 依赖: exists_between, h.exists_between, lt_add_of_pos_right
-/
theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    exists b in s, a < b ∧ b < a + ε :=
h.exists_between' h₂ lt_add_of_pos_right _ hε

/--
theorem `IsLUB.exists_between_sub_self` / 定理 `IsLUB.exists_between_sub_self`

English:
theorem IsLUB.exists_between_sub_self
  given: (h : IsLUB s a) (hε : 0 < ε)
  statement: exists b in s, a - ε < b ∧ b <= a
  proof: h.exists_between sub_lt_self _ hε

中文:
定理 IsLUB.exists_between_sub_self
  条件: (h : IsLUB s a) (hε : 0 < ε)
  结论: 存在 b in s, a - ε < b ∧ b <= a
  证明: h.exists_between sub_lt_self _ hε

Depends on / 依赖: exists_between, h.exists_between, sub_lt_self
-/
theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : exists b in s, a - ε < b ∧ b <= a :=
h.exists_between sub_lt_self _ hε

/--
theorem `IsLUB.exists_between_sub_self'` / 定理 `IsLUB.exists_between_sub_self'`

English:
theorem IsLUB.exists_between_sub_self'
  given: (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε)
  proof: h.exists_between' h₂ sub_lt_self _ hε

中文:
定理 IsLUB.exists_between_sub_self'
  条件: (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε)
  证明: h.exists_between' h₂ sub_lt_self _ hε

Depends on / 依赖: exists_between, h.exists_between, sub_lt_self
-/
theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    exists b in s, a - ε < b ∧ b < a :=
h.exists_between' h₂ sub_lt_self _ hε

end LinearOrderedAddCommGroup
