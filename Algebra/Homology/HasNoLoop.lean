/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Complex shapes with no loop

Let `c : ComplexShape ι`. We define a type class `c.HasNoLoop`
which expresses that `¬ c.Rel i i` for all `i : ι`.

-/

public section

namespace ComplexShape

variable {ι : Type*}

/--
Definition of `HasNoLoop` / `HasNoLoop` 的定义

English:
class HasNoLoop
  parameters: (c : ComplexShape ι)
  axioms and operations (1):
    - not_rel_self((i : ι)) : ¬ c.Rel i i

中文:
类 HasNoLoop
  参数: (c : ComplexShape ι)
  公理与运算 (1 个):
    - not_rel_self((i : ι)) : ¬ c.Rel i i
-/
class HasNoLoop (c : ComplexShape ι) : Prop where
  not_rel_self (i : ι) : ¬ c.Rel i i

section

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

/--
lemma `not_rel_self` / 引理 `not_rel_self`

English:
lemma not_rel_self
  statement: ¬ c.Rel j j
  proof: HasNoLoop.not_rel_self j

中文:
引理 not_rel_self
  结论: ¬ c.Rel j j
  证明: HasNoLoop.not_rel_self j

Depends on / 依赖: HasNoLoop, HasNoLoop.not_rel_self, not_rel_self
-/
lemma not_rel_self : ¬ c.Rel j j :=
  HasNoLoop.not_rel_self j

variable {j} in
/--
lemma `not_rel_of_eq` / 引理 `not_rel_of_eq`

English:
lemma not_rel_of_eq
  given: {j' : ι} (h : j = j')
  statement: ¬ c.Rel j j'
  proof: by
  subst h
  exact c.not_rel_self j

中文:
引理 not_rel_of_eq
  条件: {j' : ι} (h : j = j')
  结论: ¬ c.Rel j j'
  证明: by
  subst h
  exact c.not_rel_self j

Depends on / 依赖: c.not_rel_self, not_rel_self
-/
lemma not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j' := by
  subst h
  exact c.not_rel_self j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: c.symm.HasNoLoop
  body: c.not_rel_self j

中文:
实例 :
  签名: c.symm.HasNoLoop
  定义体: c.not_rel_self j

Depends on / 依赖: c.not_rel_self, not_rel_self
-/
instance : c.symm.HasNoLoop where
  not_rel_self j := c.not_rel_self j

/--
lemma `exists_distinct_prev_or` / 引理 `exists_distinct_prev_or`

English:
lemma exists_distinct_prev_or
  proof: by
  grind +splitIndPred

中文:
引理 exists_distinct_prev_or
  证明: by
  grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
lemma exists_distinct_prev_or :
    (exists (k : ι), c.Rel j k ∧ j != k) ∨ forall (k : ι), ¬ c.Rel j k := by
  grind +splitIndPred

/--
lemma `exists_distinct_next_or` / 引理 `exists_distinct_next_or`

English:
lemma exists_distinct_next_or
  proof: by
  grind +splitIndPred

中文:
引理 exists_distinct_next_or
  证明: by
  grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
lemma exists_distinct_next_or :
    (exists (i : ι), c.Rel i j ∧ i != j) ∨ forall (i : ι), ¬ c.Rel i j := by
  grind +splitIndPred

/--
lemma `hasNoLoop_up'` / 引理 `hasNoLoop_up'`

English:
lemma hasNoLoop_up'
  statement: {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  proof: ha (add_left_cancel (by rw [add_zero, hi]))

中文:
引理 hasNoLoop_up'
  结论: {α : 类型} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  证明: ha (add_left_cancel (by rw [add_zero, hi]))

Depends on / 依赖: add_left_cancel, add_zero
-/
lemma hasNoLoop_up' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a != 0) :
    (up' a).HasNoLoop where
  not_rel_self i (hi : _ = _) :=
    ha (add_left_cancel (by rw [add_zero, hi]))

/--
lemma `hasNoLoop_down'` / 引理 `hasNoLoop_down'`

English:
lemma hasNoLoop_down'
  statement: {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  proof: by
  have := hasNoLoop_up' a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop

中文:
引理 hasNoLoop_down'
  结论: {α : 类型} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  证明: by
  have := hasNoLoop_up' a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop

Depends on / 依赖: HasNoLoop, hasNoLoop_up, symm.HasNoLoop
-/
lemma hasNoLoop_down' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a != 0) :
    (down' a).HasNoLoop := by
  have := hasNoLoop_up' a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop

/--
lemma `hasNoLoop_up` / 引理 `hasNoLoop_up`

English:
lemma hasNoLoop_up
  statement: {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  proof: hasNoLoop_up' _ ha

中文:
引理 hasNoLoop_up
  结论: {α : 类型} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  证明: hasNoLoop_up' _ ha

Depends on / 依赖: hasNoLoop_up
-/
lemma hasNoLoop_up {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) != 0) :
    (up α).HasNoLoop :=
  hasNoLoop_up' _ ha

/--
lemma `hasNoLoop_down` / 引理 `hasNoLoop_down`

English:
lemma hasNoLoop_down
  statement: {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  proof: hasNoLoop_down' _ ha

中文:
引理 hasNoLoop_down
  结论: {α : 类型} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
  证明: hasNoLoop_down' _ ha

Depends on / 依赖: hasNoLoop_down
-/
lemma hasNoLoop_down {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) != 0) :
    (down α).HasNoLoop :=
  hasNoLoop_down' _ ha

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (up Int).HasNoLoop
  body: hasNoLoop_up (by simp)

中文:
实例 :
  签名: (up 整数).HasNoLoop
  定义体: hasNoLoop_up (by simp)

Depends on / 依赖: hasNoLoop_up
-/
instance : (up Int).HasNoLoop := hasNoLoop_up (by simp)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (up Nat).HasNoLoop
  body: hasNoLoop_up (by simp)

中文:
实例 :
  签名: (up 自然数).HasNoLoop
  定义体: hasNoLoop_up (by simp)

Depends on / 依赖: hasNoLoop_up
-/
instance : (up Nat).HasNoLoop := hasNoLoop_up (by simp)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (down Int).HasNoLoop
  body: hasNoLoop_down (by simp)

中文:
实例 :
  签名: (down 整数).HasNoLoop
  定义体: hasNoLoop_down (by simp)

Depends on / 依赖: hasNoLoop_down
-/
instance : (down Int).HasNoLoop := hasNoLoop_down (by simp)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (down Nat).HasNoLoop
  body: hasNoLoop_down (by simp)

中文:
实例 :
  签名: (down 自然数).HasNoLoop
  定义体: hasNoLoop_down (by simp)

Depends on / 依赖: hasNoLoop_down
-/
instance : (down Nat).HasNoLoop := hasNoLoop_down (by simp)

end ComplexShape
