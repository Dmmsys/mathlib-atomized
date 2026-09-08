/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual

/-!
# Definitions about upper/lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
* `IsCofinal s`: for every `a`, there exists a member of `s` greater or equal to it.
* `IsCofinalFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `a ≤ b`
* `IsCoinitial s`: for every `a`, there exists a member of `s` less than or equal to it.
* `IsCoinitialFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `b ≤ a`
-/

@[expose] public section

variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
@[to_dual /-- The set of lower bounds of a set. -/]
/-
**upperBounds** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：upperBounds (s : Set α) : Set α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of upper bounds of a set.
-/
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- A set is bounded above if there exists an upper bound. -/
@[to_dual /-- A set is bounded below if there exists a lower bound. -/]
/-
**BddAbove** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BddAbove (s : Set α)
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is bounded above if there exists an upper bound.
-/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
/-
**IsLeast** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLeast (s : Set α) (a : α) : Prop
参数：s : Set α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/]
/-
**IsLUB** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLUB (s : Set α) : α -> Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `a ≤ b`. -/
@[to_dual /-- A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists
`b ∈ t` such that `b ≤ a`. -/]
/-
**IsCofinalFor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCofinalFor (s t : Set α)
参数：s t : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsCofinalFor (s t : Set α) := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b

/-- A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`. -/
@[to_dual /-- A set is coinitial when for every `x : α` there exists `y ∈ s` with `y ≤ x`. -/]
/-
**IsCofinal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCofinal (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`.
-/
def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y
