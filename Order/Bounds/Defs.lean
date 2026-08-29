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
/--
Definition of `upperBounds` / `upperBounds` 的定义

English:
definition upperBounds
  signature: (s : Set α)
  body: { x | forall ⦃a⦄, a in s -> a <= x }

中文:
定义 upperBounds
  签名: (s : Set α)
  定义体: { x | forall ⦃a⦄, a in s -> a <= x }
-/
def upperBounds (s : Set α) : Set α :=
  { x | forall ⦃a⦄, a in s -> a <= x }

/-- A set is bounded above if there exists an upper bound. -/
@[to_dual /-- A set is bounded below if there exists a lower bound. -/]
/--
Definition of `BddAbove` / `BddAbove` 的定义

English:
definition BddAbove
  signature: (s : Set α)
  body: (upperBounds s).Nonempty

中文:
定义 BddAbove
  签名: (s : Set α)
  定义体: (upperBounds s).Nonempty

Depends on / 依赖: Nonempty, upperBounds
-/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
/--
Definition of `IsLeast` / `IsLeast` 的定义

English:
definition IsLeast
  signature: (s : Set α) (a : α)
  body: a in s ∧ a in lowerBounds s

中文:
定义 IsLeast
  签名: (s : Set α) (a : α)
  定义体: a in s ∧ a in lowerBounds s

Depends on / 依赖: lowerBounds
-/
def IsLeast (s : Set α) (a : α) : Prop :=
  a in s ∧ a in lowerBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/]
/--
Definition of `IsLUB` / `IsLUB` 的定义

English:
definition IsLUB
  signature: (s : Set α)
  body: IsLeast (upperBounds s)

中文:
定义 IsLUB
  签名: (s : Set α)
  定义体: IsLeast (upperBounds s)

Depends on / 依赖: IsLeast, upperBounds
-/
def IsLUB (s : Set α) : α -> Prop :=
  IsLeast (upperBounds s)

/-- A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `a ≤ b`. -/
@[to_dual /-- A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists
`b ∈ t` such that `b ≤ a`. -/]
/--
Definition of `IsCofinalFor` / `IsCofinalFor` 的定义

English:
definition IsCofinalFor
  signature: (s t : Set α)
  body: forall ⦃a⦄, a in s -> exists b in t, a <= b

中文:
定义 IsCofinalFor
  签名: (s t : Set α)
  定义体: forall ⦃a⦄, a in s -> exists b in t, a <= b
-/
def IsCofinalFor (s t : Set α) := forall ⦃a⦄, a in s -> exists b in t, a <= b

/-- A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`. -/
@[to_dual /-- A set is coinitial when for every `x : α` there exists `y ∈ s` with `y ≤ x`. -/]
/--
Definition of `IsCofinal` / `IsCofinal` 的定义

English:
definition IsCofinal
  signature: (s : Set α)
  body: forall x, exists y in s, x <= y

中文:
定义 IsCofinal
  签名: (s : Set α)
  定义体: forall x, exists y in s, x <= y
-/
def IsCofinal (s : Set α) : Prop :=
  forall x, exists y in s, x <= y
