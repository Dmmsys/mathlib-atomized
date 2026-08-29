/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import Mathlib.Order.Atoms

/-! # Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main definitions

- `IsSimpleRing`: a predicate expressing that a ring is simple.

-/

public section


/--
Definition of `IsSimpleRing` / `IsSimpleRing` 的定义

English:
class IsSimpleRing
  parameters: (R : Type*) [NonUnitalNonAssocRing R]
  axioms and operations (1):
    - simple : IsSimpleOrder (TwoSidedIdeal R)

中文:
类 是单环
  参数: (R : 类型) [非幺非结合环 R]
  公理与运算 (1 个):
    - simple : 是单序 (TwoSided理想 R)
-/
@[mk_iff] class IsSimpleRing (R : Type*) [NonUnitalNonAssocRing R] : Prop where
  simple : IsSimpleOrder (TwoSidedIdeal R)

attribute [instance] IsSimpleRing.simple
