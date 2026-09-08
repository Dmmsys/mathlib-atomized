/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs

/-!

# Local rings

Define the notion of a local ring for non-commutative semirings. In the commutative case,
this is shown to be equivalent to the familiar definition that there exists a unique
maximal ideal in `IsLocalRing.of_unique_max_ideal` and `IsLocalRing.maximal_ideal_unique`.

## Main definitions

* `IsLocalRing`: A predicate on semirings, stating that for any pair of elements that
  adds up to `1`, one of them is a unit.

-/

public section
/-- A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b = 1`.
Note that `IsLocalRing` is a predicate. -/
@[wikidata Q1142704]
/-
**IsLocalRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b
 = 1`.
Note that `IsLocalRing` is a predicate.
-/
class IsLocalRing (R : Type*) [Semiring R] : Prop extends Nontrivial R where
  of_is_unit_or_is_unit_of_add_one ::
  /-- in a local ring `R`, if `a + b = 1`, then either `a` is a unit or `b` is a unit. In another
  word, for every `a : R`, either `a` is a unit or `1 - a` is a unit. -/
  isUnit_or_isUnit_of_add_one {a b : R} (h : a + b = 1) : IsUnit a ∨ IsUnit b
