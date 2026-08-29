/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Defs

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

The main application is in algebraic number theory, where `G := Gal(L/K)` is the Galois group
of some finite Galois extension of number fields, and `A := 𝓞K` and `B := 𝓞L` are their rings of
integers.
-/

public section

namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/--
Definition of `IsInvariant` / `IsInvariant` 的定义

English:
class IsInvariant
  parameters: : Prop where
  axioms and operations (1):
    - isInvariant : forall b : B, (forall g : G, g • b = b) -> exists a : A, algebraMap A B a = b

中文:
类 IsInvariant
  参数: : 命题 where
  公理与运算 (1 个):
    - isInvariant : 对任意 b : B, (对任意 g : G, g • b = b) -> 存在 a : A, algebraMap A B a = b
-/
@[mk_iff] class IsInvariant : Prop where
  isInvariant : forall b : B, (forall g : G, g • b = b) -> exists a : A, algebraMap A B a = b

end Algebra
