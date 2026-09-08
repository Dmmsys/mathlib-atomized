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

/-- An action of a group `G` on an extension of rings `B/A` is invariant if every fixed point of
`B` lies in the image of `A`. The converse statement that every point in the image of `A` is fixed
by `G` is `smul_algebraMap` (assuming `SMulCommClass A B G`). -/
/-
**Algebra.IsInvariant** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(A : Type u_1) →   (B : Type u_2) →     (G : Type u_3) →       [inst : Com
mSemiring A] →         [inst_1 : Semiring B] → [Algebra A B] → [inst : Group G] 
→ [MulSemiringAction G B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of a group `G` on an extension of rings `B/A` is invariant if every fi
xed point of
`B` lies in the image of `A`. The converse statement that every point in the ima
ge of `A` is fixed
by `G` is `smul_algebraMap` (assuming `SMulCommClass A B G`).
-/
@[mk_iff] class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

end Algebra

