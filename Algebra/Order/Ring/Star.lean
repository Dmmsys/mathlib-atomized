/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Commutative star-ordered rings are ordered rings

A noncommutative star-ordered ring is generally not an ordered ring. Indeed, in a star-ordered
ring, nonnegative elements are self-adjoint, but the product of self-adjoint elements is
self-adjoint if and only if they commute. Therefore, a necessary condition for a star-ordered ring
to be an ordered ring is that all nonnegative elements commute.  Consequently, if a star-ordered
ring is spanned by it nonnegative elements (as is the case for C⋆-algebras) and it is also an
ordered ring, then it is commutative.

In this file we prove the converse: a *commutative* star-ordered ring is an ordered ring.
-/

public section

namespace StarOrderedRing

/-! This example shows that nonnegative elements in an ordered semiring which is also star-ordered
must commute. We provide this only as an example as opposed to a lemma because we never expect the
type class assumptions to be satisfied without a `CommSemiring` instance already in scope; not that
it is impossible, only that it shouldn't occur in practice. -/
/-
**StarOrderedRing.** 是 Mathlib 中的一个示例，位于命名空间 `StarOrderedRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This example shows that nonnegative elements in an ordered semiring which is als
o star-ordered
must commute. We provide this only as an example as opposed to a lemma because w
e never expect the
type class assumptions to be satisfied without a `CommSemiring` instance already
 in scope; not that
it is impossible, only that it shouldn't occur in practice.
-/
example {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [StarRing R] [StarOrderedRing R] {x y : R} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : x * y = y * x := by
  rw [← IsSelfAdjoint.of_nonneg (mul_nonneg hy hx), star_mul, IsSelfAdjoint.of_nonneg hx,
    IsSelfAdjoint.of_nonneg hy]

/-- A commutative star-ordered semiring is an ordered semiring. -/
/-
**StarOrderedRing.toIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `StarOrderedRing`。
形式化陈述：toIsOrderedRing (R : Type*) [CommSemiring R] [PartialOrder R] [StarRing R]
 [StarOrderedRing R] : IsOrderedRing R where mul_le_mul_of_nonneg_left _a ha _b 
_c hbc
参数：R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …

--- 原说明 ---
A commutative star-ordered semiring is an ordered semiring.
-/
instance toIsOrderedRing (R : Type*) [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : IsOrderedRing R where
  mul_le_mul_of_nonneg_left _a ha _b _c hbc := smul_le_smul_of_nonneg_left hbc ha
  mul_le_mul_of_nonneg_right _a ha _b _c hbc := smul_le_smul_of_nonneg_right hbc ha

end StarOrderedRing

