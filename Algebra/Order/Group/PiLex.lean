/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.PiLex

/-!
# Lexicographic product of algebraic order structures

This file proves that the lexicographic order on pi types is compatible with the pointwise algebraic
operations.
-/

public section

namespace Pi.Lex
variable {ι : Type*} {α : ι -> Type*} [LinearOrder ι]

@[to_additive]
/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: [forall i, CommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr_arg (· * z j) (hi.1 j hji), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

中文:
实例 isOrderedCancelMonoid
  签名: [对任意 i, 交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr_arg (· * z j) (hi.1 j hji), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.toIsStrictOrderedModule, Or.inr, congr_arg, hxy.elim, hxyz.elim, le_of_mul_le_mul_left, le_rfl, lt_of_mul_lt_mul_left, mul_left_cancel, mul_lt_mul_left, toIsStrictOrderedModule
-/
instance isOrderedCancelMonoid [forall i, CommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedCancelMonoid (α i)] :
    IsOrderedCancelMonoid (Lex (forall i, α i)) where
  mul_le_mul_left _ _ hxy z :=
    hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr_arg (· * z j) (hi.1 j hji), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

end Pi.Lex
