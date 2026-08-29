/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs

/-!
# The naturals form a linear ordered monoid

This file contains the linear ordered monoid instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat


/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid Nat where
  body: @Nat.add_le_add_right

中文:
实例 instIsOrderedAddMonoid
  签名: : IsOrderedAddMonoid 自然数 where
  定义体: @Nat.add_le_add_right

Depends on / 依赖: Nat.add_le_add_right, add_le_add_right, nsmul_le_nsmul_left
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := @Nat.add_le_add_right

/--
Instance `instIsOrderedCancelAddMonoid` / 实例 `instIsOrderedCancelAddMonoid`

English:
instance instIsOrderedCancelAddMonoid
  signature: : IsOrderedCancelAddMonoid Nat where
  body: @Nat.add_le_add_right
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left

中文:
实例 instIsOrderedCancelAddMonoid
  签名: : IsOrderedCancelAddMonoid 自然数 where
  定义体: @Nat.add_le_add_right
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left

Depends on / 依赖: Nat.add_le_add_right, add_le_add_right, hn.ne, nsmul_lt_nsmul_right
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Nat where
  add_le_add_left := @Nat.add_le_add_right
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left

/--
Instance `instCanonicallyOrderedAdd` / 实例 `instCanonicallyOrderedAdd`

English:
instance instCanonicallyOrderedAdd
  signature: : CanonicallyOrderedAdd Nat where
  body: Nat.le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le

中文:
实例 instCanonicallyOrderedAdd
  签名: : CanonicallyOrderedAdd 自然数 where
  定义体: Nat.le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le

Depends on / 依赖: Nat.le_add_left, le_add_left, nsmul_lt_nsmul_left
-/
instance instCanonicallyOrderedAdd : CanonicallyOrderedAdd Nat where
  le_add_self := Nat.le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le

/--
Instance `instOrderedSub` / 实例 `instOrderedSub`

English:
instance instOrderedSub
  signature: : OrderedSub Nat
  body: by
  refine ⟨fun m n k => ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

中文:
实例 instOrderedSub
  签名: : OrderedSub 自然数
  定义体: by
  refine ⟨fun m n k => ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

Depends on / 依赖: add_succ, generalizing, pred_le_iff, sub_succ, succ_add, zsmul_lt_zsmul_right
-/
instance instOrderedSub : OrderedSub Nat := by
  refine ⟨fun m n k => ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

/-! ### Miscellaneous lemmas -/

variable {α : Type*} {n : Nat} {f : α -> Nat}

/--
lemma `pow_left_strictMono` / 引理 `pow_left_strictMono`

English:
lemma pow_left_strictMono
  given: (hn : n != 0)
  statement: StrictMono (· ^ n : Nat -> Nat)
  proof: fun _ _ h => Nat.pow_lt_pow_left h hn

中文:
引理 pow_left_strictMono
  条件: (hn : n != 0)
  结论: StrictMono (· ^ n : 自然数 -> 自然数)
  证明: fun _ _ h => Nat.pow_lt_pow_left h hn

Depends on / 依赖: zsmul_lt_zsmul_left
-/
protected lemma pow_left_strictMono (hn : n != 0) : StrictMono (· ^ n : Nat -> Nat) :=
  fun _ _ h => Nat.pow_lt_pow_left h hn

/--
lemma `_root_.StrictMono.nat_pow` / 引理 `_root_.StrictMono.nat_pow`

English:
lemma _root_.StrictMono.nat_pow
  given: [Preorder α] (hn : n != 0) (hf : StrictMono f)
  proof: (Nat.pow_left_strictMono hn).comp hf

中文:
引理 _root_.StrictMono.nat_pow
  条件: [Preorder α] (hn : n != 0) (hf : StrictMono f)
  证明: (Nat.pow_left_strictMono hn).comp hf

Depends on / 依赖: Nat.pow_left_strictMono, pow_left_strictMono
-/
lemma _root_.StrictMono.nat_pow [Preorder α] (hn : n != 0) (hf : StrictMono f) :
    StrictMono (f · ^ n) := (Nat.pow_left_strictMono hn).comp hf

end Nat
