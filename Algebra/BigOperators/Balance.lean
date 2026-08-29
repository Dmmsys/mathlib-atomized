/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Expect

/-!
# Balancing a function

This file defines the balancing of a function `f`, defined as `f` minus its average.

This is the unique function `g` such that `f a - f b = g a - g b` for all `a` and `b`, and
`∑ a, g a = 0`. This is particularly useful in Fourier analysis as `f` and `g` then have the same
Fourier transform, except in the `0`-th frequency where the Fourier transform of `g` vanishes.
-/

@[expose] public section

open Finset Function
open scoped BigOperators

variable {ι H F G : Type*}

namespace Fintype

section AddCommGroup
variable [Fintype ι] [AddCommGroup G] [Module Rat>=0 G] [AddCommGroup H] [Module Rat>=0 H]

/--
Definition of `balance` / `balance` 的定义

English:
definition balance
  signature: (f : ι -> G)
  body: f - Function.const _ (𝔼 y, f y)

中文:
定义 balance
  签名: (f : ι -> G)
  定义体: f - Function.const _ (𝔼 y, f y)

Depends on / 依赖: Function, Function.const
-/
def balance (f : ι -> G) : ι -> G := f - Function.const _ (𝔼 y, f y)

/--
lemma `balance_apply` / 引理 `balance_apply`

English:
lemma balance_apply
  given: (f : ι -> G) (x : ι)
  statement: balance f x = f x - 𝔼 y, f y
  proof: rfl

中文:
引理 balance_apply
  条件: (f : ι -> G) (x : ι)
  结论: balance f x = f x - 𝔼 y, f y
  证明: rfl
-/
lemma balance_apply (f : ι -> G) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl

/--
lemma `balance_zero` / 引理 `balance_zero`

English:
lemma balance_zero
  statement: balance (0 : ι -> G) = 0
  proof: by simp [balance]

中文:
引理 balance_zero
  结论: balance (0 : ι -> G) = 0
  证明: by simp [balance]
-/
@[simp] lemma balance_zero : balance (0 : ι -> G) = 0 := by simp [balance]

/--
lemma `balance_add` / 引理 `balance_add`

English:
lemma balance_add
  given: (f g : ι -> G)
  statement: balance (f + g) = balance f + balance g
  proof: by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]

中文:
引理 balance_add
  条件: (f g : ι -> G)
  结论: balance (f + g) = balance f + balance g
  证明: by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]
-/
@[simp] lemma balance_add (f g : ι -> G) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]

/--
lemma `balance_sub` / 引理 `balance_sub`

English:
lemma balance_sub
  given: (f g : ι -> G)
  statement: balance (f - g) = balance f - balance g
  proof: by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]

中文:
引理 balance_sub
  条件: (f g : ι -> G)
  结论: balance (f - g) = balance f - balance g
  证明: by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]
-/
@[simp] lemma balance_sub (f g : ι -> G) : balance (f - g) = balance f - balance g := by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]

/--
lemma `balance_neg` / 引理 `balance_neg`

English:
lemma balance_neg
  given: (f : ι -> G)
  statement: balance (-f) = -balance f
  proof: by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]

中文:
引理 balance_neg
  条件: (f : ι -> G)
  结论: balance (-f) = -balance f
  证明: by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]
-/
@[simp] lemma balance_neg (f : ι -> G) : balance (-f) = -balance f := by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]

/--
lemma `sum_balance` / 引理 `sum_balance`

English:
lemma sum_balance
  given: (f : ι -> G)
  statement: ∑ x, balance f x = 0
  proof: by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]

中文:
引理 sum_balance
  条件: (f : ι -> G)
  结论: ∑ x, balance f x = 0
  证明: by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]
-/
@[simp] lemma sum_balance (f : ι -> G) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]

/--
lemma `expect_balance` / 引理 `expect_balance`

English:
lemma expect_balance
  given: (f : ι -> G)
  statement: 𝔼 x, balance f x = 0
  proof: by simp [expect]

中文:
引理 expect_balance
  条件: (f : ι -> G)
  结论: 𝔼 x, balance f x = 0
  证明: by simp [expect]
-/
@[simp] lemma expect_balance (f : ι -> G) : 𝔼 x, balance f x = 0 := by simp [expect]

/--
lemma `balance_idem` / 引理 `balance_idem`

English:
lemma balance_idem
  given: (f : ι -> G)
  statement: balance (balance f) = balance f
  proof: by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

中文:
引理 balance_idem
  条件: (f : ι -> G)
  结论: balance (balance f) = balance f
  证明: by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]
-/
@[simp] lemma balance_idem (f : ι -> G) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

/--
lemma `map_balance` / 引理 `map_balance`

English:
lemma map_balance
  given: [FunLike F G H] [LinearMapClass F Rat>=0 G H] (g : F) (f : ι -> G) (a : ι)
  proof: by simp [balance, map_expect]

中文:
引理 map_balance
  条件: [函数状 F G H] [线性映射类 F 有理数>=0 G H] (g : F) (f : ι -> G) (a : ι)
  证明: by simp [balance, map_expect]
-/
@[simp] lemma map_balance [FunLike F G H] [LinearMapClass F Rat>=0 G H] (g : F) (f : ι -> G) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

end AddCommGroup
end Fintype
