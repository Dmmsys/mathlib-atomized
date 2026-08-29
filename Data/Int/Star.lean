/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Star ordered ring structure on `ℤ`

This file shows that `ℤ` is a `StarOrderedRing`.
-/

public section

open AddSubmonoid Set

namespace Int

/--
lemma `addSubmonoid_closure_range_pow` / 引理 `addSubmonoid_closure_range_pow`

English:
lemma addSubmonoid_closure_range_pow
  given: {n : Nat} (hn : Even n)
  proof: by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx => ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure <| mem_range_self _) _

@[simp]

中文:
引理 addSubmonoid_closure_range_pow
  条件: {n : 自然数} (hn : Even n)
  证明: by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx => ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure <| mem_range_self _) _

@[simp]
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : Nat} (hn : Even n) :
    closure (range fun x : Int => x ^ n) = nonneg _ := by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx => ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure <| mem_range_self _) _

@[simp]
/--
lemma `addSubmonoid_closure_range_mul_self` / 引理 `addSubmonoid_closure_range_mul_self`

English:
lemma addSubmonoid_closure_range_mul_self
  statement: closure (range fun x : Int => x * x) = nonneg _
  proof: by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two

中文:
引理 addSubmonoid_closure_range_mul_self
  结论: closure (range fun x : 整数 => x * x) = nonneg _
  证明: by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two

Depends on / 依赖: addSubmonoid_closure_range_pow, even_two
-/
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : Int => x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two

/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: : StarOrderedRing Int where
  body: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

中文:
实例 instStarOrderedRing
  签名: : StarOrdered环 整数 where
  定义体: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

Depends on / 依赖: eq_comm, le_iff_exists_nonneg_add
-/
instance instStarOrderedRing : StarOrderedRing Int where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Int
