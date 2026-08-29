/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Star ordered ring structures on `ℚ` and `ℚ≥0`

This file shows that `ℚ` and `ℚ≥0` are `StarOrderedRing`s. In particular, this means that every
nonnegative rational number is a sum of squares.
-/

public section

open AddSubmonoid Set
open scoped NNRat

namespace NNRat

/--
lemma `addSubmonoid_closure_range_pow` / 引理 `addSubmonoid_closure_range_pow`

English:
lemma addSubmonoid_closure_range_pow
  given: {n : Nat} (hn₀ : n != 0)
  proof: by
  refine (eq_top_iff' _).2 fun x => ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : Rat>=0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc]; rw [pow_sub₀]; rw [pow_one]; rw [mul_right_comm]; rw [← mul_pow]; 

中文:
引理 addSubmonoid_closure_range_pow
  条件: {n : 自然数} (hn₀ : n != 0)
  证明: by
  refine (eq_top_iff' _).2 fun x => ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : Rat>=0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc]; rw [pow_sub₀]; rw [pow_one]; rw [mul_right_comm]; rw [← mul_pow]; 
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : Nat} (hn₀ : n != 0) :
    closure (range fun x : Rat>=0 => x ^ n) = ⊤ := by
  refine (eq_top_iff' _).2 fun x => ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : Rat>=0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc]; rw [pow_sub₀]; rw [pow_one]; rw [mul_right_comm]; rw [← mul_pow]; rw [mul_inv_cancel₀]; rw [one_pow]; rw [one_mul]; rw [← div_eq_mul_inv]; rw [num_div_den]
  all_goals simp [x.den_pos.ne', Nat.one_le_iff_ne_zero, *]

/--
lemma `addSubmonoid_closure_range_mul_self` / 引理 `addSubmonoid_closure_range_mul_self`

English:
lemma addSubmonoid_closure_range_mul_self
  statement: closure (range fun x : Rat>=0 => x * x) = ⊤
  proof: by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

中文:
引理 addSubmonoid_closure_range_mul_self
  结论: closure (range fun x : Rat>=0 => x * x) = ⊤
  证明: by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero
-/
@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : Rat>=0 => x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: : StarOrderedRing Rat>=0 where
  body: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

中文:
实例 instStarOrderedRing
  签名: : StarOrderedRing Rat>=0 where
  定义体: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

Depends on / 依赖: eq_comm, le_iff_exists_nonneg_add
-/
instance instStarOrderedRing : StarOrderedRing Rat>=0 where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end NNRat

namespace Rat

/--
lemma `addSubmonoid_closure_range_pow` / 引理 `addSubmonoid_closure_range_pow`

English:
lemma addSubmonoid_closure_range_pow
  given: {n : Nat} (hn₀ : n != 0) (hn : Even n)
  proof: by
  convert! (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x => x ^ n).symm
  · have (x : Rat) : exists y : Rat>=0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists

中文:
引理 addSubmonoid_closure_range_pow
  条件: {n : 自然数} (hn₀ : n != 0) (hn : Even n)
  证明: by
  convert! (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x => x ^ n).symm
  · have (x : Rat) : exists y : Rat>=0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : Nat} (hn₀ : n != 0) (hn : Even n) :
    closure (range fun x : Rat => x ^ n) = nonneg _ := by
  convert! (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x => x ^ n).symm
  · have (x : Rat) : exists y : Rat>=0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists]

@[simp]
/--
lemma `addSubmonoid_closure_range_mul_self` / 引理 `addSubmonoid_closure_range_mul_self`

English:
lemma addSubmonoid_closure_range_mul_self
  statement: closure (range fun x : Rat => x * x) = nonneg _
  proof: by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

中文:
引理 addSubmonoid_closure_range_mul_self
  结论: closure (range fun x : Rat => x * x) = nonneg _
  证明: by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

Depends on / 依赖: addSubmonoid_closure_range_pow, even_two, two_ne_zero
-/
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : Rat => x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: : StarOrderedRing Rat where
  body: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

中文:
实例 instStarOrderedRing
  签名: : StarOrderedRing Rat where
  定义体: by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

Depends on / 依赖: eq_comm, le_iff_exists_nonneg_add
-/
instance instStarOrderedRing : StarOrderedRing Rat where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Rat
