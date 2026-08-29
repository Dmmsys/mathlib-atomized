/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.NNReal.Star

/-! # `ℝ` and `ℝ≥0` are \*-ordered rings. -/

public section

open scoped NNReal

/--
Instance `Real.instStarOrderedRing` / 实例 `Real.instStarOrderedRing`

English:
instance Real.instStarOrderedRing
  signature: : StarOrderedRing Real
  body: StarOrderedRing.of_nonneg_iff' add_le_add_right fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s

中文:
实例 Real.instStarOrderedRing
  签名: : StarOrderedRing 实数
  定义体: StarOrderedRing.of_nonneg_iff' add_le_add_right fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s

Depends on / 依赖: StarOrderedRing, StarOrderedRing.of_nonneg_iff, add_le_add_right, mul_self_nonneg, mul_self_sqrt, of_nonneg_iff
-/
instance Real.instStarOrderedRing : StarOrderedRing Real :=
  StarOrderedRing.of_nonneg_iff' add_le_add_right fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s

/--
Instance `NNReal.instStarOrderedRing` / 实例 `NNReal.instStarOrderedRing`

English:
instance NNReal.instStarOrderedRing
  signature: : StarOrderedRing Real>=0
  body: by
  refine .of_le_iff fun x y => ⟨fun h => ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

中文:
实例 NNReal.instStarOrderedRing
  签名: : StarOrderedRing 实数>=0
  定义体: by
  refine .of_le_iff fun x y => ⟨fun h => ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

Depends on / 依赖: exists_add_of_le, le_self_add, mul_self_sqrt, of_le_iff, star_trivial
-/
instance NNReal.instStarOrderedRing : StarOrderedRing Real>=0 := by
  refine .of_le_iff fun x y => ⟨fun h => ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

-- for lack of a better place with the necessary imports, we place this here
-- this exists only to satisfy the trivial instances of this class
instance {R : Type*} [AddGroup R] [Lattice R] [AddLeftMono R] [Star R] :
    SelfAdjointDecompose R where
  exists_nonneg_sub_nonneg {a} _ :=
    ⟨a⁺, a⁻, posPart_nonneg a, negPart_nonneg a, by simp⟩
