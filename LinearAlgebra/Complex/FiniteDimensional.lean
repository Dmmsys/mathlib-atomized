/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Complex number as a finite-dimensional vector space over `ℝ`

This file contains the `FiniteDimensional ℝ ℂ` instance, as well as some results about the rank
(`finrank` and `Module.rank`).
-/

public section

open Module

namespace Complex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiniteDimensional Real Complex
  body: basisOneI.finiteDimensional_of_finite

中文:
实例 :
  签名: FiniteDimensional 实数 Complex
  定义体: basisOneI.finiteDimensional_of_finite

Depends on / 依赖: basisOneI, basisOneI.finiteDimensional_of_finite, finiteDimensional_of_finite
-/
instance : FiniteDimensional Real Complex := basisOneI.finiteDimensional_of_finite

/-- `ℂ` is a finite extension of `ℝ` of degree 2, i.e `[ℂ : ℝ] = 2` -/
@[simp, stacks 09G4]
/--
theorem `finrank_real_complex` / 定理 `finrank_real_complex`

English:
theorem finrank_real_complex
  statement: finrank Real Complex = 2
  proof: by
  rw [finrank_eq_card_basis basisOneI]; rw [Fintype.card_fin]

@[simp]

中文:
定理 finrank_real_complex
  结论: finrank 实数 Complex = 2
  证明: by
  rw [finrank_eq_card_basis basisOneI]; rw [Fintype.card_fin]

@[simp]

Depends on / 依赖: Fintype, Fintype.card_fin, basisOneI, card_fin, finrank_eq_card_basis
-/
theorem finrank_real_complex : finrank Real Complex = 2 := by
  rw [finrank_eq_card_basis basisOneI]; rw [Fintype.card_fin]

@[simp]
/--
theorem `rank_real_complex` / 定理 `rank_real_complex`

English:
theorem rank_real_complex
  statement: Module.rank Real Complex = 2
  proof: by simp [← finrank_eq_rank, finrank_real_complex]

中文:
定理 rank_real_complex
  结论: Module.rank 实数 Complex = 2
  证明: by simp [← finrank_eq_rank, finrank_real_complex]

Depends on / 依赖: finrank_eq_rank, finrank_real_complex
-/
theorem rank_real_complex : Module.rank Real Complex = 2 := by simp [← finrank_eq_rank, finrank_real_complex]

/--
theorem `rank_real_complex'.` / 定理 `rank_real_complex'.`

English:
theorem rank_real_complex'.{u}
  statement: Cardinal.lift.{u} (Module.rank Real Complex) = 2
  proof: by
  rw [← finrank_eq_rank]; rw [finrank_real_complex]; rw [Cardinal.lift_natCast]; rw [Nat.cast_ofNat]

中文:
定理 rank_real_complex'.{u}
  结论: Cardinal.lift.{u} (Module.rank 实数 Complex) = 2
  证明: by
  rw [← finrank_eq_rank]; rw [finrank_real_complex]; rw [Cardinal.lift_natCast]; rw [Nat.cast_ofNat]

Depends on / 依赖: Cardinal, Cardinal.lift_natCast, Nat.cast_ofNat, cast_ofNat, finrank_eq_rank, finrank_real_complex, lift_natCast
-/
theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank Real Complex) = 2 := by
  rw [← finrank_eq_rank]; rw [finrank_real_complex]; rw [Cardinal.lift_natCast]; rw [Nat.cast_ofNat]

/--
theorem `finrank_real_complex_fact` / 定理 `finrank_real_complex_fact`

English:
theorem finrank_real_complex_fact
  statement: Fact (finrank Real Complex = 2)
  proof: ⟨finrank_real_complex⟩

中文:
定理 finrank_real_complex_fact
  结论: Fact (finrank 实数 Complex = 2)
  证明: ⟨finrank_real_complex⟩

Depends on / 依赖: finrank_real_complex
-/
theorem finrank_real_complex_fact : Fact (finrank Real Complex = 2) :=
  ⟨finrank_real_complex⟩

end Complex

instance (priority := 500) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module Complex E] [FiniteDimensional Complex E] : FiniteDimensional Real E :=
  FiniteDimensional.trans Real Complex E

/--
theorem `rank_real_of_complex` / 定理 `rank_real_of_complex`

English:
theorem rank_real_of_complex
  given: (E : Type*) [AddCommGroup E] [Module Complex E]
  proof: Cardinal.lift_inj.{_, 0}.1 by
    rw [← lift_rank_mul_lift_rank Real Complex E]; rw [Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

中文:
定理 rank_real_of_complex
  条件: (E : 类型) [AddCommGroup E] [Module Complex E]
  证明: Cardinal.lift_inj.{_, 0}.1 by
    rw [← lift_rank_mul_lift_rank Real Complex E]; rw [Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

Depends on / 依赖: Cardinal, Cardinal.lift_id, Cardinal.lift_inj, Complex.rank_real_complex, lift_id, lift_inj, lift_rank_mul_lift_rank, rank_real_complex
-/
theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module Complex E] :
    Module.rank Real E = 2 * Module.rank Complex E :=
Cardinal.lift_inj.{_, 0}.1 by
    rw [← lift_rank_mul_lift_rank Real Complex E]; rw [Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

/--
theorem `finrank_real_of_complex` / 定理 `finrank_real_of_complex`

English:
theorem finrank_real_of_complex
  given: (E : Type*) [AddCommGroup E] [Module Complex E]
  proof: by
  rw [← Module.finrank_mul_finrank Real Complex E]; rw [Complex.finrank_real_complex]

中文:
定理 finrank_real_of_complex
  条件: (E : 类型) [AddCommGroup E] [Module Complex E]
  证明: by
  rw [← Module.finrank_mul_finrank Real Complex E]; rw [Complex.finrank_real_complex]

Depends on / 依赖: Complex.finrank_real_complex, Module, Module.finrank_mul_finrank, finrank_mul_finrank, finrank_real_complex
-/
theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module Complex E] :
    Module.finrank Real E = 2 * Module.finrank Complex E := by
  rw [← Module.finrank_mul_finrank Real Complex E]; rw [Complex.finrank_real_complex]

section Rational

open Cardinal Module

@[simp]
/--
lemma `Real.rank_rat_real` / 引理 `Real.rank_rat_real`

English:
lemma Real.rank_rat_real
  statement: Module.rank Rat Real = continuum
  proof: by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Real ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

中文:
引理 Real.rank_rat_real
  结论: Module.rank Rat 实数 = continuum
  证明: by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Real ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

Depends on / 依赖: Free.rank_eq_mk_of_infinite_lt, aleph0_lt_continuum, mk_real, rank_eq_mk_of_infinite_lt
-/
lemma Real.rank_rat_real : Module.rank Rat Real = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Real ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

/-- `C` has an uncountable basis over `ℚ`. -/
@[simp, stacks 09G0]
/--
lemma `Complex.rank_rat_complex` / 引理 `Complex.rank_rat_complex`

English:
lemma Complex.rank_rat_complex
  statement: Module.rank Rat Complex = continuum
  proof: by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Complex ?_).trans Cardinal.mk_complex
  simpa using aleph0_lt_continuum

中文:
引理 Complex.rank_rat_complex
  结论: Module.rank Rat Complex = continuum
  证明: by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Complex ?_).trans Cardinal.mk_complex
  simpa using aleph0_lt_continuum

Depends on / 依赖: Cardinal, Cardinal.mk_complex, Free.rank_eq_mk_of_infinite_lt, aleph0_lt_continuum, mk_complex, rank_eq_mk_of_infinite_lt
-/
lemma Complex.rank_rat_complex : Module.rank Rat Complex = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt Rat Complex ?_).trans Cardinal.mk_complex
  simpa using aleph0_lt_continuum

/--
theorem `Complex.nonempty_linearEquiv_real` / 定理 `Complex.nonempty_linearEquiv_real`

English:
theorem Complex.nonempty_linearEquiv_real
  statement: Nonempty (Complex ≃ₗ[Rat] Real)
  proof: Module.nonempty_linearEquiv_iff_rank_eq.mpr by simp

中文:
定理 Complex.nonempty_linearEquiv_real
  结论: Nonempty (Complex ≃ₗ[Rat] 实数)
  证明: Module.nonempty_linearEquiv_iff_rank_eq.mpr by simp

Depends on / 依赖: Module, Module.nonempty_linearEquiv_iff_rank_eq.mpr, nonempty_linearEquiv_iff_rank_eq
-/
theorem Complex.nonempty_linearEquiv_real : Nonempty (Complex ≃ₗ[Rat] Real) :=
Module.nonempty_linearEquiv_iff_rank_eq.mpr by simp

end Rational
