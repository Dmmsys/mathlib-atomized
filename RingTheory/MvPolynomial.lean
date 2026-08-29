/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Multivariate polynomials over fields

This file contains basic facts about multivariate polynomials over fields, for example that the
dimension of the space of multivariate polynomials over a field is equal to the cardinality of
finitely supported functions from the indexing set to `ℕ`.
-/

public section


noncomputable section

open Set LinearMap Submodule

universe u v

namespace MvPolynomial

variable (σ : Type u) (K : Type v)

/--
theorem `quotient_mk_comp_C_injective` / 定理 `quotient_mk_comp_C_injective`

English:
theorem quotient_mk_comp_C_injective
  given: [Field K] (I : Ideal (MvPolynomial σ K)) (hI : I != ⊤)
  proof: by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  refine _root_.by_contradiction fun hx0 => absurd (I.eq_top_iff_one.2 ?_) hI
  have := I.mul_mem_left (MvPolynomial.C x⁻¹) hx
  rwa [← MvPolynomial.C.map_mul, inv_mul_canc

中文:
定理 quotient_mk_comp_C_injective
  条件: [Field K] (I : Ideal (MvPolynomial σ K)) (hI : I != ⊤)
  证明: by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  refine _root_.by_contradiction fun hx0 => absurd (I.eq_top_iff_one.2 ?_) hI
  have := I.mul_mem_left (MvPolynomial.C x⁻¹) hx
  rwa [← MvPolynomial.C.map_mul, inv_mul_canc

Depends on / 依赖: I.eq_top_iff_one, I.mul_mem_left, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial, MvPolynomial.C, MvPolynomial.C.map_mul, MvPolynomial.C_1, Quotient, RingHom, RingHom.comp_apply, _root_, _root_.by_contradiction, absurd, by_contradiction, comp_apply, eq_top_iff_one, eq_zero_iff_mem, injective_iff_map_eq_zero, map_mul, mul_mem_left
-/
theorem quotient_mk_comp_C_injective [Field K] (I : Ideal (MvPolynomial σ K)) (hI : I != ⊤) :
    Function.Injective ((Ideal.Quotient.mk I).comp MvPolynomial.C) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  refine _root_.by_contradiction fun hx0 => absurd (I.eq_top_iff_one.2 ?_) hI
  have := I.mul_mem_left (MvPolynomial.C x⁻¹) hx
  rwa [← MvPolynomial.C.map_mul, inv_mul_cancel₀ hx0, MvPolynomial.C_1] at this

variable {σ K} [CommRing K] [Nontrivial K]
open Cardinal

/--
theorem `rank_eq_lift` / 定理 `rank_eq_lift`

English:
theorem rank_eq_lift
  statement: Module.rank K (MvPolynomial σ K) = lift.{v} #(σ ->₀ Nat)
  proof: by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]; rw [lift_lift]; rw [lift_umax.{u]; rw [v}]

中文:
定理 rank_eq_lift
  结论: Module.rank K (MvPolynomial σ K) = lift.{v} #(σ ->₀ 自然数)
  证明: by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]; rw [lift_lift]; rw [lift_umax.{u]; rw [v}]

Depends on / 依赖: Cardinal, Cardinal.lift_inj, basisMonomials, lift_inj, lift_lift, lift_umax, mk_eq_rank
-/
theorem rank_eq_lift : Module.rank K (MvPolynomial σ K) = lift.{v} #(σ ->₀ Nat) := by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]; rw [lift_lift]; rw [lift_umax.{u]; rw [v}]

/--
theorem `rank_eq` / 定理 `rank_eq`

English:
theorem rank_eq
  given: {σ : Type v}
  statement: Module.rank K (MvPolynomial σ K) = #(σ ->₀ Nat)
  proof: by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]

中文:
定理 rank_eq
  条件: {σ : 类型v}
  结论: Module.rank K (MvPolynomial σ K) = #(σ ->₀ 自然数)
  证明: by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]

Depends on / 依赖: Cardinal, Cardinal.lift_inj, basisMonomials, lift_inj, mk_eq_rank
-/
theorem rank_eq {σ : Type v} : Module.rank K (MvPolynomial σ K) = #(σ ->₀ Nat) := by
  rw [← Cardinal.lift_inj]; rw [← (basisMonomials σ K).mk_eq_rank]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module K (MvPolynomial σ K)
  body: inferInstanceAs Module K (AddMonoidAlgebra K (σ ->₀ Nat))

中文:
实例 :
  签名: Module K (MvPolynomial σ K)
  定义体: inferInstanceAs Module K (AddMonoidAlgebra K (σ ->₀ Nat))

Depends on / 依赖: AddMonoidAlgebra, Module
-/
instance : Module K (MvPolynomial σ K) :=
inferInstanceAs Module K (AddMonoidAlgebra K (σ ->₀ Nat))

/--
theorem `finrank_eq_zero` / 定理 `finrank_eq_zero`

English:
theorem finrank_eq_zero
  given: [Nonempty σ]
  statement: Module.finrank K (MvPolynomial σ K) = 0
  proof: (basisMonomials σ K).linearIndependent.finrank_eq_zero_of_infinite

omit [Nontrivial K] in

中文:
定理 finrank_eq_zero
  条件: [Nonempty σ]
  结论: Module.finrank K (MvPolynomial σ K) = 0
  证明: (basisMonomials σ K).linearIndependent.finrank_eq_zero_of_infinite

omit [Nontrivial K] in

Depends on / 依赖: basisMonomials, finrank_eq_zero_of_infinite, linearIndependent, linearIndependent.finrank_eq_zero_of_infinite
-/
theorem finrank_eq_zero [Nonempty σ] : Module.finrank K (MvPolynomial σ K) = 0 :=
  (basisMonomials σ K).linearIndependent.finrank_eq_zero_of_infinite

omit [Nontrivial K] in
/--
theorem `finrank_eq_one` / 定理 `finrank_eq_one`

English:
theorem finrank_eq_one
  given: [IsEmpty σ]
  statement: Module.finrank K (MvPolynomial σ K) = 1
  proof: Module.rank_eq_one_iff_finrank_eq_one.mp by
    cases subsingleton_or_nontrivial K <;> simp [rank_eq_lift]

中文:
定理 finrank_eq_one
  条件: [IsEmpty σ]
  结论: Module.finrank K (MvPolynomial σ K) = 1
  证明: Module.rank_eq_one_iff_finrank_eq_one.mp by
    cases subsingleton_or_nontrivial K <;> simp [rank_eq_lift]

Depends on / 依赖: Module, Module.rank_eq_one_iff_finrank_eq_one.mp, rank_eq_lift, rank_eq_one_iff_finrank_eq_one, subsingleton_or_nontrivial
-/
theorem finrank_eq_one [IsEmpty σ] : Module.finrank K (MvPolynomial σ K) = 1 :=
Module.rank_eq_one_iff_finrank_eq_one.mp by
    cases subsingleton_or_nontrivial K <;> simp [rank_eq_lift]

end MvPolynomial
