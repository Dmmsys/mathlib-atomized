/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-! # Positive linear maps in C⋆-algebras

This file develops the API for positive linear maps over C⋆-algebras.

## Main results

* `PositiveLinearMap.exists_norm_apply_le`: positive maps are bounded (and therefore continuous)
  on non-unital C⋆-algebras.

## References

* The proof that positive maps are bounded was taken from
  https://math.stackexchange.com/questions/426487/why-is-every-positive-linear-map-between-c-algebras-bounded
-/

public section

open scoped NNReal

variable {A₁ A₂ B₁ B₂ : Type*}

section CStarAlgebra

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra B₁] [CStarAlgebra B₂] [PartialOrder B₁] [PartialOrder B₂]
  [StarOrderedRing B₁]

/--
lemma `apply_le_of_isSelfAdjoint` / 引理 `apply_le_of_isSelfAdjoint`

English:
lemma apply_le_of_isSelfAdjoint
  given: (f : B₁ ->ₚ[Complex] B₂) (x : B₁) (hx : IsSelfAdjoint x)
  proof: by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx

中文:
引理 apply_le_of_isSelfAdjoint
  条件: (f : B₁ ->ₚ[复形] B₂) (x : B₁) (hx : IsSelfAdjoint x)
  证明: by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.le_algebraMap_norm_self, le_algebraMap_norm_self
-/
lemma apply_le_of_isSelfAdjoint (f : B₁ ->ₚ[Complex] B₂) (x : B₁) (hx : IsSelfAdjoint x) :
    f x <= f (algebraMap Real B₁ ‖x‖) := by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx

/--
lemma `norm_apply_le_of_nonneg` / 引理 `norm_apply_le_of_nonneg`

English:
lemma norm_apply_le_of_nonneg
  given: [StarOrderedRing B₂] (f : B₁ ->ₚ[Complex] B₂) (x : B₁) (hx : 0 <= x)
  proof: by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm]; rw [← h]; rw [← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  rw [← Complex.coe_smul]; rw [← LinearMapClass.map_smul f]
  gcongr
  rw [← Algebra.algebraMap_eq_smul_one]
exact IsSelfAdjoint.le_algebraMap_norm_self .of_nonneg hx

中文:
引理 norm_apply_le_of_nonneg
  条件: [StarOrdered环 B₂] (f : B₁ ->ₚ[复形] B₂) (x : B₁) (hx : 0 <= x)
  证明: by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm]; rw [← h]; rw [← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  rw [← Complex.coe_smul]; rw [← LinearMapClass.map_smul f]
  gcongr
  rw [← Algebra.algebraMap_eq_smul_one]
exact IsSelfAdjoint.le_algebraMap_norm_self .of_nonneg hx

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, CStarAlgebra, CStarAlgebra.norm_le_norm_of_nonneg_of_le, Complex.coe_smul, IsSelfAdjoint, IsSelfAdjoint.le_algebraMap_norm_self, LinearMapClass, LinearMapClass.map_smul, algebraMap_eq_smul_one, coe_smul, f.map_nonneg, le_algebraMap_norm_self, map_nonneg, map_smul, mul_comm, norm_le_norm_of_nonneg_of_le, norm_smul, of_nonneg
-/
lemma norm_apply_le_of_nonneg [StarOrderedRing B₂] (f : B₁ ->ₚ[Complex] B₂) (x : B₁) (hx : 0 <= x) :
    ‖f x‖ <= ‖f 1‖ * ‖x‖ := by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm]; rw [← h]; rw [← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  rw [← Complex.coe_smul]; rw [← LinearMapClass.map_smul f]
  gcongr
  rw [← Algebra.algebraMap_eq_smul_one]
exact IsSelfAdjoint.le_algebraMap_norm_self .of_nonneg hx

open Complex Filter in
/--
lemma `exists_norm_apply_le` / 引理 `exists_norm_apply_le`

English:
lemma exists_norm_apply_le
  given: (f : A₁ ->ₚ[Complex] A₂)
  statement: exists C : Real>=0, forall a, ‖f a‖ <= C * ‖a‖
  proof: by
  /- It suffices to only consider for positive `a`, by decomposing `a` into positive and negative
     parts of the real and imaginary parts. -/
  suffices h_nonneg : exists C : Real>=0, forall a, 0 <= a -> ‖f a‖ <= C * ‖a‖ by
    obtain ⟨C, hmain⟩ := h_nonneg
    refine ⟨4 * C, fun x => ?_⟩
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul]
.trans apply norm_sum_le _ _
    simp only [norm_smul, norm_pow, norm_I, one_pow, one_mul]
.trans by simp [mul_assoc] apply Finset.sum_le_sum (g := fun _ => C * ‖x‖) (fun i _ => ?_)
.trans apply hmain _ (hy_nonneg i)
    gcongr
    exact hy_norm i
  -- Let's proceed by contradiction
  by_contra! hcontra
  -- Given `n : ℕ`, we can always choose a positive element of norm one with `2 ^ (2 * n) < ‖f x‖`
  have (n : Nat) : exists x, 0 <= x ∧ ‖x‖ = 1 ∧ 2 ^ (2 * n) < ‖f x‖ := by
    obtain ⟨hx₁, hx₂⟩ := Classical.choose_spec (hcontra (2 ^ (2 * n)))
    set x := Classical.choose (hcontra (2 ^ (2 * n)))
    have hx := (eq_zero_or_norm_pos x).resolve_left (fun hx => by simp_all)
    refine ⟨‖x‖⁻¹ • x, smul_nonneg (by positivity) hx₁, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hx.ne']
    · simpa [norm_smul] using (lt_inv_mul_iff₀' hx).mpr hx₂
  -- Let `x n` be a sequence of nonnegative elements such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4 ^ n`.
  choose x hx using this
  simp only [forall_and] at hx
  obtain ⟨hx_nonneg, hx_norm, hx⟩ := hx
  -- `∑ n, 2 ^ (-n) • x n` converges
  have x_summable : Summable fun n : Nat => (2 : Real) ^ (-(n : Int)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : Real)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- There is some `n` such that `‖f (∑' m, 2 ^ (-m) • x m)‖ < 2 ^ n`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f (∑' (n : Nat), (2 : Real) ^ (-(n : Int)) • x n)‖ < (2 : Real) ^ n :=
.eventually_gt_atTop _ tendsto_pow_atTop_atTop_of_one_lt one_lt_two
.exists
  -- But `2 ^ n ≤ ‖f (2 ^ (-n) • x n)‖ ≤ ‖f (∑' m, 2 ^ (-m) • x m)‖`, which is a contradiction.
  apply hn.not_ge
  trans ‖f ((2 : Real) ^ (-n : Int) • x n)‖
.le · have := hx n
    rw [pow_mul']; rw [sq] at this
    simpa [norm_smul] using (le_inv_mul_iff₀ (show 0 < (2 : Real) ^ n by positivity)).mpr this
  · have (m : Nat) : 0 <= ((2 : Real) ^ (-(m : Int)) • x m) := smul_nonneg (by positivity) (hx_nonneg m)
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (this n)) ?_
    gcongr
    exact x_summable.le_tsum n fun m _ => this m

中文:
引理 存在_norm_apply_le
  条件: (f : A₁ ->ₚ[复形] A₂)
  结论: 存在 C : 实数>=0, 对任意 a, ‖f a‖ <= C * ‖a‖
  证明: by
  /- It suffices to only consider for positive `a`, by decomposing `a` into positive and negative
     parts of the real and imaginary parts. -/
  suffices h_nonneg : exists C : Real>=0, forall a, 0 <= a -> ‖f a‖ <= C * ‖a‖ by
    obtain ⟨C, hmain⟩ := h_nonneg
    refine ⟨4 * C, fun x => ?_⟩
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul]
.trans apply norm_sum_le _ _
    simp only [norm_smul, norm_pow, norm_I, one_pow, one_mul]
.trans by simp [mul_assoc] apply Finset.sum_le_sum (g := fun _ => C * ‖x‖) (fun i _ => ?_)
.trans apply hmain _ (hy_nonneg i)
    gcongr
    exact hy_norm i
  -- Let's proceed by contradiction
  by_contra! hcontra
  -- Given `n : ℕ`, we can always choose a positive element of norm one with `2 ^ (2 * n) < ‖f x‖`
  have (n : Nat) : exists x, 0 <= x ∧ ‖x‖ = 1 ∧ 2 ^ (2 * n) < ‖f x‖ := by
    obtain ⟨hx₁, hx₂⟩ := Classical.choose_spec (hcontra (2 ^ (2 * n)))
    set x := Classical.choose (hcontra (2 ^ (2 * n)))
    have hx := (eq_zero_or_norm_pos x).resolve_left (fun hx => by simp_all)
    refine ⟨‖x‖⁻¹ • x, smul_nonneg (by positivity) hx₁, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hx.ne']
    · simpa [norm_smul] using (lt_inv_mul_iff₀' hx).mpr hx₂
  -- Let `x n` be a sequence of nonnegative elements such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4 ^ n`.
  choose x hx using this
  simp only [forall_and] at hx
  obtain ⟨hx_nonneg, hx_norm, hx⟩ := hx
  -- `∑ n, 2 ^ (-n) • x n` converges
  have x_summable : Summable fun n : Nat => (2 : Real) ^ (-(n : Int)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : Real)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- There is some `n` such that `‖f (∑' m, 2 ^ (-m) • x m)‖ < 2 ^ n`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f (∑' (n : Nat), (2 : Real) ^ (-(n : Int)) • x n)‖ < (2 : Real) ^ n :=
.eventually_gt_atTop _ tendsto_pow_atTop_atTop_of_one_lt one_lt_two
.exists
  -- But `2 ^ n ≤ ‖f (2 ^ (-n) • x n)‖ ≤ ‖f (∑' m, 2 ^ (-m) • x m)‖`, which is a contradiction.
  apply hn.not_ge
  trans ‖f ((2 : Real) ^ (-n : Int) • x n)‖
.le · have := hx n
    rw [pow_mul']; rw [sq] at this
    simpa [norm_smul] using (le_inv_mul_iff₀ (show 0 < (2 : Real) ^ n by positivity)).mpr this
  · have (m : Nat) : 0 <= ((2 : Real) ^ (-(m : Int)) • x m) := smul_nonneg (by positivity) (hx_nonneg m)
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (this n)) ?_
    gcongr
    exact x_summable.le_tsum n fun m _ => this m
-/
lemma exists_norm_apply_le (f : A₁ ->ₚ[Complex] A₂) : exists C : Real>=0, forall a, ‖f a‖ <= C * ‖a‖ := by
  /- It suffices to only consider for positive `a`, by decomposing `a` into positive and negative
     parts of the real and imaginary parts. -/
  suffices h_nonneg : exists C : Real>=0, forall a, 0 <= a -> ‖f a‖ <= C * ‖a‖ by
    obtain ⟨C, hmain⟩ := h_nonneg
    refine ⟨4 * C, fun x => ?_⟩
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul]
.trans apply norm_sum_le _ _
    simp only [norm_smul, norm_pow, norm_I, one_pow, one_mul]
.trans by simp [mul_assoc] apply Finset.sum_le_sum (g := fun _ => C * ‖x‖) (fun i _ => ?_)
.trans apply hmain _ (hy_nonneg i)
    gcongr
    exact hy_norm i
  -- Let's proceed by contradiction
  by_contra! hcontra
  -- Given `n : ℕ`, we can always choose a positive element of norm one with `2 ^ (2 * n) < ‖f x‖`
  have (n : Nat) : exists x, 0 <= x ∧ ‖x‖ = 1 ∧ 2 ^ (2 * n) < ‖f x‖ := by
    obtain ⟨hx₁, hx₂⟩ := Classical.choose_spec (hcontra (2 ^ (2 * n)))
    set x := Classical.choose (hcontra (2 ^ (2 * n)))
    have hx := (eq_zero_or_norm_pos x).resolve_left (fun hx => by simp_all)
    refine ⟨‖x‖⁻¹ • x, smul_nonneg (by positivity) hx₁, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hx.ne']
    · simpa [norm_smul] using (lt_inv_mul_iff₀' hx).mpr hx₂
  -- Let `x n` be a sequence of nonnegative elements such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4 ^ n`.
  choose x hx using this
  simp only [forall_and] at hx
  obtain ⟨hx_nonneg, hx_norm, hx⟩ := hx
  -- `∑ n, 2 ^ (-n) • x n` converges
  have x_summable : Summable fun n : Nat => (2 : Real) ^ (-(n : Int)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : Real)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- There is some `n` such that `‖f (∑' m, 2 ^ (-m) • x m)‖ < 2 ^ n`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f (∑' (n : Nat), (2 : Real) ^ (-(n : Int)) • x n)‖ < (2 : Real) ^ n :=
.eventually_gt_atTop _ tendsto_pow_atTop_atTop_of_one_lt one_lt_two
.exists
  -- But `2 ^ n ≤ ‖f (2 ^ (-n) • x n)‖ ≤ ‖f (∑' m, 2 ^ (-m) • x m)‖`, which is a contradiction.
  apply hn.not_ge
  trans ‖f ((2 : Real) ^ (-n : Int) • x n)‖
.le · have := hx n
    rw [pow_mul']; rw [sq] at this
    simpa [norm_smul] using (le_inv_mul_iff₀ (show 0 < (2 : Real) ^ n by positivity)).mpr this
  · have (m : Nat) : 0 <= ((2 : Real) ^ (-(m : Int)) • x m) := smul_nonneg (by positivity) (hx_nonneg m)
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (this n)) ?_
    gcongr
    exact x_summable.le_tsum n fun m _ => this m

instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F Complex A₁ A₂] [OrderHomClass F A₁ A₂] :
    ContinuousLinearMapClass F Complex A₁ A₂ where
  map_continuous f := by
    have hbound : exists C : Real, forall a, ‖f a‖ <= C * ‖a‖ := by
      obtain ⟨C, h⟩ := exists_norm_apply_le (.ofClass f)
      exact ⟨C, h⟩
    exact (LinearMap.mkContinuousOfExistsBound (f : A₁ ->ₗ[Complex] A₂) hbound).continuous

end PositiveLinearMap

end CStarAlgebra
