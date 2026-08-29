/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.FieldSimp

/-!
# Exponential map on algebras

This file defines the exponential map `IsNilpotent.exp` on `ℚ`-algebras. The definition of
`IsNilpotent.exp a` applies to any element `a` in an algebra over `ℚ`, though it yields meaningful
(non-junk) values only when `a` is nilpotent.

The main result is `IsNilpotent.exp_add_of_commute`, which establishes the expected connection
between the additive and multiplicative structures of `A` for commuting nilpotent elements.

Additionally, `IsNilpotent.isUnit_exp` shows that if `a` is nilpotent in `A`, then
`IsNilpotent.exp a` is a unit in `A`.

Note: Although the definition works with `ℚ`-algebras, the results can be applied to any algebra
over a characteristic zero field.

## Main definitions

  * `IsNilpotent.exp`

## Tags

algebra, exponential map, nilpotent
-/

@[expose] public section

namespace IsNilpotent

variable {A : Type*} [Ring A] [Module Rat A]

open Finset
open scoped Nat

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: (a : A)
  body: ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i)

中文:
定义 exp
  签名: (a : A)
  定义体: ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i)

Depends on / 依赖: factorial, i.factorial, nilpotencyClass
-/
noncomputable def exp (a : A) : A :=
  ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i)

/--
theorem `exp_eq_sum` / 定理 `exp_eq_sum`

English:
theorem exp_eq_sum
  given: {a : A} {k : Nat} (h : a ^ k = 0)
  proof: by
  have h₁ : ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) =
      ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i) +
        ∑ i in Ico (nilpotencyClass a) k, (i.factorial : Rat)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i in Ico (nilpotencyCl

中文:
定理 exp_eq_sum
  条件: {a : A} {k : 自然数} (h : a ^ k = 0)
  证明: by
  have h₁ : ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) =
      ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i) +
        ∑ i in Ico (nilpotencyClass a) k, (i.factorial : Rat)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i in Ico (nilpotencyCl

Depends on / 依赖: add_zero, csInf_le, factorial, i.factorial, mem_Ico, nilpotencyClass, pow_eq_zero_of_le, pow_nilpotencyClass, smul_zero, sum_eq_zero, sum_range_add_sum_Ico
-/
theorem exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) :
    exp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) := by
  have h₁ : ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) =
      ∑ i in range (nilpotencyClass a), (i.factorial : Rat)⁻¹ • (a ^ i) +
        ∑ i in Ico (nilpotencyClass a) k, (i.factorial : Rat)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i in Ico (nilpotencyClass a) k, (i.factorial : Rat)⁻¹ • (a ^ i) = 0 by
    dsimp [exp]
    rw [h₁]; rw [this]; rw [add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k]; rw [h⟩)]; rw [smul_zero]

/--
theorem `exp_smul_eq_sum` / 定理 `exp_smul_eq_sum`

English:
theorem exp_smul_eq_sum
  statement: {M : Type*} [AddCommGroup M] [Module A M] [Module Rat M] {a : A} {m : M}
  proof: by
  rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
  · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)), sum_smul, smul_assoc]
  rw [exp]; rw [sum_smul]; rw [← sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
  suffices ∑ i in Ico k (nilpotencyClass a), ((i.factorial : Rat)⁻¹ 

中文:
定理 exp_smul_eq_sum
  结论: {M : 类型} [AddCommGroup M] [Module A M] [Module Rat M] {a : A} {m : M}
  证明: by
  rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
  · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)), sum_smul, smul_assoc]
  rw [exp]; rw [sum_smul]; rw [← sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
  suffices ∑ i in Ico k (nilpotencyClass a), ((i.factorial : Rat)⁻¹ 

Depends on / 依赖: Nat.le_of_succ_le, add_zero, exp_eq_sum, factorial, i.factorial, le_of_succ_le, le_or_gt, mem_Ico, mul_smul, nilpotencyClass, pow_eq_zero_of_le, pow_nilpotencyClass, pow_sub_mul_pow, simp_rw, smul_assoc, smul_zero, sum_eq_zero, sum_range_add_sum_Ico, sum_smul
-/
theorem exp_smul_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module Rat M] {a : A} {m : M}
    {k : Nat} (h : (a ^ k) • m = 0) (hn : IsNilpotent a) :
    exp a • m = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) • m := by
  rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
  · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)), sum_smul, smul_assoc]
  rw [exp]; rw [sum_smul]; rw [← sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
  suffices ∑ i in Ico k (nilpotencyClass a), ((i.factorial : Rat)⁻¹ • (a ^ i)) • m = 0 by
    simp_rw [this, add_zero, smul_assoc]
  refine sum_eq_zero fun r h₂ => ?_
  rw [smul_assoc]; rw [← pow_sub_mul_pow a (mem_Ico.1 h₂).1]; rw [mul_smul]; rw [h]; rw [smul_zero]; rw [smul_zero]

/--
theorem `exp_add_of_commute` / 定理 `exp_add_of_commute`

English:
theorem exp_add_of_commute
  given: {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b)
  proof: by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [exp_eq_sum (k := 2 * N + 1)
    (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h

中文:
定理 exp_add_of_commute
  条件: {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b)
  证明: by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [exp_eq_sum (k := 2 * N + 1)
    (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h

Depends on / 依赖: Commute, Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero, add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero, exp_eq_sum, pow_eq_zero_of_le
-/
theorem exp_add_of_commute {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp (a + b) = exp a * exp b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [exp_eq_sum (k := 2 * N + 1)
    (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ (by lia))]; rw [exp_eq_sum h₄]; rw [exp_eq_sum h₅]
  set R2N := range (2 * N + 1) with hR2N
  set RN := range (N + 1) with hRN
  have s₁ := by
    calc ∑ i in R2N, (i ! : Rat)⁻¹ • (a + b) ^ i
        = ∑ i in R2N, (i ! : Rat)⁻¹ • ∑ j in range (i + 1), a ^ j * b ^ (i - j) * i.choose j := ?_
      _ = ∑ i in R2N, (∑ j in range (i + 1),
            ((j ! : Rat)⁻¹ * ((i - j) ! : Rat)⁻¹) • (a ^ j * b ^ (i - j))) := ?_
      _ = ∑ ij in R2N ×ˢ R2N with ij.1 + ij.2 <= 2 * N,
            ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · refine sum_congr rfl fun i _ => ?_
      rw [Commute.add_pow h₁ i]
    · simp_rw [smul_sum]
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      simp only [mem_range] at hi hj
      replace hj := Nat.le_of_lt_succ hj
      suffices (i ! : Rat)⁻¹ * (i.choose j) = ((j ! : Rat)⁻¹ * ((i - j)! : Rat)⁻¹) by
        rw [← Nat.cast_commute (i.choose j)]; rw [← this]; rw [← mul_smul_comm]; rw [← nsmul_eq_mul]; rw [mul_smul]; rw [← smul_assoc]; rw [smul_comm]; rw [smul_assoc]
        norm_cast
      rw [Nat.choose_eq_factorial_div_factorial hj]; rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hj) (by positivity)]
      simp [field]
    · rw [hR2N, sum_sigma']
      apply sum_bij (fun ⟨i, j⟩ _ => (j, i - j))
      · simp only [mem_sigma, mem_range, mem_filter, mem_product, and_imp]
        lia
      · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
        rintro ⟨x₁, y₁⟩ - h₁ ⟨x₂, y₂⟩ - h₂ h₃ h₄
        simp_all
        lia
      · simp only [mem_filter, mem_product, mem_range, mem_sigma, exists_prop, Sigma.exists,
          and_imp, Prod.forall, Prod.mk.injEq]
        exact fun x y _ _ _ => ⟨x + y, x, by lia⟩
      · simp only [mem_sigma, mem_range, implies_true]
  have z₁ : ∑ ij in R2N ×ˢ R2N with ¬ ij.1 + ij.2 <= 2 * N,
      ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi => by
      rw [mem_filter] at hi
      cases le_or_gt (N + 1) i.1 with
        | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
        | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅, mul_zero, smul_zero]
  have split₁ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij => ij.1 + ij.2 <= 2 * N)
    (fun ij => ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₁]; rw [add_zero] at split₁
  rw [split₁] at s₁
  have z₂ : ∑ ij in R2N ×ˢ R2N with ¬ (ij.1 <= N ∧ ij.2 <= N),
      ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi => by
    simp only [not_and, not_le, mem_filter] at hi
    cases le_or_gt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅, mul_zero, smul_zero]
  have split₂ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij => ij.1 <= N ∧ ij.2 <= N)
    (fun ij => ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₂]; rw [add_zero] at split₂
  rw [← split₂] at s₁
  have restrict : ∑ ij in R2N ×ˢ R2N with ij.1 <= N ∧ ij.2 <= N,
      ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij in RN ×ˢ RN, ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    apply sum_congr
    · ext x
      simp only [mem_filter, mem_product, mem_range, hR2N, hRN]
      lia
    · tauto
  rw [restrict] at s₁
  have s₂ := by
    calc (∑ i in RN, (i ! : Rat)⁻¹ • a ^ i) * ∑ i in RN, (i ! : Rat)⁻¹ • b ^ i
        = ∑ i in RN, ∑ j in RN, ((i ! : Rat)⁻¹ * (j ! : Rat)⁻¹) • (a ^ i * b ^ j) := ?_
      _ = ∑ ij in RN ×ˢ RN, ((ij.1 ! : Rat)⁻¹ * (ij.2 ! : Rat)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · rw [sum_mul_sum]
      refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
      rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [smul_smul]
    · rw [sum_sigma']
      apply sum_bijective (fun ⟨i, j⟩ => (i, j))
      · exact ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h => by cases h; rfl, fun ⟨i, j⟩ => ⟨⟨i, j⟩, rfl⟩⟩
      · simp only [mem_sigma, mem_product, implies_true]
      · simp only [implies_true]
  rwa [s₂.symm] at s₁

@[simp]
/--
theorem `exp_zero` / 定理 `exp_zero`

English:
theorem exp_zero
  proof: by
  simp [exp_eq_sum (pow_one 0)]

中文:
定理 exp_zero
  证明: by
  simp [exp_eq_sum (pow_one 0)]

Depends on / 依赖: exp_eq_sum, pow_one
-/
theorem exp_zero :
    exp (0 : A) = 1 := by
  simp [exp_eq_sum (pow_one 0)]

/--
theorem `exp_mul_exp_neg_self` / 定理 `exp_mul_exp_neg_self`

English:
theorem exp_mul_exp_neg_self
  given: {a : A} (h : IsNilpotent a)
  proof: by
  simp [← exp_add_of_commute (Commute.neg_right rfl) h h.neg]

中文:
定理 exp_mul_exp_neg_self
  条件: {a : A} (h : IsNilpotent a)
  证明: by
  simp [← exp_add_of_commute (Commute.neg_right rfl) h h.neg]

Depends on / 依赖: Commute, Commute.neg_right, exp_add_of_commute, h.neg, neg_right
-/
theorem exp_mul_exp_neg_self {a : A} (h : IsNilpotent a) :
    exp a * exp (-a) = 1 := by
  simp [← exp_add_of_commute (Commute.neg_right rfl) h h.neg]

/--
theorem `exp_neg_mul_exp_self` / 定理 `exp_neg_mul_exp_self`

English:
theorem exp_neg_mul_exp_self
  given: {a : A} (h : IsNilpotent a)
  proof: by
  simp [← exp_add_of_commute (Commute.neg_left rfl) h.neg h]

中文:
定理 exp_neg_mul_exp_self
  条件: {a : A} (h : IsNilpotent a)
  证明: by
  simp [← exp_add_of_commute (Commute.neg_left rfl) h.neg h]

Depends on / 依赖: Commute, Commute.neg_left, exp_add_of_commute, h.neg, neg_left
-/
theorem exp_neg_mul_exp_self {a : A} (h : IsNilpotent a) :
    exp (-a) * exp a = 1 := by
  simp [← exp_add_of_commute (Commute.neg_left rfl) h.neg h]

/--
theorem `isUnit_exp` / 定理 `isUnit_exp`

English:
theorem isUnit_exp
  given: {a : A} (h : IsNilpotent a)
  statement: IsUnit (exp a)
  proof: by
  apply isUnit_iff_exists.2
  use exp (-a)
  exact ⟨exp_mul_exp_neg_self h, exp_neg_mul_exp_self h⟩

中文:
定理 isUnit_exp
  条件: {a : A} (h : IsNilpotent a)
  结论: IsUnit (exp a)
  证明: by
  apply isUnit_iff_exists.2
  use exp (-a)
  exact ⟨exp_mul_exp_neg_self h, exp_neg_mul_exp_self h⟩

Depends on / 依赖: exp_mul_exp_neg_self, exp_neg_mul_exp_self, isUnit_iff_exists
-/
theorem isUnit_exp {a : A} (h : IsNilpotent a) : IsUnit (exp a) := by
  apply isUnit_iff_exists.2
  use exp (-a)
  exact ⟨exp_mul_exp_neg_self h, exp_neg_mul_exp_self h⟩

/--
theorem `map_exp` / 定理 `map_exp`

English:
theorem map_exp
  statement: {B F : Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module Rat B]
  proof: by
  obtain ⟨k, hk⟩ := ha
  have hk' : (f a) ^ k = 0 := by simp [← map_pow, hk]
  simp [exp_eq_sum hk, exp_eq_sum hk', map_rat_smul]

中文:
定理 map_exp
  结论: {B F : 类型} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module Rat B]
  证明: by
  obtain ⟨k, hk⟩ := ha
  have hk' : (f a) ^ k = 0 := by simp [← map_pow, hk]
  simp [exp_eq_sum hk, exp_eq_sum hk', map_rat_smul]

Depends on / 依赖: exp_eq_sum, map_pow, map_rat_smul
-/
theorem map_exp {B F : Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module Rat B]
    {a : A} (ha : IsNilpotent a) (f : F) :
    f (exp a) = exp (f a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (f a) ^ k = 0 := by simp [← map_pow, hk]
  simp [exp_eq_sum hk, exp_eq_sum hk', map_rat_smul]

/--
theorem `exp_smul` / 定理 `exp_smul`

English:
theorem exp_smul
  statement: {G : Type*} [Monoid G] [MulSemiringAction G A]
  proof: (map_exp ha (MulSemiringAction.toRingHom G A g)).symm

中文:
定理 exp_smul
  结论: {G : 类型} [Monoid G] [MulSemiringAction G A]
  证明: (map_exp ha (MulSemiringAction.toRingHom G A g)).symm

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingHom, map_exp, toRingHom
-/
theorem exp_smul {G : Type*} [Monoid G] [MulSemiringAction G A]
    (g : G) {a : A} (ha : IsNilpotent a) :
    exp (g • a) = g • exp a :=
  (map_exp ha (MulSemiringAction.toRingHom G A g)).symm

/--
theorem `isNilpotent_exp_sub_one` / 定理 `isNilpotent_exp_sub_one`

English:
theorem isNilpotent_exp_sub_one
  given: {a : A} (ha : IsNilpotent a)
  statement: IsNilpotent (exp a - 1)
  proof: by
  nontriviality A
  rw [exp]; rw [← Nat.sub_add_cancel (pos_nilpotencyClass_iff.2 ha)]; rw [Finset.sum_range_succ']
  simp only [Nat.succ_eq_add_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul, add_sub_cancel_right]
  apply Commute.isNilpotent_sum fun _ _ => smul 

中文:
定理 isNilpotent_exp_sub_one
  条件: {a : A} (ha : IsNilpotent a)
  结论: IsNilpotent (exp a - 1)
  证明: by
  nontriviality A
  rw [exp]; rw [← Nat.sub_add_cancel (pos_nilpotencyClass_iff.2 ha)]; rw [Finset.sum_range_succ']
  simp only [Nat.succ_eq_add_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul, add_sub_cancel_right]
  apply Commute.isNilpotent_sum fun _ _ => smul 

Depends on / 依赖: Commute, Commute.isNilpotent_sum, Finset, Finset.sum_range_succ, Nat.cast_one, Nat.factorial_ne_zero, Nat.factorial_zero, Nat.sub_add_cancel, Nat.succ_eq_add_one, add_sub_cancel_right, cast_one, factorial_ne_zero, factorial_zero, inv_one, isNilpotent_sum, nontriviality, one_smul, pos_nilpotencyClass_iff, pow_of_pos, pow_zero
-/
theorem isNilpotent_exp_sub_one {a : A} (ha : IsNilpotent a) : IsNilpotent (exp a - 1) := by
  nontriviality A
  rw [exp]; rw [← Nat.sub_add_cancel (pos_nilpotencyClass_iff.2 ha)]; rw [Finset.sum_range_succ']
  simp only [Nat.succ_eq_add_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul, add_sub_cancel_right]
  apply Commute.isNilpotent_sum fun _ _ => smul (pow_of_pos ha <| by positivity) _
  simp [Nat.factorial_ne_zero]

end IsNilpotent

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module Rat M] [Module Rat N]

open IsNilpotent TensorProduct

/--
theorem `commute_exp_left_of_commute` / 定理 `commute_exp_left_of_commute`

English:
theorem commute_exp_left_of_commute
  proof: by
  ext m
  obtain ⟨k, hfM⟩ := hfM
  obtain ⟨l, hfN⟩ := hfN
  let kl := max k l
  replace hfM : fM ^ kl = 0 := pow_eq_zero_of_le (by omega) hfM
  replace hfN : fN ^ kl = 0 := pow_eq_zero_of_le (by omega) hfN
  have (i : Nat) : (fN ^ i) (g m) = g ((fM ^ i) m) := by
    simpa using LinearMap.congr_fu

中文:
定理 commute_exp_left_of_commute
  证明: by
  ext m
  obtain ⟨k, hfM⟩ := hfM
  obtain ⟨l, hfN⟩ := hfN
  let kl := max k l
  replace hfM : fM ^ kl = 0 := pow_eq_zero_of_le (by omega) hfM
  replace hfN : fN ^ kl = 0 := pow_eq_zero_of_le (by omega) hfN
  have (i : Nat) : (fN ^ i) (g m) = g ((fM ^ i) m) := by
    simpa using LinearMap.congr_fu

Depends on / 依赖: LinearMap, LinearMap.congr_fun, Module, Module.End.commute_pow_left_of_commute, commute_pow_left_of_commute, congr_fun, exp_eq_sum, map_rat_smul, pow_eq_zero_of_le, replace
-/
theorem commute_exp_left_of_commute
    {fM : Module.End R M} {fN : Module.End R N} {g : M ->ₗ[R] N}
    (hfM : IsNilpotent fM)
    (hfN : IsNilpotent fN)
    (h : fN ∘ₗ g = g ∘ₗ fM) :
    exp fN ∘ₗ g = g ∘ₗ exp fM := by
  ext m
  obtain ⟨k, hfM⟩ := hfM
  obtain ⟨l, hfN⟩ := hfN
  let kl := max k l
  replace hfM : fM ^ kl = 0 := pow_eq_zero_of_le (by omega) hfM
  replace hfN : fN ^ kl = 0 := pow_eq_zero_of_le (by omega) hfN
  have (i : Nat) : (fN ^ i) (g m) = g ((fM ^ i) m) := by
    simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) m
  simp [exp_eq_sum hfM, exp_eq_sum hfN, this, map_rat_smul]

/--
theorem `exp_mul_of_derivation` / 定理 `exp_mul_of_derivation`

English:
theorem exp_mul_of_derivation
  statement: (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B]
  proof: by
  let DL : Module.End R (B otimes[R] B) := D.lTensor B
  let DR : Module.End R (B otimes[R] B) := D.rTensor B
have h_nilL : IsNilpotent DL := h_nil.map lTensorAlgHom R B B
have h_nilR : IsNilpotent DR := h_nil.map rTensorAlgHom R B B
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m 

中文:
定理 exp_mul_of_derivation
  结论: (R B : 类型) [CommRing R] [NonUnitalNonAssocRing B]
  证明: by
  let DL : Module.End R (B otimes[R] B) := D.lTensor B
  let DR : Module.End R (B otimes[R] B) := D.rTensor B
have h_nilL : IsNilpotent DL := h_nil.map lTensorAlgHom R B B
have h_nilR : IsNilpotent DR := h_nil.map rTensorAlgHom R B B
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m 

Depends on / 依赖: Commute, D.lTensor, D.rTensor, IsNilpotent, LinearMap, LinearMap.congr_fun, LinearMap.mul, Module, Module.End, congr_fun, h_comm, h_nil, h_nil.map, h_nilL, h_nilR, lTensor, lTensorAlgHom, otimes, rTensor, rTensorAlgHom
-/
theorem exp_mul_of_derivation (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B]
    [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [Module Rat B]
    (D : B ->ₗ[R] B) (h_der : forall x y, D (x * y) = x * D y + (D x) * y)
    (h_nil : IsNilpotent D) (x y : B) :
    exp D (x * y) = (exp D x) * (exp D y) := by
  let DL : Module.End R (B otimes[R] B) := D.lTensor B
  let DR : Module.End R (B otimes[R] B) := D.rTensor B
have h_nilL : IsNilpotent DL := h_nil.map lTensorAlgHom R B B
have h_nilR : IsNilpotent DR := h_nil.map rTensorAlgHom R B B
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m : B otimes[R] B ->ₗ[R] B := LinearMap.mul' R B with hm
  have h₁ : exp D (x * y) = m (exp (DL + DR) (x otimesₜ[R] y)) := by
    suffices exp D ∘ₗ m = m ∘ₗ exp (DL + DR) by simpa using! LinearMap.congr_fun this (x otimesₜ[R] y)
    apply commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h_nil
    ext
    simp [DL, DR, hm, h_der]
  have h₂ : exp DL = (exp D).lTensor B := (h_nil.map_exp (lTensorAlgHom R B B)).symm
  have h₃ : exp DR = (exp D).rTensor B := (h_nil.map_exp (rTensorAlgHom R B B)).symm
  simp [h₁, exp_add_of_commute h_comm h_nilL h_nilR, h₂, h₃, hm]

end Module.End
