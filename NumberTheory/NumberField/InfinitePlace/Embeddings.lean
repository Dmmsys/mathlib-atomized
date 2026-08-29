/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Embeddings of number fields

This file defines the embeddings of a number field and, in particular, the embeddings into
the field of complex numbers.

## Main Definitions and Results

* `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`: let `x ∈ K` with `K` a number field and
  let `A` be an algebraically closed field of char. 0. Then the images of `x` under the
  embeddings of `K` in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `NumberField.Embeddings.pow_eq_one_of_norm_le_one`: A non-zero algebraic integer whose conjugates
  are all inside the closed unit disk is a root of unity, this is also known as Kronecker's theorem.
* `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags

number field, embeddings
-/

@[expose] public section

open scoped Finset

namespace NumberField.Embeddings

section Fintype

open Module

variable (K : Type*) [Field K]
variable (A : Type*) [Field A] [CharZero A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: K] [Algebra.IsAlgebraic Rat K] [IsAlgClosed A] : Nonempty (K ->+* A)
  body: by
  obtain ⟨f⟩ : Nonempty (K ->ₐ[Rat] A) := by
    apply IntermediateField.nonempty_algHom_of_splits
    exact fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  exact ⟨f.toRingHom⟩

中文:
实例 [特征零
  签名: K] [代数.是代数 有理数 K] [是代数闭 A] : 非空 (K ->+* A)
  定义体: by
  obtain ⟨f⟩ : Nonempty (K ->ₐ[Rat] A) := by
    apply IntermediateField.nonempty_algHom_of_splits
    exact fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  exact ⟨f.toRingHom⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IntermediateField, IntermediateField.nonempty_algHom_of_splits, IsAlgClosed, IsAlgClosed.splits, IsIntegral, Nonempty, f.toRingHom, isIntegral, nonempty_algHom_of_splits, splits, toRingHom
-/
instance [CharZero K] [Algebra.IsAlgebraic Rat K] [IsAlgClosed A] : Nonempty (K ->+* A) := by
  obtain ⟨f⟩ : Nonempty (K ->ₐ[Rat] A) := by
    apply IntermediateField.nonempty_algHom_of_splits
    exact fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  exact ⟨f.toRingHom⟩

variable [NumberField K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (K ->+* A)
  body: Fintype.ofEquiv (K ->ₐ[Rat] A) (RingHom.equivRatAlgHom K A).symm

中文:
实例 :
  签名: 有限类型 (K ->+* A)
  定义体: Fintype.ofEquiv (K ->ₐ[Rat] A) (RingHom.equivRatAlgHom K A).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, RingHom, RingHom.equivRatAlgHom, equivRatAlgHom, ofEquiv
-/
noncomputable instance : Fintype (K ->+* A) :=
  Fintype.ofEquiv (K ->ₐ[Rat] A) (RingHom.equivRatAlgHom K A).symm

variable [IsAlgClosed A]

/--
theorem `card` / 定理 `card`

English:
theorem card
  statement: Fintype.card (K ->+* A) = finrank Rat K
  proof: by
  rw [Fintype.ofEquiv_card (RingHom.equivRatAlgHom K A).symm]; rw [AlgHom.card]

中文:
定理 card
  结论: 有限类型.card (K ->+* A) = finrank 有理数 K
  证明: by
  rw [Fintype.ofEquiv_card (RingHom.equivRatAlgHom K A).symm]; rw [AlgHom.card]

Depends on / 依赖: AlgHom, AlgHom.card, Fintype, Fintype.ofEquiv_card, RingHom, RingHom.equivRatAlgHom, equivRatAlgHom, ofEquiv_card
-/
theorem card : Fintype.card (K ->+* A) = finrank Rat K := by
  rw [Fintype.ofEquiv_card (RingHom.equivRatAlgHom K A).symm]; rw [AlgHom.card]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (K ->+* A)
  body: by
  rw [← Fintype.card_pos_iff]; rw [NumberField.Embeddings.card K A]
  exact Module.finrank_pos

中文:
实例 :
  签名: 非空 (K ->+* A)
  定义体: by
  rw [← Fintype.card_pos_iff]; rw [NumberField.Embeddings.card K A]
  exact Module.finrank_pos

Depends on / 依赖: Embeddings, Fintype, Fintype.card_pos_iff, Module, Module.finrank_pos, NumberField, NumberField.Embeddings.card, card_pos_iff, finrank_pos
-/
instance : Nonempty (K ->+* A) := by
  rw [← Fintype.card_pos_iff]; rw [NumberField.Embeddings.card K A]
  exact Module.finrank_pos

end Fintype

section Roots

open Set Polynomial

variable (K A : Type*) [Field K] [NumberField K] [Field A] [Algebra Rat A] [IsAlgClosed A] (x : K)

/--
theorem `range_eval_eq_rootSet_minpoly` / 定理 `range_eval_eq_rootSet_minpoly`

English:
theorem range_eval_eq_rootSet_minpoly
  proof: by
  convert! (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

中文:
定理 range_eval_eq_rootSet_minpoly
  证明: by
  convert! (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

Depends on / 依赖: NumberField, NumberField.isAlgebraic, convert, isAlgebraic, range_eval_eq_rootSet_minpoly, toRatAlgHom, toRingHom
-/
theorem range_eval_eq_rootSet_minpoly :
    (range fun φ : K ->+* A => φ x) = (minpoly Rat x).rootSet A := by
  convert! (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

end Roots

section Bounded

open Module Polynomial Set

variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra Rat A]

/--
theorem `coeff_bdd_of_norm_le` / 定理 `coeff_bdd_of_norm_le`

English:
theorem coeff_bdd_of_norm_le
  given: {B : Real} {x : K} (h : forall φ : K ->+* A, ‖φ x‖ <= B) (i : Nat)
  proof: by
  have hx := Algebra.IsSeparable.isIntegral Rat x
  rw [← norm_algebraMap' A]; rw [← coeff_map (algebraMap Rat A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

中文:
定理 coeff_bdd_of_norm_le
  条件: {B : 实数} {x : K} (h : 对任意 φ : K ->+* A, ‖φ x‖ <= B) (i : 自然数)
  证明: by
  have hx := Algebra.IsSeparable.isIntegral Rat x
  rw [← norm_algebraMap' A]; rw [← coeff_map (algebraMap Rat A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, IsAlgClosed, IsAlgClosed.splits, IsSeparable, Multiset, Multiset.mem_toFinset, algebraMap, classical, coeff_bdd_of_roots_le, coeff_map, isIntegral, mem_toFinset, minpoly, minpoly.monic, minpoly.natDegree_le, natDegree_le, norm_algebraMap, range_eval_eq_rootSet_minpoly, splits
-/
theorem coeff_bdd_of_norm_le {B : Real} {x : K} (h : forall φ : K ->+* A, ‖φ x‖ <= B) (i : Nat) :
    ‖(minpoly Rat x).coeff i‖ <= max B 1 ^ finrank Rat K * (finrank Rat K).choose (finrank Rat K / 2) := by
  have hx := Algebra.IsSeparable.isIntegral Rat x
  rw [← norm_algebraMap' A]; rw [← coeff_map (algebraMap Rat A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

variable (K A)

/--
theorem `finite_of_norm_le` / 定理 `finite_of_norm_le`

English:
theorem finite_of_norm_le
  given: (B : Real)
  statement: {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite
  proof: by
  classical
  let C := Nat.ceil (max B 1 ^ finrank Rat K * (finrank Rat K).choose (finrank Rat K / 2))
  have := bUnion_roots_finite (algebraMap Int K) (finrank Rat K) (finite_Icc (-C : Int) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_Rat_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' Rat hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval Int x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap Int Rat), ← h_map_Rat_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc]; rw [← abs_le]; rw [← @Int.cast_le Real]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_Rat_minpoly]; rw [coeff_map]; rw [eq_intCast]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

中文:
定理 finite_of_norm_le
  条件: (B : 实数)
  结论: {x : K | 是整 整数 x ∧ 对任意 φ : K ->+* A, ‖φ x‖ <= B}.有限
  证明: by
  classical
  let C := Nat.ceil (max B 1 ^ finrank Rat K * (finrank Rat K).choose (finrank Rat K / 2))
  have := bUnion_roots_finite (algebraMap Int K) (finrank Rat K) (finite_Icc (-C : Int) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_Rat_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' Rat hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval Int x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap Int Rat), ← h_map_Rat_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc]; rw [← abs_le]; rw [← @Int.cast_le Real]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_Rat_minpoly]; rw [coeff_map]; rw [eq_intCast]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

Depends on / 依赖: Nat.ceil, algebraMap, bUnion_roots_finite, classical, finite_Icc, finrank, h_map_Rat_minpo, h_map_Rat_minpoly, isIntegrallyClosed_eq_field_fractions, mem_iUnion, mem_rootSet, minpoly, minpoly.aeval, minpoly.isIntegrallyClosed_eq_field_fractions, minpoly.monic, minpoly.ne_zero, natDegree_map, ne_zero, simp_rw, subset
-/
theorem finite_of_norm_le (B : Real) : {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite := by
  classical
  let C := Nat.ceil (max B 1 ^ finrank Rat K * (finrank Rat K).choose (finrank Rat K / 2))
  have := bUnion_roots_finite (algebraMap Int K) (finrank Rat K) (finite_Icc (-C : Int) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_Rat_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' Rat hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval Int x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap Int Rat), ← h_map_Rat_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc]; rw [← abs_le]; rw [← @Int.cast_le Real]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_Rat_minpoly]; rw [coeff_map]; rw [eq_intCast]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

/--
theorem `pow_eq_one_of_norm_le_one` / 定理 `pow_eq_one_of_norm_le_one`

English:
theorem pow_eq_one_of_norm_le_one
  statement: {x : K} (hx₀ : x != 0) (hxi : IsIntegral Int x)
  proof: by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (f := (x ^ · : Nat -> K)) Set.infinite_univ
      (fun a _ => mem_ofPred.mpr <|
        ⟨hxi.pow a, fun φ => by simp [pow_le_one₀ (norm_nonneg (φ x)) <| hx φ]⟩)
      (finite_of_norm_le K A (1 : Real))
  wlog hlt : b < a
  · exact this K A hx₀ hxi hx b a habne.symm h.symm (habne.lt_or_gt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le]; rw [pow_add]; rw [mul_left_eq_self₀] at h
  refine h.resolve_right fun hp => hx₀ (eq_zero_of_pow_eq_zero hp)

中文:
定理 pow_eq_one_of_norm_le_one
  结论: {x : K} (hx₀ : x != 0) (hxi : 是整 整数 x)
  证明: by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (f := (x ^ · : Nat -> K)) Set.infinite_univ
      (fun a _ => mem_ofPred.mpr <|
        ⟨hxi.pow a, fun φ => by simp [pow_le_one₀ (norm_nonneg (φ x)) <| hx φ]⟩)
      (finite_of_norm_le K A (1 : Real))
  wlog hlt : b < a
  · exact this K A hx₀ hxi hx b a habne.symm h.symm (habne.lt_or_gt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le]; rw [pow_add]; rw [mul_left_eq_self₀] at h
  refine h.resolve_right fun hp => hx₀ (eq_zero_of_pow_eq_zero hp)

Depends on / 依赖: Infinite, Nat.sub_add_cancel, Set.Infinite.exists_ne_map_eq_of_mapsTo, Set.infinite_univ, exists_ne_map_eq_of_mapsTo, finite_of_norm_le, h.resolve_right, h.symm, habne.lt_or_gt.resolve_right, habne.symm, hlt.le, hxi.pow, infinite_univ, lt_or_gt, mem_ofPred, mem_ofPred.mpr, norm_nonneg, pow_add, resolve_right, sub_add_cancel
-/
theorem pow_eq_one_of_norm_le_one {x : K} (hx₀ : x != 0) (hxi : IsIntegral Int x)
    (hx : forall φ : K ->+* A, ‖φ x‖ <= 1) : exists (n : Nat) (_ : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (f := (x ^ · : Nat -> K)) Set.infinite_univ
      (fun a _ => mem_ofPred.mpr <|
        ⟨hxi.pow a, fun φ => by simp [pow_le_one₀ (norm_nonneg (φ x)) <| hx φ]⟩)
      (finite_of_norm_le K A (1 : Real))
  wlog hlt : b < a
  · exact this K A hx₀ hxi hx b a habne.symm h.symm (habne.lt_or_gt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le]; rw [pow_add]; rw [mul_left_eq_self₀] at h
  refine h.resolve_right fun hp => hx₀ (eq_zero_of_pow_eq_zero hp)

/--
theorem `pow_eq_one_of_norm_eq_one` / 定理 `pow_eq_one_of_norm_eq_one`

English:
theorem pow_eq_one_of_norm_eq_one
  given: {x : K} (hxi : IsIntegral Int x) (hx : forall φ : K ->+* A, ‖φ x‖ = 1)
  proof: by
apply pow_eq_one_of_norm_le_one K A _ hxi fun φ => le_of_eq hx φ
  intro rfl
  simp_rw [map_zero, norm_zero, zero_ne_one] at hx
  exact hx (IsAlgClosed.lift (R := Rat)).toRingHom

中文:
定理 pow_eq_one_of_norm_eq_one
  条件: {x : K} (hxi : 是整 整数 x) (hx : 对任意 φ : K ->+* A, ‖φ x‖ = 1)
  证明: by
apply pow_eq_one_of_norm_le_one K A _ hxi fun φ => le_of_eq hx φ
  intro rfl
  simp_rw [map_zero, norm_zero, zero_ne_one] at hx
  exact hx (IsAlgClosed.lift (R := Rat)).toRingHom

Depends on / 依赖: IsAlgClosed, IsAlgClosed.lift, le_of_eq, map_zero, norm_zero, pow_eq_one_of_norm_le_one, simp_rw, toRingHom, zero_ne_one
-/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral Int x) (hx : forall φ : K ->+* A, ‖φ x‖ = 1) :
    exists (n : Nat) (_ : 0 < n), x ^ n = 1 := by
apply pow_eq_one_of_norm_le_one K A _ hxi fun φ => le_of_eq hx φ
  intro rfl
  simp_rw [map_zero, norm_zero, zero_ne_one] at hx
  exact hx (IsAlgClosed.lift (R := Rat)).toRingHom

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] (φ : K ->+* A)

/--
Definition of `NumberField.place` / `NumberField.place` 的定义

English:
definition NumberField.place
  signature: : AbsoluteValue K Real
  body: (IsAbsoluteValue.toAbsoluteValue (norm : A -> Real)).comp φ.injective

@[simp]

中文:
定义 数域.place
  签名: : 绝对值 K 实数
  定义体: (IsAbsoluteValue.toAbsoluteValue (norm : A -> Real)).comp φ.injective

@[simp]

Depends on / 依赖: IsAbsoluteValue, IsAbsoluteValue.toAbsoluteValue, injective, toAbsoluteValue
-/
def NumberField.place : AbsoluteValue K Real :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A -> Real)).comp φ.injective

@[simp]
/--
theorem `NumberField.place_apply` / 定理 `NumberField.place_apply`

English:
theorem NumberField.place_apply
  given: (x : K)
  statement: (NumberField.place φ) x = norm (φ x)
  proof: rfl

中文:
定理 数域.place_apply
  条件: (x : K)
  结论: (数域.place φ) x = norm (φ x)
  证明: rfl
-/
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) := rfl

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open scoped ComplexConjugate

variable (K : Type*) [Field K] {k : Type*} [Field k]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex)
  body: by
  letI := φ.toAlgebra
  exact (IsAlgClosed.lift (R := k)).toRingHom

@[simp]

中文:
定义 lift
  签名: [代数 k K] [代数.是代数 k K] (φ : k ->+* 复形)
  定义体: by
  letI := φ.toAlgebra
  exact (IsAlgClosed.lift (R := k)).toRingHom

@[simp]

Depends on / 依赖: IsAlgClosed, IsAlgClosed.lift, toAlgebra, toRingHom
-/
noncomputable def lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) : K ->+* Complex := by
  letI := φ.toAlgebra
  exact (IsAlgClosed.lift (R := k)).toRingHom

@[simp]
/--
theorem `lift_comp_algebraMap` / 定理 `lift_comp_algebraMap`

English:
theorem lift_comp_algebraMap
  given: [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex)
  proof: by
  unfold lift
  let := φ.toAlgebra
  rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]; rw [RingHom.algebraMap_toAlgebra']

@[simp]

中文:
定理 lift_comp_algebraMap
  条件: [代数 k K] [代数.是代数 k K] (φ : k ->+* 复形)
  证明: by
  unfold lift
  let := φ.toAlgebra
  rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]; rw [RingHom.algebraMap_toAlgebra']

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_algebraMap_of_tower, AlgHom.toRingHom_eq_coe, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, comp_algebraMap_of_tower, toAlgebra, toRingHom_eq_coe
-/
theorem lift_comp_algebraMap [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) :
    (lift K φ).comp (algebraMap k K) = φ := by
  unfold lift
  let := φ.toAlgebra
  rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]; rw [RingHom.algebraMap_toAlgebra']

@[simp]
/--
theorem `lift_algebraMap_apply` / 定理 `lift_algebraMap_apply`

English:
theorem lift_algebraMap_apply
  given: [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) (x : k)
  proof: RingHom.congr_fun (lift_comp_algebraMap K φ) x

中文:
定理 lift_algebraMap_apply
  条件: [代数 k K] [代数.是代数 k K] (φ : k ->+* 复形) (x : k)
  证明: RingHom.congr_fun (lift_comp_algebraMap K φ) x

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun, lift_comp_algebraMap
-/
theorem lift_algebraMap_apply [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) (x : k) :
    lift K φ (algebraMap k K x) = φ x :=
  RingHom.congr_fun (lift_comp_algebraMap K φ) x

variable {K}

/--
Definition of `conjugate` / `conjugate` 的定义

English:
abbreviation conjugate
  signature: (φ : K ->+* Complex)
  body: star φ

@[simp]

中文:
缩写 conjugate
  签名: (φ : K ->+* 复形)
  定义体: star φ

@[simp]
-/
abbrev conjugate (φ : K ->+* Complex) : K ->+* Complex := star φ

@[simp]
/--
theorem `conjugate_comp` / 定理 `conjugate_comp`

English:
theorem conjugate_comp
  given: (φ : K ->+* Complex) (σ : k ->+* K)
  proof: rfl

中文:
定理 conjugate_comp
  条件: (φ : K ->+* 复形) (σ : k ->+* K)
  证明: rfl
-/
theorem conjugate_comp (φ : K ->+* Complex) (σ : k ->+* K) :
    (conjugate φ).comp σ = conjugate (φ.comp σ) :=
  rfl

variable (K) in
/--
theorem `involutive_conjugate` / 定理 `involutive_conjugate`

English:
theorem involutive_conjugate
  proof: by
  intro; simp

@[simp]

中文:
定理 involutive_conjugate
  证明: by
  intro; simp

@[simp]
-/
theorem involutive_conjugate :
    Function.Involutive (conjugate : (K ->+* Complex) -> (K ->+* Complex)) := by
  intro; simp

@[simp]
/--
theorem `conjugate_coe_eq` / 定理 `conjugate_coe_eq`

English:
theorem conjugate_coe_eq
  given: (φ : K ->+* Complex) (x : K)
  statement: (conjugate φ) x = conj (φ x)
  proof: rfl

中文:
定理 conjugate_coe_eq
  条件: (φ : K ->+* 复形) (x : K)
  结论: (conjugate φ) x = conj (φ x)
  证明: rfl
-/
theorem conjugate_coe_eq (φ : K ->+* Complex) (x : K) : (conjugate φ) x = conj (φ x) := rfl

/--
theorem `place_conjugate` / 定理 `place_conjugate`

English:
theorem place_conjugate
  given: (φ : K ->+* Complex)
  statement: place (conjugate φ) = place φ
  proof: by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

中文:
定理 place_conjugate
  条件: (φ : K ->+* 复形)
  结论: place (conjugate φ) = place φ
  证明: by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

Depends on / 依赖: conjugate_coe_eq, norm_conj, place_apply
-/
theorem place_conjugate (φ : K ->+* Complex) : place (conjugate φ) = place φ := by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

/--
Definition of `IsReal` / `IsReal` 的定义

English:
abbreviation IsReal
  signature: (φ : K ->+* Complex)
  body: IsSelfAdjoint φ

中文:
缩写 Is实数
  签名: (φ : K ->+* 复形)
  定义体: IsSelfAdjoint φ

Depends on / 依赖: IsSelfAdjoint
-/
abbrev IsReal (φ : K ->+* Complex) : Prop := IsSelfAdjoint φ

/--
theorem `isReal_iff` / 定理 `isReal_iff`

English:
theorem isReal_iff
  given: {φ : K ->+* Complex}
  statement: IsReal φ ↔ conjugate φ = φ
  proof: isSelfAdjoint_iff

中文:
定理 is实数_iff
  条件: {φ : K ->+* 复形}
  结论: Is实数 φ ↔ conjugate φ = φ
  证明: isSelfAdjoint_iff

Depends on / 依赖: isSelfAdjoint_iff
-/
theorem isReal_iff {φ : K ->+* Complex} : IsReal φ ↔ conjugate φ = φ := isSelfAdjoint_iff

/--
theorem `isReal_conjugate_iff` / 定理 `isReal_conjugate_iff`

English:
theorem isReal_conjugate_iff
  given: {φ : K ->+* Complex}
  statement: IsReal (conjugate φ) ↔ IsReal φ
  proof: IsSelfAdjoint.star_iff

中文:
定理 is实数_conjugate_iff
  条件: {φ : K ->+* 复形}
  结论: Is实数 (conjugate φ) ↔ Is实数 φ
  证明: IsSelfAdjoint.star_iff

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_iff, star_iff
-/
theorem isReal_conjugate_iff {φ : K ->+* Complex} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff

/--
Definition of `IsReal.embedding` / `IsReal.embedding` 的定义

English:
definition IsReal.embedding
  signature: {φ : K ->+* Complex} (hφ : IsReal φ)
  body: (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, forall_const]

@[simp]

中文:
定义 Is实数.embedding
  签名: {φ : K ->+* 复形} (hφ : Is实数 φ)
  定义体: (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, forall_const]

@[simp]
-/
def IsReal.embedding {φ : K ->+* Complex} (hφ : IsReal φ) : K ->+* Real where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, forall_const]

@[simp]
/--
theorem `IsReal.coe_embedding_apply` / 定理 `IsReal.coe_embedding_apply`

English:
theorem IsReal.coe_embedding_apply
  given: {φ : K ->+* Complex} (hφ : IsReal φ) (x : K)
  proof: by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x

中文:
定理 Is实数.coe_embedding_apply
  条件: {φ : K ->+* 复形} (hφ : Is实数 φ) (x : K)
  证明: by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x

Depends on / 依赖: Complex.conj_eq_iff_im, Complex.ext, RingHom, RingHom.congr_fun, congr_fun, conj_eq_iff_im, eq_comm, ofReal_im
-/
theorem IsReal.coe_embedding_apply {φ : K ->+* Complex} (hφ : IsReal φ) (x : K) :
    (hφ.embedding x : Complex) = φ x := by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x

/--
lemma `IsReal.comp` / 引理 `IsReal.comp`

English:
lemma IsReal.comp
  given: (f : k ->+* K) {φ : K ->+* Complex} (hφ : IsReal φ)
  proof: by ext1 x; simpa using RingHom.congr_fun hφ (f x)

中文:
引理 Is实数.comp
  条件: (f : k ->+* K) {φ : K ->+* 复形} (hφ : Is实数 φ)
  证明: by ext1 x; simpa using RingHom.congr_fun hφ (f x)

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun
-/
lemma IsReal.comp (f : k ->+* K) {φ : K ->+* Complex} (hφ : IsReal φ) :
    IsReal (φ.comp f) := by ext1 x; simpa using RingHom.congr_fun hφ (f x)

/--
lemma `isReal_comp_iff` / 引理 `isReal_comp_iff`

English:
lemma isReal_comp_iff
  given: {f : k ≃+* K} {φ : K ->+* Complex}
  proof: ⟨fun H => by convert! H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩

中文:
引理 is实数_comp_iff
  条件: {f : k ≃+* K} {φ : K ->+* 复形}
  证明: ⟨fun H => by convert! H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩

Depends on / 依赖: H.comp, IsReal, IsReal.comp, convert, f.symm.toRingHom, toRingHom
-/
lemma isReal_comp_iff {f : k ≃+* K} {φ : K ->+* Complex} :
    IsReal (φ.comp (f : k ->+* K)) ↔ IsReal φ :=
  ⟨fun H => by convert! H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩

/--
lemma `exists_comp_symm_eq_of_comp_eq` / 引理 `exists_comp_symm_eq_of_comp_eq`

English:
lemma exists_comp_symm_eq_of_comp_eq
  statement: [Algebra k K] [IsGalois k K] (φ ψ : K ->+* Complex)
  proof: by
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K ->ₐ[k] Complex := { ψ with commutes' := fun r => (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

中文:
引理 存在_comp_symm_eq_of_comp_eq
  结论: [代数 k K] [是Galois k K] (φ ψ : K ->+* 复形)
  证明: by
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K ->ₐ[k] Complex := { ψ with commutes' := fun r => (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

Depends on / 依赖: AlgHom, AlgHom.restrictNormal, AlgHom.restrictNormal_commutes, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.congr_fun, algebraMap, commutes, congr_fun, of_algebraMap_eq, restrictNormal, restrictNormal_commutes, toAlgebra
-/
lemma exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K ->+* Complex)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    exists σ : Gal(K/k), φ.comp σ.symm = ψ := by
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K ->ₐ[k] Complex := { ψ with commutes' := fun r => (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

variable [Algebra k K] (φ : K ->+* Complex) (σ : Gal(K/k))

/--
Definition of `IsConj` / `IsConj` 的定义

English:
definition IsConj
  signature: : Prop
  body: conjugate φ = φ.comp σ

中文:
定义 IsConj
  签名: : 命题
  定义体: conjugate φ = φ.comp σ

Depends on / 依赖: conjugate
-/
def IsConj : Prop := conjugate φ = φ.comp σ

variable {φ σ}

/--
lemma `IsConj.eq` / 引理 `IsConj.eq`

English:
lemma IsConj.eq
  given: (h : IsConj φ σ) (x)
  statement: φ (σ x) = star (φ x)
  proof: RingHom.congr_fun h.symm x

中文:
引理 IsConj.eq
  条件: (h : IsConj φ σ) (x)
  结论: φ (σ x) = star (φ x)
  证明: RingHom.congr_fun h.symm x

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun, h.symm
-/
lemma IsConj.eq (h : IsConj φ σ) (x) : φ (σ x) = star (φ x) := RingHom.congr_fun h.symm x

/--
lemma `IsConj.ext` / 引理 `IsConj.ext`

English:
lemma IsConj.ext
  given: {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂)
  statement: σ₁ = σ₂
  proof: AlgEquiv.ext fun x => φ.injective ((h₁.eq x).trans (h₂.eq x).symm)

中文:
引理 IsConj.ext
  条件: {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂)
  结论: σ₁ = σ₂
  证明: AlgEquiv.ext fun x => φ.injective ((h₁.eq x).trans (h₂.eq x).symm)

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, injective
-/
lemma IsConj.ext {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂) : σ₁ = σ₂ :=
  AlgEquiv.ext fun x => φ.injective ((h₁.eq x).trans (h₂.eq x).symm)

/--
lemma `IsConj.ext_iff` / 引理 `IsConj.ext_iff`

English:
lemma IsConj.ext_iff
  given: {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁)
  statement: σ₁ = σ₂ ↔ IsConj φ σ₂
  proof: ⟨fun e => e ▸ h₁, h₁.ext⟩

中文:
引理 IsConj.ext_iff
  条件: {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁)
  结论: σ₁ = σ₂ ↔ IsConj φ σ₂
  证明: ⟨fun e => e ▸ h₁, h₁.ext⟩
-/
lemma IsConj.ext_iff {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) : σ₁ = σ₂ ↔ IsConj φ σ₂ :=
  ⟨fun e => e ▸ h₁, h₁.ext⟩

/--
lemma `IsConj.isReal_comp` / 引理 `IsConj.isReal_comp`

English:
lemma IsConj.isReal_comp
  given: (h : IsConj φ σ)
  statement: IsReal (φ.comp (algebraMap k K))
  proof: by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]

中文:
引理 IsConj.is实数_comp
  条件: (h : IsConj φ σ)
  结论: Is实数 (φ.comp (algebraMap k K))
  证明: by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, commutes, comp_apply, conjugate_coe_eq, h.eq, starRingEnd_apply
-/
lemma IsConj.isReal_comp (h : IsConj φ σ) : IsReal (φ.comp (algebraMap k K)) := by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]

/--
lemma `isConj_one_iff` / 引理 `isConj_one_iff`

English:
lemma isConj_one_iff
  statement: IsConj φ (1 : Gal(K/k)) ↔ IsReal φ
  proof: Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff

中文:
引理 isConj_one_iff
  结论: IsConj φ (1 : Gal(K/k)) ↔ Is实数 φ
  证明: Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff

Depends on / 依赖: Iff.rfl
-/
lemma isConj_one_iff : IsConj φ (1 : Gal(K/k)) ↔ IsReal φ := Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff

/--
lemma `isConj_ne_one_iff` / 引理 `isConj_ne_one_iff`

English:
lemma isConj_ne_one_iff
  given: (hσ : IsConj φ σ)
  proof: not_iff_not.mpr ⟨fun h => isConj_one_iff.mp (h ▸ hσ),
    fun h => (IsConj.ext_iff hσ).mpr h.isConjGal_one⟩

中文:
引理 isConj_ne_one_iff
  条件: (hσ : IsConj φ σ)
  证明: not_iff_not.mpr ⟨fun h => isConj_one_iff.mp (h ▸ hσ),
    fun h => (IsConj.ext_iff hσ).mpr h.isConjGal_one⟩

Depends on / 依赖: IsConj, IsConj.ext_iff, ext_iff, h.isConjGal_one, isConjGal_one, isConj_one_iff, isConj_one_iff.mp, not_iff_not, not_iff_not.mpr
-/
lemma isConj_ne_one_iff (hσ : IsConj φ σ) :
    σ != 1 ↔ ¬ IsReal φ :=
  not_iff_not.mpr ⟨fun h => isConj_one_iff.mp (h ▸ hσ),
    fun h => (IsConj.ext_iff hσ).mpr h.isConjGal_one⟩

/--
lemma `IsConj.symm` / 引理 `IsConj.symm`

English:
lemma IsConj.symm
  given: (hσ : IsConj φ σ)
  proof: RingHom.ext fun x => by simpa using congr_arg star (hσ.eq (σ.symm x))

中文:
引理 IsConj.symm
  条件: (hσ : IsConj φ σ)
  证明: RingHom.ext fun x => by simpa using congr_arg star (hσ.eq (σ.symm x))

Depends on / 依赖: RingHom, RingHom.ext, congr_arg
-/
lemma IsConj.symm (hσ : IsConj φ σ) :
    IsConj φ σ.symm := RingHom.ext fun x => by simpa using congr_arg star (hσ.eq (σ.symm x))

/--
lemma `isConj_symm` / 引理 `isConj_symm`

English:
lemma isConj_symm
  statement: IsConj φ σ.symm ↔ IsConj φ σ
  proof: ⟨IsConj.symm, IsConj.symm⟩

中文:
引理 isConj_symm
  结论: IsConj φ σ.symm ↔ IsConj φ σ
  证明: ⟨IsConj.symm, IsConj.symm⟩

Depends on / 依赖: IsConj, IsConj.symm
-/
lemma isConj_symm : IsConj φ σ.symm ↔ IsConj φ σ :=
  ⟨IsConj.symm, IsConj.symm⟩

/--
lemma `isConj_apply_apply` / 引理 `isConj_apply_apply`

English:
lemma isConj_apply_apply
  given: (hσ : IsConj φ σ) (x : K)
  proof: by
  simp [← φ.injective.eq_iff, hσ.eq]

中文:
引理 isConj_apply_apply
  条件: (hσ : IsConj φ σ) (x : K)
  证明: by
  simp [← φ.injective.eq_iff, hσ.eq]

Depends on / 依赖: eq_iff, injective, injective.eq_iff
-/
lemma isConj_apply_apply (hσ : IsConj φ σ) (x : K) :
    σ (σ x) = x := by
  simp [← φ.injective.eq_iff, hσ.eq]

/--
theorem `IsConj.comp` / 定理 `IsConj.comp`

English:
theorem IsConj.comp
  given: (hσ : IsConj φ σ) (ν : Gal(K/k))
  proof: by
  ext
  simpa [← AlgEquiv.mul_apply, ← mul_assoc] using! RingHom.congr_fun hσ _

中文:
定理 IsConj.comp
  条件: (hσ : IsConj φ σ) (ν : Gal(K/k))
  证明: by
  ext
  simpa [← AlgEquiv.mul_apply, ← mul_assoc] using! RingHom.congr_fun hσ _

Depends on / 依赖: AlgEquiv, AlgEquiv.mul_apply, RingHom, RingHom.congr_fun, congr_fun, mul_apply, mul_assoc
-/
theorem IsConj.comp (hσ : IsConj φ σ) (ν : Gal(K/k)) :
    IsConj (φ.comp ν) (ν⁻¹ * σ * ν) := by
  ext
  simpa [← AlgEquiv.mul_apply, ← mul_assoc] using! RingHom.congr_fun hσ _

/--
lemma `orderOf_isConj_two_of_ne_one` / 引理 `orderOf_isConj_two_of_ne_one`

English:
lemma orderOf_isConj_two_of_ne_one
  given: (hσ : IsConj φ σ) (hσ' : σ != 1)
  proof: orderOf_eq_prime_iff.mpr ⟨by ext; simpa using isConj_apply_apply hσ _, hσ'⟩

中文:
引理 orderOf_isConj_two_of_ne_one
  条件: (hσ : IsConj φ σ) (hσ' : σ != 1)
  证明: orderOf_eq_prime_iff.mpr ⟨by ext; simpa using isConj_apply_apply hσ _, hσ'⟩

Depends on / 依赖: isConj_apply_apply, orderOf_eq_prime_iff, orderOf_eq_prime_iff.mpr
-/
lemma orderOf_isConj_two_of_ne_one (hσ : IsConj φ σ) (hσ' : σ != 1) :
    orderOf σ = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simpa using isConj_apply_apply hσ _, hσ'⟩

section Extension

variable {K : Type*} {L : Type*} [Field K] [Field L] (ψ : K ->+* Complex) [Algebra K L]

/--
Definition of `LiesOver` / `LiesOver` 的定义

English:
class LiesOver
  parameters: (φ : L ->+* Complex) (ψ : K ->+* Complex)
  axioms and operations (1):
    - over((φ ψ)) : φ.comp (algebraMap K L) = ψ

中文:
类 LiesOver
  参数: (φ : L ->+* 复形) (ψ : K ->+* 复形)
  公理与运算 (1 个):
    - over((φ ψ)) : φ.comp (algebraMap K L) = ψ
-/
protected class LiesOver (φ : L ->+* Complex) (ψ : K ->+* Complex) : Prop where
  over (φ ψ) : φ.comp (algebraMap K L) = ψ

/--
theorem `LiesOver.over_apply` / 定理 `LiesOver.over_apply`

English:
theorem LiesOver.over_apply
  given: (φ : L ->+* Complex) (ψ : K ->+* Complex) [ComplexEmbedding.LiesOver φ ψ] {x : K}
  proof: RingHom.ext_iff.1 (LiesOver.over φ ψ) _

中文:
定理 LiesOver.over_apply
  条件: (φ : L ->+* 复形) (ψ : K ->+* 复形) [ComplexEmbedding.LiesOver φ ψ] {x : K}
  证明: RingHom.ext_iff.1 (LiesOver.over φ ψ) _

Depends on / 依赖: LiesOver, LiesOver.over, RingHom, RingHom.ext_iff, ext_iff
-/
theorem LiesOver.over_apply (φ : L ->+* Complex) (ψ : K ->+* Complex) [ComplexEmbedding.LiesOver φ ψ] {x : K} :
    φ (algebraMap K L x) = ψ x := RingHom.ext_iff.1 (LiesOver.over φ ψ) _

/--
theorem `liesOver_iff` / 定理 `liesOver_iff`

English:
theorem liesOver_iff
  given: {φ : L ->+* Complex} {ψ : K ->+* Complex}
  proof: ⟨fun _ => LiesOver.over φ ψ, fun h => ⟨h⟩⟩

中文:
定理 liesOver_iff
  条件: {φ : L ->+* 复形} {ψ : K ->+* 复形}
  证明: ⟨fun _ => LiesOver.over φ ψ, fun h => ⟨h⟩⟩

Depends on / 依赖: LiesOver, LiesOver.over
-/
theorem liesOver_iff {φ : L ->+* Complex} {ψ : K ->+* Complex} :
    ComplexEmbedding.LiesOver φ ψ ↔ φ.comp (algebraMap K L) = ψ :=
  ⟨fun _ => LiesOver.over φ ψ, fun h => ⟨h⟩⟩

variable (L)

/--
Definition of `Extension` / `Extension` 的定义

English:
abbreviation Extension
  body: { φ : L ->+* Complex // ComplexEmbedding.LiesOver φ ψ }

中文:
缩写 扩张
  定义体: { φ : L ->+* Complex // ComplexEmbedding.LiesOver φ ψ }
-/
protected abbrev Extension := { φ : L ->+* Complex // ComplexEmbedding.LiesOver φ ψ }

namespace Extension

variable (φ : ComplexEmbedding.Extension L ψ) {L ψ}

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  statement: φ.1.comp (algebraMap K L) = ψ
  proof: φ.2.over

中文:
定理 comp_eq
  结论: φ.1.comp (algebraMap K L) = ψ
  证明: φ.2.over
-/
theorem comp_eq : φ.1.comp (algebraMap K L) = ψ := φ.2.over

/--
theorem `conjugate_comp_ne` / 定理 `conjugate_comp_ne`

English:
theorem conjugate_comp_ne
  given: (h : ¬IsReal ψ)
  statement: (conjugate φ).comp (algebraMap K L) != ψ
  proof: by
  simp_all [ComplexEmbedding.isReal_iff, comp_eq]

中文:
定理 conjugate_comp_ne
  条件: (h : ¬Is实数 ψ)
  结论: (conjugate φ).comp (algebraMap K L) != ψ
  证明: by
  simp_all [ComplexEmbedding.isReal_iff, comp_eq]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff, comp_eq, isReal_iff
-/
theorem conjugate_comp_ne (h : ¬IsReal ψ) : (conjugate φ).comp (algebraMap K L) != ψ := by
  simp_all [ComplexEmbedding.isReal_iff, comp_eq]

/--
theorem `not_isReal_of_not_isReal` / 定理 `not_isReal_of_not_isReal`

English:
theorem not_isReal_of_not_isReal
  given: (h : ¬IsReal ψ)
  statement: ¬IsReal φ.1
  proof: mt (IsReal.comp _) (comp_eq φ ▸ h)

中文:
定理 not_is实数_of_not_is实数
  条件: (h : ¬Is实数 ψ)
  结论: ¬Is实数 φ.1
  证明: mt (IsReal.comp _) (comp_eq φ ▸ h)

Depends on / 依赖: IsReal, IsReal.comp, comp_eq
-/
theorem not_isReal_of_not_isReal (h : ¬IsReal ψ) : ¬IsReal φ.1 :=
  mt (IsReal.comp _) (comp_eq φ ▸ h)

end Extension

variable (K) {L ψ}

/--
Definition of `IsMixed` / `IsMixed` 的定义

English:
abbreviation IsMixed
  signature: (φ : L ->+* Complex)
  body: ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ∧ ¬ComplexEmbedding.IsReal φ

中文:
缩写 IsMixed
  签名: (φ : L ->+* 复形)
  定义体: ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ∧ ¬ComplexEmbedding.IsReal φ

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, IsReal, algebraMap
-/
abbrev IsMixed (φ : L ->+* Complex) :=
  ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ∧ ¬ComplexEmbedding.IsReal φ

/--
Definition of `IsUnmixed` / `IsUnmixed` 的定义

English:
abbreviation IsUnmixed
  signature: (φ : L ->+* Complex)
  body: IsReal (φ.comp (algebraMap K L)) -> IsReal φ

中文:
缩写 IsUnmixed
  签名: (φ : L ->+* 复形)
  定义体: IsReal (φ.comp (algebraMap K L)) -> IsReal φ

Depends on / 依赖: IsReal, algebraMap
-/
abbrev IsUnmixed (φ : L ->+* Complex) := IsReal (φ.comp (algebraMap K L)) -> IsReal φ

/--
theorem `IsUnmixed.isReal_iff_isReal` / 定理 `IsUnmixed.isReal_iff_isReal`

English:
theorem IsUnmixed.isReal_iff_isReal
  given: {φ : L ->+* Complex} (h : IsUnmixed K φ)
  proof: by
  aesop (add simp [IsReal.comp])

中文:
定理 IsUnmixed.is实数_iff_is实数
  条件: {φ : L ->+* 复形} (h : IsUnmixed K φ)
  证明: by
  aesop (add simp [IsReal.comp])

Depends on / 依赖: IsReal, IsReal.comp
-/
theorem IsUnmixed.isReal_iff_isReal {φ : L ->+* Complex} (h : IsUnmixed K φ) :
    IsReal (φ.comp (algebraMap K L)) ↔ IsReal φ := by
  aesop (add simp [IsReal.comp])

variable {K} (L) (ψ)

/--
Definition of `mixedEmbeddingsOver` / `mixedEmbeddingsOver` 的定义

English:
definition mixedEmbeddingsOver
  signature: : Set (L ->+* Complex)
  body: { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsMixed K φ }

中文:
定义 mixedEmbeddingsOver
  签名: : 集合 (L ->+* 复形)
  定义体: { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsMixed K φ }

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.LiesOver, IsMixed, LiesOver
-/
def mixedEmbeddingsOver : Set (L ->+* Complex) := { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsMixed K φ }
/--
Definition of `unmixedEmbeddingsOver` / `unmixedEmbeddingsOver` 的定义

English:
definition unmixedEmbeddingsOver
  signature: : Set (L ->+* Complex)
  body: { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsUnmixed K φ }

中文:
定义 unmixedEmbeddingsOver
  签名: : 集合 (L ->+* 复形)
  定义体: { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsUnmixed K φ }

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.LiesOver, IsUnmixed, LiesOver
-/
def unmixedEmbeddingsOver : Set (L ->+* Complex) := { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsUnmixed K φ }

/--
theorem `disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver` / 定理 `disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver`

English:
theorem disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver
  proof: by
  grind [mixedEmbeddingsOver, unmixedEmbeddingsOver]

中文:
定理 disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver
  证明: by
  grind [mixedEmbeddingsOver, unmixedEmbeddingsOver]

Depends on / 依赖: mixedEmbeddingsOver, unmixedEmbeddingsOver
-/
theorem disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver :
    Disjoint (unmixedEmbeddingsOver L ψ) (mixedEmbeddingsOver L ψ) := by
  grind [mixedEmbeddingsOver, unmixedEmbeddingsOver]

/--
theorem `union_unmixedEmbeddingsOver_mixedEmbeddingsOver` / 定理 `union_unmixedEmbeddingsOver_mixedEmbeddingsOver`

English:
theorem union_unmixedEmbeddingsOver_mixedEmbeddingsOver
  proof: by
  grind [unmixedEmbeddingsOver, mixedEmbeddingsOver, ← Set.ofPred_or]

中文:
定理 union_unmixedEmbeddingsOver_mixedEmbeddingsOver
  证明: by
  grind [unmixedEmbeddingsOver, mixedEmbeddingsOver, ← Set.ofPred_or]

Depends on / 依赖: Set.ofPred_or, mixedEmbeddingsOver, ofPred_or, unmixedEmbeddingsOver
-/
theorem union_unmixedEmbeddingsOver_mixedEmbeddingsOver :
    (unmixedEmbeddingsOver L ψ) union (mixedEmbeddingsOver L ψ) =
      { φ | ComplexEmbedding.LiesOver φ ψ } := by
  grind [unmixedEmbeddingsOver, mixedEmbeddingsOver, ← Set.ofPred_or]

end Extension

end NumberField.ComplexEmbedding
