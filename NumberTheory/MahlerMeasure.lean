/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Pi.Interval
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Mahler measure of integer polynomials

The main purpose of this file is to prove some facts about the Mahler measure of integer
polynomials, in particular Northcott's Theorem for the Mahler measure.

## Main results
- `Polynomial.finite_mahlerMeasure_le`: Northcott's Theorem: the set of integer polynomials of
  degree at most `n` and Mahler measure at most `B` is finite.
- `Polynomial.card_mahlerMeasure_le_prod`: an upper bound on the number of integer polynomials
  of degree at most `n` and Mahler measure at most `B`.
- `Polynomial.cyclotomic_mahlerMeasure_eq_one`: the Mahler measure of a cyclotomic polynomial is 1.
- `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`: if an integer polynomial has Mahler measure equal
  to 1, then all its complex nonzero roots are roots of unity.
- `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`: if an integer non-constant polynomial has
  Mahler measure equal to 1 and is not a multiple of X, then it is divisible by a cyclotomic
  polynomial.
-/

public section

namespace Polynomial

open Int

/--
lemma `one_le_mahlerMeasure_of_ne_zero` / 引理 `one_le_mahlerMeasure_of_ne_zero`

English:
lemma one_le_mahlerMeasure_of_ne_zero
  given: {p : Int[X]} (hp : p != 0)
  proof: by
  apply le_trans _ (p.map (castRingHom Complex)).leadingCoeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast]
  norm_cast
exact one_le_abs leadingCoeff_ne_zero.mpr hp

中文:
引理 one_le_mahlerMeasure_of_ne_zero
  条件: {p : 整数[X]} (hp : p != 0)
  证明: by
  apply le_trans _ (p.map (castRingHom Complex)).leadingCoeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast]
  norm_cast
exact one_le_abs leadingCoeff_ne_zero.mpr hp

Depends on / 依赖: castRingHom, eq_intCast, injective_int, le_trans, leadingCoeff_le_mahlerMeasure, leadingCoeff_map_of_injective, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, one_le_abs, p.map
-/
lemma one_le_mahlerMeasure_of_ne_zero {p : Int[X]} (hp : p != 0) :
    1 <= (p.map (castRingHom Complex)).mahlerMeasure := by
  apply le_trans _ (p.map (castRingHom Complex)).leadingCoeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast]
  norm_cast
exact one_le_abs leadingCoeff_ne_zero.mpr hp

section Northcott

variable (n : Nat) (B₁ B₂ : Fin (n + 1) -> Real)

/--
Definition of `boxPoly` / `boxPoly` 的定义

English:
definition boxPoly
  signature: : Set Int[X]
  body: {p : Int[X] | p.natDegree <= n ∧ forall i, B₁ i <= p.coeff i ∧ p.coeff i <= B₂ i}

中文:
定义 boxPoly
  签名: : 集合 整数[X]
  定义体: {p : Int[X] | p.natDegree <= n ∧ forall i, B₁ i <= p.coeff i ∧ p.coeff i <= B₂ i}

Depends on / 依赖: natDegree, p.coeff, p.natDegree
-/
def boxPoly : Set Int[X] := {p : Int[X] | p.natDegree <= n ∧ forall i, B₁ i <= p.coeff i ∧ p.coeff i <= B₂ i}

/--
theorem `ncard_boxPoly` / 定理 `ncard_boxPoly`

English:
theorem ncard_boxPoly
  statement: (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat
  proof: by
  trans Set.ncard (α := Fin (n + 1) -> Int) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p => ⟨toFn (n + 1) p, ?_⟩, fun p => ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i => ceil_le.mpr (prop i).1, fun i => le_floor.mpr (prop i).2⟩
· refine ⟨Nat.le_of_lt_succ ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i => ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]

@[deprecated (since := "2026-02-02")]
alias card_eq_of_natDegree_le_of_coeff_le := ncard_boxPoly

中文:
定理 ncard_boxPoly
  结论: (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).to自然数
  证明: by
  trans Set.ncard (α := Fin (n + 1) -> Int) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p => ⟨toFn (n + 1) p, ?_⟩, fun p => ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i => ceil_le.mpr (prop i).1, fun i => le_floor.mpr (prop i).2⟩
· refine ⟨Nat.le_of_lt_succ ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i => ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]

@[deprecated (since := "2026-02-02")]
alias card_eq_of_natDegree_le_of_coeff_le := ncard_boxPoly

Depends on / 依赖: Finset, Finset.Icc, Finset.mem_Icc.mp, Nat.le_add_left, Nat.le_of_lt_succ, Set.ncard, Set.ncard_congr, ceil_le, ceil_le.mp, ceil_le.mpr, le_add_left, le_floor, le_floor.mp, le_floor.mpr, le_of_lt_succ, mem_Icc, ncard_congr, ofFn_coeff_eq_val_of_lt, ofFn_natDegree_lt, p.property
-/
theorem ncard_boxPoly : (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  trans Set.ncard (α := Fin (n + 1) -> Int) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p => ⟨toFn (n + 1) p, ?_⟩, fun p => ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i => ceil_le.mpr (prop i).1, fun i => le_floor.mpr (prop i).2⟩
· refine ⟨Nat.le_of_lt_succ ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i => ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]

@[deprecated (since := "2026-02-02")]
alias card_eq_of_natDegree_le_of_coeff_le := ncard_boxPoly

open NNReal

/--
lemma `card_mahlerMeasure` / 引理 `card_mahlerMeasure`

English:
lemma card_mahlerMeasure
  given: (n : Nat) (B : Real>=0)
  proof: by
  have h_card :
      Set.ncard {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    simp_rw [norm_eq_abs, abs_le]
    rw [← boxPoly]; rw [ncard_boxPoly]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ => ?_
    zify
    rw [toNat_of_nonneg (by positivity)]; rw [← natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : Int[X] | p.natDegree <= n ∧ (p.map (Int.castRingHom Complex)).mahlerMeasure <= B} subseteq
      {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (castRingHom Complex)).coeff d‖ by aesop]
apply le_trans (p.map (castRingHom Complex)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : Int[X]| p.natDegree <= n ∧
      forall (i : Fin (n + 1)), ‖p.coeff ↑i‖ <= ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card]; rw [Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩

中文:
引理 card_mahlerMeasure
  条件: (n : 自然数) (B : 实数>=0)
  证明: by
  have h_card :
      Set.ncard {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    simp_rw [norm_eq_abs, abs_le]
    rw [← boxPoly]; rw [ncard_boxPoly]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ => ?_
    zify
    rw [toNat_of_nonneg (by positivity)]; rw [← natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : Int[X] | p.natDegree <= n ∧ (p.map (Int.castRingHom Complex)).mahlerMeasure <= B} subseteq
      {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (castRingHom Complex)).coeff d‖ by aesop]
apply le_trans (p.map (castRingHom Complex)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : Int[X]| p.natDegree <= n ∧
      forall (i : Fin (n + 1)), ‖p.coeff ↑i‖ <= ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card]; rw [Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩
-/
private lemma card_mahlerMeasure (n : Nat) (B : Real>=0) :
    Set.Finite {p : Int[X] | p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B} ∧
    Set.ncard {p : Int[X] | p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B} <=
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  have h_card :
      Set.ncard {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    simp_rw [norm_eq_abs, abs_le]
    rw [← boxPoly]; rw [ncard_boxPoly]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ => ?_
    zify
    rw [toNat_of_nonneg (by positivity)]; rw [← natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : Int[X] | p.natDegree <= n ∧ (p.map (Int.castRingHom Complex)).mahlerMeasure <= B} subseteq
      {p : Int[X] | p.natDegree <= n ∧ forall i : Fin (n + 1), ‖p.coeff i‖ <= n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (castRingHom Complex)).coeff d‖ by aesop]
apply le_trans (p.map (castRingHom Complex)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : Int[X]| p.natDegree <= n ∧
      forall (i : Fin (n + 1)), ‖p.coeff ↑i‖ <= ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card]; rw [Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩

/--
theorem `finite_mahlerMeasure_le` / 定理 `finite_mahlerMeasure_le`

English:
theorem finite_mahlerMeasure_le
  given: (n : Nat) (B : Real>=0)
  proof: (card_mahlerMeasure n B).1

中文:
定理 finite_mahlerMeasure_le
  条件: (n : 自然数) (B : 实数>=0)
  证明: (card_mahlerMeasure n B).1

Depends on / 依赖: card_mahlerMeasure
-/
theorem finite_mahlerMeasure_le (n : Nat) (B : Real>=0) :
    Set.Finite {p : Int[X] | p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B} :=
  (card_mahlerMeasure n B).1

/--
theorem `card_mahlerMeasure_le_prod` / 定理 `card_mahlerMeasure_le_prod`

English:
theorem card_mahlerMeasure_le_prod
  given: (n : Nat) (B : Real>=0)
  proof: (card_mahlerMeasure n B).2

中文:
定理 card_mahlerMeasure_le_prod
  条件: (n : 自然数) (B : 实数>=0)
  证明: (card_mahlerMeasure n B).2

Depends on / 依赖: card_mahlerMeasure
-/
theorem card_mahlerMeasure_le_prod (n : Nat) (B : Real>=0) :
    Set.ncard {p : Int[X] | p.natDegree <= n ∧ (p.map (castRingHom Complex)).mahlerMeasure <= B} <=
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := (card_mahlerMeasure n B).2

end Northcott

section Cyclotomic

/--
theorem `cyclotomic_mahlerMeasure_eq_one` / 定理 `cyclotomic_mahlerMeasure_eq_one`

English:
theorem cyclotomic_mahlerMeasure_eq_one
  given: {R : Type*} [CommRing R] [Algebra R Complex] (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  have : NeZero n := ⟨hn⟩
  suffices ∏ x in primitiveRoots n Complex, max 1 ‖x‖ = 1 by
    simpa [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n Complex,
      Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  suffices forall x in primitiveRoots n Complex, ‖x‖ <= 1 from Multiset.prod_eq_one (by simpa)
  intro _ hz
  exact (IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn).le

中文:
定理 cyclotomic_mahlerMeasure_eq_one
  条件: {R : 类型} [交换环 R] [代数 R 复形] (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  have : NeZero n := ⟨hn⟩
  suffices ∏ x in primitiveRoots n Complex, max 1 ‖x‖ = 1 by
    simpa [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n Complex,
      Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  suffices forall x in primitiveRoots n Complex, ‖x‖ <= 1 from Multiset.prod_eq_one (by simpa)
  intro _ hz
  exact (IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn).le

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.norm, Multiset, Multiset.prod_eq_one, NeZero, Polynomial, Polynomial.cyclotomic.roots_eq_primitiveRoots_val, _eq_one, cyclotomic, cyclotomic.monic, eq_or_ne, isPrimitiveRoot_of_mem_primitiveRoots, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, primitiveRoots, prod_eq_one, roots_eq_primitiveRoots_val
-/
theorem cyclotomic_mahlerMeasure_eq_one {R : Type*} [CommRing R] [Algebra R Complex] (n : Nat) :
    ((cyclotomic n R).map (algebraMap R Complex)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  have : NeZero n := ⟨hn⟩
  suffices ∏ x in primitiveRoots n Complex, max 1 ‖x‖ = 1 by
    simpa [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n Complex,
      Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  suffices forall x in primitiveRoots n Complex, ‖x‖ <= 1 from Multiset.prod_eq_one (by simpa)
  intro _ hz
  exact (IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn).le

variable {p : Int[X]} (h : (p.map (castRingHom Complex)).mahlerMeasure = 1)

include h in
/--
lemma `norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one` / 引理 `norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one`

English:
lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
  proof: by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := h ▸ (leadingCoeff_le_mahlerMeasure <| p.map (castRingHom Complex))
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in

中文:
引理 norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
  证明: by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := h ▸ (leadingCoeff_le_mahlerMeasure <| p.map (castRingHom Complex))
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in

Depends on / 依赖: castRingHom, eq_intCast, eq_or_ne, h_ineq, injective_int, leadingCoeff_eq_zero, leadingCoeff_le_mahlerMeasure, leadingCoeff_map_of_injective, p.map
-/
lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one :
    ‖(p.map (castRingHom Complex)).leadingCoeff‖ = 1 := by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := h ▸ (leadingCoeff_le_mahlerMeasure <| p.map (castRingHom Complex))
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in
/--
lemma `abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one` / 引理 `abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one`

English:
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
  statement: |p.leadingCoeff| = 1
  proof: by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at this
  norm_cast at this

中文:
引理 abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
  结论: |p.leadingCoeff| = 1
  证明: by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at this
  norm_cast at this

Depends on / 依赖: castRingHom, eq_intCast, injective_int, leadingCoeff_map_of_injective, norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
-/
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1 := by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective (castRingHom Complex).injective_int]; rw [eq_intCast] at this
  norm_cast at this

variable {z : Complex} (hz₀ : z != 0) (hz : z in p.aroots Complex)

include hz h in
/--
theorem `isIntegral_of_mahlerMeasure_eq_one` / 定理 `isIntegral_of_mahlerMeasure_eq_one`

English:
theorem isIntegral_of_mahlerMeasure_eq_one
  statement: IsIntegral Int z
  proof: by
have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp
    abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

中文:
定理 is整数egral_of_mahlerMeasure_eq_one
  结论: 是整 整数 z
  证明: by
have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp
    abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

Depends on / 依赖: IsIntegral, IsIntegralElem, IsRoot, IsRoot.def, Monic.def, RingHom, RingHom.IsIntegralElem, abs_eq_abs, abs_eq_abs.mp, abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one, eval_map, leadingCoeff, mem_roots, p.leadingCoeff
-/
theorem isIntegral_of_mahlerMeasure_eq_one : IsIntegral Int z := by
have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp
    abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

set_option linter.style.whitespace false in -- manual alignment is not recognised
open Multiset in
include h hz in
/--
lemma `norm_root_le_one_of_mahlerMeasure_eq_one` / 引理 `norm_root_le_one_of_mahlerMeasure_eq_one`

English:
lemma norm_root_le_one_of_mahlerMeasure_eq_one
  statement: ‖z‖ <= 1
  proof: by
  calc
  ‖z‖ <= max 1 ‖z‖ := le_max_right 1 ‖z‖
  _ <= ((p.map (castRingHom Complex)).roots.map (fun a => max 1 ‖a‖)).prod :=
        mem_le_prod_of_one_le (fun a => le_max_left 1 ‖a‖) hz
  _ <= 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]

中文:
引理 norm_root_le_one_of_mahlerMeasure_eq_one
  结论: ‖z‖ <= 1
  证明: by
  calc
  ‖z‖ <= max 1 ‖z‖ := le_max_right 1 ‖z‖
  _ <= ((p.map (castRingHom Complex)).roots.map (fun a => max 1 ‖a‖)).prod :=
        mem_le_prod_of_one_le (fun a => le_max_left 1 ‖a‖) hz
  _ <= 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]

Depends on / 依赖: castRingHom, le_max_left, le_max_right, mem_le_prod_of_one_le, norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one, p.map, prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff, roots.map
-/
lemma norm_root_le_one_of_mahlerMeasure_eq_one : ‖z‖ <= 1 := by
  calc
  ‖z‖ <= max 1 ‖z‖ := le_max_right 1 ‖z‖
  _ <= ((p.map (castRingHom Complex)).roots.map (fun a => max 1 ‖a‖)).prod :=
        mem_le_prod_of_one_le (fun a => le_max_left 1 ‖a‖) hz
  _ <= 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]

open IntermediateField in
include hz₀ hz h in
/--
theorem `pow_eq_one_of_mahlerMeasure_eq_one` / 定理 `pow_eq_one_of_mahlerMeasure_eq_one`

English:
theorem pow_eq_one_of_mahlerMeasure_eq_one
  statement: exists n, 0 < n ∧ z ^ n = 1
  proof: by

中文:
定理 pow_eq_one_of_mahlerMeasure_eq_one
  结论: 存在 n, 0 < n ∧ z ^ n = 1
  证明: by
-/
theorem pow_eq_one_of_mahlerMeasure_eq_one : exists n, 0 < n ∧ z ^ n = 1 := by
/- We want to use `NumberField.Embeddings.pow_eq_one_of_norm_le_one` but it can only be applied to
elements of number fields. We thus first construct the number field `K` obtained by adjoining `z`
to `ℚ`.
-/
  let K := Rat⟮z⟯
  let : NumberField K := {
    to_charZero := Rat⟮z⟯.charZero,
    to_finiteDimensional := adjoin.finiteDimensional
      (isIntegral_of_mahlerMeasure_eq_one h hz).tower_top }
-- `y` is `z` as an element of `K`
  let y : K := ⟨z, mem_adjoin_simple_self Rat z⟩
  suffices exists (n : Nat) (_ : 0 < n), y ^ n = 1 by
    obtain ⟨n, hn₀, hn₁⟩ := this
    exact ⟨n, hn₀, congrArg (algebraMap K Complex) hn₁⟩
  refine NumberField.Embeddings.pow_eq_one_of_norm_le_one (x := y) K Complex (Subtype.coe_ne_coe.mp hz₀)
    (coe_isIntegral_iff.mp <| isIntegral_of_mahlerMeasure_eq_one h hz)
    fun φ => norm_root_le_one_of_mahlerMeasure_eq_one h ?_
  rw [mem_aroots] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have H (ψ : K ->+* Complex) : ψ ((aeval y) p) = (aeval (ψ y)) p := by
    conv_rhs => rw [← map_id (p := p)]
    exact p.map_aeval_eq_aeval_map (by ext; simp) y
  rw [← H]; rw [map_eq_zero_iff _ φ.injective]; rw [← map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ↥K Complex)]; rw [H]
  exact hz.2

include h hz₀ hz in
/--
theorem `isPrimitiveRoot_of_mahlerMeasure_eq_one` / 定理 `isPrimitiveRoot_of_mahlerMeasure_eq_one`

English:
theorem isPrimitiveRoot_of_mahlerMeasure_eq_one
  statement: exists n, 0 < n ∧ IsPrimitiveRoot z n
  proof: by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

include h in

中文:
定理 isPrimitiveRoot_of_mahlerMeasure_eq_one
  结论: 存在 n, 0 < n ∧ 是PrimitiveRoot z n
  证明: by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

include h in

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.exists_pos, exists_pos, hz_pow, pow_eq_one_of_mahlerMeasure_eq_one
-/
theorem isPrimitiveRoot_of_mahlerMeasure_eq_one : exists n, 0 < n ∧ IsPrimitiveRoot z n := by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

include h in
/--
theorem `cyclotomic_dvd_of_mahlerMeasure_eq_one` / 定理 `cyclotomic_dvd_of_mahlerMeasure_eq_one`

English:
theorem cyclotomic_dvd_of_mahlerMeasure_eq_one
  given: (hX : ¬ X ∣ p) (hpdeg : p.degree != 0)
  proof: by
  have hpdegC : (p.map (castRingHom Complex)).degree != 0 := by
    rwa [p.degree_map_eq_of_injective (castRingHom Complex).injective_int]
  obtain ⟨z, _⟩ := Splits.exists_eval_eq_zero (IsAlgClosed.splits <| p.map (castRingHom Complex))
    hpdegC
  have hz₀ : z != 0 := by
    contrapose hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z in p.aroots Complex := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [cyclotomic_eq_minpoly h_prim h_m_pos]
apply minpoly.isIntegrallyClosed_dvd isIntegral_of_mahlerMeasure_eq_one h h_z_root
  exact (mem_aroots.mp h_z_root).2

中文:
定理 cyclotomic_dvd_of_mahlerMeasure_eq_one
  条件: (hX : ¬ X ∣ p) (hpdeg : p.degree != 0)
  证明: by
  have hpdegC : (p.map (castRingHom Complex)).degree != 0 := by
    rwa [p.degree_map_eq_of_injective (castRingHom Complex).injective_int]
  obtain ⟨z, _⟩ := Splits.exists_eval_eq_zero (IsAlgClosed.splits <| p.map (castRingHom Complex))
    hpdegC
  have hz₀ : z != 0 := by
    contrapose hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z in p.aroots Complex := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [cyclotomic_eq_minpoly h_prim h_m_pos]
apply minpoly.isIntegrallyClosed_dvd isIntegral_of_mahlerMeasure_eq_one h h_z_root
  exact (mem_aroots.mp h_z_root).2

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, Splits, Splits.exists_eval_eq_zero, X_dvd_iff, aroots, castRingHom, coeff_zero_eq_aeval_zero, contrapose, cyclotomic_eq_minpoly, degree, degree_map_eq_of_injective, exists_eval_eq_zero, h_m_pos, h_prim, h_z_root, hpdegC, injective_int, isPrimitiveRoot_of_mahlerMeasure_eq_one, p.aroots
-/
theorem cyclotomic_dvd_of_mahlerMeasure_eq_one (hX : ¬ X ∣ p) (hpdeg : p.degree != 0) :
    exists n, 0 < n ∧ cyclotomic n Int ∣ p := by
  have hpdegC : (p.map (castRingHom Complex)).degree != 0 := by
    rwa [p.degree_map_eq_of_injective (castRingHom Complex).injective_int]
  obtain ⟨z, _⟩ := Splits.exists_eval_eq_zero (IsAlgClosed.splits <| p.map (castRingHom Complex))
    hpdegC
  have hz₀ : z != 0 := by
    contrapose hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z in p.aroots Complex := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [cyclotomic_eq_minpoly h_prim h_m_pos]
apply minpoly.isIntegrallyClosed_dvd isIntegral_of_mahlerMeasure_eq_one h h_z_root
  exact (mem_aroots.mp h_z_root).2

end Cyclotomic

end Polynomial
