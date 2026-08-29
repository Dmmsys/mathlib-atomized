/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Birkhoff's theorem

## Main statements

* `doublyStochastic_eq_sum_perm`: If `M` is a doubly stochastic matrix, then it is a convex
  combination of permutation matrices.
* `doublyStochastic_eq_convexHull_perm`: The set of doubly stochastic matrices is the convex hull
  of the permutation matrices.
* `extremePoints_doublyStochastic`: The set of extreme points of the doubly stochastic matrices is
  the set of permutation matrices.

## TODO

* Show that for `x y : n → R`, `x` is majorized by `y` if and only if there is a doubly stochastic
  matrix `M` such that `M *ᵥ y = x`.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

public section

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_perm_eq_zero_implies_eq_zero` / 引理 `exists_perm_eq_zero_implies_eq_zero`

English:
lemma exists_perm_eq_zero_implies_eq_zero
  statement: {s : R} (hs : 0 < s)
  proof: by
  rw [exists_mem_doublyStochastic_eq_smul_iff hs.le] at hM
  let f (i : n) : Finset n := {j | M i j != 0}
  have hf (A : Finset n) : #A <= #(A.biUnion f) := by
    have (i : _) : ∑ j in f i, M i j = s := by simp [f, sum_subset (filter_subset _ _), hM.2.1]
    have h₁ : ∑ i in A, ∑ j in f i, M i j

中文:
引理 存在_perm_eq_zero_implies_eq_zero
  结论: {s : R} (hs : 0 < s)
  证明: by
  rw [exists_mem_doublyStochastic_eq_smul_iff hs.le] at hM
  let f (i : n) : Finset n := {j | M i j != 0}
  have hf (A : Finset n) : #A <= #(A.biUnion f) := by
    have (i : _) : ∑ j in f i, M i j = s := by simp [f, sum_subset (filter_subset _ _), hM.2.1]
    have h₁ : ∑ i in A, ∑ j in f i, M i j
-/
private lemma exists_perm_eq_zero_implies_eq_zero {s : R} (hs : 0 < s)
    (hM : exists M' in doublyStochastic R n, M = s • M') :
    exists σ : Equiv.Perm n, forall i j, M i j = 0 -> σ.permMatrix R i j = 0 := by
  rw [exists_mem_doublyStochastic_eq_smul_iff hs.le] at hM
  let f (i : n) : Finset n := {j | M i j != 0}
  have hf (A : Finset n) : #A <= #(A.biUnion f) := by
    have (i : _) : ∑ j in f i, M i j = s := by simp [f, sum_subset (filter_subset _ _), hM.2.1]
    have h₁ : ∑ i in A, ∑ j in f i, M i j = #A * s := by simp [this]
    have h₂ : ∑ i, ∑ j in A.biUnion f, M i j = #(A.biUnion f) * s := by
      simp [sum_comm (t := A.biUnion f), hM.2.2]
    suffices #A * s <= #(A.biUnion f) * s by exact_mod_cast le_of_mul_le_mul_right this hs
    rw [← h₁]; rw [← h₂]
    trans ∑ i in A, ∑ j in A.biUnion f, M i j
    · refine sum_le_sum fun i hi => ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_biUnion_of_mem f hi) (by simp [*])
    · exact sum_le_sum_of_subset_of_nonneg (by simp) fun _ _ _ => sum_nonneg fun j _ => hM.1 _ _
  obtain ⟨g, hg, hg'⟩ := (all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, fun i j hij => ?_⟩
  simp only [PEquiv.toMatrix_apply, Option.mem_def, ite_eq_right_iff, one_ne_zero, imp_false,
    Equiv.toPEquiv_apply, Equiv.ofBijective_apply, Option.some.injEq]
  rintro rfl
  simpa [f, hij] using hg' i

end LinearOrderedSemifield

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

/--
lemma `doublyStochastic_sum_perm_aux` / 引理 `doublyStochastic_sum_perm_aux`

English:
lemma doublyStochastic_sum_perm_aux
  statement: (M : Matrix n n R)
  proof: by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : Nat := #{i : n × n | M i.1 i.2 != 0} with ← hd
  clear_value d
  induction d using Nat.strongRecOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    use 0

中文:
引理 doublyStochastic_sum_perm_aux
  结论: (M : 矩阵 n n R)
  证明: by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : Nat := #{i : n × n | M i.1 i.2 != 0} with ← hd
  clear_value d
  induction d using Nat.strongRecOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    use 0
-/
private lemma doublyStochastic_sum_perm_aux (M : Matrix n n R)
    (s : R) (hs : 0 <= s)
    (hM : exists M' in doublyStochastic R n, M = s • M') :
    exists w : Equiv.Perm n -> R, (forall σ, 0 <= w σ) ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : Nat := #{i : n × n | M i.1 i.2 != 0} with ← hd
  clear_value d
  induction d using Nat.strongRecOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    use 0
    simp only [zero_smul, exists_and_right] at hM
    simp [hM]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_zero_implies_eq_zero hs' hM
  obtain ⟨i, hi, hi'⟩ := exists_min_image _ (fun i => M i (σ i)) univ_nonempty
  rw [exists_mem_doublyStochastic_eq_smul_iff hs] at hM
  let N : Matrix n n R := M - M i (σ i) • σ.permMatrix R
  have hMi' : 0 < M i (σ i) := (hM.1 _ _).lt_of_ne' fun h => by
    simpa [Equiv.toPEquiv_apply] using hσ _ _ h
  let s' : R := s - M i (σ i)
  have hs' : 0 <= s' := by
    simp only [s', sub_nonneg, ← hM.2.1 i]
    exact single_le_sum (fun j _ => hM.1 i j) (by simp)
  have : exists M' in doublyStochastic R n, N = s' • M' := by
    rw [exists_mem_doublyStochastic_eq_smul_iff hs']
    simp only [Matrix.sub_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_nonneg,
      sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, N]
    refine ⟨fun i' j => ?_, by simp [s', hM.2.1], by simp [s', ← σ.eq_symm_apply, hM]⟩
    split
    case isTrue h => exact (hi' i' (by simp)).trans_eq (by rw [h])
    case isFalse h => exact hM.1 _ _
  have hd' : #{i : n × n | N i.1 i.2 != 0} < d := by
    rw [← hd]
    gcongr
    rw [ssubset_iff_of_subset (monotone_filter_right _ _)]
    · simp_rw [mem_filter_univ, not_not, Prod.exists]
      exact ⟨i, σ i, hMi'.ne', by simp [N, Equiv.toPEquiv_apply]⟩
    · rintro ⟨i', j'⟩ _ hN' hM'
      have hσ' : σ i' != j' := by
        simpa [Equiv.toPEquiv_apply] using hσ i' j' hM'
exact hN' by simp [N, hM', hσ', Equiv.toPEquiv_apply]
  obtain ⟨w, hw, hw'⟩ := ih _ hd' _ s' hs' this rfl
  refine ⟨w + fun σ' => if σ' = σ then M i (σ i) else 0, ?_⟩
  simp only [Pi.add_apply, add_smul, sum_add_distrib, hw', ite_smul, zero_smul,
    sum_ite_eq', mem_univ, ↓reduceIte, N, sub_add_cancel, and_true]
  intro σ'
  split <;> simp [add_nonneg, hw, hM.1]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_eq_sum_perm_of_mem_doublyStochastic` / 引理 `exists_eq_sum_perm_of_mem_doublyStochastic`

English:
lemma exists_eq_sum_perm_of_mem_doublyStochastic
  given: (hM : M in doublyStochastic R n)
  proof: by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm_aux M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • σ.permMatrix R default j =

中文:
引理 存在_eq_sum_perm_of_mem_doublyStochastic
  条件: (hM : M in doublyStochastic R n)
  证明: by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm_aux M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • σ.permMatrix R default j =

Depends on / 依赖: Equiv.Perm, Equiv.toPEquiv_apply, Finset, Finset.sum_apply, Subsingleton, Subsingleton.elim, doublyStochastic_sum_perm_aux, inhabit, isEmpty_or_nonempty, permMatrix, smul_apply, sum_apply, sum_comm, sum_row_of_mem_doublyStochastic, toPEquiv_apply
-/
lemma exists_eq_sum_perm_of_mem_doublyStochastic (hM : M in doublyStochastic R n) :
    exists w : Equiv.Perm n -> R, (forall σ, 0 <= w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm_aux M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • σ.permMatrix R default j = 1 := by
    simp only [← smul_apply (m := n), ← Finset.sum_apply, hw3]
    rw [sum_row_of_mem_doublyStochastic hM]
  simpa [sum_comm (γ := n), Equiv.toPEquiv_apply] using this

/--
theorem `doublyStochastic_eq_convexHull_permMatrix` / 定理 `doublyStochastic_eq_convexHull_permMatrix`

English:
theorem doublyStochastic_eq_convexHull_permMatrix
  proof: by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' fun M hM => ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_mem_doublyStochastic
  case g2 =>
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    exact mem_convexHull_of_exists_fintype w (·.

中文:
定理 doublyStochastic_eq_convexHull_permMatrix
  证明: by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' fun M hM => ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_mem_doublyStochastic
  case g2 =>
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    exact mem_convexHull_of_exists_fintype w (·.

Depends on / 依赖: antisymm, convexHull_min, convex_doublyStochastic, exists_eq_sum_perm_of_mem_doublyStochastic, mem_convexHull_of_exists_fintype, permMatrix, permMatrix_mem_doublyStochastic
-/
theorem doublyStochastic_eq_convexHull_permMatrix :
    doublyStochastic R n = convexHull R {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' fun M hM => ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_mem_doublyStochastic
  case g2 =>
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    exact mem_convexHull_of_exists_fintype w (·.permMatrix R) hw1 hw2 (by simp) hw3

/--
theorem `extremePoints_doublyStochastic` / 定理 `extremePoints_doublyStochastic`

English:
theorem extremePoints_doublyStochastic
  proof: by
  refine subset_antisymm ?_ ?_
  · rw [doublyStochastic_eq_convexHull_permMatrix]
    exact extremePoints_convexHull_subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨permMatrix_mem_doublyStochastic, fun x₁ hx₁ x₂ hx₂ hσ => ?_⟩
  suffices forall i j : n, x₁ i j = x₂ i j by
    obtain rfl : x₁ = x₂ := by simpa

中文:
定理 extremePoints_doublyStochastic
  证明: by
  refine subset_antisymm ?_ ?_
  · rw [doublyStochastic_eq_convexHull_permMatrix]
    exact extremePoints_convexHull_subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨permMatrix_mem_doublyStochastic, fun x₁ hx₁ x₂ hx₂ hσ => ?_⟩
  suffices forall i j : n, x₁ i j = x₂ i j by
    obtain rfl : x₁ = x₂ := by simpa

Depends on / 依赖: Matrix, Matrix.ext_iff, doublyStochastic_eq_convexHull_permMatrix, entryLinearMap, ext_iff, extremePoints_convexHull_subset, image_openSegment, openSegment, permMatrix, permMatrix_mem_doublyStochastic, subset_antisymm, toAffineMap
-/
theorem extremePoints_doublyStochastic :
    Set.extremePoints R (doublyStochastic R n) = {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine subset_antisymm ?_ ?_
  · rw [doublyStochastic_eq_convexHull_permMatrix]
    exact extremePoints_convexHull_subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨permMatrix_mem_doublyStochastic, fun x₁ hx₁ x₂ hx₂ hσ => ?_⟩
  suffices forall i j : n, x₁ i j = x₂ i j by
    obtain rfl : x₁ = x₂ := by simpa [← Matrix.ext_iff]
    simp_all
  intro i j
  have h₁ : σ.permMatrix R i j in openSegment R (x₁ i j) (x₂ i j) :=
    image_openSegment _ (entryLinearMap R R i j).toAffineMap x₁ x₂ ▸ ⟨_, hσ, rfl⟩
  by_contra! h
  have h₂ : openSegment R (x₁ i j) (x₂ i j) subseteq Set.Ioo 0 1 := by
    rw [openSegment_eq_Ioo' h]
    apply Set.Ioo_subset_Ioo <;>
    simp_all [nonneg_of_mem_doublyStochastic, le_one_of_mem_doublyStochastic]
  specialize h₂ h₁
  aesop

end LinearOrderedField

open scoped Matrix.Norms.L2Operator

/--
theorem `Matrix.l2_opNorm_le_one_of_mem_doublyStochastic` / 定理 `Matrix.l2_opNorm_le_one_of_mem_doublyStochastic`

English:
theorem Matrix.l2_opNorm_le_one_of_mem_doublyStochastic
  statement: {M : Matrix n n Real}
  proof: by
  rw [← SetLike.mem_coe]; rw [doublyStochastic_eq_convexHull_permMatrix] at hM
  have ⟨_, ⟨σ, rfl⟩, hσ⟩ := convexOn_univ_norm.exists_ge_of_mem_convexHull (by simp) hM
  exact hσ.trans (permMatrix_l2_opNorm_le _)

中文:
定理 矩阵.l2_opNorm_le_one_of_mem_doublyStochastic
  结论: {M : 矩阵 n n 实数}
  证明: by
  rw [← SetLike.mem_coe]; rw [doublyStochastic_eq_convexHull_permMatrix] at hM
  have ⟨_, ⟨σ, rfl⟩, hσ⟩ := convexOn_univ_norm.exists_ge_of_mem_convexHull (by simp) hM
  exact hσ.trans (permMatrix_l2_opNorm_le _)

Depends on / 依赖: SetLike, SetLike.mem_coe, convexOn_univ_norm, convexOn_univ_norm.exists_ge_of_mem_convexHull, doublyStochastic_eq_convexHull_permMatrix, exists_ge_of_mem_convexHull, mem_coe, permMatrix_l2_opNorm_le
-/
theorem Matrix.l2_opNorm_le_one_of_mem_doublyStochastic {M : Matrix n n Real}
    (hM : M in doublyStochastic Real n) :
    ‖M‖ <= 1 := by
  rw [← SetLike.mem_coe]; rw [doublyStochastic_eq_convexHull_permMatrix] at hM
  have ⟨_, ⟨σ, rfl⟩, hσ⟩ := convexOn_univ_norm.exists_ge_of_mem_convexHull (by simp) hM
  exact hσ.trans (permMatrix_l2_opNorm_le _)
