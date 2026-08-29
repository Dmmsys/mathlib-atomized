/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `Matrix.det`, and its essential properties.

## Main definitions

- `Matrix.det`: the determinant of a square matrix, as a sum over permutations
- `Matrix.detRowAlternating`: the determinant, as an `AlternatingMap` in the rows of the matrix

## Main results

- `det_mul`: the determinant of `A * B` is the product of determinants
- `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
- `det_block_diagonal`: the determinant of a block diagonal matrix is a product
  of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`MathlibTest/matrix.lean` for some examples.

-/

@[expose] public section


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : Int) : R)

/--
Definition of `detRowAlternating` / `detRowAlternating` 的定义

English:
definition detRowAlternating
  signature: : (n -> R) [⋀^n]->ₗ[R] R
  body: MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

中文:
定义 detRowAlternating
  签名: : (n -> R) [⋀^n]->ₗ[R] R
  定义体: MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

Depends on / 依赖: LinearMap, LinearMap.proj, MultilinearMap, MultilinearMap.alternatization, MultilinearMap.mkPiAlgebra, alternatization, compLinearMap, mkPiAlgebra
-/
def detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

/-- The determinant of a matrix given by the Leibniz formula. -/
@[wikidata Q178546]
/--
Definition of `det` / `det` 的定义

English:
definition det
  signature: (M : Matrix n n R)
  body: detRowAlternating M

中文:
定义 det
  签名: (M : 矩阵 n n R)
  定义体: detRowAlternating M

Depends on / 依赖: detRowAlternating
-/
def det (M : Matrix n n R) : R :=
  detRowAlternating M

/--
theorem `det_apply` / 定理 `det_apply`

English:
theorem det_apply
  given: (M : Matrix n n R)
  statement: M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i
  proof: MultilinearMap.alternatization_apply _ M

中文:
定理 det_apply
  条件: (M : 矩阵 n n R)
  结论: M.det = ∑ σ : 置换 n, 等价.置换.sign σ • ∏ i, M (σ i) i
  证明: MultilinearMap.alternatization_apply _ M

Depends on / 依赖: MultilinearMap, MultilinearMap.alternatization_apply, alternatization_apply
-/
theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below
/--
theorem `det_apply'` / 定理 `det_apply'`

English:
theorem det_apply'
  given: (M : Matrix n n R)
  statement: M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i
  proof: by
  simp [det_apply, Units.smul_def]

中文:
定理 det_apply'
  条件: (M : 矩阵 n n R)
  结论: M.det = ∑ σ : 置换 n, ε σ * ∏ i, M (σ i) i
  证明: by
  simp [det_apply, Units.smul_def]

Depends on / 依赖: Units.smul_def, det_apply, smul_def
-/
theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [det_apply, Units.smul_def]

/--
theorem `det_eq_detp_sub_detp` / 定理 `det_eq_detp_sub_detp`

English:
theorem det_eq_detp_sub_detp
  given: (M : Matrix n n R)
  statement: M.det = M.detp 1 - M.detp (-1)
  proof: by
  rw [det_apply]; rw [← Equiv.sum_comp (Equiv.inv (Perm n))]; rw [← ofSign_disjUnion]; rw [sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (sum_congr rfl fun σ hσ => ?_) <;>
    rw [mem_ofSign.mp hσ

中文:
定理 det_eq_detp_sub_detp
  条件: (M : 矩阵 n n R)
  结论: M.det = M.detp 1 - M.detp (-1)
  证明: by
  rw [det_apply]; rw [← Equiv.sum_comp (Equiv.inv (Perm n))]; rw [← ofSign_disjUnion]; rw [sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (sum_congr rfl fun σ hσ => ?_) <;>
    rw [mem_ofSign.mp hσ

Depends on / 依赖: Equiv.inv, Equiv.prod_comp, Equiv.sum_comp, det_apply, inv_apply, mem_ofSign, mem_ofSign.mp, ofSign_disjUnion, prod_comp, sign_inv, simp_rw, sub_eq_add_neg, sum_comp, sum_congr, sum_disjUnion, sum_neg_distrib
-/
theorem det_eq_detp_sub_detp (M : Matrix n n R) : M.det = M.detp 1 - M.detp (-1) := by
  rw [det_apply]; rw [← Equiv.sum_comp (Equiv.inv (Perm n))]; rw [← ofSign_disjUnion]; rw [sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (sum_congr rfl fun σ hσ => ?_) <;>
    rw [mem_ofSign.mp hσ]; rw [← Equiv.prod_comp σ] <;> simp

@[simp]
/--
theorem `det_diagonal` / 定理 `det_diagonal`

English:
theorem det_diagonal
  given: {d : n -> R}
  statement: det (diagonal d) = ∏ i, d i
  proof: by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert! mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

中文:
定理 det_diagonal
  条件: {d : n -> R}
  结论: det (diagonal d) = ∏ i, d i
  证明: by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert! mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

Depends on / 依赖: Equiv.ext, Finset, Finset.prod_eq_zero, Finset.sum_eq_single, convert, det_apply, if_neg, mem_univ, mul_zero, not_forall, prod_eq_zero, sum_eq_single
-/
theorem det_diagonal {d : n -> R} : det (diagonal d) = ∏ i, d i := by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert! mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

/--
theorem `det_zero` / 定理 `det_zero`

English:
theorem det_zero
  given: [Nonempty n]
  statement: det (0 : Matrix n n R) = 0
  proof: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_zero

@[simp]

中文:
定理 det_zero
  条件: [非空 n]
  结论: det (0 : 矩阵 n n R) = 0
  证明: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_zero

@[simp]
-/
@[simp] theorem det_zero [Nonempty n] : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_zero

@[simp]
/--
theorem `det_one` / 定理 `det_one`

English:
theorem det_one
  statement: det (1 : Matrix n n R) = 1
  proof: by rw [← diagonal_one]; simp [-diagonal_one]

中文:
定理 det_one
  结论: det (1 : 矩阵 n n R) = 1
  证明: by rw [← diagonal_one]; simp [-diagonal_one]

Depends on / 依赖: diagonal_one
-/
theorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

/--
theorem `det_isEmpty` / 定理 `det_isEmpty`

English:
theorem det_isEmpty
  given: [IsEmpty n] {A : Matrix n n R}
  statement: det A = 1
  proof: by simp [det_apply]

@[simp]

中文:
定理 det_isEmpty
  条件: [是空 n] {A : 矩阵 n n R}
  结论: det A = 1
  证明: by simp [det_apply]

@[simp]

Depends on / 依赖: det_apply
-/
theorem det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by simp [det_apply]

@[simp]
/--
theorem `coe_det_isEmpty` / 定理 `coe_det_isEmpty`

English:
theorem coe_det_isEmpty
  given: [IsEmpty n]
  statement: (det : Matrix n n R -> R) = Function.const _ 1
  proof: by
  ext
  exact det_isEmpty

中文:
定理 coe_det_isEmpty
  条件: [是空 n]
  结论: (det : 矩阵 n n R -> R) = 函数.const _ 1
  证明: by
  ext
  exact det_isEmpty

Depends on / 依赖: det_isEmpty
-/
theorem coe_det_isEmpty [IsEmpty n] : (det : Matrix n n R -> R) = Function.const _ 1 := by
  ext
  exact det_isEmpty

/--
theorem `det_eq_one_of_card_eq_zero` / 定理 `det_eq_one_of_card_eq_zero`

English:
theorem det_eq_one_of_card_eq_zero
  given: {A : Matrix n n R} (h : Fintype.card n = 0)
  statement: det A = 1
  proof: haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty

中文:
定理 det_eq_one_of_card_eq_zero
  条件: {A : 矩阵 n n R} (h : 有限类型.card n = 0)
  结论: det A = 1
  证明: haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff.mp, IsEmpty, card_eq_zero_iff, det_isEmpty
-/
theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 :=
  haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
/--
theorem `det_unique` / 定理 `det_unique`

English:
theorem det_unique
  given: {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R)
  proof: by simp [det_apply, univ_unique]

中文:
定理 det_unique
  条件: {n : 类型} [唯一 n] [DecidableEq n] [有限类型 n] (A : 矩阵 n n R)
  证明: by simp [det_apply, univ_unique]

Depends on / 依赖: det_apply, univ_unique
-/
theorem det_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    det A = A default default := by simp [det_apply, univ_unique]

/--
theorem `det_eq_elem_of_subsingleton` / 定理 `det_eq_elem_of_subsingleton`

English:
theorem det_eq_elem_of_subsingleton
  given: [Subsingleton n] (A : Matrix n n R) (k : n)
  proof: by
  have := uniqueOfSubsingleton k
  convert! det_unique A

中文:
定理 det_eq_elem_of_subsingleton
  条件: [子单例 n] (A : 矩阵 n n R) (k : n)
  证明: by
  have := uniqueOfSubsingleton k
  convert! det_unique A

Depends on / 依赖: convert, det_unique, uniqueOfSubsingleton
-/
theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    det A = A k k := by
  have := uniqueOfSubsingleton k
  convert! det_unique A

/--
theorem `det_eq_elem_of_card_eq_one` / 定理 `det_eq_elem_of_card_eq_one`

English:
theorem det_eq_elem_of_card_eq_one
  given: {A : Matrix n n R} (h : Fintype.card n = 1) (k : n)
  proof: haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _

中文:
定理 det_eq_elem_of_card_eq_one
  条件: {A : 矩阵 n n R} (h : 有限类型.card n = 1) (k : n)
  证明: haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _

Depends on / 依赖: Fintype, Fintype.card_le_one_iff_subsingleton.mp, Subsingleton, card_le_one_iff_subsingleton, det_eq_elem_of_subsingleton, h.le
-/
theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    det A = A k k :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _

/--
theorem `det_mul_aux` / 定理 `det_mul_aux`

English:
theorem det_mul_aux
  given: {M N : Matrix n n R} {p : n -> n} (H : ¬Bijective p)
  proof: by
  obtain ⟨i, j, hpij, hij⟩ : exists i j, p i = p j ∧ i != j := by
    rw [← Finite.injective_iff_bijective]; rw [Injective] at H
    push Not at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.s

中文:
定理 det_mul_aux
  条件: {M N : 矩阵 n n R} {p : n -> n} (H : ¬双射 p)
  证明: by
  obtain ⟨i, j, hpij, hij⟩ : exists i j, p i = p j ∧ i != j := by
    rw [← Finite.injective_iff_bijective]; rw [Injective] at H
    push Not at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.s

Depends on / 依赖: Equiv.swap, Finite, Finite.injective_iff_bijective, Fintype, Fintype.prod_equiv, Injective, apply_swap_eq_self, injective_iff_bijective, mem_univ, mul_swap_eq_iff, not_congr, prod_equiv, prod_mul_distrib, sign_swap, sum_involution
-/
theorem det_mul_aux {M N : Matrix n n R} {p : n -> n} (H : ¬Bijective p) :
    (∑ σ : Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : exists i j, p i = p j ∧ i != j := by
    rw [← Finite.injective_iff_bijective]; rw [Injective] at H
    push Not at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij])
        simp [this, sign_swap hij, -sign_swap', prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ =>
      mul_swap_involutive i j σ

@[simp]
/--
theorem `det_mul` / 定理 `det_mul`

English:
theorem det_mul
  given: (M N : Matrix n n R)
  statement: det (M * N) = det M * det N
  proof: calc
    det (M * N) = ∑ p : n -> n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n -> n with Bijective p, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=

中文:
定理 det_mul
  条件: (M N : 矩阵 n n R)
  结论: det (M * N) = det M * det N
  证明: calc
    det (M * N) = ∑ p : n -> n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n -> n with Bijective p, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=

Depends on / 依赖: Bijective, Equiv.of, Finset, Finset.sum_comm, Fintype, Fintype.piFinset_univ, det_apply, det_mul_aux, filter_subset, mem_filter_univ, mul_apply, mul_sum, piFinset_univ, prod_univ_sum, sum_bij, sum_comm, sum_subset
-/
theorem det_mul (M N : Matrix n n R) : det (M * N) = det M * det N :=
  calc
    det (M * N) = ∑ p : n -> n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n -> n with Bijective p, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      refine (sum_subset (filter_subset _ _) fun f _ hbij => det_mul_aux ?_).symm
      simpa only [mem_filter_univ] using hbij
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      sum_bij (fun p h => Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _)
        (fun _ _ _ _ h => by injection h)
        (fun b _ => ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩) fun _ _ => rfl
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      (sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp
          have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                rw [mul_comm]; rw [sign_mul (τ * σ⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε τ := by simp only [inv_mul_cancel_right]
          simp_rw [Equiv.coe_mulRight, h]
          simp only [this])
    _ = det M * det N := by
      simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/--
Definition of `detMonoidHom` / `detMonoidHom` 的定义

English:
definition detMonoidHom
  signature: : Matrix n n R ->* R where
  body: det
  map_one' := det_one
  map_mul' := det_mul

@[simp]

中文:
定义 detMonoidHom
  签名: : 矩阵 n n R ->* R where
  定义体: det
  map_one' := det_one
  map_mul' := det_mul

@[simp]
-/
def detMonoidHom : Matrix n n R ->* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul

@[simp]
/--
theorem `coe_detMonoidHom` / 定理 `coe_detMonoidHom`

English:
theorem coe_detMonoidHom
  statement: (detMonoidHom : Matrix n n R -> R) = det
  proof: rfl

中文:
定理 coe_detMonoidHom
  结论: (detMonoidHom : 矩阵 n n R -> R) = det
  证明: rfl
-/
theorem coe_detMonoidHom : (detMonoidHom : Matrix n n R -> R) = det :=
  rfl

/--
theorem `det_mul_comm` / 定理 `det_mul_comm`

English:
theorem det_mul_comm
  given: (M N : Matrix m m R)
  statement: det (M * N) = det (N * M)
  proof: by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

中文:
定理 det_mul_comm
  条件: (M N : 矩阵 m m R)
  结论: det (M * N) = det (N * M)
  证明: by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

Depends on / 依赖: det_mul, mul_comm
-/
theorem det_mul_comm (M N : Matrix m m R) : det (M * N) = det (N * M) := by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

/--
theorem `det_mul_left_comm` / 定理 `det_mul_left_comm`

English:
theorem det_mul_left_comm
  given: (M N P : Matrix m m R)
  statement: det (M * (N * P)) = det (N * (M * P))
  proof: by
  rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm M N]; rw [← det_mul]

中文:
定理 det_mul_left_comm
  条件: (M N P : 矩阵 m m R)
  结论: det (M * (N * P)) = det (N * (M * P))
  证明: by
  rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm M N]; rw [← det_mul]

Depends on / 依赖: Matrix, Matrix.mul_assoc, det_mul, det_mul_comm, mul_assoc
-/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M * (N * P)) = det (N * (M * P)) := by
  rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm M N]; rw [← det_mul]

/--
theorem `det_mul_right_comm` / 定理 `det_mul_right_comm`

English:
theorem det_mul_right_comm
  given: (M N P : Matrix m m R)
  statement: det (M * N * P) = det (M * P * N)
  proof: by
  rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm N P]; rw [← det_mul]

中文:
定理 det_mul_right_comm
  条件: (M N P : 矩阵 m m R)
  结论: det (M * N * P) = det (M * P * N)
  证明: by
  rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm N P]; rw [← det_mul]

Depends on / 依赖: Matrix, Matrix.mul_assoc, det_mul, det_mul_comm, mul_assoc
-/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M * N * P) = det (M * P * N) := by
  rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [det_mul]; rw [det_mul_comm N P]; rw [← det_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed
/--
theorem `det_units_conj` / 定理 `det_units_conj`

English:
theorem det_units_conj
  given: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  proof: by
  rw [det_mul_right_comm]; rw [Units.mul_inv]; rw [one_mul]

中文:
定理 det_units_conj
  条件: (M : (矩阵 m m R)ˣ) (N : 矩阵 m m R)
  证明: by
  rw [det_mul_right_comm]; rw [Units.mul_inv]; rw [one_mul]

Depends on / 依赖: Units.mul_inv, det_mul_right_comm, mul_inv, one_mul
-/
theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (M.val * N * M⁻¹.val) = det N := by
  rw [det_mul_right_comm]; rw [Units.mul_inv]; rw [one_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed
/--
theorem `det_units_conj'` / 定理 `det_units_conj'`

English:
theorem det_units_conj'
  given: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  proof: det_units_conj M⁻¹ N

中文:
定理 det_units_conj'
  条件: (M : (矩阵 m m R)ˣ) (N : 矩阵 m m R)
  证明: det_units_conj M⁻¹ N

Depends on / 依赖: det_units_conj
-/
theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (M⁻¹.val * N * ↑M.val) = det N :=
  det_units_conj M⁻¹ N

/-- Transposing a matrix preserves the determinant. -/
@[simp]
/--
theorem `det_transpose` / 定理 `det_transpose`

English:
theorem det_transpose
  given: (M : Matrix n n R)
  statement: Mᵀ.det = M.det
  proof: by
  rw [det_apply']; rw [det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp

中文:
定理 det_transpose
  条件: (M : 矩阵 n n R)
  结论: Mᵀ.det = M.det
  证明: by
  rw [det_apply']; rw [det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp

Depends on / 依赖: Fintype, Fintype.prod_equiv, Fintype.sum_bijective, bijective, det_apply, inv_involutive, inv_involutive.bijective, prod_equiv, sign_inv, sum_bijective
-/
theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det := by
  rw [det_apply']; rw [det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp

/--
theorem `det_permute` / 定理 `det_permute`

English:
theorem det_permute
  given: (σ : Perm n) (M : Matrix n n R)
  proof: ((detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def, det])

中文:
定理 det_permute
  条件: (σ : 置换 n) (M : 矩阵 n n R)
  证明: ((detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def, det])

Depends on / 依赖: Units.smul_def, detRowAlternating, map_perm, smul_def
-/
theorem det_permute (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).det = Perm.sign σ * M.det :=
  ((detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def, det])

/--
theorem `det_permute'` / 定理 `det_permute'`

English:
theorem det_permute'
  given: (σ : Perm n) (M : Matrix n n R)
  proof: by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [det_permute]; rw [det_transpose]

中文:
定理 det_permute'
  条件: (σ : 置换 n) (M : 矩阵 n n R)
  证明: by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [det_permute]; rw [det_transpose]

Depends on / 依赖: det_permute, det_transpose, transpose_submatrix
-/
theorem det_permute' (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).det = Perm.sign σ * M.det := by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [det_permute]; rw [det_transpose]

/-- Permuting rows and columns with the same equivalence does not change the determinant. -/
@[simp]
/--
theorem `det_submatrix_equiv_self` / 定理 `det_submatrix_equiv_self`

English:
theorem det_submatrix_equiv_self
  given: (e : n ≃ m) (A : Matrix m m R)
  proof: by
  rw [det_apply']; rw [det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply]; rw [Equiv.symm_apply_apply]; rw [submatrix_apply]

中文:
定理 det_submatrix_equiv_self
  条件: (e : n ≃ m) (A : 矩阵 m m R)
  证明: by
  rw [det_apply']; rw [det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply]; rw [Equiv.symm_apply_apply]; rw [submatrix_apply]

Depends on / 依赖: Equiv.Perm.sign_permCongr, Equiv.permCongr, Equiv.permCongr_apply, Equiv.symm_apply_apply, Fintype, Fintype.prod_equiv, Fintype.sum_equiv, det_apply, permCongr, permCongr_apply, prod_equiv, sign_permCongr, submatrix_apply, sum_equiv, symm_apply_apply
-/
theorem det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) :
    det (A.submatrix e e) = det A := by
  rw [det_apply']; rw [det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply]; rw [Equiv.symm_apply_apply]; rw [submatrix_apply]

/-- Permuting rows and columns with two equivalences does not change the absolute value of the
determinant. -/
@[simp]
/--
theorem `abs_det_submatrix_equiv_equiv` / 定理 `abs_det_submatrix_equiv_equiv`

English:
theorem abs_det_submatrix_equiv_equiv
  statement: {R : Type*}
  proof: by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change |((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det| = |A.det|
  rw [Matrix.det_submatrix_equiv_self]; rw [Matrix.det_permute']; rw [abs_mul]; rw [abs_unit_intCast]; rw [one_mul]

中文:
定理 abs_det_submatrix_equiv_equiv
  结论: {R : 类型}
  证明: by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change |((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det| = |A.det|
  rw [Matrix.det_submatrix_equiv_self]; rw [Matrix.det_permute']; rw [abs_mul]; rw [abs_unit_intCast]; rw [one_mul]

Depends on / 依赖: A.det, A.submatrix, Matrix, Matrix.det_permute, Matrix.det_submatrix_equiv_self, abs_mul, abs_unit_intCast, det_permute, det_submatrix_equiv_self, one_mul, submatrix, symm.trans
-/
theorem abs_det_submatrix_equiv_equiv {R : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    |(A.submatrix e₁ e₂).det| = |A.det| := by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change |((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det| = |A.det|
  rw [Matrix.det_submatrix_equiv_self]; rw [Matrix.det_permute']; rw [abs_mul]; rw [abs_unit_intCast]; rw [one_mul]

/--
theorem `det_reindex_self` / 定理 `det_reindex_self`

English:
theorem det_reindex_self
  given: (e : m ≃ n) (A : Matrix m m R)
  statement: det (reindex e e A) = det A
  proof: det_submatrix_equiv_self e.symm A

中文:
定理 det_reindex_self
  条件: (e : m ≃ n) (A : 矩阵 m m R)
  结论: det (reindex e e A) = det A
  证明: det_submatrix_equiv_self e.symm A

Depends on / 依赖: det_submatrix_equiv_self, e.symm
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_submatrix_equiv_self e.symm A

/--
lemma `det_reindex` / 引理 `det_reindex`

English:
lemma det_reindex
  given: (e e' : m ≃ n) (M : Matrix m m R)
  proof: by
  trans ((M.reindex (e.trans e'.symm) (.refl _)).reindex e' e').det
  · congr 1; ext; simp
  · simp_rw [det_reindex_self, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, det_permute]
    rfl

中文:
引理 det_reindex
  条件: (e e' : m ≃ n) (M : 矩阵 m m R)
  证明: by
  trans ((M.reindex (e.trans e'.symm) (.refl _)).reindex e' e').det
  · congr 1; ext; simp
  · simp_rw [det_reindex_self, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, det_permute]
    rfl

Depends on / 依赖: Equiv.coe_refl, Equiv.refl_symm, M.reindex, coe_refl, det_permute, det_reindex_self, e.trans, refl_symm, reindex, reindex_apply, simp_rw
-/
lemma det_reindex (e e' : m ≃ n) (M : Matrix m m R) :
    (M.reindex e e').det = sign (e'.trans e.symm) * M.det := by
  trans ((M.reindex (e.trans e'.symm) (.refl _)).reindex e' e').det
  · congr 1; ext; simp
  · simp_rw [det_reindex_self, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, det_permute]
    rfl

/--
theorem `abs_det_reindex` / 定理 `abs_det_reindex`

English:
theorem abs_det_reindex
  statement: {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A

中文:
定理 abs_det_reindex
  结论: {R : 类型} [交换环 R] [线性序 R] [是StrictOrdered环 R]
  证明: abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A

Depends on / 依赖: abs_det_submatrix_equiv_equiv
-/
theorem abs_det_reindex {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    |det (reindex e₁ e₂ A)| = |det A| :=
  abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A

/--
theorem `det_smul` / 定理 `det_smul`

English:
theorem det_smul
  given: (A : Matrix n n R) (c : R)
  statement: det (c • A) = c ^ Fintype.card n * det A
  proof: calc
    det (c • A) = det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp

@[simp]

中文:
定理 det_smul
  条件: (A : 矩阵 n n R) (c : R)
  结论: det (c • A) = c ^ 有限类型.card n * det A
  证明: calc
    det (c • A) = det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp

@[simp]

Depends on / 依赖: Fintype, Fintype.card, det_mul, diagonal, smul_eq_diagonal_mul
-/
theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
  calc
    det (c • A) = det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp

@[simp]
/--
theorem `det_smul_of_tower` / 定理 `det_smul_of_tower`

English:
theorem det_smul_of_tower
  statement: {α} [Monoid α] [MulAction α R] [IsScalarTower α R R]
  proof: by
  rw [← smul_one_smul R c A]; rw [det_smul]; rw [smul_pow]; rw [one_pow]; rw [smul_mul_assoc]; rw [one_mul]

中文:
定理 det_smul_of_tower
  结论: {α} [幺半群 α] [乘法作用 α R] [标量塔 α R R]
  证明: by
  rw [← smul_one_smul R c A]; rw [det_smul]; rw [smul_pow]; rw [one_pow]; rw [smul_mul_assoc]; rw [one_mul]

Depends on / 依赖: det_smul, one_mul, one_pow, smul_mul_assoc, smul_one_smul, smul_pow
-/
theorem det_smul_of_tower {α} [Monoid α] [MulAction α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : α) (A : Matrix n n R) :
    det (c • A) = c ^ Fintype.card n • det A := by
  rw [← smul_one_smul R c A]; rw [det_smul]; rw [smul_pow]; rw [one_pow]; rw [smul_mul_assoc]; rw [one_mul]

/--
theorem `det_neg` / 定理 `det_neg`

English:
theorem det_neg
  given: (A : Matrix n n R)
  statement: det (-A) = (-1) ^ Fintype.card n * det A
  proof: by
  rw [← det_smul]; rw [neg_one_smul]

中文:
定理 det_neg
  条件: (A : 矩阵 n n R)
  结论: det (-A) = (-1) ^ 有限类型.card n * det A
  证明: by
  rw [← det_smul]; rw [neg_one_smul]

Depends on / 依赖: det_smul, neg_one_smul
-/
theorem det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.card n * det A := by
  rw [← det_smul]; rw [neg_one_smul]

/--
theorem `det_neg_eq_smul` / 定理 `det_neg_eq_smul`

English:
theorem det_neg_eq_smul
  given: (A : Matrix n n R)
  proof: by
  rw [← det_smul_of_tower]; rw [Units.neg_smul]; rw [one_smul]

中文:
定理 det_neg_eq_smul
  条件: (A : 矩阵 n n R)
  证明: by
  rw [← det_smul_of_tower]; rw [Units.neg_smul]; rw [one_smul]

Depends on / 依赖: Units.neg_smul, det_smul_of_tower, neg_smul, one_smul
-/
theorem det_neg_eq_smul (A : Matrix n n R) :
    det (-A) = (-1 : Units Int) ^ Fintype.card n • det A := by
  rw [← det_smul_of_tower]; rw [Units.neg_smul]; rw [one_smul]

/--
theorem `det_mul_row` / 定理 `det_mul_row`

English:
theorem det_mul_row
  given: (v : n -> R) (A : Matrix n n R)
  proof: calc
    det (of fun i j => v j * A i j) = det (A * diagonal v) :=
congr_arg det by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]

中文:
定理 det_mul_row
  条件: (v : n -> R) (A : 矩阵 n n R)
  证明: calc
    det (of fun i j => v j * A i j) = det (A * diagonal v) :=
congr_arg det by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]

Depends on / 依赖: congr_arg, det_diagonal, det_mul, diagonal, mul_comm
-/
theorem det_mul_row (v : n -> R) (A : Matrix n n R) :
    det (of fun i j => v j * A i j) = (∏ i, v i) * det A :=
  calc
    det (of fun i j => v j * A i j) = det (A * diagonal v) :=
congr_arg det by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]

/--
theorem `det_mul_column` / 定理 `det_mul_column`

English:
theorem det_mul_column
  given: (v : n -> R) (A : Matrix n n R)
  proof: MultilinearMap.map_smul_univ _ v A

@[simp]

中文:
定理 det_mul_column
  条件: (v : n -> R) (A : 矩阵 n n R)
  证明: MultilinearMap.map_smul_univ _ v A

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.map_smul_univ, map_smul_univ
-/
theorem det_mul_column (v : n -> R) (A : Matrix n n R) :
    det (of fun i j => v i * A i j) = (∏ i, v i) * det A :=
  MultilinearMap.map_smul_univ _ v A

@[simp]
/--
theorem `det_pow` / 定理 `det_pow`

English:
theorem det_pow
  given: (M : Matrix m m R) (n : Nat)
  statement: det (M ^ n) = det M ^ n
  proof: (detMonoidHom : Matrix m m R ->* R).map_pow M n

中文:
定理 det_pow
  条件: (M : 矩阵 m m R) (n : 自然数)
  结论: det (M ^ n) = det M ^ n
  证明: (detMonoidHom : Matrix m m R ->* R).map_pow M n

Depends on / 依赖: Matrix, detMonoidHom, map_pow
-/
theorem det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det M ^ n :=
  (detMonoidHom : Matrix m m R ->* R).map_pow M n

section HomMap

variable {S : Type w} [CommRing S]

/--
theorem `_root_.RingHom.map_det` / 定理 `_root_.RingHom.map_det`

English:
theorem _root_.RingHom.map_det
  given: (f : R ->+* S) (M : Matrix n n R)
  proof: by
  simp [Matrix.det_apply', map_sum f, map_prod f]

中文:
定理 _root_.环态射.map_det
  条件: (f : R ->+* S) (M : 矩阵 n n R)
  证明: by
  simp [Matrix.det_apply', map_sum f, map_prod f]

Depends on / 依赖: Matrix, Matrix.det_apply, det_apply, map_prod, map_sum
-/
theorem _root_.RingHom.map_det (f : R ->+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) := by
  simp [Matrix.det_apply', map_sum f, map_prod f]

/--
theorem `_root_.RingEquiv.map_det` / 定理 `_root_.RingEquiv.map_det`

English:
theorem _root_.RingEquiv.map_det
  given: (f : R ≃+* S) (M : Matrix n n R)
  proof: f.toRingHom.map_det _

中文:
定理 _root_.环等价.map_det
  条件: (f : R ≃+* S) (M : 矩阵 n n R)
  证明: f.toRingHom.map_det _

Depends on / 依赖: f.toRingHom.map_det, map_det, toRingHom
-/
theorem _root_.RingEquiv.map_det (f : R ≃+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _

/--
theorem `_root_.AlgHom.map_det` / 定理 `_root_.AlgHom.map_det`

English:
theorem _root_.AlgHom.map_det
  statement: [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S ->ₐ[R] T)
  proof: f.toRingHom.map_det _

中文:
定理 _root_.代数态射.map_det
  结论: [代数 R S] {T : 类型 z} [交换环 T] [代数 R T] (f : S ->ₐ[R] T)
  证明: f.toRingHom.map_det _

Depends on / 依赖: f.toRingHom.map_det, map_det, toRingHom
-/
theorem _root_.AlgHom.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S ->ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _

/--
theorem `_root_.AlgEquiv.map_det` / 定理 `_root_.AlgEquiv.map_det`

English:
theorem _root_.AlgEquiv.map_det
  statement: [Algebra R S] {T : Type z} [CommRing T] [Algebra R T]
  proof: f.toAlgHom.map_det _

@[norm_cast]

中文:
定理 _root_.代数等价.map_det
  结论: [代数 R S] {T : 类型 z} [交换环 T] [代数 R T]
  证明: f.toAlgHom.map_det _

@[norm_cast]

Depends on / 依赖: f.toAlgHom.map_det, map_det, toAlgHom
-/
theorem _root_.AlgEquiv.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T]
    (f : S ≃ₐ[R] T) (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toAlgHom.map_det _

@[norm_cast]
/--
theorem `_root_.Int.cast_det` / 定理 `_root_.Int.cast_det`

English:
theorem _root_.Int.cast_det
  given: (M : Matrix n n Int)
  proof: .map_det M Int.castRingHom R

@[norm_cast]

中文:
定理 _root_.整数.cast_det
  条件: (M : 矩阵 n n 整数)
  证明: .map_det M Int.castRingHom R

@[norm_cast]

Depends on / 依赖: Int.castRingHom, castRingHom, map_det
-/
theorem _root_.Int.cast_det (M : Matrix n n Int) :
    (M.det : R) = (M.map fun x => (x : R)).det :=
.map_det M Int.castRingHom R

@[norm_cast]
/--
theorem `_root_.Rat.cast_det` / 定理 `_root_.Rat.cast_det`

English:
theorem _root_.Rat.cast_det
  given: {F : Type*} [Field F] [CharZero F] (M : Matrix n n Rat)
  proof: .map_det M Rat.castHom F

中文:
定理 _root_.有理数.cast_det
  条件: {F : 类型} [域 F] [特征零 F] (M : 矩阵 n n 有理数)
  证明: .map_det M Rat.castHom F

Depends on / 依赖: Rat.castHom, castHom, map_det
-/
theorem _root_.Rat.cast_det {F : Type*} [Field F] [CharZero F] (M : Matrix n n Rat) :
    (M.det : F) = (M.map fun x => (x : F)).det :=
.map_det M Rat.castHom F

end HomMap

@[simp]
/--
theorem `det_conjTranspose` / 定理 `det_conjTranspose`

English:
theorem det_conjTranspose
  given: [StarRing R] (M : Matrix m m R)
  statement: det Mᴴ = star (det M)
  proof: ((starRingEnd R).map_det _).symm.trans congr_arg star M.det_transpose

中文:
定理 det_conjTranspose
  条件: [对合环 R] (M : 矩阵 m m R)
  结论: det Mᴴ = star (det M)
  证明: ((starRingEnd R).map_det _).symm.trans congr_arg star M.det_transpose

Depends on / 依赖: M.det_transpose, congr_arg, det_transpose, map_det, starRingEnd, symm.trans
-/
theorem det_conjTranspose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
((starRingEnd R).map_det _).symm.trans congr_arg star M.det_transpose

section DetZero



/--
theorem `det_eq_zero_of_row_eq_zero` / 定理 `det_eq_zero_of_row_eq_zero`

English:
theorem det_eq_zero_of_row_eq_zero
  given: {A : Matrix n n R} (i : n) (h : forall j, A i j = 0)
  statement: det A = 0
  proof: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_coord_zero i (funext h)

中文:
定理 det_eq_zero_of_row_eq_zero
  条件: {A : 矩阵 n n R} (i : n) (h : 对任意 j, A i j = 0)
  结论: det A = 0
  证明: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_coord_zero i (funext h)

Depends on / 依赖: detRowAlternating, map_coord_zero
-/
theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : forall j, A i j = 0) : det A = 0 :=
  (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_coord_zero i (funext h)

/--
theorem `det_eq_zero_of_column_eq_zero` / 定理 `det_eq_zero_of_column_eq_zero`

English:
theorem det_eq_zero_of_column_eq_zero
  given: {A : Matrix n n R} (j : n) (h : forall i, A i j = 0)
  proof: by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

中文:
定理 det_eq_zero_of_column_eq_zero
  条件: {A : 矩阵 n n R} (j : n) (h : 对任意 i, A i j = 0)
  证明: by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

Depends on / 依赖: det_eq_zero_of_row_eq_zero, det_transpose
-/
theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : forall i, A i j = 0) :
    det A = 0 := by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

variable {M : Matrix n n R} {i j : n}

/--
theorem `det_zero_of_row_eq` / 定理 `det_zero_of_row_eq`

English:
theorem det_zero_of_row_eq
  given: (i_ne_j : i != j) (hij : M i = M j)
  statement: M.det = 0
  proof: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

中文:
定理 det_zero_of_row_eq
  条件: (i_ne_j : i != j) (hij : M i = M j)
  结论: M.det = 0
  证明: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

Depends on / 依赖: detRowAlternating, i_ne_j, map_eq_zero_of_eq
-/
theorem det_zero_of_row_eq (i_ne_j : i != j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

/--
theorem `det_zero_of_column_eq` / 定理 `det_zero_of_column_eq`

English:
theorem det_zero_of_column_eq
  given: (i_ne_j : i != j) (hij : forall k, M k i = M k j)
  statement: M.det = 0
  proof: by
  rw [← det_transpose]; rw [det_zero_of_row_eq i_ne_j]
  exact funext hij

中文:
定理 det_zero_of_column_eq
  条件: (i_ne_j : i != j) (hij : 对任意 k, M k i = M k j)
  结论: M.det = 0
  证明: by
  rw [← det_transpose]; rw [det_zero_of_row_eq i_ne_j]
  exact funext hij

Depends on / 依赖: det_transpose, det_zero_of_row_eq, i_ne_j
-/
theorem det_zero_of_column_eq (i_ne_j : i != j) (hij : forall k, M k i = M k j) : M.det = 0 := by
  rw [← det_transpose]; rw [det_zero_of_row_eq i_ne_j]
  exact funext hij

/--
theorem `det_updateRow_eq_zero` / 定理 `det_updateRow_eq_zero`

English:
theorem det_updateRow_eq_zero
  given: (h : i != j)
  proof: det_zero_of_row_eq h (by simp [h])

中文:
定理 det_updateRow_eq_zero
  条件: (h : i != j)
  证明: det_zero_of_row_eq h (by simp [h])

Depends on / 依赖: det_zero_of_row_eq
-/
theorem det_updateRow_eq_zero (h : i != j) :
    (M.updateRow j (M i)).det = 0 := det_zero_of_row_eq h (by simp [h])

/--
theorem `det_updateCol_eq_zero` / 定理 `det_updateCol_eq_zero`

English:
theorem det_updateCol_eq_zero
  given: (h : i != j)
  proof: det_zero_of_column_eq h (by simp [h])

中文:
定理 det_updateCol_eq_zero
  条件: (h : i != j)
  证明: det_zero_of_column_eq h (by simp [h])

Depends on / 依赖: det_zero_of_column_eq
-/
theorem det_updateCol_eq_zero (h : i != j) :
    (M.updateCol j (fun k => M k i)).det = 0 := det_zero_of_column_eq h (by simp [h])

end DetZero

/--
theorem `det_updateRow_add` / 定理 `det_updateRow_add`

English:
theorem det_updateRow_add
  given: (M : Matrix n n R) (j : n) (u v : n -> R)
  proof: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_add M j u v

中文:
定理 det_updateRow_add
  条件: (M : 矩阵 n n R) (j : n) (u v : n -> R)
  证明: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_add M j u v

Depends on / 依赖: detRowAlternating, map_update_add
-/
theorem det_updateRow_add (M : Matrix n n R) (j : n) (u v : n -> R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_add M j u v

/--
theorem `det_updateCol_add` / 定理 `det_updateCol_add`

English:
theorem det_updateCol_add
  given: (M : Matrix n n R) (j : n) (u v : n -> R)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_add]
  simp [updateRow_transpose, det_transpose]

中文:
定理 det_updateCol_add
  条件: (M : 矩阵 n n R) (j : n) (u v : n -> R)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_add]
  simp [updateRow_transpose, det_transpose]

Depends on / 依赖: det_transpose, det_updateRow_add, updateRow_transpose
-/
theorem det_updateCol_add (M : Matrix n n R) (j : n) (u v : n -> R) :
    det (updateCol M j <| u + v) = det (updateCol M j u) + det (updateCol M j v) := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_add]
  simp [updateRow_transpose, det_transpose]

/--
theorem `det_updateRow_smul` / 定理 `det_updateRow_smul`

English:
theorem det_updateRow_smul
  given: (M : Matrix n n R) (j : n) (s : R) (u : n -> R)
  proof: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_smul M j s u

中文:
定理 det_updateRow_smul
  条件: (M : 矩阵 n n R) (j : n) (s : R) (u : n -> R)
  证明: (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_smul M j s u

Depends on / 依赖: detRowAlternating, map_update_smul
-/
theorem det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n -> R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R).map_update_smul M j s u

/--
theorem `det_updateCol_smul` / 定理 `det_updateCol_smul`

English:
theorem det_updateCol_smul
  given: (M : Matrix n n R) (j : n) (s : R) (u : n -> R)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]

中文:
定理 det_updateCol_smul
  条件: (M : 矩阵 n n R) (j : n) (s : R) (u : n -> R)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]

Depends on / 依赖: det_transpose, det_updateRow_smul, updateRow_transpose
-/
theorem det_updateCol_smul (M : Matrix n n R) (j : n) (s : R) (u : n -> R) :
    det (updateCol M j <| s • u) = s * det (updateCol M j u) := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]

/--
theorem `det_updateRow_smul_left` / 定理 `det_updateRow_smul_left`

English:
theorem det_updateRow_smul_left
  given: (M : Matrix n n R) (j : n) (s : R) (u : n -> R)
  proof: MultilinearMap.map_update_smul_left _ M j s u

中文:
定理 det_updateRow_smul_left
  条件: (M : 矩阵 n n R) (j : n) (s : R) (u : n -> R)
  证明: MultilinearMap.map_update_smul_left _ M j s u

Depends on / 依赖: MultilinearMap, MultilinearMap.map_update_smul_left, map_update_smul_left
-/
theorem det_updateRow_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n -> R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul_left _ M j s u

/--
theorem `det_updateCol_smul_left` / 定理 `det_updateCol_smul_left`

English:
theorem det_updateCol_smul_left
  given: (M : Matrix n n R) (j : n) (s : R) (u : n -> R)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [transpose_smul]; rw [det_updateRow_smul_left]
  simp [updateRow_transpose, det_transpose]

中文:
定理 det_updateCol_smul_left
  条件: (M : 矩阵 n n R) (j : n) (s : R) (u : n -> R)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [transpose_smul]; rw [det_updateRow_smul_left]
  simp [updateRow_transpose, det_transpose]

Depends on / 依赖: det_transpose, det_updateRow_smul_left, transpose_smul, updateRow_transpose
-/
theorem det_updateCol_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n -> R) :
    det (updateCol (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateCol M j u) := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [transpose_smul]; rw [det_updateRow_smul_left]
  simp [updateRow_transpose, det_transpose]

/--
theorem `det_updateRow_sum_aux` / 定理 `det_updateRow_sum_aux`

English:
theorem det_updateRow_sum_aux
  statement: (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n -> R)
  proof: by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | insert k _ hk h_ind =>
      have h : k != j := fun h => (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk]; rw [add_comm ((c k) • M

中文:
定理 det_updateRow_sum_aux
  结论: (M : 矩阵 n n R) {j : n} (s : 有限集 n) (hj : j ∉ s) (c : n -> R)
  证明: by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | insert k _ hk h_ind =>
      have h : k != j := fun h => (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk]; rw [add_comm ((c k) • M

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_empty, Finset.sum_insert, add_assoc, add_comm, add_zero, det_updateRow_add, det_updateRow_eq_zero, det_updateRow_smul, h_ind, induction_on, insert, mem_insert_of_mem, mem_insert_self, mul_zero, smul_eq_mul, sum_empty
-/
theorem det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n -> R)
    (a : R) :
    (M.updateRow j (a • M j + ∑ k in s, (c k) • M k)).det = a • M.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | insert k _ hk h_ind =>
      have h : k != j := fun h => (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk]; rw [add_comm ((c k) • M k)]; rw [← add_assoc]; rw [det_updateRow_add]; rw [det_updateRow_smul]; rw [det_updateRow_eq_zero h]; rw [mul_zero]; rw [add_zero]; rw [h_ind]
      exact fun h => hj (Finset.mem_insert_of_mem h)

/--
theorem `det_updateRow_sum` / 定理 `det_updateRow_sum`

English:
theorem det_updateRow_sum
  given: (A : Matrix n n R) (j : n) (c : n -> R)
  proof: by
  convert! det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.notMem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

中文:
定理 det_updateRow_sum
  条件: (A : 矩阵 n n R) (j : n) (c : n -> R)
  证明: by
  convert! det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.notMem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.add_sum_erase, Finset.univ.erase, Finset.univ.notMem_erase, add_sum_erase, convert, det_updateRow_sum_aux, mem_univ, notMem_erase
-/
theorem det_updateRow_sum (A : Matrix n n R) (j : n) (c : n -> R) :
    (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det := by
  convert! det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.notMem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

/--
theorem `det_updateCol_sum` / 定理 `det_updateCol_sum`

English:
theorem det_updateCol_sum
  given: (A : Matrix n n R) (j : n) (c : n -> R)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  convert! det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

中文:
定理 det_updateCol_sum
  条件: (A : 矩阵 n n R) (j : n) (c : n -> R)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  convert! det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

Depends on / 依赖: A.transpose, Finset, Finset.sum_apply, Pi.smul_apply, convert, det_transpose, det_updateRow_sum, smul_apply, smul_eq_mul, sum_apply, transpose, transpose_apply, updateRow_transpose
-/
theorem det_updateCol_sum (A : Matrix n n R) (j : n) (c : n -> R) :
    (A.updateCol j (fun k => ∑ i, (c i) • A k i)).det = (c j) • A.det := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  convert! det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

section DetEq



/--
theorem `det_eq_of_eq_mul_det_one` / 定理 `det_eq_of_eq_mul_det_one`

English:
theorem det_eq_of_eq_mul_det_one
  statement: {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
  proof: calc
    det A = det (B * C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]

中文:
定理 det_eq_of_eq_mul_det_one
  结论: {A B : 矩阵 n n R} (C : 矩阵 n n R) (hC : det C = 1)
  证明: calc
    det A = det (B * C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]

Depends on / 依赖: congr_arg, det_mul, mul_one
-/
theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = B * C) : det A = det B :=
  calc
    det A = det (B * C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]

/--
theorem `det_eq_of_eq_det_one_mul` / 定理 `det_eq_of_eq_det_one_mul`

English:
theorem det_eq_of_eq_det_one_mul
  statement: {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
  proof: calc
    det A = det (C * B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]

中文:
定理 det_eq_of_eq_det_one_mul
  结论: {A B : 矩阵 n n R} (C : 矩阵 n n R) (hC : det C = 1)
  证明: calc
    det A = det (C * B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]

Depends on / 依赖: congr_arg, det_mul, one_mul
-/
theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = C * B) : det A = det B :=
  calc
    det A = det (C * B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]

/--
theorem `det_updateRow_add_self` / 定理 `det_updateRow_add_self`

English:
theorem det_updateRow_add_self
  given: (A : Matrix n n R) {i j : n} (hij : i != j)
  proof: by
  simp [det_updateRow_add,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

中文:
定理 det_updateRow_add_self
  条件: (A : 矩阵 n n R) {i j : n} (hij : i != j)
  证明: by
  simp [det_updateRow_add,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

Depends on / 依赖: det_updateRow_add, det_zero_of_row_eq, hij.symm, updateRow_ne, updateRow_self, updateRow_self.trans
-/
theorem det_updateRow_add_self (A : Matrix n n R) {i j : n} (hij : i != j) :
    det (updateRow A i (A i + A j)) = det A := by
  simp [det_updateRow_add,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

/--
theorem `det_updateCol_add_self` / 定理 `det_updateCol_add_self`

English:
theorem det_updateCol_add_self
  given: (A : Matrix n n R) {i j : n} (hij : i != j)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_self Aᵀ hij

中文:
定理 det_updateCol_add_self
  条件: (A : 矩阵 n n R) {i j : n} (hij : i != j)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_self Aᵀ hij

Depends on / 依赖: det_transpose, det_updateRow_add_self, updateRow_transpose
-/
theorem det_updateCol_add_self (A : Matrix n n R) {i j : n} (hij : i != j) :
    det (updateCol A i fun k => A k i + A k j) = det A := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_self Aᵀ hij

/--
theorem `det_updateRow_add_smul_self` / 定理 `det_updateRow_add_smul_self`

English:
theorem det_updateRow_add_smul_self
  given: (A : Matrix n n R) {i j : n} (hij : i != j) (c : R)
  proof: by
  simp [det_updateRow_add, det_updateRow_smul,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

中文:
定理 det_updateRow_add_smul_self
  条件: (A : 矩阵 n n R) {i j : n} (hij : i != j) (c : R)
  证明: by
  simp [det_updateRow_add, det_updateRow_smul,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

Depends on / 依赖: det_updateRow_add, det_updateRow_smul, det_zero_of_row_eq, hij.symm, updateRow_ne, updateRow_self, updateRow_self.trans
-/
theorem det_updateRow_add_smul_self (A : Matrix n n R) {i j : n} (hij : i != j) (c : R) :
    det (updateRow A i (A i + c • A j)) = det A := by
  simp [det_updateRow_add, det_updateRow_smul,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

/--
theorem `det_updateCol_add_smul_self` / 定理 `det_updateCol_add_smul_self`

English:
theorem det_updateCol_add_smul_self
  given: (A : Matrix n n R) {i j : n} (hij : i != j) (c : R)
  proof: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_smul_self Aᵀ hij c

中文:
定理 det_updateCol_add_smul_self
  条件: (A : 矩阵 n n R) {i j : n} (hij : i != j) (c : R)
  证明: by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_smul_self Aᵀ hij c

Depends on / 依赖: det_transpose, det_updateRow_add_smul_self, updateRow_transpose
-/
theorem det_updateCol_add_smul_self (A : Matrix n n R) {i j : n} (hij : i != j) (c : R) :
    det (updateCol A i fun k => A k i + c • A k j) = det A := by
  rw [← det_transpose]; rw [← updateRow_transpose]; rw [← det_transpose A]
  exact det_updateRow_add_smul_self Aᵀ hij c

/--
theorem `det_eq_zero_of_not_linearIndependent_rows` / 定理 `det_eq_zero_of_not_linearIndependent_rows`

English:
theorem det_eq_zero_of_not_linearIndependent_rows
  statement: [IsDomain R] {A : Matrix m m R}
  proof: detRowAlternating.map_linearDependent A hA

中文:
定理 det_eq_zero_of_not_linearIndependent_rows
  结论: [是整环 R] {A : 矩阵 m m R}
  证明: detRowAlternating.map_linearDependent A hA

Depends on / 依赖: detRowAlternating, detRowAlternating.map_linearDependent, map_linearDependent
-/
theorem det_eq_zero_of_not_linearIndependent_rows [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i => A i)) :
    det A = 0 := detRowAlternating.map_linearDependent A hA

/--
theorem `linearIndependent_rows_of_det_ne_zero` / 定理 `linearIndependent_rows_of_det_ne_zero`

English:
theorem linearIndependent_rows_of_det_ne_zero
  given: [IsDomain R] {A : Matrix m m R} (hA : A.det != 0)
  proof: by
  contrapose hA
  exact det_eq_zero_of_not_linearIndependent_rows hA

中文:
定理 linearIndependent_rows_of_det_ne_zero
  条件: [是整环 R] {A : 矩阵 m m R} (hA : A.det != 0)
  证明: by
  contrapose hA
  exact det_eq_zero_of_not_linearIndependent_rows hA

Depends on / 依赖: contrapose, det_eq_zero_of_not_linearIndependent_rows
-/
theorem linearIndependent_rows_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det != 0) :
    LinearIndependent R (fun i => A i) := by
  contrapose hA
  exact det_eq_zero_of_not_linearIndependent_rows hA

/--
theorem `linearIndependent_cols_of_det_ne_zero` / 定理 `linearIndependent_cols_of_det_ne_zero`

English:
theorem linearIndependent_cols_of_det_ne_zero
  given: [IsDomain R] {A : Matrix m m R} (hA : A.det != 0)
  proof: Matrix.linearIndependent_rows_of_det_ne_zero (by simpa [Matrix.col])

中文:
定理 linearIndependent_cols_of_det_ne_zero
  条件: [是整环 R] {A : 矩阵 m m R} (hA : A.det != 0)
  证明: Matrix.linearIndependent_rows_of_det_ne_zero (by simpa [Matrix.col])

Depends on / 依赖: Matrix, Matrix.col, Matrix.linearIndependent_rows_of_det_ne_zero, linearIndependent_rows_of_det_ne_zero
-/
theorem linearIndependent_cols_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det != 0) :
    LinearIndependent R A.col :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by simpa [Matrix.col])

/--
theorem `det_eq_zero_of_not_linearIndependent_cols` / 定理 `det_eq_zero_of_not_linearIndependent_cols`

English:
theorem det_eq_zero_of_not_linearIndependent_cols
  statement: [IsDomain R] {A : Matrix m m R}
  proof: by
  contrapose! hA
  exact linearIndependent_cols_of_det_ne_zero hA

中文:
定理 det_eq_zero_of_not_linearIndependent_cols
  结论: [是整环 R] {A : 矩阵 m m R}
  证明: by
  contrapose! hA
  exact linearIndependent_cols_of_det_ne_zero hA

Depends on / 依赖: contrapose, linearIndependent_cols_of_det_ne_zero
-/
theorem det_eq_zero_of_not_linearIndependent_cols [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i => Aᵀ i)) :
    det A = 0 := by
  contrapose! hA
  exact linearIndependent_cols_of_det_ne_zero hA

/--
theorem `det_vecMulVec` / 定理 `det_vecMulVec`

English:
theorem det_vecMulVec
  given: [Nontrivial n] (u v : n -> R)
  statement: (vecMulVec u v).det = 0
  proof: by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let uv' := ((vecMulVec u v).updateRow i v).updateRow j v
  have huv' : uv'.det = 0 := by
    refine detRowAlternating.map_eq_zero_of_eq _ ?_ hij
    simp [uv', hij]
  have : vecMulVec u v =
      (uv'.updateRow i (u i • uv' i)).updateRow j (u j • uv'.upd

中文:
定理 det_vecMulVec
  条件: [非平凡 n] (u v : n -> R)
  结论: (vecMulVec u v).det = 0
  证明: by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let uv' := ((vecMulVec u v).updateRow i v).updateRow j v
  have huv' : uv'.det = 0 := by
    refine detRowAlternating.map_eq_zero_of_eq _ ?_ hij
    simp [uv', hij]
  have : vecMulVec u v =
      (uv'.updateRow i (u i • uv' i)).updateRow j (u j • uv'.upd

Depends on / 依赖: detRowAlternating, detRowAlternating.map_eq_zero_of_eq, exists_pair_ne, hij.symm, map_eq_zero_of_eq, updateR, updateRow, updateRow_comm, updateRow_idem, updateRow_ne, updateRow_self, vecMulVec
-/
theorem det_vecMulVec [Nontrivial n] (u v : n -> R) : (vecMulVec u v).det = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let uv' := ((vecMulVec u v).updateRow i v).updateRow j v
  have huv' : uv'.det = 0 := by
    refine detRowAlternating.map_eq_zero_of_eq _ ?_ hij
    simp [uv', hij]
  have : vecMulVec u v =
      (uv'.updateRow i (u i • uv' i)).updateRow j (u j • uv'.updateRow i (u i • uv' i) j) := by
    unfold uv'
    rw [updateRow_comm _ hij]; rw [updateRow_idem]; rw [updateRow_ne hij.symm]; rw [updateRow_ne hij]; rw [updateRow_self]; rw [updateRow_self]; rw [updateRow_comm _ hij]; rw [updateRow_idem]; rw [← update_vecMulVec u v j]; rw [update_eq_self]; rw [← update_vecMulVec u v i]; rw [update_eq_self]
  rw [this]; rw [det_updateRow_smul]; rw [updateRow_eq_self]; rw [det_updateRow_smul]; rw [updateRow_eq_self]; rw [huv']; rw [mul_zero]; rw [mul_zero]

/--
theorem `det_eq_of_forall_row_eq_smul_add_const_aux` / 定理 `det_eq_of_forall_row_eq_smul_add_const_aux`

English:
theorem det_eq_of_forall_row_eq_smul_add_const_aux
  given: {A B : Matrix n n R} {s : Finset n}
  proof: by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    rintro c hs k - A_eq
    have : forall i, c i = 0 := by grind
    congr
    ext i j
    rw [A_eq]; rw [this]; rw [zero_mul]; rw [add_zero]
  | insert i s _hi ih =>
    intro c hs k hk A_eq
    have hAi : A i = B i + c i 

中文:
定理 det_eq_of_对任意_row_eq_smul_add_const_aux
  条件: {A B : 矩阵 n n R} {s : 有限集 n}
  证明: by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    rintro c hs k - A_eq
    have : forall i, c i = 0 := by grind
    congr
    ext i j
    rw [A_eq]; rw [this]; rw [zero_mul]; rw [add_zero]
  | insert i s _hi ih =>
    intro c hs k hk A_eq
    have hAi : A i = B i + c i 

Depends on / 依赖: A_eq, Finset, Finset.induction_on, Finset.mem_insert_self, Function, Function.update, add_zero, det_updateRow_add_smul_self, generalizing, induction_on, insert, mem_insert_self, update, updateRow, zero_mul
-/
theorem det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} :
    forall (c : n -> R) (_ : forall i, i ∉ s -> c i = 0) (k : n) (_ : k ∉ s)
      (_ : forall i j, A i j = B i j + c i * B k j), det A = det B := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    rintro c hs k - A_eq
    have : forall i, c i = 0 := by grind
    congr
    ext i j
    rw [A_eq]; rw [this]; rw [zero_mul]; rw [add_zero]
  | insert i s _hi ih =>
    intro c hs k hk A_eq
    have hAi : A i = B i + c i • B k := funext (A_eq i)
    rw [@ih (updateRow B i (A i)) (Function.update c i 0)]; rw [hAi]; rw [det_updateRow_add_smul_self]
    · exact mt (fun h => show k in insert i s from h ▸ Finset.mem_insert_self _ _) hk
    · intro i' hi'
      rw [Function.update_apply]
      split_ifs with hi'i
      · rfl
      · exact hs i' fun h => hi' ((Finset.mem_insert.mp h).resolve_left hi'i)
    · exact k
    · exact fun h => hk (Finset.mem_insert_of_mem h)
    · intro i' j'
      rw [updateRow_apply]; rw [Function.update_apply]
      split_ifs with hi'i
      · simp [hi'i]
      rw [A_eq]; rw [updateRow_ne fun h : k = i => hk <| h ▸ Finset.mem_insert_self k s]

/--
theorem `det_eq_of_forall_row_eq_smul_add_const` / 定理 `det_eq_of_forall_row_eq_smul_add_const`

English:
theorem det_eq_of_forall_row_eq_smul_add_const
  statement: {A B : Matrix n n R} (c : n -> R) (k : n)
  proof: det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.notMem_erase k Finset.univ) A_eq

中文:
定理 det_eq_of_对任意_row_eq_smul_add_const
  结论: {A B : 矩阵 n n R} (c : n -> R) (k : n)
  证明: det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.notMem_erase k Finset.univ) A_eq

Depends on / 依赖: A_eq, Finset, Finset.mem_erase.mpr, Finset.mem_univ, Finset.notMem_erase, Finset.univ, det_eq_of_forall_row_eq_smul_add_const_aux, h.symm, mem_erase, mem_univ, notMem_erase, not_imp_comm, not_imp_comm.mp
-/
theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n -> R) (k : n)
    (hk : c k = 0) (A_eq : forall i j, A i j = B i j + c i * B k j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.notMem_erase k Finset.univ) A_eq

/--
theorem `det_eq_of_forall_row_eq_smul_add_pred_aux` / 定理 `det_eq_of_forall_row_eq_smul_add_pred_aux`

English:
theorem det_eq_of_forall_row_eq_smul_add_pred_aux
  given: {n : Nat} (k : Fin (n + 1))
  proof: by
  refine Fin.induction ?_ (fun k ih => ?_) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine Fin.cases (h0 j) (fun i => ?_) i
    rw [hsucc]; rw [hc i (Fin.succ_pos _)]; rw [zero_mul]; rw [add_zero]
  set M' := updateRow M k.succ (N k.succ) with hM'
  have hM : M = updateRow M' k.suc

中文:
定理 det_eq_of_对任意_row_eq_smul_add_pred_aux
  条件: {n : 自然数} (k : 有限集 (n + 1))
  证明: by
  refine Fin.induction ?_ (fun k ih => ?_) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine Fin.cases (h0 j) (fun i => ?_) i
    rw [hsucc]; rw [hc i (Fin.succ_pos _)]; rw [zero_mul]; rw [add_zero]
  set M' := updateRow M k.succ (N k.succ) with hM'
  have hM : M = updateRow M' k.suc

Depends on / 依赖: Fin.cases, Fin.castSucc, Fin.induction, Fin.succ_pos, add_zero, castSucc, k.succ, k_ne_succ, succ_pos, updateRow, updateRow_ne, updateRow_self, zero_mul
-/
theorem det_eq_of_forall_row_eq_smul_add_pred_aux {n : Nat} (k : Fin (n + 1)) :
    forall (c : Fin n -> R) (_hc : forall i : Fin n, k < i.succ -> c i = 0)
      {M N : Matrix (Fin n.succ) (Fin n.succ) R} (_h0 : forall j, M 0 j = N 0 j)
      (_hsucc : forall (i : Fin n) (j), M i.succ j = N i.succ j + c i * M (Fin.castSucc i) j),
      det M = det N := by
  refine Fin.induction ?_ (fun k ih => ?_) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine Fin.cases (h0 j) (fun i => ?_) i
    rw [hsucc]; rw [hc i (Fin.succ_pos _)]; rw [zero_mul]; rw [add_zero]
  set M' := updateRow M k.succ (N k.succ) with hM'
  have hM : M = updateRow M' k.succ (M' k.succ + c k • M (Fin.castSucc k)) := by
    ext i j
    by_cases hi : i = k.succ
    · simp [hi, hM', hsucc, updateRow_self]
    rw [updateRow_ne hi]; rw [hM']; rw [updateRow_ne hi]
  have k_ne_succ : (Fin.castSucc k) != k.succ := Fin.castSucc_lt_succ.ne
  have M_k : M (Fin.castSucc k) = M' (Fin.castSucc k) := (updateRow_ne k_ne_succ).symm
  rw [hM]; rw [M_k]; rw [det_updateRow_add_smul_self M' k_ne_succ.symm]; rw [ih (Function.update c k 0)]
  · intro i hi
    rw [Fin.lt_def]; rw [Fin.val_castSucc]; rw [Fin.val_succ]; rw [Nat.lt_succ_iff] at hi
    rw [Function.update_apply]
    split_ifs with hik
    · rfl
    exact hc _ (Fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (Ne.symm hik)))
  · rwa [hM', updateRow_ne (Fin.succ_ne_zero _).symm]
  intro i j
  rw [Function.update_apply]
  split_ifs with hik
  · rw [zero_mul, add_zero, hM', hik, updateRow_self]
  rw [hM']; rw [updateRow_ne ((Fin.succ_injective _).ne hik)]; rw [hsucc]
  by_cases hik2 : k < i
  · simp [hc i (Fin.succ_lt_succ_iff.mpr hik2)]
  rw [updateRow_ne]
  apply ne_of_lt
  rwa [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Nat.lt_succ_iff, ← not_lt]

/--
theorem `det_eq_of_forall_row_eq_smul_add_pred` / 定理 `det_eq_of_forall_row_eq_smul_add_pred`

English:
theorem det_eq_of_forall_row_eq_smul_add_pred
  statement: {n : Nat} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
  proof: det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun _ hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ

中文:
定理 det_eq_of_对任意_row_eq_smul_add_pred
  结论: {n : 自然数} {A B : 矩阵 (有限集 (n + 1)) (有限集 (n + 1)) R}
  证明: det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun _ hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ

Depends on / 依赖: A_succ, A_zero, Fin.last, Fin.le_last, absurd, det_eq_of_forall_row_eq_smul_add_pred_aux, le_last, not_lt_of_ge
-/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : Nat} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n -> R) (A_zero : forall j, A 0 j = B 0 j)
    (A_succ : forall (i : Fin n) (j), A i.succ j = B i.succ j + c i * A (Fin.castSucc i) j) :
    det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun _ hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ

/--
theorem `det_eq_of_forall_col_eq_smul_add_pred` / 定理 `det_eq_of_forall_col_eq_smul_add_pred`

English:
theorem det_eq_of_forall_col_eq_smul_add_pred
  statement: {n : Nat} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
  proof: by
  rw [← det_transpose A]; rw [← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

中文:
定理 det_eq_of_对任意_col_eq_smul_add_pred
  结论: {n : 自然数} {A B : 矩阵 (有限集 (n + 1)) (有限集 (n + 1)) R}
  证明: by
  rw [← det_transpose A]; rw [← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

Depends on / 依赖: A_succ, A_zero, det_eq_of_forall_row_eq_smul_add_pred, det_transpose
-/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : Nat} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n -> R) (A_zero : forall i, A i 0 = B i 0)
    (A_succ : forall (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)) :
    det A = det B := by
  rw [← det_transpose A]; rw [← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

end DetEq

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `det_blockDiagonal` / 定理 `det_blockDiagonal`

English:
theorem det_blockDiagonal
  given: {o : Type*} [Fintype o] [DecidableEq o] (M : o -> Matrix n n R)
  proof: by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right-hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to

中文:
定理 det_blockDiagonal
  条件: {o : 类型} [有限类型 o] [DecidableEq o] (M : o -> 矩阵 n n R)
  证明: by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right-hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to
-/
theorem det_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] (M : o -> Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det := by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right-hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equiv.Perm (n × o)) := {σ | forall x, (σ x).snd = x.snd}
  have mem_preserving_snd :
    forall {σ : Equiv.Perm (n × o)}, σ in preserving_snd ↔ forall x, (σ x).snd = x.snd := fun {σ} =>
    Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → Equiv.Perm m`.
  · refine (Finset.sum_bij (fun σ _ => prodCongrLeft fun k => σ k (mem_univ k)) ?_ ?_ ?_ ?_).symm
    · intro σ _
      rw [mem_preserving_snd]
      rintro ⟨-, x⟩
      simp only [prodCongrLeft_apply]
    · intro σ _ σ' _ eq
      ext x hx k
      have :
        forall k x,
          prodCongrLeft (fun k => σ k (Finset.mem_univ _)) (k, x) =
            prodCongrLeft (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
        fun k x => by rw [eq]
      simp only [prodCongrLeft_apply, Prod.mk_inj] at this
      exact (this k x).1
    · intro σ hσ
      rw [mem_preserving_snd] at hσ
      have hσ' x : (σ.symm x).snd = x.snd := by simpa [eq_comm] using hσ (σ.symm x)
      have mk_apply_eq : forall k x, ((σ (x, k)).fst, k) = σ (x, k) := by
        intro k x
        ext
        · simp only
        · simp only [hσ]
      have mk_inv_apply_eq : forall k x, ((σ.symm (x, k)).fst, k) = σ.symm (x, k) := by grind
      refine ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ.symm (x, k)).fst, ?_, ?_⟩, ?_, ?_⟩
      · intro x
        simp [mk_apply_eq]
      · intro x
        simp [mk_inv_apply_eq]
      · apply Finset.mem_univ
      · ext ⟨k, x⟩
        · simp only [coe_fn_mk, prodCongrLeft_apply]
        · simp only [prodCongrLeft_apply, hσ]
    · intro σ _
      rw [Finset.prod_mul_distrib]; rw [← Finset.univ_product_univ]; rw [Finset.prod_product_right]
      simp only [sign_prodCongrLeft, Units.coe_prod, Int.cast_prod, blockDiagonal_apply_eq,
        prodCongrLeft_apply]
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k]; rw [x))]; rw [mul_zero]
    rw [blockDiagonal_apply_ne]
    exact hkx

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a 2×2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_isUpperTriangular`. -/
@[simp]
/--
theorem `det_fromBlocks_zero₂₁` / 定理 `det_fromBlocks_zero₂₁`

English:
theorem det_fromBlocks_zero₂₁
  given: (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R)
  proof: by
  classical
    simp_rw [det_apply']
    convert!
Eq.symm
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m oplus n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
     

中文:
定理 det_fromBlocks_zero₂₁
  条件: (A : 矩阵 m m R) (B : 矩阵 m n R) (D : 矩阵 n n R)
  证明: by
  classical
    simp_rw [det_apply']
    convert!
Eq.symm
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m oplus n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
     

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Eq.symm, Perm.sumCongr, Perm.sumCongr_apply, Sum.forall, Sum.map_inl, Sum.map_inr, classical, congr_fun, convert, det_apply, fst.sumCongr, map_inl, map_inr, simp_rw, subset_univ, sumCongr, sumCongrHom, sumCongr_apply
-/
theorem det_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
    simp_rw [det_apply']
    convert!
Eq.symm
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m oplus n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
      · intro σ₁₂ _
        simp
      · intro σ₁ _ σ₂ _
        dsimp only
        intro h
        have h2 : forall x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
          DFunLike.congr_fun h
        simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
          Sum.inr.injEq] at h2
        ext x
        · exact h2.left x
        · exact h2.right x
      · intro σ hσ
        rw [mem_coe]; rw [Set.mem_toFinset] at hσ
        obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
        use σ₁₂
        rw [← hσ₁₂]
        simp
      · simp only [forall_prop_of_true, Prod.forall, mem_univ]
        intro σ₁ σ₂
        rw [Fintype.prod_sum_type]
        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
          fromBlocks_apply₂₂]
        rw [mul_mul_mul_comm]
        congr
        rw [sign_sumCongr]; rw [Units.val_mul]; rw [Int.cast_mul]
    · rintro σ - hσn
      have h1 : ¬forall x, exists y, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσn
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
      obtain ⟨a, ha⟩ := not_forall.mp h1
      rcases hx : σ (Sum.inl a) with a2 | b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
        rw [hx]; rw [fromBlocks_apply₂₁]; rw [zero_apply]

/-- The determinant of a 2×2 block matrix with the upper-right block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_isLowerTriangular`. -/
@[simp]
/--
theorem `det_fromBlocks_zero₁₂` / 定理 `det_fromBlocks_zero₁₂`

English:
theorem det_fromBlocks_zero₁₂
  given: (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R)
  proof: by
  rw [← det_transpose]; rw [fromBlocks_transpose]; rw [transpose_zero]; rw [det_fromBlocks_zero₂₁]; rw [det_transpose]; rw [det_transpose]

中文:
定理 det_fromBlocks_zero₁₂
  条件: (A : 矩阵 m m R) (C : 矩阵 n m R) (D : 矩阵 n n R)
  证明: by
  rw [← det_transpose]; rw [fromBlocks_transpose]; rw [transpose_zero]; rw [det_fromBlocks_zero₂₁]; rw [det_transpose]; rw [det_transpose]

Depends on / 依赖: det_transpose, fromBlocks_transpose, transpose_zero
-/
theorem det_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← det_transpose]; rw [fromBlocks_transpose]; rw [transpose_zero]; rw [det_fromBlocks_zero₂₁]; rw [det_transpose]; rw [det_transpose]

/--
theorem `det_succ_column_zero` / 定理 `det_succ_column_zero`

English:
theorem det_succ_column_zero
  given: {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R)
  proof: by
  rw [Matrix.det_apply]; rw [Finset.univ_perm_fin_succ]; rw [← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_

中文:
定理 det_succ_column_zero
  条件: {n : 自然数} (A : 矩阵 (有限集 n.succ) (有限集 n.succ) R)
  证明: by
  rw [Matrix.det_apply]; rw [Finset.univ_perm_fin_succ]; rw [← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_

Depends on / 依赖: Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.swap_self, Equiv.toEmbedding_apply, Fin.cases, Fin.prod_univ_succ, Fin.succAbove_z, Fin.val_zero, Finset, Finset.mul_sum, Finset.sum_congr, Finset.sum_map, Finset.sum_product, Finset.univ_perm_fin_succ, Finset.univ_product_univ, Matrix, Matrix.det_apply, Matrix.submatrix, decomposeFin
-/
theorem det_succ_column_zero {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : Nat) * A i 0 * det (A.submatrix i.succAbove Fin.succ) := by
  rw [Matrix.det_apply]; rw [Finset.univ_perm_fin_succ]; rw [← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero, one_mul,
      Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_self, if_true, id,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, Equiv.coe_refl, pow_zero,
      mul_smul_comm, of_apply]
  -- `univ_perm_fin_succ` gives a different embedding of `Perm (Fin n)` into
  -- `Perm (Fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : Nat) = (Perm.sign i.cycleRange) := by simp [Fin.sign_cycleRange]
  rw [Fin.val_succ]; rw [pow_succ']; rw [this]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_left_comm (ε _)]; rw [← det_permute]; rw [Matrix.det_apply]; rw [Finset.mul_sum]; rw [Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Equiv.Perm.decomposeFin.symm_sign]; rw [if_neg (Fin.succ_ne_zero i)]
  calc
    ((-1 * Perm.sign σ : Int) • ∏ i', A (Perm.decomposeFin.symm (Fin.succ i, σ) i') i') =
        (-1 * Perm.sign σ : Int) • (A (Fin.succ i) 0 *
          ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
        Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
    _ = -1 * (A (Fin.succ i) 0 * (Perm.sign σ : Int) •
        ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp [_root_.neg_mul, one_mul, zsmul_eq_mul, neg_smul,
        Fin.succAbove_cycleRange, mul_left_comm]

/--
theorem `det_succ_row_zero` / 定理 `det_succ_row_zero`

English:
theorem det_succ_row_zero
  given: {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R)
  proof: by
  rw [← det_transpose A]; rw [det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

中文:
定理 det_succ_row_zero
  条件: {n : 自然数} (A : 矩阵 (有限集 n.succ) (有限集 n.succ) R)
  证明: by
  rw [← det_transpose A]; rw [det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

Depends on / 依赖: Finset, Finset.sum_congr, det_succ_column_zero, det_transpose, sum_congr, transpose_apply, transpose_submatrix, transpose_transpose
-/
theorem det_succ_row_zero {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * det (A.submatrix Fin.succ j.succAbove) := by
  rw [← det_transpose A]; rw [det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

/--
theorem `det_succ_row` / 定理 `det_succ_row`

English:
theorem det_succ_row
  given: {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ)
  proof: by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := by
    calc
      det A = ↑((-1 : Intˣ) ^ (i : Nat) * (-1 : Intˣ) ^ (i : Nat) : Intˣ) * det A := by simp
      _ = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := b

中文:
定理 det_succ_row
  条件: {n : 自然数} (A : 矩阵 (有限集 n.succ) (有限集 n.succ) R) (i : 有限集 n.succ)
  证明: by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := by
    calc
      det A = ↑((-1 : Intˣ) ^ (i : Nat) * (-1 : Intˣ) ^ (i : Nat) : Intˣ) * det A := by simp
      _ = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := b

Depends on / 依赖: Finset, Finset.sum_congr, Int.units_mul_self, Matrix, Matrix.submatrix_apply, Perm.sign, cycleRange, det_permute, det_succ_row_zero, i.cycleRange, mul_assoc, mul_sum, pow_add, simp_rw, submatrix_apply, submatrix_submatrix, sum_congr, units_mul_self
-/
theorem det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    det A =
      ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := by
    calc
      det A = ↑((-1 : Intˣ) ^ (i : Nat) * (-1 : Intˣ) ^ (i : Nat) : Intˣ) * det A := by simp
      _ = (-1 : R) ^ (i : Nat) * (Perm.sign i.cycleRange⁻¹) * det A := by simp [-Int.units_mul_self]
  rw [this]; rw [mul_assoc]
  congr
  rw [← det_permute]; rw [det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]; rw [Matrix.submatrix_apply]; rw [submatrix_submatrix]; rw [id_comp]; rw [Function.comp_def]; rw [id]
  simp

/--
theorem `det_succ_column` / 定理 `det_succ_column`

English:
theorem det_succ_column
  given: {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ)
  proof: by
  rw [← det_transpose]; rw [det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]; rw [← det_transpose]; rw [transpose_apply]; rw [transpose_submatrix]; rw [transpose_transpose]

中文:
定理 det_succ_column
  条件: {n : 自然数} (A : 矩阵 (有限集 n.succ) (有限集 n.succ) R) (j : 有限集 n.succ)
  证明: by
  rw [← det_transpose]; rw [det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]; rw [← det_transpose]; rw [transpose_apply]; rw [transpose_submatrix]; rw [transpose_transpose]

Depends on / 依赖: Finset, Finset.sum_congr, add_comm, det_succ_row, det_transpose, sum_congr, transpose_apply, transpose_submatrix, transpose_transpose
-/
theorem det_succ_column {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    det A =
      ∑ i : Fin n.succ, (-1) ^ (i + j : Nat) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  rw [← det_transpose]; rw [det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]; rw [← det_transpose]; rw [transpose_apply]; rw [transpose_submatrix]; rw [transpose_transpose]

/-- Determinant of 0x0 matrix -/
@[simp]
/--
theorem `det_fin_zero` / 定理 `det_fin_zero`

English:
theorem det_fin_zero
  given: {A : Matrix (Fin 0) (Fin 0) R}
  statement: det A = 1
  proof: det_isEmpty

中文:
定理 det_fin_zero
  条件: {A : 矩阵 (有限集 0) (有限集 0) R}
  结论: det A = 1
  证明: det_isEmpty

Depends on / 依赖: det_isEmpty
-/
theorem det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A = 1 :=
  det_isEmpty

/--
theorem `det_fin_one` / 定理 `det_fin_one`

English:
theorem det_fin_one
  given: (A : Matrix (Fin 1) (Fin 1) R)
  statement: det A = A 0 0
  proof: det_unique A

中文:
定理 det_fin_one
  条件: (A : 矩阵 (有限集 1) (有限集 1) R)
  结论: det A = A 0 0
  证明: det_unique A

Depends on / 依赖: det_unique
-/
theorem det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A = A 0 0 :=
  det_unique A

/--
theorem `det_fin_one_of` / 定理 `det_fin_one_of`

English:
theorem det_fin_one_of
  given: (a : R)
  statement: det !![a] = a
  proof: det_fin_one _

中文:
定理 det_fin_one_of
  条件: (a : R)
  结论: det !![a] = a
  证明: det_fin_one _

Depends on / 依赖: det_fin_one
-/
theorem det_fin_one_of (a : R) : det !![a] = a :=
  det_fin_one _

/--
theorem `det_fin_two` / 定理 `det_fin_two`

English:
theorem det_fin_two
  given: (A : Matrix (Fin 2) (Fin 2) R)
  statement: det A = A 0 0 * A 1 1 - A 0 1 * A 1 0
  proof: by
  simp only [det_succ_row_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, sum_singleton]
  ring

@[simp]

中文:
定理 det_fin_two
  条件: (A : 矩阵 (有限集 2) (有限集 2) R)
  结论: det A = A 0 0 * A 1 1 - A 0 1 * A 1 0
  证明: by
  simp only [det_succ_row_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, sum_singleton]
  ring

@[simp]

Depends on / 依赖: Fin.default_eq_zero, Fin.succ_succAbove_zero, Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_eq_zero, Fin.val_succ, Fin.val_zero, Fin.zero_succAbove, default_eq_zero, det_succ_row_zero, det_unique, submatrix_apply, succ_succAbove_zero, succ_zero_eq_one, sum_singleton, sum_univ_succ, univ_unique, val_eq_zero, val_succ, val_zero
-/
theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp only [det_succ_row_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, sum_singleton]
  ring

@[simp]
/--
theorem `det_fin_two_of` / 定理 `det_fin_two_of`

English:
theorem det_fin_two_of
  given: (a b c d : R)
  statement: Matrix.det !![a, b; c, d] = a * d - b * c
  proof: det_fin_two _

中文:
定理 det_fin_two_of
  条件: (a b c d : R)
  结论: 矩阵.det !![a, b; c, d] = a * d - b * c
  证明: det_fin_two _

Depends on / 依赖: det_fin_two
-/
theorem det_fin_two_of (a b c d : R) : Matrix.det !![a, b; c, d] = a * d - b * c :=
  det_fin_two _

/--
theorem `det_fin_three` / 定理 `det_fin_three`

English:
theorem det_fin_three
  given: (A : Matrix (Fin 3) (Fin 3) R)
  proof: by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_ze

中文:
定理 det_fin_three
  条件: (A : 矩阵 (有限集 3) (有限集 3) R)
  证明: by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_ze

Depends on / 依赖: Fin.default_eq_zero, Fin.succ_one_eq_two, Fin.succ_succAbove_one, Fin.succ_succAbove_zero, Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_eq_zero, Fin.val_succ, Fin.val_zero, Fin.zero_succAbove, Function, Function.comp_apply, comp_apply, default_eq_zero, det_succ_row_zero, det_unique, submatrix_apply, submatrix_submatrix, succ_one_eq_two, succ_succAbove_one
-/
theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
      - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
      + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_zero, sum_singleton, Fin.succ_succAbove_one]
  ring

end Matrix
