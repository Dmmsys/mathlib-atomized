/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `LinearAlgebra.Trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/

@[expose] public section


open Matrix

namespace Matrix

variable {ι m n p : Type*} {α R S : Type*}
variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoid

variable [AddCommMonoid R]

/--
Definition of `trace` / `trace` 的定义

English:
definition trace
  signature: (A : Matrix n n R)
  body: ∑ i, diag A i

中文:
定义 trace
  签名: (A : Matrix n n R)
  定义体: ∑ i, diag A i
-/
def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i

/--
lemma `trace_diagonal` / 引理 `trace_diagonal`

English:
lemma trace_diagonal
  given: {o} [Fintype o] [DecidableEq o] (d : o -> R)
  proof: by
  simp only [trace, diag_apply, diagonal_apply_eq]

中文:
引理 trace_diagonal
  条件: {o} [Fintype o] [DecidableEq o] (d : o -> R)
  证明: by
  simp only [trace, diag_apply, diagonal_apply_eq]
-/
@[simp] lemma trace_diagonal {o} [Fintype o] [DecidableEq o] (d : o -> R) :
    trace (diagonal d) = ∑ i, d i := by
  simp only [trace, diag_apply, diagonal_apply_eq]

variable (n R)

@[simp]
/--
theorem `trace_zero` / 定理 `trace_zero`

English:
theorem trace_zero
  statement: trace (0 : Matrix n n R) = 0
  proof: (Finset.sum_const (0 : R)).trans smul_zero _

中文:
定理 trace_zero
  结论: trace (0 : Matrix n n R) = 0
  证明: (Finset.sum_const (0 : R)).trans smul_zero _

Depends on / 依赖: Finset, Finset.sum_const, mkMetric, smul_zero, sum_const
-/
theorem trace_zero : trace (0 : Matrix n n R) = 0 :=
(Finset.sum_const (0 : R)).trans smul_zero _

variable {n R}

@[simp]
/--
lemma `trace_eq_zero_of_isEmpty` / 引理 `trace_eq_zero_of_isEmpty`

English:
lemma trace_eq_zero_of_isEmpty
  given: [IsEmpty n] (A : Matrix n n R)
  statement: trace A = 0
  proof: by simp [trace]

@[simp]

中文:
引理 trace_eq_zero_of_isEmpty
  条件: [IsEmpty n] (A : Matrix n n R)
  结论: trace A = 0
  证明: by simp [trace]

@[simp]
-/
lemma trace_eq_zero_of_isEmpty [IsEmpty n] (A : Matrix n n R) : trace A = 0 := by simp [trace]

@[simp]
/--
theorem `trace_add` / 定理 `trace_add`

English:
theorem trace_add
  given: (A B : Matrix n n R)
  statement: trace (A + B) = trace A + trace B
  proof: Finset.sum_add_distrib

@[simp]

中文:
定理 trace_add
  条件: (A B : Matrix n n R)
  结论: trace (A + B) = trace A + trace B
  证明: Finset.sum_add_distrib

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, sum_add_distrib
-/
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B :=
  Finset.sum_add_distrib

@[simp]
/--
theorem `trace_smul` / 定理 `trace_smul`

English:
theorem trace_smul
  given: [DistribSMul α R] (r : α) (A : Matrix n n R)
  proof: Finset.smul_sum.symm

@[simp]

中文:
定理 trace_smul
  条件: [DistribSMul α R] (r : α) (A : Matrix n n R)
  证明: Finset.smul_sum.symm

@[simp]

Depends on / 依赖: Finset, Finset.smul_sum.symm, smul_sum
-/
theorem trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) :
    trace (r • A) = r • trace A :=
  Finset.smul_sum.symm

@[simp]
/--
theorem `trace_transpose` / 定理 `trace_transpose`

English:
theorem trace_transpose
  given: (A : Matrix n n R)
  statement: trace Aᵀ = trace A
  proof: rfl

@[simp]

中文:
定理 trace_transpose
  条件: (A : Matrix n n R)
  结论: trace Aᵀ = trace A
  证明: rfl

@[simp]
-/
theorem trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A :=
  rfl

@[simp]
/--
theorem `trace_conjTranspose` / 定理 `trace_conjTranspose`

English:
theorem trace_conjTranspose
  given: [StarAddMonoid R] (A : Matrix n n R)
  statement: trace Aᴴ = star (trace A)
  proof: (star_sum _ _).symm

中文:
定理 trace_conjTranspose
  条件: [StarAddMonoid R] (A : Matrix n n R)
  结论: trace Aᴴ = star (trace A)
  证明: (star_sum _ _).symm

Depends on / 依赖: star_sum
-/
theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star (trace A) :=
  (star_sum _ _).symm

variable (n α R)

/-- `Matrix.trace` as an `AddMonoidHom` -/
@[simps]
/--
Definition of `traceAddMonoidHom` / `traceAddMonoidHom` 的定义

English:
definition traceAddMonoidHom
  signature: : Matrix n n R ->+ R where
  body: trace
  map_zero' := trace_zero n R
  map_add' := trace_add

中文:
定义 traceAddMonoidHom
  签名: : Matrix n n R ->+ R where
  定义体: trace
  map_zero' := trace_zero n R
  map_add' := trace_add
-/
def traceAddMonoidHom : Matrix n n R ->+ R where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add

/-- `Matrix.trace` as a `LinearMap` -/
@[simps]
/--
Definition of `traceLinearMap` / `traceLinearMap` 的定义

English:
definition traceLinearMap
  signature: [Semiring α] [Module α R]
  body: trace
  map_add' := trace_add
  map_smul' := trace_smul

中文:
定义 traceLinearMap
  签名: [Semiring α] [Module α R]
  定义体: trace
  map_add' := trace_add
  map_smul' := trace_smul
-/
def traceLinearMap [Semiring α] [Module α R] : Matrix n n R ->ₗ[α] R where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

variable {n α R}

@[simp]
/--
theorem `trace_list_sum` / 定理 `trace_list_sum`

English:
theorem trace_list_sum
  given: (l : List (Matrix n n R))
  statement: trace l.sum = (l.map trace).sum
  proof: map_list_sum (traceAddMonoidHom n R) l

@[simp]

中文:
定理 trace_list_sum
  条件: (l : List (Matrix n n R))
  结论: trace l.sum = (l.map trace).sum
  证明: map_list_sum (traceAddMonoidHom n R) l

@[simp]

Depends on / 依赖: map_list_sum, traceAddMonoidHom
-/
theorem trace_list_sum (l : List (Matrix n n R)) : trace l.sum = (l.map trace).sum :=
  map_list_sum (traceAddMonoidHom n R) l

@[simp]
/--
theorem `trace_multiset_sum` / 定理 `trace_multiset_sum`

English:
theorem trace_multiset_sum
  given: (s : Multiset (Matrix n n R))
  statement: trace s.sum = (s.map trace).sum
  proof: map_multiset_sum (traceAddMonoidHom n R) s

@[simp]

中文:
定理 trace_multiset_sum
  条件: (s : Multiset (Matrix n n R))
  结论: trace s.sum = (s.map trace).sum
  证明: map_multiset_sum (traceAddMonoidHom n R) s

@[simp]

Depends on / 依赖: map_multiset_sum, traceAddMonoidHom
-/
theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.sum = (s.map trace).sum :=
  map_multiset_sum (traceAddMonoidHom n R) s

@[simp]
/--
theorem `trace_sum` / 定理 `trace_sum`

English:
theorem trace_sum
  given: (s : Finset ι) (f : ι -> Matrix n n R)
  proof: map_sum (traceAddMonoidHom n R) f s

中文:
定理 trace_sum
  条件: (s : Finset ι) (f : ι -> Matrix n n R)
  证明: map_sum (traceAddMonoidHom n R) f s

Depends on / 依赖: Ioo_mem_nhdsGT, boundedBy_union_of_top_of_nonempty_inter, edist_le_ediam_of_mem, filter_upwards, iInf_eq_top, map_sum, mkMetric, not_ge, pos_iff_ne_zero, r.trans_le, tendsto_nhds_unique_of_eventuallyEq, tendsto_pre, this.not_ge, traceAddMonoidHom, trans_le
-/
theorem trace_sum (s : Finset ι) (f : ι -> Matrix n n R) :
    trace (∑ i in s, f i) = ∑ i in s, trace (f i) :=
  map_sum (traceAddMonoidHom n R) f s

/--
theorem `_root_.AddMonoidHom.map_trace` / 定理 `_root_.AddMonoidHom.map_trace`

English:
theorem _root_.AddMonoidHom.map_trace
  statement: [AddCommMonoid S] {F : Type*} [FunLike F R S]
  proof: map_sum f (fun i => diag A i) Finset.univ

中文:
定理 _root_.AddMonoidHom.map_trace
  结论: [AddCommMonoid S] {F : 类型} [FunLike F R S]
  证明: map_sum f (fun i => diag A i) Finset.univ

Depends on / 依赖: Finset, Finset.univ, map_sum
-/
theorem _root_.AddMonoidHom.map_trace [AddCommMonoid S] {F : Type*} [FunLike F R S]
    [AddMonoidHomClass F R S] (f : F) (A : Matrix n n R) :
    f (trace A) = trace (A.map f) :=
  map_sum f (fun i => diag A i) Finset.univ

/--
lemma `trace_blockDiagonal` / 引理 `trace_blockDiagonal`

English:
lemma trace_blockDiagonal
  given: [DecidableEq p] (M : p -> Matrix n n R)
  proof: by
  simp [blockDiagonal, trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]

中文:
引理 trace_blockDiagonal
  条件: [DecidableEq p] (M : p -> Matrix n n R)
  证明: by
  simp [blockDiagonal, trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]

Depends on / 依赖: Finset, Finset.sum_comm, Fintype, Fintype.sum_prod_type, blockDiagonal, sum_comm, sum_prod_type
-/
lemma trace_blockDiagonal [DecidableEq p] (M : p -> Matrix n n R) :
    trace (blockDiagonal M) = ∑ i, trace (M i) := by
  simp [blockDiagonal, trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]

/--
lemma `trace_blockDiagonal'` / 引理 `trace_blockDiagonal'`

English:
lemma trace_blockDiagonal'
  statement: [DecidableEq p] {m : p -> Type*} [forall i, Fintype (m i)]
  proof: by
  simp [blockDiagonal', trace, Finset.sum_sigma']

中文:
引理 trace_blockDiagonal'
  结论: [DecidableEq p] {m : p -> 类型} [对任意 i, Fintype (m i)]
  证明: by
  simp [blockDiagonal', trace, Finset.sum_sigma']

Depends on / 依赖: Finset, Finset.sum_sigma, blockDiagonal, sum_sigma
-/
lemma trace_blockDiagonal' [DecidableEq p] {m : p -> Type*} [forall i, Fintype (m i)]
    (M : forall i, Matrix (m i) (m i) R) :
    trace (blockDiagonal' M) = ∑ i, trace (M i) := by
  simp [blockDiagonal', trace, Finset.sum_sigma']

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

@[simp]
/--
theorem `trace_sub` / 定理 `trace_sub`

English:
theorem trace_sub
  given: (A B : Matrix n n R)
  statement: trace (A - B) = trace A - trace B
  proof: Finset.sum_sub_distrib ..

@[simp]

中文:
定理 trace_sub
  条件: (A B : Matrix n n R)
  结论: trace (A - B) = trace A - trace B
  证明: Finset.sum_sub_distrib ..

@[simp]

Depends on / 依赖: Finset, Finset.sum_sub_distrib, sum_sub_distrib
-/
theorem trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B :=
  Finset.sum_sub_distrib ..

@[simp]
/--
theorem `trace_neg` / 定理 `trace_neg`

English:
theorem trace_neg
  given: (A : Matrix n n R)
  statement: trace (-A) = -trace A
  proof: Finset.sum_neg_distrib ..

中文:
定理 trace_neg
  条件: (A : Matrix n n R)
  结论: trace (-A) = -trace A
  证明: Finset.sum_neg_distrib ..

Depends on / 依赖: Finset, Finset.sum_neg_distrib, sum_neg_distrib
-/
theorem trace_neg (A : Matrix n n R) : trace (-A) = -trace A :=
  Finset.sum_neg_distrib ..

end AddCommGroup

section One

variable [DecidableEq n] [AddCommMonoidWithOne R]

@[simp]
/--
theorem `trace_one` / 定理 `trace_one`

English:
theorem trace_one
  statement: trace (1 : Matrix n n R) = Fintype.card n
  proof: by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

中文:
定理 trace_one
  结论: trace (1 : Matrix n n R) = Fintype.card n
  证明: by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Pi.one_def, card_univ, diag_one, nsmul_one, one_def, simp_rw, sum_const
-/
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

end One

section Mul

@[simp]
/--
theorem `trace_transpose_mul` / 定理 `trace_transpose_mul`

English:
theorem trace_transpose_mul
  given: [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R)
  proof: Finset.sum_comm

中文:
定理 trace_transpose_mul
  条件: [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R)
  证明: Finset.sum_comm

Depends on / 依赖: Finset, Finset.sum_comm, sum_comm
-/
theorem trace_transpose_mul [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (Aᵀ * Bᵀ) = trace (A * B) :=
  Finset.sum_comm

/--
theorem `trace_mul_comm` / 定理 `trace_mul_comm`

English:
theorem trace_mul_comm
  given: [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R)
  proof: by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]

中文:
定理 trace_mul_comm
  条件: [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R)
  证明: by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]

Depends on / 依赖: trace_transpose, trace_transpose_mul, transpose_mul
-/
theorem trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = trace (B * A) := by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]

/--
theorem `trace_mul_cycle` / 定理 `trace_mul_cycle`

English:
theorem trace_mul_cycle
  statement: [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
  proof: by
  rw [trace_mul_comm]; rw [Matrix.mul_assoc]

中文:
定理 trace_mul_cycle
  结论: [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
  证明: by
  rw [trace_mul_comm]; rw [Matrix.mul_assoc]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, trace_mul_comm
-/
theorem trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * B * C) = trace (C * A * B) := by
  rw [trace_mul_comm]; rw [Matrix.mul_assoc]

/--
theorem `trace_mul_cycle'` / 定理 `trace_mul_cycle'`

English:
theorem trace_mul_cycle'
  statement: [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
  proof: by
  rw [← Matrix.mul_assoc]; rw [trace_mul_comm]

@[simp]

中文:
定理 trace_mul_cycle'
  结论: [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
  证明: by
  rw [← Matrix.mul_assoc]; rw [trace_mul_comm]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, trace_mul_comm
-/
theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * (B * C)) = trace (C * (A * B)) := by
  rw [← Matrix.mul_assoc]; rw [trace_mul_comm]

@[simp]
/--
theorem `trace_replicateCol_mul_replicateRow` / 定理 `trace_replicateCol_mul_replicateRow`

English:
theorem trace_replicateCol_mul_replicateRow
  statement: {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R]
  proof: by
  apply Finset.sum_congr rfl
  simp [mul_apply]

@[simp]

中文:
定理 trace_replicateCol_mul_replicateRow
  结论: {ι : 类型} [Unique ι] [NonUnitalNonAssocSemiring R]
  证明: by
  apply Finset.sum_congr rfl
  simp [mul_apply]

@[simp]

Depends on / 依赖: Finset, Finset.sum_congr, mul_apply, sum_congr
-/
theorem trace_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R]
    (a b : n -> R) : trace (replicateCol ι a * replicateRow ι b) = a ⬝ᵥ b := by
  apply Finset.sum_congr rfl
  simp [mul_apply]

@[simp]
/--
theorem `trace_vecMulVec` / 定理 `trace_vecMulVec`

English:
theorem trace_vecMulVec
  given: [NonUnitalNonAssocSemiring R] (a b : n -> R)
  proof: by
  rw [vecMulVec_eq Unit]; rw [trace_replicateCol_mul_replicateRow]

中文:
定理 trace_vecMulVec
  条件: [NonUnitalNonAssocSemiring R] (a b : n -> R)
  证明: by
  rw [vecMulVec_eq Unit]; rw [trace_replicateCol_mul_replicateRow]

Depends on / 依赖: trace_replicateCol_mul_replicateRow, vecMulVec_eq
-/
theorem trace_vecMulVec [NonUnitalNonAssocSemiring R] (a b : n -> R) :
    trace (vecMulVec a b) = a ⬝ᵥ b := by
  rw [vecMulVec_eq Unit]; rw [trace_replicateCol_mul_replicateRow]

end Mul

/--
lemma `trace_submatrix_succ` / 引理 `trace_submatrix_succ`

English:
lemma trace_submatrix_succ
  statement: {n : Nat} [AddCommMonoid R]
  proof: by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

中文:
引理 trace_submatrix_succ
  结论: {n : 自然数} [AddCommMonoid R]
  证明: by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

Depends on / 依赖: finSuccEquiv, sum_comp, symm.sum_comp
-/
lemma trace_submatrix_succ {n : Nat} [AddCommMonoid R]
    (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M := by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

section CommSemiring

variable [DecidableEq m] [CommSemiring R]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
/--
theorem `trace_units_conj` / 定理 `trace_units_conj`

English:
theorem trace_units_conj
  given: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  proof: by
  rw [trace_mul_cycle]; rw [Units.inv_mul]; rw [one_mul]

中文:
定理 trace_units_conj
  条件: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  证明: by
  rw [trace_mul_cycle]; rw [Units.inv_mul]; rw [one_mul]

Depends on / 依赖: Units.inv_mul, inv_mul, one_mul, trace_mul_cycle
-/
theorem trace_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N := by
  rw [trace_mul_cycle]; rw [Units.inv_mul]; rw [one_mul]

set_option linter.docPrime false in
-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
/--
theorem `trace_units_conj'` / 定理 `trace_units_conj'`

English:
theorem trace_units_conj'
  given: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  proof: trace_units_conj M⁻¹ N

中文:
定理 trace_units_conj'
  条件: (M : (Matrix m m R)ˣ) (N : Matrix m m R)
  证明: trace_units_conj M⁻¹ N

Depends on / 依赖: trace_units_conj
-/
theorem trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N :=
  trace_units_conj M⁻¹ N

end CommSemiring

section Fin

variable [AddCommMonoid R]

/-! ### Special cases for `Fin n` for low values of `n`
-/

@[simp]
/--
theorem `trace_fin_zero` / 定理 `trace_fin_zero`

English:
theorem trace_fin_zero
  given: (A : Matrix (Fin 0) (Fin 0) R)
  statement: trace A = 0
  proof: rfl

中文:
定理 trace_fin_zero
  条件: (A : Matrix (Fin 0) (Fin 0) R)
  结论: trace A = 0
  证明: rfl
-/
theorem trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : trace A = 0 :=
  rfl

/--
theorem `trace_fin_one` / 定理 `trace_fin_one`

English:
theorem trace_fin_one
  given: (A : Matrix (Fin 1) (Fin 1) R)
  statement: trace A = A 0 0
  proof: add_zero _

中文:
定理 trace_fin_one
  条件: (A : Matrix (Fin 1) (Fin 1) R)
  结论: trace A = A 0 0
  证明: add_zero _

Depends on / 依赖: add_zero
-/
theorem trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : trace A = A 0 0 :=
  add_zero _

/--
theorem `trace_fin_two` / 定理 `trace_fin_two`

English:
theorem trace_fin_two
  given: (A : Matrix (Fin 2) (Fin 2) R)
  statement: trace A = A 0 0 + A 1 1
  proof: congr_arg (_ + ·) (add_zero (A 1 1))

中文:
定理 trace_fin_two
  条件: (A : Matrix (Fin 2) (Fin 2) R)
  结论: trace A = A 0 0 + A 1 1
  证明: congr_arg (_ + ·) (add_zero (A 1 1))

Depends on / 依赖: add_zero, congr_arg
-/
theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1 :=
  congr_arg (_ + ·) (add_zero (A 1 1))

/--
theorem `trace_fin_three` / 定理 `trace_fin_three`

English:
theorem trace_fin_three
  given: (A : Matrix (Fin 3) (Fin 3) R)
  statement: trace A = A 0 0 + A 1 1 + A 2 2
  proof: by
  rw [← add_zero (A 2 2)]; rw [add_assoc]
  rfl

@[simp]

中文:
定理 trace_fin_three
  条件: (A : Matrix (Fin 3) (Fin 3) R)
  结论: trace A = A 0 0 + A 1 1 + A 2 2
  证明: by
  rw [← add_zero (A 2 2)]; rw [add_assoc]
  rfl

@[simp]

Depends on / 依赖: add_assoc, add_zero
-/
theorem trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 := by
  rw [← add_zero (A 2 2)]; rw [add_assoc]
  rfl

@[simp]
/--
theorem `trace_fin_one_of` / 定理 `trace_fin_one_of`

English:
theorem trace_fin_one_of
  given: (a : R)
  statement: trace !![a] = a
  proof: trace_fin_one _

@[simp]

中文:
定理 trace_fin_one_of
  条件: (a : R)
  结论: trace !![a] = a
  证明: trace_fin_one _

@[simp]

Depends on / 依赖: trace_fin_one
-/
theorem trace_fin_one_of (a : R) : trace !![a] = a :=
  trace_fin_one _

@[simp]
/--
theorem `trace_fin_two_of` / 定理 `trace_fin_two_of`

English:
theorem trace_fin_two_of
  given: (a b c d : R)
  statement: trace !![a, b; c, d] = a + d
  proof: trace_fin_two _

@[simp]

中文:
定理 trace_fin_two_of
  条件: (a b c d : R)
  结论: trace !![a, b; c, d] = a + d
  证明: trace_fin_two _

@[simp]

Depends on / 依赖: trace_fin_two
-/
theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d :=
  trace_fin_two _

@[simp]
/--
theorem `trace_fin_three_of` / 定理 `trace_fin_three_of`

English:
theorem trace_fin_three_of
  given: (a b c d e f g h i : R)
  proof: trace_fin_three _

中文:
定理 trace_fin_three_of
  条件: (a b c d e f g h i : R)
  证明: trace_fin_three _

Depends on / 依赖: trace_fin_three
-/
theorem trace_fin_three_of (a b c d e f g h i : R) :
    trace !![a, b, c; d, e, f; g, h, i] = a + e + i :=
  trace_fin_three _

end Fin

section single

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]
variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

@[simp]
/--
theorem `trace_single_eq_of_ne` / 定理 `trace_single_eq_of_ne`

English:
theorem trace_single_eq_of_ne
  given: (h : i != j)
  statement: trace (single i j c) = 0
  proof: by
  simp [trace, h]

@[simp]

中文:
定理 trace_single_eq_of_ne
  条件: (h : i != j)
  结论: trace (single i j c) = 0
  证明: by
  simp [trace, h]

@[simp]
-/
theorem trace_single_eq_of_ne (h : i != j) : trace (single i j c) = 0 := by
  simp [trace, h]

@[simp]
/--
theorem `trace_single_eq_same` / 定理 `trace_single_eq_same`

English:
theorem trace_single_eq_same
  statement: trace (single i i c) = c
  proof: by
  simp [trace]

中文:
定理 trace_single_eq_same
  结论: trace (single i i c) = c
  证明: by
  simp [trace]
-/
theorem trace_single_eq_same : trace (single i i c) = c := by
  simp [trace]

/--
theorem `trace_single_mul` / 定理 `trace_single_mul`

English:
theorem trace_single_mul
  statement: [NonUnitalNonAssocSemiring R] [Fintype m]
  proof: by
  simp [trace, mul_apply, single, ite_and]

中文:
定理 trace_single_mul
  结论: [NonUnitalNonAssocSemiring R] [Fintype m]
  证明: by
  simp [trace, mul_apply, single, ite_and]

Depends on / 依赖: ite_and, mul_apply, single
-/
theorem trace_single_mul [NonUnitalNonAssocSemiring R] [Fintype m]
    (i : n) (j : m) (a : R) (x : Matrix m n R) :
    (single i j a * x).trace = a • x j i := by
  simp [trace, mul_apply, single, ite_and]

/--
theorem `trace_mul_single` / 定理 `trace_mul_single`

English:
theorem trace_mul_single
  statement: [NonUnitalNonAssocSemiring R] [Fintype m]
  proof: by
  simp [trace, mul_apply, single, ite_and]

中文:
定理 trace_mul_single
  结论: [NonUnitalNonAssocSemiring R] [Fintype m]
  证明: by
  simp [trace, mul_apply, single, ite_and]

Depends on / 依赖: ite_and, mul_apply, single
-/
theorem trace_mul_single [NonUnitalNonAssocSemiring R] [Fintype m]
    (x : Matrix m n R) (i : n) (j : m) (a : R) :
    (x * single i j a).trace = MulOpposite.op a • x j i := by
  simp [trace, mul_apply, single, ite_and]

end single

/--
theorem `trace_surjective` / 定理 `trace_surjective`

English:
theorem trace_surjective
  given: [AddCommMonoid R] [Nonempty n]
  proof: fun r => by
  classical
  inhabit n
  exact ⟨single default default r, trace_single_eq_same default r⟩

中文:
定理 trace_surjective
  条件: [AddCommMonoid R] [Nonempty n]
  证明: fun r => by
  classical
  inhabit n
  exact ⟨single default default r, trace_single_eq_same default r⟩

Depends on / 依赖: classical, inhabit, single, trace_single_eq_same
-/
theorem trace_surjective [AddCommMonoid R] [Nonempty n] :
    Function.Surjective (trace : Matrix n n R -> R) := fun r => by
  classical
  inhabit n
  exact ⟨single default default r, trace_single_eq_same default r⟩

/--
theorem `ext_iff_trace_mul_left` / 定理 `ext_iff_trace_mul_left`

English:
theorem ext_iff_trace_mul_left
  given: [NonAssocSemiring R] {A B : Matrix m n R}
  proof: by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_single_mul] using h (single j i (1 : R))

中文:
定理 ext_iff_trace_mul_left
  条件: [NonAssocSemiring R] {A B : Matrix m n R}
  证明: by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_single_mul] using h (single j i (1 : R))

Depends on / 依赖: classical, single, trace_single_mul
-/
theorem ext_iff_trace_mul_left [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ forall x, (x * A).trace = (x * B).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_single_mul] using h (single j i (1 : R))

/--
theorem `ext_iff_trace_mul_right` / 定理 `ext_iff_trace_mul_right`

English:
theorem ext_iff_trace_mul_right
  given: [NonAssocSemiring R] {A B : Matrix m n R}
  proof: by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_mul_single] using h (single j i (1 : R))

中文:
定理 ext_iff_trace_mul_right
  条件: [NonAssocSemiring R] {A B : Matrix m n R}
  证明: by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_mul_single] using h (single j i (1 : R))

Depends on / 依赖: classical, single, trace_mul_single
-/
theorem ext_iff_trace_mul_right [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ forall x, (A * x).trace = (B * x).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_mul_single] using h (single j i (1 : R))

end Matrix
