/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Wen Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases

/-!
# Block matrices and their determinant

This file defines a predicate `Matrix.BlockTriangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

* `Matrix.BlockTriangular` expresses that an `o` by `o` matrix is block triangular,
  if the rows and columns are ordered according to some order `b : o → α`

## Main results

* `Matrix.det_of_blockTriangular`: the determinant of a block triangular matrix
  is equal to the product of the determinants of all the blocks
* `Matrix.det_of_isUpperTriangular` and `Matrix.det_of_isLowerTriangular`: the determinant of
  a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

@[expose] public section


open Finset Function OrderDual

open Matrix

universe v

variable {α β m n o : Type*} {m' n' : α -> Type*}
variable {R : Type v} {A : Type*} {M N : Matrix m m R} {b : m -> α}

namespace Matrix

section LT

variable [LT α]

section Zero

variable [Zero R]

/--
Definition of `BlockTriangular` / `BlockTriangular` 的定义

English:
definition BlockTriangular
  signature: (M : Matrix m m R) (b : m -> α)
  body: forall ⦃i j⦄, b j < b i -> M i j = 0

中文:
定义 BlockTriangular
  签名: (M : 矩阵 m m R) (b : m -> α)
  定义体: forall ⦃i j⦄, b j < b i -> M i j = 0
-/
def BlockTriangular (M : Matrix m m R) (b : m -> α) : Prop :=
  forall ⦃i j⦄, b j < b i -> M i j = 0

/--
Definition of `IsUpperTriangular` / `IsUpperTriangular` 的定义

English:
abbreviation IsUpperTriangular
  signature: [LT m] (M : Matrix m m R)
  body: M.BlockTriangular id

中文:
缩写 IsUpperTriangular
  签名: [LT m] (M : 矩阵 m m R)
  定义体: M.BlockTriangular id

Depends on / 依赖: BlockTriangular, M.BlockTriangular
-/
abbrev IsUpperTriangular [LT m] (M : Matrix m m R) : Prop :=
  M.BlockTriangular id

/--
Definition of `IsLowerTriangular` / `IsLowerTriangular` 的定义

English:
abbreviation IsLowerTriangular
  signature: [LT m] (M : Matrix m m R)
  body: M.BlockTriangular toDual

@[simp]

中文:
缩写 IsLowerTriangular
  签名: [LT m] (M : 矩阵 m m R)
  定义体: M.BlockTriangular toDual

@[simp]

Depends on / 依赖: BlockTriangular, M.BlockTriangular, toDual
-/
abbrev IsLowerTriangular [LT m] (M : Matrix m m R) : Prop :=
  M.BlockTriangular toDual

@[simp]
/--
theorem `BlockTriangular.submatrix` / 定理 `BlockTriangular.submatrix`

English:
theorem BlockTriangular.submatrix
  given: {f : n -> m} (h : M.BlockTriangular b)
  proof: fun _ _ hij => h hij

中文:
定理 BlockTriangular.submatrix
  条件: {f : n -> m} (h : M.BlockTriangular b)
  证明: fun _ _ hij => h hij
-/
protected theorem BlockTriangular.submatrix {f : n -> m} (h : M.BlockTriangular b) :
    (M.submatrix f f).BlockTriangular (b ∘ f) := fun _ _ hij => h hij

/--
theorem `blockTriangular_reindex_iff` / 定理 `blockTriangular_reindex_iff`

English:
theorem blockTriangular_reindex_iff
  given: {b : n -> α} {e : m ≃ n}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · convert! h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert! h.submatrix
    simp only [comp_assoc b e e.symm, Equiv.self_comp_symm, comp_id]

中文:
定理 blockTriangular_reindex_iff
  条件: {b : n -> α} {e : m ≃ n}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · convert! h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert! h.submatrix
    simp only [comp_assoc b e e.symm, Equiv.self_comp_symm, comp_id]

Depends on / 依赖: Equiv.self_comp_symm, Equiv.symm_comp_self, comp_assoc, comp_id, convert, e.symm, h.submatrix, reindex_apply, self_comp_symm, submatrix, submatrix_id_id, submatrix_submatrix, symm_comp_self
-/
theorem blockTriangular_reindex_iff {b : n -> α} {e : m ≃ n} :
    (reindex e e M).BlockTriangular b ↔ M.BlockTriangular (b ∘ e) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · convert! h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert! h.submatrix
    simp only [comp_assoc b e e.symm, Equiv.self_comp_symm, comp_id]

/--
theorem `BlockTriangular.transpose` / 定理 `BlockTriangular.transpose`

English:
theorem BlockTriangular.transpose
  proof: swap

@[simp]

中文:
定理 BlockTriangular.transpose
  证明: swap

@[simp]
-/
protected theorem BlockTriangular.transpose :
    M.BlockTriangular b -> Mᵀ.BlockTriangular (toDual ∘ b) :=
  swap

@[simp]
/--
theorem `blockTriangular_transpose_iff` / 定理 `blockTriangular_transpose_iff`

English:
theorem blockTriangular_transpose_iff
  given: {b : m -> αᵒᵈ}
  proof: forall_comm

@[simp]

中文:
定理 blockTriangular_transpose_iff
  条件: {b : m -> αᵒᵈ}
  证明: forall_comm

@[simp]
-/
protected theorem blockTriangular_transpose_iff {b : m -> αᵒᵈ} :
    Mᵀ.BlockTriangular b ↔ M.BlockTriangular (ofDual ∘ b) :=
  forall_comm

@[simp]
/--
theorem `blockTriangular_zero` / 定理 `blockTriangular_zero`

English:
theorem blockTriangular_zero
  statement: BlockTriangular (0 : Matrix m m R) b
  proof: fun _ _ _ => rfl

中文:
定理 blockTriangular_zero
  结论: BlockTriangular (0 : 矩阵 m m R) b
  证明: fun _ _ _ => rfl
-/
theorem blockTriangular_zero : BlockTriangular (0 : Matrix m m R) b := fun _ _ _ => rfl

/--
Instance `decidableBlockTriangular` / 实例 `decidableBlockTriangular`

English:
instance decidableBlockTriangular
  signature: [DecidableEq R] [Fintype m] [DecidableLT α]
  body: decidable_of_iff (forall ij : m × m, b ij.2 < b ij.1 -> M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

中文:
实例 decidableBlockTriangular
  签名: [DecidableEq R] [有限类型 m] [DecidableLT α]
  定义体: decidable_of_iff (forall ij : m × m, b ij.2 < b ij.1 -> M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

Depends on / 依赖: decidable_of_iff
-/
instance decidableBlockTriangular [DecidableEq R] [Fintype m] [DecidableLT α] :
    Decidable (M.BlockTriangular b) :=
  decidable_of_iff (forall ij : m × m, b ij.2 < b ij.1 -> M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

end Zero

/--
theorem `BlockTriangular.neg` / 定理 `BlockTriangular.neg`

English:
theorem BlockTriangular.neg
  statement: [NegZeroClass R] {M : Matrix m m R}
  proof: fun _ _ h => by rw [neg_apply, hM h, neg_zero]

中文:
定理 BlockTriangular.neg
  结论: [NegZero类 R] {M : 矩阵 m m R}
  证明: fun _ _ h => by rw [neg_apply, hM h, neg_zero]
-/
protected theorem BlockTriangular.neg [NegZeroClass R] {M : Matrix m m R}
    (hM : BlockTriangular M b) : BlockTriangular (-M) b :=
  fun _ _ h => by rw [neg_apply, hM h, neg_zero]

/--
theorem `BlockTriangular.add` / 定理 `BlockTriangular.add`

English:
theorem BlockTriangular.add
  given: [AddZeroClass R] (hM : BlockTriangular M b) (hN : BlockTriangular N b)
  proof: fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]

中文:
定理 BlockTriangular.add
  条件: [加法零类 R] (hM : BlockTriangular M b) (hN : BlockTriangular N b)
  证明: fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]

Depends on / 依赖: Matrix, Matrix.add_apply, add_apply, simp_rw, zero_add
-/
theorem BlockTriangular.add [AddZeroClass R] (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M + N) b := fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]

/--
theorem `BlockTriangular.sub` / 定理 `BlockTriangular.sub`

English:
theorem BlockTriangular.sub
  statement: [SubNegZeroMonoid R]
  proof: fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]

中文:
定理 BlockTriangular.sub
  结论: [SubNegZero幺半群 R]
  证明: fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]

Depends on / 依赖: Matrix, Matrix.sub_apply, simp_rw, sub_apply, sub_zero
-/
theorem BlockTriangular.sub [SubNegZeroMonoid R]
    (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b := fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]

/--
lemma `BlockTriangular.add_iff_right` / 引理 `BlockTriangular.add_iff_right`

English:
lemma BlockTriangular.add_iff_right
  given: [AddGroup R] (hM : BlockTriangular M b)
  proof: ⟨(by simpa using hM.neg.add ·), hM.add⟩

中文:
引理 BlockTriangular.add_iff_right
  条件: [加法群 R] (hM : BlockTriangular M b)
  证明: ⟨(by simpa using hM.neg.add ·), hM.add⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.extend_eq, denseRange, extend_eq, hM.add, hM.neg.add, isUniformInducing, one_ne_top, simpleFunc, simpleFunc.denseRange, simpleFunc.isUniformInducing
-/
lemma BlockTriangular.add_iff_right [AddGroup R] (hM : BlockTriangular M b) :
    BlockTriangular (M + N) b ↔ BlockTriangular N b := ⟨(by simpa using hM.neg.add ·), hM.add⟩

/--
lemma `BlockTriangular.add_iff_left` / 引理 `BlockTriangular.add_iff_left`

English:
lemma BlockTriangular.add_iff_left
  given: [AddGroup R] (hN : BlockTriangular N b)
  proof: ⟨(by simpa using ·.sub hN), (·.add hN)⟩

中文:
引理 BlockTriangular.add_iff_left
  条件: [加法群 R] (hN : BlockTriangular N b)
  证明: ⟨(by simpa using ·.sub hN), (·.add hN)⟩

Depends on / 依赖: _eq_setToL1SCLM, h_smul, setToL1
-/
lemma BlockTriangular.add_iff_left [AddGroup R] (hN : BlockTriangular N b) :
    BlockTriangular (M + N) b ↔ BlockTriangular M b := ⟨(by simpa using ·.sub hN), (·.add hN)⟩

/--
lemma `BlockTriangular.sub_iff_right` / 引理 `BlockTriangular.sub_iff_right`

English:
lemma BlockTriangular.sub_iff_right
  given: [AddGroup R] (hM : BlockTriangular M b)
  proof: ⟨(by simpa using ·.neg.add hM), hM.sub⟩

中文:
引理 BlockTriangular.sub_iff_right
  条件: [加法群 R] (hM : BlockTriangular M b)
  证明: ⟨(by simpa using ·.neg.add hM), hM.sub⟩

Depends on / 依赖: hM.sub, neg.add
-/
lemma BlockTriangular.sub_iff_right [AddGroup R] (hM : BlockTriangular M b) :
    BlockTriangular (M - N) b ↔ BlockTriangular N b := ⟨(by simpa using ·.neg.add hM), hM.sub⟩

/--
lemma `BlockTriangular.sub_iff_left` / 引理 `BlockTriangular.sub_iff_left`

English:
lemma BlockTriangular.sub_iff_left
  given: [AddGroup R] (hN : BlockTriangular N b)
  proof: ⟨(by simpa using ·.add hN), (·.sub hN)⟩

中文:
引理 BlockTriangular.sub_iff_left
  条件: [加法群 R] (hN : BlockTriangular N b)
  证明: ⟨(by simpa using ·.add hN), (·.sub hN)⟩
-/
lemma BlockTriangular.sub_iff_left [AddGroup R] (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b ↔ BlockTriangular M b := ⟨(by simpa using ·.add hN), (·.sub hN)⟩

/--
lemma `BlockTriangular.map` / 引理 `BlockTriangular.map`

English:
lemma BlockTriangular.map
  statement: {S F} [FunLike F R S] [Zero R] [Zero S] [ZeroHomClass F R S] (f : F)
  proof: fun i j lt => by simp [h lt]

中文:
引理 BlockTriangular.map
  结论: {S F} [函数状 F R S] [零 R] [零 S] [保零态射类 F R S] (f : F)
  证明: fun i j lt => by simp [h lt]
-/
lemma BlockTriangular.map {S F} [FunLike F R S] [Zero R] [Zero S] [ZeroHomClass F R S] (f : F)
    (h : BlockTriangular M b) : BlockTriangular (M.map f) b :=
  fun i j lt => by simp [h lt]

/--
lemma `BlockTriangular.comp` / 引理 `BlockTriangular.comp`

English:
lemma BlockTriangular.comp
  given: [Zero R] {M : Matrix m m (Matrix n n R)} (h : BlockTriangular M b)
  proof: fun i j lt => by simp [h lt]

中文:
引理 BlockTriangular.comp
  条件: [零 R] {M : 矩阵 m m (矩阵 n n R)} (h : BlockTriangular M b)
  证明: fun i j lt => by simp [h lt]
-/
lemma BlockTriangular.comp [Zero R] {M : Matrix m m (Matrix n n R)} (h : BlockTriangular M b) :
    BlockTriangular (M.comp m m n n R) fun i => b i.1 :=
  fun i j lt => by simp [h lt]

end LT

section Preorder

variable [Preorder α]

section Zero

variable [Zero R]

/--
theorem `blockTriangular_diagonal` / 定理 `blockTriangular_diagonal`

English:
theorem blockTriangular_diagonal
  given: [DecidableEq m] (d : m -> R)
  statement: BlockTriangular (diagonal d) b
  proof: fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')

中文:
定理 blockTriangular_diagonal
  条件: [DecidableEq m] (d : m -> R)
  结论: BlockTriangular (diagonal d) b
  证明: fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')

Depends on / 依赖: congr_arg, diagonal_apply_ne, ne_of_lt
-/
theorem blockTriangular_diagonal [DecidableEq m] (d : m -> R) : BlockTriangular (diagonal d) b :=
  fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')

/--
theorem `blockTriangular_blockDiagonal'` / 定理 `blockTriangular_blockDiagonal'`

English:
theorem blockTriangular_blockDiagonal'
  given: [DecidableEq α] (d : forall i : α, Matrix (m' i) (m' i) R)
  proof: by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm

中文:
定理 blockTriangular_blockDiagonal'
  条件: [DecidableEq α] (d : 对任意 i : α, 矩阵 (m' i) (m' i) R)
  证明: by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm

Depends on / 依赖: _apply_ne, blockDiagonal, ne_of_lt
-/
theorem blockTriangular_blockDiagonal' [DecidableEq α] (d : forall i : α, Matrix (m' i) (m' i) R) :
    BlockTriangular (blockDiagonal' d) Sigma.fst := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm

/--
theorem `blockTriangular_blockDiagonal` / 定理 `blockTriangular_blockDiagonal`

English:
theorem blockTriangular_blockDiagonal
  given: [DecidableEq α] (d : α -> Matrix m m R)
  proof: by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal]; rw [blockTriangular_blockDiagonal']
  exact h

中文:
定理 blockTriangular_blockDiagonal
  条件: [DecidableEq α] (d : α -> 矩阵 m m R)
  证明: by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal]; rw [blockTriangular_blockDiagonal']
  exact h

Depends on / 依赖: _eq_blockDiagonal, blockDiagonal, blockTriangular_blockDiagonal
-/
theorem blockTriangular_blockDiagonal [DecidableEq α] (d : α -> Matrix m m R) :
    BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal]; rw [blockTriangular_blockDiagonal']
  exact h

variable [DecidableEq m]

/--
theorem `blockTriangular_one` / 定理 `blockTriangular_one`

English:
theorem blockTriangular_one
  given: [One R]
  statement: BlockTriangular (1 : Matrix m m R) b
  proof: blockTriangular_diagonal _

中文:
定理 blockTriangular_one
  条件: [幺 R]
  结论: BlockTriangular (1 : 矩阵 m m R) b
  证明: blockTriangular_diagonal _

Depends on / 依赖: blockTriangular_diagonal
-/
theorem blockTriangular_one [One R] : BlockTriangular (1 : Matrix m m R) b :=
  blockTriangular_diagonal _

/--
theorem `blockTriangular_single` / 定理 `blockTriangular_single`

English:
theorem blockTriangular_single
  given: {i j : m} (hij : b i <= b j) (c : R)
  proof: by
  intro r s hrs
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false

中文:
定理 blockTriangular_single
  条件: {i j : m} (hij : b i <= b j) (c : R)
  证明: by
  intro r s hrs
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false

Depends on / 依赖: hij.trans_lt, single_apply_of_ne, trans_lt
-/
theorem blockTriangular_single {i j : m} (hij : b i <= b j) (c : R) :
    BlockTriangular (single i j c) b := by
  intro r s hrs
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false

/--
theorem `blockTriangular_single'` / 定理 `blockTriangular_single'`

English:
theorem blockTriangular_single'
  given: {i j : m} (hij : b j <= b i) (c : R)
  proof: blockTriangular_single (by exact toDual_le_toDual.mpr hij) _

中文:
定理 blockTriangular_single'
  条件: {i j : m} (hij : b j <= b i) (c : R)
  证明: blockTriangular_single (by exact toDual_le_toDual.mpr hij) _

Depends on / 依赖: blockTriangular_single, toDual_le_toDual, toDual_le_toDual.mpr
-/
theorem blockTriangular_single' {i j : m} (hij : b j <= b i) (c : R) :
    BlockTriangular (single i j c) (toDual ∘ b) :=
  blockTriangular_single (by exact toDual_le_toDual.mpr hij) _

end Zero

variable [CommRing R] [DecidableEq m]

/--
theorem `blockTriangular_transvection` / 定理 `blockTriangular_transvection`

English:
theorem blockTriangular_transvection
  given: {i j : m} (hij : b i <= b j) (c : R)
  proof: blockTriangular_one.add (blockTriangular_single hij c)

中文:
定理 blockTriangular_transvection
  条件: {i j : m} (hij : b i <= b j) (c : R)
  证明: blockTriangular_one.add (blockTriangular_single hij c)

Depends on / 依赖: blockTriangular_one, blockTriangular_one.add, blockTriangular_single
-/
theorem blockTriangular_transvection {i j : m} (hij : b i <= b j) (c : R) :
    BlockTriangular (transvection i j c) b :=
  blockTriangular_one.add (blockTriangular_single hij c)

/--
theorem `blockTriangular_transvection'` / 定理 `blockTriangular_transvection'`

English:
theorem blockTriangular_transvection'
  given: {i j : m} (hij : b j <= b i) (c : R)
  proof: blockTriangular_one.add (blockTriangular_single' hij c)

中文:
定理 blockTriangular_transvection'
  条件: {i j : m} (hij : b j <= b i) (c : R)
  证明: blockTriangular_one.add (blockTriangular_single' hij c)

Depends on / 依赖: blockTriangular_one, blockTriangular_one.add, blockTriangular_single
-/
theorem blockTriangular_transvection' {i j : m} (hij : b j <= b i) (c : R) :
    BlockTriangular (transvection i j c) (OrderDual.toDual ∘ b) :=
  blockTriangular_one.add (blockTriangular_single' hij c)

end Preorder

section LinearOrder

variable [LinearOrder α]

/--
theorem `BlockTriangular.mul` / 定理 `BlockTriangular.mul`

English:
theorem BlockTriangular.mul
  statement: [Fintype m] [NonUnitalNonAssocSemiring R]
  proof: by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

中文:
定理 BlockTriangular.mul
  结论: [有限类型 m] [非幺非结合半环 R]
  证明: by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

Depends on / 依赖: Finset, Finset.sum_eq_zero, lt_of_lt_of_le, mul_zero, simp_rw, sum_eq_zero, zero_mul
-/
theorem BlockTriangular.mul [Fintype m] [NonUnitalNonAssocSemiring R]
    {M N : Matrix m m R} (hM : BlockTriangular M b)
    (hN : BlockTriangular N b) : BlockTriangular (M * N) b := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

variable (R b) in
/-- `BlockTriangular` matrices form a subsemiring. -/
@[simps]
/--
Definition of `blockTriangularSubsemiring` / `blockTriangularSubsemiring` 的定义

English:
definition blockTriangularSubsemiring
  signature: [DecidableEq m] [Fintype m] [Semiring R]
  body: {M | BlockTriangular M b}
  zero_mem' := blockTriangular_zero
  one_mem' := blockTriangular_one
  mul_mem' := .mul
  add_mem' := .add

@[simp]

中文:
定义 blockTriangularSubsemiring
  签名: [DecidableEq m] [有限类型 m] [半环 R]
  定义体: {M | BlockTriangular M b}
  zero_mem' := blockTriangular_zero
  one_mem' := blockTriangular_one
  mul_mem' := .mul
  add_mem' := .add

@[simp]

Depends on / 依赖: BlockTriangular
-/
def blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R] :
    Subsemiring (Matrix m m R) where
  carrier := {M | BlockTriangular M b}
  zero_mem' := blockTriangular_zero
  one_mem' := blockTriangular_one
  mul_mem' := .mul
  add_mem' := .add

@[simp]
/--
theorem `mem_blockTriangularSubsemiring` / 定理 `mem_blockTriangularSubsemiring`

English:
theorem mem_blockTriangularSubsemiring
  statement: [DecidableEq m] [Fintype m] [Semiring R]
  proof: Iff.rfl

中文:
定理 mem_blockTriangularSubsemiring
  结论: [DecidableEq m] [有限类型 m] [半环 R]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_blockTriangularSubsemiring [DecidableEq m] [Fintype m] [Semiring R]
    {M : Matrix m m R} :
    M in blockTriangularSubsemiring R b ↔ BlockTriangular M b :=
  Iff.rfl

/--
theorem `BlockTriangular.pow` / 定理 `BlockTriangular.pow`

English:
theorem BlockTriangular.pow
  statement: [DecidableEq m] [Fintype m] [Semiring R] (hM : BlockTriangular M b)
  proof: pow_mem (S := blockTriangularSubsemiring R b) hM n

中文:
定理 BlockTriangular.pow
  结论: [DecidableEq m] [有限类型 m] [半环 R] (hM : BlockTriangular M b)
  证明: pow_mem (S := blockTriangularSubsemiring R b) hM n

Depends on / 依赖: blockTriangularSubsemiring, pow_mem
-/
theorem BlockTriangular.pow [DecidableEq m] [Fintype m] [Semiring R] (hM : BlockTriangular M b)
    (n : Nat) : BlockTriangular (M ^ n) b :=
  pow_mem (S := blockTriangularSubsemiring R b) hM n

/--
theorem `blockTriangular_algebraMap` / 定理 `blockTriangular_algebraMap`

English:
theorem blockTriangular_algebraMap
  statement: [CommSemiring R] [Semiring A] [Algebra R A]
  proof: blockTriangular_diagonal _

中文:
定理 blockTriangular_algebraMap
  结论: [交换半环 R] [半环 A] [代数 R A]
  证明: blockTriangular_diagonal _

Depends on / 依赖: blockTriangular_diagonal
-/
theorem blockTriangular_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] (r : R) : (algebraMap R (Matrix m m A) r).BlockTriangular b :=
  blockTriangular_diagonal _

variable (R A b) in
/--
Definition of `blockTriangularSubalgebra` / `blockTriangularSubalgebra` 的定义

English:
definition blockTriangularSubalgebra
  signature: [CommSemiring R] [Semiring A] [Algebra R A]
  body: blockTriangularSubsemiring A b
  algebraMap_mem' r := blockTriangular_algebraMap r

@[simp]

中文:
定义 blockTriangularSubalgebra
  签名: [交换半环 R] [半环 A] [代数 R A]
  定义体: blockTriangularSubsemiring A b
  algebraMap_mem' r := blockTriangular_algebraMap r

@[simp]

Depends on / 依赖: blockTriangularSubsemiring
-/
def blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] : Subalgebra R (Matrix m m A) where
  __ := blockTriangularSubsemiring A b
  algebraMap_mem' r := blockTriangular_algebraMap r

@[simp]
/--
theorem `mem_blockTriangularSubalgebra` / 定理 `mem_blockTriangularSubalgebra`

English:
theorem mem_blockTriangularSubalgebra
  statement: [CommSemiring R] [Semiring A] [Algebra R A]
  proof: Iff.rfl

中文:
定理 mem_blockTriangularSubalgebra
  结论: [交换半环 R] [半环 A] [代数 R A]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_blockTriangularSubalgebra [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq m] [Fintype m] {M : Matrix m m A} :
    M in blockTriangularSubalgebra R A b ↔ BlockTriangular M b :=
  Iff.rfl

end LinearOrder

/--
theorem `upper_two_blockTriangular` / 定理 `upper_two_blockTriangular`

English:
theorem upper_two_blockTriangular
  statement: [Zero R] [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
  proof: by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_gt] at hcd ⊢

中文:
定理 upper_two_blockTriangular
  结论: [零 R] [预序 α] (A : 矩阵 m m R) (B : 矩阵 m n R)
  证明: by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_gt] at hcd ⊢

Depends on / 依赖: hab.not_gt, not_gt
-/
theorem upper_two_blockTriangular [Zero R] [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) {a b : α} (hab : a < b) :
    BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b) := by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_gt] at hcd ⊢

/-! ### Determinant -/


variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

/--
theorem `equiv_block_det` / 定理 `equiv_block_det`

English:
theorem equiv_block_det
  statement: (M : Matrix m m R) {p q : m -> Prop} [DecidablePred p] [DecidablePred q]
  proof: by
  convert!
    Matrix.det_reindex_self (Equiv.subtypeEquivRight e)
      (toSquareBlockProp M q)
        -- Removed `@[simp]` attribute,
        -- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`

中文:
定理 equiv_block_det
  结论: (M : 矩阵 m m R) {p q : m -> 命题} [DecidablePred p] [DecidablePred q]
  证明: by
  convert!
    Matrix.det_reindex_self (Equiv.subtypeEquivRight e)
      (toSquareBlockProp M q)
        -- Removed `@[simp]` attribute,
        -- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`

Depends on / 依赖: Equiv.subtypeEquivRight, Matrix, Matrix.det_reindex_self, convert, det_reindex_self, subtypeEquivRight, toSquareBlockProp
-/
theorem equiv_block_det (M : Matrix m m R) {p q : m -> Prop} [DecidablePred p] [DecidablePred q]
    (e : forall x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert!
    Matrix.det_reindex_self (Equiv.subtypeEquivRight e)
      (toSquareBlockProp M q)
        -- Removed `@[simp]` attribute,
        -- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`


-- Removed `@[simp]` attribute,
-- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`
/--
theorem `det_toSquareBlock_id` / 定理 `det_toSquareBlock_id`

English:
theorem det_toSquareBlock_id
  given: (M : Matrix m m R) (i : m)
  statement: (M.toSquareBlock id i).det = M i i
  proof: letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl

中文:
定理 det_toSquareBlock_id
  条件: (M : 矩阵 m m R) (i : m)
  结论: (M.toSquareBlock id i).det = M i i
  证明: letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl

Depends on / 依赖: Subtype, Subtype.ext, Unique, det_unique, j.property, property
-/
theorem det_toSquareBlock_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).det = M i i :=
  letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl

/--
theorem `det_toBlock` / 定理 `det_toBlock`

English:
theorem det_toBlock
  given: (M : Matrix m m R) (p : m -> Prop) [DecidablePred p]
  proof: by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply']; rw [det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_

中文:
定理 det_toBlock
  条件: (M : 矩阵 m m R) (p : m -> 命题) [DecidablePred p]
  证明: by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply']; rw [det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_

Depends on / 依赖: Equiv.sumCompl, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Equiv.symm_symm, Matrix, Matrix.det_reindex_self, Matrix.reindex_apply, Matrix.submatrix_apply, det_apply, det_reindex_self, generalize, reindex_apply, submatrix_apply, sumCompl, sumCompl_apply_inl, sumCompl_apply_inr, symm_symm, toBlock_apply
-/
theorem det_toBlock (M : Matrix m m R) (p : m -> Prop) [DecidablePred p] :
    M.det =
      (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p j) p) <|
          toBlock M (fun j => ¬p j) fun j => ¬p j).det := by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply']; rw [det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.submatrix_apply]

/--
theorem `twoBlockTriangular_det` / 定理 `twoBlockTriangular_det`

English:
theorem twoBlockTriangular_det
  statement: (M : Matrix m m R) (p : m -> Prop) [DecidablePred p]
  proof: by
  rw [det_toBlock M p]
  convert!
    det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2

中文:
定理 twoBlockTriangular_det
  结论: (M : 矩阵 m m R) (p : m -> 命题) [DecidablePred p]
  证明: by
  rw [det_toBlock M p]
  convert!
    det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2

Depends on / 依赖: convert, det_toBlock, toBlock
-/
theorem twoBlockTriangular_det (M : Matrix m m R) (p : m -> Prop) [DecidablePred p]
    (h : forall i, ¬p i -> forall j, p j -> M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_toBlock M p]
  convert!
    det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2

/--
theorem `twoBlockTriangular_det'` / 定理 `twoBlockTriangular_det'`

English:
theorem twoBlockTriangular_det'
  statement: (M : Matrix m m R) (p : m -> Prop) [DecidablePred p]
  proof: by
  rw [M.twoBlockTriangular_det fun i => ¬p i]; rw [mul_comm]
  · congr 1
    exact equiv_block_det _ fun _ => not_not.symm
  · simpa only [Classical.not_not] using h

中文:
定理 twoBlockTriangular_det'
  结论: (M : 矩阵 m m R) (p : m -> 命题) [DecidablePred p]
  证明: by
  rw [M.twoBlockTriangular_det fun i => ¬p i]; rw [mul_comm]
  · congr 1
    exact equiv_block_det _ fun _ => not_not.symm
  · simpa only [Classical.not_not] using h

Depends on / 依赖: Classical, Classical.not_not, M.twoBlockTriangular_det, equiv_block_det, mul_comm, not_not, not_not.symm, twoBlockTriangular_det
-/
theorem twoBlockTriangular_det' (M : Matrix m m R) (p : m -> Prop) [DecidablePred p]
    (h : forall i, p i -> forall j, ¬p j -> M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [M.twoBlockTriangular_det fun i => ¬p i]; rw [mul_comm]
  · congr 1
    exact equiv_block_det _ fun _ => not_not.symm
  · simpa only [Classical.not_not] using h

/--
theorem `BlockTriangular.det` / 定理 `BlockTriangular.det`

English:
theorem BlockTriangular.det
  given: [DecidableEq α] [LinearOrder α] (hM : BlockTriangular M b)
  proof: by
  suffices forall hs : Finset α, univ.image b = hs -> M.det = ∏ a in hs, (M.toSquareBlock b a).det by
    exact this _ rfl
  intro s hs
  induction s using Finset.eraseInduction generalizing m with | H s ih =>
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (univ.image b).max' (univ_

中文:
定理 BlockTriangular.det
  条件: [DecidableEq α] [线性序 α] (hM : BlockTriangular M b)
  证明: by
  suffices forall hs : Finset α, univ.image b = hs -> M.det = ∏ a in hs, (M.toSquareBlock b a).det by
    exact this _ rfl
  intro s hs
  induction s using Finset.eraseInduction generalizing m with | H s ih =>
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (univ.image b).max' (univ_
-/
protected theorem BlockTriangular.det [DecidableEq α] [LinearOrder α] (hM : BlockTriangular M b) :
    M.det = ∏ a in univ.image b, (M.toSquareBlock b a).det := by
  suffices forall hs : Finset α, univ.image b = hs -> M.det = ∏ a in hs, (M.toSquareBlock b a).det by
    exact this _ rfl
  intro s hs
  induction s using Finset.eraseInduction generalizing m with | H s ih =>
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (univ.image b).max' (univ_nonempty.image _)
  rw [twoBlockTriangular_det' M fun i => b i = k]
  · have : univ.image b = insert k ((univ.image b).erase k) := by
      rw [insert_erase]
      apply max'_mem
    rw [this]; rw [prod_insert (notMem_erase _ _)]
    refine congr_arg _ ?_
    let b' := fun i : { a // b a != k } => b ↑i
    have h' : BlockTriangular (M.toSquareBlockProp fun i => b i != k) b' := hM.submatrix
    have hb' : image b' univ = (image b univ).erase k := by
      convert! image_subtype_ne_univ_eq_image_erase k b
    rw [ih _ (max'_mem _ _) h' hb']
    refine Finset.prod_congr rfl fun l hl => ?_
    let he : { a // b' a = l } ≃ { a // b a = l } :=
      haveI hc : forall i, b i = l -> b i != k := fun i hi => ne_of_eq_of_ne hi (ne_of_mem_erase hl)
      Equiv.subtypeSubtypeEquivSubtype @hc
    rw [toSquareBlock_def]; rw [← Matrix.det_reindex_self he.symm]
    rfl
  · intro i hi j hj
    apply hM
    rw [hi]
    apply lt_of_le_of_ne _ hj
    exact Finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _))

/--
theorem `BlockTriangular.det_fintype` / 定理 `BlockTriangular.det_fintype`

English:
theorem BlockTriangular.det_fintype
  statement: [DecidableEq α] [Fintype α] [LinearOrder α]
  proof: by
  refine h.det.trans (prod_subset (subset_univ _) fun a _ ha => ?_)
have : IsEmpty { i // b i = a } := ⟨fun i => ha mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty

中文:
定理 BlockTriangular.det_fintype
  结论: [DecidableEq α] [有限类型 α] [线性序 α]
  证明: by
  refine h.det.trans (prod_subset (subset_univ _) fun a _ ha => ?_)
have : IsEmpty { i // b i = a } := ⟨fun i => ha mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty

Depends on / 依赖: IsEmpty, det_isEmpty, h.det.trans, mem_image, mem_univ, prod_subset, subset_univ
-/
theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrder α]
    (h : BlockTriangular M b) : M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine h.det.trans (prod_subset (subset_univ _) fun a _ ha => ?_)
have : IsEmpty { i // b i = a } := ⟨fun i => ha mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty

/--
theorem `det_of_isUpperTriangular` / 定理 `det_of_isUpperTriangular`

English:
theorem det_of_isUpperTriangular
  given: [LinearOrder m] (h : M.IsUpperTriangular)
  proof: by
  have : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_toSquareBlock_id]

@[deprecated (since := "2026-07-30")] alias det_of_upperTriangular := det_of_isUpperTriangular

中文:
定理 det_of_isUpperTriangular
  条件: [线性序 m] (h : M.IsUpperTriangular)
  证明: by
  have : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_toSquareBlock_id]

@[deprecated (since := "2026-07-30")] alias det_of_upperTriangular := det_of_isUpperTriangular

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, det_toSquareBlock_id, h.det, image_id, simp_rw
-/
theorem det_of_isUpperTriangular [LinearOrder m] (h : M.IsUpperTriangular) :
    M.det = ∏ i : m, M i i := by
  have : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_toSquareBlock_id]

@[deprecated (since := "2026-07-30")] alias det_of_upperTriangular := det_of_isUpperTriangular

/--
theorem `det_of_isLowerTriangular` / 定理 `det_of_isLowerTriangular`

English:
theorem det_of_isLowerTriangular
  given: [LinearOrder m] (M : Matrix m m R) (h : M.IsLowerTriangular)
  proof: by
  rw [← det_transpose]
  exact det_of_isUpperTriangular h.transpose

@[deprecated (since := "2026-07-30")] alias det_of_lowerTriangular := det_of_isLowerTriangular

中文:
定理 det_of_isLowerTriangular
  条件: [线性序 m] (M : 矩阵 m m R) (h : M.IsLowerTriangular)
  证明: by
  rw [← det_transpose]
  exact det_of_isUpperTriangular h.transpose

@[deprecated (since := "2026-07-30")] alias det_of_lowerTriangular := det_of_isLowerTriangular

Depends on / 依赖: det_of_isUpperTriangular, det_transpose, h.transpose, transpose
-/
theorem det_of_isLowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.IsLowerTriangular) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact det_of_isUpperTriangular h.transpose

@[deprecated (since := "2026-07-30")] alias det_of_lowerTriangular := det_of_isLowerTriangular

open Polynomial

/--
theorem `matrixOfPolynomials_blockTriangular` / 定理 `matrixOfPolynomials_blockTriangular`

English:
theorem matrixOfPolynomials_blockTriangular
  statement: {R} [Semiring R] {n : Nat} (p : Fin n -> R[X])
  proof: fun _ j h => by
exact coeff_eq_zero_of_natDegree_lt Nat.lt_of_le_of_lt (h_deg j) h

中文:
定理 matrixOfPolynomials_blockTriangular
  结论: {R} [半环 R] {n : 自然数} (p : 有限集 n -> R[X])
  证明: fun _ j h => by
exact coeff_eq_zero_of_natDegree_lt Nat.lt_of_le_of_lt (h_deg j) h

Depends on / 依赖: Nat.lt_of_le_of_lt, coeff_eq_zero_of_natDegree_lt, h_deg, lt_of_le_of_lt
-/
theorem matrixOfPolynomials_blockTriangular {R} [Semiring R] {n : Nat} (p : Fin n -> R[X])
    (h_deg : forall i, (p i).natDegree <= i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id :=
  fun _ j h => by
exact coeff_eq_zero_of_natDegree_lt Nat.lt_of_le_of_lt (h_deg j) h

/--
theorem `det_matrixOfPolynomials` / 定理 `det_matrixOfPolynomials`

English:
theorem det_matrixOfPolynomials
  statement: {n : Nat} (p : Fin n -> R[X])
  proof: by
  rw [Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p (fun i =>
      Nat.le_of_eq (h_deg i)))]
  convert! prod_const_one with x _
  rw [Matrix.of_apply]; rw [← h_deg]; rw [coeff_natDegree]; rw [(h_monic x).leadingCoeff]

中文:
定理 det_matrixOfPolynomials
  结论: {n : 自然数} (p : 有限集 n -> R[X])
  证明: by
  rw [Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p (fun i =>
      Nat.le_of_eq (h_deg i)))]
  convert! prod_const_one with x _
  rw [Matrix.of_apply]; rw [← h_deg]; rw [coeff_natDegree]; rw [(h_monic x).leadingCoeff]

Depends on / 依赖: Matrix, Matrix.det_of_isUpperTriangular, Matrix.matrixOfPolynomials_blockTriangular, Matrix.of_apply, Nat.le_of_eq, coeff_natDegree, convert, det_of_isUpperTriangular, h_deg, h_monic, le_of_eq, leadingCoeff, matrixOfPolynomials_blockTriangular, of_apply, prod_const_one
-/
theorem det_matrixOfPolynomials {n : Nat} (p : Fin n -> R[X])
    (h_deg : forall i, (p i).natDegree = i) (h_monic : forall i, Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p (fun i =>
      Nat.le_of_eq (h_deg i)))]
  convert! prod_const_one with x _
  rw [Matrix.of_apply]; rw [← h_deg]; rw [coeff_natDegree]; rw [(h_monic x).leadingCoeff]



/--
theorem `BlockTriangular.toBlock_inverse_mul_toBlock_eq_one` / 定理 `BlockTriangular.toBlock_inverse_mul_toBlock_eq_one`

English:
theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one
  statement: [LinearOrder α] [Invertible M]
  proof: by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
  

中文:
定理 BlockTriangular.toBlock_inverse_mul_toBlock_eq_one
  结论: [线性序 α] [可逆 M]
  证明: by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
  

Depends on / 依赖: M.toBlock, h_sum, h_zero, inv_mul_of_invertible, le_of_not_gt, lt_of_lt_of_le, toBlock, toBlock_mul_eq_add, toBlock_one_self
-/
theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) (k : α) :
    ((M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) *
        M.toBlock (fun i => b i < k) fun i => b i < k) =
      1 := by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_gt i.2))
  simpa [h_zero] using h_sum

/--
theorem `BlockTriangular.inv_toBlock` / 定理 `BlockTriangular.inv_toBlock`

English:
theorem BlockTriangular.inv_toBlock
  statement: [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
  proof: inv_eq_left_inv hM.toBlock_inverse_mul_toBlock_eq_one k

中文:
定理 BlockTriangular.inv_toBlock
  结论: [线性序 α] [可逆 M] (hM : BlockTriangular M b)
  证明: inv_eq_left_inv hM.toBlock_inverse_mul_toBlock_eq_one k

Depends on / 依赖: hM.toBlock_inverse_mul_toBlock_eq_one, inv_eq_left_inv, toBlock_inverse_mul_toBlock_eq_one
-/
theorem BlockTriangular.inv_toBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) :
    (M.toBlock (fun i => b i < k) fun i => b i < k)⁻¹ =
      M⁻¹.toBlock (fun i => b i < k) fun i => b i < k :=
inv_eq_left_inv hM.toBlock_inverse_mul_toBlock_eq_one k

/-- An upper-left subblock of an invertible block-triangular matrix is invertible. -/
@[instance_reducible]
/--
Definition of `BlockTriangular.invertibleToBlock` / `BlockTriangular.invertibleToBlock` 的定义

English:
definition BlockTriangular.invertibleToBlock
  signature: [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
  body: invertibleOfLeftInverse _ ((⅟M).toBlock (fun i => b i < k) fun i => b i < k) by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k

中文:
定义 BlockTriangular.invertibleToBlock
  签名: [线性序 α] [可逆 M] (hM : BlockTriangular M b)
  定义体: invertibleOfLeftInverse _ ((⅟M).toBlock (fun i => b i < k) fun i => b i < k) by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k

Depends on / 依赖: hM.toBlock_inverse_mul_toBlock_eq_one, invOf_eq_nonsing_inv, invertibleOfLeftInverse, toBlock, toBlock_inverse_mul_toBlock_eq_one
-/
def BlockTriangular.invertibleToBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) : Invertible (M.toBlock (fun i => b i < k) fun i => b i < k) :=
invertibleOfLeftInverse _ ((⅟M).toBlock (fun i => b i < k) fun i => b i < k) by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k

/--
theorem `toBlock_inverse_eq_zero` / 定理 `toBlock_inverse_eq_zero`

English:
theorem toBlock_inverse_eq_zero
  given: [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α)
  proof: by
  let p i := b i < k
  let q i := ¬b i < k
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.

中文:
定理 toBlock_inverse_eq_zero
  条件: [线性序 α] [可逆 M] (hM : BlockTriangular M b) (k : α)
  证明: by
  let p i := b i < k
  let q i := ¬b i < k
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.

Depends on / 依赖: Invertible, M.toBlock, disjoint_iff_inf_le, hM.inve, h_mul_eq_zero, h_sum, h_zero, inv_mul_of_invertible, le_of_not_gt, lt_of_lt_of_le, toBlock, toBlock_mul_eq_add, toBlock_one_disjoint
-/
theorem toBlock_inverse_eq_zero [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α) :
    (M⁻¹.toBlock (fun i => k <= b i) fun i => b i < k) = 0 := by
  let p i := b i < k
  let q i := ¬b i < k
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add]; rw [inv_mul_of_invertible M]; rw [toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.toBlock q p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 <| le_of_not_gt i.2)
  have h_mul_eq_zero : M⁻¹.toBlock q p * M.toBlock p p = 0 := by simpa [h_zero] using h_sum
  have : Invertible (M.toBlock p p) := hM.invertibleToBlock k
  have : (fun i => k <= b i) = q := by
    ext
    exact not_lt.symm
  rw [this]; rw [← Matrix.zero_mul (M.toBlock p p)⁻¹]; rw [← h_mul_eq_zero]; rw [mul_inv_cancel_right_of_invertible]

/--
theorem `blockTriangular_inv_of_blockTriangular` / 定理 `blockTriangular_inv_of_blockTriangular`

English:
theorem blockTriangular_inv_of_blockTriangular
  statement: [LinearOrder α] [Invertible M]
  proof: by
  suffices forall hs : Finset α, univ.image b = hs -> BlockTriangular M⁻¹ b by exact this _ rfl
  intro s hs
  induction s using Finset.strongInduction generalizing m with | H s ih =>
  subst hs
  intro i j hij
  have : Inhabited m := ⟨i⟩
  let k := (univ.image b).max' (univ_nonempty.image _)
  l

中文:
定理 blockTriangular_inv_of_blockTriangular
  结论: [线性序 α] [可逆 M]
  证明: by
  suffices forall hs : Finset α, univ.image b = hs -> BlockTriangular M⁻¹ b by exact this _ rfl
  intro s hs
  induction s using Finset.strongInduction generalizing m with | H s ih =>
  subst hs
  intro i j hij
  have : Inhabited m := ⟨i⟩
  let k := (univ.image b).max' (univ_nonempty.image _)
  l

Depends on / 依赖: BlockTriangular, Finset, Finset.strongInduction, Inhabited, M.toBlock, eq_or_lt, generalizing, le_max, mem_image_of_mem, mem_univ, strongInduction, toBlock, univ.image, univ_nonempty, univ_nonempty.image
-/
theorem blockTriangular_inv_of_blockTriangular [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) : BlockTriangular M⁻¹ b := by
  suffices forall hs : Finset α, univ.image b = hs -> BlockTriangular M⁻¹ b by exact this _ rfl
  intro s hs
  induction s using Finset.strongInduction generalizing m with | H s ih =>
  subst hs
  intro i j hij
  have : Inhabited m := ⟨i⟩
  let k := (univ.image b).max' (univ_nonempty.image _)
  let b' := fun i : { a // b a < k } => b ↑i
  let A := M.toBlock (fun i => b i < k) fun j => b j < k
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) <| mem_image_of_mem _ <| mem_univ _).eq_or_lt
  · have : M⁻¹.toBlock (fun i => k <= b i) (fun i => b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0 := by
      simp only [toBlock_inverse_eq_zero hM k, Matrix.zero_apply]
    simp [this.symm]
  have : Invertible A := hM.invertibleToBlock _
  have hA : A.BlockTriangular b' := hM.submatrix
  have hb' : image b' univ ⊂ image b univ := by
    convert! image_subtype_univ_ssubset_image_univ k b _ (fun a => a < k) (lt_irrefl _)
    convert! max'_mem (α := α) _ _
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩ := by simp_rw [b', hij]
  simp [A, hM.inv_toBlock k, (ih (image b' univ) hb' hA rfl hij').symm]

end Matrix
