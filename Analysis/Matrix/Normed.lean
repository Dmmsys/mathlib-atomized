/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm (with `open scoped Matrix.Norms.Elementwise`):

  * `Matrix.seminormedAddCommGroup`
  * `Matrix.normedAddCommGroup`
  * `Matrix.normedSpace`
  * `Matrix.isBoundedSMul`
  * `Matrix.normSMulClass`

* The Frobenius norm (with `open scoped Matrix.Norms.Frobenius`):

  * `Matrix.frobeniusSeminormedAddCommGroup`
  * `Matrix.frobeniusNormedAddCommGroup`
  * `Matrix.frobeniusNormedSpace`
  * `Matrix.frobeniusNormedRing`
  * `Matrix.frobeniusNormedAlgebra`
  * `Matrix.frobeniusIsBoundedSMul`
  * `Matrix.frobeniusNormSMulClass`

* The $L^\infty$ operator norm (with `open scoped Matrix.Norms.Operator`):

  * `Matrix.linftyOpSeminormedAddCommGroup`
  * `Matrix.linftyOpNormedAddCommGroup`
  * `Matrix.linftyOpNormedSpace`
  * `Matrix.linftyOpIsBoundedSMul`
  * `Matrix.linftyOpNormSMulClass`
  * `Matrix.linftyOpNonUnitalSemiNormedRing`
  * `Matrix.linftyOpSemiNormedRing`
  * `Matrix.linftyOpNonUnitalNormedRing`
  * `Matrix.linftyOpNormedRing`
  * `Matrix.linftyOpNormedAlgebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.

The norm induced by the identification of `Matrix m n 𝕜` with
`EuclideanSpace n 𝕜 →L[𝕜] EuclideanSpace m 𝕜` (i.e., the ℓ² operator norm) can be found in
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` and `open scoped Matrix.Norms.L2Operator`.
It is separated to avoid extraneous imports in this file.
-/

@[expose] public section

noncomputable section

open WithLp
open scoped NNReal Matrix

namespace Matrix

variable {R l m n α β ι : Type*} [Fintype l] [Fintype m] [Fintype n] [Unique ι]

/-! ### The elementwise supremum norm -/


section LinfLinf

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/--
Definition of `seminormedAddCommGroup` / `seminormedAddCommGroup` 的定义

English:
definition seminormedAddCommGroup
  signature: : SeminormedAddCommGroup (Matrix m n α)
  body: fast_instance% Pi.seminormedAddCommGroup

中文:
定义 seminormedAddCommGroup
  签名: : SeminormedAddComm群 (矩阵 m n α)
  定义体: fast_instance% Pi.seminormedAddCommGroup
-/
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance% Pi.seminormedAddCommGroup

attribute [local instance] Matrix.seminormedAddCommGroup

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (A : Matrix m n α)
  statement: ‖A‖ = ‖fun i j => A i j‖
  proof: rfl

中文:
定理 norm_def
  条件: (A : 矩阵 m n α)
  结论: ‖A‖ = ‖fun i j => A i j‖
  证明: rfl
-/
theorem norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖ := rfl

/--
lemma `norm_eq_sup_sup_nnnorm` / 引理 `norm_eq_sup_sup_nnnorm`

English:
lemma norm_eq_sup_sup_nnnorm
  given: (A : Matrix m n α)
  proof: by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

中文:
引理 norm_eq_sup_sup_nnnorm
  条件: (A : 矩阵 m n α)
  证明: by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

Depends on / 依赖: Matrix, Matrix.norm_def, Pi.nnnorm_def, Pi.norm_def, nnnorm_def, norm_def, simp_rw
-/
lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i => Finset.sup Finset.univ fun j => ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (A : Matrix m n α)
  statement: ‖A‖₊ = ‖fun i j => A i j‖₊
  proof: rfl

中文:
定理 nnnorm_def
  条件: (A : 矩阵 m n α)
  结论: ‖A‖₊ = ‖fun i j => A i j‖₊
  证明: rfl
-/
theorem nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊ := rfl

/--
theorem `norm_le_iff` / 定理 `norm_le_iff`

English:
theorem norm_le_iff
  given: {r : Real} (hr : 0 <= r) {A : Matrix m n α}
  statement: ‖A‖ <= r ↔ forall i j, ‖A i j‖ <= r
  proof: by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]

中文:
定理 norm_le_iff
  条件: {r : 实数} (hr : 0 <= r) {A : 矩阵 m n α}
  结论: ‖A‖ <= r ↔ 对任意 i j, ‖A i j‖ <= r
  证明: by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]

Depends on / 依赖: norm_def, pi_norm_le_iff_of_nonneg, simp_rw
-/
theorem norm_le_iff {r : Real} (hr : 0 <= r) {A : Matrix m n α} : ‖A‖ <= r ↔ forall i j, ‖A i j‖ <= r := by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]

/--
theorem `nnnorm_le_iff` / 定理 `nnnorm_le_iff`

English:
theorem nnnorm_le_iff
  given: {r : Real>=0} {A : Matrix m n α}
  statement: ‖A‖₊ <= r ↔ forall i j, ‖A i j‖₊ <= r
  proof: by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]

中文:
定理 nnnorm_le_iff
  条件: {r : 实数>=0} {A : 矩阵 m n α}
  结论: ‖A‖₊ <= r ↔ 对任意 i j, ‖A i j‖₊ <= r
  证明: by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]

Depends on / 依赖: nnnorm_def, pi_nnnorm_le_iff, simp_rw
-/
theorem nnnorm_le_iff {r : Real>=0} {A : Matrix m n α} : ‖A‖₊ <= r ↔ forall i j, ‖A i j‖₊ <= r := by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]

/--
theorem `norm_lt_iff` / 定理 `norm_lt_iff`

English:
theorem norm_lt_iff
  given: {r : Real} (hr : 0 < r) {A : Matrix m n α}
  statement: ‖A‖ < r ↔ forall i j, ‖A i j‖ < r
  proof: by
  simp_rw [norm_def, pi_norm_lt_iff hr]

中文:
定理 norm_lt_iff
  条件: {r : 实数} (hr : 0 < r) {A : 矩阵 m n α}
  结论: ‖A‖ < r ↔ 对任意 i j, ‖A i j‖ < r
  证明: by
  simp_rw [norm_def, pi_norm_lt_iff hr]

Depends on / 依赖: norm_def, pi_norm_lt_iff, simp_rw
-/
theorem norm_lt_iff {r : Real} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ forall i j, ‖A i j‖ < r := by
  simp_rw [norm_def, pi_norm_lt_iff hr]

/--
theorem `nnnorm_lt_iff` / 定理 `nnnorm_lt_iff`

English:
theorem nnnorm_lt_iff
  given: {r : Real>=0} (hr : 0 < r) {A : Matrix m n α}
  proof: by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]

中文:
定理 nnnorm_lt_iff
  条件: {r : 实数>=0} (hr : 0 < r) {A : 矩阵 m n α}
  证明: by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]

Depends on / 依赖: nnnorm_def, pi_nnnorm_lt_iff, simp_rw
-/
theorem nnnorm_lt_iff {r : Real>=0} (hr : 0 < r) {A : Matrix m n α} :
    ‖A‖₊ < r ↔ forall i j, ‖A i j‖₊ < r := by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]

/--
theorem `norm_entry_le_entrywise_sup_norm` / 定理 `norm_entry_le_entrywise_sup_norm`

English:
theorem norm_entry_le_entrywise_sup_norm
  given: (A : Matrix m n α) {i : m} {j : n}
  statement: ‖A i j‖ <= ‖A‖
  proof: (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

中文:
定理 norm_entry_le_entrywise_sup_norm
  条件: (A : 矩阵 m n α) {i : m} {j : n}
  结论: ‖A i j‖ <= ‖A‖
  证明: (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

Depends on / 依赖: norm_le_pi_norm
-/
theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ <= ‖A‖ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

/--
theorem `nnnorm_entry_le_entrywise_sup_nnnorm` / 定理 `nnnorm_entry_le_entrywise_sup_nnnorm`

English:
theorem nnnorm_entry_le_entrywise_sup_nnnorm
  given: (A : Matrix m n α) {i : m} {j : n}
  statement: ‖A i j‖₊ <= ‖A‖₊
  proof: (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]

中文:
定理 nnnorm_entry_le_entrywise_sup_nnnorm
  条件: (A : 矩阵 m n α) {i : m} {j : n}
  结论: ‖A i j‖₊ <= ‖A‖₊
  证明: (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]

Depends on / 依赖: nnnorm_le_pi_nnnorm
-/
theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ <= ‖A‖₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]
/--
theorem `nnnorm_map_eq` / 定理 `nnnorm_map_eq`

English:
theorem nnnorm_map_eq
  given: (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊)
  proof: by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]

中文:
定理 nnnorm_map_eq
  条件: (A : 矩阵 m n α) (f : α -> β) (hf : 对任意 a, ‖f a‖₊ = ‖a‖₊)
  证明: by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_apply, Pi.nnnorm_def, map_apply, nnnorm_def
-/
theorem nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]
/--
theorem `norm_map_eq` / 定理 `norm_map_eq`

English:
theorem norm_map_eq
  given: (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖ = ‖a‖)
  statement: ‖A.map f‖ = ‖A‖
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]

中文:
定理 norm_map_eq
  条件: (A : 矩阵 m n α) (f : α -> β) (hf : 对任意 a, ‖f a‖ = ‖a‖)
  结论: ‖A.map f‖ = ‖A‖
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, nnnorm_map_eq
-/
theorem norm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖ = ‖a‖) : ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : Real>=0 -> Real) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
/--
theorem `nnnorm_transpose` / 定理 `nnnorm_transpose`

English:
theorem nnnorm_transpose
  given: (A : Matrix m n α)
  statement: ‖Aᵀ‖₊ = ‖A‖₊
  proof: Finset.sup_comm _ _ _

@[simp]

中文:
定理 nnnorm_transpose
  条件: (A : 矩阵 m n α)
  结论: ‖Aᵀ‖₊ = ‖A‖₊
  证明: Finset.sup_comm _ _ _

@[simp]

Depends on / 依赖: Finset, Finset.sup_comm, sup_comm
-/
theorem nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
  Finset.sup_comm _ _ _

@[simp]
/--
theorem `norm_transpose` / 定理 `norm_transpose`

English:
theorem norm_transpose
  given: (A : Matrix m n α)
  statement: ‖Aᵀ‖ = ‖A‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_transpose A

@[simp]

中文:
定理 norm_transpose
  条件: (A : 矩阵 m n α)
  结论: ‖Aᵀ‖ = ‖A‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_transpose A

@[simp]

Depends on / 依赖: congr_arg, nnnorm_transpose
-/
theorem norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_transpose A

@[simp]
/--
theorem `nnnorm_conjTranspose` / 定理 `nnnorm_conjTranspose`

English:
theorem nnnorm_conjTranspose
  given: [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α)
  proof: (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]

中文:
定理 nnnorm_conjTranspose
  条件: [StarAdd幺半群 α] [NormedStar群 α] (A : 矩阵 m n α)
  证明: (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]

Depends on / 依赖: A.nnnorm_transpose, nnnorm_map_eq, nnnorm_star, nnnorm_transpose
-/
theorem nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]
/--
theorem `norm_conjTranspose` / 定理 `norm_conjTranspose`

English:
theorem norm_conjTranspose
  given: [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α)
  statement: ‖Aᴴ‖ = ‖A‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_conjTranspose A

中文:
定理 norm_conjTranspose
  条件: [StarAdd幺半群 α] [NormedStar群 α] (A : 矩阵 m n α)
  结论: ‖Aᴴ‖ = ‖A‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_conjTranspose A

Depends on / 依赖: congr_arg, nnnorm_conjTranspose
-/
theorem norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_conjTranspose A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StarAddMonoid
  signature: α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α)
  body: ⟨(le_of_eq <| norm_conjTranspose ·)⟩

@[simp]

中文:
实例 [StarAdd幺半群
  签名: α] [NormedStar群 α] : NormedStar群 (矩阵 m m α)
  定义体: ⟨(le_of_eq <| norm_conjTranspose ·)⟩

@[simp]

Depends on / 依赖: le_of_eq, norm_conjTranspose
-/
instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| norm_conjTranspose ·)⟩

@[simp]
/--
theorem `nnnorm_replicateCol` / 定理 `nnnorm_replicateCol`

English:
theorem nnnorm_replicateCol
  given: (v : m -> α)
  statement: ‖replicateCol ι v‖₊ = ‖v‖₊
  proof: by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]

中文:
定理 nnnorm_replicateCol
  条件: (v : m -> α)
  结论: ‖replicateCol ι v‖₊ = ‖v‖₊
  证明: by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]

Depends on / 依赖: Pi.nnnorm_def, nnnorm_def
-/
theorem nnnorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
/--
theorem `norm_replicateCol` / 定理 `norm_replicateCol`

English:
theorem norm_replicateCol
  given: (v : m -> α)
  statement: ‖replicateCol ι v‖ = ‖v‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateCol v

@[simp]

中文:
定理 norm_replicateCol
  条件: (v : m -> α)
  结论: ‖replicateCol ι v‖ = ‖v‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateCol v

@[simp]

Depends on / 依赖: congr_arg, nnnorm_replicateCol
-/
theorem norm_replicateCol (v : m -> α) : ‖replicateCol ι v‖ = ‖v‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateCol v

@[simp]
/--
theorem `nnnorm_replicateRow` / 定理 `nnnorm_replicateRow`

English:
theorem nnnorm_replicateRow
  given: (v : n -> α)
  statement: ‖replicateRow ι v‖₊ = ‖v‖₊
  proof: by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]

中文:
定理 nnnorm_replicateRow
  条件: (v : n -> α)
  结论: ‖replicateRow ι v‖₊ = ‖v‖₊
  证明: by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]

Depends on / 依赖: Pi.nnnorm_def, nnnorm_def
-/
theorem nnnorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
/--
theorem `norm_replicateRow` / 定理 `norm_replicateRow`

English:
theorem norm_replicateRow
  given: (v : n -> α)
  statement: ‖replicateRow ι v‖ = ‖v‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateRow v

@[simp]

中文:
定理 norm_replicateRow
  条件: (v : n -> α)
  结论: ‖replicateRow ι v‖ = ‖v‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateRow v

@[simp]

Depends on / 依赖: congr_arg, nnnorm_replicateRow
-/
theorem norm_replicateRow (v : n -> α) : ‖replicateRow ι v‖ = ‖v‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_replicateRow v

@[simp]
/--
theorem `nnnorm_diagonal` / 定理 `nnnorm_diagonal`

English:
theorem nnnorm_diagonal
  given: [DecidableEq n] (v : n -> α)
  statement: ‖diagonal v‖₊ = ‖v‖₊
  proof: by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · simp [hij]
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]

@[simp]

中文:
定理 nnnorm_diagonal
  条件: [DecidableEq n] (v : n -> α)
  结论: ‖diagonal v‖₊ = ‖v‖₊
  证明: by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · simp [hij]
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]

@[simp]

Depends on / 依赖: Eq.trans_le, Finset, Finset.le_sup, Finset.mem_univ, Finset.sup_le, Pi.nnnorm_def, diagonal_apply_eq, eq_or_ne, le_antisymm, le_sup, mem_univ, nnnorm_def, simp_rw, sup_le, trans_le
-/
theorem nnnorm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · simp [hij]
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]

@[simp]
/--
theorem `norm_diagonal` / 定理 `norm_diagonal`

English:
theorem norm_diagonal
  given: [DecidableEq n] (v : n -> α)
  statement: ‖diagonal v‖ = ‖v‖
  proof: congr_arg ((↑) : Real>=0 -> Real) nnnorm_diagonal v

中文:
定理 norm_diagonal
  条件: [DecidableEq n] (v : n -> α)
  结论: ‖diagonal v‖ = ‖v‖
  证明: congr_arg ((↑) : Real>=0 -> Real) nnnorm_diagonal v

Depends on / 依赖: congr_arg, nnnorm_diagonal
-/
theorem norm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖ = ‖v‖ :=
congr_arg ((↑) : Real>=0 -> Real) nnnorm_diagonal v

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α)
  body: ⟨(norm_diagonal _).trans norm_one⟩

中文:
实例 [非空
  签名: n] [DecidableEq n] [幺 α] [NormOne类 α] : NormOne类 (矩阵 n n α)
  定义体: ⟨(norm_diagonal _).trans norm_one⟩

Depends on / 依赖: norm_diagonal, norm_one
-/
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
⟨(norm_diagonal _).trans norm_one⟩

end SeminormedAddCommGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/--
Definition of `normedAddCommGroup` / `normedAddCommGroup` 的定义

English:
definition normedAddCommGroup
  signature: [NormedAddCommGroup α]
  body: fast_instance% Pi.normedAddCommGroup

中文:
定义 normedAddCommGroup
  签名: [赋范交换加群 α]
  定义体: fast_instance% Pi.normedAddCommGroup
-/
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  fast_instance% Pi.normedAddCommGroup

section NormedSpace

attribute [local instance] Matrix.seminormedAddCommGroup

/--
theorem `isBoundedSMul` / 定理 `isBoundedSMul`

English:
theorem isBoundedSMul
  statement: [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
  proof: Pi.instIsBoundedSMul

中文:
定理 isBoundedSMul
  结论: [Seminormed环 R] [SeminormedAddComm群 α] [模 R α]
  证明: Pi.instIsBoundedSMul
-/
protected theorem isBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] : IsBoundedSMul R (Matrix m n α) :=
  Pi.instIsBoundedSMul

/--
theorem `normSMulClass` / 定理 `normSMulClass`

English:
theorem normSMulClass
  statement: [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
  proof: Pi.instNormSMulClass

中文:
定理 normSMulClass
  结论: [Seminormed环 R] [SeminormedAddComm群 α] [模 R α]
  证明: Pi.instNormSMulClass
-/
protected theorem normSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] : NormSMulClass R (Matrix m n α) :=
  Pi.instNormSMulClass

variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/--
Definition of `normedSpace` / `normedSpace` 的定义

English:
definition normedSpace
  signature: : NormedSpace R (Matrix m n α)
  body: fast_instance% Pi.normedSpace

中文:
定义 normedSpace
  签名: : 赋范空间 R (矩阵 m n α)
  定义体: fast_instance% Pi.normedSpace
-/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  fast_instance% Pi.normedSpace

namespace Norms.Elementwise

attribute [scoped instance]
  Matrix.seminormedAddCommGroup
  Matrix.normedAddCommGroup
  Matrix.normedSpace
  Matrix.isBoundedSMul
  Matrix.normSMulClass

end Norms.Elementwise

end NormedSpace

end LinfLinf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering $A$ as a linear map between two
$L^\infty$ spaces.
-/


section LinftyOp

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpSeminormedAddCommGroup` / `linftyOpSeminormedAddCommGroup` 的定义

English:
definition linftyOpSeminormedAddCommGroup
  signature: [SeminormedAddCommGroup α]
  body: fast_instance%
  @Pi.seminormedAddCommGroup m _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α))

中文:
定义 linftyOpSeminormedAddCommGroup
  签名: [SeminormedAddComm群 α]
  定义体: fast_instance%
  @Pi.seminormedAddCommGroup m _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α))
-/
protected def linftyOpSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @Pi.seminormedAddCommGroup m _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNormedAddCommGroup` / `linftyOpNormedAddCommGroup` 的定义

English:
definition linftyOpNormedAddCommGroup
  signature: [NormedAddCommGroup α]
  body: fast_instance%
  @Pi.normedAddCommGroup m _ _ (fun _ => PiLp.normedAddCommGroupToPi 1 (fun _ : n => α))

中文:
定义 linftyOpNormedAddCommGroup
  签名: [赋范交换加群 α]
  定义体: fast_instance%
  @Pi.normedAddCommGroup m _ _ (fun _ => PiLp.normedAddCommGroupToPi 1 (fun _ : n => α))
-/
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] :
    NormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @Pi.normedAddCommGroup m _ _ (fun _ => PiLp.normedAddCommGroupToPi 1 (fun _ : n => α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
/--
theorem `linftyOpIsBoundedSMul` / 定理 `linftyOpIsBoundedSMul`

English:
theorem linftyOpIsBoundedSMul
  proof: letI := PiLp.pseudoMetricSpaceToPi 1 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (IsBoundedSMul R (m -> n -> α))

中文:
定理 linftyOpIsBoundedSMul
  证明: letI := PiLp.pseudoMetricSpaceToPi 1 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (IsBoundedSMul R (m -> n -> α))
-/
protected theorem linftyOpIsBoundedSMul
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  letI := PiLp.pseudoMetricSpaceToPi 1 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (IsBoundedSMul R (m -> n -> α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
/--
theorem `linftyOpNormSMulClass` / 定理 `linftyOpNormSMulClass`

English:
theorem linftyOpNormSMulClass
  proof: letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormSMulClass R (m -> n -> α))

中文:
定理 linftyOpNormSMulClass
  证明: letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormSMulClass R (m -> n -> α))
-/
protected theorem linftyOpNormSMulClass
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormSMulClass R (m -> n -> α))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNormedSpace` / `linftyOpNormedSpace` 的定义

English:
definition linftyOpNormedSpace
  signature: [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]
  body: letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormedSpace R (m -> n -> α))

中文:
定义 linftyOpNormedSpace
  签名: [赋范域 R] [SeminormedAddComm群 α] [赋范空间 R α]
  定义体: letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormedSpace R (m -> n -> α))
-/
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n => α)
  inferInstanceAs (NormedSpace R (m -> n -> α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α]

/--
theorem `linfty_opNorm_def` / 定理 `linfty_opNorm_def`

English:
theorem linfty_opNorm_def
  given: (A : Matrix m n α)
  proof: by
  change ‖fun i => toLp 1 (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_of_L1]

中文:
定理 linfty_opNorm_def
  条件: (A : 矩阵 m n α)
  证明: by
  change ‖fun i => toLp 1 (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_of_L1]

Depends on / 依赖: Pi.norm_def, PiLp.nnnorm_eq_of_L1, nnnorm_eq_of_L1, norm_def
-/
theorem linfty_opNorm_def (A : Matrix m n α) :
    ‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : Real>=0) := by
  change ‖fun i => toLp 1 (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_of_L1]

/--
theorem `linfty_opNNNorm_def` / 定理 `linfty_opNNNorm_def`

English:
theorem linfty_opNNNorm_def
  given: (A : Matrix m n α)
  proof: Subtype.ext linfty_opNorm_def A

@[simp]

中文:
定理 linfty_opNNNorm_def
  条件: (A : 矩阵 m n α)
  证明: Subtype.ext linfty_opNorm_def A

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, linfty_opNorm_def
-/
theorem linfty_opNNNorm_def (A : Matrix m n α) :
    ‖A‖₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ :=
Subtype.ext linfty_opNorm_def A

@[simp]
/--
theorem `linfty_opNNNorm_replicateCol` / 定理 `linfty_opNNNorm_replicateCol`

English:
theorem linfty_opNNNorm_replicateCol
  given: (v : m -> α)
  statement: ‖replicateCol ι v‖₊ = ‖v‖₊
  proof: by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  simp

@[simp]

中文:
定理 linfty_opNNNorm_replicateCol
  条件: (v : m -> α)
  结论: ‖replicateCol ι v‖₊ = ‖v‖₊
  证明: by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  simp

@[simp]

Depends on / 依赖: Pi.nnnorm_def, linfty_opNNNorm_def, nnnorm_def
-/
theorem linfty_opNNNorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  simp

@[simp]
/--
theorem `linfty_opNorm_replicateCol` / 定理 `linfty_opNorm_replicateCol`

English:
theorem linfty_opNorm_replicateCol
  given: (v : m -> α)
  statement: ‖replicateCol ι v‖ = ‖v‖
  proof: congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_replicateCol v

@[simp]

中文:
定理 linfty_opNorm_replicateCol
  条件: (v : m -> α)
  结论: ‖replicateCol ι v‖ = ‖v‖
  证明: congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_replicateCol v

@[simp]

Depends on / 依赖: congr_arg, linfty_opNNNorm_replicateCol
-/
theorem linfty_opNorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖ = ‖v‖ :=
congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_replicateCol v

@[simp]
/--
theorem `linfty_opNNNorm_replicateRow` / 定理 `linfty_opNNNorm_replicateRow`

English:
theorem linfty_opNNNorm_replicateRow
  given: (v : n -> α)
  statement: ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊
  proof: by
  simp [linfty_opNNNorm_def]

@[simp]

中文:
定理 linfty_opNNNorm_replicateRow
  条件: (v : n -> α)
  结论: ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊
  证明: by
  simp [linfty_opNNNorm_def]

@[simp]

Depends on / 依赖: linfty_opNNNorm_def
-/
theorem linfty_opNNNorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊ := by
  simp [linfty_opNNNorm_def]

@[simp]
/--
theorem `linfty_opNorm_replicateRow` / 定理 `linfty_opNorm_replicateRow`

English:
theorem linfty_opNorm_replicateRow
  given: (v : n -> α)
  statement: ‖replicateRow ι v‖ = ∑ i, ‖v i‖
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| linfty_opNNNorm_replicateRow v).trans by simp [NNReal.coe_sum]

@[simp]

中文:
定理 linfty_opNorm_replicateRow
  条件: (v : n -> α)
  结论: ‖replicateRow ι v‖ = ∑ i, ‖v i‖
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| linfty_opNNNorm_replicateRow v).trans by simp [NNReal.coe_sum]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_sum, coe_sum, congr_arg, linfty_opNNNorm_replicateRow
-/
theorem linfty_opNorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖ = ∑ i, ‖v i‖ :=
(congr_arg ((↑) : Real>=0 -> Real) <| linfty_opNNNorm_replicateRow v).trans by simp [NNReal.coe_sum]

@[simp]
/--
theorem `linfty_opNNNorm_diagonal` / 定理 `linfty_opNNNorm_diagonal`

English:
theorem linfty_opNNNorm_diagonal
  given: [DecidableEq m] (v : m -> α)
  statement: ‖diagonal v‖₊ = ‖v‖₊
  proof: by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]

@[simp]

中文:
定理 linfty_opNNNorm_diagonal
  条件: [DecidableEq m] (v : m -> α)
  结论: ‖diagonal v‖₊ = ‖v‖₊
  证明: by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]

@[simp]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_eq_single_of_mem, Pi.nnnorm_def, diagonal_apply_eq, diagonal_apply_ne, linfty_opNNNorm_def, mem_univ, nnnorm_def, nnnorm_zero, sum_eq_single_of_mem
-/
theorem linfty_opNNNorm_diagonal [DecidableEq m] (v : m -> α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def]; rw [Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]

@[simp]
/--
theorem `linfty_opNorm_diagonal` / 定理 `linfty_opNorm_diagonal`

English:
theorem linfty_opNorm_diagonal
  given: [DecidableEq m] (v : m -> α)
  statement: ‖diagonal v‖ = ‖v‖
  proof: congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_diagonal v

中文:
定理 linfty_opNorm_diagonal
  条件: [DecidableEq m] (v : m -> α)
  结论: ‖diagonal v‖ = ‖v‖
  证明: congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_diagonal v

Depends on / 依赖: congr_arg, linfty_opNNNorm_diagonal
-/
theorem linfty_opNorm_diagonal [DecidableEq m] (v : m -> α) : ‖diagonal v‖ = ‖v‖ :=
congr_arg ((↑) : Real>=0 -> Real) linfty_opNNNorm_diagonal v

end SeminormedAddCommGroup

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

/--
theorem `linfty_opNNNorm_mul` / 定理 `linfty_opNNNorm_mul`

English:
theorem linfty_opNNNorm_mul
  given: (A : Matrix l m α) (B : Matrix m n α)
  statement: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  proof: by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) <=
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => 

中文:
定理 linfty_opNNNorm_mul
  条件: (A : 矩阵 l m α) (B : 矩阵 m n α)
  结论: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  证明: by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) <=
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => 

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Finset.sum_le_sum, Finset.sup_mono_fun, Finset.univ.sup, Matrix, Matrix.mul_apply, linfty_opNNNorm_def, mul_apply, mul_sum, nnnorm_mul_le, nnnorm_sum_le_of_le, simp_rw, sum_comm, sum_le_sum, sup_mono_fun
-/
theorem linfty_opNNNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊ := by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) <=
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
    _ = Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * ∑ k, ‖B j k‖₊ := by
      simp_rw [@Finset.sum_comm m, Finset.mul_sum]
    _ <= Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      refine Finset.sup_mono_fun fun i _hi => ?_
      gcongr with j hj
      exact Finset.le_sup (f := fun i => ∑ k : n, ‖B i k‖₊) hj
    _ <= (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      simp_rw [← Finset.sum_mul, ← NNReal.finset_sup_mul]
      rfl

/--
theorem `linfty_opNorm_mul` / 定理 `linfty_opNorm_mul`

English:
theorem linfty_opNorm_mul
  given: (A : Matrix l m α) (B : Matrix m n α)
  statement: ‖A * B‖ <= ‖A‖ * ‖B‖
  proof: linfty_opNNNorm_mul _ _

中文:
定理 linfty_opNorm_mul
  条件: (A : 矩阵 l m α) (B : 矩阵 m n α)
  结论: ‖A * B‖ <= ‖A‖ * ‖B‖
  证明: linfty_opNNNorm_mul _ _

Depends on / 依赖: linfty_opNNNorm_mul
-/
theorem linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ <= ‖A‖ * ‖B‖ :=
  linfty_opNNNorm_mul _ _

/--
theorem `linfty_opNNNorm_mulVec` / 定理 `linfty_opNNNorm_mulVec`

English:
theorem linfty_opNNNorm_mulVec
  given: (A : Matrix l m α) (v : m -> α)
  statement: ‖A *ᵥ v‖₊ <= ‖A‖₊ * ‖v‖₊
  proof: by
  rw [← linfty_opNNNorm_replicateCol (ι := Fin 1) (A *ᵥ v)]; rw [← linfty_opNNNorm_replicateCol v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (replicateCol (Fin 1) v)

中文:
定理 linfty_opNNNorm_mulVec
  条件: (A : 矩阵 l m α) (v : m -> α)
  结论: ‖A *ᵥ v‖₊ <= ‖A‖₊ * ‖v‖₊
  证明: by
  rw [← linfty_opNNNorm_replicateCol (ι := Fin 1) (A *ᵥ v)]; rw [← linfty_opNNNorm_replicateCol v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (replicateCol (Fin 1) v)

Depends on / 依赖: linfty_opNNNorm_mul, linfty_opNNNorm_replicateCol, replicateCol
-/
theorem linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m -> α) : ‖A *ᵥ v‖₊ <= ‖A‖₊ * ‖v‖₊ := by
  rw [← linfty_opNNNorm_replicateCol (ι := Fin 1) (A *ᵥ v)]; rw [← linfty_opNNNorm_replicateCol v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (replicateCol (Fin 1) v)

/--
theorem `linfty_opNorm_mulVec` / 定理 `linfty_opNorm_mulVec`

English:
theorem linfty_opNorm_mulVec
  given: (A : Matrix l m α) (v : m -> α)
  statement: ‖A *ᵥ v‖ <= ‖A‖ * ‖v‖
  proof: linfty_opNNNorm_mulVec _ _

中文:
定理 linfty_opNorm_mulVec
  条件: (A : 矩阵 l m α) (v : m -> α)
  结论: ‖A *ᵥ v‖ <= ‖A‖ * ‖v‖
  证明: linfty_opNNNorm_mulVec _ _

Depends on / 依赖: linfty_opNNNorm_mulVec
-/
theorem linfty_opNorm_mulVec (A : Matrix l m α) (v : m -> α) : ‖A *ᵥ v‖ <= ‖A‖ * ‖v‖ :=
  linfty_opNNNorm_mulVec _ _

end NonUnitalSeminormedRing

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a seminormed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNonUnitalSemiNormedRing` / `linftyOpNonUnitalSemiNormedRing` 的定义

English:
definition linftyOpNonUnitalSemiNormedRing
  signature: [NonUnitalSeminormedRing α]
  body: { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul_le := linfty_opNorm_mul }

中文:
定义 linftyOpNonUnitalSemiNormedRing
  签名: [非幺Seminormed环 α]
  定义体: { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul_le := linfty_opNorm_mul }
-/
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
    NonUnitalSeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul_le := linfty_opNorm_mul }

/--
Instance `linfty_opNormOneClass` / 实例 `linfty_opNormOneClass`

English:
instance linfty_opNormOneClass
  signature: [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n]
  body: (linfty_opNorm_diagonal _).trans norm_one

中文:
实例 linfty_opNormOneClass
  签名: [Seminormed环 α] [NormOne类 α] [DecidableEq n] [非空 n]
  定义体: (linfty_opNorm_diagonal _).trans norm_one

Depends on / 依赖: linfty_opNorm_diagonal, norm_one
-/
instance linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_opNorm_diagonal _).trans norm_one

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpSemiNormedRing` / `linftyOpSemiNormedRing` 的定义

English:
definition linftyOpSemiNormedRing
  signature: [SeminormedRing α] [DecidableEq n]
  body: { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }

中文:
定义 linftyOpSemiNormedRing
  签名: [Seminormed环 α] [DecidableEq n]
  定义体: { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }
-/
protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
    SeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNonUnitalNormedRing` / `linftyOpNonUnitalNormedRing` 的定义

English:
definition linftyOpNonUnitalNormedRing
  signature: [NonUnitalNormedRing α]
  body: { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
定义 linftyOpNonUnitalNormedRing
  签名: [非幺赋范环 α]
  定义体: { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
-/
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
    NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNormedRing` / `linftyOpNormedRing` 的定义

English:
definition linftyOpNormedRing
  signature: [NormedRing α] [DecidableEq n]
  body: { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
定义 linftyOpNormedRing
  签名: [赋范环 α] [DecidableEq n]
  定义体: { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
-/
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `linftyOpNormedAlgebra` / `linftyOpNormedAlgebra` 的定义

English:
definition linftyOpNormedAlgebra
  signature: [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
  body: { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }

中文:
定义 linftyOpNormedAlgebra
  签名: [赋范域 R] [Seminormed环 α] [赋范代数 R α]
  定义体: { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }
-/
protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }


section
variable [NormedDivisionRing α] [NormedAlgebra Real α]

/--
Definition of `unitOf` / `unitOf` 的定义

English:
definition unitOf
  signature: (a : α)
  body: by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹

中文:
定义 unitOf
  签名: (a : α)
  定义体: by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹
-/
private def unitOf (a : α) : α := by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹

/--
theorem `norm_unitOf` / 定理 `norm_unitOf`

English:
theorem norm_unitOf
  given: (a : α)
  statement: ‖unitOf a‖₊ = 1
  proof: by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul]; rw [nnnorm_inv]; rw [nnnorm_norm]; rw [mul_inv_cancel₀ h]

中文:
定理 norm_unitOf
  条件: (a : α)
  结论: ‖unitOf a‖₊ = 1
  证明: by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul]; rw [nnnorm_inv]; rw [nnnorm_norm]; rw [mul_inv_cancel₀ h]
-/
private theorem norm_unitOf (a : α) : ‖unitOf a‖₊ = 1 := by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul]; rw [nnnorm_inv]; rw [nnnorm_norm]; rw [mul_inv_cancel₀ h]

/--
theorem `mul_unitOf` / 定理 `mul_unitOf`

English:
theorem mul_unitOf
  given: (a : α)
  statement: a * unitOf a = algebraMap _ _ (‖a‖₊ : Real)
  proof: by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]

中文:
定理 mul_unitOf
  条件: (a : α)
  结论: a * unitOf a = algebraMap _ _ (‖a‖₊ : 实数)
  证明: by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]
-/
private theorem mul_unitOf (a : α) : a * unitOf a = algebraMap _ _ (‖a‖₊ : Real) := by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]

end

/-!
For a matrix over a field, the norm defined in this section agrees with the operator norm on
`ContinuousLinearMap`s between function types (which have the infinity norm).
-/
section
variable [NontriviallyNormedField α] [NormedAlgebra Real α]

/--
lemma `linfty_opNNNorm_eq_opNNNorm` / 引理 `linfty_opNNNorm_eq_opNNNorm`

English:
lemma linfty_opNNNorm_eq_opNNNorm
  given: (A : Matrix m n α)
  proof: by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  let x : n -> α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def

中文:
引理 linfty_opNNNorm_eq_opNNNorm
  条件: (A : 矩阵 m n α)
  证明: by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  let x : n -> α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNNNorm_eq_of_bounds, Finset, Finset.mem_univ, Finset.sup_const, Finset.sup_le, Finset.sup_le_iff, Finset.univ_nonempty, Pi.nnnorm_def, dotProduct, isEmpty_or_nonempty, linfty_opNNNorm_def, linfty_opNNNorm_mulVec, mem_univ, mulVec, mul_one, nnnorm_def, norm_unitOf, opNNNorm_eq_of_bounds, replace
-/
lemma linfty_opNNNorm_eq_opNNNorm (A : Matrix m n α) :
    ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊ := by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  let x : n -> α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def, norm_unitOf, Finset.sup_const Finset.univ_nonempty]
  specialize hN x
  rw [hxn]; rw [mul_one]; rw [Pi.nnnorm_def]; rw [Finset.sup_le_iff] at hN
  replace hN := hN i (Finset.mem_univ _)
  dsimp [mulVec, dotProduct] at hN
  simp_rw [x, mul_unitOf, ← map_sum, nnnorm_algebraMap, ← NNReal.coe_sum, NNReal.nnnorm_eq,
    nnnorm_one, mul_one] at hN
  exact hN

/--
lemma `linfty_opNorm_eq_opNorm` / 引理 `linfty_opNorm_eq_opNorm`

English:
lemma linfty_opNorm_eq_opNorm
  given: (A : Matrix m n α)
  proof: congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

中文:
引理 linfty_opNorm_eq_opNorm
  条件: (A : 矩阵 m n α)
  证明: congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, linfty_opNNNorm_eq_opNNNorm, toReal
-/
lemma linfty_opNorm_eq_opNorm (A : Matrix m n α) :
    ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

variable [DecidableEq n]

/--
lemma `linfty_opNNNorm_toMatrix` / 引理 `linfty_opNNNorm_toMatrix`

English:
lemma linfty_opNNNorm_toMatrix
  given: (f : (n -> α) ->L[α] (m -> α))
  proof: by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']

中文:
引理 linfty_opNNNorm_toMatrix
  条件: (f : (n -> α) ->L[α] (m -> α))
  证明: by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']
-/
@[simp] lemma linfty_opNNNorm_toMatrix (f : (n -> α) ->L[α] (m -> α)) :
    ‖LinearMap.toMatrix' (↑f : (n -> α) ->ₗ[α] (m -> α))‖₊ = ‖f‖₊ := by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']

/--
lemma `linfty_opNorm_toMatrix` / 引理 `linfty_opNorm_toMatrix`

English:
lemma linfty_opNorm_toMatrix
  given: (f : (n -> α) ->L[α] (m -> α))
  proof: congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)

中文:
引理 linfty_opNorm_toMatrix
  条件: (f : (n -> α) ->L[α] (m -> α))
  证明: congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)
-/
@[simp] lemma linfty_opNorm_toMatrix (f : (n -> α) ->L[α] (m -> α)) :
    ‖LinearMap.toMatrix' (↑f : (n -> α) ->ₗ[α] (m -> α))‖ = ‖f‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)

end

namespace Norms.Operator
attribute [scoped instance]
  Matrix.linftyOpSeminormedAddCommGroup
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpIsBoundedSMul
  Matrix.linftyOpNormSMulClass
  Matrix.linftyOpNonUnitalSemiNormedRing
  Matrix.linftyOpSemiNormedRing
  Matrix.linftyOpNonUnitalNormedRing
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
end Norms.Operator

end LinftyOp

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/


section frobenius

open scoped Matrix

/-- Seminormed group instance (using the Frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `frobeniusSeminormedAddCommGroup` / `frobeniusSeminormedAddCommGroup` 的定义

English:
definition frobeniusSeminormedAddCommGroup
  signature: [SeminormedAddCommGroup α]
  body: fast_instance%
  @PiLp.seminormedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 2 _)

中文:
定义 frobeniusSeminormedAddCommGroup
  签名: [SeminormedAddComm群 α]
  定义体: fast_instance%
  @PiLp.seminormedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 2 _)

Depends on / 依赖: PiLp.seminormedAddCommGroupToPi, fast_instance, seminormedAddCommGroupToPi
-/
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @PiLp.seminormedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.seminormedAddCommGroupToPi 2 _)

/-- Normed group instance (using the Frobenius norm) for matrices over a normed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `frobeniusNormedAddCommGroup` / `frobeniusNormedAddCommGroup` 的定义

English:
definition frobeniusNormedAddCommGroup
  signature: [NormedAddCommGroup α]
  body: fast_instance% @PiLp.normedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.normedAddCommGroupToPi 2 _)

中文:
定义 frobeniusNormedAddCommGroup
  签名: [赋范交换加群 α]
  定义体: fast_instance% @PiLp.normedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.normedAddCommGroupToPi 2 _)

Depends on / 依赖: PiLp.normedAddCommGroupToPi, fast_instance, normedAddCommGroupToPi
-/
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  fast_instance% @PiLp.normedAddCommGroupToPi 2 _ _ _ _ (fun _ => PiLp.normedAddCommGroupToPi 2 _)

/-- This applies to the Frobenius norm. -/
@[local instance]
/--
theorem `frobeniusIsBoundedSMul` / 定理 `frobeniusIsBoundedSMul`

English:
theorem frobeniusIsBoundedSMul
  statement: [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
  proof: letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.isBoundedSMulSeminormedAddCommGroupToPi 2 _

中文:
定理 frobeniusIsBoundedSMul
  结论: [Seminormed环 R] [SeminormedAddComm群 α] [模 R α]
  证明: letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.isBoundedSMulSeminormedAddCommGroupToPi 2 _

Depends on / 依赖: PiLp.isBoundedSMulSeminormedAddCommGroupToPi, PiLp.seminormedAddCommGroupToPi, isBoundedSMulSeminormedAddCommGroupToPi, seminormedAddCommGroupToPi
-/
theorem frobeniusIsBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.isBoundedSMulSeminormedAddCommGroupToPi 2 _

/-- This applies to the Frobenius norm. -/
@[local instance]
/--
theorem `frobeniusNormSMulClass` / 定理 `frobeniusNormSMulClass`

English:
theorem frobeniusNormSMulClass
  statement: [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
  proof: letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normSMulClassSeminormedAddCommGroupToPi 2 _

中文:
定理 frobeniusNormSMulClass
  结论: [Seminormed环 R] [SeminormedAddComm群 α] [模 R α]
  证明: letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normSMulClassSeminormedAddCommGroupToPi 2 _

Depends on / 依赖: PiLp.normSMulClassSeminormedAddCommGroupToPi, PiLp.seminormedAddCommGroupToPi, normSMulClassSeminormedAddCommGroupToPi, seminormedAddCommGroupToPi
-/
theorem frobeniusNormSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normSMulClassSeminormedAddCommGroupToPi 2 _

/-- Normed space instance (using the Frobenius norm) for matrices over a normed space. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `frobeniusNormedSpace` / `frobeniusNormedSpace` 的定义

English:
definition frobeniusNormedSpace
  signature: [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]
  body: fast_instance%
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normedSpaceSeminormedAddCommGroupToPi 2 _

中文:
定义 frobeniusNormedSpace
  签名: [赋范域 R] [SeminormedAddComm群 α] [赋范空间 R α]
  定义体: fast_instance%
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normedSpaceSeminormedAddCommGroupToPi 2 _

Depends on / 依赖: PiLp.normedSpaceSeminormedAddCommGroupToPi, PiLp.seminormedAddCommGroupToPi, fast_instance, normedSpaceSeminormedAddCommGroupToPi, seminormedAddCommGroupToPi
-/
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  fast_instance%
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n => α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n => α)
  PiLp.normedSpaceSeminormedAddCommGroupToPi 2 _

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/--
theorem `frobenius_nnnorm_def` / 定理 `frobenius_nnnorm_def`

English:
theorem frobenius_nnnorm_def
  given: (A : Matrix m n α)
  proof: by
  change ‖toLp 2 fun i => toLp 2 fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]

中文:
定理 frobenius_nnnorm_def
  条件: (A : 矩阵 m n α)
  证明: by
  change ‖toLp 2 fun i => toLp 2 fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]

Depends on / 依赖: NNReal, NNReal.rpow_two, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, PiLp.nnnorm_eq_of_L2, nnnorm_eq_of_L2, rpow_two, simp_rw, sq_sqrt, sqrt_eq_rpow
-/
theorem frobenius_nnnorm_def (A : Matrix m n α) :
    ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real) := by
  change ‖toLp 2 fun i => toLp 2 fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]

/--
theorem `frobenius_norm_def` / 定理 `frobenius_norm_def`

English:
theorem frobenius_norm_def
  given: (A : Matrix m n α)
  proof: (congr_arg ((↑) : Real>=0 -> Real) (frobenius_nnnorm_def A)).trans by simp [NNReal.coe_sum]

@[simp]

中文:
定理 frobenius_norm_def
  条件: (A : 矩阵 m n α)
  证明: (congr_arg ((↑) : Real>=0 -> Real) (frobenius_nnnorm_def A)).trans by simp [NNReal.coe_sum]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_sum, coe_sum, congr_arg, frobenius_nnnorm_def
-/
theorem frobenius_norm_def (A : Matrix m n α) :
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : Real)) ^ (1 / 2 : Real) :=
(congr_arg ((↑) : Real>=0 -> Real) (frobenius_nnnorm_def A)).trans by simp [NNReal.coe_sum]

@[simp]
/--
theorem `frobenius_nnnorm_map_eq` / 定理 `frobenius_nnnorm_map_eq`

English:
theorem frobenius_nnnorm_map_eq
  given: (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊)
  proof: by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]

中文:
定理 frobenius_nnnorm_map_eq
  条件: (A : 矩阵 m n α) (f : α -> β) (hf : 对任意 a, ‖f a‖₊ = ‖a‖₊)
  证明: by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_apply, frobenius_nnnorm_def, map_apply, simp_rw
-/
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]
/--
theorem `frobenius_norm_map_eq` / 定理 `frobenius_norm_map_eq`

English:
theorem frobenius_norm_map_eq
  given: (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖ = ‖a‖)
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]

中文:
定理 frobenius_norm_map_eq
  条件: (A : 矩阵 m n α) (f : α -> β) (hf : 对任意 a, ‖f a‖ = ‖a‖)
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, frobenius_nnnorm_map_eq
-/
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖ = ‖a‖) :
    ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
/--
theorem `frobenius_nnnorm_transpose` / 定理 `frobenius_nnnorm_transpose`

English:
theorem frobenius_nnnorm_transpose
  given: (A : Matrix m n α)
  statement: ‖Aᵀ‖₊ = ‖A‖₊
  proof: by
  rw [frobenius_nnnorm_def]; rw [frobenius_nnnorm_def]; rw [Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]

@[simp]

中文:
定理 frobenius_nnnorm_transpose
  条件: (A : 矩阵 m n α)
  结论: ‖Aᵀ‖₊ = ‖A‖₊
  证明: by
  rw [frobenius_nnnorm_def]; rw [frobenius_nnnorm_def]; rw [Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]

@[simp]

Depends on / 依赖: Finset, Finset.sum_comm, Matrix, Matrix.transpose_apply, frobenius_nnnorm_def, simp_rw, sum_comm, transpose_apply
-/
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ := by
  rw [frobenius_nnnorm_def]; rw [frobenius_nnnorm_def]; rw [Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]

@[simp]
/--
theorem `frobenius_norm_transpose` / 定理 `frobenius_norm_transpose`

English:
theorem frobenius_norm_transpose
  given: (A : Matrix m n α)
  statement: ‖Aᵀ‖ = ‖A‖
  proof: congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_transpose A

@[simp]

中文:
定理 frobenius_norm_transpose
  条件: (A : 矩阵 m n α)
  结论: ‖Aᵀ‖ = ‖A‖
  证明: congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_transpose A

@[simp]

Depends on / 依赖: FiniteDimensional, completeSpace, congr_arg, frobenius_nnnorm_transpose, h_fin
-/
theorem frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_transpose A

@[simp]
/--
theorem `frobenius_nnnorm_conjTranspose` / 定理 `frobenius_nnnorm_conjTranspose`

English:
theorem frobenius_nnnorm_conjTranspose
  given: [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α)
  proof: (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]

中文:
定理 frobenius_nnnorm_conjTranspose
  条件: [StarAdd幺半群 α] [NormedStar群 α] (A : 矩阵 m n α)
  证明: (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]

Depends on / 依赖: A.frobenius_nnnorm_transpose, frobenius_nnnorm_map_eq, frobenius_nnnorm_transpose, nnnorm_star
-/
theorem frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]
/--
theorem `frobenius_norm_conjTranspose` / 定理 `frobenius_norm_conjTranspose`

English:
theorem frobenius_norm_conjTranspose
  given: [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α)
  proof: congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_conjTranspose A

中文:
定理 frobenius_norm_conjTranspose
  条件: [StarAdd幺半群 α] [NormedStar群 α] (A : 矩阵 m n α)
  证明: congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_conjTranspose A

Depends on / 依赖: congr_arg, frobenius_nnnorm_conjTranspose
-/
theorem frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖ = ‖A‖ :=
congr_arg ((↑) : Real>=0 -> Real) frobenius_nnnorm_conjTranspose A

/--
Instance `frobenius_normedStarGroup` / 实例 `frobenius_normedStarGroup`

English:
instance frobenius_normedStarGroup
  signature: [StarAddMonoid α] [NormedStarGroup α]
  body: ⟨(le_of_eq <| frobenius_norm_conjTranspose ·)⟩

@[simp]

中文:
实例 frobenius_normedStarGroup
  签名: [StarAdd幺半群 α] [NormedStar群 α]
  定义体: ⟨(le_of_eq <| frobenius_norm_conjTranspose ·)⟩

@[simp]

Depends on / 依赖: frobenius_norm_conjTranspose, le_of_eq
-/
instance frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] :
    NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| frobenius_norm_conjTranspose ·)⟩

@[simp]
/--
lemma `frobenius_norm_replicateRow` / 引理 `frobenius_norm_replicateRow`

English:
lemma frobenius_norm_replicateRow
  given: (v : m -> α)
  statement: ‖replicateRow ι v‖ = ‖toLp 2 v‖
  proof: by
  rw [frobenius_norm_def]; rw [Fintype.sum_unique]; rw [PiLp.norm_eq_of_L2]; rw [Real.sqrt_eq_rpow]
  simp only [replicateRow_apply, Real.rpow_two]

@[simp]

中文:
引理 frobenius_norm_replicateRow
  条件: (v : m -> α)
  结论: ‖replicateRow ι v‖ = ‖toLp 2 v‖
  证明: by
  rw [frobenius_norm_def]; rw [Fintype.sum_unique]; rw [PiLp.norm_eq_of_L2]; rw [Real.sqrt_eq_rpow]
  simp only [replicateRow_apply, Real.rpow_two]

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.rpow_two, Real.sqrt_eq_rpow, frobenius_norm_def, norm_eq_of_L2, replicateRow_apply, rpow_two, sqrt_eq_rpow, sum_unique
-/
lemma frobenius_norm_replicateRow (v : m -> α) : ‖replicateRow ι v‖ = ‖toLp 2 v‖ := by
  rw [frobenius_norm_def]; rw [Fintype.sum_unique]; rw [PiLp.norm_eq_of_L2]; rw [Real.sqrt_eq_rpow]
  simp only [replicateRow_apply, Real.rpow_two]

@[simp]
/--
lemma `frobenius_nnnorm_replicateRow` / 引理 `frobenius_nnnorm_replicateRow`

English:
lemma frobenius_nnnorm_replicateRow
  given: (v : m -> α)
  statement: ‖replicateRow ι v‖₊ = ‖toLp 2 v‖₊
  proof: Subtype.ext frobenius_norm_replicateRow v

@[simp]

中文:
引理 frobenius_nnnorm_replicateRow
  条件: (v : m -> α)
  结论: ‖replicateRow ι v‖₊ = ‖toLp 2 v‖₊
  证明: Subtype.ext frobenius_norm_replicateRow v

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, frobenius_norm_replicateRow
-/
lemma frobenius_nnnorm_replicateRow (v : m -> α) : ‖replicateRow ι v‖₊ = ‖toLp 2 v‖₊ :=
Subtype.ext frobenius_norm_replicateRow v

@[simp]
/--
lemma `frobenius_norm_replicateCol` / 引理 `frobenius_norm_replicateCol`

English:
lemma frobenius_norm_replicateCol
  given: (v : n -> α)
  statement: ‖replicateCol ι v‖ = ‖toLp 2 v‖
  proof: by
  simp [frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]

@[simp]

中文:
引理 frobenius_norm_replicateCol
  条件: (v : n -> α)
  结论: ‖replicateCol ι v‖ = ‖toLp 2 v‖
  证明: by
  simp [frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]

@[simp]

Depends on / 依赖: PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow, frobenius_norm_def, norm_eq_of_L2, sqrt_eq_rpow
-/
lemma frobenius_norm_replicateCol (v : n -> α) : ‖replicateCol ι v‖ = ‖toLp 2 v‖ := by
  simp [frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]

@[simp]
/--
lemma `frobenius_nnnorm_replicateCol` / 引理 `frobenius_nnnorm_replicateCol`

English:
lemma frobenius_nnnorm_replicateCol
  given: (v : n -> α)
  statement: ‖replicateCol ι v‖₊ = ‖toLp 2 v‖₊
  proof: Subtype.ext frobenius_norm_replicateCol v

中文:
引理 frobenius_nnnorm_replicateCol
  条件: (v : n -> α)
  结论: ‖replicateCol ι v‖₊ = ‖toLp 2 v‖₊
  证明: Subtype.ext frobenius_norm_replicateCol v

Depends on / 依赖: Subtype, Subtype.ext, frobenius_norm_replicateCol
-/
lemma frobenius_nnnorm_replicateCol (v : n -> α) : ‖replicateCol ι v‖₊ = ‖toLp 2 v‖₊ :=
Subtype.ext frobenius_norm_replicateCol v

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `frobenius_nnnorm_diagonal` / 引理 `frobenius_nnnorm_diagonal`

English:
lemma frobenius_nnnorm_diagonal
  given: [DecidableEq n] (v : n -> α)
  statement: ‖diagonal v‖₊ = ‖toLp 2 v‖₊
  proof: by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map

中文:
引理 frobenius_nnnorm_diagonal
  条件: [DecidableEq n] (v : n -> α)
  结论: ‖diagonal v‖₊ = ‖toLp 2 v‖₊
  证明: by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map

Depends on / 依赖: Finset, Finset.mem_map.not.mp, Finset.subset_univ, Finset.sum_map, Finset.sum_product, Finset.sum_subset, Finset.univ, Finset.univ_product_univ, NNReal, NNReal.rpow_two, NNReal.sqrt_eq_rpow, NNReal.zero_rpow, PiLp.nnnorm_eq_of_L2, Prod.fst, congr_arg, diagonal_apply_eq, diagonal_apply_ne, frobenius_nnnorm_def, mem_map, nnnorm_eq_of_L2
-/
lemma frobenius_nnnorm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖₊ = ‖toLp 2 v‖₊ := by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map, NNReal.sqrt_eq_rpow]
    dsimp
    simp_rw [diagonal_apply_eq, NNReal.rpow_two]
  · suffices i.1 != i.2 by rw [diagonal_apply_ne _ this, nnnorm_zero, NNReal.zero_rpow two_ne_zero]
    intro h
    exact Finset.mem_map.not.mp his ⟨i.1, Finset.mem_univ _, Prod.ext rfl h⟩

@[simp]
/--
lemma `frobenius_norm_diagonal` / 引理 `frobenius_norm_diagonal`

English:
lemma frobenius_norm_diagonal
  given: [DecidableEq n] (v : n -> α)
  statement: ‖diagonal v‖ = ‖toLp 2 v‖
  proof: (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_diagonal v :).trans rfl

中文:
引理 frobenius_norm_diagonal
  条件: [DecidableEq n] (v : n -> α)
  结论: ‖diagonal v‖ = ‖toLp 2 v‖
  证明: (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_diagonal v :).trans rfl

Depends on / 依赖: congr_arg, frobenius_nnnorm_diagonal
-/
lemma frobenius_norm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖ = ‖toLp 2 v‖ :=
  (congr_arg ((↑) : Real>=0 -> Real) <| frobenius_nnnorm_diagonal v :).trans rfl

end SeminormedAddCommGroup

/--
theorem `frobenius_nnnorm_one` / 定理 `frobenius_nnnorm_one`

English:
theorem frobenius_nnnorm_one
  given: [DecidableEq n] [SeminormedAddCommGroup α] [One α]
  proof: by
  calc
    ‖(diagonal 1 : Matrix n n α)‖₊
    _ = ‖toLp 2 (Function.const _ 1)‖₊ := frobenius_nnnorm_diagonal _
    _ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
      rw [PiLp.nnnorm_toLp_const (ENNReal.ofNat_ne_top (n := 2))]
      simp [NNReal.sqrt_eq_rpow]

中文:
定理 frobenius_nnnorm_one
  条件: [DecidableEq n] [SeminormedAddComm群 α] [幺 α]
  证明: by
  calc
    ‖(diagonal 1 : Matrix n n α)‖₊
    _ = ‖toLp 2 (Function.const _ 1)‖₊ := frobenius_nnnorm_diagonal _
    _ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
      rw [PiLp.nnnorm_toLp_const (ENNReal.ofNat_ne_top (n := 2))]
      simp [NNReal.sqrt_eq_rpow]

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, Fintype, Fintype.card, Function, Function.const, Matrix, NNReal, NNReal.sqrt_eq_rpow, PiLp.nnnorm_toLp_const, diagonal, frobenius_nnnorm_diagonal, nnnorm_toLp_const, ofNat_ne_top, sqrt_eq_rpow
-/
theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ‖(1 : Matrix n n α)‖₊ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
  calc
    ‖(diagonal 1 : Matrix n n α)‖₊
    _ = ‖toLp 2 (Function.const _ 1)‖₊ := frobenius_nnnorm_diagonal _
    _ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
      rw [PiLp.nnnorm_toLp_const (ENNReal.ofNat_ne_top (n := 2))]
      simp [NNReal.sqrt_eq_rpow]

section RCLike

variable [RCLike α]

/--
theorem `frobenius_nnnorm_mul` / 定理 `frobenius_nnnorm_mul`

English:
theorem frobenius_nnnorm_mul
  given: (A : Matrix l m α) (B : Matrix m n α)
  statement: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  proof: by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow]; rw [@Finset.sum_comm _ _ m]; rw [Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos]; rw [← NNReal.rpow_mul]; rw [mul_div_cancel₀ (1 : Real) two_ne_zero]; rw [NNReal.rpow_one]; rw [NNRea

中文:
定理 frobenius_nnnorm_mul
  条件: (A : 矩阵 l m α) (B : 矩阵 m n α)
  结论: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  证明: by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow]; rw [@Finset.sum_comm _ _ m]; rw [Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos]; rw [← NNReal.rpow_mul]; rw [mul_div_cancel₀ (1 : Real) two_ne_zero]; rw [NNReal.rpow_one]; rw [NNRea

Depends on / 依赖: Finset, Finset.sum_comm, Finset.sum_mul_sum, Matrix, Matrix.mul_apply, NNReal, NNReal.mul_rpow, NNReal.rpow_le_rpow_iff, NNReal.rpow_mul, NNReal.rpow_one, NNReal.rpow_two, NNReal.sqrt_eq_rpow, Pi.nnnorm_def, PiLp.inner_apply, PiLp.nnnorm_eq_of_L2, PiLp.toLp_apply, RCLike, RCLike.inner_apply, frobenius_nnnorm_def, inner_apply
-/
theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow]; rw [@Finset.sum_comm _ _ m]; rw [Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos]; rw [← NNReal.rpow_mul]; rw [mul_div_cancel₀ (1 : Real) two_ne_zero]; rw [NNReal.rpow_one]; rw [NNReal.mul_rpow]
  simpa only [PiLp.toLp_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply,
    Pi.nnnorm_def, PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, NNReal.sqrt_eq_rpow,
    NNReal.rpow_two] using nnnorm_inner_le_nnnorm (𝕜 := α) (toLp 2 (star <| A i ·)) (toLp 2 (B · j))

/--
theorem `frobenius_norm_mul` / 定理 `frobenius_norm_mul`

English:
theorem frobenius_norm_mul
  given: (A : Matrix l m α) (B : Matrix m n α)
  statement: ‖A * B‖ <= ‖A‖ * ‖B‖
  proof: frobenius_nnnorm_mul A B

中文:
定理 frobenius_norm_mul
  条件: (A : 矩阵 l m α) (B : 矩阵 m n α)
  结论: ‖A * B‖ <= ‖A‖ * ‖B‖
  证明: frobenius_nnnorm_mul A B

Depends on / 依赖: frobenius_nnnorm_mul
-/
theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ <= ‖A‖ * ‖B‖ :=
  frobenius_nnnorm_mul A B

/-- Normed ring instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `frobeniusNormedRing` / `frobeniusNormedRing` 的定义

English:
definition frobeniusNormedRing
  signature: [DecidableEq m]
  body: { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm_mul_le := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
定义 frobeniusNormedRing
  签名: [DecidableEq m]
  定义体: { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm_mul_le := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Matrix, Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing, eq_of_dist_eq_zero, frobeniusSeminormedAddCommGroup, frobenius_norm_mul, instRing, norm_mul_le
-/
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm_mul_le := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/--
Definition of `frobeniusNormedAlgebra` / `frobeniusNormedAlgebra` 的定义

English:
definition frobeniusNormedAlgebra
  signature: [DecidableEq m] [NormedField R] [NormedAlgebra R α]
  body: { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }

中文:
定义 frobeniusNormedAlgebra
  签名: [DecidableEq m] [赋范域 R] [赋范代数 R α]
  定义体: { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }

Depends on / 依赖: Matrix, Matrix.frobeniusNormedSpace, Matrix.instAlgebra, frobeniusNormedSpace, instAlgebra
-/
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
    NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }

end RCLike

end frobenius

namespace Norms.Frobenius
attribute [scoped instance]
  Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
  Matrix.frobeniusIsBoundedSMul
  Matrix.frobeniusNormSMulClass
end Norms.Frobenius

end Matrix
