/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Diagonal matrices

This file contains the definition and basic results about diagonal matrices.

## Main results

- `Matrix.IsDiag`: a proposition that states a given square matrix `A` is diagonal.

## Tags

diag, diagonal, matrix
-/

@[expose] public section


namespace Matrix

variable {α β R n m : Type*}

open Function

open Matrix Kronecker

/--
Definition of `IsDiag` / `IsDiag` 的定义

English:
definition IsDiag
  signature: [Zero α] (A : Matrix n n α)
  body: Pairwise fun i j => A i j = 0

@[simp]

中文:
定义 IsDiag
  签名: [零 α] (A : 矩阵 n n α)
  定义体: Pairwise fun i j => A i j = 0

@[simp]

Depends on / 依赖: Pairwise
-/
def IsDiag [Zero α] (A : Matrix n n α) : Prop :=
  Pairwise fun i j => A i j = 0

@[simp]
/--
theorem `isDiag_diagonal` / 定理 `isDiag_diagonal`

English:
theorem isDiag_diagonal
  given: [Zero α] [DecidableEq n] (d : n -> α)
  statement: (diagonal d).IsDiag
  proof: fun _ _ =>
  Matrix.diagonal_apply_ne _

中文:
定理 isDiag_diagonal
  条件: [零 α] [DecidableEq n] (d : n -> α)
  结论: (diagonal d).IsDiag
  证明: fun _ _ =>
  Matrix.diagonal_apply_ne _
-/
theorem isDiag_diagonal [Zero α] [DecidableEq n] (d : n -> α) : (diagonal d).IsDiag := fun _ _ =>
  Matrix.diagonal_apply_ne _

/--
theorem `IsDiag.diagonal_diag` / 定理 `IsDiag.diagonal_diag`

English:
theorem IsDiag.diagonal_diag
  given: [Zero α] [DecidableEq n] {A : Matrix n n α} (h : A.IsDiag)
  proof: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [diagonal_apply_eq, diag]
    · rw [diagonal_apply_ne _ hij, h hij]

中文:
定理 IsDiag.diagonal_diag
  条件: [零 α] [DecidableEq n] {A : 矩阵 n n α} (h : A.IsDiag)
  证明: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [diagonal_apply_eq, diag]
    · rw [diagonal_apply_ne _ hij, h hij]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, diagonal_apply_eq, diagonal_apply_ne, eq_or_ne
-/
theorem IsDiag.diagonal_diag [Zero α] [DecidableEq n] {A : Matrix n n α} (h : A.IsDiag) :
    diagonal (diag A) = A :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [diagonal_apply_eq, diag]
    · rw [diagonal_apply_ne _ hij, h hij]

/--
theorem `isDiag_iff_diagonal_diag` / 定理 `isDiag_iff_diagonal_diag`

English:
theorem isDiag_iff_diagonal_diag
  given: [Zero α] [DecidableEq n] (A : Matrix n n α)
  proof: ⟨IsDiag.diagonal_diag, fun hd => hd ▸ isDiag_diagonal (diag A)⟩

中文:
定理 isDiag_iff_diagonal_diag
  条件: [零 α] [DecidableEq n] (A : 矩阵 n n α)
  证明: ⟨IsDiag.diagonal_diag, fun hd => hd ▸ isDiag_diagonal (diag A)⟩

Depends on / 依赖: IsDiag, IsDiag.diagonal_diag, diagonal_diag, isDiag_diagonal
-/
theorem isDiag_iff_diagonal_diag [Zero α] [DecidableEq n] (A : Matrix n n α) :
    A.IsDiag ↔ diagonal (diag A) = A :=
  ⟨IsDiag.diagonal_diag, fun hd => hd ▸ isDiag_diagonal (diag A)⟩

/--
theorem `isDiag_of_subsingleton` / 定理 `isDiag_of_subsingleton`

English:
theorem isDiag_of_subsingleton
  given: [Zero α] [Subsingleton n] (A : Matrix n n α)
  statement: A.IsDiag
  proof: fun i j h => (h <| Subsingleton.elim i j).elim

中文:
定理 isDiag_of_subsingleton
  条件: [零 α] [子单例 n] (A : 矩阵 n n α)
  结论: A.IsDiag
  证明: fun i j h => (h <| Subsingleton.elim i j).elim

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem isDiag_of_subsingleton [Zero α] [Subsingleton n] (A : Matrix n n α) : A.IsDiag :=
  fun i j h => (h <| Subsingleton.elim i j).elim

/-- Every zero matrix is diagonal. -/
@[simp]
/--
theorem `isDiag_zero` / 定理 `isDiag_zero`

English:
theorem isDiag_zero
  given: [Zero α]
  statement: (0 : Matrix n n α).IsDiag
  proof: fun _ _ _ => rfl

中文:
定理 isDiag_zero
  条件: [零 α]
  结论: (0 : 矩阵 n n α).IsDiag
  证明: fun _ _ _ => rfl
-/
theorem isDiag_zero [Zero α] : (0 : Matrix n n α).IsDiag := fun _ _ _ => rfl

/-- Every identity matrix is diagonal. -/
@[simp]
/--
theorem `isDiag_one` / 定理 `isDiag_one`

English:
theorem isDiag_one
  given: [DecidableEq n] [Zero α] [One α]
  statement: (1 : Matrix n n α).IsDiag
  proof: fun _ _ =>
  one_apply_ne

中文:
定理 isDiag_one
  条件: [DecidableEq n] [零 α] [幺 α]
  结论: (1 : 矩阵 n n α).IsDiag
  证明: fun _ _ =>
  one_apply_ne
-/
theorem isDiag_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsDiag := fun _ _ =>
  one_apply_ne

/--
theorem `IsDiag.map` / 定理 `IsDiag.map`

English:
theorem IsDiag.map
  given: [Zero α] [Zero β] {A : Matrix n n α} (ha : A.IsDiag) {f : α -> β} (hf : f 0 = 0)
  proof: by
  intro i j h
  simp [ha h, hf]

中文:
定理 IsDiag.map
  条件: [零 α] [零 β] {A : 矩阵 n n α} (ha : A.IsDiag) {f : α -> β} (hf : f 0 = 0)
  证明: by
  intro i j h
  simp [ha h, hf]
-/
theorem IsDiag.map [Zero α] [Zero β] {A : Matrix n n α} (ha : A.IsDiag) {f : α -> β} (hf : f 0 = 0) :
    (A.map f).IsDiag := by
  intro i j h
  simp [ha h, hf]

/--
theorem `IsDiag.neg` / 定理 `IsDiag.neg`

English:
theorem IsDiag.neg
  given: [SubtractionMonoid α] {A : Matrix n n α} (ha : A.IsDiag)
  statement: (-A).IsDiag
  proof: by
  intro i j h
  simp [ha h]

@[simp]

中文:
定理 IsDiag.neg
  条件: [Subtraction幺半群 α] {A : 矩阵 n n α} (ha : A.IsDiag)
  结论: (-A).IsDiag
  证明: by
  intro i j h
  simp [ha h]

@[simp]
-/
theorem IsDiag.neg [SubtractionMonoid α] {A : Matrix n n α} (ha : A.IsDiag) : (-A).IsDiag := by
  intro i j h
  simp [ha h]

@[simp]
/--
theorem `isDiag_neg_iff` / 定理 `isDiag_neg_iff`

English:
theorem isDiag_neg_iff
  given: [SubtractionMonoid α] {A : Matrix n n α}
  statement: (-A).IsDiag ↔ A.IsDiag
  proof: ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), IsDiag.neg⟩

中文:
定理 isDiag_neg_iff
  条件: [Subtraction幺半群 α] {A : 矩阵 n n α}
  结论: (-A).IsDiag ↔ A.IsDiag
  证明: ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), IsDiag.neg⟩

Depends on / 依赖: IsDiag, IsDiag.neg, neg_eq_zero
-/
theorem isDiag_neg_iff [SubtractionMonoid α] {A : Matrix n n α} : (-A).IsDiag ↔ A.IsDiag :=
  ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), IsDiag.neg⟩

/--
theorem `IsDiag.add` / 定理 `IsDiag.add`

English:
theorem IsDiag.add
  given: [AddZeroClass α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag)
  proof: by
  intro i j h
  simp [ha h, hb h]

中文:
定理 IsDiag.add
  条件: [加法零类 α] {A B : 矩阵 n n α} (ha : A.IsDiag) (hb : B.IsDiag)
  证明: by
  intro i j h
  simp [ha h, hb h]
-/
theorem IsDiag.add [AddZeroClass α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A + B).IsDiag := by
  intro i j h
  simp [ha h, hb h]

/--
theorem `IsDiag.sub` / 定理 `IsDiag.sub`

English:
theorem IsDiag.sub
  given: [SubtractionMonoid α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag)
  proof: by
  intro i j h
  simp [ha h, hb h]

中文:
定理 IsDiag.sub
  条件: [Subtraction幺半群 α] {A B : 矩阵 n n α} (ha : A.IsDiag) (hb : B.IsDiag)
  证明: by
  intro i j h
  simp [ha h, hb h]
-/
theorem IsDiag.sub [SubtractionMonoid α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A - B).IsDiag := by
  intro i j h
  simp [ha h, hb h]

/--
theorem `IsDiag.smul` / 定理 `IsDiag.smul`

English:
theorem IsDiag.smul
  statement: [Zero α] [SMulZeroClass R α] (k : R) {A : Matrix n n α}
  proof: by
  intro i j h
  simp [ha h]

@[simp]

中文:
定理 IsDiag.smul
  结论: [零 α] [SMulZero类 R α] (k : R) {A : 矩阵 n n α}
  证明: by
  intro i j h
  simp [ha h]

@[simp]
-/
theorem IsDiag.smul [Zero α] [SMulZeroClass R α] (k : R) {A : Matrix n n α}
    (ha : A.IsDiag) : (k • A).IsDiag := by
  intro i j h
  simp [ha h]

@[simp]
/--
theorem `isDiag_smul_one` / 定理 `isDiag_smul_one`

English:
theorem isDiag_smul_one
  given: (n) [MulZeroOneClass α] [DecidableEq n] (k : α)
  proof: isDiag_one.smul k

中文:
定理 isDiag_smul_one
  条件: (n) [乘零幺类 α] [DecidableEq n] (k : α)
  证明: isDiag_one.smul k

Depends on / 依赖: isDiag_one, isDiag_one.smul
-/
theorem isDiag_smul_one (n) [MulZeroOneClass α] [DecidableEq n] (k : α) :
    (k • (1 : Matrix n n α)).IsDiag :=
  isDiag_one.smul k

/--
theorem `IsDiag.transpose` / 定理 `IsDiag.transpose`

English:
theorem IsDiag.transpose
  given: [Zero α] {A : Matrix n n α} (ha : A.IsDiag)
  statement: Aᵀ.IsDiag
  proof: fun _ _ h =>
  ha h.symm

@[simp]

中文:
定理 IsDiag.transpose
  条件: [零 α] {A : 矩阵 n n α} (ha : A.IsDiag)
  结论: Aᵀ.IsDiag
  证明: fun _ _ h =>
  ha h.symm

@[simp]
-/
theorem IsDiag.transpose [Zero α] {A : Matrix n n α} (ha : A.IsDiag) : Aᵀ.IsDiag := fun _ _ h =>
  ha h.symm

@[simp]
/--
theorem `isDiag_transpose_iff` / 定理 `isDiag_transpose_iff`

English:
theorem isDiag_transpose_iff
  given: [Zero α] {A : Matrix n n α}
  statement: Aᵀ.IsDiag ↔ A.IsDiag
  proof: ⟨IsDiag.transpose, IsDiag.transpose⟩

中文:
定理 isDiag_transpose_iff
  条件: [零 α] {A : 矩阵 n n α}
  结论: Aᵀ.IsDiag ↔ A.IsDiag
  证明: ⟨IsDiag.transpose, IsDiag.transpose⟩

Depends on / 依赖: IsDiag, IsDiag.transpose, transpose
-/
theorem isDiag_transpose_iff [Zero α] {A : Matrix n n α} : Aᵀ.IsDiag ↔ A.IsDiag :=
  ⟨IsDiag.transpose, IsDiag.transpose⟩

/--
theorem `IsDiag.conjTranspose` / 定理 `IsDiag.conjTranspose`

English:
theorem IsDiag.conjTranspose
  statement: [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α}
  proof: ha.transpose.map (star_zero _)

@[simp]

中文:
定理 IsDiag.conjTranspose
  结论: [非幺非结合半环 α] [对合环 α] {A : 矩阵 n n α}
  证明: ha.transpose.map (star_zero _)

@[simp]

Depends on / 依赖: ha.transpose.map, star_zero, transpose
-/
theorem IsDiag.conjTranspose [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α}
    (ha : A.IsDiag) : Aᴴ.IsDiag :=
  ha.transpose.map (star_zero _)

@[simp]
/--
theorem `isDiag_conjTranspose_iff` / 定理 `isDiag_conjTranspose_iff`

English:
theorem isDiag_conjTranspose_iff
  given: [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α}
  proof: ⟨fun ha => by
    convert! ha.conjTranspose
    simp, IsDiag.conjTranspose⟩

中文:
定理 isDiag_conjTranspose_iff
  条件: [非幺非结合半环 α] [对合环 α] {A : 矩阵 n n α}
  证明: ⟨fun ha => by
    convert! ha.conjTranspose
    simp, IsDiag.conjTranspose⟩

Depends on / 依赖: IsDiag, IsDiag.conjTranspose, conjTranspose, convert, ha.conjTranspose
-/
theorem isDiag_conjTranspose_iff [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α} :
    Aᴴ.IsDiag ↔ A.IsDiag :=
  ⟨fun ha => by
    convert! ha.conjTranspose
    simp, IsDiag.conjTranspose⟩

/--
theorem `IsDiag.submatrix` / 定理 `IsDiag.submatrix`

English:
theorem IsDiag.submatrix
  statement: [Zero α] {A : Matrix n n α} (ha : A.IsDiag) {f : m -> n}
  proof: fun _ _ h => ha (hf.ne h)

中文:
定理 IsDiag.submatrix
  结论: [零 α] {A : 矩阵 n n α} (ha : A.IsDiag) {f : m -> n}
  证明: fun _ _ h => ha (hf.ne h)

Depends on / 依赖: hf.ne
-/
theorem IsDiag.submatrix [Zero α] {A : Matrix n n α} (ha : A.IsDiag) {f : m -> n}
    (hf : Injective f) : (A.submatrix f f).IsDiag := fun _ _ h => ha (hf.ne h)

/--
theorem `IsDiag.kronecker` / 定理 `IsDiag.kronecker`

English:
theorem IsDiag.kronecker
  statement: [MulZeroClass α] {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsDiag)
  proof: by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk_inj, Ne, not_and_or] at h
  rcases h with hac | hbd
  · simp [hA hac]
  · simp [hB hbd]

中文:
定理 IsDiag.kronecker
  结论: [乘零类 α] {A : 矩阵 m m α} {B : 矩阵 n n α} (hA : A.IsDiag)
  证明: by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk_inj, Ne, not_and_or] at h
  rcases h with hac | hbd
  · simp [hA hac]
  · simp [hB hbd]

Depends on / 依赖: Prod.mk_inj, mk_inj, not_and_or
-/
theorem IsDiag.kronecker [MulZeroClass α] {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsDiag)
    (hB : B.IsDiag) : (A otimesₖ B).IsDiag := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk_inj, Ne, not_and_or] at h
  rcases h with hac | hbd
  · simp [hA hac]
  · simp [hB hbd]

/--
theorem `IsDiag.isSymm` / 定理 `IsDiag.isSymm`

English:
theorem IsDiag.isSymm
  given: [Zero α] {A : Matrix n n α} (h : A.IsDiag)
  statement: A.IsSymm
  proof: by
  ext i j
  by_cases g : i = j; · rw [g, transpose_apply]
  simp [h g, h (Ne.symm g)]

中文:
定理 IsDiag.isSymm
  条件: [零 α] {A : 矩阵 n n α} (h : A.IsDiag)
  结论: A.是Symm
  证明: by
  ext i j
  by_cases g : i = j; · rw [g, transpose_apply]
  simp [h g, h (Ne.symm g)]

Depends on / 依赖: Ne.symm, transpose_apply
-/
theorem IsDiag.isSymm [Zero α] {A : Matrix n n α} (h : A.IsDiag) : A.IsSymm := by
  ext i j
  by_cases g : i = j; · rw [g, transpose_apply]
  simp [h g, h (Ne.symm g)]

/--
theorem `IsDiag.fromBlocks` / 定理 `IsDiag.fromBlocks`

English:
theorem IsDiag.fromBlocks
  statement: [Zero α] {A : Matrix m m α} {D : Matrix n n α} (ha : A.IsDiag)
  proof: by
  rintro (i | i) (j | j) hij
  · exact ha (ne_of_apply_ne _ hij)
  · rfl
  · rfl
  · exact hd (ne_of_apply_ne _ hij)

中文:
定理 IsDiag.fromBlocks
  结论: [零 α] {A : 矩阵 m m α} {D : 矩阵 n n α} (ha : A.IsDiag)
  证明: by
  rintro (i | i) (j | j) hij
  · exact ha (ne_of_apply_ne _ hij)
  · rfl
  · rfl
  · exact hd (ne_of_apply_ne _ hij)

Depends on / 依赖: ne_of_apply_ne
-/
theorem IsDiag.fromBlocks [Zero α] {A : Matrix m m α} {D : Matrix n n α} (ha : A.IsDiag)
    (hd : D.IsDiag) : (A.fromBlocks 0 0 D).IsDiag := by
  rintro (i | i) (j | j) hij
  · exact ha (ne_of_apply_ne _ hij)
  · rfl
  · rfl
  · exact hd (ne_of_apply_ne _ hij)

/--
theorem `isDiag_fromBlocks_iff` / 定理 `isDiag_fromBlocks_iff`

English:
theorem isDiag_fromBlocks_iff
  statement: [Zero α] {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
  proof: by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ext fun i j => ?_, ext fun i j => ?_, fun i j hij => ?_⟩
    · exact h (Sum.inl_injective.ne hij)
    · exact h Sum.inl_ne_inr
    · exact h Sum.inr_ne_inl
    · exact h (Sum.inr_injective.ne hij)
  · rintro ⟨ha, hb, hc, hd⟩
    convert! Is

中文:
定理 isDiag_fromBlocks_iff
  结论: [零 α] {A : 矩阵 m m α} {B : 矩阵 m n α} {C : 矩阵 n m α}
  证明: by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ext fun i j => ?_, ext fun i j => ?_, fun i j hij => ?_⟩
    · exact h (Sum.inl_injective.ne hij)
    · exact h Sum.inl_ne_inr
    · exact h Sum.inr_ne_inl
    · exact h (Sum.inr_injective.ne hij)
  · rintro ⟨ha, hb, hc, hd⟩
    convert! Is

Depends on / 依赖: IsDiag, IsDiag.fromBlocks, Sum.inl_injective.ne, Sum.inl_ne_inr, Sum.inr_injective.ne, Sum.inr_ne_inl, convert, fromBlocks, inl_injective, inl_ne_inr, inr_injective, inr_ne_inl
-/
theorem isDiag_fromBlocks_iff [Zero α] {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsDiag ↔ A.IsDiag ∧ B = 0 ∧ C = 0 ∧ D.IsDiag := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ext fun i j => ?_, ext fun i j => ?_, fun i j hij => ?_⟩
    · exact h (Sum.inl_injective.ne hij)
    · exact h Sum.inl_ne_inr
    · exact h Sum.inr_ne_inl
    · exact h (Sum.inr_injective.ne hij)
  · rintro ⟨ha, hb, hc, hd⟩
    convert! IsDiag.fromBlocks ha hd

/--
theorem `IsDiag.fromBlocks_of_isSymm` / 定理 `IsDiag.fromBlocks_of_isSymm`

English:
theorem IsDiag.fromBlocks_of_isSymm
  statement: [Zero α] {A : Matrix m m α} {C : Matrix n m α}
  proof: by
  rw [← (isSymm_fromBlocks_iff.1 h).2.1]
  exact ha.fromBlocks hd

中文:
定理 IsDiag.fromBlocks_of_isSymm
  结论: [零 α] {A : 矩阵 m m α} {C : 矩阵 n m α}
  证明: by
  rw [← (isSymm_fromBlocks_iff.1 h).2.1]
  exact ha.fromBlocks hd

Depends on / 依赖: fromBlocks, ha.fromBlocks, isSymm_fromBlocks_iff
-/
theorem IsDiag.fromBlocks_of_isSymm [Zero α] {A : Matrix m m α} {C : Matrix n m α}
    {D : Matrix n n α} (h : (A.fromBlocks 0 C D).IsSymm) (ha : A.IsDiag) (hd : D.IsDiag) :
    (A.fromBlocks 0 C D).IsDiag := by
  rw [← (isSymm_fromBlocks_iff.1 h).2.1]
  exact ha.fromBlocks hd

/--
theorem `mul_transpose_self_isDiag_iff_hasOrthogonalRows` / 定理 `mul_transpose_self_isDiag_iff_hasOrthogonalRows`

English:
theorem mul_transpose_self_isDiag_iff_hasOrthogonalRows
  statement: [Fintype n] [Mul α] [AddCommMonoid α]
  proof: Iff.rfl

中文:
定理 mul_transpose_self_isDiag_iff_hasOrthogonalRows
  结论: [有限类型 n] [乘法 α] [加法交换幺半群 α]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mul_transpose_self_isDiag_iff_hasOrthogonalRows [Fintype n] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (A * Aᵀ).IsDiag ↔ A.HasOrthogonalRows :=
  Iff.rfl

/--
theorem `transpose_mul_self_isDiag_iff_hasOrthogonalCols` / 定理 `transpose_mul_self_isDiag_iff_hasOrthogonalCols`

English:
theorem transpose_mul_self_isDiag_iff_hasOrthogonalCols
  statement: [Fintype m] [Mul α] [AddCommMonoid α]
  proof: Iff.rfl

中文:
定理 transpose_mul_self_isDiag_iff_hasOrthogonalCols
  结论: [有限类型 m] [乘法 α] [加法交换幺半群 α]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem transpose_mul_self_isDiag_iff_hasOrthogonalCols [Fintype m] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (Aᵀ * A).IsDiag ↔ A.HasOrthogonalCols :=
  Iff.rfl

end Matrix
