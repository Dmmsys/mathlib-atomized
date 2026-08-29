/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.ZPow

/-! # Hermitian matrices

This file defines Hermitian matrices and some basic results about them.

See also `IsSelfAdjoint`, which generalizes this definition to other star rings.

## Main definition

* `Matrix.IsHermitian` : a matrix `A : Matrix n n α` is Hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidAlgebra
assert_not_exists NormedGroup

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section Star

variable [Star α] [Star β]

/--
Definition of `IsHermitian` / `IsHermitian` 的定义

English:
definition IsHermitian
  signature: (A : Matrix n n α)
  body: Aᴴ = A

中文:
定义 IsHermitian
  签名: (A : 矩阵 n n α)
  定义体: Aᴴ = A
-/
def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A

instance (A : Matrix n n α) [Decidable (Aᴴ = A)] : Decidable (IsHermitian A) :=
inferInstanceAs Decidable (_ = _)

/--
theorem `IsHermitian.eq` / 定理 `IsHermitian.eq`

English:
theorem IsHermitian.eq
  given: {A : Matrix n n α} (h : A.IsHermitian)
  statement: Aᴴ = A
  proof: h

中文:
定理 IsHermitian.eq
  条件: {A : 矩阵 n n α} (h : A.IsHermitian)
  结论: Aᴴ = A
  证明: h
-/
theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A := h

/--
theorem `isHermitian_iff_isSelfAdjoint` / 定理 `isHermitian_iff_isSelfAdjoint`

English:
theorem isHermitian_iff_isSelfAdjoint
  given: {A : Matrix n n α}
  proof: Iff.rfl

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint

中文:
定理 isHermitian_iff_isSelfAdjoint
  条件: {A : 矩阵 n n α}
  证明: Iff.rfl

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint

Depends on / 依赖: Iff.rfl
-/
theorem isHermitian_iff_isSelfAdjoint {A : Matrix n n α} :
    A.IsHermitian ↔ IsSelfAdjoint A := Iff.rfl

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint

/--
theorem `IsHermitian.star_eq` / 定理 `IsHermitian.star_eq`

English:
theorem IsHermitian.star_eq
  given: (hA : A.IsHermitian)
  statement: star A = A
  proof: hA.isSelfAdjoint.star_eq

中文:
定理 IsHermitian.star_eq
  条件: (hA : A.IsHermitian)
  结论: star A = A
  证明: hA.isSelfAdjoint.star_eq

Depends on / 依赖: hA.isSelfAdjoint.star_eq, isSelfAdjoint, star_eq
-/
theorem IsHermitian.star_eq (hA : A.IsHermitian) : star A = A := hA.isSelfAdjoint.star_eq

/--
theorem `IsHermitian.ext` / 定理 `IsHermitian.ext`

English:
theorem IsHermitian.ext
  given: {A : Matrix n n α}
  statement: (forall i j, star (A j i) = A i j) -> A.IsHermitian
  proof: by
  intro h; ext i j; exact h i j

中文:
定理 IsHermitian.ext
  条件: {A : 矩阵 n n α}
  结论: (对任意 i j, star (A j i) = A i j) -> A.IsHermitian
  证明: by
  intro h; ext i j; exact h i j
-/
theorem IsHermitian.ext {A : Matrix n n α} : (forall i j, star (A j i) = A i j) -> A.IsHermitian := by
  intro h; ext i j; exact h i j

/--
theorem `IsHermitian.apply` / 定理 `IsHermitian.apply`

English:
theorem IsHermitian.apply
  given: {A : Matrix n n α} (h : A.IsHermitian) (i j : n)
  statement: star (A j i) = A i j
  proof: congr_fun (congr_fun h _) _

中文:
定理 IsHermitian.apply
  条件: {A : 矩阵 n n α} (h : A.IsHermitian) (i j : n)
  结论: star (A j i) = A i j
  证明: congr_fun (congr_fun h _) _

Depends on / 依赖: congr_fun
-/
theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _

/--
theorem `IsHermitian.ext_iff` / 定理 `IsHermitian.ext_iff`

English:
theorem IsHermitian.ext_iff
  given: {A : Matrix n n α}
  statement: A.IsHermitian ↔ forall i j, star (A j i) = A i j
  proof: ⟨IsHermitian.apply, IsHermitian.ext⟩

中文:
定理 IsHermitian.ext_iff
  条件: {A : 矩阵 n n α}
  结论: A.IsHermitian ↔ 对任意 i j, star (A j i) = A i j
  证明: ⟨IsHermitian.apply, IsHermitian.ext⟩

Depends on / 依赖: IsHermitian, IsHermitian.apply, IsHermitian.ext
-/
theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ forall i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩

/--
lemma `isHermitian_iff_isSymm` / 引理 `isHermitian_iff_isSymm`

English:
lemma isHermitian_iff_isSymm
  given: [TrivialStar α] {A : Matrix n n α}
  proof: by
  simp [IsHermitian.ext_iff, IsSymm.ext_iff]

@[simp]

中文:
引理 isHermitian_iff_isSymm
  条件: [TrivialStar α] {A : 矩阵 n n α}
  证明: by
  simp [IsHermitian.ext_iff, IsSymm.ext_iff]

@[simp]
-/
@[simp] lemma isHermitian_iff_isSymm [TrivialStar α] {A : Matrix n n α} :
    A.IsHermitian ↔ A.IsSymm := by
  simp [IsHermitian.ext_iff, IsSymm.ext_iff]

@[simp]
/--
theorem `IsHermitian.map` / 定理 `IsHermitian.map`

English:
theorem IsHermitian.map
  statement: {A : Matrix n n α} (h : A.IsHermitian) (f : α -> β)
  proof: by
  rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [h.eq]

@[simp]

中文:
定理 IsHermitian.map
  结论: {A : 矩阵 n n α} (h : A.IsHermitian) (f : α -> β)
  证明: by
  rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [h.eq]

@[simp]

Depends on / 依赖: IsHermitian, conjTranspose_map, h.eq
-/
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α -> β)
    (hf : Function.Semiconj f star star) : (A.map f).IsHermitian := by
  rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [h.eq]

@[simp]
/--
theorem `isHermitian_map_iff` / 定理 `isHermitian_map_iff`

English:
theorem isHermitian_map_iff
  statement: {A : Matrix n n α} {f : α -> β} (hf : Function.Semiconj f star star)
  proof: by
  rw [IsHermitian]; rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [map_injective hinj |>.eq_iff]

@[simp, nontriviality]

中文:
定理 isHermitian_map_iff
  结论: {A : 矩阵 n n α} {f : α -> β} (hf : 函数.Semiconj f star star)
  证明: by
  rw [IsHermitian]; rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [map_injective hinj |>.eq_iff]

@[simp, nontriviality]

Depends on / 依赖: IsHermitian, conjTranspose_map, eq_iff, map_injective
-/
theorem isHermitian_map_iff {A : Matrix n n α} {f : α -> β} (hf : Function.Semiconj f star star)
    (hinj : f.Injective) : (A.map f).IsHermitian ↔ A.IsHermitian := by
  rw [IsHermitian]; rw [IsHermitian]; rw [← conjTranspose_map f hf]; rw [map_injective hinj |>.eq_iff]

@[simp, nontriviality]
/--
theorem `IsHermitian.of_subsingleton` / 定理 `IsHermitian.of_subsingleton`

English:
theorem IsHermitian.of_subsingleton
  given: {A : Matrix n n α} [Subsingleton α]
  statement: A.IsHermitian
  proof: .ext fun _ _ => Subsingleton.elim ..

中文:
定理 IsHermitian.of_subsingleton
  条件: {A : 矩阵 n n α} [子单例 α]
  结论: A.IsHermitian
  证明: .ext fun _ _ => Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem IsHermitian.of_subsingleton {A : Matrix n n α} [Subsingleton α] : A.IsHermitian :=
  .ext fun _ _ => Subsingleton.elim ..

/--
theorem `IsHermitian.transpose` / 定理 `IsHermitian.transpose`

English:
theorem IsHermitian.transpose
  given: {A : Matrix n n α} (h : A.IsHermitian)
  statement: Aᵀ.IsHermitian
  proof: by
  rw [IsHermitian]; rw [conjTranspose]; rw [transpose_map]
  exact congr_arg Matrix.transpose h

@[simp]

中文:
定理 IsHermitian.transpose
  条件: {A : 矩阵 n n α} (h : A.IsHermitian)
  结论: Aᵀ.IsHermitian
  证明: by
  rw [IsHermitian]; rw [conjTranspose]; rw [transpose_map]
  exact congr_arg Matrix.transpose h

@[simp]

Depends on / 依赖: IsHermitian, Matrix, Matrix.transpose, congr_arg, conjTranspose, transpose, transpose_map
-/
theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose]; rw [transpose_map]
  exact congr_arg Matrix.transpose h

@[simp]
/--
theorem `isHermitian_transpose_iff` / 定理 `isHermitian_transpose_iff`

English:
theorem isHermitian_transpose_iff
  given: {A : Matrix n n α}
  statement: Aᵀ.IsHermitian ↔ A.IsHermitian
  proof: ⟨by intro h; rw [← transpose_transpose A]; exact IsHermitian.transpose h, IsHermitian.transpose⟩

中文:
定理 isHermitian_transpose_iff
  条件: {A : 矩阵 n n α}
  结论: Aᵀ.IsHermitian ↔ A.IsHermitian
  证明: ⟨by intro h; rw [← transpose_transpose A]; exact IsHermitian.transpose h, IsHermitian.transpose⟩

Depends on / 依赖: IsHermitian, IsHermitian.transpose, transpose, transpose_transpose
-/
theorem isHermitian_transpose_iff {A : Matrix n n α} : Aᵀ.IsHermitian ↔ A.IsHermitian :=
  ⟨by intro h; rw [← transpose_transpose A]; exact IsHermitian.transpose h, IsHermitian.transpose⟩

/--
theorem `IsHermitian.conjTranspose` / 定理 `IsHermitian.conjTranspose`

English:
theorem IsHermitian.conjTranspose
  given: {A : Matrix n n α} (h : A.IsHermitian)
  statement: Aᴴ.IsHermitian
  proof: h.transpose.map _ fun _ => rfl

@[simp]

中文:
定理 IsHermitian.conjTranspose
  条件: {A : 矩阵 n n α} (h : A.IsHermitian)
  结论: Aᴴ.IsHermitian
  证明: h.transpose.map _ fun _ => rfl

@[simp]

Depends on / 依赖: h.transpose.map, transpose
-/
theorem IsHermitian.conjTranspose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  h.transpose.map _ fun _ => rfl

@[simp]
/--
theorem `IsHermitian.submatrix` / 定理 `IsHermitian.submatrix`

English:
theorem IsHermitian.submatrix
  given: {A : Matrix n n α} (h : A.IsHermitian) (f : m -> n)
  proof: (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp]

中文:
定理 IsHermitian.submatrix
  条件: {A : 矩阵 n n α} (h : A.IsHermitian) (f : m -> n)
  证明: (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp]

Depends on / 依赖: conjTranspose_submatrix, h.symm
-/
theorem IsHermitian.submatrix {A : Matrix n n α} (h : A.IsHermitian) (f : m -> n) :
    (A.submatrix f f).IsHermitian := (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp]
/--
theorem `isHermitian_submatrix_equiv` / 定理 `isHermitian_submatrix_equiv`

English:
theorem isHermitian_submatrix_equiv
  given: {A : Matrix n n α} (e : m ≃ n)
  proof: ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

中文:
定理 isHermitian_submatrix_equiv
  条件: {A : 矩阵 n n α} (e : m ≃ n)
  证明: ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

Depends on / 依赖: e.symm, h.submatrix, submatrix
-/
theorem isHermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) :
    (A.submatrix e e).IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

/--
theorem `IsHermitian.reindex` / 定理 `IsHermitian.reindex`

English:
theorem IsHermitian.reindex
  given: {A : Matrix n n α} (h : A.IsHermitian) (f : n ≃ m)
  proof: by
  rw [reindex_apply]
  apply submatrix h

中文:
定理 IsHermitian.reindex
  条件: {A : 矩阵 n n α} (h : A.IsHermitian) (f : n ≃ m)
  证明: by
  rw [reindex_apply]
  apply submatrix h

Depends on / 依赖: reindex_apply, submatrix
-/
theorem IsHermitian.reindex {A : Matrix n n α} (h : A.IsHermitian) (f : n ≃ m) :
    (A.reindex f f).IsHermitian := by
  rw [reindex_apply]
  apply submatrix h

/--
theorem `isHermitian_reindex_iff` / 定理 `isHermitian_reindex_iff`

English:
theorem isHermitian_reindex_iff
  given: {A : Matrix n n α} (f : n ≃ m)
  proof: by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

中文:
定理 isHermitian_reindex_iff
  条件: {A : 矩阵 n n α} (f : n ≃ m)
  证明: by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

Depends on / 依赖: f.symm, h.reindex, reindex
-/
theorem isHermitian_reindex_iff {A : Matrix n n α} (f : n ≃ m) :
    (A.reindex f f).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

/--
theorem `conjTranspose_comp` / 定理 `conjTranspose_comp`

English:
theorem conjTranspose_comp
  given: {I J K L : Type*} (M : Matrix I J (Matrix K L α))
  proof: rfl

中文:
定理 conjTranspose_comp
  条件: {I J K L : 类型} (M : 矩阵 I J (矩阵 K L α))
  证明: rfl
-/
theorem conjTranspose_comp {I J K L : Type*} (M : Matrix I J (Matrix K L α)) :
    (comp I J K L α M)ᴴ = comp J I L K α (Mᵀ.map (·ᴴ)) :=
  rfl

/--
theorem `conjTranspose_comp'` / 定理 `conjTranspose_comp'`

English:
theorem conjTranspose_comp'
  given: {I J K : Type*} (M : Matrix I J (Matrix K K α))
  proof: rfl

中文:
定理 conjTranspose_comp'
  条件: {I J K : 类型} (M : 矩阵 I J (矩阵 K K α))
  证明: rfl
-/
theorem conjTranspose_comp' {I J K : Type*} (M : Matrix I J (Matrix K K α)) :
    (comp I J K K α M)ᴴ = comp J I K K α Mᴴ :=
  rfl

/--
theorem `isHermitian_comp_iff` / 定理 `isHermitian_comp_iff`

English:
theorem isHermitian_comp_iff
  given: {A : Matrix m m (Matrix n n α)}
  proof: by
  rw [IsHermitian]; rw [IsHermitian]; rw [conjTranspose_comp']; rw [comp .. |>.injective.eq_iff]

中文:
定理 isHermitian_comp_iff
  条件: {A : 矩阵 m m (矩阵 n n α)}
  证明: by
  rw [IsHermitian]; rw [IsHermitian]; rw [conjTranspose_comp']; rw [comp .. |>.injective.eq_iff]

Depends on / 依赖: IsHermitian, conjTranspose_comp, eq_iff, injective, injective.eq_iff
-/
theorem isHermitian_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ A.IsHermitian := by
  rw [IsHermitian]; rw [IsHermitian]; rw [conjTranspose_comp']; rw [comp .. |>.injective.eq_iff]

/--
theorem `isHermitian_comp_iff_forall` / 定理 `isHermitian_comp_iff_forall`

English:
theorem isHermitian_comp_iff_forall
  given: {A : Matrix m m (Matrix n n α)}
  proof: by
  simp [IsHermitian.ext_iff]
  grind

中文:
定理 isHermitian_comp_iff_对任意
  条件: {A : 矩阵 m m (矩阵 n n α)}
  证明: by
  simp [IsHermitian.ext_iff]
  grind

Depends on / 依赖: IsHermitian, IsHermitian.ext_iff, ext_iff
-/
theorem isHermitian_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ forall i j i' j', star (A j i j' i') = A i j i' j' := by
  simp [IsHermitian.ext_iff]
  grind

end Star

section InvolutiveStar

variable [InvolutiveStar α]

@[simp]
/--
theorem `isHermitian_conjTranspose_iff` / 定理 `isHermitian_conjTranspose_iff`

English:
theorem isHermitian_conjTranspose_iff
  given: {A : Matrix n n α}
  statement: Aᴴ.IsHermitian ↔ A.IsHermitian
  proof: IsSelfAdjoint.star_iff

中文:
定理 isHermitian_conjTranspose_iff
  条件: {A : 矩阵 n n α}
  结论: Aᴴ.IsHermitian ↔ A.IsHermitian
  证明: IsSelfAdjoint.star_iff

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_iff, star_iff
-/
theorem isHermitian_conjTranspose_iff {A : Matrix n n α} : Aᴴ.IsHermitian ↔ A.IsHermitian :=
  IsSelfAdjoint.star_iff

/--
theorem `IsHermitian.fromBlocks` / 定理 `IsHermitian.fromBlocks`

English:
theorem IsHermitian.fromBlocks
  statement: {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
  proof: by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose]; rw [hBC]; rw [hCB]; rw [hA]; rw [hD]

中文:
定理 IsHermitian.fromBlocks
  结论: {A : 矩阵 m m α} {B : 矩阵 m n α} {C : 矩阵 n m α}
  证明: by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose]; rw [hBC]; rw [hCB]; rw [hA]; rw [hD]

Depends on / 依赖: IsHermitian, Matrix, Matrix.IsHermitian, conjTranspose_conjTranspose, fromBlocks_conjTranspose
-/
theorem IsHermitian.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose]; rw [hBC]; rw [hCB]; rw [hA]; rw [hD]

/--
theorem `isHermitian_fromBlocks_iff` / 定理 `isHermitian_fromBlocks_iff`

English:
theorem isHermitian_fromBlocks_iff
  statement: {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
  proof: ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, _hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩

中文:
定理 isHermitian_fromBlocks_iff
  结论: {A : 矩阵 m m α} {B : 矩阵 m n α} {C : 矩阵 n m α}
  证明: ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, _hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩

Depends on / 依赖: IsHermitian, IsHermitian.fromBlocks, _hCB, congr_arg, fromBlocks
-/
theorem isHermitian_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, _hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩

end InvolutiveStar

/--
theorem `IsHermitian.hadamard` / 定理 `IsHermitian.hadamard`

English:
theorem IsHermitian.hadamard
  statement: [CommMonoid α] [StarMul α] {A B : Matrix n n α}
  proof: by
  rw [IsHermitian]; rw [conjTranspose_hadamard]; rw [hB.eq]; rw [hA.eq]; rw [hadamard_comm]

中文:
定理 IsHermitian.hadamard
  结论: [交换幺半群 α] [StarMul α] {A B : 矩阵 n n α}
  证明: by
  rw [IsHermitian]; rw [conjTranspose_hadamard]; rw [hB.eq]; rw [hA.eq]; rw [hadamard_comm]

Depends on / 依赖: IsHermitian, conjTranspose_hadamard, hA.eq, hB.eq, hadamard_comm
-/
theorem IsHermitian.hadamard [CommMonoid α] [StarMul α] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊙ B).IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose_hadamard]; rw [hB.eq]; rw [hA.eq]; rw [hadamard_comm]

section AddMonoid

variable [AddMonoid α] [StarAddMonoid α]

/--
theorem `isHermitian_diagonal_of_self_adjoint` / 定理 `isHermitian_diagonal_of_self_adjoint`

English:
theorem isHermitian_diagonal_of_self_adjoint
  given: [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v)
  proof: (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

中文:
定理 isHermitian_diagonal_of_self_adjoint
  条件: [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v)
  证明: (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

Depends on / 依赖: congr_arg, diagonal_conjTranspose, has_trivial_star, instance, pi.has_trivial_star, remove
-/
theorem isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v) :
    (diagonal v).IsHermitian :=
  (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

/--
lemma `isHermitian_diagonal_iff` / 引理 `isHermitian_diagonal_iff`

English:
lemma isHermitian_diagonal_iff
  given: [DecidableEq n] {d : n -> α}
  proof: by
  simp [isSelfAdjoint_iff, IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

中文:
引理 isHermitian_diagonal_iff
  条件: [DecidableEq n] {d : n -> α}
  证明: by
  simp [isSelfAdjoint_iff, IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

Depends on / 依赖: IsHermitian, conjTranspose, diagonal_map, diagonal_transpose, isSelfAdjoint_iff
-/
lemma isHermitian_diagonal_iff [DecidableEq n] {d : n -> α} :
    IsHermitian (diagonal d) ↔ (forall i : n, IsSelfAdjoint (d i)) := by
  simp [isSelfAdjoint_iff, IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

/--
theorem `isHermitian_blockDiagonal'_iff` / 定理 `isHermitian_blockDiagonal'_iff`

English:
theorem isHermitian_blockDiagonal'_iff
  statement: [DecidableEq n] {p : n -> Type*}
  proof: by
  grind [IsHermitian, blockDiagonal'_conjTranspose, blockDiagonal'_inj]

中文:
定理 isHermitian_blockDiagonal'_iff
  结论: [DecidableEq n] {p : n -> 类型}
  证明: by
  grind [IsHermitian, blockDiagonal'_conjTranspose, blockDiagonal'_inj]

Depends on / 依赖: IsHermitian, _conjTranspose, _inj, blockDiagonal
-/
theorem isHermitian_blockDiagonal'_iff [DecidableEq n] {p : n -> Type*}
    {M : forall i, Matrix (p i) (p i) α} : (blockDiagonal' M).IsHermitian ↔ forall i, (M i).IsHermitian := by
  grind [IsHermitian, blockDiagonal'_conjTranspose, blockDiagonal'_inj]

/--
theorem `isHermitian_blockDiagonal_iff` / 定理 `isHermitian_blockDiagonal_iff`

English:
theorem isHermitian_blockDiagonal_iff
  given: [DecidableEq n] {M : n -> Matrix m m α}
  proof: by
  simpa [IsHermitian] using isHermitian_blockDiagonal'_iff

中文:
定理 isHermitian_blockDiagonal_iff
  条件: [DecidableEq n] {M : n -> 矩阵 m m α}
  证明: by
  simpa [IsHermitian] using isHermitian_blockDiagonal'_iff

Depends on / 依赖: IsHermitian, _iff, isHermitian_blockDiagonal
-/
theorem isHermitian_blockDiagonal_iff [DecidableEq n] {M : n -> Matrix m m α} :
    (blockDiagonal M).IsHermitian ↔ forall i, (M i).IsHermitian := by
  simpa [IsHermitian] using isHermitian_blockDiagonal'_iff

/--
theorem `isHermitian_diagonal` / 定理 `isHermitian_diagonal`

English:
theorem isHermitian_diagonal
  given: [TrivialStar α] [DecidableEq n] (v : n -> α)
  proof: isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

@[simp]

中文:
定理 isHermitian_diagonal
  条件: [TrivialStar α] [DecidableEq n] (v : n -> α)
  证明: isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

@[simp]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.all, isHermitian_diagonal_of_self_adjoint
-/
theorem isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n -> α) :
    (diagonal v).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

@[simp]
/--
theorem `isHermitian_zero` / 定理 `isHermitian_zero`

English:
theorem isHermitian_zero
  statement: (0 : Matrix n n α).IsHermitian
  proof: IsSelfAdjoint.zero _

@[simp]

中文:
定理 isHermitian_zero
  结论: (0 : 矩阵 n n α).IsHermitian
  证明: IsSelfAdjoint.zero _

@[simp]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.zero
-/
theorem isHermitian_zero : (0 : Matrix n n α).IsHermitian :=
  IsSelfAdjoint.zero _

@[simp]
/--
theorem `IsHermitian.add` / 定理 `IsHermitian.add`

English:
theorem IsHermitian.add
  given: {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian)
  proof: IsSelfAdjoint.add hA hB

中文:
定理 IsHermitian.add
  条件: {A B : 矩阵 n n α} (hA : A.IsHermitian) (hB : B.IsHermitian)
  证明: IsSelfAdjoint.add hA hB

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.add
-/
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  IsSelfAdjoint.add hA hB

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [StarAddMonoid α]

/--
theorem `isHermitian_add_transpose_self` / 定理 `isHermitian_add_transpose_self`

English:
theorem isHermitian_add_transpose_self
  given: (A : Matrix n n α)
  statement: (A + Aᴴ).IsHermitian
  proof: IsSelfAdjoint.add_star_self A

中文:
定理 isHermitian_add_transpose_self
  条件: (A : 矩阵 n n α)
  结论: (A + Aᴴ).IsHermitian
  证明: IsSelfAdjoint.add_star_self A

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.add_star_self, add_star_self
-/
theorem isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian :=
  IsSelfAdjoint.add_star_self A

/--
theorem `isHermitian_transpose_add_self` / 定理 `isHermitian_transpose_add_self`

English:
theorem isHermitian_transpose_add_self
  given: (A : Matrix n n α)
  statement: (Aᴴ + A).IsHermitian
  proof: IsSelfAdjoint.star_add_self A

中文:
定理 isHermitian_transpose_add_self
  条件: (A : 矩阵 n n α)
  结论: (Aᴴ + A).IsHermitian
  证明: IsSelfAdjoint.star_add_self A

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_add_self, star_add_self
-/
theorem isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian :=
  IsSelfAdjoint.star_add_self A

end AddCommMonoid

section AddGroup

variable [AddGroup α] [StarAddMonoid α]

@[simp]
/--
theorem `IsHermitian.neg` / 定理 `IsHermitian.neg`

English:
theorem IsHermitian.neg
  given: {A : Matrix n n α} (h : A.IsHermitian)
  statement: (-A).IsHermitian
  proof: IsSelfAdjoint.neg h

@[simp]

中文:
定理 IsHermitian.neg
  条件: {A : 矩阵 n n α} (h : A.IsHermitian)
  结论: (-A).IsHermitian
  证明: IsSelfAdjoint.neg h

@[simp]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.neg
-/
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  IsSelfAdjoint.neg h

@[simp]
/--
theorem `isHermitian_neg_iff` / 定理 `isHermitian_neg_iff`

English:
theorem isHermitian_neg_iff
  given: {A : Matrix n n α}
  statement: (-A).IsHermitian ↔ A.IsHermitian
  proof: by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]

中文:
定理 isHermitian_neg_iff
  条件: {A : 矩阵 n n α}
  结论: (-A).IsHermitian ↔ A.IsHermitian
  证明: by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]

Depends on / 依赖: h.neg, neg_neg
-/
theorem isHermitian_neg_iff {A : Matrix n n α} : (-A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]
/--
theorem `IsHermitian.sub` / 定理 `IsHermitian.sub`

English:
theorem IsHermitian.sub
  given: {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian)
  proof: IsSelfAdjoint.sub hA hB

中文:
定理 IsHermitian.sub
  条件: {A B : 矩阵 n n α} (hA : A.IsHermitian) (hB : B.IsHermitian)
  证明: IsSelfAdjoint.sub hA hB

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.sub
-/
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian :=
  IsSelfAdjoint.sub hA hB

end AddGroup

section StarModule

variable {R : Type*} [Star R] [Star α] [SMul R α] [StarModule R α]

/--
theorem `IsHermitian.smul` / 定理 `IsHermitian.smul`

English:
theorem IsHermitian.smul
  given: {A : Matrix n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k)
  proof: by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq]; rw [h.eq]

中文:
定理 IsHermitian.smul
  条件: {A : 矩阵 n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k)
  证明: by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq]; rw [h.eq]

Depends on / 依赖: IsHermitian, conjTranspose_smul, h.eq, hk.star_eq, star_eq
-/
theorem IsHermitian.smul {A : Matrix n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq]; rw [h.eq]

end StarModule

section MulAction_StarModule

variable {R : Type*} [Monoid R] [Star R] [Star α] [MulAction R α] [StarModule R α]

/--
theorem `IsHermitian.of_smul` / 定理 `IsHermitian.of_smul`

English:
theorem IsHermitian.of_smul
  statement: {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
  proof: by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq] at h
  simpa using! congr(⅟k • $h)

中文:
定理 IsHermitian.of_smul
  结论: {A : 矩阵 n n α} {k : R} [可逆 k] (h : (k • A).IsHermitian)
  证明: by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq] at h
  simpa using! congr(⅟k • $h)

Depends on / 依赖: IsHermitian, conjTranspose_smul, hk.star_eq, star_eq
-/
theorem IsHermitian.of_smul {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint k) : A.IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose_smul]; rw [hk.star_eq] at h
  simpa using! congr(⅟k • $h)

/--
theorem `IsHermitian.of_smul'` / 定理 `IsHermitian.of_smul'`

English:
theorem IsHermitian.of_smul'
  statement: {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
  proof: by
  rw [← invOf_smul_smul k A]
  exact h.smul hk

@[simp]

中文:
定理 IsHermitian.of_smul'
  结论: {A : 矩阵 n n α} {k : R} [可逆 k] (h : (k • A).IsHermitian)
  证明: by
  rw [← invOf_smul_smul k A]
  exact h.smul hk

@[simp]

Depends on / 依赖: h.smul, invOf_smul_smul
-/
theorem IsHermitian.of_smul' {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint ⅟k) : A.IsHermitian := by
  rw [← invOf_smul_smul k A]
  exact h.smul hk

@[simp]
/--
theorem `isHermitian_smul_iff` / 定理 `isHermitian_smul_iff`

English:
theorem isHermitian_smul_iff
  given: {A : Matrix n n α} {k : R} [Invertible k] (hk : IsSelfAdjoint k)
  proof: ⟨(·.of_smul hk), (·.smul hk)⟩

中文:
定理 isHermitian_smul_iff
  条件: {A : 矩阵 n n α} {k : R} [可逆 k] (hk : IsSelfAdjoint k)
  证明: ⟨(·.of_smul hk), (·.smul hk)⟩

Depends on / 依赖: of_smul
-/
theorem isHermitian_smul_iff {A : Matrix n n α} {k : R} [Invertible k] (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian ↔ A.IsHermitian :=
  ⟨(·.of_smul hk), (·.smul hk)⟩

end MulAction_StarModule

section NonUnitalSemiring

variable [NonUnitalSemiring α] [StarRing α]

/--
theorem `isHermitian_mul_conjTranspose_self` / 定理 `isHermitian_mul_conjTranspose_self`

English:
theorem isHermitian_mul_conjTranspose_self
  given: [Fintype n] (A : Matrix m n α)
  proof: by rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

中文:
定理 isHermitian_mul_conjTranspose_self
  条件: [有限类型 n] (A : 矩阵 m n α)
  证明: by rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

Depends on / 依赖: IsHermitian, conjTranspose_conjTranspose, conjTranspose_mul
-/
theorem isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) :
    (A * Aᴴ).IsHermitian := by rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/--
theorem `isHermitian_conjTranspose_mul_self` / 定理 `isHermitian_conjTranspose_mul_self`

English:
theorem isHermitian_conjTranspose_mul_self
  given: [Fintype m] (A : Matrix m n α)
  proof: by
  rw [IsHermitian]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]

中文:
定理 isHermitian_conjTranspose_mul_self
  条件: [有限类型 m] (A : 矩阵 m n α)
  证明: by
  rw [IsHermitian]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]

Depends on / 依赖: IsHermitian, conjTranspose_conjTranspose, conjTranspose_mul
-/
theorem isHermitian_conjTranspose_mul_self [Fintype m] (A : Matrix m n α) :
    (Aᴴ * A).IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]

/--
theorem `isHermitian_conjTranspose_mul_mul` / 定理 `isHermitian_conjTranspose_mul_mul`

English:
theorem isHermitian_conjTranspose_mul_mul
  statement: [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
  proof: by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

中文:
定理 isHermitian_conjTranspose_mul_mul
  结论: [有限类型 m] {A : 矩阵 m m α} (B : 矩阵 m n α)
  证明: by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

Depends on / 依赖: IsHermitian, Matrix, Matrix.mul_assoc, conjTranspose_conjTranspose, conjTranspose_mul, hA.eq, mul_assoc
-/
theorem isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ * A * B).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/--
theorem `isHermitian_mul_mul_conjTranspose` / 定理 `isHermitian_mul_mul_conjTranspose`

English:
theorem isHermitian_mul_mul_conjTranspose
  statement: [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
  proof: by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

中文:
定理 isHermitian_mul_mul_conjTranspose
  结论: [有限类型 m] {A : 矩阵 m m α} (B : 矩阵 n m α)
  证明: by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

Depends on / 依赖: IsHermitian, Matrix, Matrix.mul_assoc, conjTranspose_conjTranspose, conjTranspose_mul, hA.eq, mul_assoc
-/
theorem isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B * A * Bᴴ).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/--
lemma `IsHermitian.commute_iff` / 引理 `IsHermitian.commute_iff`

English:
lemma IsHermitian.commute_iff
  statement: [Fintype n] {A B : Matrix n n α}
  proof: hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

中文:
引理 IsHermitian.commute_iff
  结论: [有限类型 n] {A B : 矩阵 n n α}
  证明: hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

Depends on / 依赖: commute_iff, hA.isSelfAdjoint.commute_iff, hB.isSelfAdjoint, isSelfAdjoint
-/
lemma IsHermitian.commute_iff [Fintype n] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Commute A B ↔ (A * B).IsHermitian :=
  hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α] [StarRing α]

/-- Note this is more general for matrices than `isSelfAdjoint_one` as it does not
require `Fintype n`, which is necessary for `Monoid (Matrix n n R)`. -/
@[simp]
/--
theorem `isHermitian_one` / 定理 `isHermitian_one`

English:
theorem isHermitian_one
  given: [DecidableEq n]
  statement: (1 : Matrix n n α).IsHermitian
  proof: conjTranspose_one

中文:
定理 isHermitian_one
  条件: [DecidableEq n]
  结论: (1 : 矩阵 n n α).IsHermitian
  证明: conjTranspose_one

Depends on / 依赖: conjTranspose_one
-/
theorem isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conjTranspose_one

end NonAssocSemiring

section Semiring

variable [Semiring α] [StarRing α]

@[simp]
/--
theorem `isHermitian_natCast` / 定理 `isHermitian_natCast`

English:
theorem isHermitian_natCast
  given: [DecidableEq n] (d : Nat)
  statement: (d : Matrix n n α).IsHermitian
  proof: conjTranspose_natCast _

中文:
定理 isHermitian_natCast
  条件: [DecidableEq n] (d : 自然数)
  结论: (d : 矩阵 n n α).IsHermitian
  证明: conjTranspose_natCast _

Depends on / 依赖: conjTranspose_natCast
-/
theorem isHermitian_natCast [DecidableEq n] (d : Nat) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_natCast _

/--
theorem `IsHermitian.pow` / 定理 `IsHermitian.pow`

English:
theorem IsHermitian.pow
  given: [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : Nat)
  proof: IsSelfAdjoint.pow h _

中文:
定理 IsHermitian.pow
  条件: [有限类型 n] [DecidableEq n] {A : 矩阵 n n α} (h : A.IsHermitian) (k : 自然数)
  证明: IsSelfAdjoint.pow h _

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.pow
-/
theorem IsHermitian.pow [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : Nat) :
    (A ^ k).IsHermitian := IsSelfAdjoint.pow h _

end Semiring

section Ring
variable [Ring α] [StarRing α]

@[simp]
/--
theorem `isHermitian_intCast` / 定理 `isHermitian_intCast`

English:
theorem isHermitian_intCast
  given: [DecidableEq n] (d : Int)
  statement: (d : Matrix n n α).IsHermitian
  proof: conjTranspose_intCast _

中文:
定理 isHermitian_intCast
  条件: [DecidableEq n] (d : 整数)
  结论: (d : 矩阵 n n α).IsHermitian
  证明: conjTranspose_intCast _

Depends on / 依赖: conjTranspose_intCast
-/
theorem isHermitian_intCast [DecidableEq n] (d : Int) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_intCast _

end Ring

section CommRing

variable [CommRing α] [StarRing α]

/--
theorem `IsHermitian.inv` / 定理 `IsHermitian.inv`

English:
theorem IsHermitian.inv
  given: [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian)
  proof: by simp [IsHermitian, conjTranspose_nonsing_inv, hA.eq]

@[simp]

中文:
定理 IsHermitian.inv
  条件: [有限类型 m] [DecidableEq m] {A : 矩阵 m m α} (hA : A.IsHermitian)
  证明: by simp [IsHermitian, conjTranspose_nonsing_inv, hA.eq]

@[simp]

Depends on / 依赖: IsHermitian, conjTranspose_nonsing_inv, hA.eq
-/
theorem IsHermitian.inv [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A⁻¹.IsHermitian := by simp [IsHermitian, conjTranspose_nonsing_inv, hA.eq]

@[simp]
/--
theorem `isHermitian_inv` / 定理 `isHermitian_inv`

English:
theorem isHermitian_inv
  given: [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A]
  proof: ⟨fun h => by rw [← inv_inv_of_invertible A]; exact IsHermitian.inv h, IsHermitian.inv⟩

中文:
定理 isHermitian_inv
  条件: [有限类型 m] [DecidableEq m] (A : 矩阵 m m α) [可逆 A]
  证明: ⟨fun h => by rw [← inv_inv_of_invertible A]; exact IsHermitian.inv h, IsHermitian.inv⟩

Depends on / 依赖: IsHermitian, IsHermitian.inv, inv_inv_of_invertible
-/
theorem isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by rw [← inv_inv_of_invertible A]; exact IsHermitian.inv h, IsHermitian.inv⟩

/--
theorem `IsHermitian.adjugate` / 定理 `IsHermitian.adjugate`

English:
theorem IsHermitian.adjugate
  given: [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian)
  proof: by simp [IsHermitian, adjugate_conjTranspose, hA.eq]

中文:
定理 IsHermitian.adjugate
  条件: [有限类型 m] [DecidableEq m] {A : 矩阵 m m α} (hA : A.IsHermitian)
  证明: by simp [IsHermitian, adjugate_conjTranspose, hA.eq]

Depends on / 依赖: IsHermitian, adjugate_conjTranspose, hA.eq
-/
theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [IsHermitian, adjugate_conjTranspose, hA.eq]

/--
theorem `IsHermitian.zpow` / 定理 `IsHermitian.zpow`

English:
theorem IsHermitian.zpow
  statement: [Fintype m] [DecidableEq m] {A : Matrix m m α} (h : A.IsHermitian)
  proof: by
  rw [IsHermitian]; rw [conjTranspose_zpow]; rw [h]

中文:
定理 IsHermitian.zpow
  结论: [有限类型 m] [DecidableEq m] {A : 矩阵 m m α} (h : A.IsHermitian)
  证明: by
  rw [IsHermitian]; rw [conjTranspose_zpow]; rw [h]

Depends on / 依赖: IsHermitian, conjTranspose_zpow
-/
theorem IsHermitian.zpow [Fintype m] [DecidableEq m] {A : Matrix m m α} (h : A.IsHermitian)
    (k : Int) :
    (A ^ k).IsHermitian := by
  rw [IsHermitian]; rw [conjTranspose_zpow]; rw [h]

section SchurComplement

/-- Notation for `Sum.elim`, scoped within the `Matrix` namespace. -/
scoped infixl:65 " oplusᵥ " => Sum.elim

/--
theorem `schur_complement_eq₁₁` / 定理 `schur_complement_eq₁₁`

English:
theorem schur_complement_eq₁₁
  statement: [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m α}
  proof: by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

中文:
定理 schur_complement_eq₁₁
  结论: [有限类型 m] [DecidableEq m] [有限类型 n] {A : 矩阵 m m α}
  证明: by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

Depends on / 依赖: Function, Function.star_sumElim, Matrix, Matrix.mul_assoc, add_vecMul, conjTranspose_nonsing_inv, dotProduct_mulVec, hA.eq, mul_assoc, star_mulVec, star_sumElim, vecMul_fromBlocks, vecMul_sub
-/
theorem schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m α}
    (B : Matrix m n α) (D : Matrix n n α) (x : m -> α) (y : n -> α) [Invertible A]
    (hA : A.IsHermitian) :
    (star (x oplusᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x oplusᵥ y) =
      (star (x + (A⁻¹ * B) *ᵥ y)) ᵥ* A ⬝ᵥ (x + (A⁻¹ * B) *ᵥ y) +
        (star y) ᵥ* (D - Bᴴ * A⁻¹ * B) ⬝ᵥ y := by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

/--
theorem `schur_complement_eq₂₂` / 定理 `schur_complement_eq₂₂`

English:
theorem schur_complement_eq₂₂
  statement: [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m α)
  proof: by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

中文:
定理 schur_complement_eq₂₂
  结论: [有限类型 m] [有限类型 n] [DecidableEq n] (A : 矩阵 m m α)
  证明: by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

Depends on / 依赖: Function, Function.star_sumElim, Matrix, Matrix.mul_assoc, add_vecMul, conjTranspose_nonsing_inv, dotProduct_mulVec, hD.eq, mul_assoc, star_mulVec, star_sumElim, vecMul_fromBlocks, vecMul_sub
-/
theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m α)
    (B : Matrix m n α) {D : Matrix n n α} (x : m -> α) (y : n -> α) [Invertible D]
    (hD : D.IsHermitian) :
    (star (x oplusᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x oplusᵥ y) =
      (star ((D⁻¹ * Bᴴ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ x + y) +
        (star x) ᵥ* (A - B * D⁻¹ * Bᴴ) ⬝ᵥ x := by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

namespace IsHermitian

/--
theorem `fromBlocks₁₁` / 定理 `fromBlocks₁₁`

English:
theorem fromBlocks₁₁
  statement: [Fintype m] [DecidableEq m] {A : Matrix m m α} (B : Matrix m n α)
  proof: by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := isHermitian_conjTranspose_mul_mul _ hA.inv
  rw [isHermitian_fromBlocks_iff]
  exact ⟨fun h => h.2.2.2.sub hBAB, fun h => ⟨hA, rfl, conjTranspose_conjTranspose B,
    sub_add_cancel D _ ▸ h.add hBAB⟩⟩

中文:
定理 fromBlocks₁₁
  结论: [有限类型 m] [DecidableEq m] {A : 矩阵 m m α} (B : 矩阵 m n α)
  证明: by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := isHermitian_conjTranspose_mul_mul _ hA.inv
  rw [isHermitian_fromBlocks_iff]
  exact ⟨fun h => h.2.2.2.sub hBAB, fun h => ⟨hA, rfl, conjTranspose_conjTranspose B,
    sub_add_cancel D _ ▸ h.add hBAB⟩⟩

Depends on / 依赖: IsHermitian, conjTranspose_conjTranspose, h.add, hA.inv, isHermitian_conjTranspose_mul_mul, isHermitian_fromBlocks_iff, sub_add_cancel
-/
theorem fromBlocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m α} (B : Matrix m n α)
    (D : Matrix n n α) (hA : A.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ * A⁻¹ * B).IsHermitian := by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := isHermitian_conjTranspose_mul_mul _ hA.inv
  rw [isHermitian_fromBlocks_iff]
  exact ⟨fun h => h.2.2.2.sub hBAB, fun h => ⟨hA, rfl, conjTranspose_conjTranspose B,
    sub_add_cancel D _ ▸ h.add hBAB⟩⟩

/--
theorem `fromBlocks₂₂` / 定理 `fromBlocks₂₂`

English:
theorem fromBlocks₂₂
  statement: [Fintype n] [DecidableEq n] (A : Matrix m m α) (B : Matrix m n α)
  proof: by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! IsHermitian.fromBlocks₁₁ _ _ hD <;> simp

中文:
定理 fromBlocks₂₂
  结论: [有限类型 n] [DecidableEq n] (A : 矩阵 m m α) (B : 矩阵 m n α)
  证明: by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! IsHermitian.fromBlocks₁₁ _ _ hD <;> simp

Depends on / 依赖: Equiv.sumComm, Equiv.sumComm_apply, IsHermitian, IsHermitian.fromBlocks, convert, fromBlocks_submatrix_sum_swap_sum_swap, isHermitian_submatrix_equiv, sumComm, sumComm_apply
-/
theorem fromBlocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m α) (B : Matrix m n α)
    {D : Matrix n n α} (hD : D.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B * D⁻¹ * Bᴴ).IsHermitian := by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! IsHermitian.fromBlocks₁₁ _ _ hD <;> simp

end IsHermitian

end SchurComplement

end CommRing
end Matrix
