/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Block Matrices

## Main definitions

* `Matrix.fromBlocks`: build a block matrix out of 4 blocks
* `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁`, `Matrix.toBlocks₂₂`:
  extract each of the four blocks from `Matrix.fromBlocks`.
* `Matrix.blockDiagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonalRingHom`.
* `Matrix.blockDiag`: extract the blocks from the diagonal of a block diagonal matrix.
* `Matrix.blockDiagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonal'RingHom`.
* `Matrix.blockDiag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/

@[expose] public section

variable {l m n o p q : Type*} {m' n' p' : o -> Type*}
variable {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open Matrix

namespace Matrix

/--
theorem `dotProduct_block` / 定理 `dotProduct_block`

English:
theorem dotProduct_block
  given: [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : m oplus n -> α)
  proof: Fintype.sum_sum_type _

中文:
定理 dotProduct_block
  条件: [有限类型 m] [有限类型 n] [乘法 α] [加法交换幺半群 α] (v w : m oplus n -> α)
  证明: Fintype.sum_sum_type _

Depends on / 依赖: Fintype, Fintype.sum_sum_type, sum_sum_type
-/
theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : m oplus n -> α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
/--
Definition of `fromBlocks` / `fromBlocks` 的定义

English:
definition fromBlocks
  signature: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
  body: of Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]

中文:
定义 fromBlocks
  签名: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α) (D : 矩阵 o m α)
  定义体: of Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]

Depends on / 依赖: Sum.elim
-/
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (n oplus o) (l oplus m) α :=
of Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]
/--
theorem `fromBlocks_apply₁₁` / 定理 `fromBlocks_apply₁₁`

English:
theorem fromBlocks_apply₁₁
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 fromBlocks_apply₁₁
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]
-/
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
/--
theorem `fromBlocks_apply₁₂` / 定理 `fromBlocks_apply₁₂`

English:
theorem fromBlocks_apply₁₂
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 fromBlocks_apply₁₂
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]
-/
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
/--
theorem `fromBlocks_apply₂₁` / 定理 `fromBlocks_apply₂₁`

English:
theorem fromBlocks_apply₂₁
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 fromBlocks_apply₂₁
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]
-/
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
/--
theorem `fromBlocks_apply₂₂` / 定理 `fromBlocks_apply₂₂`

English:
theorem fromBlocks_apply₂₂
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

中文:
定理 fromBlocks_apply₂₂
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl
-/
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl

/--
Definition of `toBlocks₁₁` / `toBlocks₁₁` 的定义

English:
definition toBlocks₁₁
  signature: (M : Matrix (n oplus o) (l oplus m) α)
  body: of fun i j => M (Sum.inl i) (Sum.inl j)

中文:
定义 toBlocks₁₁
  签名: (M : 矩阵 (n oplus o) (l oplus m) α)
  定义体: of fun i j => M (Sum.inl i) (Sum.inl j)

Depends on / 依赖: Sum.inl
-/
def toBlocks₁₁ (M : Matrix (n oplus o) (l oplus m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)

/--
Definition of `toBlocks₁₂` / `toBlocks₁₂` 的定义

English:
definition toBlocks₁₂
  signature: (M : Matrix (n oplus o) (l oplus m) α)
  body: of fun i j => M (Sum.inl i) (Sum.inr j)

中文:
定义 toBlocks₁₂
  签名: (M : 矩阵 (n oplus o) (l oplus m) α)
  定义体: of fun i j => M (Sum.inl i) (Sum.inr j)

Depends on / 依赖: Sum.inl, Sum.inr
-/
def toBlocks₁₂ (M : Matrix (n oplus o) (l oplus m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)

/--
Definition of `toBlocks₂₁` / `toBlocks₂₁` 的定义

English:
definition toBlocks₂₁
  signature: (M : Matrix (n oplus o) (l oplus m) α)
  body: of fun i j => M (Sum.inr i) (Sum.inl j)

中文:
定义 toBlocks₂₁
  签名: (M : 矩阵 (n oplus o) (l oplus m) α)
  定义体: of fun i j => M (Sum.inr i) (Sum.inl j)

Depends on / 依赖: Sum.inl, Sum.inr
-/
def toBlocks₂₁ (M : Matrix (n oplus o) (l oplus m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)

/--
Definition of `toBlocks₂₂` / `toBlocks₂₂` 的定义

English:
definition toBlocks₂₂
  signature: (M : Matrix (n oplus o) (l oplus m) α)
  body: of fun i j => M (Sum.inr i) (Sum.inr j)

中文:
定义 toBlocks₂₂
  签名: (M : 矩阵 (n oplus o) (l oplus m) α)
  定义体: of fun i j => M (Sum.inr i) (Sum.inr j)

Depends on / 依赖: Sum.inr
-/
def toBlocks₂₂ (M : Matrix (n oplus o) (l oplus m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)

/--
theorem `fromBlocks_toBlocks` / 定理 `fromBlocks_toBlocks`

English:
theorem fromBlocks_toBlocks
  given: (M : Matrix (n oplus o) (l oplus m) α)
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]

中文:
定理 fromBlocks_toBlocks
  条件: (M : 矩阵 (n oplus o) (l oplus m) α)
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
-/
theorem fromBlocks_toBlocks (M : Matrix (n oplus o) (l oplus m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
/--
theorem `toBlocks_fromBlocks₁₁` / 定理 `toBlocks_fromBlocks₁₁`

English:
theorem toBlocks_fromBlocks₁₁
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 toBlocks_fromBlocks₁₁
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]

Depends on / 依赖: Fintype, SetLike
-/
theorem toBlocks_fromBlocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl

@[simp]
/--
theorem `toBlocks_fromBlocks₁₂` / 定理 `toBlocks_fromBlocks₁₂`

English:
theorem toBlocks_fromBlocks₁₂
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 toBlocks_fromBlocks₁₂
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]

Depends on / 依赖: Finite, SetLike
-/
theorem toBlocks_fromBlocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl

@[simp]
/--
theorem `toBlocks_fromBlocks₂₁` / 定理 `toBlocks_fromBlocks₂₁`

English:
theorem toBlocks_fromBlocks₂₁
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

@[simp]

中文:
定理 toBlocks_fromBlocks₂₁
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl

@[simp]
-/
theorem toBlocks_fromBlocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl

@[simp]
/--
theorem `toBlocks_fromBlocks₂₂` / 定理 `toBlocks_fromBlocks₂₂`

English:
theorem toBlocks_fromBlocks₂₂
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: rfl

中文:
定理 toBlocks_fromBlocks₂₂
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: rfl
-/
theorem toBlocks_fromBlocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl

/--
theorem `ext_iff_blocks` / 定理 `ext_iff_blocks`

English:
theorem ext_iff_blocks
  given: {A B : Matrix (n oplus o) (l oplus m) α}
  proof: ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A]; rw [← fromBlocks_toBlocks B]; rw [h₁₁]; rw [h₁₂]; rw [h₂₁]; rw [h₂₂]⟩

@[simp]

中文:
定理 ext_iff_blocks
  条件: {A B : 矩阵 (n oplus o) (l oplus m) α}
  证明: ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A]; rw [← fromBlocks_toBlocks B]; rw [h₁₁]; rw [h₁₂]; rw [h₂₁]; rw [h₂₂]⟩

@[simp]

Depends on / 依赖: fromBlocks_toBlocks
-/
theorem ext_iff_blocks {A B : Matrix (n oplus o) (l oplus m) α} :
    A = B ↔
      A.toBlocks₁₁ = B.toBlocks₁₁ ∧
        A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ ∧ A.toBlocks₂₂ = B.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A]; rw [← fromBlocks_toBlocks B]; rw [h₁₁]; rw [h₁₂]; rw [h₂₁]; rw [h₂₂]⟩

@[simp]
/--
theorem `fromBlocks_inj` / 定理 `fromBlocks_inj`

English:
theorem fromBlocks_inj
  statement: {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
  proof: ext_iff_blocks

中文:
定理 fromBlocks_inj
  结论: {A : 矩阵 n l α} {B : 矩阵 n m α} {C : 矩阵 o l α} {D : 矩阵 o m α}
  证明: ext_iff_blocks

Depends on / 依赖: ext_iff_blocks
-/
theorem fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
    {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D' : Matrix o m α} :
    fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
  ext_iff_blocks

/--
theorem `fromBlocks_map` / 定理 `fromBlocks_map`

English:
theorem fromBlocks_map
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
  proof: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

中文:
定理 fromBlocks_map
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α) (D : 矩阵 o m α)
  证明: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

Depends on / 依赖: fromBlocks
-/
theorem fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α -> β) : (fromBlocks A B C D).map f =
      fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

/--
theorem `fromBlocks_transpose` / 定理 `fromBlocks_transpose`

English:
theorem fromBlocks_transpose
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

中文:
定理 fromBlocks_transpose
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

Depends on / 依赖: fromBlocks
-/
theorem fromBlocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

/--
theorem `fromBlocks_conjTranspose` / 定理 `fromBlocks_conjTranspose`

English:
theorem fromBlocks_conjTranspose
  statement: [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]

@[simp]

中文:
定理 fromBlocks_conjTranspose
  结论: [对合 α] (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]

@[simp]

Depends on / 依赖: conjTranspose, fromBlocks_map, fromBlocks_transpose
-/
theorem fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]

@[simp]
/--
theorem `fromBlocks_submatrix_sum_swap_left` / 定理 `fromBlocks_submatrix_sum_swap_left`

English:
theorem fromBlocks_submatrix_sum_swap_left
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  ext i j
  cases i <;> dsimp <;> cases f j <;> rfl

@[simp]

中文:
定理 fromBlocks_submatrix_sum_swap_left
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  ext i j
  cases i <;> dsimp <;> cases f j <;> rfl

@[simp]
-/
theorem fromBlocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p -> l oplus m) :
    (fromBlocks A B C D).submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f := by
  ext i j
  cases i <;> dsimp <;> cases f j <;> rfl

@[simp]
/--
theorem `fromBlocks_submatrix_sum_swap_right` / 定理 `fromBlocks_submatrix_sum_swap_right`

English:
theorem fromBlocks_submatrix_sum_swap_right
  statement: (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  ext i j
  cases j <;> dsimp <;> cases f i <;> rfl

中文:
定理 fromBlocks_submatrix_sum_swap_right
  结论: (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  ext i j
  cases j <;> dsimp <;> cases f i <;> rfl
-/
theorem fromBlocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p -> n oplus o) :
    (fromBlocks A B C D).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id := by
  ext i j
  cases j <;> dsimp <;> cases f i <;> rfl

/--
theorem `fromBlocks_submatrix_sum_swap_sum_swap` / 定理 `fromBlocks_submatrix_sum_swap_sum_swap`

English:
theorem fromBlocks_submatrix_sum_swap_sum_swap
  statement: {l m n o α : Type*} (A : Matrix n l α)
  proof: by simp

中文:
定理 fromBlocks_submatrix_sum_swap_sum_swap
  结论: {l m n o α : 类型} (A : 矩阵 n l α)
  证明: by simp
-/
theorem fromBlocks_submatrix_sum_swap_sum_swap {l m n o α : Type*} (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).submatrix Sum.swap Sum.swap = fromBlocks D C B A := by simp

/--
Definition of `IsTwoBlockDiagonal` / `IsTwoBlockDiagonal` 的定义

English:
definition IsTwoBlockDiagonal
  signature: [Zero α] (A : Matrix (n oplus o) (l oplus m) α)
  body: toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0

中文:
定义 IsTwoBlockDiagonal
  签名: [零 α] (A : 矩阵 (n oplus o) (l oplus m) α)
  定义体: toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0
-/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (n oplus o) (l oplus m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0

/--
Definition of `toBlock` / `toBlock` 的定义

English:
definition toBlock
  signature: (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop)
  body: M.submatrix (↑) (↑)

@[simp]

中文:
定义 toBlock
  签名: (M : 矩阵 m n α) (p : m -> 命题) (q : n -> 命题)
  定义体: M.submatrix (↑) (↑)

@[simp]

Depends on / 依赖: M.submatrix, submatrix
-/
def toBlock (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop) : Matrix { a // p a } { a // q a } α :=
  M.submatrix (↑) (↑)

@[simp]
/--
theorem `toBlock_apply` / 定理 `toBlock_apply`

English:
theorem toBlock_apply
  statement: (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop) (i : { a // p a })
  proof: rfl

中文:
定理 toBlock_apply
  结论: (M : 矩阵 m n α) (p : m -> 命题) (q : n -> 命题) (i : { a // p a })
  证明: rfl
-/
theorem toBlock_apply (M : Matrix m n α) (p : m -> Prop) (q : n -> Prop) (i : { a // p a })
    (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j :=
  rfl

/--
Definition of `toSquareBlockProp` / `toSquareBlockProp` 的定义

English:
definition toSquareBlockProp
  signature: (M : Matrix m m α) (p : m -> Prop)
  body: toBlock M _ _

中文:
定义 toSquareBlockProp
  签名: (M : 矩阵 m m α) (p : m -> 命题)
  定义体: toBlock M _ _

Depends on / 依赖: toBlock
-/
def toSquareBlockProp (M : Matrix m m α) (p : m -> Prop) : Matrix { a // p a } { a // p a } α :=
  toBlock M _ _

/--
theorem `toSquareBlockProp_def` / 定理 `toSquareBlockProp_def`

English:
theorem toSquareBlockProp_def
  given: (M : Matrix m m α) (p : m -> Prop)
  proof: rfl

中文:
定理 toSquareBlockProp_def
  条件: (M : 矩阵 m m α) (p : m -> 命题)
  证明: rfl
-/
theorem toSquareBlockProp_def (M : Matrix m m α) (p : m -> Prop) :
    toSquareBlockProp M p = of (fun i j : { a // p a } => M ↑i ↑j) :=
  rfl

/--
Definition of `toSquareBlock` / `toSquareBlock` 的定义

English:
definition toSquareBlock
  signature: (M : Matrix m m α) (b : m -> β) (k : β)
  body: toSquareBlockProp M _

中文:
定义 toSquareBlock
  签名: (M : 矩阵 m m α) (b : m -> β) (k : β)
  定义体: toSquareBlockProp M _

Depends on / 依赖: toSquareBlockProp
-/
def toSquareBlock (M : Matrix m m α) (b : m -> β) (k : β) :
    Matrix { a // b a = k } { a // b a = k } α :=
  toSquareBlockProp M _

/--
theorem `toSquareBlock_def` / 定理 `toSquareBlock_def`

English:
theorem toSquareBlock_def
  given: (M : Matrix m m α) (b : m -> β) (k : β)
  proof: rfl

中文:
定理 toSquareBlock_def
  条件: (M : 矩阵 m m α) (b : m -> β) (k : β)
  证明: rfl
-/
theorem toSquareBlock_def (M : Matrix m m α) (b : m -> β) (k : β) :
    toSquareBlock M b k = of (fun i j : { a // b a = k } => M ↑i ↑j) :=
  rfl

/--
theorem `fromBlocks_smul` / 定理 `fromBlocks_smul`

English:
theorem fromBlocks_smul
  statement: [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

中文:
定理 fromBlocks_smul
  结论: [标量乘法 R α] (x : R) (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

Depends on / 依赖: fromBlocks
-/
theorem fromBlocks_smul [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]

/--
theorem `fromBlocks_neg` / 定理 `fromBlocks_neg`

English:
theorem fromBlocks_neg
  statement: [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
  proof: by
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

@[simp]

中文:
定理 fromBlocks_neg
  结论: [取负 R] (A : 矩阵 n l R) (B : 矩阵 n m R) (C : 矩阵 o l R)
  证明: by
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

@[simp]

Depends on / 依赖: fromBlocks
-/
theorem fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
    (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D) := by
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

@[simp]
/--
theorem `fromBlocks_zero` / 定理 `fromBlocks_zero`

English:
theorem fromBlocks_zero
  given: [Zero α]
  statement: fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o m α) = 0
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

中文:
定理 fromBlocks_zero
  条件: [零 α]
  结论: fromBlocks (0 : 矩阵 n l α) 0 0 (0 : 矩阵 o m α) = 0
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
-/
theorem fromBlocks_zero [Zero α] : fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o m α) = 0 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

/--
theorem `fromBlocks_add` / 定理 `fromBlocks_add`

English:
theorem fromBlocks_add
  statement: [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
  proof: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

中文:
定理 fromBlocks_add
  结论: [加法 α] (A : 矩阵 n l α) (B : 矩阵 n m α) (C : 矩阵 o l α)
  证明: by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
-/
theorem fromBlocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α)
    (D' : Matrix o m α) : fromBlocks A B C D + fromBlocks A' B' C' D' =
      fromBlocks (A + A') (B + B') (C + C') (D + D') := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

/--
theorem `fromBlocks_multiply` / 定理 `fromBlocks_multiply`

English:
theorem fromBlocks_multiply
  statement: [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]

中文:
定理 fromBlocks_multiply
  结论: [有限类型 l] [有限类型 m] [非幺非结合半环 α] (A : 矩阵 n l α)
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]

Depends on / 依赖: Fintype, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_apply, elim_inl, elim_inr, fromBlocks, mul_apply, of_apply, sum_sum_type
-/
theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α)
    (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D * fromBlocks A' B' C' D' =
      fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]

/--
theorem `fromBlocks_diagonal_pow` / 定理 `fromBlocks_diagonal_pow`

English:
theorem fromBlocks_diagonal_pow
  statement: [Semiring α] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  proof: by
  induction k with
  | zero => ext (i | i) (j | j) <;> simp [one_apply]
  | succ n ih =>
    simp [ih, pow_succ, fromBlocks_multiply]

中文:
定理 fromBlocks_diagonal_pow
  结论: [半环 α] [有限类型 n] [有限类型 m] [DecidableEq n] [DecidableEq m]
  证明: by
  induction k with
  | zero => ext (i | i) (j | j) <;> simp [one_apply]
  | succ n ih =>
    simp [ih, pow_succ, fromBlocks_multiply]

Depends on / 依赖: fromBlocks_multiply, one_apply, pow_succ
-/
theorem fromBlocks_diagonal_pow [Semiring α] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n α) (D : Matrix m m α) (k : Nat) :
    (fromBlocks A 0 0 D) ^ k = fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => ext (i | i) (j | j) <;> simp [one_apply]
  | succ n ih =>
    simp [ih, pow_succ, fromBlocks_multiply]

/--
theorem `fromBlocks_mulVec` / 定理 `fromBlocks_mulVec`

English:
theorem fromBlocks_mulVec
  statement: [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
  proof: by
  ext i
  cases i <;> simp [mulVec, dotProduct]

中文:
定理 fromBlocks_mulVec
  结论: [有限类型 l] [有限类型 m] [非幺非结合半环 α] (A : 矩阵 n l α)
  证明: by
  ext i
  cases i <;> simp [mulVec, dotProduct]

Depends on / 依赖: dotProduct, mulVec
-/
theorem fromBlocks_mulVec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : l oplus m -> α) :
    (fromBlocks A B C D) *ᵥ x =
      Sum.elim (A *ᵥ (x ∘ Sum.inl) + B *ᵥ (x ∘ Sum.inr))
        (C *ᵥ (x ∘ Sum.inl) + D *ᵥ (x ∘ Sum.inr)) := by
  ext i
  cases i <;> simp [mulVec, dotProduct]

/--
theorem `vecMul_fromBlocks` / 定理 `vecMul_fromBlocks`

English:
theorem vecMul_fromBlocks
  statement: [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
  proof: by
  ext i
  cases i <;> simp [vecMul, dotProduct]

中文:
定理 vecMul_fromBlocks
  结论: [有限类型 n] [有限类型 o] [非幺非结合半环 α] (A : 矩阵 n l α)
  证明: by
  ext i
  cases i <;> simp [vecMul, dotProduct]

Depends on / 依赖: dotProduct, vecMul
-/
theorem vecMul_fromBlocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : n oplus o -> α) :
    x ᵥ* fromBlocks A B C D =
      Sum.elim ((x ∘ Sum.inl) ᵥ* A + (x ∘ Sum.inr) ᵥ* C)
        ((x ∘ Sum.inl) ᵥ* B + (x ∘ Sum.inr) ᵥ* D) := by
  ext i
  cases i <;> simp [vecMul, dotProduct]

variable [DecidableEq l] [DecidableEq m]

section Zero

variable [Zero α]

/--
theorem `toBlock_diagonal_self` / 定理 `toBlock_diagonal_self`

English:
theorem toBlock_diagonal_self
  given: (d : m -> α) (p : m -> Prop)
  proof: by
  ext i j
  by_cases h : i = j
  · simp [h]
  · simp [h, Subtype.val_injective.ne h]

中文:
定理 toBlock_diagonal_self
  条件: (d : m -> α) (p : m -> 命题)
  证明: by
  ext i j
  by_cases h : i = j
  · simp [h]
  · simp [h, Subtype.val_injective.ne h]

Depends on / 依赖: Subtype, Subtype.val_injective.ne, val_injective
-/
theorem toBlock_diagonal_self (d : m -> α) (p : m -> Prop) :
    Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i := by
  ext i j
  by_cases h : i = j
  · simp [h]
  · simp [h, Subtype.val_injective.ne h]

/--
theorem `toBlock_diagonal_disjoint` / 定理 `toBlock_diagonal_disjoint`

English:
theorem toBlock_diagonal_disjoint
  given: (d : m -> α) {p q : m -> Prop} (hpq : Disjoint p q)
  proof: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  have : i != j := fun heq => hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]

@[simp]

中文:
定理 toBlock_diagonal_disjoint
  条件: (d : m -> α) {p q : m -> 命题} (hpq : Disjoint p q)
  证明: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  have : i != j := fun heq => hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]

@[simp]

Depends on / 依赖: diagonal_apply_ne, heq.symm, hpq.le_bot, le_bot
-/
theorem toBlock_diagonal_disjoint (d : m -> α) {p q : m -> Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (diagonal d) p q = 0 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  have : i != j := fun heq => hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]

@[simp]
/--
theorem `fromBlocks_diagonal` / 定理 `fromBlocks_diagonal`

English:
theorem fromBlocks_diagonal
  given: (d₁ : l -> α) (d₂ : m -> α)
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]

@[simp]

中文:
定理 fromBlocks_diagonal
  条件: (d₁ : l -> α) (d₂ : m -> α)
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]

@[simp]

Depends on / 依赖: diagonal
-/
theorem fromBlocks_diagonal (d₁ : l -> α) (d₂ : m -> α) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]

@[simp]
/--
lemma `toBlocks₁₁_diagonal` / 引理 `toBlocks₁₁_diagonal`

English:
lemma toBlocks₁₁_diagonal
  given: (v : l oplus m -> α)
  proof: by
  unfold toBlocks₁₁
  funext i j
  simp only [Sum.inl.injEq, of_apply, diagonal_apply]

@[simp]

中文:
引理 toBlocks₁₁_diagonal
  条件: (v : l oplus m -> α)
  证明: by
  unfold toBlocks₁₁
  funext i j
  simp only [Sum.inl.injEq, of_apply, diagonal_apply]

@[simp]

Depends on / 依赖: Sum.inl.injEq, diagonal_apply, of_apply
-/
lemma toBlocks₁₁_diagonal (v : l oplus m -> α) :
    toBlocks₁₁ (diagonal v) = diagonal (fun i => v (Sum.inl i)) := by
  unfold toBlocks₁₁
  funext i j
  simp only [Sum.inl.injEq, of_apply, diagonal_apply]

@[simp]
/--
lemma `toBlocks₂₂_diagonal` / 引理 `toBlocks₂₂_diagonal`

English:
lemma toBlocks₂₂_diagonal
  given: (v : l oplus m -> α)
  proof: by
  unfold toBlocks₂₂
  funext i j
  simp only [Sum.inr.injEq, of_apply, diagonal_apply]

@[simp]

中文:
引理 toBlocks₂₂_diagonal
  条件: (v : l oplus m -> α)
  证明: by
  unfold toBlocks₂₂
  funext i j
  simp only [Sum.inr.injEq, of_apply, diagonal_apply]

@[simp]

Depends on / 依赖: Sum.inr.injEq, diagonal_apply, of_apply
-/
lemma toBlocks₂₂_diagonal (v : l oplus m -> α) :
    toBlocks₂₂ (diagonal v) = diagonal (fun i => v (Sum.inr i)) := by
  unfold toBlocks₂₂
  funext i j
  simp only [Sum.inr.injEq, of_apply, diagonal_apply]

@[simp]
/--
lemma `toBlocks₁₂_diagonal` / 引理 `toBlocks₁₂_diagonal`

English:
lemma toBlocks₁₂_diagonal
  given: (v : l oplus m -> α)
  statement: toBlocks₁₂ (diagonal v) = 0
  proof: rfl

@[simp]

中文:
引理 toBlocks₁₂_diagonal
  条件: (v : l oplus m -> α)
  结论: toBlocks₁₂ (diagonal v) = 0
  证明: rfl

@[simp]
-/
lemma toBlocks₁₂_diagonal (v : l oplus m -> α) : toBlocks₁₂ (diagonal v) = 0 := rfl

@[simp]
/--
lemma `toBlocks₂₁_diagonal` / 引理 `toBlocks₂₁_diagonal`

English:
lemma toBlocks₂₁_diagonal
  given: (v : l oplus m -> α)
  statement: toBlocks₂₁ (diagonal v) = 0
  proof: rfl

中文:
引理 toBlocks₂₁_diagonal
  条件: (v : l oplus m -> α)
  结论: toBlocks₂₁ (diagonal v) = 0
  证明: rfl
-/
lemma toBlocks₂₁_diagonal (v : l oplus m -> α) : toBlocks₂₁ (diagonal v) = 0 := rfl

end Zero

section HasZeroHasOne

variable [Zero α] [One α]

@[simp]
/--
theorem `fromBlocks_one` / 定理 `fromBlocks_one`

English:
theorem fromBlocks_one
  statement: fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1
  proof: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]

@[simp]

中文:
定理 fromBlocks_one
  结论: fromBlocks (1 : 矩阵 l l α) 0 0 (1 : 矩阵 m m α) = 1
  证明: by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]

@[simp]

Depends on / 依赖: one_apply
-/
theorem fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]

@[simp]
/--
theorem `toBlock_one_self` / 定理 `toBlock_one_self`

English:
theorem toBlock_one_self
  given: (p : m -> Prop)
  statement: Matrix.toBlock (1 : Matrix m m α) p p = 1
  proof: toBlock_diagonal_self _ p

中文:
定理 toBlock_one_self
  条件: (p : m -> 命题)
  结论: 矩阵.toBlock (1 : 矩阵 m m α) p p = 1
  证明: toBlock_diagonal_self _ p

Depends on / 依赖: toBlock_diagonal_self
-/
theorem toBlock_one_self (p : m -> Prop) : Matrix.toBlock (1 : Matrix m m α) p p = 1 :=
  toBlock_diagonal_self _ p

/--
theorem `toBlock_one_disjoint` / 定理 `toBlock_one_disjoint`

English:
theorem toBlock_one_disjoint
  given: {p q : m -> Prop} (hpq : Disjoint p q)
  proof: toBlock_diagonal_disjoint _ hpq

中文:
定理 toBlock_one_disjoint
  条件: {p q : m -> 命题} (hpq : Disjoint p q)
  证明: toBlock_diagonal_disjoint _ hpq

Depends on / 依赖: toBlock_diagonal_disjoint
-/
theorem toBlock_one_disjoint {p q : m -> Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (1 : Matrix m m α) p q = 0 :=
  toBlock_diagonal_disjoint _ hpq

end HasZeroHasOne

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/--
Definition of `blockDiagonal` / `blockDiagonal` 的定义

English:
definition blockDiagonal
  signature: (M : o -> Matrix m n α)
  body: of (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o -> n × o -> α)

中文:
定义 blockDiagonal
  签名: (M : o -> 矩阵 m n α)
  定义体: of (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o -> n × o -> α)
-/
def blockDiagonal (M : o -> Matrix m n α) : Matrix (m × o) (n × o) α :=
of (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o -> n × o -> α)

-- TODO: set as an equation lemma for `blockDiagonal`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `blockDiagonal_apply'` / 定理 `blockDiagonal_apply'`

English:
theorem blockDiagonal_apply'
  given: (M : o -> Matrix m n α) (i k j k')
  proof: rfl

中文:
定理 blockDiagonal_apply'
  条件: (M : o -> 矩阵 m n α) (i k j k')
  证明: rfl
-/
theorem blockDiagonal_apply' (M : o -> Matrix m n α) (i k j k') :
    blockDiagonal M ⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0 :=
  rfl

/--
theorem `blockDiagonal_apply` / 定理 `blockDiagonal_apply`

English:
theorem blockDiagonal_apply
  given: (M : o -> Matrix m n α) (ik jk)
  proof: rfl

@[simp]

中文:
定理 blockDiagonal_apply
  条件: (M : o -> 矩阵 m n α) (ik jk)
  证明: rfl

@[simp]
-/
theorem blockDiagonal_apply (M : o -> Matrix m n α) (ik jk) :
    blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := rfl

@[simp]
/--
theorem `blockDiagonal_apply_eq` / 定理 `blockDiagonal_apply_eq`

English:
theorem blockDiagonal_apply_eq
  given: (M : o -> Matrix m n α) (i j k)
  proof: if_pos rfl

中文:
定理 blockDiagonal_apply_eq
  条件: (M : o -> 矩阵 m n α) (i j k)
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem blockDiagonal_apply_eq (M : o -> Matrix m n α) (i j k) :
    blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl

/--
theorem `blockDiagonal_apply_ne` / 定理 `blockDiagonal_apply_ne`

English:
theorem blockDiagonal_apply_ne
  given: (M : o -> Matrix m n α) (i j) {k k'} (h : k != k')
  proof: if_neg h

中文:
定理 blockDiagonal_apply_ne
  条件: (M : o -> 矩阵 m n α) (i j) {k k'} (h : k != k')
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem blockDiagonal_apply_ne (M : o -> Matrix m n α) (i j) {k k'} (h : k != k') :
    blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h

/--
theorem `blockDiagonal_map` / 定理 `blockDiagonal_map`

English:
theorem blockDiagonal_map
  given: (M : o -> Matrix m n α) (f : α -> β) (hf : f 0 = 0)
  proof: by
  ext
  simp only [map_apply, blockDiagonal_apply]
  rw [apply_ite f]; rw [hf]

@[simp]

中文:
定理 blockDiagonal_map
  条件: (M : o -> 矩阵 m n α) (f : α -> β) (hf : f 0 = 0)
  证明: by
  ext
  simp only [map_apply, blockDiagonal_apply]
  rw [apply_ite f]; rw [hf]

@[simp]

Depends on / 依赖: apply_ite, blockDiagonal_apply, map_apply
-/
theorem blockDiagonal_map (M : o -> Matrix m n α) (f : α -> β) (hf : f 0 = 0) :
    (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f := by
  ext
  simp only [map_apply, blockDiagonal_apply]
  rw [apply_ite f]; rw [hf]

@[simp]
/--
theorem `blockDiagonal_transpose` / 定理 `blockDiagonal_transpose`

English:
theorem blockDiagonal_transpose
  given: (M : o -> Matrix m n α)
  proof: by
  ext
  simp only [transpose_apply, blockDiagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl

@[simp]

中文:
定理 blockDiagonal_transpose
  条件: (M : o -> 矩阵 m n α)
  证明: by
  ext
  simp only [transpose_apply, blockDiagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl

@[simp]

Depends on / 依赖: blockDiagonal_apply, eq_comm, split_ifs, transpose_apply
-/
theorem blockDiagonal_transpose (M : o -> Matrix m n α) :
    (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ := by
  ext
  simp only [transpose_apply, blockDiagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl

@[simp]
/--
theorem `blockDiagonal_conjTranspose` / 定理 `blockDiagonal_conjTranspose`

English:
theorem blockDiagonal_conjTranspose
  statement: {α : Type*} [AddMonoid α] [StarAddMonoid α]
  proof: by
  simp only [conjTranspose, blockDiagonal_transpose]
  rw [blockDiagonal_map _ star (star_zero α)]

@[simp]

中文:
定理 blockDiagonal_conjTranspose
  结论: {α : 类型} [加法幺半群 α] [StarAdd幺半群 α]
  证明: by
  simp only [conjTranspose, blockDiagonal_transpose]
  rw [blockDiagonal_map _ star (star_zero α)]

@[simp]

Depends on / 依赖: blockDiagonal_map, blockDiagonal_transpose, conjTranspose, star_zero
-/
theorem blockDiagonal_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (M : o -> Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal_transpose]
  rw [blockDiagonal_map _ star (star_zero α)]

@[simp]
/--
theorem `blockDiagonal_zero` / 定理 `blockDiagonal_zero`

English:
theorem blockDiagonal_zero
  statement: blockDiagonal (0 : o -> Matrix m n α) = 0
  proof: by
  ext
  simp [blockDiagonal_apply]

@[simp]

中文:
定理 blockDiagonal_zero
  结论: blockDiagonal (0 : o -> 矩阵 m n α) = 0
  证明: by
  ext
  simp [blockDiagonal_apply]

@[simp]

Depends on / 依赖: blockDiagonal_apply
-/
theorem blockDiagonal_zero : blockDiagonal (0 : o -> Matrix m n α) = 0 := by
  ext
  simp [blockDiagonal_apply]

@[simp]
/--
theorem `blockDiagonal_diagonal` / 定理 `blockDiagonal_diagonal`

English:
theorem blockDiagonal_diagonal
  given: [DecidableEq m] (d : o -> m -> α)
  proof: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, diagonal_apply, Prod.mk_inj, ← ite_and]
  congr 1
  rw [and_comm]

@[simp]

中文:
定理 blockDiagonal_diagonal
  条件: [DecidableEq m] (d : o -> m -> α)
  证明: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, diagonal_apply, Prod.mk_inj, ← ite_and]
  congr 1
  rw [and_comm]

@[simp]

Depends on / 依赖: Prod.mk_inj, and_comm, blockDiagonal_apply, diagonal_apply, ite_and, mk_inj
-/
theorem blockDiagonal_diagonal [DecidableEq m] (d : o -> m -> α) :
    (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, diagonal_apply, Prod.mk_inj, ← ite_and]
  congr 1
  rw [and_comm]

@[simp]
/--
theorem `blockDiagonal_one` / 定理 `blockDiagonal_one`

English:
theorem blockDiagonal_one
  given: [DecidableEq m] [One α]
  statement: blockDiagonal (1 : o -> Matrix m m α) = 1
  proof: show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal_diagonal]

中文:
定理 blockDiagonal_one
  条件: [DecidableEq m] [幺 α]
  结论: blockDiagonal (1 : o -> 矩阵 m m α) = 1
  证明: show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal_diagonal]

Depends on / 依赖: blockDiagonal, blockDiagonal_diagonal, diagonal
-/
theorem blockDiagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o -> Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal_diagonal]

end Zero

@[simp]
/--
theorem `blockDiagonal_add` / 定理 `blockDiagonal_add`

English:
theorem blockDiagonal_add
  given: [AddZeroClass α] (M N : o -> Matrix m n α)
  proof: by
  ext
  simp only [blockDiagonal_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

中文:
定理 blockDiagonal_add
  条件: [加法零类 α] (M N : o -> 矩阵 m n α)
  证明: by
  ext
  simp only [blockDiagonal_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

Depends on / 依赖: Pi.add_apply, add_apply, blockDiagonal_apply, split_ifs
-/
theorem blockDiagonal_add [AddZeroClass α] (M N : o -> Matrix m n α) :
    blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N := by
  ext
  simp only [blockDiagonal_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

section

variable (o m n α)

/-- `Matrix.blockDiagonal` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `blockDiagonalAddMonoidHom` / `blockDiagonalAddMonoidHom` 的定义

English:
definition blockDiagonalAddMonoidHom
  signature: [AddZeroClass α]
  body: blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add

中文:
定义 blockDiagonalAddMonoidHom
  签名: [加法零类 α]
  定义体: blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add

Depends on / 依赖: blockDiagonal
-/
def blockDiagonalAddMonoidHom [AddZeroClass α] :
    (o -> Matrix m n α) ->+ Matrix (m × o) (n × o) α where
  toFun := blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add

end

@[simp]
/--
theorem `blockDiagonal_neg` / 定理 `blockDiagonal_neg`

English:
theorem blockDiagonal_neg
  given: [AddGroup α] (M : o -> Matrix m n α)
  proof: map_neg (blockDiagonalAddMonoidHom m n o α) M

@[simp]

中文:
定理 blockDiagonal_neg
  条件: [加法群 α] (M : o -> 矩阵 m n α)
  证明: map_neg (blockDiagonalAddMonoidHom m n o α) M

@[simp]

Depends on / 依赖: blockDiagonalAddMonoidHom, map_neg
-/
theorem blockDiagonal_neg [AddGroup α] (M : o -> Matrix m n α) :
    blockDiagonal (-M) = -blockDiagonal M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M

@[simp]
/--
theorem `blockDiagonal_sub` / 定理 `blockDiagonal_sub`

English:
theorem blockDiagonal_sub
  given: [AddGroup α] (M N : o -> Matrix m n α)
  proof: map_sub (blockDiagonalAddMonoidHom m n o α) M N

@[simp]

中文:
定理 blockDiagonal_sub
  条件: [加法群 α] (M N : o -> 矩阵 m n α)
  证明: map_sub (blockDiagonalAddMonoidHom m n o α) M N

@[simp]

Depends on / 依赖: blockDiagonalAddMonoidHom, map_sub
-/
theorem blockDiagonal_sub [AddGroup α] (M N : o -> Matrix m n α) :
    blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N

@[simp]
/--
theorem `blockDiagonal_mul` / 定理 `blockDiagonal_mul`

English:
theorem blockDiagonal_mul
  statement: [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
  proof: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]

中文:
定理 blockDiagonal_mul
  结论: [有限类型 n] [有限类型 o] [非幺非结合半环 α]
  证明: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]

Depends on / 依赖: Finset, Finset.sum_product, Finset.univ_product_univ, blockDiagonal_apply, mul_apply, split_ifs, sum_product, univ_product_univ
-/
theorem blockDiagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : o -> Matrix m n α) (N : o -> Matrix n p α) :
    (blockDiagonal fun k => M k * N k) = blockDiagonal M * blockDiagonal N := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]

section

variable (α m o)

/-- `Matrix.blockDiagonal` as a `RingHom`. -/
@[simps]
/--
Definition of `blockDiagonalRingHom` / `blockDiagonalRingHom` 的定义

English:
definition blockDiagonalRingHom
  signature: [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α]
  body: { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }

中文:
定义 blockDiagonalRingHom
  签名: [DecidableEq m] [有限类型 o] [有限类型 m] [非结合半环 α]
  定义体: { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }

Depends on / 依赖: blockDiagonal, blockDiagonalAddMonoidHom, blockDiagonal_mul, blockDiagonal_one, map_mul, map_one
-/
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α] :
    (o -> Matrix m m α) ->+* Matrix (m × o) (m × o) α :=
  { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }

end

@[simp]
/--
theorem `blockDiagonal_pow` / 定理 `blockDiagonal_pow`

English:
theorem blockDiagonal_pow
  statement: [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
  proof: map_pow (blockDiagonalRingHom m o α) M n

@[simp]

中文:
定理 blockDiagonal_pow
  结论: [DecidableEq m] [有限类型 o] [有限类型 m] [半环 α]
  证明: map_pow (blockDiagonalRingHom m o α) M n

@[simp]

Depends on / 依赖: blockDiagonalRingHom, map_pow
-/
theorem blockDiagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
    (M : o -> Matrix m m α) (n : Nat) : blockDiagonal (M ^ n) = blockDiagonal M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n

@[simp]
/--
theorem `blockDiagonal_smul` / 定理 `blockDiagonal_smul`

English:
theorem blockDiagonal_smul
  statement: {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
  proof: by
  ext
  simp only [blockDiagonal_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

中文:
定理 blockDiagonal_smul
  结论: {R : 类型} [零 α] [SMulZero类 R α] (x : R)
  证明: by
  ext
  simp only [blockDiagonal_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

Depends on / 依赖: Pi.smul_apply, blockDiagonal_apply, smul_apply, split_ifs
-/
theorem blockDiagonal_smul {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
    (M : o -> Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M := by
  ext
  simp only [blockDiagonal_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

end BlockDiagonal

section BlockDiag

/--
Definition of `blockDiag` / `blockDiag` 的定义

English:
definition blockDiag
  signature: (M : Matrix (m × o) (n × o) α) (k : o)
  body: of fun i j => M (i, k) (j, k)

中文:
定义 blockDiag
  签名: (M : 矩阵 (m × o) (n × o) α) (k : o)
  定义体: of fun i j => M (i, k) (j, k)
-/
def blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α :=
  of fun i j => M (i, k) (j, k)

-- TODO: set as an equation lemma for `blockDiag`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `blockDiag_apply` / 定理 `blockDiag_apply`

English:
theorem blockDiag_apply
  given: (M : Matrix (m × o) (n × o) α) (k : o) (i j)
  proof: rfl

中文:
定理 blockDiag_apply
  条件: (M : 矩阵 (m × o) (n × o) α) (k : o) (i j)
  证明: rfl
-/
theorem blockDiag_apply (M : Matrix (m × o) (n × o) α) (k : o) (i j) :
    blockDiag M k i j = M (i, k) (j, k) :=
  rfl

/--
theorem `blockDiag_map` / 定理 `blockDiag_map`

English:
theorem blockDiag_map
  given: (M : Matrix (m × o) (n × o) α) (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 blockDiag_map
  条件: (M : 矩阵 (m × o) (n × o) α) (f : α -> β)
  证明: rfl

@[simp]
-/
theorem blockDiag_map (M : Matrix (m × o) (n × o) α) (f : α -> β) :
    blockDiag (M.map f) = fun k => (blockDiag M k).map f :=
  rfl

@[simp]
/--
theorem `blockDiag_transpose` / 定理 `blockDiag_transpose`

English:
theorem blockDiag_transpose
  given: (M : Matrix (m × o) (n × o) α) (k : o)
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 blockDiag_transpose
  条件: (M : 矩阵 (m × o) (n × o) α) (k : o)
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem blockDiag_transpose (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiag Mᵀ k = (blockDiag M k)ᵀ :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `blockDiag_conjTranspose` / 定理 `blockDiag_conjTranspose`

English:
theorem blockDiag_conjTranspose
  statement: {α : Type*} [Star α]
  proof: ext fun _ _ => rfl

中文:
定理 blockDiag_conjTranspose
  结论: {α : 类型} [对合 α]
  证明: ext fun _ _ => rfl
-/
theorem blockDiag_conjTranspose {α : Type*} [Star α]
    (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ :=
  ext fun _ _ => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
/--
theorem `blockDiag_zero` / 定理 `blockDiag_zero`

English:
theorem blockDiag_zero
  statement: blockDiag (0 : Matrix (m × o) (n × o) α) = 0
  proof: rfl

@[simp]

中文:
定理 blockDiag_zero
  结论: blockDiag (0 : 矩阵 (m × o) (n × o) α) = 0
  证明: rfl

@[simp]
-/
theorem blockDiag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl

@[simp]
/--
theorem `blockDiag_diagonal` / 定理 `blockDiag_diagonal`

English:
theorem blockDiag_diagonal
  given: [DecidableEq o] [DecidableEq m] (d : m × o -> α) (k : o)
  proof: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact Prod.fst_eq_iff.mpr

@[simp]

中文:
定理 blockDiag_diagonal
  条件: [DecidableEq o] [DecidableEq m] (d : m × o -> α) (k : o)
  证明: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact Prod.fst_eq_iff.mpr

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Prod.fst_eq_iff.mpr, blockDiag_apply, diagonal_apply_eq, diagonal_apply_ne, eq_or_ne, fst_eq_iff
-/
theorem blockDiag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o -> α) (k : o) :
    blockDiag (diagonal d) k = diagonal fun i => d (i, k) :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact Prod.fst_eq_iff.mpr

@[simp]
/--
theorem `blockDiag_blockDiagonal` / 定理 `blockDiag_blockDiagonal`

English:
theorem blockDiag_blockDiagonal
  given: [DecidableEq o] (M : o -> Matrix m n α)
  proof: funext fun _ => ext fun i j => blockDiagonal_apply_eq M i j _

中文:
定理 blockDiag_blockDiagonal
  条件: [DecidableEq o] (M : o -> 矩阵 m n α)
  证明: funext fun _ => ext fun i j => blockDiagonal_apply_eq M i j _

Depends on / 依赖: blockDiagonal_apply_eq
-/
theorem blockDiag_blockDiagonal [DecidableEq o] (M : o -> Matrix m n α) :
    blockDiag (blockDiagonal M) = M :=
  funext fun _ => ext fun i j => blockDiagonal_apply_eq M i j _

/--
theorem `blockDiagonal_injective` / 定理 `blockDiagonal_injective`

English:
theorem blockDiagonal_injective
  given: [DecidableEq o]
  proof: Function.LeftInverse.injective blockDiag_blockDiagonal

@[simp]

中文:
定理 blockDiagonal_injective
  条件: [DecidableEq o]
  证明: Function.LeftInverse.injective blockDiag_blockDiagonal

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, blockDiag_blockDiagonal, injective
-/
theorem blockDiagonal_injective [DecidableEq o] :
    Function.Injective (blockDiagonal : (o -> Matrix m n α) -> Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag_blockDiagonal

@[simp]
/--
theorem `blockDiagonal_inj` / 定理 `blockDiagonal_inj`

English:
theorem blockDiagonal_inj
  given: [DecidableEq o] {M N : o -> Matrix m n α}
  proof: blockDiagonal_injective.eq_iff

@[simp]

中文:
定理 blockDiagonal_inj
  条件: [DecidableEq o] {M N : o -> 矩阵 m n α}
  证明: blockDiagonal_injective.eq_iff

@[simp]

Depends on / 依赖: blockDiagonal_injective, blockDiagonal_injective.eq_iff, eq_iff
-/
theorem blockDiagonal_inj [DecidableEq o] {M N : o -> Matrix m n α} :
    blockDiagonal M = blockDiagonal N ↔ M = N :=
  blockDiagonal_injective.eq_iff

@[simp]
/--
theorem `blockDiag_one` / 定理 `blockDiag_one`

English:
theorem blockDiag_one
  given: [DecidableEq o] [DecidableEq m] [One α]
  proof: funext blockDiag_diagonal _

中文:
定理 blockDiag_one
  条件: [DecidableEq o] [DecidableEq m] [幺 α]
  证明: funext blockDiag_diagonal _

Depends on / 依赖: blockDiag_diagonal
-/
theorem blockDiag_one [DecidableEq o] [DecidableEq m] [One α] :
    blockDiag (1 : Matrix (m × o) (m × o) α) = 1 :=
funext blockDiag_diagonal _

end Zero

@[simp]
/--
theorem `blockDiag_add` / 定理 `blockDiag_add`

English:
theorem blockDiag_add
  given: [Add α] (M N : Matrix (m × o) (n × o) α)
  proof: rfl

中文:
定理 blockDiag_add
  条件: [加法 α] (M N : 矩阵 (m × o) (n × o) α)
  证明: rfl
-/
theorem blockDiag_add [Add α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M + N) = blockDiag M + blockDiag N :=
  rfl

section

variable (o m n α)

/-- `Matrix.blockDiag` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `blockDiagAddMonoidHom` / `blockDiagAddMonoidHom` 的定义

English:
definition blockDiagAddMonoidHom
  signature: [AddZeroClass α]
  body: blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add

中文:
定义 blockDiagAddMonoidHom
  签名: [加法零类 α]
  定义体: blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add

Depends on / 依赖: blockDiag
-/
def blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α ->+ o -> Matrix m n α where
  toFun := blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add

end

@[simp]
/--
theorem `blockDiag_neg` / 定理 `blockDiag_neg`

English:
theorem blockDiag_neg
  given: [AddGroup α] (M : Matrix (m × o) (n × o) α)
  statement: blockDiag (-M) = -blockDiag M
  proof: map_neg (blockDiagAddMonoidHom m n o α) M

@[simp]

中文:
定理 blockDiag_neg
  条件: [加法群 α] (M : 矩阵 (m × o) (n × o) α)
  结论: blockDiag (-M) = -blockDiag M
  证明: map_neg (blockDiagAddMonoidHom m n o α) M

@[simp]

Depends on / 依赖: blockDiagAddMonoidHom, map_neg
-/
theorem blockDiag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) : blockDiag (-M) = -blockDiag M :=
  map_neg (blockDiagAddMonoidHom m n o α) M

@[simp]
/--
theorem `blockDiag_sub` / 定理 `blockDiag_sub`

English:
theorem blockDiag_sub
  given: [AddGroup α] (M N : Matrix (m × o) (n × o) α)
  proof: map_sub (blockDiagAddMonoidHom m n o α) M N

@[simp]

中文:
定理 blockDiag_sub
  条件: [加法群 α] (M N : 矩阵 (m × o) (n × o) α)
  证明: map_sub (blockDiagAddMonoidHom m n o α) M N

@[simp]

Depends on / 依赖: blockDiagAddMonoidHom, map_sub
-/
theorem blockDiag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M - N) = blockDiag M - blockDiag N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N

@[simp]
/--
theorem `blockDiag_smul` / 定理 `blockDiag_smul`

English:
theorem blockDiag_smul
  statement: {R : Type*} [SMul R α] (x : R)
  proof: rfl

中文:
定理 blockDiag_smul
  结论: {R : 类型} [标量乘法 R α] (x : R)
  证明: rfl
-/
theorem blockDiag_smul {R : Type*} [SMul R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiag (x • M) = x • blockDiag M :=
  rfl

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/--
Definition of `blockDiagonal'` / `blockDiagonal'` 的定义

English:
definition blockDiagonal'
  signature: (M : forall i, Matrix (m' i) (n' i) α)
  body: of
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σ i, m' i) -> (Σ i, n' i) -> α)

中文:
定义 blockDiagonal'
  签名: (M : 对任意 i, 矩阵 (m' i) (n' i) α)
  定义体: of
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σ i, m' i) -> (Σ i, n' i) -> α)

Depends on / 依赖: congr_arg, h.symm
-/
def blockDiagonal' (M : forall i, Matrix (m' i) (n' i) α) : Matrix (Σ i, m' i) (Σ i, n' i) α :=
of
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σ i, m' i) -> (Σ i, n' i) -> α)

-- TODO: set as an equation lemma for `blockDiagonal'`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `blockDiagonal'_apply'` / 定理 `blockDiagonal'_apply'`

English:
theorem blockDiagonal'_apply'
  given: (M : forall i, Matrix (m' i) (n' i) α) (k i k' j)
  proof: rfl

中文:
定理 blockDiagonal'_apply'
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α) (k i k' j)
  证明: rfl
-/
theorem blockDiagonal'_apply' (M : forall i, Matrix (m' i) (n' i) α) (k i k' j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ =
      if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :=
  rfl

/--
theorem `blockDiagonal'_eq_blockDiagonal` / 定理 `blockDiagonal'_eq_blockDiagonal`

English:
theorem blockDiagonal'_eq_blockDiagonal
  given: (M : o -> Matrix m n α) {k k'} (i j)
  proof: rfl

中文:
定理 blockDiagonal'_eq_blockDiagonal
  条件: (M : o -> 矩阵 m n α) {k k'} (i j)
  证明: rfl
-/
theorem blockDiagonal'_eq_blockDiagonal (M : o -> Matrix m n α) {k k'} (i j) :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl

/--
theorem `blockDiagonal'_submatrix_eq_blockDiagonal` / 定理 `blockDiagonal'_submatrix_eq_blockDiagonal`

English:
theorem blockDiagonal'_submatrix_eq_blockDiagonal
  given: (M : o -> Matrix m n α)
  proof: Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => rfl

中文:
定理 blockDiagonal'_submatrix_eq_blockDiagonal
  条件: (M : o -> 矩阵 m n α)
  证明: Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => rfl
-/
theorem blockDiagonal'_submatrix_eq_blockDiagonal (M : o -> Matrix m n α) :
    (blockDiagonal' M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) =
      blockDiagonal M :=
  Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => rfl

/--
theorem `blockDiagonal'_apply` / 定理 `blockDiagonal'_apply`

English:
theorem blockDiagonal'_apply
  given: (M : forall i, Matrix (m' i) (n' i) α) (ik jk)
  proof: rfl

@[simp]

中文:
定理 blockDiagonal'_apply
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α) (ik jk)
  证明: rfl

@[simp]
-/
theorem blockDiagonal'_apply (M : forall i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal' M ik jk =
      if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 := rfl

@[simp]
/--
theorem `blockDiagonal'_apply_eq` / 定理 `blockDiagonal'_apply_eq`

English:
theorem blockDiagonal'_apply_eq
  given: (M : forall i, Matrix (m' i) (n' i) α) (k i j)
  proof: dif_pos rfl

中文:
定理 blockDiagonal'_apply_eq
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α) (k i j)
  证明: dif_pos rfl
-/
theorem blockDiagonal'_apply_eq (M : forall i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl

/--
theorem `blockDiagonal'_apply_ne` / 定理 `blockDiagonal'_apply_ne`

English:
theorem blockDiagonal'_apply_ne
  given: (M : forall i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k != k')
  proof: dif_neg h

中文:
定理 blockDiagonal'_apply_ne
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α) {k k'} (i j) (h : k != k')
  证明: dif_neg h
-/
theorem blockDiagonal'_apply_ne (M : forall i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k != k') :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h

/--
theorem `blockDiagonal'_map` / 定理 `blockDiagonal'_map`

English:
theorem blockDiagonal'_map
  given: (M : forall i, Matrix (m' i) (n' i) α) (f : α -> β) (hf : f 0 = 0)
  proof: by
  ext
  simp only [map_apply, blockDiagonal'_apply]
  rw [apply_dite f]; rw [hf]

@[simp]

中文:
定理 blockDiagonal'_map
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α) (f : α -> β) (hf : f 0 = 0)
  证明: by
  ext
  simp only [map_apply, blockDiagonal'_apply]
  rw [apply_dite f]; rw [hf]

@[simp]
-/
theorem blockDiagonal'_map (M : forall i, Matrix (m' i) (n' i) α) (f : α -> β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f := by
  ext
  simp only [map_apply, blockDiagonal'_apply]
  rw [apply_dite f]; rw [hf]

@[simp]
/--
theorem `blockDiagonal'_transpose` / 定理 `blockDiagonal'_transpose`

English:
theorem blockDiagonal'_transpose
  given: (M : forall i, Matrix (m' i) (n' i) α)
  proof: by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [transpose_apply, blockDiagonal'_apply]
  split_ifs <;> grind

@[simp]

中文:
定理 blockDiagonal'_transpose
  条件: (M : 对任意 i, 矩阵 (m' i) (n' i) α)
  证明: by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [transpose_apply, blockDiagonal'_apply]
  split_ifs <;> grind

@[simp]
-/
theorem blockDiagonal'_transpose (M : forall i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ := by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [transpose_apply, blockDiagonal'_apply]
  split_ifs <;> grind

@[simp]
/--
theorem `blockDiagonal'_conjTranspose` / 定理 `blockDiagonal'_conjTranspose`

English:
theorem blockDiagonal'_conjTranspose
  statement: {α} [AddMonoid α] [StarAddMonoid α]
  proof: by
  simp only [conjTranspose, blockDiagonal'_transpose]
  exact blockDiagonal'_map _ star (star_zero α)

@[simp]

中文:
定理 blockDiagonal'_conjTranspose
  结论: {α} [加法幺半群 α] [StarAdd幺半群 α]
  证明: by
  simp only [conjTranspose, blockDiagonal'_transpose]
  exact blockDiagonal'_map _ star (star_zero α)

@[simp]
-/
theorem blockDiagonal'_conjTranspose {α} [AddMonoid α] [StarAddMonoid α]
    (M : forall i, Matrix (m' i) (n' i) α) : (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal'_transpose]
  exact blockDiagonal'_map _ star (star_zero α)

@[simp]
/--
theorem `blockDiagonal'_zero` / 定理 `blockDiagonal'_zero`

English:
theorem blockDiagonal'_zero
  statement: blockDiagonal' (0 : forall i, Matrix (m' i) (n' i) α) = 0
  proof: by
  ext
  simp [blockDiagonal'_apply]

@[simp]

中文:
定理 blockDiagonal'_zero
  结论: blockDiagonal' (0 : 对任意 i, 矩阵 (m' i) (n' i) α) = 0
  证明: by
  ext
  simp [blockDiagonal'_apply]

@[simp]
-/
theorem blockDiagonal'_zero : blockDiagonal' (0 : forall i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  simp [blockDiagonal'_apply]

@[simp]
/--
theorem `blockDiagonal'_diagonal` / 定理 `blockDiagonal'_diagonal`

English:
theorem blockDiagonal'_diagonal
  given: [forall i, DecidableEq (m' i)] (d : forall i, m' i -> α)
  proof: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]

@[simp]

中文:
定理 blockDiagonal'_diagonal
  条件: [对任意 i, DecidableEq (m' i)] (d : 对任意 i, m' i -> α)
  证明: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]

@[simp]
-/
theorem blockDiagonal'_diagonal [forall i, DecidableEq (m' i)] (d : forall i, m' i -> α) :
    (blockDiagonal' fun k => diagonal (d k)) = diagonal fun ik => d ik.1 ik.2 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [blockDiagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]

@[simp]
/--
theorem `blockDiagonal'_one` / 定理 `blockDiagonal'_one`

English:
theorem blockDiagonal'_one
  given: [forall i, DecidableEq (m' i)] [One α]
  proof: show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal'_diagonal]

中文:
定理 blockDiagonal'_one
  条件: [对任意 i, DecidableEq (m' i)] [幺 α]
  证明: show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal'_diagonal]
-/
theorem blockDiagonal'_one [forall i, DecidableEq (m' i)] [One α] :
    blockDiagonal' (1 : forall i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal'_diagonal]

end Zero

@[simp]
/--
theorem `blockDiagonal'_add` / 定理 `blockDiagonal'_add`

English:
theorem blockDiagonal'_add
  given: [AddZeroClass α] (M N : forall i, Matrix (m' i) (n' i) α)
  proof: by
  ext
  simp only [blockDiagonal'_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

中文:
定理 blockDiagonal'_add
  条件: [加法零类 α] (M N : 对任意 i, 矩阵 (m' i) (n' i) α)
  证明: by
  ext
  simp only [blockDiagonal'_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp
-/
theorem blockDiagonal'_add [AddZeroClass α] (M N : forall i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N := by
  ext
  simp only [blockDiagonal'_apply, Pi.add_apply, add_apply]
  split_ifs <;> simp

section

variable (m' n' α)

/-- `Matrix.blockDiagonal'` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `blockDiagonal'AddMonoidHom` / `blockDiagonal'AddMonoidHom` 的定义

English:
definition blockDiagonal'AddMonoidHom
  signature: [AddZeroClass α]
  body: blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add

中文:
定义 blockDiagonal'加法幺半群态射
  签名: [加法零类 α]
  定义体: blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add
-/
def blockDiagonal'AddMonoidHom [AddZeroClass α] :
    (forall i, Matrix (m' i) (n' i) α) ->+ Matrix (Σ i, m' i) (Σ i, n' i) α where
  toFun := blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add

end

@[simp]
/--
theorem `blockDiagonal'_neg` / 定理 `blockDiagonal'_neg`

English:
theorem blockDiagonal'_neg
  given: [AddGroup α] (M : forall i, Matrix (m' i) (n' i) α)
  proof: map_neg (blockDiagonal'AddMonoidHom m' n' α) M

@[simp]

中文:
定理 blockDiagonal'_neg
  条件: [加法群 α] (M : 对任意 i, 矩阵 (m' i) (n' i) α)
  证明: map_neg (blockDiagonal'AddMonoidHom m' n' α) M

@[simp]
-/
theorem blockDiagonal'_neg [AddGroup α] (M : forall i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (-M) = -blockDiagonal' M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M

@[simp]
/--
theorem `blockDiagonal'_sub` / 定理 `blockDiagonal'_sub`

English:
theorem blockDiagonal'_sub
  given: [AddGroup α] (M N : forall i, Matrix (m' i) (n' i) α)
  proof: map_sub (blockDiagonal'AddMonoidHom m' n' α) M N

@[simp]

中文:
定理 blockDiagonal'_sub
  条件: [加法群 α] (M N : 对任意 i, 矩阵 (m' i) (n' i) α)
  证明: map_sub (blockDiagonal'AddMonoidHom m' n' α) M N

@[simp]
-/
theorem blockDiagonal'_sub [AddGroup α] (M N : forall i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N

@[simp]
/--
theorem `blockDiagonal'_mul` / 定理 `blockDiagonal'_mul`

English:
theorem blockDiagonal'_mul
  statement: [NonUnitalNonAssocSemiring α] [forall i, Fintype (n' i)] [Fintype o]
  proof: by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [blockDiagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp only [dif_pos]
    split_ifs <;> simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]

中文:
定理 blockDiagonal'_mul
  结论: [非幺非结合半环 α] [对任意 i, 有限类型 (n' i)] [有限类型 o]
  证明: by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [blockDiagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp only [dif_pos]
    split_ifs <;> simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]
-/
theorem blockDiagonal'_mul [NonUnitalNonAssocSemiring α] [forall i, Fintype (n' i)] [Fintype o]
    (M : forall i, Matrix (m' i) (n' i) α) (N : forall i, Matrix (n' i) (p' i) α) :
    (blockDiagonal' fun k => M k * N k) = blockDiagonal' M * blockDiagonal' N := by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [blockDiagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp only [dif_pos]
    split_ifs <;> simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]

section

variable (α m')

/-- `Matrix.blockDiagonal'` as a `RingHom`. -/
@[simps]
/--
Definition of `blockDiagonal'RingHom` / `blockDiagonal'RingHom` 的定义

English:
definition blockDiagonal'RingHom
  signature: [forall i, DecidableEq (m' i)] [Fintype o] [forall i, Fintype (m' i)]
  body: { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }

中文:
定义 blockDiagonal'环态射
  签名: [对任意 i, DecidableEq (m' i)] [有限类型 o] [对任意 i, 有限类型 (m' i)]
  定义体: { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }
-/
def blockDiagonal'RingHom [forall i, DecidableEq (m' i)] [Fintype o] [forall i, Fintype (m' i)]
    [NonAssocSemiring α] : (forall i, Matrix (m' i) (m' i) α) ->+* Matrix (Σ i, m' i) (Σ i, m' i) α :=
  { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }

end

@[simp]
/--
theorem `blockDiagonal'_pow` / 定理 `blockDiagonal'_pow`

English:
theorem blockDiagonal'_pow
  statement: [forall i, DecidableEq (m' i)] [Fintype o] [forall i, Fintype (m' i)] [Semiring α]
  proof: map_pow (blockDiagonal'RingHom m' α) M n

@[simp]

中文:
定理 blockDiagonal'_pow
  结论: [对任意 i, DecidableEq (m' i)] [有限类型 o] [对任意 i, 有限类型 (m' i)] [半环 α]
  证明: map_pow (blockDiagonal'RingHom m' α) M n

@[simp]
-/
theorem blockDiagonal'_pow [forall i, DecidableEq (m' i)] [Fintype o] [forall i, Fintype (m' i)] [Semiring α]
    (M : forall i, Matrix (m' i) (m' i) α) (n : Nat) : blockDiagonal' (M ^ n) = blockDiagonal' M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n

@[simp]
/--
theorem `blockDiagonal'_smul` / 定理 `blockDiagonal'_smul`

English:
theorem blockDiagonal'_smul
  statement: {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
  proof: by
  ext
  simp only [blockDiagonal'_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

中文:
定理 blockDiagonal'_smul
  结论: {R : 类型} [零 α] [SMulZero类 R α] (x : R)
  证明: by
  ext
  simp only [blockDiagonal'_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp
-/
theorem blockDiagonal'_smul {R : Type*} [Zero α] [SMulZeroClass R α] (x : R)
    (M : forall i, Matrix (m' i) (n' i) α) : blockDiagonal' (x • M) = x • blockDiagonal' M := by
  ext
  simp only [blockDiagonal'_apply, Pi.smul_apply, smul_apply]
  split_ifs <;> simp

end BlockDiagonal'

section BlockDiag'

/--
Definition of `blockDiag'` / `blockDiag'` 的定义

English:
definition blockDiag'
  signature: (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o)
  body: of fun i j => M ⟨k, i⟩ ⟨k, j⟩

中文:
定义 blockDiag'
  签名: (M : 矩阵 (Σ i, m' i) (Σ i, n' i) α) (k : o)
  定义体: of fun i j => M ⟨k, i⟩ ⟨k, j⟩
-/
def blockDiag' (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : Matrix (m' k) (n' k) α :=
  of fun i j => M ⟨k, i⟩ ⟨k, j⟩

-- TODO: set as an equation lemma for `blockDiag'`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `blockDiag'_apply` / 定理 `blockDiag'_apply`

English:
theorem blockDiag'_apply
  given: (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) (i j)
  proof: rfl

中文:
定理 blockDiag'_apply
  条件: (M : 矩阵 (Σ i, m' i) (Σ i, n' i) α) (k : o) (i j)
  证明: rfl
-/
theorem blockDiag'_apply (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) (i j) :
    blockDiag' M k i j = M ⟨k, i⟩ ⟨k, j⟩ :=
  rfl

/--
theorem `blockDiag'_map` / 定理 `blockDiag'_map`

English:
theorem blockDiag'_map
  given: (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 blockDiag'_map
  条件: (M : 矩阵 (Σ i, m' i) (Σ i, n' i) α) (f : α -> β)
  证明: rfl

@[simp]
-/
theorem blockDiag'_map (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (f : α -> β) :
    blockDiag' (M.map f) = fun k => (blockDiag' M k).map f :=
  rfl

@[simp]
/--
theorem `blockDiag'_transpose` / 定理 `blockDiag'_transpose`

English:
theorem blockDiag'_transpose
  given: (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o)
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 blockDiag'_transpose
  条件: (M : 矩阵 (Σ i, m' i) (Σ i, n' i) α) (k : o)
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem blockDiag'_transpose (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) :
    blockDiag' Mᵀ k = (blockDiag' M k)ᵀ :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `blockDiag'_conjTranspose` / 定理 `blockDiag'_conjTranspose`

English:
theorem blockDiag'_conjTranspose
  statement: {α : Type*} [Star α]
  proof: ext fun _ _ => rfl

中文:
定理 blockDiag'_conjTranspose
  结论: {α : 类型} [对合 α]
  证明: ext fun _ _ => rfl
-/
theorem blockDiag'_conjTranspose {α : Type*} [Star α]
    (M : Matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : blockDiag' Mᴴ k = (blockDiag' M k)ᴴ :=
  ext fun _ _ => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
/--
theorem `blockDiag'_zero` / 定理 `blockDiag'_zero`

English:
theorem blockDiag'_zero
  statement: blockDiag' (0 : Matrix (Σ i, m' i) (Σ i, n' i) α) = 0
  proof: rfl

@[simp]

中文:
定理 blockDiag'_zero
  结论: blockDiag' (0 : 矩阵 (Σ i, m' i) (Σ i, n' i) α) = 0
  证明: rfl

@[simp]
-/
theorem blockDiag'_zero : blockDiag' (0 : Matrix (Σ i, m' i) (Σ i, n' i) α) = 0 :=
  rfl

@[simp]
/--
theorem `blockDiag'_diagonal` / 定理 `blockDiag'_diagonal`

English:
theorem blockDiag'_diagonal
  proof: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag'_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => ?_) hij)]
      cases h
      rfl

@[simp]

中文:
定理 blockDiag'_diagonal
  证明: ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag'_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => ?_) hij)]
      cases h
      rfl

@[simp]
-/
theorem blockDiag'_diagonal
    [DecidableEq o] [forall i, DecidableEq (m' i)] (d : (Σ i, m' i) -> α) (k : o) :
    blockDiag' (diagonal d) k = diagonal fun i => d ⟨k, i⟩ :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [blockDiag'_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [blockDiag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => ?_) hij)]
      cases h
      rfl

@[simp]
/--
theorem `blockDiag'_blockDiagonal'` / 定理 `blockDiag'_blockDiagonal'`

English:
theorem blockDiag'_blockDiagonal'
  given: [DecidableEq o] (M : forall i, Matrix (m' i) (n' i) α)
  proof: funext fun _ => ext fun _ _ => blockDiagonal'_apply_eq M _ _ _

中文:
定理 blockDiag'_blockDiagonal'
  条件: [DecidableEq o] (M : 对任意 i, 矩阵 (m' i) (n' i) α)
  证明: funext fun _ => ext fun _ _ => blockDiagonal'_apply_eq M _ _ _
-/
theorem blockDiag'_blockDiagonal' [DecidableEq o] (M : forall i, Matrix (m' i) (n' i) α) :
    blockDiag' (blockDiagonal' M) = M :=
  funext fun _ => ext fun _ _ => blockDiagonal'_apply_eq M _ _ _

/--
theorem `blockDiagonal'_injective` / 定理 `blockDiagonal'_injective`

English:
theorem blockDiagonal'_injective
  given: [DecidableEq o]
  proof: Function.LeftInverse.injective blockDiag'_blockDiagonal'

@[simp]

中文:
定理 blockDiagonal'_injective
  条件: [DecidableEq o]
  证明: Function.LeftInverse.injective blockDiag'_blockDiagonal'

@[simp]
-/
theorem blockDiagonal'_injective [DecidableEq o] :
    Function.Injective (blockDiagonal' : (forall i, Matrix (m' i) (n' i) α) -> Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag'_blockDiagonal'

@[simp]
/--
theorem `blockDiagonal'_inj` / 定理 `blockDiagonal'_inj`

English:
theorem blockDiagonal'_inj
  given: [DecidableEq o] {M N : forall i, Matrix (m' i) (n' i) α}
  proof: blockDiagonal'_injective.eq_iff

@[simp]

中文:
定理 blockDiagonal'_inj
  条件: [DecidableEq o] {M N : 对任意 i, 矩阵 (m' i) (n' i) α}
  证明: blockDiagonal'_injective.eq_iff

@[simp]
-/
theorem blockDiagonal'_inj [DecidableEq o] {M N : forall i, Matrix (m' i) (n' i) α} :
    blockDiagonal' M = blockDiagonal' N ↔ M = N :=
  blockDiagonal'_injective.eq_iff

@[simp]
/--
theorem `blockDiag'_one` / 定理 `blockDiag'_one`

English:
theorem blockDiag'_one
  given: [DecidableEq o] [forall i, DecidableEq (m' i)] [One α]
  proof: funext blockDiag'_diagonal _

中文:
定理 blockDiag'_one
  条件: [DecidableEq o] [对任意 i, DecidableEq (m' i)] [幺 α]
  证明: funext blockDiag'_diagonal _
-/
theorem blockDiag'_one [DecidableEq o] [forall i, DecidableEq (m' i)] [One α] :
    blockDiag' (1 : Matrix (Σ i, m' i) (Σ i, m' i) α) = 1 :=
funext blockDiag'_diagonal _

end Zero

@[simp]
/--
theorem `blockDiag'_add` / 定理 `blockDiag'_add`

English:
theorem blockDiag'_add
  given: [Add α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α)
  proof: rfl

中文:
定理 blockDiag'_add
  条件: [加法 α] (M N : 矩阵 (Σ i, m' i) (Σ i, n' i) α)
  证明: rfl
-/
theorem blockDiag'_add [Add α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (M + N) = blockDiag' M + blockDiag' N :=
  rfl

section

variable (m' n' α)

/-- `Matrix.blockDiag'` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `blockDiag'AddMonoidHom` / `blockDiag'AddMonoidHom` 的定义

English:
definition blockDiag'AddMonoidHom
  signature: [AddZeroClass α]
  body: blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add

中文:
定义 blockDiag'加法幺半群态射
  签名: [加法零类 α]
  定义体: blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add
-/
def blockDiag'AddMonoidHom [AddZeroClass α] :
    Matrix (Σ i, m' i) (Σ i, n' i) α ->+ forall i, Matrix (m' i) (n' i) α where
  toFun := blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add

end

@[simp]
/--
theorem `blockDiag'_neg` / 定理 `blockDiag'_neg`

English:
theorem blockDiag'_neg
  given: [AddGroup α] (M : Matrix (Σ i, m' i) (Σ i, n' i) α)
  proof: map_neg (blockDiag'AddMonoidHom m' n' α) M

@[simp]

中文:
定理 blockDiag'_neg
  条件: [加法群 α] (M : 矩阵 (Σ i, m' i) (Σ i, n' i) α)
  证明: map_neg (blockDiag'AddMonoidHom m' n' α) M

@[simp]
-/
theorem blockDiag'_neg [AddGroup α] (M : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (-M) = -blockDiag' M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M

@[simp]
/--
theorem `blockDiag'_sub` / 定理 `blockDiag'_sub`

English:
theorem blockDiag'_sub
  given: [AddGroup α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α)
  proof: map_sub (blockDiag'AddMonoidHom m' n' α) M N

@[simp]

中文:
定理 blockDiag'_sub
  条件: [加法群 α] (M N : 矩阵 (Σ i, m' i) (Σ i, n' i) α)
  证明: map_sub (blockDiag'AddMonoidHom m' n' α) M N

@[simp]
-/
theorem blockDiag'_sub [AddGroup α] (M N : Matrix (Σ i, m' i) (Σ i, n' i) α) :
    blockDiag' (M - N) = blockDiag' M - blockDiag' N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N

@[simp]
/--
theorem `blockDiag'_smul` / 定理 `blockDiag'_smul`

English:
theorem blockDiag'_smul
  statement: {R : Type*} [SMul R α] (x : R)
  proof: rfl

中文:
定理 blockDiag'_smul
  结论: {R : 类型} [标量乘法 R α] (x : R)
  证明: rfl
-/
theorem blockDiag'_smul {R : Type*} [SMul R α] (x : R)
    (M : Matrix (Σ i, m' i) (Σ i, n' i) α) : blockDiag' (x • M) = x • blockDiag' M :=
  rfl

end BlockDiag'

section

variable [CommRing R]

/--
theorem `toBlock_mul_eq_mul` / 定理 `toBlock_mul_eq_mul`

English:
theorem toBlock_mul_eq_mul
  statement: {m n k : Type*} [Fintype n] (p : m -> Prop) (q : k -> Prop)
  proof: by
  ext i k
  simp only [toBlock_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Pi.top_apply, Prop.top_eq_true]

中文:
定理 toBlock_mul_eq_mul
  结论: {m n k : 类型} [有限类型 n] (p : m -> 命题) (q : k -> 命题)
  证明: by
  ext i k
  simp only [toBlock_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Pi.top_apply, Prop.top_eq_true]

Depends on / 依赖: Finset, Finset.sum_subtype, Pi.top_apply, Prop.top_eq_true, mul_apply, sum_subtype, toBlock_apply, top_apply, top_eq_true
-/
theorem toBlock_mul_eq_mul {m n k : Type*} [Fintype n] (p : m -> Prop) (q : k -> Prop)
    (A : Matrix m n R) (B : Matrix n k R) :
    (A * B).toBlock p q = A.toBlock p ⊤ * B.toBlock ⊤ q := by
  ext i k
  simp only [toBlock_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Pi.top_apply, Prop.top_eq_true]

/--
theorem `toBlock_mul_eq_add` / 定理 `toBlock_mul_eq_add`

English:
theorem toBlock_mul_eq_add
  statement: {m n k : Type*} [Fintype n] (p : m -> Prop) (q : n -> Prop)
  proof: by
  ext i k
  simp only [toBlock_apply, mul_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

中文:
定理 toBlock_mul_eq_add
  结论: {m n k : 类型} [有限类型 n] (p : m -> 命题) (q : n -> 命题)
  证明: by
  ext i k
  simp only [toBlock_apply, mul_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

Depends on / 依赖: Fintype, Fintype.sum_subtype_add_sum_subtype, mul_apply, sum_subtype_add_sum_subtype, toBlock_apply
-/
theorem toBlock_mul_eq_add {m n k : Type*} [Fintype n] (p : m -> Prop) (q : n -> Prop)
    [DecidablePred q] (r : k -> Prop) (A : Matrix m n R) (B : Matrix n k R) : (A * B).toBlock p r =
    A.toBlock p q * B.toBlock q r + (A.toBlock p fun i => ¬q i) * B.toBlock (fun i => ¬q i) r := by
  ext i k
  simp only [toBlock_apply, mul_apply]
  exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm

end

end Matrix

section Maps

variable {R α β ι : Type*}

/--
lemma `Matrix.map_toSquareBlock` / 引理 `Matrix.map_toSquareBlock`

English:
lemma Matrix.map_toSquareBlock
  proof: submatrix_map _ _ _ _

中文:
引理 矩阵.map_toSquareBlock
  证明: submatrix_map _ _ _ _

Depends on / 依赖: submatrix_map
-/
lemma Matrix.map_toSquareBlock
    (f : α -> β) {M : Matrix m m α} {ι} {b : m -> ι} {i : ι} :
    (M.map f).toSquareBlock b i = (M.toSquareBlock b i).map f :=
  submatrix_map _ _ _ _

/--
lemma `Matrix.comp_toSquareBlock` / 引理 `Matrix.comp_toSquareBlock`

English:
lemma Matrix.comp_toSquareBlock
  statement: {b : m -> α}
  proof: Equiv.prodSubtypeFstEquivSubtypeProd.symm
    (M.comp m m n n R).toSquareBlock (fun i => b i.1) a =
      ((M.toSquareBlock b a).comp _ _ n n R).reindex equiv equiv :=
  rfl

中文:
引理 矩阵.comp_toSquareBlock
  结论: {b : m -> α}
  证明: Equiv.prodSubtypeFstEquivSubtypeProd.symm
    (M.comp m m n n R).toSquareBlock (fun i => b i.1) a =
      ((M.toSquareBlock b a).comp _ _ n n R).reindex equiv equiv :=
  rfl

Depends on / 依赖: Equiv.prodSubtypeFstEquivSubtypeProd.symm, prodSubtypeFstEquivSubtypeProd
-/
lemma Matrix.comp_toSquareBlock {b : m -> α}
    (M : Matrix m m (Matrix n n R)) (a : α) :
    letI equiv := Equiv.prodSubtypeFstEquivSubtypeProd.symm
    (M.comp m m n n R).toSquareBlock (fun i => b i.1) a =
      ((M.toSquareBlock b a).comp _ _ n n R).reindex equiv equiv :=
  rfl

variable [Zero R] [DecidableEq m]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Matrix.comp_diagonal` / 引理 `Matrix.comp_diagonal`

English:
lemma Matrix.comp_diagonal
  given: (d)
  proof: by
  ext
  simp [diagonal, blockDiagonal, Matrix.ite_apply]

中文:
引理 矩阵.comp_diagonal
  条件: (d)
  证明: by
  ext
  simp [diagonal, blockDiagonal, Matrix.ite_apply]

Depends on / 依赖: Matrix, Matrix.ite_apply, blockDiagonal, diagonal, ite_apply
-/
lemma Matrix.comp_diagonal (d) :
    comp m m n n R (diagonal d) =
      (blockDiagonal d).reindex (.prodComm ..) (.prodComm ..) := by
  ext
  simp [diagonal, blockDiagonal, Matrix.ite_apply]

end Maps
