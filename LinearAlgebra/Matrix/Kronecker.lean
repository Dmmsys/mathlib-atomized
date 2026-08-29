/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `Matrix.kroneckerMap`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kroneckerMap f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `Matrix.kroneckerMapBilinear`: when `f` is bilinear, so is `kroneckerMap f`.

## Specializations

* `Matrix.kronecker`: An alias of `kroneckerMap (*)`. Prefer using the notation.
* `Matrix.kroneckerBilinear`: `Matrix.kronecker` is bilinear

* `Matrix.kroneckerTMul`: An alias of `kroneckerMap (⊗ₜ)`. Prefer using the notation.
* `Matrix.kroneckerTMulBilinear`: `Matrix.kroneckerTMul` is bilinear

## Notation

These require `open Kronecker`:

* `A ⊗ₖ B` for `kroneckerMap (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kroneckerMap (⊗ₜ) A B`.
  Lemmas about this notation use the token `kroneckerTMul`.

-/

@[expose] public section


namespace Matrix
open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}
variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section KroneckerMap

/--
Definition of `kroneckerMap` / `kroneckerMap` 的定义

English:
definition kroneckerMap
  signature: (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β)
  body: of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)

中文:
定义 kroneckerMap
  签名: (f : α -> β -> γ) (A : 矩阵 l m α) (B : 矩阵 n p β)
  定义体: of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)
-/
def kroneckerMap (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)

-- TODO: set as an equation lemma for `kroneckerMap`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `kroneckerMap_apply` / 定理 `kroneckerMap_apply`

English:
theorem kroneckerMap_apply
  given: (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) (i j)
  proof: rfl

中文:
定理 kroneckerMap_apply
  条件: (f : α -> β -> γ) (A : 矩阵 l m α) (B : 矩阵 n p β) (i j)
  证明: rfl
-/
theorem kroneckerMap_apply (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) (i j) :
    kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2) :=
  rfl

/--
theorem `kroneckerMap_transpose` / 定理 `kroneckerMap_transpose`

English:
theorem kroneckerMap_transpose
  given: (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β)
  proof: ext fun _ _ => rfl

中文:
定理 kroneckerMap_transpose
  条件: (f : α -> β -> γ) (A : 矩阵 l m α) (B : 矩阵 n p β)
  证明: ext fun _ _ => rfl
-/
theorem kroneckerMap_transpose (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ :=
  ext fun _ _ => rfl

/--
theorem `kroneckerMap_map_left` / 定理 `kroneckerMap_map_left`

English:
theorem kroneckerMap_map_left
  given: (f : α' -> β -> γ) (g : α -> α') (A : Matrix l m α) (B : Matrix n p β)
  proof: ext fun _ _ => rfl

中文:
定理 kroneckerMap_map_left
  条件: (f : α' -> β -> γ) (g : α -> α') (A : 矩阵 l m α) (B : 矩阵 n p β)
  证明: ext fun _ _ => rfl
-/
theorem kroneckerMap_map_left (f : α' -> β -> γ) (g : α -> α') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A.map g) B = kroneckerMap (fun a b => f (g a) b) A B :=
  ext fun _ _ => rfl

/--
theorem `kroneckerMap_map_right` / 定理 `kroneckerMap_map_right`

English:
theorem kroneckerMap_map_right
  given: (f : α -> β' -> γ) (g : β -> β') (A : Matrix l m α) (B : Matrix n p β)
  proof: ext fun _ _ => rfl

中文:
定理 kroneckerMap_map_right
  条件: (f : α -> β' -> γ) (g : β -> β') (A : 矩阵 l m α) (B : 矩阵 n p β)
  证明: ext fun _ _ => rfl
-/
theorem kroneckerMap_map_right (f : α -> β' -> γ) (g : β -> β') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (B.map g) = kroneckerMap (fun a b => f a (g b)) A B :=
  ext fun _ _ => rfl

/--
theorem `kroneckerMap_map` / 定理 `kroneckerMap_map`

English:
theorem kroneckerMap_map
  given: (f : α -> β -> γ) (g : γ -> γ') (A : Matrix l m α) (B : Matrix n p β)
  proof: ext fun _ _ => rfl

中文:
定理 kroneckerMap_map
  条件: (f : α -> β -> γ) (g : γ -> γ') (A : 矩阵 l m α) (B : 矩阵 n p β)
  证明: ext fun _ _ => rfl
-/
theorem kroneckerMap_map (f : α -> β -> γ) (g : γ -> γ') (A : Matrix l m α) (B : Matrix n p β) :
    (kroneckerMap f A B).map g = kroneckerMap (fun a b => g (f a b)) A B :=
  ext fun _ _ => rfl

/--
theorem `kroneckerMap_submatrix_left` / 定理 `kroneckerMap_submatrix_left`

English:
theorem kroneckerMap_submatrix_left
  proof: rfl

中文:
定理 kroneckerMap_submatrix_left
  证明: rfl
-/
theorem kroneckerMap_submatrix_left
    (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) (r : l' -> l) (c : m' -> m) :
    kroneckerMap f (A.submatrix r c) B =
      (kroneckerMap f A B).submatrix (.map r id) (.map c id) :=
  rfl

/--
theorem `kroneckerMap_submatrix_right` / 定理 `kroneckerMap_submatrix_right`

English:
theorem kroneckerMap_submatrix_right
  proof: rfl

中文:
定理 kroneckerMap_submatrix_right
  证明: rfl
-/
theorem kroneckerMap_submatrix_right
    (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β) (r : n' -> n) (c : p' -> p) :
    kroneckerMap f A (B.submatrix r c) =
      (kroneckerMap f A B).submatrix (.map id r) (.map id c) :=
  rfl

/--
theorem `kroneckerMap_submatrix_submatrix` / 定理 `kroneckerMap_submatrix_submatrix`

English:
theorem kroneckerMap_submatrix_submatrix
  proof: rfl

@[simp]

中文:
定理 kroneckerMap_submatrix_submatrix
  证明: rfl

@[simp]
-/
theorem kroneckerMap_submatrix_submatrix
    (f : α -> β -> γ) (A : Matrix l m α) (B : Matrix n p β)
    (r : l' -> l) (c : m' -> m) (r' : n' -> n) (c' : p' -> p) :
    kroneckerMap f (A.submatrix r c) (B.submatrix r' c') =
      (kroneckerMap f A B).submatrix (.map r r') (.map c c') :=
  rfl

@[simp]
/--
theorem `kroneckerMap_zero_left` / 定理 `kroneckerMap_zero_left`

English:
theorem kroneckerMap_zero_left
  statement: [Zero α] [Zero γ] (f : α -> β -> γ) (hf : forall b, f 0 b = 0)
  proof: ext fun _ _ => hf _

@[simp]

中文:
定理 kroneckerMap_zero_left
  结论: [零 α] [零 γ] (f : α -> β -> γ) (hf : 对任意 b, f 0 b = 0)
  证明: ext fun _ _ => hf _

@[simp]
-/
theorem kroneckerMap_zero_left [Zero α] [Zero γ] (f : α -> β -> γ) (hf : forall b, f 0 b = 0)
    (B : Matrix n p β) : kroneckerMap f (0 : Matrix l m α) B = 0 :=
  ext fun _ _ => hf _

@[simp]
/--
theorem `kroneckerMap_zero_right` / 定理 `kroneckerMap_zero_right`

English:
theorem kroneckerMap_zero_right
  statement: [Zero β] [Zero γ] (f : α -> β -> γ) (hf : forall a, f a 0 = 0)
  proof: ext fun _ _ => hf _

中文:
定理 kroneckerMap_zero_right
  结论: [零 β] [零 γ] (f : α -> β -> γ) (hf : 对任意 a, f a 0 = 0)
  证明: ext fun _ _ => hf _
-/
theorem kroneckerMap_zero_right [Zero β] [Zero γ] (f : α -> β -> γ) (hf : forall a, f a 0 = 0)
    (A : Matrix l m α) : kroneckerMap f A (0 : Matrix n p β) = 0 :=
  ext fun _ _ => hf _

/--
theorem `kroneckerMap_add_left` / 定理 `kroneckerMap_add_left`

English:
theorem kroneckerMap_add_left
  statement: [Add α] [Add γ] (f : α -> β -> γ)
  proof: ext fun _ _ => hf _ _ _

中文:
定理 kroneckerMap_add_left
  结论: [加法 α] [加法 γ] (f : α -> β -> γ)
  证明: ext fun _ _ => hf _ _ _
-/
theorem kroneckerMap_add_left [Add α] [Add γ] (f : α -> β -> γ)
    (hf : forall a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B :=
  ext fun _ _ => hf _ _ _

/--
theorem `kroneckerMap_add_right` / 定理 `kroneckerMap_add_right`

English:
theorem kroneckerMap_add_right
  statement: [Add β] [Add γ] (f : α -> β -> γ)
  proof: ext fun _ _ => hf _ _ _

中文:
定理 kroneckerMap_add_right
  结论: [加法 β] [加法 γ] (f : α -> β -> γ)
  证明: ext fun _ _ => hf _ _ _
-/
theorem kroneckerMap_add_right [Add β] [Add γ] (f : α -> β -> γ)
    (hf : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    kroneckerMap f A (B₁ + B₂) = kroneckerMap f A B₁ + kroneckerMap f A B₂ :=
  ext fun _ _ => hf _ _ _

/--
theorem `kroneckerMap_smul_left` / 定理 `kroneckerMap_smul_left`

English:
theorem kroneckerMap_smul_left
  statement: [SMul R α] [SMul R γ] (f : α -> β -> γ) (r : R)
  proof: ext fun _ _ => hf _ _

中文:
定理 kroneckerMap_smul_left
  结论: [标量乘法 R α] [标量乘法 R γ] (f : α -> β -> γ) (r : R)
  证明: ext fun _ _ => hf _ _
-/
theorem kroneckerMap_smul_left [SMul R α] [SMul R γ] (f : α -> β -> γ) (r : R)
    (hf : forall a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (r • A) B = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _

/--
theorem `kroneckerMap_smul_right` / 定理 `kroneckerMap_smul_right`

English:
theorem kroneckerMap_smul_right
  statement: [SMul R β] [SMul R γ] (f : α -> β -> γ) (r : R)
  proof: ext fun _ _ => hf _ _

中文:
定理 kroneckerMap_smul_right
  结论: [标量乘法 R β] [标量乘法 R γ] (f : α -> β -> γ) (r : R)
  证明: ext fun _ _ => hf _ _
-/
theorem kroneckerMap_smul_right [SMul R β] [SMul R γ] (f : α -> β -> γ) (r : R)
    (hf : forall a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (r • B) = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _

/--
theorem `kroneckerMap_single_single` / 定理 `kroneckerMap_single_single`

English:
theorem kroneckerMap_single_single
  proof: by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind

中文:
定理 kroneckerMap_single_single
  证明: by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind

Depends on / 依赖: single
-/
theorem kroneckerMap_single_single
    [Zero α] [Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p)
    (f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂ : forall a, f a 0 = 0) (a : α) (b : β) :
    kroneckerMap f (single i₁ j₁ a) (single i₂ j₂ b) = single (i₁, i₂) (j₁, j₂) (f a b) := by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind

/--
theorem `kroneckerMap_diagonal_diagonal` / 定理 `kroneckerMap_diagonal_diagonal`

English:
theorem kroneckerMap_diagonal_diagonal
  statement: [Zero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n]
  proof: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]

中文:
定理 kroneckerMap_diagonal_diagonal
  结论: [零 α] [零 β] [零 γ] [DecidableEq m] [DecidableEq n]
  证明: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]

Depends on / 依赖: apply_ite, diagonal, ite_and, ite_apply
-/
theorem kroneckerMap_diagonal_diagonal [Zero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n]
    (f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂ : forall a, f a 0 = 0) (a : m -> α) (b : n -> β) :
    kroneckerMap f (diagonal a) (diagonal b) = diagonal fun mn => f (a mn.1) (b mn.2) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]

/--
theorem `kroneckerMap_diagonal_right` / 定理 `kroneckerMap_diagonal_right`

English:
theorem kroneckerMap_diagonal_right
  statement: [Zero β] [Zero γ] [DecidableEq n] (f : α -> β -> γ)
  proof: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite (f (A i₁ j₁)), hf]

中文:
定理 kroneckerMap_diagonal_right
  结论: [零 β] [零 γ] [DecidableEq n] (f : α -> β -> γ)
  证明: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite (f (A i₁ j₁)), hf]

Depends on / 依赖: apply_ite, blockDiagonal, diagonal
-/
theorem kroneckerMap_diagonal_right [Zero β] [Zero γ] [DecidableEq n] (f : α -> β -> γ)
    (hf : forall a, f a 0 = 0) (A : Matrix l m α) (b : n -> β) :
    kroneckerMap f A (diagonal b) = blockDiagonal fun i => A.map fun a => f a (b i) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite (f (A i₁ j₁)), hf]

/--
theorem `kroneckerMap_diagonal_left` / 定理 `kroneckerMap_diagonal_left`

English:
theorem kroneckerMap_diagonal_left
  statement: [Zero α] [Zero γ] [DecidableEq l] (f : α -> β -> γ)
  proof: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite f, ite_apply, hf]

@[simp]

中文:
定理 kroneckerMap_diagonal_left
  结论: [零 α] [零 γ] [DecidableEq l] (f : α -> β -> γ)
  证明: by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite f, ite_apply, hf]

@[simp]

Depends on / 依赖: apply_ite, blockDiagonal, diagonal, ite_apply
-/
theorem kroneckerMap_diagonal_left [Zero α] [Zero γ] [DecidableEq l] (f : α -> β -> γ)
    (hf : forall b, f 0 b = 0) (a : l -> α) (B : Matrix m n β) :
    kroneckerMap f (diagonal a) B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => f (a i) b) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite f, ite_apply, hf]

@[simp]
/--
theorem `kroneckerMap_one_one` / 定理 `kroneckerMap_one_one`

English:
theorem kroneckerMap_one_one
  statement: [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [DecidableEq m]
  proof: (kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans by simp only [hf₃, diagonal_one]

中文:
定理 kroneckerMap_one_one
  结论: [零 α] [零 β] [零 γ] [幺 α] [幺 β] [幺 γ] [DecidableEq m]
  证明: (kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans by simp only [hf₃, diagonal_one]

Depends on / 依赖: diagonal_one, kroneckerMap_diagonal_diagonal
-/
theorem kroneckerMap_one_one [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [DecidableEq m]
    [DecidableEq n] (f : α -> β -> γ) (hf₁ : forall b, f 0 b = 0) (hf₂ : forall a, f a 0 = 0)
    (hf₃ : f 1 1 = 1) : kroneckerMap f (1 : Matrix m m α) (1 : Matrix n n β) = 1 :=
(kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans by simp only [hf₃, diagonal_one]

/--
theorem `kroneckerMap_reindex` / 定理 `kroneckerMap_reindex`

English:
theorem kroneckerMap_reindex
  statement: (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
  proof: by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl

中文:
定理 kroneckerMap_reindex
  结论: (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
  证明: by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl
-/
theorem kroneckerMap_reindex (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
    (M : Matrix l m α) (N : Matrix n p β) :
    kroneckerMap f (reindex el em M) (reindex en ep N) =
      reindex (el.prodCongr en) (em.prodCongr ep) (kroneckerMap f M N) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl

/--
theorem `kroneckerMap_reindex_left` / 定理 `kroneckerMap_reindex_left`

English:
theorem kroneckerMap_reindex_left
  statement: (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α)
  proof: kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _

中文:
定理 kroneckerMap_reindex_left
  结论: (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (M : 矩阵 l m α)
  证明: kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _

Depends on / 依赖: Equiv.refl, kroneckerMap_reindex
-/
theorem kroneckerMap_reindex_left (f : α -> β -> γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α)
    (N : Matrix n n' β) :
    kroneckerMap f (Matrix.reindex el em M) N =
      reindex (el.prodCongr (Equiv.refl _)) (em.prodCongr (Equiv.refl _)) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _

/--
theorem `kroneckerMap_reindex_right` / 定理 `kroneckerMap_reindex_right`

English:
theorem kroneckerMap_reindex_right
  statement: (f : α -> β -> γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α)
  proof: kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _

中文:
定理 kroneckerMap_reindex_right
  结论: (f : α -> β -> γ) (em : m ≃ m') (en : n ≃ n') (M : 矩阵 l l' α)
  证明: kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _

Depends on / 依赖: Equiv.refl, kroneckerMap_reindex
-/
theorem kroneckerMap_reindex_right (f : α -> β -> γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α)
    (N : Matrix m n β) :
    kroneckerMap f M (reindex em en N) =
      reindex ((Equiv.refl _).prodCongr em) ((Equiv.refl _).prodCongr en) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _

/--
theorem `kroneckerMap_assoc` / 定理 `kroneckerMap_assoc`

English:
theorem kroneckerMap_assoc
  statement: {δ ξ ω ω' : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω')
  proof: ext fun _ _ => hφ _ _ _

中文:
定理 kroneckerMap_assoc
  结论: {δ ξ ω ω' : 类型} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω')
  证明: ext fun _ _ => hφ _ _ _
-/
theorem kroneckerMap_assoc {δ ξ ω ω' : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω')
    (g' : β -> δ -> ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (φ : ω ≃ ω')
    (hφ : forall a b d, φ (g (f a b) d) = f' a (g' b d)) :
    (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMatrix φ)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => hφ _ _ _

/--
theorem `kroneckerMap_assoc₁` / 定理 `kroneckerMap_assoc₁`

English:
theorem kroneckerMap_assoc₁
  statement: {δ ξ ω : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω)
  proof: ext fun _ _ => h _ _ _

中文:
定理 kroneckerMap_assoc₁
  结论: {δ ξ ω : 类型} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω)
  证明: ext fun _ _ => h _ _ _
-/
theorem kroneckerMap_assoc₁ {δ ξ ω : Type*} (f : α -> β -> γ) (g : γ -> δ -> ω) (f' : α -> ξ -> ω)
    (g' : β -> δ -> ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ)
    (h : forall a b d, g (f a b) d = f' a (g' b d)) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => h _ _ _

/-- When `f` is bilinear then `Matrix.kroneckerMap f` is also bilinear. -/
@[simps!]
/--
Definition of `kroneckerMapBilinear` / `kroneckerMapBilinear` 的定义

English:
definition kroneckerMapBilinear
  signature: [Semiring S] [Semiring R]
  body: LinearMap.mk₂' R S (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun _ => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r

中文:
定义 kroneckerMapBilinear
  签名: [半环 S] [半环 R]
  定义体: LinearMap.mk₂' R S (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun _ => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r

Depends on / 依赖: LinearMap, LinearMap.mk, f.map_add, f.map_smul, kroneckerMap, kroneckerMap_add_left, kroneckerMap_add_right, kroneckerMap_smul_left, kroneckerMap_smul_right, map_add, map_smul
-/
def kroneckerMapBilinear [Semiring S] [Semiring R]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α ->ₗ[R] β ->ₗ[S] γ) :
    Matrix l m α ->ₗ[R] Matrix n p β ->ₗ[S] Matrix (l × n) (m × p) γ :=
  LinearMap.mk₂' R S (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun _ => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r

/--
theorem `kroneckerMapBilinear_mul_mul` / 定理 `kroneckerMapBilinear_mul_mul`

English:
theorem kroneckerMapBilinear_mul_mul
  statement: [Semiring S] [Semiring R] [Fintype m] [Fintype m']
  proof: by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kroneckerMapBilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kroneckerMap_apply]
  simp_rw [map_sum f, LinearMap.sum_apply, map_sum, h_comm]

中文:
定理 kroneckerMapBilinear_mul_mul
  结论: [半环 S] [半环 R] [有限类型 m] [有限类型 m']
  证明: by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kroneckerMapBilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kroneckerMap_apply]
  simp_rw [map_sum f, LinearMap.sum_apply, map_sum, h_comm]

Depends on / 依赖: Finset, Finset.sum_product, Finset.univ_product_univ, LinearMap, LinearMap.sum_apply, h_comm, kroneckerMapBilinear_apply_apply, kroneckerMap_apply, map_sum, mul_apply, simp_rw, sum_apply, sum_product, univ_product_univ
-/
theorem kroneckerMapBilinear_mul_mul [Semiring S] [Semiring R] [Fintype m] [Fintype m']
    [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α ->ₗ[R] β ->ₗ[S] γ)
    (h_comm : forall a b a' b', f (a * b) (a' * b') = f a a' * f b b') (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    kroneckerMapBilinear f (A * B) (A' * B') =
      kroneckerMapBilinear f A A' * kroneckerMapBilinear f B B' := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kroneckerMapBilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kroneckerMap_apply]
  simp_rw [map_sum f, LinearMap.sum_apply, map_sum, h_comm]

/--
theorem `trace_kroneckerMapBilinear` / 定理 `trace_kroneckerMapBilinear`

English:
theorem trace_kroneckerMapBilinear
  statement: [Semiring S] [Semiring R] [Fintype m] [Fintype n]
  proof: by
  simp_rw [Matrix.trace, Matrix.diag, kroneckerMapBilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kroneckerMap_apply]

中文:
定理 trace_kroneckerMapBilinear
  结论: [半环 S] [半环 R] [有限类型 m] [有限类型 n]
  证明: by
  simp_rw [Matrix.trace, Matrix.diag, kroneckerMapBilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kroneckerMap_apply]

Depends on / 依赖: Finset, Finset.sum_product, Finset.univ_product_univ, LinearMap, LinearMap.map_sum, Matrix, Matrix.diag, Matrix.trace, kroneckerMapBilinear_apply_apply, kroneckerMap_apply, map_sum, simp_rw, sum_product, univ_product_univ
-/
theorem trace_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α ->ₗ[R] β ->ₗ[S] γ)
    (A : Matrix m m α) (B : Matrix n n β) :
    trace (kroneckerMapBilinear f A B) = f (trace A) (trace B) := by
  simp_rw [Matrix.trace, Matrix.diag, kroneckerMapBilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kroneckerMap_apply]

/--
theorem `det_kroneckerMapBilinear` / 定理 `det_kroneckerMapBilinear`

English:
theorem det_kroneckerMapBilinear
  statement: [Semiring S] [Semiring R] [Fintype m] [Fintype n] [DecidableEq m]
  proof: calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 * kroneckerMapBilinear f 1 B) := by
      rw [← kroneckerMapBilinear_mul_mul f h_comm]; rw [Matrix.mul_one]; rw [Matrix.one_mul]
    _ = det (blockDiagonal fun (_ : n) => A.map fun a => f a 1) *
        det (blockDia

中文:
定理 det_kroneckerMapBilinear
  结论: [半环 S] [半环 R] [有限类型 m] [有限类型 n] [DecidableEq m]
  证明: calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 * kroneckerMapBilinear f 1 B) := by
      rw [← kroneckerMapBilinear_mul_mul f h_comm]; rw [Matrix.mul_one]; rw [Matrix.one_mul]
    _ = det (blockDiagonal fun (_ : n) => A.map fun a => f a 1) *
        det (blockDia

Depends on / 依赖: A.map, B.map, Matrix, Matrix.mul_one, Matrix.one_mul, blockDiagonal, det_mul, diagonal_one, h_comm, kroneckerMapBilinear, kroneckerMapBilinear_apply_apply, kroneckerMapBilinear_mul_mul, kroneckerMap_diagonal_right, mul_one, one_mul
-/
theorem det_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β] [CommRing γ] [Module R α] [Module S β]
    [Module R γ] [Module S γ] [SMulCommClass S R γ]
    (f : α ->ₗ[R] β ->ₗ[S] γ) (h_comm : forall a b a' b', f (a * b) (a' * b') = f a a' * f b b')
    (A : Matrix m m α) (B : Matrix n n β) :
    det (kroneckerMapBilinear f A B) =
      det (A.map fun a => f a 1) ^ Fintype.card n * det (B.map fun b => f 1 b) ^ Fintype.card m :=
  calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 * kroneckerMapBilinear f 1 B) := by
      rw [← kroneckerMapBilinear_mul_mul f h_comm]; rw [Matrix.mul_one]; rw [Matrix.one_mul]
    _ = det (blockDiagonal fun (_ : n) => A.map fun a => f a 1) *
        det (blockDiagonal fun (_ : m) => B.map fun b => f 1 b) := by
      rw [det_mul]; rw [← diagonal_one]; rw [← diagonal_one]; rw [kroneckerMapBilinear_apply_apply]; rw [kroneckerMap_diagonal_right _ fun _ => _]; rw [kroneckerMapBilinear_apply_apply]; rw [kroneckerMap_diagonal_left _ fun _ => _]; rw [det_reindex_self]
      · intro; exact LinearMap.map_zero₂ _ _
      · intro; exact map_zero _
    _ = _ := by simp_rw [det_blockDiagonal, Finset.prod_const, Finset.card_univ]

end KroneckerMap

/-! ### Specialization to `Matrix.kroneckerMap (*)` -/


section Kronecker

open Matrix

/-- The Kronecker product. This is just a shorthand for `kroneckerMap (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
/--
Definition of `kronecker` / `kronecker` 的定义

English:
definition kronecker
  signature: [Mul α]
  body: kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " otimesₖ " => Matrix.kroneckerMap (· * ·)

中文:
定义 kronecker
  签名: [乘法 α]
  定义体: kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " otimesₖ " => Matrix.kroneckerMap (· * ·)

Depends on / 依赖: kroneckerMap
-/
def kronecker [Mul α] : Matrix l m α -> Matrix n p α -> Matrix (l × n) (m × p) α :=
  kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " otimesₖ " => Matrix.kroneckerMap (· * ·)

open Kronecker

@[simp]
/--
theorem `kronecker_apply` / 定理 `kronecker_apply`

English:
theorem kronecker_apply
  given: [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂)
  proof: rfl

中文:
定理 kronecker_apply
  条件: [乘法 α] (A : 矩阵 l m α) (B : 矩阵 n p α) (i₁ i₂ j₁ j₂)
  证明: rfl
-/
theorem kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂) :
    (A otimesₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ :=
  rfl

/--
Definition of `kroneckerBilinear` / `kroneckerBilinear` 的定义

English:
definition kroneckerBilinear
  signature: [CommSemiring R] [Semiring α] [Algebra R α]
  body: kroneckerMapBilinear (Algebra.lmul R α)

中文:
定义 kroneckerBilinear
  签名: [交换半环 R] [半环 α] [代数 R α]
  定义体: kroneckerMapBilinear (Algebra.lmul R α)

Depends on / 依赖: Algebra, Algebra.lmul, kroneckerMapBilinear
-/
def kroneckerBilinear [CommSemiring R] [Semiring α] [Algebra R α] :
    Matrix l m α ->ₗ[R] Matrix n p α ->ₗ[R] Matrix (l × n) (m × p) α :=
  kroneckerMapBilinear (Algebra.lmul R α)



/--
theorem `zero_kronecker` / 定理 `zero_kronecker`

English:
theorem zero_kronecker
  given: [MulZeroClass α] (B : Matrix n p α)
  statement: (0 : Matrix l m α) otimesₖ B = 0
  proof: kroneckerMap_zero_left _ zero_mul B

中文:
定理 zero_kronecker
  条件: [乘零类 α] (B : 矩阵 n p α)
  结论: (0 : 矩阵 l m α) otimesₖ B = 0
  证明: kroneckerMap_zero_left _ zero_mul B

Depends on / 依赖: kroneckerMap_zero_left, zero_mul
-/
theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) otimesₖ B = 0 :=
  kroneckerMap_zero_left _ zero_mul B

/--
theorem `kronecker_zero` / 定理 `kronecker_zero`

English:
theorem kronecker_zero
  given: [MulZeroClass α] (A : Matrix l m α)
  statement: A otimesₖ (0 : Matrix n p α) = 0
  proof: kroneckerMap_zero_right _ mul_zero A

中文:
定理 kronecker_zero
  条件: [乘零类 α] (A : 矩阵 l m α)
  结论: A otimesₖ (0 : 矩阵 n p α) = 0
  证明: kroneckerMap_zero_right _ mul_zero A

Depends on / 依赖: kroneckerMap_zero_right, mul_zero
-/
theorem kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A otimesₖ (0 : Matrix n p α) = 0 :=
  kroneckerMap_zero_right _ mul_zero A

/--
theorem `add_kronecker` / 定理 `add_kronecker`

English:
theorem add_kronecker
  given: [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α)
  proof: kroneckerMap_add_left _ add_mul _ _ _

中文:
定理 add_kronecker
  条件: [Distrib α] (A₁ A₂ : 矩阵 l m α) (B : 矩阵 n p α)
  证明: kroneckerMap_add_left _ add_mul _ _ _

Depends on / 依赖: add_mul, kroneckerMap_add_left
-/
theorem add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) otimesₖ B = A₁ otimesₖ B + A₂ otimesₖ B :=
  kroneckerMap_add_left _ add_mul _ _ _

/--
theorem `kronecker_add` / 定理 `kronecker_add`

English:
theorem kronecker_add
  given: [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α)
  proof: kroneckerMap_add_right _ mul_add _ _ _

中文:
定理 kronecker_add
  条件: [Distrib α] (A : 矩阵 l m α) (B₁ B₂ : 矩阵 n p α)
  证明: kroneckerMap_add_right _ mul_add _ _ _

Depends on / 依赖: kroneckerMap_add_right, mul_add
-/
theorem kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) :
    A otimesₖ (B₁ + B₂) = A otimesₖ B₁ + A otimesₖ B₂ :=
  kroneckerMap_add_right _ mul_add _ _ _

/--
theorem `smul_kronecker` / 定理 `smul_kronecker`

English:
theorem smul_kronecker
  statement: [Mul α] [SMul R α] [IsScalarTower R α α] (r : R)
  proof: kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

中文:
定理 smul_kronecker
  结论: [乘法 α] [标量乘法 R α] [标量塔 R α α] (r : R)
  证明: kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

Depends on / 依赖: kroneckerMap_smul_left, smul_mul_assoc
-/
theorem smul_kronecker [Mul α] [SMul R α] [IsScalarTower R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : (r • A) otimesₖ B = r • A otimesₖ B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

/--
theorem `kronecker_smul` / 定理 `kronecker_smul`

English:
theorem kronecker_smul
  statement: [Mul α] [SMul R α] [SMulCommClass R α α] (r : R)
  proof: kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _

中文:
定理 kronecker_smul
  结论: [乘法 α] [标量乘法 R α] [标量交换类 R α α] (r : R)
  证明: kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _

Depends on / 依赖: kroneckerMap_smul_right, mul_smul_comm
-/
theorem kronecker_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : A otimesₖ (r • B) = r • A otimesₖ B :=
  kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _

/--
theorem `single_kronecker_single` / 定理 `single_kronecker_single`

English:
theorem single_kronecker_single
  proof: kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _

中文:
定理 single_kronecker_single
  证明: kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _

Depends on / 依赖: kroneckerMap_single_single, mul_zero, zero_mul
-/
theorem single_kronecker_single
    [MulZeroClass α] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ia : l) (ja : m) (ib : n) (jb : p) (a b : α) :
    single ia ja a otimesₖ single ib jb b = single (ia, ib) (ja, jb) (a * b) :=
  kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _

/--
theorem `diagonal_kronecker_diagonal` / 定理 `diagonal_kronecker_diagonal`

English:
theorem diagonal_kronecker_diagonal
  statement: [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m -> α)
  proof: kroneckerMap_diagonal_diagonal _ zero_mul mul_zero _ _

中文:
定理 diagonal_kronecker_diagonal
  结论: [乘零类 α] [DecidableEq m] [DecidableEq n] (a : m -> α)
  证明: kroneckerMap_diagonal_diagonal _ zero_mul mul_zero _ _

Depends on / 依赖: kroneckerMap_diagonal_diagonal, mul_zero, zero_mul
-/
theorem diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m -> α)
    (b : n -> α) : diagonal a otimesₖ diagonal b = diagonal fun mn => a mn.1 * b mn.2 :=
  kroneckerMap_diagonal_diagonal _ zero_mul mul_zero _ _

/--
theorem `kronecker_diagonal` / 定理 `kronecker_diagonal`

English:
theorem kronecker_diagonal
  given: [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b : n -> α)
  proof: kroneckerMap_diagonal_right _ mul_zero _ _

中文:
定理 kronecker_diagonal
  条件: [乘零类 α] [DecidableEq n] (A : 矩阵 l m α) (b : n -> α)
  证明: kroneckerMap_diagonal_right _ mul_zero _ _

Depends on / 依赖: kroneckerMap_diagonal_right, mul_zero
-/
theorem kronecker_diagonal [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b : n -> α) :
    A otimesₖ diagonal b = blockDiagonal fun i => A <• b i :=
  kroneckerMap_diagonal_right _ mul_zero _ _

/--
theorem `diagonal_kronecker` / 定理 `diagonal_kronecker`

English:
theorem diagonal_kronecker
  given: [MulZeroClass α] [DecidableEq l] (a : l -> α) (B : Matrix m n α)
  proof: kroneckerMap_diagonal_left _ zero_mul _ _

@[simp]

中文:
定理 diagonal_kronecker
  条件: [乘零类 α] [DecidableEq l] (a : l -> α) (B : 矩阵 m n α)
  证明: kroneckerMap_diagonal_left _ zero_mul _ _

@[simp]

Depends on / 依赖: kroneckerMap_diagonal_left, zero_mul
-/
theorem diagonal_kronecker [MulZeroClass α] [DecidableEq l] (a : l -> α) (B : Matrix m n α) :
    diagonal a otimesₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun i => a i • B) :=
  kroneckerMap_diagonal_left _ zero_mul _ _

@[simp]
/--
theorem `natCast_kronecker_natCast` / 定理 `natCast_kronecker_natCast`

English:
theorem natCast_kronecker_natCast
  given: [NonAssocSemiring α] [DecidableEq m] [DecidableEq n] (a b : Nat)
  proof: (diagonal_kronecker_diagonal _ _).trans by simp_rw [← Nat.cast_mul]; rfl

中文:
定理 natCast_kronecker_natCast
  条件: [非结合半环 α] [DecidableEq m] [DecidableEq n] (a b : 自然数)
  证明: (diagonal_kronecker_diagonal _ _).trans by simp_rw [← Nat.cast_mul]; rfl

Depends on / 依赖: Nat.cast_mul, cast_mul, diagonal_kronecker_diagonal, simp_rw
-/
theorem natCast_kronecker_natCast [NonAssocSemiring α] [DecidableEq m] [DecidableEq n] (a b : Nat) :
    (a : Matrix m m α) otimesₖ (b : Matrix n n α) = ↑(a * b) :=
(diagonal_kronecker_diagonal _ _).trans by simp_rw [← Nat.cast_mul]; rfl

/--
theorem `kronecker_natCast` / 定理 `kronecker_natCast`

English:
theorem kronecker_natCast
  given: [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : Nat)
  proof: .trans by kronecker_diagonal _ _
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]

中文:
定理 kronecker_natCast
  条件: [非结合半环 α] [DecidableEq n] (A : 矩阵 l m α) (b : 自然数)
  证明: .trans by kronecker_diagonal _ _
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]

Depends on / 依赖: Nat.cast_commute, cast_commute, kronecker_diagonal
-/
theorem kronecker_natCast [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : Nat) :
    A otimesₖ (b : Matrix n n α) = blockDiagonal fun _ => b • A :=
.trans by kronecker_diagonal _ _
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]

/--
theorem `natCast_kronecker` / 定理 `natCast_kronecker`

English:
theorem natCast_kronecker
  given: [NonAssocSemiring α] [DecidableEq l] (a : Nat) (B : Matrix m n α)
  proof: .trans by diagonal_kronecker _ _
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]

中文:
定理 natCast_kronecker
  条件: [非结合半环 α] [DecidableEq l] (a : 自然数) (B : 矩阵 m n α)
  证明: .trans by diagonal_kronecker _ _
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]

Depends on / 依赖: Nat.cast_commute, cast_commute, diagonal_kronecker
-/
theorem natCast_kronecker [NonAssocSemiring α] [DecidableEq l] (a : Nat) (B : Matrix m n α) :
    (a : Matrix l l α) otimesₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => a • B) :=
.trans by diagonal_kronecker _ _
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]

/--
theorem `kronecker_ofNat` / 定理 `kronecker_ofNat`

English:
theorem kronecker_ofNat
  statement: [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : Nat)
  proof: kronecker_diagonal _ _

中文:
定理 kronecker_of自然数
  结论: [非结合半环 α] [DecidableEq n] (A : 矩阵 l m α) (b : 自然数)
  证明: kronecker_diagonal _ _

Depends on / 依赖: kronecker_diagonal
-/
theorem kronecker_ofNat [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : Nat)
    [b.AtLeastTwo] : A otimesₖ (ofNat(b) : Matrix n n α) =
      blockDiagonal fun _ => A <• (ofNat(b) : α) :=
  kronecker_diagonal _ _

/--
theorem `ofNat_kronecker` / 定理 `ofNat_kronecker`

English:
theorem ofNat_kronecker
  statement: [NonAssocSemiring α] [DecidableEq l] (a : Nat) [a.AtLeastTwo]
  proof: diagonal_kronecker _ _

中文:
定理 of自然数_kronecker
  结论: [非结合半环 α] [DecidableEq l] (a : 自然数) [a.AtLeastTwo]
  证明: diagonal_kronecker _ _

Depends on / 依赖: diagonal_kronecker
-/
theorem ofNat_kronecker [NonAssocSemiring α] [DecidableEq l] (a : Nat) [a.AtLeastTwo]
    (B : Matrix m n α) : (ofNat(a) : Matrix l l α) otimesₖ B =
      Matrix.reindex (.prodComm _ _) (.prodComm _ _)
        (blockDiagonal fun _ => (ofNat(a) : α) • B) :=
  diagonal_kronecker _ _

/--
theorem `one_kronecker_one` / 定理 `one_kronecker_one`

English:
theorem one_kronecker_one
  given: [MulZeroOneClass α] [DecidableEq m] [DecidableEq n]
  proof: kroneckerMap_one_one _ zero_mul mul_zero (one_mul _)

中文:
定理 one_kronecker_one
  条件: [乘零幺类 α] [DecidableEq m] [DecidableEq n]
  证明: kroneckerMap_one_one _ zero_mul mul_zero (one_mul _)

Depends on / 依赖: kroneckerMap_one_one, mul_zero, one_mul, zero_mul
-/
theorem one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) otimesₖ (1 : Matrix n n α) = 1 :=
  kroneckerMap_one_one _ zero_mul mul_zero (one_mul _)

/--
theorem `kronecker_one` / 定理 `kronecker_one`

English:
theorem kronecker_one
  given: [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α)
  proof: (kronecker_diagonal _ _).trans congr_arg _ funext fun _ => Matrix.ext fun _ _ => mul_one _

中文:
定理 kronecker_one
  条件: [乘零幺类 α] [DecidableEq n] (A : 矩阵 l m α)
  证明: (kronecker_diagonal _ _).trans congr_arg _ funext fun _ => Matrix.ext fun _ _ => mul_one _

Depends on / 依赖: Matrix, Matrix.ext, congr_arg, kronecker_diagonal, mul_one
-/
theorem kronecker_one [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α) :
    A otimesₖ (1 : Matrix n n α) = blockDiagonal fun _ => A :=
(kronecker_diagonal _ _).trans congr_arg _ funext fun _ => Matrix.ext fun _ _ => mul_one _

/--
theorem `one_kronecker` / 定理 `one_kronecker`

English:
theorem one_kronecker
  given: [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α)
  proof: (diagonal_kronecker _ _).trans
congr_arg _ congr_arg _ funext fun _ => Matrix.ext fun _ _ => one_mul _

中文:
定理 one_kronecker
  条件: [乘零幺类 α] [DecidableEq l] (B : 矩阵 m n α)
  证明: (diagonal_kronecker _ _).trans
congr_arg _ congr_arg _ funext fun _ => Matrix.ext fun _ _ => one_mul _

Depends on / 依赖: Matrix, Matrix.ext, congr_arg, diagonal_kronecker, one_mul
-/
theorem one_kronecker [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α) :
    (1 : Matrix l l α) otimesₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => B) :=
(diagonal_kronecker _ _).trans
congr_arg _ congr_arg _ funext fun _ => Matrix.ext fun _ _ => one_mul _

/--
theorem `mul_kronecker_mul` / 定理 `mul_kronecker_mul`

English:
theorem mul_kronecker_mul
  statement: [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l m α)
  proof: kroneckerMapBilinear_mul_mul (Algebra.lmul Nat α).toLinearMap mul_mul_mul_comm A B A' B'

中文:
定理 mul_kronecker_mul
  结论: [有限类型 m] [有限类型 m'] [交换半环 α] (A : 矩阵 l m α)
  证明: kroneckerMapBilinear_mul_mul (Algebra.lmul Nat α).toLinearMap mul_mul_mul_comm A B A' B'

Depends on / 依赖: Algebra, Algebra.lmul, kroneckerMapBilinear_mul_mul, mul_mul_mul_comm, toLinearMap
-/
theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
    (A * B) otimesₖ (A' * B') = A otimesₖ A' * B otimesₖ B' :=
  kroneckerMapBilinear_mul_mul (Algebra.lmul Nat α).toLinearMap mul_mul_mul_comm A B A' B'

-- simp-normal form is `kronecker_assoc'`
/--
theorem `kronecker_assoc` / 定理 `kronecker_assoc`

English:
theorem kronecker_assoc
  given: [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α)
  proof: kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

@[simp]

中文:
定理 kronecker_assoc
  条件: [半群 α] (A : 矩阵 l m α) (B : 矩阵 n p α) (C : 矩阵 q r α)
  证明: kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

@[simp]

Depends on / 依赖: mul_assoc
-/
theorem kronecker_assoc [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (A otimesₖ B otimesₖ C) = A otimesₖ (B otimesₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

@[simp]
/--
theorem `kronecker_assoc'` / 定理 `kronecker_assoc'`

English:
theorem kronecker_assoc'
  given: [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α)
  proof: kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

中文:
定理 kronecker_assoc'
  条件: [半群 α] (A : 矩阵 l m α) (B : 矩阵 n p α) (C : 矩阵 q r α)
  证明: kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

Depends on / 依赖: mul_assoc
-/
theorem kronecker_assoc' [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    submatrix (A otimesₖ B otimesₖ C) (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm =
    A otimesₖ (B otimesₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

/--
theorem `trace_kronecker` / 定理 `trace_kronecker`

English:
theorem trace_kronecker
  given: [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B : Matrix n n α)
  proof: trace_kroneckerMapBilinear (Algebra.lmul Nat α).toLinearMap _ _

中文:
定理 trace_kronecker
  条件: [有限类型 m] [有限类型 n] [半环 α] (A : 矩阵 m m α) (B : 矩阵 n n α)
  证明: trace_kroneckerMapBilinear (Algebra.lmul Nat α).toLinearMap _ _

Depends on / 依赖: Algebra, Algebra.lmul, toLinearMap, trace_kroneckerMapBilinear
-/
theorem trace_kronecker [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B : Matrix n n α) :
    trace (A otimesₖ B) = trace A * trace B :=
  trace_kroneckerMapBilinear (Algebra.lmul Nat α).toLinearMap _ _

/--
theorem `det_kronecker` / 定理 `det_kronecker`

English:
theorem det_kronecker
  statement: [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
  proof: by
  refine (det_kroneckerMapBilinear (Algebra.lmul Nat R).toLinearMap mul_mul_mul_comm _ _).trans ?_
  simp

中文:
定理 det_kronecker
  结论: [有限类型 m] [有限类型 n] [DecidableEq m] [DecidableEq n] [交换环 R]
  证明: by
  refine (det_kroneckerMapBilinear (Algebra.lmul Nat R).toLinearMap mul_mul_mul_comm _ _).trans ?_
  simp

Depends on / 依赖: Algebra, Algebra.lmul, det_kroneckerMapBilinear, mul_mul_mul_comm, toLinearMap
-/
theorem det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) :
    det (A otimesₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m := by
  refine (det_kroneckerMapBilinear (Algebra.lmul Nat R).toLinearMap mul_mul_mul_comm _ _).trans ?_
  simp

/--
theorem `conjTranspose_kronecker` / 定理 `conjTranspose_kronecker`

English:
theorem conjTranspose_kronecker
  given: [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R)
  proof: by
  ext; simp

中文:
定理 conjTranspose_kronecker
  条件: [交换原群 R] [StarMul R] (x : 矩阵 l m R) (y : 矩阵 n p R)
  证明: by
  ext; simp
-/
theorem conjTranspose_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x otimesₖ y)ᴴ = xᴴ otimesₖ yᴴ := by
  ext; simp

/--
theorem `conjTranspose_kronecker'` / 定理 `conjTranspose_kronecker'`

English:
theorem conjTranspose_kronecker'
  given: [Mul R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R)
  proof: by
  ext; simp

中文:
定理 conjTranspose_kronecker'
  条件: [乘法 R] [StarMul R] (x : 矩阵 l m R) (y : 矩阵 n p R)
  证明: by
  ext; simp
-/
theorem conjTranspose_kronecker' [Mul R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x otimesₖ y)ᴴ = (yᴴ otimesₖ xᴴ).submatrix Prod.swap Prod.swap := by
  ext; simp

end Kronecker

/-! ### Specialization to `Matrix.kroneckerMap (⊗ₜ)` -/


section KroneckerTmul

variable (R)

open TensorProduct

open Matrix TensorProduct

section Module

variable [CommSemiring R]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module R β] [Module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kroneckerMap (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp]
/--
Definition of `kroneckerTMul` / `kroneckerTMul` 的定义

English:
definition kroneckerTMul
  signature: : Matrix l m α -> Matrix n p β -> Matrix (l × n) (m × p) (α otimes[R] β)
  body: kroneckerMap (· otimesₜ ·)

@[inherit_doc kroneckerTMul]
scoped[Kronecker] infixl:100 " otimesₖₜ " => Matrix.kroneckerMap (TensorProduct.tmul _)

@[inherit_doc kroneckerTMul] scoped[Kronecker] notation:100 x " otimesₖₜ[" R "] " y:100 =>
  Matrix.kroneckerMap (TensorProduct.tmul R) x y

中文:
定义 kroneckerTMul
  签名: : 矩阵 l m α -> 矩阵 n p β -> 矩阵 (l × n) (m × p) (α otimes[R] β)
  定义体: kroneckerMap (· otimesₜ ·)

@[inherit_doc kroneckerTMul]
scoped[Kronecker] infixl:100 " otimesₖₜ " => Matrix.kroneckerMap (TensorProduct.tmul _)

@[inherit_doc kroneckerTMul] scoped[Kronecker] notation:100 x " otimesₖₜ[" R "] " y:100 =>
  Matrix.kroneckerMap (TensorProduct.tmul R) x y

Depends on / 依赖: kroneckerMap
-/
def kroneckerTMul : Matrix l m α -> Matrix n p β -> Matrix (l × n) (m × p) (α otimes[R] β) :=
  kroneckerMap (· otimesₜ ·)

@[inherit_doc kroneckerTMul]
scoped[Kronecker] infixl:100 " otimesₖₜ " => Matrix.kroneckerMap (TensorProduct.tmul _)

@[inherit_doc kroneckerTMul] scoped[Kronecker] notation:100 x " otimesₖₜ[" R "] " y:100 =>
  Matrix.kroneckerMap (TensorProduct.tmul R) x y

open Kronecker

@[simp]
/--
theorem `kroneckerTMul_apply` / 定理 `kroneckerTMul_apply`

English:
theorem kroneckerTMul_apply
  given: (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂)
  proof: rfl

中文:
定理 kroneckerTMul_apply
  条件: (A : 矩阵 l m α) (B : 矩阵 n p β) (i₁ i₂ j₁ j₂)
  证明: rfl
-/
theorem kroneckerTMul_apply (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂) :
    (A otimesₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ otimesₜ[R] B i₂ j₂ :=
  rfl

variable (S) in
/--
Definition of `kroneckerTMulBilinear` / `kroneckerTMulBilinear` 的定义

English:
definition kroneckerTMulBilinear
  signature: [Semiring S] [Module S α] [SMulCommClass R S α]
  body: kroneckerMapBilinear (AlgebraTensorModule.mk _ _ α β)

@[simp]

中文:
定义 kroneckerTMulBilinear
  签名: [半环 S] [模 S α] [标量交换类 R S α]
  定义体: kroneckerMapBilinear (AlgebraTensorModule.mk _ _ α β)

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.mk, kroneckerMapBilinear
-/
def kroneckerTMulBilinear [Semiring S] [Module S α] [SMulCommClass R S α] :
    Matrix l m α ->ₗ[S] Matrix n p β ->ₗ[R] Matrix (l × n) (m × p) (α otimes[R] β) :=
  kroneckerMapBilinear (AlgebraTensorModule.mk _ _ α β)

@[simp]
/--
theorem `kroneckerTMulBilinear_apply` / 定理 `kroneckerTMulBilinear_apply`

English:
theorem kroneckerTMulBilinear_apply
  statement: [Semiring S] [Module S α] [SMulCommClass R S α]
  proof: rfl

中文:
定理 kroneckerTMulBilinear_apply
  结论: [半环 S] [模 S α] [标量交换类 R S α]
  证明: rfl
-/
theorem kroneckerTMulBilinear_apply [Semiring S] [Module S α] [SMulCommClass R S α]
    (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerTMulBilinear R S A B = A otimesₖₜ[R] B := rfl



/--
theorem `zero_kroneckerTMul` / 定理 `zero_kroneckerTMul`

English:
theorem zero_kroneckerTMul
  given: (B : Matrix n p β)
  statement: (0 : Matrix l m α) otimesₖₜ[R] B = 0
  proof: kroneckerMap_zero_left _ (zero_tmul α) B

中文:
定理 zero_kroneckerTMul
  条件: (B : 矩阵 n p β)
  结论: (0 : 矩阵 l m α) otimesₖₜ[R] B = 0
  证明: kroneckerMap_zero_left _ (zero_tmul α) B

Depends on / 依赖: kroneckerMap_zero_left, zero_tmul
-/
theorem zero_kroneckerTMul (B : Matrix n p β) : (0 : Matrix l m α) otimesₖₜ[R] B = 0 :=
  kroneckerMap_zero_left _ (zero_tmul α) B

/--
theorem `kroneckerTMul_zero` / 定理 `kroneckerTMul_zero`

English:
theorem kroneckerTMul_zero
  given: (A : Matrix l m α)
  statement: A otimesₖₜ[R] (0 : Matrix n p β) = 0
  proof: kroneckerMap_zero_right _ (tmul_zero β) A

中文:
定理 kroneckerTMul_zero
  条件: (A : 矩阵 l m α)
  结论: A otimesₖₜ[R] (0 : 矩阵 n p β) = 0
  证明: kroneckerMap_zero_right _ (tmul_zero β) A

Depends on / 依赖: kroneckerMap_zero_right, tmul_zero
-/
theorem kroneckerTMul_zero (A : Matrix l m α) : A otimesₖₜ[R] (0 : Matrix n p β) = 0 :=
  kroneckerMap_zero_right _ (tmul_zero β) A

/--
theorem `add_kroneckerTMul` / 定理 `add_kroneckerTMul`

English:
theorem add_kroneckerTMul
  given: (A₁ A₂ : Matrix l m α) (B : Matrix n p α)
  proof: kroneckerMap_add_left _ add_tmul _ _ _

中文:
定理 add_kroneckerTMul
  条件: (A₁ A₂ : 矩阵 l m α) (B : 矩阵 n p α)
  证明: kroneckerMap_add_left _ add_tmul _ _ _

Depends on / 依赖: add_tmul, kroneckerMap_add_left
-/
theorem add_kroneckerTMul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) otimesₖₜ[R] B = A₁ otimesₖₜ B + A₂ otimesₖₜ B :=
  kroneckerMap_add_left _ add_tmul _ _ _

/--
theorem `kroneckerTMul_add` / 定理 `kroneckerTMul_add`

English:
theorem kroneckerTMul_add
  given: (A : Matrix l m α) (B₁ B₂ : Matrix n p β)
  proof: kroneckerMap_add_right _ tmul_add _ _ _

中文:
定理 kroneckerTMul_add
  条件: (A : 矩阵 l m α) (B₁ B₂ : 矩阵 n p β)
  证明: kroneckerMap_add_right _ tmul_add _ _ _

Depends on / 依赖: kroneckerMap_add_right, tmul_add
-/
theorem kroneckerTMul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    A otimesₖₜ[R] (B₁ + B₂) = A otimesₖₜ B₁ + A otimesₖₜ B₂ :=
  kroneckerMap_add_right _ tmul_add _ _ _

/--
theorem `smul_kroneckerTMul` / 定理 `smul_kroneckerTMul`

English:
theorem smul_kroneckerTMul
  statement: [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
  proof: kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

中文:
定理 smul_kroneckerTMul
  结论: [幺半群 S] [分配乘法作用 S α] [标量交换类 R S α]
  证明: kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

Depends on / 依赖: kroneckerMap_smul_left, smul_tmul
-/
theorem smul_kroneckerTMul [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    (r • A) otimesₖₜ[R] B = r • A otimesₖₜ[R] B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

/--
theorem `kroneckerTMul_smul` / 定理 `kroneckerTMul_smul`

English:
theorem kroneckerTMul_smul
  statement: [Monoid S] [DistribMulAction S α] [DistribMulAction S β]
  proof: kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

中文:
定理 kroneckerTMul_smul
  结论: [幺半群 S] [分配乘法作用 S α] [分配乘法作用 S β]
  证明: kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

Depends on / 依赖: kroneckerMap_smul_right, tmul_smul
-/
theorem kroneckerTMul_smul [Monoid S] [DistribMulAction S α] [DistribMulAction S β]
    [SMul S R] [SMulCommClass R S α] [IsScalarTower S R α] [IsScalarTower S R β]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    A otimesₖₜ[R] (r • B) = r • A otimesₖₜ[R] B :=
  kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

/--
theorem `single_kroneckerTMul_single` / 定理 `single_kroneckerTMul_single`

English:
theorem single_kroneckerTMul_single
  proof: kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _

中文:
定理 single_kroneckerTMul_single
  证明: kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _

Depends on / 依赖: kroneckerMap_single_single, tmul_zero, zero_tmul
-/
theorem single_kroneckerTMul_single
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) (a : α) (b : β) :
    single i₁ j₁ a otimesₖₜ[R] single i₂ j₂ b = single (i₁, i₂) (j₁, j₂) (a otimesₜ b) :=
  kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _

/--
theorem `diagonal_kroneckerTMul_diagonal` / 定理 `diagonal_kroneckerTMul_diagonal`

English:
theorem diagonal_kroneckerTMul_diagonal
  given: [DecidableEq m] [DecidableEq n] (a : m -> α) (b : n -> β)
  proof: kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

中文:
定理 diagonal_kroneckerTMul_diagonal
  条件: [DecidableEq m] [DecidableEq n] (a : m -> α) (b : n -> β)
  证明: kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

Depends on / 依赖: kroneckerMap_diagonal_diagonal, tmul_zero, zero_tmul
-/
theorem diagonal_kroneckerTMul_diagonal [DecidableEq m] [DecidableEq n] (a : m -> α) (b : n -> β) :
    diagonal a otimesₖₜ[R] diagonal b = diagonal fun mn => a mn.1 otimesₜ b mn.2 :=
  kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

/--
theorem `kroneckerTMul_diagonal` / 定理 `kroneckerTMul_diagonal`

English:
theorem kroneckerTMul_diagonal
  given: [DecidableEq n] (A : Matrix l m α) (b : n -> β)
  proof: kroneckerMap_diagonal_right _ (tmul_zero _) _ _

中文:
定理 kroneckerTMul_diagonal
  条件: [DecidableEq n] (A : 矩阵 l m α) (b : n -> β)
  证明: kroneckerMap_diagonal_right _ (tmul_zero _) _ _

Depends on / 依赖: kroneckerMap_diagonal_right, tmul_zero
-/
theorem kroneckerTMul_diagonal [DecidableEq n] (A : Matrix l m α) (b : n -> β) :
    A otimesₖₜ[R] diagonal b = blockDiagonal fun i => A.map fun a => a otimesₜ[R] b i :=
  kroneckerMap_diagonal_right _ (tmul_zero _) _ _

/--
theorem `diagonal_kroneckerTMul` / 定理 `diagonal_kroneckerTMul`

English:
theorem diagonal_kroneckerTMul
  given: [DecidableEq l] (a : l -> α) (B : Matrix m n β)
  proof: kroneckerMap_diagonal_left _ (zero_tmul _) _ _

中文:
定理 diagonal_kroneckerTMul
  条件: [DecidableEq l] (a : l -> α) (B : 矩阵 m n β)
  证明: kroneckerMap_diagonal_left _ (zero_tmul _) _ _

Depends on / 依赖: kroneckerMap_diagonal_left, zero_tmul
-/
theorem diagonal_kroneckerTMul [DecidableEq l] (a : l -> α) (B : Matrix m n β) :
    diagonal a otimesₖₜ[R] B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => a i otimesₜ[R] b) :=
  kroneckerMap_diagonal_left _ (zero_tmul _) _ _

-- simp-normal form is `kroneckerTMul_assoc'`
/--
theorem `kroneckerTMul_assoc` / 定理 `kroneckerTMul_assoc`

English:
theorem kroneckerTMul_assoc
  given: (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ)
  proof: ext fun _ _ => assoc_tmul _ _ _

@[simp]

中文:
定理 kroneckerTMul_assoc
  条件: (A : 矩阵 l m α) (B : 矩阵 n p β) (C : 矩阵 q r γ)
  证明: ext fun _ _ => assoc_tmul _ _ _

@[simp]

Depends on / 依赖: assoc_tmul
-/
theorem kroneckerTMul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (((A otimesₖₜ[R] B) otimesₖₜ[R] C).map (TensorProduct.assoc R α β γ)) =
      A otimesₖₜ[R] B otimesₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _

@[simp]
/--
theorem `kroneckerTMul_assoc'` / 定理 `kroneckerTMul_assoc'`

English:
theorem kroneckerTMul_assoc'
  given: (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ)
  proof: ext fun _ _ => assoc_tmul _ _ _

中文:
定理 kroneckerTMul_assoc'
  条件: (A : 矩阵 l m α) (B : 矩阵 n p β) (C : 矩阵 q r γ)
  证明: ext fun _ _ => assoc_tmul _ _ _

Depends on / 依赖: assoc_tmul
-/
theorem kroneckerTMul_assoc' (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    submatrix (((A otimesₖₜ[R] B) otimesₖₜ[R] C).map (TensorProduct.assoc R α β γ))
      (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm = A otimesₖₜ[R] B otimesₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _

/--
theorem `trace_kroneckerTMul` / 定理 `trace_kroneckerTMul`

English:
theorem trace_kroneckerTMul
  given: [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix n n β)
  proof: trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _

中文:
定理 trace_kroneckerTMul
  条件: [有限类型 m] [有限类型 n] (A : 矩阵 m m α) (B : 矩阵 n n β)
  证明: trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _

Depends on / 依赖: TensorProduct, TensorProduct.mk, trace_kroneckerMapBilinear
-/
theorem trace_kroneckerTMul [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix n n β) :
    trace (A otimesₖₜ[R] B) = trace A otimesₜ[R] trace B :=
  trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _

/--
theorem `conjTranspose_kroneckerTMul` / 定理 `conjTranspose_kroneckerTMul`

English:
theorem conjTranspose_kroneckerTMul
  statement: [StarRing R] [StarAddMonoid α] [StarAddMonoid β]
  proof: by
  ext; simp

中文:
定理 conjTranspose_kroneckerTMul
  结论: [对合环 R] [StarAdd幺半群 α] [StarAdd幺半群 β]
  证明: by
  ext; simp
-/
theorem conjTranspose_kroneckerTMul [StarRing R] [StarAddMonoid α] [StarAddMonoid β]
    [StarModule R α] [StarModule R β] (x : Matrix l m α) (y : Matrix n p β) :
    (x otimesₖₜ[R] y)ᴴ = xᴴ otimesₖₜ[R] yᴴ := by
  ext; simp

end Module

section Algebra

open Kronecker

open Algebra.TensorProduct

section Semiring
variable [CommSemiring R]

@[simp]
/--
theorem `one_kroneckerTMul_one` / 定理 `one_kroneckerTMul_one`

English:
theorem one_kroneckerTMul_one
  proof: kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in

中文:
定理 one_kroneckerTMul_one
  证明: kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in

Depends on / 依赖: kroneckerMap_one_one, tmul_zero, zero_tmul
-/
theorem one_kroneckerTMul_one
    [AddCommMonoidWithOne α] [AddCommMonoidWithOne β] [Module R α] [Module R β]
    [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) otimesₖₜ[R] (1 : Matrix n n β) = 1 :=
  kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in
/--
theorem `mul_kroneckerTMul_mul` / 定理 `mul_kroneckerTMul_mul`

English:
theorem mul_kroneckerTMul_mul
  proof: kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

中文:
定理 mul_kroneckerTMul_mul
  证明: kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

Depends on / 依赖: TensorProduct, TensorProduct.mk, kroneckerMapBilinear_mul_mul, tmul_mul_tmul
-/
theorem mul_kroneckerTMul_mul
    [NonUnitalSemiring α] [NonUnitalSemiring β] [Module R α] [Module R β]
    [IsScalarTower R α α] [SMulCommClass R α α] [IsScalarTower R β β] [SMulCommClass R β β]
    [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    (A * B) otimesₖₜ[R] (A' * B') = A otimesₖₜ[R] A' * B otimesₖₜ[R] B' :=
  kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

end Semiring

section CommRing

variable [CommRing R] [CommRing α] [CommRing β] [Algebra R α] [Algebra R β]

unseal mul in
/--
theorem `det_kroneckerTMul` / 定理 `det_kroneckerTMul`

English:
theorem det_kroneckerTMul
  statement: [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  proof: by
  refine (det_kroneckerMapBilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans ?_
  simp -eta only [mk_apply, ← includeLeft_apply (S := R), ← includeRight_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [includeLeft_apply, includeRight_apply, tmul_pow, tmul_mul_t

中文:
定理 det_kroneckerTMul
  结论: [有限类型 m] [有限类型 n] [DecidableEq m] [DecidableEq n]
  证明: by
  refine (det_kroneckerMapBilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans ?_
  simp -eta only [mk_apply, ← includeLeft_apply (S := R), ← includeRight_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [includeLeft_apply, includeRight_apply, tmul_pow, tmul_mul_t

Depends on / 依赖: AlgHom, AlgHom.mapMatrix_apply, AlgHom.map_det, TensorProduct, TensorProduct.mk, _root_, _root_.mul_one, _root_.one_mul, det_kroneckerMapBilinear, includeLeft_apply, includeRight_apply, mapMatrix_apply, map_det, mk_apply, mul_one, one_mul, one_pow, tmul_mul_tmul, tmul_pow
-/
theorem det_kroneckerTMul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix n n β) :
    det (A otimesₖₜ[R] B) = (det A ^ Fintype.card n) otimesₜ[R] (det B ^ Fintype.card m) := by
  refine (det_kroneckerMapBilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans ?_
  simp -eta only [mk_apply, ← includeLeft_apply (S := R), ← includeRight_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [includeLeft_apply, includeRight_apply, tmul_pow, tmul_mul_tmul, one_pow,
    _root_.mul_one, _root_.one_mul]

end CommRing

end Algebra

-- insert lemmas specific to `kroneckerTMul` below this line
end KroneckerTmul

end Matrix
