/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.PEquiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `PEquiv.toMatrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.toMatrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`toMatrix_trans : (f.trans g).toMatrix = f.toMatrix * g.toMatrix`
`toMatrix_symm : f.symm.toMatrix = f.toMatrixᵀ`
`toMatrix_refl : (PEquiv.refl n).toMatrix = 1`
`toMatrix_bot : ⊥.toMatrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : Fin 1) (i : Fin n)).toMatrix` corresponds to the ith
projection map from R^n to R.

Any injective function `Fin m → Fin n` gives rise to a `PEquiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## Notation

This file uses `ᵀ` for `Matrix.transpose`.
-/

@[expose] public section

assert_not_exists Field

namespace PEquiv

open Matrix

universe u v

variable {k l m n : Type*}
variable {α β : Type*}

open Matrix

/--
Definition of `toMatrix` / `toMatrix` 的定义

English:
definition toMatrix
  signature: [DecidableEq n] [Zero α] [One α] (f : m ≃. n)
  body: of fun i j => if j in f i then (1 : α) else 0

中文:
定义 toMatrix
  签名: [DecidableEq n] [零 α] [幺 α] (f : m ≃. n)
  定义体: of fun i j => if j in f i then (1 : α) else 0
-/
def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α :=
  of fun i j => if j in f i then (1 : α) else 0

-- TODO: set as an equation lemma for `toMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `toMatrix_apply` / 定理 `toMatrix_apply`

English:
theorem toMatrix_apply
  given: [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j)
  proof: rfl

中文:
定理 toMatrix_apply
  条件: [DecidableEq n] [零 α] [幺 α] (f : m ≃. n) (i j)
  证明: rfl
-/
theorem toMatrix_apply [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j) :
    toMatrix f i j = if j in f i then (1 : α) else 0 :=
  rfl

/--
theorem `toMatrix_mul_apply` / 定理 `toMatrix_mul_apply`

English:
theorem toMatrix_mul_apply
  statement: [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f : l ≃. m) (i j)
  proof: by
  dsimp [toMatrix, Matrix.mul_apply]
  rcases h : f i with - | fi
  · simp
  · rw [Finset.sum_eq_single fi] <;> simp +contextual [eq_comm]

中文:
定理 toMatrix_mul_apply
  结论: [有限类型 m] [DecidableEq m] [非结合半环 α] (f : l ≃. m) (i j)
  证明: by
  dsimp [toMatrix, Matrix.mul_apply]
  rcases h : f i with - | fi
  · simp
  · rw [Finset.sum_eq_single fi] <;> simp +contextual [eq_comm]

Depends on / 依赖: Finset, Finset.sum_eq_single, Matrix, Matrix.mul_apply, contextual, eq_comm, mul_apply, sum_eq_single, toMatrix
-/
theorem toMatrix_mul_apply [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f : l ≃. m) (i j)
    (M : Matrix m n α) : (f.toMatrix * M :) i j = Option.casesOn (f i) 0 fun fi => M fi j := by
  dsimp [toMatrix, Matrix.mul_apply]
  rcases h : f i with - | fi
  · simp
  · rw [Finset.sum_eq_single fi] <;> simp +contextual [eq_comm]

/--
theorem `mul_toMatrix_apply` / 定理 `mul_toMatrix_apply`

English:
theorem mul_toMatrix_apply
  statement: [Fintype m] [NonAssocSemiring α] [DecidableEq n] (M : Matrix l m α)
  proof: by
  dsimp [Matrix.mul_apply, toMatrix_apply]
  rcases h : f.symm j with - | fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · rintro b - n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp

中文:
定理 mul_toMatrix_apply
  结论: [有限类型 m] [非结合半环 α] [DecidableEq n] (M : 矩阵 l m α)
  证明: by
  dsimp [Matrix.mul_apply, toMatrix_apply]
  rcases h : f.symm j with - | fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · rintro b - n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp

Depends on / 依赖: Finset, Finset.sum_eq_single, Matrix, Matrix.mul_apply, eq_some_iff, f.eq_some_iff, f.symm, mul_apply, n.symm, sum_eq_single, toMatrix_apply
-/
theorem mul_toMatrix_apply [Fintype m] [NonAssocSemiring α] [DecidableEq n] (M : Matrix l m α)
    (f : m ≃. n) (i j) : (M * f.toMatrix :) i j = Option.casesOn (f.symm j) 0 (M i) := by
  dsimp [Matrix.mul_apply, toMatrix_apply]
  rcases h : f.symm j with - | fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · rintro b - n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp

/--
theorem `toMatrix_symm` / 定理 `toMatrix_symm`

English:
theorem toMatrix_symm
  given: [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n)
  proof: by
  ext
  simp only [transpose, mem_iff_mem f, toMatrix_apply]
  congr

@[simp]

中文:
定理 toMatrix_symm
  条件: [DecidableEq m] [DecidableEq n] [零 α] [幺 α] (f : m ≃. n)
  证明: by
  ext
  simp only [transpose, mem_iff_mem f, toMatrix_apply]
  congr

@[simp]

Depends on / 依赖: mem_iff_mem, toMatrix_apply, transpose
-/
theorem toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n) :
    (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ := by
  ext
  simp only [transpose, mem_iff_mem f, toMatrix_apply]
  congr

@[simp]
/--
theorem `toMatrix_refl` / 定理 `toMatrix_refl`

English:
theorem toMatrix_refl
  given: [DecidableEq n] [Zero α] [One α]
  proof: by
  ext
  simp [toMatrix_apply, one_apply]

@[simp]

中文:
定理 toMatrix_refl
  条件: [DecidableEq n] [零 α] [幺 α]
  证明: by
  ext
  simp [toMatrix_apply, one_apply]

@[simp]

Depends on / 依赖: one_apply, toMatrix_apply
-/
theorem toMatrix_refl [DecidableEq n] [Zero α] [One α] :
    ((PEquiv.refl n).toMatrix : Matrix n n α) = 1 := by
  ext
  simp [toMatrix_apply, one_apply]

@[simp]
/--
theorem `toMatrix_toPEquiv_apply` / 定理 `toMatrix_toPEquiv_apply`

English:
theorem toMatrix_toPEquiv_apply
  given: [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (i)
  proof: by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm]

@[simp]

中文:
定理 toMatrix_toPEquiv_apply
  条件: [DecidableEq n] [零 α] [幺 α] (f : m ≃ n) (i)
  证明: by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm]

@[simp]

Depends on / 依赖: Pi.single_apply, eq_comm, single_apply, toMatrix_apply
-/
theorem toMatrix_toPEquiv_apply [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (i) :
    f.toPEquiv.toMatrix i = Pi.single (f i) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm]

@[simp]
/--
theorem `transpose_toMatrix_toPEquiv_apply` / 定理 `transpose_toMatrix_toPEquiv_apply`

English:
theorem transpose_toMatrix_toPEquiv_apply
  proof: by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

中文:
定理 transpose_toMatrix_toPEquiv_apply
  证明: by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

Depends on / 依赖: Equiv.eq_symm_apply, Pi.single_apply, eq_comm, eq_symm_apply, single_apply, toMatrix_apply
-/
theorem transpose_toMatrix_toPEquiv_apply
    [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (j) :
    f.toPEquiv.toMatrixᵀ j = Pi.single (f.symm j) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

/--
theorem `toMatrix_toPEquiv_mul` / 定理 `toMatrix_toPEquiv_mul`

English:
theorem toMatrix_toPEquiv_mul
  statement: [Fintype m] [DecidableEq m]
  proof: by
  ext i j
  rw [toMatrix_mul_apply]; rw [Equiv.toPEquiv_apply]; rw [submatrix_apply]; rw [id]

中文:
定理 toMatrix_toPEquiv_mul
  结论: [有限类型 m] [DecidableEq m]
  证明: by
  ext i j
  rw [toMatrix_mul_apply]; rw [Equiv.toPEquiv_apply]; rw [submatrix_apply]; rw [id]

Depends on / 依赖: Equiv.toPEquiv_apply, submatrix_apply, toMatrix_mul_apply, toPEquiv_apply
-/
theorem toMatrix_toPEquiv_mul [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) :
    f.toPEquiv.toMatrix * M = M.submatrix f id := by
  ext i j
  rw [toMatrix_mul_apply]; rw [Equiv.toPEquiv_apply]; rw [submatrix_apply]; rw [id]

/--
theorem `mul_toMatrix_toPEquiv` / 定理 `mul_toMatrix_toPEquiv`

English:
theorem mul_toMatrix_toPEquiv
  statement: [Fintype m] [DecidableEq n]
  proof: Matrix.ext fun i j => by
    rw [PEquiv.mul_toMatrix_apply]; rw [← Equiv.toPEquiv_symm]; rw [Equiv.toPEquiv_apply]; rw [Matrix.submatrix_apply]; rw [id]

中文:
定理 mul_toMatrix_toPEquiv
  结论: [有限类型 m] [DecidableEq n]
  证明: Matrix.ext fun i j => by
    rw [PEquiv.mul_toMatrix_apply]; rw [← Equiv.toPEquiv_symm]; rw [Equiv.toPEquiv_apply]; rw [Matrix.submatrix_apply]; rw [id]

Depends on / 依赖: Equiv.toPEquiv_apply, Equiv.toPEquiv_symm, Matrix, Matrix.ext, Matrix.submatrix_apply, PEquiv, PEquiv.mul_toMatrix_apply, mul_toMatrix_apply, submatrix_apply, toPEquiv_apply, toPEquiv_symm
-/
theorem mul_toMatrix_toPEquiv [Fintype m] [DecidableEq n]
    [NonAssocSemiring α] (M : Matrix l m α) (f : m ≃ n) :
    (M * f.toPEquiv.toMatrix) = M.submatrix id f.symm :=
  Matrix.ext fun i j => by
    rw [PEquiv.mul_toMatrix_apply]; rw [← Equiv.toPEquiv_symm]; rw [Equiv.toPEquiv_apply]; rw [Matrix.submatrix_apply]; rw [id]

/--
lemma `toMatrix_toPEquiv_mulVec` / 引理 `toMatrix_toPEquiv_mulVec`

English:
lemma toMatrix_toPEquiv_mulVec
  statement: [DecidableEq n] [Fintype n]
  proof: by
  ext j
  simp [toMatrix, mulVec, dotProduct]

中文:
引理 toMatrix_toPEquiv_mulVec
  结论: [DecidableEq n] [有限类型 n]
  证明: by
  ext j
  simp [toMatrix, mulVec, dotProduct]

Depends on / 依赖: dotProduct, mulVec, toMatrix
-/
lemma toMatrix_toPEquiv_mulVec [DecidableEq n] [Fintype n]
    [NonAssocSemiring α] (σ : m ≃ n) (a : n -> α) :
    σ.toPEquiv.toMatrix *ᵥ a = a ∘ σ := by
  ext j
  simp [toMatrix, mulVec, dotProduct]

/--
lemma `vecMul_toMatrix_toPEquiv` / 引理 `vecMul_toMatrix_toPEquiv`

English:
lemma vecMul_toMatrix_toPEquiv
  statement: [DecidableEq n] [Fintype m]
  proof: by
  classical
  ext j
  simp [toMatrix, ← σ.eq_symm_apply, vecMul, dotProduct]

中文:
引理 vecMul_toMatrix_toPEquiv
  结论: [DecidableEq n] [有限类型 m]
  证明: by
  classical
  ext j
  simp [toMatrix, ← σ.eq_symm_apply, vecMul, dotProduct]

Depends on / 依赖: classical, dotProduct, eq_symm_apply, toMatrix, vecMul
-/
lemma vecMul_toMatrix_toPEquiv [DecidableEq n] [Fintype m]
    [NonAssocSemiring α] (σ : m ≃ n) (a : m -> α) :
    a ᵥ* σ.toPEquiv.toMatrix = a ∘ σ.symm := by
  classical
  ext j
  simp [toMatrix, ← σ.eq_symm_apply, vecMul, dotProduct]

/--
theorem `toMatrix_trans` / 定理 `toMatrix_trans`

English:
theorem toMatrix_trans
  statement: [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring α] (f : l ≃. m)
  proof: by
  ext i j
  rw [toMatrix_mul_apply]
  dsimp +instances [toMatrix, PEquiv.trans]
  cases f i <;> simp

@[simp]

中文:
定理 toMatrix_trans
  结论: [有限类型 m] [DecidableEq m] [DecidableEq n] [非结合半环 α] (f : l ≃. m)
  证明: by
  ext i j
  rw [toMatrix_mul_apply]
  dsimp +instances [toMatrix, PEquiv.trans]
  cases f i <;> simp

@[simp]

Depends on / 依赖: PEquiv, PEquiv.trans, instances, toMatrix, toMatrix_mul_apply
-/
theorem toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring α] (f : l ≃. m)
    (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMatrix * g.toMatrix := by
  ext i j
  rw [toMatrix_mul_apply]
  dsimp +instances [toMatrix, PEquiv.trans]
  cases f i <;> simp

@[simp]
/--
theorem `toMatrix_bot` / 定理 `toMatrix_bot`

English:
theorem toMatrix_bot
  given: [DecidableEq n] [Zero α] [One α]
  proof: rfl

中文:
定理 toMatrix_bot
  条件: [DecidableEq n] [零 α] [幺 α]
  证明: rfl
-/
theorem toMatrix_bot [DecidableEq n] [Zero α] [One α] :
    ((⊥ : PEquiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl

/--
theorem `toMatrix_injective` / 定理 `toMatrix_injective`

English:
theorem toMatrix_injective
  given: [DecidableEq n] [MulZeroOneClass α] [Nontrivial α]
  proof: by
  intro f g
  refine not_imp_not.1 ?_
  simp only [Matrix.ext_iff.symm, toMatrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
  intro i hi
  use i
  rcases hf : f i with - | fi
  · rcases hg : g i with - | gi
    · rw [hf, hg] at hi; exact (hi rfl).elim
    · use gi
      simp
  · use fi
    simp [hf.symm, Ne.symm hi]

中文:
定理 toMatrix_injective
  条件: [DecidableEq n] [乘零幺类 α] [非平凡 α]
  证明: by
  intro f g
  refine not_imp_not.1 ?_
  simp only [Matrix.ext_iff.symm, toMatrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
  intro i hi
  use i
  rcases hf : f i with - | fi
  · rcases hg : g i with - | gi
    · rw [hf, hg] at hi; exact (hi rfl).elim
    · use gi
      simp
  · use fi
    simp [hf.symm, Ne.symm hi]

Depends on / 依赖: Matrix, Matrix.ext_iff.symm, Ne.symm, PEquiv, PEquiv.ext_iff, exists_imp, ext_iff, hf.symm, not_forall, not_imp_not, toMatrix_apply
-/
theorem toMatrix_injective [DecidableEq n] [MulZeroOneClass α] [Nontrivial α] :
    Function.Injective (@toMatrix m n α _ _ _) := by
  intro f g
  refine not_imp_not.1 ?_
  simp only [Matrix.ext_iff.symm, toMatrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
  intro i hi
  use i
  rcases hf : f i with - | fi
  · rcases hg : g i with - | gi
    · rw [hf, hg] at hi; exact (hi rfl).elim
    · use gi
      simp
  · use fi
    simp [hf.symm, Ne.symm hi]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toMatrix_swap` / 定理 `toMatrix_swap`

English:
theorem toMatrix_swap
  given: [DecidableEq n] [AddGroupWithOne α] (i j : n)
  proof: by
  ext
  dsimp [toMatrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

@[simp]

中文:
定理 toMatrix_swap
  条件: [DecidableEq n] [加法带幺群 α] (i j : n)
  证明: by
  ext
  dsimp [toMatrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: Equiv.swap_apply_def, Equiv.toPEquiv, Matrix, Matrix.one_apply, one_apply, single, split_ifs, swap_apply_def, toMatrix, toPEquiv
-/
theorem toMatrix_swap [DecidableEq n] [AddGroupWithOne α] (i j : n) :
    (Equiv.swap i j).toPEquiv.toMatrix =
      (1 : Matrix n n α) - (single i i).toMatrix - (single j j).toMatrix + (single i j).toMatrix +
        (single j i).toMatrix := by
  ext
  dsimp [toMatrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

@[simp]
/--
theorem `single_mul_single` / 定理 `single_mul_single`

English:
theorem single_mul_single
  statement: [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n]
  proof: by
  rw [← toMatrix_trans]; rw [single_trans_single]

中文:
定理 single_mul_single
  结论: [有限类型 n] [DecidableEq k] [DecidableEq m] [DecidableEq n]
  证明: by
  rw [← toMatrix_trans]; rw [single_trans_single]

Depends on / 依赖: single_trans_single, toMatrix_trans
-/
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring α] (a : m) (b : n) (c : k) :
    ((single a b).toMatrix : Matrix _ _ α) * (single b c).toMatrix = (single a c).toMatrix := by
  rw [← toMatrix_trans]; rw [single_trans_single]

/--
theorem `single_mul_single_of_ne` / 定理 `single_mul_single_of_ne`

English:
theorem single_mul_single_of_ne
  statement: [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
  proof: by
  rw [← toMatrix_trans]; rw [single_trans_single_of_ne hb]; rw [toMatrix_bot]

中文:
定理 single_mul_single_of_ne
  结论: [有限类型 n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
  证明: by
  rw [← toMatrix_trans]; rw [single_trans_single_of_ne hb]; rw [toMatrix_bot]

Depends on / 依赖: single_trans_single_of_ne, toMatrix_bot, toMatrix_trans
-/
theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    [NonAssocSemiring α] {b₁ b₂ : n} (hb : b₁ != b₂) (a : m) (c : k) :
    (single a b₁).toMatrix * (single b₂ c).toMatrix = (0 : Matrix _ _ α) := by
  rw [← toMatrix_trans]; rw [single_trans_single_of_ne hb]; rw [toMatrix_bot]

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
/--
theorem `single_mul_single_right` / 定理 `single_mul_single_right`

English:
theorem single_mul_single_right
  statement: [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
  proof: by
  rw [← Matrix.mul_assoc]; rw [single_mul_single]

中文:
定理 single_mul_single_right
  结论: [有限类型 n] [有限类型 k] [DecidableEq n] [DecidableEq k]
  证明: by
  rw [← Matrix.mul_assoc]; rw [single_mul_single]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, single_mul_single
-/
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) :
    (single a b).toMatrix * ((single b c).toMatrix * M) = (single a c).toMatrix * M := by
  rw [← Matrix.mul_assoc]; rw [single_mul_single]

/--
theorem `toMatrix_toPEquiv_eq` / 定理 `toMatrix_toPEquiv_eq`

English:
theorem toMatrix_toPEquiv_eq
  given: [DecidableEq n] [Zero α] [One α] (σ : Equiv.Perm n)
  proof: Matrix.ext fun _ _ => if_congr Option.some_inj rfl rfl

@[simp]

中文:
定理 toMatrix_toPEquiv_eq
  条件: [DecidableEq n] [零 α] [幺 α] (σ : 等价.置换 n)
  证明: Matrix.ext fun _ _ => if_congr Option.some_inj rfl rfl

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, Option.some_inj, if_congr, some_inj
-/
theorem toMatrix_toPEquiv_eq [DecidableEq n] [Zero α] [One α] (σ : Equiv.Perm n) :
    σ.toPEquiv.toMatrix = (1 : Matrix n n α).submatrix σ id :=
  Matrix.ext fun _ _ => if_congr Option.some_inj rfl rfl

@[simp]
/--
lemma `map_toMatrix` / 引理 `map_toMatrix`

English:
lemma map_toMatrix
  statement: [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β]
  proof: by
  ext i j
  simp

中文:
引理 map_toMatrix
  结论: [DecidableEq n] [非结合半环 α] [非结合半环 β]
  证明: by
  ext i j
  simp
-/
lemma map_toMatrix [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α ->+* β) (σ : m ≃. n) : σ.toMatrix.map f = σ.toMatrix := by
  ext i j
  simp

end PEquiv
