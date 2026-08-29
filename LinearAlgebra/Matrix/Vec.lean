/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Vectorization of matrices

This file defines `Matrix.vec A`, the vectorization of a matrix `A`,
formed by stacking the columns of A into a single large column vector.

Since mathlib indices matrices by arbitrary types rather than `Fin n`,
the result of `Matrix.vec` on `A : Matrix m n R` is indexed by `n × m`.
The `Fin (n * m)` interpretation can be restored by composing with `finProdFinEquiv.symm`:
```lean
-- ![1, 2, 3, 4]
#eval vec !![1, 3; 2, 4] ∘ finProdFinEquiv.symm
```

While it may seem more natural to index by `m × n`, keeping the indices in the same order,
this would amount to stacking the rows into one long row, and goes against the literature.
If you want this function, you can write `Matrix.vec Aᵀ` instead.

### References

* [Wikipedia](https://en.wikipedia.org/wiki/Vectorization_(mathematics))
-/

@[expose] public section
namespace Matrix

variable {ι l m n p R S}

/-- All the matrix entries, arranged into one column. -/
@[simp]
/--
Definition of `vec` / `vec` 的定义

English:
definition vec
  signature: (A : Matrix m n R)
  body: fun ij => A ij.2 ij.1

@[simp]

中文:
定义 vec
  签名: (A : 矩阵 m n R)
  定义体: fun ij => A ij.2 ij.1

@[simp]
-/
def vec (A : Matrix m n R) : n × m -> R :=
  fun ij => A ij.2 ij.1

@[simp]
/--
theorem `vec_of` / 定理 `vec_of`

English:
theorem vec_of
  given: (f : m -> n -> R)
  statement: vec (of f) = Function.uncurry (flip f)
  proof: rfl

中文:
定理 vec_of
  条件: (f : m -> n -> R)
  结论: vec (of f) = 函数.uncurry (flip f)
  证明: rfl
-/
theorem vec_of (f : m -> n -> R) : vec (of f) = Function.uncurry (flip f) := rfl

/--
theorem `vec_transpose` / 定理 `vec_transpose`

English:
theorem vec_transpose
  given: (A : Matrix m n R)
  statement: vec Aᵀ = vec A ∘ Prod.swap
  proof: rfl

中文:
定理 vec_transpose
  条件: (A : 矩阵 m n R)
  结论: vec Aᵀ = vec A ∘ 积类型.swap
  证明: rfl
-/
theorem vec_transpose (A : Matrix m n R) : vec Aᵀ = vec A ∘ Prod.swap := rfl

/--
theorem `vec_eq_uncurry` / 定理 `vec_eq_uncurry`

English:
theorem vec_eq_uncurry
  given: (A : Matrix m n R)
  statement: vec A = Function.uncurry fun i j => A j i
  proof: rfl

中文:
定理 vec_eq_uncurry
  条件: (A : 矩阵 m n R)
  结论: vec A = 函数.uncurry fun i j => A j i
  证明: rfl
-/
theorem vec_eq_uncurry (A : Matrix m n R) : vec A = Function.uncurry fun i j => A j i := rfl

/--
theorem `vec_inj` / 定理 `vec_inj`

English:
theorem vec_inj
  given: {A B : Matrix m n R}
  statement: A.vec = B.vec ↔ A = B
  proof: by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]

中文:
定理 vec_inj
  条件: {A B : 矩阵 m n R}
  结论: A.vec = B.vec ↔ A = B
  证明: by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]

Depends on / 依赖: Matrix, Matrix.ext_iff, Prod.forall, ext_iff, forall_comm, funext_iff, simp_rw
-/
theorem vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B := by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]

/--
theorem `vec_bijective` / 定理 `vec_bijective`

English:
theorem vec_bijective
  statement: Function.Bijective (vec : Matrix m n R -> _)
  proof: .symm.bijective.comp Function.swap_bijective Equiv.curry _ _ _

中文:
定理 vec_bijective
  结论: 函数.双射 (vec : 矩阵 m n R -> _)
  证明: .symm.bijective.comp Function.swap_bijective Equiv.curry _ _ _

Depends on / 依赖: Equiv.curry, Function, Function.swap_bijective, bijective, swap_bijective, symm.bijective.comp
-/
theorem vec_bijective : Function.Bijective (vec : Matrix m n R -> _) :=
.symm.bijective.comp Function.swap_bijective Equiv.curry _ _ _

/--
theorem `vec_map` / 定理 `vec_map`

English:
theorem vec_map
  given: (A : Matrix m n R) (f : R -> S)
  statement: vec (A.map f) = f ∘ vec A
  proof: rfl

@[simp]

中文:
定理 vec_map
  条件: (A : 矩阵 m n R) (f : R -> S)
  结论: vec (A.map f) = f ∘ vec A
  证明: rfl

@[simp]
-/
theorem vec_map (A : Matrix m n R) (f : R -> S) : vec (A.map f) = f ∘ vec A := rfl

@[simp]
/--
theorem `vec_zero` / 定理 `vec_zero`

English:
theorem vec_zero
  given: [Zero R]
  statement: vec (0 : Matrix m n R) = 0
  proof: rfl

@[simp]

中文:
定理 vec_zero
  条件: [零 R]
  结论: vec (0 : 矩阵 m n R) = 0
  证明: rfl

@[simp]
-/
theorem vec_zero [Zero R] : vec (0 : Matrix m n R) = 0 :=
  rfl

@[simp]
/--
theorem `vec_eq_zero_iff` / 定理 `vec_eq_zero_iff`

English:
theorem vec_eq_zero_iff
  given: [Zero R] {A : Matrix m n R}
  statement: vec A = 0 ↔ A = 0
  proof: vec_inj (B := 0)

@[simp]

中文:
定理 vec_eq_zero_iff
  条件: [零 R] {A : 矩阵 m n R}
  结论: vec A = 0 ↔ A = 0
  证明: vec_inj (B := 0)

@[simp]

Depends on / 依赖: vec_inj
-/
theorem vec_eq_zero_iff [Zero R] {A : Matrix m n R} : vec A = 0 ↔ A = 0 := vec_inj (B := 0)

@[simp]
/--
theorem `vec_add` / 定理 `vec_add`

English:
theorem vec_add
  given: [Add R] (A B : Matrix m n R)
  statement: vec (A + B) = vec A + vec B
  proof: rfl

中文:
定理 vec_add
  条件: [加法 R] (A B : 矩阵 m n R)
  结论: vec (A + B) = vec A + vec B
  证明: rfl
-/
theorem vec_add [Add R] (A B : Matrix m n R) : vec (A + B) = vec A + vec B :=
  rfl

/--
theorem `vec_neg` / 定理 `vec_neg`

English:
theorem vec_neg
  given: [Neg R] (A : Matrix m n R)
  statement: vec (-A) = -vec A
  proof: rfl

@[simp]

中文:
定理 vec_neg
  条件: [取负 R] (A : 矩阵 m n R)
  结论: vec (-A) = -vec A
  证明: rfl

@[simp]
-/
theorem vec_neg [Neg R] (A : Matrix m n R) : vec (-A) = -vec A :=
  rfl

@[simp]
/--
theorem `vec_sub` / 定理 `vec_sub`

English:
theorem vec_sub
  given: [Sub R] (A B : Matrix m n R)
  statement: vec (A - B) = vec A - vec B
  proof: rfl

@[simp]

中文:
定理 vec_sub
  条件: [减法 R] (A B : 矩阵 m n R)
  结论: vec (A - B) = vec A - vec B
  证明: rfl

@[simp]
-/
theorem vec_sub [Sub R] (A B : Matrix m n R) : vec (A - B) = vec A - vec B :=
  rfl

@[simp]
/--
theorem `vec_smul` / 定理 `vec_smul`

English:
theorem vec_smul
  given: {α} [SMul α R] (r : α) (A : Matrix m n R)
  statement: vec (r • A) = r • vec A
  proof: rfl

中文:
定理 vec_smul
  条件: {α} [标量乘法 α R] (r : α) (A : 矩阵 m n R)
  结论: vec (r • A) = r • vec A
  证明: rfl
-/
theorem vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : vec (r • A) = r • vec A :=
  rfl

/--
theorem `vec_sum` / 定理 `vec_sum`

English:
theorem vec_sum
  given: [AddCommMonoid R] (s : Finset ι) (A : ι -> Matrix m n R)
  proof: by
  ext
  simp_rw [vec, Finset.sum_apply, vec, Matrix.sum_apply]

中文:
定理 vec_sum
  条件: [加法交换幺半群 R] (s : 有限集 ι) (A : ι -> 矩阵 m n R)
  证明: by
  ext
  simp_rw [vec, Finset.sum_apply, vec, Matrix.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, Matrix, Matrix.sum_apply, simp_rw, sum_apply
-/
theorem vec_sum [AddCommMonoid R] (s : Finset ι) (A : ι -> Matrix m n R) :
    vec (∑ i in s, A i) = ∑ i in s, vec (A i) := by
  ext
  simp_rw [vec, Finset.sum_apply, vec, Matrix.sum_apply]

/--
theorem `vec_dotProduct_vec` / 定理 `vec_dotProduct_vec`

English:
theorem vec_dotProduct_vec
  statement: [AddCommMonoid R] [Mul R] [Fintype m] [Fintype n]
  proof: by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

中文:
定理 vec_dotProduct_vec
  结论: [加法交换幺半群 R] [乘法 R] [有限类型 m] [有限类型 n]
  证明: by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

Depends on / 依赖: Finset, Finset.sum_product, Finset.univ_product_univ, Matrix, Matrix.diag, Matrix.mul_apply, Matrix.trace, dotProduct, mul_apply, simp_rw, sum_product, transpose_apply, univ_product_univ
-/
theorem vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    vec A ⬝ᵥ vec B = (Aᵀ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

/--
theorem `star_vec` / 定理 `star_vec`

English:
theorem star_vec
  given: [Star R] (x : Matrix m n R)
  proof: rfl

中文:
定理 star_vec
  条件: [对合 R] (x : 矩阵 m n R)
  证明: rfl
-/
theorem star_vec [Star R] (x : Matrix m n R) :
    star x.vec = (x.map star).vec :=
  rfl

/--
theorem `star_vec_dotProduct_vec` / 定理 `star_vec_dotProduct_vec`

English:
theorem star_vec_dotProduct_vec
  statement: [AddCommMonoid R] [Mul R] [Star R] [Fintype m] [Fintype n]
  proof: by
  simp_rw [star_vec, vec_dotProduct_vec, ← conjTranspose_transpose, transpose_transpose]

中文:
定理 star_vec_dotProduct_vec
  结论: [加法交换幺半群 R] [乘法 R] [对合 R] [有限类型 m] [有限类型 n]
  证明: by
  simp_rw [star_vec, vec_dotProduct_vec, ← conjTranspose_transpose, transpose_transpose]

Depends on / 依赖: conjTranspose_transpose, simp_rw, star_vec, transpose_transpose, vec_dotProduct_vec
-/
theorem star_vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Star R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    star (vec A) ⬝ᵥ vec B = (Aᴴ * B).trace := by
  simp_rw [star_vec, vec_dotProduct_vec, ← conjTranspose_transpose, transpose_transpose]

/--
theorem `vec_hadamard` / 定理 `vec_hadamard`

English:
theorem vec_hadamard
  given: [Mul R] (A B : Matrix m n R)
  statement: vec (A ⊙ B) = vec A * vec B
  proof: rfl

@[simp]

中文:
定理 vec_hadamard
  条件: [乘法 R] (A B : 矩阵 m n R)
  结论: vec (A ⊙ B) = vec A * vec B
  证明: rfl

@[simp]
-/
theorem vec_hadamard [Mul R] (A B : Matrix m n R) : vec (A ⊙ B) = vec A * vec B := rfl

@[simp]
/--
theorem `vec_single` / 定理 `vec_single`

English:
theorem vec_single
  given: [DecidableEq m] [DecidableEq n] [Zero R] (i : m) (j : n) (r : R)
  proof: by
  rw [single_eq_of_single_single]; rw [vec_of]; rw [Function.uncurry_flip]; rw [Pi.uncurry_single_single]
  exact Pi.single_comp_equiv (Equiv.prodComm _ _) _ _

中文:
定理 vec_single
  条件: [DecidableEq m] [DecidableEq n] [零 R] (i : m) (j : n) (r : R)
  证明: by
  rw [single_eq_of_single_single]; rw [vec_of]; rw [Function.uncurry_flip]; rw [Pi.uncurry_single_single]
  exact Pi.single_comp_equiv (Equiv.prodComm _ _) _ _

Depends on / 依赖: Equiv.prodComm, Function, Function.uncurry_flip, Pi.single_comp_equiv, Pi.uncurry_single_single, prodComm, single_comp_equiv, single_eq_of_single_single, uncurry_flip, uncurry_single_single, vec_of
-/
theorem vec_single [DecidableEq m] [DecidableEq n] [Zero R] (i : m) (j : n) (r : R) :
    vec (Matrix.single i j r) = Pi.single (j, i) r := by
  rw [single_eq_of_single_single]; rw [vec_of]; rw [Function.uncurry_flip]; rw [Pi.uncurry_single_single]
  exact Pi.single_comp_equiv (Equiv.prodComm _ _) _ _

section Kronecker
open scoped Kronecker

section CommSemigroup
variable [CommSemigroup R]

/--
theorem `hadamard_kronecker_hadamard` / 定理 `hadamard_kronecker_hadamard`

English:
theorem hadamard_kronecker_hadamard
  given: (A B : Matrix l m R) (C D : Matrix n p R)
  proof: ext fun _ _ => mul_mul_mul_comm _ _ _ _

中文:
定理 hadamard_kronecker_hadamard
  条件: (A B : 矩阵 l m R) (C D : 矩阵 n p R)
  证明: ext fun _ _ => mul_mul_mul_comm _ _ _ _

Depends on / 依赖: mul_mul_mul_comm
-/
theorem hadamard_kronecker_hadamard (A B : Matrix l m R) (C D : Matrix n p R) :
    (A ⊙ B) otimesₖ (C ⊙ D) = (A otimesₖ C) ⊙ (B otimesₖ D) :=
  ext fun _ _ => mul_mul_mul_comm _ _ _ _

/--
theorem `kronecker_hadamard_kronecker` / 定理 `kronecker_hadamard_kronecker`

English:
theorem kronecker_hadamard_kronecker
  proof: .symm hadamard_kronecker_hadamard _ _ _ _

中文:
定理 kronecker_hadamard_kronecker
  证明: .symm hadamard_kronecker_hadamard _ _ _ _

Depends on / 依赖: hadamard_kronecker_hadamard
-/
theorem kronecker_hadamard_kronecker
    (A : Matrix l m R) (B : Matrix n p R) (C : Matrix l m R) (D : Matrix n p R) :
    (A otimesₖ B) ⊙ (C otimesₖ D) = (A ⊙ C) otimesₖ (B ⊙ D) :=
.symm hadamard_kronecker_hadamard _ _ _ _

end CommSemigroup

section NonUnitalSemiring
variable [NonUnitalSemiring R] [Fintype m] [Fintype n]

/--
theorem `kronecker_mulVec_vec_of_commute` / 定理 `kronecker_mulVec_vec_of_commute`

English:
theorem kronecker_mulVec_vec_of_commute
  statement: (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
  proof: by
  ext ⟨k, l⟩
  simp_rw [vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, vec, (hB ..).eq]

中文:
定理 kronecker_mulVec_vec_of_commute
  结论: (A : 矩阵 l m R) (X : 矩阵 m n R) (B : 矩阵 p n R)
  证明: by
  ext ⟨k, l⟩
  simp_rw [vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, vec, (hB ..).eq]

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sum_product, Finset.univ_product_univ, dotProduct, kroneckerMap_apply, mulVec, mul_apply, right_comm, simp_rw, sum_mul, sum_product, transpose_apply, univ_product_univ
-/
theorem kronecker_mulVec_vec_of_commute (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
    (hB : forall x i j, Commute x (B i j)) :
    (B otimesₖ A) *ᵥ vec X = vec (A * X * Bᵀ) := by
  ext ⟨k, l⟩
  simp_rw [vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, vec, (hB ..).eq]

/--
theorem `vec_vecMul_kronecker_of_commute` / 定理 `vec_vecMul_kronecker_of_commute`

English:
theorem vec_vecMul_kronecker_of_commute
  statement: (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
  proof: by
  ext ⟨k, l⟩
  simp_rw [vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, vec]

中文:
定理 vec_vecMul_kronecker_of_commute
  结论: (A : 矩阵 m l R) (X : 矩阵 m n R) (B : 矩阵 n p R)
  证明: by
  ext ⟨k, l⟩
  simp_rw [vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, vec]

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sum_product, Finset.univ_product_univ, dotProduct, kroneckerMap_apply, mul_apply, mul_assoc, right_comm, simp_rw, sum_mul, sum_product, transpose_apply, univ_product_univ, vecMul
-/
theorem vec_vecMul_kronecker_of_commute (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
    (hA : forall x i j, Commute (A i j) x) :
    vec X ᵥ* (B otimesₖ A) = vec (Aᵀ * X * B) := by
  ext ⟨k, l⟩
  simp_rw [vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, vec]

end NonUnitalSemiring

section NonUnitalCommSemiring
variable [NonUnitalCommSemiring R] [Fintype m] [Fintype n]

/--
theorem `kronecker_mulVec_vec` / 定理 `kronecker_mulVec_vec`

English:
theorem kronecker_mulVec_vec
  given: (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
  proof: kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _

中文:
定理 kronecker_mulVec_vec
  条件: (A : 矩阵 l m R) (X : 矩阵 m n R) (B : 矩阵 p n R)
  证明: kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all, kronecker_mulVec_vec_of_commute
-/
theorem kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) :
    (B otimesₖ A) *ᵥ vec X = vec (A * X * Bᵀ) :=
  kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _

/--
theorem `vec_vecMul_kronecker` / 定理 `vec_vecMul_kronecker`

English:
theorem vec_vecMul_kronecker
  given: (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
  proof: vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _ => Commute.all _ _

中文:
定理 vec_vecMul_kronecker
  条件: (A : 矩阵 m l R) (X : 矩阵 m n R) (B : 矩阵 n p R)
  证明: vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all, vec_vecMul_kronecker_of_commute
-/
theorem vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) :
    vec X ᵥ* (B otimesₖ A) = vec (Aᵀ * X * B) :=
  vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _ => Commute.all _ _

end NonUnitalCommSemiring

section Semiring
variable [Semiring R] [Fintype m] [Fintype n]

/--
theorem `vec_mul_eq_mulVec` / 定理 `vec_mul_eq_mulVec`

English:
theorem vec_mul_eq_mulVec
  given: [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R)
  proof: by
  rw [kronecker_mulVec_vec_of_commute]; rw [transpose_one]; rw [Matrix.mul_one]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

中文:
定理 vec_mul_eq_mulVec
  条件: [DecidableEq n] (A : 矩阵 l m R) (B : 矩阵 m n R)
  证明: by
  rw [kronecker_mulVec_vec_of_commute]; rw [transpose_one]; rw [Matrix.mul_one]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

Depends on / 依赖: Matrix, Matrix.mul_one, eq_or_ne, kronecker_mulVec_vec_of_commute, mul_one, transpose_one
-/
theorem vec_mul_eq_mulVec [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R) :
    vec (A * B) = (1 otimesₖ A) *ᵥ vec B := by
  rw [kronecker_mulVec_vec_of_commute]; rw [transpose_one]; rw [Matrix.mul_one]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

/--
theorem `vec_mul_eq_vecMul` / 定理 `vec_mul_eq_vecMul`

English:
theorem vec_mul_eq_vecMul
  given: [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R)
  proof: by
  rw [vec_vecMul_kronecker_of_commute]; rw [transpose_one]; rw [Matrix.one_mul]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

中文:
定理 vec_mul_eq_vecMul
  条件: [DecidableEq m] (A : 矩阵 m n R) (B : 矩阵 n p R)
  证明: by
  rw [vec_vecMul_kronecker_of_commute]; rw [transpose_one]; rw [Matrix.one_mul]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

Depends on / 依赖: LevyProkhorov, LevyProkhorov.probabilityMeasureHomeomorph, Matrix, Matrix.one_mul, PseudoMetricSpace, TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, eq_or_ne, isInducing, isInducing.pseudoMetrizableSpace, one_mul, probabilityMeasureHomeomorph, pseudoMetrizableSpace, pseudoMetrizableSpacePseudoMetric, transpose_one, vec_vecMul_kronecker_of_commute
-/
theorem vec_mul_eq_vecMul [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R) :
    vec (A * B) = A.vec ᵥ* (B otimesₖ 1) := by
  rw [vec_vecMul_kronecker_of_commute]; rw [transpose_one]; rw [Matrix.one_mul]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

end Semiring

section Hadamard

variable [NonUnitalSemiring R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

/--
theorem `dotProduct_hadamard_mulVec_eq_kronecker` / 定理 `dotProduct_hadamard_mulVec_eq_kronecker`

English:
theorem dotProduct_hadamard_mulVec_eq_kronecker
  proof: by
  simp [diagonal, mulVec, dotProduct, Fintype.sum_prod_type]

中文:
定理 dotProduct_hadamard_mulVec_eq_kronecker
  证明: by
  simp [diagonal, mulVec, dotProduct, Fintype.sum_prod_type]

Depends on / 依赖: Fintype, Fintype.sum_prod_type, diagonal, dotProduct, mulVec, sum_prod_type
-/
theorem dotProduct_hadamard_mulVec_eq_kronecker
    (x : m -> R) (A B : Matrix m n R) (x' : n -> R) :
    x ⬝ᵥ (A ⊙ B) *ᵥ x' = vec (diagonal x) ⬝ᵥ (A otimesₖ B) *ᵥ vec (diagonal x') := by
  simp [diagonal, mulVec, dotProduct, Fintype.sum_prod_type]

/--
theorem `star_dotProduct_hadamard_mulVec_eq_kronecker` / 定理 `star_dotProduct_hadamard_mulVec_eq_kronecker`

English:
theorem star_dotProduct_hadamard_mulVec_eq_kronecker
  statement: [StarAddMonoid R]
  proof: by
  rw [dotProduct_hadamard_mulVec_eq_kronecker]; rw [← map_diagonal_star]; rw [star_vec]

中文:
定理 star_dotProduct_hadamard_mulVec_eq_kronecker
  结论: [StarAdd幺半群 R]
  证明: by
  rw [dotProduct_hadamard_mulVec_eq_kronecker]; rw [← map_diagonal_star]; rw [star_vec]

Depends on / 依赖: dotProduct_hadamard_mulVec_eq_kronecker, map_diagonal_star, star_vec
-/
theorem star_dotProduct_hadamard_mulVec_eq_kronecker [StarAddMonoid R]
    (x : m -> R) (A B : Matrix m n R) (x' : n -> R) :
    star x ⬝ᵥ (A ⊙ B) *ᵥ x' = star (vec (diagonal x)) ⬝ᵥ (A otimesₖ B) *ᵥ vec (diagonal x') := by
  rw [dotProduct_hadamard_mulVec_eq_kronecker]; rw [← map_diagonal_star]; rw [star_vec]

end Hadamard

end Kronecker

end Matrix
