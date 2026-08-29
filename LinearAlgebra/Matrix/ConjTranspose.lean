/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis

/-!
# Matrices over star rings.

## Notation

The scope `Matrix` gives the following notation:

* `ᴴ` for `Matrix.conjTranspose`

-/

@[expose] public section


universe u u' v w

variable {l m n o : Type*} {m' : o -> Type*} {n' : o -> Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix


/--
Definition of `conjTranspose` / `conjTranspose` 的定义

English:
definition conjTranspose
  signature: [Star α] (M : Matrix m n α)
  body: M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

@[simp]

中文:
定义 conjTranspose
  签名: [对合 α] (M : 矩阵 m n α)
  定义体: M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

@[simp]

Depends on / 依赖: M.transpose.map, transpose
-/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

@[simp]
/--
lemma `conjTranspose_single` / 引理 `conjTranspose_single`

English:
lemma conjTranspose_single
  statement: [DecidableEq n] [DecidableEq m] [AddMonoid α]
  proof: by
  change (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

中文:
引理 conjTranspose_single
  结论: [DecidableEq n] [DecidableEq m] [加法幺半群 α]
  证明: by
  change (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

Depends on / 依赖: single, starAddEquiv, transpose, transpose.map
-/
lemma conjTranspose_single [DecidableEq n] [DecidableEq m] [AddMonoid α]
    [StarAddMonoid α] (i : m) (j : n) (a : α) :
    (single i j a)ᴴ = single j i (star a) := by
  change (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

section Diagonal

variable [DecidableEq n]

@[simp]
/--
theorem `diagonal_conjTranspose` / 定理 `diagonal_conjTranspose`

English:
theorem diagonal_conjTranspose
  given: [AddMonoid α] [StarAddMonoid α] (v : n -> α)
  proof: by
  rw [conjTranspose]; rw [diagonal_transpose]; rw [diagonal_map (star_zero _)]
  rfl

中文:
定理 diagonal_conjTranspose
  条件: [加法幺半群 α] [StarAdd幺半群 α] (v : n -> α)
  证明: by
  rw [conjTranspose]; rw [diagonal_transpose]; rw [diagonal_map (star_zero _)]
  rfl

Depends on / 依赖: conjTranspose, diagonal_map, diagonal_transpose, star_zero
-/
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n -> α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [conjTranspose]; rw [diagonal_transpose]; rw [diagonal_map (star_zero _)]
  rfl

/--
theorem `map_diagonal_star` / 定理 `map_diagonal_star`

English:
theorem map_diagonal_star
  given: [AddMonoid α] [StarAddMonoid α] (x : n -> α)
  proof: diagonal_map (star_zero _)

中文:
定理 map_diagonal_star
  条件: [加法幺半群 α] [StarAdd幺半群 α] (x : n -> α)
  证明: diagonal_map (star_zero _)

Depends on / 依赖: diagonal_map, star_zero
-/
theorem map_diagonal_star [AddMonoid α] [StarAddMonoid α] (x : n -> α) :
    (diagonal x).map star = diagonal (star x) := diagonal_map (star_zero _)

end Diagonal

section Diag

@[simp]
/--
theorem `diag_conjTranspose` / 定理 `diag_conjTranspose`

English:
theorem diag_conjTranspose
  given: [Star α] (A : Matrix n n α)
  proof: rfl

中文:
定理 diag_conjTranspose
  条件: [对合 α] (A : 矩阵 n n α)
  证明: rfl
-/
theorem diag_conjTranspose [Star α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl

/--
theorem `diag_map_star` / 定理 `diag_map_star`

English:
theorem diag_map_star
  given: [Star α] (A : Matrix n n α)
  statement: diag (A.map star) = star (diag A)
  proof: rfl

中文:
定理 diag_map_star
  条件: [对合 α] (A : 矩阵 n n α)
  结论: diag (A.map star) = star (diag A)
  证明: rfl
-/
@[simp] theorem diag_map_star [Star α] (A : Matrix n n α) : diag (A.map star) = star (diag A) := rfl

end Diag

section DotProduct

variable [Fintype m] [Fintype n]

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m -> α)

/--
theorem `star_dotProduct_star` / 定理 `star_dotProduct_star`

English:
theorem star_dotProduct_star
  statement: star v ⬝ᵥ star w = star (w ⬝ᵥ v)
  proof: by simp [dotProduct]

中文:
定理 star_dotProduct_star
  结论: star v ⬝ᵥ star w = star (w ⬝ᵥ v)
  证明: by simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dotProduct]

/--
theorem `star_dotProduct` / 定理 `star_dotProduct`

English:
theorem star_dotProduct
  statement: star v ⬝ᵥ w = star (star w ⬝ᵥ v)
  proof: by simp [dotProduct]

中文:
定理 star_dotProduct
  结论: star v ⬝ᵥ w = star (star w ⬝ᵥ v)
  证明: by simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]

/--
theorem `dotProduct_star` / 定理 `dotProduct_star`

English:
theorem dotProduct_star
  statement: v ⬝ᵥ star w = star (w ⬝ᵥ star v)
  proof: by simp [dotProduct]

中文:
定理 dotProduct_star
  结论: v ⬝ᵥ star w = star (w ⬝ᵥ star v)
  证明: by simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dotProduct]

end StarRing

end DotProduct

section NonUnitalSemiring

variable [NonUnitalSemiring α]

/--
theorem `star_mulVec` / 定理 `star_mulVec`

English:
theorem star_mulVec
  given: [Fintype n] [StarRing α] (M : Matrix m n α) (v : n -> α)
  proof: funext fun _ => (star_dotProduct_star _ _).symm

中文:
定理 star_mulVec
  条件: [有限类型 n] [对合环 α] (M : 矩阵 m n α) (v : n -> α)
  证明: funext fun _ => (star_dotProduct_star _ _).symm

Depends on / 依赖: star_dotProduct_star
-/
theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n -> α) :
    star (M *ᵥ v) = star v ᵥ* Mᴴ :=
  funext fun _ => (star_dotProduct_star _ _).symm

/--
theorem `star_vecMul` / 定理 `star_vecMul`

English:
theorem star_vecMul
  given: [Fintype m] [StarRing α] (M : Matrix m n α) (v : m -> α)
  proof: funext fun _ => (star_dotProduct_star _ _).symm

中文:
定理 star_vecMul
  条件: [有限类型 m] [对合环 α] (M : 矩阵 m n α) (v : m -> α)
  证明: funext fun _ => (star_dotProduct_star _ _).symm

Depends on / 依赖: star_dotProduct_star
-/
theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m -> α) :
    star (v ᵥ* M) = Mᴴ *ᵥ star v :=
  funext fun _ => (star_dotProduct_star _ _).symm

/--
theorem `mulVec_conjTranspose` / 定理 `mulVec_conjTranspose`

English:
theorem mulVec_conjTranspose
  given: [Fintype m] [StarRing α] (A : Matrix m n α) (x : m -> α)
  proof: funext fun _ => star_dotProduct _ _

中文:
定理 mulVec_conjTranspose
  条件: [有限类型 m] [对合环 α] (A : 矩阵 m n α) (x : m -> α)
  证明: funext fun _ => star_dotProduct _ _

Depends on / 依赖: star_dotProduct
-/
theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m -> α) :
    Aᴴ *ᵥ x = star (star x ᵥ* A) :=
  funext fun _ => star_dotProduct _ _

/--
theorem `vecMul_conjTranspose` / 定理 `vecMul_conjTranspose`

English:
theorem vecMul_conjTranspose
  given: [Fintype n] [StarRing α] (A : Matrix m n α) (x : n -> α)
  proof: funext fun _ => dotProduct_star _ _

中文:
定理 vecMul_conjTranspose
  条件: [有限类型 n] [对合环 α] (A : 矩阵 m n α) (x : n -> α)
  证明: funext fun _ => dotProduct_star _ _

Depends on / 依赖: dotProduct_star
-/
theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n -> α) :
    x ᵥ* Aᴴ = star (A *ᵥ star x) :=
  funext fun _ => dotProduct_star _ _

end NonUnitalSemiring

@[simp]
/--
theorem `conjTranspose_vecMulVec` / 定理 `conjTranspose_vecMulVec`

English:
theorem conjTranspose_vecMulVec
  given: [Mul α] [StarMul α] (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => star_mul _ _

中文:
定理 conjTranspose_vecMulVec
  条件: [乘法 α] [StarMul α] (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => star_mul _ _

Depends on / 依赖: star_mul
-/
theorem conjTranspose_vecMulVec [Mul α] [StarMul α] (w : m -> α) (v : n -> α) :
    (vecMulVec w v)ᴴ = vecMulVec (star v) (star w) :=
  ext fun _ _ => star_mul _ _

/--
theorem `map_vecMulVec_star` / 定理 `map_vecMulVec_star`

English:
theorem map_vecMulVec_star
  given: [Mul α] [StarMul α] (w : m -> α) (v : n -> α)
  proof: by
  rw [← conjTranspose_vecMulVec]; rfl

中文:
定理 map_vecMulVec_star
  条件: [乘法 α] [StarMul α] (w : m -> α) (v : n -> α)
  证明: by
  rw [← conjTranspose_vecMulVec]; rfl
-/
@[simp] theorem map_vecMulVec_star [Mul α] [StarMul α] (w : m -> α) (v : n -> α) :
    (vecMulVec w v).map star = (vecMulVec (star v) (star w))ᵀ := by
  rw [← conjTranspose_vecMulVec]; rfl

section ConjTranspose

open Matrix

/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
/--
theorem `conjTranspose_apply` / 定理 `conjTranspose_apply`

English:
theorem conjTranspose_apply
  given: [Star α] (M : Matrix m n α) (i j)
  proof: rfl

@[simp]

中文:
定理 conjTranspose_apply
  条件: [对合 α] (M : 矩阵 m n α) (i j)
  证明: rfl

@[simp]
-/
theorem conjTranspose_apply [Star α] (M : Matrix m n α) (i j) :
    M.conjTranspose j i = star (M i j) :=
  rfl

@[simp]
/--
theorem `conjTranspose_conjTranspose` / 定理 `conjTranspose_conjTranspose`

English:
theorem conjTranspose_conjTranspose
  given: [InvolutiveStar α] (M : Matrix m n α)
  statement: Mᴴᴴ = M
  proof: Matrix.ext by simp

中文:
定理 conjTranspose_conjTranspose
  条件: [InvolutiveStar α] (M : 矩阵 m n α)
  结论: Mᴴᴴ = M
  证明: Matrix.ext by simp

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
Matrix.ext by simp

variable (n α) in
/--
theorem `conjTranspose_involutive` / 定理 `conjTranspose_involutive`

English:
theorem conjTranspose_involutive
  given: [InvolutiveStar α]
  proof: conjTranspose_conjTranspose

中文:
定理 conjTranspose_involutive
  条件: [InvolutiveStar α]
  证明: conjTranspose_conjTranspose

Depends on / 依赖: conjTranspose_conjTranspose
-/
theorem conjTranspose_involutive [InvolutiveStar α] :
    (conjTranspose : Matrix n n α -> Matrix n n α).Involutive :=
  conjTranspose_conjTranspose

/--
theorem `conjTranspose_transpose` / 定理 `conjTranspose_transpose`

English:
theorem conjTranspose_transpose
  given: [Star α] (M : Matrix m n α)
  proof: rfl

中文:
定理 conjTranspose_transpose
  条件: [对合 α] (M : 矩阵 m n α)
  证明: rfl
-/
theorem conjTranspose_transpose [Star α] (M : Matrix m n α) :
    Mᴴᵀ = M.map star :=
  rfl

/--
theorem `transpose_conjTranspose` / 定理 `transpose_conjTranspose`

English:
theorem transpose_conjTranspose
  given: [Star α] (M : Matrix m n α)
  proof: rfl

中文:
定理 transpose_conjTranspose
  条件: [对合 α] (M : 矩阵 m n α)
  证明: rfl
-/
theorem transpose_conjTranspose [Star α] (M : Matrix m n α) :
    Mᵀᴴ = M.map star :=
  rfl

/--
theorem `conjTranspose_transpose_eq_transpose_conjTranspose` / 定理 `conjTranspose_transpose_eq_transpose_conjTranspose`

English:
theorem conjTranspose_transpose_eq_transpose_conjTranspose
  given: [Star α] (M : Matrix m n α)
  proof: rfl

中文:
定理 conjTranspose_transpose_eq_transpose_conjTranspose
  条件: [对合 α] (M : 矩阵 m n α)
  证明: rfl
-/
theorem conjTranspose_transpose_eq_transpose_conjTranspose [Star α] (M : Matrix m n α) :
    Mᵀᴴ = Mᴴᵀ :=
  rfl

/--
theorem `conjTranspose_injective` / 定理 `conjTranspose_injective`

English:
theorem conjTranspose_injective
  given: [InvolutiveStar α]
  proof: (map_injective star_injective).comp transpose_injective

中文:
定理 conjTranspose_injective
  条件: [InvolutiveStar α]
  证明: (map_injective star_injective).comp transpose_injective

Depends on / 依赖: map_injective, star_injective, transpose_injective
-/
theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (conjTranspose : Matrix m n α -> Matrix n m α) :=
  (map_injective star_injective).comp transpose_injective

/--
theorem `conjTranspose_inj` / 定理 `conjTranspose_inj`

English:
theorem conjTranspose_inj
  given: [InvolutiveStar α] {A B : Matrix m n α}
  statement: Aᴴ = Bᴴ ↔ A = B
  proof: conjTranspose_injective.eq_iff

@[simp]

中文:
定理 conjTranspose_inj
  条件: [InvolutiveStar α] {A B : 矩阵 m n α}
  结论: Aᴴ = Bᴴ ↔ A = B
  证明: conjTranspose_injective.eq_iff

@[simp]
-/
@[simp] theorem conjTranspose_inj [InvolutiveStar α] {A B : Matrix m n α} : Aᴴ = Bᴴ ↔ A = B :=
  conjTranspose_injective.eq_iff

@[simp]
/--
theorem `conjTranspose_eq_diagonal` / 定理 `conjTranspose_eq_diagonal`

English:
theorem conjTranspose_eq_diagonal
  statement: [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
  proof: (conjTranspose_involutive n α).eq_iff.trans by rw [diagonal_conjTranspose]

中文:
定理 conjTranspose_eq_diagonal
  结论: [DecidableEq n] [加法幺半群 α] [StarAdd幺半群 α]
  证明: (conjTranspose_involutive n α).eq_iff.trans by rw [diagonal_conjTranspose]

Depends on / 依赖: conjTranspose_involutive, diagonal_conjTranspose, eq_iff, eq_iff.trans
-/
theorem conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n -> α} :
    Mᴴ = diagonal v ↔ M = diagonal (star v) :=
(conjTranspose_involutive n α).eq_iff.trans by rw [diagonal_conjTranspose]

/--
theorem `map_star_eq_diagonal` / 定理 `map_star_eq_diagonal`

English:
theorem map_star_eq_diagonal
  statement: [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
  proof: .eq_iff.trans by rw [map_diagonal_star] map_involutive star_involutive

@[simp]

中文:
定理 map_star_eq_diagonal
  结论: [DecidableEq n] [加法幺半群 α] [StarAdd幺半群 α]
  证明: .eq_iff.trans by rw [map_diagonal_star] map_involutive star_involutive

@[simp]
-/
@[simp] theorem map_star_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n -> α} : M.map star = diagonal v ↔ M = diagonal (star v) :=
.eq_iff.trans by rw [map_diagonal_star] map_involutive star_involutive

@[simp]
/--
theorem `conjTranspose_zero` / 定理 `conjTranspose_zero`

English:
theorem conjTranspose_zero
  given: [AddMonoid α] [StarAddMonoid α]
  statement: (0 : Matrix m n α)ᴴ = 0
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_zero
  条件: [加法幺半群 α] [StarAdd幺半群 α]
  结论: (0 : 矩阵 m n α)ᴴ = 0
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_eq_zero` / 定理 `conjTranspose_eq_zero`

English:
theorem conjTranspose_eq_zero
  given: [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α}
  proof: by
  rw [← conjTranspose_inj (A := M)]; rw [conjTranspose_zero]

中文:
定理 conjTranspose_eq_zero
  条件: [加法幺半群 α] [StarAdd幺半群 α] {M : 矩阵 m n α}
  证明: by
  rw [← conjTranspose_inj (A := M)]; rw [conjTranspose_zero]

Depends on / 依赖: conjTranspose_inj, conjTranspose_zero
-/
theorem conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    Mᴴ = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (A := M)]; rw [conjTranspose_zero]

/--
theorem `map_star_eq_zero` / 定理 `map_star_eq_zero`

English:
theorem map_star_eq_zero
  given: [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α}
  proof: by simp [← ext_iff]

@[simp]

中文:
定理 map_star_eq_zero
  条件: [加法幺半群 α] [StarAdd幺半群 α] {M : 矩阵 m n α}
  证明: by simp [← ext_iff]

@[simp]
-/
@[simp] theorem map_star_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    M.map star = 0 ↔ M = 0 := by simp [← ext_iff]

@[simp]
/--
theorem `conjTranspose_one` / 定理 `conjTranspose_one`

English:
theorem conjTranspose_one
  given: [DecidableEq n] [NonAssocSemiring α] [StarRing α]
  proof: by
  simp [conjTranspose]

@[simp]

中文:
定理 conjTranspose_one
  条件: [DecidableEq n] [非结合半环 α] [对合环 α]
  证明: by
  simp [conjTranspose]

@[simp]

Depends on / 依赖: conjTranspose
-/
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴ = 1 := by
  simp [conjTranspose]

@[simp]
/--
theorem `conjTranspose_eq_one` / 定理 `conjTranspose_eq_one`

English:
theorem conjTranspose_eq_one
  given: [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α}
  proof: (conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_one]

中文:
定理 conjTranspose_eq_one
  条件: [DecidableEq n] [非结合半环 α] [对合环 α] {M : 矩阵 n n α}
  证明: (conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_one]

Depends on / 依赖: conjTranspose_involutive, conjTranspose_one, eq_iff, eq_iff.trans
-/
theorem conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 :=
(conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_one]

/--
theorem `map_star_eq_one` / 定理 `map_star_eq_one`

English:
theorem map_star_eq_one
  statement: [DecidableEq n] [NonAssocSemiring α] [StarRing α]
  proof: .eq_iff.trans by simp map_involutive star_involutive

@[simp]

中文:
定理 map_star_eq_one
  结论: [DecidableEq n] [非结合半环 α] [对合环 α]
  证明: .eq_iff.trans by simp map_involutive star_involutive

@[simp]
-/
@[simp] theorem map_star_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} : M.map star = 1 ↔ M = 1 :=
.eq_iff.trans by simp map_involutive star_involutive

@[simp]
/--
theorem `conjTranspose_natCast` / 定理 `conjTranspose_natCast`

English:
theorem conjTranspose_natCast
  given: [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
  proof: by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]

中文:
定理 conjTranspose_natCast
  条件: [DecidableEq n] [非结合半环 α] [对合环 α] (d : 自然数)
  证明: by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_natCast, conjTranspose, diagonal_natCast, map_natCast
-/
theorem conjTranspose_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]
/--
theorem `map_natCast_star` / 定理 `map_natCast_star`

English:
theorem map_natCast_star
  given: [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
  proof: by simp [Matrix.map_natCast, diagonal_natCast]

@[simp]

中文:
定理 map_natCast_star
  条件: [DecidableEq n] [非结合半环 α] [对合环 α] (d : 自然数)
  证明: by simp [Matrix.map_natCast, diagonal_natCast]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_natCast, diagonal_natCast, map_natCast
-/
theorem map_natCast_star [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat) :
    (d : Matrix n n α).map star = d := by simp [Matrix.map_natCast, diagonal_natCast]

@[simp]
/--
theorem `conjTranspose_eq_natCast` / 定理 `conjTranspose_eq_natCast`

English:
theorem conjTranspose_eq_natCast
  statement: [DecidableEq n] [NonAssocSemiring α] [StarRing α]
  proof: (conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_natCast]

中文:
定理 conjTranspose_eq_natCast
  结论: [DecidableEq n] [非结合半环 α] [对合环 α]
  证明: (conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_natCast]

Depends on / 依赖: conjTranspose_involutive, conjTranspose_natCast, eq_iff, eq_iff.trans
-/
theorem conjTranspose_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} {d : Nat} :
    Mᴴ = d ↔ M = d :=
(conjTranspose_involutive n α).eq_iff.trans by rw [conjTranspose_natCast]

/--
theorem `map_star_eq_natCast` / 定理 `map_star_eq_natCast`

English:
theorem map_star_eq_natCast
  statement: [DecidableEq n] [NonAssocSemiring α] [StarRing α]
  proof: (map_involutive star_involutive).eq_iff.trans by rw [map_natCast_star]

@[simp]

中文:
定理 map_star_eq_natCast
  结论: [DecidableEq n] [非结合半环 α] [对合环 α]
  证明: (map_involutive star_involutive).eq_iff.trans by rw [map_natCast_star]

@[simp]
-/
@[simp] theorem map_star_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} {d : Nat} : M.map star = d ↔ M = d :=
(map_involutive star_involutive).eq_iff.trans by rw [map_natCast_star]

@[simp]
/--
theorem `conjTranspose_ofNat` / 定理 `conjTranspose_ofNat`

English:
theorem conjTranspose_ofNat
  statement: [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
  proof: conjTranspose_natCast _

中文:
定理 conjTranspose_of自然数
  结论: [DecidableEq n] [非结合半环 α] [对合环 α] (d : 自然数)
  证明: conjTranspose_natCast _

Depends on / 依赖: conjTranspose_natCast
-/
theorem conjTranspose_ofNat [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α)ᴴ = OfNat.ofNat d :=
  conjTranspose_natCast _

/--
theorem `map_ofNat_star` / 定理 `map_ofNat_star`

English:
theorem map_ofNat_star
  statement: [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
  proof: map_natCast_star _

@[simp]

中文:
定理 map_of自然数_star
  结论: [DecidableEq n] [非结合半环 α] [对合环 α] (d : 自然数)
  证明: map_natCast_star _

@[simp]
-/
@[simp] theorem map_ofNat_star [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Nat)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α).map star = OfNat.ofNat d := map_natCast_star _

@[simp]
/--
theorem `conjTranspose_eq_ofNat` / 定理 `conjTranspose_eq_ofNat`

English:
theorem conjTranspose_eq_ofNat
  statement: [DecidableEq n] [Semiring α] [StarRing α]
  proof: conjTranspose_eq_natCast

中文:
定理 conjTranspose_eq_of自然数
  结论: [DecidableEq n] [半环 α] [对合环 α]
  证明: conjTranspose_eq_natCast

Depends on / 依赖: conjTranspose_eq_natCast
-/
theorem conjTranspose_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α]
    {M : Matrix n n α} {d : Nat} [d.AtLeastTwo] :
    Mᴴ = ofNat(d) ↔ M = OfNat.ofNat d :=
  conjTranspose_eq_natCast

/--
theorem `map_star_eq_ofNat` / 定理 `map_star_eq_ofNat`

English:
theorem map_star_eq_ofNat
  statement: [DecidableEq n] [Semiring α] [StarRing α] {M : Matrix n n α}
  proof: map_star_eq_natCast

@[simp]

中文:
定理 map_star_eq_of自然数
  结论: [DecidableEq n] [半环 α] [对合环 α] {M : 矩阵 n n α}
  证明: map_star_eq_natCast

@[simp]
-/
@[simp] theorem map_star_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α] {M : Matrix n n α}
    {d : Nat} [d.AtLeastTwo] : M.map star = ofNat(d) ↔ M = OfNat.ofNat d := map_star_eq_natCast

@[simp]
/--
theorem `conjTranspose_intCast` / 定理 `conjTranspose_intCast`

English:
theorem conjTranspose_intCast
  given: [DecidableEq n] [Ring α] [StarRing α] (d : Int)
  proof: by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]

中文:
定理 conjTranspose_intCast
  条件: [DecidableEq n] [环 α] [对合环 α] (d : 整数)
  证明: by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]

Depends on / 依赖: Matrix, Matrix.map_intCast, conjTranspose, diagonal_intCast, map_intCast
-/
theorem conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : Int) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]

/--
theorem `map_intCast_star` / 定理 `map_intCast_star`

English:
theorem map_intCast_star
  given: [DecidableEq n] [Ring α] [StarRing α] (d : Int)
  proof: by simp [Matrix.map_intCast, diagonal_intCast]

@[simp]

中文:
定理 map_intCast_star
  条件: [DecidableEq n] [环 α] [对合环 α] (d : 整数)
  证明: by simp [Matrix.map_intCast, diagonal_intCast]

@[simp]
-/
@[simp] theorem map_intCast_star [DecidableEq n] [Ring α] [StarRing α] (d : Int) :
    (d : Matrix n n α).map star = d := by simp [Matrix.map_intCast, diagonal_intCast]

@[simp]
/--
theorem `conjTranspose_eq_intCast` / 定理 `conjTranspose_eq_intCast`

English:
theorem conjTranspose_eq_intCast
  statement: [DecidableEq n] [Ring α] [StarRing α]
  proof: (conjTranspose_involutive n α).eq_iff.trans
    by rw [conjTranspose_intCast]

中文:
定理 conjTranspose_eq_intCast
  结论: [DecidableEq n] [环 α] [对合环 α]
  证明: (conjTranspose_involutive n α).eq_iff.trans
    by rw [conjTranspose_intCast]

Depends on / 依赖: conjTranspose_intCast, conjTranspose_involutive, eq_iff, eq_iff.trans
-/
theorem conjTranspose_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : Int} :
    Mᴴ = d ↔ M = d :=
(conjTranspose_involutive n α).eq_iff.trans
    by rw [conjTranspose_intCast]

/--
theorem `map_star_eq_intCast` / 定理 `map_star_eq_intCast`

English:
theorem map_star_eq_intCast
  statement: [DecidableEq n] [Ring α] [StarRing α]
  proof: (map_involutive star_involutive).eq_iff.trans by rw [map_intCast_star]

@[simp]

中文:
定理 map_star_eq_intCast
  结论: [DecidableEq n] [环 α] [对合环 α]
  证明: (map_involutive star_involutive).eq_iff.trans by rw [map_intCast_star]

@[simp]
-/
@[simp] theorem map_star_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : Int} : M.map star = d ↔ M = d :=
(map_involutive star_involutive).eq_iff.trans by rw [map_intCast_star]

@[simp]
/--
theorem `conjTranspose_add` / 定理 `conjTranspose_add`

English:
theorem conjTranspose_add
  given: [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α)
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_add
  条件: [加法幺半群 α] [StarAdd幺半群 α] (M N : 矩阵 m n α)
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_sub` / 定理 `conjTranspose_sub`

English:
theorem conjTranspose_sub
  given: [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α)
  proof: Matrix.ext by simp

中文:
定理 conjTranspose_sub
  条件: [加法群 α] [StarAdd幺半群 α] (M N : 矩阵 m n α)
  证明: Matrix.ext by simp

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
Matrix.ext by simp

/-- Note that `StarModule` is quite a strong requirement; as such we also provide the following
variants which this lemma would not apply to:
* `Matrix.conjTranspose_smul_non_comm`
* `Matrix.conjTranspose_nsmul`
* `Matrix.conjTranspose_zsmul`
* `Matrix.conjTranspose_natCast_smul`
* `Matrix.conjTranspose_intCast_smul`
* `Matrix.conjTranspose_inv_natCast_smul`
* `Matrix.conjTranspose_inv_intCast_smul`
* `Matrix.conjTranspose_ratCast_smul`
-/
@[simp]
/--
theorem `conjTranspose_smul` / 定理 `conjTranspose_smul`

English:
theorem conjTranspose_smul
  statement: [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
  proof: Matrix.ext fun _ _ => star_smul _ _

@[simp]

中文:
定理 conjTranspose_smul
  结论: [对合 R] [对合 α] [标量乘法 R α] [对合模 R α] (c : R)
  证明: Matrix.ext fun _ _ => star_smul _ _

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, star_smul
-/
theorem conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ :=
  Matrix.ext fun _ _ => star_smul _ _

@[simp]
/--
theorem `conjTranspose_smul_non_comm` / 定理 `conjTranspose_smul_non_comm`

English:
theorem conjTranspose_smul_non_comm
  statement: [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
  proof: Matrix.ext by simp [h]

中文:
定理 conjTranspose_smul_non_comm
  结论: [对合 R] [对合 α] [标量乘法 R α] [标量乘法 Rᵐᵒᵖ α] (c : R)
  证明: Matrix.ext by simp [h]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : forall (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
Matrix.ext by simp [h]

/--
theorem `conjTranspose_smul_self` / 定理 `conjTranspose_smul_self`

English:
theorem conjTranspose_smul_self
  given: [Mul α] [StarMul α] (c : α) (M : Matrix m n α)
  proof: conjTranspose_smul_non_comm c M star_mul

中文:
定理 conjTranspose_smul_self
  条件: [乘法 α] [StarMul α] (c : α) (M : 矩阵 m n α)
  证明: conjTranspose_smul_non_comm c M star_mul

Depends on / 依赖: conjTranspose_smul_non_comm, star_mul
-/
theorem conjTranspose_smul_self [Mul α] [StarMul α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul

/--
theorem `conjTranspose_nsmul` / 定理 `conjTranspose_nsmul`

English:
theorem conjTranspose_nsmul
  given: [AddMonoid α] [StarAddMonoid α] (c : Nat) (M : Matrix m n α)
  proof: by
  simp

中文:
定理 conjTranspose_nsmul
  条件: [加法幺半群 α] [StarAdd幺半群 α] (c : 自然数) (M : 矩阵 m n α)
  证明: by
  simp
-/
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : Nat) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ := by
  simp

/--
theorem `conjTranspose_zsmul` / 定理 `conjTranspose_zsmul`

English:
theorem conjTranspose_zsmul
  given: [AddGroup α] [StarAddMonoid α] (c : Int) (M : Matrix m n α)
  proof: by
  simp

@[simp]

中文:
定理 conjTranspose_zsmul
  条件: [加法群 α] [StarAdd幺半群 α] (c : 整数) (M : 矩阵 m n α)
  证明: by
  simp

@[simp]
-/
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : Int) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ := by
  simp

@[simp]
/--
theorem `conjTranspose_natCast_smul` / 定理 `conjTranspose_natCast_smul`

English:
theorem conjTranspose_natCast_smul
  statement: [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_natCast_smul
  结论: [半环 R] [加法交换幺半群 α] [StarAdd幺半群 α] [模 R α]
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : Nat) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_ofNat_smul` / 定理 `conjTranspose_ofNat_smul`

English:
theorem conjTranspose_ofNat_smul
  statement: [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
  proof: conjTranspose_natCast_smul c M

@[simp]

中文:
定理 conjTranspose_of自然数_smul
  结论: [半环 R] [加法交换幺半群 α] [StarAdd幺半群 α] [模 R α]
  证明: conjTranspose_natCast_smul c M

@[simp]

Depends on / 依赖: conjTranspose_natCast_smul
-/
theorem conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : Nat) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R) • M)ᴴ = (OfNat.ofNat c : R) • Mᴴ :=
  conjTranspose_natCast_smul c M

@[simp]
/--
theorem `conjTranspose_intCast_smul` / 定理 `conjTranspose_intCast_smul`

English:
theorem conjTranspose_intCast_smul
  statement: [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : Int)
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_intCast_smul
  结论: [环 R] [加法交换群 α] [StarAdd幺半群 α] [模 R α] (c : 整数)
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : Int)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_inv_natCast_smul` / 定理 `conjTranspose_inv_natCast_smul`

English:
theorem conjTranspose_inv_natCast_smul
  statement: [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_inv_natCast_smul
  结论: [除半环 R] [加法交换幺半群 α] [StarAdd幺半群 α]
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : Nat) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_inv_ofNat_smul` / 定理 `conjTranspose_inv_ofNat_smul`

English:
theorem conjTranspose_inv_ofNat_smul
  statement: [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
  proof: conjTranspose_inv_natCast_smul c M

@[simp]

中文:
定理 conjTranspose_inv_of自然数_smul
  结论: [除半环 R] [加法交换幺半群 α] [StarAdd幺半群 α]
  证明: conjTranspose_inv_natCast_smul c M

@[simp]

Depends on / 依赖: conjTranspose_inv_natCast_smul
-/
theorem conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : Nat) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R)⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ :=
  conjTranspose_inv_natCast_smul c M

@[simp]
/--
theorem `conjTranspose_inv_intCast_smul` / 定理 `conjTranspose_inv_intCast_smul`

English:
theorem conjTranspose_inv_intCast_smul
  statement: [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_inv_intCast_smul
  结论: [除环 R] [加法交换群 α] [StarAdd幺半群 α]
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : Int) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_ratCast_smul` / 定理 `conjTranspose_ratCast_smul`

English:
theorem conjTranspose_ratCast_smul
  statement: [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
  proof: Matrix.ext by simp

中文:
定理 conjTranspose_ratCast_smul
  结论: [除环 R] [加法交换群 α] [StarAdd幺半群 α] [模 R α]
  证明: Matrix.ext by simp

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : Rat) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
Matrix.ext by simp

/--
theorem `conjTranspose_rat_smul` / 定理 `conjTranspose_rat_smul`

English:
theorem conjTranspose_rat_smul
  statement: [AddCommGroup α] [StarAddMonoid α] [Module Rat α] (c : Rat)
  proof: Matrix.ext by simp

@[simp]

中文:
定理 conjTranspose_rat_smul
  结论: [加法交换群 α] [StarAdd幺半群 α] [模 有理数 α] (c : 有理数)
  证明: Matrix.ext by simp

@[simp]

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module Rat α] (c : Rat)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
Matrix.ext by simp

@[simp]
/--
theorem `conjTranspose_mul` / 定理 `conjTranspose_mul`

English:
theorem conjTranspose_mul
  statement: [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M : Matrix m n α)
  proof: Matrix.ext by simp [mul_apply]

@[simp]

中文:
定理 conjTranspose_mul
  结论: [有限类型 n] [非幺非结合半环 α] [对合环 α] (M : 矩阵 m n α)
  证明: Matrix.ext by simp [mul_apply]

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, mul_apply
-/
theorem conjTranspose_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ :=
Matrix.ext by simp [mul_apply]

@[simp]
/--
theorem `conjTranspose_neg` / 定理 `conjTranspose_neg`

English:
theorem conjTranspose_neg
  given: [AddGroup α] [StarAddMonoid α] (M : Matrix m n α)
  statement: (-M)ᴴ = -Mᴴ
  proof: Matrix.ext by simp

中文:
定理 conjTranspose_neg
  条件: [加法群 α] [StarAdd幺半群 α] (M : 矩阵 m n α)
  结论: (-M)ᴴ = -Mᴴ
  证明: Matrix.ext by simp

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
Matrix.ext by simp

/--
theorem `conjTranspose_map` / 定理 `conjTranspose_map`

English:
theorem conjTranspose_map
  statement: [Star α] [Star β] {A : Matrix m n α} (f : α -> β)
  proof: Matrix.ext fun _ _ => hf _

中文:
定理 conjTranspose_map
  结论: [对合 α] [对合 β] {A : 矩阵 m n α} (f : α -> β)
  证明: Matrix.ext fun _ _ => hf _

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α -> β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun _ _ => hf _

/-- When `star x = x` on the coefficients (such as the real numbers) `conjTranspose` and `transpose`
are the same operation. -/
@[simp]
/--
theorem `conjTranspose_eq_transpose_of_trivial` / 定理 `conjTranspose_eq_transpose_of_trivial`

English:
theorem conjTranspose_eq_transpose_of_trivial
  given: [Star α] [TrivialStar α] (A : Matrix m n α)
  proof: Matrix.ext fun _ _ => star_trivial _

中文:
定理 conjTranspose_eq_transpose_of_trivial
  条件: [对合 α] [TrivialStar α] (A : 矩阵 m n α)
  证明: Matrix.ext fun _ _ => star_trivial _

Depends on / 依赖: Matrix, Matrix.ext, star_trivial
-/
theorem conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) :
    Aᴴ = Aᵀ := Matrix.ext fun _ _ => star_trivial _

variable (m n α)

/-- `Matrix.conjTranspose` as an `AddEquiv` -/
@[simps apply]
/--
Definition of `conjTransposeAddEquiv` / `conjTransposeAddEquiv` 的定义

English:
definition conjTransposeAddEquiv
  signature: [AddMonoid α] [StarAddMonoid α]
  body: conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]

中文:
定义 conjTransposeAddEquiv
  签名: [加法幺半群 α] [StarAdd幺半群 α]
  定义体: conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]

Depends on / 依赖: conjTranspose
-/
def conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]
/--
theorem `conjTransposeAddEquiv_symm` / 定理 `conjTransposeAddEquiv_symm`

English:
theorem conjTransposeAddEquiv_symm
  given: [AddMonoid α] [StarAddMonoid α]
  proof: rfl

中文:
定理 conjTransposeAddEquiv_symm
  条件: [加法幺半群 α] [StarAdd幺半群 α]
  证明: rfl
-/
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl

variable {m n α}

/--
theorem `conjTranspose_list_sum` / 定理 `conjTranspose_list_sum`

English:
theorem conjTranspose_list_sum
  given: [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α))
  proof: map_list_sum (conjTransposeAddEquiv m n α) l

中文:
定理 conjTranspose_list_sum
  条件: [加法幺半群 α] [StarAdd幺半群 α] (l : 列表 (矩阵 m n α))
  证明: map_list_sum (conjTransposeAddEquiv m n α) l

Depends on / 依赖: conjTransposeAddEquiv, map_list_sum
-/
theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.sumᴴ = (l.map conjTranspose).sum :=
  map_list_sum (conjTransposeAddEquiv m n α) l

/--
theorem `conjTranspose_multiset_sum` / 定理 `conjTranspose_multiset_sum`

English:
theorem conjTranspose_multiset_sum
  statement: [AddCommMonoid α] [StarAddMonoid α]
  proof: (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

中文:
定理 conjTranspose_multiset_sum
  结论: [加法交换幺半群 α] [StarAdd幺半群 α]
  证明: (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

Depends on / 依赖: conjTransposeAddEquiv, map_multiset_sum, toAddMonoidHom, toAddMonoidHom.map_multiset_sum
-/
theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

/--
theorem `conjTranspose_sum` / 定理 `conjTranspose_sum`

English:
theorem conjTranspose_sum
  statement: [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
  proof: map_sum (conjTransposeAddEquiv m n α) _ s

中文:
定理 conjTranspose_sum
  结论: [加法交换幺半群 α] [StarAdd幺半群 α] {ι : 类型} (s : 有限集 ι)
  证明: map_sum (conjTransposeAddEquiv m n α) _ s

Depends on / 依赖: conjTransposeAddEquiv, map_sum
-/
theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
    (M : ι -> Matrix m n α) : (∑ i in s, M i)ᴴ = ∑ i in s, (M i)ᴴ :=
  map_sum (conjTransposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
/--
Definition of `conjTransposeLinearEquiv` / `conjTransposeLinearEquiv` 的定义

English:
definition conjTransposeLinearEquiv
  signature: [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
  body: conjTransposeAddEquiv m n α
  map_smul' := conjTranspose_smul

@[simp]

中文:
定义 conjTransposeLinearEquiv
  签名: [交换半环 R] [对合环 R] [加法交换幺半群 α] [StarAdd幺半群 α]
  定义体: conjTransposeAddEquiv m n α
  map_smul' := conjTranspose_smul

@[simp]

Depends on / 依赖: conjTransposeAddEquiv
-/
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α where
  __ := conjTransposeAddEquiv m n α
  map_smul' := conjTranspose_smul

@[simp]
/--
theorem `conjTransposeLinearEquiv_symm` / 定理 `conjTransposeLinearEquiv_symm`

English:
theorem conjTransposeLinearEquiv_symm
  statement: [CommSemiring R] [StarRing R] [AddCommMonoid α]
  proof: rfl

中文:
定理 conjTransposeLinearEquiv_symm
  结论: [交换半环 R] [对合环 R] [加法交换幺半群 α]
  证明: rfl
-/
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl

end ConjTranspose

section Star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: α] : Star (Matrix n n α) where star
  body: conjTranspose

中文:
实例 [对合
  签名: α] : 对合 (矩阵 n n α) where star
  定义体: conjTranspose

Depends on / 依赖: conjTranspose
-/
instance [Star α] : Star (Matrix n n α) where star := conjTranspose

/--
theorem `star_eq_conjTranspose` / 定理 `star_eq_conjTranspose`

English:
theorem star_eq_conjTranspose
  given: [Star α] (M : Matrix m m α)
  statement: star M = Mᴴ
  proof: rfl

@[simp]

中文:
定理 star_eq_conjTranspose
  条件: [对合 α] (M : 矩阵 m m α)
  结论: star M = Mᴴ
  证明: rfl

@[simp]
-/
theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl

@[simp]
/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: [Star α] (M : Matrix n n α) (i j)
  statement: (star M) i j = star (M j i)
  proof: rfl

中文:
定理 star_apply
  条件: [对合 α] (M : 矩阵 n n α) (i j)
  结论: (star M) i j = star (M j i)
  证明: rfl
-/
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: α] : InvolutiveStar (Matrix n n α) where
  body: conjTranspose_conjTranspose

中文:
实例 [InvolutiveStar
  签名: α] : InvolutiveStar (矩阵 n n α) where
  定义体: conjTranspose_conjTranspose

Depends on / 依赖: conjTranspose_conjTranspose
-/
instance [InvolutiveStar α] : InvolutiveStar (Matrix n n α) where
  star_involutive := conjTranspose_conjTranspose

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  body: conjTranspose_add

中文:
实例 [加法幺半群
  签名: α] [StarAdd幺半群 α] : StarAdd幺半群 (矩阵 n n α) where
  定义体: conjTranspose_add

Depends on / 依赖: conjTranspose_add
-/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  star_add := conjTranspose_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β) where
  body: conjTranspose_smul

中文:
实例 [对合
  签名: α] [对合 β] [标量乘法 α β] [对合模 α β] : 对合模 α (矩阵 n n β) where
  定义体: conjTranspose_smul

Depends on / 依赖: conjTranspose_smul
-/
instance [Star α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β) where
  star_smul := conjTranspose_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (Matrix n n α) where
  body: conjTranspose_add
  star_mul := conjTranspose_mul

@[deprecated (since := "2026-04-20")] protected alias star_mul := StarMul.star_mul

中文:
实例 [有限类型
  签名: n] [非幺非结合半环 α] [对合环 α] : 对合环 (矩阵 n n α) where
  定义体: conjTranspose_add
  star_mul := conjTranspose_mul

@[deprecated (since := "2026-04-20")] protected alias star_mul := StarMul.star_mul

Depends on / 依赖: conjTranspose_add
-/
instance [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (Matrix n n α) where
  star_add := conjTranspose_add
  star_mul := conjTranspose_mul

@[deprecated (since := "2026-04-20")] protected alias star_mul := StarMul.star_mul

end Star

@[simp]
/--
theorem `conjTranspose_submatrix` / 定理 `conjTranspose_submatrix`

English:
theorem conjTranspose_submatrix
  statement: [Star α] (A : Matrix m n α) (r : l -> m)
  proof: ext fun _ _ => rfl

中文:
定理 conjTranspose_submatrix
  结论: [对合 α] (A : 矩阵 m n α) (r : l -> m)
  证明: ext fun _ _ => rfl
-/
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r : l -> m)
    (c : o -> n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r :=
  ext fun _ _ => rfl

/--
theorem `conjTranspose_reindex` / 定理 `conjTranspose_reindex`

English:
theorem conjTranspose_reindex
  given: [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α)
  proof: rfl

中文:
定理 conjTranspose_reindex
  条件: [对合 α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : 矩阵 m n α)
  证明: rfl
-/
theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

variable (m α) in
/-- `Matrix.conjTranspose` as a `StarRingEquiv` to the opposite ring -/
@[simps!]
/--
Definition of `conjTransposeRingEquiv` / `conjTransposeRingEquiv` 的定义

English:
definition conjTransposeRingEquiv
  signature: [NonUnitalNonAssocSemiring α] [StarRing α] [Fintype m]
  body: (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv
map_mul' M N := (congrArg MulOpposite.op <| conjTranspose_mul M N).trans MulOpposite.op_mul ..
  map_star' _ := rfl

@[simp]

中文:
定义 conjTransposeRingEquiv
  签名: [非幺非结合半环 α] [对合环 α] [有限类型 m]
  定义体: (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv
map_mul' M N := (congrArg MulOpposite.op <| conjTranspose_mul M N).trans MulOpposite.op_mul ..
  map_star' _ := rfl

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.opAddEquiv, conjTransposeAddEquiv, opAddEquiv
-/
def conjTransposeRingEquiv [NonUnitalNonAssocSemiring α] [StarRing α] [Fintype m] :
    Matrix m m α ≃⋆+* (Matrix m m α)ᵐᵒᵖ where
  __ := (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv
map_mul' M N := (congrArg MulOpposite.op <| conjTranspose_mul M N).trans MulOpposite.op_mul ..
  map_star' _ := rfl

@[simp]
/--
theorem `conjTranspose_pow` / 定理 `conjTranspose_pow`

English:
theorem conjTranspose_pow
  statement: [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
  proof: MulOpposite.op_injective map_pow (conjTransposeRingEquiv m α) M k

中文:
定理 conjTranspose_pow
  结论: [半环 α] [对合环 α] [有限类型 m] [DecidableEq m] (M : 矩阵 m m α)
  证明: MulOpposite.op_injective map_pow (conjTransposeRingEquiv m α) M k

Depends on / 依赖: MulOpposite, MulOpposite.op_injective, conjTransposeRingEquiv, map_pow, op_injective
-/
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : Nat) : (M ^ k)ᴴ = Mᴴ ^ k :=
MulOpposite.op_injective map_pow (conjTransposeRingEquiv m α) M k

/--
theorem `conjTranspose_list_prod` / 定理 `conjTranspose_list_prod`

English:
theorem conjTranspose_list_prod
  statement: [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
  proof: (conjTransposeRingEquiv m α).unop_map_list_prod l

中文:
定理 conjTranspose_list_prod
  结论: [半环 α] [对合环 α] [有限类型 m] [DecidableEq m]
  证明: (conjTransposeRingEquiv m α).unop_map_list_prod l

Depends on / 依赖: conjTransposeRingEquiv, unop_map_list_prod
-/
theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l

variable (n α) in
/-- `Matrix.conjTranspose` as a `StarAlgEquiv` to the opposite ring -/
@[simps!]
/--
Definition of `conjTransposeAlgEquiv` / `conjTransposeAlgEquiv` 的定义

English:
definition conjTransposeAlgEquiv
  signature: [Fintype n] [CommSemiring R] [StarRing R] [TrivialStar R] [Semiring α]
  body: conjTransposeRingEquiv n α
  map_smul' r M := by
    change conjTransposeRingEquiv n α (r • M) = r • conjTransposeRingEquiv n α M
    simp

中文:
定义 conjTransposeAlgEquiv
  签名: [有限类型 n] [交换半环 R] [对合环 R] [TrivialStar R] [半环 α]
  定义体: conjTransposeRingEquiv n α
  map_smul' r M := by
    change conjTransposeRingEquiv n α (r • M) = r • conjTransposeRingEquiv n α M
    simp

Depends on / 依赖: conjTransposeRingEquiv
-/
def conjTransposeAlgEquiv [Fintype n] [CommSemiring R] [StarRing R] [TrivialStar R] [Semiring α]
    [StarRing α] [Algebra R α] [StarModule R α] : Matrix n n α ≃⋆ₐ[R] (Matrix n n α)ᵐᵒᵖ where
  __ := conjTransposeRingEquiv n α
  map_smul' r M := by
    change conjTransposeRingEquiv n α (r • M) = r • conjTransposeRingEquiv n α M
    simp

end Matrix
