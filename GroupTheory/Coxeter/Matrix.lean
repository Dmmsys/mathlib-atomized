/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Coxeter matrices

Let us say that a matrix (possibly an infinite matrix) is a *Coxeter matrix* (`CoxeterMatrix`) if
its entries are natural numbers, it is symmetric, its diagonal entries are equal to 1, and its
off-diagonal entries are not equal to 1. In this file, we define Coxeter matrices and provide some
ways of constructing them.

We also define the Coxeter matrices `CoxeterMatrix.Aₙ` (`n : ℕ`), `CoxeterMatrix.Bₙ` (`n : ℕ`),
`CoxeterMatrix.Dₙ` (`n : ℕ`), `CoxeterMatrix.I₂ₘ` (`m : ℕ`), `CoxeterMatrix.E₆`, `CoxeterMatrix.E₇`,
`CoxeterMatrix.E₈`, `CoxeterMatrix.F₄`, `CoxeterMatrix.G₂`, `CoxeterMatrix.H₃`, and
`CoxeterMatrix.H₄`. Up to reindexing, these are exactly the Coxeter matrices whose corresponding
Coxeter group (`CoxeterMatrix.coxeterGroup`) is finite and irreducible, although we do not prove
that in this file.

## Implementation details

In some texts on Coxeter groups, each entry $M_{i,i'}$ of a Coxeter matrix can be either a
positive integer or $\infty$. In our treatment of Coxeter matrices, we use the value $0$ instead of
$\infty$. This will turn out to have some fortunate consequences when defining the Coxeter group of
a Coxeter matrix and the standard geometric representation of a Coxeter group.

## Main definitions

* `CoxeterMatrix` : The type of symmetric matrices of natural numbers, with rows and columns
  indexed by a type `B`, whose diagonal entries are equal to 1 and whose off-diagonal entries are
  not equal to 1.
* `CoxeterMatrix.reindex` : Reindexes a Coxeter matrix by a bijection on the index type.
* `CoxeterMatrix.Aₙ` : Coxeter matrix for the symmetry group of the regular n-simplex.
* `CoxeterMatrix.Bₙ` : Coxeter matrix for the symmetry group of the regular n-hypercube
  and its dual, the regular n-orthoplex (or n-cross-polytope).
* `CoxeterMatrix.Dₙ` : Coxeter matrix for the symmetry group of the n-demicube.
* `CoxeterMatrix.I₂ₘ` : Coxeter matrix for the symmetry group of the regular (m + 2)-gon.
* `CoxeterMatrix.E₆` : Coxeter matrix for the symmetry group of the E₆ root polytope.
* `CoxeterMatrix.E₇` : Coxeter matrix for the symmetry group of the E₇ root polytope.
* `CoxeterMatrix.E₈` : Coxeter matrix for the symmetry group of the E₈ root polytope.
* `CoxeterMatrix.F₄` : Coxeter matrix for the symmetry group of the regular 4-polytope,
  the 24-cell.
* `CoxeterMatrix.G₂` : Coxeter matrix for the symmetry group of the regular hexagon.
* `CoxeterMatrix.H₃` : Coxeter matrix for the symmetry group of the regular dodecahedron
  and icosahedron.
* `CoxeterMatrix.H₄` : Coxeter matrix for the symmetry group of the regular 4-polytopes,
  the 120-cell and 600-cell.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

-/

@[expose] public section

/-- A *Coxeter matrix* is a symmetric matrix of natural numbers whose diagonal entries are equal to
1 and whose off-diagonal entries are not equal to 1. -/
@[ext]
/--
Definition of `CoxeterMatrix` / `CoxeterMatrix` 的定义

English:
structure CoxeterMatrix
  parameters: (B : Type*)
  axioms and operations (4):
    - M : Matrix B B Nat
    - isSymm : M.IsSymm  [default: by decide]
    - diagonal(i) : M i i = 1  [default: by decide]
    - off_diagonal(i i') : i != i' -> M i i' != 1  [default: by decide]

中文:
结构 余xeterMatrix
  参数: (B : 类型)
  公理与运算 (4 个):
    - M : 矩阵 B B 自然数
    - isSymm : M.是Symm  [默认: by decide]
    - diagonal(i) : M i i = 1  [默认: by decide]
    - off_diagonal(i i') : i != i' -> M i i' != 1  [默认: by decide]

Depends on / 依赖: diagonal, off_diagonal
-/
structure CoxeterMatrix (B : Type*) where
  /-- The underlying matrix of the Coxeter matrix. -/
  M : Matrix B B Nat
  isSymm : M.IsSymm := by decide
  diagonal i : M i i = 1 := by decide
  off_diagonal i i' : i != i' -> M i i' != 1 := by decide

namespace CoxeterMatrix

variable {B : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (CoxeterMatrix B) fun _ => (Matrix B B Nat)
  body: ⟨M⟩

中文:
实例 :
  签名: CoeFun (余xeterMatrix B) fun _ => (矩阵 B B 自然数)
  定义体: ⟨M⟩
-/
instance : CoeFun (CoxeterMatrix B) fun _ => (Matrix B B Nat) := ⟨M⟩

variable {B' : Type*} (e : B ≃ B') (M : CoxeterMatrix B)

attribute [simp] diagonal

/--
theorem `symmetric` / 定理 `symmetric`

English:
theorem symmetric
  given: (i i' : B)
  statement: M i i' = M i' i
  proof: M.isSymm.apply i' i

中文:
定理 symmetric
  条件: (i i' : B)
  结论: M i i' = M i' i
  证明: M.isSymm.apply i' i

Depends on / 依赖: M.isSymm.apply, isSymm
-/
theorem symmetric (i i' : B) : M i i' = M i' i := M.isSymm.apply i' i

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: : CoxeterMatrix B' where
  body: Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)

中文:
定义 reindex
  签名: : 余xeterMatrix B' where
  定义体: Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)
-/
protected def reindex : CoxeterMatrix B' where
  M := Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)

/--
theorem `reindex_apply` / 定理 `reindex_apply`

English:
theorem reindex_apply
  given: (i i' : B')
  statement: M.reindex e i i' = M (e.symm i) (e.symm i')
  proof: rfl

中文:
定理 reindex_apply
  条件: (i i' : B')
  结论: M.reindex e i i' = M (e.symm i) (e.symm i')
  证明: rfl
-/
theorem reindex_apply (i i' : B') : M.reindex e i i' = M (e.symm i) (e.symm i') := rfl

variable (n : Nat)

/--
Definition of `A` / `A` 的定义

English:
definition A
  signature: : CoxeterMatrix (Fin n) where
  body: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Aₙ := CoxeterMatrix.A

中文:
定义 A
  签名: : 余xeterMatrix (有限集 n) where
  定义体: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Aₙ := CoxeterMatrix.A
-/
protected def A : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Aₙ := CoxeterMatrix.A

/--
Definition of `B` / `B` 的定义

English:
definition B
  signature: : CoxeterMatrix (Fin n) where
  body: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Bₙ := CoxeterMatrix.B

中文:
定义 B
  签名: : 余xeterMatrix (有限集 n) where
  定义体: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Bₙ := CoxeterMatrix.B
-/
protected def B : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Bₙ := CoxeterMatrix.B

/--
Definition of `D` / `D` 的定义

English:
definition D
  signature: : CoxeterMatrix (Fin n) where
  body: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Dₙ := CoxeterMatrix.D

中文:
定义 D
  签名: : 余xeterMatrix (有限集 n) where
  定义体: Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Dₙ := CoxeterMatrix.D
-/
protected def D : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : Nat) + 1 = i ∨ (i : Nat) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

@[deprecated (since := "2026-03-25")] alias Dₙ := CoxeterMatrix.D

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: (m : Nat)
  body: Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

@[deprecated (since := "2026-03-25")] alias I₂ₙ := CoxeterMatrix.I

中文:
定义 I
  签名: (m : 自然数)
  定义体: Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

@[deprecated (since := "2026-03-25")] alias I₂ₙ := CoxeterMatrix.I
-/
protected def I (m : Nat) : CoxeterMatrix (Fin 2) where
  M := Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

@[deprecated (since := "2026-03-25")] alias I₂ₙ := CoxeterMatrix.I

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `E₆` / `E₆` 的定义

English:
definition E₆
  signature: : CoxeterMatrix (Fin 6) where
  body: !![1, 2, 3, 2, 2, 2;
          2, 1, 2, 3, 2, 2;
          3, 2, 1, 3, 2, 2;
          2, 3, 3, 1, 3, 2;
          2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 3, 1]

中文:
定义 E₆
  签名: : 余xeterMatrix (有限集 6) where
  定义体: !![1, 2, 3, 2, 2, 2;
          2, 1, 2, 3, 2, 2;
          3, 2, 1, 3, 2, 2;
          2, 3, 3, 1, 3, 2;
          2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 3, 1]
-/
def E₆ : CoxeterMatrix (Fin 6) where
  M := !![1, 2, 3, 2, 2, 2;
          2, 1, 2, 3, 2, 2;
          3, 2, 1, 3, 2, 2;
          2, 3, 3, 1, 3, 2;
          2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 3, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `E₇` / `E₇` 的定义

English:
definition E₇
  signature: : CoxeterMatrix (Fin 7) where
  body: !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 3, 1]

中文:
定义 E₇
  签名: : 余xeterMatrix (有限集 7) where
  定义体: !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 3, 1]
-/
def E₇ : CoxeterMatrix (Fin 7) where
  M := !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 3, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `E₈` / `E₈` 的定义

English:
definition E₈
  signature: : CoxeterMatrix (Fin 8) where
  body: !![1, 2, 3, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 3, 1]

中文:
定义 E₈
  签名: : 余xeterMatrix (有限集 8) where
  定义体: !![1, 2, 3, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 3, 1]
-/
def E₈ : CoxeterMatrix (Fin 8) where
  M := !![1, 2, 3, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 3, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `F₄` / `F₄` 的定义

English:
definition F₄
  signature: : CoxeterMatrix (Fin 4) where
  body: !![1, 3, 2, 2;
          3, 1, 4, 2;
          2, 4, 1, 3;
          2, 2, 3, 1]

中文:
定义 F₄
  签名: : 余xeterMatrix (有限集 4) where
  定义体: !![1, 3, 2, 2;
          3, 1, 4, 2;
          2, 4, 1, 3;
          2, 2, 3, 1]
-/
def F₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 4, 2;
          2, 4, 1, 3;
          2, 2, 3, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `G₂` / `G₂` 的定义

English:
definition G₂
  signature: : CoxeterMatrix (Fin 2) where
  body: !![1, 6;
          6, 1]

中文:
定义 G₂
  签名: : 余xeterMatrix (有限集 2) where
  定义体: !![1, 6;
          6, 1]
-/
def G₂ : CoxeterMatrix (Fin 2) where
  M := !![1, 6;
          6, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `H₃` / `H₃` 的定义

English:
definition H₃
  signature: : CoxeterMatrix (Fin 3) where
  body: !![1, 3, 2;
          3, 1, 5;
          2, 5, 1]

中文:
定义 H₃
  签名: : 余xeterMatrix (有限集 3) where
  定义体: !![1, 3, 2;
          3, 1, 5;
          2, 5, 1]
-/
def H₃ : CoxeterMatrix (Fin 3) where
  M := !![1, 3, 2;
          3, 1, 5;
          2, 5, 1]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `H₄` / `H₄` 的定义

English:
definition H₄
  signature: : CoxeterMatrix (Fin 4) where
  body: !![1, 3, 2, 2;
          3, 1, 3, 2;
          2, 3, 1, 5;
          2, 2, 5, 1]

中文:
定义 H₄
  签名: : 余xeterMatrix (有限集 4) where
  定义体: !![1, 3, 2, 2;
          3, 1, 3, 2;
          2, 3, 1, 5;
          2, 2, 5, 1]
-/
def H₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 3, 2;
          2, 3, 1, 5;
          2, 2, 5, 1]

end CoxeterMatrix
