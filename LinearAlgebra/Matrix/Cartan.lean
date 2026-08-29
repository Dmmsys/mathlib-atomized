/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NormDet

/-!
# Cartan matrices

This file defines Cartan matrices for simple Lie algebras, both the exceptional types
(E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D).

## Main definitions

### Exceptional types
* `CartanMatrix.E₆` : The Cartan matrix of type E₆
* `CartanMatrix.E₇` : The Cartan matrix of type E₇
* `CartanMatrix.E₈` : The Cartan matrix of type E₈
* `CartanMatrix.F₄` : The Cartan matrix of type F₄
* `CartanMatrix.G₂` : The Cartan matrix of type G₂

### Classical types
* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

/-! ### Exceptional Cartan matrices -/

/--
Definition of `E₆` / `E₆` 的定义

English:
definition E₆
  signature: : Matrix (Fin 6) (Fin 6) Int
  body: !![ 2, 0, -1, 0, 0, 0;
      0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
      0, -1, -1, 2, -1, 0;
      0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, -1, 2]

中文:
定义 E₆
  签名: : 矩阵 (有限集 6) (有限集 6) 整数
  定义体: !![ 2, 0, -1, 0, 0, 0;
      0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
      0, -1, -1, 2, -1, 0;
      0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, -1, 2]
-/
def E₆ : Matrix (Fin 6) (Fin 6) Int :=
  !![ 2, 0, -1, 0, 0, 0;
      0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
      0, -1, -1, 2, -1, 0;
      0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, -1, 2]

/--
Definition of `E₇` / `E₇` 的定义

English:
definition E₇
  signature: : Matrix (Fin 7) (Fin 7) Int
  body: !![ 2, 0, -1, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0;
      0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, -1, 2]

中文:
定义 E₇
  签名: : 矩阵 (有限集 7) (有限集 7) 整数
  定义体: !![ 2, 0, -1, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0;
      0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, -1, 2]
-/
def E₇ : Matrix (Fin 7) (Fin 7) Int :=
  !![ 2, 0, -1, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0;
      0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, -1, 2]

/--
Definition of `E₈` / `E₈` 的定义

English:
definition E₈
  signature: : Matrix (Fin 8) (Fin 8) Int
  body: !![ 2, 0, -1, 0, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0, 0;
      0, 0, 0, -1, 2, -1, 0, 0;
      0, 0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, 0, -1, 2]

中文:
定义 E₈
  签名: : 矩阵 (有限集 8) (有限集 8) 整数
  定义体: !![ 2, 0, -1, 0, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0, 0;
      0, 0, 0, -1, 2, -1, 0, 0;
      0, 0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, 0, -1, 2]
-/
def E₈ : Matrix (Fin 8) (Fin 8) Int :=
  !![ 2, 0, -1, 0, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
      0, -1, -1, 2, -1, 0, 0, 0;
      0, 0, 0, -1, 2, -1, 0, 0;
      0, 0, 0, 0, -1, 2, -1, 0;
      0, 0, 0, 0, 0, -1, 2, -1;
      0, 0, 0, 0, 0, 0, -1, 2]

/--
Definition of `F₄` / `F₄` 的定义

English:
definition F₄
  signature: : Matrix (Fin 4) (Fin 4) Int
  body: !![ 2, -1, 0, 0;
     -1, 2, -2, 0;
      0, -1, 2, -1;
      0, 0, -1, 2]

中文:
定义 F₄
  签名: : 矩阵 (有限集 4) (有限集 4) 整数
  定义体: !![ 2, -1, 0, 0;
     -1, 2, -2, 0;
      0, -1, 2, -1;
      0, 0, -1, 2]
-/
def F₄ : Matrix (Fin 4) (Fin 4) Int :=
  !![ 2, -1, 0, 0;
     -1, 2, -2, 0;
      0, -1, 2, -1;
      0, 0, -1, 2]

/--
Definition of `G₂` / `G₂` 的定义

English:
definition G₂
  signature: : Matrix (Fin 2) (Fin 2) Int
  body: !![ 2, -3;
     -1, 2]

中文:
定义 G₂
  签名: : 矩阵 (有限集 2) (有限集 2) 整数
  定义体: !![ 2, -3;
     -1, 2]
-/
def G₂ : Matrix (Fin 2) (Fin 2) Int :=
  !![ 2, -3;
     -1, 2]

/-! ### Classical Cartan matrices -/

/--
Definition of `A` / `A` 的定义

English:
definition A
  signature: (n : Nat)
  body: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

中文:
定义 A
  签名: (n : 自然数)
  定义体: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

Depends on / 依赖: Matrix, Matrix.of, i.val, j.val
-/
def A (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

/--
Definition of `B` / `B` 的定义

English:
definition B
  signature: (n : Nat)
  body: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

中文:
定义 B
  签名: (n : 自然数)
  定义体: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

Depends on / 依赖: Matrix, Matrix.of, i.val, j.val
-/
def B (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: (n : Nat)
  body: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

中文:
定义 C
  签名: (n : 自然数)
  定义体: Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

Depends on / 依赖: Matrix, Matrix.of, i.val, j.val
-/
def C (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

/--
Definition of `D` / `D` 的定义

English:
definition D
  signature: (n : Nat)
  body: Matrix.of fun i j =>
    if i = j then 2
    else if n <= 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

中文:
定义 D
  签名: (n : 自然数)
  定义体: Matrix.of fun i j =>
    if i = j then 2
    else if n <= 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

Depends on / 依赖: Matrix, Matrix.of, i.val, j.val
-/
def D (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j =>
    if i = j then 2
    else if n <= 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

/-! ### Properties -/

section Properties

variable (n : Nat)

/--
theorem `A_diag` / 定理 `A_diag`

English:
theorem A_diag
  statement: (A n).diag = 2
  proof: by ext; simp [A]

中文:
定理 A_diag
  结论: (A n).diag = 2
  证明: by ext; simp [A]
-/
@[simp] theorem A_diag : (A n).diag = 2 := by ext; simp [A]
/--
theorem `B_diag` / 定理 `B_diag`

English:
theorem B_diag
  given: (i : Fin n)
  statement: B n i i = 2
  proof: by simp [B, Matrix.of_apply]

中文:
定理 B_diag
  条件: (i : 有限集 n)
  结论: B n i i = 2
  证明: by simp [B, Matrix.of_apply]
-/
@[simp] theorem B_diag (i : Fin n) : B n i i = 2 := by simp [B, Matrix.of_apply]
/--
theorem `C_diag` / 定理 `C_diag`

English:
theorem C_diag
  given: (i : Fin n)
  statement: C n i i = 2
  proof: by simp [C, Matrix.of_apply]

中文:
定理 C_diag
  条件: (i : 有限集 n)
  结论: C n i i = 2
  证明: by simp [C, Matrix.of_apply]
-/
@[simp] theorem C_diag (i : Fin n) : C n i i = 2 := by simp [C, Matrix.of_apply]
/--
theorem `D_diag` / 定理 `D_diag`

English:
theorem D_diag
  given: (i : Fin n)
  statement: D n i i = 2
  proof: by simp [D, Matrix.of_apply]

中文:
定理 D_diag
  条件: (i : 有限集 n)
  结论: D n i i = 2
  证明: by simp [D, Matrix.of_apply]
-/
@[simp] theorem D_diag (i : Fin n) : D n i i = 2 := by simp [D, Matrix.of_apply]

/--
theorem `A_apply_le_zero_of_ne` / 定理 `A_apply_le_zero_of_ne`

English:
theorem A_apply_le_zero_of_ne
  given: (i j : Fin n) (h : i != j)
  statement: A n i j <= 0
  proof: by
  simp only [A, Matrix.of_apply]; split_ifs <;> omega

中文:
定理 A_apply_le_zero_of_ne
  条件: (i j : 有限集 n) (h : i != j)
  结论: A n i j <= 0
  证明: by
  simp only [A, Matrix.of_apply]; split_ifs <;> omega

Depends on / 依赖: Matrix, Matrix.of_apply, of_apply, split_ifs
-/
theorem A_apply_le_zero_of_ne (i j : Fin n) (h : i != j) : A n i j <= 0 := by
  simp only [A, Matrix.of_apply]; split_ifs <;> omega

/--
theorem `B_off_diag_nonpos` / 定理 `B_off_diag_nonpos`

English:
theorem B_off_diag_nonpos
  given: (i j : Fin n) (h : i != j)
  statement: B n i j <= 0
  proof: by
  simp only [B, Matrix.of_apply]; split_ifs <;> omega

中文:
定理 B_off_diag_nonpos
  条件: (i j : 有限集 n) (h : i != j)
  结论: B n i j <= 0
  证明: by
  simp only [B, Matrix.of_apply]; split_ifs <;> omega

Depends on / 依赖: Matrix, Matrix.of_apply, of_apply, split_ifs
-/
theorem B_off_diag_nonpos (i j : Fin n) (h : i != j) : B n i j <= 0 := by
  simp only [B, Matrix.of_apply]; split_ifs <;> omega

/--
theorem `C_off_diag_nonpos` / 定理 `C_off_diag_nonpos`

English:
theorem C_off_diag_nonpos
  given: (i j : Fin n) (h : i != j)
  statement: C n i j <= 0
  proof: by
  simp only [C, Matrix.of_apply]; split_ifs <;> omega

中文:
定理 C_off_diag_nonpos
  条件: (i j : 有限集 n) (h : i != j)
  结论: C n i j <= 0
  证明: by
  simp only [C, Matrix.of_apply]; split_ifs <;> omega

Depends on / 依赖: Matrix, Matrix.of_apply, of_apply, split_ifs
-/
theorem C_off_diag_nonpos (i j : Fin n) (h : i != j) : C n i j <= 0 := by
  simp only [C, Matrix.of_apply]; split_ifs <;> omega

/--
theorem `D_off_diag_nonpos` / 定理 `D_off_diag_nonpos`

English:
theorem D_off_diag_nonpos
  given: (i j : Fin n) (h : i != j)
  statement: D n i j <= 0
  proof: by
  simp only [D, Matrix.of_apply]; split_ifs <;> omega

中文:
定理 D_off_diag_nonpos
  条件: (i j : 有限集 n) (h : i != j)
  结论: D n i j <= 0
  证明: by
  simp only [D, Matrix.of_apply]; split_ifs <;> omega

Depends on / 依赖: Matrix, Matrix.of_apply, of_apply, split_ifs
-/
theorem D_off_diag_nonpos (i j : Fin n) (h : i != j) : D n i j <= 0 := by
  simp only [D, Matrix.of_apply]; split_ifs <;> omega


/--
theorem `A_transpose` / 定理 `A_transpose`

English:
theorem A_transpose
  statement: (A n).transpose = A n
  proof: by
  ext; simp only [A, transpose_apply, of_apply]; grind

中文:
定理 A_transpose
  结论: (A n).transpose = A n
  证明: by
  ext; simp only [A, transpose_apply, of_apply]; grind
-/
@[simp] theorem A_transpose : (A n).transpose = A n := by
  ext; simp only [A, transpose_apply, of_apply]; grind

/--
theorem `A_isSymm` / 定理 `A_isSymm`

English:
theorem A_isSymm
  statement: (A n).IsSymm
  proof: A_transpose n

中文:
定理 A_isSymm
  结论: (A n).是Symm
  证明: A_transpose n

Depends on / 依赖: A_transpose
-/
theorem A_isSymm : (A n).IsSymm := A_transpose n

/--
theorem `B_transpose` / 定理 `B_transpose`

English:
theorem B_transpose
  statement: (B n).transpose = C n
  proof: by
  ext; simp only [B, C, transpose_apply, of_apply]; grind

中文:
定理 B_transpose
  结论: (B n).transpose = C n
  证明: by
  ext; simp only [B, C, transpose_apply, of_apply]; grind
-/
@[simp] theorem B_transpose : (B n).transpose = C n := by
  ext; simp only [B, C, transpose_apply, of_apply]; grind

/--
theorem `C_transpose` / 定理 `C_transpose`

English:
theorem C_transpose
  statement: (C n).transpose = B n
  proof: by
  rw [← (B n).transpose_transpose]; rw [B_transpose]

中文:
定理 C_transpose
  结论: (C n).transpose = B n
  证明: by
  rw [← (B n).transpose_transpose]; rw [B_transpose]
-/
@[simp] theorem C_transpose : (C n).transpose = B n := by
  rw [← (B n).transpose_transpose]; rw [B_transpose]

/--
theorem `D_transpose` / 定理 `D_transpose`

English:
theorem D_transpose
  statement: (D n).transpose = D n
  proof: by
  ext; simp only [D, transpose_apply, of_apply]; grind

中文:
定理 D_transpose
  结论: (D n).transpose = D n
  证明: by
  ext; simp only [D, transpose_apply, of_apply]; grind
-/
@[simp] theorem D_transpose : (D n).transpose = D n := by
  ext; simp only [D, transpose_apply, of_apply]; grind

/--
theorem `D_isSymm` / 定理 `D_isSymm`

English:
theorem D_isSymm
  statement: (D n).IsSymm
  proof: D_transpose n

中文:
定理 D_isSymm
  结论: (D n).是Symm
  证明: D_transpose n

Depends on / 依赖: D_transpose
-/
theorem D_isSymm : (D n).IsSymm := D_transpose n


/--
theorem `A_one` / 定理 `A_one`

English:
theorem A_one
  statement: A 1 = !![2]
  proof: by decide

中文:
定理 A_one
  结论: A 1 = !![2]
  证明: by decide
-/
theorem A_one : A 1 = !![2] := by decide

/--
theorem `A_two` / 定理 `A_two`

English:
theorem A_two
  statement: A 2 = !![ 2, -1;
  proof: by decide

中文:
定理 A_two
  结论: A 2 = !![ 2, -1;
  证明: by decide
-/
theorem A_two : A 2 = !![ 2, -1;
                         -1, 2] := by decide

/--
theorem `A_three` / 定理 `A_three`

English:
theorem A_three
  statement: A 3 = !![ 2, -1, 0;
  proof: by decide

中文:
定理 A_three
  结论: A 3 = !![ 2, -1, 0;
  证明: by decide
-/
theorem A_three : A 3 = !![ 2, -1, 0;
                           -1, 2, -1;
                            0, -1, 2] := by decide

/--
theorem `B_one` / 定理 `B_one`

English:
theorem B_one
  statement: B 1 = A 1
  proof: by decide

中文:
定理 B_one
  结论: B 1 = A 1
  证明: by decide
-/
theorem B_one : B 1 = A 1 := by decide

/--
theorem `C_one` / 定理 `C_one`

English:
theorem C_one
  statement: C 1 = A 1
  proof: by decide

中文:
定理 C_one
  结论: C 1 = A 1
  证明: by decide
-/
theorem C_one : C 1 = A 1 := by decide

/--
theorem `D_one` / 定理 `D_one`

English:
theorem D_one
  statement: D 1 = A 1
  proof: by decide

中文:
定理 D_one
  结论: D 1 = A 1
  证明: by decide
-/
theorem D_one : D 1 = A 1 := by decide

/--
theorem `D_two` / 定理 `D_two`

English:
theorem D_two
  statement: D 2 = !![2, 0;
  proof: by decide

中文:
定理 D_two
  结论: D 2 = !![2, 0;
  证明: by decide
-/
theorem D_two : D 2 = !![2, 0;
                         0, 2] := by decide

/--
theorem `B_two` / 定理 `B_two`

English:
theorem B_two
  statement: B 2 = !![ 2, -2;
  proof: by decide

中文:
定理 B_two
  结论: B 2 = !![ 2, -2;
  证明: by decide
-/
theorem B_two : B 2 = !![ 2, -2;
                         -1, 2] := by decide

/--
theorem `C_two` / 定理 `C_two`

English:
theorem C_two
  statement: C 2 = !![ 2, -1;
  proof: by decide

中文:
定理 C_two
  结论: C 2 = !![ 2, -1;
  证明: by decide
-/
theorem C_two : C 2 = !![ 2, -1;
                         -2, 2] := by decide

/--
theorem `D_three` / 定理 `D_three`

English:
theorem D_three
  statement: D 3 = !![ 2, -1, -1;
  proof: by decide

中文:
定理 D_three
  结论: D 3 = !![ 2, -1, -1;
  证明: by decide
-/
theorem D_three : D 3 = !![ 2, -1, -1;
                           -1, 2, 0;
                           -1, 0, 2] := by decide

/--
theorem `D_three'` / 定理 `D_three'`

English:
theorem D_three'
  statement: (D 3).reindex c[0, 1] c[0, 1] = A 3
  proof: by decide

中文:
定理 D_three'
  结论: (D 3).reindex c[0, 1] c[0, 1] = A 3
  证明: by decide
-/
theorem D_three' : (D 3).reindex c[0, 1] c[0, 1] = A 3 := by decide

/--
theorem `D_four` / 定理 `D_four`

English:
theorem D_four
  statement: D 4 = !![ 2, -1, 0, 0;
  proof: by decide

中文:
定理 D_four
  结论: D 4 = !![ 2, -1, 0, 0;
  证明: by decide
-/
theorem D_four : D 4 = !![ 2, -1, 0, 0;
                          -1, 2, -1, -1;
                           0, -1, 2, 0;
                           0, -1, 0, 2] := by decide




/--
theorem `E₆_diag` / 定理 `E₆_diag`

English:
theorem E₆_diag
  given: (i : Fin 6)
  statement: E₆ i i = 2
  proof: by fin_cases i <;> decide

中文:
定理 E₆_diag
  条件: (i : 有限集 6)
  结论: E₆ i i = 2
  证明: by fin_cases i <;> decide
-/
@[simp] theorem E₆_diag (i : Fin 6) : E₆ i i = 2 := by fin_cases i <;> decide

/--
theorem `E₇_diag` / 定理 `E₇_diag`

English:
theorem E₇_diag
  given: (i : Fin 7)
  statement: E₇ i i = 2
  proof: by fin_cases i <;> decide

中文:
定理 E₇_diag
  条件: (i : 有限集 7)
  结论: E₇ i i = 2
  证明: by fin_cases i <;> decide
-/
@[simp] theorem E₇_diag (i : Fin 7) : E₇ i i = 2 := by fin_cases i <;> decide

/--
theorem `E₈_diag` / 定理 `E₈_diag`

English:
theorem E₈_diag
  given: (i : Fin 8)
  statement: E₈ i i = 2
  proof: by fin_cases i <;> decide

中文:
定理 E₈_diag
  条件: (i : 有限集 8)
  结论: E₈ i i = 2
  证明: by fin_cases i <;> decide
-/
@[simp] theorem E₈_diag (i : Fin 8) : E₈ i i = 2 := by fin_cases i <;> decide

/--
theorem `F₄_diag` / 定理 `F₄_diag`

English:
theorem F₄_diag
  given: (i : Fin 4)
  statement: F₄ i i = 2
  proof: by fin_cases i <;> decide

中文:
定理 F₄_diag
  条件: (i : 有限集 4)
  结论: F₄ i i = 2
  证明: by fin_cases i <;> decide
-/
@[simp] theorem F₄_diag (i : Fin 4) : F₄ i i = 2 := by fin_cases i <;> decide

/--
theorem `G₂_diag` / 定理 `G₂_diag`

English:
theorem G₂_diag
  given: (i : Fin 2)
  statement: G₂ i i = 2
  proof: by fin_cases i <;> decide

中文:
定理 G₂_diag
  条件: (i : 有限集 2)
  结论: G₂ i i = 2
  证明: by fin_cases i <;> decide
-/
@[simp] theorem G₂_diag (i : Fin 2) : G₂ i i = 2 := by fin_cases i <;> decide



/--
theorem `E₆_off_diag_nonpos` / 定理 `E₆_off_diag_nonpos`

English:
theorem E₆_off_diag_nonpos
  given: (i j : Fin 6) (h : i != j)
  statement: E₆ i j <= 0
  proof: by
  fin_cases i <;> fin_cases j <;> simp_all [E₆]

中文:
定理 E₆_off_diag_nonpos
  条件: (i j : 有限集 6) (h : i != j)
  结论: E₆ i j <= 0
  证明: by
  fin_cases i <;> fin_cases j <;> simp_all [E₆]

Depends on / 依赖: fin_cases
-/
theorem E₆_off_diag_nonpos (i j : Fin 6) (h : i != j) : E₆ i j <= 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₆]

/--
theorem `E₇_off_diag_nonpos` / 定理 `E₇_off_diag_nonpos`

English:
theorem E₇_off_diag_nonpos
  given: (i j : Fin 7) (h : i != j)
  statement: E₇ i j <= 0
  proof: by
  fin_cases i <;> fin_cases j <;> simp_all [E₇]

中文:
定理 E₇_off_diag_nonpos
  条件: (i j : 有限集 7) (h : i != j)
  结论: E₇ i j <= 0
  证明: by
  fin_cases i <;> fin_cases j <;> simp_all [E₇]

Depends on / 依赖: fin_cases
-/
theorem E₇_off_diag_nonpos (i j : Fin 7) (h : i != j) : E₇ i j <= 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₇]

/--
theorem `E₈_off_diag_nonpos` / 定理 `E₈_off_diag_nonpos`

English:
theorem E₈_off_diag_nonpos
  given: (i j : Fin 8) (h : i != j)
  statement: E₈ i j <= 0
  proof: by
  fin_cases i <;> fin_cases j <;> simp_all [E₈]

中文:
定理 E₈_off_diag_nonpos
  条件: (i j : 有限集 8) (h : i != j)
  结论: E₈ i j <= 0
  证明: by
  fin_cases i <;> fin_cases j <;> simp_all [E₈]

Depends on / 依赖: fin_cases
-/
theorem E₈_off_diag_nonpos (i j : Fin 8) (h : i != j) : E₈ i j <= 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₈]

/--
theorem `F₄_off_diag_nonpos` / 定理 `F₄_off_diag_nonpos`

English:
theorem F₄_off_diag_nonpos
  given: (i j : Fin 4) (h : i != j)
  statement: F₄ i j <= 0
  proof: by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]

中文:
定理 F₄_off_diag_nonpos
  条件: (i j : 有限集 4) (h : i != j)
  结论: F₄ i j <= 0
  证明: by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]

Depends on / 依赖: fin_cases
-/
theorem F₄_off_diag_nonpos (i j : Fin 4) (h : i != j) : F₄ i j <= 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]

/--
theorem `G₂_off_diag_nonpos` / 定理 `G₂_off_diag_nonpos`

English:
theorem G₂_off_diag_nonpos
  given: (i j : Fin 2) (h : i != j)
  statement: G₂ i j <= 0
  proof: by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]

中文:
定理 G₂_off_diag_nonpos
  条件: (i j : 有限集 2) (h : i != j)
  结论: G₂ i j <= 0
  证明: by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]

Depends on / 依赖: fin_cases
-/
theorem G₂_off_diag_nonpos (i j : Fin 2) (h : i != j) : G₂ i j <= 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]


/--
theorem `E₆_transpose` / 定理 `E₆_transpose`

English:
theorem E₆_transpose
  statement: E₆.transpose = E₆
  proof: by decide

中文:
定理 E₆_transpose
  结论: E₆.transpose = E₆
  证明: by decide
-/
@[simp] theorem E₆_transpose : E₆.transpose = E₆ := by decide
/--
theorem `E₇_transpose` / 定理 `E₇_transpose`

English:
theorem E₇_transpose
  statement: E₇.transpose = E₇
  proof: by decide

中文:
定理 E₇_transpose
  结论: E₇.transpose = E₇
  证明: by decide
-/
@[simp] theorem E₇_transpose : E₇.transpose = E₇ := by decide
/--
theorem `E₈_transpose` / 定理 `E₈_transpose`

English:
theorem E₈_transpose
  statement: E₈.transpose = E₈
  proof: by decide

中文:
定理 E₈_transpose
  结论: E₈.transpose = E₈
  证明: by decide
-/
@[simp] theorem E₈_transpose : E₈.transpose = E₈ := by decide

/--
theorem `E₆_isSymm` / 定理 `E₆_isSymm`

English:
theorem E₆_isSymm
  statement: E₆.IsSymm
  proof: E₆_transpose

中文:
定理 E₆_isSymm
  结论: E₆.是Symm
  证明: E₆_transpose
-/
theorem E₆_isSymm : E₆.IsSymm := E₆_transpose
/--
theorem `E₇_isSymm` / 定理 `E₇_isSymm`

English:
theorem E₇_isSymm
  statement: E₇.IsSymm
  proof: E₇_transpose

中文:
定理 E₇_isSymm
  结论: E₇.是Symm
  证明: E₇_transpose
-/
theorem E₇_isSymm : E₇.IsSymm := E₇_transpose
/--
theorem `E₈_isSymm` / 定理 `E₈_isSymm`

English:
theorem E₈_isSymm
  statement: E₈.IsSymm
  proof: E₈_transpose

中文:
定理 E₈_isSymm
  结论: E₈.是Symm
  证明: E₈_transpose
-/
theorem E₈_isSymm : E₈.IsSymm := E₈_transpose


/--
theorem `G₂_det` / 定理 `G₂_det`

English:
theorem G₂_det
  statement: G₂.det = 1
  proof: by decide

中文:
定理 G₂_det
  结论: G₂.det = 1
  证明: by decide
-/
theorem G₂_det : G₂.det = 1 := by decide

/--
theorem `F₄_det` / 定理 `F₄_det`

English:
theorem F₄_det
  statement: F₄.det = 1
  proof: by decide

中文:
定理 F₄_det
  结论: F₄.det = 1
  证明: by decide
-/
theorem F₄_det : F₄.det = 1 := by decide


/--
theorem `E₆_det` / 定理 `E₆_det`

English:
theorem E₆_det
  statement: E₆.det = 3
  proof: by
  simp only [E₆, norm_det]

中文:
定理 E₆_det
  结论: E₆.det = 3
  证明: by
  simp only [E₆, norm_det]

Depends on / 依赖: norm_det
-/
theorem E₆_det : E₆.det = 3 := by
  simp only [E₆, norm_det]

/--
theorem `E₇_det` / 定理 `E₇_det`

English:
theorem E₇_det
  statement: E₇.det = 2
  proof: by
  simp only [E₇, norm_det]

中文:
定理 E₇_det
  结论: E₇.det = 2
  证明: by
  simp only [E₇, norm_det]

Depends on / 依赖: norm_det
-/
theorem E₇_det : E₇.det = 2 := by
  simp only [E₇, norm_det]

/--
theorem `E₈_det` / 定理 `E₈_det`

English:
theorem E₈_det
  statement: E₈.det = 1
  proof: by
  simp only [E₈, norm_det]

中文:
定理 E₈_det
  结论: E₈.det = 1
  证明: by
  simp only [E₈, norm_det]

Depends on / 依赖: norm_det
-/
theorem E₈_det : E₈.det = 1 := by
  simp only [E₈, norm_det]

/--
Definition of `_root_.Matrix.IsSimplyLaced` / `_root_.Matrix.IsSimplyLaced` 的定义

English:
definition _root_.Matrix.IsSimplyLaced
  signature: {ι : Type*} (A : Matrix ι ι Int)
  body: Pairwise fun i j => A i j = 0 ∨ A i j = -1

中文:
定义 _root_.矩阵.IsSimplyLaced
  签名: {ι : 类型} (A : 矩阵 ι ι 整数)
  定义体: Pairwise fun i j => A i j = 0 ∨ A i j = -1

Depends on / 依赖: Pairwise
-/
def _root_.Matrix.IsSimplyLaced {ι : Type*} (A : Matrix ι ι Int) : Prop :=
  Pairwise fun i j => A i j = 0 ∨ A i j = -1

set_option backward.isDefEq.respectTransparency.types false in
instance {ι : Type*} [Fintype ι] [DecidableEq ι] : DecidablePred (Matrix.IsSimplyLaced (ι := ι)) :=
inferInstanceAs
    DecidablePred fun A : Matrix ι ι Int => forall ⦃i j : ι⦄, i != j -> (fun i j => A i j = 0 ∨ A i j = -1) i j

/--
lemma `_root_.Matrix.isSimplyLaced_iff_of_linearOrder` / 引理 `_root_.Matrix.isSimplyLaced_iff_of_linearOrder`

English:
lemma _root_.Matrix.isSimplyLaced_iff_of_linearOrder
  proof: by
  constructor
  · intro h i j hij
    exact h hij.ne'
  · intro h i j hij
    obtain hij | hij := hij.lt_or_gt
    · simpa only [hA.apply i j] using h hij
    · exact h hij

中文:
引理 _root_.矩阵.isSimplyLaced_iff_of_linearOrder
  证明: by
  constructor
  · intro h i j hij
    exact h hij.ne'
  · intro h i j hij
    obtain hij | hij := hij.lt_or_gt
    · simpa only [hA.apply i j] using h hij
    · exact h hij

Depends on / 依赖: hA.apply, hij.lt_or_gt, hij.ne, lt_or_gt
-/
lemma _root_.Matrix.isSimplyLaced_iff_of_linearOrder
    {ι : Type*} [LinearOrder ι] (A : Matrix ι ι Int) (hA : A.IsSymm) :
    A.IsSimplyLaced ↔ forall ⦃i j : ι⦄, j < i -> (A i j = 0 ∨ A i j = -1) := by
  constructor
  · intro h i j hij
    exact h hij.ne'
  · intro h i j hij
    obtain hij | hij := hij.lt_or_gt
    · simpa only [hA.apply i j] using h hij
    · exact h hij

/--
theorem `_root_.Matrix.isSimplyLaced_transpose` / 定理 `_root_.Matrix.isSimplyLaced_transpose`

English:
theorem _root_.Matrix.isSimplyLaced_transpose
  given: {ι : Type*} (A : Matrix ι ι Int)
  proof: by
  rw [IsSimplyLaced]; rw [IsSimplyLaced]; rw [Pairwise]; rw [Pairwise]; rw [forall_comm]
  aesop

中文:
定理 _root_.矩阵.isSimplyLaced_transpose
  条件: {ι : 类型} (A : 矩阵 ι ι 整数)
  证明: by
  rw [IsSimplyLaced]; rw [IsSimplyLaced]; rw [Pairwise]; rw [Pairwise]; rw [forall_comm]
  aesop
-/
@[simp] theorem _root_.Matrix.isSimplyLaced_transpose {ι : Type*} (A : Matrix ι ι Int) :
    A.transpose.IsSimplyLaced ↔ A.IsSimplyLaced := by
  rw [IsSimplyLaced]; rw [IsSimplyLaced]; rw [Pairwise]; rw [Pairwise]; rw [forall_comm]
  aesop

/--
theorem `isSimplyLaced_A` / 定理 `isSimplyLaced_A`

English:
theorem isSimplyLaced_A
  given: (n : Nat)
  statement: IsSimplyLaced (A n)
  proof: by
  intro i j h
  simp only [A, of_apply]
  grind

中文:
定理 isSimplyLaced_A
  条件: (n : 自然数)
  结论: IsSimplyLaced (A n)
  证明: by
  intro i j h
  simp only [A, of_apply]
  grind

Depends on / 依赖: of_apply
-/
theorem isSimplyLaced_A (n : Nat) : IsSimplyLaced (A n) := by
  intro i j h
  simp only [A, of_apply]
  grind

/--
theorem `isSimplyLaced_D` / 定理 `isSimplyLaced_D`

English:
theorem isSimplyLaced_D
  given: (n : Nat)
  statement: IsSimplyLaced (D n)
  proof: by
  intro i j h
  simp only [D, of_apply]
  grind

中文:
定理 isSimplyLaced_D
  条件: (n : 自然数)
  结论: IsSimplyLaced (D n)
  证明: by
  intro i j h
  simp only [D, of_apply]
  grind

Depends on / 依赖: of_apply
-/
theorem isSimplyLaced_D (n : Nat) : IsSimplyLaced (D n) := by
  intro i j h
  simp only [D, of_apply]
  grind

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSimplyLaced_E₆` / 定理 `isSimplyLaced_E₆`

English:
theorem isSimplyLaced_E₆
  statement: IsSimplyLaced E₆
  proof: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₆ E₆_isSymm]; decide

中文:
定理 isSimplyLaced_E₆
  结论: IsSimplyLaced E₆
  证明: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₆ E₆_isSymm]; decide

Depends on / 依赖: Matrix, Matrix.isSimplyLaced_iff_of_linearOrder, isSimplyLaced_iff_of_linearOrder
-/
theorem isSimplyLaced_E₆ : IsSimplyLaced E₆ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₆ E₆_isSymm]; decide

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSimplyLaced_E₇` / 定理 `isSimplyLaced_E₇`

English:
theorem isSimplyLaced_E₇
  statement: IsSimplyLaced E₇
  proof: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₇ E₇_isSymm]; decide

中文:
定理 isSimplyLaced_E₇
  结论: IsSimplyLaced E₇
  证明: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₇ E₇_isSymm]; decide

Depends on / 依赖: Matrix, Matrix.isSimplyLaced_iff_of_linearOrder, isSimplyLaced_iff_of_linearOrder
-/
theorem isSimplyLaced_E₇ : IsSimplyLaced E₇ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₇ E₇_isSymm]; decide

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSimplyLaced_E₈` / 定理 `isSimplyLaced_E₈`

English:
theorem isSimplyLaced_E₈
  statement: IsSimplyLaced E₈
  proof: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₈ E₈_isSymm]; decide

中文:
定理 isSimplyLaced_E₈
  结论: IsSimplyLaced E₈
  证明: by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₈ E₈_isSymm]; decide

Depends on / 依赖: Matrix, Matrix.isSimplyLaced_iff_of_linearOrder, isSimplyLaced_iff_of_linearOrder
-/
theorem isSimplyLaced_E₈ : IsSimplyLaced E₈ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₈ E₈_isSymm]; decide


/--
theorem `not_isSimplyLaced_F₄` / 定理 `not_isSimplyLaced_F₄`

English:
theorem not_isSimplyLaced_F₄
  statement: ¬ IsSimplyLaced F₄
  proof: by decide

中文:
定理 not_isSimplyLaced_F₄
  结论: ¬ IsSimplyLaced F₄
  证明: by decide
-/
theorem not_isSimplyLaced_F₄ : ¬ IsSimplyLaced F₄ := by decide

/--
theorem `not_isSimplyLaced_G₂` / 定理 `not_isSimplyLaced_G₂`

English:
theorem not_isSimplyLaced_G₂
  statement: ¬ IsSimplyLaced G₂
  proof: by decide

中文:
定理 not_isSimplyLaced_G₂
  结论: ¬ IsSimplyLaced G₂
  证明: by decide
-/
theorem not_isSimplyLaced_G₂ : ¬ IsSimplyLaced G₂ := by decide

end Properties

end CartanMatrix

end
