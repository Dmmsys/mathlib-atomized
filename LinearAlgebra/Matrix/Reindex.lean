/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Snir Broshi
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Changing the index type of a matrix

This file concerns the map `Matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `Matrix.reindexAddEquiv R`: `Matrix.reindex` as an `AddEquiv` between `R`-matrices.
* `Matrix.reindexRingEquiv R`: `Matrix.reindex` as a `RingEquiv` between `R`-matrices.
* `Matrix.reindexLinearEquiv R A`: `Matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `Matrix.reindexAlgEquiv R A`: `Matrix.reindex` is an `R`-algebra equivalence between `A`-matrices.

## Tags

matrix, reindex

-/

@[expose] public section


namespace Matrix

open Equiv Matrix

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}
variable (R A : Type*)

section Add

variable [Add R]

/--
Definition of `reindexAddEquiv` / `reindexAddEquiv` 的定义

English:
definition reindexAddEquiv
  signature: (eₘ : m ≃ m') (eₙ : n ≃ n')
  body: reindex eₘ eₙ
  map_add' _ _ := rfl

@[simp]

中文:
定义 reindexAddEquiv
  签名: (eₘ : m ≃ m') (eₙ : n ≃ n')
  定义体: reindex eₘ eₙ
  map_add' _ _ := rfl

@[simp]

Depends on / 依赖: reindex
-/
def reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n R ≃+ Matrix m' n' R where
  __ := reindex eₘ eₙ
  map_add' _ _ := rfl

@[simp]
/--
theorem `coe_reindexAddEquiv` / 定理 `coe_reindexAddEquiv`

English:
theorem coe_reindexAddEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[simp]

中文:
定理 coe_reindexAddEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[simp]
-/
theorem coe_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexAddEquiv R eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
/--
theorem `toEquiv_reindexAddEquiv` / 定理 `toEquiv_reindexAddEquiv`

English:
theorem toEquiv_reindexAddEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[simp]

中文:
定理 toEquiv_reindexAddEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[simp]
-/
theorem toEquiv_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ : Matrix m n R ≃ Matrix m' n' R) = reindex eₘ eₙ :=
  rfl

@[simp]
/--
theorem `symm_reindexAddEquiv` / 定理 `symm_reindexAddEquiv`

English:
theorem symm_reindexAddEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[simp]

中文:
定理 symm_reindexAddEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[simp]
-/
theorem symm_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ).symm = reindexAddEquiv R eₘ.symm eₙ.symm :=
  rfl

@[simp]
/--
theorem `reindexAddEquiv_refl_refl` / 定理 `reindexAddEquiv_refl_refl`

English:
theorem reindexAddEquiv_refl_refl
  statement: reindexAddEquiv R (.refl m) (.refl n) = .refl _
  proof: rfl

@[simp]

中文:
定理 reindexAddEquiv_refl_refl
  结论: reindexAddEquiv R (.refl m) (.refl n) = .refl _
  证明: rfl

@[simp]
-/
theorem reindexAddEquiv_refl_refl : reindexAddEquiv R (.refl m) (.refl n) = .refl _ :=
  rfl

@[simp]
/--
theorem `reindexAddEquiv_trans_reindexAddEquiv` / 定理 `reindexAddEquiv_trans_reindexAddEquiv`

English:
theorem reindexAddEquiv_trans_reindexAddEquiv
  statement: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  proof: rfl

中文:
定理 reindexAddEquiv_trans_reindexAddEquiv
  结论: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  证明: rfl
-/
theorem reindexAddEquiv_trans_reindexAddEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
    (e₂' : n' ≃ n'') :
    .trans (reindexAddEquiv R e₁ e₂) (reindexAddEquiv R e₁' e₂') =
      reindexAddEquiv R (.trans e₁ e₁') (.trans e₂ e₂') :=
  rfl

end Add

section Mul

variable [Fintype m] [Fintype n] [Fintype o] [Mul R] [AddCommMonoid R]

/--
Definition of `reindexRingEquiv` / `reindexRingEquiv` 的定义

English:
definition reindexRingEquiv
  signature: (e : m ≃ n)
  body: reindexAddEquiv R e e
.symm map_mul' A B := submatrix_mul_equiv A B ..

@[simp]

中文:
定义 reindexRingEquiv
  签名: (e : m ≃ n)
  定义体: reindexAddEquiv R e e
.symm map_mul' A B := submatrix_mul_equiv A B ..

@[simp]

Depends on / 依赖: reindexAddEquiv
-/
def reindexRingEquiv (e : m ≃ n) : Matrix m m R ≃+* Matrix n n R where
  __ := reindexAddEquiv R e e
.symm map_mul' A B := submatrix_mul_equiv A B ..

@[simp]
/--
theorem `coe_reindexRingEquiv` / 定理 `coe_reindexRingEquiv`

English:
theorem coe_reindexRingEquiv
  given: (e : m ≃ n)
  statement: ⇑(reindexRingEquiv R e) = reindex e e
  proof: rfl

@[simp]

中文:
定理 coe_reindexRingEquiv
  条件: (e : m ≃ n)
  结论: ⇑(reindexRingEquiv R e) = reindex e e
  证明: rfl

@[simp]
-/
theorem coe_reindexRingEquiv (e : m ≃ n) : ⇑(reindexRingEquiv R e) = reindex e e :=
  rfl

@[simp]
/--
theorem `toEquiv_reindexRingEquiv` / 定理 `toEquiv_reindexRingEquiv`

English:
theorem toEquiv_reindexRingEquiv
  given: (e : m ≃ n)
  proof: rfl

@[simp]

中文:
定理 toEquiv_reindexRingEquiv
  条件: (e : m ≃ n)
  证明: rfl

@[simp]
-/
theorem toEquiv_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e : Matrix m m R ≃ Matrix n n R) = reindex e e :=
  rfl

@[simp]
/--
theorem `toAddEquiv_reindexRingEquiv` / 定理 `toAddEquiv_reindexRingEquiv`

English:
theorem toAddEquiv_reindexRingEquiv
  given: (e : m ≃ n)
  statement: reindexRingEquiv R e = reindexAddEquiv R e e
  proof: rfl

@[simp]

中文:
定理 toAddEquiv_reindexRingEquiv
  条件: (e : m ≃ n)
  结论: reindexRingEquiv R e = reindexAddEquiv R e e
  证明: rfl

@[simp]
-/
theorem toAddEquiv_reindexRingEquiv (e : m ≃ n) : reindexRingEquiv R e = reindexAddEquiv R e e :=
  rfl

@[simp]
/--
theorem `symm_reindexRingEquiv` / 定理 `symm_reindexRingEquiv`

English:
theorem symm_reindexRingEquiv
  given: (e : m ≃ n)
  proof: rfl

@[simp]

中文:
定理 symm_reindexRingEquiv
  条件: (e : m ≃ n)
  证明: rfl

@[simp]
-/
theorem symm_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e).symm = reindexRingEquiv R e.symm :=
  rfl

@[simp]
/--
theorem `reindexRingEquiv_refl` / 定理 `reindexRingEquiv_refl`

English:
theorem reindexRingEquiv_refl
  statement: reindexRingEquiv R (.refl n) = .refl _
  proof: rfl

@[simp]

中文:
定理 reindexRingEquiv_refl
  结论: reindexRingEquiv R (.refl n) = .refl _
  证明: rfl

@[simp]
-/
theorem reindexRingEquiv_refl : reindexRingEquiv R (.refl n) = .refl _ :=
  rfl

@[simp]
/--
theorem `reindexRingEquiv_trans_reindexRingEquiv` / 定理 `reindexRingEquiv_trans_reindexRingEquiv`

English:
theorem reindexRingEquiv_trans_reindexRingEquiv
  given: (e : m ≃ n) (e' : n ≃ o)
  proof: rfl

中文:
定理 reindexRingEquiv_trans_reindexRingEquiv
  条件: (e : m ≃ n) (e' : n ≃ o)
  证明: rfl

Depends on / 依赖: Equiv.Set.prod
-/
theorem reindexRingEquiv_trans_reindexRingEquiv (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexRingEquiv R e) (reindexRingEquiv R e') = reindexRingEquiv R (.trans e e') :=
  rfl

end Mul

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

/--
Definition of `reindexLinearEquiv` / `reindexLinearEquiv` 的定义

English:
definition reindexLinearEquiv
  signature: (eₘ : m ≃ m') (eₙ : n ≃ n')
  body: reindexAddEquiv A eₘ eₙ
  map_smul' _ _ := rfl

@[simp]

中文:
定义 reindexLinearEquiv
  签名: (eₘ : m ≃ m') (eₙ : n ≃ n')
  定义体: reindexAddEquiv A eₘ eₙ
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: Equiv.Set.univ, reindexAddEquiv
-/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A where
  __ := reindexAddEquiv A eₘ eₙ
  map_smul' _ _ := rfl

@[simp]
/--
theorem `coe_reindexLinearEquiv` / 定理 `coe_reindexLinearEquiv`

English:
theorem coe_reindexLinearEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[simp]

中文:
定理 coe_reindexLinearEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[simp]
-/
theorem coe_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexLinearEquiv R A eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
/--
theorem `toEquiv_reindexLinearEquiv` / 定理 `toEquiv_reindexLinearEquiv`

English:
theorem toEquiv_reindexLinearEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[simp]

中文:
定理 toEquiv_reindexLinearEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[simp]
-/
theorem toEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ : Matrix m n A ≃ Matrix m' n' A) = reindex eₘ eₙ :=
  rfl

@[simp]
/--
theorem `toAddEquiv_reindexLinearEquiv` / 定理 `toAddEquiv_reindexLinearEquiv`

English:
theorem toAddEquiv_reindexLinearEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[deprecated coe_reindexLinearEquiv (since := "2026-06-06")]

中文:
定理 toAddEquiv_reindexLinearEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[deprecated coe_reindexLinearEquiv (since := "2026-06-06")]
-/
theorem toAddEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    reindexLinearEquiv R A eₘ eₙ = reindexAddEquiv A eₘ eₙ :=
  rfl

@[deprecated coe_reindexLinearEquiv (since := "2026-06-06")]
/--
theorem `reindexLinearEquiv_apply` / 定理 `reindexLinearEquiv_apply`

English:
theorem reindexLinearEquiv_apply
  given: (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A)
  proof: by
  simp

@[simp]

中文:
定理 reindexLinearEquiv_apply
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A)
  证明: by
  simp

@[simp]
-/
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M := by
  simp

@[simp]
/--
theorem `symm_reindexLinearEquiv` / 定理 `symm_reindexLinearEquiv`

English:
theorem symm_reindexLinearEquiv
  given: (eₘ : m ≃ m') (eₙ : n ≃ n')
  proof: rfl

@[deprecated (since := "2026-06-06")] alias reindexLinearEquiv_symm := symm_reindexLinearEquiv

@[simp]

中文:
定理 symm_reindexLinearEquiv
  条件: (eₘ : m ≃ m') (eₙ : n ≃ n')
  证明: rfl

@[deprecated (since := "2026-06-06")] alias reindexLinearEquiv_symm := symm_reindexLinearEquiv

@[simp]
-/
theorem symm_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl

@[deprecated (since := "2026-06-06")] alias reindexLinearEquiv_symm := symm_reindexLinearEquiv

@[simp]
/--
theorem `reindexLinearEquiv_refl_refl` / 定理 `reindexLinearEquiv_refl_refl`

English:
theorem reindexLinearEquiv_refl_refl
  proof: rfl

@[simp]

中文:
定理 reindexLinearEquiv_refl_refl
  证明: rfl

@[simp]
-/
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  rfl

@[simp]
/--
theorem `reindexLinearEquiv_trans_reindexLinearEquiv` / 定理 `reindexLinearEquiv_trans_reindexLinearEquiv`

English:
theorem reindexLinearEquiv_trans_reindexLinearEquiv
  statement: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  proof: rfl

@[deprecated (since := "2026-06-06")]
alias reindexLinearEquiv_trans := reindexLinearEquiv_trans_reindexLinearEquiv

中文:
定理 reindexLinearEquiv_trans_reindexLinearEquiv
  结论: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  证明: rfl

@[deprecated (since := "2026-06-06")]
alias reindexLinearEquiv_trans := reindexLinearEquiv_trans_reindexLinearEquiv
-/
theorem reindexLinearEquiv_trans_reindexLinearEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
    (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
  rfl

@[deprecated (since := "2026-06-06")]
alias reindexLinearEquiv_trans := reindexLinearEquiv_trans_reindexLinearEquiv

/--
theorem `reindexLinearEquiv_comp` / 定理 `reindexLinearEquiv_comp`

English:
theorem reindexLinearEquiv_comp
  given: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
  proof: rfl

中文:
定理 reindexLinearEquiv_comp
  条件: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
  证明: rfl
-/
theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') :=
  rfl

/--
theorem `reindexLinearEquiv_comp_apply` / 定理 `reindexLinearEquiv_comp_apply`

English:
theorem reindexLinearEquiv_comp_apply
  statement: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
  proof: rfl

中文:
定理 reindexLinearEquiv_comp_apply
  结论: (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
  证明: rfl
-/
theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  rfl

/--
theorem `reindexLinearEquiv_one` / 定理 `reindexLinearEquiv_one`

English:
theorem reindexLinearEquiv_one
  given: [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m')
  proof: by
  simp

中文:
定理 reindexLinearEquiv_one
  条件: [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m')
  证明: by
  simp
-/
theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 := by
  simp

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

/--
theorem `reindexLinearEquiv_mul` / 定理 `reindexLinearEquiv_mul`

English:
theorem reindexLinearEquiv_mul
  statement: [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
  proof: by
  simp

中文:
定理 reindexLinearEquiv_mul
  结论: [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
  证明: by
  simp
-/
theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M * N) := by
  simp

/--
theorem `mul_reindexLinearEquiv_one` / 定理 `mul_reindexLinearEquiv_one`

English:
theorem mul_reindexLinearEquiv_one
  statement: [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
  proof: haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

中文:
定理 mul_reindexLinearEquiv_one
  结论: [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
  证明: haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

Depends on / 依赖: Fintype, Fintype.ofEquiv, mul_submatrix_one, ofEquiv
-/
theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M * (reindexLinearEquiv R A e₁ e₂ 1) =
      reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M :=
  haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

end Semiring

section Algebra

variable [CommSemiring R] [Fintype n] [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o] [Semiring A] [Algebra R A]

/--
Definition of `reindexAlgEquiv` / `reindexAlgEquiv` 的定义

English:
definition reindexAlgEquiv
  signature: (e : m ≃ n)
  body: reindexRingEquiv A e
  commutes' _ := by simp [algebraMap]

@[simp]

中文:
定义 reindexAlgEquiv
  签名: (e : m ≃ n)
  定义体: reindexRingEquiv A e
  commutes' _ := by simp [algebraMap]

@[simp]

Depends on / 依赖: reindexRingEquiv
-/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m A ≃ₐ[R] Matrix n n A where
  __ := reindexRingEquiv A e
  commutes' _ := by simp [algebraMap]

@[simp]
/--
theorem `coe_reindexAlgEquiv` / 定理 `coe_reindexAlgEquiv`

English:
theorem coe_reindexAlgEquiv
  given: (e : m ≃ n)
  statement: ⇑(reindexAlgEquiv R A e) = reindex e e
  proof: rfl

@[simp]

中文:
定理 coe_reindexAlgEquiv
  条件: (e : m ≃ n)
  结论: ⇑(reindexAlgEquiv R A e) = reindex e e
  证明: rfl

@[simp]
-/
theorem coe_reindexAlgEquiv (e : m ≃ n) : ⇑(reindexAlgEquiv R A e) = reindex e e :=
  rfl

@[simp]
/--
theorem `toEquiv_reindexAlgEquiv` / 定理 `toEquiv_reindexAlgEquiv`

English:
theorem toEquiv_reindexAlgEquiv
  given: (e : m ≃ n)
  proof: rfl

@[simp]

中文:
定理 toEquiv_reindexAlgEquiv
  条件: (e : m ≃ n)
  证明: rfl

@[simp]
-/
theorem toEquiv_reindexAlgEquiv (e : m ≃ n) :
    (reindexAlgEquiv R A e : Matrix m m A ≃ Matrix n n A) = reindex e e :=
  rfl

@[simp]
/--
theorem `toAddEquiv_reindexAlgEquiv` / 定理 `toAddEquiv_reindexAlgEquiv`

English:
theorem toAddEquiv_reindexAlgEquiv
  given: (e : m ≃ n)
  statement: reindexAlgEquiv R A e = reindexAddEquiv A e e
  proof: rfl

@[simp]

中文:
定理 toAddEquiv_reindexAlgEquiv
  条件: (e : m ≃ n)
  结论: reindexAlgEquiv R A e = reindexAddEquiv A e e
  证明: rfl

@[simp]
-/
theorem toAddEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexAddEquiv A e e :=
  rfl

@[simp]
/--
theorem `toRingEquiv_reindexAlgEquiv` / 定理 `toRingEquiv_reindexAlgEquiv`

English:
theorem toRingEquiv_reindexAlgEquiv
  given: (e : m ≃ n)
  statement: reindexAlgEquiv R A e = reindexRingEquiv A e
  proof: rfl

@[simp]

中文:
定理 toRingEquiv_reindexAlgEquiv
  条件: (e : m ≃ n)
  结论: reindexAlgEquiv R A e = reindexRingEquiv A e
  证明: rfl

@[simp]
-/
theorem toRingEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexRingEquiv A e :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_reindexAlgEquiv` / 定理 `toLinearEquiv_reindexAlgEquiv`

English:
theorem toLinearEquiv_reindexAlgEquiv
  given: (e : m ≃ n)
  proof: rfl

@[deprecated coe_reindexAlgEquiv (since := "2026-06-06")]

中文:
定理 toLinearEquiv_reindexAlgEquiv
  条件: (e : m ≃ n)
  证明: rfl

@[deprecated coe_reindexAlgEquiv (since := "2026-06-06")]
-/
theorem toLinearEquiv_reindexAlgEquiv (e : m ≃ n) :
    reindexAlgEquiv R A e = reindexLinearEquiv R A e e :=
  rfl

@[deprecated coe_reindexAlgEquiv (since := "2026-06-06")]
/--
theorem `reindexAlgEquiv_apply` / 定理 `reindexAlgEquiv_apply`

English:
theorem reindexAlgEquiv_apply
  given: (e : m ≃ n) (M : Matrix m m A)
  proof: by
  simp

@[simp]

中文:
定理 reindexAlgEquiv_apply
  条件: (e : m ≃ n) (M : Matrix m m A)
  证明: by
  simp

@[simp]
-/
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexAlgEquiv R A e M = reindex e e M := by
  simp

@[simp]
/--
theorem `symm_reindexAlgEquiv` / 定理 `symm_reindexAlgEquiv`

English:
theorem symm_reindexAlgEquiv
  given: (e : m ≃ n)
  proof: rfl

@[deprecated (since := "2026-06-06")] alias reindexAlgEquiv_symm := symm_reindexAlgEquiv

@[simp]

中文:
定理 symm_reindexAlgEquiv
  条件: (e : m ≃ n)
  证明: rfl

@[deprecated (since := "2026-06-06")] alias reindexAlgEquiv_symm := symm_reindexAlgEquiv

@[simp]
-/
theorem symm_reindexAlgEquiv (e : m ≃ n) :
    (reindexAlgEquiv R A e).symm = reindexAlgEquiv R A e.symm :=
  rfl

@[deprecated (since := "2026-06-06")] alias reindexAlgEquiv_symm := symm_reindexAlgEquiv

@[simp]
/--
theorem `reindexAlgEquiv_refl` / 定理 `reindexAlgEquiv_refl`

English:
theorem reindexAlgEquiv_refl
  statement: reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl
  proof: rfl

@[simp]

中文:
定理 reindexAlgEquiv_refl
  结论: reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl
  证明: rfl

@[simp]
-/
theorem reindexAlgEquiv_refl : reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl :=
  rfl

@[simp]
/--
theorem `reindexAlgEquiv_trans_reindexAlgEquiv` / 定理 `reindexAlgEquiv_trans_reindexAlgEquiv`

English:
theorem reindexAlgEquiv_trans_reindexAlgEquiv
  given: (e : m ≃ n) (e' : n ≃ o)
  proof: rfl

@[deprecated map_mul (since := "2026-06-06")]

中文:
定理 reindexAlgEquiv_trans_reindexAlgEquiv
  条件: (e : m ≃ n) (e' : n ≃ o)
  证明: rfl

@[deprecated map_mul (since := "2026-06-06")]
-/
theorem reindexAlgEquiv_trans_reindexAlgEquiv (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexAlgEquiv R A e) (reindexAlgEquiv R A e') = reindexAlgEquiv R A (.trans e e') :=
  rfl

@[deprecated map_mul (since := "2026-06-06")]
/--
theorem `reindexAlgEquiv_mul` / 定理 `reindexAlgEquiv_mul`

English:
theorem reindexAlgEquiv_mul
  given: (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A)
  proof: map_mul ..

中文:
定理 reindexAlgEquiv_mul
  条件: (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A)
  证明: map_mul ..

Depends on / 依赖: map_mul
-/
theorem reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A) :
    reindexAlgEquiv R A e (M * N) = reindexAlgEquiv R A e M * reindexAlgEquiv R A e N :=
  map_mul ..

end Algebra

/--
theorem `det_reindexLinearEquiv_self` / 定理 `det_reindexLinearEquiv_self`

English:
theorem det_reindexLinearEquiv_self
  statement: [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
  proof: det_reindex_self e M

中文:
定理 det_reindexLinearEquiv_self
  结论: [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
  证明: det_reindex_self e M

Depends on / 依赖: det_reindex_self
-/
theorem det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M

/--
theorem `det_reindexAlgEquiv` / 定理 `det_reindexAlgEquiv`

English:
theorem det_reindexAlgEquiv
  statement: (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
  proof: det_reindex_self e A

中文:
定理 det_reindexAlgEquiv
  结论: (B : 类型) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
  证明: det_reindex_self e A

Depends on / 依赖: det_reindex_self
-/
theorem det_reindexAlgEquiv (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m B) :
    det (reindexAlgEquiv R B e A) = det A :=
  det_reindex_self e A

end Matrix
