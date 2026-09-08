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

/-- `Matrix.reindex` as an `AddEquiv` between `R`-matrices. -/
/-
**Matrix.reindexAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n R ≃+ Matrix m' n'
 R where __
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.reindex` as an `AddEquiv` between `R`-matrices.
-/
def reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n R ≃+ Matrix m' n' R where
  __ := reindex eₘ eₙ
  map_add' _ _ := rfl

@[simp]
/-
**Matrix.coe_reindexAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : ⇑(reindexAddEquiv R eₘ e
ₙ) = reindex eₘ eₙ
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexAddEquiv R eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
/-
**Matrix.toEquiv_reindexAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEquiv_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : (reindexAddEquiv R e
ₘ eₙ : Matrix m n R ≃ Matrix m' n' R) = reindex eₘ eₙ
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ : Matrix m n R ≃ Matrix m' n' R) = reindex eₘ eₙ :=
  rfl

@[simp]
/-
**Matrix.symm_reindexAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：symm_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : (reindexAddEquiv R eₘ e
ₙ).symm = reindexAddEquiv R eₘ.symm eₙ.symm
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ).symm = reindexAddEquiv R eₘ.symm eₙ.symm :=
  rfl

@[simp]
/-
**Matrix.reindexAddEquiv_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexAddEquiv_refl_refl : reindexAddEquiv R (.refl m) (.refl n) = .refl 
_
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindexAddEquiv_refl_refl : reindexAddEquiv R (.refl m) (.refl n) = .refl _ :=
  rfl

@[simp]
/-
**Matrix.reindexAddEquiv_trans_reindexAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：reindexAddEquiv_trans_reindexAddEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m
' ≃ m'') (e₂' : n' ≃ n'') : .trans (reindexAddEquiv R e₁ e₂) (reindexAddEquiv R 
e₁' e₂') = reindexAddEquiv R (.trans e₁ e₁') (.trans e₂ e₂')
参数：e₁ : m ≃ m'；e₂ : n ≃ n'；e₁' : m' ≃ m''；e₂' : n' ≃ n''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexAddEquiv_trans_reindexAddEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
    (e₂' : n' ≃ n'') :
    .trans (reindexAddEquiv R e₁ e₂) (reindexAddEquiv R e₁' e₂') =
      reindexAddEquiv R (.trans e₁ e₁') (.trans e₂ e₂') :=
  rfl

end Add

section Mul

variable [Fintype m] [Fintype n] [Fintype o] [Mul R] [AddCommMonoid R]

/-- `Matrix.reindex` as a `RingEquiv` between `R`-matrices. -/
/-
**Matrix.reindexRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindexRingEquiv (e : m ≃ n) : Matrix m m R ≃+* Matrix n n R where __
参数：e : m ≃ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.reindex` as a `RingEquiv` between `R`-matrices.
-/
def reindexRingEquiv (e : m ≃ n) : Matrix m m R ≃+* Matrix n n R where
  __ := reindexAddEquiv R e e
  map_mul' A B := submatrix_mul_equiv A B .. |>.symm

@[simp]
/-
**Matrix.coe_reindexRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_reindexRingEquiv (e : m ≃ n) : ⇑(reindexRingEquiv R e) = reindex e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reindexRingEquiv (e : m ≃ n) : ⇑(reindexRingEquiv R e) = reindex e e :=
  rfl

@[simp]
/-
**Matrix.toEquiv_reindexRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEquiv_reindexRingEquiv (e : m ≃ n) : (reindexRingEquiv R e : Matrix m m 
R ≃ Matrix n n R) = reindex e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e : Matrix m m R ≃ Matrix n n R) = reindex e e :=
  rfl

@[simp]
/-
**Matrix.toAddEquiv_reindexRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toAddEquiv_reindexRingEquiv (e : m ≃ n) : reindexRingEquiv R e = reindexAd
dEquiv R e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem toAddEquiv_reindexRingEquiv (e : m ≃ n) : reindexRingEquiv R e = reindexAddEquiv R e e :=
  rfl

@[simp]
/-
**Matrix.symm_reindexRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：symm_reindexRingEquiv (e : m ≃ n) : (reindexRingEquiv R e).symm = reindexR
ingEquiv R e.symm
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e).symm = reindexRingEquiv R e.symm :=
  rfl

@[simp]
/-
**Matrix.reindexRingEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexRingEquiv_refl : reindexRingEquiv R (.refl n) = .refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindexRingEquiv_refl : reindexRingEquiv R (.refl n) = .refl _ :=
  rfl

@[simp]
/-
**Matrix.reindexRingEquiv_trans_reindexRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix`。
形式化陈述：reindexRingEquiv_trans_reindexRingEquiv (e : m ≃ n) (e' : n ≃ o) : .trans 
(reindexRingEquiv R e) (reindexRingEquiv R e') = reindexRingEquiv R (.trans e e'
)
参数：e : m ≃ n；e' : n ≃ o。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexRingEquiv_trans_reindexRingEquiv (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexRingEquiv R e) (reindexRingEquiv R e') = reindexRingEquiv R (.trans e e') :=
  rfl

end Mul

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is a linear equivalence. -/
/-
**Matrix.reindexLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix
 m' n' A where __
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map that reindexes a matrix's rows and columns with equivalent types
,
`Matrix.reindex`, is a linear equivalence.
-/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A where
  __ := reindexAddEquiv A eₘ eₙ
  map_smul' _ _ := rfl

@[simp]
/-
**Matrix.coe_reindexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : ⇑(reindexLinearEquiv 
R A eₘ eₙ) = reindex eₘ eₙ
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexLinearEquiv R A eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
/-
**Matrix.toEquiv_reindexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : (reindexLinearEqu
iv R A eₘ eₙ : Matrix m n A ≃ Matrix m' n' A) = reindex eₘ eₙ
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ : Matrix m n A ≃ Matrix m' n' A) = reindex eₘ eₙ :=
  rfl

@[simp]
/-
**Matrix.toAddEquiv_reindexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toAddEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : reindexLinearE
quiv R A eₘ eₙ = reindexAddEquiv A eₘ eₙ
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem toAddEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    reindexLinearEquiv R A eₘ eₙ = reindexAddEquiv A eₘ eₙ :=
  rfl

@[deprecated coe_reindexLinearEquiv (since := "2026-06-06")]
/-
**Matrix.reindexLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) : 
reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M
参数：eₘ : m ≃ m'；eₙ : n ≃ n'；M : Matrix m n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M := by
  simp

@[simp]
/-
**Matrix.symm_reindexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：symm_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : (reindexLinearEquiv 
R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm
参数：eₘ : m ≃ m'；eₙ : n ≃ n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl

@[deprecated (since := "2026-06-06")] alias reindexLinearEquiv_symm := symm_reindexLinearEquiv

@[simp]
/-
**Matrix.reindexLinearEquiv_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_refl_refl : reindexLinearEquiv R A (Equiv.refl m) (Equi
v.refl n) = LinearEquiv.refl R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  rfl

@[simp]
/-
**Matrix.reindexLinearEquiv_trans_reindexLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix`。
形式化陈述：reindexLinearEquiv_trans_reindexLinearEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e
₁' : m' ≃ m'') (e₂' : n' ≃ n'') : (reindexLinearEquiv R A e₁ e₂).trans (reindexL
inearEquiv R A e₁' e₂') = (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') 
: _ ≃ₗ[R] _)
参数：e₁ : m ≃ m'；e₂ : n ≃ n'；e₁' : m' ≃ m''；e₂' : n' ≃ n''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexLinearEquiv_trans_reindexLinearEquiv (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
    (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
  rfl

@[deprecated (since := "2026-06-06")]
alias reindexLinearEquiv_trans := reindexLinearEquiv_trans_reindexLinearEquiv
/-
**Matrix.reindexLinearEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' 
: n' ≃ n'') : reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ = re
indexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂')
参数：e₁ : m ≃ m'；e₂ : n ≃ n'；e₁' : m' ≃ m''；e₂' : n' ≃ n''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') :=
  rfl
/-
**Matrix.reindexLinearEquiv_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
 (e₂' : n' ≃ n'') (M : Matrix m n A) : (reindexLinearEquiv R A e₁' e₂') (reindex
LinearEquiv R A e₁ e₂ M) = reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') 
M
参数：e₁ : m ≃ m'；e₂ : n ≃ n'；e₁' : m' ≃ m''；e₂' : n' ≃ n''；M : Matrix m n A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  rfl
/-
**Matrix.reindexLinearEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m
') : reindexLinearEquiv R A e e (1 : Matrix m m A) = 1
参数：e : m ≃ m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_one_equiv`：submatrix_one_equiv [Zero α] [One α] [Decida
bleEq m] [DecidableEq l] (e : l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 := by
  simp

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

/-
**Matrix.reindexLinearEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n'
) (eₒ : o ≃ o') (M : Matrix m n A) (N : Matrix n o A) : reindexLinearEquiv R A e
ₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N = reindexLinearEquiv R A eₘ eₒ (M * N)
参数：eₘ : m ≃ m'；eₙ : n ≃ n'；eₒ : o ≃ o'；M : Matrix m n A；N : Matrix n o A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M * N) := by
  simp
/-
**Matrix.mul_reindexLinearEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : 
o ≃ n') (M : Matrix m n A) : M * (reindexLinearEquiv R A e₁ e₂ 1) = reindexLinea
rEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M
参数：e₁ : o ≃ n；e₂ : o ≃ n'；M : Matrix m n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_submatrix_one`：mul_submatrix_one [Fintype n] [Finite o] [NonA
ssocSemiring α] [DecidableEq o] (e₁ : n ≃ o) (e₂ : l -> o) (M : Matrix m n α) : 
M * (1 : Matri…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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

/-- For square matrices with coefficients in an algebra over a commutative semiring, the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of algebras. -/
/-
**Matrix.reindexAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindexAlgEquiv (e : m ≃ n) : Matrix m m A ≃ₐ[R] Matrix n n A where __
参数：e : m ≃ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For square matrices with coefficients in an algebra over a commutative semiring,
 the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of algebras.
-/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m A ≃ₐ[R] Matrix n n A where
  __ := reindexRingEquiv A e
  commutes' _ := by simp [algebraMap]

@[simp]
/-
**Matrix.coe_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_reindexAlgEquiv (e : m ≃ n) : ⇑(reindexAlgEquiv R A e) = reindex e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reindexAlgEquiv (e : m ≃ n) : ⇑(reindexAlgEquiv R A e) = reindex e e :=
  rfl

@[simp]
/-
**Matrix.toEquiv_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEquiv_reindexAlgEquiv (e : m ≃ n) : (reindexAlgEquiv R A e : Matrix m m 
A ≃ Matrix n n A) = reindex e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_reindexAlgEquiv (e : m ≃ n) :
    (reindexAlgEquiv R A e : Matrix m m A ≃ Matrix n n A) = reindex e e :=
  rfl

@[simp]
/-
**Matrix.toAddEquiv_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toAddEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexAd
dEquiv A e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `AlgEquivClass.toLinearEquivClass`：∀ (F : Type u_1) (R : Type u_2) (A : T
ype u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Semiring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem toAddEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexAddEquiv A e e :=
  rfl

@[simp]
/-
**Matrix.toRingEquiv_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toRingEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexR
ingEquiv A e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexRingEquiv A e :=
  rfl

@[simp]
/-
**Matrix.toLinearEquiv_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toLinearEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reinde
xLinearEquiv R A e e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_reindexAlgEquiv (e : m ≃ n) :
    reindexAlgEquiv R A e = reindexLinearEquiv R A e e :=
  rfl

@[deprecated coe_reindexAlgEquiv (since := "2026-06-06")]
/-
**Matrix.reindexAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) : reindexAlgEquiv R A
 e M = reindex e e M
参数：e : m ≃ n；M : Matrix m m A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexAlgEquiv R A e M = reindex e e M := by
  simp

@[simp]
/-
**Matrix.symm_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：symm_reindexAlgEquiv (e : m ≃ n) : (reindexAlgEquiv R A e).symm = reindexA
lgEquiv R A e.symm
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_reindexAlgEquiv (e : m ≃ n) :
    (reindexAlgEquiv R A e).symm = reindexAlgEquiv R A e.symm :=
  rfl

@[deprecated (since := "2026-06-06")] alias reindexAlgEquiv_symm := symm_reindexAlgEquiv

@[simp]
/-
**Matrix.reindexAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexAlgEquiv_refl : reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindexAlgEquiv_refl : reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl :=
  rfl

@[simp]
/-
**Matrix.reindexAlgEquiv_trans_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：reindexAlgEquiv_trans_reindexAlgEquiv (e : m ≃ n) (e' : n ≃ o) : .trans (r
eindexAlgEquiv R A e) (reindexAlgEquiv R A e') = reindexAlgEquiv R A (.trans e e
')
参数：e : m ≃ n；e' : n ≃ o。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexAlgEquiv_trans_reindexAlgEquiv (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexAlgEquiv R A e) (reindexAlgEquiv R A e') = reindexAlgEquiv R A (.trans e e') :=
  rfl

@[deprecated map_mul (since := "2026-06-06")]
/-
**Matrix.reindexAlgEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A) : re
indexAlgEquiv R A e (M * N) = reindexAlgEquiv R A e M * reindexAlgEquiv R A e N
参数：e : m ≃ n；M : Matrix m m A；N : Matrix m m A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A) :
    reindexAlgEquiv R A e (M * N) = reindexAlgEquiv R A e M * reindexAlgEquiv R A e N :=
  map_mul ..

end Algebra

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
/-
**Matrix.det_reindexLinearEquiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fint
ype n] [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv 
R R e e M) = det M
参数：e : m ≃ n；M : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A

--- 原说明 ---
Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
/-
**Matrix.det_reindexAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_reindexAlgEquiv (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B
] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matri
x m m B) : det (reindexAlgEquiv R B e A) = det A
参数：B : Type*；e : m ≃ n；A : Matrix m m B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A

--- 原说明 ---
Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexAlgEquiv (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m B) :
    det (reindexAlgEquiv R B e A) = det A :=
  det_reindex_self e A

end Matrix

