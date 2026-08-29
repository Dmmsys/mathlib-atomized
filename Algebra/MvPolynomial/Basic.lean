/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Regular.Pow
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Order.SymmDiff
public meta import Mathlib.Tactic.Polynomial.Core

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `MvPolynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `MvPolynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`
* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`
* `C a` : the constant polynomial with value `a`
* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.
* `coeff s p` : the coefficient of `s` in `p`.

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `MvPolynomial σ R` is `(σ →₀ ℕ) →₀ R`; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/

@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

/--
Definition of `MvPolynomial` / `MvPolynomial` 的定义

English:
abbreviation MvPolynomial
  signature: (σ : Type*) (R : Type*) [CommSemiring R]
  body: AddMonoidAlgebra R (σ ->₀ Nat)

中文:
缩写 多元多项式
  签名: (σ : 类型) (R : 类型) [交换半环 R]
  定义体: AddMonoidAlgebra R (σ ->₀ Nat)

Depends on / 依赖: AddMonoidAlgebra
-/
abbrev MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ ->₀ Nat)

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : Nat} {n m : σ} {s : σ ->₀ Nat}

section CommSemiring
variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: (s : σ ->₀ Nat)
  body: AddMonoidAlgebra.lsingle s

中文:
定义 monomial
  签名: (s : σ ->₀ 自然数)
  定义体: AddMonoidAlgebra.lsingle s

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.lsingle, lsingle
-/
def monomial (s : σ ->₀ Nat) : R ->ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.lsingle s

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : MvPolynomial σ R) = monomial 0 1
  proof: rfl

中文:
定理 one_def
  结论: (1 : 多元多项式 σ R) = monomial 0 1
  证明: rfl
-/
theorem one_def : (1 : MvPolynomial σ R) = monomial 0 1 := rfl

/--
theorem `single_eq_monomial` / 定理 `single_eq_monomial`

English:
theorem single_eq_monomial
  given: (s : σ ->₀ Nat) (a : R)
  statement: .single s a = monomial s a
  proof: rfl

中文:
定理 single_eq_monomial
  条件: (s : σ ->₀ 自然数) (a : R)
  结论: .single s a = monomial s a
  证明: rfl
-/
theorem single_eq_monomial (s : σ ->₀ Nat) (a : R) : .single s a = monomial s a :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  statement: p * q = p.coeff.sum fun m a => q.coeff.sum fun n b => monomial (m + n) (a * b)
  proof: AddMonoidAlgebra.mul_def ..

中文:
定理 mul_def
  结论: p * q = p.coeff.求和 fun m a => q.coeff.求和 fun n b => monomial (m + n) (a * b)
  证明: AddMonoidAlgebra.mul_def ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mul_def, mul_def
-/
theorem mul_def : p * q = p.coeff.sum fun m a => q.coeff.sum fun n b => monomial (m + n) (a * b) :=
  AddMonoidAlgebra.mul_def ..

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* MvPolynomial σ R
  body: { singleZeroRingHom with toFun := monomial 0 }

中文:
定义 C
  签名: : R ->+* 多元多项式 σ R
  定义体: { singleZeroRingHom with toFun := monomial 0 }

Depends on / 依赖: monomial, singleZeroRingHom
-/
def C : R ->+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

@[simp, polynomial_post]
/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: algebraMap R (MvPolynomial σ R) = C
  proof: rfl

@[polynomial_pre]

中文:
定理 algebraMap_eq
  结论: algebraMap R (多元多项式 σ R) = C
  证明: rfl

@[polynomial_pre]
-/
theorem algebraMap_eq : algebraMap R (MvPolynomial σ R) = C :=
  rfl

@[polynomial_pre]
/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  statement: MvPolynomial.C = algebraMap R (MvPolynomial σ R)
  proof: rfl

中文:
定理 C_eq_algebraMap
  结论: 多元多项式.C = algebraMap R (多元多项式 σ R)
  证明: rfl
-/
theorem C_eq_algebraMap : MvPolynomial.C = algebraMap R (MvPolynomial σ R) :=
  rfl

variable {R σ}

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: [Algebra R S₁] (r : R)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: [代数 R S₁] (r : R)
  证明: rfl
-/
theorem algebraMap_apply [Algebra R S₁] (r : R) :
    algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) :=
  rfl

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: (n : σ)
  body: monomial (Finsupp.single n 1) 1

中文:
定义 X
  签名: (n : σ)
  定义体: monomial (Finsupp.single n 1) 1

Depends on / 依赖: Finsupp, Finsupp.single, monomial, single
-/
def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1

/--
theorem `monomial_left_injective` / 定理 `monomial_left_injective`

English:
theorem monomial_left_injective
  given: {r : R} (hr : r != 0)
  proof: single_left_injective hr

@[simp]

中文:
定理 monomial_left_injective
  条件: {r : R} (hr : r != 0)
  证明: single_left_injective hr

@[simp]

Depends on / 依赖: single_left_injective
-/
theorem monomial_left_injective {r : R} (hr : r != 0) :
    Function.Injective fun s : σ ->₀ Nat => monomial s r :=
  single_left_injective hr

@[simp]
/--
theorem `monomial_left_inj` / 定理 `monomial_left_inj`

English:
theorem monomial_left_inj
  given: {s t : σ ->₀ Nat} {r : R} (hr : r != 0)
  proof: single_left_inj hr

中文:
定理 monomial_left_inj
  条件: {s t : σ ->₀ 自然数} {r : R} (hr : r != 0)
  证明: single_left_inj hr

Depends on / 依赖: single_left_inj
-/
theorem monomial_left_inj {s t : σ ->₀ Nat} {r : R} (hr : r != 0) :
    monomial s r = monomial t r ↔ s = t :=
  single_left_inj hr

/--
theorem `C_apply` / 定理 `C_apply`

English:
theorem C_apply
  statement: (C a : MvPolynomial σ R) = monomial 0 a
  proof: rfl

@[simp]

中文:
定理 C_apply
  结论: (C a : 多元多项式 σ R) = monomial 0 a
  证明: rfl

@[simp]
-/
theorem C_apply : (C a : MvPolynomial σ R) = monomial 0 a :=
  rfl

@[simp]
/--
theorem `C_0` / 定理 `C_0`

English:
theorem C_0
  statement: C 0 = (0 : MvPolynomial σ R)
  proof: map_zero _

@[simp]

中文:
定理 C_0
  结论: C 0 = (0 : 多元多项式 σ R)
  证明: map_zero _

@[simp]

Depends on / 依赖: map_zero
-/
theorem C_0 : C 0 = (0 : MvPolynomial σ R) := map_zero _

@[simp]
/--
theorem `C_1` / 定理 `C_1`

English:
theorem C_1
  statement: C 1 = (1 : MvPolynomial σ R)
  proof: rfl

中文:
定理 C_1
  结论: C 1 = (1 : 多元多项式 σ R)
  证明: rfl
-/
theorem C_1 : C 1 = (1 : MvPolynomial σ R) :=
  rfl

/--
theorem `C_mul_monomial` / 定理 `C_mul_monomial`

English:
theorem C_mul_monomial
  statement: C a * monomial s a' = monomial s (a * a')
  proof: by
  have := single_mul_single 0 s a a'
  rw [zero_add] at this
  exact this

@[simp]

中文:
定理 C_mul_monomial
  结论: C a * monomial s a' = monomial s (a * a')
  证明: by
  have := single_mul_single 0 s a a'
  rw [zero_add] at this
  exact this

@[simp]

Depends on / 依赖: single_mul_single, zero_add
-/
theorem C_mul_monomial : C a * monomial s a' = monomial s (a * a') := by
  have := single_mul_single 0 s a a'
  rw [zero_add] at this
  exact this

@[simp]
/--
theorem `C_add` / 定理 `C_add`

English:
theorem C_add
  statement: (C (a + a') : MvPolynomial σ R) = C a + C a'
  proof: by simp

@[simp]

中文:
定理 C_add
  结论: (C (a + a') : 多元多项式 σ R) = C a + C a'
  证明: by simp

@[simp]
-/
theorem C_add : (C (a + a') : MvPolynomial σ R) = C a + C a' := by simp

@[simp]
/--
theorem `C_mul` / 定理 `C_mul`

English:
theorem C_mul
  statement: (C (a * a') : MvPolynomial σ R) = C a * C a'
  proof: C_mul_monomial.symm

@[simp]

中文:
定理 C_mul
  结论: (C (a * a') : 多元多项式 σ R) = C a * C a'
  证明: C_mul_monomial.symm

@[simp]

Depends on / 依赖: C_mul_monomial, C_mul_monomial.symm
-/
theorem C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a' :=
  C_mul_monomial.symm

@[simp]
/--
theorem `C_pow` / 定理 `C_pow`

English:
theorem C_pow
  given: (a : R) (n : Nat)
  statement: (C (a ^ n) : MvPolynomial σ R) = C a ^ n
  proof: map_pow _ _ _

@[grind inj]

中文:
定理 C_pow
  条件: (a : R) (n : 自然数)
  结论: (C (a ^ n) : 多元多项式 σ R) = C a ^ n
  证明: map_pow _ _ _

@[grind inj]

Depends on / 依赖: map_pow
-/
theorem C_pow (a : R) (n : Nat) : (C (a ^ n) : MvPolynomial σ R) = C a ^ n :=
  map_pow _ _ _

@[grind inj]
/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  given: (σ : Type*) (R : Type*) [CommSemiring R]
  proof: single_right_injective

中文:
定理 C_injective
  条件: (σ : 类型) (R : 类型) [交换半环 R]
  证明: single_right_injective

Depends on / 依赖: single_right_injective
-/
theorem C_injective (σ : Type*) (R : Type*) [CommSemiring R] :
    Function.Injective (C : R -> MvPolynomial σ R) :=
  single_right_injective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `C_surjective` / 定理 `C_surjective`

English:
theorem C_surjective
  given: {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ]
  proof: fun p => ⟨p.coeff 0, by apply AddMonoidAlgebra.ext; ext; simp [C_apply, ← single_eq_monomial]⟩

@[simp]

中文:
定理 C_surjective
  条件: {R : 类型} [交换半环 R] (σ : 类型) [是空 σ]
  证明: fun p => ⟨p.coeff 0, by apply AddMonoidAlgebra.ext; ext; simp [C_apply, ← single_eq_monomial]⟩

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.ext, C_apply, p.coeff, single_eq_monomial
-/
theorem C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] :
    Function.Surjective (C : R -> MvPolynomial σ R) :=
  fun p => ⟨p.coeff 0, by apply AddMonoidAlgebra.ext; ext; simp [C_apply, ← single_eq_monomial]⟩

@[simp]
/--
theorem `C_inj` / 定理 `C_inj`

English:
theorem C_inj
  given: {σ : Type*} (R : Type*) [CommSemiring R] (r s : R)
  proof: (C_injective σ R).eq_iff

中文:
定理 C_inj
  条件: {σ : 类型} (R : 类型) [交换半环 R] (r s : R)
  证明: (C_injective σ R).eq_iff

Depends on / 依赖: C_injective, eq_iff
-/
theorem C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) :
    (C r : MvPolynomial σ R) = C s ↔ r = s :=
  (C_injective σ R).eq_iff

/--
lemma `C_eq_zero` / 引理 `C_eq_zero`

English:
lemma C_eq_zero
  statement: (C a : MvPolynomial σ R) = 0 ↔ a = 0
  proof: by rw [← map_zero C, C_inj]

中文:
引理 C_eq_zero
  结论: (C a : 多元多项式 σ R) = 0 ↔ a = 0
  证明: by rw [← map_zero C, C_inj]
-/
@[simp] lemma C_eq_zero : (C a : MvPolynomial σ R) = 0 ↔ a = 0 := by rw [← map_zero C, C_inj]

/--
lemma `C_ne_zero` / 引理 `C_ne_zero`

English:
lemma C_ne_zero
  statement: (C a : MvPolynomial σ R) != 0 ↔ a != 0
  proof: C_eq_zero.ne

中文:
引理 C_ne_zero
  结论: (C a : 多元多项式 σ R) != 0 ↔ a != 0
  证明: C_eq_zero.ne

Depends on / 依赖: C_eq_zero, C_eq_zero.ne
-/
lemma C_ne_zero : (C a : MvPolynomial σ R) != 0 ↔ a != 0 :=
  C_eq_zero.ne

/--
Instance `nontrivial_of_nontrivial` / 实例 `nontrivial_of_nontrivial`

English:
instance nontrivial_of_nontrivial
  signature: (σ : Type*) (R : Type*) [CommSemiring R] [Nontrivial R]
  body: inferInstanceAs (Nontrivial <| AddMonoidAlgebra R (σ ->₀ Nat))

中文:
实例 nontrivial_of_nontrivial
  签名: (σ : 类型) (R : 类型) [交换半环 R] [非平凡 R]
  定义体: inferInstanceAs (Nontrivial <| AddMonoidAlgebra R (σ ->₀ Nat))

Depends on / 依赖: AddMonoidAlgebra, Nontrivial
-/
instance nontrivial_of_nontrivial (σ : Type*) (R : Type*) [CommSemiring R] [Nontrivial R] :
    Nontrivial (MvPolynomial σ R) :=
  inferInstanceAs (Nontrivial <| AddMonoidAlgebra R (σ ->₀ Nat))

/--
Instance `infinite_of_infinite` / 实例 `infinite_of_infinite`

English:
instance infinite_of_infinite
  signature: (σ : Type*) (R : Type*) [CommSemiring R] [Infinite R]
  body: Infinite.of_injective C (C_injective _ _)

中文:
实例 infinite_of_infinite
  签名: (σ : 类型) (R : 类型) [交换半环 R] [无限 R]
  定义体: Infinite.of_injective C (C_injective _ _)

Depends on / 依赖: C_injective, Infinite, Infinite.of_injective, of_injective
-/
instance infinite_of_infinite (σ : Type*) (R : Type*) [CommSemiring R] [Infinite R] :
    Infinite (MvPolynomial σ R) :=
  Infinite.of_injective C (C_injective _ _)

/--
Instance `infinite_of_nonempty` / 实例 `infinite_of_nonempty`

English:
instance infinite_of_nonempty
  signature: (σ : Type*) (R : Type*) [Nonempty σ] [CommSemiring R]
  body: Infinite.of_injective ((fun s : σ ->₀ Nat => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
 (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)

中文:
实例 infinite_of_nonempty
  签名: (σ : 类型) (R : 类型) [非空 σ] [交换半环 R]
  定义体: Infinite.of_injective ((fun s : σ ->₀ Nat => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
 (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)

Depends on / 依赖: Classical, Classical.arbitrary, Finsupp, Finsupp.single, Finsupp.single_injective, Infinite, Infinite.of_injective, arbitrary, monomial, monomial_left_injective, of_injective, one_ne_zero, single, single_injective
-/
instance infinite_of_nonempty (σ : Type*) (R : Type*) [Nonempty σ] [CommSemiring R]
    [Nontrivial R] : Infinite (MvPolynomial σ R) :=
  Infinite.of_injective ((fun s : σ ->₀ Nat => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
 (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : NoZeroDivisors (MvPolynomial σ R)
  body: inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ..))

中文:
实例 [无零因子
  签名: R] : 无零因子 (多元多项式 σ R)
  定义体: inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ..))

Depends on / 依赖: AddMonoidAlgebra, NoZeroDivisors
-/
instance [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) :=
  inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ..))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsCancelMulZero R] : IsCancelMulZero (MvPolynomial σ R)
  body: inferInstanceAs (IsCancelMulZero (AddMonoidAlgebra ..))

中文:
实例 [是消去加法
  签名: R] [是乘零消去 R] : 是乘零消去 (多元多项式 σ R)
  定义体: inferInstanceAs (IsCancelMulZero (AddMonoidAlgebra ..))

Depends on / 依赖: AddMonoidAlgebra, IsCancelMulZero
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero (MvPolynomial σ R) :=
  inferInstanceAs (IsCancelMulZero (AddMonoidAlgebra ..))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsDomain R] : IsDomain (MvPolynomial σ R) where

中文:
实例 [是消去加法
  签名: R] [是整环 R] : 是整环 (多元多项式 σ R) where
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain (MvPolynomial σ R) where

/--
theorem `C_eq_coe_nat` / 定理 `C_eq_coe_nat`

English:
theorem C_eq_coe_nat
  given: (n : Nat)
  statement: (C ↑n : MvPolynomial σ R) = n
  proof: by
  induction n <;> simp [*]

中文:
定理 C_eq_coe_nat
  条件: (n : 自然数)
  结论: (C ↑n : 多元多项式 σ R) = n
  证明: by
  induction n <;> simp [*]
-/
theorem C_eq_coe_nat (n : Nat) : (C ↑n : MvPolynomial σ R) = n := by
  induction n <;> simp [*]

/--
theorem `C_mul'` / 定理 `C_mul'`

English:
theorem C_mul'
  statement: MvPolynomial.C a * p = a • p
  proof: (Algebra.smul_def a p).symm

中文:
定理 C_mul'
  结论: 多元多项式.C a * p = a • p
  证明: (Algebra.smul_def a p).symm

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
theorem C_mul' : MvPolynomial.C a * p = a • p :=
  (Algebra.smul_def a p).symm

/--
theorem `smul_eq_C_mul` / 定理 `smul_eq_C_mul`

English:
theorem smul_eq_C_mul
  given: (p : MvPolynomial σ R) (a : R)
  statement: a • p = C a * p
  proof: C_mul'.symm

中文:
定理 smul_eq_C_mul
  条件: (p : 多元多项式 σ R) (a : R)
  结论: a • p = C a * p
  证明: C_mul'.symm

Depends on / 依赖: C_mul
-/
theorem smul_eq_C_mul (p : MvPolynomial σ R) (a : R) : a • p = C a * p :=
  C_mul'.symm

/--
theorem `C_eq_smul_one` / 定理 `C_eq_smul_one`

English:
theorem C_eq_smul_one
  statement: (C a : MvPolynomial σ R) = a • (1 : MvPolynomial σ R)
  proof: by
  rw [← C_mul']; rw [mul_one]

中文:
定理 C_eq_smul_one
  结论: (C a : 多元多项式 σ R) = a • (1 : 多元多项式 σ R)
  证明: by
  rw [← C_mul']; rw [mul_one]

Depends on / 依赖: C_mul, mul_one
-/
theorem C_eq_smul_one : (C a : MvPolynomial σ R) = a • (1 : MvPolynomial σ R) := by
  rw [← C_mul']; rw [mul_one]

/--
theorem `smul_monomial` / 定理 `smul_monomial`

English:
theorem smul_monomial
  given: {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁)
  proof: smul_single _ _ _

中文:
定理 smul_monomial
  条件: {S₁ : 类型} [SMulZero类 S₁ R] (r : S₁)
  证明: smul_single _ _ _

Depends on / 依赖: smul_single
-/
theorem smul_monomial {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁) :
    r • monomial s a = monomial s (r • a) := smul_single _ _ _

/--
theorem `X_injective` / 定理 `X_injective`

English:
theorem X_injective
  given: [Nontrivial R]
  statement: Function.Injective (X : σ -> MvPolynomial σ R)
  proof: (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]

中文:
定理 X_injective
  条件: [非平凡 R]
  结论: 函数.单射 (X : σ -> 多元多项式 σ R)
  证明: (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_left_injective, monomial_left_injective, one_ne_zero, single_left_injective
-/
theorem X_injective [Nontrivial R] : Function.Injective (X : σ -> MvPolynomial σ R) :=
  (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]
/--
theorem `X_inj` / 定理 `X_inj`

English:
theorem X_inj
  given: [Nontrivial R] (m n : σ)
  statement: X m = (X n : MvPolynomial σ R) ↔ m = n
  proof: X_injective.eq_iff

中文:
定理 X_inj
  条件: [非平凡 R] (m n : σ)
  结论: X m = (X n : 多元多项式 σ R) ↔ m = n
  证明: X_injective.eq_iff

Depends on / 依赖: X_injective, X_injective.eq_iff, eq_iff
-/
theorem X_inj [Nontrivial R] (m n : σ) : X m = (X n : MvPolynomial σ R) ↔ m = n :=
  X_injective.eq_iff

/--
theorem `monomial_pow` / 定理 `monomial_pow`

English:
theorem monomial_pow
  statement: monomial s a ^ e = monomial (e • s) (a ^ e)
  proof: AddMonoidAlgebra.single_pow ..

@[simp]

中文:
定理 monomial_pow
  结论: monomial s a ^ e = monomial (e • s) (a ^ e)
  证明: AddMonoidAlgebra.single_pow ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.single_pow, single_pow
-/
theorem monomial_pow : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow ..

@[simp]
/--
theorem `monomial_mul` / 定理 `monomial_mul`

English:
theorem monomial_mul
  given: {s s' : σ ->₀ Nat} {a b : R}
  proof: AddMonoidAlgebra.single_mul_single ..

中文:
定理 monomial_mul
  条件: {s s' : σ ->₀ 自然数} {a b : R}
  证明: AddMonoidAlgebra.single_mul_single ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.single_mul_single, single_mul_single
-/
theorem monomial_mul {s s' : σ ->₀ Nat} {a b : R} :
    monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single ..

variable (σ R)

/--
Definition of `monomialOneHom` / `monomialOneHom` 的定义

English:
definition monomialOneHom
  signature: : Multiplicative (σ ->₀ Nat) ->* MvPolynomial σ R
  body: AddMonoidAlgebra.of _ _

中文:
定义 monomialOneHom
  签名: : Multiplicative (σ ->₀ 自然数) ->* 多元多项式 σ R
  定义体: AddMonoidAlgebra.of _ _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.of
-/
def monomialOneHom : Multiplicative (σ ->₀ Nat) ->* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _

variable {σ R}

@[simp]
/--
theorem `monomialOneHom_apply` / 定理 `monomialOneHom_apply`

English:
theorem monomialOneHom_apply
  statement: monomialOneHom R σ s = (monomial s 1 : MvPolynomial σ R)
  proof: rfl

中文:
定理 monomialOneHom_apply
  结论: monomialOneHom R σ s = (monomial s 1 : 多元多项式 σ R)
  证明: rfl
-/
theorem monomialOneHom_apply : monomialOneHom R σ s = (monomial s 1 : MvPolynomial σ R) :=
  rfl

/--
theorem `X_pow_eq_monomial` / 定理 `X_pow_eq_monomial`

English:
theorem X_pow_eq_monomial
  statement: X n ^ e = monomial (Finsupp.single n e) (1 : R)
  proof: by
  simp [X, monomial_pow]

中文:
定理 X_pow_eq_monomial
  结论: X n ^ e = monomial (有限支撑.single n e) (1 : R)
  证明: by
  simp [X, monomial_pow]

Depends on / 依赖: monomial_pow
-/
theorem X_pow_eq_monomial : X n ^ e = monomial (Finsupp.single n e) (1 : R) := by
  simp [X, monomial_pow]

/--
theorem `monomial_add_single` / 定理 `monomial_add_single`

English:
theorem monomial_add_single
  statement: monomial (s + Finsupp.single n e) a = monomial s a * X n ^ e
  proof: by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [mul_one]

中文:
定理 monomial_add_single
  结论: monomial (s + 有限支撑.single n e) a = monomial s a * X n ^ e
  证明: by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [mul_one]

Depends on / 依赖: X_pow_eq_monomial, monomial_mul, mul_one
-/
theorem monomial_add_single : monomial (s + Finsupp.single n e) a = monomial s a * X n ^ e := by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [mul_one]

/--
theorem `monomial_single_add` / 定理 `monomial_single_add`

English:
theorem monomial_single_add
  statement: monomial (Finsupp.single n e + s) a = X n ^ e * monomial s a
  proof: by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [one_mul]

中文:
定理 monomial_single_add
  结论: monomial (有限支撑.single n e + s) a = X n ^ e * monomial s a
  证明: by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [one_mul]

Depends on / 依赖: X_pow_eq_monomial, monomial_mul, one_mul
-/
theorem monomial_single_add : monomial (Finsupp.single n e + s) a = X n ^ e * monomial s a := by
  rw [X_pow_eq_monomial]; rw [monomial_mul]; rw [one_mul]

/--
theorem `C_mul_X_pow_eq_monomial` / 定理 `C_mul_X_pow_eq_monomial`

English:
theorem C_mul_X_pow_eq_monomial
  given: {s : σ} {a : R} {n : Nat}
  proof: by
  rw [← zero_add (Finsupp.single s n)]; rw [monomial_add_single]; rw [C_apply]

中文:
定理 C_mul_X_pow_eq_monomial
  条件: {s : σ} {a : R} {n : 自然数}
  证明: by
  rw [← zero_add (Finsupp.single s n)]; rw [monomial_add_single]; rw [C_apply]

Depends on / 依赖: C_apply, Finsupp, Finsupp.single, monomial_add_single, single, zero_add
-/
theorem C_mul_X_pow_eq_monomial {s : σ} {a : R} {n : Nat} :
    C a * X s ^ n = monomial (Finsupp.single s n) a := by
  rw [← zero_add (Finsupp.single s n)]; rw [monomial_add_single]; rw [C_apply]

/--
theorem `C_mul_X_eq_monomial` / 定理 `C_mul_X_eq_monomial`

English:
theorem C_mul_X_eq_monomial
  given: {s : σ} {a : R}
  statement: C a * X s = monomial (Finsupp.single s 1) a
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

@[simp]

中文:
定理 C_mul_X_eq_monomial
  条件: {s : σ} {a : R}
  结论: C a * X s = monomial (有限支撑.single s 1) a
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, pow_one
-/
theorem C_mul_X_eq_monomial {s : σ} {a : R} : C a * X s = monomial (Finsupp.single s 1) a := by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

@[simp]
/--
theorem `monomial_zero` / 定理 `monomial_zero`

English:
theorem monomial_zero
  given: {s : σ ->₀ Nat}
  statement: monomial s (0 : R) = 0
  proof: single_zero _

@[simp]

中文:
定理 monomial_zero
  条件: {s : σ ->₀ 自然数}
  结论: monomial s (0 : R) = 0
  证明: single_zero _

@[simp]

Depends on / 依赖: single_zero
-/
theorem monomial_zero {s : σ ->₀ Nat} : monomial s (0 : R) = 0 := single_zero _

@[simp]
/--
theorem `monomial_zero'` / 定理 `monomial_zero'`

English:
theorem monomial_zero'
  statement: (monomial (0 : σ ->₀ Nat) : R -> MvPolynomial σ R) = C
  proof: rfl

@[simp]

中文:
定理 monomial_zero'
  结论: (monomial (0 : σ ->₀ 自然数) : R -> 多元多项式 σ R) = C
  证明: rfl

@[simp]
-/
theorem monomial_zero' : (monomial (0 : σ ->₀ Nat) : R -> MvPolynomial σ R) = C :=
  rfl

@[simp]
/--
theorem `monomial_eq_zero` / 定理 `monomial_eq_zero`

English:
theorem monomial_eq_zero
  given: {s : σ ->₀ Nat} {b : R}
  statement: monomial s b = 0 ↔ b = 0
  proof: single_eq_zero

@[simp]

中文:
定理 monomial_eq_zero
  条件: {s : σ ->₀ 自然数} {b : R}
  结论: monomial s b = 0 ↔ b = 0
  证明: single_eq_zero

@[simp]

Depends on / 依赖: single_eq_zero
-/
theorem monomial_eq_zero {s : σ ->₀ Nat} {b : R} : monomial s b = 0 ↔ b = 0 := single_eq_zero

@[simp]
/--
theorem `sum_monomial_eq` / 定理 `sum_monomial_eq`

English:
theorem sum_monomial_eq
  statement: {A : Type*} [AddCommMonoid A] {u : σ ->₀ Nat} {r : R} {b : (σ ->₀ Nat) -> R -> A}
  proof: Finsupp.sum_single_index w

@[simp]

中文:
定理 sum_monomial_eq
  结论: {A : 类型} [加法交换幺半群 A] {u : σ ->₀ 自然数} {r : R} {b : (σ ->₀ 自然数) -> R -> A}
  证明: Finsupp.sum_single_index w

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, sum_single_index
-/
theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] {u : σ ->₀ Nat} {r : R} {b : (σ ->₀ Nat) -> R -> A}
    (w : b u 0 = 0) : sum (monomial u r).coeff b = b u r :=
  Finsupp.sum_single_index w

@[simp]
/--
theorem `sum_C` / 定理 `sum_C`

English:
theorem sum_C
  given: {A : Type*} [AddCommMonoid A] {b : (σ ->₀ Nat) -> R -> A} (w : b 0 0 = 0)
  proof: sum_monomial_eq w

中文:
定理 sum_C
  条件: {A : 类型} [加法交换幺半群 A] {b : (σ ->₀ 自然数) -> R -> A} (w : b 0 0 = 0)
  证明: sum_monomial_eq w

Depends on / 依赖: sum_monomial_eq
-/
theorem sum_C {A : Type*} [AddCommMonoid A] {b : (σ ->₀ Nat) -> R -> A} (w : b 0 0 = 0) :
    sum (C a).coeff b = b 0 a :=
  sum_monomial_eq w

/--
theorem `monomial_sum_one` / 定理 `monomial_sum_one`

English:
theorem monomial_sum_one
  given: {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat)
  proof: map_prod (monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

中文:
定理 monomial_sum_one
  条件: {α : 类型} (s : 有限集 α) (f : α -> σ ->₀ 自然数)
  证明: map_prod (monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, map_prod, monomialOneHom
-/
theorem monomial_sum_one {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) :
    (monomial (∑ i in s, f i) 1 : MvPolynomial σ R) = ∏ i in s, monomial (f i) 1 :=
  map_prod (monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `monomial_sum_index` / 定理 `monomial_sum_index`

English:
theorem monomial_sum_index
  given: {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (a : R)
  proof: by
  rw [← monomial_sum_one]; rw [C_mul']; rw [← (monomial _).map_smul]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 monomial_sum_index
  条件: {α : 类型} (s : 有限集 α) (f : α -> σ ->₀ 自然数) (a : R)
  证明: by
  rw [← monomial_sum_one]; rw [C_mul']; rw [← (monomial _).map_smul]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: C_mul, map_smul, monomial, monomial_sum_one, mul_one, smul_eq_mul
-/
theorem monomial_sum_index {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (a : R) :
    monomial (∑ i in s, f i) a = C a * ∏ i in s, monomial (f i) 1 := by
  rw [← monomial_sum_one]; rw [C_mul']; rw [← (monomial _).map_smul]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `monomial_sum_prod` / 定理 `monomial_sum_prod`

English:
theorem monomial_sum_prod
  given: {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (g : α -> R)
  proof: by
  simp_rw [monomial_sum_index, map_prod, ← Finset.prod_mul_distrib, C_mul_monomial, mul_one]

中文:
定理 monomial_sum_prod
  条件: {α : 类型} (s : 有限集 α) (f : α -> σ ->₀ 自然数) (g : α -> R)
  证明: by
  simp_rw [monomial_sum_index, map_prod, ← Finset.prod_mul_distrib, C_mul_monomial, mul_one]

Depends on / 依赖: C_mul_monomial, Finset, Finset.prod_mul_distrib, map_prod, monomial_sum_index, mul_one, prod_mul_distrib, simp_rw
-/
theorem monomial_sum_prod {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (g : α -> R) :
    monomial (∑ i in s, f i) (∏ i in s, g i) = ∏ i in s, monomial (f i) (g i) := by
  simp_rw [monomial_sum_index, map_prod, ← Finset.prod_mul_distrib, C_mul_monomial, mul_one]

/--
theorem `monomial_finsupp_sum_index` / 定理 `monomial_finsupp_sum_index`

English:
theorem monomial_finsupp_sum_index
  statement: {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> σ ->₀ Nat)
  proof: monomial_sum_index _ _ _

中文:
定理 monomial_finsupp_sum_index
  结论: {α β : 类型} [零 β] (f : α ->₀ β) (g : α -> β -> σ ->₀ 自然数)
  证明: monomial_sum_index _ _ _

Depends on / 依赖: monomial_sum_index
-/
theorem monomial_finsupp_sum_index {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> σ ->₀ Nat)
    (a : R) : monomial (f.sum g) a = C a * f.prod fun a b => monomial (g a b) 1 :=
  monomial_sum_index _ _ _

/--
theorem `monomial_eq_monomial_iff` / 定理 `monomial_eq_monomial_iff`

English:
theorem monomial_eq_monomial_iff
  given: {α : Type*} (a₁ a₂ : α ->₀ Nat) (b₁ b₂ : R)
  proof: single_inj

中文:
定理 monomial_eq_monomial_iff
  条件: {α : 类型} (a₁ a₂ : α ->₀ 自然数) (b₁ b₂ : R)
  证明: single_inj

Depends on / 依赖: single_inj
-/
theorem monomial_eq_monomial_iff {α : Type*} (a₁ a₂ : α ->₀ Nat) (b₁ b₂ : R) :
    monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := single_inj

/--
theorem `monomial_eq` / 定理 `monomial_eq`

English:
theorem monomial_eq
  statement: monomial s a = C a * (s.prod fun n e => X n ^ e : MvPolynomial σ R)
  proof: by
  simp only [X_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]

@[simp]

中文:
定理 monomial_eq
  结论: monomial s a = C a * (s.乘积 fun n e => X n ^ e : 多元多项式 σ R)
  证明: by
  simp only [X_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_single, X_pow_eq_monomial, monomial_finsupp_sum_index, sum_single
-/
theorem monomial_eq : monomial s a = C a * (s.prod fun n e => X n ^ e : MvPolynomial σ R) := by
  simp only [X_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]

@[simp]
/--
lemma `prod_X_pow_eq_monomial` / 引理 `prod_X_pow_eq_monomial`

English:
lemma prod_X_pow_eq_monomial
  statement: ∏ x in s.support, X x ^ s x = monomial s (1 : R)
  proof: by
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod]

中文:
引理 prod_X_pow_eq_monomial
  结论: ∏ x in s.support, X x ^ s x = monomial s (1 : R)
  证明: by
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod]

Depends on / 依赖: Finsupp, Finsupp.prod, map_one, monomial_eq, one_mul
-/
lemma prod_X_pow_eq_monomial : ∏ x in s.support, X x ^ s x = monomial s (1 : R) := by
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod]

/--
theorem `prod_X_pow` / 定理 `prod_X_pow`

English:
theorem prod_X_pow
  given: (x : σ -> Nat) (t : Finset σ)
  proof: by
  rw [monomial_eq]; rw [C_1]; rw [one_mul]; rw [Finsupp.prod]; rw [Finset.prod_subset (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi => by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff]; rw [ne_eq]; rw [not_not] at hi'
    rw [hi']; rw

中文:
定理 prod_X_pow
  条件: (x : σ -> 自然数) (t : 有限集 σ)
  证明: by
  rw [monomial_eq]; rw [C_1]; rw [one_mul]; rw [Finsupp.prod]; rw [Finset.prod_subset (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi => by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff]; rw [ne_eq]; rw [not_not] at hi'
    rw [hi']; rw

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_subset, Finsupp, Finsupp.indicator, Finsupp.mem_support_iff, Finsupp.prod, indicator, mem_support_iff, monomial_eq, ne_eq, not_not, one_mul, pow_zero, prod_congr, prod_subset, support_indicator_subset
-/
theorem prod_X_pow (x : σ -> Nat) (t : Finset σ) :
    ∏ y in t, (X y : MvPolynomial σ R) ^ x y = monomial (indicator t (fun i _ => x i)) (1 : R) := by
  rw [monomial_eq]; rw [C_1]; rw [one_mul]; rw [Finsupp.prod]; rw [Finset.prod_subset (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi => by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff]; rw [ne_eq]; rw [not_not] at hi'
    rw [hi']; rw [pow_zero]

@[elab_as_elim]
/--
theorem `induction_on_monomial` / 定理 `induction_on_monomial`

English:
theorem induction_on_monomial
  statement: {motive : MvPolynomial σ R -> Prop}
  proof: by
  intro s a
  apply @Finsupp.induction σ Nat _ _ s
  · change motive (monomial 0 a)
    exact C a
  · intro n e p _hpn _he ih
    have : forall e : Nat, motive (monomial p a * X n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [pow_succ, (mul

中文:
定理 induction_on_monomial
  结论: {motive : 多元多项式 σ R -> 命题}
  证明: by
  intro s a
  apply @Finsupp.induction σ Nat _ _ s
  · change motive (monomial 0 a)
    exact C a
  · intro n e p _hpn _he ih
    have : forall e : Nat, motive (monomial p a * X n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [pow_succ, (mul

Depends on / 依赖: Finsupp, Finsupp.induction, _hpn, add_comm, e_ih, monomial, monomial_add_single, motive, mul_X, mul_assoc, pow_succ
-/
theorem induction_on_monomial {motive : MvPolynomial σ R -> Prop}
    (C : forall a, motive (C a))
    (mul_X : forall p n, motive p -> motive (p * X n)) : forall s a, motive (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ Nat _ _ s
  · change motive (monomial 0 a)
    exact C a
  · intro n e p _hpn _he ih
    have : forall e : Nat, motive (monomial p a * X n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [pow_succ, (mul_assoc _ _ _).symm, mul_X, e_ih]
    simp [add_comm, monomial_add_single, this]

/-- Analog of `Polynomial.induction_on'`.
To prove something about `MVPolynomials`,
it suffices to show the condition is closed under taking sums,
and it holds for monomials. -/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {P : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
  proof: induction p
    (suffices P (MvPolynomial.monomial 0 0) by rwa [monomial_zero] at this
    show P (MvPolynomial.monomial 0 0) from monomial 0 0)
    fun _ _ _ _ha _hb hPf => add _ _ (monomial _ _) hPf

中文:
定理 induction_on'
  结论: {P : 多元多项式 σ R -> 命题} (p : 多元多项式 σ R)
  证明: induction p
    (suffices P (MvPolynomial.monomial 0 0) by rwa [monomial_zero] at this
    show P (MvPolynomial.monomial 0 0) from monomial 0 0)
    fun _ _ _ _ha _hb hPf => add _ _ (monomial _ _) hPf

Depends on / 依赖: MvPolynomial, MvPolynomial.monomial, monomial, monomial_zero
-/
theorem induction_on' {P : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
    (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial u a))
    (add : forall p q : MvPolynomial σ R, P p -> P q -> P (p + q)) : P p :=
  induction p
    (suffices P (MvPolynomial.monomial 0 0) by rwa [monomial_zero] at this
    show P (MvPolynomial.monomial 0 0) from monomial 0 0)
    fun _ _ _ _ha _hb hPf => add _ _ (monomial _ _) hPf

/--
Similar to `MvPolynomial.induction_on` but only a weak form of `h_add` is required.
In particular, this version only requires us to show
that `motive` is closed under addition of nontrivial monomials not present in the support.
-/
@[elab_as_elim]
/--
theorem `monomial_add_induction_on` / 定理 `monomial_add_induction_on`

English:
theorem monomial_add_induction_on
  statement: {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
  proof: induction p (C_0.rec <| C 0) monomial_add

中文:
定理 monomial_add_induction_on
  结论: {motive : 多元多项式 σ R -> 命题} (p : 多元多项式 σ R)
  证明: induction p (C_0.rec <| C 0) monomial_add

Depends on / 依赖: C_0.rec, monomial_add
-/
theorem monomial_add_induction_on {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
    (C : forall a, motive (C a))
    (monomial_add :
      forall (a : σ ->₀ Nat) (b : R) (f : MvPolynomial σ R),
        a ∉ f.coeff.support -> b != 0 -> motive f -> motive (monomial a b + f)) :
    motive p :=
  induction p (C_0.rec <| C 0) monomial_add

/--
theorem `induction_on''` / 定理 `induction_on''`

English:
theorem induction_on''
  statement: {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
  proof: monomial_add_induction_on p C fun a b f ha hb hf =>
monomial_add a b f ha hb hf induction_on_monomial C mul_X a b

中文:
定理 induction_on''
  结论: {motive : 多元多项式 σ R -> 命题} (p : 多元多项式 σ R)
  证明: monomial_add_induction_on p C fun a b f ha hb hf =>
monomial_add a b f ha hb hf induction_on_monomial C mul_X a b

Depends on / 依赖: induction_on_monomial, monomial_add, monomial_add_induction_on, mul_X
-/
theorem induction_on'' {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
    (C : forall a, motive (C a))
    (monomial_add :
      forall (a : σ ->₀ Nat) (b : R) (f : MvPolynomial σ R),
        a ∉ f.coeff.support -> b != 0 -> motive f -> motive (monomial a b) ->
          motive ((monomial a b) + f))
    (mul_X : forall (p : MvPolynomial σ R) (n : σ), motive p -> motive (p * MvPolynomial.X n)) :
    motive p :=
  monomial_add_induction_on p C fun a b f ha hb hf =>
monomial_add a b f ha hb hf induction_on_monomial C mul_X a b

/--
Analog of `Polynomial.induction_on`.
If a property holds for any constant polynomial
and is preserved under addition and multiplication by variables
then it holds for all multivariate polynomials.
-/
@[recursor 5]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
  proof: induction_on'' p C (fun a b f _ha _hb hf hm => add (monomial a b) f hm hf) mul_X

中文:
定理 induction_on
  结论: {motive : 多元多项式 σ R -> 命题} (p : 多元多项式 σ R)
  证明: induction_on'' p C (fun a b f _ha _hb hf hm => add (monomial a b) f hm hf) mul_X

Depends on / 依赖: induction_on, monomial, mul_X
-/
theorem induction_on {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R)
    (C : forall a, motive (C a))
    (add : forall p q, motive p -> motive q -> motive (p + q))
    (mul_X : forall p n, motive p -> motive (p * X n)) : motive p :=
  induction_on'' p C (fun a b f _ha _hb hf hm => add (monomial a b) f hm hf) mul_X

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  statement: {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A}
  proof: by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intr

中文:
定理 ringHom_ext
  结论: {A : 类型} [半环 A] {f g : 多元多项式 σ R ->+* A}
  证明: by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intr

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.ringHom_ext, ringHom_ext
-/
theorem ringHom_ext {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A}
    (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i) = g (X i)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intro x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `Finsupp.mulHom_ext'` needs to have increased priority
    apply MonoidHom.ext_mnat
    exact hX _

/-- See note [partially-applied ext lemmas].

We set the priority higher than that of `AddMonoidAlgebra.ringHom_ext'`. -/
@[ext high + 1]
/--
theorem `ringHom_ext'` / 定理 `ringHom_ext'`

English:
theorem ringHom_ext'
  statement: {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A}
  proof: ringHom_ext (RingHom.ext_iff.1 hC) hX

中文:
定理 ringHom_ext'
  结论: {A : 类型} [半环 A] {f g : 多元多项式 σ R ->+* A}
  证明: ringHom_ext (RingHom.ext_iff.1 hC) hX

Depends on / 依赖: RingHom, RingHom.ext_iff, ext_iff, ringHom_ext
-/
theorem ringHom_ext' {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A}
    (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g (X i)) : f = g :=
  ringHom_ext (RingHom.ext_iff.1 hC) hX

/--
theorem `hom_eq_hom` / 定理 `hom_eq_hom`

English:
theorem hom_eq_hom
  statement: [Semiring S₂] (f g : MvPolynomial σ R ->+* S₂) (hC : f.comp C = g.comp C)
  proof: RingHom.congr_fun (ringHom_ext' hC hX) p

中文:
定理 hom_eq_hom
  结论: [半环 S₂] (f g : 多元多项式 σ R ->+* S₂) (hC : f.comp C = g.comp C)
  证明: RingHom.congr_fun (ringHom_ext' hC hX) p

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun, ringHom_ext
-/
theorem hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ R ->+* S₂) (hC : f.comp C = g.comp C)
    (hX : forall n : σ, f (X n) = g (X n)) (p : MvPolynomial σ R) : f p = g p :=
  RingHom.congr_fun (ringHom_ext' hC hX) p

/--
theorem `is_id` / 定理 `is_id`

English:
theorem is_id
  statement: (f : MvPolynomial σ R ->+* MvPolynomial σ R) (hC : f.comp C = C)
  proof: hom_eq_hom f (RingHom.id _) hC hX p

中文:
定理 is_id
  结论: (f : 多元多项式 σ R ->+* 多元多项式 σ R) (hC : f.comp C = C)
  证明: hom_eq_hom f (RingHom.id _) hC hX p

Depends on / 依赖: RingHom, RingHom.id, hom_eq_hom
-/
theorem is_id (f : MvPolynomial σ R ->+* MvPolynomial σ R) (hC : f.comp C = C)
    (hX : forall n : σ, f (X n) = X n) (p : MvPolynomial σ R) : f p = p :=
  hom_eq_hom f (RingHom.id _) hC hX p

/-- See note [partially-applied ext lemmas].

We set the priority higher than that of `AddMonoidAlgebra.algHom_ext`. -/
@[ext high + 1]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  statement: {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
  proof: AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

中文:
定理 algHom_ext'
  结论: {A B : 类型} [交换半环 A] [交换半环 B] [代数 R A] [代数 R B]
  证明: AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, AlgHom.toRingHom, MvPolynomial, MvPolynomial.ringHom_ext, coe_ringHom_injective, congr_arg, ringHom_ext, toRingHom
-/
theorem algHom_ext' {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    {f g : MvPolynomial σ A ->ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) =
        g.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (h₂ : forall i, f (X i) = g (X i)) : f = g :=
  AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

/-- See note [partially-applied ext lemmas].

We set the priority higher than that of `MvPolynomial.algHom_ext'`. -/
@[ext high + 2]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R ->ₐ[R] A}
  proof: AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun X : σ => MonoidHom.ext_mnat (hf X)) (by ext)

@[simp]

中文:
定理 algHom_ext
  结论: {A : 类型} [半环 A] [代数 R A] {f g : 多元多项式 σ R ->ₐ[R] A}
  证明: AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun X : σ => MonoidHom.ext_mnat (hf X)) (by ext)

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.algHom_ext, MonoidHom, MonoidHom.ext_mnat, algHom_ext, ext_mnat, mulHom_ext
-/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R ->ₐ[R] A}
    (hf : forall i : σ, f (X i) = g (X i)) : f = g :=
  AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun X : σ => MonoidHom.ext_mnat (hf X)) (by ext)

@[simp]
/--
theorem `algHom_C` / 定理 `algHom_C`

English:
theorem algHom_C
  given: {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R ->ₐ[R] A) (r : R)
  proof: f.commutes r

@[simp]

中文:
定理 algHom_C
  条件: {A : 类型} [半环 A] [代数 R A] (f : 多元多项式 σ R ->ₐ[R] A) (r : R)
  证明: f.commutes r

@[simp]

Depends on / 依赖: commutes, f.commutes
-/
theorem algHom_C {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R ->ₐ[R] A) (r : R) :
    f (C r) = algebraMap R A r :=
  f.commutes r

@[simp]
/--
theorem `adjoin_range_X` / 定理 `adjoin_range_X`

English:
theorem adjoin_range_X
  statement: Algebra.adjoin R (range (X : σ -> MvPolynomial σ R)) = ⊤
  proof: by
  set S := Algebra.adjoin R (range (X : σ -> MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoi

中文:
定理 adjoin_range_X
  结论: 代数.adjoin R (range (X : σ -> 多元多项式 σ R)) = ⊤
  证明: by
  set S := Algebra.adjoin R (range (X : σ -> MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoi

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, MvPolynomial, MvPolynomial.induction_on, S.add_mem, S.algebraMap_mem, S.mul_mem, add_mem, adjoin, algebraMap_mem, induction_on, mem_range_self, mul_X, mul_mem, subset_adjoin, top_unique
-/
theorem adjoin_range_X : Algebra.adjoin R (range (X : σ -> MvPolynomial σ R)) = ⊤ := by
  set S := Algebra.adjoin R (range (X : σ -> MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin <| mem_range_self _)

@[ext]
/--
theorem `linearMap_ext` / 定理 `linearMap_ext`

English:
theorem linearMap_ext
  statement: {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomial σ R ->ₗ[R] M}
  proof: lhom_ext' h

中文:
定理 linearMap_ext
  结论: {M : 类型} [加法交换幺半群 M] [模 R M] {f g : 多元多项式 σ R ->ₗ[R] M}
  证明: lhom_ext' h

Depends on / 依赖: lhom_ext
-/
theorem linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomial σ R ->ₗ[R] M}
    (h : forall s, f ∘ₗ monomial s = g ∘ₗ monomial s) : f = g :=
  lhom_ext' h

section Support

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (p : MvPolynomial σ R)
  body: p.coeff.support

中文:
定义 support
  签名: (p : 多元多项式 σ R)
  定义体: p.coeff.support

Depends on / 依赖: p.coeff.support, support
-/
def support (p : MvPolynomial σ R) : Finset (σ ->₀ Nat) :=
  p.coeff.support

/--
theorem `finsupp_support_eq_support` / 定理 `finsupp_support_eq_support`

English:
theorem finsupp_support_eq_support
  given: (p : MvPolynomial σ R)
  statement: p.coeff.support = p.support
  proof: rfl

中文:
定理 finsupp_support_eq_support
  条件: (p : 多元多项式 σ R)
  结论: p.coeff.support = p.support
  证明: rfl
-/
theorem finsupp_support_eq_support (p : MvPolynomial σ R) : p.coeff.support = p.support :=
  rfl

/--
theorem `support_monomial` / 定理 `support_monomial`

English:
theorem support_monomial
  given: [h : Decidable (a = 0)]
  proof: by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl

中文:
定理 support_monomial
  条件: [h : 可判定 (a = 0)]
  证明: by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl

Depends on / 依赖: Classical, Classical.decEq, Subsingleton, Subsingleton.elim
-/
theorem support_monomial [h : Decidable (a = 0)] :
    (monomial s a).support = if a = 0 then ∅ else {s} := by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl

/--
lemma `support_C` / 引理 `support_C`

English:
lemma support_C
  given: (c : R) [h : Decidable (c = 0)]
  proof: support_monomial

中文:
引理 support_C
  条件: (c : R) [h : 可判定 (c = 0)]
  证明: support_monomial

Depends on / 依赖: support
-/
lemma support_C (c : R) [h : Decidable (c = 0)] :
    (C (σ := σ) c).support = if c = 0 then ∅ else {0} :=
  support_monomial

/--
theorem `support_monomial_subset` / 定理 `support_monomial_subset`

English:
theorem support_monomial_subset
  statement: (monomial s a).support subseteq {s}
  proof: support_single_subset

中文:
定理 support_monomial_subset
  结论: (monomial s a).support subseteq {s}
  证明: support_single_subset

Depends on / 依赖: support_single_subset
-/
theorem support_monomial_subset : (monomial s a).support subseteq {s} :=
  support_single_subset

/--
theorem `support_add` / 定理 `support_add`

English:
theorem support_add
  given: [DecidableEq σ]
  statement: (p + q).support subseteq p.support union q.support
  proof: Finsupp.support_add

中文:
定理 support_add
  条件: [DecidableEq σ]
  结论: (p + q).support subseteq p.support union q.support
  证明: Finsupp.support_add

Depends on / 依赖: Finsupp, Finsupp.support_add, support_add
-/
theorem support_add [DecidableEq σ] : (p + q).support subseteq p.support union q.support :=
  Finsupp.support_add

/--
theorem `support_X` / 定理 `support_X`

English:
theorem support_X
  given: [Nontrivial R]
  statement: (X n : MvPolynomial σ R).support = {Finsupp.single n 1}
  proof: by
  classical rw [X, support_monomial, if_neg]; exact one_ne_zero

中文:
定理 support_X
  条件: [非平凡 R]
  结论: (X n : 多元多项式 σ R).support = {有限支撑.single n 1}
  证明: by
  classical rw [X, support_monomial, if_neg]; exact one_ne_zero

Depends on / 依赖: classical, if_neg, one_ne_zero, support_monomial
-/
theorem support_X [Nontrivial R] : (X n : MvPolynomial σ R).support = {Finsupp.single n 1} := by
  classical rw [X, support_monomial, if_neg]; exact one_ne_zero

/--
theorem `support_X_pow` / 定理 `support_X_pow`

English:
theorem support_X_pow
  given: [Nontrivial R] (s : σ) (n : Nat)
  proof: by
  classical
    rw [X_pow_eq_monomial]; rw [support_monomial]; rw [if_neg (one_ne_zero' R)]

@[simp]

中文:
定理 support_X_pow
  条件: [非平凡 R] (s : σ) (n : 自然数)
  证明: by
  classical
    rw [X_pow_eq_monomial]; rw [support_monomial]; rw [if_neg (one_ne_zero' R)]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, classical, if_neg, one_ne_zero, support_monomial
-/
theorem support_X_pow [Nontrivial R] (s : σ) (n : Nat) :
    (X s ^ n : MvPolynomial σ R).support = {Finsupp.single s n} := by
  classical
    rw [X_pow_eq_monomial]; rw [support_monomial]; rw [if_neg (one_ne_zero' R)]

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: (0 : MvPolynomial σ R).support = ∅
  proof: rfl

@[simp]

中文:
定理 support_zero
  结论: (0 : 多元多项式 σ R).support = ∅
  证明: rfl

@[simp]
-/
theorem support_zero : (0 : MvPolynomial σ R).support = ∅ :=
  rfl

@[simp]
/--
lemma `support_one` / 引理 `support_one`

English:
lemma support_one
  given: [Nontrivial R]
  statement: (1 : MvPolynomial σ R).support = {0}
  proof: by
  classical
  simp [show support (1 : MvPolynomial σ R) = if (1 : R) = 0 then ∅ else {0} from rfl]

中文:
引理 support_one
  条件: [非平凡 R]
  结论: (1 : 多元多项式 σ R).support = {0}
  证明: by
  classical
  simp [show support (1 : MvPolynomial σ R) = if (1 : R) = 0 then ∅ else {0} from rfl]

Depends on / 依赖: MvPolynomial, classical, support
-/
lemma support_one [Nontrivial R] : (1 : MvPolynomial σ R).support = {0} := by
  classical
  simp [show support (1 : MvPolynomial σ R) = if (1 : R) = 0 then ∅ else {0} from rfl]

/--
theorem `support_smul` / 定理 `support_smul`

English:
theorem support_smul
  given: {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial σ R}
  proof: Finsupp.support_smul

中文:
定理 support_smul
  条件: {S₁ : 类型} [SMulZero类 S₁ R] {a : S₁} {f : 多元多项式 σ R}
  证明: Finsupp.support_smul

Depends on / 依赖: Finsupp, Finsupp.support_smul, support_smul
-/
theorem support_smul {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial σ R} :
    (a • f).support subseteq f.support :=
  Finsupp.support_smul

/--
theorem `support_sum` / 定理 `support_sum`

English:
theorem support_sum
  given: {α : Type*} [DecidableEq σ] {s : Finset α} {f : α -> MvPolynomial σ R}
  proof: by
  simpa [support, coeff, MvPolynomial] using Finsupp.support_finsetSum

中文:
定理 support_sum
  条件: {α : 类型} [DecidableEq σ] {s : 有限集 α} {f : α -> 多元多项式 σ R}
  证明: by
  simpa [support, coeff, MvPolynomial] using Finsupp.support_finsetSum

Depends on / 依赖: Finsupp, Finsupp.support_finsetSum, MvPolynomial, support, support_finsetSum
-/
theorem support_sum {α : Type*} [DecidableEq σ] {s : Finset α} {f : α -> MvPolynomial σ R} :
    (∑ x in s, f x).support subseteq s.biUnion fun x => (f x).support := by
  simpa [support, coeff, MvPolynomial] using Finsupp.support_finsetSum

end Support

section Coeff

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (m : σ ->₀ Nat) (p : MvPolynomial σ R)
  body: @DFunLike.coe ((σ ->₀ Nat) ->₀ R) _ _ _ (AddMonoidAlgebra.coeff p) m

中文:
定义 coeff
  签名: (m : σ ->₀ 自然数) (p : 多元多项式 σ R)
  定义体: @DFunLike.coe ((σ ->₀ Nat) ->₀ R) _ _ _ (AddMonoidAlgebra.coeff p) m

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff, DFunLike, DFunLike.coe
-/
def coeff (m : σ ->₀ Nat) (p : MvPolynomial σ R) : R :=
  @DFunLike.coe ((σ ->₀ Nat) ->₀ R) _ _ _ (AddMonoidAlgebra.coeff p) m

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: {p : MvPolynomial σ R} {m : σ ->₀ Nat}
  statement: m in p.support ↔ p.coeff m != 0
  proof: by
  simp [support, coeff]

中文:
定理 mem_support_iff
  条件: {p : 多元多项式 σ R} {m : σ ->₀ 自然数}
  结论: m in p.support ↔ p.coeff m != 0
  证明: by
  simp [support, coeff]

Depends on / 依赖: support
-/
theorem mem_support_iff {p : MvPolynomial σ R} {m : σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0 := by
  simp [support, coeff]

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  given: {p : MvPolynomial σ R} {m : σ ->₀ Nat}
  statement: m ∉ p.support ↔ p.coeff m = 0
  proof: by
  simp

中文:
定理 notMem_support_iff
  条件: {p : 多元多项式 σ R} {m : σ ->₀ 自然数}
  结论: m ∉ p.support ↔ p.coeff m = 0
  证明: by
  simp
-/
theorem notMem_support_iff {p : MvPolynomial σ R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0 := by
  simp

/--
theorem `sum_def` / 定理 `sum_def`

English:
theorem sum_def
  given: {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ ->₀ Nat) -> R -> A}
  proof: by
  simp [support, Finsupp.sum, coeff]

中文:
定理 sum_def
  条件: {A} [加法交换幺半群 A] {p : 多元多项式 σ R} {b : (σ ->₀ 自然数) -> R -> A}
  证明: by
  simp [support, Finsupp.sum, coeff]

Depends on / 依赖: Finsupp, Finsupp.sum, support
-/
theorem sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ ->₀ Nat) -> R -> A} :
    (AddMonoidAlgebra.coeff p).sum b = ∑ m in p.support, b m (p.coeff m) := by
  simp [support, Finsupp.sum, coeff]

/--
theorem `support_mul` / 定理 `support_mul`

English:
theorem support_mul
  given: [DecidableEq σ] (p q : MvPolynomial σ R)
  proof: AddMonoidAlgebra.support_coeff_mul_subset p q

中文:
定理 support_mul
  条件: [DecidableEq σ] (p q : 多元多项式 σ R)
  证明: AddMonoidAlgebra.support_coeff_mul_subset p q

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.support_coeff_mul_subset, support_coeff_mul_subset
-/
theorem support_mul [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p * q).support subseteq p.support + q.support :=
  AddMonoidAlgebra.support_coeff_mul_subset p q

/--
lemma `disjoint_support_monomial` / 引理 `disjoint_support_monomial`

English:
lemma disjoint_support_monomial
  statement: {a : σ ->₀ Nat} {p : MvPolynomial σ R} {s : R}
  proof: by
  classical
  simpa [support_monomial, hs] using notMem_support_iff.mp ha

@[ext]

中文:
引理 disjoint_support_monomial
  结论: {a : σ ->₀ 自然数} {p : 多元多项式 σ R} {s : R}
  证明: by
  classical
  simpa [support_monomial, hs] using notMem_support_iff.mp ha

@[ext]

Depends on / 依赖: classical, notMem_support_iff, notMem_support_iff.mp, support_monomial
-/
lemma disjoint_support_monomial {a : σ ->₀ Nat} {p : MvPolynomial σ R} {s : R}
    (ha : a ∉ p.support) (hs : s != 0) : Disjoint (monomial a s).support p.support := by
  classical
  simpa [support_monomial, hs] using notMem_support_iff.mp ha

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (p q : MvPolynomial σ R)
  statement: (forall m, coeff m p = coeff m q) -> p = q
  proof: fun h => AddMonoidAlgebra.ext by ext; exact h _

中文:
定理 ext
  条件: (p q : 多元多项式 σ R)
  结论: (对任意 m, coeff m p = coeff m q) -> p = q
  证明: fun h => AddMonoidAlgebra.ext by ext; exact h _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.ext
-/
theorem ext (p q : MvPolynomial σ R) : (forall m, coeff m p = coeff m q) -> p = q :=
fun h => AddMonoidAlgebra.ext by ext; exact h _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_add` / 定理 `coeff_add`

English:
theorem coeff_add
  given: (m : σ ->₀ Nat) (p q : MvPolynomial σ R)
  proof: by simp [coeff, MvPolynomial]

@[simp]

中文:
定理 coeff_add
  条件: (m : σ ->₀ 自然数) (p q : 多元多项式 σ R)
  证明: by simp [coeff, MvPolynomial]

@[simp]

Depends on / 依赖: MvPolynomial
-/
theorem coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ R) :
    coeff m (p + q) = coeff m p + coeff m q := by simp [coeff, MvPolynomial]

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ ->₀ Nat) (C : S₁) (p : MvPolynomial σ R)
  proof: AddMonoidAlgebra.coeff_smul_apply ..

@[simp]

中文:
定理 coeff_smul
  条件: {S₁ : 类型} [SMulZero类 S₁ R] (m : σ ->₀ 自然数) (C : S₁) (p : 多元多项式 σ R)
  证明: AddMonoidAlgebra.coeff_smul_apply ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_smul_apply, coeff_smul_apply
-/
theorem coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ ->₀ Nat) (C : S₁) (p : MvPolynomial σ R) :
    coeff m (C • p) = C • coeff m p :=
  AddMonoidAlgebra.coeff_smul_apply ..

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  given: (m : σ ->₀ Nat)
  statement: coeff m (0 : MvPolynomial σ R) = 0
  proof: rfl

@[simp]

中文:
定理 coeff_zero
  条件: (m : σ ->₀ 自然数)
  结论: coeff m (0 : 多元多项式 σ R) = 0
  证明: rfl

@[simp]
-/
theorem coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPolynomial σ R) = 0 :=
  rfl

@[simp]
/--
theorem `coeff_zero_X` / 定理 `coeff_zero_X`

English:
theorem coeff_zero_X
  given: (i : σ)
  statement: coeff 0 (X i : MvPolynomial σ R) = 0
  proof: single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

中文:
定理 coeff_zero_X
  条件: (i : σ)
  结论: coeff 0 (X i : 多元多项式 σ R) = 0
  证明: single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

Depends on / 依赖: Finsupp, Finsupp.single_eq_zero, single_eq_of_ne, single_eq_zero
-/
theorem coeff_zero_X (i : σ) : coeff 0 (X i : MvPolynomial σ R) = 0 :=
  single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

-- TODO: Remove once its use in the Witt vector API has been removed.
@[simp]
/--
lemma `coeff_addMonoidAlgebraMap` / 引理 `coeff_addMonoidAlgebraMap`

English:
lemma coeff_addMonoidAlgebraMap
  given: (g : S₁ ->+ R) (φ : MvPolynomial σ S₁) (m)
  proof: rfl

@[deprecated (since := "2026-03-27")] alias coeff_mapRange := coeff_addMonoidAlgebraMap

中文:
引理 coeff_addMonoidAlgebraMap
  条件: (g : S₁ ->+ R) (φ : 多元多项式 σ S₁) (m)
  证明: rfl

@[deprecated (since := "2026-03-27")] alias coeff_mapRange := coeff_addMonoidAlgebraMap
-/
lemma coeff_addMonoidAlgebraMap (g : S₁ ->+ R) (φ : MvPolynomial σ S₁) (m) :
    coeff m (φ.map g) = g (coeff m φ) := rfl

@[deprecated (since := "2026-03-27")] alias coeff_mapRange := coeff_addMonoidAlgebraMap

/-- `MvPolynomial.coeff m` but promoted to an `AddMonoidHom`. -/
@[simps]
/--
Definition of `coeffAddMonoidHom` / `coeffAddMonoidHom` 的定义

English:
definition coeffAddMonoidHom
  signature: (m : σ ->₀ Nat)
  body: coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m

中文:
定义 coeffAddMonoidHom
  签名: (m : σ ->₀ 自然数)
  定义体: coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m
-/
def coeffAddMonoidHom (m : σ ->₀ Nat) : MvPolynomial σ R ->+ R where
  toFun := coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m

variable (R) in
/-- `MvPolynomial.coeff m` but promoted to a `LinearMap`. -/
@[simps]
/--
Definition of `lcoeff` / `lcoeff` 的定义

English:
definition lcoeff
  signature: (m : σ ->₀ Nat)
  body: coeff m
  map_add' := coeff_add m
  map_smul' := coeff_smul m

中文:
定义 lcoeff
  签名: (m : σ ->₀ 自然数)
  定义体: coeff m
  map_add' := coeff_add m
  map_smul' := coeff_smul m
-/
def lcoeff (m : σ ->₀ Nat) : MvPolynomial σ R ->ₗ[R] R where
  toFun := coeff m
  map_add' := coeff_add m
  map_smul' := coeff_smul m

/--
theorem `coeff_sum` / 定理 `coeff_sum`

English:
theorem coeff_sum
  given: {X : Type*} (s : Finset X) (f : X -> MvPolynomial σ R) (m : σ ->₀ Nat)
  proof: map_sum (@coeffAddMonoidHom R σ _ _) _ s

中文:
定理 coeff_sum
  条件: {X : 类型} (s : 有限集 X) (f : X -> 多元多项式 σ R) (m : σ ->₀ 自然数)
  证明: map_sum (@coeffAddMonoidHom R σ _ _) _ s

Depends on / 依赖: coeffAddMonoidHom, map_sum
-/
theorem coeff_sum {X : Type*} (s : Finset X) (f : X -> MvPolynomial σ R) (m : σ ->₀ Nat) :
    coeff m (∑ x in s, f x) = ∑ x in s, coeff m (f x) :=
  map_sum (@coeffAddMonoidHom R σ _ _) _ s

/--
theorem `monic_monomial_eq` / 定理 `monic_monomial_eq`

English:
theorem monic_monomial_eq
  given: (m)
  proof: by simp [monomial_eq]

@[simp]

中文:
定理 monic_monomial_eq
  条件: (m)
  证明: by simp [monomial_eq]

@[simp]

Depends on / 依赖: monomial_eq
-/
theorem monic_monomial_eq (m) :
    monomial m (1 : R) = (m.prod fun n e => X n ^ e : MvPolynomial σ R) := by simp [monomial_eq]

@[simp]
/--
theorem `coeff_monomial` / 定理 `coeff_monomial`

English:
theorem coeff_monomial
  given: [DecidableEq σ] (m n) (a)
  proof: Finsupp.single_apply

中文:
定理 coeff_monomial
  条件: [DecidableEq σ] (m n) (a)
  证明: Finsupp.single_apply

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem coeff_monomial [DecidableEq σ] (m n) (a) :
    coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0 :=
  Finsupp.single_apply

/--
theorem `eq_monomial_of_support_subset_singleton` / 定理 `eq_monomial_of_support_subset_singleton`

English:
theorem eq_monomial_of_support_subset_singleton
  statement: {φ : MvPolynomial σ R} {d₀ : σ ->₀ Nat}
  proof: by
  classical
  ext d
  rcases eq_or_ne d d₀ with rfl | hd
  · rw [coeff_monomial, if_pos rfl]
  · rw [notMem_support_iff.mp fun hmem => hd (h d hmem), coeff_monomial, if_neg fun e => hd e.symm]

@[simp]

中文:
定理 eq_monomial_of_support_subset_singleton
  结论: {φ : 多元多项式 σ R} {d₀ : σ ->₀ 自然数}
  证明: by
  classical
  ext d
  rcases eq_or_ne d d₀ with rfl | hd
  · rw [coeff_monomial, if_pos rfl]
  · rw [notMem_support_iff.mp fun hmem => hd (h d hmem), coeff_monomial, if_neg fun e => hd e.symm]

@[simp]

Depends on / 依赖: classical, coeff_monomial, e.symm, eq_or_ne, if_neg, if_pos, notMem_support_iff, notMem_support_iff.mp
-/
theorem eq_monomial_of_support_subset_singleton {φ : MvPolynomial σ R} {d₀ : σ ->₀ Nat}
    (h : forall d in φ.support, d = d₀) : φ = monomial d₀ (coeff d₀ φ) := by
  classical
  ext d
  rcases eq_or_ne d d₀ with rfl | hd
  · rw [coeff_monomial, if_pos rfl]
  · rw [notMem_support_iff.mp fun hmem => hd (h d hmem), coeff_monomial, if_neg fun e => hd e.symm]

@[simp]
/--
theorem `coeff_C` / 定理 `coeff_C`

English:
theorem coeff_C
  given: [DecidableEq σ] (m) (a)
  proof: Finsupp.single_apply

中文:
定理 coeff_C
  条件: [DecidableEq σ] (m) (a)
  证明: Finsupp.single_apply

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem coeff_C [DecidableEq σ] (m) (a) :
    coeff m (C a : MvPolynomial σ R) = if 0 = m then a else 0 :=
  Finsupp.single_apply

/--
theorem `coeff_C_of_ne_zero` / 定理 `coeff_C_of_ne_zero`

English:
theorem coeff_C_of_ne_zero
  given: {m : σ ->₀ Nat} (h : m != 0) (a : R)
  statement: coeff m (C a) = 0
  proof: by
  classical rw [coeff_C, if_neg h.symm]

中文:
定理 coeff_C_of_ne_zero
  条件: {m : σ ->₀ 自然数} (h : m != 0) (a : R)
  结论: coeff m (C a) = 0
  证明: by
  classical rw [coeff_C, if_neg h.symm]

Depends on / 依赖: classical, coeff_C, h.symm, if_neg
-/
theorem coeff_C_of_ne_zero {m : σ ->₀ Nat} (h : m != 0) (a : R) : coeff m (C a) = 0 := by
  classical rw [coeff_C, if_neg h.symm]

-- The intended use case of this theorem is for `n = 1` (often useful for `pderiv`).
@[simp]
/--
theorem `coeff_add_single_C` / 定理 `coeff_add_single_C`

English:
theorem coeff_add_single_C
  given: {n : Nat} [NeZero n] {m : σ ->₀ Nat} (a : R) (i : σ)
  proof: coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

中文:
定理 coeff_add_single_C
  条件: {n : 自然数} [NeZero n] {m : σ ->₀ 自然数} (a : R) (i : σ)
  证明: coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

Depends on / 依赖: NeZero, NeZero.ne, coeff_C_of_ne_zero
-/
theorem coeff_add_single_C {n : Nat} [NeZero n] {m : σ ->₀ Nat} (a : R) (i : σ) :
    coeff (m + Finsupp.single i n) (C a) = 0 :=
  coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

/--
lemma `eq_C_of_isEmpty` / 引理 `eq_C_of_isEmpty`

English:
lemma eq_C_of_isEmpty
  given: [IsEmpty σ] (p : MvPolynomial σ R)
  proof: by
  obtain ⟨x, rfl⟩ := C_surjective σ p
  simp

中文:
引理 eq_C_of_isEmpty
  条件: [是空 σ] (p : 多元多项式 σ R)
  证明: by
  obtain ⟨x, rfl⟩ := C_surjective σ p
  simp

Depends on / 依赖: C_surjective
-/
lemma eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynomial σ R) :
    p = C (p.coeff 0) := by
  obtain ⟨x, rfl⟩ := C_surjective σ p
  simp

/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: [DecidableEq σ] (m)
  statement: coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0
  proof: coeff_C m 1

@[simp]

中文:
定理 coeff_one
  条件: [DecidableEq σ] (m)
  结论: coeff m (1 : 多元多项式 σ R) = if 0 = m then 1 else 0
  证明: coeff_C m 1

@[simp]

Depends on / 依赖: coeff_C
-/
theorem coeff_one [DecidableEq σ] (m) : coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0 :=
  coeff_C m 1

@[simp]
/--
theorem `coeff_zero_C` / 定理 `coeff_zero_C`

English:
theorem coeff_zero_C
  given: (a)
  statement: coeff 0 (C a : MvPolynomial σ R) = a
  proof: single_eq_same

@[simp]

中文:
定理 coeff_zero_C
  条件: (a)
  结论: coeff 0 (C a : 多元多项式 σ R) = a
  证明: single_eq_same

@[simp]

Depends on / 依赖: single_eq_same
-/
theorem coeff_zero_C (a) : coeff 0 (C a : MvPolynomial σ R) = a :=
  single_eq_same

@[simp]
/--
theorem `coeff_zero_one` / 定理 `coeff_zero_one`

English:
theorem coeff_zero_one
  statement: coeff 0 (1 : MvPolynomial σ R) = 1
  proof: coeff_zero_C 1

中文:
定理 coeff_zero_one
  结论: coeff 0 (1 : 多元多项式 σ R) = 1
  证明: coeff_zero_C 1

Depends on / 依赖: coeff_zero_C
-/
theorem coeff_zero_one : coeff 0 (1 : MvPolynomial σ R) = 1 :=
  coeff_zero_C 1

/--
theorem `coeff_X_pow` / 定理 `coeff_X_pow`

English:
theorem coeff_X_pow
  given: [DecidableEq σ] (i : σ) (m) (k : Nat)
  proof: by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _

中文:
定理 coeff_X_pow
  条件: [DecidableEq σ] (i : σ) (m) (k : 自然数)
  证明: by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _

Depends on / 依赖: Finsupp, Finsupp.prod_single_index, Finsupp.single, coeff_monomial, monomial_eq, one_mul, pow_zero, prod_single_index, single
-/
theorem coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : Nat) :
    coeff m (X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 else 0 := by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _

/--
theorem `coeff_X` / 定理 `coeff_X`

English:
theorem coeff_X
  given: [DecidableEq σ] (i : σ) (m)
  proof: by
  rw [← coeff_X_pow]; rw [pow_one]

@[deprecated (since := "2026-05-25")]
alias coeff_X' := coeff_X

@[simp]

中文:
定理 coeff_X
  条件: [DecidableEq σ] (i : σ) (m)
  证明: by
  rw [← coeff_X_pow]; rw [pow_one]

@[deprecated (since := "2026-05-25")]
alias coeff_X' := coeff_X

@[simp]

Depends on / 依赖: IsDirectedOrder, coeff_X_pow, pow_one
-/
theorem coeff_X [DecidableEq σ] (i : σ) (m) :
    coeff m (X i : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0 := by
  rw [← coeff_X_pow]; rw [pow_one]

@[deprecated (since := "2026-05-25")]
alias coeff_X' := coeff_X

@[simp]
/--
theorem `coeff_X_same` / 定理 `coeff_X_same`

English:
theorem coeff_X_same
  given: (i : σ)
  proof: by
  classical rw [coeff_X, if_pos rfl]

中文:
定理 coeff_X_same
  条件: (i : σ)
  证明: by
  classical rw [coeff_X, if_pos rfl]

Depends on / 依赖: classical, coeff_X, if_pos
-/
theorem coeff_X_same (i : σ) :
    coeff (Finsupp.single i 1) (X i : MvPolynomial σ R) = 1 := by
  classical rw [coeff_X, if_pos rfl]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_C_mul` / 定理 `coeff_C_mul`

English:
theorem coeff_C_mul
  given: (m) (a : R) (p : MvPolynomial σ R)
  statement: coeff m (C a * p) = a * coeff m p
  proof: by
  classical
  rw [mul_def]; rw [sum_C]
  · simp +contextual [sum_def, coeff_sum]
  simp

中文:
定理 coeff_C_mul
  条件: (m) (a : R) (p : 多元多项式 σ R)
  结论: coeff m (C a * p) = a * coeff m p
  证明: by
  classical
  rw [mul_def]; rw [sum_C]
  · simp +contextual [sum_def, coeff_sum]
  simp

Depends on / 依赖: classical, coeff_sum, contextual, mul_def, sum_C, sum_def
-/
theorem coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : coeff m (C a * p) = a * coeff m p := by
  classical
  rw [mul_def]; rw [sum_C]
  · simp +contextual [sum_def, coeff_sum]
  simp

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  given: [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ ->₀ Nat)
  proof: AddMonoidAlgebra.coeff_mul_antidiag p q _ _ Finset.mem_antidiagonal

@[simp]

中文:
定理 coeff_mul
  条件: [DecidableEq σ] (p q : 多元多项式 σ R) (n : σ ->₀ 自然数)
  证明: AddMonoidAlgebra.coeff_mul_antidiag p q _ _ Finset.mem_antidiagonal

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_mul_antidiag, Finset, Finset.mem_antidiagonal, IsCodirectedOrder, coeff_mul_antidiag, mem_antidiagonal
-/
theorem coeff_mul [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ ->₀ Nat) :
    coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p * coeff x.2 q :=
  AddMonoidAlgebra.coeff_mul_antidiag p q _ _ Finset.mem_antidiagonal

@[simp]
/--
theorem `coeff_mul_monomial` / 定理 `coeff_mul_monomial`

English:
theorem coeff_mul_monomial
  given: (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R)
  proof: coeff_mul_single_add ..

@[simp]

中文:
定理 coeff_mul_monomial
  条件: (m) (s : σ ->₀ 自然数) (r : R) (p : 多元多项式 σ R)
  证明: coeff_mul_single_add ..

@[simp]

Depends on / 依赖: coeff_mul_single_add
-/
theorem coeff_mul_monomial (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) :
    coeff (m + s) (p * monomial s r) = coeff m p * r := coeff_mul_single_add ..

@[simp]
/--
theorem `coeff_monomial_mul` / 定理 `coeff_monomial_mul`

English:
theorem coeff_monomial_mul
  given: (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R)
  proof: coeff_single_mul_add ..

@[simp]

中文:
定理 coeff_monomial_mul
  条件: (m) (s : σ ->₀ 自然数) (r : R) (p : 多元多项式 σ R)
  证明: coeff_single_mul_add ..

@[simp]

Depends on / 依赖: coeff_single_mul_add
-/
theorem coeff_monomial_mul (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) :
    coeff (s + m) (monomial s r * p) = r * coeff m p := coeff_single_mul_add ..

@[simp]
/--
theorem `coeff_mul_X` / 定理 `coeff_mul_X`

English:
theorem coeff_mul_X
  given: (m) (s : σ) (p : MvPolynomial σ R)
  proof: (coeff_mul_monomial _ _ _ _).trans (mul_one _)

@[simp]

中文:
定理 coeff_mul_X
  条件: (m) (s : σ) (p : 多元多项式 σ R)
  证明: (coeff_mul_monomial _ _ _ _).trans (mul_one _)

@[simp]

Depends on / 依赖: coeff_mul_monomial, mul_one
-/
theorem coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (m + Finsupp.single s 1) (p * X s) = coeff m p :=
  (coeff_mul_monomial _ _ _ _).trans (mul_one _)

@[simp]
/--
theorem `coeff_X_mul` / 定理 `coeff_X_mul`

English:
theorem coeff_X_mul
  given: (m) (s : σ) (p : MvPolynomial σ R)
  proof: (coeff_monomial_mul _ _ _ _).trans (one_mul _)

中文:
定理 coeff_X_mul
  条件: (m) (s : σ) (p : 多元多项式 σ R)
  证明: (coeff_monomial_mul _ _ _ _).trans (one_mul _)

Depends on / 依赖: coeff_monomial_mul, one_mul
-/
theorem coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p :=
  (coeff_monomial_mul _ _ _ _).trans (one_mul _)

/--
lemma `coeff_single_X_pow` / 引理 `coeff_single_X_pow`

English:
lemma coeff_single_X_pow
  given: [DecidableEq σ] (s s' : σ) (n n' : Nat)
  proof: by
  simp only [coeff_X_pow, single_eq_single_iff]

@[simp]

中文:
引理 coeff_single_X_pow
  条件: [DecidableEq σ] (s s' : σ) (n n' : 自然数)
  证明: by
  simp only [coeff_X_pow, single_eq_single_iff]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
lemma coeff_single_X_pow [DecidableEq σ] (s s' : σ) (n n' : Nat) :
    (X (R := R) s ^ n).coeff (Finsupp.single s' n')
    = if s = s' ∧ n = n' ∨ n = 0 ∧ n' = 0 then 1 else 0 := by
  simp only [coeff_X_pow, single_eq_single_iff]

@[simp]
/--
lemma `coeff_single_X` / 引理 `coeff_single_X`

English:
lemma coeff_single_X
  given: [DecidableEq σ] (s s' : σ) (n : Nat)
  proof: by
  simpa [eq_comm, and_comm] using coeff_single_X_pow s s' 1 n

中文:
引理 coeff_single_X
  条件: [DecidableEq σ] (s s' : σ) (n : 自然数)
  证明: by
  simpa [eq_comm, and_comm] using coeff_single_X_pow s s' 1 n

Depends on / 依赖: Finsupp, Finsupp.single, and_comm, coeff_single_X_pow, eq_comm, single
-/
lemma coeff_single_X [DecidableEq σ] (s s' : σ) (n : Nat) :
    (X s).coeff (R := R) (Finsupp.single s' n) = if n = 1 ∧ s = s' then 1 else 0 := by
  simpa [eq_comm, and_comm] using coeff_single_X_pow s s' 1 n

/--
theorem `coeff_prod_X_pow` / 定理 `coeff_prod_X_pow`

English:
theorem coeff_prod_X_pow
  given: [DecidableEq σ] (d : σ ->₀ Nat) (x : σ -> Nat) (s : Finset σ)
  proof: by
  simp_rw [prod_X_pow x s, coeff_monomial, eq_comm]

@[simp]

中文:
定理 coeff_prod_X_pow
  条件: [DecidableEq σ] (d : σ ->₀ 自然数) (x : σ -> 自然数) (s : 有限集 σ)
  证明: by
  simp_rw [prod_X_pow x s, coeff_monomial, eq_comm]

@[simp]

Depends on / 依赖: coeff_monomial, eq_comm, prod_X_pow, simp_rw
-/
theorem coeff_prod_X_pow [DecidableEq σ] (d : σ ->₀ Nat) (x : σ -> Nat) (s : Finset σ) :
    coeff d (∏ y in s, (X y : MvPolynomial σ R) ^ x y) =
      if d = Finsupp.indicator s (fun i _ => x i) then 1 else 0 := by
  simp_rw [prod_X_pow x s, coeff_monomial, eq_comm]

@[simp]
/--
theorem `support_mul_X` / 定理 `support_mul_X`

English:
theorem support_mul_X
  given: (s : σ) (p : MvPolynomial σ R)
  proof: AddMonoidAlgebra.support_coeff_mul_single p _ (by simp) _

@[simp]

中文:
定理 support_mul_X
  条件: (s : σ) (p : 多元多项式 σ R)
  证明: AddMonoidAlgebra.support_coeff_mul_single p _ (by simp) _

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.support_coeff_mul_single, support_coeff_mul_single
-/
theorem support_mul_X (s : σ) (p : MvPolynomial σ R) :
    (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_coeff_mul_single p _ (by simp) _

@[simp]
/--
theorem `support_X_mul` / 定理 `support_X_mul`

English:
theorem support_X_mul
  given: (s : σ) (p : MvPolynomial σ R)
  proof: AddMonoidAlgebra.support_coeff_single_mul p _ (by simp) _

@[simp]

中文:
定理 support_X_mul
  条件: (s : σ) (p : 多元多项式 σ R)
  证明: AddMonoidAlgebra.support_coeff_single_mul p _ (by simp) _

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.support_coeff_single_mul, support_coeff_single_mul
-/
theorem support_X_mul (s : σ) (p : MvPolynomial σ R) :
    (X s * p).support = p.support.map (addLeftEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_coeff_single_mul p _ (by simp) _

@[simp]
/--
theorem `support_smul_eq` / 定理 `support_smul_eq`

English:
theorem support_smul_eq
  statement: {S : Type*} [Semiring S] [IsDomain S] [Module S R]
  proof: Finsupp.support_smul_eq h

中文:
定理 support_smul_eq
  结论: {S : 类型} [半环 S] [是整环 S] [模 S R]
  证明: Finsupp.support_smul_eq h

Depends on / 依赖: Finsupp, Finsupp.support_smul_eq, support_smul_eq
-/
theorem support_smul_eq {S : Type*} [Semiring S] [IsDomain S] [Module S R]
    [Module.IsTorsionFree S R] {a : S} (h : a != 0) (p : MvPolynomial σ R) :
    (a • p).support = p.support :=
  Finsupp.support_smul_eq h

/--
theorem `support_sdiff_support_subset_support_add` / 定理 `support_sdiff_support_subset_support_add`

English:
theorem support_sdiff_support_subset_support_add
  given: [DecidableEq σ] (p q : MvPolynomial σ R)
  proof: by
  intro m hm
  simp only [Classical.not_not, mem_support_iff, Finset.mem_sdiff, Ne] at hm
  simp [hm.2, hm.1]

中文:
定理 support_sdiff_support_subset_support_add
  条件: [DecidableEq σ] (p q : 多元多项式 σ R)
  证明: by
  intro m hm
  simp only [Classical.not_not, mem_support_iff, Finset.mem_sdiff, Ne] at hm
  simp [hm.2, hm.1]

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.mem_sdiff, mem_sdiff, mem_support_iff, not_not
-/
theorem support_sdiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support \ q.support subseteq (p + q).support := by
  intro m hm
  simp only [Classical.not_not, mem_support_iff, Finset.mem_sdiff, Ne] at hm
  simp [hm.2, hm.1]

open scoped symmDiff in
/--
theorem `support_symmDiff_support_subset_support_add` / 定理 `support_symmDiff_support_subset_support_add`

English:
theorem support_symmDiff_support_subset_support_add
  given: [DecidableEq σ] (p q : MvPolynomial σ R)
  proof: by
  rw [symmDiff_def]; rw [Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact support_sdiff_support_subset_support_add q p

中文:
定理 support_symmDiff_support_subset_support_add
  条件: [DecidableEq σ] (p q : 多元多项式 σ R)
  证明: by
  rw [symmDiff_def]; rw [Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact support_sdiff_support_subset_support_add q p

Depends on / 依赖: Finset, Finset.sup_eq_union, Finset.union_subset, add_comm, sup_eq_union, support_sdiff_support_subset_support_add, symmDiff_def, union_subset
-/
theorem support_symmDiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support ∆ q.support subseteq (p + q).support := by
  rw [symmDiff_def]; rw [Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact support_sdiff_support_subset_support_add q p

/--
theorem `coeff_mul_monomial'` / 定理 `coeff_mul_monomial'`

English:
theorem coeff_mul_monomial'
  given: (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R)
  proof: by
  classical
  split_ifs with h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : exists j in support p, j + s = m := by
      simpa [Finset.mem_add]
using Finset.add_subset_add_left support_mon

中文:
定理 coeff_mul_monomial'
  条件: (m) (s : σ ->₀ 自然数) (r : R) (p : 多元多项式 σ R)
  证明: by
  classical
  split_ifs with h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : exists j in support p, j + s = m := by
      simpa [Finset.mem_add]
using Finset.add_subset_add_left support_mon

Depends on / 依赖: Finset, Finset.add_subset_add_left, Finset.mem_add, add_subset_add_left, classical, coeff_mul_monomial, contrapose, conv_rhs, le_add_left, le_rfl, mem_add, mem_support_iff, split_ifs, support, support_monomial_subset, support_mul, tsub_add_cancel_of_le
-/
theorem coeff_mul_monomial' (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) :
    coeff m (p * monomial s r) = if s <= m then coeff (m - s) p * r else 0 := by
  classical
  split_ifs with h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : exists j in support p, j + s = m := by
      simpa [Finset.mem_add]
using Finset.add_subset_add_left support_monomial_subset support_mul _ _ h
    exact le_add_left le_rfl

/--
theorem `coeff_monomial_mul'` / 定理 `coeff_monomial_mul'`

English:
theorem coeff_monomial_mul'
  given: (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R)
  proof: by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm]; rw [mul_comm r]
  exact coeff_mul_monomial' _ _ _ _

中文:
定理 coeff_monomial_mul'
  条件: (m) (s : σ ->₀ 自然数) (r : R) (p : 多元多项式 σ R)
  证明: by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm]; rw [mul_comm r]
  exact coeff_mul_monomial' _ _ _ _
-/
theorem coeff_monomial_mul' (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) :
    coeff m (monomial s r * p) = if s <= m then r * coeff (m - s) p else 0 := by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm]; rw [mul_comm r]
  exact coeff_mul_monomial' _ _ _ _

/--
theorem `coeff_mul_X'` / 定理 `coeff_mul_X'`

English:
theorem coeff_mul_X'
  given: [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R)
  proof: by
  refine (coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]

中文:
定理 coeff_mul_X'
  条件: [DecidableEq σ] (m) (s : σ) (p : 多元多项式 σ R)
  证明: by
  refine (coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.single_le_iff, Nat.succ_le_iff, coeff_mul_monomial, mem_support_iff, mul_one, pos_iff_ne_zero, simp_rw, single_le_iff, succ_le_iff
-/
theorem coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (p * X s) = if s in m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]

/--
theorem `coeff_X_mul'` / 定理 `coeff_X_mul'`

English:
theorem coeff_X_mul'
  given: [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R)
  proof: by
  refine (coeff_monomial_mul' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    one_mul]

中文:
定理 coeff_X_mul'
  条件: [DecidableEq σ] (m) (s : σ) (p : 多元多项式 σ R)
  证明: by
  refine (coeff_monomial_mul' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    one_mul]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.single_le_iff, Nat.succ_le_iff, coeff_monomial_mul, mem_support_iff, one_mul, pos_iff_ne_zero, simp_rw, single_le_iff, succ_le_iff
-/
theorem coeff_X_mul' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (X s * p) = if s in m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_monomial_mul' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    one_mul]

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {p : MvPolynomial σ R}
  statement: p = 0 ↔ forall d, coeff d p = 0
  proof: by
  rw [MvPolynomial.ext_iff]
  simp only [coeff_zero]

中文:
定理 eq_zero_iff
  条件: {p : 多元多项式 σ R}
  结论: p = 0 ↔ 对任意 d, coeff d p = 0
  证明: by
  rw [MvPolynomial.ext_iff]
  simp only [coeff_zero]

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, coeff_zero, ext_iff
-/
theorem eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ forall d, coeff d p = 0 := by
  rw [MvPolynomial.ext_iff]
  simp only [coeff_zero]

/--
theorem `ne_zero_iff` / 定理 `ne_zero_iff`

English:
theorem ne_zero_iff
  given: {p : MvPolynomial σ R}
  statement: p != 0 ↔ exists d, coeff d p != 0
  proof: by
  rw [Ne]; rw [eq_zero_iff]
  push Not
  rfl

@[simp]

中文:
定理 ne_zero_iff
  条件: {p : 多元多项式 σ R}
  结论: p != 0 ↔ 存在 d, coeff d p != 0
  证明: by
  rw [Ne]; rw [eq_zero_iff]
  push Not
  rfl

@[simp]

Depends on / 依赖: eq_zero_iff
-/
theorem ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ exists d, coeff d p != 0 := by
  rw [Ne]; rw [eq_zero_iff]
  push Not
  rfl

@[simp]
/--
theorem `X_ne_zero` / 定理 `X_ne_zero`

English:
theorem X_ne_zero
  given: [Nontrivial R] (s : σ)
  proof: by
  rw [ne_zero_iff]
  use Finsupp.single s 1
  simp only [coeff_X_same, ne_eq, one_ne_zero, not_false_eq_true]

中文:
定理 X_ne_zero
  条件: [非平凡 R] (s : σ)
  证明: by
  rw [ne_zero_iff]
  use Finsupp.single s 1
  simp only [coeff_X_same, ne_eq, one_ne_zero, not_false_eq_true]

Depends on / 依赖: Finsupp, Finsupp.single, coeff_X_same, ne_eq, ne_zero_iff, not_false_eq_true, one_ne_zero, single
-/
theorem X_ne_zero [Nontrivial R] (s : σ) :
    X (R := R) s != 0 := by
  rw [ne_zero_iff]
  use Finsupp.single s 1
  simp only [coeff_X_same, ne_eq, one_ne_zero, not_false_eq_true]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  given: {p : MvPolynomial σ R}
  statement: p.support = ∅ ↔ p = 0
  proof: by simp [support]

@[simp]

中文:
定理 support_eq_empty
  条件: {p : 多元多项式 σ R}
  结论: p.support = ∅ ↔ p = 0
  证明: by simp [support]

@[simp]

Depends on / 依赖: support
-/
theorem support_eq_empty {p : MvPolynomial σ R} : p.support = ∅ ↔ p = 0 := by simp [support]

@[simp]
/--
lemma `support_nonempty` / 引理 `support_nonempty`

English:
lemma support_nonempty
  given: {p : MvPolynomial σ R}
  statement: p.support.Nonempty ↔ p != 0
  proof: by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]

中文:
引理 support_nonempty
  条件: {p : 多元多项式 σ R}
  结论: p.support.非空 ↔ p != 0
  证明: by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, ne_eq, nonempty_iff_ne_empty, support_eq_empty
-/
lemma support_nonempty {p : MvPolynomial σ R} : p.support.Nonempty ↔ p != 0 := by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]

/--
theorem `exists_coeff_ne_zero` / 定理 `exists_coeff_ne_zero`

English:
theorem exists_coeff_ne_zero
  given: {p : MvPolynomial σ R} (h : p != 0)
  statement: exists d, coeff d p != 0
  proof: ne_zero_iff.mp h

中文:
定理 存在_coeff_ne_zero
  条件: {p : 多元多项式 σ R} (h : p != 0)
  结论: 存在 d, coeff d p != 0
  证明: ne_zero_iff.mp h

Depends on / 依赖: ne_zero_iff, ne_zero_iff.mp
-/
theorem exists_coeff_ne_zero {p : MvPolynomial σ R} (h : p != 0) : exists d, coeff d p != 0 :=
  ne_zero_iff.mp h

/--
theorem `_root_.IsRegular.monomial` / 定理 `_root_.IsRegular.monomial`

English:
theorem _root_.IsRegular.monomial
  statement: {m : σ ->₀ Nat} {a : R}
  proof: by
  rw [← isLeftRegular_iff_isRegular]
  intro p q h
  ext d
  have h' := congr_arg (coeff (m + d)) h
  simp only [coeff_monomial_mul] at h'
  rw [← ha.left.eq_iff]; rw [h']

@[simp]

中文:
定理 _root_.是正则.monomial
  结论: {m : σ ->₀ 自然数} {a : R}
  证明: by
  rw [← isLeftRegular_iff_isRegular]
  intro p q h
  ext d
  have h' := congr_arg (coeff (m + d)) h
  simp only [coeff_monomial_mul] at h'
  rw [← ha.left.eq_iff]; rw [h']

@[simp]

Depends on / 依赖: coeff_monomial_mul, congr_arg, eq_iff, ha.left.eq_iff, isLeftRegular_iff_isRegular
-/
theorem _root_.IsRegular.monomial {m : σ ->₀ Nat} {a : R}
    (ha : IsRegular a) :
    IsRegular (monomial m a) := by
  rw [← isLeftRegular_iff_isRegular]
  intro p q h
  ext d
  have h' := congr_arg (coeff (m + d)) h
  simp only [coeff_monomial_mul] at h'
  rw [← ha.left.eq_iff]; rw [h']

@[simp]
/--
theorem `monomial_one_mul_cancel_left_iff` / 定理 `monomial_one_mul_cancel_left_iff`

English:
theorem monomial_one_mul_cancel_left_iff
  given: {m : σ ->₀ Nat}
  proof: isRegular_one.monomial.left.eq_iff

@[simp]

中文:
定理 monomial_one_mul_cancel_left_iff
  条件: {m : σ ->₀ 自然数}
  证明: isRegular_one.monomial.left.eq_iff

@[simp]

Depends on / 依赖: eq_iff, isRegular_one, isRegular_one.monomial.left.eq_iff, monomial
-/
theorem monomial_one_mul_cancel_left_iff {m : σ ->₀ Nat} :
    monomial m 1 * p = monomial m 1 * q ↔ p = q :=
  isRegular_one.monomial.left.eq_iff

@[simp]
/--
theorem `X_mul_cancel_left_iff` / 定理 `X_mul_cancel_left_iff`

English:
theorem X_mul_cancel_left_iff
  given: {i : σ}
  proof: monomial_one_mul_cancel_left_iff

@[simp]

中文:
定理 X_mul_cancel_left_iff
  条件: {i : σ}
  证明: monomial_one_mul_cancel_left_iff

@[simp]

Depends on / 依赖: monomial_one_mul_cancel_left_iff
-/
theorem X_mul_cancel_left_iff {i : σ} :
    X i * p = X i * q ↔ p = q :=
  monomial_one_mul_cancel_left_iff

@[simp]
/--
theorem `monomial_one_mul_cancel_right_iff` / 定理 `monomial_one_mul_cancel_right_iff`

English:
theorem monomial_one_mul_cancel_right_iff
  given: {m : σ ->₀ Nat}
  proof: isRegular_one.monomial.right.eq_iff

@[simp]

中文:
定理 monomial_one_mul_cancel_right_iff
  条件: {m : σ ->₀ 自然数}
  证明: isRegular_one.monomial.right.eq_iff

@[simp]

Depends on / 依赖: eq_iff, isRegular_one, isRegular_one.monomial.right.eq_iff, monomial
-/
theorem monomial_one_mul_cancel_right_iff {m : σ ->₀ Nat} :
    p * monomial m 1 = q * monomial m 1 ↔ p = q :=
  isRegular_one.monomial.right.eq_iff

@[simp]
/--
theorem `X_mul_cancel_right_iff` / 定理 `X_mul_cancel_right_iff`

English:
theorem X_mul_cancel_right_iff
  given: {i : σ}
  proof: monomial_one_mul_cancel_right_iff

中文:
定理 X_mul_cancel_right_iff
  条件: {i : σ}
  证明: monomial_one_mul_cancel_right_iff

Depends on / 依赖: monomial_one_mul_cancel_right_iff
-/
theorem X_mul_cancel_right_iff {i : σ} :
    p * X i = q * X i ↔ p = q :=
  monomial_one_mul_cancel_right_iff

/--
theorem `C_dvd_iff_dvd_coeff` / 定理 `C_dvd_iff_dvd_coeff`

English:
theorem C_dvd_iff_dvd_coeff
  given: (r : R) (φ : MvPolynomial σ R)
  statement: C r ∣ φ ↔ forall i, r ∣ φ.coeff i
  proof: by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose C hc using h
    classical
      let c' : (σ ->₀ Nat) -> R := fun i => if i in φ.support then C i else 0
      let ψ : MvPolynomial σ R := ∑ i in φ.support, monomial i (c' i)
      use ψ
      

中文:
定理 C_dvd_iff_dvd_coeff
  条件: (r : R) (φ : 多元多项式 σ R)
  结论: C r ∣ φ ↔ 对任意 i, r ∣ φ.coeff i
  证明: by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose C hc using h
    classical
      let c' : (σ ->₀ Nat) -> R := fun i => if i in φ.support then C i else 0
      let ψ : MvPolynomial σ R := ∑ i in φ.support, monomial i (c' i)
      use ψ
      

Depends on / 依赖: Finset, Finset.sum_ite_eq, MvPolynomial, MvPolynomial.ext, classical, coeff_C_mul, coeff_monomial, coeff_sum, dvd_mul_right, monomial, mul_zero, notMem_support_iff, split_ifs, sum_ite_eq, support
-/
theorem C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : C r ∣ φ ↔ forall i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose C hc using h
    classical
      let c' : (σ ->₀ Nat) -> R := fun i => if i in φ.support then C i else 0
      let ψ : MvPolynomial σ R := ∑ i in φ.support, monomial i (c' i)
      use ψ
      apply MvPolynomial.ext
      intro i
      simp only [ψ, c', coeff_C_mul, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [notMem_support_iff] at hi
        rwa [mul_zero]

/--
lemma `isRegular_X` / 引理 `isRegular_X`

English:
lemma isRegular_X
  statement: IsRegular (X n : MvPolynomial σ R)
  proof: by
  suffices IsLeftRegular (X n : MvPolynomial σ R) from
⟨this, this.right_of_commute Commute.all _⟩
  intro P Q (hPQ : (X n) * P = (X n) * Q)
  ext i
  rw [← coeff_X_mul i n P]; rw [hPQ]; rw [coeff_X_mul i n Q]

中文:
引理 isRegular_X
  结论: 是正则 (X n : 多元多项式 σ R)
  证明: by
  suffices IsLeftRegular (X n : MvPolynomial σ R) from
⟨this, this.right_of_commute Commute.all _⟩
  intro P Q (hPQ : (X n) * P = (X n) * Q)
  ext i
  rw [← coeff_X_mul i n P]; rw [hPQ]; rw [coeff_X_mul i n Q]
-/
@[simp] lemma isRegular_X : IsRegular (X n : MvPolynomial σ R) := by
  suffices IsLeftRegular (X n : MvPolynomial σ R) from
⟨this, this.right_of_commute Commute.all _⟩
  intro P Q (hPQ : (X n) * P = (X n) * Q)
  ext i
  rw [← coeff_X_mul i n P]; rw [hPQ]; rw [coeff_X_mul i n Q]

/--
lemma `isRegular_X_pow` / 引理 `isRegular_X_pow`

English:
lemma isRegular_X_pow
  given: (k : Nat)
  statement: IsRegular (X n ^ k : MvPolynomial σ R)
  proof: isRegular_X.pow k

中文:
引理 isRegular_X_pow
  条件: (k : 自然数)
  结论: 是正则 (X n ^ k : 多元多项式 σ R)
  证明: isRegular_X.pow k
-/
@[simp] lemma isRegular_X_pow (k : Nat) : IsRegular (X n ^ k : MvPolynomial σ R) := isRegular_X.pow k

/--
lemma `isRegular_prod_X` / 引理 `isRegular_prod_X`

English:
lemma isRegular_prod_X
  given: (s : Finset σ)
  proof: IsRegular.prod fun _ _ => isRegular_X

中文:
引理 isRegular_prod_X
  条件: (s : 有限集 σ)
  证明: IsRegular.prod fun _ _ => isRegular_X
-/
@[simp] lemma isRegular_prod_X (s : Finset σ) :
    IsRegular (∏ n in s, X n : MvPolynomial σ R) :=
  IsRegular.prod fun _ _ => isRegular_X

/--
Definition of `coeffs` / `coeffs` 的定义

English:
definition coeffs
  signature: (p : MvPolynomial σ R)
  body: letI := Classical.decEq R
  Finset.image p.coeff p.support

@[simp]

中文:
定义 coeffs
  签名: (p : 多元多项式 σ R)
  定义体: letI := Classical.decEq R
  Finset.image p.coeff p.support

@[simp]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.image, p.coeff, p.support, support
-/
def coeffs (p : MvPolynomial σ R) : Finset R :=
  letI := Classical.decEq R
  Finset.image p.coeff p.support

@[simp]
/--
lemma `coeffs_zero` / 引理 `coeffs_zero`

English:
lemma coeffs_zero
  statement: coeffs (0 : MvPolynomial σ R) = ∅
  proof: rfl

中文:
引理 coeffs_zero
  结论: coeffs (0 : 多元多项式 σ R) = ∅
  证明: rfl
-/
lemma coeffs_zero : coeffs (0 : MvPolynomial σ R) = ∅ :=
  rfl

/--
lemma `coeffs_one` / 引理 `coeffs_one`

English:
lemma coeffs_one
  statement: coeffs (1 : MvPolynomial σ R) subseteq {1}
  proof: by
  classical
    rw [coeffs]; rw [Finset.image_subset_iff]
    simp_all [coeff_one]

@[nontriviality]

中文:
引理 coeffs_one
  结论: coeffs (1 : 多元多项式 σ R) subseteq {1}
  证明: by
  classical
    rw [coeffs]; rw [Finset.image_subset_iff]
    simp_all [coeff_one]

@[nontriviality]

Depends on / 依赖: Finset, Finset.image_subset_iff, classical, coeff_one, coeffs, image_subset_iff
-/
lemma coeffs_one : coeffs (1 : MvPolynomial σ R) subseteq {1} := by
  classical
    rw [coeffs]; rw [Finset.image_subset_iff]
    simp_all [coeff_one]

@[nontriviality]
/--
lemma `coeffs_eq_empty_of_subsingleton` / 引理 `coeffs_eq_empty_of_subsingleton`

English:
lemma coeffs_eq_empty_of_subsingleton
  given: [Subsingleton R] (p : MvPolynomial σ R)
  statement: p.coeffs = ∅
  proof: by
  simpa [coeffs] using Subsingleton.eq_zero p

@[simp]

中文:
引理 coeffs_eq_empty_of_subsingleton
  条件: [子单例 R] (p : 多元多项式 σ R)
  结论: p.coeffs = ∅
  证明: by
  simpa [coeffs] using Subsingleton.eq_zero p

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, coeffs, eq_zero
-/
lemma coeffs_eq_empty_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : p.coeffs = ∅ := by
  simpa [coeffs] using Subsingleton.eq_zero p

@[simp]
/--
lemma `coeffs_one_of_nontrivial` / 引理 `coeffs_one_of_nontrivial`

English:
lemma coeffs_one_of_nontrivial
  given: [Nontrivial R]
  statement: coeffs (1 : MvPolynomial σ R) = {1}
  proof: by
  apply Finset.Subset.antisymm coeffs_one
  simp only [coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩

中文:
引理 coeffs_one_of_nontrivial
  条件: [非平凡 R]
  结论: coeffs (1 : 多元多项式 σ R) = {1}
  证明: by
  apply Finset.Subset.antisymm coeffs_one
  simp only [coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩

Depends on / 依赖: Finset, Finset.Subset.antisymm, Finset.mem_image, Finset.singleton_subset_iff, Subset, antisymm, coeffs, coeffs_one, mem_image, singleton_subset_iff
-/
lemma coeffs_one_of_nontrivial [Nontrivial R] : coeffs (1 : MvPolynomial σ R) = {1} := by
  apply Finset.Subset.antisymm coeffs_one
  simp only [coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩

/--
lemma `mem_coeffs_iff` / 引理 `mem_coeffs_iff`

English:
lemma mem_coeffs_iff
  given: {p : MvPolynomial σ R} {c : R}
  proof: by
  simp [coeffs, eq_comm, (Finset.mem_image)]

中文:
引理 mem_coeffs_iff
  条件: {p : 多元多项式 σ R} {c : R}
  证明: by
  simp [coeffs, eq_comm, (Finset.mem_image)]

Depends on / 依赖: Finset, Finset.mem_image, coeffs, eq_comm, mem_image
-/
lemma mem_coeffs_iff {p : MvPolynomial σ R} {c : R} :
    c in p.coeffs ↔ exists n in p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]

/--
lemma `coeff_mem_coeffs` / 引理 `coeff_mem_coeffs`

English:
lemma coeff_mem_coeffs
  statement: {p : MvPolynomial σ R} (m : σ ->₀ Nat)
  proof: letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (mem_support_iff.mpr h)

中文:
引理 coeff_mem_coeffs
  结论: {p : 多元多项式 σ R} (m : σ ->₀ 自然数)
  证明: letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (mem_support_iff.mpr h)

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.mem_image_of_mem, mem_image_of_mem, mem_support_iff, mem_support_iff.mpr, p.coeff
-/
lemma coeff_mem_coeffs {p : MvPolynomial σ R} (m : σ ->₀ Nat)
    (h : p.coeff m != 0) : p.coeff m in p.coeffs :=
  letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (mem_support_iff.mpr h)

/--
lemma `zero_notMem_coeffs` / 引理 `zero_notMem_coeffs`

English:
lemma zero_notMem_coeffs
  given: (p : MvPolynomial σ R)
  statement: 0 ∉ p.coeffs
  proof: by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := mem_coeffs_iff.mp hz
  exact (mem_support_iff.mp hnsupp) hn.symm

中文:
引理 zero_notMem_coeffs
  条件: (p : 多元多项式 σ R)
  结论: 0 ∉ p.coeffs
  证明: by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := mem_coeffs_iff.mp hz
  exact (mem_support_iff.mp hnsupp) hn.symm

Depends on / 依赖: FloorRing, FloorRing.archimedean, LinearOrder, archimedean, hn.symm, hnsupp, mem_coeffs_iff, mem_coeffs_iff.mp, mem_support_iff, mem_support_iff.mp
-/
lemma zero_notMem_coeffs (p : MvPolynomial σ R) : 0 ∉ p.coeffs := by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := mem_coeffs_iff.mp hz
  exact (mem_support_iff.mp hnsupp) hn.symm

/--
lemma `coeffs_C` / 引理 `coeffs_C`

English:
lemma coeffs_C
  given: [DecidableEq R] (r : R)
  statement: (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r}
  proof: by
  classical
  aesop (add simp mem_coeffs_iff)

中文:
引理 coeffs_C
  条件: [DecidableEq R] (r : R)
  结论: (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r}
  证明: by
  classical
  aesop (add simp mem_coeffs_iff)

Depends on / 依赖: classical, coeffs, mem_coeffs_iff
-/
lemma coeffs_C [DecidableEq R] (r : R) : (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r} := by
  classical
  aesop (add simp mem_coeffs_iff)

/--
lemma `coeffs_C_subset` / 引理 `coeffs_C_subset`

English:
lemma coeffs_C_subset
  given: (r : R)
  statement: (C (σ := σ) r).coeffs subseteq {r}
  proof: by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]

中文:
引理 coeffs_C_subset
  条件: (r : R)
  结论: (C (σ := σ) r).coeffs subseteq {r}
  证明: by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]

Depends on / 依赖: classical, coeffs, coeffs_C, subseteq
-/
lemma coeffs_C_subset (r : R) : (C (σ := σ) r).coeffs subseteq {r} := by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]
/--
lemma `coeffs_mul_X` / 引理 `coeffs_mul_X`

English:
lemma coeffs_mul_X
  given: (p : MvPolynomial σ R) (n : σ)
  statement: (p * X n).coeffs = p.coeffs
  proof: by
  aesop (add simp mem_coeffs_iff)

@[simp]

中文:
引理 coeffs_mul_X
  条件: (p : 多元多项式 σ R) (n : σ)
  结论: (p * X n).coeffs = p.coeffs
  证明: by
  aesop (add simp mem_coeffs_iff)

@[simp]

Depends on / 依赖: mem_coeffs_iff
-/
lemma coeffs_mul_X (p : MvPolynomial σ R) (n : σ) : (p * X n).coeffs = p.coeffs := by
  aesop (add simp mem_coeffs_iff)

@[simp]
/--
lemma `coeffs_X_mul` / 引理 `coeffs_X_mul`

English:
lemma coeffs_X_mul
  given: (p : MvPolynomial σ R) (n : σ)
  statement: (X n * p).coeffs = p.coeffs
  proof: by
  aesop (add simp mem_coeffs_iff)

中文:
引理 coeffs_X_mul
  条件: (p : 多元多项式 σ R) (n : σ)
  结论: (X n * p).coeffs = p.coeffs
  证明: by
  aesop (add simp mem_coeffs_iff)

Depends on / 依赖: mem_coeffs_iff
-/
lemma coeffs_X_mul (p : MvPolynomial σ R) (n : σ) : (X n * p).coeffs = p.coeffs := by
  aesop (add simp mem_coeffs_iff)

/--
lemma `coeffs_add` / 引理 `coeffs_add`

English:
lemma coeffs_add
  given: [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.support q.support)
  proof: by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ ->₀ Nat) (hne : p.coeff n != 0) : q.coeff n = 0 :=
notMem_support_iff.mp h.notMem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ ->₀ Nat) (hne : q.coeff n != 0) : p.coeff n = 

中文:
引理 coeffs_add
  条件: [DecidableEq R] {p q : 多元多项式 σ R} (h : Disjoint p.support q.support)
  证明: by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ ->₀ Nat) (hne : p.coeff n != 0) : q.coeff n = 0 :=
notMem_support_iff.mp h.notMem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ ->₀ Nat) (hne : q.coeff n != 0) : p.coeff n = 

Depends on / 依赖: Finset, Finset.mem_union, coeff_add, h.notMem_of_mem_left_finset, h.notMem_of_mem_right_finset, mem_coeffs_iff, mem_support_iff, mem_support_iff.mpr, mem_union, ne_eq, notMem_of_mem_left_finset, notMem_of_mem_right_finset, notMem_support_iff, notMem_support_iff.mp, p.coeff, q.coeff
-/
lemma coeffs_add [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.support q.support) :
    (p + q).coeffs = p.coeffs union q.coeffs := by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ ->₀ Nat) (hne : p.coeff n != 0) : q.coeff n = 0 :=
notMem_support_iff.mp h.notMem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ ->₀ Nat) (hne : q.coeff n != 0) : p.coeff n = 0 :=
notMem_support_iff.mp h.notMem_of_mem_right_finset (mem_support_iff.mpr hne)
  have hor (n) (h : ¬coeff n p + coeff n q = 0) : coeff n p != 0 ∨ coeff n q != 0 := by
    by_cases hp : coeff n p = 0 <;> simp_all
  refine ⟨fun ⟨n, hn1, hn2⟩ => ?_, ?_⟩
  · obtain (h | h) := hor n hn1
    · exact Or.inl ⟨n, by simp [h, hn2, hl n h]⟩
    · exact Or.inr ⟨n, by simp [h, hn2, hr n h]⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨n, by simp [hl n hn, hn]⟩
    · exact ⟨n, by simp [hr n hn, hn]⟩

end Coeff

section ConstantCoeff

/--
Definition of `constantCoeff` / `constantCoeff` 的定义

English:
definition constantCoeff
  signature: : MvPolynomial σ R ->+* R where
  body: coeff 0
  map_one' := by simp
  map_mul' := by classical simp [coeff_mul]
  map_zero' := coeff_zero _
  map_add' := coeff_add _

中文:
定义 constantCoeff
  签名: : 多元多项式 σ R ->+* R where
  定义体: coeff 0
  map_one' := by simp
  map_mul' := by classical simp [coeff_mul]
  map_zero' := coeff_zero _
  map_add' := coeff_add _
-/
def constantCoeff : MvPolynomial σ R ->+* R where
  toFun := coeff 0
  map_one' := by simp
  map_mul' := by classical simp [coeff_mul]
  map_zero' := coeff_zero _
  map_add' := coeff_add _

/--
theorem `constantCoeff_eq` / 定理 `constantCoeff_eq`

English:
theorem constantCoeff_eq
  statement: (constantCoeff : MvPolynomial σ R -> R) = coeff 0
  proof: rfl

中文:
定理 constantCoeff_eq
  结论: (constantCoeff : 多元多项式 σ R -> R) = coeff 0
  证明: rfl
-/
theorem constantCoeff_eq : (constantCoeff : MvPolynomial σ R -> R) = coeff 0 :=
  rfl

variable (σ) in
@[simp]
/--
theorem `constantCoeff_C` / 定理 `constantCoeff_C`

English:
theorem constantCoeff_C
  given: (r : R)
  statement: constantCoeff (C r : MvPolynomial σ R) = r
  proof: by
  simp [constantCoeff_eq]

中文:
定理 constantCoeff_C
  条件: (r : R)
  结论: constantCoeff (C r : 多元多项式 σ R) = r
  证明: by
  simp [constantCoeff_eq]

Depends on / 依赖: constantCoeff_eq
-/
theorem constantCoeff_C (r : R) : constantCoeff (C r : MvPolynomial σ R) = r := by
  simp [constantCoeff_eq]

variable (R) in
@[simp]
/--
theorem `constantCoeff_X` / 定理 `constantCoeff_X`

English:
theorem constantCoeff_X
  given: (i : σ)
  statement: constantCoeff (X i : MvPolynomial σ R) = 0
  proof: by
  simp [constantCoeff_eq]

@[simp]

中文:
定理 constantCoeff_X
  条件: (i : σ)
  结论: constantCoeff (X i : 多元多项式 σ R) = 0
  证明: by
  simp [constantCoeff_eq]

@[simp]

Depends on / 依赖: constantCoeff_eq
-/
theorem constantCoeff_X (i : σ) : constantCoeff (X i : MvPolynomial σ R) = 0 := by
  simp [constantCoeff_eq]

@[simp]
/--
theorem `constantCoeff_smul` / 定理 `constantCoeff_smul`

English:
theorem constantCoeff_smul
  given: {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynomial σ S₁)
  proof: rfl

中文:
定理 constantCoeff_smul
  条件: {R : 类型} [SMulZero类 R S₁] (a : R) (f : 多元多项式 σ S₁)
  证明: rfl
-/
theorem constantCoeff_smul {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynomial σ S₁) :
    constantCoeff (a • f) = a • constantCoeff f :=
  rfl

/--
theorem `constantCoeff_monomial` / 定理 `constantCoeff_monomial`

English:
theorem constantCoeff_monomial
  given: [DecidableEq σ] (d : σ ->₀ Nat) (r : R)
  proof: by
  rw [constantCoeff_eq]; rw [coeff_monomial]

中文:
定理 constantCoeff_monomial
  条件: [DecidableEq σ] (d : σ ->₀ 自然数) (r : R)
  证明: by
  rw [constantCoeff_eq]; rw [coeff_monomial]

Depends on / 依赖: coeff_monomial, constantCoeff_eq
-/
theorem constantCoeff_monomial [DecidableEq σ] (d : σ ->₀ Nat) (r : R) :
    constantCoeff (monomial d r) = if d = 0 then r else 0 := by
  rw [constantCoeff_eq]; rw [coeff_monomial]

variable (σ R)

@[simp]
/--
theorem `constantCoeff_comp_C` / 定理 `constantCoeff_comp_C`

English:
theorem constantCoeff_comp_C
  statement: constantCoeff.comp (C : R ->+* MvPolynomial σ R) = RingHom.id R
  proof: by
  ext x
  exact constantCoeff_C σ x

中文:
定理 constantCoeff_comp_C
  结论: constantCoeff.comp (C : R ->+* 多元多项式 σ R) = 环态射.id R
  证明: by
  ext x
  exact constantCoeff_C σ x

Depends on / 依赖: constantCoeff_C
-/
theorem constantCoeff_comp_C : constantCoeff.comp (C : R ->+* MvPolynomial σ R) = RingHom.id R := by
  ext x
  exact constantCoeff_C σ x

/--
theorem `constantCoeff_comp_algebraMap` / 定理 `constantCoeff_comp_algebraMap`

English:
theorem constantCoeff_comp_algebraMap
  proof: constantCoeff_comp_C _ _

中文:
定理 constantCoeff_comp_algebraMap
  证明: constantCoeff_comp_C _ _

Depends on / 依赖: constantCoeff_comp_C
-/
theorem constantCoeff_comp_algebraMap :
    constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R :=
  constantCoeff_comp_C _ _

end ConstantCoeff

section AsSum

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `support_sum_monomial_coeff` / 定理 `support_sum_monomial_coeff`

English:
theorem support_sum_monomial_coeff
  given: (p : MvPolynomial σ R)
  proof: by
  apply AddMonoidAlgebra.ext; rw [AddMonoidAlgebra.coeff_sum]; exact Finsupp.sum_single _

中文:
定理 support_sum_monomial_coeff
  条件: (p : 多元多项式 σ R)
  证明: by
  apply AddMonoidAlgebra.ext; rw [AddMonoidAlgebra.coeff_sum]; exact Finsupp.sum_single _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.ext, Finsupp, Finsupp.sum_single, coeff_sum, sum_single
-/
theorem support_sum_monomial_coeff (p : MvPolynomial σ R) :
    ∑ v in p.support, monomial v (coeff v p) = p := by
  apply AddMonoidAlgebra.ext; rw [AddMonoidAlgebra.coeff_sum]; exact Finsupp.sum_single _

/--
theorem `as_sum` / 定理 `as_sum`

English:
theorem as_sum
  given: (p : MvPolynomial σ R)
  statement: p = ∑ v in p.support, monomial v (coeff v p)
  proof: (support_sum_monomial_coeff p).symm

中文:
定理 as_sum
  条件: (p : 多元多项式 σ R)
  结论: p = ∑ v in p.support, monomial v (coeff v p)
  证明: (support_sum_monomial_coeff p).symm

Depends on / 依赖: support_sum_monomial_coeff
-/
theorem as_sum (p : MvPolynomial σ R) : p = ∑ v in p.support, monomial v (coeff v p) :=
  (support_sum_monomial_coeff p).symm

end AsSum

section coeffsIn
variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

section Module
variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ ->₀ Nat} {x : S}
  {n : Nat}

variable (σ M) in
/-- The `R`-submodule of multivariate polynomials whose coefficients lie in an `R`-submodule `M`. -/
@[simps]
/--
Definition of `coeffsIn` / `coeffsIn` 的定义

English:
definition coeffsIn
  signature: : Submodule R (MvPolynomial σ S) where
  body: {p | forall i, p.coeff i in M}
  add_mem' := by simp +contextual [add_mem]
  zero_mem' := by simp
  smul_mem' r p hp i := Submodule.smul_mem _ _ (hp i)

中文:
定义 coeffsIn
  签名: : 子模 R (多元多项式 σ S) where
  定义体: {p | forall i, p.coeff i in M}
  add_mem' := by simp +contextual [add_mem]
  zero_mem' := by simp
  smul_mem' r p hp i := Submodule.smul_mem _ _ (hp i)

Depends on / 依赖: p.coeff
-/
def coeffsIn : Submodule R (MvPolynomial σ S) where
  carrier := {p | forall i, p.coeff i in M}
  add_mem' := by simp +contextual [add_mem]
  zero_mem' := by simp
  smul_mem' r p hp i := Submodule.smul_mem _ _ (hp i)

/--
lemma `mem_coeffsIn` / 引理 `mem_coeffsIn`

English:
lemma mem_coeffsIn
  statement: p in coeffsIn σ M ↔ forall i, p.coeff i in M
  proof: .rfl

@[simp]

中文:
引理 mem_coeffsIn
  结论: p in coeffsIn σ M ↔ 对任意 i, p.coeff i in M
  证明: .rfl

@[simp]
-/
lemma mem_coeffsIn : p in coeffsIn σ M ↔ forall i, p.coeff i in M := .rfl

@[simp]
/--
lemma `monomial_mem_coeffsIn` / 引理 `monomial_mem_coeffsIn`

English:
lemma monomial_mem_coeffsIn
  statement: monomial i x in coeffsIn σ M ↔ x in M
  proof: by
  classical
  simp only [mem_coeffsIn, coeff_monomial]
  exact ⟨fun h => by simpa using h i, fun hs j => by split <;> simp [hs]⟩

@[simp]

中文:
引理 monomial_mem_coeffsIn
  结论: monomial i x in coeffsIn σ M ↔ x in M
  证明: by
  classical
  simp only [mem_coeffsIn, coeff_monomial]
  exact ⟨fun h => by simpa using h i, fun hs j => by split <;> simp [hs]⟩

@[simp]

Depends on / 依赖: classical, coeff_monomial, mem_coeffsIn
-/
lemma monomial_mem_coeffsIn : monomial i x in coeffsIn σ M ↔ x in M := by
  classical
  simp only [mem_coeffsIn, coeff_monomial]
  exact ⟨fun h => by simpa using h i, fun hs j => by split <;> simp [hs]⟩

@[simp]
/--
lemma `C_mem_coeffsIn` / 引理 `C_mem_coeffsIn`

English:
lemma C_mem_coeffsIn
  statement: C x in coeffsIn σ M ↔ x in M
  proof: by simpa using monomial_mem_coeffsIn (i := 0)

@[simp]

中文:
引理 C_mem_coeffsIn
  结论: C x in coeffsIn σ M ↔ x in M
  证明: by simpa using monomial_mem_coeffsIn (i := 0)

@[simp]

Depends on / 依赖: monomial_mem_coeffsIn
-/
lemma C_mem_coeffsIn : C x in coeffsIn σ M ↔ x in M := by simpa using monomial_mem_coeffsIn (i := 0)

@[simp]
/--
lemma `one_coeffsIn` / 引理 `one_coeffsIn`

English:
lemma one_coeffsIn
  statement: 1 in coeffsIn σ M ↔ 1 in M
  proof: by simpa using C_mem_coeffsIn (x := (1 : S))

@[simp]

中文:
引理 one_coeffsIn
  结论: 1 in coeffsIn σ M ↔ 1 in M
  证明: by simpa using C_mem_coeffsIn (x := (1 : S))

@[simp]

Depends on / 依赖: C_mem_coeffsIn
-/
lemma one_coeffsIn : 1 in coeffsIn σ M ↔ 1 in M := by simpa using C_mem_coeffsIn (x := (1 : S))

@[simp]
/--
lemma `mul_monomial_mem_coeffsIn` / 引理 `mul_monomial_mem_coeffsIn`

English:
lemma mul_monomial_mem_coeffsIn
  statement: p * monomial i 1 in coeffsIn σ M ↔ p in coeffsIn σ M
  proof: by
  simp only [mem_coeffsIn, coeff_mul_monomial']
  constructor
  · rintro hp j
    simpa using hp (j + i)
  · rintro hp i
    split <;> simp [hp]

@[simp]

中文:
引理 mul_monomial_mem_coeffsIn
  结论: p * monomial i 1 in coeffsIn σ M ↔ p in coeffsIn σ M
  证明: by
  simp only [mem_coeffsIn, coeff_mul_monomial']
  constructor
  · rintro hp j
    simpa using hp (j + i)
  · rintro hp i
    split <;> simp [hp]

@[simp]

Depends on / 依赖: coeff_mul_monomial, mem_coeffsIn
-/
lemma mul_monomial_mem_coeffsIn : p * monomial i 1 in coeffsIn σ M ↔ p in coeffsIn σ M := by
  simp only [mem_coeffsIn, coeff_mul_monomial']
  constructor
  · rintro hp j
    simpa using hp (j + i)
  · rintro hp i
    split <;> simp [hp]

@[simp]
/--
lemma `monomial_mul_mem_coeffsIn` / 引理 `monomial_mul_mem_coeffsIn`

English:
lemma monomial_mul_mem_coeffsIn
  statement: monomial i 1 * p in coeffsIn σ M ↔ p in coeffsIn σ M
  proof: by
  simp [mul_comm]

@[simp]

中文:
引理 monomial_mul_mem_coeffsIn
  结论: monomial i 1 * p in coeffsIn σ M ↔ p in coeffsIn σ M
  证明: by
  simp [mul_comm]

@[simp]

Depends on / 依赖: mul_comm
-/
lemma monomial_mul_mem_coeffsIn : monomial i 1 * p in coeffsIn σ M ↔ p in coeffsIn σ M := by
  simp [mul_comm]

@[simp]
/--
lemma `mul_X_mem_coeffsIn` / 引理 `mul_X_mem_coeffsIn`

English:
lemma mul_X_mem_coeffsIn
  statement: p * X s in coeffsIn σ M ↔ p in coeffsIn σ M
  proof: by
  simpa [-mul_monomial_mem_coeffsIn] using! mul_monomial_mem_coeffsIn (i := .single s 1)

@[simp]

中文:
引理 mul_X_mem_coeffsIn
  结论: p * X s in coeffsIn σ M ↔ p in coeffsIn σ M
  证明: by
  simpa [-mul_monomial_mem_coeffsIn] using! mul_monomial_mem_coeffsIn (i := .single s 1)

@[simp]

Depends on / 依赖: mul_monomial_mem_coeffsIn, single
-/
lemma mul_X_mem_coeffsIn : p * X s in coeffsIn σ M ↔ p in coeffsIn σ M := by
  simpa [-mul_monomial_mem_coeffsIn] using! mul_monomial_mem_coeffsIn (i := .single s 1)

@[simp]
/--
lemma `X_mul_mem_coeffsIn` / 引理 `X_mul_mem_coeffsIn`

English:
lemma X_mul_mem_coeffsIn
  statement: X s * p in coeffsIn σ M ↔ p in coeffsIn σ M
  proof: by simp [mul_comm]

中文:
引理 X_mul_mem_coeffsIn
  结论: X s * p in coeffsIn σ M ↔ p in coeffsIn σ M
  证明: by simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma X_mul_mem_coeffsIn : X s * p in coeffsIn σ M ↔ p in coeffsIn σ M := by simp [mul_comm]

variable (M) in
/--
lemma `coeffsIn_eq_span_monomial` / 引理 `coeffsIn_eq_span_monomial`

English:
lemma coeffsIn_eq_span_monomial
  statement: coeffsIn σ M = .span R {monomial i m | (m in M) (i : σ ->₀ Nat)}
  proof: by
  classical
refine le_antisymm ?_ Submodule.span_le.2 ?_
  · rintro p hp
    rw [p.as_sum]
    exact sum_mem fun i hi => Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]

中文:
引理 coeffsIn_eq_span_monomial
  结论: coeffsIn σ M = .span R {monomial i m | (m in M) (i : σ ->₀ 自然数)}
  证明: by
  classical
refine le_antisymm ?_ Submodule.span_le.2 ?_
  · rintro p hp
    rw [p.as_sum]
    exact sum_mem fun i hi => Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]

Depends on / 依赖: Submodule, Submodule.span_le, Submodule.subset_span, as_sum, classical, le_antisymm, p.as_sum, span_le, subset_span, sum_mem
-/
lemma coeffsIn_eq_span_monomial : coeffsIn σ M = .span R {monomial i m | (m in M) (i : σ ->₀ Nat)} := by
  classical
refine le_antisymm ?_ Submodule.span_le.2 ?_
  · rintro p hp
    rw [p.as_sum]
    exact sum_mem fun i hi => Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]

/--
lemma `coeffsIn_le` / 引理 `coeffsIn_le`

English:
lemma coeffsIn_le
  given: {N : Submodule R (MvPolynomial σ S)}
  proof: by
  simp [coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_comm (α := MvPolynomial σ S)]

中文:
引理 coeffsIn_le
  条件: {N : 子模 R (多元多项式 σ S)}
  证明: by
  simp [coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_comm (α := MvPolynomial σ S)]

Depends on / 依赖: MvPolynomial, Set.subset_def, Submodule, Submodule.span_le, coeffsIn_eq_span_monomial, forall_comm, span_le, subset_def
-/
lemma coeffsIn_le {N : Submodule R (MvPolynomial σ S)} :
    coeffsIn σ M <= N ↔ forall m in M, forall i, monomial i m in N := by
  simp [coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_comm (α := MvPolynomial σ S)]

/--
lemma `mem_coeffsIn_iff_coeffs_subset` / 引理 `mem_coeffsIn_iff_coeffs_subset`

English:
lemma mem_coeffsIn_iff_coeffs_subset
  statement: p in coeffsIn σ M ↔ (p.coeffs : Set S) subseteq M
  proof: by
  simp only [mem_coeffsIn, coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ => h x, fun h i => ?_⟩
  by_cases hp : i in p.support
  · exact h hp
  · convert! M.zero_mem
    simpa using hp

中文:
引理 mem_coeffsIn_iff_coeffs_subset
  结论: p in coeffsIn σ M ↔ (p.coeffs : 集合 S) subseteq M
  证明: by
  simp only [mem_coeffsIn, coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ => h x, fun h i => ?_⟩
  by_cases hp : i in p.support
  · exact h hp
  · convert! M.zero_mem
    simpa using hp

Depends on / 依赖: Finset, Finset.coe_image, M.zero_mem, coe_image, coeffs, convert, image_subset_iff, mem_coeffsIn, p.support, support, zero_mem
-/
lemma mem_coeffsIn_iff_coeffs_subset : p in coeffsIn σ M ↔ (p.coeffs : Set S) subseteq M := by
  simp only [mem_coeffsIn, coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ => h x, fun h i => ?_⟩
  by_cases hp : i in p.support
  · exact h hp
  · convert! M.zero_mem
    simpa using hp

end Module

section Algebra
variable [Algebra R S] {M : Submodule R S}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coeffsIn_mul` / 引理 `coeffsIn_mul`

English:
lemma coeffsIn_mul
  given: (M N : Submodule R S)
  statement: coeffsIn σ (M * N) = coeffsIn σ M * coeffsIn σ N
  proof: by
  classical
  refine le_antisymm (coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s]; rw [← monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] 

中文:
引理 coeffsIn_mul
  条件: (M N : 子模 R S)
  结论: coeffsIn σ (M * N) = coeffsIn σ M * coeffsIn σ N
  证明: by
  classical
  refine le_antisymm (coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s]; rw [← monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] 

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_mul, Submodule, Submodule.mul_induction_on, Submodule.mul_le, Submodule.mul_mem_mul, add_mem, add_zero, classical, coeff_mul, coeffsIn_le, le_antisymm, map_add, mem_mul_mem, monomial_mul, mul_induction_on, mul_le, mul_mem_mul, sum_mem
-/
lemma coeffsIn_mul (M N : Submodule R S) : coeffsIn σ (M * N) = coeffsIn σ M * coeffsIn σ N := by
  classical
  refine le_antisymm (coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s]; rw [← monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] using add_mem hx hy
  · rw [Submodule.mul_le]
    intro x hx y hy k
    rw [MvPolynomial.coeff_mul]
    exact sum_mem fun c hc => Submodule.mul_mem_mul (hx _) (hy _)

/--
lemma `coeffsIn_pow` / 引理 `coeffsIn_pow`

English:
lemma coeffsIn_pow
  statement: forall {n}, n != 0 -> forall M : Submodule R S, coeffsIn σ (M ^ n) = coeffsIn σ M ^ n

中文:
引理 coeffsIn_pow
  结论: 对任意 {n}, n != 0 -> 对任意 M : 子模 R S, coeffsIn σ (M ^ n) = coeffsIn σ M ^ n
-/
lemma coeffsIn_pow : forall {n}, n != 0 -> forall M : Submodule R S, coeffsIn σ (M ^ n) = coeffsIn σ M ^ n
  | 1, _, M => by simp
  | n + 2, _, M => by rw [pow_succ, coeffsIn_mul, coeffsIn_pow, ← pow_succ]; exact n.succ_ne_zero

/--
lemma `le_coeffsIn_pow` / 引理 `le_coeffsIn_pow`

English:
lemma le_coeffsIn_pow
  statement: forall {n}, coeffsIn σ M ^ n <= coeffsIn σ (M ^ n)

中文:
引理 le_coeffsIn_pow
  结论: 对任意 {n}, coeffsIn σ M ^ n <= coeffsIn σ (M ^ n)
-/
lemma le_coeffsIn_pow : forall {n}, coeffsIn σ M ^ n <= coeffsIn σ (M ^ n)
  | 0 => by simpa using ⟨1, map_one _⟩
  | n + 1 => (coeffsIn_pow n.succ_ne_zero _).ge

end Algebra
end coeffsIn

end CommSemiring

meta section Meta

open Mathlib.Tactic.Polynomial in
/-- Infer base ring for `MvPolynomial _ R`. Used by the `polynomial` tactic. -/
@[polynomial_infer_base]
/--
Definition of `mvPolynomialInferBaseImpl` / `mvPolynomialInferBaseImpl` 的定义

English:
definition mvPolynomialInferBaseImpl
  signature: : PolynomialExt where
  body: do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure

中文:
定义 mvPolynomialInferBaseImpl
  签名: : PolynomialExt where
  定义体: do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure
-/
def mvPolynomialInferBaseImpl : PolynomialExt where
  infer e := do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure

end Meta

end MvPolynomial
