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

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
/-
**MvPolynomial** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R]
参数：σ : Type*；R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring
-/
abbrev MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring
variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s` -/
/-
**MvPolynomial.monomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：monomial (s : σ ->₀ Nat) : R ->ₗ[R] MvPolynomial σ R
参数：s : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`monomial s a` is the monomial with coefficient `a` and exponents given by `s`
-/
def monomial (s : σ →₀ ℕ) : R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.lsingle s
/-
**MvPolynomial.one_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：one_def : (1 : MvPolynomial σ R) = monomial 0 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : MvPolynomial σ R) = monomial 0 1 := rfl
/-
**MvPolynomial.single_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：single_eq_monomial (s : σ ->₀ Nat) (a : R) : .single s a = monomial s a
参数：s : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_monomial (s : σ →₀ ℕ) (a : R) : .single s a = monomial s a :=
  rfl
/-
**MvPolynomial.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mul_def : p * q = p.coeff.sum fun m a => q.coeff.sum fun n b => monomial (
m + n) (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.mul_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Add M] (x y : AddMonoidAlgebra R M),   x * y = x.coeff.sum fun m
₁ r₁ => y.coef…
-/
theorem mul_def : p * q = p.coeff.sum fun m a => q.coeff.sum fun n b => monomial (m + n) (a * b) :=
  AddMonoidAlgebra.mul_def ..

/-- `C a` is the constant polynomial with value `a` -/
/-
**MvPolynomial.C** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：C : R ->+* MvPolynomial σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C a` is the constant polynomial with value `a`
-/
def C : R →+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

@[simp, polynomial_post]
/-
**MvPolynomial.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：algebraMap_eq : algebraMap R (MvPolynomial σ R) = C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq : algebraMap R (MvPolynomial σ R) = C :=
  rfl

@[polynomial_pre]
/-
**MvPolynomial.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_eq_algebraMap : MvPolynomial.C = algebraMap R (MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_eq_algebraMap : MvPolynomial.C = algebraMap R (MvPolynomial σ R) :=
  rfl

variable {R σ}

@[simp]
/-
**MvPolynomial.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：algebraMap_apply [Algebra R S₁] (r : R) : algebraMap R (MvPolynomial σ S₁)
 r = C (algebraMap R S₁ r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply [Algebra R S₁] (r : R) :
    algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) :=
  rfl

/-- `X n` is the degree `1` monomial $X_n$. -/
/-
**MvPolynomial.X** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：X (n : σ) : MvPolynomial σ R
参数：n : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X n` is the degree `1` monomial $X_n$.
-/
def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1
/-
**MvPolynomial.monomial_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_left_injective {r : R} (hr : r != 0) : Function.Injective fun s :
 σ ->₀ Nat => monomial s r
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_left_injective`：∀ {R : Type u_1} {M : Type u_4} 
[inst : Semiring R] {r : R},   r ≠ 0 → Function.Injective fun m => AddMonoidAlge
bra.single m r
-/
theorem monomial_left_injective {r : R} (hr : r ≠ 0) :
    Function.Injective fun s : σ →₀ ℕ => monomial s r :=
  single_left_injective hr

@[simp]
/-
**MvPolynomial.monomial_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_left_inj {s t : σ ->₀ Nat} {r : R} (hr : r != 0) : monomial s r =
 monomial t r ↔ s = t
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_left_inj`：∀ {R : Type u_1} {M : Type u_4} [inst 
: Semiring R] {r : R} {m₁ m₂ : M},   r ≠ 0 → (AddMonoidAlgebra.single m₁ r = Add
MonoidAlgebra.single m…
-/
theorem monomial_left_inj {s t : σ →₀ ℕ} {r : R} (hr : r ≠ 0) :
    monomial s r = monomial t r ↔ s = t :=
  single_left_inj hr
/-
**MvPolynomial.C_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_apply : (C a : MvPolynomial σ R) = monomial 0 a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_apply : (C a : MvPolynomial σ R) = monomial 0 a :=
  rfl

@[simp]
/-
**MvPolynomial.C_0** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_0 : C 0 = (0 : MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem C_0 : C 0 = (0 : MvPolynomial σ R) := map_zero _

@[simp]
/-
**MvPolynomial.C_1** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_1 : C 1 = (1 : MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_1 : C 1 = (1 : MvPolynomial σ R) :=
  rfl
/-
**MvPolynomial.C_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mul_monomial : C a * monomial s a' = monomial s (a * a')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem C_mul_monomial : C a * monomial s a' = monomial s (a * a') := by
  have := single_mul_single 0 s a a'
  rw [zero_add] at this
  exact this

@[simp]
/-
**MvPolynomial.C_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_add : (C (a + a') : MvPolynomial σ R) = C a + C a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_add : (C (a + a') : MvPolynomial σ R) = C a + C a' := by simp

@[simp]
/-
**MvPolynomial.C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
-/
theorem C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a' :=
  C_mul_monomial.symm

@[simp]
/-
**MvPolynomial.C_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_pow (a : R) (n : Nat) : (C (a ^ n) : MvPolynomial σ R) = C a ^ n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem C_pow (a : R) (n : ℕ) : (C (a ^ n) : MvPolynomial σ R) = C a ^ n :=
  map_pow _ _ _

@[grind inj]
/-
**MvPolynomial.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_injective (σ : Type*) (R : Type*) [CommSemiring R] : Function.Injective 
(C : R -> MvPolynomial σ R)
参数：σ : Type*；R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_right_injective`：∀ {R : Type u_1} {M : Type u_4}
 [inst : Semiring R] {m : M}, Function.Injective (AddMonoidAlgebra.single m)
-/
theorem C_injective (σ : Type*) (R : Type*) [CommSemiring R] :
    Function.Injective (C : R → MvPolynomial σ R) :=
  single_right_injective

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.C_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] : Functi
on.Surjective (C : R -> MvPolynomial σ R)
参数：σ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] :
    Function.Surjective (C : R → MvPolynomial σ R) :=
  fun p ↦ ⟨p.coeff 0, by apply AddMonoidAlgebra.ext; ext; simp [C_apply, ← single_eq_monomial]⟩

@[simp]
/-
**MvPolynomial.C_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) : (C r : MvPolyno
mial σ R) = C s ↔ r = s
参数：R : Type*；r s : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
-/
theorem C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) :
    (C r : MvPolynomial σ R) = C s ↔ r = s :=
  (C_injective σ R).eq_iff
/-
**MvPolynomial.C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} {a : R} [inst : CommSemiring R], MvPolynomia
l.C a = 0 ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.C_inj`：C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s 
: R) : (C r : MvPolynomial σ R) = C s ↔ r = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma C_eq_zero : (C a : MvPolynomial σ R) = 0 ↔ a = 0 := by rw [← map_zero C, C_inj]
/-
**MvPolynomial.C_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：C_ne_zero : (C a : MvPolynomial σ R) != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `MvPolynomial.C_eq_zero`：∀ {R : Type u} {σ : Type u_1} {a : R} [inst : Co
mmSemiring R], MvPolynomial.C a = 0 ↔ a = 0
-/
lemma C_ne_zero : (C a : MvPolynomial σ R) ≠ 0 ↔ a ≠ 0 :=
  C_eq_zero.ne
/-
**MvPolynomial.nontrivial_of_nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`
。
形式化陈述：nontrivial_of_nontrivial (σ : Type*) (R : Type*) [CommSemiring R] [Nontriv
ial R] : Nontrivial (MvPolynomial σ R)
参数：σ : Type*；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nontrivial_of_nontrivial (σ : Type*) (R : Type*) [CommSemiring R] [Nontrivial R] :
    Nontrivial (MvPolynomial σ R) :=
  inferInstanceAs (Nontrivial <| AddMonoidAlgebra R (σ →₀ ℕ))
/-
**MvPolynomial.infinite_of_infinite** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：infinite_of_infinite (σ : Type*) (R : Type*) [CommSemiring R] [Infinite R]
 : Infinite (MvPolynomial σ R)
参数：σ : Type*；R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
-/
instance infinite_of_infinite (σ : Type*) (R : Type*) [CommSemiring R] [Infinite R] :
    Infinite (MvPolynomial σ R) :=
  Infinite.of_injective C (C_injective _ _)
/-
**MvPolynomial.infinite_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：infinite_of_nonempty (σ : Type*) (R : Type*) [Nonempty σ] [CommSemiring R]
 [Nontrivial R] : Infinite (MvPolynomial σ R)
参数：σ : Type*；R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MvPolynomial.monomial_left_injective`：monomial_left_injective {r : R} (h
r : r != 0) : Function.Injective fun s : σ ->₀ Nat => monomial s r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
instance infinite_of_nonempty (σ : Type*) (R : Type*) [Nonempty σ] [CommSemiring R]
    [Nontrivial R] : Infinite (MvPolynomial σ R) :=
  Infinite.of_injective ((fun s : σ →₀ ℕ => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
    <| (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) :=
  inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ..))
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero (MvPolynomial σ R) :=
  inferInstanceAs (IsCancelMulZero (AddMonoidAlgebra ..))

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multivariate polynomial ring over an integral domain is an integral domain.
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain (MvPolynomial σ R) where
/-
**MvPolynomial.C_eq_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_eq_coe_nat (n : Nat) : (C ↑n : MvPolynomial σ R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `MvPolynomial.C_add`：C_add : (C (a + a') : MvPolynomial σ R) = C a + C a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem C_eq_coe_nat (n : ℕ) : (C ↑n : MvPolynomial σ R) = n := by
  induction n <;> simp [*]
/-
**MvPolynomial.C_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mul' : MvPolynomial.C a * p = a • p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem C_mul' : MvPolynomial.C a * p = a • p :=
  (Algebra.smul_def a p).symm
/-
**MvPolynomial.smul_eq_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：smul_eq_C_mul (p : MvPolynomial σ R) (a : R) : a • p = C a * p
参数：p : MvPolynomial σ R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
-/
theorem smul_eq_C_mul (p : MvPolynomial σ R) (a : R) : a • p = C a * p :=
  C_mul'.symm
/-
**MvPolynomial.C_eq_smul_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_eq_smul_one : (C a : MvPolynomial σ R) = a • (1 : MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem C_eq_smul_one : (C a : MvPolynomial σ R) = a • (1 : MvPolynomial σ R) := by
  rw [← C_mul', mul_one]
/-
**MvPolynomial.smul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：smul_monomial {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁) : r • monomial s 
a = monomial s (r • a)
参数：r : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.smul_single`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {A : Type u_8} [inst_1 : SMulZeroClass A R] (a : A) (m : M) (r : R),  
 a • AddMonoidAlge…
-/
theorem smul_monomial {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁) :
    r • monomial s a = monomial s (r • a) := smul_single _ _ _
/-
**MvPolynomial.X_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_injective [Nontrivial R] : Function.Injective (X : σ -> MvPolynomial σ R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MvPolynomial.monomial_left_injective`：monomial_left_injective {r : R} (h
r : r != 0) : Function.Injective fun s : σ ->₀ Nat => monomial s r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Finsupp.single_left_injective`：single_left_injective (h : b != 0) : Func
tion.Injective fun a : α => single a b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem X_injective [Nontrivial R] : Function.Injective (X : σ → MvPolynomial σ R) :=
  (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]
/-
**MvPolynomial.X_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_inj [Nontrivial R] (m n : σ) : X m = (X n : MvPolynomial σ R) ↔ m = n
参数：m n : σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPolynomial.X_injective`：X_injective [Nontrivial R] : Function.Injectiv
e (X : σ -> MvPolynomial σ R)
-/
theorem X_inj [Nontrivial R] (m n : σ) : X m = (X n : MvPolynomial σ R) ↔ m = n :=
  X_injective.eq_iff
/-
**MvPolynomial.monomial_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_pow : monomial s a ^ e = monomial (e • s) (a ^ e)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_pow`：∀ {R : Type u_1} {M : Type u_4} [inst : Sem
iring R] [inst_1 : AddMonoid M] (m : M) (r : R) (n : ℕ),   AddMonoidAlgebra.sing
le m r ^ n = AddM…
-/
theorem monomial_pow : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow ..

@[simp]
/-
**MvPolynomial.monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : monomial s a * monomial s' b =
 monomial (s + s') (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
-/
theorem monomial_mul {s s' : σ →₀ ℕ} {a b : R} :
    monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single ..

variable (σ R)

/-- `fun s ↦ monomial s 1` as a homomorphism. -/
/-
**MvPolynomial.monomialOneHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：monomialOneHom : Multiplicative (σ ->₀ Nat) ->* MvPolynomial σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fun s ↦ monomial s 1` as a homomorphism.
-/
def monomialOneHom : Multiplicative (σ →₀ ℕ) →* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _

variable {σ R}

@[simp]
/-
**MvPolynomial.monomialOneHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomialOneHom_apply : monomialOneHom R σ s = (monomial s 1 : MvPolynomial
 σ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomialOneHom_apply : monomialOneHom R σ s = (monomial s 1 : MvPolynomial σ R) :=
  rfl
/-
**MvPolynomial.X_pow_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_pow_eq_monomial : X n ^ e = monomial (Finsupp.single n e) (1 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_pow`：monomial_pow : monomial s a ^ e = monomial (e
 • s) (a ^ e)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem X_pow_eq_monomial : X n ^ e = monomial (Finsupp.single n e) (1 : R) := by
  simp [X, monomial_pow]
/-
**MvPolynomial.monomial_add_single** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_add_single : monomial (s + Finsupp.single n e) a = monomial s a *
 X n ^ e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem monomial_add_single : monomial (s + Finsupp.single n e) a = monomial s a * X n ^ e := by
  rw [X_pow_eq_monomial, monomial_mul, mul_one]
/-
**MvPolynomial.monomial_single_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_single_add : monomial (Finsupp.single n e + s) a = X n ^ e * mono
mial s a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem monomial_single_add : monomial (Finsupp.single n e + s) a = X n ^ e * monomial s a := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]
/-
**MvPolynomial.C_mul_X_pow_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mul_X_pow_eq_monomial {s : σ} {a : R} {n : Nat} : C a * X s ^ n = monomi
al (Finsupp.single s n) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPolynomial.monomial_add_single`：monomial_add_single : monomial (s + Fi
nsupp.single n e) a = monomial s a * X n ^ e
· 使用定理 `MvPolynomial.C_apply`：C_apply : (C a : MvPolynomial σ R) = monomial 0 a
-/
theorem C_mul_X_pow_eq_monomial {s : σ} {a : R} {n : ℕ} :
    C a * X s ^ n = monomial (Finsupp.single s n) a := by
  rw [← zero_add (Finsupp.single s n), monomial_add_single, C_apply]
/-
**MvPolynomial.C_mul_X_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mul_X_eq_monomial {s : σ} {a : R} : C a * X s = monomial (Finsupp.single
 s 1) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul_X_pow_eq_monomial`：C_mul_X_pow_eq_monomial {s : σ} {a
 : R} {n : Nat} : C a * X s ^ n = monomial (Finsupp.single s n) a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem C_mul_X_eq_monomial {s : σ} {a : R} : C a * X s = monomial (Finsupp.single s 1) a := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp]
/-
**MvPolynomial.monomial_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_zero {s : σ ->₀ Nat} : monomial s (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_zero`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] (m : M), AddMonoidAlgebra.single m 0 = 0
-/
theorem monomial_zero {s : σ →₀ ℕ} : monomial s (0 : R) = 0 := single_zero _

@[simp]
/-
**MvPolynomial.monomial_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_zero' : (monomial (0 : σ ->₀ Nat) : R -> MvPolynomial σ R) = C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero' : (monomial (0 : σ →₀ ℕ) : R → MvPolynomial σ R) = C :=
  rfl

@[simp]
/-
**MvPolynomial.monomial_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_eq_zero {s : σ ->₀ Nat} {b : R} : monomial s b = 0 ↔ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_eq_zero`：∀ {R : Type u_1} {M : Type u_4} [inst :
 Semiring R] {r : R} {m : M}, AddMonoidAlgebra.single m r = 0 ↔ r = 0
-/
theorem monomial_eq_zero {s : σ →₀ ℕ} {b : R} : monomial s b = 0 ↔ b = 0 := single_eq_zero

@[simp]
/-
**MvPolynomial.sum_monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sum_monomial_eq {A : Type*} [AddCommMonoid A] {u : σ ->₀ Nat} {r : R} {b :
 (σ ->₀ Nat) -> R -> A} (w : b u 0 = 0) : sum (monomial u r).coeff b = b u r
参数：σ ->₀ Nat；w : b u 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A}
    (w : b u 0 = 0) : sum (monomial u r).coeff b = b u r :=
  Finsupp.sum_single_index w

@[simp]
/-
**MvPolynomial.sum_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sum_C {A : Type*} [AddCommMonoid A] {b : (σ ->₀ Nat) -> R -> A} (w : b 0 0
 = 0) : sum (C a).coeff b = b 0 a
参数：σ ->₀ Nat；w : b 0 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.sum_monomial_eq`：sum_monomial_eq {A : Type*} [AddCommMonoid
 A] {u : σ ->₀ Nat} {r : R} {b : (σ ->₀ Nat) -> R -> A} (w : b u 0 = 0) : sum (m
onomial u r).coeff…
-/
theorem sum_C {A : Type*} [AddCommMonoid A] {b : (σ →₀ ℕ) → R → A} (w : b 0 0 = 0) :
    sum (C a).coeff b = b 0 a :=
  sum_monomial_eq w
/-
**MvPolynomial.monomial_sum_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_sum_one {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) : (monomi
al (∑ i in s, f i) 1 : MvPolynomial σ R) = ∏ i in s, monomial (f i) 1
参数：s : Finset α；f : α -> σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem monomial_sum_one {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) :
    (monomial (∑ i ∈ s, f i) 1 : MvPolynomial σ R) = ∏ i ∈ s, monomial (f i) 1 :=
  map_prod (monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.monomial_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_sum_index {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (a : R)
 : monomial (∑ i in s, f i) a = C a * ∏ i in s, monomial (f i) 1
参数：s : Finset α；f : α -> σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.monomial_sum_one`：monomial_sum_one {α : Type*} (s : Finset 
α) (f : α -> σ ->₀ Nat) : (monomial (∑ i in s, f i) 1 : MvPolynomial σ R) = ∏ i 
in s, monomial (f i…
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem monomial_sum_index {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) (a : R) :
    monomial (∑ i ∈ s, f i) a = C a * ∏ i ∈ s, monomial (f i) 1 := by
  rw [← monomial_sum_one, C_mul', ← (monomial _).map_smul, smul_eq_mul, mul_one]
/-
**MvPolynomial.monomial_sum_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_sum_prod {α : Type*} (s : Finset α) (f : α -> σ ->₀ Nat) (g : α -
> R) : monomial (∑ i in s, f i) (∏ i in s, g i) = ∏ i in s, monomial (f i) (g i)
参数：s : Finset α；f : α -> σ ->₀ Nat；g : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_sum_index`：monomial_sum_index {α : Type*} (s : Fin
set α) (f : α -> σ ->₀ Nat) (a : R) : monomial (∑ i in s, f i) a = C a * ∏ i in 
s, monomial (f i) 1
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_sum_prod {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) (g : α → R) :
    monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) = ∏ i ∈ s, monomial (f i) (g i) := by
  simp_rw [monomial_sum_index, map_prod, ← Finset.prod_mul_distrib, C_mul_monomial, mul_one]
/-
**MvPolynomial.monomial_finsupp_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：monomial_finsupp_sum_index {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> 
β -> σ ->₀ Nat) (a : R) : monomial (f.sum g) a = C a * f.prod fun a b => monomia
l (g a b) 1
参数：f : α ->₀ β；g : α -> β -> σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_sum_index`：monomial_sum_index {α : Type*} (s : Fin
set α) (f : α -> σ ->₀ Nat) (a : R) : monomial (∑ i in s, f i) a = C a * ∏ i in 
s, monomial (f i) 1
-/
theorem monomial_finsupp_sum_index {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → σ →₀ ℕ)
    (a : R) : monomial (f.sum g) a = C a * f.prod fun a b => monomial (g a b) 1 :=
  monomial_sum_index _ _ _
/-
**MvPolynomial.monomial_eq_monomial_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：monomial_eq_monomial_iff {α : Type*} (a₁ a₂ : α ->₀ Nat) (b₁ b₂ : R) : mon
omial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
参数：a₁ a₂ : α ->₀ Nat；b₁ b₂ : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_inj`：∀ {R : Type u_1} {M : Type u_4} [inst : Sem
iring R] {r₁ r₂ : R} {m₁ m₂ : M},   AddMonoidAlgebra.single m₁ r₁ = AddMonoidAlg
ebra.single m₂ r₂…
-/
theorem monomial_eq_monomial_iff {α : Type*} (a₁ a₂ : α →₀ ℕ) (b₁ b₂ : R) :
    monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := single_inj
/-
**MvPolynomial.monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_eq : monomial s a = C a * (s.prod fun n e => X n ^ e : MvPolynomi
al σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_eq : monomial s a = C a * (s.prod fun n e => X n ^ e : MvPolynomial σ R) := by
  simp only [X_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]

@[simp]
/-
**MvPolynomial.prod_X_pow_eq_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：prod_X_pow_eq_monomial : ∏ x in s.support, X x ^ s x = monomial s (1 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_X_pow_eq_monomial : ∏ x ∈ s.support, X x ^ s x = monomial s (1 : R) := by
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod]
/-
**MvPolynomial.prod_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：prod_X_pow (x : σ -> Nat) (t : Finset σ) : ∏ y in t, (X y : MvPolynomial σ
 R) ^ x y = monomial (indicator t (fun i _ => x i)) (1 : R)
参数：x : σ -> Nat；t : Finset σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `MvPolynomial.C_1`：C_1 : C 1 = (1 : MvPolynomial σ R)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finsupp.support_indicator_subset`：support_indicator_subset : (indicator 
s f).support subseteq s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_X_pow (x : σ → ℕ) (t : Finset σ) :
    ∏ y ∈ t, (X y : MvPolynomial σ R) ^ x y = monomial (indicator t (fun i _ ↦ x i)) (1 : R) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, Finset.prod_subset (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi ↦ by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff, ne_eq, not_not] at hi'
    rw [hi', pow_zero]

@[elab_as_elim]
/-
**MvPolynomial.induction_on_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：induction_on_monomial {motive : MvPolynomial σ R -> Prop} (C : forall a, m
otive (C a)) (mul_X : forall p n, motive p -> motive (p * X n)) : forall s a, mo
tive (monomial s a)
参数：C : forall a, motive (C a)；mul_X : forall p n, motive p -> motive (p * X n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPolynomial.monomial_add_single`：monomial_add_single : monomial (s + Fi
nsupp.single n e) a = monomial s a * X n ^ e
-/
theorem induction_on_monomial {motive : MvPolynomial σ R → Prop}
    (C : ∀ a, motive (C a))
    (mul_X : ∀ p n, motive p → motive (p * X n)) : ∀ s a, motive (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℕ _ _ s
  · change motive (monomial 0 a)
    exact C a
  · intro n e p _hpn _he ih
    have : ∀ e : ℕ, motive (monomial p a * X n ^ e) := by
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
/-
**MvPolynomial.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：induction_on' {P : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R) (monom
ial : forall (u : σ ->₀ Nat) (a : R), P (monomial u a)) (add : forall p q : MvPo
lynomial σ R, P p -> P q -> P (p + q)) : P p
参数：p : MvPolynomial σ R；monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial u
 a)；add : forall p q : MvPolynomial σ R, P p -> P q -> P (p + q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.induction`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] {motive : AddMonoidAlgebra R M → Prop} (x : AddMonoidAlgebra R M),   mot
ive 0 →     (∀ (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0

--- 原说明 ---
Analog of `Polynomial.induction_on'`.
To prove something about `MVPolynomials`,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
theorem induction_on' {P : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (monomial : ∀ (u : σ →₀ ℕ) (a : R), P (monomial u a))
    (add : ∀ p q : MvPolynomial σ R, P p → P q → P (p + q)) : P p :=
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
/-
**MvPolynomial.monomial_add_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：monomial_add_induction_on {motive : MvPolynomial σ R -> Prop} (p : MvPolyn
omial σ R) (C : forall a, motive (C a)) (monomial_add : forall (a : σ ->₀ Nat) (
b : R) (f : MvPolynomial σ R), a ∉ f.coeff.support -> b != 0 -> motive f -> moti
ve (monomial a b + f)) : motive p
参数：p : MvPolynomial σ R；C : forall a, motive (C a)；monomial_add : forall (a : σ 
->₀ Nat) (b : R) (f : MvPolynomial σ R), a ∉ f.coeff.support -> b != 0 -> motive
 f -> motive (monomial a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.induction`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] {motive : AddMonoidAlgebra R M → Prop} (x : AddMonoidAlgebra R M),   mot
ive 0 →     (∀ (…
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)

--- 原说明 ---
Similar to `MvPolynomial.induction_on` but only a weak form of `h_add` is requir
ed.
In particular, this version only requires us to show
that `motive` is closed under addition of nontrivial monomials not present in th
e support.
-/
theorem monomial_add_induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.coeff.support → b ≠ 0 → motive f → motive (monomial a b + f)) :
    motive p :=
  induction p (C_0.rec <| C 0) monomial_add

/--
Similar to `MvPolynomial.induction_on` but only a yet weaker form of `h_add` is required.
In particular, this version only requires us to show
that `motive` is closed under addition of monomials not present in the support
for which `motive` is already known to hold.
-/
/-
**MvPolynomial.induction_on''** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：induction_on'' {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R) 
(C : forall a, motive (C a)) (monomial_add : forall (a : σ ->₀ Nat) (b : R) (f :
 MvPolynomial σ R), a ∉ f.coeff.support -> b != 0 -> motive f -> motive (monomia
l a b) -> motive ((monomial a b) + f)) (mul_X : forall (p : MvPolynomial σ R) (n
 : σ), motive p -> motive (p * MvPolynomial.X n)) : motive p
参数：p : MvPolynomial σ R；C : forall a, motive (C a)；monomial_add : forall (a : σ 
->₀ Nat) (b : R) (f : MvPolynomial σ R), a ∉ f.coeff.support -> b != 0 -> motive
 f -> motive (monomial a b) -> motive ((monomial a b) + f)；mul_X : forall (p : M
vPolynomial σ R) (n : σ), motive p -> motive (p * MvPolynomial.X n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_add_induction_on`：monomial_add_induction_on {motiv
e : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R) (C : forall a, motive (C a)
) (monomial_add : forall (a …
· 使用定理 `MvPolynomial.induction_on_monomial`：induction_on_monomial {motive : MvPo
lynomial σ R -> Prop} (C : forall a, motive (C a)) (mul_X : forall p n, motive p
 -> motive (p * X n)) : …

--- 原说明 ---
Similar to `MvPolynomial.induction_on` but only a yet weaker form of `h_add` is 
required.
In particular, this version only requires us to show
that `motive` is closed under addition of monomials not present in the support
for which `motive` is already known to hold.
-/
theorem induction_on'' {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.coeff.support → b ≠ 0 → motive f → motive (monomial a b) →
          motive ((monomial a b) + f))
    (mul_X : ∀ (p : MvPolynomial σ R) (n : σ), motive p → motive (p * MvPolynomial.X n)) :
    motive p :=
  monomial_add_induction_on p C fun a b f ha hb hf =>
    monomial_add a b f ha hb hf <| induction_on_monomial C mul_X a b

/--
Analog of `Polynomial.induction_on`.
If a property holds for any constant polynomial
and is preserved under addition and multiplication by variables
then it holds for all multivariate polynomials.
-/
@[recursor 5]
/-
**MvPolynomial.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：induction_on {motive : MvPolynomial σ R -> Prop} (p : MvPolynomial σ R) (C
 : forall a, motive (C a)) (add : forall p q, motive p -> motive q -> motive (p 
+ q)) (mul_X : forall p n, motive p -> motive (p * X n)) : motive p
参数：p : MvPolynomial σ R；C : forall a, motive (C a)；add : forall p q, motive p ->
 motive q -> motive (p + q)；mul_X : forall p n, motive p -> motive (p * X n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on''`：induction_on'' {motive : MvPolynomial σ R -
> Prop} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (monomial_add : fora
ll (a : σ ->₀ Nat…

--- 原说明 ---
Analog of `Polynomial.induction_on`.
If a property holds for any constant polynomial
and is preserved under addition and multiplication by variables
then it holds for all multivariate polynomials.
-/
theorem induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (mul_X : ∀ p n, motive p → motive (p * X n)) : motive p :=
  induction_on'' p C (fun a b f _ha _hb hf hm => add (monomial a b) f hm hf) mul_X
/-
**MvPolynomial.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ringHom_ext {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A} (hC :
 forall r, f (C r) = g (C r)) (hX : forall i, f (X i) = g (X i)) : f = g
参数：hC : forall r, f (C r) = g (C r)；hX : forall i, f (X i) = g (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] [AddMonoid M] {
f g : R[M] ->+* S} (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom) (h
_of : (f : R[M] ->*…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Finsupp.mulHom_ext'`：mulHom_ext' [MulOneClass N] {f g : Multiplicative (
α ->₀ M) ->* N} (H : forall x, f.comp (AddMonoidHom.toMultiplicative (singleAddH
om x)) = …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `MonoidHom.ext_mnat`：MonoidHom.ext_mnat ⦃f g : Multiplicative Nat ->* M⦄ 
(h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g
-/
theorem ringHom_ext {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : ∀ r, f (C r) = g (C r)) (hX : ∀ i, f (X i) = g (X i)) : f = g := by
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
/-
**MvPolynomial.ringHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ringHom_ext' {A : Type*} [Semiring A] {f g : MvPolynomial σ R ->+* A} (hC 
: f.comp C = g.comp C) (hX : forall i, f (X i) = g (X i)) : f = g
参数：hC : f.comp C = g.comp C；hX : forall i, f (X i) = g (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext`：ringHom_ext {A : Type*} [Semiring A] {f g : Mv
Polynomial σ R ->+* A} (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i
) = g (X i)) :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2

--- 原说明 ---
See note [partially-applied ext lemmas].

We set the priority higher than that of `AddMonoidAlgebra.ringHom_ext'`.
-/
theorem ringHom_ext' {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : f.comp C = g.comp C) (hX : ∀ i, f (X i) = g (X i)) : f = g :=
  ringHom_ext (RingHom.ext_iff.1 hC) hX
/-
**MvPolynomial.hom_eq_hom** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ R ->+* S₂) (hC : f.comp C =
 g.comp C) (hX : forall n : σ, f (X n) = g (X n)) (p : MvPolynomial σ R) : f p =
 g p
参数：f g : MvPolynomial σ R ->+* S₂；hC : f.comp C = g.comp C；hX : forall n : σ, f 
(X n) = g (X n)；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
-/
theorem hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ R →+* S₂) (hC : f.comp C = g.comp C)
    (hX : ∀ n : σ, f (X n) = g (X n)) (p : MvPolynomial σ R) : f p = g p :=
  RingHom.congr_fun (ringHom_ext' hC hX) p
/-
**MvPolynomial.is_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：is_id (f : MvPolynomial σ R ->+* MvPolynomial σ R) (hC : f.comp C = C) (hX
 : forall n : σ, f (X n) = X n) (p : MvPolynomial σ R) : f p = p
参数：f : MvPolynomial σ R ->+* MvPolynomial σ R；hC : f.comp C = C；hX : forall n : 
σ, f (X n) = X n；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.hom_eq_hom`：hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ 
R ->+* S₂) (hC : f.comp C = g.comp C) (hX : forall n : σ, f (X n) = g (X n)) (p 
: MvPolynomia…
-/
theorem is_id (f : MvPolynomial σ R →+* MvPolynomial σ R) (hC : f.comp C = C)
    (hX : ∀ n : σ, f (X n) = X n) (p : MvPolynomial σ R) : f p = p :=
  hom_eq_hom f (RingHom.id _) hC hX p

/-- See note [partially-applied ext lemmas].

We set the priority higher than that of `AddMonoidAlgebra.algHom_ext`. -/
@[ext high + 1]
/-
**MvPolynomial.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：algHom_ext' {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] 
[Algebra R B] {f g : MvPolynomial σ A ->ₐ[R] B} (h₁ : f.comp (IsScalarTower.toAl
gHom R A (MvPolynomial σ A)) = g.comp (IsScalarTower.toAlgHom R A (MvPolynomial 
σ A))) (h₂ : forall i, f (X i) = g (X i)) : f = g
参数：h₁ : f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) = g.comp (IsScala
rTower.toAlgHom R A (MvPolynomial σ A))；h₂ : forall i, f (X i) = g (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
See note [partially-applied ext lemmas].

We set the priority higher than that of `AddMonoidAlgebra.algHom_ext`.
-/
theorem algHom_ext' {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    {f g : MvPolynomial σ A →ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) =
        g.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (h₂ : ∀ i, f (X i) = g (X i)) : f = g :=
  AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

/-- See note [partially-applied ext lemmas].

We set the priority higher than that of `MvPolynomial.algHom_ext'`. -/
@[ext high + 2]
/-
**MvPolynomial.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R 
->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f = g
参数：hf : forall i : σ, f (X i) = g (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddMonoidAlgebra.algHom_ext'`：algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (singl
e_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
 (single_one_left …
· 使用定理 `Finsupp.mulHom_ext'`：mulHom_ext' [MulOneClass N] {f g : Multiplicative (
α ->₀ M) ->* N} (H : forall x, f.comp (AddMonoidHom.toMultiplicative (singleAddH
om x)) = …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MonoidHom.ext_mnat`：MonoidHom.ext_mnat ⦃f g : Multiplicative Nat ->* M⦄ 
(h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g

--- 原说明 ---
See note [partially-applied ext lemmas].

We set the priority higher than that of `MvPolynomial.algHom_ext'`.
-/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R →ₐ[R] A}
    (hf : ∀ i : σ, f (X i) = g (X i)) : f = g :=
  AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun X : σ => MonoidHom.ext_mnat (hf X)) (by ext)

@[simp]
/-
**MvPolynomial.algHom_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：algHom_C {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R ->ₐ[
R] A) (r : R) : f (C r) = algebraMap R A r
参数：f : MvPolynomial σ R ->ₐ[R] A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem algHom_C {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R →ₐ[R] A) (r : R) :
    f (C r) = algebraMap R A r :=
  f.commutes r

@[simp]
/-
**MvPolynomial.adjoin_range_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：adjoin_range_X : Algebra.adjoin R (range (X : σ -> MvPolynomial σ R)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem adjoin_range_X : Algebra.adjoin R (range (X : σ → MvPolynomial σ R)) = ⊤ := by
  set S := Algebra.adjoin R (range (X : σ → MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin <| mem_range_self _)

@[ext]
/-
**MvPolynomial.linearMap_ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomi
al σ R ->ₗ[R] M} (h : forall s, f ∘ₗ monomial s = g ∘ₗ monomial s) : f = g
参数：h : forall s, f ∘ₗ monomial s = g ∘ₗ monomial s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.lhom_ext'`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} [inst : Semiring S] {N : Type u_7} [inst_1 : Semiring R]   [inst_2 : AddCommM
onoid N] [inst_3…
-/
theorem linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomial σ R →ₗ[R] M}
    (h : ∀ s, f ∘ₗ monomial s = g ∘ₗ monomial s) : f = g :=
  lhom_ext' h

section Support

/-- The finite set of all `m : σ →₀ ℕ` such that `X^m` has a non-zero coefficient. -/
/-
**MvPolynomial.support** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：support (p : MvPolynomial σ R) : Finset (σ ->₀ Nat)
参数：p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite set of all `m : σ →₀ ℕ` such that `X^m` has a non-zero coefficient.
-/
def support (p : MvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  p.coeff.support
/-
**MvPolynomial.finsupp_support_eq_support** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：finsupp_support_eq_support (p : MvPolynomial σ R) : p.coeff.support = p.su
pport
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsupp_support_eq_support (p : MvPolynomial σ R) : p.coeff.support = p.support :=
  rfl
/-
**MvPolynomial.support_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_monomial [h : Decidable (a = 0)] : (monomial s a).support = if a =
 0 then ∅ else {s}
参数：a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem support_monomial [h : Decidable (a = 0)] :
    (monomial s a).support = if a = 0 then ∅ else {s} := by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl
/-
**MvPolynomial.support_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_C (c : R) [h : Decidable (c = 0)] : (C (σ
参数：c : R；c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
-/
lemma support_C (c : R) [h : Decidable (c = 0)] :
    (C (σ := σ) c).support = if c = 0 then ∅ else {0} :=
  support_monomial
/-
**MvPolynomial.support_monomial_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_monomial_subset : (monomial s a).support subseteq {s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
theorem support_monomial_subset : (monomial s a).support ⊆ {s} :=
  support_single_subset
/-
**MvPolynomial.support_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_add [DecidableEq σ] : (p + q).support subseteq p.support union q.s
upport
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
-/
theorem support_add [DecidableEq σ] : (p + q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_add
/-
**MvPolynomial.support_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_X [Nontrivial R] : (X n : MvPolynomial σ R).support = {Finsupp.sin
gle n 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring 
R] (n : σ),   MvPolynomial.X n = (MvPolynomial.monomial fun₀ | n => 1) 1
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem support_X [Nontrivial R] : (X n : MvPolynomial σ R).support = {Finsupp.single n 1} := by
  classical rw [X, support_monomial, if_neg]; exact one_ne_zero
/-
**MvPolynomial.support_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_X_pow [Nontrivial R] (s : σ) (n : Nat) : (X s ^ n : MvPolynomial σ
 R).support = {Finsupp.single s n}
参数：s : σ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
-/
theorem support_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (X s ^ n : MvPolynomial σ R).support = {Finsupp.single s n} := by
  classical
    rw [X_pow_eq_monomial, support_monomial, if_neg (one_ne_zero' R)]

@[simp]
/-
**MvPolynomial.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_zero : (0 : MvPolynomial σ R).support = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zero : (0 : MvPolynomial σ R).support = ∅ :=
  rfl

@[simp]
/-
**MvPolynomial.support_one** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_one [Nontrivial R] : (1 : MvPolynomial σ R).support = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_one [Nontrivial R] : (1 : MvPolynomial σ R).support = {0} := by
  classical
  simp [show support (1 : MvPolynomial σ R) = if (1 : R) = 0 then ∅ else {0} from rfl]
/-
**MvPolynomial.support_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_smul {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial 
σ R} : (a • f).support subseteq f.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_smul`：support_smul [Zero M] [SMulZeroClass R M] {b : R} 
{g : α ->₀ M} : (b • g).support subseteq g.support
-/
theorem support_smul {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial σ R} :
    (a • f).support ⊆ f.support :=
  Finsupp.support_smul
/-
**MvPolynomial.support_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_sum {α : Type*} [DecidableEq σ] {s : Finset α} {f : α -> MvPolynom
ial σ R} : (∑ x in s, f x).support subseteq s.biUnion fun x => (f x).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_sum`：∀ {R : Type u_1} {M : Type u_4} {ι : Type u_
7} [inst : Semiring R] (s : Finset ι) (f : ι → AddMonoidAlgebra R M),   (∑ i ∈ s
, f i).coeff = ∑…
· 使用定理 `Finsupp.support_finsetSum`：support_finsetSum [DecidableEq β] [AddCommMon
oid M] {s : Finset α} {f : α -> β ->₀ M} : (Finset.sum s f).support subseteq s.b
iUnion fun x =>…
-/
theorem support_sum {α : Type*} [DecidableEq σ] {s : Finset α} {f : α → MvPolynomial σ R} :
    (∑ x ∈ s, f x).support ⊆ s.biUnion fun x => (f x).support := by
  simpa [support, coeff, MvPolynomial] using Finsupp.support_finsetSum

end Support

section Coeff

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
/-
**MvPolynomial.coeff** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：coeff (m : σ ->₀ Nat) (p : MvPolynomial σ R) : R
参数：m : σ ->₀ Nat；p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficient of the monomial `m` in the multi-variable polynomial `p`.
-/
def coeff (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  @DFunLike.coe ((σ →₀ ℕ) →₀ R) _ _ _ (AddMonoidAlgebra.coeff p) m

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/-
**MvPolynomial.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_support_iff {p : MvPolynomial σ R} {m : σ ->₀ Nat} : m in p.support ↔ 
p.coeff m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∈ p.support ↔ p.coeff m ≠ 0 := by
  simp [support, coeff]
/-
**MvPolynomial.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：notMem_support_iff {p : MvPolynomial σ R} {m : σ ->₀ Nat} : m ∉ p.support 
↔ p.coeff m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∉ p.support ↔ p.coeff m = 0 := by
  simp
/-
**MvPolynomial.sum_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ ->₀ Nat) -> R
 -> A} : (AddMonoidAlgebra.coeff p).sum b = ∑ m in p.support, b m (p.coeff m)
参数：σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ →₀ ℕ) → R → A} :
    (AddMonoidAlgebra.coeff p).sum b = ∑ m ∈ p.support, b m (p.coeff m) := by
  simp [support, Finsupp.sum, coeff]
/-
**MvPolynomial.support_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_mul [DecidableEq σ] (p q : MvPolynomial σ R) : (p * q).support sub
seteq p.support + q.support
参数：p q : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.support_coeff_mul_subset`：∀ {k : Type u₁} {G : Type u₂}
 [inst : Semiring k] [inst_1 : Add G] [inst_2 : DecidableEq G]   (x y : AddMonoi
dAlgebra k G), (x * y).coeff.su…
-/
theorem support_mul [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p * q).support ⊆ p.support + q.support :=
  AddMonoidAlgebra.support_coeff_mul_subset p q
/-
**MvPolynomial.disjoint_support_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：disjoint_support_monomial {a : σ ->₀ Nat} {p : MvPolynomial σ R} {s : R} (
ha : a ∉ p.support) (hs : s != 0) : Disjoint (monomial a s).support p.support
参数：ha : a ∉ p.support；hs : s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
-/
lemma disjoint_support_monomial {a : σ →₀ ℕ} {p : MvPolynomial σ R} {s : R}
    (ha : a ∉ p.support) (hs : s ≠ 0) : Disjoint (monomial a s).support p.support := by
  classical
  simpa [support_monomial, hs] using notMem_support_iff.mp ha

@[ext]
/-
**MvPolynomial.ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = coeff m q) -> p = q
参数：p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem ext (p q : MvPolynomial σ R) : (∀ m, coeff m p = coeff m q) → p = q :=
  fun h ↦ AddMonoidAlgebra.ext <| by ext; exact h _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MvPolynomial.coeff_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ R) : coeff m (p + q) = coe
ff m p + coeff m q
参数：m : σ ->₀ Nat；p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_add (m : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    coeff m (p + q) = coeff m p + coeff m q := by simp [coeff, MvPolynomial]

@[simp]
/-
**MvPolynomial.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ ->₀ Nat) (C : S₁) (p :
 MvPolynomial σ R) : coeff m (C • p) = C • coeff m p
参数：m : σ ->₀ Nat；C : S₁；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_smul_apply`：∀ {R : Type u_1} {M : Type u_4} [inst
 : Semiring R] {A : Type u_8} [inst_1 : SMulZeroClass A R] (a : A)   (x : AddMon
oidAlgebra R M) (m : M)…
-/
theorem coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ →₀ ℕ) (C : S₁) (p : MvPolynomial σ R) :
    coeff m (C • p) = C • coeff m p :=
  AddMonoidAlgebra.coeff_smul_apply ..

@[simp]
/-
**MvPolynomial.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPolynomial σ R) = 0
参数：m : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero (m : σ →₀ ℕ) : coeff m (0 : MvPolynomial σ R) = 0 :=
  rfl

@[simp]
/-
**MvPolynomial.coeff_zero_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_zero_X (i : σ) : coeff 0 (X i : MvPolynomial σ R) = 0
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem coeff_zero_X (i : σ) : coeff 0 (X i : MvPolynomial σ R) = 0 :=
  single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

-- TODO: Remove once its use in the Witt vector API has been removed.
@[simp]
/-
**MvPolynomial.coeff_addMonoidAlgebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：coeff_addMonoidAlgebraMap (g : S₁ ->+ R) (φ : MvPolynomial σ S₁) (m) : coe
ff m (φ.map g) = g (coeff m φ)
参数：g : S₁ ->+ R；φ : MvPolynomial σ S₁；m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_addMonoidAlgebraMap (g : S₁ →+ R) (φ : MvPolynomial σ S₁) (m) :
    coeff m (φ.map g) = g (coeff m φ) := rfl

@[deprecated (since := "2026-03-27")] alias coeff_mapRange := coeff_addMonoidAlgebraMap

/-- `MvPolynomial.coeff m` but promoted to an `AddMonoidHom`. -/
@[simps]
/-
**MvPolynomial.coeffAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：coeffAddMonoidHom (m : σ ->₀ Nat) : MvPolynomial σ R ->+ R where toFun
参数：m : σ ->₀ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_zero`：coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPol
ynomial σ R) = 0
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q

--- 原说明 ---
`MvPolynomial.coeff m` but promoted to an `AddMonoidHom`.
-/
def coeffAddMonoidHom (m : σ →₀ ℕ) : MvPolynomial σ R →+ R where
  toFun := coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m

variable (R) in
/-- `MvPolynomial.coeff m` but promoted to a `LinearMap`. -/
@[simps]
/-
**MvPolynomial.lcoeff** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：lcoeff (m : σ ->₀ Nat) : MvPolynomial σ R ->ₗ[R] R where toFun
参数：m : σ ->₀ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q

--- 原说明 ---
`MvPolynomial.coeff m` but promoted to a `LinearMap`.
-/
def lcoeff (m : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] R where
  toFun := coeff m
  map_add' := coeff_add m
  map_smul' := coeff_smul m
/-
**MvPolynomial.coeff_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_sum {X : Type*} (s : Finset X) (f : X -> MvPolynomial σ R) (m : σ ->
₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (f x)
参数：s : Finset X；f : X -> MvPolynomial σ R；m : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coeff_sum {X : Type*} (s : Finset X) (f : X → MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, coeff m (f x) :=
  map_sum (@coeffAddMonoidHom R σ _ _) _ s
/-
**MvPolynomial.monic_monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monic_monomial_eq (m) : monomial m (1 : R) = (m.prod fun n e => X n ^ e : 
MvPolynomial σ R)
参数：m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monic_monomial_eq (m) :
    monomial m (1 : R) = (m.prod fun n e => X n ^ e : MvPolynomial σ R) := by simp [monomial_eq]

@[simp]
/-
**MvPolynomial.coeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_monomial [DecidableEq σ] (m n) (a) : coeff m (monomial n a : MvPolyn
omial σ R) = if n = m then a else 0
参数：m n；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
theorem coeff_monomial [DecidableEq σ] (m n) (a) :
    coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0 :=
  Finsupp.single_apply

/-- A polynomial all of whose support degrees equal a fixed `d₀` is the single monomial
`monomial d₀ (coeff d₀ φ)`. -/
/-
**MvPolynomial.eq_monomial_of_support_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `MvPolynomial`。
形式化陈述：eq_monomial_of_support_subset_singleton {φ : MvPolynomial σ R} {d₀ : σ ->₀
 Nat} (h : forall d in φ.support, d = d₀) : φ = monomial d₀ (coeff d₀ φ)
参数：h : forall d in φ.support, d = d₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A polynomial all of whose support degrees equal a fixed `d₀` is the single monom
ial
`monomial d₀ (coeff d₀ φ)`.
-/
theorem eq_monomial_of_support_subset_singleton {φ : MvPolynomial σ R} {d₀ : σ →₀ ℕ}
    (h : ∀ d ∈ φ.support, d = d₀) : φ = monomial d₀ (coeff d₀ φ) := by
  classical
  ext d
  rcases eq_or_ne d d₀ with rfl | hd
  · rw [coeff_monomial, if_pos rfl]
  · rw [notMem_support_iff.mp fun hmem ↦ hd (h d hmem), coeff_monomial, if_neg fun e ↦ hd e.symm]

@[simp]
/-
**MvPolynomial.coeff_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : MvPolynomial σ R) = if 0 
= m then a else 0
参数：m；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
theorem coeff_C [DecidableEq σ] (m) (a) :
    coeff m (C a : MvPolynomial σ R) = if 0 = m then a else 0 :=
  Finsupp.single_apply
/-
**MvPolynomial.coeff_C_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_C_of_ne_zero {m : σ ->₀ Nat} (h : m != 0) (a : R) : coeff m (C a) = 
0
参数：h : m != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem coeff_C_of_ne_zero {m : σ →₀ ℕ} (h : m ≠ 0) (a : R) : coeff m (C a) = 0 := by
  classical rw [coeff_C, if_neg h.symm]

-- The intended use case of this theorem is for `n = 1` (often useful for `pderiv`).
@[simp]
/-
**MvPolynomial.coeff_add_single_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_add_single_C {n : Nat} [NeZero n] {m : σ ->₀ Nat} (a : R) (i : σ) : 
coeff (m + Finsupp.single i n) (C a) = 0
参数：a : R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_C_of_ne_zero`：coeff_C_of_ne_zero {m : σ ->₀ Nat} (h :
 m != 0) (a : R) : coeff m (C a) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem coeff_add_single_C {n : ℕ} [NeZero n] {m : σ →₀ ℕ} (a : R) (i : σ) :
    coeff (m + Finsupp.single i n) (C a) = 0 :=
  coeff_C_of_ne_zero (fun H ↦ by simpa [NeZero.ne] using congr($(H) i)) a
/-
**MvPolynomial.eq_C_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynomial σ R) : p = C (p.coeff 0)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.C_surjective`：C_surjective {R : Type*} [CommSemiring R] (σ 
: Type*) [IsEmpty σ] : Function.Surjective (C : R -> MvPolynomial σ R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynomial σ R) :
    p = C (p.coeff 0) := by
  obtain ⟨x, rfl⟩ := C_surjective σ p
  simp
/-
**MvPolynomial.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_one [DecidableEq σ] (m) : coeff m (1 : MvPolynomial σ R) = if 0 = m 
then 1 else 0
参数：m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
-/
theorem coeff_one [DecidableEq σ] (m) : coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0 :=
  coeff_C m 1

@[simp]
/-
**MvPolynomial.coeff_zero_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_zero_C (a) : coeff 0 (C a : MvPolynomial σ R) = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_zero_C (a) : coeff 0 (C a : MvPolynomial σ R) = a :=
  single_eq_same

@[simp]
/-
**MvPolynomial.coeff_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_zero_one : coeff 0 (1 : MvPolynomial σ R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
-/
theorem coeff_zero_one : coeff 0 (1 : MvPolynomial σ R) = 1 :=
  coeff_zero_C 1
/-
**MvPolynomial.coeff_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : Nat) : coeff m (X i ^ k : MvP
olynomial σ R) = if Finsupp.single i k = m then 1 else 0
参数：i : σ；m；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MvPolynomial.C_1`：C_1 : C 1 = (1 : MvPolynomial σ R)
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
-/
theorem coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : ℕ) :
    coeff m (X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 else 0 := by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _
/-
**MvPolynomial.coeff_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_X [DecidableEq σ] (i : σ) (m) : coeff m (X i : MvPolynomial σ R) = i
f Finsupp.single i 1 = m then 1 else 0
参数：i : σ；m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_X_pow`：coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : N
at) : coeff m (X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 el
se 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem coeff_X [DecidableEq σ] (i : σ) (m) :
    coeff m (X i : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0 := by
  rw [← coeff_X_pow, pow_one]

@[deprecated (since := "2026-05-25")]
alias coeff_X' := coeff_X

@[simp]
/-
**MvPolynomial.coeff_X_same** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_X_same (i : σ) : coeff (Finsupp.single i 1) (X i : MvPolynomial σ R)
 = 1
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_X`：coeff_X [DecidableEq σ] (i : σ) (m) : coeff m (X i
 : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_X_same (i : σ) :
    coeff (Finsupp.single i 1) (X i : MvPolynomial σ R) = 1 := by
  classical rw [coeff_X, if_pos rfl]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MvPolynomial.coeff_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : coeff m (C a * p) = a * c
oeff m p
参数：m；a : R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mul_def`：mul_def : p * q = p.coeff.sum fun m a => q.coeff.s
um fun n b => monomial (m + n) (a * b)
· 使用定理 `MvPolynomial.sum_C`：sum_C {A : Type*} [AddCommMonoid A] {b : (σ ->₀ Nat)
 -> R -> A} (w : b 0 0 = 0) : sum (C a).coeff b = b 0 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.sum_def`：sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ 
R} {b : (σ ->₀ Nat) -> R -> A} : (AddMonoidAlgebra.coeff p).sum b = ∑ m in p.sup
port, b m …
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : coeff m (C a * p) = a * coeff m p := by
  classical
  rw [mul_def, sum_C]
  · simp +contextual [sum_def, coeff_sum]
  simp
/-
**MvPolynomial.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ ->₀ Nat) : coeff
 n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p * coeff x.2 q
参数：p q : MvPolynomial σ R；n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_mul_antidiag`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] [inst_1 : Add M] (x y : AddMonoidAlgebra R M) (m : M)   (s : Fi
nset (M × M)), (∀ {p : M …
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
theorem coeff_mul [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (p * q) = ∑ x ∈ Finset.antidiagonal n, coeff x.1 p * coeff x.2 q :=
  AddMonoidAlgebra.coeff_mul_antidiag p q _ _ Finset.mem_antidiagonal

@[simp]
/-
**MvPolynomial.coeff_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mul_monomial (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) : co
eff (m + s) (p * monomial s r) = coeff m p * r
参数：m；s : σ ->₀ Nat；r : R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_mul_single_add`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddMonoid M] [IsCancelAdd M] (x : AddMonoidAlgebra 
R M)   (r : R) (m m' : M), …
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem coeff_mul_monomial (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (m + s) (p * monomial s r) = coeff m p * r := coeff_mul_single_add ..

@[simp]
/-
**MvPolynomial.coeff_monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_monomial_mul (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) : co
eff (s + m) (monomial s r * p) = r * coeff m p
参数：m；s : σ ->₀ Nat；r : R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_single_mul_add`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddMonoid M] [IsCancelAdd M] (x : AddMonoidAlgebra 
R M)   (r : R) (m m' : M), …
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem coeff_monomial_mul (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (s + m) (monomial s r * p) = r * coeff m p := coeff_single_mul_add ..

@[simp]
/-
**MvPolynomial.coeff_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) : coeff (m + Finsupp.single
 s 1) (p * X s) = coeff m p
参数：m；s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_mul_monomial`：coeff_mul_monomial (m) (s : σ ->₀ Nat) 
(r : R) (p : MvPolynomial σ R) : coeff (m + s) (p * monomial s r) = coeff m p * 
r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (m + Finsupp.single s 1) (p * X s) = coeff m p :=
  (coeff_mul_monomial _ _ _ _).trans (mul_one _)

@[simp]
/-
**MvPolynomial.coeff_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) : coeff (Finsupp.single s 1
 + m) (X s * p) = coeff m p
参数：m；s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_monomial_mul`：coeff_monomial_mul (m) (s : σ ->₀ Nat) 
(r : R) (p : MvPolynomial σ R) : coeff (s + m) (monomial s r * p) = r * coeff m 
p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p :=
  (coeff_monomial_mul _ _ _ _).trans (one_mul _)
/-
**MvPolynomial.coeff_single_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_single_X_pow [DecidableEq σ] (s s' : σ) (n n' : Nat) : (X (R
参数：s s' : σ；n n' : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_X_pow`：coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : N
at) : coeff m (X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 el
se 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_single_X_pow [DecidableEq σ] (s s' : σ) (n n' : ℕ) :
    (X (R := R) s ^ n).coeff (Finsupp.single s' n')
    = if s = s' ∧ n = n' ∨ n = 0 ∧ n' = 0 then 1 else 0 := by
  simp only [coeff_X_pow, single_eq_single_iff]

@[simp]
/-
**MvPolynomial.coeff_single_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_single_X [DecidableEq σ] (s s' : σ) (n : Nat) : (X s).coeff (R
参数：s s' : σ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `MvPolynomial.coeff_single_X_pow`：coeff_single_X_pow [DecidableEq σ] (s s
' : σ) (n n' : Nat) : (X (R
-/
lemma coeff_single_X [DecidableEq σ] (s s' : σ) (n : ℕ) :
    (X s).coeff (R := R) (Finsupp.single s' n) = if n = 1 ∧ s = s' then 1 else 0 := by
  simpa [eq_comm, and_comm] using coeff_single_X_pow s s' 1 n
/-
**MvPolynomial.coeff_prod_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_prod_X_pow [DecidableEq σ] (d : σ ->₀ Nat) (x : σ -> Nat) (s : Finse
t σ) : coeff d (∏ y in s, (X y : MvPolynomial σ R) ^ x y) = if d = Finsupp.indic
ator s (fun i _ => x i) then 1 else 0
参数：d : σ ->₀ Nat；x : σ -> Nat；s : Finset σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.prod_X_pow`：prod_X_pow (x : σ -> Nat) (t : Finset σ) : ∏ y 
in t, (X y : MvPolynomial σ R) ^ x y = monomial (indicator t (fun i _ => x i)) (
1 : R)
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_prod_X_pow [DecidableEq σ] (d : σ →₀ ℕ) (x : σ → ℕ) (s : Finset σ) :
    coeff d (∏ y ∈ s, (X y : MvPolynomial σ R) ^ x y) =
      if d = Finsupp.indicator s (fun i _ ↦ x i) then 1 else 0 := by
  simp_rw [prod_X_pow x s, coeff_monomial, eq_comm]

@[simp]
/-
**MvPolynomial.support_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_mul_X (s : σ) (p : MvPolynomial σ R) : (p * X s).support = p.suppo
rt.map (addRightEmbedding (Finsupp.single s 1))
参数：s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.support_coeff_mul_single`：∀ {k : Type u₁} {G : Type u₂}
 [inst : Semiring k] [inst_1 : Add G] [inst_2 : IsRightCancelAdd G]   (f : AddMo
noidAlgebra k G) (r : k),   (∀ …
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_mul_X (s : σ) (p : MvPolynomial σ R) :
    (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_coeff_mul_single p _ (by simp) _

@[simp]
/-
**MvPolynomial.support_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_X_mul (s : σ) (p : MvPolynomial σ R) : (X s * p).support = p.suppo
rt.map (addLeftEmbedding (Finsupp.single s 1))
参数：s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.support_coeff_single_mul`：∀ {k : Type u₁} {G : Type u₂}
 [inst : Semiring k] [inst_1 : Add G] [inst_2 : IsLeftCancelAdd G]   (f : AddMon
oidAlgebra k G) (r : k),   (∀ (…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_X_mul (s : σ) (p : MvPolynomial σ R) :
    (X s * p).support = p.support.map (addLeftEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_coeff_single_mul p _ (by simp) _

@[simp]
/-
**MvPolynomial.support_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_smul_eq {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module
.IsTorsionFree S R] {a : S} (h : a != 0) (p : MvPolynomial σ R) : (a • p).suppor
t = p.support
参数：h : a != 0；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_smul_eq`：support_smul_eq [Semiring R] [IsDomain R] [AddC
ommMonoid M] [Module R M] [Module.IsTorsionFree R M] {b : R} (hb : b != 0) {g : 
α ->₀ M} : (b…
-/
theorem support_smul_eq {S : Type*} [Semiring S] [IsDomain S] [Module S R]
    [Module.IsTorsionFree S R] {a : S} (h : a ≠ 0) (p : MvPolynomial σ R) :
    (a • p).support = p.support :=
  Finsupp.support_smul_eq h
/-
**MvPolynomial.support_sdiff_support_subset_support_add** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：support_sdiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomi
al σ R) : p.support \ q.support subseteq (p + q).support
参数：p q : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_sdiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support \ q.support ⊆ (p + q).support := by
  intro m hm
  simp only [Classical.not_not, mem_support_iff, Finset.mem_sdiff, Ne] at hm
  simp [hm.2, hm.1]

open scoped symmDiff in
/-
**MvPolynomial.support_symmDiff_support_subset_support_add** 是 Mathlib 中的一个定理，位于
命名空间 `MvPolynomial`。
形式化陈述：support_symmDiff_support_subset_support_add [DecidableEq σ] (p q : MvPolyn
omial σ R) : p.support ∆ q.support subseteq (p + q).support
参数：p q : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_def`：symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔
 b \ a
· 使用定理 `Finset.sup_eq_union`：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `MvPolynomial.support_sdiff_support_subset_support_add`：support_sdiff_sup
port_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) : p.support \ q
.support subseteq (p + q).support
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem support_symmDiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support ∆ q.support ⊆ (p + q).support := by
  rw [symmDiff_def, Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact support_sdiff_support_subset_support_add q p
/-
**MvPolynomial.coeff_mul_monomial'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mul_monomial' (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) : c
oeff m (p * monomial s r) = if s <= m then coeff (m - s) p * r else 0
参数：m；s : σ ->₀ Nat；r : R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_mul_monomial`：coeff_mul_monomial (m) (s : σ ->₀ Nat) 
(r : R) (p : MvPolynomial σ R) : coeff (m + s) (p * monomial s r) = coeff m p * 
r
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.add_subset_add_left`：∀ {α : Type u_2} [inst : DecidableEq α] [ins
t_1 : Add α] {s t₁ t₂ : Finset α}, t₁ ⊆ t₂ → s + t₁ ⊆ s + t₂
· 使用定理 `MvPolynomial.support_monomial_subset`：support_monomial_subset : (monomia
l s a).support subseteq {s}
· 使用定理 `MvPolynomial.support_mul`：support_mul [DecidableEq σ] (p q : MvPolynomia
l σ R) : (p * q).support subseteq p.support + q.support
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeff_mul_monomial' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (p * monomial s r) = if s ≤ m then coeff (m - s) p * r else 0 := by
  classical
  split_ifs with h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : ∃ j ∈ support p, j + s = m := by
      simpa [Finset.mem_add]
        using Finset.add_subset_add_left support_monomial_subset <| support_mul _ _ h
    exact le_add_left le_rfl
/-
**MvPolynomial.coeff_monomial_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_monomial_mul' (m) (s : σ ->₀ Nat) (r : R) (p : MvPolynomial σ R) : c
oeff m (monomial s r * p) = if s <= m then r * coeff (m - s) p else 0
参数：m；s : σ ->₀ Nat；r : R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPolynomial.coeff_mul_monomial'`：coeff_mul_monomial' (m) (s : σ ->₀ Nat
) (r : R) (p : MvPolynomial σ R) : coeff m (p * monomial s r) = if s <= m then c
oeff (m - s) p * r els…
-/
theorem coeff_monomial_mul' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (monomial s r * p) = if s ≤ m then r * coeff (m - s) p else 0 := by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm, mul_comm r]
  exact coeff_mul_monomial' _ _ _ _
/-
**MvPolynomial.coeff_mul_X'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) : coeff m 
(p * X s) = if s in m.support then coeff (m - Finsupp.single s 1) p else 0
参数：m；s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_mul_monomial'`：coeff_mul_monomial' (m) (s : σ ->₀ Nat
) (r : R) (p : MvPolynomial σ R) : coeff m (p * monomial s r) = if s <= m then c
oeff (m - s) p * r els…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (p * X s) = if s ∈ m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]
/-
**MvPolynomial.coeff_X_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_X_mul' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) : coeff m 
(X s * p) = if s in m.support then coeff (m - Finsupp.single s 1) p else 0
参数：m；s : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_monomial_mul'`：coeff_monomial_mul' (m) (s : σ ->₀ Nat
) (r : R) (p : MvPolynomial σ R) : coeff m (monomial s r * p) = if s <= m then r
 * coeff (m - s) p els…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_X_mul' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (X s * p) = if s ∈ m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_monomial_mul' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    one_mul]
/-
**MvPolynomial.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ forall d, coeff d p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.ext_iff`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring
 R] {p q : MvPolynomial σ R},   p = q ↔ ∀ (m : σ →₀ ℕ), MvPolynomial.coeff m p =
 MvPolynom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ ∀ d, coeff d p = 0 := by
  rw [MvPolynomial.ext_iff]
  simp only [coeff_zero]
/-
**MvPolynomial.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ exists d, coeff d p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPolynomial.eq_zero_iff`：eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ f
orall d, coeff d p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ne_zero_iff {p : MvPolynomial σ R} : p ≠ 0 ↔ ∃ d, coeff d p ≠ 0 := by
  rw [Ne, eq_zero_iff]
  push Not
  rfl

@[simp]
/-
**MvPolynomial.X_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_ne_zero [Nontrivial R] (s : σ) : X (R
参数：s : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.ne_zero_iff`：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ 
exists d, coeff d p != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_X_same`：coeff_X_same (i : σ) : coeff (Finsupp.single 
i 1) (X i : MvPolynomial σ R) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem X_ne_zero [Nontrivial R] (s : σ) :
    X (R := R) s ≠ 0 := by
  rw [ne_zero_iff]
  use Finsupp.single s 1
  simp only [coeff_X_same, ne_eq, one_ne_zero, not_false_eq_true]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MvPolynomial.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_eq_empty {p : MvPolynomial σ R} : p.support = ∅ ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq_empty {p : MvPolynomial σ R} : p.support = ∅ ↔ p = 0 := by simp [support]

@[simp]
/-
**MvPolynomial.support_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_nonempty {p : MvPolynomial σ R} : p.support.Nonempty ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPolynomial.support_eq_empty`：support_eq_empty {p : MvPolynomial σ R} :
 p.support = ∅ ↔ p = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma support_nonempty {p : MvPolynomial σ R} : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
/-
**MvPolynomial.exists_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_coeff_ne_zero {p : MvPolynomial σ R} (h : p != 0) : exists d, coeff
 d p != 0
参数：h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.ne_zero_iff`：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ 
exists d, coeff d p != 0
-/
theorem exists_coeff_ne_zero {p : MvPolynomial σ R} (h : p ≠ 0) : ∃ d, coeff d p ≠ 0 :=
  ne_zero_iff.mp h
/-
**MvPolynomial._root_.IsRegular.monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsRegular.monomial {m : σ →₀ ℕ} {a : R}
    (ha : IsRegular a) :
    IsRegular (monomial m a) := by
  rw [← isLeftRegular_iff_isRegular]
  intro p q h
  ext d
  have h' := congr_arg (coeff (m + d)) h
  simp only [coeff_monomial_mul] at h'
  rw [← ha.left.eq_iff, h']

@[simp]
/-
**MvPolynomial.monomial_one_mul_cancel_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：monomial_one_mul_cancel_left_iff {m : σ ->₀ Nat} : monomial m 1 * p = mono
mial m 1 * q ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRegular.monomial`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R
] {m : σ →₀ ℕ} {a : R},   IsRegular a → IsRegular ((MvPolynomial.monomial m) a)
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)
-/
theorem monomial_one_mul_cancel_left_iff {m : σ →₀ ℕ} :
    monomial m 1 * p = monomial m 1 * q ↔ p = q :=
  isRegular_one.monomial.left.eq_iff

@[simp]
/-
**MvPolynomial.X_mul_cancel_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mul_cancel_left_iff {i : σ} : X i * p = X i * q ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_one_mul_cancel_left_iff`：monomial_one_mul_cancel_l
eft_iff {m : σ ->₀ Nat} : monomial m 1 * p = monomial m 1 * q ↔ p = q
-/
theorem X_mul_cancel_left_iff {i : σ} :
    X i * p = X i * q ↔ p = q :=
  monomial_one_mul_cancel_left_iff

@[simp]
/-
**MvPolynomial.monomial_one_mul_cancel_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：monomial_one_mul_cancel_right_iff {m : σ ->₀ Nat} : p * monomial m 1 = q *
 monomial m 1 ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsRegular.monomial`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R
] {m : σ →₀ ℕ} {a : R},   IsRegular a → IsRegular ((MvPolynomial.monomial m) a)
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)
-/
theorem monomial_one_mul_cancel_right_iff {m : σ →₀ ℕ} :
    p * monomial m 1 = q * monomial m 1 ↔ p = q :=
  isRegular_one.monomial.right.eq_iff

@[simp]
/-
**MvPolynomial.X_mul_cancel_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mul_cancel_right_iff {i : σ} : p * X i = q * X i ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_one_mul_cancel_right_iff`：monomial_one_mul_cancel_
right_iff {m : σ ->₀ Nat} : p * monomial m 1 = q * monomial m 1 ↔ p = q
-/
theorem X_mul_cancel_right_iff {i : σ} :
    p * X i = q * X i ↔ p = q :=
  monomial_one_mul_cancel_right_iff
/-
**MvPolynomial.C_dvd_iff_dvd_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : C r ∣ φ ↔ forall i, r
 ∣ φ.coeff i
参数：r : R；φ : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose C hc using h
    classical
      let c' : (σ →₀ ℕ) → R := fun i => if i ∈ φ.support then C i else 0
      let ψ : MvPolynomial σ R := ∑ i ∈ φ.support, monomial i (c' i)
      use ψ
      apply MvPolynomial.ext
      intro i
      simp only [ψ, c', coeff_C_mul, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [notMem_support_iff] at hi
        rwa [mul_zero]
/-
**MvPolynomial.isRegular_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} {n : σ} [inst : CommSemiring R], IsRegular (
MvPolynomial.X n)
参数：MvPolynomial.X n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_X_mul`：coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R)
 : coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p
· 使用定理 `IsLeftRegular.right_of_commute`：∀ {R : Type u_1} [inst : Mul R] {a : R},
 (∀ (b : R), Commute a b) → IsLeftRegular a → IsRightRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
@[simp] lemma isRegular_X : IsRegular (X n : MvPolynomial σ R) := by
  suffices IsLeftRegular (X n : MvPolynomial σ R) from
    ⟨this, this.right_of_commute <| Commute.all _⟩
  intro P Q (hPQ : (X n) * P = (X n) * Q)
  ext i
  rw [← coeff_X_mul i n P, hPQ, coeff_X_mul i n Q]
/-
**MvPolynomial.isRegular_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} {n : σ} [inst : CommSemiring R] (k : ℕ), IsR
egular (MvPolynomial.X n ^ k)
参数：k : ℕ；MvPolynomial.X n ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.pow`：∀ {R : Type u_1} [inst : Monoid R] {a : R} (n : ℕ), IsReg
ular a → IsRegular (a ^ n)
· 使用定理 `MvPolynomial.isRegular_X`：∀ {R : Type u} {σ : Type u_1} {n : σ} [inst : 
CommSemiring R], IsRegular (MvPolynomial.X n)
-/
@[simp] lemma isRegular_X_pow (k : ℕ) : IsRegular (X n ^ k : MvPolynomial σ R) := isRegular_X.pow k
/-
**MvPolynomial.isRegular_prod_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] (s : Finset σ), IsRe
gular (∏ n ∈ s, MvPolynomial.X n)
参数：s : Finset σ；∏ n ∈ s, MvPolynomial.X n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsRegular.prod`：IsRegular.prod (h : forall i in s, IsRegular (f i)) : Is
Regular (∏ i in s, f i)
· 使用定理 `MvPolynomial.isRegular_X`：∀ {R : Type u} {σ : Type u_1} {n : σ} [inst : 
CommSemiring R], IsRegular (MvPolynomial.X n)
-/
@[simp] lemma isRegular_prod_X (s : Finset σ) :
    IsRegular (∏ n ∈ s, X n : MvPolynomial σ R) :=
  IsRegular.prod fun _ _ ↦ isRegular_X

/-- The finset of nonzero coefficients of a multivariate polynomial. -/
/-
**MvPolynomial.coeffs** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs (p : MvPolynomial σ R) : Finset R
参数：p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of nonzero coefficients of a multivariate polynomial.
-/
def coeffs (p : MvPolynomial σ R) : Finset R :=
  letI := Classical.decEq R
  Finset.image p.coeff p.support

@[simp]
/-
**MvPolynomial.coeffs_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_zero : coeffs (0 : MvPolynomial σ R) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeffs_zero : coeffs (0 : MvPolynomial σ R) = ∅ :=
  rfl
/-
**MvPolynomial.coeffs_one** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_one : coeffs (1 : MvPolynomial σ R) subseteq {1}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeffs.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemi
ring R] (p : MvPolynomial σ R),   p.coeffs = Finset.image (fun m => MvPolynomial
.coeff m p) p.…
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_one`：coeff_one [DecidableEq σ] (m) : coeff m (1 : MvP
olynomial σ R) = if 0 = m then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coeffs_one : coeffs (1 : MvPolynomial σ R) ⊆ {1} := by
  classical
    rw [coeffs, Finset.image_subset_iff]
    simp_all [coeff_one]

@[nontriviality]
/-
**MvPolynomial.coeffs_eq_empty_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：coeffs_eq_empty_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : 
p.coeffs = ∅
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma coeffs_eq_empty_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : p.coeffs = ∅ := by
  simpa [coeffs] using Subsingleton.eq_zero p

@[simp]
/-
**MvPolynomial.coeffs_one_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
形式化陈述：coeffs_one_of_nontrivial [Nontrivial R] : coeffs (1 : MvPolynomial σ R) = 
{1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用引理 `MvPolynomial.coeffs_one`：coeffs_one : coeffs (1 : MvPolynomial σ R) subs
eteq {1}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.support_one`：support_one [Nontrivial R] : (1 : MvPolynomial
 σ R).support = {0}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.coeff_zero_one`：coeff_zero_one : coeff 0 (1 : MvPolynomial 
σ R) = 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma coeffs_one_of_nontrivial [Nontrivial R] : coeffs (1 : MvPolynomial σ R) = {1} := by
  apply Finset.Subset.antisymm coeffs_one
  simp only [coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩
/-
**MvPolynomial.mem_coeffs_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_coeffs_iff {p : MvPolynomial σ R} {c : R} : c in p.coeffs ↔ exists n i
n p.support, c = p.coeff n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_coeffs_iff {p : MvPolynomial σ R} {c : R} :
    c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]
/-
**MvPolynomial.coeff_mem_coeffs** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_mem_coeffs {p : MvPolynomial σ R} (m : σ ->₀ Nat) (h : p.coeff m != 
0) : p.coeff m in p.coeffs
参数：m : σ ->₀ Nat；h : p.coeff m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
-/
lemma coeff_mem_coeffs {p : MvPolynomial σ R} (m : σ →₀ ℕ)
    (h : p.coeff m ≠ 0) : p.coeff m ∈ p.coeffs :=
  letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (mem_support_iff.mpr h)
/-
**MvPolynomial.zero_notMem_coeffs** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：zero_notMem_coeffs (p : MvPolynomial σ R) : 0 ∉ p.coeffs
参数：p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MvPolynomial.mem_coeffs_iff`：mem_coeffs_iff {p : MvPolynomial σ R} {c : 
R} : c in p.coeffs ↔ exists n in p.support, c = p.coeff n
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma zero_notMem_coeffs (p : MvPolynomial σ R) : 0 ∉ p.coeffs := by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := mem_coeffs_iff.mp hz
  exact (mem_support_iff.mp hnsupp) hn.symm
/-
**MvPolynomial.coeffs_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_C [DecidableEq R] (r : R) : (C (σ
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coeffs_C [DecidableEq R] (r : R) : (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r} := by
  classical
  aesop (add simp mem_coeffs_iff)
/-
**MvPolynomial.coeffs_C_subset** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_C_subset (r : R) : (C (σ
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.coeffs_C`：coeffs_C [DecidableEq R] (r : R) : (C (σ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma coeffs_C_subset (r : R) : (C (σ := σ) r).coeffs ⊆ {r} := by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]
/-
**MvPolynomial.coeffs_mul_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_mul_X (p : MvPolynomial σ R) (n : σ) : (p * X n).coeffs = p.coeffs
参数：p : MvPolynomial σ R；n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MvPolynomial.support_mul_X`：support_mul_X (s : σ) (p : MvPolynomial σ R)
 : (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1))
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `MvPolynomial.coeff_mul_X`：coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R)
 : coeff (m + Finsupp.single s 1) (p * X s) = coeff m p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coeffs_mul_X (p : MvPolynomial σ R) (n : σ) : (p * X n).coeffs = p.coeffs := by
  aesop (add simp mem_coeffs_iff)

@[simp]
/-
**MvPolynomial.coeffs_X_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_X_mul (p : MvPolynomial σ R) (n : σ) : (X n * p).coeffs = p.coeffs
参数：p : MvPolynomial σ R；n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `MvPolynomial.support_X_mul`：support_X_mul (s : σ) (p : MvPolynomial σ R)
 : (X s * p).support = p.support.map (addLeftEmbedding (Finsupp.single s 1))
· 使用定理 `addLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeft
CancelAdd G] (g h : G), (addLeftEmbedding g) h = g + h
· 使用定理 `MvPolynomial.coeff_X_mul`：coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R)
 : coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coeffs_X_mul (p : MvPolynomial σ R) (n : σ) : (X n * p).coeffs = p.coeffs := by
  aesop (add simp mem_coeffs_iff)
/-
**MvPolynomial.coeffs_add** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_add [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.suppor
t q.support) : (p + q).coeffs = p.coeffs union q.coeffs
参数：h : Disjoint p.support q.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `Disjoint.notMem_of_mem_left_finset`：∀ {α : Type u_2} {s t : Finset α}, D
isjoint s t → ∀ ⦃a : α⦄, a ∈ s → a ∉ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `Disjoint.notMem_of_mem_right_finset`：∀ {α : Type u_2} {s t : Finset α}, 
Disjoint s t → ∀ ⦃a : α⦄, a ∈ t → a ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coeffs_add [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.support q.support) :
    (p + q).coeffs = p.coeffs ∪ q.coeffs := by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ →₀ ℕ) (hne : p.coeff n ≠ 0) : q.coeff n = 0 :=
    notMem_support_iff.mp <| h.notMem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ →₀ ℕ) (hne : q.coeff n ≠ 0) : p.coeff n = 0 :=
    notMem_support_iff.mp <| h.notMem_of_mem_right_finset (mem_support_iff.mpr hne)
  have hor (n) (h : ¬coeff n p + coeff n q = 0) : coeff n p ≠ 0 ∨ coeff n q ≠ 0 := by
    by_cases hp : coeff n p = 0 <;> simp_all
  refine ⟨fun ⟨n, hn1, hn2⟩ ↦ ?_, ?_⟩
  · obtain (h | h) := hor n hn1
    · exact Or.inl ⟨n, by simp [h, hn2, hl n h]⟩
    · exact Or.inr ⟨n, by simp [h, hn2, hr n h]⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨n, by simp [hl n hn, hn]⟩
    · exact ⟨n, by simp [hr n hn, hn]⟩

end Coeff

section ConstantCoeff

/-- `constantCoeff p` returns the constant term of the polynomial `p`, defined as `coeff 0 p`.
This is a ring homomorphism.
-/
/-
**MvPolynomial.constantCoeff** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff : MvPolynomial σ R ->+* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`constantCoeff p` returns the constant term of the polynomial `p`, defined as `c
oeff 0 p`.
This is a ring homomorphism.
-/
def constantCoeff : MvPolynomial σ R →+* R where
  toFun := coeff 0
  map_one' := by simp
  map_mul' := by classical simp [coeff_mul]
  map_zero' := coeff_zero _
  map_add' := coeff_add _
/-
**MvPolynomial.constantCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_eq : (constantCoeff : MvPolynomial σ R -> R) = coeff 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_eq : (constantCoeff : MvPolynomial σ R → R) = coeff 0 :=
  rfl

variable (σ) in
@[simp]
/-
**MvPolynomial.constantCoeff_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_C (r : R) : constantCoeff (C r : MvPolynomial σ R) = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_C (r : R) : constantCoeff (C r : MvPolynomial σ R) = r := by
  simp [constantCoeff_eq]

variable (R) in
@[simp]
/-
**MvPolynomial.constantCoeff_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_X (i : σ) : constantCoeff (X i : MvPolynomial σ R) = 0
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_zero_X`：coeff_zero_X (i : σ) : coeff 0 (X i : MvPolyn
omial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_X (i : σ) : constantCoeff (X i : MvPolynomial σ R) = 0 := by
  simp [constantCoeff_eq]

@[simp]
/-
**MvPolynomial.constantCoeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_smul {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynom
ial σ S₁) : constantCoeff (a • f) = a • constantCoeff f
参数：a : R；f : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_smul {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynomial σ S₁) :
    constantCoeff (a • f) = a • constantCoeff f :=
  rfl
/-
**MvPolynomial.constantCoeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_monomial [DecidableEq σ] (d : σ ->₀ Nat) (r : R) : constantC
oeff (monomial d r) = if d = 0 then r else 0
参数：d : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.constantCoeff_eq`：constantCoeff_eq : (constantCoeff : MvPol
ynomial σ R -> R) = coeff 0
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
-/
theorem constantCoeff_monomial [DecidableEq σ] (d : σ →₀ ℕ) (r : R) :
    constantCoeff (monomial d r) = if d = 0 then r else 0 := by
  rw [constantCoeff_eq, coeff_monomial]

variable (σ R)

@[simp]
/-
**MvPolynomial.constantCoeff_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_comp_C : constantCoeff.comp (C : R ->+* MvPolynomial σ R) = 
RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.constantCoeff_C`：constantCoeff_C (r : R) : constantCoeff (C
 r : MvPolynomial σ R) = r
-/
theorem constantCoeff_comp_C : constantCoeff.comp (C : R →+* MvPolynomial σ R) = RingHom.id R := by
  ext x
  exact constantCoeff_C σ x
/-
**MvPolynomial.constantCoeff_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：constantCoeff_comp_algebraMap : constantCoeff.comp (algebraMap R (MvPolyno
mial σ R)) = RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.constantCoeff_comp_C`：constantCoeff_comp_C : constantCoeff.
comp (C : R ->+* MvPolynomial σ R) = RingHom.id R
-/
theorem constantCoeff_comp_algebraMap :
    constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R :=
  constantCoeff_comp_C _ _

end ConstantCoeff

section AsSum

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MvPolynomial.support_sum_monomial_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：support_sum_monomial_coeff (p : MvPolynomial σ R) : ∑ v in p.support, mono
mial v (coeff v p) = p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_sum`：∀ {R : Type u_1} {M : Type u_4} {ι : Type u_
7} [inst : Semiring R] (s : Finset ι) (f : ι → AddMonoidAlgebra R M),   (∑ i ∈ s
, f i).coeff = ∑…
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
-/
theorem support_sum_monomial_coeff (p : MvPolynomial σ R) :
    ∑ v ∈ p.support, monomial v (coeff v p) = p := by
  apply AddMonoidAlgebra.ext; rw [AddMonoidAlgebra.coeff_sum]; exact Finsupp.sum_single _
/-
**MvPolynomial.as_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.support, monomial v (coeff v 
p)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.support_sum_monomial_coeff`：support_sum_monomial_coeff (p :
 MvPolynomial σ R) : ∑ v in p.support, monomial v (coeff v p) = p
-/
theorem as_sum (p : MvPolynomial σ R) : p = ∑ v ∈ p.support, monomial v (coeff v p) :=
  (support_sum_monomial_coeff p).symm

end AsSum

section coeffsIn
variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

section Module
variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

variable (σ M) in
/-- The `R`-submodule of multivariate polynomials whose coefficients lie in an `R`-submodule `M`. -/
@[simps]
/-
**MvPolynomial.coeffsIn** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：coeffsIn : Submodule R (MvPolynomial σ S) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-submodule of multivariate polynomials whose coefficients lie in an `R`-s
ubmodule `M`.
-/
def coeffsIn : Submodule R (MvPolynomial σ S) where
  carrier := {p | ∀ i, p.coeff i ∈ M}
  add_mem' := by simp +contextual [add_mem]
  zero_mem' := by simp
  smul_mem' r p hp i := Submodule.smul_mem _ _ (hp i)
/-
**MvPolynomial.mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_coeffsIn : p in coeffsIn σ M ↔ forall i, p.coeff i in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_coeffsIn : p ∈ coeffsIn σ M ↔ ∀ i, p.coeff i ∈ M := .rfl

@[simp]
/-
**MvPolynomial.monomial_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_mem_coeffsIn : monomial i x in coeffsIn σ M ↔ x in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma monomial_mem_coeffsIn : monomial i x ∈ coeffsIn σ M ↔ x ∈ M := by
  classical
  simp only [mem_coeffsIn, coeff_monomial]
  exact ⟨fun h ↦ by simpa using h i, fun hs j ↦ by split <;> simp [hs]⟩

@[simp]
/-
**MvPolynomial.C_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：C_mem_coeffsIn : C x in coeffsIn σ M ↔ x in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.monomial_mem_coeffsIn`：monomial_mem_coeffsIn : monomial i x
 in coeffsIn σ M ↔ x in M
-/
lemma C_mem_coeffsIn : C x ∈ coeffsIn σ M ↔ x ∈ M := by simpa using monomial_mem_coeffsIn (i := 0)

@[simp]
/-
**MvPolynomial.one_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：one_coeffsIn : 1 in coeffsIn σ M ↔ 1 in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.C_mem_coeffsIn`：C_mem_coeffsIn : C x in coeffsIn σ M ↔ x in
 M
-/
lemma one_coeffsIn : 1 ∈ coeffsIn σ M ↔ 1 ∈ M := by simpa using C_mem_coeffsIn (x := (1 : S))

@[simp]
/-
**MvPolynomial.mul_monomial_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：mul_monomial_mem_coeffsIn : p * monomial i 1 in coeffsIn σ M ↔ p in coeffs
In σ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.coeff_mul_monomial'`：coeff_mul_monomial' (m) (s : σ ->₀ Nat
) (r : R) (p : MvPolynomial σ R) : coeff m (p * monomial s r) = if s <= m then c
oeff (m - s) p * r els…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma mul_monomial_mem_coeffsIn : p * monomial i 1 ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  simp only [mem_coeffsIn, coeff_mul_monomial']
  constructor
  · rintro hp j
    simpa using hp (j + i)
  · rintro hp i
    split <;> simp [hp]

@[simp]
/-
**MvPolynomial.monomial_mul_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：monomial_mul_mem_coeffsIn : monomial i 1 * p in coeffsIn σ M ↔ p in coeffs
In σ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monomial_mul_mem_coeffsIn : monomial i 1 * p ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  simp [mul_comm]

@[simp]
/-
**MvPolynomial.mul_X_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mul_X_mem_coeffsIn : p * X s in coeffsIn σ M ↔ p in coeffsIn σ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.mul_monomial_mem_coeffsIn`：mul_monomial_mem_coeffsIn : p * 
monomial i 1 in coeffsIn σ M ↔ p in coeffsIn σ M
-/
lemma mul_X_mem_coeffsIn : p * X s ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  simpa [-mul_monomial_mem_coeffsIn] using! mul_monomial_mem_coeffsIn (i := .single s 1)

@[simp]
/-
**MvPolynomial.X_mul_mem_coeffsIn** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mul_mem_coeffsIn : X s * p in coeffsIn σ M ↔ p in coeffsIn σ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma X_mul_mem_coeffsIn : X s * p ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by simp [mul_comm]

variable (M) in
/-
**MvPolynomial.coeffsIn_eq_span_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：coeffsIn_eq_span_monomial : coeffsIn σ M = .span R {monomial i m | (m in M
) (i : σ ->₀ Nat)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coeffsIn_eq_span_monomial : coeffsIn σ M = .span R {monomial i m | (m ∈ M) (i : σ →₀ ℕ)} := by
  classical
  refine le_antisymm ?_ <| Submodule.span_le.2 ?_
  · rintro p hp
    rw [p.as_sum]
    exact sum_mem fun i hi ↦ Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]
/-
**MvPolynomial.coeffsIn_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffsIn_le {N : Submodule R (MvPolynomial σ S)} : coeffsIn σ M <= N ↔ for
all m in M, forall i, monomial i m in N
参数：MvPolynomial σ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.coeffsIn_eq_span_monomial`：coeffsIn_eq_span_monomial : coef
fsIn σ M = .span R {monomial i m | (m in M) (i : σ ->₀ Nat)}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coeffsIn_le {N : Submodule R (MvPolynomial σ S)} :
    coeffsIn σ M ≤ N ↔ ∀ m ∈ M, ∀ i, monomial i m ∈ N := by
  simp [coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_comm (α := MvPolynomial σ S)]
/-
**MvPolynomial.mem_coeffsIn_iff_coeffs_subset** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyn
omial`。
形式化陈述：mem_coeffsIn_iff_coeffs_subset : p in coeffsIn σ M ↔ (p.coeffs : Set S) su
bseteq M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
lemma mem_coeffsIn_iff_coeffs_subset : p ∈ coeffsIn σ M ↔ (p.coeffs : Set S) ⊆ M := by
  simp only [mem_coeffsIn, coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ ↦ h x, fun h i ↦ ?_⟩
  by_cases hp : i ∈ p.support
  · exact h hp
  · convert! M.zero_mem
    simpa using hp

end Module

section Algebra
variable [Algebra R S] {M : Submodule R S}

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.coeffsIn_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffsIn_mul (M N : Submodule R S) : coeffsIn σ (M * N) = coeffsIn σ M * c
oeffsIn σ N
参数：M N : Submodule R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MvPolynomial.coeffsIn_le`：coeffsIn_le {N : Submodule R (MvPolynomial σ S
)} : coeffsIn σ M <= N ↔ forall m in M, forall i, monomial i m in N
· 使用定理 `Submodule.mul_induction_on'`：∀ {R : Type u} [inst : Semiring R] {A : Typ
e v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTowe
r R A A] {M N : S…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
-/
lemma coeffsIn_mul (M N : Submodule R S) : coeffsIn σ (M * N) = coeffsIn σ M * coeffsIn σ N := by
  classical
  refine le_antisymm (coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s, ← monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] using add_mem hx hy
  · rw [Submodule.mul_le]
    intro x hx y hy k
    rw [MvPolynomial.coeff_mul]
    exact sum_mem fun c hc ↦ Submodule.mul_mem_mul (hx _) (hy _)
/-
**MvPolynomial.coeffsIn_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} {σ : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring S] [inst_2 : Algebra R S]   {n : ℕ}, n ≠ 0 → ∀ (M : Submodul
e R S), MvPolynomial.coeffsIn σ (M ^ n) = MvPolynomial.coeffsIn σ M ^ n
参数：M : Submodule R S；M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma coeffsIn_pow : ∀ {n}, n ≠ 0 → ∀ M : Submodule R S, coeffsIn σ (M ^ n) = coeffsIn σ M ^ n
  | 1, _, M => by simp
  | n + 2, _, M => by rw [pow_succ, coeffsIn_mul, coeffsIn_pow, ← pow_succ]; exact n.succ_ne_zero
/-
**MvPolynomial.le_coeffsIn_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} {σ : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring S] [inst_2 : Algebra R S]   {M : Submodule R S} {n : ℕ}, MvP
olynomial.coeffsIn σ M ^ n ≤ MvPolynomial.coeffsIn σ (M ^ n)
参数：M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MvPolynomial.coeffsIn_pow`：∀ {R : Type u_2} {S : Type u_3} {σ : Type u_4
} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {n 
: ℕ}, n ≠ 0 → ∀…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
lemma le_coeffsIn_pow : ∀ {n}, coeffsIn σ M ^ n ≤ coeffsIn σ (M ^ n)
  | 0 => by simpa using ⟨1, map_one _⟩
  | n + 1 => (coeffsIn_pow n.succ_ne_zero _).ge

end Algebra
end coeffsIn

end CommSemiring

meta section Meta

open Mathlib.Tactic.Polynomial in
/-- Infer base ring for `MvPolynomial _ R`. Used by the `polynomial` tactic. -/
@[polynomial_infer_base]
/-
**MvPolynomial.mvPolynomialInferBaseImpl** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial
`。
形式化陈述：mvPolynomialInferBaseImpl : PolynomialExt where infer e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Infer base ring for `MvPolynomial _ R`. Used by the `polynomial` tactic.
-/
def mvPolynomialInferBaseImpl : PolynomialExt where
  infer e := do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure

end Meta

end MvPolynomial

