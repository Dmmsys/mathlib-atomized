/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Tactic.NormNum

/-!
# Formal (multivariate) power series

This file defines multivariate formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from multivariate polynomials to multivariate formal power series.

## Main definitions

- `MvPowerSeries.C`: constant power series

- `MvPowerSeries.X`: the indeterminates

- `MvPowerSeries.coeff`, `MvPowerSeries.constantCoeff`:
  the coefficients of a `MvPowerSeries`, its constant coefficient

- `MvPowerSeries.monomial`: the monomials

- `MvPowerSeries.coeff_mul`: computes the coefficients of the product of two `MvPowerSeries`

- `MvPowerSeries.coeff_prod` : computes the coefficients of products of `MvPowerSeries`

- `MvPowerSeries.coeff_pow` : computes the coefficients of powers of a `MvPowerSeries`

- `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`: if the constant coefficient
  of a `MvPowerSeries` is nilpotent, then some coefficients of its powers are automatically zero

- `MvPowerSeries.map`: apply a `RingHom` to the coefficients of a `MvPowerSeries` (as a `RingHom`).

- `MvPowerSeries.X_pow_dvd_iff`, `MvPowerSeries.X_dvd_iff`: equivalent
  conditions for (a power of) an indeterminate to divide a `MvPowerSeries`

- `MvPolynomial.toMvPowerSeries`: the canonical coercion from `MvPolynomial` to `MvPowerSeries`


## Note

This file sets up the (semi)ring structure on multivariate power series:
additional results are in:
* `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` : invertibility,
  formal power series over a local ring form a local ring;
* `Mathlib/RingTheory/MvPowerSeries/Trunc.lean`: truncation of power series.

In `Mathlib/RingTheory/PowerSeries/Basic.lean`, formal power series in one variable
will be obtained as a particular case, defined by
  `PowerSeries R := MvPowerSeries Unit R`.
See that file for a specific description.

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`MvPowerSeries σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring. -/
/-
**MvPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MvPowerSeries (σ : Type*) (R : Type*)
参数：σ : Type*；R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.
-/
def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ →₀ ℕ) → R

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
  inferInstanceAs <| Inhabited ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : Zero (MvPowerSeries σ R) :=
  inferInstanceAs <| Zero ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid R] : AddMonoid (MvPowerSeries σ R) :=
  inferInstanceAs <| AddMonoid ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] : AddGroup (MvPowerSeries σ R) :=
  inferInstanceAs <| AddGroup ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid R] : AddCommMonoid (MvPowerSeries σ R) :=
  inferInstanceAs <| AddCommMonoid ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : AddCommGroup (MvPowerSeries σ R) :=
  inferInstanceAs <| AddCommGroup ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
  inferInstanceAs <| Nontrivial ((σ →₀ ℕ) → R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R (MvPowerSeries σ A) :=
  inferInstanceAs <| Module R ((σ →₀ ℕ) → A)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
  inferInstanceAs <| IsScalarTower R S ((σ →₀ ℕ) → A)

section Semiring

variable [Semiring R]

/-- The `n`th monomial as multivariate formal power series:
  it is defined as the `R`-linear map from `R` to the semiring
  of multivariate formal power series associating to each `a`
  the map sending `n : σ →₀ ℕ` to the value `a`
  and sending all other `x : σ →₀ ℕ` different from `n` to `0`. -/
/-
**MvPowerSeries.monomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial (n : σ ->₀ Nat) : R ->ₗ[R] MvPowerSeries σ R
参数：n : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th monomial as multivariate formal power series:
  it is defined as the `R`-linear map from `R` to the semiring
  of multivariate formal power series associating to each `a`
  the map sending `n : σ →₀ ℕ` to the value `a`
  and sending all other `x : σ →₀ ℕ` different from `n` to `0`.
-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.single R (fun _ ↦ R) n

/-- The `n`th coefficient of a multivariate formal power series. -/
/-
**MvPowerSeries.coeff** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff (n : σ ->₀ Nat) : MvPowerSeries σ R ->ₗ[R] R
参数：n : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th coefficient of a multivariate formal power series.
-/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n
/-
**MvPowerSeries.coeff_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_apply (f : MvPowerSeries σ R) (d : σ ->₀ Nat) : coeff d f = f d
参数：f : MvPowerSeries σ R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_apply (f : MvPowerSeries σ R) (d : σ →₀ ℕ) : coeff d f = f d :=
  rfl

/-- Two multivariate formal power series are equal if all their coefficients are equal. -/
@[ext]
/-
**MvPowerSeries.ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ Nat, coeff n φ = coeff
 n ψ) : φ = ψ
参数：h : forall n : σ ->₀ Nat, coeff n φ = coeff n ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two multivariate formal power series are equal if all their coefficients are equ
al.
-/
theorem ext {φ ψ : MvPowerSeries σ R} (h : ∀ n : σ →₀ ℕ, coeff n φ = coeff n ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
if and only if all their coefficients are equal. -/
add_decl_doc MvPowerSeries.ext_iff

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.monomial_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial_def [DecidableEq σ] (n : σ ->₀ Nat) : monomial n = LinearMap.sing
le R (fun _ => R) n
参数：n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.monomial.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst : Sem
iring R] (n : σ →₀ ℕ),   MvPowerSeries.monomial n = LinearMap.single R (fun x =>
 R) n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) :
    monomial n = LinearMap.single R (fun _ ↦ R) n := by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.coeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_monomial [DecidableEq σ] (m n : σ ->₀ Nat) (a : R) : coeff m (monomi
al n a) = if m = n then a else 0
参数：m n : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.monomial_def`：monomial_def [DecidableEq σ] (n : σ ->₀ Nat)
 : monomial n = LinearMap.single R (fun _ => R) n
· 使用定理 `LinearMap.proj_apply`：proj_apply (i : ι) (b : (i : ι) -> φ i) : (proj i 
: ((i : ι) -> φ i) ->ₗ[R] φ i) b = b i
· 使用引理 `LinearMap.single_apply`：single_apply [DecidableEq ι] {i : ι} (v : φ i) :
 single R φ i v = Pi.single i v
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) :
    coeff m (monomial n a) = if m = n then a else 0 := by
  dsimp only [coeff, MvPowerSeries]
  rw [monomial_def, LinearMap.proj_apply (i := m), LinearMap.single_apply, Pi.single_apply]

@[simp]
/-
**MvPowerSeries.coeff_monomial_same** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_monomial_same (n : σ ->₀ Nat) (a : R) : coeff n (monomial n a) = a
参数：n : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.monomial_def`：monomial_def [DecidableEq σ] (n : σ ->₀ Nat)
 : monomial n = LinearMap.single R (fun _ => R) n
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff n (monomial n a) = a := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_same _ _
/-
**MvPowerSeries.coeff_monomial_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_monomial_ne {m n : σ ->₀ Nat} (h : m != n) (a : R) : coeff m (monomi
al n a) = 0
参数：h : m != n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.monomial_def`：monomial_def [DecidableEq σ] (n : σ ->₀ Nat)
 : monomial n = LinearMap.single R (fun _ => R) n
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff m (monomial n a) = 0 := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_of_ne h _
/-
**MvPowerSeries.eq_of_coeff_monomial_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries`。
形式化陈述：eq_of_coeff_monomial_ne_zero {m n : σ ->₀ Nat} {a : R} (h : coeff m (monom
ial n a) != 0) : m = n
参数：h : coeff m (monomial n a) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MvPowerSeries.coeff_monomial_ne`：coeff_monomial_ne {m n : σ ->₀ Nat} (h 
: m != n) (a : R) : coeff m (monomial n a) = 0
-/
theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff m (monomial n a) ≠ 0) :
    m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a

@[simp]
/-
**MvPowerSeries.coeff_comp_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_comp_monomial (n : σ ->₀ Nat) : (coeff (R
参数：n : σ ->₀ Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
-/
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

@[simp]
/-
**MvPowerSeries.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPowerSeries σ R) = 0
参数：n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero (n : σ →₀ ℕ) : coeff n (0 : MvPowerSeries σ R) = 0 :=
  rfl
/-
**MvPowerSeries.eq_zero_iff_forall_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPower
Series`。
形式化陈述：eq_zero_iff_forall_coeff_zero {f : MvPowerSeries σ R} : f = 0 ↔ (forall d 
: σ ->₀ Nat, coeff d f = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext_iff`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring 
R] {φ ψ : MvPowerSeries σ R},   φ = ψ ↔ ∀ (n : σ →₀ ℕ), (MvPowerSeries.coeff n) 
φ = (MvPowe…
-/
theorem eq_zero_iff_forall_coeff_zero {f : MvPowerSeries σ R} :
    f = 0 ↔ (∀ d : σ →₀ ℕ, coeff d f = 0) :=
  MvPowerSeries.ext_iff
/-
**MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
werSeries`。
形式化陈述：ne_zero_iff_exists_coeff_ne_zero (f : MvPowerSeries σ R) : f != 0 ↔ (exist
s d : σ ->₀ Nat, coeff d f != 0)
参数：f : MvPowerSeries σ R。
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
theorem ne_zero_iff_exists_coeff_ne_zero (f : MvPowerSeries σ R) :
    f ≠ 0 ↔ (∃ d : σ →₀ ℕ, coeff d f ≠ 0) := by
  simp only [MvPowerSeries.ext_iff, ne_eq, coeff_zero, not_forall]

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (MvPowerSeries σ R) :=
  ⟨monomial (0 : σ →₀ ℕ) 1⟩
/-
**MvPowerSeries.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_one [DecidableEq σ] : coeff n (1 : MvPowerSeries σ R) = if n = 0 the
n 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
-/
theorem coeff_one [DecidableEq σ] : coeff n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _
/-
**MvPowerSeries.coeff_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_one : coeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
-/
theorem coeff_zero_one : coeff (R := R) (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1
/-
**MvPowerSeries.monomial_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial_zero_one : monomial (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero_one : monomial (R := R) (0 : σ →₀ ℕ) 1 = 1 :=
  rfl
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoidWithOne (MvPowerSeries σ R) where
  natCast := fun n => monomial 0 n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := by simp [Nat.cast, monomial_zero_one]
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (MvPowerSeries σ R) :=
  letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ⟩
/-
**MvPowerSeries.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑ p in antidiagonal n, coeff
 p.1 φ * coeff p.2 ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem coeff_mul [DecidableEq σ] :
    coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]
/-
**MvPowerSeries.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ : MvPowerSeries σ R
), 0 * φ = 0
参数：φ : MvPowerSeries σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by classical simp [coeff_mul]
/-
**MvPowerSeries.mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ : MvPowerSeries σ R
), φ * 0 = 0
参数：φ : MvPowerSeries σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by classical simp [coeff_mul]
/-
**MvPowerSeries.coeff_monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_monomial_mul (a : R) : coeff m (monomial n a * φ) = if n <= m then a
 * coeff (m - n) φ else 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.eq_of_coeff_monomial_ne_zero`：eq_of_coeff_monomial_ne_zero
 {m n : σ ->₀ Nat} {a : R} (h : coeff m (monomial n a) != 0) : m = n
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `Finset.HasAntidiagonal.filter_fst_eq_antidiagonal`：filter_fst_eq_antidia
gonal (n m : A) [DecidablePred (· = m)] [Decidable (m <= n)] : {x in antidiagona
l n | x.fst = m} = if m <= n then {(m, …
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_ite_index`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s t : Finset ι) (f : ι → M),   ∑ x ∈ i
f p then s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_monomial_mul (a : R) :
    coeff m (monomial n a * φ) = if n ≤ m then a * coeff (m - n) φ else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial n a) * coeff p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.HasAntidiagonal.filter_fst_eq_antidiagonal
    _ n, Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
/-
**MvPowerSeries.coeff_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul_monomial (a : R) : coeff m (φ * monomial n a) = if n <= m then c
oeff (m - n) φ * a else 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.eq_of_coeff_monomial_ne_zero`：eq_of_coeff_monomial_ne_zero
 {m n : σ ->₀ Nat} {a : R} (h : coeff m (monomial n a) != 0) : m = n
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `Finset.HasAntidiagonal.filter_snd_eq_antidiagonal`：filter_snd_eq_antidia
gonal (n m : A) [DecidablePred (· = m)] [Decidable (m <= n)] : {x in antidiagona
l n | x.snd = m} = if m <= n then {(n -…
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_ite_index`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s t : Finset ι) (f : ι → M),   ∑ x ∈ i
f p then s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_monomial (a : R) :
    coeff m (φ * monomial n a) = if n ≤ m then coeff (m - n) φ * a else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff p.2 (monomial n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.HasAntidiagonal.filter_snd_eq_antidiagonal
    _ n, Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
/-
**MvPowerSeries.coeff_add_monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：coeff_add_monomial_mul (a : R) : coeff (m + n) (monomial m a * φ) = a * co
eff n φ
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_monomial_mul`：coeff_monomial_mul (a : R) : coeff m (
monomial n a * φ) = if n <= m then a * coeff (m - n) φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem coeff_add_monomial_mul (a : R) :
    coeff (m + n) (monomial m a * φ) = a * coeff n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  exact le_add_right le_rfl
/-
**MvPowerSeries.coeff_add_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：coeff_add_mul_monomial (a : R) : coeff (m + n) (φ * monomial n a) = coeff 
m φ * a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul_monomial`：coeff_mul_monomial (a : R) : coeff m (
φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem coeff_add_mul_monomial (a : R) :
    coeff (m + n) (φ * monomial n a) = coeff m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  exact le_add_left le_rfl

@[simp]
/-
**MvPowerSeries.commute_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：commute_monomial {a : R} {n} : Commute φ (monomial n a) ↔ forall m, Commut
e (coeff m φ) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `MvPowerSeries.ext_iff`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring 
R] {φ ψ : MvPowerSeries σ R},   φ = ψ ↔ ∀ (n : σ →₀ ℕ), (MvPowerSeries.coeff n) 
φ = (MvPowe…
· 使用定理 `MvPowerSeries.coeff_add_monomial_mul`：coeff_add_monomial_mul (a : R) : c
oeff (m + n) (monomial m a * φ) = a * coeff n φ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPowerSeries.coeff_add_mul_monomial`：coeff_add_mul_monomial (a : R) : c
oeff (m + n) (φ * monomial n a) = coeff m φ * a
· 使用定理 `MvPowerSeries.coeff_mul_monomial`：coeff_mul_monomial (a : R) : coeff m (
φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0
· 使用定理 `MvPowerSeries.coeff_monomial_mul`：coeff_monomial_mul (a : R) : coeff m (
monomial n a * φ) = if n <= m then a * coeff (m - n) φ else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial n a) ↔ ∀ m, Commute (coeff m φ) a := by
  rw [commute_iff_eq, MvPowerSeries.ext_iff]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]
/-
**MvPowerSeries.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ : MvPowerSeries σ R
), 1 * φ = φ
参数：φ : MvPowerSeries σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MvPowerSeries.coeff_add_monomial_mul`：coeff_add_monomial_mul (a : R) : c
oeff (m + n) (monomial m a * φ) = a * coeff n φ
-/
protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using! coeff_add_monomial_mul 0 n φ 1
/-
**MvPowerSeries.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ : MvPowerSeries σ R
), φ * 1 = φ
参数：φ : MvPowerSeries σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPowerSeries.coeff_add_mul_monomial`：coeff_add_mul_monomial (a : R) : c
oeff (m + n) (φ * monomial n a) = coeff m φ * a
-/
protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using! coeff_add_mul_monomial n 0 φ 1
/-
**MvPowerSeries.mul_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ₁ φ₂ φ₃ : MvPowerSer
ies σ R), φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃
参数：φ₁ φ₂ φ₃ : MvPowerSeries σ R；φ₂ + φ₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, map_add]
/-
**MvPowerSeries.add_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ₁ φ₂ φ₃ : MvPowerSer
ies σ R), (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃
参数：φ₁ φ₂ φ₃ : MvPowerSeries σ R；φ₁ + φ₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, map_add]
/-
**MvPowerSeries.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (φ₁ φ₂ φ₃ : MvPowerSer
ies σ R), φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃)
参数：φ₁ φ₂ φ₃ : MvPowerSeries σ R；φ₂ * φ₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (MvPowerSeries σ R) where
  mul_one := MvPowerSeries.mul_one
  one_mul := MvPowerSeries.one_mul
  mul_assoc := MvPowerSeries.mul_assoc
  mul_zero := MvPowerSeries.mul_zero
  zero_mul := MvPowerSeries.zero_mul
  left_distrib := MvPowerSeries.mul_add
  right_distrib := MvPowerSeries.add_mul

end Semiring

/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R) where
  mul_comm := fun φ ψ =>
    ext fun n => by
      classical
      simpa only [coeff_mul, mul_comm] using
        sum_antidiagonal_swap n fun a b => coeff a φ * coeff b ψ
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] : Ring (MvPowerSeries σ R) where
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : CommRing (MvPowerSeries σ R) where

section Semiring

variable [Semiring R]

/-
**MvPowerSeries.monomial_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial_mul_monomial (m n : σ ->₀ Nat) (a b : R) : monomial m a * monomia
l n b = monomial (m + n) (a * b)
参数：m n : σ ->₀ Nat；a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_mul_monomial`：coeff_mul_monomial (a : R) : coeff m (
φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
  classical
  ext k
  simp only [coeff_mul_monomial, coeff_monomial]
  split_ifs with h₁ h₂ h₃ h₃ h₂ <;> try rfl
  · rw [← h₂, tsub_add_cancel_of_le h₁] at h₃
    exact (h₃ rfl).elim
  · rw [h₃, add_tsub_cancel_right] at h₂
    exact (h₂ rfl).elim
  · exact zero_mul b
  · rw [h₂] at h₁
    exact (h₁ <| le_add_left le_rfl).elim

/-- The constant multivariate formal power series. -/
/-
**MvPowerSeries.C** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：C : R ->+* MvPowerSeries σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant multivariate formal power series.
-/
def C : R →+* MvPowerSeries σ R :=
  { monomial (0 : σ →₀ ℕ) with
    map_one' := rfl
    map_mul' := fun a b => Eq.trans (by simp) (monomial_mul_monomial _ _ a b).symm
    map_zero' := (monomial 0).map_zero }

@[simp]
/-
**MvPowerSeries.monomial_zero_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial_zero_eq_C : ⇑(monomial (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero_eq_C : ⇑(monomial (R := R) (0 : σ →₀ ℕ)) = C :=
  rfl
/-
**MvPowerSeries.monomial_zero_eq_C_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：monomial_zero_eq_C_apply (a : R) : monomial (0 : σ ->₀ Nat) a = C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero_eq_C_apply (a : R) : monomial (0 : σ →₀ ℕ) a = C a :=
  rfl
/-
**MvPowerSeries.coeff_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) : coeff n (C a) = if n = 0
 then a else 0
参数：n : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
-/
theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) :
    coeff n (C a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _
/-
**MvPowerSeries.coeff_zero_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_C (a : R) : coeff (0 : σ ->₀ Nat) (C a) = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
-/
theorem coeff_zero_C (a : R) : coeff (0 : σ →₀ ℕ) (C a) = a :=
  coeff_monomial_same 0 a
/-
**MvPowerSeries.coeff_C_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_C_of_ne_zero {n : σ ->₀ Nat} (h : n != 0) (a : R) : coeff n (C a) = 
0
参数：h : n != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_C_of_ne_zero {n : σ →₀ ℕ} (h : n ≠ 0) (a : R) : coeff n (C a) = 0 := by
  classical rw [coeff_C, if_neg h]

-- The intended use case of this theorem is for `m = 1` (often useful for `pderiv`).
@[simp]
/-
**MvPowerSeries.coeff_add_single_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_add_single_C {m : Nat} [NeZero m] {n : σ ->₀ Nat} (a : R) (i : σ) : 
coeff (n + single i m) (C a) = 0
参数：a : R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_C_of_ne_zero`：coeff_C_of_ne_zero {n : σ ->₀ Nat} (h 
: n != 0) (a : R) : coeff n (C a) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem coeff_add_single_C {m : ℕ} [NeZero m] {n : σ →₀ ℕ} (a : R) (i : σ) :
    coeff (n + single i m) (C a) = 0 :=
  coeff_C_of_ne_zero (fun H ↦ by simpa [NeZero.ne] using congr($(H) i)) a

@[grind inj]
/-
**MvPowerSeries.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：C_injective : Function.Injective (C : R -> MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_C`：coeff_zero_C (a : R) : coeff (0 : σ ->₀ Nat)
 (C a) = a
-/
theorem C_injective : Function.Injective (C : R → MvPowerSeries σ R) := by
  intro a b h
  rw [← coeff_zero_C a, h, coeff_zero_C]
/-
**MvPowerSeries.C_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：C_surjective [IsEmpty σ] : Function.Surjective (C : R -> MvPowerSeries σ R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.coeff_apply`：coeff_apply (f : MvPowerSeries σ R) (d : σ ->
₀ Nat) : coeff d f = f d
-/
theorem C_surjective [IsEmpty σ] : Function.Surjective (C : R → MvPowerSeries σ R) :=
  fun p => ⟨p 0, by ext n; simpa [coeff_C, Subsingleton.eq_zero n] using! coeff_apply _ _⟩
/-
**MvPowerSeries.C_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (r s : R), MvPowerSeri
es.C r = MvPowerSeries.C s ↔ r = s
参数：r s : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPowerSeries.C_injective`：C_injective : Function.Injective (C : R -> Mv
PowerSeries σ R)
-/
@[simp] theorem C_inj (r s : R) : (C r : MvPowerSeries σ R) = C s ↔ r = s := (C_injective).eq_iff

/-- The variables of the multivariate formal power series ring. -/
/-
**MvPowerSeries.X** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：X (s : σ) : MvPowerSeries σ R
参数：s : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The variables of the multivariate formal power series ring.
-/
def X (s : σ) : MvPowerSeries σ R :=
  monomial (single s 1) 1
/-
**MvPowerSeries.coeff_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) : coeff n (X s : MvPowerSe
ries σ R) = if n = single s 1 then 1 else 0
参数：n : σ ->₀ Nat；s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
-/
theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
    coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _
/-
**MvPowerSeries.coeff_index_single_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_index_single_X [DecidableEq σ] (s t : σ) : coeff (single t 1) (X s :
 MvPowerSeries σ R) = if t = s then 1 else 0
参数：s t : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finsupp.single_left_inj`：single_left_inj (h : b != 0) : single a b = sin
gle a' b ↔ a = a'
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

@[simp]
/-
**MvPowerSeries.coeff_index_single_self_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：coeff_index_single_self_X (s : σ) : coeff (single s 1) (X s : MvPowerSerie
s σ R) = 1
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
-/
theorem coeff_index_single_self_X (s : σ) : coeff (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _
/-
**MvPowerSeries.coeff_zero_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_X (s : σ) : coeff (0 : σ ->₀ Nat) (X s : MvPowerSeries σ R) = 0
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_zero_X (s : σ) : coeff (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 := by
  classical
  rw [coeff_X, if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)
/-
**MvPowerSeries.commute_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s)
参数：φ : MvPowerSeries σ R；s : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.commute_monomial`：commute_monomial {a : R} {n} : Commute φ
 (monomial n a) ↔ forall m, Commute (coeff m φ) a
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
-/
theorem commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s) :=
  φ.commute_monomial.mpr fun _m => Commute.one_right _
/-
**MvPowerSeries.X_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_mul {φ : MvPowerSeries σ R} {s : σ} : X s * φ = φ * X s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `MvPowerSeries.commute_X`：commute_X (φ : MvPowerSeries σ R) (s : σ) : Com
mute φ (X s)
-/
theorem X_mul {φ : MvPowerSeries σ R} {s : σ} : X s * φ = φ * X s :=
  φ.commute_X s |>.symm.eq
/-
**MvPowerSeries.commute_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：commute_X_pow (φ : MvPowerSeries σ R) (s : σ) (n : Nat) : Commute φ (X s ^
 n)
参数：φ : MvPowerSeries σ R；s : σ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `MvPowerSeries.commute_X`：commute_X (φ : MvPowerSeries σ R) (s : σ) : Com
mute φ (X s)
-/
theorem commute_X_pow (φ : MvPowerSeries σ R) (s : σ) (n : ℕ) : Commute φ (X s ^ n) :=
  φ.commute_X s |>.pow_right _
/-
**MvPowerSeries.X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_pow_mul {φ : MvPowerSeries σ R} {s : σ} {n : Nat} : X s ^ n * φ = φ * X 
s ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `MvPowerSeries.commute_X_pow`：commute_X_pow (φ : MvPowerSeries σ R) (s : 
σ) (n : Nat) : Commute φ (X s ^ n)
-/
theorem X_pow_mul {φ : MvPowerSeries σ R} {s : σ} {n : ℕ} : X s ^ n * φ = φ * X s ^ n :=
  φ.commute_X_pow s n |>.symm.eq
/-
**MvPowerSeries.X_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_def (s : σ) : X s = monomial (single s 1) (1 : R)
参数：s : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem X_def (s : σ) : X s = monomial (single s 1) (1 : R) :=
  rfl
/-
**MvPowerSeries.X_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_pow_eq (s : σ) (n : Nat) : (X s : MvPowerSeries σ R) ^ n = monomial (sin
gle s n) 1
参数：s : σ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `MvPowerSeries.X.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R
] (s : σ),   MvPowerSeries.X s = (MvPowerSeries.monomial fun₀ | s => 1) 1
· 使用定理 `MvPowerSeries.monomial_mul_monomial`：monomial_mul_monomial (m n : σ ->₀ 
Nat) (a b : R) : monomial m a * monomial n b = monomial (m + n) (a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem X_pow_eq (s : σ) (n : ℕ) : (X s : MvPowerSeries σ R) ^ n = monomial (single s n) 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]
/-
**MvPowerSeries.coeff_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_X_pow [DecidableEq σ] (m : σ ->₀ Nat) (s : σ) (n : Nat) : coeff m ((
X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0
参数：m : σ ->₀ Nat；s : σ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.X_pow_eq`：X_pow_eq (s : σ) (n : Nat) : (X s : MvPowerSerie
s σ R) ^ n = monomial (single s n) 1
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
-/
theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]

@[simp]
/-
**MvPowerSeries.coeff_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul_C (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R) : coeff n (φ *
 C a) = coeff n φ * a
参数：n : σ ->₀ Nat；φ : MvPowerSeries σ R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MvPowerSeries.coeff_add_mul_monomial`：coeff_add_mul_monomial (a : R) : c
oeff (m + n) (φ * monomial n a) = coeff m φ * a
-/
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (φ * C a) = coeff n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a

@[simp]
/-
**MvPowerSeries.coeff_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R) : coeff n (C a
 * φ) = a * coeff n φ
参数：n : σ ->₀ Nat；φ : MvPowerSeries σ R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPowerSeries.coeff_add_monomial_mul`：coeff_add_monomial_mul (a : R) : c
oeff (m + n) (monomial m a * φ) = a * coeff n φ
-/
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (C a * φ) = a * coeff n φ := by simpa using coeff_add_monomial_mul 0 n φ a
/-
**MvPowerSeries.coeff_zero_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ ->₀ Nat) (
φ * X s) = 0
参数：φ : MvPowerSeries σ R；s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPowerSeries.coeff_mul_monomial`：coeff_mul_monomial (a : R) : coeff m (
φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ →₀ ℕ) (φ * X s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]
/-
**MvPowerSeries.coeff_zero_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ ->₀ Nat) (
X s * φ) = 0
参数：φ : MvPowerSeries σ R；s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `MvPowerSeries.commute_X`：commute_X (φ : MvPowerSeries σ R) (s : σ) : Com
mute φ (X s)
· 使用定理 `MvPowerSeries.coeff_zero_mul_X`：coeff_zero_mul_X (φ : MvPowerSeries σ R)
 (s : σ) : coeff (0 : σ ->₀ Nat) (φ * X s) = 0
-/
theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ →₀ ℕ) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq, coeff_zero_mul_X]

/-- The constant coefficient of a formal power series. -/
/-
**MvPowerSeries.constantCoeff** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff : MvPowerSeries σ R ->+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_zero_one`：coeff_zero_one : coeff (R

--- 原说明 ---
The constant coefficient of a formal power series.
-/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff (0 : σ →₀ ℕ) with
    toFun := coeff (0 : σ →₀ ℕ)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul]
    map_zero' := map_zero _ }

@[simp]
/-
**MvPowerSeries.coeff_zero_eq_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：coeff_zero_eq_constantCoeff : ⇑(coeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) (0 : σ →₀ ℕ)) = constantCoeff :=
  rfl
/-
**MvPowerSeries.coeff_zero_eq_constantCoeff_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvP
owerSeries`。
形式化陈述：coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ -
>₀ Nat) φ = constantCoeff φ
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) :
    coeff (0 : σ →₀ ℕ) φ = constantCoeff φ :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_C (a : R) : constantCoeff (σ
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_C (a : R) : constantCoeff (σ := σ) (C a) = a :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_comp_C : (constantCoeff (σ
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_comp_C : (constantCoeff (σ := σ)).comp C = RingHom.id R :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_zero : constantCoeff (0 : MvPowerSeries σ R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_zero : constantCoeff (0 : MvPowerSeries σ R) = 0 :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_one : constantCoeff (1 : MvPowerSeries σ R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_one : constantCoeff (1 : MvPowerSeries σ R) = 1 :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_X (s : σ) : constantCoeff (R
参数：s : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_zero_X`：coeff_zero_X (s : σ) : coeff (0 : σ ->₀ Nat)
 (X s : MvPowerSeries σ R) = 0
-/
theorem constantCoeff_X (s : σ) : constantCoeff (R := R) (X s) = 0 :=
  coeff_zero_X s

@[simp]
/-
**MvPowerSeries.constantCoeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : MvPowerSerie
s σ S) (a : R) : constantCoeff (a • φ) = a • constantCoeff φ
参数：φ : MvPowerSeries σ S；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ := rfl

/-- If a multivariate formal power series is invertible,
then so is its constant coefficient. -/
/-
**MvPowerSeries.isUnit_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) : IsUnit (cons
tantCoeff φ)
参数：φ : MvPowerSeries σ R；h : IsUnit φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If a multivariate formal power series is invertible,
then so is its constant coefficient.
-/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff φ) :=
  h.map _

@[simp]
/-
**MvPowerSeries.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff n (a • f) = a * coe
ff n f
参数：f : MvPowerSeries σ R；n；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff n (a • f) = a * coeff n f :=
  rfl
/-
**MvPowerSeries.smul_eq_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C a * f
参数：f : MvPowerSeries σ R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MvPowerSeries.coeff_C_mul`：coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSerie
s σ R) (a : R) : coeff n (C a * φ) = a * coeff n φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C a * f := by
  ext
  simp
/-
**MvPowerSeries.X_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_single_iff`：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : 
M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    classical
    intro h
    replace h := congr_arg (coeff (single s 1)) h
    rw [coeff_X, if_pos rfl, coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      rcases H with H | H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · exfalso
      exact one_ne_zero h, congr_arg X⟩

end Semiring

section Map

variable {S T : Type*} [Semiring R] [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

set_option backward.isDefEq.respectTransparency false in
/-- The map between multivariate formal power series induced by a map on the coefficients. -/
/-
**MvPowerSeries.map** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：map : MvPowerSeries σ R ->+* MvPowerSeries σ S where toFun φ n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between multivariate formal power series induced by a map on the coeffic
ients.
-/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun φ n := f <| coeff n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f (coeff n 1) = coeff n 1 by
        classical
        rw [coeff_one, coeff_one]
        split_ifs with h
        · simp only [map_one]
        · simp only [map_zero]
  map_add' φ ψ :=
    ext fun n => show f (coeff n (φ + ψ)) = f (coeff n φ) + f (coeff n ψ) by simp
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        classical
        rw [coeff_mul, map_sum, coeff_mul]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ _; rw [f.map_mul]; rfl

@[simp]
/-
**MvPowerSeries.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_id : map (σ
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : map (σ := σ) (RingHom.id R) = RingHom.id _ :=
  rfl
/-
**MvPowerSeries.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_comp : map (σ
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp : map (σ := σ) (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
/-
**MvPowerSeries.coeff_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_map (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) : coeff n (map f φ) = f 
(coeff n φ)
参数：n : σ ->₀ Nat；φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_map (φ : MvPowerSeries σ R) : constantCoeff (map f φ) = f (c
onstantCoeff φ)
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_map (φ : MvPowerSeries σ R) :
    constantCoeff (map f φ) = f (constantCoeff φ) :=
  rfl

@[simp]
/-
**MvPowerSeries.map_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_monomial (n : σ ->₀ Nat) (a : R) : map f (monomial n a) = monomial n (
f a)
参数：n : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map f (monomial n a) = monomial n (f a) := by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]

@[simp]
/-
**MvPowerSeries.map_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_C (a : R) : map (σ
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.map_monomial`：map_monomial (n : σ ->₀ Nat) (a : R) : map f
 (monomial n a) = monomial n (f a)
-/
theorem map_C (a : R) : map (σ := σ) f (C a) = C (f a) :=
  map_monomial _ _ _

@[simp]
/-
**MvPowerSeries.map_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_X (s : σ) : map f (X s) = X s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.map_monomial`：map_monomial (n : σ ->₀ Nat) (a : R) : map f
 (monomial n a) = monomial n (f a)
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_X (s : σ) : map f (X s) = X s := by simp [MvPowerSeries.X]

@[simp]
/-
**MvPowerSeries.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_map {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂] (f : R ->+* S₁
) (g : S₁ ->+* S₂) (p : MvPowerSeries σ R) : map g (map f p) = map (g.comp f) p
参数：f : R ->+* S₁；g : S₁ ->+* S₂；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (f : R →+* S₁) (g : S₁ →+* S₂) (p : MvPowerSeries σ R) :
    map g (map f p) = map (g.comp f) p := by
  ext n
  simp

end Map

section toSubring

variable [Ring R] (p : MvPowerSeries σ R) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T)

/-- Given a multivariate formal power series `p` and a subring `T` that contains the
coefficients of `p`, return the corresponding multivariate formal power series
whose coefficients are in `T`. -/
/-
**MvPowerSeries.toSubring** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：toSubring : MvPowerSeries σ T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multivariate formal power series `p` and a subring `T` that contains the
coefficients of `p`, return the corresponding multivariate formal power series
whose coefficients are in `T`.
-/
def toSubring : MvPowerSeries σ T := fun n => ⟨p.coeff n, hp n⟩

@[simp]
/-
**MvPowerSeries.coeff_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_toSubring {n : σ ->₀ Nat} : (p.toSubring T hp).coeff n = p.coeff n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_toSubring {n : σ →₀ ℕ} : (p.toSubring T hp).coeff n = p.coeff n := rfl

@[simp]
/-
**MvPowerSeries.constantCoeff_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoe
ff
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoeff := rfl

@[simp]
/-
**MvPowerSeries.map_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_toSubring : (p.toSubring T hp).map T.subtype = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_toSubring : (p.toSubring T hp).map T.subtype = p := rfl

end toSubring

@[simp]
/-
**MvPowerSeries.map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_eq_zero {S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S] (
φ : MvPowerSeries σ R) (f : R ->+* S) : φ.map f = 0 ↔ φ = 0
参数：φ : MvPowerSeries σ R；f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_zero {S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S]
    (φ : MvPowerSeries σ R) (f : R →+* S) : φ.map f = 0 ↔ φ = 0 := by
  simp only [MvPowerSeries.ext_iff]
  congr! with n
  simp

section Semiring

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.X_pow_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_pow_dvd_iff {s : σ} {n : Nat} {φ : MvPowerSeries σ R} : (X s : MvPowerSe
ries σ R) ^ n ∣ φ ↔ forall m : σ ->₀ Nat, m s < n -> coeff m φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `MvPowerSeries.coeff_X_pow`：coeff_X_pow [DecidableEq σ] (m : σ ->₀ Nat) (
s : σ) (n : Nat) : coeff m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n t
hen 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 41 条，此处仅展示前 30 条）
-/
theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff m φ = 0 := by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul, Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow, if_neg, zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right n _
  · intro h
    refine ⟨fun m => coeff (m + single s n) φ, ?_⟩
    ext m
    by_cases H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        simpa using! congr_arg (fun m : σ →₀ ℕ => coeff m φ) H.symm
      · rintro ⟨i, j⟩ hij hne
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij, ← hi, Prod.mk_inj]
          refine ⟨rfl, ?_⟩
          ext t
          simp only [add_tsub_cancel_left]
        · exact zero_mul _
      · intro hni
        exfalso
        apply hni
        rwa [mem_antidiagonal, add_comm]
    · rw [h, coeff_mul, Finset.sum_eq_zero]
      · rintro ⟨i, j⟩ hij
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply H
          rw [← hij, hi]
          ext
          rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_comm]
        · exact zero_mul _
      · contrapose! H
        ext t
        by_cases hst : s = t
        · subst t
          simpa using! tsub_add_cancel_of_le H
        · simp [hst]
/-
**MvPowerSeries.X_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} : (X s : MvPowerSeries σ R) ∣ φ 
↔ forall m : σ ->₀ Nat, m s = 0 -> coeff m φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MvPowerSeries.X_pow_dvd_iff`：X_pow_dvd_iff {s : σ} {n : Nat} {φ : MvPowe
rSeries σ R} : (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ forall m : σ ->₀ Nat, m s < n
 -> coeff m φ = 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
-/
theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)

end Semiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- Coefficients of a product of power series -/
/-
**MvPowerSeries.coeff_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_prod [DecidableEq ι] [DecidableEq σ] (f : ι -> MvPowerSeries σ R) (d
 : σ ->₀ Nat) (s : Finset ι) : coeff d (∏ j in s, f j) = ∑ l in finsuppAntidiag 
s d, ∏ i in s, coeff (l i) (f i)
参数：f : ι -> MvPowerSeries σ R；d : σ ->₀ Nat；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_one`：coeff_one [DecidableEq σ] : coeff n (1 : MvPowe
rSeries σ R) = if n = 0 then 1 else 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.finsuppAntidiag_empty`：finsuppAntidiag_empty (n : μ) : finsuppAnt
idiag (∅ : Finset ι) n = if n = 0 then {0} else ∅
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finset.finsuppAntidiag_insert`：finsuppAntidiag_insert {a : ι} {s : Finse
t ι} (h : a ∉ s) (n : μ) : finsuppAntidiag (insert a s) n = (antidiagonal n).biU
nion (fun p : μ × μ…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_biUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {t : κ
 → Finse…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Coefficients of a product of power series
-/
theorem coeff_prod [DecidableEq ι] [DecidableEq σ]
    (f : ι → MvPowerSeries σ R) (d : σ →₀ ℕ) (s : Finset ι) :
    coeff d (∏ j ∈ s, f j) =
      ∑ l ∈ finsuppAntidiag s d,
        ∏ i ∈ s, coeff (l i) (f i) := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | insert a s ha ih =>
    rw [finsuppAntidiag_insert ha, prod_insert ha, coeff_mul, sum_biUnion]
    · apply Finset.sum_congr rfl
      simp only [mem_antidiagonal, sum_map, Function.Embedding.coeFn_mk, coe_update, Prod.forall]
      rintro u v rfl
      rw [ih, Finset.mul_sum, ← Finset.sum_attach]
      apply Finset.sum_congr rfl
      simp only [mem_attach, Finset.prod_insert ha, Function.update_self, forall_true_left,
        Subtype.forall]
      rintro x -
      rw [Finset.prod_congr rfl]
      intro i hi
      rw [Function.update_of_ne]
      exact ne_of_mem_of_not_mem hi ha
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, mem_coe, mem_antidiagonal, ne_eq,
        disjoint_left, mem_map, mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists,
        exists_prop, not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Prod.forall, Prod.mk.injEq]
      rintro u v rfl u' v' huv h k - l - hkl
      obtain rfl : u' = u := by
        simpa only [Finsupp.coe_update, Function.update_self] using DFunLike.congr_fun hkl a
      simp only [add_right_inj] at huv
      exact h rfl huv.symm
/-
**MvPowerSeries.prod_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：prod_monomial (f : ι -> σ ->₀ Nat) (g : ι -> R) (s : Finset ι) : ∏ i in s,
 monomial (f i) (g i) = monomial (∑ i in s, f i) (∏ i in s, g i)
参数：f : ι -> σ ->₀ Nat；g : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `MvPowerSeries.monomial_mul_monomial`：monomial_mul_monomial (m n : σ ->₀ 
Nat) (a b : R) : monomial m a * monomial n b = monomial (m + n) (a * b)
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
-/
theorem prod_monomial (f : ι → σ →₀ ℕ) (g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, monomial (f i) (g i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha h => simp [h, monomial_mul_monomial]

/-- The `d`th coefficient of a power of a multivariate power series
is the sum, indexed by `finsuppAntidiag (Finset.range n) d`, of products of coefficients -/
/-
**MvPowerSeries.coeff_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_pow [DecidableEq σ] (f : MvPowerSeries σ R) {n : Nat} (d : σ ->₀ Nat
) : coeff d (f ^ n) = ∑ l in finsuppAntidiag (Finset.range n) d, ∏ i in Finset.r
ange n, coeff (l i) f
参数：f : MvPowerSeries σ R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `MvPowerSeries.coeff_prod`：coeff_prod [DecidableEq ι] [DecidableEq σ] (f 
: ι -> MvPowerSeries σ R) (d : σ ->₀ Nat) (s : Finset ι) : coeff d (∏ j in s, f 
j) = ∑ l in fi…

--- 原说明 ---
The `d`th coefficient of a power of a multivariate power series
is the sum, indexed by `finsuppAntidiag (Finset.range n) d`, of products of coef
ficients
-/
theorem coeff_pow [DecidableEq σ] (f : MvPowerSeries σ R) {n : ℕ} (d : σ →₀ ℕ) :
    coeff d (f ^ n) =
      ∑ l ∈ finsuppAntidiag (Finset.range n) d,
        ∏ i ∈ Finset.range n, coeff (l i) f := by
  suffices f ^ n = (Finset.range n).prod fun _ ↦ f by
    rw [this, coeff_prod]
  rw [Finset.prod_const, card_range]
/-
**MvPowerSeries.monomial_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：monomial_pow (m : σ ->₀ Nat) (a : R) (n : Nat) : (monomial m a) ^ n = mono
mial (n • m) (a ^ n)
参数：m : σ ->₀ Nat；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pow_eq_prod_const`：pow_eq_prod_const (b : M) : forall n, b ^ n = 
∏ _k in range n, b
· 使用定理 `MvPowerSeries.prod_monomial`：prod_monomial (f : ι -> σ ->₀ Nat) (g : ι -
> R) (s : Finset ι) : ∏ i in s, monomial (f i) (g i) = monomial (∑ i in s, f i) 
(∏ i in s, g i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.nsmul_eq_sum_const`：∀ {M : Type u_4} [inst : AddCommMonoid M] (b 
: M) (n : ℕ), n • b = ∑ _k ∈ Finset.range n, b
-/
theorem monomial_pow (m : σ →₀ ℕ) (a : R) (n : ℕ) :
    (monomial m a) ^ n = monomial (n • m) (a ^ n) := by
  rw [Finset.pow_eq_prod_const, prod_monomial, ← Finset.nsmul_eq_sum_const,
    ← Finset.pow_eq_prod_const]

/-- Vanishing of coefficients of powers of multivariate power series
when the constant coefficient is nilpotent
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, proposition 3][bourbaki1981] -/
/-
**MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：coeff_eq_zero_of_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : Nat}
 (hf : constantCoeff f ^ m = 0) {d : σ ->₀ Nat} {n : Nat} (hn : m + degree d <= 
n) : coeff d (f ^ n) = 0
参数：hf : constantCoeff f ^ m = 0；hn : m + degree d <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_pow`：coeff_pow [DecidableEq σ] (f : MvPowerSeries σ 
R) {n : Nat} (d : σ ->₀ Nat) : coeff d (f ^ n) = ∑ l in finsuppAntidiag (Finset.
range n) d, ∏…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff :
 ⇑(coeff (R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.card_sdiff_add_card_eq_card`：card_sdiff_add_card_eq_card (h : s s
ubseteq t) : #(t \ s) + #s = #t
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_finsuppAntidiag`：∀ {ι : Type u_1} {μ : Type u_2} [inst : Deci
dableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ]   [ins
t_3 : DecidableE…
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Vanishing of coefficients of powers of multivariate power series
when the constant coefficient is nilpotent
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, proposition 3][bourbaki1981]
-/
theorem coeff_eq_zero_of_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : ℕ}
    (hf : constantCoeff f ^ m = 0) {d : σ →₀ ℕ} {n : ℕ} (hn : m + degree d ≤ n) :
    coeff d (f ^ n) = 0 := by
  classical
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_finsuppAntidiag] at hk
  set s := {i ∈ range n | k i = 0} with hs_def
  have hs : s ⊆ range n := filter_subset _ _
  have hs' (i : ℕ) (hi : i ∈ s) : coeff (k i) f = constantCoeff f := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2, coeff_zero_eq_constantCoeff]
  have hs'' (i : ℕ) (hi : i ∈ s) : k i = 0 := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2]
  rw [← prod_sdiff (s₁ := s) (filter_subset _ _)]
  apply mul_eq_zero_of_right
  rw [prod_congr rfl hs', prod_const]
  suffices m ≤ #s by
    obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le this
    rw [hm', pow_add, hf, zero_mul]
  rw [← Nat.add_le_add_iff_right, add_comm #s,
    Finset.card_sdiff_add_card_eq_card (filter_subset _ _), card_range]
  apply le_trans _ hn
  simp only [add_comm m, Nat.add_le_add_iff_right, ← hk.1,
    ← sum_sdiff (hs), sum_eq_zero (s := s) hs'', add_zero]
  rw [← hs_def]
  convert! Finset.card_nsmul_le_sum (range n \ s) (fun x ↦ degree (k x)) 1 _
  · simp only [smul_eq_mul, mul_one]
  · simp only [degree_eq_weight_one, map_sum]
  · simp only [hs_def, mem_filter, mem_sdiff, mem_range, not_and, and_imp]
    intro i hi hi'
    rw [← not_lt, Nat.lt_one_iff, degree_eq_zero_iff]
    exact hi' hi

end CommSemiring

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B]

/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (MvPowerSeries σ A) where
  algebraMap := (MvPowerSeries.map (algebraMap R A)).comp C
  commutes' := fun a φ => by
    ext n
    simp [Algebra.commutes]
  smul_def' := fun a σ => by
    ext n
    simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]
/-
**MvPowerSeries.c_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：c_eq_algebraMap : C = algebraMap R (MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c_eq_algebraMap : C = algebraMap R (MvPowerSeries σ R) :=
  rfl
/-
**MvPowerSeries.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：algebraMap_apply {r : R} : algebraMap R (MvPowerSeries σ A) r = C (algebra
Map R A r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.map_C`：map_C (a : R) : map (σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C (algebraMap R A r) := by
  change (MvPowerSeries.map (algebraMap R A)).comp C r = _
  simp

/-- Change of coefficients in mv power series, as an `AlgHom` -/
/-
**MvPowerSeries.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：mapAlgHom (φ : A ->ₐ[R] B) : MvPowerSeries σ A ->ₐ[R] MvPowerSeries σ B wh
ere toRingHom
参数：φ : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change of coefficients in mv power series, as an `AlgHom`
-/
def mapAlgHom (φ : A →ₐ[R] B) :
    MvPowerSeries σ A →ₐ[R] MvPowerSeries σ B where
  toRingHom := MvPowerSeries.map φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]
/-
**MvPowerSeries.mapAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：mapAlgHom_apply (φ : A ->ₐ[R] B) (f : MvPowerSeries σ A) : mapAlgHom (σ
参数：φ : A ->ₐ[R] B；f : MvPowerSeries σ A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgHom_apply (φ : A →ₐ[R] B) (f : MvPowerSeries σ A) :
    mapAlgHom (σ := σ) φ f = MvPowerSeries.map φ f := rfl
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      classical
      rw [Ne, SetLike.ext_iff, not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [MvPowerSeries.ext_iff, not_forall]
      refine ⟨Finsupp.single default 1, ?_⟩
      simp [algebraMap_apply, coeff_C]⟩⟩

end Algebra


end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
@[coe]
/-
**MvPolynomial.toMvPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：toMvPowerSeries : MvPolynomial σ R -> MvPowerSeries σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from multivariate polynomials into multivariate formal pow
er series.
-/
def toMvPowerSeries : MvPolynomial σ R → MvPowerSeries σ R :=
  fun φ n => coeff n φ

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
/-
**MvPolynomial.coeToMvPowerSeries** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from multivariate polynomials into multivariate formal pow
er series.
-/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨toMvPowerSeries⟩
/-
**MvPolynomial.coe_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl

@[simp, norm_cast]
/-
**MvPolynomial.coeff_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff n ↑φ = coeff n φ
参数：n : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_coe (n : σ →₀ ℕ) : MvPowerSeries.coeff n ↑φ = coeff n φ :=
  rfl

@[simp, norm_cast]
/-
**MvPolynomial.coe_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_monomial (n : σ ->₀ Nat) (a : R) : (monomial n a : MvPowerSeries σ R) 
= MvPowerSeries.monomial n a
参数：n : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_coe`：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff 
n ↑φ = coeff n φ
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_monomial (n : σ →₀ ℕ) (a : R) :
    (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a :=
  MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | subst m; contradiction

@[simp, norm_cast]
/-
**MvPolynomial.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl

@[simp, norm_cast]
/-
**MvPolynomial.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coe_monomial`：coe_monomial (n : σ ->₀ Nat) (a : R) : (monom
ial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a
-/
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
    coe_monomial _ _

@[simp, norm_cast]
/-
**MvPolynomial.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl

@[simp, norm_cast]
/-
**MvPolynomial.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
/-
**MvPolynomial.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_smul (φ : MvPolynomial σ R) (r : R) : (r • φ : MvPolynomial σ R) = r •
 (φ : MvPowerSeries σ R)
参数：φ : MvPolynomial σ R；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (φ : MvPolynomial σ R) (r : R) :
    (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp, norm_cast]
/-
**MvPolynomial.coe_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSe
ries.C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coe_monomial`：coe_monomial (n : σ ->₀ Nat) (a : R) : (monom
ial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a
-/
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C a :=
  coe_monomial _ _

@[simp, norm_cast]
/-
**MvPolynomial.coe_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSe
ries.X s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coe_monomial`：coe_monomial (n : σ ->₀ Nat) (a : R) : (monom
ial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a
-/
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s :=
  coe_monomial _ _

variable (σ R)
/-
**MvPolynomial.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_injective : Function.Injective ((↑) : MvPolynomial σ R -> MvPowerSerie
s σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_injective : Function.Injective ((↑) : MvPolynomial σ R → MvPowerSeries σ R) := by
  intro x y h
  ext
  simp_rw [← coeff_coe, h]

variable {σ R φ ψ}

@[simp, norm_cast]
/-
**MvPolynomial.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPolynomial.coe_injective`：coe_injective : Function.Injective ((↑) : Mv
Polynomial σ R -> MvPowerSeries σ R)
-/
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff

@[simp]
/-
**MvPolynomial.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coe_zero`：coe_zero : ((0 : MvPolynomial σ R) : MvPowerSerie
s σ R) = 0
· 使用定理 `MvPolynomial.coe_inj`：coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
/-
**MvPolynomial.coe_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coe_one`：coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries 
σ R) = 1
· 使用定理 `MvPolynomial.coe_inj`：coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/-- The coercion from multivariate polynomials to multivariate power series
as a ring homomorphism.
-/
/-
**MvPolynomial.coeToMvPowerSeries.ringHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomia
l.coeToMvPowerSeries`。
形式化陈述：{σ : Type u_1} → {R : Type u_2} → [inst : CommSemiring R] → MvPolynomial σ
 R →+* MvPowerSeries σ R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coe_one`：coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries 
σ R) = 1
· 使用定理 `MvPolynomial.coe_mul`：coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSer
ies σ R) = φ * ψ
· 使用定理 `MvPolynomial.coe_zero`：coe_zero : ((0 : MvPolynomial σ R) : MvPowerSerie
s σ R) = 0
· 使用定理 `MvPolynomial.coe_add`：coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSer
ies σ R) = φ + ψ

--- 原说明 ---
The coercion from multivariate polynomials to multivariate power series
as a ring homomorphism.
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R where
  toFun := (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]
/-
**MvPolynomial.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_pow (n : Nat) : ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ 
: MvPowerSeries σ R) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem coe_pow (n : ℕ) :
    ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _

variable (φ ψ)

@[simp]
/-
**MvPolynomial.coeToMvPowerSeries.ringHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial.coeToMvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (φ : MvPolynomial 
σ R),   MvPolynomial.coeToMvPowerSeries.ringHom φ = ↑φ
参数：φ : MvPolynomial σ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToMvPowerSeries.ringHom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl
/-
**MvPolynomial._root_.MvPowerSeries.monomial_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
vPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_one_eq
    (e : σ →₀ ℕ) :
    MvPowerSeries.monomial e (1 : R) =
      e.prod fun s n ↦ (MvPowerSeries.X s) ^ n := by
  simp only [← coe_X, ← coe_pow, ← coe_monomial, monomial_eq, map_one, one_mul]
  simp only [← coeToMvPowerSeries.ringHom_apply, ← map_finsuppProd]
/-
**MvPolynomial._root_.MvPowerSeries.monomial_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_eq' (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial e r
      = MvPowerSeries.C r * e.prod fun s e => (MvPowerSeries.X s) ^ e := by
  conv_lhs => rw [← mul_one r]
  rw [← smul_eq_mul, ← MvPowerSeries.smul_eq_C_mul, LinearMap.CompatibleSMul.map_smul,
    MvPowerSeries.monomial_one_eq]
/-
**MvPolynomial._root_.MvPowerSeries.monomial_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_smul_eq (e : σ →₀ ℕ) (p : ℕ) (r : R) :
    MvPowerSeries.monomial (p • e) r
      = MvPowerSeries.C r * e.prod fun s e => ((MvPowerSeries.X s) ^ p) ^ e := by
  rw [MvPowerSeries.monomial_eq', Finsupp.prod_of_support_subset _ Finsupp.support_smul _
    (by simp), Finsupp.prod]
  simp [pow_mul]
/-
**MvPolynomial._root_.MvPowerSeries.monomial_mapDomain_apply_one** 是 Mathlib 中的一
个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_mapDomain_apply_one {τ : Type*} (d : σ →₀ ℕ) (f : σ → τ) :
    MvPowerSeries.monomial (mapDomain f d) (1 : R) =
      d.prod fun s e ↦ MvPowerSeries.X (f s) ^ e := by
  simp [pow_add, prod_sum_index, MvPowerSeries.monomial_one_eq, mapDomain]

section Algebra

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The coercion from multivariate polynomials to multivariate power series
as an algebra homomorphism.
-/
/-
**MvPolynomial.coeToMvPowerSeries.algHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial
.coeToMvPowerSeries`。
形式化陈述：{σ : Type u_1} →   {R : Type u_2} →     [inst : CommSemiring R] →       (A
 : Type u_3) → [inst_1 : CommSemiring A] → [inst_2 : Algebra R A] → MvPolynomial
 σ R →ₐ[R] MvPowerSeries σ A
参数：A : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from multivariate polynomials to multivariate power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

@[simp]
/-
**MvPolynomial.coeToMvPowerSeries.algHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial.coeToMvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (φ : MvPolynomial 
σ R) (A : Type u_3) [inst_1 : CommSemiring A]   [inst_2 : Algebra R A], (MvPolyn
omial.coeToMvPowerSeries.algHom A) φ = (MvPowerSeries.map (algebraMap R A)) ↑φ
参数：φ : MvPolynomial σ R；A : Type u_3；MvPolynomial.coeToMvPowerSeries.algHom A；Mv
PowerSeries.map (algebraMap R A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToMvPowerSeries.algHom_apply :
    coeToMvPowerSeries.algHom A φ = MvPowerSeries.map (algebraMap R A) ↑φ :=
  rfl
/-
**MvPolynomial._root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one** 是 Mathlib
 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one
    {A : Type*} [CommSemiring A] [Algebra A R] (e : σ →₀ ℕ) (a : σ → A) :
    e.prod (fun s n ↦ ((a s • MvPowerSeries.X s) ^ n))
      = (e.prod fun s n ↦ (a s) ^ n) • MvPowerSeries.monomial (R := R) e 1 := by
  rw [Finsupp.prod_congr
    (g2 := fun s n ↦ ((MvPowerSeries.C (algebraMap A R (a s)) * (MvPowerSeries.X s)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f =
      MvPowerSeries.C ((algebraMap A R) a) * f := by
      rw [← MvPowerSeries.smul_eq_C_mul, IsScalarTower.algebraMap_smul]
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow, ← MvPowerSeries.monomial_one_eq, this]
    simp only [map_finsuppProd, map_pow]
  · intro x _
    rw [algebra_compatible_smul R, MvPowerSeries.smul_eq_C_mul]
/-
**MvPolynomial._root_.MvPowerSeries.monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_eq (e : σ →₀ ℕ) (r : σ → R) :
    MvPowerSeries.monomial e (e.prod (fun s n => r s ^ n))
      = e.prod fun s e => (r s • MvPowerSeries.X s) ^ e := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
/-
**MvPolynomial._root_.MvPowerSeries.monomial_smul_const** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.monomial_smul_const
    {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial e (r ^ (e.sum fun _ n => n))
      = (e.prod fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : MvPowerSeries σ R)

/-
**MvPowerSeries.algebraMvPolynomial** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
形式化陈述：algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom
/-
**MvPowerSeries.algebraMvPowerSeries** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
形式化陈述：algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map (algebraMap R A)).toAlgebra

variable (A)
/-
**MvPowerSeries.algebraMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：algebraMap_apply' (p : MvPolynomial σ R) : algebraMap (MvPolynomial σ R) (
MvPowerSeries σ A) p = map (algebraMap R A) p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map (algebraMap R A) p :=
  rfl
/-
**MvPowerSeries.algebraMap_apply''** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：algebraMap_apply'' : algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f 
= map (algebraMap R A) f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply'' :
    algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map (algebraMap R A) f :=
  rfl

end MvPowerSeries

end

