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

/--
Definition of `MvPowerSeries` / `MvPowerSeries` 的定义

English:
definition MvPowerSeries
  signature: (σ : Type*) (R : Type*)
  body: (σ ->₀ Nat) -> R

中文:
定义 MvPowerSeries
  签名: (σ : 类型) (R : 类型)
  定义体: (σ ->₀ Nat) -> R
-/
def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ ->₀ Nat) -> R

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: R] : Inhabited (MvPowerSeries σ R)
  body: inferInstanceAs Inhabited ((σ ->₀ Nat) -> R)

中文:
实例 [Inhabited
  签名: R] : Inhabited (MvPowerSeries σ R)
  定义体: inferInstanceAs Inhabited ((σ ->₀ Nat) -> R)

Depends on / 依赖: Inhabited
-/
instance [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
inferInstanceAs Inhabited ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : Zero (MvPowerSeries σ R)
  body: inferInstanceAs Zero ((σ ->₀ Nat) -> R)

中文:
实例 [Zero
  签名: R] : Zero (MvPowerSeries σ R)
  定义体: inferInstanceAs Zero ((σ ->₀ Nat) -> R)
-/
instance [Zero R] : Zero (MvPowerSeries σ R) :=
inferInstanceAs Zero ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] : AddMonoid (MvPowerSeries σ R)
  body: inferInstanceAs AddMonoid ((σ ->₀ Nat) -> R)

中文:
实例 [AddMonoid
  签名: R] : AddMonoid (MvPowerSeries σ R)
  定义体: inferInstanceAs AddMonoid ((σ ->₀ Nat) -> R)

Depends on / 依赖: AddMonoid
-/
instance [AddMonoid R] : AddMonoid (MvPowerSeries σ R) :=
inferInstanceAs AddMonoid ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] : AddGroup (MvPowerSeries σ R)
  body: inferInstanceAs AddGroup ((σ ->₀ Nat) -> R)

中文:
实例 [AddGroup
  签名: R] : AddGroup (MvPowerSeries σ R)
  定义体: inferInstanceAs AddGroup ((σ ->₀ Nat) -> R)

Depends on / 依赖: AddGroup
-/
instance [AddGroup R] : AddGroup (MvPowerSeries σ R) :=
inferInstanceAs AddGroup ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: R] : AddCommMonoid (MvPowerSeries σ R)
  body: inferInstanceAs AddCommMonoid ((σ ->₀ Nat) -> R)

中文:
实例 [AddCommMonoid
  签名: R] : AddCommMonoid (MvPowerSeries σ R)
  定义体: inferInstanceAs AddCommMonoid ((σ ->₀ Nat) -> R)

Depends on / 依赖: AddCommMonoid
-/
instance [AddCommMonoid R] : AddCommMonoid (MvPowerSeries σ R) :=
inferInstanceAs AddCommMonoid ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : AddCommGroup (MvPowerSeries σ R)
  body: inferInstanceAs AddCommGroup ((σ ->₀ Nat) -> R)

中文:
实例 [AddCommGroup
  签名: R] : AddCommGroup (MvPowerSeries σ R)
  定义体: inferInstanceAs AddCommGroup ((σ ->₀ Nat) -> R)

Depends on / 依赖: AddCommGroup
-/
instance [AddCommGroup R] : AddCommGroup (MvPowerSeries σ R) :=
inferInstanceAs AddCommGroup ((σ ->₀ Nat) -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (MvPowerSeries σ R)
  body: inferInstanceAs Nontrivial ((σ ->₀ Nat) -> R)

中文:
实例 [Nontrivial
  签名: R] : Nontrivial (MvPowerSeries σ R)
  定义体: inferInstanceAs Nontrivial ((σ ->₀ Nat) -> R)

Depends on / 依赖: Nontrivial
-/
instance [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
inferInstanceAs Nontrivial ((σ ->₀ Nat) -> R)

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R (MvPowerSeries σ A) :=
inferInstanceAs Module R ((σ ->₀ Nat) -> A)

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
inferInstanceAs IsScalarTower R S ((σ ->₀ Nat) -> A)

section Semiring

variable [Semiring R]

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: (n : σ ->₀ Nat)
  body: letI := Classical.decEq σ
  LinearMap.single R (fun _ => R) n

中文:
定义 monomial
  签名: (n : σ ->₀ 自然数)
  定义体: letI := Classical.decEq σ
  LinearMap.single R (fun _ => R) n

Depends on / 依赖: Classical, Classical.decEq, LinearMap, LinearMap.single, single
-/
def monomial (n : σ ->₀ Nat) : R ->ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.single R (fun _ => R) n

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (n : σ ->₀ Nat)
  body: LinearMap.proj n

中文:
定义 coeff
  签名: (n : σ ->₀ 自然数)
  定义体: LinearMap.proj n

Depends on / 依赖: LinearMap, LinearMap.proj
-/
def coeff (n : σ ->₀ Nat) : MvPowerSeries σ R ->ₗ[R] R :=
  LinearMap.proj n

/--
theorem `coeff_apply` / 定理 `coeff_apply`

English:
theorem coeff_apply
  given: (f : MvPowerSeries σ R) (d : σ ->₀ Nat)
  statement: coeff d f = f d
  proof: rfl

中文:
定理 coeff_apply
  条件: (f : MvPowerSeries σ R) (d : σ ->₀ 自然数)
  结论: coeff d f = f d
  证明: rfl
-/
theorem coeff_apply (f : MvPowerSeries σ R) (d : σ ->₀ Nat) : coeff d f = f d :=
  rfl

/-- Two multivariate formal power series are equal if all their coefficients are equal. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ Nat, coeff n φ = coeff n ψ)
  statement: φ = ψ
  proof: funext h

中文:
定理 ext
  条件: {φ ψ : MvPowerSeries σ R} (h : 对任意 n : σ ->₀ 自然数, coeff n φ = coeff n ψ)
  结论: φ = ψ
  证明: funext h
-/
theorem ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ Nat, coeff n φ = coeff n ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
if and only if all their coefficients are equal. -/
add_decl_doc MvPowerSeries.ext_iff

set_option backward.isDefEq.respectTransparency false in
/--
theorem `monomial_def` / 定理 `monomial_def`

English:
theorem monomial_def
  given: [DecidableEq σ] (n : σ ->₀ Nat)
  proof: by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert! rfl

中文:
定理 monomial_def
  条件: [DecidableEq σ] (n : σ ->₀ 自然数)
  证明: by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert! rfl

Depends on / 依赖: monomial
-/
theorem monomial_def [DecidableEq σ] (n : σ ->₀ Nat) :
    monomial n = LinearMap.single R (fun _ => R) n := by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_monomial` / 定理 `coeff_monomial`

English:
theorem coeff_monomial
  given: [DecidableEq σ] (m n : σ ->₀ Nat) (a : R)
  proof: by
  dsimp only [coeff, MvPowerSeries]
  rw [monomial_def]; rw [LinearMap.proj_apply (i := m)]; rw [LinearMap.single_apply]; rw [Pi.single_apply]

@[simp]

中文:
定理 coeff_monomial
  条件: [DecidableEq σ] (m n : σ ->₀ 自然数) (a : R)
  证明: by
  dsimp only [coeff, MvPowerSeries]
  rw [monomial_def]; rw [LinearMap.proj_apply (i := m)]; rw [LinearMap.single_apply]; rw [Pi.single_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.proj_apply, LinearMap.single_apply, MvPowerSeries, Pi.single_apply, monomial_def, proj_apply, single_apply
-/
theorem coeff_monomial [DecidableEq σ] (m n : σ ->₀ Nat) (a : R) :
    coeff m (monomial n a) = if m = n then a else 0 := by
  dsimp only [coeff, MvPowerSeries]
  rw [monomial_def]; rw [LinearMap.proj_apply (i := m)]; rw [LinearMap.single_apply]; rw [Pi.single_apply]

@[simp]
/--
theorem `coeff_monomial_same` / 定理 `coeff_monomial_same`

English:
theorem coeff_monomial_same
  given: (n : σ ->₀ Nat) (a : R)
  statement: coeff n (monomial n a) = a
  proof: by
  classical
  rw [monomial_def]
  exact Pi.single_eq_same _ _

中文:
定理 coeff_monomial_same
  条件: (n : σ ->₀ 自然数) (a : R)
  结论: coeff n (monomial n a) = a
  证明: by
  classical
  rw [monomial_def]
  exact Pi.single_eq_same _ _

Depends on / 依赖: Pi.single_eq_same, classical, monomial_def, single_eq_same
-/
theorem coeff_monomial_same (n : σ ->₀ Nat) (a : R) : coeff n (monomial n a) = a := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_same _ _

/--
theorem `coeff_monomial_ne` / 定理 `coeff_monomial_ne`

English:
theorem coeff_monomial_ne
  given: {m n : σ ->₀ Nat} (h : m != n) (a : R)
  statement: coeff m (monomial n a) = 0
  proof: by
  classical
  rw [monomial_def]
  exact Pi.single_eq_of_ne h _

中文:
定理 coeff_monomial_ne
  条件: {m n : σ ->₀ 自然数} (h : m != n) (a : R)
  结论: coeff m (monomial n a) = 0
  证明: by
  classical
  rw [monomial_def]
  exact Pi.single_eq_of_ne h _

Depends on / 依赖: Pi.single_eq_of_ne, classical, monomial_def, single_eq_of_ne
-/
theorem coeff_monomial_ne {m n : σ ->₀ Nat} (h : m != n) (a : R) : coeff m (monomial n a) = 0 := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_of_ne h _

/--
theorem `eq_of_coeff_monomial_ne_zero` / 定理 `eq_of_coeff_monomial_ne_zero`

English:
theorem eq_of_coeff_monomial_ne_zero
  given: {m n : σ ->₀ Nat} {a : R} (h : coeff m (monomial n a) != 0)
  proof: by_contra fun h' => h coeff_monomial_ne h' a

@[simp]

中文:
定理 eq_of_coeff_monomial_ne_zero
  条件: {m n : σ ->₀ 自然数} {a : R} (h : coeff m (monomial n a) != 0)
  证明: by_contra fun h' => h coeff_monomial_ne h' a

@[simp]

Depends on / 依赖: coeff_monomial_ne
-/
theorem eq_of_coeff_monomial_ne_zero {m n : σ ->₀ Nat} {a : R} (h : coeff m (monomial n a) != 0) :
    m = n :=
by_contra fun h' => h coeff_monomial_ne h' a

@[simp]
/--
theorem `coeff_comp_monomial` / 定理 `coeff_comp_monomial`

English:
theorem coeff_comp_monomial
  given: (n : σ ->₀ Nat)
  statement: (coeff (R := R) n).comp (monomial n) = LinearMap.id
  proof: LinearMap.ext coeff_monomial_same n

@[simp]

中文:
定理 coeff_comp_monomial
  条件: (n : σ ->₀ 自然数)
  结论: (coeff (R := R) n).comp (monomial n) = LinearMap.id
  证明: LinearMap.ext coeff_monomial_same n

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id, monomial
-/
theorem coeff_comp_monomial (n : σ ->₀ Nat) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
LinearMap.ext coeff_monomial_same n

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  given: (n : σ ->₀ Nat)
  statement: coeff n (0 : MvPowerSeries σ R) = 0
  proof: rfl

中文:
定理 coeff_zero
  条件: (n : σ ->₀ 自然数)
  结论: coeff n (0 : MvPowerSeries σ R) = 0
  证明: rfl
-/
theorem coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPowerSeries σ R) = 0 :=
  rfl

/--
theorem `eq_zero_iff_forall_coeff_zero` / 定理 `eq_zero_iff_forall_coeff_zero`

English:
theorem eq_zero_iff_forall_coeff_zero
  given: {f : MvPowerSeries σ R}
  proof: MvPowerSeries.ext_iff

中文:
定理 eq_zero_iff_forall_coeff_zero
  条件: {f : MvPowerSeries σ R}
  证明: MvPowerSeries.ext_iff

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext_iff, ext_iff
-/
theorem eq_zero_iff_forall_coeff_zero {f : MvPowerSeries σ R} :
    f = 0 ↔ (forall d : σ ->₀ Nat, coeff d f = 0) :=
  MvPowerSeries.ext_iff

/--
theorem `ne_zero_iff_exists_coeff_ne_zero` / 定理 `ne_zero_iff_exists_coeff_ne_zero`

English:
theorem ne_zero_iff_exists_coeff_ne_zero
  given: (f : MvPowerSeries σ R)
  proof: by
  simp only [MvPowerSeries.ext_iff, ne_eq, coeff_zero, not_forall]

中文:
定理 ne_zero_iff_exists_coeff_ne_zero
  条件: (f : MvPowerSeries σ R)
  证明: by
  simp only [MvPowerSeries.ext_iff, ne_eq, coeff_zero, not_forall]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext_iff, coeff_zero, ext_iff, ne_eq, not_forall
-/
theorem ne_zero_iff_exists_coeff_ne_zero (f : MvPowerSeries σ R) :
    f != 0 ↔ (exists d : σ ->₀ Nat, coeff d f != 0) := by
  simp only [MvPowerSeries.ext_iff, ne_eq, coeff_zero, not_forall]

variable (m n : σ ->₀ Nat) (φ ψ : MvPowerSeries σ R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (MvPowerSeries σ R)
  body: ⟨monomial (0 : σ ->₀ Nat) 1⟩

中文:
实例 :
  签名: One (MvPowerSeries σ R)
  定义体: ⟨monomial (0 : σ ->₀ Nat) 1⟩

Depends on / 依赖: monomial
-/
instance : One (MvPowerSeries σ R) :=
  ⟨monomial (0 : σ ->₀ Nat) 1⟩

/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: [DecidableEq σ]
  statement: coeff n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0
  proof: coeff_monomial _ _ _

中文:
定理 coeff_one
  条件: [DecidableEq σ]
  结论: coeff n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0
  证明: coeff_monomial _ _ _

Depends on / 依赖: coeff_monomial
-/
theorem coeff_one [DecidableEq σ] : coeff n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _

/--
theorem `coeff_zero_one` / 定理 `coeff_zero_one`

English:
theorem coeff_zero_one
  statement: coeff (R := R) (0 : σ ->₀ Nat) 1 = 1
  proof: coeff_monomial_same 0 1

中文:
定理 coeff_zero_one
  结论: coeff (R := R) (0 : σ ->₀ 自然数) 1 = 1
  证明: coeff_monomial_same 0 1
-/
theorem coeff_zero_one : coeff (R := R) (0 : σ ->₀ Nat) 1 = 1 :=
  coeff_monomial_same 0 1

/--
theorem `monomial_zero_one` / 定理 `monomial_zero_one`

English:
theorem monomial_zero_one
  statement: monomial (R := R) (0 : σ ->₀ Nat) 1 = 1
  proof: rfl

中文:
定理 monomial_zero_one
  结论: monomial (R := R) (0 : σ ->₀ 自然数) 1 = 1
  证明: rfl
-/
theorem monomial_zero_one : monomial (R := R) (0 : σ ->₀ Nat) 1 = 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoidWithOne (MvPowerSeries σ R)
  body: fun n => monomial 0 n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := by simp [Nat.cast, monomial_zero_one]

中文:
实例 :
  签名: AddMonoidWithOne (MvPowerSeries σ R)
  定义体: fun n => monomial 0 n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := by simp [Nat.cast, monomial_zero_one]

Depends on / 依赖: monomial
-/
instance : AddMonoidWithOne (MvPowerSeries σ R) where
  natCast := fun n => monomial 0 n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := by simp [Nat.cast, monomial_zero_one]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (MvPowerSeries σ R)
  body: letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ⟩

中文:
实例 :
  签名: Mul (MvPowerSeries σ R)
  定义体: letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ⟩

Depends on / 依赖: Classical, Classical.decEq, antidiagonal
-/
instance : Mul (MvPowerSeries σ R) :=
  letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ⟩

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  given: [DecidableEq σ]
  proof: by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

中文:
定理 coeff_mul
  条件: [DecidableEq σ]
  证明: by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Finset, Finset.sum_congr, Subsingleton, Subsingleton.elim, sum_congr
-/
theorem coeff_mul [DecidableEq σ] :
    coeff n (φ * ψ) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  statement: (0 : MvPowerSeries σ R) * φ = 0
  proof: ext fun n => by classical simp [coeff_mul]

中文:
定理 zero_mul
  结论: (0 : MvPowerSeries σ R) * φ = 0
  证明: ext fun n => by classical simp [coeff_mul]
-/
protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by classical simp [coeff_mul]

/--
theorem `mul_zero` / 定理 `mul_zero`

English:
theorem mul_zero
  statement: φ * 0 = 0
  proof: ext fun n => by classical simp [coeff_mul]

中文:
定理 mul_zero
  结论: φ * 0 = 0
  证明: ext fun n => by classical simp [coeff_mul]
-/
protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by classical simp [coeff_mul]

/--
theorem `coeff_monomial_mul` / 定理 `coeff_monomial_mul`

English:
theorem coeff_monomial_mul
  given: (a : R)
  proof: by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 (monomial n a) * coeff p.2 φ != 0 -> p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiago

中文:
定理 coeff_monomial_mul
  条件: (a : R)
  证明: by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 (monomial n a) * coeff p.2 φ != 0 -> p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiago

Depends on / 依赖: Finset, Finset.HasAntidiagonal.filter_fst_eq_antidiagonal, Finset.sum_empty, Finset.sum_filter_of_ne, Finset.sum_ite_index, Finset.sum_singleton, HasAntidiagonal, antidiagonal, classical, coeff_monomial_same, coeff_mul, eq_of_coeff_monomial_ne_zero, filter_fst_eq_antidiagonal, left_ne_zero_of_mul, monomial, sum_empty, sum_filter_of_ne, sum_ite_index, sum_singleton
-/
theorem coeff_monomial_mul (a : R) :
    coeff m (monomial n a * φ) = if n <= m then a * coeff (m - n) φ else 0 := by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 (monomial n a) * coeff p.2 φ != 0 -> p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiagonal.filter_fst_eq_antidiagonal
    _ n]; rw [Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

/--
theorem `coeff_mul_monomial` / 定理 `coeff_mul_monomial`

English:
theorem coeff_mul_monomial
  given: (a : R)
  proof: by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 φ * coeff p.2 (monomial n a) != 0 -> p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiag

中文:
定理 coeff_mul_monomial
  条件: (a : R)
  证明: by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 φ * coeff p.2 (monomial n a) != 0 -> p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiag

Depends on / 依赖: Finset, Finset.HasAntidiagonal.filter_snd_eq_antidiagonal, Finset.sum_empty, Finset.sum_filter_of_ne, Finset.sum_ite_index, Finset.sum_singleton, HasAntidiagonal, antidiagonal, classical, coeff_monomial_same, coeff_mul, eq_of_coeff_monomial_ne_zero, filter_snd_eq_antidiagonal, monomial, right_ne_zero_of_mul, sum_empty, sum_filter_of_ne, sum_ite_index, sum_singleton
-/
theorem coeff_mul_monomial (a : R) :
    coeff m (φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0 := by
  classical
  have :
    forall p in antidiagonal m,
      coeff (p : (σ ->₀ Nat) × (σ ->₀ Nat)).1 φ * coeff p.2 (monomial n a) != 0 -> p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul]; rw [← Finset.sum_filter_of_ne this]; rw [Finset.HasAntidiagonal.filter_snd_eq_antidiagonal
    _ n]; rw [Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

/--
theorem `coeff_add_monomial_mul` / 定理 `coeff_add_monomial_mul`

English:
theorem coeff_add_monomial_mul
  given: (a : R)
  proof: by
  rw [coeff_monomial_mul]; rw [if_pos]; rw [add_tsub_cancel_left]
  exact le_add_right le_rfl

中文:
定理 coeff_add_monomial_mul
  条件: (a : R)
  证明: by
  rw [coeff_monomial_mul]; rw [if_pos]; rw [add_tsub_cancel_left]
  exact le_add_right le_rfl

Depends on / 依赖: add_tsub_cancel_left, coeff_monomial_mul, if_pos, le_add_right, le_rfl
-/
theorem coeff_add_monomial_mul (a : R) :
    coeff (m + n) (monomial m a * φ) = a * coeff n φ := by
  rw [coeff_monomial_mul]; rw [if_pos]; rw [add_tsub_cancel_left]
  exact le_add_right le_rfl

/--
theorem `coeff_add_mul_monomial` / 定理 `coeff_add_mul_monomial`

English:
theorem coeff_add_mul_monomial
  given: (a : R)
  proof: by
  rw [coeff_mul_monomial]; rw [if_pos]; rw [add_tsub_cancel_right]
  exact le_add_left le_rfl

@[simp]

中文:
定理 coeff_add_mul_monomial
  条件: (a : R)
  证明: by
  rw [coeff_mul_monomial]; rw [if_pos]; rw [add_tsub_cancel_right]
  exact le_add_left le_rfl

@[simp]

Depends on / 依赖: add_tsub_cancel_right, coeff_mul_monomial, if_pos, le_add_left, le_rfl
-/
theorem coeff_add_mul_monomial (a : R) :
    coeff (m + n) (φ * monomial n a) = coeff m φ * a := by
  rw [coeff_mul_monomial]; rw [if_pos]; rw [add_tsub_cancel_right]
  exact le_add_left le_rfl

@[simp]
/--
theorem `commute_monomial` / 定理 `commute_monomial`

English:
theorem commute_monomial
  given: {a : R} {n}
  proof: by
  rw [commute_iff_eq]; rw [MvPowerSeries.ext_iff]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]

中文:
定理 commute_monomial
  条件: {a : R} {n}
  证明: by
  rw [commute_iff_eq]; rw [MvPowerSeries.ext_iff]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext_iff, add_comm, coeff_add_monomial_mul, coeff_add_mul_monomial, coeff_monomial_mul, coeff_mul_monomial, commute_iff_eq, ext_iff, split_ifs
-/
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial n a) ↔ forall m, Commute (coeff m φ) a := by
  rw [commute_iff_eq]; rw [MvPowerSeries.ext_iff]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  statement: (1 : MvPowerSeries σ R) * φ = φ
  proof: ext fun n => by simpa using! coeff_add_monomial_mul 0 n φ 1

中文:
定理 one_mul
  结论: (1 : MvPowerSeries σ R) * φ = φ
  证明: ext fun n => by simpa using! coeff_add_monomial_mul 0 n φ 1
-/
protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using! coeff_add_monomial_mul 0 n φ 1

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  statement: φ * 1 = φ
  proof: ext fun n => by simpa using! coeff_add_mul_monomial n 0 φ 1

中文:
定理 mul_one
  结论: φ * 1 = φ
  证明: ext fun n => by simpa using! coeff_add_mul_monomial n 0 φ 1
-/
protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using! coeff_add_mul_monomial n 0 φ 1

/--
theorem `mul_add` / 定理 `mul_add`

English:
theorem mul_add
  given: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  statement: φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃
  proof: ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, map_add]

中文:
定理 mul_add
  条件: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  结论: φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃
  证明: ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, map_add]
-/
protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, map_add]

/--
theorem `add_mul` / 定理 `add_mul`

English:
theorem add_mul
  given: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  statement: (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃
  proof: ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, map_add]

中文:
定理 add_mul
  条件: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  结论: (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃
  证明: ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, map_add]
-/
protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, map_add]

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  statement: φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃)
  proof: by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

中文:
定理 mul_assoc
  条件: (φ₁ φ₂ φ₃ : MvPowerSeries σ R)
  结论: φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃)
  证明: by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])
-/
protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (MvPowerSeries σ R)
  body: MvPowerSeries.mul_one
  one_mul := MvPowerSeries.one_mul
  mul_assoc := MvPowerSeries.mul_assoc
  mul_zero := MvPowerSeries.mul_zero
  zero_mul := MvPowerSeries.zero_mul
  left_distrib := MvPowerSeries.mul_add
  right_distrib := MvPowerSeries.add_mul

中文:
实例 :
  签名: Semiring (MvPowerSeries σ R)
  定义体: MvPowerSeries.mul_one
  one_mul := MvPowerSeries.one_mul
  mul_assoc := MvPowerSeries.mul_assoc
  mul_zero := MvPowerSeries.mul_zero
  zero_mul := MvPowerSeries.zero_mul
  left_distrib := MvPowerSeries.mul_add
  right_distrib := MvPowerSeries.add_mul

Depends on / 依赖: MvPowerSeries, MvPowerSeries.mul_one, mul_one
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : CommSemiring (MvPowerSeries σ R) where
  body: fun φ ψ =>
    ext fun n => by
      classical
      simpa only [coeff_mul, mul_comm] using
        sum_antidiagonal_swap n fun a b => coeff a φ * coeff b ψ

中文:
实例 [CommSemiring
  签名: R] : CommSemiring (MvPowerSeries σ R) where
  定义体: fun φ ψ =>
    ext fun n => by
      classical
      simpa only [coeff_mul, mul_comm] using
        sum_antidiagonal_swap n fun a b => coeff a φ * coeff b ψ
-/
instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R) where
  mul_comm := fun φ ψ =>
    ext fun n => by
      classical
      simpa only [coeff_mul, mul_comm] using
        sum_antidiagonal_swap n fun a b => coeff a φ * coeff b ψ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] : Ring (MvPowerSeries σ R) where

中文:
实例 [Ring
  签名: R] : Ring (MvPowerSeries σ R) where
-/
instance [Ring R] : Ring (MvPowerSeries σ R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : CommRing (MvPowerSeries σ R) where

中文:
实例 [CommRing
  签名: R] : CommRing (MvPowerSeries σ R) where
-/
instance [CommRing R] : CommRing (MvPowerSeries σ R) where

section Semiring

variable [Semiring R]

/--
theorem `monomial_mul_monomial` / 定理 `monomial_mul_monomial`

English:
theorem monomial_mul_monomial
  given: (m n : σ ->₀ Nat) (a b : R)
  proof: by
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
    exact 

中文:
定理 monomial_mul_monomial
  条件: (m n : σ ->₀ 自然数) (a b : R)
  证明: by
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
    exact 

Depends on / 依赖: add_tsub_cancel_right, classical, coeff_monomial, coeff_mul_monomial, le_add_left, le_rfl, split_ifs, tsub_add_cancel_of_le, zero_mul
-/
theorem monomial_mul_monomial (m n : σ ->₀ Nat) (a b : R) :
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

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* MvPowerSeries σ R
  body: { monomial (0 : σ ->₀ Nat) with
    map_one' := rfl
    map_mul' := fun a b => Eq.trans (by simp) (monomial_mul_monomial _ _ a b).symm
    map_zero' := (monomial 0).map_zero }

@[simp]

中文:
定义 C
  签名: : R ->+* MvPowerSeries σ R
  定义体: { monomial (0 : σ ->₀ Nat) with
    map_one' := rfl
    map_mul' := fun a b => Eq.trans (by simp) (monomial_mul_monomial _ _ a b).symm
    map_zero' := (monomial 0).map_zero }

@[simp]

Depends on / 依赖: Eq.trans, map_mul, map_one, map_zero, monomial, monomial_mul_monomial
-/
def C : R ->+* MvPowerSeries σ R :=
  { monomial (0 : σ ->₀ Nat) with
    map_one' := rfl
    map_mul' := fun a b => Eq.trans (by simp) (monomial_mul_monomial _ _ a b).symm
    map_zero' := (monomial 0).map_zero }

@[simp]
/--
theorem `monomial_zero_eq_C` / 定理 `monomial_zero_eq_C`

English:
theorem monomial_zero_eq_C
  statement: ⇑(monomial (R := R) (0 : σ ->₀ Nat)) = C
  proof: rfl

中文:
定理 monomial_zero_eq_C
  结论: ⇑(monomial (R := R) (0 : σ ->₀ 自然数)) = C
  证明: rfl
-/
theorem monomial_zero_eq_C : ⇑(monomial (R := R) (0 : σ ->₀ Nat)) = C :=
  rfl

/--
theorem `monomial_zero_eq_C_apply` / 定理 `monomial_zero_eq_C_apply`

English:
theorem monomial_zero_eq_C_apply
  given: (a : R)
  statement: monomial (0 : σ ->₀ Nat) a = C a
  proof: rfl

中文:
定理 monomial_zero_eq_C_apply
  条件: (a : R)
  结论: monomial (0 : σ ->₀ 自然数) a = C a
  证明: rfl
-/
theorem monomial_zero_eq_C_apply (a : R) : monomial (0 : σ ->₀ Nat) a = C a :=
  rfl

/--
theorem `coeff_C` / 定理 `coeff_C`

English:
theorem coeff_C
  given: [DecidableEq σ] (n : σ ->₀ Nat) (a : R)
  proof: coeff_monomial _ _ _

中文:
定理 coeff_C
  条件: [DecidableEq σ] (n : σ ->₀ 自然数) (a : R)
  证明: coeff_monomial _ _ _

Depends on / 依赖: coeff_monomial
-/
theorem coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
    coeff n (C a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _

/--
theorem `coeff_zero_C` / 定理 `coeff_zero_C`

English:
theorem coeff_zero_C
  given: (a : R)
  statement: coeff (0 : σ ->₀ Nat) (C a) = a
  proof: coeff_monomial_same 0 a

中文:
定理 coeff_zero_C
  条件: (a : R)
  结论: coeff (0 : σ ->₀ 自然数) (C a) = a
  证明: coeff_monomial_same 0 a

Depends on / 依赖: coeff_monomial_same
-/
theorem coeff_zero_C (a : R) : coeff (0 : σ ->₀ Nat) (C a) = a :=
  coeff_monomial_same 0 a

/--
theorem `coeff_C_of_ne_zero` / 定理 `coeff_C_of_ne_zero`

English:
theorem coeff_C_of_ne_zero
  given: {n : σ ->₀ Nat} (h : n != 0) (a : R)
  statement: coeff n (C a) = 0
  proof: by
  classical rw [coeff_C, if_neg h]

中文:
定理 coeff_C_of_ne_zero
  条件: {n : σ ->₀ 自然数} (h : n != 0) (a : R)
  结论: coeff n (C a) = 0
  证明: by
  classical rw [coeff_C, if_neg h]

Depends on / 依赖: classical, coeff_C, if_neg
-/
theorem coeff_C_of_ne_zero {n : σ ->₀ Nat} (h : n != 0) (a : R) : coeff n (C a) = 0 := by
  classical rw [coeff_C, if_neg h]

-- The intended use case of this theorem is for `m = 1` (often useful for `pderiv`).
@[simp]
/--
theorem `coeff_add_single_C` / 定理 `coeff_add_single_C`

English:
theorem coeff_add_single_C
  given: {m : Nat} [NeZero m] {n : σ ->₀ Nat} (a : R) (i : σ)
  proof: coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

@[grind inj]

中文:
定理 coeff_add_single_C
  条件: {m : 自然数} [NeZero m] {n : σ ->₀ 自然数} (a : R) (i : σ)
  证明: coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

@[grind inj]

Depends on / 依赖: NeZero, NeZero.ne, coeff_C_of_ne_zero
-/
theorem coeff_add_single_C {m : Nat} [NeZero m] {n : σ ->₀ Nat} (a : R) (i : σ) :
    coeff (n + single i m) (C a) = 0 :=
  coeff_C_of_ne_zero (fun H => by simpa [NeZero.ne] using congr($(H) i)) a

@[grind inj]
/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  statement: Function.Injective (C : R -> MvPowerSeries σ R)
  proof: by
  intro a b h
  rw [← coeff_zero_C a]; rw [h]; rw [coeff_zero_C]

中文:
定理 C_injective
  结论: Function.Injective (C : R -> MvPowerSeries σ R)
  证明: by
  intro a b h
  rw [← coeff_zero_C a]; rw [h]; rw [coeff_zero_C]

Depends on / 依赖: coeff_zero_C
-/
theorem C_injective : Function.Injective (C : R -> MvPowerSeries σ R) := by
  intro a b h
  rw [← coeff_zero_C a]; rw [h]; rw [coeff_zero_C]

/--
theorem `C_surjective` / 定理 `C_surjective`

English:
theorem C_surjective
  given: [IsEmpty σ]
  statement: Function.Surjective (C : R -> MvPowerSeries σ R)
  proof: fun p => ⟨p 0, by ext n; simpa [coeff_C, Subsingleton.eq_zero n] using! coeff_apply _ _⟩

中文:
定理 C_surjective
  条件: [IsEmpty σ]
  结论: Function.Surjective (C : R -> MvPowerSeries σ R)
  证明: fun p => ⟨p 0, by ext n; simpa [coeff_C, Subsingleton.eq_zero n] using! coeff_apply _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, coeff_C, coeff_apply, eq_zero
-/
theorem C_surjective [IsEmpty σ] : Function.Surjective (C : R -> MvPowerSeries σ R) :=
  fun p => ⟨p 0, by ext n; simpa [coeff_C, Subsingleton.eq_zero n] using! coeff_apply _ _⟩

/--
theorem `C_inj` / 定理 `C_inj`

English:
theorem C_inj
  given: (r s : R)
  statement: (C r : MvPowerSeries σ R) = C s ↔ r = s
  proof: (C_injective).eq_iff

中文:
定理 C_inj
  条件: (r s : R)
  结论: (C r : MvPowerSeries σ R) = C s ↔ r = s
  证明: (C_injective).eq_iff
-/
@[simp] theorem C_inj (r s : R) : (C r : MvPowerSeries σ R) = C s ↔ r = s := (C_injective).eq_iff

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: (s : σ)
  body: monomial (single s 1) 1

中文:
定义 X
  签名: (s : σ)
  定义体: monomial (single s 1) 1

Depends on / 依赖: monomial, single
-/
def X (s : σ) : MvPowerSeries σ R :=
  monomial (single s 1) 1

/--
theorem `coeff_X` / 定理 `coeff_X`

English:
theorem coeff_X
  given: [DecidableEq σ] (n : σ ->₀ Nat) (s : σ)
  proof: coeff_monomial _ _ _

中文:
定理 coeff_X
  条件: [DecidableEq σ] (n : σ ->₀ 自然数) (s : σ)
  证明: coeff_monomial _ _ _

Depends on / 依赖: coeff_monomial
-/
theorem coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
    coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _

/--
theorem `coeff_index_single_X` / 定理 `coeff_index_single_X`

English:
theorem coeff_index_single_X
  given: [DecidableEq σ] (s t : σ)
  proof: by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : Nat) != 0)]

@[simp]

中文:
定理 coeff_index_single_X
  条件: [DecidableEq σ] (s t : σ)
  证明: by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : Nat) != 0)]

@[simp]

Depends on / 依赖: coeff_X, one_ne_zero, single_left_inj
-/
theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : Nat) != 0)]

@[simp]
/--
theorem `coeff_index_single_self_X` / 定理 `coeff_index_single_self_X`

English:
theorem coeff_index_single_self_X
  given: (s : σ)
  statement: coeff (single s 1) (X s : MvPowerSeries σ R) = 1
  proof: coeff_monomial_same _ _

中文:
定理 coeff_index_single_self_X
  条件: (s : σ)
  结论: coeff (single s 1) (X s : MvPowerSeries σ R) = 1
  证明: coeff_monomial_same _ _

Depends on / 依赖: coeff_monomial_same
-/
theorem coeff_index_single_self_X (s : σ) : coeff (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _

/--
theorem `coeff_zero_X` / 定理 `coeff_zero_X`

English:
theorem coeff_zero_X
  given: (s : σ)
  statement: coeff (0 : σ ->₀ Nat) (X s : MvPowerSeries σ R) = 0
  proof: by
  classical
  rw [coeff_X]; rw [if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)

中文:
定理 coeff_zero_X
  条件: (s : σ)
  结论: coeff (0 : σ ->₀ 自然数) (X s : MvPowerSeries σ R) = 0
  证明: by
  classical
  rw [coeff_X]; rw [if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)

Depends on / 依赖: classical, coeff_X, h.symm, if_neg, one_ne_zero, single_eq_zero, single_eq_zero.mp
-/
theorem coeff_zero_X (s : σ) : coeff (0 : σ ->₀ Nat) (X s : MvPowerSeries σ R) = 0 := by
  classical
  rw [coeff_X]; rw [if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)

/--
theorem `commute_X` / 定理 `commute_X`

English:
theorem commute_X
  given: (φ : MvPowerSeries σ R) (s : σ)
  statement: Commute φ (X s)
  proof: φ.commute_monomial.mpr fun _m => Commute.one_right _

中文:
定理 commute_X
  条件: (φ : MvPowerSeries σ R) (s : σ)
  结论: Commute φ (X s)
  证明: φ.commute_monomial.mpr fun _m => Commute.one_right _

Depends on / 依赖: Commute, Commute.one_right, commute_monomial, commute_monomial.mpr, one_right
-/
theorem commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s) :=
  φ.commute_monomial.mpr fun _m => Commute.one_right _

/--
theorem `X_mul` / 定理 `X_mul`

English:
theorem X_mul
  given: {φ : MvPowerSeries σ R} {s : σ}
  statement: X s * φ = φ * X s
  proof: .symm.eq φ.commute_X s

中文:
定理 X_mul
  条件: {φ : MvPowerSeries σ R} {s : σ}
  结论: X s * φ = φ * X s
  证明: .symm.eq φ.commute_X s

Depends on / 依赖: commute_X, symm.eq
-/
theorem X_mul {φ : MvPowerSeries σ R} {s : σ} : X s * φ = φ * X s :=
.symm.eq φ.commute_X s

/--
theorem `commute_X_pow` / 定理 `commute_X_pow`

English:
theorem commute_X_pow
  given: (φ : MvPowerSeries σ R) (s : σ) (n : Nat)
  statement: Commute φ (X s ^ n)
  proof: .pow_right _ φ.commute_X s

中文:
定理 commute_X_pow
  条件: (φ : MvPowerSeries σ R) (s : σ) (n : 自然数)
  结论: Commute φ (X s ^ n)
  证明: .pow_right _ φ.commute_X s

Depends on / 依赖: commute_X, pow_right
-/
theorem commute_X_pow (φ : MvPowerSeries σ R) (s : σ) (n : Nat) : Commute φ (X s ^ n) :=
.pow_right _ φ.commute_X s

/--
theorem `X_pow_mul` / 定理 `X_pow_mul`

English:
theorem X_pow_mul
  given: {φ : MvPowerSeries σ R} {s : σ} {n : Nat}
  statement: X s ^ n * φ = φ * X s ^ n
  proof: .symm.eq φ.commute_X_pow s n

中文:
定理 X_pow_mul
  条件: {φ : MvPowerSeries σ R} {s : σ} {n : 自然数}
  结论: X s ^ n * φ = φ * X s ^ n
  证明: .symm.eq φ.commute_X_pow s n

Depends on / 依赖: commute_X_pow, symm.eq
-/
theorem X_pow_mul {φ : MvPowerSeries σ R} {s : σ} {n : Nat} : X s ^ n * φ = φ * X s ^ n :=
.symm.eq φ.commute_X_pow s n

/--
theorem `X_def` / 定理 `X_def`

English:
theorem X_def
  given: (s : σ)
  statement: X s = monomial (single s 1) (1 : R)
  proof: rfl

中文:
定理 X_def
  条件: (s : σ)
  结论: X s = monomial (single s 1) (1 : R)
  证明: rfl
-/
theorem X_def (s : σ) : X s = monomial (single s 1) (1 : R) :=
  rfl

/--
theorem `X_pow_eq` / 定理 `X_pow_eq`

English:
theorem X_pow_eq
  given: (s : σ) (n : Nat)
  statement: (X s : MvPowerSeries σ R) ^ n = monomial (single s n) 1
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]

中文:
定理 X_pow_eq
  条件: (s : σ) (n : 自然数)
  结论: (X s : MvPowerSeries σ R) ^ n = monomial (single s n) 1
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]

Depends on / 依赖: Finsupp, Finsupp.single_add, monomial_mul_monomial, one_mul, pow_succ, single_add
-/
theorem X_pow_eq (s : σ) (n : Nat) : (X s : MvPowerSeries σ R) ^ n = monomial (single s n) 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]

/--
theorem `coeff_X_pow` / 定理 `coeff_X_pow`

English:
theorem coeff_X_pow
  given: [DecidableEq σ] (m : σ ->₀ Nat) (s : σ) (n : Nat)
  proof: by
  rw [X_pow_eq s n]; rw [coeff_monomial]

@[simp]

中文:
定理 coeff_X_pow
  条件: [DecidableEq σ] (m : σ ->₀ 自然数) (s : σ) (n : 自然数)
  证明: by
  rw [X_pow_eq s n]; rw [coeff_monomial]

@[simp]

Depends on / 依赖: X_pow_eq, coeff_monomial
-/
theorem coeff_X_pow [DecidableEq σ] (m : σ ->₀ Nat) (s : σ) (n : Nat) :
    coeff m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n]; rw [coeff_monomial]

@[simp]
/--
theorem `coeff_mul_C` / 定理 `coeff_mul_C`

English:
theorem coeff_mul_C
  given: (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R)
  proof: by simpa using coeff_add_mul_monomial n 0 φ a

@[simp]

中文:
定理 coeff_mul_C
  条件: (n : σ ->₀ 自然数) (φ : MvPowerSeries σ R) (a : R)
  证明: by simpa using coeff_add_mul_monomial n 0 φ a

@[simp]

Depends on / 依赖: coeff_add_mul_monomial
-/
theorem coeff_mul_C (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (φ * C a) = coeff n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a

@[simp]
/--
theorem `coeff_C_mul` / 定理 `coeff_C_mul`

English:
theorem coeff_C_mul
  given: (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R)
  proof: by simpa using coeff_add_monomial_mul 0 n φ a

中文:
定理 coeff_C_mul
  条件: (n : σ ->₀ 自然数) (φ : MvPowerSeries σ R) (a : R)
  证明: by simpa using coeff_add_monomial_mul 0 n φ a

Depends on / 依赖: coeff_add_monomial_mul
-/
theorem coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (C a * φ) = a * coeff n φ := by simpa using coeff_add_monomial_mul 0 n φ a

/--
theorem `coeff_zero_mul_X` / 定理 `coeff_zero_mul_X`

English:
theorem coeff_zero_mul_X
  given: (φ : MvPowerSeries σ R) (s : σ)
  statement: coeff (0 : σ ->₀ Nat) (φ * X s) = 0
  proof: by
  have : ¬single s 1 <= 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]

中文:
定理 coeff_zero_mul_X
  条件: (φ : MvPowerSeries σ R) (s : σ)
  结论: coeff (0 : σ ->₀ 自然数) (φ * X s) = 0
  证明: by
  have : ¬single s 1 <= 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]

Depends on / 依赖: coeff_mul_monomial, if_neg, single
-/
theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ ->₀ Nat) (φ * X s) = 0 := by
  have : ¬single s 1 <= 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]

/--
theorem `coeff_zero_X_mul` / 定理 `coeff_zero_X_mul`

English:
theorem coeff_zero_X_mul
  given: (φ : MvPowerSeries σ R) (s : σ)
  statement: coeff (0 : σ ->₀ Nat) (X s * φ) = 0
  proof: by
  rw [← (φ.commute_X s).eq]; rw [coeff_zero_mul_X]

中文:
定理 coeff_zero_X_mul
  条件: (φ : MvPowerSeries σ R) (s : σ)
  结论: coeff (0 : σ ->₀ 自然数) (X s * φ) = 0
  证明: by
  rw [← (φ.commute_X s).eq]; rw [coeff_zero_mul_X]

Depends on / 依赖: coeff_zero_mul_X, commute_X
-/
theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ ->₀ Nat) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq]; rw [coeff_zero_mul_X]

/--
Definition of `constantCoeff` / `constantCoeff` 的定义

English:
definition constantCoeff
  signature: : MvPowerSeries σ R ->+* R
  body: { coeff (0 : σ ->₀ Nat) with
    toFun := coeff (0 : σ ->₀ Nat)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul]
    map_zero' := map_zero _ }

@[simp]

中文:
定义 constantCoeff
  签名: : MvPowerSeries σ R ->+* R
  定义体: { coeff (0 : σ ->₀ Nat) with
    toFun := coeff (0 : σ ->₀ Nat)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul]
    map_zero' := map_zero _ }

@[simp]

Depends on / 依赖: classical, coeff_mul, coeff_zero_one, map_mul, map_one, map_zero
-/
def constantCoeff : MvPowerSeries σ R ->+* R :=
  { coeff (0 : σ ->₀ Nat) with
    toFun := coeff (0 : σ ->₀ Nat)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul]
    map_zero' := map_zero _ }

@[simp]
/--
theorem `coeff_zero_eq_constantCoeff` / 定理 `coeff_zero_eq_constantCoeff`

English:
theorem coeff_zero_eq_constantCoeff
  statement: ⇑(coeff (R := R) (0 : σ ->₀ Nat)) = constantCoeff
  proof: rfl

中文:
定理 coeff_zero_eq_constantCoeff
  结论: ⇑(coeff (R := R) (0 : σ ->₀ 自然数)) = constantCoeff
  证明: rfl

Depends on / 依赖: constantCoeff
-/
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) (0 : σ ->₀ Nat)) = constantCoeff :=
  rfl

/--
theorem `coeff_zero_eq_constantCoeff_apply` / 定理 `coeff_zero_eq_constantCoeff_apply`

English:
theorem coeff_zero_eq_constantCoeff_apply
  given: (φ : MvPowerSeries σ R)
  proof: rfl

@[simp]

中文:
定理 coeff_zero_eq_constantCoeff_apply
  条件: (φ : MvPowerSeries σ R)
  证明: rfl

@[simp]
-/
theorem coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) :
    coeff (0 : σ ->₀ Nat) φ = constantCoeff φ :=
  rfl

@[simp]
/--
theorem `constantCoeff_C` / 定理 `constantCoeff_C`

English:
theorem constantCoeff_C
  given: (a : R)
  statement: constantCoeff (σ := σ) (C a) = a
  proof: rfl

@[simp]

中文:
定理 constantCoeff_C
  条件: (a : R)
  结论: constantCoeff (σ := σ) (C a) = a
  证明: rfl

@[simp]
-/
theorem constantCoeff_C (a : R) : constantCoeff (σ := σ) (C a) = a :=
  rfl

@[simp]
/--
theorem `constantCoeff_comp_C` / 定理 `constantCoeff_comp_C`

English:
theorem constantCoeff_comp_C
  statement: (constantCoeff (σ := σ)).comp C = RingHom.id R
  proof: rfl

@[simp]

中文:
定理 constantCoeff_comp_C
  结论: (constantCoeff (σ := σ)).comp C = RingHom.id R
  证明: rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.id
-/
theorem constantCoeff_comp_C : (constantCoeff (σ := σ)).comp C = RingHom.id R :=
  rfl

@[simp]
/--
theorem `constantCoeff_zero` / 定理 `constantCoeff_zero`

English:
theorem constantCoeff_zero
  statement: constantCoeff (0 : MvPowerSeries σ R) = 0
  proof: rfl

@[simp]

中文:
定理 constantCoeff_zero
  结论: constantCoeff (0 : MvPowerSeries σ R) = 0
  证明: rfl

@[simp]
-/
theorem constantCoeff_zero : constantCoeff (0 : MvPowerSeries σ R) = 0 :=
  rfl

@[simp]
/--
theorem `constantCoeff_one` / 定理 `constantCoeff_one`

English:
theorem constantCoeff_one
  statement: constantCoeff (1 : MvPowerSeries σ R) = 1
  proof: rfl

@[simp]

中文:
定理 constantCoeff_one
  结论: constantCoeff (1 : MvPowerSeries σ R) = 1
  证明: rfl

@[simp]
-/
theorem constantCoeff_one : constantCoeff (1 : MvPowerSeries σ R) = 1 :=
  rfl

@[simp]
/--
theorem `constantCoeff_X` / 定理 `constantCoeff_X`

English:
theorem constantCoeff_X
  given: (s : σ)
  statement: constantCoeff (R := R) (X s) = 0
  proof: coeff_zero_X s

@[simp]

中文:
定理 constantCoeff_X
  条件: (s : σ)
  结论: constantCoeff (R := R) (X s) = 0
  证明: coeff_zero_X s

@[simp]
-/
theorem constantCoeff_X (s : σ) : constantCoeff (R := R) (X s) = 0 :=
  coeff_zero_X s

@[simp]
/--
theorem `constantCoeff_smul` / 定理 `constantCoeff_smul`

English:
theorem constantCoeff_smul
  statement: {S : Type*} [Semiring S] [Module R S]
  proof: rfl

中文:
定理 constantCoeff_smul
  结论: {S : 类型} [Semiring S] [Module R S]
  证明: rfl
-/
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ := rfl

/--
theorem `isUnit_constantCoeff` / 定理 `isUnit_constantCoeff`

English:
theorem isUnit_constantCoeff
  given: (φ : MvPowerSeries σ R) (h : IsUnit φ)
  proof: h.map _

@[simp]

中文:
定理 isUnit_constantCoeff
  条件: (φ : MvPowerSeries σ R) (h : IsUnit φ)
  证明: h.map _

@[simp]

Depends on / 依赖: h.map
-/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff φ) :=
  h.map _

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: (f : MvPowerSeries σ R) (n) (a : R)
  statement: coeff n (a • f) = a * coeff n f
  proof: rfl

中文:
定理 coeff_smul
  条件: (f : MvPowerSeries σ R) (n) (a : R)
  结论: coeff n (a • f) = a * coeff n f
  证明: rfl
-/
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff n (a • f) = a * coeff n f :=
  rfl

/--
theorem `smul_eq_C_mul` / 定理 `smul_eq_C_mul`

English:
theorem smul_eq_C_mul
  given: (f : MvPowerSeries σ R) (a : R)
  statement: a • f = C a * f
  proof: by
  ext
  simp

中文:
定理 smul_eq_C_mul
  条件: (f : MvPowerSeries σ R) (a : R)
  结论: a • f = C a * f
  证明: by
  ext
  simp
-/
theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C a * f := by
  ext
  simp

/--
theorem `X_inj` / 定理 `X_inj`

English:
theorem X_inj
  given: [Nontrivial R] {s t : σ}
  statement: (X s : MvPowerSeries σ R) = X t ↔ s = t
  proof: ⟨by
    classical
    intro h
    replace h := congr_arg (coeff (single s 1)) h
    rw [coeff_X]; rw [if_pos rfl]; rw [coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      rcases H with H | H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · 

中文:
定理 X_inj
  条件: [Nontrivial R] {s t : σ}
  结论: (X s : MvPowerSeries σ R) = X t ↔ s = t
  证明: ⟨by
    classical
    intro h
    replace h := congr_arg (coeff (single s 1)) h
    rw [coeff_X]; rw [if_pos rfl]; rw [coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      rcases H with H | H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · 

Depends on / 依赖: Finsupp, Finsupp.single_eq_single_iff, classical, coeff_X, congr_arg, if_pos, one_ne_zero, replace, single, single_eq_single_iff, split_ifs
-/
theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    classical
    intro h
    replace h := congr_arg (coeff (single s 1)) h
    rw [coeff_X]; rw [if_pos rfl]; rw [coeff_X] at h
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
variable (f : R ->+* S) (g : S ->+* T)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : MvPowerSeries σ R ->+* MvPowerSeries σ S where
  body: f coeff n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f (coeff n 1) = coeff n 1 by
        classical
        rw [coeff_one]; rw [coeff_one]
        split_ifs with h
        · simp only [map_one]
        · simp only [map_zero]
  map_add' φ ψ :=
    ext fun n =>

中文:
定义 map
  签名: : MvPowerSeries σ R ->+* MvPowerSeries σ S where
  定义体: f coeff n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f (coeff n 1) = coeff n 1 by
        classical
        rw [coeff_one]; rw [coeff_one]
        split_ifs with h
        · simp only [map_one]
        · simp only [map_zero]
  map_add' φ ψ :=
    ext fun n =>
-/
def map : MvPowerSeries σ R ->+* MvPowerSeries σ S where
toFun φ n := f coeff n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f (coeff n 1) = coeff n 1 by
        classical
        rw [coeff_one]; rw [coeff_one]
        split_ifs with h
        · simp only [map_one]
        · simp only [map_zero]
  map_add' φ ψ :=
    ext fun n => show f (coeff n (φ + ψ)) = f (coeff n φ) + f (coeff n ψ) by simp
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        classical
        rw [coeff_mul]; rw [map_sum]; rw [coeff_mul]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ _; rw [f.map_mul]; rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (σ := σ) (RingHom.id R) = RingHom.id _
  proof: rfl

中文:
定理 map_id
  结论: map (σ := σ) (RingHom.id R) = RingHom.id _
  证明: rfl

Depends on / 依赖: RingHom, RingHom.id
-/
theorem map_id : map (σ := σ) (RingHom.id R) = RingHom.id _ :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: map (σ := σ) (g.comp f) = (map g).comp (map f)
  proof: rfl

@[simp]

中文:
定理 map_comp
  结论: map (σ := σ) (g.comp f) = (map g).comp (map f)
  证明: rfl

@[simp]

Depends on / 依赖: g.comp
-/
theorem map_comp : map (σ := σ) (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
/--
theorem `coeff_map` / 定理 `coeff_map`

English:
theorem coeff_map
  given: (n : σ ->₀ Nat) (φ : MvPowerSeries σ R)
  statement: coeff n (map f φ) = f (coeff n φ)
  proof: rfl

@[simp]

中文:
定理 coeff_map
  条件: (n : σ ->₀ 自然数) (φ : MvPowerSeries σ R)
  结论: coeff n (map f φ) = f (coeff n φ)
  证明: rfl

@[simp]
-/
theorem coeff_map (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
/--
theorem `constantCoeff_map` / 定理 `constantCoeff_map`

English:
theorem constantCoeff_map
  given: (φ : MvPowerSeries σ R)
  proof: rfl

@[simp]

中文:
定理 constantCoeff_map
  条件: (φ : MvPowerSeries σ R)
  证明: rfl

@[simp]
-/
theorem constantCoeff_map (φ : MvPowerSeries σ R) :
    constantCoeff (map f φ) = f (constantCoeff φ) :=
  rfl

@[simp]
/--
theorem `map_monomial` / 定理 `map_monomial`

English:
theorem map_monomial
  given: (n : σ ->₀ Nat) (a : R)
  statement: map f (monomial n a) = monomial n (f a)
  proof: by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]

@[simp]

中文:
定理 map_monomial
  条件: (n : σ ->₀ 自然数) (a : R)
  结论: map f (monomial n a) = monomial n (f a)
  证明: by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]

@[simp]

Depends on / 依赖: apply_ite, classical, coeff_monomial
-/
theorem map_monomial (n : σ ->₀ Nat) (a : R) : map f (monomial n a) = monomial n (f a) := by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]

@[simp]
/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  given: (a : R)
  statement: map (σ := σ) f (C a) = C (f a)
  proof: map_monomial _ _ _

@[simp]

中文:
定理 map_C
  条件: (a : R)
  结论: map (σ := σ) f (C a) = C (f a)
  证明: map_monomial _ _ _

@[simp]
-/
theorem map_C (a : R) : map (σ := σ) f (C a) = C (f a) :=
  map_monomial _ _ _

@[simp]
/--
theorem `map_X` / 定理 `map_X`

English:
theorem map_X
  given: (s : σ)
  statement: map f (X s) = X s
  proof: by simp [MvPowerSeries.X]

@[simp]

中文:
定理 map_X
  条件: (s : σ)
  结论: map f (X s) = X s
  证明: by simp [MvPowerSeries.X]

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X
-/
theorem map_X (s : σ) : map f (X s) = X s := by simp [MvPowerSeries.X]

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
  proof: by
  ext n
  simp

中文:
定理 map_map
  结论: {S₁ S₂ : 类型} [CommSemiring S₁] [CommSemiring S₂]
  证明: by
  ext n
  simp
-/
theorem map_map {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (f : R ->+* S₁) (g : S₁ ->+* S₂) (p : MvPowerSeries σ R) :
    map g (map f p) = map (g.comp f) p := by
  ext n
  simp

end Map

section toSubring

variable [Ring R] (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.coeff n in T)

/--
Definition of `toSubring` / `toSubring` 的定义

English:
definition toSubring
  signature: : MvPowerSeries σ T
  body: fun n => ⟨p.coeff n, hp n⟩

@[simp]

中文:
定义 toSubring
  签名: : MvPowerSeries σ T
  定义体: fun n => ⟨p.coeff n, hp n⟩

@[simp]

Depends on / 依赖: p.coeff
-/
def toSubring : MvPowerSeries σ T := fun n => ⟨p.coeff n, hp n⟩

@[simp]
/--
theorem `coeff_toSubring` / 定理 `coeff_toSubring`

English:
theorem coeff_toSubring
  given: {n : σ ->₀ Nat}
  statement: (p.toSubring T hp).coeff n = p.coeff n
  proof: rfl

@[simp]

中文:
定理 coeff_toSubring
  条件: {n : σ ->₀ 自然数}
  结论: (p.toSubring T hp).coeff n = p.coeff n
  证明: rfl

@[simp]
-/
theorem coeff_toSubring {n : σ ->₀ Nat} : (p.toSubring T hp).coeff n = p.coeff n := rfl

@[simp]
/--
theorem `constantCoeff_toSubring` / 定理 `constantCoeff_toSubring`

English:
theorem constantCoeff_toSubring
  statement: (p.toSubring T hp).constantCoeff = p.constantCoeff
  proof: rfl

@[simp]

中文:
定理 constantCoeff_toSubring
  结论: (p.toSubring T hp).constantCoeff = p.constantCoeff
  证明: rfl

@[simp]
-/
theorem constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoeff := rfl

@[simp]
/--
theorem `map_toSubring` / 定理 `map_toSubring`

English:
theorem map_toSubring
  statement: (p.toSubring T hp).map T.subtype = p
  proof: rfl

中文:
定理 map_toSubring
  结论: (p.toSubring T hp).map T.subtype = p
  证明: rfl
-/
theorem map_toSubring : (p.toSubring T hp).map T.subtype = p := rfl

end toSubring

@[simp]
/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  statement: {S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S]
  proof: by
  simp only [MvPowerSeries.ext_iff]
  congr! with n
  simp

中文:
定理 map_eq_zero
  结论: {S : 类型} [DivisionSemiring R] [Semiring S] [Nontrivial S]
  证明: by
  simp only [MvPowerSeries.ext_iff]
  congr! with n
  simp

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext_iff, ext_iff
-/
theorem map_eq_zero {S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S]
    (φ : MvPowerSeries σ R) (f : R ->+* S) : φ.map f = 0 ↔ φ = 0 := by
  simp only [MvPowerSeries.ext_iff]
  congr! with n
  simp

section Semiring

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `X_pow_dvd_iff` / 定理 `X_pow_dvd_iff`

English:
theorem X_pow_dvd_iff
  given: {s : σ} {n : Nat} {φ : MvPowerSeries σ R}
  proof: by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul]; rw [Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij]; rw [Finsupp.add_apply]; rw [Finsupp.si

中文:
定理 X_pow_dvd_iff
  条件: {s : σ} {n : 自然数} {φ : MvPowerSeries σ R}
  证明: by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul]; rw [Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij]; rw [Finsupp.add_apply]; rw [Finsupp.si

Depends on / 依赖: Finset, Finset.sum_eq_single, Finset.sum_eq_zero, Finsupp, Finsupp.add_apply, Finsupp.single_eq_same, Nat.le_add_right, add_apply, classical, coeff_X_pow, coeff_mul, contrapose, if_neg, le_add_right, mem_antidiagonal, single, single_eq_same, sum_eq_single, sum_eq_zero, zero_mul
-/
theorem X_pow_dvd_iff {s : σ} {n : Nat} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ forall m : σ ->₀ Nat, m s < n -> coeff m φ = 0 := by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul]; rw [Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij]; rw [Finsupp.add_apply]; rw [Finsupp.single_eq_same]
    exact Nat.le_add_right n _
  · intro h
    refine ⟨fun m => coeff (m + single s n) φ, ?_⟩
    ext m
    by_cases H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        simpa using! congr_arg (fun m : σ ->₀ Nat => coeff m φ) H.symm
      · rintro ⟨i, j⟩ hij hne
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij]; rw [← hi]; rw [Prod.mk_inj]
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
          rw [← hij]; rw [hi]
          ext
          rw [coe_add]; rw [coe_add]; rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_tsub_cancel_left]; rw [add_comm]
        · exact zero_mul _
      · contrapose! H
        ext t
        by_cases hst : s = t
        · subst t
          simpa using! tsub_add_cancel_of_le H
        · simp [hst]

/--
theorem `X_dvd_iff` / 定理 `X_dvd_iff`

English:
theorem X_dvd_iff
  given: {s : σ} {φ : MvPowerSeries σ R}
  proof: by
  rw [← pow_one (X s : MvPowerSeries σ R)]; rw [X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)

中文:
定理 X_dvd_iff
  条件: {s : σ} {φ : MvPowerSeries σ R}
  证明: by
  rw [← pow_one (X s : MvPowerSeries σ R)]; rw [X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)

Depends on / 依赖: MvPowerSeries, Nat.eq_zero_of_le_zero, Nat.le_of_succ_le_succ, X_pow_dvd_iff, eq_zero_of_le_zero, hm.symm, le_of_succ_le_succ, pow_one, zero_lt_one
-/
theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ forall m : σ ->₀ Nat, m s = 0 -> coeff m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R)]; rw [X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)

end Semiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_prod` / 定理 `coeff_prod`

English:
theorem coeff_prod
  statement: [DecidableEq ι] [DecidableEq σ]
  proof: by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | insert a s ha ih =>


中文:
定理 coeff_prod
  结论: [DecidableEq ι] [DecidableEq σ]
  证明: by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | insert a s ha ih =>


Depends on / 依赖: Embedding, Finset, Finset.induction_on, Finset.sum_congr, Function, Function.Embedding.coeFn_mk, Nat.cast_one, Nat.cast_zero, Prod.forall, card_empty, card_singleton, cast_one, cast_zero, coeFn_mk, coe_update, coeff_mul, coeff_one, finsuppAntidiag_empty, finsuppAntidiag_insert, generalizing
-/
theorem coeff_prod [DecidableEq ι] [DecidableEq σ]
    (f : ι -> MvPowerSeries σ R) (d : σ ->₀ Nat) (s : Finset ι) :
    coeff d (∏ j in s, f j) =
      ∑ l in finsuppAntidiag s d,
        ∏ i in s, coeff (l i) (f i) := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | insert a s ha ih =>
    rw [finsuppAntidiag_insert ha]; rw [prod_insert ha]; rw [coeff_mul]; rw [sum_biUnion]
    · apply Finset.sum_congr rfl
      simp only [mem_antidiagonal, sum_map, Function.Embedding.coeFn_mk, coe_update, Prod.forall]
      rintro u v rfl
      rw [ih]; rw [Finset.mul_sum]; rw [← Finset.sum_attach]
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

/--
theorem `prod_monomial` / 定理 `prod_monomial`

English:
theorem prod_monomial
  given: (f : ι -> σ ->₀ Nat) (g : ι -> R) (s : Finset ι)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha h => simp [h, monomial_mul_monomial]

中文:
定理 prod_monomial
  条件: (f : ι -> σ ->₀ 自然数) (g : ι -> R) (s : Finset ι)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha h => simp [h, monomial_mul_monomial]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, monomial_mul_monomial
-/
theorem prod_monomial (f : ι -> σ ->₀ Nat) (g : ι -> R) (s : Finset ι) :
    ∏ i in s, monomial (f i) (g i) = monomial (∑ i in s, f i) (∏ i in s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha h => simp [h, monomial_mul_monomial]

/--
theorem `coeff_pow` / 定理 `coeff_pow`

English:
theorem coeff_pow
  given: [DecidableEq σ] (f : MvPowerSeries σ R) {n : Nat} (d : σ ->₀ Nat)
  proof: by
  suffices f ^ n = (Finset.range n).prod fun _ => f by
    rw [this]; rw [coeff_prod]
  rw [Finset.prod_const]; rw [card_range]

中文:
定理 coeff_pow
  条件: [DecidableEq σ] (f : MvPowerSeries σ R) {n : 自然数} (d : σ ->₀ 自然数)
  证明: by
  suffices f ^ n = (Finset.range n).prod fun _ => f by
    rw [this]; rw [coeff_prod]
  rw [Finset.prod_const]; rw [card_range]

Depends on / 依赖: Finset, Finset.prod_const, Finset.range, card_range, coeff_prod, prod_const
-/
theorem coeff_pow [DecidableEq σ] (f : MvPowerSeries σ R) {n : Nat} (d : σ ->₀ Nat) :
    coeff d (f ^ n) =
      ∑ l in finsuppAntidiag (Finset.range n) d,
        ∏ i in Finset.range n, coeff (l i) f := by
  suffices f ^ n = (Finset.range n).prod fun _ => f by
    rw [this]; rw [coeff_prod]
  rw [Finset.prod_const]; rw [card_range]

/--
theorem `monomial_pow` / 定理 `monomial_pow`

English:
theorem monomial_pow
  given: (m : σ ->₀ Nat) (a : R) (n : Nat)
  proof: by
  rw [Finset.pow_eq_prod_const]; rw [prod_monomial]; rw [← Finset.nsmul_eq_sum_const]; rw [← Finset.pow_eq_prod_const]

中文:
定理 monomial_pow
  条件: (m : σ ->₀ 自然数) (a : R) (n : 自然数)
  证明: by
  rw [Finset.pow_eq_prod_const]; rw [prod_monomial]; rw [← Finset.nsmul_eq_sum_const]; rw [← Finset.pow_eq_prod_const]

Depends on / 依赖: Finset, Finset.nsmul_eq_sum_const, Finset.pow_eq_prod_const, nsmul_eq_sum_const, pow_eq_prod_const, prod_monomial
-/
theorem monomial_pow (m : σ ->₀ Nat) (a : R) (n : Nat) :
    (monomial m a) ^ n = monomial (n • m) (a ^ n) := by
  rw [Finset.pow_eq_prod_const]; rw [prod_monomial]; rw [← Finset.nsmul_eq_sum_const]; rw [← Finset.pow_eq_prod_const]

/--
theorem `coeff_eq_zero_of_constantCoeff_nilpotent` / 定理 `coeff_eq_zero_of_constantCoeff_nilpotent`

English:
theorem coeff_eq_zero_of_constantCoeff_nilpotent
  statement: {f : MvPowerSeries σ R} {m : Nat}
  proof: by
  classical
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_finsuppAntidiag] at hk
  set s := {i in range n | k i = 0} with hs_def
  have hs : s subseteq range n := filter_subset _ _
  have hs' (i : Nat) (hi : i in s) : coeff (k i) f = constantCoeff f := by
    simp only [hs_def, mem_

中文:
定理 coeff_eq_zero_of_constantCoeff_nilpotent
  结论: {f : MvPowerSeries σ R} {m : 自然数}
  证明: by
  classical
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_finsuppAntidiag] at hk
  set s := {i in range n | k i = 0} with hs_def
  have hs : s subseteq range n := filter_subset _ _
  have hs' (i : Nat) (hi : i in s) : coeff (k i) f = constantCoeff f := by
    simp only [hs_def, mem_

Depends on / 依赖: classical, coeff_pow, coeff_zero_eq_constantCoeff, constantCoeff, filter_subset, hs_def, mem_filter, mem_finsuppAntidiag, mul_eq_zero, prod_sdiff, subseteq, sum_eq_zero
-/
theorem coeff_eq_zero_of_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : Nat}
    (hf : constantCoeff f ^ m = 0) {d : σ ->₀ Nat} {n : Nat} (hn : m + degree d <= n) :
    coeff d (f ^ n) = 0 := by
  classical
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_finsuppAntidiag] at hk
  set s := {i in range n | k i = 0} with hs_def
  have hs : s subseteq range n := filter_subset _ _
  have hs' (i : Nat) (hi : i in s) : coeff (k i) f = constantCoeff f := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2]; rw [coeff_zero_eq_constantCoeff]
  have hs'' (i : Nat) (hi : i in s) : k i = 0 := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2]
  rw [← prod_sdiff (s₁ := s) (filter_subset _ _)]
  apply mul_eq_zero_of_right
  rw [prod_congr rfl hs']; rw [prod_const]
  suffices m <= #s by
    obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le this
    rw [hm']; rw [pow_add]; rw [hf]; rw [zero_mul]
  rw [← Nat.add_le_add_iff_right]; rw [add_comm #s]; rw [Finset.card_sdiff_add_card_eq_card (filter_subset _ _)]; rw [card_range]
  apply le_trans _ hn
  simp only [add_comm m, Nat.add_le_add_iff_right, ← hk.1,
    ← sum_sdiff (hs), sum_eq_zero (s := s) hs'', add_zero]
  rw [← hs_def]
  convert! Finset.card_nsmul_le_sum (range n \ s) (fun x => degree (k x)) 1 _
  · simp only [smul_eq_mul, mul_one]
  · simp only [degree_eq_weight_one, map_sum]
  · simp only [hs_def, mem_filter, mem_sdiff, mem_range, not_and, and_imp]
    intro i hi hi'
    rw [← not_lt]; rw [Nat.lt_one_iff]; rw [degree_eq_zero_iff]
    exact hi' hi

end CommSemiring

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (MvPowerSeries σ A)
  body: (MvPowerSeries.map (algebraMap R A)).comp C
  commutes' := fun a φ => by
    ext n
    simp [Algebra.commutes]
  smul_def' := fun a σ => by
    ext n
    simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]

中文:
实例 :
  签名: Algebra R (MvPowerSeries σ A)
  定义体: (MvPowerSeries.map (algebraMap R A)).comp C
  commutes' := fun a φ => by
    ext n
    simp [Algebra.commutes]
  smul_def' := fun a σ => by
    ext n
    simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map, algebraMap
-/
instance : Algebra R (MvPowerSeries σ A) where
  algebraMap := (MvPowerSeries.map (algebraMap R A)).comp C
  commutes' := fun a φ => by
    ext n
    simp [Algebra.commutes]
  smul_def' := fun a σ => by
    ext n
    simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]

/--
theorem `c_eq_algebraMap` / 定理 `c_eq_algebraMap`

English:
theorem c_eq_algebraMap
  statement: C = algebraMap R (MvPowerSeries σ R)
  proof: rfl

中文:
定理 c_eq_algebraMap
  结论: C = algebraMap R (MvPowerSeries σ R)
  证明: rfl
-/
theorem c_eq_algebraMap : C = algebraMap R (MvPowerSeries σ R) :=
  rfl

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: {r : R}
  proof: by
  change (MvPowerSeries.map (algebraMap R A)).comp C r = _
  simp

中文:
定理 algebraMap_apply
  条件: {r : R}
  证明: by
  change (MvPowerSeries.map (algebraMap R A)).comp C r = _
  simp

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map, algebraMap
-/
theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C (algebraMap R A r) := by
  change (MvPowerSeries.map (algebraMap R A)).comp C r = _
  simp

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (φ : A ->ₐ[R] B)
  body: MvPowerSeries.map φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

中文:
定义 mapAlgHom
  签名: (φ : A ->ₐ[R] B)
  定义体: MvPowerSeries.map φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map
-/
def mapAlgHom (φ : A ->ₐ[R] B) :
    MvPowerSeries σ A ->ₐ[R] MvPowerSeries σ B where
  toRingHom := MvPowerSeries.map φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

/--
theorem `mapAlgHom_apply` / 定理 `mapAlgHom_apply`

English:
theorem mapAlgHom_apply
  given: (φ : A ->ₐ[R] B) (f : MvPowerSeries σ A)
  proof: rfl

中文:
定理 mapAlgHom_apply
  条件: (φ : A ->ₐ[R] B) (f : MvPowerSeries σ A)
  证明: rfl

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map
-/
theorem mapAlgHom_apply (φ : A ->ₐ[R] B) (f : MvPowerSeries σ A) :
    mapAlgHom (σ := σ) φ f = MvPowerSeries.map φ f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R))
  body: ⟨⟨⊥, ⊤, by
      classical
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [MvPowerSeries.ext_iff]; rw [not_forall]
      refine ⟨Finsupp.s

中文:
实例 [Nonempty
  签名: σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R))
  定义体: ⟨⟨⊥, ⊤, by
      classical
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [MvPowerSeries.ext_iff]; rw [not_forall]
      refine ⟨Finsupp.s

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_top, Finsupp, Finsupp.single, MvPowerSeries, MvPowerSeries.ext_iff, Set.mem_range, SetLike, SetLike.ext_iff, algebraMap_apply, classical, coeff_C, ext_iff, iff_true, inhabit, mem_bot, mem_range, mem_top, not_exists
-/
instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      classical
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [MvPowerSeries.ext_iff]; rw [not_forall]
      refine ⟨Finsupp.single default 1, ?_⟩
      simp [algebraMap_apply, coeff_C]⟩⟩

end Algebra


end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
@[coe]
/--
Definition of `toMvPowerSeries` / `toMvPowerSeries` 的定义

English:
definition toMvPowerSeries
  signature: : MvPolynomial σ R -> MvPowerSeries σ R
  body: fun φ n => coeff n φ

中文:
定义 toMvPowerSeries
  签名: : MvPolynomial σ R -> MvPowerSeries σ R
  定义体: fun φ n => coeff n φ
-/
def toMvPowerSeries : MvPolynomial σ R -> MvPowerSeries σ R :=
  fun φ n => coeff n φ

/--
Instance `coeToMvPowerSeries` / 实例 `coeToMvPowerSeries`

English:
instance coeToMvPowerSeries
  signature: : Coe (MvPolynomial σ R) (MvPowerSeries σ R)
  body: ⟨toMvPowerSeries⟩

中文:
实例 coeToMvPowerSeries
  签名: : Coe (MvPolynomial σ R) (MvPowerSeries σ R)
  定义体: ⟨toMvPowerSeries⟩

Depends on / 依赖: toMvPowerSeries
-/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨toMvPowerSeries⟩

/--
theorem `coe_def` / 定理 `coe_def`

English:
theorem coe_def
  statement: (φ : MvPowerSeries σ R) = fun n => coeff n φ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_def
  结论: (φ : MvPowerSeries σ R) = fun n => coeff n φ
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl

@[simp, norm_cast]
/--
theorem `coeff_coe` / 定理 `coeff_coe`

English:
theorem coeff_coe
  given: (n : σ ->₀ Nat)
  statement: MvPowerSeries.coeff n ↑φ = coeff n φ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coeff_coe
  条件: (n : σ ->₀ 自然数)
  结论: MvPowerSeries.coeff n ↑φ = coeff n φ
  证明: rfl

@[simp, norm_cast]
-/
theorem coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff n ↑φ = coeff n φ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_monomial` / 定理 `coe_monomial`

English:
theorem coe_monomial
  given: (n : σ ->₀ Nat) (a : R)
  proof: MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe]; rw [coeff_monomial]; rw [MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | subst m; contradiction

@[simp, norm_cast]

中文:
定理 coe_monomial
  条件: (n : σ ->₀ 自然数) (a : R)
  证明: MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe]; rw [coeff_monomial]; rw [MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | subst m; contradiction

@[simp, norm_cast]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_monomial, MvPowerSeries.ext, classical, coeff_coe, coeff_monomial, split_ifs
-/
theorem coe_monomial (n : σ ->₀ Nat) (a : R) :
    (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a :=
  MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe]; rw [coeff_monomial]; rw [MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | subst m; contradiction

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1
  proof: coe_monomial _ _

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1
  证明: coe_monomial _ _

@[simp, norm_cast]

Depends on / 依赖: coe_monomial
-/
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
    coe_monomial _ _

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  结论: ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ
  proof: MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]

中文:
定理 coe_mul
  结论: ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ
  证明: MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_mul, MvPowerSeries.ext, classical, coeff_coe, coeff_mul
-/
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (φ : MvPolynomial σ R) (r : R)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_smul
  条件: (φ : MvPolynomial σ R) (r : R)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_smul (φ : MvPolynomial σ R) (r : R) :
    (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp, norm_cast]
/--
theorem `coe_C` / 定理 `coe_C`

English:
theorem coe_C
  given: (a : R)
  statement: ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C a
  proof: coe_monomial _ _

@[simp, norm_cast]

中文:
定理 coe_C
  条件: (a : R)
  结论: ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C a
  证明: coe_monomial _ _

@[simp, norm_cast]

Depends on / 依赖: coe_monomial
-/
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C a :=
  coe_monomial _ _

@[simp, norm_cast]
/--
theorem `coe_X` / 定理 `coe_X`

English:
theorem coe_X
  given: (s : σ)
  statement: ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s
  proof: coe_monomial _ _

中文:
定理 coe_X
  条件: (s : σ)
  结论: ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s
  证明: coe_monomial _ _

Depends on / 依赖: coe_monomial
-/
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s :=
  coe_monomial _ _

variable (σ R)

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : MvPolynomial σ R -> MvPowerSeries σ R)
  proof: by
  intro x y h
  ext
  simp_rw [← coeff_coe, h]

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : MvPolynomial σ R -> MvPowerSeries σ R)
  证明: by
  intro x y h
  ext
  simp_rw [← coeff_coe, h]

Depends on / 依赖: coeff_coe, simp_rw
-/
theorem coe_injective : Function.Injective ((↑) : MvPolynomial σ R -> MvPowerSeries σ R) := by
  intro x y h
  ext
  simp_rw [← coeff_coe, h]

variable {σ R φ ψ}

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ
  proof: (coe_injective σ R).eq_iff

@[simp]

中文:
定理 coe_inj
  结论: (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ
  证明: (coe_injective σ R).eq_iff

@[simp]

Depends on / 依赖: coe_injective, eq_iff
-/
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff

@[simp]
/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  statement: (φ : MvPowerSeries σ R) = 0 ↔ φ = 0
  proof: by rw [← coe_zero, coe_inj]

@[simp]

中文:
定理 coe_eq_zero_iff
  结论: (φ : MvPowerSeries σ R) = 0 ↔ φ = 0
  证明: by rw [← coe_zero, coe_inj]

@[simp]

Depends on / 依赖: coe_inj, coe_zero
-/
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
/--
theorem `coe_eq_one_iff` / 定理 `coe_eq_one_iff`

English:
theorem coe_eq_one_iff
  statement: (φ : MvPowerSeries σ R) = 1 ↔ φ = 1
  proof: by rw [← coe_one, coe_inj]

中文:
定理 coe_eq_one_iff
  结论: (φ : MvPowerSeries σ R) = 1 ↔ φ = 1
  证明: by rw [← coe_one, coe_inj]

Depends on / 依赖: coe_inj, coe_one
-/
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/--
Definition of `coeToMvPowerSeries.ringHom` / `coeToMvPowerSeries.ringHom` 的定义

English:
definition coeToMvPowerSeries.ringHom
  signature: : MvPolynomial σ R ->+* MvPowerSeries σ R where
  body: (Coe.coe : MvPolynomial σ R -> MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]

中文:
定义 coeToMvPowerSeries.ringHom
  签名: : MvPolynomial σ R ->+* MvPowerSeries σ R where
  定义体: (Coe.coe : MvPolynomial σ R -> MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]

Depends on / 依赖: Coe.coe, MvPolynomial, MvPowerSeries
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R ->+* MvPowerSeries σ R where
  toFun := (Coe.coe : MvPolynomial σ R -> MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (n : Nat)
  proof: coeToMvPowerSeries.ringHom.map_pow _ _

中文:
定理 coe_pow
  条件: (n : 自然数)
  证明: coeToMvPowerSeries.ringHom.map_pow _ _

Depends on / 依赖: coeToMvPowerSeries, coeToMvPowerSeries.ringHom.map_pow, map_pow, ringHom
-/
theorem coe_pow (n : Nat) :
    ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _

variable (φ ψ)

@[simp]
/--
theorem `coeToMvPowerSeries.ringHom_apply` / 定理 `coeToMvPowerSeries.ringHom_apply`

English:
theorem coeToMvPowerSeries.ringHom_apply
  statement: coeToMvPowerSeries.ringHom φ = φ
  proof: rfl

中文:
定理 coeToMvPowerSeries.ringHom_apply
  结论: coeToMvPowerSeries.ringHom φ = φ
  证明: rfl
-/
theorem coeToMvPowerSeries.ringHom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl

/--
theorem `_root_.MvPowerSeries.monomial_one_eq` / 定理 `_root_.MvPowerSeries.monomial_one_eq`

English:
theorem _root_.MvPowerSeries.monomial_one_eq
  proof: by
  simp only [← coe_X, ← coe_pow, ← coe_monomial, monomial_eq, map_one, one_mul]
  simp only [← coeToMvPowerSeries.ringHom_apply, ← map_finsuppProd]

中文:
定理 _root_.MvPowerSeries.monomial_one_eq
  证明: by
  simp only [← coe_X, ← coe_pow, ← coe_monomial, monomial_eq, map_one, one_mul]
  simp only [← coeToMvPowerSeries.ringHom_apply, ← map_finsuppProd]

Depends on / 依赖: coeToMvPowerSeries, coeToMvPowerSeries.ringHom_apply, coe_X, coe_monomial, coe_pow, map_finsuppProd, map_one, monomial_eq, one_mul, ringHom_apply
-/
theorem _root_.MvPowerSeries.monomial_one_eq
    (e : σ ->₀ Nat) :
    MvPowerSeries.monomial e (1 : R) =
      e.prod fun s n => (MvPowerSeries.X s) ^ n := by
  simp only [← coe_X, ← coe_pow, ← coe_monomial, monomial_eq, map_one, one_mul]
  simp only [← coeToMvPowerSeries.ringHom_apply, ← map_finsuppProd]

/--
theorem `_root_.MvPowerSeries.monomial_eq'` / 定理 `_root_.MvPowerSeries.monomial_eq'`

English:
theorem _root_.MvPowerSeries.monomial_eq'
  given: (e : σ ->₀ Nat) (r : R)
  proof: by
  conv_lhs => rw [← mul_one r]
  rw [← smul_eq_mul]; rw [← MvPowerSeries.smul_eq_C_mul]; rw [LinearMap.CompatibleSMul.map_smul]; rw [MvPowerSeries.monomial_one_eq]

中文:
定理 _root_.MvPowerSeries.monomial_eq'
  条件: (e : σ ->₀ 自然数) (r : R)
  证明: by
  conv_lhs => rw [← mul_one r]
  rw [← smul_eq_mul]; rw [← MvPowerSeries.smul_eq_C_mul]; rw [LinearMap.CompatibleSMul.map_smul]; rw [MvPowerSeries.monomial_one_eq]

Depends on / 依赖: CompatibleSMul, LinearMap, LinearMap.CompatibleSMul.map_smul, MvPowerSeries, MvPowerSeries.monomial_one_eq, MvPowerSeries.smul_eq_C_mul, conv_lhs, map_smul, monomial_one_eq, mul_one, smul_eq_C_mul, smul_eq_mul
-/
theorem _root_.MvPowerSeries.monomial_eq' (e : σ ->₀ Nat) (r : R) :
    MvPowerSeries.monomial e r
      = MvPowerSeries.C r * e.prod fun s e => (MvPowerSeries.X s) ^ e := by
  conv_lhs => rw [← mul_one r]
  rw [← smul_eq_mul]; rw [← MvPowerSeries.smul_eq_C_mul]; rw [LinearMap.CompatibleSMul.map_smul]; rw [MvPowerSeries.monomial_one_eq]

/--
theorem `_root_.MvPowerSeries.monomial_smul_eq` / 定理 `_root_.MvPowerSeries.monomial_smul_eq`

English:
theorem _root_.MvPowerSeries.monomial_smul_eq
  given: (e : σ ->₀ Nat) (p : Nat) (r : R)
  proof: by
  rw [MvPowerSeries.monomial_eq']; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _
    (by simp)]; rw [Finsupp.prod]
  simp [pow_mul]

中文:
定理 _root_.MvPowerSeries.monomial_smul_eq
  条件: (e : σ ->₀ 自然数) (p : 自然数) (r : R)
  证明: by
  rw [MvPowerSeries.monomial_eq']; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _
    (by simp)]; rw [Finsupp.prod]
  simp [pow_mul]

Depends on / 依赖: Finsupp, Finsupp.prod, Finsupp.prod_of_support_subset, Finsupp.support_smul, MvPowerSeries, MvPowerSeries.monomial_eq, monomial_eq, pow_mul, prod_of_support_subset, support_smul
-/
theorem _root_.MvPowerSeries.monomial_smul_eq (e : σ ->₀ Nat) (p : Nat) (r : R) :
    MvPowerSeries.monomial (p • e) r
      = MvPowerSeries.C r * e.prod fun s e => ((MvPowerSeries.X s) ^ p) ^ e := by
  rw [MvPowerSeries.monomial_eq']; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _
    (by simp)]; rw [Finsupp.prod]
  simp [pow_mul]

/--
theorem `_root_.MvPowerSeries.monomial_mapDomain_apply_one` / 定理 `_root_.MvPowerSeries.monomial_mapDomain_apply_one`

English:
theorem _root_.MvPowerSeries.monomial_mapDomain_apply_one
  given: {τ : Type*} (d : σ ->₀ Nat) (f : σ -> τ)
  proof: by
  simp [pow_add, prod_sum_index, MvPowerSeries.monomial_one_eq, mapDomain]

中文:
定理 _root_.MvPowerSeries.monomial_mapDomain_apply_one
  条件: {τ : 类型} (d : σ ->₀ 自然数) (f : σ -> τ)
  证明: by
  simp [pow_add, prod_sum_index, MvPowerSeries.monomial_one_eq, mapDomain]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.monomial_one_eq, mapDomain, monomial_one_eq, pow_add, prod_sum_index
-/
theorem _root_.MvPowerSeries.monomial_mapDomain_apply_one {τ : Type*} (d : σ ->₀ Nat) (f : σ -> τ) :
    MvPowerSeries.monomial (mapDomain f d) (1 : R) =
      d.prod fun s e => MvPowerSeries.X (f s) ^ e := by
  simp [pow_add, prod_sum_index, MvPowerSeries.monomial_one_eq, mapDomain]

section Algebra

variable (A : Type*) [CommSemiring A] [Algebra R A]

/--
Definition of `coeToMvPowerSeries.algHom` / `coeToMvPowerSeries.algHom` 的定义

English:
definition coeToMvPowerSeries.algHom
  signature: : MvPolynomial σ R ->ₐ[R] MvPowerSeries σ A
  body: { (MvPowerSeries.map (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

@[simp]

中文:
定义 coeToMvPowerSeries.algHom
  签名: : MvPolynomial σ R ->ₐ[R] MvPowerSeries σ A
  定义体: { (MvPowerSeries.map (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.algebraMap_apply, MvPowerSeries.map, algebraMap, algebraMap_apply, coeToMvPowerSeries, coeToMvPowerSeries.ringHom, commutes, ringHom
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R ->ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

@[simp]
/--
theorem `coeToMvPowerSeries.algHom_apply` / 定理 `coeToMvPowerSeries.algHom_apply`

English:
theorem coeToMvPowerSeries.algHom_apply
  proof: rfl

中文:
定理 coeToMvPowerSeries.algHom_apply
  证明: rfl
-/
theorem coeToMvPowerSeries.algHom_apply :
    coeToMvPowerSeries.algHom A φ = MvPowerSeries.map (algebraMap R A) ↑φ :=
  rfl

/--
theorem `_root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one` / 定理 `_root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one`

English:
theorem _root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one
  proof: by
  rw [Finsupp.prod_congr
    (g2 := fun s n => ((MvPowerSeries.C (algebraMap A R (a s)) * (MvPowerSeries.X s)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f =
      MvPowerSeries.C ((algebraMap A R) a) * f := by
      rw [← MvPowerSeries.smul_eq_C_mul]; rw [IsScalarTower.algebraMap_smul

中文:
定理 _root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one
  证明: by
  rw [Finsupp.prod_congr
    (g2 := fun s n => ((MvPowerSeries.C (algebraMap A R (a s)) * (MvPowerSeries.X s)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f =
      MvPowerSeries.C ((algebraMap A R) a) * f := by
      rw [← MvPowerSeries.smul_eq_C_mul]; rw [IsScalarTower.algebraMap_smul

Depends on / 依赖: Finsupp, Finsupp.prod_congr, Finsupp.prod_mul, IsScalarTower, IsScalarTower.algebraMap_smul, MvPowerSeries, MvPowerSeries.C, MvPowerSeries.X, MvPowerSeries.monomial_one_eq, MvPowerSeries.smul_eq_C_mul, algebraMap, algebraMap_smul, algebra_compatible_smul, map_finsuppProd, map_pow, monomial_one_eq, mul_pow, prod_congr, prod_mul, smul_eq_C_mul
-/
theorem _root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one
    {A : Type*} [CommSemiring A] [Algebra A R] (e : σ ->₀ Nat) (a : σ -> A) :
    e.prod (fun s n => ((a s • MvPowerSeries.X s) ^ n))
      = (e.prod fun s n => (a s) ^ n) • MvPowerSeries.monomial (R := R) e 1 := by
  rw [Finsupp.prod_congr
    (g2 := fun s n => ((MvPowerSeries.C (algebraMap A R (a s)) * (MvPowerSeries.X s)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f =
      MvPowerSeries.C ((algebraMap A R) a) * f := by
      rw [← MvPowerSeries.smul_eq_C_mul]; rw [IsScalarTower.algebraMap_smul]
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow, ← MvPowerSeries.monomial_one_eq, this]
    simp only [map_finsuppProd, map_pow]
  · intro x _
    rw [algebra_compatible_smul R]; rw [MvPowerSeries.smul_eq_C_mul]

/--
theorem `_root_.MvPowerSeries.monomial_eq` / 定理 `_root_.MvPowerSeries.monomial_eq`

English:
theorem _root_.MvPowerSeries.monomial_eq
  given: (e : σ ->₀ Nat) (r : σ -> R)
  proof: by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 _root_.MvPowerSeries.monomial_eq
  条件: (e : σ ->₀ 自然数) (r : σ -> R)
  证明: by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.prod_smul_X_eq_smul_monomial_one, map_smul, mul_one, prod_smul_X_eq_smul_monomial_one, smul_eq_mul
-/
theorem _root_.MvPowerSeries.monomial_eq (e : σ ->₀ Nat) (r : σ -> R) :
    MvPowerSeries.monomial e (e.prod (fun s n => r s ^ n))
      = e.prod fun s e => (r s • MvPowerSeries.X s) ^ e := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `_root_.MvPowerSeries.monomial_smul_const` / 定理 `_root_.MvPowerSeries.monomial_smul_const`

English:
theorem _root_.MvPowerSeries.monomial_smul_const
  proof: by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

中文:
定理 _root_.MvPowerSeries.monomial_smul_const
  证明: by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

Depends on / 依赖: Finset, Finset.prod_pow_eq_pow_sum, Finsupp, Finsupp.prod, Finsupp.sum, MvPowerSeries, MvPowerSeries.prod_smul_X_eq_smul_monomial_one, map_smul, mul_one, prod_pow_eq_pow_sum, prod_smul_X_eq_smul_monomial_one, smul_eq_mul
-/
theorem _root_.MvPowerSeries.monomial_smul_const
    {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ ->₀ Nat) (r : R) :
    MvPowerSeries.monomial e (r ^ (e.sum fun _ n => n))
      = (e.prod fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : MvPowerSeries σ R)

/--
Instance `algebraMvPolynomial` / 实例 `algebraMvPolynomial`

English:
instance algebraMvPolynomial
  signature: : Algebra (MvPolynomial σ R) (MvPowerSeries σ A)
  body: RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom

中文:
实例 algebraMvPolynomial
  签名: : Algebra (MvPolynomial σ R) (MvPowerSeries σ A)
  定义体: RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom

Depends on / 依赖: MvPolynomial, MvPolynomial.coeToMvPowerSeries.algHom, RingHom, RingHom.toAlgebra, algHom, coeToMvPowerSeries, toAlgebra, toRingHom
-/
instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom

/--
Instance `algebraMvPowerSeries` / 实例 `algebraMvPowerSeries`

English:
instance algebraMvPowerSeries
  signature: : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A)
  body: (map (algebraMap R A)).toAlgebra

中文:
实例 algebraMvPowerSeries
  签名: : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A)
  定义体: (map (algebraMap R A)).toAlgebra

Depends on / 依赖: algebraMap, toAlgebra
-/
instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map (algebraMap R A)).toAlgebra

variable (A)

/--
theorem `algebraMap_apply'` / 定理 `algebraMap_apply'`

English:
theorem algebraMap_apply'
  given: (p : MvPolynomial σ R)
  proof: rfl

中文:
定理 algebraMap_apply'
  条件: (p : MvPolynomial σ R)
  证明: rfl
-/
theorem algebraMap_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map (algebraMap R A) p :=
  rfl

/--
theorem `algebraMap_apply''` / 定理 `algebraMap_apply''`

English:
theorem algebraMap_apply''
  proof: rfl

中文:
定理 algebraMap_apply''
  证明: rfl
-/
theorem algebraMap_apply'' :
    algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map (algebraMap R A) f :=
  rfl

end MvPowerSeries

end
