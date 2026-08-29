/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Ralf Stephan
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Formal power series (in one variable)

This file defines (univariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

Formal power series in one variable are defined from multivariate
power series as `PowerSeries R := MvPowerSeries Unit R`.

The file sets up the (semi)ring structure on univariate power series.

We provide the natural inclusion from polynomials to formal power series.

Additional results can be found in:
* `Mathlib/RingTheory/PowerSeries/Trunc.lean`, truncation of power series;
* `Mathlib/RingTheory/PowerSeries/Inverse.lean`, about inverses of power series,
  and the fact that power series over a local ring form a local ring;
* `Mathlib/RingTheory/PowerSeries/Order.lean`, the order of a power series at 0,
  and application to the fact that power series over an integral domain form an integral domain.

## Implementation notes

Because of its definition,
  `PowerSeries R := MvPowerSeries Unit R`.
a lot of proofs and properties from the multivariate case
can be ported to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they were indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.

-/

@[expose] public section

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Formal power series over a coefficient type `R` -/
@[wikidata Q1003025]
/--
Definition of `PowerSeries` / `PowerSeries` 的定义

English:
abbreviation PowerSeries
  signature: (R : Type*)
  body: MvPowerSeries Unit R

中文:
缩写 幂级数
  签名: (R : 类型)
  定义体: MvPowerSeries Unit R

Depends on / 依赖: MvPowerSeries
-/
abbrev PowerSeries (R : Type*) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

/--
`R⟦X⟧` is notation for `PowerSeries R`,
the semiring of formal power series in one variable over a semiring `R`.
-/
scoped notation:9000 R "⟦X⟧" => PowerSeries R

section Semiring

variable [Semiring R]

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (n : Nat)
  body: MvPowerSeries.coeff (single () n)

中文:
定义 coeff
  签名: (n : 自然数)
  定义体: MvPowerSeries.coeff (single () n)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff, single
-/
def coeff (n : Nat) : R⟦X⟧ ->ₗ[R] R :=
  MvPowerSeries.coeff (single () n)

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: (n : Nat)
  body: MvPowerSeries.monomial (single () n)

中文:
定义 monomial
  签名: (n : 自然数)
  定义体: MvPowerSeries.monomial (single () n)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.monomial, monomial, single
-/
def monomial (n : Nat) : R ->ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial (single () n)

/--
theorem `coeff_def` / 定理 `coeff_def`

English:
theorem coeff_def
  given: {s : Unit ->₀ Nat} {n : Nat} (h : s () = n)
  proof: by
  rw [coeff]; rw [← h]; rw [← Finsupp.unique_single s]

@[simp]

中文:
定理 coeff_def
  条件: {s : 单元 ->₀ 自然数} {n : 自然数} (h : s () = n)
  证明: by
  rw [coeff]; rw [← h]; rw [← Finsupp.unique_single s]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.unique_single, MvPowerSeries, MvPowerSeries.coeff, unique_single
-/
theorem coeff_def {s : Unit ->₀ Nat} {n : Nat} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  rw [coeff]; rw [← h]; rw [← Finsupp.unique_single s]

@[simp]
/--
lemma `coeff_coeToMvPowerSeries` / 引理 `coeff_coeToMvPowerSeries`

English:
lemma coeff_coeToMvPowerSeries
  given: {f : R⟦X⟧} (n : Nat)
  proof: rfl

中文:
引理 coeff_coeToMvPowerSeries
  条件: {f : R⟦X⟧} (n : 自然数)
  证明: rfl
-/
lemma coeff_coeToMvPowerSeries {f : R⟦X⟧} (n : Nat) :
    MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n := rfl

/-- Two formal power series are equal if all their coefficients are equal. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ)
  statement: φ = ψ
  proof: MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

@[simp]

中文:
定理 ext
  条件: {φ ψ : R⟦X⟧} (h : 对任意 n, coeff n φ = coeff n ψ)
  结论: φ = ψ
  证明: MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext, coeff_def
-/
theorem ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

@[simp]
/--
theorem `forall_coeff_eq_zero` / 定理 `forall_coeff_eq_zero`

English:
theorem forall_coeff_eq_zero
  given: (φ : R⟦X⟧)
  statement: (forall n, coeff n φ = 0) ↔ φ = 0
  proof: ⟨fun h => ext h, fun h => by simp [h]⟩

中文:
定理 对任意_coeff_eq_zero
  条件: (φ : R⟦X⟧)
  结论: (对任意 n, coeff n φ = 0) ↔ φ = 0
  证明: ⟨fun h => ext h, fun h => by simp [h]⟩
-/
theorem forall_coeff_eq_zero (φ : R⟦X⟧) : (forall n, coeff n φ = 0) ↔ φ = 0 :=
  ⟨fun h => ext h, fun h => by simp [h]⟩

/-- Two formal power series are equal if all their coefficients are equal. -/
add_decl_doc PowerSeries.ext_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton R⟦X⟧
  body: by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

中文:
实例 [子单例
  签名: R] : 子单例 R⟦X⟧
  定义体: by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff, subsingleton, subsingleton_iff
-/
instance [Subsingleton R] : Subsingleton R⟦X⟧ := by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {R} (f : Nat -> R)
  body: fun s => f (s ())

@[simp]

中文:
定义 mk
  签名: {R} (f : 自然数 -> R)
  定义体: fun s => f (s ())

@[simp]
-/
def mk {R} (f : Nat -> R) : R⟦X⟧ := fun s => f (s ())

@[simp]
/--
theorem `coeff_mk` / 定理 `coeff_mk`

English:
theorem coeff_mk
  given: (n : Nat) (f : Nat -> R)
  statement: coeff n (mk f) = f n
  proof: congr_arg f Finsupp.single_eq_same

中文:
定理 coeff_mk
  条件: (n : 自然数) (f : 自然数 -> R)
  结论: coeff n (mk f) = f n
  证明: congr_arg f Finsupp.single_eq_same

Depends on / 依赖: Finsupp, Finsupp.single_eq_same, congr_arg, single_eq_same
-/
theorem coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same

/--
theorem `coeff_monomial` / 定理 `coeff_monomial`

English:
theorem coeff_monomial
  given: (m n : Nat) (a : R)
  statement: coeff m (monomial n a) = if m = n then a else 0
  proof: calc
    coeff m (monomial n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

中文:
定理 coeff_monomial
  条件: (m n : 自然数) (a : R)
  结论: coeff m (monomial n a) = if m = n then a else 0
  证明: calc
    coeff m (monomial n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

Depends on / 依赖: BaireSpace, BaireSpace.of_t2Space_locallyCompactSpace, Finsupp, Finsupp.unique_single_eq_iff, MvPowerSeries, MvPowerSeries.coeff_monomial, coeff_monomial, monomial, of_t2Space_locallyCompactSpace, unique_single_eq_iff
-/
theorem coeff_monomial (m n : Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0 :=
  calc
    coeff m (monomial n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

/--
theorem `monomial_eq_mk` / 定理 `monomial_eq_mk`

English:
theorem monomial_eq_mk
  given: (n : Nat) (a : R)
  statement: monomial n a = mk fun m => if m = n then a else 0
  proof: ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]

中文:
定理 monomial_eq_mk
  条件: (n : 自然数) (a : R)
  结论: monomial n a = mk fun m => if m = n then a else 0
  证明: ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]

Depends on / 依赖: coeff_mk, coeff_monomial
-/
theorem monomial_eq_mk (n : Nat) (a : R) : monomial n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]
/--
theorem `coeff_monomial_same` / 定理 `coeff_monomial_same`

English:
theorem coeff_monomial_same
  given: (n : Nat) (a : R)
  statement: coeff n (monomial n a) = a
  proof: MvPowerSeries.coeff_monomial_same _ _

@[simp]

中文:
定理 coeff_monomial_same
  条件: (n : 自然数) (a : R)
  结论: coeff n (monomial n a) = a
  证明: MvPowerSeries.coeff_monomial_same _ _

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_monomial_same, coeff_monomial_same
-/
theorem coeff_monomial_same (n : Nat) (a : R) : coeff n (monomial n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
/--
theorem `coeff_comp_monomial` / 定理 `coeff_comp_monomial`

English:
theorem coeff_comp_monomial
  given: (n : Nat)
  statement: (coeff (R := R) n).comp (monomial n) = LinearMap.id
  proof: LinearMap.ext coeff_monomial_same n

中文:
定理 coeff_comp_monomial
  条件: (n : 自然数)
  结论: (coeff (R := R) n).comp (monomial n) = 线性映射.id
  证明: LinearMap.ext coeff_monomial_same n

Depends on / 依赖: LinearMap, LinearMap.id, monomial
-/
theorem coeff_comp_monomial (n : Nat) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
LinearMap.ext coeff_monomial_same n

/--
theorem `monomial_mul_monomial` / 定理 `monomial_mul_monomial`

English:
theorem monomial_mul_monomial
  given: (m n : Nat) (a b : R)
  proof: by
  simpa [monomial] using
    MvPowerSeries.monomial_mul_monomial (Finsupp.single () m) (Finsupp.single () n) a b

中文:
定理 monomial_mul_monomial
  条件: (m n : 自然数) (a b : R)
  证明: by
  simpa [monomial] using
    MvPowerSeries.monomial_mul_monomial (Finsupp.single () m) (Finsupp.single () n) a b

Depends on / 依赖: Finsupp, Finsupp.single, MvPowerSeries, MvPowerSeries.monomial_mul_monomial, monomial, monomial_mul_monomial, single
-/
theorem monomial_mul_monomial (m n : Nat) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
  simpa [monomial] using
    MvPowerSeries.monomial_mul_monomial (Finsupp.single () m) (Finsupp.single () n) a b

/--
Definition of `constantCoeff` / `constantCoeff` 的定义

English:
definition constantCoeff
  signature: : R⟦X⟧ ->+* R
  body: MvPowerSeries.constantCoeff

中文:
定义 constantCoeff
  签名: : R⟦X⟧ ->+* R
  定义体: MvPowerSeries.constantCoeff

Depends on / 依赖: MvPowerSeries, MvPowerSeries.constantCoeff, constantCoeff
-/
def constantCoeff : R⟦X⟧ ->+* R :=
  MvPowerSeries.constantCoeff

/--
theorem `constantCoeff_eq` / 定理 `constantCoeff_eq`

English:
theorem constantCoeff_eq
  given: (f : R⟦X⟧)
  proof: rfl

中文:
定理 constantCoeff_eq
  条件: (f : R⟦X⟧)
  证明: rfl
-/
theorem constantCoeff_eq (f : R⟦X⟧) :
    constantCoeff f = MvPowerSeries.constantCoeff f := rfl

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* R⟦X⟧
  body: MvPowerSeries.C

中文:
定义 C
  签名: : R ->+* R⟦X⟧
  定义体: MvPowerSeries.C

Depends on / 依赖: MvPowerSeries, MvPowerSeries.C
-/
def C : R ->+* R⟦X⟧ :=
  MvPowerSeries.C

/--
lemma `C_apply` / 引理 `C_apply`

English:
lemma C_apply
  given: {r : R}
  statement: C r = MvPowerSeries.C r
  proof: rfl

中文:
引理 C_apply
  条件: {r : R}
  结论: C r = MvPowerSeries.C r
  证明: rfl
-/
lemma C_apply {r : R} : C r = MvPowerSeries.C r := rfl

/--
lemma `algebraMap_eq` / 引理 `algebraMap_eq`

English:
lemma algebraMap_eq
  given: {R : Type*} [CommSemiring R]
  statement: algebraMap R R⟦X⟧ = C
  proof: rfl

中文:
引理 algebraMap_eq
  条件: {R : 类型} [交换半环 R]
  结论: algebraMap R R⟦X⟧ = C
  证明: rfl
-/
@[simp] lemma algebraMap_eq {R : Type*} [CommSemiring R] : algebraMap R R⟦X⟧ = C := rfl

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : R⟦X⟧
  body: MvPowerSeries.X ()

中文:
定义 X
  签名: : R⟦X⟧
  定义体: MvPowerSeries.X ()

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X
-/
def X : R⟦X⟧ :=
  MvPowerSeries.X ()

/--
lemma `X_apply` / 引理 `X_apply`

English:
lemma X_apply
  statement: X (R := R) = MvPowerSeries.X ()
  proof: rfl

中文:
引理 X_apply
  结论: X (R := R) = MvPowerSeries.X ()
  证明: rfl

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X
-/
lemma X_apply : X (R := R) = MvPowerSeries.X () := rfl

/--
theorem `commute_X` / 定理 `commute_X`

English:
theorem commute_X
  given: (φ : R⟦X⟧)
  statement: Commute φ X
  proof: MvPowerSeries.commute_X _ _

中文:
定理 commute_X
  条件: (φ : R⟦X⟧)
  结论: Commute φ X
  证明: MvPowerSeries.commute_X _ _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.commute_X, commute_X
-/
theorem commute_X (φ : R⟦X⟧) : Commute φ X :=
  MvPowerSeries.commute_X _ _

/--
theorem `X_mul` / 定理 `X_mul`

English:
theorem X_mul
  given: {φ : R⟦X⟧}
  statement: X * φ = φ * X
  proof: MvPowerSeries.X_mul

中文:
定理 X_mul
  条件: {φ : R⟦X⟧}
  结论: X * φ = φ * X
  证明: MvPowerSeries.X_mul

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X_mul, X_mul
-/
theorem X_mul {φ : R⟦X⟧} : X * φ = φ * X :=
  MvPowerSeries.X_mul

/--
theorem `commute_X_pow` / 定理 `commute_X_pow`

English:
theorem commute_X_pow
  given: (φ : R⟦X⟧) (n : Nat)
  statement: Commute φ (X ^ n)
  proof: MvPowerSeries.commute_X_pow _ _ _

中文:
定理 commute_X_pow
  条件: (φ : R⟦X⟧) (n : 自然数)
  结论: Commute φ (X ^ n)
  证明: MvPowerSeries.commute_X_pow _ _ _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.commute_X_pow, commute_X_pow
-/
theorem commute_X_pow (φ : R⟦X⟧) (n : Nat) : Commute φ (X ^ n) :=
  MvPowerSeries.commute_X_pow _ _ _

/--
theorem `X_pow_mul` / 定理 `X_pow_mul`

English:
theorem X_pow_mul
  given: {φ : R⟦X⟧} {n : Nat}
  statement: X ^ n * φ = φ * X ^ n
  proof: MvPowerSeries.X_pow_mul

@[simp]

中文:
定理 X_pow_mul
  条件: {φ : R⟦X⟧} {n : 自然数}
  结论: X ^ n * φ = φ * X ^ n
  证明: MvPowerSeries.X_pow_mul

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X_pow_mul, X_pow_mul
-/
theorem X_pow_mul {φ : R⟦X⟧} {n : Nat} : X ^ n * φ = φ * X ^ n :=
  MvPowerSeries.X_pow_mul

@[simp]
/--
theorem `coeff_zero_eq_constantCoeff` / 定理 `coeff_zero_eq_constantCoeff`

English:
theorem coeff_zero_eq_constantCoeff
  statement: ⇑(coeff (R := R) 0) = constantCoeff
  proof: by
  rw [coeff]; rw [Finsupp.single_zero]
  rfl

中文:
定理 coeff_zero_eq_constantCoeff
  结论: ⇑(coeff (R := R) 0) = constantCoeff
  证明: by
  rw [coeff]; rw [Finsupp.single_zero]
  rfl

Depends on / 依赖: Finsupp, Finsupp.single_zero, constantCoeff, single_zero
-/
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) 0) = constantCoeff := by
  rw [coeff]; rw [Finsupp.single_zero]
  rfl

/--
theorem `coeff_zero_eq_constantCoeff_apply` / 定理 `coeff_zero_eq_constantCoeff_apply`

English:
theorem coeff_zero_eq_constantCoeff_apply
  given: (φ : R⟦X⟧)
  statement: coeff 0 φ = constantCoeff φ
  proof: by
  rw [coeff_zero_eq_constantCoeff]

@[simp]

中文:
定理 coeff_zero_eq_constantCoeff_apply
  条件: (φ : R⟦X⟧)
  结论: coeff 0 φ = constantCoeff φ
  证明: by
  rw [coeff_zero_eq_constantCoeff]

@[simp]

Depends on / 依赖: coeff_zero_eq_constantCoeff
-/
theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  rw [coeff_zero_eq_constantCoeff]

@[simp]
/--
theorem `monomial_zero_eq_C` / 定理 `monomial_zero_eq_C`

English:
theorem monomial_zero_eq_C
  statement: ⇑(monomial (R := R) 0) = C
  proof: by
  -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
  rw [monomial]; rw [Finsupp.single_zero]; rw [MvPowerSeries.monomial_zero_eq_C]
  rfl

中文:
定理 monomial_zero_eq_C
  结论: ⇑(monomial (R := R) 0) = C
  证明: by
  -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
  rw [monomial]; rw [Finsupp.single_zero]; rw [MvPowerSeries.monomial_zero_eq_C]
  rfl
-/
theorem monomial_zero_eq_C : ⇑(monomial (R := R) 0) = C := by
  -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
  rw [monomial]; rw [Finsupp.single_zero]; rw [MvPowerSeries.monomial_zero_eq_C]
  rfl

/--
theorem `monomial_zero_eq_C_apply` / 定理 `monomial_zero_eq_C_apply`

English:
theorem monomial_zero_eq_C_apply
  given: (a : R)
  statement: monomial 0 a = C a
  proof: by simp

中文:
定理 monomial_zero_eq_C_apply
  条件: (a : R)
  结论: monomial 0 a = C a
  证明: by simp
-/
theorem monomial_zero_eq_C_apply (a : R) : monomial 0 a = C a := by simp

/--
theorem `coeff_C` / 定理 `coeff_C`

English:
theorem coeff_C
  given: (n : Nat) (a : R)
  statement: coeff n (C a : R⟦X⟧) = if n = 0 then a else 0
  proof: by
  rw [← monomial_zero_eq_C_apply]; rw [coeff_monomial]

@[simp]

中文:
定理 coeff_C
  条件: (n : 自然数) (a : R)
  结论: coeff n (C a : R⟦X⟧) = if n = 0 then a else 0
  证明: by
  rw [← monomial_zero_eq_C_apply]; rw [coeff_monomial]

@[simp]

Depends on / 依赖: coeff_monomial, monomial_zero_eq_C_apply
-/
theorem coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply]; rw [coeff_monomial]

@[simp]
/--
theorem `coeff_zero_C` / 定理 `coeff_zero_C`

English:
theorem coeff_zero_C
  given: (a : R)
  statement: coeff 0 (C a) = a
  proof: by
  rw [coeff_C]; rw [if_pos rfl]

中文:
定理 coeff_zero_C
  条件: (a : R)
  结论: coeff 0 (C a) = a
  证明: by
  rw [coeff_C]; rw [if_pos rfl]

Depends on / 依赖: coeff_C, if_pos
-/
theorem coeff_zero_C (a : R) : coeff 0 (C a) = a := by
  rw [coeff_C]; rw [if_pos rfl]

/--
theorem `coeff_C_of_ne_zero` / 定理 `coeff_C_of_ne_zero`

English:
theorem coeff_C_of_ne_zero
  given: {a : R} {n : Nat} (h : n != 0)
  statement: coeff n (C a) = 0
  proof: by
  rw [coeff_C]; rw [if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_ne_zero_C := coeff_C_of_ne_zero

@[simp]

中文:
定理 coeff_C_of_ne_zero
  条件: {a : R} {n : 自然数} (h : n != 0)
  结论: coeff n (C a) = 0
  证明: by
  rw [coeff_C]; rw [if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_ne_zero_C := coeff_C_of_ne_zero

@[simp]

Depends on / 依赖: coeff_C, if_neg
-/
theorem coeff_C_of_ne_zero {a : R} {n : Nat} (h : n != 0) : coeff n (C a) = 0 := by
  rw [coeff_C]; rw [if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_ne_zero_C := coeff_C_of_ne_zero

@[simp]
/--
theorem `coeff_succ_C` / 定理 `coeff_succ_C`

English:
theorem coeff_succ_C
  given: {a : R} {n : Nat}
  statement: coeff (n + 1) (C a) = 0
  proof: coeff_C_of_ne_zero n.succ_ne_zero

@[grind inj]

中文:
定理 coeff_succ_C
  条件: {a : R} {n : 自然数}
  结论: coeff (n + 1) (C a) = 0
  证明: coeff_C_of_ne_zero n.succ_ne_zero

@[grind inj]

Depends on / 依赖: coeff_C_of_ne_zero, n.succ_ne_zero, succ_ne_zero
-/
theorem coeff_succ_C {a : R} {n : Nat} : coeff (n + 1) (C a) = 0 :=
  coeff_C_of_ne_zero n.succ_ne_zero

@[grind inj]
/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  statement: Function.Injective (C (R := R))
  proof: MvPowerSeries.C_injective

中文:
定理 C_injective
  结论: 函数.单射 (C (R := R))
  证明: MvPowerSeries.C_injective

Depends on / 依赖: C_injective, MvPowerSeries, MvPowerSeries.C_injective
-/
theorem C_injective : Function.Injective (C (R := R)) := MvPowerSeries.C_injective

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton R⟦X⟧ ↔ Subsingleton R
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b => C_injective (h (C a) (C b))

中文:
定理 subsingleton_iff
  结论: 子单例 R⟦X⟧ ↔ 子单例 R
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b => C_injective (h (C a) (C b))
-/
protected theorem subsingleton_iff : Subsingleton R⟦X⟧ ↔ Subsingleton R := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b => C_injective (h (C a) (C b))

/--
theorem `X_eq` / 定理 `X_eq`

English:
theorem X_eq
  statement: (X : R⟦X⟧) = monomial 1 1
  proof: rfl

中文:
定理 X_eq
  结论: (X : R⟦X⟧) = monomial 1 1
  证明: rfl
-/
theorem X_eq : (X : R⟦X⟧) = monomial 1 1 :=
  rfl

/--
theorem `coeff_X` / 定理 `coeff_X`

English:
theorem coeff_X
  given: (n : Nat)
  statement: coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0
  proof: by
  rw [X_eq]; rw [coeff_monomial]

@[simp]

中文:
定理 coeff_X
  条件: (n : 自然数)
  结论: coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0
  证明: by
  rw [X_eq]; rw [coeff_monomial]

@[simp]

Depends on / 依赖: X_eq, coeff_monomial
-/
theorem coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0 := by
  rw [X_eq]; rw [coeff_monomial]

@[simp]
/--
theorem `coeff_zero_X` / 定理 `coeff_zero_X`

English:
theorem coeff_zero_X
  statement: coeff 0 (X : R⟦X⟧) = 0
  proof: by
  rw [coeff]; rw [Finsupp.single_zero]; rw [X]; rw [MvPowerSeries.coeff_zero_X]

@[simp]

中文:
定理 coeff_zero_X
  结论: coeff 0 (X : R⟦X⟧) = 0
  证明: by
  rw [coeff]; rw [Finsupp.single_zero]; rw [X]; rw [MvPowerSeries.coeff_zero_X]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_zero, MvPowerSeries, MvPowerSeries.coeff_zero_X, coeff_zero_X, single_zero
-/
theorem coeff_zero_X : coeff 0 (X : R⟦X⟧) = 0 := by
  rw [coeff]; rw [Finsupp.single_zero]; rw [X]; rw [MvPowerSeries.coeff_zero_X]

@[simp]
/--
theorem `coeff_one_X` / 定理 `coeff_one_X`

English:
theorem coeff_one_X
  statement: coeff 1 (X : R⟦X⟧) = 1
  proof: by rw [coeff_X, if_pos rfl]

@[simp]

中文:
定理 coeff_one_X
  结论: coeff 1 (X : R⟦X⟧) = 1
  证明: by rw [coeff_X, if_pos rfl]

@[simp]

Depends on / 依赖: coeff_X, if_pos
-/
theorem coeff_one_X : coeff 1 (X : R⟦X⟧) = 1 := by rw [coeff_X, if_pos rfl]

@[simp]
/--
theorem `X_ne_zero` / 定理 `X_ne_zero`

English:
theorem X_ne_zero
  given: [Nontrivial R]
  statement: (X : R⟦X⟧) != 0
  proof: fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff 1) H

中文:
定理 X_ne_zero
  条件: [非平凡 R]
  结论: (X : R⟦X⟧) != 0
  证明: fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff 1) H

Depends on / 依赖: coeff_one_X, congr_arg, map_zero, one_ne_zero
-/
theorem X_ne_zero [Nontrivial R] : (X : R⟦X⟧) != 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff 1) H

/--
theorem `X_pow_eq` / 定理 `X_pow_eq`

English:
theorem X_pow_eq
  given: (n : Nat)
  statement: (X : R⟦X⟧) ^ n = monomial n 1
  proof: MvPowerSeries.X_pow_eq _ n

@[simp, grind =]

中文:
定理 X_pow_eq
  条件: (n : 自然数)
  结论: (X : R⟦X⟧) ^ n = monomial n 1
  证明: MvPowerSeries.X_pow_eq _ n

@[simp, grind =]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X_pow_eq, X_pow_eq
-/
theorem X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1 :=
  MvPowerSeries.X_pow_eq _ n

@[simp, grind =]
/--
theorem `coeff_X_pow` / 定理 `coeff_X_pow`

English:
theorem coeff_X_pow
  given: (m n : Nat)
  statement: coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0
  proof: by
  rw [X_pow_eq]; rw [coeff_monomial]

中文:
定理 coeff_X_pow
  条件: (m n : 自然数)
  结论: coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0
  证明: by
  rw [X_pow_eq]; rw [coeff_monomial]

Depends on / 依赖: X_pow_eq, coeff_monomial
-/
theorem coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq]; rw [coeff_monomial]

/--
theorem `coeff_X_pow_self` / 定理 `coeff_X_pow_self`

English:
theorem coeff_X_pow_self
  given: (n : Nat)
  statement: coeff n ((X : R⟦X⟧) ^ n) = 1
  proof: by
  simp

@[simp]

中文:
定理 coeff_X_pow_self
  条件: (n : 自然数)
  结论: coeff n ((X : R⟦X⟧) ^ n) = 1
  证明: by
  simp

@[simp]
-/
theorem coeff_X_pow_self (n : Nat) : coeff n ((X : R⟦X⟧) ^ n) = 1 := by
  simp

@[simp]
/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: (n : Nat)
  statement: coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0
  proof: coeff_C n 1

中文:
定理 coeff_one
  条件: (n : 自然数)
  结论: coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0
  证明: coeff_C n 1

Depends on / 依赖: coeff_C
-/
theorem coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0 :=
  coeff_C n 1

/--
theorem `coeff_zero_one` / 定理 `coeff_zero_one`

English:
theorem coeff_zero_one
  statement: coeff 0 (1 : R⟦X⟧) = 1
  proof: coeff_zero_C 1

中文:
定理 coeff_zero_one
  结论: coeff 0 (1 : R⟦X⟧) = 1
  证明: coeff_zero_C 1

Depends on / 依赖: coeff_zero_C
-/
theorem coeff_zero_one : coeff 0 (1 : R⟦X⟧) = 1 :=
  coeff_zero_C 1

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  given: (n : Nat) (φ ψ : R⟦X⟧)
  proof: by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single]; rw [Finset.sum_map]
  rfl

@[simp]

中文:
定理 coeff_mul
  条件: (n : 自然数) (φ ψ : R⟦X⟧)
  证明: by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single]; rw [Finset.sum_map]
  rfl

@[simp]
-/
theorem coeff_mul (n : Nat) (φ ψ : R⟦X⟧) :
    coeff n (φ * ψ) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single]; rw [Finset.sum_map]
  rfl

@[simp]
/--
theorem `coeff_mul_C` / 定理 `coeff_mul_C`

English:
theorem coeff_mul_C
  given: (n : Nat) (φ : R⟦X⟧) (a : R)
  statement: coeff n (φ * C a) = coeff n φ * a
  proof: MvPowerSeries.coeff_mul_C _ φ a

@[simp]

中文:
定理 coeff_mul_C
  条件: (n : 自然数) (φ : R⟦X⟧) (a : R)
  结论: coeff n (φ * C a) = coeff n φ * a
  证明: MvPowerSeries.coeff_mul_C _ φ a

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_mul_C, coeff_mul_C
-/
theorem coeff_mul_C (n : Nat) (φ : R⟦X⟧) (a : R) : coeff n (φ * C a) = coeff n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
/--
theorem `coeff_C_mul` / 定理 `coeff_C_mul`

English:
theorem coeff_C_mul
  given: (n : Nat) (φ : R⟦X⟧) (a : R)
  statement: coeff n (C a * φ) = a * coeff n φ
  proof: MvPowerSeries.coeff_C_mul _ φ a

@[simp]

中文:
定理 coeff_C_mul
  条件: (n : 自然数) (φ : R⟦X⟧) (a : R)
  结论: coeff n (C a * φ) = a * coeff n φ
  证明: MvPowerSeries.coeff_C_mul _ φ a

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_C_mul, coeff_C_mul
-/
theorem coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coeff n (C a * φ) = a * coeff n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: {S : Type*} [Semiring S] [Module R S] (n : Nat) (φ : PowerSeries S) (a : R)
  proof: rfl

@[simp]

中文:
定理 coeff_smul
  条件: {S : 类型} [半环 S] [模 R S] (n : 自然数) (φ : 幂级数 S) (a : R)
  证明: rfl

@[simp]
-/
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : Nat) (φ : PowerSeries S) (a : R) :
    coeff n (a • φ) = a • coeff n φ :=
  rfl

@[simp]
/--
theorem `constantCoeff_smul` / 定理 `constantCoeff_smul`

English:
theorem constantCoeff_smul
  given: {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R)
  proof: rfl

中文:
定理 constantCoeff_smul
  条件: {S : 类型} [半环 S] [模 R S] (φ : 幂级数 S) (a : R)
  证明: rfl
-/
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ :=
  rfl

/--
theorem `smul_eq_C_mul` / 定理 `smul_eq_C_mul`

English:
theorem smul_eq_C_mul
  given: (f : R⟦X⟧) (a : R)
  statement: a • f = C a * f
  proof: by
  ext
  simp

@[simp]

中文:
定理 smul_eq_C_mul
  条件: (f : R⟦X⟧) (a : R)
  结论: a • f = C a * f
  证明: by
  ext
  simp

@[simp]
-/
theorem smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C a * f := by
  ext
  simp

@[simp]
/--
theorem `coeff_succ_mul_X` / 定理 `coeff_succ_mul_X`

English:
theorem coeff_succ_mul_X
  given: (n : Nat) (φ : R⟦X⟧)
  statement: coeff (n + 1) (φ * X) = coeff n φ
  proof: by
  simp only [coeff, Finsupp.single_add]
  convert! φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]

中文:
定理 coeff_succ_mul_X
  条件: (n : 自然数) (φ : R⟦X⟧)
  结论: coeff (n + 1) (φ * X) = coeff n φ
  证明: by
  simp only [coeff, Finsupp.single_add]
  convert! φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_add, coeff_add_mul_monomial, convert, mul_one, single, single_add
-/
theorem coeff_succ_mul_X (n : Nat) (φ : R⟦X⟧) : coeff (n + 1) (φ * X) = coeff n φ := by
  simp only [coeff, Finsupp.single_add]
  convert! φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]
/--
theorem `coeff_succ_X_mul` / 定理 `coeff_succ_X_mul`

English:
theorem coeff_succ_X_mul
  given: (n : Nat) (φ : R⟦X⟧)
  statement: coeff (n + 1) (X * φ) = coeff n φ
  proof: by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert! φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]

中文:
定理 coeff_succ_X_mul
  条件: (n : 自然数) (φ : R⟦X⟧)
  结论: coeff (n + 1) (X * φ) = coeff n φ
  证明: by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert! φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]

Depends on / 依赖: Finsupp, Finsupp.single_add, add_comm, coeff_add_monomial_mul, convert, one_mul, single, single_add
-/
theorem coeff_succ_X_mul (n : Nat) (φ : R⟦X⟧) : coeff (n + 1) (X * φ) = coeff n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert! φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]

/--
theorem `mul_X_cancel` / 定理 `mul_X_cancel`

English:
theorem mul_X_cancel
  given: {φ ψ : R⟦X⟧} (h : φ * X = ψ * X)
  statement: φ = ψ
  proof: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

中文:
定理 mul_X_cancel
  条件: {φ ψ : R⟦X⟧} (h : φ * X = ψ * X)
  结论: φ = ψ
  证明: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff
-/
theorem mul_X_cancel {φ ψ : R⟦X⟧} (h : φ * X = ψ * X) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

/--
theorem `mul_X_injective` / 定理 `mul_X_injective`

English:
theorem mul_X_injective
  statement: Function.Injective (· * X : R⟦X⟧ -> R⟦X⟧)
  proof: fun _ _ => mul_X_cancel

中文:
定理 mul_X_injective
  结论: 函数.单射 (· * X : R⟦X⟧ -> R⟦X⟧)
  证明: fun _ _ => mul_X_cancel

Depends on / 依赖: mul_X_cancel
-/
theorem mul_X_injective : Function.Injective (· * X : R⟦X⟧ -> R⟦X⟧) :=
  fun _ _ => mul_X_cancel

/--
theorem `mul_X_inj` / 定理 `mul_X_inj`

English:
theorem mul_X_inj
  given: {φ ψ : R⟦X⟧}
  statement: φ * X = ψ * X ↔ φ = ψ
  proof: mul_X_injective.eq_iff

中文:
定理 mul_X_inj
  条件: {φ ψ : R⟦X⟧}
  结论: φ * X = ψ * X ↔ φ = ψ
  证明: mul_X_injective.eq_iff

Depends on / 依赖: eq_iff, mul_X_injective, mul_X_injective.eq_iff
-/
theorem mul_X_inj {φ ψ : R⟦X⟧} : φ * X = ψ * X ↔ φ = ψ :=
  mul_X_injective.eq_iff

/--
theorem `X_mul_cancel` / 定理 `X_mul_cancel`

English:
theorem X_mul_cancel
  given: {φ ψ : R⟦X⟧} (h : X * φ = X * ψ)
  statement: φ = ψ
  proof: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

中文:
定理 X_mul_cancel
  条件: {φ ψ : R⟦X⟧} (h : X * φ = X * ψ)
  结论: φ = ψ
  证明: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff
-/
theorem X_mul_cancel {φ ψ : R⟦X⟧} (h : X * φ = X * ψ) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

/--
theorem `X_mul_injective` / 定理 `X_mul_injective`

English:
theorem X_mul_injective
  statement: Function.Injective (X * · : R⟦X⟧ -> R⟦X⟧)
  proof: fun _ _ => X_mul_cancel

中文:
定理 X_mul_injective
  结论: 函数.单射 (X * · : R⟦X⟧ -> R⟦X⟧)
  证明: fun _ _ => X_mul_cancel

Depends on / 依赖: X_mul_cancel
-/
theorem X_mul_injective : Function.Injective (X * · : R⟦X⟧ -> R⟦X⟧) :=
  fun _ _ => X_mul_cancel

/--
theorem `X_mul_inj` / 定理 `X_mul_inj`

English:
theorem X_mul_inj
  given: {φ ψ : R⟦X⟧}
  statement: X * φ = X * ψ ↔ φ = ψ
  proof: X_mul_injective.eq_iff

@[simp]

中文:
定理 X_mul_inj
  条件: {φ ψ : R⟦X⟧}
  结论: X * φ = X * ψ ↔ φ = ψ
  证明: X_mul_injective.eq_iff

@[simp]

Depends on / 依赖: X_mul_injective, X_mul_injective.eq_iff, eq_iff
-/
theorem X_mul_inj {φ ψ : R⟦X⟧} : X * φ = X * ψ ↔ φ = ψ :=
  X_mul_injective.eq_iff

@[simp]
/--
theorem `constantCoeff_C` / 定理 `constantCoeff_C`

English:
theorem constantCoeff_C
  given: (a : R)
  statement: constantCoeff (C a) = a
  proof: rfl

@[simp]

中文:
定理 constantCoeff_C
  条件: (a : R)
  结论: constantCoeff (C a) = a
  证明: rfl

@[simp]
-/
theorem constantCoeff_C (a : R) : constantCoeff (C a) = a :=
  rfl

@[simp]
/--
theorem `constantCoeff_comp_C` / 定理 `constantCoeff_comp_C`

English:
theorem constantCoeff_comp_C
  statement: constantCoeff.comp C = RingHom.id R
  proof: rfl

@[simp]

中文:
定理 constantCoeff_comp_C
  结论: constantCoeff.comp C = 环态射.id R
  证明: rfl

@[simp]
-/
theorem constantCoeff_comp_C : constantCoeff.comp C = RingHom.id R :=
  rfl

@[simp]
/--
theorem `constantCoeff_zero` / 定理 `constantCoeff_zero`

English:
theorem constantCoeff_zero
  statement: constantCoeff (R := R) 0 = 0
  proof: rfl

@[simp]

中文:
定理 constantCoeff_zero
  结论: constantCoeff (R := R) 0 = 0
  证明: rfl

@[simp]
-/
theorem constantCoeff_zero : constantCoeff (R := R) 0 = 0 :=
  rfl

@[simp]
/--
theorem `constantCoeff_one` / 定理 `constantCoeff_one`

English:
theorem constantCoeff_one
  statement: constantCoeff (R := R) 1 = 1
  proof: rfl

@[simp]

中文:
定理 constantCoeff_one
  结论: constantCoeff (R := R) 1 = 1
  证明: rfl

@[simp]
-/
theorem constantCoeff_one : constantCoeff (R := R) 1 = 1 :=
  rfl

@[simp]
/--
theorem `constantCoeff_X` / 定理 `constantCoeff_X`

English:
theorem constantCoeff_X
  statement: constantCoeff (R := R) X = 0
  proof: MvPowerSeries.coeff_zero_X _

@[simp]

中文:
定理 constantCoeff_X
  结论: constantCoeff (R := R) X = 0
  证明: MvPowerSeries.coeff_zero_X _

@[simp]
-/
theorem constantCoeff_X : constantCoeff (R := R) X = 0 :=
  MvPowerSeries.coeff_zero_X _

@[simp]
/--
theorem `constantCoeff_mk` / 定理 `constantCoeff_mk`

English:
theorem constantCoeff_mk
  given: {f : Nat -> R}
  statement: constantCoeff (mk f) = f 0
  proof: rfl

中文:
定理 constantCoeff_mk
  条件: {f : 自然数 -> R}
  结论: constantCoeff (mk f) = f 0
  证明: rfl
-/
theorem constantCoeff_mk {f : Nat -> R} : constantCoeff (mk f) = f 0 := rfl

/--
theorem `coeff_zero_mul_X` / 定理 `coeff_zero_mul_X`

English:
theorem coeff_zero_mul_X
  given: (φ : R⟦X⟧)
  statement: coeff 0 (φ * X) = 0
  proof: by simp

中文:
定理 coeff_zero_mul_X
  条件: (φ : R⟦X⟧)
  结论: coeff 0 (φ * X) = 0
  证明: by simp
-/
theorem coeff_zero_mul_X (φ : R⟦X⟧) : coeff 0 (φ * X) = 0 := by simp

/--
theorem `coeff_zero_X_mul` / 定理 `coeff_zero_X_mul`

English:
theorem coeff_zero_X_mul
  given: (φ : R⟦X⟧)
  statement: coeff 0 (X * φ) = 0
  proof: by simp

中文:
定理 coeff_zero_X_mul
  条件: (φ : R⟦X⟧)
  结论: coeff 0 (X * φ) = 0
  证明: by simp
-/
theorem coeff_zero_X_mul (φ : R⟦X⟧) : coeff 0 (X * φ) = 0 := by simp

/--
theorem `constantCoeff_surj` / 定理 `constantCoeff_surj`

English:
theorem constantCoeff_surj
  statement: Function.Surjective (constantCoeff (R := R))
  proof: fun r => ⟨C r, constantCoeff_C r⟩

中文:
定理 constantCoeff_surj
  结论: 函数.满射 (constantCoeff (R := R))
  证明: fun r => ⟨C r, constantCoeff_C r⟩
-/
theorem constantCoeff_surj : Function.Surjective (constantCoeff (R := R)) :=
  fun r => ⟨C r, constantCoeff_C r⟩

-- The following section duplicates the API of `Mathlib.Data.Polynomial.Coeff` and should attempt
-- to keep up to date with that
section

/--
theorem `coeff_C_mul_X_pow` / 定理 `coeff_C_mul_X_pow`

English:
theorem coeff_C_mul_X_pow
  given: (x : R) (k n : Nat)
  proof: by
  simp [X_pow_eq, coeff_monomial]

@[simp]

中文:
定理 coeff_C_mul_X_pow
  条件: (x : R) (k n : 自然数)
  证明: by
  simp [X_pow_eq, coeff_monomial]

@[simp]

Depends on / 依赖: X_pow_eq, coeff_monomial
-/
theorem coeff_C_mul_X_pow (x : R) (k n : Nat) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]

@[simp]
/--
theorem `coeff_mul_X_pow` / 定理 `coeff_mul_X_pow`

English:
theorem coeff_mul_X_pow
  given: (p : R⟦X⟧) (n d : Nat)
  proof: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact f

中文:
定理 coeff_mul_X_pow
  条件: (p : R⟦X⟧) (n d : 自然数)
  证明: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact f

Depends on / 依赖: Finset, Finset.sum_eq_single, add_right_cancel_iff, coeff_X_pow, coeff_mul, if_neg, if_pos, mem_antidiagonal, mul_one, mul_zero, sum_eq_single
-/
theorem coeff_mul_X_pow (p : R⟦X⟧) (n d : Nat) :
    coeff (d + n) (p * X ^ n) = coeff d p := by
  rw [coeff_mul]; rw [Finset.sum_eq_single (d]; rw [n)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

@[simp]
/--
theorem `coeff_X_pow_mul` / 定理 `coeff_X_pow_mul`

English:
theorem coeff_X_pow_mul
  given: (p : R⟦X⟧) (n d : Nat)
  proof: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (n]; rw [d)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_comm]; rw [add_right_cancel_iff] at h1
    subst h1
    

中文:
定理 coeff_X_pow_mul
  条件: (p : R⟦X⟧) (n d : 自然数)
  证明: by
  rw [coeff_mul]; rw [Finset.sum_eq_single (n]; rw [d)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_comm]; rw [add_right_cancel_iff] at h1
    subst h1
    

Depends on / 依赖: Finset, Finset.sum_eq_single, add_comm, add_right_cancel_iff, coeff_X_pow, coeff_mul, if_neg, if_pos, mem_antidiagonal, one_mul, sum_eq_single, zero_mul
-/
theorem coeff_X_pow_mul (p : R⟦X⟧) (n d : Nat) :
    coeff (d + n) (X ^ n * p) = coeff d p := by
  rw [coeff_mul]; rw [Finset.sum_eq_single (n]; rw [d)]; rw [coeff_X_pow]; rw [if_pos rfl]; rw [one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal]; rw [add_comm]; rw [add_right_cancel_iff] at h1
    subst h1
    rfl
  · rw [add_comm]
    exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

/--
theorem `mul_X_pow_cancel` / 定理 `mul_X_pow_cancel`

English:
theorem mul_X_pow_cancel
  given: {k : Nat} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k)
  proof: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

中文:
定理 mul_X_pow_cancel
  条件: {k : 自然数} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k)
  证明: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff
-/
theorem mul_X_pow_cancel {k : Nat} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

/--
theorem `mul_X_pow_injective` / 定理 `mul_X_pow_injective`

English:
theorem mul_X_pow_injective
  given: {k : Nat}
  statement: Function.Injective (· * X ^ k : R⟦X⟧ -> R⟦X⟧)
  proof: fun _ _ => mul_X_pow_cancel

中文:
定理 mul_X_pow_injective
  条件: {k : 自然数}
  结论: 函数.单射 (· * X ^ k : R⟦X⟧ -> R⟦X⟧)
  证明: fun _ _ => mul_X_pow_cancel

Depends on / 依赖: mul_X_pow_cancel
-/
theorem mul_X_pow_injective {k : Nat} : Function.Injective (· * X ^ k : R⟦X⟧ -> R⟦X⟧) :=
  fun _ _ => mul_X_pow_cancel

/--
theorem `mul_X_pow_inj` / 定理 `mul_X_pow_inj`

English:
theorem mul_X_pow_inj
  given: {k : Nat} {φ ψ : R⟦X⟧}
  proof: mul_X_pow_injective.eq_iff

中文:
定理 mul_X_pow_inj
  条件: {k : 自然数} {φ ψ : R⟦X⟧}
  证明: mul_X_pow_injective.eq_iff

Depends on / 依赖: eq_iff, mul_X_pow_injective, mul_X_pow_injective.eq_iff
-/
theorem mul_X_pow_inj {k : Nat} {φ ψ : R⟦X⟧} :
    φ * X ^ k = ψ * X ^ k ↔ φ = ψ :=
  mul_X_pow_injective.eq_iff

/--
theorem `X_pow_mul_cancel` / 定理 `X_pow_mul_cancel`

English:
theorem X_pow_mul_cancel
  given: {k : Nat} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ)
  proof: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

中文:
定理 X_pow_mul_cancel
  条件: {k : 自然数} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ)
  证明: by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff
-/
theorem X_pow_mul_cancel {k : Nat} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

/--
theorem `X_pow_mul_injective` / 定理 `X_pow_mul_injective`

English:
theorem X_pow_mul_injective
  given: {k : Nat}
  statement: Function.Injective (X ^ k * · : R⟦X⟧ -> R⟦X⟧)
  proof: fun _ _ => X_pow_mul_cancel

中文:
定理 X_pow_mul_injective
  条件: {k : 自然数}
  结论: 函数.单射 (X ^ k * · : R⟦X⟧ -> R⟦X⟧)
  证明: fun _ _ => X_pow_mul_cancel

Depends on / 依赖: X_pow_mul_cancel
-/
theorem X_pow_mul_injective {k : Nat} : Function.Injective (X ^ k * · : R⟦X⟧ -> R⟦X⟧) :=
  fun _ _ => X_pow_mul_cancel

/--
theorem `X_pow_mul_inj` / 定理 `X_pow_mul_inj`

English:
theorem X_pow_mul_inj
  given: {k : Nat} {φ ψ : R⟦X⟧}
  proof: X_pow_mul_injective.eq_iff

中文:
定理 X_pow_mul_inj
  条件: {k : 自然数} {φ ψ : R⟦X⟧}
  证明: X_pow_mul_injective.eq_iff

Depends on / 依赖: X_pow_mul_injective, X_pow_mul_injective.eq_iff, eq_iff
-/
theorem X_pow_mul_inj {k : Nat} {φ ψ : R⟦X⟧} :
    X ^ k * φ = X ^ k * ψ ↔ φ = ψ :=
  X_pow_mul_injective.eq_iff

/--
theorem `coeff_mul_X_pow'` / 定理 `coeff_mul_X_pow'`

English:
theorem coeff_mul_X_pow'
  given: (p : R⟦X⟧) (n d : Nat)
  proof: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h

中文:
定理 coeff_mul_X_pow'
  条件: (p : R⟦X⟧) (n d : 自然数)
  证明: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h

Depends on / 依赖: Finset, Finset.sum_eq_zero, add_tsub_cancel_right, coeff_X_pow, coeff_mul, coeff_mul_X_pow, if_neg, le_of_add_le_right, mem_antidiagonal, mem_antidiagonal.mp, mul_zero, not_le, not_le.mp, split_ifs, sum_eq_zero, trans_lt, tsub_add_cancel_of_le
-/
theorem coeff_mul_X_pow' (p : R⟦X⟧) (n d : Nat) :
    coeff d (p * X ^ n) = ite (n <= d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

/--
theorem `coeff_X_pow_mul'` / 定理 `coeff_X_pow_mul'`

English:
theorem coeff_X_pow_mul'
  given: (p : R⟦X⟧) (n d : Nat)
  proof: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.

中文:
定理 coeff_X_pow_mul'
  条件: (p : R⟦X⟧) (n d : 自然数)
  证明: by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.

Depends on / 依赖: Finset, Finset.sum_eq_zero, add_comm, bot_le, coeff_X_pow, coeff_X_pow_mul, coeff_mul, if_neg, le_of_add_le_right, mem_antidiagonal, mem_antidiagonal.mp, not_le, not_le.mp, split_ifs, sum_eq_zero, this.le, trans_lt, tsub_add_cancel_of_le, zero_mul
-/
theorem coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) :
    coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow]; rw [if_neg]; rw [zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne

end

/--
theorem `isUnit_constantCoeff` / 定理 `isUnit_constantCoeff`

English:
theorem isUnit_constantCoeff
  given: (φ : R⟦X⟧) (h : IsUnit φ)
  statement: IsUnit (constantCoeff φ)
  proof: MvPowerSeries.isUnit_constantCoeff φ h

中文:
定理 isUnit_constantCoeff
  条件: (φ : R⟦X⟧) (h : 是单位 φ)
  结论: 是单位 (constantCoeff φ)
  证明: MvPowerSeries.isUnit_constantCoeff φ h

Depends on / 依赖: MvPowerSeries, MvPowerSeries.isUnit_constantCoeff, isUnit_constantCoeff
-/
theorem isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h

/--
theorem `eq_shift_mul_X_add_const` / 定理 `eq_shift_mul_X_add_const`

English:
theorem eq_shift_mul_X_add_const
  given: (φ : R⟦X⟧)
  proof: by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_mul_X, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

中文:
定理 eq_shift_mul_X_add_const
  条件: (φ : R⟦X⟧)
  证明: by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_mul_X, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

Depends on / 依赖: Bornology, BoundedSpace, BoundedSpace.of_finite, Finite, add_zero, coeff_C, coeff_mk, coeff_succ_mul_X, if_false, map_add, n.succ_ne_zero, of_finite, succ_ne_zero
-/
theorem eq_shift_mul_X_add_const (φ : R⟦X⟧) :
    φ = (mk fun p => coeff (p + 1) φ) * X + C (constantCoeff φ) := by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_mul_X, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

/--
theorem `eq_X_mul_shift_add_const` / 定理 `eq_X_mul_shift_add_const`

English:
theorem eq_X_mul_shift_add_const
  given: (φ : R⟦X⟧)
  proof: by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_X_mul, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

中文:
定理 eq_X_mul_shift_add_const
  条件: (φ : R⟦X⟧)
  证明: by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_X_mul, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

Depends on / 依赖: add_zero, coeff_C, coeff_mk, coeff_succ_X_mul, if_false, map_add, n.succ_ne_zero, succ_ne_zero
-/
theorem eq_X_mul_shift_add_const (φ : R⟦X⟧) :
    φ = (X * mk fun p => coeff (p + 1) φ) + C (constantCoeff φ) := by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_X_mul, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]
variable (f : R ->+* S) (g : S ->+* T)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : R⟦X⟧ ->+* S⟦X⟧
  body: MvPowerSeries.map f

@[simp]

中文:
定义 map
  签名: : R⟦X⟧ ->+* S⟦X⟧
  定义体: MvPowerSeries.map f

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map
-/
def map : R⟦X⟧ ->+* S⟦X⟧ :=
  MvPowerSeries.map f

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: (map (RingHom.id R) : R⟦X⟧ -> R⟦X⟧) = id
  proof: rfl

中文:
定理 map_id
  结论: (map (环态射.id R) : R⟦X⟧ -> R⟦X⟧) = id
  证明: rfl
-/
theorem map_id : (map (RingHom.id R) : R⟦X⟧ -> R⟦X⟧) = id :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

@[simp]

中文:
定理 map_comp
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl

@[simp]
-/
theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
/--
theorem `coeff_map` / 定理 `coeff_map`

English:
theorem coeff_map
  given: (n : Nat) (φ : R⟦X⟧)
  statement: coeff n (map f φ) = f (coeff n φ)
  proof: rfl

@[simp]

中文:
定理 coeff_map
  条件: (n : 自然数) (φ : R⟦X⟧)
  结论: coeff n (map f φ) = f (coeff n φ)
  证明: rfl

@[simp]
-/
theorem coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  given: (r : R)
  statement: map f (C r) = C (f r)
  proof: by
  ext
  simp [coeff_C, apply_ite f]

@[simp]

中文:
定理 map_C
  条件: (r : R)
  结论: map f (C r) = C (f r)
  证明: by
  ext
  simp [coeff_C, apply_ite f]

@[simp]

Depends on / 依赖: apply_ite, coeff_C
-/
theorem map_C (r : R) : map f (C r) = C (f r) := by
  ext
  simp [coeff_C, apply_ite f]

@[simp]
/--
theorem `map_X` / 定理 `map_X`

English:
theorem map_X
  statement: map f X = X
  proof: by
  ext
  simp [coeff_X, apply_ite f]

中文:
定理 map_X
  结论: map f X = X
  证明: by
  ext
  simp [coeff_X, apply_ite f]

Depends on / 依赖: apply_ite, coeff_X
-/
theorem map_X : map f X = X := by
  ext
  simp [coeff_X, apply_ite f]

/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (f : S ->+* T) (hf : Function.Surjective f)
  proof: by
  intro g
  use PowerSeries.mk fun k => Function.surjInv hf (PowerSeries.coeff k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf (coeff k g))

中文:
定理 map_surjective
  条件: (f : S ->+* T) (hf : 函数.满射 f)
  证明: by
  intro g
  use PowerSeries.mk fun k => Function.surjInv hf (PowerSeries.coeff k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf (coeff k g))

Depends on / 依赖: Classical, Classical.choose_spec, Function, Function.surjInv, PowerSeries, PowerSeries.coeff, PowerSeries.mk, choose_spec, coeff_map, coeff_mk, surjInv
-/
theorem map_surjective (f : S ->+* T) (hf : Function.Surjective f) :
    Function.Surjective (PowerSeries.map f) := by
  intro g
  use PowerSeries.mk fun k => Function.surjInv hf (PowerSeries.coeff k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf (coeff k g))

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : S ->+* T) (hf : Function.Injective ⇑f)
  proof: by
  intro u v huv
  ext k
  apply hf
  rw [← PowerSeries.coeff_map]; rw [← PowerSeries.coeff_map]; rw [huv]

中文:
定理 map_injective
  条件: (f : S ->+* T) (hf : 函数.单射 ⇑f)
  证明: by
  intro u v huv
  ext k
  apply hf
  rw [← PowerSeries.coeff_map]; rw [← PowerSeries.coeff_map]; rw [huv]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_map, coeff_map
-/
theorem map_injective (f : S ->+* T) (hf : Function.Injective ⇑f) :
    Function.Injective (PowerSeries.map f) := by
  intro u v huv
  ext k
  apply hf
  rw [← PowerSeries.coeff_map]; rw [← PowerSeries.coeff_map]; rw [huv]

end Map

@[simp]
/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  statement: {R S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S] (φ : R⟦X⟧)
  proof: MvPowerSeries.map_eq_zero _ _

中文:
定理 map_eq_zero
  结论: {R S : 类型} [除半环 R] [半环 S] [非平凡 S] (φ : R⟦X⟧)
  证明: MvPowerSeries.map_eq_zero _ _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map_eq_zero, map_eq_zero
-/
theorem map_eq_zero {R S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S] (φ : R⟦X⟧)
    (f : R ->+* S) : φ.map f = 0 ↔ φ = 0 :=
  MvPowerSeries.map_eq_zero _ _

/--
theorem `X_pow_dvd_iff` / 定理 `X_pow_dvd_iff`

English:
theorem X_pow_dvd_iff
  given: {n : Nat} {φ : R⟦X⟧}
  proof: by
  convert! @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert! h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm

中文:
定理 X_pow_dvd_iff
  条件: {n : 自然数} {φ : R⟦X⟧}
  证明: by
  convert! @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert! h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm

Depends on / 依赖: Finsupp, Finsupp.single_eq_same, Finsupp.unique_single, MvPowerSeries, MvPowerSeries.X_pow_dvd_iff, X_pow_dvd_iff, convert, single_eq_same, unique_single
-/
theorem X_pow_dvd_iff {n : Nat} {φ : R⟦X⟧} :
    (X : R⟦X⟧) ^ n ∣ φ ↔ forall m, m < n -> coeff m φ = 0 := by
  convert! @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert! h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm

/--
theorem `X_dvd_iff` / 定理 `X_dvd_iff`

English:
theorem X_dvd_iff
  given: {φ : R⟦X⟧}
  statement: (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0
  proof: by
  rw [← pow_one (X : R⟦X⟧)]; rw [X_pow_dvd_iff]; rw [← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

中文:
定理 X_dvd_iff
  条件: {φ : R⟦X⟧}
  结论: (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0
  证明: by
  rw [← pow_one (X : R⟦X⟧)]; rw [X_pow_dvd_iff]; rw [← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

Depends on / 依赖: Nat.eq_zero_of_le_zero, Nat.le_of_succ_le_succ, X_pow_dvd_iff, coeff_zero_eq_constantCoeff_apply, eq_zero_of_le_zero, le_of_succ_le_succ, pow_one, zero_lt_one
-/
theorem X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0 := by
  rw [← pow_one (X : R⟦X⟧)]; rw [X_pow_dvd_iff]; rw [← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

end Semiring

section toSubring

variable [Ring R] (p : PowerSeries R) (T : Subring R) (hp : forall n, p.coeff n in T)

/--
Definition of `toSubring` / `toSubring` 的定义

English:
definition toSubring
  signature: : PowerSeries T
  body: mk fun n => ⟨p.coeff n, hp n⟩

@[simp]

中文:
定义 toSubring
  签名: : 幂级数 T
  定义体: mk fun n => ⟨p.coeff n, hp n⟩

@[simp]

Depends on / 依赖: p.coeff
-/
def toSubring : PowerSeries T := mk fun n => ⟨p.coeff n, hp n⟩

@[simp]
/--
theorem `coeff_toSubring` / 定理 `coeff_toSubring`

English:
theorem coeff_toSubring
  given: {n : Nat}
  statement: (p.toSubring T hp).coeff n = p.coeff n
  proof: by
  rw [toSubring]; rw [coeff_mk]

@[simp]

中文:
定理 coeff_toSubring
  条件: {n : 自然数}
  结论: (p.toSubring T hp).coeff n = p.coeff n
  证明: by
  rw [toSubring]; rw [coeff_mk]

@[simp]

Depends on / 依赖: coeff_mk, toSubring
-/
theorem coeff_toSubring {n : Nat} : (p.toSubring T hp).coeff n = p.coeff n := by
  rw [toSubring]; rw [coeff_mk]

@[simp]
/--
theorem `constantCoeff_toSubring` / 定理 `constantCoeff_toSubring`

English:
theorem constantCoeff_toSubring
  statement: (p.toSubring T hp).constantCoeff = p.constantCoeff
  proof: coeff_zero_eq_constantCoeff_apply p

@[simp]

中文:
定理 constantCoeff_toSubring
  结论: (p.toSubring T hp).constantCoeff = p.constantCoeff
  证明: coeff_zero_eq_constantCoeff_apply p

@[simp]

Depends on / 依赖: coeff_zero_eq_constantCoeff_apply
-/
theorem constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoeff :=
  coeff_zero_eq_constantCoeff_apply p

@[simp]
/--
theorem `map_toSubring` / 定理 `map_toSubring`

English:
theorem map_toSubring
  statement: (p.toSubring T hp).map T.subtype = p
  proof: ext fun n => by simp

中文:
定理 map_toSubring
  结论: (p.toSubring T hp).map T.subtype = p
  证明: ext fun n => by simp
-/
theorem map_toSubring : (p.toSubring T hp).map T.subtype = p := ext fun n => by simp

end toSubring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/--
Definition of `rescale` / `rescale` 的定义

English:
definition rescale
  signature: (a : R)
  body: PowerSeries.mk fun n => a ^ n * PowerSeries.coeff n f
  map_zero' := by
    ext
    simp only [map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' :

中文:
定义 rescale
  签名: (a : R)
  定义体: PowerSeries.mk fun n => a ^ n * PowerSeries.coeff n f
  map_zero' := by
    ext
    simp only [map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' :

Depends on / 依赖: PowerSeries, PowerSeries.coeff, PowerSeries.mk
-/
noncomputable def rescale (a : R) : R⟦X⟧ ->+* R⟦X⟧ where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff n f
  map_zero' := by
    ext
    simp only [map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' := by
    intros
    ext
    exact mul_add _ _ _
  map_mul' f g := by
    ext
    rw [PowerSeries.coeff_mul]; rw [PowerSeries.coeff_mk]; rw [PowerSeries.coeff_mul]; rw [Finset.mul_sum]
    apply sum_congr rfl
    simp only [coeff_mk, Prod.forall, mem_antidiagonal]
    intro b c H
    rw [← H]; rw [pow_add]; rw [mul_mul_mul_comm]

@[simp]
/--
theorem `coeff_rescale` / 定理 `coeff_rescale`

English:
theorem coeff_rescale
  given: (f : R⟦X⟧) (a : R) (n : Nat)
  proof: coeff_mk n (fun n => a ^ n * coeff n f)

@[simp]

中文:
定理 coeff_rescale
  条件: (f : R⟦X⟧) (a : R) (n : 自然数)
  证明: coeff_mk n (fun n => a ^ n * coeff n f)

@[simp]

Depends on / 依赖: coeff_mk
-/
theorem coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) :
    coeff n (rescale a f) = a ^ n * coeff n f :=
  coeff_mk n (fun n => a ^ n * coeff n f)

@[simp]
/--
theorem `rescale_zero` / 定理 `rescale_zero`

English:
theorem rescale_zero
  statement: rescale 0 = (C (R := R)).comp constantCoeff
  proof: by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    coeff_C]
  split_ifs with h <;> simp [h]

中文:
定理 rescale_zero
  结论: rescale 0 = (C (R := R)).comp constantCoeff
  证明: by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    coeff_C]
  split_ifs with h <;> simp [h]

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, RingHom.coe_mk, coe_comp, coe_mk, coeff_C, comp_apply, constantCoeff, rescale, split_ifs
-/
theorem rescale_zero : rescale 0 = (C (R := R)).comp constantCoeff := by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    coeff_C]
  split_ifs with h <;> simp [h]

/--
theorem `rescale_zero_apply` / 定理 `rescale_zero_apply`

English:
theorem rescale_zero_apply
  given: (f : R⟦X⟧)
  statement: rescale 0 f = C (constantCoeff f)
  proof: by simp

@[simp]

中文:
定理 rescale_zero_apply
  条件: (f : R⟦X⟧)
  结论: rescale 0 f = C (constantCoeff f)
  证明: by simp

@[simp]
-/
theorem rescale_zero_apply (f : R⟦X⟧) : rescale 0 f = C (constantCoeff f) := by simp

@[simp]
/--
theorem `rescale_one` / 定理 `rescale_one`

English:
theorem rescale_one
  statement: rescale 1 = RingHom.id R⟦X⟧
  proof: by
  ext
  simp [coeff_rescale]

中文:
定理 rescale_one
  结论: rescale 1 = 环态射.id R⟦X⟧
  证明: by
  ext
  simp [coeff_rescale]

Depends on / 依赖: coeff_rescale
-/
theorem rescale_one : rescale 1 = RingHom.id R⟦X⟧ := by
  ext
  simp [coeff_rescale]

/--
theorem `rescale_mk` / 定理 `rescale_mk`

English:
theorem rescale_mk
  given: (f : Nat -> R) (a : R)
  statement: rescale a (mk f) = mk fun n : Nat => a ^ n * f n
  proof: by
  ext
  rw [coeff_rescale]; rw [coeff_mk]; rw [coeff_mk]

中文:
定理 rescale_mk
  条件: (f : 自然数 -> R) (a : R)
  结论: rescale a (mk f) = mk fun n : 自然数 => a ^ n * f n
  证明: by
  ext
  rw [coeff_rescale]; rw [coeff_mk]; rw [coeff_mk]

Depends on / 依赖: coeff_mk, coeff_rescale
-/
theorem rescale_mk (f : Nat -> R) (a : R) : rescale a (mk f) = mk fun n : Nat => a ^ n * f n := by
  ext
  rw [coeff_rescale]; rw [coeff_mk]; rw [coeff_mk]

/--
theorem `rescale_rescale` / 定理 `rescale_rescale`

English:
theorem rescale_rescale
  given: (f : R⟦X⟧) (a b : R)
  proof: by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow]; rw [mul_comm _ (b ^ n)]; rw [mul_assoc]

中文:
定理 rescale_rescale
  条件: (f : R⟦X⟧) (a b : R)
  证明: by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow]; rw [mul_comm _ (b ^ n)]; rw [mul_assoc]

Depends on / 依赖: coeff_rescale, mul_assoc, mul_comm, mul_pow, simp_rw
-/
theorem rescale_rescale (f : R⟦X⟧) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow]; rw [mul_comm _ (b ^ n)]; rw [mul_assoc]

/--
theorem `rescale_mul` / 定理 `rescale_mul`

English:
theorem rescale_mul
  given: (a b : R)
  statement: rescale (a * b) = (rescale b).comp (rescale a)
  proof: by
  ext
  simp [← rescale_rescale]

中文:
定理 rescale_mul
  条件: (a b : R)
  结论: rescale (a * b) = (rescale b).comp (rescale a)
  证明: by
  ext
  simp [← rescale_rescale]

Depends on / 依赖: rescale_rescale
-/
theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]

/--
theorem `rescale_map` / 定理 `rescale_map`

English:
theorem rescale_map
  given: {S : Type*} [CommSemiring S] (φ : R ->+* S) (r : R) (f : R⟦X⟧)
  proof: by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]

中文:
定理 rescale_map
  条件: {S : 类型} [交换半环 S] (φ : R ->+* S) (r : R) (f : R⟦X⟧)
  证明: by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]

Depends on / 依赖: coeff_map, coeff_rescale, map_mul, map_pow
-/
theorem rescale_map {S : Type*} [CommSemiring S] (φ : R ->+* S) (r : R) (f : R⟦X⟧) :
    rescale (φ r) (f.map φ) = (rescale r f).map (φ : R ->+* S) := by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]

/--
theorem `rescale_algebraMap_map` / 定理 `rescale_algebraMap_map`

English:
theorem rescale_algebraMap_map
  statement: {A S : Type*} [CommSemiring A] [Algebra A R] [CommSemiring S]
  proof: by
  convert! rescale_map (φ : R ->+* S) _ _
  simp

中文:
定理 rescale_algebraMap_map
  结论: {A S : 类型} [交换半环 A] [代数 A R] [交换半环 S]
  证明: by
  convert! rescale_map (φ : R ->+* S) _ _
  simp

Depends on / 依赖: Bornology, Bornology.induced, Subtype, Subtype.val, convert, induced, rescale_map
-/
theorem rescale_algebraMap_map {A S : Type*} [CommSemiring A] [Algebra A R] [CommSemiring S]
    [Algebra A S] (φ : R ->ₐ[A] S) (a : A) (f : R⟦X⟧) :
    rescale (algebraMap A S a) (f.map φ) = (rescale (algebraMap A R a) f).map φ := by
  convert! rescale_map (φ : R ->+* S) _ _
  simp

end CommSemiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*}

/--
theorem `coeff_prod` / 定理 `coeff_prod`

English:
theorem coeff_prod
  given: [DecidableEq ι] (f : ι -> PowerSeries R) (d : Nat) (s : Finset ι)
  proof: by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod]; rw [← Finsupp.uniqueAddEquiv_symm_apply _ d]; rw [← mapRange_finsuppAntidiag_eq]; rw [sum_map]
  rfl

中文:
定理 coeff_prod
  条件: [DecidableEq ι] (f : ι -> 幂级数 R) (d : 自然数) (s : 有限集 ι)
  证明: by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod]; rw [← Finsupp.uniqueAddEquiv_symm_apply _ d]; rw [← mapRange_finsuppAntidiag_eq]; rw [sum_map]
  rfl

Depends on / 依赖: Finsupp, Finsupp.uniqueAddEquiv_symm_apply, MvPowerSeries, MvPowerSeries.coeff_prod, coeff_prod, mapRange_finsuppAntidiag_eq, sum_map, uniqueAddEquiv_symm_apply
-/
theorem coeff_prod [DecidableEq ι] (f : ι -> PowerSeries R) (d : Nat) (s : Finset ι) :
    coeff d (∏ j in s, f j) = ∑ l in finsuppAntidiag s d, ∏ i in s, coeff (l i) (f i) := by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod]; rw [← Finsupp.uniqueAddEquiv_symm_apply _ d]; rw [← mapRange_finsuppAntidiag_eq]; rw [sum_map]
  rfl

/--
theorem `prod_monomial` / 定理 `prod_monomial`

English:
theorem prod_monomial
  given: (f : ι -> Nat) (g : ι -> R) (s : Finset ι)
  proof: by
  simpa [monomial, Finsupp.single_finsetSum] using
    MvPowerSeries.prod_monomial (fun i => Finsupp.single () (f i)) g s

中文:
定理 prod_monomial
  条件: (f : ι -> 自然数) (g : ι -> R) (s : 有限集 ι)
  证明: by
  simpa [monomial, Finsupp.single_finsetSum] using
    MvPowerSeries.prod_monomial (fun i => Finsupp.single () (f i)) g s

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.single_finsetSum, MvPowerSeries, MvPowerSeries.prod_monomial, monomial, prod_monomial, single, single_finsetSum
-/
theorem prod_monomial (f : ι -> Nat) (g : ι -> R) (s : Finset ι) :
    ∏ i in s, monomial (f i) (g i) = monomial (∑ i in s, f i) (∏ i in s, g i) := by
  simpa [monomial, Finsupp.single_finsetSum] using
    MvPowerSeries.prod_monomial (fun i => Finsupp.single () (f i)) g s

/--
theorem `monomial_pow` / 定理 `monomial_pow`

English:
theorem monomial_pow
  given: (m : Nat) (a : R) (n : Nat)
  statement: (monomial m a) ^ n = monomial (n * m) (a ^ n)
  proof: by
  simpa [monomial] using MvPowerSeries.monomial_pow (Finsupp.single () m) a n

中文:
定理 monomial_pow
  条件: (m : 自然数) (a : R) (n : 自然数)
  结论: (monomial m a) ^ n = monomial (n * m) (a ^ n)
  证明: by
  simpa [monomial] using MvPowerSeries.monomial_pow (Finsupp.single () m) a n

Depends on / 依赖: Finsupp, Finsupp.single, MvPowerSeries, MvPowerSeries.monomial_pow, monomial, monomial_pow, single
-/
theorem monomial_pow (m : Nat) (a : R) (n : Nat) : (monomial m a) ^ n = monomial (n * m) (a ^ n) := by
  simpa [monomial] using MvPowerSeries.monomial_pow (Finsupp.single () m) a n

/--
lemma `coeff_pow` / 引理 `coeff_pow`

English:
lemma coeff_pow
  given: (k n : Nat) (φ : R⟦X⟧)
  proof: by
  have h₁ (i : Nat) : Function.const Nat φ i = φ := rfl
  have h₂ (i : Nat) : ∏ j in range i, Function.const Nat φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl i (fun _ => congrFun rfl)
  rw [← h₂]; rw [← h₁ k]
  apply coeff_prod (f := Function.const Nat φ) (d 

中文:
引理 coeff_pow
  条件: (k n : 自然数) (φ : R⟦X⟧)
  证明: by
  have h₁ (i : Nat) : Function.const Nat φ i = φ := rfl
  have h₂ (i : Nat) : ∏ j in range i, Function.const Nat φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl i (fun _ => congrFun rfl)
  rw [← h₂]; rw [← h₁ k]
  apply coeff_prod (f := Function.const Nat φ) (d 

Depends on / 依赖: Function, Function.const, coeff_prod, prod_range_induction
-/
lemma coeff_pow (k n : Nat) (φ : R⟦X⟧) :
    coeff n (φ ^ k) = ∑ l in finsuppAntidiag (range k) n, ∏ i in range k, coeff (l i) φ := by
  have h₁ (i : Nat) : Function.const Nat φ i = φ := rfl
  have h₂ (i : Nat) : ∏ j in range i, Function.const Nat φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl i (fun _ => congrFun rfl)
  rw [← h₂]; rw [← h₁ k]
  apply coeff_prod (f := Function.const Nat φ) (d := n) (s := range k)

/--
lemma `coeff_one_mul` / 引理 `coeff_one_mul`

English:
lemma coeff_one_mul
  given: (φ ψ : R⟦X⟧)
  statement: coeff 1 (φ * ψ) =
  proof: by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul]; rw [this]; rw [Finset.sum_insert]; rw [Finset.sum_singleton]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm]; rw [add_comm]
  simp

中文:
引理 coeff_one_mul
  条件: (φ ψ : R⟦X⟧)
  结论: coeff 1 (φ * ψ) =
  证明: by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul]; rw [this]; rw [Finset.sum_insert]; rw [Finset.sum_singleton]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm]; rw [add_comm]
  simp

Depends on / 依赖: Finset, Finset.antidiagonal, Finset.sum_insert, Finset.sum_singleton, add_comm, antidiagonal, coeff_mul, coeff_zero_eq_constantCoeff, mul_comm, sum_insert, sum_singleton
-/
lemma coeff_one_mul (φ ψ : R⟦X⟧) : coeff 1 (φ * ψ) =
    coeff 1 φ * constantCoeff ψ + coeff 1 ψ * constantCoeff φ := by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul]; rw [this]; rw [Finset.sum_insert]; rw [Finset.sum_singleton]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm]; rw [add_comm]
  simp

/--
lemma `coeff_one_pow` / 引理 `coeff_one_pow`

English:
lemma coeff_one_pow
  given: (n : Nat) (φ : R⟦X⟧)
  proof: by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => lia
  | succ n' ih =>
      have h₁ (m : Nat) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁]; rw [coeff_mul]; rw [h₂]; rw [Finset

中文:
引理 coeff_one_pow
  条件: (n : 自然数) (φ : R⟦X⟧)
  证明: by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => lia
  | succ n' ih =>
      have h₁ (m : Nat) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁]; rw [coeff_mul]; rw [h₂]; rw [Finset

Depends on / 依赖: Finset, Finset.antidiagonal, Finset.sum_insert, Finset.sum_singleton, Nat.cast_add, Nat.cast_one, Nat.eq_zero_or_pos, add_tsub_cancel_right, antidiagonal, cast_add, cast_one, coeff_mul, coeff_zero_eq_constantCoeff, eq_zero_or_pos, map_pow, sum_insert, sum_singleton
-/
lemma coeff_one_pow (n : Nat) (φ : R⟦X⟧) :
    coeff 1 (φ ^ n) = n * coeff 1 φ * (constantCoeff φ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => lia
  | succ n' ih =>
      have h₁ (m : Nat) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁]; rw [coeff_mul]; rw [h₂]; rw [Finset.sum_insert]; rw [Finset.sum_singleton]
      · simp only [coeff_zero_eq_constantCoeff, map_pow, Nat.cast_add, Nat.cast_one,
          add_tsub_cancel_right]
        have h₀ : n' = 0 ∨ 1 <= n' := by lia
        rcases h₀ with h' | h'
        · by_contra h''
          rw [h'] at h''
          simp only [pow_zero, one_mul, coeff_one, one_ne_zero, ↓reduceIte, zero_mul, add_zero,
            mul_one] at h''
          norm_num at h''
        · rw [ih]
          · conv => lhs; arg 2; rw [mul_comm, ← mul_assoc]
            move_mul [← constantCoeff φ ^ (n' - 1)]
            conv => enter [1, 2, 1, 1, 2]; rw [← pow_one (a := constantCoeff φ)]
            rw [← pow_add (a := constantCoeff φ)]
            conv => enter [1, 2, 1, 1]; rw [Nat.sub_add_cancel h']
            ring
          exact h'
      · decide

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A]

/--
theorem `not_isField` / 定理 `not_isField`

English:
theorem not_isField
  statement: ¬IsField A⟦X⟧
  proof: by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_n

中文:
定理 not_isField
  结论: ¬是域 A⟦X⟧
  证明: by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_n

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.mem_span_singleton, Ideal.span, Ideal.span_singleton_eq_bot, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, Subsingleton, X_dvd_iff, X_ne_zero, bot_lt_iff_ne_bot, constantCoeff_one, eq_top_iff_one, lt_top_iff_ne_top, mem_span_singleton, nontriviality, not_isField_iff_exists_ideal_bot_lt_and_lt_top, not_isField_of_subsingleton, one_ne_zero, span_singleton_eq_bot
-/
theorem not_isField : ¬IsField A⟦X⟧ := by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
        X_dvd_iff, constantCoeff_one]
      exact one_ne_zero

@[simp]
/--
theorem `rescale_X` / 定理 `rescale_X`

English:
theorem rescale_X
  given: (a : A)
  statement: rescale a X = C a * X
  proof: by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]

中文:
定理 rescale_X
  条件: (a : A)
  结论: rescale a X = C a * X
  证明: by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]

Depends on / 依赖: coeff_C_mul, coeff_X, coeff_rescale, split_ifs
-/
theorem rescale_X (a : A) : rescale a X = C a * X := by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]

/--
theorem `rescale_neg_one_X` / 定理 `rescale_neg_one_X`

English:
theorem rescale_neg_one_X
  statement: rescale (-1 : A) X = -X
  proof: by
  rw [rescale_X]; rw [map_neg]; rw [map_one]; rw [neg_one_mul]

中文:
定理 rescale_neg_one_X
  结论: rescale (-1 : A) X = -X
  证明: by
  rw [rescale_X]; rw [map_neg]; rw [map_one]; rw [neg_one_mul]

Depends on / 依赖: map_neg, map_one, neg_one_mul, rescale_X
-/
theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X]; rw [map_neg]; rw [map_one]; rw [neg_one_mul]

/--
Definition of `evalNegHom` / `evalNegHom` 的定义

English:
definition evalNegHom
  signature: : A⟦X⟧ ->+* A⟦X⟧
  body: rescale (-1 : A)

@[simp]

中文:
定义 evalNegHom
  签名: : A⟦X⟧ ->+* A⟦X⟧
  定义体: rescale (-1 : A)

@[simp]

Depends on / 依赖: rescale
-/
noncomputable def evalNegHom : A⟦X⟧ ->+* A⟦X⟧ :=
  rescale (-1 : A)

@[simp]
/--
theorem `evalNegHom_X` / 定理 `evalNegHom_X`

English:
theorem evalNegHom_X
  statement: evalNegHom (X : A⟦X⟧) = -X
  proof: rescale_neg_one_X

中文:
定理 evalNegHom_X
  结论: evalNegHom (X : A⟦X⟧) = -X
  证明: rescale_neg_one_X

Depends on / 依赖: rescale_neg_one_X
-/
theorem evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X :=
  rescale_neg_one_X

end CommRing

section Algebra

variable {A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  given: {r : R}
  statement: C r = (algebraMap R R⟦X⟧) r
  proof: rfl

中文:
定理 C_eq_algebraMap
  条件: {r : R}
  结论: C r = (algebraMap R R⟦X⟧) r
  证明: rfl
-/
theorem C_eq_algebraMap {r : R} : C r = (algebraMap R R⟦X⟧) r :=
  rfl

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: {r : R}
  statement: algebraMap R A⟦X⟧ r = C (algebraMap R A r)
  proof: MvPowerSeries.algebraMap_apply

中文:
定理 algebraMap_apply
  条件: {r : R}
  结论: algebraMap R A⟦X⟧ r = C (algebraMap R A r)
  证明: MvPowerSeries.algebraMap_apply

Depends on / 依赖: MvPowerSeries, MvPowerSeries.algebraMap_apply, algebraMap_apply
-/
theorem algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (Subalgebra R R⟦X⟧)
  body: { (inferInstance : Nontrivial <| Subalgebra R <| MvPowerSeries Unit R) with }

中文:
实例 [非平凡
  签名: R] : 非平凡 (子代数 R R⟦X⟧)
  定义体: { (inferInstance : Nontrivial <| Subalgebra R <| MvPowerSeries Unit R) with }

Depends on / 依赖: MvPowerSeries, Nontrivial, Subalgebra
-/
instance [Nontrivial R] : Nontrivial (Subalgebra R R⟦X⟧) :=
  { (inferInstance : Nontrivial <| Subalgebra R <| MvPowerSeries Unit R) with }

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (φ : A ->ₐ[R] B)
  body: MvPowerSeries.mapAlgHom φ

中文:
定义 mapAlgHom
  签名: (φ : A ->ₐ[R] B)
  定义体: MvPowerSeries.mapAlgHom φ

Depends on / 依赖: MvPowerSeries, MvPowerSeries.mapAlgHom, mapAlgHom
-/
def mapAlgHom (φ : A ->ₐ[R] B) :
    PowerSeries A ->ₐ[R] PowerSeries B :=
  MvPowerSeries.mapAlgHom φ

/--
theorem `mapAlgHom_apply` / 定理 `mapAlgHom_apply`

English:
theorem mapAlgHom_apply
  given: (φ : A ->ₐ[R] B) (f : A⟦X⟧)
  proof: MvPowerSeries.mapAlgHom_apply φ f

中文:
定理 mapAlgHom_apply
  条件: (φ : A ->ₐ[R] B) (f : A⟦X⟧)
  证明: MvPowerSeries.mapAlgHom_apply φ f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.mapAlgHom_apply, mapAlgHom_apply
-/
theorem mapAlgHom_apply (φ : A ->ₐ[R] B) (f : A⟦X⟧) :
    mapAlgHom φ f = f.map φ :=
  MvPowerSeries.mapAlgHom_apply φ f

end Algebra

end PowerSeries

namespace Polynomial

open Finsupp Polynomial

section Semiring
variable {R : Type*} [Semiring R] (φ ψ : R[X])

/-- The natural inclusion from polynomials into formal power series. -/
@[coe]
/--
Definition of `toPowerSeries` / `toPowerSeries` 的定义

English:
definition toPowerSeries
  signature: : R[X] -> PowerSeries R
  body: fun φ =>
  PowerSeries.mk fun n => coeff φ n

中文:
定义 toPowerSeries
  签名: : R[X] -> 幂级数 R
  定义体: fun φ =>
  PowerSeries.mk fun n => coeff φ n
-/
def toPowerSeries : R[X] -> PowerSeries R := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/--
Instance `coeToPowerSeries` / 实例 `coeToPowerSeries`

English:
instance coeToPowerSeries
  signature: : Coe R[X] (PowerSeries R)
  body: ⟨toPowerSeries⟩

中文:
实例 coeToPowerSeries
  签名: : Coe R[X] (幂级数 R)
  定义体: ⟨toPowerSeries⟩

Depends on / 依赖: toPowerSeries
-/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨toPowerSeries⟩

/--
theorem `coe_def` / 定理 `coe_def`

English:
theorem coe_def
  statement: (φ : PowerSeries R) = PowerSeries.mk (coeff φ)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_def
  结论: (φ : 幂级数 R) = 幂级数.mk (coeff φ)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl

@[simp, norm_cast]
/--
theorem `coeff_coe` / 定理 `coeff_coe`

English:
theorem coeff_coe
  given: (n)
  statement: PowerSeries.coeff n φ = coeff φ n
  proof: congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]

中文:
定理 coeff_coe
  条件: (n)
  结论: 幂级数.coeff n φ = coeff φ n
  证明: congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]

Depends on / 依赖: Finsupp, Finsupp.single_eq_same, congr_arg, single_eq_same
-/
theorem coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]
/--
theorem `coe_monomial` / 定理 `coe_monomial`

English:
theorem coe_monomial
  given: (n : Nat) (a : R)
  proof: by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]

中文:
定理 coe_monomial
  条件: (n : 自然数) (a : R)
  证明: by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]

Depends on / 依赖: Polynomial, Polynomial.coeff_monomial, PowerSeries, PowerSeries.coeff_monomial, coeff_coe, coeff_monomial, eq_comm
-/
theorem coe_monomial (n : Nat) (a : R) :
    (monomial n a : PowerSeries R) = PowerSeries.monomial n a := by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : R[X]) : PowerSeries R) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : R[X]) : 幂级数 R) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : R[X]) : PowerSeries R) = 1
  proof: by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : R[X]) : 幂级数 R) = 1
  证明: by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]

Depends on / 依赖: PowerSeries, PowerSeries.monomial_zero_eq_C_apply, coe_monomial, monomial_zero_eq_C_apply
-/
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ
  proof: by
  ext
  simp

@[simp, norm_cast]

中文:
定理 coe_add
  结论: ((φ + ψ : R[X]) : 幂级数 R) = φ + ψ
  证明: by
  ext
  simp

@[simp, norm_cast]
-/
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
  proof: PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]

中文:
定理 coe_mul
  结论: ((φ * ψ : R[X]) : 幂级数 R) = φ * ψ
  证明: PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_mul, PowerSeries.ext, coeff_coe, coeff_mul
-/
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (φ : R[X]) (r : R)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_smul
  条件: (φ : R[X]) (r : R)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_smul (φ : R[X]) (r : R) :
    (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

@[simp, norm_cast]
/--
theorem `coe_C` / 定理 `coe_C`

English:
theorem coe_C
  given: (a : R)
  statement: ((C a : R[X]) : PowerSeries R) = PowerSeries.C a
  proof: by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]

中文:
定理 coe_C
  条件: (a : R)
  结论: ((C a : R[X]) : 幂级数 R) = 幂级数.C a
  证明: by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]

Depends on / 依赖: PowerSeries, PowerSeries.monomial_zero_eq_C_apply, coe_monomial, monomial_zero_eq_C_apply
-/
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
/--
theorem `coe_X` / 定理 `coe_X`

English:
theorem coe_X
  statement: ((X : R[X]) : PowerSeries R) = PowerSeries.X
  proof: coe_monomial _ _

@[simp]

中文:
定理 coe_X
  结论: ((X : R[X]) : 幂级数 R) = 幂级数.X
  证明: coe_monomial _ _

@[simp]

Depends on / 依赖: coe_monomial
-/
theorem coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X :=
  coe_monomial _ _

@[simp]
/--
lemma `polynomial_map_coe` / 引理 `polynomial_map_coe`

English:
lemma polynomial_map_coe
  statement: {U V : Type*} [CommSemiring U] [CommSemiring V] {φ : U ->+* V}
  proof: by
  ext
  simp

@[simp]

中文:
引理 polynomial_map_coe
  结论: {U V : 类型} [交换半环 U] [交换半环 V] {φ : U ->+* V}
  证明: by
  ext
  simp

@[simp]
-/
lemma polynomial_map_coe {U V : Type*} [CommSemiring U] [CommSemiring V] {φ : U ->+* V}
    {f : Polynomial U} : Polynomial.map φ f = PowerSeries.map φ f := by
  ext
  simp

@[simp]
/--
theorem `constantCoeff_coe` / 定理 `constantCoeff_coe`

English:
theorem constantCoeff_coe
  statement: PowerSeries.constantCoeff φ = φ.coeff 0
  proof: rfl

中文:
定理 constantCoeff_coe
  结论: 幂级数.constantCoeff φ = φ.coeff 0
  证明: rfl
-/
theorem constantCoeff_coe : PowerSeries.constantCoeff φ = φ.coeff 0 :=
  rfl

variable (R)

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : R[X] -> PowerSeries R)
  proof: fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : R[X] -> 幂级数 R)
  证明: fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

Depends on / 依赖: coeff_coe, simp_rw
-/
theorem coe_injective : Function.Injective ((↑) : R[X] -> PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

variable {R φ ψ}

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (φ : PowerSeries R) = ψ ↔ φ = ψ
  proof: (coe_injective R).eq_iff

@[simp]

中文:
定理 coe_inj
  结论: (φ : 幂级数 R) = ψ ↔ φ = ψ
  证明: (coe_injective R).eq_iff

@[simp]

Depends on / 依赖: coe_injective, eq_iff
-/
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff

@[simp]
/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  statement: (φ : PowerSeries R) = 0 ↔ φ = 0
  proof: by rw [← coe_zero, coe_inj]

@[simp]

中文:
定理 coe_eq_zero_iff
  结论: (φ : 幂级数 R) = 0 ↔ φ = 0
  证明: by rw [← coe_zero, coe_inj]

@[simp]

Depends on / 依赖: coe_inj, coe_zero
-/
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
/--
theorem `coe_eq_one_iff` / 定理 `coe_eq_one_iff`

English:
theorem coe_eq_one_iff
  statement: (φ : PowerSeries R) = 1 ↔ φ = 1
  proof: by rw [← coe_one, coe_inj]

中文:
定理 coe_eq_one_iff
  结论: (φ : 幂级数 R) = 1 ↔ φ = 1
  证明: by rw [← coe_one, coe_inj]

Depends on / 依赖: coe_inj, coe_one
-/
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/--
Definition of `coeToPowerSeries.ringHom` / `coeToPowerSeries.ringHom` 的定义

English:
definition coeToPowerSeries.ringHom
  signature: : R[X] ->+* PowerSeries R where
  body: (↑)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]

中文:
定义 coeToPowerSeries.ringHom
  签名: : R[X] ->+* 幂级数 R where
  定义体: (↑)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
-/
def coeToPowerSeries.ringHom : R[X] ->+* PowerSeries R where
  toFun := (↑)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
/--
theorem `coeToPowerSeries.ringHom_apply` / 定理 `coeToPowerSeries.ringHom_apply`

English:
theorem coeToPowerSeries.ringHom_apply
  statement: coeToPowerSeries.ringHom φ = φ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coeToPowerSeries.ringHom_apply
  结论: coeToPowerSeries.ringHom φ = φ
  证明: rfl

@[simp, norm_cast]
-/
theorem coeToPowerSeries.ringHom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (n : Nat)
  statement: ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n
  proof: coeToPowerSeries.ringHom.map_pow _ _

中文:
定理 coe_pow
  条件: (n : 自然数)
  结论: ((φ ^ n : R[X]) : 幂级数 R) = (φ : 幂级数 R) ^ n
  证明: coeToPowerSeries.ringHom.map_pow _ _

Depends on / 依赖: coeToPowerSeries, coeToPowerSeries.ringHom.map_pow, map_pow, ringHom
-/
theorem coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _

/--
theorem `eval₂_C_X_eq_coe` / 定理 `eval₂_C_X_eq_coe`

English:
theorem eval₂_C_X_eq_coe
  statement: φ.eval₂ PowerSeries.C PowerSeries.X = ↑φ
  proof: by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply]; rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul]; rw [map_pow]; rw [coeToPowerSeries.ringHom_apply]; rw [coeToPowerSeries.ringHom_apply]; rw [coe_C]; rw [c

中文:
定理 eval₂_C_X_eq_coe
  结论: φ.eval₂ 幂级数.C 幂级数.X = ↑φ
  证明: by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply]; rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul]; rw [map_pow]; rw [coeToPowerSeries.ringHom_apply]; rw [coeToPowerSeries.ringHom_apply]; rw [coe_C]; rw [c

Depends on / 依赖: Finset, Finset.sum_congr, coeToPowerSeries, coeToPowerSeries.ringHom_apply, coe_C, coe_X, intros, map_mul, map_pow, map_sum, nth_rw, ringHom_apply, sum_congr
-/
theorem eval₂_C_X_eq_coe : φ.eval₂ PowerSeries.C PowerSeries.X = ↑φ := by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply]; rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul]; rw [map_pow]; rw [coeToPowerSeries.ringHom_apply]; rw [coeToPowerSeries.ringHom_apply]; rw [coe_C]; rw [coe_X]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] (φ ψ : R[X])

/--
theorem `_root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv` / 定理 `_root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv`

English:
theorem _root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv
  given: {f : MvPolynomial PUnit R}
  proof: by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    --Note: this `have` should be a generic `simp` lemma for a `Unique` type with `()` replaced
    --by any element.
    have : single () (d ()) = d := by ext; simp
    simp only [MvPolynomial.coe_monomial, MvPolynomial.uniq

中文:
定理 _root_.多元多项式.toMvPowerSeries_pUnitAlgEquiv
  条件: {f : 多元多项式 命题单元 R}
  证明: by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    --Note: this `have` should be a generic `simp` lemma for a `Unique` type with `()` replaced
    --by any element.
    have : single () (d ()) = d := by ext; simp
    simp only [MvPolynomial.coe_monomial, MvPolynomial.uniq

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, monomial
-/
theorem _root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv {f : MvPolynomial PUnit R} :
    (f.toMvPowerSeries : PowerSeries R) =
      (MvPolynomial.uniqueAlgEquiv R PUnit f).toPowerSeries := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    --Note: this `have` should be a generic `simp` lemma for a `Unique` type with `()` replaced
    --by any element.
    have : single () (d ()) = d := by ext; simp
    simp only [MvPolynomial.coe_monomial, MvPolynomial.uniqueAlgEquiv_monomial,
      Polynomial.coe_monomial, PowerSeries.monomial, this]
  | add f g hf hg => simp [hf, hg]

/--
theorem `pUnitAlgEquiv_symm_toPowerSeries` / 定理 `pUnitAlgEquiv_symm_toPowerSeries`

English:
theorem pUnitAlgEquiv_symm_toPowerSeries
  given: {f : Polynomial R}
  proof: by
  set g := (MvPolynomial.uniqueAlgEquiv R PUnit).symm f
  have : f = MvPolynomial.uniqueAlgEquiv R PUnit g := by simp only [g, AlgEquiv.apply_symm_apply]
  rw [this]; rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]

中文:
定理 pUnitAlgEquiv_symm_toPowerSeries
  条件: {f : 多项式 R}
  证明: by
  set g := (MvPolynomial.uniqueAlgEquiv R PUnit).symm f
  have : f = MvPolynomial.uniqueAlgEquiv R PUnit g := by simp only [g, AlgEquiv.apply_symm_apply]
  rw [this]; rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, MvPolynomial, MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, MvPolynomial.uniqueAlgEquiv, apply_symm_apply, toMvPowerSeries_pUnitAlgEquiv, uniqueAlgEquiv
-/
theorem pUnitAlgEquiv_symm_toPowerSeries {f : Polynomial R} :
    ((f.toPowerSeries) : MvPowerSeries PUnit R)
      = ((MvPolynomial.uniqueAlgEquiv R PUnit).symm f).toMvPowerSeries := by
  set g := (MvPolynomial.uniqueAlgEquiv R PUnit).symm f
  have : f = MvPolynomial.uniqueAlgEquiv R PUnit g := by simp only [g, AlgEquiv.apply_symm_apply]
  rw [this]; rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]

variable (A : Type*) [Semiring A] [Algebra R A]

/--
Definition of `coeToPowerSeries.algHom` / `coeToPowerSeries.algHom` 的定义

English:
definition coeToPowerSeries.algHom
  signature: : R[X] ->ₐ[R] PowerSeries A
  body: { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }

@[simp]

中文:
定义 coeToPowerSeries.algHom
  签名: : R[X] ->ₐ[R] 幂级数 A
  定义体: { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.algebraMap_apply, PowerSeries.map, algebraMap, algebraMap_apply, coeToPowerSeries, coeToPowerSeries.ringHom, commutes, ringHom
-/
def coeToPowerSeries.algHom : R[X] ->ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }

@[simp]
/--
theorem `coeToPowerSeries.algHom_apply` / 定理 `coeToPowerSeries.algHom_apply`

English:
theorem coeToPowerSeries.algHom_apply
  proof: rfl

中文:
定理 coeToPowerSeries.algHom_apply
  证明: rfl
-/
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl

end CommSemiring

section CommRing
variable {R : Type*} [CommRing R]

@[simp, norm_cast]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (p : R[X])
  statement: ((-p : R[X]) : PowerSeries R) = -p
  proof: coeToPowerSeries.ringHom.map_neg p

@[simp, norm_cast]

中文:
引理 coe_neg
  条件: (p : R[X])
  结论: ((-p : R[X]) : 幂级数 R) = -p
  证明: coeToPowerSeries.ringHom.map_neg p

@[simp, norm_cast]

Depends on / 依赖: coeToPowerSeries, coeToPowerSeries.ringHom.map_neg, map_neg, ringHom
-/
lemma coe_neg (p : R[X]) : ((-p : R[X]) : PowerSeries R) = -p :=
  coeToPowerSeries.ringHom.map_neg p

@[simp, norm_cast]
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (p q : R[X])
  statement: ((p - q : R[X]) : PowerSeries R) = p - q
  proof: coeToPowerSeries.ringHom.map_sub p q

中文:
引理 coe_sub
  条件: (p q : R[X])
  结论: ((p - q : R[X]) : 幂级数 R) = p - q
  证明: coeToPowerSeries.ringHom.map_sub p q

Depends on / 依赖: coeToPowerSeries, coeToPowerSeries.ringHom.map_sub, map_sub, ringHom
-/
lemma coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries R) = p - q :=
  coeToPowerSeries.ringHom.map_sub p q

end CommRing

end Polynomial

namespace PowerSeries

section Algebra

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : R⟦X⟧)

/--
Instance `algebraPolynomial` / 实例 `algebraPolynomial`

English:
instance algebraPolynomial
  signature: : Algebra R[X] A⟦X⟧
  body: RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

中文:
实例 algebraPolynomial
  签名: : 代数 R[X] A⟦X⟧
  定义体: RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

Depends on / 依赖: Polynomial, Polynomial.coeToPowerSeries.algHom, RingHom, RingHom.toAlgebra, algHom, coeToPowerSeries, toAlgebra, toRingHom
-/
instance algebraPolynomial : Algebra R[X] A⟦X⟧ :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

/--
Instance `algebraPowerSeries` / 实例 `algebraPowerSeries`

English:
instance algebraPowerSeries
  signature: : Algebra R⟦X⟧ A⟦X⟧
  body: (map (algebraMap R A)).toAlgebra

中文:
实例 algebraPowerSeries
  签名: : 代数 R⟦X⟧ A⟦X⟧
  定义体: (map (algebraMap R A)).toAlgebra

Depends on / 依赖: algebraMap, toAlgebra
-/
instance algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧ :=
  (map (algebraMap R A)).toAlgebra

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R A⟦X⟧ :=
RingHom.toAlgebra Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])

variable (A)

/--
theorem `algebraMap_apply'` / 定理 `algebraMap_apply'`

English:
theorem algebraMap_apply'
  given: (p : R[X])
  statement: algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p
  proof: rfl

中文:
定理 algebraMap_apply'
  条件: (p : R[X])
  结论: algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p
  证明: rfl
-/
theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p :=
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
    algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f :=
  rfl

end Algebra

end PowerSeries

end
