/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`. Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`. Thus, negative exponents are allowed. The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials.

## Notation
The symbol `R[T;T⁻¹]` stands for `LaurentPolynomial R`. We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `AddMonoidAlgebra R ℤ`.
Thus, they are essentially `Finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `Polynomial`, that instead shields away
the implementation via `Finsupp`s. It is closer to the original definition of polynomials.

As a consequence, `LaurentPolynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `Finsupp` implementation of `R[X]` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed. Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

## Future work
Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- A "better" definition of `trunc` would be as an `R`-linear map. This works:
-- ```
-- def trunc : R[T;T⁻¹] →[R] R[X] :=
-- refine (?_ : R[ℕ] →[R] R[X]).comp ?_
-- · exact ⟨(toFinsuppIso R).symm, by simp⟩
-- · refine ⟨fun r ↦ comapDomain _ r
-- (Set.injOn_of_injective (fun _ _ ↦ Int.ofNat.inj) _), ?_⟩
-- exact fun r f ↦ comapDomain_smul ..
-- ```
-- but it would make sense to bundle the maps better, for a smoother user experience.
-- I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
-- this stage of the Laurent process!
-- This would likely involve adding a `comapDomain` analogue of
-- `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
-- `Polynomial.toFinsuppIso`.
-- Add `degree, intDegree, intTrailingDegree, leadingCoeff, trailingCoeff,...`.
-/

@[expose] public section


open Polynomial Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R S : Type*}

/--
Definition of `LaurentPolynomial` / `LaurentPolynomial` 的定义

English:
abbreviation LaurentPolynomial
  signature: (R : Type*) [Semiring R]
  body: AddMonoidAlgebra R Int

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

中文:
缩写 LaurentPolynomial
  签名: (R : 类型) [半环 R]
  定义体: AddMonoidAlgebra R Int

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

Depends on / 依赖: AddMonoidAlgebra
-/
abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R Int

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

open LaurentPolynomial

@[ext]
/--
theorem `LaurentPolynomial.ext` / 定理 `LaurentPolynomial.ext`

English:
theorem LaurentPolynomial.ext
  given: [Semiring R] {p q : R[T;T⁻¹]} (h : forall a, p.coeff a = q.coeff a)
  proof: by ext; exact h _

中文:
定理 LaurentPolynomial.ext
  条件: [半环 R] {p q : R[T;T⁻¹]} (h : 对任意 a, p.coeff a = q.coeff a)
  证明: by ext; exact h _
-/
theorem LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : forall a, p.coeff a = q.coeff a) :
    p = q := by ext; exact h _

/--
Definition of `Polynomial.toLaurent` / `Polynomial.toLaurent` 的定义

English:
definition Polynomial.toLaurent
  signature: [Semiring R]
  body: (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R).toRingHom

中文:
定义 多项式.toLaurent
  签名: [半环 R]
  定义体: (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R).toRingHom

Depends on / 依赖: Int.ofNatHom, SetLike, SetLike.coe_injective, coe_injective, ha.symm, mapDomainRingHom, ofNatHom, toFinsuppIso, toRingHom
-/
def Polynomial.toLaurent [Semiring R] : R[X] ->+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R).toRingHom

/--
theorem `Polynomial.toLaurent_apply` / 定理 `Polynomial.toLaurent_apply`

English:
theorem Polynomial.toLaurent_apply
  given: [Semiring R] (p : R[X])
  proof: rfl

中文:
定理 多项式.toLaurent_apply
  条件: [半环 R] (p : R[X])
  证明: rfl
-/
theorem Polynomial.toLaurent_apply [Semiring R] (p : R[X]) :
    toLaurent p = p.toFinsupp.mapDomain (↑) :=
  rfl

/--
Definition of `Polynomial.toLaurentAlg` / `Polynomial.toLaurentAlg` 的定义

English:
definition Polynomial.toLaurentAlg
  signature: [CommSemiring R]
  body: (mapDomainAlgHom R R Int.ofNatHom).comp (toFinsuppIsoAlg R).toAlgHom

中文:
定义 多项式.toLaurentAlg
  签名: [交换半环 R]
  定义体: (mapDomainAlgHom R R Int.ofNatHom).comp (toFinsuppIsoAlg R).toAlgHom

Depends on / 依赖: Int.ofNatHom, mapDomainAlgHom, ofNatHom, toAlgHom, toFinsuppIsoAlg
-/
def Polynomial.toLaurentAlg [CommSemiring R] : R[X] ->ₐ[R] R[T;T⁻¹] :=
  (mapDomainAlgHom R R Int.ofNatHom).comp (toFinsuppIsoAlg R).toAlgHom

/--
lemma `Polynomial.coe_toLaurentAlg` / 引理 `Polynomial.coe_toLaurentAlg`

English:
lemma Polynomial.coe_toLaurentAlg
  given: [CommSemiring R]
  proof: rfl

中文:
引理 多项式.coe_toLaurentAlg
  条件: [交换半环 R]
  证明: rfl
-/
@[simp] lemma Polynomial.coe_toLaurentAlg [CommSemiring R] :
    (toLaurentAlg : R[X] -> R[T;T⁻¹]) = toLaurent :=
  rfl

/--
theorem `Polynomial.toLaurentAlg_apply` / 定理 `Polynomial.toLaurentAlg_apply`

English:
theorem Polynomial.toLaurentAlg_apply
  given: [CommSemiring R] (f : R[X])
  statement: toLaurentAlg f = toLaurent f
  proof: rfl

中文:
定理 多项式.toLaurentAlg_apply
  条件: [交换半环 R] (f : R[X])
  结论: toLaurentAlg f = toLaurent f
  证明: rfl
-/
theorem Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : toLaurentAlg f = toLaurent f :=
  rfl

namespace LaurentPolynomial

section Semiring

variable [Semiring R]

/--
theorem `single_zero_one_eq_one` / 定理 `single_zero_one_eq_one`

English:
theorem single_zero_one_eq_one
  statement: (.single 0 1 : R[T;T⁻¹]) = 1
  proof: rfl

中文:
定理 single_zero_one_eq_one
  结论: (.single 0 1 : R[T;T⁻¹]) = 1
  证明: rfl
-/
theorem single_zero_one_eq_one : (.single 0 1 : R[T;T⁻¹]) = 1 := rfl

/-! ### The functions `C` and `T`. -/

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* R[T;T⁻¹]
  body: singleZeroRingHom

中文:
定义 C
  签名: : R ->+* R[T;T⁻¹]
  定义体: singleZeroRingHom

Depends on / 依赖: singleZeroRingHom
-/
def C : R ->+* R[T;T⁻¹] :=
  singleZeroRingHom

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: {R A : 类型} [交换半环 R] [半环 A] [代数 R A] (r : R)
  证明: rfl
-/
theorem algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = C (algebraMap R A r) :=
  rfl

/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  given: {R : Type*} [CommSemiring R] (r : R)
  statement: C r = algebraMap R R[T;T⁻¹] r
  proof: rfl

中文:
定理 C_eq_algebraMap
  条件: {R : 类型} [交换半环 R] (r : R)
  结论: C r = algebraMap R R[T;T⁻¹] r
  证明: rfl
-/
theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R R[T;T⁻¹] r :=
  rfl

/--
theorem `single_eq_C` / 定理 `single_eq_C`

English:
theorem single_eq_C
  given: (r : R)
  statement: .single 0 r = C r
  proof: rfl

中文:
定理 single_eq_C
  条件: (r : R)
  结论: .single 0 r = C r
  证明: rfl
-/
theorem single_eq_C (r : R) : .single 0 r = C r := rfl

/--
lemma `C_apply` / 引理 `C_apply`

English:
lemma C_apply
  given: (t : R) (n : Int)
  statement: (C t).coeff n = if n = 0 then t else 0
  proof: by
  simp [← single_eq_C]; aesop

中文:
引理 C_apply
  条件: (t : R) (n : 整数)
  结论: (C t).coeff n = if n = 0 then t else 0
  证明: by
  simp [← single_eq_C]; aesop
-/
@[simp] lemma C_apply (t : R) (n : Int) : (C t).coeff n = if n = 0 then t else 0 := by
  simp [← single_eq_C]; aesop

/--
Definition of `T` / `T` 的定义

English:
definition T
  signature: (n : Int)
  body: .single n 1

中文:
定义 T
  签名: (n : 整数)
  定义体: .single n 1

Depends on / 依赖: single
-/
def T (n : Int) : R[T;T⁻¹] := .single n 1

/--
lemma `T_apply` / 引理 `T_apply`

English:
lemma T_apply
  given: (m n : Int)
  statement: (T n : R[T;T⁻¹]).coeff m = if n = m then 1 else 0
  proof: Finsupp.single_apply

@[simp]

中文:
引理 T_apply
  条件: (m n : 整数)
  结论: (T n : R[T;T⁻¹]).coeff m = if n = m then 1 else 0
  证明: Finsupp.single_apply

@[simp]
-/
@[simp] lemma T_apply (m n : Int) : (T n : R[T;T⁻¹]).coeff m = if n = m then 1 else 0 :=
  Finsupp.single_apply

@[simp]
/--
theorem `T_zero` / 定理 `T_zero`

English:
theorem T_zero
  statement: (T 0 : R[T;T⁻¹]) = 1
  proof: rfl

中文:
定理 T_zero
  结论: (T 0 : R[T;T⁻¹]) = 1
  证明: rfl
-/
theorem T_zero : (T 0 : R[T;T⁻¹]) = 1 :=
  rfl

/--
theorem `T_add` / 定理 `T_add`

English:
theorem T_add
  given: (m n : Int)
  statement: (T (m + n) : R[T;T⁻¹]) = T m * T n
  proof: by
  simp [T, single_mul_single]

中文:
定理 T_add
  条件: (m n : 整数)
  结论: (T (m + n) : R[T;T⁻¹]) = T m * T n
  证明: by
  simp [T, single_mul_single]

Depends on / 依赖: single_mul_single
-/
theorem T_add (m n : Int) : (T (m + n) : R[T;T⁻¹]) = T m * T n := by
  simp [T, single_mul_single]

/--
theorem `T_sub` / 定理 `T_sub`

English:
theorem T_sub
  given: (m n : Int)
  statement: (T (m - n) : R[T;T⁻¹]) = T m * T (-n)
  proof: by rw [← T_add, sub_eq_add_neg]

@[simp]

中文:
定理 T_sub
  条件: (m n : 整数)
  结论: (T (m - n) : R[T;T⁻¹]) = T m * T (-n)
  证明: by rw [← T_add, sub_eq_add_neg]

@[simp]

Depends on / 依赖: T_add, sub_eq_add_neg
-/
theorem T_sub (m n : Int) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n) := by rw [← T_add, sub_eq_add_neg]

@[simp]
/--
theorem `T_pow` / 定理 `T_pow`

English:
theorem T_pow
  given: (m : Int) (n : Nat)
  statement: (T m ^ n : R[T;T⁻¹]) = T (n * m)
  proof: by
  rw [T]; rw [T]; rw [single_pow]; rw [one_pow]; rw [nsmul_eq_mul]

中文:
定理 T_pow
  条件: (m : 整数) (n : 自然数)
  结论: (T m ^ n : R[T;T⁻¹]) = T (n * m)
  证明: by
  rw [T]; rw [T]; rw [single_pow]; rw [one_pow]; rw [nsmul_eq_mul]

Depends on / 依赖: nsmul_eq_mul, one_pow, single_pow
-/
theorem T_pow (m : Int) (n : Nat) : (T m ^ n : R[T;T⁻¹]) = T (n * m) := by
  rw [T]; rw [T]; rw [single_pow]; rw [one_pow]; rw [nsmul_eq_mul]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
/--
theorem `mul_T_assoc` / 定理 `mul_T_assoc`

English:
theorem mul_T_assoc
  given: (f : R[T;T⁻¹]) (m n : Int)
  statement: f * T m * T n = f * T (m + n)
  proof: by
  simp [← T_add, mul_assoc]

@[simp]

中文:
定理 mul_T_assoc
  条件: (f : R[T;T⁻¹]) (m n : 整数)
  结论: f * T m * T n = f * T (m + n)
  证明: by
  simp [← T_add, mul_assoc]

@[simp]

Depends on / 依赖: T_add, mul_assoc
-/
theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : f * T m * T n = f * T (m + n) := by
  simp [← T_add, mul_assoc]

@[simp]
/--
theorem `single_eq_C_mul_T` / 定理 `single_eq_C_mul_T`

English:
theorem single_eq_C_mul_T
  given: (r : R) (n : Int)
  statement: .single n r = C r * T n
  proof: by
  simp [C, T, single_mul_single]

中文:
定理 single_eq_C_mul_T
  条件: (r : R) (n : 整数)
  结论: .single n r = C r * T n
  证明: by
  simp [C, T, single_mul_single]

Depends on / 依赖: single_mul_single
-/
theorem single_eq_C_mul_T (r : R) (n : Int) : .single n r = C r * T n := by
  simp [C, T, single_mul_single]

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
/--
theorem `_root_.Polynomial.toLaurent_C_mul_T` / 定理 `_root_.Polynomial.toLaurent_C_mul_T`

English:
theorem _root_.Polynomial.toLaurent_C_mul_T
  given: (n : Nat) (r : R)
  proof: by simp [toLaurent]

@[simp]

中文:
定理 _root_.多项式.toLaurent_C_mul_T
  条件: (n : 自然数) (r : R)
  证明: by simp [toLaurent]

@[simp]

Depends on / 依赖: toLaurent
-/
theorem _root_.Polynomial.toLaurent_C_mul_T (n : Nat) (r : R) :
    (toLaurent (Polynomial.monomial n r) : R[T;T⁻¹]) = C r * T n := by simp [toLaurent]

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_C` / 定理 `_root_.Polynomial.toLaurent_C`

English:
theorem _root_.Polynomial.toLaurent_C
  given: (r : R)
  statement: toLaurent (Polynomial.C r) = C r
  proof: by
  convert! Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, T_zero, mul_one]

@[simp]

中文:
定理 _root_.多项式.toLaurent_C
  条件: (r : R)
  结论: toLaurent (多项式.C r) = C r
  证明: by
  convert! Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, T_zero, mul_one]

@[simp]

Depends on / 依赖: Int.ofNat_zero, Polynomial, Polynomial.toLaurent_C_mul_T, T_zero, convert, mul_one, ofNat_zero, toLaurent_C_mul_T
-/
theorem _root_.Polynomial.toLaurent_C (r : R) : toLaurent (Polynomial.C r) = C r := by
  convert! Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, T_zero, mul_one]

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_comp_C` / 定理 `_root_.Polynomial.toLaurent_comp_C`

English:
theorem _root_.Polynomial.toLaurent_comp_C
  statement: toLaurent (R := R) ∘ Polynomial.C = C
  proof: funext Polynomial.toLaurent_C

@[simp]

中文:
定理 _root_.多项式.toLaurent_comp_C
  结论: toLaurent (R := R) ∘ 多项式.C = C
  证明: funext Polynomial.toLaurent_C

@[simp]

Depends on / 依赖: Polynomial, Polynomial.C
-/
theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ Polynomial.C = C :=
  funext Polynomial.toLaurent_C

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_X` / 定理 `_root_.Polynomial.toLaurent_X`

English:
theorem _root_.Polynomial.toLaurent_X
  statement: (toLaurent Polynomial.X : R[T;T⁻¹]) = T 1
  proof: by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

@[simp]

中文:
定理 _root_.多项式.toLaurent_X
  结论: (toLaurent 多项式.X : R[T;T⁻¹]) = T 1
  证明: by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.X, Polynomial.toLaurent_C_mul_T, monomial, toLaurent_C_mul_T
-/
theorem _root_.Polynomial.toLaurent_X : (toLaurent Polynomial.X : R[T;T⁻¹]) = T 1 := by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_one` / 定理 `_root_.Polynomial.toLaurent_one`

English:
theorem _root_.Polynomial.toLaurent_one
  statement: (Polynomial.toLaurent : R[X] -> R[T;T⁻¹]) 1 = 1
  proof: map_one Polynomial.toLaurent

@[simp]

中文:
定理 _root_.多项式.toLaurent_one
  结论: (多项式.toLaurent : R[X] -> R[T;T⁻¹]) 1 = 1
  证明: map_one Polynomial.toLaurent

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toLaurent, map_one, toLaurent
-/
theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : R[X] -> R[T;T⁻¹]) 1 = 1 :=
  map_one Polynomial.toLaurent

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_C_mul_eq` / 定理 `_root_.Polynomial.toLaurent_C_mul_eq`

English:
theorem _root_.Polynomial.toLaurent_C_mul_eq
  given: (r : R) (f : R[X])
  proof: by
  simp only [map_mul, Polynomial.toLaurent_C]

@[simp]

中文:
定理 _root_.多项式.toLaurent_C_mul_eq
  条件: (r : R) (f : R[X])
  证明: by
  simp only [map_mul, Polynomial.toLaurent_C]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_C, map_mul, toLaurent_C
-/
theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : R[X]) :
    toLaurent (Polynomial.C r * f) = C r * toLaurent f := by
  simp only [map_mul, Polynomial.toLaurent_C]

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_X_pow` / 定理 `_root_.Polynomial.toLaurent_X_pow`

English:
theorem _root_.Polynomial.toLaurent_X_pow
  given: (n : Nat)
  statement: toLaurent (X ^ n : R[X]) = T n
  proof: by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]

中文:
定理 _root_.多项式.toLaurent_X_pow
  条件: (n : 自然数)
  结论: toLaurent (X ^ n : R[X]) = T n
  证明: by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_X, T_pow, map_pow, mul_one, toLaurent_X
-/
theorem _root_.Polynomial.toLaurent_X_pow (n : Nat) : toLaurent (X ^ n : R[X]) = T n := by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]

/--
theorem `_root_.Polynomial.toLaurent_C_mul_X_pow` / 定理 `_root_.Polynomial.toLaurent_C_mul_X_pow`

English:
theorem _root_.Polynomial.toLaurent_C_mul_X_pow
  given: (n : Nat) (r : R)
  proof: by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

中文:
定理 _root_.多项式.toLaurent_C_mul_X_pow
  条件: (n : 自然数) (r : R)
  证明: by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, map_mul, toLaurent_C, toLaurent_X_pow
-/
theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : Nat) (r : R) :
    toLaurent (Polynomial.C r * X ^ n) = C r * T n := by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

/--
Instance `invertibleT` / 实例 `invertibleT`

English:
instance invertibleT
  signature: (n : Int)
  body: T (-n)
  invOf_mul_self := by rw [← T_add, neg_add_cancel, T_zero]
  mul_invOf_self := by rw [← T_add, add_neg_cancel, T_zero]

@[simp]

中文:
实例 invertibleT
  签名: (n : 整数)
  定义体: T (-n)
  invOf_mul_self := by rw [← T_add, neg_add_cancel, T_zero]
  mul_invOf_self := by rw [← T_add, add_neg_cancel, T_zero]

@[simp]
-/
instance invertibleT (n : Int) : Invertible (T n : R[T;T⁻¹]) where
  invOf := T (-n)
  invOf_mul_self := by rw [← T_add, neg_add_cancel, T_zero]
  mul_invOf_self := by rw [← T_add, add_neg_cancel, T_zero]

@[simp]
/--
theorem `invOf_T` / 定理 `invOf_T`

English:
theorem invOf_T
  given: (n : Int)
  statement: ⅟(T n : R[T;T⁻¹]) = T (-n)
  proof: rfl

中文:
定理 invOf_T
  条件: (n : 整数)
  结论: ⅟(T n : R[T;T⁻¹]) = T (-n)
  证明: rfl
-/
theorem invOf_T (n : Int) : ⅟(T n : R[T;T⁻¹]) = T (-n) :=
  rfl

/--
theorem `isUnit_T` / 定理 `isUnit_T`

English:
theorem isUnit_T
  given: (n : Int)
  statement: IsUnit (T n : R[T;T⁻¹])
  proof: isUnit_of_invertible _

@[elab_as_elim]

中文:
定理 isUnit_T
  条件: (n : 整数)
  结论: 是单位 (T n : R[T;T⁻¹])
  证明: isUnit_of_invertible _

@[elab_as_elim]

Depends on / 依赖: isUnit_of_invertible
-/
theorem isUnit_T (n : Int) : IsUnit (T n : R[T;T⁻¹]) :=
  isUnit_of_invertible _

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {M : R[T;T⁻¹] -> Prop} (p : R[T;T⁻¹]) (h_C : forall a, M (C a))
  proof: by
  have A : forall {n : Int} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : forall s : Finset Int, M (s.sum fun n : Int => C (p.coeff n) * T n) := by
    apply Finset.induction
    · convert! h_C 0
      simp only [Finset.sum_empty, map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert! B p.coeff.support
  ext a
  simp_rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_sum, coeff_single]
  rw [Finset.sum_apply']; rw [Finset.sum_eq_single a]; rw [single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same]; rw [notMem_support_iff.mp ha]

中文:
定理 induction_on
  结论: {M : R[T;T⁻¹] -> 命题} (p : R[T;T⁻¹]) (h_C : 对任意 a, M (C a))
  证明: by
  have A : forall {n : Int} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : forall s : Finset Int, M (s.sum fun n : Int => C (p.coeff n) * T n) := by
    apply Finset.induction
    · convert! h_C 0
      simp only [Finset.sum_empty, map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert! B p.coeff.support
  ext a
  simp_rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_sum, coeff_single]
  rw [Finset.sum_apply']; rw [Finset.sum_eq_single a]; rw [single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same]; rw [notMem_support_iff.mp ha]
-/
protected theorem induction_on {M : R[T;T⁻¹] -> Prop} (p : R[T;T⁻¹]) (h_C : forall a, M (C a))
    (h_add : forall {p q}, M p -> M q -> M (p + q))
    (h_C_mul_T : forall (n : Nat) (a : R), M (C a * T n) -> M (C a * T (n + 1)))
    (h_C_mul_T_Z : forall (n : Nat) (a : R), M (C a * T (-n)) -> M (C a * T (-n - 1))) : M p := by
  have A : forall {n : Int} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : forall s : Finset Int, M (s.sum fun n : Int => C (p.coeff n) * T n) := by
    apply Finset.induction
    · convert! h_C 0
      simp only [Finset.sum_empty, map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert! B p.coeff.support
  ext a
  simp_rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_sum, coeff_single]
  rw [Finset.sum_apply']; rw [Finset.sum_eq_single a]; rw [single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same]; rw [notMem_support_iff.mp ha]

/-- To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {motive : R[T;T⁻¹] -> Prop} (p : R[T;T⁻¹])
  proof: by
  refine p.induction_on (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert! C_mul_T 0 a
  exact (mul_one _).symm

中文:
定理 induction_on'
  结论: {motive : R[T;T⁻¹] -> 命题} (p : R[T;T⁻¹])
  证明: by
  refine p.induction_on (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert! C_mul_T 0 a
  exact (mul_one _).symm
-/
protected theorem induction_on' {motive : R[T;T⁻¹] -> Prop} (p : R[T;T⁻¹])
    (add : forall p q, motive p -> motive q -> motive (p + q))
    (C_mul_T : forall (n : Int) (a : R), motive (C a * T n)) : motive p := by
  refine p.induction_on (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert! C_mul_T 0 a
  exact (mul_one _).symm

/--
theorem `commute_T` / 定理 `commute_T`

English:
theorem commute_T
  given: (n : Int) (f : R[T;T⁻¹])
  statement: Commute (T n) f
  proof: f.induction_on' (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T]; rw [T]; rw [← single_eq_C]; rw [single_mul_single]; rw [single_mul_single]; rw [single_mul_single]
      simp [add_comm]

@[simp]

中文:
定理 commute_T
  条件: (n : 整数) (f : R[T;T⁻¹])
  结论: Commute (T n) f
  证明: f.induction_on' (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T]; rw [T]; rw [← single_eq_C]; rw [single_mul_single]; rw [single_mul_single]; rw [single_mul_single]
      simp [add_comm]

@[simp]

Depends on / 依赖: Commute, Commute.add_right, add_comm, add_right, f.induction_on, induction_on, single_eq_C, single_mul_single
-/
theorem commute_T (n : Int) (f : R[T;T⁻¹]) : Commute (T n) f :=
  f.induction_on' (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T]; rw [T]; rw [← single_eq_C]; rw [single_mul_single]; rw [single_mul_single]; rw [single_mul_single]
      simp [add_comm]

@[simp]
/--
theorem `T_mul` / 定理 `T_mul`

English:
theorem T_mul
  given: (n : Int) (f : R[T;T⁻¹])
  statement: T n * f = f * T n
  proof: (commute_T n f).eq

中文:
定理 T_mul
  条件: (n : 整数) (f : R[T;T⁻¹])
  结论: T n * f = f * T n
  证明: (commute_T n f).eq

Depends on / 依赖: commute_T
-/
theorem T_mul (n : Int) (f : R[T;T⁻¹]) : T n * f = f * T n :=
  (commute_T n f).eq

/--
theorem `smul_eq_C_mul` / 定理 `smul_eq_C_mul`

English:
theorem smul_eq_C_mul
  given: (r : R) (f : R[T;T⁻¹])
  statement: r • f = C r * f
  proof: by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add]; rw [mul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← smul_mul_assoc]; rw [mul_left_inj_of_invertible]; rw [← map_mul]; rw [← single_eq_C]; rw [AddMonoidAlgebra.smul_single']
    rfl

中文:
定理 smul_eq_C_mul
  条件: (r : R) (f : R[T;T⁻¹])
  结论: r • f = C r * f
  证明: by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add]; rw [mul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← smul_mul_assoc]; rw [mul_left_inj_of_invertible]; rw [← map_mul]; rw [← single_eq_C]; rw [AddMonoidAlgebra.smul_single']
    rfl

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.smul_single, C_mul_T, LaurentPolynomial, LaurentPolynomial.induction_on, induction_on, map_mul, mul_add, mul_assoc, mul_left_inj_of_invertible, single_eq_C, smul_add, smul_mul_assoc, smul_single
-/
theorem smul_eq_C_mul (r : R) (f : R[T;T⁻¹]) : r • f = C r * f := by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add]; rw [mul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← smul_mul_assoc]; rw [mul_left_inj_of_invertible]; rw [← map_mul]; rw [← single_eq_C]; rw [AddMonoidAlgebra.smul_single']
    rfl

/--
Definition of `trunc` / `trunc` 的定义

English:
definition trunc
  signature: : R[T;T⁻¹] ->+ R[X]
  body: (toFinsuppIso R).symm.toAddMonoidHom.comp comapDomainAddMonoidHom (↑) Nat.cast_injective

中文:
定义 trunc
  签名: : R[T;T⁻¹] ->+ R[X]
  定义体: (toFinsuppIso R).symm.toAddMonoidHom.comp comapDomainAddMonoidHom (↑) Nat.cast_injective

Depends on / 依赖: Nat.cast_injective, cast_injective, comapDomainAddMonoidHom, symm.toAddMonoidHom.comp, toAddMonoidHom, toFinsuppIso
-/
def trunc : R[T;T⁻¹] ->+ R[X] :=
(toFinsuppIso R).symm.toAddMonoidHom.comp comapDomainAddMonoidHom (↑) Nat.cast_injective

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `trunc_C_mul_T` / 定理 `trunc_C_mul_T`

English:
theorem trunc_C_mul_T
  given: (n : Int) (r : R)
  statement: trunc (C r * T n) = ite (0 <= n) (monomial n.toNat r) 0
  proof: by
  apply (toFinsuppIso R).injective
  simp only [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  split_ifs with hn
  · lift n to Nat using hn
    simp [toFinsupp_monomial, -single_eq_C_mul_T]
  · ext a
    have : a != n := by lia
    simp [-single_eq_C_mul_T, single_eq_of_ne this]

@[simp]

中文:
定理 trunc_C_mul_T
  条件: (n : 整数) (r : R)
  结论: trunc (C r * T n) = ite (0 <= n) (monomial n.to自然数 r) 0
  证明: by
  apply (toFinsuppIso R).injective
  simp only [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  split_ifs with hn
  · lift n to Nat using hn
    simp [toFinsupp_monomial, -single_eq_C_mul_T]
  · ext a
    have : a != n := by lia
    simp [-single_eq_C_mul_T, single_eq_of_ne this]

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.coe_comp, Function, Function.comp_apply, RingEquiv, RingEquiv.apply_symm_apply, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_coe, RingHom.toAddMonoidHom_eq_coe, apply_symm_apply, coe_coe, coe_comp, comp_apply, injective, single_eq_C_mul_T, single_eq_of_ne, split_ifs, toAddMonoidHom_eq_coe
-/
theorem trunc_C_mul_T (n : Int) (r : R) : trunc (C r * T n) = ite (0 <= n) (monomial n.toNat r) 0 := by
  apply (toFinsuppIso R).injective
  simp only [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  split_ifs with hn
  · lift n to Nat using hn
    simp [toFinsupp_monomial, -single_eq_C_mul_T]
  · ext a
    have : a != n := by lia
    simp [-single_eq_C_mul_T, single_eq_of_ne this]

@[simp]
/--
theorem `leftInverse_trunc_toLaurent` / 定理 `leftInverse_trunc_toLaurent`

English:
theorem leftInverse_trunc_toLaurent
  proof: by
  refine fun f => f.induction_on' ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

@[simp]

中文:
定理 leftInverse_trunc_toLaurent
  证明: by
  refine fun f => f.induction_on' ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

@[simp]

Depends on / 依赖: Int.natCast_nonneg, Int.toNat_natCast, Polynomial, Polynomial.toLaurent_C_mul_T, f.induction_on, if_true, induction_on, map_add, natCast_nonneg, toLaurent_C_mul_T, toNat_natCast, trunc_C_mul_T
-/
theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (trunc : R[T;T⁻¹] -> R[X]) Polynomial.toLaurent := by
  refine fun f => f.induction_on' ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

@[simp]
/--
theorem `_root_.Polynomial.trunc_toLaurent` / 定理 `_root_.Polynomial.trunc_toLaurent`

English:
theorem _root_.Polynomial.trunc_toLaurent
  given: (f : R[X])
  statement: trunc (toLaurent f) = f
  proof: leftInverse_trunc_toLaurent _

中文:
定理 _root_.多项式.trunc_toLaurent
  条件: (f : R[X])
  结论: trunc (toLaurent f) = f
  证明: leftInverse_trunc_toLaurent _

Depends on / 依赖: leftInverse_trunc_toLaurent
-/
theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : trunc (toLaurent f) = f :=
  leftInverse_trunc_toLaurent _

/--
theorem `_root_.Polynomial.toLaurent_injective` / 定理 `_root_.Polynomial.toLaurent_injective`

English:
theorem _root_.Polynomial.toLaurent_injective
  proof: leftInverse_trunc_toLaurent.injective

@[simp]

中文:
定理 _root_.多项式.toLaurent_injective
  证明: leftInverse_trunc_toLaurent.injective

@[simp]

Depends on / 依赖: injective, leftInverse_trunc_toLaurent, leftInverse_trunc_toLaurent.injective
-/
theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] -> R[T;T⁻¹]) :=
  leftInverse_trunc_toLaurent.injective

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_inj` / 定理 `_root_.Polynomial.toLaurent_inj`

English:
theorem _root_.Polynomial.toLaurent_inj
  given: (f g : R[X])
  statement: toLaurent f = toLaurent g ↔ f = g
  proof: ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩

中文:
定理 _root_.多项式.toLaurent_inj
  条件: (f g : R[X])
  结论: toLaurent f = toLaurent g ↔ f = g
  证明: ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩

Depends on / 依赖: Polynomial, Polynomial.toLaurent_injective, congr_arg, toLaurent_injective
-/
theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g :=
  ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩

/--
theorem `_root_.Polynomial.toLaurent_ne_zero` / 定理 `_root_.Polynomial.toLaurent_ne_zero`

English:
theorem _root_.Polynomial.toLaurent_ne_zero
  given: {f : R[X]}
  statement: toLaurent f != 0 ↔ f != 0
  proof: map_ne_zero_iff _ Polynomial.toLaurent_injective

@[simp]

中文:
定理 _root_.多项式.toLaurent_ne_zero
  条件: {f : R[X]}
  结论: toLaurent f != 0 ↔ f != 0
  证明: map_ne_zero_iff _ Polynomial.toLaurent_injective

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_injective, map_ne_zero_iff, toLaurent_injective
-/
theorem _root_.Polynomial.toLaurent_ne_zero {f : R[X]} : toLaurent f != 0 ↔ f != 0 :=
  map_ne_zero_iff _ Polynomial.toLaurent_injective

@[simp]
/--
theorem `_root_.Polynomial.toLaurent_eq_zero` / 定理 `_root_.Polynomial.toLaurent_eq_zero`

English:
theorem _root_.Polynomial.toLaurent_eq_zero
  given: {f : R[X]}
  statement: toLaurent f = 0 ↔ f = 0
  proof: map_eq_zero_iff _ Polynomial.toLaurent_injective

中文:
定理 _root_.多项式.toLaurent_eq_zero
  条件: {f : R[X]}
  结论: toLaurent f = 0 ↔ f = 0
  证明: map_eq_zero_iff _ Polynomial.toLaurent_injective

Depends on / 依赖: Polynomial, Polynomial.toLaurent_injective, map_eq_zero_iff, toLaurent_injective
-/
theorem _root_.Polynomial.toLaurent_eq_zero {f : R[X]} : toLaurent f = 0 ↔ f = 0 :=
  map_eq_zero_iff _ Polynomial.toLaurent_injective

/--
theorem `exists_T_pow` / 定理 `exists_T_pow`

English:
theorem exists_T_pow
  given: (f : R[T;T⁻¹])
  statement: exists (n : Nat) (f' : R[X]), toLaurent f' = f * T n
  proof: by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : Int), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, mul_T_assoc,
        neg_add_cancel, T_zero, mul_one]

中文:
定理 存在_T_pow
  条件: (f : R[T;T⁻¹])
  结论: 存在 (n : 自然数) (f' : R[X]), toLaurent f' = f * T n
  证明: by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : Int), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, mul_T_assoc,
        neg_add_cancel, T_zero, mul_one]

Depends on / 依赖: Int.natCast_add, Int.natCast_succ, Int.negSucc_eq, Polynomial, Polynomial.C, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, T_zero, add_comm, add_mul, f.induction_on, induction_on, map_add, map_mul, mul_T_assoc, mul_one, natCast_add, natCast_succ, negSucc_eq, neg_add_cancel
-/
theorem exists_T_pow (f : R[T;T⁻¹]) : exists (n : Nat) (f' : R[X]), toLaurent f' = f * T n := by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : Int), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, mul_T_assoc,
        neg_add_cancel, T_zero, mul_one]

/-- This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_elim]
/--
theorem `induction_on_mul_T` / 定理 `induction_on_mul_T`

English:
theorem induction_on_mul_T
  statement: {motive : R[T;T⁻¹] -> Prop} (f : R[T;T⁻¹])
  proof: by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f]; rw [← T_zero]; rw [← Nat.cast_zero]; rw [← Nat.sub_self n]; rw [Nat.cast_sub rfl.le]; rw [T_sub]; rw [← mul_assoc]; rw [← hf]
  exact mul_T ..

中文:
定理 induction_on_mul_T
  结论: {motive : R[T;T⁻¹] -> 命题} (f : R[T;T⁻¹])
  证明: by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f]; rw [← T_zero]; rw [← Nat.cast_zero]; rw [← Nat.sub_self n]; rw [Nat.cast_sub rfl.le]; rw [T_sub]; rw [← mul_assoc]; rw [← hf]
  exact mul_T ..

Depends on / 依赖: Nat.cast_sub, Nat.cast_zero, Nat.sub_self, T_sub, T_zero, cast_sub, cast_zero, exists_T_pow, f.exists_T_pow, mul_T, mul_assoc, mul_one, rfl.le, sub_self
-/
theorem induction_on_mul_T {motive : R[T;T⁻¹] -> Prop} (f : R[T;T⁻¹])
    (mul_T : forall (f : R[X]) (n : Nat), motive (toLaurent f * T (-n))) : motive f := by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f]; rw [← T_zero]; rw [← Nat.cast_zero]; rw [← Nat.sub_self n]; rw [Nat.cast_sub rfl.le]; rw [T_sub]; rw [← mul_assoc]; rw [← hf]
  exact mul_T ..

/--
theorem `reduce_to_polynomial_of_mul_T` / 定理 `reduce_to_polynomial_of_mul_T`

English:
theorem reduce_to_polynomial_of_mul_T
  statement: (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] -> Prop}
  proof: by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa

中文:
定理 reduce_to_polynomial_of_mul_T
  结论: (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] -> 命题}
  证明: by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa

Depends on / 依赖: LaurentPolynomial, LaurentPolynomial.induction_on_mul_T, Nat.cast_zero, T_zero, cast_zero, convert, induction_on_mul_T, mul_one, neg_zero
-/
theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] -> Prop}
    (Qf : forall f : R[X], Q (toLaurent f)) (QT : forall f, Q (f * T 1) -> Q f) : Q f := by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa

section Support

/--
theorem `support_C_mul_T` / 定理 `support_C_mul_T`

English:
theorem support_C_mul_T
  given: (a : R) (n : Int)
  statement: (C a * T n).coeff.support subseteq {n}
  proof: by
  rw [← single_eq_C_mul_T]
  exact support_single_subset

中文:
定理 support_C_mul_T
  条件: (a : R) (n : 整数)
  结论: (C a * T n).coeff.support subseteq {n}
  证明: by
  rw [← single_eq_C_mul_T]
  exact support_single_subset

Depends on / 依赖: single_eq_C_mul_T, support_single_subset
-/
theorem support_C_mul_T (a : R) (n : Int) : (C a * T n).coeff.support subseteq {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_subset

/--
theorem `support_coeff_C_mul_T_of_ne_zero` / 定理 `support_coeff_C_mul_T_of_ne_zero`

English:
theorem support_coeff_C_mul_T_of_ne_zero
  given: {a : R} (a0 : a != 0) (n : Int)
  proof: by
  rw [← single_eq_C_mul_T]
  exact support_single _ a0

@[deprecated (since := "2026-06-18")]
alias support_C_mul_T_of_ne_zero := support_coeff_C_mul_T_of_ne_zero

中文:
定理 support_coeff_C_mul_T_of_ne_zero
  条件: {a : R} (a0 : a != 0) (n : 整数)
  证明: by
  rw [← single_eq_C_mul_T]
  exact support_single _ a0

@[deprecated (since := "2026-06-18")]
alias support_C_mul_T_of_ne_zero := support_coeff_C_mul_T_of_ne_zero

Depends on / 依赖: single_eq_C_mul_T, support_single
-/
theorem support_coeff_C_mul_T_of_ne_zero {a : R} (a0 : a != 0) (n : Int) :
    (C a * T n).coeff.support = {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single _ a0

@[deprecated (since := "2026-06-18")]
alias support_C_mul_T_of_ne_zero := support_coeff_C_mul_T_of_ne_zero

/--
lemma `coeff_toLaurent` / 引理 `coeff_toLaurent`

English:
lemma coeff_toLaurent
  given: (f : R[X])
  proof: rfl

中文:
引理 coeff_toLaurent
  条件: (f : R[X])
  证明: rfl
-/
@[simp] lemma coeff_toLaurent (f : R[X]) :
    f.toLaurent.coeff = f.toFinsupp.coeff.mapDomain Nat.castEmbedding := rfl

/--
theorem `support_coeff_toLaurent` / 定理 `support_coeff_toLaurent`

English:
theorem support_coeff_toLaurent
  given: (f : R[X])
  proof: by simp [Polynomial.support]

@[deprecated (since := "2026-06-18")] alias toLaurent_support := support_coeff_toLaurent

中文:
定理 support_coeff_toLaurent
  条件: (f : R[X])
  证明: by simp [Polynomial.support]

@[deprecated (since := "2026-06-18")] alias toLaurent_support := support_coeff_toLaurent

Depends on / 依赖: Polynomial, Polynomial.support, support
-/
theorem support_coeff_toLaurent (f : R[X]) :
    f.toLaurent.coeff.support = f.support.map Nat.castEmbedding := by simp [Polynomial.support]

@[deprecated (since := "2026-06-18")] alias toLaurent_support := support_coeff_toLaurent

end Support

section Degrees

/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: (f : R[T;T⁻¹])
  body: f.coeff.support.max

@[simp]

中文:
定义 degree
  签名: (f : R[T;T⁻¹])
  定义体: f.coeff.support.max

@[simp]

Depends on / 依赖: f.coeff.support.max, support
-/
def degree (f : R[T;T⁻¹]) : WithBot Int :=
  f.coeff.support.max

@[simp]
/--
theorem `degree_zero` / 定理 `degree_zero`

English:
theorem degree_zero
  statement: degree (0 : R[T;T⁻¹]) = ⊥
  proof: rfl

@[simp]

中文:
定理 degree_zero
  结论: degree (0 : R[T;T⁻¹]) = ⊥
  证明: rfl

@[simp]
-/
theorem degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ :=
  rfl

@[simp]
/--
theorem `degree_eq_bot_iff` / 定理 `degree_eq_bot_iff`

English:
theorem degree_eq_bot_iff
  given: {f : R[T;T⁻¹]}
  statement: f.degree = ⊥ ↔ f = 0
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h, degree_zero]⟩
  ext n
  simp only [AddMonoidAlgebra.coeff_zero, coe_zero, Pi.ofNat_apply]
  simp_rw [degree, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne,
    WithBot.coe_ne_bot, imp_false, not_not] at h
  exact h n

中文:
定理 degree_eq_bot_iff
  条件: {f : R[T;T⁻¹]}
  结论: f.degree = ⊥ ↔ f = 0
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h, degree_zero]⟩
  ext n
  simp only [AddMonoidAlgebra.coeff_zero, coe_zero, Pi.ofNat_apply]
  simp_rw [degree, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne,
    WithBot.coe_ne_bot, imp_false, not_not] at h
  exact h n

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_zero, Finset, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp, Finsupp.mem_support_iff, Pi.ofNat_apply, WithBot, WithBot.coe_ne_bot, coe_ne_bot, coe_zero, coeff_zero, degree, degree_zero, imp_false, max_eq_sup_withBot, mem_support_iff, not_not, ofNat_apply
-/
theorem degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, degree_zero]⟩
  ext n
  simp only [AddMonoidAlgebra.coeff_zero, coe_zero, Pi.ofNat_apply]
  simp_rw [degree, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne,
    WithBot.coe_ne_bot, imp_false, not_not] at h
  exact h n

section ExactDegrees

@[simp]
/--
theorem `degree_C_mul_T` / 定理 `degree_C_mul_T`

English:
theorem degree_C_mul_T
  given: (n : Int) (a : R) (a0 : a != 0)
  statement: degree (C a * T n) = n
  proof: by
  rw [degree]; rw [support_coeff_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton

中文:
定理 degree_C_mul_T
  条件: (n : 整数) (a : R) (a0 : a != 0)
  结论: degree (C a * T n) = n
  证明: by
  rw [degree]; rw [support_coeff_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton

Depends on / 依赖: Finset, Finset.max_singleton, degree, max_singleton, support_coeff_C_mul_T_of_ne_zero
-/
theorem degree_C_mul_T (n : Int) (a : R) (a0 : a != 0) : degree (C a * T n) = n := by
  rw [degree]; rw [support_coeff_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton

/--
theorem `degree_C_mul_T_ite` / 定理 `degree_C_mul_T_ite`

English:
theorem degree_C_mul_T_ite
  given: [DecidableEq R] (n : Int) (a : R)
  proof: by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne,
      not_false_iff]

@[simp]

中文:
定理 degree_C_mul_T_ite
  条件: [DecidableEq R] (n : 整数) (a : R)
  证明: by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne,
      not_false_iff]

@[simp]

Depends on / 依赖: degree_C_mul_T, degree_zero, map_zero, not_false_iff, split_ifs, zero_mul
-/
theorem degree_C_mul_T_ite [DecidableEq R] (n : Int) (a : R) :
    degree (C a * T n) = if a = 0 then ⊥ else ↑n := by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne,
      not_false_iff]

@[simp]
/--
theorem `degree_T` / 定理 `degree_T`

English:
theorem degree_T
  given: [Nontrivial R] (n : Int)
  statement: (T n : R[T;T⁻¹]).degree = n
  proof: by
  rw [← one_mul (T n)]; rw [← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) != 0)

中文:
定理 degree_T
  条件: [非平凡 R] (n : 整数)
  结论: (T n : R[T;T⁻¹]).degree = n
  证明: by
  rw [← one_mul (T n)]; rw [← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) != 0)

Depends on / 依赖: degree_C_mul_T, map_one, one_mul, one_ne_zero
-/
theorem degree_T [Nontrivial R] (n : Int) : (T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (T n)]; rw [← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) != 0)

/--
theorem `degree_C` / 定理 `degree_C`

English:
theorem degree_C
  given: {a : R} (a0 : a != 0)
  statement: (C a).degree = 0
  proof: by
  rw [← mul_one (C a)]; rw [← T_zero]
  exact degree_C_mul_T 0 a a0

中文:
定理 degree_C
  条件: {a : R} (a0 : a != 0)
  结论: (C a).degree = 0
  证明: by
  rw [← mul_one (C a)]; rw [← T_zero]
  exact degree_C_mul_T 0 a a0

Depends on / 依赖: T_zero, degree_C_mul_T, mul_one
-/
theorem degree_C {a : R} (a0 : a != 0) : (C a).degree = 0 := by
  rw [← mul_one (C a)]; rw [← T_zero]
  exact degree_C_mul_T 0 a a0

/--
theorem `degree_C_ite` / 定理 `degree_C_ite`

English:
theorem degree_C_ite
  given: [DecidableEq R] (a : R)
  statement: (C a).degree = if a = 0 then ⊥ else 0
  proof: by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne, not_false_iff]

中文:
定理 degree_C_ite
  条件: [DecidableEq R] (a : R)
  结论: (C a).degree = if a = 0 then ⊥ else 0
  证明: by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne, not_false_iff]

Depends on / 依赖: degree_C, degree_zero, map_zero, not_false_iff, split_ifs
-/
theorem degree_C_ite [DecidableEq R] (a : R) : (C a).degree = if a = 0 then ⊥ else 0 := by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne, not_false_iff]

end ExactDegrees

section DegreeBounds

/--
theorem `degree_C_mul_T_le` / 定理 `degree_C_mul_T_le`

English:
theorem degree_C_mul_T_le
  given: (n : Int) (a : R)
  statement: degree (C a * T n) <= n
  proof: by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le

中文:
定理 degree_C_mul_T_le
  条件: (n : 整数) (a : R)
  结论: degree (C a * T n) <= n
  证明: by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le

Depends on / 依赖: bot_le, degree_C_mul_T, degree_zero, map_zero, zero_mul
-/
theorem degree_C_mul_T_le (n : Int) (a : R) : degree (C a * T n) <= n := by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le

/--
theorem `degree_T_le` / 定理 `degree_T_le`

English:
theorem degree_T_le
  given: (n : Int)
  statement: (T n : R[T;T⁻¹]).degree <= n
  proof: (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))

中文:
定理 degree_T_le
  条件: (n : 整数)
  结论: (T n : R[T;T⁻¹]).degree <= n
  证明: (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))

Depends on / 依赖: degree_C_mul_T_le, le_of_eq, map_one, one_mul
-/
theorem degree_T_le (n : Int) : (T n : R[T;T⁻¹]).degree <= n :=
  (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))

/--
theorem `degree_C_le` / 定理 `degree_C_le`

English:
theorem degree_C_le
  given: (a : R)
  statement: (C a).degree <= 0
  proof: (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

中文:
定理 degree_C_le
  条件: (a : R)
  结论: (C a).degree <= 0
  证明: (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

Depends on / 依赖: T_zero, degree_C_mul_T_le, le_of_eq, mul_one
-/
theorem degree_C_le (a : R) : (C a).degree <= 0 :=
  (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

end DegreeBounds

end Degrees

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R[X] R[T;T⁻¹]
  body: Module.compHom _ Polynomial.toLaurent

中文:
实例 :
  签名: 模 R[X] R[T;T⁻¹]
  定义体: Module.compHom _ Polynomial.toLaurent

Depends on / 依赖: Module, Module.compHom, Polynomial, Polynomial.toLaurent, compHom, toLaurent
-/
instance : Module R[X] R[T;T⁻¹] :=
  Module.compHom _ Polynomial.toLaurent

instance (R : Type*) [Semiring R] : IsScalarTower R[X] R[X] R[T;T⁻¹] where
  smul_assoc x y z := by rw [smul_eq_mul, mul_smul]

end Semiring

section CommSemiring

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R ->+* S) (x : Sˣ)

/--
Instance `algebraPolynomial` / 实例 `algebraPolynomial`

English:
instance algebraPolynomial
  signature: (R : Type*) [CommSemiring R]
  body: Polynomial.toLaurent
  commutes' := fun f l => by simp [mul_comm]
  smul_def' := fun _ _ => rfl

中文:
实例 algebraPolynomial
  签名: (R : 类型) [交换半环 R]
  定义体: Polynomial.toLaurent
  commutes' := fun f l => by simp [mul_comm]
  smul_def' := fun _ _ => rfl

Depends on / 依赖: Polynomial, Polynomial.toLaurent, toLaurent
-/
instance algebraPolynomial (R : Type*) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] where
  algebraMap := Polynomial.toLaurent
  commutes' := fun f l => by simp [mul_comm]
  smul_def' := fun _ _ => rfl

/--
theorem `algebraMap_X_pow` / 定理 `algebraMap_X_pow`

English:
theorem algebraMap_X_pow
  given: (n : Nat)
  statement: algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n
  proof: Polynomial.toLaurent_X_pow n

@[simp]

中文:
定理 algebraMap_X_pow
  条件: (n : 自然数)
  结论: algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n
  证明: Polynomial.toLaurent_X_pow n

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_X_pow, toLaurent_X_pow
-/
theorem algebraMap_X_pow (n : Nat) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n :=
  Polynomial.toLaurent_X_pow n

@[simp]
/--
theorem `algebraMap_eq_toLaurent` / 定理 `algebraMap_eq_toLaurent`

English:
theorem algebraMap_eq_toLaurent
  given: (f : R[X])
  statement: algebraMap R[X] R[T;T⁻¹] f = toLaurent f
  proof: rfl

中文:
定理 algebraMap_eq_toLaurent
  条件: (f : R[X])
  结论: algebraMap R[X] R[T;T⁻¹] f = toLaurent f
  证明: rfl
-/
theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f :=
  rfl

/--
Instance `isLocalization` / 实例 `isLocalization`

English:
instance isLocalization
  signature: : IsLocalization.Away (X : R[X]) R[T;T⁻¹]
  body: { map_units := fun ⟨t, ht⟩ => by
      obtain ⟨n, rfl⟩ := ht
      rw [algebraMap_eq_toLaurent]; rw [toLaurent_X_pow]
      exact isUnit_T ↑n
    surj f := by
      induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
      have : X ^ n in Submonoid.powers (X : R[X]) := ⟨n, rfl⟩
      refine ⟨(f, ⟨_, this⟩), ?_⟩
      simp only [algebraMap_eq_toLaurent, toLaurent_X_pow, mul_T_assoc, neg_add_cancel, T_zero,
        mul_one]
    exists_of_eq := fun {f g} => by
      rw [algebraMap_eq_toLaurent]; rw [algebraMap_eq_toLaurent]; rw [Polynomial.toLaurent_inj]
      rintro rfl
      exact ⟨1, rfl⟩ }

中文:
实例 isLocalization
  签名: : 是Localization.Away (X : R[X]) R[T;T⁻¹]
  定义体: { map_units := fun ⟨t, ht⟩ => by
      obtain ⟨n, rfl⟩ := ht
      rw [algebraMap_eq_toLaurent]; rw [toLaurent_X_pow]
      exact isUnit_T ↑n
    surj f := by
      induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
      have : X ^ n in Submonoid.powers (X : R[X]) := ⟨n, rfl⟩
      refine ⟨(f, ⟨_, this⟩), ?_⟩
      simp only [algebraMap_eq_toLaurent, toLaurent_X_pow, mul_T_assoc, neg_add_cancel, T_zero,
        mul_one]
    exists_of_eq := fun {f g} => by
      rw [algebraMap_eq_toLaurent]; rw [algebraMap_eq_toLaurent]; rw [Polynomial.toLaurent_inj]
      rintro rfl
      exact ⟨1, rfl⟩ }

Depends on / 依赖: LaurentPolynomial, LaurentPolynomial.induction_on_mul_T, Polynomial, Polynomial.toLau, Submonoid, Submonoid.powers, T_zero, algebraMap_eq_toLaurent, exists_of_eq, induction_on_mul_T, isUnit_T, map_units, mul_T_assoc, mul_one, neg_add_cancel, powers, toLaurent_X_pow
-/
instance isLocalization : IsLocalization.Away (X : R[X]) R[T;T⁻¹] :=
  { map_units := fun ⟨t, ht⟩ => by
      obtain ⟨n, rfl⟩ := ht
      rw [algebraMap_eq_toLaurent]; rw [toLaurent_X_pow]
      exact isUnit_T ↑n
    surj f := by
      induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
      have : X ^ n in Submonoid.powers (X : R[X]) := ⟨n, rfl⟩
      refine ⟨(f, ⟨_, this⟩), ?_⟩
      simp only [algebraMap_eq_toLaurent, toLaurent_X_pow, mul_T_assoc, neg_add_cancel, T_zero,
        mul_one]
    exists_of_eq := fun {f g} => by
      rw [algebraMap_eq_toLaurent]; rw [algebraMap_eq_toLaurent]; rw [Polynomial.toLaurent_inj]
      rintro rfl
      exact ⟨1, rfl⟩ }

/--
theorem `mk'_mul_T` / 定理 `mk'_mul_T`

English:
theorem mk'_mul_T
  given: (p : R[X]) (n : Nat)
  proof: by
  rw [← toLaurent_X_pow]; rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.mk'_spec]; rw [algebraMap_eq_toLaurent]

@[simp]

中文:
定理 mk'_mul_T
  条件: (p : R[X]) (n : 自然数)
  证明: by
  rw [← toLaurent_X_pow]; rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.mk'_spec]; rw [algebraMap_eq_toLaurent]

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.mk, _spec, algebraMap_eq_toLaurent, toLaurent_X_pow
-/
theorem mk'_mul_T (p : R[X]) (n : Nat) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) * T n =
      toLaurent p := by
  rw [← toLaurent_X_pow]; rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.mk'_spec]; rw [algebraMap_eq_toLaurent]

@[simp]
/--
theorem `mk'_eq` / 定理 `mk'_eq`

English:
theorem mk'_eq
  given: (p : R[X]) (n : Nat)
  proof: by
  rw [← IsUnit.mul_left_inj (isUnit_T n)]; rw [mul_T_assoc]; rw [neg_add_cancel]; rw [T_zero]; rw [mul_one]
  exact mk'_mul_T p n

中文:
定理 mk'_eq
  条件: (p : R[X]) (n : 自然数)
  证明: by
  rw [← IsUnit.mul_left_inj (isUnit_T n)]; rw [mul_T_assoc]; rw [neg_add_cancel]; rw [T_zero]; rw [mul_one]
  exact mk'_mul_T p n
-/
theorem mk'_eq (p : R[X]) (n : Nat) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) =
      toLaurent p * T (-n) := by
  rw [← IsUnit.mul_left_inj (isUnit_T n)]; rw [mul_T_assoc]; rw [neg_add_cancel]; rw [T_zero]; rw [mul_one]
  exact mk'_mul_T p n

/--
theorem `mk'_one_X_pow` / 定理 `mk'_one_X_pow`

English:
theorem mk'_one_X_pow
  given: (n : Nat)
  proof: by
  rw [mk'_eq 1 n]; rw [toLaurent_one]; rw [one_mul]

中文:
定理 mk'_one_X_pow
  条件: (n : 自然数)
  证明: by
  rw [mk'_eq 1 n]; rw [toLaurent_one]; rw [one_mul]
-/
theorem mk'_one_X_pow (n : Nat) :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) = T (-n) := by
  rw [mk'_eq 1 n]; rw [toLaurent_one]; rw [one_mul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mk'_one_X` / 定理 `mk'_one_X`

English:
theorem mk'_one_X
  proof: by
  convert! mk'_one_X_pow 1
  exact (pow_one X).symm

中文:
定理 mk'_one_X
  证明: by
  convert! mk'_one_X_pow 1
  exact (pow_one X).symm
-/
theorem mk'_one_X :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X, 1, pow_one X⟩ : Submonoid.powers (X : R[X])) = T (-1) := by
  convert! mk'_one_X_pow 1
  exact (pow_one X).symm

/--
Definition of `eval₂` / `eval₂` 的定义

English:
definition eval₂
  signature: : R[T;T⁻¹] ->+* S
  body: IsLocalization.lift (M := Submonoid.powers (X : R[X])) (g := Polynomial.eval₂RingHom f x) by
    rintro ⟨y, n, rfl⟩
    simpa only [coe_eval₂RingHom, eval₂_X_pow] using x.isUnit.pow n

@[simp]

中文:
定义 eval₂
  签名: : R[T;T⁻¹] ->+* S
  定义体: IsLocalization.lift (M := Submonoid.powers (X : R[X])) (g := Polynomial.eval₂RingHom f x) by
    rintro ⟨y, n, rfl⟩
    simpa only [coe_eval₂RingHom, eval₂_X_pow] using x.isUnit.pow n

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.lift, Polynomial, Polynomial.eval, Submonoid, Submonoid.powers, isUnit, powers, x.isUnit.pow
-/
def eval₂ : R[T;T⁻¹] ->+* S :=
IsLocalization.lift (M := Submonoid.powers (X : R[X])) (g := Polynomial.eval₂RingHom f x) by
    rintro ⟨y, n, rfl⟩
    simpa only [coe_eval₂RingHom, eval₂_X_pow] using x.isUnit.pow n

@[simp]
/--
theorem `eval₂_toLaurent` / 定理 `eval₂_toLaurent`

English:
theorem eval₂_toLaurent
  given: (p : R[X])
  statement: eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p
  proof: by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.lift_eq]; rw [coe_eval₂RingHom]

中文:
定理 eval₂_toLaurent
  条件: (p : R[X])
  结论: eval₂ f x (toLaurent p) = 多项式.eval₂ f x p
  证明: by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.lift_eq]; rw [coe_eval₂RingHom]

Depends on / 依赖: IsLocalization, IsLocalization.lift_eq, algebraMap_eq_toLaurent, lift_eq
-/
theorem eval₂_toLaurent (p : R[X]) : eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p := by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent]; rw [IsLocalization.lift_eq]; rw [coe_eval₂RingHom]

/--
theorem `eval₂_T_n` / 定理 `eval₂_T_n`

English:
theorem eval₂_T_n
  given: (n : Nat)
  statement: eval₂ f x (T n) = x ^ n
  proof: by
  rw [← Polynomial.toLaurent_X_pow]; rw [eval₂_toLaurent]; rw [eval₂_X_pow]

中文:
定理 eval₂_T_n
  条件: (n : 自然数)
  结论: eval₂ f x (T n) = x ^ n
  证明: by
  rw [← Polynomial.toLaurent_X_pow]; rw [eval₂_toLaurent]; rw [eval₂_X_pow]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_X_pow, toLaurent_X_pow
-/
theorem eval₂_T_n (n : Nat) : eval₂ f x (T n) = x ^ n := by
  rw [← Polynomial.toLaurent_X_pow]; rw [eval₂_toLaurent]; rw [eval₂_X_pow]

/--
theorem `eval₂_T_neg_n` / 定理 `eval₂_T_neg_n`

English:
theorem eval₂_T_neg_n
  given: (n : Nat)
  statement: eval₂ f x (T (-n)) = x⁻¹ ^ n
  proof: by
  rw [← mk'_one_X_pow]
  unfold eval₂
  rw [IsLocalization.lift_mk'_spec]; rw [map_one]; rw [coe_eval₂RingHom]; rw [eval₂_X_pow]; rw [← mul_pow]; rw [Units.mul_inv]; rw [one_pow]

@[simp]

中文:
定理 eval₂_T_neg_n
  条件: (n : 自然数)
  结论: eval₂ f x (T (-n)) = x⁻¹ ^ n
  证明: by
  rw [← mk'_one_X_pow]
  unfold eval₂
  rw [IsLocalization.lift_mk'_spec]; rw [map_one]; rw [coe_eval₂RingHom]; rw [eval₂_X_pow]; rw [← mul_pow]; rw [Units.mul_inv]; rw [one_pow]

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.lift_mk, Units.mul_inv, _one_X_pow, _spec, lift_mk, map_one, mul_inv, mul_pow, one_pow
-/
theorem eval₂_T_neg_n (n : Nat) : eval₂ f x (T (-n)) = x⁻¹ ^ n := by
  rw [← mk'_one_X_pow]
  unfold eval₂
  rw [IsLocalization.lift_mk'_spec]; rw [map_one]; rw [coe_eval₂RingHom]; rw [eval₂_X_pow]; rw [← mul_pow]; rw [Units.mul_inv]; rw [one_pow]

@[simp]
/--
theorem `eval₂_T` / 定理 `eval₂_T`

English:
theorem eval₂_T
  given: (n : Int)
  statement: eval₂ f x (T n) = (x ^ n).val
  proof: by
  by_cases! hn : 0 <= n
  · lift n to Nat using hn
    apply eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [eval₂_T_neg_n]; rw [zpow_neg]; rw [zpow_natCast]; rw [← inv_pow]; rw [Units.val_pow_eq_pow_val]

@[simp]

中文:
定理 eval₂_T
  条件: (n : 整数)
  结论: eval₂ f x (T n) = (x ^ n).val
  证明: by
  by_cases! hn : 0 <= n
  · lift n to Nat using hn
    apply eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [eval₂_T_neg_n]; rw [zpow_neg]; rw [zpow_natCast]; rw [← inv_pow]; rw [Units.val_pow_eq_pow_val]

@[simp]

Depends on / 依赖: Int.exists_eq_neg_ofNat, Units.val_pow_eq_pow_val, exists_eq_neg_ofNat, hn.le, inv_pow, val_pow_eq_pow_val, zpow_natCast, zpow_neg
-/
theorem eval₂_T (n : Int) : eval₂ f x (T n) = (x ^ n).val := by
  by_cases! hn : 0 <= n
  · lift n to Nat using hn
    apply eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [eval₂_T_neg_n]; rw [zpow_neg]; rw [zpow_natCast]; rw [← inv_pow]; rw [Units.val_pow_eq_pow_val]

@[simp]
/--
theorem `eval₂_C` / 定理 `eval₂_C`

English:
theorem eval₂_C
  given: (r : R)
  statement: eval₂ f x (C r) = f r
  proof: by
  rw [← toLaurent_C]; rw [eval₂_toLaurent]; rw [Polynomial.eval₂_C]

中文:
定理 eval₂_C
  条件: (r : R)
  结论: eval₂ f x (C r) = f r
  证明: by
  rw [← toLaurent_C]; rw [eval₂_toLaurent]; rw [Polynomial.eval₂_C]

Depends on / 依赖: Polynomial, Polynomial.eval, toLaurent_C
-/
theorem eval₂_C (r : R) : eval₂ f x (C r) = f r := by
  rw [← toLaurent_C]; rw [eval₂_toLaurent]; rw [Polynomial.eval₂_C]

/--
theorem `eval₂_C_mul_T_n` / 定理 `eval₂_C_mul_T_n`

English:
theorem eval₂_C_mul_T_n
  given: (r : R) (n : Nat)
  statement: eval₂ f x (C r * T n) = f r * x ^ n
  proof: by
  rw [← Polynomial.toLaurent_C_mul_T]; rw [eval₂_toLaurent]; rw [eval₂_monomial]

中文:
定理 eval₂_C_mul_T_n
  条件: (r : R) (n : 自然数)
  结论: eval₂ f x (C r * T n) = f r * x ^ n
  证明: by
  rw [← Polynomial.toLaurent_C_mul_T]; rw [eval₂_toLaurent]; rw [eval₂_monomial]

Depends on / 依赖: Polynomial, Polynomial.toLaurent_C_mul_T, toLaurent_C_mul_T
-/
theorem eval₂_C_mul_T_n (r : R) (n : Nat) : eval₂ f x (C r * T n) = f r * x ^ n := by
  rw [← Polynomial.toLaurent_C_mul_T]; rw [eval₂_toLaurent]; rw [eval₂_monomial]

/--
theorem `eval₂_C_mul_T_neg_n` / 定理 `eval₂_C_mul_T_neg_n`

English:
theorem eval₂_C_mul_T_neg_n
  given: (r : R) (n : Nat)
  statement: eval₂ f x (C r * T (-n)) = f r * x⁻¹ ^ n
  proof: by
  rw [map_mul]; rw [eval₂_T_neg_n]; rw [eval₂_C]

@[simp]

中文:
定理 eval₂_C_mul_T_neg_n
  条件: (r : R) (n : 自然数)
  结论: eval₂ f x (C r * T (-n)) = f r * x⁻¹ ^ n
  证明: by
  rw [map_mul]; rw [eval₂_T_neg_n]; rw [eval₂_C]

@[simp]

Depends on / 依赖: map_mul
-/
theorem eval₂_C_mul_T_neg_n (r : R) (n : Nat) : eval₂ f x (C r * T (-n)) = f r * x⁻¹ ^ n := by
  rw [map_mul]; rw [eval₂_T_neg_n]; rw [eval₂_C]

@[simp]
/--
theorem `eval₂_C_mul_T` / 定理 `eval₂_C_mul_T`

English:
theorem eval₂_C_mul_T
  given: (r : R) (n : Int)
  statement: eval₂ f x (C r * T n) = f r * (x ^ n).val
  proof: by
  simp

中文:
定理 eval₂_C_mul_T
  条件: (r : R) (n : 整数)
  结论: eval₂ f x (C r * T n) = f r * (x ^ n).val
  证明: by
  simp
-/
theorem eval₂_C_mul_T (r : R) (n : Int) : eval₂ f x (C r * T n) = f r * (x ^ n).val := by
  simp

end CommSemiring

section Inversion

variable {R : Type*} [CommSemiring R]

/--
Definition of `invert` / `invert` 的定义

English:
definition invert
  signature: : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]
  body: AddMonoidAlgebra.domCongr R R AddEquiv.neg _

中文:
定义 invert
  签名: : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]
  定义体: AddMonoidAlgebra.domCongr R R AddEquiv.neg _

Depends on / 依赖: AddEquiv, AddEquiv.neg, AddMonoidAlgebra, AddMonoidAlgebra.domCongr, domCongr
-/
def invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] := AddMonoidAlgebra.domCongr R R AddEquiv.neg _

/--
lemma `invert_T` / 引理 `invert_T`

English:
lemma invert_T
  given: (n : Int)
  statement: invert (T n : R[T;T⁻¹]) = T (-n)
  proof: AddMonoidAlgebra.domCongr_single ..

中文:
引理 invert_T
  条件: (n : 整数)
  结论: invert (T n : R[T;T⁻¹]) = T (-n)
  证明: AddMonoidAlgebra.domCongr_single ..
-/
@[simp] lemma invert_T (n : Int) : invert (T n : R[T;T⁻¹]) = T (-n) :=
  AddMonoidAlgebra.domCongr_single ..

/--
lemma `invert_apply` / 引理 `invert_apply`

English:
lemma invert_apply
  given: (f : R[T;T⁻¹]) (n : Int)
  statement: (invert f).coeff n = f.coeff (-n)
  proof: by
  simp [invert]

中文:
引理 invert_apply
  条件: (f : R[T;T⁻¹]) (n : 整数)
  结论: (invert f).coeff n = f.coeff (-n)
  证明: by
  simp [invert]
-/
@[simp] lemma invert_apply (f : R[T;T⁻¹]) (n : Int) : (invert f).coeff n = f.coeff (-n) := by
  simp [invert]

/--
lemma `invert_comp_C` / 引理 `invert_comp_C`

English:
lemma invert_comp_C
  statement: invert ∘ (@C R _) = C
  proof: by ext; simp

中文:
引理 invert_comp_C
  结论: invert ∘ (@C R _) = C
  证明: by ext; simp
-/
@[simp] lemma invert_comp_C : invert ∘ (@C R _) = C := by ext; simp

/--
lemma `invert_C` / 引理 `invert_C`

English:
lemma invert_C
  given: (t : R)
  statement: invert (C t) = C t
  proof: by ext; simp

中文:
引理 invert_C
  条件: (t : R)
  结论: invert (C t) = C t
  证明: by ext; simp
-/
@[simp] lemma invert_C (t : R) : invert (C t) = C t := by ext; simp

/--
lemma `involutive_invert` / 引理 `involutive_invert`

English:
lemma involutive_invert
  statement: Involutive (invert (R := R))
  proof: fun _ => by ext; simp

中文:
引理 involutive_invert
  结论: 对合 (invert (R := R))
  证明: fun _ => by ext; simp
-/
lemma involutive_invert : Involutive (invert (R := R)) := fun _ => by ext; simp

/--
lemma `invert_symm` / 引理 `invert_symm`

English:
lemma invert_symm
  statement: (invert (R := R)).symm = invert
  proof: rfl

中文:
引理 invert_symm
  结论: (invert (R := R)).symm = invert
  证明: rfl
-/
@[simp] lemma invert_symm : (invert (R := R)).symm = invert := rfl

/--
lemma `toLaurent_reverse` / 引理 `toLaurent_reverse`

English:
lemma toLaurent_reverse
  given: (p : R[X])
  proof: by
  nontriviality R
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC _ _ _ _ ih => simp [add_mul, ← ih]
  | MX _ hp => simpa [natDegree_mul_X hp]

中文:
引理 toLaurent_reverse
  条件: (p : R[X])
  证明: by
  nontriviality R
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC _ _ _ _ ih => simp [add_mul, ← ih]
  | MX _ hp => simpa [natDegree_mul_X hp]

Depends on / 依赖: Polynomial, Polynomial.recOnHorner, add_mul, natDegree_mul_X, nontriviality, recOnHorner
-/
lemma toLaurent_reverse (p : R[X]) :
    toLaurent p.reverse = invert (toLaurent p) * (T p.natDegree) := by
  nontriviality R
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC _ _ _ _ ih => simp [add_mul, ← ih]
  | MX _ hp => simpa [natDegree_mul_X hp]

end Inversion

section Smeval

section SMulWithZero

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

/--
Definition of `smeval` / `smeval` 的定义

English:
definition smeval
  signature: : S
  body: f.coeff.sum fun n r => r • (x ^ n).val

中文:
定义 smeval
  签名: : S
  定义体: f.coeff.sum fun n r => r • (x ^ n).val

Depends on / 依赖: f.coeff.sum
-/
def smeval : S := f.coeff.sum fun n r => r • (x ^ n).val

/--
theorem `smeval_eq_sum` / 定理 `smeval_eq_sum`

English:
theorem smeval_eq_sum
  statement: f.smeval x = f.coeff.sum fun n r => r • (x ^ n).val
  proof: rfl

中文:
定理 smeval_eq_sum
  结论: f.smeval x = f.coeff.求和 fun n r => r • (x ^ n).val
  证明: rfl
-/
theorem smeval_eq_sum : f.smeval x = f.coeff.sum fun n r => r • (x ^ n).val := rfl

/--
theorem `smeval_congr` / 定理 `smeval_congr`

English:
theorem smeval_congr
  statement: f = g -> x = y -> f.smeval x = g.smeval y
  proof: by rintro rfl rfl; rfl

中文:
定理 smeval_congr
  结论: f = g -> x = y -> f.smeval x = g.smeval y
  证明: by rintro rfl rfl; rfl
-/
theorem smeval_congr : f = g -> x = y -> f.smeval x = g.smeval y := by rintro rfl rfl; rfl

/--
lemma `smeval_zero` / 引理 `smeval_zero`

English:
lemma smeval_zero
  statement: (0 : R[T;T⁻¹]).smeval x = (0 : S)
  proof: by simp [smeval]

中文:
引理 smeval_zero
  结论: (0 : R[T;T⁻¹]).smeval x = (0 : S)
  证明: by simp [smeval]
-/
@[simp] lemma smeval_zero : (0 : R[T;T⁻¹]).smeval x = (0 : S) := by simp [smeval]

/--
theorem `smeval_single` / 定理 `smeval_single`

English:
theorem smeval_single
  given: (n : Int) (r : R)
  statement: smeval (.single n r) x = r • (x ^ n).val
  proof: by
  simp [smeval, -single_eq_C_mul_T]

@[simp]

中文:
定理 smeval_single
  条件: (n : 整数) (r : R)
  结论: smeval (.single n r) x = r • (x ^ n).val
  证明: by
  simp [smeval, -single_eq_C_mul_T]

@[simp]

Depends on / 依赖: single_eq_C_mul_T, smeval
-/
theorem smeval_single (n : Int) (r : R) : smeval (.single n r) x = r • (x ^ n).val := by
  simp [smeval, -single_eq_C_mul_T]

@[simp]
/--
theorem `smeval_C_mul_T_n` / 定理 `smeval_C_mul_T_n`

English:
theorem smeval_C_mul_T_n
  given: (n : Int) (r : R)
  statement: (C r * T n).smeval x = r • (x ^ n).val
  proof: by
  rw [← single_eq_C_mul_T]; rw [smeval_single]

@[simp]

中文:
定理 smeval_C_mul_T_n
  条件: (n : 整数) (r : R)
  结论: (C r * T n).smeval x = r • (x ^ n).val
  证明: by
  rw [← single_eq_C_mul_T]; rw [smeval_single]

@[simp]

Depends on / 依赖: single_eq_C_mul_T, smeval_single
-/
theorem smeval_C_mul_T_n (n : Int) (r : R) : (C r * T n).smeval x = r • (x ^ n).val := by
  rw [← single_eq_C_mul_T]; rw [smeval_single]

@[simp]
/--
theorem `smeval_C` / 定理 `smeval_C`

English:
theorem smeval_C
  given: (r : R)
  statement: (C r).smeval x = r • 1
  proof: by
  rw [← single_eq_C]; rw [smeval_single x (0 : Int) r]; rw [zpow_zero]; rw [Units.val_one]

中文:
定理 smeval_C
  条件: (r : R)
  结论: (C r).smeval x = r • 1
  证明: by
  rw [← single_eq_C]; rw [smeval_single x (0 : Int) r]; rw [zpow_zero]; rw [Units.val_one]

Depends on / 依赖: Units.val_one, single_eq_C, smeval_single, val_one, zpow_zero
-/
theorem smeval_C (r : R) : (C r).smeval x = r • 1 := by
  rw [← single_eq_C]; rw [smeval_single x (0 : Int) r]; rw [zpow_zero]; rw [Units.val_one]

end SMulWithZero

section MulActionWithZero

variable [Semiring R] [AddCommMonoid S] [MulActionWithZero R S] [Monoid S] (f g : R[T;T⁻¹])
  (x y : Sˣ)

@[simp]
/--
theorem `smeval_T_pow` / 定理 `smeval_T_pow`

English:
theorem smeval_T_pow
  given: (n : Int) (x : Sˣ)
  statement: (T n : R[T;T⁻¹]).smeval x = (x ^ n).val
  proof: by
  rw [T]; rw [smeval_single]; rw [one_smul]

@[simp]

中文:
定理 smeval_T_pow
  条件: (n : 整数) (x : Sˣ)
  结论: (T n : R[T;T⁻¹]).smeval x = (x ^ n).val
  证明: by
  rw [T]; rw [smeval_single]; rw [one_smul]

@[simp]

Depends on / 依赖: one_smul, smeval_single
-/
theorem smeval_T_pow (n : Int) (x : Sˣ) : (T n : R[T;T⁻¹]).smeval x = (x ^ n).val := by
  rw [T]; rw [smeval_single]; rw [one_smul]

@[simp]
/--
theorem `smeval_one` / 定理 `smeval_one`

English:
theorem smeval_one
  statement: (1 : R[T;T⁻¹]).smeval x = 1
  proof: by
  rw [← T_zero]; rw [smeval_T_pow 0 x]; rw [zpow_zero]; rw [Units.val_eq_one]

中文:
定理 smeval_one
  结论: (1 : R[T;T⁻¹]).smeval x = 1
  证明: by
  rw [← T_zero]; rw [smeval_T_pow 0 x]; rw [zpow_zero]; rw [Units.val_eq_one]

Depends on / 依赖: T_zero, Units.val_eq_one, smeval_T_pow, val_eq_one, zpow_zero
-/
theorem smeval_one : (1 : R[T;T⁻¹]).smeval x = 1 := by
  rw [← T_zero]; rw [smeval_T_pow 0 x]; rw [zpow_zero]; rw [Units.val_eq_one]

end MulActionWithZero

section Module

variable [Semiring R] [AddCommMonoid S] [Module R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

@[simp]
/--
theorem `smeval_add` / 定理 `smeval_add`

English:
theorem smeval_add
  statement: (f + g).smeval x = f.smeval x + g.smeval x
  proof: by
  simp [smeval, Finsupp.sum_add_index, add_smul]

@[simp]

中文:
定理 smeval_add
  结论: (f + g).smeval x = f.smeval x + g.smeval x
  证明: by
  simp [smeval, Finsupp.sum_add_index, add_smul]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, add_smul, smeval, sum_add_index
-/
theorem smeval_add : (f + g).smeval x = f.smeval x + g.smeval x := by
  simp [smeval, Finsupp.sum_add_index, add_smul]

@[simp]
/--
theorem `smeval_C_mul` / 定理 `smeval_C_mul`

English:
theorem smeval_C_mul
  given: (r : R)
  statement: (C r * f).smeval x = r • (f.smeval x)
  proof: by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add]; rw [smeval_add]; rw [smeval_add]; rw [smul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← map_mul]; rw [smeval_C_mul_T_n]; rw [smeval_C_mul_T_n]; rw [mul_smul]

中文:
定理 smeval_C_mul
  条件: (r : R)
  结论: (C r * f).smeval x = r • (f.smeval x)
  证明: by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add]; rw [smeval_add]; rw [smeval_add]; rw [smul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← map_mul]; rw [smeval_C_mul_T_n]; rw [smeval_C_mul_T_n]; rw [mul_smul]

Depends on / 依赖: C_mul_T, LaurentPolynomial, LaurentPolynomial.induction_on, induction_on, map_mul, mul_add, mul_assoc, mul_smul, smeval_C_mul_T_n, smeval_add, smul_add
-/
theorem smeval_C_mul (r : R) : (C r * f).smeval x = r • (f.smeval x) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add]; rw [smeval_add]; rw [smeval_add]; rw [smul_add]; rw [hp]; rw [hq]
  | C_mul_T n s =>
    rw [← mul_assoc]; rw [← map_mul]; rw [smeval_C_mul_T_n]; rw [smeval_C_mul_T_n]; rw [mul_smul]

variable (R) in
/-- Evaluation as an `R`-linear map. -/
@[simps]
/--
Definition of `leval` / `leval` 的定义

English:
definition leval
  signature: : R[T;T⁻¹] ->ₗ[R] S where
  body: f.smeval x
  map_add' f g := smeval_add f g x
  map_smul' r f := by simp [smul_eq_C_mul]

中文:
定义 leval
  签名: : R[T;T⁻¹] ->ₗ[R] S where
  定义体: f.smeval x
  map_add' f g := smeval_add f g x
  map_smul' r f := by simp [smul_eq_C_mul]

Depends on / 依赖: f.smeval, smeval
-/
def leval : R[T;T⁻¹] ->ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := smeval_add f g x
  map_smul' r f := by simp [smul_eq_C_mul]

end Module

end Smeval

end LaurentPolynomial
