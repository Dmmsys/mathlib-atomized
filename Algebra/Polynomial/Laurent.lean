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

We introduce Laurent polynomials over a semiring `R`.  Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`.  Thus, negative exponents are allowed.  The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials.

## Notation
The symbol `R[T;T⁻¹]` stands for `LaurentPolynomial R`.  We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `AddMonoidAlgebra R ℤ`.
Thus, they are essentially `Finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `Polynomial`, that instead shields away
the implementation via `Finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `LaurentPolynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `Finsupp` implementation of `R[X]` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

## Future work
Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- A "better" definition of `trunc` would be as an `R`-linear map.  This works:
--  ```
--  def trunc : R[T;T⁻¹] →[R] R[X] :=
--    refine (?_ : R[ℕ] →[R] R[X]).comp ?_
--    · exact ⟨(toFinsuppIso R).symm, by simp⟩
--    · refine ⟨fun r ↦ comapDomain _ r
--        (Set.injOn_of_injective (fun _ _ ↦ Int.ofNat.inj) _), ?_⟩
--      exact fun r f ↦ comapDomain_smul ..
--  ```
--  but it would make sense to bundle the maps better, for a smoother user experience.
--  I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
--  this stage of the Laurent process!
--  This would likely involve adding a `comapDomain` analogue of
--  `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
--  `Polynomial.toFinsuppIso`.
-- Add `degree, intDegree, intTrailingDegree, leadingCoeff, trailingCoeff,...`.
-/

@[expose] public section


open Polynomial Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R S : Type*}

/-- The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
/-
**LaurentPolynomial** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LaurentPolynomial (R : Type*) [Semiring R]
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomi
als.
-/
abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R ℤ

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

open LaurentPolynomial

@[ext]
/-
**LaurentPolynomial.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : forall a, p.coeff
 a = q.coeff a) : p = q
参数：h : forall a, p.coeff a = q.coeff a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : ∀ a, p.coeff a = q.coeff a) :
    p = q := by ext; exact h _

/-- The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
/-
**Polynomial.toLaurent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.toLaurent [Semiring R] : R[X] ->+* R[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent
 polynomial
with coefficients in `R`.
-/
def Polynomial.toLaurent [Semiring R] : R[X] →+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R).toRingHom

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
/-
**Polynomial.toLaurent_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.toLaurent_apply [Semiring R] (p : R[X]) : toLaurent p = p.toFin
supp.mapDomain (↑)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not a simp lemma, as it is usually preferable to use the lemmas about `C
` and `X`
instead.
-/
theorem Polynomial.toLaurent_apply [Semiring R] (p : R[X]) :
    toLaurent p = p.toFinsupp.mapDomain (↑) :=
  rfl

/-- The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
/-
**Polynomial.toLaurentAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.toLaurentAlg [CommSemiring R] : R[X] ->ₐ[R] R[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent p
olynomial
with coefficients in `R`.
-/
def Polynomial.toLaurentAlg [CommSemiring R] : R[X] →ₐ[R] R[T;T⁻¹] :=
  (mapDomainAlgHom R R Int.ofNatHom).comp (toFinsuppIsoAlg R).toAlgHom
/-
**Polynomial.coe_toLaurentAlg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], ⇑Polynomial.toLaurentAlg = ⇑Poly
nomial.toLaurent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Polynomial.coe_toLaurentAlg [CommSemiring R] :
    (toLaurentAlg : R[X] → R[T;T⁻¹]) = toLaurent :=
  rfl
/-
**Polynomial.toLaurentAlg_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : toLaurentAlg f
 = toLaurent f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : toLaurentAlg f = toLaurent f :=
  rfl

namespace LaurentPolynomial

section Semiring

variable [Semiring R]

/-
**LaurentPolynomial.single_zero_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPol
ynomial`。
形式化陈述：single_zero_one_eq_one : (.single 0 1 : R[T;T⁻¹]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_one_eq_one : (.single 0 1 : R[T;T⁻¹]) = 1 := rfl

/-!  ### The functions `C` and `T`. -/

/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
/-
**LaurentPolynomial.C** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：C : R ->+* R[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism `C`, including `R` into the ring of Laurent polynomials ov
er `R` as
the constant Laurent polynomials.
-/
def C : R →+* R[T;T⁻¹] :=
  singleZeroRingHom
/-
**LaurentPolynomial.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomia
l`。
形式化陈述：algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
 (r : R) : algebraMap R (LaurentPolynomial A) r = C (algebraMap R A r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = C (algebraMap R A r) :=
  rfl

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
/-
**LaurentPolynomial.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial
`。
形式化陈述：C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R 
R[T;T⁻¹] r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R
[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which 
case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R R[T;T⁻¹] r :=
  rfl
/-
**LaurentPolynomial.single_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：single_eq_C (r : R) : .single 0 r = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_C (r : R) : .single 0 r = C r := rfl
/-
**LaurentPolynomial.C_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (t : R) (n : ℤ), (LaurentPolynomial.C
 t).coeff n = if n = 0 then t else 0
参数：t : R；n : ℤ；LaurentPolynomial.C t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma C_apply (t : R) (n : ℤ) : (C t).coeff n = if n = 0 then t else 0 := by
  simp [← single_eq_C]; aesop

/-- The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
/-
**LaurentPolynomial.T** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：T (n : Int) : R[T;T⁻¹]
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type 
`ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extr
a coercions.
For these reasons, the definition of `T` is as a sequence.
-/
def T (n : ℤ) : R[T;T⁻¹] := .single n 1
/-
**LaurentPolynomial.T_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (m n : ℤ), (LaurentPolynomial.T n).co
eff m = if n = m then 1 else 0
参数：m n : ℤ；LaurentPolynomial.T n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
@[simp] lemma T_apply (m n : ℤ) : (T n : R[T;T⁻¹]).coeff m = if n = m then 1 else 0 :=
  Finsupp.single_apply

@[simp]
/-
**LaurentPolynomial.T_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：T_zero : (T 0 : R[T;T⁻¹]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem T_zero : (T 0 : R[T;T⁻¹]) = 1 :=
  rfl
/-
**LaurentPolynomial.T_add** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：T_add (m n : Int) : (T (m + n) : R[T;T⁻¹]) = T m * T n
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n := by
  simp [T, single_mul_single]
/-
**LaurentPolynomial.T_sub** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：T_sub (m n : Int) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n)
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.T_add`：T_add (m n : Int) : (T (m + n) : R[T;T⁻¹]) = T 
m * T n
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem T_sub (m n : ℤ) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n) := by rw [← T_add, sub_eq_add_neg]

@[simp]
/-
**LaurentPolynomial.T_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：T_pow (m : Int) (n : Nat) : (T m ^ n : R[T;T⁻¹]) = T (n * m)
参数：m : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.T.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℤ), 
LaurentPolynomial.T n = AddMonoidAlgebra.single n 1
· 使用定理 `AddMonoidAlgebra.single_pow`：∀ {R : Type u_1} {M : Type u_4} [inst : Sem
iring R] [inst_1 : AddMonoid M] (m : M) (r : R) (n : ℕ),   AddMonoidAlgebra.sing
le m r ^ n = AddM…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
theorem T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) := by
  rw [T, T, single_pow, one_pow, nsmul_eq_mul]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
/-
**LaurentPolynomial.mul_T_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : f * T m * T n = f * T (m + n)
参数：f : R[T;T⁻¹]；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `simp` version of `mul_assoc`, in the presence of `T`'s.
-/
theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * T m * T n = f * T (m + n) := by
  simp [← T_add, mul_assoc]

@[simp]
/-
**LaurentPolynomial.single_eq_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：single_eq_C_mul_T (r : R) (n : Int) : .single n r = C r * T n
参数：r : R；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.singleZeroRingHom_apply`：∀ {R : Type u_1} {M : Type u_4
} [inst : Semiring R] [inst_1 : AddZeroClass M] (a : R),   AddMonoidAlgebra.sing
leZeroRingHom a = (↑(AddMonoid…
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_eq_C_mul_T (r : R) (n : ℤ) : .single n r = C r * T n := by
  simp [C, T, single_mul_single]

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_C_mul_T** 是 Mathlib 中的一个定理，位于命名空
间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_C_mul_T (n : ℕ) (r : R) :
    (toLaurent (Polynomial.monomial n r) : R[T;T⁻¹]) = C r * T n := by simp [toLaurent]

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_C** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_C (r : R) : toLaurent (Polynomial.C r) = C r := by
  convert! Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, T_zero, mul_one]

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_comp_C** 是 Mathlib 中的一个定理，位于命名空间
 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ Polynomial.C = C :=
  funext Polynomial.toLaurent_C

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_X** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_X : (toLaurent Polynomial.X : R[T;T⁻¹]) = T 1 := by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_one** 是 Mathlib 中的一个定理，位于命名空间 `L
aurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) 1 = 1 :=
  map_one Polynomial.toLaurent

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_C_mul_eq** 是 Mathlib 中的一个定理，位于命名
空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : R[X]) :
    toLaurent (Polynomial.C r * f) = C r * toLaurent f := by
  simp only [map_mul, Polynomial.toLaurent_C]

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_X_pow** 是 Mathlib 中的一个定理，位于命名空间 
`LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_X_pow (n : ℕ) : toLaurent (X ^ n : R[X]) = T n := by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_C_mul_X_pow** 是 Mathlib 中的一个定理，位
于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : ℕ) (r : R) :
    toLaurent (Polynomial.C r * X ^ n) = C r * T n := by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
/-
**LaurentPolynomial.invertibleT** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
形式化陈述：invertibleT (n : Int) : Invertible (T n : R[T;T⁻¹]) where invOf
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invertibleT (n : ℤ) : Invertible (T n : R[T;T⁻¹]) where
  invOf := T (-n)
  invOf_mul_self := by rw [← T_add, neg_add_cancel, T_zero]
  mul_invOf_self := by rw [← T_add, add_neg_cancel, T_zero]

@[simp]
/-
**LaurentPolynomial.invOf_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：invOf_T (n : Int) : ⅟(T n : R[T;T⁻¹]) = T (-n)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invOf_T (n : ℤ) : ⅟(T n : R[T;T⁻¹]) = T (-n) :=
  rfl
/-
**LaurentPolynomial.isUnit_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：isUnit_T (n : Int) : IsUnit (T n : R[T;T⁻¹])
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem isUnit_T (n : ℤ) : IsUnit (T n : R[T;T⁻¹]) :=
  isUnit_of_invertible _

@[elab_as_elim]
/-
**LaurentPolynomial.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : LaurentPolynomial R → Prop} (p :
 LaurentPolynomial R),   (∀ (a : R), M (LaurentPolynomial.C a)) →     (∀ {p q : 
LaurentPolynomial R}, M p → M q → M (p + q)) →       (∀ (n : ℕ) (a : R),        
   M (LaurentPolynomial.C a * LaurentPolynomial.T ↑n) →             M (LaurentPo
lynomial.C a * LaurentPolynomial.T (↑n + 1))) →         (∀ (n : ℕ) (a : R),     
        M (LaurentPolynomial.C a * LaurentPolynomial.T (-↑n)) →               M 
(LaurentPolynomial.C a * LaurentPolynomial.T (-↑n - 1))) →           M p
参数：p : LaurentPolynomial R；∀ (a : R), M (LaurentPolynomial.C a)；∀ {p q : Laurent
Polynomial R}, M p → M q → M (p + q)；∀ (n : ℕ) (a : R),           M (LaurentPoly
nomial.C a * LaurentPolynomial.T ↑n) →             M (LaurentPolynomial.C a * La
urentPolynomial.T (↑n + 1))；∀ (n : ℕ) (a : R),             M (LaurentPolynomial.
C a * LaurentPolynomial.T (-↑n)) →               M (LaurentPolynomial.C a * Laur
entPolynomial.T (-↑n - 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `LaurentPolynomial.ext`：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹
]} (h : forall a, p.coeff a = q.coeff a) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddMonoidAlgebra.coeff_sum`：∀ {R : Type u_1} {M : Type u_4} {ι : Type u_
7} [inst : Semiring R] (s : Finset ι) (f : ι → AddMonoidAlgebra R M),   (∑ i ∈ s
, f i).coeff = ∑…
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
-/
protected theorem induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_C : ∀ a, M (C a))
    (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_C_mul_T : ∀ (n : ℕ) (a : R), M (C a * T n) → M (C a * T (n + 1)))
    (h_C_mul_T_Z : ∀ (n : ℕ) (a : R), M (C a * T (-n)) → M (C a * T (-n - 1))) : M p := by
  have A : ∀ {n : ℤ} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : ∀ s : Finset ℤ, M (s.sum fun n : ℤ => C (p.coeff n) * T n) := by
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
  rw [Finset.sum_apply', Finset.sum_eq_single a, single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same, notMem_support_iff.mp ha]

/-- To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_elim]
/-
**LaurentPolynomial.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {motive : LaurentPolynomial R → Prop}
 (p : LaurentPolynomial R),   (∀ (p q : LaurentPolynomial R), motive p → motive 
q → motive (p + q)) →     (∀ (n : ℤ) (a : R), motive (LaurentPolynomial.C a * La
urentPolynomial.T n)) → motive p
参数：p : LaurentPolynomial R；∀ (p q : LaurentPolynomial R), motive p → motive q → 
motive (p + q)；∀ (n : ℤ) (a : R), motive (LaurentPolynomial.C a * LaurentPolynom
ial.T n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on`：∀ {R : Type u_1} [inst : Semiring R] {M 
: LaurentPolynomial R → Prop} (p : LaurentPolynomial R),   (∀ (a : R), M (Lauren
tPolynomial.C a)) → …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
protected theorem induction_on' {motive : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (C_mul_T : ∀ (n : ℤ) (a : R), motive (C a * T n)) : motive p := by
  refine p.induction_on (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert! C_mul_T 0 a
  exact (mul_one _).symm
/-
**LaurentPolynomial.commute_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：commute_T (n : Int) (f : R[T;T⁻¹]) : Commute (T n) f
参数：n : Int；f : R[T;T⁻¹]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on'`：∀ {R : Type u_1} [inst : Semiring R] {m
otive : LaurentPolynomial R → Prop} (p : LaurentPolynomial R),   (∀ (p q : Laure
ntPolynomial R), moti…
· 使用定理 `Commute.add_right`：add_right [Distrib R] {a b c : R} : Commute a b -> Co
mmute a c -> Commute a (b + c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.T.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℤ), 
LaurentPolynomial.T n = AddMonoidAlgebra.single n 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C`：single_eq_C (r : R) : .single 0 r = C r
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (T n) f :=
  f.induction_on' (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      simp [add_comm]

@[simp]
/-
**LaurentPolynomial.T_mul** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：T_mul (n : Int) (f : R[T;T⁻¹]) : T n * f = f * T n
参数：n : Int；f : R[T;T⁻¹]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `LaurentPolynomial.commute_T`：commute_T (n : Int) (f : R[T;T⁻¹]) : Commut
e (T n) f
-/
theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : T n * f = f * T n :=
  (commute_T n f).eq
/-
**LaurentPolynomial.smul_eq_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smul_eq_C_mul (r : R) (f : R[T;T⁻¹]) : r • f = C r * f
参数：r : R；f : R[T;T⁻¹]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on'`：∀ {R : Type u_1} [inst : Semiring R] {m
otive : LaurentPolynomial R → Prop} (p : LaurentPolynomial R),   (∀ (p q : Laure
ntPolynomial R), moti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `AddMonoidAlgebra.isScalarTower_self`：∀ {R : Type u_1} (S : Type u_2) {M 
: Type u_3} [inst : Semiring S] [inst_1 : DistribSMul R S] [inst_2 : Add M]   [I
sScalarTower R S S], IsSc…
· 使用定理 `mul_left_inj_of_invertible`：mul_left_inj_of_invertible : a * c = b * c ↔
 a = b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `LaurentPolynomial.single_eq_C`：single_eq_C (r : R) : .single 0 r = C r
· 使用定理 `AddMonoidAlgebra.smul_single'`：∀ {R : Type u_1} {M : Type u_4} [inst : S
emiring R] (r' : R) (m : M) (r : R),   r' • AddMonoidAlgebra.single m r = AddMon
oidAlgebra.single m…
-/
theorem smul_eq_C_mul (r : R) (f : R[T;T⁻¹]) : r • f = C r * f := by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add, mul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← smul_mul_assoc, mul_left_inj_of_invertible, ← map_mul, ← single_eq_C,
      AddMonoidAlgebra.smul_single']
    rfl

/-- `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree of `f` "vanish".
`trunc` is a left-inverse to `Polynomial.toLaurent`. -/
/-
**LaurentPolynomial.trunc** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：trunc : R[T;T⁻¹] ->+ R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose
 terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree 
of `f` "vanish".
`trunc` is a left-inverse to `Polynomial.toLaurent`.
-/
def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comapDomainAddMonoidHom (↑) Nat.cast_injective

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LaurentPolynomial.trunc_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：trunc_C_mul_T (n : Int) (r : R) : trunc (C r * T n) = ite (0 <= n) (monomi
al n.toNat r) 0
参数：n : Int；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Polynomial.toFinsuppIso_apply`：∀ (R : Type u) [inst : Semiring R] (self 
: Polynomial R), (Polynomial.toFinsuppIso R) self = self.toFinsupp
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.comapDomainAddMonoidHom_apply`：∀ {R : Type u_3} {M : Ty
pe u_6} {N : Type u_7} [inst : Semiring R] (f : M → N) (hf : Function.Injective 
f)   (x : AddMonoidAlgebra R N), (Ad…
· 使用定理 `AddMonoidAlgebra.comapDomain_single_map`：∀ {R : Type u_3} {M : Type u_6}
 {N : Type u_7} [inst : Semiring R] (f : M → N) (hf : Function.Injective f) (m :
 M)   (r : R), AddMonoidAlgeb…
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `AddMonoidAlgebra.coeff_comapDomain`：∀ {R : Type u_3} {M : Type u_6} {N :
 Type u_7} [inst : Semiring R] (f : M → N) (hf : Function.Injective f)   (x : Ad
dMonoidAlgebra R N), (Ad…
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
-/
theorem trunc_C_mul_T (n : ℤ) (r : R) : trunc (C r * T n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  apply (toFinsuppIso R).injective
  simp only [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  split_ifs with hn
  · lift n to ℕ using hn
    simp [toFinsupp_monomial, -single_eq_C_mul_T]
  · ext a
    have : a ≠ n := by lia
    simp [-single_eq_C_mul_T, single_eq_of_ne this]

@[simp]
/-
**LaurentPolynomial.leftInverse_trunc_toLaurent** 是 Mathlib 中的一个定理，位于命名空间 `Laure
ntPolynomial`。
形式化陈述：leftInverse_trunc_toLaurent : Function.LeftInverse (trunc : R[T;T⁻¹] -> R[
X]) Polynomial.toLaurent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
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
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.toLaurent_C_mul_T`：∀ {R : Type u_1} [inst : Semiring R] (n : 
ℕ) (r : R),   Polynomial.toLaurent ((Polynomial.monomial n) r) = LaurentPolynomi
al.C r * LaurentPo…
· 使用定理 `LaurentPolynomial.trunc_C_mul_T`：trunc_C_mul_T (n : Int) (r : R) : trunc
 (C r * T n) = ite (0 <= n) (monomial n.toNat r) 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine fun f => f.induction_on' ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.trunc_toLaurent** 是 Mathlib 中的一个定理，位于命名空间 
`LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : trunc (toLaurent f) = f :=
  leftInverse_trunc_toLaurent _
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_injective** 是 Mathlib 中的一个定理，位于命
名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) :=
  leftInverse_trunc_toLaurent.injective

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_inj** 是 Mathlib 中的一个定理，位于命名空间 `L
aurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g :=
  ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_ne_zero {f : R[X]} : toLaurent f ≠ 0 ↔ f ≠ 0 :=
  map_ne_zero_iff _ Polynomial.toLaurent_injective

@[simp]
/-
**LaurentPolynomial._root_.Polynomial.toLaurent_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toLaurent_eq_zero {f : R[X]} : toLaurent f = 0 ↔ f = 0 :=
  map_eq_zero_iff _ Polynomial.toLaurent_injective
/-
**LaurentPolynomial.exists_T_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：exists_T_pow (f : R[T;T⁻¹]) : exists (n : Nat) (f' : R[X]), toLaurent f' =
 f * T n
参数：f : R[T;T⁻¹]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on'`：∀ {R : Type u_1} [inst : Semiring R] {m
otive : LaurentPolynomial R → Prop} (p : LaurentPolynomial R),   (∀ (p q : Laure
ntPolynomial R), moti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.toLaurent_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ)
, Polynomial.toLaurent (Polynomial.X ^ n) = LaurentPolynomial.T ↑n
· 使用定理 `LaurentPolynomial.mul_T_assoc`：mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : 
f * T m * T n = f * T (m + n)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.toLaurent_C_mul_eq`：∀ {R : Type u_1} [inst : Semiring R] (r :
 R) (f : Polynomial R),   Polynomial.toLaurent (Polynomial.C r * f) = LaurentPol
ynomial.C r * Polyn…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.toLaurent_C`：∀ {R : Type u_1} [inst : Semiring R] (r : R), Po
lynomial.toLaurent (Polynomial.C r) = LaurentPolynomial.C r
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
theorem exists_T_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), toLaurent f' = f * T n := by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, mul_T_assoc,
        neg_add_cancel, T_zero, mul_one]

/-- This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_elim]
/-
**LaurentPolynomial.induction_on_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynom
ial`。
形式化陈述：induction_on_mul_T {motive : R[T;T⁻¹] -> Prop} (f : R[T;T⁻¹]) (mul_T : for
all (f : R[X]) (n : Nat), motive (toLaurent f * T (-n))) : motive f
参数：f : R[T;T⁻¹]；mul_T : forall (f : R[X]) (n : Nat), motive (toLaurent f * T (-n
))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.exists_T_pow`：exists_T_pow (f : R[T;T⁻¹]) : exists (n 
: Nat) (f' : R[X]), toLaurent f' = f * T n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LaurentPolynomial.T_sub`：T_sub (m n : Int) : (T (m - n) : R[T;T⁻¹]) = T 
m * T (-n)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
This is a version of `exists_T_pow` stated as an induction principle.
-/
theorem induction_on_mul_T {motive : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
    (mul_T : ∀ (f : R[X]) (n : ℕ), motive (toLaurent f * T (-n))) : motive f := by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f, ← T_zero, ← Nat.cast_zero, ← Nat.sub_self n, Nat.cast_sub rfl.le, T_sub,
    ← mul_assoc, ← hf]
  exact mul_T ..

/-- Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;

it follow that `Q` is true on all Laurent polynomials. -/
/-
**LaurentPolynomial.reduce_to_polynomial_of_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentPolynomial`。
形式化陈述：reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] -> Prop} (Qf : 
forall f : R[X], Q (toLaurent f)) (QT : forall f, Q (f * T 1) -> Q f) : Q f
参数：f : R[T;T⁻¹]；Qf : forall f : R[X], Q (toLaurent f)；QT : forall f, Q (f * T 1)
 -> Q f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on_mul_T`：induction_on_mul_T {motive : R[T;T
⁻¹] -> Prop} (f : R[T;T⁻¹]) (mul_T : forall (f : R[X]) (n : Nat), motive (toLaur
ent f * T (-n))) : motive …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `LaurentPolynomial.mul_T_assoc`：mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : 
f * T m * T n = f * T (m + n)
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b

--- 原说明 ---
Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;

it follow that `Q` is true on all Laurent polynomials.
-/
theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
    (Qf : ∀ f : R[X], Q (toLaurent f)) (QT : ∀ f, Q (f * T 1) → Q f) : Q f := by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa

section Support

/-
**LaurentPolynomial.support_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial
`。
形式化陈述：support_C_mul_T (a : R) (n : Int) : (C a * T n).coeff.support subseteq {n}
参数：a : R；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
theorem support_C_mul_T (a : R) (n : ℤ) : (C a * T n).coeff.support ⊆ {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_subset
/-
**LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `
LaurentPolynomial`。
形式化陈述：support_coeff_C_mul_T_of_ne_zero {a : R} (a0 : a != 0) (n : Int) : (C a * 
T n).coeff.support = {n}
参数：a0 : a != 0；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
-/
theorem support_coeff_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    (C a * T n).coeff.support = {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single _ a0

@[deprecated (since := "2026-06-18")]
alias support_C_mul_T_of_ne_zero := support_coeff_C_mul_T_of_ne_zero
/-
**LaurentPolynomial.coeff_toLaurent** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial
`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (f : Polynomial R),   (Polynomial.toL
aurent f).coeff = Finsupp.mapDomain (⇑Nat.castEmbedding) f.toFinsupp.coeff
参数：f : Polynomial R；Polynomial.toLaurent f；⇑Nat.castEmbedding。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_toLaurent (f : R[X]) :
    f.toLaurent.coeff = f.toFinsupp.coeff.mapDomain Nat.castEmbedding := rfl

/-- The support of a polynomial `f` is a finset in `ℕ`.  The lemma `toLaurent_support f`
shows that the support of `f.toLaurent` is the same finset, but viewed in `ℤ` under the natural
inclusion `ℕ ↪ ℤ`. -/
/-
**LaurentPolynomial.support_coeff_toLaurent** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPo
lynomial`。
形式化陈述：support_coeff_toLaurent (f : R[X]) : f.toLaurent.coeff.support = f.support
.map Nat.castEmbedding
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_mapDomain_embedding`：∀ {α : Type u_1} {β : Type u_2} {M 
: Type u_5} [inst : AddCommMonoid M] (f : α ↪ β) (x : α →₀ M),   (Finsupp.mapDom
ain (⇑f) x).support = Fin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The support of a polynomial `f` is a finset in `ℕ`.  The lemma `toLaurent_suppor
t f`
shows that the support of `f.toLaurent` is the same finset, but viewed in `ℤ` un
der the natural
inclusion `ℕ ↪ ℤ`.
-/
theorem support_coeff_toLaurent (f : R[X]) :
    f.toLaurent.coeff.support = f.support.map Nat.castEmbedding := by simp [Polynomial.support]

@[deprecated (since := "2026-06-18")] alias toLaurent_support := support_coeff_toLaurent

end Support

section Degrees

/-- The degree of a Laurent polynomial takes values in `WithBot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its support of `f`,
or `⊥`, if `f = 0`. -/
/-
**LaurentPolynomial.degree** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree (f : R[T;T⁻¹]) : WithBot Int
参数：f : R[T;T⁻¹]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of a Laurent polynomial takes values in `WithBot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its
 support of `f`,
or `⊥`, if `f = 0`.
-/
def degree (f : R[T;T⁻¹]) : WithBot ℤ :=
  f.coeff.support.max

@[simp]
/-
**LaurentPolynomial.degree_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_zero : degree (0 : R[T;T⁻¹]) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ :=
  rfl

@[simp]
/-
**LaurentPolynomial.degree_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.ext`：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹
]} (h : forall a, p.coeff a = q.coeff a) : p = q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.degree_zero`：degree_zero : degree (0 : R[T;T⁻¹]) = ⊥
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
/-
**LaurentPolynomial.degree_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`
。
形式化陈述：degree_C_mul_T (n : Int) (a : R) (a0 : a != 0) : degree (C a * T n) = n
参数：n : Int；a : R；a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.degree.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f :
 LaurentPolynomial R), f.degree = f.coeff.support.max
· 使用定理 `LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero`：support_coeff_C_mul_
T_of_ne_zero {a : R} (a0 : a != 0) (n : Int) : (C a * T n).coeff.support = {n}
· 使用定理 `Finset.max_singleton`：max_singleton {a : α} : Finset.max {a} = (a : With
Bot α)
-/
theorem degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : degree (C a * T n) = n := by
  rw [degree, support_coeff_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton
/-
**LaurentPolynomial.degree_C_mul_T_ite** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynom
ial`。
形式化陈述：degree_C_mul_T_ite [DecidableEq R] (n : Int) (a : R) : degree (C a * T n) 
= if a = 0 then ⊥ else ↑n
参数：n : Int；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LaurentPolynomial.degree_C_mul_T`：degree_C_mul_T (n : Int) (a : R) (a0 :
 a != 0) : degree (C a * T n) = n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem degree_C_mul_T_ite [DecidableEq R] (n : ℤ) (a : R) :
    degree (C a * T n) = if a = 0 then ⊥ else ↑n := by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne,
      not_false_iff]

@[simp]
/-
**LaurentPolynomial.degree_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_T [Nontrivial R] (n : Int) : (T n : R[T;T⁻¹]).degree = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
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
· 使用定理 `LaurentPolynomial.degree_C_mul_T`：degree_C_mul_T (n : Int) (a : R) (a0 :
 a != 0) : degree (C a * T n) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem degree_T [Nontrivial R] (n : ℤ) : (T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (T n), ← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0)
/-
**LaurentPolynomial.degree_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_C {a : R} (a0 : a != 0) : (C a).degree = 0
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `LaurentPolynomial.degree_C_mul_T`：degree_C_mul_T (n : Int) (a : R) (a0 :
 a != 0) : degree (C a * T n) = n
-/
theorem degree_C {a : R} (a0 : a ≠ 0) : (C a).degree = 0 := by
  rw [← mul_one (C a), ← T_zero]
  exact degree_C_mul_T 0 a a0
/-
**LaurentPolynomial.degree_C_ite** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_C_ite [DecidableEq R] (a : R) : (C a).degree = if a = 0 then ⊥ else
 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LaurentPolynomial.degree_C`：degree_C {a : R} (a0 : a != 0) : (C a).degre
e = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem degree_C_ite [DecidableEq R] (a : R) : (C a).degree = if a = 0 then ⊥ else 0 := by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne, not_false_iff]

end ExactDegrees

section DegreeBounds

/-
**LaurentPolynomial.degree_C_mul_T_le** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：degree_C_mul_T_le (n : Int) (a : R) : degree (C a * T n) <= n
参数：n : Int；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LaurentPolynomial.degree_C_mul_T`：degree_C_mul_T (n : Int) (a : R) (a0 :
 a != 0) : degree (C a * T n) = n
-/
theorem degree_C_mul_T_le (n : ℤ) (a : R) : degree (C a * T n) ≤ n := by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le
/-
**LaurentPolynomial.degree_T_le** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_T_le (n : Int) : (T n : R[T;T⁻¹]).degree <= n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LaurentPolynomial.degree_C_mul_T_le`：degree_C_mul_T_le (n : Int) (a : R)
 : degree (C a * T n) <= n
-/
theorem degree_T_le (n : ℤ) : (T n : R[T;T⁻¹]).degree ≤ n :=
  (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))
/-
**LaurentPolynomial.degree_C_le** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：degree_C_le (a : R) : (C a).degree <= 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LaurentPolynomial.degree_C_mul_T_le`：degree_C_mul_T_le (n : Int) (a : R)
 : degree (C a * T n) <= n
-/
theorem degree_C_le (a : R) : (C a).degree ≤ 0 :=
  (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

end DegreeBounds

end Degrees

/-
**LaurentPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R[X] R[T;T⁻¹] :=
  Module.compHom _ Polynomial.toLaurent
/-
**LaurentPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Semiring R] : IsScalarTower R[X] R[X] R[T;T⁻¹] where
  smul_assoc x y z := by rw [smul_eq_mul, mul_smul]

end Semiring

section CommSemiring

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

/-
**LaurentPolynomial.algebraPolynomial** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：algebraPolynomial (R : Type*) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] whe
re algebraMap
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraPolynomial (R : Type*) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] where
  algebraMap := Polynomial.toLaurent
  commutes' := fun f l => by simp [mul_comm]
  smul_def' := fun _ _ => rfl
/-
**LaurentPolynomial.algebraMap_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomia
l`。
形式化陈述：algebraMap_X_pow (n : Nat) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toLaurent_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ)
, Polynomial.toLaurent (Polynomial.X ^ n) = LaurentPolynomial.T ↑n
-/
theorem algebraMap_X_pow (n : ℕ) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n :=
  Polynomial.toLaurent_X_pow n

@[simp]
/-
**LaurentPolynomial.algebraMap_eq_toLaurent** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPo
lynomial`。
形式化陈述：algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLauren
t f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f :=
  rfl
/-
**LaurentPolynomial.isLocalization** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`
。
形式化陈述：isLocalization : IsLocalization.Away (X : R[X]) R[T;T⁻¹]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.algebraMap_eq_toLaurent`：algebraMap_eq_toLaurent (f : 
R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f
· 使用定理 `Polynomial.toLaurent_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ)
, Polynomial.toLaurent (Polynomial.X ^ n) = LaurentPolynomial.T ↑n
· 使用定理 `LaurentPolynomial.isUnit_T`：isUnit_T (n : Int) : IsUnit (T n : R[T;T⁻¹])
· 使用定理 `LaurentPolynomial.induction_on_mul_T`：induction_on_mul_T {motive : R[T;T
⁻¹] -> Prop} (f : R[T;T⁻¹]) (mul_T : forall (f : R[X]) (n : Nat), motive (toLaur
ent f * T (-n))) : motive …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LaurentPolynomial.mul_T_assoc`：mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : 
f * T m * T n = f * T (m + n)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.toLaurent_inj`：∀ {R : Type u_1} [inst : Semiring R] (f g : Po
lynomial R), Polynomial.toLaurent f = Polynomial.toLaurent g ↔ f = g
-/
instance isLocalization : IsLocalization.Away (X : R[X]) R[T;T⁻¹] :=
  { map_units := fun ⟨t, ht⟩ => by
      obtain ⟨n, rfl⟩ := ht
      rw [algebraMap_eq_toLaurent, toLaurent_X_pow]
      exact isUnit_T ↑n
    surj f := by
      induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
      have : X ^ n ∈ Submonoid.powers (X : R[X]) := ⟨n, rfl⟩
      refine ⟨(f, ⟨_, this⟩), ?_⟩
      simp only [algebraMap_eq_toLaurent, toLaurent_X_pow, mul_T_assoc, neg_add_cancel, T_zero,
        mul_one]
    exists_of_eq := fun {f g} => by
      rw [algebraMap_eq_toLaurent, algebraMap_eq_toLaurent, Polynomial.toLaurent_inj]
      rintro rfl
      exact ⟨1, rfl⟩ }
/-
**LaurentPolynomial.mk'_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (p : Polynomial R) (n : ℕ),   IsL
ocalization.mk' (LaurentPolynomial R) p ⟨Polynomial.X ^ n, ⋯⟩ * LaurentPolynomia
l.T ↑n = Polynomial.toLaurent p
参数：p : Polynomial R；n : ℕ；LaurentPolynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.toLaurent_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ)
, Polynomial.toLaurent (Polynomial.X ^ n) = LaurentPolynomial.T ↑n
· 使用定理 `LaurentPolynomial.algebraMap_eq_toLaurent`：algebraMap_eq_toLaurent (f : 
R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem mk'_mul_T (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) * T n =
      toLaurent p := by
  rw [← toLaurent_X_pow, ← algebraMap_eq_toLaurent, IsLocalization.mk'_spec,
    algebraMap_eq_toLaurent]

@[simp]
/-
**LaurentPolynomial.mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (p : Polynomial R) (n : ℕ),   IsL
ocalization.mk' (LaurentPolynomial R) p ⟨Polynomial.X ^ n, ⋯⟩ = Polynomial.toLau
rent p * LaurentPolynomial.T (-↑n)
参数：p : Polynomial R；n : ℕ；LaurentPolynomial R；-↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `LaurentPolynomial.isUnit_T`：isUnit_T (n : Int) : IsUnit (T n : R[T;T⁻¹])
· 使用定理 `LaurentPolynomial.mul_T_assoc`：mul_T_assoc (f : R[T;T⁻¹]) (m n : Int) : 
f * T m * T n = f * T (m + n)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LaurentPolynomial.mk'_mul_T`：∀ {R : Type u_1} [inst : CommSemiring R] (p
 : Polynomial R) (n : ℕ),   IsLocalization.mk' (LaurentPolynomial R) p ⟨Polynomi
al.X ^ n, ⋯⟩ * La…
-/
theorem mk'_eq (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) =
      toLaurent p * T (-n) := by
  rw [← IsUnit.mul_left_inj (isUnit_T n), mul_T_assoc, neg_add_cancel, T_zero, mul_one]
  exact mk'_mul_T p n
/-
**LaurentPolynomial.mk'_one_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (n : ℕ),   IsLocalization.mk' (La
urentPolynomial R) 1 ⟨Polynomial.X ^ n, ⋯⟩ = LaurentPolynomial.T (-↑n)
参数：n : ℕ；LaurentPolynomial R；-↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (p : 
Polynomial R) (n : ℕ),   IsLocalization.mk' (LaurentPolynomial R) p ⟨Polynomial.
X ^ n, ⋯⟩ = Po…
· 使用定理 `Polynomial.toLaurent_one`：∀ {R : Type u_1} [inst : Semiring R], Polynomi
al.toLaurent 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mk'_one_X_pow (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) = T (-n) := by
  rw [mk'_eq 1 n, toLaurent_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LaurentPolynomial.mk'_one_X** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R],   IsLocalization.mk' (LaurentPol
ynomial R) 1 ⟨Polynomial.X, ⋯⟩ = LaurentPolynomial.T (-1)
参数：LaurentPolynomial R；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.mk'_one_X_pow`：∀ {R : Type u_1} [inst : CommSemiring R
] (n : ℕ),   IsLocalization.mk' (LaurentPolynomial R) 1 ⟨Polynomial.X ^ n, ⋯⟩ = 
LaurentPolynomial.T (…
-/
theorem mk'_one_X :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X, 1, pow_one X⟩ : Submonoid.powers (X : R[X])) = T (-1) := by
  convert! mk'_one_X_pow 1
  exact (pow_one X).symm

/-- Given a ring homomorphism `f : R →+* S` and a unit `x` in `S`, the induced homomorphism
`R[T;T⁻¹] →+* S` sending `T` to `x` and `T⁻¹` to `x⁻¹`. -/
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring homomorphism `f : R →+* S` and a unit `x` in `S`, the induced homom
orphism
`R[T;T⁻¹] →+* S` sending `T` to `x` and `T⁻¹` to `x⁻¹`.
-/
def eval₂ : R[T;T⁻¹] →+* S :=
  IsLocalization.lift (M := Submonoid.powers (X : R[X])) (g := Polynomial.eval₂RingHom f x) <| by
    rintro ⟨y, n, rfl⟩
    simpa only [coe_eval₂RingHom, eval₂_X_pow] using x.isUnit.pow n

@[simp]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_toLaurent (p : R[X]) : eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p := by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent, IsLocalization.lift_eq, coe_eval₂RingHom]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_T_n (n : ℕ) : eval₂ f x (T n) = x ^ n := by
  rw [← Polynomial.toLaurent_X_pow, eval₂_toLaurent, eval₂_X_pow]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_T_neg_n (n : ℕ) : eval₂ f x (T (-n)) = x⁻¹ ^ n := by
  rw [← mk'_one_X_pow]
  unfold eval₂
  rw [IsLocalization.lift_mk'_spec, map_one, coe_eval₂RingHom, eval₂_X_pow, ← mul_pow,
    Units.mul_inv, one_pow]

@[simp]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_T (n : ℤ) : eval₂ f x (T n) = (x ^ n).val := by
  by_cases! hn : 0 ≤ n
  · lift n to ℕ using hn
    apply eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [eval₂_T_neg_n, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]

@[simp]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C (r : R) : eval₂ f x (C r) = f r := by
  rw [← toLaurent_C, eval₂_toLaurent, Polynomial.eval₂_C]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_mul_T_n (r : R) (n : ℕ) : eval₂ f x (C r * T n) = f r * x ^ n := by
  rw [← Polynomial.toLaurent_C_mul_T, eval₂_toLaurent, eval₂_monomial]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_mul_T_neg_n (r : R) (n : ℕ) : eval₂ f x (C r * T (-n)) = f r * x⁻¹ ^ n := by
  rw [map_mul, eval₂_T_neg_n, eval₂_C]

@[simp]
/-
**LaurentPolynomial.eval** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_mul_T (r : R) (n : ℤ) : eval₂ f x (C r * T n) = f r * (x ^ n).val := by
  simp

end CommSemiring

section Inversion

variable {R : Type*} [CommSemiring R]

/-- The map which substitutes `T ↦ T⁻¹` into a Laurent polynomial. -/
/-
**LaurentPolynomial.invert** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map which substitutes `T ↦ T⁻¹` into a Laurent polynomial.
-/
def invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] := AddMonoidAlgebra.domCongr R R <| AddEquiv.neg _
/-
**LaurentPolynomial.invert_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (n : ℤ),   LaurentPolynomial.inve
rt (LaurentPolynomial.T n) = LaurentPolynomial.T (-n)
参数：n : ℤ；LaurentPolynomial.T n；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
-/
@[simp] lemma invert_T (n : ℤ) : invert (T n : R[T;T⁻¹]) = T (-n) :=
  AddMonoidAlgebra.domCongr_single ..
/-
**LaurentPolynomial.invert_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (f : LaurentPolynomial R) (n : ℤ)
,   (LaurentPolynomial.invert f).coeff n = f.coeff (-n)
参数：f : LaurentPolynomial R；n : ℤ；LaurentPolynomial.invert f；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_domCongr`：∀ {R : Type u_1} {A : Type u_4} {M : Ty
pe u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Algebra R A] [inst_3…
· 使用定理 `AddEquiv.neg_apply`：∀ (G : Type u_6) [inst : SubtractionCommMonoid G] (a
 : G), (AddEquiv.neg G) a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma invert_apply (f : R[T;T⁻¹]) (n : ℤ) : (invert f).coeff n = f.coeff (-n) := by
  simp [invert]
/-
**LaurentPolynomial.invert_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R], ⇑LaurentPolynomial.invert ∘ ⇑Lau
rentPolynomial.C = ⇑LaurentPolynomial.C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LaurentPolynomial.ext`：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹
]} (h : forall a, p.coeff a = q.coeff a) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.invert_apply`：∀ {R : Type u_3} [inst : CommSemiring R]
 (f : LaurentPolynomial R) (n : ℤ),   (LaurentPolynomial.invert f).coeff n = f.c
oeff (-n)
· 使用定理 `LaurentPolynomial.C_apply`：∀ {R : Type u_1} [inst : Semiring R] (t : R) 
(n : ℤ), (LaurentPolynomial.C t).coeff n = if n = 0 then t else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma invert_comp_C : invert ∘ (@C R _) = C := by ext; simp
/-
**LaurentPolynomial.invert_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (t : R),   LaurentPolynomial.inve
rt (LaurentPolynomial.C t) = LaurentPolynomial.C t
参数：t : R；LaurentPolynomial.C t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.ext`：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹
]} (h : forall a, p.coeff a = q.coeff a) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.invert_apply`：∀ {R : Type u_3} [inst : CommSemiring R]
 (f : LaurentPolynomial R) (n : ℤ),   (LaurentPolynomial.invert f).coeff n = f.c
oeff (-n)
· 使用定理 `LaurentPolynomial.C_apply`：∀ {R : Type u_1} [inst : Semiring R] (t : R) 
(n : ℤ), (LaurentPolynomial.C t).coeff n = if n = 0 then t else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma invert_C (t : R) : invert (C t) = C t := by ext; simp
/-
**LaurentPolynomial.involutive_invert** 是 Mathlib 中的一个引理，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：involutive_invert : Involutive (invert (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.ext`：LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹
]} (h : forall a, p.coeff a = q.coeff a) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.invert_apply`：∀ {R : Type u_3} [inst : CommSemiring R]
 (f : LaurentPolynomial R) (n : ℤ),   (LaurentPolynomial.invert f).coeff n = f.c
oeff (-n)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma involutive_invert : Involutive (invert (R := R)) := fun _ ↦ by ext; simp
/-
**LaurentPolynomial.invert_symm** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R], LaurentPolynomial.invert.symm = 
LaurentPolynomial.invert
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma invert_symm : (invert (R := R)).symm = invert := rfl
/-
**LaurentPolynomial.toLaurent_reverse** 是 Mathlib 中的一个引理，位于命名空间 `LaurentPolynomi
al`。
形式化陈述：toLaurent_reverse (p : R[X]) : toLaurent p.reverse = invert (toLaurent p) 
* (T p.natDegree)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.reverse_add_C`：∀ {R : Type u_1} [inst : Semiring R] (p : Poly
nomial R) (t : R),   (p + Polynomial.C t).reverse = p.reverse + Polynomial.C t *
 Polynomial.X …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.toLaurent_C_mul_eq`：∀ {R : Type u_1} [inst : Semiring R] (r :
 R) (f : Polynomial R),   Polynomial.toLaurent (Polynomial.C r * f) = LaurentPol
ynomial.C r * Polyn…
· 使用定理 `Polynomial.toLaurent_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ)
, Polynomial.toLaurent (Polynomial.X ^ n) = LaurentPolynomial.T ↑n
· 使用定理 `Polynomial.toLaurent_C`：∀ {R : Type u_1} [inst : Semiring R] (r : R), Po
lynomial.toLaurent (Polynomial.C r) = LaurentPolynomial.C r
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LaurentPolynomial.invert_C`：∀ {R : Type u_3} [inst : CommSemiring R] (t 
: R),   LaurentPolynomial.invert (LaurentPolynomial.C t) = LaurentPolynomial.C t
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
（共 44 条，此处仅展示前 30 条）
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

/-- Evaluate a Laurent polynomial at a unit, using scalar multiplication. -/
/-
**LaurentPolynomial.smeval** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval : S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a Laurent polynomial at a unit, using scalar multiplication.
-/
def smeval : S := f.coeff.sum fun n r => r • (x ^ n).val
/-
**LaurentPolynomial.smeval_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_eq_sum : f.smeval x = f.coeff.sum fun n r => r • (x ^ n).val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_eq_sum : f.smeval x = f.coeff.sum fun n r => r • (x ^ n).val := rfl
/-
**LaurentPolynomial.smeval_congr** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_congr : f = g -> x = y -> f.smeval x = g.smeval y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_congr : f = g → x = y → f.smeval x = g.smeval y := by rintro rfl rfl; rfl
/-
**LaurentPolynomial.smeval_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d S] [inst_2 : SMulWithZero R S]   [inst_3 : Monoid S] (x : Sˣ), LaurentPolynomi
al.smeval 0 x = 0
参数：x : Sˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma smeval_zero : (0 : R[T;T⁻¹]).smeval x = (0 : S) := by simp [smeval]
/-
**LaurentPolynomial.smeval_single** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_single (n : Int) (r : R) : smeval (.single n r) x = r • (x ^ n).val
参数：n : Int；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_single (n : ℤ) (r : R) : smeval (.single n r) x = r • (x ^ n).val := by
  simp [smeval, -single_eq_C_mul_T]

@[simp]
/-
**LaurentPolynomial.smeval_C_mul_T_n** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomia
l`。
形式化陈述：smeval_C_mul_T_n (n : Int) (r : R) : (C r * T n).smeval x = r • (x ^ n).va
l
参数：n : Int；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `LaurentPolynomial.smeval_single`：smeval_single (n : Int) (r : R) : smeva
l (.single n r) x = r • (x ^ n).val
-/
theorem smeval_C_mul_T_n (n : ℤ) (r : R) : (C r * T n).smeval x = r • (x ^ n).val := by
  rw [← single_eq_C_mul_T, smeval_single]

@[simp]
/-
**LaurentPolynomial.smeval_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_C (r : R) : (C r).smeval x = r • 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C`：single_eq_C (r : R) : .single 0 r = C r
· 使用定理 `LaurentPolynomial.smeval_single`：smeval_single (n : Int) (r : R) : smeva
l (.single n r) x = r • (x ^ n).val
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
-/
theorem smeval_C (r : R) : (C r).smeval x = r • 1 := by
  rw [← single_eq_C, smeval_single x (0 : ℤ) r, zpow_zero, Units.val_one]

end SMulWithZero

section MulActionWithZero

variable [Semiring R] [AddCommMonoid S] [MulActionWithZero R S] [Monoid S] (f g : R[T;T⁻¹])
  (x y : Sˣ)

@[simp]
/-
**LaurentPolynomial.smeval_T_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_T_pow (n : Int) (x : Sˣ) : (T n : R[T;T⁻¹]).smeval x = (x ^ n).val
参数：n : Int；x : Sˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.T.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℤ), 
LaurentPolynomial.T n = AddMonoidAlgebra.single n 1
· 使用定理 `LaurentPolynomial.smeval_single`：smeval_single (n : Int) (r : R) : smeva
l (.single n r) x = r • (x ^ n).val
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smeval_T_pow (n : ℤ) (x : Sˣ) : (T n : R[T;T⁻¹]).smeval x = (x ^ n).val := by
  rw [T, smeval_single, one_smul]

@[simp]
/-
**LaurentPolynomial.smeval_one** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_one : (1 : R[T;T⁻¹]).smeval x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `LaurentPolynomial.smeval_T_pow`：smeval_T_pow (n : Int) (x : Sˣ) : (T n :
 R[T;T⁻¹]).smeval x = (x ^ n).val
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
-/
theorem smeval_one : (1 : R[T;T⁻¹]).smeval x = 1 := by
  rw [← T_zero, smeval_T_pow 0 x, zpow_zero, Units.val_eq_one]

end MulActionWithZero

section Module

variable [Semiring R] [AddCommMonoid S] [Module R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

@[simp]
/-
**LaurentPolynomial.smeval_add** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_add : (f + g).smeval x = f.smeval x + g.smeval x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem smeval_add : (f + g).smeval x = f.smeval x + g.smeval x := by
  simp [smeval, Finsupp.sum_add_index, add_smul]

@[simp]
/-
**LaurentPolynomial.smeval_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：smeval_C_mul (r : R) : (C r * f).smeval x = r • (f.smeval x)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.induction_on'`：∀ {R : Type u_1} [inst : Semiring R] {m
otive : LaurentPolynomial R → Prop} (p : LaurentPolynomial R),   (∀ (p q : Laure
ntPolynomial R), moti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `LaurentPolynomial.smeval_add`：smeval_add : (f + g).smeval x = f.smeval x
 + g.smeval x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `LaurentPolynomial.smeval_C_mul_T_n`：smeval_C_mul_T_n (n : Int) (r : R) :
 (C r * T n).smeval x = r • (x ^ n).val
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem smeval_C_mul (r : R) : (C r * f).smeval x = r • (f.smeval x) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, smeval_add, smeval_add, smul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← map_mul, smeval_C_mul_T_n, smeval_C_mul_T_n, mul_smul]

variable (R) in
/-- Evaluation as an `R`-linear map. -/
@[simps]
/-
**LaurentPolynomial.leval** 是 Mathlib 中的一个定义，位于命名空间 `LaurentPolynomial`。
形式化陈述：leval : R[T;T⁻¹] ->ₗ[R] S where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentPolynomial.smeval_add`：smeval_add : (f + g).smeval x = f.smeval x
 + g.smeval x

--- 原说明 ---
Evaluation as an `R`-linear map.
-/
def leval : R[T;T⁻¹] →ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := smeval_add f g x
  map_smul' r f := by simp [smul_eq_C_mul]

end Module

end Smeval

end LaurentPolynomial

