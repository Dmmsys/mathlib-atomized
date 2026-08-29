/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.FastInstance
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Order.Group.Nat

import Mathlib.Data.Finsupp.SMul

/-!
# Theory of univariate polynomials

This file defines `Polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.
* `ofMultiset s` is the monic polynomial `p` which has roots `s`.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (fun n x ↦ f n x + g n x) = p.sum f + p.sum g`.
* Notation to refer to `Polynomial R`, as `R[X]` or `R[t]`.

## Implementation

Polynomials are defined using `R[ℕ]`, where `R` is a semiring.
The variable `X` commutes with every polynomial `p`: lemma `X_mul` proves the identity
`X * p = p * X`. The relationship to `R[ℕ]` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean cannot compute anyway with `AddMonoidAlgebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `R[X]` and `R[ℕ]` is
done through `ofFinsupp` and `toFinsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `R[ℕ]`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `Polynomial.toFinsuppIso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

@[expose] public section

noncomputable section

/-- `Polynomial R` is the type of univariate polynomials over `R`,
denoted as `R[X]` within the `Polynomial` namespace.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
@[wikidata Q43260]
/--
Definition of `Polynomial` / `Polynomial` 的定义

English:
structure Polynomial
  parameters: (R : Type*) [Semiring R]
  (no additional axioms)

中文:
结构 多项式
  参数: (R : 类型) [半环 R]
  (无附加公理)
-/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/
  toFinsupp : AddMonoidAlgebra R Nat

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset Module
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q : R[X]}

/--
theorem `forall_iff_forall_finsupp` / 定理 `forall_iff_forall_finsupp`

English:
theorem forall_iff_forall_finsupp
  given: (P : R[X] -> Prop)
  proof: ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

中文:
定理 对任意_iff_对任意_finsupp
  条件: (P : R[X] -> 命题)
  证明: ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩
-/
theorem forall_iff_forall_finsupp (P : R[X] -> Prop) :
    (forall p, P p) ↔ forall q : R[Nat], P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

/--
theorem `exists_iff_exists_finsupp` / 定理 `exists_iff_exists_finsupp`

English:
theorem exists_iff_exists_finsupp
  given: (P : R[X] -> Prop)
  proof: ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]

中文:
定理 存在_iff_存在_finsupp
  条件: (P : R[X] -> 命题)
  证明: ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
-/
theorem exists_iff_exists_finsupp (P : R[X] -> Prop) :
    (exists p, P p) ↔ exists q : R[Nat], P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  given: (f : R[X])
  statement: Polynomial.ofFinsupp f.toFinsupp = f
  proof: by constructor

中文:
定理 eta
  条件: (f : R[X])
  结论: 多项式.ofFinsupp f.toFinsupp = f
  证明: by constructor
-/
theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by constructor

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero R[X]
  body: ⟨⟨0⟩⟩

中文:
实例 :
  签名: 零 R[X]
  定义体: ⟨⟨0⟩⟩
-/
instance : Zero R[X] :=
  ⟨⟨0⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One R[X]
  body: ⟨⟨1⟩⟩

中文:
实例 :
  签名: 幺 R[X]
  定义体: ⟨⟨1⟩⟩
-/
instance : One R[X] :=
  ⟨⟨1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add R[X]
  body: ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a + b⟩⟩

中文:
实例 :
  签名: 加法 R[X]
  定义体: ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a + b⟩⟩
-/
@[no_expose] instance : Add R[X] :=
  ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a + b⟩⟩

@[no_expose] instance {R : Type u} [Ring R] : Neg R[X] :=
  ⟨fun ⟨a⟩ => ⟨-a⟩⟩

instance {R : Type u} [Ring R] : Sub R[X] :=
  ⟨fun a b => a + -b⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul R[X]
  body: ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a * b⟩⟩

中文:
实例 :
  签名: 乘法 R[X]
  定义体: ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a * b⟩⟩
-/
@[no_expose] instance : Mul R[X] :=
  ⟨fun ⟨a⟩ ⟨b⟩ => ⟨a * b⟩⟩

/--
Instance `instNSMul` / 实例 `instNSMul`

English:
instance instNSMul
  signature: : SMul Nat R[X] where
  body: ⟨r • p.toFinsupp⟩

中文:
实例 instNSMul
  签名: : 标量乘法 自然数 R[X] where
  定义体: ⟨r • p.toFinsupp⟩

Depends on / 依赖: p.toFinsupp, toFinsupp
-/
instance instNSMul : SMul Nat R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

/--
Instance `smulZeroClass` / 实例 `smulZeroClass`

English:
instance smulZeroClass
  signature: {S : Type*} [SMulZeroClass S R]
  body: ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

中文:
实例 smulZeroClass
  签名: {S : 类型} [SMulZero类 S R]
  定义体: ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

Depends on / 依赖: p.toFinsupp, toFinsupp
-/
instance smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul r p := ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

-- to avoid a bug in the `ring` tactic
instance (priority := 1) pow : Pow R[X] Nat where pow p n := npowRec n p

@[simp]
/--
theorem `ofFinsupp_zero` / 定理 `ofFinsupp_zero`

English:
theorem ofFinsupp_zero
  statement: (⟨0⟩ : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_zero
  结论: (⟨0⟩ : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `ofFinsupp_one` / 定理 `ofFinsupp_one`

English:
theorem ofFinsupp_one
  statement: (⟨1⟩ : R[X]) = 1
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_one
  结论: (⟨1⟩ : R[X]) = 1
  证明: rfl

@[simp]
-/
theorem ofFinsupp_one : (⟨1⟩ : R[X]) = 1 :=
  rfl

@[simp]
/--
theorem `ofFinsupp_add` / 定理 `ofFinsupp_add`

English:
theorem ofFinsupp_add
  given: {a b}
  statement: (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩
  proof: (rfl)

@[simp]

中文:
定理 ofFinsupp_add
  条件: {a b}
  结论: (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩
  证明: (rfl)

@[simp]
-/
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ :=
  (rfl)

@[simp]
/--
theorem `ofFinsupp_neg` / 定理 `ofFinsupp_neg`

English:
theorem ofFinsupp_neg
  given: {R : Type u} [Ring R] {a}
  statement: (⟨-a⟩ : R[X]) = -⟨a⟩
  proof: (rfl)

@[simp]

中文:
定理 ofFinsupp_neg
  条件: {R : 类型u} [环 R] {a}
  结论: (⟨-a⟩ : R[X]) = -⟨a⟩
  证明: (rfl)

@[simp]
-/
theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
  (rfl)

@[simp]
/--
theorem `ofFinsupp_sub` / 定理 `ofFinsupp_sub`

English:
theorem ofFinsupp_sub
  given: {R : Type u} [Ring R] {a b}
  statement: (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩
  proof: by
  rw [sub_eq_add_neg]
  rfl

@[simp]

中文:
定理 ofFinsupp_sub
  条件: {R : 类型u} [环 R] {a b}
  结论: (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩
  证明: by
  rw [sub_eq_add_neg]
  rfl

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg]
  rfl

@[simp]
/--
theorem `ofFinsupp_mul` / 定理 `ofFinsupp_mul`

English:
theorem ofFinsupp_mul
  given: (a b)
  statement: (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩
  proof: (rfl)

@[simp]

中文:
定理 ofFinsupp_mul
  条件: (a b)
  结论: (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩
  证明: (rfl)

@[simp]
-/
theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ :=
  (rfl)

@[simp]
/--
theorem `ofFinsupp_nsmul` / 定理 `ofFinsupp_nsmul`

English:
theorem ofFinsupp_nsmul
  given: (a : Nat) (b)
  statement: (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X])
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_nsmul
  条件: (a : 自然数) (b)
  结论: (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X])
  证明: rfl

@[simp]
-/
theorem ofFinsupp_nsmul (a : Nat) (b) : (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
/--
theorem `ofFinsupp_smul` / 定理 `ofFinsupp_smul`

English:
theorem ofFinsupp_smul
  given: {S : Type*} [SMulZeroClass S R] (a : S) (b)
  proof: rfl

中文:
定理 ofFinsupp_smul
  条件: {S : 类型} [SMulZero类 S R] (a : S) (b)
  证明: rfl
-/
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[simp]
/--
theorem `ofFinsupp_pow` / 定理 `ofFinsupp_pow`

English:
theorem ofFinsupp_pow
  given: (a) (n : Nat)
  statement: (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n
  proof: by
  change _ = npowRec n _
  induction n with
  | zero => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]

中文:
定理 ofFinsupp_pow
  条件: (a) (n : 自然数)
  结论: (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n
  证明: by
  change _ = npowRec n _
  induction n with
  | zero => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]

Depends on / 依赖: n_ih, npowRec, pow_succ
-/
theorem ofFinsupp_pow (a) (n : Nat) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]
/--
theorem `toFinsupp_zero` / 定理 `toFinsupp_zero`

English:
theorem toFinsupp_zero
  statement: (0 : R[X]).toFinsupp = 0
  proof: rfl

@[simp]

中文:
定理 toFinsupp_zero
  结论: (0 : R[X]).toFinsupp = 0
  证明: rfl

@[simp]
-/
theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 :=
  rfl

@[simp]
/--
theorem `toFinsupp_one` / 定理 `toFinsupp_one`

English:
theorem toFinsupp_one
  statement: (1 : R[X]).toFinsupp = 1
  proof: rfl

@[simp]

中文:
定理 toFinsupp_one
  结论: (1 : R[X]).toFinsupp = 1
  证明: rfl

@[simp]
-/
theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 :=
  rfl

@[simp]
/--
theorem `toFinsupp_add` / 定理 `toFinsupp_add`

English:
theorem toFinsupp_add
  given: (a b : R[X])
  statement: (a + b).toFinsupp = a.toFinsupp + b.toFinsupp
  proof: (rfl)

@[simp]

中文:
定理 toFinsupp_add
  条件: (a b : R[X])
  结论: (a + b).toFinsupp = a.toFinsupp + b.toFinsupp
  证明: (rfl)

@[simp]
-/
theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp :=
  (rfl)

@[simp]
/--
theorem `toFinsupp_neg` / 定理 `toFinsupp_neg`

English:
theorem toFinsupp_neg
  given: {R : Type u} [Ring R] (a : R[X])
  statement: (-a).toFinsupp = -a.toFinsupp
  proof: (rfl)

@[simp]

中文:
定理 toFinsupp_neg
  条件: {R : 类型u} [环 R] (a : R[X])
  结论: (-a).toFinsupp = -a.toFinsupp
  证明: (rfl)

@[simp]
-/
theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp :=
  (rfl)

@[simp]
/--
theorem `toFinsupp_sub` / 定理 `toFinsupp_sub`

English:
theorem toFinsupp_sub
  given: {R : Type u} [Ring R] (a b : R[X])
  proof: by
  rw [sub_eq_add_neg]
  rfl

@[simp]

中文:
定理 toFinsupp_sub
  条件: {R : 类型u} [环 R] (a b : R[X])
  证明: by
  rw [sub_eq_add_neg]
  rfl

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg]
  rfl

@[simp]
/--
theorem `toFinsupp_mul` / 定理 `toFinsupp_mul`

English:
theorem toFinsupp_mul
  given: (a b : R[X])
  statement: (a * b).toFinsupp = a.toFinsupp * b.toFinsupp
  proof: (rfl)

@[simp]

中文:
定理 toFinsupp_mul
  条件: (a b : R[X])
  结论: (a * b).toFinsupp = a.toFinsupp * b.toFinsupp
  证明: (rfl)

@[simp]
-/
theorem toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp :=
  (rfl)

@[simp]
/--
theorem `toFinsupp_nsmul` / 定理 `toFinsupp_nsmul`

English:
theorem toFinsupp_nsmul
  given: (a : Nat) (b : R[X])
  statement: (a • b).toFinsupp = a • b.toFinsupp
  proof: rfl

@[simp]

中文:
定理 toFinsupp_nsmul
  条件: (a : 自然数) (b : R[X])
  结论: (a • b).toFinsupp = a • b.toFinsupp
  证明: rfl

@[simp]
-/
theorem toFinsupp_nsmul (a : Nat) (b : R[X]) : (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
/--
theorem `toFinsupp_smul` / 定理 `toFinsupp_smul`

English:
theorem toFinsupp_smul
  given: {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X])
  proof: rfl

@[simp]

中文:
定理 toFinsupp_smul
  条件: {S : 类型} [SMulZero类 S R] (a : S) (b : R[X])
  证明: rfl

@[simp]
-/
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
/--
theorem `toFinsupp_pow` / 定理 `toFinsupp_pow`

English:
theorem toFinsupp_pow
  given: (a : R[X]) (n : Nat)
  statement: (a ^ n).toFinsupp = a.toFinsupp ^ n
  proof: by
  rw [← ofFinsupp_pow]

中文:
定理 toFinsupp_pow
  条件: (a : R[X]) (n : 自然数)
  结论: (a ^ n).toFinsupp = a.toFinsupp ^ n
  证明: by
  rw [← ofFinsupp_pow]

Depends on / 依赖: ofFinsupp_pow
-/
theorem toFinsupp_pow (a : R[X]) (n : Nat) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  rw [← ofFinsupp_pow]

/--
theorem `_root_.IsSMulRegular.polynomial` / 定理 `_root_.IsSMulRegular.polynomial`

English:
theorem _root_.IsSMulRegular.polynomial
  statement: {S : Type*} [SMulZeroClass S R] {a : S}

中文:
定理 _root_.IsSMulRegular.polynomial
  结论: {S : 类型} [SMulZero类 S R] {a : S}
-/
theorem _root_.IsSMulRegular.polynomial {S : Type*} [SMulZeroClass S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
| ⟨_x⟩, ⟨_y⟩, h => congr_arg _ coeff_injective ha.finsupp congr(($h).toFinsupp.coeff)

/--
theorem `toFinsupp_injective` / 定理 `toFinsupp_injective`

English:
theorem toFinsupp_injective
  statement: Function.Injective (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
  proof: fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]

中文:
定理 toFinsupp_injective
  结论: 函数.单射 (toFinsupp : R[X] -> 加法幺半群代数 _ _)
  证明: fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]

Depends on / 依赖: congr_arg
-/
theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] -> AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]
/--
theorem `toFinsupp_inj` / 定理 `toFinsupp_inj`

English:
theorem toFinsupp_inj
  given: {a b : R[X]}
  statement: a.toFinsupp = b.toFinsupp ↔ a = b
  proof: toFinsupp_injective.eq_iff

@[simp]

中文:
定理 toFinsupp_inj
  条件: {a b : R[X]}
  结论: a.toFinsupp = b.toFinsupp ↔ a = b
  证明: toFinsupp_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toFinsupp_injective, toFinsupp_injective.eq_iff
-/
theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
/--
theorem `toFinsupp_eq_zero` / 定理 `toFinsupp_eq_zero`

English:
theorem toFinsupp_eq_zero
  given: {a : R[X]}
  statement: a.toFinsupp = 0 ↔ a = 0
  proof: by
  rw [← toFinsupp_zero]; rw [toFinsupp_inj]

@[simp]

中文:
定理 toFinsupp_eq_zero
  条件: {a : R[X]}
  结论: a.toFinsupp = 0 ↔ a = 0
  证明: by
  rw [← toFinsupp_zero]; rw [toFinsupp_inj]

@[simp]

Depends on / 依赖: toFinsupp_inj, toFinsupp_zero
-/
theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero]; rw [toFinsupp_inj]

@[simp]
/--
theorem `toFinsupp_eq_one` / 定理 `toFinsupp_eq_one`

English:
theorem toFinsupp_eq_one
  given: {a : R[X]}
  statement: a.toFinsupp = 1 ↔ a = 1
  proof: by
  rw [← toFinsupp_one]; rw [toFinsupp_inj]

中文:
定理 toFinsupp_eq_one
  条件: {a : R[X]}
  结论: a.toFinsupp = 1 ↔ a = 1
  证明: by
  rw [← toFinsupp_one]; rw [toFinsupp_inj]

Depends on / 依赖: toFinsupp_inj, toFinsupp_one
-/
theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one]; rw [toFinsupp_inj]

/--
theorem `ofFinsupp_inj` / 定理 `ofFinsupp_inj`

English:
theorem ofFinsupp_inj
  given: {a b}
  statement: (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b
  proof: iff_of_eq (ofFinsupp.injEq _ _)

@[simp]

中文:
定理 ofFinsupp_inj
  条件: {a b}
  结论: (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b
  证明: iff_of_eq (ofFinsupp.injEq _ _)

@[simp]

Depends on / 依赖: iff_of_eq, ofFinsupp, ofFinsupp.injEq
-/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
/--
theorem `ofFinsupp_eq_zero` / 定理 `ofFinsupp_eq_zero`

English:
theorem ofFinsupp_eq_zero
  given: {a}
  statement: (⟨a⟩ : R[X]) = 0 ↔ a = 0
  proof: by
  rw [← ofFinsupp_zero]; rw [ofFinsupp_inj]

@[simp]

中文:
定理 ofFinsupp_eq_zero
  条件: {a}
  结论: (⟨a⟩ : R[X]) = 0 ↔ a = 0
  证明: by
  rw [← ofFinsupp_zero]; rw [ofFinsupp_inj]

@[simp]

Depends on / 依赖: ofFinsupp_inj, ofFinsupp_zero
-/
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero]; rw [ofFinsupp_inj]

@[simp]
/--
theorem `ofFinsupp_eq_one` / 定理 `ofFinsupp_eq_one`

English:
theorem ofFinsupp_eq_one
  given: {a}
  statement: (⟨a⟩ : R[X]) = 1 ↔ a = 1
  proof: by rw [← ofFinsupp_one, ofFinsupp_inj]

中文:
定理 ofFinsupp_eq_one
  条件: {a}
  结论: (⟨a⟩ : R[X]) = 1 ↔ a = 1
  证明: by rw [← ofFinsupp_one, ofFinsupp_inj]

Depends on / 依赖: ofFinsupp_inj, ofFinsupp_one
-/
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited R[X]
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : 可居 R[X]
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited R[X] :=
  ⟨0⟩

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast R[X] where natCast n
  body: ofFinsupp n

@[simp]

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 R[X] where natCast n
  定义体: ofFinsupp n

@[simp]

Depends on / 依赖: ofFinsupp
-/
instance instNatCast : NatCast R[X] where natCast n := ofFinsupp n

@[simp]
/--
theorem `ofFinsupp_natCast` / 定理 `ofFinsupp_natCast`

English:
theorem ofFinsupp_natCast
  given: (n : Nat)
  statement: (⟨n⟩ : R[X]) = n
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_natCast
  条件: (n : 自然数)
  结论: (⟨n⟩ : R[X]) = n
  证明: rfl

@[simp]
-/
theorem ofFinsupp_natCast (n : Nat) : (⟨n⟩ : R[X]) = n := rfl

@[simp]
/--
theorem `toFinsupp_natCast` / 定理 `toFinsupp_natCast`

English:
theorem toFinsupp_natCast
  given: (n : Nat)
  statement: (n : R[X]).toFinsupp = n
  proof: rfl

@[simp]

中文:
定理 toFinsupp_natCast
  条件: (n : 自然数)
  结论: (n : R[X]).toFinsupp = n
  证明: rfl

@[simp]
-/
theorem toFinsupp_natCast (n : Nat) : (n : R[X]).toFinsupp = n := rfl

@[simp]
/--
theorem `ofFinsupp_ofNat` / 定理 `ofFinsupp_ofNat`

English:
theorem ofFinsupp_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (⟨ofNat(n)⟩ : R[X]) = ofNat(n)
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (⟨of自然数(n)⟩ : R[X]) = of自然数(n)
  证明: rfl

@[simp]
-/
theorem ofFinsupp_ofNat (n : Nat) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n) := rfl

@[simp]
/--
theorem `toFinsupp_ofNat` / 定理 `toFinsupp_ofNat`

English:
theorem toFinsupp_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : R[X]).toFinsupp = ofNat(n)
  proof: rfl

中文:
定理 toFinsupp_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : R[X]).toFinsupp = of自然数(n)
  证明: rfl
-/
theorem toFinsupp_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : R[X]).toFinsupp = ofNat(n) := rfl

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: : Semiring R[X]
  body: fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ => rfl

中文:
实例 semiring
  签名: : 半环 R[X]
  定义体: fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ => rfl

Depends on / 依赖: Function, Function.Injective.semiring, Injective, fast_instance, semiring, toFinsupp, toFinsupp_add, toFinsupp_injective, toFinsupp_mul, toFinsupp_nsmul, toFinsupp_one, toFinsupp_pow, toFinsupp_zero
-/
instance semiring : Semiring R[X] :=
  fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ => rfl

/--
Instance `distribSMul` / 实例 `distribSMul`

English:
instance distribSMul
  signature: {S} [DistribSMul S R]
  body: fast_instance% Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

中文:
实例 distribSMul
  签名: {S} [分配标量乘法 S R]
  定义体: fast_instance% Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

Depends on / 依赖: Function, Function.Injective.distribSMul, Injective, distribSMul, fast_instance, toFinsupp, toFinsupp_add, toFinsupp_injective, toFinsupp_smul, toFinsupp_zero
-/
instance distribSMul {S} [DistribSMul S R] : DistribSMul S R[X] :=
  fast_instance% Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: {S} [Monoid S] [DistribMulAction S R]
  body: fast_instance% Function.Injective.distribMulAction
    ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

中文:
实例 distribMulAction
  签名: {S} [幺半群 S] [分配乘法作用 S R]
  定义体: fast_instance% Function.Injective.distribMulAction
    ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, distribMulAction, fast_instance, toFinsupp, toFinsupp_add, toFinsupp_injective, toFinsupp_smul, toFinsupp_zero
-/
instance distribMulAction {S} [Monoid S] [DistribMulAction S R] : DistribMulAction S R[X] :=
  fast_instance% Function.Injective.distribMulAction
    ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: {S} [SMulZeroClass S R] [FaithfulSMul S R]
  body: eq_of_smul_eq_smul fun a : R[Nat] => congr(($(h ⟨a⟩)).toFinsupp)

中文:
实例 faithfulSMul
  签名: {S} [SMulZero类 S R] [忠实标量乘法 S R]
  定义体: eq_of_smul_eq_smul fun a : R[Nat] => congr(($(h ⟨a⟩)).toFinsupp)

Depends on / 依赖: eq_of_smul_eq_smul, toFinsupp
-/
instance faithfulSMul {S} [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul {_s₁ _s₂} h := eq_of_smul_eq_smul fun a : R[Nat] => congr(($(h ⟨a⟩)).toFinsupp)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: {S} [Semiring S] [Module S R]
  body: fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

中文:
实例 module
  签名: {S} [半环 S] [模 S R]
  定义体: fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, fast_instance, module, toFinsupp, toFinsupp_add, toFinsupp_injective, toFinsupp_smul, toFinsupp_zero
-/
instance module {S} [Semiring S] [Module S R] : Module S R[X] :=
  fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R]
  body: ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩

中文:
实例 smulCommClass
  签名: {S₁ S₂} [SMulZero类 S₁ R] [SMulZero类 S₂ R] [标量交换类 S₁ S₂ R]
  定义体: ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩

Depends on / 依赖: ofFinsupp_smul, simp_rw, smul_comm
-/
instance smulCommClass {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
    SMulCommClass S₁ S₂ R[X] :=
  ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
  body: ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩

中文:
实例 isScalarTower
  签名: {S₁ S₂} [标量乘法 S₁ S₂] [SMulZero类 S₁ R] [SMulZero类 S₂ R]
  定义体: ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩

Depends on / 依赖: ofFinsupp_smul, simp_rw, smul_assoc
-/
instance isScalarTower {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X] :=
  ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩

/--
Instance `isScalarTower_right` / 实例 `isScalarTower_right`

English:
instance isScalarTower_right
  signature: {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalarTower α K K]
  body: ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩

中文:
实例 isScalarTower_right
  签名: {α K : 类型} [半环 K] [分配标量乘法 α K] [标量塔 α K K]
  定义体: ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩

Depends on / 依赖: ofFinsupp_mul, ofFinsupp_smul, simp_rw, smul_eq_mul, smul_mul_assoc
-/
instance isScalarTower_right {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalarTower α K K] :
    IsScalarTower α K[X] K[X] :=
  ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R]
  body: ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

中文:
实例 isCentralScalar
  签名: {S} [SMulZero类 S R] [SMulZero类 Sᵐᵒᵖ R] [中心标量 S R]
  定义体: ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

Depends on / 依赖: ofFinsupp_smul, op_smul_eq_smul, simp_rw
-/
instance isCentralScalar {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
    IsCentralScalar S R[X] :=
  ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

instance {S : Type*} [Semiring S] [Module S R] [IsTorsionFree S R] : IsTorsionFree S R[X] where
  isSMulRegular s hs := by
    rintro ⟨f⟩ ⟨g⟩ hfg; congr; apply hs.isSMulRegular; simpa using congr(($hfg).toFinsupp)

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [Subsingleton R]
  body: { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      apply congr_arg ofFinsupp
      simp [eq_iff_true_of_subsingleton] }

中文:
实例 unique
  签名: [子单例 R]
  定义体: { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      apply congr_arg ofFinsupp
      simp [eq_iff_true_of_subsingleton] }

Depends on / 依赖: Polynomial, Polynomial.inhabited, congr_arg, eq_iff_true_of_subsingleton, inhabited, ofFinsupp
-/
instance unique [Subsingleton R] : Unique R[X] :=
  { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      apply congr_arg ofFinsupp
      simp [eq_iff_true_of_subsingleton] }

variable (R)

/-- Ring isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps apply symm_apply]
/--
Definition of `toFinsuppIso` / `toFinsuppIso` 的定义

English:
definition toFinsuppIso
  signature: : R[X] ≃+* R[Nat] where
  body: toFinsupp
  invFun := ofFinsupp
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add

中文:
定义 toFinsuppIso
  签名: : R[X] ≃+* R[自然数] where
  定义体: toFinsupp
  invFun := ofFinsupp
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add

Depends on / 依赖: toFinsupp
-/
def toFinsuppIso : R[X] ≃+* R[Nat] where
  toFun := toFinsupp
  invFun := ofFinsupp
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : DecidableEq R[X]
  body: (toFinsuppIso R).toEquiv.decidableEq

中文:
实例 [DecidableEq
  签名: R] : DecidableEq R[X]
  定义体: (toFinsuppIso R).toEquiv.decidableEq

Depends on / 依赖: decidableEq, toEquiv, toEquiv.decidableEq, toFinsuppIso
-/
instance [DecidableEq R] : DecidableEq R[X] := (toFinsuppIso R).toEquiv.decidableEq

/-- Linear isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
/--
Definition of `toFinsuppIsoLinear` / `toFinsuppIsoLinear` 的定义

English:
definition toFinsuppIsoLinear
  signature: : R[X] ≃ₗ[R] R[Nat] where
  body: toFinsuppIso R
  map_smul' _ _ := rfl

中文:
定义 toFinsuppIsoLinear
  签名: : R[X] ≃ₗ[R] R[自然数] where
  定义体: toFinsuppIso R
  map_smul' _ _ := rfl

Depends on / 依赖: toFinsuppIso
-/
def toFinsuppIsoLinear : R[X] ≃ₗ[R] R[Nat] where
  __ := toFinsuppIso R
  map_smul' _ _ := rfl

end AddMonoidAlgebra

/--
theorem `ofFinsupp_sum` / 定理 `ofFinsupp_sum`

English:
theorem ofFinsupp_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> R[Nat])
  proof: map_sum (toFinsuppIso R).symm f s

中文:
定理 ofFinsupp_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R[自然数])
  证明: map_sum (toFinsuppIso R).symm f s

Depends on / 依赖: map_sum, toFinsuppIso
-/
theorem ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι -> R[Nat]) :
    (⟨∑ i in s, f i⟩ : R[X]) = ∑ i in s, ⟨f i⟩ :=
  map_sum (toFinsuppIso R).symm f s

/--
theorem `toFinsupp_sum` / 定理 `toFinsupp_sum`

English:
theorem toFinsupp_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> R[X])
  proof: map_sum (toFinsuppIso R) f s

中文:
定理 toFinsupp_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R[X])
  证明: map_sum (toFinsuppIso R) f s

Depends on / 依赖: map_sum, toFinsuppIso
-/
theorem toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι -> R[X]) :
    (∑ i in s, f i : R[X]).toFinsupp = ∑ i in s, (f i).toFinsupp :=
  map_sum (toFinsuppIso R) f s

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: : R[X] -> Finset Nat

中文:
定义 support
  签名: : R[X] -> 有限集 自然数
-/
def support : R[X] -> Finset Nat
  | ⟨p⟩ => p.coeff.support

@[simp]
/--
theorem `support_ofFinsupp` / 定理 `support_ofFinsupp`

English:
theorem support_ofFinsupp
  given: (p)
  statement: support (⟨p⟩ : R[X]) = p.coeff.support
  proof: by rw [support]

中文:
定理 support_ofFinsupp
  条件: (p)
  结论: support (⟨p⟩ : R[X]) = p.coeff.support
  证明: by rw [support]

Depends on / 依赖: support
-/
theorem support_ofFinsupp (p) : support (⟨p⟩ : R[X]) = p.coeff.support := by rw [support]

/--
theorem `support_toFinsupp` / 定理 `support_toFinsupp`

English:
theorem support_toFinsupp
  given: (p : R[X])
  statement: p.toFinsupp.coeff.support = p.support
  proof: by rw [support]

@[simp]

中文:
定理 support_toFinsupp
  条件: (p : R[X])
  结论: p.toFinsupp.coeff.support = p.support
  证明: by rw [support]

@[simp]

Depends on / 依赖: support
-/
theorem support_toFinsupp (p : R[X]) : p.toFinsupp.coeff.support = p.support := by rw [support]

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: (0 : R[X]).support = ∅
  proof: rfl

@[simp]

中文:
定理 support_zero
  结论: (0 : R[X]).support = ∅
  证明: rfl

@[simp]
-/
theorem support_zero : (0 : R[X]).support = ∅ :=
  rfl

@[simp]
/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  statement: p.support = ∅ ↔ p = 0
  proof: by
  rcases p with ⟨⟩
  simp [support]

中文:
定理 support_eq_empty
  结论: p.support = ∅ ↔ p = 0
  证明: by
  rcases p with ⟨⟩
  simp [support]

Depends on / 依赖: support
-/
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [support]

/--
lemma `support_nonempty` / 引理 `support_nonempty`

English:
lemma support_nonempty
  statement: p.support.Nonempty ↔ p != 0
  proof: Finset.nonempty_iff_ne_empty.trans support_eq_empty.not

中文:
引理 support_nonempty
  结论: p.support.非空 ↔ p != 0
  证明: Finset.nonempty_iff_ne_empty.trans support_eq_empty.not
-/
@[simp] lemma support_nonempty : p.support.Nonempty ↔ p != 0 :=
  Finset.nonempty_iff_ne_empty.trans support_eq_empty.not

/--
theorem `card_support_eq_zero` / 定理 `card_support_eq_zero`

English:
theorem card_support_eq_zero
  statement: #p.support = 0 ↔ p = 0
  proof: by simp

中文:
定理 card_support_eq_zero
  结论: #p.support = 0 ↔ p = 0
  证明: by simp
-/
theorem card_support_eq_zero : #p.support = 0 ↔ p = 0 := by simp

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: (n : Nat)
  body: ⟨.single n t⟩
  map_add' x y := by simp [← ofFinsupp_add]
  map_smul' r x := by simp [← ofFinsupp_smul]

@[simp]

中文:
定义 monomial
  签名: (n : 自然数)
  定义体: ⟨.single n t⟩
  map_add' x y := by simp [← ofFinsupp_add]
  map_smul' r x := by simp [← ofFinsupp_smul]

@[simp]

Depends on / 依赖: single
-/
def monomial (n : Nat) : R ->ₗ[R] R[X] where
  toFun t := ⟨.single n t⟩
  map_add' x y := by simp [← ofFinsupp_add]
  map_smul' r x := by simp [← ofFinsupp_smul]

@[simp]
/--
theorem `toFinsupp_monomial` / 定理 `toFinsupp_monomial`

English:
theorem toFinsupp_monomial
  given: (n : Nat) (r : R)
  statement: (monomial n r).toFinsupp = .single n r
  proof: by
  simp [monomial]

@[simp]

中文:
定理 toFinsupp_monomial
  条件: (n : 自然数) (r : R)
  结论: (monomial n r).toFinsupp = .single n r
  证明: by
  simp [monomial]

@[simp]

Depends on / 依赖: monomial
-/
theorem toFinsupp_monomial (n : Nat) (r : R) : (monomial n r).toFinsupp = .single n r := by
  simp [monomial]

@[simp]
/--
theorem `ofFinsupp_single` / 定理 `ofFinsupp_single`

English:
theorem ofFinsupp_single
  given: (n : Nat) (r : R)
  statement: (⟨.single n r⟩ : R[X]) = monomial n r
  proof: by
  simp [monomial]

@[simp]

中文:
定理 ofFinsupp_single
  条件: (n : 自然数) (r : R)
  结论: (⟨.single n r⟩ : R[X]) = monomial n r
  证明: by
  simp [monomial]

@[simp]

Depends on / 依赖: monomial
-/
theorem ofFinsupp_single (n : Nat) (r : R) : (⟨.single n r⟩ : R[X]) = monomial n r := by
  simp [monomial]

@[simp]
/--
theorem `monomial_zero_right` / 定理 `monomial_zero_right`

English:
theorem monomial_zero_right
  given: (n : Nat)
  statement: monomial n (0 : R) = 0
  proof: (monomial n).map_zero

中文:
定理 monomial_zero_right
  条件: (n : 自然数)
  结论: monomial n (0 : R) = 0
  证明: (monomial n).map_zero

Depends on / 依赖: map_zero, monomial
-/
theorem monomial_zero_right (n : Nat) : monomial n (0 : R) = 0 :=
  (monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
/--
theorem `monomial_zero_one` / 定理 `monomial_zero_one`

English:
theorem monomial_zero_one
  statement: monomial 0 (1 : R) = 1
  proof: rfl

中文:
定理 monomial_zero_one
  结论: monomial 0 (1 : R) = 1
  证明: rfl
-/
theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl

/--
theorem `monomial_mul_monomial` / 定理 `monomial_mul_monomial`

English:
theorem monomial_mul_monomial
  given: (n m : Nat) (r s : R)
  proof: toFinsupp_injective by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]

中文:
定理 monomial_mul_monomial
  条件: (n m : 自然数) (r s : R)
  证明: toFinsupp_injective by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.single_mul_single, single_mul_single, toFinsupp_injective, toFinsupp_monomial, toFinsupp_mul
-/
theorem monomial_mul_monomial (n m : Nat) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * s) :=
toFinsupp_injective by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]
/--
theorem `monomial_pow` / 定理 `monomial_pow`

English:
theorem monomial_pow
  given: (n : Nat) (r : R) (k : Nat)
  statement: monomial n r ^ k = monomial (n * k) (r ^ k)
  proof: by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]

中文:
定理 monomial_pow
  条件: (n : 自然数) (r : R) (k : 自然数)
  结论: monomial n r ^ k = monomial (n * k) (r ^ k)
  证明: by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]

Depends on / 依赖: add_comm, monomial_mul_monomial, monomial_zero_one, mul_add, pow_succ, pow_zero
-/
theorem monomial_pow (n : Nat) (r : R) (k : Nat) : monomial n r ^ k = monomial (n * k) (r ^ k) := by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]

/--
theorem `smul_monomial` / 定理 `smul_monomial`

English:
theorem smul_monomial
  given: {S} [SMulZeroClass S R] (a : S) (n : Nat) (b : R)
  proof: toFinsupp_injective AddMonoidAlgebra.smul_single _ _ _

中文:
定理 smul_monomial
  条件: {S} [SMulZero类 S R] (a : S) (n : 自然数) (b : R)
  证明: toFinsupp_injective AddMonoidAlgebra.smul_single _ _ _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.smul_single, smul_single, toFinsupp_injective
-/
theorem smul_monomial {S} [SMulZeroClass S R] (a : S) (n : Nat) (b : R) :
    a • monomial n b = monomial n (a • b) :=
toFinsupp_injective AddMonoidAlgebra.smul_single _ _ _

/--
theorem `monomial_injective` / 定理 `monomial_injective`

English:
theorem monomial_injective
  given: (n : Nat)
  statement: Function.Injective (monomial n : R -> R[X])
  proof: (toFinsuppIso R).symm.injective.comp single_right_injective

@[simp]

中文:
定理 monomial_injective
  条件: (n : 自然数)
  结论: 函数.单射 (monomial n : R -> R[X])
  证明: (toFinsuppIso R).symm.injective.comp single_right_injective

@[simp]

Depends on / 依赖: injective, single_right_injective, symm.injective.comp, toFinsuppIso
-/
theorem monomial_injective (n : Nat) : Function.Injective (monomial n : R -> R[X]) :=
  (toFinsuppIso R).symm.injective.comp single_right_injective

@[simp]
/--
theorem `monomial_eq_zero_iff` / 定理 `monomial_eq_zero_iff`

English:
theorem monomial_eq_zero_iff
  given: (t : R) (n : Nat)
  statement: monomial n t = 0 ↔ t = 0
  proof: LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

中文:
定理 monomial_eq_zero_iff
  条件: (t : R) (n : 自然数)
  结论: monomial n t = 0 ↔ t = 0
  证明: LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

Depends on / 依赖: LinearMap, LinearMap.map_eq_zero_iff, Polynomial, Polynomial.monomial_injective, map_eq_zero_iff, monomial_injective
-/
theorem monomial_eq_zero_iff (t : R) (n : Nat) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

/--
theorem `monomial_eq_monomial_iff` / 定理 `monomial_eq_monomial_iff`

English:
theorem monomial_eq_monomial_iff
  given: {m n : Nat} {a b : R}
  proof: by
  rw [← toFinsupp_inj]; rw [toFinsupp_monomial]; rw [toFinsupp_monomial]; rw [single_inj]

中文:
定理 monomial_eq_monomial_iff
  条件: {m n : 自然数} {a b : R}
  证明: by
  rw [← toFinsupp_inj]; rw [toFinsupp_monomial]; rw [toFinsupp_monomial]; rw [single_inj]

Depends on / 依赖: single_inj, toFinsupp_inj, toFinsupp_monomial
-/
theorem monomial_eq_monomial_iff {m n : Nat} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← toFinsupp_inj]; rw [toFinsupp_monomial]; rw [toFinsupp_monomial]; rw [single_inj]

/--
theorem `support_add` / 定理 `support_add`

English:
theorem support_add
  statement: (p + q).support subseteq p.support union q.support
  proof: by
  simpa [support] using! Finsupp.support_add

中文:
定理 support_add
  结论: (p + q).support subseteq p.support union q.support
  证明: by
  simpa [support] using! Finsupp.support_add

Depends on / 依赖: Finsupp, Finsupp.support_add, support, support_add
-/
theorem support_add : (p + q).support subseteq p.support union q.support := by
  simpa [support] using! Finsupp.support_add

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* R[X]
  body: { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]

中文:
定义 C
  签名: : R ->+* R[X]
  定义体: { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]

Depends on / 依赖: map_mul, map_one, map_zero, monomial, monomial_mul_monomial, monomial_zero_one
-/
def C : R ->+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]
/--
theorem `monomial_zero_left` / 定理 `monomial_zero_left`

English:
theorem monomial_zero_left
  given: ⦃a
  statement: R⦄ : monomial 0 a = C a
  proof: rfl

@[simp]

中文:
定理 monomial_zero_left
  条件: ⦃a
  结论: R⦄ : monomial 0 a = C a
  证明: rfl

@[simp]
-/
theorem monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a :=
  rfl

@[simp]
/--
theorem `toFinsupp_C` / 定理 `toFinsupp_C`

English:
theorem toFinsupp_C
  given: (a : R)
  statement: (C a).toFinsupp = single 0 a
  proof: rfl

中文:
定理 toFinsupp_C
  条件: (a : R)
  结论: (C a).toFinsupp = single 0 a
  证明: rfl
-/
theorem toFinsupp_C (a : R) : (C a).toFinsupp = single 0 a :=
  rfl

/--
theorem `C_0` / 定理 `C_0`

English:
theorem C_0
  statement: C (0 : R) = 0
  proof: by simp

中文:
定理 C_0
  结论: C (0 : R) = 0
  证明: by simp
-/
theorem C_0 : C (0 : R) = 0 := by simp

/--
theorem `C_1` / 定理 `C_1`

English:
theorem C_1
  statement: C (1 : R) = 1
  proof: rfl

中文:
定理 C_1
  结论: C (1 : R) = 1
  证明: rfl
-/
theorem C_1 : C (1 : R) = 1 :=
  rfl

/--
theorem `C_ofNat` / 定理 `C_ofNat`

English:
theorem C_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: C ofNat(n) = (ofNat(n) : R[X])
  proof: rfl

中文:
定理 C_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: C of自然数(n) = (of自然数(n) : R[X])
  证明: rfl
-/
theorem C_ofNat (n : Nat) [n.AtLeastTwo] : C ofNat(n) = (ofNat(n) : R[X]) :=
  rfl

/--
theorem `C_mul` / 定理 `C_mul`

English:
theorem C_mul
  statement: C (a * b) = C a * C b
  proof: C.map_mul a b

中文:
定理 C_mul
  结论: C (a * b) = C a * C b
  证明: C.map_mul a b

Depends on / 依赖: C.map_mul, map_mul
-/
theorem C_mul : C (a * b) = C a * C b :=
  C.map_mul a b

/--
theorem `C_add` / 定理 `C_add`

English:
theorem C_add
  statement: C (a + b) = C a + C b
  proof: C.map_add a b

@[simp]

中文:
定理 C_add
  结论: C (a + b) = C a + C b
  证明: C.map_add a b

@[simp]

Depends on / 依赖: C.map_add, map_add
-/
theorem C_add : C (a + b) = C a + C b :=
  C.map_add a b

@[simp]
/--
theorem `smul_C` / 定理 `smul_C`

English:
theorem smul_C
  given: {S} [SMulZeroClass S R] (s : S) (r : R)
  statement: s • C r = C (s • r)
  proof: smul_monomial _ _ r

中文:
定理 smul_C
  条件: {S} [SMulZero类 S R] (s : S) (r : R)
  结论: s • C r = C (s • r)
  证明: smul_monomial _ _ r

Depends on / 依赖: smul_monomial
-/
theorem smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r

/--
theorem `C_pow` / 定理 `C_pow`

English:
theorem C_pow
  statement: C (a ^ n) = C a ^ n
  proof: C.map_pow a n

中文:
定理 C_pow
  结论: C (a ^ n) = C a ^ n
  证明: C.map_pow a n

Depends on / 依赖: C.map_pow, map_pow
-/
theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n

/--
theorem `C_eq_natCast` / 定理 `C_eq_natCast`

English:
theorem C_eq_natCast
  given: (n : Nat)
  statement: C (n : R) = (n : R[X])
  proof: map_natCast C n

@[simp, grind =]

中文:
定理 C_eq_natCast
  条件: (n : 自然数)
  结论: C (n : R) = (n : R[X])
  证明: map_natCast C n

@[simp, grind =]

Depends on / 依赖: map_natCast
-/
theorem C_eq_natCast (n : Nat) : C (n : R) = (n : R[X]) :=
  map_natCast C n

@[simp, grind =]
/--
theorem `C_mul_monomial` / 定理 `C_mul_monomial`

English:
theorem C_mul_monomial
  statement: C a * monomial n b = monomial n (a * b)
  proof: by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp, grind =]

中文:
定理 C_mul_monomial
  结论: C a * monomial n b = monomial n (a * b)
  证明: by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp, grind =]

Depends on / 依赖: monomial_mul_monomial, monomial_zero_left, zero_add
-/
theorem C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp, grind =]
/--
theorem `monomial_mul_C` / 定理 `monomial_mul_C`

English:
theorem monomial_mul_C
  statement: monomial n a * C b = monomial n (a * b)
  proof: by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

中文:
定理 monomial_mul_C
  结论: monomial n a * C b = monomial n (a * b)
  证明: by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

Depends on / 依赖: add_zero, monomial_mul_monomial, monomial_zero_left
-/
theorem monomial_mul_C : monomial n a * C b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : R[X]
  body: monomial 1 1

中文:
定义 X
  签名: : R[X]
  定义体: monomial 1 1

Depends on / 依赖: monomial
-/
def X : R[X] :=
  monomial 1 1

/--
theorem `monomial_one_one_eq_X` / 定理 `monomial_one_one_eq_X`

English:
theorem monomial_one_one_eq_X
  statement: monomial 1 (1 : R) = X
  proof: rfl

中文:
定理 monomial_one_one_eq_X
  结论: monomial 1 (1 : R) = X
  证明: rfl
-/
theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl

/--
theorem `monomial_one_right_eq_X_pow` / 定理 `monomial_one_right_eq_X_pow`

English:
theorem monomial_one_right_eq_X_pow
  given: (n : Nat)
  statement: monomial n (1 : R) = X ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]

中文:
定理 monomial_one_right_eq_X_pow
  条件: (n : 自然数)
  结论: monomial n (1 : R) = X ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]

Depends on / 依赖: monomial_mul_monomial, monomial_one_one_eq_X, mul_one, pow_succ
-/
theorem monomial_one_right_eq_X_pow (n : Nat) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]
/--
theorem `toFinsupp_X` / 定理 `toFinsupp_X`

English:
theorem toFinsupp_X
  statement: X.toFinsupp = .single 1 (1 : R)
  proof: rfl

中文:
定理 toFinsupp_X
  结论: X.toFinsupp = .single 1 (1 : R)
  证明: rfl
-/
theorem toFinsupp_X : X.toFinsupp = .single 1 (1 : R) :=
  rfl

/--
theorem `X_ne_C` / 定理 `X_ne_C`

English:
theorem X_ne_C
  given: [Nontrivial R] (a : R)
  statement: X != C a
  proof: by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

中文:
定理 X_ne_C
  条件: [非平凡 R] (a : R)
  结论: X != C a
  证明: by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

Depends on / 依赖: monomial_eq_monomial_iff
-/
theorem X_ne_C [Nontrivial R] (a : R) : X != C a := by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

set_option backward.isDefEq.respectTransparency false in
/--
theorem `X_mul` / 定理 `X_mul`

English:
theorem X_mul
  statement: X * p = p * X
  proof: by
  rcases p with ⟨⟩
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.coeff_mul, add_comm]

中文:
定理 X_mul
  结论: X * p = p * X
  证明: by
  rcases p with ⟨⟩
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.coeff_mul, add_comm]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_mul, add_comm, coeff_mul, ofFinsupp, ofFinsupp.injEq, ofFinsupp_mul, ofFinsupp_single
-/
theorem X_mul : X * p = p * X := by
  rcases p with ⟨⟩
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.coeff_mul, add_comm]

/--
theorem `X_pow_mul` / 定理 `X_pow_mul`

English:
theorem X_pow_mul
  given: {n : Nat}
  statement: X ^ n * p = p * X ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]

中文:
定理 X_pow_mul
  条件: {n : 自然数}
  结论: X ^ n * p = p * X ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]

Depends on / 依赖: X_mul, conv_lhs, mul_assoc, pow_succ
-/
theorem X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]

/-- Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `Polynomial.X_mul`. -/
@[simp]
/--
theorem `X_mul_C` / 定理 `X_mul_C`

English:
theorem X_mul_C
  given: (r : R)
  statement: X * C r = C r * X
  proof: X_mul

中文:
定理 X_mul_C
  条件: (r : R)
  结论: X * C r = C r * X
  证明: X_mul

Depends on / 依赖: X_mul
-/
theorem X_mul_C (r : R) : X * C r = C r * X :=
  X_mul

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`. -/
@[simp]
/--
theorem `X_pow_mul_C` / 定理 `X_pow_mul_C`

English:
theorem X_pow_mul_C
  given: (r : R) (n : Nat)
  statement: X ^ n * C r = C r * X ^ n
  proof: X_pow_mul

中文:
定理 X_pow_mul_C
  条件: (r : R) (n : 自然数)
  结论: X ^ n * C r = C r * X ^ n
  证明: X_pow_mul

Depends on / 依赖: X_pow_mul
-/
theorem X_pow_mul_C (r : R) (n : Nat) : X ^ n * C r = C r * X ^ n :=
  X_pow_mul

/--
theorem `X_pow_mul_assoc` / 定理 `X_pow_mul_assoc`

English:
theorem X_pow_mul_assoc
  given: {n : Nat}
  statement: p * X ^ n * q = p * q * X ^ n
  proof: by
  rw [mul_assoc]; rw [X_pow_mul]; rw [← mul_assoc]

中文:
定理 X_pow_mul_assoc
  条件: {n : 自然数}
  结论: p * X ^ n * q = p * q * X ^ n
  证明: by
  rw [mul_assoc]; rw [X_pow_mul]; rw [← mul_assoc]

Depends on / 依赖: X_pow_mul, mul_assoc
-/
theorem X_pow_mul_assoc {n : Nat} : p * X ^ n * q = p * q * X ^ n := by
  rw [mul_assoc]; rw [X_pow_mul]; rw [← mul_assoc]

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`. -/
@[simp]
/--
theorem `X_pow_mul_assoc_C` / 定理 `X_pow_mul_assoc_C`

English:
theorem X_pow_mul_assoc_C
  given: {n : Nat} (r : R)
  statement: p * X ^ n * C r = p * C r * X ^ n
  proof: X_pow_mul_assoc

中文:
定理 X_pow_mul_assoc_C
  条件: {n : 自然数} (r : R)
  结论: p * X ^ n * C r = p * C r * X ^ n
  证明: X_pow_mul_assoc

Depends on / 依赖: X_pow_mul_assoc
-/
theorem X_pow_mul_assoc_C {n : Nat} (r : R) : p * X ^ n * C r = p * C r * X ^ n :=
  X_pow_mul_assoc

/--
theorem `commute_X` / 定理 `commute_X`

English:
theorem commute_X
  given: (p : R[X])
  statement: Commute X p
  proof: X_mul

中文:
定理 commute_X
  条件: (p : R[X])
  结论: Commute X p
  证明: X_mul

Depends on / 依赖: X_mul
-/
theorem commute_X (p : R[X]) : Commute X p :=
  X_mul

/--
theorem `commute_X_pow` / 定理 `commute_X_pow`

English:
theorem commute_X_pow
  given: (p : R[X]) (n : Nat)
  statement: Commute (X ^ n) p
  proof: X_pow_mul

@[simp]

中文:
定理 commute_X_pow
  条件: (p : R[X]) (n : 自然数)
  结论: Commute (X ^ n) p
  证明: X_pow_mul

@[simp]

Depends on / 依赖: X_pow_mul
-/
theorem commute_X_pow (p : R[X]) (n : Nat) : Commute (X ^ n) p :=
  X_pow_mul

@[simp]
/--
theorem `monomial_mul_X` / 定理 `monomial_mul_X`

English:
theorem monomial_mul_X
  given: (n : Nat) (r : R)
  statement: monomial n r * X = monomial (n + 1) r
  proof: by
  rw [X]; rw [monomial_mul_monomial]; rw [mul_one]

@[simp]

中文:
定理 monomial_mul_X
  条件: (n : 自然数) (r : R)
  结论: monomial n r * X = monomial (n + 1) r
  证明: by
  rw [X]; rw [monomial_mul_monomial]; rw [mul_one]

@[simp]

Depends on / 依赖: monomial_mul_monomial, mul_one
-/
theorem monomial_mul_X (n : Nat) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [X]; rw [monomial_mul_monomial]; rw [mul_one]

@[simp]
/--
theorem `monomial_mul_X_pow` / 定理 `monomial_mul_X_pow`

English:
theorem monomial_mul_X_pow
  given: (n : Nat) (r : R) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]

中文:
定理 monomial_mul_X_pow
  条件: (n : 自然数) (r : R) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]

Depends on / 依赖: add_assoc, mul_assoc, pow_succ
-/
theorem monomial_mul_X_pow (n : Nat) (r : R) (k : Nat) :
    monomial n r * X ^ k = monomial (n + k) r := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]
/--
theorem `X_mul_monomial` / 定理 `X_mul_monomial`

English:
theorem X_mul_monomial
  given: (n : Nat) (r : R)
  statement: X * monomial n r = monomial (n + 1) r
  proof: by
  rw [X_mul]; rw [monomial_mul_X]

@[simp]

中文:
定理 X_mul_monomial
  条件: (n : 自然数) (r : R)
  结论: X * monomial n r = monomial (n + 1) r
  证明: by
  rw [X_mul]; rw [monomial_mul_X]

@[simp]

Depends on / 依赖: X_mul, monomial_mul_X
-/
theorem X_mul_monomial (n : Nat) (r : R) : X * monomial n r = monomial (n + 1) r := by
  rw [X_mul]; rw [monomial_mul_X]

@[simp]
/--
theorem `X_pow_mul_monomial` / 定理 `X_pow_mul_monomial`

English:
theorem X_pow_mul_monomial
  given: (k n : Nat) (r : R)
  statement: X ^ k * monomial n r = monomial (n + k) r
  proof: by
  rw [X_pow_mul]; rw [monomial_mul_X_pow]

中文:
定理 X_pow_mul_monomial
  条件: (k n : 自然数) (r : R)
  结论: X ^ k * monomial n r = monomial (n + k) r
  证明: by
  rw [X_pow_mul]; rw [monomial_mul_X_pow]

Depends on / 依赖: X_pow_mul, monomial_mul_X_pow
-/
theorem X_pow_mul_monomial (k n : Nat) (r : R) : X ^ k * monomial n r = monomial (n + k) r := by
  rw [X_pow_mul]; rw [monomial_mul_X_pow]

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: : R[X] -> Nat -> R

中文:
定义 coeff
  签名: : R[X] -> 自然数 -> R
-/
def coeff : R[X] -> Nat -> R
  | ⟨p⟩ => p.coeff

@[simp]
/--
theorem `coeff_ofFinsupp` / 定理 `coeff_ofFinsupp`

English:
theorem coeff_ofFinsupp
  given: (p)
  statement: coeff (⟨p⟩ : R[X]) = p.coeff
  proof: by rw [coeff]

中文:
定理 coeff_ofFinsupp
  条件: (p)
  结论: coeff (⟨p⟩ : R[X]) = p.coeff
  证明: by rw [coeff]
-/
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p.coeff := by rw [coeff]

/--
theorem `coeff_injective` / 定理 `coeff_injective`

English:
theorem coeff_injective
  statement: Injective (coeff : R[X] -> Nat -> R)
  proof: by rintro ⟨p⟩ ⟨q⟩; simp [coeff]

@[simp]

中文:
定理 coeff_injective
  结论: 单射 (coeff : R[X] -> 自然数 -> R)
  证明: by rintro ⟨p⟩ ⟨q⟩; simp [coeff]

@[simp]
-/
theorem coeff_injective : Injective (coeff : R[X] -> Nat -> R) := by rintro ⟨p⟩ ⟨q⟩; simp [coeff]

@[simp]
/--
theorem `coeff_inj` / 定理 `coeff_inj`

English:
theorem coeff_inj
  statement: p.coeff = q.coeff ↔ p = q
  proof: coeff_injective.eq_iff

中文:
定理 coeff_inj
  结论: p.coeff = q.coeff ↔ p = q
  证明: coeff_injective.eq_iff

Depends on / 依赖: coeff_injective, coeff_injective.eq_iff, eq_iff
-/
theorem coeff_inj : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff

/--
theorem `toFinsupp_apply` / 定理 `toFinsupp_apply`

English:
theorem toFinsupp_apply
  given: (f : R[X]) (i)
  statement: f.toFinsupp.coeff i = f.coeff i
  proof: by cases f; rfl

中文:
定理 toFinsupp_apply
  条件: (f : R[X]) (i)
  结论: f.toFinsupp.coeff i = f.coeff i
  证明: by cases f; rfl
-/
theorem toFinsupp_apply (f : R[X]) (i) : f.toFinsupp.coeff i = f.coeff i := by cases f; rfl

/--
theorem `finite_range_coeff` / 定理 `finite_range_coeff`

English:
theorem finite_range_coeff
  given: (f : R[X])
  statement: (Set.range f.coeff).Finite
  proof: Finsupp.finite_range _

中文:
定理 finite_range_coeff
  条件: (f : R[X])
  结论: (集合.range f.coeff).有限
  证明: Finsupp.finite_range _

Depends on / 依赖: Finsupp, Finsupp.finite_range, finite_range
-/
theorem finite_range_coeff (f : R[X]) : (Set.range f.coeff).Finite :=
  Finsupp.finite_range _

/--
theorem `coeff_monomial` / 定理 `coeff_monomial`

English:
theorem coeff_monomial
  statement: coeff (monomial n a) m = if n = m then a else 0
  proof: by
  simp [coeff, Finsupp.single_apply]

@[simp]

中文:
定理 coeff_monomial
  结论: coeff (monomial n a) m = if n = m then a else 0
  证明: by
  simp [coeff, Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 := by
  simp [coeff, Finsupp.single_apply]

@[simp]
/--
theorem `coeff_monomial_same` / 定理 `coeff_monomial_same`

English:
theorem coeff_monomial_same
  given: (n : Nat) (c : R)
  statement: (monomial n c).coeff n = c
  proof: Finsupp.single_eq_same

中文:
定理 coeff_monomial_same
  条件: (n : 自然数) (c : R)
  结论: (monomial n c).coeff n = c
  证明: Finsupp.single_eq_same

Depends on / 依赖: Finsupp, Finsupp.single_eq_same, single_eq_same
-/
theorem coeff_monomial_same (n : Nat) (c : R) : (monomial n c).coeff n = c :=
  Finsupp.single_eq_same

/--
theorem `coeff_monomial_of_ne` / 定理 `coeff_monomial_of_ne`

English:
theorem coeff_monomial_of_ne
  given: {m n : Nat} (c : R) (h : m != n)
  statement: (monomial n c).coeff m = 0
  proof: Finsupp.single_eq_of_ne h

@[simp]

中文:
定理 coeff_monomial_of_ne
  条件: {m n : 自然数} (c : R) (h : m != n)
  结论: (monomial n c).coeff m = 0
  证明: Finsupp.single_eq_of_ne h

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_eq_of_ne, single_eq_of_ne
-/
theorem coeff_monomial_of_ne {m n : Nat} (c : R) (h : m != n) : (monomial n c).coeff m = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  given: (n : Nat)
  statement: coeff (0 : R[X]) n = 0
  proof: rfl

@[aesop simp]

中文:
定理 coeff_zero
  条件: (n : 自然数)
  结论: coeff (0 : R[X]) n = 0
  证明: rfl

@[aesop simp]
-/
theorem coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0 :=
  rfl

@[aesop simp]
/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: {n : Nat}
  statement: coeff (1 : R[X]) n = if n = 0 then 1 else 0
  proof: by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]

中文:
定理 coeff_one
  条件: {n : 自然数}
  结论: coeff (1 : R[X]) n = if n = 0 then 1 else 0
  证明: by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]

Depends on / 依赖: coeff_monomial, eq_comm, simp_rw
-/
theorem coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]
/--
theorem `coeff_one_zero` / 定理 `coeff_one_zero`

English:
theorem coeff_one_zero
  statement: coeff (1 : R[X]) 0 = 1
  proof: by
  simp [coeff_one]

@[simp]

中文:
定理 coeff_one_zero
  结论: coeff (1 : R[X]) 0 = 1
  证明: by
  simp [coeff_one]

@[simp]

Depends on / 依赖: IsAddTorsionFree, IsAddTorsionFree.of_isCancelMulZero_charZero, coeff_one, of_isCancelMulZero_charZero
-/
theorem coeff_one_zero : coeff (1 : R[X]) 0 = 1 := by
  simp [coeff_one]

@[simp]
/--
theorem `coeff_X_one` / 定理 `coeff_X_one`

English:
theorem coeff_X_one
  statement: coeff (X : R[X]) 1 = 1
  proof: coeff_monomial

@[simp]

中文:
定理 coeff_X_one
  结论: coeff (X : R[X]) 1 = 1
  证明: coeff_monomial

@[simp]

Depends on / 依赖: coeff_monomial
-/
theorem coeff_X_one : coeff (X : R[X]) 1 = 1 :=
  coeff_monomial

@[simp]
/--
theorem `coeff_X_zero` / 定理 `coeff_X_zero`

English:
theorem coeff_X_zero
  statement: coeff (X : R[X]) 0 = 0
  proof: coeff_monomial

@[simp]

中文:
定理 coeff_X_zero
  结论: coeff (X : R[X]) 0 = 0
  证明: coeff_monomial

@[simp]

Depends on / 依赖: coeff_monomial
-/
theorem coeff_X_zero : coeff (X : R[X]) 0 = 0 :=
  coeff_monomial

@[simp]
/--
theorem `coeff_monomial_succ` / 定理 `coeff_monomial_succ`

English:
theorem coeff_monomial_succ
  statement: coeff (monomial (n + 1) a) 0 = 0
  proof: by simp [coeff_monomial]

@[aesop simp]

中文:
定理 coeff_monomial_succ
  结论: coeff (monomial (n + 1) a) 0 = 0
  证明: by simp [coeff_monomial]

@[aesop simp]

Depends on / 依赖: coeff_monomial
-/
theorem coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

@[aesop simp]
/--
theorem `coeff_X` / 定理 `coeff_X`

English:
theorem coeff_X
  statement: coeff (X : R[X]) n = if 1 = n then 1 else 0
  proof: coeff_monomial

中文:
定理 coeff_X
  结论: coeff (X : R[X]) n = if 1 = n then 1 else 0
  证明: coeff_monomial

Depends on / 依赖: coeff_monomial
-/
theorem coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 :=
  coeff_monomial

/--
theorem `coeff_X_of_ne_one` / 定理 `coeff_X_of_ne_one`

English:
theorem coeff_X_of_ne_one
  given: {n : Nat} (hn : n != 1)
  statement: coeff (X : R[X]) n = 0
  proof: by
  rw [coeff_X]; rw [if_neg hn.symm]

中文:
定理 coeff_X_of_ne_one
  条件: {n : 自然数} (hn : n != 1)
  结论: coeff (X : R[X]) n = 0
  证明: by
  rw [coeff_X]; rw [if_neg hn.symm]

Depends on / 依赖: coeff_X, hn.symm, if_neg
-/
theorem coeff_X_of_ne_one {n : Nat} (hn : n != 1) : coeff (X : R[X]) n = 0 := by
  rw [coeff_X]; rw [if_neg hn.symm]

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  statement: n in p.support ↔ p.coeff n != 0
  proof: by
  rcases p with ⟨⟩
  simp

中文:
定理 mem_support_iff
  结论: n in p.support ↔ p.coeff n != 0
  证明: by
  rcases p with ⟨⟩
  simp
-/
theorem mem_support_iff : n in p.support ↔ p.coeff n != 0 := by
  rcases p with ⟨⟩
  simp

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  statement: n ∉ p.support ↔ p.coeff n = 0
  proof: by simp

@[aesop simp]

中文:
定理 notMem_support_iff
  结论: n ∉ p.support ↔ p.coeff n = 0
  证明: by simp

@[aesop simp]
-/
theorem notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

@[aesop simp]
/--
theorem `coeff_C` / 定理 `coeff_C`

English:
theorem coeff_C
  statement: coeff (C a) n = ite (n = 0) a 0
  proof: by
  convert! coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]

中文:
定理 coeff_C
  结论: coeff (C a) n = ite (n = 0) a 0
  证明: by
  convert! coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]

Depends on / 依赖: coeff_monomial, convert, eq_comm
-/
theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert! coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]
/--
theorem `coeff_C_zero` / 定理 `coeff_C_zero`

English:
theorem coeff_C_zero
  statement: coeff (C a) 0 = a
  proof: coeff_monomial

中文:
定理 coeff_C_zero
  结论: coeff (C a) 0 = a
  证明: coeff_monomial

Depends on / 依赖: coeff_monomial
-/
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial

/--
theorem `coeff_C_of_ne_zero` / 定理 `coeff_C_of_ne_zero`

English:
theorem coeff_C_of_ne_zero
  given: (h : n != 0)
  statement: (C a).coeff n = 0
  proof: by rw [coeff_C, if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_C_ne_zero := coeff_C_of_ne_zero

@[simp]

中文:
定理 coeff_C_of_ne_zero
  条件: (h : n != 0)
  结论: (C a).coeff n = 0
  证明: by rw [coeff_C, if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_C_ne_zero := coeff_C_of_ne_zero

@[simp]

Depends on / 依赖: coeff_C, if_neg
-/
theorem coeff_C_of_ne_zero (h : n != 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_C_ne_zero := coeff_C_of_ne_zero

@[simp]
/--
lemma `coeff_C_succ` / 引理 `coeff_C_succ`

English:
lemma coeff_C_succ
  given: {r : R} {n : Nat}
  statement: coeff (C r) (n + 1) = 0
  proof: by simp [coeff_C]

@[simp]

中文:
引理 coeff_C_succ
  条件: {r : R} {n : 自然数}
  结论: coeff (C r) (n + 1) = 0
  证明: by simp [coeff_C]

@[simp]

Depends on / 依赖: coeff_C
-/
lemma coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
/--
theorem `coeff_natCast_ite` / 定理 `coeff_natCast_ite`

English:
theorem coeff_natCast_ite
  statement: (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0
  proof: by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[simp]

中文:
定理 coeff_natCast_ite
  结论: (自然数.cast m : R[X]).coeff n = ite (n = 0) m 0
  证明: by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[simp]

Depends on / 依赖: C_eq_natCast, Nat.cast_ite, Nat.cast_zero, cast_ite, cast_zero, coeff_C
-/
theorem coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0 := by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[simp]
/--
theorem `coeff_ofNat_zero` / 定理 `coeff_ofNat_zero`

English:
theorem coeff_ofNat_zero
  given: (a : Nat) [a.AtLeastTwo]
  proof: coeff_monomial

@[simp]

中文:
定理 coeff_of自然数_zero
  条件: (a : 自然数) [a.AtLeastTwo]
  证明: coeff_monomial

@[simp]

Depends on / 依赖: coeff_monomial
-/
theorem coeff_ofNat_zero (a : Nat) [a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) 0 = ofNat(a) :=
  coeff_monomial

@[simp]
/--
theorem `coeff_ofNat_succ` / 定理 `coeff_ofNat_succ`

English:
theorem coeff_ofNat_succ
  given: (a n : Nat) [h : a.AtLeastTwo]
  proof: by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

中文:
定理 coeff_of自然数_succ
  条件: (a n : 自然数) [h : a.AtLeastTwo]
  证明: by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

Depends on / 依赖: Nat.cast_ofNat, cast_ofNat
-/
theorem coeff_ofNat_succ (a n : Nat) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

/--
theorem `C_mul_X_pow_eq_monomial` / 定理 `C_mul_X_pow_eq_monomial`

English:
theorem C_mul_X_pow_eq_monomial
  statement: forall {n : Nat}, C a * X ^ n = monomial n a

中文:
定理 C_mul_X_pow_eq_monomial
  结论: 对任意 {n : 自然数}, C a * X ^ n = monomial n a
-/
theorem C_mul_X_pow_eq_monomial : forall {n : Nat}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ]; rw [← mul_assoc]; rw [C_mul_X_pow_eq_monomial]; rw [X]; rw [monomial_mul_monomial]; rw [mul_one]

@[simp high]
/--
lemma `toFinsupp_C_mul_X_pow` / 引理 `toFinsupp_C_mul_X_pow`

English:
lemma toFinsupp_C_mul_X_pow
  given: (a : R) (n : Nat)
  statement: (C a * X ^ n).toFinsupp = .single n a
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [toFinsupp_monomial]

中文:
引理 toFinsupp_C_mul_X_pow
  条件: (a : R) (n : 自然数)
  结论: (C a * X ^ n).toFinsupp = .single n a
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [toFinsupp_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, toFinsupp_monomial
-/
lemma toFinsupp_C_mul_X_pow (a : R) (n : Nat) : (C a * X ^ n).toFinsupp = .single n a := by
  rw [C_mul_X_pow_eq_monomial]; rw [toFinsupp_monomial]

/--
theorem `C_mul_X_eq_monomial` / 定理 `C_mul_X_eq_monomial`

English:
theorem C_mul_X_eq_monomial
  statement: C a * X = monomial 1 a
  proof: by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]

中文:
定理 C_mul_X_eq_monomial
  结论: C a * X = monomial 1 a
  证明: by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]

Depends on / 依赖: C_mul_X_pow_eq_monomial, pow_one
-/
theorem C_mul_X_eq_monomial : C a * X = monomial 1 a := by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]
/--
theorem `toFinsupp_C_mul_X` / 定理 `toFinsupp_C_mul_X`

English:
theorem toFinsupp_C_mul_X
  given: (a : R)
  statement: (C a * X).toFinsupp = .single 1 a
  proof: by
  rw [C_mul_X_eq_monomial]; rw [toFinsupp_monomial]

@[grind inj]

中文:
定理 toFinsupp_C_mul_X
  条件: (a : R)
  结论: (C a * X).toFinsupp = .single 1 a
  证明: by
  rw [C_mul_X_eq_monomial]; rw [toFinsupp_monomial]

@[grind inj]

Depends on / 依赖: C_mul_X_eq_monomial, toFinsupp_monomial
-/
theorem toFinsupp_C_mul_X (a : R) : (C a * X).toFinsupp = .single 1 a := by
  rw [C_mul_X_eq_monomial]; rw [toFinsupp_monomial]

@[grind inj]
/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  statement: Injective (C : R -> R[X])
  proof: monomial_injective 0

@[simp]

中文:
定理 C_injective
  结论: 单射 (C : R -> R[X])
  证明: monomial_injective 0

@[simp]

Depends on / 依赖: monomial_injective
-/
theorem C_injective : Injective (C : R -> R[X]) :=
  monomial_injective 0

@[simp]
/--
theorem `C_inj` / 定理 `C_inj`

English:
theorem C_inj
  statement: C a = C b ↔ a = b
  proof: C_injective.eq_iff

@[simp]

中文:
定理 C_inj
  结论: C a = C b ↔ a = b
  证明: C_injective.eq_iff

@[simp]

Depends on / 依赖: C_injective, C_injective.eq_iff, eq_iff
-/
theorem C_inj : C a = C b ↔ a = b :=
  C_injective.eq_iff

@[simp]
/--
theorem `C_eq_zero` / 定理 `C_eq_zero`

English:
theorem C_eq_zero
  statement: C a = 0 ↔ a = 0
  proof: C_injective.eq_iff' (map_zero C)

中文:
定理 C_eq_zero
  结论: C a = 0 ↔ a = 0
  证明: C_injective.eq_iff' (map_zero C)

Depends on / 依赖: C_injective, C_injective.eq_iff, eq_iff, map_zero
-/
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  C_injective.eq_iff' (map_zero C)

/--
theorem `C_ne_zero` / 定理 `C_ne_zero`

English:
theorem C_ne_zero
  statement: C a != 0 ↔ a != 0
  proof: C_eq_zero.not

中文:
定理 C_ne_zero
  结论: C a != 0 ↔ a != 0
  证明: C_eq_zero.not

Depends on / 依赖: C_eq_zero, C_eq_zero.not
-/
theorem C_ne_zero : C a != 0 ↔ a != 0 :=
  C_eq_zero.not

/--
theorem `subsingleton_iff_subsingleton` / 定理 `subsingleton_iff_subsingleton`

English:
theorem subsingleton_iff_subsingleton
  statement: Subsingleton R[X] ↔ Subsingleton R
  proof: ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩

中文:
定理 subsingleton_iff_subsingleton
  结论: 子单例 R[X] ↔ 子单例 R
  证明: ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩

Depends on / 依赖: C_injective, Injective, Injective.subsingleton, infer_instance, subsingleton
-/
theorem subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R :=
  ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩

/--
theorem `Nontrivial.of_polynomial_ne` / 定理 `Nontrivial.of_polynomial_ne`

English:
theorem Nontrivial.of_polynomial_ne
  given: (h : p != q)
  statement: Nontrivial R
  proof: (subsingleton_or_nontrivial R).resolve_left fun _hI => h Subsingleton.elim _ _

中文:
定理 非平凡.of_polynomial_ne
  条件: (h : p != q)
  结论: 非平凡 R
  证明: (subsingleton_or_nontrivial R).resolve_left fun _hI => h Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, resolve_left, subsingleton_or_nontrivial
-/
theorem Nontrivial.of_polynomial_ne (h : p != q) : Nontrivial R :=
(subsingleton_or_nontrivial R).resolve_left fun _hI => h Subsingleton.elim _ _

/--
theorem `forall_eq_iff_forall_eq` / 定理 `forall_eq_iff_forall_eq`

English:
theorem forall_eq_iff_forall_eq
  statement: (forall f g : R[X], f = g) ↔ forall a b : R, a = b
  proof: by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

中文:
定理 对任意_eq_iff_对任意_eq
  结论: (对任意 f g : R[X], f = g) ↔ 对任意 a b : R, a = b
  证明: by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

Depends on / 依赖: subsingleton_iff, subsingleton_iff_subsingleton
-/
theorem forall_eq_iff_forall_eq : (forall f g : R[X], f = g) ↔ forall a b : R, a = b := by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {p q : R[X]}
  statement: p = q ↔ forall n, coeff p n = coeff q n
  proof: by
  rcases p with ⟨f⟩
  rcases q with ⟨g⟩
  simpa [coeff] using! DFunLike.ext_iff (f := f.coeff) (g := g.coeff)

@[ext]

中文:
定理 ext_iff
  条件: {p q : R[X]}
  结论: p = q ↔ 对任意 n, coeff p n = coeff q n
  证明: by
  rcases p with ⟨f⟩
  rcases q with ⟨g⟩
  simpa [coeff] using! DFunLike.ext_iff (f := f.coeff) (g := g.coeff)

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, f.coeff, g.coeff
-/
theorem ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n = coeff q n := by
  rcases p with ⟨f⟩
  rcases q with ⟨g⟩
  simpa [coeff] using! DFunLike.ext_iff (f := f.coeff) (g := g.coeff)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : R[X]}
  statement: (forall n, coeff p n = coeff q n) -> p = q
  proof: ext_iff.2

中文:
定理 ext
  条件: {p q : R[X]}
  结论: (对任意 n, coeff p n = coeff q n) -> p = q
  证明: ext_iff.2

Depends on / 依赖: ext_iff
-/
theorem ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> p = q :=
  ext_iff.2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addSubmonoid_closure_setOfPred_eq_monomial` / 定理 `addSubmonoid_closure_setOfPred_eq_monomial`

English:
theorem addSubmonoid_closure_setOfPred_eq_monomial
  proof: by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv]; rw [← addSubmonoidClosure_single]; rw [AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

@[depre

中文:
定理 addSubmonoid_closure_setOfPred_eq_monomial
  证明: by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv]; rw [← addSubmonoidClosure_single]; rw [AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

@[depre

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_mclosure, AddSubmonoid, AddSubmonoid.closure_mono, AddSubmonoid.map_equiv_top, Polynomial, Polynomial.ofFinsupp_single, Set.image_subset_iff, addSubmonoidClosure_single, closure_mono, image_subset_iff, map_equiv_top, map_mclosure, ofFinsupp_single, symm.toAddEquiv, toAddEquiv, toFinsuppIso, top_unique
-/
theorem addSubmonoid_closure_setOfPred_eq_monomial :
    AddSubmonoid.closure { p : R[X] | exists n a, p = monomial n a } = ⊤ := by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv]; rw [← addSubmonoidClosure_single]; rw [AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

@[deprecated (since := "2026-07-09")]
alias addSubmonoid_closure_setOf_eq_monomial := addSubmonoid_closure_setOfPred_eq_monomial

@[ext high]
/--
theorem `addHom_ext` / 定理 `addHom_ext`

English:
theorem addHom_ext
  statement: {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M}
  proof: AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOfPred_eq_monomial by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]

中文:
定理 addHom_ext
  结论: {M : 类型} [加法零类 M] {f g : R[X] ->+ M}
  证明: AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOfPred_eq_monomial by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.eq_of_eqOn_denseM, addSubmonoid_closure_setOfPred_eq_monomial, eq_of_eqOn_denseM
-/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M}
    (h : forall n a, f (monomial n a) = g (monomial n a)) : f = g :=
AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOfPred_eq_monomial by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]
/--
theorem `addHom_ext'` / 定理 `addHom_ext'`

English:
theorem addHom_ext'
  statement: {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M}
  proof: addHom_ext fun n => DFunLike.congr_fun (h n)

@[ext high]

中文:
定理 addHom_ext'
  结论: {M : 类型} [加法零类 M] {f g : R[X] ->+ M}
  证明: addHom_ext fun n => DFunLike.congr_fun (h n)

@[ext high]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, addHom_ext, congr_fun
-/
theorem addHom_ext' {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M}
    (h : forall n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  addHom_ext fun n => DFunLike.congr_fun (h n)

@[ext high]
/--
theorem `lhom_ext'` / 定理 `lhom_ext'`

English:
theorem lhom_ext'
  statement: {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] ->ₗ[R] M}
  proof: LinearMap.toAddMonoidHom_injective addHom_ext fun n => LinearMap.congr_fun (h n)

中文:
定理 lhom_ext'
  结论: {M : 类型} [加法交换幺半群 M] [模 R M] {f g : R[X] ->ₗ[R] M}
  证明: LinearMap.toAddMonoidHom_injective addHom_ext fun n => LinearMap.congr_fun (h n)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.toAddMonoidHom_injective, addHom_ext, congr_fun, toAddMonoidHom_injective
-/
theorem lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] ->ₗ[R] M}
    (h : forall n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
LinearMap.toAddMonoidHom_injective addHom_ext fun n => LinearMap.congr_fun (h n)

-- this has the same content as the subsingleton
/--
theorem `eq_zero_of_eq_zero` / 定理 `eq_zero_of_eq_zero`

English:
theorem eq_zero_of_eq_zero
  given: (h : (0 : R) = (1 : R)) (p : R[X])
  statement: p = 0
  proof: by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

中文:
定理 eq_zero_of_eq_zero
  条件: (h : (0 : R) = (1 : R)) (p : R[X])
  结论: p = 0
  证明: by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

Depends on / 依赖: one_smul, zero_smul
-/
theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 := by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

section Fewnomials

@[simp]
/--
theorem `support_monomial` / 定理 `support_monomial`

English:
theorem support_monomial
  given: (n) {a : R} (h : a != 0)
  statement: (monomial n a).support = singleton n
  proof: by
  rw [← ofFinsupp_single]; rw [support]; exact Finsupp.support_single _ h

中文:
定理 support_monomial
  条件: (n) {a : R} (h : a != 0)
  结论: (monomial n a).support = singleton n
  证明: by
  rw [← ofFinsupp_single]; rw [support]; exact Finsupp.support_single _ h

Depends on / 依赖: Finsupp, Finsupp.support_single, ofFinsupp_single, support, support_single
-/
theorem support_monomial (n) {a : R} (h : a != 0) : (monomial n a).support = singleton n := by
  rw [← ofFinsupp_single]; rw [support]; exact Finsupp.support_single _ h

/--
theorem `support_monomial_subset` / 定理 `support_monomial_subset`

English:
theorem support_monomial_subset
  given: (n) (a : R)
  statement: (monomial n a).support subseteq singleton n
  proof: by
  rw [← ofFinsupp_single]; rw [support]
  exact Finsupp.support_single_subset

@[deprecated (since := "2026-06-09")] alias support_monomial' := support_monomial_subset

@[simp]

中文:
定理 support_monomial_subset
  条件: (n) (a : R)
  结论: (monomial n a).support subseteq singleton n
  证明: by
  rw [← ofFinsupp_single]; rw [support]
  exact Finsupp.support_single_subset

@[deprecated (since := "2026-06-09")] alias support_monomial' := support_monomial_subset

@[simp]

Depends on / 依赖: Finsupp, Finsupp.support_single_subset, ofFinsupp_single, support, support_single_subset
-/
theorem support_monomial_subset (n) (a : R) : (monomial n a).support subseteq singleton n := by
  rw [← ofFinsupp_single]; rw [support]
  exact Finsupp.support_single_subset

@[deprecated (since := "2026-06-09")] alias support_monomial' := support_monomial_subset

@[simp]
/--
theorem `support_C` / 定理 `support_C`

English:
theorem support_C
  given: {a : R} (h : a != 0)
  statement: (C a).support = singleton 0
  proof: support_monomial 0 h

中文:
定理 support_C
  条件: {a : R} (h : a != 0)
  结论: (C a).support = singleton 0
  证明: support_monomial 0 h

Depends on / 依赖: Bracket, instBracket, support_monomial
-/
theorem support_C {a : R} (h : a != 0) : (C a).support = singleton 0 :=
  support_monomial 0 h

/--
theorem `support_C_subset` / 定理 `support_C_subset`

English:
theorem support_C_subset
  given: (a : R)
  statement: (C a).support subseteq singleton 0
  proof: support_monomial_subset 0 a

@[simp]

中文:
定理 support_C_subset
  条件: (a : R)
  结论: (C a).support subseteq singleton 0
  证明: support_monomial_subset 0 a

@[simp]

Depends on / 依赖: support_monomial_subset
-/
theorem support_C_subset (a : R) : (C a).support subseteq singleton 0 :=
  support_monomial_subset 0 a

@[simp]
/--
theorem `support_C_mul_X` / 定理 `support_C_mul_X`

English:
theorem support_C_mul_X
  given: {c : R} (h : c != 0)
  statement: Polynomial.support (C c * X) = singleton 1
  proof: by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]

中文:
定理 support_C_mul_X
  条件: {c : R} (h : c != 0)
  结论: 多项式.support (C c * X) = singleton 1
  证明: by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]

Depends on / 依赖: C_mul_X_eq_monomial, support_monomial
-/
theorem support_C_mul_X {c : R} (h : c != 0) : Polynomial.support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]

/--
theorem `support_C_mul_X_subset` / 定理 `support_C_mul_X_subset`

English:
theorem support_C_mul_X_subset
  given: (c : R)
  statement: Polynomial.support (C c * X) subseteq singleton 1
  proof: by
  simpa only [C_mul_X_eq_monomial] using support_monomial_subset 1 c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X' := support_C_mul_X_subset

@[simp]

中文:
定理 support_C_mul_X_subset
  条件: (c : R)
  结论: 多项式.support (C c * X) subseteq singleton 1
  证明: by
  simpa only [C_mul_X_eq_monomial] using support_monomial_subset 1 c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X' := support_C_mul_X_subset

@[simp]

Depends on / 依赖: C_mul_X_eq_monomial, support_monomial_subset
-/
theorem support_C_mul_X_subset (c : R) : Polynomial.support (C c * X) subseteq singleton 1 := by
  simpa only [C_mul_X_eq_monomial] using support_monomial_subset 1 c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X' := support_C_mul_X_subset

@[simp]
/--
theorem `support_C_mul_X_pow` / 定理 `support_C_mul_X_pow`

English:
theorem support_C_mul_X_pow
  given: (n : Nat) {c : R} (h : c != 0)
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

中文:
定理 support_C_mul_X_pow
  条件: (n : 自然数) {c : R} (h : c != 0)
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

Depends on / 依赖: C_mul_X_pow_eq_monomial, support_monomial
-/
theorem support_C_mul_X_pow (n : Nat) {c : R} (h : c != 0) :
    Polynomial.support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

/--
theorem `support_C_mul_X_pow_subset` / 定理 `support_C_mul_X_pow_subset`

English:
theorem support_C_mul_X_pow_subset
  given: (n : Nat) (c : R)
  proof: by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial_subset n c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X_pow' := support_C_mul_X_pow_subset

中文:
定理 support_C_mul_X_pow_subset
  条件: (n : 自然数) (c : R)
  证明: by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial_subset n c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X_pow' := support_C_mul_X_pow_subset

Depends on / 依赖: C_mul_X_pow_eq_monomial, support_monomial_subset
-/
theorem support_C_mul_X_pow_subset (n : Nat) (c : R) :
    Polynomial.support (C c * X ^ n) subseteq singleton n := by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial_subset n c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X_pow' := support_C_mul_X_pow_subset

open Finset

/--
theorem `support_binomial_subset` / 定理 `support_binomial_subset`

English:
theorem support_binomial_subset
  given: (k m : Nat) (x y : R)
  proof: support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

@[deprecated (since := "2026-06-09")] a

中文:
定理 support_binomial_subset
  条件: (k m : 自然数) (x y : R)
  证明: support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

@[deprecated (since := "2026-06-09")] a

Depends on / 依赖: mem_insert_of_mem, mem_insert_self, mem_singleton_self, singleton_subset_iff, singleton_subset_iff.mpr, support_C_mul_X_pow_subset, support_add, support_add.trans, union_subset
-/
theorem support_binomial_subset (k m : Nat) (x y : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m) subseteq {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

@[deprecated (since := "2026-06-09")] alias support_binomial' := support_binomial_subset

/--
theorem `support_trinomial_subset` / 定理 `support_trinomial_subset`

English:
theorem support_trinomial_subset
  given: (k m n : Nat) (x y z : R)
  proof: support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow_subset k x).trans
            (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow_subset m y).trans
            (singleton_subset_iff.mpr (mem_insert_

中文:
定理 support_trinomial_subset
  条件: (k m n : 自然数) (x y z : R)
  证明: support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow_subset k x).trans
            (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow_subset m y).trans
            (singleton_subset_iff.mpr (mem_insert_

Depends on / 依赖: mem_insert_of_mem, mem_insert_self, mem_singleton_self, singleton_subset_iff, singleton_subset_iff.mpr, support_C_mul_X_pow_subset, support_add, support_add.trans, union_subset
-/
theorem support_trinomial_subset (k m n : Nat) (x y z : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) subseteq {k, m, n} :=
  support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow_subset k x).trans
            (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow_subset m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((support_C_mul_X_pow_subset n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

@[deprecated (since := "2026-06-09")] alias support_trinomial' := support_trinomial_subset

end Fewnomials

/--
theorem `X_pow_eq_monomial` / 定理 `X_pow_eq_monomial`

English:
theorem X_pow_eq_monomial
  given: (n)
  statement: X ^ n = monomial n (1 : R)
  proof: (monomial_one_right_eq_X_pow n).symm

@[simp high]

中文:
定理 X_pow_eq_monomial
  条件: (n)
  结论: X ^ n = monomial n (1 : R)
  证明: (monomial_one_right_eq_X_pow n).symm

@[simp high]

Depends on / 依赖: monomial_one_right_eq_X_pow
-/
theorem X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R) :=
  (monomial_one_right_eq_X_pow n).symm

@[simp high]
/--
theorem `toFinsupp_X_pow` / 定理 `toFinsupp_X_pow`

English:
theorem toFinsupp_X_pow
  given: (n : Nat)
  statement: (X ^ n).toFinsupp = .single n (1 : R)
  proof: by
  rw [X_pow_eq_monomial]; rw [toFinsupp_monomial]

中文:
定理 toFinsupp_X_pow
  条件: (n : 自然数)
  结论: (X ^ n).toFinsupp = .single n (1 : R)
  证明: by
  rw [X_pow_eq_monomial]; rw [toFinsupp_monomial]

Depends on / 依赖: X_pow_eq_monomial, toFinsupp_monomial
-/
theorem toFinsupp_X_pow (n : Nat) : (X ^ n).toFinsupp = .single n (1 : R) := by
  rw [X_pow_eq_monomial]; rw [toFinsupp_monomial]

/--
theorem `smul_X_eq_monomial` / 定理 `smul_X_eq_monomial`

English:
theorem smul_X_eq_monomial
  given: {n}
  statement: a • X ^ n = monomial n (a : R)
  proof: by
  rw [X_pow_eq_monomial]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]

@[simp]

中文:
定理 smul_X_eq_monomial
  条件: {n}
  结论: a • X ^ n = monomial n (a : R)
  证明: by
  rw [X_pow_eq_monomial]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, mul_one, smul_eq_mul, smul_monomial
-/
theorem smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R) := by
  rw [X_pow_eq_monomial]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]

@[simp]
/--
theorem `support_X_pow` / 定理 `support_X_pow`

English:
theorem support_X_pow
  given: [Nontrivial R] (n : Nat)
  statement: (X ^ n : R[X]).support = singleton n
  proof: by
  convert! support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

中文:
定理 support_X_pow
  条件: [非平凡 R] (n : 自然数)
  结论: (X ^ n : R[X]).support = singleton n
  证明: by
  convert! support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

Depends on / 依赖: NeZero, NeZero.out, X_pow_eq_monomial, convert, support_monomial
-/
theorem support_X_pow [Nontrivial R] (n : Nat) : (X ^ n : R[X]).support = singleton n := by
  convert! support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

/--
theorem `support_X_empty` / 定理 `support_X_empty`

English:
theorem support_X_empty
  given: (H : (1 : R) = 0)
  statement: (X : R[X]).support = ∅
  proof: by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]

中文:
定理 support_X_empty
  条件: (H : (1 : R) = 0)
  结论: (X : R[X]).support = ∅
  证明: by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]

Depends on / 依赖: monomial_zero_right, support_zero
-/
theorem support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅ := by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]
/--
theorem `support_X` / 定理 `support_X`

English:
theorem support_X
  given: [Nontrivial R]
  statement: (X : R[X]).support = singleton 1
  proof: by
  rw [← pow_one X]; rw [support_X_pow 1]

中文:
定理 support_X
  条件: [非平凡 R]
  结论: (X : R[X]).support = singleton 1
  证明: by
  rw [← pow_one X]; rw [support_X_pow 1]

Depends on / 依赖: pow_one, support_X_pow
-/
theorem support_X [Nontrivial R] : (X : R[X]).support = singleton 1 := by
  rw [← pow_one X]; rw [support_X_pow 1]

/--
theorem `monomial_left_inj` / 定理 `monomial_left_inj`

English:
theorem monomial_left_inj
  given: {a : R} (ha : a != 0) {i j : Nat}
  proof: by
  simp [monomial_eq_monomial_iff, ha]

中文:
定理 monomial_left_inj
  条件: {a : R} (ha : a != 0) {i j : 自然数}
  证明: by
  simp [monomial_eq_monomial_iff, ha]

Depends on / 依赖: monomial_eq_monomial_iff
-/
theorem monomial_left_inj {a : R} (ha : a != 0) {i j : Nat} :
    monomial i a = monomial j a ↔ i = j := by
  simp [monomial_eq_monomial_iff, ha]

/--
theorem `binomial_eq_binomial` / 定理 `binomial_eq_binomial`

English:
theorem binomial_eq_binomial
  given: {k l m n : Nat} {u v : R} (hu : u != 0) (hv : v != 0)
  proof: by
  simp [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, single_add_single_inj, *]

中文:
定理 binomial_eq_binomial
  条件: {k l m n : 自然数} {u v : R} (hu : u != 0) (hv : v != 0)
  证明: by
  simp [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, single_add_single_inj, *]

Depends on / 依赖: C_mul_X_pow_eq_monomial, single_add_single_inj, toFinsupp_inj
-/
theorem binomial_eq_binomial {k l m n : Nat} {u v : R} (hu : u != 0) (hv : v != 0) :
    C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n := by
  simp [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, single_add_single_inj, *]

/--
theorem `natCast_mul` / 定理 `natCast_mul`

English:
theorem natCast_mul
  given: (n : Nat) (p : R[X])
  statement: (n : R[X]) * p = n • p
  proof: (nsmul_eq_mul _ _).symm

中文:
定理 natCast_mul
  条件: (n : 自然数) (p : R[X])
  结论: (n : R[X]) * p = n • p
  证明: (nsmul_eq_mul _ _).symm

Depends on / 依赖: nsmul_eq_mul
-/
theorem natCast_mul (n : Nat) (p : R[X]) : (n : R[X]) * p = n • p :=
  (nsmul_eq_mul _ _).symm

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S)
  body: ∑ n in p.support, f n (p.coeff n)

中文:
定义 求和
  签名: {S : 类型} [加法交换幺半群 S] (p : R[X]) (f : 自然数 -> R -> S)
  定义体: ∑ n in p.support, f n (p.coeff n)

Depends on / 依赖: p.coeff, p.support, support
-/
def sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S) : S :=
  ∑ n in p.support, f n (p.coeff n)

/--
theorem `sum_def` / 定理 `sum_def`

English:
theorem sum_def
  given: {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S)
  proof: rfl

中文:
定理 sum_def
  条件: {S : 类型} [加法交换幺半群 S] (p : R[X]) (f : 自然数 -> R -> S)
  证明: rfl

Depends on / 依赖: RingHomInvPair, invPair
-/
theorem sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S) :
    p.sum f = ∑ n in p.support, f n (p.coeff n) :=
  rfl

/--
theorem `sum_eq_of_subset` / 定理 `sum_eq_of_subset`

English:
theorem sum_eq_of_subset
  statement: {S : Type*} [AddCommMonoid S] {p : R[X]} (f : Nat -> R -> S)
  proof: Finsupp.sum_of_support_subset _ hs f (fun i _ => hf i)

中文:
定理 sum_eq_of_subset
  结论: {S : 类型} [加法交换幺半群 S] {p : R[X]} (f : 自然数 -> R -> S)
  证明: Finsupp.sum_of_support_subset _ hs f (fun i _ => hf i)

Depends on / 依赖: Finsupp, Finsupp.sum_of_support_subset, sum_of_support_subset
-/
theorem sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : Nat -> R -> S)
    (hf : forall i, f i 0 = 0) {s : Finset Nat} (hs : p.support subseteq s) :
    p.sum f = ∑ n in s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ => hf i)

/--
theorem `mul_eq_sum_sum` / 定理 `mul_eq_sum_sum`

English:
theorem mul_eq_sum_sum
  proof: by
  apply toFinsupp_injective
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]

中文:
定理 mul_eq_sum_sum
  证明: by
  apply toFinsupp_injective
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mul_def, Finsupp, Finsupp.sum, mul_def, simp_rw, support, toFinsupp_injective, toFinsupp_monomial, toFinsupp_mul, toFinsupp_sum
-/
theorem mul_eq_sum_sum :
    p * q = ∑ i in p.support, q.sum fun j a => (monomial (i + j)) (p.coeff i * a) := by
  apply toFinsupp_injective
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]
/--
theorem `sum_zero_index` / 定理 `sum_zero_index`

English:
theorem sum_zero_index
  given: {S : Type*} [AddCommMonoid S] (f : Nat -> R -> S)
  statement: (0 : R[X]).sum f = 0
  proof: by
  simp [sum]

@[simp]

中文:
定理 sum_zero_index
  条件: {S : 类型} [加法交换幺半群 S] (f : 自然数 -> R -> S)
  结论: (0 : R[X]).求和 f = 0
  证明: by
  simp [sum]

@[simp]

Depends on / 依赖: surjective
-/
theorem sum_zero_index {S : Type*} [AddCommMonoid S] (f : Nat -> R -> S) : (0 : R[X]).sum f = 0 := by
  simp [sum]

@[simp]
/--
theorem `sum_monomial_index` / 定理 `sum_monomial_index`

English:
theorem sum_monomial_index
  statement: {S : Type*} [AddCommMonoid S] {n : Nat} (a : R) (f : Nat -> R -> S)
  proof: Finsupp.sum_single_index hf

@[simp]

中文:
定理 sum_monomial_index
  结论: {S : 类型} [加法交换幺半群 S] {n : 自然数} (a : R) (f : 自然数 -> R -> S)
  证明: Finsupp.sum_single_index hf

@[simp]

Depends on / 依赖: Distrib, Distrib.leftDistribClass, Finsupp, Finsupp.sum_single_index, LeftDistribClass, leftDistribClass, sum_single_index
-/
theorem sum_monomial_index {S : Type*} [AddCommMonoid S] {n : Nat} (a : R) (f : Nat -> R -> S)
    (hf : f n 0 = 0) : (monomial n a : R[X]).sum f = f n a :=
  Finsupp.sum_single_index hf

@[simp]
/--
theorem `sum_C_index` / 定理 `sum_C_index`

English:
theorem sum_C_index
  given: {a} {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0)
  proof: sum_monomial_index a f h

中文:
定理 sum_C_index
  条件: {a} {β} [加法交换幺半群 β] {f : 自然数 -> R -> β} (h : f 0 0 = 0)
  证明: sum_monomial_index a f h

Depends on / 依赖: Distrib, Distrib.rightDistribClass, rightDistribClass, sum_monomial_index
-/
theorem sum_C_index {a} {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0) :
    (C a).sum f = f 0 a :=
  sum_monomial_index a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp]
/--
theorem `sum_X_index` / 定理 `sum_X_index`

English:
theorem sum_X_index
  given: {S : Type*} [AddCommMonoid S] {f : Nat -> R -> S} (hf : f 1 0 = 0)
  proof: sum_monomial_index 1 f hf

中文:
定理 sum_X_index
  条件: {S : 类型} [加法交换幺半群 S] {f : 自然数 -> R -> S} (hf : f 1 0 = 0)
  证明: sum_monomial_index 1 f hf

Depends on / 依赖: sum_monomial_index
-/
theorem sum_X_index {S : Type*} [AddCommMonoid S] {f : Nat -> R -> S} (hf : f 1 0 = 0) :
    (X : R[X]).sum f = f 1 1 :=
  sum_monomial_index 1 f hf

/--
theorem `sum_add_index` / 定理 `sum_add_index`

English:
theorem sum_add_index
  statement: {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : Nat -> R -> S)
  proof: by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ from rfl]
  exact Finsupp.sum_add_index (fun i _ => hf i) (fun a _ b₁ b₂ => h_add a b₁ b₂)

中文:
定理 sum_add_index
  结论: {S : 类型} [加法交换幺半群 S] (p q : R[X]) (f : 自然数 -> R -> S)
  证明: by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ from rfl]
  exact Finsupp.sum_add_index (fun i _ => hf i) (fun a _ b₁ b₂ => h_add a b₁ b₂)

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, h_add, p.toFinsupp, q.toFinsupp, sum_add_index, toFinsupp
-/
theorem sum_add_index {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : Nat -> R -> S)
    (hf : forall i, f i 0 = 0) (h_add : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ from rfl]
  exact Finsupp.sum_add_index (fun i _ => hf i) (fun a _ b₁ b₂ => h_add a b₁ b₂)

/-- See also `Polynomial.sum_add`. -/
@[simp]
/--
theorem `sum_add'` / 定理 `sum_add'`

English:
theorem sum_add'
  given: {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S)
  proof: by simp [sum_def, Finset.sum_add_distrib]

中文:
定理 sum_add'
  条件: {S : 类型} [加法交换幺半群 S] (p : R[X]) (f g : 自然数 -> R -> S)
  证明: by simp [sum_def, Finset.sum_add_distrib]

Depends on / 依赖: Finset, Finset.sum_add_distrib, sum_add_distrib, sum_def
-/
theorem sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [sum_def, Finset.sum_add_distrib]

/-- See also `Polynomial.sum_add'`. -/
@[simp]
/--
theorem `sum_add` / 定理 `sum_add`

English:
theorem sum_add
  given: {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S)
  proof: sum_add' _ _ _

中文:
定理 sum_add
  条件: {S : 类型} [加法交换幺半群 S] (p : R[X]) (f g : 自然数 -> R -> S)
  证明: sum_add' _ _ _

Depends on / 依赖: sum_add
-/
theorem sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

/--
theorem `sum_smul_index` / 定理 `sum_smul_index`

English:
theorem sum_smul_index
  statement: {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : Nat -> R -> S)
  proof: Finsupp.sum_smul_index hf

中文:
定理 sum_smul_index
  结论: {S : 类型} [加法交换幺半群 S] (p : R[X]) (b : R) (f : 自然数 -> R -> S)
  证明: Finsupp.sum_smul_index hf

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, sum_smul_index
-/
theorem sum_smul_index {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : Nat -> R -> S)
    (hf : forall i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b * a) :=
  Finsupp.sum_smul_index hf

/--
theorem `sum_smul_index'` / 定理 `sum_smul_index'`

English:
theorem sum_smul_index'
  statement: {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
  proof: Finsupp.sum_smul_index' hf

中文:
定理 sum_smul_index'
  结论: {S T : 类型} [分配标量乘法 T R] [加法交换幺半群 S] (p : R[X]) (b : T)
  证明: Finsupp.sum_smul_index' hf

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, sum_smul_index
-/
theorem sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
    (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) :=
  Finsupp.sum_smul_index' hf

/--
theorem `smul_sum` / 定理 `smul_sum`

English:
theorem smul_sum
  statement: {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
  proof: Finsupp.smul_sum

@[simp]

中文:
定理 smul_sum
  结论: {S T : 类型} [加法交换幺半群 S] [分配标量乘法 T S] (p : R[X]) (b : T)
  证明: Finsupp.smul_sum

@[simp]
-/
protected theorem smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
    (f : Nat -> R -> S) : b • p.sum f = p.sum fun n a => b • f n a :=
  Finsupp.smul_sum

@[simp]
/--
theorem `sum_monomial_eq` / 定理 `sum_monomial_eq`

English:
theorem sum_monomial_eq
  statement: forall p : R[X], (p.sum fun n a => monomial n a) = p

中文:
定理 sum_monomial_eq
  结论: 对任意 p : R[X], (p.求和 fun n a => monomial n a) = p
-/
theorem sum_monomial_eq : forall p : R[X], (p.sum fun n a => monomial n a) = p
  | ⟨_p⟩ => (ofFinsupp_sum _ _).symm.trans (congr_arg _ <| sum_coeff_single _)

/--
theorem `sum_C_mul_X_pow_eq` / 定理 `sum_C_mul_X_pow_eq`

English:
theorem sum_C_mul_X_pow_eq
  given: (p : R[X])
  statement: (p.sum fun n a => C a * X ^ n) = p
  proof: by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]

中文:
定理 sum_C_mul_X_pow_eq
  条件: (p : R[X])
  结论: (p.求和 fun n a => C a * X ^ n) = p
  证明: by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]

Depends on / 依赖: C_mul_X_pow_eq_monomial, simp_rw, sum_monomial_eq
-/
theorem sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a => C a * X ^ n) = p := by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : R[X] -> Prop} (p : R[X]) (C : forall a, motive (C a))
  proof: by
  have A : forall {n : Nat} {a}, motive (Polynomial.C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact C a
    | succ n ih => exact monomial _ _ ih
  have B : forall s : Finset Nat, motive (s.sum fun n : Nat => Polynomial.C (p.coeff n) * X ^ n) := by

中文:
定理 induction_on
  结论: {motive : R[X] -> 命题} (p : R[X]) (C : 对任意 a, motive (C a))
  证明: by
  have A : forall {n : Nat} {a}, motive (Polynomial.C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact C a
    | succ n ih => exact monomial _ _ ih
  have B : forall s : Finset Nat, motive (s.sum fun n : Nat => Polynomial.C (p.coeff n) * X ^ n) := by
-/
protected theorem induction_on {motive : R[X] -> Prop} (p : R[X]) (C : forall a, motive (C a))
    (add : forall p q, motive p -> motive q -> motive (p + q))
    (monomial : forall (n : Nat) (a : R),
      motive (Polynomial.C a * X ^ n) -> motive (Polynomial.C a * X ^ (n + 1))) : motive p := by
  have A : forall {n : Nat} {a}, motive (Polynomial.C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact C a
    | succ n ih => exact monomial _ _ ih
  have B : forall s : Finset Nat, motive (s.sum fun n : Nat => Polynomial.C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert! C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p]; rw [Polynomial.sum]
  exact B (support p)

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {motive : R[X] -> Prop} (p : R[X])
  proof: Polynomial.induction_on p (monomial 0) add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact monomial _ _

中文:
定理 induction_on'
  结论: {motive : R[X] -> 命题} (p : R[X])
  证明: Polynomial.induction_on p (monomial 0) add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact monomial _ _
-/
protected theorem induction_on' {motive : R[X] -> Prop} (p : R[X])
    (add : forall p q, motive p -> motive q -> motive (p + q))
    (monomial : forall (n : Nat) (a : R), motive (monomial n a)) : motive p :=
  Polynomial.induction_on p (monomial 0) add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact monomial _ _

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
irreducible_def erase (n : Nat) : R[X] -> R[X]
  | ⟨p⟩ => ⟨p.erase n⟩

@[simp]
/--
theorem `toFinsupp_erase` / 定理 `toFinsupp_erase`

English:
theorem toFinsupp_erase
  given: (p : R[X]) (n : Nat)
  statement: toFinsupp (p.erase n) = p.toFinsupp.erase n
  proof: by
  simp only [erase_def]

@[simp]

中文:
定理 toFinsupp_erase
  条件: (p : R[X]) (n : 自然数)
  结论: toFinsupp (p.erase n) = p.toFinsupp.erase n
  证明: by
  simp only [erase_def]

@[simp]

Depends on / 依赖: erase_def
-/
theorem toFinsupp_erase (p : R[X]) (n : Nat) : toFinsupp (p.erase n) = p.toFinsupp.erase n := by
  simp only [erase_def]

@[simp]
/--
theorem `ofFinsupp_erase` / 定理 `ofFinsupp_erase`

English:
theorem ofFinsupp_erase
  given: (p : R[Nat]) (n : Nat)
  proof: by
  simp only [erase_def]

中文:
定理 ofFinsupp_erase
  条件: (p : R[自然数]) (n : 自然数)
  证明: by
  simp only [erase_def]

Depends on / 依赖: erase_def
-/
theorem ofFinsupp_erase (p : R[Nat]) (n : Nat) :
    (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X]).erase n := by
  simp only [erase_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `support_erase` / 定理 `support_erase`

English:
theorem support_erase
  given: (p : R[X]) (n : Nat)
  statement: support (p.erase n) = (support p).erase n
  proof: by
  simp [support]

中文:
定理 support_erase
  条件: (p : R[X]) (n : 自然数)
  结论: support (p.erase n) = (support p).erase n
  证明: by
  simp [support]

Depends on / 依赖: support
-/
theorem support_erase (p : R[X]) (n : Nat) : support (p.erase n) = (support p).erase n := by
  simp [support]

/--
theorem `monomial_add_erase` / 定理 `monomial_add_erase`

English:
theorem monomial_add_erase
  given: (p : R[X]) (n : Nat)
  statement: monomial n (coeff p n) + p.erase n = p
  proof: by
  apply toFinsupp_injective
  simp only [toFinsupp_add, toFinsupp_monomial, toFinsupp_erase]
  exact AddMonoidAlgebra.single_add_erase ..

中文:
定理 monomial_add_erase
  条件: (p : R[X]) (n : 自然数)
  结论: monomial n (coeff p n) + p.erase n = p
  证明: by
  apply toFinsupp_injective
  simp only [toFinsupp_add, toFinsupp_monomial, toFinsupp_erase]
  exact AddMonoidAlgebra.single_add_erase ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.single_add_erase, single_add_erase, toFinsupp_add, toFinsupp_erase, toFinsupp_injective, toFinsupp_monomial
-/
theorem monomial_add_erase (p : R[X]) (n : Nat) : monomial n (coeff p n) + p.erase n = p := by
  apply toFinsupp_injective
  simp only [toFinsupp_add, toFinsupp_monomial, toFinsupp_erase]
  exact AddMonoidAlgebra.single_add_erase ..

/--
theorem `coeff_erase` / 定理 `coeff_erase`

English:
theorem coeff_erase
  given: (p : R[X]) (n i : Nat)
  proof: by
  rcases p with ⟨⟩
  simp only [erase_def, coeff]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]

中文:
定理 coeff_erase
  条件: (p : R[X]) (n i : 自然数)
  证明: by
  rcases p with ⟨⟩
  simp only [erase_def, coeff]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]

Depends on / 依赖: erase_def, ite_congr
-/
theorem coeff_erase (p : R[X]) (n i : Nat) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  rcases p with ⟨⟩
  simp only [erase_def, coeff]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]
/--
theorem `erase_zero` / 定理 `erase_zero`

English:
theorem erase_zero
  given: (n : Nat)
  statement: (0 : R[X]).erase n = 0
  proof: toFinsupp_injective by simp

@[simp]

中文:
定理 erase_zero
  条件: (n : 自然数)
  结论: (0 : R[X]).erase n = 0
  证明: toFinsupp_injective by simp

@[simp]

Depends on / 依赖: toFinsupp_injective
-/
theorem erase_zero (n : Nat) : (0 : R[X]).erase n = 0 :=
toFinsupp_injective by simp

@[simp]
/--
theorem `erase_monomial` / 定理 `erase_monomial`

English:
theorem erase_monomial
  given: {n : Nat} {a : R}
  statement: erase n (monomial n a) = 0
  proof: toFinsupp_injective by simp

@[simp]

中文:
定理 erase_monomial
  条件: {n : 自然数} {a : R}
  结论: erase n (monomial n a) = 0
  证明: toFinsupp_injective by simp

@[simp]

Depends on / 依赖: NonUnitalCommSemiring, NonUnitalCommSemiring.toNonUnitalNonAssocCommSemiring, toFinsupp_injective, toNonUnitalNonAssocCommSemiring
-/
theorem erase_monomial {n : Nat} {a : R} : erase n (monomial n a) = 0 :=
toFinsupp_injective by simp

@[simp]
/--
theorem `erase_same` / 定理 `erase_same`

English:
theorem erase_same
  given: (p : R[X]) (n : Nat)
  statement: coeff (p.erase n) n = 0
  proof: by simp [coeff_erase]

@[simp]

中文:
定理 erase_same
  条件: (p : R[X]) (n : 自然数)
  结论: coeff (p.erase n) n = 0
  证明: by simp [coeff_erase]

@[simp]

Depends on / 依赖: CommSemiring, CommSemiring.toNonAssocCommSemiring, coeff_erase, toNonAssocCommSemiring
-/
theorem erase_same (p : R[X]) (n : Nat) : coeff (p.erase n) n = 0 := by simp [coeff_erase]

@[simp]
/--
theorem `erase_ne` / 定理 `erase_ne`

English:
theorem erase_ne
  given: (p : R[X]) {n i : Nat} (h : i != n)
  statement: coeff (p.erase n) i = coeff p i
  proof: by
  simp [coeff_erase, h]

中文:
定理 erase_ne
  条件: (p : R[X]) {n i : 自然数} (h : i != n)
  结论: coeff (p.erase n) i = coeff p i
  证明: by
  simp [coeff_erase, h]

Depends on / 依赖: CommSemiring, CommSemiring.toNonUnitalCommSemiring, coeff_erase, toNonUnitalCommSemiring
-/
theorem erase_ne (p : R[X]) {n i : Nat} (h : i != n) : coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

section Update

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (p : R[X]) (n : Nat) (a : R)
  body: Polynomial.ofFinsupp (p.toFinsupp.update n a)

中文:
定义 update
  签名: (p : R[X]) (n : 自然数) (a : R)
  定义体: Polynomial.ofFinsupp (p.toFinsupp.update n a)

Depends on / 依赖: CommSemiring, CommSemiring.toCommMonoidWithZero, Polynomial, Polynomial.ofFinsupp, ofFinsupp, p.toFinsupp.update, toCommMonoidWithZero, toFinsupp, update
-/
def update (p : R[X]) (n : Nat) (a : R) : R[X] :=
  Polynomial.ofFinsupp (p.toFinsupp.update n a)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_update` / 定理 `coeff_update`

English:
theorem coeff_update
  given: (p : R[X]) (n : Nat) (a : R)
  proof: by ext; simp [coeff, update]

中文:
定理 coeff_update
  条件: (p : R[X]) (n : 自然数) (a : R)
  证明: by ext; simp [coeff, update]

Depends on / 依赖: update
-/
theorem coeff_update (p : R[X]) (n : Nat) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by ext; simp [coeff, update]

/--
theorem `coeff_update_apply` / 定理 `coeff_update_apply`

English:
theorem coeff_update_apply
  given: (p : R[X]) (n : Nat) (a : R) (i : Nat)
  proof: by
  rw [coeff_update]; rw [Function.update_apply]

@[simp]

中文:
定理 coeff_update_apply
  条件: (p : R[X]) (n : 自然数) (a : R) (i : 自然数)
  证明: by
  rw [coeff_update]; rw [Function.update_apply]

@[simp]

Depends on / 依赖: Function, Function.update_apply, coeff_update, update_apply
-/
theorem coeff_update_apply (p : R[X]) (n : Nat) (a : R) (i : Nat) :
    (p.update n a).coeff i = if i = n then a else p.coeff i := by
  rw [coeff_update]; rw [Function.update_apply]

@[simp]
/--
theorem `coeff_update_same` / 定理 `coeff_update_same`

English:
theorem coeff_update_same
  given: (p : R[X]) (n : Nat) (a : R)
  statement: (p.update n a).coeff n = a
  proof: by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

中文:
定理 coeff_update_same
  条件: (p : R[X]) (n : 自然数) (a : R)
  结论: (p.update n a).coeff n = a
  证明: by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

Depends on / 依赖: coeff_update_apply, if_pos, p.coeff_update_apply
-/
theorem coeff_update_same (p : R[X]) (n : Nat) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

/--
theorem `coeff_update_ne` / 定理 `coeff_update_ne`

English:
theorem coeff_update_ne
  given: (p : R[X]) {n i : Nat} (a : R) (h : i != n)
  proof: by rw [p.coeff_update_apply, if_neg h]

@[simp]

中文:
定理 coeff_update_ne
  条件: (p : R[X]) {n i : 自然数} (a : R) (h : i != n)
  证明: by rw [p.coeff_update_apply, if_neg h]

@[simp]

Depends on / 依赖: coeff_update_apply, if_neg, p.coeff_update_apply
-/
theorem coeff_update_ne (p : R[X]) {n i : Nat} (a : R) (h : i != n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
/--
theorem `update_zero_eq_erase` / 定理 `update_zero_eq_erase`

English:
theorem update_zero_eq_erase
  given: (p : R[X]) (n : Nat)
  statement: p.update n 0 = p.erase n
  proof: by
  ext
  rw [coeff_update_apply]; rw [coeff_erase]

中文:
定理 update_zero_eq_erase
  条件: (p : R[X]) (n : 自然数)
  结论: p.update n 0 = p.erase n
  证明: by
  ext
  rw [coeff_update_apply]; rw [coeff_erase]

Depends on / 依赖: coeff_erase, coeff_update_apply
-/
theorem update_zero_eq_erase (p : R[X]) (n : Nat) : p.update n 0 = p.erase n := by
  ext
  rw [coeff_update_apply]; rw [coeff_erase]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `support_update` / 定理 `support_update`

English:
theorem support_update
  given: (p : R[X]) (n : Nat) (a : R) [Decidable (a = 0)]
  proof: by
  classical simp [support, update, Finsupp.support_update]

中文:
定理 support_update
  条件: (p : R[X]) (n : 自然数) (a : R) [可判定 (a = 0)]
  证明: by
  classical simp [support, update, Finsupp.support_update]

Depends on / 依赖: Finsupp, Finsupp.support_update, classical, support, support_update, update
-/
theorem support_update (p : R[X]) (n : Nat) (a : R) [Decidable (a = 0)] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  classical simp [support, update, Finsupp.support_update]

/--
theorem `support_update_zero` / 定理 `support_update_zero`

English:
theorem support_update_zero
  given: (p : R[X]) (n : Nat)
  statement: support (p.update n 0) = p.support.erase n
  proof: by
  rw [update_zero_eq_erase]; rw [support_erase]

中文:
定理 support_update_zero
  条件: (p : R[X]) (n : 自然数)
  结论: support (p.update n 0) = p.support.erase n
  证明: by
  rw [update_zero_eq_erase]; rw [support_erase]

Depends on / 依赖: support_erase, update_zero_eq_erase
-/
theorem support_update_zero (p : R[X]) (n : Nat) : support (p.update n 0) = p.support.erase n := by
  rw [update_zero_eq_erase]; rw [support_erase]

/--
theorem `support_update_ne_zero` / 定理 `support_update_ne_zero`

English:
theorem support_update_ne_zero
  given: (p : R[X]) (n : Nat) {a : R} (ha : a != 0)
  proof: by classical rw [support_update, if_neg ha]

中文:
定理 support_update_ne_zero
  条件: (p : R[X]) (n : 自然数) {a : R} (ha : a != 0)
  证明: by classical rw [support_update, if_neg ha]

Depends on / 依赖: classical, if_neg, support_update
-/
theorem support_update_ne_zero (p : R[X]) (n : Nat) {a : R} (ha : a != 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end Update

/--
Definition of `coeffs` / `coeffs` 的定义

English:
definition coeffs
  signature: (p : R[X])
  body: letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support

@[simp]

中文:
定义 coeffs
  签名: (p : R[X])
  定义体: letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support

@[simp]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.image, p.coeff, p.support, support
-/
def coeffs (p : R[X]) : Finset R :=
  letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support

@[simp]
/--
theorem `coeffs_zero` / 定理 `coeffs_zero`

English:
theorem coeffs_zero
  statement: coeffs (0 : R[X]) = ∅
  proof: rfl

中文:
定理 coeffs_zero
  结论: coeffs (0 : R[X]) = ∅
  证明: rfl
-/
theorem coeffs_zero : coeffs (0 : R[X]) = ∅ :=
  rfl

/--
theorem `mem_coeffs_iff` / 定理 `mem_coeffs_iff`

English:
theorem mem_coeffs_iff
  given: {p : R[X]} {c : R}
  statement: c in p.coeffs ↔ exists n in p.support, c = p.coeff n
  proof: by
  simp [coeffs, eq_comm, (Finset.mem_image)]

中文:
定理 mem_coeffs_iff
  条件: {p : R[X]} {c : R}
  结论: c in p.coeffs ↔ 存在 n in p.support, c = p.coeff n
  证明: by
  simp [coeffs, eq_comm, (Finset.mem_image)]

Depends on / 依赖: Finset, Finset.mem_image, coeffs, eq_comm, mem_image
-/
theorem mem_coeffs_iff {p : R[X]} {c : R} : c in p.coeffs ↔ exists n in p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]

/--
theorem `coeffs_one` / 定理 `coeffs_one`

English:
theorem coeffs_one
  statement: coeffs (1 : R[X]) subseteq {1}
  proof: by
  simp_rw [coeffs, Finset.image_subset_iff]
  simp_all [coeff_one]

中文:
定理 coeffs_one
  结论: coeffs (1 : R[X]) subseteq {1}
  证明: by
  simp_rw [coeffs, Finset.image_subset_iff]
  simp_all [coeff_one]

Depends on / 依赖: Finset, Finset.image_subset_iff, coeff_one, coeffs, image_subset_iff, simp_rw
-/
theorem coeffs_one : coeffs (1 : R[X]) subseteq {1} := by
  simp_rw [coeffs, Finset.image_subset_iff]
  simp_all [coeff_one]

/--
theorem `coeff_mem_coeffs` / 定理 `coeff_mem_coeffs`

English:
theorem coeff_mem_coeffs
  given: {p : R[X]} {n : Nat} (h : p.coeff n != 0)
  statement: p.coeff n in p.coeffs
  proof: by
  simp only [coeffs, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

@[simp]

中文:
定理 coeff_mem_coeffs
  条件: {p : R[X]} {n : 自然数} (h : p.coeff n != 0)
  结论: p.coeff n in p.coeffs
  证明: by
  simp only [coeffs, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

@[simp]

Depends on / 依赖: Finset, Finset.mem_image, MulZeroClass, MulZeroClass.negZeroClass, NegZeroClass, coeffs, mem_image, mem_support_iff, negZeroClass
-/
theorem coeff_mem_coeffs {p : R[X]} {n : Nat} (h : p.coeff n != 0) : p.coeff n in p.coeffs := by
  simp only [coeffs, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

@[simp]
/--
theorem `coeffs_empty_iff` / 定理 `coeffs_empty_iff`

English:
theorem coeffs_empty_iff
  given: {p : R[X]}
  statement: coeffs p = ∅ ↔ p = 0
  proof: by
  refine ⟨?_, fun h => by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [mem_support_iff] at hn
  exact ⟨p.coeff n, coeff_mem_coeffs hn⟩

@[simp]

中文:
定理 coeffs_empty_iff
  条件: {p : R[X]}
  结论: coeffs p = ∅ ↔ p = 0
  证明: by
  refine ⟨?_, fun h => by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [mem_support_iff] at hn
  exact ⟨p.coeff n, coeff_mem_coeffs hn⟩

@[simp]

Depends on / 依赖: HasDistribNeg, NonUnitalNonAssocRing, NonUnitalNonAssocRing.toHasDistribNeg, coeff_mem_coeffs, contrapose, mem_support_iff, p.coeff, support_nonempty, toHasDistribNeg
-/
theorem coeffs_empty_iff {p : R[X]} : coeffs p = ∅ ↔ p = 0 := by
  refine ⟨?_, fun h => by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [mem_support_iff] at hn
  exact ⟨p.coeff n, coeff_mem_coeffs hn⟩

@[simp]
/--
theorem `coeffs_nonempty_iff` / 定理 `coeffs_nonempty_iff`

English:
theorem coeffs_nonempty_iff
  given: {p : R[X]}
  statement: p.coeffs.Nonempty ↔ p != 0
  proof: by
  simp [Finset.nonempty_iff_ne_empty]

中文:
定理 coeffs_nonempty_iff
  条件: {p : R[X]}
  结论: p.coeffs.非空 ↔ p != 0
  证明: by
  simp [Finset.nonempty_iff_ne_empty]

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, nonempty_iff_ne_empty
-/
theorem coeffs_nonempty_iff {p : R[X]} : p.coeffs.Nonempty ↔ p != 0 := by
  simp [Finset.nonempty_iff_ne_empty]

/--
theorem `coeffs_monomial` / 定理 `coeffs_monomial`

English:
theorem coeffs_monomial
  given: (n : Nat) {c : R} (hc : c != 0)
  statement: (monomial n c).coeffs = {c}
  proof: by
  rw [coeffs]; rw [support_monomial n hc]
  simp

中文:
定理 coeffs_monomial
  条件: (n : 自然数) {c : R} (hc : c != 0)
  结论: (monomial n c).coeffs = {c}
  证明: by
  rw [coeffs]; rw [support_monomial n hc]
  simp

Depends on / 依赖: coeffs, support_monomial
-/
theorem coeffs_monomial (n : Nat) {c : R} (hc : c != 0) : (monomial n c).coeffs = {c} := by
  rw [coeffs]; rw [support_monomial n hc]
  simp

end Semiring

section CommSemiring

variable [CommSemiring R]

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring R[X]
  body: fast_instance% { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

中文:
实例 commSemiring
  签名: : 交换半环 R[X]
  定义体: fast_instance% { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

Depends on / 依赖: Function, Function.Injective.commSemigroup, Injective, Polynomial, Polynomial.semiring, commSemigroup, fast_instance, semiring, toFinsupp, toFinsupp_injective, toFinsupp_mul, toSemiring
-/
instance commSemiring : CommSemiring R[X] :=
  fast_instance% { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

end CommSemiring

section Ring

variable [Ring R]

/--
Instance `instZSMul` / 实例 `instZSMul`

English:
instance instZSMul
  signature: : SMul Int R[X] where
  body: ⟨r • p.toFinsupp⟩

@[simp]

中文:
实例 instZSMul
  签名: : 标量乘法 整数 R[X] where
  定义体: ⟨r • p.toFinsupp⟩

@[simp]

Depends on / 依赖: p.toFinsupp, toFinsupp
-/
instance instZSMul : SMul Int R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

@[simp]
/--
theorem `ofFinsupp_zsmul` / 定理 `ofFinsupp_zsmul`

English:
theorem ofFinsupp_zsmul
  given: (a : Int) (b)
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_zsmul
  条件: (a : 整数) (b)
  证明: rfl

@[simp]
-/
theorem ofFinsupp_zsmul (a : Int) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
/--
theorem `toFinsupp_zsmul` / 定理 `toFinsupp_zsmul`

English:
theorem toFinsupp_zsmul
  given: (a : Int) (b : R[X])
  proof: rfl

中文:
定理 toFinsupp_zsmul
  条件: (a : 整数) (b : R[X])
  证明: rfl
-/
theorem toFinsupp_zsmul (a : Int) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast R[X] where intCast n
  body: ofFinsupp n

@[simp]

中文:
实例 inst整数Cast
  签名: : 整数嵌入 R[X] where intCast n
  定义体: ofFinsupp n

@[simp]

Depends on / 依赖: ofFinsupp
-/
instance instIntCast : IntCast R[X] where intCast n := ofFinsupp n

@[simp]
/--
theorem `ofFinsupp_intCast` / 定理 `ofFinsupp_intCast`

English:
theorem ofFinsupp_intCast
  given: (z : Int)
  statement: (⟨z⟩ : R[X]) = z
  proof: rfl

@[simp]

中文:
定理 ofFinsupp_intCast
  条件: (z : 整数)
  结论: (⟨z⟩ : R[X]) = z
  证明: rfl

@[simp]

Depends on / 依赖: NonUnitalRing, Ring.toNonUnitalRing, toNonUnitalRing
-/
theorem ofFinsupp_intCast (z : Int) : (⟨z⟩ : R[X]) = z := rfl

@[simp]
/--
theorem `toFinsupp_intCast` / 定理 `toFinsupp_intCast`

English:
theorem toFinsupp_intCast
  given: (z : Int)
  statement: (z : R[X]).toFinsupp = z
  proof: rfl

中文:
定理 toFinsupp_intCast
  条件: (z : 整数)
  结论: (z : R[X]).toFinsupp = z
  证明: rfl

Depends on / 依赖: NonAssocRing, Ring.toNonAssocRing, toNonAssocRing
-/
theorem toFinsupp_intCast (z : Int) : (z : R[X]).toFinsupp = z := rfl

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: : Ring R[X]
  body: fast_instance% Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ => toFinsupp_nsmul _ _)
      (fun _ _ => toFinsupp_zsmul _ _) toFinsupp_pow (fun _ => rfl) fun _ => rfl

@[simp]

中文:
实例 ring
  签名: : 环 R[X]
  定义体: fast_instance% Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ => toFinsupp_nsmul _ _)
      (fun _ _ => toFinsupp_zsmul _ _) toFinsupp_pow (fun _ => rfl) fun _ => rfl

@[simp]

Depends on / 依赖: Function, Function.Injective.ring, Injective, NonUnitalCommRing, NonUnitalCommRing.toNonUnitalCommSemiring, fast_instance, toFinsupp, toFinsupp_add, toFinsupp_injective, toFinsupp_mul, toFinsupp_neg, toFinsupp_nsmul, toFinsupp_one, toFinsupp_pow, toFinsupp_sub, toFinsupp_zero, toFinsupp_zsmul, toNonUnitalCommSemiring
-/
instance ring : Ring R[X] :=
  fast_instance% Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ => toFinsupp_nsmul _ _)
      (fun _ _ => toFinsupp_zsmul _ _) toFinsupp_pow (fun _ => rfl) fun _ => rfl

@[simp]
/--
theorem `coeff_neg` / 定理 `coeff_neg`

English:
theorem coeff_neg
  given: (p : R[X]) (n : Nat)
  statement: coeff (-p) n = -coeff p n
  proof: by simp [coeff]

@[simp]

中文:
定理 coeff_neg
  条件: (p : R[X]) (n : 自然数)
  结论: coeff (-p) n = -coeff p n
  证明: by simp [coeff]

@[simp]

Depends on / 依赖: CommRing, CommRing.toNonAssocCommRing, NonAssocCommRing, toNonAssocCommRing
-/
theorem coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -coeff p n := by simp [coeff]

@[simp]
/--
theorem `coeff_sub` / 定理 `coeff_sub`

English:
theorem coeff_sub
  given: (p q : R[X]) (n : Nat)
  statement: coeff (p - q) n = coeff p n - coeff q n
  proof: by
  simp [coeff, sub_eq_add_neg]

@[simp]

中文:
定理 coeff_sub
  条件: (p q : R[X]) (n : 自然数)
  结论: coeff (p - q) n = coeff p n - coeff q n
  证明: by
  simp [coeff, sub_eq_add_neg]

@[simp]

Depends on / 依赖: CommRing, CommRing.toCommSemiring, CommSemiring, sub_eq_add_neg, toCommSemiring
-/
theorem coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n = coeff p n - coeff q n := by
  simp [coeff, sub_eq_add_neg]

@[simp]
/--
theorem `monomial_neg` / 定理 `monomial_neg`

English:
theorem monomial_neg
  given: (n : Nat) (a : R)
  statement: monomial n (-a) = -monomial n a
  proof: by
  rw [eq_neg_iff_add_eq_zero]; rw [← map_add]; rw [neg_add_cancel]; rw [monomial_zero_right]

中文:
定理 monomial_neg
  条件: (n : 自然数) (a : R)
  结论: monomial n (-a) = -monomial n a
  证明: by
  rw [eq_neg_iff_add_eq_zero]; rw [← map_add]; rw [neg_add_cancel]; rw [monomial_zero_right]

Depends on / 依赖: CommRing, CommRing.toNonUnitalCommRing, NonUnitalCommRing, eq_neg_iff_add_eq_zero, map_add, monomial_zero_right, neg_add_cancel, toNonUnitalCommRing
-/
theorem monomial_neg (n : Nat) (a : R) : monomial n (-a) = -monomial n a := by
  rw [eq_neg_iff_add_eq_zero]; rw [← map_add]; rw [neg_add_cancel]; rw [monomial_zero_right]

/--
theorem `monomial_sub` / 定理 `monomial_sub`

English:
theorem monomial_sub
  given: (n : Nat)
  statement: monomial n (a - b) = monomial n a - monomial n b
  proof: by
  rw [sub_eq_add_neg]; rw [map_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 monomial_sub
  条件: (n : 自然数)
  结论: monomial n (a - b) = monomial n a - monomial n b
  证明: by
  rw [sub_eq_add_neg]; rw [map_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: CommRing, CommRing.toAddCommGroupWithOne, map_add, monomial_neg, sub_eq_add_neg, toAddCommGroupWithOne
-/
theorem monomial_sub (n : Nat) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg]; rw [map_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `support_neg` / 定理 `support_neg`

English:
theorem support_neg
  given: {p : R[X]}
  statement: (-p).support = p.support
  proof: by simp [support]

中文:
定理 support_neg
  条件: {p : R[X]}
  结论: (-p).support = p.support
  证明: by simp [support]

Depends on / 依赖: support, toAddEquivClass
-/
theorem support_neg {p : R[X]} : (-p).support = p.support := by simp [support]

/--
theorem `C_eq_intCast` / 定理 `C_eq_intCast`

English:
theorem C_eq_intCast
  given: (n : Int)
  statement: C (n : R) = n
  proof: by simp

中文:
定理 C_eq_intCast
  条件: (n : 整数)
  结论: C (n : R) = n
  证明: by simp

Depends on / 依赖: NonAssocSemiring, toRingHomClass
-/
theorem C_eq_intCast (n : Int) : C (n : R) = n := by simp

/--
theorem `C_neg` / 定理 `C_neg`

English:
theorem C_neg
  statement: C (-a) = -C a
  proof: map_neg C a

中文:
定理 C_neg
  结论: C (-a) = -C a
  证明: map_neg C a

Depends on / 依赖: NonUnitalNonAssocSemiring, map_neg, toNonUnitalRingHomClass
-/
theorem C_neg : C (-a) = -C a :=
  map_neg C a

/--
theorem `C_sub` / 定理 `C_sub`

English:
theorem C_sub
  statement: C (a - b) = C a - C b
  proof: map_sub C a b

中文:
定理 C_sub
  结论: C (a - b) = C a - C b
  证明: map_sub C a b

Depends on / 依赖: map_sub
-/
theorem C_sub : C (a - b) = C a - C b :=
  map_sub C a b

end Ring

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: [CommRing R]
  body: --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }

中文:
实例 commRing
  签名: [交换环 R]
  定义体: --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }
-/
instance commRing [CommRing R] : CommRing R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }

section Semiring

variable [Semiring R]

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Nontrivial R]
  body: by
  have h : Nontrivial R[Nat] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

@[simp]

中文:
实例 nontrivial
  签名: [非平凡 R]
  定义体: by
  have h : Nontrivial R[Nat] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

@[simp]

Depends on / 依赖: Nontrivial, exists_pair_ne, h.exists_pair_ne, infer_instance
-/
instance nontrivial [Nontrivial R] : Nontrivial R[X] := by
  have h : Nontrivial R[Nat] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

@[simp]
/--
theorem `X_ne_zero` / 定理 `X_ne_zero`

English:
theorem X_ne_zero
  given: [Nontrivial R]
  statement: (X : R[X]) != 0
  proof: mt (congr_arg fun p => coeff p 1) (by simp)

中文:
定理 X_ne_zero
  条件: [非平凡 R]
  结论: (X : R[X]) != 0
  证明: mt (congr_arg fun p => coeff p 1) (by simp)

Depends on / 依赖: congr_arg
-/
theorem X_ne_zero [Nontrivial R] : (X : R[X]) != 0 :=
  mt (congr_arg fun p => coeff p 1) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : NoZeroDivisors R[X]
  body: (toFinsuppIso R).injective.noZeroDivisors _ (map_zero _) (map_mul _)

中文:
实例 [无零因子
  签名: R] : 无零因子 R[X]
  定义体: (toFinsuppIso R).injective.noZeroDivisors _ (map_zero _) (map_mul _)

Depends on / 依赖: injective, injective.noZeroDivisors, map_mul, map_zero, noZeroDivisors, toFinsuppIso
-/
instance [NoZeroDivisors R] : NoZeroDivisors R[X] :=
  (toFinsuppIso R).injective.noZeroDivisors _ (map_zero _) (map_mul _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsLeftCancelMulZero R] : IsLeftCancelMulZero R[X]
  body: (toFinsuppIso R).injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

中文:
实例 [是消去加法
  签名: R] [是左消去MulZero R] : 是左消去MulZero R[X]
  定义体: (toFinsuppIso R).injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

Depends on / 依赖: injective, injective.isLeftCancelMulZero, isLeftCancelMulZero, map_mul, map_zero, toFinsuppIso
-/
instance [IsCancelAdd R] [IsLeftCancelMulZero R] : IsLeftCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsRightCancelMulZero R] : IsRightCancelMulZero R[X]
  body: (toFinsuppIso R).injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

中文:
实例 [是消去加法
  签名: R] [是右消去MulZero R] : 是右消去MulZero R[X]
  定义体: (toFinsuppIso R).injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

Depends on / 依赖: injective, injective.isRightCancelMulZero, isRightCancelMulZero, map_mul, map_zero, toFinsuppIso
-/
instance [IsCancelAdd R] [IsRightCancelMulZero R] : IsRightCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsCancelMulZero R] : IsCancelMulZero R[X] where

中文:
实例 [是消去加法
  签名: R] [是乘零消去 R] : 是乘零消去 R[X] where
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R[X] where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsDomain R] : IsDomain R[X] where

中文:
实例 [是消去加法
  签名: R] [是整环 R] : 是整环 R[X] where
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain R[X] where

/--
theorem `noZeroDivisors_iff` / 定理 `noZeroDivisors_iff`

English:
theorem noZeroDivisors_iff
  statement: NoZeroDivisors R[X] ↔ NoZeroDivisors R where
  proof: C_injective.noZeroDivisors _ C_0 fun _ _ => C_mul
  mpr _ := inferInstance

中文:
定理 noZeroDivisors_iff
  结论: 无零因子 R[X] ↔ 无零因子 R where
  证明: C_injective.noZeroDivisors _ C_0 fun _ _ => C_mul
  mpr _ := inferInstance

Depends on / 依赖: C_injective, C_injective.noZeroDivisors, C_mul, noZeroDivisors
-/
theorem noZeroDivisors_iff : NoZeroDivisors R[X] ↔ NoZeroDivisors R where
  mp _ := C_injective.noZeroDivisors _ C_0 fun _ _ => C_mul
  mpr _ := inferInstance

end Semiring

section DivisionSemiring
variable [DivisionSemiring R]

/--
lemma `nnqsmul_eq_C_mul` / 引理 `nnqsmul_eq_C_mul`

English:
lemma nnqsmul_eq_C_mul
  given: (q : Rat>=0) (f : R[X])
  statement: q • f = Polynomial.C (q : R) * f
  proof: by
  rw [← NNRat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

中文:
引理 nnqsmul_eq_C_mul
  条件: (q : 有理数>=0) (f : R[X])
  结论: q • f = 多项式.C (q : R) * f
  证明: by
  rw [← NNRat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

Depends on / 依赖: NNRat.smul_one_eq_cast, Polynomial, Polynomial.smul_C, smul_C, smul_one_eq_cast, smul_one_mul
-/
lemma nnqsmul_eq_C_mul (q : Rat>=0) (f : R[X]) : q • f = Polynomial.C (q : R) * f := by
  rw [← NNRat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

end DivisionSemiring

section DivisionRing

variable [DivisionRing R]

/--
theorem `qsmul_eq_C_mul` / 定理 `qsmul_eq_C_mul`

English:
theorem qsmul_eq_C_mul
  given: (a : Rat) (f : R[X])
  statement: a • f = Polynomial.C (a : R) * f
  proof: by
  rw [← Rat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

中文:
定理 qsmul_eq_C_mul
  条件: (a : 有理数) (f : R[X])
  结论: a • f = 多项式.C (a : R) * f
  证明: by
  rw [← Rat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

Depends on / 依赖: Polynomial, Polynomial.smul_C, Rat.smul_one_eq_cast, smul_C, smul_one_eq_cast, smul_one_mul
-/
theorem qsmul_eq_C_mul (a : Rat) (f : R[X]) : a • f = Polynomial.C (a : R) * f := by
  rw [← Rat.smul_one_eq_cast]; rw [← Polynomial.smul_C]; rw [C_1]; rw [smul_one_mul]

end DivisionRing

@[simp]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  given: [Semiring R]
  statement: Nontrivial R[X] ↔ Nontrivial R
  proof: ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

中文:
定理 nontrivial_iff
  条件: [半环 R]
  结论: 非平凡 R[X] ↔ 非平凡 R
  证明: ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

Depends on / 依赖: Nontrivial, Nontrivial.of_polynomial_ne, Polynomial, Polynomial.nontrivial, exists_pair_ne, nontrivial, of_polynomial_ne
-/
theorem nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R :=
  ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

/--
Definition of `ofMultiset` / `ofMultiset` 的定义

English:
definition ofMultiset
  signature: [CommRing R]
  body: (s.map (fun a => X - C a)).prod
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

中文:
定义 ofMultiset
  签名: [交换环 R]
  定义体: (s.map (fun a => X - C a)).prod
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp
-/
@[simps] def ofMultiset [CommRing R] : AddChar (Multiset R) R[X] where
  toFun s := (s.map (fun a => X - C a)).prod
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

section repr

variable [Semiring R]

/--
Instance `repr` / 实例 `repr`

English:
instance repr
  signature: [Repr R] [DecidableEq R]
  body: ⟨fun p prec =>
    let termPrecAndReprs : List (WithTop Nat × Lean.Format) :=
      List.map (fun
        | 0 => (max_prec, "C " ++ reprArg (coeff p 0))
        | 1 => if coeff p 1 = 1
          then (⊤, "X")
          else (70, "C " ++ reprArg (coeff p 1) ++ " * X")
        | n =>
          if coef

中文:
实例 repr
  签名: [Repr R] [DecidableEq R]
  定义体: ⟨fun p prec =>
    let termPrecAndReprs : List (WithTop Nat × Lean.Format) :=
      List.map (fun
        | 0 => (max_prec, "C " ++ reprArg (coeff p 0))
        | 1 => if coeff p 1 = 1
          then (⊤, "X")
          else (70, "C " ++ reprArg (coeff p 1) ++ " * X")
        | n =>
          if coef
-/
protected instance repr [Repr R] [DecidableEq R] : Repr R[X] :=
  ⟨fun p prec =>
    let termPrecAndReprs : List (WithTop Nat × Lean.Format) :=
      List.map (fun
        | 0 => (max_prec, "C " ++ reprArg (coeff p 0))
        | 1 => if coeff p 1 = 1
          then (⊤, "X")
          else (70, "C " ++ reprArg (coeff p 1) ++ " * X")
        | n =>
          if coeff p n = 1
          then (80, "X ^ " ++ Nat.repr n)
          else (70, "C " ++ reprArg (coeff p n) ++ " * X ^ " ++ Nat.repr n))
      p.support.sort
    match termPrecAndReprs with
    | [] => "0"
    | [(tprec, t)] => if prec >= tprec then Lean.Format.paren t else t
    | ts =>
      -- multiple terms, use `+` precedence
      (if prec >= 65 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep (ts.map Prod.snd) (" +" ++ Lean.Format.line)))⟩

end repr

end Polynomial
