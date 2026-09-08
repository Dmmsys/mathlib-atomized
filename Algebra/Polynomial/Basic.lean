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
`X * p = p * X`.  The relationship to `R[ℕ]` is through a structure
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
/-
**Polynomial** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Semiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial R` is the type of univariate polynomials over `R`,
denoted as `R[X]` within the `Polynomial` namespace.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`.
-/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/
  toFinsupp : AddMonoidAlgebra R ℕ

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset Module
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

/-
**Polynomial.forall_iff_forall_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：forall_iff_forall_finsupp (P : R[X] -> Prop) : (forall p, P p) ↔ forall q 
: R[Nat], P ⟨q⟩
参数：P : R[X] -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_iff_forall_finsupp (P : R[X] → Prop) :
    (∀ p, P p) ↔ ∀ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun h q ↦ h ⟨q⟩, fun h ⟨p⟩ ↦ h p⟩
/-
**Polynomial.exists_iff_exists_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_iff_exists_finsupp (P : R[X] -> Prop) : (exists p, P p) ↔ exists q 
: R[Nat], P ⟨q⟩
参数：P : R[X] -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_iff_exists_finsupp (P : R[X] → Prop) :
    (∃ p, P p) ↔ ∃ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ ↦ ⟨p, hp⟩, fun ⟨q, hq⟩ ↦ ⟨⟨q⟩, hq⟩⟩

@[simp]
/-
**Polynomial.eta** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by constructor

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero R[X] :=
  ⟨⟨0⟩⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One R[X] :=
  ⟨⟨1⟩⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance : Add R[X] :=
  ⟨fun ⟨a⟩ ⟨b⟩ ↦ ⟨a + b⟩⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance {R : Type u} [Ring R] : Neg R[X] :=
  ⟨fun ⟨a⟩ ↦ ⟨-a⟩⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u} [Ring R] : Sub R[X] :=
  ⟨fun a b ↦ a + -b⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance : Mul R[X] :=
  ⟨fun ⟨a⟩ ⟨b⟩ ↦ ⟨a * b⟩⟩
/-
**Polynomial.instNSMul** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instNSMul : SMul Nat R[X] where smul r p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNSMul : SMul ℕ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩
/-
**Polynomial.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S R[X] where
 smul r p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul r p := ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

-- to avoid a bug in the `ring` tactic
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 1) pow : Pow R[X] ℕ where pow p n := npowRec n p

@[simp]
/-
**Polynomial.ofFinsupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_zero : (⟨0⟩ : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.ofFinsupp_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_one : (⟨1⟩ : R[X]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_one : (⟨1⟩ : R[X]) = 1 :=
  rfl

@[simp]
/-
**Polynomial.ofFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ :=
  (rfl)

@[simp]
/-
**Polynomial.ofFinsupp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
  (rfl)

@[simp]
/-
**Polynomial.ofFinsupp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg]
  rfl

@[simp]
/-
**Polynomial.ofFinsupp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ :=
  (rfl)

@[simp]
/-
**Polynomial.ofFinsupp_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_nsmul (a : Nat) (b) : (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X])
参数：a : Nat；b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_nsmul (a : ℕ) (b) : (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
/-
**Polynomial.ofFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b) : (⟨a • b⟩ : R[
X]) = (a • ⟨b⟩ : R[X])
参数：a : S；b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[simp]
/-
**Polynomial.ofFinsupp_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_pow (a) (n : Nat) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n
参数：a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.ofFinsupp_mul`：ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ *
 ⟨b⟩
-/
theorem ofFinsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]
/-
**Polynomial.toFinsupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_zero : (0 : R[X]).toFinsupp = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_one : (1 : R[X]).toFinsupp = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp :=
  (rfl)

@[simp]
/-
**Polynomial.toFinsupp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFin
supp
参数：a : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp :=
  (rfl)

@[simp]
/-
**Polynomial.toFinsupp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) : (a - b).toFinsupp = a.t
oFinsupp - b.toFinsupp
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg]
  rfl

@[simp]
/-
**Polynomial.toFinsupp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp :=
  (rfl)

@[simp]
/-
**Polynomial.toFinsupp_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_nsmul (a : Nat) (b : R[X]) : (a • b).toFinsupp = a • b.toFinsupp
参数：a : Nat；b : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_nsmul (a : ℕ) (b : R[X]) : (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X]) : (a • b
).toFinsupp = a • b.toFinsupp
参数：a : S；b : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_pow (a : R[X]) (n : Nat) : (a ^ n).toFinsupp = a.toFinsupp ^ n
参数：a : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_pow`：ofFinsupp_pow (a) (n : Nat) : (⟨a ^ n⟩ : R[X])
 = ⟨a⟩ ^ n
-/
theorem toFinsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  rw [← ofFinsupp_pow]
/-
**Polynomial._root_.IsSMulRegular.polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSMulRegular.polynomial {S : Type*} [SMulZeroClass S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| coeff_injective <| ha.finsupp congr(($h).toFinsupp.coeff)
/-
**Polynomial.toFinsupp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_injective : Function.Injective (toFinsupp : R[X] -> AddMonoidAlg
ebra _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] → AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ ↦ congr_arg _

@[simp]
/-
**Polynomial.toFinsupp_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
-/
theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
/-
**Polynomial.toFinsupp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.toFinsupp_zero`：toFinsupp_zero : (0 : R[X]).toFinsupp = 0
· 使用定理 `Polynomial.toFinsupp_inj`：toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.t
oFinsupp ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
/-
**Polynomial.toFinsupp_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.toFinsupp_one`：toFinsupp_one : (1 : R[X]).toFinsupp = 1
· 使用定理 `Polynomial.toFinsupp_inj`：toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.t
oFinsupp ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

/-- A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`. -/
/-
**Polynomial.ofFinsupp_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…

--- 原说明 ---
A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`.
-/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
/-
**Polynomial.ofFinsupp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_zero`：ofFinsupp_zero : (⟨0⟩ : R[X]) = 0
· 使用定理 `Polynomial.ofFinsupp_inj`：ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a =
 b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

@[simp]
/-
**Polynomial.ofFinsupp_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_one`：ofFinsupp_one : (⟨1⟩ : R[X]) = 1
· 使用定理 `Polynomial.ofFinsupp_inj`：ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a =
 b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]
/-
**Polynomial.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：inhabited : Inhabited R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited R[X] :=
  ⟨0⟩
/-
**Polynomial.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instNatCast : NatCast R[X] where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast R[X] where natCast n := ofFinsupp n

@[simp]
/-
**Polynomial.ofFinsupp_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_natCast (n : Nat) : (⟨n⟩ : R[X]) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_natCast (n : ℕ) : (⟨n⟩ : R[X]) = n := rfl

@[simp]
/-
**Polynomial.toFinsupp_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_natCast (n : Nat) : (n : R[X]).toFinsupp = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_natCast (n : ℕ) : (n : R[X]).toFinsupp = n := rfl

@[simp]
/-
**Polynomial.ofFinsupp_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_ofNat (n : Nat) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n) := rfl

@[simp]
/-
**Polynomial.toFinsupp_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : R[X]).toFinsupp = o
fNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]).toFinsupp = ofNat(n) := rfl
/-
**Polynomial.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：semiring : Semiring R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring : Semiring R[X] :=
  fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ ↦ toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ ↦ rfl
/-
**Polynomial.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：distribSMul {S} [DistribSMul S R] : DistribSMul S R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul {S} [DistribSMul S R] : DistribSMul S R[X] :=
  fast_instance% Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul
/-
**Polynomial.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：distribMulAction {S} [Monoid S] [DistribMulAction S R] : DistribMulAction 
S R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction {S} [Monoid S] [DistribMulAction S R] : DistribMulAction S R[X] :=
  fast_instance% Function.Injective.distribMulAction
    ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul
/-
**Polynomial.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：faithfulSMul {S} [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R
[X] where eq_of_smul_eq_smul {_s₁ _s₂} h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `AddMonoidAlgebra.faithfulSMul`：∀ {R : Type u_1} {S : Type u_2} {M : Type
 u_3} [inst : Semiring S] [inst_1 : SMulZeroClass R S] [FaithfulSMul R S]   [Non
empty M], FaithfulS…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance faithfulSMul {S} [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul {_s₁ _s₂} h := eq_of_smul_eq_smul fun a : R[ℕ] ↦ congr(($(h ⟨a⟩)).toFinsupp)
/-
**Polynomial.module** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：module {S} [Semiring S] [Module S R] : Module S R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module {S} [Semiring S] [Module S R] : Module S R[X] :=
  fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul
/-
**Polynomial.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：smulCommClass {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommC
lass S₁ S₂ R] : SMulCommClass S₁ S₂ R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance smulCommClass {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
    SMulCommClass S₁ S₂ R[X] :=
  ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩
/-
**Polynomial.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：isScalarTower {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ 
R] [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X] :=
  ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩
/-
**Polynomial.isScalarTower_right** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：isScalarTower_right {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalar
Tower α K K] : IsScalarTower α K[X] K[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `AddMonoidAlgebra.isScalarTower_self`：∀ {R : Type u_1} (S : Type u_2) {M 
: Type u_3} [inst : Semiring S] [inst_1 : DistribSMul R S] [inst_2 : Add M]   [I
sScalarTower R S S], IsSc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower_right {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalarTower α K K] :
    IsScalarTower α K[X] K[X] :=
  ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩
/-
**Polynomial.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：isCentralScalar {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralS
calar S R] : IsCentralScalar S R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `AddMonoidAlgebra.isCentralScalar`：∀ {R : Type u_1} {M : Type u_4} {N : T
ype u_5} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2 : SMulZeroCl
ass Nᵐᵒᵖ R] [IsCentral…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isCentralScalar {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
    IsCentralScalar S R[X] :=
  ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [Semiring S] [Module S R] [IsTorsionFree S R] : IsTorsionFree S R[X] where
  isSMulRegular s hs := by
    rintro ⟨f⟩ ⟨g⟩ hfg; congr; apply hs.isSMulRegular; simpa using congr(($hfg).toFinsupp)
/-
**Polynomial.unique** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：unique [Subsingleton R] : Unique R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Polynomial.toFinsuppIso** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toFinsuppIso : R[X] ≃+* R[Nat] where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_mul`：toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp
 = a.toFinsupp * b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp

--- 原说明 ---
Ring isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` t
o polynomials.
-/
def toFinsuppIso : R[X] ≃+* R[ℕ] where
  toFun := toFinsupp
  invFun := ofFinsupp
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq R] : DecidableEq R[X] := (toFinsuppIso R).toEquiv.decidableEq

/-- Linear isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
/-
**Polynomial.toFinsuppIsoLinear** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toFinsuppIsoLinear : R[X] ≃ₗ[R] R[Nat] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` t
o polynomials.
-/
def toFinsuppIsoLinear : R[X] ≃ₗ[R] R[ℕ] where
  __ := toFinsuppIso R
  map_smul' _ _ := rfl

end AddMonoidAlgebra

/-
**Polynomial.ofFinsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι -> R[Nat]) : (⟨∑ i in s, f
 i⟩ : R[X]) = ∑ i in s, ⟨f i⟩
参数：s : Finset ι；f : ι -> R[Nat]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[ℕ]) :
    (⟨∑ i ∈ s, f i⟩ : R[X]) = ∑ i ∈ s, ⟨f i⟩ :=
  map_sum (toFinsuppIso R).symm f s
/-
**Polynomial.toFinsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι -> R[X]) : (∑ i in s, f i 
: R[X]).toFinsupp = ∑ i in s, (f i).toFinsupp
参数：s : Finset ι；f : ι -> R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i : R[X]).toFinsupp = ∑ i ∈ s, (f i).toFinsupp :=
  map_sum (toFinsuppIso R) f s

/-- The set of all `n` such that `X^n` has a non-zero coefficient. -/
/-
**Polynomial.support** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : Semiring R] → Polynomial R → Finset ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support : R[X] → Finset ℕ
  | ⟨p⟩ => p.coeff.support

@[simp]
/-
**Polynomial.support_ofFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_ofFinsupp (p) : support (⟨p⟩ : R[X]) = p.coeff.support
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : AddMono
idAlgebra R ℕ), { toFinsupp := p }.support = p.coeff.support
-/
theorem support_ofFinsupp (p) : support (⟨p⟩ : R[X]) = p.coeff.support := by rw [support]
/-
**Polynomial.support_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_toFinsupp (p : R[X]) : p.toFinsupp.coeff.support = p.support
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : AddMono
idAlgebra R ℕ), { toFinsupp := p }.support = p.coeff.support
-/
theorem support_toFinsupp (p : R[X]) : p.toFinsupp.coeff.support = p.support := by rw [support]

@[simp]
/-
**Polynomial.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_zero : (0 : R[X]).support = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zero : (0 : R[X]).support = ∅ :=
  rfl

@[simp]
/-
**Polynomial.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_eq_empty : p.support = ∅ ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [support]
/-
**Polynomial.support_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.support.Nonempty 
↔ p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.support_eq_empty`：support_eq_empty : p.support = ∅ ↔ p = 0
-/
@[simp] lemma support_nonempty : p.support.Nonempty ↔ p ≠ 0 :=
  Finset.nonempty_iff_ne_empty.trans support_eq_empty.not
/-
**Polynomial.card_support_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq_zero : #p.support = 0 ↔ p = 0
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
theorem card_support_eq_zero : #p.support = 0 ↔ p = 0 := by simp

/-- `monomial s a` is the monomial `a * X^s` -/
/-
**Polynomial.monomial** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：monomial (n : Nat) : R ->ₗ[R] R[X] where toFun t
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`monomial s a` is the monomial `a * X^s`
-/
def monomial (n : ℕ) : R →ₗ[R] R[X] where
  toFun t := ⟨.single n t⟩
  map_add' x y := by simp [← ofFinsupp_add]
  map_smul' r x := by simp [← ofFinsupp_smul]

@[simp]
/-
**Polynomial.toFinsupp_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_monomial (n : Nat) (r : R) : (monomial n r).toFinsupp = .single 
n r
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinsupp_monomial (n : ℕ) (r : R) : (monomial n r).toFinsupp = .single n r := by
  simp [monomial]

@[simp]
/-
**Polynomial.ofFinsupp_single** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_single (n : Nat) (r : R) : (⟨.single n r⟩ : R[X]) = monomial n r
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsupp_single (n : ℕ) (r : R) : (⟨.single n r⟩ : R[X]) = monomial n r := by
  simp [monomial]

@[simp]
/-
**Polynomial.monomial_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_zero_right (n : Nat) : monomial n (0 : R) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 :=
  (monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
/-
**Polynomial.monomial_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_zero_one : monomial 0 (1 : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl
/-
**Polynomial.monomial_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_mul_monomial (n m : Nat) (r s : R) : monomial n r * monomial m s 
= monomial (n + m) (r * s)
参数：n m : Nat；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_mul`：toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp
 = a.toFinsupp * b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_mul_monomial (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * s) :=
  toFinsupp_injective <| by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]
/-
**Polynomial.monomial_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_pow (n : Nat) (r : R) (k : Nat) : monomial n r ^ k = monomial (n 
* k) (r ^ k)
参数：n : Nat；r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r ^ k = monomial (n * k) (r ^ k) := by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]
/-
**Polynomial.smul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_monomial {S} [SMulZeroClass S R] (a : S) (n : Nat) (b : R) : a • mono
mial n b = monomial n (a • b)
参数：a : S；n : Nat；b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `AddMonoidAlgebra.smul_single`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {A : Type u_8} [inst_1 : SMulZeroClass A R] (a : A) (m : M) (r : R),  
 a • AddMonoidAlge…
-/
theorem smul_monomial {S} [SMulZeroClass S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  toFinsupp_injective <| AddMonoidAlgebra.smul_single _ _ _
/-
**Polynomial.monomial_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_injective (n : Nat) : Function.Injective (monomial n : R -> R[X])
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `AddMonoidAlgebra.single_right_injective`：∀ {R : Type u_1} {M : Type u_4}
 [inst : Semiring R] {m : M}, Function.Injective (AddMonoidAlgebra.single m)
-/
theorem monomial_injective (n : ℕ) : Function.Injective (monomial n : R → R[X]) :=
  (toFinsuppIso R).symm.injective.comp single_right_injective

@[simp]
/-
**Polynomial.monomial_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_eq_zero_iff (t : R) (n : Nat) : monomial n t = 0 ↔ t = 0
参数：t : R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `Polynomial.monomial_injective`：monomial_injective (n : Nat) : Function.I
njective (monomial n : R -> R[X])
-/
theorem monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)
/-
**Polynomial.monomial_eq_monomial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_eq_monomial_iff {m n : Nat} {a b : R} : monomial m a = monomial n
 b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.toFinsupp_inj`：toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.t
oFinsupp ↔ a = b
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `AddMonoidAlgebra.single_inj`：∀ {R : Type u_1} {M : Type u_4} [inst : Sem
iring R] {r₁ r₂ : R} {m₁ m₂ : M},   AddMonoidAlgebra.single m₁ r₁ = AddMonoidAlg
ebra.single m₂ r₂…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← toFinsupp_inj, toFinsupp_monomial, toFinsupp_monomial, single_inj]
/-
**Polynomial.support_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_add : (p + q).support subseteq p.support union q.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
-/
theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support] using! Finsupp.support_add

/-- `C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
/-
**Polynomial.C** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：C : R ->+* R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]
/-
**Polynomial.monomial_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_C (a : R) : (C a).toFinsupp = single 0 a
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_C (a : R) : (C a).toFinsupp = single 0 a :=
  rfl
/-
**Polynomial.C_0** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_0 : C (0 : R) = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_0 : C (0 : R) = 0 := by simp
/-
**Polynomial.C_1** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_1 : C (1 : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_1 : C (1 : R) = 1 :=
  rfl
/-
**Polynomial.C_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_ofNat (n : Nat) [n.AtLeastTwo] : C ofNat(n) = (ofNat(n) : R[X])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_ofNat (n : ℕ) [n.AtLeastTwo] : C ofNat(n) = (ofNat(n) : R[X]) :=
  rfl
/-
**Polynomial.C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mul : C (a * b) = C a * C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
-/
theorem C_mul : C (a * b) = C a * C b :=
  C.map_mul a b
/-
**Polynomial.C_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_add : C (a + b) = C a + C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
-/
theorem C_add : C (a + b) = C a + C b :=
  C.map_add a b

@[simp]
/-
**Polynomial.smul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • C r = C (s • r)
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.smul_monomial`：smul_monomial {S} [SMulZeroClass S R] (a : S) 
(n : Nat) (b : R) : a • monomial n b = monomial n (a • b)
-/
theorem smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r
/-
**Polynomial.C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_pow : C (a ^ n) = C a ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n
/-
**Polynomial.C_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem C_eq_natCast (n : ℕ) : C (n : R) = (n : R[X]) :=
  map_natCast C n

@[simp, grind =]
/-
**Polynomial.C_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mul_monomial : C a * monomial n b = monomial n (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp, grind =]
/-
**Polynomial.monomial_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_mul_C : monomial n a * C b = monomial n (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_mul_C : monomial n a * C b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

/-- `X` is the polynomial variable (aka indeterminate). -/
/-
**Polynomial.X** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：X : R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is the polynomial variable (aka indeterminate).
-/
def X : R[X] :=
  monomial 1 1
/-
**Polynomial.monomial_one_one_eq_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_one_one_eq_X : monomial 1 (1 : R) = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl
/-
**Polynomial.monomial_one_right_eq_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_one_right_eq_X_pow (n : Nat) : monomial n (1 : R) = X ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monomial_one_one_eq_X`：monomial_one_one_eq_X : monomial 1 (1 
: R) = X
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]
/-
**Polynomial.toFinsupp_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_X : X.toFinsupp = .single 1 (1 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_X : X.toFinsupp = .single 1 (1 : R) :=
  rfl
/-
**Polynomial.X_ne_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_ne_C [Nontrivial R] (a : R) : X != C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.monomial_eq_monomial_iff`：monomial_eq_monomial_iff {m n : Nat
} {a b : R} : monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0
-/
theorem X_ne_C [Nontrivial R] (a : R) : X ≠ C a := by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

set_option backward.isDefEq.respectTransparency false in
/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
/-
**Polynomial.X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_mul : X * p = p * X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidAlgebra.coeff_mul`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] [inst_1 : Add M] [inst_2 : DecidableEq M]   (x y : AddMonoidAlgebra R M)
 (m : M),   (x *…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
`X` commutes with everything, even when the coefficients are noncommutative.
-/
theorem X_mul : X * p = p * X := by
  rcases p with ⟨⟩
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.coeff_mul, add_comm]
/-
**Polynomial.X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem X_pow_mul {n : ℕ} : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ]

/-- Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `Polynomial.X_mul`. -/
@[simp]
/-
**Polynomial.X_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_mul_C (r : R) : X * C r = C r * X
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X

--- 原说明 ---
Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `Polynomial.X_mul`.
-/
theorem X_mul_C (r : R) : X * C r = C r * X :=
  X_mul

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`. -/
@[simp]
/-
**Polynomial.X_pow_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mul_C (r : R) (n : Nat) : X ^ n * C r = C r * X ^ n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n

--- 原说明 ---
Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`.
-/
theorem X_pow_mul_C (r : R) (n : ℕ) : X ^ n * C r = C r * X ^ n :=
  X_pow_mul
/-
**Polynomial.X_pow_mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mul_assoc {n : Nat} : p * X ^ n * q = p * q * X ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem X_pow_mul_assoc {n : ℕ} : p * X ^ n * q = p * q * X ^ n := by
  rw [mul_assoc, X_pow_mul, ← mul_assoc]

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`. -/
@[simp]
/-
**Polynomial.X_pow_mul_assoc_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mul_assoc_C {n : Nat} (r : R) : p * X ^ n * C r = p * C r * X ^ n
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_mul_assoc`：X_pow_mul_assoc {n : Nat} : p * X ^ n * q = 
p * q * X ^ n

--- 原说明 ---
Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`.
-/
theorem X_pow_mul_assoc_C {n : ℕ} (r : R) : p * X ^ n * C r = p * C r * X ^ n :=
  X_pow_mul_assoc
/-
**Polynomial.commute_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：commute_X (p : R[X]) : Commute X p
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
-/
theorem commute_X (p : R[X]) : Commute X p :=
  X_mul
/-
**Polynomial.commute_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：commute_X_pow (p : R[X]) (n : Nat) : Commute (X ^ n) p
参数：p : R[X]；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
-/
theorem commute_X_pow (p : R[X]) (n : ℕ) : Commute (X ^ n) p :=
  X_pow_mul

@[simp]
/-
**Polynomial.monomial_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_mul_X (n : Nat) (r : R) : monomial n r * X = monomial (n + 1) r
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X.eq_1`：∀ {R : Type u} [inst : Semiring R], Polynomial.X = (P
olynomial.monomial 1) 1
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [X, monomial_mul_monomial, mul_one]

@[simp]
/-
**Polynomial.monomial_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_mul_X_pow (n : Nat) (r : R) (k : Nat) : monomial n r * X ^ k = mo
nomial (n + k) r
参数：n : Nat；r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Polynomial.monomial_mul_X`：monomial_mul_X (n : Nat) (r : R) : monomial n
 r * X = monomial (n + 1) r
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) :
    monomial n r * X ^ k = monomial (n + k) r := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]
/-
**Polynomial.X_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_mul_monomial (n : Nat) (r : R) : X * monomial n r = monomial (n + 1) r
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.monomial_mul_X`：monomial_mul_X (n : Nat) (r : R) : monomial n
 r * X = monomial (n + 1) r
-/
theorem X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n + 1) r := by
  rw [X_mul, monomial_mul_X]

@[simp]
/-
**Polynomial.X_pow_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mul_monomial (k n : Nat) (r : R) : X ^ k * monomial n r = monomial (
n + k) r
参数：k n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
· 使用定理 `Polynomial.monomial_mul_X_pow`：monomial_mul_X_pow (n : Nat) (r : R) (k :
 Nat) : monomial n r * X ^ k = monomial (n + k) r
-/
theorem X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n + k) r := by
  rw [X_pow_mul, monomial_mul_X_pow]

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
/-
**Polynomial.coeff** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : Semiring R] → Polynomial R → ℕ → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`.
-/
def coeff : R[X] → ℕ → R
  | ⟨p⟩ => p.coeff

@[simp]
/-
**Polynomial.coeff_ofFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p.coeff
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : AddMonoid
Algebra R ℕ), { toFinsupp := p }.coeff = ⇑p.coeff
-/
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p.coeff := by rw [coeff]
/-
**Polynomial.coeff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_injective : Injective (coeff : R[X] -> Nat -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…
-/
theorem coeff_injective : Injective (coeff : R[X] → ℕ → R) := by rintro ⟨p⟩ ⟨q⟩; simp [coeff]

@[simp]
/-
**Polynomial.coeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_inj : p.coeff = q.coeff ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.coeff_injective`：coeff_injective : Injective (coeff : R[X] ->
 Nat -> R)
-/
theorem coeff_inj : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff
/-
**Polynomial.toFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_apply (f : R[X]) (i) : f.toFinsupp.coeff i = f.coeff i
参数：f : R[X]；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toFinsupp_apply (f : R[X]) (i) : f.toFinsupp.coeff i = f.coeff i := by cases f; rfl
/-
**Polynomial.finite_range_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：finite_range_coeff (f : R[X]) : (Set.range f.coeff).Finite
参数：f : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.finite_range`：finite_range (f : α ->₀ M) : (Set.range f).Finite
-/
theorem finite_range_coeff (f : R[X]) : (Set.range f.coeff).Finite :=
  Finsupp.finite_range _
/-
**Polynomial.coeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_monomial : coeff (monomial n a) m = if n = m then a else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 := by
  simp [coeff, Finsupp.single_apply]

@[simp]
/-
**Polynomial.coeff_monomial_same** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_monomial_same (n : Nat) (c : R) : (monomial n c).coeff n = c
参数：n : Nat；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_monomial_same (n : ℕ) (c : R) : (monomial n c).coeff n = c :=
  Finsupp.single_eq_same
/-
**Polynomial.coeff_monomial_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_monomial_of_ne {m n : Nat} (c : R) (h : m != n) : (monomial n c).coe
ff m = 0
参数：c : R；h : m != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
-/
theorem coeff_monomial_of_ne {m n : ℕ} (c : R) (h : m ≠ n) : (monomial n c).coeff m = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
/-
**Polynomial.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero (n : ℕ) : coeff (0 : R[X]) n = 0 :=
  rfl

@[aesop simp]
/-
**Polynomial.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 0 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_one {n : ℕ} : coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]
/-
**Polynomial.coeff_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_one_zero : coeff (1 : R[X]) 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_one_zero : coeff (1 : R[X]) 0 = 1 := by
  simp [coeff_one]

@[simp]
/-
**Polynomial.coeff_X_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_X_one : coeff (X : R[X]) 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_X_one : coeff (X : R[X]) 1 = 1 :=
  coeff_monomial

@[simp]
/-
**Polynomial.coeff_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_X_zero : coeff (X : R[X]) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_X_zero : coeff (X : R[X]) 0 = 0 :=
  coeff_monomial

@[simp]
/-
**Polynomial.coeff_monomial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

@[aesop simp]
/-
**Polynomial.coeff_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 :=
  coeff_monomial
/-
**Polynomial.coeff_X_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_X_of_ne_one {n : Nat} (hn : n != 1) : coeff (X : R[X]) n = 0
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X`：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 
0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : R[X]) n = 0 := by
  rw [coeff_X, if_neg hn.symm]

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/-
**Polynomial.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_support_iff : n in p.support ↔ p.coeff n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.support_ofFinsupp`：support_ofFinsupp (p) : support (⟨p⟩ : R[X
]) = p.coeff.support
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  rcases p with ⟨⟩
  simp
/-
**Polynomial.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0
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
theorem notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

@[aesop simp]
/-
**Polynomial.coeff_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_C : coeff (C a) n = ite (n = 0) a 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert! coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]
/-
**Polynomial.coeff_C_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_C_zero : coeff (C a) 0 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial
/-
**Polynomial.coeff_C_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_C_of_ne_zero (h : n != 0) : (C a).coeff n = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_C_of_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_C_ne_zero := coeff_C_of_ne_zero

@[simp]
/-
**Polynomial.coeff_C_succ** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n + 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
/-
**Polynomial.coeff_natCast_ite** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0 := by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[simp]
/-
**Polynomial.coeff_ofNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_ofNat_zero (a : Nat) [a.AtLeastTwo] : coeff (ofNat(a) : R[X]) 0 = of
Nat(a)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
-/
theorem coeff_ofNat_zero (a : ℕ) [a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) 0 = ofNat(a) :=
  coeff_monomial

@[simp]
/-
**Polynomial.coeff_ofNat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_ofNat_succ (a n : Nat) [h : a.AtLeastTwo] : coeff (ofNat(a) : R[X]) 
(n + 1) = 0
参数：a n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_natCast_ite`：coeff_natCast_ite : (Nat.cast m : R[X]).co
eff n = ite (n = 0) m 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_ofNat_succ (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]
/-
**Polynomial.C_mul_X_pow_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {a : R} [inst : Semiring R] {n : ℕ}, Polynomial.C a * Polyn
omial.X ^ n = (Polynomial.monomial n) a
参数：Polynomial.monomial n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial, mul_one]

@[simp high]
/-
**Polynomial.toFinsupp_C_mul_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_C_mul_X_pow (a : R) (n : Nat) : (C a * X ^ n).toFinsupp = .singl
e n a
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
-/
lemma toFinsupp_C_mul_X_pow (a : R) (n : ℕ) : (C a * X ^ n).toFinsupp = .single n a := by
  rw [C_mul_X_pow_eq_monomial, toFinsupp_monomial]
/-
**Polynomial.C_mul_X_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mul_X_eq_monomial : C a * X = monomial 1 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem C_mul_X_eq_monomial : C a * X = monomial 1 a := by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]
/-
**Polynomial.toFinsupp_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_C_mul_X (a : R) : (C a * X).toFinsupp = .single 1 a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial : C a * X = monomial
 1 a
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
-/
theorem toFinsupp_C_mul_X (a : R) : (C a * X).toFinsupp = .single 1 a := by
  rw [C_mul_X_eq_monomial, toFinsupp_monomial]

@[grind inj]
/-
**Polynomial.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_injective : Injective (C : R -> R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monomial_injective`：monomial_injective (n : Nat) : Function.I
njective (monomial n : R -> R[X])
-/
theorem C_injective : Injective (C : R → R[X]) :=
  monomial_injective 0

@[simp]
/-
**Polynomial.C_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_inj : C a = C b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
-/
theorem C_inj : C a = C b ↔ a = b :=
  C_injective.eq_iff

@[simp]
/-
**Polynomial.C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_eq_zero : C a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  C_injective.eq_iff' (map_zero C)
/-
**Polynomial.C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_ne_zero : C a != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
-/
theorem C_ne_zero : C a ≠ 0 ↔ a ≠ 0 :=
  C_eq_zero.not
/-
**Polynomial.subsingleton_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R :=
  ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩
/-
**Polynomial.Nontrivial.of_polynomial_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.N
ontrivial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, p ≠ q → Nontrivia
l R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R :=
  (subsingleton_or_nontrivial R).resolve_left fun _hI ↦ h <| Subsingleton.elim _ _
/-
**Polynomial.forall_eq_iff_forall_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：forall_eq_iff_forall_eq : (forall f g : R[X], f = g) ↔ forall a b : R, a =
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.subsingleton_iff_subsingleton`：subsingleton_iff_subsingleton 
: Subsingleton R[X] ↔ Subsingleton R
-/
theorem forall_eq_iff_forall_eq : (∀ f g : R[X], f = g) ↔ ∀ a b : R, a = b := by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n = coeff q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨f⟩
  rcases q with ⟨g⟩
  simpa [coeff] using! DFunLike.ext_iff (f := f.coeff) (g := g.coeff)

@[ext]
/-
**Polynomial.ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
-/
theorem ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
  ext_iff.2

set_option backward.isDefEq.respectTransparency false in
/-- Monomials generate the additive monoid of polynomials. -/
/-
**Polynomial.addSubmonoid_closure_setOfPred_eq_monomial** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：addSubmonoid_closure_setOfPred_eq_monomial : AddSubmonoid.closure { p : R[
X] | exists n a, p = monomial n a } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.map_equiv_top`：∀ {N : Type u_2} [inst : AddZeroClass N] {M 
: Type u_5} [inst_1 : AddZeroClass M] (f : M ≃+ N), AddSubmonoid.map f ⊤ = ⊤
· 使用定理 `AddMonoidAlgebra.addSubmonoidClosure_single`：∀ {R : Type u_1} {M : Type 
u_4} [inst : Semiring R],   AddSubmonoid.closure {x | ∃ m r, x = AddMonoidAlgebr
a.single m r} = ⊤
· 使用定理 `AddMonoidHom.map_mclosure`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZe
roClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [
mc : AddMonoidH…
· 使用定理 `AddSubmonoid.closure_mono`：∀ {M : Type u_1} [inst : AddZeroClass M] ⦃s t
 : Set M⦄, s ⊆ t → AddSubmonoid.closure s ≤ AddSubmonoid.closure t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Polynomial.ofFinsupp_single`：ofFinsupp_single (n : Nat) (r : R) : (⟨.sin
gle n r⟩ : R[X]) = monomial n r

--- 原说明 ---
Monomials generate the additive monoid of polynomials.
-/
theorem addSubmonoid_closure_setOfPred_eq_monomial :
    AddSubmonoid.closure { p : R[X] | ∃ n a, p = monomial n a } = ⊤ := by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv, ← addSubmonoidClosure_single,
    AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

@[deprecated (since := "2026-07-09")]
alias addSubmonoid_closure_setOf_eq_monomial := addSubmonoid_closure_setOfPred_eq_monomial

@[ext high]
/-
**Polynomial.addHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：addHom_ext {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M} (h : forall n a
, f (monomial n a) = g (monomial n a)) : f = g
参数：h : forall n a, f (monomial n a) = g (monomial n a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.eq_of_eqOn_denseM`：∀ {M : Type u_1} {N : Type u_2} [inst : 
AddZeroClass M] [inst_1 : AddZeroClass N] {s : Set M},   AddSubmonoid.closure s 
= ⊤ → ∀ {f g : M →+ …
· 使用定理 `Polynomial.addSubmonoid_closure_setOfPred_eq_monomial`：addSubmonoid_clos
ure_setOfPred_eq_monomial : AddSubmonoid.closure { p : R[X] | exists n a, p = mo
nomial n a } = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOfPred_eq_monomial <| by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]
/-
**Polynomial.addHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：addHom_ext' {M : Type*} [AddZeroClass M] {f g : R[X] ->+ M} (h : forall n,
 f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = 
g
参数：h : forall n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddM
onoidHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f g : R[
X] ->+ M} (h : forall n a, f (monomial n a) = g (monomial n a)) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem addHom_ext' {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  addHom_ext fun n ↦ DFunLike.congr_fun (h n)

@[ext high]
/-
**Polynomial.lhom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] ->ₗ[R] M}
 (h : forall n, f.comp (monomial n) = g.comp (monomial n)) : f = g
参数：h : forall n, f.comp (monomial n) = g.comp (monomial n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `Polynomial.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f g : R[
X] ->+ M} (h : forall n a, f (monomial n a) = g (monomial n a)) : f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] →ₗ[R] M}
    (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext fun n ↦ LinearMap.congr_fun (h n)

-- this has the same content as the subsingleton
/-
**Polynomial.eq_zero_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0
参数：h : (0 : R) = (1 : R)；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Fewnomials

@[simp]
/-
**Polynomial.support_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_monomial (n) {a : R} (h : a != 0) : (monomial n a).support = singl
eton n
参数：n；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_single`：ofFinsupp_single (n : Nat) (r : R) : (⟨.sin
gle n r⟩ : R[X]) = monomial n r
· 使用定理 `Polynomial.support.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : AddMono
idAlgebra R ℕ), { toFinsupp := p }.support = p.coeff.support
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
-/
theorem support_monomial (n) {a : R} (h : a ≠ 0) : (monomial n a).support = singleton n := by
  rw [← ofFinsupp_single, support]; exact Finsupp.support_single _ h
/-
**Polynomial.support_monomial_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_monomial_subset (n) (a : R) : (monomial n a).support subseteq sing
leton n
参数：n；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_single`：ofFinsupp_single (n : Nat) (r : R) : (⟨.sin
gle n r⟩ : R[X]) = monomial n r
· 使用定理 `Polynomial.support.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : AddMono
idAlgebra R ℕ), { toFinsupp := p }.support = p.coeff.support
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
theorem support_monomial_subset (n) (a : R) : (monomial n a).support ⊆ singleton n := by
  rw [← ofFinsupp_single, support]
  exact Finsupp.support_single_subset

@[deprecated (since := "2026-06-09")] alias support_monomial' := support_monomial_subset

@[simp]
/-
**Polynomial.support_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C {a : R} (h : a != 0) : (C a).support = singleton 0
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
-/
theorem support_C {a : R} (h : a ≠ 0) : (C a).support = singleton 0 :=
  support_monomial 0 h
/-
**Polynomial.support_C_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C_subset (a : R) : (C a).support subseteq singleton 0
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.support_monomial_subset`：support_monomial_subset (n) (a : R) 
: (monomial n a).support subseteq singleton n
-/
theorem support_C_subset (a : R) : (C a).support ⊆ singleton 0 :=
  support_monomial_subset 0 a

@[simp]
/-
**Polynomial.support_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C_mul_X {c : R} (h : c != 0) : Polynomial.support (C c * X) = sing
leton 1
参数：h : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial : C a * X = monomial
 1 a
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
-/
theorem support_C_mul_X {c : R} (h : c ≠ 0) : Polynomial.support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]
/-
**Polynomial.support_C_mul_X_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C_mul_X_subset (c : R) : Polynomial.support (C c * X) subseteq sin
gleton 1
参数：c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial : C a * X = monomial
 1 a
· 使用定理 `Polynomial.support_monomial_subset`：support_monomial_subset (n) (a : R) 
: (monomial n a).support subseteq singleton n
-/
theorem support_C_mul_X_subset (c : R) : Polynomial.support (C c * X) ⊆ singleton 1 := by
  simpa only [C_mul_X_eq_monomial] using support_monomial_subset 1 c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X' := support_C_mul_X_subset

@[simp]
/-
**Polynomial.support_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C_mul_X_pow (n : Nat) {c : R} (h : c != 0) : Polynomial.support (C
 c * X ^ n) = singleton n
参数：n : Nat；h : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
-/
theorem support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) :
    Polynomial.support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]
/-
**Polynomial.support_C_mul_X_pow_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_C_mul_X_pow_subset (n : Nat) (c : R) : Polynomial.support (C c * X
 ^ n) subseteq singleton n
参数：n : Nat；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.support_monomial_subset`：support_monomial_subset (n) (a : R) 
: (monomial n a).support subseteq singleton n
-/
theorem support_C_mul_X_pow_subset (n : ℕ) (c : R) :
    Polynomial.support (C c * X ^ n) ⊆ singleton n := by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial_subset n c

@[deprecated (since := "2026-06-09")] alias support_C_mul_X_pow' := support_C_mul_X_pow_subset

open Finset
/-
**Polynomial.support_binomial_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_binomial_subset (k m : Nat) (x y : R) : Polynomial.support (C x * 
X ^ k + C y * X ^ m) subseteq {k, m}
参数：k m : Nat；x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.support_add`：support_add : (p + q).support subseteq p.support
 union q.support
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Polynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset (n : N
at) (c : R) : Polynomial.support (C c * X ^ n) subseteq singleton n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem support_binomial_subset (k m : ℕ) (x y : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

@[deprecated (since := "2026-06-09")] alias support_binomial' := support_binomial_subset
/-
**Polynomial.support_trinomial_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_trinomial_subset (k m n : Nat) (x y z : R) : Polynomial.support (C
 x * X ^ k + C y * X ^ m + C z * X ^ n) subseteq {k, m, n}
参数：k m n : Nat；x y z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.support_add`：support_add : (p + q).support subseteq p.support
 union q.support
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Polynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset (n : N
at) (c : R) : Polynomial.support (C c * X ^ n) subseteq singleton n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem support_trinomial_subset (k m n : ℕ) (x y z : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
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

/-
**Polynomial.X_pow_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monomial_one_right_eq_X_pow`：monomial_one_right_eq_X_pow (n :
 Nat) : monomial n (1 : R) = X ^ n
-/
theorem X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R) :=
  (monomial_one_right_eq_X_pow n).symm

@[simp high]
/-
**Polynomial.toFinsupp_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_X_pow (n : Nat) : (X ^ n).toFinsupp = .single n (1 : R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
-/
theorem toFinsupp_X_pow (n : ℕ) : (X ^ n).toFinsupp = .single n (1 : R) := by
  rw [X_pow_eq_monomial, toFinsupp_monomial]
/-
**Polynomial.smul_X_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.smul_monomial`：smul_monomial {S} [SMulZeroClass S R] (a : S) 
(n : Nat) (b : R) : a • monomial n b = monomial n (a • b)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R) := by
  rw [X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]

@[simp]
/-
**Polynomial.support_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_X_pow [Nontrivial R] (n : Nat) : (X ^ n : R[X]).support = singleto
n n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
theorem support_X_pow [Nontrivial R] (n : ℕ) : (X ^ n : R[X]).support = singleton n := by
  convert! support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n
/-
**Polynomial.support_X_empty** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅
参数：H : (1 : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X.eq_1`：∀ {R : Type u} [inst : Semiring R], Polynomial.X = (P
olynomial.monomial 1) 1
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `Polynomial.support_zero`：support_zero : (0 : R[X]).support = ∅
-/
theorem support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

@[simp]
/-
**Polynomial.support_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_X [Nontrivial R] : (X : R[X]).support = singleton 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.support_X_pow`：support_X_pow [Nontrivial R] (n : Nat) : (X ^ 
n : R[X]).support = singleton n
-/
theorem support_X [Nontrivial R] : (X : R[X]).support = singleton 1 := by
  rw [← pow_one X, support_X_pow 1]
/-
**Polynomial.monomial_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_left_inj {a : R} (ha : a != 0) {i j : Nat} : monomial i a = monom
ial j a ↔ i = j
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} :
    monomial i a = monomial j a ↔ i = j := by
  simp [monomial_eq_monomial_iff, ha]
/-
**Polynomial.binomial_eq_binomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：binomial_eq_binomial {k l m n : Nat} {u v : R} (hu : u != 0) (hv : v != 0)
 : C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔ k = m ∧ l = n ∨ u = v
 ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n
参数：hu : u != 0；hv : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
    C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n := by
  simp [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, single_add_single_inj, *]
/-
**Polynomial.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natCast_mul (n : Nat) (p : R[X]) : (n : R[X]) * p = n • p
参数：n : Nat；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
theorem natCast_mul (n : ℕ) (p : R[X]) : (n : R[X]) * p = n • p :=
  (nsmul_eq_mul _ _).symm

/-- Summing the values of a function applied to the coefficients of a polynomial -/
/-
**Polynomial.sum** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S) : S
参数：p : R[X]；f : Nat -> R -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Summing the values of a function applied to the coefficients of a polynomial
-/
def sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) : S :=
  ∑ n ∈ p.support, f n (p.coeff n)
/-
**Polynomial.sum_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : Nat -> R -> S) : p.s
um f = ∑ n in p.support, f n (p.coeff n)
参数：p : R[X]；f : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) :=
  rfl
/-
**Polynomial.sum_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : Nat -> R ->
 S) (hf : forall i, f i 0 = 0) {s : Finset Nat} (hs : p.support subseteq s) : p.
sum f = ∑ n in s, f n (p.coeff n)
参数：f : Nat -> R -> S；hf : forall i, f i 0 = 0；hs : p.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
-/
theorem sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) {s : Finset ℕ} (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

/-- Expressing the product of two polynomials as a double sum. -/
/-
**Polynomial.mul_eq_sum_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_eq_sum_sum : p * q = ∑ i in p.support, q.sum fun j a => (monomial (i +
 j)) (p.coeff i * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.toFinsupp_sum`：toFinsupp_sum {ι : Type*} (s : Finset ι) (f : 
ι -> R[X]) : (∑ i in s, f i : R[X]).toFinsupp = ∑ i in s, (f i).toFinsupp
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.toFinsupp_mul`：toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp
 = a.toFinsupp * b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `AddMonoidAlgebra.mul_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Add M] (x y : AddMonoidAlgebra R M),   x * y = x.coeff.sum fun m
₁ r₁ => y.coef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expressing the product of two polynomials as a double sum.
-/
theorem mul_eq_sum_sum :
    p * q = ∑ i ∈ p.support, q.sum fun j a ↦ (monomial (i + j)) (p.coeff i * a) := by
  apply toFinsupp_injective
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]
/-
**Polynomial.sum_zero_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_zero_index {S : Type*} [AddCommMonoid S] (f : Nat -> R -> S) : (0 : R[
X]).sum f = 0
参数：f : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_zero_index {S : Type*} [AddCommMonoid S] (f : ℕ → R → S) : (0 : R[X]).sum f = 0 := by
  simp [sum]

@[simp]
/-
**Polynomial.sum_monomial_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_monomial_index {S : Type*} [AddCommMonoid S] {n : Nat} (a : R) (f : Na
t -> R -> S) (hf : f n 0 = 0) : (monomial n a : R[X]).sum f = f n a
参数：a : R；f : Nat -> R -> S；hf : f n 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem sum_monomial_index {S : Type*} [AddCommMonoid S] {n : ℕ} (a : R) (f : ℕ → R → S)
    (hf : f n 0 = 0) : (monomial n a : R[X]).sum f = f n a :=
  Finsupp.sum_single_index hf

@[simp]
/-
**Polynomial.sum_C_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_C_index {a} {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0) 
: (C a).sum f = f 0 a
参数：h : f 0 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.sum_monomial_index`：sum_monomial_index {S : Type*} [AddCommMo
noid S] {n : Nat} (a : R) (f : Nat -> R -> S) (hf : f n 0 = 0) : (monomial n a :
 R[X]).sum f = f n …
-/
theorem sum_C_index {a} {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
    (C a).sum f = f 0 a :=
  sum_monomial_index a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp]
/-
**Polynomial.sum_X_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_X_index {S : Type*} [AddCommMonoid S] {f : Nat -> R -> S} (hf : f 1 0 
= 0) : (X : R[X]).sum f = f 1 1
参数：hf : f 1 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.sum_monomial_index`：sum_monomial_index {S : Type*} [AddCommMo
noid S] {n : Nat} (a : R) (f : Nat -> R -> S) (hf : f n 0 = 0) : (monomial n a :
 R[X]).sum f = f n …
-/
theorem sum_X_index {S : Type*} [AddCommMonoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (X : R[X]).sum f = f 1 1 :=
  sum_monomial_index 1 f hf
/-
**Polynomial.sum_add_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_add_index {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : Nat -> R -> 
S) (hf : forall i, f i 0 = 0) (h_add : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + 
f a b₂) : (p + q).sum f = p.sum f + q.sum f
参数：p q : R[X]；f : Nat -> R -> S；hf : forall i, f i 0 = 0；h_add : forall a b₁ b₂,
 f a (b₁ + b₂) = f a b₁ + f a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
-/
theorem sum_add_index {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ from rfl]
  exact Finsupp.sum_add_index (fun i _ ↦ hf i) (fun a _ b₁ b₂ ↦ h_add a b₁ b₂)

/-- See also `Polynomial.sum_add`. -/
@[simp]
/-
**Polynomial.sum_add'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S) : 
p.sum (f + g) = p.sum f + p.sum g
参数：p : R[X]；f g : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `Polynomial.sum_add`.
-/
theorem sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [sum_def, Finset.sum_add_distrib]

/-- See also `Polynomial.sum_add'`. -/
@[simp]
/-
**Polynomial.sum_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : Nat -> R -> S) : (
p.sum fun n x => f n x + g n x) = p.sum f + p.sum g
参数：p : R[X]；f g : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.sum_add'`：sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (
f g : Nat -> R -> S) : p.sum (f + g) = p.sum f + p.sum g

--- 原说明 ---
See also `Polynomial.sum_add'`.
-/
theorem sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

/-- See also `Polynomial.sum_smul_index'` for a version using `smul` on the RHS. -/
/-
**Polynomial.sum_smul_index** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_smul_index {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : Nat -
> R -> S) (hf : forall i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b *
 a)
参数：p : R[X]；b : R；f : Nat -> R -> S；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_smul_index`：sum_smul_index [MulZeroClass R] [AddCommMonoid M
] {g : α ->₀ R} {b : R} {h : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).s
um h = g.sum…

--- 原说明 ---
See also `Polynomial.sum_smul_index'` for a version using `smul` on the RHS.
-/
theorem sum_smul_index {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a ↦ f n (b * a) :=
  Finsupp.sum_smul_index hf

/-- See also `Polynomial.sum_smul_index` for a version using multiplication on the RHS. -/
/-
**Polynomial.sum_smul_index'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X
]) (b : T) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) : (b • p).sum f = p.su
m fun n a => f n (b • a)
参数：p : R[X]；b : T；f : Nat -> R -> S；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…

--- 原说明 ---
See also `Polynomial.sum_smul_index` for a version using multiplication on the R
HS.
-/
theorem sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
    (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a ↦ f n (b • a) :=
  Finsupp.sum_smul_index' hf
/-
**Polynomial.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} {T : Type u_2} [inst_1 :
 AddCommMonoid S] [inst_2 : DistribSMul T S]   (p : Polynomial R) (b : T) (f : ℕ
 → R → S), b • p.sum f = p.sum fun n a => b • f n a
参数：p : Polynomial R；b : T；f : ℕ → R → S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
-/
protected theorem smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a ↦ b • f n a :=
  Finsupp.smul_sum

@[simp]
/-
**Polynomial.sum_monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] (p : Polynomial R), (p.sum fun n a => (
Polynomial.monomial n) a) = p
参数：p : Polynomial R；p.sum fun n a => (Polynomial.monomial n) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ofFinsupp_sum`：ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : 
ι -> R[Nat]) : (⟨∑ i in s, f i⟩ : R[X]) = ∑ i in s, ⟨f i⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.sum_coeff_single`：∀ {R : Type u_1} {M : Type u_4} [inst
 : Semiring R] (f : AddMonoidAlgebra R M), f.coeff.sum AddMonoidAlgebra.single =
 f
-/
theorem sum_monomial_eq : ∀ p : R[X], (p.sum fun n a ↦ monomial n a) = p
  | ⟨_p⟩ => (ofFinsupp_sum _ _).symm.trans (congr_arg _ <| sum_coeff_single _)
/-
**Polynomial.sum_C_mul_X_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a => C a * X ^ n) = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a ↦ C a * X ^ n) = p := by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]
/-
**Polynomial.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {motive : Polynomial R → Prop} (p : Pol
ynomial R),   (∀ (a : R), motive (Polynomial.C a)) →     (∀ (p q : Polynomial R)
, motive p → motive q → motive (p + q)) →       (∀ (n : ℕ) (a : R),           mo
tive (Polynomial.C a * Polynomial.X ^ n) → motive (Polynomial.C a * Polynomial.X
 ^ (n + 1))) →         motive p
参数：p : Polynomial R；∀ (a : R), motive (Polynomial.C a)；∀ (p q : Polynomial R), m
otive p → motive q → motive (p + q)；∀ (n : ℕ) (a : R),           motive (Polynom
ial.C a * Polynomial.X ^ n) → motive (Polynomial.C a * Polynomial.X ^ (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Polynomial.sum_C_mul_X_pow_eq`：sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fu
n n a => C a * X ^ n) = p
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
-/
protected theorem induction_on {motive : R[X] → Prop} (p : R[X]) (C : ∀ a, motive (C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (monomial : ∀ (n : ℕ) (a : R),
      motive (Polynomial.C a * X ^ n) → motive (Polynomial.C a * X ^ (n + 1))) : motive p := by
  have A : ∀ {n : ℕ} {a}, motive (Polynomial.C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact C a
    | succ n ih => exact monomial _ _ ih
  have B : ∀ s : Finset ℕ, motive (s.sum fun n : ℕ ↦ Polynomial.C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert! C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (support p)

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
/-
**Polynomial.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {motive : Polynomial R → Prop} (p : Pol
ynomial R),   (∀ (p q : Polynomial R), motive p → motive q → motive (p + q)) →  
   (∀ (n : ℕ) (a : R), motive ((Polynomial.monomial n) a)) → motive p
参数：p : Polynomial R；∀ (p q : Polynomial R), motive p → motive q → motive (p + q)
；∀ (n : ℕ) (a : R), motive ((Polynomial.monomial n) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a

--- 原说明 ---
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
protected theorem induction_on' {motive : R[X] → Prop} (p : R[X])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (monomial : ∀ (n : ℕ) (a : R), motive (monomial n a)) : motive p :=
  Polynomial.induction_on p (monomial 0) add fun n a _h ↦
    by rw [C_mul_X_pow_eq_monomial]; exact monomial _ _

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
irreducible_def erase (n : ℕ) : R[X] → R[X]
  | ⟨p⟩ => ⟨p.erase n⟩

@[simp]
/-
**Polynomial.toFinsupp_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_erase (p : R[X]) (n : Nat) : toFinsupp (p.erase n) = p.toFinsupp
.erase n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.erase_def`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ) (x : 
Polynomial R),   Polynomial.erase n x =     match x with     | { toFinsupp := p 
} => { toF…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinsupp_erase (p : R[X]) (n : ℕ) : toFinsupp (p.erase n) = p.toFinsupp.erase n := by
  simp only [erase_def]

@[simp]
/-
**Polynomial.ofFinsupp_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_erase (p : R[Nat]) (n : Nat) : (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X
]).erase n
参数：p : R[Nat]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.erase_def`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ) (x : 
Polynomial R),   Polynomial.erase n x =     match x with     | { toFinsupp := p 
} => { toF…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsupp_erase (p : R[ℕ]) (n : ℕ) :
    (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X]).erase n := by
  simp only [erase_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Polynomial.support_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_erase (p : R[X]) (n : Nat) : support (p.erase n) = (support p).era
se n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_erase`：toFinsupp_erase (p : R[X]) (n : Nat) : toFin
supp (p.erase n) = p.toFinsupp.erase n
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_erase (p : R[X]) (n : ℕ) : support (p.erase n) = (support p).erase n := by
  simp [support]
/-
**Polynomial.monomial_add_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_add_erase (p : R[X]) (n : Nat) : monomial n (coeff p n) + p.erase
 n = p
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `Polynomial.toFinsupp_erase`：toFinsupp_erase (p : R[X]) (n : Nat) : toFin
supp (p.erase n) = p.toFinsupp.erase n
· 使用定理 `AddMonoidAlgebra.single_add_erase`：∀ {R : Type u_1} {M : Type u_4} [inst
 : Semiring R] (m : M) (x : AddMonoidAlgebra R M),   AddMonoidAlgebra.single m (
x.coeff m) + AddMonoidA…
-/
theorem monomial_add_erase (p : R[X]) (n : ℕ) : monomial n (coeff p n) + p.erase n = p := by
  apply toFinsupp_injective
  simp only [toFinsupp_add, toFinsupp_monomial, toFinsupp_erase]
  exact AddMonoidAlgebra.single_add_erase ..
/-
**Polynomial.coeff_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_erase (p : R[X]) (n i : Nat) : (p.erase n).coeff i = if i = n then 0
 else p.coeff i
参数：p : R[X]；n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.erase_def`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ) (x : 
Polynomial R),   Polynomial.erase n x =     match x with     | { toFinsupp := p 
} => { toF…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem coeff_erase (p : R[X]) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  rcases p with ⟨⟩
  simp only [erase_def, coeff]
  exact ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

@[simp]
/-
**Polynomial.erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：erase_zero (n : Nat) : (0 : R[X]).erase n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_erase`：toFinsupp_erase (p : R[X]) (n : Nat) : toFin
supp (p.erase n) = p.toFinsupp.erase n
· 使用定理 `AddMonoidAlgebra.erase_zero`：∀ {R : Type u_1} {M : Type u_4} [inst : Sem
iring R] (m : M), AddMonoidAlgebra.erase m 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 :=
  toFinsupp_injective <| by simp

@[simp]
/-
**Polynomial.erase_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：erase_monomial {n : Nat} {a : R} : erase n (monomial n a) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.toFinsupp_injective`：toFinsupp_injective : Function.Injective
 (toFinsupp : R[X] -> AddMonoidAlgebra _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toFinsupp_erase`：toFinsupp_erase (p : R[X]) (n : Nat) : toFin
supp (p.erase n) = p.toFinsupp.erase n
· 使用定理 `Polynomial.toFinsupp_monomial`：toFinsupp_monomial (n : Nat) (r : R) : (m
onomial n r).toFinsupp = .single n r
· 使用定理 `AddMonoidAlgebra.erase_single`：∀ {R : Type u_1} {M : Type u_4} [inst : S
emiring R] (m : M) (r : R),   AddMonoidAlgebra.erase m (AddMonoidAlgebra.single 
m r) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
  toFinsupp_injective <| by simp

@[simp]
/-
**Polynomial.erase_same** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：erase_same (p : R[X]) (n : Nat) : coeff (p.erase n) n = 0
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_erase`：coeff_erase (p : R[X]) (n i : Nat) : (p.erase n)
.coeff i = if i = n then 0 else p.coeff i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_same (p : R[X]) (n : ℕ) : coeff (p.erase n) n = 0 := by simp [coeff_erase]

@[simp]
/-
**Polynomial.erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：erase_ne (p : R[X]) {n i : Nat} (h : i != n) : coeff (p.erase n) i = coeff
 p i
参数：p : R[X]；h : i != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_erase`：coeff_erase (p : R[X]) (n i : Nat) : (p.erase n)
.coeff i = if i = n then 0 else p.coeff i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_ne (p : R[X]) {n i : ℕ} (h : i ≠ n) : coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

section Update

/-- Replace the coefficient of a `p : R[X]` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`. -/
/-
**Polynomial.update** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：update (p : R[X]) (n : Nat) (a : R) : R[X]
参数：p : R[X]；n : Nat；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the coefficient of a `p : R[X]` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`.
-/
def update (p : R[X]) (n : ℕ) (a : R) : R[X] :=
  Polynomial.ofFinsupp (p.toFinsupp.update n a)

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.coeff_update** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_update (p : R[X]) (n : Nat) (a : R) : (p.update n a).coeff = Functio
n.update p.coeff n a
参数：p : R[X]；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_update (p : R[X]) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by ext; simp [coeff, update]
/-
**Polynomial.coeff_update_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_update_apply (p : R[X]) (n : Nat) (a : R) (i : Nat) : (p.update n a)
.coeff i = if i = n then a else p.coeff i
参数：p : R[X]；n : Nat；a : R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_update`：coeff_update (p : R[X]) (n : Nat) (a : R) : (p.
update n a).coeff = Function.update p.coeff n a
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
-/
theorem coeff_update_apply (p : R[X]) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i := by
  rw [coeff_update, Function.update_apply]

@[simp]
/-
**Polynomial.coeff_update_same** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_update_same (p : R[X]) (n : Nat) (a : R) : (p.update n a).coeff n = 
a
参数：p : R[X]；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_update_apply`：coeff_update_apply (p : R[X]) (n : Nat) (
a : R) (i : Nat) : (p.update n a).coeff i = if i = n then a else p.coeff i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_update_same (p : R[X]) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, if_pos rfl]
/-
**Polynomial.coeff_update_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_update_ne (p : R[X]) {n i : Nat} (a : R) (h : i != n) : (p.update n 
a).coeff i = p.coeff i
参数：p : R[X]；a : R；h : i != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_update_apply`：coeff_update_apply (p : R[X]) (n : Nat) (
a : R) (i : Nat) : (p.update n a).coeff i = if i = n then a else p.coeff i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_update_ne (p : R[X]) {n i : ℕ} (a : R) (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
/-
**Polynomial.update_zero_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：update_zero_eq_erase (p : R[X]) (n : Nat) : p.update n 0 = p.erase n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_update_apply`：coeff_update_apply (p : R[X]) (n : Nat) (
a : R) (i : Nat) : (p.update n a).coeff i = if i = n then a else p.coeff i
· 使用定理 `Polynomial.coeff_erase`：coeff_erase (p : R[X]) (n i : Nat) : (p.erase n)
.coeff i = if i = n then 0 else p.coeff i
-/
theorem update_zero_eq_erase (p : R[X]) (n : ℕ) : p.update n 0 = p.erase n := by
  ext
  rw [coeff_update_apply, coeff_erase]

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.support_update** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_update (p : R[X]) (n : Nat) (a : R) [Decidable (a = 0)] : support 
(p.update n a) = if a = 0 then p.support.erase n else insert n p.support
参数：p : R[X]；n : Nat；a : R；a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_update`：support_update [DecidableEq α] [DecidableEq M] :
 support (f.update a b) = if b = 0 then f.support.erase a else insert a f.suppor
t
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem support_update (p : R[X]) (n : ℕ) (a : R) [Decidable (a = 0)] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  classical simp [support, update, Finsupp.support_update]
/-
**Polynomial.support_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_update_zero (p : R[X]) (n : Nat) : support (p.update n 0) = p.supp
ort.erase n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.update_zero_eq_erase`：update_zero_eq_erase (p : R[X]) (n : Na
t) : p.update n 0 = p.erase n
· 使用定理 `Polynomial.support_erase`：support_erase (p : R[X]) (n : Nat) : support (
p.erase n) = (support p).erase n
-/
theorem support_update_zero (p : R[X]) (n : ℕ) : support (p.update n 0) = p.support.erase n := by
  rw [update_zero_eq_erase, support_erase]
/-
**Polynomial.support_update_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_update_ne_zero (p : R[X]) (n : Nat) {a : R} (ha : a != 0) : suppor
t (p.update n a) = insert n p.support
参数：p : R[X]；n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_update`：support_update (p : R[X]) (n : Nat) (a : R) [
Decidable (a = 0)] : support (p.update n a) = if a = 0 then p.support.erase n el
se insert n p.s…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end Update

/-- The finset of nonzero coefficients of a polynomial. -/
/-
**Polynomial.coeffs** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：coeffs (p : R[X]) : Finset R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of nonzero coefficients of a polynomial.
-/
def coeffs (p : R[X]) : Finset R :=
  letI := Classical.decEq R
  Finset.image (fun n ↦ p.coeff n) p.support

@[simp]
/-
**Polynomial.coeffs_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeffs_zero : coeffs (0 : R[X]) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeffs_zero : coeffs (0 : R[X]) = ∅ :=
  rfl
/-
**Polynomial.mem_coeffs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_coeffs_iff {p : R[X]} {c : R} : c in p.coeffs ↔ exists n in p.support,
 c = p.coeff n
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
theorem mem_coeffs_iff {p : R[X]} {c : R} : c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]
/-
**Polynomial.coeffs_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeffs_one : coeffs (1 : R[X]) subseteq {1}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeffs_one : coeffs (1 : R[X]) ⊆ {1} := by
  simp_rw [coeffs, Finset.image_subset_iff]
  simp_all [coeff_one]
/-
**Polynomial.coeff_mem_coeffs** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mem_coeffs {p : R[X]} {n : Nat} (h : p.coeff n != 0) : p.coeff n in 
p.coeffs
参数：h : p.coeff n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem coeff_mem_coeffs {p : R[X]} {n : ℕ} (h : p.coeff n ≠ 0) : p.coeff n ∈ p.coeffs := by
  simp only [coeffs, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

@[simp]
/-
**Polynomial.coeffs_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeffs_empty_iff {p : R[X]} : coeffs p = ∅ ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `Polynomial.coeff_mem_coeffs`：coeff_mem_coeffs {p : R[X]} {n : Nat} (h : 
p.coeff n != 0) : p.coeff n in p.coeffs
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeffs_empty_iff {p : R[X]} : coeffs p = ∅ ↔ p = 0 := by
  refine ⟨?_, fun h ↦ by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [mem_support_iff] at hn
  exact ⟨p.coeff n, coeff_mem_coeffs hn⟩

@[simp]
/-
**Polynomial.coeffs_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeffs_nonempty_iff {p : R[X]} : p.coeffs.Nonempty ↔ p != 0
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
theorem coeffs_nonempty_iff {p : R[X]} : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]
/-
**Polynomial.coeffs_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeffs_monomial (n : Nat) {c : R} (hc : c != 0) : (monomial n c).coeffs = 
{c}
参数：n : Nat；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeffs.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.coeffs = Finset.image (fun n => p.coeff n) p.support
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeffs_monomial (n : ℕ) {c : R} (hc : c ≠ 0) : (monomial n c).coeffs = {c} := by
  rw [coeffs, support_monomial n hc]
  simp

end Semiring

section CommSemiring

variable [CommSemiring R]

/-
**Polynomial.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：commSemiring : CommSemiring R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring : CommSemiring R[X] :=
  fast_instance% { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

end CommSemiring

section Ring

variable [Ring R]

/-
**Polynomial.instZSMul** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instZSMul : SMul Int R[X] where smul r p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZSMul : SMul ℤ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

@[simp]
/-
**Polynomial.ofFinsupp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_zsmul (a : Int) (b) : (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X])
参数：a : Int；b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_zsmul (a : ℤ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
/-
**Polynomial.toFinsupp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_zsmul (a : Int) (b : R[X]) : (a • b).toFinsupp = a • b.toFinsupp
参数：a : Int；b : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_zsmul (a : ℤ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl
/-
**Polynomial.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instIntCast : IntCast R[X] where intCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast R[X] where intCast n := ofFinsupp n

@[simp]
/-
**Polynomial.ofFinsupp_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFinsupp_intCast (z : Int) : (⟨z⟩ : R[X]) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinsupp_intCast (z : ℤ) : (⟨z⟩ : R[X]) = z := rfl

@[simp]
/-
**Polynomial.toFinsupp_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFinsupp_intCast (z : Int) : (z : R[X]).toFinsupp = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_intCast (z : ℤ) : (z : R[X]).toFinsupp = z := rfl
/-
**Polynomial.ring** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：ring : Ring R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring : Ring R[X] :=
  fast_instance% Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ ↦ toFinsupp_nsmul _ _)
      (fun _ _ ↦ toFinsupp_zsmul _ _) toFinsupp_pow (fun _ ↦ rfl) fun _ ↦ rfl

@[simp]
/-
**Polynomial.coeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -coeff p n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n := by simp [coeff]

@[simp]
/-
**Polynomial.coeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n = coeff p n - coeff q n
参数：p q : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.toFinsupp_add`：toFinsupp_add (a b : R[X]) : (a + b).toFinsupp
 = a.toFinsupp + b.toFinsupp
· 使用定理 `Polynomial.toFinsupp_neg`：toFinsupp_neg {R : Type u} [Ring R] (a : R[X])
 : (-a).toFinsupp = -a.toFinsupp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  simp [coeff, sub_eq_add_neg]

@[simp]
/-
**Polynomial.monomial_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_neg (n : Nat) (a : R) : monomial n (-a) = -monomial n a
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
-/
theorem monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -monomial n a := by
  rw [eq_neg_iff_add_eq_zero, ← map_add, neg_add_cancel, monomial_zero_right]
/-
**Polynomial.monomial_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_sub (n : Nat) : monomial n (a - b) = monomial n a - monomial n b
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.monomial_neg`：monomial_neg (n : Nat) (a : R) : monomial n (-a
) = -monomial n a
-/
theorem monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, map_add, monomial_neg, sub_eq_add_neg]

@[simp]
/-
**Polynomial.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_neg {p : R[X]} : (-p).support = p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_neg {p : R[X]} : (-p).support = p.support := by simp [support]
/-
**Polynomial.C_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_eq_intCast (n : Int) : C (n : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_eq_intCast (n : ℤ) : C (n : R) = n := by simp
/-
**Polynomial.C_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_neg : C (-a) = -C a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem C_neg : C (-a) = -C a :=
  map_neg C a
/-
**Polynomial.C_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_sub : C (a - b) = C a - C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem C_sub : C (a - b) = C a - C b :=
  map_sub C a b

end Ring

/-
**Polynomial.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：commRing [CommRing R] : CommRing R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing [CommRing R] : CommRing R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }

section Semiring

variable [Semiring R]

/-
**Polynomial.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：nontrivial [Nontrivial R] : Nontrivial R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.instNontrivial`：∀ {R : Type u_1} {M : Type u_4} [inst :
 Semiring R] [Nontrivial R] [Nonempty M], Nontrivial (AddMonoidAlgebra R M)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance nontrivial [Nontrivial R] : Nontrivial R[X] := by
  have h : Nontrivial R[ℕ] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

@[simp]
/-
**Polynomial.X_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_ne_zero [Nontrivial R] : (X : R[X]) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem X_ne_zero [Nontrivial R] : (X : R[X]) ≠ 0 :=
  mt (congr_arg fun p ↦ coeff p 1) (by simp)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors R] : NoZeroDivisors R[X] :=
  (toFinsuppIso R).injective.noZeroDivisors _ (map_zero _) (map_mul _)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsLeftCancelMulZero R] : IsLeftCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsRightCancelMulZero R] : IsRightCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R[X] where
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain R[X] where

/-- See also `Polynomial.isCancelMulZero_iff`: in order for `R[X]` to have cancellative
multiplication (stronger than `NoZeroDivisors` in general, but equivalent if `R` is a ring),
`R` must have both cancellative multiplication and cancellative addition. -/
/-
**Polynomial.noZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：noZeroDivisors_iff : NoZeroDivisors R[X] ↔ NoZeroDivisors R where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)

--- 原说明 ---
See also `Polynomial.isCancelMulZero_iff`: in order for `R[X]` to have cancellat
ive
multiplication (stronger than `NoZeroDivisors` in general, but equivalent if `R`
 is a ring),
`R` must have both cancellative multiplication and cancellative addition.
-/
theorem noZeroDivisors_iff : NoZeroDivisors R[X] ↔ NoZeroDivisors R where
  mp _ := C_injective.noZeroDivisors _ C_0 fun _ _ ↦ C_mul
  mpr _ := inferInstance

end Semiring

section DivisionSemiring
variable [DivisionSemiring R]

/-
**Polynomial.nnqsmul_eq_C_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nnqsmul_eq_C_mul (q : Rat>=0) (f : R[X]) : q • f = Polynomial.C (q : R) * 
f
参数：q : Rat>=0；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.smul_one_eq_cast`：∀ (K : Type u_1) [inst : DivisionSemiring K] (q 
: ℚ≥0), q • 1 = ↑q
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
-/
lemma nnqsmul_eq_C_mul (q : ℚ≥0) (f : R[X]) : q • f = Polynomial.C (q : R) * f := by
  rw [← NNRat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionSemiring

section DivisionRing

variable [DivisionRing R]

/-
**Polynomial.qsmul_eq_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：qsmul_eq_C_mul (a : Rat) (f : R[X]) : a • f = Polynomial.C (a : R) * f
参数：a : Rat；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.smul_one_eq_cast`：smul_one_eq_cast (A : Type*) [DivisionRing A] (m :
 Rat) : m • (1 : A) = ↑m
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
-/
theorem qsmul_eq_C_mul (a : ℚ) (f : R[X]) : a • f = Polynomial.C (a : R) * f := by
  rw [← Rat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionRing

@[simp]
/-
**Polynomial.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
-/
theorem nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R :=
  ⟨fun h ↦
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h ↦ @Polynomial.nontrivial _ _ h⟩

/-- The map sending a collection of roots into a polynomial, as a morphism. -/
/-
**Polynomial.ofMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : CommRing R] → AddChar (Multiset R) (Polynomial R)
参数：Multiset R；Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map sending a collection of roots into a polynomial, as a morphism.
-/
@[simps] def ofMultiset [CommRing R] : AddChar (Multiset R) R[X] where
  toFun s := (s.map (fun a ↦ X - C a)).prod
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

section repr

variable [Semiring R]

/-
**Polynomial.repr** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : Semiring R] → [Repr R] → [DecidableEq R] → Repr (Po
lynomial R)
参数：Polynomial R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
-/
protected instance repr [Repr R] [DecidableEq R] : Repr R[X] :=
  ⟨fun p prec ↦
    let termPrecAndReprs : List (WithTop ℕ × Lean.Format) :=
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
    | [(tprec, t)] => if prec ≥ tprec then Lean.Format.paren t else t
    | ts =>
      -- multiple terms, use `+` precedence
      (if prec ≥ 65 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep (ts.map Prod.snd) (" +" ++ Lean.Format.line)))⟩

end repr

end Polynomial

