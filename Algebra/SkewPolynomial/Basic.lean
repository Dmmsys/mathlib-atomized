/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.SkewMonoidAlgebra.Single
public import Mathlib.Algebra.SkewMonoidAlgebra.Support
/-!
# Univariate skew polynomials

Given a ring `R` and an endomorphism `φ` on `R` the skew polynomials over `R`
are polynomials
$$\sum_{i= 0}^n a_iX^n, n\geq 0, a_i\in R$$
where the addition is the usual addition of polynomials
$$\sum_{i= 0}^n a_iX^n + \sum_{i= 0}^n b_iX^n= \sum_{i= 0}^n (a_i + b_i)X^n.$$
The multiplication, however, is determined by
$$Xa = \varphi (a)X$$
by extending it to all polynomials in the obvious way.

Skew polynomials are represented as `SkewMonoidAlgebra R (Multiplicative ℕ)`,
where `R` is usually at least a Semiring. In this file, we define `SkewPolynomial`
and provide basic instances.

**Note**: To register the endomorphism `φ` see notation below.

## Notation

The endomorphism `φ` is implemented using some action of `Multiplicative ℕ` on `R`.
From this action, `φ` is an `abbrev` denoting $(\text{ofAdd } 1) \cdot a := \varphi(a)$.

Users that want to work with a specific map `φ` should introduce an action of
`Multiplicative ℕ` on `R`. Specifying that this action is a `MulSemiringAction` amounts
to saying that `φ` is an endomorphism.

Furthermore, with this notation `φ^[n](a) = (ofAdd n) • a`, see `φ_iterate_apply`.

## Main definitions

* `SkewPolynomial.monomial n a` is the skew polynomial `a X ^ n`. Note that
  `SkewPolynomial.monomial n` is defined as an `R`-linear map.
* `SkewPolynomial.C a` is the constant skew polynomial `a`. Note that `C` is defined as an additive
  homomorphism.
* `SkewPolynomial.CRingHom a` is the constant skew polynomial `a`, as a ring homomorphism. This
  requires to assume `[MulSemiringAction (Multiplicative ℕ) R]`.
* `SkewPolynomial.X` is the skew polynomial `X`, i.e., `SkewPolynomial.monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `SkewPolynomial.coeff p n` is the coefficient of `X ^ n` in `p`.
* `SkewPolynomial.erase p n` is the skew polynomial `p` in which one removes the monomial in
  degree `n`.
* `SkewPolynomial.update p n a` is the skew polynomial obtained by replacing the coefficient of
  degree `n` by a given value `a : R`.  If `a = 0`, this is equal to `p.erase n` If
  `p.natDegree < n` and `a ≠ 0`, this increases the degree of `p` to `n`.

## Implementation notes

The implementation uses `Multiplicative ℕ` instead of `ℕ`, since Mathlib does not contain an
additive version of `SkewMonoidAlgebra`.

This decision was made because we use the type class `MulSemiringAction` to specify the properties
the action needs to respect for associativity. There is no version of this in Mathlib that
uses an acting `AddMonoid M` and so we need to use `Multiplicative ℕ` for the action.

For associativity to hold, there should be an instance of
`MulSemiringAction (Multiplicative ℕ) R` present in the context.
For example, in the context of $\mathbb{F}_q$-linear polynomials, this can be the
$q$-th Frobenius endomorphism - so $\varphi(a) = a^q$.

## Reference

The definition is inspired by Chapter 3 of [Papikian2023].

## Tags

Skew Polynomials, Twisted Polynomials.

Note that [ore33] proposes a more general definition of skew polynomial ring, where the
multiplication is determined by  $Xa = \varphi (a)X + δ (a)$, where `φ` is as above and
`δ` is a derivation.

-/

@[expose] public section

noncomputable section

open Function Multiplicative SkewMonoidAlgebra

/-- The skew polynomials over `R` is the type of univariate polynomials over `R`
endowed with a skewed convolution product. -/
/-
**SkewPolynomial** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SkewPolynomial (R : Type*) [AddCommMonoid R]
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew polynomials over `R` is the type of univariate polynomials over `R`
endowed with a skewed convolution product.
-/
abbrev SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative ℕ)

namespace SkewPolynomial

variable {R : Type*} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : SkewPolynomial R}


/-
**SkewPolynomial.zero_def** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：zero_def : (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicati
ve Nat))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_def : (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative ℕ)) := rfl

variable {S S₁ S₂ : Type*}

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
/-
**SkewPolynomial.support** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：support (p : SkewPolynomial R) : Finset Nat
参数：p : SkewPolynomial R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support (p : SkewPolynomial R) : Finset ℕ :=
  Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

/-- Though `SkewPolynomial.support` is not definiyionally equal to `SkewMonoidAlgebra.support` we
  can relate them using the following lemma. -/
/-
**SkewPolynomial.support_eq_skewMonoidAlgebra_support** 是 Mathlib 中的一个引理，位于命名空间 
`SkewPolynomial`。
形式化陈述：support_eq_skewMonoidAlgebra_support (p : SkewPolynomial R) : p.support = 
Finset.map (Multiplicative.toAdd (α
参数：p : SkewPolynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Though `SkewPolynomial.support` is not definiyionally equal to `SkewMonoidAlgebr
a.support` we
  can relate them using the following lemma.
-/
lemma support_eq_skewMonoidAlgebra_support (p : SkewPolynomial R) :
    p.support = Finset.map (Multiplicative.toAdd (α := ℕ)) (SkewMonoidAlgebra.support p) := by
  simp only [support]
/-
**SkewPolynomial.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], SkewPolynomial.support 0 = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma support_zero : (0 : SkewPolynomial R).support = ∅ := rfl
/-
**SkewPolynomial.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : SkewPolynomial R}, p.support = ∅
 ↔ p = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 := by simp [support]
/-
**SkewPolynomial.card_support_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`
。
形式化陈述：card_support_eq_zero : p.support.card = 0 ↔ p = 0
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
lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by simp
/-
**SkewPolynomial.support_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_add : (p + q).support subseteq p.support union q.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewMonoidAlgebra.support_add`：support_add [DecidableEq G] {p q : SkewMo
noidAlgebra k G} : (p + q).support subseteq p.support union q.support
-/
lemma support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

/-- `coeff p n` is the coefficient of `X ^ n` in `p`. -/
/-
**SkewPolynomial.coeff** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff (p : SkewPolynomial R) : Nat -> R
参数：p : SkewPolynomial R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeff p n` is the coefficient of `X ^ n` in `p`.
-/
def coeff (p : SkewPolynomial R) : ℕ → R := fun n ↦ (SkewMonoidAlgebra.coeff p (ofAdd n))

@[simp]
/-
**SkewPolynomial.mem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：mem_support_iff : n in p.support ↔ p.coeff n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  simp [support, coeff]
/-
**SkewPolynomial.notMem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
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
lemma notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

/-- `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`. -/
/-
**SkewPolynomial.sum** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：sum {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> 
S) : S
参数：p : SkewPolynomial R；f : Nat -> R -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of fu
nctions applied
  to coefficients of the polynomial `p`.
-/
def sum {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) : S :=
  SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r)

/-- For a skew polynomial `p`, `p.sum f` can be written in terms of `SkewMonoidAlgebra.sum p`. -/
/-
**SkewPolynomial.sum_def'** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_def' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> 
R -> S) : p.sum f = SkewMonoidAlgebra.sum p (fun n r => f (toAdd n : Nat) r)
参数：p : SkewPolynomial R；f : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a skew polynomial `p`, `p.sum f` can be written in terms of `SkewMonoidAlgeb
ra.sum p`.
-/
lemma sum_def' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r) := rfl
/-
**SkewPolynomial.sum_def** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_def {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R
 -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
参数：p : SkewPolynomial R；f : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_of_injOn`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [ins
t : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e 
: ι → κ),…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_def {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) := by
  simp only [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a) (fun _ ↦ ?_) <;>
  simp +contextual [coeff]
/-
**SkewPolynomial.sum_sum_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_sum_index {R' P : Type*} [AddCommMonoid P] [Semiring R'] {f : SkewPoly
nomial R} {g : Nat -> R -> SkewPolynomial R'} {h : Nat -> R' -> P} (h_zero : for
all (a : Nat), h a 0 = 0) (h_add : forall (a : Nat) (b₁ b₂ : R'), h a (b₁ + b₂) 
= h a b₁ + h a b₂) : sum (sum f g) h = sum f fun (a : Nat) (b : R) => sum (g a b
) h
参数：h_zero : forall (a : Nat), h a 0 = 0；h_add : forall (a : Nat) (b₁ b₂ : R'), h
 a (b₁ + b₂) = h a b₁ + h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.sum_sum_index`：sum_sum_index {α β M N P : Type*} [AddC
ommMonoid M] [AddCommMonoid N] [AddCommMonoid P] {f : SkewMonoidAlgebra M α} {g 
: α -> M -> SkewMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_sum_index {R' P : Type*} [AddCommMonoid P] [Semiring R']
    {f : SkewPolynomial R} {g : ℕ → R → SkewPolynomial R'} {h : ℕ → R' → P}
    (h_zero : ∀ (a : ℕ), h a 0 = 0)
    (h_add : ∀ (a : ℕ) (b₁ b₂ : R'), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun (a : ℕ) (b : R) ↦ sum (g a b) h := by
  simp only [sum_def', SkewMonoidAlgebra.sum_sum_index (fun a ↦ h_zero (toAdd a))
    (fun a ↦ h_add (toAdd a))]

@[simp]
/-
**SkewPolynomial.sum_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_zero {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R} : (f.sum fun
 (_ : Nat) _ => (0 : N)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
-/
lemma sum_zero {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R} :
    (f.sum fun (_ : ℕ) _ ↦ (0 : N)) = 0 :=
  SkewMonoidAlgebra.sum_zero

section Monomial

variable (n)

/-- `monomial s a` is the monomial `a * X ^ s`. -/
/-
**SkewPolynomial.monomial** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial : R ->ₗ[R] SkewPolynomial R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`monomial s a` is the monomial `a * X ^ s`.
-/
def monomial : R →ₗ[R] SkewPolynomial R := lsingle R (ofAdd n)
/-
**SkewPolynomial.monomial_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_zero_right : monomial n (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
-/
lemma monomial_zero_right : monomial n (0 : R) = 0 := single_zero _
/-
**SkewPolynomial.monomial_zero_one** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_zero_one : monomial 0 (1 : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl
/-
**SkewPolynomial.monomial_def** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_def (a : R) : monomial n a = single (ofAdd n) a
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monomial_def (a : R) : monomial n a = single (ofAdd n) a := rfl
/-
**SkewPolynomial.monomial_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_add (r s : R) : monomial n (r + s) = monomial n r + monomial n s
参数：r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.single_add`：single_add (a : G) (b₁ b₂ : k) : single a 
(b₁ + b₂) = single a b₁ + single a b₂
-/
lemma monomial_add (r s : R) : monomial n (r + s) = monomial n r + monomial n s :=
  single_add ..
/-
**SkewPolynomial.smul_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：smul_monomial {S} [Semiring S] [Module S R] (a : S) (b : R) : a • monomial
 n b = monomial n (a • b)
参数：a : S；b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.smul_single`：smul_single {S} [SMulZeroClass S k] (s : 
S) (a : G) (b : k) : s • single a b = single a (s • b)
-/
lemma smul_monomial {S} [Semiring S] [Module S R] (a : S) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  smul_single ..

@[simp]
/-
**SkewPolynomial.sum_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_monomial (f : SkewPolynomial R) : f.sum (fun (a : Nat) => monomial a) 
= f
参数：f : SkewPolynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
-/
lemma sum_monomial (f : SkewPolynomial R) : f.sum (fun (a : ℕ) ↦ monomial a) = f :=
  SkewMonoidAlgebra.sum_single _

@[simp]
/-
**SkewPolynomial.sum_monomial_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_monomial_index {N} [AddCommMonoid N] {n : Nat} {b : R} {h : Nat -> R -
> N} (h_zero : h n 0 = 0) : (monomial n b).sum h = h n b
参数：h_zero : h n 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
-/
lemma sum_monomial_index {N} [AddCommMonoid N] {n : ℕ} {b : R} {h : ℕ → R → N}
    (h_zero : h n 0 = 0) : (monomial n b).sum h = h n b :=
  SkewMonoidAlgebra.sum_single_index h_zero
/-
**SkewPolynomial.monomial_injective** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_injective : Function.Injective (monomial n : R -> SkewPolynomial 
R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.single_injective`：single_injective (a : G) : Function.
Injective (single a : k -> SkewMonoidAlgebra k G)
-/
lemma monomial_injective : Function.Injective (monomial n : R → SkewPolynomial R) :=
  single_injective (ofAdd n)

@[simp]
/-
**SkewPolynomial.monomial_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`
。
形式化陈述：monomial_eq_zero_iff (t : R) : monomial n t = 0 ↔ t = 0
参数：t : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用引理 `SkewPolynomial.monomial_injective`：monomial_injective : Function.Injecti
ve (monomial n : R -> SkewPolynomial R)
-/
lemma monomial_eq_zero_iff (t : R) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)
/-
**SkewPolynomial.monomial_eq_monomial_iff** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynom
ial`。
形式化陈述：monomial_eq_monomial_iff {m n : Nat} {a b : R} : monomial m a = monomial n
 b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_single_iff`：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : 
M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← coeff_single, coeff_inj]
  simp only [← ofCoeff_single, SkewMonoidAlgebra.ofCoeff_inj, Finsupp.single_eq_single_iff,
    EmbeddingLike.apply_eq_iff_eq]
/-
**SkewPolynomial.induction** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：induction {motive : SkewPolynomial R -> Prop} (p : SkewPolynomial R) (h0 :
 motive 0) (ha : forall (n : Nat) (r : R) (q : SkewPolynomial R), n ∉ q.support 
-> r != 0 -> motive q -> motive (SkewPolynomial.monomial n r + q)) : motive p
参数：p : SkewPolynomial R；h0 : motive 0；ha : forall (n : Nat) (r : R) (q : SkewPol
ynomial R), n ∉ q.support -> r != 0 -> motive q -> motive (SkewPolynomial.monomi
al n r + q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.induction`：induction {p : SkewMonoidAlgebra M α -> Pro
p} (f : SkewMonoidAlgebra M α) (h0 : p 0) (ha : forall (a b) (f : SkewMonoidAlge
bra M α), a ∉ f.s…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma induction {motive : SkewPolynomial R → Prop} (p : SkewPolynomial R) (h0 : motive 0)
  (ha : ∀ (n : ℕ) (r : R) (q : SkewPolynomial R), n ∉ q.support → r ≠ 0 → motive q →
    motive (SkewPolynomial.monomial n r + q)) : motive p := by
  apply SkewMonoidAlgebra.induction <;> aesop

end Monomial
section phi

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- Ring homomorphism associated to the twist of the skew polynomial ring.
The multiplication in a skew polynomial ring is given by `xr = φ(r)x`. -/
/-
**SkewPolynomial.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SkewPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphism associated to the twist of the skew polynomial ring.
The multiplication in a skew polynomial ring is given by `xr = φ(r)x`.
-/
abbrev φ := MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1)
/-
**SkewPolynomial.** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1) := rfl
/-
**SkewPolynomial.** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_iterate_apply (n : ℕ) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

end phi

/-
**SkewPolynomial.monomial_mul_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial
`。
形式化陈述：monomial_mul_monomial [MulSemiringAction (Multiplicative Nat) R] (n m : Na
t) (r s : R) : monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s))
参数：Multiplicative Nat；n m : Nat；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.φ_iterate_apply`：φ_iterate_apply (n : Nat) (a : R) : (φ^[
n] a) = ((ofAdd n) • a)
· 使用定理 `SkewMonoidAlgebra.single_mul_single`：single_mul_single {a₁ a₂ : G} {b₁ b
₂ : k} : (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂)
-/
lemma monomial_mul_monomial [MulSemiringAction (Multiplicative ℕ) R] (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s)) := by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single
/-
**SkewPolynomial.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：mul_def {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative Nat) R
] : f * g = f.sum fun (a₁ : Nat) b₁ => g.sum fun (a₂ : Nat) b₂ => monomial (a₁ +
 a₂) (b₁ * φ^[a₁] b₂)
参数：Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SkewPolynomial.φ_iterate_apply`：φ_iterate_apply (n : Nat) (a : R) : (φ^[
n] a) = ((ofAdd n) • a)
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_def {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative ℕ) R] : f * g =
    f.sum fun (a₁ : ℕ) b₁ ↦ g.sum fun (a₂ : ℕ) b₂ ↦ monomial (a₁ + a₂) (b₁ * φ^[a₁] b₂) := by
  ext
  simp [φ_iterate_apply, sum_def', coeff_mul, monomial, lsingle_apply, SkewMonoidAlgebra.coeff_sum']
  simp [SkewMonoidAlgebra.sum, Finsupp.single_apply]

section Constant

/-- `C a` is the constant SkewPolynomial `a`. `C` is provided as an additive homomorphism. -/
/-
**SkewPolynomial.C** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：C : R ->+ SkewPolynomial R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C a` is the constant SkewPolynomial `a`. `C` is provided as an additive homomor
phism.
-/
def C : R →+ SkewPolynomial R := SkewMonoidAlgebra.singleAddHom 1

variable {a b : R}
/-
**SkewPolynomial.monomial_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] ⦃a : R⦄, (SkewPolynomial.monomial 0) 
a = SkewPolynomial.C a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a := rfl
/-
**SkewPolynomial.C_0** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_0 : C (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
-/
lemma C_0 : C (0 : R) = 0 := single_zero _
/-
**SkewPolynomial.C_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_add : C (a + b) = C a + C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
lemma C_add : C (a + b) = C a + C b := C.map_add a b
/-
**SkewPolynomial.C_1** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_1 : C (1 : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma C_1 : C (1 : R) = 1 := rfl

@[simp]
/-
**SkewPolynomial.sum_C_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_C_index {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0) : (C
 a).sum f = f 0 a
参数：h : f 0 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
-/
lemma sum_C_index {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a := sum_single_index h

section RingHom

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- `CRingHom a` is the constant SkewPolynomial `a`, as a ring homomorphism. This requires
`[MulSemiringAction (Multiplicative ℕ) R]`. -/
/-
**SkewPolynomial.CRingHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：CRingHom : R ->+* SkewPolynomial R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CRingHom a` is the constant SkewPolynomial `a`, as a ring homomorphism. This re
quires
`[MulSemiringAction (Multiplicative ℕ) R]`.
-/
def CRingHom : R →+* SkewPolynomial R := SkewMonoidAlgebra.singleOneRingHom
/-
**SkewPolynomial.CRingHom_eq_C** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：CRingHom_eq_C : CRingHom a = C a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CRingHom_eq_C : CRingHom a = C a := rfl
/-
**SkewPolynomial.C_mul** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_mul : C (a * b) = C a * C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
-/
lemma C_mul : C (a * b) = C a * C b := CRingHom.map_mul a b
/-
**SkewPolynomial.C_pow** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_pow : C (a ^ n) = C a ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
lemma C_pow : C (a ^ n) = C a ^ n := CRingHom.map_pow a n
/-
**SkewPolynomial.C_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_eq_natCast (n : Nat) : C (n : R) = (n : SkewPolynomial R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
lemma C_eq_natCast (n : ℕ) : C (n : R) = (n : SkewPolynomial R) := map_natCast CRingHom n

@[simp]
/-
**SkewPolynomial.C_mul_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_mul_monomial : C a * monomial n b = monomial n (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.monomial_mul_monomial`：monomial_mul_monomial [MulSemiring
Action (Multiplicative Nat) R] (n m : Nat) (r s : R) : monomial n r * monomial m
 s = monomial (n + m) (r *…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]
/-
**SkewPolynomial.monomial_mul_C** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_mul_C : monomial n a * C b = monomial n (a * φ^[n] b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.monomial_mul_monomial`：monomial_mul_monomial [MulSemiring
Action (Multiplicative Nat) R] (n m : Nat) (r s : R) : monomial n r * monomial m
 s = monomial (n + m) (r *…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monomial_mul_C : monomial n a * C b = monomial n (a * φ^[n] b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

end RingHom

end Constant

section Variable

/-- `X` is the SkewPolynomial variable (aka indeterminate). -/
/-
**SkewPolynomial.X** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：X : SkewPolynomial R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is the SkewPolynomial variable (aka indeterminate).
-/
def X : SkewPolynomial R := monomial 1 1
/-
**SkewPolynomial.monomial_one_one_eq_X** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial
`。
形式化陈述：monomial_one_one_eq_X : monomial 1 (1 : R) = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

variable [MulSemiringAction (Multiplicative ℕ) R]
/-
**SkewPolynomial.monomial_one_right_eq_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `SkewPoly
nomial`。
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
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SkewPolynomial.monomial_one_one_eq_X`：monomial_one_one_eq_X : monomial 1
 (1 : R) = X
· 使用引理 `SkewPolynomial.monomial_mul_monomial`：monomial_mul_monomial [MulSemiring
Action (Multiplicative Nat) R] (n m : Nat) (r s : R) : monomial n r * monomial m
 s = monomial (n + m) (r *…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `MulSemiringAction.toRingHom_apply`：∀ (M : Type u_1) [inst : Monoid M] (R
 : Type v) [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R] (x : M)   (x_1
 : R), (MulSemiringActi…
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero      => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ', ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial]
    simp [add_comm]
/-
**SkewPolynomial.X_mul** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_mul : X * p = sum p (fun a b => monomial a (φ b)) * X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.mul_def`：mul_def {f g : SkewPolynomial R} [MulSemiringAct
ion (Multiplicative Nat) R] : f * g = f.sum fun (a₁ : Nat) b₁ => g.sum fun (a₂ :
 Nat) b₂ => …
· 使用引理 `SkewPolynomial.sum_monomial_index`：sum_monomial_index {N} [AddCommMonoid
 N] {n : Nat} {b : R} {h : Nat -> R -> N} (h_zero : h n 0 = 0) : (monomial n b).
sum h = h n b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `MulSemiringAction.toRingHom_apply`：∀ (M : Type u_1) [inst : Monoid M] (R
 : Type v) [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R] (x : M)   (x_1
 : R), (MulSemiringActi…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `SkewPolynomial.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : Ske
wPolynomial R} : (f.sum fun (_ : Nat) _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SkewPolynomial.sum_sum_index`：sum_sum_index {R' P : Type*} [AddCommMonoi
d P] [Semiring R'] {f : SkewPolynomial R} {g : Nat -> R -> SkewPolynomial R'} {h
 : Nat -> R' -> P}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `iterate_map_one`：iterate_map_one {M F : Type*} [One M] [FunLike F M M] [
OneHomClass F M M] (f : F) (n : Nat) : f^[n] 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 33 条，此处仅展示前 30 条）
-/
lemma X_mul : X * p = sum p (fun a b ↦ monomial a (φ b)) * X := by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp), sum_sum_index (by simp) (by simp)]
  simp [add_comm]
/-
**SkewPolynomial.X_pow_mul** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_pow_mul {n : Nat} : X ^ n * p = sum p (fun (a : Nat) b => monomial a (φ^
[n] b)) * X ^ n
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
· 使用引理 `SkewPolynomial.sum_monomial`：sum_monomial (f : SkewPolynomial R) : f.sum
 (fun (a : Nat) => monomial a) = f
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `SkewPolynomial.X_mul`：X_mul : X * p = sum p (fun a b => monomial a (φ b)
) * X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SkewPolynomial.sum_sum_index`：sum_sum_index {R' P : Type*} [AddCommMonoi
d P] [Semiring R'] {f : SkewPolynomial R} {g : Nat -> R -> SkewPolynomial R'} {h
 : Nat -> R' -> P}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iterate_map_add`：∀ {M : Type u_10} {F : Type u_11} [inst : Add M] [inst_
1 : FunLike F M M] [AddHomClass F M M] (f : F) (n : ℕ) (x y : M),   (⇑f)^[n] (x 
+ y) …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 32 条，此处仅展示前 30 条）
-/
lemma X_pow_mul {n : ℕ} : X ^ n * p = sum p (fun (a : ℕ) b ↦ monomial a (φ^[n] b)) * X ^ n := by
  induction n generalizing p with
  | zero      => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ, sum_sum_index (by simp) (by simp)]
    simp

@[simp]
/-
**SkewPolynomial.monomial_mul_X** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_mul_X (n : Nat) (r : R) : monomial n r * X = monomial (n + 1) r
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SkewPolynomial.monomial_one_one_eq_X`：monomial_one_one_eq_X : monomial 1
 (1 : R) = X
· 使用引理 `SkewPolynomial.monomial_mul_monomial`：monomial_mul_monomial [MulSemiring
Action (Multiplicative Nat) R] (n m : Nat) (r s : R) : monomial n r * monomial m
 s = monomial (n + m) (r *…
· 使用引理 `iterate_map_one`：iterate_map_one {M F : Type*} [One M] [FunLike F M M] [
OneHomClass F M M] (f : F) (n : Nat) : f^[n] 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [← monomial_one_one_eq_X, monomial_mul_monomial, iterate_map_one, mul_one]

@[simp]
/-
**SkewPolynomial.monomial_mul_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_mul_X_pow (n : Nat) (r : R) (k : Nat) : monomial n r * X ^ k = mo
nomial (n+k) r
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `SkewPolynomial.monomial_mul_X`：monomial_mul_X (n : Nat) (r : R) : monomi
al n r * X = monomial (n + 1) r
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X ^ k = monomial (n+k) r := by
  induction k with
  | zero      => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

@[simp]
/-
**SkewPolynomial.X_mul_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_mul_monomial (n : Nat) (r : R) : X * monomial n r = monomial (n+1) (φ r)
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.X_mul`：X_mul : X * p = sum p (fun a b => monomial a (φ b)
) * X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulSemiringAction.toRingHom_apply`：∀ (M : Type u_1) [inst : Monoid M] (R
 : Type v) [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R] (x : M)   (x_1
 : R), (MulSemiringActi…
· 使用引理 `SkewPolynomial.sum_monomial_index`：sum_monomial_index {N} [AddCommMonoid
 N] {n : Nat} {b : R} {h : Nat -> R -> N} (h_zero : h n 0 = 0) : (monomial n b).
sum h = h n b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SkewPolynomial.monomial_mul_X`：monomial_mul_X (n : Nat) (r : R) : monomi
al n r * X = monomial (n + 1) r
-/
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) (φ r) := by
  simp [X_mul]

@[simp]
/-
**SkewPolynomial.X_pow_mul_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_pow_mul_monomial (k n : Nat) (r : R) : X ^ k * monomial n r = monomial (
n + k) (φ^[k] r)
参数：k n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = sum p (fun (
a : Nat) b => monomial a (φ^[n] b)) * X ^ n
· 使用引理 `SkewPolynomial.sum_monomial_index`：sum_monomial_index {N} [AddCommMonoid
 N] {n : Nat} {b : R} {h : Nat -> R -> N} (h_zero : h n 0 = 0) : (monomial n b).
sum h = h n b
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SkewPolynomial.monomial_mul_X_pow`：monomial_mul_X_pow (n : Nat) (r : R) 
(k : Nat) : monomial n r * X ^ k = monomial (n+k) r
-/
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n + k) (φ^[k] r) := by
  simp [X_pow_mul]

end Variable

section Coefficient

variable {a b : R}

/-
**SkewPolynomial.coeff_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_monomial : coeff (monomial n a) m = if n = m then a else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_single_apply`：coeff_single_apply {a a' : G} {b :
 k} [Decidable (a = a')] : coeff (single a b) a' = if a = a' then b else 0
-/
lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
  SkewMonoidAlgebra.coeff_single_apply
/-
**SkewPolynomial.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), SkewPolynomial.coeff 0 n = 0
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : SkewPolynomial R) n = 0 := rfl
/-
**SkewPolynomial.coeff_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], SkewPolynomial.coeff 1 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
@[simp] lemma coeff_one_zero : coeff (1 : SkewPolynomial R) 0 = 1 := coeff_monomial
/-
**SkewPolynomial.coeff_one** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_one [MulSemiringAction (Multiplicative Nat) R] (n : Nat) : coeff (1 
: SkewPolynomial R) n = if 0 = n then 1 else 0
参数：Multiplicative Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
lemma coeff_one [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) :
    coeff (1 : SkewPolynomial R) n = if 0 = n then 1 else 0 := by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this, coeff_monomial]
/-
**SkewPolynomial.coeff_X_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], SkewPolynomial.X.coeff 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
@[simp] lemma coeff_X_one : coeff (X : SkewPolynomial R) 1 = 1 := coeff_monomial
/-
**SkewPolynomial.coeff_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], SkewPolynomial.X.coeff 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
@[simp] lemma coeff_X_zero : coeff (X : SkewPolynomial R) 0 = 0 := coeff_monomial
/-
**SkewPolynomial.coeff_monomial_succ** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} {n : ℕ} [inst : Semiring R] {a : R}, ((SkewPolynomial.mon
omial (n + 1)) a).coeff 0 = 0
参数：(SkewPolynomial.monomial (n + 1)) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]
/-
**SkewPolynomial.coeff_X** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_X : coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
lemma coeff_X : coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0 := coeff_monomial
/-
**SkewPolynomial.coeff_X_of_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_X_of_ne_one {n : Nat} (hn : n != 1) : coeff (X : SkewPolynomial R) n
 = 0
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_X`：coeff_X : coeff (X : SkewPolynomial R) n = if 1 
= n then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : SkewPolynomial R) n = 0 := by
  rw [coeff_X, if_neg hn.symm]
/-
**SkewPolynomial.coeff_C** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_C : coeff (C a) n = ite (n = 0) a 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert! coeff_monomial using 2; simp [eq_comm]
/-
**SkewPolynomial.coeff_C_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {a : R}, (SkewPolynomial.C a).coeff 0
 = a
参数：SkewPolynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m =
 if n = m then a else 0
-/
@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial
/-
**SkewPolynomial.coeff_C_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_C_ne_zero (h : n != 0) : (C a).coeff n = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[simp]
/-
**SkewPolynomial.coeff_C_succ** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n + 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
/-
**SkewPolynomial.coeff_natCast_ite** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_natCast_ite [MulSemiringAction (Multiplicative Nat) R] : (Nat.cast m
 : SkewPolynomial R).coeff n = ite (n = 0) m 0
参数：Multiplicative Nat。
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
· 使用引理 `SkewPolynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_natCast_ite [MulSemiringAction (Multiplicative ℕ) R] :
    (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m 0 := by
  simp [← C_eq_natCast, coeff_C]

@[simp]
/-
**SkewPolynomial.coeff_ofNat_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_ofNat_zero [MulSemiringAction (Multiplicative Nat) R] (a : Nat) [a.A
tLeastTwo] : coeff (ofNat(a) : SkewPolynomial R) 0 = ofNat(a)
参数：Multiplicative Nat；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_natCast_ite`：coeff_natCast_ite [MulSemiringAction (
Multiplicative Nat) R] : (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m
 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_ofNat_zero [MulSemiringAction (Multiplicative ℕ) R] (a : ℕ) [a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) 0 = ofNat(a) := by simp [OfNat.ofNat]

@[simp]
/-
**SkewPolynomial.coeff_ofNat_succ** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_ofNat_succ [MulSemiringAction (Multiplicative Nat) R] (a n : Nat) [h
 : a.AtLeastTwo] : coeff (ofNat(a) : SkewPolynomial R) (n + 1) = 0
参数：Multiplicative Nat；a n : Nat。
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
· 使用引理 `SkewPolynomial.coeff_natCast_ite`：coeff_natCast_ite [MulSemiringAction (
Multiplicative Nat) R] : (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m
 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_ofNat_succ [MulSemiringAction (Multiplicative ℕ) R] (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]
/-
**SkewPolynomial.C_mul_X_pow_eq_monomial** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomi
al`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {a : R} [inst_1 : MulSemiringAction (
Multiplicative ℕ) R] ⦃n : ℕ⦄,   SkewPolynomial.C a * SkewPolynomial.X ^ n = (Ske
wPolynomial.monomial n) a
参数：Multiplicative ℕ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma C_mul_X_pow_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] :
    ∀ ⦃n : ℕ⦄, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial,
      iterate_map_one, mul_one]
/-
**SkewPolynomial.C_mul_X_eq_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_mul_X_eq_monomial [MulSemiringAction (Multiplicative Nat) R] : C a * X =
 monomial 1 a
参数：Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewPolynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u_1} [inst : Semirin
g R] {a : R} [inst_1 : MulSemiringAction (Multiplicative ℕ) R] ⦃n : ℕ⦄,   SkewPo
lynomial.C a * SkewPolynomia…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma C_mul_X_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] : C a * X = monomial 1 a := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]
/-
**SkewPolynomial.C_injective** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_injective : Injective (C : R -> SkewPolynomial R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.monomial_injective`：monomial_injective : Function.Injecti
ve (monomial n : R -> SkewPolynomial R)
-/
lemma C_injective : Injective (C : R → SkewPolynomial R) := monomial_injective 0
/-
**SkewPolynomial.C_inj** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {a b : R}, SkewPolynomial.C a = SkewP
olynomial.C b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewPolynomial.coeff_C_zero`：∀ {R : Type u_1} [inst : Semiring R] {a : R
}, (SkewPolynomial.C a).coeff 0 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
@[simp] lemma C_inj : C a = C b ↔ a = b :=
  ⟨fun h ↦ coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩
/-
**SkewPolynomial.C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {a : R}, SkewPolynomial.C a = 0 ↔ a =
 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `SkewPolynomial.C_inj`：∀ {R : Type u_1} [inst : Semiring R] {a b : R}, Sk
ewPolynomial.C a = SkewPolynomial.C b ↔ a = b
-/
@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj

end Coefficient

/-
**SkewPolynomial.Nontrivial.of_polynomial_ne** 是 Mathlib 中的一个定理，位于命名空间 `SkewPoly
nomial.Nontrivial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : SkewPolynomial R} [MulSemiring
Action (Multiplicative ℕ) R],   p ≠ q → Nontrivial R
参数：Multiplicative ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `SkewPolynomial.C_1`：C_1 : C (1 : R) = 1
· 使用引理 `SkewPolynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma Nontrivial.of_polynomial_ne [MulSemiringAction (Multiplicative ℕ) R] (h : p ≠ q) :
    Nontrivial R :=
  ⟨⟨0, 1, fun h01 : 0 = 1 ↦ h <|
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩
/-
**SkewPolynomial.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：ext_iff {p q : SkewPolynomial R} : p = q ↔ forall n, coeff p n = coeff q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext_iff`：ext_iff {p q : SkewMonoidAlgebra k G} : p = q
 ↔ forall n, coeff p n = coeff q n
-/
lemma ext_iff {p q : SkewPolynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
  SkewMonoidAlgebra.ext_iff
/-
**SkewPolynomial.ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : SkewPolynomial R}, (∀ (n : ℕ),
 p.coeff n = q.coeff n) → p = q
参数：∀ (n : ℕ), p.coeff n = q.coeff n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
-/
@[ext] lemma ext {p q : SkewPolynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
  SkewMonoidAlgebra.ext
/-
**SkewPolynomial.addHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_5} [inst_1 : AddMonoid M]
 {f g : SkewPolynomial R →+ M},   (∀ (n : ℕ), f.comp (SkewPolynomial.monomial n)
.toAddMonoidHom = g.comp (SkewPolynomial.monomial n).toAddMonoidHom) →     f = g
参数：∀ (n : ℕ), f.comp (SkewPolynomial.monomial n).toAddMonoidHom = g.comp (SkewPo
lynomial.monomial n).toAddMonoidHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.addHom_ext'`：addHom_ext' {N : Type*} [AddZeroClass N] 
⦃f g : SkewMonoidAlgebra k G ->+ N⦄ (H : forall x, f.comp (singleAddHom x) = g.c
omp (singleAddHom x…
-/
@[ext] lemma addHom_ext' {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  SkewMonoidAlgebra.addHom_ext' h
/-
**SkewPolynomial.addHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_5} [inst_1 : AddMonoid M]
 {f g : SkewPolynomial R →+ M},   (∀ (n : ℕ) (a : R), f ((SkewPolynomial.monomia
l n) a) = g ((SkewPolynomial.monomial n) a)) → f = g
参数：∀ (n : ℕ) (a : R), f ((SkewPolynomial.monomial n) a) = g ((SkewPolynomial.mon
omial n) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g
-/
@[ext] lemma addHom_ext {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  SkewMonoidAlgebra.addHom_ext h
/-
**SkewPolynomial.linearMap_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_5} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {f g : SkewPolynomial R →ₗ[R] M}, (∀ (n : ℕ)
, f ∘ₗ SkewPolynomial.monomial n = g ∘ₗ SkewPolynomial.monomial n) → f = g
参数：∀ (n : ℕ), f ∘ₗ SkewPolynomial.monomial n = g ∘ₗ SkewPolynomial.monomial n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.lhom_ext'`：lhom_ext' {α : Type*} [Module R M] [Module 
R N] ⦃φ ψ : SkewMonoidAlgebra M α ->ₗ[R] N⦄ (h : forall a, φ.comp (lsingle R a) 
= ψ.comp (lsingle…
-/
@[ext] lemma linearMap_ext' {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : SkewPolynomial R →ₗ[R] M} (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
    f = g :=
  SkewMonoidAlgebra.lhom_ext' h
/-
**SkewPolynomial.eq_zero_of_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : SkewPolynomial R) : p = 0
参数：h : (0 : R) = (1 : R)；p : SkewPolynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : SkewPolynomial R) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Support

/-
**SkewPolynomial.support_monomial** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ) {a : R}, a ≠ 0 → ((SkewPolyno
mial.monomial n) a).support = {n}
参数：n : ℕ；(SkewPolynomial.monomial n) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SkewPolynomial.support_eq_skewMonoidAlgebra_support`：support_eq_skewMono
idAlgebra_support (p : SkewPolynomial R) : p.support = Finset.map (Multiplicativ
e.toAdd (α
· 使用定理 `SkewMonoidAlgebra.support_single`：∀ {k : Type u_1} {G : Type u_2} [inst 
: AddCommMonoid k] {b : k} (a : G),   b ≠ 0 → (SkewMonoidAlgebra.single a b).sup
port = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_monomial (n) {a : R} (h : a ≠ 0) : (monomial n a).support = singleton n := by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, h]
/-
**SkewPolynomial.support_monomial_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomi
al`。
形式化陈述：support_monomial_subset (n) {a : R} : (monomial n a).support subseteq sing
leton n
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.support_eq_skewMonoidAlgebra_support`：support_eq_skewMono
idAlgebra_support (p : SkewPolynomial R) : p.support = Finset.map (Multiplicativ
e.toAdd (α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.subset_map_symm`：subset_map_symm {t : Finset β} {f : α ≃ β} : s s
ubseteq t.map f.symm ↔ s.map f subseteq t
· 使用定理 `SkewMonoidAlgebra.support_single_subset`：support_single_subset : (single
 a b).support subseteq {a}
-/
lemma support_monomial_subset (n) {a : R} : (monomial n a).support ⊆ singleton n := by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset
/-
**SkewPolynomial.support_C** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {a : R}, a ≠ 0 → (SkewPolynomial.C a)
.support = {0}
参数：SkewPolynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewPolynomial.support_monomial`：∀ {R : Type u_1} [inst : Semiring R] (n
 : ℕ) {a : R}, a ≠ 0 → ((SkewPolynomial.monomial n) a).support = {n}
-/
@[simp] lemma support_C {a : R} (h : a ≠ 0) : (C a).support = singleton 0 := support_monomial 0 h
/-
**SkewPolynomial.support_C_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_C_subset (a : R) : (C a).support subseteq singleton 0
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.support_monomial_subset`：support_monomial_subset (n) {a :
 R} : (monomial n a).support subseteq singleton n
-/
lemma support_C_subset (a : R) : (C a).support ⊆ singleton 0 := support_monomial_subset 0
/-
**SkewPolynomial.support_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : MulSemiringAction (Multipli
cative ℕ) R] {c : R},   c ≠ 0 → (SkewPolynomial.C c * SkewPolynomial.X).support 
= {1}
参数：Multiplicative ℕ；SkewPolynomial.C c * SkewPolynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial [MulSemiringActi
on (Multiplicative Nat) R] : C a * X = monomial 1 a
· 使用定理 `SkewPolynomial.support_monomial`：∀ {R : Type u_1} [inst : Semiring R] (n
 : ℕ) {a : R}, a ≠ 0 → ((SkewPolynomial.monomial n) a).support = {n}
-/
@[simp] lemma support_C_mul_X [MulSemiringAction (Multiplicative ℕ) R] {c : R} (h : c ≠ 0) :
    support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]
/-
**SkewPolynomial.support_C_mul_X_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomia
l`。
形式化陈述：support_C_mul_X_subset [MulSemiringAction (Multiplicative Nat) R] (c : R) 
: support (C c * X) subseteq singleton 1
参数：Multiplicative Nat；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial [MulSemiringActi
on (Multiplicative Nat) R] : C a * X = monomial 1 a
· 使用引理 `SkewPolynomial.support_monomial_subset`：support_monomial_subset (n) {a :
 R} : (monomial n a).support subseteq singleton n
-/
lemma support_C_mul_X_subset [MulSemiringAction (Multiplicative ℕ) R] (c : R) :
    support (C c * X) ⊆ singleton 1 := by
  simpa [C_mul_X_eq_monomial] using support_monomial_subset 1

@[simp]
/-
**SkewPolynomial.support_C_mul_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_C_mul_X_pow [MulSemiringAction (Multiplicative Nat) R] (n : Nat) {
c : R} (h : c != 0) : support (C c * X ^ n) = singleton n
参数：Multiplicative Nat；n : Nat；h : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewPolynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u_1} [inst : Semirin
g R] {a : R} [inst_1 : MulSemiringAction (Multiplicative ℕ) R] ⦃n : ℕ⦄,   SkewPo
lynomial.C a * SkewPolynomia…
· 使用定理 `SkewPolynomial.support_monomial`：∀ {R : Type u_1} [inst : Semiring R] (n
 : ℕ) {a : R}, a ≠ 0 → ((SkewPolynomial.monomial n) a).support = {n}
-/
lemma support_C_mul_X_pow [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) {c : R} (h : c ≠ 0) :
    support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]
/-
**SkewPolynomial.support_C_mul_X_pow_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolyn
omial`。
形式化陈述：support_C_mul_X_pow_subset [MulSemiringAction (Multiplicative Nat) R] (n :
 Nat) (c : R) : support (C c * X ^ n) subseteq singleton n
参数：Multiplicative Nat；n : Nat；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewPolynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u_1} [inst : Semirin
g R] {a : R} [inst_1 : MulSemiringAction (Multiplicative ℕ) R] ⦃n : ℕ⦄,   SkewPo
lynomial.C a * SkewPolynomia…
· 使用引理 `SkewPolynomial.support_monomial_subset`：support_monomial_subset (n) {a :
 R} : (monomial n a).support subseteq singleton n
-/
lemma support_C_mul_X_pow_subset [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) (c : R) :
    support (C c * X ^ n) ⊆ singleton n := by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial_subset n

open Finset
/-
**SkewPolynomial.support_binomial_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomi
al`。
形式化陈述：support_binomial_subset [MulSemiringAction (Multiplicative Nat) R] (k m : 
Nat) (x y : R) : support (C x * X ^ k + C y * X ^ m) subseteq {k, m}
参数：Multiplicative Nat；k m : Nat；x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SkewPolynomial.support_add`：support_add : (p + q).support subseteq p.sup
port union q.support
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用引理 `SkewPolynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset [M
ulSemiringAction (Multiplicative Nat) R] (n : Nat) (c : R) : support (C c * X ^ 
n) subseteq singleton n
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
lemma support_binomial_subset [MulSemiringAction (Multiplicative ℕ) R] (k m : ℕ) (x y : R) :
    support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))
/-
**SkewPolynomial.support_trinomial_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynom
ial`。
形式化陈述：support_trinomial_subset [MulSemiringAction (Multiplicative Nat) R] (k m n
 : Nat) (x y z : R) : support (C x * X ^ k + C y * X ^ m + C z * X ^ n) subseteq
 {k, m, n}
参数：Multiplicative Nat；k m n : Nat；x y z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SkewPolynomial.support_add`：support_add : (p + q).support subseteq p.sup
port union q.support
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用引理 `SkewPolynomial.support_C_mul_X_pow_subset`：support_C_mul_X_pow_subset [M
ulSemiringAction (Multiplicative Nat) R] (n : Nat) (c : R) : support (C c * X ^ 
n) subseteq singleton n
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
lemma support_trinomial_subset [MulSemiringAction (Multiplicative ℕ) R] (k m n : ℕ) (x y z : R) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
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

end Support

variable {a b : R}

/-
**SkewPolynomial.X_pow_eq_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_pow_eq_monomial (n) [MulSemiringAction (Multiplicative Nat) R] : X ^ n =
 monomial n (1 : R)
参数：n；Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SkewPolynomial.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], SkewPolynom
ial.X = (SkewPolynomial.monomial 1) 1
· 使用引理 `SkewPolynomial.monomial_mul_monomial`：monomial_mul_monomial [MulSemiring
Action (Multiplicative Nat) R] (n m : Nat) (r s : R) : monomial n r * monomial m
 s = monomial (n + m) (r *…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `MulSemiringAction.toRingHom_apply`：∀ (M : Type u_1) [inst : Monoid M] (R
 : Type v) [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R] (x : M)   (x_1
 : R), (MulSemiringActi…
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma X_pow_eq_monomial (n) [MulSemiringAction (Multiplicative ℕ) R] :
    X ^ n = monomial n (1 : R) := by
  induction n with
  | zero      => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ', hn, X, monomial_mul_monomial]
    simp [add_comm]
/-
**SkewPolynomial.smul_X_eq_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：smul_X_eq_monomial {n} [MulSemiringAction (Multiplicative Nat) R] : a • X 
^ n = monomial n (a : R)
参数：Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.smul_single`：smul_single {S} [SMulZeroClass S k] (s : 
S) (a : G) (b : k) : s • single a b = single a (s • b)
· 使用引理 `SkewPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) [MulSemiringActi
on (Multiplicative Nat) R] : X ^ n = monomial n (1 : R)
-/
lemma smul_X_eq_monomial {n} [MulSemiringAction (Multiplicative ℕ) R] :
    a • X ^ n = monomial n (a : R) := by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n  := by rw [X_pow_eq_monomial]

@[simp]
/-
**SkewPolynomial.support_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_X_pow [Nontrivial R] (n : Nat) [MulSemiringAction (Multiplicative 
Nat) R] : (X ^ n : SkewPolynomial R).support = singleton n
参数：n : Nat；Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SkewPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) [MulSemiringActi
on (Multiplicative Nat) R] : X ^ n = monomial n (1 : R)
· 使用定理 `SkewPolynomial.support_monomial`：∀ {R : Type u_1} [inst : Semiring R] (n
 : ℕ) {a : R}, a ≠ 0 → ((SkewPolynomial.monomial n) a).support = {n}
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma support_X_pow [Nontrivial R] (n : ℕ) [MulSemiringAction (Multiplicative ℕ) R] :
    (X ^ n : SkewPolynomial R).support = singleton n := by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n
/-
**SkewPolynomial.support_X_empty** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_X_empty (H : (1 : R) = 0) : (X : SkewPolynomial R).support = ∅
参数：H : (1 : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewPolynomial.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], SkewPolynom
ial.X = (SkewPolynomial.monomial 1) 1
· 使用引理 `SkewPolynomial.monomial_zero_right`：monomial_zero_right : monomial n (0 
: R) = 0
· 使用定理 `SkewPolynomial.support_zero`：∀ {R : Type u_1} [inst : Semiring R], SkewP
olynomial.support 0 = ∅
-/
lemma support_X_empty (H : (1 : R) = 0) : (X : SkewPolynomial R).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

@[simp]
/-
**SkewPolynomial.support_X** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_X [Nontrivial R] [MulSemiringAction (Multiplicative Nat) R] : (X :
 SkewPolynomial R).support = singleton 1
参数：Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `SkewPolynomial.support_X_pow`：support_X_pow [Nontrivial R] (n : Nat) [Mu
lSemiringAction (Multiplicative Nat) R] : (X ^ n : SkewPolynomial R).support = s
ingleton n
-/
lemma support_X [Nontrivial R] [MulSemiringAction (Multiplicative ℕ) R] :
    (X : SkewPolynomial R).support = singleton 1 := by
  rw [← pow_one X, support_X_pow 1]
/-
**SkewPolynomial.monomial_left_inj** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_left_inj {R : Type*} [Semiring R] {a : R} (ha : a != 0) {i j : Na
t} : (monomial i a) = (monomial j a) ↔ i = j
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.single_left_inj`：single_left_inj {a a' : G} {b : k} (h
 : b != 0) : single a b = single a' b ↔ a = a'
-/
lemma monomial_left_inj {R : Type*} [Semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
    (monomial i a) = (monomial j a) ↔ i = j :=
  SkewMonoidAlgebra.single_left_inj ha
/-
**SkewPolynomial.nat_cast_mul** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：nat_cast_mul {R : Type*} [Semiring R] (n : Nat) (p : SkewPolynomial R) [Mu
lSemiringAction (Multiplicative Nat) R] : (n : SkewPolynomial R) * p = n • p
参数：n : Nat；p : SkewPolynomial R；Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
lemma nat_cast_mul {R : Type*} [Semiring R] (n : ℕ) (p : SkewPolynomial R)
    [MulSemiringAction (Multiplicative ℕ) R] : (n : SkewPolynomial R) * p = n • p :=
  (nsmul_eq_mul _ _).symm
section Sum

variable {S : Type*} [AddCommMonoid S]

/-
**SkewPolynomial.sum_eq_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_eq_of_subset {p : SkewPolynomial R} (f : Nat -> R -> S) (hf : forall i
, f i 0 = 0) {s : Finset Nat} (hs : p.support subseteq s) : p.sum f = ∑ n in s, 
f n (p.coeff n)
参数：f : Nat -> R -> S；hf : forall i, f i 0 = 0；hs : p.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : SkewP
olynomial R) (f : Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_eq_of_subset {p : SkewPolynomial R} (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {s : Finset ℕ}
    (hs : p.support ⊆ s) : p.sum f = ∑ n ∈ s, f n (p.coeff n) := by
  rw [sum_def , Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

@[simp]
/-
**SkewPolynomial.sum_zero_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_zero_index (f : Nat -> R -> S) : (0 : SkewPolynomial R).sum f = 0
参数：f : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.sum_zero_index`：sum_zero_index {S : Type*} [AddCommMon
oid S] {f : G -> k -> S} : (0 : SkewMonoidAlgebra k G).sum f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_zero_index (f : ℕ → R → S) : (0 : SkewPolynomial R).sum f = 0 := by
  simp [sum_def', zero_def]

@[simp]
/-
**SkewPolynomial.sum_X_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_X_index {f : Nat -> R -> S} (hf : f 1 0 = 0) : (X : SkewPolynomial R).
sum f = f 1 1
参数：hf : f 1 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.sum_monomial_index`：sum_monomial_index {N} [AddCommMonoid
 N] {n : Nat} {b : R} {h : Nat -> R -> N} (h_zero : h n 0 = 0) : (monomial n b).
sum h = h n b
-/
lemma sum_X_index {f : ℕ → R → S} (hf : f 1 0 = 0) : (X : SkewPolynomial R).sum f = f 1 1 :=
  sum_monomial_index hf
/-
**SkewPolynomial.sum_add_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_add_index (p q : SkewPolynomial R) (f : Nat -> R -> S) (hf : forall i,
 f i 0 = 0) (h_add : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) : (p + q).
sum f = p.sum f + q.sum f
参数：p q : SkewPolynomial R；f : Nat -> R -> S；hf : forall i, f i 0 = 0；h_add : for
all a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_add_index`：sum_add_index {S : Type*} [DecidableEq 
G] [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G -> k -> S} (h_zero : f
orall a in f.support …
-/
lemma sum_add_index (p q : SkewPolynomial R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0)
    (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ ↦ hf (toAdd n)) (fun n _ ↦ h_add (toAdd n))

/-- See also `SkewPolynomial.sum_add`. -/
@[simp]
/-
**SkewPolynomial.sum_add'** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_add' (p : SkewPolynomial R) (f g : Nat -> R -> S) : p.sum (f + g) = p.
sum f + p.sum g
参数：p : SkewPolynomial R；f g : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : SkewP
olynomial R) (f : Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `SkewPolynomial.sum_add`.
-/
lemma sum_add' (p : SkewPolynomial R) (f g : ℕ → R → S) : p.sum (f + g) = p.sum f + p.sum g := by
  simp [sum_def, Finset.sum_add_distrib]

/-- See also `SkewPolynomial.sum_add'`. -/
@[simp]
/-
**SkewPolynomial.sum_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_add (p : SkewPolynomial R) (f g : Nat -> R -> S) : (p.sum fun n x => f
 n x + g n x) = p.sum f + p.sum g
参数：p : SkewPolynomial R；f g : Nat -> R -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SkewPolynomial.sum_add'`：sum_add' (p : SkewPolynomial R) (f g : Nat -> R
 -> S) : p.sum (f + g) = p.sum f + p.sum g

--- 原说明 ---
See also `SkewPolynomial.sum_add'`.
-/
lemma sum_add (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

/-- See also `SkewPolynomial.sum_smul_index'` for a version using `smul` on the RHS. -/
/-
**SkewPolynomial.sum_smul_index** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_smul_index (p : SkewPolynomial R) (b : R) (f : Nat -> R -> S) (hf : fo
rall i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b * a)
参数：p : SkewPolynomial R；b : R；f : Nat -> R -> S；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_smul_index`：sum_smul_index [MulZeroClass R] [AddCommMonoid M
] {g : α ->₀ R} {b : R} {h : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).s
um h = g.sum…

--- 原说明 ---
See also `SkewPolynomial.sum_smul_index'` for a version using `smul` on the RHS.
-/
lemma sum_smul_index (p : SkewPolynomial R) (b : R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) :
    (b • p).sum f = p.sum fun n a ↦ f n (b * a) :=
  Finsupp.sum_smul_index hf

/-- See also `SkewPolynomial.sum_smul_index` for a version using multiplication on the RHS. -/
/-
**SkewPolynomial.sum_smul_index'** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：sum_smul_index' {T : Type*} [DistribSMul T R] (p : SkewPolynomial R) (b : 
T) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) : (b • p).sum f = p.sum fun n 
a => f n (b • a)
参数：p : SkewPolynomial R；b : T；f : Nat -> R -> S；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…

--- 原说明 ---
See also `SkewPolynomial.sum_smul_index` for a version using multiplication on t
he RHS.
-/
lemma sum_smul_index' {T : Type*} [DistribSMul T R] (p : SkewPolynomial R) (b : T) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a ↦ f n (b • a) :=
  Finsupp.sum_smul_index' hf
/-
**SkewPolynomial.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_5} [inst_1 : AddCommMonoi
d S] {T : Type u_6} [inst_2 : DistribSMul T S]   (p : SkewPolynomial R) (b : T) 
(f : ℕ → R → S), b • p.sum f = p.sum fun n a => b • f n a
参数：p : SkewPolynomial R；b : T；f : ℕ → R → S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
-/
protected lemma smul_sum {T : Type*} [DistribSMul T S] (p : SkewPolynomial R) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a ↦ b • f n a :=
  Finsupp.smul_sum

end Sum

@[simp]
/-
**SkewPolynomial.coeff_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_add (p q : SkewPolynomial R) (n : Nat) : coeff (p + q) n = coeff p n
 + coeff q n
参数：p q : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_add (p q : SkewPolynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  simp [coeff]

end Semiring

section Ring

variable [Ring R] {a b : R}

/-
**SkewPolynomial.sum_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {S : Type u_2} [inst_1 : Ring S] (p : Ske
wPolynomial R) (f : ℕ → R → S),   (p.sum fun n x => -f n x) = -p.sum f
参数：p : SkewPolynomial R；f : ℕ → R → S；p.sum fun n x => -f n x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : SkewP
olynomial R) (f : Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sum_neg {S : Type*} [Ring S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    (p.sum fun n x ↦ - f n x) = - p.sum f := by
  simp [sum_def, Finset.sum_neg_distrib]
/-
**SkewPolynomial.sum_sub** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {S : Type u_2} [inst_1 : Ring S] (p : Ske
wPolynomial R) (f g : ℕ → R → S),   (p.sum fun n x => f n x - g n x) = p.sum f -
 p.sum g
参数：p : SkewPolynomial R；f g : ℕ → R → S；p.sum fun n x => f n x - g n x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `SkewPolynomial.sum_add`：sum_add (p : SkewPolynomial R) (f g : Nat -> R -
> S) : (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g
· 使用定理 `SkewPolynomial.sum_neg`：∀ {R : Type u_1} [inst : Ring R] {S : Type u_2} 
[inst_1 : Ring S] (p : SkewPolynomial R) (f : ℕ → R → S),   (p.sum fun n x => -f
 n x) = -p.s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sum_sub {S : Type*} [Ring S] (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x ↦ f n x - g n x) = p.sum f - p.sum g := by
  simp only [sub_eq_add_neg, sum_add, sum_neg]
/-
**SkewPolynomial.instRing** 是 Mathlib 中的一个实例，位于命名空间 `SkewPolynomial`。
形式化陈述：instRing [MulSemiringAction (Multiplicative Nat) R] : Ring (SkewPolynomial
 R)
参数：Multiplicative Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [MulSemiringAction (Multiplicative ℕ) R] : Ring (SkewPolynomial R) :=
  SkewMonoidAlgebra.instRing

@[simp]
/-
**SkewPolynomial.coeff_neg** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_neg (p : SkewPolynomial R) (n : Nat) : coeff (-p) n = -coeff p n
参数：p : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_neg (p : SkewPolynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

@[simp]
/-
**SkewPolynomial.coeff_sub** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_sub (p q : SkewPolynomial R) (n : Nat) : coeff (p - q) n = coeff p n
 - coeff q n
参数：p q : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SkewPolynomial.coeff_add`：coeff_add (p q : SkewPolynomial R) (n : Nat) :
 coeff (p + q) n = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_sub (p q : SkewPolynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]
/-
**SkewPolynomial.monomial_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (n : ℕ) (a : R), (SkewPolynomial.monomial
 n) (-a) = -(SkewPolynomial.monomial n) a
参数：n : ℕ；a : R；SkewPolynomial.monomial n；-a；SkewPolynomial.monomial n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SkewPolynomial.monomial_add`：monomial_add (r s : R) : monomial n (r + s)
 = monomial n r + monomial n s
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `SkewPolynomial.monomial_zero_right`：monomial_zero_right : monomial n (0 
: R) = 0
-/
@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_cancel, monomial_zero_right]
/-
**SkewPolynomial.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewPolynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {p : SkewPolynomial R}, (-p).support = p.
support
参数：-p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.support_eq_skewMonoidAlgebra_support`：support_eq_skewMono
idAlgebra_support (p : SkewPolynomial R) : p.support = Finset.map (Multiplicativ
e.toAdd (α
· 使用定理 `SkewMonoidAlgebra.support_neg`：support_neg (p : SkewMonoidAlgebra k G) :
 (-p).support = p.support
-/
@[simp] lemma support_neg {p : SkewPolynomial R} : (-p).support = p.support := by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p
/-
**SkewPolynomial.monomial_sub** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_sub (n : Nat) : monomial n (a - b) = monomial n a - monomial n b
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `SkewPolynomial.monomial_add`：monomial_add (r s : R) : monomial n (r + s)
 = monomial n r + monomial n s
· 使用定理 `SkewPolynomial.monomial_neg`：∀ {R : Type u_1} [inst : Ring R] (n : ℕ) (a
 : R), (SkewPolynomial.monomial n) (-a) = -(SkewPolynomial.monomial n) a
-/
lemma monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, monomial_add, monomial_neg, sub_eq_add_neg]

variable [MulSemiringAction (Multiplicative ℕ) R]
/-
**SkewPolynomial.C_eq_intCast** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
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
lemma C_eq_intCast (n : ℤ) : C (n : R) = n := by simp [← CRingHom_eq_C]
/-
**SkewPolynomial.C_neg** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_neg : C (-a) = -C a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
-/
lemma C_neg : C (-a) = -C a := RingHom.map_neg CRingHom a
/-
**SkewPolynomial.C_sub** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：C_sub : C (a - b) = C a - C b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
lemma C_sub : C (a - b) = C a - C b := RingHom.map_sub CRingHom a b

end Ring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R]

/-
**SkewPolynomial.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `SkewPolynomial`。
形式化陈述：instNontrivial : Nontrivial (SkewPolynomial R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.instNontrivialOfNonempty`：∀ {k : Type u_1} {G : Type u
_2} [inst : AddMonoid k] [Nontrivial k] [Nonempty G], Nontrivial (SkewMonoidAlge
bra k G)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instNontrivial : Nontrivial (SkewPolynomial R) :=
  SkewMonoidAlgebra.instNontrivialOfNonempty
/-
**SkewPolynomial.X_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：X_ne_zero : (X : SkewPolynomial R) != 0
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
· 使用定理 `SkewPolynomial.coeff_X_one`：∀ {R : Type u_1} [inst : Semiring R], SkewPo
lynomial.X.coeff 1 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma X_ne_zero : (X : SkewPolynomial R) ≠ 0 := mt (congr_arg (fun p ↦ coeff p 1)) (by simp)

end NontrivialSemiring

section erase

variable [Semiring R]

/-- `erase p n` is the polynomial `p` in which the `X ^ n` term has been erased. -/
/-
**SkewPolynomial.erase** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：erase (n : Nat) (p : SkewPolynomial R) : SkewPolynomial R
参数：n : Nat；p : SkewPolynomial R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`erase p n` is the polynomial `p` in which the `X ^ n` term has been erased.
-/
def erase (n : ℕ) (p : SkewPolynomial R) : SkewPolynomial R :=
  SkewMonoidAlgebra.erase (ofAdd n) p

@[simp]
/-
**SkewPolynomial.support_erase** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_erase {p : SkewPolynomial R} (n : Nat) : support (p.erase n) = (su
pport p).erase n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.support_eq_skewMonoidAlgebra_support`：support_eq_skewMono
idAlgebra_support (p : SkewPolynomial R) : p.support = Finset.map (Multiplicativ
e.toAdd (α
· 使用定理 `SkewMonoidAlgebra.support_erase`：support_erase [DecidableEq α] : (f.eras
e a).support = f.support.erase a
· 使用定理 `Finset.map_erase`：map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (
a : α) : (s.erase a).map f = (s.map f).erase (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_erase {p : SkewPolynomial R} (n : ℕ) :
    support (p.erase n) = (support p).erase n := by
  simp [support_eq_skewMonoidAlgebra_support, erase]
/-
**SkewPolynomial.monomial_add_erase** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：monomial_add_erase (p : SkewPolynomial R) (n : Nat) : monomial n (coeff p 
n) + p.erase n = p
参数：p : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.single_add_erase`：single_add_erase (a : α) (f : SkewMo
noidAlgebra M α) : single a (f.coeff a) + f.erase a = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monomial_add_erase (p : SkewPolynomial R) (n : ℕ) :
    monomial n (coeff p n) + p.erase n = p := by
  simp [coeff, monomial_def, erase, SkewMonoidAlgebra.single_add_erase]

@[simp]
/-
**SkewPolynomial.coeff_erase** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_erase (p : SkewPolynomial R) (n i : Nat) : (p.erase n).coeff i = if 
i = n then 0 else p.coeff i
参数：p : SkewPolynomial R；n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
lemma coeff_erase (p : SkewPolynomial R) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  exact ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

@[simp]
/-
**SkewPolynomial.erase_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：erase_zero (n : Nat) : (0 : SkewPolynomial R).erase n = 0
参数：n : Nat。
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
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma erase_zero (n : ℕ) : (0 : SkewPolynomial R).erase n = 0 := by
  simp [erase, zero_def]

@[simp]
/-
**SkewPolynomial.erase_monomial** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：erase_monomial {n : Nat} {a : R} : erase n (monomial n a) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.erase_single`：erase_single : erase a (single a b) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 := by
  simp [erase, monomial_def, zero_def]

@[deprecated coeff_erase (since := "2026-07-06")]
/-
**SkewPolynomial.erase_same** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：erase_same (p : SkewPolynomial R) (n : Nat) : coeff (p.erase n) n = 0
参数：p : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_erase`：coeff_erase (p : SkewPolynomial R) (n i : Na
t) : (p.erase n).coeff i = if i = n then 0 else p.coeff i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma erase_same (p : SkewPolynomial R) (n : ℕ) : coeff (p.erase n) n = 0 := by
    simp [coeff_erase]

@[deprecated coeff_erase (since := "2026-07-06")]
/-
**SkewPolynomial.erase_ne** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：erase_ne (p : SkewPolynomial R) {n i : Nat} (h : i != n) : coeff (p.erase 
n) i = coeff p i
参数：p : SkewPolynomial R；h : i != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_erase`：coeff_erase (p : SkewPolynomial R) (n i : Na
t) : (p.erase n).coeff i = if i = n then 0 else p.coeff i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma erase_ne (p : SkewPolynomial R) {n i : ℕ} (h : i ≠ n) :
    coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

end erase

section update

variable [Semiring R]

/-- Replace the coefficient of a `p : SkewPolynomial R` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`. -/
/-
**SkewPolynomial.update** 是 Mathlib 中的一个定义，位于命名空间 `SkewPolynomial`。
形式化陈述：update (p : SkewPolynomial R) (n : Nat) (a : R) : SkewPolynomial R
参数：p : SkewPolynomial R；n : Nat；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the coefficient of a `p : SkewPolynomial R` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`.
-/
def update (p : SkewPolynomial R) (n : ℕ) (a : R) : SkewPolynomial R :=
  SkewMonoidAlgebra.update p (ofAdd n) a
/-
**SkewPolynomial.update_def** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：update_def (p : SkewPolynomial R) (n : Nat) (a : R) : p.update n a = SkewM
onoidAlgebra.update p (ofAdd n) a
参数：p : SkewPolynomial R；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma update_def (p : SkewPolynomial R) (n : ℕ) (a : R) :
    p.update n a = SkewMonoidAlgebra.update p (ofAdd n) a := rfl

@[simp]
/-
**SkewPolynomial.coeff_update** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_update (p : SkewPolynomial R) (n : Nat) (a : R) : (p.update n a).coe
ff = Function.update p.coeff n a
参数：p : SkewPolynomial R；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.coeff_update`：∀ {M : Type u_4} {α : Type u_5} [inst : 
AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) (b : M),   (f.update a b).c
oeff = f.coeff.updat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
-/
lemma coeff_update (p : SkewPolynomial R) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by
  ext; simp [coeff, update]; rfl

@[deprecated coeff_update (since := "2026-07-06")]
/-
**SkewPolynomial.coeff_update_apply** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_update_apply (p : SkewPolynomial R) (n : Nat) (a : R) (i : Nat) : (p
.update n a).coeff i = if i = n then a else p.coeff i
参数：p : SkewPolynomial R；n : Nat；a : R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_update_apply`：coeff_update_apply [DecidableEq α]
 : (f.update a b).coeff a' = if a' = a then b else f.coeff a'
-/
lemma coeff_update_apply (p : SkewPolynomial R) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i :=
  SkewMonoidAlgebra.coeff_update_apply _ _ _ _

@[deprecated coeff_update (since := "2026-07-06")]
/-
**SkewPolynomial.coeff_update_same** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_update_same (p : SkewPolynomial R) (n : Nat) (a : R) : (p.update n a
).coeff n = a
参数：p : SkewPolynomial R；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_update_apply`：coeff_update_apply (p : SkewPolynomia
l R) (n : Nat) (a : R) (i : Nat) : (p.update n a).coeff i = if i = n then a else
 p.coeff i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma coeff_update_same (p : SkewPolynomial R) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, if_pos rfl]

@[deprecated coeff_update (since := "2026-07-06")]
/-
**SkewPolynomial.coeff_update_ne** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：coeff_update_ne (p : SkewPolynomial R) {n i : Nat} (a : R) (h : i != n) : 
(p.update n a).coeff i = p.coeff i
参数：p : SkewPolynomial R；a : R；h : i != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.coeff_update_apply`：coeff_update_apply (p : SkewPolynomia
l R) (n : Nat) (a : R) (i : Nat) : (p.update n a).coeff i = if i = n then a else
 p.coeff i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma coeff_update_ne (p : SkewPolynomial R) {n i : ℕ} (a : R) (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
/-
**SkewPolynomial.update_zero_eq_erase** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`
。
形式化陈述：update_zero_eq_erase (p : SkewPolynomial R) (n : Nat) : p.update n 0 = p.e
rase n
参数：p : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewPolynomial.ext`：∀ {R : Type u_1} [inst : Semiring R] {p q : SkewPoly
nomial R}, (∀ (n : ℕ), p.coeff n = q.coeff n) → p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SkewPolynomial.coeff_update`：coeff_update (p : SkewPolynomial R) (n : Na
t) (a : R) : (p.update n a).coeff = Function.update p.coeff n a
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用引理 `SkewPolynomial.coeff_erase`：coeff_erase (p : SkewPolynomial R) (n i : Na
t) : (p.erase n).coeff i = if i = n then 0 else p.coeff i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma update_zero_eq_erase (p : SkewPolynomial R) (n : ℕ) : p.update n 0 = p.erase n := by
  ext; simp [Function.update_apply]
/-
**SkewPolynomial.support_update** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_update (p : SkewPolynomial R) (n : Nat) (a : R) [DecidableEq R] : 
support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support
参数：p : SkewPolynomial R；n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SkewPolynomial.support_eq_skewMonoidAlgebra_support`：support_eq_skewMono
idAlgebra_support (p : SkewPolynomial R) : p.support = Finset.map (Multiplicativ
e.toAdd (α
· 使用定理 `SkewMonoidAlgebra.support_update`：support_update [DecidableEq α] [Decida
bleEq M] : support (f.update a b) = if b = 0 then f.support.erase a else insert 
a f.support
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.map_erase`：map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (
a : α) : (s.erase a).map f = (s.map f).erase (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.map_insert`：map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β
) (a : α) (s : Finset α) : (insert a s).map f = insert (f a) (s.map f)
-/
lemma support_update (p : SkewPolynomial R) (n : ℕ) (a : R) [DecidableEq R] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs <;> simp
/-
**SkewPolynomial.support_update_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomial`。
形式化陈述：support_update_zero (p : SkewPolynomial R) (n : Nat) : support (p.update n
 0) = p.support.erase n
参数：p : SkewPolynomial R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.update_zero_eq_erase`：update_zero_eq_erase (p : SkewPolyn
omial R) (n : Nat) : p.update n 0 = p.erase n
· 使用引理 `SkewPolynomial.support_erase`：support_erase {p : SkewPolynomial R} (n : 
Nat) : support (p.erase n) = (support p).erase n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_update_zero (p : SkewPolynomial R) (n : ℕ) :
    support (p.update n 0) = p.support.erase n := by
  simp
/-
**SkewPolynomial.support_update_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SkewPolynomia
l`。
形式化陈述：support_update_ne_zero (p : SkewPolynomial R) (n : Nat) {a : R} (ha : a !=
 0) : support (p.update n a) = insert n p.support
参数：p : SkewPolynomial R；n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewPolynomial.support_update`：support_update (p : SkewPolynomial R) (n 
: Nat) (a : R) [DecidableEq R] : support (p.update n a) = if a = 0 then p.suppor
t.erase n else inse…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma support_update_ne_zero (p : SkewPolynomial R) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end update

end SkewPolynomial

