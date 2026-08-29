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
  degree `n` by a given value `a : R`. If `a = 0`, this is equal to `p.erase n` If
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
multiplication is determined by $Xa = \varphi (a)X + δ (a)$, where `φ` is as above and
`δ` is a derivation.

-/

@[expose] public section

noncomputable section

open Function Multiplicative SkewMonoidAlgebra

/--
Definition of `SkewPolynomial` / `SkewPolynomial` 的定义

English:
abbreviation SkewPolynomial
  signature: (R : Type*) [AddCommMonoid R]
  body: SkewMonoidAlgebra R (Multiplicative Nat)

中文:
缩写 SkewPolynomial
  签名: (R : 类型) [AddCommMonoid R]
  定义体: SkewMonoidAlgebra R (Multiplicative Nat)

Depends on / 依赖: Multiplicative, SkewMonoidAlgebra
-/
abbrev SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative Nat)

namespace SkewPolynomial

variable {R : Type*} {m n : Nat}

section Semiring

variable [Semiring R] {p q : SkewPolynomial R}


/--
lemma `zero_def` / 引理 `zero_def`

English:
lemma zero_def
  statement: (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative Nat))
  proof: rfl

中文:
引理 zero_def
  结论: (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative 自然数))
  证明: rfl
-/
lemma zero_def : (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative Nat)) := rfl

variable {S S₁ S₂ : Type*}

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (p : SkewPolynomial R)
  body: Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

中文:
定义 support
  签名: (p : SkewPolynomial R)
  定义体: Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

Depends on / 依赖: Finset, Finset.map, SkewMonoidAlgebra, SkewMonoidAlgebra.support, injective, support, toAdd.injective
-/
def support (p : SkewPolynomial R) : Finset Nat :=
  Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

/--
lemma `support_eq_skewMonoidAlgebra_support` / 引理 `support_eq_skewMonoidAlgebra_support`

English:
lemma support_eq_skewMonoidAlgebra_support
  given: (p : SkewPolynomial R)
  proof: by
  simp only [support]

中文:
引理 support_eq_skewMonoidAlgebra_support
  条件: (p : SkewPolynomial R)
  证明: by
  simp only [support]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.support, support
-/
lemma support_eq_skewMonoidAlgebra_support (p : SkewPolynomial R) :
    p.support = Finset.map (Multiplicative.toAdd (α := Nat)) (SkewMonoidAlgebra.support p) := by
  simp only [support]

/--
lemma `support_zero` / 引理 `support_zero`

English:
lemma support_zero
  statement: (0 : SkewPolynomial R).support = ∅
  proof: rfl

中文:
引理 support_zero
  结论: (0 : SkewPolynomial R).support = ∅
  证明: rfl
-/
@[simp] lemma support_zero : (0 : SkewPolynomial R).support = ∅ := rfl

/--
lemma `support_eq_empty` / 引理 `support_eq_empty`

English:
lemma support_eq_empty
  statement: p.support = ∅ ↔ p = 0
  proof: by simp [support]

中文:
引理 support_eq_empty
  结论: p.support = ∅ ↔ p = 0
  证明: by simp [support]
-/
@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 := by simp [support]

/--
lemma `card_support_eq_zero` / 引理 `card_support_eq_zero`

English:
lemma card_support_eq_zero
  statement: p.support.card = 0 ↔ p = 0
  proof: by simp

中文:
引理 card_support_eq_zero
  结论: p.support.card = 0 ↔ p = 0
  证明: by simp
-/
lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by simp

/--
lemma `support_add` / 引理 `support_add`

English:
lemma support_add
  statement: (p + q).support subseteq p.support union q.support
  proof: by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

中文:
引理 support_add
  结论: (p + q).support subseteq p.support union q.support
  证明: by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

Depends on / 依赖: Finset, Finset.map_subset_map, Finset.map_union, SkewMonoidAlgebra, SkewMonoidAlgebra.support_add, map_subset_map, map_union, support, support_add
-/
lemma support_add : (p + q).support subseteq p.support union q.support := by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (p : SkewPolynomial R)
  body: fun n => (SkewMonoidAlgebra.coeff p (ofAdd n))

@[simp]

中文:
定义 coeff
  签名: (p : SkewPolynomial R)
  定义体: fun n => (SkewMonoidAlgebra.coeff p (ofAdd n))

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.coeff
-/
def coeff (p : SkewPolynomial R) : Nat -> R := fun n => (SkewMonoidAlgebra.coeff p (ofAdd n))

@[simp]
/--
lemma `mem_support_iff` / 引理 `mem_support_iff`

English:
lemma mem_support_iff
  statement: n in p.support ↔ p.coeff n != 0
  proof: by
  simp [support, coeff]

中文:
引理 mem_support_iff
  结论: n in p.support ↔ p.coeff n != 0
  证明: by
  simp [support, coeff]

Depends on / 依赖: support
-/
lemma mem_support_iff : n in p.support ↔ p.coeff n != 0 := by
  simp [support, coeff]

/--
lemma `notMem_support_iff` / 引理 `notMem_support_iff`

English:
lemma notMem_support_iff
  statement: n ∉ p.support ↔ p.coeff n = 0
  proof: by simp

中文:
引理 notMem_support_iff
  结论: n ∉ p.support ↔ p.coeff n = 0
  证明: by simp
-/
lemma notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S)
  body: SkewMonoidAlgebra.sum p (fun n r => f (toAdd n : Nat) r)

中文:
定义 sum
  签名: {S : 类型} [AddCommMonoid S] (p : SkewPolynomial R) (f : 自然数 -> R -> S)
  定义体: SkewMonoidAlgebra.sum p (fun n r => f (toAdd n : Nat) r)

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum
-/
def sum {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S) : S :=
  SkewMonoidAlgebra.sum p (fun n r => f (toAdd n : Nat) r)

/--
lemma `sum_def'` / 引理 `sum_def'`

English:
lemma sum_def'
  given: {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S)
  proof: rfl

中文:
引理 sum_def'
  条件: {S : 类型} [AddCommMonoid S] (p : SkewPolynomial R) (f : 自然数 -> R -> S)
  证明: rfl
-/
lemma sum_def' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S) :
    p.sum f = SkewMonoidAlgebra.sum p (fun n r => f (toAdd n : Nat) r) := rfl

/--
lemma `sum_def` / 引理 `sum_def`

English:
lemma sum_def
  given: {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S)
  proof: by
  simp only [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a => a) (fun _ => ?_) <;>
  simp +contextual [coeff]

中文:
引理 sum_def
  条件: {S : 类型} [AddCommMonoid S] (p : SkewPolynomial R) (f : 自然数 -> R -> S)
  证明: by
  simp only [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a => a) (fun _ => ?_) <;>
  simp +contextual [coeff]

Depends on / 依赖: Finset, Finset.sum_of_injOn, Finsupp, Finsupp.sum, Injective, Injective.injOn, SkewMonoidAlgebra, SkewMonoidAlgebra.sum_def, contextual, sum_def, sum_of_injOn
-/
lemma sum_def {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : Nat -> R -> S) :
    p.sum f = ∑ n in p.support, f n (p.coeff n) := by
  simp only [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a => a) (fun _ => ?_) <;>
  simp +contextual [coeff]

/--
lemma `sum_sum_index` / 引理 `sum_sum_index`

English:
lemma sum_sum_index
  statement: {R' P : Type*} [AddCommMonoid P] [Semiring R']
  proof: by
  simp only [sum_def', SkewMonoidAlgebra.sum_sum_index (fun a => h_zero (toAdd a))
    (fun a => h_add (toAdd a))]

@[simp]

中文:
引理 sum_sum_index
  结论: {R' P : 类型} [AddCommMonoid P] [Semiring R']
  证明: by
  simp only [sum_def', SkewMonoidAlgebra.sum_sum_index (fun a => h_zero (toAdd a))
    (fun a => h_add (toAdd a))]

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum_sum_index, h_add, h_zero, sum_def, sum_sum_index
-/
lemma sum_sum_index {R' P : Type*} [AddCommMonoid P] [Semiring R']
    {f : SkewPolynomial R} {g : Nat -> R -> SkewPolynomial R'} {h : Nat -> R' -> P}
    (h_zero : forall (a : Nat), h a 0 = 0)
    (h_add : forall (a : Nat) (b₁ b₂ : R'), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun (a : Nat) (b : R) => sum (g a b) h := by
  simp only [sum_def', SkewMonoidAlgebra.sum_sum_index (fun a => h_zero (toAdd a))
    (fun a => h_add (toAdd a))]

@[simp]
/--
lemma `sum_zero` / 引理 `sum_zero`

English:
lemma sum_zero
  given: {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R}
  proof: SkewMonoidAlgebra.sum_zero

中文:
引理 sum_zero
  条件: {N : 类型} [AddCommMonoid N] {f : SkewPolynomial R}
  证明: SkewMonoidAlgebra.sum_zero

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum_zero, sum_zero
-/
lemma sum_zero {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R} :
    (f.sum fun (_ : Nat) _ => (0 : N)) = 0 :=
  SkewMonoidAlgebra.sum_zero

section Monomial

variable (n)

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: : R ->ₗ[R] SkewPolynomial R
  body: lsingle R (ofAdd n)

中文:
定义 monomial
  签名: : R ->ₗ[R] SkewPolynomial R
  定义体: lsingle R (ofAdd n)

Depends on / 依赖: lsingle
-/
def monomial : R ->ₗ[R] SkewPolynomial R := lsingle R (ofAdd n)

/--
lemma `monomial_zero_right` / 引理 `monomial_zero_right`

English:
lemma monomial_zero_right
  statement: monomial n (0 : R) = 0
  proof: single_zero _

中文:
引理 monomial_zero_right
  结论: monomial n (0 : R) = 0
  证明: single_zero _

Depends on / 依赖: single_zero
-/
lemma monomial_zero_right : monomial n (0 : R) = 0 := single_zero _

/--
lemma `monomial_zero_one` / 引理 `monomial_zero_one`

English:
lemma monomial_zero_one
  statement: monomial 0 (1 : R) = 1
  proof: rfl

中文:
引理 monomial_zero_one
  结论: monomial 0 (1 : R) = 1
  证明: rfl
-/
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

/--
lemma `monomial_def` / 引理 `monomial_def`

English:
lemma monomial_def
  given: (a : R)
  statement: monomial n a = single (ofAdd n) a
  proof: rfl

中文:
引理 monomial_def
  条件: (a : R)
  结论: monomial n a = single (ofAdd n) a
  证明: rfl
-/
lemma monomial_def (a : R) : monomial n a = single (ofAdd n) a := rfl

/--
lemma `monomial_add` / 引理 `monomial_add`

English:
lemma monomial_add
  given: (r s : R)
  statement: monomial n (r + s) = monomial n r + monomial n s
  proof: single_add ..

中文:
引理 monomial_add
  条件: (r s : R)
  结论: monomial n (r + s) = monomial n r + monomial n s
  证明: single_add ..

Depends on / 依赖: single_add
-/
lemma monomial_add (r s : R) : monomial n (r + s) = monomial n r + monomial n s :=
  single_add ..

/--
lemma `smul_monomial` / 引理 `smul_monomial`

English:
lemma smul_monomial
  given: {S} [Semiring S] [Module S R] (a : S) (b : R)
  proof: smul_single ..

@[simp]

中文:
引理 smul_monomial
  条件: {S} [Semiring S] [Module S R] (a : S) (b : R)
  证明: smul_single ..

@[simp]

Depends on / 依赖: smul_single
-/
lemma smul_monomial {S} [Semiring S] [Module S R] (a : S) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  smul_single ..

@[simp]
/--
lemma `sum_monomial` / 引理 `sum_monomial`

English:
lemma sum_monomial
  given: (f : SkewPolynomial R)
  statement: f.sum (fun (a : Nat) => monomial a) = f
  proof: SkewMonoidAlgebra.sum_single _

@[simp]

中文:
引理 sum_monomial
  条件: (f : SkewPolynomial R)
  结论: f.sum (fun (a : 自然数) => monomial a) = f
  证明: SkewMonoidAlgebra.sum_single _

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum_single, sum_single
-/
lemma sum_monomial (f : SkewPolynomial R) : f.sum (fun (a : Nat) => monomial a) = f :=
  SkewMonoidAlgebra.sum_single _

@[simp]
/--
lemma `sum_monomial_index` / 引理 `sum_monomial_index`

English:
lemma sum_monomial_index
  statement: {N} [AddCommMonoid N] {n : Nat} {b : R} {h : Nat -> R -> N}
  proof: SkewMonoidAlgebra.sum_single_index h_zero

中文:
引理 sum_monomial_index
  结论: {N} [AddCommMonoid N] {n : 自然数} {b : R} {h : 自然数 -> R -> N}
  证明: SkewMonoidAlgebra.sum_single_index h_zero

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum_single_index, h_zero, sum_single_index
-/
lemma sum_monomial_index {N} [AddCommMonoid N] {n : Nat} {b : R} {h : Nat -> R -> N}
    (h_zero : h n 0 = 0) : (monomial n b).sum h = h n b :=
  SkewMonoidAlgebra.sum_single_index h_zero

/--
lemma `monomial_injective` / 引理 `monomial_injective`

English:
lemma monomial_injective
  statement: Function.Injective (monomial n : R -> SkewPolynomial R)
  proof: single_injective (ofAdd n)

@[simp]

中文:
引理 monomial_injective
  结论: Function.Injective (monomial n : R -> SkewPolynomial R)
  证明: single_injective (ofAdd n)

@[simp]

Depends on / 依赖: single_injective
-/
lemma monomial_injective : Function.Injective (monomial n : R -> SkewPolynomial R) :=
  single_injective (ofAdd n)

@[simp]
/--
lemma `monomial_eq_zero_iff` / 引理 `monomial_eq_zero_iff`

English:
lemma monomial_eq_zero_iff
  given: (t : R)
  statement: monomial n t = 0 ↔ t = 0
  proof: LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)

中文:
引理 monomial_eq_zero_iff
  条件: (t : R)
  结论: monomial n t = 0 ↔ t = 0
  证明: LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)

Depends on / 依赖: LinearMap, LinearMap.map_eq_zero_iff, SkewPolynomial, SkewPolynomial.monomial_injective, map_eq_zero_iff, monomial_injective
-/
lemma monomial_eq_zero_iff (t : R) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)

/--
lemma `monomial_eq_monomial_iff` / 引理 `monomial_eq_monomial_iff`

English:
lemma monomial_eq_monomial_iff
  given: {m n : Nat} {a b : R}
  proof: by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← coeff_single, coeff_inj]
  simp only [← ofCoeff_single, SkewMonoidAlgebra.ofCoeff_inj, Finsupp.single_eq_single_iff,
    EmbeddingLike.apply_eq_iff_eq]

中文:
引理 monomial_eq_monomial_iff
  条件: {m n : 自然数} {a b : R}
  证明: by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← coeff_single, coeff_inj]
  simp only [← ofCoeff_single, SkewMonoidAlgebra.ofCoeff_inj, Finsupp.single_eq_single_iff,
    EmbeddingLike.apply_eq_iff_eq]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Finsupp, Finsupp.single_eq_single_iff, SkewMonoidAlgebra, SkewMonoidAlgebra.ofCoeff_inj, apply_eq_iff_eq, coeff_inj, coeff_single, monomial_def, ofCoeff_inj, ofCoeff_single, single_eq_single_iff
-/
lemma monomial_eq_monomial_iff {m n : Nat} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← coeff_single, coeff_inj]
  simp only [← ofCoeff_single, SkewMonoidAlgebra.ofCoeff_inj, Finsupp.single_eq_single_iff,
    EmbeddingLike.apply_eq_iff_eq]

/--
lemma `induction` / 引理 `induction`

English:
lemma induction
  statement: {motive : SkewPolynomial R -> Prop} (p : SkewPolynomial R) (h0 : motive 0)
  proof: by
  apply SkewMonoidAlgebra.induction <;> aesop

中文:
引理 induction
  结论: {motive : SkewPolynomial R -> 命题} (p : SkewPolynomial R) (h0 : motive 0)
  证明: by
  apply SkewMonoidAlgebra.induction <;> aesop

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.induction
-/
lemma induction {motive : SkewPolynomial R -> Prop} (p : SkewPolynomial R) (h0 : motive 0)
  (ha : forall (n : Nat) (r : R) (q : SkewPolynomial R), n ∉ q.support -> r != 0 -> motive q ->
    motive (SkewPolynomial.monomial n r + q)) : motive p := by
  apply SkewMonoidAlgebra.induction <;> aesop

end Monomial
section phi

variable [MulSemiringAction (Multiplicative Nat) R]

/--
Definition of `φ` / `φ` 的定义

English:
abbreviation φ
  body: MulSemiringAction.toRingHom (Multiplicative Nat) R (ofAdd 1)

中文:
缩写 φ
  定义体: MulSemiringAction.toRingHom (Multiplicative Nat) R (ofAdd 1)

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingHom, Multiplicative, toRingHom
-/
abbrev φ := MulSemiringAction.toRingHom (Multiplicative Nat) R (ofAdd 1)

/--
theorem `φ_def` / 定理 `φ_def`

English:
theorem φ_def
  statement: φ = MulSemiringAction.toRingHom (Multiplicative Nat) R (ofAdd 1)
  proof: rfl

中文:
定理 φ_def
  结论: φ = MulSemiringAction.toRingHom (Multiplicative 自然数) R (ofAdd 1)
  证明: rfl
-/
theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative Nat) R (ofAdd 1) := rfl

/--
lemma `φ_iterate_apply` / 引理 `φ_iterate_apply`

English:
lemma φ_iterate_apply
  given: (n : Nat) (a : R)
  statement: (φ^[n] a) = ((ofAdd n) • a)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

中文:
引理 φ_iterate_apply
  条件: (n : 自然数) (a : R)
  结论: (φ^[n] a) = ((ofAdd n) • a)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

Depends on / 依赖: Function, Function.iterate_succ, MulSemiringAction, MulSemiringAction.toRingHom_apply, iterate_succ, mul_comm, mul_smul, toRingHom_apply
-/
lemma φ_iterate_apply (n : Nat) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

end phi

/--
lemma `monomial_mul_monomial` / 引理 `monomial_mul_monomial`

English:
lemma monomial_mul_monomial
  given: [MulSemiringAction (Multiplicative Nat) R] (n m : Nat) (r s : R)
  proof: by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

中文:
引理 monomial_mul_monomial
  条件: [MulSemiringAction (Multiplicative 自然数) R] (n m : 自然数) (r s : R)
  证明: by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.single_mul_single, single_mul_single
-/
lemma monomial_mul_monomial [MulSemiringAction (Multiplicative Nat) R] (n m : Nat) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s)) := by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative Nat) R]
  statement: f * g =
  proof: by
  ext
  simp [φ_iterate_apply, sum_def', coeff_mul, monomial, lsingle_apply, SkewMonoidAlgebra.coeff_sum']
  simp [SkewMonoidAlgebra.sum, Finsupp.single_apply]

中文:
引理 mul_def
  条件: {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative 自然数) R]
  结论: f * g =
  证明: by
  ext
  simp [φ_iterate_apply, sum_def', coeff_mul, monomial, lsingle_apply, SkewMonoidAlgebra.coeff_sum']
  simp [SkewMonoidAlgebra.sum, Finsupp.single_apply]

Depends on / 依赖: Finsupp, Finsupp.single_apply, SkewMonoidAlgebra, SkewMonoidAlgebra.coeff_sum, SkewMonoidAlgebra.sum, coeff_mul, coeff_sum, lsingle_apply, monomial, single_apply, sum_def
-/
lemma mul_def {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative Nat) R] : f * g =
    f.sum fun (a₁ : Nat) b₁ => g.sum fun (a₂ : Nat) b₂ => monomial (a₁ + a₂) (b₁ * φ^[a₁] b₂) := by
  ext
  simp [φ_iterate_apply, sum_def', coeff_mul, monomial, lsingle_apply, SkewMonoidAlgebra.coeff_sum']
  simp [SkewMonoidAlgebra.sum, Finsupp.single_apply]

section Constant

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+ SkewPolynomial R
  body: SkewMonoidAlgebra.singleAddHom 1

中文:
定义 C
  签名: : R ->+ SkewPolynomial R
  定义体: SkewMonoidAlgebra.singleAddHom 1

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.singleAddHom, singleAddHom
-/
def C : R ->+ SkewPolynomial R := SkewMonoidAlgebra.singleAddHom 1

variable {a b : R}

/--
lemma `monomial_zero_left` / 引理 `monomial_zero_left`

English:
lemma monomial_zero_left
  given: ⦃a
  statement: R⦄ : monomial 0 a = C a
  proof: rfl

中文:
引理 monomial_zero_left
  条件: ⦃a
  结论: R⦄ : monomial 0 a = C a
  证明: rfl
-/
@[simp] lemma monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a := rfl

/--
lemma `C_0` / 引理 `C_0`

English:
lemma C_0
  statement: C (0 : R) = 0
  proof: single_zero _

中文:
引理 C_0
  结论: C (0 : R) = 0
  证明: single_zero _

Depends on / 依赖: single_zero
-/
lemma C_0 : C (0 : R) = 0 := single_zero _

/--
lemma `C_add` / 引理 `C_add`

English:
lemma C_add
  statement: C (a + b) = C a + C b
  proof: C.map_add a b

中文:
引理 C_add
  结论: C (a + b) = C a + C b
  证明: C.map_add a b

Depends on / 依赖: C.map_add, map_add
-/
lemma C_add : C (a + b) = C a + C b := C.map_add a b

/--
lemma `C_1` / 引理 `C_1`

English:
lemma C_1
  statement: C (1 : R) = 1
  proof: rfl

@[simp]

中文:
引理 C_1
  结论: C (1 : R) = 1
  证明: rfl

@[simp]
-/
lemma C_1 : C (1 : R) = 1 := rfl

@[simp]
/--
lemma `sum_C_index` / 引理 `sum_C_index`

English:
lemma sum_C_index
  given: {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0)
  proof: sum_single_index h

中文:
引理 sum_C_index
  条件: {β} [AddCommMonoid β] {f : 自然数 -> R -> β} (h : f 0 0 = 0)
  证明: sum_single_index h

Depends on / 依赖: sum_single_index
-/
lemma sum_C_index {β} [AddCommMonoid β] {f : Nat -> R -> β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a := sum_single_index h

section RingHom

variable [MulSemiringAction (Multiplicative Nat) R]

/--
Definition of `CRingHom` / `CRingHom` 的定义

English:
definition CRingHom
  signature: : R ->+* SkewPolynomial R
  body: SkewMonoidAlgebra.singleOneRingHom

中文:
定义 CRingHom
  签名: : R ->+* SkewPolynomial R
  定义体: SkewMonoidAlgebra.singleOneRingHom

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.singleOneRingHom, singleOneRingHom
-/
def CRingHom : R ->+* SkewPolynomial R := SkewMonoidAlgebra.singleOneRingHom

/--
lemma `CRingHom_eq_C` / 引理 `CRingHom_eq_C`

English:
lemma CRingHom_eq_C
  statement: CRingHom a = C a
  proof: rfl

中文:
引理 CRingHom_eq_C
  结论: CRingHom a = C a
  证明: rfl
-/
lemma CRingHom_eq_C : CRingHom a = C a := rfl

/--
lemma `C_mul` / 引理 `C_mul`

English:
lemma C_mul
  statement: C (a * b) = C a * C b
  proof: CRingHom.map_mul a b

中文:
引理 C_mul
  结论: C (a * b) = C a * C b
  证明: CRingHom.map_mul a b

Depends on / 依赖: CRingHom, CRingHom.map_mul, map_mul
-/
lemma C_mul : C (a * b) = C a * C b := CRingHom.map_mul a b

/--
lemma `C_pow` / 引理 `C_pow`

English:
lemma C_pow
  statement: C (a ^ n) = C a ^ n
  proof: CRingHom.map_pow a n

中文:
引理 C_pow
  结论: C (a ^ n) = C a ^ n
  证明: CRingHom.map_pow a n

Depends on / 依赖: CRingHom, CRingHom.map_pow, map_pow
-/
lemma C_pow : C (a ^ n) = C a ^ n := CRingHom.map_pow a n

/--
lemma `C_eq_natCast` / 引理 `C_eq_natCast`

English:
lemma C_eq_natCast
  given: (n : Nat)
  statement: C (n : R) = (n : SkewPolynomial R)
  proof: map_natCast CRingHom n

@[simp]

中文:
引理 C_eq_natCast
  条件: (n : 自然数)
  结论: C (n : R) = (n : SkewPolynomial R)
  证明: map_natCast CRingHom n

@[simp]

Depends on / 依赖: CRingHom, map_natCast
-/
lemma C_eq_natCast (n : Nat) : C (n : R) = (n : SkewPolynomial R) := map_natCast CRingHom n

@[simp]
/--
lemma `C_mul_monomial` / 引理 `C_mul_monomial`

English:
lemma C_mul_monomial
  statement: C a * monomial n b = monomial n (a * b)
  proof: by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]

中文:
引理 C_mul_monomial
  结论: C a * monomial n b = monomial n (a * b)
  证明: by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]

Depends on / 依赖: monomial_mul_monomial, monomial_zero_left, zero_add
-/
lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]
/--
lemma `monomial_mul_C` / 引理 `monomial_mul_C`

English:
lemma monomial_mul_C
  statement: monomial n a * C b = monomial n (a * φ^[n] b)
  proof: by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

中文:
引理 monomial_mul_C
  结论: monomial n a * C b = monomial n (a * φ^[n] b)
  证明: by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

Depends on / 依赖: add_zero, monomial_mul_monomial, monomial_zero_left
-/
lemma monomial_mul_C : monomial n a * C b = monomial n (a * φ^[n] b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

end RingHom

end Constant

section Variable

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : SkewPolynomial R
  body: monomial 1 1

中文:
定义 X
  签名: : SkewPolynomial R
  定义体: monomial 1 1

Depends on / 依赖: monomial
-/
def X : SkewPolynomial R := monomial 1 1

/--
lemma `monomial_one_one_eq_X` / 引理 `monomial_one_one_eq_X`

English:
lemma monomial_one_one_eq_X
  statement: monomial 1 (1 : R) = X
  proof: rfl

中文:
引理 monomial_one_one_eq_X
  结论: monomial 1 (1 : R) = X
  证明: rfl
-/
lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

variable [MulSemiringAction (Multiplicative Nat) R]

/--
lemma `monomial_one_right_eq_X_pow` / 引理 `monomial_one_right_eq_X_pow`

English:
lemma monomial_one_right_eq_X_pow
  given: (n : Nat)
  statement: monomial n (1 : R) = X ^ n
  proof: by
  induction n with
  | zero => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ']; rw [← ih]; rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]
    simp [add_comm]

中文:
引理 monomial_one_right_eq_X_pow
  条件: (n : 自然数)
  结论: monomial n (1 : R) = X ^ n
  证明: by
  induction n with
  | zero => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ']; rw [← ih]; rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]
    simp [add_comm]

Depends on / 依赖: CRingHom_eq_C, add_comm, map_one, monomial_mul_monomial, monomial_one_one_eq_X, monomial_zero_left, pow_succ, pow_zero
-/
lemma monomial_one_right_eq_X_pow (n : Nat) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ']; rw [← ih]; rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]
    simp [add_comm]

/--
lemma `X_mul` / 引理 `X_mul`

English:
lemma X_mul
  statement: X * p = sum p (fun a b => monomial a (φ b)) * X
  proof: by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp)]; rw [sum_sum_index (by simp) (by simp)]
  simp [add_comm]

中文:
引理 X_mul
  结论: X * p = sum p (fun a b => monomial a (φ b)) * X
  证明: by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp)]; rw [sum_sum_index (by simp) (by simp)]
  simp [add_comm]

Depends on / 依赖: add_comm, mul_def, sum_monomial_index, sum_sum_index
-/
lemma X_mul : X * p = sum p (fun a b => monomial a (φ b)) * X := by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp)]; rw [sum_sum_index (by simp) (by simp)]
  simp [add_comm]

/--
lemma `X_pow_mul` / 引理 `X_pow_mul`

English:
lemma X_pow_mul
  given: {n : Nat}
  statement: X ^ n * p = sum p (fun (a : Nat) b => monomial a (φ^[n] b)) * X ^ n
  proof: by
  induction n generalizing p with
  | zero => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]; rw [sum_sum_index (by simp) (

中文:
引理 X_pow_mul
  条件: {n : 自然数}
  结论: X ^ n * p = sum p (fun (a : 自然数) b => monomial a (φ^[n] b)) * X ^ n
  证明: by
  induction n generalizing p with
  | zero => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]; rw [sum_sum_index (by simp) (

Depends on / 依赖: Function, Function.iterate_zero, X_mul, conv_lhs, generalizing, id_eq, iterate_zero, mul_assoc, mul_one, one_mul, pow_succ, pow_zero, sum_monomial, sum_sum_index
-/
lemma X_pow_mul {n : Nat} : X ^ n * p = sum p (fun (a : Nat) b => monomial a (φ^[n] b)) * X ^ n := by
  induction n generalizing p with
  | zero => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc]; rw [X_mul]; rw [← mul_assoc]; rw [ih]; rw [mul_assoc]; rw [← pow_succ]; rw [sum_sum_index (by simp) (by simp)]
    simp

@[simp]
/--
lemma `monomial_mul_X` / 引理 `monomial_mul_X`

English:
lemma monomial_mul_X
  given: (n : Nat) (r : R)
  statement: monomial n r * X = monomial (n + 1) r
  proof: by
  rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [iterate_map_one]; rw [mul_one]

@[simp]

中文:
引理 monomial_mul_X
  条件: (n : 自然数) (r : R)
  结论: monomial n r * X = monomial (n + 1) r
  证明: by
  rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [iterate_map_one]; rw [mul_one]

@[simp]

Depends on / 依赖: iterate_map_one, monomial_mul_monomial, monomial_one_one_eq_X, mul_one
-/
lemma monomial_mul_X (n : Nat) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [iterate_map_one]; rw [mul_one]

@[simp]
/--
lemma `monomial_mul_X_pow` / 引理 `monomial_mul_X_pow`

English:
lemma monomial_mul_X_pow
  given: (n : Nat) (r : R) (k : Nat)
  statement: monomial n r * X ^ k = monomial (n+k) r
  proof: by
  induction k with
  | zero => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

@[simp]

中文:
引理 monomial_mul_X_pow
  条件: (n : 自然数) (r : R) (k : 自然数)
  结论: monomial n r * X ^ k = monomial (n+k) r
  证明: by
  induction k with
  | zero => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

@[simp]

Depends on / 依赖: add_assoc, mul_assoc, pow_succ
-/
lemma monomial_mul_X_pow (n : Nat) (r : R) (k : Nat) : monomial n r * X ^ k = monomial (n+k) r := by
  induction k with
  | zero => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

@[simp]
/--
lemma `X_mul_monomial` / 引理 `X_mul_monomial`

English:
lemma X_mul_monomial
  given: (n : Nat) (r : R)
  statement: X * monomial n r = monomial (n+1) (φ r)
  proof: by
  simp [X_mul]

@[simp]

中文:
引理 X_mul_monomial
  条件: (n : 自然数) (r : R)
  结论: X * monomial n r = monomial (n+1) (φ r)
  证明: by
  simp [X_mul]

@[simp]

Depends on / 依赖: X_mul
-/
lemma X_mul_monomial (n : Nat) (r : R) : X * monomial n r = monomial (n+1) (φ r) := by
  simp [X_mul]

@[simp]
/--
lemma `X_pow_mul_monomial` / 引理 `X_pow_mul_monomial`

English:
lemma X_pow_mul_monomial
  given: (k n : Nat) (r : R)
  statement: X ^ k * monomial n r = monomial (n + k) (φ^[k] r)
  proof: by
  simp [X_pow_mul]

中文:
引理 X_pow_mul_monomial
  条件: (k n : 自然数) (r : R)
  结论: X ^ k * monomial n r = monomial (n + k) (φ^[k] r)
  证明: by
  simp [X_pow_mul]

Depends on / 依赖: X_pow_mul
-/
lemma X_pow_mul_monomial (k n : Nat) (r : R) : X ^ k * monomial n r = monomial (n + k) (φ^[k] r) := by
  simp [X_pow_mul]

end Variable

section Coefficient

variable {a b : R}

/--
lemma `coeff_monomial` / 引理 `coeff_monomial`

English:
lemma coeff_monomial
  statement: coeff (monomial n a) m = if n = m then a else 0
  proof: SkewMonoidAlgebra.coeff_single_apply

中文:
引理 coeff_monomial
  结论: coeff (monomial n a) m = if n = m then a else 0
  证明: SkewMonoidAlgebra.coeff_single_apply

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.coeff_single_apply, coeff_single_apply
-/
lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
  SkewMonoidAlgebra.coeff_single_apply

/--
lemma `coeff_zero` / 引理 `coeff_zero`

English:
lemma coeff_zero
  given: (n : Nat)
  statement: coeff (0 : SkewPolynomial R) n = 0
  proof: rfl

中文:
引理 coeff_zero
  条件: (n : 自然数)
  结论: coeff (0 : SkewPolynomial R) n = 0
  证明: rfl
-/
@[simp] lemma coeff_zero (n : Nat) : coeff (0 : SkewPolynomial R) n = 0 := rfl

/--
lemma `coeff_one_zero` / 引理 `coeff_one_zero`

English:
lemma coeff_one_zero
  statement: coeff (1 : SkewPolynomial R) 0 = 1
  proof: coeff_monomial

中文:
引理 coeff_one_zero
  结论: coeff (1 : SkewPolynomial R) 0 = 1
  证明: coeff_monomial
-/
@[simp] lemma coeff_one_zero : coeff (1 : SkewPolynomial R) 0 = 1 := coeff_monomial

/--
lemma `coeff_one` / 引理 `coeff_one`

English:
lemma coeff_one
  given: [MulSemiringAction (Multiplicative Nat) R] (n : Nat)
  proof: by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this]; rw [coeff_monomial]

中文:
引理 coeff_one
  条件: [MulSemiringAction (Multiplicative 自然数) R] (n : 自然数)
  证明: by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this]; rw [coeff_monomial]

Depends on / 依赖: CRingHom_eq_C, SkewPolynomial, coeff_monomial, monomial
-/
lemma coeff_one [MulSemiringAction (Multiplicative Nat) R] (n : Nat) :
    coeff (1 : SkewPolynomial R) n = if 0 = n then 1 else 0 := by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this]; rw [coeff_monomial]

/--
lemma `coeff_X_one` / 引理 `coeff_X_one`

English:
lemma coeff_X_one
  statement: coeff (X : SkewPolynomial R) 1 = 1
  proof: coeff_monomial

中文:
引理 coeff_X_one
  结论: coeff (X : SkewPolynomial R) 1 = 1
  证明: coeff_monomial
-/
@[simp] lemma coeff_X_one : coeff (X : SkewPolynomial R) 1 = 1 := coeff_monomial

/--
lemma `coeff_X_zero` / 引理 `coeff_X_zero`

English:
lemma coeff_X_zero
  statement: coeff (X : SkewPolynomial R) 0 = 0
  proof: coeff_monomial

中文:
引理 coeff_X_zero
  结论: coeff (X : SkewPolynomial R) 0 = 0
  证明: coeff_monomial
-/
@[simp] lemma coeff_X_zero : coeff (X : SkewPolynomial R) 0 = 0 := coeff_monomial

/--
lemma `coeff_monomial_succ` / 引理 `coeff_monomial_succ`

English:
lemma coeff_monomial_succ
  statement: coeff (monomial (n + 1) a) 0 = 0
  proof: by simp [coeff_monomial]

中文:
引理 coeff_monomial_succ
  结论: coeff (monomial (n + 1) a) 0 = 0
  证明: by simp [coeff_monomial]
-/
@[simp] lemma coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

/--
lemma `coeff_X` / 引理 `coeff_X`

English:
lemma coeff_X
  statement: coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0
  proof: coeff_monomial

中文:
引理 coeff_X
  结论: coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0
  证明: coeff_monomial

Depends on / 依赖: coeff_monomial
-/
lemma coeff_X : coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

/--
lemma `coeff_X_of_ne_one` / 引理 `coeff_X_of_ne_one`

English:
lemma coeff_X_of_ne_one
  given: {n : Nat} (hn : n != 1)
  statement: coeff (X : SkewPolynomial R) n = 0
  proof: by
  rw [coeff_X]; rw [if_neg hn.symm]

中文:
引理 coeff_X_of_ne_one
  条件: {n : 自然数} (hn : n != 1)
  结论: coeff (X : SkewPolynomial R) n = 0
  证明: by
  rw [coeff_X]; rw [if_neg hn.symm]

Depends on / 依赖: coeff_X, hn.symm, if_neg
-/
lemma coeff_X_of_ne_one {n : Nat} (hn : n != 1) : coeff (X : SkewPolynomial R) n = 0 := by
  rw [coeff_X]; rw [if_neg hn.symm]

/--
lemma `coeff_C` / 引理 `coeff_C`

English:
lemma coeff_C
  statement: coeff (C a) n = ite (n = 0) a 0
  proof: by
  convert! coeff_monomial using 2; simp [eq_comm]

中文:
引理 coeff_C
  结论: coeff (C a) n = ite (n = 0) a 0
  证明: by
  convert! coeff_monomial using 2; simp [eq_comm]

Depends on / 依赖: coeff_monomial, convert, eq_comm
-/
lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert! coeff_monomial using 2; simp [eq_comm]

/--
lemma `coeff_C_zero` / 引理 `coeff_C_zero`

English:
lemma coeff_C_zero
  statement: coeff (C a) 0 = a
  proof: coeff_monomial

中文:
引理 coeff_C_zero
  结论: coeff (C a) 0 = a
  证明: coeff_monomial
-/
@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

/--
lemma `coeff_C_ne_zero` / 引理 `coeff_C_ne_zero`

English:
lemma coeff_C_ne_zero
  given: (h : n != 0)
  statement: (C a).coeff n = 0
  proof: by rw [coeff_C, if_neg h]

@[simp]

中文:
引理 coeff_C_ne_zero
  条件: (h : n != 0)
  结论: (C a).coeff n = 0
  证明: by rw [coeff_C, if_neg h]

@[simp]

Depends on / 依赖: coeff_C, if_neg
-/
lemma coeff_C_ne_zero (h : n != 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

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
lemma `coeff_natCast_ite` / 引理 `coeff_natCast_ite`

English:
lemma coeff_natCast_ite
  given: [MulSemiringAction (Multiplicative Nat) R]
  proof: by
  simp [← C_eq_natCast, coeff_C]

@[simp]

中文:
引理 coeff_natCast_ite
  条件: [MulSemiringAction (Multiplicative 自然数) R]
  证明: by
  simp [← C_eq_natCast, coeff_C]

@[simp]

Depends on / 依赖: C_eq_natCast, coeff_C
-/
lemma coeff_natCast_ite [MulSemiringAction (Multiplicative Nat) R] :
    (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m 0 := by
  simp [← C_eq_natCast, coeff_C]

@[simp]
/--
lemma `coeff_ofNat_zero` / 引理 `coeff_ofNat_zero`

English:
lemma coeff_ofNat_zero
  given: [MulSemiringAction (Multiplicative Nat) R] (a : Nat) [a.AtLeastTwo]
  proof: by simp [OfNat.ofNat]

@[simp]

中文:
引理 coeff_ofNat_zero
  条件: [MulSemiringAction (Multiplicative 自然数) R] (a : 自然数) [a.AtLeastTwo]
  证明: by simp [OfNat.ofNat]

@[simp]

Depends on / 依赖: OfNat.ofNat
-/
lemma coeff_ofNat_zero [MulSemiringAction (Multiplicative Nat) R] (a : Nat) [a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) 0 = ofNat(a) := by simp [OfNat.ofNat]

@[simp]
/--
lemma `coeff_ofNat_succ` / 引理 `coeff_ofNat_succ`

English:
lemma coeff_ofNat_succ
  given: [MulSemiringAction (Multiplicative Nat) R] (a n : Nat) [h : a.AtLeastTwo]
  proof: by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

中文:
引理 coeff_ofNat_succ
  条件: [MulSemiringAction (Multiplicative 自然数) R] (a n : 自然数) [h : a.AtLeastTwo]
  证明: by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

Depends on / 依赖: Nat.cast_ofNat, cast_ofNat
-/
lemma coeff_ofNat_succ [MulSemiringAction (Multiplicative Nat) R] (a n : Nat) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

/--
lemma `C_mul_X_pow_eq_monomial` / 引理 `C_mul_X_pow_eq_monomial`

English:
lemma C_mul_X_pow_eq_monomial
  given: [MulSemiringAction (Multiplicative Nat) R]

中文:
引理 C_mul_X_pow_eq_monomial
  条件: [MulSemiringAction (Multiplicative 自然数) R]
-/
lemma C_mul_X_pow_eq_monomial [MulSemiringAction (Multiplicative Nat) R] :
    forall ⦃n : Nat⦄, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ]; rw [← mul_assoc]; rw [C_mul_X_pow_eq_monomial]; rw [X]; rw [monomial_mul_monomial]; rw [iterate_map_one]; rw [mul_one]

/--
lemma `C_mul_X_eq_monomial` / 引理 `C_mul_X_eq_monomial`

English:
lemma C_mul_X_eq_monomial
  given: [MulSemiringAction (Multiplicative Nat) R]
  statement: C a * X = monomial 1 a
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

中文:
引理 C_mul_X_eq_monomial
  条件: [MulSemiringAction (Multiplicative 自然数) R]
  结论: C a * X = monomial 1 a
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

Depends on / 依赖: C_mul_X_pow_eq_monomial, pow_one
-/
lemma C_mul_X_eq_monomial [MulSemiringAction (Multiplicative Nat) R] : C a * X = monomial 1 a := by
  rw [← C_mul_X_pow_eq_monomial]; rw [pow_one]

/--
lemma `C_injective` / 引理 `C_injective`

English:
lemma C_injective
  statement: Injective (C : R -> SkewPolynomial R)
  proof: monomial_injective 0

中文:
引理 C_injective
  结论: Injective (C : R -> SkewPolynomial R)
  证明: monomial_injective 0

Depends on / 依赖: monomial_injective
-/
lemma C_injective : Injective (C : R -> SkewPolynomial R) := monomial_injective 0

/--
lemma `C_inj` / 引理 `C_inj`

English:
lemma C_inj
  statement: C a = C b ↔ a = b
  proof: ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

中文:
引理 C_inj
  结论: C a = C b ↔ a = b
  证明: ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩
-/
@[simp] lemma C_inj : C a = C b ↔ a = b :=
  ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

/--
lemma `C_eq_zero` / 引理 `C_eq_zero`

English:
lemma C_eq_zero
  statement: C a = 0 ↔ a = 0
  proof: calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj

中文:
引理 C_eq_zero
  结论: C a = 0 ↔ a = 0
  证明: calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj
-/
@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj

end Coefficient

/--
lemma `Nontrivial.of_polynomial_ne` / 引理 `Nontrivial.of_polynomial_ne`

English:
lemma Nontrivial.of_polynomial_ne
  given: [MulSemiringAction (Multiplicative Nat) R] (h : p != q)
  proof: ⟨⟨0, 1, fun h01 : 0 = 1 => h
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

中文:
引理 Nontrivial.of_polynomial_ne
  条件: [MulSemiringAction (Multiplicative 自然数) R] (h : p != q)
  证明: ⟨⟨0, 1, fun h01 : 0 = 1 => h
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩
-/
lemma Nontrivial.of_polynomial_ne [MulSemiringAction (Multiplicative Nat) R] (h : p != q) :
    Nontrivial R :=
⟨⟨0, 1, fun h01 : 0 = 1 => h
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: {p q : SkewPolynomial R}
  statement: p = q ↔ forall n, coeff p n = coeff q n
  proof: SkewMonoidAlgebra.ext_iff

中文:
引理 ext_iff
  条件: {p q : SkewPolynomial R}
  结论: p = q ↔ 对任意 n, coeff p n = coeff q n
  证明: SkewMonoidAlgebra.ext_iff

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.ext_iff, ext_iff
-/
lemma ext_iff {p q : SkewPolynomial R} : p = q ↔ forall n, coeff p n = coeff q n :=
  SkewMonoidAlgebra.ext_iff

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {p q : SkewPolynomial R}
  statement: (forall n, coeff p n = coeff q n) -> p = q
  proof: SkewMonoidAlgebra.ext

中文:
引理 ext
  条件: {p q : SkewPolynomial R}
  结论: (对任意 n, coeff p n = coeff q n) -> p = q
  证明: SkewMonoidAlgebra.ext
-/
@[ext] lemma ext {p q : SkewPolynomial R} : (forall n, coeff p n = coeff q n) -> p = q :=
  SkewMonoidAlgebra.ext

/--
lemma `addHom_ext'` / 引理 `addHom_ext'`

English:
lemma addHom_ext'
  statement: {M : Type*} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
  proof: SkewMonoidAlgebra.addHom_ext' h

中文:
引理 addHom_ext'
  结论: {M : 类型} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
  证明: SkewMonoidAlgebra.addHom_ext' h
-/
@[ext] lemma addHom_ext' {M : Type*} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
    (h : forall n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  SkewMonoidAlgebra.addHom_ext' h

/--
lemma `addHom_ext` / 引理 `addHom_ext`

English:
lemma addHom_ext
  statement: {M : Type*} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
  proof: SkewMonoidAlgebra.addHom_ext h

中文:
引理 addHom_ext
  结论: {M : 类型} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
  证明: SkewMonoidAlgebra.addHom_ext h
-/
@[ext] lemma addHom_ext {M : Type*} [AddMonoid M] {f g : SkewPolynomial R ->+ M}
    (h : forall n a, f (monomial n a) = g (monomial n a)) : f = g :=
  SkewMonoidAlgebra.addHom_ext h

/--
lemma `linearMap_ext'` / 引理 `linearMap_ext'`

English:
lemma linearMap_ext'
  statement: {M : Type*} [AddCommMonoid M] [Module R M]
  proof: SkewMonoidAlgebra.lhom_ext' h

中文:
引理 linearMap_ext'
  结论: {M : 类型} [AddCommMonoid M] [Module R M]
  证明: SkewMonoidAlgebra.lhom_ext' h
-/
@[ext] lemma linearMap_ext' {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : SkewPolynomial R ->ₗ[R] M} (h : forall n, f.comp (monomial n) = g.comp (monomial n)) :
    f = g :=
  SkewMonoidAlgebra.lhom_ext' h

/--
lemma `eq_zero_of_eq_zero` / 引理 `eq_zero_of_eq_zero`

English:
lemma eq_zero_of_eq_zero
  given: (h : (0 : R) = (1 : R)) (p : SkewPolynomial R)
  statement: p = 0
  proof: by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

中文:
引理 eq_zero_of_eq_zero
  条件: (h : (0 : R) = (1 : R)) (p : SkewPolynomial R)
  结论: p = 0
  证明: by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

Depends on / 依赖: one_smul, zero_smul
-/
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : SkewPolynomial R) : p = 0 := by
  rw [← one_smul R p]; rw [← h]; rw [zero_smul]

section Support

/--
lemma `support_monomial` / 引理 `support_monomial`

English:
lemma support_monomial
  given: (n) {a : R} (h : a != 0)
  statement: (monomial n a).support = singleton n
  proof: by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, h]

中文:
引理 support_monomial
  条件: (n) {a : R} (h : a != 0)
  结论: (monomial n a).support = singleton n
  证明: by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, h]
-/
@[simp] lemma support_monomial (n) {a : R} (h : a != 0) : (monomial n a).support = singleton n := by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, h]

/--
lemma `support_monomial_subset` / 引理 `support_monomial_subset`

English:
lemma support_monomial_subset
  given: (n) {a : R}
  statement: (monomial n a).support subseteq singleton n
  proof: by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset

中文:
引理 support_monomial_subset
  条件: (n) {a : R}
  结论: (monomial n a).support subseteq singleton n
  证明: by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset

Depends on / 依赖: Finset, Finset.subset_map_symm.mp, SkewMonoidAlgebra, SkewMonoidAlgebra.support_single_subset, monomial_def, subset_map_symm, support_eq_skewMonoidAlgebra_support, support_single_subset
-/
lemma support_monomial_subset (n) {a : R} : (monomial n a).support subseteq singleton n := by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset

/--
lemma `support_C` / 引理 `support_C`

English:
lemma support_C
  given: {a : R} (h : a != 0)
  statement: (C a).support = singleton 0
  proof: support_monomial 0 h

中文:
引理 support_C
  条件: {a : R} (h : a != 0)
  结论: (C a).support = singleton 0
  证明: support_monomial 0 h
-/
@[simp] lemma support_C {a : R} (h : a != 0) : (C a).support = singleton 0 := support_monomial 0 h

/--
lemma `support_C_subset` / 引理 `support_C_subset`

English:
lemma support_C_subset
  given: (a : R)
  statement: (C a).support subseteq singleton 0
  proof: support_monomial_subset 0

中文:
引理 support_C_subset
  条件: (a : R)
  结论: (C a).support subseteq singleton 0
  证明: support_monomial_subset 0

Depends on / 依赖: ClassGroup, ClassGroup.mk_eq_mk_of_coe_ideal, XClass_ne_zero, XYIdeal, XYIdeal_mul_XYIdeal, YClass_ne_zero, coeIdeal_mul, map_mul, mk_eq_mk_of_coe_ideal, support_monomial_subset
-/
lemma support_C_subset (a : R) : (C a).support subseteq singleton 0 := support_monomial_subset 0

/--
lemma `support_C_mul_X` / 引理 `support_C_mul_X`

English:
lemma support_C_mul_X
  given: [MulSemiringAction (Multiplicative Nat) R] {c : R} (h : c != 0)
  proof: by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]

中文:
引理 support_C_mul_X
  条件: [MulSemiringAction (Multiplicative 自然数) R] {c : R} (h : c != 0)
  证明: by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]
-/
@[simp] lemma support_C_mul_X [MulSemiringAction (Multiplicative Nat) R] {c : R} (h : c != 0) :
    support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial]; rw [support_monomial 1 h]

/--
lemma `support_C_mul_X_subset` / 引理 `support_C_mul_X_subset`

English:
lemma support_C_mul_X_subset
  given: [MulSemiringAction (Multiplicative Nat) R] (c : R)
  proof: by
  simpa [C_mul_X_eq_monomial] using support_monomial_subset 1

@[simp]

中文:
引理 support_C_mul_X_subset
  条件: [MulSemiringAction (Multiplicative 自然数) R] (c : R)
  证明: by
  simpa [C_mul_X_eq_monomial] using support_monomial_subset 1

@[simp]

Depends on / 依赖: C_mul_X_eq_monomial, support_monomial_subset
-/
lemma support_C_mul_X_subset [MulSemiringAction (Multiplicative Nat) R] (c : R) :
    support (C c * X) subseteq singleton 1 := by
  simpa [C_mul_X_eq_monomial] using support_monomial_subset 1

@[simp]
/--
lemma `support_C_mul_X_pow` / 引理 `support_C_mul_X_pow`

English:
lemma support_C_mul_X_pow
  given: [MulSemiringAction (Multiplicative Nat) R] (n : Nat) {c : R} (h : c != 0)
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

中文:
引理 support_C_mul_X_pow
  条件: [MulSemiringAction (Multiplicative 自然数) R] (n : 自然数) {c : R} (h : c != 0)
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

Depends on / 依赖: C_mul_X_pow_eq_monomial, support_monomial
-/
lemma support_C_mul_X_pow [MulSemiringAction (Multiplicative Nat) R] (n : Nat) {c : R} (h : c != 0) :
    support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial]; rw [support_monomial n h]

/--
lemma `support_C_mul_X_pow_subset` / 引理 `support_C_mul_X_pow_subset`

English:
lemma support_C_mul_X_pow_subset
  given: [MulSemiringAction (Multiplicative Nat) R] (n : Nat) (c : R)
  proof: by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial_subset n

中文:
引理 support_C_mul_X_pow_subset
  条件: [MulSemiringAction (Multiplicative 自然数) R] (n : 自然数) (c : R)
  证明: by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial_subset n

Depends on / 依赖: C_mul_X_pow_eq_monomial, support_monomial_subset
-/
lemma support_C_mul_X_pow_subset [MulSemiringAction (Multiplicative Nat) R] (n : Nat) (c : R) :
    support (C c * X ^ n) subseteq singleton n := by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial_subset n

open Finset
/--
lemma `support_binomial_subset` / 引理 `support_binomial_subset`

English:
lemma support_binomial_subset
  given: [MulSemiringAction (Multiplicative Nat) R] (k m : Nat) (x y : R)
  proof: support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

中文:
引理 support_binomial_subset
  条件: [MulSemiringAction (Multiplicative 自然数) R] (k m : 自然数) (x y : R)
  证明: support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

Depends on / 依赖: mem_insert_of_mem, mem_insert_self, mem_singleton_self, singleton_subset_iff, singleton_subset_iff.mpr, support_C_mul_X_pow_subset, support_add, support_add.trans, union_subset
-/
lemma support_binomial_subset [MulSemiringAction (Multiplicative Nat) R] (k m : Nat) (x y : R) :
    support (C x * X ^ k + C y * X ^ m) subseteq {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

/--
lemma `support_trinomial_subset` / 引理 `support_trinomial_subset`

English:
lemma support_trinomial_subset
  given: [MulSemiringAction (Multiplicative Nat) R] (k m n : Nat) (x y z : R)
  proof: support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow_subset k x).trans
            (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow_subset m y).trans
            (singleton_subset_iff.mpr (mem_insert_

中文:
引理 support_trinomial_subset
  条件: [MulSemiringAction (Multiplicative 自然数) R] (k m n : 自然数) (x y z : R)
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
lemma support_trinomial_subset [MulSemiringAction (Multiplicative Nat) R] (k m n : Nat) (x y z : R) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) subseteq {k, m, n} :=
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

/--
lemma `X_pow_eq_monomial` / 引理 `X_pow_eq_monomial`

English:
lemma X_pow_eq_monomial
  given: (n) [MulSemiringAction (Multiplicative Nat) R]
  proof: by
  induction n with
  | zero => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ']; rw [hn]; rw [X]; rw [monomial_mul_monomial]
    simp [add_comm]

中文:
引理 X_pow_eq_monomial
  条件: (n) [MulSemiringAction (Multiplicative 自然数) R]
  证明: by
  induction n with
  | zero => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ']; rw [hn]; rw [X]; rw [monomial_mul_monomial]
    simp [add_comm]

Depends on / 依赖: CRingHom_eq_C, add_comm, map_one, monomial_mul_monomial, monomial_zero_left, pow_succ, pow_zero
-/
lemma X_pow_eq_monomial (n) [MulSemiringAction (Multiplicative Nat) R] :
    X ^ n = monomial n (1 : R) := by
  induction n with
  | zero => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ']; rw [hn]; rw [X]; rw [monomial_mul_monomial]
    simp [add_comm]

/--
lemma `smul_X_eq_monomial` / 引理 `smul_X_eq_monomial`

English:
lemma smul_X_eq_monomial
  given: {n} [MulSemiringAction (Multiplicative Nat) R]
  proof: by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n := by rw [X_pow_eq_monomial]

@[simp]

中文:
引理 smul_X_eq_monomial
  条件: {n} [MulSemiringAction (Multiplicative 自然数) R]
  证明: by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n := by rw [X_pow_eq_monomial]

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.smul_single, X_pow_eq_monomial, eq_comm, monomial, mul_one, smul_eq_mul, smul_single
-/
lemma smul_X_eq_monomial {n} [MulSemiringAction (Multiplicative Nat) R] :
    a • X ^ n = monomial n (a : R) := by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n := by rw [X_pow_eq_monomial]

@[simp]
/--
lemma `support_X_pow` / 引理 `support_X_pow`

English:
lemma support_X_pow
  given: [Nontrivial R] (n : Nat) [MulSemiringAction (Multiplicative Nat) R]
  proof: by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

中文:
引理 support_X_pow
  条件: [Nontrivial R] (n : 自然数) [MulSemiringAction (Multiplicative 自然数) R]
  证明: by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

Depends on / 依赖: NeZero, NeZero.out, X_pow_eq_monomial, convert, support_monomial
-/
lemma support_X_pow [Nontrivial R] (n : Nat) [MulSemiringAction (Multiplicative Nat) R] :
    (X ^ n : SkewPolynomial R).support = singleton n := by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

/--
lemma `support_X_empty` / 引理 `support_X_empty`

English:
lemma support_X_empty
  given: (H : (1 : R) = 0)
  statement: (X : SkewPolynomial R).support = ∅
  proof: by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]

中文:
引理 support_X_empty
  条件: (H : (1 : R) = 0)
  结论: (X : SkewPolynomial R).support = ∅
  证明: by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]

Depends on / 依赖: monomial_zero_right, support_zero
-/
lemma support_X_empty (H : (1 : R) = 0) : (X : SkewPolynomial R).support = ∅ := by
  rw [X]; rw [H]; rw [monomial_zero_right]; rw [support_zero]

@[simp]
/--
lemma `support_X` / 引理 `support_X`

English:
lemma support_X
  given: [Nontrivial R] [MulSemiringAction (Multiplicative Nat) R]
  proof: by
  rw [← pow_one X]; rw [support_X_pow 1]

中文:
引理 support_X
  条件: [Nontrivial R] [MulSemiringAction (Multiplicative 自然数) R]
  证明: by
  rw [← pow_one X]; rw [support_X_pow 1]

Depends on / 依赖: pow_one, support_X_pow
-/
lemma support_X [Nontrivial R] [MulSemiringAction (Multiplicative Nat) R] :
    (X : SkewPolynomial R).support = singleton 1 := by
  rw [← pow_one X]; rw [support_X_pow 1]

/--
lemma `monomial_left_inj` / 引理 `monomial_left_inj`

English:
lemma monomial_left_inj
  given: {R : Type*} [Semiring R] {a : R} (ha : a != 0) {i j : Nat}
  proof: SkewMonoidAlgebra.single_left_inj ha

中文:
引理 monomial_left_inj
  条件: {R : 类型} [Semiring R] {a : R} (ha : a != 0) {i j : 自然数}
  证明: SkewMonoidAlgebra.single_left_inj ha

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.single_left_inj, single_left_inj
-/
lemma monomial_left_inj {R : Type*} [Semiring R] {a : R} (ha : a != 0) {i j : Nat} :
    (monomial i a) = (monomial j a) ↔ i = j :=
  SkewMonoidAlgebra.single_left_inj ha

/--
lemma `nat_cast_mul` / 引理 `nat_cast_mul`

English:
lemma nat_cast_mul
  statement: {R : Type*} [Semiring R] (n : Nat) (p : SkewPolynomial R)
  proof: (nsmul_eq_mul _ _).symm

中文:
引理 nat_cast_mul
  结论: {R : 类型} [Semiring R] (n : 自然数) (p : SkewPolynomial R)
  证明: (nsmul_eq_mul _ _).symm

Depends on / 依赖: nsmul_eq_mul
-/
lemma nat_cast_mul {R : Type*} [Semiring R] (n : Nat) (p : SkewPolynomial R)
    [MulSemiringAction (Multiplicative Nat) R] : (n : SkewPolynomial R) * p = n • p :=
  (nsmul_eq_mul _ _).symm
section Sum

variable {S : Type*} [AddCommMonoid S]

/--
lemma `sum_eq_of_subset` / 引理 `sum_eq_of_subset`

English:
lemma sum_eq_of_subset
  statement: {p : SkewPolynomial R} (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {s : Finset Nat}
  proof: by
  rw [sum_def]; rw [Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

@[simp]

中文:
引理 sum_eq_of_subset
  结论: {p : SkewPolynomial R} (f : 自然数 -> R -> S) (hf : 对任意 i, f i 0 = 0) {s : Finset 自然数}
  证明: by
  rw [sum_def]; rw [Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

@[simp]

Depends on / 依赖: Finset, Finset.sum_subset, mem_support_iff, ne_eq, not_not, sum_def, sum_subset
-/
lemma sum_eq_of_subset {p : SkewPolynomial R} (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {s : Finset Nat}
    (hs : p.support subseteq s) : p.sum f = ∑ n in s, f n (p.coeff n) := by
  rw [sum_def]; rw [Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

@[simp]
/--
lemma `sum_zero_index` / 引理 `sum_zero_index`

English:
lemma sum_zero_index
  given: (f : Nat -> R -> S)
  statement: (0 : SkewPolynomial R).sum f = 0
  proof: by
  simp [sum_def', zero_def]

@[simp]

中文:
引理 sum_zero_index
  条件: (f : 自然数 -> R -> S)
  结论: (0 : SkewPolynomial R).sum f = 0
  证明: by
  simp [sum_def', zero_def]

@[simp]

Depends on / 依赖: sum_def, zero_def
-/
lemma sum_zero_index (f : Nat -> R -> S) : (0 : SkewPolynomial R).sum f = 0 := by
  simp [sum_def', zero_def]

@[simp]
/--
lemma `sum_X_index` / 引理 `sum_X_index`

English:
lemma sum_X_index
  given: {f : Nat -> R -> S} (hf : f 1 0 = 0)
  statement: (X : SkewPolynomial R).sum f = f 1 1
  proof: sum_monomial_index hf

中文:
引理 sum_X_index
  条件: {f : 自然数 -> R -> S} (hf : f 1 0 = 0)
  结论: (X : SkewPolynomial R).sum f = f 1 1
  证明: sum_monomial_index hf

Depends on / 依赖: sum_monomial_index
-/
lemma sum_X_index {f : Nat -> R -> S} (hf : f 1 0 = 0) : (X : SkewPolynomial R).sum f = f 1 1 :=
  sum_monomial_index hf

/--
lemma `sum_add_index` / 引理 `sum_add_index`

English:
lemma sum_add_index
  statement: (p q : SkewPolynomial R) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0)
  proof: by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ => hf (toAdd n)) (fun n _ => h_add (toAdd n))

中文:
引理 sum_add_index
  结论: (p q : SkewPolynomial R) (f : 自然数 -> R -> S) (hf : 对任意 i, f i 0 = 0)
  证明: by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ => hf (toAdd n)) (fun n _ => h_add (toAdd n))

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.sum_add_index, h_add, sum_add_index, sum_def
-/
lemma sum_add_index (p q : SkewPolynomial R) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0)
    (h_add : forall a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ => hf (toAdd n)) (fun n _ => h_add (toAdd n))

/-- See also `SkewPolynomial.sum_add`. -/
@[simp]
/--
lemma `sum_add'` / 引理 `sum_add'`

English:
lemma sum_add'
  given: (p : SkewPolynomial R) (f g : Nat -> R -> S)
  statement: p.sum (f + g) = p.sum f + p.sum g
  proof: by
  simp [sum_def, Finset.sum_add_distrib]

中文:
引理 sum_add'
  条件: (p : SkewPolynomial R) (f g : 自然数 -> R -> S)
  结论: p.sum (f + g) = p.sum f + p.sum g
  证明: by
  simp [sum_def, Finset.sum_add_distrib]

Depends on / 依赖: Finset, Finset.sum_add_distrib, sum_add_distrib, sum_def
-/
lemma sum_add' (p : SkewPolynomial R) (f g : Nat -> R -> S) : p.sum (f + g) = p.sum f + p.sum g := by
  simp [sum_def, Finset.sum_add_distrib]

/-- See also `SkewPolynomial.sum_add'`. -/
@[simp]
/--
lemma `sum_add` / 引理 `sum_add`

English:
lemma sum_add
  given: (p : SkewPolynomial R) (f g : Nat -> R -> S)
  proof: sum_add' _ _ _

中文:
引理 sum_add
  条件: (p : SkewPolynomial R) (f g : 自然数 -> R -> S)
  证明: sum_add' _ _ _

Depends on / 依赖: sum_add
-/
lemma sum_add (p : SkewPolynomial R) (f g : Nat -> R -> S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

/--
lemma `sum_smul_index` / 引理 `sum_smul_index`

English:
lemma sum_smul_index
  given: (p : SkewPolynomial R) (b : R) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0)
  proof: Finsupp.sum_smul_index hf

中文:
引理 sum_smul_index
  条件: (p : SkewPolynomial R) (b : R) (f : 自然数 -> R -> S) (hf : 对任意 i, f i 0 = 0)
  证明: Finsupp.sum_smul_index hf

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, sum_smul_index
-/
lemma sum_smul_index (p : SkewPolynomial R) (b : R) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) :
    (b • p).sum f = p.sum fun n a => f n (b * a) :=
  Finsupp.sum_smul_index hf

/--
lemma `sum_smul_index'` / 引理 `sum_smul_index'`

English:
lemma sum_smul_index'
  statement: {T : Type*} [DistribSMul T R] (p : SkewPolynomial R) (b : T) (f : Nat -> R -> S)
  proof: Finsupp.sum_smul_index' hf

中文:
引理 sum_smul_index'
  结论: {T : 类型} [DistribSMul T R] (p : SkewPolynomial R) (b : T) (f : 自然数 -> R -> S)
  证明: Finsupp.sum_smul_index' hf

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, sum_smul_index
-/
lemma sum_smul_index' {T : Type*} [DistribSMul T R] (p : SkewPolynomial R) (b : T) (f : Nat -> R -> S)
    (hf : forall i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) :=
  Finsupp.sum_smul_index' hf

/--
lemma `smul_sum` / 引理 `smul_sum`

English:
lemma smul_sum
  statement: {T : Type*} [DistribSMul T S] (p : SkewPolynomial R) (b : T)
  proof: Finsupp.smul_sum

中文:
引理 smul_sum
  结论: {T : 类型} [DistribSMul T S] (p : SkewPolynomial R) (b : T)
  证明: Finsupp.smul_sum
-/
protected lemma smul_sum {T : Type*} [DistribSMul T S] (p : SkewPolynomial R) (b : T)
    (f : Nat -> R -> S) : b • p.sum f = p.sum fun n a => b • f n a :=
  Finsupp.smul_sum

end Sum

@[simp]
/--
lemma `coeff_add` / 引理 `coeff_add`

English:
lemma coeff_add
  given: (p q : SkewPolynomial R) (n : Nat)
  statement: coeff (p + q) n = coeff p n + coeff q n
  proof: by
  simp [coeff]

中文:
引理 coeff_add
  条件: (p q : SkewPolynomial R) (n : 自然数)
  结论: coeff (p + q) n = coeff p n + coeff q n
  证明: by
  simp [coeff]
-/
lemma coeff_add (p q : SkewPolynomial R) (n : Nat) : coeff (p + q) n = coeff p n + coeff q n := by
  simp [coeff]

end Semiring

section Ring

variable [Ring R] {a b : R}

/--
lemma `sum_neg` / 引理 `sum_neg`

English:
lemma sum_neg
  given: {S : Type*} [Ring S] (p : SkewPolynomial R) (f : Nat -> R -> S)
  proof: by
  simp [sum_def, Finset.sum_neg_distrib]

中文:
引理 sum_neg
  条件: {S : 类型} [Ring S] (p : SkewPolynomial R) (f : 自然数 -> R -> S)
  证明: by
  simp [sum_def, Finset.sum_neg_distrib]
-/
@[simp] lemma sum_neg {S : Type*} [Ring S] (p : SkewPolynomial R) (f : Nat -> R -> S) :
    (p.sum fun n x => - f n x) = - p.sum f := by
  simp [sum_def, Finset.sum_neg_distrib]

/--
lemma `sum_sub` / 引理 `sum_sub`

English:
lemma sum_sub
  given: {S : Type*} [Ring S] (p : SkewPolynomial R) (f g : Nat -> R -> S)
  proof: by
  simp only [sub_eq_add_neg, sum_add, sum_neg]

中文:
引理 sum_sub
  条件: {S : 类型} [Ring S] (p : SkewPolynomial R) (f g : 自然数 -> R -> S)
  证明: by
  simp only [sub_eq_add_neg, sum_add, sum_neg]
-/
@[simp] lemma sum_sub {S : Type*} [Ring S] (p : SkewPolynomial R) (f g : Nat -> R -> S) :
    (p.sum fun n x => f n x - g n x) = p.sum f - p.sum g := by
  simp only [sub_eq_add_neg, sum_add, sum_neg]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [MulSemiringAction (Multiplicative Nat) R]
  body: SkewMonoidAlgebra.instRing

@[simp]

中文:
实例 instRing
  签名: [MulSemiringAction (Multiplicative 自然数) R]
  定义体: SkewMonoidAlgebra.instRing

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.instRing, instRing
-/
instance instRing [MulSemiringAction (Multiplicative Nat) R] : Ring (SkewPolynomial R) :=
  SkewMonoidAlgebra.instRing

@[simp]
/--
lemma `coeff_neg` / 引理 `coeff_neg`

English:
lemma coeff_neg
  given: (p : SkewPolynomial R) (n : Nat)
  statement: coeff (-p) n = -coeff p n
  proof: by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

@[simp]

中文:
引理 coeff_neg
  条件: (p : SkewPolynomial R) (n : 自然数)
  结论: coeff (-p) n = -coeff p n
  证明: by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

@[simp]

Depends on / 依赖: add_eq_zero_iff_eq_neg, coeff_add, neg_add_cancel
-/
lemma coeff_neg (p : SkewPolynomial R) (n : Nat) : coeff (-p) n = -coeff p n := by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

@[simp]
/--
lemma `coeff_sub` / 引理 `coeff_sub`

English:
lemma coeff_sub
  given: (p q : SkewPolynomial R) (n : Nat)
  statement: coeff (p - q) n = coeff p n - coeff q n
  proof: by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]

中文:
引理 coeff_sub
  条件: (p q : SkewPolynomial R) (n : 自然数)
  结论: coeff (p - q) n = coeff p n - coeff q n
  证明: by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]

Depends on / 依赖: SkewPolynomial, SkewPolynomial.coeff_add, coeff_add, coeff_neg, simp_rw, sub_eq_add_neg
-/
lemma coeff_sub (p q : SkewPolynomial R) (n : Nat) : coeff (p - q) n = coeff p n - coeff q n := by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]

/--
lemma `monomial_neg` / 引理 `monomial_neg`

English:
lemma monomial_neg
  given: (n : Nat) (a : R)
  statement: monomial n (-a) = -(monomial n a)
  proof: by
  rw [eq_neg_iff_add_eq_zero]; rw [← monomial_add]; rw [neg_add_cancel]; rw [monomial_zero_right]

中文:
引理 monomial_neg
  条件: (n : 自然数) (a : R)
  结论: monomial n (-a) = -(monomial n a)
  证明: by
  rw [eq_neg_iff_add_eq_zero]; rw [← monomial_add]; rw [neg_add_cancel]; rw [monomial_zero_right]
-/
@[simp] lemma monomial_neg (n : Nat) (a : R) : monomial n (-a) = -(monomial n a) := by
  rw [eq_neg_iff_add_eq_zero]; rw [← monomial_add]; rw [neg_add_cancel]; rw [monomial_zero_right]

/--
lemma `support_neg` / 引理 `support_neg`

English:
lemma support_neg
  given: {p : SkewPolynomial R}
  statement: (-p).support = p.support
  proof: by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p

中文:
引理 support_neg
  条件: {p : SkewPolynomial R}
  结论: (-p).support = p.support
  证明: by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p
-/
@[simp] lemma support_neg {p : SkewPolynomial R} : (-p).support = p.support := by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p

/--
lemma `monomial_sub` / 引理 `monomial_sub`

English:
lemma monomial_sub
  given: (n : Nat)
  statement: monomial n (a - b) = monomial n a - monomial n b
  proof: by
  rw [sub_eq_add_neg]; rw [monomial_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

中文:
引理 monomial_sub
  条件: (n : 自然数)
  结论: monomial n (a - b) = monomial n a - monomial n b
  证明: by
  rw [sub_eq_add_neg]; rw [monomial_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

Depends on / 依赖: monomial_add, monomial_neg, sub_eq_add_neg
-/
lemma monomial_sub (n : Nat) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg]; rw [monomial_add]; rw [monomial_neg]; rw [sub_eq_add_neg]

variable [MulSemiringAction (Multiplicative Nat) R]

/--
lemma `C_eq_intCast` / 引理 `C_eq_intCast`

English:
lemma C_eq_intCast
  given: (n : Int)
  statement: C (n : R) = n
  proof: by simp [← CRingHom_eq_C]

中文:
引理 C_eq_intCast
  条件: (n : 整数)
  结论: C (n : R) = n
  证明: by simp [← CRingHom_eq_C]

Depends on / 依赖: CRingHom_eq_C
-/
lemma C_eq_intCast (n : Int) : C (n : R) = n := by simp [← CRingHom_eq_C]

/--
lemma `C_neg` / 引理 `C_neg`

English:
lemma C_neg
  statement: C (-a) = -C a
  proof: RingHom.map_neg CRingHom a

中文:
引理 C_neg
  结论: C (-a) = -C a
  证明: RingHom.map_neg CRingHom a

Depends on / 依赖: CRingHom, RingHom, RingHom.map_neg, map_neg
-/
lemma C_neg : C (-a) = -C a := RingHom.map_neg CRingHom a

/--
lemma `C_sub` / 引理 `C_sub`

English:
lemma C_sub
  statement: C (a - b) = C a - C b
  proof: RingHom.map_sub CRingHom a b

中文:
引理 C_sub
  结论: C (a - b) = C a - C b
  证明: RingHom.map_sub CRingHom a b

Depends on / 依赖: CRingHom, RingHom, RingHom.map_sub, map_sub
-/
lemma C_sub : C (a - b) = C a - C b := RingHom.map_sub CRingHom a b

end Ring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R]

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial (SkewPolynomial R)
  body: SkewMonoidAlgebra.instNontrivialOfNonempty

中文:
实例 instNontrivial
  签名: : Nontrivial (SkewPolynomial R)
  定义体: SkewMonoidAlgebra.instNontrivialOfNonempty

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.instNontrivialOfNonempty, instNontrivialOfNonempty
-/
instance instNontrivial : Nontrivial (SkewPolynomial R) :=
  SkewMonoidAlgebra.instNontrivialOfNonempty

/--
lemma `X_ne_zero` / 引理 `X_ne_zero`

English:
lemma X_ne_zero
  statement: (X : SkewPolynomial R) != 0
  proof: mt (congr_arg (fun p => coeff p 1)) (by simp)

中文:
引理 X_ne_zero
  结论: (X : SkewPolynomial R) != 0
  证明: mt (congr_arg (fun p => coeff p 1)) (by simp)

Depends on / 依赖: congr_arg
-/
lemma X_ne_zero : (X : SkewPolynomial R) != 0 := mt (congr_arg (fun p => coeff p 1)) (by simp)

end NontrivialSemiring

section erase

variable [Semiring R]

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (n : Nat) (p : SkewPolynomial R)
  body: SkewMonoidAlgebra.erase (ofAdd n) p

@[simp]

中文:
定义 erase
  签名: (n : 自然数) (p : SkewPolynomial R)
  定义体: SkewMonoidAlgebra.erase (ofAdd n) p

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.erase
-/
def erase (n : Nat) (p : SkewPolynomial R) : SkewPolynomial R :=
  SkewMonoidAlgebra.erase (ofAdd n) p

@[simp]
/--
lemma `support_erase` / 引理 `support_erase`

English:
lemma support_erase
  given: {p : SkewPolynomial R} (n : Nat)
  proof: by
  simp [support_eq_skewMonoidAlgebra_support, erase]

中文:
引理 support_erase
  条件: {p : SkewPolynomial R} (n : 自然数)
  证明: by
  simp [support_eq_skewMonoidAlgebra_support, erase]

Depends on / 依赖: support_eq_skewMonoidAlgebra_support
-/
lemma support_erase {p : SkewPolynomial R} (n : Nat) :
    support (p.erase n) = (support p).erase n := by
  simp [support_eq_skewMonoidAlgebra_support, erase]

/--
lemma `monomial_add_erase` / 引理 `monomial_add_erase`

English:
lemma monomial_add_erase
  given: (p : SkewPolynomial R) (n : Nat)
  proof: by
  simp [coeff, monomial_def, erase, SkewMonoidAlgebra.single_add_erase]

@[simp]

中文:
引理 monomial_add_erase
  条件: (p : SkewPolynomial R) (n : 自然数)
  证明: by
  simp [coeff, monomial_def, erase, SkewMonoidAlgebra.single_add_erase]

@[simp]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.single_add_erase, monomial_def, single_add_erase
-/
lemma monomial_add_erase (p : SkewPolynomial R) (n : Nat) :
    monomial n (coeff p n) + p.erase n = p := by
  simp [coeff, monomial_def, erase, SkewMonoidAlgebra.single_add_erase]

@[simp]
/--
lemma `coeff_erase` / 引理 `coeff_erase`

English:
lemma coeff_erase
  given: (p : SkewPolynomial R) (n i : Nat)
  proof: by
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]

中文:
引理 coeff_erase
  条件: (p : SkewPolynomial R) (n i : 自然数)
  证明: by
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]

Depends on / 依赖: ite_congr
-/
lemma coeff_erase (p : SkewPolynomial R) (n i : Nat) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]
/--
lemma `erase_zero` / 引理 `erase_zero`

English:
lemma erase_zero
  given: (n : Nat)
  statement: (0 : SkewPolynomial R).erase n = 0
  proof: by
  simp [erase, zero_def]

@[simp]

中文:
引理 erase_zero
  条件: (n : 自然数)
  结论: (0 : SkewPolynomial R).erase n = 0
  证明: by
  simp [erase, zero_def]

@[simp]

Depends on / 依赖: zero_def
-/
lemma erase_zero (n : Nat) : (0 : SkewPolynomial R).erase n = 0 := by
  simp [erase, zero_def]

@[simp]
/--
lemma `erase_monomial` / 引理 `erase_monomial`

English:
lemma erase_monomial
  given: {n : Nat} {a : R}
  statement: erase n (monomial n a) = 0
  proof: by
  simp [erase, monomial_def, zero_def]

@[deprecated coeff_erase (since := "2026-07-06")]

中文:
引理 erase_monomial
  条件: {n : 自然数} {a : R}
  结论: erase n (monomial n a) = 0
  证明: by
  simp [erase, monomial_def, zero_def]

@[deprecated coeff_erase (since := "2026-07-06")]

Depends on / 依赖: monomial_def, zero_def
-/
lemma erase_monomial {n : Nat} {a : R} : erase n (monomial n a) = 0 := by
  simp [erase, monomial_def, zero_def]

@[deprecated coeff_erase (since := "2026-07-06")]
/--
lemma `erase_same` / 引理 `erase_same`

English:
lemma erase_same
  given: (p : SkewPolynomial R) (n : Nat)
  statement: coeff (p.erase n) n = 0
  proof: by
    simp [coeff_erase]

@[deprecated coeff_erase (since := "2026-07-06")]

中文:
引理 erase_same
  条件: (p : SkewPolynomial R) (n : 自然数)
  结论: coeff (p.erase n) n = 0
  证明: by
    simp [coeff_erase]

@[deprecated coeff_erase (since := "2026-07-06")]

Depends on / 依赖: coeff_erase
-/
lemma erase_same (p : SkewPolynomial R) (n : Nat) : coeff (p.erase n) n = 0 := by
    simp [coeff_erase]

@[deprecated coeff_erase (since := "2026-07-06")]
/--
lemma `erase_ne` / 引理 `erase_ne`

English:
lemma erase_ne
  given: (p : SkewPolynomial R) {n i : Nat} (h : i != n)
  proof: by
  simp [coeff_erase, h]

中文:
引理 erase_ne
  条件: (p : SkewPolynomial R) {n i : 自然数} (h : i != n)
  证明: by
  simp [coeff_erase, h]

Depends on / 依赖: coeff_erase
-/
lemma erase_ne (p : SkewPolynomial R) {n i : Nat} (h : i != n) :
    coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

end erase

section update

variable [Semiring R]

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (p : SkewPolynomial R) (n : Nat) (a : R)
  body: SkewMonoidAlgebra.update p (ofAdd n) a

中文:
定义 update
  签名: (p : SkewPolynomial R) (n : 自然数) (a : R)
  定义体: SkewMonoidAlgebra.update p (ofAdd n) a

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.update, update
-/
def update (p : SkewPolynomial R) (n : Nat) (a : R) : SkewPolynomial R :=
  SkewMonoidAlgebra.update p (ofAdd n) a

/--
lemma `update_def` / 引理 `update_def`

English:
lemma update_def
  given: (p : SkewPolynomial R) (n : Nat) (a : R)
  proof: rfl

@[simp]

中文:
引理 update_def
  条件: (p : SkewPolynomial R) (n : 自然数) (a : R)
  证明: rfl

@[simp]
-/
lemma update_def (p : SkewPolynomial R) (n : Nat) (a : R) :
    p.update n a = SkewMonoidAlgebra.update p (ofAdd n) a := rfl

@[simp]
/--
lemma `coeff_update` / 引理 `coeff_update`

English:
lemma coeff_update
  given: (p : SkewPolynomial R) (n : Nat) (a : R)
  proof: by
  ext; simp [coeff, update]; rfl

@[deprecated coeff_update (since := "2026-07-06")]

中文:
引理 coeff_update
  条件: (p : SkewPolynomial R) (n : 自然数) (a : R)
  证明: by
  ext; simp [coeff, update]; rfl

@[deprecated coeff_update (since := "2026-07-06")]

Depends on / 依赖: update
-/
lemma coeff_update (p : SkewPolynomial R) (n : Nat) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by
  ext; simp [coeff, update]; rfl

@[deprecated coeff_update (since := "2026-07-06")]
/--
lemma `coeff_update_apply` / 引理 `coeff_update_apply`

English:
lemma coeff_update_apply
  given: (p : SkewPolynomial R) (n : Nat) (a : R) (i : Nat)
  proof: SkewMonoidAlgebra.coeff_update_apply _ _ _ _

@[deprecated coeff_update (since := "2026-07-06")]

中文:
引理 coeff_update_apply
  条件: (p : SkewPolynomial R) (n : 自然数) (a : R) (i : 自然数)
  证明: SkewMonoidAlgebra.coeff_update_apply _ _ _ _

@[deprecated coeff_update (since := "2026-07-06")]

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.coeff_update_apply, coeff_update_apply
-/
lemma coeff_update_apply (p : SkewPolynomial R) (n : Nat) (a : R) (i : Nat) :
    (p.update n a).coeff i = if i = n then a else p.coeff i :=
  SkewMonoidAlgebra.coeff_update_apply _ _ _ _

@[deprecated coeff_update (since := "2026-07-06")]
/--
lemma `coeff_update_same` / 引理 `coeff_update_same`

English:
lemma coeff_update_same
  given: (p : SkewPolynomial R) (n : Nat) (a : R)
  statement: (p.update n a).coeff n = a
  proof: by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

@[deprecated coeff_update (since := "2026-07-06")]

中文:
引理 coeff_update_same
  条件: (p : SkewPolynomial R) (n : 自然数) (a : R)
  结论: (p.update n a).coeff n = a
  证明: by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

@[deprecated coeff_update (since := "2026-07-06")]

Depends on / 依赖: coeff_update_apply, if_pos, p.coeff_update_apply
-/
lemma coeff_update_same (p : SkewPolynomial R) (n : Nat) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply]; rw [if_pos rfl]

@[deprecated coeff_update (since := "2026-07-06")]
/--
lemma `coeff_update_ne` / 引理 `coeff_update_ne`

English:
lemma coeff_update_ne
  given: (p : SkewPolynomial R) {n i : Nat} (a : R) (h : i != n)
  proof: by rw [p.coeff_update_apply, if_neg h]

@[simp]

中文:
引理 coeff_update_ne
  条件: (p : SkewPolynomial R) {n i : 自然数} (a : R) (h : i != n)
  证明: by rw [p.coeff_update_apply, if_neg h]

@[simp]

Depends on / 依赖: coeff_update_apply, if_neg, p.coeff_update_apply
-/
lemma coeff_update_ne (p : SkewPolynomial R) {n i : Nat} (a : R) (h : i != n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
/--
lemma `update_zero_eq_erase` / 引理 `update_zero_eq_erase`

English:
lemma update_zero_eq_erase
  given: (p : SkewPolynomial R) (n : Nat)
  statement: p.update n 0 = p.erase n
  proof: by
  ext; simp [Function.update_apply]

中文:
引理 update_zero_eq_erase
  条件: (p : SkewPolynomial R) (n : 自然数)
  结论: p.update n 0 = p.erase n
  证明: by
  ext; simp [Function.update_apply]

Depends on / 依赖: Function, Function.update_apply, update_apply
-/
lemma update_zero_eq_erase (p : SkewPolynomial R) (n : Nat) : p.update n 0 = p.erase n := by
  ext; simp [Function.update_apply]

/--
lemma `support_update` / 引理 `support_update`

English:
lemma support_update
  given: (p : SkewPolynomial R) (n : Nat) (a : R) [DecidableEq R]
  proof: by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs <;> simp

中文:
引理 support_update
  条件: (p : SkewPolynomial R) (n : 自然数) (a : R) [DecidableEq R]
  证明: by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs <;> simp

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.support_update, split_ifs, support_eq_skewMonoidAlgebra_support, support_update, update_def
-/
lemma support_update (p : SkewPolynomial R) (n : Nat) (a : R) [DecidableEq R] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs <;> simp

/--
lemma `support_update_zero` / 引理 `support_update_zero`

English:
lemma support_update_zero
  given: (p : SkewPolynomial R) (n : Nat)
  proof: by
  simp

中文:
引理 support_update_zero
  条件: (p : SkewPolynomial R) (n : 自然数)
  证明: by
  simp
-/
lemma support_update_zero (p : SkewPolynomial R) (n : Nat) :
    support (p.update n 0) = p.support.erase n := by
  simp

/--
lemma `support_update_ne_zero` / 引理 `support_update_ne_zero`

English:
lemma support_update_ne_zero
  given: (p : SkewPolynomial R) (n : Nat) {a : R} (ha : a != 0)
  proof: by classical rw [support_update, if_neg ha]

中文:
引理 support_update_ne_zero
  条件: (p : SkewPolynomial R) (n : 自然数) {a : R} (ha : a != 0)
  证明: by classical rw [support_update, if_neg ha]

Depends on / 依赖: classical, if_neg, support_update
-/
lemma support_update_ne_zero (p : SkewPolynomial R) (n : Nat) {a : R} (ha : a != 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end update

end SkewPolynomial
