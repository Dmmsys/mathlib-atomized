/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Degree, leading coefficient and leading term of polynomials with respect to a monomial order

We consider a type `σ` of indeterminates and a commutative semiring `R`
and a monomial order `m : MonomialOrder σ`.

* `m.degree f` is the degree of `f` for the monomial ordering `m`, where the polynomial `0` has
  degree `0`. For the variant mapping polynomial `0` to `⊥` which is less than `0`, see
  `MonomialOrder.withBotDegree`.

* `m.leadingCoeff f` is the leading coefficient of `f` for the monomial ordering `m`.

* `m.Monic f` asserts that the leading coefficient of `f` is `1`.

* `m.leadingTerm f` is the leading term of `f` for the monomial ordering `m`.

* `m.sPolynomial f g` is S-polynomial of `f` and `g`.

* `m.withBotDegree f` is the degree of `f` for the monomial ordering `m`, where the polynomial `0`
  has degree `⊥`, which is not equal to `0`. `MonomialOrder.withBotDegree` is to
  `MonomialOrder.degree` as `Polynomial.degree` is to `Polynomial.natDegree`.

* `m.leadingCoeff_ne_zero_iff f` asserts that this coefficient is nonzero iff `f ≠ 0`.

* in a field, `m.isUnit_leadingCoeff f` asserts that this coefficient is a unit iff `f ≠ 0`.

* `m.degree_add_le` : the `m.degree` of `f + g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_add_of_lt h` : the `m.degree` of `f + g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_add_of_lt h`: then, the leading coefficient of `f + g` is that of `f`.

* `m.degree_add_of_ne h` : the `m.degree` of `f + g` is equal to that the supremum
  of those of `f` and `g` if they are distinct.

* `m.degree_sub_le` : the `m.degree` of `f - g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_sub_of_lt h` : the `m.degree` of `f - g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_sub_of_lt h`: then, the leading coefficient of `f - g` is that of `f`.

* `m.degree_mul_le`: the `m.degree` of `f * g` is smaller than or equal to the sum of those of
  `f` and `g`.

* `m.degree_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the degree is the sum of the degrees.

* `m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the leading coefficient is that product.

* `m.degree_mul_of_left_mem_nonZeroDivisors`, `m.degree_mul_of_right_mem_nonZeroDivisors` and
  `m.degree_mul` assert the equality when the leading coefficient of `f` or `g` isn't zero divisors,
  or when `R` is a domain and `f` and `g` are nonzero.

* `m.leadingCoeff_mul_of_left_mem_nonZeroDivisors`,
  `m.leadingCoeff_mul_of_right_mem_nonZeroDivisors`
  and `m.leadingCoeff_mul` say that `m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g`

* `m.degree_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the degree of `f ^ n` is `n • (m.degree f)`

* `m.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the leading coefficient of `f ^ n` is that power.

* `m.degree_prod_of_mem_nonZeroDivisors` : the degree of a product of polynomials whose leading
  coefficients aren't zero divisors is the sum of their degrees.

* `m.leadingCoeff_prod_of_mem_nonZeroDivisors` : the leading coefficient of a product of polynomials
  whose leading coefficients aren't zero divisors is the product of their leading coefficients.

* `m.Monic.prod` : a product of monic polynomials is monic.

* `m.degree_sub_leadingTerm_lt_iff` : the degree of `f - m.leadingTerm f` is smaller than the
  degree of `f` if and only if `m.degree f ≠ 0`.

## Reference

[Becker-Weispfenning1993]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder nonZeroDivisors

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in
/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: (f : MvPolynomial σ R)
  body: m.toSyn.symm (f.support.sup m.toSyn)

中文:
定义 degree
  签名: (f : 多元多项式 σ R)
  定义体: m.toSyn.symm (f.support.sup m.toSyn)

Depends on / 依赖: f.support.sup, m.toSyn, m.toSyn.symm, support
-/
noncomputable def degree (f : MvPolynomial σ R) : σ ->₀ Nat :=
  m.toSyn.symm (f.support.sup m.toSyn)

variable (m) in
/--
Definition of `leadingCoeff` / `leadingCoeff` 的定义

English:
definition leadingCoeff
  signature: (f : MvPolynomial σ R)
  body: f.coeff (m.degree f)

中文:
定义 leadingCoeff
  签名: (f : 多元多项式 σ R)
  定义体: f.coeff (m.degree f)

Depends on / 依赖: degree, f.coeff, m.degree
-/
noncomputable def leadingCoeff (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

variable (m) in
/--
Definition of `Monic` / `Monic` 的定义

English:
definition Monic
  signature: (f : MvPolynomial σ R)
  body: m.leadingCoeff f = 1

中文:
定义 Monic
  签名: (f : 多元多项式 σ R)
  定义体: m.leadingCoeff f = 1

Depends on / 依赖: leadingCoeff, m.leadingCoeff
-/
def Monic (f : MvPolynomial σ R) : Prop :=
  m.leadingCoeff f = 1

variable (m) in
/--
Definition of `leadingTerm` / `leadingTerm` 的定义

English:
definition leadingTerm
  signature: (f : MvPolynomial σ R)
  body: monomial (m.degree f) (m.leadingCoeff f)

@[simp]

中文:
定义 leadingTerm
  签名: (f : 多元多项式 σ R)
  定义体: monomial (m.degree f) (m.leadingCoeff f)

@[simp]

Depends on / 依赖: degree, leadingCoeff, m.degree, m.leadingCoeff, monomial
-/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

@[simp]
/--
lemma `C_mul_leadingCoeff_monomial_degree` / 引理 `C_mul_leadingCoeff_monomial_degree`

English:
lemma C_mul_leadingCoeff_monomial_degree
  given: (p : MvPolynomial σ R)
  proof: by
  rw [MvPolynomial.C_mul_monomial]; rw [mul_one]; rw [leadingTerm]

中文:
引理 C_mul_leadingCoeff_monomial_degree
  条件: (p : 多元多项式 σ R)
  证明: by
  rw [MvPolynomial.C_mul_monomial]; rw [mul_one]; rw [leadingTerm]

Depends on / 依赖: C_mul_monomial, MvPolynomial, MvPolynomial.C_mul_monomial, leadingTerm, mul_one
-/
lemma C_mul_leadingCoeff_monomial_degree (p : MvPolynomial σ R) :
    MvPolynomial.C (m.leadingCoeff p : R) * MvPolynomial.monomial (m.degree p) (1 : R) =
      m.leadingTerm p := by
  rw [MvPolynomial.C_mul_monomial]; rw [mul_one]; rw [leadingTerm]

/--
theorem `Monic.of_subsingleton` / 定理 `Monic.of_subsingleton`

English:
theorem Monic.of_subsingleton
  given: [Subsingleton R] {f : MvPolynomial σ R}
  proof: Subsingleton.eq_one (m.leadingCoeff f)

中文:
定理 Monic.of_subsingleton
  条件: [子单例 R] {f : 多元多项式 σ R}
  证明: Subsingleton.eq_one (m.leadingCoeff f)
-/
@[nontriviality] theorem Monic.of_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.Monic f :=
  Subsingleton.eq_one (m.leadingCoeff f)

/--
Instance `Monic.decidable` / 实例 `Monic.decidable`

English:
instance Monic.decidable
  signature: [DecidableEq R] (f : MvPolynomial σ R)
  body: inferInstanceAs Decidable (m.leadingCoeff f = 1)

@[simp]

中文:
实例 Monic.decidable
  签名: [DecidableEq R] (f : 多元多项式 σ R)
  定义体: inferInstanceAs Decidable (m.leadingCoeff f = 1)

@[simp]
-/
noncomputable instance Monic.decidable [DecidableEq R] (f : MvPolynomial σ R) :
    Decidable (m.Monic f) :=
inferInstanceAs Decidable (m.leadingCoeff f = 1)

@[simp]
/--
theorem `Monic.leadingCoeff_eq_one` / 定理 `Monic.leadingCoeff_eq_one`

English:
theorem Monic.leadingCoeff_eq_one
  given: {f : MvPolynomial σ R} (hf : m.Monic f)
  statement: m.leadingCoeff f = 1
  proof: hf

中文:
定理 Monic.leadingCoeff_eq_one
  条件: {f : 多元多项式 σ R} (hf : m.Monic f)
  结论: m.leadingCoeff f = 1
  证明: hf
-/
theorem Monic.leadingCoeff_eq_one {f : MvPolynomial σ R} (hf : m.Monic f) : m.leadingCoeff f = 1 :=
  hf

/--
theorem `Monic.coeff_degree` / 定理 `Monic.coeff_degree`

English:
theorem Monic.coeff_degree
  given: {f : MvPolynomial σ R} (hf : m.Monic f)
  statement: f.coeff (m.degree f) = 1
  proof: hf

@[simp]

中文:
定理 Monic.coeff_degree
  条件: {f : 多元多项式 σ R} (hf : m.Monic f)
  结论: f.coeff (m.degree f) = 1
  证明: hf

@[simp]
-/
theorem Monic.coeff_degree {f : MvPolynomial σ R} (hf : m.Monic f) : f.coeff (m.degree f) = 1 :=
  hf

@[simp]
/--
theorem `degree_zero` / 定理 `degree_zero`

English:
theorem degree_zero
  statement: m.degree (0 : MvPolynomial σ R) = 0
  proof: by
  simp [degree]

中文:
定理 degree_zero
  结论: m.degree (0 : 多元多项式 σ R) = 0
  证明: by
  simp [degree]

Depends on / 依赖: degree
-/
theorem degree_zero : m.degree (0 : MvPolynomial σ R) = 0 := by
  simp [degree]

/--
theorem `ne_zero_of_degree_ne_zero` / 定理 `ne_zero_of_degree_ne_zero`

English:
theorem ne_zero_of_degree_ne_zero
  given: {f : MvPolynomial σ R} (h : m.degree f != 0)
  statement: f != 0
  proof: by
  rintro rfl
  exact h m.degree_zero

@[simp, nontriviality]

中文:
定理 ne_zero_of_degree_ne_zero
  条件: {f : 多元多项式 σ R} (h : m.degree f != 0)
  结论: f != 0
  证明: by
  rintro rfl
  exact h m.degree_zero

@[simp, nontriviality]

Depends on / 依赖: degree_zero, m.degree_zero
-/
theorem ne_zero_of_degree_ne_zero {f : MvPolynomial σ R} (h : m.degree f != 0) : f != 0 := by
  rintro rfl
  exact h m.degree_zero

@[simp, nontriviality]
/--
theorem `degree_subsingleton` / 定理 `degree_subsingleton`

English:
theorem degree_subsingleton
  given: [Subsingleton R] {f : MvPolynomial σ R}
  proof: by
  rw [Subsingleton.eq_zero f]; rw [degree_zero]

@[simp]

中文:
定理 degree_subsingleton
  条件: [子单例 R] {f : 多元多项式 σ R}
  证明: by
  rw [Subsingleton.eq_zero f]; rw [degree_zero]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, degree_zero, eq_zero
-/
theorem degree_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.degree f = 0 := by
  rw [Subsingleton.eq_zero f]; rw [degree_zero]

@[simp]
/--
theorem `leadingCoeff_zero` / 定理 `leadingCoeff_zero`

English:
theorem leadingCoeff_zero
  statement: m.leadingCoeff (0 : MvPolynomial σ R) = 0
  proof: by
  simp [degree, leadingCoeff]

中文:
定理 leadingCoeff_zero
  结论: m.leadingCoeff (0 : 多元多项式 σ R) = 0
  证明: by
  simp [degree, leadingCoeff]

Depends on / 依赖: TopologicalSpace, continuousInv_of_discreteTopology, degree, leadingCoeff
-/
theorem leadingCoeff_zero : m.leadingCoeff (0 : MvPolynomial σ R) = 0 := by
  simp [degree, leadingCoeff]

/--
theorem `Monic.ne_zero` / 定理 `Monic.ne_zero`

English:
theorem Monic.ne_zero
  given: [Nontrivial R] {f : MvPolynomial σ R} (hf : m.Monic f)
  proof: by
  rintro rfl
  simp [Monic, leadingCoeff_zero] at hf

中文:
定理 Monic.ne_zero
  条件: [非平凡 R] {f : 多元多项式 σ R} (hf : m.Monic f)
  证明: by
  rintro rfl
  simp [Monic, leadingCoeff_zero] at hf

Depends on / 依赖: TopologicalSpace, continuousInv_of_indiscreteTopology
-/
theorem Monic.ne_zero [Nontrivial R] {f : MvPolynomial σ R} (hf : m.Monic f) :
    f != 0 := by
  rintro rfl
  simp [Monic, leadingCoeff_zero] at hf

/--
theorem `degree_monomial_le` / 定理 `degree_monomial_le`

English:
theorem degree_monomial_le
  given: {d : σ ->₀ Nat} (c : R)
  proof: by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

中文:
定理 degree_monomial_le
  条件: {d : σ ->₀ 自然数} (c : R)
  证明: by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, Finset, Finset.sup_mono, Finset.sup_singleton, TopologicalSpace, apply_symm_apply, continuousDiv_of_discreteTopology, degree, le_refl, le_trans, sup_mono, sup_singleton, support_monomial_subset
-/
theorem degree_monomial_le {d : σ ->₀ Nat} (c : R) :
    m.degree (monomial d c) ≼[m] d := by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

/--
theorem `degree_monomial` / 定理 `degree_monomial`

English:
theorem degree_monomial
  given: {d : σ ->₀ Nat} (c : R) [Decidable (c = 0)]
  proof: by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

中文:
定理 degree_monomial
  条件: {d : σ ->₀ 自然数} (c : R) [可判定 (c = 0)]
  证明: by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

Depends on / 依赖: TopologicalSpace, continuousDiv_of_indiscreteTopology, degree, split_ifs, support_monomial
-/
theorem degree_monomial {d : σ ->₀ Nat} (c : R) [Decidable (c = 0)] :
    m.degree (monomial d c) = if c = 0 then 0 else d := by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

/--
theorem `degree_X_le_single` / 定理 `degree_X_le_single`

English:
theorem degree_X_le_single
  given: {s : σ}
  statement: m.degree (X s : MvPolynomial σ R) ≼[m] Finsupp.single s 1
  proof: degree_monomial_le 1

中文:
定理 degree_X_le_single
  条件: {s : σ}
  结论: m.degree (X s : 多元多项式 σ R) ≼[m] 有限支撑.single s 1
  证明: degree_monomial_le 1

Depends on / 依赖: degree_monomial_le, topologicalGroup_of_discreteTopology
-/
theorem degree_X_le_single {s : σ} : m.degree (X s : MvPolynomial σ R) ≼[m] Finsupp.single s 1 :=
  degree_monomial_le 1

/--
theorem `degree_X` / 定理 `degree_X`

English:
theorem degree_X
  given: [Nontrivial R] {s : σ}
  proof: by
  classical
  change m.degree (monomial (Finsupp.single s 1) (1 : R)) = _
  rw [degree_monomial]; rw [if_neg one_ne_zero]

中文:
定理 degree_X
  条件: [非平凡 R] {s : σ}
  证明: by
  classical
  change m.degree (monomial (Finsupp.single s 1) (1 : R)) = _
  rw [degree_monomial]; rw [if_neg one_ne_zero]

Depends on / 依赖: Finsupp, Finsupp.single, classical, degree, degree_monomial, if_neg, m.degree, monomial, one_ne_zero, single, topologicalGroup_of_indiscreteTopology
-/
theorem degree_X [Nontrivial R] {s : σ} :
    m.degree (X s : MvPolynomial σ R) = Finsupp.single s 1 := by
  classical
  change m.degree (monomial (Finsupp.single s 1) (1 : R)) = _
  rw [degree_monomial]; rw [if_neg one_ne_zero]

/--
theorem `degree_one` / 定理 `degree_one`

English:
theorem degree_one
  statement: m.degree (1 : MvPolynomial σ R) = 0
  proof: by
  nontriviality R
  classical rw [MvPolynomial.one_def, degree_monomial]
  simp

@[simp]

中文:
定理 degree_one
  结论: m.degree (1 : 多元多项式 σ R) = 0
  证明: by
  nontriviality R
  classical rw [MvPolynomial.one_def, degree_monomial]
  simp

@[simp]
-/
@[simp] theorem degree_one : m.degree (1 : MvPolynomial σ R) = 0 := by
  nontriviality R
  classical rw [MvPolynomial.one_def, degree_monomial]
  simp

@[simp]
/--
theorem `leadingCoeff_monomial` / 定理 `leadingCoeff_monomial`

English:
theorem leadingCoeff_monomial
  given: {d : σ ->₀ Nat} (c : R)
  proof: by
  classical
  simp only [leadingCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

中文:
定理 leadingCoeff_monomial
  条件: {d : σ ->₀ 自然数} (c : R)
  证明: by
  classical
  simp only [leadingCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

Depends on / 依赖: classical, degree_monomial, leadingCoeff, split_ifs
-/
theorem leadingCoeff_monomial {d : σ ->₀ Nat} (c : R) :
    m.leadingCoeff (monomial d c) = c := by
  classical
  simp only [leadingCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

/--
theorem `monic_monomial_one` / 定理 `monic_monomial_one`

English:
theorem monic_monomial_one
  given: {d : σ ->₀ Nat}
  proof: m.leadingCoeff_monomial 1

中文:
定理 monic_monomial_one
  条件: {d : σ ->₀ 自然数}
  证明: m.leadingCoeff_monomial 1
-/
@[simp] theorem monic_monomial_one {d : σ ->₀ Nat} :
    m.Monic (monomial d (1 : R)) :=
  m.leadingCoeff_monomial 1

/--
theorem `monic_monomial` / 定理 `monic_monomial`

English:
theorem monic_monomial
  given: {d : σ ->₀ Nat} {c : R}
  proof: by
  rw [Monic]; rw [m.leadingCoeff_monomial]

中文:
定理 monic_monomial
  条件: {d : σ ->₀ 自然数} {c : R}
  证明: by
  rw [Monic]; rw [m.leadingCoeff_monomial]

Depends on / 依赖: leadingCoeff_monomial, m.leadingCoeff_monomial
-/
theorem monic_monomial {d : σ ->₀ Nat} {c : R} :
    m.Monic (monomial d c) ↔ c = 1 := by
  rw [Monic]; rw [m.leadingCoeff_monomial]

/--
theorem `leadingCoeff_X` / 定理 `leadingCoeff_X`

English:
theorem leadingCoeff_X
  given: {s : σ}
  proof: m.leadingCoeff_monomial 1

中文:
定理 leadingCoeff_X
  条件: {s : σ}
  证明: m.leadingCoeff_monomial 1

Depends on / 依赖: leadingCoeff_monomial, m.leadingCoeff_monomial
-/
theorem leadingCoeff_X {s : σ} :
    m.leadingCoeff (X s : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1

/--
theorem `monic_X` / 定理 `monic_X`

English:
theorem monic_X
  given: {s : σ}
  proof: monic_monomial_one

中文:
定理 monic_X
  条件: {s : σ}
  证明: monic_monomial_one
-/
@[simp] theorem monic_X {s : σ} :
    m.Monic (X s : MvPolynomial σ R) :=
  monic_monomial_one

/--
theorem `leadingCoeff_one` / 定理 `leadingCoeff_one`

English:
theorem leadingCoeff_one
  statement: m.leadingCoeff (1 : MvPolynomial σ R) = 1
  proof: m.leadingCoeff_monomial 1

中文:
定理 leadingCoeff_one
  结论: m.leadingCoeff (1 : 多元多项式 σ R) = 1
  证明: m.leadingCoeff_monomial 1

Depends on / 依赖: leadingCoeff_monomial, m.leadingCoeff_monomial
-/
theorem leadingCoeff_one : m.leadingCoeff (1 : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1

/--
theorem `monic_C_one` / 定理 `monic_C_one`

English:
theorem monic_C_one
  statement: m.Monic (C 1 : MvPolynomial σ R)
  proof: monic_monomial_one

@[simp]

中文:
定理 monic_C_one
  结论: m.Monic (C 1 : 多元多项式 σ R)
  证明: monic_monomial_one

@[simp]

Depends on / 依赖: monic_monomial_one
-/
theorem monic_C_one : m.Monic (C 1 : MvPolynomial σ R) :=
  monic_monomial_one

@[simp]
/--
lemma `monic_one` / 引理 `monic_one`

English:
lemma monic_one
  statement: m.Monic (1 : MvPolynomial σ R)
  proof: monic_monomial_one

中文:
引理 monic_one
  结论: m.Monic (1 : 多元多项式 σ R)
  证明: monic_monomial_one

Depends on / 依赖: monic_monomial_one
-/
lemma monic_one : m.Monic (1 : MvPolynomial σ R) := monic_monomial_one

/--
theorem `degree_le_iff` / 定理 `degree_le_iff`

English:
theorem degree_le_iff
  given: {f : MvPolynomial σ R} {d : σ ->₀ Nat}
  proof: by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

中文:
定理 degree_le_iff
  条件: {f : 多元多项式 σ R} {d : σ ->₀ 自然数}
  证明: by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, Finset, Finset.sup_le_iff, apply_symm_apply, degree, mem_support_iff, ne_eq, sup_le_iff
-/
theorem degree_le_iff {f : MvPolynomial σ R} {d : σ ->₀ Nat} :
    m.degree f ≼[m] d ↔ forall c in f.support, c ≼[m] d := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

/--
theorem `degree_lt_iff` / 定理 `degree_lt_iff`

English:
theorem degree_lt_iff
  given: {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : 0 ≺[m] d)
  proof: by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

中文:
定理 degree_lt_iff
  条件: {f : 多元多项式 σ R} {d : σ ->₀ 自然数} (hd : 0 ≺[m] d)
  证明: by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, Finset, Finset.sup_lt_iff, apply_symm_apply, degree, map_zero, sup_lt_iff
-/
theorem degree_lt_iff {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : 0 ≺[m] d) :
    m.degree f ≺[m] d ↔ forall c in f.support, c ≺[m] d := by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

/--
theorem `le_degree` / 定理 `le_degree`

English:
theorem le_degree
  given: {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : d in f.support)
  proof: by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

中文:
定理 le_degree
  条件: {f : 多元多项式 σ R} {d : σ ->₀ 自然数} (hd : d in f.support)
  证明: by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, Finset, Finset.le_sup, apply_symm_apply, degree, le_sup
-/
theorem le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : d in f.support) :
    d ≼[m] m.degree f := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

/--
theorem `coeff_eq_zero_of_lt` / 定理 `coeff_eq_zero_of_lt`

English:
theorem coeff_eq_zero_of_lt
  given: {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d)
  proof: by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))

中文:
定理 coeff_eq_zero_of_lt
  条件: {f : 多元多项式 σ R} {d : σ ->₀ 自然数} (hd : m.degree f ≺[m] d)
  证明: by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))

Depends on / 依赖: le_degree, m.le_degree, mem_support_iff, mem_support_iff.mpr, not_le
-/
theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))

/--
theorem `leadingCoeff_ne_zero_iff` / 定理 `leadingCoeff_ne_zero_iff`

English:
theorem leadingCoeff_ne_zero_iff
  given: {f : MvPolynomial σ R}
  proof: by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf]; rw [leadingCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [leadingCoeff]; rw [← mem_support_iff]; rw [degree]
    suffices f.support.sup m.toSyn in m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd']; rw [AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]

中文:
定理 leadingCoeff_ne_zero_iff
  条件: {f : 多元多项式 σ R}
  证明: by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf]; rw [leadingCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [leadingCoeff]; rw [← mem_support_iff]; rw [degree]
    suffices f.support.sup m.toSyn in m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd']; rw [AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.symm_apply_apply, Finset, Finset.sup_mem_of_nonempty, degree, f.support, f.support.sup, leadingCoeff, leadingCoeff_zero, m.toSyn, mem_support_iff, not_imp_not, sup_mem_of_nonempty, support, support_nonempty, symm_apply_apply
-/
theorem leadingCoeff_ne_zero_iff {f : MvPolynomial σ R} :
    m.leadingCoeff f != 0 ↔ f != 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf]; rw [leadingCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [leadingCoeff]; rw [← mem_support_iff]; rw [degree]
    suffices f.support.sup m.toSyn in m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd']; rw [AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
/--
theorem `leadingCoeff_eq_zero_iff` / 定理 `leadingCoeff_eq_zero_iff`

English:
theorem leadingCoeff_eq_zero_iff
  given: {f : MvPolynomial σ R}
  proof: by
  simp only [← not_iff_not, leadingCoeff_ne_zero_iff]

中文:
定理 leadingCoeff_eq_zero_iff
  条件: {f : 多元多项式 σ R}
  证明: by
  simp only [← not_iff_not, leadingCoeff_ne_zero_iff]

Depends on / 依赖: leadingCoeff_ne_zero_iff, not_iff_not
-/
theorem leadingCoeff_eq_zero_iff {f : MvPolynomial σ R} :
    leadingCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, leadingCoeff_ne_zero_iff]

/--
theorem `coeff_degree_ne_zero_iff` / 定理 `coeff_degree_ne_zero_iff`

English:
theorem coeff_degree_ne_zero_iff
  given: {f : MvPolynomial σ R}
  proof: m.leadingCoeff_ne_zero_iff

中文:
定理 coeff_degree_ne_zero_iff
  条件: {f : 多元多项式 σ R}
  证明: m.leadingCoeff_ne_zero_iff

Depends on / 依赖: leadingCoeff_ne_zero_iff, m.leadingCoeff_ne_zero_iff
-/
theorem coeff_degree_ne_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) != 0 ↔ f != 0 :=
  m.leadingCoeff_ne_zero_iff

/--
theorem `degree_mem_support_iff` / 定理 `degree_mem_support_iff`

English:
theorem degree_mem_support_iff
  given: (f : MvPolynomial σ R)
  statement: m.degree f in f.support ↔ f != 0
  proof: mem_support_iff.trans coeff_degree_ne_zero_iff

@[simp]

中文:
定理 degree_mem_support_iff
  条件: (f : 多元多项式 σ R)
  结论: m.degree f in f.support ↔ f != 0
  证明: mem_support_iff.trans coeff_degree_ne_zero_iff

@[simp]

Depends on / 依赖: coeff_degree_ne_zero_iff, mem_support_iff, mem_support_iff.trans
-/
theorem degree_mem_support_iff (f : MvPolynomial σ R) : m.degree f in f.support ↔ f != 0 :=
  mem_support_iff.trans coeff_degree_ne_zero_iff

@[simp]
/--
theorem `coeff_degree_eq_zero_iff` / 定理 `coeff_degree_eq_zero_iff`

English:
theorem coeff_degree_eq_zero_iff
  given: {f : MvPolynomial σ R}
  proof: m.leadingCoeff_eq_zero_iff

中文:
定理 coeff_degree_eq_zero_iff
  条件: {f : 多元多项式 σ R}
  证明: m.leadingCoeff_eq_zero_iff

Depends on / 依赖: leadingCoeff_eq_zero_iff, m.leadingCoeff_eq_zero_iff
-/
theorem coeff_degree_eq_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) = 0 ↔ f = 0 :=
  m.leadingCoeff_eq_zero_iff

/--
lemma `degree_mem_support` / 引理 `degree_mem_support`

English:
lemma degree_mem_support
  given: {p : MvPolynomial σ R} (hp : p != 0)
  proof: by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

中文:
引理 degree_mem_support
  条件: {p : 多元多项式 σ R} (hp : p != 0)
  证明: by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

Depends on / 依赖: MvPolynomial, MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff, mem_support_iff
-/
lemma degree_mem_support {p : MvPolynomial σ R} (hp : p != 0) :
    m.degree p in p.support := by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

/--
theorem `degree_eq_zero_iff_totalDegree_eq_zero` / 定理 `degree_eq_zero_iff_totalDegree_eq_zero`

English:
theorem degree_eq_zero_iff_totalDegree_eq_zero
  given: {f : MvPolynomial σ R}
  proof: by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [eq_bot_iff]; rw [m.bot_eq_zero]; rw [← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [← eq_bot_iff]; rw [m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]

中文:
定理 degree_eq_zero_iff_totalDegree_eq_zero
  条件: {f : 多元多项式 σ R}
  证明: by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [eq_bot_iff]; rw [m.bot_eq_zero]; rw [← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [← eq_bot_iff]; rw [m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, Finsupp, Finsupp.ext_iff, bot_eq_zero, degree_le_iff, eq_bot_iff, eq_iff, ext_iff, forall_congr, imp_congr, injective, m.bot_eq_zero, m.toSyn.injective.eq_iff, m.toSyn.map_zero, map_eq_zero_iff, map_zero, rfl.to_iff, to_iff, totalDegree_eq_zero_iff
-/
theorem degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f.totalDegree = 0 := by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [eq_bot_iff]; rw [m.bot_eq_zero]; rw [← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero]; rw [← m.bot_eq_zero]; rw [← eq_bot_iff]; rw [m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]
/--
theorem `degree_C` / 定理 `degree_C`

English:
theorem degree_C
  given: (r : R)
  proof: by
  rw [degree_eq_zero_iff_totalDegree_eq_zero]; rw [totalDegree_C]

@[simp]

中文:
定理 degree_C
  条件: (r : R)
  证明: by
  rw [degree_eq_zero_iff_totalDegree_eq_zero]; rw [totalDegree_C]

@[simp]

Depends on / 依赖: degree_eq_zero_iff_totalDegree_eq_zero, totalDegree_C
-/
theorem degree_C (r : R) :
    m.degree (C r) = 0 := by
  rw [degree_eq_zero_iff_totalDegree_eq_zero]; rw [totalDegree_C]

@[simp]
/--
theorem `leadingCoeff_C` / 定理 `leadingCoeff_C`

English:
theorem leadingCoeff_C
  given: (c : R)
  statement: m.leadingCoeff (C c) = c
  proof: by
  simp [leadingCoeff]

中文:
定理 leadingCoeff_C
  条件: (c : R)
  结论: m.leadingCoeff (C c) = c
  证明: by
  simp [leadingCoeff]

Depends on / 依赖: leadingCoeff
-/
theorem leadingCoeff_C (c : R) : m.leadingCoeff (C c) = c := by
  simp [leadingCoeff]

/--
theorem `eq_C_of_degree_eq_zero` / 定理 `eq_C_of_degree_eq_zero`

English:
theorem eq_C_of_degree_eq_zero
  given: {f : MvPolynomial σ R} (hf : m.degree f = 0)
  proof: by
  ext d
  simp only [leadingCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf]; rw [map_zero]; rw [lt_iff_le_and_ne]; rw [ne_eq]; rw [eq_comm]; rw [EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩

中文:
定理 eq_C_of_degree_eq_zero
  条件: {f : 多元多项式 σ R} (hf : m.degree f = 0)
  证明: by
  ext d
  simp only [leadingCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf]; rw [map_zero]; rw [lt_iff_le_and_ne]; rw [ne_eq]; rw [eq_comm]; rw [EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, IsDiscrete, IsDiscrete.image_of_isOpenMap, IsOpenMap, IsOpenMap.of_inverse, Ne.symm, SetLike, SetLike.coe_sort_coe, bot_le, classical, coe_sort_coe, coeff_C, coeff_eq_zero_of_lt, continuous_const_smul, eq_comm, if_neg, image_of_isOpenMap, isDiscrete_iff_discreteTopology, leadingCoeff
-/
theorem eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) :
    f = C (m.leadingCoeff f) := by
  ext d
  simp only [leadingCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf]; rw [map_zero]; rw [lt_iff_le_and_ne]; rw [ne_eq]; rw [eq_comm]; rw [EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩

/--
theorem `degree_eq_zero_iff` / 定理 `degree_eq_zero_iff`

English:
theorem degree_eq_zero_iff
  given: {f : MvPolynomial σ R}
  proof: ⟨MonomialOrder.eq_C_of_degree_eq_zero, fun h => by rw [h, MonomialOrder.degree_C]⟩

中文:
定理 degree_eq_zero_iff
  条件: {f : 多元多项式 σ R}
  证明: ⟨MonomialOrder.eq_C_of_degree_eq_zero, fun h => by rw [h, MonomialOrder.degree_C]⟩

Depends on / 依赖: MonomialOrder, MonomialOrder.degree_C, MonomialOrder.eq_C_of_degree_eq_zero, degree_C, eq_C_of_degree_eq_zero
-/
theorem degree_eq_zero_iff {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) :=
  ⟨MonomialOrder.eq_C_of_degree_eq_zero, fun h => by rw [h, MonomialOrder.degree_C]⟩

/--
theorem `degree_add_le` / 定理 `degree_add_le`

English:
theorem degree_add_le
  given: {f g : MvPolynomial σ R}
  proof: by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b in f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [notMem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

中文:
定理 degree_add_le
  条件: {f g : 多元多项式 σ R}
  证明: by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b in f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [notMem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, apply_symm_apply, coeff_add, conv_rhs, degree_le_iff, f.support, le_degree, le_sup_iff, m.le_degree, m.toSyn.apply_symm_apply, mem_support_iff, notMem_support_iff, support, zero_add
-/
theorem degree_add_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f + g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b in f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [notMem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

/--
theorem `degree_sum_le` / 定理 `degree_sum_le`

English:
theorem degree_sum_le
  given: {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R}
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)

中文:
定理 degree_sum_le
  条件: {α : 类型} {s : 有限集 α} {f : α -> 多元多项式 σ R}
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)

Depends on / 依赖: ConjAct, ConjAct.ofConjAct, Finset, Finset.cons_induction_on, Finset.sum_cons, Finset.sup_cons, IsTopologicalGroup, IsTopologicalGroup.continuous_conj, cons_induction_on, continuous_conj, degree_add_le, le_rfl, le_trans, m.degree_add_le, max_le_max, ofConjAct, sum_cons, sup_cons
-/
theorem degree_sum_le {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R} :
    (m.toSyn <| m.degree <| ∑ x in s, f x) <= s.sup fun x => (m.toSyn <| m.degree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)

/--
theorem `degree_add_of_lt` / 定理 `degree_add_of_lt`

English:
theorem degree_add_of_lt
  given: {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
  proof: by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff]; rw [coeff_add]; rw [m.coeff_eq_zero_of_lt h]; rw [add_zero]; rw [← leadingCoeff]; rw [leadingCoeff_ne_zero_iff]
    intro hf
    rw [← not_le]; rw [hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

中文:
定理 degree_add_of_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree g ≺[m] m.degree f)
  证明: by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff]; rw [coeff_add]; rw [m.coeff_eq_zero_of_lt h]; rw [add_zero]; rw [← leadingCoeff]; rw [leadingCoeff_ne_zero_iff]
    intro hf
    rw [← not_le]; rw [hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

Depends on / 依赖: add_zero, bot_le, coeff_add, coeff_eq_zero_of_lt, degree_add_le, degree_zero, injective, le_antisymm, le_degree, le_of_lt, le_refl, le_trans, leadingCoeff, leadingCoeff_ne_zero_iff, m.coeff_eq_zero_of_lt, m.toSyn.injective, map_zero, mem_support_iff, not_le, sup_le_iff
-/
theorem degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f + g) = m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff]; rw [coeff_add]; rw [m.coeff_eq_zero_of_lt h]; rw [add_zero]; rw [← leadingCoeff]; rw [leadingCoeff_ne_zero_iff]
    intro hf
    rw [← not_le]; rw [hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

/--
theorem `degree_add_eq_right_of_lt` / 定理 `degree_add_eq_right_of_lt`

English:
theorem degree_add_eq_right_of_lt
  given: {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g)
  proof: by
  rw [add_comm]
  exact degree_add_of_lt h

中文:
定理 degree_add_eq_right_of_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree f ≺[m] m.degree g)
  证明: by
  rw [add_comm]
  exact degree_add_of_lt h

Depends on / 依赖: add_comm, degree_add_of_lt
-/
theorem degree_add_eq_right_of_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree (f + g) = m.degree g := by
  rw [add_comm]
  exact degree_add_of_lt h

/--
theorem `leadingCoeff_add_of_lt` / 定理 `leadingCoeff_add_of_lt`

English:
theorem leadingCoeff_add_of_lt
  given: {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
  proof: by
  simp only [leadingCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]

中文:
定理 leadingCoeff_add_of_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree g ≺[m] m.degree f)
  证明: by
  simp only [leadingCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]

Depends on / 依赖: add_zero, coeff_add, coeff_eq_zero_of_lt, degree_add_of_lt, leadingCoeff, m.degree_add_of_lt
-/
theorem leadingCoeff_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f + g) = m.leadingCoeff f := by
  simp only [leadingCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]

/--
theorem `Monic.add_of_lt` / 定理 `Monic.add_of_lt`

English:
theorem Monic.add_of_lt
  given: {f g : MvPolynomial σ R} (hf : m.Monic f) (h : m.degree g ≺[m] m.degree f)
  proof: by
  simp only [Monic, leadingCoeff_add_of_lt h, hf.leadingCoeff_eq_one]

中文:
定理 Monic.add_of_lt
  条件: {f g : 多元多项式 σ R} (hf : m.Monic f) (h : m.degree g ≺[m] m.degree f)
  证明: by
  simp only [Monic, leadingCoeff_add_of_lt h, hf.leadingCoeff_eq_one]

Depends on / 依赖: hf.leadingCoeff_eq_one, leadingCoeff_add_of_lt, leadingCoeff_eq_one
-/
theorem Monic.add_of_lt {f g : MvPolynomial σ R} (hf : m.Monic f) (h : m.degree g ≺[m] m.degree f) :
    m.Monic (f + g) := by
  simp only [Monic, leadingCoeff_add_of_lt h, hf.leadingCoeff_eq_one]

/--
theorem `degree_add_of_ne` / 定理 `degree_add_of_ne`

English:
theorem degree_add_of_ne
  statement: {f g : MvPolynomial σ R}
  proof: by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm]; rw [degree_add_of_lt (h' h)]; rw [right_eq_sup]
    simp only [le_of_lt (h' h)]

中文:
定理 degree_add_of_ne
  结论: {f g : 多元多项式 σ R}
  证明: by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm]; rw [degree_add_of_lt (h' h)]; rw [right_eq_sup]
    simp only [le_of_lt (h' h)]

Depends on / 依赖: Classical, Classical.or_iff_not_imp_left, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, add_comm, apply_eq_iff_eq, degree, degree_add_of_lt, le_iff_eq_or_lt, le_of_lt, m.degree, not_lt, or_iff_not_imp_left, right_eq_sup
-/
theorem degree_add_of_ne {f g : MvPolynomial σ R}
    (h : m.degree f != m.degree g) :
    m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm]; rw [degree_add_of_lt (h' h)]; rw [right_eq_sup]
    simp only [le_of_lt (h' h)]

/--
theorem `degree_mul_le` / 定理 `degree_mul_le`

English:
theorem degree_mul_le
  given: {f g : MvPolynomial σ R}
  proof: by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt]; rw [mem_support_iff]; rw [not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this]; rw [mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    grw [← map_add _ _ e, hd, ← map_add, hde]
    exact hc

中文:
定理 degree_mul_le
  条件: {f g : 多元多项式 σ R}
  证明: by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt]; rw [mem_support_iff]; rw [not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this]; rw [mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    grw [← map_add _ _ e, hd, ← map_add, hde]
    exact hc

Depends on / 依赖: Finset, Finset.mem_antidiagonal, Finset.sum_eq_zero, classical, coeff_eq_zero_of_lt, coeff_mul, degree, degree_le_iff, lt_of_add_lt_add_left, m.coeff_eq_zero_of_lt, m.degree, m.toSyn, map_add, mem_antidiagonal, mem_support_iff, mul_zero, not_imp_not, not_lt, sum_eq_zero, zero_mul
-/
theorem degree_mul_le {f g : MvPolynomial σ R} :
    m.degree (f * g) ≼[m] m.degree f + m.degree g := by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt]; rw [mem_support_iff]; rw [not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this]; rw [mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    grw [← map_add _ _ e, hd, ← map_add, hde]
    exact hc

/--
theorem `coeff_mul_of_add_of_degree_le` / 定理 `coeff_mul_of_add_of_degree_le`

English:
theorem coeff_mul_of_add_of_degree_le
  statement: {f g : MvPolynomial σ R} {a b : σ ->₀ Nat}
  proof: by
  classical
  rw [coeff_mul]; rw [Finset.sum_eq_single (a]; rw [b)]
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this]; rw [mul_zero]
      rw [not_lt] at hf
      rw [← not_le]
      intro hf'
      apply h
      suffices c = a by
        simpa [Prod.mk.injEq, this] using hcd
      apply m.toSyn.injective
      apply le_antisymm (le_trans hf ha)
      apply le_of_add_le_add_right (a := m.toSyn b)
      rw [← map_add]; rw [← hcd]; rw [map_add]
      simp only [add_le_add_iff_left]
      exact le_trans hf' hb
  · simp

中文:
定理 coeff_mul_of_add_of_degree_le
  结论: {f g : 多元多项式 σ R} {a b : σ ->₀ 自然数}
  证明: by
  classical
  rw [coeff_mul]; rw [Finset.sum_eq_single (a]; rw [b)]
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this]; rw [mul_zero]
      rw [not_lt] at hf
      rw [← not_le]
      intro hf'
      apply h
      suffices c = a by
        simpa [Prod.mk.injEq, this] using hcd
      apply m.toSyn.injective
      apply le_antisymm (le_trans hf ha)
      apply le_of_add_le_add_right (a := m.toSyn b)
      rw [← map_add]; rw [← hcd]; rw [map_add]
      simp only [add_le_add_iff_left]
      exact le_trans hf' hb
  · simp

Depends on / 依赖: Finset, Finset.mem_antidiagonal, Finset.sum_eq_single, Prod.mk.injEq, classical, coeff_eq_zero_of_lt, coeff_mul, degree, injective, le_antisymm, le_of_add_le_add_right, le_trans, m.coeff_eq_zero_of_lt, m.degree, m.toSyn, m.toSyn.injective, mem_antidiagonal, mul_zero, not_le, not_lt
-/
theorem coeff_mul_of_add_of_degree_le {f g : MvPolynomial σ R} {a b : σ ->₀ Nat}
    (ha : m.degree f ≼[m] a) (hb : m.degree g ≼[m] b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [coeff_mul]; rw [Finset.sum_eq_single (a]; rw [b)]
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this]; rw [mul_zero]
      rw [not_lt] at hf
      rw [← not_le]
      intro hf'
      apply h
      suffices c = a by
        simpa [Prod.mk.injEq, this] using hcd
      apply m.toSyn.injective
      apply le_antisymm (le_trans hf ha)
      apply le_of_add_le_add_right (a := m.toSyn b)
      rw [← map_add]; rw [← hcd]; rw [map_add]
      simp only [add_le_add_iff_left]
      exact le_trans hf' hb
  · simp

/--
theorem `coeff_mul_of_degree_add` / 定理 `coeff_mul_of_degree_add`

English:
theorem coeff_mul_of_degree_add
  given: {f g : MvPolynomial σ R}
  proof: coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)

中文:
定理 coeff_mul_of_degree_add
  条件: {f g : 多元多项式 σ R}
  证明: coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)

Depends on / 依赖: coeff_mul_of_add_of_degree_le, le_of_eq
-/
theorem coeff_mul_of_degree_add {f g : MvPolynomial σ R} :
    (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m.leadingCoeff g :=
  coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)

/--
theorem `degree_mul_of_mul_leadingCoeff_ne_zero` / 定理 `degree_mul_of_mul_leadingCoeff_ne_zero`

English:
theorem degree_mul_of_mul_leadingCoeff_ne_zero
  statement: {f g : MvPolynomial σ R}
  proof: by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff]; rw [coeff_mul_of_degree_add]
  exact hfg

中文:
定理 degree_mul_of_mul_leadingCoeff_ne_zero
  结论: {f g : 多元多项式 σ R}
  证明: by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff]; rw [coeff_mul_of_degree_add]
  exact hfg

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_le, injective, le_antisymm, le_degree, m.toSyn.injective, mem_support_iff
-/
theorem degree_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g != 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff]; rw [coeff_mul_of_degree_add]
  exact hfg

/--
theorem `leadingCoeff_mul_of_mul_leadingCoeff_ne_zero` / 定理 `leadingCoeff_mul_of_mul_leadingCoeff_ne_zero`

English:
theorem leadingCoeff_mul_of_mul_leadingCoeff_ne_zero
  statement: {f g : MvPolynomial σ R}
  proof: by
  rw [leadingCoeff]; rw [← coeff_mul_of_degree_add]; rw [degree_mul_of_mul_leadingCoeff_ne_zero hfg]

中文:
定理 leadingCoeff_mul_of_mul_leadingCoeff_ne_zero
  结论: {f g : 多元多项式 σ R}
  证明: by
  rw [leadingCoeff]; rw [← coeff_mul_of_degree_add]; rw [degree_mul_of_mul_leadingCoeff_ne_zero hfg]

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_of_mul_leadingCoeff_ne_zero, leadingCoeff
-/
theorem leadingCoeff_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g != 0) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  rw [leadingCoeff]; rw [← coeff_mul_of_degree_add]; rw [degree_mul_of_mul_leadingCoeff_ne_zero hfg]

/--
theorem `degree_mul_of_left_mem_nonZeroDivisors` / 定理 `degree_mul_of_left_mem_nonZeroDivisors`

English:
theorem degree_mul_of_left_mem_nonZeroDivisors
  statement: {f g : MvPolynomial σ R}
  proof: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  apply not_imp_not.mpr (mem_nonZeroDivisors_iff.mp hf |>.1 _)
  simp [hg]

中文:
定理 degree_mul_of_left_mem_nonZeroDivisors
  结论: {f g : 多元多项式 σ R}
  证明: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  apply not_imp_not.mpr (mem_nonZeroDivisors_iff.mp hf |>.1 _)
  simp [hg]

Depends on / 依赖: degree_mul_of_mul_leadingCoeff_ne_zero, mem_nonZeroDivisors_iff, mem_nonZeroDivisors_iff.mp, not_imp_not, not_imp_not.mpr
-/
theorem degree_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f in nonZeroDivisors _) (hg : g != 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  apply not_imp_not.mpr (mem_nonZeroDivisors_iff.mp hf |>.1 _)
  simp [hg]

/--
theorem `degree_mul_of_right_mem_nonZeroDivisors` / 定理 `degree_mul_of_right_mem_nonZeroDivisors`

English:
theorem degree_mul_of_right_mem_nonZeroDivisors
  statement: {f g : MvPolynomial σ R}
  proof: add_comm (m.degree f) (m.degree g) ▸ mul_comm f g ▸ degree_mul_of_left_mem_nonZeroDivisors hg hf

中文:
定理 degree_mul_of_right_mem_nonZeroDivisors
  结论: {f g : 多元多项式 σ R}
  证明: add_comm (m.degree f) (m.degree g) ▸ mul_comm f g ▸ degree_mul_of_left_mem_nonZeroDivisors hg hf

Depends on / 依赖: add_comm, degree, degree_mul_of_left_mem_nonZeroDivisors, m.degree, mul_comm
-/
theorem degree_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : f != 0) (hg : m.leadingCoeff g in nonZeroDivisors _) :
    m.degree (f * g) = m.degree f + m.degree g :=
  add_comm (m.degree f) (m.degree g) ▸ mul_comm f g ▸ degree_mul_of_left_mem_nonZeroDivisors hg hf

/--
theorem `leadingCoeff_mul_of_left_mem_nonZeroDivisors` / 定理 `leadingCoeff_mul_of_left_mem_nonZeroDivisors`

English:
theorem leadingCoeff_mul_of_left_mem_nonZeroDivisors
  statement: {f g : MvPolynomial σ R}
  proof: by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

中文:
定理 leadingCoeff_mul_of_left_mem_nonZeroDivisors
  结论: {f g : 多元多项式 σ R}
  证明: by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_of_left_mem_nonZeroDivisors, leadingCoeff
-/
theorem leadingCoeff_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f in nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

/--
theorem `leadingCoeff_mul_of_right_mem_nonZeroDivisors` / 定理 `leadingCoeff_mul_of_right_mem_nonZeroDivisors`

English:
theorem leadingCoeff_mul_of_right_mem_nonZeroDivisors
  statement: {f g : MvPolynomial σ R}
  proof: by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

中文:
定理 leadingCoeff_mul_of_right_mem_nonZeroDivisors
  结论: {f g : 多元多项式 σ R}
  证明: by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_of_right_mem_nonZeroDivisors, leadingCoeff
-/
theorem leadingCoeff_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hg : m.leadingCoeff g in nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

/--
theorem `degree_mul_of_isRegular_left` / 定理 `degree_mul_of_isRegular_left`

English:
theorem degree_mul_of_isRegular_left
  statement: {f g : MvPolynomial σ R}
  proof: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    leadingCoeff_eq_zero_iff]
  exact hg

中文:
定理 degree_mul_of_isRegular_left
  结论: {f g : 多元多项式 σ R}
  证明: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    leadingCoeff_eq_zero_iff]
  exact hg

Depends on / 依赖: IsLeftRegular, IsLeftRegular.mul_left_eq_zero_iff, IsRegular, IsRegular.left, degree_mul_of_mul_leadingCoeff_ne_zero, leadingCoeff_eq_zero_iff, mul_left_eq_zero_iff, ne_eq
-/
theorem degree_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) (hg : g != 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    leadingCoeff_eq_zero_iff]
  exact hg

/--
theorem `leadingCoeff_mul_of_isRegular_left` / 定理 `leadingCoeff_mul_of_isRegular_left`

English:
theorem leadingCoeff_mul_of_isRegular_left
  statement: {f g : MvPolynomial σ R}
  proof: by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

中文:
定理 leadingCoeff_mul_of_isRegular_left
  结论: {f g : 多元多项式 σ R}
  证明: by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_of_isRegular_left, leadingCoeff
-/
theorem leadingCoeff_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

/--
theorem `degree_mul_of_isRegular_right` / 定理 `degree_mul_of_isRegular_right`

English:
theorem degree_mul_of_isRegular_right
  statement: {f g : MvPolynomial σ R}
  proof: by
  rw [mul_comm]; rw [m.degree_mul_of_isRegular_left hg hf]; rw [add_comm]

中文:
定理 degree_mul_of_isRegular_right
  结论: {f g : 多元多项式 σ R}
  证明: by
  rw [mul_comm]; rw [m.degree_mul_of_isRegular_left hg hf]; rw [add_comm]

Depends on / 依赖: add_comm, degree_mul_of_isRegular_left, m.degree_mul_of_isRegular_left, mul_comm
-/
theorem degree_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f != 0) (hg : IsRegular (m.leadingCoeff g)) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_comm]; rw [m.degree_mul_of_isRegular_left hg hf]; rw [add_comm]

/--
theorem `leadingCoeff_mul_of_isRegular_right` / 定理 `leadingCoeff_mul_of_isRegular_right`

English:
theorem leadingCoeff_mul_of_isRegular_right
  statement: {f g : MvPolynomial σ R}
  proof: by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]

中文:
定理 leadingCoeff_mul_of_isRegular_right
  结论: {f g : 多元多项式 σ R}
  证明: by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]

Depends on / 依赖: coeff_mul_of_degree_add, degree_mul_of_isRegular_right, leadingCoeff
-/
theorem leadingCoeff_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hg : IsRegular (m.leadingCoeff g)) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]

/--
theorem `Monic.mul` / 定理 `Monic.mul`

English:
theorem Monic.mul
  given: {f g : MvPolynomial σ R} (hf : m.Monic f) (hg : m.Monic g)
  proof: by
  nontriviality R
  suffices m.leadingCoeff f * m.leadingCoeff g = 1 by
    rw [Monic]; rw [MonomialOrder.leadingCoeff]; rw [degree_mul_of_mul_leadingCoeff_ne_zero]; rw [coeff_mul_of_degree_add]; rw [this]
    rw [this]
    exact one_ne_zero
  rw [hf.leadingCoeff_eq_one]; rw [hg.leadingCoeff_eq_one]; rw [one_mul]

中文:
定理 Monic.mul
  条件: {f g : 多元多项式 σ R} (hf : m.Monic f) (hg : m.Monic g)
  证明: by
  nontriviality R
  suffices m.leadingCoeff f * m.leadingCoeff g = 1 by
    rw [Monic]; rw [MonomialOrder.leadingCoeff]; rw [degree_mul_of_mul_leadingCoeff_ne_zero]; rw [coeff_mul_of_degree_add]; rw [this]
    rw [this]
    exact one_ne_zero
  rw [hf.leadingCoeff_eq_one]; rw [hg.leadingCoeff_eq_one]; rw [one_mul]
-/
theorem Monic.mul {f g : MvPolynomial σ R} (hf : m.Monic f) (hg : m.Monic g) :
    m.Monic (f * g) := by
  nontriviality R
  suffices m.leadingCoeff f * m.leadingCoeff g = 1 by
    rw [Monic]; rw [MonomialOrder.leadingCoeff]; rw [degree_mul_of_mul_leadingCoeff_ne_zero]; rw [coeff_mul_of_degree_add]; rw [this]
    rw [this]
    exact one_ne_zero
  rw [hf.leadingCoeff_eq_one]; rw [hg.leadingCoeff_eq_one]; rw [one_mul]

/--
theorem `degree_mul` / 定理 `degree_mul`

English:
theorem degree_mul
  given: [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f != 0) (hg : g != 0)
  proof: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero_iff, not_or]
  tauto

中文:
定理 degree_mul
  条件: [无零因子 R] {f g : 多元多项式 σ R} (hf : f != 0) (hg : g != 0)
  证明: by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero_iff, not_or]
  tauto

Depends on / 依赖: degree_mul_of_mul_leadingCoeff_ne_zero, leadingCoeff_eq_zero_iff, mul_eq_zero, ne_eq, not_or
-/
theorem degree_mul [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f != 0) (hg : g != 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero_iff, not_or]
  tauto

/--
theorem `leadingCoeff_mul` / 定理 `leadingCoeff_mul`

English:
theorem leadingCoeff_mul
  given: [NoZeroDivisors R] {f g : MvPolynomial σ R}
  proof: by
  by_cases! +distrib h : f = 0 ∨ g = 0
  · cases h <;> simp [*]
  obtain ⟨hf, hg⟩ := h
  rw [leadingCoeff]; rw [degree_mul hf hg]; rw [← coeff_mul_of_degree_add]

中文:
定理 leadingCoeff_mul
  条件: [无零因子 R] {f g : 多元多项式 σ R}
  证明: by
  by_cases! +distrib h : f = 0 ∨ g = 0
  · cases h <;> simp [*]
  obtain ⟨hf, hg⟩ := h
  rw [leadingCoeff]; rw [degree_mul hf hg]; rw [← coeff_mul_of_degree_add]
-/
@[simp] theorem leadingCoeff_mul [NoZeroDivisors R] {f g : MvPolynomial σ R} :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases! +distrib h : f = 0 ∨ g = 0
  · cases h <;> simp [*]
  obtain ⟨hf, hg⟩ := h
  rw [leadingCoeff]; rw [degree_mul hf hg]; rw [← coeff_mul_of_degree_add]

/--
theorem `degree_pow_le` / 定理 `degree_pow_le`

English:
theorem degree_pow_le
  given: {f : MvPolynomial σ R} (n : Nat)
  proof: by
  induction n with
  | zero => simp [m.degree_one]
  | succ n hrec =>
      simp only [pow_add, pow_one, add_smul, one_smul]
      apply le_trans m.degree_mul_le
      simp only [map_add, add_le_add_iff_right]
      exact hrec

中文:
定理 degree_pow_le
  条件: {f : 多元多项式 σ R} (n : 自然数)
  证明: by
  induction n with
  | zero => simp [m.degree_one]
  | succ n hrec =>
      simp only [pow_add, pow_one, add_smul, one_smul]
      apply le_trans m.degree_mul_le
      simp only [map_add, add_le_add_iff_right]
      exact hrec

Depends on / 依赖: add_le_add_iff_right, add_smul, degree_mul_le, degree_one, le_trans, m.degree_mul_le, m.degree_one, map_add, one_smul, pow_add, pow_one
-/
theorem degree_pow_le {f : MvPolynomial σ R} (n : Nat) :
    m.degree (f ^ n) ≼[m] n • (m.degree f) := by
  induction n with
  | zero => simp [m.degree_one]
  | succ n hrec =>
      simp only [pow_add, pow_one, add_smul, one_smul]
      apply le_trans m.degree_mul_le
      simp only [map_add, add_le_add_iff_right]
      exact hrec

/--
theorem `coeff_pow_nsmul_degree` / 定理 `coeff_pow_nsmul_degree`

English:
theorem coeff_pow_nsmul_degree
  given: (f : MvPolynomial σ R) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hrec =>
    simp only [add_smul, one_smul, pow_add, pow_one]
    rw [m.coeff_mul_of_add_of_degree_le (m.degree_pow_le _) le_rfl]; rw [hrec]; rw [leadingCoeff]

中文:
定理 coeff_pow_nsmul_degree
  条件: (f : 多元多项式 σ R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hrec =>
    simp only [add_smul, one_smul, pow_add, pow_one]
    rw [m.coeff_mul_of_add_of_degree_le (m.degree_pow_le _) le_rfl]; rw [hrec]; rw [leadingCoeff]

Depends on / 依赖: add_smul, coeff_mul_of_add_of_degree_le, degree_pow_le, le_rfl, leadingCoeff, m.coeff_mul_of_add_of_degree_le, m.degree_pow_le, one_smul, pow_add, pow_one
-/
theorem coeff_pow_nsmul_degree (f : MvPolynomial σ R) (n : Nat) :
    (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n := by
  induction n with
  | zero => simp
  | succ n hrec =>
    simp only [add_smul, one_smul, pow_add, pow_one]
    rw [m.coeff_mul_of_add_of_degree_le (m.degree_pow_le _) le_rfl]; rw [hrec]; rw [leadingCoeff]

/--
theorem `degree_pow_of_pow_leadingCoeff_ne_zero` / 定理 `degree_pow_of_pow_leadingCoeff_ne_zero`

English:
theorem degree_pow_of_pow_leadingCoeff_ne_zero
  statement: {f : MvPolynomial σ R} {n : Nat}
  proof: by
  apply m.toSyn.injective
  apply le_antisymm (m.degree_pow_le n)
  apply le_degree
  rw [mem_support_iff]; rw [coeff_pow_nsmul_degree]
  exact hf

中文:
定理 degree_pow_of_pow_leadingCoeff_ne_zero
  结论: {f : 多元多项式 σ R} {n : 自然数}
  证明: by
  apply m.toSyn.injective
  apply le_antisymm (m.degree_pow_le n)
  apply le_degree
  rw [mem_support_iff]; rw [coeff_pow_nsmul_degree]
  exact hf

Depends on / 依赖: coeff_pow_nsmul_degree, degree_pow_le, injective, le_antisymm, le_degree, m.degree_pow_le, m.toSyn.injective, mem_support_iff
-/
theorem degree_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat}
    (hf : m.leadingCoeff f ^ n != 0) :
    m.degree (f ^ n) = n • m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm (m.degree_pow_le n)
  apply le_degree
  rw [mem_support_iff]; rw [coeff_pow_nsmul_degree]
  exact hf

/--
theorem `leadingCoeff_pow_of_pow_leadingCoeff_ne_zero` / 定理 `leadingCoeff_pow_of_pow_leadingCoeff_ne_zero`

English:
theorem leadingCoeff_pow_of_pow_leadingCoeff_ne_zero
  statement: {f : MvPolynomial σ R} {n : Nat}
  proof: by
  rw [leadingCoeff]; rw [degree_pow_of_pow_leadingCoeff_ne_zero hf]; rw [coeff_pow_nsmul_degree]

中文:
定理 leadingCoeff_pow_of_pow_leadingCoeff_ne_zero
  结论: {f : 多元多项式 σ R} {n : 自然数}
  证明: by
  rw [leadingCoeff]; rw [degree_pow_of_pow_leadingCoeff_ne_zero hf]; rw [coeff_pow_nsmul_degree]

Depends on / 依赖: coeff_pow_nsmul_degree, degree_pow_of_pow_leadingCoeff_ne_zero, leadingCoeff
-/
theorem leadingCoeff_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat}
    (hf : m.leadingCoeff f ^ n != 0) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff]; rw [degree_pow_of_pow_leadingCoeff_ne_zero hf]; rw [coeff_pow_nsmul_degree]

/--
theorem `Monic.pow` / 定理 `Monic.pow`

English:
theorem Monic.pow
  given: {f : MvPolynomial σ R} {n : Nat} (hf : m.Monic f)
  proof: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_pow_of_pow_leadingCoeff_ne_zero]; rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  exact one_ne_zero

中文:
定理 Monic.pow
  条件: {f : 多元多项式 σ R} {n : 自然数} (hf : m.Monic f)
  证明: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_pow_of_pow_leadingCoeff_ne_zero]; rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  exact one_ne_zero
-/
protected theorem Monic.pow {f : MvPolynomial σ R} {n : Nat} (hf : m.Monic f) :
    m.Monic (f ^ n) := by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_pow_of_pow_leadingCoeff_ne_zero]; rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  rw [hf.leadingCoeff_eq_one]; rw [one_pow]
  exact one_ne_zero

/--
theorem `degree_pow` / 定理 `degree_pow`

English:
theorem degree_pow
  given: [IsReduced R] (f : MvPolynomial σ R) (n : Nat)
  proof: by
  by_cases hf : f = 0
  · rw [hf, degree_zero, smul_zero]
    by_cases hn : n = 0
    · rw [hn, pow_zero, degree_one]
    · rw [zero_pow hn, degree_zero]
  apply degree_pow_of_pow_leadingCoeff_ne_zero
  apply pow_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact hf

中文:
定理 degree_pow
  条件: [是既约 R] (f : 多元多项式 σ R) (n : 自然数)
  证明: by
  by_cases hf : f = 0
  · rw [hf, degree_zero, smul_zero]
    by_cases hn : n = 0
    · rw [hn, pow_zero, degree_one]
    · rw [zero_pow hn, degree_zero]
  apply degree_pow_of_pow_leadingCoeff_ne_zero
  apply pow_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact hf

Depends on / 依赖: degree_one, degree_pow_of_pow_leadingCoeff_ne_zero, degree_zero, leadingCoeff_ne_zero_iff, pow_ne_zero, pow_zero, smul_zero, zero_pow
-/
theorem degree_pow [IsReduced R] (f : MvPolynomial σ R) (n : Nat) :
    m.degree (f ^ n) = n • m.degree f := by
  by_cases hf : f = 0
  · rw [hf, degree_zero, smul_zero]
    by_cases hn : n = 0
    · rw [hn, pow_zero, degree_one]
    · rw [zero_pow hn, degree_zero]
  apply degree_pow_of_pow_leadingCoeff_ne_zero
  apply pow_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact hf

/--
theorem `leadingCoeff_pow` / 定理 `leadingCoeff_pow`

English:
theorem leadingCoeff_pow
  given: [IsReduced R] (f : MvPolynomial σ R) (n : Nat)
  proof: by
  rw [leadingCoeff]; rw [degree_pow]; rw [coeff_pow_nsmul_degree]

中文:
定理 leadingCoeff_pow
  条件: [是既约 R] (f : 多元多项式 σ R) (n : 自然数)
  证明: by
  rw [leadingCoeff]; rw [degree_pow]; rw [coeff_pow_nsmul_degree]

Depends on / 依赖: coeff_pow_nsmul_degree, degree_pow, leadingCoeff
-/
theorem leadingCoeff_pow [IsReduced R] (f : MvPolynomial σ R) (n : Nat) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff]; rw [degree_pow]; rw [coeff_pow_nsmul_degree]

/--
theorem `degree_smul_le` / 定理 `degree_smul_le`

English:
theorem degree_smul_le
  given: {r : R} {f : MvPolynomial σ R}
  proof: by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp

中文:
定理 degree_smul_le
  条件: {r : R} {f : 多元多项式 σ R}
  证明: by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp

Depends on / 依赖: degree_mul_le, le_of_le_of_eq, smul_eq_C_mul
-/
theorem degree_smul_le {r : R} {f : MvPolynomial σ R} :
    m.degree (r • f) ≼[m] m.degree f := by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp

/--
theorem `degree_smul_of_mem_nonZeroDivisors` / 定理 `degree_smul_of_mem_nonZeroDivisors`

English:
theorem degree_smul_of_mem_nonZeroDivisors
  statement: {r : R} (hr : r in nonZeroDivisors _)
  proof: by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f)]; rw [← degree_C r]; rw [coeff_mul_of_degree_add]
  simp [not_imp_not.mpr ((mem_nonZeroDivisors_iff.mp hr).1 _) <| m.leadingCoeff_ne_zero_iff.mpr hf]

中文:
定理 degree_smul_of_mem_nonZeroDivisors
  结论: {r : R} (hr : r in nonZeroDivisors _)
  证明: by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f)]; rw [← degree_C r]; rw [coeff_mul_of_degree_add]
  simp [not_imp_not.mpr ((mem_nonZeroDivisors_iff.mp hr).1 _) <| m.leadingCoeff_ne_zero_iff.mpr hf]

Depends on / 依赖: coeff_mul_of_degree_add, degree, degree_C, degree_smul_le, injective, le_antisymm, le_degree, leadingCoeff_ne_zero_iff, m.leadingCoeff_ne_zero_iff.mpr, m.toSyn.injective, mem_nonZeroDivisors_iff, mem_nonZeroDivisors_iff.mp, mem_support_iff, not_imp_not, not_imp_not.mpr, smul_eq_C_mul, zero_add
-/
theorem degree_smul_of_mem_nonZeroDivisors {r : R} (hr : r in nonZeroDivisors _)
    {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f)]; rw [← degree_C r]; rw [coeff_mul_of_degree_add]
  simp [not_imp_not.mpr ((mem_nonZeroDivisors_iff.mp hr).1 _) <| m.leadingCoeff_ne_zero_iff.mpr hf]

/--
theorem `degree_smul_of_isRegular` / 定理 `degree_smul_of_isRegular`

English:
theorem degree_smul_of_isRegular
  given: {r : R} (hr : IsRegular r) {f : MvPolynomial σ R}
  proof: m.degree_smul_of_mem_nonZeroDivisors hr.mem_nonZeroDivisors

中文:
定理 degree_smul_of_isRegular
  条件: {r : R} (hr : 是正则 r) {f : 多元多项式 σ R}
  证明: m.degree_smul_of_mem_nonZeroDivisors hr.mem_nonZeroDivisors

Depends on / 依赖: degree_smul_of_mem_nonZeroDivisors, hr.mem_nonZeroDivisors, m.degree_smul_of_mem_nonZeroDivisors, mem_nonZeroDivisors
-/
theorem degree_smul_of_isRegular {r : R} (hr : IsRegular r) {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f :=
  m.degree_smul_of_mem_nonZeroDivisors hr.mem_nonZeroDivisors

/--
theorem `degree_prod_le` / 定理 `degree_prod_le`

English:
theorem degree_prod_le
  given: {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]; rw [m.degree_C]; rw [map_zero]
  | insert a s has hrec =>
    rw [Finset.prod_insert has]; rw [Finset.sum_insert has]
    apply le_trans degree_mul_le
    simp only [map_add, add_le_add_iff_left, hrec]

中文:
定理 degree_prod_le
  条件: {ι : 类型} {P : ι -> 多元多项式 σ R} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]; rw [m.degree_C]; rw [map_zero]
  | insert a s has hrec =>
    rw [Finset.prod_insert has]; rw [Finset.sum_insert has]
    apply le_trans degree_mul_le
    simp only [map_add, add_le_add_iff_left, hrec]

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_empty, Finset.prod_insert, Finset.sum_empty, Finset.sum_insert, add_le_add_iff_left, classical, degree_C, degree_mul_le, induction_on, insert, le_trans, m.degree_C, map_add, map_zero, prod_empty, prod_insert, sum_empty, sum_insert
-/
theorem degree_prod_le {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι} :
    m.degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]; rw [m.degree_C]; rw [map_zero]
  | insert a s has hrec =>
    rw [Finset.prod_insert has]; rw [Finset.sum_insert has]
    apply le_trans degree_mul_le
    simp only [map_add, add_le_add_iff_left, hrec]

/--
theorem `coeff_prod_sum_degree` / 定理 `coeff_prod_sum_degree`

English:
theorem coeff_prod_sum_degree
  given: {ι : Type*} (P : ι -> MvPolynomial σ R) (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hrec =>
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    rw [coeff_mul_of_add_of_degree_le (le_of_eq rfl) degree_prod_le]
    exact congr_arg₂ _ rfl hrec

中文:
定理 coeff_prod_sum_degree
  条件: {ι : 类型} (P : ι -> 多元多项式 σ R) (s : 有限集 ι)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hrec =>
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    rw [coeff_mul_of_add_of_degree_le (le_of_eq rfl) degree_prod_le]
    exact congr_arg₂ _ rfl hrec

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_insert, Finset.sum_insert, classical, coeff_mul_of_add_of_degree_le, degree_prod_le, induction_on, insert, le_of_eq, prod_insert, sum_insert
-/
theorem coeff_prod_sum_degree {ι : Type*} (P : ι -> MvPolynomial σ R) (s : Finset ι) :
    coeff (∑ i in s, m.degree (P i)) (∏ i in s, P i) = ∏ i in s, m.leadingCoeff (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hrec =>
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    rw [coeff_mul_of_add_of_degree_le (le_of_eq rfl) degree_prod_le]
    exact congr_arg₂ _ rfl hrec

/--
theorem `degree_prod_of_mem_nonZeroDivisors` / 定理 `degree_prod_of_mem_nonZeroDivisors`

English:
theorem degree_prod_of_mem_nonZeroDivisors
  statement: {ι : Type*}
  proof: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact nonZeroDivisors.ne_zero (prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors H)

中文:
定理 degree_prod_of_mem_nonZeroDivisors
  结论: {ι : 类型}
  证明: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact nonZeroDivisors.ne_zero (prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors H)

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.topologicalGroup, MvPolynomial, S.subtype, Subsingleton, Subsingleton.elim, coeff_prod_sum_degree, degree_prod_le, injective, le_antisymm, le_degree, m.coeff_prod_sum_degree, m.le_degree, m.toSyn.injective, mem_support_iff, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors, subsingleton_or_nontrivial
-/
theorem degree_prod_of_mem_nonZeroDivisors {ι : Type*}
    {P : ι -> MvPolynomial σ R} {s : Finset ι}
    (H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisors _) :
    m.degree (∏ i in s, P i) = ∑ i in s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact nonZeroDivisors.ne_zero (prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors H)

-- TODO : it suffices that all leading coefficients but one are regular
/--
theorem `degree_prod_of_regular` / 定理 `degree_prod_of_regular`

English:
theorem degree_prod_of_regular
  statement: {ι : Type*}
  proof: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact (IsRegular.prod H).ne_zero

中文:
定理 degree_prod_of_regular
  结论: {ι : 类型}
  证明: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact (IsRegular.prod H).ne_zero

Depends on / 依赖: IsRegular, IsRegular.prod, MvPolynomial, Subsingleton, Subsingleton.elim, coeff_prod_sum_degree, degree_prod_le, injective, le_antisymm, le_degree, m.coeff_prod_sum_degree, m.le_degree, m.toSyn.injective, mem_support_iff, ne_zero, subsingleton_or_nontrivial
-/
theorem degree_prod_of_regular {ι : Type*}
    {P : ι -> MvPolynomial σ R} {s : Finset ι} (H : forall i in s, IsRegular (m.leadingCoeff (P i))) :
    m.degree (∏ i in s, P i) = ∑ i in s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff]; rw [m.coeff_prod_sum_degree]
    exact (IsRegular.prod H).ne_zero

/--
theorem `degree_prod` / 定理 `degree_prod`

English:
theorem degree_prod
  statement: [NoZeroDivisors R] {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι}
  proof: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    simpa [m.coeff_prod_sum_degree, Finset.prod_eq_zero_iff]

中文:
定理 degree_prod
  结论: [无零因子 R] {ι : 类型} {P : ι -> 多元多项式 σ R} {s : 有限集 ι}
  证明: by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    simpa [m.coeff_prod_sum_degree, Finset.prod_eq_zero_iff]

Depends on / 依赖: Finset, Finset.prod_eq_zero_iff, MvPolynomial, Subsingleton, Subsingleton.elim, coeff_prod_sum_degree, degree_prod_le, injective, le_antisymm, le_degree, m.coeff_prod_sum_degree, m.le_degree, m.toSyn.injective, prod_eq_zero_iff, subsingleton_or_nontrivial
-/
theorem degree_prod [NoZeroDivisors R] {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι}
    (H : forall i in s, P i != 0) :
    m.degree (∏ i in s, P i) = ∑ i in s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    simpa [m.coeff_prod_sum_degree, Finset.prod_eq_zero_iff]

/--
lemma `degree_mul'` / 引理 `degree_mul'`

English:
lemma degree_mul'
  given: [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g != 0)
  proof: by
  apply ne_zero_and_ne_zero_of_mul at hf
  exact m.degree_mul hf.1 hf.2

中文:
引理 degree_mul'
  条件: [无零因子 R] {f g : 多元多项式 σ R} (hf : f * g != 0)
  证明: by
  apply ne_zero_and_ne_zero_of_mul at hf
  exact m.degree_mul hf.1 hf.2

Depends on / 依赖: degree_mul, m.degree_mul, ne_zero_and_ne_zero_of_mul
-/
lemma degree_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g != 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply ne_zero_and_ne_zero_of_mul at hf
  exact m.degree_mul hf.1 hf.2

/--
lemma `notMem_support_of_degree_lt` / 引理 `notMem_support_of_degree_lt`

English:
lemma notMem_support_of_degree_lt
  given: {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g)
  proof: by
  simp [coeff_eq_zero_of_lt h]

中文:
引理 notMem_support_of_degree_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree f ≺[m] m.degree g)
  证明: by
  simp [coeff_eq_zero_of_lt h]

Depends on / 依赖: coeff_eq_zero_of_lt
-/
lemma notMem_support_of_degree_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree g ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

/--
theorem `leadingCoeff_prod_of_mem_nonZeroDivisors` / 定理 `leadingCoeff_prod_of_mem_nonZeroDivisors`

English:
theorem leadingCoeff_prod_of_mem_nonZeroDivisors
  statement: {ι : Type*}
  proof: by
  simp only [leadingCoeff, degree_prod_of_mem_nonZeroDivisors H, coeff_prod_sum_degree]

中文:
定理 leadingCoeff_prod_of_mem_nonZeroDivisors
  结论: {ι : 类型}
  证明: by
  simp only [leadingCoeff, degree_prod_of_mem_nonZeroDivisors H, coeff_prod_sum_degree]

Depends on / 依赖: coeff_prod_sum_degree, degree_prod_of_mem_nonZeroDivisors, leadingCoeff
-/
theorem leadingCoeff_prod_of_mem_nonZeroDivisors {ι : Type*}
    {P : ι -> MvPolynomial σ R} {s : Finset ι}
    (H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisors _) :
    m.leadingCoeff (∏ i in s, P i) = ∏ i in s, m.leadingCoeff (P i) := by
  simp only [leadingCoeff, degree_prod_of_mem_nonZeroDivisors H, coeff_prod_sum_degree]

-- TODO : it suffices that all leading coefficients but one are regular
/--
theorem `leadingCoeff_prod_of_regular` / 定理 `leadingCoeff_prod_of_regular`

English:
theorem leadingCoeff_prod_of_regular
  statement: {ι : Type*}
  proof: by
  simp only [leadingCoeff, degree_prod_of_regular H, coeff_prod_sum_degree]

中文:
定理 leadingCoeff_prod_of_regular
  结论: {ι : 类型}
  证明: by
  simp only [leadingCoeff, degree_prod_of_regular H, coeff_prod_sum_degree]

Depends on / 依赖: coeff_prod_sum_degree, degree_prod_of_regular, leadingCoeff
-/
theorem leadingCoeff_prod_of_regular {ι : Type*}
    {P : ι -> MvPolynomial σ R} {s : Finset ι} (H : forall i in s, IsRegular (m.leadingCoeff (P i))) :
    m.leadingCoeff (∏ i in s, P i) = ∏ i in s, m.leadingCoeff (P i) := by
  simp only [leadingCoeff, degree_prod_of_regular H, coeff_prod_sum_degree]

/--
theorem `Monic.prod` / 定理 `Monic.prod`

English:
theorem Monic.prod
  statement: {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι}
  proof: by
  rw [Monic]; rw [leadingCoeff_prod_of_regular]
  · exact Finset.prod_eq_one H
  · intro i hi
    rw [(H i hi).leadingCoeff_eq_one]
    exact isRegular_one

中文:
定理 Monic.乘积
  结论: {ι : 类型} {P : ι -> 多元多项式 σ R} {s : 有限集 ι}
  证明: by
  rw [Monic]; rw [leadingCoeff_prod_of_regular]
  · exact Finset.prod_eq_one H
  · intro i hi
    rw [(H i hi).leadingCoeff_eq_one]
    exact isRegular_one
-/
protected theorem Monic.prod {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι}
    (H : forall i in s, m.Monic (P i)) :
    m.Monic (∏ i in s, P i) := by
  rw [Monic]; rw [leadingCoeff_prod_of_regular]
  · exact Finset.prod_eq_one H
  · intro i hi
    rw [(H i hi).leadingCoeff_eq_one]
    exact isRegular_one

/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
@[simp]
/--
lemma `leadingTerm_eq_zero_iff` / 引理 `leadingTerm_eq_zero_iff`

English:
lemma leadingTerm_eq_zero_iff
  given: (p : MvPolynomial σ R)
  statement: m.leadingTerm p = 0 ↔ p = 0
  proof: by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

中文:
引理 leadingTerm_eq_zero_iff
  条件: (p : 多元多项式 σ R)
  结论: m.leadingTerm p = 0 ↔ p = 0
  证明: by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

Depends on / 依赖: leadingCoeff_eq_zero_iff, leadingTerm, monomial_eq_zero
-/
lemma leadingTerm_eq_zero_iff (p : MvPolynomial σ R) : m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

/-- The leading term of the zero polynomial is zero -/
@[simp]
/--
lemma `leadingTerm_zero` / 引理 `leadingTerm_zero`

English:
lemma leadingTerm_zero
  statement: m.leadingTerm (0 : MvPolynomial σ R) = 0
  proof: by
  rw [leadingTerm_eq_zero_iff]

中文:
引理 leadingTerm_zero
  结论: m.leadingTerm (0 : 多元多项式 σ R) = 0
  证明: by
  rw [leadingTerm_eq_zero_iff]

Depends on / 依赖: leadingTerm_eq_zero_iff
-/
lemma leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0 := by
  rw [leadingTerm_eq_zero_iff]

/--
lemma `image_leadingTerm_sdiff_singleton_zero` / 引理 `image_leadingTerm_sdiff_singleton_zero`

English:
lemma image_leadingTerm_sdiff_singleton_zero
  given: (B : Set (MvPolynomial σ R))
  proof: by
  aesop

中文:
引理 image_leadingTerm_sdiff_singleton_zero
  条件: (B : 集合 (多元多项式 σ R))
  证明: by
  aesop
-/
lemma image_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0} := by
  aesop

/--
lemma `image_leadingTerm_insert_zero` / 引理 `image_leadingTerm_insert_zero`

English:
lemma image_leadingTerm_insert_zero
  given: (B : Set (MvPolynomial σ R))
  proof: by
  aesop

中文:
引理 image_leadingTerm_insert_zero
  条件: (B : 集合 (多元多项式 σ R))
  证明: by
  aesop
-/
lemma image_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B) := by
  aesop

/-- The degree of `f` equals to the degree of `leadingTerm f` -/
@[simp]
/--
lemma `degree_leadingTerm` / 引理 `degree_leadingTerm`

English:
lemma degree_leadingTerm
  given: (f : MvPolynomial σ R)
  proof: by
  classical
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

@[simp]

中文:
引理 degree_leadingTerm
  条件: (f : 多元多项式 σ R)
  证明: by
  classical
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

@[simp]

Depends on / 依赖: classical, degree_monomial, ite_eq_right_iff, leadingCoeff_eq_zero_iff, leadingTerm, simp_intro
-/
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

@[simp]
/--
lemma `leadingCoeff_leadingTerm` / 引理 `leadingCoeff_leadingTerm`

English:
lemma leadingCoeff_leadingTerm
  given: (f : MvPolynomial σ R)
  proof: by
  simp [leadingTerm, leadingCoeff_monomial]

@[simp]

中文:
引理 leadingCoeff_leadingTerm
  条件: (f : 多元多项式 σ R)
  证明: by
  simp [leadingTerm, leadingCoeff_monomial]

@[simp]

Depends on / 依赖: leadingCoeff_monomial, leadingTerm
-/
lemma leadingCoeff_leadingTerm (f : MvPolynomial σ R) :
    m.leadingCoeff (m.leadingTerm f) = m.leadingCoeff f := by
  simp [leadingTerm, leadingCoeff_monomial]

@[simp]
/--
lemma `leadingTerm_leadingTerm` / 引理 `leadingTerm_leadingTerm`

English:
lemma leadingTerm_leadingTerm
  given: (f : MvPolynomial σ R)
  proof: by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm, h, degree_monomial]

@[simp]

中文:
引理 leadingTerm_leadingTerm
  条件: (f : 多元多项式 σ R)
  证明: by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm, h, degree_monomial]

@[simp]

Depends on / 依赖: classical, degree_monomial, leadingTerm
-/
lemma leadingTerm_leadingTerm (f : MvPolynomial σ R) :
    m.leadingTerm (m.leadingTerm f) = m.leadingTerm f := by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm, h, degree_monomial]

@[simp]
/--
lemma `leadingTerm_C` / 引理 `leadingTerm_C`

English:
lemma leadingTerm_C
  given: (c : R)
  statement: m.leadingTerm (C c) = C c
  proof: by
  simp [leadingTerm, leadingCoeff_C]

@[simp]

中文:
引理 leadingTerm_C
  条件: (c : R)
  结论: m.leadingTerm (C c) = C c
  证明: by
  simp [leadingTerm, leadingCoeff_C]

@[simp]

Depends on / 依赖: leadingCoeff_C, leadingTerm
-/
lemma leadingTerm_C (c : R) : m.leadingTerm (C c) = C c := by
  simp [leadingTerm, leadingCoeff_C]

@[simp]
/--
lemma `leadingTerm_monomial` / 引理 `leadingTerm_monomial`

English:
lemma leadingTerm_monomial
  given: (s : σ ->₀ Nat) (c : R)
  proof: by
  classical
  by_cases h : c = 0 <;> simp [leadingTerm, degree_monomial, h]

@[simp]

中文:
引理 leadingTerm_monomial
  条件: (s : σ ->₀ 自然数) (c : R)
  证明: by
  classical
  by_cases h : c = 0 <;> simp [leadingTerm, degree_monomial, h]

@[simp]

Depends on / 依赖: classical, degree_monomial, leadingTerm
-/
lemma leadingTerm_monomial (s : σ ->₀ Nat) (c : R) :
    m.leadingTerm (monomial s c) = monomial s c := by
  classical
  by_cases h : c = 0 <;> simp [leadingTerm, degree_monomial, h]

@[simp]
/--
lemma `degree_leadingTerm_mul` / 引理 `degree_leadingTerm_mul`

English:
lemma degree_leadingTerm_mul
  given: [NoZeroDivisors R] (p q : MvPolynomial σ R)
  proof: by
  wlog! +distrib h : p != 0 ∧ q != 0
  · obtain rfl | rfl := h <;> simp
  classical
  simp [leadingTerm, degree_mul, h, degree_monomial]

@[simp]

中文:
引理 degree_leadingTerm_mul
  条件: [无零因子 R] (p q : 多元多项式 σ R)
  证明: by
  wlog! +distrib h : p != 0 ∧ q != 0
  · obtain rfl | rfl := h <;> simp
  classical
  simp [leadingTerm, degree_mul, h, degree_monomial]

@[simp]

Depends on / 依赖: classical, degree_monomial, degree_mul, distrib, leadingTerm
-/
lemma degree_leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.degree (m.leadingTerm p * q) = m.degree (p * q) := by
  wlog! +distrib h : p != 0 ∧ q != 0
  · obtain rfl | rfl := h <;> simp
  classical
  simp [leadingTerm, degree_mul, h, degree_monomial]

@[simp]
/--
lemma `degree_mul_leadingTerm` / 引理 `degree_mul_leadingTerm`

English:
lemma degree_mul_leadingTerm
  given: [NoZeroDivisors R] (p q : MvPolynomial σ R)
  proof: mul_comm _ p ▸ mul_comm _ p ▸ m.degree_leadingTerm_mul q p

中文:
引理 degree_mul_leadingTerm
  条件: [无零因子 R] (p q : 多元多项式 σ R)
  证明: mul_comm _ p ▸ mul_comm _ p ▸ m.degree_leadingTerm_mul q p

Depends on / 依赖: degree_leadingTerm_mul, m.degree_leadingTerm_mul, mul_comm
-/
lemma degree_mul_leadingTerm [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.degree (p * m.leadingTerm q) = m.degree (p * q) :=
  mul_comm _ p ▸ mul_comm _ p ▸ m.degree_leadingTerm_mul q p

/--
lemma `degree_lt_of_left_ne_zero_of_degree_mul_lt` / 引理 `degree_lt_of_left_ne_zero_of_degree_mul_lt`

English:
lemma degree_lt_of_left_ne_zero_of_degree_mul_lt
  statement: [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
  proof: by
  wlog! hq : q != 0
  · simp [hq] at h
  apply lt_of_le_of_lt' m.degree_mul_le at h
  simpa [m.degree_mul hp hq] using h

中文:
引理 degree_lt_of_left_ne_zero_of_degree_mul_lt
  结论: [无零因子 R] {p p' q : 多元多项式 σ R}
  证明: by
  wlog! hq : q != 0
  · simp [hq] at h
  apply lt_of_le_of_lt' m.degree_mul_le at h
  simpa [m.degree_mul hp hq] using h

Depends on / 依赖: degree_mul, degree_mul_le, lt_of_le_of_lt, m.degree_mul, m.degree_mul_le
-/
lemma degree_lt_of_left_ne_zero_of_degree_mul_lt [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
    (hp : p != 0) (h : m.degree (p * q) ≺[m] m.degree (p' * q)) :
    m.degree p ≺[m] m.degree p' := by
  wlog! hq : q != 0
  · simp [hq] at h
  apply lt_of_le_of_lt' m.degree_mul_le at h
  simpa [m.degree_mul hp hq] using h

/--
lemma `degree_mul_lt_iff_left_lt_of_ne_zero` / 引理 `degree_mul_lt_iff_left_lt_of_ne_zero`

English:
lemma degree_mul_lt_iff_left_lt_of_ne_zero
  statement: [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
  proof: by
  refine ⟨m.degree_lt_of_left_ne_zero_of_degree_mul_lt hp, ?_⟩
  intro h
  simpa [m.degree_mul hp hq, m.degree_mul (show p' != 0 by contrapose! h; simp [h]) hq] using h

@[simp]

中文:
引理 degree_mul_lt_iff_left_lt_of_ne_zero
  结论: [无零因子 R] {p p' q : 多元多项式 σ R}
  证明: by
  refine ⟨m.degree_lt_of_left_ne_zero_of_degree_mul_lt hp, ?_⟩
  intro h
  simpa [m.degree_mul hp hq, m.degree_mul (show p' != 0 by contrapose! h; simp [h]) hq] using h

@[simp]

Depends on / 依赖: contrapose, degree_lt_of_left_ne_zero_of_degree_mul_lt, degree_mul, m.degree_lt_of_left_ne_zero_of_degree_mul_lt, m.degree_mul
-/
lemma degree_mul_lt_iff_left_lt_of_ne_zero [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
    (hp : p != 0) (hq : q != 0) :
    m.degree (p * q) ≺[m] m.degree (p' * q) ↔ m.degree p ≺[m] m.degree p' := by
  refine ⟨m.degree_lt_of_left_ne_zero_of_degree_mul_lt hp, ?_⟩
  intro h
  simpa [m.degree_mul hp hq, m.degree_mul (show p' != 0 by contrapose! h; simp [h]) hq] using h

@[simp]
/--
lemma `monic_leadingTerm` / 引理 `monic_leadingTerm`

English:
lemma monic_leadingTerm
  given: (p : MvPolynomial σ R)
  proof: by simp [leadingTerm, Monic]

中文:
引理 monic_leadingTerm
  条件: (p : 多元多项式 σ R)
  证明: by simp [leadingTerm, Monic]

Depends on / 依赖: leadingTerm
-/
lemma monic_leadingTerm (p : MvPolynomial σ R) :
    m.Monic (m.leadingTerm p) ↔ m.Monic p := by simp [leadingTerm, Monic]

/--
lemma `support_leadingTerm` / 引理 `support_leadingTerm`

English:
lemma support_leadingTerm
  given: (p : MvPolynomial σ R) [Decidable (p = 0)]
  proof: by
  classical
  simp [leadingTerm, support_monomial]

中文:
引理 support_leadingTerm
  条件: (p : 多元多项式 σ R) [可判定 (p = 0)]
  证明: by
  classical
  simp [leadingTerm, support_monomial]

Depends on / 依赖: classical, leadingTerm, support_monomial
-/
lemma support_leadingTerm (p : MvPolynomial σ R) [Decidable (p = 0)] :
    support (m.leadingTerm p) = if p = 0 then ∅ else {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial]

/--
lemma `support_leadingTerm'` / 引理 `support_leadingTerm'`

English:
lemma support_leadingTerm'
  given: {p : MvPolynomial σ R} (hp : p != 0)
  proof: by
  classical
  simp [leadingTerm, support_monomial, hp]

中文:
引理 support_leadingTerm'
  条件: {p : 多元多项式 σ R} (hp : p != 0)
  证明: by
  classical
  simp [leadingTerm, support_monomial, hp]

Depends on / 依赖: classical, leadingTerm, support_monomial
-/
lemma support_leadingTerm' {p : MvPolynomial σ R} (hp : p != 0) :
    support (m.leadingTerm p) = {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial, hp]

/--
lemma `le_degree_of_mem_support` / 引理 `le_degree_of_mem_support`

English:
lemma le_degree_of_mem_support
  statement: {p : MvPolynomial σ R} {a : σ ->₀ Nat}
  proof: by
  simp [degree, Finset.le_sup ha]

中文:
引理 le_degree_of_mem_support
  结论: {p : 多元多项式 σ R} {a : σ ->₀ 自然数}
  证明: by
  simp [degree, Finset.le_sup ha]

Depends on / 依赖: Finset, Finset.le_sup, degree, le_sup
-/
lemma le_degree_of_mem_support {p : MvPolynomial σ R} {a : σ ->₀ Nat}
    (ha : a in p.support) : a ≼[m] m.degree p := by
  simp [degree, Finset.le_sup ha]

/--
lemma `leadingTerm_eq_leadingTerm_iff` / 引理 `leadingTerm_eq_leadingTerm_iff`

English:
lemma leadingTerm_eq_leadingTerm_iff
  given: {p q : MvPolynomial σ R}
  proof: by
  rw [leadingTerm]; rw [leadingTerm]; rw [monomial_eq_monomial_iff]
  aesop

@[simp]

中文:
引理 leadingTerm_eq_leadingTerm_iff
  条件: {p q : 多元多项式 σ R}
  证明: by
  rw [leadingTerm]; rw [leadingTerm]; rw [monomial_eq_monomial_iff]
  aesop

@[simp]

Depends on / 依赖: leadingTerm, monomial_eq_monomial_iff
-/
lemma leadingTerm_eq_leadingTerm_iff {p q : MvPolynomial σ R} :
    m.leadingTerm p = m.leadingTerm q ↔
    m.leadingCoeff p = m.leadingCoeff q ∧ m.degree p = m.degree q := by
  rw [leadingTerm]; rw [leadingTerm]; rw [monomial_eq_monomial_iff]
  aesop

@[simp]
/--
theorem `leadingTerm_mul` / 定理 `leadingTerm_mul`

English:
theorem leadingTerm_mul
  given: [NoZeroDivisors R] (p q : MvPolynomial σ R)
  proof: by
  by_cases! h0 : p * q = 0
  · simp [h0, zero_eq_mul.mp]
  simp [leadingTerm, m.degree_mul' h0]

@[simp, nontriviality]

中文:
定理 leadingTerm_mul
  条件: [无零因子 R] (p q : 多元多项式 σ R)
  证明: by
  by_cases! h0 : p * q = 0
  · simp [h0, zero_eq_mul.mp]
  simp [leadingTerm, m.degree_mul' h0]

@[simp, nontriviality]

Depends on / 依赖: degree_mul, leadingTerm, m.degree_mul, zero_eq_mul, zero_eq_mul.mp
-/
theorem leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.leadingTerm (p * q) = m.leadingTerm p * m.leadingTerm q := by
  by_cases! h0 : p * q = 0
  · simp [h0, zero_eq_mul.mp]
  simp [leadingTerm, m.degree_mul' h0]

@[simp, nontriviality]
/--
lemma `monic_of_subsingleton` / 引理 `monic_of_subsingleton`

English:
lemma monic_of_subsingleton
  given: [Subsingleton R] (p : MvPolynomial σ R)
  proof: by
  simp [Subsingleton.eq_one (α := MvPolynomial σ R)]

中文:
引理 monic_of_subsingleton
  条件: [子单例 R] (p : 多元多项式 σ R)
  证明: by
  simp [Subsingleton.eq_one (α := MvPolynomial σ R)]

Depends on / 依赖: MvPolynomial, Subsingleton, Subsingleton.eq_one, eq_one
-/
lemma monic_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) :
    m.Monic p := by
  simp [Subsingleton.eq_one (α := MvPolynomial σ R)]

/--
lemma `degree_le_degree_of_support_subset` / 引理 `degree_le_degree_of_support_subset`

English:
lemma degree_le_degree_of_support_subset
  given: {p q : MvPolynomial σ R} (h : p.support subseteq q.support)
  proof: by
  simp_rw [degree, m.toSyn.apply_symm_apply]
  exact Finset.sup_mono h

中文:
引理 degree_le_degree_of_support_subset
  条件: {p q : 多元多项式 σ R} (h : p.support subseteq q.support)
  证明: by
  simp_rw [degree, m.toSyn.apply_symm_apply]
  exact Finset.sup_mono h

Depends on / 依赖: Finset, Finset.sup_mono, apply_symm_apply, degree, m.toSyn.apply_symm_apply, simp_rw, sup_mono
-/
lemma degree_le_degree_of_support_subset {p q : MvPolynomial σ R} (h : p.support subseteq q.support) :
    m.degree p ≼[m] m.degree q := by
  simp_rw [degree, m.toSyn.apply_symm_apply]
  exact Finset.sup_mono h

/--
theorem `toSyn_degree_mul_le` / 定理 `toSyn_degree_mul_le`

English:
theorem toSyn_degree_mul_le
  given: {f g : MvPolynomial σ R}
  proof: map_add m.toSyn _ _ ▸ degree_mul_le

中文:
定理 toSyn_degree_mul_le
  条件: {f g : 多元多项式 σ R}
  证明: map_add m.toSyn _ _ ▸ degree_mul_le

Depends on / 依赖: degree_mul_le, m.toSyn, map_add
-/
theorem toSyn_degree_mul_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f * g)) <= m.toSyn (m.degree f) + m.toSyn (m.degree g) :=
  map_add m.toSyn _ _ ▸ degree_mul_le

/--
lemma `mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors` / 引理 `mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors`

English:
lemma mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
  proof: by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rw [mem_nonZeroDivisorsLeft_iff]
  intro g
  simp [← m.leadingCoeff_eq_zero_iff (f := f * g),
    m.leadingCoeff_mul_of_left_mem_nonZeroDivisors hf, mul_left_mem_nonZeroDivisors_eq_zero_iff hf]

中文:
引理 mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
  证明: by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rw [mem_nonZeroDivisorsLeft_iff]
  intro g
  simp [← m.leadingCoeff_eq_zero_iff (f := f * g),
    m.leadingCoeff_mul_of_left_mem_nonZeroDivisors hf, mul_left_mem_nonZeroDivisors_eq_zero_iff hf]

Depends on / 依赖: leadingCoeff_eq_zero_iff, leadingCoeff_mul_of_left_mem_nonZeroDivisors, m.leadingCoeff_eq_zero_iff, m.leadingCoeff_mul_of_left_mem_nonZeroDivisors, mem_nonZeroDivisorsLeft_iff, mul_left_mem_nonZeroDivisors_eq_zero_iff, nonZeroDivisorsLeft_eq_nonZeroDivisors
-/
lemma mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
    {f : MvPolynomial σ R} (hf : m.leadingCoeff f in R⁰) : f in (MvPolynomial σ R)⁰ := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rw [mem_nonZeroDivisorsLeft_iff]
  intro g
  simp [← m.leadingCoeff_eq_zero_iff (f := f * g),
    m.leadingCoeff_mul_of_left_mem_nonZeroDivisors hf, mul_left_mem_nonZeroDivisors_eq_zero_iff hf]

section withBotDegree

variable (f g : MvPolynomial σ R)

variable (m) in
/--
Definition of `withBotDegree` / `withBotDegree` 的定义

English:
definition withBotDegree
  signature: : WithBot (σ ->₀ Nat)
  body: .max.map m.toSyn.symm f.support.image m.toSyn

中文:
定义 withBotDegree
  签名: : WithBot (σ ->₀ 自然数)
  定义体: .max.map m.toSyn.symm f.support.image m.toSyn

Depends on / 依赖: f.support.image, m.toSyn, m.toSyn.symm, max.map, support
-/
noncomputable def withBotDegree : WithBot (σ ->₀ Nat) :=
.max.map m.toSyn.symm f.support.image m.toSyn

/--
lemma `withBotDegree_eq` / 引理 `withBotDegree_eq`

English:
lemma withBotDegree_eq
  given: [Decidable (f = 0)]
  proof: by
  simp [withBotDegree, degree]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, Finset.max_eq_sup_coe, ← Finset.coe_sup_of_nonempty _ (⇑m.toSyn)]

@[simp]

中文:
引理 withBotDegree_eq
  条件: [可判定 (f = 0)]
  证明: by
  simp [withBotDegree, degree]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, Finset.max_eq_sup_coe, ← Finset.coe_sup_of_nonempty _ (⇑m.toSyn)]

@[simp]

Depends on / 依赖: Finset, Finset.coe_sup_of_nonempty, Finset.max_eq_sup_coe, coe_sup_of_nonempty, degree, m.toSyn, max_eq_sup_coe, withBotDegree
-/
lemma withBotDegree_eq [Decidable (f = 0)] :
    m.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f) := by
  simp [withBotDegree, degree]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, Finset.max_eq_sup_coe, ← Finset.coe_sup_of_nonempty _ (⇑m.toSyn)]

@[simp]
/--
lemma `withBotDegree_eq_coe_degree_iff` / 引理 `withBotDegree_eq_coe_degree_iff`

English:
lemma withBotDegree_eq_coe_degree_iff
  statement: m.withBotDegree f = m.degree f ↔ f != 0
  proof: by
  classical
  simp [withBotDegree_eq]

@[simp]

中文:
引理 withBotDegree_eq_coe_degree_iff
  结论: m.withBotDegree f = m.degree f ↔ f != 0
  证明: by
  classical
  simp [withBotDegree_eq]

@[simp]

Depends on / 依赖: classical, withBotDegree_eq
-/
lemma withBotDegree_eq_coe_degree_iff : m.withBotDegree f = m.degree f ↔ f != 0 := by
  classical
  simp [withBotDegree_eq]

@[simp]
/--
lemma `withBotDegree_eq_bot_iff` / 引理 `withBotDegree_eq_bot_iff`

English:
lemma withBotDegree_eq_bot_iff
  statement: m.withBotDegree f = ⊥ ↔ f = 0
  proof: by
  classical
  simp [withBotDegree_eq]

中文:
引理 withBotDegree_eq_bot_iff
  结论: m.withBotDegree f = ⊥ ↔ f = 0
  证明: by
  classical
  simp [withBotDegree_eq]

Depends on / 依赖: classical, withBotDegree_eq
-/
lemma withBotDegree_eq_bot_iff : m.withBotDegree f = ⊥ ↔ f = 0 := by
  classical
  simp [withBotDegree_eq]

/--
lemma `degree_eq_unbotD_withBotDegree` / 引理 `degree_eq_unbotD_withBotDegree`

English:
lemma degree_eq_unbotD_withBotDegree
  statement: m.degree f = (m.withBotDegree f).unbotD 0
  proof: by
  classical
  by_cases h : f = 0 <;> simp [withBotDegree_eq, h]

@[simp]

中文:
引理 degree_eq_unbotD_withBotDegree
  结论: m.degree f = (m.withBotDegree f).unbotD 0
  证明: by
  classical
  by_cases h : f = 0 <;> simp [withBotDegree_eq, h]

@[simp]

Depends on / 依赖: classical, withBotDegree_eq
-/
lemma degree_eq_unbotD_withBotDegree : m.degree f = (m.withBotDegree f).unbotD 0 := by
  classical
  by_cases h : f = 0 <;> simp [withBotDegree_eq, h]

@[simp]
/--
lemma `withBotDegree_zero` / 引理 `withBotDegree_zero`

English:
lemma withBotDegree_zero
  statement: m.withBotDegree (R := R) 0 = ⊥
  proof: rfl

中文:
引理 withBotDegree_zero
  结论: m.withBotDegree (R := R) 0 = ⊥
  证明: rfl
-/
lemma withBotDegree_zero : m.withBotDegree (R := R) 0 = ⊥ := rfl

/--
lemma `withBotDegree_monomial` / 引理 `withBotDegree_monomial`

English:
lemma withBotDegree_monomial
  given: (d) (c) [Decidable (c = 0)]
  proof: by
  classical
  split_ifs <;> simp [withBotDegree_eq, *, m.degree_monomial]

中文:
引理 withBotDegree_monomial
  条件: (d) (c) [可判定 (c = 0)]
  证明: by
  classical
  split_ifs <;> simp [withBotDegree_eq, *, m.degree_monomial]

Depends on / 依赖: classical, degree_monomial, m.degree_monomial, monomial, split_ifs, withBotDegree_eq
-/
lemma withBotDegree_monomial (d) (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (monomial d c) = if c = 0 then ⊥ else ↑d := by
  classical
  split_ifs <;> simp [withBotDegree_eq, *, m.degree_monomial]

/--
lemma `withBotDegree_C` / 引理 `withBotDegree_C`

English:
lemma withBotDegree_C
  given: (c) [Decidable (c = 0)]
  proof: by
  simp [← monomial_zero', withBotDegree_monomial]

@[simp]

中文:
引理 withBotDegree_C
  条件: (c) [可判定 (c = 0)]
  证明: by
  simp [← monomial_zero', withBotDegree_monomial]

@[simp]

Depends on / 依赖: monomial_zero, withBotDegree_monomial
-/
lemma withBotDegree_C (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (C c) = if c = 0 then ⊥ else 0 := by
  simp [← monomial_zero', withBotDegree_monomial]

@[simp]
/--
lemma `withBotDegree_leadingTerm` / 引理 `withBotDegree_leadingTerm`

English:
lemma withBotDegree_leadingTerm
  statement: m.withBotDegree (m.leadingTerm f) = m.withBotDegree f
  proof: by
  classical
  simp [withBotDegree_eq]

@[simp]

中文:
引理 withBotDegree_leadingTerm
  结论: m.withBotDegree (m.leadingTerm f) = m.withBotDegree f
  证明: by
  classical
  simp [withBotDegree_eq]

@[simp]

Depends on / 依赖: classical, withBotDegree_eq
-/
lemma withBotDegree_leadingTerm : m.withBotDegree (m.leadingTerm f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq]

@[simp]
/--
lemma `withBotDegree_one` / 引理 `withBotDegree_one`

English:
lemma withBotDegree_one
  given: [Nontrivial R]
  statement: m.withBotDegree (R := R) 1 = 0
  proof: by
  classical
  simp [withBotDegree_eq]

中文:
引理 withBotDegree_one
  条件: [非平凡 R]
  结论: m.withBotDegree (R := R) 1 = 0
  证明: by
  classical
  simp [withBotDegree_eq]

Depends on / 依赖: classical, withBotDegree_eq
-/
lemma withBotDegree_one [Nontrivial R] : m.withBotDegree (R := R) 1 = 0 := by
  classical
  simp [withBotDegree_eq]

variable {f g} in
/--
lemma `withBotDegree_mul_of_left_mem_nonZeroDivisors` / 引理 `withBotDegree_mul_of_left_mem_nonZeroDivisors`

English:
lemma withBotDegree_mul_of_left_mem_nonZeroDivisors
  given: (hf : m.leadingCoeff f in nonZeroDivisors _)
  proof: by
  classical
  by_cases! h0 : f = 0 ∨ g = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  suffices f * g != 0 by simp [withBotDegree_eq, m.degree_mul_of_left_mem_nonZeroDivisors hf, *]
  apply mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors at hf
  rw [mem_nonZeroDivisors_iff_left] at hf
  tauto

中文:
引理 withBotDegree_mul_of_left_mem_nonZeroDivisors
  条件: (hf : m.leadingCoeff f in nonZeroDivisors _)
  证明: by
  classical
  by_cases! h0 : f = 0 ∨ g = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  suffices f * g != 0 by simp [withBotDegree_eq, m.degree_mul_of_left_mem_nonZeroDivisors hf, *]
  apply mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors at hf
  rw [mem_nonZeroDivisors_iff_left] at hf
  tauto

Depends on / 依赖: classical, degree_mul_of_left_mem_nonZeroDivisors, m.degree_mul_of_left_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left, mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors, withBotDegree_eq
-/
lemma withBotDegree_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f in nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  classical
  by_cases! h0 : f = 0 ∨ g = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  suffices f * g != 0 by simp [withBotDegree_eq, m.degree_mul_of_left_mem_nonZeroDivisors hf, *]
  apply mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors at hf
  rw [mem_nonZeroDivisors_iff_left] at hf
  tauto

variable {f g} in
/--
lemma `withBotDegree_mul_of_right_mem_nonZeroDivisors` / 引理 `withBotDegree_mul_of_right_mem_nonZeroDivisors`

English:
lemma withBotDegree_mul_of_right_mem_nonZeroDivisors
  given: (hf : m.leadingCoeff g in nonZeroDivisors _)
  proof: by
  rw [mul_comm]; rw [add_comm]; rw [withBotDegree_mul_of_left_mem_nonZeroDivisors (hf := hf)]

@[simp]

中文:
引理 withBotDegree_mul_of_right_mem_nonZeroDivisors
  条件: (hf : m.leadingCoeff g in nonZeroDivisors _)
  证明: by
  rw [mul_comm]; rw [add_comm]; rw [withBotDegree_mul_of_left_mem_nonZeroDivisors (hf := hf)]

@[simp]

Depends on / 依赖: add_comm, mul_comm, withBotDegree_mul_of_left_mem_nonZeroDivisors
-/
lemma withBotDegree_mul_of_right_mem_nonZeroDivisors (hf : m.leadingCoeff g in nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  rw [mul_comm]; rw [add_comm]; rw [withBotDegree_mul_of_left_mem_nonZeroDivisors (hf := hf)]

@[simp]
/--
lemma `withBotDegree_mul` / 引理 `withBotDegree_mul`

English:
lemma withBotDegree_mul
  given: [NoZeroDivisors R]
  proof: by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  by_cases! hf : f = 0
  · simp [hf]
  rw [← m.leadingCoeff_ne_zero_iff]; rw [← mem_nonZeroDivisors_iff_ne_zero] at hf
  exact m.withBotDegree_mul_of_left_mem_nonZeroDivisors hf

中文:
引理 withBotDegree_mul
  条件: [无零因子 R]
  证明: by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  by_cases! hf : f = 0
  · simp [hf]
  rw [← m.leadingCoeff_ne_zero_iff]; rw [← mem_nonZeroDivisors_iff_ne_zero] at hf
  exact m.withBotDegree_mul_of_left_mem_nonZeroDivisors hf

Depends on / 依赖: MvPolynomial, Subsingleton, Subsingleton.eq_zero, eq_zero, leadingCoeff_ne_zero_iff, m.leadingCoeff_ne_zero_iff, m.withBotDegree_mul_of_left_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_ne_zero, nontriviality, withBotDegree_mul_of_left_mem_nonZeroDivisors
-/
lemma withBotDegree_mul [NoZeroDivisors R] :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  by_cases! hf : f = 0
  · simp [hf]
  rw [← m.leadingCoeff_ne_zero_iff]; rw [← mem_nonZeroDivisors_iff_ne_zero] at hf
  exact m.withBotDegree_mul_of_left_mem_nonZeroDivisors hf

/--
lemma `withBotDegree_mul_le` / 引理 `withBotDegree_mul_le`

English:
lemma withBotDegree_mul_le
  proof: by
  by_cases! h0 : f * g = 0
  · simp [h0]
  simp [-map_add, m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0,
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff f
.mpr (by grind), ← WithBot.coe_add, m.degree_mul_le] m.withBotDegree_eq_coe_degree_iff g

中文:
引理 withBotDegree_mul_le
  证明: by
  by_cases! h0 : f * g = 0
  · simp [h0]
  simp [-map_add, m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0,
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff f
.mpr (by grind), ← WithBot.coe_add, m.degree_mul_le] m.withBotDegree_eq_coe_degree_iff g

Depends on / 依赖: WithBot, WithBot.coe_add, coe_add, degree_mul_le, m.degree_mul_le, m.withBotDegree_eq_coe_degree_iff, map_add, withBotDegree_eq_coe_degree_iff
-/
lemma withBotDegree_mul_le :
    m.withBotDegree (f * g) ≼'[m] m.withBotDegree f + m.withBotDegree g := by
  by_cases! h0 : f * g = 0
  · simp [h0]
  simp [-map_add, m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0,
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff f
.mpr (by grind), ← WithBot.coe_add, m.degree_mul_le] m.withBotDegree_eq_coe_degree_iff g

/--
lemma `toWithBotSyn_withBotDegree_mul_le` / 引理 `toWithBotSyn_withBotDegree_mul_le`

English:
lemma toWithBotSyn_withBotDegree_mul_le
  proof: by
  by_cases h0 : f * g = 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by grind),
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff g
.mpr h0, ← WithBot.coe_add, m.withBotDegree_eq_coe_degree_iff _
    m.toSyn_degree_mul_le]

中文:
引理 toWithBotSyn_withBotDegree_mul_le
  证明: by
  by_cases h0 : f * g = 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by grind),
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff g
.mpr h0, ← WithBot.coe_add, m.withBotDegree_eq_coe_degree_iff _
    m.toSyn_degree_mul_le]

Depends on / 依赖: WithBot, WithBot.coe_add, coe_add, m.toSyn_degree_mul_le, m.withBotDegree_eq_coe_degree_iff, toSyn_degree_mul_le, withBotDegree_eq_coe_degree_iff
-/
lemma toWithBotSyn_withBotDegree_mul_le :
    m.toWithBotSyn (m.withBotDegree (f * g)) <=
      m.toWithBotSyn (m.withBotDegree f) + m.toWithBotSyn (m.withBotDegree g) := by
  by_cases h0 : f * g = 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by grind),
.mpr (by grind), m.withBotDegree_eq_coe_degree_iff g
.mpr h0, ← WithBot.coe_add, m.withBotDegree_eq_coe_degree_iff _
    m.toSyn_degree_mul_le]

/--
lemma `withBotDegree_le_withBotDegree_iff` / 引理 `withBotDegree_le_withBotDegree_iff`

English:
lemma withBotDegree_le_withBotDegree_iff
  proof: by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]
  rcases h with h | _
  · simp [h]
  · aesop

中文:
引理 withBotDegree_le_withBotDegree_iff
  证明: by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]
  rcases h with h | _
  · simp [h]
  · aesop

Depends on / 依赖: classical, distrib, m.toWithBotSyn_apply, m.withBotDegree_eq, toWithBotSyn_apply, withBotDegree_eq
-/
lemma withBotDegree_le_withBotDegree_iff :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔
      (m.degree f ≼[m] m.degree g ∧ (g = 0 -> f = 0)) := by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]
  rcases h with h | _
  · simp [h]
  · aesop

variable {g} in
/--
lemma `withBotDegree_le_withBotDegree_iff_of_ne_zero` / 引理 `withBotDegree_le_withBotDegree_iff_of_ne_zero`

English:
lemma withBotDegree_le_withBotDegree_iff_of_ne_zero
  given: (hg : g != 0)
  proof: by
  simp [withBotDegree_le_withBotDegree_iff, hg]

中文:
引理 withBotDegree_le_withBotDegree_iff_of_ne_zero
  条件: (hg : g != 0)
  证明: by
  simp [withBotDegree_le_withBotDegree_iff, hg]

Depends on / 依赖: withBotDegree_le_withBotDegree_iff
-/
lemma withBotDegree_le_withBotDegree_iff_of_ne_zero (hg : g != 0) :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔ m.degree f ≼[m] m.degree g := by
  simp [withBotDegree_le_withBotDegree_iff, hg]

/--
lemma `withBotDegree_lt_withBotDegree_iff` / 引理 `withBotDegree_lt_withBotDegree_iff`

English:
lemma withBotDegree_lt_withBotDegree_iff
  proof: by
  classical
  by_cases! hg : g = 0
  · simp_rw [toWithBotSyn_apply]
    aesop
  by_cases! hf : f = 0
  · simp [hg, hf, bot_lt_iff_ne_bot, toWithBotSyn_apply]
  simp [withBotDegree_eq, hf, hg, toWithBotSyn_apply]

中文:
引理 withBotDegree_lt_withBotDegree_iff
  证明: by
  classical
  by_cases! hg : g = 0
  · simp_rw [toWithBotSyn_apply]
    aesop
  by_cases! hf : f = 0
  · simp [hg, hf, bot_lt_iff_ne_bot, toWithBotSyn_apply]
  simp [withBotDegree_eq, hf, hg, toWithBotSyn_apply]

Depends on / 依赖: bot_lt_iff_ne_bot, classical, simp_rw, toWithBotSyn_apply, withBotDegree_eq
-/
lemma withBotDegree_lt_withBotDegree_iff :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔
      (m.degree f ≺[m] m.degree g ∨ (f = 0 ∧ g != 0)) := by
  classical
  by_cases! hg : g = 0
  · simp_rw [toWithBotSyn_apply]
    aesop
  by_cases! hf : f = 0
  · simp [hg, hf, bot_lt_iff_ne_bot, toWithBotSyn_apply]
  simp [withBotDegree_eq, hf, hg, toWithBotSyn_apply]

variable {f} in
/--
lemma `withBotDegree_lt_withBotDegree_iff_of_ne_zero` / 引理 `withBotDegree_lt_withBotDegree_iff_of_ne_zero`

English:
lemma withBotDegree_lt_withBotDegree_iff_of_ne_zero
  given: (hf : f != 0)
  proof: by
  simp [withBotDegree_lt_withBotDegree_iff, hf]

中文:
引理 withBotDegree_lt_withBotDegree_iff_of_ne_zero
  条件: (hf : f != 0)
  证明: by
  simp [withBotDegree_lt_withBotDegree_iff, hf]

Depends on / 依赖: withBotDegree_lt_withBotDegree_iff
-/
lemma withBotDegree_lt_withBotDegree_iff_of_ne_zero (hf : f != 0) :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔ m.degree f ≺[m] m.degree g := by
  simp [withBotDegree_lt_withBotDegree_iff, hf]

/--
lemma `withBotDegree_eq_withBotDegree_iff` / 引理 `withBotDegree_eq_withBotDegree_iff`

English:
lemma withBotDegree_eq_withBotDegree_iff
  proof: by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [h, m.withBotDegree_eq]
  rcases h with h | h
  all_goals
    simp_rw [h]
    revert f g
    simp [m.withBotDegree_eq, m.degree_zero]

中文:
引理 withBotDegree_eq_withBotDegree_iff
  证明: by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [h, m.withBotDegree_eq]
  rcases h with h | h
  all_goals
    simp_rw [h]
    revert f g
    simp [m.withBotDegree_eq, m.degree_zero]

Depends on / 依赖: all_goals, classical, degree_zero, distrib, m.degree_zero, m.withBotDegree_eq, revert, simp_rw, withBotDegree_eq
-/
lemma withBotDegree_eq_withBotDegree_iff :
    m.withBotDegree f = m.withBotDegree g ↔ (m.degree f = m.degree g ∧ (f = 0 ↔ g = 0)) := by
  classical
  by_cases! +distrib h : f != 0 ∧ g != 0
  · simp [h, m.withBotDegree_eq]
  rcases h with h | h
  all_goals
    simp_rw [h]
    revert f g
    simp [m.withBotDegree_eq, m.degree_zero]

/--
lemma `withBotDegree_add_le` / 引理 `withBotDegree_add_le`

English:
lemma withBotDegree_add_le
  proof: by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with h | h <;> simp [h, m.toWithBotSyn_apply]
  simpa [withBotDegree_le_withBotDegree_iff, h] using degree_add_le (R := R)

中文:
引理 withBotDegree_add_le
  证明: by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with h | h <;> simp [h, m.toWithBotSyn_apply]
  simpa [withBotDegree_le_withBotDegree_iff, h] using degree_add_le (R := R)

Depends on / 依赖: degree_add_le, m.toWithBotSyn_apply, toWithBotSyn_apply, withBotDegree_le_withBotDegree_iff
-/
lemma withBotDegree_add_le :
    (m.toWithBotSyn <| m.withBotDegree (f + g)) <=
      (m.toWithBotSyn <| m.withBotDegree f) ⊔ (m.toWithBotSyn <| m.withBotDegree g) := by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with h | h <;> simp [h, m.toWithBotSyn_apply]
  simpa [withBotDegree_le_withBotDegree_iff, h] using degree_add_le (R := R)

variable {f g} in
/--
lemma `withBotDegree_add_of_lt` / 引理 `withBotDegree_add_of_lt`

English:
lemma withBotDegree_add_of_lt
  given: (h : m.withBotDegree g ≺'[m] m.withBotDegree f)
  proof: by
  by_cases hg : g = 0
  · simp [hg]
  simp only [withBotDegree_lt_withBotDegree_iff, hg, ne_eq, false_and, or_false] at h
  simp only [withBotDegree_eq_withBotDegree_iff, show f != 0 by contrapose h; simp [h], iff_false]
  apply (show forall {p q}, p -> (p -> q) -> (p ∧ q) by tauto) (m.degree_add_of_lt h)
  intro h'
  contrapose! h
  simp [← h', h]

中文:
引理 withBotDegree_add_of_lt
  条件: (h : m.withBotDegree g ≺'[m] m.withBotDegree f)
  证明: by
  by_cases hg : g = 0
  · simp [hg]
  simp only [withBotDegree_lt_withBotDegree_iff, hg, ne_eq, false_and, or_false] at h
  simp only [withBotDegree_eq_withBotDegree_iff, show f != 0 by contrapose h; simp [h], iff_false]
  apply (show forall {p q}, p -> (p -> q) -> (p ∧ q) by tauto) (m.degree_add_of_lt h)
  intro h'
  contrapose! h
  simp [← h', h]

Depends on / 依赖: contrapose, degree_add_of_lt, false_and, iff_false, m.degree_add_of_lt, ne_eq, or_false, withBotDegree_eq_withBotDegree_iff, withBotDegree_lt_withBotDegree_iff
-/
lemma withBotDegree_add_of_lt (h : m.withBotDegree g ≺'[m] m.withBotDegree f) :
    m.withBotDegree (f + g) = m.withBotDegree f := by
  by_cases hg : g = 0
  · simp [hg]
  simp only [withBotDegree_lt_withBotDegree_iff, hg, ne_eq, false_and, or_false] at h
  simp only [withBotDegree_eq_withBotDegree_iff, show f != 0 by contrapose h; simp [h], iff_false]
  apply (show forall {p q}, p -> (p -> q) -> (p ∧ q) by tauto) (m.degree_add_of_lt h)
  intro h'
  contrapose! h
  simp [← h', h]

variable {f g} in
/--
lemma `withBotDegree_add_of_right_lt` / 引理 `withBotDegree_add_of_right_lt`

English:
lemma withBotDegree_add_of_right_lt
  given: (h : m.withBotDegree f ≺'[m] m.withBotDegree g)
  proof: by
  rw [add_comm]; rw [withBotDegree_add_of_lt h]

中文:
引理 withBotDegree_add_of_right_lt
  条件: (h : m.withBotDegree f ≺'[m] m.withBotDegree g)
  证明: by
  rw [add_comm]; rw [withBotDegree_add_of_lt h]

Depends on / 依赖: add_comm, withBotDegree_add_of_lt
-/
lemma withBotDegree_add_of_right_lt (h : m.withBotDegree f ≺'[m] m.withBotDegree g) :
    m.withBotDegree (f + g) = m.withBotDegree g := by
  rw [add_comm]; rw [withBotDegree_add_of_lt h]

/--
lemma `withBotDegree_sum_le` / 引理 `withBotDegree_sum_le`

English:
lemma withBotDegree_sum_le
  given: {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R}
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans (m.withBotDegree_add_le _ _) (max_le_max le_rfl h)

中文:
引理 withBotDegree_sum_le
  条件: {α : 类型} {s : 有限集 α} {f : α -> 多元多项式 σ R}
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans (m.withBotDegree_add_le _ _) (max_le_max le_rfl h)

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.sum_cons, Finset.sup_cons, cons_induction_on, le_rfl, le_trans, m.withBotDegree_add_le, max_le_max, sum_cons, sup_cons, withBotDegree_add_le
-/
lemma withBotDegree_sum_le {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R} :
    (m.toWithBotSyn <| m.withBotDegree <| ∑ x in s, f x) <=
      s.sup fun x => (m.toWithBotSyn <| m.withBotDegree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact le_trans (m.withBotDegree_add_le _ _) (max_le_max le_rfl h)

variable {f} in
/--
lemma `le_withBotDegree` / 引理 `le_withBotDegree`

English:
lemma le_withBotDegree
  given: {d : σ ->₀ Nat} (hd : d in f.support)
  proof: by
  classical
  simp [withBotDegree_eq, toWithBotSyn_apply, ne_zero_iff.mpr ⟨d, by simpa using hd⟩, le_degree hd]

中文:
引理 le_withBotDegree
  条件: {d : σ ->₀ 自然数} (hd : d in f.support)
  证明: by
  classical
  simp [withBotDegree_eq, toWithBotSyn_apply, ne_zero_iff.mpr ⟨d, by simpa using hd⟩, le_degree hd]

Depends on / 依赖: classical, le_degree, ne_zero_iff, ne_zero_iff.mpr, toWithBotSyn_apply, withBotDegree_eq
-/
lemma le_withBotDegree {d : σ ->₀ Nat} (hd : d in f.support) :
    d ≼'[m] m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, toWithBotSyn_apply, ne_zero_iff.mpr ⟨d, by simpa using hd⟩, le_degree hd]

variable {f g} in
/--
lemma `withBotDegree_le_withBotDegree_of_support_subset` / 引理 `withBotDegree_le_withBotDegree_of_support_subset`

English:
lemma withBotDegree_le_withBotDegree_of_support_subset
  proof: by
  by_cases hg : g = 0
  · simpa [hg] using h
  rw [m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hg]
  exact m.degree_le_degree_of_support_subset h

中文:
引理 withBotDegree_le_withBotDegree_of_support_subset
  证明: by
  by_cases hg : g = 0
  · simpa [hg] using h
  rw [m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hg]
  exact m.degree_le_degree_of_support_subset h

Depends on / 依赖: degree_le_degree_of_support_subset, m.degree_le_degree_of_support_subset, m.withBotDegree_le_withBotDegree_iff_of_ne_zero, withBotDegree_le_withBotDegree_iff_of_ne_zero
-/
lemma withBotDegree_le_withBotDegree_of_support_subset
    (h : f.support subseteq g.support) :
    m.withBotDegree f ≼'[m] m.withBotDegree g := by
  by_cases hg : g = 0
  · simpa [hg] using h
  rw [m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hg]
  exact m.degree_le_degree_of_support_subset h

end withBotDegree

end Semiring

section Ring

variable {R : Type*} [CommRing R]

variable (m) in
/--
Definition of `sPolynomial` / `sPolynomial` 的定义

English:
definition sPolynomial
  signature: (f g : MvPolynomial σ R)
  body: monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

中文:
定义 sPolynomial
  签名: (f g : 多元多项式 σ R)
  定义体: monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

Depends on / 依赖: degree, leadingCoeff, m.degree, m.leadingCoeff, monomial
-/
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

/--
lemma `sPolynomial_def` / 引理 `sPolynomial_def`

English:
lemma sPolynomial_def
  given: (f g : MvPolynomial σ R)
  proof: by
  suffices forall f g, m.degree g - m.degree f = m.degree f ⊔ m.degree g - m.degree f by
    rw [sPolynomial]; rw [this]; rw [this]; rw [sup_comm]
  intro f g
  ext a
  obtain (h | h) := le_total (m.degree f a) (m.degree g a) <;> simp [h]

中文:
引理 sPolynomial_def
  条件: (f g : 多元多项式 σ R)
  证明: by
  suffices forall f g, m.degree g - m.degree f = m.degree f ⊔ m.degree g - m.degree f by
    rw [sPolynomial]; rw [this]; rw [this]; rw [sup_comm]
  intro f g
  ext a
  obtain (h | h) := le_total (m.degree f a) (m.degree g a) <;> simp [h]

Depends on / 依赖: degree, le_total, m.degree, sPolynomial, sup_comm
-/
lemma sPolynomial_def (f g : MvPolynomial σ R) :
    m.sPolynomial f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  suffices forall f g, m.degree g - m.degree f = m.degree f ⊔ m.degree g - m.degree f by
    rw [sPolynomial]; rw [this]; rw [this]; rw [sup_comm]
  intro f g
  ext a
  obtain (h | h) := le_total (m.degree f a) (m.degree g a) <;> simp [h]

/--
lemma `degree_ne_zero_of_sub_leadingTerm_ne_zero` / 引理 `degree_ne_zero_of_sub_leadingTerm_ne_zero`

English:
lemma degree_ne_zero_of_sub_leadingTerm_ne_zero
  statement: {f : MvPolynomial σ R}
  proof: by
  contrapose h
  rw [m.degree_eq_zero_iff.mp h]; rw [leadingTerm_C]; rw [sub_eq_zero]

@[simp]

中文:
引理 degree_ne_zero_of_sub_leadingTerm_ne_zero
  结论: {f : 多元多项式 σ R}
  证明: by
  contrapose h
  rw [m.degree_eq_zero_iff.mp h]; rw [leadingTerm_C]; rw [sub_eq_zero]

@[simp]

Depends on / 依赖: contrapose, degree_eq_zero_iff, leadingTerm_C, m.degree_eq_zero_iff.mp, sub_eq_zero
-/
lemma degree_ne_zero_of_sub_leadingTerm_ne_zero {f : MvPolynomial σ R}
    (h : f - m.leadingTerm f != 0) : m.degree f != 0 := by
  contrapose h
  rw [m.degree_eq_zero_iff.mp h]; rw [leadingTerm_C]; rw [sub_eq_zero]

@[simp]
/--
theorem `degree_neg` / 定理 `degree_neg`

English:
theorem degree_neg
  given: {f : MvPolynomial σ R}
  proof: by
  unfold degree
  rw [support_neg]

@[simp]

中文:
定理 degree_neg
  条件: {f : 多元多项式 σ R}
  证明: by
  unfold degree
  rw [support_neg]

@[simp]

Depends on / 依赖: degree, support_neg
-/
theorem degree_neg {f : MvPolynomial σ R} :
    m.degree (-f) = m.degree f := by
  unfold degree
  rw [support_neg]

@[simp]
/--
theorem `leadingCoeff_neg` / 定理 `leadingCoeff_neg`

English:
theorem leadingCoeff_neg
  given: {f : MvPolynomial σ R}
  proof: by
  simp only [leadingCoeff, degree_neg, coeff_neg]

中文:
定理 leadingCoeff_neg
  条件: {f : 多元多项式 σ R}
  证明: by
  simp only [leadingCoeff, degree_neg, coeff_neg]

Depends on / 依赖: coeff_neg, degree_neg, leadingCoeff
-/
theorem leadingCoeff_neg {f : MvPolynomial σ R} :
    m.leadingCoeff (-f) = - m.leadingCoeff f := by
  simp only [leadingCoeff, degree_neg, coeff_neg]

/--
theorem `degree_sub_le` / 定理 `degree_sub_le`

English:
theorem degree_sub_le
  given: {f g : MvPolynomial σ R}
  proof: by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

中文:
定理 degree_sub_le
  条件: {f g : 多元多项式 σ R}
  证明: by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

Depends on / 依赖: degree_add_le, degree_neg, le_of_le_of_eq, m.degree_add_le, sub_eq_add_neg
-/
theorem degree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f - g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

/--
theorem `degree_sub_of_lt` / 定理 `degree_sub_of_lt`

English:
theorem degree_sub_of_lt
  given: {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
  proof: by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]

中文:
定理 degree_sub_of_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree g ≺[m] m.degree f)
  证明: by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]

Depends on / 依赖: degree_add_of_lt, degree_neg, sub_eq_add_neg
-/
theorem degree_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f - g) = m.degree f := by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]

/--
theorem `leadingCoeff_sub_of_lt` / 定理 `leadingCoeff_sub_of_lt`

English:
theorem leadingCoeff_sub_of_lt
  given: {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
  proof: by
  rw [sub_eq_add_neg]
  apply leadingCoeff_add_of_lt
  simp only [degree_neg, h]

中文:
定理 leadingCoeff_sub_of_lt
  条件: {f g : 多元多项式 σ R} (h : m.degree g ≺[m] m.degree f)
  证明: by
  rw [sub_eq_add_neg]
  apply leadingCoeff_add_of_lt
  simp only [degree_neg, h]

Depends on / 依赖: degree_neg, leadingCoeff_add_of_lt, sub_eq_add_neg
-/
theorem leadingCoeff_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f - g) = m.leadingCoeff f := by
  rw [sub_eq_add_neg]
  apply leadingCoeff_add_of_lt
  simp only [degree_neg, h]

/--
theorem `degree_sub_leadingTerm_le` / 定理 `degree_sub_leadingTerm_le`

English:
theorem degree_sub_leadingTerm_le
  given: (f : MvPolynomial σ R)
  proof: by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]

中文:
定理 degree_sub_leadingTerm_le
  条件: (f : 多元多项式 σ R)
  证明: by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]

Depends on / 依赖: degree_leadingTerm, degree_sub_le, le_trans
-/
theorem degree_sub_leadingTerm_le (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]

/--
theorem `degree_sub_leadingTerm_lt_degree` / 定理 `degree_sub_leadingTerm_lt_degree`

English:
theorem degree_sub_leadingTerm_lt_degree
  given: {f : MvPolynomial σ R} (h : m.degree f != 0)
  proof: by
  classical
  by_cases hl : f - m.leadingTerm f = 0
  · simpa [hl, toSyn_lt_iff_ne_zero]
  · apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f)
    by_contra! h'
    simp only [EmbeddingLike.apply_eq_iff_eq] at h'
    apply m.degree_mem_support at hl
    rw [h']; rw [mem_support_iff] at hl
    simp [leadingTerm, leadingCoeff] at hl

中文:
定理 degree_sub_leadingTerm_lt_degree
  条件: {f : 多元多项式 σ R} (h : m.degree f != 0)
  证明: by
  classical
  by_cases hl : f - m.leadingTerm f = 0
  · simpa [hl, toSyn_lt_iff_ne_zero]
  · apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f)
    by_contra! h'
    simp only [EmbeddingLike.apply_eq_iff_eq] at h'
    apply m.degree_mem_support at hl
    rw [h']; rw [mem_support_iff] at hl
    simp [leadingTerm, leadingCoeff] at hl

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, classical, degree_mem_support, degree_sub_leadingTerm_le, leadingCoeff, leadingTerm, lt_of_le_of_ne, m.degree_mem_support, m.degree_sub_leadingTerm_le, m.leadingTerm, mem_support_iff, toSyn_lt_iff_ne_zero
-/
theorem degree_sub_leadingTerm_lt_degree {f : MvPolynomial σ R} (h : m.degree f != 0) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f := by
  classical
  by_cases hl : f - m.leadingTerm f = 0
  · simpa [hl, toSyn_lt_iff_ne_zero]
  · apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f)
    by_contra! h'
    simp only [EmbeddingLike.apply_eq_iff_eq] at h'
    apply m.degree_mem_support at hl
    rw [h']; rw [mem_support_iff] at hl
    simp [leadingTerm, leadingCoeff] at hl

/--
theorem `degree_sub_leadingTerm_lt_iff` / 定理 `degree_sub_leadingTerm_lt_iff`

English:
theorem degree_sub_leadingTerm_lt_iff
  given: {f : MvPolynomial σ R}
  proof: by
  refine ⟨?_, degree_sub_leadingTerm_lt_degree⟩
  intro h h'
  simp only [h', map_zero] at h
  exact not_lt_bot h

中文:
定理 degree_sub_leadingTerm_lt_iff
  条件: {f : 多元多项式 σ R}
  证明: by
  refine ⟨?_, degree_sub_leadingTerm_lt_degree⟩
  intro h h'
  simp only [h', map_zero] at h
  exact not_lt_bot h

Depends on / 依赖: degree_sub_leadingTerm_lt_degree, map_zero, not_lt_bot
-/
theorem degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ↔ m.degree f != 0 := by
  refine ⟨?_, degree_sub_leadingTerm_lt_degree⟩
  intro h h'
  simp only [h', map_zero] at h
  exact not_lt_bot h

/--
lemma `sPolynomial_antisymm` / 引理 `sPolynomial_antisymm`

English:
lemma sPolynomial_antisymm
  given: (f g : MvPolynomial σ R)
  proof: (neg_sub (_ * g) (_ * f)).symm

@[simp]

中文:
引理 sPolynomial_antisymm
  条件: (f g : 多元多项式 σ R)
  证明: (neg_sub (_ * g) (_ * f)).symm

@[simp]

Depends on / 依赖: neg_sub
-/
lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
    m.sPolynomial f g = - m.sPolynomial g f :=
  (neg_sub (_ * g) (_ * f)).symm

@[simp]
/--
lemma `sPolynomial_left_zero` / 引理 `sPolynomial_left_zero`

English:
lemma sPolynomial_left_zero
  given: (g : MvPolynomial σ R)
  proof: by
  simp [sPolynomial]

@[simp]

中文:
引理 sPolynomial_left_zero
  条件: (g : 多元多项式 σ R)
  证明: by
  simp [sPolynomial]

@[simp]

Depends on / 依赖: SeparableSpace, SeparableWeaklyLocallyCompactGroup, SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace, sPolynomial, sigmaCompactSpace
-/
lemma sPolynomial_left_zero (g : MvPolynomial σ R) :
    m.sPolynomial 0 g = 0 := by
  simp [sPolynomial]

@[simp]
/--
lemma `sPolynomial_right_zero` / 引理 `sPolynomial_right_zero`

English:
lemma sPolynomial_right_zero
  given: (f : MvPolynomial σ R)
  proof: by
  rw [sPolynomial_antisymm]; rw [sPolynomial_left_zero]; rw [neg_zero]

@[simp]

中文:
引理 sPolynomial_right_zero
  条件: (f : 多元多项式 σ R)
  证明: by
  rw [sPolynomial_antisymm]; rw [sPolynomial_left_zero]; rw [neg_zero]

@[simp]

Depends on / 依赖: neg_zero, sPolynomial_antisymm, sPolynomial_left_zero
-/
lemma sPolynomial_right_zero (f : MvPolynomial σ R) :
    m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm]; rw [sPolynomial_left_zero]; rw [neg_zero]

@[simp]
/--
lemma `sPolynomial_self` / 引理 `sPolynomial_self`

English:
lemma sPolynomial_self
  given: (f : MvPolynomial σ R)
  statement: m.sPolynomial f f = 0
  proof: sub_self _

中文:
引理 sPolynomial_self
  条件: (f : 多元多项式 σ R)
  结论: m.sPolynomial f f = 0
  证明: sub_self _

Depends on / 依赖: sub_self
-/
lemma sPolynomial_self (f : MvPolynomial σ R) : m.sPolynomial f f = 0 := sub_self _

/--
lemma `degree_sPolynomial_le` / 引理 `degree_sPolynomial_le`

English:
lemma degree_sPolynomial_le
  given: (f g : MvPolynomial σ R)
  proof: by
  classical
  wlog! +distrib h0 : f != 0 ∧ g != 0
  · (obtain rfl | rfl := h0) <;> simp
  simp only [sPolynomial_def]
  apply degree_sub_le.trans
  apply (sup_le_sup degree_mul_le degree_mul_le).trans
  simp [degree_monomial, h0.1, h0.2, tsub_add_cancel_of_le, le_sup_left, le_sup_right]

中文:
引理 degree_sPolynomial_le
  条件: (f g : 多元多项式 σ R)
  证明: by
  classical
  wlog! +distrib h0 : f != 0 ∧ g != 0
  · (obtain rfl | rfl := h0) <;> simp
  simp only [sPolynomial_def]
  apply degree_sub_le.trans
  apply (sup_le_sup degree_mul_le degree_mul_le).trans
  simp [degree_monomial, h0.1, h0.2, tsub_add_cancel_of_le, le_sup_left, le_sup_right]

Depends on / 依赖: classical, degree_monomial, degree_mul_le, degree_sub_le, degree_sub_le.trans, distrib, le_sup_left, le_sup_right, sPolynomial_def, sup_le_sup, tsub_add_cancel_of_le
-/
lemma degree_sPolynomial_le (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial f g) ≼[m] m.degree f ⊔ m.degree g) := by
  classical
  wlog! +distrib h0 : f != 0 ∧ g != 0
  · (obtain rfl | rfl := h0) <;> simp
  simp only [sPolynomial_def]
  apply degree_sub_le.trans
  apply (sup_le_sup degree_mul_le degree_mul_le).trans
  simp [degree_monomial, h0.1, h0.2, tsub_add_cancel_of_le, le_sup_left, le_sup_right]

/--
lemma `coeff_sPolynomial_sup_eq_zero` / 引理 `coeff_sPolynomial_sup_eq_zero`

English:
lemma coeff_sPolynomial_sup_eq_zero
  given: (f g : MvPolynomial σ R)
  proof: by
  rw [sPolynomial_def]; rw [coeff_sub]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_left, coeff_monomial_mul]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_right, coeff_monomial_mul]
  unfold leadingCoeff
  ring

中文:
引理 coeff_sPolynomial_sup_eq_zero
  条件: (f g : 多元多项式 σ R)
  证明: by
  rw [sPolynomial_def]; rw [coeff_sub]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_left, coeff_monomial_mul]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_right, coeff_monomial_mul]
  unfold leadingCoeff
  ring

Depends on / 依赖: coeff_monomial_mul, coeff_sub, continuous_inv, le_sup_left, le_sup_right, leadingCoeff, nth_rewrite, sPolynomial_def, tsub_add_cancel_of_le
-/
lemma coeff_sPolynomial_sup_eq_zero (f g : MvPolynomial σ R) :
    (m.sPolynomial f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
  rw [sPolynomial_def]; rw [coeff_sub]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_left, coeff_monomial_mul]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_right, coeff_monomial_mul]
  unfold leadingCoeff
  ring

/--
lemma `degree_sPolynomial` / 引理 `degree_sPolynomial`

English:
lemma degree_sPolynomial
  given: (f g : MvPolynomial σ R)
  proof: by
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    suffices C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 by simp_all [sPolynomial_def]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · rw [or_iff_not_imp_right]
    intro hs
    apply (m.degree_sPolynomial_le f g).lt_of_ne
    apply m.toSyn.injective.ne
    contrapose hs
    rw [← m.coeff_degree_eq_zero_iff]; rw [hs]; rw [m.coeff_sPolynomial_sup_eq_zero]

中文:
引理 degree_sPolynomial
  条件: (f g : 多元多项式 σ R)
  证明: by
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    suffices C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 by simp_all [sPolynomial_def]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · rw [or_iff_not_imp_right]
    intro hs
    apply (m.degree_sPolynomial_le f g).lt_of_ne
    apply m.toSyn.injective.ne
    contrapose hs
    rw [← m.coeff_degree_eq_zero_iff]; rw [hs]; rw [m.coeff_sPolynomial_sup_eq_zero]

Depends on / 依赖: coeff_degree_eq_zero_iff, coeff_sPolynomial_sup_eq_zero, continuous_neg, contrapose, degree, degree_eq_zero_iff, degree_eq_zero_iff.mp, degree_sPolynomial_le, injective, leadingCoeff, lt_of_ne, m.coeff_degree_eq_zero_iff, m.coeff_sPolynomial_sup_eq_zero, m.degree, m.degree_sPolynomial_le, m.leadingCoeff, m.toSyn.injective.ne, nth_rewrite, or_iff_not_imp_right, sPolynomial_def
-/
lemma degree_sPolynomial (f g : MvPolynomial σ R) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial f g = 0 := by
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    suffices C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 by simp_all [sPolynomial_def]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · rw [or_iff_not_imp_right]
    intro hs
    apply (m.degree_sPolynomial_le f g).lt_of_ne
    apply m.toSyn.injective.ne
    contrapose hs
    rw [← m.coeff_degree_eq_zero_iff]; rw [hs]; rw [m.coeff_sPolynomial_sup_eq_zero]

/--
lemma `degree_sPolynomial_lt_sup_degree` / 引理 `degree_sPolynomial_lt_sup_degree`

English:
lemma degree_sPolynomial_lt_sup_degree
  given: {f g : MvPolynomial σ R} (h : m.sPolynomial f g != 0)
  proof: (or_iff_left h).mp m.degree_sPolynomial f g

中文:
引理 degree_sPolynomial_lt_sup_degree
  条件: {f g : 多元多项式 σ R} (h : m.sPolynomial f g != 0)
  证明: (or_iff_left h).mp m.degree_sPolynomial f g

Depends on / 依赖: degree_sPolynomial, m.degree_sPolynomial, or_iff_left
-/
lemma degree_sPolynomial_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomial f g != 0) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g :=
(or_iff_left h).mp m.degree_sPolynomial f g

/--
lemma `sPolynomial_lt_of_degree_ne_zero_of_degree_eq` / 引理 `sPolynomial_lt_of_degree_ne_zero_of_degree_eq`

English:
lemma sPolynomial_lt_of_degree_ne_zero_of_degree_eq
  statement: {f g : MvPolynomial σ R}
  proof: by
  simpa [h] using m.degree_sPolynomial_lt_sup_degree hs

中文:
引理 sPolynomial_lt_of_degree_ne_zero_of_degree_eq
  结论: {f g : 多元多项式 σ R}
  证明: by
  simpa [h] using m.degree_sPolynomial_lt_sup_degree hs

Depends on / 依赖: degree_sPolynomial_lt_sup_degree, m.degree_sPolynomial_lt_sup_degree
-/
lemma sPolynomial_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R}
    (h : m.degree f = m.degree g) (hs : m.sPolynomial f g != 0) :
    m.degree (m.sPolynomial f g) ≺[m] m.degree f := by
  simpa [h] using m.degree_sPolynomial_lt_sup_degree hs

/--
lemma `sPolynomial_monomial_mul` / 引理 `sPolynomial_monomial_mul`

English:
lemma sPolynomial_monomial_mul
  statement: [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat)
  proof: by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2, hp1, hp2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul, m.leadingCoeff_monomial,
    degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_eq_add_tsub le_sup_left]; rw [tsub_add_eq_add_tsub le_sup_right]; rw [add_comm d₁]; rw [add_comm d₂]; rw [add_tsub_add_eq_tsub_right]; rw [add_tsub_add_eq_tsub_right]

中文:
引理 sPolynomial_monomial_mul
  结论: [无零因子 R] (p₁ p₂ : 多元多项式 σ R) (d₁ d₂ : σ ->₀ 自然数)
  证明: by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2, hp1, hp2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul, m.leadingCoeff_monomial,
    degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_eq_add_tsub le_sup_left]; rw [tsub_add_eq_add_tsub le_sup_right]; rw [add_comm d₁]; rw [add_comm d₂]; rw [add_tsub_add_eq_tsub_right]; rw [add_tsub_add_eq_tsub_right]

Depends on / 依赖: classical, degree_monomial, degree_mul, distrib, leadingCoeff_monomial, leadingCoeff_mul, m.degree_mul, m.leadingCoeff_monomial, m.leadingCoeff_mul, monomial_eq_zero, monomial_mul, mul_assoc, mul_right_comm, mul_sub, not.mpr, reduceIte, sPolynomial_def, simp_rw
-/
lemma sPolynomial_monomial_mul [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2, hp1, hp2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul, m.leadingCoeff_monomial,
    degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp)]; rw [tsub_add_eq_add_tsub le_sup_left]; rw [tsub_add_eq_add_tsub le_sup_right]; rw [add_comm d₁]; rw [add_comm d₂]; rw [add_tsub_add_eq_tsub_right]; rw [add_tsub_add_eq_tsub_right]

/--
lemma `sPolynomial_monomial_mul'` / 引理 `sPolynomial_monomial_mul'`

English:
lemma sPolynomial_monomial_mul'
  statement: [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat)
  proof: by
  classical
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, degree_mul, sPolynomial_monomial_mul, degree_monomial]

中文:
引理 sPolynomial_monomial_mul'
  结论: [无零因子 R] (p₁ p₂ : 多元多项式 σ R) (d₁ d₂ : σ ->₀ 自然数)
  证明: by
  classical
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, degree_mul, sPolynomial_monomial_mul, degree_monomial]

Depends on / 依赖: classical, degree_monomial, degree_mul, distrib, sPolynomial_monomial_mul
-/
lemma sPolynomial_monomial_mul' [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat)
    (c₁ c₂ : R) :
    m.sPolynomial (monomial d₁ c₁ * p₁) (monomial d₂ c₂ * p₂) =
      monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ * p₂) -
          m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  wlog! +distrib H : c₁ != 0 ∧ c₂ != 0 ∧ p₁ != 0 ∧ p₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, degree_mul, sPolynomial_monomial_mul, degree_monomial]

/--
lemma `sPolynomial_leadingTerm_mul` / 引理 `sPolynomial_leadingTerm_mul`

English:
lemma sPolynomial_leadingTerm_mul
  given: [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R)
  proof: by
  simp [sPolynomial_monomial_mul, leadingTerm]

中文:
引理 sPolynomial_leadingTerm_mul
  条件: [无零因子 R] (p₁ p₂ q₁ q₂ : 多元多项式 σ R)
  证明: by
  simp [sPolynomial_monomial_mul, leadingTerm]

Depends on / 依赖: leadingTerm, sPolynomial_monomial_mul
-/
lemma sPolynomial_leadingTerm_mul [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree p₁ + m.degree q₁) ⊔ (m.degree p₂ + m.degree q₂) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial q₁ q₂ := by
  simp [sPolynomial_monomial_mul, leadingTerm]

/--
lemma `sPolynomial_leadingTerm_mul'` / 引理 `sPolynomial_leadingTerm_mul'`

English:
lemma sPolynomial_leadingTerm_mul'
  given: [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R)
  proof: by
  wlog! +distrib H : p₁ != 0 ∧ p₂ != 0 ∧ q₁ != 0 ∧ q₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, leadingTerm, sPolynomial_monomial_mul, degree_mul]

中文:
引理 sPolynomial_leadingTerm_mul'
  条件: [无零因子 R] (p₁ p₂ q₁ q₂ : 多元多项式 σ R)
  证明: by
  wlog! +distrib H : p₁ != 0 ∧ p₂ != 0 ∧ q₁ != 0 ∧ q₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, leadingTerm, sPolynomial_monomial_mul, degree_mul]

Depends on / 依赖: degree_mul, distrib, leadingTerm, sPolynomial_monomial_mul
-/
lemma sPolynomial_leadingTerm_mul' [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree (p₁ * q₁)) ⊔ (m.degree (p₂ * q₂)) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial q₁ q₂ := by
  wlog! +distrib H : p₁ != 0 ∧ p₂ != 0 ∧ q₁ != 0 ∧ q₂ != 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, leadingTerm, sPolynomial_monomial_mul, degree_mul]

/--
lemma `sPolynomial_decomposition` / 引理 `sPolynomial_decomposition`

English:
lemma sPolynomial_decomposition
  statement: {d : m.syn} {ι : Type*}
  proof: by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false]
        at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ => if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' in B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i in B, m.leadingCoeff (g i))) = m.leadingCoeff (g b) by
        rw [add_comm]; rw [Finset.sum_sub_distrib]; rw [sub_eq_add_neg]; rw [← Finset.sum_smul]; rw [← Finset.sum_mul]; rw [← neg_smul]; rw [← neg_mul]; rw [this]; rw [isunit_gb.mul_val_inv]; rw [one_smul]
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i in B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      obtain (⟨h, -⟩ | h) := hd b' hb' <;>
        simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul, mul_comm (m.leadingCoeff (g b'))]

@[simp]

中文:
引理 sPolynomial_decomposition
  结论: {d : m.syn} {ι : 类型}
  证明: by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false]
        at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ => if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' in B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i in B, m.leadingCoeff (g i))) = m.leadingCoeff (g b) by
        rw [add_comm]; rw [Finset.sum_sub_distrib]; rw [sub_eq_add_neg]; rw [← Finset.sum_smul]; rw [← Finset.sum_mul]; rw [← neg_smul]; rw [← neg_mul]; rw [this]; rw [isunit_gb.mul_val_inv]; rw [one_smul]
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i in B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      obtain (⟨h, -⟩ | h) := hd b' hb' <;>
        simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul, mul_comm (m.leadingCoeff (g b'))]

@[simp]

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_insert, Finset.sum_ite_eq, add_zero, classical, forall_eq_or_imp, induction_on, insert, isunit_gb, isunit_gb.unit, ite_smul, mem_insert, or_false, reduceIte, sum_insert, sum_ite_eq, zero_smul
-/
lemma sPolynomial_decomposition {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι -> MvPolynomial σ R}
    (hd : forall b in B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b in B, g b) < d) :
    exists (c : ι -> ι -> R),
      ∑ b in B, g b = ∑ b₁ in B, ∑ b₂ in B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false]
        at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ => if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' in B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i in B, m.leadingCoeff (g i))) = m.leadingCoeff (g b) by
        rw [add_comm]; rw [Finset.sum_sub_distrib]; rw [sub_eq_add_neg]; rw [← Finset.sum_smul]; rw [← Finset.sum_mul]; rw [← neg_smul]; rw [← neg_mul]; rw [this]; rw [isunit_gb.mul_val_inv]; rw [one_smul]
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i in B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      obtain (⟨h, -⟩ | h) := hd b' hb' <;>
        simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul, mul_comm (m.leadingCoeff (g b'))]

@[simp]
/--
lemma `withBotDegree_neg` / 引理 `withBotDegree_neg`

English:
lemma withBotDegree_neg
  given: (f : MvPolynomial σ R)
  proof: by
  classical
  simp [m.withBotDegree_eq]

中文:
引理 withBotDegree_neg
  条件: (f : 多元多项式 σ R)
  证明: by
  classical
  simp [m.withBotDegree_eq]

Depends on / 依赖: classical, m.withBotDegree_eq, withBotDegree_eq
-/
lemma withBotDegree_neg (f : MvPolynomial σ R) :
    m.withBotDegree (-f) = m.withBotDegree f := by
  classical
  simp [m.withBotDegree_eq]

end Ring

section Field

variable {R : Type*} [Field R]

/--
theorem `isUnit_leadingCoeff` / 定理 `isUnit_leadingCoeff`

English:
theorem isUnit_leadingCoeff
  given: {f : MvPolynomial σ R}
  proof: by
  simp only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]

中文:
定理 isUnit_leadingCoeff
  条件: {f : 多元多项式 σ R}
  证明: by
  simp only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]

Depends on / 依赖: isUnit_iff_ne_zero, leadingCoeff_eq_zero_iff, ne_eq
-/
theorem isUnit_leadingCoeff {f : MvPolynomial σ R} :
    IsUnit (m.leadingCoeff f) ↔ f != 0 := by
  simp only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]

/--
lemma `sPolynomial_decomposition'` / 引理 `sPolynomial_decomposition'`

English:
lemma sPolynomial_decomposition'
  statement: {d : m.syn} {ι : Type*}
  proof: by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

中文:
引理 sPolynomial_decomposition'
  结论: {d : m.syn} {ι : 类型}
  证明: by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

Depends on / 依赖: and_or_right, m.sPolynomial_decomposition, sPolynomial_decomposition
-/
lemma sPolynomial_decomposition' {d : m.syn} {ι : Type*}
    {B : Finset ι} (g : ι -> MvPolynomial σ R)
    (hd : forall b in B, (m.toSyn <| m.degree <| g b) = d ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b in B, g b) < d) :
    exists (c : ι -> ι -> R),
      ∑ b in B, g b = ∑ b₁ in B, ∑ b₂ in B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

end Field

section Binomial

variable {R : Type*} [CommRing R]

open Finsupp MvPolynomial

/--
lemma `degree_X_add_C` / 引理 `degree_X_add_C`

English:
lemma degree_X_add_C
  statement: [Nontrivial R]
  proof: by
  rw [degree_add_of_lt]; rw [degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero]; rw [bot_lt_iff_ne_bot]; rw [bot_eq_zero]; rw [← map_zero m.toSyn]
  simp

中文:
引理 degree_X_add_C
  结论: [非平凡 R]
  证明: by
  rw [degree_add_of_lt]; rw [degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero]; rw [bot_lt_iff_ne_bot]; rw [bot_eq_zero]; rw [← map_zero m.toSyn]
  simp

Depends on / 依赖: bot_eq_zero, bot_lt_iff_ne_bot, degree_C, degree_X, degree_add_of_lt, m.toSyn, map_zero
-/
lemma degree_X_add_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i + C r) = single i 1 := by
  rw [degree_add_of_lt]; rw [degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero]; rw [bot_lt_iff_ne_bot]; rw [bot_eq_zero]; rw [← map_zero m.toSyn]
  simp

/--
lemma `degree_X_sub_C` / 引理 `degree_X_sub_C`

English:
lemma degree_X_sub_C
  statement: [Nontrivial R]
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg]; rw [degree_X_add_C]

中文:
引理 degree_X_sub_C
  结论: [非平凡 R]
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg]; rw [degree_X_add_C]

Depends on / 依赖: degree_X_add_C, map_neg, sub_eq_add_neg
-/
lemma degree_X_sub_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i - C r) = single i 1 := by
  rw [sub_eq_add_neg]; rw [← map_neg]; rw [degree_X_add_C]

/--
lemma `monic_X_add_C` / 引理 `monic_X_add_C`

English:
lemma monic_X_add_C
  given: {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R)
  proof: by
  nontriviality R
  apply monic_X.add_of_lt
  simp [degree_C, degree_X, ← not_le, ← eq_zero_iff]

中文:
引理 monic_X_add_C
  条件: {ι : 类型} (m : 单项式序 ι) (i : ι) (r : R)
  证明: by
  nontriviality R
  apply monic_X.add_of_lt
  simp [degree_C, degree_X, ← not_le, ← eq_zero_iff]

Depends on / 依赖: add_of_lt, degree_C, degree_X, eq_zero_iff, monic_X, monic_X.add_of_lt, nontriviality, not_le
-/
lemma monic_X_add_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i + C r) := by
  nontriviality R
  apply monic_X.add_of_lt
  simp [degree_C, degree_X, ← not_le, ← eq_zero_iff]

/--
lemma `monic_X_sub_C` / 引理 `monic_X_sub_C`

English:
lemma monic_X_sub_C
  given: {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R)
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg]
  apply monic_X_add_C

中文:
引理 monic_X_sub_C
  条件: {ι : 类型} (m : 单项式序 ι) (i : ι) (r : R)
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg]
  apply monic_X_add_C

Depends on / 依赖: map_neg, monic_X_add_C, sub_eq_add_neg
-/
lemma monic_X_sub_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i - C r) := by
  rw [sub_eq_add_neg]; rw [← map_neg]
  apply monic_X_add_C

end Binomial

end MonomialOrder
