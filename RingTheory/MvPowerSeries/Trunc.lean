/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPowerSeries.Order

/-!

# Formal (multivariate) power series - Truncation

* `MvPowerSeries.truncFinset s p` restricts the support of a multivariate power series `p`
  to a finite set of monomials and obtains a multivariate polynomial.

* `MvPowerSeries.trunc n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m < n`, and `0` otherwise.

  Note that here, `m` and `n` have types `σ →₀ ℕ`,
  so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

* `MvPowerSeries.trunc_one` : truncation of the unit power series

* `MvPowerSeries.trunc_C` : truncation of a constant

* `MvPowerSeries.trunc_C_mul` : truncation of constant multiple.

* `MvPowerSeries.trunc' n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m ≤ n`, and `0` otherwise.

  Here, `m` and `n`  have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


* `MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'` : compares the coefficients
  of a product with those of the product of truncations.

* `MvPowerSeries.trunc'_one` : truncation of the unit power series.

* `MvPowerSeries.trunc'_C` : truncation of a constant.

* `MvPowerSeries.trunc'_C_mul` : truncation of a constant multiple.

* `MvPowerSeries.trunc'_map` : image of a truncation under a change of rings

* `MvPowerSeries.truncTotal` : the truncation of a multivariate formal power series at
  a total degree `n` when the index `σ` is finite

-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

open Finsupp Finset

variable {σ R S : Type*}

section TruncFinset

variable [CommSemiring R] {s : Finset (σ →₀ ℕ)}

/-- Restrict the support of a multivariate power series to a finite set of monomials and
obtain a multivariate polynomial. -/
/-
**MvPowerSeries.truncFinset** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset (R : Type*) [CommSemiring R] (s : Finset (σ ->₀ Nat)) : MvPowe
rSeries σ R ->ₗ[R] MvPolynomial σ R where toFun p
参数：R : Type*；s : Finset (σ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the support of a multivariate power series to a finite set of monomials
 and
obtain a multivariate polynomial.
-/
def truncFinset (R : Type*) [CommSemiring R] (s : Finset (σ →₀ ℕ)) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R where
  toFun p := ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    ext
    simp [MvPolynomial.coeff, single, MvPolynomial.monomial]
/-
**MvPowerSeries.truncFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset_apply (p : MvPowerSeries σ R) : truncFinset R s p = ∑ x in s, 
MvPolynomial.monomial x (p.coeff x)
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem truncFinset_apply (p : MvPowerSeries σ R) :
    truncFinset R s p = ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x) := by rfl

@[grind =]
/-
**MvPowerSeries.coeff_truncFinset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：coeff_truncFinset_of_mem {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x in
 s) : (truncFinset R s p).coeff x = p.coeff x
参数：p : MvPowerSeries σ R；h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncFinset_apply`：truncFinset_apply (p : MvPowerSeries σ 
R) : truncFinset R s p = ∑ x in s, MvPolynomial.monomial x (p.coeff x)
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_truncFinset_of_mem {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∈ s) :
    (truncFinset R s p).coeff x = p.coeff x := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

@[grind =]
/-
**MvPowerSeries.coeff_truncFinset_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：coeff_truncFinset_eq_zero {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉
 s) : (truncFinset R s p).coeff x = 0
参数：p : MvPowerSeries σ R；h : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncFinset_apply`：truncFinset_apply (p : MvPowerSeries σ 
R) : truncFinset R s p = ∑ x in s, MvPolynomial.monomial x (p.coeff x)
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_truncFinset_eq_zero {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∉ s) :
    (truncFinset R s p).coeff x = 0 := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]
/-
**MvPowerSeries.coeff_truncFinset** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncFinset [DecidableEq σ] {x : σ ->₀ Nat} (p : MvPowerSeries σ R) 
: (truncFinset R s p).coeff x = if x in s then p.coeff x else 0
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncFinset_apply`：truncFinset_apply (p : MvPowerSeries σ 
R) : truncFinset R s p = ∑ x in s, MvPolynomial.monomial x (p.coeff x)
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_truncFinset [DecidableEq σ] {x : σ →₀ ℕ} (p : MvPowerSeries σ R) :
    (truncFinset R s p).coeff x = if x ∈ s then p.coeff x else 0 := by
  simp [truncFinset_apply, MvPolynomial.coeff_sum]
/-
**MvPowerSeries.truncFinset_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset_monomial {x : σ ->₀ Nat} (r : R) (h : x in s) : truncFinset R 
s (monomial x r) = MvPolynomial.monomial x r
参数：r : R；h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
-/
theorem truncFinset_monomial {x : σ →₀ ℕ} (r : R) (h : x ∈ s) :
    truncFinset R s (monomial x r) = MvPolynomial.monomial x r := by
  classical
  ext
  grind [coeff_monomial, MvPolynomial.coeff_monomial]
/-
**MvPowerSeries.truncFinset_monomial_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries`。
形式化陈述：truncFinset_monomial_eq_zero {x : σ ->₀ Nat} (r : R) (h : x ∉ s) : truncFi
nset R s (monomial x r) = 0
参数：r : R；h : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem truncFinset_monomial_eq_zero {x : σ →₀ ℕ} (r : R) (h : x ∉ s) :
    truncFinset R s (monomial x r) = 0 := by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  grind
/-
**MvPowerSeries.truncFinset_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset_C (h : 0 in s) (r : R) : truncFinset R s (C r) = MvPolynomial.
C r
参数：h : 0 in s；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_monomial`：truncFinset_monomial {x : σ ->₀ Nat}
 (r : R) (h : x in s) : truncFinset R s (monomial x r) = MvPolynomial.monomial x
 r
-/
theorem truncFinset_C (h : 0 ∈ s) (r : R) : truncFinset R s (C r) = MvPolynomial.C r :=
  truncFinset_monomial r h
/-
**MvPowerSeries.truncFinset_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset_one (h : 0 in s) : truncFinset R s (1 : MvPowerSeries σ R) = 1
参数：h : 0 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_C`：truncFinset_C (h : 0 in s) (r : R) : truncF
inset R s (C r) = MvPolynomial.C r
-/
theorem truncFinset_one (h : 0 ∈ s) : truncFinset R s (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_C h 1
/-
**MvPowerSeries.truncFinset_truncFinset** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：truncFinset_truncFinset {t : Finset (σ ->₀ Nat)} (h : s subseteq t) (p : M
vPowerSeries σ R) : truncFinset R s (truncFinset R t p) = truncFinset R s p
参数：σ ->₀ Nat；h : s subseteq t；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
-/
theorem truncFinset_truncFinset {t : Finset (σ →₀ ℕ)} (h : s ⊆ t) (p : MvPowerSeries σ R) :
    truncFinset R s (truncFinset R t p) = truncFinset R s p := by
  ext x
  by_cases x ∈ s <;> grind [MvPolynomial.coeff_coe]
/-
**MvPowerSeries.truncFinset_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncFinset_map [CommSemiring S] (f : R ->+* S) (p : MvPowerSeries σ R) : 
truncFinset S s (map f p) = MvPolynomial.map f (truncFinset R s p)
参数：f : R ->+* S；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
-/
theorem truncFinset_map [CommSemiring S] (f : R →+* S) (p : MvPowerSeries σ R) :
    truncFinset S s (map f p) = MvPolynomial.map f (truncFinset R s p) := by
  ext x
  by_cases x ∈ s <;> grind [coeff_map, MvPolynomial.coeff_map]

/-- A coefficient of a product of finset-truncated power series equals the coefficient of the
untruncated product, with the two truncation finsets `s` and `t` allowed to differ. -/
/-
**MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul** 是 Mathlib 中的一个定
理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (
σ ->₀ Nat))) {x : σ ->₀ Nat} (f g : MvPowerSeries σ R) (hx : x in s) : (truncFin
set R s f * truncFinset R s g).coeff x = coeff x (f * g)
参数：hs : IsLowerSet (s : Set (σ ->₀ Nat))；f g : MvPowerSeries σ R；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂`：coeff_tru
ncFinset_mul_truncFinset_eq_coeff_mul₂ {t : Finset (σ ->₀ Nat)} (hs : IsLowerSet
 (s : Set (σ ->₀ Nat))) (ht : IsLowerSet (t : Set (…

--- 原说明 ---
A coefficient of a product of finset-truncated power series equals the coefficie
nt of the
untruncated product, with the two truncation finsets `s` and `t` allowed to diff
er.
-/
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ {t : Finset (σ →₀ ℕ)}
    (hs : IsLowerSet (s : Set (σ →₀ ℕ))) (ht : IsLowerSet (t : Set (σ →₀ ℕ)))
    {x : σ →₀ ℕ} (f g : MvPowerSeries σ R) (hxs : x ∈ s) (hxt : x ∈ t) :
      (truncFinset R s f * truncFinset R t g).coeff x = coeff x (f * g) := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset_of_mem _ (hs (show i ≤ x by simp [← hij]) hxs),
    coeff_truncFinset_of_mem _ (ht (show j ≤ x by simp [← hij]) hxt)]
/-
**MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul** 是 Mathlib 中的一个定
理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (
σ ->₀ Nat))) {x : σ ->₀ Nat} (f g : MvPowerSeries σ R) (hx : x in s) : (truncFin
set R s f * truncFinset R s g).coeff x = coeff x (f * g)
参数：hs : IsLowerSet (s : Set (σ ->₀ Nat))；f g : MvPowerSeries σ R；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂`：coeff_tru
ncFinset_mul_truncFinset_eq_coeff_mul₂ {t : Finset (σ ->₀ Nat)} (hs : IsLowerSet
 (s : Set (σ ->₀ Nat))) (ht : IsLowerSet (t : Set (…
-/
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (σ →₀ ℕ)))
    {x : σ →₀ ℕ} (f g : MvPowerSeries σ R) (hx : x ∈ s) :
      (truncFinset R s f * truncFinset R s g).coeff x = coeff x (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ hs hs f g hx hx
/-
**MvPowerSeries.truncFinset_truncFinset_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：truncFinset_truncFinset_pow (hs : IsLowerSet (s : Set (σ ->₀ Nat))) {k : N
at} (hk : 1 <= k) (p : MvPowerSeries σ R) : truncFinset R s ((truncFinset R s p)
 ^ k) = truncFinset R s (p ^ k)
参数：hs : IsLowerSet (s : Set (σ ->₀ Nat))；hk : 1 <= k；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MvPowerSeries.truncFinset_truncFinset`：truncFinset_truncFinset {t : Fins
et (σ ->₀ Nat)} (h : s subseteq t) (p : MvPowerSeries σ R) : truncFinset R s (tr
uncFinset R t p) = truncFin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `MvPowerSeries.coeff_truncFinset_of_mem`：coeff_truncFinset_of_mem {x : σ 
->₀ Nat} (p : MvPowerSeries σ R) (h : x in s) : (truncFinset R s p).coeff x = p.
coeff x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul`：coeff_trun
cFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (σ ->₀ Nat))) {x 
: σ ->₀ Nat} (f g : MvPowerSeries σ R) (hx : x in …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MvPowerSeries.coeff_truncFinset_eq_zero`：coeff_truncFinset_eq_zero {x : 
σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉ s) : (truncFinset R s p).coeff x = 0
-/
theorem truncFinset_truncFinset_pow (hs : IsLowerSet (s : Set (σ →₀ ℕ))) {k : ℕ} (hk : 1 ≤ k)
    (p : MvPowerSeries σ R) : truncFinset R s ((truncFinset R s p) ^ k) =
      truncFinset R s (p ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x ∈ s
    · rw [coeff_truncFinset_of_mem _ hx, coeff_truncFinset_of_mem _ hx, pow_succ,
        ← coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx, ih, truncFinset_truncFinset
        (by rfl), pow_succ, coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx]
    simp [coeff_truncFinset_eq_zero _ hx]
/-
**MvPowerSeries.support_truncFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSer
ies`。
形式化陈述：support_truncFinset_subset (p : MvPowerSeries σ R) : (truncFinset R s p).s
upport subseteq s
参数：p : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_truncFinset_eq_zero`：coeff_truncFinset_eq_zero {x : 
σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉ s) : (truncFinset R s p).coeff x = 0
-/
theorem support_truncFinset_subset (p : MvPowerSeries σ R) : (truncFinset R s p).support ⊆ s := by
  intro; contrapose
  simpa using coeff_truncFinset_eq_zero p
/-
**MvPowerSeries.totalDegree_truncFinset** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries
`。
形式化陈述：totalDegree_truncFinset (p : MvPowerSeries σ R) : (truncFinset R s p).tota
lDegree <= s.sup degree
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `MvPowerSeries.support_truncFinset_subset`：support_truncFinset_subset (p 
: MvPowerSeries σ R) : (truncFinset R s p).support subseteq s
-/
lemma totalDegree_truncFinset (p : MvPowerSeries σ R) :
    (truncFinset R s p).totalDegree ≤ s.sup degree := by
  simpa [MvPolynomial.totalDegree] using! sup_mono (support_truncFinset_subset p)
/-
**MvPowerSeries.truncFinset_coe_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：truncFinset_coe_eq_self_iff (p : MvPolynomial σ R) : truncFinset R s p = p
 ↔ p.support subseteq s
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.support_truncFinset_subset`：support_truncFinset_subset (p 
: MvPowerSeries σ R) : (truncFinset R s p).support subseteq s
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
-/
lemma truncFinset_coe_eq_self_iff (p : MvPolynomial σ R) :
    truncFinset R s p = p ↔ p.support ⊆ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ MvPolynomial.ext _ _ fun x ↦ ?_⟩
  · rw [← h]
    exact support_truncFinset_subset ..
  by_cases x ∈ s <;> grind [MvPolynomial.coeff_coe]

end TruncFinset

section TruncLT

variable [DecidableEq σ] [CommSemiring R]

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and `a i < n i` for some `i`. -/
/-
**MvPowerSeries.trunc** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc (R : Type*) [CommSemiring R] (n : σ ->₀ Nat) : MvPowerSeries σ R ->ₗ
[R] MvPolynomial σ R
参数：R : Type*；n : σ ->₀ Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
The `n`th truncation of a multivariate formal power series to a multivariate pol
ynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function f
rom `σ`
to the naturals, then `trunc R n f` is the multivariable polynomial obtained fro
m `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and `a i < n i` for some `i`.
-/
def trunc (R : Type*) [CommSemiring R] (n : σ →₀ ℕ) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Iio n)
/-
**MvPowerSeries.coeff_trunc** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_trunc (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R) : (trunc R n φ).coef
f m = if m < n then coeff m φ else 0
参数：m n : σ ->₀ Nat；φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `MvPowerSeries.coeff_truncFinset`：coeff_truncFinset [DecidableEq σ] {x : 
σ ->₀ Nat} (p : MvPowerSeries σ R) : (truncFinset R s p).coeff x = if x in s the
n p.coeff x else 0
-/
theorem coeff_trunc (m n : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff m φ else 0 := by
  simpa using! coeff_truncFinset (s := Iio n) (x := m) φ

@[simp]
/-
**MvPowerSeries.trunc_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc_one (n : σ ->₀ Nat) (hnn : n != 0) : trunc R n 1 = 1
参数：n : σ ->₀ Nat；hnn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_one`：truncFinset_one (h : 0 in s) : truncFinse
t R s (1 : MvPowerSeries σ R) = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
-/
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  truncFinset_one (by simpa using pos_of_ne_zero hnn)

@[simp]
/-
**MvPowerSeries.trunc_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc_C (n : σ ->₀ Nat) (hnn : n != 0) (a : R) : trunc R n (C a) = MvPolyn
omial.C a
参数：n : σ ->₀ Nat；hnn : n != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_C`：truncFinset_C (h : 0 in s) (r : R) : truncF
inset R s (C r) = MvPolynomial.C r
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
-/
theorem trunc_C (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simpa using pos_of_ne_zero hnn) a

@[simp]
/-
**MvPowerSeries.trunc_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc_C_mul (n : σ ->₀ Nat) (a : R) (p : MvPowerSeries σ R) : trunc R n (C
 a * p) = MvPolynomial.C a * trunc R n p
参数：n : σ ->₀ Nat；a : R；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_trunc`：coeff_trunc (m n : σ ->₀ Nat) (φ : MvPowerSer
ies σ R) : (trunc R n φ).coeff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MvPowerSeries.coeff_C_mul`：coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSerie
s σ R) (a : R) : coeff n (C a * φ) = a * coeff n φ
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trunc_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
/-
**MvPowerSeries.trunc_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc_map [CommSemiring S] (n : σ ->₀ Nat) (f : R ->+* S) (p : MvPowerSeri
es σ R) : trunc S n (map f p) = MvPolynomial.map f (trunc R n p)
参数：n : σ ->₀ Nat；f : R ->+* S；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_map`：truncFinset_map [CommSemiring S] (f : R -
>+* S) (p : MvPowerSeries σ R) : truncFinset S s (map f p) = MvPolynomial.map f 
(truncFinset R s p)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem trunc_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc S n (map f p) = MvPolynomial.map f (trunc R n p) := truncFinset_map f p

/-- A coefficient of a product of truncated power series equals the coefficient of the untruncated
product, with the two truncation levels `n₁` and `n₂` allowed to differ. -/
/-
**MvPowerSeries.coeff_trunc_mul_trunc_eq_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：coeff_trunc_mul_trunc_eq_coeff_mul (n : σ ->₀ Nat) (f g : MvPowerSeries σ 
R) {m : σ ->₀ Nat} (h : m < n) : (trunc R n f * trunc R n g).coeff m = coeff m (
f * g)
参数：n : σ ->₀ Nat；f g : MvPowerSeries σ R；h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_trunc_mul_trunc_eq_coeff_mul₂`：coeff_trunc_mul_trunc
_eq_coeff_mul₂ (n₁ n₂ : σ ->₀ Nat) (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h₁
 : m < n₁) (h₂ : m < n₂) : (trunc R n₁ …

--- 原说明 ---
A coefficient of a product of truncated power series equals the coefficient of t
he untruncated
product, with the two truncation levels `n₁` and `n₂` allowed to differ.
-/
theorem coeff_trunc_mul_trunc_eq_coeff_mul₂ (n₁ n₂ : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h₁ : m < n₁) (h₂ : m < n₂) :
    (trunc R n₁ f * trunc R n₂ g).coeff m = coeff m (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

/-- A coefficient of a product of truncated power series equals the coefficient of the untruncated
product. Both factors are truncated at the same level `n`. -/
/-
**MvPowerSeries.coeff_trunc_mul_trunc_eq_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：coeff_trunc_mul_trunc_eq_coeff_mul (n : σ ->₀ Nat) (f g : MvPowerSeries σ 
R) {m : σ ->₀ Nat} (h : m < n) : (trunc R n f * trunc R n g).coeff m = coeff m (
f * g)
参数：n : σ ->₀ Nat；f g : MvPowerSeries σ R；h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_trunc_mul_trunc_eq_coeff_mul₂`：coeff_trunc_mul_trunc
_eq_coeff_mul₂ (n₁ n₂ : σ ->₀ Nat) (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h₁
 : m < n₁) (h₂ : m < n₂) : (trunc R n₁ …

--- 原说明 ---
A coefficient of a product of truncated power series equals the coefficient of t
he untruncated
product. Both factors are truncated at the same level `n`.
-/
theorem coeff_trunc_mul_trunc_eq_coeff_mul (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m < n) :
    (trunc R n f * trunc R n g).coeff m = coeff m (f * g) :=
  coeff_trunc_mul_trunc_eq_coeff_mul₂ n n f g h h

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R]

/--
The `n`th truncation of a multivariate formal power series to a multivariate polynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`. -/
/-
**MvPowerSeries.trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ : MvPowerSeries σ R) : tr
unc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
The `n`th truncation of a multivariate formal power series to a multivariate pol
ynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function f
rom `σ`
to the naturals, then `trunc' R n f` is the multivariable polynomial obtained fr
om `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
.
-/
def trunc' (R : Type*) [CommSemiring R] (n : σ →₀ ℕ) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Iic n)

/-- Coefficients of the truncation of a multivariate power series. -/
/-
**MvPowerSeries.coeff_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R) : (trunc' R n φ).co
eff m = if m <= n then coeff m φ else 0
参数：m n : σ ->₀ Nat；φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `MvPowerSeries.coeff_truncFinset`：coeff_truncFinset [DecidableEq σ] {x : 
σ ->₀ Nat} (p : MvPowerSeries σ R) : (truncFinset R s p).coeff x = if x in s the
n p.coeff x else 0

--- 原说明 ---
Coefficients of the truncation of a multivariate power series.
-/
theorem coeff_trunc' (m n : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff m φ else 0 := by
  simpa using! coeff_truncFinset (s := Iic n) (x := m) φ
/-
**MvPowerSeries.trunc'_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] {n m : σ →₀ ℕ},   n ≤ m →     ∀ (φ : MvPowerSeries σ R), (MvPowerSeries.t
runc' R n) ↑((MvPowerSeries.trunc' R m) φ) = (MvPowerSeries.trunc' R n) φ
参数：φ : MvPowerSeries σ R；MvPowerSeries.trunc' R n；(MvPowerSeries.trunc' R m) φ；M
vPowerSeries.trunc' R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_truncFinset`：truncFinset_truncFinset {t : Fins
et (σ ->₀ Nat)} (h : s subseteq t) (p : MvPowerSeries σ R) : truncFinset R s (tr
uncFinset R t p) = truncFin…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
-/
theorem trunc'_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) (φ : MvPowerSeries σ R) :
    trunc' R n (trunc' R m φ) = trunc' R n φ :=
  truncFinset_truncFinset (Iic_subset_Iic.mpr h) φ

/-- Truncation of the multivariate power series `1` -/
@[simp]
/-
**MvPowerSeries.trunc'_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ),   (MvPowerSeries.trunc' R n) 1 = 1
参数：n : σ →₀ ℕ；MvPowerSeries.trunc' R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_one`：truncFinset_one (h : 0 in s) : truncFinse
t R s (1 : MvPowerSeries σ R) = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)

--- 原说明 ---
Truncation of the multivariate power series `1`
-/
theorem trunc'_one (n : σ →₀ ℕ) : trunc' R n 1 = 1 := truncFinset_one (by simp)

@[simp]
/-
**MvPowerSeries.trunc'_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ) (a : R),   (MvPowerSeries.trunc' R n) (MvPowerSeries.C a) = 
MvPolynomial.C a
参数：n : σ →₀ ℕ；a : R；MvPowerSeries.trunc' R n；MvPowerSeries.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_C`：truncFinset_C (h : 0 in s) (r : R) : truncF
inset R s (C r) = MvPolynomial.C r
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
-/
theorem trunc'_C (n : σ →₀ ℕ) (a : R) : trunc' R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simp) a

/-- A coefficient of a product of truncated power series equals the coefficient of the untruncated
product, with the two truncation levels `n₁` and `n₂` allowed to differ. -/
/-
**MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ) (f g : MvPowerSeries σ R)   {m : σ →₀ ℕ},   m ≤ n →     MvPo
lynomial.coeff m ((MvPowerSeries.trunc' R n) f * (MvPowerSeries.trunc' R n) g) =
 (MvPowerSeries.coeff m) (f * g)
参数：n : σ →₀ ℕ；f g : MvPowerSeries σ R；(MvPowerSeries.trunc' R n) f * (MvPowerSer
ies.trunc' R n) g；MvPowerSeries.coeff m；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul₂`：∀ {σ : Type u_1} {R
 : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemiring R] (n₁ n₂ : σ →₀ ℕ)  
 (f g : MvPowerSeries σ R) {m : σ →₀ ℕ}, …

--- 原说明 ---
A coefficient of a product of truncated power series equals the coefficient of t
he untruncated
product, with the two truncation levels `n₁` and `n₂` allowed to differ.
-/
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul₂ (n₁ n₂ : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h₁ : m ≤ n₁) (h₂ : m ≤ n₂) :
    (trunc' R n₁ f * trunc' R n₂ g).coeff m = coeff m (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

/-- A coefficient of a product of truncated power series equals the coefficient of the untruncated
product. Both factors are truncated at the same level `n`. -/
/-
**MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ) (f g : MvPowerSeries σ R)   {m : σ →₀ ℕ},   m ≤ n →     MvPo
lynomial.coeff m ((MvPowerSeries.trunc' R n) f * (MvPowerSeries.trunc' R n) g) =
 (MvPowerSeries.coeff m) (f * g)
参数：n : σ →₀ ℕ；f g : MvPowerSeries σ R；(MvPowerSeries.trunc' R n) f * (MvPowerSer
ies.trunc' R n) g；MvPowerSeries.coeff m；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul₂`：∀ {σ : Type u_1} {R
 : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemiring R] (n₁ n₂ : σ →₀ ℕ)  
 (f g : MvPowerSeries σ R) {m : σ →₀ ℕ}, …

--- 原说明 ---
A coefficient of a product of truncated power series equals the coefficient of t
he untruncated
product. Both factors are truncated at the same level `n`.
-/
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m ≤ n) :
    (trunc' R n f * trunc' R n g).coeff m = coeff m (f * g) :=
  coeff_trunc'_mul_trunc'_eq_coeff_mul₂ n n f g h h

@[deprecated coeff_trunc'_mul_trunc'_eq_coeff_mul (since := "2026-02-20")]
/-
**MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ) (f g : MvPowerSeries σ R)   {m : σ →₀ ℕ},   m ≤ n →     (MvP
owerSeries.coeff m) (f * g) = MvPolynomial.coeff m ((MvPowerSeries.trunc' R n) f
 * (MvPowerSeries.trunc' R n) g)
参数：n : σ →₀ ℕ；f g : MvPowerSeries σ R；MvPowerSeries.coeff m；f * g；(MvPowerSeries
.trunc' R n) f * (MvPowerSeries.trunc' R n) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul`：∀ {σ : Type u_1} {R 
: Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemiring R] (n : σ →₀ ℕ) (f g :
 MvPowerSeries σ R)   {m : σ →₀ ℕ},   m …
-/
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ →₀ ℕ) (f g : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (h : m ≤ n) : coeff m (f * g) = (trunc' R n f * trunc' R n g).coeff m :=
  (coeff_trunc'_mul_trunc'_eq_coeff_mul n f g h).symm
/-
**MvPowerSeries.trunc'_trunc'_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] {n : σ →₀ ℕ} {k : ℕ},   1 ≤ k →     ∀ (φ : MvPowerSeries σ R),       (MvP
owerSeries.trunc' R n) (↑((MvPowerSeries.trunc' R n) φ) ^ k) = (MvPowerSeries.tr
unc' R n) (φ ^ k)
参数：φ : MvPowerSeries σ R；MvPowerSeries.trunc' R n；↑((MvPowerSeries.trunc' R n) φ
) ^ k；MvPowerSeries.trunc' R n；φ ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_truncFinset_pow`：truncFinset_truncFinset_pow (
hs : IsLowerSet (s : Set (σ ->₀ Nat))) {k : Nat} (hk : 1 <= k) (p : MvPowerSerie
s σ R) : truncFinset R s ((trun…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem trunc'_trunc'_pow {n : σ →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) (φ : MvPowerSeries σ R) :
    trunc' R n ((trunc' R n φ) ^ k) = trunc' R n (φ ^ k) :=
  truncFinset_truncFinset_pow (by intro; grind) hk φ

@[simp]
/-
**MvPowerSeries.trunc'_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] (n : σ →₀ ℕ) (a : R)   (p : MvPowerSeries σ R),   (MvPowerSeries.trunc' R
 n) (MvPowerSeries.C a * p) = MvPolynomial.C a * (MvPowerSeries.trunc' R n) p
参数：n : σ →₀ ℕ；a : R；p : MvPowerSeries σ R；MvPowerSeries.trunc' R n；MvPowerSeries
.C a * p；MvPowerSeries.trunc' R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_trunc'`：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerS
eries σ R) : (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MvPowerSeries.coeff_C_mul`：coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSerie
s σ R) (a : R) : coeff n (C a * φ) = a * coeff n φ
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trunc'_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
/-
**MvPowerSeries.trunc'_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} {S : Type u_3} [inst : DecidableEq σ] [ins
t_1 : CommSemiring R]   [inst_2 : CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p 
: MvPowerSeries σ R),   (MvPowerSeries.trunc' S n) ((MvPowerSeries.map f) p) = (
MvPolynomial.map f) ((MvPowerSeries.trunc' R n) p)
参数：n : σ →₀ ℕ；f : R →+* S；p : MvPowerSeries σ R；MvPowerSeries.trunc' S n；(MvPowe
rSeries.map f) p；MvPolynomial.map f；(MvPowerSeries.trunc' R n) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_map`：truncFinset_map [CommSemiring S] (f : R -
>+* S) (p : MvPowerSeries σ R) : truncFinset S s (map f p) = MvPolynomial.map f 
(truncFinset R s p)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem trunc'_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map f p) = MvPolynomial.map f (trunc' R n p) := truncFinset_map f p

section

/-
**MvPowerSeries.totalDegree_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：totalDegree_trunc' {n : σ ->₀ Nat} (φ : MvPowerSeries σ R) : (trunc' R n φ
).totalDegree <= n.degree
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_Iic_of_monotone`：sup_Iic_of_monotone {β : Type*} [Semilattice
Sup β] [OrderBot β] {f : α -> β} (hf : Monotone f) : (Iic a).sup f = f a
· 使用引理 `Finsupp.degree_mono`：degree_mono {R : Type*} [AddCommMonoid R] [PartialO
rder R] [CanonicallyOrderedAdd R] : Monotone (Finsupp.degree (σ
· 使用引理 `MvPowerSeries.totalDegree_truncFinset`：totalDegree_truncFinset (p : MvPo
werSeries σ R) : (truncFinset R s p).totalDegree <= s.sup degree
-/
theorem totalDegree_trunc' {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    (trunc' R n φ).totalDegree ≤ n.degree := by
  simpa [← sup_Iic_of_monotone degree_mono] using! totalDegree_truncFinset φ
/-
**MvPowerSeries.ext_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：ext_trunc' {f g : MvPowerSeries σ R} : f = g ↔ forall n, trunc' R n f = tr
unc' R n g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `MvPowerSeries.coeff_trunc'`：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerS
eries σ R) : (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem ext_trunc' {f g : MvPowerSeries σ R} : f = g ↔ ∀ n, trunc' R n f = trunc' R n g := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc', if_pos le_rfl]
  simp_rw [this, h]

open Filter in
/-
**MvPowerSeries.eq_iff_frequently_trunc'_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : DecidableEq σ] [inst_1 : CommSemir
ing R] {f g : MvPowerSeries σ R},   f = g ↔ ∃ᶠ (m : σ →₀ ℕ) in Filter.atTop, (Mv
PowerSeries.trunc' R m) f = (MvPowerSeries.trunc' R m) g
参数：m : σ →₀ ℕ；MvPowerSeries.trunc' R m；MvPowerSeries.trunc' R m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `Filter.Frequently.forall_exists_of_atTop`：∀ {α : Type u_3} [inst : Preor
der α] {p : α → Prop}, (∃ᶠ (x : α) in Filter.atTop, p x) → ∀ (a : α), ∃ b, a ≤ b
 ∧ p b
· 使用定理 `MvPowerSeries.coeff_trunc'`：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerS
eries σ R) : (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem eq_iff_frequently_trunc'_eq {f g : MvPowerSeries σ R} :
    f = g ↔ ∃ᶠ m in atTop, trunc' R m f = trunc' R m g := by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc', if_pos hm₁]
  simp [this, hm₂]

end

end TruncLE

section TruncTotal

variable {n m : ℕ} [Finite σ] [CommSemiring R] (p q : MvPowerSeries σ R) {x : σ →₀ ℕ}

/-- The truncation of a multivariate formal power series at a total degree `n`
when the index `σ` is finite. -/
/-
**MvPowerSeries.truncTotal** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal {R : Type*} [CommSemiring R] (n : Nat) : MvPowerSeries σ R ->ₗ[
R] MvPolynomial σ R
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite

--- 原说明 ---
The truncation of a multivariate formal power series at a total degree `n`
when the index `σ` is finite.
-/
def truncTotal {R : Type*} [CommSemiring R] (n : ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R :=
  truncFinset R (finite_of_degree_lt n).toFinset
/-
**MvPowerSeries.coeff_truncTotal** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncTotal (h : degree x < n) : (truncTotal n p).coeff x = p.coeff x
参数：h : degree x < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_truncFinset_of_mem`：coeff_truncFinset_of_mem {x : σ 
->₀ Nat} (p : MvPowerSeries σ R) (h : x in s) : (truncFinset R s p).coeff x = p.
coeff x
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
-/
theorem coeff_truncTotal (h : degree x < n) :
    (truncTotal n p).coeff x = p.coeff x := coeff_truncFinset_of_mem p (by simpa)
/-
**MvPowerSeries.coeff_truncTotal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：coeff_truncTotal_eq_zero (h : n <= degree x) : (truncTotal n p).coeff x = 
0
参数：h : n <= degree x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_truncFinset_eq_zero`：coeff_truncFinset_eq_zero {x : 
σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉ s) : (truncFinset R s p).coeff x = 0
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem coeff_truncTotal_eq_zero (h : n ≤ degree x) :
    (truncTotal n p).coeff x = 0 := coeff_truncFinset_eq_zero p (by simpa)
/-
**MvPowerSeries.coeff_truncTotal_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：coeff_truncTotal_eq_ite : (truncTotal n p).coeff x = if x.degree < n then 
p.coeff x else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.coeff_truncTotal_eq_zero`：coeff_truncTotal_eq_zero (h : n 
<= degree x) : (truncTotal n p).coeff x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem coeff_truncTotal_eq_ite :
    (truncTotal n p).coeff x = if x.degree < n then p.coeff x else 0 := by
  by_cases h : x.degree < n
  · rw [if_pos h, coeff_truncTotal _ h]
  · rw [if_neg h, coeff_truncTotal_eq_zero _ (not_lt.mp h)]
/-
**MvPowerSeries.constantCoeff_truncTotal_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `MvPow
erSeries`。
形式化陈述：constantCoeff_truncTotal_eq_ite : (truncTotal n p).constantCoeff = if 0 < 
n then p.constantCoeff else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_truncTotal_eq_ite`：coeff_truncTotal_eq_ite : (truncT
otal n p).coeff x = if x.degree < n then p.coeff x else 0
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_truncTotal_eq_ite :
    (truncTotal n p).constantCoeff = if 0 < n then p.constantCoeff else 0 := by
  simp [MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite]
/-
**MvPowerSeries.truncTotal_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_eq_sum : p.truncTotal n = ∑ i in range n, p.homogeneousComponen
t i
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
· 使用定理 `MvPowerSeries.coeff_truncTotal_eq_ite`：coeff_truncTotal_eq_ite : (truncT
otal n p).coeff x = if x.degree < n then p.coeff x else 0
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPowerSeries.coeff_homogeneousComponent`：coeff_homogeneousComponent (p 
: Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (homogeneousComponent p
 f) = if degree d = p then coe…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncTotal_eq_sum : p.truncTotal n = ∑ i ∈ range n, p.homogeneousComponent i := by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncTotal_eq_ite]
/-
**MvPowerSeries.truncTotal_one** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_one (h : n != 0) : truncTotal n (1 : MvPowerSeries σ R) = 1
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.truncFinset_one`：truncFinset_one (h : 0 in s) : truncFinse
t R s (1 : MvPowerSeries σ R) = 1
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma truncTotal_one (h : n ≠ 0) : truncTotal n (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_one (by revert h; contrapose; simp)
/-
**MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul** 是 Mathlib 中的一个引理，
位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncTotal_mul_truncTotal_eq_coeff_mul (hx : degree x < n) : MvPolyn
omial.coeff x (p.truncTotal n * q.truncTotal n) = (coeff x) (p * q)
参数：hx : degree x < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul`：coeff_trun
cFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (σ ->₀ Nat))) {x 
: σ ->₀ Nat} (f g : MvPowerSeries σ R) (hx : x in …
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
lemma coeff_truncTotal_mul_truncTotal_eq_coeff_mul (hx : degree x < n) :
    MvPolynomial.coeff x (p.truncTotal n * q.truncTotal n) =
      (coeff x) (p * q) := coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  (fun _ _ h ↦ by simp; grind [degree_mono h]) p q (by simpa)
/-
**MvPowerSeries.coeff_truncTotal_pow** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_truncTotal_pow (h : x.degree < n) : ((p.truncTotal n ^ m)).coeff x =
 (p ^ m).coeff x
参数：h : x.degree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
-/
lemma coeff_truncTotal_pow (h : x.degree < n) :
    ((p.truncTotal n ^ m)).coeff x = (p ^ m).coeff x := by
  classical
  induction m using Nat.caseStrongRecOn generalizing x with
  | zero => grind [coeff_one, MvPolynomial.coeff_one]
  | ind k ih =>
    simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, MvPolynomial.coeff_mul, coeff_mul]
    congr! 2 with _ _
    · exact ih _ k.le_refl (by grind [mem_antidiagonal])
    · exact coeff_truncTotal _ (by grind [mem_antidiagonal])
/-
**MvPowerSeries.truncTotal_pow_eq_truncTotal_truncTotal_pow** 是 Mathlib 中的一个引理，位
于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_pow_eq_truncTotal_truncTotal_pow : (p ^ m).truncTotal n = ((p.t
runcTotal n).toMvPowerSeries ^ m).truncTotal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPowerSeries.coeff_truncTotal_pow`：coeff_truncTotal_pow (h : x.degree <
 n) : ((p.truncTotal n ^ m)).coeff x = (p ^ m).coeff x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_truncTotal_eq_zero`：coeff_truncTotal_eq_zero (h : n 
<= degree x) : (truncTotal n p).coeff x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncTotal_pow_eq_truncTotal_truncTotal_pow :
    (p ^ m).truncTotal n = ((p.truncTotal n).toMvPowerSeries ^ m).truncTotal n := by
  ext d
  by_cases hd : d.degree < n
  · simp_rw [coeff_truncTotal _ hd]
    exact_mod_cast (coeff_truncTotal_pow _ hd).symm
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
/-
**MvPowerSeries.totalDegree_truncTotal_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：totalDegree_truncTotal_lt (h : n != 0) : (truncTotal n p).totalDegree < n
参数：h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
· 使用引理 `MvPowerSeries.totalDegree_truncFinset`：totalDegree_truncFinset (p : MvPo
werSeries σ R) : (truncFinset R s p).totalDegree <= s.sup degree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `Nat.lt_of_sub_ne_zero`：∀ {n m : ℕ}, n - m ≠ 0 → m < n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem totalDegree_truncTotal_lt (h : n ≠ 0) :
    (truncTotal n p).totalDegree < n := by
  apply (totalDegree_truncFinset p).trans_lt
  simp [Finset.sup_lt_iff (Nat.lt_of_sub_ne_zero h)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.truncTotal_coe_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSer
ies`。
形式化陈述：truncTotal_coe_eq_self_iff (p : MvPolynomial σ R) (h : n != 0) : truncTota
l n p = p ↔ p.totalDegree < n
参数：p : MvPolynomial σ R；h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.finite_of_degree_lt`：finite_of_degree_lt [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f < n}.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.truncTotal.eq_1`：∀ {σ : Type u_1} [inst : Finite σ] {R : T
ype u_4} [inst_1 : CommSemiring R] (n : ℕ),   MvPowerSeries.truncTotal n = MvPow
erSeries.truncFinse…
· 使用引理 `MvPowerSeries.truncFinset_coe_eq_self_iff`：truncFinset_coe_eq_self_iff (
p : MvPolynomial σ R) : truncFinset R s p = p ↔ p.support subseteq s
· 使用定理 `Set.Finite.subset_toFinset`：subset_toFinset {s : Finset α} : s subseteq 
ht.toFinset ↔ ↑s subseteq t
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem truncTotal_coe_eq_self_iff (p : MvPolynomial σ R) (h : n ≠ 0) :
    truncTotal n p = p ↔ p.totalDegree < n := by
  rw [truncTotal, truncFinset_coe_eq_self_iff, Set.Finite.subset_toFinset,
    MvPolynomial.totalDegree, Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr h), Set.subset_def]
  simp [degree, sum]

end TruncTotal

end MvPowerSeries

end

