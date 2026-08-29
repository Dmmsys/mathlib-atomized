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

  Here, `m` and `n` have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


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

variable [CommSemiring R] {s : Finset (σ ->₀ Nat)}

/--
Definition of `truncFinset` / `truncFinset` 的定义

English:
definition truncFinset
  signature: (R : Type*) [CommSemiring R] (s : Finset (σ ->₀ Nat))
  body: ∑ x in s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    ext
    simp [MvPolynomial.coeff, single, MvPolynomial.monomial]

中文:
定义 truncFinset
  签名: (R : 类型) [CommSemiring R] (s : Finset (σ ->₀ 自然数))
  定义体: ∑ x in s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    ext
    simp [MvPolynomial.coeff, single, MvPolynomial.monomial]

Depends on / 依赖: MvPolynomial, MvPolynomial.monomial, monomial, p.coeff
-/
def truncFinset (R : Type*) [CommSemiring R] (s : Finset (σ ->₀ Nat)) :
    MvPowerSeries σ R ->ₗ[R] MvPolynomial σ R where
  toFun p := ∑ x in s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    ext
    simp [MvPolynomial.coeff, single, MvPolynomial.monomial]

/--
theorem `truncFinset_apply` / 定理 `truncFinset_apply`

English:
theorem truncFinset_apply
  given: (p : MvPowerSeries σ R)
  proof: by rfl

@[grind =]

中文:
定理 truncFinset_apply
  条件: (p : MvPowerSeries σ R)
  证明: by rfl

@[grind =]
-/
theorem truncFinset_apply (p : MvPowerSeries σ R) :
    truncFinset R s p = ∑ x in s, MvPolynomial.monomial x (p.coeff x) := by rfl

@[grind =]
/--
theorem `coeff_truncFinset_of_mem` / 定理 `coeff_truncFinset_of_mem`

English:
theorem coeff_truncFinset_of_mem
  given: {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x in s)
  proof: by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

@[grind =]

中文:
定理 coeff_truncFinset_of_mem
  条件: {x : σ ->₀ 自然数} (p : MvPowerSeries σ R) (h : x in s)
  证明: by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

@[grind =]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sum, classical, coeff_sum, truncFinset_apply
-/
theorem coeff_truncFinset_of_mem {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x in s) :
    (truncFinset R s p).coeff x = p.coeff x := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

@[grind =]
/--
theorem `coeff_truncFinset_eq_zero` / 定理 `coeff_truncFinset_eq_zero`

English:
theorem coeff_truncFinset_eq_zero
  given: {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉ s)
  proof: by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

中文:
定理 coeff_truncFinset_eq_zero
  条件: {x : σ ->₀ 自然数} (p : MvPowerSeries σ R) (h : x ∉ s)
  证明: by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sum, classical, coeff_sum, truncFinset_apply
-/
theorem coeff_truncFinset_eq_zero {x : σ ->₀ Nat} (p : MvPowerSeries σ R) (h : x ∉ s) :
    (truncFinset R s p).coeff x = 0 := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

/--
lemma `coeff_truncFinset` / 引理 `coeff_truncFinset`

English:
lemma coeff_truncFinset
  given: [DecidableEq σ] {x : σ ->₀ Nat} (p : MvPowerSeries σ R)
  proof: by
  simp [truncFinset_apply, MvPolynomial.coeff_sum]

中文:
引理 coeff_truncFinset
  条件: [DecidableEq σ] {x : σ ->₀ 自然数} (p : MvPowerSeries σ R)
  证明: by
  simp [truncFinset_apply, MvPolynomial.coeff_sum]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sum, coeff_sum, truncFinset_apply
-/
lemma coeff_truncFinset [DecidableEq σ] {x : σ ->₀ Nat} (p : MvPowerSeries σ R) :
    (truncFinset R s p).coeff x = if x in s then p.coeff x else 0 := by
  simp [truncFinset_apply, MvPolynomial.coeff_sum]

/--
theorem `truncFinset_monomial` / 定理 `truncFinset_monomial`

English:
theorem truncFinset_monomial
  given: {x : σ ->₀ Nat} (r : R) (h : x in s)
  proof: by
  classical
  ext
  grind [coeff_monomial, MvPolynomial.coeff_monomial]

中文:
定理 truncFinset_monomial
  条件: {x : σ ->₀ 自然数} (r : R) (h : x in s)
  证明: by
  classical
  ext
  grind [coeff_monomial, MvPolynomial.coeff_monomial]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_monomial, classical, coeff_monomial
-/
theorem truncFinset_monomial {x : σ ->₀ Nat} (r : R) (h : x in s) :
    truncFinset R s (monomial x r) = MvPolynomial.monomial x r := by
  classical
  ext
  grind [coeff_monomial, MvPolynomial.coeff_monomial]

/--
theorem `truncFinset_monomial_eq_zero` / 定理 `truncFinset_monomial_eq_zero`

English:
theorem truncFinset_monomial_eq_zero
  given: {x : σ ->₀ Nat} (r : R) (h : x ∉ s)
  proof: by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  grind

中文:
定理 truncFinset_monomial_eq_zero
  条件: {x : σ ->₀ 自然数} (r : R) (h : x ∉ s)
  证明: by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  grind

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sum, classical, coeff_monomial, coeff_sum, truncFinset
-/
theorem truncFinset_monomial_eq_zero {x : σ ->₀ Nat} (r : R) (h : x ∉ s) :
    truncFinset R s (monomial x r) = 0 := by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  grind

/--
theorem `truncFinset_C` / 定理 `truncFinset_C`

English:
theorem truncFinset_C
  given: (h : 0 in s) (r : R)
  statement: truncFinset R s (C r) = MvPolynomial.C r
  proof: truncFinset_monomial r h

中文:
定理 truncFinset_C
  条件: (h : 0 in s) (r : R)
  结论: truncFinset R s (C r) = MvPolynomial.C r
  证明: truncFinset_monomial r h

Depends on / 依赖: truncFinset_monomial
-/
theorem truncFinset_C (h : 0 in s) (r : R) : truncFinset R s (C r) = MvPolynomial.C r :=
  truncFinset_monomial r h

/--
theorem `truncFinset_one` / 定理 `truncFinset_one`

English:
theorem truncFinset_one
  given: (h : 0 in s)
  statement: truncFinset R s (1 : MvPowerSeries σ R) = 1
  proof: truncFinset_C h 1

中文:
定理 truncFinset_one
  条件: (h : 0 in s)
  结论: truncFinset R s (1 : MvPowerSeries σ R) = 1
  证明: truncFinset_C h 1

Depends on / 依赖: truncFinset_C
-/
theorem truncFinset_one (h : 0 in s) : truncFinset R s (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_C h 1

/--
theorem `truncFinset_truncFinset` / 定理 `truncFinset_truncFinset`

English:
theorem truncFinset_truncFinset
  given: {t : Finset (σ ->₀ Nat)} (h : s subseteq t) (p : MvPowerSeries σ R)
  proof: by
  ext x
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

中文:
定理 truncFinset_truncFinset
  条件: {t : Finset (σ ->₀ 自然数)} (h : s subseteq t) (p : MvPowerSeries σ R)
  证明: by
  ext x
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_coe, coeff_coe
-/
theorem truncFinset_truncFinset {t : Finset (σ ->₀ Nat)} (h : s subseteq t) (p : MvPowerSeries σ R) :
    truncFinset R s (truncFinset R t p) = truncFinset R s p := by
  ext x
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

/--
theorem `truncFinset_map` / 定理 `truncFinset_map`

English:
theorem truncFinset_map
  given: [CommSemiring S] (f : R ->+* S) (p : MvPowerSeries σ R)
  proof: by
  ext x
  by_cases x in s <;> grind [coeff_map, MvPolynomial.coeff_map]

中文:
定理 truncFinset_map
  条件: [CommSemiring S] (f : R ->+* S) (p : MvPowerSeries σ R)
  证明: by
  ext x
  by_cases x in s <;> grind [coeff_map, MvPolynomial.coeff_map]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_map, coeff_map
-/
theorem truncFinset_map [CommSemiring S] (f : R ->+* S) (p : MvPowerSeries σ R) :
    truncFinset S s (map f p) = MvPolynomial.map f (truncFinset R s p) := by
  ext x
  by_cases x in s <;> grind [coeff_map, MvPolynomial.coeff_map]

/--
theorem `coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂` / 定理 `coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂`

English:
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂
  statement: {t : Finset (σ ->₀ Nat)}
  proof: by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset_of_mem _ (hs (show i <= x by simp [← hij]) hxs),
    coeff_truncFinset_of_mem _ (ht (show j <= x by simp [← hij]) hxt)]

中文:
定理 coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂
  结论: {t : Finset (σ ->₀ 自然数)}
  证明: by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset_of_mem _ (hs (show i <= x by simp [← hij]) hxs),
    coeff_truncFinset_of_mem _ (ht (show j <= x by simp [← hij]) hxt)]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_mul, MvPowerSeries, MvPowerSeries.coeff_mul, classical, coeff_mul, coeff_truncFinset_of_mem, mem_antidiagonal, sum_congr
-/
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ {t : Finset (σ ->₀ Nat)}
    (hs : IsLowerSet (s : Set (σ ->₀ Nat))) (ht : IsLowerSet (t : Set (σ ->₀ Nat)))
    {x : σ ->₀ Nat} (f g : MvPowerSeries σ R) (hxs : x in s) (hxt : x in t) :
      (truncFinset R s f * truncFinset R t g).coeff x = coeff x (f * g) := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset_of_mem _ (hs (show i <= x by simp [← hij]) hxs),
    coeff_truncFinset_of_mem _ (ht (show j <= x by simp [← hij]) hxt)]

/--
theorem `coeff_truncFinset_mul_truncFinset_eq_coeff_mul` / 定理 `coeff_truncFinset_mul_truncFinset_eq_coeff_mul`

English:
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  statement: (hs : IsLowerSet (s : Set (σ ->₀ Nat)))
  proof: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ hs hs f g hx hx

中文:
定理 coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  结论: (hs : IsLowerSet (s : Set (σ ->₀ 自然数)))
  证明: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ hs hs f g hx hx
-/
theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (σ ->₀ Nat)))
    {x : σ ->₀ Nat} (f g : MvPowerSeries σ R) (hx : x in s) :
      (truncFinset R s f * truncFinset R s g).coeff x = coeff x (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ hs hs f g hx hx

/--
theorem `truncFinset_truncFinset_pow` / 定理 `truncFinset_truncFinset_pow`

English:
theorem truncFinset_truncFinset_pow
  statement: (hs : IsLowerSet (s : Set (σ ->₀ Nat))) {k : Nat} (hk : 1 <= k)
  proof: by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x in s
    · rw [coeff_truncFinset_of_mem _ hx, coeff_truncFinset_of_mem _ hx, pow_succ,
        ← coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx, ih, t

中文:
定理 truncFinset_truncFinset_pow
  结论: (hs : IsLowerSet (s : Set (σ ->₀ 自然数))) {k : 自然数} (hk : 1 <= k)
  证明: by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x in s
    · rw [coeff_truncFinset_of_mem _ hx, coeff_truncFinset_of_mem _ hx, pow_succ,
        ← coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx, ih, t

Depends on / 依赖: Nat.le_induction, coeff_truncFinset_eq_zero, coeff_truncFinset_mul_truncFinset_eq_coeff_mul, coeff_truncFinset_of_mem, le_induction, pow_succ, truncFinset_truncFinset
-/
theorem truncFinset_truncFinset_pow (hs : IsLowerSet (s : Set (σ ->₀ Nat))) {k : Nat} (hk : 1 <= k)
    (p : MvPowerSeries σ R) : truncFinset R s ((truncFinset R s p) ^ k) =
      truncFinset R s (p ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x in s
    · rw [coeff_truncFinset_of_mem _ hx, coeff_truncFinset_of_mem _ hx, pow_succ,
        ← coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx, ih, truncFinset_truncFinset
        (by rfl), pow_succ, coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx]
    simp [coeff_truncFinset_eq_zero _ hx]

/--
theorem `support_truncFinset_subset` / 定理 `support_truncFinset_subset`

English:
theorem support_truncFinset_subset
  given: (p : MvPowerSeries σ R)
  statement: (truncFinset R s p).support subseteq s
  proof: by
  intro; contrapose
  simpa using coeff_truncFinset_eq_zero p

中文:
定理 support_truncFinset_subset
  条件: (p : MvPowerSeries σ R)
  结论: (truncFinset R s p).support subseteq s
  证明: by
  intro; contrapose
  simpa using coeff_truncFinset_eq_zero p

Depends on / 依赖: coeff_truncFinset_eq_zero, contrapose
-/
theorem support_truncFinset_subset (p : MvPowerSeries σ R) : (truncFinset R s p).support subseteq s := by
  intro; contrapose
  simpa using coeff_truncFinset_eq_zero p

/--
lemma `totalDegree_truncFinset` / 引理 `totalDegree_truncFinset`

English:
lemma totalDegree_truncFinset
  given: (p : MvPowerSeries σ R)
  proof: by
  simpa [MvPolynomial.totalDegree] using! sup_mono (support_truncFinset_subset p)

中文:
引理 totalDegree_truncFinset
  条件: (p : MvPowerSeries σ R)
  证明: by
  simpa [MvPolynomial.totalDegree] using! sup_mono (support_truncFinset_subset p)

Depends on / 依赖: MvPolynomial, MvPolynomial.totalDegree, sup_mono, support_truncFinset_subset, totalDegree
-/
lemma totalDegree_truncFinset (p : MvPowerSeries σ R) :
    (truncFinset R s p).totalDegree <= s.sup degree := by
  simpa [MvPolynomial.totalDegree] using! sup_mono (support_truncFinset_subset p)

/--
lemma `truncFinset_coe_eq_self_iff` / 引理 `truncFinset_coe_eq_self_iff`

English:
lemma truncFinset_coe_eq_self_iff
  given: (p : MvPolynomial σ R)
  proof: by
  refine ⟨fun h => ?_, fun h => MvPolynomial.ext _ _ fun x => ?_⟩
  · rw [← h]
    exact support_truncFinset_subset ..
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

中文:
引理 truncFinset_coe_eq_self_iff
  条件: (p : MvPolynomial σ R)
  证明: by
  refine ⟨fun h => ?_, fun h => MvPolynomial.ext _ _ fun x => ?_⟩
  · rw [← h]
    exact support_truncFinset_subset ..
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_coe, MvPolynomial.ext, coeff_coe, support_truncFinset_subset
-/
lemma truncFinset_coe_eq_self_iff (p : MvPolynomial σ R) :
    truncFinset R s p = p ↔ p.support subseteq s := by
  refine ⟨fun h => ?_, fun h => MvPolynomial.ext _ _ fun x => ?_⟩
  · rw [← h]
    exact support_truncFinset_subset ..
  by_cases x in s <;> grind [MvPolynomial.coeff_coe]

end TruncFinset

section TruncLT

variable [DecidableEq σ] [CommSemiring R]

/--
Definition of `trunc` / `trunc` 的定义

English:
definition trunc
  signature: (R : Type*) [CommSemiring R] (n : σ ->₀ Nat)
  body: truncFinset R (Iio n)

中文:
定义 trunc
  签名: (R : 类型) [CommSemiring R] (n : σ ->₀ 自然数)
  定义体: truncFinset R (Iio n)

Depends on / 依赖: truncFinset
-/
def trunc (R : Type*) [CommSemiring R] (n : σ ->₀ Nat) :
    MvPowerSeries σ R ->ₗ[R] MvPolynomial σ R := truncFinset R (Iio n)

/--
theorem `coeff_trunc` / 定理 `coeff_trunc`

English:
theorem coeff_trunc
  given: (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R)
  proof: by
  simpa using! coeff_truncFinset (s := Iio n) (x := m) φ

@[simp]

中文:
定理 coeff_trunc
  条件: (m n : σ ->₀ 自然数) (φ : MvPowerSeries σ R)
  证明: by
  simpa using! coeff_truncFinset (s := Iio n) (x := m) φ

@[simp]

Depends on / 依赖: coeff_truncFinset
-/
theorem coeff_trunc (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff m φ else 0 := by
  simpa using! coeff_truncFinset (s := Iio n) (x := m) φ

@[simp]
/--
theorem `trunc_one` / 定理 `trunc_one`

English:
theorem trunc_one
  given: (n : σ ->₀ Nat) (hnn : n != 0)
  statement: trunc R n 1 = 1
  proof: truncFinset_one (by simpa using pos_of_ne_zero hnn)

@[simp]

中文:
定理 trunc_one
  条件: (n : σ ->₀ 自然数) (hnn : n != 0)
  结论: trunc R n 1 = 1
  证明: truncFinset_one (by simpa using pos_of_ne_zero hnn)

@[simp]

Depends on / 依赖: pos_of_ne_zero, truncFinset_one
-/
theorem trunc_one (n : σ ->₀ Nat) (hnn : n != 0) : trunc R n 1 = 1 :=
  truncFinset_one (by simpa using pos_of_ne_zero hnn)

@[simp]
/--
theorem `trunc_C` / 定理 `trunc_C`

English:
theorem trunc_C
  given: (n : σ ->₀ Nat) (hnn : n != 0) (a : R)
  statement: trunc R n (C a) = MvPolynomial.C a
  proof: truncFinset_C (by simpa using pos_of_ne_zero hnn) a

@[simp]

中文:
定理 trunc_C
  条件: (n : σ ->₀ 自然数) (hnn : n != 0) (a : R)
  结论: trunc R n (C a) = MvPolynomial.C a
  证明: truncFinset_C (by simpa using pos_of_ne_zero hnn) a

@[simp]

Depends on / 依赖: pos_of_ne_zero, truncFinset_C
-/
theorem trunc_C (n : σ ->₀ Nat) (hnn : n != 0) (a : R) : trunc R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simpa using pos_of_ne_zero hnn) a

@[simp]
/--
theorem `trunc_C_mul` / 定理 `trunc_C_mul`

English:
theorem trunc_C_mul
  given: (n : σ ->₀ Nat) (a : R) (p : MvPowerSeries σ R)
  proof: by
  ext m; simp [coeff_trunc]

@[simp]

中文:
定理 trunc_C_mul
  条件: (n : σ ->₀ 自然数) (a : R) (p : MvPowerSeries σ R)
  证明: by
  ext m; simp [coeff_trunc]

@[simp]

Depends on / 依赖: coeff_trunc
-/
theorem trunc_C_mul (n : σ ->₀ Nat) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
/--
theorem `trunc_map` / 定理 `trunc_map`

English:
theorem trunc_map
  given: [CommSemiring S] (n : σ ->₀ Nat) (f : R ->+* S) (p : MvPowerSeries σ R)
  proof: truncFinset_map f p

中文:
定理 trunc_map
  条件: [CommSemiring S] (n : σ ->₀ 自然数) (f : R ->+* S) (p : MvPowerSeries σ R)
  证明: truncFinset_map f p

Depends on / 依赖: truncFinset_map
-/
theorem trunc_map [CommSemiring S] (n : σ ->₀ Nat) (f : R ->+* S) (p : MvPowerSeries σ R) :
    trunc S n (map f p) = MvPolynomial.map f (trunc R n p) := truncFinset_map f p

/--
theorem `coeff_trunc_mul_trunc_eq_coeff_mul₂` / 定理 `coeff_trunc_mul_trunc_eq_coeff_mul₂`

English:
theorem coeff_trunc_mul_trunc_eq_coeff_mul₂
  statement: (n₁ n₂ : σ ->₀ Nat)
  proof: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

中文:
定理 coeff_trunc_mul_trunc_eq_coeff_mul₂
  结论: (n₁ n₂ : σ ->₀ 自然数)
  证明: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

Depends on / 依赖: IsLowerSet
-/
theorem coeff_trunc_mul_trunc_eq_coeff_mul₂ (n₁ n₂ : σ ->₀ Nat)
    (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h₁ : m < n₁) (h₂ : m < n₂) :
    (trunc R n₁ f * trunc R n₂ g).coeff m = coeff m (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

/--
theorem `coeff_trunc_mul_trunc_eq_coeff_mul` / 定理 `coeff_trunc_mul_trunc_eq_coeff_mul`

English:
theorem coeff_trunc_mul_trunc_eq_coeff_mul
  statement: (n : σ ->₀ Nat)
  proof: coeff_trunc_mul_trunc_eq_coeff_mul₂ n n f g h h

中文:
定理 coeff_trunc_mul_trunc_eq_coeff_mul
  结论: (n : σ ->₀ 自然数)
  证明: coeff_trunc_mul_trunc_eq_coeff_mul₂ n n f g h h
-/
theorem coeff_trunc_mul_trunc_eq_coeff_mul (n : σ ->₀ Nat)
    (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h : m < n) :
    (trunc R n f * trunc R n g).coeff m = coeff m (f * g) :=
  coeff_trunc_mul_trunc_eq_coeff_mul₂ n n f g h h

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R]

/--
Definition of `trunc'` / `trunc'` 的定义

English:
definition trunc'
  signature: (R : Type*) [CommSemiring R] (n : σ ->₀ Nat)
  body: truncFinset R (Iic n)

中文:
定义 trunc'
  签名: (R : 类型) [CommSemiring R] (n : σ ->₀ 自然数)
  定义体: truncFinset R (Iic n)
-/
def trunc' (R : Type*) [CommSemiring R] (n : σ ->₀ Nat) :
    MvPowerSeries σ R ->ₗ[R] MvPolynomial σ R := truncFinset R (Iic n)

/--
theorem `coeff_trunc'` / 定理 `coeff_trunc'`

English:
theorem coeff_trunc'
  given: (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R)
  proof: by
  simpa using! coeff_truncFinset (s := Iic n) (x := m) φ

中文:
定理 coeff_trunc'
  条件: (m n : σ ->₀ 自然数) (φ : MvPowerSeries σ R)
  证明: by
  simpa using! coeff_truncFinset (s := Iic n) (x := m) φ

Depends on / 依赖: coeff_truncFinset
-/
theorem coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0 := by
  simpa using! coeff_truncFinset (s := Iic n) (x := m) φ

/--
theorem `trunc'_trunc'` / 定理 `trunc'_trunc'`

English:
theorem trunc'_trunc'
  given: {n m : σ ->₀ Nat} (h : n <= m) (φ : MvPowerSeries σ R)
  proof: truncFinset_truncFinset (Iic_subset_Iic.mpr h) φ

中文:
定理 trunc'_trunc'
  条件: {n m : σ ->₀ 自然数} (h : n <= m) (φ : MvPowerSeries σ R)
  证明: truncFinset_truncFinset (Iic_subset_Iic.mpr h) φ
-/
theorem trunc'_trunc' {n m : σ ->₀ Nat} (h : n <= m) (φ : MvPowerSeries σ R) :
    trunc' R n (trunc' R m φ) = trunc' R n φ :=
  truncFinset_truncFinset (Iic_subset_Iic.mpr h) φ

/-- Truncation of the multivariate power series `1` -/
@[simp]
/--
theorem `trunc'_one` / 定理 `trunc'_one`

English:
theorem trunc'_one
  given: (n : σ ->₀ Nat)
  statement: trunc' R n 1 = 1
  proof: truncFinset_one (by simp)

@[simp]

中文:
定理 trunc'_one
  条件: (n : σ ->₀ 自然数)
  结论: trunc' R n 1 = 1
  证明: truncFinset_one (by simp)

@[simp]
-/
theorem trunc'_one (n : σ ->₀ Nat) : trunc' R n 1 = 1 := truncFinset_one (by simp)

@[simp]
/--
theorem `trunc'_C` / 定理 `trunc'_C`

English:
theorem trunc'_C
  given: (n : σ ->₀ Nat) (a : R)
  statement: trunc' R n (C a) = MvPolynomial.C a
  proof: truncFinset_C (by simp) a

中文:
定理 trunc'_C
  条件: (n : σ ->₀ 自然数) (a : R)
  结论: trunc' R n (C a) = MvPolynomial.C a
  证明: truncFinset_C (by simp) a
-/
theorem trunc'_C (n : σ ->₀ Nat) (a : R) : trunc' R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simp) a

/--
theorem `coeff_trunc'_mul_trunc'_eq_coeff_mul₂` / 定理 `coeff_trunc'_mul_trunc'_eq_coeff_mul₂`

English:
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul₂
  statement: (n₁ n₂ : σ ->₀ Nat)
  proof: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

中文:
定理 coeff_trunc'_mul_trunc'_eq_coeff_mul₂
  结论: (n₁ n₂ : σ ->₀ 自然数)
  证明: coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)
-/
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul₂ (n₁ n₂ : σ ->₀ Nat)
    (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h₁ : m <= n₁) (h₂ : m <= n₂) :
    (trunc' R n₁ f * trunc' R n₂ g).coeff m = coeff m (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul₂ (by grind [IsLowerSet]) (by grind [IsLowerSet])
    f g (by simpa) (by simpa)

/--
theorem `coeff_trunc'_mul_trunc'_eq_coeff_mul` / 定理 `coeff_trunc'_mul_trunc'_eq_coeff_mul`

English:
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul
  statement: (n : σ ->₀ Nat)
  proof: coeff_trunc'_mul_trunc'_eq_coeff_mul₂ n n f g h h

@[deprecated coeff_trunc'_mul_trunc'_eq_coeff_mul (since := "2026-02-20")]

中文:
定理 coeff_trunc'_mul_trunc'_eq_coeff_mul
  结论: (n : σ ->₀ 自然数)
  证明: coeff_trunc'_mul_trunc'_eq_coeff_mul₂ n n f g h h

@[deprecated coeff_trunc'_mul_trunc'_eq_coeff_mul (since := "2026-02-20")]
-/
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul (n : σ ->₀ Nat)
    (f g : MvPowerSeries σ R) {m : σ ->₀ Nat} (h : m <= n) :
    (trunc' R n f * trunc' R n g).coeff m = coeff m (f * g) :=
  coeff_trunc'_mul_trunc'_eq_coeff_mul₂ n n f g h h

@[deprecated coeff_trunc'_mul_trunc'_eq_coeff_mul (since := "2026-02-20")]
/--
theorem `coeff_mul_eq_coeff_trunc'_mul_trunc'` / 定理 `coeff_mul_eq_coeff_trunc'_mul_trunc'`

English:
theorem coeff_mul_eq_coeff_trunc'_mul_trunc'
  statement: (n : σ ->₀ Nat) (f g : MvPowerSeries σ R) {m : σ ->₀ Nat}
  proof: (coeff_trunc'_mul_trunc'_eq_coeff_mul n f g h).symm

中文:
定理 coeff_mul_eq_coeff_trunc'_mul_trunc'
  结论: (n : σ ->₀ 自然数) (f g : MvPowerSeries σ R) {m : σ ->₀ 自然数}
  证明: (coeff_trunc'_mul_trunc'_eq_coeff_mul n f g h).symm

Depends on / 依赖: _eq_coeff_mul, _mul_trunc, coeff_trunc
-/
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ ->₀ Nat) (f g : MvPowerSeries σ R) {m : σ ->₀ Nat}
    (h : m <= n) : coeff m (f * g) = (trunc' R n f * trunc' R n g).coeff m :=
  (coeff_trunc'_mul_trunc'_eq_coeff_mul n f g h).symm

/--
theorem `trunc'_trunc'_pow` / 定理 `trunc'_trunc'_pow`

English:
theorem trunc'_trunc'_pow
  given: {n : σ ->₀ Nat} {k : Nat} (hk : 1 <= k) (φ : MvPowerSeries σ R)
  proof: truncFinset_truncFinset_pow (by intro; grind) hk φ

@[simp]

中文:
定理 trunc'_trunc'_pow
  条件: {n : σ ->₀ 自然数} {k : 自然数} (hk : 1 <= k) (φ : MvPowerSeries σ R)
  证明: truncFinset_truncFinset_pow (by intro; grind) hk φ

@[simp]
-/
theorem trunc'_trunc'_pow {n : σ ->₀ Nat} {k : Nat} (hk : 1 <= k) (φ : MvPowerSeries σ R) :
    trunc' R n ((trunc' R n φ) ^ k) = trunc' R n (φ ^ k) :=
  truncFinset_truncFinset_pow (by intro; grind) hk φ

@[simp]
/--
theorem `trunc'_C_mul` / 定理 `trunc'_C_mul`

English:
theorem trunc'_C_mul
  given: (n : σ ->₀ Nat) (a : R) (p : MvPowerSeries σ R)
  proof: by
  ext m; simp [coeff_trunc']

@[simp]

中文:
定理 trunc'_C_mul
  条件: (n : σ ->₀ 自然数) (a : R) (p : MvPowerSeries σ R)
  证明: by
  ext m; simp [coeff_trunc']

@[simp]
-/
theorem trunc'_C_mul (n : σ ->₀ Nat) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
/--
theorem `trunc'_map` / 定理 `trunc'_map`

English:
theorem trunc'_map
  given: [CommSemiring S] (n : σ ->₀ Nat) (f : R ->+* S) (p : MvPowerSeries σ R)
  proof: truncFinset_map f p

中文:
定理 trunc'_map
  条件: [CommSemiring S] (n : σ ->₀ 自然数) (f : R ->+* S) (p : MvPowerSeries σ R)
  证明: truncFinset_map f p
-/
theorem trunc'_map [CommSemiring S] (n : σ ->₀ Nat) (f : R ->+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map f p) = MvPolynomial.map f (trunc' R n p) := truncFinset_map f p

section

/--
theorem `totalDegree_trunc'` / 定理 `totalDegree_trunc'`

English:
theorem totalDegree_trunc'
  given: {n : σ ->₀ Nat} (φ : MvPowerSeries σ R)
  proof: by
  simpa [← sup_Iic_of_monotone degree_mono] using! totalDegree_truncFinset φ

中文:
定理 totalDegree_trunc'
  条件: {n : σ ->₀ 自然数} (φ : MvPowerSeries σ R)
  证明: by
  simpa [← sup_Iic_of_monotone degree_mono] using! totalDegree_truncFinset φ

Depends on / 依赖: degree_mono, sup_Iic_of_monotone, totalDegree_truncFinset
-/
theorem totalDegree_trunc' {n : σ ->₀ Nat} (φ : MvPowerSeries σ R) :
    (trunc' R n φ).totalDegree <= n.degree := by
  simpa [← sup_Iic_of_monotone degree_mono] using! totalDegree_truncFinset φ

/--
theorem `ext_trunc'` / 定理 `ext_trunc'`

English:
theorem ext_trunc'
  given: {f g : MvPowerSeries σ R}
  statement: f = g ↔ forall n, trunc' R n f = trunc' R n g
  proof: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc']; rw [if_pos le_rfl]
  simp_rw [this, h]

中文:
定理 ext_trunc'
  条件: {f g : MvPowerSeries σ R}
  结论: f = g ↔ 对任意 n, trunc' R n f = trunc' R n g
  证明: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc']; rw [if_pos le_rfl]
  simp_rw [this, h]

Depends on / 依赖: MvPowerSeries, coeff_trunc, if_pos, le_rfl, simp_rw, specialize
-/
theorem ext_trunc' {f g : MvPowerSeries σ R} : f = g ↔ forall n, trunc' R n f = trunc' R n g := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc']; rw [if_pos le_rfl]
  simp_rw [this, h]

open Filter in
/--
theorem `eq_iff_frequently_trunc'_eq` / 定理 `eq_iff_frequently_trunc'_eq`

English:
theorem eq_iff_frequently_trunc'_eq
  given: {f g : MvPowerSeries σ R}
  proof: by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc']; rw [if_pos hm₁]
  simp [this, hm₂]

中文:
定理 eq_iff_frequently_trunc'_eq
  条件: {f g : MvPowerSeries σ R}
  证明: by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc']; rw [if_pos hm₁]
  simp [this, hm₂]

Depends on / 依赖: MvPowerSeries, atTop_neBot, coeff_trunc, forall_exists_of_atTop, h.forall_exists_of_atTop, if_pos
-/
theorem eq_iff_frequently_trunc'_eq {f g : MvPowerSeries σ R} :
    f = g ↔ existsᶠ m in atTop, trunc' R m f = trunc' R m g := by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc']; rw [if_pos hm₁]
  simp [this, hm₂]

end

end TruncLE

section TruncTotal

variable {n m : Nat} [Finite σ] [CommSemiring R] (p q : MvPowerSeries σ R) {x : σ ->₀ Nat}

/--
Definition of `truncTotal` / `truncTotal` 的定义

English:
definition truncTotal
  signature: {R : Type*} [CommSemiring R] (n : Nat)
  body: truncFinset R (finite_of_degree_lt n).toFinset

中文:
定义 truncTotal
  签名: {R : 类型} [CommSemiring R] (n : 自然数)
  定义体: truncFinset R (finite_of_degree_lt n).toFinset

Depends on / 依赖: finite_of_degree_lt, toFinset, truncFinset
-/
def truncTotal {R : Type*} [CommSemiring R] (n : Nat) : MvPowerSeries σ R ->ₗ[R] MvPolynomial σ R :=
  truncFinset R (finite_of_degree_lt n).toFinset

/--
theorem `coeff_truncTotal` / 定理 `coeff_truncTotal`

English:
theorem coeff_truncTotal
  given: (h : degree x < n)
  proof: coeff_truncFinset_of_mem p (by simpa)

中文:
定理 coeff_truncTotal
  条件: (h : degree x < n)
  证明: coeff_truncFinset_of_mem p (by simpa)

Depends on / 依赖: coeff_truncFinset_of_mem
-/
theorem coeff_truncTotal (h : degree x < n) :
    (truncTotal n p).coeff x = p.coeff x := coeff_truncFinset_of_mem p (by simpa)

/--
theorem `coeff_truncTotal_eq_zero` / 定理 `coeff_truncTotal_eq_zero`

English:
theorem coeff_truncTotal_eq_zero
  given: (h : n <= degree x)
  proof: coeff_truncFinset_eq_zero p (by simpa)

中文:
定理 coeff_truncTotal_eq_zero
  条件: (h : n <= degree x)
  证明: coeff_truncFinset_eq_zero p (by simpa)

Depends on / 依赖: coeff_truncFinset_eq_zero
-/
theorem coeff_truncTotal_eq_zero (h : n <= degree x) :
    (truncTotal n p).coeff x = 0 := coeff_truncFinset_eq_zero p (by simpa)

/--
theorem `coeff_truncTotal_eq_ite` / 定理 `coeff_truncTotal_eq_ite`

English:
theorem coeff_truncTotal_eq_ite
  proof: by
  by_cases h : x.degree < n
  · rw [if_pos h, coeff_truncTotal _ h]
  · rw [if_neg h, coeff_truncTotal_eq_zero _ (not_lt.mp h)]

中文:
定理 coeff_truncTotal_eq_ite
  证明: by
  by_cases h : x.degree < n
  · rw [if_pos h, coeff_truncTotal _ h]
  · rw [if_neg h, coeff_truncTotal_eq_zero _ (not_lt.mp h)]

Depends on / 依赖: coeff_truncTotal, coeff_truncTotal_eq_zero, degree, if_neg, if_pos, not_lt, not_lt.mp, x.degree
-/
theorem coeff_truncTotal_eq_ite :
    (truncTotal n p).coeff x = if x.degree < n then p.coeff x else 0 := by
  by_cases h : x.degree < n
  · rw [if_pos h, coeff_truncTotal _ h]
  · rw [if_neg h, coeff_truncTotal_eq_zero _ (not_lt.mp h)]

/--
theorem `constantCoeff_truncTotal_eq_ite` / 定理 `constantCoeff_truncTotal_eq_ite`

English:
theorem constantCoeff_truncTotal_eq_ite
  proof: by
  simp [MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite]

中文:
定理 constantCoeff_truncTotal_eq_ite
  证明: by
  simp [MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite]

Depends on / 依赖: MvPolynomial, MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite, constantCoeff_eq
-/
theorem constantCoeff_truncTotal_eq_ite :
    (truncTotal n p).constantCoeff = if 0 < n then p.constantCoeff else 0 := by
  simp [MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite]

/--
theorem `truncTotal_eq_sum` / 定理 `truncTotal_eq_sum`

English:
theorem truncTotal_eq_sum
  statement: p.truncTotal n = ∑ i in range n, p.homogeneousComponent i
  proof: by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncTotal_eq_ite]

中文:
定理 truncTotal_eq_sum
  结论: p.truncTotal n = ∑ i in range n, p.homogeneousComponent i
  证明: by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncTotal_eq_ite]

Depends on / 依赖: coeff_homogeneousComponent, coeff_truncTotal_eq_ite
-/
theorem truncTotal_eq_sum : p.truncTotal n = ∑ i in range n, p.homogeneousComponent i := by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncTotal_eq_ite]

/--
lemma `truncTotal_one` / 引理 `truncTotal_one`

English:
lemma truncTotal_one
  given: (h : n != 0)
  statement: truncTotal n (1 : MvPowerSeries σ R) = 1
  proof: truncFinset_one (by revert h; contrapose; simp)

中文:
引理 truncTotal_one
  条件: (h : n != 0)
  结论: truncTotal n (1 : MvPowerSeries σ R) = 1
  证明: truncFinset_one (by revert h; contrapose; simp)

Depends on / 依赖: contrapose, revert, truncFinset_one
-/
lemma truncTotal_one (h : n != 0) : truncTotal n (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_one (by revert h; contrapose; simp)

/--
lemma `coeff_truncTotal_mul_truncTotal_eq_coeff_mul` / 引理 `coeff_truncTotal_mul_truncTotal_eq_coeff_mul`

English:
lemma coeff_truncTotal_mul_truncTotal_eq_coeff_mul
  given: (hx : degree x < n)
  proof: coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  (fun _ _ h => by simp; grind [degree_mono h]) p q (by simpa)

中文:
引理 coeff_truncTotal_mul_truncTotal_eq_coeff_mul
  条件: (hx : degree x < n)
  证明: coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  (fun _ _ h => by simp; grind [degree_mono h]) p q (by simpa)

Depends on / 依赖: coeff_truncFinset_mul_truncFinset_eq_coeff_mul
-/
lemma coeff_truncTotal_mul_truncTotal_eq_coeff_mul (hx : degree x < n) :
    MvPolynomial.coeff x (p.truncTotal n * q.truncTotal n) =
      (coeff x) (p * q) := coeff_truncFinset_mul_truncFinset_eq_coeff_mul
  (fun _ _ h => by simp; grind [degree_mono h]) p q (by simpa)

/--
lemma `coeff_truncTotal_pow` / 引理 `coeff_truncTotal_pow`

English:
lemma coeff_truncTotal_pow
  given: (h : x.degree < n)
  proof: by
  classical
  induction m using Nat.caseStrongRecOn generalizing x with
  | zero => grind [coeff_one, MvPolynomial.coeff_one]
  | ind k ih =>
    simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, MvPolynomial.coeff_mul, coeff_mul]
    congr! 2 with _ _
    · exact ih _ k.le_refl (by grind [mem_anti

中文:
引理 coeff_truncTotal_pow
  条件: (h : x.degree < n)
  证明: by
  classical
  induction m using Nat.caseStrongRecOn generalizing x with
  | zero => grind [coeff_one, MvPolynomial.coeff_one]
  | ind k ih =>
    simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, MvPolynomial.coeff_mul, coeff_mul]
    congr! 2 with _ _
    · exact ih _ k.le_refl (by grind [mem_anti

Depends on / 依赖: IsTopologicalGroup, IsUniformGroup, IsUniformGroup.to_topologicalGroup, MvPolynomial, MvPolynomial.coeff_mul, MvPolynomial.coeff_one, Nat.caseStrongRecOn, Nat.succ_eq_add_one, caseStrongRecOn, classical, coeff_mul, coeff_one, coeff_truncTotal, generalizing, k.le_refl, le_refl, mem_antidiagonal, pow_add, pow_one, simp_rw
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

/--
lemma `truncTotal_pow_eq_truncTotal_truncTotal_pow` / 引理 `truncTotal_pow_eq_truncTotal_truncTotal_pow`

English:
lemma truncTotal_pow_eq_truncTotal_truncTotal_pow
  proof: by
  ext d
  by_cases hd : d.degree < n
  · simp_rw [coeff_truncTotal _ hd]
    exact_mod_cast (coeff_truncTotal_pow _ hd).symm
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

中文:
引理 truncTotal_pow_eq_truncTotal_truncTotal_pow
  证明: by
  ext d
  by_cases hd : d.degree < n
  · simp_rw [coeff_truncTotal _ hd]
    exact_mod_cast (coeff_truncTotal_pow _ hd).symm
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

Depends on / 依赖: coeff_truncTotal, coeff_truncTotal_eq_zero, coeff_truncTotal_pow, d.degree, degree, not_lt, not_lt.mp, simp_rw
-/
lemma truncTotal_pow_eq_truncTotal_truncTotal_pow :
    (p ^ m).truncTotal n = ((p.truncTotal n).toMvPowerSeries ^ m).truncTotal n := by
  ext d
  by_cases hd : d.degree < n
  · simp_rw [coeff_truncTotal _ hd]
    exact_mod_cast (coeff_truncTotal_pow _ hd).symm
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

/--
theorem `totalDegree_truncTotal_lt` / 定理 `totalDegree_truncTotal_lt`

English:
theorem totalDegree_truncTotal_lt
  given: (h : n != 0)
  proof: by
  apply (totalDegree_truncFinset p).trans_lt
  simp [Finset.sup_lt_iff (Nat.lt_of_sub_ne_zero h)]

中文:
定理 totalDegree_truncTotal_lt
  条件: (h : n != 0)
  证明: by
  apply (totalDegree_truncFinset p).trans_lt
  simp [Finset.sup_lt_iff (Nat.lt_of_sub_ne_zero h)]

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.lt_of_sub_ne_zero, lt_of_sub_ne_zero, sup_lt_iff, totalDegree_truncFinset, trans_lt
-/
theorem totalDegree_truncTotal_lt (h : n != 0) :
    (truncTotal n p).totalDegree < n := by
  apply (totalDegree_truncFinset p).trans_lt
  simp [Finset.sup_lt_iff (Nat.lt_of_sub_ne_zero h)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `truncTotal_coe_eq_self_iff` / 定理 `truncTotal_coe_eq_self_iff`

English:
theorem truncTotal_coe_eq_self_iff
  given: (p : MvPolynomial σ R) (h : n != 0)
  proof: by
  rw [truncTotal]; rw [truncFinset_coe_eq_self_iff]; rw [Set.Finite.subset_toFinset]; rw [MvPolynomial.totalDegree]; rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr h)]; rw [Set.subset_def]
  simp [degree, sum]

中文:
定理 truncTotal_coe_eq_self_iff
  条件: (p : MvPolynomial σ R) (h : n != 0)
  证明: by
  rw [truncTotal]; rw [truncFinset_coe_eq_self_iff]; rw [Set.Finite.subset_toFinset]; rw [MvPolynomial.totalDegree]; rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr h)]; rw [Set.subset_def]
  simp [degree, sum]

Depends on / 依赖: Finite, Finset, Finset.sup_lt_iff, MvPolynomial, MvPolynomial.totalDegree, Set.Finite.subset_toFinset, Set.subset_def, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, degree, subset_def, subset_toFinset, sup_lt_iff, totalDegree, truncFinset_coe_eq_self_iff, truncTotal
-/
theorem truncTotal_coe_eq_self_iff (p : MvPolynomial σ R) (h : n != 0) :
    truncTotal n p = p ↔ p.totalDegree < n := by
  rw [truncTotal]; rw [truncFinset_coe_eq_self_iff]; rw [Set.Finite.subset_toFinset]; rw [MvPolynomial.totalDegree]; rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr h)]; rw [Set.subset_def]
  simp [degree, sum]

end TruncTotal

end MvPowerSeries

end
