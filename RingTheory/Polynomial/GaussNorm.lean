/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norm for polynomials

This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.

This is mostly useful when `v` is an absolute value on `R` and `c` is set to be `1`, in which case
the Gauss norm corresponds to the maximum of the absolute values of the coefficients of `p`. When
`R` is a subring of `ℂ` and `v` is the standard absolute value, this is sometimes called the
"height" of `p`.

In the file `Mathlib/RingTheory/PowerSeries/GaussNorm.lean`, the Gauss norm is defined for power
series. This is a generalization of the Gauss norm defined in this file in case `v` is a
nonnegative function with `v 0 = 0` and `c ≥ 0`.

## Main Definitions and Results
* `Polynomial.gaussNorm` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a real number.
* `Polynomial.gaussNorm_coe_powerSeries`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, the Gauss norm of a polynomial is equal to its Gauss norm as a power series.
* `Polynomial.exists_min_eq_gaussNorm`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, there exists a minimal index `i` such that the Gauss norm of `p` at `c` is
  attained at `i`.
* `Polynomial.isNonarchimedean_gaussNorm`: if `v` is a nonnegative nonarchimedean function with
  `v 0 = 0` and `c` is nonnegative, the Gauss norm is nonarchimedean.
* `Polynomial.gaussNorm_mul`: if `v` is a nonarchimedean absolute value, then the Gauss norm is
  multiplicative.
* `Polynomial.gaussNorm_isAbsoluteValue`: if `v` is a nonarchimedean absolute value, then the
  Gauss norm is an absolute value.
-/

@[expose] public section
variable {R F : Type*} [Semiring R] [FunLike F R Real] (v : F) (c : Real)

namespace Polynomial

variable (p : R[X])

/--
Definition of `gaussNorm` / `gaussNorm` 的定义

English:
definition gaussNorm
  signature: : Real
  body: if h : p.support.Nonempty then p.support.sup' h fun i =>
    (v (p.coeff i) * c ^ i) else 0

@[simp]

中文:
定义 gaussNorm
  签名: : 实数
  定义体: if h : p.support.Nonempty then p.support.sup' h fun i =>
    (v (p.coeff i) * c ^ i) else 0

@[simp]

Depends on / 依赖: Nonempty, p.support.Nonempty, p.support.sup, support
-/
def gaussNorm : Real := if h : p.support.Nonempty then p.support.sup' h fun i =>
    (v (p.coeff i) * c ^ i) else 0

@[simp]
/--
lemma `gaussNorm_zero` / 引理 `gaussNorm_zero`

English:
lemma gaussNorm_zero
  statement: gaussNorm v c 0 = 0
  proof: by simp [gaussNorm]

中文:
引理 gaussNorm_zero
  结论: gaussNorm v c 0 = 0
  证明: by simp [gaussNorm]

Depends on / 依赖: gaussNorm
-/
lemma gaussNorm_zero : gaussNorm v c 0 = 0 := by simp [gaussNorm]

variable [ZeroHomClass F R Real]

/--
theorem `exists_eq_gaussNorm` / 定理 `exists_eq_gaussNorm`

English:
theorem exists_eq_gaussNorm
  statement: exists i, p.gaussNorm v c = v (p.coeff i) * c ^ i
  proof: by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNorm, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i => (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

@[simp]

中文:
定理 存在_eq_gaussNorm
  结论: 存在 i, p.gaussNorm v c = v (p.coeff i) * c ^ i
  证明: by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNorm, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i => (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

@[simp]

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, Nonempty, exists_mem_eq_sup, gaussNorm, h_supp, p.coeff, p.support.Nonempty, support
-/
theorem exists_eq_gaussNorm : exists i, p.gaussNorm v c = v (p.coeff i) * c ^ i := by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNorm, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i => (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

@[simp]
/--
lemma `gaussNorm_C` / 引理 `gaussNorm_C`

English:
lemma gaussNorm_C
  given: (r : R)
  statement: (C r).gaussNorm v c = v r
  proof: by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_C, hr]

@[simp]

中文:
引理 gaussNorm_C
  条件: (r : R)
  结论: (C r).gaussNorm v c = v r
  证明: by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_C, hr]

@[simp]

Depends on / 依赖: gaussNorm, support_C
-/
lemma gaussNorm_C (r : R) : (C r).gaussNorm v c = v r := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_C, hr]

@[simp]
/--
theorem `gaussNorm_monomial` / 定理 `gaussNorm_monomial`

English:
theorem gaussNorm_monomial
  given: (n : Nat) (r : R)
  proof: by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_monomial, hr]

中文:
定理 gaussNorm_monomial
  条件: (n : 自然数) (r : R)
  证明: by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_monomial, hr]

Depends on / 依赖: gaussNorm, support_monomial
-/
theorem gaussNorm_monomial (n : Nat) (r : R) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_monomial, hr]

variable {c}

omit [ZeroHomClass F R Real] in
/--
lemma `sup'_nonneg_of_ne_zero` / 引理 `sup'_nonneg_of_ne_zero`

English:
lemma sup'_nonneg_of_ne_zero
  statement: [NonnegHomClass F R Real] {p : R[X]} (h : p.support.Nonempty)
  proof: by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

中文:
引理 上确界'_nonneg_of_ne_zero
  结论: [Nonneg态射类 F R 实数] {p : R[X]} (h : p.support.非空)
  证明: by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity
-/
private lemma sup'_nonneg_of_ne_zero [NonnegHomClass F R Real] {p : R[X]} (h : p.support.Nonempty)
    (hc : 0 <= c) : 0 <= p.support.sup' h fun i => (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

/--
lemma `aux_bdd` / 引理 `aux_bdd`

English:
lemma aux_bdd
  statement: BddAbove {x | exists i, v (p.coeff i) * c ^ i = x}
  proof: by
  let f : p.support -> Real := fun i => v (p.coeff i) * c ^ i.val
  have h_fin : (f '' ⊤ union {0}).Finite := by
apply Set.Finite.union _ Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ]; rw [Set.finite_univ_iff]; rw [← @Finset.coe_sort_coe]
    exact Finite.of_fintype

中文:
引理 aux_bdd
  结论: BddAbove {x | 存在 i, v (p.coeff i) * c ^ i = x}
  证明: by
  let f : p.support -> Real := fun i => v (p.coeff i) * c ^ i.val
  have h_fin : (f '' ⊤ union {0}).Finite := by
apply Set.Finite.union _ Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ]; rw [Set.finite_univ_iff]; rw [← @Finset.coe_sort_coe]
    exact Finite.of_fintype
-/
private lemma aux_bdd : BddAbove {x | exists i, v (p.coeff i) * c ^ i = x} := by
  let f : p.support -> Real := fun i => v (p.coeff i) * c ^ i.val
  have h_fin : (f '' ⊤ union {0}).Finite := by
apply Set.Finite.union _ Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ]; rw [Set.finite_univ_iff]; rw [← @Finset.coe_sort_coe]
    exact Finite.of_fintype p.support
refine Set.Finite.bddAbove Set.Finite.subset h_fin fun _ => ?_
  simp only [Set.top_eq_univ, Set.image_univ, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_range, Subtype.exists, mem_support_iff]
  grind

variable [NonnegHomClass F R Real]

/-- If `v` is a nonnegative function with `v 0 = 0` and `c` is nonnegative, the Gauss norm of a
polynomial is equal to its Gauss norm as a power series. -/
@[simp]
/--
theorem `gaussNorm_coe_powerSeries` / 定理 `gaussNorm_coe_powerSeries`

English:
theorem gaussNorm_coe_powerSeries
  given: (hc : 0 <= c)
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  · simp only [PowerSeries.gaussNorm_eq, coeff_coe, gaussNorm, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n in p.support
      · exact Finset.le_sup' (fun j => v

中文:
定理 gaussNorm_coe_powerSeries
  条件: (hc : 0 <= c)
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  · simp only [PowerSeries.gaussNorm_eq, coeff_coe, gaussNorm, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n in p.support
      · exact Finset.le_sup' (fun j => v

Depends on / 依赖: Finset, Finset.le_sup, PowerSeries, PowerSeries.gaussNorm_eq, _nonneg_of_ne_zero, aux_bdd, ciSup_le, coeff_coe, exists_eq_gaussNorm, gaussNorm, gaussNorm_eq, le_antisymm, le_ciSup, le_sup, ne_eq, not_false_eq_true, p.coeff, p.support, reduceDIte, support
-/
theorem gaussNorm_coe_powerSeries (hc : 0 <= c) :
    (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c := by
  by_cases hp : p = 0
  · simp [hp]
  · simp only [PowerSeries.gaussNorm_eq, coeff_coe, gaussNorm, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n in p.support
      · exact Finset.le_sup' (fun j => v (p.coeff j) * c ^ j) h
      · simp_all [sup'_nonneg_of_ne_zero v (support_nonempty.mpr hp) hc]
    · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
      simp only [gaussNorm, support_nonempty.mpr hp, ↓reduceDIte] at hi
      rw [hi]
      exact le_ciSup (aux_bdd v p) i

/-- If `v x = 0 → x = 0` for all `x : R` and `v` is nonnegative, then the Gauss norm is zero if and
only if the polynomial is zero. -/
@[simp]
/--
theorem `gaussNorm_eq_zero_iff` / 定理 `gaussNorm_eq_zero_iff`

English:
theorem gaussNorm_eq_zero_iff
  given: (h_eq_zero : forall x : R, v x = 0 -> x = 0) (hc : 0 < c)
  proof: by
  rw [← gaussNorm_coe_powerSeries _ _ (le_of_lt hc)]
  convert PowerSeries.gaussNorm_eq_zero_iff v c p (by grind) (by simp) h_eq_zero hc
    (by simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p)
  exact Iff.symm coe_eq_zero_iff

omit [ZeroHomClass F R Real] in

中文:
定理 gaussNorm_eq_zero_iff
  条件: (h_eq_zero : 对任意 x : R, v x = 0 -> x = 0) (hc : 0 < c)
  证明: by
  rw [← gaussNorm_coe_powerSeries _ _ (le_of_lt hc)]
  convert PowerSeries.gaussNorm_eq_zero_iff v c p (by grind) (by simp) h_eq_zero hc
    (by simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p)
  exact Iff.symm coe_eq_zero_iff

omit [ZeroHomClass F R Real] in

Depends on / 依赖: HasGaussNorm, Iff.symm, PowerSeries, PowerSeries.HasGaussNorm, PowerSeries.gaussNorm_eq_zero_iff, aux_bdd, coe_eq_zero_iff, convert, gaussNorm_coe_powerSeries, gaussNorm_eq_zero_iff, h_eq_zero, le_of_lt
-/
theorem gaussNorm_eq_zero_iff (h_eq_zero : forall x : R, v x = 0 -> x = 0) (hc : 0 < c) :
    p.gaussNorm v c = 0 ↔ p = 0 := by
  rw [← gaussNorm_coe_powerSeries _ _ (le_of_lt hc)]
  convert PowerSeries.gaussNorm_eq_zero_iff v c p (by grind) (by simp) h_eq_zero hc
    (by simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p)
  exact Iff.symm coe_eq_zero_iff

omit [ZeroHomClass F R Real] in
/--
theorem `gaussNorm_nonneg` / 定理 `gaussNorm_nonneg`

English:
theorem gaussNorm_nonneg
  given: (hc : 0 <= c)
  statement: 0 <= p.gaussNorm v c
  proof: by
  by_cases hp : p.support.Nonempty <;>
  simp_all [gaussNorm, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]

中文:
定理 gaussNorm_nonneg
  条件: (hc : 0 <= c)
  结论: 0 <= p.gaussNorm v c
  证明: by
  by_cases hp : p.support.Nonempty <;>
  simp_all [gaussNorm, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]

Depends on / 依赖: Finset, Finset.le_sup, Nonempty, _iff, _nonneg_of_ne_zero, gaussNorm, le_sup, p.support.Nonempty, support
-/
theorem gaussNorm_nonneg (hc : 0 <= c) : 0 <= p.gaussNorm v c := by
  by_cases hp : p.support.Nonempty <;>
  simp_all [gaussNorm, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]

/--
lemma `le_gaussNorm` / 引理 `le_gaussNorm`

English:
lemma le_gaussNorm
  given: (hc : 0 <= c) (i : Nat)
  statement: v (p.coeff i) * c ^ i <= p.gaussNorm v c
  proof: by
  rw [← gaussNorm_coe_powerSeries _ _ hc]; rw [← coeff_coe]
  apply PowerSeries.le_gaussNorm
  simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p

@[simp]

中文:
引理 le_gaussNorm
  条件: (hc : 0 <= c) (i : 自然数)
  结论: v (p.coeff i) * c ^ i <= p.gaussNorm v c
  证明: by
  rw [← gaussNorm_coe_powerSeries _ _ hc]; rw [← coeff_coe]
  apply PowerSeries.le_gaussNorm
  simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p

@[simp]

Depends on / 依赖: HasGaussNorm, PowerSeries, PowerSeries.HasGaussNorm, PowerSeries.le_gaussNorm, aux_bdd, coeff_coe, gaussNorm_coe_powerSeries, le_gaussNorm
-/
lemma le_gaussNorm (hc : 0 <= c) (i : Nat) : v (p.coeff i) * c ^ i <= p.gaussNorm v c := by
  rw [← gaussNorm_coe_powerSeries _ _ hc]; rw [← coeff_coe]
  apply PowerSeries.le_gaussNorm
  simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p

@[simp]
/--
lemma `gaussNorm_zero_right` / 引理 `gaussNorm_zero_right`

English:
lemma gaussNorm_zero_right
  statement: p.gaussNorm v 0 = v (p.coeff 0)
  proof: by
  have : (fun i => v (p.coeff i) * 0 ^ i) = fun i => if i = 0 then v (p.coeff 0) else 0 := by
    aesop
  rcases eq_or_ne (p.coeff 0) 0 with _ | hcoeff0
  · simp_all [gaussNorm]
  · apply le_antisymm
    · aesop (add norm (by simp [gaussNorm, Finset.sup'_le_iff]))
    · grind [p.le_gaussNorm v (l

中文:
引理 gaussNorm_zero_right
  结论: p.gaussNorm v 0 = v (p.coeff 0)
  证明: by
  have : (fun i => v (p.coeff i) * 0 ^ i) = fun i => if i = 0 then v (p.coeff 0) else 0 := by
    aesop
  rcases eq_or_ne (p.coeff 0) 0 with _ | hcoeff0
  · simp_all [gaussNorm]
  · apply le_antisymm
    · aesop (add norm (by simp [gaussNorm, Finset.sup'_le_iff]))
    · grind [p.le_gaussNorm v (l

Depends on / 依赖: Finset, Finset.sup, _le_iff, eq_or_ne, gaussNorm, hcoeff0, le_antisymm, le_gaussNorm, le_refl, p.coeff, p.le_gaussNorm
-/
lemma gaussNorm_zero_right : p.gaussNorm v 0 = v (p.coeff 0) := by
  have : (fun i => v (p.coeff i) * 0 ^ i) = fun i => if i = 0 then v (p.coeff 0) else 0 := by
    aesop
  rcases eq_or_ne (p.coeff 0) 0 with _ | hcoeff0
  · simp_all [gaussNorm]
  · apply le_antisymm
    · aesop (add norm (by simp [gaussNorm, Finset.sup'_le_iff]))
    · grind [p.le_gaussNorm v (le_refl 0) 0]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_min_eq_gaussNorm` / 引理 `exists_min_eq_gaussNorm`

English:
lemma exists_min_eq_gaussNorm
  given: (p : R[X]) (hc : 0 <= c)
  proof: by
  have h_nonempty : {i | gaussNorm v c p = v (p.coeff i) * c ^ i}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
    exact ⟨i, Set.mem_ofPred.mpr hi⟩
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, ?_⟩
  intro j hj_lt
  simp only [Nat.lt_find_iff, Set.mem_ofPred_eq] at hj

中文:
引理 存在_min_eq_gaussNorm
  条件: (p : R[X]) (hc : 0 <= c)
  证明: by
  have h_nonempty : {i | gaussNorm v c p = v (p.coeff i) * c ^ i}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
    exact ⟨i, Set.mem_ofPred.mpr hi⟩
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, ?_⟩
  intro j hj_lt
  simp only [Nat.lt_find_iff, Set.mem_ofPred_eq] at hj

Depends on / 依赖: Nat.find, Nat.find_spec, Nat.le_refl, Nat.lt_find_iff, Nonempty, Set.mem_ofPred.mpr, Set.mem_ofPred_eq, a.symm, exists_eq_gaussNorm, find_spec, gaussNorm, h_nonempty, hj_lt, le_gaussNorm, le_refl, lt_find_iff, lt_of_le_of_ne, mem_ofPred, mem_ofPred_eq, p.coeff
-/
lemma exists_min_eq_gaussNorm (p : R[X]) (hc : 0 <= c) :
    exists i, p.gaussNorm v c = v (p.coeff i) * c ^ i ∧
    forall j, j < i -> v (p.coeff j) * c ^ j < p.gaussNorm v c := by
  have h_nonempty : {i | gaussNorm v c p = v (p.coeff i) * c ^ i}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
    exact ⟨i, Set.mem_ofPred.mpr hi⟩
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, ?_⟩
  intro j hj_lt
  simp only [Nat.lt_find_iff, Set.mem_ofPred_eq] at hj_lt
  exact lt_of_le_of_ne (le_gaussNorm v _ hc j) fun a => hj_lt j (Nat.le_refl j) a.symm

/--
theorem `isNonarchimedean_gaussNorm` / 定理 `isNonarchimedean_gaussNorm`

English:
theorem isNonarchimedean_gaussNorm
  given: (hna : IsNonarchimedean v) {c : Real} (hc : 0 <= c)
  proof: by
  intro p q
  rcases eq_or_ne p 0 with hp | _
  · simp [hp]
  rcases eq_or_ne q 0 with hq | _
  · simp [hq]
  rcases eq_or_ne (p + q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg]
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
    Finset.sup'_le_iff]

中文:
定理 isNonarchimedean_gaussNorm
  条件: (hna : IsNonarchimedean v) {c : 实数} (hc : 0 <= c)
  证明: by
  intro p q
  rcases eq_or_ne p 0 with hp | _
  · simp [hp]
  rcases eq_or_ne q 0 with hq | _
  · simp [hq]
  rcases eq_or_ne (p + q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg]
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
    Finset.sup'_le_iff]

Depends on / 依赖: Finset, Finset.sup, _le_iff, coeff_add, eq_or_ne, gaussNorm, gaussNorm_nonneg, ne_eq, not_false_eq_true, p.coeff, q.coeff, reduceDIte, support_nonempty
-/
theorem isNonarchimedean_gaussNorm (hna : IsNonarchimedean v) {c : Real} (hc : 0 <= c) :
    IsNonarchimedean (gaussNorm v c) := by
  intro p q
  rcases eq_or_ne p 0 with hp | _
  · simp [hp]
  rcases eq_or_ne q 0 with hq | _
  · simp [hq]
  rcases eq_or_ne (p + q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg]
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
    Finset.sup'_le_iff]
  intro i _
  calc
  v ((p + q).coeff i) * c ^ i
    <= max (v (p.coeff i)) (v (q.coeff i)) * c ^ i := by
    rw [coeff_add]
    gcongr
    exact hna (p.coeff i) (q.coeff i)
  _ = max (v (p.coeff i) * c ^ i) (v (q.coeff i) * c ^ i) := by
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _)]
  _ <= max (gaussNorm v c p) (gaussNorm v c q) := by
    apply max_le_max <;>
    exact le_gaussNorm v _ hc i

open Finset in
/--
theorem `gaussNorm_mul_le` / 定理 `gaussNorm_mul_le`

English:
theorem gaussNorm_mul_le
  given: [MulHomClass F R Real] (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 <= c)
  proof: by
  rcases eq_or_ne (p * q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg, mul_nonneg]
have h_supp_p : p.support.Nonempty := support_nonempty.mpr left_ne_zero_of_mul hpq
have h_supp_q : q.support.Nonempty := support_nonempty.mpr right_ne_zero_of_mul hpq
  simp only [gaussNorm, support_nonemp

中文:
定理 gaussNorm_mul_le
  条件: [乘法态射类 F R 实数] (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 <= c)
  证明: by
  rcases eq_or_ne (p * q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg, mul_nonneg]
have h_supp_p : p.support.Nonempty := support_nonempty.mpr left_ne_zero_of_mul hpq
have h_supp_q : q.support.Nonempty := support_nonempty.mpr right_ne_zero_of_mul hpq
  simp only [gaussNorm, support_nonemp

Depends on / 依赖: IsNonarchimedean, IsNonarchimedean.finset_image_add_of_none, Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nonempty, _le_iff, coeff_mul, eq_or_ne, finset_image_add_of_none, gaussNorm, gaussNorm_nonneg, h_supp_p, h_supp_q, left_ne_zero_of_mul, mul_nonneg, ne_eq, not_false_eq_true, p.support.Nonempty, q.support.Nonempty, reduceDIte, right_ne_zero_of_mul
-/
theorem gaussNorm_mul_le [MulHomClass F R Real] (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 <= c) :
    (p * q).gaussNorm v c <= p.gaussNorm v c * q.gaussNorm v c := by
  rcases eq_or_ne (p * q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg, mul_nonneg]
have h_supp_p : p.support.Nonempty := support_nonempty.mpr left_ne_zero_of_mul hpq
have h_supp_q : q.support.Nonempty := support_nonempty.mpr right_ne_zero_of_mul hpq
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, h_supp_p,
    h_supp_q, sup'_le_iff, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  intro i _
  obtain ⟨j, _, _⟩ := IsNonarchimedean.finset_image_add_of_nonempty hna _ nonempty_range_add_one
  calc
  v (∑ j in range (i + 1), p.coeff j * q.coeff (i - j)) * c ^ i
  _ <= v (p.coeff j * q.coeff (i - j)) * c ^ i := by gcongr
  _ = (v (p.coeff j) * c ^ j) * (v (q.coeff (i - j)) * c ^ (i - j)) := by
      have : c ^ j * c ^ (i - j) = c ^ i := by simp_all [← pow_add]
      grind
  _ <= (p.support.sup' _ fun i => v (p.coeff i) * c ^ i)
    * q.support.sup' _ fun i => v (q.coeff i) * c ^ i := by
      have hp_le := p.le_gaussNorm v hc j
      have hq_le := q.le_gaussNorm v hc (i - j)
      have := p.gaussNorm_nonneg v hc
      simp_all only [gaussNorm, ↓reduceDIte]
      gcongr

section AbsoluteValue

variable {R : Type*} [Ring R] {v : AbsoluteValue R Real} (hna : IsNonarchimedean v) (hc : 0 < c)

open Finset in
include hna hc in
/--
theorem `mul_gaussNorm_le_gaussNorm_mul` / 定理 `mul_gaussNorm_le_gaussNorm_mul`

English:
theorem mul_gaussNorm_le_gaussNorm_mul
  given: (p q : R[X])
  proof: by
  have hc0 : 0 <= c := le_of_lt hc
  obtain ⟨i, hi_p, hlt_p⟩ := p.exists_min_eq_gaussNorm v hc0
  obtain ⟨j, hj_q, hlt_q⟩ := q.exists_min_eq_gaussNorm v hc0
  -- i and j are the minimal indices where the gauss norms are attained
  wlog hvpq : v (p.coeff i) != 0 ∧ v (q.coeff j) != 0
  · grind [mul

中文:
定理 mul_gaussNorm_le_gaussNorm_mul
  条件: (p q : R[X])
  证明: by
  have hc0 : 0 <= c := le_of_lt hc
  obtain ⟨i, hi_p, hlt_p⟩ := p.exists_min_eq_gaussNorm v hc0
  obtain ⟨j, hj_q, hlt_q⟩ := q.exists_min_eq_gaussNorm v hc0
  -- i and j are the minimal indices where the gauss norms are attained
  wlog hvpq : v (p.coeff i) != 0 ∧ v (q.coeff j) != 0
  · grind [mul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.module, coeAddMonoidHom, coe_injective, module
-/
private theorem mul_gaussNorm_le_gaussNorm_mul (p q : R[X]) :
    p.gaussNorm v c * q.gaussNorm v c <= (p * q).gaussNorm v c := by
  have hc0 : 0 <= c := le_of_lt hc
  obtain ⟨i, hi_p, hlt_p⟩ := p.exists_min_eq_gaussNorm v hc0
  obtain ⟨j, hj_q, hlt_q⟩ := q.exists_min_eq_gaussNorm v hc0
  -- i and j are the minimal indices where the gauss norms are attained
  wlog hvpq : v (p.coeff i) != 0 ∧ v (q.coeff j) != 0
  · grind [mul_mul_mul_comm, gaussNorm_nonneg]
  have := hvpq.1
  have := hvpq.2
apply le_of_eq_of_le _ (p * q).le_gaussNorm v hc0 (i + j)
  -- gaussNorm v c p * gaussNorm v c q is actually equal to v ((p * q).coeff (i + j)) * c ^ (i + j)
  rw [hi_p]; rw [hj_q]; rw [coeff_mul]; rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rw [IsNonarchimedean.apply_sum_eq_of_lt hna (k := i) (by simp) (by simp)]
  /- IsNonarchimedean.apply_sum_eq_of_lt makes the goal almost trivial so we are left to prove
  the hmax hypothesis -/
  · grind
  intro x hx hneq
apply lt_of_mul_lt_mul_right _ pow_nonneg hc0 (i + j)
  have : x + (i + j - x) = i + j := by simp_all
  convert_to! v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) <
    v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j)
  · grind
  · grind
  -- we need to distinguish two cases depending on whether x < i or x > i
  rcases lt_or_gt_of_ne hneq
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ <= v (p.coeff x) * c ^ x * gaussNorm v c q := by
        gcongr
        exact q.le_gaussNorm v hc0 (i + j - x)
    _ = v (p.coeff x) * c ^ x * (v (q.coeff j) * c ^ j) := by
        rw [hj_q]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ <= gaussNorm v c p * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        gcongr
        exact p.le_gaussNorm v hc0 x
    _ = v (p.coeff i) * c ^ i * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        rw [hi_p]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind

include hna hc in
/--
theorem `gaussNorm_mul` / 定理 `gaussNorm_mul`

English:
theorem gaussNorm_mul
  given: (p q : R[X])
  proof: le_antisymm (gaussNorm_mul_le v hna p q (le_of_lt hc))
 mul_gaussNorm_le_gaussNorm_mul hna hc p q

include hna hc in

中文:
定理 gaussNorm_mul
  条件: (p q : R[X])
  证明: le_antisymm (gaussNorm_mul_le v hna p q (le_of_lt hc))
 mul_gaussNorm_le_gaussNorm_mul hna hc p q

include hna hc in

Depends on / 依赖: gaussNorm_mul_le, le_antisymm, le_of_lt, mul_gaussNorm_le_gaussNorm_mul
-/
theorem gaussNorm_mul (p q : R[X]) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c :=
  le_antisymm (gaussNorm_mul_le v hna p q (le_of_lt hc))
 mul_gaussNorm_le_gaussNorm_mul hna hc p q

include hna hc in
/--
theorem `gaussNorm_isAbsoluteValue` / 定理 `gaussNorm_isAbsoluteValue`

English:
theorem gaussNorm_isAbsoluteValue
  proof: p.gaussNorm_nonneg v le_of_lt hc
  abv_eq_zero' := gaussNorm_eq_zero_iff v _ (fun _ hx => (AbsoluteValue.eq_zero v).mp hx) hc
  abv_add' p q := by
    grind [isNonarchimedean_gaussNorm v hna (le_of_lt hc) p q, gaussNorm_nonneg]
  abv_mul' p q := gaussNorm_mul hna hc p q

中文:
定理 gaussNorm_isAbsoluteValue
  证明: p.gaussNorm_nonneg v le_of_lt hc
  abv_eq_zero' := gaussNorm_eq_zero_iff v _ (fun _ hx => (AbsoluteValue.eq_zero v).mp hx) hc
  abv_add' p q := by
    grind [isNonarchimedean_gaussNorm v hna (le_of_lt hc) p q, gaussNorm_nonneg]
  abv_mul' p q := gaussNorm_mul hna hc p q

Depends on / 依赖: gaussNorm_nonneg, le_of_lt, p.gaussNorm_nonneg
-/
theorem gaussNorm_isAbsoluteValue :
    IsAbsoluteValue (gaussNorm v c) where
abv_nonneg' p := p.gaussNorm_nonneg v le_of_lt hc
  abv_eq_zero' := gaussNorm_eq_zero_iff v _ (fun _ hx => (AbsoluteValue.eq_zero v).mp hx) hc
  abv_add' p q := by
    grind [isNonarchimedean_gaussNorm v hna (le_of_lt hc) p q, gaussNorm_nonneg]
  abv_mul' p q := gaussNorm_mul hna hc p q

end AbsoluteValue

end Polynomial

namespace PowerSeries

variable {c} (r : R)

@[simp]
/--
theorem `gaussNorm_C` / 定理 `gaussNorm_C`

English:
theorem gaussNorm_C
  given: [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc : 0 <= c)
  proof: by
  simp [← Polynomial.coe_C, hc]

@[simp]

中文:
定理 gaussNorm_C
  条件: [保零态射类 F R 实数] [Nonneg态射类 F R 实数] (hc : 0 <= c)
  证明: by
  simp [← Polynomial.coe_C, hc]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.coe_C, coe_C
-/
theorem gaussNorm_C [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc : 0 <= c) :
    (C r).gaussNorm v c = v r := by
  simp [← Polynomial.coe_C, hc]

@[simp]
/--
theorem `gaussNorm_monomial` / 定理 `gaussNorm_monomial`

English:
theorem gaussNorm_monomial
  given: [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc : 0 <= c) (n : Nat)
  proof: by
  simp [← Polynomial.coe_monomial, hc]

中文:
定理 gaussNorm_monomial
  条件: [保零态射类 F R 实数] [Nonneg态射类 F R 实数] (hc : 0 <= c) (n : 自然数)
  证明: by
  simp [← Polynomial.coe_monomial, hc]

Depends on / 依赖: Polynomial, Polynomial.coe_monomial, coe_monomial
-/
theorem gaussNorm_monomial [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc : 0 <= c) (n : Nat) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  simp [← Polynomial.coe_monomial, hc]

end PowerSeries
