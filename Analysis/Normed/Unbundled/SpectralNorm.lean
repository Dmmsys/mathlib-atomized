/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.InvariantExtension
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The spectral norm and the norm extension theorem

This file shows that if `K` is a nonarchimedean normed field and `L/K` is an algebraic extension,
then there is a natural extension of the norm on `K` to a `K`-algebra norm on `L`, the so-called
*spectral norm*. The spectral norm of an element of `L` only depends on its minimal polynomial
over `K`, so for `K ⊆ L ⊆ M` two extensions of `K`, the spectral norm on `M` restricts to the
spectral norm on `L`. This work can be used to uniquely extend the `p`-adic norm on `ℚ_[p]` to an
algebraic closure of `ℚ_[p]`, for example.

## Details

We define the spectral value and the spectral norm. We prove the norm extension theorem
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Theorem 3.2.1/2)]
[bosch-guntzer-remmert] : given a nonarchimedean normed field `K` and an algebraic
extension `L/K`, the spectral norm is a power-multiplicative `K`-algebra norm on `L` extending
the norm on `K`. All `K`-algebra automorphisms of `L` are isometries with respect to this norm.
If `L/K` is finite, we get a formula relating the spectral norm on `L` with any other
power-multiplicative norm on `L` extending the norm on `K`.

Moreover, we also prove the unique norm extension theorem: if `K` is a field complete with respect
to a nontrivial nonarchimedean multiplicative norm and `L/K` is an algebraic extension, then the
spectral norm on `L` is a nonarchimedean multiplicative norm, and any power-multiplicative
`K`-algebra norm on `L` coincides with the spectral norm. More over, if `L/K` is finite, then `L`
is a complete space. This result is [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*
(Theorem 3.2.4/2)][bosch-guntzer-remmert].

As a prerequisite, we formalize the proof of [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert].

## Main Definitions

* `spectralValue` : the spectral value of a polynomial in `R[X]`.
* `spectralNorm` : the spectral norm `|y|_sp` is the spectral value of the minimal polynomial
  of `y : L` over `K`.
* `spectralAlgNorm` : the spectral norm is a `K`-algebra norm on `L`.
* `spectralMulAlgNorm` : the spectral norm is a multiplicative `K`-algebra norm on `L`.

## Main Results

* `norm_le_spectralNorm` : if `f` is a power-multiplicative `K`-algebra norm on `L`, then `f` is
  bounded above by `spectralNorm K L`.
* `spectralNorm_eq_of_equiv` : the `K`-algebra automorphisms of `L` are isometries with respect to
  the spectral norm.
* `spectralNorm_eq_iSup_of_finiteDimensional_normal` : if `L/K` is finite and normal, then
  `spectralNorm K L x = iSup (fun (σ : Gal(L/K)) ↦ f (σ x))`.
* `isPowMul_spectralNorm` : the spectral norm is power-multiplicative.
* `isNonarchimedean_spectralNorm` : the spectral norm is nonarchimedean.
* `spectralNorm_extends` : the spectral norm extends the norm on `K`.
* `spectralNorm_unique` : any power-multiplicative `K`-algebra norm on `L` coincides with the
  spectral norm.
* `spectralAlgNorm_mul` : the spectral norm on `L` is multiplicative.
* `spectralNorm.completeSpace` : if `L/K` is finite dimensional, then `L` is a complete space
  with respect to topology induced by the spectral norm.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, spectral value, seminorm, norm, nonarchimedean
-/

@[expose] public section

open Polynomial

open scoped Polynomial


noncomputable section

variable {R : Type*}

section spectralValue

open Nat Real

section Seminormed

variable [SeminormedRing R]

/--
Definition of `spectralValueTerms` / `spectralValueTerms` 的定义

English:
definition spectralValueTerms
  signature: (p : R[X])
  body: fun n : Nat =>
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) else 0

中文:
定义 spectralValueTerms
  签名: (p : R[X])
  定义体: fun n : Nat =>
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) else 0
-/
def spectralValueTerms (p : R[X]) : Nat -> Real := fun n : Nat =>
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) else 0

/--
theorem `spectralValueTerms_of_lt_natDegree` / 定理 `spectralValueTerms_of_lt_natDegree`

English:
theorem spectralValueTerms_of_lt_natDegree
  given: (p : R[X]) {n : Nat} (hn : n < p.natDegree)
  proof: by
  simp [spectralValueTerms, if_pos hn]

中文:
定理 spectralValueTerms_of_lt_natDegree
  条件: (p : R[X]) {n : 自然数} (hn : n < p.natDegree)
  证明: by
  simp [spectralValueTerms, if_pos hn]

Depends on / 依赖: if_pos, spectralValueTerms
-/
theorem spectralValueTerms_of_lt_natDegree (p : R[X]) {n : Nat} (hn : n < p.natDegree) :
    spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) := by
  simp [spectralValueTerms, if_pos hn]

/--
theorem `spectralValueTerms_of_natDegree_le` / 定理 `spectralValueTerms_of_natDegree_le`

English:
theorem spectralValueTerms_of_natDegree_le
  given: (p : R[X]) {n : Nat} (hn : p.natDegree <= n)
  proof: by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

中文:
定理 spectralValueTerms_of_natDegree_le
  条件: (p : R[X]) {n : 自然数} (hn : p.natDegree <= n)
  证明: by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

Depends on / 依赖: Countable, Countable.of_equiv, FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, ShrinkHoms, ShrinkHoms.equivalence, equivalence, homEquiv, homEquiv.symm, if_neg, inverse, inverse.obj, not_lt, not_lt.mpr, ofFullyFaithful, of_equiv, spectralValueTerms
-/
theorem spectralValueTerms_of_natDegree_le (p : R[X]) {n : Nat} (hn : p.natDegree <= n) :
    spectralValueTerms p n = 0 := by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

/--
Definition of `spectralValue` / `spectralValue` 的定义

English:
definition spectralValue
  signature: (p : R[X])
  body: iSup (spectralValueTerms p)

中文:
定义 spectralValue
  签名: (p : R[X])
  定义体: iSup (spectralValueTerms p)

Depends on / 依赖: spectralValueTerms
-/
def spectralValue (p : R[X]) : Real := iSup (spectralValueTerms p)

/--
theorem `spectralValueTerms_finite_range` / 定理 `spectralValueTerms_finite_range`

English:
theorem spectralValueTerms_finite_range
  given: (p : R[X])
  statement: (Set.range (spectralValueTerms p)).Finite
  proof: Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio p.natDegree).image (fun n => ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)))) <| by
      aesop (add simp [Set.range_subset_iff, spectralValueTerms])

中文:
定理 spectralValueTerms_finite_range
  条件: (p : R[X])
  结论: (集合.range (spectralValueTerms p)).有限
  证明: Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio p.natDegree).image (fun n => ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)))) <| by
      aesop (add simp [Set.range_subset_iff, spectralValueTerms])

Depends on / 依赖: Finite, Set.Finite.subset, Set.Finite.union, Set.finite_Iio, Set.finite_singleton, Set.range_subset_iff, finite_Iio, finite_singleton, natDegree, p.coeff, p.natDegree, range_subset_iff, spectralValueTerms, subset
-/
theorem spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerms p)).Finite :=
  Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio p.natDegree).image (fun n => ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)))) <| by
      aesop (add simp [Set.range_subset_iff, spectralValueTerms])

open List in
/--
theorem `spectralValueTerms_bddAbove` / 定理 `spectralValueTerms_bddAbove`

English:
theorem spectralValueTerms_bddAbove
  given: (p : R[X])
  statement: BddAbove (Set.range (spectralValueTerms p))
  proof: (spectralValueTerms_finite_range p).bddAbove

中文:
定理 spectralValueTerms_bddAbove
  条件: (p : R[X])
  结论: BddAbove (集合.range (spectralValueTerms p))
  证明: (spectralValueTerms_finite_range p).bddAbove

Depends on / 依赖: bddAbove, spectralValueTerms_finite_range
-/
theorem spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValueTerms p)) :=
  (spectralValueTerms_finite_range p).bddAbove

/--
theorem `spectralValueTerms_nonneg` / 定理 `spectralValueTerms_nonneg`

English:
theorem spectralValueTerms_nonneg
  given: (p : R[X]) (n : Nat)
  statement: 0 <= spectralValueTerms p n
  proof: by
  simp only [spectralValueTerms]
  split_ifs with h
  · positivity
  · exact le_refl _

中文:
定理 spectralValueTerms_nonneg
  条件: (p : R[X]) (n : 自然数)
  结论: 0 <= spectralValueTerms p n
  证明: by
  simp only [spectralValueTerms]
  split_ifs with h
  · positivity
  · exact le_refl _

Depends on / 依赖: le_refl, spectralValueTerms, split_ifs
-/
theorem spectralValueTerms_nonneg (p : R[X]) (n : Nat) : 0 <= spectralValueTerms p n := by
  simp only [spectralValueTerms]
  split_ifs with h
  · positivity
  · exact le_refl _

/--
theorem `spectralValue_nonneg` / 定理 `spectralValue_nonneg`

English:
theorem spectralValue_nonneg
  given: (p : R[X])
  statement: 0 <= spectralValue p
  proof: iSup_nonneg (spectralValueTerms_nonneg p)

中文:
定理 spectralValue_nonneg
  条件: (p : R[X])
  结论: 0 <= spectralValue p
  证明: iSup_nonneg (spectralValueTerms_nonneg p)

Depends on / 依赖: iSup_nonneg, spectralValueTerms_nonneg
-/
theorem spectralValue_nonneg (p : R[X]) : 0 <= spectralValue p :=
  iSup_nonneg (spectralValueTerms_nonneg p)

variable [Nontrivial R]

/--
theorem `spectralValue_X_sub_C` / 定理 `spectralValue_X_sub_C`

English:
theorem spectralValue_X_sub_C
  given: (r : R)
  statement: spectralValue (X - C r) = ‖r‖
  proof: by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, lt_one_iff, coeff_sub, cast_one, one_div]
  suffices (⨆ n : Nat, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, cast_zero, sub_ze

中文:
定理 spectralValue_X_sub_C
  条件: (r : R)
  结论: spectralValue (X - C r) = ‖r‖
  证明: by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, lt_one_iff, coeff_sub, cast_one, one_div]
  suffices (⨆ n : Nat, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, cast_zero, sub_ze

Depends on / 依赖: cast_one, cast_zero, ciSup_eq_of_forall_le_of_forall_lt_exists_gt, coeff_C_zero, coeff_X_zero, coeff_sub, congr_arg, if_neg, if_pos, if_true, inv_one, lt_one_iff, natDegree_X_sub_C, norm_neg, one_div, rpow_one, spectralValue, spectralValueTerms, split_ifs, sub_zero
-/
theorem spectralValue_X_sub_C (r : R) : spectralValue (X - C r) = ‖r‖ := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, lt_one_iff, coeff_sub, cast_one, one_div]
  suffices (⨆ n : Nat, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, cast_zero, sub_zero, coeff_X_zero, coeff_C_zero, zero_sub,
        norm_neg, inv_one, rpow_one]
    · rw [if_neg hn, if_neg hn]
  · apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun n => ?_)
      (fun _ hx => ⟨0, by simp only [if_true, hx]⟩)
    split_ifs
    · exact le_refl _
    · exact norm_nonneg _

/--
theorem `spectralValue_X_pow` / 定理 `spectralValue_X_pow`

English:
theorem spectralValue_X_pow
  given: (n : Nat)
  statement: spectralValue (X ^ n : R[X]) = 0
  proof: by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert! ciSup_const using 2
  · ext m
    by_cases hmn : m < n
    · rw [if_pos hmn, rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (_root_.ne_of_lt hmn),
        norm_zero, one_div, ne_eq, inv_eq_z

中文:
定理 spectralValue_X_pow
  条件: (n : 自然数)
  结论: spectralValue (X ^ n : R[X]) = 0
  证明: by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert! ciSup_const using 2
  · ext m
    by_cases hmn : m < n
    · rw [if_pos hmn, rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (_root_.ne_of_lt hmn),
        norm_zero, one_div, ne_eq, inv_eq_z

Depends on / 依赖: Eq.refl, Nat.sub_eq_zero_iff_le, _root_, _root_.ne_of_lt, cast_eq_zero, cast_sub, ciSup_const, coeff_X_pow, convert, if_neg, if_pos, infer_instance, inv_eq_zero, le_of_lt, natDegree_X_pow, ne_eq, ne_of_lt, norm_nonneg, norm_zero, not_le_of_gt
-/
theorem spectralValue_X_pow (n : Nat) : spectralValue (X ^ n : R[X]) = 0 := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert! ciSup_const using 2
  · ext m
    by_cases hmn : m < n
    · rw [if_pos hmn, rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (_root_.ne_of_lt hmn),
        norm_zero, one_div, ne_eq, inv_eq_zero, ← cast_sub (le_of_lt hmn), cast_eq_zero,
        Nat.sub_eq_zero_iff_le]
      exact ⟨Eq.refl _, not_le_of_gt hmn⟩
    · rw [if_neg hmn]
  · infer_instance

end Seminormed

section Normed

variable [NormedRing R]

/--
theorem `spectralValue_eq_zero_iff` / 定理 `spectralValue_eq_zero_iff`

English:
theorem spectralValue_eq_zero_iff
  given: [Nontrivial R] {p : R[X]} (hp : p.Monic)
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ spectralValue_X_pow p.natDegree⟩
refine hp.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr
    le_natTrailingDegree hp.ne_zero fun n hn => ?_
  have h0 : spectralValueTerms p n = 0 := by
    apply le_antisymm ((le_ciSup (spectralValueTerms_bddAbove p) n).trans 

中文:
定理 spectralValue_eq_zero_iff
  条件: [非平凡 R] {p : R[X]} (hp : p.Monic)
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ spectralValue_X_pow p.natDegree⟩
refine hp.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr
    le_natTrailingDegree hp.ne_zero fun n hn => ?_
  have h0 : spectralValueTerms p n = 0 := by
    apply le_antisymm ((le_ciSup (spectralValueTerms_bddAbove p) n).trans 

Depends on / 依赖: Real.rpow_eq_zero_iff_of_nonneg, eq_X_pow_iff_natDegree_le_natTrailingDegree, h.le, hp.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr, hp.ne_zero, le_antisymm, le_ciSup, le_natTrailingDegree, natDegree, ne_zero, norm_eq_zero, norm_eq_zero.mp, norm_nonneg, p.natDegree, rpow_eq_zero_iff_of_nonneg, spectralValueTerms, spectralValueTerms_bddAbove, spectralValueTerms_nonneg, spectralValueTerms_of_lt_natDegree, spectralValue_X_pow
-/
theorem spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    spectralValue p = 0 ↔ p = X ^ p.natDegree := by
  refine ⟨fun h => ?_, fun h => h ▸ spectralValue_X_pow p.natDegree⟩
refine hp.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr
    le_natTrailingDegree hp.ne_zero fun n hn => ?_
  have h0 : spectralValueTerms p n = 0 := by
    apply le_antisymm ((le_ciSup (spectralValueTerms_bddAbove p) n).trans h.le)
    exact spectralValueTerms_nonneg _ _
  rw [spectralValueTerms_of_lt_natDegree _ hn]; rw [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)] at h0
  exact norm_eq_zero.mp h0.1

end Normed

section NormedDivisionRing

variable [NormedDivisionRing R]

/--
theorem `spectralValue_le_one_iff` / 定理 `spectralValue_le_one_iff`

English:
theorem spectralValue_le_one_iff
  given: {P : R[X]} (hP : Monic P)
  proof: by
  rw [spectralValue]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · obtain hPn | hPn | hPn := lt_trichotomy P.natDegree n
    · simp [coeff_eq_zero_of_natDegree_lt hPn]
    · rw [← hPn, hP.coeff_natDegree, norm_one]
.trans h · have : spectralValueTerms P n <= 1 := le_ciSup (spectralValueTerms_bddAbove

中文:
定理 spectralValue_le_one_iff
  条件: {P : R[X]} (hP : Monic P)
  证明: by
  rw [spectralValue]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · obtain hPn | hPn | hPn := lt_trichotomy P.natDegree n
    · simp [coeff_eq_zero_of_natDegree_lt hPn]
    · rw [← hPn, hP.coeff_natDegree, norm_one]
.trans h · have : spectralValueTerms P n <= 1 := le_ciSup (spectralValueTerms_bddAbove

Depends on / 依赖: P.natDegree, Real.one_lt_rpow, Real.rpow_le_, ciSup_le, coeff_eq_zero_of_natDegree_lt, coeff_natDegree, contrapose, hP.coeff_natDegree, le_ciSup, lt_trichotomy, natDegree, norm_one, one_lt_rpow, rpow_le_, spectralValue, spectralValueTerms, spectralValueTerms_bddAbove, spectralValueTerms_of_lt_natDegree, split_ifs
-/
theorem spectralValue_le_one_iff {P : R[X]} (hP : Monic P) :
    spectralValue P <= 1 ↔ forall n : Nat, ‖P.coeff n‖ <= 1 := by
  rw [spectralValue]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · obtain hPn | hPn | hPn := lt_trichotomy P.natDegree n
    · simp [coeff_eq_zero_of_natDegree_lt hPn]
    · rw [← hPn, hP.coeff_natDegree, norm_one]
.trans h · have : spectralValueTerms P n <= 1 := le_ciSup (spectralValueTerms_bddAbove P) n
      contrapose! this
      simp only [spectralValueTerms_of_lt_natDegree _ hPn]
      exact Real.one_lt_rpow this (by simp [hPn])
  · apply ciSup_le (fun n => ?_)
    rw [spectralValueTerms]
    split_ifs with hn
    · apply Real.rpow_le_one (norm_nonneg _) (h n)
      rw [one_div_nonneg]; rw [sub_nonneg]; rw [Nat.cast_le]
      exact le_of_lt hn
    · exact zero_le_one

end NormedDivisionRing

end spectralValue

/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert]. -/
section BddBySpectralValue

open Real

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]

open Nat in
/--
theorem `norm_root_le_spectralValue` / 定理 `norm_root_le_spectralValue`

English:
theorem norm_root_le_spectralValue
  statement: {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
  proof: by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt (n : Nat) (hn : n < p.natDegree) : ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real))) ^ (p.natDegree - n) =
          ‖p.coeff n‖ := by
 

中文:
定理 norm_root_le_spectralValue
  结论: {f : 代数范数 K L} (hf_pm : IsPowMul f)
  证明: by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt (n : Nat) (hn : n < p.natDegree) : ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real))) ^ (p.natDegree - n) =
          ‖p.coeff n‖ := by
 

Depends on / 依赖: _root_, _root_.ne_of_gt, cast_sub, h_ge, hn_lt, le_of_lt, mul_comm, natDegree, ne_of_gt, norm_nonneg, one_div, p.coeff, p.natDegree, pow_rpow_inv_natCast, rpow_mul, rpow_natCast, spectralValue_nonneg
-/
theorem norm_root_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) :
    f x <= spectralValue p := by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt (n : Nat) (hn : n < p.natDegree) : ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real))) ^ (p.natDegree - n) =
          ‖p.coeff n‖ := by
        rw [← rpow_natCast]; rw [← rpow_mul (norm_nonneg _)]; rw [mul_comm]; rw [rpow_mul (norm_nonneg _)]; rw [rpow_natCast]; rw [← cast_sub (le_of_lt hn)]; rw [one_div]; rw [pow_rpow_inv_natCast (norm_nonneg _) (_root_.ne_of_gt (tsub_pos_of_lt hn))]
      have h_base : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) < f x := by
        rw [spectralValue]; rw [iSup]; rw [not_le]; rw [Set.Finite.csSup_lt_iff (spectralValueTerms_finite_range p)
          (Set.range_nonempty (spectralValueTerms p))] at h_ge
        have h_rg : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real)) in
          Set.range (spectralValueTerms p) := by use n; simp only [spectralValueTerms, if_pos hn]
        exact h_ge (‖p.coeff n‖₊ ^ (1 / (p.natDegree - n : Real))) h_rg
      rw [← hexp]; rw [← rpow_natCast]; rw [← rpow_natCast]
      gcongr
      exact cast_pos.mpr (tsub_pos_of_lt hn)
    have h_deg : 0 < p.natDegree := natDegree_pos_of_monic_of_aeval_eq_zero hp hx
    have h_lt : f ((Finset.range p.natDegree).sum fun i : Nat => p.coeff i • x ^ i) <
        f (x ^ p.natDegree) := by
      have hn' (n : Nat) (hn : n < p.natDegree) : f (p.coeff n • x ^ n) < f (x ^ p.natDegree) := by
        by_cases hn0 : n = 0
        · rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (succ_le_iff.mpr h_deg),
            ← Nat.sub_zero p.natDegree, ← hn0]
          exact (mul_le_of_le_one_right (norm_nonneg _) hf_pm.map_one_le_one).trans_lt (hn_lt n hn)
        · have : p.natDegree = p.natDegree - n + n := by rw [Nat.sub_add_cancel (le_of_lt hn)]
          rw [map_smul_eq_mul]; rw [hf_pm _ (succ_le_iff.mp (pos_iff_ne_zero.mpr hn0))]; rw [hf_pm _ (succ_le_iff.mpr h_deg)]; rw [this]; rw [pow_add]
          gcongr
          exact hn_lt n hn
      set g := fun i : Nat => p.coeff i • x ^ i
      obtain ⟨m, hm_in, hm⟩ : exists (m : Nat) (_ : 0 < p.natDegree -> m < p.natDegree),
          f ((Finset.range p.natDegree).sum g) <= f (g m) := by
        obtain ⟨m, hm, h⟩ := IsNonarchimedean.finset_image_add (map_zero _) (apply_nonneg _) hf_na g
          (Finset.range p.natDegree)
        rw [Finset.nonempty_range_iff]; rw [← zero_lt_iff]; rw [Finset.mem_range] at hm
        exact ⟨m, hm, h⟩
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))
    have h0 : f 0 != 0 := by
      have h_eq : f 0 = f (x ^ p.natDegree) := by
        rw [← hx]; rw [aeval_eq_sum_range]; rw [Finset.sum_range_succ]; rw [add_comm]; rw [hp.coeff_natDegree]; rw [one_smul]; rw [← max_eq_left_of_lt h_lt]
        exact IsNonarchimedean.add_eq_max_of_ne hf_na (ne_of_gt h_lt)
      exact h_eq ▸ ne_of_gt (lt_of_le_of_lt (apply_nonneg _ _) h_lt)
    exact h0 (map_zero _)

open Multiset

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `max_norm_root_eq_spectralValue` / 定理 `max_norm_root_eq_spectralValue`

English:
theorem max_norm_root_eq_spectralValue
  statement: [DecidableEq L] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
  proof: by
  have h_le : 0 <= ⨆ x : L, ite (x in s) (f x) 0 := by
    apply iSup_nonneg (fun _ => ?_)
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le (fun x => ?_)
    by_cases hx : x in s
    · have hx0 : aeval x p = 0 := aeval_root_of_mapAlg_eq_multiset_prod_X

中文:
定理 max_norm_root_eq_spectralValue
  结论: [DecidableEq L] {f : 代数范数 K L} (hf_pm : IsPowMul f)
  证明: by
  have h_le : 0 <= ⨆ x : L, ite (x in s) (f x) 0 := by
    apply iSup_nonneg (fun _ => ?_)
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le (fun x => ?_)
    by_cases hx : x in s
    · have hx0 : aeval x p = 0 := aeval_root_of_mapAlg_eq_multiset_prod_X

Depends on / 依赖: aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C, apply_nonneg, ciSup_le, exacts, h_le, hf_na, hf_pm, iSup_nonneg, if_neg, if_pos, le_antisymm, le_refl, monic_multisetProd_X_sub_C, monic_of_monic_mapAlg, norm_root_le_spectralValue, spectralValue_nonneg, split_ifs
-/
theorem max_norm_root_eq_spectralValue [DecidableEq L] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (map (fun a : L => X - C a) s).prod) :
    (⨆ x : L, if x in s then f x else 0) = spectralValue p := by
  have h_le : 0 <= ⨆ x : L, ite (x in s) (f x) 0 := by
    apply iSup_nonneg (fun _ => ?_)
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le (fun x => ?_)
    by_cases hx : x in s
    · have hx0 : aeval x p = 0 := aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s hx hp
      rw [if_pos hx]
      exact norm_root_le_spectralValue hf_pm hf_na
        (monic_of_monic_mapAlg (hp ▸ monic_multisetProd_X_sub_C s)) hx0
    · simp only [if_neg hx, spectralValue_nonneg _]
  · apply ciSup_le (fun m => ?_)
    by_cases hm : m < p.natDegree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.natDegree - m : Real) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← rpow_le_rpow_iff (rpow_nonneg (norm_nonneg _) _) h_le h]; rw [← rpow_mul (norm_nonneg _)]; rw [one_div_mul_cancel (ne_of_gt h)]; rw [rpow_one]; rw [← Nat.cast_sub (le_of_lt hm)]; rw [rpow_natCast]
      have hps : card s = p.natDegree := by
        rw [← natDegree_map (algebraMap K L)]; rw [← mapAlg_eq_map]; rw [hp]; rw [natDegree_multiset_prod_X_sub_C_eq_card]
      have hc : ‖p.coeff m‖ = f (((mapAlg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1]; rw [mapAlg_eq_map]; rw [coeff_map]
      rw [hc]; rw [hp]; rw [prod_X_sub_C_coeff s (hps ▸ le_of_lt hm)]
      have h : f ((-1) ^ (card s - m) * s.esymm (card s - m)) = f (s.esymm (card s - m)) := by
        rcases neg_one_pow_eq_or L (card s - m) with h1 | hn1
        · rw [h1, one_mul]
        · rw [hn1, neg_mul, one_mul, map_neg_eq_map]
      rw [h]; rw [esymm]
      obtain ⟨t, ht_card, hts, ht_ge⟩ : exists t : Multiset L, card t = card s - m ∧
          (forall x : L, x in t -> x in s) ∧ f (map prod (powersetCard (card s - m) s)).sum <= f t.prod :=
        hf_na.multiset_powerset_image_add s m
      apply le_trans ht_ge
      have h_pr : f t.prod <= (t.map f).prod := le_prod_of_submultiplicative_of_nonneg f
        (apply_nonneg _) (le_of_eq hf1) (map_mul_le_mul _) t
      apply le_trans h_pr
      have hs_ne : s != 0 :=
        have hpos : 0 < s.toFinset.card := by
          have hs0 : 0 < s.card := hps ▸ hm.pos
          obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hs0
          exact Finset.card_pos.mpr ⟨x, mem_toFinset.mpr hx⟩
        toFinset_nonempty.mp (Finset.card_pos.mp hpos)
      obtain ⟨y, hyx, hy_max⟩ : exists y : L, y in s ∧ forall z : L, z in s -> f z <= f y :=
        exists_max_image f hs_ne
      have : (map f t).prod <= f y ^ (p.natDegree - m) := by
        set g : L -> NNReal := fun x => ⟨f x, apply_nonneg f x⟩
        have h_card : p.natDegree - m = card (t.map g) := by rw [card_map, ht_card, ← hps]
        have hx_le : forall x : NNReal, x in map g t -> x <= g y := by
          intro r hr
          obtain ⟨_, hzt, hzr⟩ := mem_map.mp hr
          exact hzr ▸ hy_max _ (hts _ hzt)
        have : (map g t).prod <= g y ^ (p.natDegree - m) := h_card ▸ prod_le_pow_card _ _ hx_le
        simpa [g, ← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_mk, NNReal.coe_multiset_prod,
          map_map, Function.comp_apply, NNReal.coe_mk] using! this
      have h_bdd : BddAbove (Set.range fun x : L => ite (x in s) (f x) 0) := by
        use f y
        intro r hr
        obtain ⟨z, hz⟩ := Set.mem_range.mpr hr
        simp only at hz
        rw [← hz]
        split_ifs with h
        · exact hy_max _ h
        · exact apply_nonneg _ _
      exact le_trans this (pow_le_pow_left₀ (apply_nonneg _ _)
        (le_trans (by rw [if_pos hyx]) (le_ciSup h_bdd y)) _)
    · simp only [spectralValueTerms, if_neg hm, h_le]

end BddBySpectralValue


section spectralNorm

section NormedField
/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*
(Theorem 3.2.1/2)][bosch-guntzer-remmert]. -/

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

/--
Definition of `spectralNorm` / `spectralNorm` 的定义

English:
definition spectralNorm
  signature: (y : L)
  body: spectralValue (minpoly K y)

中文:
定义 spectralNorm
  签名: (y : L)
  定义体: spectralValue (minpoly K y)

Depends on / 依赖: minpoly, spectralValue
-/
def spectralNorm (y : L) : Real := spectralValue (minpoly K y)

variable {K L}

/--
theorem `spectralNorm.eq_of_tower` / 定理 `spectralNorm.eq_of_tower`

English:
theorem spectralNorm.eq_of_tower
  statement: {E : Type*} [Field E] [Algebra K E] [Algebra E L]
  proof: by
  have hx : minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

中文:
定理 spectralNorm.eq_of_tower
  结论: {E : 类型} [域 E] [代数 K E] [代数 E L]
  证明: by
  have hx : minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

Depends on / 依赖: algebraMap, algebraMap_eq, injective, minpoly, minpoly.algebraMap_eq, spectralNorm
-/
theorem spectralNorm.eq_of_tower {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm K E x = spectralNorm K L (algebraMap E L x) := by
  have hx : minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

variable (E : IntermediateField K L)

/--
theorem `spectralNorm.eq_of_normalClosure'` / 定理 `spectralNorm.eq_of_normalClosure'`

English:
theorem spectralNorm.eq_of_normalClosure'
  given: (x : E)
  proof: by
  simp_rw [← spectralNorm.eq_of_tower]

中文:
定理 spectralNorm.eq_of_normalClosure'
  条件: (x : E)
  证明: by
  simp_rw [← spectralNorm.eq_of_tower]

Depends on / 依赖: eq_of_tower, simp_rw, spectralNorm, spectralNorm.eq_of_tower
-/
theorem spectralNorm.eq_of_normalClosure' (x : E) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
      (algebraMap E (normalClosure K E (AlgebraicClosure E)) x) =
    spectralNorm K L (algebraMap E L x) := by
  simp_rw [← spectralNorm.eq_of_tower]

/--
theorem `spectralNorm.eq_of_normalClosure` / 定理 `spectralNorm.eq_of_normalClosure`

English:
theorem spectralNorm.eq_of_normalClosure
  statement: {E : IntermediateField K L} {x : L} (g : E)
  proof: h_map ▸ spectralNorm.eq_of_normalClosure' E g

中文:
定理 spectralNorm.eq_of_normalClosure
  结论: {E : 中间域 K L} {x : L} (g : E)
  证明: h_map ▸ spectralNorm.eq_of_normalClosure' E g

Depends on / 依赖: eq_of_normalClosure, h_map, spectralNorm, spectralNorm.eq_of_normalClosure
-/
theorem spectralNorm.eq_of_normalClosure {E : IntermediateField K L} {x : L} (g : E)
    (h_map : algebraMap E L g = x) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
        (algebraMap E (normalClosure K E (AlgebraicClosure E)) g) =
      spectralNorm K L x :=
  h_map ▸ spectralNorm.eq_of_normalClosure' E g

variable (y : L)

open Real

/--
theorem `spectralNorm_zero` / 定理 `spectralNorm_zero`

English:
theorem spectralNorm_zero
  statement: spectralNorm K L (0 : L) = 0
  proof: by
  unfold spectralNorm
  rw [minpoly.zero]; rw [← pow_one X]; rw [spectralValue_X_pow 1]

中文:
定理 spectralNorm_zero
  结论: spectralNorm K L (0 : L) = 0
  证明: by
  unfold spectralNorm
  rw [minpoly.zero]; rw [← pow_one X]; rw [spectralValue_X_pow 1]

Depends on / 依赖: minpoly, minpoly.zero, pow_one, spectralNorm, spectralValue_X_pow
-/
theorem spectralNorm_zero : spectralNorm K L (0 : L) = 0 := by
  unfold spectralNorm
  rw [minpoly.zero]; rw [← pow_one X]; rw [spectralValue_X_pow 1]

/--
theorem `spectralNorm_nonneg` / 定理 `spectralNorm_nonneg`

English:
theorem spectralNorm_nonneg
  given: (y : L)
  statement: 0 <= spectralNorm K L y
  proof: le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

中文:
定理 spectralNorm_nonneg
  条件: (y : L)
  结论: 0 <= spectralNorm K L y
  证明: le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

Depends on / 依赖: le_ciSup_of_le, minpoly, spectralValueTerms_bddAbove, spectralValueTerms_nonneg
-/
theorem spectralNorm_nonneg (y : L) : 0 <= spectralNorm K L y :=
  le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

/--
theorem `spectralNorm_zero_lt` / 定理 `spectralNorm_zero_lt`

English:
theorem spectralNorm_zero_lt
  given: {y : L} (hy : y != 0) (hy_alg : IsAlgebraic K y)
  proof: by
  apply lt_of_le_of_ne (spectralNorm_nonneg _)
  rw [spectralNorm]; rw [ne_eq]; rw [eq_comm]; rw [spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  intro h
  apply minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  rw [h]; rw [coeff_X_pow]; rw [if_neg (ne_of_lt (minpoly.natDegree_pos 

中文:
定理 spectralNorm_zero_lt
  条件: {y : L} (hy : y != 0) (hy_alg : 是代数 K y)
  证明: by
  apply lt_of_le_of_ne (spectralNorm_nonneg _)
  rw [spectralNorm]; rw [ne_eq]; rw [eq_comm]; rw [spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  intro h
  apply minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  rw [h]; rw [coeff_X_pow]; rw [if_neg (ne_of_lt (minpoly.natDegree_pos 

Depends on / 依赖: coeff_X_pow, coeff_zero_ne_zero, eq_comm, hy_alg, hy_alg.isIntegral, if_neg, isIntegral, lt_of_le_of_ne, minpoly, minpoly.coeff_zero_ne_zero, minpoly.monic, minpoly.natDegree_pos, natDegree_pos, ne_eq, ne_of_lt, spectralNorm, spectralNorm_nonneg, spectralValue_eq_zero_iff
-/
theorem spectralNorm_zero_lt {y : L} (hy : y != 0) (hy_alg : IsAlgebraic K y) :
    0 < spectralNorm K L y := by
  apply lt_of_le_of_ne (spectralNorm_nonneg _)
  rw [spectralNorm]; rw [ne_eq]; rw [eq_comm]; rw [spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  intro h
  apply minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  rw [h]; rw [coeff_X_pow]; rw [if_neg (ne_of_lt (minpoly.natDegree_pos hy_alg.isIntegral))]

/--
theorem `eq_zero_of_map_spectralNorm_eq_zero` / 定理 `eq_zero_of_map_spectralNorm_eq_zero`

English:
theorem eq_zero_of_map_spectralNorm_eq_zero
  statement: {x : L} (hx : spectralNorm K L x = 0)
  proof: by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

中文:
定理 eq_zero_of_map_spectralNorm_eq_zero
  结论: {x : L} (hx : spectralNorm K L x = 0)
  证明: by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

Depends on / 依赖: hx_alg, ne_of_gt, spectralNorm_zero_lt
-/
theorem eq_zero_of_map_spectralNorm_eq_zero {x : L} (hx : spectralNorm K L x = 0)
    (hx_alg : IsAlgebraic K x) : x = 0 := by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

/--
theorem `norm_le_spectralNorm` / 定理 `norm_le_spectralNorm`

English:
theorem norm_le_spectralNorm
  statement: {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
  proof: norm_root_le_spectralValue hf_pm hf_na (minpoly.monic hx_alg.isIntegral)
    (by rw [minpoly.aeval])

中文:
定理 norm_le_spectralNorm
  结论: {f : 代数范数 K L} (hf_pm : IsPowMul f)
  证明: norm_root_le_spectralValue hf_pm hf_na (minpoly.monic hx_alg.isIntegral)
    (by rw [minpoly.aeval])

Depends on / 依赖: hf_na, hf_pm, hx_alg, hx_alg.isIntegral, isIntegral, minpoly, minpoly.aeval, minpoly.monic, norm_root_le_spectralValue
-/
theorem norm_le_spectralNorm {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {x : L} (hx_alg : IsAlgebraic K x) :
    f x <= spectralNorm K L x :=
  norm_root_le_spectralValue hf_pm hf_na (minpoly.monic hx_alg.isIntegral)
    (by rw [minpoly.aeval])

/--
theorem `spectralNorm_eq_of_equiv` / 定理 `spectralNorm_eq_of_equiv`

English:
theorem spectralNorm_eq_of_equiv
  given: (σ : Gal(L/K)) (x : L)
  proof: by
  simp only [spectralNorm, minpoly.algEquiv_eq]

中文:
定理 spectralNorm_eq_of_equiv
  条件: (σ : Gal(L/K)) (x : L)
  证明: by
  simp only [spectralNorm, minpoly.algEquiv_eq]

Depends on / 依赖: algEquiv_eq, minpoly, minpoly.algEquiv_eq, spectralNorm
-/
theorem spectralNorm_eq_of_equiv (σ : Gal(L/K)) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

-- We first assume that the extension is finite and normal

section FiniteNormal

variable (K L) [h_fin : FiniteDimensional K L] [hn : Normal K L]

/--
theorem `spectralNorm_eq_iSup_of_finiteDimensional_normal` / 定理 `spectralNorm_eq_iSup_of_finiteDimensional_normal`

English:
theorem spectralNorm_eq_iSup_of_finiteDimensional_normal
  proof: by
  classical
  have hf1 : f 1 = 1 := by
    rw [← (algebraMap K L).map_one]; rw [hf_ext]
    simp
  refine le_antisymm ?_ (ciSup_le fun σ =>
    norm_root_le_spectralValue hf_pm hf_na
      (minpoly.monic (hn.isIntegral x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have h

中文:
定理 spectralNorm_eq_iSup_of_finiteDimensional_normal
  证明: by
  classical
  have hf1 : f 1 = 1 := by
    rw [← (algebraMap K L).map_one]; rw [hf_ext]
    simp
  refine le_antisymm ?_ (ciSup_le fun σ =>
    norm_root_le_spectralValue hf_pm hf_na
      (minpoly.monic (hn.isIntegral x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have h

Depends on / 依赖: Splits, aeval_algHom, algebraMap, ciSup_le, classical, h_lc, hf_ext, hf_na, hf_pm, hn.isIntegral, hn.splits, hp_sp, isIntegral, le_antisymm, leadingCoeff, map_one, minpoly, minpoly.aeval_algHom, minpoly.monic, norm_root_le_spectralValue
-/
theorem spectralNorm_eq_iSup_of_finiteDimensional_normal
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    spectralNorm K L x = ⨆ σ : Gal(L/K), f (σ x) := by
  classical
  have hf1 : f 1 = 1 := by
    rw [← (algebraMap K L).map_one]; rw [hf_ext]
    simp
  refine le_antisymm ?_ (ciSup_le fun σ =>
    norm_root_le_spectralValue hf_pm hf_na
      (minpoly.monic (hn.isIntegral x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have hp_sp : Splits ((minpoly K x).map (algebraMap K L)) := hn.splits x
    obtain ⟨s, hs⟩ := splits_iff_exists_multiset.mp hp_sp
    have h_lc : (algebraMap K L) (minpoly K x).leadingCoeff = 1 := by
      rw [minpoly.monic (hn.isIntegral x)]; rw [map_one]
    rw [leadingCoeff_map]; rw [h_lc]; rw [map_one]; rw [one_mul] at hs
    simp only [spectralNorm]
    rw [← max_norm_root_eq_spectralValue hf_pm hf_na hf1 _ _ hs]
    apply ciSup_le
    intro y
    split_ifs with h
    · obtain ⟨σ, hσ⟩ : exists σ : Gal(L/K), σ x = y := minpoly.exists_algEquiv_of_root'
        (Algebra.IsAlgebraic.isAlgebraic x) (aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s h hs)
      rw [← hσ]
      apply Finite.le_ciSup _ σ
    · exact iSup_nonneg fun σ => apply_nonneg _ _

open IsUltrametricDist

/--
theorem `spectralNorm_eq_invariantExtension` / 定理 `spectralNorm_eq_invariantExtension`

English:
theorem spectralNorm_eq_invariantExtension
  given: [hu : IsUltrametricDist K]
  proof: by
  ext x
  have hna := hu.isNonarchimedean_norm
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
    with hf
  have hf_pow : IsPowMul f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have

中文:
定理 spectralNorm_eq_invariantExtension
  条件: [hu : 是UltrametricDist K]
  证明: by
  ext x
  have hna := hu.isNonarchimedean_norm
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
    with hf
  have hf_pow : IsPowMul f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, IsNonarchimedean, IsPowMul, algebraMap, choose_spec, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional, h_fin, hf_ext, hf_na, hf_pow, hu.isNonarchimedean_norm, isNonarchimedean_norm
-/
theorem spectralNorm_eq_invariantExtension [hu : IsUltrametricDist K] :
    spectralNorm K L = invariantExtension K L := by
  ext x
  have hna := hu.isNonarchimedean_norm
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
    with hf
  have hf_pow : IsPowMul f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖ := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.1
  have hf_na : IsNonarchimedean f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.2
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pow hf_na hf_ext]
  simp only [invariantExtension_apply, algNormOfAlgEquiv_apply, hf]

/- Note that the main results below are reproved without the finite dimensionality and normality
  assumptions later on in this file. -/

/--
theorem `isPowMul_spectralNorm_of_finiteDimensional_normal` / 定理 `isPowMul_spectralNorm_of_finiteDimensional_normal`

English:
theorem isPowMul_spectralNorm_of_finiteDimensional_normal
  given: [IsUltrametricDist K]
  proof: by
  rw [spectralNorm_eq_invariantExtension K L]
  exact isPowMul_invariantExtension K L

中文:
定理 isPowMul_spectralNorm_of_finiteDimensional_normal
  条件: [是UltrametricDist K]
  证明: by
  rw [spectralNorm_eq_invariantExtension K L]
  exact isPowMul_invariantExtension K L

Depends on / 依赖: isPowMul_invariantExtension, spectralNorm_eq_invariantExtension
-/
theorem isPowMul_spectralNorm_of_finiteDimensional_normal [IsUltrametricDist K] :
    IsPowMul (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension K L]
  exact isPowMul_invariantExtension K L

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `spectralAlgNorm_of_finiteDimensional_normal` / `spectralAlgNorm_of_finiteDimensional_normal` 的定义

English:
definition spectralAlgNorm_of_finiteDimensional_normal
  signature: [IsUltrametricDist K]
  body: spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_invariantExtension K L, map_zero]
  add_le' := by rw [spectralNorm_eq_invariantExtension]; exact map_add_le_add _
  neg' := by rw [spectralNorm_eq_invariantExtension]; exact map_neg_eq_map _
  mul_le' := by
    simp only [spectralNorm_eq_invaria

中文:
定义 spectralAlgNorm_of_finiteDimensional_normal
  签名: [是UltrametricDist K]
  定义体: spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_invariantExtension K L, map_zero]
  add_le' := by rw [spectralNorm_eq_invariantExtension]; exact map_add_le_add _
  neg' := by rw [spectralNorm_eq_invariantExtension]; exact map_neg_eq_map _
  mul_le' := by
    simp only [spectralNorm_eq_invaria

Depends on / 依赖: spectralNorm
-/
def spectralAlgNorm_of_finiteDimensional_normal [IsUltrametricDist K] : AlgebraNorm K L where
  toFun := spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_invariantExtension K L, map_zero]
  add_le' := by rw [spectralNorm_eq_invariantExtension]; exact map_add_le_add _
  neg' := by rw [spectralNorm_eq_invariantExtension]; exact map_neg_eq_map _
  mul_le' := by
    simp only [spectralNorm_eq_invariantExtension]
    exact map_mul_le_mul (invariantExtension K L)
  smul' := by
    simp [spectralNorm_eq_invariantExtension, AlgebraNormClass.map_smul_eq_mul _]
  eq_zero_of_map_eq_zero' x := by
    simp only [spectralNorm_eq_invariantExtension]
    exact eq_zero_of_map_eq_zero _

/--
theorem `spectralAlgNorm_of_finiteDimensional_normal_def` / 定理 `spectralAlgNorm_of_finiteDimensional_normal_def`

English:
theorem spectralAlgNorm_of_finiteDimensional_normal_def
  given: [IsUltrametricDist K] (x : L)
  proof: rfl

中文:
定理 spectralAlgNorm_of_finiteDimensional_normal_def
  条件: [是UltrametricDist K] (x : L)
  证明: rfl
-/
theorem spectralAlgNorm_of_finiteDimensional_normal_def [IsUltrametricDist K] (x : L) :
    spectralAlgNorm_of_finiteDimensional_normal K L x = spectralNorm K L x := rfl

/--
theorem `isNonarchimedean_spectralNorm_of_finiteDimensional_normal` / 定理 `isNonarchimedean_spectralNorm_of_finiteDimensional_normal`

English:
theorem isNonarchimedean_spectralNorm_of_finiteDimensional_normal
  proof: by
  rw [spectralNorm_eq_invariantExtension]
  exact isNonarchimedean_invariantExtension K L

中文:
定理 isNonarchimedean_spectralNorm_of_finiteDimensional_normal
  证明: by
  rw [spectralNorm_eq_invariantExtension]
  exact isNonarchimedean_invariantExtension K L

Depends on / 依赖: isNonarchimedean_invariantExtension, spectralNorm_eq_invariantExtension
-/
theorem isNonarchimedean_spectralNorm_of_finiteDimensional_normal
    [IsUltrametricDist K] : IsNonarchimedean (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension]
  exact isNonarchimedean_invariantExtension K L

/--
theorem `spectralNorm_extends_of_finiteDimensional` / 定理 `spectralNorm_extends_of_finiteDimensional`

English:
theorem spectralNorm_extends_of_finiteDimensional
  given: [IsUltrametricDist K] (x : K)
  proof: by
  rw [spectralNorm_eq_invariantExtension]; rw [invariantExtension_extends K L x]

中文:
定理 spectralNorm_extends_of_finiteDimensional
  条件: [是UltrametricDist K] (x : K)
  证明: by
  rw [spectralNorm_eq_invariantExtension]; rw [invariantExtension_extends K L x]

Depends on / 依赖: invariantExtension_extends, spectralNorm_eq_invariantExtension
-/
theorem spectralNorm_extends_of_finiteDimensional [IsUltrametricDist K] (x : K) :
    spectralNorm K L (algebraMap K L x) = ‖x‖ := by
  rw [spectralNorm_eq_invariantExtension]; rw [invariantExtension_extends K L x]

/--
theorem `spectralNorm_unique_of_finiteDimensional_normal` / 定理 `spectralNorm_unique_of_finiteDimensional_normal`

English:
theorem spectralNorm_unique_of_finiteDimensional_normal
  statement: {f : AlgebraNorm K L}
  proof: by
  have h_sup : (⨆ σ : Gal(L/K), f (σ x)) = f x := by
    rw [← @ciSup_const _ Gal(L/K) _ _ (f x)]
    exact iSup_congr fun σ => by rw [hf_iso σ x]
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pm hf_na hf_ext]; rw [h_sup]

中文:
定理 spectralNorm_unique_of_finiteDimensional_normal
  结论: {f : 代数范数 K L}
  证明: by
  have h_sup : (⨆ σ : Gal(L/K), f (σ x)) = f x := by
    rw [← @ciSup_const _ Gal(L/K) _ _ (f x)]
    exact iSup_congr fun σ => by rw [hf_iso σ x]
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pm hf_na hf_ext]; rw [h_sup]

Depends on / 依赖: ciSup_const, h_sup, hf_ext, hf_iso, hf_na, hf_pm, iSup_congr, spectralNorm_eq_iSup_of_finiteDimensional_normal
-/
theorem spectralNorm_unique_of_finiteDimensional_normal {f : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖₊)
    (hf_iso : forall (σ : Gal(L/K)) (x : L), f x = f (σ x)) (x : L) : f x = spectralNorm K L x := by
  have h_sup : (⨆ σ : Gal(L/K), f (σ x)) = f x := by
    rw [← @ciSup_const _ Gal(L/K) _ _ (f x)]
    exact iSup_congr fun σ => by rw [hf_iso σ x]
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pm hf_na hf_ext]; rw [h_sup]

end FiniteNormal

-- Now we let `L/K` be any algebraic extension.

open scoped IntermediateField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeminormClass (AlgebraNorm K ↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) K
  body: AlgebraNormClass.toSeminormClass

中文:
实例 :
  签名: 半范数类 (代数范数 K ↥(normalClosure K (↥E) (代数闭包 ↥E))) K
  定义体: AlgebraNormClass.toSeminormClass

Depends on / 依赖: AlgebraNormClass, AlgebraNormClass.toSeminormClass, toSeminormClass
-/
instance : SeminormClass (AlgebraNorm K ↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) K
    ↥(normalClosure K (↥E) (AlgebraicClosure ↥E)) := AlgebraNormClass.toSeminormClass

/--
theorem `spectralNorm_extends` / 定理 `spectralNorm_extends`

English:
theorem spectralNorm_extends
  given: (k : K)
  statement: spectralNorm K L (algebraMap K L k) = ‖k‖
  proof: by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_X_sub_C k

中文:
定理 spectralNorm_extends
  条件: (k : K)
  结论: spectralNorm K L (algebraMap K L k) = ‖k‖
  证明: by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_X_sub_C k

Depends on / 依赖: algebraMap, eq_X_sub_C_of_algebraMap_inj, injective, minpoly, minpoly.eq_X_sub_C_of_algebraMap_inj, simp_rw, spectralNorm, spectralValue_X_sub_C
-/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ := by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_X_sub_C k

/--
theorem `spectralNorm_one` / 定理 `spectralNorm_one`

English:
theorem spectralNorm_one
  statement: spectralNorm K L 1 = 1
  proof: by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1]; rw [spectralNorm_extends]; rw [norm_one]

中文:
定理 spectralNorm_one
  结论: spectralNorm K L 1 = 1
  证明: by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1]; rw [spectralNorm_extends]; rw [norm_one]

Depends on / 依赖: algebraMap, map_one, norm_one, spectralNorm_extends
-/
theorem spectralNorm_one : spectralNorm K L 1 = 1 := by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1]; rw [spectralNorm_extends]; rw [norm_one]

variable [IsUltrametricDist K]

/--
theorem `spectralNorm_neg` / 定理 `spectralNorm_neg`

English:
theorem spectralNorm_neg
  given: {y : L} (hy : IsAlgebraic K y)
  proof: by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.Adj

中文:
定理 spectralNorm_neg
  条件: {y : L} (hy : 是代数 K y)
  证明: by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.Adj

Depends on / 依赖: AdjoinSimple, FiniteDimensional, IntermediateField, IntermediateField.AdjoinSimple.algebraMap_gen, IntermediateField.AdjoinSimple.gen, IntermediateField.adjoin.finiteDimensional, adjoin, algebraMap, algebraMap_gen, eq_of_normalClosure, finiteDimensional, h_finiteDimensional_E, hy.isIntegral, isIntegral, map_neg, map_neg_eq_map, spectralAlgNorm_of_finiteDimensional_normal_def, spectralNorm, spectralNorm.eq_of_normalClosure
-/
theorem spectralNorm_neg {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (-y) = spectralNorm K L y := by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y)]; rw [hy]; rw [← spectralNorm.eq_of_normalClosure (-g) hy]; rw [map_neg]; rw [← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_neg_eq_map _ _

/--
theorem `spectralNorm_smul` / 定理 `spectralNorm_smul`

English:
theorem spectralNorm_smul
  given: (k : K) {y : L} (hy : IsAlgebraic K y)
  proof: by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (Algeb

中文:
定理 spectralNorm_smul
  条件: (k : K) {y : L} (hy : 是代数 K y)
  证明: by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (Algeb

Depends on / 依赖: AdjoinSimple, Algebra, Algebra.algebraMap_eq_smul_one, AlgebraicClosure, FiniteDimensional, IntermediateField, IntermediateField.AdjoinSimple.gen, IntermediateField.adjoin.finiteDimensional, adjoin, algebraMap, algebraMap_eq_smul_one, finiteDimensional, h_finiteDimensional_E, hy.isIntegral, isIntegral, normalClosure, smul_assoc, spectralNorm, spectralNorm.e
-/
theorem spectralNorm_smul (k : K) {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (k • y) = ‖k‖₊ * spectralNorm K L y := by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) (k • g) =
      k • algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) g := by
    rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_assoc]
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y)]; rw [hgy]; rw [← spectralNorm.eq_of_normalClosure (k • g) rfl]; rw [h]
  rw [← spectralAlgNorm_of_finiteDimensional_normal_def]
  apply map_smul_eq_mul

/--
theorem `spectralNorm_mul` / 定理 `spectralNorm_mul`

English:
theorem spectralNorm_mul
  given: {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y)
  proof: by
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, 

中文:
定理 spectralNorm_mul
  条件: {x y : L} (hx : 是代数 K x) (hy : 是代数 K y)
  证明: by
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, 

Depends on / 依赖: AdjoinPair, FiniteDimensional, IntermediateField, IntermediateField.AdjoinPair.algebraMap_gen, IntermediateField.AdjoinPair.gen, IntermediateField.finiteDimensional_adjoin_pair, algebraMap, eq_of_norm, eq_of_normalClosure, finiteDimensional_adjoin_pair, h_finiteDimensional_E, hx.isIntegral, hy.isIntegral, isIntegral, spectralNorm, spectralNorm.eq_of_norm, spectralNorm.eq_of_normalClosure
-/
theorem spectralNorm_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) <= spectralNorm K L x * spectralNorm K L y := by
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, y⟯ L) (gx * gy) := rfl
  rw [hxy]; rw [← spectralNorm.eq_of_normalClosure (gx * gy) hxy]; rw [← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y)]; rw [← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y)]; rw [map_mul]; rw [← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_mul_le_mul _ _ _

section IsAlgebraic

variable [h_alg : Algebra.IsAlgebraic K L]

/--
theorem `isPowMul_spectralNorm` / 定理 `isPowMul_spectralNorm`

English:
theorem isPowMul_spectralNorm
  statement: IsPowMul (spectralNorm K L)
  proof: by
  intro x n hn
  set E := K⟮x⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  rw [← spectralNorm.

中文:
定理 isPowMul_spectralNorm
  结论: IsPowMul (spectralNorm K L)
  证明: by
  intro x n hn
  set E := K⟮x⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  rw [← spectralNorm.

Depends on / 依赖: AdjoinSimple, FiniteDimensional, IntermediateField, IntermediateField.AdjoinSimple.algebraMap_gen, IntermediateField.AdjoinSimple.gen, IntermediateField.adjoin.finiteDimensional, adjoin, algebraMap, algebraMap_gen, eq_of_normalClosure, finiteDimensional, h_alg, h_alg.isAlgebraic, h_finiteDimensional_E, h_map, isAlgebraic, isIntegral, isPowMul_spectralNorm_of_finiteDimensional_normal, map_pow, spectralNorm
-/
theorem isPowMul_spectralNorm : IsPowMul (spectralNorm K L) := by
  intro x n hn
  set E := K⟮x⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  rw [← spectralNorm.eq_of_normalClosure _ (IntermediateField.AdjoinSimple.algebraMap_gen K x)]; rw [← spectralNorm.eq_of_normalClosure (g ^ n) h_map]; rw [map_pow]; rw [← hg]
  exact isPowMul_spectralNorm_of_finiteDimensional_normal _ _
    ((algebraMap ↥K⟮x⟯ ↥(normalClosure K (↥K⟮x⟯) (AlgebraicClosure ↥K⟮x⟯))) g) hn

/--
theorem `isNonarchimedean_spectralNorm` / 定理 `isNonarchimedean_spectralNorm`

English:
theorem isNonarchimedean_spectralNorm
  statement: IsNonarchimedean (spectralNorm K L)
  proof: by
  intro x y
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.Adj

中文:
定理 isNonarchimedean_spectralNorm
  结论: IsNonarchimedean (spectralNorm K L)
  证明: by
  intro x y
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.Adj

Depends on / 依赖: AdjoinPair, FiniteDimensional, IntermediateField, IntermediateField.AdjoinPair.algebr, IntermediateField.AdjoinPair.gen, IntermediateField.finiteDimensional_adjoin_pair, algebr, algebraMap, eq_of_normalClosure, finiteDimensional_adjoin_pair, h_alg, h_alg.isAlgebraic, h_finiteDimensional_E, isAlgebraic, isIntegral, spectralNorm, spectralNorm.eq_of_normalClosure
-/
theorem isNonarchimedean_spectralNorm : IsNonarchimedean (spectralNorm K L) := by
  intro x y
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x + y = (algebraMap K⟮x, y⟯ L) (gx + gy) := rfl
  rw [hxy]; rw [← spectralNorm.eq_of_normalClosure (gx + gy) hxy]; rw [← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y)]; rw [← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y)]; rw [_root_.map_add]
  apply isNonarchimedean_spectralNorm_of_finiteDimensional_normal

set_option linter.style.whitespace false in -- manual alignment is not recognised
variable (K L) in
/--
Definition of `spectralAlgNorm` / `spectralAlgNorm` 的定义

English:
definition spectralAlgNorm
  signature: : AlgebraNorm K L where
  body: spectralNorm K L
  map_zero' := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg isNonarchimedean_spectralNorm
  mul_le' x y := spectralNorm_mul (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x := spectralNorm_smul k (h_alg.isAlgebraic x)
  neg' x := spectralNorm

中文:
定义 spectralAlgNorm
  签名: : 代数范数 K L where
  定义体: spectralNorm K L
  map_zero' := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg isNonarchimedean_spectralNorm
  mul_le' x y := spectralNorm_mul (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x := spectralNorm_smul k (h_alg.isAlgebraic x)
  neg' x := spectralNorm

Depends on / 依赖: spectralNorm
-/
def spectralAlgNorm : AlgebraNorm K L where
  toFun := spectralNorm K L
  map_zero' := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg isNonarchimedean_spectralNorm
  mul_le' x y := spectralNorm_mul (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x := spectralNorm_smul k (h_alg.isAlgebraic x)
  neg' x := spectralNorm_neg (h_alg.isAlgebraic x)
  eq_zero_of_map_eq_zero' x hx := eq_zero_of_map_spectralNorm_eq_zero hx (h_alg.isAlgebraic x)

/--
theorem `spectralAlgNorm_def` / 定理 `spectralAlgNorm_def`

English:
theorem spectralAlgNorm_def
  given: (x : L)
  statement: spectralAlgNorm K L x = spectralNorm K L x
  proof: rfl

中文:
定理 spectralAlgNorm_def
  条件: (x : L)
  结论: spectralAlgNorm K L x = spectralNorm K L x
  证明: rfl
-/
theorem spectralAlgNorm_def (x : L) : spectralAlgNorm K L x = spectralNorm K L x := rfl

/--
theorem `spectralAlgNorm_extends` / 定理 `spectralAlgNorm_extends`

English:
theorem spectralAlgNorm_extends
  given: (k : K)
  statement: spectralAlgNorm K L (algebraMap K L k) = ‖k‖
  proof: spectralNorm_extends k

中文:
定理 spectralAlgNorm_extends
  条件: (k : K)
  结论: spectralAlgNorm K L (algebraMap K L k) = ‖k‖
  证明: spectralNorm_extends k

Depends on / 依赖: spectralNorm_extends
-/
theorem spectralAlgNorm_extends (k : K) : spectralAlgNorm K L (algebraMap K L k) = ‖k‖ :=
  spectralNorm_extends k

/--
theorem `spectralAlgNorm_one` / 定理 `spectralAlgNorm_one`

English:
theorem spectralAlgNorm_one
  statement: spectralAlgNorm K L (1 : L) = 1
  proof: spectralNorm_one

中文:
定理 spectralAlgNorm_one
  结论: spectralAlgNorm K L (1 : L) = 1
  证明: spectralNorm_one

Depends on / 依赖: spectralNorm_one
-/
theorem spectralAlgNorm_one : spectralAlgNorm K L (1 : L) = 1 := spectralNorm_one

/--
theorem `spectralAlgNorm_isPowMul` / 定理 `spectralAlgNorm_isPowMul`

English:
theorem spectralAlgNorm_isPowMul
  statement: IsPowMul (spectralAlgNorm K L)
  proof: isPowMul_spectralNorm

中文:
定理 spectralAlgNorm_isPowMul
  结论: IsPowMul (spectralAlgNorm K L)
  证明: isPowMul_spectralNorm

Depends on / 依赖: isPowMul_spectralNorm
-/
theorem spectralAlgNorm_isPowMul : IsPowMul (spectralAlgNorm K L) := isPowMul_spectralNorm

end IsAlgebraic

end NormedField

section NontriviallyNormedField

open IntermediateField

universe u v

variable {K : Type u} [NontriviallyNormedField K] {L : Type v} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K]

set_option allowUnsafeReducibility true

/--
theorem `spectralNorm_unique` / 定理 `spectralNorm_unique`

English:
theorem spectralNorm_unique
  given: [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
  proof: by
  apply eq_of_powMul_faithful f hf_pm _ spectralAlgNorm_isPowMul
  intro x
  let E : Type v := id K⟮x⟯
let : Field E := id show Field K⟮x⟯ by infer_instance
let : Module K E := id show Module K K⟮x⟯ by infer_instance
  let id1 : K⟮x⟯ ->ₗ[K] E := LinearMap.id
  let id2 : E ->ₗ[K] K⟮x⟯ := LinearMap

中文:
定理 spectralNorm_unique
  条件: [完备空间 K] {f : 代数范数 K L} (hf_pm : IsPowMul f)
  证明: by
  apply eq_of_powMul_faithful f hf_pm _ spectralAlgNorm_isPowMul
  intro x
  let E : Type v := id K⟮x⟯
let : Field E := id show Field K⟮x⟯ by infer_instance
let : Module K E := id show Module K K⟮x⟯ by infer_instance
  let id1 : K⟮x⟯ ->ₗ[K] E := LinearMap.id
  let id2 : E ->ₗ[K] K⟮x⟯ := LinearMap

Depends on / 依赖: LinearMap, LinearMap.id, Module, RingNorm, ZeroMemClass, ZeroMemClass.coe_zero, add_le, coe_zero, eq_of_powMul_faithful, hf_pm, hs_norm, infer_instance, map_, map_zero, spectralAlgNorm_def, spectralAlgNorm_isPowMul, spectralNorm, spectralNorm_zero
-/
theorem spectralNorm_unique [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f) :
    f = spectralAlgNorm K L := by
  apply eq_of_powMul_faithful f hf_pm _ spectralAlgNorm_isPowMul
  intro x
  let E : Type v := id K⟮x⟯
let : Field E := id show Field K⟮x⟯ by infer_instance
let : Module K E := id show Module K K⟮x⟯ by infer_instance
  let id1 : K⟮x⟯ ->ₗ[K] E := LinearMap.id
  let id2 : E ->ₗ[K] K⟮x⟯ := LinearMap.id
  set hs_norm : RingNorm E :=
    { toFun y := spectralNorm K L (id2 y : L)
      map_zero' := by simp [map_zero, spectralNorm_zero, ZeroMemClass.coe_zero]
      add_le' a b := by
        simp only [← spectralAlgNorm_def]
        exact map_add_le_add _ _ _
      neg' a := by simp [map_neg, NegMemClass.coe_neg, ← spectralAlgNorm_def, map_neg_eq_map]
      mul_le' a b := by
        simp only [← spectralAlgNorm_def]
        exact map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, ← spectralAlgNorm_def,
          map_eq_zero_iff_eq_zero, ZeroMemClass.coe_eq_zero] using! ha }
  let n1 : NormedRing E := RingNorm.toNormedRing hs_norm
  let N1 : NormedSpace K E :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e_1 e_ := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (spectralAlgNorm K L (id2 (k • y) : L) : Real) <=
          ‖k‖ * spectralAlgNorm K L (id2 y : L)
        rw [map_smul]; rw [IntermediateField.coe_smul]; rw [map_smul_eq_mul] }
  set hf_norm : RingNorm K⟮x⟯ :=
    { toFun y := f ((algebraMap K⟮x⟯ L) y)
      map_zero' := map_zero _
      add_le' a b := map_add_le_add _ _ _
      neg' y := by simp [(algebraMap K⟮x⟯ L).map_neg y]
      mul_le' a b := map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [map_eq_zero_iff_eq_zero, map_eq_zero] using! ha }
  let n2 : NormedRing K⟮x⟯ := RingNorm.toNormedRing hf_norm
  let N2 : NormedSpace K K⟮x⟯ :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e1 e2 := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (f ((algebraMap K⟮x⟯ L) (k • y)) : Real) <= ‖k‖ * f (algebraMap K⟮x⟯ L y)
        have : (algebraMap (↥K⟮x⟯) L) (k • y) = k • algebraMap (↥K⟮x⟯) L y := by
          simp [IntermediateField.algebraMap_apply]
        rw [this]; rw [map_smul_eq_mul] }
  have hKx_fin : FiniteDimensional K ↥K⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : FiniteDimensional K E := hKx_fin
  set Id1 : K⟮x⟯ ->L[K] E := ⟨id1, id1.continuous_of_finiteDimensional⟩
  set Id2 : E ->L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finiteDimensional⟩
  obtain ⟨C1, hC1_pos, hC1⟩ : exists C1 : Real, 0 < C1 ∧ forall y : K⟮x⟯, ‖id1 y‖ <= C1 * ‖y‖ :=
    Id1.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ : exists C2 : Real, 0 < C2 ∧ forall y : E, ‖id2 y‖ <= C2 * ‖y‖ :=
    Id2.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y => hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y => hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

/--
theorem `spectralNorm_unique_field_norm_ext` / 定理 `spectralNorm_unique_field_norm_ext`

English:
theorem spectralNorm_unique_field_norm_ext
  statement: [CompleteSpace K]
  proof: by
  set g : AlgebraNorm K L :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
      smul' k x := by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def]; rw [map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_

中文:
定理 spectralNorm_unique_field_norm_ext
  结论: [完备空间 K]
  证明: by
  set g : AlgebraNorm K L :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
      smul' k x := by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def]; rw [map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toFun_eq_coe, Algebra, Algebra.smul_def, AlgebraNorm, IsPowMul, MulRingNorm, MulRingNorm.isPowMul, MulRingNorm.mulRingNormEquivAbsoluteValue.invFun, MulRingSeminorm, MulRingSeminorm.toFun_eq_coe, hf_ext, hg_pow, invFun, isPowMul, map_mul, mulRingNormEquivAbsoluteValue, mul_le, smul_def, spectralAlgNorm_def
-/
theorem spectralNorm_unique_field_norm_ext [CompleteSpace K]
    {f : AbsoluteValue L Real} (hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    f x = spectralNorm K L x := by
  set g : AlgebraNorm K L :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
      smul' k x := by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def]; rw [map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_le' x y := by simp [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] }
  have hg_pow : IsPowMul g := MulRingNorm.isPowMul _
  have hgx : f x = g x := rfl
  rw [hgx]; rw [spectralNorm_unique hg_pow]; rw [spectralAlgNorm_def]

variable (K) in
/--
theorem `NormedAlgebra.norm_eq_spectralNorm` / 定理 `NormedAlgebra.norm_eq_spectralNorm`

English:
theorem NormedAlgebra.norm_eq_spectralNorm
  statement: {L : Type*} [NormedField L] [NormedAlgebra K L]
  proof: by
  rw [← toMulAlgebraNorm_apply K L x]; rw [← spectralAlgNorm_def]; rw [← MulAlgebraNorm.coe_AlgebraNorm]; rw [spectralNorm_unique (f := (toMulAlgebraNorm K L).toAlgebraNorm)
      (MulRingNorm.isPowMul (toMulAlgebraNorm K L).toMulRingNorm)]

中文:
定理 赋范代数.norm_eq_spectralNorm
  结论: {L : 类型} [赋范域 L] [赋范代数 K L]
  证明: by
  rw [← toMulAlgebraNorm_apply K L x]; rw [← spectralAlgNorm_def]; rw [← MulAlgebraNorm.coe_AlgebraNorm]; rw [spectralNorm_unique (f := (toMulAlgebraNorm K L).toAlgebraNorm)
      (MulRingNorm.isPowMul (toMulAlgebraNorm K L).toMulRingNorm)]

Depends on / 依赖: MulAlgebraNorm, MulAlgebraNorm.coe_AlgebraNorm, MulRingNorm, MulRingNorm.isPowMul, coe_AlgebraNorm, isPowMul, spectralAlgNorm_def, spectralNorm_unique, toAlgebraNorm, toMulAlgebraNorm, toMulAlgebraNorm_apply, toMulRingNorm
-/
theorem NormedAlgebra.norm_eq_spectralNorm {L : Type*} [NormedField L] [NormedAlgebra K L]
    [Algebra.IsAlgebraic K L] [CompleteSpace K] (x : L) : ‖x‖ = spectralNorm K L x := by
  rw [← toMulAlgebraNorm_apply K L x]; rw [← spectralAlgNorm_def]; rw [← MulAlgebraNorm.coe_AlgebraNorm]; rw [spectralNorm_unique (f := (toMulAlgebraNorm K L).toAlgebraNorm)
      (MulRingNorm.isPowMul (toMulAlgebraNorm K L).toMulRingNorm)]

/--
Definition of `algNormFromConst` / `algNormFromConst` 的定义

English:
definition algNormFromConst
  signature: (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x : L} (hx : x != 0)
  body: have hx' : spectralAlgNorm K L x != 0 :=
    ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
  { normFromConst h1 hx' spectralAlgNorm_isPowMul with
    smul' k y := by
      have h_mul : forall y : L, spectralNorm K L (algebraMap K L k * y) =
          spectralNorm K L (algebr

中文:
定义 algNormFromConst
  签名: (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x : L} (hx : x != 0)
  定义体: have hx' : spectralAlgNorm K L x != 0 :=
    ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
  { normFromConst h1 hx' spectralAlgNorm_isPowMul with
    smul' k y := by
      have h_mul : forall y : L, spectralNorm K L (algebraMap K L k * y) =
          spectralNorm K L (algebr

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Algebra.smul_def, IsAlgebraic, algebraMap, h_mul, isAlgebraic, map_smul_eq_mul, ne_of_gt, normFromConst, smul_def, spectralAlgNorm, spectralAlgNorm_def, spectralAlgNorm_isPowMul, spectralNorm, spectralNorm_extends, spectralNorm_zero_lt
-/
def algNormFromConst (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x : L} (hx : x != 0) :
    AlgebraNorm K L :=
  have hx' : spectralAlgNorm K L x != 0 :=
    ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
  { normFromConst h1 hx' spectralAlgNorm_isPowMul with
    smul' k y := by
      have h_mul : forall y : L, spectralNorm K L (algebraMap K L k * y) =
          spectralNorm K L (algebraMap K L k) * spectralNorm K L y := fun y => by
        rw [spectralNorm_extends]; rw [← Algebra.smul_def]; rw [← spectralAlgNorm_def]; rw [map_smul_eq_mul _ _ _]; rw [spectralAlgNorm_def]
      have h : spectralNorm K L (algebraMap K L k) =
        seminormFromConst' x (spectralAlgNorm K L).toRingSeminorm (algebraMap K L k) := by
          rw [seminormFromConst_apply_of_isMul h1 hx' spectralAlgNorm_isPowMul h_mul]; rfl
      rw [← @spectralNorm_extends K _ L _ _ k]; rw [Algebra.smul_def]; rw [h]
      exact seminormFromConst_isMul_of_isMul h1 hx' spectralAlgNorm_isPowMul h_mul y }

/--
theorem `algNormFromConst_def` / 定理 `algNormFromConst_def`

English:
theorem algNormFromConst_def
  statement: (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x y : L}
  proof: rfl

中文:
定理 algNormFromConst_def
  结论: (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x y : L}
  证明: rfl
-/
theorem algNormFromConst_def (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x y : L}
    (hx : x != 0) :
    algNormFromConst h1 hx y =
      seminormFromConst h1 (ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x)))
        isPowMul_spectralNorm y := rfl

section CompleteSpace

variable [CompleteSpace K]

/--
theorem `spectralAlgNorm_mul` / 定理 `spectralAlgNorm_mul`

English:
theorem spectralAlgNorm_mul
  given: (x y : L)
  proof: by
  by_cases hx : x = 0
  · simp [hx, zero_mul, map_zero]
  · have hx' : spectralAlgNorm K L x != 0 :=
      ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
    have hf1 : (spectralAlgNorm K L) 1 <= 1 := le_of_eq spectralAlgNorm_one
    set f : AlgebraNorm K L := algNormFromC

中文:
定理 spectralAlgNorm_mul
  条件: (x y : L)
  证明: by
  by_cases hx : x = 0
  · simp [hx, zero_mul, map_zero]
  · have hx' : spectralAlgNorm K L x != 0 :=
      ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
    have hf1 : (spectralAlgNorm K L) 1 <= 1 := le_of_eq spectralAlgNorm_one
    set f : AlgebraNorm K L := algNormFromC

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, AlgebraNorm, IsAlgebraic, IsPowMul, algNormFromConst, hf_pow, isAlgebraic, isPowMul_spectralNorm, le_of_eq, map_zero, ne_of_gt, seminormFromConst_const_mul, seminormFromConst_isPowMul, spectralAlgNorm, spectralAlgNorm_one, spectralNorm_unique, spectralNorm_zero_lt, zero_mul
-/
theorem spectralAlgNorm_mul (x y : L) :
    spectralAlgNorm K L (x * y) = spectralAlgNorm K L x * spectralAlgNorm K L y := by
  by_cases hx : x = 0
  · simp [hx, zero_mul, map_zero]
  · have hx' : spectralAlgNorm K L x != 0 :=
      ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
    have hf1 : (spectralAlgNorm K L) 1 <= 1 := le_of_eq spectralAlgNorm_one
    set f : AlgebraNorm K L := algNormFromConst hf1 hx with hf
    have hf_pow : IsPowMul f := seminormFromConst_isPowMul hf1 hx' isPowMul_spectralNorm
    rw [← spectralNorm_unique hf_pow]; rw [hf]
    exact seminormFromConst_const_mul hf1 hx' isPowMul_spectralNorm _

variable (K L) in
/--
Definition of `spectralMulAlgNorm` / `spectralMulAlgNorm` 的定义

English:
definition spectralMulAlgNorm
  signature: : MulAlgebraNorm K L
  body: { spectralAlgNorm K L with
    map_one' := spectralAlgNorm_one
    map_mul' := spectralAlgNorm_mul }

中文:
定义 spectralMulAlgNorm
  签名: : 乘法代数范数 K L
  定义体: { spectralAlgNorm K L with
    map_one' := spectralAlgNorm_one
    map_mul' := spectralAlgNorm_mul }

Depends on / 依赖: map_mul, map_one, spectralAlgNorm, spectralAlgNorm_mul, spectralAlgNorm_one
-/
def spectralMulAlgNorm : MulAlgebraNorm K L :=
  { spectralAlgNorm K L with
    map_one' := spectralAlgNorm_one
    map_mul' := spectralAlgNorm_mul }

/--
theorem `spectralMulAlgNorm_def` / 定理 `spectralMulAlgNorm_def`

English:
theorem spectralMulAlgNorm_def
  given: (x : L)
  statement: spectralMulAlgNorm K L x = spectralNorm K L x
  proof: rfl

中文:
定理 spectralMulAlgNorm_def
  条件: (x : L)
  结论: spectralMulAlgNorm K L x = spectralNorm K L x
  证明: rfl
-/
theorem spectralMulAlgNorm_def (x : L) : spectralMulAlgNorm K L x = spectralNorm K L x := rfl

namespace spectralNorm

variable (K L)

/-- `L` with the spectral norm is a `NormedField`. -/
@[instance_reducible]
/--
Definition of `normedField` / `normedField` 的定义

English:
definition normedField
  signature: : NormedField L
  body: { (inferInstance : Field L) with
    norm x := (spectralNorm K L x : Real)
    dist x y := (spectralNorm K L (x - y) : Real)
    dist_self x := by simp [sub_self, spectralNorm_zero]
    dist_comm x y := by rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle x y z :

中文:
定义 normedField
  签名: : 赋范域 L
  定义体: { (inferInstance : Field L) with
    norm x := (spectralNorm K L x : Real)
    dist x y := (spectralNorm K L (x - y) : Real)
    dist_self x := by simp [sub_self, spectralNorm_zero]
    dist_comm x y := by rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle x y z :

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, add_le, dist_comm, dist_eq, dist_self, dist_triangle, eq_of_dist_eq_zero, isAlgebraic, isNonarchimedean_spectralNorm, isNonarchimedean_spectralNorm.add_le, map_eq_zero_iff_eq_zero, neg_sub, spectralMulAlgNorm, spectralNorm, spectralNorm_neg, spectralNorm_nonneg, spectralNorm_zero, sub_add_sub_cancel
-/
def normedField : NormedField L :=
  { (inferInstance : Field L) with
    norm x := (spectralNorm K L x : Real)
    dist x y := (spectralNorm K L (x - y) : Real)
    dist_self x := by simp [sub_self, spectralNorm_zero]
    dist_comm x y := by rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle x y z :=
      sub_add_sub_cancel x y z ▸ isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg
    eq_of_dist_eq_zero hxy := by
      rw [← sub_eq_zero]
      exact (map_eq_zero_iff_eq_zero (spectralMulAlgNorm K L)).mp hxy
    dist_eq x y := by
      rw [← spectralNorm_neg]; rw [sub_eq_add_neg]; rw [neg_add]; rw [neg_neg]
      exact Algebra.IsAlgebraic.isAlgebraic (x - y)
    norm_mul x y := by simp [← spectralMulAlgNorm_def, map_mul]
    edist_dist x y := by rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- `L` with the spectral norm is a `NontriviallyNormedField`. -/
@[instance_reducible]
/--
Definition of `nontriviallyNormedField` / `nontriviallyNormedField` 的定义

English:
definition nontriviallyNormedField
  signature: : NontriviallyNormedField L where
  body: spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
⟨algebraMap K L x, hx.trans_eq (spectralNorm_extends _).symm⟩

中文:
定义 nontriviallyNormedField
  签名: : NontriviallyNormedField L where
  定义体: spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
⟨algebraMap K L x, hx.trans_eq (spectralNorm_extends _).symm⟩

Depends on / 依赖: normedField, spectralNorm, spectralNorm.normedField
-/
def nontriviallyNormedField : NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
⟨algebraMap K L x, hx.trans_eq (spectralNorm_extends _).symm⟩

/-- `L` with the spectral norm is a `SeminormedRing`. -/
@[instance_reducible]
/--
Definition of `seminormedRing` / `seminormedRing` 的定义

English:
definition seminormedRing
  signature: : SeminormedRing L
  body: by
  letI : NormedField L := normedField K L
  infer_instance

中文:
定义 seminormedRing
  签名: : Seminormed环 L
  定义体: by
  letI : NormedField L := normedField K L
  infer_instance

Depends on / 依赖: NormedField, infer_instance, normedField
-/
def seminormedRing : SeminormedRing L := by
  letI : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `NormedAddCommGroup`. -/
@[instance_reducible]
/--
Definition of `normedAddCommGroup` / `normedAddCommGroup` 的定义

English:
definition normedAddCommGroup
  signature: : NormedAddCommGroup L
  body: by
  haveI : NormedField L := normedField K L
  infer_instance

中文:
定义 normedAddCommGroup
  签名: : 赋范交换加群 L
  定义体: by
  haveI : NormedField L := normedField K L
  infer_instance

Depends on / 依赖: NormedField, infer_instance, normedField
-/
def normedAddCommGroup : NormedAddCommGroup L := by
  haveI : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `SeminormedAddCommGroup`. -/
@[instance_reducible]
/--
Definition of `seminormedAddCommGroup` / `seminormedAddCommGroup` 的定义

English:
definition seminormedAddCommGroup
  signature: : SeminormedAddCommGroup L
  body: by
  have : NormedField L := normedField K L
  infer_instance

中文:
定义 seminormedAddCommGroup
  签名: : SeminormedAddComm群 L
  定义体: by
  have : NormedField L := normedField K L
  infer_instance

Depends on / 依赖: NormedField, infer_instance, normedField
-/
def seminormedAddCommGroup : SeminormedAddCommGroup L := by
  have : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `NormedSpace` over `K`. -/
@[instance_reducible]
/--
Definition of `normedSpace` / `normedSpace` 的定义

English:
definition normedSpace
  signature: : @NormedSpace K L _ (seminormedAddCommGroup K L)
  body: letI _ := seminormedAddCommGroup K L
  { (inferInstance : Module K L) with
    norm_smul_le r x := by
      change spectralAlgNorm K L (r • x) <= ‖r‖ * spectralAlgNorm K L x
      exact le_of_eq (map_smul_eq_mul _ _ _) }

中文:
定义 normedSpace
  签名: : @赋范空间 K L _ (seminormedAddCommGroup K L)
  定义体: letI _ := seminormedAddCommGroup K L
  { (inferInstance : Module K L) with
    norm_smul_le r x := by
      change spectralAlgNorm K L (r • x) <= ‖r‖ * spectralAlgNorm K L x
      exact le_of_eq (map_smul_eq_mul _ _ _) }

Depends on / 依赖: Module, le_of_eq, map_smul_eq_mul, norm_smul_le, seminormedAddCommGroup, spectralAlgNorm
-/
def normedSpace : @NormedSpace K L _ (seminormedAddCommGroup K L) :=
  letI _ := seminormedAddCommGroup K L
  { (inferInstance : Module K L) with
    norm_smul_le r x := by
      change spectralAlgNorm K L (r • x) <= ‖r‖ * spectralAlgNorm K L x
      exact le_of_eq (map_smul_eq_mul _ _ _) }

/-- `L` with the spectral norm is a `NormedAlgebra` over `K`. -/
@[instance_reducible]
/--
Definition of `normedAlgebra` / `normedAlgebra` 的定义

English:
definition normedAlgebra
  signature: :
  body: letI _ := normedField K L
  { normedSpace K L, (inferInstance : Algebra K L) with }

中文:
定义 normedAlgebra
  签名: :
  定义体: letI _ := normedField K L
  { normedSpace K L, (inferInstance : Algebra K L) with }

Depends on / 依赖: Algebra, normedField, normedSpace
-/
def normedAlgebra :
    @NormedAlgebra K L _ (seminormedRing K L) :=
  letI _ := normedField K L
  { normedSpace K L, (inferInstance : Algebra K L) with }

/-- `L` with the spectral norm is a `NormedAlgebra` over any intermediate `E`
that is a normed algebra over `K`. -/
@[instance_reducible]
/--
Definition of `normedAlgebra'` / `normedAlgebra'` 的定义

English:
definition normedAlgebra'
  signature: (E L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [NormedField E]
  body: letI _ := normedField K L
  letI _ := normedAlgebra K L
  letI _ := Algebra.IsAlgebraic.tower_bot K E L
  { (inferInstance : Algebra E L) with
    norm_smul_le _ _ := by
      apply le_of_eq
      simp only [Algebra.smul_def, norm_mul, mul_eq_mul_right_iff, _root_.norm_eq_zero]
      simp only [Norm

中文:
定义 normedAlgebra'
  签名: (E L : 类型) [域 L] [代数 K L] [代数.是代数 K L] [赋范域 E]
  定义体: letI _ := normedField K L
  letI _ := normedAlgebra K L
  letI _ := Algebra.IsAlgebraic.tower_bot K E L
  { (inferInstance : Algebra E L) with
    norm_smul_le _ _ := by
      apply le_of_eq
      simp only [Algebra.smul_def, norm_mul, mul_eq_mul_right_iff, _root_.norm_eq_zero]
      simp only [Norm

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.tower_bot, Algebra.smul_def, IsAlgebraic, NormedAlgebra, NormedAlgebra.norm_eq_spectralNorm, Or.inl, _root_, _root_.norm_eq_zero, eq_of_tower, le_of_eq, mul_eq_mul_right_iff, norm_eq_spectralNorm, norm_eq_zero, norm_mul, norm_smul_le, normedAlgebra, normedField, smul_def, spectralNorm
-/
def normedAlgebra' (E L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [NormedField E]
    [NormedAlgebra K E] [Algebra E L] [IsScalarTower K E L] :
    @NormedAlgebra E L _ (seminormedRing K L) :=
  letI _ := normedField K L
  letI _ := normedAlgebra K L
  letI _ := Algebra.IsAlgebraic.tower_bot K E L
  { (inferInstance : Algebra E L) with
    norm_smul_le _ _ := by
      apply le_of_eq
      simp only [Algebra.smul_def, norm_mul, mul_eq_mul_right_iff, _root_.norm_eq_zero]
      simp only [NormedAlgebra.norm_eq_spectralNorm K]
exact Or.inl (spectralNorm.eq_of_tower _).symm }

/-- The metric space structure on `L` induced by the spectral norm. -/
@[instance_reducible]
/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
definition metricSpace
  signature: : MetricSpace L
  body: (normedField K L).toMetricSpace

中文:
定义 metricSpace
  签名: : 度量空间 L
  定义体: (normedField K L).toMetricSpace

Depends on / 依赖: normedField, toMetricSpace
-/
def metricSpace : MetricSpace L := (normedField K L).toMetricSpace

/-- The uniform space structure on `L` induced by the spectral norm. -/
@[instance_reducible]
/--
Definition of `uniformSpace` / `uniformSpace` 的定义

English:
definition uniformSpace
  signature: : UniformSpace L
  body: (metricSpace K L).toUniformSpace

中文:
定义 uniformSpace
  签名: : 一致空间 L
  定义体: (metricSpace K L).toUniformSpace

Depends on / 依赖: metricSpace, toUniformSpace
-/
def uniformSpace : UniformSpace L := (metricSpace K L).toUniformSpace

/-- If `L/K` is finite dimensional, then `L` is a complete space with respect to topology induced
  by the spectral norm. -/
instance (priority := 100) completeSpace [h_fin : FiniteDimensional K L] :
    @CompleteSpace L (uniformSpace K L) := by
  let := (normedAddCommGroup K L)
  let := (normedSpace K L)
  exact FiniteDimensional.complete K L

omit [Algebra.IsAlgebraic K L] in
/--
lemma `spectralMulAlgNorm_eq_of_mem_roots` / 引理 `spectralMulAlgNorm_eq_of_mem_roots`

English:
lemma spectralMulAlgNorm_eq_of_mem_roots
  statement: (x : L) {E : Type*} [Field E] [Algebra K E] [Algebra L E]
  proof: by
  simp only [spectralMulAlgNorm_def, spectralNorm]
  have : (aeval a) (minpoly K ((algebraMap L E) x)) = 0 := by
    simp only [mem_roots', IsRoot.def] at ha
    rw [← ha.2]; rw [mapAlg_eq_map]; rw [minpoly.algebraMap_eq (algebraMap L E).injective]; rw [aeval_def]; rw [eval_map]
  rw [← minpoly.e

中文:
引理 spectralMulAlgNorm_eq_of_mem_roots
  结论: (x : L) {E : 类型} [域 E] [代数 K E] [代数 L E]
  证明: by
  simp only [spectralMulAlgNorm_def, spectralNorm]
  have : (aeval a) (minpoly K ((algebraMap L E) x)) = 0 := by
    simp only [mem_roots', IsRoot.def] at ha
    rw [← ha.2]; rw [mapAlg_eq_map]; rw [minpoly.algebraMap_eq (algebraMap L E).injective]; rw [aeval_def]; rw [eval_map]
  rw [← minpoly.e

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, IsRoot, IsRoot.def, aeval_def, algebraMap, algebraMap_eq, eq_of_root, eval_map, injective, isAlgebraic, mapAlg_eq_map, mem_roots, minpoly, minpoly.algebraMap_eq, minpoly.eq_of_root, spectralMulAlgNorm_def, spectralNorm
-/
lemma spectralMulAlgNorm_eq_of_mem_roots (x : L) {E : Type*} [Field E] [Algebra K E] [Algebra L E]
    [IsScalarTower K L E] [Algebra.IsAlgebraic K E] {a : E}
    (ha : a in ((mapAlg K E) (minpoly K x)).roots) :
    (spectralMulAlgNorm K E) a = (spectralMulAlgNorm K E) ((algebraMap L E) x) := by
  simp only [spectralMulAlgNorm_def, spectralNorm]
  have : (aeval a) (minpoly K ((algebraMap L E) x)) = 0 := by
    simp only [mem_roots', IsRoot.def] at ha
    rw [← ha.2]; rw [mapAlg_eq_map]; rw [minpoly.algebraMap_eq (algebraMap L E).injective]; rw [aeval_def]; rw [eval_map]
  rw [← minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic ((algebraMap L E) x)) this]

omit [Algebra.IsAlgebraic K L] in
/--
theorem `spectralNorm_pow_natDegree_eq_prod_roots` / 定理 `spectralNorm_pow_natDegree_eq_prod_roots`

English:
theorem spectralNorm_pow_natDegree_eq_prod_roots
  statement: (x : L) {E : Type*} [Field E] [Algebra K E]
  proof: by
  have h_deg : (minpoly K x).natDegree = Multiset.card ((mapAlg K E) (minpoly K x)).roots := by
    trans (mapAlg K E (minpoly K x)).natDegree
    · rw [mapAlg_eq_map, natDegree_map]
    · rw [eq_comm, ← splits_iff_card_roots]
      exact IsSplittingField.IsScalarTower.splits (K := L) E (minpoly 

中文:
定理 spectralNorm_pow_natDegree_eq_prod_roots
  结论: (x : L) {E : 类型} [域 E] [代数 K E]
  证明: by
  have h_deg : (minpoly K x).natDegree = Multiset.card ((mapAlg K E) (minpoly K x)).roots := by
    trans (mapAlg K E (minpoly K x)).natDegree
    · rw [mapAlg_eq_map, natDegree_map]
    · rw [eq_comm, ← splits_iff_card_roots]
      exact IsSplittingField.IsScalarTower.splits (K := L) E (minpoly 

Depends on / 依赖: IsScalarTower, IsSplittingField, IsSplittingField.IsScalarTower.splits, Multiset, Multiset.card, Multiset.count_replicate, Multiset.map, Multiset.prod_replicate, congr_arg, count_replicate, eq_comm, h_deg, mapAlg, mapAlg_eq_map, map_multiset_prod, minpoly, natDegree, natDegree_map, prod_replicate, spectralMulAlgNorm
-/
theorem spectralNorm_pow_natDegree_eq_prod_roots (x : L) {E : Type*} [Field E] [Algebra K E]
    [Algebra L E] [IsScalarTower K L E] [IsSplittingField L E (mapAlg K L (minpoly K x))]
    [Algebra.IsAlgebraic K E] :
    (spectralMulAlgNorm K E) ((algebraMap L E) x) ^ (minpoly K x).natDegree =
      (spectralMulAlgNorm K E) ((mapAlg K E) (minpoly K x)).roots.prod := by
  have h_deg : (minpoly K x).natDegree = Multiset.card ((mapAlg K E) (minpoly K x)).roots := by
    trans (mapAlg K E (minpoly K x)).natDegree
    · rw [mapAlg_eq_map, natDegree_map]
    · rw [eq_comm, ← splits_iff_card_roots]
      exact IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  rw [map_multiset_prod]; rw [← Multiset.prod_replicate]
  apply congr_arg
  ext r
  rw [Multiset.count_replicate]
  split_ifs with hr
  · have h : forall s in Multiset.map (spectralMulAlgNorm K E) ((mapAlg K E) (minpoly K x)).roots,
        r = s := by
      intro s hs
      obtain ⟨a, ha, has⟩ := Multiset.mem_map.mp hs
      rw [← hr]; rw [← has]; rw [spectralMulAlgNorm_eq_of_mem_roots K L x ha]
    rwa [Multiset.count_eq_card.mpr h, Multiset.card_map]
  · rw [Multiset.count_eq_zero_of_notMem]
    intro hr_mem
    obtain ⟨e, he, her⟩ := Multiset.mem_map.mp hr_mem
    rw [spectralMulAlgNorm_eq_of_mem_roots K L x he] at her
    exact hr her

/--
theorem `spectralNorm_eq_norm_coeff_zero_rpow` / 定理 `spectralNorm_eq_norm_coeff_zero_rpow`

English:
theorem spectralNorm_eq_norm_coeff_zero_rpow
  given: (x : L)
  proof: by
  set E := (mapAlg K L (minpoly K x)).SplittingField
  have hspl : Splits (mapAlg K E (minpoly K x)) :=
    IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  have : Algebra.IsAlgebraic L E :=
    IsSplittingField.IsScalarTower.isAlgebraic E (mapAlg K L (minpoly K x))
  have : Algeb

中文:
定理 spectralNorm_eq_norm_coeff_zero_rpow
  条件: (x : L)
  证明: by
  set E := (mapAlg K L (minpoly K x)).SplittingField
  have hspl : Splits (mapAlg K E (minpoly K x)) :=
    IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  have : Algebra.IsAlgebraic L E :=
    IsSplittingField.IsScalarTower.isAlgebraic E (mapAlg K L (minpoly K x))
  have : Algeb

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.trans, IsAlgebraic, IsScalarTower, IsSplittingField, IsSplittingField.IsScalarTower.isAlgebraic, IsSplittingField.IsScalarTower.splits, Real.eq_rpow_inv, Real.rpow_natCast, Splits, SplittingField, eq_of_tower, eq_rpow_inv, isAlgebraic, mapAlg, minpoly, norm_nonneg, one_div, rpow_natCast
-/
theorem spectralNorm_eq_norm_coeff_zero_rpow (x : L) :
    spectralNorm K L x = ‖(minpoly K x).coeff 0‖ ^ (1 / (minpoly K x).natDegree : Real) := by
  set E := (mapAlg K L (minpoly K x)).SplittingField
  have hspl : Splits (mapAlg K E (minpoly K x)) :=
    IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  have : Algebra.IsAlgebraic L E :=
    IsSplittingField.IsScalarTower.isAlgebraic E (mapAlg K L (minpoly K x))
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.trans K L E
  rw [one_div]; rw [Real.eq_rpow_inv (spectralNorm_nonneg x) (norm_nonneg ((minpoly K x).coeff 0))]; rw [Real.rpow_natCast]; rw [@spectralNorm.eq_of_tower K _ E]; rw [← @spectralNorm_extends K _ L _ _ ((minpoly K x).coeff 0)]; rw [@spectralNorm.eq_of_tower K _ E _ _ L]; rw [← spectralMulAlgNorm_def]; rw [← spectralMulAlgNorm_def]; rw [Polynomial.coeff_zero_of_isScalarTower]; rw [hspl.coeff_zero_eq_prod_roots_of_monic _]; rw [map_mul]; rw [map_pow]; rw [map_neg_eq_map]; rw [map_one]; rw [one_pow]; rw [one_mul]; rw [spectralNorm_pow_natDegree_eq_prod_roots _ _ x]
  · simp [monic_mapAlg_iff, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral]
  · exact_mod_cast (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'

end spectralNorm

end CompleteSpace

end NontriviallyNormedField

end spectralNorm
