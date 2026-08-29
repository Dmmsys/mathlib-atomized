/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Approximate roots and polynomials in a normed field

In this file, we prove several approximation lemmas on a normed field.

## Main results
- `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` : **Continuity of Roots.**
Let `f` and `g` be two monic polynomials such that `g` splits. If the coefficients of two
polynomials `f` and `g` are sufficiently close, then every root of `f` has a corresponding root
of `g` nearby.

- `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` : Let `K` be a
dense subfield of a normed field `L`. Every monic polynomial in `L` can be approximated by
a monic polynomial in `K` of the same degree.

## TODO
Use the fact that `f.discr` is polynomial of the coefficients of `f` to show that
every polynomial `f` can be approximated by a *separable* polynomial. This result can be used
to show that the completion a separably closed field is algebraically closed, upgrading the
current theorem `IsAlgClosed.of_denseRange`.

## Tags
Approximation, polynomial, normed field, continuity of roots
-/

public section

variable {K L : Type*}

namespace Polynomial

section ContinuityOfRoots

variable [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K}
  {f g : Polynomial K} {ε : Real}

/--
theorem `exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` / 定理 `exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`

English:
theorem exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
  statement: (hε : 0 < ε) {a : K} (ha : f.eval a = 0)
  proof: by
  -- Let `a` be a root of `f`. To show there exists a root `b` of `g` such that `‖a - b‖` is small,
  -- it suffices to show that `∏ (b ∈ g.roots) ‖a - b‖` is small.
  suffices this : (g.roots.map fun x => ‖a - x‖).prod <
      ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : Real) by
    b

中文:
定理 exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
  结论: (hε : 0 < ε) {a : K} (ha : f.eval a = 0)
  证明: by
  -- Let `a` be a root of `f`. To show there exists a root `b` of `g` such that `‖a - b‖` is small,
  -- it suffices to show that `∏ (b ∈ g.roots) ‖a - b‖` is small.
  suffices this : (g.roots.map fun x => ‖a - x‖).prod <
      ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : Real) by
    b
-/
theorem exists_roots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : K} (ha : f.eval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε) (hg : g.Splits) :
    exists b in g.roots, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : Real)⁻¹ * max ‖a‖ 1 := by
  -- Let `a` be a root of `f`. To show there exists a root `b` of `g` such that `‖a - b‖` is small,
  -- it suffices to show that `∏ (b ∈ g.roots) ‖a - b‖` is small.
  suffices this : (g.roots.map fun x => ‖a - x‖).prod <
      ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : Real) by
    by_contra! h
    have := Multiset.prod_map_le_prod_map₀ (fun b => ((f.natDegree + 1) * ε) ^ (f.natDegree : Real)⁻¹ *
        (‖a‖ ⊔ 1)) (fun b => ‖a - b‖) (by intros; positivity) h
    simp only [Multiset.map_const', hg.natDegree_eq_card_roots.symm ▸ hdeg, Multiset.prod_replicate,
      mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : ((f.natDegree + 1) * ε) > 0).le] at this
    rw [inv_mul_cancel₀]; rw [Real.rpow_one] at this
    · linarith
    · simp only [ne_eq, Nat.cast_eq_zero, hfm, Monic.natDegree_eq_zero]
      intro h
      simp [h] at ha
  -- `∏ (b ∈ g.roots) ‖a - b‖ = ‖g(a)‖ = ‖(g - f)(a)‖` is small since every
  -- coefficient of `‖g - f‖` is small.
  calc
  _ = (g.roots.map (fun x => NormedField.toMulRingNorm K (a - x))).prod := rfl
  _ = ‖(g.roots.map (fun x => a - x)).prod‖ := by
    rw [g.roots.prod_hom' (NormedField.toMulRingNorm K) (fun x : K => a - x)]
    rfl
  _ = ‖g.eval a‖ := by
    congr
    rw [hg.eval_eq_prod_roots_of_monic hgm]
  _ <= ‖g.eval a - f.eval a‖ + ‖f.eval a‖ := by
    convert! norm_add_le (g.eval a - f.eval a) (f.eval a)
    simp
  _ = ‖(∑ i in Finset.range (g.natDegree + 1), C (g.coeff i - f.coeff i) * X ^ i).eval a‖ := by
    rw [← eval_sub]
    simp only [ha, norm_zero, add_zero]
    rw [(g - f).as_sum_range' (g.natDegree + 1)]
    · congr
      simp [← C_mul_X_pow_eq_monomial]
    · simpa [hdeg, Nat.lt_succ_iff] using g.natDegree_sub_le f
  _ <= ∑ i in Finset.range (g.natDegree + 1), ‖(g.coeff i - f.coeff i) * a ^ i‖ := by
    have := norm_sum_le (Finset.range (g.natDegree + 1))
        (fun i => (C (g.coeff i - f.coeff i) * X ^ i).eval a)
    simpa [eval_mul, eval_finsetSum] using this
    -- The following tactic does not work here:
    -- simpa [eval_mul, eval_finsetSum] using norm_sum_le (Finset.range (g.natDegree + 1))
    -- (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).eval a)
  _ < _ := by
    rw [hdeg]
    convert!
      Finset.sum_lt_sum_of_nonempty (g := fun i => ε * (‖a‖ ⊔ 1) ^ ↑f.natDegree)
        (Finset.nonempty_range_add_one) ?_
    · simp [mul_assoc]
    · simp only [Finset.mem_range, norm_mul, norm_pow]
      intro i hi
      apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      · simpa [← map_sub] using hcoeff i
      · refine (pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ 1) i).trans ?_
        exact pow_le_pow_right₀ (le_max_right ‖a‖ 1) (Nat.le_of_lt_succ hi)
      all_goals positivity

/--
theorem `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt` / 定理 `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`

English:
theorem exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
  statement: (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
  proof: by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

中文:
定理 exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
  结论: (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
  证明: by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

Depends on / 依赖: algebraMap, exists_roots_norm_sub_lt_of_norm_coeff_sub_lt, f.map, hcoeff, hfm.map, hgm.map, map_sub
-/
theorem exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : forall i : Nat, ‖g.coeff i - f.coeff i‖ < ε) (hg : (g.map (algebraMap K L)).Splits) :
    exists b in g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : Real)⁻¹ * max ‖a‖ 1 := by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

end ContinuityOfRoots

section Approximation

variable [Field K] [NormedField L] [Algebra K L]

/--
theorem `exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` / 定理 `exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`

English:
theorem exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
  proof: by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i => Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 

中文:
定理 exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
  证明: by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i => Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 

Depends on / 依赖: Metric, Metric.denseRange_iff.mp, Polynomial, Polynomial.map_one, Polynomial.natDegree_add_eq_left_of_natDegree_lt, and_self, denseRange_iff, f.coeff, f.natDegree, hf.natDegree_eq_zero.mp, implies_true, map_one, monic_one, natDegree, natDegree_add_eq_left_of_natDegree_lt, natDegree_eq_zero, natDegree_one, norm_zero, one_mul, sub_self
-/
theorem exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    (hd : DenseRange (algebraMap K L)) {f : Polynomial L} (hf : f.Monic) {ε : Real} (hε : ε > 0) :
    exists g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ forall n : Nat,
    ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i => Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i).natDegree
      = f.natDegree := by
    calc
      _ = (C (1 : K) * X ^ f.natDegree).natDegree := by
        apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
        simp only [map_one, one_mul, natDegree_pow, natDegree_X, mul_one]
        rw [← Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)]
        apply Polynomial.natDegree_sum_le_of_forall_le
        refine fun i hi => (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        simpa [Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)] using hi
      _ = f.natDegree := by
        simp
  use C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i
  refine ⟨?_, hdeg.symm, fun n => ?_⟩
  · rw [Monic, leadingCoeff, hdeg]
    simp
  · rcases lt_trichotomy n f.natDegree with h | h | h
    · simpa [h, ne_of_lt h, ← dist_eq_norm_sub'] using hc n
    · simp [h, hf, hε]
    · simp [not_lt_of_gt h, ne_of_gt h, coeff_eq_zero_of_natDegree_lt h, hε]

end Approximation

end Polynomial
