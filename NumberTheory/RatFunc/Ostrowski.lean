/-
Copyright (c) 2025 María Inés de Frutos-Fernández & Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.FieldTheory.Finite.Valuation
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Ostrowski's theorem for `K(X)`

This file proves Ostrowski's theorem for the field of rational functions `K(X)`, where `K` is any
field: if `v` is a discrete valuation on `K(X)` which is trivial on elements of `K`, then `v` is
equivalent to either the `I`-adic valuation for some `I : HeightOneSpectrum K[X]`, or to the
valuation at infinity `FunctionField.inftyValuation K`.

## Main results
- `RatFunc.valuation_isEquiv_infty_or_adic`: Ostrowski's theorem for `K(X)`.
-/

@[expose] public noncomputable section


open Multiplicative WithZero

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation (RatFunc K) Γ}

namespace RatFunc

section Infinity

open Polynomial Valuation

/--
lemma `valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X` / 引理 `valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X`

English:
lemma valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
  statement: {f : RatFunc K}
  proof: by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [intDegree_div (by grind only) (by grind only)]; rw [v.map_div]; rw [zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coePolynomial_eq_algebraMap]
    have hp : p != 0 := by contrapose hf; simp [

中文:
引理 valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
  结论: {f : 有理函数 K}
  证明: by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [intDegree_div (by grind only) (by grind only)]; rw [v.map_div]; rw [zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coePolynomial_eq_algebraMap]
    have hp : p != 0 := by contrapose hf; simp [

Depends on / 依赖: RatFunc, RatFunc.induction_on, coePolynomial_eq_algebraMap, contrapose, induction_on, intDegree_div, intDegree_polynomial, map_div, ne_zero_of_lt, simp_rw, v.map_div, valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X, zpow_natCast
-/
lemma valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc K}
    [v.IsTrivialOn K] (hlt : 1 < v X) (hf : f != 0) : v f = v RatFunc.X ^ f.intDegree := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [intDegree_div (by grind only) (by grind only)]; rw [v.map_div]; rw [zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coePolynomial_eq_algebraMap]
    have hp : p != 0 := by contrapose hf; simp [hf]
    rw [valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hp]; rw [valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hq]

variable [DecidableEq (RatFunc K)]

/--
lemma `valuation_isEquiv_inftyValuation_of_one_lt_valuation_X` / 引理 `valuation_isEquiv_inftyValuation_of_one_lt_valuation_X`

English:
lemma valuation_isEquiv_inftyValuation_of_one_lt_valuation_X
  given: [v.IsTrivialOn K] (hlt : 1 < v X)
  proof: by
  refine isEquiv_iff_val_lt_one.mpr fun {f} => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf]; rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuat

中文:
引理 valuation_isEquiv_inftyValuation_of_one_lt_valuation_X
  条件: [v.是TrivialOn K] (hlt : 1 < v X)
  证明: by
  refine isEquiv_iff_val_lt_one.mpr fun {f} => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf]; rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuat

Depends on / 依赖: eq_or_ne, exp_zero, inftyValuation, isEquiv_iff_val_lt_one, isEquiv_iff_val_lt_one.mpr, valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
-/
lemma valuation_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (hlt : 1 < v X) :
    v.IsEquiv (inftyValuation K) := by
  refine isEquiv_iff_val_lt_one.mpr fun {f} => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf]; rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt' hf]
    grind [one_le_zpow_iff_right₀]

end Infinity

open IsDedekindDomain HeightOneSpectrum Set Valuation Polynomial

/--
lemma `setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty` / 引理 `setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty`

English:
lemma setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
  statement: [v.IsNontrivial] [v.IsTrivialOn K]
  proof: by
  obtain ⟨w, h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, _root_.div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or,
      map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aeso

中文:
引理 setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
  结论: [v.是非平凡] [v.是TrivialOn K]
  证明: by
  obtain ⟨w, h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, _root_.div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or,
      map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aeso

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, IsNontrivial, IsNontrivial.exists_lt_one, Nonempty, Or.elim, RatFunc, RatFunc.induction_on, _root_, _root_.div_eq_zero_iff, algebraMap_eq_zero_iff, div_eq_zero_iff, exists_lt_one, induction_on, lt_iff_le_and_ne, lt_iff_le_and_ne.mpr, ne_eq, not_and_or, not_or
-/
lemma setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTrivialOn K]
    (hle : v RatFunc.X <= 1) : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty := by
  obtain ⟨w, h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, _root_.div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or,
      map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aesop
    suffices forall r : K[X], v (↑r) != 1 -> r != 0 -> {p : K[X] | v ↑p < 1 ∧ ¬p = 0}.Nonempty by
      exact Or.elim hor (fun hp => this p hp h0.1) (fun hq => this q hq h0.2)
    exact fun r hr hr0 => ⟨r, lt_iff_le_and_ne.mpr
      ⟨Polynomial.valuation_le_one_of_valuation_X_le_one _ hle r, hr⟩, hr0⟩

@[deprecated (since := "2026-07-09")]
alias setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty :=
  setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty

/--
lemma `one_le_valuation_factor` / 引理 `one_le_valuation_factor`

English:
lemma one_le_valuation_factor
  statement: (hne : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty) {a b : K[X]}
  proof: by
  set πᵥ := degree_lt_wf.min _ hne
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_co

中文:
引理 one_le_valuation_factor
  结论: (hne : {p : K[X] | v p < 1 ∧ p != 0}.非空) {a b : K[X]}
  证明: by
  set πᵥ := degree_lt_wf.min _ hne
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_co
-/
private lemma one_le_valuation_factor (hne : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty) {a b : K[X]}
    (hab : v ↑(a * b) < 1 ∧ a != 0 ∧ b != 0) (hπᵥ : degree_lt_wf.min _ hne = a * b)
    (hb : ¬IsUnit b) : 1 <= v ↑a := by
  set πᵥ := degree_lt_wf.min _ hne
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_comm.mp (degree_lt_wf.not_lt_min _) hda
  grind

/--
lemma `irreducible_min_polynomial_valuation_lt_one_and_ne_zero` / 引理 `irreducible_min_polynomial_valuation_lt_one_and_ne_zero`

English:
lemma irreducible_min_polynomial_valuation_lt_one_and_ne_zero
  statement: [v.IsTrivialOn K]
  proof: by
  set πᵥ := degree_lt_wf.min _ hne
  have hπᵥ : v πᵥ < 1 ∧ πᵥ != 0 := degree_lt_wf.min_mem _ hne
  refine irreducible_iff.mpr ⟨?_, fun a b hab => ?_⟩
  · simp only [Polynomial.isUnit_iff, isUnit_iff_ne_zero]
    intro ⟨a, ha0, ha⟩
    rw [← ha]; rw [coePolynomial]; rw [algebraMap_C]; rw [← algebr

中文:
引理 irreducible_min_polynomial_valuation_lt_one_and_ne_zero
  结论: [v.是TrivialOn K]
  证明: by
  set πᵥ := degree_lt_wf.min _ hne
  have hπᵥ : v πᵥ < 1 ∧ πᵥ != 0 := degree_lt_wf.min_mem _ hne
  refine irreducible_iff.mpr ⟨?_, fun a b hab => ?_⟩
  · simp only [Polynomial.isUnit_iff, isUnit_iff_ne_zero]
    intro ⟨a, ha0, ha⟩
    rw [← ha]; rw [coePolynomial]; rw [algebraMap_C]; rw [← algebr

Depends on / 依赖: Polynomial, Polynomial.isUnit_iff, Right.one_, algebraMap_C, algebraMap_eq_C, and_comm, coePolynomial, degree_lt_wf, degree_lt_wf.min, degree_lt_wf.min_mem, irreducible_iff, irreducible_iff.mpr, isUnit_iff, isUnit_iff_ne_zero, min_mem, mul_comm, mul_eq_zero, ne_eq, not_or, one_
-/
lemma irreducible_min_polynomial_valuation_lt_one_and_ne_zero [v.IsTrivialOn K]
    (hne : {p : K[X] | v p < 1 ∧ p != 0}.Nonempty) :
    Irreducible (degree_lt_wf.min {p : K[X] | v p < 1 ∧ p != 0} hne) := by
  set πᵥ := degree_lt_wf.min _ hne
  have hπᵥ : v πᵥ < 1 ∧ πᵥ != 0 := degree_lt_wf.min_mem _ hne
  refine irreducible_iff.mpr ⟨?_, fun a b hab => ?_⟩
  · simp only [Polynomial.isUnit_iff, isUnit_iff_ne_zero]
    intro ⟨a, ha0, ha⟩
    rw [← ha]; rw [coePolynomial]; rw [algebraMap_C]; rw [← algebraMap_eq_C] at hπᵥ
    grind
  · by_contra! H
    simp only [hab, ne_eq, mul_eq_zero, not_or] at hπᵥ
    have hva := one_le_valuation_factor hne hπᵥ hab H.2
    simp only [mul_comm a b, @and_comm (¬a = 0)] at hπᵥ hab
    have := Right.one_le_mul (one_le_valuation_factor hne hπᵥ hab H.1) hva
    simp only [coePolynomial_eq_algebraMap, map_mul] at hπᵥ this
    grind

section valuation_X_le_one

variable [v.IsNontrivial] [v.IsTrivialOn K] (hle : v RatFunc.X <= 1)

/--
Definition of `uniformizingPolynomial` / `uniformizingPolynomial` 的定义

English:
abbreviation uniformizingPolynomial
  signature: : K[X]
  body: WellFounded.min degree_lt_wf _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)

@[inherit_doc]
local notation "πᵥ" => uniformizingPolynomial hle

中文:
缩写 uniformizingPolynomial
  签名: : K[X]
  定义体: WellFounded.min degree_lt_wf _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)

@[inherit_doc]
local notation "πᵥ" => uniformizingPolynomial hle

Depends on / 依赖: WellFounded, WellFounded.min, degree_lt_wf, setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
-/
abbrev uniformizingPolynomial : K[X] :=
  WellFounded.min degree_lt_wf _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)

@[inherit_doc]
local notation "πᵥ" => uniformizingPolynomial hle

/--
lemma `uniformizingPolynomial_ne_zero` / 引理 `uniformizingPolynomial_ne_zero`

English:
lemma uniformizingPolynomial_ne_zero
  statement: πᵥ != 0
  proof: by
  have := degree_lt_wf.min_mem _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
  simp_all [uniformizingPolynomial]

中文:
引理 uniformizingPolynomial_ne_zero
  结论: πᵥ != 0
  证明: by
  have := degree_lt_wf.min_mem _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
  simp_all [uniformizingPolynomial]

Depends on / 依赖: degree_lt_wf, degree_lt_wf.min_mem, min_mem, setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty, uniformizingPolynomial
-/
lemma uniformizingPolynomial_ne_zero : πᵥ != 0 := by
  have := degree_lt_wf.min_mem _ (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
  simp_all [uniformizingPolynomial]

/--
lemma `valuation_uniformizingPolynomial_lt_one` / 引理 `valuation_uniformizingPolynomial_lt_one`

English:
lemma valuation_uniformizingPolynomial_lt_one
  statement: v πᵥ < 1
  proof: by
  simpa using! (degree_lt_wf.min_mem _
    (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)).1

中文:
引理 valuation_uniformizingPolynomial_lt_one
  结论: v πᵥ < 1
  证明: by
  simpa using! (degree_lt_wf.min_mem _
    (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)).1

Depends on / 依赖: degree_lt_wf, degree_lt_wf.min_mem, min_mem, setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
-/
lemma valuation_uniformizingPolynomial_lt_one : v πᵥ < 1 := by
  simpa using! (degree_lt_wf.min_mem _
    (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)).1

open Ideal in
/--
Definition of `valuationIdeal` / `valuationIdeal` 的定义

English:
definition valuationIdeal
  signature: : HeightOneSpectrum K[X] where
  body: Submodule.span K[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle

@[

中文:
定义 valuationIdeal
  签名: : 高一谱 K[X] where
  定义体: Submodule.span K[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle

@[

Depends on / 依赖: Submodule, Submodule.span
-/
def valuationIdeal : HeightOneSpectrum K[X] where
  asIdeal := Submodule.span K[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle

@[inherit_doc]
local notation "Pᵥ" => RatFunc.valuationIdeal hle

section Associates

open EuclideanDomain in
/--
lemma `valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one` / 引理 `valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one`

English:
lemma valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one
  statement: {p : K[X]}
  proof: by
  set π := πᵥ
  have hne := setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π in _ := degree_lt_wf.min_mem _ hn

中文:
引理 valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one
  结论: {p : K[X]}
  证明: by
  set π := πᵥ
  have hne := setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π in _ := degree_lt_wf.min_mem _ hn

Depends on / 依赖: Ideal.count_associates_eq, Irreducible, RatFunc, WfDvdMonoid, WfDvdMonoid.max_power_factor, algebraMap, count_associates_eq, degree_lt_wf, degree_lt_wf.min_mem, irreducible_, irreducible_min_polynomial_valuation_lt_one_and_ne_zero, map_mul, map_pow, max_power_factor, mem_ofPred, min_mem, mul_one, ne_eq, nth_rw, setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty
-/
lemma valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one {p : K[X]}
    (hp : p != 0) :
    v (algebraMap K[X] (RatFunc K) p) = v (πᵥ ^ ((Associates.mk (Pᵥ).asIdeal).count
      (Associates.mk (Ideal.span {p})).factors)) := by
  set π := πᵥ
  have hne := setOfPred_polynomial_valuation_lt_one_and_ne_zero_nonempty hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π in _ := degree_lt_wf.min_mem _ hne
  simp only [ne_eq, mem_ofPred] at hπ
  nth_rw 1 [heq]
  simp only [map_mul, map_pow]
  suffices v (algebraMap K[X] (RatFunc K) q) = 1 by
    simp only [this, mul_one]
    congr
    exact (Ideal.count_associates_eq (irreducible_iff_prime.mp hπirr) hnq heq).symm
  rw [← mod_add_div q π]; rw [map_add]
  rw [← mod_eq_zero] at hnq
  suffices v (algebraMap K[X] (RatFunc K) (q % π)) = 1 ∧
      v (algebraMap K[X] (RatFunc K) (π * (q / π))) < 1 by
    obtain ⟨h₁, h₂⟩ := this
    rw [← h₁] at h₂ ⊢
    exact Valuation.map_add_eq_of_lt_left _ h₂
  constructor
  · rw [← coePolynomial_eq_algebraMap]
    have hnπ : q % π ∉ {p : K[X] | v ↑p < 1 ∧ p != 0} :=
      imp_not_comm.mp (degree_lt_wf.not_lt_min _) (EuclideanDomain.remainder_lt q hπ.2)
    have := Polynomial.valuation_le_one_of_valuation_X_le_one _ hle (q % π)
    grind
  · simpa only [map_mul, ← coePolynomial_eq_algebraMap]
using mul_lt_one_of_lt_of_le hπ.1 (q / π).valuation_le_one_of_valuation_X_le_one _ hle

/--
lemma `exists_zpow_uniformizingPolynomial` / 引理 `exists_zpow_uniformizingPolynomial`

English:
lemma exists_zpow_uniformizingPolynomial
  given: {f : RatFunc K} (hf : f != 0)
  proof: by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  induction f using RatFunc.induction_on with
  | f p q hq =>
    use (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors -
      (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).

中文:
引理 存在_zpow_uniformizingPolynomial
  条件: {f : 有理函数 K} (hf : f != 0)
  证明: by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  induction f using RatFunc.induction_on with
  | f p q hq =>
    use (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors -
      (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).

Depends on / 依赖: Associates, Associates.mk, Ideal.span, RatFunc, RatFunc.induction_on, asIdeal, factors, induction_on, map_pow, uniformizingPolynomial_ne_zero, valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_on, valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one, zpow_natCast
-/
lemma exists_zpow_uniformizingPolynomial {f : RatFunc K} (hf : f != 0) :
    exists (z : Int), v f = v πᵥ ^ z := by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  induction f using RatFunc.induction_on with
  | f p q hq =>
    use (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors -
      (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).factors
    simp only [map_div₀, map_pow, zpow_sub₀ h0, zpow_natCast,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle
        (p := p) (by aesop)]

/--
lemma `uniformizingPolynomial_isUniformizer` / 引理 `uniformizingPolynomial_isUniformizer`

English:
lemma uniformizingPolynomial_isUniformizer
  given: [hv : IsRankOneDiscrete v]
  proof: by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  rw [IsUniformizer]; rw [← hv.valueGroup_genLTOne_eq_generator]; rw [← h0.isUnit.unit_spec]; rw [Units.val_inj]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · rw [← Units.val_lt_val, h0.isUnit.unit_spec, Unit

中文:
引理 uniformizingPolynomial_isUniformizer
  条件: [hv : 是RankOneDiscrete v]
  证明: by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  rw [IsUniformizer]; rw [← hv.valueGroup_genLTOne_eq_generator]; rw [← h0.isUnit.unit_spec]; rw [Units.val_inj]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · rw [← Units.val_lt_val, h0.isUnit.unit_spec, Unit

Depends on / 依赖: IsUniformizer, LinearOrderedCommGroup, LinearOrderedCommGroup.Subgroup.genLTOne_unique, MonoidWithZeroHom, MonoidWithZeroHom.mem_valueGroup_iff_of_comm, Subgroup, Subgroup.mem_zpowers_iff, Units.val_inj, Units.val_lt_val, Units.val_one, coePolynomial_eq_algebraMap, genLTOne_unique, h0.isUnit.unit_spec, hv.valueGroup_genLTOne_eq_generator, isUnit, map_eq_zero, mem_valueGroup_iff_of_comm, mem_zpowers_iff, ne_eq, uniformizingPolynomial_ne_zero
-/
lemma uniformizingPolynomial_isUniformizer [hv : IsRankOneDiscrete v] :
    v.IsUniformizer πᵥ := by
  have h0 : v πᵥ != 0 := by simpa using uniformizingPolynomial_ne_zero hle
  rw [IsUniformizer]; rw [← hv.valueGroup_genLTOne_eq_generator]; rw [← h0.isUnit.unit_spec]; rw [Units.val_inj]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · rw [← Units.val_lt_val, h0.isUnit.unit_spec, Units.val_one]
    exact valuation_uniformizingPolynomial_lt_one hle
  · ext γ
    simp only [coePolynomial_eq_algebraMap, MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq,
      map_eq_zero, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨a, ha, b, hab⟩ => ?_⟩
    · use 1, one_ne_zero, πᵥ ^ k
      simp only [← Units.val_inj, Units.val_zpow_eq_zpow_val] at hk
      simp [← hk]
    · obtain ⟨ka, hka⟩ := exists_zpow_uniformizingPolynomial hle ha
      obtain ⟨kb, hkb⟩ := exists_zpow_uniformizingPolynomial hle (f := b) (by aesop)
      rw [MonoidWithZeroHom.coe_ofClass]; rw [hka]; rw [hkb] at hab
      use kb - ka
      have : v ↑πᵥ ^ ka != 0 := zpow_ne_zero _ h0
      simp [zpow_sub, ← Units.val_inj, ← coePolynomial_eq_algebraMap, field, ← hab]

/--
lemma `valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one` / 引理 `valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one`

English:
lemma valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one
  given: [IsRankOneDiscrete v]
  proof: by
  rw [isEquiv_iff_val_le_one]
  intro f
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p != 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc K) := uniformizingPolynomi

中文:
引理 valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one
  条件: [是RankOneDiscrete v]
  证明: by
  rw [isEquiv_iff_val_le_one]
  intro f
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p != 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc K) := uniformizingPolynomi

Depends on / 依赖: IsUniformizer, RatFunc, RatFunc.induction_on, div_inv_eq_mul, eq_or_ne, exp_neg, hpi_def, if_neg, induction_on, intValuation_def, isEquiv_iff_val_le_one, uniformizingPolynomial_isUniformizer, v.IsUniformizer, valuatio, valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one, valuation_of_algebraMap
-/
lemma valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDiscrete v] :
    v.IsEquiv ((Pᵥ).valuation (RatFunc K)) := by
  rw [isEquiv_iff_val_le_one]
  intro f
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p != 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc K) := uniformizingPolynomial_isUniformizer hle
      simp only [map_div₀, valuation_of_algebraMap, intValuation_def, exp_neg, if_neg hp0,
        if_neg hq0, div_inv_eq_mul]
      rw [valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hp0]; rw [valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq0]
      simp_all [div_le_one₀, inv_mul_le_one₀,
        (pow_le_pow_iff_right_of_lt_one₀ (by simp_all) (IsRankOneDiscrete.generator_lt_one v))]

end Associates

end valuation_X_le_one

/--
lemma `adicValuation_not_isEquiv_infty_valuation` / 引理 `adicValuation_not_isEquiv_infty_valuation`

English:
lemma adicValuation_not_isEquiv_infty_valuation
  statement: [DecidableEq (RatFunc K)]
  proof: by
  simp only [isEquiv_iff_val_le_one]
  push Not
  refine ⟨X, .inl ⟨p.valuation_le_one _, ?_⟩⟩
  rw [inftyValuation.X]; rw [← log_lt_iff_lt_exp one_ne_zero]; rw [log_one]
  exact zero_lt_one

中文:
引理 adicValuation_not_isEquiv_infty_valuation
  结论: [DecidableEq (有理函数 K)]
  证明: by
  simp only [isEquiv_iff_val_le_one]
  push Not
  refine ⟨X, .inl ⟨p.valuation_le_one _, ?_⟩⟩
  rw [inftyValuation.X]; rw [← log_lt_iff_lt_exp one_ne_zero]; rw [log_one]
  exact zero_lt_one

Depends on / 依赖: inftyValuation, inftyValuation.X, isEquiv_iff_val_le_one, log_lt_iff_lt_exp, log_one, one_ne_zero, p.valuation_le_one, valuation_le_one, zero_lt_one
-/
lemma adicValuation_not_isEquiv_infty_valuation [DecidableEq (RatFunc K)]
    (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    ¬ (p.valuation (RatFunc K)).IsEquiv (inftyValuation K) := by
  simp only [isEquiv_iff_val_le_one]
  push Not
  refine ⟨X, .inl ⟨p.valuation_le_one _, ?_⟩⟩
  rw [inftyValuation.X]; rw [← log_lt_iff_lt_exp one_ne_zero]; rw [log_one]
  exact zero_lt_one

/--
lemma `adicValuation_ne_inftyValuation` / 引理 `adicValuation_ne_inftyValuation`

English:
lemma adicValuation_ne_inftyValuation
  statement: [DecidableEq (RatFunc K)]
  proof: by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ adicValuation_not_isEquiv_infty_valuation p)

中文:
引理 adicValuation_ne_inftyValuation
  结论: [DecidableEq (有理函数 K)]
  证明: by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ adicValuation_not_isEquiv_infty_valuation p)

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.refl, absurd, adicValuation_not_isEquiv_infty_valuation
-/
lemma adicValuation_ne_inftyValuation [DecidableEq (RatFunc K)]
   (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    p.valuation (RatFunc K) != inftyValuation K := by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ adicValuation_not_isEquiv_infty_valuation p)

section Discrete

variable [IsRankOneDiscrete v]

section IsTrivialOn

variable [v.IsTrivialOn K]

/--
lemma `valuation_isEquiv_adic_of_valuation_X_le_one` / 引理 `valuation_isEquiv_adic_of_valuation_X_le_one`

English:
lemma valuation_isEquiv_adic_of_valuation_X_le_one
  given: (hle : v X <= 1)
  proof: ⟨_, valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle⟩

中文:
引理 valuation_isEquiv_adic_of_valuation_X_le_one
  条件: (hle : v X <= 1)
  证明: ⟨_, valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle⟩

Depends on / 依赖: valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one
-/
lemma valuation_isEquiv_adic_of_valuation_X_le_one (hle : v X <= 1) :
    exists (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  ⟨_, valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle⟩

/--
theorem `valuation_isEquiv_infty_or_adic` / 定理 `valuation_isEquiv_infty_or_adic`

English:
theorem valuation_isEquiv_infty_or_adic
  given: [DecidableEq (RatFunc K)]
  proof: by
  rcases lt_or_ge 1 (v X) with hlt | hge
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
    refine .inl ⟨hv, ?_⟩
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (adicValuation_not_is

中文:
定理 valuation_isEquiv_infty_or_adic
  条件: [DecidableEq (有理函数 K)]
  证明: by
  rcases lt_or_ge 1 (v X) with hlt | hge
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
    refine .inl ⟨hv, ?_⟩
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (adicValuation_not_is

Depends on / 依赖: lt_or_ge
-/
theorem valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc K)] :
    Xor (v.IsEquiv (RatFunc.inftyValuation K))
      (exists! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _)) := by
  rcases lt_or_ge 1 (v X) with hlt | hge
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
    refine .inl ⟨hv, ?_⟩
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)
  /- Prime case -/
  · obtain ⟨pw, hw⟩ := valuation_isEquiv_adic_of_valuation_X_le_one hge
    exact .inr ⟨⟨pw, hw, fun pw' hw' => eq_of_valuation_isEquiv_valuation (hw'.symm.trans hw)⟩,
      fun hv => absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)⟩

/--
lemma `valuation_isEquiv_adic_of_not_isEquiv_infty` / 引理 `valuation_isEquiv_adic_of_not_isEquiv_infty`

English:
lemma valuation_isEquiv_adic_of_not_isEquiv_infty
  statement: [DecidableEq (RatFunc K)]
  proof: valuation_isEquiv_infty_or_adic.or.resolve_left hni

中文:
引理 valuation_isEquiv_adic_of_not_isEquiv_infty
  结论: [DecidableEq (有理函数 K)]
  证明: valuation_isEquiv_infty_or_adic.or.resolve_left hni

Depends on / 依赖: resolve_left, valuation_isEquiv_infty_or_adic, valuation_isEquiv_infty_or_adic.or.resolve_left
-/
lemma valuation_isEquiv_adic_of_not_isEquiv_infty [DecidableEq (RatFunc K)]
    (hni : ¬ v.IsEquiv (RatFunc.inftyValuation K)) :
    exists! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  valuation_isEquiv_infty_or_adic.or.resolve_left hni

end IsTrivialOn

end Discrete

end RatFunc

end
