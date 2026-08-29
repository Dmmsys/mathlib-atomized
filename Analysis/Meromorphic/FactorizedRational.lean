/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form `∏ᶠ u, (· - u) ^ d u`, where `d : 𝕜 → ℤ` is
integer-valued. We show that these "factorized rational functions" are meromorphic in normal form,
with divisor equal to `d`.

Under suitable assumptions, we show that meromorphic functions are equivalent, modulo equality on
codiscrete sets, to the product of a factorized rational function and an analytic function without
zeros.

Implementation Note: For consistency, we use `∏ᶠ u, (· - u) ^ d u` throughout. If the support of `d`
is finite, then evaluation of functions commutes with finprod, and the helper lemma
`Function.FactorizedRational.finprod_eval` asserts that `∏ᶠ u, (· - u) ^ d u` equals the function
`fun x ↦ ∏ᶠ u, (x - u) ^ d u`. If `d` has infinite support, this equality is wrong in general.
There are elementary examples of functions `d` where `∏ᶠ u, (· - u) ^ d u` is constant one, while
`fun x ↦ ∏ᶠ u, (x - u) ^ d u` is not continuous.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜}

open Filter Function Real Set

namespace Function.FactorizedRational

/-!
## Elementary Properties of Factorized Rational Functions
-/

/--
lemma `mulSupport` / 引理 `mulSupport`

English:
lemma mulSupport
  given: (d : 𝕜 -> Int)
  proof: by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

中文:
引理 mulSupport
  条件: (d : 𝕜 -> 整数)
  证明: by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

Depends on / 依赖: mem_mulSupport, mem_support, ne_eq, ne_iff
-/
lemma mulSupport (d : 𝕜 -> Int) :
    (fun u => (· - u) ^ d u).mulSupport = d.support := by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finprod_eq_fun` / 引理 `finprod_eq_fun`

English:
lemma finprod_eq_fun
  given: {d : 𝕜 -> Int} (h : d.HasFiniteSupport)
  proof: by
  ext x
  rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]; rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]
  · simp
  · intro u
    contrapose
    simp_all
  · simp [mulSupport d]

中文:
引理 finprod_eq_fun
  条件: {d : 𝕜 -> 整数} (h : d.HasFiniteSupport)
  证明: by
  ext x
  rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]; rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]
  · simp
  · intro u
    contrapose
    simp_all
  · simp [mulSupport d]

Depends on / 依赖: contrapose, finprod_eq_prod_of_mulSupport_subset, h.toFinset, mulSupport, toFinset
-/
lemma finprod_eq_fun {d : 𝕜 -> Int} (h : d.HasFiniteSupport) :
    (∏ᶠ u, (· - u) ^ d u) = fun x => ∏ᶠ u, (x - u) ^ d u := by
  ext x
  rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]; rw [finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]
  · simp
  · intro u
    contrapose
    simp_all
  · simp [mulSupport d]

/--
theorem `analyticAt` / 定理 `analyticAt`

English:
theorem analyticAt
  given: {d : 𝕜 -> Int} {x : 𝕜} (h : 0 <= d x)
  proof: by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

中文:
定理 analyticAt
  条件: {d : 𝕜 -> 整数} {x : 𝕜} (h : 0 <= d x)
  证明: by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

Depends on / 依赖: AnalyticAt, AnalyticAt.fun_zpow, AnalyticAt.fun_zpow_nonneg, analyticAt_finprod, fun_prop, fun_zpow, fun_zpow_nonneg, sub_ne_zero
-/
theorem analyticAt {d : 𝕜 -> Int} {x : 𝕜} (h : 0 <= d x) :
    AnalyticAt 𝕜 (∏ᶠ u, (· - u) ^ d u) x := by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: {d : 𝕜 -> Int} {x : 𝕜} (h : d x = 0)
  proof: by
  by_cases h₁ : (fun u => (· - u) ^ d u).HasFiniteMulSupport
  · rw [finprod_eq_prod _ h₁, Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : x = z <;> simp_all [zpow_ne_zero, sub_ne_zero]
  · simp [finprod_of_infinite_mulSupport h₁]

中文:
定理 ne_zero
  条件: {d : 𝕜 -> 整数} {x : 𝕜} (h : d x = 0)
  证明: by
  by_cases h₁ : (fun u => (· - u) ^ d u).HasFiniteMulSupport
  · rw [finprod_eq_prod _ h₁, Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : x = z <;> simp_all [zpow_ne_zero, sub_ne_zero]
  · simp [finprod_of_infinite_mulSupport h₁]

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_ne_zero_iff, HasFiniteMulSupport, Pi.pow_apply, finprod_eq_prod, finprod_of_infinite_mulSupport, ne_eq, pow_apply, prod_apply, prod_ne_zero_iff, sub_ne_zero, zpow_ne_zero
-/
theorem ne_zero {d : 𝕜 -> Int} {x : 𝕜} (h : d x = 0) :
    (∏ᶠ u, (· - u) ^ d u) x != 0 := by
  by_cases h₁ : (fun u => (· - u) ^ d u).HasFiniteMulSupport
  · rw [finprod_eq_prod _ h₁, Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : x = z <;> simp_all [zpow_ne_zero, sub_ne_zero]
  · simp [finprod_of_infinite_mulSupport h₁]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
lemma `extractFactor` / 引理 `extractFactor`

English:
lemma extractFactor
  given: {d : 𝕜 -> Int} (u₀ : 𝕜) (hd : d.HasFiniteSupport)
  proof: by
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u => (fun x => x - u) ^ d u).mulSupport subseteq hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ in hd.toFinset := by simp_all
    rw [← Finset.mul_pro

中文:
引理 extractFactor
  条件: {d : 𝕜 -> 整数} (u₀ : 𝕜) (hd : d.HasFiniteSupport)
  证明: by
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u => (fun x => x - u) ^ d u).mulSupport subseteq hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ in hd.toFinset := by simp_all
    rw [← Finset.mul_pro

Depends on / 依赖: Finset, Finset.mul_prod_erase, eq_update_self_iff, finprod_eq_prod_of_mulS, finprod_eq_prod_of_mulSupport_subset, hd.toFinset, hd.toFinset.erase, mulSupport, mul_prod_erase, subseteq, toFinset, update
-/
lemma extractFactor {d : 𝕜 -> Int} (u₀ : 𝕜) (hd : d.HasFiniteSupport) :
    (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u)) := by
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u => (fun x => x - u) ^ d u).mulSupport subseteq hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ in hd.toFinset := by simp_all
    rw [← Finset.mul_prod_erase hd.toFinset _ this]
    congr 1
    have : (fun u => (· - u) ^ (update d u₀ 0 u)).mulSupport subseteq hd.toFinset.erase u₀ := by
      rw [mulSupport]
      intro x hx
      by_cases h₁x : x = u₀ <;> simp_all
    simp_all [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]

/--
theorem `meromorphicNFOn_univ` / 定理 `meromorphicNFOn_univ`

English:
theorem meromorphicNFOn_univ
  given: (d : 𝕜 -> Int)
  proof: by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    simp [analyticAt, ne_zero]
  · rw [← mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticO

中文:
定理 meromorphicNFOn_univ
  条件: (d : 𝕜 -> 整数)
  证明: by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    simp [analyticAt, ne_zero]
  · rw [← mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticO

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.meromorphicNFOn, Finite, analyticAt, analyticOnNhd_const, classical, d.support.Finite, extractFactor, finprod_of_infinite_mulSupport, meromorphicNFOn, mulSupport, ne_zero, support, update
-/
theorem meromorphicNFOn_univ (d : 𝕜 -> Int) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) univ := by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    simp [analyticAt, ne_zero]
  · rw [← mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticOnNhd_const

/--
theorem `meromorphicNFOn` / 定理 `meromorphicNFOn`

English:
theorem meromorphicNFOn
  given: (d : 𝕜 -> Int) (U : Set 𝕜)
  proof: fun _ _ => meromorphicNFOn_univ d (trivial)

中文:
定理 meromorphicNFOn
  条件: (d : 𝕜 -> 整数) (U : Set 𝕜)
  证明: fun _ _ => meromorphicNFOn_univ d (trivial)

Depends on / 依赖: meromorphicNFOn_univ
-/
theorem meromorphicNFOn (d : 𝕜 -> Int) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U := fun _ _ => meromorphicNFOn_univ d (trivial)

/-!
## Orders and Divisors of Factorized Rational Functions
-/

/--
theorem `meromorphicOrderAt_eq` / 定理 `meromorphicOrderAt_eq`

English:
theorem meromorphicOrderAt_eq
  given: {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport)
  proof: by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use ∏ᶠ u, (· - u) ^ update d z 0 u
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

中文:
定理 meromorphicOrderAt_eq
  条件: {z : 𝕜} (d : 𝕜 -> 整数) (h₁d : d.HasFiniteSupport)
  证明: by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use ∏ᶠ u, (· - u) ^ update d z 0 u
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

Depends on / 依赖: analyticAt, classical, extractFactor, filter_upwards, le_refl, mem_univ, meromorphicNFOn_univ, meromorphicOn, meromorphicOrderAt_eq_int_iff, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul, true_and, update, update_self
-/
theorem meromorphicOrderAt_eq {z : 𝕜} (d : 𝕜 -> Int) (h₁d : d.HasFiniteSupport) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z = d z := by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use ∏ᶠ u, (· - u) ^ update d z 0 u
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

/--
theorem `meromorphicOrderAt_ne_top` / 定理 `meromorphicOrderAt_ne_top`

English:
theorem meromorphicOrderAt_ne_top
  given: {z : 𝕜} (d : 𝕜 -> Int)
  proof: by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · rw [← mulSupport] at hd
    simp [finprod_of_infinite_mulSupport hd]

中文:
定理 meromorphicOrderAt_ne_top
  条件: {z : 𝕜} (d : 𝕜 -> 整数)
  证明: by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · rw [← mulSupport] at hd
    simp [finprod_of_infinite_mulSupport hd]

Depends on / 依赖: Finite, classical, d.support.Finite, finprod_of_infinite_mulSupport, meromorphicOrderAt_eq, mulSupport, support
-/
theorem meromorphicOrderAt_ne_top {z : 𝕜} (d : 𝕜 -> Int) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z != ⊤ := by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · rw [← mulSupport] at hd
    simp [finprod_of_infinite_mulSupport hd]

/--
theorem `divisor` / 定理 `divisor`

English:
theorem divisor
  given: {U : Set 𝕜} {D : locallyFinsuppWithin U Int} (hD : D.support.Finite)
  proof: by
  ext z
  by_cases hz : z in U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

中文:
定理 divisor
  条件: {U : Set 𝕜} {D : locallyFinsuppWithin U 整数} (hD : D.support.Finite)
  证明: by
  ext z
  by_cases hz : z in U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

Depends on / 依赖: meromorphicNFOn, meromorphicOn, meromorphicOrderAt_eq
-/
theorem divisor {U : Set 𝕜} {D : locallyFinsuppWithin U Int} (hD : D.support.Finite) :
    MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D := by
  ext z
  by_cases hz : z in U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

open scoped Classical in
/--
lemma `mulSupport_update` / 引理 `mulSupport_update`

English:
lemma mulSupport_update
  statement: {d : 𝕜 -> Int} {x : 𝕜}
  proof: by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

中文:
引理 mulSupport_update
  结论: {d : 𝕜 -> 整数} {x : 𝕜}
  证明: by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all
-/
private lemma mulSupport_update {d : 𝕜 -> Int} {x : 𝕜}
    (h : d.support.Finite) :
    (fun u => (x - u) ^ Function.update d x 0 u).mulSupport subseteq h.toFinset := by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Compute the trailing coefficient of the factorized rational function associated with `d : 𝕜 → ℤ`.
-/
/--
theorem `meromorphicTrailingCoeffAt_factorizedRational` / 定理 `meromorphicTrailingCoeffAt_factorizedRational`

English:
theorem meromorphicTrailingCoeffAt_factorizedRational
  given: {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFiniteSupport)
  proof: by
  have : (fun u => (· - u) ^ d u).mulSupport subseteq h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this]; rw [meromorphicTrailingCoeffAt_prod
      (fun _ => by fun_prop)]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_up

中文:
定理 meromorphicTrailingCoeffAt_factorizedRational
  条件: {d : 𝕜 -> 整数} {x : 𝕜} (h : d.HasFiniteSupport)
  证明: by
  have : (fun u => (· - u) ^ d u).mulSupport subseteq h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this]; rw [meromorphicTrailingCoeffAt_prod
      (fun _ => by fun_prop)]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_up

Depends on / 依赖: FactorizedRational, Finset, Finset.prod_congr, Function, Function.FactorizedRational.mulSupport, MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_zpow, finprod_eq_prod_of_mulSupport_subset, fun_prop, h.toFinset, meromorphi, meromorphicTrailingCoeffAt_id_sub_const, meromorphicTrailingCoeffAt_prod, meromorphicTrailingCoeffAt_zpow, mulSupport, mulSupport_update, prod_congr, subseteq, toFinset
-/
theorem meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFiniteSupport) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u => (· - u) ^ d u).mulSupport subseteq h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this]; rw [meromorphicTrailingCoeffAt_prod
      (fun _ => by fun_prop)]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  apply Finset.prod_congr rfl
  intro y hy
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
  by_cases hxy : x = y
  · rw [hxy, meromorphicTrailingCoeffAt_id_sub_const]
    simp_all
  · grind [meromorphicTrailingCoeffAt_id_sub_const]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `meromorphicTrailingCoeffAt_factorizedRational_off_support` / 定理 `meromorphicTrailingCoeffAt_factorizedRational_off_support`

English:
theorem meromorphicTrailingCoeffAt_factorizedRational_off_support
  statement: {d : 𝕜 -> Int} {x : 𝕜}
  proof: by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u => (x - u) ^ d u).mulSupport subseteq h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this

中文:
定理 meromorphicTrailingCoeffAt_factorizedRational_off_support
  结论: {d : 𝕜 -> 整数} {x : 𝕜}
  证明: by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u => (x - u) ^ d u).mulSupport subseteq h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this

Depends on / 依赖: Finset, Finset.prod_congr, Function, Function.update_of_ne, classical, contrapose, finprod_eq_prod_of_mulSupport_subset, meromorphicTrailingCoeffAt_factorizedRational, mulSupport, mulSupport_update, prod_congr, subseteq, toFinset, update_of_ne
-/
theorem meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 -> Int} {x : 𝕜}
    (h₁ : d.HasFiniteSupport) (h₂ : x ∉ d.support) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u => (x - u) ^ d u).mulSupport subseteq h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this]; rw [Finset.prod_congr rfl]
  intro y hy
  congr
  apply Function.update_of_ne
  by_contra hCon
  simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `log_norm_meromorphicTrailingCoeffAt` / 定理 `log_norm_meromorphicTrailingCoeffAt`

English:
theorem log_norm_meromorphicTrailingCoeffAt
  given: {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFiniteSupport)
  proof: by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : forall y in h.toFinset, ‖(x - y) ^ update d x 0 y‖ != 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zer

中文:
定理 log_norm_meromorphicTrailingCoeffAt
  条件: {d : 𝕜 -> 整数} {x : 𝕜} (h : d.HasFiniteSupport)
  证明: by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : forall y in h.toFinset, ‖(x - y) ^ update d x 0 y‖ != 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zer

Depends on / 依赖: Finset, Finset.sum_congr, classical, contrapose, finprod_eq_prod_of_mulSupport_subset, finsum_eq_sum_of_support_subset, h.toFinset, log_prod, meromorphicTrailingCoeffAt_factorizedRational, mulSupport_update, norm_prod, sub_ne_zero, subseteq, sum_congr, support, toFinset, update, zpow_ne_zero
-/
theorem log_norm_meromorphicTrailingCoeffAt {d : 𝕜 -> Int} {x : 𝕜} (h : d.HasFiniteSupport) :
    log ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h]; rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : forall y in h.toFinset, ‖(x - y) ^ update d x 0 y‖ != 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zero, sub_ne_zero]
  rw [norm_prod]; rw [log_prod this]
  have : (fun u => (d u) * log ‖x - u‖).support subseteq h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow]; rw [Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · rw [Function.update_of_ne (by tauto)]

end Function.FactorizedRational

open Function.FactorizedRational

/-!
## Elimination of Zeros and Poles

This section shows that every meromorphic function with finitely many zeros and poles is equivalent,
modulo equality on codiscrete sets, to the product of a factorized rational function and an analytic
function without zeros.

We provide analogous results for functions of the form `log ‖meromorphic‖`.
-/

/-
TODO: Identify some of the terms that appear in the decomposition.
-/

/--
theorem `MeromorphicOn.extract_zeros_poles` / 定理 `MeromorphicOn.extract_zeros_poles`

English:
theorem MeromorphicOn.extract_zeros_poles
  statement: {f : 𝕜 -> E} (h₁f : MeromorphicOn f U)
  proof: by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted to a meromorphic
  -- function in normal form. Then check all the properties.
  let φ := ∏ᶠ u, (· - u) ^ (divisor f U u)
  have hφ : MeromorphicOn φ U := (meromorphicNFOn (divisor f U) U).meromorphicOn
  let g := toMe

中文:
定理 MeromorphicOn.extract_zeros_poles
  结论: {f : 𝕜 -> E} (h₁f : MeromorphicOn f U)
  证明: by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted to a meromorphic
  -- function in normal form. Then check all the properties.
  let φ := ∏ᶠ u, (· - u) ^ (divisor f U u)
  have hφ : MeromorphicOn φ U := (meromorphicNFOn (divisor f U) U).meromorphicOn
  let g := toMe
-/
theorem MeromorphicOn.extract_zeros_poles {f : 𝕜 -> E} (h₁f : MeromorphicOn f U)
    (h₂f : forall u : U, meromorphicOrderAt f u != ⊤) (h₃f : (divisor f U).support.Finite) :
    exists g : 𝕜 -> E, AnalyticOnNhd 𝕜 g U ∧ (forall u : U, g u != 0) ∧
      f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ divisor f U u) • g := by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted to a meromorphic
  -- function in normal form. Then check all the properties.
  let φ := ∏ᶠ u, (· - u) ^ (divisor f U u)
  have hφ : MeromorphicOn φ U := (meromorphicNFOn (divisor f U) U).meromorphicOn
  let g := toMeromorphicNFOn (φ⁻¹ • f) U
  have hg : MeromorphicNFOn g U := by apply meromorphicNFOn_toMeromorphicNFOn
  refine ⟨g, ?_, ?_, ?_⟩
  · -- AnalyticOnNhd 𝕜 g U
    rw [← hg.divisor_nonneg_iff_analyticOnNhd]; rw [divisor_of_toMeromorphicNFOn (hφ.inv.smul h₁f)]; rw [divisor_smul hφ.inv h₁f _ (fun z hz => h₂f ⟨z]; rw [hz⟩)]; rw [divisor_inv]; rw [Function.FactorizedRational.divisor h₃f]; rw [neg_add_cancel]
    intro z hz
    simpa [meromorphicOrderAt_inv] using meromorphicOrderAt_ne_top (divisor f U)
  · -- ∀ (u : ↑U), g ↑u ≠ 0
    intro ⟨u, hu⟩
    rw [← (hg hu).meromorphicOrderAt_eq_zero_iff]; rw [← meromorphicOrderAt_congr
        (toMeromorphicNFOn_eq_self_on_nhdsNE (hφ.inv.smul h₁f) hu).symm]; rw [meromorphicOrderAt_smul (hφ u hu).inv (h₁f u hu)]; rw [meromorphicOrderAt_inv]; rw [meromorphicOrderAt_eq _ h₃f]
    simp only [h₁f, hu, divisor_apply]
    lift meromorphicOrderAt f u to Int using (h₂f ⟨u, hu⟩) with n hn
    rw [WithTop.untop₀_coe]; rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; rw [← WithTop.coe_add]
    simp
  · -- f =ᶠ[codiscreteWithin U] (∏ᶠ (u : 𝕜), fun z ↦ (z - u) ^ (divisor f U) u) * g
    filter_upwards [(divisor f U).eq_zero_codiscreteWithin,
      (hφ.inv.smul h₁f).meromorphicNFAt_mem_codiscreteWithin,
      self_mem_codiscreteWithin U] with a h₂a h₃a h₄a
    unfold g
    simp only [Pi.smul_apply', toMeromorphicNFOn_eq_toMeromorphicNFAt (hφ.inv.smul h₁f) h₄a,
      toMeromorphicNFAt_eq_self.2 h₃a, Pi.inv_apply]
    rw [← smul_assoc]; rw [smul_eq_mul]; rw [mul_inv_cancel₀ _]; rw [one_smul]
    rwa [← ((meromorphicNFOn_univ (divisor f U)) trivial).meromorphicOrderAt_eq_zero_iff,
      meromorphicOrderAt_eq, h₂a, Pi.zero_apply, WithTop.coe_zero]

/--
theorem `MeromorphicOn.extract_zeros_poles_log` / 定理 `MeromorphicOn.extract_zeros_poles_log`

English:
theorem MeromorphicOn.extract_zeros_poles_log
  statement: {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U Int}
  proof: by
  -- Identify support of the sum in the goal
  have t₁ : (fun u => (D u * log ‖· - u‖)).support = D.support := by
    ext u
    rw [← not_iff_not]
    simp only [ne_eq, not_not, Function.mem_support]
    constructor <;> intro hx
    · obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm 𝕜
      have 

中文:
定理 MeromorphicOn.extract_zeros_poles_log
  结论: {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U 整数}
  证明: by
  -- Identify support of the sum in the goal
  have t₁ : (fun u => (D u * log ‖· - u‖)).support = D.support := by
    ext u
    rw [← not_iff_not]
    simp only [ne_eq, not_not, Function.mem_support]
    constructor <;> intro hx
    · obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm 𝕜
      have 
-/
theorem MeromorphicOn.extract_zeros_poles_log {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U Int}
    (hg : forall u : U, g u != 0) (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    (log ‖f ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * log ‖· - u‖) + (log ‖g ·‖) := by
  -- Identify support of the sum in the goal
  have t₁ : (fun u => (D u * log ‖· - u‖)).support = D.support := by
    ext u
    rw [← not_iff_not]
    simp only [ne_eq, not_not, Function.mem_support]
    constructor <;> intro hx
    · obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm 𝕜
      have := congrFun hx (y + u)
      simp only [add_sub_cancel_right, Pi.zero_apply, mul_eq_zero, Int.cast_eq_zero, log_eq_zero,
        norm_eq_zero] at this
      rcases this with h | h | h | h
      · assumption
      · simp only [h, norm_zero] at hy
        linarith
      · simp only [h, lt_self_iff_false] at hy
      · simp only [h, lt_neg_self_iff] at hy
        linarith
    · simp_all [Pi.zero_def]
  -- Trivial case: the support of D is infinite
  by_cases h₃f : D.support.Finite
  case neg =>
    rw [finsum_of_infinite_support (by simpa [t₁] using h₃f)]
    rw [finprod_of_infinite_mulSupport (by simpa [FactorizedRational.mulSupport] using h₃f)] at h
    filter_upwards [h] with x hx
    simp [hx]
  -- General case
  filter_upwards [h, D.eq_zero_codiscreteWithin, self_mem_codiscreteWithin U] with z hz h₂z h₃z
  rw [Pi.zero_apply] at h₂z
  rw [hz]; rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _
      (by simp_all [FactorizedRational.mulSupport]),
    finsum_eq_sum_of_support_subset (s := h₃f.toFinset) _ (by simp_all)]
  have : forall x in h₃f.toFinset, ‖z - x‖ ^ D x != 0 := by
    intro x hx
    rw [Finite.mem_toFinset]; rw [Function.mem_support] at hx
    rw [ne_eq]; rw [zpow_eq_zero_iff hx]; rw [norm_eq_zero]; rw [sub_eq_zero]; rw [eq_comm]
    apply ne_of_apply_ne D
    rwa [h₂z]
  simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply, norm_smul, norm_prod, norm_zpow]
  rw [log_mul (Finset.prod_ne_zero_iff.2 this) (by simp [hg ⟨z]; rw [h₃z⟩]), log_prod this]
  simp [log_zpow]

open scoped Classical in
/--
theorem `MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles` / 定理 `MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles`

English:
theorem MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
  proof: by
  have t₀ : MeromorphicAt (∏ᶠ u, (· - u) ^ D u) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h)]; rw [t₀.meromorphicTrailingCoeffAt_smul h₁g.

中文:
定理 MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
  证明: by
  have t₀ : MeromorphicAt (∏ᶠ u, (· - u) ^ D u) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h)]; rw [t₀.meromorphicTrailingCoeffAt_smul h₁g.

Depends on / 依赖: FactorizedRational, FactorizedRational.meromorphicNFOn, MeromorphicAt, eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, fun_prop, g.meromorphicAt, g.meromorphicTrailingCoeffAt_of_ne_zero, hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, meromorphicAt, meromorphicNFOn, meromorphicOn, meromorphicTrailingCoeffAt_congr_nhdsNE, meromorphicTrailingCoeffAt_factorizedRational, meromorphicTrailingCoeffAt_of_ne_zero, meromorphicTrailingCoeffAt_smul
-/
theorem MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 -> E} {D : 𝕜 -> Int} (hD : D.HasFiniteSupport) (h₁x : x in U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0)
    (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    meromorphicTrailingCoeffAt f x = (∏ᶠ u, (x - u) ^ Function.update D x 0 u) • g x := by
  have t₀ : MeromorphicAt (∏ᶠ u, (· - u) ^ D u) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h)]; rw [t₀.meromorphicTrailingCoeffAt_smul h₁g.meromorphicAt]; rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g]
  simp [meromorphicTrailingCoeffAt_factorizedRational hD]

/--
theorem `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles` / 定理 `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles`

English:
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
  proof: by
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).smul h₁g.meromorphicAt)
          h₁x h₂x h)]; rw [((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).me

中文:
定理 MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
  证明: by
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).smul h₁g.meromorphicAt)
          h₁x h₂x h)]; rw [((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).me

Depends on / 依赖: FactorizedRational, FactorizedRational.meromorphicNFOn, Meromorphi, eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, g.meromorphicAt, g.meromorphicTrailingCoeffAt_of_ne_zero, hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, log_mul, log_norm_meromorphicTrailingCoeffAt, meromorphicAt, meromorphicNFOn, meromorphicOn, meromorphicTrailingCoeffAt_congr_nhdsNE, meromorphicTrailingCoeffAt_of_ne_zero, meromorphicTrailingCoeffAt_smul, ne_eq, norm_eq_zero, norm_smul
-/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 -> E} {D : 𝕜 -> Int} (hD : D.HasFiniteSupport) (h₁x : x in U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0)
    (h : f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    log ‖meromorphicTrailingCoeffAt f x‖ = ∑ᶠ u, (D u) * log ‖x - u‖ + log ‖g x‖ := by
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).smul h₁g.meromorphicAt)
          h₁x h₂x h)]; rw [((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).meromorphicTrailingCoeffAt_smul
      h₁g.meromorphicAt]; rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g]; rw [norm_smul]; rw [log_mul]; rw [log_norm_meromorphicTrailingCoeffAt hD]
  · simp only [ne_eq, norm_eq_zero]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
      ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x)
    apply FactorizedRational.meromorphicOrderAt_ne_top
  · simp_all
