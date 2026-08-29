/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function, that is
the coefficients are divides by `∏ i, Gamma (b i)`, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

This definition is valid for all values of `c`, whereas the usual hypergeometric function has a
pole for `c = -k` and `k : ℕ`. To our knowledge the regularized hypergeometric function only appears
in the literature only for the Gaussian case, it is implicit in the definition of the Bessel
function (`p = 0` and `q = 1`).
To recover the usual hypergeometric function, simply multiply by `∏ i, Gamma (b i)`.

## Definitions
For the general case we have
* `Complex.regularizedHGFunCoeff`: the coefficients
* `Complex.regularizedHGFunSeries`: the formal multilinear series
* `Complex.regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `Complex.regularizedGaussHGFunSeries`: the formal multilinear series
* `Complex.regularizedGaussHGFun`: the function

## Results

Convergence:
* `radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `Complex.radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/

@[expose] public noncomputable section

namespace Complex

open scoped Nat Real
open Topology Filter

variable {p q : Nat}

variable {a : Multiset Complex} {b : Multiset Complex} {n m : Nat} {j k : Complex}

/--
Definition of `regularizedHGFunCoeff` / `regularizedHGFunCoeff` 的定义

English:
definition regularizedHGFunCoeff
  signature: (a : Multiset Complex) (b : Multiset Complex) (n : Nat)
  body: (a.map (ascPochhammer Complex n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

中文:
定义 regularizedHGFunCoeff
  签名: (a : Multiset Complex) (b : Multiset Complex) (n : 自然数)
  定义体: (a.map (ascPochhammer Complex n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

Depends on / 依赖: a.map, ascPochhammer, b.map
-/
def regularizedHGFunCoeff (a : Multiset Complex) (b : Multiset Complex) (n : Nat) : Complex :=
  (a.map (ascPochhammer Complex n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

attribute [grind .] Nat.factorial_ne_zero

@[grind =]
/--
theorem `regularizedHGFunCoeff_eq_zero_iff` / 定理 `regularizedHGFunCoeff_eq_zero_iff`

English:
theorem regularizedHGFunCoeff_eq_zero_iff
  proof: by
  unfold regularizedHGFunCoeff
  simp
  grind

中文:
定理 regularizedHGFunCoeff_eq_zero_iff
  证明: by
  unfold regularizedHGFunCoeff
  simp
  grind

Depends on / 依赖: regularizedHGFunCoeff
-/
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (exists j in a, exists k < n, j = -k) ∨ exists j in b, exists (m : Nat), j + n = -m := by
  unfold regularizedHGFunCoeff
  simp
  grind

variable (a b n m) in
/--
theorem `regularizedHGFunCoeff_eq_zero_right` / 定理 `regularizedHGFunCoeff_eq_zero_right`

English:
theorem regularizedHGFunCoeff_eq_zero_right
  given: (hb : -(n : Complex) - m in b := by grind)
  proof: by grind

中文:
定理 regularizedHGFunCoeff_eq_zero_right
  条件: (hb : -(n : Complex) - m in b := by grind)
  证明: by grind

Depends on / 依赖: regularizedHGFunCoeff
-/
theorem regularizedHGFunCoeff_eq_zero_right (hb : -(n : Complex) - m in b := by grind) :
    regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n m) in
/--
theorem `regularizedHGFunCoeff_eq_zero_left` / 定理 `regularizedHGFunCoeff_eq_zero_left`

English:
theorem regularizedHGFunCoeff_eq_zero_left
  statement: (ha : -(m : Complex) in a := by grind)
  proof: by grind

中文:
定理 regularizedHGFunCoeff_eq_zero_left
  结论: (ha : -(m : Complex) in a := by grind)
  证明: by grind

Depends on / 依赖: regularizedHGFunCoeff
-/
theorem regularizedHGFunCoeff_eq_zero_left (ha : -(m : Complex) in a := by grind)
    (hm : m < n := by grind) :
  regularizedHGFunCoeff a b n = 0 := by grind

/--
theorem `regularizedHGFunCoeff_add_one` / 定理 `regularizedHGFunCoeff_add_one`

English:
theorem regularizedHGFunCoeff_add_one
  given: (hb : forall k in b, k != -n)
  proof: calc
  _ = (a.map fun i => ((ascPochhammer Complex n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j => Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · 

中文:
定理 regularizedHGFunCoeff_add_one
  条件: (hb : 对任意 k in b, k != -n)
  证明: calc
  _ = (a.map fun i => ((ascPochhammer Complex n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j => Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · 
-/
theorem regularizedHGFunCoeff_add_one (hb : forall k in b, k != -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((a.map (· + (n : Complex))).prod / ((b.map (· + (n : Complex))).prod * (n + 1))) := calc
  _ = (a.map fun i => ((ascPochhammer Complex n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j => Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      grind
    · refine Multiset.map_congr rfl (fun j hj => ?_)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      grind
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Multiset.prod_map_mul]
    ring

/--
theorem `regularizedHGFunCoeff_add_one_div_self` / 定理 `regularizedHGFunCoeff_add_one_div_self`

English:
theorem regularizedHGFunCoeff_add_one_div_self
  given: (h : regularizedHGFunCoeff a b n != 0)
  proof: by
  by_cases! hb : forall k in b, k != -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : Complex))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]

中文:
定理 regularizedHGFunCoeff_add_one_div_self
  条件: (h : regularizedHGFunCoeff a b n != 0)
  证明: by
  by_cases! hb : forall k in b, k != -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : Complex))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.prod_eq_zero, b.map, mem_map, prod_eq_zero, regularizedHGFunCoeff_add_one, regularizedHGFunCoeff_eq_zero_right
-/
theorem regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n != 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (a.map (· + (n : Complex))).prod / ((b.map (· + (n : Complex))).prod * (n + 1)) := by
  by_cases! hb : forall k in b, k != -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : Complex))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]

/--
theorem `multiset_prod_eq_pow_mul_multiset_prod` / 定理 `multiset_prod_eq_pow_mul_multiset_prod`

English:
theorem multiset_prod_eq_pow_mul_multiset_prod
  given: (a : Multiset Complex) (hn : n != 0)
  proof: calc
  _ = (a.map (fun j => n * (j / (n : Complex) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private

中文:
定理 multiset_prod_eq_pow_mul_multiset_prod
  条件: (a : Multiset Complex) (hn : n != 0)
  证明: calc
  _ = (a.map (fun j => n * (j / (n : Complex) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private
-/
private theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset Complex) (hn : n != 0) :
    (a.map (· + (n : Complex))).prod = n ^ a.card * (a.map (· / (n : Complex) + 1)).prod := calc
  _ = (a.map (fun j => n * (j / (n : Complex) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private
/--
theorem `multiset_prod_div_multiset_prod_mul` / 定理 `multiset_prod_div_multiset_prod_mul`

English:
theorem multiset_prod_div_multiset_prod_mul
  given: (a : Multiset Complex) (b : Multiset Complex) (hn : n != 0)
  proof: by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn]; rw [multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : Int)) *
        (a.map (fun x : Complex => (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ']; rw [← z

中文:
定理 multiset_prod_div_multiset_prod_mul
  条件: (a : Multiset Complex) (b : Multiset Complex) (hn : n != 0)
  证明: by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn]; rw [multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : Int)) *
        (a.map (fun x : Complex => (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ']; rw [← z

Depends on / 依赖: a.card, a.map, b.card, multiset_prod_eq_pow_mul_multiset_prod, pow_succ, zpow_add, zpow_natCast
-/
theorem multiset_prod_div_multiset_prod_mul (a : Multiset Complex) (b : Multiset Complex) (hn : n != 0) :
    (a.map (· + (n : Complex))).prod / ((b.map (· + (n : Complex))).prod * (n + 1)) =
      n ^ (a.card - (b.card : Int) - 1) * (a.map (· / (n : Complex) + 1)).prod /
      ((b.map (· / (n : Complex) + 1)).prod * (1 + (n : Complex)⁻¹)) := by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn]; rw [multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : Int)) *
        (a.map (fun x : Complex => (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ']; rw [← zpow_natCast]; rw [← zpow_natCast]; rw [← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

variable (a b) in
/--
Definition of `regularizedHGFunSeries` / `regularizedHGFunSeries` 的定义

English:
definition regularizedHGFunSeries
  signature: : FormalMultilinearSeries Complex Complex Complex
  body: .ofScalars Complex (regularizedHGFunCoeff a b)

@[simp]

中文:
定义 regularizedHGFunSeries
  签名: : FormalMultilinearSeries Complex Complex Complex
  定义体: .ofScalars Complex (regularizedHGFunCoeff a b)

@[simp]

Depends on / 依赖: ofScalars, regularizedHGFunCoeff
-/
def regularizedHGFunSeries : FormalMultilinearSeries Complex Complex Complex :=
  .ofScalars Complex (regularizedHGFunCoeff a b)

@[simp]
/--
theorem `regularizedHGFunSeries_coeff` / 定理 `regularizedHGFunSeries_coeff`

English:
theorem regularizedHGFunSeries_coeff
  proof: by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]

中文:
定理 regularizedHGFunSeries_coeff
  证明: by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]

Depends on / 依赖: regularizedHGFunSeries
-/
theorem regularizedHGFunSeries_coeff :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
/--
theorem `regularizedHGFunSeries_eq_zero` / 定理 `regularizedHGFunSeries_eq_zero`

English:
theorem regularizedHGFunSeries_eq_zero
  proof: by
  apply FormalMultilinearSeries.ofScalars_eq_zero

中文:
定理 regularizedHGFunSeries_eq_zero
  证明: by
  apply FormalMultilinearSeries.ofScalars_eq_zero

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_eq_zero, ofScalars_eq_zero
-/
theorem regularizedHGFunSeries_eq_zero :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

variable (a b) in
/--
Definition of `regularizedHGFun` / `regularizedHGFun` 的定义

English:
definition regularizedHGFun
  signature: (z : Complex)
  body: (regularizedHGFunSeries a b).sum z

中文:
定义 regularizedHGFun
  签名: (z : Complex)
  定义体: (regularizedHGFunSeries a b).sum z

Depends on / 依赖: regularizedHGFunSeries
-/
def regularizedHGFun (z : Complex) : Complex := (regularizedHGFunSeries a b).sum z

/--
theorem `radius_regularizedHGFunSeries_eq_top_of_finite` / 定理 `radius_regularizedHGFunSeries_eq_top_of_finite`

English:
theorem radius_regularizedHGFunSeries_eq_top_of_finite
  given: (ha : j in a) (hj : j = -n)
  proof: by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

中文:
定理 radius_regularizedHGFunSeries_eq_top_of_finite
  条件: (ha : j in a) (hj : j = -n)
  证明: by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero, eventually_atTop, eventually_atTop.mpr, radius_eq_top_of_eventually_eq_zero
-/
theorem radius_regularizedHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

variable (b) in
/--
theorem `eventually_atTop_regularizedHGFunCoeff_ne_zero` / 定理 `eventually_atTop_regularizedHGFunCoeff_ne_zero`

English:
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero
  given: (h : forall j in a, forall (k : Nat), j != -↑k)
  proof: by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : Real) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] u

中文:
定理 eventually_atTop_regularizedHGFunCoeff_ne_zero
  条件: (h : 对任意 j in a, 对任意 (k : 自然数), j != -↑k)
  证明: by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : Real) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] u

Depends on / 依赖: Filter, Filter.eventually_atTop, Finset, Finset.le_sup, Nat.le_ceil, b.toFinset.sup, eventually_atTop, j.re, le_ceil, le_sup, mod_cast, regularizedHGFunCoeff_eq_zero_iff, toFinset
-/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero (h : forall j in a, forall (k : Nat), j != -↑k) :
    forallᶠ (n : Nat) in atTop, regularizedHGFunCoeff a b n != 0 := by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : Real) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] using this
    calc
      -j.re <= ⌈-j.re⌉₊ := Nat.le_ceil (-j.re)
      _ <= b.toFinset.sup (⌈-re ·⌉₊) := mod_cast Finset.le_sup (by grind) (f := (⌈-re ·⌉₊))
      _ < n := by norm_cast

variable (a) in
/--
theorem `tendsto_multiset_prod_div_add_one` / 定理 `tendsto_multiset_prod_div_add_one`

English:
theorem tendsto_multiset_prod_div_add_one
  proof: by
  suffices forall i in a, Tendsto (fun n : Nat => (i / n + 1)) atTop (𝓝 <| (fun _ : _ => 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

中文:
定理 tendsto_multiset_prod_div_add_one
  证明: by
  suffices forall i in a, Tendsto (fun n : Nat => (i / n + 1)) atTop (𝓝 <| (fun _ : _ => 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1
-/
private theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : Nat => (a.map (· / (n : Complex) + 1)).prod) atTop (𝓝 1) := by
  suffices forall i in a, Tendsto (fun n : Nat => (i / n + 1)) atTop (𝓝 <| (fun _ : _ => 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b) in
/--
theorem `tendsto_multiset_prod_div_multiset_prod_mul` / 定理 `tendsto_multiset_prod_div_multiset_prod_mul`

English:
theorem tendsto_multiset_prod_div_multiset_prod_mul
  proof: by
  have h : Tendsto (fun n : Nat => (n : Complex)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, 

中文:
定理 tendsto_multiset_prod_div_multiset_prod_mul
  证明: by
  have h : Tendsto (fun n : Nat => (n : Complex)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, 
-/
private theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : Nat => (a.map (· / (n : Complex) + 1)).prod /
      ((b.map (· / (n : Complex) + 1)).prod * (1 + (n : Complex)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : Nat => (n : Complex)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/
@[grind =]
/--
theorem `radius_regularizedHGFunSeries_eq_top` / 定理 `radius_regularizedHGFunSeries_eq_top`

English:
theorem radius_regularizedHGFunSeries_eq_top
  given: (h : a.card <= b.card)
  proof: by
  by_cases! ha : exists j in a, exists k : Nat, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat

中文:
定理 radius_regularizedHGFunSeries_eq_top
  条件: (h : a.card <= b.card)
  证明: by
  by_cases! ha : exists j in a, exists k : Nat, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto, Nat.succ_eq_add_one, Tendsto, a.card, b.card, eventually_atTop_regularizedHGFunCoeff_ne_zero, ofScalars_radius_eq_top_of_tendsto, radius_regularizedHGFunSeries_eq_top_of_finite, succ_eq_add_one, tendsto_one_div_atTop_nhds_zero_nat
-/
theorem radius_regularizedHGFunSeries_eq_top (h : a.card <= b.card) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : exists j in a, exists k : Nat, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : Nat) => (n : Complex) ^ (a.card - (b.card : Int) - 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Complex)).pow (b.card + 1 - a.card)
      rw [zero_pow (by grind)] at this
      apply this.congr
      intro n
      rw [one_div]; rw [inv_pow]; rw [← zpow_natCast]; rw [← zpow_neg]; rw [Int.ofNat_sub (by grind)]; rw [Int.natCast_add_one]
      ring_nf
    have := (h₁.mul (tendsto_multiset_prod_div_multiset_prod_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    rw [← Complex.norm_div]; rw [regularizedHGFunCoeff_add_one_div_self hn₁]; rw [multiset_prod_div_multiset_prod_mul a b hn₂]; rw [mul_div]

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/
@[grind =]
/--
theorem `radius_regularizedHGFunSeries_eq_one` / 定理 `radius_regularizedHGFunSeries_eq_one`

English:
theorem radius_regularizedHGFunSeries_eq_one
  statement: (h : a.card = b.card + 1)
  proof: by
  have : Tendsto (fun n => ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_

中文:
定理 radius_regularizedHGFunSeries_eq_one
  结论: (h : a.card = b.card + 1)
  证明: by
  have : Tendsto (fun n => ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_

Depends on / 依赖: Complex.norm_div, Filter, Filter.eventually_ne_atTop, Nat.succ_eq_add_one, Tendsto, eventually_atTop_regularizedHGFunCoeff_ne_zero, eventually_ne_atTop, filter_upwards, h_ne, multiset_prod_div_multiset_prod_mul, n.succ, norm_div, norm_one, regularizedHGFunCoeff, regularizedHGFunCoeff_add_one_div_self, succ_eq_add_one, tendsto_multiset_prod_div_multiset_prod_mul, this.congr
-/
theorem radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1)
    (h' : forall j in a, forall k : Nat, j != -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n => ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b h'
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    simp [Nat.succ_eq_add_one, ← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) Complex _ (by simp) this
  simpa

/--
theorem `radius_regularizedHGFunSeries_ge_one` / 定理 `radius_regularizedHGFunSeries_ge_one`

English:
theorem radius_regularizedHGFunSeries_ge_one
  given: (h : a.card = b.card + 1)
  proof: by
  by_cases! h' : forall j in a, forall k : Nat, j != -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

中文:
定理 radius_regularizedHGFunSeries_ge_one
  条件: (h : a.card = b.card + 1)
  证明: by
  by_cases! h' : forall j in a, forall k : Nat, j != -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

Depends on / 依赖: radius_regularizedHGFunSeries_eq_top_of_finite
-/
theorem radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) :
    1 <= (regularizedHGFunSeries a b).radius := by
  by_cases! h' : forall j in a, forall k : Nat, j != -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp, grind =]
/--
theorem `regularizedHGFunSeries_zero_zero` / 定理 `regularizedHGFunSeries_zero_zero`

English:
theorem regularizedHGFunSeries_zero_zero
  proof: by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

中文:
定理 regularizedHGFunSeries_zero_zero
  证明: by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

Depends on / 依赖: NormedSpace, NormedSpace.expSeries, expSeries, regularizedHGFunCoeff
-/
theorem regularizedHGFunSeries_zero_zero :
    regularizedHGFunSeries 0 0 = NormedSpace.expSeries Complex Complex := by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp, grind =]
/--
theorem `regularizedHGFun_zero_zero` / 定理 `regularizedHGFun_zero_zero`

English:
theorem regularizedHGFun_zero_zero
  statement: regularizedHGFun 0 0 = exp
  proof: by
  rw [exp_eq_exp_Complex]; rw [NormedSpace.exp_eq_expSeries_sum (𝕂 := Complex)]
  unfold regularizedHGFun
  simp

中文:
定理 regularizedHGFun_zero_zero
  结论: regularizedHGFun 0 0 = exp
  证明: by
  rw [exp_eq_exp_Complex]; rw [NormedSpace.exp_eq_expSeries_sum (𝕂 := Complex)]
  unfold regularizedHGFun
  simp

Depends on / 依赖: NormedSpace, NormedSpace.exp_eq_expSeries_sum, exp_eq_expSeries_sum, exp_eq_exp_Complex, regularizedHGFun
-/
theorem regularizedHGFun_zero_zero : regularizedHGFun 0 0 = exp := by
  rw [exp_eq_exp_Complex]; rw [NormedSpace.exp_eq_expSeries_sum (𝕂 := Complex)]
  unfold regularizedHGFun
  simp

end ZeroZero

section Gaussian

/--
Definition of `regularizedGaussHGFunSeries` / `regularizedGaussHGFunSeries` 的定义

English:
definition regularizedGaussHGFunSeries
  signature: (a b c : Complex)
  body: regularizedHGFunSeries {a, b} {c}

中文:
定义 regularizedGaussHGFunSeries
  签名: (a b c : Complex)
  定义体: regularizedHGFunSeries {a, b} {c}

Depends on / 依赖: regularizedHGFunSeries
-/
def regularizedGaussHGFunSeries (a b c : Complex) : FormalMultilinearSeries Complex Complex Complex :=
  regularizedHGFunSeries {a, b} {c}

/--
Definition of `regularizedGaussHGFun` / `regularizedGaussHGFun` 的定义

English:
definition regularizedGaussHGFun
  signature: (a b c z : Complex)
  body: (regularizedGaussHGFunSeries a b c).sum z

中文:
定义 regularizedGaussHGFun
  签名: (a b c z : Complex)
  定义体: (regularizedGaussHGFunSeries a b c).sum z

Depends on / 依赖: regularizedGaussHGFunSeries
-/
def regularizedGaussHGFun (a b c z : Complex) : Complex :=
  (regularizedGaussHGFunSeries a b c).sum z

variable {a b c z : Complex}

variable (a b c) in
/--
theorem `regularizedGaussHGFunSeries_symm` / 定理 `regularizedGaussHGFunSeries_symm`

English:
theorem regularizedGaussHGFunSeries_symm
  proof: by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

中文:
定理 regularizedGaussHGFunSeries_symm
  证明: by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

Depends on / 依赖: Multiset, Multiset.pair_comm, pair_comm, regularizedGaussHGFunSeries
-/
theorem regularizedGaussHGFunSeries_symm :
    regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c := by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

variable (a b c) in
/--
theorem `regularizedGaussHGFun_symm` / 定理 `regularizedGaussHGFun_symm`

English:
theorem regularizedGaussHGFun_symm
  proof: by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]

中文:
定理 regularizedGaussHGFun_symm
  证明: by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]

Depends on / 依赖: regularizedGaussHGFun, regularizedGaussHGFunSeries_symm
-/
theorem regularizedGaussHGFun_symm :
    regularizedGaussHGFun a b c = regularizedGaussHGFun b a c := by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]

/--
theorem `coeff_regularizedGaussHGFunSeries` / 定理 `coeff_regularizedGaussHGFunSeries`

English:
theorem coeff_regularizedGaussHGFunSeries
  proof: by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

中文:
定理 coeff_regularizedGaussHGFunSeries
  证明: by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

Depends on / 依赖: regularizedGaussHGFunSeries, regularizedHGFunCoeff
-/
theorem coeff_regularizedGaussHGFunSeries :
    (a.regularizedGaussHGFunSeries b c).coeff n =
    ((ascPochhammer Complex n).eval a * (ascPochhammer Complex n).eval b) / (n ! * Gamma (c + n)) := by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

/--
theorem `Gamma_inv_mul_ordinaryHypergeometricSeries_eq` / 定理 `Gamma_inv_mul_ordinaryHypergeometricSeries_eq`

English:
theorem Gamma_inv_mul_ordinaryHypergeometricSeries_eq
  given: (hc : forall k : Nat, c != -k) {n : Nat}
  proof: by
  rw [coeff_regularizedGaussHGFunSeries]; rw [ordinaryHypergeometricSeries]; rw [FormalMultilinearSeries.coeff_ofScalars]; rw [ordinaryHypergeometricCoefficient]; rw [← Gamma_add_nat_div_Gamma_eq c hc]
  grind

中文:
定理 Gamma_inv_mul_ordinaryHypergeometricSeries_eq
  条件: (hc : 对任意 k : 自然数, c != -k) {n : 自然数}
  证明: by
  rw [coeff_regularizedGaussHGFunSeries]; rw [ordinaryHypergeometricSeries]; rw [FormalMultilinearSeries.coeff_ofScalars]; rw [ordinaryHypergeometricCoefficient]; rw [← Gamma_add_nat_div_Gamma_eq c hc]
  grind

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars, Gamma_add_nat_div_Gamma_eq, coeff_ofScalars, coeff_regularizedGaussHGFunSeries, ordinaryHypergeometricCoefficient, ordinaryHypergeometricSeries
-/
theorem Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : forall k : Nat, c != -k) {n : Nat} :
    (Gamma c)⁻¹ * (ordinaryHypergeometricSeries Complex a b c).coeff n =
      (a.regularizedGaussHGFunSeries b c).coeff n := by
  rw [coeff_regularizedGaussHGFunSeries]; rw [ordinaryHypergeometricSeries]; rw [FormalMultilinearSeries.coeff_ofScalars]; rw [ordinaryHypergeometricCoefficient]; rw [← Gamma_add_nat_div_Gamma_eq c hc]
  grind

/--
theorem `ordinaryHypergeometric_div_Gamma_eq` / 定理 `ordinaryHypergeometric_div_Gamma_eq`

English:
theorem ordinaryHypergeometric_div_Gamma_eq
  given: (hc : forall k : Nat, c != -k)
  proof: by
  rw [regularizedGaussHGFun]; rw [ordinaryHypergeometric]; rw [div_eq_inv_mul]; rw [← smul_eq_mul]; rw [FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

中文:
定理 ordinaryHypergeometric_div_Gamma_eq
  条件: (hc : 对任意 k : 自然数, c != -k)
  证明: by
  rw [regularizedGaussHGFun]; rw [ordinaryHypergeometric]; rw [div_eq_inv_mul]; rw [← smul_eq_mul]; rw [FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.const_smul_sum_apply, Gamma_inv_mul_ordinaryHypergeometricSeries_eq, const_smul_sum_apply, div_eq_inv_mul, ordinaryHypergeometric, regularizedGaussHGFun, smul_eq_mul
-/
theorem ordinaryHypergeometric_div_Gamma_eq (hc : forall k : Nat, c != -k) :
    ordinaryHypergeometric a b c z / Gamma c = regularizedGaussHGFun a b c z := by
  rw [regularizedGaussHGFun]; rw [ordinaryHypergeometric]; rw [div_eq_inv_mul]; rw [← smul_eq_mul]; rw [FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

variable (b c) in
@[simp]
/--
theorem `radius_regularizedGaussHGFunSeries_eq_top_of_left` / 定理 `radius_regularizedGaussHGFunSeries_eq_top_of_left`

English:
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left
  given: (k : Nat)
  proof: radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

中文:
定理 radius_regularizedGaussHGFunSeries_eq_top_of_left
  条件: (k : 自然数)
  证明: radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

Depends on / 依赖: radius_regularizedHGFunSeries_eq_top_of_finite
-/
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left (k : Nat) :
    (regularizedGaussHGFunSeries (-k) b c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

variable (a c) in
@[simp]
/--
theorem `radius_regularizedGaussHGFunSeries_eq_top_of_right` / 定理 `radius_regularizedGaussHGFunSeries_eq_top_of_right`

English:
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right
  given: (k : Nat)
  proof: radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

中文:
定理 radius_regularizedGaussHGFunSeries_eq_top_of_right
  条件: (k : 自然数)
  证明: radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

Depends on / 依赖: radius_regularizedHGFunSeries_eq_top_of_finite
-/
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right (k : Nat) :
    (regularizedGaussHGFunSeries a (-k) c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : Complex)) (by simp) rfl

variable (c) in
@[grind =]
/--
theorem `radius_regularizedGaussHGFunSeries_eq_one` / 定理 `radius_regularizedGaussHGFunSeries_eq_one`

English:
theorem radius_regularizedGaussHGFunSeries_eq_one
  given: (h : forall k : Nat, a != -k ∧ b != -k)
  proof: radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

中文:
定理 radius_regularizedGaussHGFunSeries_eq_one
  条件: (h : 对任意 k : 自然数, a != -k ∧ b != -k)
  证明: radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

Depends on / 依赖: radius_regularizedHGFunSeries_eq_one
-/
theorem radius_regularizedGaussHGFunSeries_eq_one (h : forall k : Nat, a != -k ∧ b != -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

variable (a b c) in
/--
theorem `radius_regularizedGaussHGFunSeries_ge_one` / 定理 `radius_regularizedGaussHGFunSeries_ge_one`

English:
theorem radius_regularizedGaussHGFunSeries_ge_one
  proof: radius_regularizedHGFunSeries_ge_one rfl

中文:
定理 radius_regularizedGaussHGFunSeries_ge_one
  证明: radius_regularizedHGFunSeries_ge_one rfl

Depends on / 依赖: Quotient, Unique, radius_regularizedHGFunSeries_ge_one
-/
theorem radius_regularizedGaussHGFunSeries_ge_one :
    1 <= (regularizedGaussHGFunSeries a b c).radius :=
  radius_regularizedHGFunSeries_ge_one rfl

end Gaussian

end Complex
