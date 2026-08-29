/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of functions on `ZMod N`

We show that if `N` is a positive integer and `Φ : ZMod N → ℂ`, then the L-series of `Φ` has
analytic continuation (away from a pole at `s = 1` if `∑ j, Φ j ≠ 0`) and satisfies a functional
equation. We also define completed L-functions (given by multiplying the naive L-function by a
Gamma-factor), and prove analytic continuation and functional equations for these too, assuming `Φ`
is either even or odd.

The most familiar case is when `Φ` is a Dirichlet character, but the results here are valid
for general functions; for the specific case of Dirichlet characters see
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`.

## Main definitions

* `ZMod.LFunction Φ s`: the meromorphic continuation of the function `∑ n : ℕ, Φ n * n ^ (-s)`.
* `ZMod.completedLFunction Φ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction Φ s` multiplied by an Archimedean Gamma-factor.

Note that `ZMod.completedLFunction Φ s` is only mathematically well-defined if `Φ` is either even
or odd. Here we extend it to all functions `Φ` by linearity (but the functional equation only holds
if `Φ` is either even or odd).

## Main theorems

Results for non-completed L-functions:

* `ZMod.LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive
  `LSeries`.
* `ZMod.differentiableAt_LFunction`: `ZMod.LFunction Φ` is differentiable at `s ∈ ℂ` if either
  `s ≠ 1` or `∑ j, Φ j = 0`.
* `ZMod.LFunction_one_sub`: the functional equation relating `LFunction Φ (1 - s)` to
  `LFunction (𝓕 Φ) s`, where `𝓕` is the Fourier transform.

Results for completed L-functions:

* `ZMod.LFunction_eq_completed_div_gammaFactor_even` and
  `LFunction_eq_completed_div_gammaFactor_odd`: we have
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ s` for `Φ` even, and
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1)` for `Φ` odd. (We formulate it this way
  so that it is still valid at the poles of the Gamma factor.)
* `ZMod.differentiableAt_completedLFunction`: `ZMod.completedLFunction Φ` is differentiable at
  `s ∈ ℂ`, unless `s = 1` and `∑ j, Φ j ≠ 0`, or `s = 0` and `Φ 0 ≠ 0`.
* `ZMod.completedLFunction_one_sub_even` and `ZMod.completedLFunction_one_sub_odd`:
  the functional equation relating `completedLFunction Φ (1 - s)` to `completedLFunction (𝓕 Φ) s`.
-/

@[expose] public section

open HurwitzZeta Complex ZMod Finset Topology Filter Set

open scoped Real

namespace ZMod

variable {N : Nat} [NeZero N]

/--
lemma `LSeriesSummable_of_one_lt_re` / 引理 `LSeriesSummable_of_one_lt_re`

English:
lemma LSeriesSummable_of_one_lt_re
  given: (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s)
  proof: by
let c := max' _ univ_nonempty.image (norm ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

中文:
引理 LSeriesSummable_of_one_lt_re
  条件: (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s)
  证明: by
let c := max' _ univ_nonempty.image (norm ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

Depends on / 依赖: LSeriesSummable_of_bounded_of_one_lt_re, le_max, mem_image_of_mem, mem_univ, univ_nonempty, univ_nonempty.image
-/
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
let c := max' _ univ_nonempty.image (norm ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/--
Definition of `LFunction` / `LFunction` 的定义

English:
definition LFunction
  signature: (Φ : ZMod N -> Complex) (s : Complex)
  body: N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

中文:
定义 LFunction
  签名: (Φ : ZMod N -> Complex) (s : Complex)
  定义体: N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

Depends on / 依赖: hurwitzZeta, toAddCircle
-/
noncomputable def LFunction (Φ : ZMod N -> Complex) (s : Complex) : Complex :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

/--
lemma `LFunction_modOne_eq` / 引理 `LFunction_modOne_eq`

English:
lemma LFunction_modOne_eq
  given: (Φ : ZMod 1 -> Complex) (s : Complex)
  proof: by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

中文:
引理 LFunction_modOne_eq
  条件: (Φ : ZMod 1 -> Complex) (s : Complex)
  证明: by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

Depends on / 依赖: LFunction, Nat.cast_one, cast_one, hurwitzZeta_zero, map_zero, one_cpow, one_mul, singleton_eq_univ, sum_singleton
-/
lemma LFunction_modOne_eq (Φ : ZMod 1 -> Complex) (s : Complex) :
    LFunction Φ s = Φ 0 * riemannZeta s := by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

/--
lemma `LFunction_eq_LSeries` / 引理 `LFunction_eq_LSeries`

English:
lemma LFunction_eq_LSeries
  given: (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s)
  proof: by
  rw [LFunction]; rw [LSeries]; rw [mul_sum]; rw [Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : Real) in Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
(div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAd

中文:
引理 LFunction_eq_LSeries
  条件: (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s)
  证明: by
  rw [LFunction]; rw [LSeries]; rw [mul_sum]; rw [Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : Real) in Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
(div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAd

Depends on / 依赖: LFunction, LSeries, LSeriesSummable_of_one_lt_re, Nat.cast_le.mpr, Nat.cast_pos.mpr, Nat.sumByResidueClasses, NeZero, NeZero.pos, Set.Icc, cast_le, cast_pos, div_le_one, hasSum_hurwitzZeta_of_one_lt_re, j.val, mem_Icc, mem_Icc.mpr, mul_assoc, mul_sum, sumByResidueClasses, toAddCircle_apply
-/
lemma LFunction_eq_LSeries (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s) :
    LFunction Φ s = LSeries (Φ ·) s := by
  rw [LFunction]; rw [LSeries]; rw [mul_sum]; rw [Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : Real) in Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
(div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAddCircle_apply]; rw [← (hasSum_hurwitzZeta_of_one_lt_re this hs).tsum_eq]; rw [← mul_assoc]; rw [← tsum_mul_left]
  congr 1 with m
  -- The following manipulation is slightly delicate because `(x * y) ^ s = x ^ s * y ^ s` is
  -- false for general complex `x`, `y`, but it is true if `x` and `y` are non-negative reals, so
  -- we have to carefully juggle coercions `ℕ → ℝ → ℂ`.
  calc N ^ (-s) * Φ j * (1 / (m + (j.val / N : Real)) ^ s)
  _ = Φ j * (N ^ (-s) * (1 / (m + (j.val / N : Real)) ^ s)) := by
    rw [← mul_assoc]; rw [mul_comm _ (Φ _)]
  _ = Φ j * (1 / (N : Real) ^ s * (1 / ((j.val + N * m) / N : Real) ^ s)) := by
    simp only [cpow_neg, ← one_div, ofReal_div, ofReal_natCast, add_comm, add_div, ofReal_add,
      ofReal_mul, mul_div_cancel_left₀ (m : Complex) (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ j / ((N : Real) * ((j.val + N * m) / N : Real)) ^ s := by -- this is the delicate step!
    rw [one_div_mul_one_div]; rw [mul_one_div]; rw [mul_cpow_ofReal_nonneg] <;> positivity
  _ = Φ j / (N * (j.val + N * m) / N) ^ s := by
    simp only [ofReal_natCast, ofReal_div, ofReal_add, ofReal_mul, mul_div_assoc]
  _ = Φ j / (j.val + N * m) ^ s := by
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ ↑(j.val + N * m) / (↑(j.val + N * m)) ^ s := by
    simp only [Nat.cast_add, Nat.cast_mul, natCast_zmod_val, natCast_self, zero_mul, add_zero]
  _ = LSeries.term (Φ ·) s (j.val + N * m) := by
    rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]

/--
lemma `differentiableAt_LFunction` / 引理 `differentiableAt_LFunction`

English:
lemma differentiableAt_LFunction
  given: (Φ : ZMod N -> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0)
  proof: by
  refine .mul (by fun_prop) ?_
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .fun_sum fun j _ => (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.fun_sum (u := univ) fun j _ =>
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa

中文:
引理 differentiableAt_LFunction
  条件: (Φ : ZMod N -> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0)
  证明: by
  refine .mul (by fun_prop) ?_
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .fun_sum fun j _ => (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.fun_sum (u := univ) fun j _ =>
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fun_sum, const_mul, differentiableAt_hurwitzZeta, differentiableAt_hurwitzZeta_sub_one_div, fun_prop, fun_sum, hs.neg_resolve_left, mul_sub, ne_or_eq, neg_resolve_left, sub_zero, sum_mul, sum_sub_distrib, toAddCircle, zero_mul
-/
lemma differentiableAt_LFunction (Φ : ZMod N -> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt Complex (LFunction Φ) s := by
  refine .mul (by fun_prop) ?_
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .fun_sum fun j _ => (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.fun_sum (u := univ) fun j _ =>
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, hs.neg_resolve_left rfl, zero_mul, sub_zero]

/--
lemma `differentiable_LFunction_of_sum_zero` / 引理 `differentiable_LFunction_of_sum_zero`

English:
lemma differentiable_LFunction_of_sum_zero
  given: {Φ : ZMod N -> Complex} (hΦ : ∑ j, Φ j = 0)
  proof: fun s => differentiableAt_LFunction Φ s (Or.inr hΦ)

中文:
引理 differentiable_LFunction_of_sum_zero
  条件: {Φ : ZMod N -> Complex} (hΦ : ∑ j, Φ j = 0)
  证明: fun s => differentiableAt_LFunction Φ s (Or.inr hΦ)

Depends on / 依赖: Or.inr, differentiableAt_LFunction
-/
lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N -> Complex} (hΦ : ∑ j, Φ j = 0) :
    Differentiable Complex (LFunction Φ) :=
  fun s => differentiableAt_LFunction Φ s (Or.inr hΦ)

/--
lemma `LFunction_residue_one` / 引理 `LFunction_residue_one`

English:
lemma LFunction_residue_one
  given: (Φ : ZMod N -> Complex)
  proof: by
  simp only [LFunction, mul_sum]
  refine tendsto_finsetSum _ fun j _ => ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1))]; rw [one_div]; rw [← cpow_neg_one]
  simp only [show forall a b c d : Complex, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_

中文:
引理 LFunction_residue_one
  条件: (Φ : ZMod N -> Complex)
  证明: by
  simp only [LFunction, mul_sum]
  refine tendsto_finsetSum _ fun j _ => ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1))]; rw [one_div]; rw [← cpow_neg_one]
  simp only [show forall a b c d : Complex, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_

Depends on / 依赖: LFunction, NeZero, NeZero.ne, Or.inl, const_cpow, continuous_neg, continuous_neg.const_cpow, cpow_neg_one, hurwitzZeta_residue_one, intros, mono_left, mul_sum, nhdsWithin_le_nhds, one_div, tendsto, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_finsetSum
-/
lemma LFunction_residue_one (Φ : ZMod N -> Complex) :
    Tendsto (fun s => (s - 1) * LFunction Φ s) (𝓝[!=] 1) (𝓝 (∑ j, Φ j / N)) := by
  simp only [LFunction, mul_sum]
  refine tendsto_finsetSum _ fun j _ => ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1))]; rw [one_div]; rw [← cpow_neg_one]
  simp only [show forall a b c d : Complex, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_ <| hurwitzZeta_residue_one _)
  exact ((continuous_neg.const_cpow (Or.inl <| NeZero.ne _)).tendsto _).mono_left
    nhdsWithin_le_nhds

local notation "𝕖" => stdAddChar

/--
lemma `LFunction_stdAddChar_eq_expZeta_of_one_lt_re` / 引理 `LFunction_stdAddChar_eq_expZeta_of_one_lt_re`

English:
lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re
  given: (j : ZMod N) {s : Complex} (hs : 1 < s.re)
  proof: by
  rw [toAddCircle_apply]; rw [← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq]; rw [LFunction_eq_LSeries _ hs]; rw [LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]; rw [ofReal_div]; rw [ofReal_natCast]; rw [ofReal_natCast]; rw [mul_assoc]; rw [div_mul_eq

中文:
引理 LFunction_stdAddChar_eq_expZeta_of_one_lt_re
  条件: (j : ZMod N) {s : Complex} (hs : 1 < s.re)
  证明: by
  rw [toAddCircle_apply]; rw [← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq]; rw [LFunction_eq_LSeries _ hs]; rw [LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]; rw [ofReal_div]; rw [ofReal_natCast]; rw [ofReal_natCast]; rw [mul_assoc]; rw [div_mul_eq
-/
private lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re (j : ZMod N) {s : Complex} (hs : 1 < s.re) :
    LFunction (fun k => 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  rw [toAddCircle_apply]; rw [← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq]; rw [LFunction_eq_LSeries _ hs]; rw [LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]; rw [ofReal_div]; rw [ofReal_natCast]; rw [ofReal_natCast]; rw [mul_assoc]; rw [div_mul_eq_mul_div]; rw [stdAddChar_apply]
  have := ZMod.toCircle_intCast (N := N) (j.val * n)
  conv_rhs at this => rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc]
  rw [← this]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [Int.cast_natCast]; rw [natCast_zmod_val]

/--
lemma `LFunction_stdAddChar_eq_expZeta` / 引理 `LFunction_stdAddChar_eq_expZeta`

English:
lemma LFunction_stdAddChar_eq_expZeta
  given: (j : ZMod N) (s : Complex) (hjs : j != 0 ∨ s != 1)
  proof: by
  let U := if j = 0 then {z : Complex | z != 1} else univ -- region of analyticity of both functions
  let V := {z : Complex | 1 < re z} -- convergence region
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using! isOpen_compl_singleton
    · simp only [h, ↓

中文:
引理 LFunction_stdAddChar_eq_expZeta
  条件: (j : ZMod N) (s : Complex) (hjs : j != 0 ∨ s != 1)
  证明: by
  let U := if j = 0 then {z : Complex | z != 1} else univ -- region of analyticity of both functions
  let V := {z : Complex | 1 < re z} -- convergence region
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using! isOpen_compl_singleton
    · simp only [h, ↓

Depends on / 依赖: IsOpen, LFunction, analyticity, convergence, expZeta, functions, isOpen_compl_singleton, isOpen_univ, mem_ite_univ_right, reduceIte, region, stdAddChar, toAddCircle
-/
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : Complex) (hjs : j != 0 ∨ s != 1) :
    LFunction (fun k => 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  let U := if j = 0 then {z : Complex | z != 1} else univ -- region of analyticity of both functions
  let V := {z : Complex | 1 < re z} -- convergence region
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using! isOpen_compl_singleton
    · simp only [h, ↓reduceIte, isOpen_univ, U]
  let f := LFunction (fun k => stdAddChar (j * k))
  let g := expZeta (toAddCircle j)
  have hU {u} : u in U ↔ u != 1 ∨ j != 0 := by simp only [mem_ite_univ_right, U]; tauto
  -- hypotheses for uniqueness of analytic continuation
  have hf : AnalyticOnNhd Complex f U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    refine (differentiableAt_LFunction _ _ ((hU.mp hu).imp_right fun h => ?_)).differentiableWithinAt
    simp only [mul_comm j, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _), h,
      ↓reduceIte, CharP.cast_eq_zero]
  have hg : AnalyticOnNhd Complex g U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    refine (differentiableAt_expZeta _ _ ((hU.mp hu).imp_right fun h => ?_)).differentiableWithinAt
    rwa [ne_eq, toAddCircle_eq_zero]
  have hUc : IsPreconnected U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using!
        (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    · simpa only [h, ↓reduceIte, U] using isPreconnected_univ
  have hV : V in 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hUmem : 2 in U := by simp [U]
  have hUmem' : s in U := hU.mpr hjs.symm
  -- apply uniqueness result
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hUmem ?_ hUmem'
  -- now remains to prove equality on `1 < re s`
  filter_upwards [hV] with z using LFunction_stdAddChar_eq_expZeta_of_one_lt_re _

/--
lemma `LFunction_dft` / 引理 `LFunction_dft`

English:
lemma LFunction_dft
  given: (Φ : ZMod N -> Complex) {s : Complex} (hs : Φ 0 = 0 ∨ s != 1)
  proof: by
  have (j : ZMod N) : Φ j * LFunction (fun k => 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j != 0 ∨ s != 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1]; rw [show Φ 0 = 0 by tauto]; rw [zer

中文:
引理 LFunction_dft
  条件: (Φ : ZMod N -> Complex) {s : Complex} (hs : Φ 0 = 0 ∨ s != 1)
  证明: by
  have (j : ZMod N) : Φ j * LFunction (fun k => 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j != 0 ∨ s != 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1]; rw [show Φ 0 = 0 by tauto]; rw [zer

Depends on / 依赖: LFunction, LFunction_stdAddChar_eq_expZeta, dft_def, expZeta, mul_assoc, mul_comm, mul_sum, neg_ne_zero, not_not, not_or, smul_eq_mul, stdAddChar_apply, sum_comm, sum_mul, toAddCircle, zero_mul
-/
lemma LFunction_dft (Φ : ZMod N -> Complex) {s : Complex} (hs : Φ 0 = 0 ∨ s != 1) :
    LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s := by
  have (j : ZMod N) : Φ j * LFunction (fun k => 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j != 0 ∨ s != 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1]; rw [show Φ 0 = 0 by tauto]; rw [zero_mul]; rw [zero_mul]
  simp only [LFunction, ← this, mul_sum]
  rw [dft_def]; rw [sum_comm]
  simp only [sum_mul, mul_sum, smul_eq_mul, stdAddChar_apply, ← mul_assoc]
  congr 1 with j
  congr 1 with k
  rw [mul_assoc (Φ _)]; rw [mul_comm (Φ _)]; rw [neg_mul]

/--
theorem `LFunction_one_sub` / 定理 `LFunction_one_sub`

English:
theorem LFunction_one_sub
  statement: (Φ : ZMod N -> Complex) {s : Complex}
  proof: by
  rw [LFunction]
  have (j : ZMod N) : Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' wi

中文:
定理 LFunction_one_sub
  结论: (Φ : ZMod N -> Complex) {s : Complex}
  证明: by
  rw [LFunction]
  have (j : ZMod N) : Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' wi

Depends on / 依赖: LFunction, Or.inl, Or.inr, eq_or_ne, expZeta, hurwitzZeta, hurwitzZeta_one_sub, mul_assoc, toAddCircle, toAddCircle_eq_zero, toAddCircle_eq_zero.not.mpr, zero_mul
-/
theorem LFunction_one_sub (Φ : ZMod N -> Complex) {s : Complex}
    (hs : forall (n : Nat), s != -n) (hs' : Φ 0 = 0 ∨ s != 1) :
    LFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
      (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s
       + cexp (-π * I * s / 2) * LFunction (𝓕 fun x => Φ (-x)) s) := by
  rw [LFunction]
  have (j : ZMod N) : Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' with hΦ | hs'
      · simp only [hΦ, zero_mul]
      · rw [hurwitzZeta_one_sub _ hs (Or.inr hs')]
    · rw [hurwitzZeta_one_sub _ hs (Or.inl <| toAddCircle_eq_zero.not.mpr hj)]
  simp only [this, mul_assoc _ _ (Gamma s)]
  -- get rid of Gamma terms and power of N
  generalize (2 * π) ^ (-s) * Gamma s = C
  simp_rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc,
    neg_sub]
  congr 2
  -- now gather sum terms
  rw [LFunction_dft _ hs']; rw [LFunction_dft _ (hs'.imp_left <| by simp only [neg_zero]; rw [imp_self])]
  conv_rhs => enter [2, 2]; rw [← (Equiv.neg _).sum_comp _ _ (by simp), Equiv.neg_apply]
  simp_rw [neg_neg, mul_sum, ← sum_add_distrib, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← mul_add, map_neg, add_comm]

section signed

variable {Φ : ZMod N -> Complex}

/--
lemma `LFunction_def_even` / 引理 `LFunction_def_even`

English:
lemma LFunction_def_even
  given: (hΦ : Φ.Even) (s : Complex)
  proof: by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_left, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]

中文:
引理 LFunction_def_even
  条件: (hΦ : Φ.Even) (s : Complex)
  证明: by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_left, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]

Depends on / 依赖: Equiv.neg_apply, Fintype, Fintype.sum_equiv, LFunction, add_eq_left, hurwitzZeta, hurwitzZetaOdd_neg, map_neg, mul_add, mul_neg, neg_apply, neg_eq_self, sum_add_distrib, sum_equiv, sum_neg_distrib
-/
lemma LFunction_def_even (hΦ : Φ.Even) (s : Complex) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_left, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]

/--
lemma `LFunction_def_odd` / 引理 `LFunction_def_odd`

English:
lemma LFunction_def_odd
  given: (hΦ : Φ.Odd) (s : Complex)
  proof: by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_right, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]

中文:
引理 LFunction_def_odd
  条件: (hΦ : Φ.Odd) (s : Complex)
  证明: by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_right, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]

Depends on / 依赖: Equiv.neg_apply, Fintype, Fintype.sum_equiv, LFunction, add_eq_right, hurwitzZeta, hurwitzZetaEven_neg, map_neg, mul_add, neg_apply, neg_eq_self, neg_mul, sum_add_distrib, sum_equiv, sum_neg_distrib
-/
lemma LFunction_def_odd (hΦ : Φ.Odd) (s : Complex) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_right, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i => ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]

/--
lemma `LFunction_apply_zero_of_even` / 引理 `LFunction_apply_zero_of_even`

English:
lemma LFunction_apply_zero_of_even
  given: (hΦ : Φ.Even)
  proof: by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]

中文:
引理 LFunction_apply_zero_of_even
  条件: (hΦ : Φ.Even)
  证明: by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]
-/
@[simp] lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 = -Φ 0 / 2 := by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]

/--
lemma `LFunction_neg_two_mul_nat_add_one` / 引理 `LFunction_neg_two_mul_nat_add_one`

English:
lemma LFunction_neg_two_mul_nat_add_one
  given: (hΦ : Φ.Even) (n : Nat)
  proof: by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]

中文:
引理 LFunction_neg_two_mul_nat_add_one
  条件: (hΦ : Φ.Even) (n : 自然数)
  证明: by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]
-/
@[simp] lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : Nat) :
    LFunction Φ (-(2 * (n + 1))) = 0 := by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]

/--
lemma `LFunction_neg_two_mul_nat_sub_one` / 引理 `LFunction_neg_two_mul_nat_sub_one`

English:
lemma LFunction_neg_two_mul_nat_sub_one
  given: (hΦ : Φ.Odd) (n : Nat)
  proof: by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, ← neg_mul,
    sum_const_zero]

中文:
引理 LFunction_neg_two_mul_nat_sub_one
  条件: (hΦ : Φ.Odd) (n : 自然数)
  证明: by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, ← neg_mul,
    sum_const_zero]
-/
@[simp] lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : Nat) :
    LFunction Φ (-(2 * n) - 1) = 0 := by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, ← neg_mul,
    sum_const_zero]

/--
Definition of `completedLFunction` / `completedLFunction` 的定义

English:
definition completedLFunction
  signature: (Φ : ZMod N -> Complex) (s : Complex)
  body: N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  + N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

中文:
定义 completedLFunction
  签名: (Φ : ZMod N -> Complex) (s : Complex)
  定义体: N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  + N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

Depends on / 依赖: completedHurwitzZetaEven, completedHurwitzZetaOdd, toAddCircle
-/
noncomputable def completedLFunction (Φ : ZMod N -> Complex) (s : Complex) : Complex :=
  N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  + N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/--
lemma `completedLFunction_zero` / 引理 `completedLFunction_zero`

English:
lemma completedLFunction_zero
  given: (s : Complex)
  statement: completedLFunction (0 : ZMod N -> Complex) s = 0
  proof: by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, zero_add]

中文:
引理 completedLFunction_zero
  条件: (s : Complex)
  结论: completedLFunction (0 : ZMod N -> Complex) s = 0
  证明: by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, zero_add]
-/
@[simp] lemma completedLFunction_zero (s : Complex) : completedLFunction (0 : ZMod N -> Complex) s = 0 := by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, zero_add]

/--
lemma `completedLFunction_const_mul` / 引理 `completedLFunction_const_mul`

English:
lemma completedLFunction_const_mul
  given: (a : Complex) (Φ : ZMod N -> Complex) (s : Complex)
  proof: by
  simp only [completedLFunction, mul_add, mul_sum]
  congr with i <;> ring

中文:
引理 completedLFunction_const_mul
  条件: (a : Complex) (Φ : ZMod N -> Complex) (s : Complex)
  证明: by
  simp only [completedLFunction, mul_add, mul_sum]
  congr with i <;> ring

Depends on / 依赖: completedLFunction, mul_add, mul_sum
-/
lemma completedLFunction_const_mul (a : Complex) (Φ : ZMod N -> Complex) (s : Complex) :
    completedLFunction (fun j => a * Φ j) s = a * completedLFunction Φ s := by
  simp only [completedLFunction, mul_add, mul_sum]
  congr with i <;> ring

/--
lemma `completedLFunction_def_even` / 引理 `completedLFunction_def_even`

English:
lemma completedLFunction_def_even
  given: (hΦ : Φ.Even) (s : Complex)
  proof: by
  suffices ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [add_zero]
  refine (hΦ.mul_odd fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaOdd_neg]

中文:
引理 completedLFunction_def_even
  条件: (hΦ : Φ.Even) (s : Complex)
  证明: by
  suffices ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [add_zero]
  refine (hΦ.mul_odd fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaOdd_neg]

Depends on / 依赖: add_zero, completedHurwitzZetaOdd, completedHurwitzZetaOdd_neg, completedLFunction, map_neg, mul_odd, mul_zero, sum_eq_zero, toAddCircle
-/
lemma completedLFunction_def_even (hΦ : Φ.Even) (s : Complex) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [add_zero]
  refine (hΦ.mul_odd fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaOdd_neg]

/--
lemma `completedLFunction_def_odd` / 引理 `completedLFunction_def_odd`

English:
lemma completedLFunction_def_odd
  given: (hΦ : Φ.Odd) (s : Complex)
  proof: by
  suffices ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [zero_add]
  refine (hΦ.mul_even fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaEven_neg]

中文:
引理 completedLFunction_def_odd
  条件: (hΦ : Φ.Odd) (s : Complex)
  证明: by
  suffices ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [zero_add]
  refine (hΦ.mul_even fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaEven_neg]

Depends on / 依赖: completedHurwitzZetaEven, completedHurwitzZetaEven_neg, completedLFunction, map_neg, mul_even, mul_zero, sum_eq_zero, toAddCircle, zero_add
-/
lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : Complex) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s = 0 by
    rw [completedLFunction]; rw [this]; rw [mul_zero]; rw [zero_add]
  refine (hΦ.mul_even fun j => ?_).sum_eq_zero
  rw [map_neg]; rw [completedHurwitzZetaEven_neg]

/--
lemma `completedLFunction_modOne_eq` / 引理 `completedLFunction_modOne_eq`

English:
lemma completedLFunction_modOne_eq
  given: (Φ : ZMod 1 -> Complex) (s : Complex)
  proof: by
  rw [completedLFunction_def_even (show Φ.Even from fun _ => congr_arg Φ (Subsingleton.elim ..))]; rw [Nat.cast_one]; rw [one_cpow]; rw [one_mul]; rw [← singleton_eq_univ 0]; rw [sum_singleton]; rw [map_zero]; rw [completedHurwitzZetaEven_zero]; rw [Subsingleton.elim 0 1]

中文:
引理 completedLFunction_modOne_eq
  条件: (Φ : ZMod 1 -> Complex) (s : Complex)
  证明: by
  rw [completedLFunction_def_even (show Φ.Even from fun _ => congr_arg Φ (Subsingleton.elim ..))]; rw [Nat.cast_one]; rw [one_cpow]; rw [one_mul]; rw [← singleton_eq_univ 0]; rw [sum_singleton]; rw [map_zero]; rw [completedHurwitzZetaEven_zero]; rw [Subsingleton.elim 0 1]

Depends on / 依赖: Nat.cast_one, Subsingleton, Subsingleton.elim, cast_one, completedHurwitzZetaEven_zero, completedLFunction_def_even, congr_arg, map_zero, one_cpow, one_mul, singleton_eq_univ, sum_singleton
-/
lemma completedLFunction_modOne_eq (Φ : ZMod 1 -> Complex) (s : Complex) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  rw [completedLFunction_def_even (show Φ.Even from fun _ => congr_arg Φ (Subsingleton.elim ..))]; rw [Nat.cast_one]; rw [one_cpow]; rw [one_mul]; rw [← singleton_eq_univ 0]; rw [sum_singleton]; rw [map_zero]; rw [completedHurwitzZetaEven_zero]; rw [Subsingleton.elim 0 1]

/--
Definition of `completedLFunction₀` / `completedLFunction₀` 的定义

English:
definition completedLFunction₀
  signature: (Φ : ZMod N -> Complex) (s : Complex)
  body: N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

中文:
定义 completedLFunction₀
  签名: (Φ : ZMod N -> Complex) (s : Complex)
  定义体: N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

Depends on / 依赖: completedHurwitzZetaOdd, toAddCircle
-/
noncomputable def completedLFunction₀ (Φ : ZMod N -> Complex) (s : Complex) : Complex :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/--
lemma `differentiable_completedLFunction₀` / 引理 `differentiable_completedLFunction₀`

English:
lemma differentiable_completedLFunction₀
  given: (Φ : ZMod N -> Complex)
  proof: by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.fun_sum fun i _ => .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

中文:
引理 differentiable_completedLFunction₀
  条件: (Φ : ZMod N -> Complex)
  证明: by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.fun_sum fun i _ => .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

Depends on / 依赖: const_mul, differentiable_completedHurwitzZetaOdd, exacts, fun_prop, fun_sum
-/
lemma differentiable_completedLFunction₀ (Φ : ZMod N -> Complex) :
    Differentiable Complex (completedLFunction₀ Φ) := by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.fun_sum fun i _ => .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

/--
lemma `completedLFunction_eq` / 引理 `completedLFunction_eq`

English:
lemma completedLFunction_eq
  given: (Φ : ZMod N -> Complex) (s : Complex)
  proof: by
  simp only [completedLFunction, completedHurwitzZetaEven_eq, toAddCircle_eq_zero, div_eq_mul_inv,
    ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, Fintype.sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  abel

中文:
引理 completedLFunction_eq
  条件: (Φ : ZMod N -> Complex) (s : Complex)
  证明: by
  simp only [completedLFunction, completedHurwitzZetaEven_eq, toAddCircle_eq_zero, div_eq_mul_inv,
    ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, Fintype.sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  abel

Depends on / 依赖: Fintype, Fintype.sum_ite_eq, completedHurwitzZetaEven_eq, completedLFunction, div_eq_mul_inv, ite_mul, mul_assoc, mul_ite, mul_sub, mul_zero, one_mul, sum_ite_eq, sum_mul, sum_sub_distrib, toAddCircle_eq_zero, zero_mul
-/
lemma completedLFunction_eq (Φ : ZMod N -> Complex) (s : Complex) :
    completedLFunction Φ s =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  simp only [completedLFunction, completedHurwitzZetaEven_eq, toAddCircle_eq_zero, div_eq_mul_inv,
    ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, Fintype.sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  abel

/--
lemma `differentiableAt_completedLFunction` / 引理 `differentiableAt_completedLFunction`

English:
lemma differentiableAt_completedLFunction
  statement: (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0)
  proof: by
  simp only [funext (completedLFunction_eq Φ), mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).s

中文:
引理 differentiableAt_completedLFunction
  结论: (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0)
  证明: by
  simp only [funext (completedLFunction_eq Φ), mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).s

Depends on / 依赖: completedLFunction_eq, mul_div_assoc
-/
lemma differentiableAt_completedLFunction (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0)
    (hs₁ : s != 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Complex (completedLFunction Φ) s := by
  simp only [funext (completedLFunction_eq Φ), mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).sub ?_
  · -- term with `1 / s`
    refine .mul (by fun_prop) (hs₀.elim ?_ ?_)
    · exact fun h => (differentiableAt_const _).div differentiableAt_id h
    · exact fun h => by simp only [h, funext zero_div, differentiableAt_const]
  · -- term with `1 / (1 - s)`
    refine .mul (by fun_prop) (hs₁.elim ?_ ?_)
    · exact fun h => .div (by fun_prop) (by fun_prop) (by rwa [sub_ne_zero, ne_comm])
    · exact fun h => by simp only [h, zero_div, differentiableAt_const]

/--
lemma `differentiable_completedLFunction` / 引理 `differentiable_completedLFunction`

English:
lemma differentiable_completedLFunction
  given: (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0)
  proof: fun s => differentiableAt_completedLFunction Φ s (.inr hΦ₂) (.inr hΦ₃)

中文:
引理 differentiable_completedLFunction
  条件: (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0)
  证明: fun s => differentiableAt_completedLFunction Φ s (.inr hΦ₂) (.inr hΦ₃)

Depends on / 依赖: differentiableAt_completedLFunction
-/
lemma differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable Complex (completedLFunction Φ) :=
  fun s => differentiableAt_completedLFunction Φ s (.inr hΦ₂) (.inr hΦ₃)

/--
lemma `LFunction_eq_completed_div_gammaFactor_even` / 引理 `LFunction_eq_completed_div_gammaFactor_even`

English:
lemma LFunction_eq_completed_div_gammaFactor_even
  given: (hΦ : Φ.Even) (s : Complex) (hs : s != 0 ∨ Φ 0 = 0)
  proof: by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.in

中文:
引理 LFunction_eq_completed_div_gammaFactor_even
  条件: (hΦ : Φ.Even) (s : Complex) (hs : s != 0 ∨ Φ 0 = 0)
  证明: by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.in

Depends on / 依赖: LFunction_def_even, completedLFunction_def_even, hurwitzZetaEven_def_of_ne_or_ne, map_zero, mul_div_assoc, ne_or_eq, sum_div, toAddCircle_eq_zero, toAddCircle_eq_zero.mp, zero_mul
-/
lemma LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : Complex) (hs : s != 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / GammaReal s := by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.inr hs)]
    · simp only [hΦ', map_zero, zero_mul]

/--
lemma `LFunction_eq_completed_div_gammaFactor_odd` / 引理 `LFunction_eq_completed_div_gammaFactor_odd`

English:
lemma LFunction_eq_completed_div_gammaFactor_odd
  given: (hΦ : Φ.Odd) (s : Complex)
  proof: by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]

中文:
引理 LFunction_eq_completed_div_gammaFactor_odd
  条件: (hΦ : Φ.Odd) (s : Complex)
  证明: by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]

Depends on / 依赖: LFunction_def_odd, completedLFunction_def_odd, hurwitzZetaOdd, mul_div_assoc, sum_div
-/
lemma LFunction_eq_completed_div_gammaFactor_odd (hΦ : Φ.Odd) (s : Complex) :
    LFunction Φ s = completedLFunction Φ s / GammaReal (s + 1) := by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]

/--
lemma `completedLFunction_one_sub_of_one_lt_even` / 引理 `completedLFunction_one_sub_of_one_lt_even`

English:
lemma completedLFunction_one_sub_of_one_lt_even
  given: (hΦ : Φ.Even) {s : Complex} (hs : 1 < re s)
  proof: by
  have hs₀ : s != 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s != 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_even hΦ, neg_sub, completedHur

中文:
引理 completedLFunction_one_sub_of_one_lt_even
  条件: (hΦ : Φ.Even) {s : Complex} (hs : 1 < re s)
  证明: by
  have hs₀ : s != 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s != 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_even hΦ, neg_sub, completedHur
-/
private lemma completedLFunction_one_sub_of_one_lt_even (hΦ : Φ.Even) {s : Complex} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  have hs₀ : s != 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s != 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_even hΦ, neg_sub, completedHurwitzZetaEven_one_sub, this]
  -- reduce to equality with un-completed L-functions:
  suffices ∑ x, Φ x * cosZeta (toAddCircle x) s = LFunction (𝓕 Φ) s by
    simpa only [cosZeta, Function.update_of_ne hs₀, ← mul_div_assoc, ← sum_div,
      LFunction_eq_completed_div_gammaFactor_even (dft_even_iff.mpr hΦ) _ (.inl hs₀),
      div_left_inj' (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]
  -- expand out `LFunction (𝓕 Φ)` and use parity:
  simp only [cosZeta_eq, ← mul_div_assoc _ _ (2 : Complex), mul_add, ← sum_div, sum_add_distrib,
    LFunction_dft Φ (.inr hs₁), map_neg, div_eq_iff (two_ne_zero' Complex), mul_two, add_left_inj]
  exact Fintype.sum_equiv (.neg _) _ _ (by simp [hΦ _])

/--
lemma `completedLFunction_one_sub_of_one_lt_odd` / 引理 `completedLFunction_one_sub_of_one_lt_odd`

English:
lemma completedLFunction_one_sub_of_one_lt_odd
  given: (hΦ : Φ.Odd) {s : Complex} (hs : 1 < re s)
  proof: by
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this,
      mul_assoc]
  -- reduce to equality with un-completed L-functions:
 

中文:
引理 completedLFunction_one_sub_of_one_lt_odd
  条件: (hΦ : Φ.Odd) {s : Complex} (hs : 1 < re s)
  证明: by
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this,
      mul_assoc]
  -- reduce to equality with un-completed L-functions:
 
-/
private lemma completedLFunction_one_sub_of_one_lt_odd (hΦ : Φ.Odd) {s : Complex} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this,
      mul_assoc]
  -- reduce to equality with un-completed L-functions:
  suffices ∑ x, Φ x * sinZeta (toAddCircle x) s = I * LFunction (𝓕 Φ) s by
    have hs' : 0 < re (s + 1) := by simp only [add_re, one_re]; linarith
    simpa only [sinZeta, ← mul_div_assoc, ← sum_div, div_left_inj' (GammaReal_ne_zero_of_re_pos hs'),
      LFunction_eq_completed_div_gammaFactor_odd (dft_odd_iff.mpr hΦ)]
  -- now calculate:
  calc ∑ x, Φ x * sinZeta (toAddCircle x) s
  _ = (∑ x, Φ x * expZeta (toAddCircle x) s) / (2 * I)
      - (∑ x, Φ x * expZeta (toAddCircle (-x)) s) / (2 * I) := by
    simp only [sinZeta_eq, ← mul_div_assoc, mul_sub, sub_div, sum_sub_distrib, sum_div, map_neg]
  _ = (∑ x, Φ (-x) * expZeta (toAddCircle (-x)) s) / (_) - (_) := by
    congrm ?_ / _ - _
    exact (Fintype.sum_equiv (.neg _) _ _ fun x => by rfl).symm
  _ = -I⁻¹ * LFunction (𝓕 Φ) s := by
    simp only [hΦ _, neg_mul, sum_neg_distrib, LFunction_dft Φ (.inl hΦ.map_zero)]
    ring
  _ = I * LFunction (𝓕 Φ) s := by rw [inv_I, neg_neg]

/--
theorem `completedLFunction_one_sub_even` / 定理 `completedLFunction_one_sub_even`

English:
theorem completedLFunction_one_sub_even
  statement: (hΦ : Φ.Even) (s : Complex)
  proof: by
  -- We prove this using `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  -- Set on whic

中文:
定理 completedLFunction_one_sub_even
  结论: (hΦ : Φ.Even) (s : Complex)
  证明: by
  -- We prove this using `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  -- Set on whic
-/
theorem completedLFunction_one_sub_even (hΦ : Φ.Even) (s : Complex)
    (hs₀ : s != 0 ∨ ∑ j, Φ j = 0) (hs₁ : s != 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  -- We prove this using `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  -- Set on which F, G are analytic:
  let U := {t : Complex | (t != 0 ∨ ∑ j, Φ j = 0) ∧ (t != 1 ∨ Φ 0 = 0)}
  -- Properties of U:
  have hsU : s in U := ⟨hs₀, hs₁⟩
  have h2U : 2 in U := ⟨.inl two_ne_zero, .inl (OfNat.ofNat_ne_one _)⟩
  have hUo : IsOpen U := (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)
  have hUp : IsPreconnected U := by
    -- need to write `U` as the complement of an obviously countable set
    let Uc : Set Complex := (if ∑ j, Φ j = 0 then ∅ else {0}) union (if Φ 0 = 0 then ∅ else {1})
    have : Uc.Countable := by
      apply Countable.union <;>
      split_ifs <;>
      simp only [countable_singleton, countable_empty]
    convert! (this.isConnected_compl_of_one_lt_rank ?_).isPreconnected using 1
    · ext x
      by_cases h : Φ 0 = 0 <;>
      by_cases h' : ∑ j, Φ j = 0 <;>
      simp [U, Uc, h, h', and_comm]
    · simp only [rank_real_complex, Nat.one_lt_ofNat]
  -- Analyticity on U:
  have hF : AnalyticOnNhd Complex F U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht => DifferentiableAt.differentiableWithinAt ?_) hUo
    refine (differentiableAt_completedLFunction Φ _ ?_ ?_).comp t (differentiableAt_id.const_sub 1)
    exacts [ht.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm), ht.1.imp_left sub_eq_self.not.mpr]
  have hG : AnalyticOnNhd Complex G U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht => DifferentiableAt.differentiableWithinAt ?_) hUo
    apply ((differentiableAt_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul
    apply differentiableAt_completedLFunction _ _ (ht.1.imp_right fun h => dft_apply_zero Φ ▸ h)
    exact ht.2.imp_right (fun h => by simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero])
  -- set where we know equality
  have hV : {z | 1 < re z} in 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
have hFG : F =ᶠ[𝓝 2] G := eventually_of_mem hV fun t ht => by
    simpa only [F, G, pow_zero, mul_one] using completedLFunction_one_sub_of_one_lt_even hΦ ht
  -- now apply the big hammer to finish
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUp h2U hFG hsU

/--
theorem `completedLFunction_one_sub_odd` / 定理 `completedLFunction_one_sub_odd`

English:
theorem completedLFunction_one_sub_odd
  given: (hΦ : Φ.Odd) (s : Complex)
  proof: by
  -- This is much easier than the even case since both functions are entire.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
  -- check F, G globally differentiable
  have hF : Differentiable Complex F := (

中文:
定理 completedLFunction_one_sub_odd
  条件: (hΦ : Φ.Odd) (s : Complex)
  证明: by
  -- This is much easier than the even case since both functions are entire.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
  -- check F, G globally differentiable
  have hF : Differentiable Complex F := (
-/
theorem completedLFunction_one_sub_odd (hΦ : Φ.Odd) (s : Complex) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  -- This is much easier than the even case since both functions are entire.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
  -- check F, G globally differentiable
  have hF : Differentiable Complex F := (differentiable_completedLFunction hΦ.map_zero
    hΦ.sum_eq_zero).comp (differentiable_id.const_sub 1)
  have hG : Differentiable Complex G := by
    apply (((differentiable_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul_const _).mul
    rw [← dft_odd_iff] at hΦ
    exact differentiable_completedLFunction hΦ.map_zero hΦ.sum_eq_zero
  -- set where we know equality
  have : {z | 1 < re z} in 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := by filter_upwards [this] with t ht
    using completedLFunction_one_sub_of_one_lt_odd hΦ ht
  -- now apply the big hammer to finish
  rw [← analyticOnNhd_univ_iff_differentiable] at hF hG
  exact congr_fun (hF.eq_of_eventuallyEq hG hFG) s

end signed

end ZMod
