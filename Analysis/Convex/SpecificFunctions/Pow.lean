/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Convexity properties of `rpow`

We prove basic convexity properties of the `rpow` function. The proofs are elementary and do not
require calculus, and as such this file has only moderate dependencies.

## Main declarations

* `NNReal.strictConcaveOn_rpow`, `Real.strictConcaveOn_rpow`: strict concavity of
  `fun x ↦ x ^ p` for p ∈ (0,1)
* `NNReal.concaveOn_rpow`, `Real.concaveOn_rpow`: concavity of `fun x ↦ x ^ p` for p ∈ [0,1]

Note that convexity for `p > 1` can be found in `Analysis.Convex.SpecificFunctions.Basic`, which
requires slightly less imports.

## TODO

* Prove convexity for negative powers.
-/

public section

open Set

namespace NNReal

/--
lemma `strictConcaveOn_rpow` / 引理 `strictConcaveOn_rpow`

English:
lemma strictConcaveOn_rpow
  given: {p : Real} (hp₀ : 0 < p) (hp₁ : p < 1)
  proof: by
  have hp₀' : 0 < 1 / p := div_pos zero_lt_one hp₀
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn Real>=0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow 

中文:
引理 strictConcaveOn_rpow
  条件: {p : 实数} (hp₀ : 0 < p) (hp₁ : p < 1)
  证明: by
  have hp₀' : 0 < 1 / p := div_pos zero_lt_one hp₀
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn Real>=0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow 

Depends on / 依赖: NNReal, NNReal.orderIsoRpow, NNReal.orderIsoRpow_symm_eq, StrictConvexOn, convex_univ, div_pos, f.symm, one_lt_div, orderIsoRpow, orderIsoRpow_symm_eq, strictConvexOn_rpow, zero_lt_one
-/
lemma strictConcaveOn_rpow {p : Real} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn Real>=0 univ fun x : Real>=0 => x ^ p := by
  have hp₀' : 0 < 1 / p := div_pos zero_lt_one hp₀
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn Real>=0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 x.2 y.2 (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : forall x, f.symm x = x ^ p := by simp [f, NNReal.orderIsoRpow_symm_eq]
  refine ⟨convex_univ, fun x mx y my hxy a b ha hb hab => ?_⟩
  simp only [← h₂]
  exact (f.strictConcaveOn_symm h₁).2 mx my hxy ha hb hab

/--
lemma `concaveOn_rpow` / 引理 `concaveOn_rpow`

English:
lemma concaveOn_rpow
  given: {p : Real} (hp₀ : 0 <= p) (hp₁ : p <= 1)
  proof: by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) convex_univ
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id convex_univ
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

中文:
引理 concaveOn_rpow
  条件: {p : 实数} (hp₀ : 0 <= p) (hp₁ : p <= 1)
  证明: by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) convex_univ
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id convex_univ
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

Depends on / 依赖: concaveOn, concaveOn_const, concaveOn_id, convex_univ, eq_or_lt_of_le, rpow_one, rpow_zero, strictConcaveOn_rpow
-/
lemma concaveOn_rpow {p : Real} (hp₀ : 0 <= p) (hp₁ : p <= 1) :
    ConcaveOn Real>=0 univ fun x : Real>=0 => x ^ p := by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) convex_univ
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id convex_univ
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

/--
lemma `strictConcaveOn_sqrt` / 引理 `strictConcaveOn_sqrt`

English:
lemma strictConcaveOn_sqrt
  statement: StrictConcaveOn Real>=0 univ NNReal.sqrt
  proof: by
  have : NNReal.sqrt = fun x : Real>=0 => x ^ (1 / (2 : Real)) := by
    ext x; exact mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

中文:
引理 strictConcaveOn_sqrt
  结论: StrictConcaveOn 实数>=0 univ NN实数.sqrt
  证明: by
  have : NNReal.sqrt = fun x : Real>=0 => x ^ (1 / (2 : Real)) := by
    ext x; exact mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

Depends on / 依赖: NNReal, NNReal.sqrt, NNReal.sqrt_eq_rpow, mod_cast, sqrt_eq_rpow, strictConcaveOn_rpow
-/
lemma strictConcaveOn_sqrt : StrictConcaveOn Real>=0 univ NNReal.sqrt := by
  have : NNReal.sqrt = fun x : Real>=0 => x ^ (1 / (2 : Real)) := by
    ext x; exact mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end NNReal

namespace Real

open NNReal

/--
lemma `strictConcaveOn_rpow` / 引理 `strictConcaveOn_rpow`

English:
lemma strictConcaveOn_rpow
  given: {p : Real} (hp₀ : 0 < p) (hp₁ : p < 1)
  proof: by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : Real>=0 := .mk x hx
  let y' : Real>=0 := .mk y hy
  let a' : Real>=0 := .mk a ha.le
  let b' : Real>=0 := .mk b hb.le
  have hxy' : x' != y' := Subtype.coe_ne_coe.1 hxy
  have hab' : a' + b' = 1 := by ext; simp [a', b', ha

中文:
引理 strictConcaveOn_rpow
  条件: {p : 实数} (hp₀ : 0 < p) (hp₁ : p < 1)
  证明: by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : Real>=0 := .mk x hx
  let y' : Real>=0 := .mk y hy
  let a' : Real>=0 := .mk a ha.le
  let b' : Real>=0 := .mk b hb.le
  have hxy' : x' != y' := Subtype.coe_ne_coe.1 hxy
  have hab' : a' + b' = 1 := by ext; simp [a', b', ha

Depends on / 依赖: NNReal, NNReal.strictConcaveOn_rpow, Set.mem_univ, Subtype, Subtype.coe_ne_coe, coe_ne_coe, convex_Ici, ha.le, hb.le, mem_univ, mod_cast, strictConcaveOn_rpow
-/
lemma strictConcaveOn_rpow {p : Real} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn Real (Set.Ici 0) fun x : Real => x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : Real>=0 := .mk x hx
  let y' : Real>=0 := .mk y hy
  let a' : Real>=0 := .mk a ha.le
  let b' : Real>=0 := .mk b hb.le
  have hxy' : x' != y' := Subtype.coe_ne_coe.1 hxy
  have hab' : a' + b' = 1 := by ext; simp [a', b', hab]
  exact_mod_cast (NNReal.strictConcaveOn_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (mod_cast ha) (mod_cast hb) hab'

/--
lemma `concaveOn_rpow` / 引理 `concaveOn_rpow`

English:
lemma concaveOn_rpow
  given: {p : Real} (hp₀ : 0 <= p) (hp₁ : p <= 1)
  proof: by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) (convex_Ici _)
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id (convex_Ici _)
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

中文:
引理 concaveOn_rpow
  条件: {p : 实数} (hp₀ : 0 <= p) (hp₁ : p <= 1)
  证明: by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) (convex_Ici _)
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id (convex_Ici _)
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

Depends on / 依赖: concaveOn, concaveOn_const, concaveOn_id, convex_Ici, eq_or_lt_of_le, rpow_one, rpow_zero, strictConcaveOn_rpow
-/
lemma concaveOn_rpow {p : Real} (hp₀ : 0 <= p) (hp₁ : p <= 1) :
    ConcaveOn Real (Set.Ici 0) fun x : Real => x ^ p := by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using! concaveOn_const (c := 1) (convex_Ici _)
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using! concaveOn_id (convex_Ici _)
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

/--
lemma `strictConcaveOn_sqrt` / 引理 `strictConcaveOn_sqrt`

English:
lemma strictConcaveOn_sqrt
  statement: StrictConcaveOn Real (Set.Ici 0) (√· : Real -> Real)
  proof: by
  rw [funext Real.sqrt_eq_rpow]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

中文:
引理 strictConcaveOn_sqrt
  结论: StrictConcaveOn 实数 (Set.Ici 0) (√· : 实数 -> 实数)
  证明: by
  rw [funext Real.sqrt_eq_rpow]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

Depends on / 依赖: Real.sqrt_eq_rpow, sqrt_eq_rpow, strictConcaveOn_rpow
-/
lemma strictConcaveOn_sqrt : StrictConcaveOn Real (Set.Ici 0) (√· : Real -> Real) := by
  rw [funext Real.sqrt_eq_rpow]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end Real
