/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points; exact formulae involving the
Euler-Mascheroni constant will follow in a subsequent PR.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`. For computation of the constant term as
`s → 1`, see `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.
-/

@[expose] public section


open CharZero Set Filter HurwitzZeta

open Complex hiding exp continuous_exp

open scoped Topology Real

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/--
Definition of `completedRiemannZeta₀` / `completedRiemannZeta₀` 的定义

English:
definition completedRiemannZeta₀
  signature: (s : Complex)
  body: completedHurwitzZetaEven₀ 0 s

中文:
定义 completedRiemannZeta₀
  签名: (s : Complex)
  定义体: completedHurwitzZetaEven₀ 0 s
-/
def completedRiemannZeta₀ (s : Complex) : Complex := completedHurwitzZetaEven₀ 0 s

/--
Definition of `completedRiemannZeta` / `completedRiemannZeta` 的定义

English:
definition completedRiemannZeta
  signature: (s : Complex)
  body: completedHurwitzZetaEven 0 s

中文:
定义 completedRiemannZeta
  签名: (s : Complex)
  定义体: completedHurwitzZetaEven 0 s

Depends on / 依赖: completedHurwitzZetaEven
-/
def completedRiemannZeta (s : Complex) : Complex := completedHurwitzZetaEven 0 s

/--
lemma `HurwitzZeta.completedHurwitzZetaEven_zero` / 引理 `HurwitzZeta.completedHurwitzZetaEven_zero`

English:
lemma HurwitzZeta.completedHurwitzZetaEven_zero
  given: (s : Complex)
  proof: rfl

中文:
引理 HurwitzZeta.completedHurwitzZetaEven_zero
  条件: (s : Complex)
  证明: rfl
-/
lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : Complex) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := rfl

/--
lemma `HurwitzZeta.completedHurwitzZetaEven₀_zero` / 引理 `HurwitzZeta.completedHurwitzZetaEven₀_zero`

English:
lemma HurwitzZeta.completedHurwitzZetaEven₀_zero
  given: (s : Complex)
  proof: rfl

中文:
引理 HurwitzZeta.completedHurwitzZetaEven₀_zero
  条件: (s : Complex)
  证明: rfl
-/
lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : Complex) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl

/--
lemma `HurwitzZeta.completedCosZeta_zero` / 引理 `HurwitzZeta.completedCosZeta_zero`

English:
lemma HurwitzZeta.completedCosZeta_zero
  given: (s : Complex)
  proof: by
  rw [completedRiemannZeta]; rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [hurwitzEvenFEPair_zero_symm]

中文:
引理 HurwitzZeta.completedCosZeta_zero
  条件: (s : Complex)
  证明: by
  rw [completedRiemannZeta]; rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [hurwitzEvenFEPair_zero_symm]

Depends on / 依赖: completedCosZeta, completedHurwitzZetaEven, completedRiemannZeta, hurwitzEvenFEPair_zero_symm
-/
lemma HurwitzZeta.completedCosZeta_zero (s : Complex) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta]; rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [hurwitzEvenFEPair_zero_symm]

/--
lemma `HurwitzZeta.completedCosZeta₀_zero` / 引理 `HurwitzZeta.completedCosZeta₀_zero`

English:
lemma HurwitzZeta.completedCosZeta₀_zero
  given: (s : Complex)
  proof: by
  rw [completedRiemannZeta₀]; rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [hurwitzEvenFEPair_zero_symm]

中文:
引理 HurwitzZeta.completedCosZeta₀_zero
  条件: (s : Complex)
  证明: by
  rw [completedRiemannZeta₀]; rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [hurwitzEvenFEPair_zero_symm]

Depends on / 依赖: hurwitzEvenFEPair_zero_symm
-/
lemma HurwitzZeta.completedCosZeta₀_zero (s : Complex) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀]; rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [hurwitzEvenFEPair_zero_symm]

/--
lemma `completedRiemannZeta_eq` / 引理 `completedRiemannZeta_eq`

English:
lemma completedRiemannZeta_eq
  given: (s : Complex)
  proof: by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

中文:
引理 completedRiemannZeta_eq
  条件: (s : Complex)
  证明: by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

Depends on / 依赖: completedHurwitzZetaEven_eq, completedRiemannZeta, if_true, simp_rw
-/
lemma completedRiemannZeta_eq (s : Complex) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

/--
theorem `differentiable_completedZeta₀` / 定理 `differentiable_completedZeta₀`

English:
theorem differentiable_completedZeta₀
  statement: Differentiable Complex completedRiemannZeta₀
  proof: differentiable_completedHurwitzZetaEven₀ 0

中文:
定理 differentiable_completedZeta₀
  结论: Differentiable Complex completedRiemannZeta₀
  证明: differentiable_completedHurwitzZetaEven₀ 0
-/
theorem differentiable_completedZeta₀ : Differentiable Complex completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0

/--
theorem `differentiableAt_completedZeta` / 定理 `differentiableAt_completedZeta`

English:
theorem differentiableAt_completedZeta
  given: {s : Complex} (hs : s != 0) (hs' : s != 1)
  proof: differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

中文:
定理 differentiableAt_completedZeta
  条件: {s : Complex} (hs : s != 0) (hs' : s != 1)
  证明: differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

Depends on / 依赖: Or.inl, differentiableAt_completedHurwitzZetaEven
-/
theorem differentiableAt_completedZeta {s : Complex} (hs : s != 0) (hs' : s != 1) :
    DifferentiableAt Complex completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/--
theorem `completedRiemannZeta₀_one_sub` / 定理 `completedRiemannZeta₀_one_sub`

English:
theorem completedRiemannZeta₀_one_sub
  given: (s : Complex)
  proof: by
  rw [← completedHurwitzZetaEven₀_zero]; rw [← completedCosZeta₀_zero]; rw [completedHurwitzZetaEven₀_one_sub]

中文:
定理 completedRiemannZeta₀_one_sub
  条件: (s : Complex)
  证明: by
  rw [← completedHurwitzZetaEven₀_zero]; rw [← completedCosZeta₀_zero]; rw [completedHurwitzZetaEven₀_one_sub]
-/
theorem completedRiemannZeta₀_one_sub (s : Complex) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero]; rw [← completedCosZeta₀_zero]; rw [completedHurwitzZetaEven₀_one_sub]

/--
theorem `completedRiemannZeta_one_sub` / 定理 `completedRiemannZeta_one_sub`

English:
theorem completedRiemannZeta_one_sub
  given: (s : Complex)
  proof: by
  rw [← completedHurwitzZetaEven_zero]; rw [← completedCosZeta_zero]; rw [completedHurwitzZetaEven_one_sub]

中文:
定理 completedRiemannZeta_one_sub
  条件: (s : Complex)
  证明: by
  rw [← completedHurwitzZetaEven_zero]; rw [← completedCosZeta_zero]; rw [completedHurwitzZetaEven_one_sub]

Depends on / 依赖: completedCosZeta_zero, completedHurwitzZetaEven_one_sub, completedHurwitzZetaEven_zero
-/
theorem completedRiemannZeta_one_sub (s : Complex) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero]; rw [← completedCosZeta_zero]; rw [completedHurwitzZetaEven_one_sub]

/--
lemma `completedRiemannZeta_residue_one` / 引理 `completedRiemannZeta_residue_one`

English:
lemma completedRiemannZeta_residue_one
  proof: completedHurwitzZetaEven_residue_one 0

中文:
引理 completedRiemannZeta_residue_one
  证明: completedHurwitzZetaEven_residue_one 0

Depends on / 依赖: completedHurwitzZetaEven_residue_one
-/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s => (s - 1) * completedRiemannZeta s) (𝓝[!=] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
@[wikidata Q187235]
/--
Definition of `riemannZeta` / `riemannZeta` 的定义

English:
definition riemannZeta
  body: hurwitzZetaEven 0

中文:
定义 riemannZeta
  定义体: hurwitzZetaEven 0

Depends on / 依赖: hurwitzZetaEven
-/
def riemannZeta := hurwitzZetaEven 0

/--
lemma `HurwitzZeta.hurwitzZetaEven_zero` / 引理 `HurwitzZeta.hurwitzZetaEven_zero`

English:
lemma HurwitzZeta.hurwitzZetaEven_zero
  statement: hurwitzZetaEven 0 = riemannZeta
  proof: rfl

中文:
引理 HurwitzZeta.hurwitzZetaEven_zero
  结论: hurwitzZetaEven 0 = riemannZeta
  证明: rfl
-/
lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl

/--
lemma `HurwitzZeta.cosZeta_zero` / 引理 `HurwitzZeta.cosZeta_zero`

English:
lemma HurwitzZeta.cosZeta_zero
  statement: cosZeta 0 = riemannZeta
  proof: by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

中文:
引理 HurwitzZeta.cosZeta_zero
  结论: cosZeta 0 = riemannZeta
  证明: by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

Depends on / 依赖: completedCosZeta_zero, completedHurwitzZetaEven_zero, cosZeta, hurwitzZetaEven, if_true, riemannZeta, simp_rw
-/
lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

/--
lemma `HurwitzZeta.hurwitzZeta_zero` / 引理 `HurwitzZeta.hurwitzZeta_zero`

English:
lemma HurwitzZeta.hurwitzZeta_zero
  statement: hurwitzZeta 0 = riemannZeta
  proof: by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

中文:
引理 HurwitzZeta.hurwitzZeta_zero
  结论: hurwitzZeta 0 = riemannZeta
  证明: by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

Depends on / 依赖: hurwitzZeta, hurwitzZetaEven_zero, hurwitzZetaOdd_neg
-/
lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

/--
lemma `HurwitzZeta.expZeta_zero` / 引理 `HurwitzZeta.expZeta_zero`

English:
lemma HurwitzZeta.expZeta_zero
  statement: expZeta 0 = riemannZeta
  proof: by
  ext1 s
  rw [expZeta]; rw [cosZeta_zero]; rw [add_eq_left]; rw [mul_eq_zero]; rw [eq_false_intro I_ne_zero]; rw [false_or]; rw [← eq_neg_self_iff]; rw [← sinZeta_neg]; rw [neg_zero]

中文:
引理 HurwitzZeta.expZeta_zero
  结论: expZeta 0 = riemannZeta
  证明: by
  ext1 s
  rw [expZeta]; rw [cosZeta_zero]; rw [add_eq_left]; rw [mul_eq_zero]; rw [eq_false_intro I_ne_zero]; rw [false_or]; rw [← eq_neg_self_iff]; rw [← sinZeta_neg]; rw [neg_zero]

Depends on / 依赖: I_ne_zero, add_eq_left, cosZeta_zero, eq_false_intro, eq_neg_self_iff, expZeta, false_or, mul_eq_zero, neg_zero, sinZeta_neg
-/
lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta]; rw [cosZeta_zero]; rw [add_eq_left]; rw [mul_eq_zero]; rw [eq_false_intro I_ne_zero]; rw [false_or]; rw [← eq_neg_self_iff]; rw [← sinZeta_neg]; rw [neg_zero]

/--
theorem `differentiableAt_riemannZeta` / 定理 `differentiableAt_riemannZeta`

English:
theorem differentiableAt_riemannZeta
  given: {s : Complex} (hs' : s != 1)
  statement: DifferentiableAt Complex riemannZeta s
  proof: differentiableAt_hurwitzZetaEven _ hs'

中文:
定理 differentiableAt_riemannZeta
  条件: {s : Complex} (hs' : s != 1)
  结论: DifferentiableAt Complex riemannZeta s
  证明: differentiableAt_hurwitzZetaEven _ hs'

Depends on / 依赖: differentiableAt_hurwitzZetaEven
-/
theorem differentiableAt_riemannZeta {s : Complex} (hs' : s != 1) : DifferentiableAt Complex riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'

/--
lemma `differentiableOn_riemannZeta` / 引理 `differentiableOn_riemannZeta`

English:
lemma differentiableOn_riemannZeta
  proof: fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

中文:
引理 differentiableOn_riemannZeta
  证明: fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

Depends on / 依赖: differentiableAt_riemannZeta, differentiableWithinAt
-/
lemma differentiableOn_riemannZeta :
    DifferentiableOn Complex riemannZeta {1}ᶜ :=
  fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

/--
lemma `analyticOn_riemannZeta` / 引理 `analyticOn_riemannZeta`

English:
lemma analyticOn_riemannZeta
  proof: differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

中文:
引理 analyticOn_riemannZeta
  证明: differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

Depends on / 依赖: analyticOnNhd, differentiableOn_riemannZeta, differentiableOn_riemannZeta.analyticOnNhd, isOpen_compl_singleton
-/
lemma analyticOn_riemannZeta :
    AnalyticOnNhd Complex riemannZeta {1}ᶜ :=
  differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

/--
theorem `riemannZeta_zero` / 定理 `riemannZeta_zero`

English:
theorem riemannZeta_zero
  statement: riemannZeta 0 = -1 / 2
  proof: by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]

中文:
定理 riemannZeta_zero
  结论: riemannZeta 0 = -1 / 2
  证明: by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]

Depends on / 依赖: Function, Function.update_self, hurwitzZetaEven, if_true, riemannZeta, simp_rw, update_self
-/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]

/--
lemma `riemannZeta_def_of_ne_zero` / 引理 `riemannZeta_def_of_ne_zero`

English:
lemma riemannZeta_def_of_ne_zero
  given: {s : Complex} (hs : s != 0)
  proof: by
  rw [riemannZeta]; rw [hurwitzZetaEven]; rw [Function.update_of_ne hs]; rw [completedHurwitzZetaEven_zero]

中文:
引理 riemannZeta_def_of_ne_zero
  条件: {s : Complex} (hs : s != 0)
  证明: by
  rw [riemannZeta]; rw [hurwitzZetaEven]; rw [Function.update_of_ne hs]; rw [completedHurwitzZetaEven_zero]

Depends on / 依赖: Function, Function.update_of_ne, completedHurwitzZetaEven_zero, hurwitzZetaEven, riemannZeta, update_of_ne
-/
lemma riemannZeta_def_of_ne_zero {s : Complex} (hs : s != 0) :
    riemannZeta s = completedRiemannZeta s / GammaReal s := by
  rw [riemannZeta]; rw [hurwitzZetaEven]; rw [Function.update_of_ne hs]; rw [completedHurwitzZetaEven_zero]

/--
lemma `riemannZeta_eq_completedRiemannZeta₀` / 引理 `riemannZeta_eq_completedRiemannZeta₀`

English:
lemma riemannZeta_eq_completedRiemannZeta₀
  given: {s : Complex} (hs : s != 0)
  statement: riemannZeta s =
  proof: by
  rw [riemannZeta_def_of_ne_zero hs]; rw [completedRiemannZeta_eq]; rw [GammaReal]

中文:
引理 riemannZeta_eq_completedRiemannZeta₀
  条件: {s : Complex} (hs : s != 0)
  结论: riemannZeta s =
  证明: by
  rw [riemannZeta_def_of_ne_zero hs]; rw [completedRiemannZeta_eq]; rw [GammaReal]

Depends on / 依赖: GammaReal, completedRiemannZeta_eq, riemannZeta_def_of_ne_zero
-/
lemma riemannZeta_eq_completedRiemannZeta₀ {s : Complex} (hs : s != 0) : riemannZeta s =
    (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) / (π ^ (-s / 2) * Gamma (s / 2)) := by
  rw [riemannZeta_def_of_ne_zero hs]; rw [completedRiemannZeta_eq]; rw [GammaReal]

/--
lemma `riemannZeta_eq_mul_completedRiemannZeta₀` / 引理 `riemannZeta_eq_mul_completedRiemannZeta₀`

English:
lemma riemannZeta_eq_mul_completedRiemannZeta₀
  given: (s : Complex)
  proof: by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [riemannZeta_zero]
  · rw [riemannZeta_eq_completedRiemannZeta₀ hs, Gamma_add_one (s / 2) (by grind)]
    field

中文:
引理 riemannZeta_eq_mul_completedRiemannZeta₀
  条件: (s : Complex)
  证明: by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [riemannZeta_zero]
  · rw [riemannZeta_eq_completedRiemannZeta₀ hs, Gamma_add_one (s / 2) (by grind)]
    field

Depends on / 依赖: Gamma_add_one, eq_or_ne, riemannZeta_zero
-/
lemma riemannZeta_eq_mul_completedRiemannZeta₀ (s : Complex) :
    riemannZeta s = (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
      (2 * π ^ (-s / 2) * Gamma (s / 2 + 1)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [riemannZeta_zero]
  · rw [riemannZeta_eq_completedRiemannZeta₀ hs, Gamma_add_one (s / 2) (by grind)]
    field

/--
theorem `riemannZeta_neg_two_mul_nat_add_one` / 定理 `riemannZeta_neg_two_mul_nat_add_one`

English:
theorem riemannZeta_neg_two_mul_nat_add_one
  given: (n : Nat)
  statement: riemannZeta (-2 * (n + 1)) = 0
  proof: hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

中文:
定理 riemannZeta_neg_two_mul_nat_add_one
  条件: (n : 自然数)
  结论: riemannZeta (-2 * (n + 1)) = 0
  证明: hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

Depends on / 依赖: hurwitzZetaEven_neg_two_mul_nat_add_one
-/
theorem riemannZeta_neg_two_mul_nat_add_one (n : Nat) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

/--
theorem `riemannZeta_one_sub` / 定理 `riemannZeta_one_sub`

English:
theorem riemannZeta_one_sub
  given: {s : Complex} (hs : forall n : Nat, s != -n) (hs' : s != 1)
  proof: by
  rw [riemannZeta]; rw [hurwitzZetaEven_one_sub 0 hs (Or.inr hs')]; rw [cosZeta_zero]; rw [hurwitzZetaEven_zero]

中文:
定理 riemannZeta_one_sub
  条件: {s : Complex} (hs : 对任意 n : 自然数, s != -n) (hs' : s != 1)
  证明: by
  rw [riemannZeta]; rw [hurwitzZetaEven_one_sub 0 hs (Or.inr hs')]; rw [cosZeta_zero]; rw [hurwitzZetaEven_zero]

Depends on / 依赖: Or.inr, cosZeta_zero, hurwitzZetaEven_one_sub, hurwitzZetaEven_zero, riemannZeta
-/
theorem riemannZeta_one_sub {s : Complex} (hs : forall n : Nat, s != -n) (hs' : s != 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta]; rw [hurwitzZetaEven_one_sub 0 hs (Or.inr hs')]; rw [cosZeta_zero]; rw [hurwitzZetaEven_zero]

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
@[wikidata Q205966]
/--
Definition of `RiemannHypothesis` / `RiemannHypothesis` 的定义

English:
definition RiemannHypothesis
  signature: : Prop
  body: forall (s : Complex) (_ : riemannZeta s = 0) (_ : ¬exists n : Nat, s = -2 * (n + 1)) (_ : s != 1), s.re = 1 / 2

中文:
定义 RiemannHypothesis
  签名: : 命题
  定义体: forall (s : Complex) (_ : riemannZeta s = 0) (_ : ¬exists n : Nat, s = -2 * (n + 1)) (_ : s != 1), s.re = 1 / 2

Depends on / 依赖: riemannZeta, s.re
-/
def RiemannHypothesis : Prop :=
  forall (s : Complex) (_ : riemannZeta s = 0) (_ : ¬exists n : Nat, s = -2 * (n + 1)) (_ : s != 1), s.re = 1 / 2


/--
theorem `completedZeta_eq_tsum_of_one_lt_re` / 定理 `completedZeta_eq_tsum_of_one_lt_re`

English:
theorem completedZeta_eq_tsum_of_one_lt_re
  given: {s : Complex} (hs : 1 < re s)
  proof: by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, GammaReal_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp 

中文:
定理 completedZeta_eq_tsum_of_one_lt_re
  条件: {s : Complex} (hs : 1 < re s)
  证明: by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, GammaReal_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp 

Depends on / 依赖: Complex.ne_zero_of_one_lt_re, GammaReal_def, Nat.cast_zero, QuotientAddGroup, QuotientAddGroup.mk_zero, Real.cos_zero, cast_zero, completedCosZeta_zero, cos_zero, div_zero, hasSum_nat_completedCosZeta, mk_zero, mul_one, mul_one_div, mul_zero, ne_zero_of_one_lt_re, ofReal_one, split_ifs, tsum_eq, tsum_eq.symm
-/
theorem completedZeta_eq_tsum_of_one_lt_re {s : Complex} (hs : 1 < re s) :
    completedRiemannZeta s =
      (π : Complex) ^ (-s / 2) * Gamma (s / 2) * ∑' n : Nat, 1 / (n : Complex) ^ s := by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, GammaReal_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp only [h, Nat.cast_zero, zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero]
  · rfl

/--
theorem `zeta_eq_tsum_one_div_nat_cpow` / 定理 `zeta_eq_tsum_one_div_nat_cpow`

English:
theorem zeta_eq_tsum_one_div_nat_cpow
  given: {s : Complex} (hs : 1 < re s)
  proof: by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

中文:
定理 zeta_eq_tsum_one_div_nat_cpow
  条件: {s : Complex} (hs : 1 < re s)
  证明: by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk_zero, Real.cos_zero, cosZeta_zero, cos_zero, hasSum_nat_cosZeta, mk_zero, mul_zero, ofReal_one, tsum_eq, tsum_eq.symm, zero_mul
-/
theorem zeta_eq_tsum_one_div_nat_cpow {s : Complex} (hs : 1 < re s) :
    riemannZeta s = ∑' n : Nat, 1 / (n : Complex) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

/--
theorem `zeta_eq_tsum_one_div_nat_add_one_cpow` / 定理 `zeta_eq_tsum_one_div_nat_add_one_cpow`

English:
theorem zeta_eq_tsum_one_div_nat_add_one_cpow
  given: {s : Complex} (hs : 1 < re s)
  proof: by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

中文:
定理 zeta_eq_tsum_one_div_nat_add_one_cpow
  条件: {s : Complex} (hs : 1 < re s)
  证明: by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

Depends on / 依赖: Complex.ne_zero_of_one_lt_re, Complex.summable_one_div_nat_cpow, Summable, Summable.tsum_eq_zero_add, ne_zero_of_one_lt_re, summable_one_div_nat_cpow, tsum_eq_zero_add, zero_cpow, zeta_eq_tsum_one_div_nat_cpow
-/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : Complex} (hs : 1 < re s) :
    riemannZeta s = ∑' n : Nat, 1 / (n + 1 : Complex) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

/--
theorem `zeta_nat_eq_tsum_of_gt_one` / 定理 `zeta_nat_eq_tsum_of_gt_one`

English:
theorem zeta_nat_eq_tsum_of_gt_one
  given: {k : Nat} (hk : 1 < k)
  proof: by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

中文:
定理 zeta_nat_eq_tsum_of_gt_one
  条件: {k : 自然数} (hk : 1 < k)
  证明: by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

Depends on / 依赖: Nat.cast_lt, Nat.cast_one, cast_lt, cast_one, cpow_natCast, ofReal_natCast, ofReal_re, zeta_eq_tsum_one_div_nat_cpow
-/
theorem zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1 < k) :
    riemannZeta k = ∑' n : Nat, 1 / (n : Complex) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

/--
lemma `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even` / 引理 `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even`

English:
lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even
  given: {k : Nat} (hk : 2 <= k) (hk2 : Even k)
  proof: by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : Complex)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : Complex) ^ k)⁻¹)]
  ·

中文:
引理 two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even
  条件: {k : 自然数} (hk : 2 <= k) (hk2 : Even k)
  证明: by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : Complex)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : Complex) ^ k)⁻¹)]
  ·

Depends on / 依赖: Even.neg_pow, Summable, Summable.of_nat_of_neg, neg_pow, of_nat_of_neg, of_norm, tsum_int_eq_zero_add_two_mul_tsum_pnat, tsum_pnat_eq_tsum_succ, zeta_eq_tsum_one_div_nat_add_one_cpow
-/
lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : Nat} (hk : 2 <= k) (hk2 : Even k) :
    2 * riemannZeta k = ∑' (n : Int), ((n : Complex) ^ k)⁻¹ := by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : Complex)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : Complex) ^ k)⁻¹)]
  · intro n
    simp [Even.neg_pow hk2]
  · exact (Summable.of_nat_of_neg (by simp [hkk]) (by simp [hkk])).of_norm

/--
lemma `riemannZeta_residue_one` / 引理 `riemannZeta_residue_one`

English:
lemma riemannZeta_residue_one
  statement: Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[!=] 1) (𝓝 1)
  proof: by
  exact hurwitzZetaEven_residue_one 0

中文:
引理 riemannZeta_residue_one
  结论: Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[!=] 1) (𝓝 1)
  证明: by
  exact hurwitzZetaEven_residue_one 0

Depends on / 依赖: hurwitzZetaEven_residue_one
-/
lemma riemannZeta_residue_one : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[!=] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

/--
theorem `tendsto_sub_mul_tsum_nat_cpow` / 定理 `tendsto_sub_mul_tsum_nat_cpow`

English:
theorem tendsto_sub_mul_tsum_nat_cpow
  proof: by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
congr_arg _ zeta_eq_tsum_one_div_nat_cpow hs

中文:
定理 tendsto_sub_mul_tsum_nat_cpow
  证明: by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
congr_arg _ zeta_eq_tsum_one_div_nat_cpow hs

Depends on / 依赖: congr_arg, eventually_mem_nhdsWithin, filter_upwards, riemannZeta_residue_one, tendsto_nhdsWithin_mono_left, zeta_eq_tsum_one_div_nat_cpow
-/
theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : Complex => (s - 1) * ∑' (n : Nat), 1 / (n : Complex) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1) := by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
congr_arg _ zeta_eq_tsum_one_div_nat_cpow hs

/--
theorem `tendsto_sub_mul_tsum_nat_rpow` / 定理 `tendsto_sub_mul_tsum_nat_rpow`

English:
theorem tendsto_sub_mul_tsum_nat_rpow
  proof: by
  rw [← tendsto_ofReal_iff]; rw [ofReal_one]
  have : Tendsto (fun s : Real => (s : Complex)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s => ?_
  simp only [one

中文:
定理 tendsto_sub_mul_tsum_nat_rpow
  证明: by
  rw [← tendsto_ofReal_iff]; rw [ofReal_one]
  have : Tendsto (fun s : Real => (s : Complex)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s => ?_
  simp only [one

Depends on / 依赖: Function, Function.comp_apply, Nat.cast_nonneg, Tendsto, cast_nonneg, comp_apply, continuousWithinAt, continuous_ofReal, continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin, ofReal_cpow, ofReal_inv, ofReal_mul, ofReal_natCast, ofReal_one, ofReal_sub, ofReal_tsum, one_div, tendsto_nhdsWithin, tendsto_ofReal_iff, tendsto_sub_mul_tsum_nat_cpow
-/
theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : Real => (s - 1) * ∑' (n : Nat), 1 / (n : Real) ^ s) (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff]; rw [ofReal_one]
  have : Tendsto (fun s : Real => (s : Complex)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s => ?_
  simp only [one_div, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one, ofReal_tsum,
    ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
