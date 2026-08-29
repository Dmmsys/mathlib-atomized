/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces (Bessel potential spaces)

In this file we define Sobolev spaces on normed vector spaces via the Fourier transform.
These spaces are also known as Bessel potential spaces. The Bessel potential operator
`besselPotential` is the Fourier multiplier with the symbol `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)` and a
tempered distribution `u` belongs to the Sobolev space `H ^ {s, p}` if
`besselPotential E F s u` can be represented by a `Lp` function, informally this is written as
`𝓕⁻ (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) 𝓕 u ∈ Lp`.

Note that the Bessel potential is the operator `(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` and not
`(1 - Δ) ^ (s / 2)` due to the convention of the Fourier transform. This obviously does not impact
the definition of the Sobolev spaces.

## Main definitions

* `TemperedDistribution.besselPotential`: The Bessel potential operator is the Fourier multiplier
  with the function `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TemperedDistribution.memSobolev`: A tempered distribution lies in the Sobolev space of order `s`
  and `p` if `besselPotential E F s u ∈ Lp`.

## Main statements

* `SchwartzMap.memSobolev`: Each Schwartz function belongs to every Sobolev space
* `TemperedDistribution.memSobolev_two_iff_fourier`: The characterization of `p = 2` Sobolev
  functions
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`: If `u` is a Sobolev
  function, then `g • u` is a Sobolev function of the same order provided `g` is bounded.
* `TemperedDistribution.MemSobolev.lineDerivOp`: If `u` is a Sobolev function of order `s`, then
  `∂_{m} u` is a Sobolev function of order `s - 1`.
* `TemperedDistribution.MemSobolev.laplacian`: If `u` is a Sobolev function of order `s`, then
  `Δ u` is a Sobolev function of order `s - 2`.


## References
* [M. Taylor, *Partial Differential Equations 1*][taylorPDE1]
* [W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*][mclean2000]

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

section normed

variable [NormedSpace Complex F]

variable (E F) in
/--
Definition of `besselPotential` / `besselPotential` 的定义

English:
definition besselPotential
  signature: (s : Real)
  body: fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real))

中文:
定义 besselPotential
  签名: (s : 实数)
  定义体: fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real))

Depends on / 依赖: fourierMultiplierCLM
-/
def besselPotential (s : Real) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real))

variable (E F) in
@[simp]
/--
theorem `besselPotential_zero` / 定理 `besselPotential_zero`

English:
theorem besselPotential_zero
  statement: besselPotential E F 0 = ContinuousLinearMap.id Complex _
  proof: by
  ext f
  simp [besselPotential]

@[simp]

中文:
定理 besselPotential_zero
  结论: besselPotential E F 0 = 连续线性映射.id 复形 _
  证明: by
  ext f
  simp [besselPotential]

@[simp]

Depends on / 依赖: besselPotential
-/
theorem besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id Complex _ := by
  ext f
  simp [besselPotential]

@[simp]
/--
theorem `besselPotential_besselPotential_apply` / 定理 `besselPotential_besselPotential_apply`

English:
theorem besselPotential_besselPotential_apply
  given: (s s' : Real) (f : 𝓢'(E, F))
  proof: by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

中文:
定理 besselPotential_besselPotential_apply
  条件: (s s' : 实数) (f : 𝓢'(E, F))
  证明: by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

Depends on / 依赖: Pi.mul_apply, Real.rpow_add, besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply, fun_prop, mul_apply, rpow_add
-/
theorem besselPotential_besselPotential_apply (s s' : Real) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f := by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

/--
theorem `besselPotential_compL_besselPotential` / 定理 `besselPotential_compL_besselPotential`

English:
theorem besselPotential_compL_besselPotential
  given: (s s' : Real)
  proof: by
  ext f : 1
  exact besselPotential_besselPotential_apply s s' f

中文:
定理 besselPotential_compL_besselPotential
  条件: (s s' : 实数)
  证明: by
  ext f : 1
  exact besselPotential_besselPotential_apply s s' f

Depends on / 依赖: besselPotential_besselPotential_apply
-/
theorem besselPotential_compL_besselPotential (s s' : Real) :
    besselPotential E F s' ∘L besselPotential E F s = besselPotential E F (s + s') := by
  ext f : 1
  exact besselPotential_besselPotential_apply s s' f

/--
theorem `besselPotential_neg_apply_eq_iff` / 定理 `besselPotential_neg_apply_eq_iff`

English:
theorem besselPotential_neg_apply_eq_iff
  given: (s : Real) (f g : 𝓢'(E, F))
  proof: by
  constructor <;>
  intro h <;> simp [← h]

中文:
定理 besselPotential_neg_apply_eq_iff
  条件: (s : 实数) (f g : 𝓢'(E, F))
  证明: by
  constructor <;>
  intro h <;> simp [← h]
-/
theorem besselPotential_neg_apply_eq_iff (s : Real) (f g : 𝓢'(E, F)) :
    besselPotential E F (-s) f = g ↔ besselPotential E F s g = f := by
  constructor <;>
  intro h <;> simp [← h]

open scoped Real Laplacian LineDeriv

/--
theorem `besselPotential_neg_one_lineDerivOp_eq` / 定理 `besselPotential_neg_one_lineDerivOp_eq`

English:
theorem besselPotential_neg_one_lineDerivOp_eq
  given: {m : E} (f : 𝓢'(E, F))
  proof: by
  rw [lineDeriv_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

中文:
定理 besselPotential_neg_one_lineDerivOp_eq
  条件: {m : E} (f : 𝓢'(E, F))
  证明: by
  rw [lineDeriv_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_smul_of_tower, besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply, fun_prop, lineDeriv_eq_fourierMultiplierCLM, map_smul_of_tower
-/
theorem besselPotential_neg_one_lineDerivOp_eq {m : E} (f : 𝓢'(E, F)) :
    (besselPotential E F (-1)) (∂_{m} f) =
      (2 * π * Complex.I) • fourierMultiplierCLM F (fun x => Complex.ofReal <|
      inner Real x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : Real)) f := by
  rw [lineDeriv_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

/--
theorem `besselPotential_neg_two_laplacian_eq` / 定理 `besselPotential_neg_two_laplacian_eq`

English:
theorem besselPotential_neg_two_laplacian_eq
  given: (f : 𝓢'(E, F))
  proof: by
  rw [laplacian_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

中文:
定理 besselPotential_neg_two_laplacian_eq
  条件: (f : 𝓢'(E, F))
  证明: by
  rw [laplacian_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_smul_of_tower, besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply, fun_prop, laplacian_eq_fourierMultiplierCLM, map_smul_of_tower
-/
theorem besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) :
    (besselPotential E F (-2)) (Δ f) = -(2 * π) ^ 2 •
      fourierMultiplierCLM F (fun x => Complex.ofReal <| ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : Real)) f := by
  rw [laplacian_eq_fourierMultiplierCLM]; rw [besselPotential]; rw [ContinuousLinearMap.map_smul_of_tower]; rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

end normed

section inner

variable [InnerProductSpace Complex F]

open FourierTransform

@[simp]
/--
theorem `fourier_besselPotential_eq_smulLeftCLM_fourier_apply` / 定理 `fourier_besselPotential_eq_smulLeftCLM_fourier_apply`

English:
theorem fourier_besselPotential_eq_smulLeftCLM_fourier_apply
  given: (s : Real) (f : 𝓢'(E, F))
  proof: by
  simp [besselPotential, fourierMultiplierCLM]

中文:
定理 fourier_besselPotential_eq_smulLeftCLM_fourier_apply
  条件: (s : 实数) (f : 𝓢'(E, F))
  证明: by
  simp [besselPotential, fourierMultiplierCLM]

Depends on / 依赖: besselPotential, fourierMultiplierCLM
-/
theorem fourier_besselPotential_eq_smulLeftCLM_fourier_apply (s : Real) (f : 𝓢'(E, F)) :
    𝓕 (besselPotential E F s f) =
      smulLeftCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) (𝓕 f) := by
  simp [besselPotential, fourierMultiplierCLM]

end inner

section normed

variable [NormedSpace Complex F] [CompleteSpace F]

/--
Definition of `MemSobolev` / `MemSobolev` 的定义

English:
definition MemSobolev
  signature: (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)] (f : 𝓢'(E, F))
  body: exists (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

中文:
定义 MemSobolev
  签名: (s : 实数) (p : 实数>=0∞) [hp : Fact (1 <= p)] (f : 𝓢'(E, F))
  定义体: exists (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

Depends on / 依赖: Measure, besselPotential, volume
-/
def MemSobolev (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)] (f : 𝓢'(E, F)) : Prop :=
  exists (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

/--
theorem `memSobolev_zero_iff` / 定理 `memSobolev_zero_iff`

English:
theorem memSobolev_zero_iff
  given: {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  statement: MemSobolev 0 p f ↔
  proof: by
  simp [MemSobolev]

中文:
定理 memSobolev_zero_iff
  条件: {p : 实数>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  结论: MemSobolev 0 p f ↔
  证明: by
  simp [MemSobolev]

Depends on / 依赖: MemSobolev
-/
theorem memSobolev_zero_iff {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    exists (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]

/--
theorem `MemSobolev.add` / 定理 `MemSobolev.add`

English:
theorem MemSobolev.add
  statement: {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
  proof: by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_add, hf, hg]

中文:
定理 MemSobolev.add
  结论: {s : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
  证明: by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_add, hf, hg]

Depends on / 依赖: Lp.toTemperedDistributionCLM_apply, map_add, toTemperedDistributionCLM_apply
-/
theorem MemSobolev.add {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_add, hf, hg]

/--
theorem `MemSobolev.sub` / 定理 `MemSobolev.sub`

English:
theorem MemSobolev.sub
  statement: {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
  proof: by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' - g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_sub, hf, hg]

中文:
定理 MemSobolev.sub
  结论: {s : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
  证明: by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' - g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_sub, hf, hg]

Depends on / 依赖: Lp.toTemperedDistributionCLM_apply, map_sub, toTemperedDistributionCLM_apply
-/
theorem MemSobolev.sub {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f - g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' - g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_sub, hf, hg]

/--
theorem `MemSobolev.neg` / 定理 `MemSobolev.neg`

English:
theorem MemSobolev.neg
  statement: {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  proof: by
  obtain ⟨f', hf⟩ := hf
  use -f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_neg, hf]

中文:
定理 MemSobolev.neg
  结论: {s : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  证明: by
  obtain ⟨f', hf⟩ := hf
  use -f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_neg, hf]

Depends on / 依赖: Lp.toTemperedDistributionCLM_apply, map_neg, toTemperedDistributionCLM_apply
-/
theorem MemSobolev.neg {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (-f) := by
  obtain ⟨f', hf⟩ := hf
  use -f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_neg, hf]

/--
theorem `MemSobolev.smul` / 定理 `MemSobolev.smul`

English:
theorem MemSobolev.smul
  statement: {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] (c : Complex) {f : 𝓢'(E, F)}
  proof: by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [hf]

中文:
定理 MemSobolev.smul
  结论: {s : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] (c : 复形) {f : 𝓢'(E, F)}
  证明: by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [hf]

Depends on / 依赖: Lp.toTemperedDistributionCLM_apply, toTemperedDistributionCLM_apply
-/
theorem MemSobolev.smul {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] (c : Complex) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [hf]

variable (E F) in
@[simp]
/--
theorem `memSobolev_fun_zero` / 定理 `memSobolev_fun_zero`

English:
theorem memSobolev_fun_zero
  given: (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)]
  proof: by
  use 0
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [map_zero]

@[simp]

中文:
定理 memSobolev_fun_zero
  条件: (s : 实数) (p : 实数>=0∞) [hp : Fact (1 <= p)]
  证明: by
  use 0
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [map_zero]

@[simp]

Depends on / 依赖: Lp.toTemperedDistributionCLM_apply, map_zero, toTemperedDistributionCLM_apply
-/
theorem memSobolev_fun_zero (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)] :
    MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [map_zero]

@[simp]
/--
theorem `memSobolev_besselPotential_iff` / 定理 `memSobolev_besselPotential_iff`

English:
theorem memSobolev_besselPotential_iff
  given: {s r : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  proof: by
  simp [MemSobolev]

中文:
定理 memSobolev_besselPotential_iff
  条件: {s r : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)}
  证明: by
  simp [MemSobolev]

Depends on / 依赖: MemSobolev
-/
theorem memSobolev_besselPotential_iff {s r : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)} :
    MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r + s) p f := by
  simp [MemSobolev]

/--
theorem `_root_.SchwartzMap.memSobolev` / 定理 `_root_.SchwartzMap.memSobolev`

English:
theorem _root_.SchwartzMap.memSobolev
  given: {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] (f : 𝓢(E, F))
  proof: by
  use (SchwartzMap.fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) f).toLp p
  rw [besselPotential]; rw [Lp.toTemperedDistribution_toLp_eq]; rw [fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal Complex
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

中文:
定理 _root_.Schwartz映射.memSobolev
  条件: {s : 实数} {p : 实数>=0∞} [hp : Fact (1 <= p)] (f : 𝓢(E, F))
  证明: by
  use (SchwartzMap.fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) f).toLp p
  rw [besselPotential]; rw [Lp.toTemperedDistribution_toLp_eq]; rw [fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal Complex
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

Depends on / 依赖: Function, Function.hasTemperateGrowth_one_add_norm_sq_rpow, Lp.toTemperedDistribution_toLp_eq, SchwartzMap, SchwartzMap.fourierMultiplierCLM, SchwartzMap.fourierMultiplierCLM_ofReal, besselPotential, fourierMultiplierCLM, fourierMultiplierCLM_ofReal, fourierMultiplierCLM_toTemperedDistributionCLM_eq, fun_prop, hasTemperateGrowth_one_add_norm_sq_rpow, toTemperedDistribution_toLp_eq
-/
theorem _root_.SchwartzMap.memSobolev {s : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] (f : 𝓢(E, F)) :
    MemSobolev s p (f : 𝓢'(E, F)) := by
  use (SchwartzMap.fourierMultiplierCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) f).toLp p
  rw [besselPotential]; rw [Lp.toTemperedDistribution_toLp_eq]; rw [fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal Complex
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

end normed

section inner

variable [InnerProductSpace Complex F] [CompleteSpace F]

/--
theorem `memSobolev_iff_exists_smulLeftCLM_fourier` / 定理 `memSobolev_iff_exists_smulLeftCLM_fourier`

English:
theorem memSobolev_iff_exists_smulLeftCLM_fourier
  given: {s : Real} {f : 𝓢'(E, F)}
  proof: by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf']; rw [Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential]; rw [TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf']; rw [Lp.fourierInv_toTemperedDistribution_eq f']

中文:
定理 memSobolev_iff_存在_smulLeftCLM_fourier
  条件: {s : 实数} {f : 𝓢'(E, F)}
  证明: by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf']; rw [Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential]; rw [TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf']; rw [Lp.fourierInv_toTemperedDistribution_eq f']

Depends on / 依赖: Lp.fourierInv_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq, TemperedDistribution, TemperedDistribution.fourierMultiplierCLM_apply, apply_fun, besselPotential, fourierInv_toTemperedDistribution_eq, fourierMultiplierCLM_apply, fourier_besselPotential_eq_smulLeftCLM_fourier_apply, fourier_toTemperedDistribution_eq
-/
theorem memSobolev_iff_exists_smulLeftCLM_fourier {s : Real} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ exists (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) (𝓕 f) = f' := by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf']; rw [Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential]; rw [TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf']; rw [Lp.fourierInv_toTemperedDistribution_eq f']

/--
theorem `memSobolev_zero_iff_exists_fourier` / 定理 `memSobolev_zero_iff_exists_fourier`

English:
theorem memSobolev_zero_iff_exists_fourier
  given: {f : 𝓢'(E, F)}
  proof: by
  simp [memSobolev_iff_exists_smulLeftCLM_fourier]

中文:
定理 memSobolev_zero_iff_存在_fourier
  条件: {f : 𝓢'(E, F)}
  证明: by
  simp [memSobolev_iff_exists_smulLeftCLM_fourier]

Depends on / 依赖: memSobolev_iff_exists_smulLeftCLM_fourier
-/
theorem memSobolev_zero_iff_exists_fourier {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ exists (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_iff_exists_smulLeftCLM_fourier]

/--
theorem `MemSobolev.fourier_memL1` / 定理 `MemSobolev.fourier_memL1`

English:
theorem MemSobolev.fourier_memL1
  statement: {s : Real} (hs : Module.finrank Real E < 2 * s) {f : 𝓢'(E, F)}
  proof: by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have : MemLp (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : Real)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

中文:
定理 MemSobolev.fourier_memL1
  结论: {s : 实数} (hs : 模.finrank 实数 E < 2 * s) {f : 𝓢'(E, F)}
  证明: by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have : MemLp (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : Real)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

Depends on / 依赖: ENNReal, ENNReal.ofReal, HasTemperateGrowth, aestronglyMeasurable, continuous, continuous.aestronglyMeasurable, convert, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, enorm_pow, fun_prop, memSobolev_iff_exists_smulLeftCLM_fourier, memSobolev_iff_exists_smulLeftCLM_fourier.mp, ofReal, ofReal_norm, simp_rw
-/
theorem MemSobolev.fourier_memL1 {s : Real} (hs : Module.finrank Real E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    exists (v : Lp F 1 (volume : Measure E)), 𝓕 f = (v : 𝓢'(E, F)) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have : MemLp (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : Real)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

open scoped BoundedContinuousFunction

/--
theorem `MemSobolev.fourierMultiplierCLM_of_bounded` / 定理 `MemSobolev.fourierMultiplierCLM_of_bounded`

English:
theorem MemSobolev.fourierMultiplierCLM_of_bounded
  statement: {s : Real} {f : 𝓢'(E, F)}
  proof: by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E ->ᵇ Complex := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁)]; rw [← hf]; rw [fourierMultiplierCLM_apply]; rw [fourier_fourierInv_eq]; rw [smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop)]; rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

中文:
定理 MemSobolev.fourierMultiplierCLM_of_bounded
  结论: {s : 实数} {f : 𝓢'(E, F)}
  证明: by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E ->ᵇ Complex := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁)]; rw [← hf]; rw [fourierMultiplierCLM_apply]; rw [fourier_fourierInv_eq]; rw [smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop)]; rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ofNormedAddCommGroup, MeasureTheory, MeasureTheory.Lp.toTemperedDistribution_smul_eq, continuous, fourierMultiplierCLM_apply, fourier_fourierInv_eq, fun_prop, memLp_top, memLp_top.toLp, memSobolev_iff_exists_smulLeftCLM_fourier, ofNormedAddCommGroup, smulLeftCLM_smulLeftCLM_apply, toTemperedDistribution_smul_eq, volume
-/
theorem MemSobolev.fourierMultiplierCLM_of_bounded {s : Real} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) {g : E -> Complex} (hg₁ : g.HasTemperateGrowth) (hg₂ : exists C, forall x, ‖g x‖ <= C) :
    MemSobolev s 2 (fourierMultiplierCLM F g f) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E ->ᵇ Complex := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁)]; rw [← hf]; rw [fourierMultiplierCLM_apply]; rw [fourier_fourierInv_eq]; rw [smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop)]; rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

/--
theorem `MemSobolev.mono` / 定理 `MemSobolev.mono`

English:
theorem MemSobolev.mono
  given: {s s' : Real} (h : s' <= s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
  proof: by
  have h' : (s' - s) / 2 <= 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs]; rw [← memSobolev_besselPotential_iff]
  apply hf.fourierMultiplierCLM_of_bounded (by fun_prop)
  use 1
  intro x
  rw [Complex.norm_real]; rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

中文:
定理 MemSobolev.mono
  条件: {s s' : 实数} (h : s' <= s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
  证明: by
  have h' : (s' - s) / 2 <= 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs]; rw [← memSobolev_besselPotential_iff]
  apply hf.fourierMultiplierCLM_of_bounded (by fun_prop)
  use 1
  intro x
  rw [Complex.norm_real]; rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

Depends on / 依赖: Complex.norm_real, Real.norm_eq_abs, Real.rpow_le_one_of_one_le_of_nonpos, abs_eq_self, abs_eq_self.mpr, fourierMultiplierCLM_of_bounded, fun_prop, hf.fourierMultiplierCLM_of_bounded, memSobolev_besselPotential_iff, norm_eq_abs, norm_real, rpow_le_one_of_one_le_of_nonpos
-/
theorem MemSobolev.mono {s s' : Real} (h : s' <= s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s' 2 f := by
  have h' : (s' - s) / 2 <= 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs]; rw [← memSobolev_besselPotential_iff]
  apply hf.fourierMultiplierCLM_of_bounded (by fun_prop)
  use 1
  intro x
  rw [Complex.norm_real]; rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

section LineDeriv

open scoped LineDeriv Laplacian Real

/--
theorem `MemSobolev.lineDerivOp` / 定理 `MemSobolev.lineDerivOp`

English:
theorem MemSobolev.lineDerivOp
  given: {s : Real} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {m : E}
  proof: by
  rw [SubNegMonoid.sub_eq_add_neg s 1]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_one_lineDerivOp_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use ‖m‖
  intro x
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : Real)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity)]; rw [sq_abs]; rw [inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : Real)) ^ (2 : Real) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner Real x m| ^ 2 <= ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow]; rw [mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

中文:
定理 MemSobolev.lineDerivOp
  条件: {s : 实数} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {m : E}
  证明: by
  rw [SubNegMonoid.sub_eq_add_neg s 1]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_one_lineDerivOp_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use ‖m‖
  intro x
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : Real)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity)]; rw [sq_abs]; rw [inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : Real)) ^ (2 : Real) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner Real x m| ^ 2 <= ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow]; rw [mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

Depends on / 依赖: Complex.norm_mul, Complex.norm_real, Complex.ofReal_mul, Real.norm_eq_abs, Real.rpow_neg, SubNegMonoid, SubNegMonoid.sub_eq_add_neg, add_comm, besselPotential_neg_one_lineDerivOp_eq, fourierMultiplierCLM_of_bounded, fun_prop, hf.fourierMultiplierCLM_of_bounded, le_of_sq_le_sq, memSobolev_besselPotential_iff, mul_pow, norm_eq_abs, norm_mul, norm_real, ofReal_mul, rpow_neg
-/
theorem MemSobolev.lineDerivOp {s : Real} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {m : E} :
    MemSobolev (s - 1) 2 (∂_{m} f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 1]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_one_lineDerivOp_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use ‖m‖
  intro x
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : Real)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity)]; rw [sq_abs]; rw [inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : Real)) ^ (2 : Real) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner Real x m| ^ 2 <= ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow]; rw [mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

/--
theorem `MemSobolev.laplacian` / 定理 `MemSobolev.laplacian`

English:
theorem MemSobolev.laplacian
  given: {s : Real} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
  proof: by
  rw [SubNegMonoid.sub_eq_add_neg s 2]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_two_laplacian_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use 1
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]; rw [mul_inv_le_iff₀ (by positivity)]
  grind

中文:
定理 MemSobolev.laplacian
  条件: {s : 实数} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
  证明: by
  rw [SubNegMonoid.sub_eq_add_neg s 2]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_two_laplacian_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use 1
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]; rw [mul_inv_le_iff₀ (by positivity)]
  grind

Depends on / 依赖: Real.norm_eq_abs, Real.rpow_neg, SubNegMonoid, SubNegMonoid.sub_eq_add_neg, abs_norm, abs_of_nonneg, add_comm, besselPotential_neg_two_laplacian_eq, fourierMultiplierCLM_of_bounded, fun_prop, hf.fourierMultiplierCLM_of_bounded, memSobolev_besselPotential_iff, norm_eq_abs, norm_inv, norm_mul, norm_pow, rpow_neg, sub_eq_add_neg
-/
theorem MemSobolev.laplacian {s : Real} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev (s - 2) 2 (Δ f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 2]; rw [add_comm]; rw [← memSobolev_besselPotential_iff]; rw [besselPotential_neg_two_laplacian_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use 1
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]; rw [mul_inv_le_iff₀ (by positivity)]
  grind

end LineDeriv

end inner

end TemperedDistribution
