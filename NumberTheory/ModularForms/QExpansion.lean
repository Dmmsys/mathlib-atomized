/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# q-expansions of functions on the upper half plane

We show that a function on the upper half plane with strict period `n` can be written as
`τ ↦ F (𝕢 n τ)` where `F` is analytic on the open unit disc, and `𝕢 n` is the parameter
`τ ↦ exp (2 * I * π * τ / n)`. As an application, we show that cusp forms decay exponentially to 0
as `im τ → ∞`.

We also define the `q`-expansion of a function `f` on the upper half plane, either as a power series
or as a `FormalMultilinearSeries`, and show that it converges to `f` if `f` is periodic, holomorphic
and bounded at infinity.

## Main definitions and results

* `UpperHalfPlane.cuspFunction`: for a function on the upper half plane with strict period `n`,
  this is the function `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of
  limit at `0`.
* `UpperHalfPlane.differentiableAt_cuspFunction`: when `f` is periodic, holomorphic and bounded at
  infinity, its `cuspFunction` is differentiable on the open unit disc (including at `0`).
* `UpperHalfPlane.qExpansion`: the `q`-expansion of a function on the upper half plane (defined as
  the Taylor series of its `cuspFunction`), bundled as a `PowerSeries`.
* `UpperHalfPlane.hasSum_qExpansion`: the `q`-expansion evaluated at `𝕢 n τ` sums to `f τ`, for
  `τ` in the upper half plane.
* `ModularForm.qExpansionRingHom` defines the ring homomorphism from the graded ring of
  modular forms to power series given by taking `q`-expansions.
* `UpperHalfPlane.qExpansion_coeff_unique` shows that q-expansion coefficients are uniquely
  determined.
* There are also more specialized versions of some of these lemmas in the `ModularFormClass`
  namespace.
-/

@[expose] public noncomputable section

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup Metric Set
open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup Topology Manifold

variable {k : Int} {F : Type*} [FunLike F ℍ Complex] {Γ : Subgroup (GL (Fin 2) Real)} {h : Real} (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace UpperHalfPlane

/--
Definition of `valueAtInfty` / `valueAtInfty` 的定义

English:
definition valueAtInfty
  signature: (f : ℍ -> Complex)
  body: limUnder atImInfty f

中文:
定义 valueAtInfty
  签名: (f : ℍ -> 复形)
  定义体: limUnder atImInfty f

Depends on / 依赖: atImInfty, limUnder
-/
def valueAtInfty (f : ℍ -> Complex) : Complex := limUnder atImInfty f

/--
lemma `IsZeroAtImInfty.valueAtInfty_eq_zero` / 引理 `IsZeroAtImInfty.valueAtInfty_eq_zero`

English:
lemma IsZeroAtImInfty.valueAtInfty_eq_zero
  given: {f : ℍ -> Complex} (hf : IsZeroAtImInfty f)
  proof: hf.limUnder_eq

中文:
引理 IsZeroAtImInfty.valueAtInfty_eq_zero
  条件: {f : ℍ -> 复形} (hf : IsZeroAtImInfty f)
  证明: hf.limUnder_eq

Depends on / 依赖: hf.limUnder_eq, limUnder_eq
-/
lemma IsZeroAtImInfty.valueAtInfty_eq_zero {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) :
    valueAtInfty f = 0 :=
  hf.limUnder_eq

/--
lemma `qParam_tendsto_atImInfty` / 引理 `qParam_tendsto_atImInfty`

English:
lemma qParam_tendsto_atImInfty
  given: {h : Real} (hh : 0 < h)
  proof: ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

中文:
引理 qParam_tendsto_atImInfty
  条件: {h : 实数} (hh : 0 < h)
  证明: ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

Depends on / 依赖: Periodic, Periodic.qParam_tendsto, mono_right, nhdsWithin_le_nhds, qParam_tendsto, tendsto_coe_atImInfty
-/
lemma qParam_tendsto_atImInfty {h : Real} (hh : 0 < h) :
    Tendsto (fun τ : ℍ => 𝕢 h τ) atImInfty (nhds 0) :=
  ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

variable (h) in
/--
Definition of `cuspFunction` / `cuspFunction` 的定义

English:
definition cuspFunction
  signature: (f : ℍ -> Complex)
  body: Function.Periodic.cuspFunction h (f ∘ ofComplex)

中文:
定义 cuspFunction
  签名: (f : ℍ -> 复形)
  定义体: Function.Periodic.cuspFunction h (f ∘ ofComplex)

Depends on / 依赖: Function, Function.Periodic.cuspFunction, Periodic, cuspFunction, ofComplex
-/
def cuspFunction (f : ℍ -> Complex) : Complex -> Complex :=
  Function.Periodic.cuspFunction h (f ∘ ofComplex)

/--
theorem `eq_cuspFunction` / 定理 `eq_cuspFunction`

English:
theorem eq_cuspFunction
  statement: {f : ℍ -> Complex} (τ : ℍ) (hh : h != 0)
  proof: by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)

中文:
定理 eq_cuspFunction
  结论: {f : ℍ -> 复形} (τ : ℍ) (hh : h != 0)
  证明: by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)

Depends on / 依赖: Periodic, Periodic.eq_cuspFunction, cuspFunction, eq_cuspFunction
-/
theorem eq_cuspFunction {f : ℍ -> Complex} (τ : ℍ) (hh : h != 0)
    (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ) = f τ := by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)

/--
theorem `differentiableAt_cuspFunction` / 定理 `differentiableAt_cuspFunction`

English:
theorem differentiableAt_cuspFunction
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hfhol ⟨z, hz⟩)))
      (hfbdd.comp_tendsto tendsto_comap_im_ofComplex)
  · exact

中文:
定理 differentiableAt_cuspFunction
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hfhol ⟨z, hz⟩)))
      (hfbdd.comp_tendsto tendsto_comap_im_ofComplex)
  · exact

Depends on / 依赖: Ioi_mem_atTop, Periodic, Periodic.im_invQParam_pos_of_norm_lt_one, Periodic.qParam_right_inv, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, comp_tendsto, differentiableAt_cuspFunction, differentiableAt_cuspFunction_zero, eq_or_ne, eventually_of_mem, hfbdd.comp_tendsto, hfper.differentiableAt_cuspFunction, hfper.differentiableAt_cuspFunction_zero, hh.ne, im_invQParam_pos_of_norm_lt_one, mdifferentiableAt_iff, preimage_mem_comap, qParam_right_inv, tendsto_comap_im_ofComplex
-/
theorem differentiableAt_cuspFunction {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    {q : Complex} (hq : ‖q‖ < 1) : DifferentiableAt Complex (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hfhol ⟨z, hz⟩)))
      (hfbdd.comp_tendsto tendsto_comap_im_ofComplex)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
hfper.differentiableAt_cuspFunction hh.ne' UpperHalfPlane.mdifferentiableAt_iff.mp
        hfhol ⟨_, Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'⟩

/--
lemma `differentiableOn_cuspFunction_ball` / 引理 `differentiableOn_cuspFunction_ball`

English:
lemma differentiableOn_cuspFunction_ball
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: fun _ hz => (differentiableAt_cuspFunction hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
.differentiableWithinAt

中文:
引理 differentiableOn_cuspFunction_ball
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: fun _ hz => (differentiableAt_cuspFunction hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
.differentiableWithinAt

Depends on / 依赖: differentiableAt_cuspFunction, differentiableWithinAt, mem_ball_zero_iff, mem_ball_zero_iff.mp
-/
lemma differentiableOn_cuspFunction_ball {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    DifferentiableOn Complex (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz => (differentiableAt_cuspFunction hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
.differentiableWithinAt

/--
lemma `analyticAt_cuspFunction_zero` / 引理 `analyticAt_cuspFunction_zero`

English:
lemma analyticAt_cuspFunction_zero
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: DifferentiableOn.analyticAt (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : Complex) zero_lt_one)

中文:
引理 analyticAt_cuspFunction_zero
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: DifferentiableOn.analyticAt (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : Complex) zero_lt_one)

Depends on / 依赖: DifferentiableOn, DifferentiableOn.analyticAt, Metric, Metric.ball_mem_nhds, analyticAt, ball_mem_nhds, ball_zero_eq, differentiableOn_cuspFunction_ball, zero_lt_one
-/
lemma analyticAt_cuspFunction_zero {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    AnalyticAt Complex (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : Complex) zero_lt_one)

/--
lemma `cuspFunction_apply_zero` / 引理 `cuspFunction_apply_zero`

English:
lemma cuspFunction_apply_zero
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  refine (Tendsto.limUnder_eq ?_).symm
  have : (cuspFunction h f ∘ fun τ => 𝕢 h τ : ℍ -> Complex) = f := by
    funext τ
    simpa using eq_cuspFunction τ hh.ne' hfper
  simpa [this] using hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

中文:
引理 cuspFunction_apply_zero
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  refine (Tendsto.limUnder_eq ?_).symm
  have : (cuspFunction h f ∘ fun τ => 𝕢 h τ : ℍ -> Complex) = f := by
    funext τ
    simpa using eq_cuspFunction τ hh.ne' hfper
  simpa [this] using hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

Depends on / 依赖: Tendsto, Tendsto.limUnder_eq, continuousAt, cuspFunction, eq_cuspFunction, hfanalytic, hfanalytic.continuousAt.tendsto.comp, hh.ne, limUnder_eq, qParam_tendsto_atImInfty, tendsto
-/
lemma cuspFunction_apply_zero {f : ℍ -> Complex} (hh : 0 < h)
    (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) : cuspFunction h f 0 = valueAtInfty f := by
  refine (Tendsto.limUnder_eq ?_).symm
  have : (cuspFunction h f ∘ fun τ => 𝕢 h τ : ℍ -> Complex) = f := by
    funext τ
    simpa using eq_cuspFunction τ hh.ne' hfper
  simpa [this] using hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

end UpperHalfPlane

namespace SlashInvariantFormClass

/--
theorem `periodic_comp_ofComplex` / 定理 `periodic_comp_ofComplex`

English:
theorem periodic_comp_ofComplex
  given: [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods)
  proof: by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w 

中文:
定理 periodic_comp_ofComplex
  条件: [斜不变形式类 F Γ k] (hΓ : h in Γ.strictPeriods)
  证明: by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w 

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods, add_comm, comp_apply, convert, ofComplex_apply_of_im_nonpos, ofComplex_apply_of_im_pos, vAdd_apply_of_mem_strictPeriods
-/
theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) :
    Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w + h) <= 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

/--
theorem `eq_cuspFunction` / 定理 `eq_cuspFunction`

English:
theorem eq_cuspFunction
  statement: [SlashInvariantFormClass F Γ k] (τ : ℍ)
  proof: eq_cuspFunction τ hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)

中文:
定理 eq_cuspFunction
  结论: [斜不变形式类 F Γ k] (τ : ℍ)
  证明: eq_cuspFunction τ hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
-/
protected theorem eq_cuspFunction [SlashInvariantFormClass F Γ k] (τ : ℍ)
    (hΓ : h in Γ.strictPeriods) (hh : h != 0) : cuspFunction h f (𝕢 h τ) = f τ :=
  eq_cuspFunction τ hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

@[deprecated ModularFormClass.bdd_at_infty (since := "2026-04-19")]
/--
theorem `bounded_at_infty_comp_ofComplex` / 定理 `bounded_at_infty_comp_ofComplex`

English:
theorem bounded_at_infty_comp_ofComplex
  given: [ModularFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ)
  proof: (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex

中文:
定理 bounded_at_infty_comp_ofComplex
  条件: [模形式类 F Γ k] (hi : IsCusp OnePoint.infty Γ)
  证明: (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex

Depends on / 依赖: OnePoint, OnePoint.isBoundedAt_infty_iff.mp, bdd_at_cusps, comp_tendsto, isBoundedAt_infty_iff, tendsto_comap_im_ofComplex
-/
theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ) :
    BoundedAtFilter I∞ (f ∘ ofComplex) :=
  (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex

/--
theorem `differentiableAt_cuspFunction` / 定理 `differentiableAt_cuspFunction`

English:
theorem differentiableAt_cuspFunction
  statement: [ModularFormClass F Γ k]
  proof: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  differentiableAt_cuspFunction hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) hq

中文:
定理 differentiableAt_cuspFunction
  结论: [模形式类 F Γ k]
  证明: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  differentiableAt_cuspFunction hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) hq
-/
protected theorem differentiableAt_cuspFunction [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h in Γ.strictPeriods) {q : Complex} (hq : ‖q‖ < 1) :
    DifferentiableAt Complex (cuspFunction h f) q :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  differentiableAt_cuspFunction hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) hq

/--
lemma `analyticAt_cuspFunction_zero` / 引理 `analyticAt_cuspFunction_zero`

English:
lemma analyticAt_cuspFunction_zero
  statement: [ModularFormClass F Γ k] (hh : 0 < h)
  proof: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

中文:
引理 analyticAt_cuspFunction_zero
  结论: [模形式类 F Γ k] (hh : 0 < h)
  证明: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)
-/
protected lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) : AnalyticAt Complex (cuspFunction h f) 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

end ModularFormClass

namespace UpperHalfPlane

variable (h) in
/--
Definition of `qExpansion` / `qExpansion` 的定义

English:
definition qExpansion
  signature: (f : ℍ -> Complex)
  body: .mk fun m => (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

中文:
定义 qExpansion
  签名: (f : ℍ -> 复形)
  定义体: .mk fun m => (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

Depends on / 依赖: cuspFunction, factorial, iteratedDeriv, m.factorial
-/
def qExpansion (f : ℍ -> Complex) : PowerSeries Complex :=
  .mk fun m => (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

/--
lemma `qExpansion_coeff` / 引理 `qExpansion_coeff`

English:
lemma qExpansion_coeff
  given: (f : ℍ -> Complex) (m : Nat)
  proof: by
  simp [qExpansion]

中文:
引理 qExpansion_coeff
  条件: (f : ℍ -> 复形) (m : 自然数)
  证明: by
  simp [qExpansion]

Depends on / 依赖: qExpansion
-/
lemma qExpansion_coeff (f : ℍ -> Complex) (m : Nat) :
    (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
  simp [qExpansion]

/--
lemma `qExpansion_coeff_zero` / 引理 `qExpansion_coeff_zero`

English:
lemma qExpansion_coeff_zero
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  simp [qExpansion_coeff, cuspFunction_apply_zero hh hfanalytic hfper]

中文:
引理 qExpansion_coeff_zero
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  simp [qExpansion_coeff, cuspFunction_apply_zero hh hfanalytic hfper]

Depends on / 依赖: cuspFunction_apply_zero, hfanalytic, qExpansion_coeff
-/
lemma qExpansion_coeff_zero {f : ℍ -> Complex} (hh : 0 < h)
    (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    (qExpansion h f).coeff 0 = valueAtInfty f := by
  simp [qExpansion_coeff, cuspFunction_apply_zero hh hfanalytic hfper]

/--
lemma `hasSum_qExpansion_of_norm_lt` / 引理 `hasSum_qExpansion_of_norm_lt`

English:
lemma hasSum_qExpansion_of_norm_lt
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  convert!
    hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
      (by simpa using hq) using
    2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

中文:
引理 hasSum_qExpansion_of_norm_lt
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  convert!
    hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
      (by simpa using hq) using
    2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

Depends on / 依赖: convert, differentiableOn_cuspFunction_ball, hasSum_taylorSeries_on_ball, qExpansion_coeff, smul_eq_mul, sub_zero
-/
lemma hasSum_qExpansion_of_norm_lt {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    {q : Complex} (hq : ‖q‖ < 1) :
    HasSum (fun m : Nat => (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert!
    hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
      (by simpa using hq) using
    2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

/--
lemma `hasSum_qExpansion` / 引理 `hasSum_qExpansion`

English:
lemma hasSum_qExpansion
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  have : ‖𝕢 h τ‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  simpa [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd this

中文:
引理 hasSum_qExpansion
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  have : ‖𝕢 h τ‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  simpa [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd this

Depends on / 依赖: Periodic, Periodic.norm_qParam_lt_one, eq_cuspFunction, hasSum_qExpansion_of_norm_lt, hh.ne, im_pos, norm_qParam_lt_one
-/
lemma hasSum_qExpansion {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) : HasSum (fun m : Nat => (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ) := by
  have : ‖𝕢 h τ‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  simpa [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd this

variable (h) in
/--
Definition of `qExpansionFormalMultilinearSeries` / `qExpansionFormalMultilinearSeries` 的定义

English:
definition qExpansionFormalMultilinearSeries
  signature: : FormalMultilinearSeries Complex Complex Complex
  body: .ofScalars Complex fun m => (qExpansion h f).coeff m

@[simp]

中文:
定义 qExpansionFormalMultilinearSeries
  签名: : FormalMultilinearSeries 复形 复形 复形
  定义体: .ofScalars Complex fun m => (qExpansion h f).coeff m

@[simp]

Depends on / 依赖: ofScalars, qExpansion
-/
def qExpansionFormalMultilinearSeries : FormalMultilinearSeries Complex Complex Complex :=
  .ofScalars Complex fun m => (qExpansion h f).coeff m

@[simp]
/--
lemma `qExpansionFormalMultilinearSeries_coeff` / 引理 `qExpansionFormalMultilinearSeries_coeff`

English:
lemma qExpansionFormalMultilinearSeries_coeff
  given: (m : Nat)
  proof: by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars]

中文:
引理 qExpansionFormalMultilinearSeries_coeff
  条件: (m : 自然数)
  证明: by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars, coeff_ofScalars, qExpansionFormalMultilinearSeries
-/
lemma qExpansionFormalMultilinearSeries_coeff (m : Nat) :
    (qExpansionFormalMultilinearSeries h f).coeff m = (qExpansion h f).coeff m := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars]

/--
lemma `qExpansionFormalMultilinearSeries_apply_norm` / 引理 `qExpansionFormalMultilinearSeries_apply_norm`

English:
lemma qExpansionFormalMultilinearSeries_apply_norm
  given: (m : Nat)
  proof: by
  rw [qExpansionFormalMultilinearSeries]; rw [← (ContinuousMultilinearMap.piFieldEquiv Complex (Fin m) Complex).symm.norm_map]
  simp

中文:
引理 qExpansionFormalMultilinearSeries_apply_norm
  条件: (m : 自然数)
  证明: by
  rw [qExpansionFormalMultilinearSeries]; rw [← (ContinuousMultilinearMap.piFieldEquiv Complex (Fin m) Complex).symm.norm_map]
  simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.piFieldEquiv, norm_map, piFieldEquiv, qExpansionFormalMultilinearSeries, symm.norm_map
-/
lemma qExpansionFormalMultilinearSeries_apply_norm (m : Nat) :
    ‖qExpansionFormalMultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖ := by
  rw [qExpansionFormalMultilinearSeries]; rw [← (ContinuousMultilinearMap.piFieldEquiv Complex (Fin m) Complex).symm.norm_map]
  simp

/--
lemma `qExpansionFormalMultilinearSeries_radius` / 引理 `qExpansionFormalMultilinearSeries_radius`

English:
lemma qExpansionFormalMultilinearSeries_radius
  statement: (hh : 0 < h)
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]

中文:
引理 qExpansionFormalMultilinearSeries_radius
  结论: (hh : 0 < h)
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]

Depends on / 依赖: Complex.norm_real, FormalMultilinearSeries, FormalMultilinearSeries.le_radius_of_summable, NNReal, Real.norm_eq_abs, UpperHalfPlane, UpperHalfPlane.hasSum_qExpansion_of_norm_lt, abs_eq, hasSum_qExpansion_of_norm_lt, hr.ne_top, le_of_forall_lt_imp_le_of_dense, le_radius_of_summable, ne_top, norm_eq_abs, norm_mul, norm_pow, norm_real, qExpansionFormalMultilinearSeries_apply_norm, r.abs_eq, simp_rw
-/
lemma qExpansionFormalMultilinearSeries_radius (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    1 <= (qExpansionFormalMultilinearSeries h f).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]
  exact (UpperHalfPlane.hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (by simpa using hr)).summable.norm

/--
lemma `hasSum_cuspFunction_of_hasSum_punctured` / 引理 `hasSum_cuspFunction_of_hasSum_punctured`

English:
lemma hasSum_cuspFunction_of_hasSum_punctured
  statement: {f : ℍ -> Complex} (hh : 0 < h) {c : Nat -> Complex}
  proof: by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1)
  have : cuspFunction h f q = f τ := by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1]
    using! h2
  grind [h

中文:
引理 hasSum_cuspFunction_of_hasSum_punctured
  结论: {f : ℍ -> 复形} (hh : 0 < h) {c : 自然数 -> 复形}
  证明: by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1)
  have : cuspFunction h f q = f τ := by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1]
    using! h2
  grind [h
-/
private lemma hasSum_cuspFunction_of_hasSum_punctured {f : ℍ -> Complex} (hh : 0 < h) {c : Nat -> Complex}
    (hf : forall (τ : ℍ), HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) {q : Complex} (hq : ‖q‖ < 1)
    (hq1 : q != 0) : HasSum (fun m => c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1)
  have : cuspFunction h f q = f τ := by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1]
    using! h2
  grind [hf τ, Periodic.qParam_right_inv]

/--
lemma `hasFPowerSeriesOnBall_update` / 引理 `hasFPowerSeriesOnBall_update`

English:
lemma hasFPowerSeriesOnBall_update
  statement: {f : ℍ -> Complex} (hh : 0 < h) {c : Nat -> Complex}
  proof: by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional Real Complex := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_sum

中文:
引理 hasFPowerSeriesOnBall_update
  结论: {f : ℍ -> 复形} (hh : 0 < h) {c : 自然数 -> 复形}
  证明: by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional Real Complex := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_sum
-/
private lemma hasFPowerSeriesOnBall_update {f : ℍ -> Complex} (hh : 0 < h) {c : Nat -> Complex}
    (hf : forall τ : ℍ, HasSum (fun m : Nat => (c m) • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars Complex c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional Real Complex := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hasSum_cuspFunction_of_hasSum_punctured hh hf (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one]; rw [Metric.eball_coe]; rw [NNReal.coe_one]; rw [mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured hh hf hy hy'

/--
theorem `isBoundedAtImInfty_of_hasSum_qExpansion` / 定理 `isBoundedAtImInfty_of_hasSum_qExpansion`

English:
theorem isBoundedAtImInfty_of_hasSum_qExpansion
  statement: {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h)
  proof: by
  have hfeq : f = fun τ : ℍ => update (cuspFunction h f) 0 (c 0) (𝕢 h τ) := by
    funext τ
    rw [update_of_ne (Periodic.qParam_ne_zero _)]
    exact (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
      (Periodic.norm_qParam_lt_one hh τ.im_pos) (exp_ne_zero _))
  have htend : Tend

中文:
定理 isBoundedAtImInfty_of_hasSum_qExpansion
  结论: {f : ℍ -> 复形} {c : 自然数 -> 复形} (hh : 0 < h)
  证明: by
  have hfeq : f = fun τ : ℍ => update (cuspFunction h f) 0 (c 0) (𝕢 h τ) := by
    funext τ
    rw [update_of_ne (Periodic.qParam_ne_zero _)]
    exact (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
      (Periodic.norm_qParam_lt_one hh τ.im_pos) (exp_ne_zero _))
  have htend : Tend

Depends on / 依赖: Function, Function.comp_def, Periodic, Periodic.norm_qParam_lt_one, Periodic.qParam_ne_zero, Tendsto, atImInfty, comp_def, continuousAt, cuspFunction, exp_ne_zero, hasFPowerSeriesAt, hasFPowerSeriesAt.continuousAt.tendsto.comp, hasFPowerSeriesOnBall_update, hasSum_cuspFunction_of_hasSum_punctured, im_pos, norm_qParam_lt_one, qParam_ne_zero, qParam_tendsto_atImInfty, tendsto
-/
theorem isBoundedAtImInfty_of_hasSum_qExpansion {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h)
    (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) : IsBoundedAtImInfty f := by
  have hfeq : f = fun τ : ℍ => update (cuspFunction h f) 0 (c 0) (𝕢 h τ) := by
    funext τ
    rw [update_of_ne (Periodic.qParam_ne_zero _)]
    exact (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
      (Periodic.norm_qParam_lt_one hh τ.im_pos) (exp_ne_zero _))
  have htend : Tendsto f atImInfty (𝓝 (c 0)) := by
    rw [hfeq]
    simpa [update_self, Function.comp_def] using
      (hasFPowerSeriesOnBall_update hh hf).hasFPowerSeriesAt.continuousAt.tendsto.comp
        (qParam_tendsto_atImInfty hh)
  -- `IsBoundedAtImInfty f = BoundedAtFilter atImInfty f = (f =O[atImInfty] 1)` by definition.
  exact htend.isBigO_one Real

/--
lemma `hasFPowerSeriesOnBall_cuspFunction` / 引理 `hasFPowerSeriesOnBall_cuspFunction`

English:
lemma hasFPowerSeriesOnBall_cuspFunction
  statement: {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h)
  proof: by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars Complex c) 0 1 :=
    hasFPowerSeriesOnBall_update hh hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhe

中文:
引理 hasFPowerSeriesOnBall_cuspFunction
  结论: {f : ℍ -> 复形} {c : 自然数 -> 复形} (hh : 0 < h)
  证明: by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars Complex c) 0 1 :=
    hasFPowerSeriesOnBall_update hh hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhe
-/
lemma hasFPowerSeriesOnBall_cuspFunction {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h)
    (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0)
    (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (.ofScalars Complex c) 0 1 := by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars Complex c) 0 1 :=
    hasFPowerSeriesOnBall_update hh hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhere else
  have H2 : c 0 = cuspFunction h f 0 := by
    have L1 := H1.hasFPowerSeriesAt.continuousAt
    have L2 := hfanalytic.continuousAt
have := (L1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE L2).mp
      by filter_upwards [self_mem_nhdsWithin] with a ha using update_of_ne ha ..
    simpa [update_self] using this.eq_of_nhds
  rwa [update_eq_self_iff.mpr H2] at H1

/--
lemma `qExpansion_coeff_eq_circleIntegral` / 引理 `qExpansion_coeff_eq_circleIntegral`

English:
lemma qExpansion_coeff_eq_circleIntegral
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  have := ((differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm]; rw [← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansi

中文:
引理 qExpansion_coeff_eq_circle整数egral
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  have := ((differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm]; rw [← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansi

Depends on / 依赖: Metric, Metric.closedBall_subset_ball, PowerSeries, PowerSeries.coeff_mk, circleIntegral_one_div_sub_center_pow_smul, closedBall_subset_ball, coeff_mk, differentiableOn_cuspFunction_ball, div_eq_iff, div_eq_inv_mul, div_eq_mul_inv, mul_assoc, mul_comm, one_div_mul_eq_div, qExpansion, simp_rw, smul_eq_mul, sub_zero, two_pi_I_ne_zero
-/
lemma qExpansion_coeff_eq_circleIntegral {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : Nat) {R : Real} (hR : 0 < R) (hR' : R < 1) : (qExpansion h f).coeff n =
      ((2 * π * Complex.I)⁻¹ * ∮ (z : Complex) in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  have := ((differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm]; rw [← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div,
    div_eq_inv_mul]

/--
lemma `qExpansion_coeff_eq_intervalIntegral` / 引理 `qExpansion_coeff_eq_intervalIntegral`

English:
lemma qExpansion_coeff_eq_intervalIntegral
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / h)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
have hR1 : R < 1 := Real.exp_lt_one_iff.2 by simpa [neg_div] using div_pos (by positivity) hh
  -- First apply `qExpansion_coeff_eq_circl

中文:
引理 qExpansion_coeff_eq_interval整数egral
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / h)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
have hR1 : R < 1 := Real.exp_lt_one_iff.2 by simpa [neg_div] using div_pos (by positivity) hh
  -- First apply `qExpansion_coeff_eq_circl
-/
lemma qExpansion_coeff_eq_intervalIntegral {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : Nat) {t : Real} (ht : 0 < t) : (qExpansion h f).coeff n =
      1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩ := by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / h)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
have hR1 : R < 1 := Real.exp_lt_one_iff.2 by simpa [neg_div] using div_pos (by positivity) hh
  -- First apply `qExpansion_coeff_eq_circleIntegral` and rescale from `0 .. 2 * π` to `0 .. h`.
  rw [qExpansion_coeff_eq_circleIntegral hh hfper hfhol hfbdd n hR0 hR1]; rw [circleIntegral]; rw [show 2 * π = h * (2 * π / h) by field_simp]
  conv => enter [1, 2, 2]; rw [show 0 = 0 * (2 * π / h) by simp]
  simp_rw [← intervalIntegral.smul_integral_comp_mul_right, real_smul, ← mul_assoc,
    ← intervalIntegral.integral_const_mul]
  -- Compare the integrands
  congr 1 with u
  let τ : ℍ := ⟨u + t * I, by simpa using ht⟩
  have : circleMap 0 R (u * (2 * π / h)) = 𝕢 h τ := by
    simp only [circleMap, ofReal_exp, ← exp_add, zero_add, τ, R]
    congr 1
    push_cast
    have := I_sq
    grind
  -- now just complex exponential arithmetic to finish
  simp_rw [deriv_circleMap, this, show ↑I = Complex.I by rfl, show u + t * Complex.I = τ by rfl,
    show ⟨↑τ, τ.2⟩ = τ by rfl, eq_cuspFunction _ hh.ne' hfper, smul_eq_mul, pow_succ]
  field_simp [(show 𝕢 h τ != 0 from Complex.exp_ne_zero _), Real.pi_ne_zero, NeZero.ne]
  push_cast
  ring

/--
theorem `exp_decay_sub_atImInfty` / 定理 `exp_decay_sub_atImInfty`

English:
theorem exp_decay_sub_atImInfty
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  have := hfbdd.comp_tendsto tendsto_comap_im_ofComplex
  convert!
    (hfper.exp_decay_sub_of_bounded_at_inf hh
          (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) fun z hz => by
            simpa using (UpperHalfPlane.mdifferentiableAt_iff.mp <| hfhol ⟨z, hz⟩))
          this).c

中文:
定理 exp_decay_sub_atImInfty
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  have := hfbdd.comp_tendsto tendsto_comap_im_ofComplex
  convert!
    (hfper.exp_decay_sub_of_bounded_at_inf hh
          (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) fun z hz => by
            simpa using (UpperHalfPlane.mdifferentiableAt_iff.mp <| hfhol ⟨z, hz⟩))
          this).c

Depends on / 依赖: Ioi_mem_atTop, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, analyticAt_cuspFunction_zero, comp_tendsto, convert, cuspFunction, cuspFunction_apply_zero, eventually_of_mem, exp_decay_sub_of_bounded_at_inf, hfbdd.comp_tendsto, hfper.exp_decay_sub_of_bounded_at_inf, mdifferentiableAt_iff, preimage_mem_comap, tendsto_coe_atImInfty, tendsto_comap_im_ofComplex
-/
theorem exp_decay_sub_atImInfty {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    (fun τ => f τ - valueAtInfty f) =O[atImInfty] fun τ => Real.exp (-2 * π * τ.im / h) := by
  have := hfbdd.comp_tendsto tendsto_comap_im_ofComplex
  convert!
    (hfper.exp_decay_sub_of_bounded_at_inf hh
          (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) fun z hz => by
            simpa using (UpperHalfPlane.mdifferentiableAt_iff.mp <| hfhol ⟨z, hz⟩))
          this).comp_tendsto
      tendsto_coe_atImInfty
  simpa [cuspFunction] using
    (cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd) hfper).symm

namespace IsZeroAtImInfty

variable {f}

/--
lemma `zero_at_infty_comp_ofComplex` / 引理 `zero_at_infty_comp_ofComplex`

English:
lemma zero_at_infty_comp_ofComplex
  given: {f : ℍ -> Complex} (hf : IsZeroAtImInfty f)
  proof: hf.comp tendsto_comap_im_ofComplex

中文:
引理 zero_at_infty_comp_ofComplex
  条件: {f : ℍ -> 复形} (hf : IsZeroAtImInfty f)
  证明: hf.comp tendsto_comap_im_ofComplex

Depends on / 依赖: hf.comp, tendsto_comap_im_ofComplex
-/
lemma zero_at_infty_comp_ofComplex {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  hf.comp tendsto_comap_im_ofComplex

/--
theorem `cuspFunction_apply_zero` / 定理 `cuspFunction_apply_zero`

English:
theorem cuspFunction_apply_zero
  given: {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h)
  proof: Periodic.cuspFunction_zero_of_zero_at_inf hh hf.zero_at_infty_comp_ofComplex

中文:
定理 cuspFunction_apply_zero
  条件: {f : ℍ -> 复形} (hf : IsZeroAtImInfty f) (hh : 0 < h)
  证明: Periodic.cuspFunction_zero_of_zero_at_inf hh hf.zero_at_infty_comp_ofComplex

Depends on / 依赖: Periodic, Periodic.cuspFunction_zero_of_zero_at_inf, cuspFunction_zero_of_zero_at_inf, hf.zero_at_infty_comp_ofComplex, zero_at_infty_comp_ofComplex
-/
theorem cuspFunction_apply_zero {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h) :
    cuspFunction h f 0 = 0 :=
  Periodic.cuspFunction_zero_of_zero_at_inf hh hf.zero_at_infty_comp_ofComplex

/--
theorem `exp_decay_atImInfty` / 定理 `exp_decay_atImInfty`

English:
theorem exp_decay_atImInfty
  statement: {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h)
  proof: by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty hh hfper hfhol hfbdd

中文:
定理 exp_decay_atImInfty
  结论: {f : ℍ -> 复形} (hf : IsZeroAtImInfty f) (hh : 0 < h)
  证明: by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty hh hfper hfhol hfbdd

Depends on / 依赖: exp_decay_sub_atImInfty, hf.valueAtInfty_eq_zero, valueAtInfty_eq_zero
-/
theorem exp_decay_atImInfty {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    f =O[atImInfty] fun τ => Real.exp (-2 * π * τ.im / h) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty hh hfper hfhol hfbdd

end UpperHalfPlane.IsZeroAtImInfty

namespace ModularFormClass

/--
lemma `qExpansion_coeff_eq_intervalIntegral` / 引理 `qExpansion_coeff_eq_intervalIntegral`

English:
lemma qExpansion_coeff_eq_intervalIntegral
  statement: [ModularFormClass F Γ k]
  proof: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  qExpansion_coeff_eq_intervalIntegral hh (periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n ht

中文:
引理 qExpansion_coeff_eq_interval整数egral
  结论: [模形式类 F Γ k]
  证明: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  qExpansion_coeff_eq_intervalIntegral hh (periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n ht
-/
protected lemma qExpansion_coeff_eq_intervalIntegral [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (n : Nat) {t : Real} (ht : 0 < t) :
    (qExpansion h f).coeff n =
      1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩ :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  qExpansion_coeff_eq_intervalIntegral hh (periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n ht

/--
theorem `exp_decay_sub_atImInfty'` / 定理 `exp_decay_sub_atImInfty'`

English:
theorem exp_decay_sub_atImInfty'
  statement: [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
  proof: by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  refine ⟨2 * π / Γ.strictWidthInfty, div_pos Real.two_pi_pos hh, ?_⟩
  convert! exp_decay_sub_atImInfty hh (periodic_comp_ofComp

中文:
定理 exp_decay_sub_atImInfty'
  结论: [模形式类 F Γ k] [Γ.有DetPlusMinusOne]
  证明: by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  refine ⟨2 * π / Γ.strictWidthInfty, div_pos Real.two_pi_pos hh, ?_⟩
  convert! exp_decay_sub_atImInfty hh (periodic_comp_ofComp

Depends on / 依赖: Fact.out, Real.two_pi_pos, bdd_at_infty, convert, div_pos, exp_decay_sub_atImInfty, periodic_comp_ofComplex, ring_nf, strictPeriods, strictWidthInfty, strictWidthInfty_mem_strictPeriods, strictWidthInfty_pos_iff, strictWidthInfty_pos_iff.mpr, two_pi_pos
-/
theorem exp_decay_sub_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] :
    exists c > 0, (fun τ => f τ - valueAtInfty f) =O[atImInfty] (fun τ => Real.exp (-c * τ.im)) := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  refine ⟨2 * π / Γ.strictWidthInfty, div_pos Real.two_pi_pos hh, ?_⟩
  convert! exp_decay_sub_atImInfty hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) using
    3 with τ
  ring_nf

/--
theorem `exp_decay_atImInfty'` / 定理 `exp_decay_atImInfty'`

English:
theorem exp_decay_atImInfty'
  statement: [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
  proof: by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty' f

中文:
定理 exp_decay_atImInfty'
  结论: [模形式类 F Γ k] [Γ.有DetPlusMinusOne]
  证明: by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty' f

Depends on / 依赖: exp_decay_sub_atImInfty, hf.valueAtInfty_eq_zero, valueAtInfty_eq_zero
-/
theorem exp_decay_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] (hf : IsZeroAtImInfty f) :
    exists c > 0, f =O[atImInfty] fun τ => Real.exp (-c * τ.im) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty' f

end ModularFormClass

open ModularFormClass

namespace CuspFormClass

include Γ k -- can't be inferred from statements but shouldn't be omitted
variable [CuspFormClass F Γ k]

/--
theorem `zero_at_infty_comp_ofComplex` / 定理 `zero_at_infty_comp_ofComplex`

English:
theorem zero_at_infty_comp_ofComplex
  given: [Fact (IsCusp OnePoint.infty Γ)]
  proof: (zero_at_infty f).comp tendsto_comap_im_ofComplex

中文:
定理 zero_at_infty_comp_ofComplex
  条件: [Fact (IsCusp OnePoint.infty Γ)]
  证明: (zero_at_infty f).comp tendsto_comap_im_ofComplex

Depends on / 依赖: tendsto_comap_im_ofComplex, zero_at_infty
-/
theorem zero_at_infty_comp_ofComplex [Fact (IsCusp OnePoint.infty Γ)] :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  (zero_at_infty f).comp tendsto_comap_im_ofComplex

/--
theorem `cuspFunction_apply_zero` / 定理 `cuspFunction_apply_zero`

English:
theorem cuspFunction_apply_zero
  given: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  proof: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

中文:
定理 cuspFunction_apply_zero
  条件: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  证明: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

Depends on / 依赖: CuspFormClass, CuspFormClass.zero_at_infty, IsCusp, OnePoint, OnePoint.infty, cuspFunction_apply_zero, isCusp_of_mem_strictPeriods, zero_at_infty
-/
theorem cuspFunction_apply_zero (hh : 0 < h) (hΓ : h in Γ.strictPeriods) :
    cuspFunction h f 0 = 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

/--
theorem `qExpansion_coeff_zero` / 定理 `qExpansion_coeff_zero`

English:
theorem qExpansion_coeff_zero
  given: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  proof: by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

中文:
定理 qExpansion_coeff_zero
  条件: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  证明: by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

Depends on / 依赖: cuspFunction_apply_zero, qExpansion_coeff
-/
theorem qExpansion_coeff_zero (hh : 0 < h) (hΓ : h in Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = 0 := by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

/--
theorem `exp_decay_atImInfty` / 定理 `exp_decay_atImInfty`

English:
theorem exp_decay_atImInfty
  given: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  proof: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty (CuspFormClass.zero_at_infty f) hh
    (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

中文:
定理 exp_decay_atImInfty
  条件: (hh : 0 < h) (hΓ : h in Γ.strictPeriods)
  证明: have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty (CuspFormClass.zero_at_infty f) hh
    (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

Depends on / 依赖: CuspFormClass, CuspFormClass.zero_at_infty, IsCusp, IsZeroAtImInfty, OnePoint, OnePoint.infty, UpperHalfPlane, UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty, bdd_at_infty, exp_decay_atImInfty, isCusp_of_mem_strictPeriods, periodic_comp_ofComplex, zero_at_infty
-/
theorem exp_decay_atImInfty (hh : 0 < h) (hΓ : h in Γ.strictPeriods) :
    f =O[atImInfty] fun τ => Real.exp (-2 * π * τ.im / h) :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty (CuspFormClass.zero_at_infty f) hh
    (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

/--
theorem `exp_decay_atImInfty'` / 定理 `exp_decay_atImInfty'`

English:
theorem exp_decay_atImInfty'
  statement: [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
  proof: ModularFormClass.exp_decay_atImInfty' f (CuspFormClass.zero_at_infty f)

中文:
定理 exp_decay_atImInfty'
  结论: [Γ.有DetPlusMinusOne] [离散拓扑 Γ]
  证明: ModularFormClass.exp_decay_atImInfty' f (CuspFormClass.zero_at_infty f)

Depends on / 依赖: CuspFormClass, CuspFormClass.zero_at_infty, ModularFormClass, ModularFormClass.exp_decay_atImInfty, exp_decay_atImInfty, zero_at_infty
-/
theorem exp_decay_atImInfty' [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [Fact (IsCusp OnePoint.infty Γ)] :
    exists c > 0, f =O[atImInfty] fun τ => Real.exp (-c * τ.im) :=
  ModularFormClass.exp_decay_atImInfty' f (CuspFormClass.zero_at_infty f)

end CuspFormClass

section ring

namespace UpperHalfPlane

/--
theorem `cuspFunction_mul_zero` / 定理 `cuspFunction_mul_zero`

English:
theorem cuspFunction_mul_zero
  statement: {f g : Complex -> Complex} (hfcts : ContinuousAt (Periodic.cuspFunction h f) 0)
  proof: by
  rw [Periodic.cuspFunction]; rw [update_self]
.limUnder_eq exact (Periodic.tendsto_nhds_zero hfcts).mul (Periodic.tendsto_nhds_zero hgcts)

中文:
定理 cuspFunction_mul_zero
  结论: {f g : 复形 -> 复形} (hfcts : ContinuousAt (周期.cuspFunction h f) 0)
  证明: by
  rw [Periodic.cuspFunction]; rw [update_self]
.limUnder_eq exact (Periodic.tendsto_nhds_zero hfcts).mul (Periodic.tendsto_nhds_zero hgcts)

Depends on / 依赖: Periodic, Periodic.cuspFunction, Periodic.tendsto_nhds_zero, cuspFunction, limUnder_eq, tendsto_nhds_zero, update_self
-/
theorem cuspFunction_mul_zero {f g : Complex -> Complex} (hfcts : ContinuousAt (Periodic.cuspFunction h f) 0)
    (hgcts : ContinuousAt (Periodic.cuspFunction h g) 0) : Periodic.cuspFunction h (f * g) 0 =
    Periodic.cuspFunction h f 0 * Periodic.cuspFunction h g 0 := by
  rw [Periodic.cuspFunction]; rw [update_self]
.limUnder_eq exact (Periodic.tendsto_nhds_zero hfcts).mul (Periodic.tendsto_nhds_zero hgcts)

/--
lemma `qExpansion_mul_coeff_zero` / 引理 `qExpansion_mul_coeff_zero`

English:
lemma qExpansion_mul_coeff_zero
  statement: {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: by
  simpa [qExpansion_coeff] using! cuspFunction_mul_zero hfcts hgcts

中文:
引理 qExpansion_mul_coeff_zero
  结论: {f g : ℍ -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: by
  simpa [qExpansion_coeff] using! cuspFunction_mul_zero hfcts hgcts

Depends on / 依赖: cuspFunction_mul_zero, qExpansion_coeff
-/
lemma qExpansion_mul_coeff_zero {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    (qExpansion h (f * g)).coeff 0 = ((qExpansion h f).coeff 0) * (qExpansion h g).coeff 0 := by
  simpa [qExpansion_coeff] using! cuspFunction_mul_zero hfcts hgcts

/--
lemma `cuspFunction_mul` / 引理 `cuspFunction_mul`

English:
lemma cuspFunction_mul
  statement: {f g : ℍ -> Complex}
  proof: by
  ext z
  by_cases H : z = 0
  · simpa [H] using! cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]

中文:
引理 cuspFunction_mul
  结论: {f g : ℍ -> 复形}
  证明: by
  ext z
  by_cases H : z = 0
  · simpa [H] using! cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]

Depends on / 依赖: Periodic, Periodic.cuspFunction, cuspFunction, cuspFunction_mul_zero
-/
lemma cuspFunction_mul {f g : ℍ -> Complex}
    (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f * g) = cuspFunction h f * cuspFunction h g := by
  ext z
  by_cases H : z = 0
  · simpa [H] using! cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]

/--
lemma `cuspFunction_smul` / 引理 `cuspFunction_smul`

English:
lemma cuspFunction_smul
  given: {f : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex)
  proof: by
  apply Periodic.cuspFunction_smul hfcts

中文:
引理 cuspFunction_smul
  条件: {f : ℍ -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : 复形)
  证明: by
  apply Periodic.cuspFunction_smul hfcts

Depends on / 依赖: Periodic, Periodic.cuspFunction_smul, cuspFunction_smul
-/
lemma cuspFunction_smul {f : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  apply Periodic.cuspFunction_smul hfcts

/--
lemma `cuspFunction_neg` / 引理 `cuspFunction_neg`

English:
lemma cuspFunction_neg
  given: {f : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: Periodic.cuspFunction_neg hfcts

中文:
引理 cuspFunction_neg
  条件: {f : ℍ -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: Periodic.cuspFunction_neg hfcts

Depends on / 依赖: Periodic, Periodic.cuspFunction_neg, cuspFunction_neg
-/
lemma cuspFunction_neg {f : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = -cuspFunction h f :=
  Periodic.cuspFunction_neg hfcts

/--
lemma `cuspFunction_add` / 引理 `cuspFunction_add`

English:
lemma cuspFunction_add
  statement: {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: Periodic.cuspFunction_add hfcts hgcts

中文:
引理 cuspFunction_add
  结论: {f g : ℍ -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: Periodic.cuspFunction_add hfcts hgcts

Depends on / 依赖: Periodic, Periodic.cuspFunction_add, cuspFunction_add
-/
lemma cuspFunction_add {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g :=
  Periodic.cuspFunction_add hfcts hgcts

/--
lemma `cuspFunction_sub` / 引理 `cuspFunction_sub`

English:
lemma cuspFunction_sub
  statement: {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: Periodic.cuspFunction_sub hfcts hgcts

中文:
引理 cuspFunction_sub
  结论: {f g : ℍ -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: Periodic.cuspFunction_sub hfcts hgcts

Depends on / 依赖: Periodic, Periodic.cuspFunction_sub, cuspFunction_sub
-/
lemma cuspFunction_sub {f g : ℍ -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g :=
  Periodic.cuspFunction_sub hfcts hgcts

/--
lemma `qExpansion_mul` / 引理 `qExpansion_mul`

English:
lemma qExpansion_mul
  statement: {f g : ℍ -> Complex}
  proof: by
  ext
  simp only [qExpansion_coeff, cuspFunction_mul hf.continuousAt hg.continuousAt,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_


中文:
引理 qExpansion_mul
  结论: {f g : ℍ -> 复形}
  证明: by
  ext
  simp only [qExpansion_coeff, cuspFunction_mul hf.continuousAt hg.continuousAt,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_


Depends on / 依赖: Finset, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum, Finset.sum_congr, Nat.cast_choose, Nat.factorial_ne_zero, Nat.succ_eq_add_one, PowerSeries, PowerSeries.coeff_mul, cast_choose, coeff_mul, contDiffAt, continuousAt, cuspFunction_mul, factorial_ne_zero, hf.contDiffAt, hf.continuousAt, hg.contDiffAt, hg.continuousAt, iteratedDeriv_mul
-/
lemma qExpansion_mul {f g : ℍ -> Complex}
    (hf : AnalyticAt Complex (cuspFunction h f) 0) (hg : AnalyticAt Complex (cuspFunction h g) 0) :
    qExpansion h (f * g) = qExpansion h f * qExpansion h g := by
  ext
  simp only [qExpansion_coeff, cuspFunction_mul hf.continuousAt hg.continuousAt,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

/--
lemma `qExpansion_smul` / 引理 `qExpansion_smul`

English:
lemma qExpansion_smul
  given: {f : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0) (a : Complex)
  proof: by
  ext m
  simp [qExpansion_coeff, cuspFunction_smul hf.continuousAt, iteratedDeriv_const_smul_field,
    mul_left_comm]

中文:
引理 qExpansion_smul
  条件: {f : ℍ -> 复形} (hf : AnalyticAt 复形 (cuspFunction h f) 0) (a : 复形)
  证明: by
  ext m
  simp [qExpansion_coeff, cuspFunction_smul hf.continuousAt, iteratedDeriv_const_smul_field,
    mul_left_comm]

Depends on / 依赖: continuousAt, cuspFunction_smul, hf.continuousAt, iteratedDeriv_const_smul_field, mul_left_comm, qExpansion_coeff
-/
lemma qExpansion_smul {f : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0) (a : Complex) :
    qExpansion h (a • f) = a • qExpansion h f := by
  ext m
  simp [qExpansion_coeff, cuspFunction_smul hf.continuousAt, iteratedDeriv_const_smul_field,
    mul_left_comm]

/--
lemma `qExpansion_neg` / 引理 `qExpansion_neg`

English:
lemma qExpansion_neg
  given: {f : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0)
  proof: by
  simpa using qExpansion_smul hf (-1)

中文:
引理 qExpansion_neg
  条件: {f : ℍ -> 复形} (hf : AnalyticAt 复形 (cuspFunction h f) 0)
  证明: by
  simpa using qExpansion_smul hf (-1)

Depends on / 依赖: qExpansion_smul
-/
lemma qExpansion_neg {f : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0) :
    qExpansion h (-f) = -qExpansion h f := by
  simpa using qExpansion_smul hf (-1)

/--
lemma `qExpansion_add` / 引理 `qExpansion_add`

English:
lemma qExpansion_add
  statement: {f g : ℍ -> Complex}
  proof: by
  ext m
  simp [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

中文:
引理 qExpansion_add
  结论: {f g : ℍ -> 复形}
  证明: by
  ext m
  simp [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

Depends on / 依赖: contDiffAt, continuousAt, cuspFunction_add, hf.contDiffAt, hf.continuousAt, hg.contDiffAt, hg.continuousAt, iteratedDeriv_add, mul_add, qExpansion_coeff
-/
lemma qExpansion_add {f g : ℍ -> Complex}
    (hf : AnalyticAt Complex (cuspFunction h f) 0) (hg : AnalyticAt Complex (cuspFunction h g) 0) :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext m
  simp [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

/--
lemma `qExpansion_sub` / 引理 `qExpansion_sub`

English:
lemma qExpansion_sub
  statement: {f g : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0) (hg : AnalyticAt Complex
  proof: by
  have hg' : AnalyticAt Complex (cuspFunction h (-g)) 0 := by
    simpa [cuspFunction_neg hg.continuousAt] using hg.neg
  simpa [sub_eq_add_neg, qExpansion_neg hg] using (qExpansion_add hf hg')

中文:
引理 qExpansion_sub
  结论: {f g : ℍ -> 复形} (hf : AnalyticAt 复形 (cuspFunction h f) 0) (hg : AnalyticAt 复形
  证明: by
  have hg' : AnalyticAt Complex (cuspFunction h (-g)) 0 := by
    simpa [cuspFunction_neg hg.continuousAt] using hg.neg
  simpa [sub_eq_add_neg, qExpansion_neg hg] using (qExpansion_add hf hg')

Depends on / 依赖: AnalyticAt, continuousAt, cuspFunction, cuspFunction_neg, hg.continuousAt, hg.neg, qExpansion_add, qExpansion_neg, sub_eq_add_neg
-/
lemma qExpansion_sub {f g : ℍ -> Complex} (hf : AnalyticAt Complex (cuspFunction h f) 0) (hg : AnalyticAt Complex
    (cuspFunction h g) 0) : qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  have hg' : AnalyticAt Complex (cuspFunction h (-g)) 0 := by
    simpa [cuspFunction_neg hg.continuousAt] using hg.neg
  simpa [sub_eq_add_neg, qExpansion_neg hg] using (qExpansion_add hf hg')

/--
lemma `qExpansion_zero` / 引理 `qExpansion_zero`

English:
lemma qExpansion_zero
  given: (h)
  statement: qExpansion h 0 = 0
  proof: by
  suffices cuspFunction h 0 = 0 by ext; simp [qExpansion_coeff, this]
  simpa [cuspFunction, Periodic.cuspFunction]
    using! (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq

中文:
引理 qExpansion_zero
  条件: (h)
  结论: qExpansion h 0 = 0
  证明: by
  suffices cuspFunction h 0 = 0 by ext; simp [qExpansion_coeff, this]
  simpa [cuspFunction, Periodic.cuspFunction]
    using! (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq

Depends on / 依赖: Periodic, Periodic.cuspFunction, cuspFunction, limUnder_eq, mono_left, nhdsWithin_le_nhds, qExpansion_coeff, tendsto_const_nhds, tendsto_const_nhds.mono_left
-/
lemma qExpansion_zero (h) : qExpansion h 0 = 0 := by
  suffices cuspFunction h 0 = 0 by ext; simp [qExpansion_coeff, this]
  simpa [cuspFunction, Periodic.cuspFunction]
    using! (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq

/--
lemma `qExpansion_eq_zero_iff` / 引理 `qExpansion_eq_zero_iff`

English:
lemma qExpansion_eq_zero_iff
  statement: {f : ℍ -> Complex} (hh : 0 < h)
  proof: by
  constructor
  · intro H
    ext z
    simp [← (hasSum_qExpansion hh hfper hfhol hfbdd z).tsum_eq, H]
  · intro H
    simpa [H] using qExpansion_zero h

中文:
引理 qExpansion_eq_zero_iff
  结论: {f : ℍ -> 复形} (hh : 0 < h)
  证明: by
  constructor
  · intro H
    ext z
    simp [← (hasSum_qExpansion hh hfper hfhol hfbdd z).tsum_eq, H]
  · intro H
    simpa [H] using qExpansion_zero h

Depends on / 依赖: hasSum_qExpansion, qExpansion_zero, tsum_eq
-/
lemma qExpansion_eq_zero_iff {f : ℍ -> Complex} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    qExpansion h f = 0 ↔ f = 0 := by
  constructor
  · intro H
    ext z
    simp [← (hasSum_qExpansion hh hfper hfhol hfbdd z).tsum_eq, H]
  · intro H
    simpa [H] using qExpansion_zero h

/--
lemma `qExpansion_one` / 引理 `qExpansion_one`

English:
lemma qExpansion_one
  given: (h)
  statement: qExpansion h (1 : ℍ -> Complex) = 1
  proof: by
  ext m
  have h1 : cuspFunction h 1 = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [cuspFunction, Periodic.cuspFunction] using! tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have h2 : iteratedDeriv m (1 : Complex -> 

中文:
引理 qExpansion_one
  条件: (h)
  结论: qExpansion h (1 : ℍ -> 复形) = 1
  证明: by
  ext m
  have h1 : cuspFunction h 1 = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [cuspFunction, Periodic.cuspFunction] using! tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have h2 : iteratedDeriv m (1 : Complex -> 

Depends on / 依赖: Periodic, Periodic.cuspFunction, Periodic.cuspFunction_eq_of_nonzero, contextual, cuspFunction, cuspFunction_eq_of_nonzero, eq_or_ne, ite_apply, iteratedDeriv, iteratedDeriv_const, limUnder_eq, qExpansion_coeff, tendsto_const_nhds, tendsto_const_nhds.limUnder_eq
-/
lemma qExpansion_one (h) : qExpansion h (1 : ℍ -> Complex) = 1 := by
  ext m
  have h1 : cuspFunction h 1 = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [cuspFunction, Periodic.cuspFunction] using! tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have h2 : iteratedDeriv m (1 : Complex -> Complex) 0 = if m = 0 then 1 else 0 := by
    simpa [ite_apply] using! iteratedDeriv_const
  simp +contextual [qExpansion_coeff, h1, h2]

end UpperHalfPlane

namespace ModularForm

/--
lemma `cuspFunction_smul` / 引理 `cuspFunction_smul`

English:
lemma cuspFunction_smul
  statement: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : Complex)
  proof: cuspFunction_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt a

中文:
引理 cuspFunction_smul
  结论: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : 复形)
  证明: cuspFunction_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt a
-/
protected lemma cuspFunction_smul (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : Complex)
    (f : F) [ModularFormClass F Γ k] : cuspFunction h (a • f) = a • cuspFunction h f :=
  cuspFunction_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt a

/--
lemma `cuspFunction_neg` / 引理 `cuspFunction_neg`

English:
lemma cuspFunction_neg
  statement: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
  proof: cuspFunction_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt

中文:
引理 cuspFunction_neg
  结论: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
  证明: cuspFunction_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
-/
protected lemma cuspFunction_neg (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
    [ModularFormClass F Γ k] : cuspFunction h (-f) = -cuspFunction h f :=
  cuspFunction_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt

/--
lemma `cuspFunction_add` / 引理 `cuspFunction_add`

English:
lemma cuspFunction_add
  statement: {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
  proof: cuspFunction_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

中文:
引理 cuspFunction_add
  结论: {G : 类型} [函数状 G ℍ 复形] (hh : 0 < h)
  证明: cuspFunction_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
-/
protected lemma cuspFunction_add {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g :=
  cuspFunction_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

/--
lemma `cuspFunction_sub` / 引理 `cuspFunction_sub`

English:
lemma cuspFunction_sub
  statement: {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
  proof: cuspFunction_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

中文:
引理 cuspFunction_sub
  结论: {G : 类型} [函数状 G ℍ 复形] (hh : 0 < h)
  证明: cuspFunction_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
-/
protected lemma cuspFunction_sub {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g :=
  cuspFunction_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

/--
lemma `cuspFunction_mul` / 引理 `cuspFunction_mul`

English:
lemma cuspFunction_mul
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: cuspFunction_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

中文:
引理 cuspFunction_mul
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: cuspFunction_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
-/
protected lemma cuspFunction_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    cuspFunction h (f.mul g) = cuspFunction h f * cuspFunction h g :=
  cuspFunction_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt

/--
lemma `qExpansion_smul` / 引理 `qExpansion_smul`

English:
lemma qExpansion_smul
  statement: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : Complex)
  proof: qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) a

中文:
引理 qExpansion_smul
  结论: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : 复形)
  证明: qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) a
-/
protected lemma qExpansion_smul (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (a : Complex)
    (f : F) [ModularFormClass F Γ k] : qExpansion h (a • f) = a • qExpansion h f :=
  qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) a

/--
lemma `qExpansion_neg` / 引理 `qExpansion_neg`

English:
lemma qExpansion_neg
  statement: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
  proof: qExpansion_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)

中文:
引理 qExpansion_neg
  结论: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
  证明: qExpansion_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
-/
protected lemma qExpansion_neg (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (f : F)
    [ModularFormClass F Γ k] : qExpansion h (-f) = -qExpansion h f :=
  qExpansion_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)

/--
lemma `qExpansion_add` / 引理 `qExpansion_add`

English:
lemma qExpansion_add
  statement: {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
  proof: qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

中文:
引理 qExpansion_add
  结论: {G : 类型} [函数状 G ℍ 复形] (hh : 0 < h)
  证明: qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)
-/
protected lemma qExpansion_add {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h (f + g) = qExpansion h f + qExpansion h g :=
    qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

/--
lemma `qExpansion_sub` / 引理 `qExpansion_sub`

English:
lemma qExpansion_sub
  statement: {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
  proof: qExpansion_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

中文:
引理 qExpansion_sub
  结论: {G : 类型} [函数状 G ℍ 复形] (hh : 0 < h)
  证明: qExpansion_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)
-/
protected lemma qExpansion_sub {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h (f - g) = qExpansion h f - qExpansion h g :=
  qExpansion_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

/--
lemma `qExpansion_mul_coe` / 引理 `qExpansion_mul_coe`

English:
lemma qExpansion_mul_coe
  statement: {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
  proof: qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

中文:
引理 qExpansion_mul_coe
  结论: {G : 类型} [函数状 G ℍ 复形] (hh : 0 < h)
  证明: qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)
-/
protected lemma qExpansion_mul_coe {G : Type*} [FunLike G ℍ Complex] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h ((⇑f * ⇑g : ℍ -> Complex)) = qExpansion h f * qExpansion h g :=
  qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

/--
lemma `qExpansion_mul` / 引理 `qExpansion_mul`

English:
lemma qExpansion_mul
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: ModularForm.qExpansion_mul_coe hh hΓ f g

中文:
引理 qExpansion_mul
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: ModularForm.qExpansion_mul_coe hh hΓ f g
-/
protected lemma qExpansion_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {a b : Int} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h (f.mul g) = qExpansion h f * qExpansion h g :=
  ModularForm.qExpansion_mul_coe hh hΓ f g

/--
lemma `qExpansion_eq_zero_iff` / 引理 `qExpansion_eq_zero_iff`

English:
lemma qExpansion_eq_zero_iff
  statement: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) {k : Int}
  proof: by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  simp [qExpansion_eq_zero_iff hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)]

中文:
引理 qExpansion_eq_zero_iff
  结论: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) {k : 整数}
  证明: by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  simp [qExpansion_eq_zero_iff hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)]
-/
protected lemma qExpansion_eq_zero_iff (hh : 0 < h) (hΓ : h in Γ.strictPeriods) {k : Int}
    (f : ModularForm Γ k) : qExpansion h f = 0 ↔ f = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  simp [qExpansion_eq_zero_iff hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)]

/--
lemma `qExpansion_one` / 引理 `qExpansion_one`

English:
lemma qExpansion_one
  given: [Γ.HasDetPlusMinusOne]
  proof: by
  simp [qExpansion_one]

@[simp]

中文:
引理 qExpansion_one
  条件: [Γ.有DetPlusMinusOne]
  证明: by
  simp [qExpansion_one]

@[simp]
-/
protected lemma qExpansion_one [Γ.HasDetPlusMinusOne] :
    qExpansion h (1 : ModularForm Γ 0) = 1 := by
  simp [qExpansion_one]

@[simp]
/--
lemma `qExpansion_mcast` / 引理 `qExpansion_mcast`

English:
lemma qExpansion_mcast
  statement: {a b : Int} {Γ' : Subgroup (GL (Fin 2) Real)}
  proof: rfl

中文:
引理 qExpansion_mcast
  结论: {a b : 整数} {Γ' : 子群 (GL (有限集 2) 实数)}
  证明: rfl
-/
protected lemma qExpansion_mcast {a b : Int} {Γ' : Subgroup (GL (Fin 2) Real)}
    (heq : a = b) (hΓ : Γ' = Γ) (f : ModularForm Γ a) :
    qExpansion h (ModularForm.mcast heq f hΓ) = qExpansion h f := rfl

/--
lemma `qExpansion_pow` / 引理 `qExpansion_pow`

English:
lemma qExpansion_pow
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: by
  induction n with
  | zero => simp only [coe_pow, pow_zero, qExpansion_one]
  | succ n ih =>
    rw [coe_pow]; rw [pow_succ]; rw [← coe_pow]; rw [← coe_mul]; rw [ModularForm.qExpansion_mul hh hΓ]; rw [ih]; rw [pow_succ]

中文:
引理 qExpansion_pow
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: by
  induction n with
  | zero => simp only [coe_pow, pow_zero, qExpansion_one]
  | succ n ih =>
    rw [coe_pow]; rw [pow_succ]; rw [← coe_pow]; rw [← coe_mul]; rw [ModularForm.qExpansion_mul hh hΓ]; rw [ih]; rw [pow_succ]
-/
protected lemma qExpansion_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) (f : ModularForm Γ k) (n : Nat) :
    qExpansion h (f.pow n) = (qExpansion h f) ^ n := by
  induction n with
  | zero => simp only [coe_pow, pow_zero, qExpansion_one]
  | succ n ih =>
    rw [coe_pow]; rw [pow_succ]; rw [← coe_pow]; rw [← coe_mul]; rw [ModularForm.qExpansion_mul hh hΓ]; rw [ih]; rw [pow_succ]

/--
lemma `mul_ne_zero` / 引理 `mul_ne_zero`

English:
lemma mul_ne_zero
  statement: [Γ.HasDetPlusMinusOne] (hΓ : exists h in Γ.strictPeriods, 0 < h)
  proof: by
  obtain ⟨h, hΓ, hh⟩ := hΓ
  simp only [ne_eq, ← ModularForm.qExpansion_eq_zero_iff hh hΓ,
    ModularForm.qExpansion_mul hh hΓ] at hf hg ⊢
  exact mul_ne_zero hf hg

中文:
引理 mul_ne_zero
  结论: [Γ.有DetPlusMinusOne] (hΓ : 存在 h in Γ.strictPeriods, 0 < h)
  证明: by
  obtain ⟨h, hΓ, hh⟩ := hΓ
  simp only [ne_eq, ← ModularForm.qExpansion_eq_zero_iff hh hΓ,
    ModularForm.qExpansion_mul hh hΓ] at hf hg ⊢
  exact mul_ne_zero hf hg
-/
protected lemma mul_ne_zero [Γ.HasDetPlusMinusOne] (hΓ : exists h in Γ.strictPeriods, 0 < h)
    {a b : Int} {f : ModularForm Γ a} {g : ModularForm Γ b} (hf : f != 0) (hg : g != 0) :
    f.mul g != 0 := by
  obtain ⟨h, hΓ, hh⟩ := hΓ
  simp only [ne_eq, ← ModularForm.qExpansion_eq_zero_iff hh hΓ,
    ModularForm.qExpansion_mul hh hΓ] at hf hg ⊢
  exact mul_ne_zero hf hg

/--
Definition of `qExpansionAddHom` / `qExpansionAddHom` 的定义

English:
definition qExpansionAddHom
  signature: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (k : Int)
  body: qExpansion h f
  map_zero' := qExpansion_zero h
  map_add' f g := ModularForm.qExpansion_add hh hΓ f g

中文:
定义 qExpansionAddHom
  签名: (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (k : 整数)
  定义体: qExpansion h f
  map_zero' := qExpansion_zero h
  map_add' f g := ModularForm.qExpansion_add hh hΓ f g

Depends on / 依赖: qExpansion
-/
def qExpansionAddHom (hh : 0 < h) (hΓ : h in Γ.strictPeriods) (k : Int) :
    ModularForm Γ k ->+ PowerSeries Complex where
  toFun f := qExpansion h f
  map_zero' := qExpansion_zero h
  map_add' f g := ModularForm.qExpansion_add hh hΓ f g

open scoped DirectSum in
/--
Definition of `qExpansionRingHom` / `qExpansionRingHom` 的定义

English:
definition qExpansionRingHom
  signature: (h) [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  body: DirectSum.toSemiring (qExpansionAddHom hh hΓ) ModularForm.qExpansion_one
    (ModularForm.qExpansion_mul hh hΓ)

@[simp]

中文:
定义 qExpansionRingHom
  签名: (h) [Γ.有DetPlusMinusOne] (hh : 0 < h)
  定义体: DirectSum.toSemiring (qExpansionAddHom hh hΓ) ModularForm.qExpansion_one
    (ModularForm.qExpansion_mul hh hΓ)

@[simp]

Depends on / 依赖: DirectSum, DirectSum.toSemiring, ModularForm, ModularForm.qExpansion_mul, ModularForm.qExpansion_one, qExpansionAddHom, qExpansion_mul, qExpansion_one, toSemiring
-/
def qExpansionRingHom (h) [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) : (⨁ k, ModularForm Γ k) ->+* PowerSeries Complex :=
  DirectSum.toSemiring (qExpansionAddHom hh hΓ) ModularForm.qExpansion_one
    (ModularForm.qExpansion_mul hh hΓ)

@[simp]
/--
lemma `qExpansionRingHom_apply` / 引理 `qExpansionRingHom_apply`

English:
lemma qExpansionRingHom_apply
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: DirectSum.toSemiring_of ..

中文:
引理 qExpansionRingHom_apply
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: DirectSum.toSemiring_of ..

Depends on / 依赖: DirectSum, DirectSum.toSemiring_of, toSemiring_of
-/
lemma qExpansionRingHom_apply [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) (k : Int) (f : ModularForm Γ k) :
    qExpansionRingHom h hh hΓ (DirectSum.of _ k f) = qExpansion h f :=
  DirectSum.toSemiring_of ..

/--
lemma `qExpansion_of_mul` / 引理 `qExpansion_of_mul`

English:
lemma qExpansion_of_mul
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: by
  simpa [DirectSum.of_mul_of] using! ModularForm.qExpansion_mul hh hΓ f g

中文:
引理 qExpansion_of_mul
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: by
  simpa [DirectSum.of_mul_of] using! ModularForm.qExpansion_mul hh hΓ f g

Depends on / 依赖: DirectSum, DirectSum.of_mul_of, ModularForm, ModularForm.qExpansion_mul, of_mul_of, qExpansion_mul
-/
lemma qExpansion_of_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) (a b : Int) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h ((DirectSum.of _ a f * DirectSum.of _ b g) (a + b)) =
    qExpansion h f * qExpansion h g := by
  simpa [DirectSum.of_mul_of] using! ModularForm.qExpansion_mul hh hΓ f g

/--
lemma `qExpansion_of_pow` / 引理 `qExpansion_of_pow`

English:
lemma qExpansion_of_pow
  statement: [Γ.HasDetPlusMinusOne] (hh : 0 < h)
  proof: by
  have := (qExpansionRingHom h hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [DirectSum.ofPow]

中文:
引理 qExpansion_of_pow
  结论: [Γ.有DetPlusMinusOne] (hh : 0 < h)
  证明: by
  have := (qExpansionRingHom h hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [DirectSum.ofPow]

Depends on / 依赖: DirectSum, DirectSum.of, DirectSum.ofPow, map_pow, qExpansionRingHom
-/
lemma qExpansion_of_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) (f : ModularForm Γ k) (n : Nat) :
    qExpansion h ((((DirectSum.of _ k f)) ^ n) (n * k)) = (qExpansion h f) ^ n := by
  have := (qExpansionRingHom h hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [DirectSum.ofPow]

/--
lemma `hasSum_qExpansion` / 引理 `hasSum_qExpansion`

English:
lemma hasSum_qExpansion
  statement: (hh : 0 < h) {k : Int} [ModularFormClass F Γ k]
  proof: τ.hasSum_qExpansion hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

中文:
引理 hasSum_qExpansion
  结论: (hh : 0 < h) {k : 整数} [模形式类 F Γ k]
  证明: τ.hasSum_qExpansion hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

Depends on / 依赖: bdd_at_infty, hasSum_qExpansion, periodic_comp_ofComplex
-/
lemma hasSum_qExpansion (hh : 0 < h) {k : Int} [ModularFormClass F Γ k]
    [Fact (IsCusp .infty Γ)] (hΓ : h in Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m => (qExpansion h f).coeff m * 𝕢 h τ ^ m) (f τ) :=
  τ.hasSum_qExpansion hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

end ModularForm

namespace ModularFormClass

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_smul := ModularForm.cuspFunction_smul

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_neg := ModularForm.cuspFunction_neg

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_add := ModularForm.cuspFunction_add

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_sub := ModularForm.cuspFunction_sub

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_smul := ModularForm.qExpansion_smul

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_neg := ModularForm.qExpansion_neg

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_add := ModularForm.qExpansion_add

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_sub := ModularForm.qExpansion_sub

end ModularFormClass

end ring

section uniqueness

namespace UpperHalfPlane

/--
lemma `hasFPowerSeries_cuspFunction` / 引理 `hasFPowerSeries_cuspFunction`

English:
lemma hasFPowerSeries_cuspFunction
  statement: {c : Nat -> Complex} (hh : 0 < h)
  proof: by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.ha

中文:
引理 hasFPowerSeries_cuspFunction
  结论: {c : 自然数 -> 复形} (hh : 0 < h)
  证明: by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.ha

Depends on / 依赖: HasFPowerSeriesAt, cuspFunction, div_eq_mul_inv, eq_formalMultilinearSeries, h1.eq_formalMultilinearSeries, hasFPowerSeriesAt, hasFPowerSeriesOnBall_cuspFunction, hfanalytic, hfanalytic.hasFPowerSeriesAt, mul_comm, qExpansionFormalMultilinearSeries, qExpansion_coeff
-/
lemma hasFPowerSeries_cuspFunction {c : Nat -> Complex} (hh : 0 < h)
    (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0)
    (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.hasFPowerSeriesAt
  simpa [h1.eq_formalMultilinearSeries h2] using hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf

/--
lemma `qExpansion_coeff_unique` / 引理 `qExpansion_coeff_unique`

English:
lemma qExpansion_coeff_unique
  statement: {c : Nat -> Complex} (hh : 0 < h)
  proof: by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 := (hasFPowerSeries_cuspFunction f hh hfanalytic hf).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

中文:
引理 qExpansion_coeff_unique
  结论: {c : 自然数 -> 复形} (hh : 0 < h)
  证明: by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 := (hasFPowerSeries_cuspFunction f hh hfanalytic hf).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.coeff, congr_arg, eq_formalMultilinearSeries, h1.eq_formalMultilinearSeries, hasFPowerSeriesAt, hasFPowerSeriesOnBall_cuspFunction, hasFPowerSeries_cuspFunction, hfanalytic
-/
lemma qExpansion_coeff_unique {c : Nat -> Complex} (hh : 0 < h)
    (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0)
    (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) (m : Nat) :
    c m = (qExpansion h f).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 := (hasFPowerSeries_cuspFunction f hh hfanalytic hf).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

end UpperHalfPlane

/--
lemma `ModularFormClass.qExpansion_coeff_unique` / 引理 `ModularFormClass.qExpansion_coeff_unique`

English:
lemma ModularFormClass.qExpansion_coeff_unique
  statement: {c : Nat -> Complex} (hh : 0 < h)
  proof: qExpansion_coeff_unique f hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) hf m

中文:
引理 模形式类.qExpansion_coeff_unique
  结论: {c : 自然数 -> 复形} (hh : 0 < h)
  证明: qExpansion_coeff_unique f hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) hf m
-/
protected lemma ModularFormClass.qExpansion_coeff_unique {c : Nat -> Complex} (hh : 0 < h)
    (hΓ : h in Γ.strictPeriods) {f : F} [ModularFormClass F Γ k]
    (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) (m : Nat) :
    c m = (qExpansion h f).coeff m :=
  qExpansion_coeff_unique f hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) hf m
