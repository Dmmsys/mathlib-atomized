/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

In namespace `VectorFourier`, we define the Fourier integral in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is a unitary additive character of `𝕜`, i.e. an `AddChar 𝕜 Circle`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, we define `fourierIntegral` to be the map from functions `V → E` to
functions `W → E` that sends `f` to

`fun w ↦ ∫ v in V, e (-L v w) • f v ∂μ`,

This includes the cases `W` is the dual of `V` and `L` is the canonical pairing, or `W = V` and `L`
is a bilinear form (e.g. an inner product).

In namespace `Fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `Real.fourierChar`, i.e. the character `fun x ↦ exp ((2 * π * x) * I)` (for which we
introduced the notation `𝐞` in the scope `FourierTransform`).

Another familiar case (which generalizes the previous one) is when `V = W` is an inner product space
over `ℝ` and `L` is the scalar product. We introduce two notations `𝓕` for the Fourier transform in
this case and `𝓕⁻ f (v) = 𝓕 f (-v)` for the inverse Fourier transform. These notations make
in particular sense for `V = W = ℝ`.

## Main results

At present the only nontrivial lemma we prove is `fourierIntegral_continuous`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/

@[expose] public section


noncomputable section

local notation "𝕊" => Circle

open MeasureTheory Filter

open scoped Topology

/-! ## Fourier theory for functions on general vector spaces -/

namespace VectorFourier

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [NormedAddCommGroup F] [NormedSpace Complex F]
  [NormedAddCommGroup G] [NormedSpace Complex G]

section Defs

/--
Definition of `fourierIntegral` / `fourierIntegral` 的定义

English:
definition fourierIntegral
  signature: (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E)
  body: ∫ v, e (-L v w) • f v ∂μ

中文:
定义 fourierIntegral
  签名: (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E)
  定义体: ∫ v, e (-L v w) • f v ∂μ
-/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E)
    (w : W) : E :=
  ∫ v, e (-L v w) • f v ∂μ

/--
theorem `fourierIntegral_congr_ae` / 定理 `fourierIntegral_congr_ae`

English:
theorem fourierIntegral_congr_ae
  statement: (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜)
  proof: by
  ext
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

中文:
定理 fourierIntegral_congr_ae
  结论: (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜)
  证明: by
  ext
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
theorem fourierIntegral_congr_ae (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜)
    {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[μ] f₂) : fourierIntegral e μ L f₁ = fourierIntegral e μ L f₂ := by
  ext
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

/--
theorem `fourierIntegral_const_smul` / 定理 `fourierIntegral_const_smul`

English:
theorem fourierIntegral_const_smul
  statement: (e : AddChar 𝕜 𝕊) (μ : Measure V)
  proof: by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

中文:
定理 fourierIntegral_const_smul
  结论: (e : AddChar 𝕜 𝕊) (μ : Measure V)
  证明: by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

Depends on / 依赖: Pi.smul_apply, fourierIntegral, integral_smul, smul_apply, smul_comm
-/
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (r : Complex) :
    fourierIntegral e μ L (r • f) = r • fourierIntegral e μ L f := by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

/--
theorem `norm_fourierIntegral_le_integral_norm` / 定理 `norm_fourierIntegral_le_integral_norm`

English:
theorem norm_fourierIntegral_le_integral_norm
  statement: (e : AddChar 𝕜 𝕊) (μ : Measure V)
  proof: by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

中文:
定理 norm_fourierIntegral_le_integral_norm
  结论: (e : AddChar 𝕜 𝕊) (μ : Measure V)
  证明: by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

Depends on / 依赖: Circle, Circle.norm_smul, le_of_eq, norm_integral_le_integral_norm, norm_smul, simp_rw
-/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (w : W) :
    ‖fourierIntegral e μ L f w‖ <= ∫ v : V, ‖f v‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

/--
theorem `fourierIntegral_comp_add_right` / 定理 `fourierIntegral_comp_add_right`

English:
theorem fourierIntegral_comp_add_right
  statement: [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
  proof: by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V => (e (-L (v - v₀) w) : Complex) • f v]; rw [← integral_smul]
  congr 1 with v
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← Ci

中文:
定理 fourierIntegral_comp_add_right
  结论: [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
  证明: by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V => (e (-L (v - v₀) w) : Complex) • f v]; rw [← integral_smul]
  congr 1 with v
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← Ci

Depends on / 依赖: Circle, Circle.coe_mul, Circle.smul_def, Function, Function.comp_apply, LinearMap, LinearMap.neg_apply, LinearMap.sub_apply, add_sub_cancel_right, coe_mul, comp_apply, e.map_add_eq_mul, fourierIntegral, integral_add_right_eq_self, integral_smul, map_add_eq_mul, map_sub, neg_apply, neg_sub, smul_assoc
-/
theorem fourierIntegral_comp_add_right [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
    [μ.IsAddRightInvariant] (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (v₀ : V) :
    fourierIntegral e μ L (f ∘ fun v => v + v₀) =
      fun w => e (L v₀ w) • fourierIntegral e μ L f w := by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V => (e (-L (v - v₀) w) : Complex) • f v]; rw [← integral_smul]
  congr 1 with v
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← Circle.coe_mul]; rw [← e.map_add_eq_mul]; rw [← LinearMap.neg_apply]; rw [← sub_eq_add_neg]; rw [← LinearMap.sub_apply]; rw [map_sub]; rw [neg_sub]

end Defs

section Continuous

/-!
In this section we assume 𝕜, `V`, `W` have topologies,
and `L`, `e` are continuous (but `f` needn't be).

This is used to ensure that `e (-L v w)` is (a.e. strongly) measurable. We could get away with
imposing only a measurable-space structure on 𝕜 (it doesn't have to be the Borel sigma-algebra of
a topology); but it seems hard to imagine cases where this extra generality would be useful, and
allowing it would complicate matters in the most important use cases.
-/
variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜}

/--
theorem `fourierIntegral_convergent_iff` / 定理 `fourierIntegral_convergent_iff`

English:
theorem fourierIntegral_convergent_iff
  statement: (he : Continuous e)
  proof: by
  -- first prove one-way implication
  have aux {g : V -> E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V => e (-L v x) • g v) μ := by
    have c : Continuous fun v => e (-L v x) := he.comp (hL.comp (.prodMk_left _)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.fu

中文:
定理 fourierIntegral_convergent_iff
  结论: (he : Continuous e)
  证明: by
  -- first prove one-way implication
  have aux {g : V -> E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V => e (-L v x) • g v) μ := by
    have c : Continuous fun v => e (-L v x) := he.comp (hL.comp (.prodMk_left _)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.fu
-/
theorem fourierIntegral_convergent_iff (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> E} (w : W) :
    Integrable (fun v : V => e (-L v w) • f v) μ ↔ Integrable f μ := by
  -- first prove one-way implication
  have aux {g : V -> E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V => e (-L v x) • g v) μ := by
    have c : Continuous fun v => e (-L v x) := he.comp (hL.comp (.prodMk_left _)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.fun_smul hg.1), Circle.norm_smul]
    exact hg.norm
  -- then use it for both directions
  refine ⟨fun hf => ?_, fun hf => aux hf w⟩
  have := aux hf (-w)
  simp_rw [← mul_smul (e _) (e _) (f _), ← e.map_add_eq_mul, map_neg, neg_add_cancel,
    e.map_zero_eq_one, one_smul] at this -- the `(e _)` speeds up elaboration considerably
  exact this

/--
theorem `fourierIntegral_add` / 定理 `fourierIntegral_add`

English:
theorem fourierIntegral_add
  statement: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  proof: by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg

中文:
定理 fourierIntegral_add
  结论: (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
  证明: by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg

Depends on / 依赖: Pi.add_apply, add_apply, fourierIntegral, fourierIntegral_convergent_iff, integral_add, simp_rw, smul_add
-/
theorem fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
    {f g : V -> E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral e μ L (f + g) = fourierIntegral e μ L f + fourierIntegral e μ L g := by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg

/--
theorem `fourierIntegral_continuous` / 定理 `fourierIntegral_continuous`

English:
theorem fourierIntegral_continuous
  statement: [FirstCountableTopology W] (he : Continuous e)
  proof: by
  apply continuous_of_dominated
  · exact fun w => ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w => ae_of_all _ fun v => le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · filter_upwards with v
    fun_prop

中文:
定理 fourierIntegral_continuous
  结论: [FirstCountableTopology W] (he : Continuous e)
  证明: by
  apply continuous_of_dominated
  · exact fun w => ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w => ae_of_all _ fun v => le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · filter_upwards with v
    fun_prop

Depends on / 依赖: Circle, Circle.norm_smul, ae_of_all, continuous_of_dominated, filter_upwards, fourierIntegral_convergent_iff, fun_prop, hf.norm, le_of_eq, norm_smul
-/
theorem fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w => ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w => ae_of_all _ fun v => le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · filter_upwards with v
    fun_prop

end Continuous

section Fubini

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜}
  {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν] [SecondCountableTopologyEither W V]

variable {σ : Complex ->+* Complex} [RingHomIsometric σ]

/--
theorem `integral_fourierIntegral_swap` / 定理 `integral_fourierIntegral_swap`

English:
theorem integral_fourierIntegral_swap
  proof: by
  rw [integral_integral_swap]
  have : Integrable (fun (p : W × V) => ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
    (hg.norm.mul_prod hf.norm).const_mul _
  apply this.mono
  · change AEStronglyMeasurable (fun p : W × V => (M (g p.1) (e (-(L p.2) p.1) • f p.2))) _
    have A : AEStronglyMeasurable

中文:
定理 integral_fourierIntegral_swap
  证明: by
  rw [integral_integral_swap]
  have : Integrable (fun (p : W × V) => ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
    (hg.norm.mul_prod hf.norm).const_mul _
  apply this.mono
  · change AEStronglyMeasurable (fun p : W × V => (M (g p.1) (e (-(L p.2) p.1) • f p.2))) _
    have A : AEStronglyMeasurable

Depends on / 依赖: AEStronglyMeasurable, Continuous, Continuous.aestronglyMeasurable, Integrable, aestronglyMeasurable, comp_snd, const_mul, continuous_swap, fun_smul, hL.comp, he.comp, hf.norm, hg.norm.mul_prod, integral_integral_swap, mul_prod, this.mono
-/
theorem integral_fourierIntegral_swap
    {f : V -> E} {g : W -> F} (M : F ->L[Complex] E ->SL[σ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (∫ x, M (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν =
    ∫ x, (∫ ξ, M (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ := by
  rw [integral_integral_swap]
  have : Integrable (fun (p : W × V) => ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
    (hg.norm.mul_prod hf.norm).const_mul _
  apply this.mono
  · change AEStronglyMeasurable (fun p : W × V => (M (g p.1) (e (-(L p.2) p.1) • f p.2))) _
    have A : AEStronglyMeasurable (fun (p : W × V) => e (-L p.2 p.1) • f p.2) (ν.prod μ) := by
      refine (Continuous.aestronglyMeasurable ?_).fun_smul hf.1.comp_snd
      exact he.comp (hL.comp continuous_swap).neg
    have A' : AEStronglyMeasurable (fun p => (g p.1, e (-(L p.2) p.1) • f p.2) : W × V -> F × E)
      (Measure.prod ν μ) := hg.1.comp_fst.prodMk A
    have hM : Continuous (fun q => M q.1 q.2 : F × E -> G) :=
      -- There is no `Continuous.clm_apply` for semilinear continuous maps
      (M.flip.cont.comp continuous_snd).clm_apply continuous_fst
    apply hM.comp_aestronglyMeasurable A' -- `exact` works, but `apply` is 10x faster!
  · filter_upwards with ⟨ξ, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul, norm_norm, ge_iff_le, ← mul_assoc]
    convert! M.le_opNorm₂ (g ξ) (e (-L x ξ) • f x) using 2
    simp

variable [CompleteSpace E] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `integral_bilin_fourierIntegral_eq_flip` / 定理 `integral_bilin_fourierIntegral_eq_flip`

English:
theorem integral_bilin_fourierIntegral_eq_flip
  proof: by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_if

中文:
定理 integral_bilin_fourierIntegral_eq_flip
  证明: by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_if

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.flip_appl, ContinuousLinearMap.integral_comp_comm, L.flip, M.flip, flip_appl, fourierIntegral_convergent_iff, integral, integral_comp_comm, integral_fourierIntegral_swap
-/
theorem integral_bilin_fourierIntegral_eq_flip
    {f : V -> E} {g : W -> F} (M : E ->L[Complex] F ->L[Complex] G) (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (-L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower,
      smul_apply, LinearMap.flip_apply]
  _ = ∫ x, M (f x) (∫ ξ, e (-L.flip ξ x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    apply (fourierIntegral_convergent_iff he _ _).2 hg
    exact hL.comp continuous_swap

/--
theorem `integral_fourierIntegral_smul_eq_flip` / 定理 `integral_fourierIntegral_smul_eq_flip`

English:
theorem integral_fourierIntegral_smul_eq_flip
  proof: integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul Complex Complex) he hL hf hg

中文:
定理 integral_fourierIntegral_smul_eq_flip
  证明: integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul Complex Complex) he hL hf hg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, integral_bilin_fourierIntegral_eq_flip
-/
theorem integral_fourierIntegral_smul_eq_flip
    {f : V -> Complex} {g : W -> F} (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν =
      ∫ x, (f x) • (fourierIntegral e ν L.flip g x) ∂μ :=
  integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul Complex Complex) he hL hf hg

/--
theorem `integral_sesq_fourierIntegral_eq_neg_flip` / 定理 `integral_sesq_fourierIntegral_eq_neg_flip`

English:
theorem integral_sesq_fourierIntegral_eq_neg_flip
  proof: by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul _ _).symm
    exact (fourierInt

中文:
定理 integral_sesq_fourierIntegral_eq_neg_flip
  证明: by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul _ _).symm
    exact (fourierInt

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.integral_comp_commSL, L.flip, M.flip, RCLike, RCLike.conj_smul, conj_smul, fourierIntegral_convergent_iff, integral, integral_comp_commSL, integral_fourierIntegral_swap
-/
theorem integral_sesq_fourierIntegral_eq_neg_flip
    {f : V -> E} {g : W -> F} (M : E ->L⋆[Complex] F ->L[Complex] G) (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν (-L.flip) g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    congr with x
    congr with ξ
    rw [← smul_one_smul Complex _ (f x)]; rw [← smul_one_smul Complex _ (g ξ)]
    simp only [map_smulₛₗ, ContinuousLinearMap.flip_apply, LinearMap.flip_apply, RingHom.id_apply,
      Circle.smul_def, smul_eq_mul, mul_one, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv,
      inv_inv]
  _ = ∫ x, (∫ ξ, M (f x) (e (-(-L.flip ξ) x) • g ξ) ∂ν) ∂μ := by
    simp only [LinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower, LinearMap.neg_apply,
      neg_neg]
  _ = ∫ x, M (f x) (∫ ξ, e (-(-L.flip ξ) x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    have hLflip : Continuous fun (p : W × V) => (-L.flip p.1) p.2 :=
      (continuous_neg.comp hL).comp continuous_swap
    exact (fourierIntegral_convergent_iff (L := -L.flip) he hLflip x).2 hg

end Fubini

/--
lemma `fourierIntegral_probChar` / 引理 `fourierIntegral_probChar`

English:
lemma fourierIntegral_probChar
  statement: {V W : Type*} {_ : MeasurableSpace V}
  proof: by
  simp_rw [fourierIntegral, Circle.smul_def, Real.probChar_apply, Complex.ofReal_neg]

中文:
引理 fourierIntegral_probChar
  结论: {V W : 类型} {_ : MeasurableSpace V}
  证明: by
  simp_rw [fourierIntegral, Circle.smul_def, Real.probChar_apply, Complex.ofReal_neg]

Depends on / 依赖: Circle, Circle.smul_def, Complex.ofReal_neg, Real.probChar_apply, fourierIntegral, ofReal_neg, probChar_apply, simp_rw, smul_def
-/
lemma fourierIntegral_probChar {V W : Type*} {_ : MeasurableSpace V}
    [AddCommGroup V] [Module Real V] [AddCommGroup W] [Module Real W]
    (L : V ->ₗ[Real] W ->ₗ[Real] Real) (μ : Measure V) (f : V -> E) (w : W) :
    fourierIntegral Real.probChar μ L f w =
      ∫ v : V, Complex.exp (- L v w * Complex.I) • f v ∂μ := by
  simp_rw [fourierIntegral, Circle.smul_def, Real.probChar_apply, Complex.ofReal_neg]

end VectorFourier

namespace VectorFourier

variable {𝕜 ι E F V W : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V ->L[𝕜] W ->L[𝕜] 𝕜}
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup E] [NormedSpace Complex E]
  {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace Real (M i)]

/--
theorem `fourierIntegral_continuousLinearMap_apply` / 定理 `fourierIntegral_continuousLinearMap_apply`

English:
theorem fourierIntegral_continuousLinearMap_apply
  proof: by
  rw [fourierIntegral]; rw [ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

中文:
定理 fourierIntegral_continuousLinearMap_apply
  证明: by
  rw [fourierIntegral]; rw [ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_apply, L.continuous, fourierIntegral, fourierIntegral_convergent_iff, integral_apply
-/
theorem fourierIntegral_continuousLinearMap_apply
    {f : V -> (F ->L[Real] E)} {a : F} {w : W} (he : Continuous e) (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w a =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x => f x a) w := by
  rw [fourierIntegral]; rw [ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

/--
theorem `fourierIntegral_continuousMultilinearMap_apply` / 定理 `fourierIntegral_continuousMultilinearMap_apply`

English:
theorem fourierIntegral_continuousMultilinearMap_apply
  proof: by
  rw [fourierIntegral]; rw [ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

中文:
定理 fourierIntegral_continuousMultilinearMap_apply
  证明: by
  rw [fourierIntegral]; rw [ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.integral_apply, L.continuous, fourierIntegral, fourierIntegral_convergent_iff, integral_apply
-/
theorem fourierIntegral_continuousMultilinearMap_apply
    {f : V -> (ContinuousMultilinearMap Real M E)} {m : (i : ι) -> M i} {w : W} (he : Continuous e)
    (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w m =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x => f x m) w := by
  rw [fourierIntegral]; rw [ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

end VectorFourier


/-! ## Fourier theory for functions on `𝕜` -/


namespace Fourier

variable {𝕜 : Type*} [CommRing 𝕜] [MeasurableSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace Complex E]

section Defs

/--
Definition of `fourierIntegral` / `fourierIntegral` 的定义

English:
definition fourierIntegral
  signature: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜)
  body: VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w

中文:
定义 fourierIntegral
  签名: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜)
  定义体: VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w

Depends on / 依赖: LinearMap, LinearMap.mul, VectorFourier, VectorFourier.fourierIntegral, fourierIntegral
-/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜) : E :=
  VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w

/--
theorem `fourierIntegral_def` / 定理 `fourierIntegral_def`

English:
theorem fourierIntegral_def
  given: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜)
  proof: rfl

中文:
定理 fourierIntegral_def
  条件: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜)
  证明: rfl
-/
theorem fourierIntegral_def (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜) :
    fourierIntegral e μ f w = ∫ v : 𝕜, e (-(v * w)) • f v ∂μ :=
  rfl

/--
theorem `fourierIntegral_const_smul` / 定理 `fourierIntegral_const_smul`

English:
theorem fourierIntegral_const_smul
  given: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (r : Complex)
  proof: VectorFourier.fourierIntegral_const_smul _ _ _ _ _

中文:
定理 fourierIntegral_const_smul
  条件: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (r : Complex)
  证明: VectorFourier.fourierIntegral_const_smul _ _ _ _ _

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_const_smul, fourierIntegral_const_smul
-/
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (r : Complex) :
    fourierIntegral e μ (r • f) = r • fourierIntegral e μ f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/--
theorem `norm_fourierIntegral_le_integral_norm` / 定理 `norm_fourierIntegral_le_integral_norm`

English:
theorem norm_fourierIntegral_le_integral_norm
  statement: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
  proof: VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

中文:
定理 norm_fourierIntegral_le_integral_norm
  结论: (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
  证明: VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

Depends on / 依赖: VectorFourier, VectorFourier.norm_fourierIntegral_le_integral_norm, norm_fourierIntegral_le_integral_norm
-/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    (f : 𝕜 -> E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ <= ∫ x : 𝕜, ‖f x‖ ∂μ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/--
theorem `fourierIntegral_comp_add_right` / 定理 `fourierIntegral_comp_add_right`

English:
theorem fourierIntegral_comp_add_right
  statement: [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
  proof: VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

中文:
定理 fourierIntegral_comp_add_right
  结论: [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
  证明: VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_comp_add_right, fourierIntegral_comp_add_right
-/
theorem fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    [μ.IsAddRightInvariant] (f : 𝕜 -> E) (v₀ : 𝕜) :
    fourierIntegral e μ (f ∘ fun v => v + v₀) = fun w => e (v₀ * w) • fourierIntegral e μ f w :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

end Defs

end Fourier

open scoped Real

namespace Real

open FourierTransform

variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
theorem `vector_fourierIntegral_eq_integral_exp_smul` / 定理 `vector_fourierIntegral_eq_integral_exp_smul`

English:
theorem vector_fourierIntegral_eq_integral_exp_smul
  statement: {V : Type*} [AddCommGroup V] [Module Real V]
  proof: by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]

中文:
定理 vector_fourierIntegral_eq_integral_exp_smul
  结论: {V : 类型} [AddCommGroup V] [Module 实数 V]
  证明: by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]

Depends on / 依赖: Circle, Circle.smul_def, Real.fourierChar_apply, VectorFourier, VectorFourier.fourierIntegral, fourierChar_apply, fourierIntegral, mul_neg, neg_mul, simp_rw, smul_def
-/
theorem vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [Module Real V]
    [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module Real W] (L : V ->ₗ[Real] W ->ₗ[Real] Real)
    (μ : Measure V) (f : V -> E) (w : W) :
    VectorFourier.fourierIntegral fourierChar μ L f w =
      ∫ v : V, Complex.exp (↑(-2 * π * L v w) * Complex.I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]

/-- The Fourier integral is well defined iff the function is integrable. Version with a general
continuous bilinear function `L`. For the specialization to the inner product in an inner product
space, see `Real.fourierIntegral_convergent_iff`. -/
@[simp]
/--
theorem `fourierIntegral_convergent_iff'` / 定理 `fourierIntegral_convergent_iff'`

English:
theorem fourierIntegral_convergent_iff'
  statement: {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  proof: VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₁₂)
    continuous_fourierChar L.continuous₂ _

中文:
定理 fourierIntegral_convergent_iff'
  结论: {V W : 类型} [NormedAddCommGroup V] [NormedSpace 实数 V]
  证明: VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₁₂)
    continuous_fourierChar L.continuous₂ _

Depends on / 依赖: L.continuous, L.toLinearMap, VectorFourier, VectorFourier.fourierIntegral_convergent_iff, continuous_fourierChar, fourierIntegral_convergent_iff
-/
theorem fourierIntegral_convergent_iff' {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V -> E} (L : V ->L[Real] W ->L[Real] Real) (w : W) :
    Integrable (fun v : V => 𝐞 (- L v w) • f v) μ ↔ Integrable f μ :=
  VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₁₂)
    continuous_fourierChar L.continuous₂ _

section Apply

variable {ι F V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace Real W]
  {μ : Measure V} {L : V ->L[Real] W ->L[Real] Real}
  [NormedAddCommGroup F] [NormedSpace Real F]
  {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace Real (M i)]

/--
theorem `fourierIntegral_continuousLinearMap_apply'` / 定理 `fourierIntegral_continuousLinearMap_apply'`

English:
theorem fourierIntegral_continuousLinearMap_apply'
  proof: VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf

中文:
定理 fourierIntegral_continuousLinearMap_apply'
  证明: VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_continuousLinearMap_apply, continuous_fourierChar, fourierIntegral_continuousLinearMap_apply
-/
theorem fourierIntegral_continuousLinearMap_apply'
    {f : V -> (F ->L[Real] E)} {a : F} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w a =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x => f x a) w :=
  VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf

/--
theorem `fourierIntegral_continuousMultilinearMap_apply'` / 定理 `fourierIntegral_continuousMultilinearMap_apply'`

English:
theorem fourierIntegral_continuousMultilinearMap_apply'
  proof: VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf

中文:
定理 fourierIntegral_continuousMultilinearMap_apply'
  证明: VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_continuousMultilinearMap_apply, continuous_fourierChar, fourierIntegral_continuousMultilinearMap_apply
-/
theorem fourierIntegral_continuousMultilinearMap_apply'
    {f : V -> ContinuousMultilinearMap Real M E} {m : (i : ι) -> M i} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w m =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x => f x m) w :=
  VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf

end Apply

variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace Real W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional Real W]

open scoped RealInnerProductSpace

/--
theorem `fourierIntegral_convergent_iff` / 定理 `fourierIntegral_convergent_iff`

English:
theorem fourierIntegral_convergent_iff
  given: {μ : Measure V} {f : V -> E} (w : V)
  proof: fourierIntegral_convergent_iff' (innerSL Real) w

中文:
定理 fourierIntegral_convergent_iff
  条件: {μ : Measure V} {f : V -> E} (w : V)
  证明: fourierIntegral_convergent_iff' (innerSL Real) w
-/
@[simp] theorem fourierIntegral_convergent_iff {μ : Measure V} {f : V -> E} (w : V) :
    Integrable (fun v : V => 𝐞 (- ⟪v, w⟫) • f v) μ ↔ Integrable f μ :=
  fourierIntegral_convergent_iff' (innerSL Real) w

variable [FiniteDimensional Real V]

/--
Instance `instFourierTransform` / 实例 `instFourierTransform`

English:
instance instFourierTransform
  signature: : FourierTransform (V -> E) (V -> E) where
  body: VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f

中文:
实例 instFourierTransform
  签名: : FourierTransform (V -> E) (V -> E) where
  定义体: VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral, fourierIntegral, volume
-/
instance instFourierTransform : FourierTransform (V -> E) (V -> E) where
  fourier f := VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f

/--
Instance `instFourierTransformInv` / 实例 `instFourierTransformInv`

English:
instance instFourierTransformInv
  signature: : FourierTransformInv (V -> E) (V -> E) where
  body: VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w

中文:
实例 instFourierTransformInv
  签名: : FourierTransformInv (V -> E) (V -> E) where
  定义体: VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral, fourierIntegral, volume
-/
instance instFourierTransformInv : FourierTransformInv (V -> E) (V -> E) where
  fourierInv f w := VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w

/--
lemma `fourier_eq` / 引理 `fourier_eq`

English:
lemma fourier_eq
  given: (f : V -> E) (w : V)
  proof: rfl

中文:
引理 fourier_eq
  条件: (f : V -> E) (w : V)
  证明: rfl
-/
lemma fourier_eq (f : V -> E) (w : V) :
    𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v := rfl

/--
lemma `fourier_eq'` / 引理 `fourier_eq'`

English:
lemma fourier_eq'
  given: (f : V -> E) (w : V)
  proof: by
  simp_rw [fourier_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]

中文:
引理 fourier_eq'
  条件: (f : V -> E) (w : V)
  证明: by
  simp_rw [fourier_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]

Depends on / 依赖: Circle, Circle.smul_def, Real.fourierChar_apply, fourierChar_apply, fourier_eq, mul_neg, neg_mul, simp_rw, smul_def
-/
lemma fourier_eq' (f : V -> E) (w : V) :
    𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourier_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]

/--
theorem `fourier_congr_ae` / 定理 `fourier_congr_ae`

English:
theorem fourier_congr_ae
  given: {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V)
  statement: 𝓕 f₁ x = 𝓕 f₂ x
  proof: by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

中文:
定理 fourier_congr_ae
  条件: {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V)
  结论: 𝓕 f₁ x = 𝓕 f₂ x
  证明: by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
theorem fourier_congr_ae {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V) : 𝓕 f₁ x = 𝓕 f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

/--
lemma `fourierInv_eq` / 引理 `fourierInv_eq`

English:
lemma fourierInv_eq
  given: (f : V -> E) (w : V)
  proof: by
  simp [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral]

中文:
引理 fourierInv_eq
  条件: (f : V -> E) (w : V)
  证明: by
  simp [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral]

Depends on / 依赖: FourierTransformInv, FourierTransformInv.fourierInv, VectorFourier, VectorFourier.fourierIntegral, fourierIntegral, fourierInv
-/
lemma fourierInv_eq (f : V -> E) (w : V) :
    𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v := by
  simp [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral]

/--
lemma `fourierInv_eq'` / 引理 `fourierInv_eq'`

English:
lemma fourierInv_eq'
  given: (f : V -> E) (w : V)
  proof: by
  simp_rw [fourierInv_eq, Circle.smul_def, Real.fourierChar_apply]

中文:
引理 fourierInv_eq'
  条件: (f : V -> E) (w : V)
  证明: by
  simp_rw [fourierInv_eq, Circle.smul_def, Real.fourierChar_apply]

Depends on / 依赖: Circle, Circle.smul_def, Real.fourierChar_apply, fourierChar_apply, fourierInv_eq, simp_rw, smul_def
-/
lemma fourierInv_eq' (f : V -> E) (w : V) :
    𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierInv_eq, Circle.smul_def, Real.fourierChar_apply]

/--
lemma `fourier_comp_linearIsometry` / 引理 `fourier_comp_linearIsometry`

English:
lemma fourier_comp_linearIsometry
  given: (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W)
  proof: by
  simp only [fourier_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]

中文:
引理 fourier_comp_linearIsometry
  条件: (A : W ≃ₗᵢ[实数] V) (f : V -> E) (w : W)
  证明: by
  simp only [fourier_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]

Depends on / 依赖: A.inner_map_map, A.measurePreserving, A.toHomeomorph.measurableEmbedding, Function, Function.comp_apply, MeasurePreserving, MeasurePreserving.integral_comp, comp_apply, fourier_eq, inner_map_map, integral_comp, measurableEmbedding, measurePreserving, toHomeomorph
-/
lemma fourier_comp_linearIsometry (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W) :
    𝓕 (f ∘ A) w = (𝓕 f) (A w) := by
  simp only [fourier_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]

/--
lemma `fourierInv_eq_fourier_neg` / 引理 `fourierInv_eq_fourier_neg`

English:
lemma fourierInv_eq_fourier_neg
  given: (f : V -> E) (w : V)
  proof: by
  simp [fourier_eq, fourierInv_eq]

中文:
引理 fourierInv_eq_fourier_neg
  条件: (f : V -> E) (w : V)
  证明: by
  simp [fourier_eq, fourierInv_eq]

Depends on / 依赖: fourierInv_eq, fourier_eq
-/
lemma fourierInv_eq_fourier_neg (f : V -> E) (w : V) :
    𝓕⁻ f w = 𝓕 f (-w) := by
  simp [fourier_eq, fourierInv_eq]

/--
lemma `fourierInv_eq_fourier_comp_neg` / 引理 `fourierInv_eq_fourier_comp_neg`

English:
lemma fourierInv_eq_fourier_comp_neg
  given: (f : V -> E)
  proof: by
  ext y
  rw [fourierInv_eq_fourier_neg]
  change 𝓕 f (LinearIsometryEquiv.neg Real y) = 𝓕 (f ∘ LinearIsometryEquiv.neg Real) y
  exact (fourier_comp_linearIsometry _ _ _).symm

中文:
引理 fourierInv_eq_fourier_comp_neg
  条件: (f : V -> E)
  证明: by
  ext y
  rw [fourierInv_eq_fourier_neg]
  change 𝓕 f (LinearIsometryEquiv.neg Real y) = 𝓕 (f ∘ LinearIsometryEquiv.neg Real) y
  exact (fourier_comp_linearIsometry _ _ _).symm

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.neg, fourierInv_eq_fourier_neg, fourier_comp_linearIsometry
-/
lemma fourierInv_eq_fourier_comp_neg (f : V -> E) :
    𝓕⁻ f = 𝓕 (fun x => f (-x)) := by
  ext y
  rw [fourierInv_eq_fourier_neg]
  change 𝓕 f (LinearIsometryEquiv.neg Real y) = 𝓕 (f ∘ LinearIsometryEquiv.neg Real) y
  exact (fourier_comp_linearIsometry _ _ _).symm

/--
lemma `fourierInv_comm` / 引理 `fourierInv_comm`

English:
lemma fourierInv_comm
  given: (f : V -> E)
  proof: by
  conv_rhs => rw [fourierInv_eq_fourier_comp_neg]
  simp_rw [← fourierInv_eq_fourier_neg]

中文:
引理 fourierInv_comm
  条件: (f : V -> E)
  证明: by
  conv_rhs => rw [fourierInv_eq_fourier_comp_neg]
  simp_rw [← fourierInv_eq_fourier_neg]

Depends on / 依赖: conv_rhs, fourierInv_eq_fourier_comp_neg, fourierInv_eq_fourier_neg, simp_rw
-/
lemma fourierInv_comm (f : V -> E) :
    𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f) := by
  conv_rhs => rw [fourierInv_eq_fourier_comp_neg]
  simp_rw [← fourierInv_eq_fourier_neg]

/--
lemma `fourierInv_comp_linearIsometry` / 引理 `fourierInv_comp_linearIsometry`

English:
lemma fourierInv_comp_linearIsometry
  given: (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W)
  proof: by
  simp [fourierInv_eq_fourier_neg, fourier_comp_linearIsometry]

中文:
引理 fourierInv_comp_linearIsometry
  条件: (A : W ≃ₗᵢ[实数] V) (f : V -> E) (w : W)
  证明: by
  simp [fourierInv_eq_fourier_neg, fourier_comp_linearIsometry]

Depends on / 依赖: fourierInv_eq_fourier_neg, fourier_comp_linearIsometry
-/
lemma fourierInv_comp_linearIsometry (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W) :
    𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w) := by
  simp [fourierInv_eq_fourier_neg, fourier_comp_linearIsometry]

/--
theorem `fourier_real_eq` / 定理 `fourier_real_eq`

English:
theorem fourier_real_eq
  given: (f : Real -> E) (w : Real)
  proof: by
  simp_rw [mul_comm _ w]
  rfl

中文:
定理 fourier_real_eq
  条件: (f : 实数 -> E) (w : 实数)
  证明: by
  simp_rw [mul_comm _ w]
  rfl

Depends on / 依赖: mul_comm, simp_rw
-/
theorem fourier_real_eq (f : Real -> E) (w : Real) :
    𝓕 f w = ∫ v : Real, 𝐞 (-(v * w)) • f v := by
  simp_rw [mul_comm _ w]
  rfl

/--
theorem `fourier_real_eq_integral_exp_smul` / 定理 `fourier_real_eq_integral_exp_smul`

English:
theorem fourier_real_eq_integral_exp_smul
  given: (f : Real -> E) (w : Real)
  proof: by
  simp_rw [fourier_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]

中文:
定理 fourier_real_eq_integral_exp_smul
  条件: (f : 实数 -> E) (w : 实数)
  证明: by
  simp_rw [fourier_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]

Depends on / 依赖: Circle, Circle.smul_def, Real.fourierChar_apply, fourierChar_apply, fourier_real_eq, mul_assoc, mul_neg, neg_mul, simp_rw, smul_def
-/
theorem fourier_real_eq_integral_exp_smul (f : Real -> E) (w : Real) :
    𝓕 f w = ∫ v : Real, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourier_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]

/--
theorem `fourier_continuousLinearMap_apply` / 定理 `fourier_continuousLinearMap_apply`

English:
theorem fourier_continuousLinearMap_apply
  proof: fourierIntegral_continuousLinearMap_apply' (L := innerSL Real) hf

中文:
定理 fourier_continuousLinearMap_apply
  证明: fourierIntegral_continuousLinearMap_apply' (L := innerSL Real) hf

Depends on / 依赖: fourierIntegral_continuousLinearMap_apply, innerSL
-/
theorem fourier_continuousLinearMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {f : V -> (F ->L[Real] E)} {a : F} {v : V} (hf : Integrable f) :
    𝓕 f v a = 𝓕 (fun x => f x a) v :=
  fourierIntegral_continuousLinearMap_apply' (L := innerSL Real) hf

/--
theorem `fourier_continuousMultilinearMap_apply` / 定理 `fourier_continuousMultilinearMap_apply`

English:
theorem fourier_continuousMultilinearMap_apply
  statement: {ι : Type*} [Fintype ι]
  proof: fourierIntegral_continuousMultilinearMap_apply' (L := innerSL Real) hf

中文:
定理 fourier_continuousMultilinearMap_apply
  结论: {ι : 类型} [Fintype ι]
  证明: fourierIntegral_continuousMultilinearMap_apply' (L := innerSL Real) hf

Depends on / 依赖: fourierIntegral_continuousMultilinearMap_apply, innerSL
-/
theorem fourier_continuousMultilinearMap_apply {ι : Type*} [Fintype ι]
    {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace Real (M i)]
    {f : V -> ContinuousMultilinearMap Real M E} {m : (i : ι) -> M i} {v : V} (hf : Integrable f) :
    𝓕 f v m = 𝓕 (fun x => f x m) v :=
  fourierIntegral_continuousMultilinearMap_apply' (L := innerSL Real) hf

open scoped BoundedContinuousFunction

/--
Definition of `Lp.fourierTransform` / `Lp.fourierTransform` 的定义

English:
definition Lp.fourierTransform
  signature: (f : Lp (α := V) E 1)
  body: BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V -> E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL Real).continuous₂ (L1.integrable_coeFn f))
  ‖f‖ fun x => by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [C

中文:
定义 Lp.fourierTransform
  签名: (f : Lp (α := V) E 1)
  定义体: BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V -> E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL Real).continuous₂ (L1.integrable_coeFn f))
  ‖f‖ fun x => by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [C
-/
def Lp.fourierTransform (f : Lp (α := V) E 1) : V ->ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V -> E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL Real).continuous₂ (L1.integrable_coeFn f))
  ‖f‖ fun x => by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le

@[norm_cast]
/--
theorem `Lp.coe_fourierTransform` / 定理 `Lp.coe_fourierTransform`

English:
theorem Lp.coe_fourierTransform
  given: (f : Lp (α := V) E 1)
  proof: rfl

@[simp]

中文:
定理 Lp.coe_fourierTransform
  条件: (f : Lp (α := V) E 1)
  证明: rfl

@[simp]
-/
theorem Lp.coe_fourierTransform (f : Lp (α := V) E 1) :
    (Lp.fourierTransform f : V -> E) = 𝓕 (f : V -> E) := rfl

@[simp]
/--
theorem `Lp.fourierTransform_apply` / 定理 `Lp.fourierTransform_apply`

English:
theorem Lp.fourierTransform_apply
  given: (f : Lp (α := V) E 1) (x : V)
  proof: rfl

@[simp]

中文:
定理 Lp.fourierTransform_apply
  条件: (f : Lp (α := V) E 1) (x : V)
  证明: rfl

@[simp]
-/
theorem Lp.fourierTransform_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransform f x = 𝓕 (f : V -> E) x := rfl

@[simp]
/--
theorem `fourierTransform_toLp` / 定理 `fourierTransform_toLp`

English:
theorem fourierTransform_toLp
  given: {f : V -> E} (hf : MemLp f 1)
  proof: by
  simp only [Lp.coe_fourierTransform]
  ext x
  exact (Real.fourier_congr_ae hf.coeFn_toLp) x

中文:
定理 fourierTransform_toLp
  条件: {f : V -> E} (hf : MemLp f 1)
  证明: by
  simp only [Lp.coe_fourierTransform]
  ext x
  exact (Real.fourier_congr_ae hf.coeFn_toLp) x

Depends on / 依赖: Lp.coe_fourierTransform, Real.fourier_congr_ae, coeFn_toLp, coe_fourierTransform, fourier_congr_ae, hf.coeFn_toLp
-/
theorem fourierTransform_toLp {f : V -> E} (hf : MemLp f 1) :
    (Lp.fourierTransform hf.toLp : V -> E) = 𝓕 f := by
  simp only [Lp.coe_fourierTransform]
  ext x
  exact (Real.fourier_congr_ae hf.coeFn_toLp) x

variable (V E) in
/--
Definition of `Lp.fourierTransformCLM` / `Lp.fourierTransformCLM` 的定义

English:
definition Lp.fourierTransformCLM
  signature: : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E
  body: LinearMap.mkContinuous
    { toFun := Lp.fourierTransform
      map_add' f g := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
          Real.fourier_eq]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_up

中文:
定义 Lp.fourierTransformCLM
  签名: : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E
  定义体: LinearMap.mkContinuous
    { toFun := Lp.fourierTransform
      map_add' f g := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
          Real.fourier_eq]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_up
-/
def Lp.fourierTransformCLM : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E :=
  LinearMap.mkContinuous
    { toFun := Lp.fourierTransform
      map_add' f g := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
          Real.fourier_eq]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with x h₁
          rw [h₁]
          simp
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn f
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn g
      map_smul' c f := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_smul, Real.fourier_eq]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x h
        rw [h]; rw [smul_comm]
        simp }
    1 fun f => by
      rw [one_mul]; rw [BoundedContinuousFunction.norm_le (by positivity)]
      intro x
      rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]; rw [Lp.fourierTransform_apply]; rw [Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans
      simp_rw [Circle.norm_smul]
      exact (L1.norm_eq_integral_norm f).symm.le

@[simp]
/--
theorem `Lp.fourierTransformCLM_apply` / 定理 `Lp.fourierTransformCLM_apply`

English:
theorem Lp.fourierTransformCLM_apply
  given: (f : Lp (α := V) E 1)
  proof: rfl

中文:
定理 Lp.fourierTransformCLM_apply
  条件: (f : Lp (α := V) E 1)
  证明: rfl
-/
theorem Lp.fourierTransformCLM_apply (f : Lp (α := V) E 1) :
  Lp.fourierTransformCLM V E f = Lp.fourierTransform f := rfl

/--
Definition of `Lp.fourierTransformInv` / `Lp.fourierTransformInv` 的定义

English:
definition Lp.fourierTransformInv
  signature: (f : Lp (α := V) E 1)
  body: (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)

中文:
定义 Lp.fourierTransformInv
  签名: (f : Lp (α := V) E 1)
  定义体: (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)
-/
def Lp.fourierTransformInv (f : Lp (α := V) E 1) : V ->ᵇ E :=
  (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)

/--
theorem `fourierInv_congr_ae` / 定理 `fourierInv_congr_ae`

English:
theorem fourierInv_congr_ae
  given: {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V)
  proof: by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

@[simp]

中文:
定理 fourierInv_congr_ae
  条件: {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V)
  证明: by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

@[simp]

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
theorem fourierInv_congr_ae {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V) :
    𝓕⁻ f₁ x = 𝓕⁻ f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

@[simp]
/--
theorem `Lp.fourierTransformInv_apply` / 定理 `Lp.fourierTransformInv_apply`

English:
theorem Lp.fourierTransformInv_apply
  given: (f : Lp (α := V) E 1) (x : V)
  proof: by
  simp [Lp.fourierTransformInv, fourierInv_eq_fourier_neg]

@[norm_cast]

中文:
定理 Lp.fourierTransformInv_apply
  条件: (f : Lp (α := V) E 1) (x : V)
  证明: by
  simp [Lp.fourierTransformInv, fourierInv_eq_fourier_neg]

@[norm_cast]
-/
theorem Lp.fourierTransformInv_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformInv f x = 𝓕⁻ (f : V -> E) x := by
  simp [Lp.fourierTransformInv, fourierInv_eq_fourier_neg]

@[norm_cast]
/--
theorem `Lp.coe_fourierTransformInv` / 定理 `Lp.coe_fourierTransformInv`

English:
theorem Lp.coe_fourierTransformInv
  given: (f : Lp (α := V) E 1)
  proof: by
  ext x
  simp

@[simp]

中文:
定理 Lp.coe_fourierTransformInv
  条件: (f : Lp (α := V) E 1)
  证明: by
  ext x
  simp

@[simp]
-/
theorem Lp.coe_fourierTransformInv (f : Lp (α := V) E 1) :
    (Lp.fourierTransformInv f : V -> E) = 𝓕⁻ (f : V -> E) := by
  ext x
  simp

@[simp]
/--
theorem `Lp.fourierTransformInv_toLp` / 定理 `Lp.fourierTransformInv_toLp`

English:
theorem Lp.fourierTransformInv_toLp
  given: {f : V -> E} (hf : MemLp f 1)
  proof: by
  ext x
  simpa using (Real.fourierInv_congr_ae hf.coeFn_toLp) x

中文:
定理 Lp.fourierTransformInv_toLp
  条件: {f : V -> E} (hf : MemLp f 1)
  证明: by
  ext x
  simpa using (Real.fourierInv_congr_ae hf.coeFn_toLp) x

Depends on / 依赖: Real.fourierInv_congr_ae, coeFn_toLp, fourierInv_congr_ae, hf.coeFn_toLp
-/
theorem Lp.fourierTransformInv_toLp {f : V -> E} (hf : MemLp f 1) :
    (Lp.fourierTransformInv hf.toLp : V -> E) = 𝓕⁻ f := by
  ext x
  simpa using (Real.fourierInv_congr_ae hf.coeFn_toLp) x

variable (V E) in
/--
Definition of `Lp.fourierTransformInvCLM` / `Lp.fourierTransformInvCLM` 的定义

English:
definition Lp.fourierTransformInvCLM
  signature: : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E
  body: BoundedContinuousFunction.compContinuousCLM _ Complex (-.id V) ∘L Lp.fourierTransformCLM V E

@[simp]

中文:
定义 Lp.fourierTransformInvCLM
  签名: : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E
  定义体: BoundedContinuousFunction.compContinuousCLM _ Complex (-.id V) ∘L Lp.fourierTransformCLM V E

@[simp]
-/
def Lp.fourierTransformInvCLM : Lp (α := V) E 1 ->L[Complex] V ->ᵇ E :=
  BoundedContinuousFunction.compContinuousCLM _ Complex (-.id V) ∘L Lp.fourierTransformCLM V E

@[simp]
/--
theorem `Lp.fourierTransformInvCLM_apply` / 定理 `Lp.fourierTransformInvCLM_apply`

English:
theorem Lp.fourierTransformInvCLM_apply
  given: (f : Lp (α := V) E 1)
  proof: by
  simp [Lp.fourierTransformInvCLM, Lp.fourierTransformInv]

中文:
定理 Lp.fourierTransformInvCLM_apply
  条件: (f : Lp (α := V) E 1)
  证明: by
  simp [Lp.fourierTransformInvCLM, Lp.fourierTransformInv]
-/
theorem Lp.fourierTransformInvCLM_apply (f : Lp (α := V) E 1) :
    Lp.fourierTransformInvCLM V E f = Lp.fourierTransformInv f := by
  simp [Lp.fourierTransformInvCLM, Lp.fourierTransformInv]

end Real
