/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.IdentDistrib

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

We also state results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution.

## Main definitions

* `TendstoInDistribution X l Z μ`: the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
* `tendstoInDistribution_of_tendstoInMeasure_sub`: the main technical tool for the next results.
  Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
  to `Z`, and `Y n - X n` converges in probability to `0`.
  Then `Y n` converges in distribution to `Z`.
* `TendstoInMeasure.tendstoInDistribution`: convergence in probability implies convergence in
  distribution.
* `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`: **Slutsky's theorem**.
  If `X n` converges in distribution to `Z`, and `Y n` converges in probability to a constant `c`,
  then the pair `(X n, Y n)` converges in distribution to `(Z, c)`.

-/

public section

open Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory

variable {ι E Ω' Ω'' : Type*} {Ω : ι -> Type*} {m : forall i, MeasurableSpace (Ω i)}
  {μ : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} {X Y : (i : ι) -> Ω i -> E} {Z : Ω' -> E} {l : Filter ι}

section TendstoInDistribution

variable [TopologicalSpace E]

/--
Definition of `TendstoInDistribution` / `TendstoInDistribution` 的定义

English:
structure TendstoInDistribution
  parameters: [OpensMeasurableSpace E] (X : (i : ι) -> Ω i -> E) (l : Filter ι)
  axioms and operations (3):
    - forall_aemeasurable : forall i, AEMeasurable (X i) (μ i)
    - aemeasurable_limit : AEMeasurable Z μ'  [default: by fun_prop]
    - tendsto : Tendsto (β := ProbabilityMeasure E) (fun n => ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

中文:
结构 TendstoInDistribution
  参数: [OpensMeasurable空间 E] (X : (i : ι) -> Ω i -> E) (l : 滤子 ι)
  公理与运算 (3 个):
    - forall_aemeasurable : 对任意 i, 几乎处处可测 (X i) (μ i)
    - aemeasurable_limit : 几乎处处可测 Z μ'  [默认: by fun_prop]
    - tendsto : 收敛 (β := 概率测度 E) (fun n => ⟨(μ n).map (X n), 测度.isProbabilityMeasure_map (对任意_aemeasurable n)⟩) l (𝓝 ⟨μ'.map Z, 测度.isProbabilityMeasure_map aemeasurable_limit⟩)

Depends on / 依赖: AEMeasurable, IsProbabilityMeasure, Measure, Measure.isProbabilityMeasure_map, ProbabilityMeasure, Tendsto, aemeasurable_limit, forall_aemeasurable, fun_prop, isProbabilityMeasure_map, tendsto, volume_tac
-/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) -> Ω i -> E) (l : Filter ι)
    (Z : Ω' -> E) (μ : (i : ι) -> Measure (Ω i)) [forall i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : forall i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

/--
lemma `tendstoInDistribution_const` / 引理 `tendstoInDistribution_const`

English:
lemma tendstoInDistribution_const
  given: [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ')
  proof: fun _ => by fun_prop
  tendsto := tendsto_const_nhds

中文:
引理 tendstoInDistribution_const
  条件: [OpensMeasurable空间 E] (hZ : 几乎处处可测 Z μ')
  证明: fun _ => by fun_prop
  tendsto := tendsto_const_nhds

Depends on / 依赖: fun_prop
-/
lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ') :
    TendstoInDistribution (fun _ => Z) l Z (fun _ => μ') μ' where
  forall_aemeasurable := fun _ => by fun_prop
  tendsto := tendsto_const_nhds

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tendstoInDistribution_of_identDistrib` / 引理 `tendstoInDistribution_of_identDistrib`

English:
lemma tendstoInDistribution_of_identDistrib
  statement: [OpensMeasurableSpace E] (i : ι)
  proof: (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert! tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq

中文:
引理 tendstoInDistribution_of_identDistrib
  结论: [OpensMeasurable空间 E] (i : ι)
  证明: (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert! tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq

Depends on / 依赖: aemeasurable_snd
-/
lemma tendstoInDistribution_of_identDistrib [OpensMeasurableSpace E] (i : ι)
    (hX : forall j, IdentDistrib (X i) (X j) (μ i) (μ j)) (hZ : IdentDistrib (X i) Z (μ i) μ') :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable j := (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert! tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `TendstoInDistribution.congr` / 引理 `TendstoInDistribution.congr`

English:
lemma TendstoInDistribution.congr
  statement: [OpensMeasurableSpace E] {T : Ω' -> E}
  proof: (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert! h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

@[simp]

中文:
引理 TendstoInDistribution.congr
  结论: [OpensMeasurable空间 E] {T : Ω' -> E}
  证明: (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert! h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

@[simp]
-/
protected lemma TendstoInDistribution.congr [OpensMeasurableSpace E] {T : Ω' -> E}
    (hXY : forall i, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable i := (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert! h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

@[simp]
/--
lemma `tendstoInDistribution_of_isEmpty` / 引理 `tendstoInDistribution_of_isEmpty`

English:
lemma tendstoInDistribution_of_isEmpty
  given: [IsEmpty E]
  proof: fun _ => (measurable_of_subsingleton_codomain _).aemeasurable
  aemeasurable_limit := (measurable_of_subsingleton_codomain _).aemeasurable
  tendsto := by
    simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds

中文:
引理 tendstoInDistribution_of_isEmpty
  条件: [是空 E]
  证明: fun _ => (measurable_of_subsingleton_codomain _).aemeasurable
  aemeasurable_limit := (measurable_of_subsingleton_codomain _).aemeasurable
  tendsto := by
    simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds

Depends on / 依赖: aemeasurable, measurable_of_subsingleton_codomain
-/
lemma tendstoInDistribution_of_isEmpty [IsEmpty E] :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable := fun _ => (measurable_of_subsingleton_codomain _).aemeasurable
  aemeasurable_limit := (measurable_of_subsingleton_codomain _).aemeasurable
  tendsto := by
    simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tendstoInDistribution_unique` / 引理 `tendstoInDistribution_unique`

English:
lemma tendstoInDistribution_unique
  statement: [HasOuterApproxClosed E] [BorelSpace E]
  proof: by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

中文:
引理 tendstoInDistribution_unique
  结论: [有OuterApproxClosed E] [Borel空间 E]
  证明: by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, h1.tendsto, h2.tendsto, h_eq, tendsto, tendsto_nhds_unique
-/
lemma tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E]
    (X : (i : ι) -> Ω i -> E) {Z : Ω' -> E} {W : Ω'' -> E} [l.NeBot]
    (h1 : TendstoInDistribution X l Z μ μ') (h2 : TendstoInDistribution X l W μ μ'') :
    μ'.map Z = μ''.map W := by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `TendstoInDistribution.continuous_comp` / 定理 `TendstoInDistribution.continuous_comp`

English:
theorem TendstoInDistribution.continuous_comp
  statement: {F : Type*} [OpensMeasurableSpace E]
  proof: fun n => hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

中文:
定理 TendstoInDistribution.continuous_comp
  结论: {F : 类型} [OpensMeasurable空间 E]
  证明: fun n => hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

Depends on / 依赖: comp_aemeasurable, forall_aemeasurable, h.forall_aemeasurable, hg.measurable.comp_aemeasurable, measurable
-/
theorem TendstoInDistribution.continuous_comp {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E -> F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) μ μ' where
  forall_aemeasurable := fun n => hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tendstoInDistribution_of_ae_tendsto` / 定理 `tendstoInDistribution_of_ae_tendsto`

English:
theorem tendstoInDistribution_of_ae_tendsto
  statement: [l.IsCountablyGenerated]
  proof: hX₁
  aemeasurable_limit := hZ
  tendsto := by
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, ProbabilityMeasure.coe_mk]
    intro f
    rw [lintegral_map' (by fun_prop) hZ]
    conv in ∫⁻ _, _ ∂_ => rw [lintegral_map' (by fun_prop) (hX₁ i)]
    apply tendsto_lintegral_filter_of_dominated_convergence' (bound := fun _ => edist 0 f)
    · exact .of_forall (by fun_prop)
    · simp [f.apply_le_edist_zero]
    · simp
    filter_upwards [hX₂] with ω hω
.comp hω simpa [Function.comp_def] using f.continuous.tendsto (Z ω)

中文:
定理 tendstoInDistribution_of_ae_tendsto
  结论: [l.是余untablyGenerated]
  证明: hX₁
  aemeasurable_limit := hZ
  tendsto := by
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, ProbabilityMeasure.coe_mk]
    intro f
    rw [lintegral_map' (by fun_prop) hZ]
    conv in ∫⁻ _, _ ∂_ => rw [lintegral_map' (by fun_prop) (hX₁ i)]
    apply tendsto_lintegral_filter_of_dominated_convergence' (bound := fun _ => edist 0 f)
    · exact .of_forall (by fun_prop)
    · simp [f.apply_le_edist_zero]
    · simp
    filter_upwards [hX₂] with ω hω
.comp hω simpa [Function.comp_def] using f.continuous.tendsto (Z ω)
-/
theorem tendstoInDistribution_of_ae_tendsto [l.IsCountablyGenerated]
    [OpensMeasurableSpace E] {X : ι -> Ω' -> E}
    (hX₁ : forall i, AEMeasurable (X i) μ') (hZ : AEMeasurable Z μ')
    (hX₂ : forallᵐ ω ∂μ', Tendsto (fun i => X i ω) l (𝓝 (Z ω))) :
    TendstoInDistribution X l Z (fun _ => μ') μ' where
  forall_aemeasurable := hX₁
  aemeasurable_limit := hZ
  tendsto := by
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, ProbabilityMeasure.coe_mk]
    intro f
    rw [lintegral_map' (by fun_prop) hZ]
    conv in ∫⁻ _, _ ∂_ => rw [lintegral_map' (by fun_prop) (hX₁ i)]
    apply tendsto_lintegral_filter_of_dominated_convergence' (bound := fun _ => edist 0 f)
    · exact .of_forall (by fun_prop)
    · simp [f.apply_le_edist_zero]
    · simp
    filter_upwards [hX₂] with ω hω
.comp hω simpa [Function.comp_def] using f.continuous.tendsto (Z ω)

end TendstoInDistribution

/--
theorem `TendstoInMeasure.tendstoInDistribution` / 定理 `TendstoInMeasure.tendstoInDistribution`

English:
theorem TendstoInMeasure.tendstoInDistribution
  statement: [PseudoEMetricSpace E] [BorelSpace E]
  proof: by
  have hZ := h.aemeasurable hX
  refine ⟨hX, hZ, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
.exists_seq_tendsto_ae' obtain ⟨ms, hms1, hms2⟩ := h.comp hns
  refine ⟨ms, TendstoInDistribution.tendsto ?_⟩
  exact tendstoInDistribution_of_ae_tendsto (by fun_prop) hZ hms2

中文:
定理 TendstoInMeasure.tendstoInDistribution
  结论: [PseudoEMetric空间 E] [Borel空间 E]
  证明: by
  have hZ := h.aemeasurable hX
  refine ⟨hX, hZ, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
.exists_seq_tendsto_ae' obtain ⟨ms, hms1, hms2⟩ := h.comp hns
  refine ⟨ms, TendstoInDistribution.tendsto ?_⟩
  exact tendstoInDistribution_of_ae_tendsto (by fun_prop) hZ hms2

Depends on / 依赖: Filter, Filter.tendsto_of_subseq_tendsto, TendstoInDistribution, TendstoInDistribution.tendsto, aemeasurable, exists_seq_tendsto_ae, fun_prop, h.aemeasurable, h.comp, tendsto, tendstoInDistribution_of_ae_tendsto, tendsto_of_subseq_tendsto
-/
theorem TendstoInMeasure.tendstoInDistribution [PseudoEMetricSpace E] [BorelSpace E]
    [l.IsCountablyGenerated] [l.NeBot] {X : ι -> Ω' -> E}
    (h : TendstoInMeasure μ' X l Z) (hX : forall i, AEMeasurable (X i) μ') :
    TendstoInDistribution X l Z (fun _ => μ') μ' := by
  have hZ := h.aemeasurable hX
  refine ⟨hX, hZ, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
.exists_seq_tendsto_ae' obtain ⟨ms, hms1, hms2⟩ := h.comp hns
  refine ⟨ms, TendstoInDistribution.tendsto ?_⟩
  exact tendstoInDistribution_of_ae_tendsto (by fun_prop) hZ hms2

variable [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tendstoInDistribution_of_tendstoInMeasure_sub` / 引理 `tendstoInDistribution_of_tendstoInMeasure_sub`

English:
lemma tendstoInDistribution_of_tendstoInMeasure_sub
  statement: {X : ι -> Ω'' -> E}
  proof: by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices forall (F : E -> Real) (hF_bounded : exists (C : Real), forall x y, dist (F x) (F y) <= C)
      (hF_lip : exists L, LipschitzWith L F),
      Tendsto (fun n => ∫ ω, F ω ∂(μ''.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ''.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices forall ε > 0, forallᶠ n in l, |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n))) (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- ` ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x => F (Y n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x => F (X n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a => ‖F (Y n a) - F (X n a)‖) μ'' := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_sub h_int_Y h_int_X]; rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ''‖
    _ <= ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ'' := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ'' := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ <= ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, M ∂μ'' := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx => hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
        rw [← dist_eq_norm]
        convert!
          hF_bounded _
            _
              -- The goal is now a simple computation

    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ''.real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

中文:
引理 tendstoInDistribution_of_tendstoInMeasure_sub
  结论: {X : ι -> Ω'' -> E}
  证明: by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices forall (F : E -> Real) (hF_bounded : exists (C : Real), forall x y, dist (F x) (F y) <= C)
      (hF_lip : exists L, LipschitzWith L F),
      Tendsto (fun n => ∫ ω, F ω ∂(μ''.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ''.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices forall ε > 0, forallᶠ n in l, |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n))) (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- ` ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x => F (Y n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x => F (X n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a => ‖F (Y n a) - F (X n a)‖) μ'' := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_sub h_int_Y h_int_X]; rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ''‖
    _ <= ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ'' := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ'' := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ <= ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, M ∂μ'' := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx => hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
        rw [← dist_eq_norm]
        convert!
          hF_bounded _
            _
              -- The goal is now a simple computation

    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ''.real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

Depends on / 依赖: AEMeasurable, aemeasurable_limit, forall_aemeasurable, hE.some, hXZ.aemeasurable_limit, hXZ.forall_aemeasurable, isEmpty_or_nonempty
-/
lemma tendstoInDistribution_of_tendstoInMeasure_sub {X : ι -> Ω'' -> E}
    [l.IsCountablyGenerated] (Y : ι -> Ω'' -> E) (Z : Ω' -> E)
    (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ') (hXY : TendstoInMeasure μ'' (Y - X) l 0)
    (hY : forall i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution Y l Z (fun _ => μ'') μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices forall (F : E -> Real) (hF_bounded : exists (C : Real), forall x y, dist (F x) (F y) <= C)
      (hF_lip : exists L, LipschitzWith L F),
      Tendsto (fun n => ∫ ω, F ω ∂(μ''.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ''.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices forall ε > 0, forallᶠ n in l, |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n))) (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- ` ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x => F (Y n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x => F (X n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a => ‖F (Y n a) - F (X n a)‖) μ'' := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_sub h_int_Y h_int_X]; rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ''‖
    _ <= ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ'' := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ'' := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ <= ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ''
        + ∫ a in {x | ε / 2 <= ‖Y n x - X n x‖}, M ∂μ'' := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx => hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
        rw [← dist_eq_norm]
        convert!
          hF_bounded _
            _
              -- The goal is now a simple computation

    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ''.real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ <= L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n => L * (ε / 2) + M * μ''.real {ω | ε / 2 <= ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/--
lemma `TendstoInMeasure.tendstoInDistribution_of_aemeasurable` / 引理 `TendstoInMeasure.tendstoInDistribution_of_aemeasurable`

English:
lemma TendstoInMeasure.tendstoInDistribution_of_aemeasurable
  statement: [l.IsCountablyGenerated]
  proof: tendstoInDistribution_of_tendstoInMeasure_sub X Z (tendstoInDistribution_const hZ)
    (by simpa [tendstoInMeasure_iff_norm] using h) hX

中文:
引理 TendstoInMeasure.tendstoInDistribution_of_aemeasurable
  结论: [l.是余untablyGenerated]
  证明: tendstoInDistribution_of_tendstoInMeasure_sub X Z (tendstoInDistribution_const hZ)
    (by simpa [tendstoInMeasure_iff_norm] using h) hX

Depends on / 依赖: tendstoInDistribution_const, tendstoInDistribution_of_tendstoInMeasure_sub, tendstoInMeasure_iff_norm
-/
lemma TendstoInMeasure.tendstoInDistribution_of_aemeasurable [l.IsCountablyGenerated]
    {X : ι -> Ω' -> E} (h : TendstoInMeasure μ' X l Z) (hX : forall i, AEMeasurable (X i) μ')
    (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z (fun _ => μ') μ' :=
  tendstoInDistribution_of_tendstoInMeasure_sub X Z (tendstoInDistribution_const hZ)
    (by simpa [tendstoInMeasure_iff_norm] using h) hX

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `TendstoInDistribution.prodMk_of_tendstoInMeasure_const` / 定理 `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`

English:
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
  proof: by
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω => (X n ω, c))
    (fun n ω => (X n ω, Y n ω)) (fun ω => (Z ω, c)) ?_ ?_ (fun i => (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x => (x, c)) (by fun_prop)
  · suffices TendstoInMeasure μ'' (fun n ω => ((0 : E), Y n ω - c)) l 0 by
      convert! this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

中文:
定理 TendstoInDistribution.prodMk_of_tendstoInMeasure_const
  证明: by
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω => (X n ω, c))
    (fun n ω => (X n ω, Y n ω)) (fun ω => (Z ω, c)) ?_ ?_ (fun i => (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x => (x, c)) (by fun_prop)
  · suffices TendstoInMeasure μ'' (fun n ω => ((0 : E), Y n ω - c)) l 0 by
      convert! this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

Depends on / 依赖: AEMeasurable, TendstoInMeasure, continuous_comp, convert, forall_aemeasurable, fun_prop, hXZ.continuous_comp, hXZ.forall_aemeasurable, hY_meas, prodMk, tendstoInDistribution_of_tendstoInMeasure_sub, tendstoInMeasure_iff_norm
-/
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    {E' : Type*} {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [l.IsCountablyGenerated] (X : ι -> Ω'' -> E) (Y : ι -> Ω'' -> E') (Z : Ω' -> E)
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ => c))
    (hY_meas : forall i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω => (X n ω, Y n ω)) l (fun ω => (Z ω, c)) (fun _ => μ'') μ' := by
  have hX : forall i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω => (X n ω, c))
    (fun n ω => (X n ω, Y n ω)) (fun ω => (Z ω, c)) ?_ ?_ (fun i => (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x => (x, c)) (by fun_prop)
  · suffices TendstoInMeasure μ'' (fun n ω => ((0 : E), Y n ω - c)) l 0 by
      convert! this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

/--
theorem `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const` / 定理 `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`

English:
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
  statement: {E' F : Type*}
  proof: by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto hY

中文:
定理 TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
  结论: {E' F : 类型}
  证明: by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto hY

Depends on / 依赖: TendstoInDistribution, TendstoInDistribution.continuous_comp, continuous_comp, hXZ.prodMk_of_tendstoInMeasure_const, hY_tendsto, prodMk_of_tendstoInMeasure_const
-/
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const {E' F : Type*}
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E × E' -> F} (hg : Continuous g)
    [l.IsCountablyGenerated] {X : ι -> Ω'' -> E} {Y : ι -> Ω'' -> E'}
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ => c))
    (hY : forall i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω => g (X n ω, Y n ω)) l (fun ω => g (Z ω, c)) (fun _ => μ'') μ' := by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto hY

/--
lemma `TendstoInDistribution.add_of_tendstoInMeasure_const` / 引理 `TendstoInDistribution.add_of_tendstoInMeasure_const`

English:
lemma TendstoInDistribution.add_of_tendstoInMeasure_const
  statement: {X Y : ι -> Ω'' -> E}
  proof: hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) => x.1 + x.2) (by fun_prop) hY_tendsto hY

中文:
引理 TendstoInDistribution.add_of_tendstoInMeasure_const
  结论: {X Y : ι -> Ω'' -> E}
  证明: hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) => x.1 + x.2) (by fun_prop) hY_tendsto hY

Depends on / 依赖: continuous_comp_prodMk_of_tendstoInMeasure_const, fun_prop, hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const, hY_tendsto
-/
lemma TendstoInDistribution.add_of_tendstoInMeasure_const {X Y : ι -> Ω'' -> E}
    [l.IsCountablyGenerated] {c : E} (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ => c)) (hY : forall i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n => X n + Y n) l (fun ω => Z ω + c) (fun _ => μ'') μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) => x.1 + x.2) (by fun_prop) hY_tendsto hY

end MeasureTheory
