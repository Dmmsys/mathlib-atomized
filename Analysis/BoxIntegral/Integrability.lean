/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# McShane integrability vs Bochner integrability

In this file we prove that any Bochner integrable function is McShane integrable (hence, it is
Henstock and `GP` integrable) with the same integral. The proof is based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

We deduce that the same is true for the Riemann integral for continuous functions.

## Tags

integral, McShane integral, Bochner integral
-/

public section

open scoped NNReal ENNReal Topology

universe u v

variable {ι : Type u} {E : Type v} [Fintype ι] [NormedAddCommGroup E] [NormedSpace Real E]

open MeasureTheory Metric Set Finset Filter BoxIntegral

namespace BoxIntegral

set_option backward.defeqAttrib.useBackward true in
/--
theorem `hasIntegralIndicatorConst` / 定理 `hasIntegralIndicatorConst`

English:
theorem hasIntegralIndicatorConst
  statement: (l : IntegrationParams) (hl : l.bRiemann = false)
  proof: by
  refine HasIntegral.of_mul ‖y‖ fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le; rw [NNReal.coe_pos] at ε0
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
    both `(s ∩ I.Icc) \ F` and `U \ s` have measure less than `ε`. -/
  have A : μ (s inter Box.Icc I) != ∞

中文:
定理 has整数egralIndicatorConst
  结论: (l : 整数egrationParams) (hl : l.bRiemann = false)
  证明: by
  refine HasIntegral.of_mul ‖y‖ fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le; rw [NNReal.coe_pos] at ε0
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
    both `(s ∩ I.Icc) \ F` and `U \ s` have measure less than `ε`. -/
  have A : μ (s inter Box.Icc I) != ∞

Depends on / 依赖: HasIntegral, HasIntegral.of_mul, NNReal, NNReal.coe_pos, coe_pos, of_mul
-/
theorem hasIntegralIndicatorConst (l : IntegrationParams) (hl : l.bRiemann = false)
    {s : Set (ι -> Real)} (hs : MeasurableSet s) (I : Box ι) (y : E) (μ : Measure (ι -> Real))
    [IsLocallyFiniteMeasure μ] :
    HasIntegral.{u, v, v} I l (s.indicator fun _ => y) μ.toBoxAdditive.toSMul
      (μ.real (s inter I) • y) := by
  refine HasIntegral.of_mul ‖y‖ fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le; rw [NNReal.coe_pos] at ε0
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
    both `(s ∩ I.Icc) \ F` and `U \ s` have measure less than `ε`. -/
  have A : μ (s inter Box.Icc I) != ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_Icc_lt_top μ)).ne
  have B : μ (s inter I) != ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_coe_lt_top μ)).ne
  obtain ⟨F, hFs, hFc, hμF⟩ : exists F, F subseteq s inter Box.Icc I ∧ IsClosed F ∧ μ ((s inter Box.Icc I) \ F) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isClosed_sdiff_lt A (ENNReal.coe_pos.2 ε0).ne'
  obtain ⟨U, hsU, hUo, hUt, hμU⟩ :
      exists U, s inter Box.Icc I subseteq U ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ (s inter Box.Icc I)) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isOpen_sdiff_lt A (ENNReal.coe_pos.2 ε0).ne'
  /- Then we choose `r` so that `closed_ball x (r x) ⊆ U` whenever `x ∈ s ∩ I.Icc` and
    `closed_ball x (r x)` is disjoint with `F` otherwise. -/
  have : forall x in s inter Box.Icc I, exists r : Ioi (0 : Real), closedBall x r subseteq U := fun x hx => by
    rcases nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds <| hsU hx) with ⟨r, hr₀, hr⟩
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs hrsU using this
  have : forall x in Box.Icc I \ s, exists r : Ioi (0 : Real), closedBall x r subseteq Fᶜ := fun x hx => by
    obtain ⟨r, hr₀, hr⟩ :=
      nhds_basis_closedBall.mem_iff.1 (hFc.isOpen_compl.mem_nhds fun hx' => hx.2 (hFs hx').1)
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs' hrs'F using this
  classical
  set r : (ι -> Real) -> Ioi (0 : Real) := s.piecewise rs rs'
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩; rw [mul_comm]
  /- Then the union of boxes `J ∈ π` such that `π.tag ∈ s` includes `F` and is included by `U`,
    hence its measure is `ε`-close to the measure of `s`. -/
  dsimp [integralSum]
  simp only [dist_eq_norm, ← indicator_const_smul_apply, sum_indicator_eq_sum_filter, ← sum_smul,
    ← sub_smul, norm_smul, Real.norm_eq_abs, ← Prepartition.filter_boxes,
    ← Prepartition.measure_iUnion_toReal]
  gcongr
  set t := (π.filter (π.tag · in s)).iUnion
  change abs (μ.real t - μ.real (s inter I)) <= ε
  have htU : t subseteq U inter I := by
    simp only [t, TaggedPrepartition.iUnion_def, iUnion_subset_iff, TaggedPrepartition.mem_filter,
      and_imp]
    refine fun J hJ hJs x hx => ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩ ?_, π.le_of_mem' J hJ hx⟩
    simpa only [r, s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (Box.coe_subset_Icc hx)
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · refine (ENNReal.le_toReal_sub B).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_sdiff.trans ?_)
    refine (measure_mono fun x hx => ?_).trans hμU.le
    exact ⟨hx.1.1, fun hx' => hx.2 ⟨hx'.1, hx.1.2⟩⟩
  · have hμt : μ t != ∞ := ((measure_mono (htU.trans inter_subset_left)).trans_lt hUt).ne
    refine (ENNReal.le_toReal_sub hμt).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine le_measure_sdiff.trans ((measure_mono ?_).trans hμF.le)
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩
    refine ⟨⟨hxs, Box.coe_subset_Icc hxI⟩, fun hxF => hxt ?_⟩
    simp only [t, TaggedPrepartition.iUnion_def, TaggedPrepartition.mem_filter, Set.mem_iUnion]
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩
    refine ⟨J, ⟨hJπ, ?_⟩, hxJ⟩
    contrapose hxF
    refine hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ ?_
    simpa only [r, s.piecewise_eq_of_notMem _ _ hxF] using hπ.1 J hJπ (Box.coe_subset_Icc hxJ)

/--
theorem `HasIntegral.of_aeEq_zero` / 定理 `HasIntegral.of_aeEq_zero`

English:
theorem HasIntegral.of_aeEq_zero
  statement: {l : IntegrationParams} {I : Box ι} {f : (ι -> Real) -> E}
  proof: by
  /- Each set `{x | n < ‖f x‖ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
    measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine hasIntegral_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.lt.le; rw [gt_iff_lt, NNReal

中文:
定理 Has整数egral.of_aeEq_zero
  结论: {l : 整数egrationParams} {I : Box ι} {f : (ι -> 实数) -> E}
  证明: by
  /- Each set `{x | n < ‖f x‖ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
    measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine hasIntegral_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.lt.le; rw [gt_iff_lt, NNReal
-/
theorem HasIntegral.of_aeEq_zero {l : IntegrationParams} {I : Box ι} {f : (ι -> Real) -> E}
    {μ : Measure (ι -> Real)} [IsLocallyFiniteMeasure μ] (hf : f =ᵐ[μ.restrict I] 0)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul 0 := by
  /- Each set `{x | n < ‖f x‖ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
    measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine hasIntegral_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.lt.le; rw [gt_iff_lt, NNReal.coe_pos] at ε0
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' Nat with ⟨δ, δ0, c, hδc, hcε⟩
  have := Fact.mk (I.measure_coe_lt_top μ)
  change μ.restrict I {x | f x != 0} = 0 at hf
  set N : (ι -> Real) -> Nat := fun x => ⌈‖f x‖⌉₊
  have N0 : forall {x}, N x = 0 ↔ f x = 0 := by simp [N]
  have : forall n, exists U, N ⁻¹' {n} subseteq U ∧ IsOpen U ∧ μ.restrict I U < δ n / n := fun n => by
    refine (N ⁻¹' {n}).exists_isOpen_lt_of_lt _ ?_
    rcases n with - | n
    · simp [ENNReal.div_zero (ENNReal.coe_pos.2 (δ0 _)).ne']
    · refine (measure_mono_null ?_ hf).le.trans_lt ?_
      · exact fun x hxN hxf => n.succ_ne_zero ((Eq.symm hxN).trans <| N0.2 hxf)
      · simp [(δ0 _).ne']
  choose U hNU hUo hμU using this
  have : forall x, exists r : Ioi (0 : Real), closedBall x r subseteq U (N x) := fun x => by
    obtain ⟨r, hr₀, hr⟩ := nhds_basis_closedBall.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl))
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose r hrU using this
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ _ => ?_⟩
  rw [dist_eq_norm]; rw [sub_zero]; rw [← integralSum_fiberwise fun J => N (π.tag J)]
  grw [← hcε, ← sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc)]
  apply norm_sum_le_of_le
  rintro n -
  dsimp [integralSum]
  have : forall J in π.filter fun J => N (π.tag J) = n,
      ‖μ.real ↑J • f (π.tag J)‖ <= μ.real J * n := fun J hJ => by
    rw [TaggedPrepartition.mem_filter] at hJ
    rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg measureReal_nonneg]
    gcongr
    exact hJ.2 ▸ Nat.le_ceil _
  refine (norm_sum_le_of_le _ this).trans ?_; clear this
  rw [← sum_mul]; rw [← Prepartition.measure_iUnion_toReal]
  let m := μ (π.filter fun J => N (π.tag J) = n).iUnion
  change m.toReal * ↑n <= ↑(δ n)
  have : m < δ n / n := by
    simp only [Measure.restrict_apply (hUo _).measurableSet] at hμU
    refine (measure_mono ?_).trans_lt (hμU _)
    simp only [Set.subset_def, TaggedPrepartition.mem_iUnion, TaggedPrepartition.mem_filter]
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩
    exact ⟨hrU _ (hπ.1 _ hJ (Box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩
  clear_value m
  lift m to Real>=0 using ne_top_of_lt this
  grw [ENNReal.coe_toReal, ← NNReal.coe_natCast, ← NNReal.coe_mul, NNReal.coe_le_coe, ←
    ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm, this, ENNReal.mul_div_le]

/--
theorem `HasIntegral.congr_ae` / 定理 `HasIntegral.congr_ae`

English:
theorem HasIntegral.congr_ae
  statement: {l : IntegrationParams} {I : Box ι} {y : E} {f g : (ι -> Real) -> E}
  proof: by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (HasIntegral.of_aeEq_zero this hl)

中文:
定理 Has整数egral.congr_ae
  结论: {l : 整数egrationParams} {I : Box ι} {y : E} {f g : (ι -> 实数) -> E}
  证明: by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (HasIntegral.of_aeEq_zero this hl)

Depends on / 依赖: HasIntegral, HasIntegral.of_aeEq_zero, hf.add, hfg.mono, hx.symm, of_aeEq_zero, restrict, sub_eq_zero
-/
theorem HasIntegral.congr_ae {l : IntegrationParams} {I : Box ι} {y : E} {f g : (ι -> Real) -> E}
    {μ : Measure (ι -> Real)} [IsLocallyFiniteMeasure μ]
    (hf : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul y) (hfg : f =ᵐ[μ.restrict I] g)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l g μ.toBoxAdditive.toSMul y := by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (HasIntegral.of_aeEq_zero this hl)

end BoxIntegral

namespace MeasureTheory

namespace SimpleFunc

/--
theorem `hasBoxIntegral` / 定理 `hasBoxIntegral`

English:
theorem hasBoxIntegral
  statement: (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ]
  proof: by
  induction f using MeasureTheory.SimpleFunc.induction with
  | @const y s hs =>
    simpa [hs] using! BoxIntegral.hasIntegralIndicatorConst l hl hs I y μ
  | @add f g _ hfi hgi =>
    borelize E; have := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts [hfi.add hgi, integrable_i

中文:
定理 hasBox整数egral
  结论: (f : SimpleFunc (ι -> 实数) E) (μ : 测度 (ι -> 实数)) [是局部有限测度 μ]
  证明: by
  induction f using MeasureTheory.SimpleFunc.induction with
  | @const y s hs =>
    simpa [hs] using! BoxIntegral.hasIntegralIndicatorConst l hl hs I y μ
  | @add f g _ hfi hgi =>
    borelize E; have := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts [hfi.add hgi, integrable_i

Depends on / 依赖: BoxIntegral, BoxIntegral.hasIntegralIndicatorConst, Fact.mk, I.measure_coe_lt_top, MeasureTheory, MeasureTheory.SimpleFunc.induction, SimpleFunc, borelize, exacts, hasIntegralIndicatorConst, hfi.add, integrable_iff, integral_add, measure_coe_lt_top, measure_lt_top
-/
theorem hasBoxIntegral (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (f.integral (μ.restrict I)) := by
  induction f using MeasureTheory.SimpleFunc.induction with
  | @const y s hs =>
    simpa [hs] using! BoxIntegral.hasIntegralIndicatorConst l hl hs I y μ
  | @add f g _ hfi hgi =>
    borelize E; have := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts [hfi.add hgi, integrable_iff.2 fun _ _ => measure_lt_top _ _,
      integrable_iff.2 fun _ _ => measure_lt_top _ _]

/--
theorem `box_integral_eq_integral` / 定理 `box_integral_eq_integral`

English:
theorem box_integral_eq_integral
  statement: (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι -> Real))
  proof: (f.hasBoxIntegral μ I l hl).integral_eq

中文:
定理 box_integral_eq_integral
  结论: (f : SimpleFunc (ι -> 实数) E) (μ : 测度 (ι -> 实数))
  证明: (f.hasBoxIntegral μ I l hl).integral_eq

Depends on / 依赖: f.hasBoxIntegral, hasBoxIntegral, integral_eq
-/
theorem box_integral_eq_integral (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι -> Real))
    [IsLocallyFiniteMeasure μ] (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul = f.integral (μ.restrict I) :=
  (f.hasBoxIntegral μ I l hl).integral_eq

end SimpleFunc

open TopologicalSpace

set_option backward.defeqAttrib.useBackward true in
/--
theorem `IntegrableOn.hasBoxIntegral` / 定理 `IntegrableOn.hasBoxIntegral`

English:
theorem IntegrableOn.hasBoxIntegral
  statement: [CompleteSpace E] {f : (ι -> Real) -> E} {μ : Measure (ι -> Real)}
  proof: by
  borelize E
  -- First we replace an `ae_strongly_measurable` function by a measurable one.
  rcases hf.aestronglyMeasurable with ⟨g, hg, hfg⟩
  have : SeparableSpace (range g union {0} : Set E) := hg.separableSpace_range_union_singleton
  rw [integral_congr_ae hfg]; have hgi : IntegrableOn g I 

中文:
定理 整数egrableOn.hasBox整数egral
  结论: [完备空间 E] {f : (ι -> 实数) -> E} {μ : 测度 (ι -> 实数)}
  证明: by
  borelize E
  -- First we replace an `ae_strongly_measurable` function by a measurable one.
  rcases hf.aestronglyMeasurable with ⟨g, hg, hfg⟩
  have : SeparableSpace (range g union {0} : Set E) := hg.separableSpace_range_union_singleton
  rw [integral_congr_ae hfg]; have hgi : IntegrableOn g I 

Depends on / 依赖: borelize
-/
theorem IntegrableOn.hasBoxIntegral [CompleteSpace E] {f : (ι -> Real) -> E} {μ : Measure (ι -> Real)}
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hf : IntegrableOn f I μ) (l : IntegrationParams)
    (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  borelize E
  -- First we replace an `ae_strongly_measurable` function by a measurable one.
  rcases hf.aestronglyMeasurable with ⟨g, hg, hfg⟩
  have : SeparableSpace (range g union {0} : Set E) := hg.separableSpace_range_union_singleton
  rw [integral_congr_ae hfg]; have hgi : IntegrableOn g I μ := (integrable_congr hfg).1 hf
  refine BoxIntegral.HasIntegral.congr_ae ?_ hfg.symm hl
  clear! f
  /- Now consider the sequence of simple functions
    `SimpleFunc.approxOn g hg.measurable (range g ∪ {0}) 0 (by simp)`
    approximating `g`. Recall some properties of this sequence. -/
  set f : Nat -> SimpleFunc (ι -> Real) E :=
    SimpleFunc.approxOn g hg.measurable (range g union {0}) 0 (by simp)
  have hfi : forall n, IntegrableOn (f n) I μ :=
    SimpleFunc.integrable_approxOn_range hg.measurable hgi
  have hfi' := fun n => ((f n).hasBoxIntegral μ I l hl).integrable
  have hfg_mono : forall (x) {m n}, m <= n -> ‖f n x - g x‖ <= ‖f m x - g x‖ := by
    intro x m n hmn
    rw [← dist_eq_norm]; rw [← dist_eq_norm]; rw [dist_nndist]; rw [dist_nndist]; rw [NNReal.coe_le_coe]; rw [←
      ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [← edist_nndist]
    exact SimpleFunc.edist_approxOn_mono hg.measurable _ x hmn
  /- Now consider `ε > 0`. We need to find `r` such that for any tagged partition subordinate
    to `r`, the integral sum is `(μ I + 1 + 1) * ε`-close to the Bochner integral. -/
  refine HasIntegral.of_mul (μ.real I + 1 + 1) fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le; rw [NNReal.coe_pos] at ε0; have ε0' := ENNReal.coe_pos.2 ε0
  -- Choose `N` such that the integral of `‖f N x - g x‖` is less than or equal to `ε`.
  obtain ⟨N₀, hN₀⟩ : exists N : Nat, ∫ x in I, ‖f N x - g x‖ ∂μ <= ε := by
    have : Tendsto (fun n => ∫⁻ x in I, ‖f n x - g x‖₊ ∂μ) atTop (𝓝 0) :=
      SimpleFunc.tendsto_approxOn_range_L1_enorm hg.measurable hgi
    refine (this.eventually (ge_mem_nhds ε0')).exists.imp fun N hN => ?_
    exact integral_coe_le_of_lintegral_coe_le hN
  -- For each `x`, we choose `Nx x ≥ N₀` such that `dist (f Nx x) (g x) ≤ ε`.
  have : forall x, exists N₁, N₀ <= N₁ ∧ dist (f N₁ x) (g x) <= ε := fun x => by
    have : Tendsto (f · x) atTop (𝓝 <| g x) :=
      SimpleFunc.tendsto_approxOn hg.measurable _ (subset_closure (by simp))
    exact ((eventually_ge_atTop N₀).and <| this <| closedBall_mem_nhds _ ε0).exists
  choose Nx hNx hNxε using this
  -- We also choose a convergent series with `∑' i : ℕ, δ i < ε`.
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' Nat with ⟨δ, δ0, c, hδc, hcε⟩
  /- Since each simple function `fᵢ` is integrable, there exists `rᵢ : ℝⁿ → (0, ∞)` such that
    the integral sum of `f` over any tagged prepartition is `δᵢ`-close to the sum of integrals
    of `fᵢ` over the boxes of this prepartition. For each `x`, we choose `r (Nx x)` as the radius
    at `x`. -/
  set r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) := fun c x => (hfi' <| Nx x).convergenceR (δ <| Nx x) c x
  refine ⟨r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩
  /- Now we prove the estimate in 3 "jumps": first we replace `g x` in the formula for the
    integral sum by `f (Nx x)`; then we replace each `μ J • f (Nx (π.tag J)) (π.tag J)`
    by the Bochner integral of `f (Nx (π.tag J)) x` over `J`, then we jump to the Bochner
    integral of `g`. -/
  refine (dist_triangle4 _ (∑ J in π.boxes, μ.real J • f (Nx <| π.tag J) (π.tag J))
    (∑ J in π.boxes, ∫ x in J, f (Nx <| π.tag J) x ∂μ) _).trans ?_
  rw [add_mul]; rw [add_mul]; rw [one_mul]
  refine add_le_add_three ?_ ?_ ?_
  · /- Since each `f (Nx <| π.tag J)` is `ε`-close to `g (π.tag J)`, replacing the latter with
        the former in the formula for the integral sum changes the sum at most by `μ I * ε`. -/
    rw [← hπp.iUnion_eq]; rw [π.measure_iUnion_toReal]; rw [sum_mul]; rw [integralSum]
    refine dist_sum_sum_le_of_le _ fun J _ => ?_; dsimp
    rw [dist_eq_norm]; rw [← smul_sub]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg measureReal_nonneg]
    gcongr
    rw [← dist_eq_norm']; exact hNxε _
  · /- We group the terms of both sums by the values of `Nx (π.tag J)`.
        For each `N`, the sum of Bochner integrals over the boxes is equal
        to the sum of box integrals, and the sum of box integrals is `δᵢ`-close
        to the corresponding integral sum due to the Henstock-Sacks inequality. -/
    rw [← π.sum_fiberwise fun J => Nx (π.tag J)]; rw [← π.sum_fiberwise fun J => Nx (π.tag J)]
    grw [← hcε]
    refine
      (dist_sum_sum_le_of_le _ fun n hn => ?_).trans
        (sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc))
    have hNxn : forall J in π.filter fun J => Nx (π.tag J) = n, Nx (π.tag J) = n := fun J hJ =>
      (π.mem_filter.1 hJ).2
    have hrn : forall J in π.filter fun J => Nx (π.tag J) = n,
        r c (π.tag J) = (hfi' n).convergenceR (δ n) c (π.tag J) := fun J hJ => by
      obtain rfl := hNxn J hJ
      rfl
    have :
        l.MemBaseSet I c ((hfi' n).convergenceR (δ n) c) (π.filter fun J => Nx (π.tag J) = n) :=
      (hπ.filter _).mono' _ le_rfl le_rfl fun J hJ => (hrn J hJ).le
    convert! (hfi' n).dist_integralSum_sum_integral_le_of_memBaseSet (δ0 _) this using 2
    · refine sum_congr rfl fun J hJ => ?_
      simp [hNxn J hJ]
    · refine sum_congr rfl fun J hJ => ?_
      rw [← SimpleFunc.integral_eq_integral]; rw [SimpleFunc.box_integral_eq_integral _ _ _ _ hl]; rw [hNxn J hJ]
      exact (hfi _).mono_set (Prepartition.le_of_mem _ hJ)
  · /- For the last jump, we use the fact that the distance between `f (Nx x) x` and `g x` is less
        than or equal to the distance between `f N₀ x` and `g x` and the integral of
        `‖f N₀ x - g x‖` is less than or equal to `ε`. -/
    refine le_trans ?_ hN₀
    have hfi : forall (n), forall J in π, IntegrableOn (f n) (↑J) μ := fun n J hJ =>
      (hfi n).mono_set (π.le_of_mem' J hJ)
    have hgi : forall J in π, IntegrableOn g (↑J) μ := fun J hJ => hgi.mono_set (π.le_of_mem' J hJ)
    have hfgi : forall (n), forall J in π, IntegrableOn (fun x => ‖f n x - g x‖) J μ := fun n J hJ =>
      ((hfi n J hJ).sub (hgi J hJ)).norm
    rw [← hπp.iUnion_eq]; rw [Prepartition.iUnion_def']; rw [integral_biUnion_finset π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint hgi]; rw [integral_biUnion_finset π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint (hfgi _)]
    refine dist_sum_sum_le_of_le _ fun J hJ => ?_
    rw [dist_eq_norm]; rw [← integral_sub (hfi _ J hJ) (hgi J hJ)]
    refine norm_integral_le_of_norm_le (hfgi _ J hJ) (Eventually.of_forall fun x => ?_)
    exact hfg_mono x (hNx (π.tag J))

/--
theorem `ContinuousOn.hasBoxIntegral` / 定理 `ContinuousOn.hasBoxIntegral`

English:
theorem ContinuousOn.hasBoxIntegral
  statement: [CompleteSpace E] {f : (ι -> Real) -> E} (μ : Measure (ι -> Real))
  proof: by
  obtain ⟨y, hy⟩ := BoxIntegral.integrable_of_continuousOn l hc μ
  convert! hy
  have : IntegrableOn f I μ :=
    IntegrableOn.mono_set (hc.integrableOn_compact I.isCompact_Icc) Box.coe_subset_Icc
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)

中文:
定理 ContinuousOn.hasBox整数egral
  结论: [完备空间 E] {f : (ι -> 实数) -> E} (μ : 测度 (ι -> 实数))
  证明: by
  obtain ⟨y, hy⟩ := BoxIntegral.integrable_of_continuousOn l hc μ
  convert! hy
  have : IntegrableOn f I μ :=
    IntegrableOn.mono_set (hc.integrableOn_compact I.isCompact_Icc) Box.coe_subset_Icc
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)

Depends on / 依赖: Box.coe_subset_Icc, BoxIntegral, BoxIntegral.integrable_of_continuousOn, HasIntegral, HasIntegral.mono, HasIntegral.unique, I.isCompact_Icc, IntegrableOn, IntegrableOn.hasBoxIntegral, IntegrableOn.mono_set, bot_le, coe_subset_Icc, convert, hasBoxIntegral, hc.integrableOn_compact, integrableOn_compact, integrable_of_continuousOn, isCompact_Icc, mono_set, unique
-/
theorem ContinuousOn.hasBoxIntegral [CompleteSpace E] {f : (ι -> Real) -> E} (μ : Measure (ι -> Real))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hc : ContinuousOn f (Box.Icc I))
    (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := BoxIntegral.integrable_of_continuousOn l hc μ
  convert! hy
  have : IntegrableOn f I μ :=
    IntegrableOn.mono_set (hc.integrableOn_compact I.isCompact_Icc) Box.coe_subset_Icc
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)

/--
theorem `AEContinuous.hasBoxIntegral` / 定理 `AEContinuous.hasBoxIntegral`

English:
theorem AEContinuous.hasBoxIntegral
  statement: [CompleteSpace E] {f : (ι -> Real) -> E} (μ : Measure (ι -> Real))
  proof: by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert! hy
  refine HasIntegral.unique (IntegrableOn.hasBoxIntegral ?_ ⊥ rfl) (HasIntegral.mono hy bot_le)
  constructor
  · let v := {x : (ι -> Real) | ContinuousAt f x}
    have : AEStronglyMeasurable f (μ.restrict v) :=
 

中文:
定理 AEContinuous.hasBox整数egral
  结论: [完备空间 E] {f : (ι -> 实数) -> E} (μ : 测度 (ι -> 实数))
  证明: by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert! hy
  refine HasIntegral.unique (IntegrableOn.hasBoxIntegral ?_ ⊥ rfl) (HasIntegral.mono hy bot_le)
  constructor
  · let v := {x : (ι -> Real) | ContinuousAt f x}
    have : AEStronglyMeasurable f (μ.restrict v) :=
 

Depends on / 依赖: AEStronglyMeasurable, ContinuousAt, HasIntegral, HasIntegral.mono, HasIntegral.unique, IntegrableOn, IntegrableOn.hasBoxIntegral, Measure, Measure.le_iff, aestronglyMeasurable, bot_le, continuousOn_of_forall_continuousAt, convert, hasBoxIntegral, integrable_of_bounded_and_ae_continuous, le_iff, le_of_le_of_, measurableSet_of_continuousAt, mono_measure, repeat
-/
theorem AEContinuous.hasBoxIntegral [CompleteSpace E] {f : (ι -> Real) -> E} (μ : Measure (ι -> Real))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hb : exists C : Real, forall x in Box.Icc I, ‖f x‖ <= C)
    (hc : forallᵐ x ∂μ, ContinuousAt f x) (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert! hy
  refine HasIntegral.unique (IntegrableOn.hasBoxIntegral ?_ ⊥ rfl) (HasIntegral.mono hy bot_le)
  constructor
  · let v := {x : (ι -> Real) | ContinuousAt f x}
    have : AEStronglyMeasurable f (μ.restrict v) :=
      (continuousOn_of_forall_continuousAt fun _ h => h).aestronglyMeasurable
      (measurableSet_of_continuousAt f)
    refine this.mono_measure (Measure.le_iff.2 fun s hs => ?_)
    repeat rw [μ.restrict_apply hs]
apply le_of_le_of_eq μ.mono s.inter_subset_left
.symm refine measure_eq_measure_of_null_sdiff s.inter_subset_left ?_
    rw [sdiff_self_inter]; rw [Set.sdiff_eq]; rw [← nonpos_iff_eq_zero]
    grw [s.inter_subset_right]
    exact hc.le
  · have : IsFiniteMeasure (μ.restrict (Box.Icc I)) :=
      { measure_univ_lt_top := by simp [I.isCompact_Icc.measure_lt_top (μ := μ)] }
    have : IsFiniteMeasure (μ.restrict I) :=
      isFiniteMeasure_of_le _ (μ.restrict_mono Box.coe_subset_Icc le_rfl)
    obtain ⟨C, hC⟩ := hb
    refine .of_bounded (C := C) (Filter.eventually_iff_exists_mem.2 ?_)
    use I, self_mem_ae_restrict I.measurableSet_coe, fun y hy => hC y (I.coe_subset_Icc hy)

end MeasureTheory
