/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which establishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales and most notably is used to
formulate the martingale convergence theorem.

## Main definitions

* `MeasureTheory.UnifIntegrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted to `s` is smaller than `ε` for all `i`.
* `MeasureTheory.UniformIntegrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

## Main results

* `MeasureTheory.unifIntegrable_finite`: a finite sequence of Lp functions is uniformly
  integrable.
* `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniformly integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

/--
Definition of `UnifIntegrable` / `UnifIntegrable` 的定义

English:
definition UnifIntegrable
  signature: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α)
  body: forall ⦃ε : Real⦄ (_ : 0 < ε), exists (δ : Real) (_ : 0 < δ), forall i s,
    MeasurableSet s -> μ s <= ENNReal.ofReal δ -> eLpNorm (s.indicator (f i)) p μ <= ENNReal.ofReal ε

中文:
定义 Unif整数egrable
  签名: {_ : 可测空间 α} (f : ι -> α -> β) (p : 实数>=0∞) (μ : 测度 α)
  定义体: forall ⦃ε : Real⦄ (_ : 0 < ε), exists (δ : Real) (_ : 0 < δ), forall i s,
    MeasurableSet s -> μ s <= ENNReal.ofReal δ -> eLpNorm (s.indicator (f i)) p μ <= ENNReal.ofReal ε

Depends on / 依赖: ENNReal, ENNReal.ofReal, MeasurableSet, eLpNorm, indicator, ofReal, s.indicator
-/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α) : Prop :=
  forall ⦃ε : Real⦄ (_ : 0 < ε), exists (δ : Real) (_ : 0 < δ), forall i s,
    MeasurableSet s -> μ s <= ENNReal.ofReal δ -> eLpNorm (s.indicator (f i)) p μ <= ENNReal.ofReal ε

/--
Definition of `UniformIntegrable` / `UniformIntegrable` 的定义

English:
definition UniformIntegrable
  signature: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α)
  body: (forall i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ exists C : Real>=0, forall i, eLpNorm (f i) p μ <= C

中文:
定义 Uniform整数egrable
  签名: {_ : 可测空间 α} (f : ι -> α -> β) (p : 实数>=0∞) (μ : 测度 α)
  定义体: (forall i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ exists C : Real>=0, forall i, eLpNorm (f i) p μ <= C

Depends on / 依赖: AEStronglyMeasurable, UnifIntegrable, eLpNorm
-/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α) : Prop :=
  (forall i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ exists C : Real>=0, forall i, eLpNorm (f i) p μ <= C

namespace UniformIntegrable

/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  statement: {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ)
  proof: hf.1 i

中文:
定理 aestronglyMeasurable
  结论: {f : ι -> α -> β} {p : 实数>=0∞} (hf : Uniform整数egrable f p μ)
  证明: hf.1 i
-/
protected theorem aestronglyMeasurable {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ)
    (i : ι) : AEStronglyMeasurable (f i) μ :=
  hf.1 i

/--
theorem `unifIntegrable` / 定理 `unifIntegrable`

English:
theorem unifIntegrable
  given: {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ)
  proof: hf.2.1

中文:
定理 unif整数egrable
  条件: {f : ι -> α -> β} {p : 实数>=0∞} (hf : Uniform整数egrable f p μ)
  证明: hf.2.1
-/
protected theorem unifIntegrable {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ) :
    UnifIntegrable f p μ :=
  hf.2.1

/--
theorem `memLp` / 定理 `memLp`

English:
theorem memLp
  given: {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ) (i : ι)
  proof: ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) ENNReal.coe_lt_top⟩

中文:
定理 memLp
  条件: {f : ι -> α -> β} {p : 实数>=0∞} (hf : Uniform整数egrable f p μ) (i : ι)
  证明: ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) ENNReal.coe_lt_top⟩
-/
protected theorem memLp {f : ι -> α -> β} {p : Real>=0∞} (hf : UniformIntegrable f p μ) (i : ι) :
    MemLp (f i) p μ :=
  ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) ENNReal.coe_lt_top⟩

end UniformIntegrable

section UnifIntegrable

/-! ### `UnifIntegrable`

This section deals with uniform integrability in the measure theory sense. -/


namespace UnifIntegrable

variable {f g : ι -> α -> β} {p : Real>=0∞}

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 <= p)
  proof: by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun i s hs hμs => ?_⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine (eLpNorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans ?_
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le]; rw [add_halves]
  rw [hε_halves]
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))

中文:
定理 add
  结论: (hf : Unif整数egrable f p μ) (hg : Unif整数egrable g p μ) (hp : 1 <= p)
  证明: by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun i s hs hμs => ?_⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine (eLpNorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans ?_
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le]; rw [add_halves]
  rw [hε_halves]
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
-/
protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 <= p)
    (hf_meas : forall i, AEStronglyMeasurable (f i) μ) (hg_meas : forall i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f + g) p μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun i s hs hμs => ?_⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine (eLpNorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans ?_
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le]; rw [add_halves]
  rw [hε_halves]
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : UnifIntegrable f p μ)
  statement: UnifIntegrable (-f) p μ
  proof: by
  simp_rw [UnifIntegrable, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf

中文:
定理 neg
  条件: (hf : Unif整数egrable f p μ)
  结论: Unif整数egrable (-f) p μ
  证明: by
  simp_rw [UnifIntegrable, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf
-/
protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  simp_rw [UnifIntegrable, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 <= p)
  proof: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg

中文:
定理 sub
  结论: (hf : Unif整数egrable f p μ) (hg : Unif整数egrable g p μ) (hp : 1 <= p)
  证明: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg
-/
protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 <= p)
    (hf_meas : forall i, AEStronglyMeasurable (f i) μ) (hg_meas : forall i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg

/--
theorem `ae_eq` / 定理 `ae_eq`

English:
theorem ae_eq
  given: (hf : UnifIntegrable f p μ) (hfg : forall n, f n =ᵐ[μ] g n)
  proof: by
  classical
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [Set.indicator_apply, hx]

中文:
定理 ae_eq
  条件: (hf : Unif整数egrable f p μ) (hfg : 对任意 n, f n =ᵐ[μ] g n)
  证明: by
  classical
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [Set.indicator_apply, hx]
-/
protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : forall n, f n =ᵐ[μ] g n) :
    UnifIntegrable g p μ := by
  classical
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [Set.indicator_apply, hx]

/--
theorem `indicator` / 定理 `indicator`

English:
theorem indicator
  given: (hf : UnifIntegrable f p μ) (E : Set α)
  proof: fun ε hε => by
  obtain ⟨δ, hδ_pos, hε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  calc
    eLpNorm (s.indicator (E.indicator (f i))) p μ
      = eLpNorm (E.indicator (s.indicator (f i))) p μ := by
      simp only [indicator_indicator, inter_comm]
    _ <= eLpNorm (s.indicator (f i)) p μ := eLpNorm_indicator_le _
    _ <= ENNReal.ofReal ε := hε _ _ hs hμs

中文:
定理 indicator
  条件: (hf : Unif整数egrable f p μ) (E : 集合 α)
  证明: fun ε hε => by
  obtain ⟨δ, hδ_pos, hε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  calc
    eLpNorm (s.indicator (E.indicator (f i))) p μ
      = eLpNorm (E.indicator (s.indicator (f i))) p μ := by
      simp only [indicator_indicator, inter_comm]
    _ <= eLpNorm (s.indicator (f i)) p μ := eLpNorm_indicator_le _
    _ <= ENNReal.ofReal ε := hε _ _ hs hμs
-/
protected theorem indicator (hf : UnifIntegrable f p μ) (E : Set α) :
    UnifIntegrable (fun i => E.indicator (f i)) p μ := fun ε hε => by
  obtain ⟨δ, hδ_pos, hε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  calc
    eLpNorm (s.indicator (E.indicator (f i))) p μ
      = eLpNorm (E.indicator (s.indicator (f i))) p μ := by
      simp only [indicator_indicator, inter_comm]
    _ <= eLpNorm (s.indicator (f i)) p μ := eLpNorm_indicator_le _
    _ <= ENNReal.ofReal ε := hε _ _ hs hμs

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hf : UnifIntegrable f p μ) (E : Set α)
  proof: fun ε hε => by
  obtain ⟨δ, hδ_pos, hδε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  rw [μ.restrict_apply hs]; rw [← measure_toMeasurable] at hμs
  calc
    eLpNorm (indicator s (f i)) p (μ.restrict E) = eLpNorm (f i) p (μ.restrict (s inter E)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [μ.restrict_restrict hs]
    _ <= eLpNorm (f i) p (μ.restrict (toMeasurable μ (s inter E))) :=
eLpNorm_mono_measure _ Measure.restrict_mono (subset_toMeasurable _ _) le_rfl
    _ = eLpNorm (indicator (toMeasurable μ (s inter E)) (f i)) p μ :=
      (eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_toMeasurable _ _)).symm
    _ <= ENNReal.ofReal ε := hδε i _ (measurableSet_toMeasurable _ _) hμs

中文:
定理 restrict
  条件: (hf : Unif整数egrable f p μ) (E : 集合 α)
  证明: fun ε hε => by
  obtain ⟨δ, hδ_pos, hδε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  rw [μ.restrict_apply hs]; rw [← measure_toMeasurable] at hμs
  calc
    eLpNorm (indicator s (f i)) p (μ.restrict E) = eLpNorm (f i) p (μ.restrict (s inter E)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [μ.restrict_restrict hs]
    _ <= eLpNorm (f i) p (μ.restrict (toMeasurable μ (s inter E))) :=
eLpNorm_mono_measure _ Measure.restrict_mono (subset_toMeasurable _ _) le_rfl
    _ = eLpNorm (indicator (toMeasurable μ (s inter E)) (f i)) p μ :=
      (eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_toMeasurable _ _)).symm
    _ <= ENNReal.ofReal ε := hδε i _ (measurableSet_toMeasurable _ _) hμs
-/
protected theorem restrict (hf : UnifIntegrable f p μ) (E : Set α) :
    UnifIntegrable f p (μ.restrict E) := fun ε hε => by
  obtain ⟨δ, hδ_pos, hδε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
  rw [μ.restrict_apply hs]; rw [← measure_toMeasurable] at hμs
  calc
    eLpNorm (indicator s (f i)) p (μ.restrict E) = eLpNorm (f i) p (μ.restrict (s inter E)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [μ.restrict_restrict hs]
    _ <= eLpNorm (f i) p (μ.restrict (toMeasurable μ (s inter E))) :=
eLpNorm_mono_measure _ Measure.restrict_mono (subset_toMeasurable _ _) le_rfl
    _ = eLpNorm (indicator (toMeasurable μ (s inter E)) (f i)) p μ :=
      (eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_toMeasurable _ _)).symm
    _ <= ENNReal.ofReal ε := hδε i _ (measurableSet_toMeasurable _ _) hμs

end UnifIntegrable

/--
theorem `unifIntegrable_zero_meas` / 定理 `unifIntegrable_zero_meas`

English:
theorem unifIntegrable_zero_meas
  given: [MeasurableSpace α] {p : Real>=0∞} {f : ι -> α -> β}
  proof: fun ε _ => ⟨1, one_pos, fun i s _ _ => by simp⟩

中文:
定理 unif整数egrable_zero_meas
  条件: [可测空间 α] {p : 实数>=0∞} {f : ι -> α -> β}
  证明: fun ε _ => ⟨1, one_pos, fun i s _ _ => by simp⟩

Depends on / 依赖: one_pos
-/
theorem unifIntegrable_zero_meas [MeasurableSpace α] {p : Real>=0∞} {f : ι -> α -> β} :
    UnifIntegrable f p (0 : Measure α) :=
  fun ε _ => ⟨1, one_pos, fun i s _ _ => by simp⟩

/--
theorem `unifIntegrable_congr_ae` / 定理 `unifIntegrable_congr_ae`

English:
theorem unifIntegrable_congr_ae
  given: {p : Real>=0∞} {f g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n)
  proof: ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

中文:
定理 unif整数egrable_congr_ae
  条件: {p : 实数>=0∞} {f g : ι -> α -> β} (hfg : 对任意 n, f n =ᵐ[μ] g n)
  证明: ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

Depends on / 依赖: ae_eq, hf.ae_eq, hg.ae_eq
-/
theorem unifIntegrable_congr_ae {p : Real>=0∞} {f g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

/--
theorem `tendsto_indicator_ge` / 定理 `tendsto_indicator_ge`

English:
theorem tendsto_indicator_ge
  given: (f : α -> β) (x : α)
  proof: by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : Real) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

中文:
定理 tendsto_indicator_ge
  条件: (f : α -> β) (x : α)
  证明: by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : Real) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

Depends on / 依赖: Nat.ceil, Nat.le_ceil, Set.indicator_of_notMem, Set.mem_ofPred_eq, indicator_of_notMem, le_ceil, lt_add_one, lt_of_le_of_lt, lt_of_lt_of_le, mem_ofPred_eq, not_le, tendsto_atTop_of_eventually_const
-/
theorem tendsto_indicator_ge (f : α -> β) (x : α) :
    Tendsto (fun M : Nat => { x | (M : Real) <= ‖f x‖₊ }.indicator f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : Real) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

variable {p : Real>=0∞}

section

variable {f : α -> β}

/--
theorem `MemLp.integral_indicator_norm_ge_le` / 定理 `MemLp.integral_indicator_norm_ge_le`

English:
theorem MemLp.integral_indicator_norm_ge_le
  statement: (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
  proof: by
  have htendsto :
      forallᵐ x ∂μ, Tendsto (fun M : Nat => { x | (M : Real) <= ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : forall M : Nat, AEStronglyMeasurable ({ x | (M : Real) <= ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memLp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : Nat => ∫⁻ a, ENNReal.ofReal ‖{ x | n <= ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : (n : Real) <= ‖f x‖
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_notMem]; rw [norm_zero]
      · exact norm_nonneg _
      · assumption
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [sub_zero] at hM
  refine ⟨M, ?_⟩
  convert! hM M le_rfl
  simp only [coe_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

中文:
定理 MemLp.integral_indicator_norm_ge_le
  结论: (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
  证明: by
  have htendsto :
      forallᵐ x ∂μ, Tendsto (fun M : Nat => { x | (M : Real) <= ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : forall M : Nat, AEStronglyMeasurable ({ x | (M : Real) <= ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memLp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : Nat => ∫⁻ a, ENNReal.ofReal ‖{ x | n <= ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : (n : Real) <= ‖f x‖
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_notMem]; rw [norm_zero]
      · exact norm_nonneg _
      · assumption
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [sub_zero] at hM
  refine ⟨M, ?_⟩
  convert! hM M le_rfl
  simp only [coe_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

Depends on / 依赖: AEStronglyMeasurable, HasFiniteIntegral, StronglyMeasurable, StronglyMeasurable.measurableSet_le, Tendsto, coe_nnreal_real, hbound, hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable, htendsto, indicator, measurable, measurableSet_le, memLp_one_iff_inte, nnnorm, stronglyMeasurable, stronglyMeasurable_const, tendsto_indicator_ge, univ_mem
-/
theorem MemLp.integral_indicator_norm_ge_le (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
    {ε : Real} (hε : 0 < ε) :
    exists M : Real, (∫⁻ x, ‖{ x | M <= ‖f x‖₊ }.indicator f x‖₊ ∂μ) <= ENNReal.ofReal ε := by
  have htendsto :
      forallᵐ x ∂μ, Tendsto (fun M : Nat => { x | (M : Real) <= ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : forall M : Nat, AEStronglyMeasurable ({ x | (M : Real) <= ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memLp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : Nat => ∫⁻ a, ENNReal.ofReal ‖{ x | n <= ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : (n : Real) <= ‖f x‖
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_notMem]; rw [norm_zero]
      · exact norm_nonneg _
      · assumption
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [sub_zero] at hM
  refine ⟨M, ?_⟩
  convert! hM M le_rfl
  simp only [coe_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

/--
theorem `MemLp.integral_indicator_norm_ge_nonneg_le_of_meas` / 定理 `MemLp.integral_indicator_norm_ge_nonneg_le_of_meas`

English:
theorem MemLp.integral_indicator_norm_ge_nonneg_le_of_meas
  statement: (hf : MemLp f 1 μ)
  proof: let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩

中文:
定理 MemLp.integral_indicator_norm_ge_nonneg_le_of_meas
  结论: (hf : MemLp f 1 μ)
  证明: let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩

Depends on / 依赖: hf.integral_indicator_norm_ge_le, integral_indicator_norm_ge_le, le_max_right
-/
theorem MemLp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : MemLp f 1 μ)
    (hmeas : StronglyMeasurable f) {ε : Real} (hε : 0 < ε) :
    exists M : Real, 0 <= M ∧ (∫⁻ x, ‖{ x | M <= ‖f x‖₊ }.indicator f x‖ₑ ∂μ) <= ENNReal.ofReal ε :=
  let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩

/--
theorem `MemLp.integral_indicator_norm_ge_nonneg_le` / 定理 `MemLp.integral_indicator_norm_ge_nonneg_le`

English:
theorem MemLp.integral_indicator_norm_ge_nonneg_le
  given: (hf : MemLp f 1 μ) {ε : Real} (hε : 0 < ε)
  proof: by
  have hf_mk : MemLp (hf.1.mk f) 1 μ := (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_ofPred_eq, hx.symm]

中文:
定理 MemLp.integral_indicator_norm_ge_nonneg_le
  条件: (hf : MemLp f 1 μ) {ε : 实数} (hε : 0 < ε)
  证明: by
  have hf_mk : MemLp (hf.1.mk f) 1 μ := (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_ofPred_eq, hx.symm]

Depends on / 依赖: Set.indicator_apply, Set.mem_ofPred_eq, ae_eq_mk, coe_nnnorm, filter_upwards, hM_pos, hf_mk, hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas, hx.symm, indicator_apply, integral_indicator_norm_ge_nonneg_le_of_meas, le_of_eq, lintegral_congr_ae, memLp_congr_ae, mem_ofPred_eq, stronglyMeasurable_mk
-/
theorem MemLp.integral_indicator_norm_ge_nonneg_le (hf : MemLp f 1 μ) {ε : Real} (hε : 0 < ε) :
    exists M : Real, 0 <= M ∧ (∫⁻ x, ‖{ x | M <= ‖f x‖₊ }.indicator f x‖ₑ ∂μ) <= ENNReal.ofReal ε := by
  have hf_mk : MemLp (hf.1.mk f) 1 μ := (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_ofPred_eq, hx.symm]

/--
theorem `MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero` / 定理 `MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero`

English:
theorem MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero
  statement: (hf : MemLp f ∞ μ)
  proof: by
  have hbdd : eLpNormEssSup f μ < ∞ := hf.eLpNorm_lt_top
  refine ⟨(eLpNorm f ∞ μ + 1).toReal, ?_⟩
  rw [eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict]
  · have : μ.restrict { x : α | (eLpNorm f ⊤ μ + 1).toReal <= ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, eLpNorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (eLpNormEssSup f μ + 1).toReal <= ‖f x‖ } subseteq
          { x : α | eLpNormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_ofPred_eq]; rw [← ENNReal.toReal_lt_toReal hbdd.ne ENNReal.coe_lt_top.ne]; rw [ENNReal.coe_toReal]; rw [coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [ENNReal.toReal_lt_toReal hbdd.ne]
        · exact ENNReal.lt_add_right hbdd.ne one_ne_zero
        · finiteness
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := enorm_ae_le_eLpNormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this]; rw [eLpNormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe

中文:
定理 MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero
  结论: (hf : MemLp f ∞ μ)
  证明: by
  have hbdd : eLpNormEssSup f μ < ∞ := hf.eLpNorm_lt_top
  refine ⟨(eLpNorm f ∞ μ + 1).toReal, ?_⟩
  rw [eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict]
  · have : μ.restrict { x : α | (eLpNorm f ⊤ μ + 1).toReal <= ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, eLpNorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (eLpNormEssSup f μ + 1).toReal <= ‖f x‖ } subseteq
          { x : α | eLpNormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_ofPred_eq]; rw [← ENNReal.toReal_lt_toReal hbdd.ne ENNReal.coe_lt_top.ne]; rw [ENNReal.coe_toReal]; rw [coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [ENNReal.toReal_lt_toReal hbdd.ne]
        · exact ENNReal.lt_add_right hbdd.ne one_ne_zero
        · finiteness
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := enorm_ae_le_eLpNormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this]; rw [eLpNormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe

Depends on / 依赖: ENNReal, ENNReal.co, ENNReal.toReal_lt_toReal, Measure, Measure.restrict_eq_zero, Set.mem_ofPred_eq, coe_nnnorm, eLpNorm, eLpNormEssSup, eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict, eLpNorm_exponent_top, eLpNorm_lt_top, hbdd.ne, hf.eLpNorm_lt_top, mem_ofPred_eq, restrict, restrict_eq_zero, subseteq, toReal, toReal_lt_toReal
-/
theorem MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero (hf : MemLp f ∞ μ)
    (hmeas : StronglyMeasurable f) :
    exists M : Real, eLpNormEssSup ({ x | M <= ‖f x‖₊ }.indicator f) μ = 0 := by
  have hbdd : eLpNormEssSup f μ < ∞ := hf.eLpNorm_lt_top
  refine ⟨(eLpNorm f ∞ μ + 1).toReal, ?_⟩
  rw [eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict]
  · have : μ.restrict { x : α | (eLpNorm f ⊤ μ + 1).toReal <= ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, eLpNorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (eLpNormEssSup f μ + 1).toReal <= ‖f x‖ } subseteq
          { x : α | eLpNormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_ofPred_eq]; rw [← ENNReal.toReal_lt_toReal hbdd.ne ENNReal.coe_lt_top.ne]; rw [ENNReal.coe_toReal]; rw [coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [ENNReal.toReal_lt_toReal hbdd.ne]
        · exact ENNReal.lt_add_right hbdd.ne one_ne_zero
        · finiteness
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := enorm_ae_le_eLpNormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this]; rw [eLpNormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe

/--
theorem `MemLp.eLpNorm_indicator_norm_ge_le` / 定理 `MemLp.eLpNorm_indicator_norm_ge_le`

English:
theorem MemLp.eLpNorm_indicator_norm_ge_le
  statement: (hf : MemLp f p μ) (hmeas : StronglyMeasurable f) {ε : Real}
  proof: by
  by_cases hp_ne_zero : p = 0
  · exact ⟨1, by simp [hp_ne_zero]⟩
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.eLpNormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [eLpNorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := MemLp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]; rw [← ENNReal.rpow_one (.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
  rw [ENNReal.rpow_mul]
  gcongr
  rw [ENNReal.ofReal_rpow_of_pos hε]
  convert! hM using 3 with x
  rw [enorm_indicator_eq_indicator_enorm]; rw [enorm_indicator_eq_indicator_enorm]
  have hiff : M ^ (1 / p.toReal) <= ‖f x‖₊ ↔ M <= ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]; rw [norm_norm]; rw [← Real.rpow_le_rpow_iff hM' (by positivity)
        (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top)]; rw [← Real.rpow_mul (norm_nonneg _)]; rw [mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]; rw [Real.rpow_one]
  by_cases hx : x in { x : α | M ^ (1 / p.toReal) <= ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.enorm_of_nonneg (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
    rw [Set.mem_ofPred_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    · simp [ENNReal.toReal_pos hp_ne_zero hp_ne_top]
    · rw [Set.mem_ofPred_eq]
      rwa [← hiff]

中文:
定理 MemLp.eLpNorm_indicator_norm_ge_le
  结论: (hf : MemLp f p μ) (hmeas : StronglyMeasurable f) {ε : 实数}
  证明: by
  by_cases hp_ne_zero : p = 0
  · exact ⟨1, by simp [hp_ne_zero]⟩
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.eLpNormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [eLpNorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := MemLp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]; rw [← ENNReal.rpow_one (.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
  rw [ENNReal.rpow_mul]
  gcongr
  rw [ENNReal.ofReal_rpow_of_pos hε]
  convert! hM using 3 with x
  rw [enorm_indicator_eq_indicator_enorm]; rw [enorm_indicator_eq_indicator_enorm]
  have hiff : M ^ (1 / p.toReal) <= ‖f x‖₊ ↔ M <= ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]; rw [norm_norm]; rw [← Real.rpow_le_rpow_iff hM' (by positivity)
        (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top)]; rw [← Real.rpow_mul (norm_nonneg _)]; rw [mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]; rw [Real.rpow_one]
  by_cases hx : x in { x : α | M ^ (1 / p.toReal) <= ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.enorm_of_nonneg (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
    rw [Set.mem_ofPred_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    · simp [ENNReal.toReal_pos hp_ne_zero hp_ne_top]
    · rw [Set.mem_ofPred_eq]
      rwa [← hiff]

Depends on / 依赖: ENNReal, ENNReal.rpow, MemLp.integral_indicator_norm_ge_nonneg_le, Real.rpow_pos_of_pos, eLpNormEssSup_indicator_norm_ge_eq_zero, eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_exponent_top, hf.eLpNormEssSup_indicator_norm_ge_eq_zero, hf.norm_rpow, hp_ne_top, hp_ne_zero, integral_indicator_norm_ge_nonneg_le, norm_rpow, p.toReal, rpow_pos_of_pos, toReal, zero_le
-/
theorem MemLp.eLpNorm_indicator_norm_ge_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f) {ε : Real}
    (hε : 0 < ε) : exists M : Real, eLpNorm ({ x | M <= ‖f x‖₊ }.indicator f) p μ <= ENNReal.ofReal ε := by
  by_cases hp_ne_zero : p = 0
  · exact ⟨1, by simp [hp_ne_zero]⟩
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.eLpNormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [eLpNorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := MemLp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]; rw [← ENNReal.rpow_one (.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
  rw [ENNReal.rpow_mul]
  gcongr
  rw [ENNReal.ofReal_rpow_of_pos hε]
  convert! hM using 3 with x
  rw [enorm_indicator_eq_indicator_enorm]; rw [enorm_indicator_eq_indicator_enorm]
  have hiff : M ^ (1 / p.toReal) <= ‖f x‖₊ ↔ M <= ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]; rw [norm_norm]; rw [← Real.rpow_le_rpow_iff hM' (by positivity)
        (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top)]; rw [← Real.rpow_mul (norm_nonneg _)]; rw [mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]; rw [Real.rpow_one]
  by_cases hx : x in { x : α | M ^ (1 / p.toReal) <= ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.enorm_of_nonneg (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
    rw [Set.mem_ofPred_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    · simp [ENNReal.toReal_pos hp_ne_zero hp_ne_top]
    · rw [Set.mem_ofPred_eq]
      rwa [← hiff]

/--
theorem `MemLp.eLpNorm_indicator_norm_ge_pos_le` / 定理 `MemLp.eLpNorm_indicator_norm_ge_pos_le`

English:
theorem MemLp.eLpNorm_indicator_norm_ge_pos_le
  statement: (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
  proof: by
  obtain ⟨M, hM⟩ := hf.eLpNorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (eLpNorm_mono fun x => ?_) hM⟩
  simp only [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

中文:
定理 MemLp.eLpNorm_indicator_norm_ge_pos_le
  结论: (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
  证明: by
  obtain ⟨M, hM⟩ := hf.eLpNorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (eLpNorm_mono fun x => ?_) hM⟩
  simp only [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

Depends on / 依赖: eLpNorm_indicator_norm_ge_le, eLpNorm_mono, hf.eLpNorm_indicator_norm_ge_le, le_max_left, le_max_right, le_trans, lt_of_lt_of_le, norm_indicator_eq_indicator_norm, zero_lt_one
-/
theorem MemLp.eLpNorm_indicator_norm_ge_pos_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
    {ε : Real} (hε : 0 < ε) :
    exists M : Real, 0 < M ∧ eLpNorm ({ x | M <= ‖f x‖₊ }.indicator f) p μ <= ENNReal.ofReal ε := by
  obtain ⟨M, hM⟩ := hf.eLpNorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (eLpNorm_mono fun x => ?_) hM⟩
  simp only [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

end

/--
theorem `eLpNorm_indicator_le_of_bound` / 定理 `eLpNorm_indicator_le_of_bound`

English:
theorem eLpNorm_indicator_le_of_bound
  statement: {f : α -> β} (hp_top : p != ∞) {ε : Real} (hε : 0 < ε) {M : Real}
  proof: by
  by_cases! hM : M <= 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply]; rw [← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / M) ^ p.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : forallᵐ x ∂μ.restrict s, ‖f x‖ <= M := by
    filter_upwards
    exact fun x => (hf x).le
  refine le_trans (eLpNorm_le_of_ae_bound haebdd) ?_
  rw [Measure.restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]; rw [← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp_top)]
    refine le_trans hμ ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM)]
    gcongr
    rw [ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]

中文:
定理 eLpNorm_indicator_le_of_bound
  结论: {f : α -> β} (hp_top : p != ∞) {ε : 实数} (hε : 0 < ε) {M : 实数}
  证明: by
  by_cases! hM : M <= 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply]; rw [← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / M) ^ p.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : forallᵐ x ∂μ.restrict s, ‖f x‖ <= M := by
    filter_upwards
    exact fun x => (hf x).le
  refine le_trans (eLpNorm_le_of_ae_bound haebdd) ?_
  rw [Measure.restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]; rw [← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp_top)]
    refine le_trans hμ ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM)]
    gcongr
    rw [ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]

Depends on / 依赖: Pi.zero_apply, Real.rpow_pos_of_pos, div_pos, eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_le_of_ae_bound, filter_upwards, haebdd, le_trans, lt_of_lt_of_le, norm_le_zero_iff, p.toReal, restrict, rpow_pos_of_pos, toReal, zero_apply, zero_lt_one
-/
theorem eLpNorm_indicator_le_of_bound {f : α -> β} (hp_top : p != ∞) {ε : Real} (hε : 0 < ε) {M : Real}
    (hf : forall x, ‖f x‖ < M) :
    exists (δ : Real) (_ : 0 < δ), forall s, MeasurableSet s ->
      μ s <= ENNReal.ofReal δ -> eLpNorm (s.indicator f) p μ <= ENNReal.ofReal ε := by
  by_cases! hM : M <= 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply]; rw [← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / M) ^ p.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : forallᵐ x ∂μ.restrict s, ‖f x‖ <= M := by
    filter_upwards
    exact fun x => (hf x).le
  refine le_trans (eLpNorm_le_of_ae_bound haebdd) ?_
  rw [Measure.restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]; rw [← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp_top)]
    refine le_trans hμ ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM)]
    gcongr
    rw [ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]

section

variable {f : α -> β}

/--
theorem `MemLp.eLpNorm_indicator_le'` / 定理 `MemLp.eLpNorm_indicator_le'`

English:
theorem MemLp.eLpNorm_indicator_le'
  statement: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
  proof: by
  obtain ⟨M, hMpos, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    eLpNorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm]; rw [Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M <= ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    refine le_trans (eLpNorm_add_le ?_ ?_ hp_one) ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add (le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) hM) ?_
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M <= ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx

中文:
定理 MemLp.eLpNorm_indicator_le'
  结论: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
  证明: by
  obtain ⟨M, hMpos, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    eLpNorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm]; rw [Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M <= ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    refine le_trans (eLpNorm_add_le ?_ ?_ hp_one) ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add (le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) hM) ?_
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M <= ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx

Depends on / 依赖: Set.indicator_apply, eLpNorm_add_le, eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_indicator_le_of_bound, eLpNorm_indicator_norm_ge_pos_le, exacts, hf.eLpNorm_indicator_norm_ge_pos_le, hp_top, indicator, indicator_apply, le_trans, norm_indicator_eq_indicator_norm, split_ifs
-/
theorem MemLp.eLpNorm_indicator_le' (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : Real} (hε : 0 < ε) :
    exists (δ : Real) (_ : 0 < δ), forall s, MeasurableSet s -> μ s <= ENNReal.ofReal δ ->
      eLpNorm (s.indicator f) p μ <= 2 * ENNReal.ofReal ε := by
  obtain ⟨M, hMpos, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    eLpNorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm]; rw [Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M <= ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    refine le_trans (eLpNorm_add_le ?_ ?_ hp_one) ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add (le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) hM) ?_
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M <= ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx

/--
theorem `MemLp.eLpNorm_indicator_le_of_meas` / 定理 `MemLp.eLpNorm_indicator_le_of_meas`

English:
theorem MemLp.eLpNorm_indicator_le_of_meas
  statement: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
  proof: by
  obtain ⟨δ, hδpos, hδ⟩ := hf.eLpNorm_indicator_le' hp_one hp_top hmeas (half_pos hε)
  refine ⟨δ, hδpos, fun s hs hμs => le_trans (hδ s hs hμs) ?_⟩
  rw [ENNReal.ofReal_div_of_pos zero_lt_two]; rw [(by simp : ENNReal.ofReal 2 = 2)]; rw [ENNReal.mul_div_cancel] <;>
    norm_num

中文:
定理 MemLp.eLpNorm_indicator_le_of_meas
  结论: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
  证明: by
  obtain ⟨δ, hδpos, hδ⟩ := hf.eLpNorm_indicator_le' hp_one hp_top hmeas (half_pos hε)
  refine ⟨δ, hδpos, fun s hs hμs => le_trans (hδ s hs hμs) ?_⟩
  rw [ENNReal.ofReal_div_of_pos zero_lt_two]; rw [(by simp : ENNReal.ofReal 2 = 2)]; rw [ENNReal.mul_div_cancel] <;>
    norm_num

Depends on / 依赖: ENNReal, ENNReal.mul_div_cancel, ENNReal.ofReal, ENNReal.ofReal_div_of_pos, eLpNorm_indicator_le, half_pos, hf.eLpNorm_indicator_le, hp_one, hp_top, le_trans, mul_div_cancel, ofReal, ofReal_div_of_pos, zero_lt_two
-/
theorem MemLp.eLpNorm_indicator_le_of_meas (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : Real} (hε : 0 < ε) :
    exists (δ : Real) (_ : 0 < δ), forall s, MeasurableSet s -> μ s <= ENNReal.ofReal δ ->
      eLpNorm (s.indicator f) p μ <= ENNReal.ofReal ε := by
  obtain ⟨δ, hδpos, hδ⟩ := hf.eLpNorm_indicator_le' hp_one hp_top hmeas (half_pos hε)
  refine ⟨δ, hδpos, fun s hs hμs => le_trans (hδ s hs hμs) ?_⟩
  rw [ENNReal.ofReal_div_of_pos zero_lt_two]; rw [(by simp : ENNReal.ofReal 2 = 2)]; rw [ENNReal.mul_div_cancel] <;>
    norm_num

/--
theorem `MemLp.eLpNorm_indicator_le` / 定理 `MemLp.eLpNorm_indicator_le`

English:
theorem MemLp.eLpNorm_indicator_le
  statement: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ) {ε : Real}
  proof: by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).eLpNorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert! hδ s hs hμs using 1
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_congr_ae heq.restrict

中文:
定理 MemLp.eLpNorm_indicator_le
  结论: (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ) {ε : 实数}
  证明: by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).eLpNorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert! hδ s hs hμs using 1
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_congr_ae heq.restrict

Depends on / 依赖: ae_eq, convert, eLpNorm_congr_ae, eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_indicator_le_of_meas, heq.restrict, hp_one, hp_top, p.ae_eq, restrict
-/
theorem MemLp.eLpNorm_indicator_le (hp_one : 1 <= p) (hp_top : p != ∞) (hf : MemLp f p μ) {ε : Real}
    (hε : 0 < ε) :
    exists (δ : Real) (_ : 0 < δ), forall s, MeasurableSet s -> μ s <= ENNReal.ofReal δ ->
      eLpNorm (s.indicator f) p μ <= ENNReal.ofReal ε := by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).eLpNorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert! hδ s hs hμs using 1
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]; rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_congr_ae heq.restrict

/--
theorem `unifIntegrable_const` / 定理 `unifIntegrable_const`

English:
theorem unifIntegrable_const
  given: {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  proof: by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.eLpNorm_indicator_le hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun _ => hgδ⟩

中文:
定理 unif整数egrable_const
  条件: {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  证明: by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.eLpNorm_indicator_le hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun _ => hgδ⟩

Depends on / 依赖: eLpNorm_indicator_le, hg.eLpNorm_indicator_le, hp_ne_top
-/
theorem unifIntegrable_const {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.eLpNorm_indicator_le hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun _ => hgδ⟩

/--
theorem `unifIntegrable_subsingleton` / 定理 `unifIntegrable_subsingleton`

English:
theorem unifIntegrable_subsingleton
  statement: [Subsingleton ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  proof: by
  intro ε hε
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨δ, hδpos, fun j s hs hμs => ?_⟩
    convert! hδ s hs hμs
· exact ⟨1, zero_lt_one, fun i => False.elim hι Nonempty.intro i⟩

中文:
定理 unif整数egrable_subsingleton
  结论: [子单例 ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  证明: by
  intro ε hε
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨δ, hδpos, fun j s hs hμs => ?_⟩
    convert! hδ s hs hμs
· exact ⟨1, zero_lt_one, fun i => False.elim hι Nonempty.intro i⟩

Depends on / 依赖: False.elim, Nonempty, Nonempty.intro, convert, eLpNorm_indicator_le, hp_one, hp_top, zero_lt_one
-/
theorem unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 <= p) (hp_top : p != ∞)
    {f : ι -> α -> β} (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  intro ε hε
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨δ, hδpos, fun j s hs hμs => ?_⟩
    convert! hδ s hs hμs
· exact ⟨1, zero_lt_one, fun i => False.elim hι Nonempty.intro i⟩

/--
theorem `unifIntegrable_fin` / 定理 `unifIntegrable_fin`

English:
theorem unifIntegrable_fin
  statement: (hp_one : 1 <= p) (hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β}
  proof: by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifIntegrable_subsingleton hp_one hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp (Fin.last n)).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun i s hs hμs => ?_⟩
    by_cases! hi : i.val < n
    · rw [(_ : f i = g ⟨i.val, hi⟩)]
      · exact hδ₁ _ s hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_left _ _)
      · simp [g]
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm (Fin.is_le i) hi)
      exact hδ₂ _ hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_right _ _)

中文:
定理 unif整数egrable_fin
  结论: (hp_one : 1 <= p) (hp_top : p != ∞) {n : 自然数} {f : 有限集 n -> α -> β}
  证明: by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifIntegrable_subsingleton hp_one hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp (Fin.last n)).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun i s hs hμs => ?_⟩
    by_cases! hi : i.val < n
    · rw [(_ : f i = g ⟨i.val, hi⟩)]
      · exact hδ₁ _ s hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_left _ _)
      · simp [g]
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm (Fin.is_le i) hi)
      exact hδ₂ _ hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_right _ _)

Depends on / 依赖: Fin.last, castSucc, eLpNorm_indicator_le, hp_one, hp_top, i.castSucc, i.val, k.castSucc, lt_min, revert, unifIntegrable_subsingleton
-/
theorem unifIntegrable_fin (hp_one : 1 <= p) (hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β}
    (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifIntegrable_subsingleton hp_one hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp (Fin.last n)).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun i s hs hμs => ?_⟩
    by_cases! hi : i.val < n
    · rw [(_ : f i = g ⟨i.val, hi⟩)]
      · exact hδ₁ _ s hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_left _ _)
      · simp [g]
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm (Fin.is_le i) hi)
      exact hδ₂ _ hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_right _ _)

/--
theorem `unifIntegrable_finite` / 定理 `unifIntegrable_finite`

English:
theorem unifIntegrable_finite
  statement: [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞) {f : ι -> α -> β}
  proof: by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  let g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_fin hp_one hp_top hg hε
  refine ⟨δ, hδpos, fun i s hs hμs => ?_⟩
  simpa [g] using hδ (hn.some i) s hs hμs

中文:
定理 unif整数egrable_finite
  结论: [有限 ι] (hp_one : 1 <= p) (hp_top : p != ∞) {f : ι -> α -> β}
  证明: by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  let g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_fin hp_one hp_top hg hε
  refine ⟨δ, hδpos, fun i s hs hμs => ?_⟩
  simpa [g] using hδ (hn.some i) s hs hμs

Depends on / 依赖: Finite, Finite.exists_equiv_fin, exists_equiv_fin, hn.some, hn.some.symm, hp_one, hp_top, unifIntegrable_fin
-/
theorem unifIntegrable_finite [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞) {f : ι -> α -> β}
    (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  let g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_fin hp_one hp_top hg hε
  refine ⟨δ, hδpos, fun i s hs hμs => ?_⟩
  simpa [g] using hδ (hn.some i) s hs hμs

end

/--
theorem `tendsto_Lp_finite_of_tendsto_ae_of_meas` / 定理 `tendsto_Lp_finite_of_tendsto_ae_of_meas`

English:
theorem tendsto_Lp_finite_of_tendsto_ae_of_meas
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases! h : ∞ <= ε
  · rw [top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε.toReal / 3 := div_pos (ENNReal.toReal_pos hε.ne' h.ne) (by simp)
  have hdivp : 0 <= 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₁ n t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₁.le]
    exact min_le_left _ _
  have hng : eLpNorm (t.indicator g) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₂ t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₂.le]
    exact min_le_right _ _
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    specialize hN n hn
    have : 0 <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine le_trans this ?_
    rw [div_mul_eq_div_mul_one_div]; rw [← ENNReal.ofReal_toReal (measure_lt_top μ tᶜ).ne]; rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hdivp]; rw [← ENNReal.ofReal_mul]; rw [mul_assoc]
    · refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hε'.le ?_)
      rw [mul_comm]; rw [mul_one_div]; rw [div_le_one]
      · gcongr
        refine (ENNReal.toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
        rw [ENNReal.ofReal_coe_nnreal]; rw [coe_measureUnivNNReal]
        exact measure_mono (Set.subset_univ _)
      · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
    · positivity
  have : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : Real) < 3 by simp)]; rw [ENNReal.ofReal_toReal h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [eLpNorm_neg]; rw [← ENNReal.add_thirds ε]; rw [← sub_eq_add_neg]
  gcongr

中文:
定理 tendsto_Lp_finite_of_tendsto_ae_of_meas
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases! h : ∞ <= ε
  · rw [top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε.toReal / 3 := div_pos (ENNReal.toReal_pos hε.ne' h.ne) (by simp)
  have hdivp : 0 <= 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₁ n t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₁.le]
    exact min_le_left _ _
  have hng : eLpNorm (t.indicator g) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₂ t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₂.le]
    exact min_le_right _ _
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    specialize hN n hn
    have : 0 <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine le_trans this ?_
    rw [div_mul_eq_div_mul_one_div]; rw [← ENNReal.ofReal_toReal (measure_lt_top μ tᶜ).ne]; rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hdivp]; rw [← ENNReal.ofReal_mul]; rw [mul_assoc]
    · refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hε'.le ?_)
      rw [mul_comm]; rw [mul_one_div]; rw [div_le_one]
      · gcongr
        refine (ENNReal.toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
        rw [ENNReal.ofReal_coe_nnreal]; rw [coe_measureUnivNNReal]
        exact measure_mono (Set.subset_univ _)
      · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
    · positivity
  have : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : Real) < 3 by simp)]; rw [ENNReal.ofReal_toReal h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [eLpNorm_neg]; rw [← ENNReal.add_thirds ε]; rw [← sub_eq_add_neg]
  gcongr

Depends on / 依赖: ENNReal, ENNReal.tendsto_atTop_zero, ENNReal.toReal_pos, Real.rpow_pos_of_pos, div_pos, eLpNorm_i, h.ne, measureUnivNNReal, measureUnivNNReal_pos, p.toReal, rpow_pos_of_pos, tendsto_atTop_zero, toReal, toReal_pos, top_le_iff
-/
theorem tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    {f : Nat -> α -> β} {g : α -> β} (hf : forall n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases! h : ∞ <= ε
  · rw [top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε.toReal / 3 := div_pos (ENNReal.toReal_pos hε.ne' h.ne) (by simp)
  have hdivp : 0 <= 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₁ n t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₁.le]
    exact min_le_left _ _
  have hng : eLpNorm (t.indicator g) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₂ t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₂.le]
    exact min_le_right _ _
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ <= ENNReal.ofReal (ε.toReal / 3) := by
    specialize hN n hn
    have : 0 <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) <= ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine le_trans this ?_
    rw [div_mul_eq_div_mul_one_div]; rw [← ENNReal.ofReal_toReal (measure_lt_top μ tᶜ).ne]; rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hdivp]; rw [← ENNReal.ofReal_mul]; rw [mul_assoc]
    · refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hε'.le ?_)
      rw [mul_comm]; rw [mul_one_div]; rw [div_le_one]
      · gcongr
        refine (ENNReal.toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
        rw [ENNReal.ofReal_coe_nnreal]; rw [coe_measureUnivNNReal]
        exact measure_mono (Set.subset_univ _)
      · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
    · positivity
  have : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : Real) < 3 by simp)]; rw [ENNReal.ofReal_toReal h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [eLpNorm_neg]; rw [← ENNReal.add_thirds ε]; rw [← sub_eq_add_neg]
  gcongr

/--
theorem `tendsto_Lp_finite_of_tendsto_ae` / 定理 `tendsto_Lp_finite_of_tendsto_ae`

English:
theorem tendsto_Lp_finite_of_tendsto_ae
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  have : forall n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : forallᵐ x ∂μ, forall n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

中文:
定理 tendsto_Lp_finite_of_tendsto_ae
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  have : forall n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : forallᵐ x ∂μ, forall n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

Depends on / 依赖: ae_all_iff, ae_eq, ae_eq_mk, ae_eq_mk.sub, eLpNorm, eLpNorm_congr_ae, filter_upwards, h_ae_forall_eq, hg.ae_eq, hui.ae_eq, simp_rw, stronglyMeasurable_mk, tendsto_Lp_finite_of_tendsto_ae_of_meas
-/
theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    {f : Nat -> α -> β} {g : α -> β} (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have : forall n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : forallᵐ x ∂μ, forall n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

variable {f : Nat -> α -> β} {g : α -> β}

/--
theorem `unifIntegrable_of_tendsto_Lp_zero` / 定理 `unifIntegrable_of_tendsto_Lp_zero`

English:
theorem unifIntegrable_of_tendsto_Lp_zero
  statement: (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
  proof: by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa)
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_fin hp hp' hF hε
  refine ⟨δ₁, hδpos₁, fun n s hs hμs => ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
  · exact (eLpNorm_indicator_le _).trans (hN n hn)

中文:
定理 unif整数egrable_of_tendsto_Lp_zero
  结论: (hp : 1 <= p) (hp' : p != ∞) (hf : 对任意 n, MemLp (f n) p μ)
  证明: by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa)
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_fin hp hp' hF hε
  refine ⟨δ₁, hδpos₁, fun n s hs hμs => ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
  · exact (eLpNorm_indicator_le _).trans (hN n hn)

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.tendsto_atTop_zero, eLpNorm_indicator_le, hf_tendsto, ofReal, tendsto_atTop_zero, unifIntegrable_fin
-/
theorem unifIntegrable_of_tendsto_Lp_zero (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa)
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_fin hp hp' hF hε
  refine ⟨δ₁, hδpos₁, fun n s hs hμs => ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
  · exact (eLpNorm_indicator_le _).trans (hN n hn)

/--
theorem `unifIntegrable_of_tendsto_Lp` / 定理 `unifIntegrable_of_tendsto_Lp`

English:
theorem unifIntegrable_of_tendsto_Lp
  statement: (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
  proof: by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg

中文:
定理 unif整数egrable_of_tendsto_Lp
  结论: (hp : 1 <= p) (hp' : p != ∞) (hf : 对任意 n, MemLp (f n) p μ)
  证明: by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg

Depends on / 依赖: UnifIntegrable, UnifIntegrable.add, aestronglyMeasurable, hg.aestronglyMeasurable, unifIntegrable_const, unifIntegrable_of_tendsto_Lp_zero
-/
theorem unifIntegrable_of_tendsto_Lp (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg

/--
theorem `tendsto_Lp_finite_of_tendstoInMeasure` / 定理 `tendsto_Lp_finite_of_tendstoInMeasure`

English:
theorem tendsto_Lp_finite_of_tendstoInMeasure
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ => hf _) hg (fun ε hε =>
      let ⟨δ, hδ, hδ'⟩ := hui hε
      ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      hms'⟩

中文:
定理 tendsto_Lp_finite_of_tendstoInMeasure
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ => hf _) hg (fun ε hε =>
      let ⟨δ, hδ, hδ'⟩ := hui hε
      ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      hms'⟩

Depends on / 依赖: TendstoInMeasure, TendstoInMeasure.exists_seq_tendsto_ae, exists_seq_tendsto_ae, tendsto_Lp_finite_of_tendsto_ae, tendsto_of_subseq_tendsto
-/
theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ => hf _) hg (fun ε hε =>
      let ⟨δ, hδ, hδ'⟩ := hui hε
      ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      hms'⟩

/--
theorem `tendstoInMeasure_iff_tendsto_Lp_finite` / 定理 `tendstoInMeasure_iff_tendsto_Lp_finite`

English:
theorem tendstoInMeasure_iff_tendsto_Lp_finite
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩

中文:
定理 tendstoInMeasure_iff_tendsto_Lp_finite
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩

Depends on / 依赖: aestronglyMeasurable, hg.aestronglyMeasurable, lt_of_lt_of_le, ne.symm, tendstoInMeasure_of_tendsto_eLpNorm, tendsto_Lp_finite_of_tendstoInMeasure, unifIntegrable_of_tendsto_Lp, zero_lt_one
-/
theorem tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩

/--
theorem `unifIntegrable_of'` / 定理 `unifIntegrable_of'`

English:
theorem unifIntegrable_of'
  statement: (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
  proof: by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne.symm
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (half_pos hε)
  refine ⟨(ε / (2 * C)) ^ ENNReal.toReal p,
    Real.rpow_pos_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos))) _,
    fun i s hs hμs => ?_⟩
  by_cases hμs' : μ s = 0
  · rw [(eLpNorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    simp
  calc
    eLpNorm (Set.indicator s (f i)) p μ <=
        eLpNorm (Set.indicator (s inter { x | C <= ‖f i x‖₊ }) (f i)) p μ +
          eLpNorm (Set.indicator (s inter { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s inter { x : α | C <= ‖f i x‖₊ }).indicator (f i) x +
        (s inter { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_gt] :
            { x : α | C <= ‖f i x‖₊ } union { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_ofPred_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ <= eLpNorm (Set.indicator { x | C <= ‖f i x‖₊ } (f i)) p μ +
        (C : Real>=0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (eLpNorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have : forallᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ <= C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (eLpNorm_le_of_ae_bound this) ?_
      rw [mul_comm]; rw [Measure.restrict_apply' hs]; rw [Set.univ_inter]; rw [ENNReal.ofReal_coe_nnreal]; rw [one_div]
    _ <= ENNReal.ofReal (ε / 2) + C * ENNReal.ofReal (ε / (2 * C)) := by
      grw [hC i]
      gcongr
      rwa [one_div, ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hpzero hp'),
        ENNReal.ofReal_rpow_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos)))]
    _ <= ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      gcongr
      rw [← ENNReal.ofReal_coe_nnreal]; rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]; rw [← div_div]; rw [mul_div_cancel₀ _ (NNReal.coe_pos.2 hCpos).ne.symm]
    _ <= ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; rw [add_halves]

中文:
定理 unif整数egrable_of'
  结论: (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
  证明: by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne.symm
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (half_pos hε)
  refine ⟨(ε / (2 * C)) ^ ENNReal.toReal p,
    Real.rpow_pos_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos))) _,
    fun i s hs hμs => ?_⟩
  by_cases hμs' : μ s = 0
  · rw [(eLpNorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    simp
  calc
    eLpNorm (Set.indicator s (f i)) p μ <=
        eLpNorm (Set.indicator (s inter { x | C <= ‖f i x‖₊ }) (f i)) p μ +
          eLpNorm (Set.indicator (s inter { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s inter { x : α | C <= ‖f i x‖₊ }).indicator (f i) x +
        (s inter { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_gt] :
            { x : α | C <= ‖f i x‖₊ } union { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_ofPred_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ <= eLpNorm (Set.indicator { x | C <= ‖f i x‖₊ } (f i)) p μ +
        (C : Real>=0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (eLpNorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have : forallᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ <= C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (eLpNorm_le_of_ae_bound this) ?_
      rw [mul_comm]; rw [Measure.restrict_apply' hs]; rw [Set.univ_inter]; rw [ENNReal.ofReal_coe_nnreal]; rw [one_div]
    _ <= ENNReal.ofReal (ε / 2) + C * ENNReal.ofReal (ε / (2 * C)) := by
      grw [hC i]
      gcongr
      rwa [one_div, ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hpzero hp'),
        ENNReal.ofReal_rpow_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos)))]
    _ <= ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      gcongr
      rw [← ENNReal.ofReal_coe_nnreal]; rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]; rw [← div_div]; rw [mul_div_cancel₀ _ (NNReal.coe_pos.2 hCpos).ne.symm]
    _ <= ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; rw [add_halves]

Depends on / 依赖: ENNReal, ENNReal.toReal, Measure, Measure.measure_univ_eq_zero, NNReal, NNReal.coe_pos, Real.rpow_pos_of_pos, Set.univ, aestronglyMeasurable, coe_pos, div_pos, eLpNorm_eq_zero_iff, half_pos, hpzero, indicator, indicator_meas_zero, lt_of_lt_of_le, measure_univ_eq_zero, mul_pos, ne.symm
-/
theorem unifIntegrable_of' (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
    (hf : forall i, StronglyMeasurable (f i))
    (h : forall ε : Real, 0 < ε -> exists C : Real>=0, 0 < C ∧
      forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne.symm
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (half_pos hε)
  refine ⟨(ε / (2 * C)) ^ ENNReal.toReal p,
    Real.rpow_pos_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos))) _,
    fun i s hs hμs => ?_⟩
  by_cases hμs' : μ s = 0
  · rw [(eLpNorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    simp
  calc
    eLpNorm (Set.indicator s (f i)) p μ <=
        eLpNorm (Set.indicator (s inter { x | C <= ‖f i x‖₊ }) (f i)) p μ +
          eLpNorm (Set.indicator (s inter { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s inter { x : α | C <= ‖f i x‖₊ }).indicator (f i) x +
        (s inter { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_gt] :
            { x : α | C <= ‖f i x‖₊ } union { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_ofPred_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ <= eLpNorm (Set.indicator { x | C <= ‖f i x‖₊ } (f i)) p μ +
        (C : Real>=0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (eLpNorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have : forallᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ <= C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (eLpNorm_le_of_ae_bound this) ?_
      rw [mul_comm]; rw [Measure.restrict_apply' hs]; rw [Set.univ_inter]; rw [ENNReal.ofReal_coe_nnreal]; rw [one_div]
    _ <= ENNReal.ofReal (ε / 2) + C * ENNReal.ofReal (ε / (2 * C)) := by
      grw [hC i]
      gcongr
      rwa [one_div, ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hpzero hp'),
        ENNReal.ofReal_rpow_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos)))]
    _ <= ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      gcongr
      rw [← ENNReal.ofReal_coe_nnreal]; rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]; rw [← div_div]; rw [mul_div_cancel₀ _ (NNReal.coe_pos.2 hCpos).ne.symm]
    _ <= ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; rw [add_halves]

/--
theorem `unifIntegrable_of` / 定理 `unifIntegrable_of`

English:
theorem unifIntegrable_of
  statement: (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
  proof: by
  set g : ι -> α -> β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : forall i, eLpNorm ({ x | C <= ‖g i x‖₊ }.indicator (g i)) p μ <= ENNReal.ofReal ε := by
    intro i
    refine le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x in { x | C <= ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_ofPred, hx] at hfx
    · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
      rwa [Set.mem_ofPred, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (eLpNorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm]; rw [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

中文:
定理 unif整数egrable_of
  结论: (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
  证明: by
  set g : ι -> α -> β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : forall i, eLpNorm ({ x | C <= ‖g i x‖₊ }.indicator (g i)) p μ <= ENNReal.ofReal ε := by
    intro i
    refine le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x in { x | C <= ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_ofPred, hx] at hfx
    · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
      rwa [Set.mem_ofPred, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (eLpNorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm]; rw [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Exists, Exists.choose_spec, Set.indicator, ae_eq, choose_spec, eLpNorm, eLpNorm_congr_ae, filter_upwards, indicator, le_of_eq, le_trans, ofReal, unifIntegrable_of
-/
theorem unifIntegrable_of (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β}
    (hf : forall i, AEStronglyMeasurable (f i) μ)
    (h : forall ε : Real, 0 < ε -> exists C : Real>=0,
      forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  set g : ι -> α -> β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : forall i, eLpNorm ({ x | C <= ‖g i x‖₊ }.indicator (g i)) p μ <= ENNReal.ofReal ε := by
    intro i
    refine le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x in { x | C <= ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_ofPred, hx] at hfx
    · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
      rwa [Set.mem_ofPred, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (eLpNorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm]; rw [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

/--
lemma `UnifIntegrable.unifIntegrable_of_tendstoInMeasure` / 引理 `UnifIntegrable.unifIntegrable_of_tendstoInMeasure`

English:
lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure
  statement: {κ : Type*} (u : Filter κ) [NeBot u]
  proof: by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun n => hδ' (s n) t ht ht') (hs.indicator t) ?_
  exact fun n => (hfn (s n)).indicator ht

中文:
引理 Unif整数egrable.unif整数egrable_of_tendstoInMeasure
  结论: {κ : 类型} (u : 滤子 κ) [NeBot u]
  证明: by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun n => hδ' (s n) t ht ht') (hs.indicator t) ?_
  exact fun n => (hfn (s n)).indicator ht

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_le_of_tendstoInMeasure, hs.indicator, indicator, of_forall
-/
lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι -> α -> β} (hUI : UnifIntegrable fn p μ)
    (hfn : forall i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α -> β | exists ni : κ -> ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) => f.1) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun n => hδ' (s n) t ht ht') (hs.indicator t) ?_
  exact fun n => (hfn (s n)).indicator ht

/--
lemma `UnifIntegrable.unifIntegrable_of_ae_tendsto` / 引理 `UnifIntegrable.unifIntegrable_of_ae_tendsto`

English:
lemma UnifIntegrable.unifIntegrable_of_ae_tendsto
  statement: {κ : Type*} (u : Filter κ) [NeBot u]
  proof: by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n => hδ' (s n) t ht ht') ?_ ?_
  · exact fun n => (hfn (s n)).indicator ht
  · filter_upwards [hs] with a ha
    by_cases memt : a in t
    · simpa [memt]
    · simp [memt]

中文:
引理 Unif整数egrable.unif整数egrable_of_ae_tendsto
  结论: {κ : 类型} (u : 滤子 κ) [NeBot u]
  证明: by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n => hδ' (s n) t ht ht') ?_ ?_
  · exact fun n => (hfn (s n)).indicator ht
  · filter_upwards [hs] with a ha
    by_cases memt : a in t
    · simpa [memt]
    · simp [memt]

Depends on / 依赖: Eventually, Eventually.of_forall, Lp.eLpNorm_le_of_ae_tendsto, eLpNorm_le_of_ae_tendsto, filter_upwards, indicator, of_forall
-/
lemma UnifIntegrable.unifIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι -> α -> β} (hUI : UnifIntegrable fn p μ)
    (hfn : forall i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α -> β | exists ni : κ -> ι,
      forallᵐ (x : α) ∂μ, Tendsto (fun n => fn (ni n) x) u (𝓝 (g x))}) => f.1) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n => hδ' (s n) t ht ht') ?_ ?_
  · exact fun n => (hfn (s n)).indicator ht
  · filter_upwards [hs] with a ha
    by_cases memt : a in t
    · simpa [memt]
    · simp [memt]

end UnifIntegrable

section UniformIntegrable

/-! `UniformIntegrable`

In probability theory, uniform integrability normally refers to the condition that a sequence
of function `(fₙ)` satisfies for all `ε > 0`, there exists some `C ≥ 0` such that
`∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`.

In this section, we will develop some API for `UniformIntegrable` and prove that
`UniformIntegrable` is equivalent to this definition of uniform integrability.
-/


variable {p : Real>=0∞} {f : ι -> α -> β}

/--
theorem `uniformIntegrable_zero_meas` / 定理 `uniformIntegrable_zero_meas`

English:
theorem uniformIntegrable_zero_meas
  given: [MeasurableSpace α]
  statement: UniformIntegrable f p (0 : Measure α)
  proof: ⟨fun _ => aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, 0,
    fun _ => eLpNorm_measure_zero.le⟩

中文:
定理 uniform整数egrable_zero_meas
  条件: [可测空间 α]
  结论: Uniform整数egrable f p (0 : 测度 α)
  证明: ⟨fun _ => aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, 0,
    fun _ => eLpNorm_measure_zero.le⟩

Depends on / 依赖: aestronglyMeasurable_zero_measure, eLpNorm_measure_zero, eLpNorm_measure_zero.le, unifIntegrable_zero_meas
-/
theorem uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0 : Measure α) :=
  ⟨fun _ => aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, 0,
    fun _ => eLpNorm_measure_zero.le⟩

/--
theorem `UniformIntegrable.ae_eq` / 定理 `UniformIntegrable.ae_eq`

English:
theorem UniformIntegrable.ae_eq
  statement: {g : ι -> α -> β} (hf : UniformIntegrable f p μ)
  proof: by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← eLpNorm_congr_ae (hfg i)]
  exact hC i

中文:
定理 Uniform整数egrable.ae_eq
  结论: {g : ι -> α -> β} (hf : Uniform整数egrable f p μ)
  证明: by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← eLpNorm_congr_ae (hfg i)]
  exact hC i

Depends on / 依赖: eLpNorm_congr_ae, unifIntegrable_congr_ae
-/
theorem UniformIntegrable.ae_eq {g : ι -> α -> β} (hf : UniformIntegrable f p μ)
    (hfg : forall n, f n =ᵐ[μ] g n) : UniformIntegrable g p μ := by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← eLpNorm_congr_ae (hfg i)]
  exact hC i

/--
theorem `uniformIntegrable_congr_ae` / 定理 `uniformIntegrable_congr_ae`

English:
theorem uniformIntegrable_congr_ae
  given: {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n)
  proof: ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

中文:
定理 uniform整数egrable_congr_ae
  条件: {g : ι -> α -> β} (hfg : 对任意 n, f n =ᵐ[μ] g n)
  证明: ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

Depends on / 依赖: ae_eq, h.ae_eq
-/
theorem uniformIntegrable_congr_ae {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

/--
theorem `uniformIntegrable_finite` / 定理 `uniformIntegrable_finite`

English:
theorem uniformIntegrable_finite
  statement: [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  proof: by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => eLpNorm (f i) p μ).max'
      ⟨eLpNorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal]
    · exact Finset.le_max' (α := Real>=0∞) _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hf i
· exact ⟨0, fun i => False.elim hι Nonempty.intro i⟩

中文:
定理 uniform整数egrable_finite
  结论: [有限 ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  证明: by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => eLpNorm (f i) p μ).max'
      ⟨eLpNorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal]
    · exact Finset.le_max' (α := Real>=0∞) _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hf i
· exact ⟨0, fun i => False.elim hι Nonempty.intro i⟩

Depends on / 依赖: C.toNNReal, ENNReal, ENNReal.coe_toNNReal, Finset, Finset.le_max, Finset.max, Finset.mem_image, Finset.mem_univ, Finset.univ.image, Nonempty, _lt_iff, coe_toNNReal, eLpNorm, hp_one, hp_top, le_max, mem_image, mem_univ, ne_of_lt, nonempty_fintype
-/
theorem uniformIntegrable_finite [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞)
    (hf : forall i, MemLp (f i) p μ) : UniformIntegrable f p μ := by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => eLpNorm (f i) p μ).max'
      ⟨eLpNorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal]
    · exact Finset.le_max' (α := Real>=0∞) _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hf i
· exact ⟨0, fun i => False.elim hι Nonempty.intro i⟩

/--
theorem `uniformIntegrable_subsingleton` / 定理 `uniformIntegrable_subsingleton`

English:
theorem uniformIntegrable_subsingleton
  statement: [Subsingleton ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  proof: uniformIntegrable_finite hp_one hp_top hf

中文:
定理 uniform整数egrable_subsingleton
  结论: [子单例 ι] (hp_one : 1 <= p) (hp_top : p != ∞)
  证明: uniformIntegrable_finite hp_one hp_top hf

Depends on / 依赖: hp_one, hp_top, uniformIntegrable_finite
-/
theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 <= p) (hp_top : p != ∞)
    (hf : forall i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp_one hp_top hf

/--
theorem `uniformIntegrable_const` / 定理 `uniformIntegrable_const`

English:
theorem uniformIntegrable_const
  given: {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  proof: ⟨fun _ => hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(eLpNorm g p μ).toNNReal, fun _ => le_of_eq (ENNReal.coe_toNNReal hg.2.ne).symm⟩⟩

中文:
定理 uniform整数egrable_const
  条件: {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  证明: ⟨fun _ => hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(eLpNorm g p μ).toNNReal, fun _ => le_of_eq (ENNReal.coe_toNNReal hg.2.ne).symm⟩⟩

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, eLpNorm, hp_ne_top, le_of_eq, toNNReal, unifIntegrable_const
-/
theorem uniformIntegrable_const {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  ⟨fun _ => hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(eLpNorm g p μ).toNNReal, fun _ => le_of_eq (ENNReal.coe_toNNReal hg.2.ne).symm⟩⟩

/--
theorem `uniformIntegrable_of'` / 定理 `uniformIntegrable_of'`

English:
theorem uniformIntegrable_of'
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    eLpNorm (f i) p μ <=
        eLpNorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          eLpNorm ({ x : α | C <= ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (eLpNorm_mono_enorm fun x => ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply]; rw [Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_notMem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ <= (C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : forallᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ <= C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (eLpNorm_le_of_ae_bound this) ?_) (ENNReal.ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ENNReal.ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : Real>=0∞).toNNReal := by
      rw [ENNReal.coe_toNNReal (by finiteness)]

中文:
定理 uniform整数egrable_of'
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    eLpNorm (f i) p μ <=
        eLpNorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          eLpNorm ({ x : α | C <= ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (eLpNorm_mono_enorm fun x => ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply]; rw [Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_notMem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ <= (C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : forallᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ <= C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (eLpNorm_le_of_ae_bound this) ?_) (ENNReal.ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ENNReal.ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : Real>=0∞).toNNReal := by
      rw [ENNReal.coe_toNNReal (by finiteness)]

Depends on / 依赖: Set.univ, StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, aestronglyMeasurable, eLpNorm, eLpNorm_add_le, eLpNorm_mono_enorm, indicator, le_trans, one_pos, p.toReal, toNNReal, toReal, unifIntegrable_of
-/
theorem uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall i, StronglyMeasurable (f i))
    (h : forall ε : Real, 0 < ε -> exists C : Real>=0,
      forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    eLpNorm (f i) p μ <=
        eLpNorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          eLpNorm ({ x : α | C <= ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (eLpNorm_mono_enorm fun x => ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply]; rw [Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_notMem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ <= (C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : forallᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ <= C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (eLpNorm_le_of_ae_bound this) ?_) (ENNReal.ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ENNReal.ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : Real>=0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : Real>=0∞).toNNReal := by
      rw [ENNReal.coe_toNNReal (by finiteness)]

/--
theorem `uniformIntegrable_of` / 定理 `uniformIntegrable_of`

English:
theorem uniformIntegrable_of
  statement: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  set g : ι -> α -> β := fun i => (hf i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : forall i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

中文:
定理 uniform整数egrable_of
  结论: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  set g : ι -> α -> β := fun i => (hf i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : forall i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

Depends on / 依赖: Exists, Exists.choose_spec, StronglyMeasurable, ae_eq, choose_spec, eLpNorm_congr_ae, filter_upwards, hgmeas, le_of_eq, le_trans, uniformIntegrable_of
-/
theorem uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall i, AEStronglyMeasurable (f i) μ)
    (h : forall ε : Real, 0 < ε -> exists C : Real>=0,
      forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  set g : ι -> α -> β := fun i => (hf i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : forall i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/--
theorem `UniformIntegrable.spec'` / 定理 `UniformIntegrable.spec'`

English:
theorem UniformIntegrable.spec'
  statement: (hp : p != 0) (hp' : p != ∞) (hf : forall i, StronglyMeasurable (f i))
  proof: by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := hfu hε
  obtain ⟨C, hC⟩ : exists C : Real>=0, forall i, μ { x | C <= ‖f i x‖₊ } <= ENNReal.ofReal δ := by
    by_contra! hcon
    choose ℐ hℐ using hcon
    lift δ to Real>=0 using hδpos.le
    have : forall C : Real>=0, C • (δ : Real>=0∞) ^ (1 / p.toReal) <= eLpNorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : Real>=0∞) ^ (1 / p.toReal) <= C • μ { x | C <= ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [smul_eq_mul]
          simp_rw [ENNReal.ofReal_coe_nnreal] at hℐ
          refine mul_le_mul' le_rfl
            (ENNReal.rpow_le_rpow (hℐ C).le (one_div_nonneg.2 ENNReal.toReal_nonneg))
        _ <= eLpNorm ({ x | C <= ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine le_eLpNorm_of_bddBelow hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (Eventually.of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ <= eLpNorm (f (ℐ C)) p μ := eLpNorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal))
    rw [← ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.2 ENNReal.toReal_nonneg)]; rw [← ENNReal.coe_smul]; rw [smul_eq_mul]; rw [mul_assoc]; rw [NNReal.inv_rpow]; rw [inv_mul_cancel₀ (NNReal.rpow_pos (NNReal.coe_pos.1 hδpos)).ne.symm]; rw [mul_one]; rw [ENNReal.coe_mul]; rw [← NNReal.inv_rpow] at this
    refine (lt_of_le_of_lt (le_trans
      (hM <| ℐ <| 2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)) (le_max_left (M : Real>=0∞) 1))
        (lt_of_lt_of_le ?_ this)).ne rfl
    rw [← ENNReal.coe_one]; rw [← ENNReal.coe_max]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_lt_coe]
    exact lt_two_mul_self (lt_max_of_lt_right one_pos)
  exact ⟨C, fun i => hδ i _ (measurableSet_le measurable_const (hf i).nnnorm.measurable) (hC i)⟩

中文:
定理 Uniform整数egrable.spec'
  结论: (hp : p != 0) (hp' : p != ∞) (hf : 对任意 i, StronglyMeasurable (f i))
  证明: by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := hfu hε
  obtain ⟨C, hC⟩ : exists C : Real>=0, forall i, μ { x | C <= ‖f i x‖₊ } <= ENNReal.ofReal δ := by
    by_contra! hcon
    choose ℐ hℐ using hcon
    lift δ to Real>=0 using hδpos.le
    have : forall C : Real>=0, C • (δ : Real>=0∞) ^ (1 / p.toReal) <= eLpNorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : Real>=0∞) ^ (1 / p.toReal) <= C • μ { x | C <= ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [smul_eq_mul]
          simp_rw [ENNReal.ofReal_coe_nnreal] at hℐ
          refine mul_le_mul' le_rfl
            (ENNReal.rpow_le_rpow (hℐ C).le (one_div_nonneg.2 ENNReal.toReal_nonneg))
        _ <= eLpNorm ({ x | C <= ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine le_eLpNorm_of_bddBelow hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (Eventually.of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ <= eLpNorm (f (ℐ C)) p μ := eLpNorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal))
    rw [← ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.2 ENNReal.toReal_nonneg)]; rw [← ENNReal.coe_smul]; rw [smul_eq_mul]; rw [mul_assoc]; rw [NNReal.inv_rpow]; rw [inv_mul_cancel₀ (NNReal.rpow_pos (NNReal.coe_pos.1 hδpos)).ne.symm]; rw [mul_one]; rw [ENNReal.coe_mul]; rw [← NNReal.inv_rpow] at this
    refine (lt_of_le_of_lt (le_trans
      (hM <| ℐ <| 2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)) (le_max_left (M : Real>=0∞) 1))
        (lt_of_lt_of_le ?_ this)).ne rfl
    rw [← ENNReal.coe_one]; rw [← ENNReal.coe_max]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_lt_coe]
    exact lt_two_mul_self (lt_max_of_lt_right one_pos)
  exact ⟨C, fun i => hδ i _ (measurableSet_le measurable_const (hf i).nnnorm.measurable) (hC i)⟩

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.smul_def, eLpNorm, ofReal, p.toReal, pos.le, smul_def, smul_eq_mul, toReal
-/
theorem UniformIntegrable.spec' (hp : p != 0) (hp' : p != ∞) (hf : forall i, StronglyMeasurable (f i))
    (hfu : UniformIntegrable f p μ) {ε : Real} (hε : 0 < ε) :
    exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε := by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := hfu hε
  obtain ⟨C, hC⟩ : exists C : Real>=0, forall i, μ { x | C <= ‖f i x‖₊ } <= ENNReal.ofReal δ := by
    by_contra! hcon
    choose ℐ hℐ using hcon
    lift δ to Real>=0 using hδpos.le
    have : forall C : Real>=0, C • (δ : Real>=0∞) ^ (1 / p.toReal) <= eLpNorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : Real>=0∞) ^ (1 / p.toReal) <= C • μ { x | C <= ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [smul_eq_mul]
          simp_rw [ENNReal.ofReal_coe_nnreal] at hℐ
          refine mul_le_mul' le_rfl
            (ENNReal.rpow_le_rpow (hℐ C).le (one_div_nonneg.2 ENNReal.toReal_nonneg))
        _ <= eLpNorm ({ x | C <= ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine le_eLpNorm_of_bddBelow hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (Eventually.of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ <= eLpNorm (f (ℐ C)) p μ := eLpNorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal))
    rw [← ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.2 ENNReal.toReal_nonneg)]; rw [← ENNReal.coe_smul]; rw [smul_eq_mul]; rw [mul_assoc]; rw [NNReal.inv_rpow]; rw [inv_mul_cancel₀ (NNReal.rpow_pos (NNReal.coe_pos.1 hδpos)).ne.symm]; rw [mul_one]; rw [ENNReal.coe_mul]; rw [← NNReal.inv_rpow] at this
    refine (lt_of_le_of_lt (le_trans
      (hM <| ℐ <| 2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)) (le_max_left (M : Real>=0∞) 1))
        (lt_of_lt_of_le ?_ this)).ne rfl
    rw [← ENNReal.coe_one]; rw [← ENNReal.coe_max]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_lt_coe]
    exact lt_two_mul_self (lt_max_of_lt_right one_pos)
  exact ⟨C, fun i => hδ i _ (measurableSet_le measurable_const (hf i).nnnorm.measurable) (hC i)⟩

/--
theorem `UniformIntegrable.spec` / 定理 `UniformIntegrable.spec`

English:
theorem UniformIntegrable.spec
  statement: (hp : p != 0) (hp' : p != ∞) (hfu : UniformIntegrable f p μ) {ε : Real}
  proof: by
  set g : ι -> α -> β := fun i => (hfu.1 i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

中文:
定理 Uniform整数egrable.spec
  结论: (hp : p != 0) (hp' : p != ∞) (hfu : Uniform整数egrable f p μ) {ε : 实数}
  证明: by
  set g : ι -> α -> β := fun i => (hfu.1 i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

Depends on / 依赖: Exists, Exists.choose_spec, Set.i, Set.indicator_of_mem, StronglyMeasurable, UniformIntegrable, ae_eq, choose_spec, eLpNorm_congr_ae, filter_upwards, hfu.ae_eq, hgmeas, hgunif, hgunif.spec, indicator_of_mem, le_of_eq, le_trans
-/
theorem UniformIntegrable.spec (hp : p != 0) (hp' : p != ∞) (hfu : UniformIntegrable f p μ) {ε : Real}
    (hε : 0 < ε) :
    exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε := by
  set g : ι -> α -> β := fun i => (hfu.1 i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x in { x | C <= ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/--
theorem `uniformIntegrable_iff` / 定理 `uniformIntegrable_iff`

English:
theorem uniformIntegrable_iff
  given: [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞)
  proof: ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne.symm hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

中文:
定理 uniform整数egrable_iff
  条件: [是有限测度 μ] (hp : 1 <= p) (hp' : p != ∞)
  证明: ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne.symm hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

Depends on / 依赖: h.spec, lt_of_lt_of_le, ne.symm, uniformIntegrable_of, zero_lt_one
-/
theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) :
    UniformIntegrable f p μ ↔
      (forall i, AEStronglyMeasurable (f i) μ) ∧
        forall ε : Real, 0 < ε -> exists C : Real>=0,
          forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε :=
  ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne.symm hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

/--
theorem `uniformIntegrable_average` / 定理 `uniformIntegrable_average`

English:
theorem uniformIntegrable_average
  proof: by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n => ?_, fun ε hε => ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := hf₂ hε
    refine ⟨δ, hδ₁, fun n s hs hle => ?_⟩
    simp_rw [Finset.smul_sum, Finset.indicator_sum]
    refine le_trans (eLpNorm_sum_le (fun i _ => ((hf₁ i).const_smul _).indicator hs) hp) ?_
    have this i : s.indicator ((n : Real)⁻¹ • f i) = (↑n : Real)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [this, eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hδ₂ _ _ hs hle
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (eLpNorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hC i

中文:
定理 uniform整数egrable_average
  证明: by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n => ?_, fun ε hε => ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := hf₂ hε
    refine ⟨δ, hδ₁, fun n s hs hle => ?_⟩
    simp_rw [Finset.smul_sum, Finset.indicator_sum]
    refine le_trans (eLpNorm_sum_le (fun i _ => ((hf₁ i).const_smul _).indicator hs) hp) ?_
    have this i : s.indicator ((n : Real)⁻¹ • f i) = (↑n : Real)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [this, eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hδ₂ _ _ hs hle
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (eLpNorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hC i

Depends on / 依赖: Finset, Finset.aestronglyMeasurable_sum, Finset.indicator_sum, Finset.smul_sum, aestronglyMeasurable_sum, const_smul, eLpNorm_sum_le, eq_or_ne, indicator, indicator_const_smul, indicator_sum, le_trans, s.indicator, simp_rw, smul_sum
-/
theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (hp : 1 <= p) {f : Nat -> α -> E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : Nat) => (n : Real)⁻¹ • (∑ i in Finset.range n, f i)) p μ := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n => ?_, fun ε hε => ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := hf₂ hε
    refine ⟨δ, hδ₁, fun n s hs hle => ?_⟩
    simp_rw [Finset.smul_sum, Finset.indicator_sum]
    refine le_trans (eLpNorm_sum_le (fun i _ => ((hf₁ i).const_smul _).indicator hs) hp) ?_
    have this i : s.indicator ((n : Real)⁻¹ • f i) = (↑n : Real)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [this, eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hδ₂ _ _ hs hle
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (eLpNorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity)]; rw [Real.enorm_natCast]; rw [← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hC i

/--
theorem `uniformIntegrable_average_real` / 定理 `uniformIntegrable_average_real`

English:
theorem uniformIntegrable_average_real
  given: (hp : 1 <= p) {f : Nat -> α -> Real} (hf : UniformIntegrable f p μ)
  proof: by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

中文:
定理 uniform整数egrable_average_real
  条件: (hp : 1 <= p) {f : 自然数 -> α -> 实数} (hf : Uniform整数egrable f p μ)
  证明: by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

Depends on / 依赖: convert, div_eq_inv_mul, uniformIntegrable_average
-/
theorem uniformIntegrable_average_real (hp : 1 <= p) {f : Nat -> α -> Real} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i in Finset.range n, f i) / (n : α -> Real)) p μ := by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

/--
lemma `UniformIntegrable.uniformIntegrable_of_tendstoInMeasure` / 引理 `UniformIntegrable.uniformIntegrable_of_tendstoInMeasure`

English:
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure
  statement: {κ : Type*} (u : Filter κ) [NeBot u]
  proof: by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure u (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => hC (s n)) hs (fun n => hUI.1 (s n))⟩

中文:
引理 Uniform整数egrable.uniform整数egrable_of_tendstoInMeasure
  结论: {κ : 类型} (u : 滤子 κ) [NeBot u]
  证明: by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure u (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => hC (s n)) hs (fun n => hUI.1 (s n))⟩

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, eLpNorm_le_of_tendstoInMeasure, hs.aestronglyMeasurable, of_forall, unifIntegrable_of_tendstoInMeasure
-/
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι -> α -> β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α -> β | exists ni : κ -> ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) => f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure u (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => hC (s n)) hs (fun n => hUI.1 (s n))⟩

/--
lemma `UniformIntegrable.memLp_of_tendstoInMeasure` / 引理 `UniformIntegrable.memLp_of_tendstoInMeasure`

English:
lemma UniformIntegrable.memLp_of_tendstoInMeasure
  statement: {κ : Type*} {u : Filter κ} [NeBot u]
  proof: by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

中文:
引理 Uniform整数egrable.memLp_of_tendstoInMeasure
  结论: {κ : 类型} {u : 滤子 κ} [NeBot u]
  证明: by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

Depends on / 依赖: hUI.uniformIntegrable_of_tendstoInMeasure, htends, uniformIntegrable_of_tendstoInMeasure
-/
lemma UniformIntegrable.memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ -> α -> β} {g : α -> β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/--
lemma `UniformIntegrable.integrable_of_tendstoInMeasure` / 引理 `UniformIntegrable.integrable_of_tendstoInMeasure`

English:
lemma UniformIntegrable.integrable_of_tendstoInMeasure
  statement: {κ : Type*} {u : Filter κ} [NeBot u]
  proof: memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

中文:
引理 Uniform整数egrable.integrable_of_tendstoInMeasure
  结论: {κ : 类型} {u : 滤子 κ} [NeBot u]
  证明: memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

Depends on / 依赖: hUI.memLp_of_tendstoInMeasure, htends, memLp_of_tendstoInMeasure, memLp_one_iff_integrable, memLp_one_iff_integrable.mp
-/
lemma UniformIntegrable.integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ -> α -> β} {g : α -> β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

/--
lemma `UniformIntegrable.uniformIntegrable_of_ae_tendsto` / 引理 `UniformIntegrable.uniformIntegrable_of_ae_tendsto`

English:
lemma UniformIntegrable.uniformIntegrable_of_ae_tendsto
  statement: {κ : Type*} (u : Filter κ) [NeBot u]
  proof: by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_ae_tendsto u (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae u (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hC (s n)) (fun n => hUI.1 (s n)) hs⟩

中文:
引理 Uniform整数egrable.uniform整数egrable_of_ae_tendsto
  结论: {κ : 类型} (u : 滤子 κ) [NeBot u]
  证明: by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_ae_tendsto u (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae u (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hC (s n)) (fun n => hUI.1 (s n)) hs⟩

Depends on / 依赖: Eventually, Eventually.of_forall, Lp.eLpNorm_le_of_ae_tendsto, aestronglyMeasurable_of_tendsto_ae, eLpNorm_le_of_ae_tendsto, of_forall, unifIntegrable_of_ae_tendsto
-/
lemma UniformIntegrable.uniformIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι -> α -> β}
    (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α -> β | exists ni : κ -> ι,
      forallᵐ (x : α) ∂μ, Tendsto (fun n => fn (ni n) x) u (𝓝 (g x))}) => f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_ae_tendsto u (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae u (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hC (s n)) (fun n => hUI.1 (s n)) hs⟩

/--
lemma `UniformIntegrable.memLp_of_ae_tendsto` / 引理 `UniformIntegrable.memLp_of_ae_tendsto`

English:
lemma UniformIntegrable.memLp_of_ae_tendsto
  statement: {κ : Type*} {u : Filter κ} [NeBot u]
  proof: by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

中文:
引理 Uniform整数egrable.memLp_of_ae_tendsto
  结论: {κ : 类型} {u : 滤子 κ} [NeBot u]
  证明: by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

Depends on / 依赖: hUI.uniformIntegrable_of_ae_tendsto, htends, uniformIntegrable_of_ae_tendsto
-/
lemma UniformIntegrable.memLp_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ -> α -> β} {g : α -> β} (hUI : UniformIntegrable f p μ)
    (htends : forallᵐ (x : α) ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/--
lemma `UniformIntegrable.integrable_of_ae_tendsto` / 引理 `UniformIntegrable.integrable_of_ae_tendsto`

English:
lemma UniformIntegrable.integrable_of_ae_tendsto
  statement: {κ : Type*} {u : Filter κ} [NeBot u]
  proof: memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

中文:
引理 Uniform整数egrable.integrable_of_ae_tendsto
  结论: {κ : 类型} {u : 滤子 κ} [NeBot u]
  证明: memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

Depends on / 依赖: hUI.memLp_of_ae_tendsto, htends, memLp_of_ae_tendsto, memLp_one_iff_integrable, memLp_one_iff_integrable.mp
-/
lemma UniformIntegrable.integrable_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ -> α -> β} {g : α -> β} (hUI : UniformIntegrable f 1 μ)
    (htends : forallᵐ (x : α) ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

end UniformIntegrable

end MeasureTheory
