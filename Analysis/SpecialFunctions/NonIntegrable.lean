/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Non-integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` and
`not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`. Then we apply the
latter lemma to prove that the function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`.

## Main results

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`: a version of
  `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured` that works for one-sided
  neighborhoods;

* `not_intervalIntegrable_of_sub_inv_isBigO_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `intervalIntegrable_sub_inv_iff`, `intervalIntegrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/

public section


open scoped MeasureTheory Topology Interval NNReal ENNReal

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F]

/--
theorem `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux` / 定理 `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux`

English:
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
  proof: by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    exists (C : Real) (_ : 0 <= C), exists s in l, (forall x in s, forall y in s, [[x, y]] subseteq k) ∧
      (forall x in s, forall y in s, forall z in [[x, y]], DifferentiableAt Real f z) ∧
        forall x in s, forall y in s, forall z in [[x, y]], ‖deriv f z‖ <= C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : forallᶠ x : Real × Real in l ×ˢ l,
        forall y in [[x.1, x.2]], (DifferentiableAt Real f y ∧ ‖deriv f y‖ <= C * ‖g y‖) ∧ y in k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_ofPred_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x => C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : exists c in s, exists d in s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : forallᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : forall x in Ι c d, ‖deriv f x‖ <= C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : forallᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ <= C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d subseteq k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x => C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_ge (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ <= ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_uIoc _
    _ <= ∫ x in Ι c d, ‖deriv f x‖ := norm_integral_le_integral_norm _
    _ <= ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ <= ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallyLE

中文:
定理 not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
  证明: by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    exists (C : Real) (_ : 0 <= C), exists s in l, (forall x in s, forall y in s, [[x, y]] subseteq k) ∧
      (forall x in s, forall y in s, forall z in [[x, y]], DifferentiableAt Real f z) ∧
        forall x in s, forall y in s, forall z in [[x, y]], ‖deriv f z‖ <= C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : forallᶠ x : Real × Real in l ×ˢ l,
        forall y in [[x.1, x.2]], (DifferentiableAt Real f y ∧ ‖deriv f y‖ <= C * ‖g y‖) ∧ y in k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_ofPred_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x => C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : exists c in s, exists d in s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : forallᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : forall x in Ι c d, ‖deriv f x‖ <= C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : forallᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ <= C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d subseteq k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x => C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_ge (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ <= ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_uIoc _
    _ <= ∫ x in Ι c d, ‖deriv f x‖ := norm_integral_le_integral_norm _
    _ <= ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ <= ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallyLE

Depends on / 依赖: DifferentiableAt, exists_nonneg, hfg.exists_nonneg, subseteq
-/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
    [CompleteSpace E] {f : Real -> E} {g : Real -> F}
    {k : Set Real} (l : Filter Real) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k in l) (hd : forallᶠ x in l, DifferentiableAt Real f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    exists (C : Real) (_ : 0 <= C), exists s in l, (forall x in s, forall y in s, [[x, y]] subseteq k) ∧
      (forall x in s, forall y in s, forall z in [[x, y]], DifferentiableAt Real f z) ∧
        forall x in s, forall y in s, forall z in [[x, y]], ‖deriv f z‖ <= C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : forallᶠ x : Real × Real in l ×ˢ l,
        forall y in [[x.1, x.2]], (DifferentiableAt Real f y ∧ ‖deriv f y‖ <= C * ‖g y‖) ∧ y in k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_ofPred_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x => C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : exists c in s, exists d in s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : forallᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : forall x in Ι c d, ‖deriv f x‖ <= C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : forallᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ <= C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d subseteq k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x => C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_ge (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ <= ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_uIoc _
    _ <= ∫ x in Ι c d, ‖deriv f x‖ := norm_integral_le_integral_norm _
    _ <= ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ <= ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallyLE

/--
theorem `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` / 定理 `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter`

English:
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
  proof: by
  let a : E ->ₗᵢ[Real] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have h'd : forallᶠ x in l, DifferentiableAt Real f' x := by
    filter_upwards [hd] with x hx using a.toContinuousLinearMap.differentiableAt.comp x hx
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x => by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x => ‖deriv f' x‖) =ᶠ[l] (fun x => ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    have : deriv f' x = a (deriv f x) := by
      rw [fderiv_comp_deriv x _ hx]
      · have : fderiv Real a (f x) = a.toContinuousLinearMap := a.toContinuousLinearMap.fderiv
        simp only [this]
        rfl
      · exact a.toContinuousLinearMap.differentiableAt
    simp only [this]
    simp
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

中文:
定理 not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
  证明: by
  let a : E ->ₗᵢ[Real] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have h'd : forallᶠ x in l, DifferentiableAt Real f' x := by
    filter_upwards [hd] with x hx using a.toContinuousLinearMap.differentiableAt.comp x hx
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x => by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x => ‖deriv f' x‖) =ᶠ[l] (fun x => ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    have : deriv f' x = a (deriv f x) := by
      rw [fderiv_comp_deriv x _ hx]
      · have : fderiv Real a (f x) = a.toContinuousLinearMap := a.toContinuousLinearMap.fderiv
        simp only [this]
        rfl
      · exact a.toContinuousLinearMap.differentiableAt
    simp only [this]
    simp
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

Depends on / 依赖: Completion, DifferentiableAt, IsBigO, IsBigO.trans, Tendsto, UniformSpace, UniformSpace.Completion, UniformSpace.Completion.toCompl, a.toContinuousLinearMap.differentiableAt.comp, differentiableAt, filter_upwards, hf.congr, isBigO, isBigO_norm_norm, this.isBigO, toContinuousLinearMap
-/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    {f : Real -> E} {g : Real -> F}
    {k : Set Real} (l : Filter Real) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k in l) (hd : forallᶠ x in l, DifferentiableAt Real f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  let a : E ->ₗᵢ[Real] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have h'd : forallᶠ x in l, DifferentiableAt Real f' x := by
    filter_upwards [hd] with x hx using a.toContinuousLinearMap.differentiableAt.comp x hx
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x => by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x => ‖deriv f' x‖) =ᶠ[l] (fun x => ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    have : deriv f' x = a (deriv f x) := by
      rw [fderiv_comp_deriv x _ hx]
      · have : fderiv Real a (f x) = a.toContinuousLinearMap := a.toContinuousLinearMap.fderiv
        simp only [this]
        rfl
      · exact a.toContinuousLinearMap.differentiableAt
    simp only [this]
    simp
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

/--
theorem `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` / 定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`

English:
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter
  statement: {f : Real -> E} {g : Real -> F}
  proof: by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg

中文:
定理 not_interval整数egrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter
  结论: {f : 实数 -> E} {g : 实数 -> F}
  证明: by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg

Depends on / 依赖: intervalIntegrable_iff, not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : Real -> E} {g : Real -> F}
    {a b : Real} (l : Filter Real) [NeBot l] [TendstoIxxClass Icc l l] (hl : [[a, b]] in l)
    (hd : forallᶠ x in l, DifferentiableAt Real f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg

/--
theorem `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton` / 定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton`

English:
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
  proof: by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    exists l : Filter Real, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l <= 𝓝 c ∧ [[a, b]] \ {c} in l := by
    rcases (min_lt_max.2 hne).gt_or_lt c with hlt | hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_sdiff_right]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsLE_of_mem ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_sdiff_left]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsGE_of_mem ⟨hc.1, hlt⟩) _
  have : l <= 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem sdiff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)

中文:
定理 not_interval整数egrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
  证明: by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    exists l : Filter Real, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l <= 𝓝 c ∧ [[a, b]] \ {c} in l := by
    rcases (min_lt_max.2 hne).gt_or_lt c with hlt | hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_sdiff_right]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsLE_of_mem ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_sdiff_left]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsGE_of_mem ⟨hc.1, hlt⟩) _
  have : l <= 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem sdiff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)

Depends on / 依赖: Filter, Icc_mem_nhdsGE_of_mem, Icc_mem_nhdsLE_of_mem, Ici_sdiff_left, Iic_sdiff_right, TendstoIxxClass, gt_or_lt, inf_le_left, l.NeBot, min_lt_max, sdiff_mem_nhdsWithin_sdiff
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    {f : Real -> E} {g : Real -> F} {a b c : Real} (hne : a != b) (hc : c in [[a, b]])
    (h_deriv : forallᶠ x in 𝓝[[[a, b]] \ {c}] c, DifferentiableAt Real f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c) atTop)
    (hg : deriv f =O[𝓝[[[a, b]] \ {c}] c] g) : ¬IntervalIntegrable g volume a b := by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    exists l : Filter Real, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l <= 𝓝 c ∧ [[a, b]] \ {c} in l := by
    rcases (min_lt_max.2 hne).gt_or_lt c with hlt | hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_sdiff_right]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsLE_of_mem ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_sdiff_left]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsGE_of_mem ⟨hc.1, hlt⟩) _
  have : l <= 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem sdiff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)

/--
theorem `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured` / 定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`

English:
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
  statement: {f : Real -> E}
  proof: have : 𝓝[[[a, b]] \ {c}] c <= 𝓝[!=] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

中文:
定理 not_interval整数egrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
  结论: {f : 实数 -> E}
  证明: have : 𝓝[[[a, b]] \ {c}] c <= 𝓝[!=] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

Depends on / 依赖: filter_mono, h_deriv, h_deriv.filter_mono, h_infty, h_infty.mono_left, hg.mono, inter_subset_right, mono_left, nhdsWithin_mono, not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f : Real -> E}
    {g : Real -> F} {a b c : Real} (h_deriv : forallᶠ x in 𝓝[!=] c, DifferentiableAt Real f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[!=] c) atTop) (hg : deriv f =O[𝓝[!=] c] g) (hne : a != b)
    (hc : c in [[a, b]]) : ¬IntervalIntegrable g volume a b :=
  have : 𝓝[[[a, b]] \ {c}] c <= 𝓝[!=] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

/--
theorem `not_intervalIntegrable_of_sub_inv_isBigO_punctured` / 定理 `not_intervalIntegrable_of_sub_inv_isBigO_punctured`

English:
theorem not_intervalIntegrable_of_sub_inv_isBigO_punctured
  statement: {f : Real -> F} {a b c : Real}
  proof: by
  have A : forallᶠ x in 𝓝[!=] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[!=] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_nhdsNE one_ne_zero
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B
    (hf.congr' (A.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl) hne hc

中文:
定理 not_interval整数egrable_of_sub_inv_isBigO_punctured
  结论: {f : 实数 -> F} {a b c : 实数}
  证明: by
  have A : forallᶠ x in 𝓝[!=] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[!=] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_nhdsNE one_ne_zero
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B
    (hf.congr' (A.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl) hne hc

Depends on / 依赖: HasDerivAt, Real.log, Real.tendsto_log_nhdsNE_zero.comp, Tendsto, filter_upwards, hasDerivAt_id, not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_p, one_ne_zero, self_mem_nhdsWithin, sub_const, sub_ne_zero, sub_self, tendsto_abs_atBot_atTop, tendsto_abs_atBot_atTop.comp, tendsto_log_nhdsNE_zero, tendsto_nhdsNE
-/
theorem not_intervalIntegrable_of_sub_inv_isBigO_punctured {f : Real -> F} {a b c : Real}
    (hf : (fun x => (x - c)⁻¹) =O[𝓝[!=] c] f) (hne : a != b) (hc : c in [[a, b]]) :
    ¬IntervalIntegrable f volume a b := by
  have A : forallᶠ x in 𝓝[!=] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[!=] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_nhdsNE one_ne_zero
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B
    (hf.congr' (A.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl) hne hc

/-- The function `fun x => (x - c)⁻¹` is integrable on `a..b` if and only if
`a = b` or `c ∉ [a, b]`. -/
@[simp]
/--
theorem `intervalIntegrable_sub_inv_iff` / 定理 `intervalIntegrable_sub_inv_iff`

English:
theorem intervalIntegrable_sub_inv_iff
  given: {a b c : Real}
  proof: by
  constructor
  · refine fun h => or_iff_not_imp_left.2 fun hne hc => ?_
    exact not_intervalIntegrable_of_sub_inv_isBigO_punctured (isBigO_refl _ _) hne hc h
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    refine ((continuous_sub_right c).continuousOn.inv₀ ?_).intervalIntegrable
exact fun x hx => sub_ne_zero.2 ne_of_mem_of_not_mem hx h₀

中文:
定理 interval整数egrable_sub_inv_iff
  条件: {a b c : 实数}
  证明: by
  constructor
  · refine fun h => or_iff_not_imp_left.2 fun hne hc => ?_
    exact not_intervalIntegrable_of_sub_inv_isBigO_punctured (isBigO_refl _ _) hne hc h
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    refine ((continuous_sub_right c).continuousOn.inv₀ ?_).intervalIntegrable
exact fun x hx => sub_ne_zero.2 ne_of_mem_of_not_mem hx h₀

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.refl, continuousOn, continuousOn.inv, continuous_sub_right, intervalIntegrable, isBigO_refl, ne_of_mem_of_not_mem, not_intervalIntegrable_of_sub_inv_isBigO_punctured, or_iff_not_imp_left, sub_ne_zero
-/
theorem intervalIntegrable_sub_inv_iff {a b c : Real} :
    IntervalIntegrable (fun x => (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [[a, b]] := by
  constructor
  · refine fun h => or_iff_not_imp_left.2 fun hne hc => ?_
    exact not_intervalIntegrable_of_sub_inv_isBigO_punctured (isBigO_refl _ _) hne hc h
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    refine ((continuous_sub_right c).continuousOn.inv₀ ?_).intervalIntegrable
exact fun x hx => sub_ne_zero.2 ne_of_mem_of_not_mem hx h₀

/-- The function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`. -/
@[simp]
/--
theorem `intervalIntegrable_inv_iff` / 定理 `intervalIntegrable_inv_iff`

English:
theorem intervalIntegrable_inv_iff
  given: {a b : Real}
  proof: by
  simp only [← intervalIntegrable_sub_inv_iff, sub_zero]

中文:
定理 interval整数egrable_inv_iff
  条件: {a b : 实数}
  证明: by
  simp only [← intervalIntegrable_sub_inv_iff, sub_zero]

Depends on / 依赖: intervalIntegrable_sub_inv_iff, sub_zero
-/
theorem intervalIntegrable_inv_iff {a b : Real} :
    IntervalIntegrable (fun x => x⁻¹) volume a b ↔ a = b ∨ (0 : Real) ∉ [[a, b]] := by
  simp only [← intervalIntegrable_sub_inv_iff, sub_zero]

/--
theorem `not_integrableOn_Ici_inv` / 定理 `not_integrableOn_Ici_inv`

English:
theorem not_integrableOn_Ici_inv
  given: {a : Real}
  proof: by
  have A : forallᶠ x in atTop, HasDerivAt (fun x => Real.log x) x⁻¹ x := by
    filter_upwards [Ioi_mem_atTop 0] with x hx using Real.hasDerivAt_log (ne_of_gt hx)
  have B : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop (Ici_mem_atTop a)
    (A.mono (fun x hx => hx.differentiableAt)) B
    (Filter.EventuallyEq.isBigO (A.mono (fun x hx => hx.deriv)))

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ici_inv := not_integrableOn_Ici_inv

中文:
定理 not_integrableOn_Ici_inv
  条件: {a : 实数}
  证明: by
  have A : forallᶠ x in atTop, HasDerivAt (fun x => Real.log x) x⁻¹ x := by
    filter_upwards [Ioi_mem_atTop 0] with x hx using Real.hasDerivAt_log (ne_of_gt hx)
  have B : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop (Ici_mem_atTop a)
    (A.mono (fun x hx => hx.differentiableAt)) B
    (Filter.EventuallyEq.isBigO (A.mono (fun x hx => hx.deriv)))

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ici_inv := not_integrableOn_Ici_inv

Depends on / 依赖: A.mono, EventuallyEq, Filter, Filter.EventuallyEq.isBigO, HasDerivAt, Ici_mem_atTop, Ioi_mem_atTop, Real.hasDerivAt_log, Real.log, Real.tendsto_log_atTop, Tendsto, differentiableAt, filter_upwards, hasDerivAt_log, hx.deriv, hx.differentiableAt, isBigO, ne_of_gt, not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter, tendsto_log_atTop
-/
theorem not_integrableOn_Ici_inv {a : Real} :
    ¬ IntegrableOn (fun x => x⁻¹) (Ici a) := by
  have A : forallᶠ x in atTop, HasDerivAt (fun x => Real.log x) x⁻¹ x := by
    filter_upwards [Ioi_mem_atTop 0] with x hx using Real.hasDerivAt_log (ne_of_gt hx)
  have B : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop (Ici_mem_atTop a)
    (A.mono (fun x hx => hx.differentiableAt)) B
    (Filter.EventuallyEq.isBigO (A.mono (fun x hx => hx.deriv)))

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ici_inv := not_integrableOn_Ici_inv

/--
theorem `not_integrableOn_Ioi_inv` / 定理 `not_integrableOn_Ioi_inv`

English:
theorem not_integrableOn_Ioi_inv
  given: {a : Real}
  proof: by
  simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using not_integrableOn_Ici_inv

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ioi_inv := not_integrableOn_Ioi_inv

中文:
定理 not_integrableOn_Ioi_inv
  条件: {a : 实数}
  证明: by
  simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using not_integrableOn_Ici_inv

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ioi_inv := not_integrableOn_Ioi_inv

Depends on / 依赖: IntegrableOn, not_integrableOn_Ici_inv, restrict_Ioi_eq_restrict_Ici
-/
theorem not_integrableOn_Ioi_inv {a : Real} :
    ¬ IntegrableOn (·⁻¹) (Ioi a) := by
  simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using not_integrableOn_Ici_inv

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ioi_inv := not_integrableOn_Ioi_inv
