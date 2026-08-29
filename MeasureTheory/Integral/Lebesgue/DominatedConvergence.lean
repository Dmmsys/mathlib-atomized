/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Dominated convergence theorem

Lebesgue's dominated convergence theorem states that the limit and Lebesgue integral of
a sequence of (almost everywhere) measurable functions can be swapped if the functions are
pointwise dominated by a fixed function. This file provides a few variants of the result.
-/

public section

open Filter ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/--
theorem `limsup_lintegral_le` / 定理 `limsup_lintegral_le`

English:
theorem limsup_lintegral_le
  statement: {f : Nat -> α -> Real>=0∞} (g : α -> Real>=0∞) (hf_meas : forall n, Measurable (f n))
  proof: calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : Nat, ⨆ i >= n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ <= ⨅ n : Nat, ∫⁻ a, ⨆ i >= n, f i a ∂μ := iInf_mono fun _ => iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : Nat, ⨆ i >= n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).s

中文:
定理 limsup_lintegral_le
  结论: {f : 自然数 -> α -> 实数>=0∞} (g : α -> 实数>=0∞) (hf_meas : 对任意 n, 可测 (f n))
  证明: calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : Nat, ⨆ i >= n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ <= ⨅ n : Nat, ∫⁻ a, ⨆ i >= n, f i a ∂μ := iInf_mono fun _ => iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : Nat, ⨆ i >= n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).s

Depends on / 依赖: Set.to_countable, ae_all_iff, h_fin, hf_meas, iInf_mono, iSup_le_iSup_of_subset, le_trans, limsup, limsup_eq_iInf_iSup_of_nat, lintegral_iInf, lintegral_mono_ae, ne_top_of_le_ne_top, to_countable
-/
theorem limsup_lintegral_le {f : Nat -> α -> Real>=0∞} (g : α -> Real>=0∞) (hf_meas : forall n, Measurable (f n))
    (h_bound : forall n, f n <=ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ != ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop <= ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : Nat, ⨆ i >= n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ <= ⨅ n : Nat, ∫⁻ a, ⨆ i >= n, f i a ∂μ := iInf_mono fun _ => iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : Nat, ⨆ i >= n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).symm
      · intro n
        exact .biSup _ (Set.to_countable _) (fun i _ => hf_meas i)
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
      · refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae ?_)
        refine (ae_all_iff.2 h_bound).mono fun n hn => ?_
        exact iSup_le fun i => iSup_le fun _ => hn i
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]

/--
theorem `tendsto_lintegral_of_dominated_convergence` / 定理 `tendsto_lintegral_of_dominated_convergence`

English:
theorem tendsto_lintegral_of_dominated_convergence
  statement: {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞}
  proof: tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : Nat => F n a) atTop ∂μ :=
lintegral_congr_ae h_lim.mono fun _ h => h.liminf_eq.symm
      _ <= liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : Nat => ∫⁻ a, F 

中文:
定理 tendsto_lintegral_of_dominated_convergence
  结论: {F : 自然数 -> α -> 实数>=0∞} {f : α -> 实数>=0∞}
  证明: tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : Nat => F n a) atTop ∂μ :=
lintegral_congr_ae h_lim.mono fun _ h => h.liminf_eq.symm
      _ <= liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : Nat => ∫⁻ a, F 

Depends on / 依赖: h.liminf_eq.symm, h.limsup_eq, hF_meas, h_bound, h_fin, h_lim, h_lim.mono, liminf, liminf_eq, limsup, limsup_eq, limsup_lintegral_le, lintegral_congr_ae, lintegral_liminf_le, tendsto_of_le_liminf_of_limsup_le
-/
theorem tendsto_lintegral_of_dominated_convergence {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞}
    (bound : α -> Real>=0∞) (hF_meas : forall n, Measurable (F n)) (h_bound : forall n, F n <=ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : Nat => F n a) atTop ∂μ :=
lintegral_congr_ae h_lim.mono fun _ h => h.liminf_eq.symm
      _ <= liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : Nat => ∫⁻ a, F n a ∂μ) atTop <= ∫⁻ a, limsup (fun n => F n a) atTop ∂μ :=
        limsup_lintegral_le _ hF_meas h_bound h_fin
_ = ∫⁻ a, f a ∂μ := lintegral_congr_ae h_lim.mono fun _ h => h.limsup_eq)

/--
theorem `tendsto_lintegral_of_dominated_convergence'` / 定理 `tendsto_lintegral_of_dominated_convergence'`

English:
theorem tendsto_lintegral_of_dominated_convergence'
  statement: {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞}
  proof: by
  have : forall n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : forall n, forallᵐ a ∂μ, (hF_meas n).mk 

中文:
定理 tendsto_lintegral_of_dominated_convergence'
  结论: {F : 自然数 -> α -> 实数>=0∞} {f : α -> 实数>=0∞}
  证明: by
  have : forall n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : forall n, forallᵐ a ∂μ, (hF_meas n).mk 

Depends on / 依赖: ae_all_iff, ae_all_iff.mpr, ae_eq_mk, ae_eq_mk.symm, filter_upwards, hF_meas, h_fin, h_lim, lintegral_congr_ae, measurable_mk, simp_rw, tendsto_lintegral_of_dominated_convergence
-/
theorem tendsto_lintegral_of_dominated_convergence' {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞}
    (bound : α -> Real>=0∞) (hF_meas : forall n, AEMeasurable (F n) μ) (h_bound : forall n, F n <=ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  have : forall n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : forall n, forallᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    have : forallᵐ a ∂μ, forall n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    filter_upwards [this, h_lim] with a H H'
    simp_rw [H]
    exact H'
  · intro n
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H'
    rwa [H'] at H

/--
theorem `tendsto_lintegral_filter_of_dominated_convergence'` / 定理 `tendsto_lintegral_filter_of_dominated_convergence'`

English:
theorem tendsto_lintegral_filter_of_dominated_convergence'
  statement: {ι} {l : Filter ι}
  proof: by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' ?_ ?_ ?_ ?_ ?_
  · 

中文:
定理 tendsto_lintegral_filter_of_dominated_convergence'
  结论: {ι} {l : 滤子 ι}
  证明: by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' ?_ ?_ ?_ ?_ ?_
  · 

Depends on / 依赖: Nat.le_add_left, Tendsto, Tendsto.comp, hF_meas, h_bound, h_lim, h_lim.mono, inter_mem, le_add_left, replace, tendsto_add_atTop_iff_nat, tendsto_atTop, tendsto_iff_seq_tendsto, tendsto_lintegral_of_dominated_convergence
-/
theorem tendsto_lintegral_filter_of_dominated_convergence' {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (bound : α -> Real>=0∞)
    (hF_meas : forallᶠ n in l, AEMeasurable (F n) μ) (h_bound : forallᶠ n in l, forallᵐ a ∂μ, F n a <= bound a)
    (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' ?_ ?_ ?_ ?_ ?_
  · exact bound
  · intro
    refine (h _ ?_).1
    exact Nat.le_add_left _ _
  · intro
    refine (h _ ?_).2
    exact Nat.le_add_left _ _
  · assumption
  · refine h_lim.mono fun a h_lim => ?_
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_atTop_iff_nat]
    assumption

/--
theorem `tendsto_lintegral_filter_of_dominated_convergence` / 定理 `tendsto_lintegral_filter_of_dominated_convergence`

English:
theorem tendsto_lintegral_filter_of_dominated_convergence
  statement: {ι} {l : Filter ι}
  proof: by
  refine tendsto_lintegral_filter_of_dominated_convergence' bound ?_ h_bound h_fin h_lim
  filter_upwards [hF_meas] using by fun_prop

中文:
定理 tendsto_lintegral_filter_of_dominated_convergence
  结论: {ι} {l : 滤子 ι}
  证明: by
  refine tendsto_lintegral_filter_of_dominated_convergence' bound ?_ h_bound h_fin h_lim
  filter_upwards [hF_meas] using by fun_prop

Depends on / 依赖: filter_upwards, fun_prop, hF_meas, h_bound, h_fin, h_lim, tendsto_lintegral_filter_of_dominated_convergence
-/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (bound : α -> Real>=0∞)
    (hF_meas : forallᶠ n in l, Measurable (F n)) (h_bound : forallᶠ n in l, forallᵐ a ∂μ, F n a <= bound a)
    (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  refine tendsto_lintegral_filter_of_dominated_convergence' bound ?_ h_bound h_fin h_lim
  filter_upwards [hF_meas] using by fun_prop

/--
lemma `tendsto_of_lintegral_tendsto_of_monotone_aux` / 引理 `tendsto_of_lintegral_tendsto_of_monotone_aux`

English:
lemma tendsto_of_lintegral_tendsto_of_monotone_aux
  statement: {α : Type*} {mα : MeasurableSpace α}
  proof: by
  have h_bound_finite : forallᵐ a ∂μ, F a != ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    h

中文:
引理 tendsto_of_lintegral_tendsto_of_monotone_aux
  结论: {α : 类型} {mα : 可测空间 α}
  证明: by
  have h_bound_finite : forallᵐ a ∂μ, F a != ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    h

Depends on / 依赖: Tendsto, ae_lt_top, filter_upwards, hF_meas, h_absurd, h_bound, h_bound_finite, h_exists, h_fin, h_int_finite, h_le, h_mono, h_tendsto, ha.ne, hf_mono, tendsto_atTop_atTop_iff_of_mo, tendsto_atTop_of_monotone
-/
lemma tendsto_of_lintegral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableSpace α}
    {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α}
    (hf_meas : forall n, AEMeasurable (f n) μ) (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a))
    (h_bound : forallᵐ a ∂μ, forall i, f i a <= F a) (h_int_finite : ∫⁻ a, F a ∂μ != ∞) :
    forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a)) := by
  have h_bound_finite : forallᵐ a ∂μ, F a != ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    have h_tendsto : Tendsto (fun i => f i a) atTop atTop ∨
        exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := tendsto_atTop_of_monotone h_mono
    rcases h_tendsto with h_absurd | h_tendsto
    · rw [tendsto_atTop_atTop_iff_of_monotone h_mono] at h_absurd
      obtain ⟨i, hi⟩ := h_absurd (F a + 1)
      refine absurd (hi.trans (h_le _)) (not_le.mpr ?_)
      exact ENNReal.lt_add_right h_fin one_ne_zero
    · exact h_tendsto
  classical
  let F' : α -> Real>=0∞ := fun a => if h : exists l, Tendsto (fun i => f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F' <=ᵐ[μ] F := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact le_of_tendsto' h_tendsto (fun m => h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ from
    ae_eq_of_ae_le_of_lintegral_le hF'_le (this ▸ h_int_finite) hF_meas this.symm.le
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_monotone hf_meas hf_mono hF'_tendsto

/--
lemma `tendsto_of_lintegral_tendsto_of_monotone` / 引理 `tendsto_of_lintegral_tendsto_of_monotone`

English:
lemma tendsto_of_lintegral_tendsto_of_monotone
  statement: {α : Type*} {mα : MeasurableSpace α}
  proof: by
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n => exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : Nat -> α -> Real>=0∞ := Nat.rec (g 0) (fun n I x => max (g (n + 1) x) (I x))
  have M n : Measura

中文:
引理 tendsto_of_lintegral_tendsto_of_monotone
  结论: {α : 类型} {mα : 可测空间 α}
  证明: by
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n => exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : Nat -> α -> Real>=0∞ := Nat.rec (g 0) (fun n I x => max (g (n + 1) x) (I x))
  have M n : Measura

Depends on / 依赖: Measurable, Measurable.max, Nat.rec, exists_measurable_le_lintegral_eq
-/
lemma tendsto_of_lintegral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace α}
    {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α}
    (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a))
    (h_bound : forallᵐ a ∂μ, forall i, f i a <= F a) (h_int_finite : ∫⁻ a, F a ∂μ != ∞) :
    forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a)) := by
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n => exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : Nat -> α -> Real>=0∞ := Nat.rec (g 0) (fun n I x => max (g (n + 1) x) (I x))
  have M n : Measurable (g' n) := by
    induction n with
    | zero => simp [g', gmeas 0]
    | succ n ih => exact Measurable.max (gmeas (n + 1)) ih
  have I : forall n x, g n x <= g' n x := by
    intro n x
    cases n with | zero | succ => simp [g']
  have I' : forallᵐ x ∂μ, forall n, g' n x <= f n x := by
    filter_upwards [hf_mono] with x hx n
    induction n with
    | zero => simpa [g'] using gf 0 x
    | succ n ih => exact max_le (gf (n + 1) x) (ih.trans (hx (Nat.le_succ n)))
  have Int_eq n : ∫⁻ x, g' n x ∂μ = ∫⁻ x, f n x ∂μ := by
    apply le_antisymm
    · apply lintegral_mono_ae
      filter_upwards [I'] with x hx using hx n
    · rw [hg n]
      exact lintegral_mono (I n)
  have : forallᵐ a ∂μ, Tendsto (fun i => g' i a) atTop (𝓝 (F a)) := by
    apply tendsto_of_lintegral_tendsto_of_monotone_aux _ hF_meas _ _ _ h_int_finite
    · exact fun n => (M n).aemeasurable
    · simp_rw [Int_eq]
      exact hf_tendsto
    · exact Eventually.of_forall (fun x => monotone_nat_of_le_succ (fun n => le_max_right _ _))
    · filter_upwards [h_bound, I'] with x h'x hx n using (hx n).trans (h'x n)
  filter_upwards [this, I', h_bound] with x hx h'x h''x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds h'x h''x

/--
lemma `tendsto_of_lintegral_tendsto_of_antitone` / 引理 `tendsto_of_lintegral_tendsto_of_antitone`

English:
lemma tendsto_of_lintegral_tendsto_of_antitone
  statement: {α : Type*} {mα : MeasurableSpace α}
  proof: by
  have h_int_finite : ∫⁻ a, F a ∂μ != ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases _roo

中文:
引理 tendsto_of_lintegral_tendsto_of_antitone
  结论: {α : 类型} {mα : 可测空间 α}
  证明: by
  have h_int_finite : ∫⁻ a, F a ∂μ != ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases _roo

Depends on / 依赖: OrderBot, OrderBot.atBot_eq, Tendsto, _root_, _root_.tendsto_atTop_of_antitone, atBot_eq, classical, filter_upwards, h.mono_right, h0.lt_top, h_bound, h_exists, h_int_finite, h_mono, hf_mono, lintegral_mono_ae, lt_top, mono_right, pure_le_nhds, tendsto_atTop_of_antitone
-/
lemma tendsto_of_lintegral_tendsto_of_antitone {α : Type*} {mα : MeasurableSpace α}
    {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α}
    (hf_meas : forall n, AEMeasurable (f n) μ)
    (hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : forallᵐ a ∂μ, Antitone (fun i => f i a))
    (h_bound : forallᵐ a ∂μ, forall i, F a <= f i a) (h0 : ∫⁻ a, f 0 a ∂μ != ∞) :
    forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a)) := by
  have h_int_finite : ∫⁻ a, F a ∂μ != ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : forallᵐ a ∂μ, exists l, Tendsto (fun i => f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases _root_.tendsto_atTop_of_antitone h_mono with h | h
    · refine ⟨0, h.mono_right ?_⟩
      rw [OrderBot.atBot_eq]
      exact pure_le_nhds _
    · exact h
  classical
  let F' : α -> Real>=0∞ := fun a => if h : exists l, Tendsto (fun i => f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F <=ᵐ[μ] F' := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact ge_of_tendsto' h_tendsto (fun m => h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ by
    refine (ae_eq_of_ae_le_of_lintegral_le hF'_le h_int_finite ?_ this.le).symm
    exact ENNReal.aemeasurable_of_tendsto hf_meas hF'_tendsto
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_antitone hf_meas hf_mono h0 hF'_tendsto

end MeasureTheory
