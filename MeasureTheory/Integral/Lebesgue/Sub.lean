/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Subtraction of Lebesgue integrals

In this file we first show that Lebesgue integrals can be subtracted with the expected results –
`∫⁻ f - ∫⁻ g ≤ ∫⁻ (f - g)`, with equality if `g ≤ f` almost everywhere. Then we prove variants of
the monotone convergence theorem that use this subtraction in their proofs.
-/

public section

open Filter ENNReal Topology

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

/--
theorem `lintegral_sub'` / 定理 `lintegral_sub'`

English:
theorem lintegral_sub'
  statement: {f g : α -> Real>=0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
  proof: by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)

中文:
定理 lintegral_sub'
  结论: {f g : α -> 实数>=0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
  证明: by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)

Depends on / 依赖: ENNReal, ENNReal.eq_sub_of_add_eq, eq_sub_of_add_eq, h_le, h_le.mono, hg_fin, lintegral_add_right, lintegral_congr_ae, tsub_add_cancel_of_le
-/
theorem lintegral_sub' {f g : α -> Real>=0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
    (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ := by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)

/--
theorem `lintegral_sub` / 定理 `lintegral_sub`

English:
theorem lintegral_sub
  statement: {f g : α -> Real>=0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
  proof: lintegral_sub' hg.aemeasurable hg_fin h_le

中文:
定理 lintegral_sub
  结论: {f g : α -> 实数>=0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
  证明: lintegral_sub' hg.aemeasurable hg_fin h_le

Depends on / 依赖: aemeasurable, h_le, hg.aemeasurable, hg_fin, lintegral_sub
-/
theorem lintegral_sub {f g : α -> Real>=0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞)
    (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
  lintegral_sub' hg.aemeasurable hg_fin h_le

/--
theorem `lintegral_sub_le'` / 定理 `lintegral_sub_le'`

English:
theorem lintegral_sub_le'
  given: (f g : α -> Real>=0∞) (hf : AEMeasurable f μ)
  proof: by
  rw [tsub_le_iff_right]
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    gcongr
    exact le_tsub_add

中文:
定理 lintegral_sub_le'
  条件: (f g : α -> 实数>=0∞) (hf : AEMeasurable f μ)
  证明: by
  rw [tsub_le_iff_right]
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    gcongr
    exact le_tsub_add

Depends on / 依赖: add_top, le_top, le_tsub_add, lintegral_add_right, tsub_le_iff_right
-/
theorem lintegral_sub_le' (f g : α -> Real>=0∞) (hf : AEMeasurable f μ) :
    ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ <= ∫⁻ x, g x - f x ∂μ := by
  rw [tsub_le_iff_right]
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    gcongr
    exact le_tsub_add

/--
theorem `lintegral_sub_le` / 定理 `lintegral_sub_le`

English:
theorem lintegral_sub_le
  given: (f g : α -> Real>=0∞) (hf : Measurable f)
  proof: lintegral_sub_le' f g hf.aemeasurable

中文:
定理 lintegral_sub_le
  条件: (f g : α -> 实数>=0∞) (hf : Measurable f)
  证明: lintegral_sub_le' f g hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, lintegral_sub_le
-/
theorem lintegral_sub_le (f g : α -> Real>=0∞) (hf : Measurable f) :
    ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ <= ∫⁻ x, g x - f x ∂μ :=
  lintegral_sub_le' f g hf.aemeasurable

/--
theorem `lintegral_iInf_ae` / 定理 `lintegral_iInf_ae`

English:
theorem lintegral_iInf_ae
  statement: {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurable (f n))
  proof: have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun _ => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
(ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 

中文:
定理 lintegral_iInf_ae
  结论: {f : 自然数 -> α -> 实数>=0∞} (h_meas : 对任意 n, Measurable (f n))
  证明: have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun _ => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
(ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 

Depends on / 依赖: ENNReal, ENNReal.sub_right_inj, ae_of, fn_le_f0, h_fin, h_meas, iInf_le, iInf_le_of_le, le_rfl, lintegral_mono, lintegral_sub, ne_top_of_le_ne_top, sub_right_inj
-/
theorem lintegral_iInf_ae {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurable (f n))
    (h_mono : forall n : Nat, f n.succ <=ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ != ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun _ => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ <= ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
(ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ from
      calc
        ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a - ⨅ n, f n a ∂μ :=
          (lintegral_sub (.iInf h_meas)
              (ne_top_of_le_ne_top h_fin <| lintegral_mono fun _ => iInf_le _ _)
              (ae_of_all _ fun _ => iInf_le _ _)).symm
        _ = ∫⁻ a, ⨆ n, f 0 a - f n a ∂μ := congr rfl (funext fun _ => ENNReal.sub_iInf)
        _ = ⨆ n, ∫⁻ a, f 0 a - f n a ∂μ :=
          (lintegral_iSup_ae (fun n => (h_meas 0).sub (h_meas n)) fun n =>
            (h_mono n).mono fun _ ha => tsub_le_tsub le_rfl ha)
        _ = ⨆ n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :=
          (have h_mono : forallᵐ a ∂μ, forall n : Nat, f n.succ a <= f n a := ae_all_iff.2 h_mono
          have h_mono : forall n, forallᵐ a ∂μ, f n a <= f 0 a := fun n =>
            h_mono.mono fun a h => by
              induction n with
              | zero => rfl
              | succ n ih => exact (h n).trans ih
congr_arg iSup
            funext fun n =>
              lintegral_sub (h_meas _) (ne_top_of_le_ne_top h_fin <| lintegral_mono_ae <| h_mono n)
                (h_mono n))
        _ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ := ENNReal.sub_iInf.symm

/--
theorem `lintegral_iInf` / 定理 `lintegral_iInf`

English:
theorem lintegral_iInf
  statement: {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurable (f n)) (h_anti : Antitone f)
  proof: lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin

中文:
定理 lintegral_iInf
  结论: {f : 自然数 -> α -> 实数>=0∞} (h_meas : 对任意 n, Measurable (f n)) (h_anti : Antitone f)
  证明: lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin

Depends on / 依赖: ae_of_all, h_anti, h_fin, h_meas, le_succ, lintegral_iInf_ae, n.le_succ
-/
theorem lintegral_iInf {f : Nat -> α -> Real>=0∞} (h_meas : forall n, Measurable (f n)) (h_anti : Antitone f)
    (h_fin : ∫⁻ a, f 0 a ∂μ != ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin

/--
theorem `lintegral_iInf'` / 定理 `lintegral_iInf'`

English:
theorem lintegral_iInf'
  statement: {f : Nat -> α -> Real>=0∞} (h_meas : forall n, AEMeasurable (f n) μ)
  proof: by
  simp_rw [← iInf_apply]
  let p : α -> (Nat -> Real>=0∞) -> Prop := fun _ f' => Antitone f'
  have hp : forallᵐ x ∂μ, p x fun i => f i x := h_anti
  have h_ae_seq_mono : Antitone (aeSeq h_meas p) := by
    intro n m hnm x
    by_cases hx : x in aeSeqSet h_meas p
    · exact aeSeq.prop_of_mem_aeS

中文:
定理 lintegral_iInf'
  结论: {f : 自然数 -> α -> 实数>=0∞} (h_meas : 对任意 n, AEMeasurable (f n) μ)
  证明: by
  simp_rw [← iInf_apply]
  let p : α -> (Nat -> Real>=0∞) -> Prop := fun _ f' => Antitone f'
  have hp : forallᵐ x ∂μ, p x fun i => f i x := h_anti
  have h_ae_seq_mono : Antitone (aeSeq h_meas p) := by
    intro n m hnm x
    by_cases hx : x in aeSeqSet h_meas p
    · exact aeSeq.prop_of_mem_aeS

Depends on / 依赖: Antitone, aeSeq.iInf, aeSeq.measurable, aeSeq.prop_of_mem_aeSeqSet, aeSeqSet, h_ae_seq_mono, h_anti, h_meas, iInf_apply, if_false, le_rfl, lintegral_congr_ae, lintegral_iInf, measurable, prop_of_mem_aeSeqSet, simp_rw
-/
theorem lintegral_iInf' {f : Nat -> α -> Real>=0∞} (h_meas : forall n, AEMeasurable (f n) μ)
    (h_anti : forallᵐ a ∂μ, Antitone (fun i => f i a)) (h_fin : ∫⁻ a, f 0 a ∂μ != ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iInf_apply]
  let p : α -> (Nat -> Real>=0∞) -> Prop := fun _ f' => Antitone f'
  have hp : forallᵐ x ∂μ, p x fun i => f i x := h_anti
  have h_ae_seq_mono : Antitone (aeSeq h_meas p) := by
    intro n m hnm x
    by_cases hx : x in aeSeqSet h_meas p
    · exact aeSeq.prop_of_mem_aeSeqSet h_meas hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iInf h_meas hp).symm]
  simp_rw [iInf_apply]
  rw [lintegral_iInf (aeSeq.measurable h_meas p) h_ae_seq_mono]
  · congr
    exact funext fun n => lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp n)
  · rwa [lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp 0)]

/--
theorem `lintegral_iInf_directed_of_measurable` / 定理 `lintegral_iInf_directed_of_measurable`

English:
theorem lintegral_iInf_directed_of_measurable
  statement: [Countable β]
  proof: by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp only [iInf_of_empty, lintegral_const,
      ENNReal.top_mul (Measure.measure_univ_ne_zero.mpr hμ)]
  inhabit β
  have : forall a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine fun a =>
      le_antisymm (le_iIn

中文:
定理 lintegral_iInf_directed_of_measurable
  结论: [Countable β]
  证明: by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp only [iInf_of_empty, lintegral_const,
      ENNReal.top_mul (Measure.measure_univ_ne_zero.mpr hμ)]
  inhabit β
  have : forall a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine fun a =>
      le_antisymm (le_iIn

Depends on / 依赖: ENNReal, ENNReal.top_mul, Encodable, Encodable.encode, Function, Function.c, Measure, Measure.measure_univ_ne_zero.mpr, encode, h_directed, h_directed.sequence, h_directed.sequence_le, iInf_le, iInf_le_of_le, iInf_of_empty, inhabit, isEmpty_or_nonempty, le_antisymm, le_iInf, lintegral_const
-/
theorem lintegral_iInf_directed_of_measurable [Countable β]
    {f : β -> α -> Real>=0∞} {μ : Measure α} (hμ : μ != 0) (hf : forall b, Measurable (f b))
    (hf_int : forall b, ∫⁻ a, f b a ∂μ != ∞) (h_directed : Directed (· >= ·) f) :
    ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp only [iInf_of_empty, lintegral_const,
      ENNReal.top_mul (Measure.measure_univ_ne_zero.mpr hμ)]
  inhabit β
  have : forall a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine fun a =>
      le_antisymm (le_iInf fun n => iInf_le _ _)
        (le_iInf fun b => iInf_le_of_le (Encodable.encode b + 1) ?_)
    exact h_directed.sequence_le b a
  calc
    ∫⁻ a, ⨅ b, f b a ∂μ
    _ = ∫⁻ a, ⨅ n, (f ∘ h_directed.sequence f) n a ∂μ := by simp only [this, Function.comp_apply]
    _ = ⨅ n, ∫⁻ a, (f ∘ h_directed.sequence f) n a ∂μ := by
      rw [lintegral_iInf ?_ h_directed.sequence_anti]
      · exact hf_int _
      · exact fun n => hf _
    _ = ⨅ b, ∫⁻ a, f b a ∂μ := by
      refine le_antisymm (le_iInf fun b => ?_) (le_iInf fun n => ?_)
      · exact iInf_le_of_le (Encodable.encode b + 1) (lintegral_mono <| h_directed.sequence_le b)
      · exact iInf_le (fun b => ∫⁻ a, f b a ∂μ) _

/--
theorem `lintegral_tendsto_of_tendsto_of_antitone` / 定理 `lintegral_tendsto_of_tendsto_of_antitone`

English:
theorem lintegral_tendsto_of_tendsto_of_antitone
  statement: {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞}
  proof: by
  have : Antitone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_anti.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨅ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iInf this
  rw [← lintegral_iInf' hf h_anti h0]
  refine lintegral_congr_ae ?_
  filter_up

中文:
定理 lintegral_tendsto_of_tendsto_of_antitone
  结论: {f : 自然数 -> α -> 实数>=0∞} {F : α -> 实数>=0∞}
  证明: by
  have : Antitone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_anti.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨅ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iInf this
  rw [← lintegral_iInf' hf h_anti h0]
  refine lintegral_congr_ae ?_
  filter_up

Depends on / 依赖: Antitone, filter_upwards, h_anti, h_anti.mono, h_tendsto, hx_anti, hx_tendsto, lintegral_congr_ae, lintegral_iInf, lintegral_mono_ae, tendsto_atTop_iInf, tendsto_nhds_unique
-/
theorem lintegral_tendsto_of_tendsto_of_antitone {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞}
    (hf : forall n, AEMeasurable (f n) μ) (h_anti : forallᵐ x ∂μ, Antitone fun n => f n x)
    (h0 : ∫⁻ a, f 0 a ∂μ != ∞)
    (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  have : Antitone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_anti.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨅ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iInf this
  rw [← lintegral_iInf' hf h_anti h0]
  refine lintegral_congr_ae ?_
  filter_upwards [h_anti, h_tendsto] with _ hx_anti hx_tendsto
    using tendsto_nhds_unique hx_tendsto (tendsto_atTop_iInf hx_anti)

section UnifTight

local infixr:25 " ->ₛ " => SimpleFunc

open Function in
/--
theorem `exists_setLIntegral_compl_lt` / 定理 `exists_setLIntegral_compl_lt`

English:
theorem exists_setLIntegral_compl_lt
  statement: {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  proof: by
  by_cases hf₀ : ∫⁻ a, f a ∂μ = 0
  · exact ⟨∅, .empty, by simp, by simpa [hf₀, pos_iff_ne_zero]⟩
  obtain ⟨g, hgf, hg_meas, hgsupp, hgε⟩ :
      exists g <= f, Measurable g ∧ μ (support g) < ∞ ∧ ∫⁻ a, f a ∂μ - ε < ∫⁻ a, g a ∂μ := by
    obtain ⟨g, hgf, hgε⟩ : exists (g : α ->ₛ Real>=0∞) (_ : g <

中文:
定理 exists_setLIntegral_compl_lt
  结论: {f : α -> 实数>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  证明: by
  by_cases hf₀ : ∫⁻ a, f a ∂μ = 0
  · exact ⟨∅, .empty, by simp, by simpa [hf₀, pos_iff_ne_zero]⟩
  obtain ⟨g, hgf, hg_meas, hgsupp, hgε⟩ :
      exists g <= f, Measurable g ∧ μ (support g) < ∞ ∧ ∫⁻ a, f a ∂μ - ε < ∫⁻ a, g a ∂μ := by
    obtain ⟨g, hgf, hgε⟩ : exists (g : α ->ₛ Real>=0∞) (_ : g <

Depends on / 依赖: ENNReal, ENNReal.sub_lt_self, Measurable, SimpleFunc, SimpleFunc.FinMe, g.lintegral, g.lintegral_eq_lintegral, g.measurable, hg_meas, hgsupp, lintegral, lintegral_def, lintegral_eq_lintegral, lt_iSup_iff, measurable, pos_iff_ne_zero, sub_lt_self, support
-/
theorem exists_setLIntegral_compl_lt {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
    {ε : Real>=0∞} (hε : ε != 0) :
    exists s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, f a ∂μ < ε := by
  by_cases hf₀ : ∫⁻ a, f a ∂μ = 0
  · exact ⟨∅, .empty, by simp, by simpa [hf₀, pos_iff_ne_zero]⟩
  obtain ⟨g, hgf, hg_meas, hgsupp, hgε⟩ :
      exists g <= f, Measurable g ∧ μ (support g) < ∞ ∧ ∫⁻ a, f a ∂μ - ε < ∫⁻ a, g a ∂μ := by
    obtain ⟨g, hgf, hgε⟩ : exists (g : α ->ₛ Real>=0∞) (_ : g <= f), ∫⁻ a, f a ∂μ - ε < g.lintegral μ := by
      simpa only [← lt_iSup_iff, ← lintegral_def] using ENNReal.sub_lt_self hf hf₀ hε
    refine ⟨g, hgf, g.measurable, ?_, by rwa [g.lintegral_eq_lintegral]⟩
exact SimpleFunc.FinMeasSupp.of_lintegral_ne_top ne_top_of_le_ne_top hf
      g.lintegral_eq_lintegral μ ▸ lintegral_mono hgf
  refine ⟨_, measurableSet_support hg_meas, hgsupp, ?_⟩
  calc
    ∫⁻ a in (support g)ᶜ, f a ∂μ
      = ∫⁻ a in (support g)ᶜ, f a - g a ∂μ := setLIntegral_congr_fun
(measurableSet_support hg_meas).compl by intro; simp_all
    _ <= ∫⁻ a, f a - g a ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
      lintegral_sub hg_meas (ne_top_of_le_ne_top hf <| lintegral_mono hgf) (ae_of_all _ hgf)
_ < ε := ENNReal.sub_lt_of_lt_add (lintegral_mono hgf)
      ENNReal.lt_add_of_sub_lt_left (.inl hf) hgε

/--
theorem `exists_measurable_le_setLIntegral_eq_of_integrable` / 定理 `exists_measurable_le_setLIntegral_eq_of_integrable`

English:
theorem exists_measurable_le_setLIntegral_eq_of_integrable
  given: {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  proof: by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  refine fun s hms => le_antisymm ?_ (lintegral_mono hgf)
  rw [← compl_compl s]; rw [setLIntegral_compl hms.compl]; rw [setLIntegral_compl hms.compl]; rw [hifg]
  · gcongr; apply hgf
  · rw [hifg] at h

中文:
定理 exists_measurable_le_setLIntegral_eq_of_integrable
  条件: {f : α -> 实数>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  证明: by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  refine fun s hms => le_antisymm ?_ (lintegral_mono hgf)
  rw [← compl_compl s]; rw [setLIntegral_compl hms.compl]; rw [setLIntegral_compl hms.compl]; rw [hifg]
  · gcongr; apply hgf
  · rw [hifg] at h

Depends on / 依赖: compl_compl, exists_measurable_le_lintegral_eq, hms.compl, le_antisymm, lintegral_mono, ne_top_of_le_ne_top, setLIntegral_compl, setLIntegral_le_lintegral
-/
theorem exists_measurable_le_setLIntegral_eq_of_integrable {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) :
    exists (g : α -> Real>=0∞), Measurable g ∧ g <= f ∧ forall s : Set α, MeasurableSet s ->
      ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  refine fun s hms => le_antisymm ?_ (lintegral_mono hgf)
  rw [← compl_compl s]; rw [setLIntegral_compl hms.compl]; rw [setLIntegral_compl hms.compl]; rw [hifg]
  · gcongr; apply hgf
  · rw [hifg] at hf
    exact ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)
  · exact ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)

end UnifTight

end MeasureTheory
