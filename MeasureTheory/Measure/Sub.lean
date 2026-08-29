/-
Copyright (c) 2022 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Subtraction of measures

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

@[expose] public section

open Set

namespace MeasureTheory

namespace Measure

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: {α : Type*} [MeasurableSpace α]
  body: ⟨fun μ ν => sInf { τ | μ <= τ + ν }⟩

中文:
实例 instSub
  签名: {α : 类型} [可测空间 α]
  定义体: ⟨fun μ ν => sInf { τ | μ <= τ + ν }⟩
-/
noncomputable instance instSub {α : Type*} [MeasurableSpace α] : Sub (Measure α) :=
  ⟨fun μ ν => sInf { τ | μ <= τ + ν }⟩

variable {α : Type*} {m : MeasurableSpace α} {μ ν ξ : Measure α} {s : Set α}

/--
theorem `sub_def` / 定理 `sub_def`

English:
theorem sub_def
  statement: μ - ν = sInf { d | μ <= d + ν }
  proof: rfl

中文:
定理 sub_def
  结论: μ - ν = sInf { d | μ <= d + ν }
  证明: rfl
-/
theorem sub_def : μ - ν = sInf { d | μ <= d + ν } := rfl

/--
theorem `sub_le_of_le_add` / 定理 `sub_le_of_le_add`

English:
theorem sub_le_of_le_add
  given: {d} (h : μ <= d + ν)
  statement: μ - ν <= d
  proof: sInf_le h

中文:
定理 sub_le_of_le_add
  条件: {d} (h : μ <= d + ν)
  结论: μ - ν <= d
  证明: sInf_le h

Depends on / 依赖: sInf_le
-/
theorem sub_le_of_le_add {d} (h : μ <= d + ν) : μ - ν <= d :=
  sInf_le h

/--
theorem `sub_eq_zero_of_le` / 定理 `sub_eq_zero_of_le`

English:
theorem sub_eq_zero_of_le
  given: (h : μ <= ν)
  statement: μ - ν = 0
  proof: nonpos_iff_eq_zero'.1 sub_le_of_le_add by rwa [zero_add]

中文:
定理 sub_eq_zero_of_le
  条件: (h : μ <= ν)
  结论: μ - ν = 0
  证明: nonpos_iff_eq_zero'.1 sub_le_of_le_add by rwa [zero_add]

Depends on / 依赖: nonpos_iff_eq_zero, sub_le_of_le_add, zero_add
-/
theorem sub_eq_zero_of_le (h : μ <= ν) : μ - ν = 0 :=
nonpos_iff_eq_zero'.1 sub_le_of_le_add by rwa [zero_add]

/--
theorem `sub_le` / 定理 `sub_le`

English:
theorem sub_le
  statement: μ - ν <= μ
  proof: sub_le_of_le_add Measure.le_add_right le_rfl

@[simp]

中文:
定理 sub_le
  结论: μ - ν <= μ
  证明: sub_le_of_le_add Measure.le_add_right le_rfl

@[simp]

Depends on / 依赖: Measure, Measure.le_add_right, le_add_right, le_rfl, sub_le_of_le_add
-/
theorem sub_le : μ - ν <= μ :=
sub_le_of_le_add Measure.le_add_right le_rfl

@[simp]
/--
theorem `sub_top` / 定理 `sub_top`

English:
theorem sub_top
  statement: μ - ⊤ = 0
  proof: sub_eq_zero_of_le le_top

@[simp]

中文:
定理 sub_top
  结论: μ - ⊤ = 0
  证明: sub_eq_zero_of_le le_top

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, LinOrd, le_top, sub_eq_zero_of_le
-/
theorem sub_top : μ - ⊤ = 0 :=
  sub_eq_zero_of_le le_top

@[simp]
/--
theorem `zero_sub` / 定理 `zero_sub`

English:
theorem zero_sub
  statement: 0 - μ = 0
  proof: sub_eq_zero_of_le μ.zero_le

@[simp]

中文:
定理 zero_sub
  结论: 0 - μ = 0
  证明: sub_eq_zero_of_le μ.zero_le

@[simp]
-/
protected theorem zero_sub : 0 - μ = 0 :=
  sub_eq_zero_of_le μ.zero_le

@[simp]
/--
theorem `sub_self` / 定理 `sub_self`

English:
theorem sub_self
  statement: μ - μ = 0
  proof: sub_eq_zero_of_le le_rfl

中文:
定理 sub_self
  结论: μ - μ = 0
  证明: sub_eq_zero_of_le le_rfl

Depends on / 依赖: f.hom
-/
protected theorem sub_self : μ - μ = 0 :=
  sub_eq_zero_of_le le_rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sub_zero` / 定理 `sub_zero`

English:
theorem sub_zero
  statement: μ - 0 = μ
  proof: by
  rw [sub_def]
  apply le_antisymm
  · simp [sInf_le]
  · simp

中文:
定理 sub_zero
  结论: μ - 0 = μ
  证明: by
  rw [sub_def]
  apply le_antisymm
  · simp [sInf_le]
  · simp
-/
protected theorem sub_zero : μ - 0 = μ := by
  rw [sub_def]
  apply le_antisymm
  · simp [sInf_le]
  · simp

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν <= μ)
  proof: by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (fun g h_meas h_disj => by
      simp only [measure_iUnion h_disj h_meas]
      rw [ENNReal.tsum_sub _ (h₂ <| g ·)]
      rw [← measure_iUnion h_disj h_meas]
      apply measure_ne_top)
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set]; rw [add_comm]; rw [tsub_add_cancel_of_le (h₂ t)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add]; rw [mem_ofPred_eq]; rw [add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  apply Measure.ofMeasurable_apply _ h₁

中文:
定理 sub_apply
  条件: [是有限测度 ν] (h₁ : 可测集 s) (h₂ : ν <= μ)
  证明: by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (fun g h_meas h_disj => by
      simp only [measure_iUnion h_disj h_meas]
      rw [ENNReal.tsum_sub _ (h₂ <| g ·)]
      rw [← measure_iUnion h_disj h_meas]
      apply measure_ne_top)
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set]; rw [add_comm]; rw [tsub_add_cancel_of_le (h₂ t)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add]; rw [mem_ofPred_eq]; rw [add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  apply Measure.ofMeasurable_apply _ h₁
-/
theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν <= μ) :
    (μ - ν) s = μ s - ν s := by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (fun g h_meas h_disj => by
      simp only [measure_iUnion h_disj h_meas]
      rw [ENNReal.tsum_sub _ (h₂ <| g ·)]
      rw [← measure_iUnion h_disj h_meas]
      apply measure_ne_top)
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set]; rw [add_comm]; rw [tsub_add_cancel_of_le (h₂ t)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add]; rw [mem_ofPred_eq]; rw [add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  apply Measure.ofMeasurable_apply _ h₁

/--
theorem `sub_add_cancel_of_le` / 定理 `sub_add_cancel_of_le`

English:
theorem sub_add_cancel_of_le
  given: [IsFiniteMeasure ν] (h₁ : ν <= μ)
  statement: μ - ν + ν = μ
  proof: by
  ext1 s h_s_meas
  rw [add_apply]; rw [sub_apply h_s_meas h₁]; rw [tsub_add_cancel_of_le (h₁ s)]

@[simp]

中文:
定理 sub_add_cancel_of_le
  条件: [是有限测度 ν] (h₁ : ν <= μ)
  结论: μ - ν + ν = μ
  证明: by
  ext1 s h_s_meas
  rw [add_apply]; rw [sub_apply h_s_meas h₁]; rw [tsub_add_cancel_of_le (h₁ s)]

@[simp]

Depends on / 依赖: add_apply, h_s_meas, sub_apply, tsub_add_cancel_of_le
-/
theorem sub_add_cancel_of_le [IsFiniteMeasure ν] (h₁ : ν <= μ) : μ - ν + ν = μ := by
  ext1 s h_s_meas
  rw [add_apply]; rw [sub_apply h_s_meas h₁]; rw [tsub_add_cancel_of_le (h₁ s)]

@[simp]
/--
lemma `add_sub_cancel` / 引理 `add_sub_cancel`

English:
lemma add_sub_cancel
  given: [IsFiniteMeasure ν]
  statement: μ + ν - ν = μ
  proof: by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _))]; rw [add_apply]; rw [ENNReal.add_sub_cancel_right (measure_ne_top ν s)]

中文:
引理 add_sub_cancel
  条件: [是有限测度 ν]
  结论: μ + ν - ν = μ
  证明: by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _))]; rw [add_apply]; rw [ENNReal.add_sub_cancel_right (measure_ne_top ν s)]
-/
protected lemma add_sub_cancel [IsFiniteMeasure ν] : μ + ν - ν = μ := by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _))]; rw [add_apply]; rw [ENNReal.add_sub_cancel_right (measure_ne_top ν s)]

/--
theorem `restrict_sub_eq_restrict_sub_restrict` / 定理 `restrict_sub_eq_restrict_sub_restrict`

English:
theorem restrict_sub_eq_restrict_sub_restrict
  given: (h_meas_s : MeasurableSet s)
  proof: by
  repeat rw [sub_def]
  have h_nonempty : { d | μ <= d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  apply le_antisymm
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    intro ν' h_ν'_in
    rw [mem_ofPred_eq] at h_ν'_in
    refine ⟨ν'.restrict s, ?_, restrict_le_self⟩
    refine ⟨ν' + (⊤ : Measure α).restrict sᶜ, ?_, ?_⟩
    · rw [mem_ofPred_eq, add_right_comm, Measure.le_iff]
      intro t h_meas_t
      repeat rw [← measure_inter_add_sdiff t h_meas_s]
      refine add_le_add ?_ ?_
      · rw [add_apply, add_apply]
        apply le_add_right _
        rw [← restrict_eq_self μ inter_subset_right]; rw [← restrict_eq_self ν inter_subset_right]
        apply h_ν'_in
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), sdiff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ <= ν' + ν + ⊤ := by simp only [add_top, le_top]
        exact Measure.le_iff'.1 h_mu_le_add_top _
    · ext1 t h_meas_t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    refine forall_mem_image.2 fun t h_t_in => ⟨t.restrict s, ?_, le_rfl⟩
    rw [Set.mem_ofPred_eq]; rw [← restrict_add]
    exact restrict_mono Subset.rfl h_t_in

中文:
定理 restrict_sub_eq_restrict_sub_restrict
  条件: (h_meas_s : 可测集 s)
  证明: by
  repeat rw [sub_def]
  have h_nonempty : { d | μ <= d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  apply le_antisymm
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    intro ν' h_ν'_in
    rw [mem_ofPred_eq] at h_ν'_in
    refine ⟨ν'.restrict s, ?_, restrict_le_self⟩
    refine ⟨ν' + (⊤ : Measure α).restrict sᶜ, ?_, ?_⟩
    · rw [mem_ofPred_eq, add_right_comm, Measure.le_iff]
      intro t h_meas_t
      repeat rw [← measure_inter_add_sdiff t h_meas_s]
      refine add_le_add ?_ ?_
      · rw [add_apply, add_apply]
        apply le_add_right _
        rw [← restrict_eq_self μ inter_subset_right]; rw [← restrict_eq_self ν inter_subset_right]
        apply h_ν'_in
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), sdiff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ <= ν' + ν + ⊤ := by simp only [add_top, le_top]
        exact Measure.le_iff'.1 h_mu_le_add_top _
    · ext1 t h_meas_t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    refine forall_mem_image.2 fun t h_t_in => ⟨t.restrict s, ?_, le_rfl⟩
    rw [Set.mem_ofPred_eq]; rw [← restrict_add]
    exact restrict_mono Subset.rfl h_t_in

Depends on / 依赖: Measure, Measure.le_add_right, Measure.le_iff, Nonempty, add_le_add, add_right_comm, h_meas_s, h_meas_t, h_nonempty, le_add_right, le_antisymm, le_iff, le_rfl, measure_inter_add_sdiff, mem_ofPred_eq, repeat, restrict, restrict_le_self, restrict_sInf_eq_sInf_restrict, sInf_le_sInf_of_isCoinitialFor
-/
theorem restrict_sub_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) :
    (μ - ν).restrict s = μ.restrict s - ν.restrict s := by
  repeat rw [sub_def]
  have h_nonempty : { d | μ <= d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  apply le_antisymm
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    intro ν' h_ν'_in
    rw [mem_ofPred_eq] at h_ν'_in
    refine ⟨ν'.restrict s, ?_, restrict_le_self⟩
    refine ⟨ν' + (⊤ : Measure α).restrict sᶜ, ?_, ?_⟩
    · rw [mem_ofPred_eq, add_right_comm, Measure.le_iff]
      intro t h_meas_t
      repeat rw [← measure_inter_add_sdiff t h_meas_s]
      refine add_le_add ?_ ?_
      · rw [add_apply, add_apply]
        apply le_add_right _
        rw [← restrict_eq_self μ inter_subset_right]; rw [← restrict_eq_self ν inter_subset_right]
        apply h_ν'_in
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), sdiff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ <= ν' + ν + ⊤ := by simp only [add_top, le_top]
        exact Measure.le_iff'.1 h_mu_le_add_top _
    · ext1 t h_meas_t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    refine forall_mem_image.2 fun t h_t_in => ⟨t.restrict s, ?_, le_rfl⟩
    rw [Set.mem_ofPred_eq]; rw [← restrict_add]
    exact restrict_mono Subset.rfl h_t_in

/--
theorem `sub_apply_eq_zero_of_restrict_le_restrict` / 定理 `sub_apply_eq_zero_of_restrict_le_restrict`

English:
theorem sub_apply_eq_zero_of_restrict_le_restrict
  statement: (h_le : μ.restrict s <= ν.restrict s)
  proof: by
  rw [← restrict_apply_self]; rw [restrict_sub_eq_restrict_sub_restrict]; rw [sub_eq_zero_of_le] <;> simp [*]

中文:
定理 sub_apply_eq_zero_of_restrict_le_restrict
  结论: (h_le : μ.restrict s <= ν.restrict s)
  证明: by
  rw [← restrict_apply_self]; rw [restrict_sub_eq_restrict_sub_restrict]; rw [sub_eq_zero_of_le] <;> simp [*]

Depends on / 依赖: restrict_apply_self, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le
-/
theorem sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s <= ν.restrict s)
    (h_meas_s : MeasurableSet s) : (μ - ν) s = 0 := by
  rw [← restrict_apply_self]; rw [restrict_sub_eq_restrict_sub_restrict]; rw [sub_eq_zero_of_le] <;> simp [*]

/--
Instance `isFiniteMeasure_sub` / 实例 `isFiniteMeasure_sub`

English:
instance isFiniteMeasure_sub
  signature: [IsFiniteMeasure μ]
  body: isFiniteMeasure_of_le μ sub_le

中文:
实例 isFiniteMeasure_sub
  签名: [是有限测度 μ]
  定义体: isFiniteMeasure_of_le μ sub_le

Depends on / 依赖: isFiniteMeasure_of_le, sub_le
-/
instance isFiniteMeasure_sub [IsFiniteMeasure μ] : IsFiniteMeasure (μ - ν) :=
  isFiniteMeasure_of_le μ sub_le

/--
lemma `sub_le_iff_le_add_of_le` / 引理 `sub_le_iff_le_add_of_le`

English:
lemma sub_le_iff_le_add_of_le
  given: [IsFiniteMeasure ν] (h_le : ν <= μ)
  statement: μ - ν <= ξ ↔ μ <= ξ + ν
  proof: by
  refine ⟨fun h => ?_, Measure.sub_le_of_le_add⟩
  simpa [sub_add_cancel_of_le h_le] using add_le_add_left h ν

中文:
引理 sub_le_iff_le_add_of_le
  条件: [是有限测度 ν] (h_le : ν <= μ)
  结论: μ - ν <= ξ ↔ μ <= ξ + ν
  证明: by
  refine ⟨fun h => ?_, Measure.sub_le_of_le_add⟩
  simpa [sub_add_cancel_of_le h_le] using add_le_add_left h ν

Depends on / 依赖: Measure, Measure.sub_le_of_le_add, add_le_add_left, h_le, sub_add_cancel_of_le, sub_le_of_le_add
-/
lemma sub_le_iff_le_add_of_le [IsFiniteMeasure ν] (h_le : ν <= μ) : μ - ν <= ξ ↔ μ <= ξ + ν := by
  refine ⟨fun h => ?_, Measure.sub_le_of_le_add⟩
  simpa [sub_add_cancel_of_le h_le] using add_le_add_left h ν

end Measure

end MeasureTheory
