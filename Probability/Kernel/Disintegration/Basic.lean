/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if
`ρ.fst ⊗ₘ ρCond = ρ`.

A kernel `ρ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if
`κ.fst ⊗ₖ κCond = κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is an s-finite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` for a **construction** of
disintegrating kernels.
-/

@[expose] public section

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mΩ : MeasurableSpace Ω}

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure
variable (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)

/--
Definition of `IsCondKernel` / `IsCondKernel` 的定义

English:
class IsCondKernel
  parameters: : Prop where
  axioms and operations (1):
    - disintegrate : ρ.fst otimesₘ ρCond = ρ

中文:
类 是余ndKernel
  参数: : 命题 where
  公理与运算 (1 个):
    - disintegrate : ρ.fst otimesₘ ρCond = ρ
-/
class IsCondKernel : Prop where
  disintegrate : ρ.fst otimesₘ ρCond = ρ

variable [ρ.IsCondKernel ρCond]

/--
lemma `disintegrate` / 引理 `disintegrate`

English:
lemma disintegrate
  statement: ρ.fst otimesₘ ρCond = ρ
  proof: IsCondKernel.disintegrate

中文:
引理 disintegrate
  结论: ρ.fst otimesₘ ρCond = ρ
  证明: IsCondKernel.disintegrate

Depends on / 依赖: IsCondKernel, IsCondKernel.disintegrate, disintegrate
-/
lemma disintegrate : ρ.fst otimesₘ ρCond = ρ := IsCondKernel.disintegrate

/--
lemma `IsCondKernel.isSFiniteKernel` / 引理 `IsCondKernel.isSFiniteKernel`

English:
lemma IsCondKernel.isSFiniteKernel
  given: (hρ : ρ != 0)
  statement: IsSFiniteKernel ρCond
  proof: by
  contrapose hρ; rwa [← ρ.disintegrate ρCond, Measure.compProd_of_not_isSFiniteKernel]

中文:
引理 是余ndKernel.isSFiniteKernel
  条件: (hρ : ρ != 0)
  结论: 是SFiniteKernel ρCond
  证明: by
  contrapose hρ; rwa [← ρ.disintegrate ρCond, Measure.compProd_of_not_isSFiniteKernel]

Depends on / 依赖: Measure, Measure.compProd_of_not_isSFiniteKernel, compProd_of_not_isSFiniteKernel, contrapose, disintegrate
-/
lemma IsCondKernel.isSFiniteKernel (hρ : ρ != 0) : IsSFiniteKernel ρCond := by
  contrapose hρ; rwa [← ρ.disintegrate ρCond, Measure.compProd_of_not_isSFiniteKernel]

variable [IsFiniteMeasure ρ]

/--
lemma `IsCondKernel.apply_of_ne_zero_of_measurableSet` / 引理 `IsCondKernel.apply_of_ne_zero_of_measurableSet`

English:
lemma IsCondKernel.apply_of_ne_zero_of_measurableSet
  statement: [MeasurableSingletonClass α] {x : α}
  proof: by
  have := isSFiniteKernel ρ ρCond (by rintro rfl; simp at hx)
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x]; rw [hs⟩))]
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := 

中文:
引理 是余ndKernel.apply_of_ne_zero_of_measurableSet
  结论: [MeasurableSingleton类 α] {x : α}
  证明: by
  have := isSFiniteKernel ρ ρCond (by rintro rfl; simp at hx)
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x]; rw [hs⟩))]
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := 
-/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} != 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have := isSFiniteKernel ρ ρCond (by rintro rfl; simp at hx)
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x]; rw [hs⟩))]
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := by
    obtain rfl | hax := eq_or_ne a x
    · simp only [singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_notMem]
      have : Prod.mk a ⁻¹' Prod.mk x '' s = ∅ := by ext y; simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hx (measure_ne_top _ _)]; rw [one_mul]

/--
lemma `IsCondKernel.apply_of_ne_zero` / 引理 `IsCondKernel.apply_of_ne_zero`

English:
lemma IsCondKernel.apply_of_ne_zero
  statement: [MeasurableSingletonClass α] {x : α}
  proof: by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) => (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).com

中文:
引理 是余ndKernel.apply_of_ne_zero
  结论: [MeasurableSingleton类 α] {x : α}
  证明: by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) => (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).com

Depends on / 依赖: IsCondKernel, IsCondKernel.apply_of_ne_zero_of_measurableSet, Set.singleton_prod, apply_of_ne_zero_of_measurableSet, comap_apply, measurableEmbedding_prodMk_left, singleton_prod
-/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} != 0) (s : Set Ω) : ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) => (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]

/--
lemma `IsCondKernel.isProbabilityMeasure` / 引理 `IsCondKernel.isProbabilityMeasure`

English:
lemma IsCondKernel.isProbabilityMeasure
  given: [MeasurableSingletonClass α] {a : α} (ha : ρ.fst {a} != 0)
  proof: by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha]; rw [prod_univ]; rw [← Measure.fst_apply
    (measurableSet_singleton _)]; rw [ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]

中文:
引理 是余ndKernel.isProbabilityMeasure
  条件: [MeasurableSingleton类 α] {a : α} (ha : ρ.fst {a} != 0)
  证明: by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha]; rw [prod_univ]; rw [← Measure.fst_apply
    (measurableSet_singleton _)]; rw [ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, IsCondKernel, IsCondKernel.apply_of_ne_zero, Measure, Measure.fst_apply, apply_of_ne_zero, fst_apply, inv_mul_cancel, measurableSet_singleton, measure_ne_top, prod_univ
-/
lemma IsCondKernel.isProbabilityMeasure [MeasurableSingletonClass α] {a : α} (ha : ρ.fst {a} != 0) :
    IsProbabilityMeasure (ρCond a) := by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha]; rw [prod_univ]; rw [← Measure.fst_apply
    (measurableSet_singleton _)]; rw [ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]

/--
lemma `IsCondKernel.isMarkovKernel` / 引理 `IsCondKernel.isMarkovKernel`

English:
lemma IsCondKernel.isMarkovKernel
  given: [MeasurableSingletonClass α] (hρ : forall a, ρ.fst {a} != 0)
  proof: ⟨fun _ => isProbabilityMeasure _ _ (hρ _)⟩

中文:
引理 是余ndKernel.isMarkovKernel
  条件: [MeasurableSingleton类 α] (hρ : 对任意 a, ρ.fst {a} != 0)
  证明: ⟨fun _ => isProbabilityMeasure _ _ (hρ _)⟩

Depends on / 依赖: isProbabilityMeasure
-/
lemma IsCondKernel.isMarkovKernel [MeasurableSingletonClass α] (hρ : forall a, ρ.fst {a} != 0) :
    IsMarkovKernel ρCond := ⟨fun _ => isProbabilityMeasure _ _ (hρ _)⟩

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel. It also proves that if `κ`
is an s-finite kernel from a countable `α` such that each measure `κ a` is disintegrated by some
kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.
-/

namespace ProbabilityTheory.Kernel
variable (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

/--
Definition of `IsCondKernel` / `IsCondKernel` 的定义

English:
class IsCondKernel
  parameters: : Prop where
  axioms and operations (1):
    - disintegrate : κ.fst otimesₖ κCond = κ

中文:
类 是余ndKernel
  参数: : 命题 where
  公理与运算 (1 个):
    - disintegrate : κ.fst otimesₖ κCond = κ
-/
class IsCondKernel : Prop where
  protected disintegrate : κ.fst otimesₖ κCond = κ

/--
Instance `instIsCondKernel_zero` / 实例 `instIsCondKernel_zero`

English:
instance instIsCondKernel_zero
  signature: (κCond : Kernel (α × β) Ω)
  body: by simp

中文:
实例 instIsCondKernel_zero
  签名: (κCond : 核 (α × β) Ω)
  定义体: by simp
-/
instance instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond where
  disintegrate := by simp

/--
lemma `disintegrate` / 引理 `disintegrate`

English:
lemma disintegrate
  given: [κ.IsCondKernel κCond]
  statement: κ.fst otimesₖ κCond = κ
  proof: IsCondKernel.disintegrate

中文:
引理 disintegrate
  条件: [κ.是余ndKernel κCond]
  结论: κ.fst otimesₖ κCond = κ
  证明: IsCondKernel.disintegrate

Depends on / 依赖: IsCondKernel, IsCondKernel.disintegrate, disintegrate
-/
lemma disintegrate [κ.IsCondKernel κCond] : κ.fst otimesₖ κCond = κ := IsCondKernel.disintegrate

/--
lemma `IsCondKernel.isProbabilityMeasure_ae` / 引理 `IsCondKernel.isProbabilityMeasure_ae`

English:
lemma IsCondKernel.isProbabilityMeasure_ae
  given: [IsFiniteKernel κ.fst] [κ.IsCondKernel κCond] (a : α)
  proof: by
  have h := disintegrate κ κCond
  by_cases h_sfin : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin] at h; simp [h.symm]
  suffices forallᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ => measure_univ, fun h => ⟨

中文:
引理 是余ndKernel.isProbabilityMeasure_ae
  条件: [是FiniteKernel κ.fst] [κ.是余ndKernel κCond] (a : α)
  证明: by
  have h := disintegrate κ κCond
  by_cases h_sfin : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin] at h; simp [h.symm]
  suffices forallᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ => measure_univ, fun h => ⟨

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.compProd_of_not_isSFiniteKernel_right, Measurabl, Set.univ, compProd_of_not_isSFiniteKernel_right, convert, disintegrate, filter_upwards, h.symm, h_eq, h_sfin, le_antisymm, measure_univ
-/
lemma IsCondKernel.isProbabilityMeasure_ae [IsFiniteKernel κ.fst] [κ.IsCondKernel κCond] (a : α) :
    forallᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have h := disintegrate κ κCond
  by_cases h_sfin : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin] at h; simp [h.symm]
  suffices forallᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ => measure_univ, fun h => ⟨h⟩⟩
  suffices (forallᵐ b ∂(κ.fst a), κCond (a, b) Set.univ <= 1)
      ∧ (forallᵐ b ∂(κ.fst a), 1 <= κCond (a, b) Set.univ) by
    filter_upwards [this.1, this.2] with b h1 h2 using le_antisymm h1 h2
  have h_eq s (hs : MeasurableSet s) :
      ∫⁻ b, s.indicator (fun b => κCond (a, b) Set.univ) b ∂κ.fst a = κ.fst a s := by
    conv_rhs => rw [← h]
    rw [fst_compProd_apply _ _ _ hs]
  have h_meas : Measurable fun b => κCond (a, b) Set.univ :=
    (κCond.measurable_coe MeasurableSet.univ).comp measurable_prodMk_left
  constructor
  · rw [ae_le_const_iff_forall_gt_measure_zero]
    intro r hr
    let s := {b | r <= κCond (a, b) Set.univ}
    have hs : MeasurableSet s := h_meas measurableSet_Ici
    have h_2_le : s.indicator (fun _ => r) <= s.indicator (fun b => (κCond (a, b)) Set.univ) := by
      intro b
      by_cases hbs : b in s
      · simpa [hbs]
      · simp [hbs]
    have : ∫⁻ b, s.indicator (fun _ => r) b ∂(κ.fst a) <= κ.fst a s :=
      (lintegral_mono h_2_le).trans_eq (h_eq s hs)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_lhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness
  · rw [ae_const_le_iff_forall_lt_measure_zero]
    intro r hr
    let s := {b | κCond (a, b) Set.univ <= r}
    have hs : MeasurableSet s := h_meas measurableSet_Iic
    have h_2_le : s.indicator (fun b => (κCond (a, b)) Set.univ) <= s.indicator (fun _ => r) := by
      intro b
      by_cases hbs : b in s
      · simpa [hbs]
      · simp [hbs]
    have : κ.fst a s <= ∫⁻ b, s.indicator (fun _ => r) b ∂(κ.fst a) :=
      (h_eq s hs).symm.trans_le (lintegral_mono h_2_le)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_rhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness


/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable
variable [Countable α] (κCond : α -> Kernel β Ω)

/--
Definition of `condKernelCountable` / `condKernelCountable` 的定义

English:
definition condKernelCountable
  signature: (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y)
  body: κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a => (κCond a).measurable) fun x y hx hy => ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl

中文:
定义 condKernelCountable
  签名: (h_atom : 对任意 x y, x in measurableAtom y -> κCond x = κCond y)
  定义体: κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a => (κCond a).measurable) fun x y hx hy => ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl
-/
noncomputable def condKernelCountable (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a => (κCond a).measurable) fun x y hx hy => ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl

/--
lemma `condKernelCountable_apply` / 引理 `condKernelCountable_apply`

English:
lemma condKernelCountable_apply
  statement: (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y)
  proof: rfl

中文:
引理 condKernelCountable_apply
  结论: (h_atom : 对任意 x y, x in measurableAtom y -> κCond x = κCond y)
  证明: rfl
-/
lemma condKernelCountable_apply (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y)
    (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p.2 := rfl

/--
Instance `condKernelCountable.instIsMarkovKernel` / 实例 `condKernelCountable.instIsMarkovKernel`

English:
instance condKernelCountable.instIsMarkovKernel
  signature: [forall a, IsMarkovKernel (κCond a)]
  body: (‹forall a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

中文:
实例 condKernelCountable.instIsMarkovKernel
  签名: [对任意 a, 是MarkovKernel (κCond a)]
  定义体: (‹forall a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AtPrime, IsLocalRing, IsLocalRing.maximalIdeal, IsMarkovKernel, IsScalarTower, IsScalarTower.toAlgHom, LiesOver, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, P.ResidueField, P.primeCompl, ResidueField, RingHom, RingHom.surjectiveOnStalks_of_isLocalization, algebraOfLiesOver, e.symm.surjective, e.symm.toLinearMap
-/
instance condKernelCountable.instIsMarkovKernel [forall a, IsMarkovKernel (κCond a)]
     (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y) :
    IsMarkovKernel (condKernelCountable κCond h_atom) where
  isProbabilityMeasure p := (‹forall a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

/--
Instance `condKernelCountable.instIsCondKernel` / 实例 `condKernelCountable.instIsCondKernel`

English:
instance condKernelCountable.instIsCondKernel
  signature: [forall a, IsMarkovKernel (κCond a)]
  body: by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

中文:
实例 condKernelCountable.instIsCondKernel
  签名: [对任意 a, 是MarkovKernel (κCond a)]
  定义体: by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

Depends on / 依赖: Measure, Measure.compProd_apply, compProd_apply, condKernelCountable_apply, conv_rhs, disintegrate, simp_rw
-/
instance condKernelCountable.instIsCondKernel [forall a, IsMarkovKernel (κCond a)]
    (h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y) (κ : Kernel α (β × Ω))
    [IsSFiniteKernel κ] [forall a, (κ a).IsCondKernel (κCond a)] :
    κ.IsCondKernel (condKernelCountable κCond h_atom) := by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable
end ProbabilityTheory.Kernel
