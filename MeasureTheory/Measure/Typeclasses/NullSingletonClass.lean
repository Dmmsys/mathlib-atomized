/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.DiscreteSubset

/-!
# Measures having value zero on singletons

## TODO

Add a `NoAtoms` class defined as
`∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s`.
This implies `NullSingletonClass` but the converse is not true.
-/

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/--
Definition of `NullSingletonClass` / `NullSingletonClass` 的定义

English:
class NullSingletonClass
  parameters: {m0 : MeasurableSpace α} (μ : Measure α)
  axioms and operations (1):
    - measure_singleton : forall x, μ {x} = 0

中文:
类 NullSingleton类
  参数: {m0 : 可测空间 α} (μ : 测度 α)
  公理与运算 (1 个):
    - measure_singleton : 对任意 x, μ {x} = 0
-/
class NullSingletonClass {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : forall x, μ {x} = 0

@[deprecated (since := "2026-06-09")]
alias NoAtoms := NullSingletonClass

export MeasureTheory.NullSingletonClass (measure_singleton)

attribute [simp] measure_singleton

variable [NullSingletonClass μ]

/--
theorem `_root_.Set.Subsingleton.measure_zero` / 定理 `_root_.Set.Subsingleton.measure_zero`

English:
theorem _root_.Set.Subsingleton.measure_zero
  statement: (hs : s.Subsingleton) (μ : Measure α)
  proof: hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

中文:
定理 _root_.集合.子单例.measure_zero
  结论: (hs : s.子单例) (μ : 测度 α)
  证明: hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

Depends on / 依赖: hs.induction_on, induction_on, measure_empty, measure_singleton
-/
theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α)
    [NullSingletonClass μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

/--
theorem `Measure.restrict_singleton'` / 定理 `Measure.restrict_singleton'`

English:
theorem Measure.restrict_singleton'
  given: {a : α}
  statement: μ.restrict {a} = 0
  proof: by
  simp only [measure_singleton, Measure.restrict_eq_zero]

中文:
定理 测度.restrict_singleton'
  条件: {a : α}
  结论: μ.restrict {a} = 0
  证明: by
  simp only [measure_singleton, Measure.restrict_eq_zero]

Depends on / 依赖: Measure, Measure.restrict_eq_zero, measure_singleton, restrict_eq_zero
-/
theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, Measure.restrict_eq_zero]

/--
Instance `Measure.restrict.instNullSingletonClass` / 实例 `Measure.restrict.instNullSingletonClass`

English:
instance Measure.restrict.instNullSingletonClass
  signature: (s : Set α)
  body: by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2

中文:
实例 测度.restrict.instNullSingletonClass
  签名: (s : 集合 α)
  定义体: by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2

Depends on / 依赖: Measure, Measure.restrict_apply, exists_measurable_superset_of_null, inter_subset_left, measure_mono_null, measure_singleton, restrict_apply
-/
instance Measure.restrict.instNullSingletonClass (s : Set α) :
    NullSingletonClass (μ.restrict s) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2

/--
theorem `_root_.Set.Countable.measure_zero` / 定理 `_root_.Set.Countable.measure_zero`

English:
theorem _root_.Set.Countable.measure_zero
  given: (h : s.Countable) (μ : Measure α) [NullSingletonClass μ]
  proof: by
  rw [← biUnion_of_singleton s]; rw [measure_biUnion_null_iff h]
  simp

中文:
定理 _root_.集合.可数.measure_zero
  条件: (h : s.可数) (μ : 测度 α) [NullSingleton类 μ]
  证明: by
  rw [← biUnion_of_singleton s]; rw [measure_biUnion_null_iff h]
  simp

Depends on / 依赖: biUnion_of_singleton, measure_biUnion_null_iff
-/
theorem _root_.Set.Countable.measure_zero (h : s.Countable) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 := by
  rw [← biUnion_of_singleton s]; rw [measure_biUnion_null_iff h]
  simp

/--
theorem `_root_.Set.Countable.ae_notMem` / 定理 `_root_.Set.Countable.ae_notMem`

English:
theorem _root_.Set.Countable.ae_notMem
  given: (h : s.Countable) (μ : Measure α) [NullSingletonClass μ]
  proof: by
  simpa only [ae_iff, Classical.not_not] using! h.measure_zero μ

中文:
定理 _root_.集合.可数.ae_notMem
  条件: (h : s.可数) (μ : 测度 α) [NullSingleton类 μ]
  证明: by
  simpa only [ae_iff, Classical.not_not] using! h.measure_zero μ

Depends on / 依赖: Classical, Classical.not_not, ae_iff, h.measure_zero, measure_zero, not_not
-/
theorem _root_.Set.Countable.ae_notMem (h : s.Countable) (μ : Measure α) [NullSingletonClass μ] :
    forallᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using! h.measure_zero μ

/--
lemma `Measure.ae_ne` / 引理 `Measure.ae_ne`

English:
lemma Measure.ae_ne
  given: (μ : Measure α) [NullSingletonClass μ] (a : α)
  statement: forallᵐ x ∂μ, x != a
  proof: (countable_singleton a).ae_notMem μ

中文:
引理 测度.ae_ne
  条件: (μ : 测度 α) [NullSingleton类 μ] (a : α)
  结论: 对任意ᵐ x ∂μ, x != a
  证明: (countable_singleton a).ae_notMem μ

Depends on / 依赖: ae_notMem, countable_singleton
-/
lemma Measure.ae_ne (μ : Measure α) [NullSingletonClass μ] (a : α) : forallᵐ x ∂μ, x != a :=
  (countable_singleton a).ae_notMem μ

/--
lemma `_root_.Set.Countable.measure_restrict_compl` / 引理 `_root_.Set.Countable.measure_restrict_compl`

English:
lemma _root_.Set.Countable.measure_restrict_compl
  statement: (h : s.Countable) (μ : Measure α)
  proof: restrict_eq_self_of_ae_mem h.ae_notMem μ

@[simp]

中文:
引理 _root_.集合.可数.measure_restrict_compl
  结论: (h : s.可数) (μ : 测度 α)
  证明: restrict_eq_self_of_ae_mem h.ae_notMem μ

@[simp]

Depends on / 依赖: ae_notMem, h.ae_notMem, restrict_eq_self_of_ae_mem
-/
lemma _root_.Set.Countable.measure_restrict_compl (h : s.Countable) (μ : Measure α)
    [NullSingletonClass μ] :
    μ.restrict sᶜ = μ :=
restrict_eq_self_of_ae_mem h.ae_notMem μ

@[simp]
/--
lemma `restrict_compl_singleton` / 引理 `restrict_compl_singleton`

English:
lemma restrict_compl_singleton
  given: (a : α)
  statement: μ.restrict ({a}ᶜ) = μ
  proof: (countable_singleton _).measure_restrict_compl μ

中文:
引理 restrict_compl_singleton
  条件: (a : α)
  结论: μ.restrict ({a}ᶜ) = μ
  证明: (countable_singleton _).measure_restrict_compl μ

Depends on / 依赖: countable_singleton, measure_restrict_compl
-/
lemma restrict_compl_singleton (a : α) : μ.restrict ({a}ᶜ) = μ :=
  (countable_singleton _).measure_restrict_compl μ

/--
theorem `_root_.Set.Finite.measure_zero` / 定理 `_root_.Set.Finite.measure_zero`

English:
theorem _root_.Set.Finite.measure_zero
  given: (h : s.Finite) (μ : Measure α) [NullSingletonClass μ]
  proof: h.countable.measure_zero μ

中文:
定理 _root_.集合.有限.measure_zero
  条件: (h : s.有限) (μ : 测度 α) [NullSingleton类 μ]
  证明: h.countable.measure_zero μ

Depends on / 依赖: countable, h.countable.measure_zero, measure_zero
-/
theorem _root_.Set.Finite.measure_zero (h : s.Finite) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 :=
  h.countable.measure_zero μ

/--
theorem `_root_.Finset.measure_zero` / 定理 `_root_.Finset.measure_zero`

English:
theorem _root_.Finset.measure_zero
  given: (s : Finset α) (μ : Measure α) [NullSingletonClass μ]
  proof: s.finite_toSet.measure_zero μ

中文:
定理 _root_.有限集.measure_zero
  条件: (s : 有限集 α) (μ : 测度 α) [NullSingleton类 μ]
  证明: s.finite_toSet.measure_zero μ

Depends on / 依赖: finite_toSet, measure_zero, s.finite_toSet.measure_zero
-/
theorem _root_.Finset.measure_zero (s : Finset α) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 :=
  s.finite_toSet.measure_zero μ

/--
theorem `insert_ae_eq_self` / 定理 `insert_ae_eq_self`

English:
theorem insert_ae_eq_self
  given: (a : α) (s : Set α)
  statement: (insert a s : Set α) =ᵐ[μ] s
  proof: union_ae_eq_right.2 measure_mono_null sdiff_subset (measure_singleton _)

中文:
定理 insert_ae_eq_self
  条件: (a : α) (s : 集合 α)
  结论: (insert a s : 集合 α) =ᵐ[μ] s
  证明: union_ae_eq_right.2 measure_mono_null sdiff_subset (measure_singleton _)

Depends on / 依赖: measure_mono_null, measure_singleton, sdiff_subset, union_ae_eq_right
-/
theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
union_ae_eq_right.2 measure_mono_null sdiff_subset (measure_singleton _)

/--
theorem `exists_accPt_of_nullSingletonClass` / 定理 `exists_accPt_of_nullSingletonClass`

English:
theorem exists_accPt_of_nullSingletonClass
  statement: {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  proof: by
  by_contra! h
  have : DiscreteTopology E := discreteTopology_of_noAccPts fun x _ => h x
exact hE.ne' (Set.countable_coe_iff.mp <| separableSpace_iff_countable.mp ‹_›).measure_zero μ

@[deprecated (since := "2026-06-09")]
alias exists_accPt_of_noAtoms := exists_accPt_of_nullSingletonClass

中文:
定理 存在_accPt_of_nullSingletonClass
  结论: {X : 类型} [拓扑空间 X] [可测空间 X]
  证明: by
  by_contra! h
  have : DiscreteTopology E := discreteTopology_of_noAccPts fun x _ => h x
exact hE.ne' (Set.countable_coe_iff.mp <| separableSpace_iff_countable.mp ‹_›).measure_zero μ

@[deprecated (since := "2026-06-09")]
alias exists_accPt_of_noAtoms := exists_accPt_of_nullSingletonClass

Depends on / 依赖: DiscreteTopology, Set.countable_coe_iff.mp, countable_coe_iff, discreteTopology_of_noAccPts, hE.ne, measure_zero, separableSpace_iff_countable, separableSpace_iff_countable.mp
-/
theorem exists_accPt_of_nullSingletonClass {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [NullSingletonClass μ] {E : Set X} [SeparableSpace E] (hE : 0 < μ E) :
    exists x, AccPt x (𝓟 E) := by
  by_contra! h
  have : DiscreteTopology E := discreteTopology_of_noAccPts fun x _ => h x
exact hE.ne' (Set.countable_coe_iff.mp <| separableSpace_iff_countable.mp ‹_›).measure_zero μ

@[deprecated (since := "2026-06-09")]
alias exists_accPt_of_noAtoms := exists_accPt_of_nullSingletonClass

section

variable [PartialOrder α] {a b : α}

/--
theorem `Iio_ae_eq_Iic` / 定理 `Iio_ae_eq_Iic`

English:
theorem Iio_ae_eq_Iic
  statement: Iio a =ᵐ[μ] Iic a
  proof: Iio_ae_eq_Iic' (measure_singleton a)

中文:
定理 Iio_ae_eq_Iic
  结论: 左无界右开区间 a =ᵐ[μ] 左无界右闭区间 a
  证明: Iio_ae_eq_Iic' (measure_singleton a)

Depends on / 依赖: Iio_ae_eq_Iic, measure_singleton
-/
theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  Iio_ae_eq_Iic' (measure_singleton a)

/--
theorem `Ioi_ae_eq_Ici` / 定理 `Ioi_ae_eq_Ici`

English:
theorem Ioi_ae_eq_Ici
  statement: Ioi a =ᵐ[μ] Ici a
  proof: Ioi_ae_eq_Ici' (measure_singleton a)

中文:
定理 Ioi_ae_eq_Ici
  结论: 左开右无界区间 a =ᵐ[μ] 左闭右无界区间 a
  证明: Ioi_ae_eq_Ici' (measure_singleton a)

Depends on / 依赖: ComplementedLattice, Ioi_ae_eq_Ici, IsAtomic, isAtomic_of_complementedLattice, measure_singleton
-/
theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)

/--
theorem `Ioo_ae_eq_Ioc` / 定理 `Ioo_ae_eq_Ioc`

English:
theorem Ioo_ae_eq_Ioc
  statement: Ioo a b =ᵐ[μ] Ioc a b
  proof: Ioo_ae_eq_Ioc' (measure_singleton b)

中文:
定理 Ioo_ae_eq_Ioc
  结论: 开区间 a b =ᵐ[μ] 左开右闭区间 a b
  证明: Ioo_ae_eq_Ioc' (measure_singleton b)

Depends on / 依赖: ComplementedLattice, Ioo_ae_eq_Ioc, isAtomistic_of_complementedLattice, measure_singleton
-/
theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)

/--
theorem `Ioc_ae_eq_Icc` / 定理 `Ioc_ae_eq_Icc`

English:
theorem Ioc_ae_eq_Icc
  statement: Ioc a b =ᵐ[μ] Icc a b
  proof: Ioc_ae_eq_Icc' (measure_singleton a)

中文:
定理 Ioc_ae_eq_Icc
  结论: 左开右闭区间 a b =ᵐ[μ] 闭区间 a b
  证明: Ioc_ae_eq_Icc' (measure_singleton a)

Depends on / 依赖: Ioc_ae_eq_Icc, measure_singleton
-/
theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioc_ae_eq_Icc' (measure_singleton a)

/--
theorem `Ioo_ae_eq_Ico` / 定理 `Ioo_ae_eq_Ico`

English:
theorem Ioo_ae_eq_Ico
  statement: Ioo a b =ᵐ[μ] Ico a b
  proof: Ioo_ae_eq_Ico' (measure_singleton a)

中文:
定理 Ioo_ae_eq_Ico
  结论: 开区间 a b =ᵐ[μ] 左闭右开区间 a b
  证明: Ioo_ae_eq_Ico' (measure_singleton a)

Depends on / 依赖: Ioo_ae_eq_Ico, measure_singleton
-/
theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioo_ae_eq_Ico' (measure_singleton a)

/--
theorem `Ioo_ae_eq_Icc` / 定理 `Ioo_ae_eq_Icc`

English:
theorem Ioo_ae_eq_Icc
  statement: Ioo a b =ᵐ[μ] Icc a b
  proof: Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)

中文:
定理 Ioo_ae_eq_Icc
  结论: 开区间 a b =ᵐ[μ] 闭区间 a b
  证明: Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)

Depends on / 依赖: Ioo_ae_eq_Icc, measure_singleton
-/
theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)

/--
theorem `Ico_ae_eq_Icc` / 定理 `Ico_ae_eq_Icc`

English:
theorem Ico_ae_eq_Icc
  statement: Ico a b =ᵐ[μ] Icc a b
  proof: Ico_ae_eq_Icc' (measure_singleton b)

中文:
定理 Ico_ae_eq_Icc
  结论: 左闭右开区间 a b =ᵐ[μ] 闭区间 a b
  证明: Ico_ae_eq_Icc' (measure_singleton b)

Depends on / 依赖: Ico_ae_eq_Icc, measure_singleton
-/
theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  Ico_ae_eq_Icc' (measure_singleton b)

/--
theorem `Ico_ae_eq_Ioc` / 定理 `Ico_ae_eq_Ioc`

English:
theorem Ico_ae_eq_Ioc
  statement: Ico a b =ᵐ[μ] Ioc a b
  proof: Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)

中文:
定理 Ico_ae_eq_Ioc
  结论: 左闭右开区间 a b =ᵐ[μ] 左开右闭区间 a b
  证明: Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)

Depends on / 依赖: Ico_ae_eq_Ioc, measure_singleton
-/
theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)

/--
theorem `restrict_Iio_eq_restrict_Iic` / 定理 `restrict_Iio_eq_restrict_Iic`

English:
theorem restrict_Iio_eq_restrict_Iic
  statement: μ.restrict (Iio a) = μ.restrict (Iic a)
  proof: restrict_congr_set Iio_ae_eq_Iic

中文:
定理 restrict_Iio_eq_restrict_Iic
  结论: μ.restrict (左无界右开区间 a) = μ.restrict (左无界右闭区间 a)
  证明: restrict_congr_set Iio_ae_eq_Iic

Depends on / 依赖: Iio_ae_eq_Iic, restrict_congr_set
-/
theorem restrict_Iio_eq_restrict_Iic : μ.restrict (Iio a) = μ.restrict (Iic a) :=
  restrict_congr_set Iio_ae_eq_Iic

/--
theorem `restrict_Ioi_eq_restrict_Ici` / 定理 `restrict_Ioi_eq_restrict_Ici`

English:
theorem restrict_Ioi_eq_restrict_Ici
  statement: μ.restrict (Ioi a) = μ.restrict (Ici a)
  proof: restrict_congr_set Ioi_ae_eq_Ici

中文:
定理 restrict_Ioi_eq_restrict_Ici
  结论: μ.restrict (左开右无界区间 a) = μ.restrict (左闭右无界区间 a)
  证明: restrict_congr_set Ioi_ae_eq_Ici

Depends on / 依赖: Ioi_ae_eq_Ici, restrict_congr_set
-/
theorem restrict_Ioi_eq_restrict_Ici : μ.restrict (Ioi a) = μ.restrict (Ici a) :=
  restrict_congr_set Ioi_ae_eq_Ici

/--
theorem `restrict_Ioo_eq_restrict_Ioc` / 定理 `restrict_Ioo_eq_restrict_Ioc`

English:
theorem restrict_Ioo_eq_restrict_Ioc
  statement: μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
  proof: restrict_congr_set Ioo_ae_eq_Ioc

中文:
定理 restrict_Ioo_eq_restrict_Ioc
  结论: μ.restrict (开区间 a b) = μ.restrict (左开右闭区间 a b)
  证明: restrict_congr_set Ioo_ae_eq_Ioc

Depends on / 依赖: Ioo_ae_eq_Ioc, restrict_congr_set
-/
theorem restrict_Ioo_eq_restrict_Ioc : μ.restrict (Ioo a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ioo_ae_eq_Ioc

/--
theorem `restrict_Ioc_eq_restrict_Icc` / 定理 `restrict_Ioc_eq_restrict_Icc`

English:
theorem restrict_Ioc_eq_restrict_Icc
  statement: μ.restrict (Ioc a b) = μ.restrict (Icc a b)
  proof: restrict_congr_set Ioc_ae_eq_Icc

中文:
定理 restrict_Ioc_eq_restrict_Icc
  结论: μ.restrict (左开右闭区间 a b) = μ.restrict (闭区间 a b)
  证明: restrict_congr_set Ioc_ae_eq_Icc

Depends on / 依赖: Ioc_ae_eq_Icc, restrict_congr_set
-/
theorem restrict_Ioc_eq_restrict_Icc : μ.restrict (Ioc a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioc_ae_eq_Icc

/--
theorem `restrict_Ioo_eq_restrict_Ico` / 定理 `restrict_Ioo_eq_restrict_Ico`

English:
theorem restrict_Ioo_eq_restrict_Ico
  statement: μ.restrict (Ioo a b) = μ.restrict (Ico a b)
  proof: restrict_congr_set Ioo_ae_eq_Ico

中文:
定理 restrict_Ioo_eq_restrict_Ico
  结论: μ.restrict (开区间 a b) = μ.restrict (左闭右开区间 a b)
  证明: restrict_congr_set Ioo_ae_eq_Ico

Depends on / 依赖: Ioo_ae_eq_Ico, restrict_congr_set
-/
theorem restrict_Ioo_eq_restrict_Ico : μ.restrict (Ioo a b) = μ.restrict (Ico a b) :=
  restrict_congr_set Ioo_ae_eq_Ico

/--
theorem `restrict_Ioo_eq_restrict_Icc` / 定理 `restrict_Ioo_eq_restrict_Icc`

English:
theorem restrict_Ioo_eq_restrict_Icc
  statement: μ.restrict (Ioo a b) = μ.restrict (Icc a b)
  proof: restrict_congr_set Ioo_ae_eq_Icc

中文:
定理 restrict_Ioo_eq_restrict_Icc
  结论: μ.restrict (开区间 a b) = μ.restrict (闭区间 a b)
  证明: restrict_congr_set Ioo_ae_eq_Icc

Depends on / 依赖: Ioo_ae_eq_Icc, restrict_congr_set
-/
theorem restrict_Ioo_eq_restrict_Icc : μ.restrict (Ioo a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioo_ae_eq_Icc

/--
theorem `restrict_Ico_eq_restrict_Icc` / 定理 `restrict_Ico_eq_restrict_Icc`

English:
theorem restrict_Ico_eq_restrict_Icc
  statement: μ.restrict (Ico a b) = μ.restrict (Icc a b)
  proof: restrict_congr_set Ico_ae_eq_Icc

中文:
定理 restrict_Ico_eq_restrict_Icc
  结论: μ.restrict (左闭右开区间 a b) = μ.restrict (闭区间 a b)
  证明: restrict_congr_set Ico_ae_eq_Icc

Depends on / 依赖: Ico_ae_eq_Icc, restrict_congr_set
-/
theorem restrict_Ico_eq_restrict_Icc : μ.restrict (Ico a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ico_ae_eq_Icc

/--
theorem `restrict_Ico_eq_restrict_Ioc` / 定理 `restrict_Ico_eq_restrict_Ioc`

English:
theorem restrict_Ico_eq_restrict_Ioc
  statement: μ.restrict (Ico a b) = μ.restrict (Ioc a b)
  proof: restrict_congr_set Ico_ae_eq_Ioc

中文:
定理 restrict_Ico_eq_restrict_Ioc
  结论: μ.restrict (左闭右开区间 a b) = μ.restrict (左开右闭区间 a b)
  证明: restrict_congr_set Ico_ae_eq_Ioc

Depends on / 依赖: Ico_ae_eq_Ioc, restrict_congr_set
-/
theorem restrict_Ico_eq_restrict_Ioc : μ.restrict (Ico a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ico_ae_eq_Ioc

end

open Interval

open scoped Interval in
/--
theorem `uIoc_ae_eq_interval` / 定理 `uIoc_ae_eq_interval`

English:
theorem uIoc_ae_eq_interval
  given: [LinearOrder α] {a b : α}
  statement: Ι a b =ᵐ[μ] [[a, b]]
  proof: Ioc_ae_eq_Icc

中文:
定理 uIoc_ae_eq_interval
  条件: [线性序 α] {a b : α}
  结论: Ι a b =ᵐ[μ] [[a, b]]
  证明: Ioc_ae_eq_Icc

Depends on / 依赖: Ioc_ae_eq_Icc
-/
theorem uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [[a, b]] :=
  Ioc_ae_eq_Icc

end MeasureTheory
