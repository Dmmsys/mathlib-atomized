/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Classes for finite measures

We introduce the following typeclasses for measures:

* `IsFiniteMeasure μ`: `μ univ < ∞`;
* `IsLocallyFiniteMeasure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`.
-/

@[expose] public section

open scoped NNReal Topology
open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal

variable {α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}
  {s t : Set α}

section IsFiniteMeasure

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
@[mk_iff]
/--
Definition of `IsFiniteMeasure` / `IsFiniteMeasure` 的定义

English:
class IsFiniteMeasure
  parameters: (μ : Measure α)
  axioms and operations (1):
    - measure_univ_lt_top : μ univ < ∞

中文:
类 是有限测度
  参数: (μ : 测度 α)
  公理与运算 (1 个):
    - measure_univ_lt_top : μ univ < ∞
-/
class IsFiniteMeasure (μ : Measure α) : Prop where
  measure_univ_lt_top : μ univ < ∞

/--
lemma `not_isFiniteMeasure_iff` / 引理 `not_isFiniteMeasure_iff`

English:
lemma not_isFiniteMeasure_iff
  statement: ¬IsFiniteMeasure μ ↔ μ univ = ∞
  proof: by simp [isFiniteMeasure_iff]

中文:
引理 not_isFiniteMeasure_iff
  结论: ¬是有限测度 μ ↔ μ univ = ∞
  证明: by simp [isFiniteMeasure_iff]

Depends on / 依赖: isFiniteMeasure_iff
-/
lemma not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ univ = ∞ := by simp [isFiniteMeasure_iff]

/--
lemma `isFiniteMeasure_restrict` / 引理 `isFiniteMeasure_restrict`

English:
lemma isFiniteMeasure_restrict
  statement: IsFiniteMeasure (μ.restrict s) ↔ μ s != ∞
  proof: by
  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]

中文:
引理 isFiniteMeasure_restrict
  结论: 是有限测度 (μ.restrict s) ↔ μ s != ∞
  证明: by
  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]

Depends on / 依赖: isFiniteMeasure_iff, lt_top_iff_ne_top
-/
lemma isFiniteMeasure_restrict : IsFiniteMeasure (μ.restrict s) ↔ μ s != ∞ := by
  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]

/--
Instance `Restrict.isFiniteMeasure` / 实例 `Restrict.isFiniteMeasure`

English:
instance Restrict.isFiniteMeasure
  signature: (μ : Measure α) [hs : Fact (μ s < ∞)]
  body: ⟨by simpa using hs.elim⟩

@[simp]

中文:
实例 Restrict.isFiniteMeasure
  签名: (μ : 测度 α) [hs : Fact (μ s < ∞)]
  定义体: ⟨by simpa using hs.elim⟩

@[simp]

Depends on / 依赖: hs.elim
-/
instance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simpa using hs.elim⟩

@[simp]
/--
theorem `measure_lt_top` / 定理 `measure_lt_top`

English:
theorem measure_lt_top
  given: (μ : Measure α) [IsFiniteMeasure μ] (s : Set α)
  statement: μ s < ∞
  proof: (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top

中文:
定理 measure_lt_top
  条件: (μ : 测度 α) [是有限测度 μ] (s : 集合 α)
  结论: μ s < ∞
  证明: (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.measure_univ_lt_top, measure_mono, measure_univ_lt_top, subset_univ, trans_lt
-/
theorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top

/--
Instance `isFiniteMeasureRestrict` / 实例 `isFiniteMeasureRestrict`

English:
instance isFiniteMeasureRestrict
  signature: (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ]
  body: ⟨by simp⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply]

中文:
实例 isFiniteMeasureRestrict
  签名: (μ : 测度 α) (s : 集合 α) [h : 是有限测度 μ]
  定义体: ⟨by simp⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply]
-/
instance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict s) := ⟨by simp⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `measure_ne_top` / 定理 `measure_ne_top`

English:
theorem measure_ne_top
  given: (μ : Measure α) [IsFiniteMeasure μ] (s : Set α)
  statement: μ s != ∞
  proof: ne_of_lt (measure_lt_top μ s)

中文:
定理 measure_ne_top
  条件: (μ : 测度 α) [是有限测度 μ] (s : 集合 α)
  结论: μ s != ∞
  证明: ne_of_lt (measure_lt_top μ s)

Depends on / 依赖: measure_lt_top, ne_of_lt
-/
theorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s != ∞ :=
  ne_of_lt (measure_lt_top μ s)

/--
theorem `measure_compl_le_add_of_le_add` / 定理 `measure_compl_le_add_of_le_add`

English:
theorem measure_compl_le_add_of_le_add
  statement: [IsFiniteMeasure μ] (hs : MeasurableSet s)
  proof: by
  rw [measure_compl ht (by finiteness)]; rw [measure_compl hs (by finiteness)]; rw [tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ <= μ univ - μ s + (μ t + ε) := by gcongr
    _ = _ := by rw [add_right_comm, add_assoc]

中文:
定理 measure_compl_le_add_of_le_add
  结论: [是有限测度 μ] (hs : 可测集 s)
  证明: by
  rw [measure_compl ht (by finiteness)]; rw [measure_compl hs (by finiteness)]; rw [tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ <= μ univ - μ s + (μ t + ε) := by gcongr
    _ = _ := by rw [add_right_comm, add_assoc]

Depends on / 依赖: add_assoc, add_right_comm, finiteness, measure_compl, measure_mono, s.subset_univ, subset_univ, tsub_add_cancel_of_le, tsub_le_iff_right
-/
theorem measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) {ε : Real>=0∞} (h : μ s <= μ t + ε) : μ tᶜ <= μ sᶜ + ε := by
  rw [measure_compl ht (by finiteness)]; rw [measure_compl hs (by finiteness)]; rw [tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ <= μ univ - μ s + (μ t + ε) := by gcongr
    _ = _ := by rw [add_right_comm, add_assoc]

/--
theorem `measure_compl_le_add_iff` / 定理 `measure_compl_le_add_iff`

English:
theorem measure_compl_le_add_iff
  statement: [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩

中文:
定理 measure_compl_le_add_iff
  结论: [是有限测度 μ] (hs : 可测集 s) (ht : 可测集 t)
  证明: ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩

Depends on / 依赖: compl_compl, hs.compl, ht.compl, measure_compl_le_add_of_le_add
-/
theorem measure_compl_le_add_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
    {ε : Real>=0∞} : μ sᶜ <= μ tᶜ + ε ↔ μ t <= μ s + ε :=
  ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩

/--
theorem `cofinite_eq_bot_iff` / 定理 `cofinite_eq_bot_iff`

English:
theorem cofinite_eq_bot_iff
  statement: μ.cofinite = ⊥ ↔ IsFiniteMeasure μ
  proof: by
  simp [← empty_mem_iff_bot, μ.mem_cofinite, isFiniteMeasure_iff]

@[nontriviality, simp]

中文:
定理 cofinite_eq_bot_iff
  结论: μ.cofinite = ⊥ ↔ 是有限测度 μ
  证明: by
  simp [← empty_mem_iff_bot, μ.mem_cofinite, isFiniteMeasure_iff]

@[nontriviality, simp]

Depends on / 依赖: empty_mem_iff_bot, isFiniteMeasure_iff, mem_cofinite
-/
theorem cofinite_eq_bot_iff : μ.cofinite = ⊥ ↔ IsFiniteMeasure μ := by
  simp [← empty_mem_iff_bot, μ.mem_cofinite, isFiniteMeasure_iff]

@[nontriviality, simp]
/--
theorem `cofinite_eq_bot` / 定理 `cofinite_eq_bot`

English:
theorem cofinite_eq_bot
  given: [IsFiniteMeasure μ]
  statement: μ.cofinite = ⊥
  proof: cofinite_eq_bot_iff.2 ‹_›

中文:
定理 cofinite_eq_bot
  条件: [是有限测度 μ]
  结论: μ.cofinite = ⊥
  证明: cofinite_eq_bot_iff.2 ‹_›

Depends on / 依赖: cofinite_eq_bot_iff
-/
theorem cofinite_eq_bot [IsFiniteMeasure μ] : μ.cofinite = ⊥ := cofinite_eq_bot_iff.2 ‹_›

/--
Definition of `measureUnivNNReal` / `measureUnivNNReal` 的定义

English:
definition measureUnivNNReal
  signature: (μ : Measure α)
  body: (μ univ).toNNReal

@[simp]

中文:
定义 measureUnivNN实数
  签名: (μ : 测度 α)
  定义体: (μ univ).toNNReal

@[simp]

Depends on / 依赖: toNNReal
-/
def measureUnivNNReal (μ : Measure α) : Real>=0 :=
  (μ univ).toNNReal

@[simp]
/--
theorem `coe_measureUnivNNReal` / 定理 `coe_measureUnivNNReal`

English:
theorem coe_measureUnivNNReal
  given: (μ : Measure α) [IsFiniteMeasure μ]
  proof: ENNReal.coe_toNNReal (by finiteness)

中文:
定理 coe_measureUnivNN实数
  条件: (μ : 测度 α) [是有限测度 μ]
  证明: ENNReal.coe_toNNReal (by finiteness)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, ENNReal, ENNReal.coe_toNNReal, Preord, coe_toNNReal, finiteness
-/
theorem coe_measureUnivNNReal (μ : Measure α) [IsFiniteMeasure μ] :
    ↑(measureUnivNNReal μ) = μ univ :=
  ENNReal.coe_toNNReal (by finiteness)

/--
Instance `isFiniteMeasureZero` / 实例 `isFiniteMeasureZero`

English:
instance isFiniteMeasureZero
  signature: : IsFiniteMeasure (0 : Measure α)
  body: ⟨by simp⟩

中文:
实例 isFiniteMeasureZero
  签名: : 是有限测度 (0 : 测度 α)
  定义体: ⟨by simp⟩
-/
instance isFiniteMeasureZero : IsFiniteMeasure (0 : Measure α) :=
  ⟨by simp⟩

instance (priority := 50) isFiniteMeasureOfIsEmpty [IsEmpty α] : IsFiniteMeasure μ := by
  rw [eq_zero_of_isEmpty μ]
  infer_instance

@[simp]
/--
theorem `measureUnivNNReal_zero` / 定理 `measureUnivNNReal_zero`

English:
theorem measureUnivNNReal_zero
  statement: measureUnivNNReal (0 : Measure α) = 0
  proof: rfl

中文:
定理 measureUnivNN实数_zero
  结论: measureUnivNN实数 (0 : 测度 α) = 0
  证明: rfl

Depends on / 依赖: f.hom
-/
theorem measureUnivNNReal_zero : measureUnivNNReal (0 : Measure α) = 0 :=
  rfl

/--
Instance `isFiniteMeasureAdd` / 实例 `isFiniteMeasureAdd`

English:
instance isFiniteMeasureAdd
  signature: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  body: by
    rw [Measure.coe_add]; rw [Pi.add_apply]; rw [ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩

中文:
实例 isFiniteMeasureAdd
  签名: [是有限测度 μ] [是有限测度 ν]
  定义体: by
    rw [Measure.coe_add]; rw [Pi.add_apply]; rw [ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, Measure, Measure.coe_add, Pi.add_apply, add_apply, add_lt_top, coe_add, measure_lt_top
-/
instance isFiniteMeasureAdd [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ + ν) where
  measure_univ_lt_top := by
    rw [Measure.coe_add]; rw [Pi.add_apply]; rw [ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩

/--
Instance `isFiniteMeasureSMulNNReal` / 实例 `isFiniteMeasureSMulNNReal`

English:
instance isFiniteMeasureSMulNNReal
  signature: [IsFiniteMeasure μ] {r : Real>=0}
  body: ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

中文:
实例 isFiniteMeasureSMulNN实数
  签名: [是有限测度 μ] {r : 实数>=0}
  定义体: ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, measure_lt_top, mul_lt_top
-/
instance isFiniteMeasureSMulNNReal [IsFiniteMeasure μ] {r : Real>=0} : IsFiniteMeasure (r • μ) where
  measure_univ_lt_top := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

/--
Instance `IsFiniteMeasure.average` / 实例 `IsFiniteMeasure.average`

English:
instance IsFiniteMeasure.average
  signature: : IsFiniteMeasure ((μ univ)⁻¹ • μ) where
  body: by
    rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

中文:
实例 是有限测度.average
  签名: : 是有限测度 ((μ univ)⁻¹ • μ) where
  定义体: by
    rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.div_self_le_one.trans_lt, ENNReal.one_lt_top, Measure, Measure.smul_apply, div_eq_inv_mul, div_self_le_one, one_lt_top, smul_apply, smul_eq_mul, trans_lt
-/
instance IsFiniteMeasure.average : IsFiniteMeasure ((μ univ)⁻¹ • μ) where
  measure_univ_lt_top := by
    rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

/--
Instance `isFiniteMeasureSMulOfNNRealTower` / 实例 `isFiniteMeasureSMulOfNNRealTower`

English:
instance isFiniteMeasureSMulOfNNRealTower
  signature: {R} [SMul R Real>=0] [SMul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0∞]
  body: by
  rw [← smul_one_smul Real>=0 r μ]
  infer_instance

中文:
实例 isFiniteMeasureSMulOfNN实数Tower
  签名: {R} [标量乘法 R 实数>=0] [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0 实数>=0∞]
  定义体: by
  rw [← smul_one_smul Real>=0 r μ]
  infer_instance

Depends on / 依赖: infer_instance, smul_one_smul
-/
instance isFiniteMeasureSMulOfNNRealTower {R} [SMul R Real>=0] [SMul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0∞]
    [IsScalarTower R Real>=0∞ Real>=0∞] [IsFiniteMeasure μ] {r : R} : IsFiniteMeasure (r • μ) := by
  rw [← smul_one_smul Real>=0 r μ]
  infer_instance

/--
theorem `isFiniteMeasure_of_le` / 定理 `isFiniteMeasure_of_le`

English:
theorem isFiniteMeasure_of_le
  given: (μ : Measure α) [IsFiniteMeasure μ] (h : ν <= μ)
  statement: IsFiniteMeasure ν
  proof: { measure_univ_lt_top := (h Set.univ).trans_lt (measure_lt_top _ _) }

@[instance]

中文:
定理 isFiniteMeasure_of_le
  条件: (μ : 测度 α) [是有限测度 μ] (h : ν <= μ)
  结论: 是有限测度 ν
  证明: { measure_univ_lt_top := (h Set.univ).trans_lt (measure_lt_top _ _) }

@[instance]

Depends on / 依赖: Set.univ, measure_lt_top, measure_univ_lt_top, trans_lt
-/
theorem isFiniteMeasure_of_le (μ : Measure α) [IsFiniteMeasure μ] (h : ν <= μ) : IsFiniteMeasure ν :=
  { measure_univ_lt_top := (h Set.univ).trans_lt (measure_lt_top _ _) }

@[instance]
/--
theorem `Measure.isFiniteMeasure_map` / 定理 `Measure.isFiniteMeasure_map`

English:
theorem Measure.isFiniteMeasure_map
  statement: {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
  proof: by
  by_cases hf : AEMeasurable f μ
  · constructor
    rw [map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_aemeasurable hf]
    exact MeasureTheory.isFiniteMeasureZero

中文:
定理 测度.isFiniteMeasure_map
  结论: {m : 可测空间 α} (μ : 测度 α) [是有限测度 μ]
  证明: by
  by_cases hf : AEMeasurable f μ
  · constructor
    rw [map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_aemeasurable hf]
    exact MeasureTheory.isFiniteMeasureZero

Depends on / 依赖: AEMeasurable, MeasurableSet, MeasurableSet.univ, MeasureTheory, MeasureTheory.isFiniteMeasureZero, isFiniteMeasureZero, map_apply_of_aemeasurable, map_of_not_aemeasurable, measure_lt_top
-/
theorem Measure.isFiniteMeasure_map {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : α -> β) : IsFiniteMeasure (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · constructor
    rw [map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_aemeasurable hf]
    exact MeasureTheory.isFiniteMeasureZero

/--
theorem `Measure.isFiniteMeasure_of_map` / 定理 `Measure.isFiniteMeasure_of_map`

English:
theorem Measure.isFiniteMeasure_of_map
  statement: {μ : Measure α} {f : α -> β}
  proof: by
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsFiniteMeasure.measure_univ_lt_top

中文:
定理 测度.isFiniteMeasure_of_map
  结论: {μ : 测度 α} {f : α -> β}
  证明: by
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsFiniteMeasure.measure_univ_lt_top

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.measure_univ_lt_top, Set.preimage_univ, map_apply_of_aemeasurable, measure_univ_lt_top, preimage_univ
-/
theorem Measure.isFiniteMeasure_of_map {μ : Measure α} {f : α -> β}
    (hf : AEMeasurable f μ) [IsFiniteMeasure (μ.map f)] : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsFiniteMeasure.measure_univ_lt_top

/--
theorem `Measure.isFiniteMeasure_map_iff` / 定理 `Measure.isFiniteMeasure_map_iff`

English:
theorem Measure.isFiniteMeasure_map_iff
  statement: {μ : Measure α} {f : α -> β}
  proof: ⟨fun _ => isFiniteMeasure_of_map hf, fun _ => isFiniteMeasure_map μ f⟩

中文:
定理 测度.isFiniteMeasure_map_iff
  结论: {μ : 测度 α} {f : α -> β}
  证明: ⟨fun _ => isFiniteMeasure_of_map hf, fun _ => isFiniteMeasure_map μ f⟩

Depends on / 依赖: isFiniteMeasure_map, isFiniteMeasure_of_map
-/
theorem Measure.isFiniteMeasure_map_iff {μ : Measure α} {f : α -> β}
    (hf : AEMeasurable f μ) : IsFiniteMeasure (μ.map f) ↔ IsFiniteMeasure μ :=
  ⟨fun _ => isFiniteMeasure_of_map hf, fun _ => isFiniteMeasure_map μ f⟩

/--
Instance `IsFiniteMeasure_comap` / 实例 `IsFiniteMeasure_comap`

English:
instance IsFiniteMeasure_comap
  signature: (f : β -> α) [IsFiniteMeasure μ]
  body: (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

@[simp]

中文:
实例 IsFiniteMeasure_comap
  签名: (f : β -> α) [是有限测度 μ]
  定义体: (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

@[simp]

Depends on / 依赖: Measure, Measure.comap_apply_le, comap_apply_le, measure_lt_top, nullMeasurableSet_univ, trans_lt
-/
instance IsFiniteMeasure_comap (f : β -> α) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.comap f) where
  measure_univ_lt_top :=
    (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

@[simp]
/--
theorem `measureUnivNNReal_eq_zero` / 定理 `measureUnivNNReal_eq_zero`

English:
theorem measureUnivNNReal_eq_zero
  given: [IsFiniteMeasure μ]
  statement: measureUnivNNReal μ = 0 ↔ μ = 0
  proof: by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero]; rw [← coe_measureUnivNNReal]
  norm_cast

中文:
定理 measureUnivNN实数_eq_zero
  条件: [是有限测度 μ]
  结论: measureUnivNN实数 μ = 0 ↔ μ = 0
  证明: by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero]; rw [← coe_measureUnivNNReal]
  norm_cast

Depends on / 依赖: Measure, MeasureTheory, MeasureTheory.Measure.measure_univ_eq_zero, coe_measureUnivNNReal, measure_univ_eq_zero
-/
theorem measureUnivNNReal_eq_zero [IsFiniteMeasure μ] : measureUnivNNReal μ = 0 ↔ μ = 0 := by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero]; rw [← coe_measureUnivNNReal]
  norm_cast

/--
theorem `measureUnivNNReal_pos` / 定理 `measureUnivNNReal_pos`

English:
theorem measureUnivNNReal_pos
  given: [IsFiniteMeasure μ] (hμ : μ != 0)
  statement: 0 < measureUnivNNReal μ
  proof: by
  contrapose! hμ
  simpa [measureUnivNNReal_eq_zero, Nat.le_zero] using hμ

中文:
定理 measureUnivNN实数_pos
  条件: [是有限测度 μ] (hμ : μ != 0)
  结论: 0 < measureUnivNN实数 μ
  证明: by
  contrapose! hμ
  simpa [measureUnivNNReal_eq_zero, Nat.le_zero] using hμ

Depends on / 依赖: Nat.le_zero, contrapose, le_zero, measureUnivNNReal_eq_zero
-/
theorem measureUnivNNReal_pos [IsFiniteMeasure μ] (hμ : μ != 0) : 0 < measureUnivNNReal μ := by
  contrapose! hμ
  simpa [measureUnivNNReal_eq_zero, Nat.le_zero] using hμ

/--
theorem `Measure.le_of_add_le_add_left` / 定理 `Measure.le_of_add_le_add_left`

English:
theorem Measure.le_of_add_le_add_left
  given: [IsFiniteMeasure μ] (A2 : μ + ν₁ <= μ + ν₂)
  statement: ν₁ <= ν₂
  proof: fun S => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S)

中文:
定理 测度.le_of_add_le_add_left
  条件: [是有限测度 μ] (A2 : μ + ν₁ <= μ + ν₂)
  结论: ν₁ <= ν₂
  证明: fun S => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S)

Depends on / 依赖: ENNReal, ENNReal.le_of_add_le_add_left, MeasureTheory, MeasureTheory.measure_ne_top, le_of_add_le_add_left, measure_ne_top
-/
theorem Measure.le_of_add_le_add_left [IsFiniteMeasure μ] (A2 : μ + ν₁ <= μ + ν₂) : ν₁ <= ν₂ :=
  fun S => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S)

/--
lemma `Measure.eq_of_le_of_measure_univ_eq` / 引理 `Measure.eq_of_le_of_measure_univ_eq`

English:
lemma Measure.eq_of_le_of_measure_univ_eq
  statement: [IsFiniteMeasure μ]
  proof: by
  refine le_antisymm hμν (le_intro fun s hs _ => ?_)
  by_contra! h_lt
  have h_disj : Disjoint s sᶜ := disjoint_compl_right_iff_subset.mpr subset_rfl
  rw [← union_compl_self s]; rw [measure_union h_disj hs.compl]; rw [measure_union h_disj hs.compl] at h_univ
.not_ge h_univ.symm.le exact ENNReal

中文:
引理 测度.eq_of_le_of_measure_univ_eq
  结论: [是有限测度 μ]
  证明: by
  refine le_antisymm hμν (le_intro fun s hs _ => ?_)
  by_contra! h_lt
  have h_disj : Disjoint s sᶜ := disjoint_compl_right_iff_subset.mpr subset_rfl
  rw [← union_compl_self s]; rw [measure_union h_disj hs.compl]; rw [measure_union h_disj hs.compl] at h_univ
.not_ge h_univ.symm.le exact ENNReal

Depends on / 依赖: Disjoint, ENNReal, ENNReal.add_lt_add_of_lt_of_le, add_lt_add_of_lt_of_le, disjoint_compl_right_iff_subset, disjoint_compl_right_iff_subset.mpr, finiteness, h_disj, h_lt, h_univ, h_univ.symm.le, hs.compl, le_antisymm, le_intro, measure_union, not_ge, subset_rfl, union_compl_self
-/
lemma Measure.eq_of_le_of_measure_univ_eq [IsFiniteMeasure μ]
    (hμν : μ <= ν) (h_univ : μ univ = ν univ) : μ = ν := by
  refine le_antisymm hμν (le_intro fun s hs _ => ?_)
  by_contra! h_lt
  have h_disj : Disjoint s sᶜ := disjoint_compl_right_iff_subset.mpr subset_rfl
  rw [← union_compl_self s]; rw [measure_union h_disj hs.compl]; rw [measure_union h_disj hs.compl] at h_univ
.not_ge h_univ.symm.le exact ENNReal.add_lt_add_of_lt_of_le (by finiteness) h_lt (hμν sᶜ)

/--
theorem `summable_measure_toReal` / 定理 `summable_measure_toReal`

English:
theorem summable_measure_toReal
  statement: [hμ : IsFiniteMeasure μ] {f : Nat -> Set α}
  proof: by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_iUnion hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)

中文:
定理 summable_measure_to实数
  结论: [hμ : 是有限测度 μ] {f : 自然数 -> 集合 α}
  证明: by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_iUnion hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)

Depends on / 依赖: ENNReal, ENNReal.summable_toReal, MeasureTheory, MeasureTheory.measure_iUnion, measure_iUnion, measure_lt_top, ne_of_lt, summable_toReal
-/
theorem summable_measure_toReal [hμ : IsFiniteMeasure μ] {f : Nat -> Set α}
    (hf₁ : forall i : Nat, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    Summable fun x => μ.real (f x) := by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_iUnion hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)

/--
theorem `ae_eq_univ_iff_measure_eq` / 定理 `ae_eq_univ_iff_measure_eq`

English:
theorem ae_eq_univ_iff_measure_eq
  given: [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
  proof: ⟨measure_congr, fun h => ae_eq_of_subset_of_measure_ge (subset_univ _) h.ge hs (by finiteness)⟩

中文:
定理 ae_eq_univ_iff_measure_eq
  条件: [是有限测度 μ] (hs : NullMeasurableSet s μ)
  证明: ⟨measure_congr, fun h => ae_eq_of_subset_of_measure_ge (subset_univ _) h.ge hs (by finiteness)⟩

Depends on / 依赖: ae_eq_of_subset_of_measure_ge, finiteness, h.ge, measure_congr, subset_univ
-/
theorem ae_eq_univ_iff_measure_eq [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] univ ↔ μ s = μ univ :=
  ⟨measure_congr, fun h => ae_eq_of_subset_of_measure_ge (subset_univ _) h.ge hs (by finiteness)⟩

/--
theorem `ae_iff_measure_eq` / 定理 `ae_iff_measure_eq`

English:
theorem ae_iff_measure_eq
  statement: [IsFiniteMeasure μ] {p : α -> Prop}
  proof: by
  rw [← ae_eq_univ_iff_measure_eq hp]; rw [eventuallyEq_univ]; rw [eventually_iff]

中文:
定理 ae_iff_measure_eq
  结论: [是有限测度 μ] {p : α -> 命题}
  证明: by
  rw [← ae_eq_univ_iff_measure_eq hp]; rw [eventuallyEq_univ]; rw [eventually_iff]

Depends on / 依赖: ae_eq_univ_iff_measure_eq, eventuallyEq_univ, eventually_iff
-/
theorem ae_iff_measure_eq [IsFiniteMeasure μ] {p : α -> Prop}
    (hp : NullMeasurableSet { a | p a } μ) : (forallᵐ a ∂μ, p a) ↔ μ { a | p a } = μ univ := by
  rw [← ae_eq_univ_iff_measure_eq hp]; rw [eventuallyEq_univ]; rw [eventually_iff]

/--
theorem `ae_mem_iff_measure_eq` / 定理 `ae_mem_iff_measure_eq`

English:
theorem ae_mem_iff_measure_eq
  given: [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurableSet s μ)
  proof: ae_iff_measure_eq hs

中文:
定理 ae_mem_iff_measure_eq
  条件: [是有限测度 μ] {s : 集合 α} (hs : NullMeasurableSet s μ)
  证明: ae_iff_measure_eq hs

Depends on / 依赖: ae_iff_measure_eq
-/
theorem ae_mem_iff_measure_eq [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurableSet s μ) :
    (forallᵐ a ∂μ, a in s) ↔ μ s = μ univ :=
  ae_iff_measure_eq hs

/--
lemma `tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint` / 引理 `tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint`

English:
lemma tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
  proof: by
  have decr : Antitone fun n => ⋃ i >= n, Es i :=
    fun n m hnm => biUnion_mono (fun _ hi => le_trans hnm hi) (fun _ _ => subset_rfl)
  have nothing : ⋂ n, ⋃ i >= n, Es i = ∅ := by
    apply subset_antisymm _ (empty_subset _)
    intro x hx
    simp only [mem_iInter, mem_iUnion, exists_prop] at

中文:
引理 tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
  证明: by
  have decr : Antitone fun n => ⋃ i >= n, Es i :=
    fun n m hnm => biUnion_mono (fun _ hi => le_trans hnm hi) (fun _ _ => subset_rfl)
  have nothing : ⋂ n, ⋃ i >= n, Es i = ∅ := by
    apply subset_antisymm _ (empty_subset _)
    intro x hx
    simp only [mem_iInter, mem_iUnion, exists_prop] at

Depends on / 依赖: Antitone, Es_disj, Nat.ne_of_lt, biUnion_mono, empty_subset, exists_prop, k_gt_j, le_trans, mem_iInter, mem_iUnion, ne_of_lt, ne_of_mem, nothing, subset_antisymm, subset_rfl, tendsto_measure_iInter_atTop, x_in_Es_j, x_in_Es_k
-/
lemma tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {Es : Nat -> Set X} (Es_mble : forall i, NullMeasurableSet (Es i) μ)
    (Es_disj : Pairwise fun n m => Disjoint (Es n) (Es m)) :
    Tendsto (μ ∘ fun n => ⋃ i >= n, Es i) atTop (𝓝 0) := by
  have decr : Antitone fun n => ⋃ i >= n, Es i :=
    fun n m hnm => biUnion_mono (fun _ hi => le_trans hnm hi) (fun _ _ => subset_rfl)
  have nothing : ⋂ n, ⋃ i >= n, Es i = ∅ := by
    apply subset_antisymm _ (empty_subset _)
    intro x hx
    simp only [mem_iInter, mem_iUnion, exists_prop] at hx
    obtain ⟨j, _, x_in_Es_j⟩ := hx 0
    obtain ⟨k, k_gt_j, x_in_Es_k⟩ := hx (j + 1)
    have oops := (Es_disj (Nat.ne_of_lt k_gt_j)).ne_of_mem x_in_Es_j x_in_Es_k
    contradiction
  have key := tendsto_measure_iInter_atTop (μ := μ) (fun n => by measurability)
    decr ⟨0, measure_ne_top _ _⟩
  simp only [nothing, measure_empty] at key
  convert! key

open scoped symmDiff

/--
theorem `abs_measureReal_sub_le_measureReal_symmDiff'` / 定理 `abs_measureReal_sub_le_measureReal_symmDiff'`

English:
theorem abs_measureReal_sub_le_measureReal_symmDiff'
  proof: by
  simp only [Measure.real]
  have hst : μ (s \ t) != ∞ := (measure_lt_top_of_subset sdiff_subset hs').ne
  have hts : μ (t \ s) != ∞ := (measure_lt_top_of_subset sdiff_subset ht').ne
  suffices (μ s).toReal - (μ t).toReal = (μ (s \ t)).toReal - (μ (t \ s)).toReal by
    rw [this]; rw [measure_sym

中文:
定理 abs_measure实数_sub_le_measure实数_symmDiff'
  证明: by
  simp only [Measure.real]
  have hst : μ (s \ t) != ∞ := (measure_lt_top_of_subset sdiff_subset hs').ne
  have hts : μ (t \ s) != ∞ := (measure_lt_top_of_subset sdiff_subset ht').ne
  suffices (μ s).toReal - (μ t).toReal = (μ (s \ t)).toReal - (μ (t \ s)).toReal by
    rw [this]; rw [measure_sym

Depends on / 依赖: ENNReal, ENNReal.toReal_add, ENNReal.toReal_sub_of_le, Measure, Measure.real, abs_sub, convert, measure_le, measure_lt_top_of_subset, measure_sdiff, measure_symmDiff_eq, sdiff_subset, toReal, toReal_add, toReal_sub_of_le
-/
theorem abs_measureReal_sub_le_measureReal_symmDiff'
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) (hs' : μ s != ∞) (ht' : μ t != ∞) :
    |μ.real s - μ.real t| <= μ.real (s ∆ t) := by
  simp only [Measure.real]
  have hst : μ (s \ t) != ∞ := (measure_lt_top_of_subset sdiff_subset hs').ne
  have hts : μ (t \ s) != ∞ := (measure_lt_top_of_subset sdiff_subset ht').ne
  suffices (μ s).toReal - (μ t).toReal = (μ (s \ t)).toReal - (μ (t \ s)).toReal by
    rw [this]; rw [measure_symmDiff_eq hs ht]; rw [ENNReal.toReal_add hst hts]
    convert! abs_sub (μ (s \ t)).toReal (μ (t \ s)).toReal <;> simp
  rw [measure_sdiff' s ht ht']; rw [measure_sdiff' t hs hs']; rw [ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness)]; rw [ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness)]; rw [union_comm t s]
  abel

/--
theorem `abs_measureReal_sub_le_measureReal_symmDiff` / 定理 `abs_measureReal_sub_le_measureReal_symmDiff`

English:
theorem abs_measureReal_sub_le_measureReal_symmDiff
  statement: [IsFiniteMeasure μ]
  proof: abs_measureReal_sub_le_measureReal_symmDiff' hs ht (by finiteness) (by finiteness)

中文:
定理 abs_measure实数_sub_le_measure实数_symmDiff
  结论: [是有限测度 μ]
  证明: abs_measureReal_sub_le_measureReal_symmDiff' hs ht (by finiteness) (by finiteness)

Depends on / 依赖: abs_measureReal_sub_le_measureReal_symmDiff, finiteness
-/
theorem abs_measureReal_sub_le_measureReal_symmDiff [IsFiniteMeasure μ]
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    |μ.real s - μ.real t| <= μ.real (s ∆ t) :=
  abs_measureReal_sub_le_measureReal_symmDiff' hs ht (by finiteness) (by finiteness)

instance {s : Finset ι} {μ : ι -> Measure α} [forall i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (∑ i in s, μ i) where measure_univ_lt_top := by simp [measure_lt_top]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] {μ
  body: by
    cases nonempty_fintype ι
    simp [measure_lt_top]

中文:
实例 [有限
  签名: ι] {μ
  定义体: by
    cases nonempty_fintype ι
    simp [measure_lt_top]

Depends on / 依赖: measure_lt_top, nonempty_fintype
-/
instance [Finite ι] {μ : ι -> Measure α} [forall i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (.sum μ) where
  measure_univ_lt_top := by
    cases nonempty_fintype ι
    simp [measure_lt_top]

end IsFiniteMeasure

/--
theorem `ite_ae_eq_of_measure_zero` / 定理 `ite_ae_eq_of_measure_zero`

English:
theorem ite_ae_eq_of_measure_zero
  statement: {γ} (f : α -> γ) (g : α -> γ) (s : Set α) [DecidablePred (· in s)]
  proof: by
  have h_ss : sᶜ subseteq { a : α | ite (a in s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine measure_mono_null ?_ hs_zero
  conv_rhs => rw [← compl_compl s]
  rwa [Set.compl_subset_compl]

中文:
定理 ite_ae_eq_of_measure_zero
  结论: {γ} (f : α -> γ) (g : α -> γ) (s : 集合 α) [DecidablePred (· in s)]
  证明: by
  have h_ss : sᶜ subseteq { a : α | ite (a in s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine measure_mono_null ?_ hs_zero
  conv_rhs => rw [← compl_compl s]
  rwa [Set.compl_subset_compl]

Depends on / 依赖: Set.compl_subset_compl, Set.mem_compl_iff, compl_compl, compl_subset_compl, conv_rhs, h_ss, hs_zero, measure_mono_null, mem_compl_iff, subseteq
-/
theorem ite_ae_eq_of_measure_zero {γ} (f : α -> γ) (g : α -> γ) (s : Set α) [DecidablePred (· in s)]
    (hs_zero : μ s = 0) :
    (fun x => ite (x in s) (f x) (g x)) =ᵐ[μ] g := by
  have h_ss : sᶜ subseteq { a : α | ite (a in s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine measure_mono_null ?_ hs_zero
  conv_rhs => rw [← compl_compl s]
  rwa [Set.compl_subset_compl]

/--
theorem `ite_ae_eq_of_measure_compl_zero` / 定理 `ite_ae_eq_of_measure_compl_zero`

English:
theorem ite_ae_eq_of_measure_compl_zero
  statement: {γ} (f : α -> γ) (g : α -> γ)
  proof: by
  rw [← mem_ae_iff] at hs_zero
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl

中文:
定理 ite_ae_eq_of_measure_compl_zero
  结论: {γ} (f : α -> γ) (g : α -> γ)
  证明: by
  rw [← mem_ae_iff] at hs_zero
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl

Depends on / 依赖: filter_upwards, hs_zero, intros, mem_ae_iff, split_ifs
-/
theorem ite_ae_eq_of_measure_compl_zero {γ} (f : α -> γ) (g : α -> γ)
    (s : Set α) [DecidablePred (· in s)] (hs_zero : μ sᶜ = 0) :
    (fun x => ite (x in s) (f x) (g x)) =ᵐ[μ] f := by
  rw [← mem_ae_iff] at hs_zero
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl

namespace Measure

/--
Definition of `FiniteAtFilter` / `FiniteAtFilter` 的定义

English:
definition FiniteAtFilter
  signature: {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α)
  body: exists s in f, μ s < ∞

中文:
定义 FiniteAtFilter
  签名: {_m0 : 可测空间 α} (μ : 测度 α) (f : 滤子 α)
  定义体: exists s in f, μ s < ∞
-/
def FiniteAtFilter {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : Prop :=
  exists s in f, μ s < ∞

/--
theorem `finiteAtFilter_of_finite` / 定理 `finiteAtFilter_of_finite`

English:
theorem finiteAtFilter_of_finite
  statement: {_m0 : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
  proof: ⟨univ, univ_mem, measure_lt_top μ univ⟩

中文:
定理 finiteAtFilter_of_finite
  结论: {_m0 : 可测空间 α} (μ : 测度 α) [是有限测度 μ]
  证明: ⟨univ, univ_mem, measure_lt_top μ univ⟩

Depends on / 依赖: measure_lt_top, univ_mem
-/
theorem finiteAtFilter_of_finite {_m0 : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : Filter α) : μ.FiniteAtFilter f :=
  ⟨univ, univ_mem, measure_lt_top μ univ⟩

/--
theorem `FiniteAtFilter.exists_mem_basis` / 定理 `FiniteAtFilter.exists_mem_basis`

English:
theorem FiniteAtFilter.exists_mem_basis
  statement: {f : Filter α} (hμ : FiniteAtFilter μ f) {p : ι -> Prop}
  proof: (hf.exists_iff fun {_s _t} hst ht => (measure_mono hst).trans_lt ht).1 hμ

中文:
定理 FiniteAtFilter.存在_mem_basis
  结论: {f : 滤子 α} (hμ : FiniteAtFilter μ f) {p : ι -> 命题}
  证明: (hf.exists_iff fun {_s _t} hst ht => (measure_mono hst).trans_lt ht).1 hμ

Depends on / 依赖: exists_iff, hf.exists_iff, measure_mono, trans_lt
-/
theorem FiniteAtFilter.exists_mem_basis {f : Filter α} (hμ : FiniteAtFilter μ f) {p : ι -> Prop}
    {s : ι -> Set α} (hf : f.HasBasis p s) : exists i, p i ∧ μ (s i) < ∞ :=
  (hf.exists_iff fun {_s _t} hst ht => (measure_mono hst).trans_lt ht).1 hμ

/--
theorem `finiteAtBot` / 定理 `finiteAtBot`

English:
theorem finiteAtBot
  given: {m0 : MeasurableSpace α} (μ : Measure α)
  statement: μ.FiniteAtFilter ⊥
  proof: ⟨∅, mem_bot, by simp only [measure_empty, zero_lt_top]⟩

中文:
定理 finiteAtBot
  条件: {m0 : 可测空间 α} (μ : 测度 α)
  结论: μ.FiniteAtFilter ⊥
  证明: ⟨∅, mem_bot, by simp only [measure_empty, zero_lt_top]⟩

Depends on / 依赖: measure_empty, mem_bot, zero_lt_top
-/
theorem finiteAtBot {m0 : MeasurableSpace α} (μ : Measure α) : μ.FiniteAtFilter ⊥ :=
  ⟨∅, mem_bot, by simp only [measure_empty, zero_lt_top]⟩

/--
Definition of `FiniteSpanningSetsIn` / `FiniteSpanningSetsIn` 的定义

English:
structure FiniteSpanningSetsIn
  parameters: {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α))
  axioms and operations (4):
    - set : Nat -> Set α
    - set_mem : forall i, set i in C
    - finite : forall i, μ (set i) < ∞
    - spanning : ⋃ i, set i = univ

中文:
结构 FiniteSpanningSetsIn
  参数: {m0 : 可测空间 α} (μ : 测度 α) (C : 集合 (集合 α))
  公理与运算 (4 个):
    - set : 自然数 -> 集合 α
    - set_mem : 对任意 i, set i in C
    - finite : 对任意 i, μ (set i) < ∞
    - spanning : ⋃ i, set i = univ
-/
structure FiniteSpanningSetsIn {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α)) where
  /-- The sequence of sets in `C` with finite measures -/
  protected set : Nat -> Set α
  protected set_mem : forall i, set i in C
  protected finite : forall i, μ (set i) < ∞
  protected spanning : ⋃ i, set i = univ

end Measure

/--
Definition of `IsLocallyFiniteMeasure` / `IsLocallyFiniteMeasure` 的定义

English:
class IsLocallyFiniteMeasure
  parameters: [TopologicalSpace α] (μ : Measure α)
  axioms and operations (1):
    - finiteAtNhds : forall x, μ.FiniteAtFilter (𝓝 x)

中文:
类 是局部有限测度
  参数: [拓扑空间 α] (μ : 测度 α)
  公理与运算 (1 个):
    - finiteAtNhds : 对任意 x, μ.FiniteAtFilter (𝓝 x)
-/
class IsLocallyFiniteMeasure [TopologicalSpace α] (μ : Measure α) : Prop where
  finiteAtNhds : forall x, μ.FiniteAtFilter (𝓝 x)

-- see Note [lower instance priority]
instance (priority := 100) IsFiniteMeasure.toIsLocallyFiniteMeasure [TopologicalSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun _ => finiteAtFilter_of_finite _ _⟩

/--
theorem `Measure.finiteAt_nhds` / 定理 `Measure.finiteAt_nhds`

English:
theorem Measure.finiteAt_nhds
  statement: [TopologicalSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
  proof: IsLocallyFiniteMeasure.finiteAtNhds x

中文:
定理 测度.finiteAt_nhds
  结论: [拓扑空间 α] (μ : 测度 α) [是局部有限测度 μ]
  证明: IsLocallyFiniteMeasure.finiteAtNhds x

Depends on / 依赖: IsLocallyFiniteMeasure, IsLocallyFiniteMeasure.finiteAtNhds, finiteAtNhds
-/
theorem Measure.finiteAt_nhds [TopologicalSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (x : α) : μ.FiniteAtFilter (𝓝 x) :=
  IsLocallyFiniteMeasure.finiteAtNhds x

/--
theorem `Measure.smul_finite` / 定理 `Measure.smul_finite`

English:
theorem Measure.smul_finite
  given: (μ : Measure α) [IsFiniteMeasure μ] {c : Real>=0∞} (hc : c != ∞)
  proof: by
  lift c to Real>=0 using hc
  exact MeasureTheory.isFiniteMeasureSMulNNReal

中文:
定理 测度.smul_finite
  条件: (μ : 测度 α) [是有限测度 μ] {c : 实数>=0∞} (hc : c != ∞)
  证明: by
  lift c to Real>=0 using hc
  exact MeasureTheory.isFiniteMeasureSMulNNReal

Depends on / 依赖: MeasureTheory, MeasureTheory.isFiniteMeasureSMulNNReal, isFiniteMeasureSMulNNReal
-/
theorem Measure.smul_finite (μ : Measure α) [IsFiniteMeasure μ] {c : Real>=0∞} (hc : c != ∞) :
    IsFiniteMeasure (c • μ) := by
  lift c to Real>=0 using hc
  exact MeasureTheory.isFiniteMeasureSMulNNReal

/--
theorem `Measure.exists_isOpen_measure_lt_top` / 定理 `Measure.exists_isOpen_measure_lt_top`

English:
theorem Measure.exists_isOpen_measure_lt_top
  statement: [TopologicalSpace α] (μ : Measure α)
  proof: by
  simpa only [and_assoc] using (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x)

中文:
定理 测度.存在_isOpen_measure_lt_top
  结论: [拓扑空间 α] (μ : 测度 α)
  证明: by
  simpa only [and_assoc] using (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x)

Depends on / 依赖: and_assoc, exists_mem_basis, finiteAt_nhds, nhds_basis_opens
-/
theorem Measure.exists_isOpen_measure_lt_top [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) : exists s : Set α, x in s ∧ IsOpen s ∧ μ s < ∞ := by
  simpa only [and_assoc] using (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x)

/--
Instance `isLocallyFiniteMeasureSMulNNReal` / 实例 `isLocallyFiniteMeasureSMulNNReal`

English:
instance isLocallyFiniteMeasureSMulNNReal
  signature: [TopologicalSpace α] (μ : Measure α)
  body: by
  refine ⟨fun x => ?_⟩
  rcases μ.exists_isOpen_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine ⟨o, o_open.mem_nhds xo, ?_⟩
  apply ENNReal.mul_lt_top _ μo
  simp

中文:
实例 isLocallyFiniteMeasureSMulNN实数
  签名: [拓扑空间 α] (μ : 测度 α)
  定义体: by
  refine ⟨fun x => ?_⟩
  rcases μ.exists_isOpen_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine ⟨o, o_open.mem_nhds xo, ?_⟩
  apply ENNReal.mul_lt_top _ μo
  simp

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, exists_isOpen_measure_lt_top, mem_nhds, mul_lt_top, o_open, o_open.mem_nhds
-/
instance isLocallyFiniteMeasureSMulNNReal [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (c : Real>=0) : IsLocallyFiniteMeasure (c • μ) := by
  refine ⟨fun x => ?_⟩
  rcases μ.exists_isOpen_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine ⟨o, o_open.mem_nhds xo, ?_⟩
  apply ENNReal.mul_lt_top _ μo
  simp

/--
theorem `Measure.isTopologicalBasis_isOpen_lt_top` / 定理 `Measure.isTopologicalBasis_isOpen_lt_top`

English:
theorem Measure.isTopologicalBasis_isOpen_lt_top
  statement: [TopologicalSpace α]
  proof: by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.1) ?_
  intro x s xs hs
  rcases μ.exists_isOpen_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine ⟨v inter s, ⟨hv.inter hs, lt_of_le_of_lt ?_ μv⟩, ⟨xv, xs⟩, inter_subset_right⟩
  exact measure_mono inter_subset_left

中文:
定理 测度.isTopologicalBasis_isOpen_lt_top
  结论: [拓扑空间 α]
  证明: by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.1) ?_
  intro x s xs hs
  rcases μ.exists_isOpen_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine ⟨v inter s, ⟨hv.inter hs, lt_of_le_of_lt ?_ μv⟩, ⟨xv, xs⟩, inter_subset_right⟩
  exact measure_mono inter_subset_left
-/
protected theorem Measure.isTopologicalBasis_isOpen_lt_top [TopologicalSpace α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    TopologicalSpace.IsTopologicalBasis { s | IsOpen s ∧ μ s < ∞ } := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.1) ?_
  intro x s xs hs
  rcases μ.exists_isOpen_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine ⟨v inter s, ⟨hv.inter hs, lt_of_le_of_lt ?_ μv⟩, ⟨xv, xs⟩, inter_subset_right⟩
  exact measure_mono inter_subset_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] (μ
  body: by
    obtain ⟨t, ht, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨t, ht, lt_of_le_of_lt (restrict_apply_le s t) hmus⟩

中文:
实例 [拓扑空间
  签名: α] (μ
  定义体: by
    obtain ⟨t, ht, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨t, ht, lt_of_le_of_lt (restrict_apply_le s t) hmus⟩

Depends on / 依赖: finiteAtNhds, lt_of_le_of_lt, restrict_apply_le
-/
instance [TopologicalSpace α] (μ : Measure α) [hμ : IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.restrict s) where
  finiteAtNhds x := by
    obtain ⟨t, ht, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨t, ht, lt_of_le_of_lt (restrict_apply_le s t) hmus⟩

/--
Definition of `IsFiniteMeasureOnCompacts` / `IsFiniteMeasureOnCompacts` 的定义

English:
class IsFiniteMeasureOnCompacts
  parameters: [TopologicalSpace α] (μ : Measure α)
  axioms and operations (1):
    - lt_top_of_isCompact : forall ⦃K : Set α⦄, IsCompact K -> μ K < ∞

中文:
类 紧集上有限测度
  参数: [拓扑空间 α] (μ : 测度 α)
  公理与运算 (1 个):
    - lt_top_of_isCompact : 对任意 ⦃K : 集合 α⦄, 是紧集 K -> μ K < ∞
-/
class IsFiniteMeasureOnCompacts [TopologicalSpace α] (μ : Measure α) : Prop where
  protected lt_top_of_isCompact : forall ⦃K : Set α⦄, IsCompact K -> μ K < ∞

/--
theorem `_root_.IsCompact.measure_lt_top` / 定理 `_root_.IsCompact.measure_lt_top`

English:
theorem _root_.IsCompact.measure_lt_top
  statement: [TopologicalSpace α] {μ : Measure α}
  proof: IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK

中文:
定理 _root_.是紧集.measure_lt_top
  结论: [拓扑空间 α] {μ : 测度 α}
  证明: IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK

Depends on / 依赖: IsFiniteMeasureOnCompacts, IsFiniteMeasureOnCompacts.lt_top_of_isCompact, lt_top_of_isCompact
-/
theorem _root_.IsCompact.measure_lt_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K < ∞ :=
  IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK

/--
theorem `_root_.IsCompact.measure_ne_top` / 定理 `_root_.IsCompact.measure_ne_top`

English:
theorem _root_.IsCompact.measure_ne_top
  statement: [TopologicalSpace α] {μ : Measure α}
  proof: hK.measure_lt_top.ne

中文:
定理 _root_.是紧集.measure_ne_top
  结论: [拓扑空间 α] {μ : 测度 α}
  证明: hK.measure_lt_top.ne

Depends on / 依赖: SupBotHom, hK.measure_lt_top.ne, measure_lt_top
-/
theorem _root_.IsCompact.measure_ne_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K != ∞ :=
  hK.measure_lt_top.ne

/--
theorem `_root_.Bornology.IsBounded.measure_lt_top` / 定理 `_root_.Bornology.IsBounded.measure_lt_top`

English:
theorem _root_.Bornology.IsBounded.measure_lt_top
  statement: [PseudoMetricSpace α] [ProperSpace α]
  proof: calc
    μ s <= μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.closure).measure_lt_top

中文:
定理 _root_.有界结构.IsBounded.measure_lt_top
  结论: [伪度量空间 α] [真空间 α]
  证明: calc
    μ s <= μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.closure).measure_lt_top

Depends on / 依赖: Metric, Metric.isCompact_of_isClosed_isBounded, closure, hs.closure, isClosed_closure, isCompact_of_isClosed_isBounded, measure_lt_top, measure_mono, subset_closure
-/
theorem _root_.Bornology.IsBounded.measure_lt_top [PseudoMetricSpace α] [ProperSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] ⦃s : Set α⦄ (hs : Bornology.IsBounded s) :
    μ s < ∞ :=
  calc
    μ s <= μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.closure).measure_lt_top

/--
theorem `measure_closedBall_lt_top` / 定理 `measure_closedBall_lt_top`

English:
theorem measure_closedBall_lt_top
  statement: [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
  proof: Metric.isBounded_closedBall.measure_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 measure_closedBall_lt_top
  结论: [伪度量空间 α] [真空间 α] {μ : 测度 α}
  证明: Metric.isBounded_closedBall.measure_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: InfTopHom, Metric, Metric.isBounded_closedBall.measure_lt_top, isBounded_closedBall, measure_lt_top
-/
theorem measure_closedBall_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.closedBall x r) < ∞ :=
  Metric.isBounded_closedBall.measure_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `measure_ball_ne_top` / 定理 `measure_ball_ne_top`

English:
theorem measure_ball_ne_top
  statement: [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
  proof: Metric.isBounded_ball.measure_lt_top.ne

中文:
定理 measure_ball_ne_top
  结论: [伪度量空间 α] [真空间 α] {μ : 测度 α}
  证明: Metric.isBounded_ball.measure_lt_top.ne

Depends on / 依赖: Metric, Metric.isBounded_ball.measure_lt_top.ne, isBounded_ball, measure_lt_top
-/
theorem measure_ball_ne_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.ball x r) != ∞ :=
  Metric.isBounded_ball.measure_lt_top.ne

/--
theorem `measure_ball_lt_top` / 定理 `measure_ball_lt_top`

English:
theorem measure_ball_lt_top
  statement: [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
  proof: by finiteness

中文:
定理 measure_ball_lt_top
  结论: [伪度量空间 α] [真空间 α] {μ : 测度 α}
  证明: by finiteness

Depends on / 依赖: finiteness
-/
theorem measure_ball_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : Real} : μ (Metric.ball x r) < ∞ := by finiteness

/--
theorem `IsFiniteMeasureOnCompacts.smul` / 定理 `IsFiniteMeasureOnCompacts.smul`

English:
theorem IsFiniteMeasureOnCompacts.smul
  statement: [TopologicalSpace α] (μ : Measure α)
  proof: ⟨fun _K hK => ENNReal.mul_lt_top hc.lt_top hK.measure_lt_top⟩

中文:
定理 紧集上有限测度.smul
  结论: [拓扑空间 α] (μ : 测度 α)
  证明: ⟨fun _K hK => ENNReal.mul_lt_top hc.lt_top hK.measure_lt_top⟩
-/
protected theorem IsFiniteMeasureOnCompacts.smul [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] {c : Real>=0∞} (hc : c != ∞) : IsFiniteMeasureOnCompacts (c • μ) :=
  ⟨fun _K hK => ENNReal.mul_lt_top hc.lt_top hK.measure_lt_top⟩

/--
Instance `IsFiniteMeasureOnCompacts.smul_nnreal` / 实例 `IsFiniteMeasureOnCompacts.smul_nnreal`

English:
instance IsFiniteMeasureOnCompacts.smul_nnreal
  signature: [TopologicalSpace α] (μ : Measure α)
  body: IsFiniteMeasureOnCompacts.smul μ coe_ne_top

中文:
实例 紧集上有限测度.smul_nnreal
  签名: [拓扑空间 α] (μ : 测度 α)
  定义体: IsFiniteMeasureOnCompacts.smul μ coe_ne_top

Depends on / 依赖: IsFiniteMeasureOnCompacts, IsFiniteMeasureOnCompacts.smul, coe_ne_top
-/
instance IsFiniteMeasureOnCompacts.smul_nnreal [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] (c : Real>=0) : IsFiniteMeasureOnCompacts (c • μ) :=
  IsFiniteMeasureOnCompacts.smul μ coe_ne_top

/--
Instance `instIsFiniteMeasureOnCompactsRestrict` / 实例 `instIsFiniteMeasureOnCompactsRestrict`

English:
instance instIsFiniteMeasureOnCompactsRestrict
  signature: [TopologicalSpace α] {μ : Measure α}
  body: ⟨fun _k hk => (restrict_apply_le _ _).trans_lt hk.measure_lt_top⟩

中文:
实例 instIsFiniteMeasureOnCompactsRestrict
  签名: [拓扑空间 α] {μ : 测度 α}
  定义体: ⟨fun _k hk => (restrict_apply_le _ _).trans_lt hk.measure_lt_top⟩

Depends on / 依赖: hk.measure_lt_top, measure_lt_top, restrict_apply_le, trans_lt
-/
instance instIsFiniteMeasureOnCompactsRestrict [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {s : Set α} : IsFiniteMeasureOnCompacts (μ.restrict s) :=
  ⟨fun _k hk => (restrict_apply_le _ _).trans_lt hk.measure_lt_top⟩

variable {mβ} in
/--
theorem `IsFiniteMeasureOnCompacts.comap'` / 定理 `IsFiniteMeasureOnCompacts.comap'`

English:
theorem IsFiniteMeasureOnCompacts.comap'
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
    rw [f_me.comap_apply]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image f_cont)

中文:
定理 紧集上有限测度.comap'
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
    rw [f_me.comap_apply]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image f_cont)
-/
protected theorem IsFiniteMeasureOnCompacts.comap' [TopologicalSpace α] [TopologicalSpace β]
    (μ : Measure β) [IsFiniteMeasureOnCompacts μ] {f : α -> β} (f_cont : Continuous f)
    (f_me : MeasurableEmbedding f) : IsFiniteMeasureOnCompacts (μ.comap f) where
  lt_top_of_isCompact K hK := by
    rw [f_me.comap_apply]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image f_cont)

instance (priority := 100) CompactSpace.isFiniteMeasure [TopologicalSpace α] [CompactSpace α]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasure μ :=
  ⟨IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ⟩

/-- A measure which is finite on compact sets in a locally compact space is locally finite. -/
instance (priority := 100) isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [WeaklyLocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨K, K_compact, K_mem⟩ := exists_compact_mem_nhds x
    ⟨K, K_mem, K_compact.measure_lt_top⟩⟩

/--
theorem `exists_pos_measure_of_cover` / 定理 `exists_pos_measure_of_cover`

English:
theorem exists_pos_measure_of_cover
  statement: [Countable ι] {U : ι -> Set α} (hU : ⋃ i, U i = univ)
  proof: by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero]; rw [← hU]
  exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (H i)

中文:
定理 存在_pos_measure_of_cover
  结论: [可数 ι] {U : ι -> 集合 α} (hU : ⋃ i, U i = univ)
  证明: by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero]; rw [← hU]
  exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (H i)

Depends on / 依赖: contrapose, measure_iUnion_null, measure_univ_eq_zero, nonpos_iff_eq_zero
-/
theorem exists_pos_measure_of_cover [Countable ι] {U : ι -> Set α} (hU : ⋃ i, U i = univ)
    (hμ : μ != 0) : exists i, 0 < μ (U i) := by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero]; rw [← hU]
  exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (H i)

/--
theorem `exists_pos_preimage_ball` / 定理 `exists_pos_preimage_ball`

English:
theorem exists_pos_preimage_ball
  given: [PseudoMetricSpace δ] (f : α -> δ) (x : δ) (hμ : μ != 0)
  proof: exists_pos_measure_of_cover (by rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]) hμ

中文:
定理 存在_pos_preimage_ball
  条件: [伪度量空间 δ] (f : α -> δ) (x : δ) (hμ : μ != 0)
  证明: exists_pos_measure_of_cover (by rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]) hμ

Depends on / 依赖: LinearOrder, LinearOrder.toCircularOrder, Metric, Metric.iUnion_ball_nat, exists_pos_measure_of_cover, iUnion_ball_nat, preimage_iUnion, preimage_univ, toCircularOrder
-/
theorem exists_pos_preimage_ball [PseudoMetricSpace δ] (f : α -> δ) (x : δ) (hμ : μ != 0) :
    exists n : Nat, 0 < μ (f ⁻¹' Metric.ball x n) :=
  exists_pos_measure_of_cover (by rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]) hμ

/--
theorem `exists_pos_ball` / 定理 `exists_pos_ball`

English:
theorem exists_pos_ball
  given: [PseudoMetricSpace α] (x : α) (hμ : μ != 0)
  proof: exists_pos_preimage_ball id x hμ

中文:
定理 存在_pos_ball
  条件: [伪度量空间 α] (x : α) (hμ : μ != 0)
  证明: exists_pos_preimage_ball id x hμ

Depends on / 依赖: exists_pos_preimage_ball
-/
theorem exists_pos_ball [PseudoMetricSpace α] (x : α) (hμ : μ != 0) :
    exists n : Nat, 0 < μ (Metric.ball x n) :=
  exists_pos_preimage_ball id x hμ

/--
theorem `exists_ne_forall_mem_nhds_pos_measure_preimage` / 定理 `exists_ne_forall_mem_nhds_pos_measure_preimage`

English:
theorem exists_ne_forall_mem_nhds_pos_measure_preimage
  statement: {β} [TopologicalSpace β] [T1Space β]
  proof: by
  -- We use an `OuterMeasure` so that the proof works without `Measurable f`
  set m : OuterMeasure β := OuterMeasure.map f μ.toOuterMeasure
  replace h : forall b : β, m {b}ᶜ != 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ != 0 := ne_bot_of_le_ne_bot (h default) (measure_mo

中文:
定理 存在_ne_对任意_mem_nhds_pos_measure_preimage
  结论: {β} [拓扑空间 β] [T1空间 β]
  证明: by
  -- We use an `OuterMeasure` so that the proof works without `Measurable f`
  set m : OuterMeasure β := OuterMeasure.map f μ.toOuterMeasure
  replace h : forall b : β, m {b}ᶜ != 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ != 0 := ne_bot_of_le_ne_bot (h default) (measure_mo
-/
theorem exists_ne_forall_mem_nhds_pos_measure_preimage {β} [TopologicalSpace β] [T1Space β]
    [SecondCountableTopology β] [Nonempty β] {f : α -> β} (h : forall b, existsᵐ x ∂μ, f x != b) :
    exists a b : β, a != b ∧ (forall s in 𝓝 a, 0 < μ (f ⁻¹' s)) ∧ forall t in 𝓝 b, 0 < μ (f ⁻¹' t) := by
  -- We use an `OuterMeasure` so that the proof works without `Measurable f`
  set m : OuterMeasure β := OuterMeasure.map f μ.toOuterMeasure
  replace h : forall b : β, m {b}ᶜ != 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ != 0 := ne_bot_of_le_ne_bot (h default) (measure_mono <| subset_univ _)
  rcases exists_mem_forall_mem_nhdsWithin_pos_measure this with ⟨b, -, hb⟩
  simp only [nhdsWithin_univ] at hb
  rcases exists_mem_forall_mem_nhdsWithin_pos_measure (h b) with ⟨a, hab : a != b, ha⟩
  simp only [isOpen_compl_singleton.nhdsWithin_eq hab] at ha
  exact ⟨a, b, hab, ha, hb⟩

/--
theorem `ext_on_measurableSpace_of_generate_finite` / 定理 `ext_on_measurableSpace_of_generate_finite`

English:
theorem ext_on_measurableSpace_of_generate_finite
  statement: {α} (m₀ : MeasurableSpace α) {μ ν : Measure α}
  proof: by
  have : IsFiniteMeasure ν := by
    constructor
    rw [← h_univ]
    apply IsFiniteMeasure.measure_univ_lt_top
  induction s, hs using induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    rw [measure_compl (h t htm) (by finiteness)]; rw [me

中文:
定理 ext_on_measurableSpace_of_generate_finite
  结论: {α} (m₀ : 可测空间 α) {μ ν : 测度 α}
  证明: by
  have : IsFiniteMeasure ν := by
    constructor
    rw [← h_univ]
    apply IsFiniteMeasure.measure_univ_lt_top
  induction s, hs using induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    rw [measure_compl (h t htm) (by finiteness)]; rw [me

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.measure_univ_lt_top, finiteness, h_univ, iUnion, induction_on_inter, measure_compl, measure_iUnion, measure_univ_lt_top
-/
theorem ext_on_measurableSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ ν : Measure α}
    [IsFiniteMeasure μ] (C : Set (Set α)) (hμν : forall s in C, μ s = ν s) {m : MeasurableSpace α}
    (h : m <= m₀) (hA : m = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) {s : Set α} (hs : MeasurableSet[m] s) : μ s = ν s := by
  have : IsFiniteMeasure ν := by
    constructor
    rw [← h_univ]
    apply IsFiniteMeasure.measure_univ_lt_top
  induction s, hs using induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    rw [measure_compl (h t htm) (by finiteness)]; rw [measure_compl (h t htm) (by finiteness)]; rw [iht]; rw [h_univ]
  | iUnion f hfd hfm ihf =>
    simp [measure_iUnion, hfd, h _ (hfm _), ihf]

/--
theorem `ext_of_generate_finite` / 定理 `ext_of_generate_finite`

English:
theorem ext_of_generate_finite
  statement: (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
  proof: Measure.ext fun _s hs =>
    ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs

中文:
定理 ext_of_generate_finite
  结论: (C : 集合 (集合 α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
  证明: Measure.ext fun _s hs =>
    ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs

Depends on / 依赖: Measure, Measure.ext, ext_on_measurableSpace_of_generate_finite, h_univ, le_rfl
-/
theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
    [IsFiniteMeasure μ] (hμν : forall s in C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν :=
  Measure.ext fun _s hs =>
    ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs

namespace Measure

namespace FiniteAtFilter

variable {f g : Filter α}

/--
theorem `filter_mono` / 定理 `filter_mono`

English:
theorem filter_mono
  given: (h : f <= g)
  statement: μ.FiniteAtFilter g -> μ.FiniteAtFilter f
  proof: fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩

中文:
定理 filter_mono
  条件: (h : f <= g)
  结论: μ.FiniteAtFilter g -> μ.FiniteAtFilter f
  证明: fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩
-/
theorem filter_mono (h : f <= g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f := fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩

/--
theorem `inf_of_left` / 定理 `inf_of_left`

English:
theorem inf_of_left
  given: (h : μ.FiniteAtFilter f)
  statement: μ.FiniteAtFilter (f ⊓ g)
  proof: h.filter_mono inf_le_left

中文:
定理 inf_of_left
  条件: (h : μ.FiniteAtFilter f)
  结论: μ.FiniteAtFilter (f ⊓ g)
  证明: h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left
-/
theorem inf_of_left (h : μ.FiniteAtFilter f) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_left

/--
theorem `inf_of_right` / 定理 `inf_of_right`

English:
theorem inf_of_right
  given: (h : μ.FiniteAtFilter g)
  statement: μ.FiniteAtFilter (f ⊓ g)
  proof: h.filter_mono inf_le_right

@[simp]

中文:
定理 inf_of_right
  条件: (h : μ.FiniteAtFilter g)
  结论: μ.FiniteAtFilter (f ⊓ g)
  证明: h.filter_mono inf_le_right

@[simp]

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_right
-/
theorem inf_of_right (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_right

@[simp]
/--
theorem `inf_ae_iff` / 定理 `inf_ae_iff`

English:
theorem inf_ae_iff
  statement: μ.FiniteAtFilter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f
  proof: by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices μ t <= μ (t inter u) from ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)

alias ⟨of_inf_ae, _⟩ := inf_ae_iff

中文:
定理 inf_ae_iff
  结论: μ.FiniteAtFilter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f
  证明: by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices μ t <= μ (t inter u) from ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)

alias ⟨of_inf_ae, _⟩ := inf_ae_iff

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, measure_mono_ae, mem_of_superset, this.trans_lt, trans_lt
-/
theorem inf_ae_iff : μ.FiniteAtFilter (f ⊓ ae μ) ↔ μ.FiniteAtFilter f := by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices μ t <= μ (t inter u) from ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)

alias ⟨of_inf_ae, _⟩ := inf_ae_iff

/--
theorem `filter_mono_ae` / 定理 `filter_mono_ae`

English:
theorem filter_mono_ae
  given: (h : f ⊓ (ae μ) <= g) (hg : μ.FiniteAtFilter g)
  statement: μ.FiniteAtFilter f
  proof: inf_ae_iff.1 (hg.filter_mono h)

中文:
定理 filter_mono_ae
  条件: (h : f ⊓ (ae μ) <= g) (hg : μ.FiniteAtFilter g)
  结论: μ.FiniteAtFilter f
  证明: inf_ae_iff.1 (hg.filter_mono h)

Depends on / 依赖: filter_mono, hg.filter_mono, inf_ae_iff
-/
theorem filter_mono_ae (h : f ⊓ (ae μ) <= g) (hg : μ.FiniteAtFilter g) : μ.FiniteAtFilter f :=
  inf_ae_iff.1 (hg.filter_mono h)

/--
theorem `measure_mono` / 定理 `measure_mono`

English:
theorem measure_mono
  given: (h : μ <= ν)
  statement: ν.FiniteAtFilter f -> μ.FiniteAtFilter f
  proof: fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩

@[gcongr, mono]

中文:
定理 measure_mono
  条件: (h : μ <= ν)
  结论: ν.FiniteAtFilter f -> μ.FiniteAtFilter f
  证明: fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩

@[gcongr, mono]
-/
protected theorem measure_mono (h : μ <= ν) : ν.FiniteAtFilter f -> μ.FiniteAtFilter f :=
  fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩

@[gcongr, mono]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : f <= g) (hμ : μ <= ν)
  statement: ν.FiniteAtFilter g -> μ.FiniteAtFilter f
  proof: fun h => (h.filter_mono hf).measure_mono hμ

中文:
定理 mono
  条件: (hf : f <= g) (hμ : μ <= ν)
  结论: ν.FiniteAtFilter g -> μ.FiniteAtFilter f
  证明: fun h => (h.filter_mono hf).measure_mono hμ
-/
protected theorem mono (hf : f <= g) (hμ : μ <= ν) : ν.FiniteAtFilter g -> μ.FiniteAtFilter f :=
  fun h => (h.filter_mono hf).measure_mono hμ

/--
theorem `eventually` / 定理 `eventually`

English:
theorem eventually
  given: (h : μ.FiniteAtFilter f)
  statement: forallᶠ s in f.smallSets, μ s < ∞
  proof: (eventually_smallSets' fun _s _t hst ht => (measure_mono hst).trans_lt ht).2 h

中文:
定理 eventually
  条件: (h : μ.FiniteAtFilter f)
  结论: 对任意ᶠ s in f.smallSets, μ s < ∞
  证明: (eventually_smallSets' fun _s _t hst ht => (measure_mono hst).trans_lt ht).2 h
-/
protected theorem eventually (h : μ.FiniteAtFilter f) : forallᶠ s in f.smallSets, μ s < ∞ :=
  (eventually_smallSets' fun _s _t hst ht => (measure_mono hst).trans_lt ht).2 h

/--
theorem `filterSup` / 定理 `filterSup`

English:
theorem filterSup
  statement: μ.FiniteAtFilter f -> μ.FiniteAtFilter g -> μ.FiniteAtFilter (f ⊔ g)
  proof: fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s union t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

中文:
定理 filterSup
  结论: μ.FiniteAtFilter f -> μ.FiniteAtFilter g -> μ.FiniteAtFilter (f ⊔ g)
  证明: fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s union t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, add_lt_top, measure_union_le, trans_lt, union_mem_sup
-/
theorem filterSup : μ.FiniteAtFilter f -> μ.FiniteAtFilter g -> μ.FiniteAtFilter (f ⊔ g) :=
  fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s union t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

end FiniteAtFilter

/--
theorem `finiteAt_nhdsWithin` / 定理 `finiteAt_nhdsWithin`

English:
theorem finiteAt_nhdsWithin
  statement: [TopologicalSpace α] {_m0 : MeasurableSpace α} (μ : Measure α)
  proof: (finiteAt_nhds μ x).inf_of_left

@[simp]

中文:
定理 finiteAt_nhdsWithin
  结论: [拓扑空间 α] {_m0 : 可测空间 α} (μ : 测度 α)
  证明: (finiteAt_nhds μ x).inf_of_left

@[simp]

Depends on / 依赖: finiteAt_nhds, inf_of_left
-/
theorem finiteAt_nhdsWithin [TopologicalSpace α] {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) (s : Set α) : μ.FiniteAtFilter (𝓝[s] x) :=
  (finiteAt_nhds μ x).inf_of_left

@[simp]
/--
theorem `finiteAt_principal` / 定理 `finiteAt_principal`

English:
theorem finiteAt_principal
  statement: μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞
  proof: ⟨fun ⟨_t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩

中文:
定理 finiteAt_principal
  结论: μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞
  证明: ⟨fun ⟨_t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩

Depends on / 依赖: measure_mono, mem_principal_self, trans_lt
-/
theorem finiteAt_principal : μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞ :=
  ⟨fun ⟨_t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩

/--
theorem `isLocallyFiniteMeasure_of_le` / 定理 `isLocallyFiniteMeasure_of_le`

English:
theorem isLocallyFiniteMeasure_of_le
  statement: [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α}
  proof: let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩

中文:
定理 isLocallyFiniteMeasure_of_le
  结论: [拓扑空间 α] {_m : 可测空间 α} {μ ν : 测度 α}
  证明: let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩

Depends on / 依赖: H.finiteAtNhds, finiteAtNhds, measure_mono
-/
theorem isLocallyFiniteMeasure_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α}
    [H : IsLocallyFiniteMeasure μ] (h : ν <= μ) : IsLocallyFiniteMeasure ν :=
  let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩

end Measure

end MeasureTheory

namespace IsCompact

variable [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} {s : Set α}

/--
theorem `exists_open_superset_measure_lt_top'` / 定理 `exists_open_superset_measure_lt_top'`

English:
theorem exists_open_superset_measure_lt_top'
  statement: (h : IsCompact s)
  proof: by
  refine IsCompact.induction_on h ?_ ?_ ?_ ?_
  · use ∅
    simp
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine
      ⟨U union V, union_subset_union hsU htV, hUo.union hVo,
(measure_union_le _ _).trans_lt EN

中文:
定理 存在_open_superset_measure_lt_top'
  结论: (h : 是紧集 s)
  证明: by
  refine IsCompact.induction_on h ?_ ?_ ?_ ?_
  · use ∅
    simp
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine
      ⟨U union V, union_subset_union hsU htV, hUo.union hVo,
(measure_union_le _ _).trans_lt EN

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, IsCompact, IsCompact.induction_on, Subset, Subset.rfl, add_lt_top, exists_mem_basis, hUo.mem_nhds, hUo.union, hst.trans, induction_on, measure_union_le, mem_nhds, nhdsWithin_le_nhds, nhds_basis_opens, trans_lt, union_subset_union
-/
theorem exists_open_superset_measure_lt_top' (h : IsCompact s)
    (hμ : forall x in s, μ.FiniteAtFilter (𝓝 x)) : exists U ⊇ s, IsOpen U ∧ μ U < ∞ := by
  refine IsCompact.induction_on h ?_ ?_ ?_ ?_
  · use ∅
    simp
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine
      ⟨U union V, union_subset_union hsU htV, hUo.union hVo,
(measure_union_le _ _).trans_lt ENNReal.add_lt_top.2 ⟨hU, hV⟩⟩
  · intro x hx
    rcases (hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩
    exact ⟨U, nhdsWithin_le_nhds (hUo.mem_nhds hx), U, Subset.rfl, hUo, hU⟩

/--
theorem `exists_open_superset_measure_lt_top` / 定理 `exists_open_superset_measure_lt_top`

English:
theorem exists_open_superset_measure_lt_top
  statement: (h : IsCompact s) (μ : Measure α)
  proof: h.exists_open_superset_measure_lt_top' fun x _ => μ.finiteAt_nhds x

中文:
定理 存在_open_superset_measure_lt_top
  结论: (h : 是紧集 s) (μ : 测度 α)
  证明: h.exists_open_superset_measure_lt_top' fun x _ => μ.finiteAt_nhds x

Depends on / 依赖: exists_open_superset_measure_lt_top, finiteAt_nhds, h.exists_open_superset_measure_lt_top
-/
theorem exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measure α)
    [IsLocallyFiniteMeasure μ] : exists U ⊇ s, IsOpen U ∧ μ U < ∞ :=
  h.exists_open_superset_measure_lt_top' fun x _ => μ.finiteAt_nhds x

/--
theorem `measure_lt_top_of_nhdsWithin` / 定理 `measure_lt_top_of_nhdsWithin`

English:
theorem measure_lt_top_of_nhdsWithin
  given: (h : IsCompact s) (hμ : forall x in s, μ.FiniteAtFilter (𝓝[s] x))
  proof: IsCompact.induction_on h (by simp) (fun _ _ hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ

中文:
定理 measure_lt_top_of_nhdsWithin
  条件: (h : 是紧集 s) (hμ : 对任意 x in s, μ.FiniteAtFilter (𝓝[s] x))
  证明: IsCompact.induction_on h (by simp) (fun _ _ hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, IsCompact, IsCompact.induction_on, add_lt_top, induction_on, measure_mono, measure_union_le, trans_lt
-/
theorem measure_lt_top_of_nhdsWithin (h : IsCompact s) (hμ : forall x in s, μ.FiniteAtFilter (𝓝[s] x)) :
    μ s < ∞ :=
  IsCompact.induction_on h (by simp) (fun _ _ hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ

/--
theorem `measure_zero_of_nhdsWithin` / 定理 `measure_zero_of_nhdsWithin`

English:
theorem measure_zero_of_nhdsWithin
  given: (hs : IsCompact s)
  proof: by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhdsWithin

中文:
定理 measure_zero_of_nhdsWithin
  条件: (hs : 是紧集 s)
  证明: by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhdsWithin

Depends on / 依赖: compl_mem_ae_iff, compl_mem_sets_of_nhdsWithin, hs.compl_mem_sets_of_nhdsWithin
-/
theorem measure_zero_of_nhdsWithin (hs : IsCompact s) :
    (forall a in s, exists t in 𝓝[s] a, μ t = 0) -> μ s = 0 := by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhdsWithin

end IsCompact

-- see Note [lower instance priority]
instance (priority := 100) isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure [TopologicalSpace α]
    {_ : MeasurableSpace α} {μ : Measure α} [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun _s hs => hs.measure_lt_top_of_nhdsWithin fun _ _ => μ.finiteAt_nhdsWithin _ _⟩

/--
theorem `isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace` / 定理 `isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace`

English:
theorem isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace
  statement: [TopologicalSpace α]
  proof: by
  constructor <;> intros
  · infer_instance
  · exact CompactSpace.isFiniteMeasure

中文:
定理 isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace
  结论: [拓扑空间 α]
  证明: by
  constructor <;> intros
  · infer_instance
  · exact CompactSpace.isFiniteMeasure

Depends on / 依赖: CompactSpace, CompactSpace.isFiniteMeasure, infer_instance, intros, isFiniteMeasure
-/
theorem isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [CompactSpace α] :
    IsFiniteMeasure μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor <;> intros
  · infer_instance
  · exact CompactSpace.isFiniteMeasure

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `MeasureTheory.Measure.finiteSpanningSetsInCompact` / `MeasureTheory.Measure.finiteSpanningSetsInCompact` 的定义

English:
definition MeasureTheory.Measure.finiteSpanningSetsInCompact
  body: compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α

中文:
定义 测度论.测度.finiteSpanningSetsInCompact
  定义体: compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α

Depends on / 依赖: compactCovering
-/
noncomputable def MeasureTheory.Measure.finiteSpanningSetsInCompact
    [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsCompact K } where
  set := compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `MeasureTheory.Measure.finiteSpanningSetsInOpen` / `MeasureTheory.Measure.finiteSpanningSetsInOpen` 的定义

English:
definition MeasureTheory.Measure.finiteSpanningSetsInOpen
  body: ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanni

中文:
定义 测度论.测度.finiteSpanningSetsInOpen
  定义体: ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanni

Depends on / 依赖: exists_open_superset_measure_lt_top, isCompact_compactCovering
-/
noncomputable def MeasureTheory.Measure.finiteSpanningSetsInOpen
    [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsOpen K } where
  set n := ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanning :=
    eq_univ_of_subset
      (iUnion_mono fun n =>
        ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.1)
      (iUnion_compactCovering α)

open TopologicalSpace

/-- A locally finite measure on a second countable topological space admits a finite spanning
sequence of open sets. -/
noncomputable irreducible_def MeasureTheory.Measure.finiteSpanningSetsInOpen' [TopologicalSpace α]
  [SecondCountableTopology α] {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
  μ.FiniteSpanningSetsIn { K | IsOpen K } := by
  suffices H : Nonempty (μ.FiniteSpanningSetsIn { K | IsOpen K }) from H.some
  cases isEmpty_or_nonempty α
  · exact
      ⟨{ set := fun _ => ∅
          set_mem := fun _ => by simp
          finite := fun _ => by simp
          spanning := by simp [eq_iff_true_of_subsingleton] }⟩
  inhabit α
  let S : Set (Set α) := { s | IsOpen s ∧ μ s < ∞ }
  obtain ⟨T, T_count, TS, hT⟩ : exists T : Set (Set α), T.Countable ∧ T subseteq S ∧ ⋃₀ T = ⋃₀ S :=
    isOpen_sUnion_countable S fun s hs => hs.1
  rw [μ.isTopologicalBasis_isOpen_lt_top.sUnion_eq] at hT
  have T_ne : T.Nonempty := by
    by_contra h'T
    rw [not_nonempty_iff_eq_empty.1 h'T]; rw [sUnion_empty] at hT
    simpa only [← hT] using! mem_univ (default : α)
  obtain ⟨f, hf⟩ : exists f : Nat -> Set α, T = range f := T_count.exists_eq_range T_ne
  have fS : forall n, f n in S := by
    intro n
    apply TS
    rw [hf]
    exact mem_range_self n
  refine
    ⟨{ set := f
        set_mem := fun n => (fS n).1
        finite := fun n => (fS n).2
        spanning := ?_ }⟩
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t, tT, xt⟩ : exists t : Set α, t in range f ∧ x in t := by
    have : x in ⋃₀ T := by simp only [hT, mem_univ]
    simpa only [mem_sUnion, exists_prop, ← hf]
  obtain ⟨n, rfl⟩ : exists n : Nat, f n = t := by simpa only using! tT
  exact mem_iUnion_of_mem _ xt

section MeasureIxx

variable [Preorder α] [TopologicalSpace α] [CompactIccSpace α] {m : MeasurableSpace α}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {a b : α}

/--
theorem `measure_Icc_lt_top` / 定理 `measure_Icc_lt_top`

English:
theorem measure_Icc_lt_top
  statement: μ (Icc a b) < ∞
  proof: isCompact_Icc.measure_lt_top

中文:
定理 measure_Icc_lt_top
  结论: μ (闭区间 a b) < ∞
  证明: isCompact_Icc.measure_lt_top

Depends on / 依赖: isCompact_Icc, isCompact_Icc.measure_lt_top, measure_lt_top
-/
theorem measure_Icc_lt_top : μ (Icc a b) < ∞ :=
  isCompact_Icc.measure_lt_top

/--
theorem `measure_Ico_lt_top` / 定理 `measure_Ico_lt_top`

English:
theorem measure_Ico_lt_top
  statement: μ (Ico a b) < ∞
  proof: (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top

中文:
定理 measure_Ico_lt_top
  结论: μ (左闭右开区间 a b) < ∞
  证明: (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top

Depends on / 依赖: Ico_subset_Icc_self, measure_Icc_lt_top, measure_mono, trans_lt
-/
theorem measure_Ico_lt_top : μ (Ico a b) < ∞ :=
  (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top

/--
theorem `measure_Ioc_lt_top` / 定理 `measure_Ioc_lt_top`

English:
theorem measure_Ioc_lt_top
  statement: μ (Ioc a b) < ∞
  proof: (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top

中文:
定理 measure_Ioc_lt_top
  结论: μ (左开右闭区间 a b) < ∞
  证明: (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top

Depends on / 依赖: Ioc_subset_Icc_self, measure_Icc_lt_top, measure_mono, trans_lt
-/
theorem measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
  (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top

/--
theorem `measure_Ioo_lt_top` / 定理 `measure_Ioo_lt_top`

English:
theorem measure_Ioo_lt_top
  statement: μ (Ioo a b) < ∞
  proof: (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

中文:
定理 measure_Ioo_lt_top
  结论: μ (开区间 a b) < ∞
  证明: (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

Depends on / 依赖: Ioo_subset_Icc_self, measure_Icc_lt_top, measure_mono, trans_lt
-/
theorem measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
  (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

end MeasureIxx
