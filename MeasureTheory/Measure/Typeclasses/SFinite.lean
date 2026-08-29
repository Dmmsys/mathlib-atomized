/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Classes for s-finite measures

We introduce the following typeclasses for measures:

* `SFinite μ`: the measure `μ` can be written as a countable sum of finite measures;
* `SigmaFinite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite.
-/

@[expose] public section

namespace MeasureTheory

open Set Filter Function Measure MeasurableSpace NNReal ENNReal
open scoped Topology

variable {α β ι : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν : Measure α}
  {s t : Set α} {a : α}

section SFinite

/--
Definition of `SFinite` / `SFinite` 的定义

English:
class SFinite
  parameters: (μ : Measure α)
  axioms and operations (1):
    - out' : exists m : Nat -> Measure α, (forall n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

中文:
类 SFinite
  参数: (μ : 测度 α)
  公理与运算 (1 个):
    - out' : 存在 m : 自然数 -> 测度 α, (对任意 n, 是有限测度 (m n)) ∧ μ = 测度.求和 m
-/
class SFinite (μ : Measure α) : Prop where
  out' : exists m : Nat -> Measure α, (forall n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

/--
Definition of `sfiniteSeq` / `sfiniteSeq` 的定义

English:
definition sfiniteSeq
  signature: (μ : Measure α) [h : SFinite μ]
  body: h.1.choose

中文:
定义 sfiniteSeq
  签名: (μ : 测度 α) [h : SFinite μ]
  定义体: h.1.choose
-/
noncomputable def sfiniteSeq (μ : Measure α) [h : SFinite μ] : Nat -> Measure α := h.1.choose

/--
Instance `isFiniteMeasure_sfiniteSeq` / 实例 `isFiniteMeasure_sfiniteSeq`

English:
instance isFiniteMeasure_sfiniteSeq
  signature: [h : SFinite μ] (n : Nat)
  body: h.1.choose_spec.1 n

中文:
实例 isFiniteMeasure_sfiniteSeq
  签名: [h : SFinite μ] (n : 自然数)
  定义体: h.1.choose_spec.1 n

Depends on / 依赖: choose_spec
-/
instance isFiniteMeasure_sfiniteSeq [h : SFinite μ] (n : Nat) : IsFiniteMeasure (sfiniteSeq μ n) :=
  h.1.choose_spec.1 n

/--
lemma `sum_sfiniteSeq` / 引理 `sum_sfiniteSeq`

English:
lemma sum_sfiniteSeq
  given: (μ : Measure α) [h : SFinite μ]
  statement: sum (sfiniteSeq μ) = μ
  proof: h.1.choose_spec.2.symm

中文:
引理 sum_sfiniteSeq
  条件: (μ : 测度 α) [h : SFinite μ]
  结论: 求和 (sfiniteSeq μ) = μ
  证明: h.1.choose_spec.2.symm

Depends on / 依赖: choose_spec
-/
lemma sum_sfiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sfiniteSeq μ) = μ :=
  h.1.choose_spec.2.symm

/--
lemma `sfiniteSeq_le` / 引理 `sfiniteSeq_le`

English:
lemma sfiniteSeq_le
  given: (μ : Measure α) [SFinite μ] (n : Nat)
  statement: sfiniteSeq μ n <= μ
  proof: (le_sum _ n).trans (sum_sfiniteSeq μ).le

中文:
引理 sfiniteSeq_le
  条件: (μ : 测度 α) [SFinite μ] (n : 自然数)
  结论: sfiniteSeq μ n <= μ
  证明: (le_sum _ n).trans (sum_sfiniteSeq μ).le

Depends on / 依赖: le_sum, sum_sfiniteSeq
-/
lemma sfiniteSeq_le (μ : Measure α) [SFinite μ] (n : Nat) : sfiniteSeq μ n <= μ :=
  (le_sum _ n).trans (sum_sfiniteSeq μ).le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SFinite (0 : Measure α)
  body: ⟨fun _ => 0, inferInstance, by rw [Measure.sum_zero]⟩

@[simp]

中文:
实例 :
  签名: SFinite (0 : 测度 α)
  定义体: ⟨fun _ => 0, inferInstance, by rw [Measure.sum_zero]⟩

@[simp]

Depends on / 依赖: Measure, Measure.sum_zero, sum_zero
-/
instance : SFinite (0 : Measure α) := ⟨fun _ => 0, inferInstance, by rw [Measure.sum_zero]⟩

@[simp]
/--
lemma `sfiniteSeq_zero` / 引理 `sfiniteSeq_zero`

English:
lemma sfiniteSeq_zero
  given: (n : Nat)
  statement: sfiniteSeq (0 : Measure α) n = 0
  proof: bot_unique sfiniteSeq_le _ _

中文:
引理 sfiniteSeq_zero
  条件: (n : 自然数)
  结论: sfiniteSeq (0 : 测度 α) n = 0
  证明: bot_unique sfiniteSeq_le _ _

Depends on / 依赖: bot_unique, sfiniteSeq_le
-/
lemma sfiniteSeq_zero (n : Nat) : sfiniteSeq (0 : Measure α) n = 0 :=
bot_unique sfiniteSeq_le _ _

/--
lemma `sfinite_sum_of_countable` / 引理 `sfinite_sum_of_countable`

English:
lemma sfinite_sum_of_countable
  statement: [Countable ι]
  proof: by
  obtain ⟨f, hf⟩ : exists f : ι -> Nat, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n => ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n in range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

中文:
引理 sfinite_sum_of_countable
  结论: [可数 ι]
  证明: by
  obtain ⟨f, hf⟩ : exists f : ι -> Nat, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n => ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n in range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

Depends on / 依赖: Countable, Countable.exists_injective_nat, Function, Function.Injective, Function.extend_apply, Injective, Pi.zero_apply, exists_injective_nat, extend_apply, hf.extend_apply, infer_instance, sum_extend_zero, zero_apply
-/
lemma sfinite_sum_of_countable [Countable ι]
    (m : ι -> Measure α) [forall n, IsFiniteMeasure (m n)] : SFinite (Measure.sum m) := by
  obtain ⟨f, hf⟩ : exists f : ι -> Nat, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n => ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n in range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: ι] (m
  body: by
  change SFinite (Measure.sum (fun i => m i))
  simp_rw [← sum_sfiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

中文:
实例 [可数
  签名: ι] (m
  定义体: by
  change SFinite (Measure.sum (fun i => m i))
  simp_rw [← sum_sfiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

Depends on / 依赖: Measure, Measure.sum, Measure.sum_sum, SFinite, sfinite_sum_of_countable, simp_rw, sum_sfiniteSeq, sum_sum
-/
instance [Countable ι] (m : ι -> Measure α) [forall n, SFinite (m n)] : SFinite (Measure.sum m) := by
  change SFinite (Measure.sum (fun i => m i))
  simp_rw [← sum_sfiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] [SFinite ν] : SFinite (μ + ν)
  body: by
  have : forall b : Bool, SFinite (cond b μ ν) := by simp [*]
  simpa using (inferInstance : SFinite (.sum (cond · μ ν)))

中文:
实例 [SFinite
  签名: μ] [SFinite ν] : SFinite (μ + ν)
  定义体: by
  have : forall b : Bool, SFinite (cond b μ ν) := by simp [*]
  simpa using (inferInstance : SFinite (.sum (cond · μ ν)))

Depends on / 依赖: SFinite
-/
instance [SFinite μ] [SFinite ν] : SFinite (μ + ν) := by
  have : forall b : Bool, SFinite (cond b μ ν) := by simp [*]
  simpa using (inferInstance : SFinite (.sum (cond · μ ν)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] (s
  body: ⟨fun n => (sfiniteSeq μ n).restrict s, fun n => inferInstance,
    by rw [← restrict_sum_of_countable, sum_sfiniteSeq]⟩

中文:
实例 [SFinite
  签名: μ] (s
  定义体: ⟨fun n => (sfiniteSeq μ n).restrict s, fun n => inferInstance,
    by rw [← restrict_sum_of_countable, sum_sfiniteSeq]⟩

Depends on / 依赖: restrict, restrict_sum_of_countable, sfiniteSeq, sum_sfiniteSeq
-/
instance [SFinite μ] (s : Set α) : SFinite (μ.restrict s) :=
  ⟨fun n => (sfiniteSeq μ n).restrict s, fun n => inferInstance,
    by rw [← restrict_sum_of_countable, sum_sfiniteSeq]⟩

variable (μ) in
/--
theorem `exists_isFiniteMeasure_absolutelyContinuous` / 定理 `exists_isFiniteMeasure_absolutelyContinuous`

English:
theorem exists_isFiniteMeasure_absolutelyContinuous
  given: [SFinite μ]
  proof: by
  rcases ENNReal.exists_pos_tsum_mul_lt_of_countable top_ne_zero (sfiniteSeq μ · univ)
    fun _ => measure_ne_top _ _ with ⟨c, hc₀, hc⟩
  have {s : Set α} : sum (fun n => c n • sfiniteSeq μ n) s = 0 ↔ μ s = 0 := by
    conv_rhs => rw [← sum_sfiniteSeq μ, sum_apply_of_countable]
    simp [(hc₀ _).ne']
  refine ⟨.sum fun n => c n • sfiniteSeq μ n, ⟨?_⟩, fun _ => this.1, fun _ => this.2⟩
  simpa [mul_comm] using hc

中文:
定理 存在_isFiniteMeasure_absolutelyContinuous
  条件: [SFinite μ]
  证明: by
  rcases ENNReal.exists_pos_tsum_mul_lt_of_countable top_ne_zero (sfiniteSeq μ · univ)
    fun _ => measure_ne_top _ _ with ⟨c, hc₀, hc⟩
  have {s : Set α} : sum (fun n => c n • sfiniteSeq μ n) s = 0 ↔ μ s = 0 := by
    conv_rhs => rw [← sum_sfiniteSeq μ, sum_apply_of_countable]
    simp [(hc₀ _).ne']
  refine ⟨.sum fun n => c n • sfiniteSeq μ n, ⟨?_⟩, fun _ => this.1, fun _ => this.2⟩
  simpa [mul_comm] using hc

Depends on / 依赖: ENNReal, ENNReal.exists_pos_tsum_mul_lt_of_countable, conv_rhs, exists_pos_tsum_mul_lt_of_countable, measure_ne_top, mul_comm, sfiniteSeq, sum_apply_of_countable, sum_sfiniteSeq, top_ne_zero
-/
theorem exists_isFiniteMeasure_absolutelyContinuous [SFinite μ] :
    exists ν : Measure α, IsFiniteMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ := by
  rcases ENNReal.exists_pos_tsum_mul_lt_of_countable top_ne_zero (sfiniteSeq μ · univ)
    fun _ => measure_ne_top _ _ with ⟨c, hc₀, hc⟩
  have {s : Set α} : sum (fun n => c n • sfiniteSeq μ n) s = 0 ↔ μ s = 0 := by
    conv_rhs => rw [← sum_sfiniteSeq μ, sum_apply_of_countable]
    simp [(hc₀ _).ne']
  refine ⟨.sum fun n => c n • sfiniteSeq μ n, ⟨?_⟩, fun _ => this.1, fun _ => this.2⟩
  simpa [mul_comm] using hc

end SFinite

/--
Definition of `SigmaFinite` / `SigmaFinite` 的定义

English:
class SigmaFinite
  parameters: {m0 : MeasurableSpace α} (μ : Measure α)
  axioms and operations (1):
    - out' : Nonempty (μ.FiniteSpanningSetsIn univ)

中文:
类 σ有限
  参数: {m0 : 可测空间 α} (μ : 测度 α)
  公理与运算 (1 个):
    - out' : 非空 (μ.FiniteSpanningSetsIn univ)
-/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)

/--
theorem `sigmaFinite_iff` / 定理 `sigmaFinite_iff`

English:
theorem sigmaFinite_iff
  statement: SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ)
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 sigmaFinite_iff
  结论: σ有限 μ ↔ 非空 (μ.FiniteSpanningSetsIn univ)
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `SigmaFinite.out` / 定理 `SigmaFinite.out`

English:
theorem SigmaFinite.out
  given: (h : SigmaFinite μ)
  statement: Nonempty (μ.FiniteSpanningSetsIn univ)
  proof: h.1

中文:
定理 σ有限.out
  条件: (h : σ有限 μ)
  结论: 非空 (μ.FiniteSpanningSetsIn univ)
  证明: h.1
-/
theorem SigmaFinite.out (h : SigmaFinite μ) : Nonempty (μ.FiniteSpanningSetsIn univ) :=
  h.1

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Measure.toFiniteSpanningSetsIn` / `Measure.toFiniteSpanningSetsIn` 的定义

English:
definition Measure.toFiniteSpanningSetsIn
  signature: (μ : Measure α) [h : SigmaFinite μ]
  body: toMeasurable μ (h.out.some.set n)
  set_mem _ := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun _ => subset_toMeasurable _ _) h.out.some.spanning

中文:
定义 测度.toFiniteSpanningSetsIn
  签名: (μ : 测度 α) [h : σ有限 μ]
  定义体: toMeasurable μ (h.out.some.set n)
  set_mem _ := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun _ => subset_toMeasurable _ _) h.out.some.spanning

Depends on / 依赖: h.out.some.set, toMeasurable
-/
noncomputable def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } where
  set n := toMeasurable μ (h.out.some.set n)
  set_mem _ := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun _ => subset_toMeasurable _ _) h.out.some.spanning

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `spanningSets` / `spanningSets` 的定义

English:
definition spanningSets
  signature: (μ : Measure α) [SigmaFinite μ] (i : Nat)
  body: accumulate μ.toFiniteSpanningSetsIn.set i

中文:
定义 spanningSets
  签名: (μ : 测度 α) [σ有限 μ] (i : 自然数)
  定义体: accumulate μ.toFiniteSpanningSetsIn.set i

Depends on / 依赖: accumulate, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.set
-/
noncomputable def spanningSets (μ : Measure α) [SigmaFinite μ] (i : Nat) : Set α :=
  accumulate μ.toFiniteSpanningSetsIn.set i

/--
theorem `monotone_spanningSets` / 定理 `monotone_spanningSets`

English:
theorem monotone_spanningSets
  given: (μ : Measure α) [SigmaFinite μ]
  statement: Monotone (spanningSets μ)
  proof: monotone_accumulate

@[gcongr]

中文:
定理 monotone_spanningSets
  条件: (μ : 测度 α) [σ有限 μ]
  结论: 递增 (spanningSets μ)
  证明: monotone_accumulate

@[gcongr]

Depends on / 依赖: monotone_accumulate
-/
theorem monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanningSets μ) :=
  monotone_accumulate

@[gcongr]
/--
lemma `spanningSets_mono` / 引理 `spanningSets_mono`

English:
lemma spanningSets_mono
  given: [SigmaFinite μ] {m n : Nat} (hmn : m <= n)
  proof: monotone_spanningSets _ hmn

中文:
引理 spanningSets_mono
  条件: [σ有限 μ] {m n : 自然数} (hmn : m <= n)
  证明: monotone_spanningSets _ hmn

Depends on / 依赖: monotone_spanningSets
-/
lemma spanningSets_mono [SigmaFinite μ] {m n : Nat} (hmn : m <= n) :
    spanningSets μ m subseteq spanningSets μ n := monotone_spanningSets _ hmn

/--
theorem `measurableSet_spanningSets` / 定理 `measurableSet_spanningSets`

English:
theorem measurableSet_spanningSets
  given: (μ : Measure α) [SigmaFinite μ] (i : Nat)
  proof: MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j

中文:
定理 measurableSet_spanningSets
  条件: (μ : 测度 α) [σ有限 μ] (i : 自然数)
  证明: MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, set_mem, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.set_mem
-/
theorem measurableSet_spanningSets (μ : Measure α) [SigmaFinite μ] (i : Nat) :
    MeasurableSet (spanningSets μ i) :=
  MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j

/--
theorem `measure_spanningSets_lt_top` / 定理 `measure_spanningSets_lt_top`

English:
theorem measure_spanningSets_lt_top
  given: (μ : Measure α) [SigmaFinite μ] (i : Nat)
  proof: measure_biUnion_lt_top (finite_le_nat i) fun j _ => μ.toFiniteSpanningSetsIn.finite j

@[simp]

中文:
定理 measure_spanningSets_lt_top
  条件: (μ : 测度 α) [σ有限 μ] (i : 自然数)
  证明: measure_biUnion_lt_top (finite_le_nat i) fun j _ => μ.toFiniteSpanningSetsIn.finite j

@[simp]

Depends on / 依赖: finite, finite_le_nat, measure_biUnion_lt_top, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.finite
-/
theorem measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : Nat) :
    μ (spanningSets μ i) < ∞ :=
  measure_biUnion_lt_top (finite_le_nat i) fun j _ => μ.toFiniteSpanningSetsIn.finite j

@[simp]
/--
theorem `iUnion_spanningSets` / 定理 `iUnion_spanningSets`

English:
theorem iUnion_spanningSets
  given: (μ : Measure α) [SigmaFinite μ]
  statement: ⋃ i : Nat, spanningSets μ i = univ
  proof: by
  simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]

中文:
定理 iUnion_spanningSets
  条件: (μ : 测度 α) [σ有限 μ]
  结论: ⋃ i : 自然数, spanningSets μ i = univ
  证明: by
  simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]

Depends on / 依赖: iUnion_accumulate, simp_rw, spanning, spanningSets, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.spanning
-/
theorem iUnion_spanningSets (μ : Measure α) [SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ := by
  simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]

/--
theorem `isCountablySpanning_spanningSets` / 定理 `isCountablySpanning_spanningSets`

English:
theorem isCountablySpanning_spanningSets
  given: (μ : Measure α) [SigmaFinite μ]
  proof: ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩

中文:
定理 isCountablySpanning_spanningSets
  条件: (μ : 测度 α) [σ有限 μ]
  证明: ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩

Depends on / 依赖: iUnion_spanningSets, mem_range_self, spanningSets
-/
theorem isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] :
    IsCountablySpanning (range (spanningSets μ)) :=
  ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩

open scoped Classical in
/--
Definition of `spanningSetsIndex` / `spanningSetsIndex` 的定义

English:
definition spanningSetsIndex
  signature: (μ : Measure α) [SigmaFinite μ] (x : α)
  body: Nat.find iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x

中文:
定义 spanningSetsIndex
  签名: (μ : 测度 α) [σ有限 μ] (x : α)
  定义体: Nat.find iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x

Depends on / 依赖: Nat.find, iUnion_eq_univ_iff, iUnion_spanningSets
-/
noncomputable def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : Nat :=
Nat.find iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x

/--
theorem `measurableSet_spanningSetsIndex` / 定理 `measurableSet_spanningSetsIndex`

English:
theorem measurableSet_spanningSetsIndex
  given: (μ : Measure α) [SigmaFinite μ]
  proof: by
  classical
exact measurable_find _ measurableSet_spanningSets μ

中文:
定理 measurableSet_spanningSetsIndex
  条件: (μ : 测度 α) [σ有限 μ]
  证明: by
  classical
exact measurable_find _ measurableSet_spanningSets μ

Depends on / 依赖: classical, measurableSet_spanningSets, measurable_find
-/
theorem measurableSet_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] :
    Measurable (spanningSetsIndex μ) := by
  classical
exact measurable_find _ measurableSet_spanningSets μ

/--
theorem `preimage_spanningSetsIndex_singleton` / 定理 `preimage_spanningSetsIndex_singleton`

English:
theorem preimage_spanningSetsIndex_singleton
  given: (μ : Measure α) [SigmaFinite μ] (n : Nat)
  proof: by
  classical
  exact preimage_find_eq_disjointed _ _ _

中文:
定理 preimage_spanningSetsIndex_singleton
  条件: (μ : 测度 α) [σ有限 μ] (n : 自然数)
  证明: by
  classical
  exact preimage_find_eq_disjointed _ _ _

Depends on / 依赖: classical, preimage_find_eq_disjointed
-/
theorem preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : Nat) :
    spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n := by
  classical
  exact preimage_find_eq_disjointed _ _ _

/--
theorem `spanningSetsIndex_eq_iff` / 定理 `spanningSetsIndex_eq_iff`

English:
theorem spanningSetsIndex_eq_iff
  given: (μ : Measure α) [SigmaFinite μ] {x : α} {n : Nat}
  proof: by
  convert! Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x

中文:
定理 spanningSetsIndex_eq_iff
  条件: (μ : 测度 α) [σ有限 μ] {x : α} {n : 自然数}
  证明: by
  convert! Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x

Depends on / 依赖: Set.ext_iff, convert, ext_iff, preimage_spanningSetsIndex_singleton
-/
theorem spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : Nat} :
    spanningSetsIndex μ x = n ↔ x in disjointed (spanningSets μ) n := by
  convert! Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x

/--
theorem `mem_disjointed_spanningSetsIndex` / 定理 `mem_disjointed_spanningSetsIndex`

English:
theorem mem_disjointed_spanningSetsIndex
  given: (μ : Measure α) [SigmaFinite μ] (x : α)
  proof: (spanningSetsIndex_eq_iff μ).1 rfl

中文:
定理 mem_disjointed_spanningSetsIndex
  条件: (μ : 测度 α) [σ有限 μ] (x : α)
  证明: (spanningSetsIndex_eq_iff μ).1 rfl

Depends on / 依赖: spanningSetsIndex_eq_iff
-/
theorem mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x in disjointed (spanningSets μ) (spanningSetsIndex μ x) :=
  (spanningSetsIndex_eq_iff μ).1 rfl

/--
theorem `mem_spanningSetsIndex` / 定理 `mem_spanningSetsIndex`

English:
theorem mem_spanningSetsIndex
  given: (μ : Measure α) [SigmaFinite μ] (x : α)
  proof: disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)

中文:
定理 mem_spanningSetsIndex
  条件: (μ : 测度 α) [σ有限 μ] (x : α)
  证明: disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)

Depends on / 依赖: disjointed_subset, mem_disjointed_spanningSetsIndex
-/
theorem mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x in spanningSets μ (spanningSetsIndex μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)

/--
theorem `mem_spanningSets_of_index_le` / 定理 `mem_spanningSets_of_index_le`

English:
theorem mem_spanningSets_of_index_le
  statement: (μ : Measure α) [SigmaFinite μ] (x : α) {n : Nat}
  proof: monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)

中文:
定理 mem_spanningSets_of_index_le
  结论: (μ : 测度 α) [σ有限 μ] (x : α) {n : 自然数}
  证明: monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)

Depends on / 依赖: mem_spanningSetsIndex, monotone_spanningSets
-/
theorem mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : Nat}
    (hn : spanningSetsIndex μ x <= n) : x in spanningSets μ n :=
  monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)

/--
theorem `eventually_mem_spanningSets` / 定理 `eventually_mem_spanningSets`

English:
theorem eventually_mem_spanningSets
  given: (μ : Measure α) [SigmaFinite μ] (x : α)
  proof: eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩

中文:
定理 eventually_mem_spanningSets
  条件: (μ : 测度 α) [σ有限 μ] (x : α)
  证明: eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩

Depends on / 依赖: eventually_atTop, mem_spanningSets_of_index_le, spanningSetsIndex
-/
theorem eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) :
    forallᶠ n in atTop, x in spanningSets μ n :=
  eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩

/--
lemma `measure_singleton_lt_top` / 引理 `measure_singleton_lt_top`

English:
lemma measure_singleton_lt_top
  given: [SigmaFinite μ]
  statement: μ {a} < ∞
  proof: measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)

中文:
引理 measure_singleton_lt_top
  条件: [σ有限 μ]
  结论: μ {a} < ∞
  证明: measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)

Depends on / 依赖: measure_lt_top_mono, measure_spanningSets_lt_top, mem_spanningSetsIndex, singleton_subset_iff
-/
lemma measure_singleton_lt_top [SigmaFinite μ] : μ {a} < ∞ :=
  measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)

/--
theorem `sum_restrict_disjointed_spanningSets` / 定理 `sum_restrict_disjointed_spanningSets`

English:
theorem sum_restrict_disjointed_spanningSets
  given: (μ ν : Measure α) [SigmaFinite ν]
  proof: by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurableSet_spanningSets _))]; rw [iUnion_disjointed]; rw [iUnion_spanningSets]; rw [restrict_univ]

中文:
定理 sum_restrict_disjointed_spanningSets
  条件: (μ ν : 测度 α) [σ有限 ν]
  证明: by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurableSet_spanningSets _))]; rw [iUnion_disjointed]; rw [iUnion_spanningSets]; rw [restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.disjointed, disjoint_disjointed, disjointed, iUnion_disjointed, iUnion_spanningSets, measurableSet_spanningSets, restrict_iUnion, restrict_univ
-/
theorem sum_restrict_disjointed_spanningSets (μ ν : Measure α) [SigmaFinite ν] :
    sum (fun n => μ.restrict (disjointed (spanningSets ν) n)) = μ := by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurableSet_spanningSets _))]; rw [iUnion_disjointed]; rw [iUnion_spanningSets]; rw [restrict_univ]

instance (priority := 100) [SigmaFinite μ] : SFinite μ := by
  have : forall n, Fact (μ (disjointed (spanningSets μ) n) < ∞) :=
    fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)⟩
  exact ⟨⟨fun n => μ.restrict (disjointed (spanningSets μ) n), fun n => by infer_instance,
    (sum_restrict_disjointed_spanningSets μ μ).symm⟩⟩

namespace Measure

/-- A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero measure. -/
@[deprecated forall_measure_inter_isCountablySpanning_eq_zero (since := "2026-03-13")]
/--
theorem `forall_measure_inter_spanningSets_eq_zero` / 定理 `forall_measure_inter_spanningSets_eq_zero`

English:
theorem forall_measure_inter_spanningSets_eq_zero
  statement: [MeasurableSpace α] {μ : Measure α}
  proof: by
  nth_rw 2 [show s = ⋃ n, s inter spanningSets μ n by
      rw [← inter_iUnion]; rw [iUnion_spanningSets]; rw [inter_univ]]
  rw [measure_iUnion_null_iff]

中文:
定理 对任意_measure_inter_spanningSets_eq_zero
  结论: [可测空间 α] {μ : 测度 α}
  证明: by
  nth_rw 2 [show s = ⋃ n, s inter spanningSets μ n by
      rw [← inter_iUnion]; rw [iUnion_spanningSets]; rw [inter_univ]]
  rw [measure_iUnion_null_iff]

Depends on / 依赖: iUnion_spanningSets, inter_iUnion, inter_univ, measure_iUnion_null_iff, nth_rw, spanningSets
-/
theorem forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (s : Set α) : (forall n, μ (s inter spanningSets μ n) = 0) ↔ μ s = 0 := by
  nth_rw 2 [show s = ⋃ n, s inter spanningSets μ n by
      rw [← inter_iUnion]; rw [iUnion_spanningSets]; rw [inter_univ]]
  rw [measure_iUnion_null_iff]

/--
theorem `exists_measure_inter_spanningSets_pos` / 定理 `exists_measure_inter_spanningSets_pos`

English:
theorem exists_measure_inter_spanningSets_pos
  statement: [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
  proof: by
  contrapose!
  rw [nonpos_iff_eq_zero]; rw [← forall_measure_inter_isCountablySpanning_eq_zero
    (isCountablySpanning_spanningSets μ)]
  simp

中文:
定理 存在_measure_inter_spanningSets_pos
  结论: [可测空间 α] {μ : 测度 α} [σ有限 μ]
  证明: by
  contrapose!
  rw [nonpos_iff_eq_zero]; rw [← forall_measure_inter_isCountablySpanning_eq_zero
    (isCountablySpanning_spanningSets μ)]
  simp

Depends on / 依赖: contrapose, forall_measure_inter_isCountablySpanning_eq_zero, isCountablySpanning_spanningSets, nonpos_iff_eq_zero
-/
theorem exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (s : Set α) : (exists n, 0 < μ (s inter spanningSets μ n)) ↔ 0 < μ s := by
  contrapose!
  rw [nonpos_iff_eq_zero]; rw [← forall_measure_inter_isCountablySpanning_eq_zero
    (isCountablySpanning_spanningSets μ)]
  simp

/--
theorem `finite_const_le_meas_of_disjoint_iUnion₀` / 定理 `finite_const_le_meas_of_disjoint_iUnion₀`

English:
theorem finite_const_le_meas_of_disjoint_iUnion₀
  statement: {ι : Type*} [MeasurableSpace α] (μ : Measure α)
  proof: ENNReal.finite_const_le_of_tsum_ne_top
    (ne_top_of_le_ne_top Union_As_finite (tsum_meas_le_meas_iUnion_of_disjoint₀ μ As_mble As_disj))
    ε_pos.ne'

中文:
定理 finite_const_le_meas_of_disjoint_iUnion₀
  结论: {ι : 类型} [可测空间 α] (μ : 测度 α)
  证明: ENNReal.finite_const_le_of_tsum_ne_top
    (ne_top_of_le_ne_top Union_As_finite (tsum_meas_le_meas_iUnion_of_disjoint₀ μ As_mble As_disj))
    ε_pos.ne'

Depends on / 依赖: As_disj, As_mble, ENNReal, ENNReal.finite_const_le_of_tsum_ne_top, Union_As_finite, _pos.ne, finite_const_le_of_tsum_ne_top, ne_top_of_le_ne_top
-/
theorem finite_const_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (As_mble : forall i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) != ∞) :
    Set.Finite { i : ι | ε <= μ (As i) } :=
  ENNReal.finite_const_le_of_tsum_ne_top
    (ne_top_of_le_ne_top Union_As_finite (tsum_meas_le_meas_iUnion_of_disjoint₀ μ As_mble As_disj))
    ε_pos.ne'

/--
theorem `finite_const_le_meas_of_disjoint_iUnion` / 定理 `finite_const_le_meas_of_disjoint_iUnion`

English:
theorem finite_const_le_meas_of_disjoint_iUnion
  statement: {ι : Type*} [MeasurableSpace α] (μ : Measure α)
  proof: finite_const_le_meas_of_disjoint_iUnion₀ μ ε_pos (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h)) Union_As_finite

中文:
定理 finite_const_le_meas_of_disjoint_iUnion
  结论: {ι : 类型} [可测空间 α] (μ : 测度 α)
  证明: finite_const_le_meas_of_disjoint_iUnion₀ μ ε_pos (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h)) Union_As_finite

Depends on / 依赖: As_disj, As_mble, Disjoint, Disjoint.aedisjoint, Union_As_finite, aedisjoint, nullMeasurableSet
-/
theorem finite_const_le_meas_of_disjoint_iUnion {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) != ∞) :
    Set.Finite { i : ι | ε <= μ (As i) } :=
  finite_const_le_meas_of_disjoint_iUnion₀ μ ε_pos (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h)) Union_As_finite

/--
theorem `_root_.Set.Infinite.meas_eq_top` / 定理 `_root_.Set.Infinite.meas_eq_top`

English:
theorem _root_.Set.Infinite.meas_eq_top
  statement: [MeasurableSingletonClass α]
  proof: top_unique
  let ⟨ε, hne, hε⟩ := h'; have := hs.to_subtype
  calc
    ∞ = ∑' _ : s, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
    _ <= ∑' x : s, μ {x.1} := ENNReal.tsum_le_tsum fun x => hε x x.2
    _ <= μ (⋃ x : s, {x.1}) := tsum_meas_le_meas_iUnion_of_disjoint _
      (fun _ => MeasurableSet.singleton _) fun x y hne => by simpa [Subtype.val_inj]
    _ = μ s := by simp

中文:
定理 _root_.集合.无限.meas_eq_top
  结论: [MeasurableSingleton类 α]
  证明: top_unique
  let ⟨ε, hne, hε⟩ := h'; have := hs.to_subtype
  calc
    ∞ = ∑' _ : s, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
    _ <= ∑' x : s, μ {x.1} := ENNReal.tsum_le_tsum fun x => hε x x.2
    _ <= μ (⋃ x : s, {x.1}) := tsum_meas_le_meas_iUnion_of_disjoint _
      (fun _ => MeasurableSet.singleton _) fun x y hne => by simpa [Subtype.val_inj]
    _ = μ s := by simp

Depends on / 依赖: top_unique
-/
theorem _root_.Set.Infinite.meas_eq_top [MeasurableSingletonClass α]
{s : Set α} (hs : s.Infinite) (h' : exists ε, ε != 0 ∧ forall x in s, ε <= μ {x}) : μ s = ∞ := top_unique
  let ⟨ε, hne, hε⟩ := h'; have := hs.to_subtype
  calc
    ∞ = ∑' _ : s, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
    _ <= ∑' x : s, μ {x.1} := ENNReal.tsum_le_tsum fun x => hε x x.2
    _ <= μ (⋃ x : s, {x.1}) := tsum_meas_le_meas_iUnion_of_disjoint _
      (fun _ => MeasurableSet.singleton _) fun x y hne => by simpa [Subtype.val_inj]
    _ = μ s := by simp

/--
theorem `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀` / 定理 `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀`

English:
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  statement: {ι : Type*} {_ : MeasurableSpace α}
  proof: by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : Real>=0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : Nat => { i : ι | as n <= μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : forall n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine countable_iUnion fun n => Finite.countable ?_
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

中文:
定理 countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  结论: {ι : 类型} {_ : 可测空间 α}
  证明: by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : Real>=0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : Nat => { i : ι | as n <= μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : forall n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine countable_iUnion fun n => Finite.countable ?_
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

Depends on / 依赖: as_lim, as_mem, countable_union, exists_seq_strictAnti_tendsto, fairmeas, fairmeas_eq, iUnion_Ici_eq_Ioi_of_lt_of_tendsto, posmeas, posmeas_def, preimage_iUnion, zero_lt_one
-/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) != ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : Real>=0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : Nat => { i : ι | as n <= μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : forall n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine countable_iUnion fun n => Finite.countable ?_
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

/--
theorem `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top` / 定理 `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top`

English:
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
  statement: {ι : Type*} {_ : MeasurableSpace α}
  proof: countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h))) Union_As_finite

中文:
定理 countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
  结论: {ι : 类型} {_ : 可测空间 α}
  证明: countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h))) Union_As_finite

Depends on / 依赖: As_disj, As_mble, Disjoint, Disjoint.aedisjoint, Union_As_finite, aedisjoint, nullMeasurableSet
-/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) != ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h))) Union_As_finite

/--
theorem `countable_meas_pos_of_disjoint_iUnion₀` / 定理 `countable_meas_pos_of_disjoint_iUnion₀`

English:
theorem countable_meas_pos_of_disjoint_iUnion₀
  statement: {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: by
  rw [← sum_sfiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sfiniteSeq μ) (As i) }
      subseteq ⋃ n, { i : ι | 0 < sfiniteSeq μ n (As i) } := by
    intro i hi
    by_contra con
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    rw [sum_apply₀] at hi
    · simp_rw [con] at hi
      simp at hi
    · exact As_mble i
  apply Countable.mono obs
  refine countable_iUnion fun n => ?_
  apply countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  · exact fun i => (As_mble i).mono (le_sum _ _)
  · exact fun i j hij => AEDisjoint.of_le (As_disj hij) (le_sum _ _)
  · exact measure_ne_top _ (⋃ i, As i)

中文:
定理 countable_meas_pos_of_disjoint_iUnion₀
  结论: {ι : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: by
  rw [← sum_sfiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sfiniteSeq μ) (As i) }
      subseteq ⋃ n, { i : ι | 0 < sfiniteSeq μ n (As i) } := by
    intro i hi
    by_contra con
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    rw [sum_apply₀] at hi
    · simp_rw [con] at hi
      simp at hi
    · exact As_mble i
  apply Countable.mono obs
  refine countable_iUnion fun n => ?_
  apply countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  · exact fun i => (As_mble i).mono (le_sum _ _)
  · exact fun i j hij => AEDisjoint.of_le (As_disj hij) (le_sum _ _)
  · exact measure_ne_top _ (⋃ i, As i)

Depends on / 依赖: As_disj, As_mble, Countable, Countable.mono, countable_iUnion, le_s, mem_iUnion, mem_ofPred_eq, nonpos_iff_eq_zero, not_exists, not_lt, sfiniteSeq, simp_rw, subseteq, sum_sfiniteSeq
-/
theorem countable_meas_pos_of_disjoint_iUnion₀ {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι -> Set α} (As_mble : forall i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  rw [← sum_sfiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sfiniteSeq μ) (As i) }
      subseteq ⋃ n, { i : ι | 0 < sfiniteSeq μ n (As i) } := by
    intro i hi
    by_contra con
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    rw [sum_apply₀] at hi
    · simp_rw [con] at hi
      simp at hi
    · exact As_mble i
  apply Countable.mono obs
  refine countable_iUnion fun n => ?_
  apply countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  · exact fun i => (As_mble i).mono (le_sum _ _)
  · exact fun i j hij => AEDisjoint.of_le (As_disj hij) (le_sum _ _)
  · exact measure_ne_top _ (⋃ i, As i)

/--
theorem `countable_meas_pos_of_disjoint_iUnion` / 定理 `countable_meas_pos_of_disjoint_iUnion`

English:
theorem countable_meas_pos_of_disjoint_iUnion
  statement: {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: countable_meas_pos_of_disjoint_iUnion₀ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h)))

中文:
定理 countable_meas_pos_of_disjoint_iUnion
  结论: {ι : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: countable_meas_pos_of_disjoint_iUnion₀ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h)))

Depends on / 依赖: As_disj, As_mble, Disjoint, Disjoint.aedisjoint, aedisjoint, nullMeasurableSet
-/
theorem countable_meas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_iUnion₀ (fun i => (As_mble i).nullMeasurableSet)
    ((fun _ _ h => Disjoint.aedisjoint (As_disj h)))

/--
theorem `countable_meas_level_set_pos₀` / 定理 `countable_meas_level_set_pos₀`

English:
theorem countable_meas_level_set_pos₀
  statement: {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: by
  have level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b))
    ((fun _ _ h => Disjoint.aedisjoint (level_sets_disjoint h)))

中文:
定理 countable_meas_level_set_pos₀
  结论: {α β : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: by
  have level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b))
    ((fun _ _ h => Disjoint.aedisjoint (level_sets_disjoint h)))

Depends on / 依赖: Disjoint, Disjoint.aedisjoint, Disjoint.preimage, MeasurableSingletonClass, Measure, Measure.countable_meas_pos_of_disjoint_iUnion, Pairwise, aedisjoint, disjoint_singleton, disjoint_singleton.mpr, g_mble, level_sets_disjoint, measurableSet_singleton, preimage
-/
theorem countable_meas_level_set_pos₀ {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α -> β}
    (g_mble : NullMeasurable g μ) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } := by
  have level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b))
    ((fun _ _ h => Disjoint.aedisjoint (level_sets_disjoint h)))

/--
theorem `countable_meas_level_set_pos` / 定理 `countable_meas_level_set_pos`

English:
theorem countable_meas_level_set_pos
  statement: {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: countable_meas_level_set_pos₀ g_mble.nullMeasurable

中文:
定理 countable_meas_level_set_pos
  结论: {α β : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: countable_meas_level_set_pos₀ g_mble.nullMeasurable

Depends on / 依赖: g_mble, g_mble.nullMeasurable, nullMeasurable
-/
theorem countable_meas_level_set_pos {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α -> β}
    (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } :=
  countable_meas_level_set_pos₀ g_mble.nullMeasurable

/--
lemma `exists_ae_subset_biUnion_countable_of_isFiniteMeasure` / 引理 `exists_ae_subset_biUnion_countable_of_isFiniteMeasure`

English:
lemma exists_ae_subset_biUnion_countable_of_isFiniteMeasure
  statement: [IsFiniteMeasure μ]
  proof: by
  let m := ⨆ D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D)
  obtain ⟨D, D_mem, hD⟩ : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D) = m := by
    rcases eq_bot_or_bot_lt m with hm | hm
    · exact ⟨∅, by simp, by simp [hm]⟩
    obtain ⟨u, -, u_mem, u_lim⟩ :
        exists u : Nat -> Real>=0∞, StrictMono u ∧ (forall n, u n in Ioo 0 m) ∧ Tendsto u atTop (𝓝 m) :=
      exists_seq_strictMono_tendsto' hm
    have A n : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, u n < μ (⋃₀ D) :=
      lt_biSup_iff.1 (u_mem n).2
    choose! D D_mem huD using A
    have hD : ⋃ n, D n in {D | D subseteq C ∧ D.Countable} := by simp; grind
    refine ⟨⋃ n, D n, hD, ?_⟩
    apply le_antisymm (le_biSup (f := fun D => μ (⋃₀ D)) hD)
    apply le_of_tendsto' u_lim (fun n => (huD n).le.trans ?_)
    exact measure_mono (fun x hx => by simp at hx ⊢; grind)
  refine ⟨D, by grind, by grind, fun s hs => union_ae_eq_right_iff_ae_subset.mp ?_⟩
  symm
  apply ae_eq_of_ae_subset_of_measure_ge subset_union_right.eventuallyLE
  · rw [hD, show s union ⋃₀ D = ⋃₀ (D union {s}) by simp]
    apply le_biSup (f := fun D => μ (⋃₀ D))
    simp [D_mem.2, insert_subset_iff, hs, D_mem.1]
  · exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
  · simp

中文:
引理 存在_ae_subset_biUnion_countable_of_isFiniteMeasure
  结论: [是有限测度 μ]
  证明: by
  let m := ⨆ D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D)
  obtain ⟨D, D_mem, hD⟩ : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D) = m := by
    rcases eq_bot_or_bot_lt m with hm | hm
    · exact ⟨∅, by simp, by simp [hm]⟩
    obtain ⟨u, -, u_mem, u_lim⟩ :
        exists u : Nat -> Real>=0∞, StrictMono u ∧ (forall n, u n in Ioo 0 m) ∧ Tendsto u atTop (𝓝 m) :=
      exists_seq_strictMono_tendsto' hm
    have A n : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, u n < μ (⋃₀ D) :=
      lt_biSup_iff.1 (u_mem n).2
    choose! D D_mem huD using A
    have hD : ⋃ n, D n in {D | D subseteq C ∧ D.Countable} := by simp; grind
    refine ⟨⋃ n, D n, hD, ?_⟩
    apply le_antisymm (le_biSup (f := fun D => μ (⋃₀ D)) hD)
    apply le_of_tendsto' u_lim (fun n => (huD n).le.trans ?_)
    exact measure_mono (fun x hx => by simp at hx ⊢; grind)
  refine ⟨D, by grind, by grind, fun s hs => union_ae_eq_right_iff_ae_subset.mp ?_⟩
  symm
  apply ae_eq_of_ae_subset_of_measure_ge subset_union_right.eventuallyLE
  · rw [hD, show s union ⋃₀ D = ⋃₀ (D union {s}) by simp]
    apply le_biSup (f := fun D => μ (⋃₀ D))
    simp [D_mem.2, insert_subset_iff, hs, D_mem.1]
  · exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
  · simp
-/
private lemma exists_ae_subset_biUnion_countable_of_isFiniteMeasure [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : forall s in C, MeasurableSet s) :
    exists D subseteq C, D.Countable ∧ forall s in C, s <=ᵐ[μ] (⋃₀ D) := by
  let m := ⨆ D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D)
  obtain ⟨D, D_mem, hD⟩ : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, μ (⋃₀ D) = m := by
    rcases eq_bot_or_bot_lt m with hm | hm
    · exact ⟨∅, by simp, by simp [hm]⟩
    obtain ⟨u, -, u_mem, u_lim⟩ :
        exists u : Nat -> Real>=0∞, StrictMono u ∧ (forall n, u n in Ioo 0 m) ∧ Tendsto u atTop (𝓝 m) :=
      exists_seq_strictMono_tendsto' hm
    have A n : exists D in {D : Set (Set α) | D subseteq C ∧ D.Countable}, u n < μ (⋃₀ D) :=
      lt_biSup_iff.1 (u_mem n).2
    choose! D D_mem huD using A
    have hD : ⋃ n, D n in {D | D subseteq C ∧ D.Countable} := by simp; grind
    refine ⟨⋃ n, D n, hD, ?_⟩
    apply le_antisymm (le_biSup (f := fun D => μ (⋃₀ D)) hD)
    apply le_of_tendsto' u_lim (fun n => (huD n).le.trans ?_)
    exact measure_mono (fun x hx => by simp at hx ⊢; grind)
  refine ⟨D, by grind, by grind, fun s hs => union_ae_eq_right_iff_ae_subset.mp ?_⟩
  symm
  apply ae_eq_of_ae_subset_of_measure_ge subset_union_right.eventuallyLE
  · rw [hD, show s union ⋃₀ D = ⋃₀ (D union {s}) by simp]
    apply le_biSup (f := fun D => μ (⋃₀ D))
    simp [D_mem.2, insert_subset_iff, hs, D_mem.1]
  · exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
  · simp

variable (μ) in
/--
lemma `exists_ae_subset_biUnion_countable` / 引理 `exists_ae_subset_biUnion_countable`

English:
lemma exists_ae_subset_biUnion_countable
  statement: [SFinite μ]
  proof: by
  have A n : exists D subseteq C, D.Countable ∧ forall s in C, s <=ᵐ[sfiniteSeq μ n] (⋃₀ D) :=
    exists_ae_subset_biUnion_countable_of_isFiniteMeasure hC
  choose D DC D_count hD using A
  refine ⟨⋃ n, D n, by simp [DC], by simp [D_count], fun s hs => ?_⟩
  rw [← sum_sfiniteSeq μ]
  apply ae_sum_iff.2 (fun n => (hD n s hs).trans ?_)
  exact LE.le.eventuallyLE (fun x hx => by simp at hx ⊢; grind)

中文:
引理 存在_ae_subset_biUnion_countable
  结论: [SFinite μ]
  证明: by
  have A n : exists D subseteq C, D.Countable ∧ forall s in C, s <=ᵐ[sfiniteSeq μ n] (⋃₀ D) :=
    exists_ae_subset_biUnion_countable_of_isFiniteMeasure hC
  choose D DC D_count hD using A
  refine ⟨⋃ n, D n, by simp [DC], by simp [D_count], fun s hs => ?_⟩
  rw [← sum_sfiniteSeq μ]
  apply ae_sum_iff.2 (fun n => (hD n s hs).trans ?_)
  exact LE.le.eventuallyLE (fun x hx => by simp at hx ⊢; grind)

Depends on / 依赖: Countable, D.Countable, D_count, LE.le.eventuallyLE, ae_sum_iff, eventuallyLE, exists_ae_subset_biUnion_countable_of_isFiniteMeasure, sfiniteSeq, subseteq, sum_sfiniteSeq
-/
lemma exists_ae_subset_biUnion_countable [SFinite μ]
    {C : Set (Set α)} (hC : forall s in C, MeasurableSet s) :
    exists D subseteq C, D.Countable ∧ forall s in C, s <=ᵐ[μ] (⋃₀ D) := by
  have A n : exists D subseteq C, D.Countable ∧ forall s in C, s <=ᵐ[sfiniteSeq μ n] (⋃₀ D) :=
    exists_ae_subset_biUnion_countable_of_isFiniteMeasure hC
  choose D DC D_count hD using A
  refine ⟨⋃ n, D n, by simp [DC], by simp [D_count], fun s hs => ?_⟩
  rw [← sum_sfiniteSeq μ]
  apply ae_sum_iff.2 (fun n => (hD n s hs).trans ?_)
  exact LE.le.eventuallyLE (fun x hx => by simp at hx ⊢; grind)

set_option backward.defeqAttrib.useBackward false in
/--
theorem `measure_toMeasurable_inter_of_sum` / 定理 `measure_toMeasurable_inter_of_sum`

English:
theorem measure_toMeasurable_inter_of_sum
  statement: {s : Set α} (hs : MeasurableSet s) {t : Set α}
  proof: by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built for each measure `mₙ` using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- then taking the intersection over `n`.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable (m n) t
    have T : t subseteq ⋂ n, w n := subset_iInter (fun i => subset_toMeasurable (m i) t)
    have M : MeasurableSet (⋂ n, w n) :=
      MeasurableSet.iInter (fun i => measurableSet_toMeasurable (m i) t)
    refine ⟨⋂ n, w n, T, M, fun u hu => ?_⟩
    refine le_antisymm ?_ (by gcongr)
    rw [hμ]; rw [sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i => ?_)
    calc
    m i ((⋂ n, w n) inter u) <= m i (w i inter u) := by gcongr; apply iInter_subset
    _ = m i (t inter u) := measure_toMeasurable_inter hu (hv i)
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

中文:
定理 measure_toMeasurable_inter_of_sum
  结论: {s : 集合 α} (hs : 可测集 s) {t : 集合 α}
  证明: by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built for each measure `mₙ` using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- then taking the intersection over `n`.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable (m n) t
    have T : t subseteq ⋂ n, w n := subset_iInter (fun i => subset_toMeasurable (m i) t)
    have M : MeasurableSet (⋂ n, w n) :=
      MeasurableSet.iInter (fun i => measurableSet_toMeasurable (m i) t)
    refine ⟨⋂ n, w n, T, M, fun u hu => ?_⟩
    refine le_antisymm ?_ (by gcongr)
    rw [hμ]; rw [sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i => ?_)
    calc
    m i ((⋂ n, w n) inter u) <= m i (w i inter u) := by gcongr; apply iInter_subset
    _ = m i (t inter u) := measure_toMeasurable_inter hu (hv i)
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs
-/
theorem measure_toMeasurable_inter_of_sum {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {m : Nat -> Measure α} (hv : forall n, m n t != ∞) (hμ : μ = sum m) :
    μ (toMeasurable μ t inter s) = μ (t inter s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built for each measure `mₙ` using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- then taking the intersection over `n`.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable (m n) t
    have T : t subseteq ⋂ n, w n := subset_iInter (fun i => subset_toMeasurable (m i) t)
    have M : MeasurableSet (⋂ n, w n) :=
      MeasurableSet.iInter (fun i => measurableSet_toMeasurable (m i) t)
    refine ⟨⋂ n, w n, T, M, fun u hu => ?_⟩
    refine le_antisymm ?_ (by gcongr)
    rw [hμ]; rw [sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i => ?_)
    calc
    m i ((⋂ n, w n) inter u) <= m i (w i inter u) := by gcongr; apply iInter_subset
    _ = m i (t inter u) := measure_toMeasurable_inter hu (hv i)
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

/--
theorem `measure_toMeasurable_inter_of_cover` / 定理 `measure_toMeasurable_inter_of_cover`

English:
theorem measure_toMeasurable_inter_of_cover
  statement: {s : Set α} (hs : MeasurableSet s) {t : Set α}
  proof: by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- the desired property passes to the union.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable μ (t inter v n)
    have hw : forall n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_toMeasurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, toMeasurable μ (t inter disjointed w n) with ht'
    have tt' : t subseteq t' :=
      calc
        t subseteq ⋃ n, t inter disjointed w n := by
          rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [inter_iUnion]
          intro x hx
          rcases mem_iUnion.1 (hv hx) with ⟨n, hn⟩
          refine mem_iUnion.2 ⟨n, ?_⟩
          have : x in t inter v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ subseteq ⋃ n, toMeasurable μ (t inter disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => ?_⟩
    apply le_antisymm _ (by gcongr)
    calc
      μ (t' inter u) <= ∑' n, μ (toMeasurable μ (t inter disjointed w n) inter u) := by
        rw [ht']; rw [iUnion_inter]
        exact measure_iUnion_le _
      _ = ∑' n, μ (t inter disjointed w n inter u) := by
        congr 1
        ext1 n
        apply measure_toMeasurable_inter hu
        apply ne_of_lt
        calc
          μ (t inter disjointed w n) <= μ (t inter w n) := by
            gcongr
            exact disjointed_le w n
          _ <= μ (w n) := measure_mono inter_subset_right
          _ < ∞ := hw n
      _ = ∑' n, μ.restrict (t inter u) (disjointed w n) := by
        congr 1
        ext1 n
        rw [restrict_apply]; rw [inter_comm t _]; rw [inter_assoc]
        refine MeasurableSet.disjointed (fun n => ?_) n
        exact measurableSet_toMeasurable _ _
      _ = μ.restrict (t inter u) (⋃ n, disjointed w n) := by
        rw [measure_iUnion]
        · exact disjoint_disjointed _
        · intro i
          refine MeasurableSet.disjointed (fun n => ?_) i
          exact measurableSet_toMeasurable _ _
      _ <= μ.restrict (t inter u) univ := measure_mono (subset_univ _)
      _ = μ (t inter u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

中文:
定理 measure_toMeasurable_inter_of_cover
  结论: {s : 集合 α} (hs : 可测集 s) {t : 集合 α}
  证明: by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- the desired property passes to the union.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable μ (t inter v n)
    have hw : forall n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_toMeasurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, toMeasurable μ (t inter disjointed w n) with ht'
    have tt' : t subseteq t' :=
      calc
        t subseteq ⋃ n, t inter disjointed w n := by
          rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [inter_iUnion]
          intro x hx
          rcases mem_iUnion.1 (hv hx) with ⟨n, hn⟩
          refine mem_iUnion.2 ⟨n, ?_⟩
          have : x in t inter v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ subseteq ⋃ n, toMeasurable μ (t inter disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => ?_⟩
    apply le_antisymm _ (by gcongr)
    calc
      μ (t' inter u) <= ∑' n, μ (toMeasurable μ (t inter disjointed w n) inter u) := by
        rw [ht']; rw [iUnion_inter]
        exact measure_iUnion_le _
      _ = ∑' n, μ (t inter disjointed w n inter u) := by
        congr 1
        ext1 n
        apply measure_toMeasurable_inter hu
        apply ne_of_lt
        calc
          μ (t inter disjointed w n) <= μ (t inter w n) := by
            gcongr
            exact disjointed_le w n
          _ <= μ (w n) := measure_mono inter_subset_right
          _ < ∞ := hw n
      _ = ∑' n, μ.restrict (t inter u) (disjointed w n) := by
        congr 1
        ext1 n
        rw [restrict_apply]; rw [inter_comm t _]; rw [inter_assoc]
        refine MeasurableSet.disjointed (fun n => ?_) n
        exact measurableSet_toMeasurable _ _
      _ = μ.restrict (t inter u) (⋃ n, disjointed w n) := by
        rw [measure_iUnion]
        · exact disjoint_disjointed _
        · intro i
          refine MeasurableSet.disjointed (fun n => ?_) i
          exact measurableSet_toMeasurable _ _
      _ <= μ.restrict (t inter u) univ := measure_mono (subset_univ _)
      _ = μ (t inter u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs
-/
theorem measure_toMeasurable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {v : Nat -> Set α} (hv : t subseteq ⋃ n, v n) (h'v : forall n, μ (t inter v n) != ∞) :
    μ (toMeasurable μ t inter s) = μ (t inter s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- the desired property passes to the union.
  have A : exists t', t' ⊇ t ∧ MeasurableSet t' ∧ forall u, MeasurableSet u -> μ (t' inter u) = μ (t inter u) := by
    let w n := toMeasurable μ (t inter v n)
    have hw : forall n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_toMeasurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, toMeasurable μ (t inter disjointed w n) with ht'
    have tt' : t subseteq t' :=
      calc
        t subseteq ⋃ n, t inter disjointed w n := by
          rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [inter_iUnion]
          intro x hx
          rcases mem_iUnion.1 (hv hx) with ⟨n, hn⟩
          refine mem_iUnion.2 ⟨n, ?_⟩
          have : x in t inter v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ subseteq ⋃ n, toMeasurable μ (t inter disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => ?_⟩
    apply le_antisymm _ (by gcongr)
    calc
      μ (t' inter u) <= ∑' n, μ (toMeasurable μ (t inter disjointed w n) inter u) := by
        rw [ht']; rw [iUnion_inter]
        exact measure_iUnion_le _
      _ = ∑' n, μ (t inter disjointed w n inter u) := by
        congr 1
        ext1 n
        apply measure_toMeasurable_inter hu
        apply ne_of_lt
        calc
          μ (t inter disjointed w n) <= μ (t inter w n) := by
            gcongr
            exact disjointed_le w n
          _ <= μ (w n) := measure_mono inter_subset_right
          _ < ∞ := hw n
      _ = ∑' n, μ.restrict (t inter u) (disjointed w n) := by
        congr 1
        ext1 n
        rw [restrict_apply]; rw [inter_comm t _]; rw [inter_assoc]
        refine MeasurableSet.disjointed (fun n => ?_) n
        exact measurableSet_toMeasurable _ _
      _ = μ.restrict (t inter u) (⋃ n, disjointed w n) := by
        rw [measure_iUnion]
        · exact disjoint_disjointed _
        · intro i
          refine MeasurableSet.disjointed (fun n => ?_) i
          exact measurableSet_toMeasurable _ _
      _ <= μ.restrict (t inter u) univ := measure_mono (subset_univ _)
      _ = μ (t inter u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

/--
theorem `restrict_toMeasurable_of_cover` / 定理 `restrict_toMeasurable_of_cover`

English:
theorem restrict_toMeasurable_of_cover
  statement: {s : Set α} {v : Nat -> Set α} (hv : s subseteq ⋃ n, v n)
  proof: ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]

中文:
定理 restrict_toMeasurable_of_cover
  结论: {s : 集合 α} {v : 自然数 -> 集合 α} (hv : s subseteq ⋃ n, v n)
  证明: ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]

Depends on / 依赖: inter_comm, measure_toMeasurable_inter_of_cover, restrict_apply
-/
theorem restrict_toMeasurable_of_cover {s : Set α} {v : Nat -> Set α} (hv : s subseteq ⋃ n, v n)
    (h'v : forall n, μ (s inter v n) != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]

/--
theorem `measure_toMeasurable_inter_of_sFinite` / 定理 `measure_toMeasurable_inter_of_sFinite`

English:
theorem measure_toMeasurable_inter_of_sFinite
  statement: [SFinite μ] {s : Set α} (hs : MeasurableSet s)
  proof: measure_toMeasurable_inter_of_sum hs (fun _ => measure_ne_top _ t) (sum_sfiniteSeq μ).symm

@[simp]

中文:
定理 measure_toMeasurable_inter_of_sFinite
  结论: [SFinite μ] {s : 集合 α} (hs : 可测集 s)
  证明: measure_toMeasurable_inter_of_sum hs (fun _ => measure_ne_top _ t) (sum_sfiniteSeq μ).symm

@[simp]

Depends on / 依赖: measure_ne_top, measure_toMeasurable_inter_of_sum, sum_sfiniteSeq
-/
theorem measure_toMeasurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s)
    (t : Set α) : μ (toMeasurable μ t inter s) = μ (t inter s) :=
  measure_toMeasurable_inter_of_sum hs (fun _ => measure_ne_top _ t) (sum_sfiniteSeq μ).symm

@[simp]
/--
theorem `restrict_toMeasurable_of_sFinite` / 定理 `restrict_toMeasurable_of_sFinite`

English:
theorem restrict_toMeasurable_of_sFinite
  given: [SFinite μ] (s : Set α)
  proof: ext fun t ht => by
    rw [restrict_apply ht]; rw [inter_comm t]; rw [measure_toMeasurable_inter_of_sFinite ht]; rw [restrict_apply ht]; rw [inter_comm t]

中文:
定理 restrict_toMeasurable_of_sFinite
  条件: [SFinite μ] (s : 集合 α)
  证明: ext fun t ht => by
    rw [restrict_apply ht]; rw [inter_comm t]; rw [measure_toMeasurable_inter_of_sFinite ht]; rw [restrict_apply ht]; rw [inter_comm t]

Depends on / 依赖: inter_comm, measure_toMeasurable_inter_of_sFinite, restrict_apply
-/
theorem restrict_toMeasurable_of_sFinite [SFinite μ] (s : Set α) :
    μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht]; rw [inter_comm t]; rw [measure_toMeasurable_inter_of_sFinite ht]; rw [restrict_apply ht]; rw [inter_comm t]

/--
theorem `iSup_restrict_spanningSets_of_measurableSet` / 定理 `iSup_restrict_spanningSets_of_measurableSet`

English:
theorem iSup_restrict_spanningSets_of_measurableSet
  given: [SigmaFinite μ] (hs : MeasurableSet s)
  proof: calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]

中文:
定理 iSup_restrict_spanningSets_of_measurableSet
  条件: [σ有限 μ] (hs : 可测集 s)
  证明: calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]

Depends on / 依赖: directed_le, iUnion_spanningSets, monotone_spanningSets, restrict, restrict_iUnion_apply_eq_iSup, restrict_univ, spanningSets
-/
theorem iSup_restrict_spanningSets_of_measurableSet [SigmaFinite μ] (hs : MeasurableSet s) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s :=
  calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]

/--
theorem `iSup_restrict_spanningSets` / 定理 `iSup_restrict_spanningSets`

English:
theorem iSup_restrict_spanningSets
  given: [SigmaFinite μ] (s : Set α)
  proof: by
  rw [← measure_toMeasurable s]; rw [← iSup_restrict_spanningSets_of_measurableSet (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurableSet_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurableSet_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurableSet_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

中文:
定理 iSup_restrict_spanningSets
  条件: [σ有限 μ] (s : 集合 α)
  证明: by
  rw [← measure_toMeasurable s]; rw [← iSup_restrict_spanningSets_of_measurableSet (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurableSet_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurableSet_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurableSet_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

Depends on / 依赖: Set.inter_comm, iSup_restrict_spanningSets_of_measurableSet, inter_comm, measurableSet_spanningSets, measurableSet_toMeasurable, measure_toMeasurable, restrict_apply, restrict_toMeasurable_of_sFinite, simp_rw, toMeasurable
-/
theorem iSup_restrict_spanningSets [SigmaFinite μ] (s : Set α) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s := by
  rw [← measure_toMeasurable s]; rw [← iSup_restrict_spanningSets_of_measurableSet (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurableSet_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurableSet_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurableSet_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

/--
theorem `exists_subset_measure_lt_top` / 定理 `exists_subset_measure_lt_top`

English:
theorem exists_subset_measure_lt_top
  statement: [SigmaFinite μ] {r : Real>=0∞} (hs : MeasurableSet s)
  proof: by
  rw [← iSup_restrict_spanningSets]; rw [@lt_iSup_iff _ _ _ r fun i : Nat => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine
    ⟨s inter spanningSets μ n, hs.inter (measurableSet_spanningSets _ _), inter_subset_left, hn, ?_⟩
  exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ _)

中文:
定理 存在_subset_measure_lt_top
  结论: [σ有限 μ] {r : 实数>=0∞} (hs : 可测集 s)
  证明: by
  rw [← iSup_restrict_spanningSets]; rw [@lt_iSup_iff _ _ _ r fun i : Nat => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine
    ⟨s inter spanningSets μ n, hs.inter (measurableSet_spanningSets _ _), inter_subset_left, hn, ?_⟩
  exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ _)

Depends on / 依赖: hs.inter, iSup_restrict_spanningSets, inter_subset_left, inter_subset_right, lt_iSup_iff, measurableSet_spanningSets, measure_mono, measure_spanningSets_lt_top, restrict, restrict_apply, spanningSets, trans_lt
-/
theorem exists_subset_measure_lt_top [SigmaFinite μ] {r : Real>=0∞} (hs : MeasurableSet s)
    (h's : r < μ s) : exists t, MeasurableSet t ∧ t subseteq s ∧ r < μ t ∧ μ t < ∞ := by
  rw [← iSup_restrict_spanningSets]; rw [@lt_iSup_iff _ _ _ r fun i : Nat => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine
    ⟨s inter spanningSets μ n, hs.inter (measurableSet_spanningSets _ _), inter_subset_left, hn, ?_⟩
  exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ _)

namespace FiniteSpanningSetsIn

variable {C D : Set (Set α)}

/--
Definition of `mono'` / `mono'` 的定义

English:
definition mono'
  signature: (h : μ.FiniteSpanningSetsIn C) (hC : C inter { s | μ s < ∞ } subseteq D)
  body: ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

中文:
定义 mono'
  签名: (h : μ.FiniteSpanningSetsIn C) (hC : C inter { s | μ s < ∞ } subseteq D)
  定义体: ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩
-/
protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C inter { s | μ s < ∞ } subseteq D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

/--
Definition of `mono` / `mono` 的定义

English:
definition mono
  signature: (h : μ.FiniteSpanningSetsIn C) (hC : C subseteq D)
  body: h.mono' fun _s hs => hC hs.1

中文:
定义 mono
  签名: (h : μ.FiniteSpanningSetsIn C) (hC : C subseteq D)
  定义体: h.mono' fun _s hs => hC hs.1
-/
protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C subseteq D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun _s hs => hC hs.1

/--
theorem `sigmaFinite` / 定理 `sigmaFinite`

English:
theorem sigmaFinite
  given: (h : μ.FiniteSpanningSetsIn C)
  statement: SigmaFinite μ
  proof: ⟨⟨h.mono subset_univ C⟩⟩

中文:
定理 sigmaFinite
  条件: (h : μ.FiniteSpanningSetsIn C)
  结论: σ有限 μ
  证明: ⟨⟨h.mono subset_univ C⟩⟩
-/
protected theorem sigmaFinite (h : μ.FiniteSpanningSetsIn C) : SigmaFinite μ :=
⟨⟨h.mono subset_univ C⟩⟩

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
  proof: ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq

中文:
定理 ext
  结论: {ν : 测度 α} {C : 集合 (集合 α)} (hA : ‹_› = generateFrom C)
  证明: ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq
-/
protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h : μ.FiniteSpanningSetsIn C) (h_eq : forall s in C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq

/--
theorem `isCountablySpanning` / 定理 `isCountablySpanning`

English:
theorem isCountablySpanning
  given: (h : μ.FiniteSpanningSetsIn C)
  statement: IsCountablySpanning C
  proof: ⟨h.set, h.set_mem, h.spanning⟩

中文:
定理 isCountablySpanning
  条件: (h : μ.FiniteSpanningSetsIn C)
  结论: IsCountablySpanning C
  证明: ⟨h.set, h.set_mem, h.spanning⟩
-/
protected theorem isCountablySpanning (h : μ.FiniteSpanningSetsIn C) : IsCountablySpanning C :=
  ⟨h.set, h.set_mem, h.spanning⟩

end FiniteSpanningSetsIn

/--
theorem `sigmaFinite_of_countable` / 定理 `sigmaFinite_of_countable`

English:
theorem sigmaFinite_of_countable
  statement: {S : Set (Set α)} (hc : S.Countable) (hμ : forall s in S, μ s < ∞)
  proof: by
  obtain ⟨s, hμ, hs⟩ : exists s : Nat -> Set α, (forall n, μ (s n) < ∞) ∧ ⋃ n, s n = univ :=
    (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩

中文:
定理 sigmaFinite_of_countable
  结论: {S : 集合 (集合 α)} (hc : S.可数) (hμ : 对任意 s in S, μ s < ∞)
  证明: by
  obtain ⟨s, hμ, hs⟩ : exists s : Nat -> Set α, (forall n, μ (s n) < ∞) ∧ ⋃ n, s n = univ :=
    (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩

Depends on / 依赖: exists_seq_cover_iff_countable
-/
theorem sigmaFinite_of_countable {S : Set (Set α)} (hc : S.Countable) (hμ : forall s in S, μ s < ∞)
    (hU : ⋃₀ S = univ) : SigmaFinite μ := by
  obtain ⟨s, hμ, hs⟩ : exists s : Nat -> Set α, (forall n, μ (s n) < ∞) ∧ ⋃ n, s n = univ :=
    (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩

/--
Definition of `FiniteSpanningSetsIn.ofLE` / `FiniteSpanningSetsIn.ofLE` 的定义

English:
definition FiniteSpanningSetsIn.ofLE
  signature: (h : ν <= μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C)
  body: S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning

中文:
定义 FiniteSpanningSetsIn.ofLE
  签名: (h : ν <= μ) {C : 集合 (集合 α)} (S : μ.FiniteSpanningSetsIn C)
  定义体: S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning

Depends on / 依赖: S.set
-/
def FiniteSpanningSetsIn.ofLE (h : ν <= μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  set := S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning

/--
theorem `sigmaFinite_of_le` / 定理 `sigmaFinite_of_le`

English:
theorem sigmaFinite_of_le
  given: (μ : Measure α) [hs : SigmaFinite μ] (h : ν <= μ)
  statement: SigmaFinite ν
  proof: ⟨hs.out.map FiniteSpanningSetsIn.ofLE h⟩

中文:
定理 sigmaFinite_of_le
  条件: (μ : 测度 α) [hs : σ有限 μ] (h : ν <= μ)
  结论: σ有限 ν
  证明: ⟨hs.out.map FiniteSpanningSetsIn.ofLE h⟩

Depends on / 依赖: FiniteSpanningSetsIn, FiniteSpanningSetsIn.ofLE, hs.out.map
-/
theorem sigmaFinite_of_le (μ : Measure α) [hs : SigmaFinite μ] (h : ν <= μ) : SigmaFinite ν :=
⟨hs.out.map FiniteSpanningSetsIn.ofLE h⟩

/--
lemma `add_right_inj` / 引理 `add_right_inj`

English:
lemma add_right_inj
  given: (μ ν₁ ν₂ : Measure α) [SigmaFinite μ]
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono s.inter_subset_right |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', coe_add, Pi.add_apply] at h
  simp [hs, h]

中文:
引理 add_right_inj
  条件: (μ ν₁ ν₂ : 测度 α) [σ有限 μ]
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono s.inter_subset_right |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', coe_add, Pi.add_apply] at h
  simp [hs, h]
-/
@[simp] lemma add_right_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono s.inter_subset_right |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', coe_add, Pi.add_apply] at h
  simp [hs, h]

/--
lemma `add_left_inj` / 引理 `add_left_inj`

English:
lemma add_left_inj
  given: (μ ν₁ ν₂ : Measure α) [SigmaFinite μ]
  proof: by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]

中文:
引理 add_left_inj
  条件: (μ ν₁ ν₂ : 测度 α) [σ有限 μ]
  证明: by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]
-/
@[simp] lemma add_left_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    ν₁ + μ = ν₂ + μ ↔ ν₁ = ν₂ := by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]

end Measure

/-- Every finite measure is σ-finite. -/
instance (priority := 100) IsFiniteMeasure.toSigmaFinite {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] : SigmaFinite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivial, fun _ => measure_lt_top μ _, iUnion_const _⟩⟩⟩

/--
lemma `Measure.sigmaFinite_iff_measure_singleton_lt_top` / 引理 `Measure.sigmaFinite_iff_measure_singleton_lt_top`

English:
lemma Measure.sigmaFinite_iff_measure_singleton_lt_top
  given: [Countable α]
  proof: measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n => {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩

中文:
引理 测度.sigmaFinite_iff_measure_singleton_lt_top
  条件: [可数 α]
  证明: measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n => {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩

Depends on / 依赖: measure_singleton_lt_top
-/
lemma Measure.sigmaFinite_iff_measure_singleton_lt_top [Countable α] :
    SigmaFinite μ ↔ forall a, μ {a} < ∞ where
  mp _ a := measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n => {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩

/--
theorem `sigmaFinite_bot_iff` / 定理 `sigmaFinite_bot_iff`

English:
theorem sigmaFinite_bot_iff
  given: (μ : @Measure α ⊥)
  statement: SigmaFinite μ ↔ IsFiniteMeasure μ
  proof: by
  refine ⟨fun h => ⟨?_⟩, fun h => by infer_instance⟩
  have : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : forall i, MeasurableSet[⊥] (s i) := measurableSet_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, measure_empty]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : exists i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : forall i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i

中文:
定理 sigmaFinite_bot_iff
  条件: (μ : @测度 α ⊥)
  结论: σ有限 μ ↔ 是有限测度 μ
  证明: by
  refine ⟨fun h => ⟨?_⟩, fun h => by infer_instance⟩
  have : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : forall i, MeasurableSet[⊥] (s i) := measurableSet_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, measure_empty]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : exists i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : forall i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top.lt_top, MeasurableSet, MeasurableSpace, MeasurableSpace.measurableSet_bot_iff, Set.univ, SigmaFinite, h_empt, h_not_univ, h_univ_empty, hs_meas, hs_univ, iUnion_spanningSets, infer_instance, lt_top, measurableSet_bot_iff, measurableSet_spanningSets, measure_empty, simp_rw, spanningSets
-/
theorem sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ := by
  refine ⟨fun h => ⟨?_⟩, fun h => by infer_instance⟩
  have : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : forall i, MeasurableSet[⊥] (s i) := measurableSet_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, measure_empty]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : exists i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : forall i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i

/--
Instance `Restrict.sigmaFinite` / 实例 `Restrict.sigmaFinite`

English:
instance Restrict.sigmaFinite
  signature: (μ : Measure α) [SigmaFinite μ] (s : Set α)
  body: by
  refine ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurableSet_spanningSets μ i)]
  exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ i)

中文:
实例 Restrict.sigmaFinite
  签名: (μ : 测度 α) [σ有限 μ] (s : 集合 α)
  定义体: by
  refine ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurableSet_spanningSets μ i)]
  exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ i)

Depends on / 依赖: Measure, Measure.restrict_apply, iUnion_spanningSets, inter_subset_left, measurableSet_spanningSets, measure_mono, measure_spanningSets_lt_top, restrict_apply, spanningSets, trans_lt
-/
instance Restrict.sigmaFinite (μ : Measure α) [SigmaFinite μ] (s : Set α) :
    SigmaFinite (μ.restrict s) := by
  refine ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurableSet_spanningSets μ i)]
  exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ i)

/--
Instance `sum.sigmaFinite` / 实例 `sum.sigmaFinite`

English:
instance sum.sigmaFinite
  signature: {ι} [Finite ι] (μ : ι -> Measure α) [forall i, SigmaFinite (μ i)]
  body: by
  cases nonempty_fintype ι
  have : forall n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurableSet_spanningSets (μ i) n
  refine ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    · simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)

中文:
实例 求和.sigmaFinite
  签名: {ι} [有限 ι] (μ : ι -> 测度 α) [对任意 i, σ有限 (μ i)]
  定义体: by
  cases nonempty_fintype ι
  have : forall n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurableSet_spanningSets (μ i) n
  refine ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    · simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)

Depends on / 依赖: ENNReal, ENNReal.sum_lt_top, MeasurableSet, MeasurableSet.iInter, iInter, iInter_subset, iInter_univ, iUnion_iInter_of_monotone, iUnion_spanningSets, measurableSet_spanningSets, measure_mono, measure_spanningSets_lt_top, nonempty_fintype, simp_rw, spanningSets, sum_apply, sum_lt_top, trans_lt, tsum_fintype
-/
instance sum.sigmaFinite {ι} [Finite ι] (μ : ι -> Measure α) [forall i, SigmaFinite (μ i)] :
    SigmaFinite (sum μ) := by
  cases nonempty_fintype ι
  have : forall n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurableSet_spanningSets (μ i) n
  refine ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    · simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)

/--
Instance `Add.sigmaFinite` / 实例 `Add.sigmaFinite`

English:
instance Add.sigmaFinite
  signature: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  body: by
  rw [← sum_cond]
  refine @sum.sigmaFinite _ _ _ _ _ (Bool.rec ?_ ?_) <;> simpa

中文:
实例 加法.sigmaFinite
  签名: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  定义体: by
  rw [← sum_cond]
  refine @sum.sigmaFinite _ _ _ _ _ (Bool.rec ?_ ?_) <;> simpa

Depends on / 依赖: Bool.rec, sigmaFinite, sum.sigmaFinite, sum_cond
-/
instance Add.sigmaFinite (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (μ + ν) := by
  rw [← sum_cond]
  refine @sum.sigmaFinite _ _ _ _ _ (Bool.rec ?_ ?_) <;> simpa

/--
Instance `SMul.sigmaFinite` / 实例 `SMul.sigmaFinite`

English:
instance SMul.sigmaFinite
  signature: {μ : Measure α} [SigmaFinite μ] (c : Real>=0)
  body: ⟨{ set := spanningSets μ
      set_mem := fun _ => trivial
      finite := by
        intro i
        simp only [Measure.coe_smul, Pi.smul_apply, nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top μ i)
      spanning := iUnion_spanningSets μ }⟩

中文:
实例 标量乘法.sigmaFinite
  签名: {μ : 测度 α} [σ有限 μ] (c : 实数>=0)
  定义体: ⟨{ set := spanningSets μ
      set_mem := fun _ => trivial
      finite := by
        intro i
        simp only [Measure.coe_smul, Pi.smul_apply, nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top μ i)
      spanning := iUnion_spanningSets μ }⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, Measure, Measure.coe_smul, Pi.smul_apply, coe_lt_top, coe_smul, finite, iUnion_spanningSets, measure_spanningSets_lt_top, mul_lt_top, nnreal_smul_coe_apply, set_mem, smul_apply, spanning, spanningSets
-/
instance SMul.sigmaFinite {μ : Measure α} [SigmaFinite μ] (c : Real>=0) :
    MeasureTheory.SigmaFinite (c • μ) where
  out' :=
  ⟨{ set := spanningSets μ
      set_mem := fun _ => trivial
      finite := by
        intro i
        simp only [Measure.coe_smul, Pi.smul_apply, nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top μ i)
      spanning := iUnion_spanningSets μ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaFinite
  signature: (μ.restrict s)] [SigmaFinite (μ.restrict t)] :
  body: sigmaFinite_of_le _ (restrict_union_le _ _)

中文:
实例 [σ有限
  签名: (μ.restrict s)] [σ有限 (μ.restrict t)] :
  定义体: sigmaFinite_of_le _ (restrict_union_le _ _)

Depends on / 依赖: restrict_union_le, sigmaFinite_of_le
-/
instance [SigmaFinite (μ.restrict s)] [SigmaFinite (μ.restrict t)] :
    SigmaFinite (μ.restrict (s union t)) := sigmaFinite_of_le _ (restrict_union_le _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaFinite
  signature: (μ.restrict s)] : SigmaFinite (μ.restrict (s inter t))
  body: sigmaFinite_of_le (μ.restrict s) (restrict_mono_ae (ae_of_all _ Set.inter_subset_left))

中文:
实例 [σ有限
  签名: (μ.restrict s)] : σ有限 (μ.restrict (s inter t))
  定义体: sigmaFinite_of_le (μ.restrict s) (restrict_mono_ae (ae_of_all _ Set.inter_subset_left))

Depends on / 依赖: Set.inter_subset_left, ae_of_all, inter_subset_left, restrict, restrict_mono_ae, sigmaFinite_of_le
-/
instance [SigmaFinite (μ.restrict s)] : SigmaFinite (μ.restrict (s inter t)) :=
  sigmaFinite_of_le (μ.restrict s) (restrict_mono_ae (ae_of_all _ Set.inter_subset_left))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaFinite
  signature: (μ.restrict t)] : SigmaFinite (μ.restrict (s inter t))
  body: sigmaFinite_of_le (μ.restrict t) (restrict_mono_ae (ae_of_all _ Set.inter_subset_right))

中文:
实例 [σ有限
  签名: (μ.restrict t)] : σ有限 (μ.restrict (s inter t))
  定义体: sigmaFinite_of_le (μ.restrict t) (restrict_mono_ae (ae_of_all _ Set.inter_subset_right))

Depends on / 依赖: Set.inter_subset_right, ae_of_all, inter_subset_right, restrict, restrict_mono_ae, sigmaFinite_of_le
-/
instance [SigmaFinite (μ.restrict t)] : SigmaFinite (μ.restrict (s inter t)) :=
  sigmaFinite_of_le (μ.restrict t) (restrict_mono_ae (ae_of_all _ Set.inter_subset_right))

/--
theorem `SigmaFinite.of_map` / 定理 `SigmaFinite.of_map`

English:
theorem SigmaFinite.of_map
  statement: (μ : Measure α) {f : α -> β} (hf : AEMeasurable f μ)
  proof: ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurableSet_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩

中文:
定理 σ有限.of_map
  结论: (μ : 测度 α) {f : α -> β} (hf : 几乎处处可测 f μ)
  证明: ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurableSet_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩

Depends on / 依赖: iUnion_spanningSets, map_apply_of_aemeasurable, measurableSet_spanningSets, measure_spanningSets_lt_top, preimage_iUnion, preimage_univ, spanningSets
-/
theorem SigmaFinite.of_map (μ : Measure α) {f : α -> β} (hf : AEMeasurable f μ)
    (h : SigmaFinite (μ.map f)) : SigmaFinite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurableSet_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩

/--
lemma `_root_.MeasurableEmbedding.sigmaFinite_map` / 引理 `_root_.MeasurableEmbedding.sigmaFinite_map`

English:
lemma _root_.MeasurableEmbedding.sigmaFinite_map
  statement: {f : α -> β} (hf : MeasurableEmbedding f)
  proof: by
  refine ⟨fun n => f '' (spanningSets μ n) union (Set.range f)ᶜ, by simp, fun n => ?_, ?_⟩
  · rw [hf.map_apply, Set.preimage_union]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ, Set.union_empty,
      Set.preimage_image_eq _ hf.injective]
    exact measure_spanningSets_lt_top μ n
  · rw [← Set.iUnion_union, ← Set.image_iUnion, iUnion_spanningSets,
      Set.image_univ, Set.union_compl_self]

中文:
引理 _root_.可测嵌入.sigmaFinite_map
  结论: {f : α -> β} (hf : 可测嵌入 f)
  证明: by
  refine ⟨fun n => f '' (spanningSets μ n) union (Set.range f)ᶜ, by simp, fun n => ?_, ?_⟩
  · rw [hf.map_apply, Set.preimage_union]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ, Set.union_empty,
      Set.preimage_image_eq _ hf.injective]
    exact measure_spanningSets_lt_top μ n
  · rw [← Set.iUnion_union, ← Set.image_iUnion, iUnion_spanningSets,
      Set.image_univ, Set.union_compl_self]

Depends on / 依赖: Set.compl_univ, Set.iUnion_union, Set.image_iUnion, Set.image_univ, Set.preimage_compl, Set.preimage_image_eq, Set.preimage_range, Set.preimage_union, Set.range, Set.union_compl_self, Set.union_empty, compl_univ, hf.injective, hf.map_apply, iUnion_spanningSets, iUnion_union, image_iUnion, image_univ, injective, map_apply
-/
lemma _root_.MeasurableEmbedding.sigmaFinite_map {f : α -> β} (hf : MeasurableEmbedding f)
    [SigmaFinite μ] :
    SigmaFinite (μ.map f) := by
  refine ⟨fun n => f '' (spanningSets μ n) union (Set.range f)ᶜ, by simp, fun n => ?_, ?_⟩
  · rw [hf.map_apply, Set.preimage_union]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ, Set.union_empty,
      Set.preimage_image_eq _ hf.injective]
    exact measure_spanningSets_lt_top μ n
  · rw [← Set.iUnion_union, ← Set.image_iUnion, iUnion_spanningSets,
      Set.image_univ, Set.union_compl_self]

/--
theorem `_root_.MeasurableEquiv.sigmaFinite_map` / 定理 `_root_.MeasurableEquiv.sigmaFinite_map`

English:
theorem _root_.MeasurableEquiv.sigmaFinite_map
  given: (f : α ≃ᵐ β) [SigmaFinite μ]
  proof: f.measurableEmbedding.sigmaFinite_map

中文:
定理 _root_.可测等价.sigmaFinite_map
  条件: (f : α ≃ᵐ β) [σ有限 μ]
  证明: f.measurableEmbedding.sigmaFinite_map

Depends on / 依赖: f.measurableEmbedding.sigmaFinite_map, measurableEmbedding, sigmaFinite_map
-/
theorem _root_.MeasurableEquiv.sigmaFinite_map (f : α ≃ᵐ β) [SigmaFinite μ] :
    SigmaFinite (μ.map f) := f.measurableEmbedding.sigmaFinite_map

/--
theorem `ae_of_forall_measure_lt_top_ae_restrict'` / 定理 `ae_of_forall_measure_lt_top_ae_restrict'`

English:
theorem ae_of_forall_measure_lt_top_ae_restrict'
  statement: {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
  proof: by
  have : forall n, forallᵐ x ∂μ, x in spanningSets (μ + ν) n -> P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurableSet_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurableSet_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)

中文:
定理 ae_of_对任意_measure_lt_top_ae_restrict'
  结论: {μ : 测度 α} (ν : 测度 α) [σ有限 μ]
  证明: by
  have : forall n, forallᵐ x ∂μ, x in spanningSets (μ + ν) n -> P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurableSet_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurableSet_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)

Depends on / 依赖: ae_all_iff, ae_restrict_iff, filter_upwards, measurableSet_spanningSets, measure_spanningSets_lt_top, mem_spanningSetsIndex, self_le_add_left, self_le_add_right, spanningSets, trans_lt
-/
theorem ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (P : α -> Prop)
    (h : forall s, MeasurableSet s -> μ s < ∞ -> ν s < ∞ -> forallᵐ x ∂μ.restrict s, P x) : forallᵐ x ∂μ, P x := by
  have : forall n, forallᵐ x ∂μ, x in spanningSets (μ + ν) n -> P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurableSet_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurableSet_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)

/--
theorem `ae_of_forall_measure_lt_top_ae_restrict` / 定理 `ae_of_forall_measure_lt_top_ae_restrict`

English:
theorem ae_of_forall_measure_lt_top_ae_restrict
  statement: {μ : Measure α} [SigmaFinite μ] (P : α -> Prop)
  proof: ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s

中文:
定理 ae_of_对任意_measure_lt_top_ae_restrict
  结论: {μ : 测度 α} [σ有限 μ] (P : α -> 命题)
  证明: ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s

Depends on / 依赖: ae_of_forall_measure_lt_top_ae_restrict
-/
theorem ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α -> Prop)
    (h : forall s, MeasurableSet s -> μ s < ∞ -> forallᵐ x ∂μ.restrict s, P x) : forallᵐ x ∂μ, P x :=
  ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s

instance (priority := 100) SigmaFinite.of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [SigmaCompactSpace α] (μ : Measure α) [IsFiniteMeasureOnCompacts μ] : SigmaFinite μ :=
  ⟨⟨{ set := compactCovering α
        set_mem := fun _ => trivial
        finite := fun n => (isCompact_compactCovering α n).measure_lt_top
        spanning := iUnion_compactCovering α }⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) sigmaFinite_of_locallyFinite [TopologicalSpace α]
    [SecondCountableTopology α] [IsLocallyFiniteMeasure μ] : SigmaFinite μ := by
  choose s hsx hsμ using μ.finiteAt_nhds
  rcases TopologicalSpace.countable_cover_nhds hsx with ⟨t, htc, htU⟩
  refine Measure.sigmaFinite_of_countable (htc.image s) (forall_mem_image.2 fun x _ => hsμ x) ?_
  rwa [sUnion_image]

namespace Measure

section disjointed

/--
Definition of `FiniteSpanningSetsIn.disjointed` / `FiniteSpanningSetsIn.disjointed` 的定义

English:
definition FiniteSpanningSetsIn.disjointed
  signature: {μ : Measure α}
  body: ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩

中文:
定义 FiniteSpanningSetsIn.disjointed
  签名: {μ : 测度 α}
  定义体: ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩
-/
protected def FiniteSpanningSetsIn.disjointed {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } :=
  ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩

/--
theorem `FiniteSpanningSetsIn.disjointed_set_eq` / 定理 `FiniteSpanningSetsIn.disjointed_set_eq`

English:
theorem FiniteSpanningSetsIn.disjointed_set_eq
  statement: {μ : Measure α}
  proof: rfl

中文:
定理 FiniteSpanningSetsIn.disjointed_set_eq
  结论: {μ : 测度 α}
  证明: rfl
-/
theorem FiniteSpanningSetsIn.disjointed_set_eq {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) : S.disjointed.set = disjointed S.set :=
  rfl

/--
theorem `exists_eq_disjoint_finiteSpanningSetsIn` / 定理 `exists_eq_disjoint_finiteSpanningSetsIn`

English:
theorem exists_eq_disjoint_finiteSpanningSetsIn
  given: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩

中文:
定理 存在_eq_disjoint_finiteSpanningSetsIn
  条件: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩

Depends on / 依赖: Measure, Measure.le_add_left, Measure.le_add_right, S.ofLE, disjoint_disjointed, disjointed, le_add_left, le_add_right, le_rfl, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.disjointed
-/
theorem exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    exists (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s })
      (T : ν.FiniteSpanningSetsIn { s | MeasurableSet s }),
      S.set = T.set ∧ Pairwise (Disjoint on S.set) :=
  let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩

end disjointed

end Measure

end MeasureTheory
