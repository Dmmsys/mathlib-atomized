/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Additivity on measurable sets with finite measure

Let `T : Set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`Set α × E`, or a linear map on indicator functions.

This property is named `FinMeasAdditive` in this file. We also define `DominatedFinMeasAdditive`,
which requires in addition that the norm on every set is less than the measure of the set
(up to a multiplicative constant); in `Mathlib/MeasureTheory/Integral/SetToL1.lean` we extend
set functions with this stronger property to integrable (L1) functions.

## Main definitions

- `FinMeasAdditive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`.
- `DominatedFinMeasAdditive μ T C`: `FinMeasAdditive μ T ∧ ∀ s, ‖T s‖ ≤ C * μ.real s`.
  This is the property needed to perform the extension from indicators to L1.

## Implementation notes

The starting object `T : Set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/

@[expose] public section


noncomputable section

open Set Filter ENNReal Finset

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup F'] [NormedSpace Real F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " ->ₛ " => SimpleFunc

section FinMeasAdditive

/--
Definition of `FinMeasAdditive` / `FinMeasAdditive` 的定义

English:
definition FinMeasAdditive
  signature: {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α -> β)
  body: forall s t, MeasurableSet s -> MeasurableSet t -> μ s != ∞ -> μ t != ∞ -> Disjoint s t ->
    T (s union t) = T s + T t

中文:
定义 FinMeasAdditive
  签名: {β} [加法幺半群 β] {_ : 可测空间 α} (μ : 测度 α) (T : 集合 α -> β)
  定义体: forall s t, MeasurableSet s -> MeasurableSet t -> μ s != ∞ -> μ t != ∞ -> Disjoint s t ->
    T (s union t) = T s + T t

Depends on / 依赖: Disjoint, MeasurableSet
-/
def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α -> β) :
    Prop :=
  forall s t, MeasurableSet s -> MeasurableSet t -> μ s != ∞ -> μ t != ∞ -> Disjoint s t ->
    T (s union t) = T s + T t

namespace FinMeasAdditive

variable {β : Type*} {T T' : Set α -> β}

section AddMonoid

variable [AddMonoid β]

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: FinMeasAdditive μ (0 : Set α -> β)
  proof: fun _ _ _ _ _ _ _ => by simp

中文:
定理 zero
  结论: FinMeasAdditive μ (0 : 集合 α -> β)
  证明: fun _ _ _ _ _ _ _ => by simp
-/
theorem zero : FinMeasAdditive μ (0 : Set α -> β) := fun _ _ _ _ _ _ _ => by simp

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜)
  proof: fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]

中文:
定理 smul
  条件: [分配标量乘法 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜)
  证明: fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]
-/
theorem smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]

/--
theorem `of_eq_top_imp_eq_top` / 定理 `of_eq_top_imp_eq_top`

English:
theorem of_eq_top_imp_eq_top
  statement: {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞)
  proof: fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst

中文:
定理 of_eq_top_imp_eq_top
  结论: {μ' : 测度 α} (h : 对任意 s, 可测集 s -> μ s = ∞ -> μ' s = ∞)
  证明: fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst
-/
theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : forall s, MeasurableSet s -> μ s = ∞ -> μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst

/--
theorem `add_right_measure` / 定理 `add_right_measure`

English:
theorem add_right_measure
  given: {ν : Measure α} (hT : FinMeasAdditive μ T)
  proof: hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_right le_rfl s)

中文:
定理 add_right_measure
  条件: {ν : 测度 α} (hT : FinMeasAdditive μ T)
  证明: hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_right le_rfl s)

Depends on / 依赖: Measure, Measure.le_add_right, hT.of_eq_top_imp_eq_top, le_add_right, le_rfl, of_eq_top_imp_eq_top, s.symm.trans_le, top_unique, trans_le
-/
theorem add_right_measure {ν : Measure α} (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (μ + ν) T :=
  hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_right le_rfl s)

/--
theorem `add_left_measure` / 定理 `add_left_measure`

English:
theorem add_left_measure
  given: {ν : Measure α} (hT : FinMeasAdditive μ T)
  proof: hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_left le_rfl s)

中文:
定理 add_left_measure
  条件: {ν : 测度 α} (hT : FinMeasAdditive μ T)
  证明: hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_left le_rfl s)

Depends on / 依赖: Measure, Measure.le_add_left, hT.of_eq_top_imp_eq_top, le_add_left, le_rfl, ofSubsingleton, of_eq_top_imp_eq_top, s.symm.trans_le, top_unique, trans_le
-/
theorem add_left_measure {ν : Measure α} (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (ν + μ) T :=
  hT.of_eq_top_imp_eq_top fun s _ hμs =>
top_unique hμs.symm.trans_le (Measure.le_add_left le_rfl s)

/--
theorem `of_smul_measure` / 定理 `of_smul_measure`

English:
theorem of_smul_measure
  given: {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : FinMeasAdditive (c • μ) T)
  proof: by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2

中文:
定理 of_smul_measure
  条件: {c : 实数>=0∞} (hc_ne_top : c != ∞) (hT : FinMeasAdditive (c • μ) T)
  证明: by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, Measure, Measure.smul_apply, false_and, hc_ne_top, mul_eq_top, of_eq_top_imp_eq_top, or_false, smul_apply, smul_eq_mul
-/
theorem of_smul_measure {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  given: (c : Real>=0∞) (hc_ne_zero : c != 0) (hT : FinMeasAdditive μ T)
  proof: by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top]
  simp only [hc_ne_zero, true_and, Ne, not_false_iff]
  exact Or.inl hμs

中文:
定理 smul_measure
  条件: (c : 实数>=0∞) (hc_ne_zero : c != 0) (hT : FinMeasAdditive μ T)
  证明: by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top]
  simp only [hc_ne_zero, true_and, Ne, not_false_iff]
  exact Or.inl hμs

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, Measure, Measure.smul_apply, Or.inl, hc_ne_zero, mul_eq_top, not_false_iff, of_eq_top_imp_eq_top, smul_apply, smul_eq_mul, true_and
-/
theorem smul_measure (c : Real>=0∞) (hc_ne_zero : c != 0) (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (c • μ) T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [ENNReal.mul_eq_top]
  simp only [hc_ne_zero, true_and, Ne, not_false_iff]
  exact Or.inl hμs

/--
theorem `smul_measure_iff` / 定理 `smul_measure_iff`

English:
theorem smul_measure_iff
  given: (c : Real>=0∞) (hc_ne_zero : c != 0) (hc_ne_top : c != ∞)
  proof: ⟨fun hT => of_smul_measure hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩

中文:
定理 smul_measure_iff
  条件: (c : 实数>=0∞) (hc_ne_zero : c != 0) (hc_ne_top : c != ∞)
  证明: ⟨fun hT => of_smul_measure hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩

Depends on / 依赖: hc_ne_top, hc_ne_zero, of_smul_measure, smul_measure
-/
theorem smul_measure_iff (c : Real>=0∞) (hc_ne_zero : c != 0) (hc_ne_top : c != ∞) :
    FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T :=
  ⟨fun hT => of_smul_measure hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩

/--
theorem `map_empty_eq_zero` / 定理 `map_empty_eq_zero`

English:
theorem map_empty_eq_zero
  given: {β} [AddCancelMonoid β] {T : Set α -> β} (hT : FinMeasAdditive μ T)
  proof: by
  have h_empty : μ ∅ != ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

中文:
定理 map_empty_eq_zero
  条件: {β} [加法消去幺半群 β] {T : 集合 α -> β} (hT : FinMeasAdditive μ T)
  证明: by
  have h_empty : μ ∅ != ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, MeasurableSet, MeasurableSet.empty, Set.union_empty, add_left_cancel, add_zero, coe_lt_top, disjoint_empty, h_empty, measure_empty, measure_empty.le.trans_lt, nth_rw, specialize, trans_lt, union_empty
-/
theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α -> β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 := by
  have h_empty : μ ∅ != ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid β]

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T')
  proof: by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel

中文:
定理 add
  条件: (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T')
  证明: by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply
-/
theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T + T') := by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel

/--
theorem `add_measure` / 定理 `add_measure`

English:
theorem add_measure
  given: {ν : Measure α} (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive ν T')
  proof: hT.add_right_measure.add (hT'.add_left_measure)

中文:
定理 add_measure
  条件: {ν : 测度 α} (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive ν T')
  证明: hT.add_right_measure.add (hT'.add_left_measure)

Depends on / 依赖: add_left_measure, add_right_measure, hT.add_right_measure.add
-/
theorem add_measure {ν : Measure α} (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive ν T') :
    FinMeasAdditive (μ + ν) (T + T') :=
  hT.add_right_measure.add (hT'.add_left_measure)

/--
theorem `map_iUnion_fin_meas_set_eq_sum` / 定理 `map_iUnion_fin_meas_set_eq_sum`

English:
theorem map_iUnion_fin_meas_set_eq_sum
  statement: (T : Set α -> β) (T_empty : T ∅ = 0)
  proof: by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has]; rw [← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i in s]; rw [S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert! Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi =>
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai => ?_
    rw [← hai] at hi
    exact has hi

中文:
定理 map_iUnion_fin_meas_set_eq_sum
  结论: (T : 集合 α -> β) (T_empty : T ∅ = 0)
  证明: by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has]; rw [← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i in s]; rw [S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert! Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi =>
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai => ?_
    rw [← hai] at hi
    exact has hi

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.notMem_empty, Finset.sum_insert, IsEmpty, IsEmpty.forall_iff, T_empty, classical, forall_iff, hS_meas, h_add, h_disj, iUnion_empty, iUnion_false, imp_true_iff, induction_on, measurableSet_biUnion, mem_insert_of_mem, notMem_empty
-/
theorem map_iUnion_fin_meas_set_eq_sum (T : Set α -> β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι -> Set α) (sι : Finset ι)
    (hS_meas : forall i, MeasurableSet (S i)) (hSp : forall i in sι, μ (S i) != ∞)
    (h_disj : forallᵉ (i in sι) (j in sι), i != j -> Disjoint (S i) (S j)) :
    T (⋃ i in sι, S i) = ∑ i in sι, T (S i) := by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has]; rw [← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i in s]; rw [S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert! Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi =>
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai => ?_
    rw [← hai] at hi
    exact has hi

end AddCommMonoid

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: [AddGroup β] (hT : FinMeasAdditive μ T)
  proof: by
  intro s t hs ht hμs hμt hst
  have h_comm : T s + T t = T t + T s := by
    rw [← hT s t hs ht hμs hμt hst]; rw [← hT t s ht hs hμt hμs hst.symm]; rw [union_comm]
  simp_all [hT s t hs ht hμs hμt hst, neg_add_rev]

中文:
定理 neg
  条件: [加法群 β] (hT : FinMeasAdditive μ T)
  证明: by
  intro s t hs ht hμs hμt hst
  have h_comm : T s + T t = T t + T s := by
    rw [← hT s t hs ht hμs hμt hst]; rw [← hT t s ht hs hμt hμs hst.symm]; rw [union_comm]
  simp_all [hT s t hs ht hμs hμt hst, neg_add_rev]

Depends on / 依赖: h_comm, hst.symm, neg_add_rev, union_comm
-/
theorem neg [AddGroup β] (hT : FinMeasAdditive μ T) :
    FinMeasAdditive μ (-T) := by
  intro s t hs ht hμs hμt hst
  have h_comm : T s + T t = T t + T s := by
    rw [← hT s t hs ht hμs hμt hst]; rw [← hT t s ht hs hμt hμs hst.symm]; rw [union_comm]
  simp_all [hT s t hs ht hμs hμt hst, neg_add_rev]

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: [AddCommGroup β] (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T')
  proof: sub_eq_add_neg T T' ▸ hT.add hT'.neg

中文:
定理 sub
  条件: [加法交换群 β] (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T')
  证明: sub_eq_add_neg T T' ▸ hT.add hT'.neg

Depends on / 依赖: hT.add, sub_eq_add_neg
-/
theorem sub [AddCommGroup β] (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T - T') :=
  sub_eq_add_neg T T' ▸ hT.add hT'.neg

end FinMeasAdditive

/--
Definition of `DominatedFinMeasAdditive` / `DominatedFinMeasAdditive` 的定义

English:
definition DominatedFinMeasAdditive
  signature: {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
  body: FinMeasAdditive μ T ∧ forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s

中文:
定义 DominatedFinMeasAdditive
  签名: {β} [SeminormedAddComm群 β] {_ : 可测空间 α} (μ : 测度 α)
  定义体: FinMeasAdditive μ T ∧ forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s

Depends on / 依赖: FinMeasAdditive, MeasurableSet
-/
def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α -> β) (C : Real) : Prop :=
  FinMeasAdditive μ T ∧ forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s

namespace DominatedFinMeasAdditive

variable {β : Type*} [SeminormedAddCommGroup β] {T T' : Set α -> β} {C C' : Real}

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: {m : MeasurableSpace α} (μ : Measure α) (hC : 0 <= C)
  proof: by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply]; rw [norm_zero]
  exact mul_nonneg hC toReal_nonneg

中文:
定理 zero
  条件: {m : 可测空间 α} (μ : 测度 α) (hC : 0 <= C)
  证明: by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply]; rw [norm_zero]
  exact mul_nonneg hC toReal_nonneg

Depends on / 依赖: FinMeasAdditive, FinMeasAdditive.zero, Pi.zero_apply, mul_nonneg, norm_zero, toReal_nonneg, zero_apply
-/
theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 <= C) :
    DominatedFinMeasAdditive μ (0 : Set α -> β) C := by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply]; rw [norm_zero]
  exact mul_nonneg hC toReal_nonneg

/--
theorem `eq_zero_of_measure_zero` / 定理 `eq_zero_of_measure_zero`

English:
theorem eq_zero_of_measure_zero
  statement: {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real}
  proof: by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def]; rw [hs_zero]; rw [ENNReal.toReal_zero]; rw [mul_zero]

中文:
定理 eq_zero_of_measure_zero
  结论: {β : 类型} [赋范交换加群 β] {T : 集合 α -> β} {C : 实数}
  证明: by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def]; rw [hs_zero]; rw [ENNReal.toReal_zero]; rw [mul_zero]

Depends on / 依赖: ENNReal, ENNReal.toReal_zero, antisymm, hs_zero, le_of_eq, measureReal_def, mul_zero, norm_eq_zero, norm_eq_zero.mp, norm_nonneg, toReal_zero
-/
theorem eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def]; rw [hs_zero]; rw [ENNReal.toReal_zero]; rw [mul_zero]

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  statement: {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} {_ : MeasurableSpace α}
  proof: eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])

中文:
定理 eq_zero
  结论: {β : 类型} [赋范交换加群 β] {T : 集合 α -> β} {C : 实数} {_ : 可测空间 α}
  证明: eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])

Depends on / 依赖: Measure, Measure.coe_zero, Pi.zero_apply, coe_zero, eq_zero_of_measure_zero, zero_apply
-/
theorem eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} {_ : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: (hT : DominatedFinMeasAdditive μ T C) (hC : C <= C')
  proof: ⟨hT.1, fun s hs hμs => (hT.2 s hs hμs).trans mul_le_mul_of_nonneg_right hC measureReal_nonneg⟩

中文:
定理 of_le
  条件: (hT : DominatedFinMeasAdditive μ T C) (hC : C <= C')
  证明: ⟨hT.1, fun s hs hμs => (hT.2 s hs hμs).trans mul_le_mul_of_nonneg_right hC measureReal_nonneg⟩

Depends on / 依赖: measureReal_nonneg, mul_le_mul_of_nonneg_right
-/
theorem of_le (hT : DominatedFinMeasAdditive μ T C) (hC : C <= C') :
    DominatedFinMeasAdditive μ T C' :=
⟨hT.1, fun s hs hμs => (hT.2 s hs hμs).trans mul_le_mul_of_nonneg_right hC measureReal_nonneg⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
  proof: by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply]; rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))

中文:
定理 add
  条件: (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
  证明: by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply]; rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))

Depends on / 依赖: Pi.add_apply, add_apply, add_le_add, add_mul, norm_add_le
-/
theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply]; rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hT : DominatedFinMeasAdditive μ T C)
  proof: ⟨hT.1.neg, fun s hs hμs => by simpa using hT.2 s hs hμs⟩

中文:
定理 neg
  条件: (hT : DominatedFinMeasAdditive μ T C)
  证明: ⟨hT.1.neg, fun s hs hμs => by simpa using hT.2 s hs hμs⟩
-/
theorem neg (hT : DominatedFinMeasAdditive μ T C) :
    DominatedFinMeasAdditive μ (-T) C :=
  ⟨hT.1.neg, fun s hs hμs => by simpa using hT.2 s hs hμs⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
  proof: by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)

中文:
定理 smul
  结论: [半赋范加群 𝕜] [分配标量乘法 𝕜 β] [是BoundedSMul 𝕜 β]
  证明: by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)

Depends on / 依赖: le_rfl, mul_assoc, mul_le_mul, norm_nonneg, norm_smul_le
-/
theorem smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
    (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) := by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)

/--
theorem `of_measure_le` / 定理 `of_measure_le`

English:
theorem of_measure_le
  statement: {μ' : Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C)
  proof: by
have h' : forall s, μ s = ∞ -> μ' s = ∞ := fun s hs => top_unique hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ => h' s, fun s hs hμ's => ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ <= C * μ.real s := hT.2 s hs hμs
    _ <= C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne

中文:
定理 of_measure_le
  结论: {μ' : 测度 α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C)
  证明: by
have h' : forall s, μ s = ∞ -> μ' s = ∞ := fun s hs => top_unique hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ => h' s, fun s hs hμ's => ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ <= C * μ.real s := hT.2 s hs hμs
    _ <= C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne

Depends on / 依赖: hs.symm.trans_le, measureReal_def, of_eq_top_imp_eq_top, s.ne, top_unique, trans_le, trans_lt
-/
theorem of_measure_le {μ' : Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 <= C) : DominatedFinMeasAdditive μ' T C := by
have h' : forall s, μ s = ∞ -> μ' s = ∞ := fun s hs => top_unique hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ => h' s, fun s hs hμ's => ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ <= C * μ.real s := hT.2 s hs hμs
    _ <= C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne

/--
theorem `add_measure` / 定理 `add_measure`

English:
theorem add_measure
  statement: {C' : Real} (μ ν : Measure α)
  proof: by
  refine ⟨hT.1.add_measure hT'.1, fun s hs hsf => ?_⟩
  have hμs : μ s < ∞ := (Measure.le_add_right le_rfl s).trans_lt hsf
  have hνs : ν s < ∞ := (Measure.le_add_left le_rfl s).trans_lt hsf
  rw [Pi.add_apply]; rw [measureReal_add_apply hμs.ne hνs.ne]; rw [mul_add]
  calc
    ‖T s + T' s‖ <= ‖T s‖ + ‖T' s‖ := norm_add_le _ _
    _ <= C * μ.real s + C' * ν.real s := add_le_add (hT.2 s hs hμs) (hT'.2 s hs hνs)
    _ <= max C C' * μ.real s + max C C' * ν.real s := by
      gcongr
      · exact le_max_left C C'
      · exact le_max_right C C'

中文:
定理 add_measure
  结论: {C' : 实数} (μ ν : 测度 α)
  证明: by
  refine ⟨hT.1.add_measure hT'.1, fun s hs hsf => ?_⟩
  have hμs : μ s < ∞ := (Measure.le_add_right le_rfl s).trans_lt hsf
  have hνs : ν s < ∞ := (Measure.le_add_left le_rfl s).trans_lt hsf
  rw [Pi.add_apply]; rw [measureReal_add_apply hμs.ne hνs.ne]; rw [mul_add]
  calc
    ‖T s + T' s‖ <= ‖T s‖ + ‖T' s‖ := norm_add_le _ _
    _ <= C * μ.real s + C' * ν.real s := add_le_add (hT.2 s hs hμs) (hT'.2 s hs hνs)
    _ <= max C C' * μ.real s + max C C' * ν.real s := by
      gcongr
      · exact le_max_left C C'
      · exact le_max_right C C'

Depends on / 依赖: Measure, Measure.le_add_left, Measure.le_add_right, Pi.add_apply, add_apply, add_le_add, add_measure, le_add_left, le_add_right, le_max_left, le_max_ri, le_rfl, measureReal_add_apply, mul_add, norm_add_le, s.ne, trans_lt
-/
theorem add_measure {C' : Real} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive ν T' C') :
    DominatedFinMeasAdditive (μ + ν) (T + T') (max C C') := by
  refine ⟨hT.1.add_measure hT'.1, fun s hs hsf => ?_⟩
  have hμs : μ s < ∞ := (Measure.le_add_right le_rfl s).trans_lt hsf
  have hνs : ν s < ∞ := (Measure.le_add_left le_rfl s).trans_lt hsf
  rw [Pi.add_apply]; rw [measureReal_add_apply hμs.ne hνs.ne]; rw [mul_add]
  calc
    ‖T s + T' s‖ <= ‖T s‖ + ‖T' s‖ := norm_add_le _ _
    _ <= C * μ.real s + C' * ν.real s := add_le_add (hT.2 s hs hμs) (hT'.2 s hs hνs)
    _ <= max C C' * μ.real s + max C C' * ν.real s := by
      gcongr
      · exact le_max_left C C'
      · exact le_max_right C C'

/--
theorem `sub_measure` / 定理 `sub_measure`

English:
theorem sub_measure
  statement: {C' : Real} (μ ν : Measure α)
  proof: sub_eq_add_neg T T' ▸ hT.add_measure μ ν hT'.neg

中文:
定理 sub_measure
  结论: {C' : 实数} (μ ν : 测度 α)
  证明: sub_eq_add_neg T T' ▸ hT.add_measure μ ν hT'.neg

Depends on / 依赖: add_measure, hT.add_measure, sub_eq_add_neg
-/
theorem sub_measure {C' : Real} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive ν T' C') :
    DominatedFinMeasAdditive (μ + ν) (T - T') (max C C') :=
  sub_eq_add_neg T T' ▸ hT.add_measure μ ν hT'.neg

/--
theorem `add_measure_right` / 定理 `add_measure_right`

English:
theorem add_measure_right
  statement: {_ : MeasurableSpace α} (μ ν : Measure α)
  proof: of_measure_le (Measure.le_add_right le_rfl) hT hC

中文:
定理 add_measure_right
  结论: {_ : 可测空间 α} (μ ν : 测度 α)
  证明: of_measure_le (Measure.le_add_right le_rfl) hT hC

Depends on / 依赖: Measure, Measure.le_add_right, le_add_right, le_rfl, of_measure_le
-/
theorem add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC

/--
theorem `add_measure_left` / 定理 `add_measure_left`

English:
theorem add_measure_left
  statement: {_ : MeasurableSpace α} (μ ν : Measure α)
  proof: of_measure_le (Measure.le_add_left le_rfl) hT hC

中文:
定理 add_measure_left
  结论: {_ : 可测空间 α} (μ ν : 测度 α)
  证明: of_measure_le (Measure.le_add_left le_rfl) hT hC

Depends on / 依赖: Measure, Measure.le_add_left, le_add_left, le_rfl, of_measure_le
-/
theorem add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 <= C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC

/--
theorem `finsetSum_measure` / 定理 `finsetSum_measure`

English:
theorem finsetSum_measure
  statement: {ι} {s : Finset ι} (hs : s.Nonempty) (μ : ι -> Measure α)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp_all
  | @cons i s his hs' ih =>
    simpa [his, Finset.sup'_cons hs' C] using (hT i).add_measure (μ i) (∑ j in s, μ j) ih

中文:
定理 finsetSum_measure
  结论: {ι} {s : 有限集 ι} (hs : s.非空) (μ : ι -> 测度 α)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp_all
  | @cons i s his hs' ih =>
    simpa [his, Finset.sup'_cons hs' C] using (hT i).add_measure (μ i) (∑ j in s, μ j) ih

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.sup, Nonempty, _cons, add_measure, cons_induction, singleton
-/
theorem finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty) (μ : ι -> Measure α)
    (T : ι -> Set α -> β) (C : ι -> Real) (hT : forall i, DominatedFinMeasAdditive (μ i) (T i) (C i)) :
    DominatedFinMeasAdditive (∑ i in s, μ i) (∑ i in s, T i) (s.sup' hs C) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp_all
  | @cons i s his hs' ih =>
    simpa [his, Finset.sup'_cons hs' C] using (hT i).add_measure (μ i) (∑ j in s, μ j) ih

/--
theorem `of_smul_measure` / 定理 `of_smul_measure`

English:
theorem of_smul_measure
  given: {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive (c • μ) T C)
  proof: by
  have h : forall s, MeasurableSet s -> c • μ s = ∞ -> μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s != ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring

中文:
定理 of_smul_measure
  条件: {c : 实数>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive (c • μ) T C)
  证明: by
  have h : forall s, MeasurableSet s -> c • μ s = ∞ -> μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s != ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, MeasurableSet, false_and, hc_ne_top, le_of_eq, lt_top, measureReal_ennreal_smul_apply, mul_eq_top, of_eq_top_imp_eq_top, or_false, s.lt_top, s.ne, smul_eq_mul
-/
theorem of_smul_measure {c : Real>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) := by
  have h : forall s, MeasurableSet s -> c • μ s = ∞ -> μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s != ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring

/--
theorem `of_measure_le_smul` / 定理 `of_measure_le_smul`

English:
theorem of_measure_le_smul
  statement: {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞) (h : μ <= c • μ')
  proof: (hT.of_measure_le h hC).of_smul_measure hc

中文:
定理 of_measure_le_smul
  结论: {μ' : 测度 α} {c : 实数>=0∞} (hc : c != ∞) (h : μ <= c • μ')
  证明: (hT.of_measure_le h hC).of_smul_measure hc

Depends on / 依赖: hT.of_measure_le, of_measure_le, of_smul_measure
-/
theorem of_measure_le_smul {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞) (h : μ <= c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure hc

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

/--
Definition of `setToSimpleFunc` / `setToSimpleFunc` 的定义

English:
definition setToSimpleFunc
  signature: {_ : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (f : α ->ₛ F)
  body: ∑ x in f.range, T (f ⁻¹' {x}) x

@[simp]

中文:
定义 setToSimpleFunc
  签名: {_ : 可测空间 α} (T : 集合 α -> F ->L[实数] F') (f : α ->ₛ F)
  定义体: ∑ x in f.range, T (f ⁻¹' {x}) x

@[simp]

Depends on / 依赖: f.range
-/
def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (f : α ->ₛ F) : F' :=
  ∑ x in f.range, T (f ⁻¹' {x}) x

@[simp]
/--
theorem `setToSimpleFunc_zero` / 定理 `setToSimpleFunc_zero`

English:
theorem setToSimpleFunc_zero
  given: {m : MeasurableSpace α} (f : α ->ₛ F)
  proof: by simp [setToSimpleFunc]

中文:
定理 setToSimpleFunc_zero
  条件: {m : 可测空间 α} (f : α ->ₛ F)
  证明: by simp [setToSimpleFunc]

Depends on / 依赖: setToSimpleFunc
-/
theorem setToSimpleFunc_zero {m : MeasurableSpace α} (f : α ->ₛ F) :
    setToSimpleFunc (0 : Set α -> F ->L[Real] F') f = 0 := by simp [setToSimpleFunc]

/--
theorem `setToSimpleFunc_zero'` / 定理 `setToSimpleFunc_zero'`

English:
theorem setToSimpleFunc_zero'
  statement: {T : Set α -> E ->L[Real] F'}
  proof: by
  simp_rw [setToSimpleFunc]
  refine sum_eq_zero fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0)]; rw [zero_apply]

@[simp]

中文:
定理 setToSimpleFunc_zero'
  结论: {T : 集合 α -> E ->L[实数] F'}
  证明: by
  simp_rw [setToSimpleFunc]
  refine sum_eq_zero fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0)]; rw [zero_apply]

@[simp]

Depends on / 依赖: h_zero, measurableSet_fiber, measure_preimage_lt_top_of_integrable, setToSimpleFunc, simp_rw, sum_eq_zero, zero_apply
-/
theorem setToSimpleFunc_zero' {T : Set α -> E ->L[Real] F'}
    (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = 0 := by
  simp_rw [setToSimpleFunc]
  refine sum_eq_zero fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0)]; rw [zero_apply]

@[simp]
/--
theorem `setToSimpleFunc_zero_apply` / 定理 `setToSimpleFunc_zero_apply`

English:
theorem setToSimpleFunc_zero_apply
  given: {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F')
  proof: by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]

中文:
定理 setToSimpleFunc_zero_apply
  条件: {m : 可测空间 α} (T : 集合 α -> F ->L[实数] F')
  证明: by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]

Depends on / 依赖: isEmpty_or_nonempty, setToSimpleFunc
-/
theorem setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') :
    setToSimpleFunc T (0 : α ->ₛ F) = 0 := by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]

/--
theorem `setToSimpleFunc_eq_sum_filter` / 定理 `setToSimpleFunc_eq_sum_filter`

English:
theorem setToSimpleFunc_eq_sum_filter
  statement: [DecidablePred fun x => x != (0 : F)]
  proof: by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

中文:
定理 setToSimpleFunc_eq_sum_filter
  结论: [DecidablePred fun x => x != (0 : F)]
  证明: by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

Depends on / 依赖: map_zero, sum_filter_of_ne
-/
theorem setToSimpleFunc_eq_sum_filter [DecidablePred fun x => x != (0 : F)]
    {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (f : α ->ₛ F) :
    setToSimpleFunc T f = ∑ x in f.range with x != 0, T (f ⁻¹' {x}) x := by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

/--
theorem `setToSimpleFunc_eq_sum_of_subset` / 定理 `setToSimpleFunc_eq_sum_of_subset`

English:
theorem setToSimpleFunc_eq_sum_of_subset
  statement: [DecidablePred fun x : F => x != 0]
  proof: by
  rw [setToSimpleFunc_eq_sum_filter]; rw [Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx, hT]

中文:
定理 setToSimpleFunc_eq_sum_of_subset
  结论: [DecidablePred fun x : F => x != 0]
  证明: by
  rw [setToSimpleFunc_eq_sum_filter]; rw [Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx, hT]

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.mem_filter, Finset.sum_subset, Set.disjoint_singleton_left, SimpleFunc, SimpleFunc.mem_range, disjoint_singleton_left, hx.symm, mem_filter, mem_range, not_and_or, not_not, preimage_eq_empty, setToSimpleFunc_eq_sum_filter, sum_subset
-/
theorem setToSimpleFunc_eq_sum_of_subset [DecidablePred fun x : F => x != 0]
    (T : Set α -> F ->L[Real] F') (hT : T ∅ = 0) {f : α ->ₛ F} {s : Finset F}
    (hs : {x in f.range | x != 0} subseteq s) :
    setToSimpleFunc T f = ∑ x in s, T (f ⁻¹' {x}) x := by
  rw [setToSimpleFunc_eq_sum_filter]; rw [Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx, hT]

/--
theorem `map_setToSimpleFunc` / 定理 `map_setToSimpleFunc`

English:
theorem map_setToSimpleFunc
  statement: (T : Set α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G}
  proof: by
  classical
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : forall x in f.range, x != 0 -> μ (f ⁻¹' {x}) != ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [map_zero]; rw [Finset.sum_eq_zero fun x hx => ?_]
    rw [mem_filter] at hx
    rw [hx.2]; rw [map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a))
      = T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a)) := by
    rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a))
      = T (⋃ y in {b in f.range | g b = g (f a)}, f ⁻¹' {y}) (g (f a)) := by
    rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
  · exact fun i => measurableSet_fiber _ _
  · grind
  · grind [Set.disjoint_iff]

中文:
定理 map_setToSimpleFunc
  结论: (T : 集合 α -> F ->L[实数] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G}
  证明: by
  classical
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : forall x in f.range, x != 0 -> μ (f ⁻¹' {x}) != ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [map_zero]; rw [Finset.sum_eq_zero fun x hx => ?_]
    rw [mem_filter] at hx
    rw [hx.2]; rw [map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a))
      = T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a)) := by
    rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a))
      = T (⋃ y in {b in f.range | g b = g (f a)}, f ⁻¹' {y}) (g (f a)) := by
    rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
  · exact fun i => measurableSet_fiber _ _
  · grind
  · grind [Set.disjoint_iff]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Finset.sum_image, T_empty, classical, f.range, h_add, h_add.map_empty_eq_zero, h_left_eq, map_empty_eq_zero, map_zero, measure_preimage_lt_top_of_integrable, mem_filter, mem_range, range_map, setToSimpleFunc, simp_rw, sum_eq_zero, sum_image
-/
theorem map_setToSimpleFunc (T : Set α -> F ->L[Real] F') (h_add : FinMeasAdditive μ T) {f : α ->ₛ G}
    (hf : Integrable f μ) {g : G -> F} (hg : g 0 = 0) :
    (f.map g).setToSimpleFunc T = ∑ x in f.range, T (f ⁻¹' {x}) (g x) := by
  classical
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : forall x in f.range, x != 0 -> μ (f ⁻¹' {x}) != ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [map_zero]; rw [Finset.sum_eq_zero fun x hx => ?_]
    rw [mem_filter] at hx
    rw [hx.2]; rw [map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a))
      = T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a)) := by
    rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ({b in f.range | g b = g (f a)} : Finset _)) (g (f a))
      = T (⋃ y in {b in f.range | g b = g (f a)}, f ⁻¹' {y}) (g (f a)) := by
    rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
  · exact fun i => measurableSet_fiber _ _
  · grind
  · grind [Set.disjoint_iff]

/--
theorem `setToSimpleFunc_congr'` / 定理 `setToSimpleFunc_congr'`

English:
theorem setToSimpleFunc_congr'
  statement: (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  proof: show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} inter g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h eq
      simp only [this, zero_apply, pair_apply]

中文:
定理 setToSimpleFunc_congr'
  结论: (T : 集合 α -> E ->L[实数] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  证明: show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} inter g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h eq
      simp only [this, zero_apply, pair_apply]

Depends on / 依赖: Finset, Finset.sum_congr, Integrable, Prod.fst, Prod.fst_zero, Prod.snd, Prod.snd_zero, f.pair, fst_zero, h_add, h_eq, h_pair, integrable_pair, map_setToSimpleFunc, mem_range, pair_apply, setToSimpleFunc, snd_zero, sum_congr
-/
theorem setToSimpleFunc_congr' (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : Pairwise fun x y => T (f ⁻¹' {x} inter g ⁻¹' {y}) = 0) :
    f.setToSimpleFunc T = g.setToSimpleFunc T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} inter g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h eq
      simp only [this, zero_apply, pair_apply]

/--
theorem `setToSimpleFunc_congr` / 定理 `setToSimpleFunc_congr`

English:
theorem setToSimpleFunc_congr
  statement: (T : Set α -> E ->L[Real] F)
  proof: by
  refine setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) ?_
  refine fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) ?_
  rw [EventuallyEq]; rw [ae_iff] at h
  refine measure_mono_null (fun z => ?_) h
  simp_rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]

中文:
定理 setToSimpleFunc_congr
  结论: (T : 集合 α -> E ->L[实数] F)
  证明: by
  refine setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) ?_
  refine fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) ?_
  rw [EventuallyEq]; rw [ae_iff] at h
  refine measure_mono_null (fun z => ?_) h
  simp_rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]

Depends on / 依赖: EventuallyEq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, ae_iff, h_add, h_zero, integrable_congr, measurableSet_fiber, measure_mono_null, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, setToSimpleFunc_congr, simp_rw
-/
theorem setToSimpleFunc_congr (T : Set α -> E ->L[Real] F)
    (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
    (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) ?_
  refine fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) ?_
  rw [EventuallyEq]; rw [ae_iff] at h
  refine measure_mono_null (fun z => ?_) h
  simp_rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]

/--
theorem `setToSimpleFunc_congr_left` / 定理 `setToSimpleFunc_congr_left`

English:
theorem setToSimpleFunc_congr_left
  statement: (T T' : Set α -> E ->L[Real] F)
  proof: by
  simp_rw [setToSimpleFunc]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]

中文:
定理 setToSimpleFunc_congr_left
  结论: (T T' : 集合 α -> E ->L[实数] F)
  证明: by
  simp_rw [setToSimpleFunc]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]

Depends on / 依赖: SimpleFunc, SimpleFunc.measurableSet_fiber, SimpleFunc.measure_preimage_lt_top_of_integrable, measurableSet_fiber, measure_preimage_lt_top_of_integrable, setToSimpleFunc, simp_rw, sum_congr
-/
theorem setToSimpleFunc_congr_left (T T' : Set α -> E ->L[Real] F)
    (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s) (f : α ->ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]

/--
theorem `setToSimpleFunc_add_left` / 定理 `setToSimpleFunc_add_left`

English:
theorem setToSimpleFunc_add_left
  given: {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] F') {f : α ->ₛ F}
  proof: by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]

中文:
定理 setToSimpleFunc_add_left
  条件: {m : 可测空间 α} (T T' : 集合 α -> F ->L[实数] F') {f : α ->ₛ F}
  证明: by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]

Depends on / 依赖: Pi.add_apply, add_apply, setToSimpleFunc, simp_rw, sum_add_distrib
-/
theorem setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] F') {f : α ->ₛ F} :
    setToSimpleFunc (T + T') f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]

/--
theorem `setToSimpleFunc_add_left'` / 定理 `setToSimpleFunc_add_left'`

English:
theorem setToSimpleFunc_add_left'
  statement: (T T' T'' : Set α -> E ->L[Real] F)
  proof: by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

中文:
定理 setToSimpleFunc_add_left'
  结论: (T T' T'' : 集合 α -> E ->L[实数] F)
  证明: by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

Depends on / 依赖: Finset, Finset.sum_congr, Pi.add_apply, add_apply, classical, f.range, h_add, measurableSet_preimage, measure_preimage_lt_top_of_integrable, mem_filter, setToSimpleFunc_eq_sum_filter, simp_rw, sum_add_distrib, sum_congr
-/
theorem setToSimpleFunc_add_left' (T T' T'' : Set α -> E ->L[Real] F)
    (h_add : forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) {f : α ->ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

/--
theorem `setToSimpleFunc_smul_left` / 定理 `setToSimpleFunc_smul_left`

English:
theorem setToSimpleFunc_smul_left
  statement: {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (c : Real)
  proof: by
  simp_rw [setToSimpleFunc, _root_.smul_apply, smul_sum]

中文:
定理 setToSimpleFunc_smul_left
  结论: {m : 可测空间 α} (T : 集合 α -> F ->L[实数] F') (c : 实数)
  证明: by
  simp_rw [setToSimpleFunc, _root_.smul_apply, smul_sum]

Depends on / 依赖: _root_, _root_.smul_apply, setToSimpleFunc, simp_rw, smul_apply, smul_sum
-/
theorem setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (c : Real)
    (f : α ->ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setToSimpleFunc T f := by
  simp_rw [setToSimpleFunc, _root_.smul_apply, smul_sum]

/--
theorem `setToSimpleFunc_smul_left'` / 定理 `setToSimpleFunc_smul_left'`

English:
theorem setToSimpleFunc_smul_left'
  statement: (T T' : Set α -> E ->L[Real] F') (c : Real)
  proof: by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]; rw [_root_.smul_apply]
  intro x hx
  refine
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

中文:
定理 setToSimpleFunc_smul_left'
  结论: (T T' : 集合 α -> E ->L[实数] F') (c : 实数)
  证明: by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]; rw [_root_.smul_apply]
  intro x hx
  refine
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

Depends on / 依赖: Finset, Finset.sum_congr, _root_, _root_.smul_apply, classical, f.range, h_smul, measurableSet_preimage, measure_preimage_lt_top_of_integrable, mem_filter, setToSimpleFunc_eq_sum_filter, simp_rw, smul_apply, smul_sum, sum_congr
-/
theorem setToSimpleFunc_smul_left' (T T' : Set α -> E ->L[Real] F') (c : Real)
    (h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) {f : α ->ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T' f = c • setToSimpleFunc T f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices forall x in {x in f.range | x != 0}, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]; rw [_root_.smul_apply]
  intro x hx
  refine
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

/--
theorem `setToSimpleFunc_add` / 定理 `setToSimpleFunc_add`

English:
theorem setToSimpleFunc_add
  statement: (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  proof: have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂]; rw [map_setToSimpleFunc T h_add hp_pair]; simp
    _ = ∑ x in (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun _ _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero]; rw [map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]

中文:
定理 setToSimpleFunc_add
  结论: (T : 集合 α -> E ->L[实数] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  证明: have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂]; rw [map_setToSimpleFunc T h_add hp_pair]; simp
    _ = ∑ x in (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun _ _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero]; rw [map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_add, Finset, Finset.sum_congr, Integrable, f.pair, h_add, hp_pair, integrable_pair, map_add, map_setToSimpleFunc, setToSimpleFunc, sum_congr, x.fst, x.snd
-/
theorem setToSimpleFunc_add (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g :=
  have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂]; rw [map_setToSimpleFunc T h_add hp_pair]; simp
    _ = ∑ x in (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun _ _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero]; rw [map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]

/--
theorem `setToSimpleFunc_neg` / 定理 `setToSimpleFunc_neg`

English:
theorem setToSimpleFunc_neg
  statement: (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E}
  proof: calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero]; rw [setToSimpleFunc]; rw [← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => map_neg _ _

中文:
定理 setToSimpleFunc_neg
  结论: (T : 集合 α -> E ->L[实数] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E}
  证明: calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero]; rw [setToSimpleFunc]; rw [← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => map_neg _ _

Depends on / 依赖: Finset, Finset.sum_congr, Neg.neg, f.map, h_add, map_neg, map_setToSimpleFunc, neg_zero, setToSimpleFunc, sum_congr, sum_neg_distrib
-/
theorem setToSimpleFunc_neg (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero]; rw [setToSimpleFunc]; rw [← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => map_neg _ _

/--
theorem `setToSimpleFunc_sub` / 定理 `setToSimpleFunc_sub`

English:
theorem setToSimpleFunc_sub
  statement: (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  proof: by
  rw [sub_eq_add_neg]; rw [setToSimpleFunc_add T h_add hf]; rw [setToSimpleFunc_neg T h_add hg]; rw [sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  rw [SimpleFunc.coe_neg]; rw [Pi.neg_def]; rw [← Function.comp_def]; rw [preimage_comp]; rw [neg_preimage]; rw [Set.neg_singleton]
  refine hg (-x) ?_
  simp [hx_ne]

中文:
定理 setToSimpleFunc_sub
  结论: (T : 集合 α -> E ->L[实数] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
  证明: by
  rw [sub_eq_add_neg]; rw [setToSimpleFunc_add T h_add hf]; rw [setToSimpleFunc_neg T h_add hg]; rw [sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  rw [SimpleFunc.coe_neg]; rw [Pi.neg_def]; rw [← Function.comp_def]; rw [preimage_comp]; rw [neg_preimage]; rw [Set.neg_singleton]
  refine hg (-x) ?_
  simp [hx_ne]

Depends on / 依赖: Function, Function.comp_def, Pi.neg_def, Set.neg_singleton, SimpleFunc, SimpleFunc.coe_neg, coe_neg, comp_def, h_add, hx_ne, integrable_iff, neg_def, neg_preimage, neg_singleton, preimage_comp, setToSimpleFunc_add, setToSimpleFunc_neg, sub_eq_add_neg
-/
theorem setToSimpleFunc_sub (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g := by
  rw [sub_eq_add_neg]; rw [setToSimpleFunc_add T h_add hf]; rw [setToSimpleFunc_neg T h_add hg]; rw [sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  rw [SimpleFunc.coe_neg]; rw [Pi.neg_def]; rw [← Function.comp_def]; rw [preimage_comp]; rw [neg_preimage]; rw [Set.neg_singleton]
  refine hg (-x) ?_
  simp [hx_ne]

/--
theorem `setToSimpleFunc_smul_real` / 定理 `setToSimpleFunc_smul_real`

English:
theorem setToSimpleFunc_smul_real
  statement: (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) (c : Real)
  proof: calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

中文:
定理 setToSimpleFunc_smul_real
  结论: (T : 集合 α -> E ->L[实数] F) (h_add : FinMeasAdditive μ T) (c : 实数)
  证明: calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

Depends on / 依赖: Finset, Finset.sum_congr, f.range, h_add, map_setToSimpleFunc, map_smul, setToSimpleFunc, smul_eq_map, smul_sum, smul_zero, sum_congr
-/
theorem setToSimpleFunc_smul_real (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) (c : Real)
    {f : α ->ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

/--
theorem `setToSimpleFunc_smul` / 定理 `setToSimpleFunc_smul`

English:
theorem setToSimpleFunc_smul
  statement: {E} [NormedAddCommGroup E] [SMulZeroClass 𝕜 E]
  proof: calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x := Finset.sum_congr rfl fun b _ => by rw [h_smul]
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

中文:
定理 setToSimpleFunc_smul
  结论: {E} [赋范交换加群 E] [SMulZero类 𝕜 E]
  证明: calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x := Finset.sum_congr rfl fun b _ => by rw [h_smul]
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

Depends on / 依赖: Finset, Finset.sum_congr, f.range, h_add, h_smul, map_setToSimpleFunc, setToSimpleFunc, smul_eq_map, smul_sum, smul_zero, sum_congr
-/
theorem setToSimpleFunc_smul {E} [NormedAddCommGroup E] [SMulZeroClass 𝕜 E]
    [NormedSpace Real E] [DistribSMul 𝕜 F] (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α ->ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f]; rw [map_setToSimpleFunc T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x := Finset.sum_congr rfl fun b _ => by rw [h_smul]
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace Real G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace Real G']

/--
theorem `setToSimpleFunc_mono_left` / 定理 `setToSimpleFunc_mono_left`

English:
theorem setToSimpleFunc_mono_left
  statement: {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] G'')
  proof: by
  simp_rw [setToSimpleFunc]; gcongr; apply hTT'

中文:
定理 setToSimpleFunc_mono_left
  结论: {m : 可测空间 α} (T T' : 集合 α -> F ->L[实数] G'')
  证明: by
  simp_rw [setToSimpleFunc]; gcongr; apply hTT'

Depends on / 依赖: setToSimpleFunc, simp_rw
-/
theorem setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] G'')
    (hTT' : forall s x, T s x <= T' s x) (f : α ->ₛ F) : setToSimpleFunc T f <= setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]; gcongr; apply hTT'

/--
theorem `setToSimpleFunc_mono_left'` / 定理 `setToSimpleFunc_mono_left'`

English:
theorem setToSimpleFunc_mono_left'
  statement: (T T' : Set α -> E ->L[Real] G'')
  proof: by
  unfold setToSimpleFunc
  gcongr with i _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i

中文:
定理 setToSimpleFunc_mono_left'
  结论: (T T' : 集合 α -> E ->L[实数] G'')
  证明: by
  unfold setToSimpleFunc
  gcongr with i _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i

Depends on / 依赖: measurableSet_fiber, measure_preimage_lt_top_of_integrable, setToSimpleFunc
-/
theorem setToSimpleFunc_mono_left' (T T' : Set α -> E ->L[Real] G'')
    (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->ₛ E)
    (hf : Integrable f μ) : setToSimpleFunc T f <= setToSimpleFunc T' f := by
  unfold setToSimpleFunc
  gcongr with i _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i

/--
theorem `setToSimpleFunc_nonneg` / 定理 `setToSimpleFunc_nonneg`

English:
theorem setToSimpleFunc_nonneg
  statement: {m : MeasurableSpace α} (T : Set α -> G' ->L[Real] G'')
  proof: by
  refine sum_nonneg fun i hi => hT_nonneg _ i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  refine le_trans ?_ (hf y)
  simp

中文:
定理 setToSimpleFunc_nonneg
  结论: {m : 可测空间 α} (T : 集合 α -> G' ->L[实数] G'')
  证明: by
  refine sum_nonneg fun i hi => hT_nonneg _ i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  refine le_trans ?_ (hf y)
  simp

Depends on / 依赖: Set.mem_range.mp, hT_nonneg, le_trans, mem_range, sum_nonneg
-/
theorem setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α -> G' ->L[Real] G'')
    (hT_nonneg : forall s x, 0 <= x -> 0 <= T s x) (f : α ->ₛ G') (hf : 0 <= f) :
    0 <= setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => hT_nonneg _ i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  refine le_trans ?_ (hf y)
  simp

/--
theorem `setToSimpleFunc_nonneg'` / 定理 `setToSimpleFunc_nonneg'`

English:
theorem setToSimpleFunc_nonneg'
  statement: (T : Set α -> G' ->L[Real] G'')
  proof: by
  refine sum_nonneg fun i hi => ?_
  by_cases h0 : i = 0
  · simp [h0]
  refine
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  convert! hf y

中文:
定理 setToSimpleFunc_nonneg'
  结论: (T : 集合 α -> G' ->L[实数] G'')
  证明: by
  refine sum_nonneg fun i hi => ?_
  by_cases h0 : i = 0
  · simp [h0]
  refine
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  convert! hf y

Depends on / 依赖: Set.mem_range.mp, convert, hT_nonneg, measurableSet_fiber, measure_preimage_lt_top_of_integrable, mem_range, sum_nonneg
-/
theorem setToSimpleFunc_nonneg' (T : Set α -> G' ->L[Real] G'')
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) (f : α ->ₛ G') (hf : 0 <= f)
    (hfi : Integrable f μ) : 0 <= setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => ?_
  by_cases h0 : i = 0
  · simp [h0]
  refine
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  convert! hf y

/--
theorem `setToSimpleFunc_mono` / 定理 `setToSimpleFunc_mono`

English:
theorem setToSimpleFunc_mono
  statement: [IsOrderedAddMonoid G']
  proof: by
  rw [← sub_nonneg]; rw [← setToSimpleFunc_sub T h_add hgi hfi]
  refine setToSimpleFunc_nonneg' T hT_nonneg _ ?_ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x

中文:
定理 setToSimpleFunc_mono
  结论: [是OrderedAdd幺半群 G']
  证明: by
  rw [← sub_nonneg]; rw [← setToSimpleFunc_sub T h_add hgi hfi]
  refine setToSimpleFunc_nonneg' T hT_nonneg _ ?_ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x

Depends on / 依赖: PartialOrder, PartialOrder.lift, Pi.sub_apply, Pi.zero_apply, Subtype, Subtype.coe_injective, coe_injective, coe_sub, coe_zero, hT_nonneg, h_add, hgi.sub, setToSimpleFunc_nonneg, setToSimpleFunc_sub, sub_apply, sub_nonneg, zero_apply
-/
theorem setToSimpleFunc_mono [IsOrderedAddMonoid G']
    {T : Set α -> G' ->L[Real] G''} (h_add : FinMeasAdditive μ T)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α ->ₛ G'}
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hfg : f <= g) :
    setToSimpleFunc T f <= setToSimpleFunc T g := by
  rw [← sub_nonneg]; rw [← setToSimpleFunc_sub T h_add hgi hfi]
  refine setToSimpleFunc_nonneg' T hT_nonneg _ ?_ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x

end Order

/--
theorem `norm_setToSimpleFunc_le_sum_opNorm` / 定理 `norm_setToSimpleFunc_le_sum_opNorm`

English:
theorem norm_setToSimpleFunc_le_sum_opNorm
  statement: {m : MeasurableSpace α} (T : Set α -> F' ->L[Real] F)
  proof: calc
    ‖∑ x in f.range, T (f ⁻¹' {x}) x‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      gcongr with b; apply ContinuousLinearMap.le_opNorm

中文:
定理 norm_setToSimpleFunc_le_sum_opNorm
  结论: {m : 可测空间 α} (T : 集合 α -> F' ->L[实数] F)
  证明: calc
    ‖∑ x in f.range, T (f ⁻¹' {x}) x‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      gcongr with b; apply ContinuousLinearMap.le_opNorm

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_opNorm, f.range, le_opNorm, norm_sum_le
-/
theorem norm_setToSimpleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α -> F' ->L[Real] F)
    (f : α ->ₛ F') : ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
  calc
    ‖∑ x in f.range, T (f ⁻¹' {x}) x‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      gcongr with b; apply ContinuousLinearMap.le_opNorm

/--
theorem `norm_setToSimpleFunc_le_sum_mul_norm` / 定理 `norm_setToSimpleFunc_le_sum_mul_norm`

English:
theorem norm_setToSimpleFunc_le_sum_mul_norm
  statement: (T : Set α -> F ->L[Real] F') {C : Real}
  proof: calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      gcongr
exact hT_norm _ SimpleFunc.measurableSet_fiber _ _
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

中文:
定理 norm_setToSimpleFunc_le_sum_mul_norm
  结论: (T : 集合 α -> F ->L[实数] F') {C : 实数}
  证明: calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      gcongr
exact hT_norm _ SimpleFunc.measurableSet_fiber _ _
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

Depends on / 依赖: SimpleFunc, SimpleFunc.measurableSet_fiber, f.range, f.setToSimpleFunc, hT_norm, measurableSet_fiber, mul_assoc, mul_sum, norm_setToSimpleFunc_le_sum_opNorm, setToSimpleFunc, simp_rw
-/
theorem norm_setToSimpleFunc_le_sum_mul_norm (T : Set α -> F ->L[Real] F') {C : Real}
    (hT_norm : forall s, MeasurableSet s -> ‖T s‖ <= C * μ.real s) (f : α ->ₛ F) :
    ‖f.setToSimpleFunc T‖ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      gcongr
exact hT_norm _ SimpleFunc.measurableSet_fiber _ _
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

/--
theorem `norm_setToSimpleFunc_le_sum_mul_norm_of_integrable` / 定理 `norm_setToSimpleFunc_le_sum_mul_norm_of_integrable`

English:
theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable
  statement: (T : Set α -> E ->L[Real] F') {C : Real}
  proof: calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain rfl | hb := eq_or_ne b 0
      · simp
      gcongr
exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _)
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

中文:
定理 norm_setToSimpleFunc_le_sum_mul_norm_of_integrable
  结论: (T : 集合 α -> E ->L[实数] F') {C : 实数}
  证明: calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain rfl | hb := eq_or_ne b 0
      · simp
      gcongr
exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _)
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

Depends on / 依赖: Finset, Finset.sum_le_sum, SimpleFunc, SimpleFunc.measurableSet_fiber, SimpleFunc.measure_preimage_lt_top_of_integrable, eq_or_ne, f.range, f.setToSimpleFunc, hT_norm, measurableSet_fiber, measure_preimage_lt_top_of_integrable, mul_assoc, mul_sum, norm_setToSimpleFunc_le_sum_opNorm, setToSimpleFunc, simp_rw, sum_le_sum
-/
theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α -> E ->L[Real] F') {C : Real}
    (hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s) (f : α ->ₛ E)
    (hf : Integrable f μ) :
    ‖f.setToSimpleFunc T‖ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ <= ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ <= ∑ x in f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain rfl | hb := eq_or_ne b 0
      · simp
      gcongr
exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _)
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ <= C * ∑ x in f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

/--
theorem `setToSimpleFunc_indicator` / 定理 `setToSimpleFunc_indicator`

English:
theorem setToSimpleFunc_indicator
  statement: (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0)
  proof: by
  classical
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  · simp only [hT_empty, zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  obtain rfl | hs_univ := eq_or_ne s univ
  · have hα := hs_empty.to_type
    simp [← Function.const_def]
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton]; rw [(T _).map_zero]; rw [add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Function.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage]; rw [← Function.const_def]; rw [preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Function.const_zero]; rw [← Function.const_def]; rw [preimage_const_of_notMem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp

中文:
定理 setToSimpleFunc_indicator
  结论: (T : 集合 α -> F ->L[实数] F') (hT_empty : T ∅ = 0)
  证明: by
  classical
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  · simp only [hT_empty, zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  obtain rfl | hs_univ := eq_or_ne s univ
  · have hα := hs_empty.to_type
    simp [← Function.const_def]
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton]; rw [(T _).map_zero]; rw [add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Function.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage]; rw [← Function.const_def]; rw [preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Function.const_zero]; rw [← Function.const_def]; rw [preimage_const_of_notMem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp

Depends on / 依赖: Finset, Finset.mem_singleton, Function, Function.const_def, add_zero, classical, coe_pi, const_def, const_zero, eq_empty_or_nonempty, eq_or_ne, hT_empty, hs_empty, hs_empty.to_type, hs_univ, map_zero, mem_singleton, piecewise_empty, range_indicator, s.eq_empty_or_nonempty
-/
theorem setToSimpleFunc_indicator (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0)
    {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) :
    SimpleFunc.setToSimpleFunc T
        (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFunc.const α 0)) =
      T s x := by
  classical
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  · simp only [hT_empty, zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  obtain rfl | hs_univ := eq_or_ne s univ
  · have hα := hs_empty.to_type
    simp [← Function.const_def]
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton]; rw [(T _).map_zero]; rw [add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Function.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage]; rw [← Function.const_def]; rw [preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Function.const_zero]; rw [← Function.const_def]; rw [preimage_const_of_notMem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp

/--
theorem `setToSimpleFunc_const'` / 定理 `setToSimpleFunc_const'`

English:
theorem setToSimpleFunc_const'
  statement: [Nonempty α] (T : Set α -> F ->L[Real] F') (x : F)
  proof: by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]

中文:
定理 setToSimpleFunc_const'
  结论: [非空 α] (T : 集合 α -> F ->L[实数] F') (x : F)
  证明: by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]

Depends on / 依赖: Function, Function.const_def, Set.mem_singleton, coe_const, const_def, mem_singleton, preimage_const_of_mem, range_const, setToSimpleFunc, sum_singleton
-/
theorem setToSimpleFunc_const' [Nonempty α] (T : Set α -> F ->L[Real] F') (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]

/--
theorem `setToSimpleFunc_const` / 定理 `setToSimpleFunc_const`

English:
theorem setToSimpleFunc_const
  statement: (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0) (x : F)
  proof: by
  cases isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty]; rw [hT_empty]
    simp only [setToSimpleFunc, zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x

中文:
定理 setToSimpleFunc_const
  结论: (T : 集合 α -> F ->L[实数] F') (hT_empty : T ∅ = 0) (x : F)
  证明: by
  cases isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty]; rw [hT_empty]
    simp only [setToSimpleFunc, zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x

Depends on / 依赖: Subsingleton, Subsingleton.elim, hT_empty, h_univ_empty, isEmpty_or_nonempty, range_eq_empty_of_isEmpty, setToSimpleFunc, setToSimpleFunc_const, sum_empty, zero_apply
-/
theorem setToSimpleFunc_const (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0) (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  cases isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty]; rw [hT_empty]
    simp only [setToSimpleFunc, zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x

end SimpleFunc

end MeasureTheory
