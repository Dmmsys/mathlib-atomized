/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/

public section


open MeasureTheory Set TopologicalSpace

open ENNReal NNReal

/--
theorem `MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets` / 定理 `MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets`

English:
theorem MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets
  statement: {α : Type*}
  proof: by
  classical
  have : Encodable s := s_count.toEncodable
  have h' : forall p q, exists u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } subseteq u ∧ { x | q < f x } subseteq v ∧ (p in s -> q in s -> p < q -> μ (u inter v) = 0) := by
    intro p q
    by_cases H : p in s ∧ q in s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun _ _ _ => hμ⟩
    · refine
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => ?_⟩
      exact (H ⟨ps, qs, pq⟩).elim
  choose! u v huv using h'
  let u' : β -> Set α := fun p => ⋂ q in s inter Ioi p, u p q
  have u'_meas : forall i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono inter_subset_left) fun b _ => (huv i b).1
  let f' : α -> β := fun x => ⨅ i : s, piecewise (u' i) (fun _ => (i : β)) (fun _ => (⊤ : β)) x
  have f'_meas : Measurable f' := by fun_prop (disch := simp_all)
  let t := ⋃ (p : s) (q : ↥(s inter Ioi p)), u' p inter v p q
  have μt : μ t <= 0 :=
    calc
      μ t <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u' p inter v p q) := by
        refine (measure_iUnion_le _).trans ?_
        refine ENNReal.tsum_le_tsum fun p => ?_
        have := (s_count.mono (s.inter_subset_left (t := Ioi ↑p))).to_subtype
        apply measure_iUnion_le
      _ <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u p q inter v p q) := by
        gcongr with p q
        exact biInter_subset_of_mem q.2
      _ = ∑' (p : s) (_ : ↥(s inter Ioi p)), (0 : Real>=0∞) := by grind
      _ = 0 := by simp only [tsum_zero]
  have ff' : forallᵐ x ∂μ, f x = f' x := by
    have : forallᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymm μt bot_le
      change μ _ = 0
      convert! this
      ext y
      simp only [mem_ofPred_eq, mem_compl_iff, not_notMem]
    filter_upwards [this] with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x in u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_notMem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (i : β) (f x) inter s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) isOpen_Ioo (nonempty_Ioo.2 hx)
      have A : x in v i r := (huv i r).2.2.2.1 rq
      refine mem_iUnion.2 ⟨i, ?_⟩
      refine mem_iUnion.2 ⟨⟨r, ⟨rs, xr⟩⟩, ?_⟩
      exact ⟨H, A⟩
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (f x) q inter s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) isOpen_Ioo (nonempty_Ioo.2 hq)
      refine ⟨⟨r, rs⟩, ?_⟩
      have A : x in u' r := mem_biInter fun i _ => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem]
  exact ⟨f', f'_meas, ff'⟩

中文:
定理 测度论.aemeasurable_of_exist_almost_disjoint_supersets
  结论: {α : 类型}
  证明: by
  classical
  have : Encodable s := s_count.toEncodable
  have h' : forall p q, exists u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } subseteq u ∧ { x | q < f x } subseteq v ∧ (p in s -> q in s -> p < q -> μ (u inter v) = 0) := by
    intro p q
    by_cases H : p in s ∧ q in s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun _ _ _ => hμ⟩
    · refine
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => ?_⟩
      exact (H ⟨ps, qs, pq⟩).elim
  choose! u v huv using h'
  let u' : β -> Set α := fun p => ⋂ q in s inter Ioi p, u p q
  have u'_meas : forall i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono inter_subset_left) fun b _ => (huv i b).1
  let f' : α -> β := fun x => ⨅ i : s, piecewise (u' i) (fun _ => (i : β)) (fun _ => (⊤ : β)) x
  have f'_meas : Measurable f' := by fun_prop (disch := simp_all)
  let t := ⋃ (p : s) (q : ↥(s inter Ioi p)), u' p inter v p q
  have μt : μ t <= 0 :=
    calc
      μ t <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u' p inter v p q) := by
        refine (measure_iUnion_le _).trans ?_
        refine ENNReal.tsum_le_tsum fun p => ?_
        have := (s_count.mono (s.inter_subset_left (t := Ioi ↑p))).to_subtype
        apply measure_iUnion_le
      _ <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u p q inter v p q) := by
        gcongr with p q
        exact biInter_subset_of_mem q.2
      _ = ∑' (p : s) (_ : ↥(s inter Ioi p)), (0 : Real>=0∞) := by grind
      _ = 0 := by simp only [tsum_zero]
  have ff' : forallᵐ x ∂μ, f x = f' x := by
    have : forallᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymm μt bot_le
      change μ _ = 0
      convert! this
      ext y
      simp only [mem_ofPred_eq, mem_compl_iff, not_notMem]
    filter_upwards [this] with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x in u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_notMem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (i : β) (f x) inter s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) isOpen_Ioo (nonempty_Ioo.2 hx)
      have A : x in v i r := (huv i r).2.2.2.1 rq
      refine mem_iUnion.2 ⟨i, ?_⟩
      refine mem_iUnion.2 ⟨⟨r, ⟨rs, xr⟩⟩, ?_⟩
      exact ⟨H, A⟩
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (f x) q inter s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) isOpen_Ioo (nonempty_Ioo.2 hq)
      refine ⟨⟨r, rs⟩, ?_⟩
      have A : x in u' r := mem_biInter fun i _ => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem]
  exact ⟨f', f'_meas, ff'⟩

Depends on / 依赖: ConjAct, ConjAct.smul_def, Encodable, HasDetOne, HasDetOne.det_eq, MeasurableSet, MeasurableSet.univ, classical, det_eq, mem_pointwise_smul_iff_inv_smul_mem, s_count, s_count.toEncodable, smul_def, subset_univ, subseteq, toEncodable
-/
theorem MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*}
    {m : MeasurableSpace α} (μ : Measure α) {β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β]
    [BorelSpace β] (s : Set β) (s_count : s.Countable) (s_dense : Dense s) (f : α -> β)
    (h : forall p in s, forall q in s, p < q -> exists u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } subseteq u ∧ { x | q < f x } subseteq v ∧ μ (u inter v) = 0) :
    AEMeasurable f μ := by
  classical
  have : Encodable s := s_count.toEncodable
  have h' : forall p q, exists u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } subseteq u ∧ { x | q < f x } subseteq v ∧ (p in s -> q in s -> p < q -> μ (u inter v) = 0) := by
    intro p q
    by_cases H : p in s ∧ q in s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun _ _ _ => hμ⟩
    · refine
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => ?_⟩
      exact (H ⟨ps, qs, pq⟩).elim
  choose! u v huv using h'
  let u' : β -> Set α := fun p => ⋂ q in s inter Ioi p, u p q
  have u'_meas : forall i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono inter_subset_left) fun b _ => (huv i b).1
  let f' : α -> β := fun x => ⨅ i : s, piecewise (u' i) (fun _ => (i : β)) (fun _ => (⊤ : β)) x
  have f'_meas : Measurable f' := by fun_prop (disch := simp_all)
  let t := ⋃ (p : s) (q : ↥(s inter Ioi p)), u' p inter v p q
  have μt : μ t <= 0 :=
    calc
      μ t <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u' p inter v p q) := by
        refine (measure_iUnion_le _).trans ?_
        refine ENNReal.tsum_le_tsum fun p => ?_
        have := (s_count.mono (s.inter_subset_left (t := Ioi ↑p))).to_subtype
        apply measure_iUnion_le
      _ <= ∑' (p : s) (q : ↥(s inter Ioi p)), μ (u p q inter v p q) := by
        gcongr with p q
        exact biInter_subset_of_mem q.2
      _ = ∑' (p : s) (_ : ↥(s inter Ioi p)), (0 : Real>=0∞) := by grind
      _ = 0 := by simp only [tsum_zero]
  have ff' : forallᵐ x ∂μ, f x = f' x := by
    have : forallᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymm μt bot_le
      change μ _ = 0
      convert! this
      ext y
      simp only [mem_ofPred_eq, mem_compl_iff, not_notMem]
    filter_upwards [this] with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x in u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_notMem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (i : β) (f x) inter s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) isOpen_Ioo (nonempty_Ioo.2 hx)
      have A : x in v i r := (huv i r).2.2.2.1 rq
      refine mem_iUnion.2 ⟨i, ?_⟩
      refine mem_iUnion.2 ⟨⟨r, ⟨rs, xr⟩⟩, ?_⟩
      exact ⟨H, A⟩
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : exists r, r in Ioo (f x) q inter s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) isOpen_Ioo (nonempty_Ioo.2 hq)
      refine ⟨⟨r, rs⟩, ?_⟩
      have A : x in u' r := mem_biInter fun i _ => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem]
  exact ⟨f', f'_meas, ff'⟩

/--
theorem `ENNReal.aemeasurable_of_exist_almost_disjoint_supersets` / 定理 `ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`

English:
theorem ENNReal.aemeasurable_of_exist_almost_disjoint_supersets
  statement: {α : Type*} {m : MeasurableSpace α}
  proof: by
  obtain ⟨s, s_count, s_dense, _, s_top⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : forall x in s, x != ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to Real>=0 using I p hp
  lift q to Real>=0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)

中文:
定理 广义非负实数.aemeasurable_of_exist_almost_disjoint_supersets
  结论: {α : 类型} {m : 可测空间 α}
  证明: by
  obtain ⟨s, s_count, s_dense, _, s_top⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : forall x in s, x != ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to Real>=0 using I p hp
  lift q to Real>=0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)

Depends on / 依赖: ConjAct, ConjAct.smul_def, Countable, ENNReal, ENNReal.coe_lt_coe, ENNReal.exists_countable_dense_no_zero_top, HasDetPlusMinusOne, HasDetPlusMinusOne.det_eq, MeasureTheory, MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets, aemeasurable_of_exist_almost_disjoint_supersets, coe_lt_coe, det_eq, exists_countable_dense_no_zero_top, mem_pointwise_smul_iff_inv_smul_mem, s.Countable, s_count, s_dense, s_top, smul_def
-/
theorem ENNReal.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) (f : α -> Real>=0∞)
    (h : forall (p : Real>=0) (q : Real>=0), p < q ->
      exists u v, MeasurableSet u ∧ MeasurableSet v ∧
        { x | f x < p } subseteq u ∧ { x | (q : Real>=0∞) < f x } subseteq v ∧ μ (u inter v) = 0) :
    AEMeasurable f μ := by
  obtain ⟨s, s_count, s_dense, _, s_top⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : forall x in s, x != ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to Real>=0 using I p hp
  lift q to Real>=0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)
