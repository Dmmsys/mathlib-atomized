/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Inner regularity of finite measures

The main result of this file is
`InnerRegularCompactLTTop_of_pseudoEMetricSpace_completeSpace_secondCountable`:
A finite measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with
`SecondCountableTopology E` is inner regular with respect to compact sets. In other
words, a finite measure on such a space is a tight measure.

Finite measures on Polish spaces are an important special case, which makes the result
`MeasureTheory.PolishSpace.innerRegular_isCompact_isClosed_measurableSet` an important result in
probability.
-/

public section

open Set MeasureTheory TopologicalSpace

open scoped ENNReal Uniformity

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/--
theorem `innerRegularWRT_isCompact_closure_iff` / 定理 `innerRegularWRT_isCompact_closure_iff`

English:
theorem innerRegularWRT_isCompact_closure_iff
  given: [TopologicalSpace α] [R1Space α]
  proof: by
  constructor <;> intro h A hA r hr
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    exact ⟨closure K, closure_minimal hK1 hA, hK2, hK3.trans_le (measure_mono subset_closure)⟩
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only 

中文:
定理 innerRegularWRT_isCompact_closure_iff
  条件: [拓扑空间 α] [R1空间 α]
  证明: by
  constructor <;> intro h A hA r hr
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    exact ⟨closure K, closure_minimal hK1 hA, hK2, hK3.trans_le (measure_mono subset_closure)⟩
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only 

Depends on / 依赖: Function, Function.comp_apply, closure, closure_closure, closure_minimal, comp_apply, hK2.closure, hK3.trans_le, measure_mono, subset_closure, trans_le
-/
theorem innerRegularWRT_isCompact_closure_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed ↔ μ.InnerRegularWRT IsCompact IsClosed := by
  constructor <;> intro h A hA r hr
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    exact ⟨closure K, closure_minimal hK1 hA, hK2, hK3.trans_le (measure_mono subset_closure)⟩
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [closure_closure, Function.comp_apply] using hK2.closure
    · exact hK3.trans_le (measure_mono subset_closure)

/--
lemma `innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure` / 引理 `innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure`

English:
lemma innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
  proof: by
  constructor <;> intro h A hA r hr
  · obtain ⟨K, hK1, ⟨hK2, _⟩, hK4⟩ := h hA r hr
    refine ⟨K, hK1, ?_, hK4⟩
    simp only [Function.comp_apply]
    exact hK2.closure
  · obtain ⟨K, hK1, hK2, hK3⟩ := h hA r hr
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [isClosed_c

中文:
引理 innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
  证明: by
  constructor <;> intro h A hA r hr
  · obtain ⟨K, hK1, ⟨hK2, _⟩, hK4⟩ := h hA r hr
    refine ⟨K, hK1, ?_, hK4⟩
    simp only [Function.comp_apply]
    exact hK2.closure
  · obtain ⟨K, hK1, hK2, hK3⟩ := h hA r hr
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [isClosed_c

Depends on / 依赖: BddLat, ConcreteCategory, ConcreteCategory.hom, Function, Function.comp_apply, and_true, closure, closure_minimal, comp_apply, hK2.closure, hK3.trans_le, isClosed_closure, measure_mono, subset_closure, trans_le
-/
lemma innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
    [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  constructor <;> intro h A hA r hr
  · obtain ⟨K, hK1, ⟨hK2, _⟩, hK4⟩ := h hA r hr
    refine ⟨K, hK1, ?_, hK4⟩
    simp only [Function.comp_apply]
    exact hK2.closure
  · obtain ⟨K, hK1, hK2, hK3⟩ := h hA r hr
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [isClosed_closure, and_true]
    · exact hK3.trans_le (measure_mono subset_closure)

/--
lemma `innerRegularWRT_isCompact_isClosed_iff` / 引理 `innerRegularWRT_isCompact_isClosed_iff`

English:
lemma innerRegularWRT_isCompact_isClosed_iff
  given: [TopologicalSpace α] [R1Space α]
  proof: innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

中文:
引理 innerRegularWRT_isCompact_isClosed_iff
  条件: [拓扑空间 α] [R1空间 α]
  证明: innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

Depends on / 依赖: innerRegularWRT_isCompact_closure_iff, innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure, innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
-/
lemma innerRegularWRT_isCompact_isClosed_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT IsCompact IsClosed :=
  innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

/--
theorem `innerRegularWRT_of_exists_compl_lt` / 定理 `innerRegularWRT_of_exists_compl_lt`

English:
theorem innerRegularWRT_of_exists_compl_lt
  statement: {p q : Set α -> Prop} (hpq : forall A B, p A -> q B -> p (A inter B))
  proof: by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : exists K, p K ∧ K subseteq A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' inter A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x => ?_).trans_lt hK'_l

中文:
定理 innerRegularWRT_of_存在_compl_lt
  结论: {p q : 集合 α -> 命题} (hpq : 对任意 A B, p A -> q B -> p (A inter B))
  证明: by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : exists K, p K ∧ K subseteq A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' inter A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x => ?_).trans_lt hK'_l

Depends on / 依赖: and_imp, f.hom, hK_subset, h_lt, imp_self, imp_true_iff, inter_subset_right, le_measure_sdiff, le_measure_sdiff.trans_lt, lt_of_tsub_lt_, measure_mono, mem_compl_iff, mem_sdiff, sdiff_inter_self_eq_sdiff, subseteq, trans_lt, tsub_pos_of_lt
-/
theorem innerRegularWRT_of_exists_compl_lt {p q : Set α -> Prop} (hpq : forall A B, p A -> q B -> p (A inter B))
    (hμ : forall ε, 0 < ε -> exists K, p K ∧ μ Kᶜ < ε) :
    μ.InnerRegularWRT p q := by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : exists K, p K ∧ K subseteq A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' inter A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x => ?_).trans_lt hK'_lt
      simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, mem_compl_iff, and_imp, imp_self,
        imp_true_iff]
  refine ⟨K, hK_subset, hK, ?_⟩
  have h_lt' : μ A - μ K < μ A - r := le_measure_sdiff.trans_lt h_lt
  exact lt_of_tsub_lt_tsub_left h_lt'

/--
theorem `innerRegularWRT_isCompact_closure_of_univ` / 定理 `innerRegularWRT_isCompact_closure_of_univ`

English:
theorem innerRegularWRT_isCompact_closure_of_univ
  statement: [TopologicalSpace α]
  proof: by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht => ?_) hμ
  have : IsCompact (closure s inter t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]

中文:
定理 innerRegularWRT_isCompact_closure_of_univ
  结论: [拓扑空间 α]
  证明: by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht => ?_) hμ
  have : IsCompact (closure s inter t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]

Depends on / 依赖: IsClosed, IsClosed.closure_eq, IsCompact, closure, closure_eq, closure_inter_subset_inter_closure, hs.inter_right, innerRegularWRT_of_exists_compl_lt, inter_right, isClosed_closure, of_isClosed_subset, this.of_isClosed_subset, trans_eq
-/
theorem innerRegularWRT_isCompact_closure_of_univ [TopologicalSpace α]
    (hμ : forall ε, 0 < ε -> exists K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht => ?_) hμ
  have : IsCompact (closure s inter t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]

/--
theorem `exists_isCompact_closure_measure_compl_lt` / 定理 `exists_isCompact_closure_measure_compl_lt`

English:
theorem exists_isCompact_closure_measure_compl_lt
  statement: [TopologicalSpace α]
  proof: by
  /-
  If α is empty, the result is trivial.

  Otherwise, fix a dense sequence `seq` and an antitone basis `t` of entourages. We find a sequence
  of natural numbers `u n`, such that `interUnionBalls seq u t`, which is the intersection over
  `n` of the `t n`-neighborhood of `seq 1, ..., seq (u 

中文:
定理 存在_isCompact_closure_measure_compl_lt
  结论: [拓扑空间 α]
  证明: by
  /-
  If α is empty, the result is trivial.

  Otherwise, fix a dense sequence `seq` and an antitone basis `t` of entourages. We find a sequence
  of natural numbers `u n`, such that `interUnionBalls seq u t`, which is the intersection over
  `n` of the `t n`-neighborhood of `seq 1, ..., seq (u 
-/
theorem exists_isCompact_closure_measure_compl_lt [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] (ε : Real>=0∞) (hε : 0 < ε) :
    exists K, IsCompact (closure K) ∧ P Kᶜ < ε := by
  /-
  If α is empty, the result is trivial.

  Otherwise, fix a dense sequence `seq` and an antitone basis `t` of entourages. We find a sequence
  of natural numbers `u n`, such that `interUnionBalls seq u t`, which is the intersection over
  `n` of the `t n`-neighborhood of `seq 1, ..., seq (u n)`, covers the space arbitrarily well.
  -/
  let := upgradeIsCompletelyPseudoMetrizable α
  cases isEmpty_or_nonempty α
  case inl =>
    refine ⟨∅, by simp, ?_⟩
    rwa [Set.eq_empty_of_isEmpty ∅ᶜ, measure_empty]
  case inr =>
    let seq := TopologicalSpace.denseSeq α
    have hseq_dense : DenseRange seq := TopologicalSpace.denseRange_denseSeq α
    obtain ⟨t : Nat -> SetRel α α,
        ht : forall i, t i in 𝓤 α ∧ IsOpen (t i) ∧ (t i).IsSymm,
        h_basis : (uniformity α).HasAntitoneBasis t⟩ :=
      (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
    choose htu hto _ using ht
    let f : Nat -> Nat -> Set α := fun n m => UniformSpace.ball (seq m) (t n)
    have h_univ n : (⋃ m, f n m) = univ := hseq_dense.iUnion_uniformity_ball (htu n)
    have h3 n (ε : Real>=0∞) (hε : 0 < ε) : exists m, P (⋂ m' <= m, (f n m')ᶜ) < ε := by
      refine exists_measure_iInter_lt (fun m => ?_) hε ⟨0, measure_ne_top P _⟩ ?_
      · exact (measurable_prodMk_left (hto n).measurableSet).compl.nullMeasurableSet
      · rw [← compl_iUnion, h_univ, compl_univ]
    choose! s' s'bound using h3
    rcases ENNReal.exists_pos_sum_of_countable' (ne_of_gt hε) Nat with ⟨δ, hδ1, hδ2⟩
    let u : Nat -> Nat := fun n => s' n (δ n)
    refine ⟨interUnionBalls seq u t, isCompact_closure_interUnionBalls h_basis.toHasBasis seq u, ?_⟩
    rw [interUnionBalls]; rw [Set.compl_iInter]
    refine ((measure_iUnion_le _).trans ?_).trans_lt hδ2
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    have h'' n : Prod.swap ⁻¹' t n = t n := by ext; exact (t n).comm
    simp only [h'', compl_iUnion, ge_iff_le]
    exact (s'bound n (δ n) (hδ1 n)).le

/--
theorem `innerRegularWRT_isCompact_closure` / 定理 `innerRegularWRT_isCompact_closure`

English:
theorem innerRegularWRT_isCompact_closure
  statement: [TopologicalSpace α]
  proof: innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_compl_lt P)

中文:
定理 innerRegularWRT_isCompact_closure
  结论: [拓扑空间 α]
  证明: innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_compl_lt P)

Depends on / 依赖: exists_isCompact_closure_measure_compl_lt, innerRegularWRT_isCompact_closure_of_univ
-/
theorem innerRegularWRT_isCompact_closure [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (IsCompact ∘ closure) IsClosed :=
  innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_compl_lt P)

/--
theorem `innerRegularWRT_isCompact_isClosed` / 定理 `innerRegularWRT_isCompact_isClosed`

English:
theorem innerRegularWRT_isCompact_isClosed
  statement: [TopologicalSpace α]
  proof: by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure P

中文:
定理 innerRegularWRT_isCompact_isClosed
  结论: [拓扑空间 α]
  证明: by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure P

Depends on / 依赖: innerRegularWRT_isCompact_closure, innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
-/
theorem innerRegularWRT_isCompact_isClosed [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) IsClosed := by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure P

/--
theorem `innerRegularWRT_isCompact` / 定理 `innerRegularWRT_isCompact`

English:
theorem innerRegularWRT_isCompact
  statement: [TopologicalSpace α]
  proof: by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure P

中文:
定理 innerRegularWRT_isCompact
  结论: [拓扑空间 α]
  证明: by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure P

Depends on / 依赖: innerRegularWRT_isCompact_closure, innerRegularWRT_isCompact_closure_iff
-/
theorem innerRegularWRT_isCompact [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsClosed := by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure P

/--
theorem `innerRegularWRT_isCompact_isClosed_isOpen` / 定理 `innerRegularWRT_isCompact_isClosed_isOpen`

English:
theorem innerRegularWRT_isCompact_isClosed_isOpen
  statement: [TopologicalSpace α]
  proof: (innerRegularWRT_isCompact_isClosed P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

中文:
定理 innerRegularWRT_isCompact_isClosed_isOpen
  结论: [拓扑空间 α]
  证明: (innerRegularWRT_isCompact_isClosed P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

Depends on / 依赖: InnerRegularWRT, Measure, Measure.InnerRegularWRT.of_pseudoMetrizableSpace, innerRegularWRT_isCompact_isClosed, of_pseudoMetrizableSpace
-/
theorem innerRegularWRT_isCompact_isClosed_isOpen [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) IsOpen :=
  (innerRegularWRT_isCompact_isClosed P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

/--
theorem `innerRegularWRT_isCompact_isOpen` / 定理 `innerRegularWRT_isCompact_isOpen`

English:
theorem innerRegularWRT_isCompact_isOpen
  statement: [TopologicalSpace α]
  proof: (innerRegularWRT_isCompact P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

中文:
定理 innerRegularWRT_isCompact_isOpen
  结论: [拓扑空间 α]
  证明: (innerRegularWRT_isCompact P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

Depends on / 依赖: InnerRegularWRT, Measure, Measure.InnerRegularWRT.of_pseudoMetrizableSpace, innerRegularWRT_isCompact, of_pseudoMetrizableSpace
-/
theorem innerRegularWRT_isCompact_isOpen [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsOpen :=
  (innerRegularWRT_isCompact P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

/--
Instance `instInnerRegularOfIsCompletelyPseudoMetrizableSpace` / 实例 `instInnerRegularOfIsCompletelyPseudoMetrizableSpace`

English:
instance instInnerRegularOfIsCompletelyPseudoMetrizableSpace
  signature: [TopologicalSpace α]
  body: by
  suffices P.InnerRegularCompactLTTop from inferInstance
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen P
  · exact fun s t hs_compact ht_open => hs_compact.inter_right ht_open.isClosed_compl

中文:
实例 instInnerRegularOfIsCompletelyPseudoMetrizableSpace
  签名: [拓扑空间 α]
  定义体: by
  suffices P.InnerRegularCompactLTTop from inferInstance
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen P
  · exact fun s t hs_compact ht_open => hs_compact.inter_right ht_open.isClosed_compl

Depends on / 依赖: InnerRegularCompactLTTop, InnerRegularWRT, Measure, Measure.InnerRegularWRT.measurableSet_of_isOpen, P.InnerRegularCompactLTTop, hs_compact, hs_compact.inter_right, ht_open, ht_open.isClosed_compl, innerRegularWRT_isCompact_isOpen, inter_right, isClosed_compl, measurableSet_of_isOpen
-/
instance instInnerRegularOfIsCompletelyPseudoMetrizableSpace [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegular := by
  suffices P.InnerRegularCompactLTTop from inferInstance
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen P
  · exact fun s t hs_compact ht_open => hs_compact.inter_right ht_open.isClosed_compl

/--
Instance `instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace` / 实例 `instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace`

English:
instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace
  body: by
  constructor
  intro A ⟨hA1, hA2⟩ r hr
  have := Fact.mk hA2.lt_top
  have hA2' : (μ.restrict A) A != ⊤ := by
    rwa [Measure.restrict_apply_self]
  have hr' : r < μ.restrict A A := by
    rwa [Measure.restrict_apply_self]
  obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := MeasurableSet.exists_lt_isCompact_of_ne

中文:
实例 instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace
  定义体: by
  constructor
  intro A ⟨hA1, hA2⟩ r hr
  have := Fact.mk hA2.lt_top
  have hA2' : (μ.restrict A) A != ⊤ := by
    rwa [Measure.restrict_apply_self]
  have hr' : r < μ.restrict A A := by
    rwa [Measure.restrict_apply_self]
  obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := MeasurableSet.exists_lt_isCompact_of_ne

Depends on / 依赖: Fact.mk, MeasurableSet, MeasurableSet.exists_lt_isCompact_of_ne_top, Measure, Measure.restrict_apply_self, Measure.restrict_eq_self, exists_lt_isCompact_of_ne_top, hA2.lt_top, lt_top, restrict, restrict_apply_self, restrict_eq_self
-/
instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace
    [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α] (μ : Measure α) :
    μ.InnerRegularCompactLTTop := by
  constructor
  intro A ⟨hA1, hA2⟩ r hr
  have := Fact.mk hA2.lt_top
  have hA2' : (μ.restrict A) A != ⊤ := by
    rwa [Measure.restrict_apply_self]
  have hr' : r < μ.restrict A A := by
    rwa [Measure.restrict_apply_self]
  obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := MeasurableSet.exists_lt_isCompact_of_ne_top hA1 hA2' hr'
  use K, hK1, hK2
  rwa [Measure.restrict_eq_self μ hK1] at hK3

/--
theorem `innerRegular_isCompact_isClosed_measurableSet_of_finite` / 定理 `innerRegular_isCompact_isClosed_measurableSet_of_finite`

English:
theorem innerRegular_isCompact_isClosed_measurableSet_of_finite
  statement: [TopologicalSpace α]
  proof: by
  suffices P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s)
      fun s => MeasurableSet s ∧ P s != ∞ by
    convert! this
    simp only [iff_self_and]
    exact fun _ => measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isC

中文:
定理 innerRegular_isCompact_isClosed_measurableSet_of_finite
  结论: [拓扑空间 α]
  证明: by
  suffices P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s)
      fun s => MeasurableSet s ∧ P s != ∞ by
    convert! this
    simp only [iff_self_and]
    exact fun _ => measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isC

Depends on / 依赖: InnerRegularWRT, IsClosed, IsCompact, MeasurableSet, Measure, Measure.InnerRegularWRT.measurableSet_of_isOpen, P.InnerRegularWRT, convert, hs_closed, hs_closed.inter, hs_compact, hs_compact.inter_right, ht_open, ht_open.isClosed_compl, iff_self_and, innerRegularWRT_isCompact_isClosed_isOpen, inter_right, isClosed_compl, isClosed_compl_iff, isClosed_compl_iff.mpr
-/
theorem innerRegular_isCompact_isClosed_measurableSet_of_finite [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
  suffices P.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s)
      fun s => MeasurableSet s ∧ P s != ∞ by
    convert! this
    simp only [iff_self_and]
    exact fun _ => measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isClosed_isOpen P
  · rintro s t ⟨hs_compact, hs_closed⟩ ht_open
    rw [sdiff_eq]
    exact ⟨hs_compact.inter_right ht_open.isClosed_compl,
      hs_closed.inter (isClosed_compl_iff.mpr ht_open)⟩

end MeasureTheory
