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

/-
**MeasureTheory.innerRegularWRT_isCompact_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_closure_iff [TopologicalSpace α] [R1Space α] : μ
.InnerRegularWRT (IsCompact ∘ closure) IsClosed ↔ μ.InnerRegularWRT IsCompact Is
Closed
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
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
/-
**MeasureTheory.innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact
_closure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure [
TopologicalSpace α] [R1Space α] : μ.InnerRegularWRT (fun s => IsCompact s ∧ IsCl
osed s) IsClosed ↔ μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
    [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
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
/-
**MeasureTheory.innerRegularWRT_isCompact_isClosed_iff** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_isClosed_iff [TopologicalSpace α] [R1Space α] : 
μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) IsClosed ↔ μ.InnerRegularW
RT IsCompact IsClosed
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `MeasureTheory.innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isC
ompact_closure`：innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact
_closure [TopologicalSpace α] [R1Space α] : μ.InnerRegularWRT (fun s => IsCo…
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_closure_iff`：innerRegularWRT_isC
ompact_closure_iff [TopologicalSpace α] [R1Space α] : μ.InnerRegularWRT (IsCompa
ct ∘ closure) IsClosed ↔ μ.InnerRegularWR…
-/
lemma innerRegularWRT_isCompact_isClosed_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT IsCompact IsClosed :=
  innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

/--
If predicate `p` is preserved under intersections with sets satisfying predicate `q`, and sets
satisfying `p` cover the space arbitrarily well, then `μ` is inner regular with respect to
predicates `p` and `q`.
-/
/-
**MeasureTheory.innerRegularWRT_of_exists_compl_lt** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：innerRegularWRT_of_exists_compl_lt {p q : Set α -> Prop} (hpq : forall A B
, p A -> q B -> p (A inter B)) (hμ : forall ε, 0 < ε -> exists K, p K ∧ μ Kᶜ < ε
) : μ.InnerRegularWRT p q
参数：hpq : forall A B, p A -> q B -> p (A inter B)；hμ : forall ε, 0 < ε -> exists 
K, p K ∧ μ Kᶜ < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `MeasureTheory.le_measure_sdiff`：le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ 
\ s₂)
· 使用定理 `lt_of_tsub_lt_tsub_left`：lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c
 < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal

--- 原说明 ---
If predicate `p` is preserved under intersections with sets satisfying predicate
 `q`, and sets
satisfying `p` cover the space arbitrarily well, then `μ` is inner regular with 
respect to
predicates `p` and `q`.
-/
theorem innerRegularWRT_of_exists_compl_lt {p q : Set α → Prop} (hpq : ∀ A B, p A → q B → p (A ∩ B))
    (hμ : ∀ ε, 0 < ε → ∃ K, p K ∧ μ Kᶜ < ε) :
    μ.InnerRegularWRT p q := by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : ∃ K, p K ∧ K ⊆ A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' ∩ A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x ↦ ?_).trans_lt hK'_lt
      simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, mem_compl_iff, and_imp, imp_self,
        imp_true_iff]
  refine ⟨K, hK_subset, hK, ?_⟩
  have h_lt' : μ A - μ K < μ A - r := le_measure_sdiff.trans_lt h_lt
  exact lt_of_tsub_lt_tsub_left h_lt'
/-
**MeasureTheory.innerRegularWRT_isCompact_closure_of_univ** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_closure_of_univ [TopologicalSpace α] (hμ : foral
l ε, 0 < ε -> exists K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) : μ.InnerRegularWRT 
(IsCompact ∘ closure) IsClosed
参数：hμ : forall ε, 0 < ε -> exists K, IsCompact (closure K) ∧ μ (Kᶜ) < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.innerRegularWRT_of_exists_compl_lt`：innerRegularWRT_of_exi
sts_compl_lt {p q : Set α -> Prop} (hpq : forall A B, p A -> q B -> p (A inter B
)) (hμ : forall ε, 0 < ε -> exists K, …
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `closure_inter_subset_inter_closure`：closure_inter_subset_inter_closure (
s t : Set X) : closure (s inter t) subseteq closure s inter closure t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem innerRegularWRT_isCompact_closure_of_univ [TopologicalSpace α]
    (hμ : ∀ ε, 0 < ε → ∃ K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht ↦ ?_) hμ
  have : IsCompact (closure s ∩ t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]
/-
**MeasureTheory.exists_isCompact_closure_measure_compl_lt** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：exists_isCompact_closure_measure_compl_lt [TopologicalSpace α] [SecondCoun
tableTopology α] [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] 
(P : Measure α) [IsFiniteMeasure P] (ε : Real>=0∞) (hε : 0 < ε) : exists K, IsCo
mpact (closure K) ∧ P Kᶜ < ε
参数：P : Measure α；ε : Real>=0∞；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.denseRange_denseSeq`：denseRange_denseSeq [SeparableSpac
e α] [Nonempty α] : DenseRange (denseSeq α)
· 使用定理 `Filter.HasBasis.exists_antitone_subbasis`：∀ {α : Type u_1} {ι' : Sort u_
5} {f : Filter α} [h : f.IsCountablyGenerated] {p : ι' → Prop} {s : ι' → Set α},
   f.HasBasis p s → ∃ x, (∀ (i…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `uniformity_hasBasis_open_symmetric`：uniformity_hasBasis_open_symmetric :
 HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id
· 使用引理 `DenseRange.iUnion_uniformity_ball`：DenseRange.iUnion_uniformity_ball {ι 
: Type*} {xs : ι -> α} (xs_dense : DenseRange xs) {U : SetRel α α} (hU : U in un
iformity α) : ⋃ i, Unif…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.exists_measure_iInter_lt`：exists_measure_iInter_lt {α ι : 
Type*} {_ : MeasurableSpace α} {μ : Measure α} [SemilatticeSup ι] [Countable ι] 
{f : ι -> Set α} (hm : foral…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
（共 53 条，此处仅展示前 30 条）
-/
theorem exists_isCompact_closure_measure_compl_lt [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact (closure K) ∧ P Kᶜ < ε := by
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
    obtain ⟨t : ℕ → SetRel α α,
        ht : ∀ i, t i ∈ 𝓤 α ∧ IsOpen (t i) ∧ (t i).IsSymm,
        h_basis : (uniformity α).HasAntitoneBasis t⟩ :=
      (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
    choose htu hto _ using ht
    let f : ℕ → ℕ → Set α := fun n m ↦ UniformSpace.ball (seq m) (t n)
    have h_univ n : (⋃ m, f n m) = univ := hseq_dense.iUnion_uniformity_ball (htu n)
    have h3 n (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ m, P (⋂ m' ≤ m, (f n m')ᶜ) < ε := by
      refine exists_measure_iInter_lt (fun m ↦ ?_) hε ⟨0, measure_ne_top P _⟩ ?_
      · exact (measurable_prodMk_left (hto n).measurableSet).compl.nullMeasurableSet
      · rw [← compl_iUnion, h_univ, compl_univ]
    choose! s' s'bound using h3
    rcases ENNReal.exists_pos_sum_of_countable' (ne_of_gt hε) ℕ with ⟨δ, hδ1, hδ2⟩
    let u : ℕ → ℕ := fun n ↦ s' n (δ n)
    refine ⟨interUnionBalls seq u t, isCompact_closure_interUnionBalls h_basis.toHasBasis seq u, ?_⟩
    rw [interUnionBalls, Set.compl_iInter]
    refine ((measure_iUnion_le _).trans ?_).trans_lt hδ2
    refine ENNReal.tsum_le_tsum (fun n ↦ ?_)
    have h'' n : Prod.swap ⁻¹' t n = t n := by ext; exact (t n).comm
    simp only [h'', compl_iUnion, ge_iff_le]
    exact (s'bound n (δ n) (hδ1 n)).le
/-
**MeasureTheory.innerRegularWRT_isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：innerRegularWRT_isCompact_closure [TopologicalSpace α] [SecondCountableTop
ology α] [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] (P : Mea
sure α) [IsFiniteMeasure P] : P.InnerRegularWRT (IsCompact ∘ closure) IsClosed
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_closure_of_univ`：innerRegularWRT
_isCompact_closure_of_univ [TopologicalSpace α] (hμ : forall ε, 0 < ε -> exists 
K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) : μ.In…
· 使用定理 `MeasureTheory.exists_isCompact_closure_measure_compl_lt`：exists_isCompac
t_closure_measure_compl_lt [TopologicalSpace α] [SecondCountableTopology α] [IsC
ompletelyPseudoMetrizableSpace α] [OpensMeasu…
-/
theorem innerRegularWRT_isCompact_closure [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (IsCompact ∘ closure) IsClosed :=
  innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_compl_lt P)
/-
**MeasureTheory.innerRegularWRT_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：innerRegularWRT_isCompact_isClosed [TopologicalSpace α] [SecondCountableTo
pology α] [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] (P : Me
asure α) [IsFiniteMeasure P] : P.InnerRegularWRT (fun s => IsCompact s ∧ IsClose
d s) IsClosed
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isC
ompact_closure`：innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact
_closure [TopologicalSpace α] [R1Space α] : μ.InnerRegularWRT (fun s => IsCo…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_closure`：innerRegularWRT_isCompa
ct_closure [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoM
etrizableSpace α] [OpensMeasurableSpa…
-/
theorem innerRegularWRT_isCompact_isClosed [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed := by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure P
/-
**MeasureTheory.innerRegularWRT_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：innerRegularWRT_isCompact [TopologicalSpace α] [SecondCountableTopology α]
 [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] (P : Measure α) 
[IsFiniteMeasure P] : P.InnerRegularWRT IsCompact IsClosed
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_closure_iff`：innerRegularWRT_isC
ompact_closure_iff [TopologicalSpace α] [R1Space α] : μ.InnerRegularWRT (IsCompa
ct ∘ closure) IsClosed ↔ μ.InnerRegularWR…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_closure`：innerRegularWRT_isCompa
ct_closure [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoM
etrizableSpace α] [OpensMeasurableSpa…
-/
theorem innerRegularWRT_isCompact [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsClosed := by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure P
/-
**MeasureTheory.innerRegularWRT_isCompact_isClosed_isOpen** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_isClosed_isOpen [TopologicalSpace α] [SecondCoun
tableTopology α] [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] 
(P : Measure α) [IsFiniteMeasure P] : P.InnerRegularWRT (fun s => IsCompact s ∧ 
IsClosed s) IsOpen
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.trans`：trans {q' : Set α -> Prop} 
(H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') : InnerRegularWRT μ p 
q'
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_isClosed`：innerRegularWRT_isComp
act_isClosed [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseud
oMetrizableSpace α] [OpensMeasurableSp…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.of_pseudoMetrizableSpace`：of_pseud
oMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X] [Mea
surableSpace X] (μ : Measure X) : InnerRegularWRT μ …
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
-/
theorem innerRegularWRT_isCompact_isClosed_isOpen [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsOpen :=
  (innerRegularWRT_isCompact_isClosed P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)
/-
**MeasureTheory.innerRegularWRT_isCompact_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：innerRegularWRT_isCompact_isOpen [TopologicalSpace α] [SecondCountableTopo
logy α] [IsCompletelyPseudoMetrizableSpace α] [OpensMeasurableSpace α] (P : Meas
ure α) [IsFiniteMeasure P] : P.InnerRegularWRT IsCompact IsOpen
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.trans`：trans {q' : Set α -> Prop} 
(H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') : InnerRegularWRT μ p 
q'
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact`：innerRegularWRT_isCompact [Topo
logicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α
] [OpensMeasurableSpace α] (P…
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.of_pseudoMetrizableSpace`：of_pseud
oMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X] [Mea
surableSpace X] (μ : Measure X) : InnerRegularWRT μ …
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
-/
theorem innerRegularWRT_isCompact_isOpen [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsOpen :=
  (innerRegularWRT_isCompact P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

/--
A finite measure `μ` on a completely pseudo-metrizable space `E` with
`SecondCountableTopology E` is inner regular. In other words, a finite measure
on such a space is a tight measure.
-/
/-
**MeasureTheory.instInnerRegularOfIsCompletelyPseudoMetrizableSpace** 是 Mathlib 
中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：instInnerRegularOfIsCompletelyPseudoMetrizableSpace [TopologicalSpace α] [
SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [BorelSpace α] 
(P : Measure α) [IsFiniteMeasure P] : P.InnerRegular
参数：P : Measure α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.measurableSet_of_isOpen`：measurabl
eSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen) (hd : forall ⦃s
 U⦄, p s -> IsOpen U -> p (s \ U)) : InnerRegularWR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_isOpen`：innerRegularWRT_isCompac
t_isOpen [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoMet
rizableSpace α] [OpensMeasurableSpac…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.instInnerRegularOfSigmaFi
nite`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
[inst_1 : TopologicalSpace α]   [μ.InnerRegularCompactLTTop] [Meas…
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…

--- 原说明 ---
A finite measure `μ` on a completely pseudo-metrizable space `E` with
`SecondCountableTopology E` is inner regular. In other words, a finite measure
on such a space is a tight measure.
-/
instance instInnerRegularOfIsCompletelyPseudoMetrizableSpace [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegular := by
  suffices P.InnerRegularCompactLTTop from inferInstance
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen P
  · exact fun s t hs_compact ht_open ↦ hs_compact.inter_right ht_open.isClosed_compl

/--
A measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with `SecondCountableTopology E`
is inner regular for finite measure sets with respect to compact sets.
-/
/-
**MeasureTheory.instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace*
* 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace [Topologic
alSpace α] [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [Bo
relSpace α] (μ : Measure α) : μ.InnerRegularCompactLTTop
参数：μ : Measure α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
· 使用定理 `MeasurableSet.exists_lt_isCompact_of_ne_top`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [
μ.InnerRegularCompactLTTop] ⦃A : …
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s

--- 原说明 ---
A measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with `SecondCoun
tableTopology E`
is inner regular for finite measure sets with respect to compact sets.
-/
instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace
    [TopologicalSpace α] [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α] (μ : Measure α) :
    μ.InnerRegularCompactLTTop := by
  constructor
  intro A ⟨hA1, hA2⟩ r hr
  have := Fact.mk hA2.lt_top
  have hA2' : (μ.restrict A) A ≠ ⊤ := by
    rwa [Measure.restrict_apply_self]
  have hr' : r < μ.restrict A A := by
    rwa [Measure.restrict_apply_self]
  obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := MeasurableSet.exists_lt_isCompact_of_ne_top hA1 hA2' hr'
  use K, hK1, hK2
  rwa [Measure.restrict_eq_self μ hK1] at hK3
/-
**MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：innerRegular_isCompact_isClosed_measurableSet_of_finite [TopologicalSpace 
α] [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [BorelSpace
 α] (P : Measure α) [IsFiniteMeasure P] : P.InnerRegularWRT (fun s => IsCompact 
s ∧ IsClosed s) MeasurableSet
参数：P : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularWRT.measurableSet_of_isOpen`：measurabl
eSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen) (hd : forall ⦃s
 U⦄, p s -> IsOpen U -> p (s \ U)) : InnerRegularWR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.innerRegularWRT_isCompact_isClosed_isOpen`：innerRegularWRT
_isCompact_isClosed_isOpen [TopologicalSpace α] [SecondCountableTopology α] [IsC
ompletelyPseudoMetrizableSpace α] [OpensMeasu…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem innerRegular_isCompact_isClosed_measurableSet_of_finite [TopologicalSpace α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  suffices P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s)
      fun s ↦ MeasurableSet s ∧ P s ≠ ∞ by
    convert! this
    simp only [iff_self_and]
    exact fun _ ↦ measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isClosed_isOpen P
  · rintro s t ⟨hs_compact, hs_closed⟩ ht_open
    rw [sdiff_eq]
    exact ⟨hs_compact.inter_right ht_open.isClosed_compl,
      hs_closed.inter (isClosed_compl_iff.mpr ht_open)⟩

end MeasureTheory

