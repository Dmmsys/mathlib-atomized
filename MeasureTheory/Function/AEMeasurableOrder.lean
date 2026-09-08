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

/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
/-
**MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} 
{m : MeasurableSpace α} (μ : Measure α) {β : Type*} [CompleteLinearOrder β] [Den
selyOrdered β] [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β
] [MeasurableSpace β] [BorelSpace β] (s : Set β) (s_count : s.Countable) (s_dens
e : Dense s) (f : α -> β) (h : forall p in s, forall q in s, p < q -> exists u v
, MeasurableSet u ∧ MeasurableSet v ∧ { x | f x < p } subseteq u ∧ { x | q < f x
 } subseteq v ∧ μ (u inter
参数：μ : Measure α；s : Set β；s_count : s.Countable；s_dense : Dense s；f : α -> β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Measurable.iInf`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Measurable.piecewise`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g :
 α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β}   {x : DecidablePred fu
n x => x ∈…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` ha
ve measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost
-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense 
set.
-/
theorem MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*}
    {m : MeasurableSpace α} (μ : Measure α) {β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β]
    [BorelSpace β] (s : Set β) (s_count : s.Countable) (s_dense : Dense s) (f : α → β)
    (h : ∀ p ∈ s, ∀ q ∈ s, p < q → ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ := by
  classical
  have : Encodable s := s_count.toEncodable
  have h' : ∀ p q, ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ (p ∈ s → q ∈ s → p < q → μ (u ∩ v) = 0) := by
    intro p q
    by_cases H : p ∈ s ∧ q ∈ s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun _ _ _ => hμ⟩
    · refine
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => ?_⟩
      exact (H ⟨ps, qs, pq⟩).elim
  choose! u v huv using h'
  let u' : β → Set α := fun p => ⋂ q ∈ s ∩ Ioi p, u p q
  have u'_meas : ∀ i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono inter_subset_left) fun b _ => (huv i b).1
  let f' : α → β := fun x => ⨅ i : s, piecewise (u' i) (fun _ => (i : β)) (fun _ => (⊤ : β)) x
  have f'_meas : Measurable f' := by fun_prop (disch := simp_all)
  let t := ⋃ (p : s) (q : ↥(s ∩ Ioi p)), u' p ∩ v p q
  have μt : μ t ≤ 0 :=
    calc
      μ t ≤ ∑' (p : s) (q : ↥(s ∩ Ioi p)), μ (u' p ∩ v p q) := by
        refine (measure_iUnion_le _).trans ?_
        refine ENNReal.tsum_le_tsum fun p => ?_
        have := (s_count.mono (s.inter_subset_left (t := Ioi ↑p))).to_subtype
        apply measure_iUnion_le
      _ ≤ ∑' (p : s) (q : ↥(s ∩ Ioi p)), μ (u p q ∩ v p q) := by
        gcongr with p q
        exact biInter_subset_of_mem q.2
      _ = ∑' (p : s) (_ : ↥(s ∩ Ioi p)), (0 : ℝ≥0∞) := by grind
      _ = 0 := by simp only [tsum_zero]
  have ff' : ∀ᵐ x ∂μ, f x = f' x := by
    have : ∀ᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymm μt bot_le
      change μ _ = 0
      convert! this
      ext y
      simp only [mem_ofPred_eq, mem_compl_iff, not_notMem]
    filter_upwards [this] with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x ∈ u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_notMem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (i : β) (f x) ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) isOpen_Ioo (nonempty_Ioo.2 hx)
      have A : x ∈ v i r := (huv i r).2.2.2.1 rq
      refine mem_iUnion.2 ⟨i, ?_⟩
      refine mem_iUnion.2 ⟨⟨r, ⟨rs, xr⟩⟩, ?_⟩
      exact ⟨H, A⟩
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (f x) q ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) isOpen_Ioo (nonempty_Ioo.2 hq)
      refine ⟨⟨r, rs⟩, ?_⟩
      have A : x ∈ u' r := mem_biInter fun i _ => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem]
  exact ⟨f', f'_meas, ff'⟩

/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
/-
**ENNReal.aemeasurable_of_exist_almost_disjoint_supersets** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：ENNReal.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} {m : M
easurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) (h : forall (p : Real>=0) 
(q : Real>=0), p < q -> exists u v, MeasurableSet u ∧ MeasurableSet v ∧ { x | f 
x < p } subseteq u ∧ { x | (q : Real>=0∞) < f x } subseteq v ∧ μ (u inter v) = 0
) : AEMeasurable f μ
参数：μ : Measure α；f : α -> Real>=0∞；h : forall (p : Real>=0) (q : Real>=0), p < q
 -> exists u v, MeasurableSet u ∧ MeasurableSet v ∧ { x | f x < p } subseteq u ∧
 { x | (q : Real>=0∞) < f x } subseteq v ∧ μ (u inter v) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_countable_dense_no_zero_top`：exists_countable_dense_no_ze
ro_top : exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s
· 使用定理 `MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets`：MeasureTh
eory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} {m : Measurable
Space α} (μ : Measure α) {β : Type*} [CompleteLinea…
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q

--- 原说明 ---
If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}`
 have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numb
ers satisfying
`p < q`, then `f` is almost-everywhere measurable.
-/
theorem ENNReal.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) (f : α → ℝ≥0∞)
    (h : ∀ (p : ℝ≥0) (q : ℝ≥0), p < q →
      ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
        { x | f x < p } ⊆ u ∧ { x | (q : ℝ≥0∞) < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ := by
  obtain ⟨s, s_count, s_dense, _, s_top⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : ∀ x ∈ s, x ≠ ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to ℝ≥0 using I p hp
  lift q to ℝ≥0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)
