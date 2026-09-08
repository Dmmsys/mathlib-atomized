/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Constructing a vector measure from an additive content

Consider a content defined on a semiring of sets. We investigate in this file
whether it is possible to extend it to a (countably additive) vector measure on the whole
sigma-algebra. We show that this is possible when the content is dominated by a finite
measure, see `exists_extension_of_isSetSemiring_of_le_measure`.
-/

@[expose] public section

open MeasurableSpace
open scoped symmDiff

namespace MeasureTheory.VectorMeasure

variable {α : Type*} {hα : MeasurableSpace α} {E : Type*} [NormedAddCommGroup E]
  [CompleteSpace E] {μ : Measure α}

/-- A finitely additive vector measure which is dominated by a finite positive measure is in
fact countably additive. -/
/-
**MeasureTheory.VectorMeasure.of_additive_of_le_measure** 是 Mathlib 中的一个定义，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：of_additive_of_le_measure (m : Set α -> E) (hm : forall s, ‖m s‖ₑ <= μ s) 
[IsFiniteMeasure μ] (h'm : forall s t, MeasurableSet s -> MeasurableSet t -> Dis
joint s t -> m (s union t) = m s + m t) (h''m : forall s, ¬ MeasurableSet s -> m
 s = 0) : VectorMeasure α E where measureOf'
参数：m : Set α -> E；hm : forall s, ‖m s‖ₑ <= μ s；h'm : forall s t, MeasurableSet s
 -> MeasurableSet t -> Disjoint s t -> m (s union t) = m s + m t；h''m : forall s
, ¬ MeasurableSet s -> m s = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finitely additive vector measure which is dominated by a finite positive measu
re is in
fact countably additive.
-/
def of_additive_of_le_measure
    (m : Set α → E) (hm : ∀ s, ‖m s‖ₑ ≤ μ s) [IsFiniteMeasure μ]
    (h'm : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t)
    (h''m : ∀ s, ¬ MeasurableSet s → m s = 0) : VectorMeasure α E where
  measureOf' := m
  empty' := by simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
  not_measurable' := h''m
  m_iUnion' f f_meas f_disj := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]; swap
    · simp only [← toReal_enorm]
      apply ENNReal.summable_toReal
      apply ne_of_lt
      calc ∑' i, ‖m (f i)‖ₑ
      _ ≤ ∑' i, μ (f i) := by gcongr; apply hm
      _ = μ (⋃ i, f i) := (measure_iUnion f_disj f_meas).symm
      _ < ⊤ := measure_lt_top μ (⋃ i, f i)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp_rw [norm_sub_rev, ← toReal_enorm, ← ENNReal.toReal_zero]
    apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    have A n : m (⋃ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, m (f i) := by
      induction n with
      | zero => simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
      | succ n ih =>
        simp only [Finset.range_add_one]
        rw [Finset.sum_insert (by simp)]
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
        rw [h'm _ _ (f_meas n), ih]
        · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
        · simp only [Finset.mem_range, Set.disjoint_iUnion_right]
          intro i hi
          exact f_disj hi.ne'
    have B n : m (⋃ i, f i) = m (⋃ i ∈ Finset.range n, f i) + m (⋃ i ∈ Set.Ici n, f i) := by
      have : ⋃ i, f i = (⋃ i ∈ Finset.range n, f i) ∪ (⋃ i ∈ Set.Ici n, f i) := by
        ext; simp; grind
      rw [this]
      apply h'm
      · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
      · exact MeasurableSet.biUnion (Set.to_countable _) (fun i hi ↦ f_meas i)
      · simp only [Finset.mem_range, Set.mem_Ici, Set.disjoint_iUnion_right,
          Set.disjoint_iUnion_left]
        intro i hi j hj
        exact f_disj (hj.trans_le hi).ne
    have C n : m (⋃ i, f i) - ∑ i ∈ Finset.range n, m (f i) = m (⋃ i ∈ Set.Ici n, f i) := by
      rw [B n, A]; simp
    simp only [C]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun n ↦ μ (⋃ i ∈ Set.Ici n, f i)) ?_ (fun i ↦ bot_le) (fun i ↦ hm _)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (fun i ↦ (f_meas i).nullMeasurableSet) f_disj

open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false in
/-- Consider an additive content on a dense ring of sets. Assume that it is dominated by a finite
positive measure. Then it extends to a countably additive vector measure. -/
/-
**MeasureTheory.VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_den
se** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_extension_of_isSetRing_of_le_measure_of_dense [IsFiniteMeasure μ] {
C : Set (Set α)} {m : AddContent E C} (hC : IsSetRing C) (hCmeas : forall s in C
, MeasurableSet s) (hm : forall s in C, ‖m s‖ₑ <= μ s) (h'C : forall t ε, Measur
ableSet t -> 0 < ε -> exists s in C, μ (s ∆ t) < ε) : exists m' : VectorMeasure 
α E, (forall s in C, m' s = m s) ∧ forall s, ‖m' s‖ₑ <= μ s
参数：Set α；hC : IsSetRing C；hCmeas : forall s in C, MeasurableSet s；hm : forall s 
in C, ‖m s‖ₑ <= μ s；h'C : forall t ε, MeasurableSet t -> 0 < ε -> exists s in C,
 μ (s ∆ t) < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `MeasureTheory.measure_symmDiff_eq`：measure_symmDiff_eq (hs : NullMeasura
bleSet s μ) (ht : NullMeasurableSet t μ) : μ (s ∆ t) = μ (s \ t) + μ (t \ s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.addContent_union`：addContent_union (hC : IsSetRing C) (hs 
: s in C) (ht : t in C) (h_dis : Disjoint s t) : m (s union t) = m s + m t
· 使用引理 `MeasureTheory.IsSetRing.inter_mem`：inter_mem (hC : IsSetRing C) (hs : s 
in C) (ht : t in C) : s inter t in C
· 使用定理 `MeasureTheory.IsSetRing.sdiff_mem`：∀ {α : Type u_1} {C : Set (Set α)}, M
easureTheory.IsSetRing C → ∀ ⦃s t : Set α⦄, s ∈ C → t ∈ C → s \ t ∈ C
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用引理 `Set.disjoint_sdiff_inter`：disjoint_sdiff_inter : Disjoint (s \ t) (s int
er t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `enorm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a b : E}, 
‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Dense.lipschitzWith_extend`：Dense.lipschitzWith_extend {α β : Type*} [Ps
eudoEMetricSpace α] [EMetricSpace β] [CompleteSpace β] {s : Set α} (hs : Dense s
) {f : s -> β} {…
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
（共 122 条，此处仅展示前 30 条）

--- 原说明 ---
Consider an additive content on a dense ring of sets. Assume that it is dominate
d by a finite
positive measure. Then it extends to a countably additive vector measure.
-/
lemma exists_extension_of_isSetRing_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hC : IsSetRing C)
    (hCmeas : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  /- We will extend by continuity the function `m` from the class `C` to all measurable sets,
  thanks to the fact that `C` is dense. To implement this properly, we work in the space
  `MeasuredSets μ` with the distance `edist s t = μ (s ∆ t)`. The assumptions guarantee that
  `m` is Lipschitz on `C` there, and therefore extends to a Lipschitz function. We check that
  the extension is still finitely additive by approximating disjoint measurable sets by disjoint
  measurable sets in `C`. Moreover, the extension is still dominated by `μ`.
  The countable additivity follows from these two properties and
  Lemma `VectorMeasure.of_additive_of_le_measure`. -/
  classical
  -- Express things inside `MeasuredSets μ`.
  let C' : Set (MeasuredSets μ) := {s | ∃ c ∈ C, s = c}
  have C'C (s : MeasuredSets μ) (hs : s ∈ C') : (s : Set α) ∈ C := by
    rcases hs with ⟨t, ht, rfl⟩; exact ht
  have C'_dense : Dense C' := by
    simp only [Dense, EMetric.mem_closure_iff, gt_iff_lt]
    intro x ε εpos
    rcases h'C x ε x.2 εpos with ⟨s, sC, hs⟩
    refine ⟨⟨s, hCmeas s sC⟩, ⟨s, sC, rfl⟩, ?_⟩
    rw [edist_comm]
    exact hs
  /- Let `m₀` be the function `m` expressed on the subtype of `MeasuredSets μ` made of
  elements of `C`. -/
  let m₀ : C' → E := fun x ↦ m x
  -- It is Lipschitz continuous
  have lip : LipschitzWith 1 m₀ := by
    intro s t
    have : edist s t = edist (s : MeasuredSets μ) t := rfl
    simp only [ENNReal.coe_one, one_mul, this, MeasuredSets.edist_def, m₀, edist_eq_enorm_sub]
    rw [measure_symmDiff_eq (by exact s.1.2.nullMeasurableSet) (by exact t.1.2.nullMeasurableSet)]
    have Is : ((s : Set α) ∩ t) ∪ (s \ t) = (s : Set α) := Set.inter_union_sdiff _ _
    have It : ((t : Set α) ∩ s) ∪ (t \ s) = (t : Set α) := Set.inter_union_sdiff _ _
    nth_rewrite 1 [← Is]
    nth_rewrite 3 [← It]
    rw [addContent_union hC (hC.inter_mem (C'C _ t.2) (C'C _ s.2))
        (hC.sdiff_mem (C'C _ t.2) (C'C _ s.2)) Set.disjoint_sdiff_inter.symm,
      addContent_union hC (hC.inter_mem (C'C _ s.2) (C'C _ t.2))
        (hC.sdiff_mem (C'C _ s.2) (C'C _ t.2)) Set.disjoint_sdiff_inter.symm, Set.inter_comm]
    simp only [add_sub_add_left_eq_sub, ge_iff_le]
    apply enorm_sub_le.trans
    gcongr
    · exact hm _ (hC.sdiff_mem (C'C _ s.2) (C'C _ t.2))
    · exact hm _ (hC.sdiff_mem (C'C _ t.2) (C'C _ s.2))
  -- Let `m₁` be the extension of `m₀` to all elements of `MeasuredSets μ` by continuity
  let m₁ : MeasuredSets μ → E := C'_dense.extend m₀
  -- It is again Lipschitz continuous and bounded by `μ`
  have m₁_lip : LipschitzWith 1 m₁ := C'_dense.lipschitzWith_extend lip
  have hBound : ∀ s, ‖m₁ s‖ₑ ≤ μ s := by
    have : IsClosed {s | ‖m₁ s‖ₑ ≤ μ s} :=
      isClosed_le m₁_lip.continuous.enorm MeasuredSets.continuous_measure
    have : Dense {s | ‖m₁ s‖ₑ ≤ μ s} := by
      apply C'_dense.mono
      intro s hs
      simp only [Set.mem_ofPred_eq]
      convert! hm s (C'C s hs)
      exact C'_dense.extend_eq lip.continuous ⟨s, hs⟩
    simpa only [Dense, IsClosed.closure_eq, Set.mem_ofPred_eq] using! this
  /- Most involved technical step: show that the extension `m₁` of `m₀` is still finitely
  additive. -/
  have hAddit (s t : MeasuredSets μ) (h : Disjoint (s : Set α) t) :
      m₁ ⟨s ∪ t, s.2.union t.2⟩ = m₁ s + m₁ t := by
    suffices ∀ ε > 0, ‖m₁ (⟨s ∪ t, s.2.union t.2⟩) - m₁ s - m₁ t‖ₑ < ε by
      rw [← sub_eq_zero, ← enorm_eq_zero, sub_add_eq_sub_sub]
      exact eq_bot_iff.2 (le_of_forall_gt this)
    intro ε εpos
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ 8 * δ = ε :=
      ⟨ε / 8, (ENNReal.div_pos εpos.ne' (by simp)), ENNReal.mul_div_cancel (by simp) (by simp)⟩
    -- approximate `s` and `t` up to `δ` by sets `s'` and `t'` in `C`.
    obtain ⟨s', s'C, hs'⟩ : ∃ s' ∈ C, μ (s' ∆ s) < δ := h'C _ _ s.2 δpos
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t' ∆ t) < δ := h'C _ _ t.2 δpos
    have It : ‖m t' - m₁ t‖ₑ < δ := by
      have : m₁ ⟨t', hCmeas _ t'C⟩ = m t' :=
        C'_dense.extend_eq lip.continuous ⟨⟨t', hCmeas _ t'C⟩, ⟨t', t'C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact ht'
    -- `s'` and `t'` have no reason to be disjoint, but their intersection has small measure
    have hμ' : μ (s' ∩ t') < 2 * δ := calc
      μ (s' ∩ t')
      _ ≤ μ (s ∩ t ∪ (s' ∆ s) ∪ (t' ∆ t)) := measure_mono (by grind)
      _ = μ ((s' ∆ s) ∪ (t' ∆ t)) := by simp [Set.disjoint_iff_inter_eq_empty.mp h]
      _ ≤ μ (s' ∆ s) + μ (t' ∆ t) := measure_union_le _ _
      _ < δ + δ := by gcongr
      _ = 2 * δ := by ring
    -- Therefore, the set `s'' := s' \ t'` still approximates well the original set `s`, it belongs
    -- to `C`, and moreover `s''` and `t'` are disjoint.
    let s'' := s' \ t'
    have s''C : s'' ∈ C := hC.sdiff_mem s'C t'C
    have hs'' : μ (s'' ∆ s) < 3 * δ := calc
      μ (s'' ∆ s)
      _ ≤ μ (s'' ∆ s') + μ (s' ∆ s) := measure_symmDiff_le _ _ _
      _ < 2 * δ + δ := by gcongr; simp [s'', symmDiff, hμ']
      _ = 3 * δ := by ring
    have Is : ‖m s'' - m₁ s‖ₑ < 3 * δ := by
      have : m₁ ⟨s'', hCmeas _ s''C⟩ = m s'' :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'', hCmeas _ s''C⟩, ⟨s'', s''C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact hs''
    -- `s'' ∪ t'` also approximates well `s ∪ t`.
    have Ist : ‖m (s'' ∪ t') - m₁ ⟨s ∪ t, s.2.union t.2⟩‖ₑ < 4 * δ := by
      have s''t'C : s'' ∪ t' ∈ C := hC.union_mem s''C t'C
      have : m₁ ⟨s'' ∪ t', hCmeas _ s''t'C⟩ = m (s'' ∪ t') :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'' ∪ t', hCmeas _ s''t'C⟩, ⟨s'' ∪ t', s''t'C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      change μ ((s'' ∪ t') ∆ (s ∪ t)) < 4 * δ
      calc μ ((s'' ∪ t') ∆ (s ∪ t))
      _ ≤ μ (s'' ∆ s ∪ t' ∆ t) := measure_mono (Set.union_symmDiff_union_subset ..)
      _ ≤ μ (s'' ∆ s) + μ (t' ∆ t) := measure_union_le _ _
      _ < 3 * δ + δ := by gcongr
      _ = 4 * δ := by ring
    -- conclusion: to estimate `m₁ (s ∪ t) - m₁ s - m₁ t`, replace it up to a small error by
    -- `m₁ (s'' ∪ t') - m₁ s'' - m₁ t'`, which is zero as `m₁` is additive on `C` and these
    -- two sets are disjoint
    calc ‖m₁ (⟨s ∪ t, s.2.union t.2⟩) - m₁ s - m₁ t‖ₑ
    _ = ‖(m (s'' ∪ t') - m s'' - m t') + (m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t'))
          + (m s'' - m₁ s) + (m t' - m₁ t)‖ₑ := by abel_nf
    _ ≤ ‖m (s'' ∪ t') - m s'' - m t'‖ₑ + ‖m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t')‖ₑ
          + ‖m s'' - m₁ s‖ₑ + ‖m t' - m₁ t‖ₑ := enorm_add₄_le
    _ = ‖m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t')‖ₑ + ‖m s'' - m₁ s‖ₑ + ‖m t' - m₁ t‖ₑ := by
      rw [addContent_union hC s''C t'C Set.disjoint_sdiff_left]
      simp
    _ < 4 * δ + 3 * δ + δ := by
      gcongr
      rwa [enorm_sub_rev]
    _ = 8 * δ := by ring
    _ = ε := hδ
  -- conclusion of the proof: the function `s ↦ m₁ s` if `s` is measurable, and `0` otherwise,
  -- defines a vector measure satisfying the required properties
  let m' (s : Set α) := if hs : MeasurableSet s then m₁ ⟨s, hs⟩ else 0
  let m'' : VectorMeasure α E := by
    apply VectorMeasure.of_additive_of_le_measure m' (μ := μ)
    · intro s
      by_cases hs : MeasurableSet s
      · simpa [hs, m'] using! hBound _
      · simp [hs, m']
    · intro s t hs ht hst
      simp only [hs, ht, MeasurableSet.union, ↓reduceDIte, m']
      exact hAddit ⟨s, hs⟩ ⟨t, ht⟩ hst
    · intro s hs
      simp [m', hs]
  refine ⟨m'', fun s hs ↦ ?_, fun s ↦ ?_⟩
  · change m' s = m s
    simp only [hCmeas s hs, ↓reduceDIte, m']
    exact C'_dense.extend_eq lip.continuous ⟨⟨s, hCmeas _ hs⟩, ⟨s, hs, rfl⟩⟩
  · change ‖m' s‖ₑ ≤ μ s
    by_cases hs : MeasurableSet s
    · simp only [hs, ↓reduceDIte, m']
      exact hBound ⟨s, hs⟩
    · simp [m', hs]

/-- Consider an additive content on a semi-ring of sets whose finite unions are dense. Assume that
it is dominated by a finite positive measure. Then it extends to a countably additive
vector measure. -/
/-
**MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of
_dense** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_extension_of_isSetSemiring_of_le_measure_of_dense [IsFiniteMeasure 
μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C) (hCmeas : foral
l s in C, MeasurableSet s) (hm : forall s in C, ‖m s‖ₑ <= μ s) (h'C : forall t ε
, MeasurableSet t -> 0 < ε -> exists s in supClosure C, μ (s ∆ t) < ε) : exists 
m' : VectorMeasure α E, (forall s in C, m' s = m s) ∧ forall s, ‖m' s‖ₑ <= μ s
参数：Set α；hC : IsSetSemiring C；hCmeas : forall s in C, MeasurableSet s；hm : foral
l s in C, ‖m s‖ₑ <= μ s；h'C : forall t ε, MeasurableSet t -> 0 < ε -> exists s i
n supClosure C, μ (s ∆ t) < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsSetSemiring.mem_supClosure_iff`：mem_supClosure_iff (hC :
 IsSetSemiring C) : s in supClosure C ↔ exists P : Finpartition s, ↑P.parts subs
eteq C where mp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `MeasureTheory.AddContent.supClosure_apply_finpartition`：∀ {α : Type u_1}
 {C : Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G] (hC : MeasureTheory.I
sSetSemiring C)   (m : MeasureTheory.AddCont…
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `enorm_sum_le`：enorm_sum_le (s : Finset ι) (f : ι -> ε) : ‖∑ i in s, f i‖
ₑ <= ∑ i in s, ‖f i‖ₑ
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Finset.measurableSet_biUnion`：Finset.measurableSet_biUnion {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b
 in s, f b)
· 使用引理 `MeasureTheory.VectorMeasure.exists_extension_of_isSetRing_of_le_measure_
of_dense`：exists_extension_of_isSetRing_of_le_measure_of_dense [IsFiniteMeasure 
μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetRing C) (hCmeas :…
· 使用定理 `MeasureTheory.IsSetSemiring.isSetRing_supClosure`：isSetRing_supClosure (
hC : IsSetSemiring C) : IsSetRing (supClosure C) where empty_mem
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用定理 `MeasureTheory.AddContent.supClosure_apply_of_mem`：∀ {α : Type u_1} {C : 
Set (Set α)} {G : Type u_2} [inst : AddCommMonoid G] (hC : MeasureTheory.IsSetSe
miring C)   (m : MeasureTheory.AddCont…

--- 原说明 ---
Consider an additive content on a semi-ring of sets whose finite unions are dens
e. Assume that
it is dominated by a finite positive measure. Then it extends to a countably add
itive
vector measure.
-/
lemma exists_extension_of_isSetSemiring_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hCmeas : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ supClosure C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  set m₀ : AddContent E (supClosure C) := m.supClosure hC with hm₀
  have A (s) (hs : s ∈ supClosure C) : ‖m₀ s‖ₑ ≤ μ s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    nth_rewrite 2 [← P.sup_parts]
    rw [hm₀, AddContent.supClosure_apply_finpartition hC _ PC, Finset.sup_set_eq_biUnion,
      measure_biUnion_finset P.disjoint (fun b hb ↦ hCmeas _ (PC hb))]
    apply (enorm_sum_le _ _).trans
    gcongr with t ht
    exact hm _ (PC ht)
  have B (s) (hs : s ∈ supClosure C) : MeasurableSet s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    rw [← P.sup_parts, Finset.sup_set_eq_biUnion]
    exact Finset.measurableSet_biUnion _ (fun b hb ↦ hCmeas _ (PC hb))
  rcases VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_dense
    hC.isSetRing_supClosure B A h'C with ⟨m', hm', m'bound⟩
  refine ⟨m', fun s hs ↦ ?_, m'bound⟩
  rw [hm' _ (subset_supClosure hs)]
  exact AddContent.supClosure_apply_of_mem _ _ hs

/-- Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated by a finite
measure `μ`. Assume that `C` generates the sigma-algebra and covers the space up to measure zero.
Then `m` extends to a countably additive vector measure which is dominated by `μ`. -/
/-
**MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of
_generateFrom_of_cover** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated
 by a finite
measure `μ`. Assume that `C` generates the sigma-algebra and covers the space up
 to measure zero.
Then `m` extends to a countably additive vector measure which is dominated by `μ
`.
-/
private lemma exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : hα = generateFrom C) (h''C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  apply VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_dense hC ?_ hm ?_
  · intro s hs
    rw [h'C]
    exact measurableSet_generateFrom hs
  · intro t ε ht εpos
    exact exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h''C h'C ht εpos

/-- Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated by a finite
measure `μ`. Assume that `C` generates the sigma-algebra.
Then `m` extends to a countably additive vector measure which is dominated by `μ`. -/
/-
**MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of
_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom [IsFiniteM
easure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C) (hm : fo
rall s in C, ‖m s‖ₑ <= μ s) (h'C : hα = generateFrom C) : exists m' : VectorMeas
ure α E, (forall s in C, m' s = m s) ∧ forall s, ‖m' s‖ₑ <= μ s
参数：Set α；hC : IsSetSemiring C；hm : forall s in C, ‖m s‖ₑ <= μ s；h'C : hα = gener
ateFrom C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.exists_ae_subset_biUnion_countable`：exists_ae_subs
et_biUnion_countable [SFinite μ] {C : Set (Set α)} (hC : forall s in C, Measurab
leSet s) : exists D subseteq C, D.Countable ∧ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasurableSet.sUnion`：∀ {α : Type u_1} {m : MeasurableSpace α} {s : Set 
(Set α)},   s.Countable → (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.AddContent.0.MeasureTheory.
VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of
_cover`：∀ {α : Type u_1} {hα : MeasurableSpace α} {E : Type u_2} [inst : NormedA
ddCommGroup E] [CompleteSpace E]   {μ : MeasureTheory.Measure α} [Me…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_mono_ae`：measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <=
 μ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `MeasureTheory.ae_le_set_inter`：ae_le_set_inter {s' t' : Set α} (h : s <=
ᵐ[μ] t) (h' : s' <=ᵐ[μ] t') : (s inter s' : Set α) <=ᵐ[μ] (t inter t' : Set α)
· 使用定理 `Filter.EventuallyLE.rfl`：∀ {α : Type u} {β : Type v} [inst : Preorder β]
 {l : Filter α} {f : α → β}, f ≤ᶠ[l] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.restrict_apply_le`：restrict_apply_le (s t : Set α)
 : μ.restrict s t <= μ t

--- 原说明 ---
Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated
 by a finite
measure `μ`. Assume that `C` generates the sigma-algebra.
Then `m` extends to a countably additive vector measure which is dominated by `μ
`.
-/
theorem exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s) (h'C : hα = generateFrom C) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  have M (s) (hs : s ∈ C) : MeasurableSet s := by
    rw [h'C]; exact measurableSet_generateFrom hs
  rcases Measure.exists_ae_subset_biUnion_countable μ M with ⟨D, DC, D_count, hD⟩
  have MD : MeasurableSet (⋃₀ D) := MeasurableSet.sUnion D_count (fun t ht ↦ M _ (DC ht))
  let μ' := μ.restrict (⋃₀ D)
  obtain ⟨m', h, h'⟩ : ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ' s := by
    apply exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover hC
      (fun s hs ↦ ?_) h'C ?_
    · exact ⟨D, D_count, DC, by simp [μ', Measure.restrict_apply' MD]⟩
    · apply (hm s hs).trans
      simp only [Measure.restrict_apply' MD, μ']
      apply measure_mono_ae
      nth_rewrite 1 [← Set.inter_self s]
      exact ae_le_set_inter Filter.EventuallyLE.rfl (hD s hs)
  exact ⟨m', h, fun s ↦ (h' s).trans (Measure.restrict_apply_le (⋃₀ D) s)⟩

/-- Consider an additive content `m` on a semi-ring of measurable sets `C`, which is dominated
by a finite measure `μ`.
Then `m` extends to a countably additive vector measure which is dominated by `μ`. -/
/-
**MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_extension_of_isSetSemiring_of_le_measure [NormedSpace Real E] [IsFi
niteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C) (hm
 : forall s in C, ‖m s‖ₑ <= μ s) (h'C : forall s in C, MeasurableSet s) : exists
 m' : VectorMeasure α E, (forall s in C, m' s = m s) ∧ forall s, ‖m' s‖ₑ <= μ s
参数：Set α；hC : IsSetSemiring C；hm : forall s in C, ‖m s‖ₑ <= μ s；h'C : forall s i
n C, MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_meas
ure_of_generateFrom`：exists_extension_of_isSetSemiring_of_le_measure_of_generate
From [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemir
i…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_empty`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f 
: α → M), ∅.indicator f = fun x => 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_fun_zero`：∀ {α : Type u_1} {E : Type u_3} {m m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E]  
 [inst_1 : NormedSpa…
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero`：integral_zero : ∫ᵛ _, 0 ∂[B; 
μ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `ae_eq_trim_of_measurable`：∀ {α : Type u_3} {β : Type u_4} {m m0 : Measur
ableSpace α} {μ : MeasureTheory.Measure α} [inst : MeasurableSpace β]   [Measura
bleEq β] (hm :…
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
（共 112 条，此处仅展示前 30 条）

--- 原说明 ---
Consider an additive content `m` on a semi-ring of measurable sets `C`, which is
 dominated
by a finite measure `μ`.
Then `m` extends to a countably additive vector measure which is dominated by `μ
`.
-/
theorem exists_extension_of_isSetSemiring_of_le_measure [NormedSpace ℝ E]
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s) (h'C : ∀ s ∈ C, MeasurableSet s) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  /- On the sigma-algebra `M` generated by `C`, the desired vector measure is provided by
  `exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`. We extend it to the whole
  sigma-algebra of measurable sets by integrating the conditional expectation with respect to `M`.
  This extension satisfies all the desired properties. -/
  classical
  let M : MeasurableSpace α := generateFrom C
  have Mle : M ≤ hα := generateFrom_le h'C
  set μ' := μ.trim Mle with hμ'
  obtain ⟨m', m'C, hm'⟩ :
      ∃ m' : @VectorMeasure α M E _ _, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ' s := by
    apply exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom hC (fun s hs ↦ ?_) rfl
    apply (hm s hs).trans_eq
    exact (MeasureTheory.trim_measurableSet_eq Mle (measurableSet_generateFrom hs)).symm
  have m'_le : m'.variation ≤ μ' := by
    exact variation_le_of_forall_enorm_le (fun s hs ↦ hm' _)
  -- next line is to make sure that the default instance is picked below when defininig `m''`.
  let : MeasurableSpace α := hα
  let m'' : VectorMeasure α E :=
  { measureOf' s := if MeasurableSet s then ∫ᵛ x, μ[s.indicator 1 | M] x ∂• m' else 0
    empty' := by simp
    not_measurable' s hs := by simp [hs]
    m_iUnion' f f_meas hf := by
      have : ∫ᵛ (x : α), μ[fun x ↦ ∑' (d : ℕ), (f d).indicator 1 x | M] x ∂•m'
          = ∫ᵛ (x : α), ∑' d, μ[(f d).indicator 1 | M] x ∂•m' := by
        apply VectorMeasure.integral_congr_ae
        apply ae_mono m'_le
        apply ae_eq_trim_of_measurable _ (by fun_prop) (by fun_prop)
        apply condExp_tsum (fun i ↦ ?_)
        · simp only [enorm_indicator_eq_indicator_enorm, Pi.one_apply, enorm_one, f_meas,
            lintegral_indicator, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
            Set.univ_inter, one_mul, ne_eq, ← measure_iUnion hf f_meas, measure_ne_top,
            not_false_eq_true]
        · exact AEStronglyMeasurable.indicator (by fun_prop) (f_meas i)
      simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion,
        indicator_iUnion_of_pairwise_disjoint _ hf, this]
      have I : ∑' (i : ℕ), ∫⁻ (a : α), ‖μ[(f i).indicator (1 : α → ℝ) | M] a‖ₑ ∂μ < ∞ := by
        have A i : ∫⁻ a, ‖μ[(f i).indicator (1 : α → ℝ) | M] a‖ₑ ∂μ = μ (f i) :=
          lintegral_enorm_condExp_indicator Mle (f_meas i)
        simp_rw [A, ← measure_iUnion hf f_meas]
        exact measure_lt_top _ _
      rw [integral_tsum (by fun_prop)]; swap
      · apply ne_of_lt
        grw [m'_le, hμ']
        have A i : Measurable[M] (fun x ↦ ‖μ[(f i).indicator (1 : α → ℝ) | M] x‖ₑ) := by fun_prop
        simp_rw [lintegral_trim Mle (A _)]
        exact I
      refine Summable.hasSum (Summable.of_enorm ?_)
      apply ne_of_lt (lt_of_le_of_lt ?_ I)
      gcongr with i
      grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_lsmul_le, one_mul,
        lintegral_mono' m'_le le_rfl, hμ', lintegral_trim _ (by fun_prop)] }
  refine ⟨m'', fun s hs ↦ ?_, fun s ↦ ?_⟩
  · simp only [coe_mk, h'C s hs, ↓reduceIte, m'']
    have : ∫ᵛ (x : α), μ[s.indicator 1 | M] x ∂•m' = ∫ᵛ (x : α), s.indicator 1 x ∂•m' := by
      apply integral_congr_ae
      filter_upwards with x
      rw [condExp_of_stronglyMeasurable Mle]
      · exact StronglyMeasurable.indicator stronglyMeasurable_const
          (measurableSet_generateFrom hs)
      · exact (integrable_const 1).indicator (h'C s hs)
    rw [this, integral_indicator (measurableSet_generateFrom hs)]
    have : IsFiniteMeasure m'.variation :=
      isFiniteMeasure_of_le _ m'_le
    simp only [Pi.one_apply, setIntegral_const]
    simp [m'C s hs]
  · by_cases hs : MeasurableSet s; swap
    · simp [not_measurable _ hs]
    simp only [coe_mk, hs, ↓reduceIte, m'']
    grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_lsmul_le, one_mul,
      lintegral_mono' m'_le le_rfl, hμ', lintegral_trim _ (by fun_prop),
      lintegral_enorm_condExp_indicator Mle hs]

end MeasureTheory.VectorMeasure

