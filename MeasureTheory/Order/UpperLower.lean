/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
module

public import Mathlib.Analysis.Normed.Order.UpperLower
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are null-measurable.
Recall that `x ≤ y` iff `∀ i, x i ≤ y i`, and `s` is order-connected iff
`∀ x y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s`.

## Main declarations

* `Set.OrdConnected.null_frontier`: The frontier of an order-connected set in `ℝⁿ` has measure `0`.

## Notes

We prove null-measurability in `ℝⁿ` with the `∞`-metric, but this transfers directly to `ℝⁿ` with
the Euclidean metric because they have the same measurable sets.

Null-measurability can't be strengthened to measurability because any antichain (and in particular
any subset of the antidiagonal `{(x, y) | x + y = 0}`) is order-connected.

## Sketch proof

1. To show an order-connected set is null-measurable, it is enough to show it has null frontier.
2. Since an order-connected set is the intersection of its upper and lower closure, it's enough to
  show that upper and lower sets have null frontier.
3. WLOG let's prove it for an upper set `s`.
4. By the Lebesgue density theorem, it is enough to show that any frontier point `x` of `s` is not a
  Lebesgue point, namely we want the density of `s` over small balls centered at `x` to not tend to
  either `0` or `1`.
5. This is true, since by the upper setness of `s` we can intercalate a ball of radius `δ / 4` in
  `s` intersected with the upper quadrant of the ball of radius `δ` centered at `x` (recall that the
  balls are taken in the ∞-norm, so they are cubes), and another ball of radius `δ / 4` in `sᶜ` and
  the lower quadrant of the ball of radius `δ` centered at `x`.

## TODO

Generalize so that it also applies to `ℝ × ℝ`, for example.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

variable {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ}

/-- If we can fit a small ball inside a set `s` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `0`.

Along with `aux₁`, this proves that `x` is not a Lebesgue point of `s`. This will be used to prove
that the frontier of an order-connected set is null. -/
/-
**aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we can fit a small ball inside a set `s` intersected with any neighborhood of
 `x`, then the
density of `s` near `x` is not `0`.

Along with `aux₁`, this proves that `x` is not a Lebesgue point of `s`. This wil
l be used to prove
that the frontier of an order-connected set is null.
-/
private lemma aux₀
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 0) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
    (Frequently.of_forall fun _ ↦ lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n ↦
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ ≤ volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
        exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) <| hf₀ _ <| hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall, Real.volume_pi_closedBall, ← ENNReal.ofReal_div_of_pos,
      ← div_pow, mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals positivity

/-- If we can fit a small ball inside a set `sᶜ` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `1`.

Along with `aux₀`, this proves that `x` is not a Lebesgue point of `s`. This will be used to prove
that the frontier of an order-connected set is null. -/
/-
**aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we can fit a small ball inside a set `sᶜ` intersected with any neighborhood o
f `x`, then the
density of `s` near `x` is not `1`.

Along with `aux₀`, this proves that `x` is not a Lebesgue point of `s`. This wil
l be used to prove
that the frontier of an order-connected set is null.
-/
private lemma aux₁
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior sᶜ) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
      (Frequently.of_forall fun _ ↦ lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n ↦ lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n))
        ≤ volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [sdiff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm, ← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    have := hε' n
    rw [measure_sdiff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top),
      Real.volume_pi_closedBall, Real.volume_pi_closedBall, ENNReal.sub_div fun _ _ ↦ _,
      ENNReal.div_self _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_div_of_pos, ← div_pow,
      mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet
/-
**IsUpperSet.null_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0
参数：hs : IsUpperSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `_private.Mathlib.MeasureTheory.Order.UpperLower.0.aux₁`：∀ {ι : Type u_1}
 [inst : Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ},   (∀ (δ : ℝ),       0 < δ → ∃
 y, Metric.closedBall y (δ / 4) ⊆ Metric.clo…
· 使用定理 `IsLowerSet.exists_subset_ball`：IsLowerSet.exists_subset_ball (hs : IsLow
erSet s) (hx : x in closure s) (hδ : 0 < δ) : exists y, closedBall y (δ / 4) sub
seteq closedBall x …
· 使用定理 `IsUpperSet.compl`：IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ
· 使用定理 `frontier_subset_closure`：frontier_subset_closure : frontier s subseteq c
losure s
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Order.UpperLower.0.aux₀`：∀ {ι : Type u_1}
 [inst : Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ},   (∀ (δ : ℝ),       0 < δ → ∃
 y, Metric.closedBall y (δ / 4) ⊆ Metric.clo…
· 使用定理 `IsUpperSet.exists_subset_ball`：IsUpperSet.exists_subset_ball (hs : IsUpp
erSet s) (hx : x in closure s) (hδ : 0 < δ) : exists y, closedBall y (δ / 4) sub
seteq closedBall x …
· 使用定理 `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`：ae_tendsto_me
asure_inter_div_of_measurableSet (μ : Measure β) [IsLocallyFiniteMeasure μ] {s :
 Set β} (hs : MeasurableSet s) : forallᵐ x ∂μ, …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Besicovitch.instHasBesicovitchCovering`：∀ (E : Type u_1) [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E],   HasBesicovi
tchCovering E
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
（共 34 条，此处仅展示前 30 条）
-/
theorem IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx
/-
**IsLowerSet.null_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0
参数：hs : IsLowerSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `_private.Mathlib.MeasureTheory.Order.UpperLower.0.aux₁`：∀ {ι : Type u_1}
 [inst : Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ},   (∀ (δ : ℝ),       0 < δ → ∃
 y, Metric.closedBall y (δ / 4) ⊆ Metric.clo…
· 使用定理 `IsUpperSet.exists_subset_ball`：IsUpperSet.exists_subset_ball (hs : IsUpp
erSet s) (hx : x in closure s) (hδ : 0 < δ) : exists y, closedBall y (δ / 4) sub
seteq closedBall x …
· 使用定理 `IsLowerSet.compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 s → IsUpperSet sᶜ
· 使用定理 `frontier_subset_closure`：frontier_subset_closure : frontier s subseteq c
losure s
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Order.UpperLower.0.aux₀`：∀ {ι : Type u_1}
 [inst : Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ},   (∀ (δ : ℝ),       0 < δ → ∃
 y, Metric.closedBall y (δ / 4) ⊆ Metric.clo…
· 使用定理 `IsLowerSet.exists_subset_ball`：IsLowerSet.exists_subset_ball (hs : IsLow
erSet s) (hx : x in closure s) (hδ : 0 < δ) : exists y, closedBall y (δ / 4) sub
seteq closedBall x …
· 使用定理 `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`：ae_tendsto_me
asure_inter_div_of_measurableSet (μ : Measure β) [IsLocallyFiniteMeasure μ] {s :
 Set β} (hs : MeasurableSet s) : forallᵐ x ∂μ, …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Besicovitch.instHasBesicovitchCovering`：∀ (E : Type u_1) [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E],   HasBesicovi
tchCovering E
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
（共 34 条，此处仅展示前 30 条）
-/
theorem IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx
/-
**Set.OrdConnected.null_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s)
 = 0
参数：hs : s.OrdConnected。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.OrdConnected.upperClosure_inter_lowerClosure`：Set.OrdConnected.upper
Closure_inter_lowerClosure (h : s.OrdConnected) : ↑(upperClosure s) inter ↑(lowe
rClosure s) = s
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `frontier_inter_subset`：frontier_inter_subset (s t : Set X) : frontier (s
 inter t) subseteq frontier s inter closure t union closure s inter frontier t
· 使用定理 `MeasureTheory.measure_union_null`：measure_union_null (hs : μ s = 0) (ht 
: μ t = 0) : μ (s union t) = 0
· 使用定理 `MeasureTheory.measure_inter_null_of_null_left`：measure_inter_null_of_nul
l_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S inter T) = 0
· 使用定理 `IsUpperSet.null_frontier`：IsUpperSet.null_frontier (hs : IsUpperSet s) :
 volume (frontier s) = 0
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
· 使用定理 `MeasureTheory.measure_inter_null_of_null_right`：measure_inter_null_of_nu
ll_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0
· 使用定理 `IsLowerSet.null_frontier`：IsLowerSet.null_frontier (hs : IsLowerSet s) :
 volume (frontier s) = 0
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
theorem Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s) = 0 := by
  rw [← hs.upperClosure_inter_lowerClosure]
  exact measure_mono_null (frontier_inter_subset _ _) <| measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)
/-
**Set.OrdConnected.nullMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected
`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {s : Set (ι → ℝ)},   s.OrdConnected → 
MeasureTheory.NullMeasurableSet s MeasureTheory.volume
参数：ι → ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nullMeasurableSet_of_null_frontier`：nullMeasurableSet_of_null_frontier {
s : Set α} {μ : Measure α} (h : μ (frontier s) = 0) : NullMeasurableSet s μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Set.OrdConnected.null_frontier`：Set.OrdConnected.null_frontier (hs : s.O
rdConnected) : volume (frontier s) = 0
-/
protected theorem Set.OrdConnected.nullMeasurableSet (hs : s.OrdConnected) : NullMeasurableSet s :=
  nullMeasurableSet_of_null_frontier hs.null_frontier
/-
**IsAntichain.volume_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· <= ·) s) : vo
lume s = 0
参数：hs : IsAntichain (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_sdiff_interior`：closure_sdiff_interior (s : Set X) : closure s \
 interior s = frontier s
· 使用引理 `IsAntichain.interior_eq_empty`：IsAntichain.interior_eq_empty [forall x :
 α, (𝓝[<] x).NeBot] {s : Set α} (hs : IsAntichain (· <= ·) s) : interior s = ∅
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.OrdConnected.null_frontier`：Set.OrdConnected.null_frontier (hs : s.O
rdConnected) : volume (frontier s) = 0
· 使用定理 `IsAntichain.ordConnected`：∀ {α : Type u_1} [inst : PartialOrder α] {s : 
Set α}, IsAntichain (fun x1 x2 => x1 ≤ x2) s → s.OrdConnected
-/
theorem IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· ≤ ·) s) : volume s = 0 := by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_sdiff_interior, hs.interior_eq_empty, sdiff_empty]
  exact subset_closure
