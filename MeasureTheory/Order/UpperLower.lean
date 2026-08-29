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

variable {ι : Type*} [Fintype ι] {s : Set (ι -> Real)} {x : ι -> Real}

/--
lemma `aux₀` / 引理 `aux₀`

English:
lemma aux₀
  proof: by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
    (Frequently.of_forall fun _ => lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n =>
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ <= volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) hf₀ _ hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals positivity

中文:
引理 aux₀
  证明: by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
    (Frequently.of_forall fun _ => lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n =>
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ <= volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) hf₀ _ hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals positivity
-/
private lemma aux₀
    (h : forall δ, 0 < δ ->
      exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall y (δ / 4) subseteq interior s) :
    ¬Tendsto (fun r => volume (closure s inter closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 0) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
    (Frequently.of_forall fun _ => lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n =>
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ <= volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) hf₀ _ hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals positivity

/--
lemma `aux₁` / 引理 `aux₁`

English:
lemma aux₁
  proof: by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
      (Frequently.of_forall fun _ => lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n => lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n))
        <= volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [sdiff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm]; rw [← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    have := hε' n
    rw [measure_sdiff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top)]; rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [ENNReal.sub_div fun _ _ => _]; rw [ENNReal.div_self _ ENNReal.ofReal_ne_top]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet

中文:
引理 aux₁
  证明: by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
      (Frequently.of_forall fun _ => lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n => lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n))
        <= volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [sdiff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm]; rw [← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    have := hε' n
    rw [measure_sdiff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top)]; rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [ENNReal.sub_div fun _ _ => _]; rw [ENNReal.div_self _ ENNReal.ofReal_ne_top]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet
-/
private lemma aux₁
    (h : forall δ, 0 < δ ->
      exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall y (δ / 4) subseteq interior sᶜ) :
    ¬Tendsto (fun r => volume (closure s inter closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : Real)
  refine not_eventually.2
      (Frequently.of_forall fun _ => lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n => lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s inter closedBall x (ε n)) / volume (closedBall x (ε n))
        <= volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [sdiff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm]; rw [← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    have := hε' n
    rw [measure_sdiff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top)]; rw [Real.volume_pi_closedBall]; rw [Real.volume_pi_closedBall]; rw [ENNReal.sub_div fun _ _ => _]; rw [ENNReal.div_self _ ENNReal.ofReal_ne_top]; rw [← ENNReal.ofReal_div_of_pos]; rw [← div_pow]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [div_right_comm]; rw [div_self]; rw [one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet

/--
theorem `IsUpperSet.null_frontier` / 定理 `IsUpperSet.null_frontier`

English:
theorem IsUpperSet.null_frontier
  given: (hs : IsUpperSet s)
  statement: volume (frontier s) = 0
  proof: by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

中文:
定理 是上集.null_frontier
  条件: (hs : 是上集 s)
  结论: volume (frontier s) = 0
  证明: by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

Depends on / 依赖: Besicovitch, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, Pi.one_apply, ae_tendsto_measure_inter_div_of_measurableSet, closure, exists_subset_ball, frontier_compl, frontier_subset_closure, hs.compl.exists_subset_ball, hs.exists_subset_ball, indicator_of_mem, indicator_of_notMem, isClosed_closure, measurableSet, measure_mono_null, mem_compl_iff, mem_ofPred, not_false_eq_true, one_apply
-/
theorem IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

/--
theorem `IsLowerSet.null_frontier` / 定理 `IsLowerSet.null_frontier`

English:
theorem IsLowerSet.null_frontier
  given: (hs : IsLowerSet s)
  statement: volume (frontier s) = 0
  proof: by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

中文:
定理 是下集.null_frontier
  条件: (hs : 是下集 s)
  结论: volume (frontier s) = 0
  证明: by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

Depends on / 依赖: Besicovitch, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, Pi.one_apply, ae_tendsto_measure_inter_div_of_measurableSet, closure, exists_subset_ball, frontier_compl, frontier_subset_closure, hs.compl.exists_subset_ball, hs.exists_subset_ball, indicator_of_mem, indicator_of_notMem, isClosed_closure, measurableSet, measure_mono_null, mem_compl_iff, mem_ofPred, not_false_eq_true, one_apply
-/
theorem IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx => ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x in closure s <;>
    simp only [mem_compl_iff, mem_ofPred, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
· refine aux₁ fun _ => hs.compl.exists_subset_ball frontier_subset_closure ?_
    rwa [frontier_compl]
· exact aux₀ fun _ => hs.exists_subset_ball frontier_subset_closure hx

/--
theorem `Set.OrdConnected.null_frontier` / 定理 `Set.OrdConnected.null_frontier`

English:
theorem Set.OrdConnected.null_frontier
  given: (hs : s.OrdConnected)
  statement: volume (frontier s) = 0
  proof: by
  rw [← hs.upperClosure_inter_lowerClosure]
exact measure_mono_null (frontier_inter_subset _ _) measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)

中文:
定理 集合.序连通.null_frontier
  条件: (hs : s.序连通)
  结论: volume (frontier s) = 0
  证明: by
  rw [← hs.upperClosure_inter_lowerClosure]
exact measure_mono_null (frontier_inter_subset _ _) measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)

Depends on / 依赖: LowerSet, LowerSet.lower, UpperSet, UpperSet.upper, frontier_inter_subset, hs.upperClosure_inter_lowerClosure, measure_inter_null_of_null_left, measure_inter_null_of_null_right, measure_mono_null, measure_union_null, null_frontier, upperClosure_inter_lowerClosure
-/
theorem Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s) = 0 := by
  rw [← hs.upperClosure_inter_lowerClosure]
exact measure_mono_null (frontier_inter_subset _ _) measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)

/--
theorem `Set.OrdConnected.nullMeasurableSet` / 定理 `Set.OrdConnected.nullMeasurableSet`

English:
theorem Set.OrdConnected.nullMeasurableSet
  given: (hs : s.OrdConnected)
  statement: NullMeasurableSet s
  proof: nullMeasurableSet_of_null_frontier hs.null_frontier

中文:
定理 集合.序连通.nullMeasurableSet
  条件: (hs : s.序连通)
  结论: NullMeasurableSet s
  证明: nullMeasurableSet_of_null_frontier hs.null_frontier
-/
protected theorem Set.OrdConnected.nullMeasurableSet (hs : s.OrdConnected) : NullMeasurableSet s :=
  nullMeasurableSet_of_null_frontier hs.null_frontier

/--
theorem `IsAntichain.volume_eq_zero` / 定理 `IsAntichain.volume_eq_zero`

English:
theorem IsAntichain.volume_eq_zero
  given: [Nonempty ι] (hs : IsAntichain (· <= ·) s)
  statement: volume s = 0
  proof: by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_sdiff_interior]; rw [hs.interior_eq_empty]; rw [sdiff_empty]
  exact subset_closure

中文:
定理 IsAntichain.volume_eq_zero
  条件: [非空 ι] (hs : IsAntichain (· <= ·) s)
  结论: volume s = 0
  证明: by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_sdiff_interior]; rw [hs.interior_eq_empty]; rw [sdiff_empty]
  exact subset_closure

Depends on / 依赖: closure_sdiff_interior, hs.interior_eq_empty, hs.ordConnected.null_frontier, interior_eq_empty, measure_mono_null, null_frontier, ordConnected, sdiff_empty, subset_closure
-/
theorem IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· <= ·) s) : volume s = 0 := by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_sdiff_interior]; rw [hs.interior_eq_empty]; rw [sdiff_empty]
  exact subset_closure
