/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme
public import Mathlib.Topology.Metrizable.Real

/-!
# Perfect Sets

In this file we define properties of `Perfect` subsets of a metric space,
including a version of the Cantor-Bendixson Theorem.

## Main Statements

* `Perfect.exists_nat_bool_injection`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.
-/

public section

open Set Filter Metric Function
open scoped ENNReal

section CantorInjMetric

variable {α : Type*} [MetricSpace α] {C : Set α} {ε : Real>=0∞}

/--
theorem `Perfect.small_diam_aux` / 定理 `Perfect.small_diam_aux`

English:
theorem Perfect.small_diam_aux
  given: (hC : Perfect C) (ε_pos : 0 < ε) {x : α} (xC : x in C)
  proof: closure (Metric.eball x (ε / 2) inter C)
    Perfect D ∧ D.Nonempty ∧ D subseteq C ∧ Metric.ediam D <= ε := by
  have : x in Metric.eball x (ε / 2) := by
    apply Metric.mem_eball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by simp⟩
  have := hC.closure_nhds_inter x xC this Metric.

中文:
定理 完美.small_diam_aux
  条件: (hC : 完美 C) (ε_pos : 0 < ε) {x : α} (xC : x in C)
  证明: closure (Metric.eball x (ε / 2) inter C)
    Perfect D ∧ D.Nonempty ∧ D subseteq C ∧ Metric.ediam D <= ε := by
  have : x in Metric.eball x (ε / 2) := by
    apply Metric.mem_eball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by simp⟩
  have := hC.closure_nhds_inter x xC this Metric.
-/
private theorem Perfect.small_diam_aux (hC : Perfect C) (ε_pos : 0 < ε) {x : α} (xC : x in C) :
    let D := closure (Metric.eball x (ε / 2) inter C)
    Perfect D ∧ D.Nonempty ∧ D subseteq C ∧ Metric.ediam D <= ε := by
  have : x in Metric.eball x (ε / 2) := by
    apply Metric.mem_eball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by simp⟩
  have := hC.closure_nhds_inter x xC this Metric.isOpen_eball
  refine ⟨this.1, this.2, ?_, ?_⟩
  · rw [IsClosed.closure_subset_iff hC.closed]
    apply inter_subset_right
  rw [Metric.ediam_closure]
  apply le_trans (Metric.ediam_mono inter_subset_left)
  convert! Metric.ediam_eball_le (x := x)
  rw [mul_comm]; rw [ENNReal.div_mul_cancel] <;> norm_num

/--
theorem `Perfect.small_diam_splitting` / 定理 `Perfect.small_diam_splitting`

English:
theorem Perfect.small_diam_splitting
  given: (hC : Perfect C) (hnonempty : C.Nonempty) (ε_pos : 0 < ε)
  proof: by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  obtain ⟨x₀, hx₀⟩ := non0
  obtain ⟨x₁, hx₁⟩ := non1
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1

中文:
定理 完美.small_diam_splitting
  条件: (hC : 完美 C) (hnonempty : C.非空) (ε_pos : 0 < ε)
  证明: by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  obtain ⟨x₀, hx₀⟩ := non0
  obtain ⟨x₁, hx₁⟩ := non1
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1

Depends on / 依赖: Disjoint, Disjoint.mono, Metric, Metric.eball, closure, hC.splitting, hnonempty, perf0.small_diam_aux, perf1.small_diam_aux, small_diam_aux, splitting
-/
theorem Perfect.small_diam_splitting (hC : Perfect C) (hnonempty : C.Nonempty) (ε_pos : 0 < ε) :
    exists C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ subseteq C ∧ Metric.ediam C₀ <= ε) ∧
    (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ subseteq C ∧ Metric.ediam C₁ <= ε) ∧ Disjoint C₀ C₁ := by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  obtain ⟨x₀, hx₀⟩ := non0
  obtain ⟨x₁, hx₁⟩ := non1
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩
  refine
    ⟨closure (Metric.eball x₀ (ε / 2) inter D₀), closure (Metric.eball x₁ (ε / 2) inter D₁),
      ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, ?_⟩
  apply Disjoint.mono _ _ hdisj <;> assumption

open CantorScheme

/--
theorem `Perfect.exists_nat_bool_injection` / 定理 `Perfect.exists_nat_bool_injection`

English:
theorem Perfect.exists_nat_bool_injection
  proof: by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' Real>=0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : Real>=0∞} (hε : 0

中文:
定理 完美.存在_nat_bool_injection
  证明: by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' Real>=0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : Real>=0∞} (hε : 0

Depends on / 依赖: C.Nonempty, E.Nonempty, Nonempty, Perfect, Subtype, exists_seq_strictAnti_tendsto, hC.small_diam_splitting, hnonempty, ih.property, l.len, property, small_diam_splitting, zero_lt_one
-/
theorem Perfect.exists_nat_bool_injection
    (hC : Perfect C) (hnonempty : C.Nonempty) [CompleteSpace α] :
    exists f : (Nat -> Bool) -> α, range f subseteq C ∧ Continuous f ∧ Injective f := by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' Real>=0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : Real>=0∞} (hε : 0 < ε) =>
    hC.small_diam_splitting hnonempty hε
  let DP : List Bool -> P := fun l => by
    induction l with
    | nil => exact ⟨C, ⟨hC, hnonempty⟩⟩
    | cons a l ih =>
      cases a
      · use C0 ih.property.1 ih.property.2 (upos (l.length + 1))
        exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩
      use C1 ih.property.1 ih.property.2 (upos (l.length + 1))
      exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩
  let D : List Bool -> Set α := fun l => (DP l).val
  have hanti : ClosureAntitone D := by
    refine Antitone.closureAntitone ?_ fun l => (DP l).property.1.closed
    intro l a
    cases a
    · exact (h0 _ _ _).2.2.1
    exact (h1 _ _ _).2.2.1
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m (hm : 1 <= m) => ?_⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert! (h0 _ _ _).2.2.2
      rw [PiNat.res_length]
    convert! (h1 _ _ _).2.2.2
    rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _
    exact (hdisj _ _ _).symm
  have hdom : forall {x : Nat -> Bool}, x in (inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam fun l => (DP l).property.2]
    apply mem_univ
  refine ⟨fun x => (inducedMap D).2 ⟨x, hdom⟩, ?_, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact map_mem ⟨_, hdom⟩ 0
  · apply hdiam.map_continuous.comp
    fun_prop
  intro x y hxy
  simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy

end CantorInjMetric

/--
theorem `IsClosed.exists_nat_bool_injection_of_not_countable` / 定理 `IsClosed.exists_nat_bool_injection_of_not_countable`

English:
theorem IsClosed.exists_nat_bool_injection_of_not_countable
  statement: {α : Type*} [TopologicalSpace α]
  proof: by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  exact ⟨f, hfD.trans hDC, hf⟩

中文:
定理 是闭集.存在_nat_bool_injection_of_not_countable
  结论: {α : 类型} [拓扑空间 α]
  证明: by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  exact ⟨f, hfD.trans hDC, hf⟩

Depends on / 依赖: Dnonempty, TopologicalSpace, TopologicalSpace.upgradeIsCompletelyMetrizable, exists_nat_bool_injection, exists_perfect_nonempty_of_isClosed_of_not_countable, hD.exists_nat_bool_injection, hfD.trans, upgradeIsCompletelyMetrizable
-/
theorem IsClosed.exists_nat_bool_injection_of_not_countable {α : Type*} [TopologicalSpace α]
    [PolishSpace α] {C : Set α} (hC : IsClosed C) (hunc : ¬C.Countable) :
    exists f : (Nat -> Bool) -> α, range f subseteq C ∧ Continuous f ∧ Function.Injective f := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  exact ⟨f, hfD.trans hDC, hf⟩
