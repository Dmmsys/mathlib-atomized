/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Convex sets are null-measurable

Let `E` be a finite-dimensional real vector space, let `μ` be a Haar measure on `E`, let `s` be a
convex set in `E`. Then the frontier of `s` has measure zero (see `Convex.addHaar_frontier`), hence
`s` is a `NullMeasurableSet` (see `Convex.nullMeasurableSet`).
-/

public section


open MeasureTheory MeasureTheory.Measure Set Metric Filter Bornology

open Module (finrank)

open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}

namespace Convex

/--
theorem `addHaar_frontier` / 定理 `addHaar_frontier`

English:
theorem addHaar_frontier
  given: (hs : Convex Real s)
  statement: μ (frontier s) = 0
  proof: by
  /- If `s` is included in a hyperplane, then `frontier s ⊆ closure s` is included in the same
    hyperplane, hence it has measure zero. -/
  rcases ne_or_eq (affineSpan Real s) ⊤ with hspan | hspan
  · refine measure_mono_null ?_ (addHaar_affineSubspace _ _ hspan)
    exact frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan _ _) (affineSpan Real s).closed_of_finiteDimensional)
  rw [← hs.interior_nonempty_iff_affineSpan_eq_top] at hspan
  rcases hspan with ⟨x, hx⟩
  /- Without loss of generality, `s` is bounded. Indeed, `∂s ⊆ ⋃ n, ∂(s ∩ ball x (n + 1))`, hence it
    suffices to prove that `∀ n, μ (s ∩ ball x (n + 1)) = 0`; the latter set is bounded.
    -/
  suffices H : forall t : Set E, Convex Real t -> x in interior t -> IsBounded t -> μ (frontier t) = 0 by
    let B : Nat -> Set E := fun n => ball x (n + 1)
    have : μ (⋃ n : Nat, frontier (s inter B n)) = 0 := by
      refine measure_iUnion_null fun n =>
        H _ (hs.inter (convex_ball _ _)) ?_ (isBounded_ball.subset inter_subset_right)
      rw [interior_inter]; rw [isOpen_ball.interior_eq]
      exact ⟨hx, mem_ball_self (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)⟩
    refine measure_mono_null (fun y hy => ?_) this; clear this
    set N : Nat := ⌊dist y x⌋₊
    refine mem_iUnion.2 ⟨N, ?_⟩
    have hN : y in B N := by simp [B, N, Nat.lt_floor_add_one]
    suffices y in frontier (s inter B N) inter B N from this.1
    rw [frontier_inter_open_inter isOpen_ball]
    exact ⟨hy, hN⟩
  intro s hs hx hb
  /- Since `s` is bounded, we have `μ (interior s) ≠ ∞`, hence it suffices to prove
    `μ (closure s) ≤ μ (interior s)`. -/
  replace hb : μ (interior s) != ∞ := (hb.subset interior_subset).measure_lt_top.ne
  suffices μ (closure s) <= μ (interior s) by
    rwa [frontier, measure_sdiff interior_subset_closure isOpen_interior.nullMeasurableSet hb,
      tsub_eq_zero_iff_le]
  /- Due to `Convex.closure_subset_image_homothety_interior_of_one_lt`, for any `r > 1` we have
    `closure s ⊆ homothety x r '' interior s`, hence `μ (closure s) ≤ r ^ d * μ (interior s)`,
    where `d = finrank ℝ E`. -/
  set d : Nat := Module.finrank Real E
  have : forall r : Real>=0, 1 < r -> μ (closure s) <= ↑(r ^ d) * μ (interior s) := fun r hr => by
    refine (measure_mono <|
      hs.closure_subset_image_homothety_interior_of_one_lt hx r hr).trans_eq ?_
    rw [addHaar_image_homothety]; rw [← NNReal.coe_pow]; rw [NNReal.abs_eq]; rw [ENNReal.ofReal_coe_nnreal]
  have : forallᶠ (r : Real>=0) in 𝓝[>] 1, μ (closure s) <= ↑(r ^ d) * μ (interior s) :=
    mem_of_superset self_mem_nhdsWithin this
  -- Taking the limit as `r → 1`, we get `μ (closure s) ≤ μ (interior s)`.
  refine ge_of_tendsto ?_ this
  refine (((ENNReal.continuous_mul_const hb).comp
    (ENNReal.continuous_coe.comp (continuous_pow d))).tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
  simp

中文:
定理 addHaar_frontier
  条件: (hs : 凸 实数 s)
  结论: μ (frontier s) = 0
  证明: by
  /- If `s` is included in a hyperplane, then `frontier s ⊆ closure s` is included in the same
    hyperplane, hence it has measure zero. -/
  rcases ne_or_eq (affineSpan Real s) ⊤ with hspan | hspan
  · refine measure_mono_null ?_ (addHaar_affineSubspace _ _ hspan)
    exact frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan _ _) (affineSpan Real s).closed_of_finiteDimensional)
  rw [← hs.interior_nonempty_iff_affineSpan_eq_top] at hspan
  rcases hspan with ⟨x, hx⟩
  /- Without loss of generality, `s` is bounded. Indeed, `∂s ⊆ ⋃ n, ∂(s ∩ ball x (n + 1))`, hence it
    suffices to prove that `∀ n, μ (s ∩ ball x (n + 1)) = 0`; the latter set is bounded.
    -/
  suffices H : forall t : Set E, Convex Real t -> x in interior t -> IsBounded t -> μ (frontier t) = 0 by
    let B : Nat -> Set E := fun n => ball x (n + 1)
    have : μ (⋃ n : Nat, frontier (s inter B n)) = 0 := by
      refine measure_iUnion_null fun n =>
        H _ (hs.inter (convex_ball _ _)) ?_ (isBounded_ball.subset inter_subset_right)
      rw [interior_inter]; rw [isOpen_ball.interior_eq]
      exact ⟨hx, mem_ball_self (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)⟩
    refine measure_mono_null (fun y hy => ?_) this; clear this
    set N : Nat := ⌊dist y x⌋₊
    refine mem_iUnion.2 ⟨N, ?_⟩
    have hN : y in B N := by simp [B, N, Nat.lt_floor_add_one]
    suffices y in frontier (s inter B N) inter B N from this.1
    rw [frontier_inter_open_inter isOpen_ball]
    exact ⟨hy, hN⟩
  intro s hs hx hb
  /- Since `s` is bounded, we have `μ (interior s) ≠ ∞`, hence it suffices to prove
    `μ (closure s) ≤ μ (interior s)`. -/
  replace hb : μ (interior s) != ∞ := (hb.subset interior_subset).measure_lt_top.ne
  suffices μ (closure s) <= μ (interior s) by
    rwa [frontier, measure_sdiff interior_subset_closure isOpen_interior.nullMeasurableSet hb,
      tsub_eq_zero_iff_le]
  /- Due to `Convex.closure_subset_image_homothety_interior_of_one_lt`, for any `r > 1` we have
    `closure s ⊆ homothety x r '' interior s`, hence `μ (closure s) ≤ r ^ d * μ (interior s)`,
    where `d = finrank ℝ E`. -/
  set d : Nat := Module.finrank Real E
  have : forall r : Real>=0, 1 < r -> μ (closure s) <= ↑(r ^ d) * μ (interior s) := fun r hr => by
    refine (measure_mono <|
      hs.closure_subset_image_homothety_interior_of_one_lt hx r hr).trans_eq ?_
    rw [addHaar_image_homothety]; rw [← NNReal.coe_pow]; rw [NNReal.abs_eq]; rw [ENNReal.ofReal_coe_nnreal]
  have : forallᶠ (r : Real>=0) in 𝓝[>] 1, μ (closure s) <= ↑(r ^ d) * μ (interior s) :=
    mem_of_superset self_mem_nhdsWithin this
  -- Taking the limit as `r → 1`, we get `μ (closure s) ≤ μ (interior s)`.
  refine ge_of_tendsto ?_ this
  refine (((ENNReal.continuous_mul_const hb).comp
    (ENNReal.continuous_coe.comp (continuous_pow d))).tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
  simp
-/
theorem addHaar_frontier (hs : Convex Real s) : μ (frontier s) = 0 := by
  /- If `s` is included in a hyperplane, then `frontier s ⊆ closure s` is included in the same
    hyperplane, hence it has measure zero. -/
  rcases ne_or_eq (affineSpan Real s) ⊤ with hspan | hspan
  · refine measure_mono_null ?_ (addHaar_affineSubspace _ _ hspan)
    exact frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan _ _) (affineSpan Real s).closed_of_finiteDimensional)
  rw [← hs.interior_nonempty_iff_affineSpan_eq_top] at hspan
  rcases hspan with ⟨x, hx⟩
  /- Without loss of generality, `s` is bounded. Indeed, `∂s ⊆ ⋃ n, ∂(s ∩ ball x (n + 1))`, hence it
    suffices to prove that `∀ n, μ (s ∩ ball x (n + 1)) = 0`; the latter set is bounded.
    -/
  suffices H : forall t : Set E, Convex Real t -> x in interior t -> IsBounded t -> μ (frontier t) = 0 by
    let B : Nat -> Set E := fun n => ball x (n + 1)
    have : μ (⋃ n : Nat, frontier (s inter B n)) = 0 := by
      refine measure_iUnion_null fun n =>
        H _ (hs.inter (convex_ball _ _)) ?_ (isBounded_ball.subset inter_subset_right)
      rw [interior_inter]; rw [isOpen_ball.interior_eq]
      exact ⟨hx, mem_ball_self (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)⟩
    refine measure_mono_null (fun y hy => ?_) this; clear this
    set N : Nat := ⌊dist y x⌋₊
    refine mem_iUnion.2 ⟨N, ?_⟩
    have hN : y in B N := by simp [B, N, Nat.lt_floor_add_one]
    suffices y in frontier (s inter B N) inter B N from this.1
    rw [frontier_inter_open_inter isOpen_ball]
    exact ⟨hy, hN⟩
  intro s hs hx hb
  /- Since `s` is bounded, we have `μ (interior s) ≠ ∞`, hence it suffices to prove
    `μ (closure s) ≤ μ (interior s)`. -/
  replace hb : μ (interior s) != ∞ := (hb.subset interior_subset).measure_lt_top.ne
  suffices μ (closure s) <= μ (interior s) by
    rwa [frontier, measure_sdiff interior_subset_closure isOpen_interior.nullMeasurableSet hb,
      tsub_eq_zero_iff_le]
  /- Due to `Convex.closure_subset_image_homothety_interior_of_one_lt`, for any `r > 1` we have
    `closure s ⊆ homothety x r '' interior s`, hence `μ (closure s) ≤ r ^ d * μ (interior s)`,
    where `d = finrank ℝ E`. -/
  set d : Nat := Module.finrank Real E
  have : forall r : Real>=0, 1 < r -> μ (closure s) <= ↑(r ^ d) * μ (interior s) := fun r hr => by
    refine (measure_mono <|
      hs.closure_subset_image_homothety_interior_of_one_lt hx r hr).trans_eq ?_
    rw [addHaar_image_homothety]; rw [← NNReal.coe_pow]; rw [NNReal.abs_eq]; rw [ENNReal.ofReal_coe_nnreal]
  have : forallᶠ (r : Real>=0) in 𝓝[>] 1, μ (closure s) <= ↑(r ^ d) * μ (interior s) :=
    mem_of_superset self_mem_nhdsWithin this
  -- Taking the limit as `r → 1`, we get `μ (closure s) ≤ μ (interior s)`.
  refine ge_of_tendsto ?_ this
  refine (((ENNReal.continuous_mul_const hb).comp
    (ENNReal.continuous_coe.comp (continuous_pow d))).tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
  simp

/--
theorem `nullMeasurableSet` / 定理 `nullMeasurableSet`

English:
theorem nullMeasurableSet
  given: (hs : Convex Real s)
  statement: NullMeasurableSet s μ
  proof: nullMeasurableSet_of_null_frontier (hs.addHaar_frontier μ)

中文:
定理 nullMeasurableSet
  条件: (hs : 凸 实数 s)
  结论: NullMeasurableSet s μ
  证明: nullMeasurableSet_of_null_frontier (hs.addHaar_frontier μ)
-/
protected theorem nullMeasurableSet (hs : Convex Real s) : NullMeasurableSet s μ :=
  nullMeasurableSet_of_null_frontier (hs.addHaar_frontier μ)

end Convex
