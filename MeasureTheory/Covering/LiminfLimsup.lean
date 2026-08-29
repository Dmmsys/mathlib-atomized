/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Liminf, limsup, and uniformly locally doubling measures.

This file is a place to collect lemmas about liminf and limsup for subsets of a metric space
carrying a uniformly locally doubling measure.

## Main results:

* `blimsup_cthickening_mul_ae_eq`: the limsup of the closed thickening of a sequence of subsets
  of a metric space is unchanged almost everywhere for a uniformly locally doubling measure if the
  sequence of distances is multiplied by a positive scale factor. This is a generalisation of a
  result of Cassels, appearing as Lemma 9 on page 217 of
  [J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).
* `blimsup_thickening_mul_ae_eq`: a variant of `blimsup_cthickening_mul_ae_eq` for thickenings
  rather than closed thickenings.

-/

public section


open Set Filter Metric MeasureTheory TopologicalSpace

open scoped NNReal ENNReal Topology

variable {α : Type*}
variable [PseudoMetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable (μ : Measure α) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]

/--
theorem `blimsup_cthickening_ae_le_of_eventually_mul_le_aux` / 定理 `blimsup_cthickening_ae_le_of_eventually_mul_le_aux`

English:
theorem blimsup_cthickening_ae_le_of_eventually_mul_le_aux
  statement: (p : Nat -> Prop) {s : Nat -> Set α}
  proof: by
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
  `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
  showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closedBall (w j) (r₁ (f j))`. Note that
  since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
  measure `μ`.

  To prove the claim, let `b j = closedBall (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  set Y₁ : Nat -> Set α := fun i => cthickening (r₁ i) (s i)
  set Y₂ : Nat -> Set α := fun i => cthickening (r₂ i) (s i)
  let Z : Nat -> Set α := fun i => ⋃ (j) (_ : p j ∧ i <= j), Y₂ j
  suffices forall i, μ (atTop.blimsup Y₁ p \ Z i) = 0 by
    rwa [ae_le_set, @blimsup_eq_iInf_biSup_of_nat _ _ _ Y₂, iInf_eq_iInter, sdiff_iInter,
      measure_iUnion_null_iff]
  intro i
  set W := atTop.blimsup Y₁ p \ Z i
  by_contra contra
  obtain ⟨d, hd, hd'⟩ : exists d, d in W ∧ forall {ι : Type _} {l : Filter ι} (w : ι -> α) (δ : ι -> Real),
      Tendsto δ l (𝓝[>] 0) -> (forallᶠ j in l, d in closedBall (w j) (2 * δ j)) ->
        Tendsto (fun j => μ (W inter closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae contra
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ W 2)
  replace hd : d in blimsup Y₁ atTop p := ((mem_sdiff _).mp hd).1
  obtain ⟨f : Nat -> Nat, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup' atTop_basis hd
  simp only [forall_and] at hf
  obtain ⟨hf₀ : forall j, d in cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : forall j, j <= f j⟩ := hf
  have hf₃ : Tendsto f atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨f j, fun i hi => (hf₂ j).trans (hi.trans <| hf₂ i)⟩
  replace hr : Tendsto (r₁ ∘ f) atTop (𝓝[>] 0) := hr.comp hf₃
  replace hMr : forallᶠ j in atTop, M * r₁ (f j) <= r₂ (f j) := hf₃.eventually hMr
  replace hf₀ : forall j, exists w in s (f j), d in closedBall w (2 * r₁ (f j)) := by
    intro j
    specialize hrp (f j)
    rw [Pi.zero_apply] at hrp
    rcases eq_or_lt_of_le hrp with (hr0 | hrp')
    · specialize hf₀ j
      rw [← hr0]; rw [cthickening_zero]; rw [(hs (f j)).closure_eq] at hf₀
      exact ⟨d, hf₀, by simp [← hr0]⟩
    · simpa using mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (s (f j))
        (by positivity) (lt_two_mul_self hrp') (hf₀ j))
  choose w hw hw' using hf₀
  let C := IsUnifLocDoublingMeasure.scalingConstantOf μ M⁻¹
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ M⁻¹)
  suffices exists η < (1 : Real>=0),
      forallᶠ j in atTop, μ (W inter closedBall (w j) (r₁ (f j))) / μ (closedBall (w j) (r₁ (f j))) <= η by
    obtain ⟨η, hη, hη'⟩ := this
    replace hη' : 1 <= η := by
      simpa only [ENNReal.one_le_coe_iff] using
        le_of_tendsto (hd' w (fun j => r₁ (f j)) hr <| Eventually.of_forall hw') hη'
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη')
  refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), ?_⟩
  replace hC : C != 0 := ne_of_gt hC
  let b : Nat -> Set α := fun j => closedBall (w j) (M * r₁ (f j))
  let B : Nat -> Set α := fun j => closedBall (w j) (r₁ (f j))
  have h₁ : forall j, b j subseteq B j := fun j =>
    closedBall_subset_closedBall (mul_le_of_le_one_left (hrp (f j)) hM'.le)
  have h₂ : forall j, W inter B j subseteq B j := fun j => inter_subset_right
  have h₃ : forallᶠ j in atTop, Disjoint (b j) (W inter B j) := by
    apply hMr.mp
    rw [eventually_atTop]
    refine
⟨i, fun j hj hj' => Disjoint.inf_right (B j) Disjoint.inf_right' (blimsup Y₁ atTop p) ?_⟩
    change Disjoint (b j) (Z i)ᶜ
    rw [disjoint_compl_right_iff_subset]
    refine (closedBall_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans fun a ha => ?_)
    simp only [Z, mem_iUnion, exists_prop]
    exact ⟨f j, ⟨hf₁ j, hj.trans (hf₂ j)⟩, ha⟩
  have h₄ : forallᶠ j in atTop, μ (B j) <= C * μ (b j) :=
    (hr.eventually (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono fun j hj => hj (w j)
  refine (h₃.and h₄).mono fun j hj₀ => ?_
  change μ (W inter B j) / μ (B j) <= ↑(1 - C⁻¹)
  rcases eq_or_ne (μ (B j)) ∞ with (hB | hB); · simp [hB]
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.coe_sub]; rw [ENNReal.coe_one]; rw [ENNReal.sub_mul fun _ _ => hB]; rw [one_mul]
  replace hB : ↑C⁻¹ * μ (B j) != ∞ := by finiteness
  obtain ⟨hj₁ : Disjoint (b j) (W inter B j), hj₂ : μ (B j) <= C * μ (b j)⟩ := hj₀
  replace hj₂ : ↑C⁻¹ * μ (B j) <= μ (b j) := by
    rw [ENNReal.coe_inv hC]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_le_of_le_mul' hj₂
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W inter B j) <= μ (B j) := by
    grw [hj₂]
    rw [← measure_union' hj₁ measurableSet_closedBall]
    grw [union_subset (h₁ j) (h₂ j)]
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j))
  rwa [ENNReal.add_sub_cancel_left hB] at hj₃

中文:
定理 blimsup_cthickening_ae_le_of_eventually_mul_le_aux
  结论: (p : 自然数 -> 命题) {s : 自然数 -> 集合 α}
  证明: by
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
  `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
  showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closedBall (w j) (r₁ (f j))`. Note that
  since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
  measure `μ`.

  To prove the claim, let `b j = closedBall (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  set Y₁ : Nat -> Set α := fun i => cthickening (r₁ i) (s i)
  set Y₂ : Nat -> Set α := fun i => cthickening (r₂ i) (s i)
  let Z : Nat -> Set α := fun i => ⋃ (j) (_ : p j ∧ i <= j), Y₂ j
  suffices forall i, μ (atTop.blimsup Y₁ p \ Z i) = 0 by
    rwa [ae_le_set, @blimsup_eq_iInf_biSup_of_nat _ _ _ Y₂, iInf_eq_iInter, sdiff_iInter,
      measure_iUnion_null_iff]
  intro i
  set W := atTop.blimsup Y₁ p \ Z i
  by_contra contra
  obtain ⟨d, hd, hd'⟩ : exists d, d in W ∧ forall {ι : Type _} {l : Filter ι} (w : ι -> α) (δ : ι -> Real),
      Tendsto δ l (𝓝[>] 0) -> (forallᶠ j in l, d in closedBall (w j) (2 * δ j)) ->
        Tendsto (fun j => μ (W inter closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae contra
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ W 2)
  replace hd : d in blimsup Y₁ atTop p := ((mem_sdiff _).mp hd).1
  obtain ⟨f : Nat -> Nat, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup' atTop_basis hd
  simp only [forall_and] at hf
  obtain ⟨hf₀ : forall j, d in cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : forall j, j <= f j⟩ := hf
  have hf₃ : Tendsto f atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨f j, fun i hi => (hf₂ j).trans (hi.trans <| hf₂ i)⟩
  replace hr : Tendsto (r₁ ∘ f) atTop (𝓝[>] 0) := hr.comp hf₃
  replace hMr : forallᶠ j in atTop, M * r₁ (f j) <= r₂ (f j) := hf₃.eventually hMr
  replace hf₀ : forall j, exists w in s (f j), d in closedBall w (2 * r₁ (f j)) := by
    intro j
    specialize hrp (f j)
    rw [Pi.zero_apply] at hrp
    rcases eq_or_lt_of_le hrp with (hr0 | hrp')
    · specialize hf₀ j
      rw [← hr0]; rw [cthickening_zero]; rw [(hs (f j)).closure_eq] at hf₀
      exact ⟨d, hf₀, by simp [← hr0]⟩
    · simpa using mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (s (f j))
        (by positivity) (lt_two_mul_self hrp') (hf₀ j))
  choose w hw hw' using hf₀
  let C := IsUnifLocDoublingMeasure.scalingConstantOf μ M⁻¹
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ M⁻¹)
  suffices exists η < (1 : Real>=0),
      forallᶠ j in atTop, μ (W inter closedBall (w j) (r₁ (f j))) / μ (closedBall (w j) (r₁ (f j))) <= η by
    obtain ⟨η, hη, hη'⟩ := this
    replace hη' : 1 <= η := by
      simpa only [ENNReal.one_le_coe_iff] using
        le_of_tendsto (hd' w (fun j => r₁ (f j)) hr <| Eventually.of_forall hw') hη'
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη')
  refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), ?_⟩
  replace hC : C != 0 := ne_of_gt hC
  let b : Nat -> Set α := fun j => closedBall (w j) (M * r₁ (f j))
  let B : Nat -> Set α := fun j => closedBall (w j) (r₁ (f j))
  have h₁ : forall j, b j subseteq B j := fun j =>
    closedBall_subset_closedBall (mul_le_of_le_one_left (hrp (f j)) hM'.le)
  have h₂ : forall j, W inter B j subseteq B j := fun j => inter_subset_right
  have h₃ : forallᶠ j in atTop, Disjoint (b j) (W inter B j) := by
    apply hMr.mp
    rw [eventually_atTop]
    refine
⟨i, fun j hj hj' => Disjoint.inf_right (B j) Disjoint.inf_right' (blimsup Y₁ atTop p) ?_⟩
    change Disjoint (b j) (Z i)ᶜ
    rw [disjoint_compl_right_iff_subset]
    refine (closedBall_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans fun a ha => ?_)
    simp only [Z, mem_iUnion, exists_prop]
    exact ⟨f j, ⟨hf₁ j, hj.trans (hf₂ j)⟩, ha⟩
  have h₄ : forallᶠ j in atTop, μ (B j) <= C * μ (b j) :=
    (hr.eventually (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono fun j hj => hj (w j)
  refine (h₃.and h₄).mono fun j hj₀ => ?_
  change μ (W inter B j) / μ (B j) <= ↑(1 - C⁻¹)
  rcases eq_or_ne (μ (B j)) ∞ with (hB | hB); · simp [hB]
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.coe_sub]; rw [ENNReal.coe_one]; rw [ENNReal.sub_mul fun _ _ => hB]; rw [one_mul]
  replace hB : ↑C⁻¹ * μ (B j) != ∞ := by finiteness
  obtain ⟨hj₁ : Disjoint (b j) (W inter B j), hj₂ : μ (B j) <= C * μ (b j)⟩ := hj₀
  replace hj₂ : ↑C⁻¹ * μ (B j) <= μ (b j) := by
    rw [ENNReal.coe_inv hC]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_le_of_le_mul' hj₂
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W inter B j) <= μ (B j) := by
    grw [hj₂]
    rw [← measure_union' hj₁ measurableSet_closedBall]
    grw [union_subset (h₁ j) (h₂ j)]
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j))
  rwa [ENNReal.add_sub_cancel_left hB] at hj₃
-/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le_aux (p : Nat -> Prop) {s : Nat -> Set α}
    (hs : forall i, IsClosed (s i)) {r₁ r₂ : Nat -> Real} (hr : Tendsto r₁ atTop (𝓝[>] 0)) (hrp : 0 <= r₁)
    {M : Real} (hM : 0 < M) (hM' : M < 1) (hMr : forallᶠ i in atTop, M * r₁ i <= r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) <=ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
  `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
  showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closedBall (w j) (r₁ (f j))`. Note that
  since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
  measure `μ`.

  To prove the claim, let `b j = closedBall (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  set Y₁ : Nat -> Set α := fun i => cthickening (r₁ i) (s i)
  set Y₂ : Nat -> Set α := fun i => cthickening (r₂ i) (s i)
  let Z : Nat -> Set α := fun i => ⋃ (j) (_ : p j ∧ i <= j), Y₂ j
  suffices forall i, μ (atTop.blimsup Y₁ p \ Z i) = 0 by
    rwa [ae_le_set, @blimsup_eq_iInf_biSup_of_nat _ _ _ Y₂, iInf_eq_iInter, sdiff_iInter,
      measure_iUnion_null_iff]
  intro i
  set W := atTop.blimsup Y₁ p \ Z i
  by_contra contra
  obtain ⟨d, hd, hd'⟩ : exists d, d in W ∧ forall {ι : Type _} {l : Filter ι} (w : ι -> α) (δ : ι -> Real),
      Tendsto δ l (𝓝[>] 0) -> (forallᶠ j in l, d in closedBall (w j) (2 * δ j)) ->
        Tendsto (fun j => μ (W inter closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae contra
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ W 2)
  replace hd : d in blimsup Y₁ atTop p := ((mem_sdiff _).mp hd).1
  obtain ⟨f : Nat -> Nat, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup' atTop_basis hd
  simp only [forall_and] at hf
  obtain ⟨hf₀ : forall j, d in cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : forall j, j <= f j⟩ := hf
  have hf₃ : Tendsto f atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨f j, fun i hi => (hf₂ j).trans (hi.trans <| hf₂ i)⟩
  replace hr : Tendsto (r₁ ∘ f) atTop (𝓝[>] 0) := hr.comp hf₃
  replace hMr : forallᶠ j in atTop, M * r₁ (f j) <= r₂ (f j) := hf₃.eventually hMr
  replace hf₀ : forall j, exists w in s (f j), d in closedBall w (2 * r₁ (f j)) := by
    intro j
    specialize hrp (f j)
    rw [Pi.zero_apply] at hrp
    rcases eq_or_lt_of_le hrp with (hr0 | hrp')
    · specialize hf₀ j
      rw [← hr0]; rw [cthickening_zero]; rw [(hs (f j)).closure_eq] at hf₀
      exact ⟨d, hf₀, by simp [← hr0]⟩
    · simpa using mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (s (f j))
        (by positivity) (lt_two_mul_self hrp') (hf₀ j))
  choose w hw hw' using hf₀
  let C := IsUnifLocDoublingMeasure.scalingConstantOf μ M⁻¹
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ M⁻¹)
  suffices exists η < (1 : Real>=0),
      forallᶠ j in atTop, μ (W inter closedBall (w j) (r₁ (f j))) / μ (closedBall (w j) (r₁ (f j))) <= η by
    obtain ⟨η, hη, hη'⟩ := this
    replace hη' : 1 <= η := by
      simpa only [ENNReal.one_le_coe_iff] using
        le_of_tendsto (hd' w (fun j => r₁ (f j)) hr <| Eventually.of_forall hw') hη'
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη')
  refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), ?_⟩
  replace hC : C != 0 := ne_of_gt hC
  let b : Nat -> Set α := fun j => closedBall (w j) (M * r₁ (f j))
  let B : Nat -> Set α := fun j => closedBall (w j) (r₁ (f j))
  have h₁ : forall j, b j subseteq B j := fun j =>
    closedBall_subset_closedBall (mul_le_of_le_one_left (hrp (f j)) hM'.le)
  have h₂ : forall j, W inter B j subseteq B j := fun j => inter_subset_right
  have h₃ : forallᶠ j in atTop, Disjoint (b j) (W inter B j) := by
    apply hMr.mp
    rw [eventually_atTop]
    refine
⟨i, fun j hj hj' => Disjoint.inf_right (B j) Disjoint.inf_right' (blimsup Y₁ atTop p) ?_⟩
    change Disjoint (b j) (Z i)ᶜ
    rw [disjoint_compl_right_iff_subset]
    refine (closedBall_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans fun a ha => ?_)
    simp only [Z, mem_iUnion, exists_prop]
    exact ⟨f j, ⟨hf₁ j, hj.trans (hf₂ j)⟩, ha⟩
  have h₄ : forallᶠ j in atTop, μ (B j) <= C * μ (b j) :=
    (hr.eventually (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono fun j hj => hj (w j)
  refine (h₃.and h₄).mono fun j hj₀ => ?_
  change μ (W inter B j) / μ (B j) <= ↑(1 - C⁻¹)
  rcases eq_or_ne (μ (B j)) ∞ with (hB | hB); · simp [hB]
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.coe_sub]; rw [ENNReal.coe_one]; rw [ENNReal.sub_mul fun _ _ => hB]; rw [one_mul]
  replace hB : ↑C⁻¹ * μ (B j) != ∞ := by finiteness
  obtain ⟨hj₁ : Disjoint (b j) (W inter B j), hj₂ : μ (B j) <= C * μ (b j)⟩ := hj₀
  replace hj₂ : ↑C⁻¹ * μ (B j) <= μ (b j) := by
    rw [ENNReal.coe_inv hC]; rw [← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_le_of_le_mul' hj₂
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W inter B j) <= μ (B j) := by
    grw [hj₂]
    rw [← measure_union' hj₁ measurableSet_closedBall]
    grw [union_subset (h₁ j) (h₂ j)]
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j))
  rwa [ENNReal.add_sub_cancel_left hB] at hj₃

/--
theorem `blimsup_cthickening_ae_le_of_eventually_mul_le` / 定理 `blimsup_cthickening_ae_le_of_eventually_mul_le`

English:
theorem blimsup_cthickening_ae_le_of_eventually_mul_le
  statement: (p : Nat -> Prop) {s : Nat -> Set α} {M : Real}
  proof: by
  let R₁ i := max 0 (r₁ i)
  let R₂ i := max 0 (r₂ i)
  have hRp : 0 <= R₁ := fun i => le_max_left 0 (r₁ i)
  replace hMr : forallᶠ i in atTop, M * R₁ i <= R₂ i := by
    refine hMr.mono fun i hi => ?_
    rw [mul_max_of_nonneg _ _ hM.le]; rw [mul_zero]
    exact max_le_max (le_refl 0) hi
  simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)]
  rcases le_or_gt 1 M with hM' | hM'
  · apply LE.le.eventuallyLE
    refine mono_blimsup' (hMr.mono fun i hi _ => cthickening_mono ?_ (s i))
    exact (le_mul_of_one_le_left (hRp i) hM').trans hi
  · simp only [← @cthickening_closure _ _ _ (s _)]
    have hs : forall i, IsClosed (closure (s i)) := fun i => isClosed_closure
    exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux μ p hs
      (tendsto_nhds_max_right hr) hRp hM hM' hMr

中文:
定理 blimsup_cthickening_ae_le_of_eventually_mul_le
  结论: (p : 自然数 -> 命题) {s : 自然数 -> 集合 α} {M : 实数}
  证明: by
  let R₁ i := max 0 (r₁ i)
  let R₂ i := max 0 (r₂ i)
  have hRp : 0 <= R₁ := fun i => le_max_left 0 (r₁ i)
  replace hMr : forallᶠ i in atTop, M * R₁ i <= R₂ i := by
    refine hMr.mono fun i hi => ?_
    rw [mul_max_of_nonneg _ _ hM.le]; rw [mul_zero]
    exact max_le_max (le_refl 0) hi
  simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)]
  rcases le_or_gt 1 M with hM' | hM'
  · apply LE.le.eventuallyLE
    refine mono_blimsup' (hMr.mono fun i hi _ => cthickening_mono ?_ (s i))
    exact (le_mul_of_one_le_left (hRp i) hM').trans hi
  · simp only [← @cthickening_closure _ _ _ (s _)]
    have hs : forall i, IsClosed (closure (s i)) := fun i => isClosed_closure
    exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux μ p hs
      (tendsto_nhds_max_right hr) hRp hM hM' hMr

Depends on / 依赖: LE.le.eventuallyLE, cthickening_max_zero, cthickening_mono, eventuallyLE, hM.le, hMr.mono, le_max_left, le_mul_of_one_l, le_or_gt, le_refl, max_le_max, mono_blimsup, mul_max_of_nonneg, mul_zero, replace, simp_rw
-/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le (p : Nat -> Prop) {s : Nat -> Set α} {M : Real}
    (hM : 0 < M) {r₁ r₂ : Nat -> Real} (hr : Tendsto r₁ atTop (𝓝[>] 0))
    (hMr : forallᶠ i in atTop, M * r₁ i <= r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) <=ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  let R₁ i := max 0 (r₁ i)
  let R₂ i := max 0 (r₂ i)
  have hRp : 0 <= R₁ := fun i => le_max_left 0 (r₁ i)
  replace hMr : forallᶠ i in atTop, M * R₁ i <= R₂ i := by
    refine hMr.mono fun i hi => ?_
    rw [mul_max_of_nonneg _ _ hM.le]; rw [mul_zero]
    exact max_le_max (le_refl 0) hi
  simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)]
  rcases le_or_gt 1 M with hM' | hM'
  · apply LE.le.eventuallyLE
    refine mono_blimsup' (hMr.mono fun i hi _ => cthickening_mono ?_ (s i))
    exact (le_mul_of_one_le_left (hRp i) hM').trans hi
  · simp only [← @cthickening_closure _ _ _ (s _)]
    have hs : forall i, IsClosed (closure (s i)) := fun i => isClosed_closure
    exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux μ p hs
      (tendsto_nhds_max_right hr) hRp hM hM' hMr

/--
theorem `blimsup_cthickening_mul_ae_eq` / 定理 `blimsup_cthickening_mul_ae_eq`

English:
theorem blimsup_cthickening_mul_ae_eq
  statement: (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M)
  proof: by
  have : forall (p : Nat -> Prop) {r : Nat -> Real} (_ : Tendsto r atTop (𝓝[>] 0)),
      (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
        (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
    clear p hr r; intro p r hr
    have hr' : Tendsto (fun i => M * r i) atTop (𝓝[>] 0) := by
      convert! TendstoNhdsWithinIoi.const_mul hM hr <;> simp only [mul_zero]
    refine eventuallyLE_antisymm_iff.mpr ⟨?_, ?_⟩
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
        (Eventually.of_forall fun i => by rw [inv_mul_cancel_left₀ hM.ne' (r i)])
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
        (Eventually.of_forall fun i => le_refl _)
  let r' : Nat -> Real := fun i => if 0 < r i then r i else 1 / ((i : Real) + 1)
  have hr' : Tendsto r' atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun i => ?_⟩
    by_cases hi : 0 < r i
    · simp [r', hi]
    · simp only [r', hi, one_div, mem_Ioi, if_false, inv_pos]; positivity
  have h₀ : forall i, p i ∧ 0 < r i -> cthickening (r i) (s i) = cthickening (r' i) (s i) := by
    grind
  have h₁ : forall i, p i ∧ 0 < r i -> cthickening (M * r i) (s i) = cthickening (M * r' i) (s i) := by
    rintro i ⟨-, hi⟩; simp only [r', hi, if_true]
  have h₂ : forall i, p i ∧ r i <= 0 -> cthickening (M * r i) (s i) = cthickening (r i) (s i) := by
    rintro i ⟨-, hi⟩
    have hi' : M * r i <= 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi
    rw [cthickening_of_nonpos hi]; rw [cthickening_of_nonpos hi']
  have hp : p = fun i => p i ∧ 0 < r i ∨ p i ∧ r i <= 0 := by
    ext i; simp [← and_or_left, lt_or_ge 0 (r i)]
  rw [hp]; rw [blimsup_or_eq_sup]; rw [blimsup_or_eq_sup]
  simp only [sup_eq_union]
  rw [blimsup_congr (Eventually.of_forall h₀)]; rw [blimsup_congr (Eventually.of_forall h₁)]; rw [blimsup_congr (Eventually.of_forall h₂)]
  exact ae_eq_set_union (this (fun i => p i ∧ 0 < r i) hr') (ae_eq_refl _)

中文:
定理 blimsup_cthickening_mul_ae_eq
  结论: (p : 自然数 -> 命题) (s : 自然数 -> 集合 α) {M : 实数} (hM : 0 < M)
  证明: by
  have : forall (p : Nat -> Prop) {r : Nat -> Real} (_ : Tendsto r atTop (𝓝[>] 0)),
      (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
        (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
    clear p hr r; intro p r hr
    have hr' : Tendsto (fun i => M * r i) atTop (𝓝[>] 0) := by
      convert! TendstoNhdsWithinIoi.const_mul hM hr <;> simp only [mul_zero]
    refine eventuallyLE_antisymm_iff.mpr ⟨?_, ?_⟩
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
        (Eventually.of_forall fun i => by rw [inv_mul_cancel_left₀ hM.ne' (r i)])
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
        (Eventually.of_forall fun i => le_refl _)
  let r' : Nat -> Real := fun i => if 0 < r i then r i else 1 / ((i : Real) + 1)
  have hr' : Tendsto r' atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun i => ?_⟩
    by_cases hi : 0 < r i
    · simp [r', hi]
    · simp only [r', hi, one_div, mem_Ioi, if_false, inv_pos]; positivity
  have h₀ : forall i, p i ∧ 0 < r i -> cthickening (r i) (s i) = cthickening (r' i) (s i) := by
    grind
  have h₁ : forall i, p i ∧ 0 < r i -> cthickening (M * r i) (s i) = cthickening (M * r' i) (s i) := by
    rintro i ⟨-, hi⟩; simp only [r', hi, if_true]
  have h₂ : forall i, p i ∧ r i <= 0 -> cthickening (M * r i) (s i) = cthickening (r i) (s i) := by
    rintro i ⟨-, hi⟩
    have hi' : M * r i <= 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi
    rw [cthickening_of_nonpos hi]; rw [cthickening_of_nonpos hi']
  have hp : p = fun i => p i ∧ 0 < r i ∨ p i ∧ r i <= 0 := by
    ext i; simp [← and_or_left, lt_or_ge 0 (r i)]
  rw [hp]; rw [blimsup_or_eq_sup]; rw [blimsup_or_eq_sup]
  simp only [sup_eq_union]
  rw [blimsup_congr (Eventually.of_forall h₀)]; rw [blimsup_congr (Eventually.of_forall h₁)]; rw [blimsup_congr (Eventually.of_forall h₂)]
  exact ae_eq_set_union (this (fun i => p i ∧ 0 < r i) hr') (ae_eq_refl _)

Depends on / 依赖: Tendsto, TendstoNhdsWithinIoi, TendstoNhdsWithinIoi.const_mul, blimsup, blimsup_cthickening_ae_le_of_eventually_mul_le, const_mul, convert, cthickening, eventuallyLE_antisymm_iff, eventuallyLE_antisymm_iff.mpr, inv_pos, inv_pos.mpr, mul_zero
-/
theorem blimsup_cthickening_mul_ae_eq (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M)
    (r : Nat -> Real) (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
  have : forall (p : Nat -> Prop) {r : Nat -> Real} (_ : Tendsto r atTop (𝓝[>] 0)),
      (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
        (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
    clear p hr r; intro p r hr
    have hr' : Tendsto (fun i => M * r i) atTop (𝓝[>] 0) := by
      convert! TendstoNhdsWithinIoi.const_mul hM hr <;> simp only [mul_zero]
    refine eventuallyLE_antisymm_iff.mpr ⟨?_, ?_⟩
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
        (Eventually.of_forall fun i => by rw [inv_mul_cancel_left₀ hM.ne' (r i)])
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
        (Eventually.of_forall fun i => le_refl _)
  let r' : Nat -> Real := fun i => if 0 < r i then r i else 1 / ((i : Real) + 1)
  have hr' : Tendsto r' atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun i => ?_⟩
    by_cases hi : 0 < r i
    · simp [r', hi]
    · simp only [r', hi, one_div, mem_Ioi, if_false, inv_pos]; positivity
  have h₀ : forall i, p i ∧ 0 < r i -> cthickening (r i) (s i) = cthickening (r' i) (s i) := by
    grind
  have h₁ : forall i, p i ∧ 0 < r i -> cthickening (M * r i) (s i) = cthickening (M * r' i) (s i) := by
    rintro i ⟨-, hi⟩; simp only [r', hi, if_true]
  have h₂ : forall i, p i ∧ r i <= 0 -> cthickening (M * r i) (s i) = cthickening (r i) (s i) := by
    rintro i ⟨-, hi⟩
    have hi' : M * r i <= 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi
    rw [cthickening_of_nonpos hi]; rw [cthickening_of_nonpos hi']
  have hp : p = fun i => p i ∧ 0 < r i ∨ p i ∧ r i <= 0 := by
    ext i; simp [← and_or_left, lt_or_ge 0 (r i)]
  rw [hp]; rw [blimsup_or_eq_sup]; rw [blimsup_or_eq_sup]
  simp only [sup_eq_union]
  rw [blimsup_congr (Eventually.of_forall h₀)]; rw [blimsup_congr (Eventually.of_forall h₁)]; rw [blimsup_congr (Eventually.of_forall h₂)]
  exact ae_eq_set_union (this (fun i => p i ∧ 0 < r i) hr') (ae_eq_refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `blimsup_cthickening_ae_eq_blimsup_thickening` / 定理 `blimsup_cthickening_ae_eq_blimsup_thickening`

English:
theorem blimsup_cthickening_ae_eq_blimsup_thickening
  statement: {p : Nat -> Prop} {s : Nat -> Set α} {r : Nat -> Real}
  proof: by
  refine eventuallyLE_antisymm_iff.mpr ⟨?_, LE.le.eventuallyLE ?_⟩
  · rw [eventuallyLE_congr (blimsup_cthickening_mul_ae_eq μ p s (one_half_pos (α := Real)) r hr).symm
      EventuallyEq.rfl]
    apply LE.le.eventuallyLE
    refine mono_blimsup' (hr'.mono fun i hi pi => cthickening_subset_thickening' (hi pi) ?_ (s i))
    nlinarith [hi pi]
  · exact mono_blimsup fun i _ => thickening_subset_cthickening _ _

中文:
定理 blimsup_cthickening_ae_eq_blimsup_thickening
  结论: {p : 自然数 -> 命题} {s : 自然数 -> 集合 α} {r : 自然数 -> 实数}
  证明: by
  refine eventuallyLE_antisymm_iff.mpr ⟨?_, LE.le.eventuallyLE ?_⟩
  · rw [eventuallyLE_congr (blimsup_cthickening_mul_ae_eq μ p s (one_half_pos (α := Real)) r hr).symm
      EventuallyEq.rfl]
    apply LE.le.eventuallyLE
    refine mono_blimsup' (hr'.mono fun i hi pi => cthickening_subset_thickening' (hi pi) ?_ (s i))
    nlinarith [hi pi]
  · exact mono_blimsup fun i _ => thickening_subset_cthickening _ _

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, LE.le.eventuallyLE, blimsup_cthickening_mul_ae_eq, cthickening_subset_thickening, eventuallyLE, eventuallyLE_antisymm_iff, eventuallyLE_antisymm_iff.mpr, eventuallyLE_congr, mono_blimsup, one_half_pos, thickening_subset_cthickening
-/
theorem blimsup_cthickening_ae_eq_blimsup_thickening {p : Nat -> Prop} {s : Nat -> Set α} {r : Nat -> Real}
    (hr : Tendsto r atTop (𝓝 0)) (hr' : forallᶠ i in atTop, p i -> 0 < r i) :
    (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  refine eventuallyLE_antisymm_iff.mpr ⟨?_, LE.le.eventuallyLE ?_⟩
  · rw [eventuallyLE_congr (blimsup_cthickening_mul_ae_eq μ p s (one_half_pos (α := Real)) r hr).symm
      EventuallyEq.rfl]
    apply LE.le.eventuallyLE
    refine mono_blimsup' (hr'.mono fun i hi pi => cthickening_subset_thickening' (hi pi) ?_ (s i))
    nlinarith [hi pi]
  · exact mono_blimsup fun i _ => thickening_subset_cthickening _ _

/--
theorem `blimsup_thickening_mul_ae_eq_aux` / 定理 `blimsup_thickening_mul_ae_eq_aux`

English:
theorem blimsup_thickening_mul_ae_eq_aux
  statement: (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M)
  proof: by
  have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr
  replace hr : Tendsto (fun i => M * r i) atTop (𝓝 0) := by convert! hr.const_mul M; simp
  replace hr' : forallᶠ i in atTop, p i -> 0 < M * r i := hr'.mono fun i hi hip => mul_pos hM (hi hip)
  have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  exact h₃.symm.trans (h₂.trans h₁)

中文:
定理 blimsup_thickening_mul_ae_eq_aux
  结论: (p : 自然数 -> 命题) (s : 自然数 -> 集合 α) {M : 实数} (hM : 0 < M)
  证明: by
  have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr
  replace hr : Tendsto (fun i => M * r i) atTop (𝓝 0) := by convert! hr.const_mul M; simp
  replace hr' : forallᶠ i in atTop, p i -> 0 < M * r i := hr'.mono fun i hi hip => mul_pos hM (hi hip)
  have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  exact h₃.symm.trans (h₂.trans h₁)

Depends on / 依赖: Tendsto, blimsup_cthickening_ae_eq_blimsup_thickening, blimsup_cthickening_mul_ae_eq, const_mul, convert, hr.const_mul, mul_pos, replace, symm.trans
-/
theorem blimsup_thickening_mul_ae_eq_aux (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M)
    (r : Nat -> Real) (hr : Tendsto r atTop (𝓝 0)) (hr' : forallᶠ i in atTop, p i -> 0 < r i) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr
  replace hr : Tendsto (fun i => M * r i) atTop (𝓝 0) := by convert! hr.const_mul M; simp
  replace hr' : forallᶠ i in atTop, p i -> 0 < M * r i := hr'.mono fun i hi hip => mul_pos hM (hi hip)
  have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  exact h₃.symm.trans (h₂.trans h₁)

/--
theorem `blimsup_thickening_mul_ae_eq` / 定理 `blimsup_thickening_mul_ae_eq`

English:
theorem blimsup_thickening_mul_ae_eq
  statement: (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M) (r : Nat -> Real)
  proof: by
  let q : Nat -> Prop := fun i => p i ∧ 0 < r i
  have hq {u : Nat -> Set α} (hu : forall i, u i != ∅ -> 0 < r i) :
      blimsup u atTop p = blimsup u atTop q :=
blimsup_congr' Eventually.of_forall fun i hi => by simp [q, hu i hi]
  rw [hq fun i hi => (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]; rw [hq fun i hi => (mul_pos_iff_of_pos_left hM).1
      (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]
  exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (Eventually.of_forall fun i hi => hi.2)

中文:
定理 blimsup_thickening_mul_ae_eq
  结论: (p : 自然数 -> 命题) (s : 自然数 -> 集合 α) {M : 实数} (hM : 0 < M) (r : 自然数 -> 实数)
  证明: by
  let q : Nat -> Prop := fun i => p i ∧ 0 < r i
  have hq {u : Nat -> Set α} (hu : forall i, u i != ∅ -> 0 < r i) :
      blimsup u atTop p = blimsup u atTop q :=
blimsup_congr' Eventually.of_forall fun i hi => by simp [q, hu i hi]
  rw [hq fun i hi => (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]; rw [hq fun i hi => (mul_pos_iff_of_pos_left hM).1
      (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]
  exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (Eventually.of_forall fun i hi => hi.2)

Depends on / 依赖: Eventually, Eventually.of_forall, blimsup, blimsup_congr, blimsup_thickening_mul_ae_eq_aux, mul_pos_iff_of_pos_left, nonempty_iff_ne_empty, of_forall, thickening_nonempty_iff
-/
theorem blimsup_thickening_mul_ae_eq (p : Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M) (r : Nat -> Real)
    (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  let q : Nat -> Prop := fun i => p i ∧ 0 < r i
  have hq {u : Nat -> Set α} (hu : forall i, u i != ∅ -> 0 < r i) :
      blimsup u atTop p = blimsup u atTop q :=
blimsup_congr' Eventually.of_forall fun i hi => by simp [q, hu i hi]
  rw [hq fun i hi => (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]; rw [hq fun i hi => (mul_pos_iff_of_pos_left hM).1
      (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]
  exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (Eventually.of_forall fun i hi => hi.2)
