/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.AdaptationNote

/-!
# Satellite configurations for Besicovitch covering lemma in vector spaces

The Besicovitch covering theorem ensures that, in a nice metric space, there exists a number `N`
such that, from any family of balls with bounded radii, one can extract `N` families, each made of
disjoint balls, covering together all the centers of the initial family.

A key tool in the proof of this theorem is the notion of a satellite configuration, i.e., a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This is a technical notion, but it shows
up naturally in the proof of the Besicovitch theorem (which goes through a greedy algorithm): to
ensure that in the end one needs at most `N` families of balls, the crucial property of the
underlying metric space is that there should be no satellite configuration of `N + 1` points.

This file is devoted to the study of this property in vector spaces: we prove the main result
of [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994],
which shows that the optimal such `N` in a vector space coincides with the maximal number
of points one can put inside the unit ball of radius `2` under the condition that their distances
are bounded below by `1`.
In particular, this number is bounded by `5 ^ dim` by a straightforward measure argument.

## Main definitions and results

* `multiplicity E` is the maximal number of points one can put inside the unit ball
  of radius `2` in the vector space `E`, under the condition that their distances
  are bounded below by `1`.
* `multiplicity_le E` shows that `multiplicity E ≤ 5 ^ (dim E)`.
* `good_τ E` is a constant `> 1`, but close enough to `1` that satellite configurations
  with this parameter `τ` are not worst than for `τ = 1`.
* `isEmpty_satelliteConfig_multiplicity` is the main theorem, saying that there are
  no satellite configurations of `(multiplicity E) + 1` points, for the parameter `goodτ E`.
-/

@[expose] public section


universe u

open Metric Set Module MeasureTheory Filter Fin

open scoped ENNReal Topology

noncomputable section

namespace Besicovitch

variable {E : Type*} [NormedAddCommGroup E]

namespace SatelliteConfig

variable [NormedSpace Real E] {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)

/--
Definition of `centerAndRescale` / `centerAndRescale` 的定义

English:
definition centerAndRescale
  signature: : SatelliteConfig E N τ where
  body: (a.r (last N))⁻¹ • (a.c i - a.c (last N))
  r i := (a.r (last N))⁻¹ * a.r i
  rpos i := by positivity
  h i j hij := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    rcases a.h hij with (⟨H₁, H₂⟩ | ⟨H₁, H₂⟩) <;> [left; right] <;> con

中文:
定义 centerAndRescale
  签名: : SatelliteConfig E N τ where
  定义体: (a.r (last N))⁻¹ • (a.c i - a.c (last N))
  r i := (a.r (last N))⁻¹ * a.r i
  rpos i := by positivity
  h i j hij := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    rcases a.h hij with (⟨H₁, H₂⟩ | ⟨H₁, H₂⟩) <;> [left; right] <;> con
-/
def centerAndRescale : SatelliteConfig E N τ where
  c i := (a.r (last N))⁻¹ • (a.c i - a.c (last N))
  r i := (a.r (last N))⁻¹ * a.r i
  rpos i := by positivity
  h i j hij := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    rcases a.h hij with (⟨H₁, H₂⟩ | ⟨H₁, H₂⟩) <;> [left; right] <;> constructor <;> gcongr
  hlast i hi := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    have ⟨H₁, H₂⟩ := a.hlast i hi
    constructor <;> gcongr
  inter i hi := by
    simp (disch := positivity) only [dist_smul₀, ← mul_add, dist_sub_right, Real.norm_of_nonneg]
    gcongr
    exact a.inter i hi

/--
theorem `centerAndRescale_center` / 定理 `centerAndRescale_center`

English:
theorem centerAndRescale_center
  statement: a.centerAndRescale.c (last N) = 0
  proof: by
  simp [SatelliteConfig.centerAndRescale]

中文:
定理 centerAndRescale_center
  结论: a.centerAndRescale.c (last N) = 0
  证明: by
  simp [SatelliteConfig.centerAndRescale]

Depends on / 依赖: SatelliteConfig, SatelliteConfig.centerAndRescale, centerAndRescale
-/
theorem centerAndRescale_center : a.centerAndRescale.c (last N) = 0 := by
  simp [SatelliteConfig.centerAndRescale]

/--
theorem `centerAndRescale_radius` / 定理 `centerAndRescale_radius`

English:
theorem centerAndRescale_radius
  given: {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
  proof: by
  simp [SatelliteConfig.centerAndRescale, inv_mul_cancel₀ (a.rpos _).ne']

中文:
定理 centerAndRescale_radius
  条件: {N : 自然数} {τ : 实数} (a : SatelliteConfig E N τ)
  证明: by
  simp [SatelliteConfig.centerAndRescale, inv_mul_cancel₀ (a.rpos _).ne']

Depends on / 依赖: SatelliteConfig, SatelliteConfig.centerAndRescale, a.rpos, centerAndRescale
-/
theorem centerAndRescale_radius {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) :
    a.centerAndRescale.r (last N) = 1 := by
  simp [SatelliteConfig.centerAndRescale, inv_mul_cancel₀ (a.rpos _).ne']

end SatelliteConfig

/-! ### Disjoint balls of radius close to `1` in the radius `2` ball. -/


/--
Definition of `multiplicity` / `multiplicity` 的定义

English:
definition multiplicity
  signature: (E : Type*) [NormedAddCommGroup E]
  body: sSup {N | exists s : Finset E, s.card = N ∧ (forall c in s, ‖c‖ <= 2) ∧ forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖}

中文:
定义 multiplicity
  签名: (E : 类型) [赋范交换加群 E]
  定义体: sSup {N | exists s : Finset E, s.card = N ∧ (forall c in s, ‖c‖ <= 2) ∧ forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖}

Depends on / 依赖: Finset, s.card
-/
def multiplicity (E : Type*) [NormedAddCommGroup E] :=
  sSup {N | exists s : Finset E, s.card = N ∧ (forall c in s, ‖c‖ <= 2) ∧ forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖}

section

variable [NormedSpace Real E] [FiniteDimensional Real E]

open scoped Function in -- required for scoped `on` notation
/--
theorem `card_le_of_separated` / 定理 `card_le_of_separated`

English:
theorem card_le_of_separated
  statement: (s : Finset E) (hs : forall c in s, ‖c‖ <= 2)
  proof: by
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
    contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
    i.e., `s.card ≤ 5^dim`. -/
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : Real := (1 

中文:
定理 card_le_of_separated
  结论: (s : 有限集 E) (hs : 对任意 c in s, ‖c‖ <= 2)
  证明: by
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
    contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
    i.e., `s.card ≤ 5^dim`. -/
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : Real := (1 
-/
theorem card_le_of_separated (s : Finset E) (hs : forall c in s, ‖c‖ <= 2)
    (h : forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖) : s.card <= 5 ^ finrank Real E := by
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
    contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
    i.e., `s.card ≤ 5^dim`. -/
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : Real := (1 : Real) / 2
  let ρ : Real := (5 : Real) / 2
  have ρpos : 0 < ρ := by norm_num
  set A := ⋃ c in s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert! h c hc d hd hcd
    norm_num
  have A_subset : A subseteq ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 <= δ + 2 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = 5 / 2 := by norm_num
  have I :
    (s.card : Real>=0∞) * ENNReal.ofReal (δ ^ finrank Real E) * μ (ball 0 1) <=
      ENNReal.ofReal (ρ ^ finrank Real E) * μ (ball 0 1) :=
    calc
      (s.card : Real>=0∞) * ENNReal.ofReal (δ ^ finrank Real E) * μ (ball 0 1) = μ A := by
        rw [hA]; rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
        have I : 0 < δ := by norm_num
        simp only [μ.addHaar_ball_of_pos _ I]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ <= μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ finrank Real E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : Real>=0∞) * ENNReal.ofReal (δ ^ finrank Real E) <= ENNReal.ofReal (ρ ^ finrank Real E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : Real) <= (5 : Real) ^ finrank Real E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using this
  exact mod_cast K

/--
theorem `multiplicity_le` / 定理 `multiplicity_le`

English:
theorem multiplicity_le
  statement: multiplicity E <= 5 ^ finrank Real E
  proof: by
  apply csSup_le
  · refine ⟨0, ⟨∅, by simp⟩⟩
  · rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2

中文:
定理 multiplicity_le
  结论: multiplicity E <= 5 ^ finrank 实数 E
  证明: by
  apply csSup_le
  · refine ⟨0, ⟨∅, by simp⟩⟩
  · rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2

Depends on / 依赖: Besicovitch, Besicovitch.card_le_of_separated, card_le_of_separated, csSup_le
-/
theorem multiplicity_le : multiplicity E <= 5 ^ finrank Real E := by
  apply csSup_le
  · refine ⟨0, ⟨∅, by simp⟩⟩
  · rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2

/--
theorem `card_le_multiplicity` / 定理 `card_le_multiplicity`

English:
theorem card_le_multiplicity
  statement: {s : Finset E} (hs : forall c in s, ‖c‖ <= 2)
  proof: by
  apply le_csSup
  · refine ⟨5 ^ finrank Real E, ?_⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
  · simp only [mem_ofPred_eq, Ne]
    exact ⟨s, rfl, hs, h's⟩

中文:
定理 card_le_multiplicity
  结论: {s : 有限集 E} (hs : 对任意 c in s, ‖c‖ <= 2)
  证明: by
  apply le_csSup
  · refine ⟨5 ^ finrank Real E, ?_⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
  · simp only [mem_ofPred_eq, Ne]
    exact ⟨s, rfl, hs, h's⟩

Depends on / 依赖: Besicovitch, Besicovitch.card_le_of_separated, card_le_of_separated, finrank, le_csSup, mem_ofPred_eq
-/
theorem card_le_multiplicity {s : Finset E} (hs : forall c in s, ‖c‖ <= 2)
    (h's : forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖) : s.card <= multiplicity E := by
  apply le_csSup
  · refine ⟨5 ^ finrank Real E, ?_⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
  · simp only [mem_ofPred_eq, Ne]
    exact ⟨s, rfl, hs, h's⟩

variable (E)

/--
theorem `exists_goodδ` / 定理 `exists_goodδ`

English:
theorem exists_goodδ
  proof: by
  classical
  /- This follows from a compactness argument: otherwise, one could extract a converging
    subsequence, to obtain a `1`-separated set in the ball of radius `2` with cardinality
    `N = multiplicity E + 1`. To formalize this, we work with functions `Fin N → E`.
     -/
  by_contra! 

中文:
定理 存在_goodδ
  证明: by
  classical
  /- This follows from a compactness argument: otherwise, one could extract a converging
    subsequence, to obtain a `1`-separated set in the ball of radius `2` with cardinality
    `N = multiplicity E + 1`. To formalize this, we work with functions `Fin N → E`.
     -/
  by_contra! 

Depends on / 依赖: classical
-/
theorem exists_goodδ :
    exists δ : Real, 0 < δ ∧ δ < 1 ∧ forall s : Finset E, (forall c in s, ‖c‖ <= 2) ->
      (forall c in s, forall d in s, c != d -> 1 - δ <= ‖c - d‖) -> s.card <= multiplicity E := by
  classical
  /- This follows from a compactness argument: otherwise, one could extract a converging
    subsequence, to obtain a `1`-separated set in the ball of radius `2` with cardinality
    `N = multiplicity E + 1`. To formalize this, we work with functions `Fin N → E`.
     -/
  by_contra! h
  set N := multiplicity E + 1 with hN
  have :
    forall δ : Real, 0 < δ -> exists f : Fin N -> E, (forall i : Fin N, ‖f i‖ <= 2) ∧
      Pairwise fun i j => 1 - δ <= ‖f i - f j‖ := by
    intro δ hδ
    rcases lt_or_ge δ 1 with (hδ' | hδ')
    · rcases h δ hδ hδ' with ⟨s, hs, h's, s_card⟩
      obtain ⟨f, f_inj, hfs⟩ : exists f : Fin N -> E, Function.Injective f ∧ range f subseteq ↑s := by
        have : Fintype.card (Fin N) <= s.card := by simp only [Fintype.card_fin]; exact s_card
        rcases Function.Embedding.exists_of_card_le_finset this with ⟨f, hf⟩
        exact ⟨f, f.injective, hf⟩
      simp only [range_subset_iff, Finset.mem_coe] at hfs
      exact ⟨f, fun i => hs _ (hfs i), fun i j hij => h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩
    · exact
        ⟨fun _ => 0, by simp, fun i j _ => by
          simpa only [norm_zero, sub_nonpos, sub_self]⟩
  -- For `δ > 0`, `F δ` is a function from `Fin N` to the ball of radius `2` for which two points
  -- in the image are separated by `1 - δ`.
  choose! F hF using this
  -- Choose a converging subsequence when `δ → 0`.
  have : exists f : Fin N -> E, (forall i : Fin N, ‖f i‖ <= 2) ∧ Pairwise fun i j => 1 <= ‖f i - f j‖ := by
    obtain ⟨u, _, zero_lt_u, hu⟩ :
      exists u : Nat -> Real,
        (forall m n : Nat, m < n -> u n < u m) ∧ (forall n : Nat, 0 < u n) ∧ Filter.Tendsto u Filter.atTop (𝓝 0) :=
      exists_seq_strictAnti_tendsto (0 : Real)
    have A : forall n, F (u n) in closedBall (0 : Fin N -> E) 2 := by
      intro n
      simp only [pi_norm_le_iff_of_nonneg zero_le_two, mem_closedBall, dist_zero_right,
        (hF (u n) (zero_lt_u n)).left, forall_const]
    obtain ⟨f, fmem, φ, φ_mono, hf⟩ :
      exists f in closedBall (0 : Fin N -> E) 2,
        exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto ((F ∘ u) ∘ φ) atTop (𝓝 f) :=
      IsCompact.tendsto_subseq (isCompact_closedBall _ _) A
    refine ⟨f, fun i => ?_, fun i j hij => ?_⟩
    · simp only [pi_norm_le_iff_of_nonneg zero_le_two, mem_closedBall, dist_zero_right] at fmem
      exact fmem i
    · have A : Tendsto (fun n => ‖F (u (φ n)) i - F (u (φ n)) j‖) atTop (𝓝 ‖f i - f j‖) :=
        ((hf.apply_nhds i).sub (hf.apply_nhds j)).norm
      have B : Tendsto (fun n => 1 - u (φ n)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_atTop)
      rw [sub_zero] at B
      exact le_of_tendsto_of_tendsto' B A fun n => (hF (u (φ n)) (zero_lt_u _)).2 hij
  rcases this with ⟨f, hf, h'f⟩
  -- the range of `f` contradicts the definition of `multiplicity E`.
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 <= ‖f i - f j‖ := h'f h
    simp only [hij, norm_zero, sub_self] at this
    exact lt_irrefl _ (this.trans_lt zero_lt_one)
  let s := Finset.image f Finset.univ
  have s_card : s.card = N := by rw [Finset.card_image_of_injective _ finj]; exact Finset.card_fin N
  have hs : forall c in s, ‖c‖ <= 2 := by
    simp only [s, hf, forall_apply_eq_imp_iff, forall_const, forall_exists_index, Finset.mem_univ,
      Finset.mem_image, true_and]
  have h's : forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖ := by
    simp only [s, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      Ne, forall_apply_eq_imp_iff, true_and]
    intro i j hij
    have : i != j := fun h => by rw [h] at hij; exact hij rfl
    exact h'f this
  have : s.card <= multiplicity E := card_le_multiplicity hs h's
  rw [s_card]; rw [hN] at this
  exact lt_irrefl _ ((Nat.lt_succ_self (multiplicity E)).trans_le this)

/--
Definition of `goodδ` / `goodδ` 的定义

English:
definition goodδ
  signature: : Real
  body: (exists_goodδ E).choose

中文:
定义 goodδ
  签名: : 实数
  定义体: (exists_goodδ E).choose
-/
def goodδ : Real :=
  (exists_goodδ E).choose

/--
theorem `goodδ_lt_one` / 定理 `goodδ_lt_one`

English:
theorem goodδ_lt_one
  statement: goodδ E < 1
  proof: (exists_goodδ E).choose_spec.2.1

中文:
定理 goodδ_lt_one
  结论: goodδ E < 1
  证明: (exists_goodδ E).choose_spec.2.1

Depends on / 依赖: choose_spec
-/
theorem goodδ_lt_one : goodδ E < 1 :=
  (exists_goodδ E).choose_spec.2.1

/--
Definition of `goodτ` / `goodτ` 的定义

English:
definition goodτ
  signature: : Real
  body: 1 + goodδ E / 4

中文:
定义 goodτ
  签名: : 实数
  定义体: 1 + goodδ E / 4
-/
def goodτ : Real :=
  1 + goodδ E / 4

/--
theorem `one_lt_goodτ` / 定理 `one_lt_goodτ`

English:
theorem one_lt_goodτ
  statement: 1 < goodτ E
  proof: by
  dsimp [goodτ, goodδ]; linarith [(exists_goodδ E).choose_spec.1]

中文:
定理 one_lt_goodτ
  结论: 1 < goodτ E
  证明: by
  dsimp [goodτ, goodδ]; linarith [(exists_goodδ E).choose_spec.1]

Depends on / 依赖: choose_spec
-/
theorem one_lt_goodτ : 1 < goodτ E := by
  dsimp [goodτ, goodδ]; linarith [(exists_goodδ E).choose_spec.1]

variable {E}

/--
theorem `card_le_multiplicity_of_δ` / 定理 `card_le_multiplicity_of_δ`

English:
theorem card_le_multiplicity_of_δ
  statement: {s : Finset E} (hs : forall c in s, ‖c‖ <= 2)
  proof: (Classical.choose_spec (exists_goodδ E)).2.2 s hs h's

中文:
定理 card_le_multiplicity_of_δ
  结论: {s : 有限集 E} (hs : 对任意 c in s, ‖c‖ <= 2)
  证明: (Classical.choose_spec (exists_goodδ E)).2.2 s hs h's

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem card_le_multiplicity_of_δ {s : Finset E} (hs : forall c in s, ‖c‖ <= 2)
    (h's : forall c in s, forall d in s, c != d -> 1 - goodδ E <= ‖c - d‖) : s.card <= multiplicity E :=
  (Classical.choose_spec (exists_goodδ E)).2.2 s hs h's

/--
theorem `le_multiplicity_of_δ_of_fin` / 定理 `le_multiplicity_of_δ_of_fin`

English:
theorem le_multiplicity_of_δ_of_fin
  statement: {n : Nat} (f : Fin n -> E) (h : forall i, ‖f i‖ <= 2)
  proof: by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 - goodδ E <= ‖f i - f j‖ := h' h
    simp only [hij, norm_zero, sub_self] at this
    linarith [goodδ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by rw [Finset.car

中文:
定理 le_multiplicity_of_δ_of_fin
  结论: {n : 自然数} (f : 有限集 n -> E) (h : 对任意 i, ‖f i‖ <= 2)
  证明: by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 - goodδ E <= ‖f i - f j‖ := h' h
    simp only [hij, norm_zero, sub_self] at this
    linarith [goodδ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by rw [Finset.car

Depends on / 依赖: Finset, Finset.card_fin, Finset.card_image_of_injective, Finset.image, Finset.mem_image, Finset.mem_univ, Finset.univ, Function, Function.Injective, Injective, card_fin, card_image_of_injective, classical, forall_apply_eq_imp_iff, forall_exists_index, imp_true_iff, mem_image, mem_univ, norm_zero, s.card
-/
theorem le_multiplicity_of_δ_of_fin {n : Nat} (f : Fin n -> E) (h : forall i, ‖f i‖ <= 2)
    (h' : Pairwise fun i j => 1 - goodδ E <= ‖f i - f j‖) : n <= multiplicity E := by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 - goodδ E <= ‖f i - f j‖ := h' h
    simp only [hij, norm_zero, sub_self] at this
    linarith [goodδ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by rw [Finset.card_image_of_injective _ finj]; exact Finset.card_fin n
  have hs : forall c in s, ‖c‖ <= 2 := by
    simp only [s, h, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ,
      Finset.mem_image, imp_true_iff, true_and]
  have h's : forall c in s, forall d in s, c != d -> 1 - goodδ E <= ‖c - d‖ := by
    simp only [s, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      Ne, forall_apply_eq_imp_iff, true_and]
    intro i j hij
    have : i != j := fun h => by rw [h] at hij; exact hij rfl
    exact h' this
  have : s.card <= multiplicity E := card_le_multiplicity_of_δ hs h's
  rwa [s_card] at this

end

namespace SatelliteConfig



/--
theorem `exists_normalized_aux1` / 定理 `exists_normalized_aux1`

English:
theorem exists_normalized_aux1
  statement: {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
  proof: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  hav

中文:
定理 存在_normalized_aux1
  结论: {N : 自然数} {τ : 实数} (a : SatelliteConfig E N τ)
  证明: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  hav

Depends on / 依赖: Pairwise, _root_, _root_.zero_lt_one.trans_le, dist_eq_norm, sq_nonneg, trans_le, zero_lt_one
-/
theorem exists_normalized_aux1 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
    (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + δ / 4) (hδ2 : δ <= 1)
    (i j : Fin N.succ) (inej : i != j) : 1 - δ <= ‖a.c i - a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have I : (1 - δ / 4) * τ <= 1 :=
    calc
      (1 - δ / 4) * τ <= (1 - δ / 4) * (1 + δ / 4) := by gcongr
      _ = (1 : Real) - δ ^ 2 / 16 := by ring
      _ <= 1 := by linarith only [sq_nonneg δ]
  have J : 1 - δ <= 1 - δ / 4 := by linarith only [δnonneg]
  have K : 1 - δ / 4 <= τ⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ τpos]; exact I
  suffices L : τ⁻¹ <= ‖a.c i - a.c j‖ by linarith only [J, K, L]
  have hτ' : forall k, τ⁻¹ <= a.r k := by
    intro k
    rw [inv_eq_one_div]; rw [div_le_iff₀ τpos]; rw [← lastr]; rw [mul_comm]
    exact a.hlast' k hτ
  rcases ah inej with (H | H)
  · apply le_trans _ H.1
    exact hτ' i
  · rw [norm_sub_rev]
    apply le_trans _ H.1
    exact hτ' j

variable [NormedSpace Real E]

/--
theorem `exists_normalized_aux2` / 定理 `exists_normalized_aux2`

English:
theorem exists_normalized_aux2
  statement: {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
  proof: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  hav

中文:
定理 存在_normalized_aux2
  结论: {N : 自然数} {τ : 实数} (a : SatelliteConfig E N τ)
  证明: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  hav

Depends on / 依赖: Pairwise, a.hlast, a.inter, dist_eq_norm, dist_zero_right, lt_or_ge
-/
theorem exists_normalized_aux2 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
    (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + δ / 4)
    (hδ2 : δ <= 1) (i j : Fin N.succ) (inej : i != j) (hi : ‖a.c i‖ <= 2) (hj : 2 < ‖a.c j‖) :
    1 - δ <= ‖a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have D : 0 <= 1 - δ / 4 := by linarith only [hδ2]
  have hcrj : ‖a.c j‖ <= a.r j + 1 := by simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have I : a.r i <= 2 := by
    rcases lt_or_ge i (last N) with (H | H)
    · apply (a.hlast i H).1.trans
      simpa only [dist_eq_norm, lastc, sub_zero] using hi
    · have : i = last N := top_le_iff.1 H
      rw [this]; rw [lastr]
      exact one_le_two
  have J : (1 - δ / 4) * τ <= 1 :=
    calc
      (1 - δ / 4) * τ <= (1 - δ / 4) * (1 + δ / 4) := by gcongr
      _ = (1 : Real) - δ ^ 2 / 16 := by ring
      _ <= 1 := by linarith only [sq_nonneg δ]
  have A : a.r j - δ <= ‖a.c i - a.c j‖ := by
    rcases ah inej.symm with (H | H); · rw [norm_sub_rev]; linarith [H.1]
    have C : a.r j <= 4 :=
      calc
        a.r j <= τ * a.r i := H.2
        _ <= τ * 2 := by gcongr
        _ <= 5 / 4 * 2 := by gcongr; linarith only [hδ1, hδ2]
        _ <= 4 := by norm_num
    calc
      a.r j - δ <= a.r j - a.r j / 4 * δ := by
        gcongr _ - ?_
        exact mul_le_of_le_one_left δnonneg (by linarith only [C])
      _ = (1 - δ / 4) * a.r j := by ring
      _ <= (1 - δ / 4) * (τ * a.r i) := by gcongr; exact H.2
      _ <= 1 * a.r i := by rw [← mul_assoc]; gcongr
      _ <= ‖a.c i - a.c j‖ := by rw [one_mul]; exact H.1
  set d := (2 / ‖a.c j‖) • a.c j with hd
  have : a.r j - δ <= ‖a.c i - d‖ + (a.r j - 1) :=
    calc
      a.r j - δ <= ‖a.c i - a.c j‖ := A
      _ <= ‖a.c i - d‖ + ‖d - a.c j‖ := by simp only [← dist_eq_norm, dist_triangle]
      _ <= ‖a.c i - d‖ + (a.r j - 1) := by
        gcongr
        have A : 0 <= 1 - 2 / ‖a.c j‖ := by simpa [div_le_iff₀ (zero_le_two.trans_lt hj)] using hj.le
        rw [← one_smul Real (a.c j)]; rw [hd]; rw [← sub_smul]; rw [norm_smul]; rw [norm_sub_rev]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg A]; rw [sub_mul]
        field_simp
        linarith only [hcrj]
  linarith only [this]

/--
theorem `exists_normalized_aux3` / 定理 `exists_normalized_aux3`

English:
theorem exists_normalized_aux3
  statement: {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
  proof: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have hcrj : ‖a.c j‖ <= a.r j + 1 := by simpa only [last

中文:
定理 存在_normalized_aux3
  结论: {N : 自然数} {τ : 实数} (a : SatelliteConfig E N τ)
  证明: by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have hcrj : ‖a.c j‖ <= a.r j + 1 := by simpa only [last

Depends on / 依赖: Pairwise, a.inter, dist_eq_norm, dist_zero_right, lt_irrefl, lt_top_iff_ne_top, norm_zero
-/
theorem exists_normalized_aux3 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ)
    (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + δ / 4)
    (i j : Fin N.succ) (inej : i != j) (hi : 2 < ‖a.c i‖) (hij : ‖a.c i‖ <= ‖a.c j‖) :
    1 - δ <= ‖(2 / ‖a.c i‖) • a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i <= ‖a.c i - a.c j‖ ∧ a.r j <= τ * a.r i ∨
        a.r j <= ‖a.c j - a.c i‖ ∧ a.r i <= τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 <= δ := by linarith only [hτ, hδ1]
  have hcrj : ‖a.c j‖ <= a.r j + 1 := by simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have A : a.r i <= ‖a.c i‖ := by
    have : i < last N := by
      apply lt_top_iff_ne_top.2
      intro iN
      change i = last N at iN
      rw [iN]; rw [lastc]; rw [norm_zero] at hi
      exact lt_irrefl _ (zero_le_two.trans_lt hi)
    convert! (a.hlast i this).1 using 1
    rw [dist_eq_norm]; rw [lastc]; rw [sub_zero]
  have hj : 2 < ‖a.c j‖ := hi.trans_le hij
  set s := ‖a.c i‖
  have spos : 0 < s := zero_lt_two.trans hi
  set d := (s / ‖a.c j‖) • a.c j with hd
  have I : ‖a.c j - a.c i‖ <= ‖a.c j‖ - s + ‖d - a.c i‖ :=
    calc
      ‖a.c j - a.c i‖ <= ‖a.c j - d‖ + ‖d - a.c i‖ := by simp [← dist_eq_norm, dist_triangle]
      _ = ‖a.c j‖ - ‖a.c i‖ + ‖d - a.c i‖ := by
        nth_rw 1 [← one_smul Real (a.c j)]
        rw [add_left_inj]; rw [hd]; rw [← sub_smul]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg]; rw [sub_mul]; rw [one_mul]; rw [div_mul_cancel₀ _ (zero_le_two.trans_lt hj).ne']
        rwa [sub_nonneg, div_le_iff₀ (zero_lt_two.trans hj), one_mul]
  have J : a.r j - ‖a.c j - a.c i‖ <= s / 2 * δ :=
    calc
      a.r j - ‖a.c j - a.c i‖ <= s * (τ - 1) := by
        rcases ah inej.symm with (H | H)
        · calc
            a.r j - ‖a.c j - a.c i‖ <= 0 := sub_nonpos.2 H.1
            _ <= s * (τ - 1) := mul_nonneg spos.le (sub_nonneg.2 hτ)
        · rw [norm_sub_rev] at H
          calc
            a.r j - ‖a.c j - a.c i‖ <= τ * a.r i - a.r i := sub_le_sub H.2 H.1
            _ = a.r i * (τ - 1) := by ring
            _ <= s * (τ - 1) := by gcongr
      _ <= s * (δ / 2) := by gcongr; linarith only [δnonneg, hδ1]
      _ = s / 2 * δ := by ring
  have invs_nonneg : 0 <= 2 / s := div_nonneg zero_le_two (zero_le_two.trans hi.le)
  calc
    1 - δ = 2 / s * (s / 2 - s / 2 * δ) := by field
    _ <= 2 / s * ‖d - a.c i‖ := by
      gcongr; linarith only [hcrj, I, J, hi]
    _ = ‖(2 / s) • a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
      conv_lhs => rw [norm_sub_rev, ← abs_of_nonneg invs_nonneg]
      rw [← Real.norm_eq_abs]; rw [← norm_smul]; rw [smul_sub]; rw [hd]; rw [smul_smul]
      congr 3
      field

/--
theorem `exists_normalized` / 定理 `exists_normalized`

English:
theorem exists_normalized
  statement: {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
  proof: by
  let c' : Fin N.succ -> E := fun i => if ‖a.c i‖ <= 2 then a.c i else (2 / ‖a.c i‖) • a.c i
  have norm_c'_le : forall i, ‖c' i‖ <= 2 := by
    intro i
    simp only [c']
    split_ifs with h; · exact h
    by_cases hi : ‖a.c i‖ = 0 <;> simp [norm_smul, hi]
  refine ⟨c', fun n => norm_c'_le n, f

中文:
定理 存在_normalized
  结论: {N : 自然数} {τ : 实数} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
  证明: by
  let c' : Fin N.succ -> E := fun i => if ‖a.c i‖ <= 2 then a.c i else (2 / ‖a.c i‖) • a.c i
  have norm_c'_le : forall i, ‖c' i‖ <= 2 := by
    intro i
    simp only [c']
    split_ifs with h; · exact h
    by_cases hi : ‖a.c i‖ = 0 <;> simp [norm_smul, hi]
  refine ⟨c', fun n => norm_c'_le n, f

Depends on / 依赖: N.succ, norm_c, norm_smul, split_ifs
-/
theorem exists_normalized {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + δ / 4) (hδ2 : δ <= 1) :
    exists c' : Fin N.succ -> E, (forall n, ‖c' n‖ <= 2) ∧ Pairwise fun i j => 1 - δ <= ‖c' i - c' j‖ := by
  let c' : Fin N.succ -> E := fun i => if ‖a.c i‖ <= 2 then a.c i else (2 / ‖a.c i‖) • a.c i
  have norm_c'_le : forall i, ‖c' i‖ <= 2 := by
    intro i
    simp only [c']
    split_ifs with h; · exact h
    by_cases hi : ‖a.c i‖ = 0 <;> simp [norm_smul, hi]
  refine ⟨c', fun n => norm_c'_le n, fun i j inej => ?_⟩
  -- up to exchanging `i` and `j`, one can assume `‖c i‖ ≤ ‖c j‖`.
  wlog hij : ‖a.c i‖ <= ‖a.c j‖ generalizing i j
  · rw [norm_sub_rev]; exact this j i inej.symm (le_of_not_ge hij)
  rcases le_or_gt ‖a.c j‖ 2 with (Hj | Hj)
  -- case `‖c j‖ ≤ 2` (and therefore also `‖c i‖ ≤ 2`)
  · simp_rw [c', Hj, hij.trans Hj, if_true]
    exact exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej
  -- case `2 < ‖c j‖`
  · have H'j : ‖a.c j‖ <= 2 ↔ False := by simpa only [not_le, iff_false] using Hj
    rcases le_or_gt ‖a.c i‖ 2 with (Hi | Hi)
    · -- case `‖c i‖ ≤ 2`
      simp_rw [c', Hi, if_true, H'j, if_false]
      exact exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj
    · -- case `2 < ‖c i‖`
      have H'i : ‖a.c i‖ <= 2 ↔ False := by simpa only [not_le, iff_false] using Hi
      simp_rw [c', H'i, if_false, H'j, if_false]
      exact exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij

end SatelliteConfig

variable (E)
variable [NormedSpace Real E] [FiniteDimensional Real E]

/--
theorem `isEmpty_satelliteConfig_multiplicity` / 定理 `isEmpty_satelliteConfig_multiplicity`

English:
theorem isEmpty_satelliteConfig_multiplicity
  proof: ⟨by
    intro a
    let b := a.centerAndRescale
    rcases b.exists_normalized a.centerAndRescale_center a.centerAndRescale_radius
        (one_lt_goodτ E).le (goodδ E) le_rfl (goodδ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact
      lt_irrefl _ ((Nat.lt_succ_self _).trans_le (le_multiplic

中文:
定理 isEmpty_satelliteConfig_multiplicity
  证明: ⟨by
    intro a
    let b := a.centerAndRescale
    rcases b.exists_normalized a.centerAndRescale_center a.centerAndRescale_radius
        (one_lt_goodτ E).le (goodδ E) le_rfl (goodδ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact
      lt_irrefl _ ((Nat.lt_succ_self _).trans_le (le_multiplic

Depends on / 依赖: Nat.lt_succ_self, _le_two, a.centerAndRescale, a.centerAndRescale_center, a.centerAndRescale_radius, b.exists_normalized, centerAndRescale, centerAndRescale_center, centerAndRescale_radius, exists_normalized, le_rfl, lt_irrefl, lt_succ_self, trans_le
-/
theorem isEmpty_satelliteConfig_multiplicity :
    IsEmpty (SatelliteConfig E (multiplicity E) (goodτ E)) :=
  ⟨by
    intro a
    let b := a.centerAndRescale
    rcases b.exists_normalized a.centerAndRescale_center a.centerAndRescale_radius
        (one_lt_goodτ E).le (goodδ E) le_rfl (goodδ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact
      lt_irrefl _ ((Nat.lt_succ_self _).trans_le (le_multiplicity_of_δ_of_fin c' c'_le_two hc'))⟩

instance (priority := 100) instHasBesicovitchCovering : HasBesicovitchCovering E :=
  ⟨⟨multiplicity E, goodτ E, one_lt_goodτ E, isEmpty_satelliteConfig_multiplicity E⟩⟩

end Besicovitch
