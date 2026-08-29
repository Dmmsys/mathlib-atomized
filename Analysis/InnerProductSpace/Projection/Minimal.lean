/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Existence of minimizers (Hilbert projection theorem)

This file shows the existence of minimizers (also known as the Hilbert projection theorem).
This is the key tool that is used to define `Submodule.orthogonalProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs Real _ _

open Topology RCLike Real Filter InnerProductSpace

/--
theorem `exists_norm_eq_iInf_of_complete_convex` / 定理 `exists_norm_eq_iInf_of_complete_convex`

English:
theorem exists_norm_eq_iInf_of_complete_convex
  statement: {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
  proof: fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  let : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 <= δ := le_ciInf fun _ => norm_nonneg _
  have δ_le : forall w : K, δ <= ‖u - w‖ := ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have δ_le' : forall w in K, δ <= ‖u - w‖ := fun w hw => δ

中文:
定理 exists_norm_eq_iInf_of_complete_convex
  结论: {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
  证明: fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  let : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 <= δ := le_ciInf fun _ => norm_nonneg _
  have δ_le : forall w : K, δ <= ‖u - w‖ := ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have δ_le' : forall w in K, δ <= ‖u - w‖ := fun w hw => δ

Depends on / 依赖: Nonempty, Set.forall_mem_range, ciInf_le, forall_mem_range, le_ciInf, ne.to_subtype, norm_nonneg, to_subtype
-/
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex Real K) : forall u : F, exists v in K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  let : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 <= δ := le_ciInf fun _ => norm_nonneg _
  have δ_le : forall w : K, δ <= ‖u - w‖ := ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have δ_le' : forall w in K, δ <= ‖u - w‖ := fun w hw => δ_le ⟨w, hw⟩
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `‖u - w n‖ < δ + 1 / (n + 1)` (which implies `‖u - w n‖ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : exists w : Nat -> K, forall n, ‖u - w n‖ < δ + 1 / (n + 1) := by
    have hδ : forall n : Nat, δ < δ + 1 / (n + 1) := fun n =>
      lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat
    have h := fun n => exists_lt_of_ciInf_lt (hδ n)
    let w : Nat -> K := fun n => Classical.choose (h n)
    exact ⟨w, fun n => Classical.choose_spec (h n)⟩
  rcases exists_seq with ⟨w, hw⟩
  have norm_tendsto : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 δ) := by
    have h : Tendsto (fun _ : Nat => δ) atTop (𝓝 δ) := tendsto_const_nhds
    have h' : Tendsto (fun n : Nat => δ + 1 / (n + 1)) atTop (𝓝 δ) := by
      convert! h.add tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [add_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (fun x => δ_le _) fun x => le_of_lt (hw _)
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : CauchySeq fun n => (w n : F) := by
    rw [cauchySeq_iff_le_tendsto_0]
    -- splits into three goals
    let b := fun n : Nat => 8 * δ * (1 / (n + 1)) + 4 * (1 / (n + 1)) * (1 / (n + 1))
    use fun n => √(b n)
    constructor
    -- first goal : `∀ (n : ℕ), 0 ≤ √(b n)`
    · intro n
      exact sqrt_nonneg _
    constructor
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ √(b N)`
    · intro p q N hp hq
      let wp := (w p : F)
      let wq := (w q : F)
      let a := u - wq
      let b := u - wp
      let half := 1 / (2 : Real)
      let div := 1 / ((N : Real) + 1)
      have :
        4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
          2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) :=
        calc
          4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
              2 * ‖u - half • (wq + wp)‖ * (2 * ‖u - half • (wq + wp)‖) +
              ‖wp - wq‖ * ‖wp - wq‖ := by
            ring
          _ =
              absR 2 * ‖u - half • (wq + wp)‖ * (absR 2 * ‖u - half • (wq + wp)‖) +
                ‖wp - wq‖ * ‖wp - wq‖ := by
            rw [abs_of_nonneg]
            exact zero_le_two
          _ =
              ‖(2 : Real) • (u - half • (wq + wp))‖ * ‖(2 : Real) • (u - half • (wq + wp))‖ +
                ‖wp - wq‖ * ‖wp - wq‖ := by simp [norm_smul]
          _ = ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ := by
            rw [smul_sub]; rw [smul_smul]; rw [mul_one_div_cancel (_root_.two_ne_zero : (2 : Real) != 0)]; rw [←
              one_add_one_eq_two]; rw [add_smul]
            simp only [one_smul]
            have eq₁ : wp - wq = a - b := (sub_sub_sub_cancel_left _ _ _).symm
            have eq₂ : u + u - (wq + wp) = a + b := by
              change u + u - (wq + wp) = u - wq + (u - wp)
              abel
            rw [eq₁]; rw [eq₂]
          _ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) := parallelogram_law_with_norm_mul Real _ _
      have eq : δ <= ‖u - half • (wq + wp)‖ := by
        rw [smul_add]
        apply δ_le'
        apply h₂
        repeat' exact Subtype.mem _
        repeat' exact le_of_lt one_half_pos
        exact add_halves 1
      have eq₂ : ‖a‖ <= δ + div := by grw [hw, Nat.one_div_le_one_div hq]
      have eq₂' : ‖b‖ <= δ + div := by grw [hw, Nat.one_div_le_one_div hp]
      rw [dist_eq_norm]
      apply nonneg_le_nonneg_of_sq_le_sq
      · exact sqrt_nonneg _
      rw [mul_self_sqrt]
      · calc
        ‖wp - wq‖ * ‖wp - wq‖ =
            2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ := by
          simp [← this]
        _ <= 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * δ * δ := by gcongr
        _ <= 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ := by gcongr
        _ = 8 * δ * div + 4 * div * div := by ring
      positivity
    -- third goal : `Tendsto (fun (n : ℕ) => √(b n)) atTop (𝓝 0)`
    suffices Tendsto (fun x => √(8 * δ * x + 4 * x * x) : Real -> Real) (𝓝 0) (𝓝 0)
      from this.comp tendsto_one_div_add_atTop_nhds_zero_nat
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchySeq_tendsto_of_isComplete h₁ (fun n => Subtype.mem _) seq_is_cauchy with
    ⟨v, hv, w_tendsto⟩
  use v, hv
  have h_cont : Continuous fun v => ‖u - v‖ := by fun_prop
  have : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 ‖u - v‖) := by
    convert! Tendsto.comp h_cont.continuousAt w_tendsto
  exact tendsto_nhds_unique this norm_tendsto

/--
theorem `norm_eq_iInf_iff_real_inner_le_zero` / 定理 `norm_eq_iInf_iff_real_inner_le_zero`

English:
theorem norm_eq_iInf_iff_real_inner_le_zero
  statement: {K : Set F} (h : Convex Real K) {u : F} {v : F}
  proof: by
  let : Nonempty K := ⟨⟨v, hv⟩⟩
  constructor
  · intro eq w hw
    let δ := ⨅ w : K, ‖u - w‖
    let p := ⟪u - v, w - v⟫_Real
    let q := ‖w - v‖ ^ 2
    have δ_le (w : K) : δ <= ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    have δ_le' (w) (hw : w in K) : δ <= ‖u - w‖ := δ_le

中文:
定理 norm_eq_iInf_iff_real_inner_le_zero
  结论: {K : Set F} (h : Convex 实数 K) {u : F} {v : F}
  证明: by
  let : Nonempty K := ⟨⟨v, hv⟩⟩
  constructor
  · intro eq w hw
    let δ := ⨅ w : K, ‖u - w‖
    let p := ⟪u - v, w - v⟫_Real
    let q := ‖w - v‖ ^ 2
    have δ_le (w : K) : δ <= ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    have δ_le' (w) (hw : w in K) : δ <= ‖u - w‖ := δ_le

Depends on / 依赖: Nonempty, _Real, ciInf_le, norm_nonneg
-/
theorem norm_eq_iInf_iff_real_inner_le_zero {K : Set F} (h : Convex Real K) {u : F} {v : F}
    (hv : v in K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪u - v, w - v⟫_Real <= 0 := by
  let : Nonempty K := ⟨⟨v, hv⟩⟩
  constructor
  · intro eq w hw
    let δ := ⨅ w : K, ‖u - w‖
    let p := ⟪u - v, w - v⟫_Real
    let q := ‖w - v‖ ^ 2
    have δ_le (w : K) : δ <= ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    have δ_le' (w) (hw : w in K) : δ <= ‖u - w‖ := δ_le ⟨w, hw⟩
    have (θ : Real) (hθ₁ : 0 < θ) (hθ₂ : θ <= 1) : 2 * p <= θ * q := by
      have : ‖u - v‖ ^ 2 <= ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_Real + θ * θ * ‖w - v‖ ^ 2 :=
        calc ‖u - v‖ ^ 2
          _ <= ‖u - (θ • w + (1 - θ) • v)‖ ^ 2 := by
            simp only [sq]; apply mul_self_le_mul_self (norm_nonneg _)
            rw [eq]; apply δ_le'
            apply h hw hv
            exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel _ _]
          _ = ‖u - v - θ • (w - v)‖ ^ 2 := by
            have : u - (θ • w + (1 - θ) • v) = u - v - θ • (w - v) := by
              rw [smul_sub]; rw [sub_smul]; rw [one_smul]
              simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev]
            rw [this]
          _ = ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_Real + θ * θ * ‖w - v‖ ^ 2 := by
            rw [@norm_sub_sq Real]; rw [inner_smul_right]; rw [norm_smul]
            simp only [sq]
            change
              ‖u - v‖ * ‖u - v‖ - 2 * (θ * ⟪u - v, w - v⟫_Real) +
                absR θ * ‖w - v‖ * (absR θ * ‖w - v‖) =
              ‖u - v‖ * ‖u - v‖ - 2 * θ * ⟪u - v, w - v⟫_Real + θ * θ * (‖w - v‖ * ‖w - v‖)
            rw [abs_of_pos hθ₁]; ring
      have eq₁ :
        ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_Real + θ * θ * ‖w - v‖ ^ 2 =
          ‖u - v‖ ^ 2 + (θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_Real) := by
        abel
      rw [eq₁]; rw [le_add_iff_nonneg_right] at this
      have eq₂ :
        θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_Real =
          θ * (θ * ‖w - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_Real) := by ring
      rw [eq₂] at this
      exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁)
    by_cases hq : q = 0
    · rw [hq] at this
      have : p <= 0 := by
        have := this (1 : Real) (by simp) (by simp)
        linarith
      exact this
    · have q_pos : 0 < q := lt_of_le_of_ne (sq_nonneg _) fun h => hq h.symm
      by_contra hp
      rw [not_le] at hp
      let θ := min (1 : Real) (p / q)
      have eq₁ : θ * q <= p :=
        calc
          θ * q <= p / q * q := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
          _ = p := div_mul_cancel₀ _ hq
      have : 2 * p <= p :=
        calc
          2 * p <= θ * q := by
            exact this θ (lt_min (by simp) (div_pos hp q_pos)) (by simp [θ])
          _ <= p := eq₁
      linarith
  · intro h
    apply le_antisymm
    · apply le_ciInf
      intro w
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      have := h w w.2
      calc
        ‖u - v‖ * ‖u - v‖ <= ‖u - v‖ * ‖u - v‖ - 2 * ⟪u - v, w - v⟫_Real := by linarith
        _ <= ‖u - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_Real + ‖w - v‖ ^ 2 := by
          rw [sq]
          refine le_add_of_nonneg_right ?_
          exact sq_nonneg _
        _ = ‖u - v - (w - v)‖ ^ 2 := (@norm_sub_sq Real _ _ _ _ _ _).symm
        _ = ‖u - w‖ * ‖u - w‖ := by
          have : u - v - (w - v) = u - w := by abel
          rw [this]; rw [sq]
    · change ⨅ w : K, ‖u - w‖ <= (fun w : K => ‖u - w‖) ⟨v, hv⟩
      apply ciInf_le
      use 0
      rintro y ⟨z, rfl⟩
      exact norm_nonneg _

namespace Submodule

variable (K : Submodule 𝕜 E)

/--
theorem `exists_norm_eq_iInf_of_complete_subspace` / 定理 `exists_norm_eq_iInf_of_complete_subspace`

English:
theorem exists_norm_eq_iInf_of_complete_subspace
  given: (h : IsComplete (↑K : Set E))
  proof: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := Submodule.restrictScalars Real K
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

中文:
定理 exists_norm_eq_iInf_of_complete_subspace
  条件: (h : IsComplete (↑K : Set E))
  证明: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := Submodule.restrictScalars Real K
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, Submodule, Submodule.restrictScalars, convex, exists_norm_eq_iInf_of_complete_convex, rclikeToReal, restrictScalars, zero_mem
-/
theorem exists_norm_eq_iInf_of_complete_subspace (h : IsComplete (↑K : Set E)) :
    forall u : E, exists v in K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖ := by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := Submodule.restrictScalars Real K
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

/--
theorem `norm_eq_iInf_iff_real_inner_eq_zero` / 定理 `norm_eq_iInf_iff_real_inner_eq_zero`

English:
theorem norm_eq_iInf_iff_real_inner_eq_zero
  given: (K : Submodule Real F) {u : F} {v : F} (hv : v in K)
  proof: Iff.intro
    (by
      intro h
      have h : forall w in K, ⟪u - v, w - v⟫_Real <= 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_Real <= 0 := by
        let w' := w + v
        have : w' in K := Submodule.ad

中文:
定理 norm_eq_iInf_iff_real_inner_eq_zero
  条件: (K : Submodule 实数 F) {u : F} {v : F} (hv : v in K)
  证明: Iff.intro
    (by
      intro h
      have h : forall w in K, ⟪u - v, w - v⟫_Real <= 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_Real <= 0 := by
        let w' := w + v
        have : w' in K := Submodule.ad

Depends on / 依赖: Iff.intro, K.convex, Submodule, Submodule.add_mem, Submodule.neg_mem, _Real, add_mem, add_neg_cancel_right, convex, exacts, neg_mem, norm_eq_iInf_iff_real_inner_le_zero, sub_eq_add_neg
-/
theorem norm_eq_iInf_iff_real_inner_eq_zero (K : Submodule Real F) {u : F} {v : F} (hv : v in K) :
    (‖u - v‖ = ⨅ w : (↑K : Set F), ‖u - w‖) ↔ forall w in K, ⟪u - v, w⟫_Real = 0 :=
  Iff.intro
    (by
      intro h
      have h : forall w in K, ⟪u - v, w - v⟫_Real <= 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_Real <= 0 := by
        let w' := w + v
        have : w' in K := Submodule.add_mem _ hw hv
        have h₁ := h w' this
        have h₂ : w' - v = w := by
          simp only [w', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂] at h₁
        exact h₁
      have ge : ⟪u - v, w⟫_Real >= 0 := by
        let w'' := -w + v
        have : w'' in K := Submodule.add_mem _ (Submodule.neg_mem _ hw) hv
        have h₁ := h w'' this
        have h₂ : w'' - v = -w := by
          simp only [w'', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂]; rw [inner_neg_right] at h₁
        linarith
      exact le_antisymm le ge)
    (by
      intro h
      have : forall w in K, ⟪u - v, w - v⟫_Real <= 0 := by
        intro w hw
        let w' := w - v
        have : w' in K := Submodule.sub_mem _ hw hv
        have h₁ := h w' this
        exact le_of_eq h₁
      rwa [norm_eq_iInf_iff_real_inner_le_zero]
      exacts [Submodule.convex _, hv])

/--
theorem `norm_eq_iInf_iff_inner_eq_zero` / 定理 `norm_eq_iInf_iff_inner_eq_zero`

English:
theorem norm_eq_iInf_iff_inner_eq_zero
  given: {u : E} {v : E} (hv : v in K)
  proof: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := K.restrictScalars Real
  constructor
  · intro H
    have A : forall w in K, re ⟪u - v, w⟫ = 0 := (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).1 H
    intro w hw
    apply RCLike.ext
    · simp [A

中文:
定理 norm_eq_iInf_iff_inner_eq_zero
  条件: {u : E} {v : E} (hv : v in K)
  证明: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := K.restrictScalars Real
  constructor
  · intro H
    have A : forall w in K, re ⟪u - v, w⟫ = 0 := (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).1 H
    intro w hw
    apply RCLike.ext
    · simp [A

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, K.restrictScalars, K.smul_mem, RCLike, RCLike.ext, Submodule, im.map_zero, inner_smul_right, map_zero, norm_eq_iInf_iff_real_inner_eq_zero, rclikeToReal, restrictScalars, smul_mem
-/
theorem norm_eq_iInf_iff_inner_eq_zero {u : E} {v : E} (hv : v in K) :
    (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪u - v, w⟫ = 0 := by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule Real E := K.restrictScalars Real
  constructor
  · intro H
    have A : forall w in K, re ⟪u - v, w⟫ = 0 := (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).1 H
    intro w hw
    apply RCLike.ext
    · simp [A w hw]
    · symm
      calc
        im (0 : 𝕜) = 0 := im.map_zero
        _ = re ⟪u - v, (-I : 𝕜) • w⟫ := (A _ (K.smul_mem (-I) hw)).symm
        _ = re (-I * ⟪u - v, w⟫) := by rw [inner_smul_right]
        _ = im ⟪u - v, w⟫ := by simp
  · intro H
    have : forall w in K', ⟪u - v, w⟫_Real = 0 := by
      intro w hw
      rw [real_inner_eq_re_inner]; rw [H w hw]
      exact zero_re
    exact (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).2 this

end Submodule
