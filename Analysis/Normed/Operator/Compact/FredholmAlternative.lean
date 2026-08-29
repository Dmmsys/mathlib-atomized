/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz, i.e. bounded below.
* `hasEigenvalue_or_mem_resolventSet`: the Fredholm alternative for compact operators, which says
  that if `T` is a compact operator and `μ ≠ 0`, then either `μ` is an eigenvalue of `T`, or `μ`
  is in the resolvent set of `T`.
* `hasEigenvalue_iff_mem_spectrum`: if `T` is a compact operator, then the nonzero eigenvalues of
  `T` are exactly the nonzero points in the spectrum of `T`.

We follow the proof given in Section 2 of
https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/
but adapt it to work in a more general setting of spaces over nontrivially normed fields,
rather than just over `ℝ` or `ℂ`. The main technical hurdle is that we don't have the ability to
rescale vectors to have norm exactly `1`, so we have to work with vectors in a shell instead of on
the unit sphere, and this makes some of the intermediate statements more complicated.
-/

public section

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {T : X ->L[𝕜] X} {μ : 𝕜}

open Module End

open Filter Topology in
/--
theorem `antilipschitz_of_not_hasEigenvalue` / 定理 `antilipschitz_of_not_hasEigenvalue`

English:
theorem antilipschitz_of_not_hasEigenvalue
  statement: (hT : IsCompactOperator T) (hμ : μ != 0)
  proof: by
  -- Suppose not, and attempt to find an eigenvector with eigenvalue `μ`.
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  -- then for every `K > 0`, there is some `x` such that `‖(T - μ • 1) x‖ < K * ‖x‖`.
  replace hK : forall K > 0, exists x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  -

中文:
定理 antilipschitz_of_not_hasEigenvalue
  结论: (hT : IsCompactOperator T) (hμ : μ != 0)
  证明: by
  -- Suppose not, and attempt to find an eigenvector with eigenvalue `μ`.
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  -- then for every `K > 0`, there is some `x` such that `‖(T - μ • 1) x‖ < K * ‖x‖`.
  replace hK : forall K > 0, exists x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  -
-/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ != 0)
    (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    exists K, AntilipschitzWith K (T - μ • 1 : X ->L[𝕜] X) := by
  -- Suppose not, and attempt to find an eigenvector with eigenvalue `μ`.
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  -- then for every `K > 0`, there is some `x` such that `‖(T - μ • 1) x‖ < K * ‖x‖`.
  replace hK : forall K > 0, exists x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  -- In fact, there is a lower bound `c` such that for every `ε > 0`, there is an `x` with norm
  -- in the interval `[c, 1]` such that `‖(T - μ • 1) x‖ < ε`.
  -- (In the case of an `RCLike` field, where we can rescale, we could even get `‖x‖ = 1`, but we
  -- don't need that.)
  replace hK : exists c > 0, forall ε > 0, exists x, ‖x‖ <= 1 ∧ c <= ‖x‖ ∧ ‖(T - μ • 1) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε => ?_⟩
    obtain ⟨x, hx⟩ := hK ε (by positivity)
    have : x != 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) this
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc₀, hc⟩ := hK
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : Real)
  -- Then find a sequence of vectors `xₙ` with norm in the interval `[c, 1]` such
  -- that `‖(T - μ • 1) xₙ‖ < φ n`, where `φ n` is a sequence of positive numbers tending to zero.
  have (n : Nat) : exists x, ‖x‖ <= 1 ∧ c <= ‖x‖ ∧ ‖(T - μ • 1) x‖ < φ n := hc (φ n) (hφ_pos n)
  choose x hx_norm_upper hx_norm_lower hx_bound using this
  have hx_lim : Tendsto (fun n => (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors `yₙ := T xₙ`
  let y_ (n : Nat) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : exists d > 0, forallᶠ n in atTop, d <= ‖y_ n‖ := by
    refine ⟨(‖μ‖ * c) / 2, by positivity, ?_⟩
    filter_upwards [hφ.eventually_le_const (show (‖μ‖ * c) / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ * ‖x n‖ <= ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    linear_combination h₂ + h₁ + hn + ‖μ‖ * hx_norm_lower n
  -- The sequence `yₙ` is contained in the image of the closed unit ball under `T`,
  -- which is compact, since `T` is,
  -- so we can extract a convergent subsequence, and say `y_ (ψ n) → y`.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) (fun n => hK' ⟨x n, by simp [*], rfl⟩)
  -- However `(T - μ • 1) yₙ = T ((T - μ • 1) xₙ) → 0`
  have hy_lim : Tendsto (fun n => (T - μ • 1) (y_ n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using T.continuous.continuousAt.tendsto.comp hx_lim
  -- so `(T - μ • 1) y = 0`.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X ->L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since `yₙ` are bounded away from `0`, we must have `y ≠ 0`.
  have hy_ne : y != 0 := by
    obtain ⟨d, hd₀, hd⟩ := hy_lower
    rintro rfl
    suffices forallᶠ n : Nat in atTop, False by rwa [eventually_const] at this
    rw [NormedAddGroup.tendsto_nhds_zero] at hψy
    filter_upwards [hψ.tendsto_atTop.eventually hd, hψy d (by positivity)] using by grind
  -- So `y` is an eigenvector of `T` with eigenvalue `μ`,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact hasEigenvalue_of_hasEigenvector this

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_seq` / 定理 `exists_seq`

English:
theorem exists_seq
  statement: {S : End 𝕜 X} (hS_not_surj : ¬ (S : X -> X).Surjective)
  proof: by
  -- Construct the sequence of submodules `V n := (S ^ n).range`, and show that they are closed.
  let V (n : Nat) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : Nat) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : Nat) : IsClosed (V n : Set X) 

中文:
定理 exists_seq
  结论: {S : End 𝕜 X} (hS_not_surj : ¬ (S : X -> X).Surjective)
  证明: by
  -- Construct the sequence of submodules `V n := (S ^ n).range`, and show that they are closed.
  let V (n : Nat) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : Nat) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : Nat) : IsClosed (V n : Set X) 
-/
private theorem exists_seq {S : End 𝕜 X} (hS_not_surj : ¬ (S : X -> X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R) :
    exists f : Nat -> X,
      (forall n, 1 <= ‖f n‖) ∧ (forall n, ‖f n‖ <= R) ∧ (forall n, f n in (S ^ n).range) ∧
      (forall n, forall y in (S ^ (n + 1)).range, 1 <= ‖f n - y‖) := by
  -- Construct the sequence of submodules `V n := (S ^ n).range`, and show that they are closed.
  let V (n : Nat) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : Nat) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : Nat) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  -- Apply Riesz's lemma repeatedly using the closed subspace `V (n+1)` inside `V n`.
  have x (n : Nat) : exists x in V n, 1 <= ‖x‖ ∧ ‖x‖ <= R ∧ forall y in V (n + 1), 1 <= ‖x - y‖ := by
    have h₁ : IsClosed ((V (n + 1)).comap (V n).subtype : Set (V n)) := by
      simpa using! (hV_closed (n + 1)).preimage_val
    have h₂ : exists x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V, (iterate_injective hS_anti.injective n).eq_iff,
        Function.Surjective] using! hS_not_surj
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Subtype.forall] at hxn hxy
    exact ⟨x, hx, by simpa using! hxy 0, hxn,
      fun y hy => hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  -- Use the existential claim to construct the sequence `f n`.
  choose x hxv hxn hxn' hxy using x
  exact ⟨x, hxn, hxn', hxv, hxy⟩

variable [CompleteSpace X]

/--
theorem `hasEigenvalue_or_mem_resolventSet` / 定理 `hasEigenvalue_or_mem_resolventSet`

English:
theorem hasEigenvalue_or_mem_resolventSet
  given: (hT : IsCompactOperator T) (hμ : μ != 0)
  proof: by
  -- Suppose not, then `μ` is not an eigenvalue and is in the spectrum.
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  -- Defining S := `T - μ • 1`, we deduce that S is antilipschitz and not surjective.
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue 

中文:
定理 hasEigenvalue_or_mem_resolventSet
  条件: (hT : IsCompactOperator T) (hμ : μ != 0)
  证明: by
  -- Suppose not, then `μ` is not an eigenvalue and is in the spectrum.
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  -- Defining S := `T - μ • 1`, we deduce that S is antilipschitz and not surjective.
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue 
-/
theorem hasEigenvalue_or_mem_resolventSet (hT : IsCompactOperator T) (hμ : μ != 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨ μ in resolventSet 𝕜 T := by
  -- Suppose not, then `μ` is not an eigenvalue and is in the spectrum.
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  -- Defining S := `T - μ • 1`, we deduce that S is antilipschitz and not surjective.
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue hT hμ h₁
  replace h₂ : ¬ (S : X -> X).Bijective := by
    rw [spectrum.mem_resolventSet_iff]; rw [← IsUnit.neg_iff]; rw [ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert! h₂
    ext x
    simp [S]
  replace h₂ : ¬ (S : X -> X).Surjective := by grind [Function.Bijective, hK.injective]
  -- Take a sequence of vectors `f n` in the range of `S ^ n` such that `‖f n‖` is in the
  -- interval `[1, ‖c‖ + 1]` and such that `f n` is at least `1` away from any vector in the range
  -- of `S ^ (n + 1)`.
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ := exists_seq h₂
    (hK.isClosedEmbedding S.uniformContinuous) hc (R := ‖c‖ + 1) (by simp)
  replace hf_mem {n m : Nat} (h : m <= n) : f n in ((S : End 𝕜 X) ^ m).range :=
    (S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem _)
  have hf_mem' {n m : Nat} (h : m <= n) : S (f n) in ((S : End 𝕜 X) ^ (m + 1)).range := by
    rw [iterate_succ']; rw [LinearMap.range_comp]
    exact ⟨f n, hf_mem h, rfl⟩
  -- Then the points `T (f n)` are bounded away from each other, using the separation property
  -- of the `f n` and the lower bound on their norms.
  have hp : Pairwise fun x₁ x₂ => ‖μ‖ <= ‖T (f x₁) - T (f x₂)‖ := by
    have : Std.Symm fun x₁ x₂ => ‖μ‖ <= ‖T (f x₁) - T (f x₂)‖ := by grind [symm_def, norm_sub_rev]
    apply Pairwise.of_lt
    intro m n hmn
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = T (f m) - T (f n) := by
      rw [smul_sub]; rw [smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u in ((S : End 𝕜 X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ (hf_mem' hmn.le) (hf_mem' le_rfl)
      · exact Submodule.smul_mem _ μ (hf_mem hmn)
    grw [← hu, norm_smul, mul_comm, ← hf_far _ u this, one_mul]
  -- However the `f n` are contained in a compact set, so their image under the compact operator `T`
  -- must contain a Cauchy subsequence, which is a contradiction.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (fun n => hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  have : ‖T (f (ψ (N + 1))) - T (f (ψ N))‖ < ‖μ‖ := by simpa [dist_eq_norm_sub] using hN (N + 1)
  refine this.not_ge (hp ?_)
  simp [hψ.injective.eq_iff]

/--
theorem `hasEigenvalue_iff_mem_spectrum` / 定理 `hasEigenvalue_iff_mem_spectrum`

English:
theorem hasEigenvalue_iff_mem_spectrum
  given: (hT : IsCompactOperator T) (hμ : μ != 0)
  proof: by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · exact (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

中文:
定理 hasEigenvalue_iff_mem_spectrum
  条件: (hT : IsCompactOperator T) (hμ : μ != 0)
  证明: by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · exact (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.spectrum_eq, hasEigenvalue_or_mem_resolventSet, mem_spectrum, resolve_right, spectrum_eq
-/
theorem hasEigenvalue_iff_mem_spectrum (hT : IsCompactOperator T) (hμ : μ != 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ in spectrum 𝕜 T := by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · exact (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

end IsCompactOperator
