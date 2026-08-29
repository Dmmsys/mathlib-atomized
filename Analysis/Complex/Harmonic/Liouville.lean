/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Liouville's Theorem for Harmonic Functions on the Complex Plane

A bounded harmonic function on the complex plane is constant.
-/

public section

open Bornology Complex Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

-- Auxiliary version of Liouville's theorem, for real-valued harmonic functions on the complex
-- plane.
/--
theorem `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux` / 定理 `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux`

English:
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux
  statement: (f : Complex -> Real)
  proof: by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := h_harm.exists_analyticOnNhd_univ_re_eq
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  suffices forall z w, Complex.exp (F z) = Complex.exp (F w) by grin

中文:
定理 内积空间.bounded_harmonic_on_complex_plane_is_constant_aux
  结论: (f : 复形 -> 实数)
  证明: by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := h_harm.exists_analyticOnNhd_univ_re_eq
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  suffices forall z w, Complex.exp (F z) = Complex.exp (F w) by grin
-/
private theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux (f : Complex -> Real)
    (h_harm : HarmonicOnNhd f univ) (h_bound : Bornology.IsBounded (range f)) :
    forall z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := h_harm.exists_analyticOnNhd_univ_re_eq
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  suffices forall z w, Complex.exp (F z) = Complex.exp (F w) by grind
  apply Differentiable.apply_eq_apply_of_bounded
  · apply (differentiable_exp.comp (fun x => (hF_diff x (mem_univ x)).differentiableAt))
  rw [isBounded_iff_forall_norm_le] at *
  obtain ⟨M, hM⟩ := h_bound
  use Real.exp M
  simp_all only [mem_range, norm_eq_abs, forall_exists_index, forall_apply_eq_imp_iff,
    norm_exp, exp_le_exp]
  rw [← hF_re] at hM
  grind

/--
theorem `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant` / 定理 `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`

English:
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant
  statement: (f : Complex -> E)
  proof: by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' Real (f z - f w)
  rw [map_sub]; rw [RCLike.ofReal_real_eq_id]; rw [id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [range_comp] using IsBounded.image ℓ h_bound
  rw [← sub_eq_zero]; rw [← norm_eq_zero]; rw [

中文:
定理 内积空间.bounded_harmonic_on_complex_plane_is_constant
  结论: (f : 复形 -> E)
  证明: by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' Real (f z - f w)
  rw [map_sub]; rw [RCLike.ofReal_real_eq_id]; rw [id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [range_comp] using IsBounded.image ℓ h_bound
  rw [← sub_eq_zero]; rw [← norm_eq_zero]; rw [

Depends on / 依赖: Bornology, Bornology.IsBounded, IsBounded, IsBounded.image, RCLike, RCLike.ofReal_real_eq_id, bounded_harmonic_on_complex_plane_is_constant_aux, comp_CLM, exists_dual_vector, h_bound, h_harm, h_harm.comp_CLM, id_eq, map_sub, norm_eq_zero, ofReal_real_eq_id, range_comp, sub_eq_zero
-/
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant (f : Complex -> E)
    (h_harm : HarmonicOnNhd f univ) (h_bound : IsBounded (range f)) :
    forall z w, f z = f w := by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' Real (f z - f w)
  rw [map_sub]; rw [RCLike.ofReal_real_eq_id]; rw [id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [range_comp] using IsBounded.image ℓ h_bound
  rw [← sub_eq_zero]; rw [← norm_eq_zero]; rw [← h₂ℓ]
  grind [bounded_harmonic_on_complex_plane_is_constant_aux (ℓ ∘ f) (h_harm.comp_CLM ℓ) η₁]
