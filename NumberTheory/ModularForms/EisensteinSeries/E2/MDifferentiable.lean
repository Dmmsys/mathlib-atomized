/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Gauss AI (Math Inc)
-/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# MDifferentiability of the weight 2 Eisenstein series

We show that the weight 2 Eisenstein series `E2` is MDifferentiable (i.e. holomorphic as a
function `ℍ → ℂ`). The proof uses the relation between `E2` and the logarithmic derivative of
the Dedekind eta function.
-/

public section

open UpperHalfPlane hiding I
open Real Complex EisensteinSeries ModularForm Manifold


--This proof was provided by Gauss to the sphere packing project.
/--
lemma `E2_mdifferentiable` / 引理 `E2_mdifferentiable`

English:
lemma E2_mdifferentiable
  statement: MDiff E2
  proof: by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn Complex η _ := fun z hz =>
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hlog : DifferentiableOn Complex (logDeriv η) _ :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη (fun _ hz => eta_

中文:
引理 E2_mdifferentiable
  结论: MDiff E2
  证明: by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn Complex η _ := fun z hz =>
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hlog : DifferentiableOn Complex (logDeriv η) _ :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη (fun _ hz => eta_

Depends on / 依赖: DifferentiableOn, UpperHalfPlane, UpperHalfPlane.mdifferentiable_iff, const_mul, differentiableAt_eta_of_mem_upperHalfPlaneSet, differentiableWithinAt, eta_ne_zero, hlog.const_mul, isOpen_upperHalfPlaneSet, logDeriv, logDeriv_eta_eq_E2, mdifferentiable_iff, ofComplex_apply_of_im_pos
-/
lemma E2_mdifferentiable : MDiff E2 := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn Complex η _ := fun z hz =>
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hlog : DifferentiableOn Complex (logDeriv η) _ :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη (fun _ hz => eta_ne_zero hz)
  refine (hlog.const_mul (π * I / 12)⁻¹).congr (fun z hz => ?_)
  simp [ofComplex_apply_of_im_pos hz, logDeriv_eta_eq_E2 ⟨z, hz⟩]
  field_simp

end
