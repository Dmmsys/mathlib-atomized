/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimple operators on inner product spaces

This file is a place to gather results related to semisimplicity of linear operators on inner
product spaces.

-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable {T : Module.End 𝕜 E} {p : Submodule 𝕜 E} (hT : T.IsSymmetric)

include hT

/--
lemma `orthogonalComplement_mem_invtSubmodule` / 引理 `orthogonalComplement_mem_invtSubmodule`

English:
lemma orthogonalComplement_mem_invtSubmodule
  given: (hp : p in T.invtSubmodule)
  proof: fun x hx y hy => hT y x ▸ hx (T y) (hp hy)

中文:
引理 orthogonalComplement_mem_invtSubmodule
  条件: (hp : p in T.invtSubmodule)
  证明: fun x hx y hy => hT y x ▸ hx (T y) (hp hy)
-/
lemma orthogonalComplement_mem_invtSubmodule (hp : p in T.invtSubmodule) :
    pᗮ in T.invtSubmodule :=
  fun x hx y hy => hT y x ▸ hx (T y) (hp hy)

/--
theorem `isFinitelySemisimple` / 定理 `isFinitelySemisimple`

English:
theorem isFinitelySemisimple
  proof: by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ =>
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ 

中文:
定理 isFinitelySemisimple
  证明: by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ =>
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ 

Depends on / 依赖: Finite, Module, Module.End.invtSubmodule.inf_mem, Module.End.isFinitelySemisimple_iff.mpr, Module.Finite, Submodule, Submodule.finiteDimensional_of_le, Submodule.inf_orthogonal_eq_bot, Submodule.sup_orthogonal_of_hasOrthogonalProjection, disjoint_iff, finiteDimensional_of_le, inf_assoc, inf_le_right, inf_mem, inf_orthogonal_eq_bot, invtSubmodule, isFinitelySemisimple_iff, orthogonalComplement_mem_invtSubmodule, replace, sup_inf_assoc_of_le
-/
theorem isFinitelySemisimple :
    T.IsFinitelySemisimple := by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ =>
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ qᗮ = ⊤ by rw [← sup_inf_assoc_of_le _ hq₂, this, top_inf_eq p]
    replace hp₂ : Module.Finite 𝕜 q := Submodule.finiteDimensional_of_le hq₂
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end LinearMap.IsSymmetric
