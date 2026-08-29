/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Analysis.InnerProductSpace.Semisimple

/-! # Joint eigenspaces of commuting symmetric operators

This file collects various decomposition results for joint eigenspaces of commuting
symmetric operators on a finite-dimensional inner product space.

## Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that in finite dimensions
  if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `Commute A B` imply that
  `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
  `eigenspace B μ ⊓ eigenspace A ν`
* `LinearMap.IsSymmetric.iSup_iInf_eigenspace_eq_top_of_commute` establishes that in finite
  dimensions, the indexed supremum of the joint eigenspaces of a commuting tuple of symmetric
  linear operators equals `⊤`
* `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute` establishes the
  analogous result to `LinearMap.IsSymmetric.directSum_isInternal_of_commute` for commuting
  tuples of symmetric operators.

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

symmetric operator, simultaneous eigenspaces, joint eigenspaces

-/

public section

open Module.End

namespace LinearMap

namespace IsSymmetric

variable {𝕜 E n m : Type*}

open Submodule

section RCLike

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {α : 𝕜} {A B : E ->ₗ[𝕜] E} {T : n -> Module.End 𝕜 E}

/--
theorem `orthogonalFamily_eigenspace_inf_eigenspace` / 定理 `orthogonalFamily_eigenspace_inf_eigenspace`

English:
theorem orthogonalFamily_eigenspace_inf_eigenspace
  given: (hA : A.IsSymmetric) (hB : B.IsSymmetric)
  proof: OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1, hv2⟩ => by
    obtain (h₁ | h₂) : i.1 != j.1 ∨ i.2 != j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

中文:
定理 orthogonalFamily_eigenspace_inf_eigenspace
  条件: (hA : A.IsSymmetric) (hB : B.IsSymmetric)
  证明: OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1, hv2⟩ => by
    obtain (h₁ | h₂) : i.1 != j.1 ∨ i.2 != j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

Depends on / 依赖: Ne.eq_def, OrthogonalFamily, OrthogonalFamily.of_pairwise, Prod.ext_iff, all_goals, eq_def, ext_iff, hA.orthogonalFamily_eigenspaces.pairwise, hB.orthogonalFamily_eigenspaces.pairwise, not_and_or, of_pairwise, orthogonalFamily_eigenspaces, pairwise
-/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
      fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1, hv2⟩ => by
    obtain (h₁ | h₂) : i.1 != j.1 ∨ i.2 != j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

/--
theorem `orthogonalFamily_iInf_eigenspaces` / 定理 `orthogonalFamily_iInf_eigenspaces`

English:
theorem orthogonalFamily_iInf_eigenspaces
  given: (hT : forall i, (T i).IsSymmetric)
  proof: by
  intro f g hfg Ef Eg
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hfg
  have H := orthogonalFamily_eigenspaces (hT a) ha
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (g _)).mp Eg.2 _

中文:
定理 orthogonalFamily_iInf_eigenspaces
  条件: (hT : 对任意 i, (T i).IsSymmetric)
  证明: by
  intro f g hfg Ef Eg
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hfg
  have H := orthogonalFamily_eigenspaces (hT a) ha
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (g _)).mp Eg.2 _

Depends on / 依赖: Function, Function.ne_iff.mp, Submodule, Submodule.coe_subtype, Submodule.mem_iInf, Subtype, Subtype.forall, coe_subtype, eigenspace, mem_iInf, ne_iff, orthogonalFamily_eigenspaces
-/
theorem orthogonalFamily_iInf_eigenspaces (hT : forall i, (T i).IsSymmetric) :
    OrthogonalFamily 𝕜 (fun γ : n -> 𝕜 => (⨅ j, eigenspace (T j) (γ j) : Submodule 𝕜 E))
      fun γ : n -> 𝕜 => (⨅ j, eigenspace (T j) (γ j)).subtypeₗᵢ := by
  intro f g hfg Ef Eg
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hfg
  have H := orthogonalFamily_eigenspaces (hT a) ha
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ => eigenspace (T _) (g _)).mp Eg.2 _

variable [FiniteDimensional 𝕜 E]

open IsFinitelySemisimple

/--
theorem `iSup_eigenspace_inf_eigenspace_of_commute` / 定理 `iSup_eigenspace_inf_eigenspace_of_commute`

English:
theorem iSup_eigenspace_inf_eigenspace_of_commute
  given: (hB : B.IsSymmetric) (hAB : Commute A B)
  proof: by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [genEigenspace_eq_eigenspace, Submodule.orthogonal_eq_bot_iff]
using orthogonalComplement_iSup_eigenspaces_eq_bot
hB.restrict_invariant mapsTo_genEigenspace_of_comm hAB α 1

中文:
定理 iSup_eigenspace_inf_eigenspace_of_commute
  条件: (hB : B.IsSymmetric) (hAB : Commute A B)
  证明: by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [genEigenspace_eq_eigenspace, Submodule.orthogonal_eq_bot_iff]
using orthogonalComplement_iSup_eigenspaces_eq_bot
hB.restrict_invariant mapsTo_genEigenspace_of_comm hAB α 1

Depends on / 依赖: Submodule, Submodule.map_iSup, Submodule.orthogonal_eq_bot_iff, conv_rhs, eigenspace, genEigenspace_eq_eigenspace, hB.restrict_invariant, inf_genEigenspace, map_iSup, map_subtype_top, mapsTo_genEigenspace_of_comm, orthogonalComplement_iSup_eigenspaces_eq_bot, orthogonal_eq_bot_iff, restrict_invariant
-/
theorem iSup_eigenspace_inf_eigenspace_of_commute (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [genEigenspace_eq_eigenspace, Submodule.orthogonal_eq_bot_iff]
using orthogonalComplement_iSup_eigenspaces_eq_bot
hB.restrict_invariant mapsTo_genEigenspace_of_comm hAB α 1

/--
theorem `iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute` / 定理 `iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute`

English:
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
  statement: (hA : A.IsSymmetric)
  proof: by
  simpa [iSup_eigenspace_inf_eigenspace_of_commute hB hAB] using
Submodule.orthogonal_eq_bot_iff.mp hA.orthogonalComplement_iSup_eigenspaces_eq_bot

中文:
定理 iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
  结论: (hA : A.IsSymmetric)
  证明: by
  simpa [iSup_eigenspace_inf_eigenspace_of_commute hB hAB] using
Submodule.orthogonal_eq_bot_iff.mp hA.orthogonalComplement_iSup_eigenspaces_eq_bot

Depends on / 依赖: Submodule, Submodule.orthogonal_eq_bot_iff.mp, hA.orthogonalComplement_iSup_eigenspaces_eq_bot, iSup_eigenspace_inf_eigenspace_of_commute, orthogonalComplement_iSup_eigenspaces_eq_bot, orthogonal_eq_bot_iff
-/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace_of_commute hB hAB] using
Submodule.orthogonal_eq_bot_iff.mp hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/--
theorem `directSum_isInternal_of_commute` / 定理 `directSum_isInternal_of_commute`

English:
theorem directSum_isInternal_of_commute
  statement: (hA : A.IsSymmetric) (hB : B.IsSymmetric)
  proof: by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff]; rw [iSup_prod]; rw [iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB

中文:
定理 directSum_is整数ernal_of_commute
  结论: (hA : A.IsSymmetric) (hB : B.IsSymmetric)
  证明: by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff]; rw [iSup_prod]; rw [iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB

Depends on / 依赖: Submodule, Submodule.orthogonal_eq_bot_iff, iSup_comm, iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute, iSup_prod, isInternal_iff, isInternal_iff.mpr, orthogonalFamily_eigenspace_inf_eigenspace, orthogonal_eq_bot_iff
-/
theorem directSum_isInternal_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : Commute A B) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1)) := by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff]; rw [iSup_prod]; rw [iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB

open scoped Function -- required for scoped `on` notation

/--
theorem `iSup_iInf_eq_top_of_commute` / 定理 `iSup_iInf_eq_top_of_commute`

English:
theorem iSup_iInf_eq_top_of_commute
  statement: {ι : Type*} {T : ι -> E ->ₗ[𝕜] E}
  proof: calc
  _ = ⨆ χ : ι -> 𝕜, ⨅ i, maxGenEigenspace (T i) (χ i) :=
    congr(⨆ χ : ι -> 𝕜, ⨅ i,
 (maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) (χ _))).symm
  _ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T h fun _ => by
    rw [← orthogonal_eq_bot_iff]; rw [congr(⨆ μ]; rw [$(maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) μ))]; rw [(hT _).orthogonalComplement_iSup_eigenspaces_eq_bot]

中文:
定理 iSup_iInf_eq_top_of_commute
  结论: {ι : 类型} {T : ι -> E ->ₗ[𝕜] E}
  证明: calc
  _ = ⨆ χ : ι -> 𝕜, ⨅ i, maxGenEigenspace (T i) (χ i) :=
    congr(⨆ χ : ι -> 𝕜, ⨅ i,
 (maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) (χ _))).symm
  _ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T h fun _ => by
    rw [← orthogonal_eq_bot_iff]; rw [congr(⨆ μ]; rw [$(maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) μ))]; rw [(hT _).orthogonalComplement_iSup_eigenspaces_eq_bot]

Depends on / 依赖: iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute, isFinitelySemisimple, maxGenEigenspace, maxGenEigenspace_eq_eigenspace, orthogonalComplement_iSup_eigenspaces_eq_bot, orthogonal_eq_bot_iff
-/
theorem iSup_iInf_eq_top_of_commute {ι : Type*} {T : ι -> E ->ₗ[𝕜] E}
    (hT : forall i, (T i).IsSymmetric) (h : Pairwise (Commute on T)) :
    ⨆ χ : ι -> 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ :=
  calc
  _ = ⨆ χ : ι -> 𝕜, ⨅ i, maxGenEigenspace (T i) (χ i) :=
    congr(⨆ χ : ι -> 𝕜, ⨅ i,
 (maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) (χ _))).symm
  _ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T h fun _ => by
    rw [← orthogonal_eq_bot_iff]; rw [congr(⨆ μ]; rw [$(maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) μ))]; rw [(hT _).orthogonalComplement_iSup_eigenspaces_eq_bot]

/--
theorem `directSum_isInternal_of_pairwise_commute` / 定理 `directSum_isInternal_of_pairwise_commute`

English:
theorem directSum_isInternal_of_pairwise_commute
  statement: [DecidableEq (n -> 𝕜)]
  proof: by
  rw [OrthogonalFamily.isInternal_iff]
  · rw [iSup_iInf_eq_top_of_commute hT hC, top_orthogonal_eq_bot]
  · exact orthogonalFamily_iInf_eigenspaces hT

中文:
定理 directSum_is整数ernal_of_pairwise_commute
  结论: [DecidableEq (n -> 𝕜)]
  证明: by
  rw [OrthogonalFamily.isInternal_iff]
  · rw [iSup_iInf_eq_top_of_commute hT hC, top_orthogonal_eq_bot]
  · exact orthogonalFamily_iInf_eigenspaces hT

Depends on / 依赖: OrthogonalFamily, OrthogonalFamily.isInternal_iff, iSup_iInf_eq_top_of_commute, isInternal_iff, orthogonalFamily_iInf_eigenspaces, top_orthogonal_eq_bot
-/
theorem directSum_isInternal_of_pairwise_commute [DecidableEq (n -> 𝕜)]
    (hT : forall i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    DirectSum.IsInternal (fun α : n -> 𝕜 => ⨅ j, eigenspace (T j) (α j)) := by
  rw [OrthogonalFamily.isInternal_iff]
  · rw [iSup_iInf_eq_top_of_commute hT hC, top_orthogonal_eq_bot]
  · exact orthogonalFamily_iInf_eigenspaces hT

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute :=
  directSum_isInternal_of_pairwise_commute

end RCLike

end IsSymmetric

end LinearMap
