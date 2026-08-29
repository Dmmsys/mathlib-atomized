/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## TODO

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/

public section


open Topology UniformConvergence

variable {R 𝕜₁ 𝕜₂ E F : Type*}

variable [AddCommGroup E] [TopologicalSpace E] [AddCommGroup F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

section General

namespace UniformConvergenceCLM

variable (R)
variable [Semiring R] [PartialOrder R]
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ ->+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/--
theorem `locallyConvexSpace` / 定理 `locallyConvexSpace`

English:
theorem locallyConvexSpace
  statement: (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
  proof: by
  apply LocallyConvexSpace.ofBasisZero _ _ _ _
    (UniformConvergenceCLM.hasBasis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (LocallyConvexSpace.convex_basis_zero R F)) _
  rintro ⟨S, V⟩ ⟨_, _, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab

中文:
定理 locallyConvexSpace
  结论: (𝔖 : 集合 (集合 E)) (h𝔖₁ : 𝔖.非空)
  证明: by
  apply LocallyConvexSpace.ofBasisZero _ _ _ _
    (UniformConvergenceCLM.hasBasis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (LocallyConvexSpace.convex_basis_zero R F)) _
  rintro ⟨S, V⟩ ⟨_, _, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab

Depends on / 依赖: LocallyConvexSpace, LocallyConvexSpace.convex_basis_zero, LocallyConvexSpace.ofBasisZero, UniformConvergenceCLM, UniformConvergenceCLM.hasBasis_nhds_zero_of_basis, convex_basis_zero, hVconvex, hasBasis_nhds_zero_of_basis, ofBasisZero
-/
theorem locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· subseteq ·) 𝔖) :
    LocallyConvexSpace R (UniformConvergenceCLM σ F 𝔖) := by
  apply LocallyConvexSpace.ofBasisZero _ _ _ _
    (UniformConvergenceCLM.hasBasis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (LocallyConvexSpace.convex_basis_zero R F)) _
  rintro ⟨S, V⟩ ⟨_, _, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab

end UniformConvergenceCLM

end General

section BoundedSets

namespace ContinuousLinearMap

variable [Semiring R] [PartialOrder R]
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ ->+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/--
Instance `instLocallyConvexSpace` / 实例 `instLocallyConvexSpace`

English:
instance instLocallyConvexSpace
  signature: : LocallyConvexSpace R (E ->SL[σ] F)
  body: UniformConvergenceCLM.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

中文:
实例 instLocallyConvexSpace
  签名: : LocallyConvex空间 R (E ->SL[σ] F)
  定义体: UniformConvergenceCLM.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

Depends on / 依赖: Bornology, Bornology.IsVonNBounded.union, Bornology.isVonNBounded_empty, IsVonNBounded, UniformConvergenceCLM, UniformConvergenceCLM.locallyConvexSpace, directedOn_of_sup_mem, isVonNBounded_empty, locallyConvexSpace
-/
instance instLocallyConvexSpace : LocallyConvexSpace R (E ->SL[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

end ContinuousLinearMap

end BoundedSets
