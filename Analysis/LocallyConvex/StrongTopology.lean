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
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/-
**UniformConvergenceCLM.locallyConvexSpace** 是 Mathlib 中的一个定理，位于命名空间 `UniformCon
vergenceCLM`。
形式化陈述：locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn 
(· subseteq ·) 𝔖) : LocallyConvexSpace R (UniformConvergenceCLM σ F 𝔖)
参数：𝔖 : Set (Set E)；h𝔖₁ : 𝔖.Nonempty；h𝔖₂ : DirectedOn (· subseteq ·) 𝔖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConvexSpace.ofBasisZero`：LocallyConvexSpace.ofBasisZero {ι : Type
*} (b : ι -> Set E) (p : ι -> Prop) (hbasis : (𝓝 0).HasBasis p b) (hconvex : for
all i, p i -> Convex…
· 使用定理 `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero_of
_basis [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set 
E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedO…
· 使用定理 `LocallyConvexSpace.convex_basis_zero`：LocallyConvexSpace.convex_basis_ze
ro [LocallyConvexSpace 𝕜 E] : (𝓝 0 : Filter E).HasBasis (fun s => s in (𝓝 0 : Fi
lter E) ∧ Convex 𝕜 s) id
-/
theorem locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
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
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/-
**ContinuousLinearMap.instLocallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：instLocallyConvexSpace : LocallyConvexSpace R (E ->SL[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.locallyConvexSpace`：locallyConvexSpace (𝔖 : Set (S
et E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· subseteq ·) 𝔖) : LocallyConvexSpa
ce R (UniformConvergenceCLM σ …
· 使用定理 `Bornology.isVonNBounded_empty`：isVonNBounded_empty : IsVonNBounded 𝕜 (∅ 
: Set E)
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
· 使用定理 `Bornology.IsVonNBounded.union`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : S
eminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalSp
ace E] {s₁ s₂ : Set…
-/
instance instLocallyConvexSpace : LocallyConvexSpace R (E →SL[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

end ContinuousLinearMap

end BoundedSets

