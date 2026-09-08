/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The space of continuous maps is a locally convex space

In this file we prove that the space of continuous maps from a topological space
to a locally convex topological vector space is a locally convex topological vector space.
-/

public section

open scoped Topology

/-
**ContinuousMap.instLocallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMap.instLocallyConvexSpace {X 𝕜 E : Type*} [TopologicalSpace X] 
[Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
 [LocallyConvexSpace 𝕜 E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] : 
LocallyConvexSpace 𝕜 C(X, E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConvexSpace.ofBasisZero`：LocallyConvexSpace.ofBasisZero {ι : Type
*} (b : ι -> Set E) (p : ι -> Prop) (hbasis : (𝓝 0).HasBasis p b) (hconvex : for
all i, p i -> Convex…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `Filter.HasBasis.nhds_continuousMapConst`：∀ {X : Type u_2} {Y : Type u_3}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {ι : Type u_6} {c : Y
}   {p : ι → Prop} {U : ι → S…
· 使用定理 `LocallyConvexSpace.convex_basis_zero`：LocallyConvexSpace.convex_basis_ze
ro [LocallyConvexSpace 𝕜 E] : (𝓝 0 : Filter E).HasBasis (fun s => s in (𝓝 0 : Fi
lter E) ∧ Convex 𝕜 s) id
-/
instance ContinuousMap.instLocallyConvexSpace {X 𝕜 E : Type*}
    [TopologicalSpace X]
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [LocallyConvexSpace 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] :
    LocallyConvexSpace 𝕜 C(X, E) :=
  .ofBasisZero _ _ _ _ (LocallyConvexSpace.convex_basis_zero 𝕜 E).nhds_continuousMapConst <| by
    rintro ⟨K, U⟩ ⟨hK, hU₀, hUc⟩ f hf g hg a b ha hb hab x hx
    exact hUc (hf hx) (hg hx) ha hb hab
