/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Sets.Compacts

/-!
# Additional results on topological groups

A result on topological groups that has been separated out
as it requires more substantial imports developing positive compacts.
-/

public section


universe u
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Every topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive
  /-- Every topological additive group
  in which there exists a compact set with nonempty interior is locally compact. -/]
/-
**TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group (K : Positi
veCompacts G) : LocallyCompactSpace G
参数：K : PositiveCompacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_group`：IsCompact.locallyCom
pactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G} (h : K in 
𝓝 x) : LocallyCompactSpace G
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    (K : PositiveCompacts G) : LocallyCompactSpace G :=
  let ⟨_x, hx⟩ := K.interior_nonempty
  K.isCompact.locallyCompactSpace_of_mem_nhds_of_group (mem_interior_iff_mem_nhds.1 hx)
