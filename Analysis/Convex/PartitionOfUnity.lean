/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Analysis.Convex.Combination

/-!
# Partition of unity and convex sets

In this file we prove the following lemma, see `exists_continuous_forall_mem_convex_of_local`. Let
`X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be a
topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for each
point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is continuous
on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map `g : C(X, E)`
such that `g x ∈ t x` for all `x`.

We also formulate a useful corollary, see `exists_continuous_forall_mem_convex_of_local_const`, that
assumes that local functions `g` are constants.

## Tags

partition of unity
-/

public section


open Set Function

open Topology

variable {ι X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E]

/-
**PartitionOfUnity.finsum_smul_mem_convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PartitionOfUnity.finsum_smul_mem_convex {s : Set X} (f : PartitionOfUnity 
ι X s) {g : ι -> X -> E} {t : Set E} {x : X} (hx : x in s) (hg : forall i, f i x
 != 0 -> g i x in t) (ht : Convex Real t) : (∑ᶠ i, f i x • g i x) in t
参数：f : PartitionOfUnity ι X s；hx : x in s；hg : forall i, f i x != 0 -> g i x in 
t；ht : Convex Real t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.finsum_mem`：Convex.finsum_mem {ι : Sort*} {w : ι -> R} {z : ι -> 
E} {s : Set E} (hs : Convex R s) (h₀ : forall i, 0 <= w i) (h₁ : ∑ᶠ i, w i = 1) 
(hz : f…
· 使用定理 `PartitionOfUnity.nonneg`：nonneg (i : ι) (x : X) : 0 <= f i x
· 使用定理 `PartitionOfUnity.sum_eq_one`：sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f 
i x = 1
-/
theorem PartitionOfUnity.finsum_smul_mem_convex {s : Set X} (f : PartitionOfUnity ι X s)
    {g : ι → X → E} {t : Set E} {x : X} (hx : x ∈ s) (hg : ∀ i, f i x ≠ 0 → g i x ∈ t)
    (ht : Convex ℝ t) : (∑ᶠ i, f i x • g i x) ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

variable [NormalSpace X] [ParacompactSpace X] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {t : X → Set E}

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is
continuous on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map
`g : C(X, E)` such that `g x ∈ t x` for all `x`. See also
`exists_continuous_forall_mem_convex_of_local_const`. -/
/-
**exists_continuous_forall_mem_convex_of_local** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_forall_mem_convex_of_local (ht : forall x, Convex Real (
t x)) (H : forall x : X, exists U in 𝓝 x, exists g : X -> E, ContinuousOn g U ∧ 
forall y in U, g y in t y) : exists g : C(X, E), forall x, g x in t x
参数：ht : forall x, Convex Real (t x)；H : forall x : X, exists U in 𝓝 x, exists g 
: X -> E, ContinuousOn g U ∧ forall y in U, g y in t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.exists_isSubordinate`：exists_isSubordinate [NormalSpace
 X] [ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOp
en (U i)) (hU : s subseteq …
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PartitionOfUnity.IsSubordinate.continuous_finsum_smul`：∀ {ι : Type u} {X
 : Type v} [inst : TopologicalSpace X] {E : Type u_1} [inst_1 : AddCommMonoid E]
   [inst_2 : SMulWithZero ℝ E] [inst_3 : To…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `PartitionOfUnity.finsum_smul_mem_convex`：PartitionOfUnity.finsum_smul_me
m_convex {s : Set X} (f : PartitionOfUnity ι X s) {g : ι -> X -> E} {t : Set E} 
{x : X} (hx : x in s) (hg : f…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `X` be a normal paracompact topological space (e.g., any extended metric spa
ce). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets.
 Suppose that for
each point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X 
→ E` that is
continuous on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists 
a continuous map
`g : C(X, E)` such that `g x ∈ t x` for all `x`. See also
`exists_continuous_forall_mem_convex_of_local_const`.
-/
theorem exists_continuous_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (H : ∀ x : X, ∃ U ∈ 𝓝 x, ∃ g : X → E, ContinuousOn g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C(X, E), ∀ x, g x ∈ t x := by
  choose U hU g hgc hgt using H
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x => interior (U x))
    (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (fun i => isOpen_interior) fun i => (hgc i).mono interior_subset⟩,
    fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ ?_) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a vector `c : E` that belongs to `t y` for all `y` in a
neighborhood of `x`. Then there exists a continuous map `g : C(X, E)` such that `g x ∈ t x` for all
`x`. See also `exists_continuous_forall_mem_convex_of_local`. -/
/-
**exists_continuous_forall_mem_convex_of_local_const** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：exists_continuous_forall_mem_convex_of_local_const (ht : forall x, Convex 
Real (t x)) (H : forall x : X, exists c : E, forallᶠ y in 𝓝 x, c in t y) : exist
s g : C(X, E), forall x, g x in t x
参数：ht : forall x, Convex Real (t x)；H : forall x : X, exists c : E, forallᶠ y in
 𝓝 x, c in t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_continuous_forall_mem_convex_of_local`：exists_continuous_forall_m
em_convex_of_local (ht : forall x, Convex Real (t x)) (H : forall x : X, exists 
U in 𝓝 x, exists g : X -> E, Conti…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s

--- 原说明 ---
Let `X` be a normal paracompact topological space (e.g., any extended metric spa
ce). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets.
 Suppose that for
each point `x : X`, there exists a vector `c : E` that belongs to `t y` for all 
`y` in a
neighborhood of `x`. Then there exists a continuous map `g : C(X, E)` such that 
`g x ∈ t x` for all
`x`. See also `exists_continuous_forall_mem_convex_of_local`.
-/
theorem exists_continuous_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (H : ∀ x : X, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C(X, E), ∀ x, g x ∈ t x :=
  exists_continuous_forall_mem_convex_of_local ht fun x =>
    let ⟨c, hc⟩ := H x
    ⟨_, hc, fun _ => c, continuousOn_const, fun _ => id⟩
