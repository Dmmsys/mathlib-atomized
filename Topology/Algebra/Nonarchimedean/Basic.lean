/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `NonarchimedeanAddGroup`: nonarchimedean additive group.
- `NonarchimedeanGroup`: nonarchimedean multiplicative group.
- `NonarchimedeanRing`: nonarchimedean ring.

-/

public section

open Topology
open scoped Pointwise

/-- A topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup. -/
/-
**NonarchimedeanAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [AddGroup G] → [TopologicalSpace G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup.
-/
class NonarchimedeanAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G] : Prop
  extends IsTopologicalAddGroup G where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : G), ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U

/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
/-
**NonarchimedeanGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Group G] → [TopologicalSpace G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological group is nonarchimedean if every neighborhood of 1 contains an ope
n subgroup.
-/
class NonarchimedeanGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop
  extends IsTopologicalGroup G where
  is_nonarchimedean : ∀ U ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ U

/-- A topological ring is nonarchimedean if its underlying topological additive
  group is nonarchimedean. -/
/-
**NonarchimedeanRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Ring R] → [TopologicalSpace R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological ring is nonarchimedean if its underlying topological additive
  group is nonarchimedean.
-/
class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] : Prop
  extends IsTopologicalRing R where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U

-- see Note [lower instance priority]
/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every nonarchimedean ring is naturally a nonarchimedean additive group.
-/
instance (priority := 100) NonarchimedeanRing.to_nonarchimedeanAddGroup (R : Type*) [Ring R]
    [TopologicalSpace R] [t : NonarchimedeanRing R] : NonarchimedeanAddGroup R :=
  { t with }

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type*} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]

/-- If a topological group embeds into a nonarchimedean group, then it is nonarchimedean. -/
@[to_additive]
/-
**NonarchimedeanGroup.nonarchimedean_of_emb** 是 Mathlib 中的一个定理，位于命名空间 `Nonarchim
edeanGroup`。
形式化陈述：nonarchimedean_of_emb (f : G ->* H) (emb : IsOpenEmbedding f) : Nonarchime
deanGroup H
参数：f : G ->* H；emb : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `NonarchimedeanGroup.is_nonarchimedean`：∀ {G : Type u_1} {inst : Group G}
 {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G],   ∀ U ∈ nhds 1, ∃
 V, ↑V ⊆ U
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t

--- 原说明 ---
If a topological group embeds into a nonarchimedean group, then it is nonarchime
dean.
-/
theorem nonarchimedean_of_emb (f : G →* H) (emb : IsOpenEmbedding f) : NonarchimedeanGroup H :=
  { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U ∈ 𝓝 (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }

/-- An open neighborhood of the identity in the Cartesian product of two nonarchimedean groups
contains the Cartesian product of an open neighborhood in each group. -/
@[to_additive NonarchimedeanAddGroup.prod_subset /-- An open neighborhood of the identity in
the Cartesian product of two nonarchimedean groups contains the Cartesian product of
an open neighborhood in each group. -/]
/-
**NonarchimedeanGroup.prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `NonarchimedeanGroup
`。
形式化陈述：prod_subset {U} (hU : U in 𝓝 (1 : G × K)) : exists (V : OpenSubgroup G) (W
 : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) subseteq U
参数：hU : U in 𝓝 (1 : G × K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `NonarchimedeanGroup.is_nonarchimedean`：∀ {G : Type u_1} {inst : Group G}
 {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G],   ∀ U ∈ nhds 1, ∃
 V, ↑V ⊆ U
-/
theorem prod_subset {U} (hU : U ∈ 𝓝 (1 : G × K)) :
    ∃ (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) ⊆ U := by
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean _ hU₁
  obtain ⟨W, hW⟩ := is_nonarchimedean _ hU₂
  use V
  grind

/-- An open neighborhood of the identity in the Cartesian square of a nonarchimedean group
contains the Cartesian square of an open neighborhood in the group. -/
@[to_additive NonarchimedeanAddGroup.prod_self_subset /-- An open neighborhood of the identity in
the Cartesian square of a nonarchimedean group contains the Cartesian square of
an open neighborhood in the group. -/]
/-
**NonarchimedeanGroup.prod_self_subset** 是 Mathlib 中的一个定理，位于命名空间 `Nonarchimedean
Group`。
形式化陈述：prod_self_subset {U} (hU : U in 𝓝 (1 : G × G)) : exists V : OpenSubgroup G
, (V : Set G) ×ˢ (V : Set G) subseteq U
参数：hU : U in 𝓝 (1 : G × G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonarchimedeanGroup.prod_subset`：prod_subset {U} (hU : U in 𝓝 (1 : G × K
)) : exists (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K
) subseteq U
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem prod_self_subset {U} (hU : U ∈ 𝓝 (1 : G × G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ×ˢ (V : Set G) ⊆ U :=
  let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine Set.Subset.trans (Set.prod_mono ?_ ?_) ‹_› <;> simp⟩

/-- The Cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive /-- The Cartesian product of two nonarchimedean groups is nonarchimedean. -/]
/-
**NonarchimedeanGroup.Prod.instNonarchimedeanGroup** 是 Mathlib 中的一个定理，位于命名空间 `No
narchimedeanGroup.Prod`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [Nonarchim
edeanGroup G] {K : Type u_3}   [inst_3 : Group K] [inst_4 : TopologicalSpace K] 
[NonarchimedeanGroup K], NonarchimedeanGroup (G × K)
参数：G × K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonarchimedeanGroup.toIsTopologicalGroup`：∀ {G : Type u_1} {inst : Group
 G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G], IsTopologicalG
roup G
· 使用定理 `NonarchimedeanGroup.prod_subset`：prod_subset {U} (hU : U in 𝓝 (1 : G × K
)) : exists (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K
) subseteq U

--- 原说明 ---
The Cartesian product of two nonarchimedean groups is nonarchimedean.
-/
instance Prod.instNonarchimedeanGroup : NonarchimedeanGroup (G × K) where
  is_nonarchimedean _ hU :=
    let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩

end NonarchimedeanGroup

namespace NonarchimedeanRing

open NonarchimedeanAddGroup

variable {R S : Type*}
variable [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]
variable [Ring S] [TopologicalSpace S] [NonarchimedeanRing S]

/-- The Cartesian product of two nonarchimedean rings is nonarchimedean. -/
/-
**NonarchimedeanRing.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchimedeanRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two nonarchimedean rings is nonarchimedean.
-/
instance : NonarchimedeanRing (R × S) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- Given an open subgroup `U` and an element `r` of a nonarchimedean ring, there is an open
  subgroup `V` such that `r • V` is contained in `U`. -/
/-
**NonarchimedeanRing.left_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `NonarchimedeanRi
ng`。
形式化陈述：left_mul_subset (U : OpenAddSubgroup R) (r : R) : exists V : OpenAddSubgro
up R, r • (V : Set R) subseteq U
参数：U : OpenAddSubgroup R；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonarchimedeanRing.toIsTopologicalRing`：∀ {R : Type u_1} {inst : Ring R}
 {inst_1 : TopologicalSpace R} [self : NonarchimedeanRing R], IsTopologicalRing 
R
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s

--- 原说明 ---
Given an open subgroup `U` and an element `r` of a nonarchimedean ring, there is
 an open
  subgroup `V` such that `r • V` is contained in `U`.
-/
theorem left_mul_subset (U : OpenAddSubgroup R) (r : R) :
    ∃ V : OpenAddSubgroup R, r • (V : Set R) ⊆ U :=
  ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_const_mul r), (U : Set R).image_preimage_subset _⟩

/-- An open subgroup of a nonarchimedean ring contains the square of another one. -/
/-
**NonarchimedeanRing.mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `NonarchimedeanRing`。
形式化陈述：mul_subset (U : OpenAddSubgroup R) : exists V : OpenAddSubgroup R, (V : Se
t R) * V subseteq U
参数：U : OpenAddSubgroup R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonarchimedeanAddGroup.prod_self_subset`：∀ {G : Type u_1} [inst : AddGro
up G] [inst_1 : TopologicalSpace G] [NonarchimedeanAddGroup G] {U : Set (G × G)}
,   U ∈ nhds 0 → ∃ V, ↑V ×ˢ ↑…
· 使用定理 `NonarchimedeanRing.to_nonarchimedeanAddGroup`：∀ (R : Type u_1) [inst : R
ing R] [inst_1 : TopologicalSpace R] [t : NonarchimedeanRing R], NonarchimedeanA
ddGroup R
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonarchimedeanRing.toIsTopologicalRing`：∀ {R : Type u_1} {inst : Ring R}
 {inst_1 : TopologicalSpace R} [self : NonarchimedeanRing R], IsTopologicalRing 
R
· 使用定理 `OpenAddSubgroup.isOpen`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : T
opologicalSpace G] (U : OpenAddSubgroup G), IsOpen ↑U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `AddSubgroup.zero_mem`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSubgr
oup G), 0 ∈ H
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p

--- 原说明 ---
An open subgroup of a nonarchimedean ring contains the square of another one.
-/
theorem mul_subset (U : OpenAddSubgroup R) : ∃ V : OpenAddSubgroup R, (V : Set R) * V ⊆ U := by
  let ⟨V, H⟩ := prod_self_subset <| (U.isOpen.preimage continuous_mul).mem_nhds <| by
    simpa only [Set.mem_preimage, Prod.snd_zero, mul_zero] using! U.zero_mem
  use V
  rintro v ⟨a, ha, b, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [SetLike.mem_coe]
  exact hy

end NonarchimedeanRing

