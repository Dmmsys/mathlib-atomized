/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song, Xuchun Li, Bryan Wang
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Separation.Connected
/-!
# Existence of an open normal subgroup in any clopen neighborhood of the neutral element

This file proves the lemma `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`,
which states that in a compact topological group, for any clopen neighborhood of 1,
there exists an open normal subgroup contained within it.

We then apply this lemma to show `ProfiniteGrp.closedSubgroup_eq_sInf_open`:
any closed subgroup of a profinite group is the intersection of the open subgroups containing it.

This file is split out from the file `OpenSubgroup` because it needs more imports.
-/

public section

namespace IsTopologicalGroup

@[to_additive]
/-
**IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one** 是 Mathlib
 中的一个定理，位于命名空间 `IsTopologicalGroup`。
形式化陈述：exist_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [Top
ologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : 
IsClopen W) (einW : 1 in W) : exists H : OpenNormalSubgroup G, (H : Set G) subse
teq W
参数：WClopen : IsClopen W；einW : 1 in W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`：exist_open
Subgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G] [IsTo
pologicalGroup G] [CompactSpace G] {W : Set G} (WC…
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用引理 `Subgroup.isOpen_of_isClosed_of_finiteIndex`：isOpen_of_isClosed_of_finite
Index (H : Subgroup G) [H.FiniteIndex] (h : IsClosed (H : Set G)) : IsOpen (H : 
Set G)
· 使用引理 `Subgroup.normalCore_isClosed`：normalCore_isClosed (H : Subgroup G) (h : 
IsClosed (H : Set G)) : IsClosed (H.normalCore : Set G)
· 使用定理 `OpenSubgroup.isClosed`：isClosed [SeparatelyContinuousMul G] (U : OpenSub
group G) : IsClosed (U : Set G)
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
-/
theorem exist_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  rcases exist_openSubgroup_sub_clopen_nhds_of_one WClopen einW with ⟨H, hH⟩
  have : Subgroup.FiniteIndex H.toSubgroup := H.finiteIndex_of_finite_quotient
  use { toSubgroup := Subgroup.normalCore H
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed H.isClosed) }
  exact fun _ b ↦ hH (H.normalCore_le b)

end IsTopologicalGroup

namespace ProfiniteGrp

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

@[to_additive]
/-
**ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one** 是 Mathlib 中的一个定理，
位于命名空间 `ProfiniteGrp`。
形式化陈述：exist_openNormalSubgroup_sub_open_nhds_of_one {U : Set G} (UOpen : IsOpen 
U) (einU : 1 in U) : exists H : OpenNormalSubgroup G, (H : Set G) subseteq U
参数：UOpen : IsOpen U；einU : 1 in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用定理 `nhds_basis_clopen`：nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : S
et X => x in s ∧ IsClopen s) id
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `TotallyDisconnectedSpace.t1Space`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [h : TotallyDisconnectedSpace X], T1Space X
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`：exis
t_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSp
ace G] [IsTopologicalGroup G] [CompactSpace G] {W : Set …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exist_openNormalSubgroup_sub_open_nhds_of_one
    {U : Set G} (UOpen : IsOpen U) (einU : 1 ∈ U) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
  rcases IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW.2 hW.1 with ⟨H, hH⟩
  exact ⟨H, fun _ a ↦ h (hH a)⟩

open scoped Pointwise in
/--
Any closed subgroup of a profinite group is the intersection of the open subgroups containing it.
See https://math.stackexchange.com/questions/5023433/closed-subgroups-of-a-compact-topological-group.
-/
@[to_additive /--
Any closed subgroup of a profinite group is the intersection of the open subgroups containing it.
See https://math.stackexchange.com/questions/5023433/closed-subgroups-of-a-compact-topological-group.
-/]
/-
**ProfiniteGrp.closedSubgroup_eq_sInf_open** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteG
rp`。
形式化陈述：closedSubgroup_eq_sInf_open (H : ClosedSubgroup G) : H = sInf {N : Subgrou
p G | IsOpen (N : Set G) ∧ H <= N}
参数：H : ClosedSubgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
· 使用定理 `ClosedSubgroup.isClosed'`：∀ {G : Type u} [inst : Group G] [inst_1 : Topo
logicalSpace G] (self : ClosedSubgroup G), IsClosed (↑self).carrier
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
· 使用定理 `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`：exist_openNo
rmalSubgroup_sub_open_nhds_of_one {U : Set G} (UOpen : IsOpen U) (einU : 1 in U)
 : exists H : OpenNormalSubgroup G, (H : Set G) …
· 使用定理 `Subgroup.mem_sup_of_normal_left`：mem_sup_of_normal_left {s t : Subgroup 
G} [hs : s.Normal] {x : G} : x in s ⊔ t ↔ exists y in s, exists z in t, y * z = 
x
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `mem_leftCoset`：mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) 
: a * x in a • s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosedSubgroup.instSubgroupClass`：∀ (G : Type u) [inst : Group G] [inst_
1 : TopologicalSpace G], SubgroupClass (ClosedSubgroup G) G
· 使用定理 `Subgroup.mem_sInf`：mem_sInf {S : Set (Subgroup G)} {x : G} : x in sInf S
 ↔ forall p in S, x in p
· 使用定理 `Subgroup.isOpen_mono`：isOpen_mono [SeparatelyContinuousMul G] {H₁ H₂ : S
ubgroup G} (h : H₁ <= H₂) (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem closedSubgroup_eq_sInf_open (H : ClosedSubgroup G) :
    H = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := by
  apply le_antisymm
  · exact le_sInf fun N hN ↦ hN.2
  · intro g hg
    by_contra hg_not
    let U : Set G := (g • H)ᶜ
    have UOpen : IsOpen U :=
      ((Homeomorph.mulLeft g).isClosedMap _ H.isClosed').isOpen_compl
    have einU : 1 ∈ U := by
      refine Set.mem_compl (fun ⟨l, hl, (hgl : g * l = 1)⟩ ↦ ?_)
      rw [← inv_eq_iff_mul_eq_one] at hgl
      exact hg_not <| inv_mem_iff.mp (hgl ▸ hl)
    obtain ⟨N, hN⟩ := exist_openNormalSubgroup_sub_open_nhds_of_one UOpen einU
    let NH : Subgroup G := N ⊔ H
    have hg_not' : g ∉ NH := by
      by_contra hg'
      rcases Subgroup.mem_sup_of_normal_left.mp hg' with ⟨y, hy, z, hz, hyz⟩
      rw [← eq_mul_inv_iff_mul_eq] at hyz
      exact hN (hyz ▸ hy) <| mem_leftCoset g (inv_mem_iff.mpr hz)
    exact hg_not' <|
      Subgroup.mem_sInf.mp hg _ ⟨Subgroup.isOpen_mono le_sup_left N.isOpen, le_sup_right⟩

end ProfiniteGrp

