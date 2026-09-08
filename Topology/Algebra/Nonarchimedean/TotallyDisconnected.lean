/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard, David Loeffler, Yongle Hu, Johan Commelin
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total separatedness of nonarchimedean groups

In this file, we prove that a nonarchimedean group is a totally separated topological space.
The fact that a nonarchimedean group is a totally disconnected topological space
is implied by the fact that a nonarchimedean group is totally separated.

## Main results

- `NonarchimedeanGroup.instTotallySeparated`:
  A nonarchimedean group is a totally separated topological space.

## Notation

- `G` : Is a nonarchimedean group.
- `V` : Is an open subgroup which is a neighbourhood of the identity in `G`.

## References

See Proposition 2.3.9 and Problem 63 in [F. Q. Gouvêa, *p-adic numbers*][gouvea1997].
-/

public section

open scoped Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G] [NonarchimedeanGroup G] [T2Space G]

namespace NonarchimedeanGroup

@[to_additive]
/-
**NonarchimedeanGroup.exists_openSubgroup_separating** 是 Mathlib 中的一个引理，位于命名空间 `
NonarchimedeanGroup`。
形式化陈述：exists_openSubgroup_separating {a b : G} (h : a != b) : exists V : OpenSub
group G, Disjoint (a • (V : Set G)) (b • V)
参数：h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `NonarchimedeanGroup.is_nonarchimedean`：∀ {G : Type u_1} {inst : Group G}
 {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G],   ∀ U ∈ nhds 1, ∃
 V, ↑V ⊆ U
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `OpenSubgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G] [inst_
1 : TopologicalSpace G], SubgroupClass (OpenSubgroup G) G
· 使用定理 `mem_leftCoset_iff`：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
lemma exists_openSubgroup_separating {a b : G} (h : a ≠ b) :
    ∃ V : OpenSubgroup G, Disjoint (a • (V : Set G)) (b • V) := by
  obtain ⟨u, v, _, open_v, mem_u, mem_v, dis⟩ := t2_separation (h ∘ inv_mul_eq_one.mp)
  obtain ⟨V, hV⟩ := is_nonarchimedean v (open_v.mem_nhds mem_v)
  use V
  simp only [Disjoint, Set.bot_eq_empty, Set.subset_empty_iff]
  intro x mem_aV mem_bV
  by_contra! ⟨s, hs⟩
  have hsa : s ∈ a • (V : Set G) := mem_aV hs
  have hsb : s ∈ b • (V : Set G) := mem_bV hs
  rw [mem_leftCoset_iff] at hsa hsb
  refine dis.subset_compl_right mem_u (hV ?_)
  simpa [mul_assoc] using mul_mem hsa (inv_mem hsb)

@[to_additive]
/-
**NonarchimedeanGroup.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchimedeanGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instTotallySeparated : TotallySeparatedSpace G where
  isTotallySeparated_univ x _ y _ hxy := by
    obtain ⟨V, dxy⟩ := exists_openSubgroup_separating hxy
    exact ⟨_, _, V.isOpen.smul x, (V.isClosed.smul x).isOpen_compl, mem_own_leftCoset ..,
      dxy.subset_compl_left <| mem_own_leftCoset .., by simp, disjoint_compl_right⟩

end NonarchimedeanGroup

