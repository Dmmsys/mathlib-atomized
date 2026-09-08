/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.GroupTheory.Complement
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Lemma of B. H. Neumann on coverings of a group by cosets.

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$:
$$ G = ⋃_{i = 1}^n C_i g_i. $$

* `Subgroup.exists_finiteIndex_of_leftCoset_cover`
  at least one subgroup $C_i$ has finite index in $G$.

* `Subgroup.leftCoset_cover_filter_FiniteIndex`
  the cosets of subgroups of infinite index may be omitted from the covering.

* `Subgroup.exists_index_le_card_of_leftCoset_cover` :
  the index of (at least) one of these subgroups does not exceed $n$.

* `Subgroup.one_le_sum_inv_index_of_leftCoset_cover` :
  the sum of the inverses of the indexes of the $C_i$ is greater than or equal to 1.

* `Subgroup.pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one`
  If the sum of the inverses of the indexes of the subgroups $C_i$ is equal to 1,
  then the cosets of the subgroups of finite index are pairwise disjoint.

A corollary of `Subgroup.exists_finiteIndex_of_leftCoset_cover` is:

* `Subspace.biUnion_ne_univ_of_ne_top` :
  a vector space over an infinite field cannot be a finite union of proper subspaces.

This can be used to show that an algebraic extension of fields is determined by the
set of all minimal polynomials (not proved here).

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

-/

public section

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

section leftCoset_cover_const

@[to_additive]
/-
**Subgroup.exists_leftTransversal_of_FiniteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Subg
roup`。
形式化陈述：exists_leftTransversal_of_FiniteIndex {D H : Subgroup G} [D.FiniteIndex] (
hD_le_H : D <= H) : exists t : Finset H, IsComplement (t : Set H) (D.subgroupOf 
H) ∧ ⋃ g in t, (g : G) • (D : Set G) = H
参数：hD_le_H : D <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.exists_isComplement_left`：exists_isComplement_left (H : Subgrou
p G) (g : G) : exists S, IsComplement S H ∧ g in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.finite_left_iff`：finite_left_iff (h : IsComplement
 S H) : Finite S ↔ H.FiniteIndex
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.IsComplement.inv_toLeftFun_mul_mem`：inv_toLeftFun_mul_mem (hS :
 IsComplement S H) (g : G) : (toLeftFun hS g : G)⁻¹ * g in H
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
theorem exists_leftTransversal_of_FiniteIndex
    {D H : Subgroup G} [D.FiniteIndex] (hD_le_H : D ≤ H) :
    ∃ t : Finset H,
      IsComplement (t : Set H) (D.subgroupOf H) ∧
        ⋃ g ∈ t, (g : G) • (D : Set G) = H := by
  have ⟨t, ht⟩ := (D.subgroupOf H).exists_isComplement_left 1
  have hf : t.Finite := ht.1.finite_left_iff.mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  suffices (∃ y ∈ t, ∃ d ∈ D, y * d = x) ↔ x ∈ H by simpa using! this
  constructor
  · rintro ⟨⟨y, hy⟩, -, d, h, rfl⟩
    exact H.mul_mem hy (hD_le_H h)
  · intro hx
    exact ⟨_, (ht.1.toLeftFun ⟨x, hx⟩).2, _,
      ht.1.inv_toLeftFun_mul_mem ⟨x, hx⟩, mul_inv_cancel_left _ _⟩

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι → G}

@[to_additive]
/-
**Subgroup.leftCoset_cover_const_iff_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：leftCoset_cover_const_iff_surjOn : ⋃ i in s, g i • (H : Set G) = Set.univ 
↔ Set.SurjOn (g · : ι -> G ⧸ H) s Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem leftCoset_cover_const_iff_surjOn :
    ⋃ i ∈ s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι → G ⧸ H) s Set.univ := by
  simp [Set.eq_univ_iff_forall, mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

variable (hcovers : ⋃ i ∈ s, g i • (H : Set G) = Set.univ)
include hcovers

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
@[to_additive]
/-
**Subgroup.finiteIndex_of_leftCoset_cover_const** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：finiteIndex_of_leftCoset_cover_const : H.FiniteIndex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `Set.Finite.of_surjOn`：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β
} (f : α → β), Set.SurjOn f s t → s.Finite → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H

--- 原说明 ---
If `H` is a subgroup of `G` and `G` is the union of a finite family of left cose
ts of `H`
then `H` has finite index.
-/
theorem finiteIndex_of_leftCoset_cover_const : H.FiniteIndex := by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]
/-
**Subgroup.index_le_of_leftCoset_cover_const** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：index_le_of_leftCoset_cover_const : H.index <= s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.surjOn_iff_surjective`：surjOn_iff_surjective : SurjOn f s univ ↔ Sur
jective (s.domRestrict f)
· 使用定理 `Subgroup.leftCoset_cover_const_iff_surjOn`：leftCoset_cover_const_iff_sur
jOn : ⋃ i in s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι -> G ⧸ H) s S
et.univ
· 使用引理 `Nat.card_eq_finsetCard`：card_eq_finsetCard (s : Finset α) : Nat.card s =
 s.card
-/
theorem index_le_of_leftCoset_cover_const : H.index ≤ s.card := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]
/-
**Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq** 是 Mathlib 中的一个定理
，位于命名空间 `Subgroup`。
形式化陈述：pairwiseDisjoint_leftCoset_cover_const_of_index_eq (hind : H.index = s.car
d) : Set.PairwiseDisjoint s (g · • (H : Set G))
参数：hind : H.index = s.card。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_ne_univ`：empty_ne_univ [Nonempty α] : (∅ : Set α) != univ
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.set_biUnion_coe`：set_biUnion_coe (s : Finset α) (t : α -> Set β) 
: ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Fintype.bijective_iff_surjective_and_card`：bijective_iff_surjective_and_
card (f : α -> β) : Bijective f ↔ Surjective f ∧ card α = card β
· 使用定理 `Set.surjOn_iff_surjective`：surjOn_iff_surjective : SurjOn f s univ ↔ Sur
jective (s.domRestrict f)
· 使用定理 `Subgroup.leftCoset_cover_const_iff_surjOn`：leftCoset_cover_const_iff_sur
jOn : ⋃ i in s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι -> G ⧸ H) s S
et.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_leftCoset_iff`：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
-/
theorem pairwiseDisjoint_leftCoset_cover_const_of_index_eq (hind : H.index = s.card) :
    Set.PairwiseDisjoint s (g · • (H : Set G)) := by
  have : Fintype (G ⧸ H) := fintypeOfIndexNeZero fun h => by
    rw [hind, Finset.card_eq_zero] at h
    rw [h, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  suffices Function.Bijective (g · : s → G ⧸ H) by
    intro i hi j hj h' c hi' hj' x hx
    specialize hi' hx
    specialize hj' hx
    rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hi' hj'
    rw [ne_eq, ← Subtype.mk.injEq (p := (· ∈ (s : Set ι))) i hi j hj] at h'
    exact h' <| this.injective <| by simp only [hi', hj']
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rwa [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
  · simp only [Fintype.card_coe, ← hind, index_eq_card, Nat.card_eq_fintype_card]

end leftCoset_cover_const

section

variable {ι : Type*} {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (g i) • (H i : Set G) = Set.univ)
include hcovers

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
@[to_additive]
/-
**Subgroup.exists_finiteIndex_of_leftCoset_cover_aux** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup`。
形式化陈述：exists_finiteIndex_of_leftCoset_cover_aux [DecidableEq (Subgroup G)] (j : 
ι) (hj : j in s) (hcovers' : ⋃ i in s.filter (H · = H j), g i • (H i : Set G) !=
 Set.univ) : exists i in s, H i != H j ∧ (H i).FiniteIndex
参数：Subgroup G；j : ι；hj : j in s；hcovers' : ⋃ i in s.filter (H · = H j), g i • (H
 i : Set G) != Set.univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq`：∀ {α : Sort u_1} {a' : α}, ∃ a, a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_leftCoset_iff`：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.iUnion₂_eq_univ_iff`：iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α
} : ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
（共 47 条，此处仅展示前 30 条）
-/
theorem exists_finiteIndex_of_leftCoset_cover_aux [DecidableEq (Subgroup G)]
    (j : ι) (hj : j ∈ s) (hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i ∈ s, H i ≠ H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨n, hn⟩ : ∃ n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i ∈ s, H i = H j → (g i : G ⧸ H i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : ∀ (y : G), y • (H j : Set G) ⊆
        ⋃ i ∈ s.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      simp_rw [Finset.mem_filter, Set.mem_iUnion]
      have ⟨i, hi, hmem⟩ : ∃ i ∈ s, x * (y⁻¹ * z) ∈ g i • (H i : Set G) := by
        simpa using Set.eq_univ_iff_forall.mp hcovers (x * (y⁻¹ * z))
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hmem
      refine ⟨i, ⟨hi, fun hij => hx i hi hij ?_⟩, ?_⟩
      · rwa [hmem, eq_comm, QuotientGroup.eq, hij, inv_mul_cancel_left,
          ← SetLike.mem_coe, ← mem_leftCoset_iff]
      · simpa [mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hmem
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(s.filter (H · ≠ H j)) × Option ↥(s.filter (H · = H j))
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩ => g k₁
    let K (k : κ) : Subgroup G := H k.1.val
    have hK' (k : κ) : K k ∈ (s.image H).erase (H j) := by
      have := Finset.mem_filter.mp k.1.property
      exact Finset.mem_erase.mpr ⟨this.2, Finset.mem_image_of_mem H this.1⟩
    have hK (k : κ) : K k ≠ H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    replace hcovers : ⋃ k ∈ Finset.univ, f k • (K k : Set G) = Set.univ :=
        Set.iUnion₂_eq_univ_iff.mpr fun y => by
      rw [← s.filter_union_filter_not_eq (H · = H j), Finset.set_biUnion_union] at hcovers
      cases (Set.mem_union _ _ _).mp (hcovers.superset (Set.mem_univ y)) with
      | inl hy =>
        have ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
        have hk' : H k = H j := And.right <| by simpa using hk
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hx (g k) (hk' ▸ hy))
        exact ⟨⟨⟨i, hi⟩, some ⟨k, hk⟩⟩, Finset.mem_univ _, hy⟩
      | inr hy =>
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨⟨⟨i, hi⟩, none⟩, Finset.mem_univ _, hy⟩
    -- Let `H k` be one of the subgroups in this covering.
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty] at hcovers
      exact Set.empty_ne_univ hcovers
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcovers' : ⋃ i ∈ Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
      exact ⟨k.1, Finset.mem_of_mem_filter k.1.1 k.1.2, hK k,
        finiteIndex_of_leftCoset_cover_const hcovers'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn' : (Finset.univ.image K).card < n := hn ▸ by
      refine ((Finset.card_le_card fun x => ?_).trans_lt <|
        Finset.card_erase_lt_of_mem (Finset.mem_image_of_mem H hj))
      rw [mem_image_univ_iff_mem_range, Set.mem_range]
      exact fun ⟨k, hk⟩ => hk ▸ hK' k
    have ⟨k', hk'⟩ := ih _ hn' hcovers k (Finset.mem_univ k) hcovers' rfl
    exact ⟨k'.1.1, Finset.mem_of_mem_filter k'.1.1 k'.1.2, hK k', hk'.2.2⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
@[to_additive]
/-
**Subgroup.exists_finiteIndex_of_leftCoset_cover** 是 Mathlib 中的一个定理，位于命名空间 `Subg
roup`。
形式化陈述：exists_finiteIndex_of_leftCoset_cover : exists k in s, (H k).FiniteIndex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.empty_ne_univ`：empty_ne_univ [Nonempty α] : (∅ : Set α) != univ
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.set_biUnion_coe`：set_biUnion_coe (s : Finset α) (t : α -> Set β) 
: ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x
· 使用定理 `Subgroup.finiteIndex_of_leftCoset_cover_const`：finiteIndex_of_leftCoset_
cover_const : H.FiniteIndex
· 使用引理 `Set.iUnion₂_congr`：iUnion₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋃ (i) (j), s i j = ⋃ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subgroup.exists_finiteIndex_of_leftCoset_cover_aux`：exists_finiteIndex_o
f_leftCoset_cover_aux [DecidableEq (Subgroup G)] (j : ι) (hj : j in s) (hcovers'
 : ⋃ i in s.filter (H · = H j), g i • (H…

--- 原说明 ---
Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`.
-/
theorem exists_finiteIndex_of_leftCoset_cover : ∃ k ∈ s, (H k).FiniteIndex := by
  classical
  have ⟨j, hj⟩ : s.Nonempty := by
    by_contra! rfl
    rw [← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  by_cases hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
    exact ⟨j, hj, finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, hi, _, hfi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers j hj hcovers'
    exact ⟨i, hi, hfi⟩

-- Auxiliary to `leftCoset_cover_filter_FiniteIndex` and `one_le_sum_inv_index_of_leftCoset_cover`.
@[to_additive]
/-
**Subgroup.leftCoset_cover_filter_FiniteIndex_aux** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：leftCoset_cover_filter_FiniteIndex_aux [DecidablePred (FiniteIndex : Subgr
oup G -> Prop)] : (⋃ k in s.filter (fun i => (H i).FiniteIndex), g k • (H k : Se
t G) = Set.univ) ∧ (1 <= ∑ i in s, ((H i).index : Rat)⁻¹) ∧ (∑ i in s, ((H i).in
dex : Rat)⁻¹ = 1 -> Set.PairwiseDisjoint (s.filter (fun i => (H i).FiniteIndex))
 (fun i => g i • (H i : Set G)))
参数：FiniteIndex : Subgroup G -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.finiteIndex_iInf'`：finiteIndex_iInf' {ι : Type*} {s : Finset ι}
 (f : ι -> Subgroup G) (hs : forall i in s, (f i).FiniteIndex) : (⨅ i in s, f i)
.FiniteIndex
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
· 使用定理 `Finset.set_biUnion_union`：set_biUnion_union (s t : Finset α) (u : α -> S
et β) : ⋃ x in s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Set.iUnion_sigma`：iUnion_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) :
 ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用引理 `Set.iUnion_congr`：iUnion_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋃ i, s i = ⋃ i, t i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 119 条，此处仅展示前 30 条）
-/
theorem leftCoset_cover_filter_FiniteIndex_aux
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    (⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ) ∧
      (1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹) ∧
      (∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 → Set.PairwiseDisjoint
        (s.filter (fun i => (H i).FiniteIndex)) (fun i ↦ g i • (H i : Set G))) := by
  classical
  let D := ⨅ k ∈ s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := finiteIndex_iInf' _ <| by simp
  have hD_le {i} (hi : i ∈ s) (hfi : (H i).FiniteIndex) : D ≤ H i :=
    iInf₂_le i (Finset.mem_filter.mpr ⟨hi, hfi⟩)
  -- Each subgroup of finite index in the covering is the union of finitely many cosets of `D`.
  choose t ht using fun i hi hfi =>
    exists_leftTransversal_of_FiniteIndex (H := H i) (hD_le hi hfi)
  -- We construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : s) × { x // x ∈ if h : (H i.1).FiniteIndex then t i.1 i.2 h else {1} }
  let f (k : κ) : G := g k.1 * k.2.val
  let K (k : κ) : Subgroup G := if (H k.1).FiniteIndex then D else H k.1
  have hcovers' : ⋃ k ∈ Finset.univ, f k • (K k : Set G) = Set.univ := by
    rw [← s.filter_union_filter_not_eq (fun i => (H i).FiniteIndex)] at hcovers
    rw [← hcovers, ← Finset.univ.filter_union_filter_not_eq (fun k => (H k.1).FiniteIndex),
      Finset.set_biUnion_union, Finset.set_biUnion_union]
    apply congrArg₂ (· ∪ ·) <;> rw [Set.iUnion_sigma, Set.iUnion_subtype] <;>
        refine Set.iUnion_congr fun i => ?_
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [← Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc, f, K, ht, hfi]
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hfi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨k, hkfi, hk⟩ : ∃ k, (H k.1.1).FiniteIndex ∧ K k = D :=
    have ⟨j, hj, hjfi⟩ := exists_finiteIndex_of_leftCoset_cover hcovers
    have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_coe_sort.mp
      (ht j hj hjfi).1.leftQuotientEquiv.symm.nonempty
    ⟨⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩, hjfi, if_pos hjfi⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' : ⋃ i ∈ Finset.univ.filter (K · = D), f i • (D : Set G) = Set.univ := by
    rw [← hk, Set.iUnion₂_congr fun i hi => by rw [← (Finset.mem_filter.mp hi).2]]
    by_contra! h
    obtain ⟨i, -, hi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k) h
    by_cases hfi : (H i.1.1).FiniteIndex <;> simp [K, hfi, hkfi] at hi
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  have hHD (i) : ¬(H i).FiniteIndex → H i ≠ D := fun hfi hD' => (hD' ▸ hfi) hD
  have hdensity : ∑ i ∈ s, ((H i).index : ℚ)⁻¹ =
      (Finset.univ.filter (K · = D)).card * (D.index : ℚ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero), Finset.sum_mul,
      ← Finset.sum_attach, eq_comm, Finset.card_filter, Nat.cast_sum, ← Finset.univ_sigma_univ,
      Finset.sum_sigma, Finset.sum_coe_sort_eq_attach]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hfi : (H i).FiniteIndex
    · rw [← relIndex_mul_index (hD_le i.2 hfi), Nat.cast_mul, mul_comm,
        mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hfi.index_ne_zero)]
      simpa [K, hfi] using! (ht i.1 i.2 hfi).1.card_left
    · rw [of_not_not (FiniteIndex.mk.mt hfi), Nat.cast_zero, inv_zero, zero_mul]
      simpa [K, hfi] using! hHD i hfi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
    refine Set.iUnion_congr fun i => ?_
    rw [Finset.mem_filter, Set.iUnion_and]
    refine Set.iUnion_congr fun hi => ?_
    by_cases hfi : (H i).FiniteIndex <;>
      simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc,
        f, K, hHD, ← (ht i hi _).2, hfi]
  · rw [hdensity]
    refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD.index_ne_zero))
    rw [one_mul, mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero), mul_one,
      Nat.cast_le]
    exact index_le_of_leftCoset_cover_const hcovers'
  · rw [hdensity, mul_inv_eq_one₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero),
      Nat.cast_inj, Finset.coe_filter]
    intro h i hi j hj hij c hi' hj' x hx
    have hdisjoint := pairwiseDisjoint_leftCoset_cover_const_of_index_eq hcovers' h.symm
    -- We know the `f k • K k` are pairwise disjoint and need to prove that the `g i • H i` are.
    rw [Set.mem_ofPred_eq] at hi hj
    have hk' (i) (hi : i ∈ s ∧ (H i).FiniteIndex) (hi' : c ≤ g i • (H i : Set G)) :
        ∃ (k : κ), k.1.1 = i ∧ K k = D ∧ x ∈ f k • (D : Set G) := by
      rw [← (ht i hi.1 hi.2).2] at hi'
      suffices ∃ r : H i, r ∈ t i hi.1 hi.2 ∧ x ∈ (g i * r) • (D : Set G) by
        have ⟨r, hr, hxr⟩ := this
        refine ⟨⟨⟨i, hi.1⟩, ⟨r, dif_pos hi.2 ▸ hr⟩⟩, rfl, ?_⟩
        simpa [K, f, if_pos hi.2] using! hxr
      simpa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_assoc] using! hi' hx
    have ⟨k₁, hik₁, hk₁, hxk₁⟩ := hk' i hi hi'
    have ⟨k₂, hjk₂, hk₂, hxk₂⟩ := hk' j hj hj'
    rw [← Set.singleton_subset_iff] at hxk₁ hxk₂ ⊢
    exact hdisjoint
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₁, hk₁⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₂, hk₂⟩)
      (ne_of_apply_ne Sigma.fst (ne_of_apply_ne Subtype.val (hik₁ ▸ hjk₂ ▸ hij)))
      hxk₁ hxk₂

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
@[to_additive]
/-
**Subgroup.leftCoset_cover_filter_FiniteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：leftCoset_cover_filter_FiniteIndex [DecidablePred (FiniteIndex : Subgroup 
G -> Prop)] : ⋃ k in s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) 
= Set.univ
参数：FiniteIndex : Subgroup G -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.leftCoset_cover_filter_FiniteIndex_aux`：leftCoset_cover_filter_
FiniteIndex_aux [DecidablePred (FiniteIndex : Subgroup G -> Prop)] : (⋃ k in s.f
ilter (fun i => (H i).FiniteIndex), g…

--- 原说明 ---
Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering.
-/
theorem leftCoset_cover_filter_FiniteIndex
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`. Then the
sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
@[to_additive one_le_sum_inv_index_of_leftCoset_cover]
/-
**Subgroup.one_le_sum_inv_index_of_leftCoset_cover** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
形式化陈述：one_le_sum_inv_index_of_leftCoset_cover : 1 <= ∑ i in s, ((H i).index : Ra
t)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subgroup.leftCoset_cover_filter_FiniteIndex_aux`：leftCoset_cover_filter_
FiniteIndex_aux [DecidablePred (FiniteIndex : Subgroup G -> Prop)] : (⋃ k in s.f
ilter (fun i => (H i).FiniteIndex), g…

--- 原说明 ---
Let the group `G` be the union of finitely many left cosets `g i • H i`. Then th
e
sum of the inverses of the indexes of the subgroups `H i` is greater than or equ
al to 1.
-/
theorem one_le_sum_inv_index_of_leftCoset_cover :
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ :=
  have := Classical.decPred (FiniteIndex : Subgroup G → Prop)
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
If the sum of the inverses of the indexes of the subgroups `H i` is equal to 1,
then the cosets of the subgroups of finite index are pairwise disjoint. -/
@[to_additive]
/-
**Subgroup.pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one** 是 Mathlib 
中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one [DecidablePred (F
initeIndex : Subgroup G -> Prop)] : ∑ i in s, ((H i).index : Rat)⁻¹ = 1 -> Set.P
airwiseDisjoint (s.filter (fun i => (H i).FiniteIndex)) (fun i => g i • (H i : S
et G))
参数：FiniteIndex : Subgroup G -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subgroup.leftCoset_cover_filter_FiniteIndex_aux`：leftCoset_cover_filter_
FiniteIndex_aux [DecidablePred (FiniteIndex : Subgroup G -> Prop)] : (⋃ k in s.f
ilter (fun i => (H i).FiniteIndex), g…

--- 原说明 ---
Let the group `G` be the union of finitely many left cosets `g i • H i`.
If the sum of the inverses of the indexes of the subgroups `H i` is equal to 1,
then the cosets of the subgroups of finite index are pairwise disjoint.
-/
theorem pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    ∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 →
      Set.PairwiseDisjoint (s.filter (fun i => (H i).FiniteIndex))
        (fun i ↦ g i • (H i : Set G)) :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

/-- B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
@[to_additive]
/-
**Subgroup.exists_index_le_card_of_leftCoset_cover** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
形式化陈述：exists_index_le_card_of_leftCoset_cover : exists i in s, (H i).FiniteIndex
 ∧ (H i).index <= s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Subgroup.one_le_sum_inv_index_of_leftCoset_cover`：one_le_sum_inv_index_o
f_leftCoset_cover : 1 <= ∑ i in s, ((H i).index : Rat)⁻¹
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Finset.sum_lt_sum_of_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → 
M} {s : Finset ι} […
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets.
-/
theorem exists_index_le_card_of_leftCoset_cover :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_gt
  cases s.eq_empty_or_nonempty with
  | inl hs => simp only [hs, Finset.sum_empty, zero_lt_one]
  | inr hs =>
  have hs' : 0 < s.card := hs.card_pos
  have hlt : ∀ i ∈ s, ((H i).index : ℚ)⁻¹ < (s.card : ℚ)⁻¹ := fun i hi ↦ by
    cases eq_or_ne (H i).index 0 with
    | inl hindex =>
      rwa [hindex, Nat.cast_zero, inv_zero, inv_pos, Nat.cast_pos]
    | inr hindex =>
      exact inv_strictAnti₀ (by exact_mod_cast hs') (by exact_mod_cast h i hi ⟨hindex⟩)
  apply (Finset.sum_lt_sum_of_nonempty hs hlt).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hs'.ne')]

end

end Subgroup

section Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : ι → Submodule R M} {s : Finset ι}

/-
**Submodule.exists_finiteIndex_of_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_finiteIndex_of_cover (hcovers : ⋃ i in s, (p i : Set M) =
 Set.univ) : exists k in s, (p k).toAddSubgroup.FiniteIndex
参数：hcovers : ⋃ i in s, (p i : Set M) = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `AddSubgroup.exists_finiteIndex_of_leftCoset_cover`：∀ {G : Type u_1} [ins
t : AddGroup G] {ι : Type u_2} {H : ι → AddSubgroup G} {g : ι → G} {s : Finset ι
},   ⋃ i ∈ s, g i +ᵥ ↑(H i) = Set.univ …
-/
theorem Submodule.exists_finiteIndex_of_cover (hcovers : ⋃ i ∈ s, (p i : Set M) = Set.univ) :
    ∃ k ∈ s, (p k).toAddSubgroup.FiniteIndex :=
  have hcovers' : ⋃ i ∈ s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using! hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

end Submodule

section Subspace

variable {k E : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E]
    {s : Finset (Subspace k E)}

/-- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
/-
**Subspace.biUnion_ne_univ_of_top_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subspace.biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) : ⋃ p in s, (p : Set E
) != Set.univ
参数：hs : ⊤ ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_finiteIndex_of_cover`：Submodule.exists_finiteIndex_of_c
over (hcovers : ⋃ i in s, (p i : Set M) = Set.univ) : exists k in s, (p k).toAdd
Subgroup.FiniteIndex
· 使用定理 `AddSubgroup.finite_quotient_of_finiteIndex`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [H.FiniteIndex], Finite (G ⧸ H)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Module.Free.infinite`：infinite [Infinite R] [Nontrivial M] : Infinite M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False

--- 原说明 ---
A vector space over an infinite field cannot be a finite union of proper subspac
es.
-/
theorem Subspace.biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) : ⋃ p ∈ s, (p : Set E) ≠ Set.univ := by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (E ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr (ne_of_mem_of_not_mem hp hs)
  have : Infinite (E ⧸ p) := Module.Free.infinite k (E ⧸ p)
  exact not_finite (E ⧸ p)

/-- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
/-
**Subspace.top_mem_of_biUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subspace.top_mem_of_biUnion_eq_univ (hcovers : ⋃ p in s, (p : Set E) = Set
.univ) : ⊤ in s
参数：hcovers : ⋃ p in s, (p : Set E) = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Subspace.biUnion_ne_univ_of_top_notMem`：Subspace.biUnion_ne_univ_of_top_
notMem (hs : ⊤ ∉ s) : ⋃ p in s, (p : Set E) != Set.univ

--- 原说明 ---
A vector space over an infinite field cannot be a finite union of proper subspac
es.
-/
theorem Subspace.top_mem_of_biUnion_eq_univ (hcovers : ⋃ p ∈ s, (p : Set E) = Set.univ) :
    ⊤ ∈ s := by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_top_notMem hcovers
/-
**Subspace.exists_eq_top_of_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subspace.exists_eq_top_of_iUnion_eq_univ {ι} [Finite ι] {p : ι -> Subspace
 k E} (hcovers : ⋃ i, (p i : Set E) = Set.univ) : exists i, p i = ⊤
参数：hcovers : ⋃ i, (p i : Set E) = Set.univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Subspace.top_mem_of_biUnion_eq_univ`：Subspace.top_mem_of_biUnion_eq_univ
 (hcovers : ⋃ p in s, (p : Set E) = Set.univ) : ⊤ in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
-/
theorem Subspace.exists_eq_top_of_iUnion_eq_univ {ι} [Finite ι] {p : ι → Subspace k E}
    (hcovers : ⋃ i, (p i : Set E) = Set.univ) : ∃ i, p i = ⊤ := by
  have := Fintype.ofFinite (Set.range p)
  simp_rw [← Set.biUnion_range (f := p), ← Set.mem_toFinset] at hcovers
  apply Set.mem_toFinset.mp (Subspace.top_mem_of_biUnion_eq_univ hcovers)

end Subspace

