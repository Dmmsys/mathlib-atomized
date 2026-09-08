/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Results using cardinal arithmetic

This file contains results using cardinal arithmetic that are not in the main cardinal theory files.
It has been separated out to not burden `Mathlib/Data/Set/Card.lean` with extra imports.

## Main results

- `exists_union_disjoint_ncard_eq_of_even`: Given a set `s` with an even cardinality, there exist
  disjoint sets `t` and `u` such that `t ∪ u = s` and `t.ncard = u.ncard`.
- `exists_union_disjoint_cardinal_eq_iff` is the same, except using cardinal notation.
-/

public section

variable {α ι : Type*}

open scoped Finset

/-
**Finset.exists_disjoint_union_of_even_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_disjoint_union_of_even_card [DecidableEq α] {s : Finset α} (
he : Even #s) : exists (t u : Finset α), t union u = s ∧ Disjoint t u ∧ #t = #u
参数：he : Even #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_sdiff_self_eq_union`：union_sdiff_self_eq_union : s union t 
\ s = s union t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Finset.exists_disjoint_union_of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) :
    ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n ≤ #s by lia)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩
/-
**Finset.exists_disjoint_union_of_even_card_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_disjoint_union_of_even_card_iff [DecidableEq α] (s : Finset 
α) : Even #s ↔ exists (t u : Finset α), t union u = s ∧ Disjoint t u ∧ #t = #u
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_disjoint_union_of_even_card`：Finset.exists_disjoint_union_
of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) : exists (t u : Finse
t α), t union u = s ∧ Disjoint …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Finset.exists_disjoint_union_of_even_card_iff [DecidableEq α] (s : Finset α) :
    Even #s ↔ ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩

@[simp]
/-
**finsum_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finsum_one {s : Set α} : ∑ᶠ i in s, 1 = s.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_or_finite`：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finsum_mem_eq_zero_of_infinite`：∀ {α : Type u_1} {M : Type u_5} [inst : 
AddCommMonoid M] {f : α → M} {s : Set α},   (s ∩ Function.support f).Infinite → 
∑ᶠ (i : α) (_ : i ∈ …
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finsum_mem_eq_finite_toFinset_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] (f : α → M) {s : Set α} (hs : s.Finite),   ∑ᶠ (i : α) (_ : i
 ∈ s), f i = ∑ i ∈ hs.t…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
-/
lemma finsum_one {s : Set α} : ∑ᶠ i ∈ s, 1 = s.ncard := by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.ncard]
    by_cases h : 1 = 0
    · simp [h]
    · exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const h])
  · simp [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]

namespace Finset

/-
**Finset.set_ncard_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：set_ncard_biUnion_le (t : Finset ι) (s : ι -> Set α) : (⋃ i in t, s i).nca
rd <= ∑ i in t, (s i).ncard
参数：t : Finset ι；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_union_le_sum`：apply_union_le_sum [AddCommMonoid β] [Preorde
r β] [AddLeftMono β] {f : Set α -> β} (zero : f ∅ = 0) (ih : forall {s t}, f (s 
union t) <= f s…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ncard_union_le`：ncard_union_le (s t : Set α) : (s union t).ncard <= 
s.ncard + t.ncard
-/
lemma set_ncard_biUnion_le (t : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ t, s i).ncard ≤ ∑ i ∈ t, (s i).ncard :=
  t.apply_union_le_sum (by simp) (Set.ncard_union_le _ _)
/-
**Finset.set_encard_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：set_encard_biUnion_le (t : Finset ι) (s : ι -> Set α) : (⋃ i in t, s i).en
card <= ∑ i in t, (s i).encard
参数：t : Finset ι；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_union_le_sum`：apply_union_le_sum [AddCommMonoid β] [Preorde
r β] [AddLeftMono β] {f : Set α -> β} (zero : f ∅ = 0) (ih : forall {s t}, f (s 
union t) <= f s…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.encard_union_le`：encard_union_le (s t : Set α) : (s union t).encard 
<= s.encard + t.encard
-/
lemma set_encard_biUnion_le (t : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ t, s i).encard ≤ ∑ i ∈ t, (s i).encard :=
  t.apply_union_le_sum (by simp) (Set.encard_union_le _ _)

end Finset

namespace Set

variable {s : Set α}

open Cardinal

/-
**Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite** 是 Mathlib 中的一个定理，
位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Infinite → ∃ t u, t ∪ u = s ∧ Disjoint t u
 ∧ Cardinal.mk ↑t = Cardinal.mk ↑u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用定理 `Cardinal.add_def`：add_def (α β : Type u) : #α + #β = #(α oplus β)
· 使用定理 `Cardinal.add_mk_eq_self`：add_mk_eq_self {α : Type*} [Infinite α] : #α + 
#α = #α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_inl_union_range_inr`：range_inl_union_range_inr : range (Sum.in
l : α -> α oplus β) union range Sum.inr = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_image_eq`：mk_image_eq {α β : Type u} {f : α -> β} {s : Set α
} (hf : Injective f) : #(f '' s) = #s
· 使用定理 `Cardinal.mk_preimage_equiv`：mk_preimage_equiv (f : α ≃ β) (s : Set β) : 
#(f ⁻¹' s) = #s
· 使用定理 `Cardinal.mk_range_inl`：mk_range_inl {α : Type u} {β : Type v} : #(range 
(@Sum.inl α β)) = lift.{v} #α
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_range_inr`：mk_range_inr {α : Type u} {β : Type v} : #(range 
(@Sum.inr α β)) = lift.{u} #β
-/
theorem Infinite.exists_union_disjoint_cardinal_eq_of_infinite (h : s.Infinite) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s ⊕ s) := by
    rw [← Cardinal.eq, ← add_def, add_mk_eq_self]
  refine ⟨Subtype.val '' f ⁻¹' (range .inl), Subtype.val '' f ⁻¹' (range .inr), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injective Subtype.val_injective
      (isCompl_range_inl_range_inr.disjoint.preimage f)
  · simp [mk_image_eq Subtype.val_injective]
/-
**Set.exists_union_disjoint_cardinal_eq_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_union_disjoint_cardinal_eq_of_even (he : Even s.ncard) : exists (t 
u : Set α), t union u = s ∧ Disjoint t u ∧ #t = #u
参数：he : Even s.ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_or_finite`：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finit
e
· 使用定理 `Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite`：∀ {α : Type 
u_1} {s : Set α}, s.Infinite → ∃ t u, t ∪ u = s ∧ Disjoint t u ∧ Cardinal.mk ↑t 
= Cardinal.mk ↑u
· 使用定理 `Finset.exists_disjoint_union_of_even_card`：Finset.exists_disjoint_union_
of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) : exists (t u : Finse
t α), t union u = s ∧ Disjoint …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_eq_toFinset_card`：ncard_eq_toFinset_card (s : Set α) (hs : s.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_union_disjoint_cardinal_eq_of_even (he : Even s.ncard) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  obtain hs | hs := s.infinite_or_finite
  · exact hs.exists_union_disjoint_cardinal_eq_of_infinite
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t, u
  simp [← Finset.coe_union, *]
/-
**Set.exists_union_disjoint_ncard_eq_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) : exists (t u :
 Set α), t union u = s ∧ Disjoint t u ∧ t.ncard = u.ncard
参数：he : Even s.ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_union_disjoint_cardinal_eq_of_even`：exists_union_disjoint_car
dinal_eq_of_even (he : Even s.ncard) : exists (t u : Set α), t union u = s ∧ Dis
joint t u ∧ #t = #u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩
/-
**Set.exists_union_disjoint_cardinal_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_union_disjoint_cardinal_eq_iff (s : Set α) : Even (s.ncard) ↔ exist
s (t u : Set α), t union u = s ∧ Disjoint t u ∧ #t = #u
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_union_disjoint_cardinal_eq_of_even`：exists_union_disjoint_car
dinal_eq_of_even (he : Even s.ncard) : exists (t u : Set α), t union u = s ∧ Dis
joint t u ∧ #t = #u
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_union_eq`：ncard_union_eq (h : Disjoint s t) (hs : s.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.finite_union`：finite_union {s t : Set α} : (s union t).Finite ↔ s.Fi
nite ∧ t.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Even.add_self`：∀ {α : Type u_2} [inst : Add α] (r : α), Even (r + r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Infinite.ncard`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.ncard =
 0
-/
theorem exists_union_disjoint_cardinal_eq_iff (s : Set α) :
    Even (s.ncard) ↔ ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t ∪ u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2, hn]
    exact Even.add_self u.ncard
  · simp [hnfin.ncard]

open scoped Function
/-
**Set.Finite.ncard_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},   t.Finite →     ∀ {s : ι → S
et α},       (∀ i ∈ t, (s i).Finite) → t.PairwiseDisjoint s → (⋃ i ∈ t, s i).nca
rd = ∑ᶠ (i : ι) (_ : i ∈ t), (s i).ncard
参数：∀ i ∈ t, (s i).Finite；⋃ i ∈ t, s i；i : ι；_ : i ∈ t；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `finsum_one`：finsum_one {s : Set α} : ∑ᶠ i in s, 1 = s.ncard
· 使用定理 `finsum_mem_biUnion`：∀ {α : Type u_1} {ι : Type u_3} {M : Type u_5} [inst
 : AddCommMonoid M] {f : α → M} {I : Set ι} {t : ι → Set α},   I.PairwiseDisjoin
t t →   …
· 使用定理 `finsum_mem_congr`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid 
M] {f g : α → M} {s t : Set α},   s = t → (∀ x ∈ t, f x = g x) → ∑ᶠ (i : α) (_ :
 i ∈ s…
-/
lemma Finite.ncard_biUnion {t : Set ι} (ht : t.Finite) {s : ι → Set α} (hs : ∀ i ∈ t, (s i).Finite)
    (h : t.PairwiseDisjoint s) : (⋃ i ∈ t, s i).ncard = ∑ᶠ i ∈ t, (s i).ncard := by
  rw [← finsum_one, finsum_mem_biUnion h ht hs, finsum_mem_congr rfl fun i hi ↦ finsum_one]
/-
**Set.ncard_iUnion_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_iUnion_of_finite [Finite ι] {s : ι -> Set α} (hs : forall i, (s i).F
inite) (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i : ι, (s i).ncard
参数：hs : forall i, (s i).Finite；h : Pairwise (Disjoint on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_mem_univ`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M
] (f : α → M),   ∑ᶠ (i : α) (_ : i ∈ Set.univ), f i = ∑ᶠ (i : α), f i
· 使用定理 `Set.Finite.ncard_biUnion`：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},  
 t.Finite →     ∀ {s : ι → Set α},       (∀ i ∈ t, (s i).Finite) → t.PairwiseDis
joint s → (⋃ i…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ncard_iUnion_of_finite [Finite ι] {s : ι → Set α} (hs : ∀ i, (s i).Finite)
    (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i : ι, (s i).ncard := by
  rw [← finsum_mem_univ, ← finite_univ.ncard_biUnion (by simpa) (fun _ _ _ _ hab ↦ h hab)]
  simp
/-
**Set.Finite.encard_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},   t.Finite → ∀ {s : ι → Set α
}, t.PairwiseDisjoint s → (⋃ i ∈ t, s i).encard = ∑ᶠ (i : ι) (_ : i ∈ t), (s i).
encard
参数：⋃ i ∈ t, s i；i : ι；_ : i ∈ t；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.Finite.ncard_biUnion`：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},  
 t.Finite →     ∀ {s : ι → Set α},       (∀ i ∈ t, (s i).Finite) → t.PairwiseDis
joint s → (⋃ i…
· 使用定理 `finsum_mem_congr`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid 
M] {f g : α → M} {s t : Set α},   s = t → (∀ x ∈ t, f x = g x) → ∑ᶠ (i : α) (_ :
 i ∈ s…
· 使用引理 `Nat.cast_finsum_mem`：Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M 
: Type*} [AddCommMonoidWithOne M] (f : ι -> Nat) : ↑(∑ᶠ x in s, f x : Nat) = ∑ᶠ 
x in s, (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `finsum_mem_insert`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid
 M] {a : α} {s : Set α} (f : α → M),   a ∉ s → s.Finite → ∑ᶠ (i : α) (_ : i ∈ in
sert a …
· 使用定理 `Set.notMem_sdiff_of_mem`：notMem_sdiff_of_mem {s t : Set α} {x : α} (hx :
 x in t) : x ∉ s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finite.encard_biUnion {t : Set ι} (ht : t.Finite) {s : ι → Set α}
    (hs : t.PairwiseDisjoint s) : (⋃ i ∈ t, s i).encard = ∑ᶠ i ∈ t, (s i).encard := by
  by_cases! h : ∀ i ∈ t, (s i).Finite
  · have : (⋃ i ∈ t, s i).Finite := ht.biUnion (fun i hi ↦ h i hi)
    rw [← this.cast_ncard_eq, ncard_biUnion ht h hs,
      ← finsum_mem_congr rfl fun i hi ↦ (h i hi).cast_ncard_eq, Nat.cast_finsum_mem ht]
  · obtain ⟨i, hi, (hn : (s i).Infinite)⟩ := h
    rw [← Set.insert_sdiff_self_of_mem hi,
      finsum_mem_insert _ (notMem_sdiff_of_mem <| mem_singleton i) ht.sdiff]
    simp [hn]
/-
**Set.encard_iUnion_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_iUnion_of_finite [Finite ι] {s : ι -> Set α} (hs : Pairwise (Disjoi
nt on s)) : (⋃ i, s i).encard = ∑ᶠ i, (s i).encard
参数：hs : Pairwise (Disjoint on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_mem_univ`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M
] (f : α → M),   ∑ᶠ (i : α) (_ : i ∈ Set.univ), f i = ∑ᶠ (i : α), f i
· 使用定理 `Set.Finite.encard_biUnion`：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι}, 
  t.Finite → ∀ {s : ι → Set α}, t.PairwiseDisjoint s → (⋃ i ∈ t, s i).encard = ∑
ᶠ (i : ι) (_ : …
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma encard_iUnion_of_finite [Finite ι] {s : ι → Set α} (hs : Pairwise (Disjoint on s)) :
    (⋃ i, s i).encard = ∑ᶠ i, (s i).encard := by
  rw [← finsum_mem_univ, ← finite_univ.encard_biUnion (fun a _ b _ hab ↦ hs hab)]
  simp
/-
**Set.Finite.ncard_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},   t.Finite → ∀ (s : ι → Set α
), (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ (i : ι) (_ : i ∈ t), (s i).ncard
参数：s : ι → Set α；⋃ i ∈ t, s i；i : ι；_ : i ∈ t；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Finset.set_ncard_biUnion_le`：set_ncard_biUnion_le (t : Finset ι) (s : ι 
-> Set α) : (⋃ i in t, s i).ncard <= ∑ i in t, (s i).ncard
-/
lemma Finite.ncard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι → Set α) :
    (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ i ∈ t, (s i).ncard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_ncard_biUnion_le s
/-
**Set.Finite.encard_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι},   t.Finite → ∀ (s : ι → Set α
), (⋃ i ∈ t, s i).encard ≤ ∑ᶠ (i : ι) (_ : i ∈ t), (s i).encard
参数：s : ι → Set α；⋃ i ∈ t, s i；i : ι；_ : i ∈ t；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Finset.set_encard_biUnion_le`：set_encard_biUnion_le (t : Finset ι) (s : 
ι -> Set α) : (⋃ i in t, s i).encard <= ∑ i in t, (s i).encard
-/
lemma Finite.encard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι → Set α) :
    (⋃ i ∈ t, s i).encard ≤ ∑ᶠ i ∈ t, (s i).encard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_encard_biUnion_le s
/-
**Set.ncard_iUnion_le_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_iUnion_le_of_fintype [Fintype ι] (s : ι -> Set α) : (⋃ i, s i).ncard
 <= ∑ i, (s i).ncard
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用引理 `Finset.set_ncard_biUnion_le`：set_ncard_biUnion_le (t : Finset ι) (s : ι 
-> Set α) : (⋃ i in t, s i).ncard <= ∑ i in t, (s i).ncard
-/
lemma ncard_iUnion_le_of_fintype [Fintype ι] (s : ι → Set α) :
    (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard := by
  simpa using Finset.univ.set_ncard_biUnion_le s
/-
**Set.encard_iUnion_le_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_iUnion_le_of_fintype [Fintype ι] (s : ι -> Set α) : (⋃ i, s i).enca
rd <= ∑ i, (s i).encard
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用引理 `Finset.set_encard_biUnion_le`：set_encard_biUnion_le (t : Finset ι) (s : 
ι -> Set α) : (⋃ i in t, s i).encard <= ∑ i in t, (s i).encard
-/
lemma encard_iUnion_le_of_fintype [Fintype ι] (s : ι → Set α) :
    (⋃ i, s i).encard ≤ ∑ i, (s i).encard := by
  simpa using Finset.univ.set_encard_biUnion_le s
/-
**Set.ncard_iUnion_le_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_iUnion_le_of_finite [Finite ι] (s : ι -> Set α) : (⋃ i, s i).ncard <
= ∑ᶠ i, (s i).ncard
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `finsum_true`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : True → M), ∑
ᶠ (i : True), f i = f trivial
· 使用定理 `Set.Finite.ncard_biUnion_le`：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι}
,   t.Finite → ∀ (s : ι → Set α), (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ (i : ι) (_ : i ∈ t),
 (s i).ncard
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma ncard_iUnion_le_of_finite [Finite ι] (s : ι → Set α) :
    (⋃ i, s i).ncard ≤ ∑ᶠ i, (s i).ncard := by
  simpa using finite_univ.ncard_biUnion_le s
/-
**Set.encard_iUnion_le_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_iUnion_le_of_finite [Finite ι] (s : ι -> Set α) : (⋃ i, s i).encard
 <= ∑ᶠ i, (s i).encard
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `finsum_true`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : True → M), ∑
ᶠ (i : True), f i = f trivial
· 使用定理 `Set.Finite.encard_biUnion_le`：∀ {α : Type u_1} {ι : Type u_2} {t : Set ι
},   t.Finite → ∀ (s : ι → Set α), (⋃ i ∈ t, s i).encard ≤ ∑ᶠ (i : ι) (_ : i ∈ t
), (s i).encard
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma encard_iUnion_le_of_finite [Finite ι] (s : ι → Set α) :
    (⋃ i, s i).encard ≤ ∑ᶠ i, (s i).encard := by
  simpa using finite_univ.encard_biUnion_le s

end Set

