/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Preorder.Finite

/-!
# Dissociation and span

This file defines dissociation and span of sets in groups. These are analogs to the usual linear
independence and linear span of sets in a vector space but where the scalars are only allowed to be
`0` or `±1`. In characteristic 2 or 3, the two pairs of concepts are actually equivalent.

## Main declarations

* `MulDissociated`/`AddDissociated`: Predicate for a set to be dissociated.
* `Finset.mulSpan`/`Finset.addSpan`: Span of a finset.
-/

@[expose] public section

variable {α β : Type*} [CommGroup α] [CommGroup β]

section dissociation
variable {s : Set α} {t u : Finset α} {d : Nat} {a : α}
open Set

/-- A set is dissociated iff all its finite subsets have different products.

This is an analog of linear independence in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive /-- A set is dissociated iff all its finite subsets have different sums.

This is an analog of linear independence in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/]
/--
Definition of `MulDissociated` / `MulDissociated` 的定义

English:
definition MulDissociated
  signature: (s : Set α)
  body: {t : Finset α | ↑t subseteq s}.InjOn (∏ x in ·, x)

中文:
定义 MulDissociated
  签名: (s : Set α)
  定义体: {t : Finset α | ↑t subseteq s}.InjOn (∏ x in ·, x)

Depends on / 依赖: Finset, subseteq
-/
def MulDissociated (s : Set α) : Prop := {t : Finset α | ↑t subseteq s}.InjOn (∏ x in ·, x)

/--
lemma `mulDissociated_iff_sum_eq_subsingleton` / 引理 `mulDissociated_iff_sum_eq_subsingleton`

English:
lemma mulDissociated_iff_sum_eq_subsingleton
  proof: ⟨fun hs _ _t ht _u hu => hs ht.1 hu.1 ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu => hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩

中文:
引理 mulDissociated_iff_sum_eq_subsingleton
  证明: ⟨fun hs _ _t ht _u hu => hs ht.1 hu.1 ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu => hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩
-/
@[to_additive] lemma mulDissociated_iff_sum_eq_subsingleton :
    MulDissociated s ↔ forall a, {t : Finset α | ↑t subseteq s ∧ ∏ x in t, x = a}.Subsingleton :=
⟨fun hs _ _t ht _u hu => hs ht.1 hu.1 ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu => hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩

/--
lemma `MulDissociated.subset` / 引理 `MulDissociated.subset`

English:
lemma MulDissociated.subset
  given: {t : Set α} (hst : s subseteq t) (ht : MulDissociated t)
  proof: ht.mono fun _ => hst.trans'

中文:
引理 MulDissociated.subset
  条件: {t : Set α} (hst : s subseteq t) (ht : MulDissociated t)
  证明: ht.mono fun _ => hst.trans'
-/
@[to_additive] lemma MulDissociated.subset {t : Set α} (hst : s subseteq t) (ht : MulDissociated t) :
    MulDissociated s := ht.mono fun _ => hst.trans'

/--
lemma `mulDissociated_empty` / 引理 `mulDissociated_empty`

English:
lemma mulDissociated_empty
  statement: MulDissociated (∅ : Set α)
  proof: by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]

中文:
引理 mulDissociated_empty
  结论: MulDissociated (∅ : Set α)
  证明: by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma mulDissociated_empty : MulDissociated (∅ : Set α) := by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]
/--
lemma `mulDissociated_singleton` / 引理 `mulDissociated_singleton`

English:
lemma mulDissociated_singleton
  statement: MulDissociated ({a} : Set α) ↔ a != 1
  proof: by
  simp [MulDissociated, ofPred_or, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]

中文:
引理 mulDissociated_singleton
  结论: MulDissociated ({a} : Set α) ↔ a != 1
  证明: by
  simp [MulDissociated, ofPred_or, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.coe_subset_singleton, MulDissociated, coe_subset_singleton, ofPred_or, subset_singleton_iff
-/
lemma mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a != 1 := by
  simp [MulDissociated, ofPred_or, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]
/--
lemma `not_mulDissociated` / 引理 `not_mulDissociated`

English:
lemma not_mulDissociated
  proof: by
  grind [MulDissociated, InjOn]

@[to_additive]

中文:
引理 not_mulDissociated
  证明: by
  grind [MulDissociated, InjOn]

@[to_additive]

Depends on / 依赖: MulDissociated
-/
lemma not_mulDissociated :
    ¬ MulDissociated s ↔
      exists t : Finset α, ↑t subseteq s ∧ exists u : Finset α, ↑u subseteq s ∧ t != u ∧ ∏ x in t, x = ∏ x in u, x := by
  grind [MulDissociated, InjOn]

@[to_additive]
/--
lemma `not_mulDissociated_iff_exists_disjoint` / 引理 `not_mulDissociated_iff_exists_disjoint`

English:
lemma not_mulDissociated_iff_exists_disjoint
  proof: by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨t, u, ht, hu, _, htune, htusum⟩ => ⟨t, ht, u, hu, htune, htusum⟩⟩
  rintro ⟨t, ht, u, hu, htu, h⟩
  refine ⟨t \ u, u \ t, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 htu,
    Finset.prod_sdiff_eq_prod_sdiff_iff.2 h⟩ <;> push_cast 

中文:
引理 not_mulDissociated_iff_exists_disjoint
  证明: by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨t, u, ht, hu, _, htune, htusum⟩ => ⟨t, ht, u, hu, htune, htusum⟩⟩
  rintro ⟨t, ht, u, hu, htu, h⟩
  refine ⟨t \ u, u \ t, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 htu,
    Finset.prod_sdiff_eq_prod_sdiff_iff.2 h⟩ <;> push_cast 

Depends on / 依赖: Finset, Finset.prod_sdiff_eq_prod_sdiff_iff, classical, disjoint_sdiff_sdiff, htusum, not_mulDissociated, not_mulDissociated.trans, prod_sdiff_eq_prod_sdiff_iff, sdiff_ne_sdiff_iff, sdiff_subset, sdiff_subset.trans
-/
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated s ↔
      exists t u : Finset α, ↑t subseteq s ∧ ↑u subseteq s ∧ Disjoint t u ∧ t != u ∧ ∏ a in t, a = ∏ a in u, a := by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨t, u, ht, hu, _, htune, htusum⟩ => ⟨t, ht, u, hu, htune, htusum⟩⟩
  rintro ⟨t, ht, u, hu, htu, h⟩
  refine ⟨t \ u, u \ t, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 htu,
    Finset.prod_sdiff_eq_prod_sdiff_iff.2 h⟩ <;> push_cast <;> exact sdiff_subset.trans ‹_›

/--
lemma `MulEquiv.mulDissociated_preimage` / 引理 `MulEquiv.mulDissociated_preimage`

English:
lemma MulEquiv.mulDissociated_preimage
  given: (e : β ≃* α)
  proof: by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_right, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]

中文:
引理 MulEquiv.mulDissociated_preimage
  条件: (e : β ≃* α)
  证明: by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_right, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]
-/
@[to_additive (attr := simp)] lemma MulEquiv.mulDissociated_preimage (e : β ≃* α) :
    MulDissociated (e ⁻¹' s) ↔ MulDissociated s := by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_right, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]

/--
lemma `mulDissociated_inv` / 引理 `mulDissociated_inv`

English:
lemma mulDissociated_inv
  statement: MulDissociated s⁻¹ ↔ MulDissociated s
  proof: (MulEquiv.inv α).mulDissociated_preimage

@[to_additive] protected alias ⟨MulDissociated.of_inv, MulDissociated.inv⟩ := mulDissociated_inv

中文:
引理 mulDissociated_inv
  结论: MulDissociated s⁻¹ ↔ MulDissociated s
  证明: (MulEquiv.inv α).mulDissociated_preimage

@[to_additive] protected alias ⟨MulDissociated.of_inv, MulDissociated.inv⟩ := mulDissociated_inv
-/
@[to_additive (attr := simp)] lemma mulDissociated_inv : MulDissociated s⁻¹ ↔ MulDissociated s :=
  (MulEquiv.inv α).mulDissociated_preimage

@[to_additive] protected alias ⟨MulDissociated.of_inv, MulDissociated.inv⟩ := mulDissociated_inv

end dissociation

namespace Finset
variable [DecidableEq α] [Fintype α] {s t u : Finset α} {a : α} {d : Nat}

/-- The span of a finset `s` is the finset of elements of the form `∏ a ∈ s, a ^ ε a` where
`ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive /-- The span of a finset `s` is the finset of elements of the form `∑ a ∈ s, ε a • a`
where `ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/]
/--
Definition of `mulSpan` / `mulSpan` 的定义

English:
definition mulSpan
  signature: (s : Finset α)
  body: (Fintype.piFinset fun _a => ({-1, 0, 1} : Finset Int)).image fun ε => ∏ a in s, a ^ ε a

@[to_additive (attr := simp)]

中文:
定义 mulSpan
  签名: (s : Finset α)
  定义体: (Fintype.piFinset fun _a => ({-1, 0, 1} : Finset Int)).image fun ε => ∏ a in s, a ^ ε a

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Fintype, Fintype.piFinset, piFinset
-/
def mulSpan (s : Finset α) : Finset α :=
  (Fintype.piFinset fun _a => ({-1, 0, 1} : Finset Int)).image fun ε => ∏ a in s, a ^ ε a

@[to_additive (attr := simp)]
/--
lemma `mem_mulSpan` / 引理 `mem_mulSpan`

English:
lemma mem_mulSpan
  proof: by
  simp [mulSpan]

@[to_additive (attr := simp)]

中文:
引理 mem_mulSpan
  证明: by
  simp [mulSpan]

@[to_additive (attr := simp)]

Depends on / 依赖: mulSpan
-/
lemma mem_mulSpan :
    a in mulSpan s ↔ exists ε : α -> Int, (forall a, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧ ∏ a in s, a ^ ε a = a := by
  simp [mulSpan]

@[to_additive (attr := simp)]
/--
lemma `subset_mulSpan` / 引理 `subset_mulSpan`

English:
lemma subset_mulSpan
  statement: s subseteq mulSpan s
  proof: fun a ha =>
  mem_mulSpan.2 ⟨Pi.single a 1, fun b => by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

@[to_additive]

中文:
引理 subset_mulSpan
  结论: s subseteq mulSpan s
  证明: fun a ha =>
  mem_mulSpan.2 ⟨Pi.single a 1, fun b => by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

@[to_additive]
-/
lemma subset_mulSpan : s subseteq mulSpan s := fun a ha =>
  mem_mulSpan.2 ⟨Pi.single a 1, fun b => by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

@[to_additive]
/--
lemma `prod_div_prod_mem_mulSpan` / 引理 `prod_div_prod_mem_mulSpan`

English:
lemma prod_div_prod_mem_mulSpan
  given: (ht : t subseteq s) (hu : u subseteq s)
  proof: mem_mulSpan.2 ⟨Set.indicator t 1 - Set.indicator u 1, fun a => by
    by_cases a in t <;> by_cases a in u <;> simp [*], by simp [prod_div_distrib, zpow_sub,
      ← div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2, *]⟩

中文:
引理 prod_div_prod_mem_mulSpan
  条件: (ht : t subseteq s) (hu : u subseteq s)
  证明: mem_mulSpan.2 ⟨Set.indicator t 1 - Set.indicator u 1, fun a => by
    by_cases a in t <;> by_cases a in u <;> simp [*], by simp [prod_div_distrib, zpow_sub,
      ← div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2, *]⟩

Depends on / 依赖: Set.indicator, div_eq_mul_inv, indicator, inter_eq_right, mem_mulSpan, pow_ite, prod_div_distrib, zpow_sub
-/
lemma prod_div_prod_mem_mulSpan (ht : t subseteq s) (hu : u subseteq s) :
    (∏ a in t, a) / ∏ a in u, a in mulSpan s :=
  mem_mulSpan.2 ⟨Set.indicator t 1 - Set.indicator u 1, fun a => by
    by_cases a in t <;> by_cases a in u <;> simp [*], by simp [prod_div_distrib, zpow_sub,
      ← div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2, *]⟩

/-- If every dissociated subset of `s` has size at most `d`, then `s` is actually generated by a
subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subsets all have
size at most `d` is of dimension at most `d` itself. -/
@[to_additive /-- If every dissociated subset of `s` has size at most `d`, then `s` is actually
generated by a subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subspaces all have
size at most `d` is of dimension at most `d` itself. -/]
/--
lemma `exists_subset_mulSpan_card_le_of_forall_mulDissociated` / 引理 `exists_subset_mulSpan_card_le_of_forall_mulDissociated`

English:
lemma exists_subset_mulSpan_card_le_of_forall_mulDissociated
  proof: by
  classical
  obtain ⟨s', hs'⟩ :=
    (s.powerset.filter fun s' : Finset α => MulDissociated (s' : Set α)).exists_maximal
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hs'
  refine ⟨s', hs'.1.1, hs _ hs'.1.1 hs'.1.2, fun a ha => ?_⟩
  by_cases h

中文:
引理 exists_subset_mulSpan_card_le_of_forall_mulDissociated
  证明: by
  classical
  obtain ⟨s', hs'⟩ :=
    (s.powerset.filter fun s' : Finset α => MulDissociated (s' : Set α)).exists_maximal
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hs'
  refine ⟨s', hs'.1.1, hs _ hs'.1.1 hs'.1.2, fun a ha => ?_⟩
  by_cases h

Depends on / 依赖: Finset, MulDissociated, classical, empty_mem_powerset, exists_maximal, filter, insert_subset_iff, mem_filter, mem_powerset, not_gt, not_mulDissociated_iff_exists_disjoint, powerset, s.powerset.filter, ssubset_insert, subset_mulSpan
-/
lemma exists_subset_mulSpan_card_le_of_forall_mulDissociated
    (hs : forall s', s' subseteq s -> MulDissociated (s' : Set α) -> s'.card <= d) :
    exists s', s' subseteq s ∧ s'.card <= d ∧ s subseteq mulSpan s' := by
  classical
  obtain ⟨s', hs'⟩ :=
    (s.powerset.filter fun s' : Finset α => MulDissociated (s' : Set α)).exists_maximal
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hs'
  refine ⟨s', hs'.1.1, hs _ hs'.1.1 hs'.1.2, fun a ha => ?_⟩
  by_cases ha' : a in s'
  · exact subset_mulSpan ha'
  obtain ⟨t, u, ht, hu, htu⟩ := not_mulDissociated_iff_exists_disjoint.1 fun h =>
hs'.not_gt ⟨insert_subset_iff.2 ⟨ha, hs'.1.1⟩, h⟩ ssubset_insert ha'
  by_cases hat : a in t
  · have : a = (∏ b in u, b) / ∏ b in t.erase a, b := by
      rw [prod_erase_eq_div hat]; rw [htu.2.2]; rw [div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan
      ((subset_insert_iff_of_notMem <| disjoint_left.1 htu.1 hat).1 hu) (subset_insert_iff.1 ht)
  rw [coe_subset]; rw [subset_insert_iff_of_notMem hat] at ht
  by_cases hau : a in u
  · have : a = (∏ b in t, b) / ∏ b in u.erase a, b := by
      rw [prod_erase_eq_div hau]; rw [htu.2.2]; rw [div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan ht (subset_insert_iff.1 hu)
  · rw [coe_subset, subset_insert_iff_of_notMem hau] at hu
    cases not_mulDissociated_iff_exists_disjoint.2 ⟨t, u, ht, hu, htu⟩ hs'.1.2

end Finset
