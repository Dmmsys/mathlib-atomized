/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lagrange's theorem: the order of a subgroup divides the order of the group.

* `Subgroup.card_subgroup_dvd_card`: Lagrange's theorem (for multiplicative groups);
  there is an analogous version for additive groups

-/

public section

assert_not_exists Field

open scoped Pointwise

variable {α : Type*} [Group α] {s : Subgroup α}

namespace QuotientGroup

@[to_additive]
/--
Instance `fintype` / 实例 `fintype`

English:
instance fintype
  signature: [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).r]
  body: Quotient.fintype (leftRel s)

@[to_additive]

中文:
实例 fintype
  签名: [有限类型 α] (s : 子群 α) [DecidableRel (leftRel s).r]
  定义体: Quotient.fintype (leftRel s)

@[to_additive]

Depends on / 依赖: Quotient, Quotient.fintype, fintype, leftRel
-/
instance fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).r] : Fintype (α ⧸ s) :=
  Quotient.fintype (leftRel s)

@[to_additive]
instance (priority := 100) finite [Finite α] : Finite (α ⧸ s) :=
  Quotient.finite _

@[to_additive]
/--
Instance `fintypeQuotientRightRel` / 实例 `fintypeQuotientRightRel`

English:
instance fintypeQuotientRightRel
  signature: [Fintype (α ⧸ s)]
  body: .ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

中文:
实例 fintypeQuotientRightRel
  签名: [有限类型 (α ⧸ s)]
  定义体: .ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

Depends on / 依赖: QuotientGroup, QuotientGroup.quotientRightRelEquivQuotientLeftRel, ofEquiv, quotientRightRelEquivQuotientLeftRel
-/
instance fintypeQuotientRightRel [Fintype (α ⧸ s)] :
    Fintype (Quotient (QuotientGroup.rightRel s)) :=
  .ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

variable (s) in
@[to_additive]
/--
lemma `card_quotient_rightRel` / 引理 `card_quotient_rightRel`

English:
lemma card_quotient_rightRel
  given: [Fintype (α ⧸ s)]
  proof: Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

中文:
引理 card_quotient_rightRel
  条件: [有限类型 (α ⧸ s)]
  证明: Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, QuotientGroup, QuotientGroup.quotientRightRelEquivQuotientLeftRel, ofEquiv_card, quotientRightRelEquivQuotientLeftRel
-/
lemma card_quotient_rightRel [Fintype (α ⧸ s)] :
    Fintype.card (Quotient (QuotientGroup.rightRel s)) = Fintype.card (α ⧸ s) :=
  Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

end QuotientGroup

namespace Subgroup

@[to_additive AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
/--
theorem `card_eq_card_quotient_mul_card_subgroup` / 定理 `card_eq_card_quotient_mul_card_subgroup`

English:
theorem card_eq_card_quotient_mul_card_subgroup
  given: (s : Subgroup α)
  proof: by
  rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

@[to_additive]

中文:
定理 card_eq_card_quotient_mul_card_subgroup
  条件: (s : 子群 α)
  证明: by
  rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

@[to_additive]

Depends on / 依赖: Nat.card_congr, Nat.card_prod, Subgroup, Subgroup.groupEquivQuotientProdSubgroup, card_congr, card_prod, groupEquivQuotientProdSubgroup
-/
theorem card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) :
    Nat.card α = Nat.card (α ⧸ s) * Nat.card s := by
  rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

@[to_additive]
/--
lemma `card_mul_eq_card_subgroup_mul_card_quotient` / 引理 `card_mul_eq_card_subgroup_mul_card_quotient`

English:
lemma card_mul_eq_card_subgroup_mul_card_quotient
  given: (s : Subgroup α) (t : Set α)
  proof: by
  rw [← Nat.card_prod]; rw [Nat.card_congr]
  apply Equiv.trans _ (QuotientGroup.preimageMkEquivSubgroupProdSet _ _)
  rw [QuotientGroup.preimage_image_mk]
  convert! Equiv.refl ↑(t * s)
  aesop (add simp [Set.mem_mul])

中文:
引理 card_mul_eq_card_subgroup_mul_card_quotient
  条件: (s : 子群 α) (t : 集合 α)
  证明: by
  rw [← Nat.card_prod]; rw [Nat.card_congr]
  apply Equiv.trans _ (QuotientGroup.preimageMkEquivSubgroupProdSet _ _)
  rw [QuotientGroup.preimage_image_mk]
  convert! Equiv.refl ↑(t * s)
  aesop (add simp [Set.mem_mul])

Depends on / 依赖: Equiv.refl, Equiv.trans, Nat.card_congr, Nat.card_prod, QuotientGroup, QuotientGroup.preimageMkEquivSubgroupProdSet, QuotientGroup.preimage_image_mk, Set.mem_mul, card_congr, card_prod, convert, mem_mul, preimageMkEquivSubgroupProdSet, preimage_image_mk
-/
lemma card_mul_eq_card_subgroup_mul_card_quotient (s : Subgroup α) (t : Set α) :
    Nat.card (t * s : Set α) = Nat.card s * Nat.card (t.image (↑) : Set (α ⧸ s)) := by
  rw [← Nat.card_prod]; rw [Nat.card_congr]
  apply Equiv.trans _ (QuotientGroup.preimageMkEquivSubgroupProdSet _ _)
  rw [QuotientGroup.preimage_image_mk]
  convert! Equiv.refl ↑(t * s)
  aesop (add simp [Set.mem_mul])

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive (attr := wikidata Q505798) /-- **Lagrange's Theorem**: The order of an additive
subgroup divides the order of its ambient additive group. -/]
/--
theorem `card_subgroup_dvd_card` / 定理 `card_subgroup_dvd_card`

English:
theorem card_subgroup_dvd_card
  given: (s : Subgroup α)
  statement: Nat.card s ∣ Nat.card α
  proof: by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left Nat]

@[to_additive]

中文:
定理 card_subgroup_dvd_card
  条件: (s : 子群 α)
  结论: 自然数.card s ∣ 自然数.card α
  证明: by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left Nat]

@[to_additive]

Depends on / 依赖: card_eq_card_quotient_mul_card_subgroup, dvd_mul_left
-/
theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left Nat]

@[to_additive]
/--
theorem `card_quotient_dvd_card` / 定理 `card_quotient_dvd_card`

English:
theorem card_quotient_dvd_card
  given: (s : Subgroup α)
  statement: Nat.card (α ⧸ s) ∣ Nat.card α
  proof: by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right Nat]

中文:
定理 card_quotient_dvd_card
  条件: (s : 子群 α)
  结论: 自然数.card (α ⧸ s) ∣ 自然数.card α
  证明: by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right Nat]

Depends on / 依赖: card_eq_card_quotient_mul_card_subgroup, dvd_mul_right
-/
theorem card_quotient_dvd_card (s : Subgroup α) : Nat.card (α ⧸ s) ∣ Nat.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right Nat]

variable {H : Type*} [Group H]

@[to_additive]
/--
theorem `card_dvd_of_injective` / 定理 `card_dvd_of_injective`

English:
theorem card_dvd_of_injective
  given: (f : α ->* H) (hf : Function.Injective f)
  proof: by
  calc
      Nat.card α = Nat.card (f.range : Subgroup H) := Nat.card_congr (Equiv.ofInjective f hf)
      _ ∣ Nat.card H := card_subgroup_dvd_card _

@[to_additive]

中文:
定理 card_dvd_of_injective
  条件: (f : α ->* H) (hf : 函数.单射 f)
  证明: by
  calc
      Nat.card α = Nat.card (f.range : Subgroup H) := Nat.card_congr (Equiv.ofInjective f hf)
      _ ∣ Nat.card H := card_subgroup_dvd_card _

@[to_additive]

Depends on / 依赖: Equiv.ofInjective, Nat.card, Nat.card_congr, Subgroup, card_congr, card_subgroup_dvd_card, f.range, ofInjective
-/
theorem card_dvd_of_injective (f : α ->* H) (hf : Function.Injective f) :
    Nat.card α ∣ Nat.card H := by
  calc
      Nat.card α = Nat.card (f.range : Subgroup H) := Nat.card_congr (Equiv.ofInjective f hf)
      _ ∣ Nat.card H := card_subgroup_dvd_card _

@[to_additive]
/--
theorem `card_dvd_of_le` / 定理 `card_dvd_of_le`

English:
theorem card_dvd_of_le
  given: {H K : Subgroup α} (hHK : H <= K)
  statement: Nat.card H ∣ Nat.card K
  proof: card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]

中文:
定理 card_dvd_of_le
  条件: {H K : 子群 α} (hHK : H <= K)
  结论: 自然数.card H ∣ 自然数.card K
  证明: card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]

Depends on / 依赖: card_dvd_of_injective, inclusion, inclusion_injective
-/
theorem card_dvd_of_le {H K : Subgroup α} (hHK : H <= K) : Nat.card H ∣ Nat.card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]
/--
theorem `card_comap_dvd_of_injective` / 定理 `card_comap_dvd_of_injective`

English:
theorem card_comap_dvd_of_injective
  statement: (K : Subgroup H) (f : α ->* H)
  proof: calc Nat.card (K.comap f) = Nat.card ((K.comap f).map f) :=
      Nat.card_congr (equivMapOfInjective _ _ hf).toEquiv
    _ ∣ Nat.card K := card_dvd_of_le (map_comap_le _ _)

中文:
定理 card_comap_dvd_of_injective
  结论: (K : 子群 H) (f : α ->* H)
  证明: calc Nat.card (K.comap f) = Nat.card ((K.comap f).map f) :=
      Nat.card_congr (equivMapOfInjective _ _ hf).toEquiv
    _ ∣ Nat.card K := card_dvd_of_le (map_comap_le _ _)

Depends on / 依赖: K.comap, Nat.card, Nat.card_congr, card_congr, card_dvd_of_le, equivMapOfInjective, map_comap_le, toEquiv
-/
theorem card_comap_dvd_of_injective (K : Subgroup H) (f : α ->* H)
    (hf : Function.Injective f) : Nat.card (K.comap f) ∣ Nat.card K :=
  calc Nat.card (K.comap f) = Nat.card ((K.comap f).map f) :=
      Nat.card_congr (equivMapOfInjective _ _ hf).toEquiv
    _ ∣ Nat.card K := card_dvd_of_le (map_comap_le _ _)

end Subgroup
