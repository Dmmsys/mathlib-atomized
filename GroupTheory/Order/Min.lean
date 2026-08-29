/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Minimum order of an element

This file defines the minimum order of an element of a monoid.

## Main declarations

* `Monoid.minOrder`: The minimum order of an element of a given monoid.
* `Monoid.minOrder_eq_top`: The minimum order is infinite iff the monoid is torsion-free.
* `ZMod.minOrder`: The minimum order of $ℤ/nℤ$ is the smallest factor of `n`, unless `n = 0, 1`.
-/

@[expose] public section

open Subgroup

variable {G α : Type*}

namespace Monoid
section Monoid
variable (α) [Monoid α]

/-- The minimum order of a non-identity element. Also the minimum size of a nontrivial subgroup, see
`Monoid.le_minOrder_iff_forall_subgroup`. Returns `∞` if the monoid is torsion-free. -/
@[to_additive /-- The minimum order of a non-identity element. Also the minimum size of a nontrivial
subgroup, see `AddMonoid.le_minOrder_iff_forall_addSubgroup`. Returns `∞` if the monoid is
torsion-free. -/]
/--
Definition of `minOrder` / `minOrder` 的定义

English:
definition minOrder
  signature: : Nat∞
  body: ⨅ (a : α) (_ha : a != 1) (_ha' : IsOfFinOrder a), orderOf a

中文:
定义 minOrder
  签名: : 自然数∞
  定义体: ⨅ (a : α) (_ha : a != 1) (_ha' : IsOfFinOrder a), orderOf a

Depends on / 依赖: IsOfFinOrder, orderOf
-/
noncomputable def minOrder : Nat∞ := ⨅ (a : α) (_ha : a != 1) (_ha' : IsOfFinOrder a), orderOf a

variable {α} {a : α}

@[to_additive (attr := simp)]
/--
lemma `le_minOrder` / 引理 `le_minOrder`

English:
lemma le_minOrder
  given: {n : Nat∞}
  proof: by simp [minOrder]

@[to_additive]

中文:
引理 le_minOrder
  条件: {n : 自然数∞}
  证明: by simp [minOrder]

@[to_additive]

Depends on / 依赖: minOrder
-/
lemma le_minOrder {n : Nat∞} :
    n <= minOrder α ↔ forall ⦃a : α⦄, a != 1 -> IsOfFinOrder a -> n <= orderOf a := by simp [minOrder]

@[to_additive]
/--
lemma `minOrder_le_orderOf` / 引理 `minOrder_le_orderOf`

English:
lemma minOrder_le_orderOf
  given: (ha : a != 1) (ha' : IsOfFinOrder a)
  statement: minOrder α <= orderOf a
  proof: le_minOrder.1 le_rfl ha ha'

中文:
引理 minOrder_le_orderOf
  条件: (ha : a != 1) (ha' : IsOfFinOrder a)
  结论: minOrder α <= orderOf a
  证明: le_minOrder.1 le_rfl ha ha'

Depends on / 依赖: le_minOrder, le_rfl
-/
lemma minOrder_le_orderOf (ha : a != 1) (ha' : IsOfFinOrder a) : minOrder α <= orderOf a :=
  le_minOrder.1 le_rfl ha ha'

end Monoid

section Group
variable [Group G] {s : Subgroup G}

@[to_additive]
/--
lemma `le_minOrder_iff_forall_subgroup` / 引理 `le_minOrder_iff_forall_subgroup`

English:
lemma le_minOrder_iff_forall_subgroup
  given: {n : Nat∞}
  proof: by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' => ?_, fun h a ha ha' => ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using

中文:
引理 le_minOrder_iff_forall_subgroup
  条件: {n : 自然数∞}
  证明: by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' => ?_, fun h a ha ha' => ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using

Depends on / 依赖: WithTop, WithTop.coe_le_coe, bot_or_exists_ne_one, coe_le_coe, finite_zpowers, le_minOrder, orderOf_le_card, resolve_left, s.bot_or_exists_ne_one.resolve_left, s.orderOf_le_card, subset, zpowers_le, zpowers_ne_bot
-/
lemma le_minOrder_iff_forall_subgroup {n : Nat∞} :
    n <= minOrder G ↔ forall ⦃s : Subgroup G⦄, s != ⊥ -> (s : Set G).Finite -> n <= Nat.card s := by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' => ?_, fun h a ha ha' => ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers

@[to_additive]
/--
lemma `minOrder_le_natCard` / 引理 `minOrder_le_natCard`

English:
lemma minOrder_le_natCard
  given: (hs : s != ⊥) (hs' : (s : Set G).Finite)
  statement: minOrder G <= Nat.card s
  proof: le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

@[to_additive (attr := simp)]

中文:
引理 minOrder_le_natCard
  条件: (hs : s != ⊥) (hs' : (s : Set G).Finite)
  结论: minOrder G <= 自然数.card s
  证明: le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

@[to_additive (attr := simp)]

Depends on / 依赖: le_minOrder_iff_forall_subgroup, le_rfl
-/
lemma minOrder_le_natCard (hs : s != ⊥) (hs' : (s : Set G).Finite) : minOrder G <= Nat.card s :=
  le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

@[to_additive (attr := simp)]
/--
lemma `minOrder_eq_top` / 引理 `minOrder_eq_top`

English:
lemma minOrder_eq_top
  given: [IsMulTorsionFree G]
  statement: minOrder G = ⊤
  proof: by
  simpa [minOrder] using fun _ => not_isOfFinOrder_of_isMulTorsionFree

中文:
引理 minOrder_eq_top
  条件: [IsMulTorsionFree G]
  结论: minOrder G = ⊤
  证明: by
  simpa [minOrder] using fun _ => not_isOfFinOrder_of_isMulTorsionFree

Depends on / 依赖: minOrder, not_isOfFinOrder_of_isMulTorsionFree
-/
lemma minOrder_eq_top [IsMulTorsionFree G] : minOrder G = ⊤ := by
  simpa [minOrder] using fun _ => not_isOfFinOrder_of_isMulTorsionFree

end Group

section CommGroup
variable [CommGroup G] {s : Subgroup G}

@[to_additive (attr := simp)]
/--
lemma `minOrder_eq_top_iff` / 引理 `minOrder_eq_top_iff`

English:
lemma minOrder_eq_top_iff
  statement: minOrder G = ⊤ ↔ IsMulTorsionFree G
  proof: by
  simp [minOrder, isMulTorsionFree_iff_not_isOfFinOrder]

中文:
引理 minOrder_eq_top_iff
  结论: minOrder G = ⊤ ↔ IsMulTorsionFree G
  证明: by
  simp [minOrder, isMulTorsionFree_iff_not_isOfFinOrder]

Depends on / 依赖: isMulTorsionFree_iff_not_isOfFinOrder, minOrder
-/
lemma minOrder_eq_top_iff : minOrder G = ⊤ ↔ IsMulTorsionFree G := by
  simp [minOrder, isMulTorsionFree_iff_not_isOfFinOrder]

end CommGroup
end Monoid

open AddMonoid AddSubgroup Nat Set

namespace ZMod

@[simp]
/--
lemma `minOrder` / 引理 `minOrder`

English:
lemma minOrder
  given: {n : Nat} (hn : n != 0) (hn₁ : n != 1)
  statement: minOrder (ZMod n) = n.minFac
  proof: by
  have : Fact (1 < n) := ⟨one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn, hn₁⟩⟩
  have : (↑(n / n.minFac) : ZMod n) != 0 := by
    rw [Ne]; rw [ringChar.spec]; rw [ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (minFac_le hn.bot_lt) n.minFac_pos)
        (div_lt_self hn.bot_lt (

中文:
引理 minOrder
  条件: {n : 自然数} (hn : n != 0) (hn₁ : n != 1)
  结论: minOrder (ZMod n) = n.minFac
  证明: by
  have : Fact (1 < n) := ⟨one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn, hn₁⟩⟩
  have : (↑(n / n.minFac) : ZMod n) != 0 := by
    rw [Ne]; rw [ringChar.spec]; rw [ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (minFac_le hn.bot_lt) n.minFac_pos)
        (div_lt_self hn.bot_lt (
-/
protected lemma minOrder {n : Nat} (hn : n != 0) (hn₁ : n != 1) : minOrder (ZMod n) = n.minFac := by
  have : Fact (1 < n) := ⟨one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn, hn₁⟩⟩
  have : (↑(n / n.minFac) : ZMod n) != 0 := by
    rw [Ne]; rw [ringChar.spec]; rw [ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (minFac_le hn.bot_lt) n.minFac_pos)
        (div_lt_self hn.bot_lt (minFac_prime hn₁).one_lt)
refine ((minOrder_le_natCard (zmultiples_eq_bot.not.2 this) <| toFinite _).trans ?_).antisymm
    le_minOrder_iff_forall_addSubgroup.2 fun s hs _ => ?_
  · rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.minFac_dvd), Nat.div_div_self n.minFac_dvd hn]
  · have : Nontrivial s := s.bot_or_nontrivial.resolve_left hs
exact WithTop.coe_le_coe.2 minFac_le_of_dvd Finite.one_lt_card
      (card_addSubgroup_dvd_card _).trans n.card_zmod.dvd

@[simp]
/--
lemma `minOrder_of_prime` / 引理 `minOrder_of_prime`

English:
lemma minOrder_of_prime
  given: {p : Nat} (hp : p.Prime)
  statement: minOrder (ZMod p) = p
  proof: by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one]; rw [hp.minFac_eq]

中文:
引理 minOrder_of_prime
  条件: {p : 自然数} (hp : p.Prime)
  结论: minOrder (ZMod p) = p
  证明: by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one]; rw [hp.minFac_eq]

Depends on / 依赖: ZMod.minOrder, hp.minFac_eq, hp.ne_one, hp.ne_zero, minFac_eq, minOrder, ne_one, ne_zero
-/
lemma minOrder_of_prime {p : Nat} (hp : p.Prime) : minOrder (ZMod p) = p := by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one]; rw [hp.minFac_eq]

end ZMod
