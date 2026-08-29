/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Subgroups

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/

public section

assert_not_exists Field

variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

namespace Subgroup

@[to_additive]
instance (K : Subgroup G) [DecidablePred (· in K)] [Fintype G] : Fintype K :=
  show Fintype { g : G // g in K } from inferInstance

@[to_additive]
instance (K : Subgroup G) [Finite G] : Finite K :=
  Subtype.finite

end Subgroup

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


namespace Subgroup

variable (H K : Subgroup G)

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive /-- Sum of a list of elements in an `AddSubgroup` is in the `AddSubgroup`. -/]
/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {l : List G}
  statement: (forall x in l, x in K) -> l.prod in K
  proof: list_prod_mem

中文:
定理 list_prod_mem
  条件: {l : 列表 G}
  结论: (对任意 x in l, x in K) -> l.乘积 in K
  证明: list_prod_mem
-/
protected theorem list_prod_mem {l : List G} : (forall x in l, x in K) -> l.prod in K :=
  list_prod_mem

/-- Product of a multiset of elements in a subgroup of a `CommGroup` is in the subgroup. -/
@[to_additive /-- Sum of a multiset of elements in an `AddSubgroup` of an `AddCommGroup` is in
the `AddSubgroup`. -/]
/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  given: {G} [CommGroup G] (K : Subgroup G) (g : Multiset G)
  proof: multiset_prod_mem g

@[to_additive]

中文:
定理 multiset_prod_mem
  条件: {G} [交换群 G] (K : 子群 G) (g : Multiset G)
  证明: multiset_prod_mem g

@[to_additive]
-/
protected theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (forall a in g, a in K) -> g.prod in K :=
  multiset_prod_mem g

@[to_additive]
/--
theorem `multiset_noncommProd_mem` / 定理 `multiset_noncommProd_mem`

English:
theorem multiset_noncommProd_mem
  given: (K : Subgroup G) (g : Multiset G) (comm)
  proof: K.toSubmonoid.multiset_noncommProd_mem g comm

中文:
定理 multiset_noncommProd_mem
  条件: (K : 子群 G) (g : Multiset G) (comm)
  证明: K.toSubmonoid.multiset_noncommProd_mem g comm

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_le, AddSubmonoid.subset_closure, K.toSubmonoid.multiset_noncommProd_mem, Multiplicative, Submonoid, Submonoid.closure_le, Submonoid.subset_closure, Submonoid.toAddSubmonoid, closure_le, l_le, le_antisymm, multiset_noncommProd_mem, subset_closure, toAddSubmonoid, toSubmonoid, to_galoisConnection, to_galoisConnection.l_le
-/
theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (forall a in g, a in K) -> g.noncommProd comm in K :=
  K.toSubmonoid.multiset_noncommProd_mem g comm

/-- Product of elements of a subgroup of a `CommGroup` indexed by a `Finset` is in the
    subgroup. -/
@[to_additive /-- Sum of elements in an `AddSubgroup` of an `AddCommGroup` indexed by a `Finset`
is in the `AddSubgroup`. -/]
/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {G : Type*} [CommGroup G] (K : Subgroup G) {ι : Type*} {t : Finset ι}
  proof: prod_mem h

@[to_additive]

中文:
定理 prod_mem
  结论: {G : 类型} [交换群 G] (K : 子群 G) {ι : 类型} {t : 有限集 ι}
  证明: prod_mem h

@[to_additive]
-/
protected theorem prod_mem {G : Type*} [CommGroup G] (K : Subgroup G) {ι : Type*} {t : Finset ι}
    {f : ι -> G} (h : forall c in t, f c in K) : (∏ c in t, f c) in K :=
  prod_mem h

@[to_additive]
/--
theorem `noncommProd_mem` / 定理 `noncommProd_mem`

English:
theorem noncommProd_mem
  given: (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι -> G} (comm)
  proof: K.toSubmonoid.noncommProd_mem t f comm

@[to_additive (attr := simp 1100, norm_cast)]

中文:
定理 noncommProd_mem
  条件: (K : 子群 G) {ι : 类型} {t : 有限集 ι} {f : ι -> G} (comm)
  证明: K.toSubmonoid.noncommProd_mem t f comm

@[to_additive (attr := simp 1100, norm_cast)]

Depends on / 依赖: K.toSubmonoid.noncommProd_mem, noncommProd_mem, toSubmonoid
-/
theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι -> G} (comm) :
    (forall c in t, f c in K) -> t.noncommProd f comm in K :=
  K.toSubmonoid.noncommProd_mem t f comm

@[to_additive (attr := simp 1100, norm_cast)]
/--
theorem `val_list_prod` / 定理 `val_list_prod`

English:
theorem val_list_prod
  given: (l : List H)
  statement: (l.prod : G) = (l.map Subtype.val).prod
  proof: SubmonoidClass.coe_list_prod l

@[to_additive (attr := simp 1100, norm_cast)]

中文:
定理 val_list_prod
  条件: (l : 列表 H)
  结论: (l.乘积 : G) = (l.map 子类型.val).乘积
  证明: SubmonoidClass.coe_list_prod l

@[to_additive (attr := simp 1100, norm_cast)]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.coe_list_prod, coe_list_prod
-/
theorem val_list_prod (l : List H) : (l.prod : G) = (l.map Subtype.val).prod :=
  SubmonoidClass.coe_list_prod l

@[to_additive (attr := simp 1100, norm_cast)]
/--
theorem `val_multiset_prod` / 定理 `val_multiset_prod`

English:
theorem val_multiset_prod
  given: {G} [CommGroup G] (H : Subgroup G) (m : Multiset H)
  proof: SubmonoidClass.coe_multiset_prod m

@[to_additive (attr := simp 1100, norm_cast)]

中文:
定理 val_multiset_prod
  条件: {G} [交换群 G] (H : 子群 G) (m : Multiset H)
  证明: SubmonoidClass.coe_multiset_prod m

@[to_additive (attr := simp 1100, norm_cast)]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.coe_multiset_prod, coe_multiset_prod
-/
theorem val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.prod : G) = (m.map Subtype.val).prod :=
  SubmonoidClass.coe_multiset_prod m

@[to_additive (attr := simp 1100, norm_cast)]
/--
theorem `val_finsetProd` / 定理 `val_finsetProd`

English:
theorem val_finsetProd
  given: {ι G} [CommGroup G] (H : Subgroup G) (f : ι -> H) (s : Finset ι)
  proof: SubmonoidClass.coe_finsetProd f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubgroup.val_finset_sum := _root_.AddSubgroup.val_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias val_finset_prod := val_finsetProd

@[to_additive]

中文:
定理 val_finsetProd
  条件: {ι G} [交换群 G] (H : 子群 G) (f : ι -> H) (s : 有限集 ι)
  证明: SubmonoidClass.coe_finsetProd f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubgroup.val_finset_sum := _root_.AddSubgroup.val_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias val_finset_prod := val_finsetProd

@[to_additive]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.coe_finsetProd, coe_finsetProd
-/
theorem val_finsetProd {ι G} [CommGroup G] (H : Subgroup G) (f : ι -> H) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : G) :=
  SubmonoidClass.coe_finsetProd f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubgroup.val_finset_sum := _root_.AddSubgroup.val_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias val_finset_prod := val_finsetProd

@[to_additive]
/--
Instance `fintypeBot` / 实例 `fintypeBot`

English:
instance fintypeBot
  signature: : Fintype (⊥ : Subgroup G)
  body: ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩

@[to_additive]

中文:
实例 fintypeBot
  签名: : 有限类型 (⊥ : 子群 G)
  定义体: ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩

@[to_additive]

Depends on / 依赖: Finset, Finset.mem_singleton_self, mem_singleton_self
-/
instance fintypeBot : Fintype (⊥ : Subgroup G) :=
  ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩

@[to_additive]
/--
theorem `card_bot` / 定理 `card_bot`

English:
theorem card_bot
  statement: Nat.card (⊥ : Subgroup G) = 1
  proof: by simp

@[to_additive]

中文:
定理 card_bot
  结论: 自然数.card (⊥ : 子群 G) = 1
  证明: by simp

@[to_additive]
-/
theorem card_bot : Nat.card (⊥ : Subgroup G) = 1 := by simp

@[to_additive]
/--
theorem `card_top` / 定理 `card_top`

English:
theorem card_top
  statement: Nat.card (⊤ : Subgroup G) = Nat.card G
  proof: Nat.card_congr Subgroup.topEquiv.toEquiv

@[to_additive]

中文:
定理 card_top
  结论: 自然数.card (⊤ : 子群 G) = 自然数.card G
  证明: Nat.card_congr Subgroup.topEquiv.toEquiv

@[to_additive]

Depends on / 依赖: Nat.card_congr, Subgroup, Subgroup.topEquiv.toEquiv, card_congr, toEquiv, topEquiv
-/
theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

@[to_additive]
/--
theorem `eq_of_le_of_card_ge` / 定理 `eq_of_le_of_card_ge`

English:
theorem eq_of_le_of_card_ge
  statement: {H K : Subgroup G} [Finite K] (hle : H <= K)
  proof: SetLike.coe_injective Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

@[to_additive]

中文:
定理 eq_of_le_of_card_ge
  结论: {H K : 子群 G} [有限 K] (hle : H <= K)
  证明: SetLike.coe_injective Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.eq_of_subset_of_card_le, Set.toFinite, SetLike, SetLike.coe_injective, coe_injective, eq_of_subset_of_card_le, toFinite
-/
theorem eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H <= K)
    (hcard : Nat.card K <= Nat.card H) :
    H = K :=
SetLike.coe_injective Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

@[to_additive]
/--
theorem `eq_top_of_le_card` / 定理 `eq_top_of_le_card`

English:
theorem eq_top_of_le_card
  given: [Finite G] (h : Nat.card G <= Nat.card H)
  statement: H = ⊤
  proof: eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

@[to_additive]

中文:
定理 eq_top_of_le_card
  条件: [有限 G] (h : 自然数.card G <= 自然数.card H)
  结论: H = ⊤
  证明: eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

@[to_additive]

Depends on / 依赖: Equiv.Set.univ, Nat.card_congr, card_congr, eq_of_le_of_card_ge, le_top
-/
theorem eq_top_of_le_card [Finite G] (h : Nat.card G <= Nat.card H) : H = ⊤ :=
  eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

@[to_additive]
/--
theorem `eq_top_of_card_eq` / 定理 `eq_top_of_card_eq`

English:
theorem eq_top_of_card_eq
  given: [Finite H] (h : Nat.card H = Nat.card G)
  statement: H = ⊤
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact eq_top_of_le_card _ (Nat.le_of_eq h.symm)

@[to_additive (attr := simp)]

中文:
定理 eq_top_of_card_eq
  条件: [有限 H] (h : 自然数.card H = 自然数.card G)
  结论: H = ⊤
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact eq_top_of_le_card _ (Nat.le_of_eq h.symm)

@[to_additive (attr := simp)]

Depends on / 依赖: Finite, Nat.card_pos.ne, Nat.finite_of_card_ne_zero, Nat.le_of_eq, card_pos, eq_top_of_le_card, finite_of_card_ne_zero, h.symm, le_of_eq
-/
theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact eq_top_of_le_card _ (Nat.le_of_eq h.symm)

@[to_additive (attr := simp)]
/--
theorem `card_eq_iff_eq_top` / 定理 `card_eq_iff_eq_top`

English:
theorem card_eq_iff_eq_top
  given: [Finite H]
  statement: Nat.card H = Nat.card G ↔ H = ⊤
  proof: Iff.intro (eq_top_of_card_eq H) (fun h => by simpa only [h] using card_top)

@[to_additive]

中文:
定理 card_eq_iff_eq_top
  条件: [有限 H]
  结论: 自然数.card H = 自然数.card G ↔ H = ⊤
  证明: Iff.intro (eq_top_of_card_eq H) (fun h => by simpa only [h] using card_top)

@[to_additive]

Depends on / 依赖: Iff.intro, card_top, eq_top_of_card_eq
-/
theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ :=
  Iff.intro (eq_top_of_card_eq H) (fun h => by simpa only [h] using card_top)

@[to_additive]
/--
theorem `eq_bot_of_card_le` / 定理 `eq_bot_of_card_le`

English:
theorem eq_bot_of_card_le
  given: [Finite H] (h : Nat.card H <= 1)
  statement: H = ⊥
  proof: let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

@[to_additive]

中文:
定理 eq_bot_of_card_le
  条件: [有限 H] (h : 自然数.card H <= 1)
  结论: H = ⊥
  证明: let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

@[to_additive]

Depends on / 依赖: Finite, Finite.card_le_one_iff_subsingleton.mp, card_le_one_iff_subsingleton, eq_bot_of_subsingleton
-/
theorem eq_bot_of_card_le [Finite H] (h : Nat.card H <= 1) : H = ⊥ :=
  let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

@[to_additive]
/--
theorem `eq_bot_of_card_eq` / 定理 `eq_bot_of_card_eq`

English:
theorem eq_bot_of_card_eq
  given: (h : Nat.card H = 1)
  statement: H = ⊥
  proof: let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

@[to_additive card_le_one_iff_eq_bot]

中文:
定理 eq_bot_of_card_eq
  条件: (h : 自然数.card H = 1)
  结论: H = ⊥
  证明: let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

@[to_additive card_le_one_iff_eq_bot]

Depends on / 依赖: Nat.card_eq_one_iff_unique.mp, card_eq_one_iff_unique, eq_bot_of_subsingleton
-/
theorem eq_bot_of_card_eq (h : Nat.card H = 1) : H = ⊥ :=
  let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

@[to_additive card_le_one_iff_eq_bot]
/--
theorem `card_le_one_iff_eq_bot` / 定理 `card_le_one_iff_eq_bot`

English:
theorem card_le_one_iff_eq_bot
  given: [Finite H]
  statement: Nat.card H <= 1 ↔ H = ⊥
  proof: ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

中文:
定理 card_le_one_iff_eq_bot
  条件: [有限 H]
  结论: 自然数.card H <= 1 ↔ H = ⊥
  证明: ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

Depends on / 依赖: H.eq_bot_of_card_le, eq_bot_of_card_le
-/
theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H <= 1 ↔ H = ⊥ :=
  ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

/--
lemma `eq_bot_iff_card` / 引理 `eq_bot_iff_card`

English:
lemma eq_bot_iff_card
  statement: H = ⊥ ↔ Nat.card H = 1
  proof: ⟨by rintro rfl; exact card_bot, eq_bot_of_card_eq _⟩

@[to_additive one_lt_card_iff_ne_bot]

中文:
引理 eq_bot_iff_card
  结论: H = ⊥ ↔ 自然数.card H = 1
  证明: ⟨by rintro rfl; exact card_bot, eq_bot_of_card_eq _⟩

@[to_additive one_lt_card_iff_ne_bot]
-/
@[to_additive] lemma eq_bot_iff_card : H = ⊥ ↔ Nat.card H = 1 :=
  ⟨by rintro rfl; exact card_bot, eq_bot_of_card_eq _⟩

@[to_additive one_lt_card_iff_ne_bot]
/--
theorem `one_lt_card_iff_ne_bot` / 定理 `one_lt_card_iff_ne_bot`

English:
theorem one_lt_card_iff_ne_bot
  given: [Finite H]
  statement: 1 < Nat.card H ↔ H != ⊥
  proof: lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

@[to_additive]

中文:
定理 one_lt_card_iff_ne_bot
  条件: [有限 H]
  结论: 1 < 自然数.card H ↔ H != ⊥
  证明: lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

@[to_additive]

Depends on / 依赖: H.card_le_one_iff_eq_bot.not, card_le_one_iff_eq_bot, lt_iff_not_ge, lt_iff_not_ge.trans
-/
theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H != ⊥ :=
  lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

@[to_additive]
/--
theorem `card_le_card_group` / 定理 `card_le_card_group`

English:
theorem card_le_card_group
  given: [Finite G]
  statement: Nat.card H <= Nat.card G
  proof: Nat.card_le_card_of_injective _ Subtype.coe_injective

@[to_additive]

中文:
定理 card_le_card_group
  条件: [有限 G]
  结论: 自然数.card H <= 自然数.card G
  证明: Nat.card_le_card_of_injective _ Subtype.coe_injective

@[to_additive]

Depends on / 依赖: Nat.card_le_card_of_injective, Subtype, Subtype.coe_injective, card_le_card_of_injective, coe_injective
-/
theorem card_le_card_group [Finite G] : Nat.card H <= Nat.card G :=
  Nat.card_le_card_of_injective _ Subtype.coe_injective

@[to_additive]
/--
theorem `card_le_of_le` / 定理 `card_le_of_le`

English:
theorem card_le_of_le
  given: {H K : Subgroup G} [Finite K] (h : H <= K)
  statement: Nat.card H <= Nat.card K
  proof: Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

@[to_additive]

中文:
定理 card_le_of_le
  条件: {H K : 子群 G} [有限 K] (h : H <= K)
  结论: 自然数.card H <= 自然数.card K
  证明: Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

@[to_additive]

Depends on / 依赖: Nat.card_le_card_of_injective, Subgroup, Subgroup.inclusion_injective, card_le_card_of_injective, inclusion_injective
-/
theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H <= K) : Nat.card H <= Nat.card K :=
  Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

@[to_additive]
/--
theorem `card_map_of_injective` / 定理 `card_map_of_injective`

English:
theorem card_map_of_injective
  statement: {H : Type*} [Group H] {K : Subgroup G} {f : G ->* H}
  proof: by
  apply Nat.card_image_of_injective hf

@[to_additive]

中文:
定理 card_map_of_injective
  结论: {H : 类型} [群 H] {K : 子群 G} {f : G ->* H}
  证明: by
  apply Nat.card_image_of_injective hf

@[to_additive]

Depends on / 依赖: Nat.card_image_of_injective, card_image_of_injective
-/
theorem card_map_of_injective {H : Type*} [Group H] {K : Subgroup G} {f : G ->* H}
    (hf : Function.Injective f) :
    Nat.card (map f K) = Nat.card K := by
  apply Nat.card_image_of_injective hf

@[to_additive]
/--
theorem `card_subtype` / 定理 `card_subtype`

English:
theorem card_subtype
  given: (K : Subgroup G) (L : Subgroup K)
  proof: card_map_of_injective K.subtype_injective

@[to_additive]

中文:
定理 card_subtype
  条件: (K : 子群 G) (L : 子群 K)
  证明: card_map_of_injective K.subtype_injective

@[to_additive]

Depends on / 依赖: K.subtype_injective, card_map_of_injective, subtype_injective
-/
theorem card_subtype (K : Subgroup G) (L : Subgroup K) :
    Nat.card (map K.subtype L) = Nat.card L :=
  card_map_of_injective K.subtype_injective

@[to_additive]
/--
theorem `card_mapSubgroup` / 定理 `card_mapSubgroup`

English:
theorem card_mapSubgroup
  given: {G' : Type*} [Group G'] (e : G ≃* G')
  proof: Subgroup.card_map_of_injective e.injective

中文:
定理 card_mapSubgroup
  条件: {G' : 类型} [群 G'] (e : G ≃* G')
  证明: Subgroup.card_map_of_injective e.injective

Depends on / 依赖: Subgroup, Subgroup.card_map_of_injective, card_map_of_injective, e.injective, injective
-/
theorem card_mapSubgroup {G' : Type*} [Group G'] (e : G ≃* G') :
    Nat.card (e.mapSubgroup H) = Nat.card H :=
  Subgroup.card_map_of_injective e.injective

end Subgroup

namespace Subgroup

section Pi

open Set

variable {η : Type*} {f : η -> Type*} [forall i, Group (f i)]

@[to_additive]
/--
theorem `pi_mem_of_mulSingle_mem` / 定理 `pi_mem_of_mulSingle_mem`

English:
theorem pi_mem_of_mulSingle_mem
  statement: [Finite η] [DecidableEq η] {H : Subgroup (forall i, f i)} (x : forall i, f i)
  proof: Submonoid.pi_mem_of_mulSingle_mem x h

中文:
定理 pi_mem_of_mulSingle_mem
  结论: [有限 η] [DecidableEq η] {H : 子群 (对任意 i, f i)} (x : 对任意 i, f i)
  证明: Submonoid.pi_mem_of_mulSingle_mem x h

Depends on / 依赖: Submonoid, Submonoid.pi_mem_of_mulSingle_mem, pi_mem_of_mulSingle_mem
-/
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (forall i, f i)} (x : forall i, f i)
    (h : forall i, Pi.mulSingle i (x i) in H) : x in H :=
  Submonoid.pi_mem_of_mulSingle_mem x h

/-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the groups. -/
@[to_additive /-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the
additive groups. -/]
/--
theorem `pi_le_iff` / 定理 `pi_le_iff`

English:
theorem pi_le_iff
  given: [DecidableEq η] [Finite η] {H : forall i, Subgroup (f i)} {J : Subgroup (forall i, f i)}
  proof: Submonoid.pi_le_iff

@[to_additive]

中文:
定理 pi_le_iff
  条件: [DecidableEq η] [有限 η] {H : 对任意 i, 子群 (f i)} {J : 子群 (对任意 i, f i)}
  证明: Submonoid.pi_le_iff

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.pi_le_iff, pi_le_iff
-/
theorem pi_le_iff [DecidableEq η] [Finite η] {H : forall i, Subgroup (f i)} {J : Subgroup (forall i, f i)} :
    pi univ H <= J ↔ forall i : η, map (MonoidHom.mulSingle f i) (H i) <= J :=
  Submonoid.pi_le_iff

@[to_additive]
/--
theorem `closure_pi` / 定理 `closure_pi`

English:
theorem closure_pi
  given: [Finite η] {s : Π i, Set (f i)} (hs : forall i, 1 in s i)
  proof: le_antisymm
    ((closure_le _).2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
exact pi_le_iff.mpr fun i => (gc_map_comap _).l_le (closure_le _).2 fun _x hx =>
subset_closure mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa


中文:
定理 closure_pi
  条件: [有限 η] {s : Π i, 集合 (f i)} (hs : 对任意 i, 1 in s i)
  证明: le_antisymm
    ((closure_le _).2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
exact pi_le_iff.mpr fun i => (gc_map_comap _).l_le (closure_le _).2 fun _x hx =>
subset_closure mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa


Depends on / 依赖: classical, closure_le, gc_map_comap, l_le, le_antisymm, mem_univ_pi, mem_univ_pi.mpr, pi_le_iff, pi_le_iff.mpr, pi_subset_pi_iff, subset_closure
-/
theorem closure_pi [Finite η] {s : Π i, Set (f i)} (hs : forall i, 1 in s i) :
    closure (univ.pi fun i => s i) = pi univ fun i => closure (s i) :=
  le_antisymm
    ((closure_le _).2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
exact pi_le_iff.mpr fun i => (gc_map_comap _).l_le (closure_le _).2 fun _x hx =>
subset_closure mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa
        · simpa [H] using hs _)

end Pi

section Normalizer

/--
theorem `mem_normalizer_fintype` / 定理 `mem_normalizer_fintype`

English:
theorem mem_normalizer_fintype
  given: {S : Set G} [Finite S] {x : G} (h : forall n, n in S -> x * n * x⁻¹ in S)
  proof: by
  have := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have :

中文:
定理 mem_normalizer_fintype
  条件: {S : 集合 G} [有限 S] {x : G} (h : 对任意 n, n in S -> x * n * x⁻¹ in S)
  证明: by
  have := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have :

Depends on / 依赖: Classical, Classical.propDecidable, Set.card_image_of_injective, Set.eq_of_subset_of_card_le, card_image_of_injective, conj_injective, eq_of_subset_of_card_le, heq.symm, nonempty_fintype, propDecidable
-/
theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : forall n, n in S -> x * n * x⁻¹ in S) :
    x in Subgroup.normalizer S := by
  have := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have : x * n * x⁻¹ in (fun n => x * n * x⁻¹) '' S := heq.symm ▸ h₁
      let ⟨y, hy⟩ := this
      conj_injective hy.2 ▸ hy.1⟩

end Normalizer

end Subgroup

namespace MonoidHom

variable {N : Type*} [Group N]

open Subgroup

@[to_additive]
/--
Instance `decidableMemRange` / 实例 `decidableMemRange`

English:
instance decidableMemRange
  signature: (f : G ->* N) [Fintype G] [DecidableEq N]
  body: fun _ => Fintype.decidableExistsFintype

中文:
实例 decidableMemRange
  签名: (f : G ->* N) [有限类型 G] [DecidableEq N]
  定义体: fun _ => Fintype.decidableExistsFintype

Depends on / 依赖: Fintype, Fintype.decidableExistsFintype, decidableExistsFintype
-/
instance decidableMemRange (f : G ->* N) [Fintype G] [DecidableEq N] : DecidablePred (· in f.range) :=
  fun _ => Fintype.decidableExistsFintype

-- this instance can't go just after the definition of `mrange` because `Fintype` is
-- not imported at that stage
/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
presence of `Fintype N`. -/
@[to_additive /-- The range of a finite additive monoid under an additive monoid homomorphism is
finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the presence
of `Fintype N`. -/]
/--
Instance `fintypeMrange` / 实例 `fintypeMrange`

English:
instance fintypeMrange
  signature: {M N : Type*} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
  body: Set.fintypeRange f

中文:
实例 fintypeMrange
  签名: {M N : 类型} [幺半群 M] [幺半群 N] [有限类型 M] [DecidableEq N]
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeMrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
    (f : M ->* N) : Fintype (mrange f) :=
  Set.fintypeRange f

/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/
@[to_additive
/-- The range of a finite additive group under an additive group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/]
/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype G] [DecidableEq N] (f : G ->* N)
  body: Set.fintypeRange f

中文:
实例 fintypeRange
  签名: [有限类型 G] [DecidableEq N] (f : G ->* N)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype G] [DecidableEq N] (f : G ->* N) : Fintype (range f) :=
  Set.fintypeRange f

/--
lemma `_root_.Fintype.card_coeSort_mrange` / 引理 `_root_.Fintype.card_coeSort_mrange`

English:
lemma _root_.Fintype.card_coeSort_mrange
  statement: {M N : Type*} [Monoid M] [Monoid N] [Fintype M]
  proof: Set.card_range_of_injective hf

中文:
引理 _root_.有限类型.card_coeSort_mrange
  结论: {M N : 类型} [幺半群 M] [幺半群 N] [有限类型 M]
  证明: Set.card_range_of_injective hf

Depends on / 依赖: Set.card_range_of_injective, card_range_of_injective
-/
lemma _root_.Fintype.card_coeSort_mrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M]
    [DecidableEq N] {f : M ->* N} (hf : Function.Injective f) :
    Fintype.card (mrange f) = Fintype.card M :=
  Set.card_range_of_injective hf

/--
lemma `_root_.Fintype.card_coeSort_range` / 引理 `_root_.Fintype.card_coeSort_range`

English:
lemma _root_.Fintype.card_coeSort_range
  statement: [Fintype G] [DecidableEq N] {f : G ->* N}
  proof: Set.card_range_of_injective hf

中文:
引理 _root_.有限类型.card_coeSort_range
  结论: [有限类型 G] [DecidableEq N] {f : G ->* N}
  证明: Set.card_range_of_injective hf

Depends on / 依赖: Set.card_range_of_injective, card_range_of_injective
-/
lemma _root_.Fintype.card_coeSort_range [Fintype G] [DecidableEq N] {f : G ->* N}
    (hf : Function.Injective f) :
    Fintype.card (range f) = Fintype.card G :=
  Set.card_range_of_injective hf

end MonoidHom
