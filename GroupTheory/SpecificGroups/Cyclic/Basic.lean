/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cyclic groups

`IsCyclic` is a predicate on a group stating that the group is cyclic.
For the concrete cyclic group of order `n`, see `Data.ZMod.Basic`.

* `isCyclic_of_prime_card` proves that a finite group of prime order is cyclic.

cyclic group
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal Field

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

@[to_additive]
/--
theorem `IsCyclic.exists_generator` / 定理 `IsCyclic.exists_generator`

English:
theorem IsCyclic.exists_generator
  given: [Group α] [IsCyclic α]
  statement: exists g : α, forall x, x in zpowers g
  proof: exists_zpow_surjective α

@[to_additive]

中文:
定理 是循环.存在_generator
  条件: [群 α] [是循环 α]
  结论: 存在 g : α, 对任意 x, x in zpowers g
  证明: exists_zpow_surjective α

@[to_additive]

Depends on / 依赖: exists_zpow_surjective
-/
theorem IsCyclic.exists_generator [Group α] [IsCyclic α] : exists g : α, forall x, x in zpowers g :=
  exists_zpow_surjective α

@[to_additive]
/--
theorem `isCyclic_iff_exists_zpowers_eq_top` / 定理 `isCyclic_iff_exists_zpowers_eq_top`

English:
theorem isCyclic_iff_exists_zpowers_eq_top
  given: [Group α]
  statement: IsCyclic α ↔ exists g : α, zpowers g = ⊤
  proof: by
  simp only [eq_top_iff', mem_zpowers_iff]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[to_additive]

中文:
定理 isCyclic_iff_存在_zpowers_eq_top
  条件: [群 α]
  结论: 是循环 α ↔ 存在 g : α, zpowers g = ⊤
  证明: by
  simp only [eq_top_iff', mem_zpowers_iff]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[to_additive]

Depends on / 依赖: eq_top_iff, mem_zpowers_iff
-/
theorem isCyclic_iff_exists_zpowers_eq_top [Group α] : IsCyclic α ↔ exists g : α, zpowers g = ⊤ := by
  simp only [eq_top_iff', mem_zpowers_iff]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[to_additive]
/--
theorem `Subgroup.isCyclic_iff_exists_zpowers_eq_top` / 定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`

English:
theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top
  given: [Group α] (H : Subgroup α)
  proof: by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  simp_rw [← map_subtype_inj, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g => and_iff_right_of_imp fun h => h ▸ mem_zpowers g

@[to_additive]

中文:
定理 子群.isCyclic_iff_存在_zpowers_eq_top
  条件: [群 α] (H : 子群 α)
  证明: by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  simp_rw [← map_subtype_inj, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g => and_iff_right_of_imp fun h => h ▸ mem_zpowers g

@[to_additive]
-/
protected theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top [Group α] (H : Subgroup α) :
    IsCyclic H ↔ exists g : α, Subgroup.zpowers g = H := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  simp_rw [← map_subtype_inj, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g => and_iff_right_of_imp fun h => h ▸ mem_zpowers g

@[to_additive]
/--
Instance `Subgroup.isCyclic_zpowers` / 实例 `Subgroup.isCyclic_zpowers`

English:
instance Subgroup.isCyclic_zpowers
  signature: [Group G] (g : G)
  body: (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨g, rfl⟩

@[to_additive]

中文:
实例 子群.isCyclic_zpowers
  签名: [群 G] (g : G)
  定义体: (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨g, rfl⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.isCyclic_iff_exists_zpowers_eq_top, isCyclic_iff_exists_zpowers_eq_top
-/
instance Subgroup.isCyclic_zpowers [Group G] (g : G) :
    IsCyclic (Subgroup.zpowers g) :=
  (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨g, rfl⟩

@[to_additive]
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α :=
  ⟨⟨1, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

@[simp]
/--
theorem `isCyclic_multiplicative_iff` / 定理 `isCyclic_multiplicative_iff`

English:
theorem isCyclic_multiplicative_iff
  given: [SubNegMonoid α]
  proof: ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩

中文:
定理 isCyclic_multiplicative_iff
  条件: [SubNeg幺半群 α]
  证明: ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩
-/
theorem isCyclic_multiplicative_iff [SubNegMonoid α] :
    IsCyclic (Multiplicative α) ↔ IsAddCyclic α :=
  ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩

/--
Instance `isCyclic_multiplicative` / 实例 `isCyclic_multiplicative`

English:
instance isCyclic_multiplicative
  signature: [AddGroup α] [IsAddCyclic α]
  body: isCyclic_multiplicative_iff.mpr inferInstance

@[simp]

中文:
实例 isCyclic_multiplicative
  签名: [加法群 α] [是加法循环 α]
  定义体: isCyclic_multiplicative_iff.mpr inferInstance

@[simp]

Depends on / 依赖: isCyclic_multiplicative_iff, isCyclic_multiplicative_iff.mpr
-/
instance isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplicative α) :=
  isCyclic_multiplicative_iff.mpr inferInstance

@[simp]
/--
theorem `isAddCyclic_additive_iff` / 定理 `isAddCyclic_additive_iff`

English:
theorem isAddCyclic_additive_iff
  given: [DivInvMonoid α]
  statement: IsAddCyclic (Additive α) ↔ IsCyclic α
  proof: ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩

中文:
定理 isAddCyclic_additive_iff
  条件: [除逆幺半群 α]
  结论: 是加法循环 (加性 α) ↔ 是循环 α
  证明: ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩
-/
theorem isAddCyclic_additive_iff [DivInvMonoid α] : IsAddCyclic (Additive α) ↔ IsCyclic α :=
  ⟨fun H => ⟨H.1⟩, fun H => ⟨H.1⟩⟩

/--
Instance `isAddCyclic_additive` / 实例 `isAddCyclic_additive`

English:
instance isAddCyclic_additive
  signature: [Group α] [IsCyclic α]
  body: isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]

中文:
实例 isAddCyclic_additive
  签名: [群 α] [是循环 α]
  定义体: isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]

Depends on / 依赖: isAddCyclic_additive_iff, isAddCyclic_additive_iff.mpr
-/
instance isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α) :=
  isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]
/--
Instance `IsCyclic.isMulCommutative` / 实例 `IsCyclic.isMulCommutative`

English:
instance IsCyclic.isMulCommutative
  signature: [Group α] [IsCyclic α]
  body: let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

中文:
实例 是循环.isMulCommutative
  签名: [群 α] [是循环 α]
  定义体: let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, exists_generator, zpow_mul_comm
-/
instance IsCyclic.isMulCommutative [Group α] [IsCyclic α] : IsMulCommutative α where
  is_comm.comm x y :=
    let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

open scoped IsMulCommutative in
/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive (attr := instance_reducible)
      /-- A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`. -/]
/--
Definition of `IsCyclic.commGroup` / `IsCyclic.commGroup` 的定义

English:
definition IsCyclic.commGroup
  signature: [Group α] [IsCyclic α]
  body: inferInstance

中文:
定义 是循环.commGroup
  签名: [群 α] [是循环 α]
  定义体: inferInstance
-/
def IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α :=
  inferInstance

variable [Group α] [Group G] [Group G']

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive /-- A non-cyclic additive group is non-trivial. -/]
/--
theorem `Nontrivial.of_not_isCyclic` / 定理 `Nontrivial.of_not_isCyclic`

English:
theorem Nontrivial.of_not_isCyclic
  given: (nc : ¬IsCyclic α)
  statement: Nontrivial α
  proof: by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]

中文:
定理 非平凡.of_not_isCyclic
  条件: (nc : ¬是循环 α)
  结论: 非平凡 α
  证明: by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]

Depends on / 依赖: contrapose, isCyclic_of_subsingleton
-/
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]
/--
theorem `MonoidHom.map_cyclic` / 定理 `MonoidHom.map_cyclic`

English:
theorem MonoidHom.map_cyclic
  given: [h : IsCyclic G] (σ : G ->* G)
  proof: by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow]; rw [← hm]; rw [← zpow_mul]; rw [← zpow_mul']

@[to_additive]

中文:
定理 幺半群态射.map_cyclic
  条件: [h : 是循环 G] (σ : G ->* G)
  证明: by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow]; rw [← hm]; rw [← zpow_mul]; rw [← zpow_mul']

@[to_additive]

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, exists_generator, map_zpow, zpow_mul
-/
theorem MonoidHom.map_cyclic [h : IsCyclic G] (σ : G ->* G) :
    exists m : Int, forall g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow]; rw [← hm]; rw [← zpow_mul]; rw [← zpow_mul']

@[to_additive]
/--
lemma `isCyclic_iff_exists_orderOf_eq_natCard` / 引理 `isCyclic_iff_exists_orderOf_eq_natCard`

English:
lemma isCyclic_iff_exists_orderOf_eq_natCard
  given: [Finite α]
  proof: by
  simp_rw [isCyclic_iff_exists_zpowers_eq_top, ← card_eq_iff_eq_top, Nat.card_zpowers]

@[to_additive]

中文:
引理 isCyclic_iff_存在_orderOf_eq_natCard
  条件: [有限 α]
  证明: by
  simp_rw [isCyclic_iff_exists_zpowers_eq_top, ← card_eq_iff_eq_top, Nat.card_zpowers]

@[to_additive]

Depends on / 依赖: Nat.card_zpowers, card_eq_iff_eq_top, card_zpowers, isCyclic_iff_exists_zpowers_eq_top, simp_rw
-/
lemma isCyclic_iff_exists_orderOf_eq_natCard [Finite α] :
    IsCyclic α ↔ exists g : α, orderOf g = Nat.card α := by
  simp_rw [isCyclic_iff_exists_zpowers_eq_top, ← card_eq_iff_eq_top, Nat.card_zpowers]

@[to_additive]
/--
lemma `isCyclic_iff_exists_natCard_le_orderOf` / 引理 `isCyclic_iff_exists_natCard_le_orderOf`

English:
lemma isCyclic_iff_exists_natCard_le_orderOf
  given: [Finite α]
  proof: by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  apply exists_congr
  intro g
  exact ⟨Eq.ge, le_antisymm orderOf_le_card⟩

@[to_additive]

中文:
引理 isCyclic_iff_存在_natCard_le_orderOf
  条件: [有限 α]
  证明: by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  apply exists_congr
  intro g
  exact ⟨Eq.ge, le_antisymm orderOf_le_card⟩

@[to_additive]

Depends on / 依赖: Eq.ge, exists_congr, isCyclic_iff_exists_orderOf_eq_natCard, le_antisymm, orderOf_le_card
-/
lemma isCyclic_iff_exists_natCard_le_orderOf [Finite α] :
    IsCyclic α ↔ exists g : α, Nat.card α <= orderOf g := by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  apply exists_congr
  intro g
  exact ⟨Eq.ge, le_antisymm orderOf_le_card⟩

@[to_additive]
/--
theorem `isCyclic_of_orderOf_eq_card` / 定理 `isCyclic_of_orderOf_eq_card`

English:
theorem isCyclic_of_orderOf_eq_card
  given: [Finite α] (x : α) (hx : orderOf x = Nat.card α)
  proof: isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hx⟩

@[to_additive]

中文:
定理 isCyclic_of_orderOf_eq_card
  条件: [有限 α] (x : α) (hx : orderOf x = 自然数.card α)
  证明: isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hx⟩

@[to_additive]

Depends on / 依赖: isCyclic_iff_exists_orderOf_eq_natCard, isCyclic_iff_exists_orderOf_eq_natCard.mpr
-/
theorem isCyclic_of_orderOf_eq_card [Finite α] (x : α) (hx : orderOf x = Nat.card α) :
    IsCyclic α :=
  isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hx⟩

@[to_additive]
/--
theorem `isCyclic_of_card_le_orderOf` / 定理 `isCyclic_of_card_le_orderOf`

English:
theorem isCyclic_of_card_le_orderOf
  given: [Finite α] (x : α) (hx : Nat.card α <= orderOf x)
  proof: isCyclic_iff_exists_natCard_le_orderOf.mpr ⟨x, hx⟩

@[to_additive]

中文:
定理 isCyclic_of_card_le_orderOf
  条件: [有限 α] (x : α) (hx : 自然数.card α <= orderOf x)
  证明: isCyclic_iff_exists_natCard_le_orderOf.mpr ⟨x, hx⟩

@[to_additive]

Depends on / 依赖: isCyclic_iff_exists_natCard_le_orderOf, isCyclic_iff_exists_natCard_le_orderOf.mpr
-/
theorem isCyclic_of_card_le_orderOf [Finite α] (x : α) (hx : Nat.card α <= orderOf x) :
    IsCyclic α :=
  isCyclic_iff_exists_natCard_le_orderOf.mpr ⟨x, hx⟩

@[to_additive]
/--
theorem `Subgroup.eq_bot_or_eq_top_of_prime_card` / 定理 `Subgroup.eq_bot_or_eq_top_of_prime_card`

English:
theorem Subgroup.eq_bot_or_eq_top_of_prime_card
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have := card_subgroup_dvd_card H
  rwa [Nat.dvd_prime hp.1, ← eq_bot_iff_card, card_eq_iff_eq_top] at this

中文:
定理 子群.eq_bot_or_eq_top_of_prime_card
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have := card_subgroup_dvd_card H
  rwa [Nat.dvd_prime hp.1, ← eq_bot_iff_card, card_eq_iff_eq_top] at this

Depends on / 依赖: Finite, Nat.dvd_prime, Nat.finite_of_card_ne_zero, card_eq_iff_eq_top, card_subgroup_dvd_card, dvd_prime, eq_bot_iff_card, finite_of_card_ne_zero, ne_zero
-/
theorem Subgroup.eq_bot_or_eq_top_of_prime_card
    (H : Subgroup G) [hp : Fact (Nat.card G).Prime] : H = ⊥ ∨ H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have := card_subgroup_dvd_card H
  rwa [Nat.dvd_prime hp.1, ← eq_bot_iff_card, card_eq_iff_eq_top] at this

/-- Any non-identity element of a finite group of prime order generates the group. -/
@[to_additive /-- Any non-identity element of a finite group of prime order generates the group. -/]
/--
theorem `zpowers_eq_top_of_prime_card` / 定理 `zpowers_eq_top_of_prime_card`

English:
theorem zpowers_eq_top_of_prime_card
  statement: {p : Nat}
  proof: by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]

中文:
定理 zpowers_eq_top_of_prime_card
  结论: {p : 自然数}
  证明: by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]

Depends on / 依赖: eq_bot_or_eq_top_of_prime_card, or_iff_right, zpowers, zpowers_eq_bot
-/
theorem zpowers_eq_top_of_prime_card {p : Nat}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g != 1) : zpowers g = ⊤ := by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]
/--
theorem `mem_zpowers_of_prime_card` / 定理 `mem_zpowers_of_prime_card`

English:
theorem mem_zpowers_of_prime_card
  statement: {p : Nat} [hp : Fact p.Prime]
  proof: by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]

中文:
定理 mem_zpowers_of_prime_card
  结论: {p : 自然数} [hp : Fact p.素]
  证明: by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_top, mem_top, simp_rw, zpowers_eq_top_of_prime_card
-/
theorem mem_zpowers_of_prime_card {p : Nat} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g != 1) : g' in zpowers g := by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]
/--
theorem `mem_powers_of_prime_card` / 定理 `mem_powers_of_prime_card`

English:
theorem mem_powers_of_prime_card
  statement: {p : Nat} [hp : Fact p.Prime]
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]

中文:
定理 mem_powers_of_prime_card
  结论: {p : 自然数} [hp : Fact p.素]
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]

Depends on / 依赖: Finite, Nat.finite_of_card_ne_zero, finite_of_card_ne_zero, mem_powers_iff_mem_zpowers, mem_zpowers_of_prime_card, ne_zero
-/
theorem mem_powers_of_prime_card {p : Nat} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g != 1) : g' in Submonoid.powers g := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]
/--
theorem `powers_eq_top_of_prime_card` / 定理 `powers_eq_top_of_prime_card`

English:
theorem powers_eq_top_of_prime_card
  statement: {p : Nat}
  proof: by
  ext x
  simp [mem_powers_of_prime_card h hg]

中文:
定理 powers_eq_top_of_prime_card
  结论: {p : 自然数}
  证明: by
  ext x
  simp [mem_powers_of_prime_card h hg]

Depends on / 依赖: mem_powers_of_prime_card
-/
theorem powers_eq_top_of_prime_card {p : Nat}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g != 1) : Submonoid.powers g = ⊤ := by
  ext x
  simp [mem_powers_of_prime_card h hg]

/-- A finite group of prime order is cyclic. -/
@[to_additive /-- A finite group of prime order is cyclic. -/]
/--
theorem `isCyclic_of_prime_card` / 定理 `isCyclic_of_prime_card`

English:
theorem isCyclic_of_prime_card
  statement: {p : Nat} [hp : Fact p.Prime]
  proof: by
  have : Finite α := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.1.one_lt)
  obtain ⟨g, hg⟩ : exists g : α, g != 1 := exists_ne 1
  exact ⟨g, fun g' => mem_zpowers_of_prime_card h hg⟩

中文:
定理 isCyclic_of_prime_card
  结论: {p : 自然数} [hp : Fact p.素]
  证明: by
  have : Finite α := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.1.one_lt)
  obtain ⟨g, hg⟩ : exists g : α, g != 1 := exists_ne 1
  exact ⟨g, fun g' => mem_zpowers_of_prime_card h hg⟩

Depends on / 依赖: Finite, Finite.one_lt_card_iff_nontrivial.mp, Nat.finite_of_card_ne_zero, Nontrivial, exists_ne, finite_of_card_ne_zero, mem_zpowers_of_prime_card, ne_zero, one_lt, one_lt_card_iff_nontrivial
-/
theorem isCyclic_of_prime_card {p : Nat} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsCyclic α := by
  have : Finite α := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.1.one_lt)
  obtain ⟨g, hg⟩ : exists g : α, g != 1 := exists_ne 1
  exact ⟨g, fun g' => mem_zpowers_of_prime_card h hg⟩

/-- A finite group of order dividing a prime is cyclic. -/
@[to_additive /-- A finite group of order dividing a prime is cyclic. -/]
/--
theorem `isCyclic_of_card_dvd_prime` / 定理 `isCyclic_of_card_dvd_prime`

English:
theorem isCyclic_of_card_dvd_prime
  statement: {p : Nat} [hp : Fact p.Prime]
  proof: by
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · exact isCyclic_of_prime_card h

@[to_additive]

中文:
定理 isCyclic_of_card_dvd_prime
  结论: {p : 自然数} [hp : Fact p.素]
  证明: by
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · exact isCyclic_of_prime_card h

@[to_additive]

Depends on / 依赖: Nat.card_eq_one_iff_unique.mp, Nat.dvd_prime, card_eq_one_iff_unique, dvd_prime, hp.out, isCyclic_of_prime_card, isCyclic_of_subsingleton
-/
theorem isCyclic_of_card_dvd_prime {p : Nat} [hp : Fact p.Prime]
    (h : Nat.card α ∣ p) : IsCyclic α := by
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · exact isCyclic_of_prime_card h

@[to_additive]
/--
theorem `isCyclic_of_surjective` / 定理 `isCyclic_of_surjective`

English:
theorem isCyclic_of_surjective
  statement: {F : Type*} [hH : IsCyclic G']
  proof: by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]

中文:
定理 isCyclic_of_surjective
  结论: {F : 类型} [hH : 是循环 G']
  证明: by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]

Depends on / 依赖: map_zpow
-/
theorem isCyclic_of_surjective {F : Type*} [hH : IsCyclic G']
    [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective f) :
    IsCyclic G := by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]
/--
theorem `MulEquiv.isCyclic` / 定理 `MulEquiv.isCyclic`

English:
theorem MulEquiv.isCyclic
  given: (e : G ≃* G')
  proof: ⟨fun _ => isCyclic_of_surjective e e.surjective,
    fun _ => isCyclic_of_surjective e.symm e.symm.surjective⟩

@[to_additive]

中文:
定理 乘法等价.isCyclic
  条件: (e : G ≃* G')
  证明: ⟨fun _ => isCyclic_of_surjective e e.surjective,
    fun _ => isCyclic_of_surjective e.symm e.symm.surjective⟩

@[to_additive]

Depends on / 依赖: e.surjective, e.symm, e.symm.surjective, isCyclic_of_surjective, surjective
-/
theorem MulEquiv.isCyclic (e : G ≃* G') :
    IsCyclic G ↔ IsCyclic G' :=
  ⟨fun _ => isCyclic_of_surjective e e.surjective,
    fun _ => isCyclic_of_surjective e.symm e.symm.surjective⟩

@[to_additive]
/--
theorem `orderOf_eq_card_of_forall_mem_zpowers` / 定理 `orderOf_eq_card_of_forall_mem_zpowers`

English:
theorem orderOf_eq_card_of_forall_mem_zpowers
  given: {g : α} (hx : forall x, x in zpowers g)
  proof: by
  rw [← Nat.card_zpowers]; rw [(zpowers g).eq_top_iff'.mpr hx]; rw [card_top]

@[to_additive]

中文:
定理 orderOf_eq_card_of_对任意_mem_zpowers
  条件: {g : α} (hx : 对任意 x, x in zpowers g)
  证明: by
  rw [← Nat.card_zpowers]; rw [(zpowers g).eq_top_iff'.mpr hx]; rw [card_top]

@[to_additive]

Depends on / 依赖: Nat.card_zpowers, card_top, card_zpowers, eq_top_iff, zpowers
-/
theorem orderOf_eq_card_of_forall_mem_zpowers {g : α} (hx : forall x, x in zpowers g) :
    orderOf g = Nat.card α := by
  rw [← Nat.card_zpowers]; rw [(zpowers g).eq_top_iff'.mpr hx]; rw [card_top]

@[to_additive]
/--
theorem `orderOf_eq_card_of_forall_mem_powers` / 定理 `orderOf_eq_card_of_forall_mem_powers`

English:
theorem orderOf_eq_card_of_forall_mem_powers
  given: {g : α} (hx : forall x, x in Submonoid.powers g)
  proof: by
  rw [orderOf_eq_card_of_forall_mem_zpowers]
  exact fun x => Submonoid.powers_le_zpowers _ (hx _)

@[to_additive]

中文:
定理 orderOf_eq_card_of_对任意_mem_powers
  条件: {g : α} (hx : 对任意 x, x in 子幺半群.powers g)
  证明: by
  rw [orderOf_eq_card_of_forall_mem_zpowers]
  exact fun x => Submonoid.powers_le_zpowers _ (hx _)

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.powers_le_zpowers, orderOf_eq_card_of_forall_mem_zpowers, powers_le_zpowers
-/
theorem orderOf_eq_card_of_forall_mem_powers {g : α} (hx : forall x, x in Submonoid.powers g) :
    orderOf g = Nat.card α := by
  rw [orderOf_eq_card_of_forall_mem_zpowers]
  exact fun x => Submonoid.powers_le_zpowers _ (hx _)

@[to_additive]
/--
theorem `orderOf_eq_card_of_zpowers_eq_top` / 定理 `orderOf_eq_card_of_zpowers_eq_top`

English:
theorem orderOf_eq_card_of_zpowers_eq_top
  given: {g : G} (h : Subgroup.zpowers g = ⊤)
  proof: orderOf_eq_card_of_forall_mem_zpowers fun _ => h.ge (Subgroup.mem_top _)

@[to_additive]

中文:
定理 orderOf_eq_card_of_zpowers_eq_top
  条件: {g : G} (h : 子群.zpowers g = ⊤)
  证明: orderOf_eq_card_of_forall_mem_zpowers fun _ => h.ge (Subgroup.mem_top _)

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_top, h.ge, mem_top, orderOf_eq_card_of_forall_mem_zpowers
-/
theorem orderOf_eq_card_of_zpowers_eq_top {g : G} (h : Subgroup.zpowers g = ⊤) :
    orderOf g = Nat.card G :=
  orderOf_eq_card_of_forall_mem_zpowers fun _ => h.ge (Subgroup.mem_top _)

@[to_additive]
/--
theorem `exists_pow_ne_one_of_isCyclic` / 定理 `exists_pow_ne_one_of_isCyclic`

English:
theorem exists_pow_ne_one_of_isCyclic
  statement: [G_cyclic : IsCyclic G]
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt k_lt_card_G)
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert! orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_zpowers]; rw [eq_comm]; rw [card_eq_iff_eq_top]; rw [eq_top_iff]
  exact fun x _ => ha x

@[to_additive]

中文:
定理 存在_pow_ne_one_of_isCyclic
  结论: [G_cyclic : 是循环 G]
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt k_lt_card_G)
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert! orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_zpowers]; rw [eq_comm]; rw [card_eq_iff_eq_top]; rw [eq_top_iff]
  exact fun x _ => ha x

@[to_additive]

Depends on / 依赖: Finite, G_cyclic, Nat.card_zpowers, Nat.finite_of_card_ne_zero, Nat.ne_zero_of_lt, bot_lt, card_eq_iff_eq_top, card_zpowers, contrapose, convert, eq_comm, eq_top_iff, finite_of_card_ne_zero, k_lt_card_G, k_pos, k_pos.bot_lt, ne_zero_of_lt, orderOf_le_of_pow_eq_one
-/
theorem exists_pow_ne_one_of_isCyclic [G_cyclic : IsCyclic G]
    {k : Nat} (k_pos : k != 0) (k_lt_card_G : k < Nat.card G) : exists a : G, a ^ k != 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt k_lt_card_G)
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert! orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_zpowers]; rw [eq_comm]; rw [card_eq_iff_eq_top]; rw [eq_top_iff]
  exact fun x _ => ha x

@[to_additive]
/--
theorem `Infinite.orderOf_eq_zero_of_forall_mem_zpowers` / 定理 `Infinite.orderOf_eq_zero_of_forall_mem_zpowers`

English:
theorem Infinite.orderOf_eq_zero_of_forall_mem_zpowers
  statement: [Infinite α] {g : α}
  proof: by
  rw [orderOf_eq_card_of_forall_mem_zpowers h]; rw [Nat.card_eq_zero_of_infinite]

@[to_additive]

中文:
定理 无限.orderOf_eq_zero_of_对任意_mem_zpowers
  结论: [无限 α] {g : α}
  证明: by
  rw [orderOf_eq_card_of_forall_mem_zpowers h]; rw [Nat.card_eq_zero_of_infinite]

@[to_additive]

Depends on / 依赖: Nat.card_eq_zero_of_infinite, card_eq_zero_of_infinite, orderOf_eq_card_of_forall_mem_zpowers
-/
theorem Infinite.orderOf_eq_zero_of_forall_mem_zpowers [Infinite α] {g : α}
    (h : forall x, x in zpowers g) : orderOf g = 0 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers h]; rw [Nat.card_eq_zero_of_infinite]

@[to_additive]
/--
Instance `Bot.isCyclic` / 实例 `Bot.isCyclic`

English:
instance Bot.isCyclic
  signature: : IsCyclic (⊥ : Subgroup α)
  body: ⟨⟨1, fun x => ⟨0, Subtype.ext (zpow_zero (1 : α)).trans Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]

中文:
实例 底元素.isCyclic
  签名: : 是循环 (⊥ : 子群 α)
  定义体: ⟨⟨1, fun x => ⟨0, Subtype.ext (zpow_zero (1 : α)).trans Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]

Depends on / 依赖: Eq.symm, Subgroup, Subgroup.mem_bot, Subtype, Subtype.ext, mem_bot, zpow_zero
-/
instance Bot.isCyclic : IsCyclic (⊥ : Subgroup α) :=
⟨⟨1, fun x => ⟨0, Subtype.ext (zpow_zero (1 : α)).trans Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]
/--
Instance `Subgroup.isCyclic` / 实例 `Subgroup.isCyclic`

English:
instance Subgroup.isCyclic
  signature: [IsCyclic α] (H : Subgroup α)
  body: haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : exists x : α, x in H ∧ x != (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : exists n : Nat, 0 < n ∧ g ^ n in H :=
      ⟨k.natAbs,
Nat.pos_of_ne_zero fun h => hx₂ by
          rw [← hk]; rw [Int.natAbs_eq_zero.mp h]; rw [zpow_zero], by
            rcases k with k | k
            · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                ← Int.ofNat_eq_natCast, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) in H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : Int) in H :=
(Subgroup.mul_mem_cancel_right H hk₂).1 by
            rw [← zpow_add]; rw [Int.emod_add_mul_ediv]; rw [hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs in H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : Int)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : Int),
          Subtype.ext_iff.2
            (by
              suffices g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆))]; rw [hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

@[to_additive]

中文:
实例 子群.isCyclic
  签名: [是循环 α] (H : 子群 α)
  定义体: haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : exists x : α, x in H ∧ x != (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : exists n : Nat, 0 < n ∧ g ^ n in H :=
      ⟨k.natAbs,
Nat.pos_of_ne_zero fun h => hx₂ by
          rw [← hk]; rw [Int.natAbs_eq_zero.mp h]; rw [zpow_zero], by
            rcases k with k | k
            · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                ← Int.ofNat_eq_natCast, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) in H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : Int) in H :=
(Subgroup.mul_mem_cancel_right H hk₂).1 by
            rw [← zpow_add]; rw [Int.emod_add_mul_ediv]; rw [hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs in H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : Int)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : Int),
          Subtype.ext_iff.2
            (by
              suffices g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆))]; rw [hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

@[to_additive]

Depends on / 依赖: Classical, Classical.propDecidable, Int.natAbs_eq_zero.mp, Int.natAbs_natCast, Int.natAbs_ne, Int.ofNat_eq_natCast, IsCyclic, IsCyclic.exists_generator, Nat.pos_of_ne_zero, exists_generator, k.natAbs, natAbs, natAbs_eq_zero, natAbs_natCast, natAbs_ne, ofNat_eq_natCast, pos_of_ne_zero, propDecidable, zpow_natCast, zpow_zero
-/
instance Subgroup.isCyclic [IsCyclic α] (H : Subgroup α) : IsCyclic H :=
  haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : exists x : α, x in H ∧ x != (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : exists n : Nat, 0 < n ∧ g ^ n in H :=
      ⟨k.natAbs,
Nat.pos_of_ne_zero fun h => hx₂ by
          rw [← hk]; rw [Int.natAbs_eq_zero.mp h]; rw [zpow_zero], by
            rcases k with k | k
            · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                ← Int.ofNat_eq_natCast, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) in H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : Int) in H :=
(Subgroup.mul_mem_cancel_right H hk₂).1 by
            rw [← zpow_add]; rw [Int.emod_add_mul_ediv]; rw [hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs in H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : Int)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : Int),
          Subtype.ext_iff.2
            (by
              suffices g ^ ((Nat.find hex : Int) * (k / Nat.find hex : Int)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆))]; rw [hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

@[to_additive]
/--
theorem `isCyclic_of_injective` / 定理 `isCyclic_of_injective`

English:
theorem isCyclic_of_injective
  given: [IsCyclic G'] (f : G ->* G') (hf : Function.Injective f)
  proof: isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MonoidHom.ofInjective hf).symm.surjective

@[to_additive]

中文:
定理 isCyclic_of_injective
  条件: [是循环 G'] (f : G ->* G') (hf : 函数.单射 f)
  证明: isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MonoidHom.ofInjective hf).symm.surjective

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.ofInjective, isCyclic_of_surjective, ofInjective, surjective, symm.surjective
-/
theorem isCyclic_of_injective [IsCyclic G'] (f : G ->* G') (hf : Function.Injective f) :
    IsCyclic G :=
  isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MonoidHom.ofInjective hf).symm.surjective

@[to_additive]
/--
lemma `Subgroup.isCyclic_of_le` / 引理 `Subgroup.isCyclic_of_le`

English:
lemma Subgroup.isCyclic_of_le
  given: {H H' : Subgroup G} (h : H <= H') [IsCyclic H']
  statement: IsCyclic H
  proof: isCyclic_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

@[to_additive]

中文:
引理 子群.isCyclic_of_le
  条件: {H H' : 子群 G} (h : H <= H') [是循环 H']
  结论: 是循环 H
  证明: isCyclic_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.inclusion, Subgroup.inclusion_injective, inclusion, inclusion_injective, isCyclic_of_injective
-/
lemma Subgroup.isCyclic_of_le {H H' : Subgroup G} (h : H <= H') [IsCyclic H'] : IsCyclic H :=
  isCyclic_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

@[to_additive]
/--
theorem `Subgroup.le_zpowers_iff` / 定理 `Subgroup.le_zpowers_iff`

English:
theorem Subgroup.le_zpowers_iff
  given: (g : G) (H : Subgroup G)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp (isCyclic_of_le h)
obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h (mem_zpowers x)
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by rw [zpow_natCast]⟩
    · exact ⟨n, by simp⟩
  · rintro ⟨k, rfl⟩
exact zpowers_le_of_mem npow_mem_zpowers g k

中文:
定理 子群.le_zpowers_iff
  条件: (g : G) (H : 子群 G)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp (isCyclic_of_le h)
obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h (mem_zpowers x)
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by rw [zpow_natCast]⟩
    · exact ⟨n, by simp⟩
  · rintro ⟨k, rfl⟩
exact zpowers_le_of_mem npow_mem_zpowers g k

Depends on / 依赖: H.isCyclic_iff_exists_zpowers_eq_top, Int.eq_nat_or_neg, eq_nat_or_neg, isCyclic_iff_exists_zpowers_eq_top, isCyclic_of_le, mem_zpowers, mem_zpowers_iff, mem_zpowers_iff.mp, npow_mem_zpowers, zpow_natCast, zpowers_le_of_mem
-/
theorem Subgroup.le_zpowers_iff (g : G) (H : Subgroup G) :
    H <= Subgroup.zpowers g ↔ exists n : Nat, H = Subgroup.zpowers (g ^ n) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp (isCyclic_of_le h)
obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h (mem_zpowers x)
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by rw [zpow_natCast]⟩
    · exact ⟨n, by simp⟩
  · rintro ⟨k, rfl⟩
exact zpowers_le_of_mem npow_mem_zpowers g k

open Finset Nat

section Classical

open scoped Classical in
@[to_additive IsAddCyclic.card_nsmul_eq_zero_le]
/--
theorem `IsCyclic.card_pow_eq_one_le` / 定理 `IsCyclic.card_pow_eq_one_le`

English:
theorem IsCyclic.card_pow_eq_one_le
  given: [DecidableEq α] [Fintype α] [IsCyclic α] {n : Nat} (hn0 : 0 < n)
  proof: let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} <=
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset := by
      gcongr
      intro x hx
let ⟨m, hm⟩ := show x in Submonoid.powers g from mem_powers_iff_mem_zpowers.2 hg x
      refine Set.mem_toFinset.2 ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : Nat), ?_⟩
      dsimp only at ⊢ hm
      rw [zpow_natCast]; rw [← pow_mul]; rw [Nat.mul_div_cancel_left']; rw [hm]
      refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
      conv_lhs =>
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]; rw [← Nat.card_eq_fintype_card]; rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
exact orderOf_dvd_of_pow_eq_one by simpa [pow_mul, hm] using (mem_filter.1 hx).2
    _ <= n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0]; rw [mul_zero]; rw [Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers]; rw [orderOf_pow g]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0)]; rw [gcd_mul_left_left]; rw [hm]; rw [Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)

中文:
定理 是循环.card_pow_eq_one_le
  条件: [DecidableEq α] [有限类型 α] [是循环 α] {n : 自然数} (hn0 : 0 < n)
  证明: let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} <=
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset := by
      gcongr
      intro x hx
let ⟨m, hm⟩ := show x in Submonoid.powers g from mem_powers_iff_mem_zpowers.2 hg x
      refine Set.mem_toFinset.2 ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : Nat), ?_⟩
      dsimp only at ⊢ hm
      rw [zpow_natCast]; rw [← pow_mul]; rw [Nat.mul_div_cancel_left']; rw [hm]
      refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
      conv_lhs =>
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]; rw [← Nat.card_eq_fintype_card]; rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
exact orderOf_dvd_of_pow_eq_one by simpa [pow_mul, hm] using (mem_filter.1 hx).2
    _ <= n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0]; rw [mul_zero]; rw [Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers]; rw [orderOf_pow g]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0)]; rw [gcd_mul_left_left]; rw [hm]; rw [Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)

Depends on / 依赖: Fintype, Fintype.card, IsCyclic, IsCyclic.exists_generator, Nat.dvd_of_mul_dvd_mul_right, Nat.gcd, Nat.mul_div_cancel_left, Set.mem_toFinset, Submonoid, Submonoid.powers, dvd_of_mul_dvd_mul_right, exists_generator, gcd_pos_of_pos, mem_powers_iff_mem_zpowers, mem_toFinset, mul_div_cancel_left, pow_mul, powers, toFinset, zpow_natCast
-/
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : Nat} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} <= n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} <=
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset := by
      gcongr
      intro x hx
let ⟨m, hm⟩ := show x in Submonoid.powers g from mem_powers_iff_mem_zpowers.2 hg x
      refine Set.mem_toFinset.2 ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : Nat), ?_⟩
      dsimp only at ⊢ hm
      rw [zpow_natCast]; rw [← pow_mul]; rw [Nat.mul_div_cancel_left']; rw [hm]
      refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
      conv_lhs =>
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]; rw [← Nat.card_eq_fintype_card]; rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
exact orderOf_dvd_of_pow_eq_one by simpa [pow_mul, hm] using (mem_filter.1 hx).2
    _ <= n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0]; rw [mul_zero]; rw [Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers]; rw [orderOf_pow g]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0)]; rw [gcd_mul_left_left]; rw [hm]; rw [Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)

end Classical

@[to_additive]
/--
theorem `IsCyclic.exists_monoid_generator` / 定理 `IsCyclic.exists_monoid_generator`

English:
theorem IsCyclic.exists_monoid_generator
  given: [Finite α] [IsCyclic α]
  proof: by
  simp_rw [mem_powers_iff_mem_zpowers]
  exact IsCyclic.exists_generator

@[to_additive]

中文:
定理 是循环.存在_monoid_generator
  条件: [有限 α] [是循环 α]
  证明: by
  simp_rw [mem_powers_iff_mem_zpowers]
  exact IsCyclic.exists_generator

@[to_additive]

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, exists_generator, mem_powers_iff_mem_zpowers, simp_rw
-/
theorem IsCyclic.exists_monoid_generator [Finite α] [IsCyclic α] :
    exists x : α, forall y : α, y in Submonoid.powers x := by
  simp_rw [mem_powers_iff_mem_zpowers]
  exact IsCyclic.exists_generator

@[to_additive]
/--
lemma `IsCyclic.exists_ofOrder_eq_natCard` / 引理 `IsCyclic.exists_ofOrder_eq_natCard`

English:
lemma IsCyclic.exists_ofOrder_eq_natCard
  given: [h : IsCyclic α]
  statement: exists g : α, orderOf g = Nat.card α
  proof: by
  obtain ⟨g, hg⟩ := h.exists_generator
  use g
  rw [← card_zpowers g]; rw [(eq_top_iff' (zpowers g)).mpr hg]
  exact Nat.card_congr (Equiv.Set.univ α)

中文:
引理 是循环.存在_ofOrder_eq_natCard
  条件: [h : 是循环 α]
  结论: 存在 g : α, orderOf g = 自然数.card α
  证明: by
  obtain ⟨g, hg⟩ := h.exists_generator
  use g
  rw [← card_zpowers g]; rw [(eq_top_iff' (zpowers g)).mpr hg]
  exact Nat.card_congr (Equiv.Set.univ α)

Depends on / 依赖: Equiv.Set.univ, Nat.card_congr, card_congr, card_zpowers, eq_top_iff, exists_generator, h.exists_generator, zpowers
-/
lemma IsCyclic.exists_ofOrder_eq_natCard [h : IsCyclic α] : exists g : α, orderOf g = Nat.card α := by
  obtain ⟨g, hg⟩ := h.exists_generator
  use g
  rw [← card_zpowers g]; rw [(eq_top_iff' (zpowers g)).mpr hg]
  exact Nat.card_congr (Equiv.Set.univ α)

variable (G) in
/--
Definition of `MulDistribMulAction.toMonoidHomZModOfIsCyclic` / `MulDistribMulAction.toMonoidHomZModOfIsCyclic` 的定义

English:
definition MulDistribMulAction.toMonoidHomZModOfIsCyclic
  signature: (M : Type*) [Monoid M]
  body: (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]; rw [← (MulDistribMulAction.toMonoidHom G 1).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [one_smul]
  map_mul' m n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_mul']; rw [← (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G n).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G (m * n)).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [mul_smul]

中文:
定义 MulDistribMul作用.toMonoidHomZModOfIsCyclic
  签名: (M : 类型) [幺半群 M]
  定义体: (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]; rw [← (MulDistribMulAction.toMonoidHom G 1).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [one_smul]
  map_mul' m n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_mul']; rw [← (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G n).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G (m * n)).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [mul_smul]

Depends on / 依赖: Inhabited, MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_cyclic, map_cyclic.choose, toMonoidHom
-/
noncomputable def MulDistribMulAction.toMonoidHomZModOfIsCyclic (M : Type*) [Monoid M]
    [IsCyclic G] [MulDistribMulAction M G] {n : Nat} (hn : Nat.card G = n) : M ->* ZMod n where
  toFun m := (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]; rw [← (MulDistribMulAction.toMonoidHom G 1).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [one_smul]
  map_mul' m n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul]; rw [ZMod.intCast_eq_intCast_iff]; rw [← hn]; rw [← hg]; rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_mul']; rw [← (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G n).map_cyclic.choose_spec]; rw [← (MulDistribMulAction.toMonoidHom G (m * n)).map_cyclic.choose_spec]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [MulDistribMulAction.toMonoidHom_apply]; rw [mul_smul]

/--
theorem `MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply` / 定理 `MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply`

English:
theorem MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply
  statement: {M : Type*} [Monoid M] [IsCyclic G]
  proof: by
  rw [← MulDistribMulAction.toMonoidHom_apply]; rw [(MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec g]; rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard g))
  rwa [hn, ← ZMod.intCast_eq_intCast_iff]

中文:
定理 MulDistribMul作用.toMonoidHomZModOfIsCyclic_apply
  结论: {M : 类型} [幺半群 M] [是循环 G]
  证明: by
  rw [← MulDistribMulAction.toMonoidHom_apply]; rw [(MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec g]; rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard g))
  rwa [hn, ← ZMod.intCast_eq_intCast_iff]

Depends on / 依赖: Int.ModEq.of_dvd, Int.natCast_dvd_natCast.mpr, MulDistribMulAction, MulDistribMulAction.toMonoidHom, MulDistribMulAction.toMonoidHom_apply, ZMod.intCast_eq_intCast_iff, choose_spec, intCast_eq_intCast_iff, map_cyclic, map_cyclic.choose_spec, natCast_dvd_natCast, of_dvd, orderOf_dvd_natCard, toMonoidHom, toMonoidHom_apply, zpow_eq_zpow_iff_modEq
-/
theorem MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply {M : Type*} [Monoid M] [IsCyclic G]
    [MulDistribMulAction M G] {n : Nat} (hn : Nat.card G = n) (m : M) (g : G) (k : Int)
    (h : toMonoidHomZModOfIsCyclic G M hn m = k) : m • g = g ^ k := by
  rw [← MulDistribMulAction.toMonoidHom_apply]; rw [(MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec g]; rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard g))
  rwa [hn, ← ZMod.intCast_eq_intCast_iff]

section

variable [Fintype α]

@[to_additive]
/--
theorem `IsCyclic.unique_zpow_zmod` / 定理 `IsCyclic.unique_zpow_zmod`

English:
theorem IsCyclic.unique_zpow_zmod
  given: (ha : forall x : α, x in zpowers a) (x : α)
  proof: by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) => ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Nat.card_eq_fintype_card, ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

中文:
定理 是循环.unique_zpow_zmod
  条件: (ha : 对任意 x : α, x in zpowers a) (x : α)
  证明: by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) => ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Nat.card_eq_fintype_card, ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

Depends on / 依赖: Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ZMod.intCast_eq_iff, ZMod.intCast_eq_intCast_iff, card_eq_fintype_card, intCast_eq_iff, intCast_eq_intCast_iff, modEq_comm, modEq_iff_add_fac, orderOf_eq_card_of_forall_mem_zpowers, zpow_eq_zpow_iff_modEq, zpow_natCast
-/
theorem IsCyclic.unique_zpow_zmod (ha : forall x : α, x in zpowers a) (x : α) :
    exists! n : ZMod (Fintype.card α), x = a ^ n.val := by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) => ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Nat.card_eq_fintype_card, ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

variable [DecidableEq α]

@[to_additive]
/--
theorem `IsCyclic.image_range_orderOf` / 定理 `IsCyclic.image_range_orderOf`

English:
theorem IsCyclic.image_range_orderOf
  given: (ha : forall x : α, x in zpowers a)
  proof: by
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]

中文:
定理 是循环.image_range_orderOf
  条件: (ha : 对任意 x : α, x in zpowers a)
  证明: by
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, Set.toFinset_univ, Subsingleton, _root_, _root_.image_range_orderOf, eq_univ_iff_forall, image_range_orderOf, instSubsingleton, toFinset_univ
-/
theorem IsCyclic.image_range_orderOf (ha : forall x : α, x in zpowers a) :
    Finset.image (fun i => a ^ i) (range (orderOf a)) = univ := by
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]
/--
theorem `IsCyclic.image_range_card` / 定理 `IsCyclic.image_range_card`

English:
theorem IsCyclic.image_range_card
  given: (ha : forall x : α, x in zpowers a)
  proof: by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha]; rw [IsCyclic.image_range_orderOf ha]

@[to_additive]

中文:
定理 是循环.image_range_card
  条件: (ha : 对任意 x : α, x in zpowers a)
  证明: by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha]; rw [IsCyclic.image_range_orderOf ha]

@[to_additive]

Depends on / 依赖: IsCyclic, IsCyclic.image_range_orderOf, image_range_orderOf, orderOf_eq_card_of_forall_mem_zpowers
-/
theorem IsCyclic.image_range_card (ha : forall x : α, x in zpowers a) :
    Finset.image (fun i => a ^ i) (range (Nat.card α)) = univ := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha]; rw [IsCyclic.image_range_orderOf ha]

@[to_additive]
/--
lemma `IsCyclic.ext` / 引理 `IsCyclic.ext`

English:
lemma IsCyclic.ext
  statement: [Finite G] [IsCyclic G] {d : Nat} {a b : ZMod d}
  proof: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

中文:
引理 是循环.ext
  结论: [有限 G] [是循环 G] {d : 自然数} {a b : ZMod d}
  证明: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, ZMod.cast_id, ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, cast_id, exists_generator, hGcard, natCast_eq_natCast_iff, natCast_val, orderOf_eq_card_of_forall_mem_zpowers, pow_eq_pow_iff_modEq, specialize
-/
lemma IsCyclic.ext [Finite G] [IsCyclic G] {d : Nat} {a b : ZMod d}
    (hGcard : Nat.card G = d) (h : forall t : G, t ^ a.val = t ^ b.val) : a = b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq]; rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

end

end Cyclic

end
