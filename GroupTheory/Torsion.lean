/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Rank
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `Monoid.IsTorsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `CommGroup.torsion G`, the torsion subgroup of an abelian group `G`
* `CommMonoid.torsion G`, the above stated for commutative monoids
* `Monoid.IsTorsionFree`, asserting no nontrivial elements have finite order in `G`
* `AddMonoid.IsTorsion` and `AddMonoid.IsTorsionFree` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `Monoid.IsTorsion.group`), but since
the definition can be stated on monoids it is implemented on `Monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/

@[expose] public section


variable {G H : Type*}

section

variable (G) [Monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive
/-- A predicate on an additive monoid saying that all elements are of finite order. -/]
/--
Definition of `IsMulTorsion` / `IsMulTorsion` 的定义

English:
definition IsMulTorsion
  body: forall g : G, IsOfFinOrder g

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion := IsMulTorsion
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion := IsAddTorsion

中文:
定义 IsMulTorsion
  定义体: forall g : G, IsOfFinOrder g

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion := IsMulTorsion
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion := IsAddTorsion

Depends on / 依赖: IsOfFinOrder
-/
def IsMulTorsion :=
  forall g : G, IsOfFinOrder g

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion := IsMulTorsion
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion := IsAddTorsion

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp)
/-- An additive monoid is not a torsion additive monoid if it has an element of infinite order. -/]
/--
theorem `not_isMulTorsion_iff` / 定理 `not_isMulTorsion_iff`

English:
theorem not_isMulTorsion_iff
  statement: ¬IsMulTorsion G ↔ exists g : G, ¬IsOfFinOrder g
  proof: not_forall

@[deprecated (since := "2026-07-01")] alias Monoid.not_isTorsion_iff := not_isMulTorsion_iff
@[deprecated (since := "2026-07-01")] alias AddMonoid.not_isTorsion_iff := not_isAddTorsion_iff

中文:
定理 not_isMulTorsion_iff
  结论: ¬IsMulTorsion G ↔ 存在 g : G, ¬IsOfFinOrder g
  证明: not_forall

@[deprecated (since := "2026-07-01")] alias Monoid.not_isTorsion_iff := not_isMulTorsion_iff
@[deprecated (since := "2026-07-01")] alias AddMonoid.not_isTorsion_iff := not_isAddTorsion_iff

Depends on / 依赖: not_forall
-/
theorem not_isMulTorsion_iff : ¬IsMulTorsion G ↔ exists g : G, ¬IsOfFinOrder g :=
  not_forall

@[deprecated (since := "2026-07-01")] alias Monoid.not_isTorsion_iff := not_isMulTorsion_iff
@[deprecated (since := "2026-07-01")] alias AddMonoid.not_isTorsion_iff := not_isAddTorsion_iff

end

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive (attr := instance_reducible)
/-- Torsion additive monoids are really additive groups. -/]
/--
Definition of `IsMulTorsion.group` / `IsMulTorsion.group` 的定义

English:
definition IsMulTorsion.group
  signature: [Monoid G] (tG : IsMulTorsion G)
  body: { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

@[deprecated (since := "2026-07-01")] alias IsTorsion.group := IsMulTorsion.group
@[deprecated (since := "2026-07

中文:
定义 IsMulTorsion.group
  签名: [Monoid G] (tG : IsMulTorsion G)
  定义体: { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

@[deprecated (since := "2026-07-01")] alias IsTorsion.group := IsMulTorsion.group
@[deprecated (since := "2026-07

Depends on / 依赖: Monoid, inv_mul_cancel, orderOf, orderOf_pos, pow_orderOf_eq_one, pow_succ, tsub_add_cancel_of_le
-/
noncomputable def IsMulTorsion.group [Monoid G] (tG : IsMulTorsion G) : Group G :=
  { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ]; rw [tsub_add_cancel_of_le]; rw [pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

@[deprecated (since := "2026-07-01")] alias IsTorsion.group := IsMulTorsion.group
@[deprecated (since := "2026-07-01")] alias IsTorsion.addGroup := IsAddTorsion.addGroup

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive /-- Additive subgroups of torsion additive groups are torsion additive groups. -/]
/--
theorem `IsMulTorsion.subgroup` / 定理 `IsMulTorsion.subgroup`

English:
theorem IsMulTorsion.subgroup
  given: (tG : IsMulTorsion G) (H : Subgroup G)
  statement: IsMulTorsion H
  proof: fun h =>
Submonoid.isOfFinOrder_coe.1 tG h

@[deprecated (since := "2026-07-01")] alias IsTorsion.subgroup := IsMulTorsion.subgroup
@[deprecated (since := "2026-07-01")] alias IsTorsion.addSubgroup := IsAddTorsion.addSubgroup

中文:
定理 IsMulTorsion.subgroup
  条件: (tG : IsMulTorsion G) (H : Subgroup G)
  结论: IsMulTorsion H
  证明: fun h =>
Submonoid.isOfFinOrder_coe.1 tG h

@[deprecated (since := "2026-07-01")] alias IsTorsion.subgroup := IsMulTorsion.subgroup
@[deprecated (since := "2026-07-01")] alias IsTorsion.addSubgroup := IsAddTorsion.addSubgroup
-/
theorem IsMulTorsion.subgroup (tG : IsMulTorsion G) (H : Subgroup G) : IsMulTorsion H := fun h =>
Submonoid.isOfFinOrder_coe.1 tG h

@[deprecated (since := "2026-07-01")] alias IsTorsion.subgroup := IsMulTorsion.subgroup
@[deprecated (since := "2026-07-01")] alias IsTorsion.addSubgroup := IsAddTorsion.addSubgroup

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive
/-- The image of a surjective torsion additive group homomorphism is torsion. -/]
/--
theorem `IsMulTorsion.of_surjective` / 定理 `IsMulTorsion.of_surjective`

English:
theorem IsMulTorsion.of_surjective
  given: {f : G ->* H} (hf : Function.Surjective f) (tG : IsMulTorsion G)
  proof: fun h => by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

@[deprecated (since := "2026-06-30")] alias IsTorsion.of_surjective := IsMulTorsion.of_surjective
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.of_surjective := IsAddTorsion.of_surjective

中文:
定理 IsMulTorsion.of_surjective
  条件: {f : G ->* H} (hf : Function.Surjective f) (tG : IsMulTorsion G)
  证明: fun h => by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

@[deprecated (since := "2026-06-30")] alias IsTorsion.of_surjective := IsMulTorsion.of_surjective
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.of_surjective := IsAddTorsion.of_surjective

Depends on / 依赖: f.isOfFinOrder, isOfFinOrder
-/
theorem IsMulTorsion.of_surjective {f : G ->* H} (hf : Function.Surjective f) (tG : IsMulTorsion G) :
    IsMulTorsion H := fun h => by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

@[deprecated (since := "2026-06-30")] alias IsTorsion.of_surjective := IsMulTorsion.of_surjective
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.of_surjective := IsAddTorsion.of_surjective

/-- Torsion groups are closed under extensions. -/
@[to_additive
/-- Torsion additive groups are closed under extensions. -/]
/--
theorem `IsMulTorsion.extension_closed` / 定理 `IsMulTorsion.extension_closed`

English:
theorem IsMulTorsion.extension_closed
  statement: {f : G ->* H} (hN : N = f.ker) (tH : IsMulTorsion H)
  proof: fun g => by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ngn * nn, mul

中文:
定理 IsMulTorsion.extension_closed
  结论: {f : G ->* H} (hN : N = f.ker) (tH : IsMulTorsion H)
  证明: fun g => by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ngn * nn, mul

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker.mpr, Subgroup, Subgroup.coe_one, Subgroup.coe_pow, coe_one, coe_pow, exists_pow_eq_one, f.map_pow, hN.symm, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, map_pow, mem_ker, mul_pos, ngnpos, pow_mul
-/
theorem IsMulTorsion.extension_closed {f : G ->* H} (hN : N = f.ker) (tH : IsMulTorsion H)
    (tN : IsMulTorsion N) : IsMulTorsion G := fun g => by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ngn * nn, mul_pos ngnpos nnpos, by
    rw [pow_mul]; rw [← h]; rw [← Subgroup.coe_pow]; rw [hnn]; rw [Subgroup.coe_one]⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.extension_closed :=
  IsMulTorsion.extension_closed
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.extension_closed :=
  IsAddTorsion.extension_closed

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive
/-- The image of a quotient is torsion iff the additive group is torsion. -/]
/--
theorem `IsMulTorsion.quotient_iff` / 定理 `IsMulTorsion.quotient_iff`

English:
theorem IsMulTorsion.quotient_iff
  statement: {f : G ->* H} (hf : Function.Surjective f) (hN : N = f.ker)
  proof: ⟨fun tH => IsMulTorsion.extension_closed hN tH tN, fun tG => IsMulTorsion.of_surjective hf tG⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.quotient_iff := IsMulTorsion.quotient_iff
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.quotient_iff := IsAddTorsion.quotient_iff

中文:
定理 IsMulTorsion.quotient_iff
  结论: {f : G ->* H} (hf : Function.Surjective f) (hN : N = f.ker)
  证明: ⟨fun tH => IsMulTorsion.extension_closed hN tH tN, fun tG => IsMulTorsion.of_surjective hf tG⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.quotient_iff := IsMulTorsion.quotient_iff
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.quotient_iff := IsAddTorsion.quotient_iff

Depends on / 依赖: IsMulTorsion, IsMulTorsion.extension_closed, IsMulTorsion.of_surjective, extension_closed, of_surjective
-/
theorem IsMulTorsion.quotient_iff {f : G ->* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsMulTorsion N) : IsMulTorsion H ↔ IsMulTorsion G :=
  ⟨fun tH => IsMulTorsion.extension_closed hN tH tN, fun tG => IsMulTorsion.of_surjective hf tG⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.quotient_iff := IsMulTorsion.quotient_iff
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.quotient_iff := IsAddTorsion.quotient_iff

/-- If a group exponent exists, the group is torsion. -/
@[to_additive
/-- If a group exponent exists, the additive group is torsion. -/]
/--
theorem `ExponentExists.isMulTorsion` / 定理 `ExponentExists.isMulTorsion`

English:
theorem ExponentExists.isMulTorsion
  given: (h : ExponentExists G)
  statement: IsMulTorsion G
  proof: fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

@[deprecated (since := "2026-06-30")] alias ExponentExists.isTorsion := ExponentExists.isMulTorsion
@[deprecated (since := "2026-06-30")] alias ExponentExists.is_add_torsion :=
  ExponentExists.isAddTors

中文:
定理 ExponentExists.isMulTorsion
  条件: (h : ExponentExists G)
  结论: IsMulTorsion G
  证明: fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

@[deprecated (since := "2026-06-30")] alias ExponentExists.isTorsion := ExponentExists.isMulTorsion
@[deprecated (since := "2026-06-30")] alias ExponentExists.is_add_torsion :=
  ExponentExists.isAddTors

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr
-/
theorem ExponentExists.isMulTorsion (h : ExponentExists G) : IsMulTorsion G := fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

@[deprecated (since := "2026-06-30")] alias ExponentExists.isTorsion := ExponentExists.isMulTorsion
@[deprecated (since := "2026-06-30")] alias ExponentExists.is_add_torsion :=
  ExponentExists.isAddTorsion

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive
/-- The group exponent exists for any bounded torsion additive group. -/]
/--
theorem `IsMulTorsion.exponentExists` / 定理 `IsMulTorsion.exponentExists`

English:
theorem IsMulTorsion.exponentExists
  statement: (tG : IsMulTorsion G)
  proof: exponent_ne_zero.mp
    (exponent_ne_zero_iff_range_orderOf_finite fun g => (tG g).orderOf_pos).mpr bounded

@[deprecated (since := "2026-07-01")] alias IsTorsion.exponentExists := IsMulTorsion.exponentExists

中文:
定理 IsMulTorsion.exponentExists
  结论: (tG : IsMulTorsion G)
  证明: exponent_ne_zero.mp
    (exponent_ne_zero_iff_range_orderOf_finite fun g => (tG g).orderOf_pos).mpr bounded

@[deprecated (since := "2026-07-01")] alias IsTorsion.exponentExists := IsMulTorsion.exponentExists

Depends on / 依赖: bounded, exponent_ne_zero, exponent_ne_zero.mp, exponent_ne_zero_iff_range_orderOf_finite, orderOf_pos
-/
theorem IsMulTorsion.exponentExists (tG : IsMulTorsion G)
    (bounded : (Set.range fun g : G => orderOf g).Finite) : ExponentExists G :=
exponent_ne_zero.mp
    (exponent_ne_zero_iff_range_orderOf_finite fun g => (tG g).orderOf_pos).mpr bounded

@[deprecated (since := "2026-07-01")] alias IsTorsion.exponentExists := IsMulTorsion.exponentExists

/-- Finite groups are torsion groups. -/
@[to_additive /-- Finite additive groups are torsion additive groups. -/]
/--
theorem `isMulTorsion_of_finite` / 定理 `isMulTorsion_of_finite`

English:
theorem isMulTorsion_of_finite
  given: [Finite G]
  statement: IsMulTorsion G
  proof: ExponentExists.isMulTorsion .of_finite

@[deprecated (since := "2026-06-30")] alias isTorsion_of_finite := isMulTorsion_of_finite
@[deprecated (since := "2026-06-30")] alias is_add_torsion_of_finite := isAddTorsion_of_finite

中文:
定理 isMulTorsion_of_finite
  条件: [Finite G]
  结论: IsMulTorsion G
  证明: ExponentExists.isMulTorsion .of_finite

@[deprecated (since := "2026-06-30")] alias isTorsion_of_finite := isMulTorsion_of_finite
@[deprecated (since := "2026-06-30")] alias is_add_torsion_of_finite := isAddTorsion_of_finite

Depends on / 依赖: ExponentExists, ExponentExists.isMulTorsion, isMulTorsion, of_finite
-/
theorem isMulTorsion_of_finite [Finite G] : IsMulTorsion G :=
  ExponentExists.isMulTorsion .of_finite

@[deprecated (since := "2026-06-30")] alias isTorsion_of_finite := isMulTorsion_of_finite
@[deprecated (since := "2026-06-30")] alias is_add_torsion_of_finite := isAddTorsion_of_finite

end Group

section CommGroup
variable [CommGroup G]

/-- A nontrivial torsion abelian group is not torsion-free. -/
@[to_additive /-- A nontrivial torsion additive abelian group is not torsion-free. -/]
/--
lemma `not_isMulTorsionFree_of_isMulTorsion` / 引理 `not_isMulTorsionFree_of_isMulTorsion`

English:
lemma not_isMulTorsionFree_of_isMulTorsion
  given: [Nontrivial G] (hG : IsMulTorsion G)
  proof: not_isMulTorsionFree_iff_isOfFinOrder.2 let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

@[deprecated (since := "2026-07-01")] alias not_isMulTorsionFree_of_isTorsion :=
  not_isMulTorsionFree_of_isMulTorsion
@[deprecated (since := "2026-07-01")] alias not_isAddTorsionFree_of_isTorsion :=
  not_isAd

中文:
引理 not_isMulTorsionFree_of_isMulTorsion
  条件: [Nontrivial G] (hG : IsMulTorsion G)
  证明: not_isMulTorsionFree_iff_isOfFinOrder.2 let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

@[deprecated (since := "2026-07-01")] alias not_isMulTorsionFree_of_isTorsion :=
  not_isMulTorsionFree_of_isMulTorsion
@[deprecated (since := "2026-07-01")] alias not_isAddTorsionFree_of_isTorsion :=
  not_isAd

Depends on / 依赖: exists_ne, not_isMulTorsionFree_iff_isOfFinOrder
-/
lemma not_isMulTorsionFree_of_isMulTorsion [Nontrivial G] (hG : IsMulTorsion G) :
    ¬ IsMulTorsionFree G :=
not_isMulTorsionFree_iff_isOfFinOrder.2 let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

@[deprecated (since := "2026-07-01")] alias not_isMulTorsionFree_of_isTorsion :=
  not_isMulTorsionFree_of_isMulTorsion
@[deprecated (since := "2026-07-01")] alias not_isAddTorsionFree_of_isTorsion :=
  not_isAddTorsionFree_of_isAddTorsion

/-- A nontrivial torsion-free abelian group is not torsion. -/
@[to_additive /-- A nontrivial torsion-free additive abelian group is not torsion. -/]
/--
lemma `not_isMulTorsion_of_isMulTorsionFree` / 引理 `not_isMulTorsion_of_isMulTorsionFree`

English:
lemma not_isMulTorsion_of_isMulTorsionFree
  given: [Nontrivial G] [IsMulTorsionFree G]
  statement: ¬ IsMulTorsion G
  proof: (not_isMulTorsionFree_of_isMulTorsion · ‹_›)

@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isMulTorsionFree :=
  not_isMulTorsion_of_isMulTorsionFree
@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isAddTorsionFree :=
  not_isAddTorsion_of_isAddTorsionFree

中文:
引理 not_isMulTorsion_of_isMulTorsionFree
  条件: [Nontrivial G] [IsMulTorsionFree G]
  结论: ¬ IsMulTorsion G
  证明: (not_isMulTorsionFree_of_isMulTorsion · ‹_›)

@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isMulTorsionFree :=
  not_isMulTorsion_of_isMulTorsionFree
@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isAddTorsionFree :=
  not_isAddTorsion_of_isAddTorsionFree

Depends on / 依赖: not_isMulTorsionFree_of_isMulTorsion
-/
lemma not_isMulTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] : ¬ IsMulTorsion G :=
  (not_isMulTorsionFree_of_isMulTorsion · ‹_›)

@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isMulTorsionFree :=
  not_isMulTorsion_of_isMulTorsionFree
@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isAddTorsionFree :=
  not_isAddTorsion_of_isAddTorsionFree

end CommGroup

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

/--
theorem `IsAddTorsion.module_of_torsion` / 定理 `IsAddTorsion.module_of_torsion`

English:
theorem IsAddTorsion.module_of_torsion
  given: [Semiring R] [Module R M] (tR : IsAddTorsion R)
  proof: fun f => isOfFinAddOrder_iff_nsmul_eq_zero.mpr by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_torsion :=
  IsAddTorsio

中文:
定理 IsAddTorsion.module_of_torsion
  条件: [Semiring R] [Module R M] (tR : IsAddTorsion R)
  证明: fun f => isOfFinAddOrder_iff_nsmul_eq_zero.mpr by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_torsion :=
  IsAddTorsio

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, exists_nsmul_eq_zero, isOfFinAddOrder_iff_nsmul_eq_zero, isOfFinAddOrder_iff_nsmul_eq_zero.mpr, nsmul_one, zero_smul
-/
theorem IsAddTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsAddTorsion R) :
    IsAddTorsion M :=
fun f => isOfFinAddOrder_iff_nsmul_eq_zero.mpr by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_torsion :=
  IsAddTorsion.module_of_torsion

/--
theorem `IsAddTorsion.module_of_finite` / 定理 `IsAddTorsion.module_of_finite`

English:
theorem IsAddTorsion.module_of_finite
  given: [Ring R] [Finite R] [Module R M]
  statement: IsAddTorsion M
  proof: (isAddTorsion_of_finite : IsAddTorsion R).module_of_torsion _ _

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_finite :=
  IsAddTorsion.module_of_finite

中文:
定理 IsAddTorsion.module_of_finite
  条件: [Ring R] [Finite R] [Module R M]
  结论: IsAddTorsion M
  证明: (isAddTorsion_of_finite : IsAddTorsion R).module_of_torsion _ _

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_finite :=
  IsAddTorsion.module_of_finite

Depends on / 依赖: IsAddTorsion, isAddTorsion_of_finite, module_of_torsion
-/
theorem IsAddTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsAddTorsion M :=
  (isAddTorsion_of_finite : IsAddTorsion R).module_of_torsion _ _

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_finite :=
  IsAddTorsion.module_of_finite

end Module

section CommMonoid

variable (G) [CommMonoid G] [CommMonoid H]

namespace CommMonoid

/-- The torsion submonoid of a commutative monoid.

(Note that by `IsMulTorsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive addTorsion /-- The torsion additive submonoid of an additive commutative monoid. -/]
/--
Definition of `torsion` / `torsion` 的定义

English:
definition torsion
  signature: : Submonoid G where
  body: { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

@[to_additive]

中文:
定义 torsion
  签名: : Submonoid G where
  定义体: { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

@[to_additive]

Depends on / 依赖: IsOfFinOrder
-/
def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

@[to_additive]
/--
theorem `mem_torsion` / 定理 `mem_torsion`

English:
theorem mem_torsion
  given: (g : G)
  statement: g in torsion G ↔ IsOfFinOrder g
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_torsion
  条件: (g : G)
  结论: g in torsion G ↔ IsOfFinOrder g
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
/--
lemma `torsion_prod` / 引理 `torsion_prod`

English:
lemma torsion_prod
  statement: torsion (G × H) = (torsion G).prod (torsion H)
  proof: by
  simp [Submonoid.ext_iff, Submonoid.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

中文:
引理 torsion_prod
  结论: torsion (G × H) = (torsion G).prod (torsion H)
  证明: by
  simp [Submonoid.ext_iff, Submonoid.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.prod_iff, Submonoid, Submonoid.ext_iff, Submonoid.mem_prod, ext_iff, mem_prod, mem_torsion, prod_iff
-/
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Submonoid.ext_iff, Submonoid.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Torsion submonoids are torsion. -/
@[to_additive /-- Torsion additive submonoids are torsion. -/]
/--
theorem `torsion.isMulTorsion` / 定理 `torsion.isMulTorsion`

English:
theorem torsion.isMulTorsion
  statement: IsMulTorsion torsion G
  proof: fun ⟨x, n, npos, hn⟩ =>
  ⟨n, npos,
Subtype.ext by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one]; rw [SubmonoidClass.coe_pow]; rw [Subtype.coe_mk]; rw [(isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

@[deprecated (since := "2026-07-01")] alias torsion.isTorsio

中文:
定理 torsion.isMulTorsion
  结论: IsMulTorsion torsion G
  证明: fun ⟨x, n, npos, hn⟩ =>
  ⟨n, npos,
Subtype.ext by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one]; rw [SubmonoidClass.coe_pow]; rw [Subtype.coe_mk]; rw [(isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

@[deprecated (since := "2026-07-01")] alias torsion.isTorsio
-/
theorem torsion.isMulTorsion : IsMulTorsion torsion G := fun ⟨x, n, npos, hn⟩ =>
  ⟨n, npos,
Subtype.ext by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one]; rw [SubmonoidClass.coe_pow]; rw [Subtype.coe_mk]; rw [(isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

@[deprecated (since := "2026-07-01")] alias torsion.isTorsion := torsion.isMulTorsion
@[deprecated (since := "2026-07-01")] alias _root_.AddCommMonoid.addTorsion.isTorsion :=
  AddCommMonoid.addTorsion.isAddTorsion

variable (G) (p : Nat)

/-- The `p`-primary component is the submonoid of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the submonoid of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
/--
Definition of `primaryComponent` / `primaryComponent` 的定义

English:
definition primaryComponent
  signature: : Submonoid G where
  body: { g | exists k : Nat, g ^ p ^ k = 1 }
  one_mem' := ⟨0, by simp⟩
  mul_mem' := fun {a b} ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by
    rw [mul_pow]; rw [pow_add]; rw [pow_mul]; rw [hm]; rw [one_pow]; rw [one_mul]; rw [mul_comm]; rw [pow_mul]; rw [hn]; rw [one_pow]⟩

中文:
定义 primaryComponent
  签名: : Submonoid G where
  定义体: { g | exists k : Nat, g ^ p ^ k = 1 }
  one_mem' := ⟨0, by simp⟩
  mul_mem' := fun {a b} ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by
    rw [mul_pow]; rw [pow_add]; rw [pow_mul]; rw [hm]; rw [one_pow]; rw [one_mul]; rw [mul_comm]; rw [pow_mul]; rw [hn]; rw [one_pow]⟩
-/
def primaryComponent : Submonoid G where
  carrier := { g | exists k : Nat, g ^ p ^ k = 1 }
  one_mem' := ⟨0, by simp⟩
  mul_mem' := fun {a b} ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by
    rw [mul_pow]; rw [pow_add]; rw [pow_mul]; rw [hm]; rw [one_pow]; rw [one_mul]; rw [mul_comm]; rw [pow_mul]; rw [hn]; rw [one_pow]⟩

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
/--
theorem `mem_primaryComponent` / 定理 `mem_primaryComponent`

English:
theorem mem_primaryComponent
  given: {g : G}
  statement: g in primaryComponent G p ↔ exists k : Nat, g ^ p ^ k = 1
  proof: .rfl

中文:
定理 mem_primaryComponent
  条件: {g : G}
  结论: g in primaryComponent G p ↔ 存在 k : 自然数, g ^ p ^ k = 1
  证明: .rfl
-/
theorem mem_primaryComponent {g : G} : g in primaryComponent G p ↔ exists k : Nat, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
/--
theorem `mem_primaryComponent_iff_orderOf` / 定理 `mem_primaryComponent_iff_orderOf`

English:
theorem mem_primaryComponent_iff_orderOf
  given: [Fact p.Prime] {g : G}
  proof: exists_orderOf_eq_prime_pow_iff.symm

中文:
定理 mem_primaryComponent_iff_orderOf
  条件: [Fact p.Prime] {g : G}
  证明: exists_orderOf_eq_prime_pow_iff.symm

Depends on / 依赖: exists_orderOf_eq_prime_pow_iff, exists_orderOf_eq_prime_pow_iff.symm
-/
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g in primaryComponent G p ↔ exists n : Nat, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

variable [hp : Fact p.Prime]

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive primaryComponent.exists_orderOf_eq_prime_nsmul
/-- Elements of the `p`-primary component have additive order `p^n` for some `n`. -/]
/--
theorem `primaryComponent.exists_orderOf_eq_prime_pow` / 定理 `primaryComponent.exists_orderOf_eq_prime_pow`

English:
theorem primaryComponent.exists_orderOf_eq_prime_pow
  given: (g : CommMonoid.primaryComponent G p)
  proof: by
  rw [← orderOf_submonoid]; rw [← mem_primaryComponent_iff_orderOf]
  exact g.property

中文:
定理 primaryComponent.exists_orderOf_eq_prime_pow
  条件: (g : CommMonoid.primaryComponent G p)
  证明: by
  rw [← orderOf_submonoid]; rw [← mem_primaryComponent_iff_orderOf]
  exact g.property

Depends on / 依赖: g.property, mem_primaryComponent_iff_orderOf, orderOf_submonoid, property
-/
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    exists n : Nat, orderOf g = p ^ n := by
  rw [← orderOf_submonoid]; rw [← mem_primaryComponent_iff_orderOf]
  exact g.property

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive /-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/]
/--
theorem `primaryComponent.disjoint` / 定理 `primaryComponent.disjoint`

English:
theorem primaryComponent.disjoint
  given: {p' : Nat} [hp' : Fact p'.Prime] (hne : p != p')
  proof: Submonoid.disjoint_def.mpr fun {g} hg hg' => by
    rw [mem_primaryComponent_iff_orderOf] at hg hg'
    obtain ⟨_ | n, hn⟩ := hg
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · obtain ⟨_, hn'⟩ := hg'
      exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn ▸ hn')) hne

中文:
定理 primaryComponent.disjoint
  条件: {p' : 自然数} [hp' : Fact p'.Prime] (hne : p != p')
  证明: Submonoid.disjoint_def.mpr fun {g} hg hg' => by
    rw [mem_primaryComponent_iff_orderOf] at hg hg'
    obtain ⟨_ | n, hn⟩ := hg
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · obtain ⟨_, hn'⟩ := hg'
      exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn ▸ hn')) hne

Depends on / 依赖: Submonoid, Submonoid.disjoint_def.mpr, absurd, disjoint_def, eq_of_prime_pow_eq, hp.out.prime, mem_primaryComponent_iff_orderOf, n.succ_pos, orderOf_eq_one_iff, out.prime, pow_zero, succ_pos
-/
theorem primaryComponent.disjoint {p' : Nat} [hp' : Fact p'.Prime] (hne : p != p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr fun {g} hg hg' => by
    rw [mem_primaryComponent_iff_orderOf] at hg hg'
    obtain ⟨_ | n, hn⟩ := hg
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · obtain ⟨_, hn'⟩ := hg'
      exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn ▸ hn')) hne

end CommMonoid

open CommMonoid (torsion)

namespace IsMulTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp)
/-- The torsion additive submonoid of a torsion additive monoid is `⊤`. -/]
/--
theorem `torsion_eq_top` / 定理 `torsion_eq_top`

English:
theorem torsion_eq_top
  given: (tG : IsMulTorsion G)
  statement: torsion G = ⊤
  proof: by ext; tauto

中文:
定理 torsion_eq_top
  条件: (tG : IsMulTorsion G)
  结论: torsion G = ⊤
  证明: by ext; tauto
-/
theorem torsion_eq_top (tG : IsMulTorsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive (attr := simps!)
/-- A torsion additive monoid is isomorphic to its torsion additive submonoid. -/]
/--
Definition of `torsionMulEquiv` / `torsionMulEquiv` 的定义

English:
definition torsionMulEquiv
  signature: (tG : IsMulTorsion G)
  body: (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

中文:
定义 torsionMulEquiv
  签名: (tG : IsMulTorsion G)
  定义体: (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

Depends on / 依赖: MulEquiv, MulEquiv.submonoidCongr, Submonoid, Submonoid.topEquiv, submonoidCongr, tG.torsion_eq_top, topEquiv, torsion_eq_top
-/
def torsionMulEquiv (tG : IsMulTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

end IsMulTorsion

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsion_eq_top :=
  IsMulTorsion.torsion_eq_top
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsion_eq_top :=
  IsAddTorsion.torsion_eq_top

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv :=
  IsMulTorsion.torsionMulEquiv
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv :=
  IsAddTorsion.torsionAddEquiv

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_apply :=
  IsMulTorsion.torsionMulEquiv_apply
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_apply :=
  IsAddTorsion.torsionAddEquiv_apply

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe :=
  IsMulTorsion.torsionMulEquiv_symm_apply_coe
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_symm_apply_coe :=
  IsAddTorsion.torsionAddEquiv_symm_apply_coe

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[to_additive (attr := simp)
/-- Torsion additive submonoids of a torsion additive submonoid are
isomorphic to the additive submonoid. -/]
/--
Definition of `CommMonoid.Torsion.ofTorsion` / `CommMonoid.Torsion.ofTorsion` 的定义

English:
definition CommMonoid.Torsion.ofTorsion
  signature: : torsion (torsion G) ≃* torsion G
  body: IsMulTorsion.torsionMulEquiv CommMonoid.torsion.isMulTorsion

@[deprecated (since := "2026-07-01")] alias Torsion.ofTorsion := CommMonoid.Torsion.ofTorsion

中文:
定义 CommMonoid.Torsion.ofTorsion
  签名: : torsion (torsion G) ≃* torsion G
  定义体: IsMulTorsion.torsionMulEquiv CommMonoid.torsion.isMulTorsion

@[deprecated (since := "2026-07-01")] alias Torsion.ofTorsion := CommMonoid.Torsion.ofTorsion

Depends on / 依赖: CommMonoid, CommMonoid.torsion.isMulTorsion, IsMulTorsion, IsMulTorsion.torsionMulEquiv, isMulTorsion, torsion, torsionMulEquiv
-/
def CommMonoid.Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  IsMulTorsion.torsionMulEquiv CommMonoid.torsion.isMulTorsion

@[deprecated (since := "2026-07-01")] alias Torsion.ofTorsion := CommMonoid.Torsion.ofTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G] [CommGroup H]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive /-- The torsion additive subgroup of an additive abelian group. -/]
/--
Definition of `torsion` / `torsion` 的定义

English:
definition torsion
  signature: : Subgroup G
  body: { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }

中文:
定义 torsion
  签名: : Subgroup G
  定义体: { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }

Depends on / 依赖: CommMonoid, CommMonoid.torsion, IsOfFinOrder, IsOfFinOrder.inv, inv_mem, torsion
-/
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive
/-- The torsion additive submonoid of an abelian group equals the torsion
additive subgroup as an additive submonoid. -/]
/--
theorem `torsion_eq_torsion_submonoid` / 定理 `torsion_eq_torsion_submonoid`

English:
theorem torsion_eq_torsion_submonoid
  statement: CommMonoid.torsion G = (torsion G).toSubmonoid
  proof: rfl

@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.add_torsion_eq_add_torsion_submonoid :=
  AddCommGroup.torsion_eq_torsion_addSubmonoid

中文:
定理 torsion_eq_torsion_submonoid
  结论: CommMonoid.torsion G = (torsion G).toSubmonoid
  证明: rfl

@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.add_torsion_eq_add_torsion_submonoid :=
  AddCommGroup.torsion_eq_torsion_addSubmonoid
-/
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl

@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.add_torsion_eq_add_torsion_submonoid :=
  AddCommGroup.torsion_eq_torsion_addSubmonoid

variable {G}

@[to_additive]
/--
theorem `mem_torsion` / 定理 `mem_torsion`

English:
theorem mem_torsion
  given: (g : G)
  statement: g in torsion G ↔ IsOfFinOrder g
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_torsion
  条件: (g : G)
  结论: g in torsion G ↔ IsOfFinOrder g
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
/--
lemma `torsion_eq_top_iff` / 引理 `torsion_eq_top_iff`

English:
lemma torsion_eq_top_iff
  statement: torsion G = ⊤ ↔ IsMulTorsion G
  proof: (torsion G).eq_top_iff'

@[to_additive]

中文:
引理 torsion_eq_top_iff
  结论: torsion G = ⊤ ↔ IsMulTorsion G
  证明: (torsion G).eq_top_iff'

@[to_additive]

Depends on / 依赖: eq_top_iff, torsion
-/
lemma torsion_eq_top_iff : torsion G = ⊤ ↔ IsMulTorsion G :=
  (torsion G).eq_top_iff'

@[to_additive]
/--
lemma `isMulTorsionFree_iff_torsion_eq_bot` / 引理 `isMulTorsionFree_iff_torsion_eq_bot`

English:
lemma isMulTorsionFree_iff_torsion_eq_bot
  statement: IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥
  proof: by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]; rw [eq_bot_iff]; rw [SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

@[to_additive]

中文:
引理 isMulTorsionFree_iff_torsion_eq_bot
  结论: IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥
  证明: by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]; rw [eq_bot_iff]; rw [SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

@[to_additive]

Depends on / 依赖: CommGroup, CommGroup.mem_torsion, SetLike, SetLike.le_def, eq_bot_iff, isMulTorsionFree_iff_not_isOfFinOrder, le_def, mem_torsion, not_imp_not
-/
lemma isMulTorsionFree_iff_torsion_eq_bot : IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]; rw [eq_bot_iff]; rw [SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

@[to_additive]
/--
lemma `le_comap_torsion` / 引理 `le_comap_torsion`

English:
lemma le_comap_torsion
  given: (f : G ->* H)
  statement: torsion G <= (torsion H).comap f
  proof: by
  intro x
  exact f.isOfFinOrder

@[to_additive]

中文:
引理 le_comap_torsion
  条件: (f : G ->* H)
  结论: torsion G <= (torsion H).comap f
  证明: by
  intro x
  exact f.isOfFinOrder

@[to_additive]

Depends on / 依赖: f.isOfFinOrder, isOfFinOrder
-/
lemma le_comap_torsion (f : G ->* H) : torsion G <= (torsion H).comap f := by
  intro x
  exact f.isOfFinOrder

@[to_additive]
/--
lemma `map_torsion_le` / 引理 `map_torsion_le`

English:
lemma map_torsion_le
  given: (f : G ->* H)
  statement: (torsion G).map f <= torsion H
  proof: Subgroup.map_le_iff_le_comap.mpr (le_comap_torsion f)

@[to_additive]

中文:
引理 map_torsion_le
  条件: (f : G ->* H)
  结论: (torsion G).map f <= torsion H
  证明: Subgroup.map_le_iff_le_comap.mpr (le_comap_torsion f)

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.map_le_iff_le_comap.mpr, le_comap_torsion, map_le_iff_le_comap
-/
lemma map_torsion_le (f : G ->* H) : (torsion G).map f <= torsion H :=
  Subgroup.map_le_iff_le_comap.mpr (le_comap_torsion f)

@[to_additive]
/--
lemma `comap_torsion_of_injective` / 引理 `comap_torsion_of_injective`

English:
lemma comap_torsion_of_injective
  given: {f : G ->* H} (hf : Function.Injective f)
  proof: by
  ext x
  exact hf.isOfFinOrder_iff

@[to_additive]

中文:
引理 comap_torsion_of_injective
  条件: {f : G ->* H} (hf : Function.Injective f)
  证明: by
  ext x
  exact hf.isOfFinOrder_iff

@[to_additive]

Depends on / 依赖: hf.isOfFinOrder_iff, isOfFinOrder_iff
-/
lemma comap_torsion_of_injective {f : G ->* H} (hf : Function.Injective f) :
    (torsion H).comap f = torsion G := by
  ext x
  exact hf.isOfFinOrder_iff

@[to_additive]
/--
lemma `_root_.MulEquiv.comap_torsion` / 引理 `_root_.MulEquiv.comap_torsion`

English:
lemma _root_.MulEquiv.comap_torsion
  given: (e : G ≃* H)
  statement: (torsion H).comap e = torsion G
  proof: comap_torsion_of_injective e.injective

@[to_additive]

中文:
引理 _root_.MulEquiv.comap_torsion
  条件: (e : G ≃* H)
  结论: (torsion H).comap e = torsion G
  证明: comap_torsion_of_injective e.injective

@[to_additive]

Depends on / 依赖: comap_torsion_of_injective, e.injective, injective
-/
lemma _root_.MulEquiv.comap_torsion (e : G ≃* H) : (torsion H).comap e = torsion G :=
  comap_torsion_of_injective e.injective

@[to_additive]
/--
lemma `_root_.MulEquiv.map_torsion` / 引理 `_root_.MulEquiv.map_torsion`

English:
lemma _root_.MulEquiv.map_torsion
  given: (e : G ≃* H)
  statement: (torsion G).map e = torsion H
  proof: by
  rw [Subgroup.map_equiv_eq_comap_symm]; rw [e.symm.comap_torsion]

@[to_additive]

中文:
引理 _root_.MulEquiv.map_torsion
  条件: (e : G ≃* H)
  结论: (torsion G).map e = torsion H
  证明: by
  rw [Subgroup.map_equiv_eq_comap_symm]; rw [e.symm.comap_torsion]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.map_equiv_eq_comap_symm, comap_torsion, e.symm.comap_torsion, map_equiv_eq_comap_symm
-/
lemma _root_.MulEquiv.map_torsion (e : G ≃* H) : (torsion G).map e = torsion H := by
  rw [Subgroup.map_equiv_eq_comap_symm]; rw [e.symm.comap_torsion]

@[to_additive]
/--
lemma `torsion_prod` / 引理 `torsion_prod`

English:
lemma torsion_prod
  statement: torsion (G × H) = (torsion G).prod (torsion H)
  proof: by
  simp [Subgroup.ext_iff, Subgroup.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

中文:
引理 torsion_prod
  结论: torsion (G × H) = (torsion G).prod (torsion H)
  证明: by
  simp [Subgroup.ext_iff, Subgroup.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

Depends on / 依赖: IsOfFinOrder, IsOfFinOrder.prod_iff, Subgroup, Subgroup.ext_iff, Subgroup.mem_prod, ext_iff, mem_prod, mem_torsion, prod_iff
-/
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Subgroup.ext_iff, Subgroup.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable (G)

@[to_additive]
/--
lemma `isMulTorsion_quotient_range_powMonoidHom` / 引理 `isMulTorsion_quotient_range_powMonoidHom`

English:
lemma isMulTorsion_quotient_range_powMonoidHom
  given: {n : Nat} (hn : n != 0)
  proof: by
  simp only [IsMulTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g => QuotientGroup.induction_on g fun a => ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow]; rw [QuotientGroup.eq_one_iff]
  simp

@[deprecated (since := "2026-07-01")] alias isTorsion_quotient_range_powMonoidHom :=
  isMulTorsion_

中文:
引理 isMulTorsion_quotient_range_powMonoidHom
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  simp only [IsMulTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g => QuotientGroup.induction_on g fun a => ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow]; rw [QuotientGroup.eq_one_iff]
  simp

@[deprecated (since := "2026-07-01")] alias isTorsion_quotient_range_powMonoidHom :=
  isMulTorsion_

Depends on / 依赖: IsMulTorsion, QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.induction_on, QuotientGroup.mk_pow, eq_one_iff, hn.pos, induction_on, isOfFinOrder_iff_pow_eq_one, mk_pow
-/
lemma isMulTorsion_quotient_range_powMonoidHom {n : Nat} (hn : n != 0) :
    IsMulTorsion (G ⧸ (powMonoidHom (α := G) n).range) := by
  simp only [IsMulTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g => QuotientGroup.induction_on g fun a => ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow]; rw [QuotientGroup.eq_one_iff]
  simp

@[deprecated (since := "2026-07-01")] alias isTorsion_quotient_range_powMonoidHom :=
  isMulTorsion_quotient_range_powMonoidHom
@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.isTorsion_quotient_range_nsmulAddMonoidHom :=
  AddCommGroup.isAddTorsion_quotient_range_nsmulAddMonoidHom

variable (p : Nat)

/-- The `p`-primary component is the subgroup of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the subgroup of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
/--
Definition of `primaryComponent` / `primaryComponent` 的定义

English:
definition primaryComponent
  signature: : Subgroup G
  body: { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨k, hk⟩ => ⟨k, by rw [inv_pow, hk, inv_one]⟩ }

中文:
定义 primaryComponent
  签名: : Subgroup G
  定义体: { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨k, hk⟩ => ⟨k, by rw [inv_pow, hk, inv_one]⟩ }

Depends on / 依赖: CommMonoid, CommMonoid.primaryComponent, inv_mem, inv_one, inv_pow, primaryComponent
-/
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨k, hk⟩ => ⟨k, by rw [inv_pow, hk, inv_one]⟩ }

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
/--
theorem `mem_primaryComponent` / 定理 `mem_primaryComponent`

English:
theorem mem_primaryComponent
  given: {g : G}
  statement: g in primaryComponent G p ↔ exists k : Nat, g ^ p ^ k = 1
  proof: .rfl

中文:
定理 mem_primaryComponent
  条件: {g : G}
  结论: g in primaryComponent G p ↔ 存在 k : 自然数, g ^ p ^ k = 1
  证明: .rfl
-/
theorem mem_primaryComponent {g : G} : g in primaryComponent G p ↔ exists k : Nat, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
/--
theorem `mem_primaryComponent_iff_orderOf` / 定理 `mem_primaryComponent_iff_orderOf`

English:
theorem mem_primaryComponent_iff_orderOf
  given: [Fact p.Prime] {g : G}
  proof: exists_orderOf_eq_prime_pow_iff.symm

中文:
定理 mem_primaryComponent_iff_orderOf
  条件: [Fact p.Prime] {g : G}
  证明: exists_orderOf_eq_prime_pow_iff.symm

Depends on / 依赖: exists_orderOf_eq_prime_pow_iff, exists_orderOf_eq_prime_pow_iff.symm
-/
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g in primaryComponent G p ↔ exists n : Nat, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

/--
theorem `primaryComponent.isPGroup` / 定理 `primaryComponent.isPGroup`

English:
theorem primaryComponent.isPGroup
  statement: IsPGroup p (primaryComponent G p)
  proof: fun g =>
g.property.imp fun _ hk => Subtype.ext by simpa using hk

中文:
定理 primaryComponent.isPGroup
  结论: IsPGroup p (primaryComponent G p)
  证明: fun g =>
g.property.imp fun _ hk => Subtype.ext by simpa using hk
-/
theorem primaryComponent.isPGroup : IsPGroup p (primaryComponent G p) := fun g =>
g.property.imp fun _ hk => Subtype.ext by simpa using hk

variable (G H)

/-- The free rank of a finitely generated abelian group is the rank of its free part. -/
@[to_additive
/-- The free rank of a finitely generated abelian group is the rank of its free part. -/]
/--
Definition of `freeRank` / `freeRank` 的定义

English:
definition freeRank
  signature: [Group.FG G]
  body: Group.rank (G ⧸ torsion G)

@[to_additive]

中文:
定义 freeRank
  签名: [Group.FG G]
  定义体: Group.rank (G ⧸ torsion G)

@[to_additive]

Depends on / 依赖: Group.rank, torsion
-/
noncomputable def freeRank [Group.FG G] : Nat := Group.rank (G ⧸ torsion G)

@[to_additive]
/--
theorem `freeRank_def` / 定理 `freeRank_def`

English:
theorem freeRank_def
  given: [Group.FG G]
  statement: freeRank G = Group.rank (G ⧸ torsion G)
  proof: rfl

中文:
定理 freeRank_def
  条件: [Group.FG G]
  结论: freeRank G = Group.rank (G ⧸ torsion G)
  证明: rfl
-/
theorem freeRank_def [Group.FG G] : freeRank G = Group.rank (G ⧸ torsion G) := rfl

variable {G H}

@[to_additive]
/--
theorem `freeRank_eq_zero_iff` / 定理 `freeRank_eq_zero_iff`

English:
theorem freeRank_eq_zero_iff
  given: [Group.FG G]
  statement: freeRank G = 0 ↔ IsMulTorsion G
  proof: by
  rw [freeRank]; rw [Group.rank_eq_zero_iff]; rw [QuotientGroup.subsingleton_iff]; rw [torsion_eq_top_iff]

@[to_additive]

中文:
定理 freeRank_eq_zero_iff
  条件: [Group.FG G]
  结论: freeRank G = 0 ↔ IsMulTorsion G
  证明: by
  rw [freeRank]; rw [Group.rank_eq_zero_iff]; rw [QuotientGroup.subsingleton_iff]; rw [torsion_eq_top_iff]

@[to_additive]

Depends on / 依赖: Group.rank_eq_zero_iff, QuotientGroup, QuotientGroup.subsingleton_iff, freeRank, rank_eq_zero_iff, subsingleton_iff, torsion_eq_top_iff
-/
theorem freeRank_eq_zero_iff [Group.FG G] : freeRank G = 0 ↔ IsMulTorsion G := by
  rw [freeRank]; rw [Group.rank_eq_zero_iff]; rw [QuotientGroup.subsingleton_iff]; rw [torsion_eq_top_iff]

@[to_additive]
/--
theorem `freeRank_eq_zero` / 定理 `freeRank_eq_zero`

English:
theorem freeRank_eq_zero
  given: (hG : IsMulTorsion G) [Group.FG G]
  statement: freeRank G = 0
  proof: freeRank_eq_zero_iff.mpr hG

@[to_additive]

中文:
定理 freeRank_eq_zero
  条件: (hG : IsMulTorsion G) [Group.FG G]
  结论: freeRank G = 0
  证明: freeRank_eq_zero_iff.mpr hG

@[to_additive]

Depends on / 依赖: freeRank_eq_zero_iff, freeRank_eq_zero_iff.mpr
-/
theorem freeRank_eq_zero (hG : IsMulTorsion G) [Group.FG G] : freeRank G = 0 :=
  freeRank_eq_zero_iff.mpr hG

@[to_additive]
/--
theorem `freeRank_eq_zero_of_finite` / 定理 `freeRank_eq_zero_of_finite`

English:
theorem freeRank_eq_zero_of_finite
  given: [Finite G]
  statement: freeRank G = 0
  proof: freeRank_eq_zero isMulTorsion_of_finite

@[to_additive]

中文:
定理 freeRank_eq_zero_of_finite
  条件: [Finite G]
  结论: freeRank G = 0
  证明: freeRank_eq_zero isMulTorsion_of_finite

@[to_additive]

Depends on / 依赖: freeRank_eq_zero, isMulTorsion_of_finite
-/
theorem freeRank_eq_zero_of_finite [Finite G] : freeRank G = 0 :=
  freeRank_eq_zero isMulTorsion_of_finite

@[to_additive]
/--
theorem `freeRank_congr` / 定理 `freeRank_congr`

English:
theorem freeRank_congr
  given: [Group.FG G] [Group.FG H] (e : G ≃* H)
  statement: freeRank G = freeRank H
  proof: Group.rank_congr (QuotientGroup.congr (torsion G) (torsion H) e e.map_torsion)

中文:
定理 freeRank_congr
  条件: [Group.FG G] [Group.FG H] (e : G ≃* H)
  结论: freeRank G = freeRank H
  证明: Group.rank_congr (QuotientGroup.congr (torsion G) (torsion H) e e.map_torsion)

Depends on / 依赖: Group.rank_congr, QuotientGroup, QuotientGroup.congr, e.map_torsion, map_torsion, rank_congr, torsion
-/
theorem freeRank_congr [Group.FG G] [Group.FG H] (e : G ≃* H) : freeRank G = freeRank H :=
  Group.rank_congr (QuotientGroup.congr (torsion G) (torsion H) e e.map_torsion)

-- TODO: Prove monotonicity of `freeRank` along injective homomorphisms. This would require proving
-- monotonicity of `rank` along injective homomorphism of abelian groups.
@[to_additive]
/--
theorem `freeRank_ge_of_surjective` / 定理 `freeRank_ge_of_surjective`

English:
theorem freeRank_ge_of_surjective
  statement: [Group.FG G] [Group.FG H] (e : G ->* H)
  proof: Group.rank_le_of_surjective _ QuotientGroup.map_surjective_of_surjective
    (torsion G) (torsion H) e (QuotientGroup.mk_surjective.comp he) (le_comap_torsion e)

中文:
定理 freeRank_ge_of_surjective
  结论: [Group.FG G] [Group.FG H] (e : G ->* H)
  证明: Group.rank_le_of_surjective _ QuotientGroup.map_surjective_of_surjective
    (torsion G) (torsion H) e (QuotientGroup.mk_surjective.comp he) (le_comap_torsion e)

Depends on / 依赖: Group.rank_le_of_surjective, QuotientGroup, QuotientGroup.map_surjective_of_surjective, QuotientGroup.mk_surjective.comp, le_comap_torsion, map_surjective_of_surjective, mk_surjective, rank_le_of_surjective, torsion
-/
theorem freeRank_ge_of_surjective [Group.FG G] [Group.FG H] (e : G ->* H)
    (he : Function.Surjective e) : freeRank H <= freeRank G :=
Group.rank_le_of_surjective _ QuotientGroup.map_surjective_of_surjective
    (torsion G) (torsion H) e (QuotientGroup.mk_surjective.comp he) (le_comap_torsion e)

end CommGroup

open CommGroup (torsion)

/-- Quotienting a group by its torsion subgroup yields a torsion-free group. -/
@[to_additive
/-- Quotienting an additive group by its torsion additive subgroup yields a torsion-free additive
group. -/]
/--
Instance `_root_.QuotientGroup.instIsMulTorsionFree` / 实例 `_root_.QuotientGroup.instIsMulTorsionFree`

English:
instance _root_.QuotientGroup.instIsMulTorsionFree
  signature: : IsMulTorsionFree G ⧸ torsion G
  body: by
  refine .of_not_isOfFinOrder fun g hne hfin => hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos 

中文:
实例 _root_.QuotientGroup.instIsMulTorsionFree
  签名: : IsMulTorsionFree G ⧸ torsion G
  定义体: by
  refine .of_not_isOfFinOrder fun g hne hfin => hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos 

Depends on / 依赖: QuotientGroup, QuotientGroup.eq_one_iff, eq_one_iff, exists_pow_eq_one, hfin.exists_pow_eq_one, isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, mul_pos, of_not_isOfFinOrder, pow_mul
-/
instance _root_.QuotientGroup.instIsMulTorsionFree : IsMulTorsionFree G ⧸ torsion G := by
  refine .of_not_isOfFinOrder fun g hne hfin => hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)

end CommGroup

section AddCommGroup

instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) :=
  -- Upgrade the torsion subgroup to a submodule.
  letI S : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ =>
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  -- The quotients are the same.
  let e : (M ⧸ AddCommGroup.torsion M) ≃+ (M ⧸ S) := QuotientAddGroup.congr _ _ (.refl _)
    (by simp [S])
  -- So we can copy over scalar multiplication.
  letI : SMul R (M ⧸ AddCommGroup.torsion M) := ⟨fun r m => e.symm (r • e m)⟩
  Function.Injective.module R e.toAddMonoidHom e.injective (fun _ _ =>
    e.symm.injective (e.symm_apply_apply _))

end AddCommGroup

section

variable {M : Type*} [CommMonoid M] [HasDistribNeg M]

/--
theorem `neg_one_mem_torsion` / 定理 `neg_one_mem_torsion`

English:
theorem neg_one_mem_torsion
  statement: -1 in CommMonoid.torsion M
  proof: ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

中文:
定理 neg_one_mem_torsion
  结论: -1 in CommMonoid.torsion M
  证明: ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

Depends on / 依赖: isPeriodicPt_mul_iff_pow_eq_one, zero_lt_two
-/
theorem neg_one_mem_torsion : -1 in CommMonoid.torsion M :=
  ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

end
