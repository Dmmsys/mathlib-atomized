/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Commutative monoids with enough roots of unity

We define a typeclass `HasEnoughRootsOfUnity M n` for a commutative monoid `M` and
a natural number `n` that asserts that `M` contains a primitive `n`th root of unity
and that the group of `n`th roots of unity in `M` is cyclic. Such monoids are suitable
targets for homomorphisms from groups of exponent (dividing) `n`; for example,
the homomorphisms can then be used to separate elements of the source group.
-/

public section

/--
Definition of `HasEnoughRootsOfUnity` / `HasEnoughRootsOfUnity` 的定义

English:
class HasEnoughRootsOfUnity
  parameters: (M : Type*) [CommMonoid M] (n : Nat)
  axioms and operations (1):
    - prim : exists m : M, IsPrimitiveRoot m n

中文:
类 HasEnoughRootsOfUnity
  参数: (M : 类型) [CommMonoid M] (n : 自然数)
  公理与运算 (1 个):
    - prim : 存在 m : M, IsPrimitiveRoot m n
-/
class HasEnoughRootsOfUnity (M : Type*) [CommMonoid M] (n : Nat) where
  prim : exists m : M, IsPrimitiveRoot m n
cyc : IsCyclic rootsOfUnity n M

namespace HasEnoughRootsOfUnity

/--
lemma `exists_primitiveRoot` / 引理 `exists_primitiveRoot`

English:
lemma exists_primitiveRoot
  given: (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n]
  proof: HasEnoughRootsOfUnity.prim

中文:
引理 exists_primitiveRoot
  条件: (M : 类型) [CommMonoid M] (n : 自然数) [HasEnoughRootsOfUnity M n]
  证明: HasEnoughRootsOfUnity.prim

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.prim
-/
lemma exists_primitiveRoot (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] :
    exists ζ : M, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim

/--
Instance `rootsOfUnity_isCyclic` / 实例 `rootsOfUnity_isCyclic`

English:
instance rootsOfUnity_isCyclic
  signature: (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n]
  body: HasEnoughRootsOfUnity.cyc

中文:
实例 rootsOfUnity_isCyclic
  签名: (M : 类型) [CommMonoid M] (n : 自然数) [HasEnoughRootsOfUnity M n]
  定义体: HasEnoughRootsOfUnity.cyc

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.cyc
-/
instance rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : Nat) [HasEnoughRootsOfUnity M n] :
    IsCyclic (rootsOfUnity n M) :=
  HasEnoughRootsOfUnity.cyc

/--
lemma `of_dvd` / 引理 `of_dvd`

English:
lemma of_dvd
  statement: (M : Type*) [CommMonoid M] {m n : Nat} [NeZero n] (hmn : m ∣ n)
  proof: have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
cyc := Subgroup.isCyclic_of_le rootsOfUnity_le_of_dvd hmn

中文:
引理 of_dvd
  结论: (M : 类型) [CommMonoid M] {m n : 自然数} [NeZero n] (hmn : m ∣ n)
  证明: have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
cyc := Subgroup.isCyclic_of_le rootsOfUnity_le_of_dvd hmn

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.pow, NeZero, NeZero.pos, Subgroup, Subgroup.isCyclic_of_le, exists_primitiveRoot, isCyclic_of_le, mul_comm, rootsOfUnity_le_of_dvd
-/
lemma of_dvd (M : Type*) [CommMonoid M] {m n : Nat} [NeZero n] (hmn : m ∣ n)
    [HasEnoughRootsOfUnity M n] :
    HasEnoughRootsOfUnity M m where
  prim :=
    have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
cyc := Subgroup.isCyclic_of_le rootsOfUnity_le_of_dvd hmn

/--
Instance `finite_rootsOfUnity` / 实例 `finite_rootsOfUnity`

English:
instance finite_rootsOfUnity
  signature: (M : Type*) [CommMonoid M] (n : Nat) [NeZero n]
  body: by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : Int)
  refine Finite.of_surjective f fun x => ?_
obtain ⟨k, hk⟩ := Subgroup.

中文:
实例 finite_rootsOfUnity
  签名: (M : 类型) [CommMonoid M] (n : 自然数) [NeZero n]
  定义体: by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : Int)
  refine Finite.of_surjective f fun x => ?_
obtain ⟨k, hk⟩ := Subgroup.

Depends on / 依赖: Finite, Finite.of_surjective, IsCyclic, IsCyclic.exists_generator, OneMemClass, OneMemClass.coe_eq_one.mp, Subgroup, Subgroup.mem_zpowers_iff.mp, ZMod.coe_intCast, ZMod.natCast_val, coe_eq_one, coe_intCast, exists_generator, g.prop, j.val, mem_zpowers_iff, natCast_val, of_surjective, rootsOfUnity, rootsOfUnity_isCyclic
-/
instance finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : Nat) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
Finite rootsOfUnity n M := by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : Int)
  refine Finite.of_surjective f fun x => ?_
obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg x
  refine ⟨k, ?_⟩
  simpa only [ZMod.natCast_val, ← hk, f, ZMod.coe_intCast] using (zpow_eq_zpow_emod' k hg').symm

/--
lemma `natCard_rootsOfUnity` / 引理 `natCard_rootsOfUnity`

English:
lemma natCard_rootsOfUnity
  statement: (M : Type*) [CommMonoid M] (n : Nat) [NeZero n]
  proof: by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g => OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit NeZero.out).unit_spec]; rw [orderOf_units]
 

中文:
引理 natCard_rootsOfUnity
  结论: (M : 类型) [CommMonoid M] (n : 自然数) [NeZero n]
  证明: by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g => OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit NeZero.out).unit_spec]; rw [orderOf_units]
 

Depends on / 依赖: IsCyclic, IsCyclic.exponent_eq_card, Monoid, Monoid.exponent_dvd_of_forall_pow_eq_one, Monoid.order_dvd_exponent, NeZero, NeZero.out, OneMemClass, OneMemClass.coe_eq_one.mp, Subgroup, Subgroup.orderOf_mk, Units.val_inj, Units.val_pow_eq_pow_val, coe_eq_one, dvd_antisymm, eq_orderOf, exists_primitiveRoot, exponent_dvd_of_forall_pow_eq_one, exponent_eq_card, g.prop
-/
lemma natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : Nat) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Nat.card (rootsOfUnity n M) = n := by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g => OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit NeZero.out).unit_spec]; rw [orderOf_units]
    let ζ' : rootsOfUnity n M := ⟨(h.isUnit NeZero.out).unit, ?_⟩
    · rw [← Subgroup.orderOf_mk]
      exact Monoid.order_dvd_exponent ζ'
    simp only [mem_rootsOfUnity]
    rw [← Units.val_inj]; rw [Units.val_pow_eq_pow_val]; rw [IsUnit.unit_spec]; rw [h.pow_eq_one]; rw [Units.val_one]

/--
lemma `of_card_le` / 引理 `of_card_le`

English:
lemma of_card_le
  statement: {R : Type*} [CommRing R] [IsDomain R] {n : Nat} [NeZero n]
  proof: card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (le_antisymm (card_rootsOfUnity R n) h)
  cyc := rootsOfUnity.isCyclic R n

中文:
引理 of_card_le
  结论: {R : 类型} [CommRing R] [IsDomain R] {n : 自然数} [NeZero n]
  证明: card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (le_antisymm (card_rootsOfUnity R n) h)
  cyc := rootsOfUnity.isCyclic R n

Depends on / 依赖: card_rootsOfUnity, card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot, card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp, le_antisymm
-/
lemma of_card_le {R : Type*} [CommRing R] [IsDomain R] {n : Nat} [NeZero n]
    (h : n <= Nat.card (rootsOfUnity n R)) : HasEnoughRootsOfUnity R n where
  prim := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (le_antisymm (card_rootsOfUnity R n) h)
  cyc := rootsOfUnity.isCyclic R n

end HasEnoughRootsOfUnity

/--
lemma `MulEquiv.hasEnoughRootsOfUnity` / 引理 `MulEquiv.hasEnoughRootsOfUnity`

English:
lemma MulEquiv.hasEnoughRootsOfUnity
  statement: {n : Nat} [NeZero n] {M N : Type*} [CommMonoid M]
  proof: by
    obtain ⟨m, hm⟩ := hm.prim
    use (e hm.toRootsOfUnity).val.val
    rw [IsPrimitiveRoot.coe_units_iff]; rw [IsPrimitiveRoot.coe_submonoidClass_iff]
    refine .map_of_injective ?_ e.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
  cyc := isCyclic

中文:
引理 MulEquiv.hasEnoughRootsOfUnity
  结论: {n : 自然数} [NeZero n] {M N : 类型} [CommMonoid M]
  证明: by
    obtain ⟨m, hm⟩ := hm.prim
    use (e hm.toRootsOfUnity).val.val
    rw [IsPrimitiveRoot.coe_units_iff]; rw [IsPrimitiveRoot.coe_submonoidClass_iff]
    refine .map_of_injective ?_ e.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
  cyc := isCyclic

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.coe_submonoidClass_iff, IsPrimitiveRoot.coe_units_iff, coe_submonoidClass_iff, coe_units_iff, e.injective, e.surjective, hm.prim, hm.toRootsOfUnity, injective, isCyclic_of_surjective, map_of_injective, surjective, toRootsOfUnity, val.val
-/
lemma MulEquiv.hasEnoughRootsOfUnity {n : Nat} [NeZero n] {M N : Type*} [CommMonoid M]
    [CommMonoid N] [hm : HasEnoughRootsOfUnity M n] (e : rootsOfUnity n M ≃* rootsOfUnity n N) :
    HasEnoughRootsOfUnity N n where
  prim := by
    obtain ⟨m, hm⟩ := hm.prim
    use (e hm.toRootsOfUnity).val.val
    rw [IsPrimitiveRoot.coe_units_iff]; rw [IsPrimitiveRoot.coe_submonoidClass_iff]
    refine .map_of_injective ?_ e.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
  cyc := isCyclic_of_surjective e e.surjective

section cyclic

/--
lemma `IsCyclic.monoidHom_equiv_self` / 引理 `IsCyclic.monoidHom_equiv_self`

English:
lemma IsCyclic.monoidHom_equiv_self
  statement: (G M : Type*) [CommGroup G] [Finite G]
  proof: by
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
.trans (mulEquivOfCyclicCardEq hord)⟩ exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G))

中文:
引理 IsCyclic.monoidHom_equiv_self
  结论: (G M : 类型) [CommGroup G] [Finite G]
  证明: by
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
.trans (mulEquivOfCyclicCardEq hord)⟩ exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G))

Depends on / 依赖: HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.natCard_rootsOfUnity, IsCyclic, IsCyclic.monoidHom_mulEquiv_rootsOfUnity, Nat.card, e.trans, monoidHom_mulEquiv_rootsOfUnity, mulEquivOfCyclicCardEq, natCard_rootsOfUnity, rootsOfUnityUnitsMulEquiv
-/
lemma IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G ->* Mˣ) ≃* G) := by
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
.trans (mulEquivOfCyclicCardEq hord)⟩ exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G))

end cyclic

instance {M : Type*} [CommMonoid M] : HasEnoughRootsOfUnity M 1 where
  prim := ⟨1, by simp⟩
  cyc := isCyclic_of_subsingleton

instance {G M : Type*} [Group G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    Finite (G ->* Mˣ) := by
  let S := rootsOfUnity (Monoid.exponent G) M
  have : Finite (G ->* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective S.subtype.comp fun f => ?_
  have H a : f a in S := by
    rw [mem_rootsOfUnity]; rw [← map_pow]; rw [Monoid.pow_exponent_eq_one]; rw [map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ => by simp⟩
