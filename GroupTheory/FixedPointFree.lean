/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

@[expose] public section

namespace MonoidHom

variable {F G : Type*}

section Definitions

variable (φ : G -> G)

/--
Definition of `FixedPointFree` / `FixedPointFree` 的定义

English:
definition FixedPointFree
  signature: [One G]
  body: forall g, φ g = g -> g = 1

中文:
定义 FixedPointFree
  签名: [幺 G]
  定义体: forall g, φ g = g -> g = 1
-/
def FixedPointFree [One G] := forall g, φ g = g -> g = 1

/--
Definition of `commutatorMap` / `commutatorMap` 的定义

English:
definition commutatorMap
  signature: [Div G] (g : G)
  body: g / φ g

中文:
定义 commutatorMap
  签名: [除法 G] (g : G)
  定义体: g / φ g
-/
def commutatorMap [Div G] (g : G) := g / φ g

/--
theorem `commutatorMap_apply` / 定理 `commutatorMap_apply`

English:
theorem commutatorMap_apply
  given: [Div G] (g : G)
  statement: commutatorMap φ g = g / φ g
  proof: rfl

中文:
定理 commutatorMap_apply
  条件: [除法 G] (g : G)
  结论: commutatorMap φ g = g / φ g
  证明: rfl
-/
@[simp] theorem commutatorMap_apply [Div G] (g : G) : commutatorMap φ g = g / φ g := rfl

end Definitions

namespace FixedPointFree
variable [Group G] [FunLike F G G] [MonoidHomClass F G G] {φ : F}

/--
theorem `commutatorMap_injective` / 定理 `commutatorMap_injective`

English:
theorem commutatorMap_injective
  given: (hφ : FixedPointFree φ)
  statement: Function.Injective (commutatorMap φ)
  proof: by
refine fun x y h => inv_mul_eq_one.mp hφ _ ?_
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

中文:
定理 commutatorMap_injective
  条件: (hφ : FixedPointFree φ)
  结论: 函数.单射 (commutatorMap φ)
  证明: by
refine fun x y h => inv_mul_eq_one.mp hφ _ ?_
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

Depends on / 依赖: division_def, eq_div_iff_mul_eq, eq_inv_mul_iff_mul_eq, inv_mul_eq_one, inv_mul_eq_one.mp, map_inv, map_mul, mul_assoc
-/
theorem commutatorMap_injective (hφ : FixedPointFree φ) : Function.Injective (commutatorMap φ) := by
refine fun x y h => inv_mul_eq_one.mp hφ _ ?_
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

variable [Finite G]

/--
theorem `commutatorMap_surjective` / 定理 `commutatorMap_surjective`

English:
theorem commutatorMap_surjective
  given: (hφ : FixedPointFree φ)
  statement: Function.Surjective (commutatorMap φ)
  proof: Finite.surjective_of_injective hφ.commutatorMap_injective

中文:
定理 commutatorMap_surjective
  条件: (hφ : FixedPointFree φ)
  结论: 函数.满射 (commutatorMap φ)
  证明: Finite.surjective_of_injective hφ.commutatorMap_injective

Depends on / 依赖: Finite, Finite.surjective_of_injective, commutatorMap_injective, surjective_of_injective
-/
theorem commutatorMap_surjective (hφ : FixedPointFree φ) : Function.Surjective (commutatorMap φ) :=
  Finite.surjective_of_injective hφ.commutatorMap_injective

/--
theorem `prod_pow_eq_one` / 定理 `prod_pow_eq_one`

English:
theorem prod_pow_eq_one
  given: (hφ : FixedPointFree φ) {n : Nat} (hn : φ^[n] = _root_.id) (g : G)
  proof: by
  obtain ⟨g, rfl⟩ := commutatorMap_surjective hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div']; rw [Function.iterate_zero_apply]; rw [hn]; rw [Function.id_def]; rw [div_self']

中文:
定理 prod_pow_eq_one
  条件: (hφ : FixedPointFree φ) {n : 自然数} (hn : φ^[n] = _root_.id) (g : G)
  证明: by
  obtain ⟨g, rfl⟩ := commutatorMap_surjective hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div']; rw [Function.iterate_zero_apply]; rw [hn]; rw [Function.id_def]; rw [div_self']

Depends on / 依赖: Function, Function.id_def, Function.iterate_succ_apply, Function.iterate_zero_apply, List.prod_range_div, commutatorMap_apply, commutatorMap_surjective, div_self, id_def, iterate_map_div, iterate_succ_apply, iterate_zero_apply, prod_range_div
-/
theorem prod_pow_eq_one (hφ : FixedPointFree φ) {n : Nat} (hn : φ^[n] = _root_.id) (g : G) :
    ((List.range n).map (fun k => φ^[k] g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := commutatorMap_surjective hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div']; rw [Function.iterate_zero_apply]; rw [hn]; rw [Function.id_def]; rw [div_self']

/--
theorem `coe_eq_inv_of_sq_eq_one` / 定理 `coe_eq_inv_of_sq_eq_one`

English:
theorem coe_eq_inv_of_sq_eq_one
  given: (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id)
  statement: ⇑φ = (·⁻¹)
  proof: by
  ext g
  have key : g * φ g = 1 := by simpa [List.range_succ] using hφ.prod_pow_eq_one h2 g
  rwa [← inv_eq_iff_mul_eq_one, eq_comm] at key

中文:
定理 coe_eq_inv_of_sq_eq_one
  条件: (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id)
  结论: ⇑φ = (·⁻¹)
  证明: by
  ext g
  have key : g * φ g = 1 := by simpa [List.range_succ] using hφ.prod_pow_eq_one h2 g
  rwa [← inv_eq_iff_mul_eq_one, eq_comm] at key

Depends on / 依赖: List.range_succ, eq_comm, inv_eq_iff_mul_eq_one, prod_pow_eq_one, range_succ
-/
theorem coe_eq_inv_of_sq_eq_one (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id) : ⇑φ = (·⁻¹) := by
  ext g
  have key : g * φ g = 1 := by simpa [List.range_succ] using hφ.prod_pow_eq_one h2 g
  rwa [← inv_eq_iff_mul_eq_one, eq_comm] at key

section Involutive

/--
theorem `coe_eq_inv_of_involutive` / 定理 `coe_eq_inv_of_involutive`

English:
theorem coe_eq_inv_of_involutive
  given: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ)
  proof: coe_eq_inv_of_sq_eq_one hφ (funext h2)

中文:
定理 coe_eq_inv_of_involutive
  条件: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ)
  证明: coe_eq_inv_of_sq_eq_one hφ (funext h2)

Depends on / 依赖: coe_eq_inv_of_sq_eq_one
-/
theorem coe_eq_inv_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    ⇑φ = (·⁻¹) :=
  coe_eq_inv_of_sq_eq_one hφ (funext h2)

/--
theorem `commute_all_of_involutive` / 定理 `commute_all_of_involutive`

English:
theorem commute_all_of_involutive
  given: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g h : G)
  proof: by
  have key := map_mul φ g h
  rwa [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, inv_inv] at key

中文:
定理 commute_all_of_involutive
  条件: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ) (g h : G)
  证明: by
  have key := map_mul φ g h
  rwa [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, inv_inv] at key

Depends on / 依赖: coe_eq_inv_of_involutive, inv_eq_iff_eq_inv, inv_inv, map_mul, mul_inv_rev
-/
theorem commute_all_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g h : G) :
    Commute g h := by
  have key := map_mul φ g h
  rwa [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, inv_inv] at key

/-- If a finite group admits a fixed-point-free involution, then it is commutative. -/
@[instance_reducible]
/--
Definition of `commGroupOfInvolutive` / `commGroupOfInvolutive` 的定义

English:
definition commGroupOfInvolutive
  signature: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ)
  body: .mk (hφ.commute_all_of_involutive h2)

中文:
定义 commGroupOfInvolutive
  签名: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ)
  定义体: .mk (hφ.commute_all_of_involutive h2)

Depends on / 依赖: commute_all_of_involutive
-/
def commGroupOfInvolutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    CommGroup G := .mk (hφ.commute_all_of_involutive h2)

/--
theorem `orderOf_ne_two_of_involutive` / 定理 `orderOf_ne_two_of_involutive`

English:
theorem orderOf_ne_two_of_involutive
  given: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G)
  proof: by
  intro hg
  have key : φ g = g := by
    rw [hφ.coe_eq_inv_of_involutive h2]; rw [inv_eq_iff_mul_eq_one]; rw [← sq]; rw [← hg]; rw [pow_orderOf_eq_one]
  rw [hφ g key]; rw [orderOf_one] at hg
  contradiction

中文:
定理 orderOf_ne_two_of_involutive
  条件: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ) (g : G)
  证明: by
  intro hg
  have key : φ g = g := by
    rw [hφ.coe_eq_inv_of_involutive h2]; rw [inv_eq_iff_mul_eq_one]; rw [← sq]; rw [← hg]; rw [pow_orderOf_eq_one]
  rw [hφ g key]; rw [orderOf_one] at hg
  contradiction

Depends on / 依赖: coe_eq_inv_of_involutive, inv_eq_iff_mul_eq_one, orderOf_one, pow_orderOf_eq_one
-/
theorem orderOf_ne_two_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    orderOf g != 2 := by
  intro hg
  have key : φ g = g := by
    rw [hφ.coe_eq_inv_of_involutive h2]; rw [inv_eq_iff_mul_eq_one]; rw [← sq]; rw [← hg]; rw [pow_orderOf_eq_one]
  rw [hφ g key]; rw [orderOf_one] at hg
  contradiction

/--
theorem `odd_card_of_involutive` / 定理 `odd_card_of_involutive`

English:
theorem odd_card_of_involutive
  given: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ)
  proof: by
  have := Fintype.ofFinite G
  by_contra h
  rw [Nat.not_odd_iff_even]; rw [even_iff_two_dvd]; rw [Nat.card_eq_fintype_card] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h
  exact hφ.orderOf_ne_two_of_involutive h2 g hg

中文:
定理 odd_card_of_involutive
  条件: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ)
  证明: by
  have := Fintype.ofFinite G
  by_contra h
  rw [Nat.not_odd_iff_even]; rw [even_iff_two_dvd]; rw [Nat.card_eq_fintype_card] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h
  exact hφ.orderOf_ne_two_of_involutive h2 g hg

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.not_odd_iff_even, card_eq_fintype_card, even_iff_two_dvd, exists_prime_orderOf_dvd_card, not_odd_iff_even, ofFinite, orderOf_ne_two_of_involutive
-/
theorem odd_card_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    Odd (Nat.card G) := by
  have := Fintype.ofFinite G
  by_contra h
  rw [Nat.not_odd_iff_even]; rw [even_iff_two_dvd]; rw [Nat.card_eq_fintype_card] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h
  exact hφ.orderOf_ne_two_of_involutive h2 g hg

/--
theorem `odd_orderOf_of_involutive` / 定理 `odd_orderOf_of_involutive`

English:
theorem odd_orderOf_of_involutive
  given: (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G)
  proof: Odd.of_dvd_nat (hφ.odd_card_of_involutive h2) (orderOf_dvd_natCard g)

中文:
定理 odd_orderOf_of_involutive
  条件: (hφ : FixedPointFree φ) (h2 : 函数.对合 φ) (g : G)
  证明: Odd.of_dvd_nat (hφ.odd_card_of_involutive h2) (orderOf_dvd_natCard g)

Depends on / 依赖: Odd.of_dvd_nat, odd_card_of_involutive, of_dvd_nat, orderOf_dvd_natCard
-/
theorem odd_orderOf_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    Odd (orderOf g) :=
  Odd.of_dvd_nat (hφ.odd_card_of_involutive h2) (orderOf_dvd_natCard g)

end Involutive

end FixedPointFree

end MonoidHom
