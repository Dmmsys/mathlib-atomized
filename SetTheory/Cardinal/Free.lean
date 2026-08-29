/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Daniel Weber
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinalities of free constructions

This file shows that all the free constructions over `α` have cardinality `max #α ℵ₀`,
and are thus infinite, and specifically countable over countable generators.

Combined with the ring `Fin n` for the finite cases, this lets us show that there is a `CommRing` of
any cardinality.
-/

public section

universe u
variable (α : Type u)

section Infinite

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Infinite (FreeMonoid α)
  body: inferInstanceAs Infinite (List α)

@[to_additive]

中文:
实例 [Nonempty
  签名: α] : Infinite (FreeMonoid α)
  定义体: inferInstanceAs Infinite (List α)

@[to_additive]

Depends on / 依赖: Infinite
-/
instance [Nonempty α] : Infinite (FreeMonoid α) := inferInstanceAs Infinite (List α)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Infinite (FreeGroup α)
  body: by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

中文:
实例 [Nonempty
  签名: α] : Infinite (FreeGroup α)
  定义体: by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

Depends on / 依赖: FreeGroup, FreeGroup.norm, FreeGroup.norm_surjective, Infinite, Infinite.of_surjective, classical, norm_surjective, of_surjective
-/
instance [Nonempty α] : Infinite (FreeGroup α) := by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Infinite (FreeAbelianGroup α)
  body: (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

deriving instance Infinite for FreeRing, FreeCommRing

中文:
实例 [Nonempty
  签名: α] : Infinite (FreeAbelianGroup α)
  定义体: (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

deriving instance Infinite for FreeRing, FreeCommRing

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, infinite_iff, toEquiv, toEquiv.infinite_iff
-/
instance [Nonempty α] : Infinite (FreeAbelianGroup α) :=
  (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

deriving instance Infinite for FreeRing, FreeCommRing

end Infinite

section Countable

variable [Countable α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (FreeMonoid α)
  body: inferInstanceAs Countable (List α)

@[to_additive]

中文:
实例 :
  签名: Countable (FreeMonoid α)
  定义体: inferInstanceAs Countable (List α)

@[to_additive]

Depends on / 依赖: Countable
-/
instance : Countable (FreeMonoid α) := inferInstanceAs Countable (List α)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (FreeGroup α)
  body: inferInstanceAs Countable (Quot _)

中文:
实例 :
  签名: Countable (FreeGroup α)
  定义体: inferInstanceAs Countable (Quot _)

Depends on / 依赖: Countable
-/
instance : Countable (FreeGroup α) := inferInstanceAs Countable (Quot _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (FreeAbelianGroup α)
  body: inferInstanceAs Countable (Quot _)

中文:
实例 :
  签名: Countable (FreeAbelianGroup α)
  定义体: inferInstanceAs Countable (Quot _)

Depends on / 依赖: Countable
-/
instance : Countable (FreeAbelianGroup α) := inferInstanceAs Countable (Quot _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (FreeRing α)
  body: inferInstanceAs Countable (Quot _)

中文:
实例 :
  签名: Countable (FreeRing α)
  定义体: inferInstanceAs Countable (Quot _)

Depends on / 依赖: Countable
-/
instance : Countable (FreeRing α) := inferInstanceAs Countable (Quot _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (FreeCommRing α)
  body: inferInstanceAs Countable (FreeAbelianGroup (Multiset α))

中文:
实例 :
  签名: Countable (FreeCommRing α)
  定义体: inferInstanceAs Countable (FreeAbelianGroup (Multiset α))

Depends on / 依赖: Countable, FreeAbelianGroup, Multiset
-/
instance : Countable (FreeCommRing α) :=
inferInstanceAs Countable (FreeAbelianGroup (Multiset α))

end Countable

namespace Cardinal

/--
theorem `mk_abelianization_le` / 定理 `mk_abelianization_le`

English:
theorem mk_abelianization_le
  given: (G : Type u) [Group G]
  proof: Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[to_additive (attr := simp)]

中文:
定理 mk_abelianization_le
  条件: (G : 类型u) [Group G]
  证明: Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[to_additive (attr := simp)]

Depends on / 依赖: Cardinal, Cardinal.mk_le_of_surjective, Quotient, Quotient.mk_surjective, mk_le_of_surjective, mk_surjective
-/
theorem mk_abelianization_le (G : Type u) [Group G] :
    #(Abelianization G) <= #G := Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[to_additive (attr := simp)]
/--
theorem `mk_freeMonoid` / 定理 `mk_freeMonoid`

English:
theorem mk_freeMonoid
  given: [Nonempty α]
  statement: #(FreeMonoid α) = max #α ℵ₀
  proof: Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]

中文:
定理 mk_freeMonoid
  条件: [Nonempty α]
  结论: #(FreeMonoid α) = max #α ℵ₀
  证明: Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]

Depends on / 依赖: Cardinal, Cardinal.mk_list_eq_max_mk_aleph0, mk_list_eq_max_mk_aleph0
-/
theorem mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = max #α ℵ₀ :=
    Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]
/--
theorem `mk_freeGroup` / 定理 `mk_freeGroup`

English:
theorem mk_freeGroup
  given: [Nonempty α]
  statement: #(FreeGroup α) = max #α ℵ₀
  proof: by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp only [mk_list_eq_max_mk_aleph0, mk_prod, lift_uzero, mk_fintype, Fintype.card_bool,
      Nat.cast_ofNat, lift_ofNat]
    obtain hα | hα := lt_or_ge #α ℵ₀
    · simp only [hα.le,

中文:
定理 mk_freeGroup
  条件: [Nonempty α]
  结论: #(FreeGroup α) = max #α ℵ₀
  证明: by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp only [mk_list_eq_max_mk_aleph0, mk_prod, lift_uzero, mk_fintype, Fintype.card_bool,
      Nat.cast_ofNat, lift_ofNat]
    obtain hα | hα := lt_or_ge #α ℵ₀
    · simp only [hα.le,

Depends on / 依赖: Cardinal, Cardinal.le_mul_right, Cardinal.mul_eq_left, Fintype, Fintype.card_bool, FreeGroup, FreeGroup.toWord_injective, Nat.cast_ofNat, card_bool, cast_ofNat, classical, le_antisymm, le_mul_right, lift_ofNat, lift_uzero, lt_or_ge, max_eq_left, max_eq_right, max_eq_right_iff, mk_fintype
-/
theorem mk_freeGroup [Nonempty α] : #(FreeGroup α) = max #α ℵ₀ := by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp only [mk_list_eq_max_mk_aleph0, mk_prod, lift_uzero, mk_fintype, Fintype.card_bool,
      Nat.cast_ofNat, lift_ofNat]
    obtain hα | hα := lt_or_ge #α ℵ₀
    · simp only [hα.le, max_eq_right, max_eq_right_iff]
      exact (mul_lt_aleph0 hα natCast_lt_aleph0).le
    · rw [max_eq_left hα, max_eq_left (hα.trans <| Cardinal.le_mul_right two_ne_zero),
        Cardinal.mul_eq_left hα _ (by simp)]
      exact natCast_le_aleph0.trans hα
  · apply max_le
    · exact mk_le_of_injective FreeGroup.of_injective
    · simp

@[simp]
/--
theorem `mk_freeAbelianGroup` / 定理 `mk_freeAbelianGroup`

English:
theorem mk_freeAbelianGroup
  given: [Nonempty α]
  statement: #(FreeAbelianGroup α) = max #α ℵ₀
  proof: by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]

中文:
定理 mk_freeAbelianGroup
  条件: [Nonempty α]
  结论: #(FreeAbelianGroup α) = max #α ℵ₀
  证明: by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]

Depends on / 依赖: Cardinal, Cardinal.mk_congr, FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, mk_congr, toEquiv
-/
theorem mk_freeAbelianGroup [Nonempty α] : #(FreeAbelianGroup α) = max #α ℵ₀ := by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]
/--
theorem `mk_freeRing` / 定理 `mk_freeRing`

English:
theorem mk_freeRing
  statement: #(FreeRing α) = max #α ℵ₀
  proof: by
  cases isEmpty_or_nonempty α <;> simp [FreeRing]

@[simp]

中文:
定理 mk_freeRing
  结论: #(FreeRing α) = max #α ℵ₀
  证明: by
  cases isEmpty_or_nonempty α <;> simp [FreeRing]

@[simp]

Depends on / 依赖: FreeRing, isEmpty_or_nonempty
-/
theorem mk_freeRing : #(FreeRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeRing]

@[simp]
/--
theorem `mk_freeCommRing` / 定理 `mk_freeCommRing`

English:
theorem mk_freeCommRing
  statement: #(FreeCommRing α) = max #α ℵ₀
  proof: by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

中文:
定理 mk_freeCommRing
  结论: #(FreeCommRing α) = max #α ℵ₀
  证明: by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

Depends on / 依赖: FreeCommRing, isEmpty_or_nonempty
-/
theorem mk_freeCommRing : #(FreeCommRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

end Cardinal

section Nonempty

/--
Instance `nonempty_commRing` / 实例 `nonempty_commRing`

English:
instance nonempty_commRing
  signature: [Nonempty α]
  body: by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨open scoped Fin.CommRing in e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardi

中文:
实例 nonempty_commRing
  签名: [Nonempty α]
  定义体: by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨open scoped Fin.CommRing in e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardi

Depends on / 依赖: Cardinal, Cardinal.eq, CommRing, Fin.CommRing, Fintype, Fintype.card, Fintype.truncEquivFin, FreeCommRing, NeZero, Nonempty, classical, commRing, e.commRing, finite_or_infinite, nonempty_fintype, scoped, truncEquivFin
-/
instance nonempty_commRing [Nonempty α] : Nonempty (CommRing α) := by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨open scoped Fin.CommRing in e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardinal.eq]
    exact ⟨e.commRing⟩

@[simp]
/--
theorem `nonempty_commRing_iff` / 定理 `nonempty_commRing_iff`

English:
theorem nonempty_commRing_iff
  statement: Nonempty (CommRing α) ↔ Nonempty α
  proof: ⟨Nonempty.map (·.zero), fun _ => nonempty_commRing _⟩

@[simp]

中文:
定理 nonempty_commRing_iff
  结论: Nonempty (CommRing α) ↔ Nonempty α
  证明: ⟨Nonempty.map (·.zero), fun _ => nonempty_commRing _⟩

@[simp]

Depends on / 依赖: Nonempty, Nonempty.map, nonempty_commRing
-/
theorem nonempty_commRing_iff : Nonempty (CommRing α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => nonempty_commRing _⟩

@[simp]
/--
theorem `nonempty_ring_iff` / 定理 `nonempty_ring_iff`

English:
theorem nonempty_ring_iff
  statement: Nonempty (Ring α) ↔ Nonempty α
  proof: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[simp]

中文:
定理 nonempty_ring_iff
  结论: Nonempty (Ring α) ↔ Nonempty α
  证明: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[simp]

Depends on / 依赖: Nonempty, Nonempty.map, nonempty_commRing, toRing
-/
theorem nonempty_ring_iff : Nonempty (Ring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[simp]
/--
theorem `nonempty_commSemiring_iff` / 定理 `nonempty_commSemiring_iff`

English:
theorem nonempty_commSemiring_iff
  statement: Nonempty (CommSemiring α) ↔ Nonempty α
  proof: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toCommSemiring)⟩

@[simp]

中文:
定理 nonempty_commSemiring_iff
  结论: Nonempty (CommSemiring α) ↔ Nonempty α
  证明: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toCommSemiring)⟩

@[simp]

Depends on / 依赖: Nonempty, Nonempty.map, nonempty_commRing, toCommSemiring
-/
theorem nonempty_commSemiring_iff : Nonempty (CommSemiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toCommSemiring)⟩

@[simp]
/--
theorem `nonempty_semiring_iff` / 定理 `nonempty_semiring_iff`

English:
theorem nonempty_semiring_iff
  statement: Nonempty (Semiring α) ↔ Nonempty α
  proof: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toSemiring)⟩

中文:
定理 nonempty_semiring_iff
  结论: Nonempty (Semiring α) ↔ Nonempty α
  证明: ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toSemiring)⟩

Depends on / 依赖: Nonempty, Nonempty.map, nonempty_commRing, toSemiring
-/
theorem nonempty_semiring_iff : Nonempty (Semiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toSemiring)⟩

end Nonempty
