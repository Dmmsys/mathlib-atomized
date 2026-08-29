/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.SetTheory.Cardinal.Divisibility

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `Fintype.nonempty_field_iff`: A `Fintype` can be given a field structure iff its cardinality is a
  prime power.
* `Infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `Field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/

public section


local notation "‖" x "‖" => Fintype.card x

open scoped Cardinal nonZeroDivisors

universe u

/--
theorem `Fintype.isPrimePow_card_of_field` / 定理 `Fintype.isPrimePow_card_of_field`

English:
theorem Fintype.isPrimePow_card_of_field
  given: {α} [Fintype α] [Field α]
  statement: IsPrimePow ‖α‖
  proof: -- TODO: `Algebra` version of `CharP.exists`, of type `∀ p, Algebra (ZMod p) α`
  FiniteField.isPrimePow_card α

中文:
定理 有限类型.isPrimePow_card_of_field
  条件: {α} [有限类型 α] [域 α]
  结论: IsPrimePow ‖α‖
  证明: -- TODO: `Algebra` version of `CharP.exists`, of type `∀ p, Algebra (ZMod p) α`
  FiniteField.isPrimePow_card α
-/
theorem Fintype.isPrimePow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α‖ :=
  -- TODO: `Algebra` version of `CharP.exists`, of type `∀ p, Algebra (ZMod p) α`
  FiniteField.isPrimePow_card α

/--
theorem `Fintype.nonempty_field_iff` / 定理 `Fintype.nonempty_field_iff`

English:
theorem Fintype.nonempty_field_iff
  given: {α} [Fintype α]
  statement: Nonempty (Field α) ↔ IsPrimePow ‖α‖
  proof: by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  have := Fact.mk hp.nat_prime
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).tran

中文:
定理 有限类型.nonempty_field_iff
  条件: {α} [有限类型 α]
  结论: 非空 (域 α) ↔ IsPrimePow ‖α‖
  证明: by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  have := Fact.mk hp.nat_prime
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).tran

Depends on / 依赖: Fact.mk, Fintype, Fintype.card_eq_nat_card, Fintype.equivOfCardEq, Fintype.isPrimePow_card_of_field, Fintype.ofFinite, GaloisField, GaloisField.card, card_eq_nat_card, equivOfCardEq, hn.ne, hp.nat_prime, isPrimePow_card_of_field, nat_prime, ofFinite, symm.field
-/
theorem Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow ‖α‖ := by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  have := Fact.mk hp.nat_prime
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).trans hα)).symm.field⟩

/--
theorem `Fintype.not_isField_of_card_not_prime_pow` / 定理 `Fintype.not_isField_of_card_not_prime_pow`

English:
theorem Fintype.not_isField_of_card_not_prime_pow
  given: {α} [Fintype α] [Ring α]
  proof: mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

中文:
定理 有限类型.not_isField_of_card_not_prime_pow
  条件: {α} [有限类型 α] [环 α]
  证明: mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

Depends on / 依赖: Fintype, Fintype.nonempty_field_iff.mp, h.toField, nonempty_field_iff, toField
-/
theorem Fintype.not_isField_of_card_not_prime_pow {α} [Fintype α] [Ring α] :
    ¬IsPrimePow ‖α‖ -> ¬IsField α :=
  mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

/--
theorem `Infinite.nonempty_field` / 定理 `Infinite.nonempty_field`

English:
theorem Infinite.nonempty_field
  given: {α : Type u} [Infinite α]
  statement: Nonempty (Field α)
  proof: by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} Rat)) from
    (Cardinal.eq.1 this).map (·.field)
  simp

中文:
定理 无限.nonempty_field
  条件: {α : 类型u} [无限 α]
  结论: 非空 (域 α)
  证明: by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} Rat)) from
    (Cardinal.eq.1 this).map (·.field)
  simp

Depends on / 依赖: Cardinal, Cardinal.eq, FractionRing, MvPolynomial
-/
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) := by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} Rat)) from
    (Cardinal.eq.1 this).map (·.field)
  simp

/--
theorem `Field.nonempty_iff` / 定理 `Field.nonempty_iff`

English:
theorem Field.nonempty_iff
  given: {α : Type u}
  statement: Nonempty (Field α) ↔ IsPrimePow #α
  proof: by
  rw [Cardinal.isPrimePow_iff]
  obtain h | h := fintypeOrInfinite α
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      Cardinal.natCast_lt_aleph0.not_ge, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinit

中文:
定理 域.nonempty_iff
  条件: {α : 类型u}
  结论: 非空 (域 α) ↔ IsPrimePow #α
  证明: by
  rw [Cardinal.isPrimePow_iff]
  obtain h | h := fintypeOrInfinite α
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      Cardinal.natCast_lt_aleph0.not_ge, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinit

Depends on / 依赖: Cardinal, Cardinal.infinite_iff, Cardinal.isPrimePow_iff, Cardinal.mk_fintype, Cardinal.natCast_lt_aleph0.not_ge, Fintype, Fintype.nonempty_field_iff, Infinite, Infinite.nonempty_field, Nat.cast_inj, cast_inj, exists_eq_left, false_or, fintypeOrInfinite, iff_true, infinite_iff, isPrimePow_iff, mk_fintype, natCast_lt_aleph0, nonempty_field
-/
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow #α := by
  rw [Cardinal.isPrimePow_iff]
  obtain h | h := fintypeOrInfinite α
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      Cardinal.natCast_lt_aleph0.not_ge, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinite.nonempty_field
